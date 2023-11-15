/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.AnalysisException;

import java.util.*;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // initialize graph traversal
        // 用于遍历时标识是否已经访问过
        // [BUG]: 维护已经遍历的数据结构应该选用 HashSet 而非 List，不然会出现 false negative :(
        Set<Stmt> isVisited = new HashSet<>();
        ArrayDeque<Stmt> queue = new ArrayDeque<>();    // BFS 队列
        queue.add(cfg.getEntry());

        while (!queue.isEmpty()) {
            Stmt stmt = queue.remove();
            isVisited.add(stmt);
            // 处理无用赋值
            if (isDeadAssignment(stmt, liveVars)) {
                deadCode.add(stmt);
            }

            // 遍历邻边
            cfg.getOutEdgesOf(stmt)
                    .stream()
                    .filter(edge -> !isUnreachableEdge(edge, constants))   // 在遍历 CFG 时，我们不进入相应的不可达分支
                    .map(Edge::getTarget)
                    .forEach(target -> {
                        if (!isVisited.contains(target)) {
                            queue.add(target);
                        }
                    });
        }
        // 处理控制流不可达以及分支不可达
        if (isVisited.size() < cfg.getNumberOfNodes()) {
            // 通过 IR 进行遍历可以拿到所有的 stmt
            // isVisited 包含的是访问到的节点(包含无用赋值)
            for (Stmt stmt : ir) {
                if (!isVisited.contains(stmt)) {
                    deadCode.add(stmt);
                }
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    private boolean isUnreachableEdge(Edge<Stmt> edge, DataflowResult<Stmt, CPFact> constants) {
        Stmt source = edge.getSource();
        // 判断 source 的 stmt 类
        if (source instanceof If ifStmt) {
            // 精妙点：复用 API
            Value condValue
                    = ConstantPropagation.evaluate(
                            ifStmt.getCondition(), constants.getInFact(ifStmt));
            // 看下 if 条件是否为常量
            if (condValue.isConstant()) {
                int v = condValue.getConstant();
                return v == 1 && edge.getKind() == Edge.Kind.IF_FALSE ||
                        v == 0 && edge.getKind() == Edge.Kind.IF_TRUE;
            }
        } else if (source instanceof SwitchStmt switchStmt) {
            Value condValue = ConstantPropagation.evaluate(
                    switchStmt.getVar(), constants.getInFact(switchStmt));
            if (condValue.isConstant()) {
                int v = condValue.getConstant();
                if (edge.isSwitchCase()) {
                    // 非 default 语句的情况
                    return v != edge.getCaseValue();
                } else {
                    // default 语句的情况
                    return switchStmt.getCaseValues()
                            .stream()
                            .anyMatch(x -> x == v);
                }
            }
        }
        return false;
    }

    private boolean isDeadAssignment(
            Stmt stmt, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (stmt instanceof AssignStmt<?, ?> assignStmt) {
            if (assignStmt.getLValue() instanceof Var lhs) {
                // OUT 集中没有 LHS 出现且无 sideEffect
                return !liveVars.getOutFact(assignStmt).contains(lhs) &&
                        hasNoSideEffect(assignStmt.getRValue());
            }
        }
        return false;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
