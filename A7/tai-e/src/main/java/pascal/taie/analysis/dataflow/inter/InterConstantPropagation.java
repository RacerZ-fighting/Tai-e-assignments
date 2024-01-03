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

package pascal.taie.analysis.dataflow.inter;

import jas.Pair;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 * TODO: 1. 需要一个 data structure 来获取指定 base 的所有别名
 *       2. 当对 base 实例字段进行 store 时，需要 propagate 至所有别名当中
 *       3. 当进行 load 时，找到其 base 及其别名变量对应字段的 store 语句，执行 meet 操作
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    public static PointerAnalysisResult pta;
    private final ConstantPropagation cp;
    public static HashMap<Obj, Set<Var>> aliasMap;
    public static HashMap<Pair<?, ?>, Value> valMap;
    public static HashMap<Pair<JClass, FieldRef>, Set<LoadField>> staticStmt;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        aliasMap = new HashMap<>();
        Collection<Obj> heap = pta.getObjects();
        heap.forEach(obj -> {
            HashSet<Var> vars = new HashSet<>();
            pta.getVars().stream()
                    .filter(var -> pta.getPointsToSet(var).contains(obj))
                    .forEach(vars::add);
            aliasMap.put(obj, vars);
        });

        valMap = new HashMap<>();

        staticStmt = new HashMap<>();
        icfg.getNodes().forEach(stmt -> {
            if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                FieldRef fieldRef = loadField.getFieldAccess().getFieldRef();
                JClass jClass = fieldRef.getDeclaringClass();
                Pair<JClass, FieldRef> key = new Pair<>(jClass, fieldRef);
                Set<LoadField> set = staticStmt.getOrDefault(key, new HashSet<>());
                set.add(loadField);
                staticStmt.put(key, set);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact in;
        in = out.copy();
        edge.getSource().getDef().ifPresent(lhs -> {
            if (lhs instanceof Var var) {
                in.remove(var);
            }
        });

        return in;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        JMethod callee = edge.getCallee();
        CPFact result = new CPFact();

        List<Var> args = invokeExp.getArgs();   // 实参
        List<Var> params = callee.getIR().getParams();  // 形参

        for (int i = 0; i < args.size(); ++i) {
            Var arg = args.get(i);
            Var param = params.get(i);
            result.update(param, callSiteOut.get(arg));
        }

        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact result = new CPFact();
        edge.getCallSite().getDef().ifPresent(lhs -> {
            if (lhs instanceof Var var) {
                Value value = edge.getReturnVars()
                        .stream()
                        .map(returnOut::get)
                        .reduce(Value.getUndef(), ConstantPropagation::meetValue);
                result.update(var, value);
            }
        });

        return result;
    }
}
