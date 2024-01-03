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
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.aliasMap;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.valMap;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.pta;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.staticStmt;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        workList = new ArrayDeque<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        Set<Node> entrys = icfg.entryMethods()
                .map(icfg::getEntryOf)
                .collect(Collectors.toSet());

        entrys.forEach(entry -> {
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
            result.setInFact(entry, analysis.newBoundaryFact(entry));
        });

        icfg.forEach(node -> {
            if (!entrys.contains(node)) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        });
    }

    private void doSolve() {
        // TODO - finish me
        icfg.forEach(workList::add);

        while (!workList.isEmpty()) {
            Node node = workList.poll();

            CPFact inFact = (CPFact) result.getInFact(node);
            icfg.getInEdgesOf(node).forEach(inEdge -> {
                Fact outPreFact = result.getOutFact(inEdge.getSource());
                analysis.meetInto(analysis.transferEdge(inEdge, outPreFact), (Fact) inFact);
            });

            // do analysis store stmt
            handleInstanceFieldAccess((Stmt) node, inFact);
            handleArrayAccess((Stmt) node, inFact);

            CPFact outFact = (CPFact) result.getOutFact(node);
            boolean changed;
            changed = analysis.transferNode(node, (Fact) inFact, (Fact) outFact);
            if (changed) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }

    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.equals(v2)) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    private void handleArrayAccess(Stmt stmt, CPFact in) {
        if (stmt instanceof StoreArray storeArray) {
            if (!ConstantPropagation.canHoldInt(storeArray.getRValue())) return;
            // resolve array index
            Value index = ConstantPropagation.evaluate(storeArray.getArrayAccess().getIndex(), in);
            // note: valMap 中没有 key pair 里包含 undef 的
            if (index.isUndef()) return;
            Var base = storeArray.getArrayAccess().getBase();
            pta.getPointsToSet(base).forEach(obj -> {
                Pair<Obj, Value> key = new Pair<>(obj, index);
                Value newVal = ConstantPropagation.evaluate(storeArray.getRValue(), in);
                Value oldVal = valMap.getOrDefault(key, Value.getUndef());
                newVal = meetValue(newVal, oldVal);
                valMap.put(key, newVal);

                if (!oldVal.equals(newVal)) {
                    // do propagate
                    aliasMap.get(obj).forEach(var -> {
                        var.getLoadArrays().stream()
                                .forEach(loadArray -> workList.add((Node) loadArray));
                    });
                }
            });
        }
    }

    private void handleInstanceFieldAccess(Stmt stmt, CPFact in) {
        if (stmt instanceof StoreField storeField) {
            // 右式是否为 int
            if (!ConstantPropagation.canHoldInt(storeField.getRValue())) return;
            if (!storeField.isStatic()) {
                // 与左式 base 指向 heap 中的实例进行 meet
                Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
                pta.getPointsToSet(base).forEach(obj -> {
                    Pair<Obj, FieldRef> key = new Pair<>(obj, storeField.getFieldRef());
                    // note: 右式不一定是变量！
                    Value newVal = ConstantPropagation.evaluate(storeField.getRValue(), in);
                    Value oldVal = valMap.getOrDefault(key, Value.getUndef());
                    newVal = meetValue(oldVal, newVal);
                    valMap.put(key, newVal);

                    if (!oldVal.equals(newVal)) {
                        // do propagate
                        aliasMap.get(obj).forEach(var -> {
                            // 找到所有对应别名相同字段的 load 语句
                            var.getLoadFields().stream()
                                    .filter(loadField -> loadField.getFieldRef().equals(storeField.getFieldRef()))
                                    .forEach(loadField -> workList.add((Node) loadField));
                        });
                    }
                });
            } else {
                // 同样需要对 staticLoadStmt 作处理
                FieldRef fieldRef = storeField.getFieldAccess().getFieldRef();
                JClass jClass = fieldRef.getDeclaringClass();
                Pair<JClass, FieldRef> key = new Pair<>(jClass, fieldRef);

                Value newVal = ConstantPropagation.evaluate(storeField.getRValue(), in);
                Value oldVal = valMap.getOrDefault(key, Value.getUndef());
                newVal = meetValue(newVal, oldVal);
                valMap.put(key, newVal);

                if (!oldVal.equals(newVal)) {
                    staticStmt.get(key).stream()
                            .filter(loadStatic -> loadStatic.getFieldRef().equals(storeField.getFieldRef()))
                            .forEach(loadStatic -> workList.add((Node) loadStatic));
                }
            }
        }
    }
}
