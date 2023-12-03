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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Var lhs = stmt.getLValue();
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(lhs),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var lhs = stmt.getLValue();
                JField staticField = stmt.getFieldRef().resolve();
                StaticField staticFieldPointer = pointerFlowGraph.getStaticField(staticField);
                VarPtr varPtr = pointerFlowGraph.getVarPtr(lhs);
                addPFGEdge(staticFieldPointer, varPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField storeField = stmt.getFieldRef().resolve();
                Var rhs = stmt.getRValue();
                VarPtr varPtr = pointerFlowGraph.getVarPtr(rhs);
                StaticField staticField = pointerFlowGraph.getStaticField(storeField);
                addPFGEdge(varPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                // 【BUG】: 这里不要用 callGraph.hasEdge(callsite.getContainer(), callee) :) 两个方法之间存在边并没考虑 callsite
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))) {
                    addReachable(method);
                    // arg -> param
                    List<Var> args = stmt.getInvokeExp().getArgs();
                    List<Var> params = method.getIR().getParams();
                    for (int i = 0; i < args.size(); ++i) {
                        Var varA = args.get(i);
                        Var varP = params.get(i);
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(varA),
                                pointerFlowGraph.getVarPtr(varP)
                        );
                    }
                    Var lhs = stmt.getLValue();
                    if (lhs != null) {
                        List<Var> returnVars = method.getIR().getReturnVars();
                        returnVars.forEach(mRet -> {
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(mRet),
                                    pointerFlowGraph.getVarPtr(lhs)
                            );
                        });
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            Var lhs = stmt.getLValue();
            Var base = stmt.getArrayAccess().getBase();
            VarPtr varPtr = pointerFlowGraph.getVarPtr(lhs);
            VarPtr basePtr = pointerFlowGraph.getVarPtr(base);
            basePtr.getPointsToSet().forEach(obj -> {
                addPFGEdge(
                        pointerFlowGraph.getArrayIndex(obj),
                        varPtr
                );
            });
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            Var rhs = stmt.getRValue();
            Var base = stmt.getArrayAccess().getBase();
            VarPtr varPtr = pointerFlowGraph.getVarPtr(rhs);
            VarPtr basePtr = pointerFlowGraph.getVarPtr(base);
            basePtr.getPointsToSet().forEach(obj -> {
                addPFGEdge(
                        varPtr,
                        pointerFlowGraph.getArrayIndex(obj)
                );
            });
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lhs = stmt.getLValue();
            Var rhs = stmt.getRValue();
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(rhs),
                    pointerFlowGraph.getVarPtr(lhs)
            );
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()) {
                workList.addEntry(target, pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pointsToSet);

            if (!delta.isEmpty() && pointer instanceof VarPtr varPtr) {
                delta.forEach(obj -> {
                    Var var = varPtr.getVar();
                    var.getLoadFields().forEach(loadField -> {
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(loadField.getLValue())
                        );
                    });

                    var.getStoreFields().forEach(storeField -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );
                    });

                    var.getLoadArrays().forEach(loadArray -> {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue())
                        );
                    });

                    var.getStoreArrays().forEach(storeArray -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    });

                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet oldSet = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();
        pointsToSet.objects()
                .filter(obj -> !oldSet.contains(obj))
                .forEach(delta::addObject);

        if (!delta.isEmpty()) {
            delta.forEach(oldSet::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> {
                workList.addEntry(succ, delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(invoke -> {
            JMethod method = resolveCallee(recv, invoke);
            Var thisVar = method.getIR().getThis();

            workList.addEntry(
                    pointerFlowGraph.getVarPtr(thisVar),
                    new PointsToSet(recv)
            );

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {
                addReachable(method);

                List<Var> params = method.getIR().getParams();
                List<Var> args = invoke.getInvokeExp().getArgs();
                for (int i = 0; i < args.size(); ++i) {
                    Var ai = args.get(i);
                    Var pi = params.get(i);
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(ai),
                            pointerFlowGraph.getVarPtr(pi)
                    );
                }

                if (invoke.getLValue() != null) {
                    List<Var> returnVars = method.getIR().getReturnVars();
                    returnVars.forEach(returnVar -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(invoke.getLValue())
                        );
                    });
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
