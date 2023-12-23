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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        if (callGraph.addReachableMethod(csMethod)) {
            csMethod.getMethod().getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Var lhs = stmt.getLValue();
            CSVar csVar = csManager.getCSVar(context, lhs);
//            CSObj csObj = csManager.getCSObj(context, heapModel.getObj(stmt));
            Context heapContext = contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt));
            PointsToSet newObj = PointsToSetFactory.make(csManager.getCSObj(heapContext, heapModel.getObj(stmt)));
            workList.addEntry(csVar, newObj);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var rValue = stmt.getRValue();
            Var lhs = stmt.getLValue();
            CSVar csRValue = csManager.getCSVar(context, rValue);
            CSVar csLhs = csManager.getCSVar(context, lhs);
            addPFGEdge(csRValue, csLhs);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var lhs = stmt.getLValue();
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = csManager.getStaticField(field);
                CSVar csVar = csManager.getCSVar(context, lhs);
                addPFGEdge(staticField, csVar);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Var rValue = stmt.getRValue();
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = csManager.getStaticField(field);
                CSVar csVar = csManager.getCSVar(context, rValue);
                addPFGEdge(csVar, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                JMethod callee = resolveCallee(null, stmt);
                Context targetContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(targetContext, callee);

                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))) {
                    addReachable(csCallee);
                    // resolve args and params
                    List<Var> args = stmt.getInvokeExp().getArgs();
                    List<Var> params = callee.getIR().getParams();
                    for (int i = 0; i < params.size(); ++i) {
                        Var arg = args.get(i);
                        Var param = params.get(i);
                        CSVar csArg = csManager.getCSVar(context, arg);
                        CSVar csParam = csManager.getCSVar(targetContext, param);
                        addPFGEdge(csArg, csParam);
                    }
                    // resolve ret
                    Var lhs = stmt.getLValue();
                    if (lhs != null) {
                        CSVar csLhs = csManager.getCSVar(context, lhs);
                        List<Var> returnVars = callee.getIR().getReturnVars();
                        returnVars.forEach(var -> {
                            CSVar csRetParam = csManager.getCSVar(targetContext, var);
                            addPFGEdge(csRetParam, csLhs);
                        });
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (source.getPointsToSet() != null && !source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
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
            PointsToSet csObjs = entry.pointsToSet();

            PointsToSet delta = propagate(pointer, csObjs);

            if (pointer instanceof CSVar csVar) {
                Context context = csVar.getContext();
                for (CSObj obj : delta) {
                    csVar.getVar()
                            .getStoreFields()
                            .forEach(storeField -> {
                                InstanceField instanceField = csManager.getInstanceField(obj, storeField.getFieldRef().resolve());
                                Var rhs = storeField.getRValue();
                                CSVar csRhs = csManager.getCSVar(context, rhs);
                                addPFGEdge(csRhs, instanceField);
                            });

                    csVar.getVar()
                            .getStoreArrays()
                            .forEach(storeArray -> {
                                ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                                Var rhs = storeArray.getRValue();
                                CSVar csRhs = csManager.getCSVar(context, rhs);
                                addPFGEdge(csRhs, arrayIndex);
                            });

                    csVar.getVar()
                            .getLoadFields()
                            .forEach(loadField -> {
                                InstanceField instanceField = csManager.getInstanceField(obj, loadField.getFieldRef().resolve());
                                Var lhs = loadField.getLValue();
                                CSVar csLhs = csManager.getCSVar(context, lhs);
                                addPFGEdge(instanceField, csLhs);
                            });

                    csVar.getVar()
                            .getLoadArrays()
                            .forEach(loadArray -> {
                                ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                                Var lhs = loadArray.getLValue();
                                CSVar csLhs = csManager.getCSVar(context, lhs);
                                addPFGEdge(arrayIndex, csLhs);
                            });

                    processCall(csVar, obj);
                }
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
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(csObj -> !oldSet.contains(csObj))
                .forEach(delta::addObject);

        if (!delta.isEmpty()) {
            oldSet.addAll(delta);
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> {
                workList.addEntry(succ, delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context context = recv.getContext();
        recv.getVar().getInvokes().forEach(invoke -> {
            JMethod callee = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            Context targetContext = contextSelector.selectContext(csCallSite, recvObj, callee);

            // add this var
            CSVar csThis = csManager.getCSVar(targetContext, callee.getIR().getThis());
            workList.addEntry(csThis, PointsToSetFactory.make(recvObj));
            // resolve csCallee
            CSMethod csMethod = csManager.getCSMethod(targetContext, callee);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod))) {
                addReachable(csMethod);
                // resolve params and args
                List<Var> params = callee.getIR().getParams();
                List<Var> args = invoke.getInvokeExp().getArgs();
                for (int i = 0; i < params.size(); ++i) {
                    Var param = params.get(i);
                    Var arg = args.get(i);
                    CSVar csArg = csManager.getCSVar(context, arg);
                    CSVar csParam = csManager.getCSVar(targetContext, param);
                    addPFGEdge(csArg, csParam);
                }
                // resolve ret
                if (invoke.getLValue() != null) {
                    List<Var> returnVars = callee.getIR().getReturnVars();
                    CSVar csLhs = csManager.getCSVar(context, invoke.getLValue());
                    returnVars.forEach(returnVar -> {
                        CSVar csRet = csManager.getCSVar(targetContext, returnVar);
                        addPFGEdge(csRet, csLhs);
                    });
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
