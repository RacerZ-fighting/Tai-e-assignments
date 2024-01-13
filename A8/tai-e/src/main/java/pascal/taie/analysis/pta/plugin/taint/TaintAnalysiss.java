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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public final HashMap<JMethod, Set<CSCallSite>> csSinks;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        csSinks = new HashMap<>();
        logger.info(config);
    }

    // TODO - finish me
    public boolean isSource(JMethod method, Type type) {
        return config.getSources().contains(new Source(method, type));
    }

    public boolean isSink(JMethod method, int index) {
        return config.getSinks().contains(new Sink(method, index));
    }

    public boolean isTaintTransfer(JMethod method, String from, String to, Type type) {
        return config.getTransfers().contains(
                new TaintTransfer(method, TaintTransfer.toInt(from),
                        TaintTransfer.toInt(to), type));
    }

    public void addSink(JMethod sink, CSCallSite csCallSite) {
        Set<CSCallSite> siteSet = csSinks.getOrDefault(sink, new HashSet<>());
        siteSet.add(csCallSite);
        csSinks.put(sink, siteSet);
    }

    public Obj makeTaint(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        config.getSinks().forEach(sink -> {
            JMethod method = sink.method();
            int index = sink.index();

            Set<CSCallSite> csCallSites = csSinks.get(method);
            // 需要获得指定 sink 方法在 call graph 上的所有调用点
            if (csCallSites != null) {
                csCallSites.forEach(csCallSite -> {
                    // c:ai
                    Var arg = csCallSite.getCallSite().getInvokeExp().getArg(index);
                    CSVar csArg = csManager.getCSVar(csCallSite.getContext(), arg);
                    result.getPointsToSet(csArg).forEach(csObj -> {
                        if (manager.isTaint(csObj.getObject())) {
                            Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                            taintFlows.add(new TaintFlow(sourceCall, csCallSite.getCallSite(), index));
                        }
                    });
                });
            }
        });

        return taintFlows;
    }
}
