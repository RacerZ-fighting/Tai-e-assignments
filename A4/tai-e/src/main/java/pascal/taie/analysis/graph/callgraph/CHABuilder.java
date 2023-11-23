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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        ArrayDeque<JMethod> queue = new ArrayDeque<>();
        queue.add(entry);
        while (!queue.isEmpty()) {
            JMethod method = queue.poll();
            callGraph.addReachableMethod(method);
            callGraph.getCallSitesIn(method).forEach(callSite -> {
                resolve(callSite).forEach(target -> {
                    if (!callGraph.contains(target)) {
                        queue.add(target);
                    }
                    callGraph.addEdge(new Edge<>(
                            CallGraphs.getCallKind(callSite), callSite, target));
                });
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        HashSet<JMethod> target = new HashSet<>();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        switch (callKind) {
            case SPECIAL, STATIC -> {
                JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
                JMethod method = dispatch(declaringClass, subsignature);
                if (method != null) {
                    target.add(method);
                }
                break;
            }
            case VIRTUAL, INTERFACE -> {
                JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
                // TODO: 这里存在多级子类结构
                LinkedList<JClass> queue = new LinkedList<>();
                queue.add(declaringClass);
                while (!queue.isEmpty()) {
                    JClass jClass = queue.poll();
                    JMethod method = dispatch(jClass, subsignature);
                    if (method != null) {
                        target.add(method);
                    }
                    if (jClass.isInterface()) {
                        queue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                        queue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    } else {
                        queue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                    }
                }
                break;
            }
            default -> throw new RuntimeException("unsupported invoke type: " + callSite);
        }

        return target;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JClass curClass = jclass;
        while (curClass != null) {
            JMethod method = curClass.getDeclaredMethod(subsignature);
            if (method != null && !method.isAbstract()) {
                return method;
            }
            curClass = curClass.getSuperClass();
        }
        return null;
    }
}
