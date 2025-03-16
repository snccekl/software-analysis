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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
        Set<JMethod> visited = new HashSet<>();
        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod m = worklist.poll();
            if (visited.add(m)) {
                callGraph.addReachableMethod(m);
                callGraph.callSitesIn(m).forEach(cs -> {
                    for (JMethod targetMethod : resolve(cs)) {
                        if (targetMethod != null) {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, targetMethod));
                            worklist.add(targetMethod);
                        }
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<JMethod>();
        MethodRef m = callSite.getMethodRef();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        switch (callKind) {
            case STATIC:
                T.add(m.getDeclaringClass().getDeclaredMethod(m.getSubsignature()));
                break;
            case SPECIAL:
                T.add(dispatch(m.getDeclaringClass(), m.getSubsignature()));
                break;
            case VIRTUAL, INTERFACE:
                Queue<JClass> worklist = new ArrayDeque<>();
                worklist.add(m.getDeclaringClass());
                while (!worklist.isEmpty()) {
                    JClass c = worklist.poll();
                    T.add(dispatch(c, m.getSubsignature()));
                    if (c.isInterface()) {
                        worklist.addAll(hierarchy.getDirectSubinterfacesOf(c));
                        worklist.addAll(hierarchy.getDirectImplementorsOf(c));
                    } else {
                        worklist.addAll(hierarchy.getDirectSubclassesOf(c));
                    }
                }
                break;
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null) {
            return null;
        }
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
