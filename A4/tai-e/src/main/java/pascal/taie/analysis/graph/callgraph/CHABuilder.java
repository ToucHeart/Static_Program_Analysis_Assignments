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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

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
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.remove();
            if(!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                for(Invoke invoke:callGraph.getCallSitesIn(method)){
                    for(JMethod target:resolve(invoke)){
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,target));
                        workList.add(target);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        CallKind callkind = CallGraphs.getCallKind(callSite);
        Set<JMethod> methods = new HashSet<>();
        JClass method_class = callSite.getMethodRef().getDeclaringClass();
        Subsignature signature = callSite.getMethodRef().getSubsignature();
        if(callkind == CallKind.STATIC){
            methods.add(method_class.getDeclaredMethod(signature));
        }else if(callkind == CallKind.SPECIAL) {
            methods.add(dispatch(method_class, signature));
        }else if(callkind == CallKind.VIRTUAL||callkind == CallKind.INTERFACE){
            Queue<JClass> queue = new LinkedList<>();
            queue.add(method_class);
            while(!queue.isEmpty()){
                JClass clazz = queue.remove();
                JMethod target = dispatch(clazz, signature);
                if(target != null){
                    methods.add(target);
                }
                if(clazz.isInterface()){
                    queue.addAll(hierarchy.getDirectImplementorsOf(clazz));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(clazz));
                }
                else{
                    queue.addAll(hierarchy.getDirectSubclassesOf(clazz));
                }
            }
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass==null)
            return null;
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method!=null&&!method.isAbstract()) {
            return method;
        }
        if(jclass.getSuperClass()!=null){
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
