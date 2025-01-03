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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private Map<CSVar, Set<Invoke>> taintTransfers;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.taintTransfers = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
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
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
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

        @Override
        public Void visit(New stmt) {
            workList.addEntry(
                    csManager.getCSVar(this.context, stmt.getLValue()),
                    PointsToSetFactory.make(
                            csManager.getCSObj(
                                    contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt)),
                                    heapModel.getObj(stmt)
                            )
                    )
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke callSite) {
            if (callSite.isStatic()) {
                JMethod callee = resolveCallee(null, callSite);
                CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                processOneCall(csCallSite, csManager.getCSMethod(calleeContext, callee));
                transferTaint(csCallSite, callee, null);
            }
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                if (stmt instanceof Invoke invoke) {
                    for (Var arg : invoke.getInvokeExp().getArgs()) {
                        CSVar var = csManager.getCSVar(context, arg);
                        Set<Invoke> invokes = taintTransfers.getOrDefault(var, new HashSet<>());
                        invokes.add(invoke);
                        taintTransfers.put(var, invokes);
                    }
                }
            }
            return null;
        }
    }

    private void transferTaint(CSCallSite csCallSite, JMethod callee, CSVar base) {
        taintAnalysis.handleTaintTransfer(csCallSite, callee, base).forEach(varObjPair -> {
            Var var = varObjPair.first();
            Obj obj = varObjPair.second();
            CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), obj);
            Pointer ptr = csManager.getCSVar(csCallSite.getContext(), var);
            workList.addEntry(ptr, PointsToSetFactory.make(csObj));
        });
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry head = workList.pollEntry();
            PointsToSet delta = propagate(head.pointer(), head.pointsToSet());
            if (head.pointer() instanceof CSVar varptr) {
                Var var = varptr.getVar();
                for (CSObj obj : delta) {
                    for (StoreField storeField : var.getStoreFields()) {
                        addPFGEdge(
                                csManager.getCSVar(varptr.getContext(), storeField.getRValue()),
                                csManager.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );
                    }
                    for (LoadField loadField : var.getLoadFields()) {
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                csManager.getCSVar(varptr.getContext(), loadField.getLValue())
                        );
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(varptr.getContext(), storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(varptr.getContext(), loadArray.getLValue())
                        );
                    }
                    // ProcessCall
                    processCall(varptr, obj);
                    // TaintTransfer
                    if (taintAnalysis.isTaint(obj.getObject())) {
                        taintTransfers.getOrDefault(varptr, new HashSet<>()).forEach(invoke -> {
                            CSCallSite csCallSite = csManager.getCSCallSite(varptr.getContext(), invoke);
                            if (invoke.getInvokeExp() instanceof InvokeInstanceExp exp) {
                                CSVar recv = csManager.getCSVar(varptr.getContext(), exp.getBase());
                                result.getPointsToSet(recv).forEach(recvObj -> {
                                    JMethod callee = resolveCallee(recvObj, invoke);
                                    transferTaint(csCallSite, callee, recv);
                                });
                            } else {
                                JMethod callee = resolveCallee(null, invoke);
                                transferTaint(csCallSite, callee, null);
                            }
                        });
                    }
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
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet receiver = pointer.getPointsToSet();
        for (CSObj obj : pointsToSet) {
            if (!receiver.contains(obj)) {
                delta.addObject(obj);
                receiver.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, delta);
            }
        }
        return delta;
    }

    private void processOneCall(CSCallSite csCallSite, CSMethod callee) {
        Invoke invoke = csCallSite.getCallSite();
        Obj obj = taintAnalysis.produceTaintObj(invoke, callee.getMethod());
        Var lVar = csCallSite.getCallSite().getLValue();
        if (obj != null && lVar != null) {
            CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), obj);
            Pointer ptr = csManager.getCSVar(csCallSite.getContext(), lVar);
            workList.addEntry(ptr, PointsToSetFactory.make(csObj));
        }
        Context callerContext = csCallSite.getContext();
        Context targetContext = callee.getContext();
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, callee))) {
            addReachable(callee);
            List<Var> args = callee.getMethod().getIR().getParams();
            for (int i = 0; i < args.size(); i++) {
                addPFGEdge(
                        csManager.getCSVar(callerContext, invoke.getRValue().getArg(i)),
                        csManager.getCSVar(targetContext, args.get(i))
                );
            }
            if (invoke.getLValue() != null) {
                for (Var ret : callee.getMethod().getIR().getReturnVars()) {
                    addPFGEdge(
                            csManager.getCSVar(targetContext, ret),
                            csManager.getCSVar(callerContext, invoke.getLValue())
                    );
                }
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(callSite -> {
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            JMethod callee = resolveCallee(recvObj, callSite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            processOneCall(csCallSite, csCallee);
            transferTaint(csCallSite, callee, recv);
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
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}