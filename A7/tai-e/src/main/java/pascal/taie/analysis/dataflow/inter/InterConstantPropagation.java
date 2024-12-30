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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
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
        if (stmt instanceof StoreField storeField) {// T.f = x or x.f = y
            if (storeField.isStatic()) {
                for (Stmt loadStmt : icfg) {
                    if (loadStmt instanceof LoadField loadField
                            && loadField.isStatic()
                            && loadField.getFieldRef().resolve() == storeField.getFieldAccess().getFieldRef().resolve()
                            && loadField.getFieldRef().getDeclaringClass() == storeField.getFieldAccess().getFieldRef().getDeclaringClass()) {
                        this.solver.addToWorkList(loadField);
                    }
                }
            } else {
                InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                Var base = instanceFieldAccess.getBase();
                Set<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
                for (Var var : pta.getVars()) {
                    Set<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                    Set<Obj> resSet = new HashSet<>(baseSet);
                    resSet.retainAll(varSet);
                    if (!resSet.isEmpty()) {
                        for (LoadField loadField : var.getLoadFields()) {
                            if (!loadField.isStatic()
                                    && loadField.getFieldRef().resolve() == instanceFieldAccess.getFieldRef().resolve()) {
                                this.solver.addToWorkList(loadField);
                            }
                        }
                    }
                }
            }
        } else if (stmt instanceof LoadField loadField) {// x = T.f or y = x.f
            Value value = Value.getUndef();
            if (loadField.isStatic()) {// x = T.f
                for (Stmt storeStmt : icfg) {
                    if (storeStmt instanceof StoreField storeField
                            && storeField.isStatic()
                            && storeField.getFieldRef().resolve() == loadField.getFieldAccess().getFieldRef().resolve()
                            && storeField.getFieldRef().getDeclaringClass() == loadField.getFieldAccess().getFieldRef().getDeclaringClass()) {
                        value = cp.meetValue(value, this.solver.getResult().getOutFact(storeField).get(storeField.getRValue()));
                    }
                }
            } else {// y = x.f
                InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
                Var base = instanceFieldAccess.getBase();
                Set<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
                for (Var var : pta.getVars()) {
                    Set<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                    Set<Obj> resSet = new HashSet<>(baseSet);
                    resSet.retainAll(varSet);
                    if (!resSet.isEmpty()) {
                        for (StoreField storeField : var.getStoreFields()) {
                            if (!storeField.isStatic()
                                    && storeField.getFieldRef().resolve() == instanceFieldAccess.getFieldRef().resolve()) {
                                value = cp.meetValue(value, this.solver.getResult().getOutFact(storeField).get(storeField.getRValue()));
                            }
                        }
                    }
                }
            }
            CPFact preOut = out.copy();
            out.copyFrom(in);
            out.update(loadField.getLValue(), value);
            return !out.equals(preOut);
        } else if (stmt instanceof StoreArray storeArray) {
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            Var base = arrayAccess.getBase();
            Set<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
            for (Var var : pta.getVars()) {
                Set<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                Set<Obj> resSet = new HashSet<>(baseSet);
                resSet.retainAll(varSet);
                if (!resSet.isEmpty()) {
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        Var loadIndex = loadArray.getArrayAccess().getIndex();
                        CPFact loadOutFact = this.solver.getResult().getOutFact(loadArray);
                        if (isIndexEffect(this.solver.getResult().getOutFact(storeArray).get(arrayAccess.getIndex()), loadOutFact.get(loadIndex))
                                || isIndexEffect(in.get(arrayAccess.getIndex()), loadOutFact.get(loadIndex))) {
                            this.solver.addToWorkList(loadArray);
                        }
                    }
                }
            }
        } else if (stmt instanceof LoadArray loadArray) {// y = x[i]
            ArrayAccess arrayAccess = loadArray.getArrayAccess();
            Var base = arrayAccess.getBase();
            Set<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
            Value value = Value.getUndef();
            for (Var var : pta.getVars()) {
                Set<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                Set<Obj> resSet = new HashSet<>(baseSet);
                resSet.retainAll(varSet);
                if (!resSet.isEmpty()) {
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        Var storeIndex = storeArray.getArrayAccess().getIndex();
                        CPFact storeOutFact = this.solver.getResult().getOutFact(storeArray);
                        if (isIndexEffect(storeOutFact.get(storeIndex), this.solver.getResult().getOutFact(loadArray).get(arrayAccess.getIndex()))
                                || isIndexEffect(storeOutFact.get(storeIndex), in.get(arrayAccess.getIndex()))) {
                            value = cp.meetValue(value, storeOutFact.get(storeArray.getRValue()));
                        }
                    }
                }
            }
            CPFact preOut = out.copy();
            out.copyFrom(in);
            out.update(loadArray.getLValue(), value);
            return !out.equals(preOut);
        }
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt stmt = edge.getSource();
        CPFact ans = out.copy();
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            if (definitionStmt.getLValue() != null) {
                LValue lVal = definitionStmt.getLValue();
                if (lVal instanceof Var v) {
                    if (ConstantPropagation.canHoldInt(v)) {
                        ans.remove(v);
                    }
                }
            }
        }
        return ans;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact ans = new CPFact();
        if (edge.getSource() instanceof Invoke invoke) {
            List<Var> args = invoke.getInvokeExp().getArgs();
            List<Var> params = edge.getCallee().getIR().getParams();
            for (int i = 0; i < args.size(); i++) {
                ans.update(params.get(i), callSiteOut.get(args.get(i)));
            }
        }
        return ans;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact ans = new CPFact();
        Value value = Value.getUndef();
        for (Var v : edge.getReturnVars()) {
            value = cp.meetValue(value, returnOut.get(v));
        }
        if (edge.getCallSite() instanceof Invoke invoke) {
            if (invoke.getResult() != null) {
                ans.update(invoke.getResult(), value);
            }
        }
        return ans;
    }


    private boolean isIndexEffect(Value v1, Value v2) {
        if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant();
        } else return !v1.isUndef() && !v2.isUndef();
    }
}