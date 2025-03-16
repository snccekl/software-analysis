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
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
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
        if(stmt instanceof LoadField loadField){
            Value value = Value.getUndef();
            if(loadField.isStatic()){
                for (Stmt storestmt : this.icfg) {
                    if(storestmt instanceof StoreField storeField && storeField.isStatic()){
                        boolean isAlias;
                        FieldAccess loadfieldAccess = loadField.getFieldAccess();
                        FieldAccess storefieldAccess = storeField.getFieldAccess();
                        if(!loadField.getFieldRef().resolve().equals(storeField.getFieldRef().resolve())){
                            isAlias = false;
                        }
                        else if(loadfieldAccess instanceof InstanceFieldAccess loadInstanceFieldAccess){
                            InstanceFieldAccess storeInstanceFieldAccess = (InstanceFieldAccess) storefieldAccess;
                            Set<Obj> b1Pts = new HashSet<>(pta.getPointsToSet(loadInstanceFieldAccess.getBase()));
                            Set<Obj> b2Pts = new HashSet<>(pta.getPointsToSet(storeInstanceFieldAccess.getBase()));
                            b1Pts.retainAll(b2Pts);
                            isAlias = !b1Pts.isEmpty();
                        }
                        else {
                            isAlias = loadfieldAccess.getFieldRef().getDeclaringClass().equals(storefieldAccess.getFieldRef().getDeclaringClass());
                        }
                        if(isAlias) {
                            value = cp.meetValue(value, this.solver.result.getOutFact(storeField).get(storeField.getRValue()));
                        }
                    }
                }
            }
            else{
                for (Stmt storestmt : this.icfg) {
                    if(storestmt instanceof StoreField storeField && !storeField.isStatic()){
                        boolean isAlias;
                        FieldAccess loadfieldAccess = loadField.getFieldAccess();
                        FieldAccess storefieldAccess = storeField.getFieldAccess();
                        if(!loadField.getFieldRef().resolve().equals(storeField.getFieldRef().resolve())){
                            isAlias = false;
                        }
                        else if(loadfieldAccess instanceof InstanceFieldAccess loadInstanceFieldAccess){
                            InstanceFieldAccess storeInstanceFieldAccess = (InstanceFieldAccess) storefieldAccess;
                            Set<Obj> b1Pts = new HashSet<>(pta.getPointsToSet(loadInstanceFieldAccess.getBase()));
                            Set<Obj> b2Pts = new HashSet<>(pta.getPointsToSet(storeInstanceFieldAccess.getBase()));
                            b1Pts.retainAll(b2Pts);
                            isAlias = !b1Pts.isEmpty();
                        }
                        else {
                            isAlias = loadfieldAccess.getFieldRef().getDeclaringClass().equals(storefieldAccess.getFieldRef().getDeclaringClass());
                        }
                        if(isAlias) {
                            value = cp.meetValue(Value.getUndef(), this.solver.result.getOutFact(storeField).get(storeField.getRValue()));
                        }
                    }
                }
            }
            CPFact temp = in.copy();
            temp.update(loadField.getLValue(), value);
            return out.copyFrom(temp);
        }
        if(stmt instanceof StoreField storeField){
                for(Var var : pta.getVars()){
                    for (LoadField loadField : var.getLoadFields()) {
                        boolean isAlias;
                        FieldAccess loadfieldAccess = loadField.getFieldAccess();
                        FieldAccess storefieldAccess = storeField.getFieldAccess();
                        if(!loadField.getFieldRef().resolve().equals(storeField.getFieldRef().resolve())){
                            isAlias = false;
                        }
                        else if(loadfieldAccess instanceof InstanceFieldAccess loadInstanceFieldAccess){
                            InstanceFieldAccess storeInstanceFieldAccess = (InstanceFieldAccess) storefieldAccess;
                            Set<Obj> b1Pts = new HashSet<>(pta.getPointsToSet(loadInstanceFieldAccess.getBase()));
                            Set<Obj> b2Pts = new HashSet<>(pta.getPointsToSet(storeInstanceFieldAccess.getBase()));
                            b1Pts.retainAll(b2Pts);
                            isAlias = !b1Pts.isEmpty();
                        }
                        else {
                            isAlias = loadfieldAccess.getFieldRef().getDeclaringClass().equals(storefieldAccess.getFieldRef().getDeclaringClass());
                        }
                        if (isAlias) {
                            if(!this.solver.workList.contains(loadField)){
                                this.solver.workList.offer(loadField);
                            }
                        }
                    }
                }
        }
        if(stmt instanceof LoadArray loadArray){
            Value value = Value.getUndef();
            for (Stmt storestmt : this.icfg) {
                if(storestmt instanceof StoreArray storeArray){
                    boolean isAlias;
                    ArrayAccess loadAccess = loadArray.getArrayAccess();
                    ArrayAccess storeAccess = storeArray.getArrayAccess();

                    Set<Obj> b1Pts = new HashSet<>(pta.getPointsToSet(loadAccess.getBase()));
                    Set<Obj> b2Pts = new HashSet<>(pta.getPointsToSet(storeAccess.getBase()));
                    b1Pts.retainAll(b2Pts);
                    if (b1Pts.isEmpty()) {
                        isAlias = false;
                    }
                    else {
                        Value index1 = this.solver.result.getInFact(loadArray).get(loadAccess.getIndex());
                        Value index2 = this.solver.result.getInFact(storeArray).get(storeAccess.getIndex());
                        isAlias = index1.isNAC() && !index2.isUndef() ||
                                index2.isNAC() && !index1.isUndef() ||
                                index1.isConstant() && index2.isConstant() && index1.getConstant() == index2.getConstant();
                    }
                    if(isAlias){
                        value = cp.meetValue(value, this.solver.result.getOutFact(storeArray).get(storeArray.getRValue()));
                    }
                }
            }
            CPFact temp = in.copy();
            temp.update(loadArray.getLValue(), value);
            return out.copyFrom(temp);
        }
        if(stmt instanceof StoreArray storeArray){
            for (Var var : pta.getVars()){
                for(LoadArray loadArray : var.getLoadArrays()){
                    boolean isAlias;
                    ArrayAccess loadAccess = loadArray.getArrayAccess();
                    ArrayAccess storeAccess = storeArray.getArrayAccess();

                    Set<Obj> b1Pts = new HashSet<>(pta.getPointsToSet(loadAccess.getBase()));
                    Set<Obj> b2Pts = new HashSet<>(pta.getPointsToSet(storeAccess.getBase()));
                    b1Pts.retainAll(b2Pts);
                    if (b1Pts.isEmpty()) {
                        isAlias = false;
                    }
                    else {
                        Value index1 = this.solver.result.getInFact(loadArray).get(loadAccess.getIndex());
                        Value index2 = this.solver.result.getInFact(storeArray).get(storeAccess.getIndex());
                        isAlias = index1.isNAC() && !index2.isUndef() ||
                                index2.isNAC() && !index1.isUndef() ||
                                index1.isConstant() && index2.isConstant() && index1.getConstant() == index2.getConstant();
                    }
                    if(isAlias){
                        if(!this.solver.workList.contains(loadArray)){
                            this.solver.workList.offer(loadArray);
                        }
                    }
                }
            }
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
        Invoke callSite = (Invoke) edge.getSource();
        CPFact newFact = out.copy();
        if (callSite.getResult() != null) {
            newFact.remove(callSite.getResult());
        }
        return newFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact newFact = new CPFact();
        Invoke invoke = (Invoke) edge.getSource();
        for(int i = 0;i<invoke.getInvokeExp().getArgCount();i++) {
            newFact.update(edge.getCallee().getIR().getParam(i), callSiteOut.get(invoke.getInvokeExp().getArg(i)));
        }
        return newFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact newFact = newInitialFact();
        Stmt cs = edge.getCallSite();
        if(cs.getDef().isPresent()){
            Value value = Value.getUndef();
            for (Var reVar : edge.getReturnVars()) {
                value = cp.meetValue(value, returnOut.get(reVar));
            }
            if (cs.getDef().get() instanceof Var lhs) {
                newFact.update(lhs, value);
            }
        }
        return newFact;
    }
}
