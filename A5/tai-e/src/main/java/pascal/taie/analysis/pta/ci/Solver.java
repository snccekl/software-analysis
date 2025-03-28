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
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
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
        if (!callGraph.contains(method) && callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet flowedInObjs = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(varPtr, flowedInObjs);
            return null;
        }

        public Void visit(Invoke stmt) {
            // TODO - finish me
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null, stmt);
                Edge<Invoke, JMethod> edge = new Edge(CallKind.STATIC, stmt, callee);
                if(callGraph.addEdge(edge)){
                    addReachable(callee);
                    InvokeExp exp = stmt.getInvokeExp();
                    if(exp != null){
                        List<Var> args = exp.getArgs();
                        for(int i = 0; i < args.size(); i++){
                            Var var = args.get(i);
                            VarPtr varPtr = pointerFlowGraph.getVarPtr(var);
                            VarPtr fPtr = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                            addPFGEdge(varPtr, fPtr);
                        }
                    }
                    Var resultVar = stmt.getResult();
                    if (resultVar != null) {
                        VarPtr resultVarPtr = pointerFlowGraph.getVarPtr(resultVar);
                        for (Var returnVar : callee.getIR().getReturnVars()) {
                            VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                            addPFGEdge(returnVarPtr, resultVarPtr);
                        }
                    }
                }
            }
            return null;
        }

        public Void visit(Copy stmt){
            Var LValue = stmt.getLValue();
            Var RValue = stmt.getRValue();
            VarPtr lPtr = pointerFlowGraph.getVarPtr(LValue);
            VarPtr rPtr = pointerFlowGraph.getVarPtr(RValue);
            addPFGEdge(rPtr, lPtr);
            return null;
        }

        public Void visit(LoadArray stmt){
            return  StmtVisitor.super.visit(stmt);
        }

        public Void visit(StoreArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        public Void visit(LoadField stmt){
            JField sField = stmt.getFieldRef().resolve();
            if (sField.isStatic()) {
                StaticField sPtr = pointerFlowGraph.getStaticField(sField);
                Var LValue = stmt.getLValue();
                VarPtr tPtr = pointerFlowGraph.getVarPtr(LValue);
                addPFGEdge(sPtr, tPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            JField sField = stmt.getFieldRef().resolve();
            if (sField.isStatic()) {
                StaticField sPtr = pointerFlowGraph.getStaticField(sField);
                Var RValue = stmt.getRValue();
                VarPtr rPtr = pointerFlowGraph.getVarPtr(RValue);
                addPFGEdge(rPtr, sPtr);
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
            PointsToSet sourceSet = source.getPointsToSet();
            if (!sourceSet.isEmpty()) {
                workList.addEntry(target, sourceSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet dta = propagate(pointer, pts);

            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                dta.forEach(obj->{
                    var.getLoadFields().forEach(loadField->{
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    });
                    var.getStoreFields().forEach(storeField->{
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve()));
                    });
                    var.getLoadArrays().forEach(loadArray->{
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    });
                    var.getStoreArrays().forEach(storeArray->{
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(obj));
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
        PointsToSet dta = new PointsToSet();
        PointsToSet current = pointer.getPointsToSet();
        if (!pointsToSet.isEmpty()) {
            for (Obj obj : pointsToSet) {
                if (!current.contains(obj)) {
                    current.addObject(obj);
                    dta.addObject(obj);
                }
            }
        }
        if(!dta.isEmpty()){
            for (Pointer predPtr : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(predPtr, dta);
            }
        }
        return dta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, invoke);
            Pointer thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(thisPtr, new PointsToSet(recv));

            CallKind callKind;
            if (invoke.isStatic()) { callKind = CallKind.STATIC; }
            else if (invoke.isSpecial()) { callKind = CallKind.SPECIAL; }
            else if (invoke.isInterface()) { callKind = CallKind.INTERFACE; }
            else if (invoke.isVirtual()) { callKind = CallKind.VIRTUAL; }
            else if (invoke.isDynamic()) { callKind = CallKind.DYNAMIC; }
            else { callKind = CallKind.OTHER; }

            if (callGraph.addEdge(new Edge<>(callKind, invoke, callee))) {
                addReachable(callee);
                InvokeExp exp = invoke.getInvokeExp();
                if (exp != null) {
                    List<Var> args = exp.getArgs();
                    for (int i = 0; i < args.size(); i++) {
                        Var arg = args.get(i);
                        VarPtr argPtr = pointerFlowGraph.getVarPtr(arg);
                        VarPtr fPtr = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                        addPFGEdge(argPtr, fPtr);
                    }
                }
                Var resultVar = invoke.getResult();
                if (resultVar != null) {
                    VarPtr resultVarPtr = pointerFlowGraph.getVarPtr(resultVar);
                    for (Var returnVar : callee.getIR().getReturnVars()) {
                        VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                        addPFGEdge(returnVarPtr, resultVarPtr);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the invoke
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param invoke the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke invoke) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, invoke);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
