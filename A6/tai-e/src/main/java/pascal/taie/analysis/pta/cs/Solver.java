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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
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
        if (callGraph.addReachableMethod(csMethod)) {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(new StmtProcessor(csMethod));
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            CSVar varPtr = csManager.getCSVar(context,stmt.getLValue());
            PointsToSet flowedInObjs = PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt)), heapModel.getObj(stmt)));
            workList.addEntry(varPtr, flowedInObjs);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var LValue = stmt.getLValue();
            Var RValue = stmt.getRValue();
            CSVar sourcePtr = csManager.getCSVar(context, RValue);
            CSVar targetPtr = csManager.getCSVar(context, LValue);
            addPFGEdge(sourcePtr, targetPtr);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite callSite = csManager.getCSCallSite(context, stmt);
                Context ctx = contextSelector.selectContext(callSite, callee);
                CSMethod targetMethod = csManager.getCSMethod(ctx, callee);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, callSite, targetMethod))){
                    addReachable(targetMethod);
                    InvokeExp exp = stmt.getInvokeExp();
                    if(exp != null){
                        List<Var> args = exp.getArgs();
                        for(int i = 0; i < args.size(); i++){
                            CSVar argPtr = csManager.getCSVar(context, args.get(i));
                            CSVar paramPtr = csManager.getCSVar(ctx, callee.getIR().getParams().get(i));
                            addPFGEdge(argPtr, paramPtr);
                        }
                    }
                    Var resultVar = stmt.getResult();
                    if(resultVar != null){
                        CSVar resultPtr = csManager.getCSVar(context, resultVar);
                        for(Var returnVar : callee.getIR().getReturnVars()){
                            CSVar returnPtr = csManager.getCSVar(ctx, returnVar);
                            addPFGEdge(returnPtr, resultPtr);
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            JField sField = stmt.getFieldRef().resolve();
            if (sField.isStatic()) {
                StaticField sPtr = csManager.getStaticField(sField);
                Var LValue = stmt.getLValue();
                CSVar tPtr = csManager.getCSVar(context,LValue);
                addPFGEdge(sPtr, tPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            JField sField = stmt.getFieldRef().resolve();
            if (sField.isStatic()) {
                StaticField sPtr = csManager.getStaticField(sField);
                Var RValue = stmt.getRValue();
                CSVar rPtr = csManager.getCSVar(context,RValue);
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
            PointsToSet setFromSource = source.getPointsToSet();
            if (!setFromSource.isEmpty()) {
                workList.addEntry(target, setFromSource);
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
            PointsToSet dta = propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof CSVar csvar) {
                Var var = csvar.getVar();
                Context context = csvar.getContext();
                dta.forEach(csobj->{
                    var.getLoadFields().forEach(loadField->{
                        addPFGEdge(csManager.getInstanceField(csobj, loadField.getFieldRef().resolve()), csManager.getCSVar(context, loadField.getLValue()));
                    });
                    var.getStoreFields().forEach(storeField->{
                        addPFGEdge(csManager.getCSVar(context, storeField.getRValue()), csManager.getInstanceField(csobj, storeField.getFieldRef().resolve()));
                    });
                    var.getLoadArrays().forEach(loadArray->{
                        addPFGEdge(csManager.getArrayIndex(csobj), csManager.getCSVar(context, loadArray.getLValue()));
                    });
                    var.getStoreArrays().forEach(storeArray->{
                        addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()), csManager.getArrayIndex(csobj));
                    });
                    processCall(csvar, csobj);
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
        PointsToSet dta = PointsToSetFactory.make();
        PointsToSet current = pointer.getPointsToSet();
        if (!pointsToSet.isEmpty()) {
            pointsToSet.forEach(obj->{
                if (!current.contains(obj)) {
                    current.addObject(obj);
                    dta.addObject(obj);
                }
            });
        }
        if(!dta.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ->{
                workList.addEntry(succ, dta);
            });
        }
        return dta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        Context context = recv.getContext();
        for(Invoke invoke: var.getInvokes()){
            JMethod callee = resolveCallee(recvObj, invoke);
            CSCallSite callSite = csManager.getCSCallSite(context, invoke);
            Context ctx = contextSelector.selectContext(callSite, recvObj, callee);
            CSMethod targetMethod = csManager.getCSMethod(ctx, callee);
            Context ctxrecv = recv.getContext();
            workList.addEntry(csManager.getCSVar(ctx, callee.getIR().getThis()), PointsToSetFactory.make(recvObj));
            CallKind callKind;
            if (invoke.isStatic()) { callKind = CallKind.STATIC; }
            else if (invoke.isSpecial()) { callKind = CallKind.SPECIAL; }
            else if (invoke.isInterface()) { callKind = CallKind.INTERFACE; }
            else if (invoke.isVirtual()) { callKind = CallKind.VIRTUAL; }
            else if (invoke.isDynamic()) { callKind = CallKind.DYNAMIC; }
            else { callKind = CallKind.OTHER; }

            if(callGraph.addEdge(new Edge<>(callKind, callSite, targetMethod))){
                addReachable(targetMethod);
                InvokeExp exp = invoke.getInvokeExp();
                if(exp != null){
                    List<Var> args = exp.getArgs();
                    for(int i = 0; i < args.size(); i++){
                        CSVar argPtr = csManager.getCSVar(ctxrecv, args.get(i));
                        CSVar paramPtr = csManager.getCSVar(ctx, callee.getIR().getParams().get(i));
                        addPFGEdge(argPtr, paramPtr);
                    }
                }
                Var resultVar = invoke.getResult();
                if(resultVar != null){
                    CSVar resultPtr = csManager.getCSVar(ctxrecv, resultVar);
                    for(Var returnVar : callee.getIR().getReturnVars()){
                        CSVar returnPtr = csManager.getCSVar(ctx, returnVar);
                        addPFGEdge(returnPtr, resultPtr);
                    }
                }
            }
        }
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
}callSite1 = csCallSite.getCallSite();
                Context calleeContext = csMethod.getContext();
                Context recvContext = csCallSite.getContext();

                for (int i = 0; i < method1.getParamCount(); ++i) {
                    CSVar sourcePtr = csManager.getCSVar(recvContext, callSite1.getInvokeExp().getArg(i));
                    CSVar targetPtr = csManager.getCSVar(calleeContext, method1.getIR().getParam(i));
                    addPFGEdge(sourcePtr, targetPtr);
                }
                Var resultVar = callSite1.getResult();
                if (resultVar != null) {
                    CSVar resultPtr = csManager.getCSVar(recvContext, resultVar);
                    for (Var returnVar : method1.getIR().getReturnVars()) {
                        CSVar returnPtr = csManager.getCSVar(calleeContext, returnVar);
                        addPFGEdge(returnPtr, resultPtr);
                    }

                    // deal with taint analysis: call(source)
                    CSObj taintObj = taintAnalysis.captureTaintObj(method1, callSite1