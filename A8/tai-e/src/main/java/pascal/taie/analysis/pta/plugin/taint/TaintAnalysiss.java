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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public CSObj captureTaintObj(JMethod method, Invoke callSite) {
        for (Source source : config.getSources()) {
            JMethod sourceMethod = source.method();
            if (sourceMethod.equals(method) && source.type().equals(method.getReturnType())) {
                return csManager.getCSObj(emptyContext, manager.makeTaint(callSite, source.type()));
            }
        }
        return null;
    }
    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    public void doTaintTransfer(JMethod method, CSVar base, CSCallSite csCallSite) {
        Context recvContext = csCallSite.getContext();
        Invoke callSite = csCallSite.getCallSite();
        CSVar result;
        if(callSite.getResult() == null){
            result = null;
        }
        else{
            result = csManager.getCSVar(recvContext, csCallSite.getCallSite().getResult());
        }
        captureBaseToResult(method, base, result);
        captureArgToBase(method, base, callSite, recvContext);
        captureArgToResult(method, callSite, result, recvContext);
    }
    private void captureBaseToResult(JMethod method, CSVar base, CSVar result) {
        if (base == null) {
            return;
        }
        if (result == null){
            return;
        }
        boolean baseTainted = false;
        for (CSObj csObj : base.getPointsToSet()) {
            baseTainted |= manager.isTaint(csObj.getObject());
        }
        if (baseTainted) {
            config.getTransfers().forEach(transfer -> {
                if (transfer.equals(new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, method.getReturnType()))) {
                    base.getPointsToSet().forEach(csObj -> {
                        if (manager.isTaint(csObj.getObject())) {
                            solver.addTaintEntryToWorkList(result, csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), method.getReturnType())));
                        }
                    });
                }
            });
        }
    }
    private void captureArgToBase(JMethod method, CSVar base, Invoke callSite, Context recvContext) {
        if (base == null) return;
        for (int i = 0; i < method.getParamCount(); ++i) {
            CSVar csArg = csManager.getCSVar(recvContext, callSite.getInvokeExp().getArg(i));
            boolean argTainted = false;
            for (CSObj csObj : csArg.getPointsToSet()) {
                argTainted |= manager.isTaint(csObj.getObject());
            }
            if (argTainted) {
                int finalI = i;
                config.getTransfers().forEach(transfer -> {
                    if (transfer.equals(new TaintTransfer(method, finalI, TaintTransfer.BASE, base.getType()))) {
                        csArg.getPointsToSet().forEach(csObj -> {
                            if (manager.isTaint(csObj.getObject())) {
                                CSObj csTaintObj = csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), base.getType()));
                                solver.addTaintEntryToWorkList(base, csTaintObj);
                            }
                        });
                    }
                });
            }
        }
    }
    private void captureArgToResult(JMethod method, Invoke callSite, CSVar result, Context recvContext){
        if (result != null) {
            for (int i = 0; i < method.getParamCount(); ++i) {
                Var arg = callSite.getInvokeExp().getArg(i);
                CSVar csArg = csManager.getCSVar(recvContext, arg);
                boolean argTainted = false;
                for (CSObj csObj : csArg.getPointsToSet()) {
                    argTainted |= manager.isTaint(csObj.getObject());
                }
                if (argTainted) {
                    int finalI = i;
                    config.getTransfers().forEach(transfer -> {
                        if (transfer.equals(new TaintTransfer(method, finalI, TaintTransfer.RESULT, method.getReturnType()))) {
                            csArg.getPointsToSet().forEach(csObj -> {
                                if (manager.isTaint(csObj.getObject())) {
                                    solver.addTaintEntryToWorkList(result, csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), method.getReturnType())));
                                }
                            });
                        }
                    });
                }
            }
        }
    }
    private void gettransfer(JMethod method, CSVar base, CSVar result, TaintTransfer taintTransfer) {
        config.getTransfers().forEach(transfer -> {
            if (transfer.equals(taintTransfer)) {
                base.getPointsToSet().forEach(csObj -> {
                    if (manager.isTaint(csObj.getObject())) {
                        Obj taintObjAfterTransfer = manager.makeTaint(manager.getSourceCall(csObj.getObject()), method.getReturnType());
                        solver.addTaintEntryToWorkList(result, csManager.getCSObj(emptyContext, taintObjAfterTransfer));
                    }
                });
            }
        });
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
        for (Edge<CSCallSite, CSMethod> callEdge : result.getCSCallGraph().edges().toList()) {
            config.getSinks().forEach(sink -> {
                if (sink.method().equals(callEdge.getCallee().getMethod())) {
                    csManager.getCSVar(callEdge.getCallSite().getContext(), callEdge.getCallSite().getCallSite().getInvokeExp().getArg(sink.index())).getPointsToSet().forEach(csObj -> {
                        if (manager.isTaint(csObj.getObject())) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(csObj.getObject()), callEdge.getCallSite().getCallSite(), sink.index()));
                        }
                    });
                }
            });
        }
        return taintFlows;
    }
}