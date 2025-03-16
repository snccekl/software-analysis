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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Set<Stmt> reachable = new HashSet<>();
        Deque<Stmt> stmts = new ArrayDeque<>();

        reachable.add(cfg.getEntry());
        stmts.add(cfg.getEntry());
        while (!stmts.isEmpty()) {
            Stmt stmt = stmts.poll();
            reachable.add(stmt);
            if (stmt instanceof AssignStmt assignStmt) {
                SetFact<Var> liveVarsResult = liveVars.getResult(assignStmt);
                LValue lhs = assignStmt.getLValue();
                RValue rhs = assignStmt.getRValue();
                if (lhs instanceof Var var && !liveVarsResult.contains(var) && hasNoSideEffect(rhs)) {
                    deadCode.add(stmt);
                }
            }
            if (stmt instanceof If ifStmt) {
                CPFact fact = constants.getOutFact(stmt);
                Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), fact);
                if (value.isConstant()) {
                    Edge.Kind kind = value.getConstant() == 1 ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE;
                    cfg.getOutEdgesOf(ifStmt).stream()
                            .filter(edge -> edge.getKind() == kind)
                            .map(Edge::getTarget)
                            .forEach(stmts::add);
                    continue;
                }
            }
            if (stmt instanceof SwitchStmt switchStmt) {
                Var var = switchStmt.getVar();
                CPFact result = constants.getResult(switchStmt);
                if (result.get(var).isConstant()) {
                    int value = result.get(var).getConstant();
                    boolean matched = cfg.getOutEdgesOf(switchStmt).stream()
                            .filter(edge -> edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == value)
                            .map(Edge::getTarget)
                            .peek(stmts::add)
                            .findAny()
                            .isPresent();
                    if (!matched) {
                        cfg.getOutEdgesOf(switchStmt).stream()
                                .filter(edge -> edge.getKind() == Edge.Kind.SWITCH_DEFAULT)
                                .map(Edge::getTarget)
                                .forEach(stmts::add);
                    }
                    continue;
                }
            }
            cfg.getSuccsOf(stmt).stream()
                    .filter(succ -> !reachable.contains(succ))
                    .forEach(stmts::add);
        }
        ir.getStmts().stream()
                .filter(stmt -> !reachable.contains(stmt))
                .forEach(deadCode::add);

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
