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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact newfact = new CPFact();
        cfg.getIR().getParams().forEach(para-> {
            if (canHoldInt(para)) {
                newfact.update(para, Value.getNAC());
            }
        });
        return newfact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        else if (v2.isUndef()) {
            return v1;
        }

        if (v1.equals(v2)) {
            return v2;
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (!(stmt instanceof DefinitionStmt<?, ?> definitionStmt)) { return out.copyFrom(in); }

        LValue lValue = definitionStmt.getLValue();
        RValue rValue = definitionStmt.getRValue();
        if (!(lValue instanceof Var key)) { return out.copyFrom(in); }
        if (rValue instanceof Var var) {
            if (!canHoldInt(var)) { return out.copyFrom(in); }
        } else if (rValue instanceof BinaryExp binaryExp) {
            if (!(canHoldInt(binaryExp.getOperand1()) && canHoldInt(binaryExp.getOperand2()))) {
                return out.copyFrom(in);
            }
        } else if (rValue instanceof NegExp negExp) {
            if (!canHoldInt(negExp.getOperand())) {
                return out.copyFrom(in);
            }
        }
        CPFact temp = in.copy();
        temp.update(key, evaluate(rValue, in));
        return out.copyFrom(temp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var var) {
            Value value = in.get(var);
            if (value.isConstant()) {
                return Value.makeConstant(value.getConstant());
            }
            if (value.isUndef()) {
                return Value.getUndef();
            }
            return Value.getNAC();
        }
        if (exp instanceof BinaryExp) {
            in.get(((BinaryExp) exp).getOperand2());
            Value v1 = in.get(((BinaryExp) exp).getOperand1());
            Value v2 = in.get(((BinaryExp) exp).getOperand2());
            if(v1.isNAC() || v2.isNAC()) {
                if (exp instanceof ArithmeticExp) {
                    if ((((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM)
                            && v2.isConstant() && v2.getConstant() == 0) {
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            if(v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
            if(v1.isConstant() && v2.isConstant()){
                if (exp instanceof ArithmeticExp) {
                    if ((((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM)
                            && v2.getConstant() == 0) {
                        return Value.getUndef();
                    }

                    if( ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.ADD) {
                        return Value.makeConstant(v1.getConstant() + v2.getConstant());
                    }

                    if( ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.SUB) {
                        return Value.makeConstant(v1.getConstant() - v2.getConstant());
                    }

                    if( ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.MUL) {
                        return Value.makeConstant(v1.getConstant() * v2.getConstant());
                    }

                    if (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV) {
                        return Value.makeConstant(v1.getConstant() / v2.getConstant());
                    }

                    if( ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM) {
                        return Value.makeConstant(v1.getConstant() % v2.getConstant());
                    }
                }

                if(exp instanceof BitwiseExp) {
                    if(((BitwiseExp) exp).getOperator() == BitwiseExp.Op.AND) {
                        return Value.makeConstant(v1.getConstant() & v2.getConstant());
                    }
                    if(((BitwiseExp) exp).getOperator() == BitwiseExp.Op.OR) {
                        return Value.makeConstant(v1.getConstant() | v2.getConstant());
                    }
                    if(((BitwiseExp) exp).getOperator() == BitwiseExp.Op.XOR) {
                        return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    }
                }

                if(exp instanceof ShiftExp) {
                    if(((ShiftExp) exp).getOperator() == ShiftExp.Op.SHL) {
                        return Value.makeConstant(v1.getConstant() << v2.getConstant());
                    }
                    if(((ShiftExp) exp).getOperator() == ShiftExp.Op.SHR) {
                        return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                    }
                    if(((ShiftExp) exp).getOperator() == ShiftExp.Op.USHR) {
                        return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    }
                }

                if(exp instanceof ConditionExp) {
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.EQ) {
                        return Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                    }
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.NE) {
                        return Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                    }
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.LT) {
                        return Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                    }
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.LE) {
                        return Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                    }
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.GT) {
                        return Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                    }
                    if(((ConditionExp) exp).getOperator() == ConditionExp.Op.GE) {
                        return Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                    }
                }
            }
            return Value.getUndef();
        }
        if (exp instanceof NegExp negExp) {
            if (in.get(negExp.getOperand()).isNAC()) {
                return Value.getNAC();
            }
            if (in.get(negExp.getOperand()).isConstant()) {
                int value = in.get(negExp.getOperand()).getConstant();
                return Value.makeConstant(-value);
            }
            return Value.getUndef();
        }
        if (exp instanceof NewExp) {
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
