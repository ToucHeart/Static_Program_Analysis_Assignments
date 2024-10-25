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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.security.Key;

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
        return new CPFact();
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var:fact.keySet()){
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            Value res = meetValue(v1, v2);
            target.update(var, res);
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
        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() != v2.getConstant()) {
                return Value.getNAC();
            } else {
                return v1;
            }
        }
        if (v1.isConstant())
            return v1;
        if (v2.isConstant())
            return v2;
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return false;
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
        if (exp instanceof Var) {
            Var v = (Var) exp;
            return in.get(v);
        }
        if (exp instanceof IntLiteral) {
            IntLiteral i = (IntLiteral) exp;
            return Value.makeConstant(i.getValue());
        }
        if (exp instanceof BinaryExp) {
            BinaryExp bin_exp = (BinaryExp) exp;
            Value val1 = in.get((Var) bin_exp.getOperand1());
            Value val2 = in.get((Var) bin_exp.getOperand2());
            if (val1.isConstant() && val2.isConstant()) {
                if (bin_exp instanceof ArithmeticExp) {
                    String op_str = ((ArithmeticExp) bin_exp).getOperator().toString();
                    switch (op_str) {
                        case "+":
                            return Value.makeConstant(val1.getConstant() + val2.getConstant());
                        case "-":
                            return Value.makeConstant(val1.getConstant() - val2.getConstant());
                        case "*":
                            return Value.makeConstant(val1.getConstant() * val2.getConstant());
                        case "/": {
                            if (val2.getConstant() != 0) {
                                return Value.makeConstant(val1.getConstant() / val2.getConstant());
                            } else {
                                return Value.getUndef();
                            }
                        }
                        case "%": {
                            if (val2.getConstant() != 0) {
                                return Value.makeConstant(val1.getConstant() % val2.getConstant());
                            } else {
                                return Value.getUndef();
                            }
                        }
                    }
                } else if (bin_exp instanceof ConditionExp) {
                    String op_str = ((ConditionExp) bin_exp).getOperator().toString();
                    switch (op_str) {
                        case "==": {
                            if (val1.getConstant() == val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case "!=": {
                            if (val1.getConstant() != val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case ">=": {
                            if (val1.getConstant() >= val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case "<=": {
                            if (val1.getConstant() <= val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case ">": {
                            if (val1.getConstant() > val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case "<": {
                            if (val1.getConstant() < val2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                    }
                } else if (bin_exp instanceof ShiftExp) {
                    String op_str = ((ShiftExp) bin_exp).getOperator().toString();
                    switch (op_str) {
                        case ">>":
                            return Value.makeConstant(val1.getConstant() >> val2.getConstant());
                        case "<<":
                            return Value.makeConstant(val1.getConstant() << val2.getConstant());
                        case ">>>":
                            return Value.makeConstant(val1.getConstant() >>> val2.getConstant());
                    }
                } else if (bin_exp instanceof BitwiseExp) {
                    String op_str = ((BitwiseExp) bin_exp).getOperator().toString();
                    switch (op_str) {
                        case "|":return Value.makeConstant(val1.getConstant() | val2.getConstant());
                        case "&":return Value.makeConstant(val1.getConstant() & val2.getConstant());
                        case "^":return Value.makeConstant(val1.getConstant() ^ val2.getConstant());
                    }
                }
            } else if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
