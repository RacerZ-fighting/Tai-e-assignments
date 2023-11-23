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
import pascal.taie.util.AnalysisException;

import java.util.List;

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
        CPFact mappings = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            if (canHoldInt(param)) {
                mappings.update(param, Value.getNAC());
            }
        }
        return mappings;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach(((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        }));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.equals(v2)) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt) {
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lValue instanceof Var lhs) {
                // 右式视为表达式
                Exp rhs = ((DefinitionStmt<?, ?>) stmt).getRValue();
                // gen U (IN[s] - {(x, _)})
                boolean changed = false;
                for (Var inVar : in.keySet()) {
                    if (!lhs.equals(inVar)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                // 如果 lhs 不是规定范围类型内的变量，则忽略，因为它不会出现在 CPFact 当中 :)
                return canHoldInt(lhs) ?
                        out.update(lhs, evaluate(rhs, in)) || changed :
                        changed;
            }
        }
        // other cases: identical function
        return out.copyFrom(in);
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
        if (exp instanceof IntLiteral) {    // 处理字面量
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var var) {    // 处理变量
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        } else if (exp instanceof BinaryExp binaryExp) {
            BinaryExp.Op op = binaryExp.getOperator();
            // 精妙之处：套用 evaluate 来获得操作数的值
            Value var1 = evaluate(binaryExp.getOperand1(), in);
            Value var2 = evaluate(binaryExp.getOperand2(), in);
            // 处理除 0 错误：var1 不论是否为常数，都会返回 UDF :(
            if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) &&
                      var2.isConstant() && var2.getConstant() == 0) {
                return Value.getUndef();
            }
            // val(y) op val(z)
            if (var1.isConstant() && var2.isConstant()) {
                // 函数重载调用
                return Value.makeConstant(evaluate(op, var1.getConstant(), var2.getConstant()));
            }
            // if val(y) or val(z) is NAC
            if (var1.isNAC() || var2.isNAC()) {
                return Value.getNAC();
            }
            // otherwise
            return Value.getUndef();
        }
        // other cases: safe approximation
        return Value.getNAC();
    }

    public static int evaluate(BinaryExp.Op op, int i1, int i2) {
        if (op instanceof ArithmeticExp.Op) {
            return switch ((ArithmeticExp.Op) op) {
                case ADD -> i1 + i2;
                case DIV -> i1 / i2;
                case MUL -> i1 * i2;
                case SUB -> i1 - i2;
                case REM -> i1 % i2;
            };
        } else if (op instanceof ConditionExp.Op) {
            return switch ((ConditionExp.Op) op) {
                case EQ -> i1 == i2 ? 1 : 0;
                case GE -> i1 >= i2 ? 1 : 0;
                case GT -> i1 > i2 ? 1 : 0;
                case LE -> i1 <= i2 ? 1 : 0;
                case LT -> i1 < i2 ? 1 : 0;
                case NE -> i1 != i2 ? 1 : 0;
            };
        } else if (op instanceof ShiftExp.Op) {
            return switch ((ShiftExp.Op) op) {
                case SHL -> i1 << i2;
                case SHR -> i1 >> i2;
                case USHR -> i1 >>> i2;
            };
        } else if (op instanceof BitwiseExp.Op) {
            return switch ((BitwiseExp.Op) op) {
                case OR -> i1 | i2;
                case AND -> i1 & i2;
                case XOR -> i1 ^ i2;
            };
        }
        throw new AnalysisException("Unsupported operator: " + op);
    }
}
