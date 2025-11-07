/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 *
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "RE.hpp"
#include "expr.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include <climits>
#include <cstring>
#include <map>
#include <vector>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    // TODO: TO COMPLETE THE VARIADIC CLASS
    std::vector<Value> args;
    for (const auto &var : rands)
        args.push_back(var->eval(e));
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    // The first character of a variable name cannot be a digit or any character from the set: {.@}
    // If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    // Variable names can overlap with primitives and reserve_words
    // Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    // When a variable is not defined in the current scope, your interpreter should output RuntimeError

    if (x.empty() || (isdigit(x[0]) || x[0] == '.' || x[0] == '@')) {
        throw RuntimeError("Invalid variable name: starts with invalid character");
    }

    // Rule 2: No forbidden characters (#, ', ", `)
    const std::string forbidden_chars = "#'\"`";
    for (char c : x) {
        if (forbidden_chars.find(c) != std::string::npos) {
            throw RuntimeError("Invalid variable name: contains forbidden character '" + std::string(1, c) + "'");
        }
    }

    // Rule 3: Reject names that can be recognized as numbers (prioritized as literals)
    auto isNumeric = [](const std::string &s) -> bool {
        // Handle integers (+123, -456, 789)
        if (s.empty())
            return false;
        size_t i = 0;
        if (s[i] == '+' || s[i] == '-')
            i++; // Sign
        // Check for digits or valid decimal format
        bool has_digit = false;
        bool has_dot = false;
        bool has_exponent = false;
        while (i < s.size()) {
            if (isdigit(s[i])) {
                has_digit = true;
            } else if (s[i] == '.') {
                if (has_dot || has_exponent)
                    return false;
                has_dot = true;
            } else if (s[i] == 'e' || s[i] == 'E') {
                if (has_exponent || !has_digit)
                    return false;
                has_exponent = true;
                // Exponent must be followed by sign or digit
                if (++i >= s.size() || (!isdigit(s[i]) && s[i] != '+' && s[i] != '-')) {
                    return false;
                }
                if (s[i] == '+' || s[i] == '-')
                    i++; // Exponent sign
                if (i >= s.size() || !isdigit(s[i]))
                    return false;
            } else {
                return false; // Invalid character for number
            }
            i++;
        }
        // Must have at least one digit (reject "." or "+.")
        return has_digit;
    };

    if (isNumeric(x)) {
        throw RuntimeError("Invalid variable name: numeric format is prioritized as literal");
    }

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                {E_VOID, {new MakeVoid(), {}}},
                {E_EXIT, {new Exit(), {}}},
                {E_BOOLQ, {new IsBoolean(new Var("parm")), {"parm"}}},
                {E_INTQ, {new IsFixnum(new Var("parm")), {"parm"}}},
                {E_NULLQ, {new IsNull(new Var("parm")), {"parm"}}},
                {E_PAIRQ, {new IsPair(new Var("parm")), {"parm"}}},
                {E_PROCQ, {new IsProcedure(new Var("parm")), {"parm"}}},
                {E_SYMBOLQ, {new IsSymbol(new Var("parm")), {"parm"}}},
                {E_STRINGQ, {new IsString(new Var("parm")), {"parm"}}},
                {E_DISPLAY, {new Display(new Var("parm")), {"parm"}}},
                {E_PLUS, {new PlusVar({}), {}}},
                {E_MINUS, {new MinusVar({}), {}}},
                {E_MUL, {new MultVar({}), {}}},
                {E_DIV, {new DivVar({}), {}}},
                {E_MODULO, {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1", "parm2"}}},
                {E_EXPT, {new Expt(new Var("parm1"), new Var("parm2")), {"parm1", "parm2"}}},
                {E_EQQ, {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            // TOD0:to PASS THE parameters correctly;
            // COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {
                // TODO
                return ProcedureV(
                    it->second.second, // Formal parameter names (e.g., {"parm"} for boolean?)
                    it->second.first,  // Implementation expression (e.g., IsBoolean)
                    e                  // Capture current environment as closure env
                );
            }
        }
        // Step 3: Variable not found in environment or primitives
        throw RuntimeError("Undefined variable: '" + x + "'");
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    // TODO: To complete the addition logic
    // Case 1: Integer + Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int x = dynamic_cast<Integer *>(rand1.get())->n;
        int y = dynamic_cast<Integer *>(rand2.get())->n;
        return IntegerV(x + y);
    }

    // Case 2: Integer + Rational
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int int_val = dynamic_cast<Integer *>(rand1.get())->n;
        int num = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = int_val * den + num;
        return RationalV(new_num, den);
    }

    // Case 3: Rational + Integer
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        int num = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den = dynamic_cast<Rational *>(rand1.get())->denominator;
        int int_val = dynamic_cast<Integer *>(rand2.get())->n;
        int new_num = num + int_val * den;
        return RationalV(new_num, den);
    }

    // Case 4: Rational + Rational
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        int num1 = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den1 = dynamic_cast<Rational *>(rand1.get())->denominator;
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = num1 * den2 + num2 * den1;
        int new_den = den1 * den2;
        return RationalV(new_num, new_den);
    }

    throw RuntimeError("Wrong typename: + requires numeric arguments (int/rational)");
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    // TODO: To complete the substraction logic
    // Case 1: Integer - Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int x = dynamic_cast<Integer *>(rand1.get())->n;
        int y = dynamic_cast<Integer *>(rand2.get())->n;
        return IntegerV(x - y);
    }

    // Case 2: Integer - Rational
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int int_val = dynamic_cast<Integer *>(rand1.get())->n;
        int num = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = int_val * den - num;
        return RationalV(new_num, den);
    }

    // Case 3: Rational - Integer
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        int num = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den = dynamic_cast<Rational *>(rand1.get())->denominator;
        int int_val = dynamic_cast<Integer *>(rand2.get())->n;
        int new_num = num - int_val * den;
        return RationalV(new_num, den);
    }

    // Case 4: Rational - Rational
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        int num1 = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den1 = dynamic_cast<Rational *>(rand1.get())->denominator;
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = num1 * den2 - num2 * den1;
        int new_den = den1 * den2;
        return RationalV(new_num, new_den);
    }

    throw RuntimeError("Wrong typename: - requires numeric arguments (int/rational)");
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    // TODO: To complete the Multiplication logic
    // Case 1: Integer * Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int x = dynamic_cast<Integer *>(rand1.get())->n;
        int y = dynamic_cast<Integer *>(rand2.get())->n;
        return IntegerV(x * y);
    }

    // Case 2: Integer * Rational
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int int_val = dynamic_cast<Integer *>(rand1.get())->n;
        int num = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = int_val * num;
        return RationalV(new_num, den);
    }

    // Case 3: Rational * Integer
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        int num = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den = dynamic_cast<Rational *>(rand1.get())->denominator;
        int int_val = dynamic_cast<Integer *>(rand2.get())->n;
        int new_num = num * int_val;
        return RationalV(new_num, den);
    }

    // Case 4: Rational * Rational
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        int num1 = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den1 = dynamic_cast<Rational *>(rand1.get())->denominator;
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = num1 * num2;
        int new_den = den1 * den2;
        return RationalV(new_num, new_den);
    }

    throw RuntimeError("Wrong typename: * requires numeric arguments (int/rational)");
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    // TODO: To complete the dicision logic
    // Check for division by zero
    if (rand2->v_type == V_INT && dynamic_cast<Integer *>(rand2.get())->n == 0) {
        throw RuntimeError("Division by zero");
    }
    if (rand2->v_type == V_RATIONAL) {
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        if (num2 == 0)
            throw RuntimeError("Division by zero");
    }

    // Case 1: Integer / Integer (result as rational if not divisible)
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer *>(rand1.get())->n;
        int divisor = dynamic_cast<Integer *>(rand2.get())->n;
        if (dividend % divisor == 0) {
            return IntegerV(dividend / divisor);
        } else {
            int num = dividend;
            int den = divisor;
            return RationalV(num, den);
        }
    }

    // Case 2: Integer / Rational (multiply by reciprocal)
    if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int int_val = dynamic_cast<Integer *>(rand1.get())->n;
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = int_val * den2;
        int new_den = num2;
        return RationalV(new_num, new_den);
    }

    // Case 3: Rational / Integer (multiply by reciprocal)
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        int num1 = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den1 = dynamic_cast<Rational *>(rand1.get())->denominator;
        int divisor = dynamic_cast<Integer *>(rand2.get())->n;
        int new_num = num1;
        int new_den = den1 * divisor;
        return RationalV(new_num, new_den);
    }

    // Case 4: Rational / Rational (multiply by reciprocal)
    if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        int num1 = dynamic_cast<Rational *>(rand1.get())->numerator;
        int den1 = dynamic_cast<Rational *>(rand1.get())->denominator;
        int num2 = dynamic_cast<Rational *>(rand2.get())->numerator;
        int den2 = dynamic_cast<Rational *>(rand2.get())->denominator;
        int new_num = num1 * den2;
        int new_den = den1 * num2;
        return RationalV(new_num, new_den);
    }

    throw RuntimeError("Wrong typename: / requires numeric arguments (int/rational)");
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer *>(rand1.get())->n;
        int divisor = dynamic_cast<Integer *>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    // TODO: To complete the addition logic
    if (args.empty()) {
        return IntegerV(0); // Scheme standard: (+) => 0
    }
    // Accumulate result by sequentially applying binary +
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = Plus(Expr(nullptr), Expr(nullptr)).evalRator(result, args[i]);
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    // TODO: To complete the substraction
    if (args.empty()) {
        throw RuntimeError("minus requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Single argument: return its negation (0 - arg)
        return Minus(Expr(nullptr), Expr(nullptr)).evalRator(IntegerV(0), args[0]);
    }
    // Accumulate result by sequentially applying binary -
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = Minus(Expr(nullptr), Expr(nullptr)).evalRator(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    // TODO: To complete the multiplication logic
    if (args.empty()) {
        return IntegerV(1); // Scheme standard: (*) => 1
    }
    // Accumulate result by sequentially applying binary *
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = Mult(Expr(nullptr), Expr(nullptr)).evalRator(result, args[i]); // Reuse Binary::Mult
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    // TODO: To complete the divisor logic
    if (args.empty()) {
        throw RuntimeError("division requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Single argument: return its reciprocal (1 / arg)
        return Div(Expr(nullptr), Expr(nullptr)).evalRator(IntegerV(1), args[0]);
    }
    // Accumulate result by sequentially applying binary /
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = Div(Expr(nullptr), Expr(nullptr)).evalRator(result, args[i]); // Reuse Binary::Div
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer *>(rand1.get())->n;
        int exponent = dynamic_cast<Integer *>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        long long result = 1;
        long long b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

// A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer *>(v1.get())->n;
        int n2 = dynamic_cast<Integer *>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1
                                          : 0;
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational *r1 = dynamic_cast<Rational *>(v1.get());
        int n2 = dynamic_cast<Integer *>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1
                                                    : 0;
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer *>(v1.get())->n;
        Rational *r2 = dynamic_cast<Rational *>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1
                                                    : 0;
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational *r1 = dynamic_cast<Rational *>(v1.get());
        Rational *r2 = dynamic_cast<Rational *>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1
                                                    : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    // TODO: To complete the less logic
    if (((rand1->v_type == V_INT) || (rand1->v_type == V_RATIONAL)) &&
        ((rand2->v_type == V_INT) || (rand2->v_type == V_RATIONAL))) {
        if (compareNumericValues(rand1, rand2) == -1)
            return BooleanV(1);
        else
            return BooleanV(0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    // TODO: To complete the lesseq logic
    if (((rand1->v_type == V_INT) || (rand1->v_type == V_RATIONAL)) &&
        ((rand2->v_type == V_INT) || (rand2->v_type == V_RATIONAL))) {
        if (compareNumericValues(rand1, rand2) != 1)
            return BooleanV(1);
        else
            return BooleanV(0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    // TODO: To complete the equal logic
    if (((rand1->v_type == V_INT) || (rand1->v_type == V_RATIONAL)) &&
        ((rand2->v_type == V_INT) || (rand2->v_type == V_RATIONAL))) {
        if (compareNumericValues(rand1, rand2) == 0)
            return BooleanV(1);
        else
            return BooleanV(0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    // TODO: To complete the greatereq logic
    if (((rand1->v_type == V_INT) || (rand1->v_type == V_RATIONAL)) &&
        ((rand2->v_type == V_INT) || (rand2->v_type == V_RATIONAL))) {
        if (compareNumericValues(rand1, rand2) != -1)
            return BooleanV(1);
        else
            return BooleanV(0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    // TODO: To complete the greater logic
    if (((rand1->v_type == V_INT) || (rand1->v_type == V_RATIONAL)) &&
        ((rand2->v_type == V_INT) || (rand2->v_type == V_RATIONAL))) {
        if (compareNumericValues(rand1, rand2) == 1)
            return BooleanV(1);
        else
            return BooleanV(0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    // TODO: To complete the less logic
    if (args.size() < 2) {
        return BooleanV(true); // Scheme standard: (<) or (< a) => #t
    }
    for (size_t i = 0; i < args.size() - 1; ++i) {
        // Reuse Binary::Less logic for pairwise comparison
        Value res = Less(Expr(nullptr), Expr(nullptr)).evalRator(args[i], args[i + 1]);
        if (!dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false); // Early exit on first failure
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    // TODO: To complete the lesseq logic
    if (args.size() < 2) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; ++i) {
        Value res = LessEq(Expr(nullptr), Expr(nullptr)).evalRator(args[i], args[i + 1]);
        if (!dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    // TODO: To complete the equal logic
    if (args.size() < 2) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; ++i) {
        Value res = Equal(Expr(nullptr), Expr(nullptr)).evalRator(args[i], args[i + 1]);
        if (!dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    // TODO: To complete the greatereq logic
    if (args.size() < 2) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; ++i) {
        Value res = GreaterEq(Expr(nullptr), Expr(nullptr)).evalRator(args[i], args[i + 1]);
        if (!dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    // TODO: To complete the greater logic
    if (args.size() < 2) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; ++i) {
        Value res = Greater(Expr(nullptr), Expr(nullptr)).evalRator(args[i], args[i + 1]);
        if (!dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    // TODO: To complete the cons logic
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    // TODO: To complete the list logic
    Value now = NullV();
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
        now = PairV(*it, now);
    }
    return now;
}

Value IsList::evalRator(const Value &rand) { // list?
                                             // TODO: To complete the list? logic
    Value current = rand;

    // Rule 1: The empty list is a valid list
    if (current->v_type == V_NULL) {
        return BooleanV(true);
    }

    // Rule 2: Non-pair values cannot be lists
    if (current->v_type != V_PAIR) {
        return BooleanV(false);
    }

    // Initialize slow and fast pointers to detect cycles (tortoise-hare algorithm)
    Value slow = current;                                  // Slow pointer: moves 1 step at a time
    Value fast = dynamic_cast<Pair *>(current.get())->cdr; // Fast pointer: initial 1st step

    // Traverse the cdr chain while fast pointer points to a pair
    while (fast->v_type == V_PAIR) {
        // Cycle detected (slow and fast pointers meet) → not a list
        if (slow.get() == fast.get()) {
            return BooleanV(false);
        }

        // Move slow pointer 1 step (follow current pair's cdr)
        slow = dynamic_cast<Pair *>(slow.get())->cdr;

        // Move fast pointer 1st step (follow current pair's cdr)
        fast = dynamic_cast<Pair *>(fast.get())->cdr;

        // Check if fast pointer can move a 2nd step (avoid invalid cdr access)
        if (fast->v_type != V_PAIR) {
            break;
        }
        fast = dynamic_cast<Pair *>(fast.get())->cdr; // Fast pointer 2nd step
    }

    // After loop: valid lists must end with the empty list (V_NULL)
    return BooleanV(fast->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    // TODO: To complete the car logic
    if (rand->v_type == V_PAIR) {
        Value current = dynamic_cast<Pair *>(rand.get())->car;
        return current;
    }
    throw(RuntimeError("Wrong typename"));
}

Value Cdr::evalRator(const Value &rand) { // cdr
    // TODO: To complete the cdr logic
    if (rand->v_type == V_PAIR) {
        Value current = dynamic_cast<Pair *>(rand.get())->cdr;
        return current;
    }
    throw(RuntimeError("Wrong typename"));
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    // TODO: To complete the set-car! logic
    // Validate first argument is a pair
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car!: first argument must be a pair");
    }
    // Mutate the car field of the pair (direct memory update)
    dynamic_cast<Pair *>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    // TODO: To complete the set-cdr! logic
    // Validate first argument is a pair
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr!: first argument must be a pair");
    }
    // Mutate the cdr field of the pair (direct memory update)
    dynamic_cast<Pair *>(rand1.get())->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer *>(rand1.get())->n) == (dynamic_cast<Integer *>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean *>(rand1.get())->b) == (dynamic_cast<Boolean *>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol *>(rand1.get())->s) == (dynamic_cast<Symbol *>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    // TODO: To complete the begin logic
    Value last_val = VoidV(); // Default to Void if no expressions

    // Evaluate all expressions in sequence (left to right)
    for (const auto &expr : es) {       // exprs: list of Expr stored in Begin
        last_val = expr.get()->eval(e); // Overwrite with result of current expression
    }

    // Return the result of the last expression
    return last_val;
}

Value Quote::eval(Assoc &e) {
    // TODO: To complete the quote logic
    // Helper function: Recursively convert SyntaxBase to Value WITHOUT evaluation
    // Ensures the original structure of quoted syntax is preserved (core of 'quote' semantics)
    auto syntaxToValue = [](SyntaxBase *sb, auto &self) -> Value {
        if (!sb) {
            throw RuntimeError("quote: invalid syntax structure (null pointer)");
        }

        // 1. Handle Symbol syntax (e.g., 'scheme → SymbolV("scheme"))
        if (auto sym_syntax = dynamic_cast<SymbolSyntax *>(sb)) {
            return SymbolV(sym_syntax->s);
        }

        // 2. Handle Integer syntax (e.g., '5 → IntegerV(5))
        if (auto num_syntax = dynamic_cast<Number *>(sb)) {
            return IntegerV(num_syntax->n);
        }

        // 3. Handle Rational number syntax (e.g., '3/4 → RationalV(3,4))
        if (auto rat_syntax = dynamic_cast<RationalSyntax *>(sb)) {
            return RationalV(rat_syntax->numerator, rat_syntax->denominator);
        }

        // 4. Handle Boolean #t syntax (e.g., '#t → BooleanV(true))
        if (dynamic_cast<TrueSyntax *>(sb)) {
            return BooleanV(true);
        }

        // 5. Handle Boolean #f syntax (e.g., '#f → BooleanV(false))
        if (dynamic_cast<FalseSyntax *>(sb)) {
            return BooleanV(false);
        }

        // 6. Handle String syntax (e.g., '"hello" → StringV("hello"))
        if (auto str_syntax = dynamic_cast<StringSyntax *>(sb)) {
            return StringV(str_syntax->s);
        }

        // 7. Handle List/Pair syntax (core logic for nested structures)
        if (auto list_syntax = dynamic_cast<List *>(sb)) {
            const auto &stxs = list_syntax->stxs;
            size_t dot_pos = stxs.size(); // Track position of '.' (init: no dot)

            // 7.1 Check for presence of '.' (dot) and validate dot rules
            for (size_t i = 0; i < stxs.size(); ++i) {
                auto elem_sb = stxs[i].get();
                if (auto sym = dynamic_cast<SymbolSyntax *>(elem_sb)) {
                    if (sym->s == ".") {
                        if (dot_pos != stxs.size()) { // Multiple dots found (illegal in Scheme)
                            throw RuntimeError("quote: invalid list (multiple dots are not allowed)");
                        }
                        dot_pos = i; // Record position of the single valid dot
                    }
                }
            }

            size_t dot_count = 0;
            for (auto &elem : stxs) {
                if (auto sym = dynamic_cast<SymbolSyntax *>(elem.get())) {
                    if (sym->s == ".")
                        dot_count++;
                }
            }
            // Reject (a . b . c) or (a .)
            if (dot_count > 1 || (dot_count == 1 && stxs.size() > 0)) {
                SymbolSyntax *last_sym = dynamic_cast<SymbolSyntax *>(stxs.back().get());
                if (last_sym && last_sym->s == ".") {
                    throw RuntimeError("quote: invalid dotted pair (multiple dots or trailing dot)");
                }
            }

            // 7.2 Handle DOTTED case (improper list, e.g., (1 2 . 3))
            if (dot_pos != stxs.size()) {
                // Validate dot position: cannot be at start/end, or followed by >1 element
                if (dot_pos == 0) {
                    throw RuntimeError("quote: invalid list (dot cannot be at the start)");
                }
                if (dot_pos == stxs.size() - 1) {
                    throw RuntimeError("quote: invalid list (dot cannot be at the end)");
                }
                if (stxs.size() - dot_pos - 1 > 1) {
                    throw RuntimeError("quote: invalid list (only one element allowed after dot)");
                }

                // 7.2.1 Build prefix (elements before dot) into a nested Pair chain
                // For dotted pair (a b . c), we need to create: (Pair a (Pair b c))
                // Start from the last element before dot and build backwards
                Value suffix_val = self(stxs[dot_pos + 1].get(), self);

                // Build the chain from right to left
                Value current = suffix_val;
                for (int i = dot_pos - 1; i >= 0; --i) {
                    Value car_val = self(stxs[i].get(), self);
                    current = PairV(car_val, current);
                }

                return current;
            }

            // 7.3 Handle NON-DOTTED case (proper list, e.g., (1 2 3) or ())
            if (stxs.empty()) { // Empty list → NullV (Scheme's '()')
                return NullV();
            }

            // Build list from RIGHT to LEFT (more efficient for nested PairV)
            // Ends with NullV to form a proper Scheme list
            Value list_val = NullV();
            for (auto it = stxs.rbegin(); it != stxs.rend(); ++it) {
                list_val = PairV(self(it->get(), self), list_val);
            }

            return list_val;
        }

        // Unsupported syntax type (should not reach here with valid parser)
        throw RuntimeError("quote: unsupported syntax type (check parser output)");
    };

    // Convert the quoted Syntax (this->s) to Value and return
    return syntaxToValue(s.get(), syntaxToValue);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    // TODO: To complete the and logic
    if (rands.empty()) {
        return BooleanV(true);
    }

    // Evaluate AND with short-circuit: returns #f on first #f, else last value
    for (const auto &expr : rands) {
        Value res = expr.get()->eval(e); // Evaluate current expression (Expr -> ExprBase* -> eval)
        // Short-circuit: return #f if current value is #f
        if (res->v_type == V_BOOL && !dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(false);
        }
    }

    // All arguments are true; return the last one's value
    return rands.back().get()->eval(e);
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    // TODO: To complete the or logic
    if (rands.empty()) {
        return BooleanV(false);
    }

    // Evaluate OR with short-circuit: returns first non-#f, else #f
    for (const auto &expr : rands) {
        Value res = expr.get()->eval(e); // Evaluate current expression (Expr -> ExprBase* -> eval)
        // Short-circuit: return current value if it's not #f
        if (res->v_type == V_BOOL && dynamic_cast<Boolean *>(res.get())->b) {
            return BooleanV(true);
        }
    }

    // All arguments are #f; return #f
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    // TODO: To complete the not logic
    if (rand->v_type == V_BOOL) {
        // If input is Boolean, return its negation
        bool is_false = !dynamic_cast<Boolean *>(rand.get())->b;
        return BooleanV(is_false);
    } else {
        // If input is non-Boolean (e.g., int, symbol), it's "true" → NOT returns #f
        return BooleanV(false);
    }
}

Value If::eval(Assoc &e) {
    // TODO: To complete the if logic
    // Evaluate the condition expression first
    Value cond_val = cond.get()->eval(e); // Convert condition Expr to Value

    // In Scheme, "true" means any value except #f
    bool is_true = !(cond_val->v_type == V_BOOL && !dynamic_cast<Boolean *>(cond_val.get())->b);

    // Short-circuit evaluation: only execute the selected branch
    if (is_true) {
        // Condition is true → evaluate consequence branch
        return conseq.get()->eval(e);
    } else {
        // Condition is false → evaluate alternative branch (or return #f if none)
        if (alter.get() != nullptr) {
            return alter.get()->eval(e);
        } else {
            return BooleanV(false);
        }
    }
}

Value Cond::eval(Assoc &env) {
    // TODO: To complete the cond logic
    for (const auto &clause : clauses) { // Iterate over `clauses` member (expr.hpp)
        if (clause.empty()) {
            throw RuntimeError("cond: empty clause is invalid");
        }
        // Evaluate the first element of the clause (the condition)
        Value cond_val = clause[0]->eval(env);
        // Scheme rule: non-#f values are true
        bool is_true = !(cond_val->v_type == V_BOOL && !dynamic_cast<Boolean *>(cond_val.get())->b);

        if (is_true) {
            // Evaluate remaining expressions in the clause; return the last one
            Value last_val = VoidV();
            for (size_t i = 1; i < clause.size(); ++i) {
                last_val = clause[i]->eval(env);
            }
            // If clause has only a condition (no body), return the condition's value
            return (clause.size() == 1) ? cond_val : last_val;
        }
    }
    // No true clauses: return #f (Scheme standard)
    return BooleanV(false);
}

Value Lambda::eval(Assoc &env) {
    // TODO: To complete the lambda logic
    // Return ProcedureV (closure) with parameters, body, and current lexical environment
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    // Step 1: Evaluate rator to get procedure (closure)
    Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    // TODO: TO COMPLETE THE CLOSURE LOGIC
    Procedure *clos_ptr = dynamic_cast<Procedure *>(proc_val.get());

    // TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    // Step 2: Evaluate all arguments (expr.hpp uses "rand" as member name, not "rands")
    std::vector<Value> args;
    for (const auto &arg_expr : rand) { // Traverse "rand" (vector<Expr>), not "rands"
        args.push_back(arg_expr.get()->eval(e));
    }

    // Step 3: Check argument count match (closure's parameters vs evaluated args)
    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments: expected " +
                           std::to_string(clos_ptr->parameters.size()) + ", got " +
                           std::to_string(args.size()));
    }

    // TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    // Step 4: Extend closure's environment with parameter bindings
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); ++i) {
        const std::string &param = clos_ptr->parameters[i];
        param_env = extend(param, args[i], param_env);
    }

    // Step 5: Evaluate procedure body (support multiple expressions via Begin)
    return clos_ptr->e.get()->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // TODO: To complete the define logic
    std::string var_name = var;

    // Validate: var cannot be primitive or reserved word
    if (primitives.count(var_name) || reserved_words.count(var_name)) {
        throw RuntimeError("Define: cannot redefine primitive/reserved word '" + var_name + "'");
    }

    // Handle unary recursion:
    // 1. First check if var exists in env; if not, extend with placeholder (VoidV)
    // 2. Evaluate the expression (may reference var for recursion)
    // 3. Modify the binding to the real value
    Value existing = find(var_name, env);
    if (existing.get() == nullptr) {
        extend(var_name, VoidV(), env); // Placeholder for recursion
    }

    // Evaluate the expression (e is Define's member in expr.hpp)
    Value val = e.get()->eval(env);

    // Update the binding (modify if exists, extend if not — but we already extended above)
    modify(var_name, val, env);

    return VoidV();
}

Value Let::eval(Assoc &env) {
    // TODO: To complete the let logic
    // 1. Evaluate all bindings in the original environment (non-recursive)
    std::vector<std::pair<std::string, Value>> evaluated_bindings;
    for (const auto &bind_pair : bind) {          // Iterate over `bind` member (expr.hpp)
        const std::string &var = bind_pair.first; // Variable name
        const Expr &expr = bind_pair.second;      // Bound expression (Expr type per expr.hpp)
        Value val = expr->eval(env);              // Evaluate in outer environment
        evaluated_bindings.emplace_back(var, val);
    }
    // 2. Extend the environment with evaluated bindings
    Assoc let_env = env;
    for (const auto &[var, val] : evaluated_bindings) {
        let_env = extend(var, val, let_env);
    }
    // 3. Evaluate `body` member (single Expr) in the extended environment
    return body->eval(let_env); // Use `body` member (expr.hpp)
}

Value Letrec::eval(Assoc &env) {
    // TODO: To complete the letrec logic
    // 1. Create placeholder bindings (VoidV) in a new environment
    Assoc letrec_env = env;
    for (const auto &bind_pair : bind) { // Iterate over `bind` member (expr.hpp)
        const std::string &var = bind_pair.first;
        letrec_env = extend(var, VoidV(), letrec_env); // Placeholder for recursion
    }
    // 2. Evaluate expressions in the new environment (allow recursive references)
    for (const auto &bind_pair : bind) {
        const std::string &var = bind_pair.first;
        const Expr &expr = bind_pair.second; // Bound expression (Expr type per expr.hpp)
        Value val = expr->eval(letrec_env);  // Can reference other letrec variables
        modify(var, val, letrec_env);        // Replace placeholder with real value
    }
    // 3. Evaluate `body` member in the updated environment
    return body->eval(letrec_env); // Use `body` member (expr.hpp)
}

Value Set::eval(Assoc &env) {
    // TODO: To complete the set logic
    // 1. Check if `var` (member) exists in the environment
    Value existing = find(var, env); // Use `var` member (expr.hpp)
    if (existing.get() == nullptr) {
        throw RuntimeError("set!: undefined variable '" + var + "'");
    }
    // 2. Evaluate `e` member (new value)
    Value new_val = e->eval(env); // Use `e` member (expr.hpp: Expr type)
    // 3. Modify the existing binding in the environment
    modify(var, new_val, env);
    // Scheme standard: set! returns void
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String *str_ptr = dynamic_cast<String *>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
