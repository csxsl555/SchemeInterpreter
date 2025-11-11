/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 *
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "Def.hpp"
#include "RE.hpp"
#include "expr.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include <iostream>
#include <map>
#include <string>

#define mp make_pair
using std::pair;
using std::string;
using std::vector;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    // std::string type_name = typeid(*this).name();
    // throw RuntimeError("Unimplemented parse method for class: " + type_name);
    return ptr->parse(env);
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    // TODO: complete the rational parser
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    // TODO: check if the first element is a symbol
    // If not, use Apply function to package to a closure;
    // If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax *>(stxs[0].get());
    if (id == nullptr) {
        // TODO: TO COMPLETE THE LOGIC
        //  Case 1: The first element is not a symbol → function application (e.g., ((lambda (x) x) 5))
        Expr rator = stxs[0].parse(env); // Parse the function (could be a lambda or variable)
        vector<Expr> rands;
        for (size_t i = 1; i < stxs.size(); ++i) {
            rands.push_back(stxs[i].parse(env)); // Parse arguments recursively
        }
        return Expr(new Apply(rator, rands));
    } else {
        string op = id->s;

        // std::cout << op << '!' << std::endl;

        if (find(op, env).get() != nullptr) {
            // 作为变量应用处理（如lambda参数if/begin/quote）
            // std::cout << op << "CNMB" << std::endl;
            Expr rator = stxs[0].parse(env);
            vector<Expr> rands;
            for (size_t i = 1; i < stxs.size(); ++i) {
                rands.push_back(stxs[i].parse(env));
            }
            return Expr(new Apply(rator, rands));
        }

        // Case 1: Check if it's a primitive operation
        if (primitives.count(op) != 0) {
            vector<Expr> parameters;
            // TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
            //  Parse all subsequent elements as parameters
            for (size_t i = 1; i < stxs.size(); ++i) {
                parameters.push_back(stxs[i].parse(env));
            }

            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                // TODO: TO COMPLETE THE LOGIC
                //  (+) => 0; (+ a) => a; (+ a b c...) => a + b + c + ...
                return Expr(new PlusVar(parameters));
            } else if (op_type == E_MINUS) {
                // TODO: TO COMPLETE THE LOGIC
                //  (- a) => 0 - a; (- a b c...) => a - b - c - ...
                if (parameters.empty()) {
                    throw RuntimeError("minus requires at least 1 argument");
                }
                return Expr(new MinusVar(parameters));
            } else if (op_type == E_MUL) {
                // TODO: TO COMPLETE THE LOGIC
                //  (*) => 1; (* a) => a; (* a b c...) => a * b * c * ...
                return Expr(new MultVar(parameters));
            } else if (op_type == E_DIV) {
                // TODO: TO COMPLETE THE LOGIC
                //  (/ a) => 1 / a; (/ a b c...) => a / b / c / ...
                if (parameters.empty()) {
                    throw RuntimeError("division requires at least 1 argument");
                }
                return Expr(new DivVar(parameters));
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for modulo");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_EXPT) {
                // std::cout << "CNMB" << std::endl;
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for expt");
                }
                return Expr(new Expt(parameters[0], parameters[1]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_LT) {
                // TODO: TO COMPLETE THE LOGIC
                //  (<) => #t; (< a) => #t; (< a b c...) => a < b < c < ...
                return Expr(new LessVar(parameters));
            } else if (op_type == E_LE) {
                // TODO: TO COMPLETE THE LOGIC
                //  (<=) => #t; (<= a) => #t; (<= a b c...) => a <= b <= c <= ...
                return Expr(new LessEqVar(parameters));
            } else if (op_type == E_EQ) {
                // TODO: TO COMPLETE THE LOGIC
                //  (=) => #t; (= a) => #t; (= a b c...) => a = b = c = ...
                return Expr(new EqualVar(parameters));
            } else if (op_type == E_GE) {
                // TODO: TO COMPLETE THE LOGIC
                //  (>=) => #t; (>= a) => #t; (>= a b c...) => a >= b >= c >= ...
                return Expr(new GreaterEqVar(parameters));
            } else if (op_type == E_GT) {
                // TODO: TO COMPLETE THE LOGIC
                //  (>) => #t; (>) => #t; (> a b c...) => a > b > c > ...
                return Expr(new GreaterVar(parameters));
            } else if (op_type == E_AND) {
                return Expr(new AndVar(parameters));
            } else if (op_type == E_OR) {
                return Expr(new OrVar(parameters));
            } else if (op_type == E_NOT) {
                if (parameters.size() == 1) {
                    return Expr(new Not(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for not");
                }
            } else if (op_type == E_CONS) {
                if (parameters.size() == 2) {
                    return Expr(new Cons(parameters[0], parameters[1]));
                } else {
                    throw RuntimeError("Wrong number of arguments for cons");
                }
            } else if (op_type == E_CAR) {
                if (parameters.size() == 1) {
                    return Expr(new Car(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for car");
                }
            } else if (op_type == E_CDR) {
                if (parameters.size() == 1) {
                    return Expr(new Cdr(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for cdr");
                }
            } else if (op_type == E_BOOLQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsBoolean(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for boolean?");
                }
            } else if (op_type == E_INTQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsFixnum(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for number?");
                }
            } else if (op_type == E_NULLQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsNull(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for null?");
                }
            } else if (op_type == E_PAIRQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsPair(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for pair?");
                }
            } else if (op_type == E_PROCQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsProcedure(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for procedure?");
                }
            } else if (op_type == E_SYMBOLQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsSymbol(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for symbol?");
                }
            } else if (op_type == E_STRINGQ) {
                if (parameters.size() == 1) {
                    return Expr(new IsString(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for string?");
                }
            } else if (op_type == E_EQQ) {
                if (parameters.size() == 2) {
                    return Expr(new IsEq(parameters[0], parameters[1]));
                } else {
                    throw RuntimeError("Wrong number of arguments for eq?");
                }
            } else if (op_type == E_DISPLAY) {
                if (parameters.size() == 1) {
                    return Expr(new Display(parameters[0]));
                } else {
                    throw RuntimeError("Wrong number of arguments for display");
                }
            } else if (op_type == E_SETCAR) {
                // Added: Parse set-car! (2 arguments: pair + new-car)
                if (parameters.size() == 2) {
                    return Expr(new SetCar(parameters[0], parameters[1]));
                } else {
                    throw RuntimeError("Wrong number of arguments for set-car!");
                }
            } else if (op_type == E_SETCDR) {
                // Added: Parse set-cdr! (2 arguments: pair + new-cdr)
                if (parameters.size() == 2) {
                    return Expr(new SetCdr(parameters[0], parameters[1]));
                } else {
                    throw RuntimeError("Wrong number of arguments for set-cdr!");
                }
            } else if (op_type == E_VOID) {
                // Added: Parse void (0 arguments)
                if (parameters.empty()) {
                    return Expr(new MakeVoid());
                } else {
                    throw RuntimeError("Wrong number of arguments for void");
                }
            } else if (op_type == E_EXIT) {
                // Added: Parse exit (0 arguments)
                if (parameters.empty()) {
                    return Expr(new Exit());
                } else {
                    throw RuntimeError("Wrong number of arguments for exit");
                }
            } else {
                throw RuntimeError("Unsupported primitive operation: " + op);
            }
        }

        // Case 2: Check if it's a reserved word
        if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
            // TODO: TO COMPLETE THE reserve_words PARSER LOGIC
            case E_QUOTE: {
                // (quote expr) must have exactly 1 argument
                if (stxs.size() != 2) {
                    throw RuntimeError("quote requires exactly 1 argument");
                }
                return Expr(new Quote(stxs[1]));
            }
            case E_IF: {
                // (if cond conseq [alter]) requires 2 or 3 arguments
                if (stxs.size() < 3 || stxs.size() > 4) {
                    throw RuntimeError("if requires 2 or 3 arguments");
                }
                Expr cond_expr = stxs[1].parse(env);
                Expr conseq_expr = stxs[2].parse(env);
                Expr alter_expr = (stxs.size() == 4) ? stxs[3].parse(env) : Expr(new False());
                return Expr(new If(cond_expr, conseq_expr, alter_expr));
            }
            case E_LAMBDA: {
                // (lambda (params...) body...) requires at least 2 arguments
                if (stxs.size() < 3) {
                    throw RuntimeError("lambda requires at least 2 arguments (parameters + body)");
                }

                // Parse parameter list (must be a List)
                List *param_list = dynamic_cast<List *>(stxs[1].get());
                if (!param_list) {
                    throw RuntimeError("lambda parameters must be a list");
                }

                // Parse parameters
                vector<string> params;
                for (const auto &param_stx : param_list->stxs) {
                    SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax *>(param_stx.get());
                    if (!param_sym) {
                        throw RuntimeError("lambda parameters must be symbols");
                    }
                    params.push_back(param_sym->s);
                }

                // [Critical fix: Temporarily add parameters to the parsing environment]
                // This ensures that parameter names (even if they match reserved words)
                // are recognized as variables during body parsing
                Assoc lambda_env = env; // Copy current environment
                for (const string &param : params) {
                    // Temporarily bind parameter to environment (value is irrelevant here;
                    // we only need to mark that the name is bound)
                    lambda_env = extend(param, VoidV(), lambda_env);
                }

                // [Parse body using the extended environment]
                // Now references to parameter names will be recognized as variables
                // instead of reserved words/special forms
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); ++i) {
                    body_exprs.push_back(stxs[i].parse(lambda_env)); // Use lambda_env instead of original env
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Lambda(params, body));
            }
            case E_DEFINE: {
                // Two forms: (define var expr) or (define (func params...) body...)
                if (stxs.size() < 3) {
                    throw RuntimeError("define requires at least 2 arguments");
                }

                // Helper function to parse body expressions
                auto parseBody = [&](size_t start_idx) -> Expr {
                    vector<Expr> body_exprs;
                    for (size_t i = start_idx; i < stxs.size(); ++i) {
                        body_exprs.push_back(stxs[i].parse(env));
                    }
                    return (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                };

                SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax *>(stxs[1].get());
                List *func_shorthand = dynamic_cast<List *>(stxs[1].get());

                // std::cout << "CNMB" << std::endl;

                if (var_sym) {
                    // Variable definition: (define var expr)
                    // std::cout << stxs[1].get() << '!' << std::endl;
                    return Expr(new Define(var_sym->s, parseBody(2)));
                } else if (func_shorthand) {
                    // Function shorthand: (define (func params...) body...) → (define func (lambda (params...) body))
                    if (func_shorthand->stxs.empty()) {
                        throw RuntimeError("define function shorthand cannot be empty");
                    }

                    SymbolSyntax *func_name_sym = dynamic_cast<SymbolSyntax *>(func_shorthand->stxs[0].get());
                    if (!func_name_sym) {
                        throw RuntimeError("define function name must be a symbol");
                    }

                    // std::cout << func_name_sym->s << '?' << std::endl;

                    // Parse parameters
                    vector<string> params;
                    for (size_t i = 1; i < func_shorthand->stxs.size(); ++i) {
                        SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax *>(func_shorthand->stxs[i].get());
                        if (!param_sym) {
                            throw RuntimeError("define function parameters must be symbols");
                        }
                        params.push_back(param_sym->s);
                    }

                    Expr lambda_expr = Expr(new Lambda(params, parseBody(2)));
                    return Expr(new Define(func_name_sym->s, lambda_expr));
                } else {
                    throw RuntimeError("define: left-hand side must be a symbol or function shorthand");
                }
            }
            case E_BEGIN: {
                // (begin expr1 expr2 ...) wraps multiple expressions
                vector<Expr> exprs;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    exprs.push_back(stxs[i].parse(env));
                }
                return Expr(new Begin(exprs));
            }
            case E_COND: {
                // (cond (clause1) (clause2) ...)
                if (stxs.size() == 1) {
                    throw RuntimeError("cond: at least one clause is required");
                }
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    List *clause_list = dynamic_cast<List *>(stxs[i].get());
                    if (!clause_list) {
                        throw RuntimeError("cond clauses must be lists");
                    }
                    vector<Expr> clause_exprs;
                    for (auto &stx : clause_list->stxs) {
                        clause_exprs.push_back(stx.parse(env));
                    }
                    clauses.push_back(clause_exprs);
                }
                return Expr(new Cond(clauses));
            }
            case E_LET: {
                // Added: Parse let syntax: (let ((var1 expr1) (var2 expr2) ...) body...)
                if (stxs.size() < 3) {
                    throw RuntimeError("let requires at least 2 arguments (bindings + body)");
                }

                // Helper function to parse bindings
                auto parseBindings = [&](List *bindings_list) -> vector<pair<string, Expr>> {
                    vector<pair<string, Expr>> bindings;
                    for (auto &binding_stx : bindings_list->stxs) {
                        List *var_expr_pair = dynamic_cast<List *>(binding_stx.get());
                        if (!var_expr_pair || var_expr_pair->stxs.size() != 2) {
                            throw RuntimeError("let binding must be a (var expr) pair");
                        }
                        SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax *>(var_expr_pair->stxs[0].get());
                        if (!var_sym) {
                            throw RuntimeError("let binding variable must be a symbol");
                        }
                        Expr expr = var_expr_pair->stxs[1].parse(env);
                        bindings.emplace_back(var_sym->s, expr);
                    }
                    return bindings;
                };

                // Parse bindings list (must be a List of (var expr) pairs)
                List *bindings_list = dynamic_cast<List *>(stxs[1].get());
                if (!bindings_list) {
                    throw RuntimeError("let bindings must be a list");
                }

                vector<pair<string, Expr>> bindings = parseBindings(bindings_list);

                // Parse body (wrap multiple expressions with Begin)
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); ++i) {
                    body_exprs.push_back(stxs[i].parse(env));
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Let(bindings, body));
            }
            case E_LETREC: {
                // Added: Parse letrec syntax: (letrec ((var1 expr1) (var2 expr2) ...) body...)
                if (stxs.size() < 3) {
                    throw RuntimeError("letrec requires at least 2 arguments (bindings + body)");
                }

                // Helper function to parse bindings
                auto parseBindings = [&](List *bindings_list) -> vector<pair<string, Expr>> {
                    vector<pair<string, Expr>> bindings;
                    for (auto &binding_stx : bindings_list->stxs) {
                        List *var_expr_pair = dynamic_cast<List *>(binding_stx.get());
                        if (!var_expr_pair || var_expr_pair->stxs.size() != 2) {
                            throw RuntimeError("letrec binding must be a (var expr) pair");
                        }
                        SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax *>(var_expr_pair->stxs[0].get());
                        if (!var_sym) {
                            throw RuntimeError("letrec binding variable must be a symbol");
                        }
                        Expr expr = var_expr_pair->stxs[1].parse(env);
                        bindings.emplace_back(var_sym->s, expr);
                    }
                    return bindings;
                };

                // Parse bindings list (must be a List of (var expr) pairs)
                List *bindings_list = dynamic_cast<List *>(stxs[1].get());
                if (!bindings_list) {
                    throw RuntimeError("letrec bindings must be a list");
                }

                vector<pair<string, Expr>> bindings = parseBindings(bindings_list);

                // Parse body (wrap multiple expressions with Begin)
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); ++i) {
                    body_exprs.push_back(stxs[i].parse(env));
                }
                Expr body = (body_exprs.size() == 1) ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Letrec(bindings, body));
            }
            case E_SET: {
                // Added: Parse set! syntax: (set! var expr)
                if (stxs.size() != 3) {
                    throw RuntimeError("set! requires exactly 2 arguments (var + expr)");
                }
                // Parse variable (must be symbol)
                SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax *>(stxs[1].get());
                if (!var_sym) {
                    throw RuntimeError("set! variable must be a symbol");
                }
                // Parse expression
                Expr expr = stxs[2].parse(env);
                return Expr(new Set(var_sym->s, expr));
            }
            default:
                throw RuntimeError("Unknown reserved word: " + op);
            }
        }

        // default: use Apply to be an expression
        // TODO: TO COMPLETE THE PARSER LOGIC
        Expr rator = stxs[0].parse(env); // The function (variable)
        vector<Expr> rands;
        for (size_t i = 1; i < stxs.size(); ++i) {
            rands.push_back(stxs[i].parse(env)); // Arguments
        }
        return Expr(new Apply(rator, rands));
    }
}
