#include "Def.hpp"
#include "RE.hpp"
#include "expr.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include <cassert>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

bool isExplicitVoidCall(Expr expr) {
    MakeVoid *make_void_expr = dynamic_cast<MakeVoid *>(expr.get());
    if (make_void_expr != nullptr) {
        return true;
    }

    Apply *apply_expr = dynamic_cast<Apply *>(expr.get());
    if (apply_expr != nullptr) {
        Var *var_expr = dynamic_cast<Var *>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "void") {
            return true;
        }
    }

    Begin *begin_expr = dynamic_cast<Begin *>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isExplicitVoidCall(begin_expr->es.back());
    }

    If *if_expr = dynamic_cast<If *>(expr.get());
    if (if_expr != nullptr) {
        return isExplicitVoidCall(if_expr->conseq) || isExplicitVoidCall(if_expr->alter);
    }

    Cond *cond_expr = dynamic_cast<Cond *>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto &clause : cond_expr->clauses) {
            if (clause.size() > 1 && isExplicitVoidCall(clause.back())) {
                return true;
            }
        }
    }
    return false;
}

void REPL() {
    // read - evaluation - print loop
    Assoc global_env = empty();
    while (1) {
        Syntax stx = readSyntax(std::cin); // read
        // stx->show(std::cout); // syntax print
        try {
            Expr expr = stx->parse(global_env); // parse
            Value val = expr->eval(global_env);
            if (val->v_type == V_TERMINATE) {
#ifndef ONLINE_JUDGE
                std::cout << "Terminate" << std::endl;
#endif
                break;
            }
            bool is_void_value = (val->v_type == V_VOID);
            bool is_explicit_void = isExplicitVoidCall(expr);
            if (!is_void_value || is_explicit_void) {
                val->show(std::cout);
                std::cout << std::endl;
                std::cout.flush();
            }
        } catch (const RuntimeError &RE) {
            // std::cout << RE.message();
            std::cout << "RuntimeError";
            std::cout << std::endl;
            std::cout.flush();
        }
    }
}

int main(int argc, char *argv[]) {
    REPL();
    return 0;
}
