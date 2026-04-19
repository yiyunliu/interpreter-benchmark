#pragma once
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

enum class Binop { Add, Sub, Mul, Quotient, Le };

struct Var;
struct App;
struct Fix;
struct Prim;
struct If;

using Expr = std::variant<
    int,
    std::unique_ptr<Var>,
    std::unique_ptr<App>,
    std::unique_ptr<Fix>,
    std::unique_ptr<Prim>,
    std::unique_ptr<If>>;

struct Var { std::string name; };
struct App { Expr fn; std::vector<Expr> args; };
struct Fix { std::string self_name; std::vector<std::string> params; Expr body; };
struct Prim { Binop op; Expr lhs; Expr rhs; };
struct If { Expr guard; Expr thn; Expr els; };

struct Closure;
using Value = std::variant<int, std::shared_ptr<Closure>>;

struct Closure {
    std::function<Value(std::vector<Value>)> fn;
};

int apply_binop(Binop op, int64_t lhs, int64_t rhs) {
    switch (op) {
        case Binop::Add: return lhs + rhs;
        case Binop::Sub: return lhs - rhs;
        case Binop::Mul: return lhs * rhs;
        case Binop::Quotient: return lhs / rhs;
        case Binop::Le: return lhs <= rhs ? 1 : 0;
    }
    __builtin_unreachable();
}

using Env = std::unordered_map<std::string, Value>;

// helpers to build Expr
inline Expr make_int(int n) { return n; }
inline Expr make_var(std::string name) { return std::make_unique<Var>(Var{std::move(name)}); }
inline Expr make_app(Expr fn, std::vector<Expr> args) { return std::make_unique<App>(App{std::move(fn), std::move(args)}); }
inline Expr make_fix(std::string self, std::vector<std::string> params, Expr body) { return std::make_unique<Fix>(Fix{std::move(self), std::move(params), std::move(body)}); }
inline Expr make_prim(Binop op, Expr lhs, Expr rhs) { return std::make_unique<Prim>(Prim{op, std::move(lhs), std::move(rhs)}); }
inline Expr make_if(Expr guard, Expr thn, Expr els) { return std::make_unique<If>(If{std::move(guard), std::move(thn), std::move(els)}); }
