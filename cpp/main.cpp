#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

template <class... Ts>
struct overloaded : Ts... {
    using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

enum class Binop { Add, Sub, Mul, Quotient, Le };

struct Var;
struct App;
struct Fix;
struct Prim;
struct If;

using Expr = std::variant<int,
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

int apply_binop(Binop op, int lhs, int rhs) {
    switch (op) {
        case Binop::Add: return lhs + rhs;
        case Binop::Sub: return lhs - rhs;
        case Binop::Mul: return lhs * rhs;
        case Binop::Quotient: return lhs / rhs;
        case Binop::Le: return lhs <= rhs ? 1 : 0;
    }
    __builtin_unreachable();
}

Expr make_int(int n) { return n; }
Expr make_var(std::string name) { return std::make_unique<Var>(Var{std::move(name)}); }
Expr make_app(Expr fn, std::vector<Expr> args) {
    return std::make_unique<App>(App{std::move(fn), std::move(args)});
}
Expr make_fix(std::string self, std::vector<std::string> params, Expr body) {
    return std::make_unique<Fix>(Fix{std::move(self), std::move(params), std::move(body)});
}
Expr make_prim(Binop op, Expr lhs, Expr rhs) {
    return std::make_unique<Prim>(Prim{op, std::move(lhs), std::move(rhs)});
}
Expr make_if(Expr guard, Expr thn, Expr els) {
    return std::make_unique<If>(If{std::move(guard), std::move(thn), std::move(els)});
}

// ---------- Naive interpreter ----------

using Env = std::unordered_map<std::string, Value>;

Value denote(const Env& env, const Expr& e) {
    return std::visit(overloaded{
        [&](int n) -> Value { return n; },
        [&](const std::unique_ptr<Var>& v) -> Value {
            auto it = env.find(v->name);
            if (it == env.end()) throw std::runtime_error("unbound: " + v->name);
            return it->second;
        },
        [&](const std::unique_ptr<App>& a) -> Value {
            auto fn_val = denote(env, a->fn);
            auto* cl = std::get_if<std::shared_ptr<Closure>>(&fn_val);
            if (!cl) throw std::runtime_error("apply non-function");
            std::vector<Value> args;
            args.reserve(a->args.size());
            for (const auto& arg : a->args) args.push_back(denote(env, arg));
            return (*cl)->fn(std::move(args));
        },
        [&](const std::unique_ptr<Fix>& f) -> Value {
            auto closure = std::make_shared<Closure>();
            auto self = closure;
            std::vector<std::string> all_params;
            all_params.push_back(f->self_name);
            for (const auto& p : f->params) all_params.push_back(p);
            const Expr* body = &f->body;
            Env env_copy = env;
            closure->fn = [self, env_copy, all_params, body](std::vector<Value> vals) -> Value {
                Env new_env = env_copy;
                new_env[all_params[0]] = Value{self};
                for (size_t i = 0; i < vals.size(); i++)
                    new_env[all_params[i + 1]] = std::move(vals[i]);
                return denote(new_env, *body);
            };
            return Value{closure};
        },
        [&](const std::unique_ptr<Prim>& p) -> Value {
            auto l = denote(env, p->lhs);
            auto r = denote(env, p->rhs);
            auto* li = std::get_if<int>(&l);
            auto* ri = std::get_if<int>(&r);
            if (!li || !ri) throw std::runtime_error("arith on non-numbers");
            return apply_binop(p->op, *li, *ri);
        },
        [&](const std::unique_ptr<If>& i) -> Value {
            auto g = denote(env, i->guard);
            auto* gi = std::get_if<int>(&g);
            if (gi && *gi == 0) return denote(env, i->els);
            return denote(env, i->thn);
        }
    }, e);
}

// ---------- Stack interpreter ----------

struct Stack {
    std::vector<Value> data;
    int top = 0;

    explicit Stack(int size) : data(size) {}

    void push(Value v) {
        if (top >= static_cast<int>(data.size()))
            throw std::runtime_error("stack overflow");
        data[top++] = std::move(v);
    }

    Value ref(int idx) const { return data[top - idx - 1]; }
    void pop(int n) { top -= n; }
};

using CEnv = std::function<int(const std::string&)>;

CEnv cenv_empty = [](const std::string& s) -> int {
    throw std::runtime_error("unmapped: " + s);
};

CEnv cenv_extend(CEnv cenv, std::string s) {
    return [cenv = std::move(cenv), s = std::move(s)](const std::string& s2) -> int {
        if (s2 == s) return 0;
        return 1 + cenv(s2);
    };
}

CEnv cenv_extend_mult(CEnv cenv, const std::vector<std::string>& syms) {
    for (const auto& s : syms) cenv = cenv_extend(std::move(cenv), s);
    return cenv;
}

std::unordered_set<std::string> collect_free(const Expr& e) {
    std::unordered_set<std::string> collected;
    std::function<void(const std::unordered_set<std::string>&, const Expr&)> go;
    go = [&](const std::unordered_set<std::string>& bounded, const Expr& expr) {
        std::visit(overloaded{
            [&](int) {},
            [&](const std::unique_ptr<Var>& v) {
                if (bounded.find(v->name) == bounded.end())
                    collected.insert(v->name);
            },
            [&](const std::unique_ptr<App>& a) {
                go(bounded, a->fn);
                for (const auto& arg : a->args) go(bounded, arg);
            },
            [&](const std::unique_ptr<Fix>& f) {
                auto nb = bounded;
                nb.insert(f->self_name);
                for (const auto& p : f->params) nb.insert(p);
                go(nb, f->body);
            },
            [&](const std::unique_ptr<Prim>& p) {
                go(bounded, p->lhs);
                go(bounded, p->rhs);
            },
            [&](const std::unique_ptr<If>& i) {
                go(bounded, i->guard);
                go(bounded, i->thn);
                go(bounded, i->els);
            }
        }, expr);
    };
    go({}, e);
    return collected;
}

std::vector<std::pair<std::string, int>>
collect_captured(const CEnv& cenv, const Expr& e) {
    auto fv = collect_free(e);
    std::vector<std::pair<std::string, int>> result;
    for (const auto& v : fv) result.push_back({v, cenv(v)});
    std::sort(result.begin(), result.end(),
              [](const auto& a, const auto& b) { return a.second > b.second; });
    return result;
}

using Compiled = std::function<Value(Stack&)>;

Compiled denote_faster(CEnv cenv, const Expr& e) {
    return std::visit(overloaded{
        [&](int n) -> Compiled {
            return [n](Stack&) -> Value { return n; };
        },
        [&](const std::unique_ptr<Var>& v) -> Compiled {
            int dvar = cenv(v->name);
            return [dvar](Stack& stk) -> Value { return stk.ref(dvar); };
        },
        [&](const std::unique_ptr<App>& a) -> Compiled {
            auto fun_clos = denote_faster(cenv, a->fn);
            std::vector<Compiled> arg_closs;
            for (const auto& arg : a->args) arg_closs.push_back(denote_faster(cenv, arg));
            return [fun_clos, arg_closs](Stack& stk) -> Value {
                auto fn_val = fun_clos(stk);
                auto* cl = std::get_if<std::shared_ptr<Closure>>(&fn_val);
                if (!cl) throw std::runtime_error("apply non-function");
                std::vector<Value> args;
                args.reserve(arg_closs.size());
                for (const auto& c : arg_closs) args.push_back(c(stk));
                return (*cl)->fn(std::move(args));
            };
        },
        [&](const std::unique_ptr<Fix>& f) -> Compiled {
            auto captured = collect_captured(cenv, e);
            std::vector<int> captured_dvars;
            std::vector<std::string> ext;
            for (const auto& [var, dvar] : captured) {
                ext.push_back(var);
                captured_dvars.push_back(dvar);
            }
            ext.push_back(f->self_name);
            for (const auto& p : f->params) ext.push_back(p);
            auto body_clos = denote_faster(cenv_extend_mult(cenv, ext), f->body);
            int len = static_cast<int>(1 + f->params.size() + captured_dvars.size());
            return [captured_dvars, body_clos, len](Stack& stk) -> Value {
                std::vector<Value> captured_args;
                captured_args.reserve(captured_dvars.size());
                for (int d : captured_dvars) captured_args.push_back(stk.ref(d));
                auto closure = std::make_shared<Closure>();
                closure->fn = [closure, captured_args, body_clos, &stk, len](
                                  std::vector<Value> vals) -> Value {
                    for (const auto& val : captured_args) stk.push(val);
                    stk.push(Value{closure});
                    for (auto& val : vals) stk.push(std::move(val));
                    auto retval = body_clos(stk);
                    stk.pop(len);
                    return retval;
                };
                return Value{closure};
            };
        },
        [&](const std::unique_ptr<Prim>& p) -> Compiled {
            auto op = p->op;
            auto lhs_clos = denote_faster(cenv, p->lhs);
            auto rhs_clos = denote_faster(cenv, p->rhs);
            return [op, lhs_clos, rhs_clos](Stack& stk) -> Value {
                auto l = lhs_clos(stk);
                auto r = rhs_clos(stk);
                auto* li = std::get_if<int>(&l);
                auto* ri = std::get_if<int>(&r);
                if (!li || !ri) throw std::runtime_error("arith on non-numbers");
                return apply_binop(op, *li, *ri);
            };
        },
        [&](const std::unique_ptr<If>& i) -> Compiled {
            auto guard_clos = denote_faster(cenv, i->guard);
            auto thn_clos = denote_faster(cenv, i->thn);
            auto els_clos = denote_faster(cenv, i->els);
            return [guard_clos, thn_clos, els_clos](Stack& stk) -> Value {
                auto g = guard_clos(stk);
                auto* gi = std::get_if<int>(&g);
                if (gi && *gi == 0) return els_clos(stk);
                return thn_clos(stk);
            };
        }
    }, e);
}

// ---------- Native ----------

int64_t native_fib(int64_t n) {
    if (n <= 1) return 1;
    return native_fib(n - 1) + native_fib(n - 2);
}

// ---------- Main ----------

Expr make_fib_expr() {
    std::vector<Expr> args1;
    args1.push_back(make_prim(Binop::Sub, make_var("x"), make_int(1)));
    std::vector<Expr> args2;
    args2.push_back(make_prim(Binop::Sub, make_var("x"), make_int(2)));
    return make_fix("self", {"x"},
        make_if(
            make_prim(Binop::Le, make_var("x"), make_int(1)),
            make_int(1),
            make_prim(Binop::Add,
                make_app(make_var("self"), std::move(args1)),
                make_app(make_var("self"), std::move(args2)))));
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        printf("Usage: interpreter [--naive|--host] <n>\n");
        return 1;
    }
    std::string mode = argv[1];
    if (mode == "--naive" || mode == "--host") {
        if (argc < 3) { printf("Usage: interpreter [--naive|--host] <n>\n"); return 1; }
        int n = std::atoi(argv[2]);
        if (mode == "--host") {
            printf("%lld\n", (long long)native_fib(n));
        } else {
            std::vector<Expr> args;
            args.push_back(make_int(n));
            auto result = denote(Env{},
                make_app(make_fib_expr(), std::move(args)));
            printf("%d\n", std::get<int>(result));
        }
    } else {
        int n = std::atoi(argv[1]);
        std::vector<Expr> args;
        args.push_back(make_int(n));
        auto expr = make_app(make_fib_expr(), std::move(args));
        auto compiled = denote_faster(cenv_empty, expr);
        Stack stack(1024);
        auto result = compiled(stack);
        printf("%d\n", std::get<int>(result));
    }
    return 0;
}
