#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <gc/gc.h>
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
using Value = std::variant<int, Closure*>;

struct Closure {
    std::function<Value(std::vector<Value>)> fn;
    void* operator new(size_t size) { return GC_MALLOC(size); }
    void operator delete(void*) {}
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
            auto* cl = std::get_if<Closure*>(&fn_val);
            if (!cl) throw std::runtime_error("apply non-function");
            std::vector<Value> args;
            args.reserve(a->args.size());
            for (const auto& arg : a->args) args.push_back(denote(env, arg));
            return (*cl)->fn(std::move(args));
        },
        [&](const std::unique_ptr<Fix>& f) -> Value {
            auto closure = new Closure();
            auto self = closure;
            std::vector<std::string> all_params;
            all_params.push_back(f->self_name);
            for (const auto& p : f->params) all_params.push_back(p);
            const Expr* body = &f->body;
            Env env_copy = env;
            closure->fn = [self, env_copy, all_params, body](std::vector<Value> vals) -> Value {
                Env new_env = env_copy;
                new_env[all_params[0]] = self;
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

// ---------- Curried interpreter ----------

using FastCompiled = std::function<Value(const Env&)>;

FastCompiled denote_fast(const Expr& e) {
    return std::visit(overloaded{
        [&](int n) -> FastCompiled {
            return [n](const Env&) -> Value { return n; };
        },
        [&](const std::unique_ptr<Var>& v) -> FastCompiled {
            std::string name = v->name;
            return [name = std::move(name)](const Env& env) -> Value {
                auto it = env.find(name);
                if (it == env.end()) throw std::runtime_error("unbound: " + name);
                return it->second;
            };
        },
        [&](const std::unique_ptr<App>& a) -> FastCompiled {
            auto fun_clos = denote_fast(a->fn);
            std::vector<FastCompiled> arg_closs;
            for (const auto& arg : a->args) arg_closs.push_back(denote_fast(arg));
            return [fun_clos, arg_closs](const Env& env) -> Value {
                auto fn_val = fun_clos(env);
                auto* cl = std::get_if<Closure*>(&fn_val);
                if (!cl) throw std::runtime_error("apply non-function");
                std::vector<Value> args;
                args.reserve(arg_closs.size());
                for (const auto& c : arg_closs) args.push_back(c(env));
                return (*cl)->fn(std::move(args));
            };
        },
        [&](const std::unique_ptr<Fix>& f) -> FastCompiled {
            std::vector<std::string> all_params;
            all_params.push_back(f->self_name);
            for (const auto& p : f->params) all_params.push_back(p);
            auto body_clos = denote_fast(f->body);
            return [all_params, body_clos](const Env& env) -> Value {
                auto closure = new Closure();
                closure->fn = [closure, env, all_params, body_clos](std::vector<Value> vals) -> Value {
                    Env new_env = env;
                    new_env[all_params[0]] = closure;
                    for (size_t i = 0; i < vals.size(); i++)
                        new_env[all_params[i + 1]] = std::move(vals[i]);
                    return body_clos(new_env);
                };
                return closure;
            };
        },
        [&](const std::unique_ptr<Prim>& p) -> FastCompiled {
            auto op = p->op;
            auto lhs_clos = denote_fast(p->lhs);
            auto rhs_clos = denote_fast(p->rhs);
            return [op, lhs_clos, rhs_clos](const Env& env) -> Value {
                auto l = lhs_clos(env);
                auto r = rhs_clos(env);
                auto* li = std::get_if<int>(&l);
                auto* ri = std::get_if<int>(&r);
                if (!li || !ri) throw std::runtime_error("arith on non-numbers");
                return apply_binop(op, *li, *ri);
            };
        },
        [&](const std::unique_ptr<If>& i) -> FastCompiled {
            auto guard_clos = denote_fast(i->guard);
            auto thn_clos = denote_fast(i->thn);
            auto els_clos = denote_fast(i->els);
            return [guard_clos, thn_clos, els_clos](const Env& env) -> Value {
                auto g = guard_clos(env);
                auto* gi = std::get_if<int>(&g);
                if (gi && *gi == 0) return els_clos(env);
                return thn_clos(env);
            };
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
                auto* cl = std::get_if<Closure*>(&fn_val);
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
                auto closure = new Closure();
                closure->fn = [closure, captured_args, body_clos, &stk, len](
                                  std::vector<Value> vals) -> Value {
                    for (const auto& val : captured_args) stk.push(val);
                    stk.push(closure);
                    for (auto& val : vals) stk.push(std::move(val));
                    auto retval = body_clos(stk);
                    stk.pop(len);
                    return retval;
                };
                return closure;
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

// ---------- Defunctionalized stack interpreter ----------

struct FInstr;
struct FFixClosure;

struct FValue {
    enum Tag { Int, Closure } tag;
    int int_val;
    FFixClosure* closure_val;
};

struct FFixClosure {
    FValue* captured_args;
    int ncaptured;
    const FInstr* body;
    int frame_len;
};

static inline FValue fv_int(int n) { return {FValue::Int, n, nullptr}; }
static inline FValue fv_closure(FFixClosure* c) { return {FValue::Closure, 0, c}; }

struct FStack {
    FValue* data;
    int top;
    int cap;
    explicit FStack(int size) : data(new FValue[size]), top(0), cap(size) {}
    void push(FValue v) {
        if (top >= cap) throw std::runtime_error("stack overflow");
        data[top++] = v;
    }
    FValue ref(int idx) const { return data[top - idx - 1]; }
    void pop(int n) { top -= n; }
};

struct FInstr {
    enum Tag { Int, Var, Prim, App, Fix, If } tag;
    int int_val;
    int dvar;
    Binop op;
    const FInstr* lhs;
    const FInstr* rhs;
    const FInstr* fn_instr;
    const FInstr** arg_instrs;
    int nargs;
    const FInstr* body_instr;
    int* captured_dvars;
    int ncaptured;
    int frame_len;
    const FInstr* guard_instr;
    const FInstr* thn_instr;
    const FInstr* els_instr;
};

FValue eval_fastest(const FInstr* instr, FStack& stk) {
    switch (instr->tag) {
        case FInstr::Int:
            return fv_int(instr->int_val);
        case FInstr::Var:
            return stk.ref(instr->dvar);
        case FInstr::Prim: {
            auto l = eval_fastest(instr->lhs, stk);
            auto r = eval_fastest(instr->rhs, stk);
            return fv_int(apply_binop(instr->op, l.int_val, r.int_val));
        }
        case FInstr::App: {
            auto fn_val = eval_fastest(instr->fn_instr, stk);
            if (fn_val.tag != FValue::Closure) throw std::runtime_error("apply non-function");
            auto& closure = *fn_val.closure_val;
            FValue arg_buf[8];
            FValue* args = instr->nargs <= 8 ? arg_buf : new FValue[instr->nargs];
            for (int i = 0; i < instr->nargs; i++)
                args[i] = eval_fastest(instr->arg_instrs[i], stk);
            for (int i = 0; i < closure.ncaptured; i++)
                stk.push(closure.captured_args[i]);
            stk.push(fv_closure(fn_val.closure_val));
            for (int i = 0; i < instr->nargs; i++)
                stk.push(args[i]);
            if (instr->nargs > 8) delete[] args;
            auto retval = eval_fastest(closure.body, stk);
            stk.pop(closure.frame_len);
            return retval;
        }
        case FInstr::Fix: {
            auto* closure = new FFixClosure();
            closure->ncaptured = instr->ncaptured;
            closure->captured_args = instr->ncaptured > 0 ? new FValue[instr->ncaptured] : nullptr;
            for (int i = 0; i < instr->ncaptured; i++)
                closure->captured_args[i] = stk.ref(instr->captured_dvars[i]);
            closure->body = instr->body_instr;
            closure->frame_len = instr->frame_len;
            return fv_closure(closure);
        }
        case FInstr::If: {
            auto g = eval_fastest(instr->guard_instr, stk);
            if (g.int_val == 0)
                return eval_fastest(instr->els_instr, stk);
            return eval_fastest(instr->thn_instr, stk);
        }
    }
    __builtin_unreachable();
}

const FInstr* denote_fastest(CEnv cenv, const Expr& e) {
    return std::visit(overloaded{
        [&](int n) -> const FInstr* {
            auto* i = new FInstr{FInstr::Int, n, 0, {}, nullptr, nullptr,
                                 nullptr, nullptr, 0, nullptr, nullptr, 0, 0,
                                 nullptr, nullptr, nullptr};
            return i;
        },
        [&](const std::unique_ptr<Var>& v) -> const FInstr* {
            auto* i = new FInstr{FInstr::Var, 0, cenv(v->name), {}, nullptr, nullptr,
                                 nullptr, nullptr, 0, nullptr, nullptr, 0, 0,
                                 nullptr, nullptr, nullptr};
            return i;
        },
        [&](const std::unique_ptr<App>& a) -> const FInstr* {
            int nargs = static_cast<int>(a->args.size());
            auto** arg_arr = new const FInstr*[nargs];
            for (int j = 0; j < nargs; j++)
                arg_arr[j] = denote_fastest(cenv, a->args[j]);
            auto* i = new FInstr{FInstr::App, 0, 0, {}, nullptr, nullptr,
                                 denote_fastest(cenv, a->fn), arg_arr, nargs,
                                 nullptr, nullptr, 0, 0,
                                 nullptr, nullptr, nullptr};
            return i;
        },
        [&](const std::unique_ptr<Fix>& f) -> const FInstr* {
            auto captured = collect_captured(cenv, e);
            std::vector<int> cdvars;
            std::vector<std::string> ext;
            for (const auto& [var, dvar] : captured) {
                ext.push_back(var);
                cdvars.push_back(dvar);
            }
            ext.push_back(f->self_name);
            for (const auto& p : f->params) ext.push_back(p);
            int nc = static_cast<int>(cdvars.size());
            int* cdarr = nc > 0 ? new int[nc] : nullptr;
            for (int j = 0; j < nc; j++) cdarr[j] = cdvars[j];
            auto* i = new FInstr{FInstr::Fix, 0, 0, {}, nullptr, nullptr,
                                 nullptr, nullptr, 0,
                                 denote_fastest(cenv_extend_mult(cenv, ext), f->body),
                                 cdarr, nc,
                                 static_cast<int>(1 + f->params.size() + cdvars.size()),
                                 nullptr, nullptr, nullptr};
            return i;
        },
        [&](const std::unique_ptr<Prim>& p) -> const FInstr* {
            auto* i = new FInstr{FInstr::Prim, 0, 0, p->op,
                                 denote_fastest(cenv, p->lhs),
                                 denote_fastest(cenv, p->rhs),
                                 nullptr, nullptr, 0, nullptr, nullptr, 0, 0,
                                 nullptr, nullptr, nullptr};
            return i;
        },
        [&](const std::unique_ptr<If>& if_) -> const FInstr* {
            auto* i = new FInstr{FInstr::If, 0, 0, {}, nullptr, nullptr,
                                 nullptr, nullptr, 0, nullptr, nullptr, 0, 0,
                                 denote_fastest(cenv, if_->guard),
                                 denote_fastest(cenv, if_->thn),
                                 denote_fastest(cenv, if_->els)};
            return i;
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
    GC_INIT();
    if (argc < 2) {
        printf("Usage: interpreter [--naive|--host] <n>\n");
        return 1;
    }
    std::string mode = argv[1];
    if (mode == "--naive" || mode == "--host" || mode == "--closure" || mode == "--fastest") {
        if (argc < 3) { printf("Usage: interpreter [--naive|--host|--closure|--fastest] <n>\n"); return 1; }
        int n = std::atoi(argv[2]);
        if (mode == "--host") {
            printf("%lld\n", (long long)native_fib(n));
        } else if (mode == "--closure") {
            std::vector<Expr> args;
            args.push_back(make_int(n));
            auto compiled = denote_fast(make_app(make_fib_expr(), std::move(args)));
            auto result = compiled(Env{});
            printf("%d\n", std::get<int>(result));
        } else if (mode == "--fastest") {
            std::vector<Expr> args;
            args.push_back(make_int(n));
            auto instr = denote_fastest(cenv_empty, make_app(make_fib_expr(), std::move(args)));
            FStack stack(1024);
            auto result = eval_fastest(instr, stack);
            printf("%d\n", result.int_val);
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
