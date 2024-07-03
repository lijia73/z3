/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include "ast/ast.h"
#include "util/top_sort.h"
#include<unordered_map>
#include<vector>
#include "model/model.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/well_sorted.h"
#include "ast/used_symbols.h"
#include "ast/for_each_expr.h"
#include "ast/for_each_ast.h"
#include "model/model.h"
#include "model/model_params.hpp"
#include "model/model_evaluator.h"
#include "model/array_factory.h"
#include "model/value_factory.h"
#include "model/seq_factory.h"
#include "model/datatype_factory.h"
#include "model/numeral_factory.h"
#include "model/fpa_factory.h"

#include "api/api_context.h"

struct coverage_small {
    unsigned long c0;
    unsigned long c1;
};

struct coverage_big {
    std::vector<bool> c0;
    std::vector<bool> c1;
};

struct coverage_struct {
    struct coverage_small s;
    struct coverage_big b;
    int index;
};

typedef struct coverage_struct coverage;

struct coverage_count_struct {
    int c0;
    int c1;
};

typedef struct coverage_count_struct coverage_count;

Z3_API bool get_coverage_vector = false;
Z3_API std::vector<coverage_count> coverage_vector;

Z3_API int coverage_enable = 0;
Z3_API int coverage_bool = 0;
Z3_API int coverage_bv = 0;
Z3_API int coverage_all_bool = 0;
Z3_API int coverage_all_bv = 0;
Z3_API std::unordered_map<app*, coverage> covered;

Z3_API Z3_ast parse_bv(char const * n, Z3_sort s, Z3_context ctx);
Z3_API std::string bv_string(Z3_ast ast, Z3_context ctx);


typedef rational numeral;

Z3_ast parse_bv(char const * n, Z3_sort s, Z3_context ctx) {
    rational result = rational(0);
    while(*n) {
        char c = *n;
        if ('0' <= c && c <= '9') {
            result *= rational(16);
            result += rational(c - '0');
        }
        else if ('a' <= c && c <= 'f') {
            result *= rational(16);
            result += rational(10 + (c - 'a'));
        }

        ++n;
    }
    ast * a = mk_c(ctx)->mk_numeral_core(result, to_sort(s));
    return of_ast(a);
}

std::string bv_string(Z3_ast ast, Z3_context ctx) {
    std::string s;
    rational val;
    unsigned sz = 0;
    unsigned bv_size = 1;
    mk_c(ctx)->bvutil().is_numeral(to_expr(ast), val, bv_size);
    if (val.is_neg())
        val.neg();
    while (val.is_pos()) {
        rational c = val % rational(16);
        val = div(val, rational(16));
        char n;
        if (c <= rational(9)) {
            n = '0' + c.get_unsigned();
        } else {
            n = 'a' + (c.get_unsigned() - 10);
        }
        s += n;
        sz+=4;
    }
    while (sz < bv_size) {
        s += '0';
        sz+=4;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

bool is_zero_bit(numeral & val, unsigned idx) {
    if (val.is_zero())
        return true;
    div(val, rational::power_of_two(idx), val);
    return (val % numeral(2)).is_zero();
}

void process_coverage(expr_ref & m_r, app * t, ast_manager & m) {
            if (coverage_enable != 2)
                return;
            auto res = covered.find(t);
            if (res == covered.end())
                return;
            if (!m_r) {
                return;
            }
            coverage & cov = res->second;
            params_ref p;
            bv_rewriter rewriter(m, p);
            numeral val;
            unsigned long value;
            unsigned sz;

            if (m.is_bool(m_r)) {
                sz = 1;
                if (m.is_true(m_r)) {
                    value = 1;
                    if (get_coverage_vector)
                        ++coverage_vector[cov.index].c1;
                } else if (m.is_false(m_r)) {
                    value = 0;
                    if (get_coverage_vector)
                        ++coverage_vector[cov.index].c0;
                } else
                    return;
            } else {
                bv_util util(m);

                if (!util.is_bv(m_r))
                    return;
                if (!rewriter.is_numeral(m_r, val, sz))
                    return;
                value = val.get_uint64();
                if (get_coverage_vector) {
                    if (value & 1) {
                        ++coverage_vector[cov.index].c1;
                    } else {
                        ++coverage_vector[cov.index].c0;
                    }
                }
            }
            if (cov.b.c0.size() == 0) {
                if (sz == 1) {
                    ++coverage_all_bool;
                } else {
                    coverage_all_bv += sz;
                }
                if (sz <= 64) {
                    cov.s.c0 = 0;
                    cov.s.c1 = 0;
                    cov.b.c0.resize(1, false);
                    cov.b.c1.resize(1, false);
                } else {
                    cov.b.c0.resize(sz, false);
                    cov.b.c1.resize(sz, false);
                }
            }
            if (sz <= 64) {
                for (unsigned long j = 0; j < sz; ++j) {
                    if ((value >> j) & 1) {
                        if (((cov.s.c1 >> j) & 1) == 0) {
                            cov.s.c1 |= 1ul << j;
                            if (sz > 1)
                                ++coverage_bv;
                            else
                                ++coverage_bool;
                        }
                    } else {
                        if (((cov.s.c0 >> j) & 1) == 0) {
                            cov.s.c0 |= 1ul << j;
                            if (sz > 1)
                                ++coverage_bv;
                            else
                                ++coverage_bool;
                        }
                    }
                }
            } else {
                int cur = coverage_bv;
                for (int j = 0; j < sz; ++j) {
                    if (is_zero_bit(val, j)) {
                        if (!cov.b.c0[j]) {
                            cov.b.c0[j] = true;
                            ++coverage_bv;
                        }
                    } else {
                        if (!cov.b.c1[j]) {
                            cov.b.c1[j] = true;
                            ++coverage_bv;
                        }
                    }
                }
            }
}

model::model(ast_manager & m):
    model_core(m),
    m_mev(*this),
    m_cleaned(false),
    m_inline(false) {
}

model::~model() {
    for (auto & kv : m_usort2universe) {
        m.dec_ref(kv.m_key);
        m.dec_array_ref(kv.m_value->size(), kv.m_value->data());
        dealloc(kv.m_value);
    }
}

void model::updt_params(params_ref const & p) {
    model_params mp(p);
    m_inline = mp.inline_def();
    m_mev.updt_params(p); 
}


void model::copy_const_interps(model const & source) {
    for (auto const& kv : source.m_interp) 
        register_decl(kv.m_key, kv.m_value.second);
}

void model::copy_func_interps(model const & source) {
    for (auto const& kv : source.m_finterp) 
        register_decl(kv.m_key, kv.m_value->copy());
}

void model::copy_usort_interps(model const & source) {
    for (auto const& kv : source.m_usort2universe) 
        register_usort(kv.m_key, kv.m_value->size(), kv.m_value->data());
}

model * model::copy() const {
    model * mdl = alloc(model, m);
    mdl->copy_const_interps(*this);
    mdl->copy_func_interps(*this);
    mdl->copy_usort_interps(*this);
    return mdl;
}

void visit(expr * e) {
    app * a = to_app(e);
    coverage cov;
    cov.index = coverage_vector.size();
    coverage_count cov_count;
    coverage_vector.push_back(cov_count);
    auto res = covered.emplace(a, cov);
    if (!res.second)
        return;
    for (int i = 0; i < a->get_num_args(); ++i)
        visit(a->get_args()[i]);
}

// Remark: eval is for backward compatibility. We should use model_evaluator.
bool model::eval_expr(expr * e, expr_ref & result, bool model_completion) {
    scoped_model_completion _smc(*this, model_completion);
    if (coverage_enable == 1) {
        // visit(e);
        return true;
    }
    model_evaluator ev(*this);
    ev.set_model_completion(model_completion);
    try {
        result = (*this)(e);
        return true;
    }
    catch (model_evaluator_exception & ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg() << "\n";);
        return false;
    }
}

value_factory* model::get_factory(sort* s) {
    if (m_factories.plugins().empty()) {
        seq_util su(m);
        fpa_util fu(m);
        m_factories.register_plugin(alloc(array_factory, m, *this));
        m_factories.register_plugin(alloc(datatype_factory, m, *this));
        m_factories.register_plugin(alloc(bv_factory, m));
        m_factories.register_plugin(alloc(arith_factory, m));
        m_factories.register_plugin(alloc(seq_factory, m, su.get_family_id(), *this));
        m_factories.register_plugin(alloc(fpa_value_factory, m, fu.get_family_id()));
    }
    family_id fid = s->get_family_id();
    return m_factories.get_plugin(fid);
}

expr * model::get_some_value(sort * s) {
    ptr_vector<expr> * u = nullptr;
    if (m_usort2universe.find(s, u)) {
        if (!u->empty())
            return u->get(0);
    }    
    return m.get_some_value(s);
}

expr * model::get_fresh_value(sort * s) {
    return get_factory(s)->get_fresh_value(s);
}

void model::register_value(expr* e) {
    get_factory(e->get_sort())->register_value(e);
}

bool model::get_some_values(sort * s, expr_ref& v1, expr_ref& v2) {
    return get_factory(s)->get_some_values(s, v1, v2);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    return *m_usort2universe[s];
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    return u != nullptr;
}

unsigned model::get_num_uninterpreted_sorts() const {
    return m_usorts.size();
}

sort * model::get_uninterpreted_sort(unsigned idx) const {
    return m_usorts[idx];
}

void model::register_usort(sort * s, unsigned usize, expr * const * universe) {
    ptr_vector<expr>* & u = m_usort2universe.insert_if_not_there(s, nullptr);
    m.inc_array_ref(usize, universe);
    if (!u) {
        m_usorts.push_back(s);
        m.inc_ref(s);
        u = alloc(ptr_vector<expr>);
        u->append(usize, universe);
    }
    else {
        m.dec_array_ref(u->size(), u->data());
        u->reset();
        u->append(usize, universe);
    }
}

model * model::translate(ast_translation & translator) const {
    model * res = alloc(model, translator.to());

    // Translate const interps
    for (auto const& kv : m_interp) {
        func_decl_ref d(translator(kv.m_key), translator.to());
        expr_ref v(translator(kv.m_value.second), translator.to());
        res->register_decl(d, v);
    }
    // Translate func interps
    for (auto const& kv : m_finterp) {
        func_interp* fi = kv.m_value->translate(translator);
        res->register_decl(translator(kv.m_key), fi);
    }

    // Translate usort interps
    for (auto const& kv : m_usort2universe) {
        ptr_vector<expr> new_universe;
        for (expr* e : *kv.m_value) {
            new_universe.push_back(translator(e));
        }
        res->register_usort(translator(kv.m_key),
                            new_universe.size(),
                            new_universe.data());
    }

    return res;
}

struct model::top_sort : public ::top_sort<func_decl> {
    func_decl_ref_vector         m_pinned; // protect keys in m_occur_count
    th_rewriter                  m_rewrite;
    obj_map<func_decl, unsigned> m_occur_count;


    top_sort(ast_manager& m):
        m_pinned(m), m_rewrite(m) 
    {
        params_ref p;
        p.set_bool("elim_ite", false);
        p.set_bool("ite_extra_rules", true);
        m_rewrite.updt_params(p);
    }

    void add_occurs(func_decl* f) {
        m_pinned.push_back(f);
        m_occur_count.insert(f, occur_count(f) + 1);
    }

    unsigned occur_count(func_decl* f) const {
        unsigned count = 0;
        m_occur_count.find(f, count);
        return count;
    }
};

void model::evaluate_constants() {
    for (auto& [k, p] : m_interp) {
        auto & [i, e] = p;
        if (m.is_value(e))
            continue;
        expr_ref val(m);
        val = (*this)(e);
        m.dec_ref(e);
        m.inc_ref(val);
        p.second = val;
    }
}


void model::compress(bool force_inline) {
    if (m_cleaned) return;

    // stratify m_finterp and m_decls in a topological sort
    // such that functions f1 < f2 then f1 does not use f2.
    // then for each function in order clean-up the interpretations
    // by substituting in auxiliary definitions that can be eliminated.

    func_decl_ref_vector pinned(m);
    while (true) {
        top_sort ts(m);
        collect_deps(ts);
        ts.topological_sort();
        for (func_decl * f : ts.top_sorted())
            cleanup_interp(ts, f, force_inline);

        func_decl_set removed;
        ts.m_occur_count.reset();
        for (func_decl * f : ts.top_sorted()) 
            collect_occs(ts, f);
        
        // remove auxiliary declarations that are not used.
        for (func_decl * f : ts.top_sorted()) {
            if (f->is_skolem() && ts.occur_count(f) == 0) {
                pinned.push_back(f);
                unregister_decl(f);
                removed.insert(f);
            }
        }
        if (removed.empty())
            break;
        TRACE("model", tout << "remove\n"; for (func_decl* f : removed) tout << f->get_name() << "\n";);
        remove_decls(m_decls, removed);
        remove_decls(m_func_decls, removed);
        remove_decls(m_const_decls, removed);
    }
    m_cleaned = true;
    reset_eval_cache();
}


void model::collect_deps(top_sort& ts) {
    recfun::util u(m);
    for (auto const& [f, v] : m_finterp) 
        if (!u.has_def(f))
            ts.insert(f, collect_deps(ts, v));
        
    for (auto const& [f,v] : m_interp)
        if (!u.has_def(f))
            ts.insert(f, collect_deps(ts, v.second));
}

struct model::deps_collector {
    model&         m;
    top_sort&      ts;
    func_decl_set& s;
    array_util     autil;
    deps_collector(model& m, top_sort& ts, func_decl_set& s): m(m), ts(ts), s(s), autil(m.get_manager()) {}
    void operator()(app* a) {
        func_decl* f = a->get_decl();
        if (autil.is_as_array(f)) {
            f = autil.get_as_array_func_decl(a);            
        }
        if (m.has_interpretation(f)) {
            s.insert(f);
            ts.add_occurs(f);
        }
    }
    void operator()(expr* ) {}
};

struct model::occs_collector {
    top_sort&      ts;
    occs_collector(top_sort& ts): ts(ts) {}
    void operator()(func_decl* f) {
        ts.add_occurs(f);
    }
    void operator()(ast*) {}
};


model::func_decl_set* model::collect_deps(top_sort& ts, expr * e) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, ts, *s);
    if (e) for_each_expr(collector, e);
    return s;
}

model::func_decl_set* model::collect_deps(top_sort& ts, func_interp * fi) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, ts, *s);
    fi->compress();
    expr* e = fi->get_else();
    if (e) for_each_expr(collector, e);
    unsigned num_args = fi->get_arity();
    for (func_entry* fe : *fi) {
        for (unsigned i = 0; i < num_args; ++i) {
            for_each_expr(collector, fe->get_arg(i));
        }
        for_each_expr(collector, fe->get_result());
    }
    return s;
}


/**
   \brief Inline interpretations of skolem functions
*/

void model::cleanup_interp(top_sort& ts, func_decl* f, bool force_inline) {
    
    unsigned pid = ts.partition_id(f);
    expr * e1 = get_const_interp(f);
    if (e1) {
        expr_ref e2 = cleanup_expr(ts, e1, pid, force_inline);
        if (e2 != e1) 
            register_decl(f, e2);
        return;
    }
    func_interp* fi = get_func_interp(f);
    if (fi) {
        e1 = fi->get_else();
        expr_ref e2 = cleanup_expr(ts, e1, pid, force_inline);
        if (e1 != e2) 
            fi->set_else(e2);
        for (auto& fe : *fi) {
            e2 = cleanup_expr(ts, fe->get_result(), pid, force_inline);
            if (e2 != fe->get_result()) {
                fi->insert_entry(fe->get_args(), e2);
            }
        }
    }
}

void model::collect_occs(top_sort& ts, func_decl* f) {
    expr * e = get_const_interp(f);
    if (e) {
        collect_occs(ts, e);
    }
    else {
        func_interp* fi = get_func_interp(f);
        if (fi) {
            e = fi->get_else();
            if (e != nullptr)
               collect_occs(ts, e);
            for (auto const& fe : *fi) {
                collect_occs(ts, fe->get_result());
                for (unsigned i = 0; i < fi->get_arity(); ++i) {
                    collect_occs(ts, fe->get_arg(i));
                }
            }
        }
    }
}

void model::collect_occs(top_sort& ts, expr* e) {
    occs_collector collector(ts);
    for_each_ast(collector, e, true);
}

bool model::can_inline_def(top_sort& ts, func_decl* f, bool force_inline) {
    if (ts.occur_count(f) <= 1) return true;
    func_interp* fi = get_func_interp(f);
    if (!fi) 
        return false;
    if (fi->get_else() == nullptr) 
        return false;
    if (m_inline) 
        return true;
    expr* e = fi->get_else();
    obj_hashtable<expr> subs;
    ptr_buffer<expr> todo;
    todo.push_back(e);
    while (!todo.empty()) {
        if (!force_inline && fi->num_entries() + subs.size() > 8) 
            return false;
        expr* e = todo.back();
        todo.pop_back();
        if (subs.contains(e)) 
            continue;
        subs.insert(e);
        if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                todo.push_back(arg);
            }
        }
        else if (is_quantifier(e)) {
            todo.push_back(to_quantifier(e)->get_expr());
        }
    }
    return true;
}


expr_ref model::cleanup_expr(top_sort& ts, expr* e, unsigned current_partition, bool force_inline) {
    if (!e) return expr_ref(nullptr, m);

    TRACE("model", tout << "cleaning up:\n" << mk_pp(e, m) << "\n";);

    obj_map<expr, expr*> cache;
    expr_ref_vector trail(m);
    ptr_buffer<expr, 128> todo;
    ptr_buffer<expr> args;
    todo.push_back(e);
    array_util autil(m);
    bv_util bv(m);
    func_interp* fi = nullptr;
    unsigned pid = 0;
    expr_ref new_t(m);

    while (!todo.empty()) {
        expr* a = todo.back();
        switch(a->get_kind()) {
        case AST_APP: {
            app * t = to_app(a);
            func_decl* f = t->get_decl();
            bool visited = true;
            
            args.reset();
            for (expr* t_arg : *t) {
                expr * arg = nullptr;
                if (!cache.find(t_arg, arg)) {
                    visited = false;
                    todo.push_back(t_arg);
                }
                else {
                    args.push_back(arg);
                }
            }
            if (!visited) {
                continue;
            }
            fi = nullptr;
            new_t = nullptr;
            sort_ref_vector domain(m);
            if (autil.is_as_array(a)) {
                func_decl* f = autil.get_as_array_func_decl(a);
                // only expand auxiliary definitions that occur once.
                if (can_inline_def(ts, f, force_inline)) {
                    fi = get_func_interp(f);
                    if (fi) {
                        new_t = fi->get_array_interp(f);
                        TRACE("model", tout << "array interpretation:" << new_t << "\n";);
                    }
                }
            }

            if (new_t) {
                // noop
            }
            else if (f->is_skolem() && can_inline_def(ts, f, force_inline) && (fi = get_func_interp(f)) && 
                     fi->get_interp() && (!ts.find(f, pid) || pid != current_partition)) {
                var_subst vs(m, false);
                new_t = vs(fi->get_interp(), args.size(), args.data());
            }
            else if (bv.is_bit2bool(t)) {
                unsigned idx = f->get_parameter(0).get_int();
                new_t = m.mk_eq(bv.mk_extract(idx, idx, args[0]), bv.mk_numeral(1, 1));
            }
#if 0
            else if (is_uninterp_const(a) && !get_const_interp(f)) {
                new_t = get_some_value(f->get_range());
                register_decl(f, new_t);                
            }
#endif
            else {
                new_t = ts.m_rewrite.mk_app(f, args.size(), args.data());                
            }
            
            if (t != new_t.get()) trail.push_back(new_t);
            CTRACE("model", (t != new_t.get()), tout << mk_bounded_pp(t, m) << " " << new_t << "\n";);
            todo.pop_back();
            cache.insert(t, new_t);
            break;
        }
        default:
            SASSERT(a != nullptr);
            cache.insert(a, a);
            todo.pop_back();
            break;
        }
    }
    
    ts.m_rewrite(cache[e], new_t);
    return new_t;
}

void model::remove_decls(ptr_vector<func_decl> & decls, func_decl_set const & s) {
    unsigned j = 0;
    for (func_decl* f : decls) {
        if (!s.contains(f)) {
            decls[j++] = f;
        }
    }
    decls.shrink(j);
}

expr_ref model::unfold_as_array(expr* e) {
    func_decl* f = nullptr;
    array_util autil(m);
    if (!autil.is_as_array(e, f))
        return expr_ref(e, m);
    auto* fi = get_func_interp(f);
    if (!fi)
        return expr_ref(e, m);
    return fi->get_array_interp(f);
}


expr_ref model::get_inlined_const_interp(func_decl* f, bool force_inline) {
    expr* v = get_const_interp(f);
    if (!v) return expr_ref(nullptr, m);
    top_sort st(m);
    expr_ref result1(v, m);
    expr_ref result2 = cleanup_expr(st, v, UINT_MAX, force_inline);
    while (result1 != result2) {
        result1 = result2;
        result2 = cleanup_expr(st, result1, UINT_MAX, force_inline);
    }
    return result2;
}

expr_ref model::operator()(expr* t) {
    return m_mev(t);
}

void model::set_solver(expr_solver* s) {
    m_mev.set_solver(s);
}

bool model::has_solver() {
    return m_mev.has_solver();
}

expr_ref_vector model::operator()(expr_ref_vector const& ts) {
    expr_ref_vector rs(m);
    for (expr* t : ts) rs.push_back((*this)(t));
    return rs;
}

bool model::is_true(expr* t) {
    return m.is_true((*this)(t));
}

bool model::is_false(expr* t) {
    return m.is_false((*this)(t));
}

bool model::is_true(expr_ref_vector const& ts) {
    for (expr* t : ts) if (!is_true(t)) return false;
    return true;
}

bool model::is_false(expr_ref_vector const& ts) {
    for (expr* t : ts) if (is_false(t)) return true;
    return false;
}

bool model::are_equal(expr* s, expr* t) {
    return m_mev.are_equal(s, t);
}

void model::reset_eval_cache() {
    m_mev.reset();
}

void model::add_rec_funs() {
    recfun::util u(m);
    func_decl_ref_vector recfuns = u.get_rec_funs();
    for (func_decl* f : recfuns) {
        auto& def = u.get_def(f);
        expr* rhs = def.get_rhs();
        if (!rhs) 
            continue;
        if (has_interpretation(f))
            continue;
        if (f->get_arity() == 0) {
            register_decl(f, rhs);
            continue;
        }
                
        func_interp* fi = alloc(func_interp, m, f->get_arity());
        // reverse argument order so that variable 0 starts at the beginning.
        expr_safe_replace subst(m);
        unsigned arity = f->get_arity();
        for (unsigned i = 0; i < arity; ++i) {
            subst.insert(m.mk_var(arity - i - 1, f->get_domain(i)), m.mk_var(i, f->get_domain(i)));            
        }
        expr_ref bodyr(m);
        subst(rhs, bodyr);
        
        fi->set_else(bodyr);
        register_decl(f, fi);
    }
    TRACE("model", tout << *this << "\n";);
}
