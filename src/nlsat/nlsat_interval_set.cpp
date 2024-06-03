/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_interval_set.cpp

Abstract:

    Sets of disjoint infeasible intervals.

Author:

    Leonardo de Moura (leonardo) 2012-01-11.

Revision History:

--*/
#include "nlsat/nlsat_interval_set.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/buffer.h"

namespace nlsat {

    struct interval {
        unsigned  m_lower_open:1;
        unsigned  m_upper_open:1;
        unsigned  m_lower_inf:1;
        unsigned  m_upper_inf:1;
        literal   m_justification;
        clause const* m_clause;
        anum      m_lower;
        anum      m_upper;
    };

    class interval_set {
    public:
        static unsigned get_obj_size(unsigned num) { return sizeof(interval_set) + num*sizeof(interval); }
        unsigned  m_num_intervals;
        unsigned  m_ref_count:31;
        unsigned  m_full:1;
        interval  m_intervals[0];
    };

    void display(std::ostream & out, anum_manager & am, interval const & curr) {
        if (curr.m_lower_inf) {
            out << "(-oo, ";
        }
        else {
            if (curr.m_lower_open)
                    out << "(";
            else
                out << "[";
            am.display_decimal(out, curr.m_lower);
            out << ", ";
        }
        if (curr.m_justification.sign())
            out << "~";
        out << "p";
        out << curr.m_justification.var() << ", ";
        if (curr.m_upper_inf) {
            out << "oo)";
        }
        else {
            am.display_decimal(out, curr.m_upper);
            if (curr.m_upper_open)
                out << ")";
            else
                out << "]";
        }
    }

    bool check_interval(anum_manager & am, interval const & i) {
        SASSERT(!i.m_lower_inf || i.m_lower_open);        
        SASSERT(!i.m_upper_inf || i.m_upper_open);
        
        if (!i.m_lower_inf && !i.m_upper_inf) {
            auto s = am.compare(i.m_lower, i.m_upper);
            (void)s;
            TRACE("nlsat_interval", tout << "lower: "; am.display_decimal(tout, i.m_lower); tout << ", upper: "; am.display_decimal(tout, i.m_upper);
                  tout << "\ns: " << s << "\n";);
            SASSERT(s <= 0);
            SASSERT(!is_zero(s) || (!i.m_lower_open && !i.m_upper_open));
        }
        return true;
    }

    bool check_no_overlap(anum_manager & am, interval const & curr, interval const & next) {
        SASSERT(!curr.m_upper_inf);
        SASSERT(!next.m_lower_inf);
        sign s = am.compare(curr.m_upper, next.m_lower);
        CTRACE("nlsat", s > 0, display(tout, am, curr); tout << "  "; display(tout, am, next); tout << "\n";);
        SASSERT(s <= 0);
        SASSERT(!is_zero(s) || curr.m_upper_open || next.m_lower_open);        
        (void)s;
        return true;
    }
    
    // Check if the intervals are valid, ordered, and are disjoint.
    bool check_interval_set(anum_manager & am, unsigned sz, interval const * ints) {
#ifdef Z3DEBUG
        for (unsigned i = 0; i < sz; i++) {
            interval const & curr = ints[i];
            SASSERT(check_interval(am, curr));
            SASSERT(i >= sz - 1 || check_no_overlap(am, curr, ints[i+1]));                
        }
#endif            
        return true;
    }

    interval_set_manager::interval_set_manager(anum_manager & m, small_object_allocator & a):
        m_am(m),
        m_allocator(a) {
    }
     
    interval_set_manager::~interval_set_manager() {
    }
    
    void interval_set_manager::del(interval_set * s) {
        if (s == nullptr)
            return;
        unsigned num    = s->m_num_intervals;
        unsigned obj_sz = interval_set::get_obj_size(num);
        for (unsigned i = 0; i < num; i++) {
            m_am.del(s->m_intervals[i].m_lower);
            m_am.del(s->m_intervals[i].m_upper);
        }
        s->~interval_set();
        m_allocator.deallocate(obj_sz, s);
    }

    void interval_set_manager::dec_ref(interval_set * s) {
        SASSERT(s->m_ref_count > 0);
        s->m_ref_count--;
        if (s->m_ref_count == 0)
            del(s);
    }

    void interval_set_manager::inc_ref(interval_set * s) {
        s->m_ref_count++;
    }
    
    interval_set * interval_set_manager::mk(bool lower_open, bool lower_inf, anum const & lower, 
                                            bool upper_open, bool upper_inf, anum const & upper,
                                            literal justification, clause const* cls) {
        void * mem = m_allocator.allocate(interval_set::get_obj_size(1));
        interval_set * new_set = new (mem) interval_set();
        new_set->m_num_intervals = 1;
        new_set->m_ref_count  = 0;
        new_set->m_full       = lower_inf && upper_inf;
        interval * i = new (new_set->m_intervals) interval();
        i->m_lower_open = lower_open;
        i->m_lower_inf  = lower_inf;
        i->m_upper_open = upper_open;
        i->m_upper_inf  = upper_inf;
        i->m_justification = justification;
        i->m_clause = cls;
        if (!lower_inf)
            m_am.set(i->m_lower, lower);
        if (!upper_inf)
            m_am.set(i->m_upper, upper);
        SASSERT(check_interval_set(m_am, 1, new_set->m_intervals));
        return new_set;
    }

    inline ::sign compare_lower_lower(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_lower_inf && i2.m_lower_inf)
            return sign_zero;
        if (i1.m_lower_inf)
            return sign_neg;
        if (i2.m_lower_inf)
            return sign_pos;
        SASSERT(!i1.m_lower_inf && !i2.m_lower_inf);
        ::sign s = am.compare(i1.m_lower, i2.m_lower);
        if (!is_zero(s)) 
            return s;
        if (i1.m_lower_open == i2.m_lower_open)
            return sign_zero;
        if (i1.m_lower_open)
            return sign_pos;
        else
            return sign_neg;
    }

    inline ::sign compare_upper_upper(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_upper_inf && i2.m_upper_inf)
            return sign_zero;
        if (i1.m_upper_inf)
            return sign_pos;
        if (i2.m_upper_inf)
            return sign_neg;
        SASSERT(!i1.m_upper_inf && !i2.m_upper_inf);
        auto s = am.compare(i1.m_upper, i2.m_upper);
        if (!::is_zero(s)) 
            return s;
        if (i1.m_upper_open == i2.m_upper_open)
            return sign_zero;
        if (i1.m_upper_open)
            return sign_neg;
        else
            return sign_pos;
    }

    inline ::sign compare_upper_lower(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_upper_inf || i2.m_lower_inf) {
            TRACE("nlsat_interval", nlsat::display(tout << "i1: ", am, i1); nlsat::display(tout << "i2: ", am, i2););
            return sign_pos;
        }
        SASSERT(!i1.m_upper_inf && !i2.m_lower_inf);
        auto s = am.compare(i1.m_upper, i2.m_lower);
        TRACE("nlsat_interval", nlsat::display(tout << "i1: ", am, i1); nlsat::display(tout << " i2: ", am, i2); 
              tout << " compare: " << s << "\n";);
        if (!::is_zero(s))
            return s;
        if (!i1.m_upper_open && !i2.m_lower_open)
            return sign_zero;
        return sign_neg;
    }
    
    typedef sbuffer<interval, 128> interval_buffer;

    // Given two interval in an interval set s.t. curr occurs before next.
    // We say curr and next are "adjacent" iff
    //      there is no "space" between them.
    bool adjacent(anum_manager & am, interval const & curr, interval const & next) {
        SASSERT(!curr.m_upper_inf);
        SASSERT(!next.m_lower_inf);
        auto sign = am.compare(curr.m_upper, next.m_lower);
        SASSERT(sign != sign_pos);
        if (is_zero(sign)) {
            SASSERT(curr.m_upper_open || next.m_lower_open);
            return !curr.m_upper_open || !next.m_lower_open;
        }
        return false;
    }

    inline void push_back(anum_manager & am, interval_buffer & buf, 
                          bool lower_open, bool lower_inf, anum const & lower, 
                          bool upper_open, bool upper_inf, anum const & upper,
                          literal justification) {
        buf.push_back(interval());
        interval & i = buf.back();
        i.m_lower_open = lower_open;
        i.m_lower_inf  = lower_inf;
        am.set(i.m_lower, lower);
        i.m_upper_open = upper_open;
        i.m_upper_inf  = upper_inf;
        am.set(i.m_upper, upper);
        i.m_justification = justification;
        SASSERT(check_interval(am, i));
    }

    inline void push_back(anum_manager & am, interval_buffer & buf, interval const & i) {
        push_back(am, buf,
                  i.m_lower_open, i.m_lower_inf, i.m_lower,
                  i.m_upper_open, i.m_upper_inf, i.m_upper,
                  i.m_justification);
    }

    inline interval_set * mk_interval(small_object_allocator & allocator, interval_buffer & buf, bool full) {
        unsigned sz = buf.size();
        void * mem = allocator.allocate(interval_set::get_obj_size(sz));
        interval_set * new_set = new (mem) interval_set();
        new_set->m_full = full;
        new_set->m_ref_count  = 0;
        new_set->m_num_intervals = sz;
        memcpy(new_set->m_intervals, buf.data(), sizeof(interval)*sz);
        return new_set;
    }

    interval_set * interval_set_manager::mk_union(interval_set const * s1, interval_set const * s2) {
        TRACE("nlsat_interval", tout << "mk_union\ns1: "; display(tout, s1); tout << "\ns2: "; display(tout, s2); tout << "\n";);
        if (s1 == nullptr || s1 == s2)
            return const_cast<interval_set*>(s2);
        if (s2 == nullptr)
            return const_cast<interval_set*>(s1);
        if (s1->m_full)
            return const_cast<interval_set*>(s1);
        if (s2->m_full)
            return const_cast<interval_set*>(s2);
        interval_buffer result;
        unsigned sz1 = s1->m_num_intervals;
        unsigned sz2 = s2->m_num_intervals;
        unsigned i1  = 0;
        unsigned i2  = 0;
        while (true) {
            if (i1 >= sz1) {
                while (i2 < sz2) {
                    TRACE("nlsat_interval", tout << "adding remaining intervals from s2: "; nlsat::display(tout, m_am, s2->m_intervals[i2]); tout << "\n";);
                    push_back(m_am, result, s2->m_intervals[i2]);
                    i2++;
                }
                break;
            }
            if (i2 >= sz2) {
                while (i1 < sz1) {
                    TRACE("nlsat_interval", tout << "adding remaining intervals from s1: "; nlsat::display(tout, m_am, s1->m_intervals[i1]); tout << "\n";);
                    push_back(m_am, result, s1->m_intervals[i1]);
                    i1++;
                }
                break;
            }
            interval const & int1 = s1->m_intervals[i1];
            interval const & int2 = s2->m_intervals[i2];
            int l1_l2_sign = compare_lower_lower(m_am, int1, int2);
            int u1_u2_sign = compare_upper_upper(m_am, int1, int2);
            TRACE("nlsat_interval", 
                  tout << "i1: " << i1 << ", i2: " << i2 << "\n";
                  tout << "int1: "; nlsat::display(tout, m_am, int1); tout << "\n";
                  tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
            if (l1_l2_sign <= 0) {
                if (u1_u2_sign == 0) {
                    // Cases:
                    // 1)  [     ]
                    //     [     ]
                    //
                    // 2) [     ]
                    //      [   ]
                    //
                    TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign == 0\n";);
                    push_back(m_am, result, int1);
                    i1++;
                    i2++;
                }
                else if (u1_u2_sign > 0) {
                    // Cases:
                    //
                    // 1) [        ]
                    //    [     ]
                    //
                    // 2) [        ]
                    //      [   ]
                    i2++;
                    TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign > 0\n";);
                    // i1 may consume other intervals of s2
                }
                else {
                    SASSERT(u1_u2_sign < 0);
                    int u1_l2_sign = compare_upper_lower(m_am, int1, int2);
                    if (u1_l2_sign < 0) {
                        SASSERT(l1_l2_sign < 0);
                        // Cases:
                        // 1)   [      ]
                        //                [     ]
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign < 0\n";);
                        push_back(m_am, result, int1);
                        i1++;
                    }
                    else if (u1_l2_sign == 0) {
                        SASSERT(l1_l2_sign <= 0);
                        SASSERT(!int1.m_upper_open && !int2.m_lower_open);
                        SASSERT(!int2.m_lower_inf);
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign == 0\n";);
                        // Cases:
                        if (l1_l2_sign != 0) {
                            SASSERT(l1_l2_sign < 0);
                            // 1)   [   ]
                            //          [    ]
                            SASSERT(!int2.m_lower_open);
                            push_back(m_am, result, 
                                      int1.m_lower_open, int1.m_lower_inf,  int1.m_lower,
                                      true /* open */, false /* not +oo */, int1.m_upper, 
                                      int1.m_justification); 
                            i1++;
                        }
                        else {
                            SASSERT(l1_l2_sign == 0);
                            // 2)   u          <<< int1 is a singleton
                            //      [     ]
                            // just consume int1
                            i1++;
                        }
                    }
                    else {
                        SASSERT(l1_l2_sign <= 0);
                        SASSERT(u1_u2_sign < 0);
                        SASSERT(u1_l2_sign > 0);
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign > 0\n";);
                        if (l1_l2_sign == 0) {
                            // Case:
                            // 1)   [      ]
                            //      [          ]
                            // just consume int1
                            i1++;
                        }
                        else {
                            SASSERT(l1_l2_sign < 0);
                            SASSERT(u1_u2_sign < 0);
                            SASSERT(u1_l2_sign > 0);
                            // 2) [        ]
                            //         [        ]
                            push_back(m_am, result, 
                                      int1.m_lower_open,     int1.m_lower_inf, int1.m_lower,
                                      !int2.m_lower_open, false /* not +oo */, int2.m_lower,
                                      int1.m_justification); 
                            i1++;
                        }
                    }
                }
            }
            else {
                SASSERT(l1_l2_sign > 0);
                if (u1_u2_sign == 0) {
                    TRACE("nlsat_interval", tout << "l2 < l1 <= u1 = u2\n";);
                    // Case:
                    // 1)    [  ]
                    //    [     ]
                    //
                    push_back(m_am, result, int2);
                    i1++;
                    i2++;
                }
                else if (u1_u2_sign < 0) {
                    TRACE("nlsat_interval", tout << "l2 < l1 <= u2 < u2\n";);
                    // Case:
                    // 1)   [   ]
                    //    [       ]
                    i1++;
                    // i2 may consume other intervals of s1
                }
                else {
                    auto u2_l1_sign = compare_upper_lower(m_am, int2, int1);
                    if (u2_l1_sign < 0) {
                        TRACE("nlsat_interval", tout << "l2 <= u2 < l1 <= u1\n";);
                        // Case:
                        // 1)           [      ]
                        //     [     ]
                        push_back(m_am, result, int2);
                        i2++;
                    }
                    else if (is_zero(u2_l1_sign)) {
                        TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign > 0, u2_l1_sign == 0\n";);
                        SASSERT(!int1.m_lower_open && !int2.m_upper_open);
                        SASSERT(!int1.m_lower_inf);
                        // Case:
                        //      [    ]   
                        //  [   ]
                        push_back(m_am, result, 
                                  int2.m_lower_open,     int2.m_lower_inf, int2.m_lower,
                                  true /* open */,    false /* not +oo */, int2.m_upper, 
                                  int2.m_justification); 
                        i2++;
                    }
                    else {
                        TRACE("nlsat_interval", tout << "l2 < l1 < u2 < u1\n";);
                        SASSERT(l1_l2_sign > 0);
                        SASSERT(u1_u2_sign > 0);
                        SASSERT(u2_l1_sign > 0);
                        // Case:
                        //     [        ]
                        // [        ]
                        push_back(m_am, result, 
                                  int2.m_lower_open,     int2.m_lower_inf, int2.m_lower,
                                  !int1.m_lower_open, false /* not +oo */, int1.m_lower,
                                  int2.m_justification); 
                        i2++;
                    }
                }
            }
            SASSERT(result.size() <= 1 ||
                    check_no_overlap(m_am, result[result.size() - 2], result[result.size() - 1]));

        }

        SASSERT(!result.empty());
        SASSERT(check_interval_set(m_am, result.size(), result.data()));
        // Compress
        // Remark: we only combine adjacent intervals when they have the same justification
        unsigned j  = 0;
        unsigned sz = result.size(); 
        for (unsigned i = 1; i < sz; i++) {
            interval & curr = result[j];
            interval & next = result[i];
            if (curr.m_justification == next.m_justification && 
                adjacent(m_am, curr, next)) {
                // merge them
                curr.m_upper_inf  = next.m_upper_inf;
                curr.m_upper_open = next.m_upper_open;
                m_am.swap(curr.m_upper, next.m_upper);
            }
            else {
                j++;
                if (i != j) {
                    interval & next_curr = result[j];
                    next_curr.m_lower_inf = next.m_lower_inf;
                    next_curr.m_lower_open = next.m_lower_open;
                    m_am.swap(next_curr.m_lower, next.m_lower);
                    next_curr.m_upper_inf = next.m_upper_inf;
                    next_curr.m_upper_open = next.m_upper_open;
                    m_am.swap(next_curr.m_upper, next.m_upper);
                    next_curr.m_justification = next.m_justification;
                }
            }
        }
        j++;
        for (unsigned i = j; i < sz; i++) {
            interval & curr = result[i];
            m_am.del(curr.m_lower);
            m_am.del(curr.m_upper);
        }
        result.shrink(j);
        SASSERT(check_interval_set(m_am, result.size(), result.data()));
        sz = j;
        SASSERT(sz >= 1);
        bool found_slack  = !result[0].m_lower_inf || !result[sz-1].m_upper_inf;
        // Check if full
        for (unsigned i = 0; i < sz - 1 && !found_slack; i++) {
            if (!adjacent(m_am, result[i], result[i+1]))
                found_slack = true;
        }
        // Create new interval set
        interval_set * new_set = mk_interval(m_allocator, result, !found_slack);
        SASSERT(check_interval_set(m_am, sz, new_set->m_intervals));
        return new_set;
    }

    bool interval_set_manager::is_full(interval_set const * s) {
        if (s == nullptr)
            return false;
        return s->m_full == 1;
    }

    unsigned interval_set_manager::num_intervals(interval_set const * s) const {
        if (s == nullptr) return 0;
        return s->m_num_intervals;
    }
    
    bool interval_set_manager::subset(interval_set const * s1, interval_set const * s2) {
        if (s1 == s2)
            return true;
        if (s1 == nullptr)
            return true;
        if (s2 == nullptr)
            return false;
        if (s2->m_full)
            return true;
        if (s1->m_full)
            return false;
        unsigned sz1 = s1->m_num_intervals;
        unsigned sz2 = s2->m_num_intervals;
        SASSERT(sz1 > 0 && sz2 > 0);
        unsigned i1  = 0;
        unsigned i2  = 0;
        while (i1 < sz1 && i2 < sz2) {
            interval const & int1 = s1->m_intervals[i1];
            interval const & int2 = s2->m_intervals[i2];
            TRACE("nlsat_interval", tout << "subset main loop, i1: " << i1 << ", i2: " << i2 << "\n";
                  tout << "int1: "; nlsat::display(tout, m_am, int1); tout << "\n";
                  tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
            if (compare_lower_lower(m_am, int1, int2) < 0) {
                TRACE("nlsat_interval", tout << "done\n";);
                // interval [int1.lower1, int2.lower2] is not in s2
                // s1: [ ...
                // s2:    [ ...
                return false;
            }
            while (i2 < sz2) {
                interval const & int2 = s2->m_intervals[i2];
                TRACE("nlsat_interval", tout << "inner loop, i2: " << i2 << "\n";
                      tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
                int u1_u2_sign = compare_upper_upper(m_am, int1, int2);
                if (u1_u2_sign == 0) {
                    TRACE("nlsat_interval", tout << "case 1, break\n";);
                    // consume both
                    // s1: ... ]
                    // s2: ... ]
                    i1++;
                    i2++;
                    break;
                }
                else if (u1_u2_sign < 0) {
                    TRACE("nlsat_interval", tout << "case 2, break\n";);
                    // consume only int1, int2 may cover other intervals of s1 
                    // s1:  ... ]
                    // s2:    ... ]
                    i1++;
                    break;
                }
                else {
                    SASSERT(u1_u2_sign > 0);
                    int u2_l1_sign = compare_upper_lower(m_am, int2, int1);
                    TRACE("nlsat_interval", tout << "subset, u2_l1_sign: " << u2_l1_sign << "\n";);
                    if (u2_l1_sign < 0) {
                        TRACE("nlsat_interval", tout << "case 3, break\n";);
                        // s1:           [ ...
                        // s2: [ ... ]  ...
                        i2++;
                        break;
                    }
                    SASSERT(u2_l1_sign >= 0);
                    // s1:      [ ...  ]
                    // s2: [ ...    ]
                    if (i2 == sz2 - 1) {
                        TRACE("nlsat_interval", tout << "case 4, done\n";);
                        // s1:   ... ]
                        // s2: ...]
                        // the interval [int2.upper, int1.upper] is not in s2
                        return false; // last interval of s2
                    }
                    interval const & next2 = s2->m_intervals[i2+1];
                    if (!adjacent(m_am, int2, next2)) {
                        TRACE("nlsat_interval", tout << "not adjacent, done\n";);
                        // s1:   ... ]
                        // s2: ... ]   [
                        // the interval [int2.upper, min(int1.upper, next2.lower)] is not in s2
                        return false;
                    }
                    TRACE("nlsat_interval", tout << "continue..\n";);
                    // continue with adjacent interval of s2
                    // s1:    ...  ]
                    // s2:  ..][ ...
                    i2++;
                }
            }
        }
        return i1 == sz1;
    }

    bool interval_set_manager::set_eq(interval_set const * s1, interval_set const * s2) {
        if (s1 == nullptr || s2 == nullptr)
            return s1 == s2;
        if (s1->m_full || s2->m_full)
            return s1->m_full == s2->m_full;
        // TODO: check if bottleneck, then replace simple implementation
        return subset(s1, s2) && subset(s2, s1);
    }
        
    bool interval_set_manager::eq(interval_set const * s1, interval_set const * s2) {
        if (s1 == nullptr || s2 == nullptr)
            return s1 == s2;
        if (s1->m_num_intervals != s2->m_num_intervals)
            return false;
        for (unsigned i = 0; i < s1->m_num_intervals; i++) {
            interval const & int1 = s1->m_intervals[i];
            interval const & int2 = s2->m_intervals[i]; 
            if (int1.m_lower_inf  != int2.m_lower_inf ||
                int1.m_lower_open != int2.m_lower_open ||
                int1.m_upper_inf  != int2.m_upper_inf ||
                int1.m_upper_open != int2.m_upper_open ||
                int1.m_justification != int2.m_justification ||
                !m_am.eq(int1.m_lower, int2.m_lower) ||
                !m_am.eq(int1.m_upper, int2.m_upper))
                return false;
        }
        return true;
    }

    void interval_set_manager::get_justifications(interval_set const * s, literal_vector & js, ptr_vector<clause>& clauses) {
        js.reset();
        clauses.reset();
        unsigned num = num_intervals(s);
        for (unsigned i = 0; i < num; i++) {
            literal l     = s->m_intervals[i].m_justification;
            unsigned lidx = l.index();
            if (m_already_visited.get(lidx, false))
                continue;
            m_already_visited.setx(lidx, true, false);
            js.push_back(l);
            if (s->m_intervals[i].m_clause) 
                clauses.push_back(const_cast<clause*>(s->m_intervals[i].m_clause));
        }
        for (unsigned i = 0; i < num; i++) {
            literal l     = s->m_intervals[i].m_justification;
            unsigned lidx = l.index();
            m_already_visited[lidx] = false;
        }
    }
    
    interval_set * interval_set_manager::get_interval(interval_set const * s, unsigned idx) const {
        SASSERT(idx < num_intervals(s));
        interval_buffer result;
        push_back(m_am, result, s->m_intervals[idx]);
        bool found_slack  = !result[0].m_lower_inf || !result[0].m_upper_inf;
        interval_set * new_set = mk_interval(m_allocator, result, !found_slack);
        SASSERT(check_interval_set(m_am, result.size(), new_set->m_intervals));
        return new_set;
    }

    void interval_set_manager::pick_randomly_with_no_restrictions(bool is_int, anum & w, bool randomize) {
           if (randomize) {
                int num = m_rand() % 2 == 0 ? 1 : -1;
#define MAX_RANDOM_DEN_K 4
                int den_k = (m_rand() % MAX_RANDOM_DEN_K);
                int den   = is_int ? 1 : (1 << den_k);
                scoped_mpq _w(m_am.qm());
                m_am.qm().set(_w, num, den);
                m_am.set(w, _w);
            }
           else {
                m_am.set(w, 0);
            }
    }

    void interval_set_manager::pick_in_unbounded_intervals(interval_set const* s, anum& w, bool randomize, unsigned &n) {
        if (!s->m_intervals[0].m_lower_inf) {
            SASSERT(n==0);
            n++;
            // lower is finite, and we can pick in (-oo, m_lower)
            m_am.int_lt(s->m_intervals[0].m_lower, w);
            if (!randomize)
                return;
        }
        unsigned num = s->m_num_intervals;
        if (!s->m_intervals[num-1].m_upper_inf) {
            n++;
            if (m_rand()%n ==0) // upper is finite, so we look int (m_upper, oo)             
                m_am.int_gt(s->m_intervals[num-1].m_upper, w);
            
        }
    }

    void interval_set_manager::pick_in_non_trivial_gaps(interval_set const *s, anum& w, bool randomize, unsigned &n) {
        // Look for  a gap with some interior
        for (unsigned i = 1; i < s->m_num_intervals; i++) {
            if (m_am.lt(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower)) {
                n++;
                if (n == 1 || m_rand()%n == 0)
                    m_am.select(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower, w);
                if (!randomize)
                    return;
            }            
        }
    }

    bool belongs_to_interval( const anum &w, interval const &i, anum_manager& am) {
        if (i.m_lower_inf && i.m_upper_inf) {
            // If the interval is (-inf, inf), then any number belongs to it
            return true;
        }
        auto &l = i.m_lower; auto &u = i.m_upper;

        if (!i.m_lower_inf && i.m_upper_inf) {
            // (l, oo) or [l, oo)
            return am.lt(l, w) || (!i.m_lower_open && am.eq(l,w));
        }

        if (i.m_lower_inf && !i.m_upper_inf) {            
            // (-oo, u)
            return am.lt(w, u) || (!i.m_upper_open && am.eq(w, u));
        }

        SASSERT(!(i.m_lower_inf || i.m_upper_inf)); // non-infinite nterval
        
        return (am.lt(l, w) || (!i.m_lower_open && am.eq(l,w))) && 
            (am.lt(w, u) || (!i.m_upper_open && am.eq(w, u)));

        return false;
    }
    
    bool belongs_to(const anum &w, interval_set const *s, anum_manager& am) {
        if (s == nullptr)
            return false;
         for (unsigned i = 0; i < s->m_num_intervals; i++) {
             if (belongs_to_interval(w, s->m_intervals[i], am))
                 return true;
         }            
         
         return false;
    }
    
    void interval_set_manager::pick_in_compliment(interval_set const * s, bool is_int, anum & w, bool randomize) {
         pick_in_compliment_(s, is_int, w, randomize);
    }
    
   bool pick_in_compliment_int_case_l_r(const interval &l, const interval &r, anum& w, anum_manager & m_am) {
       bool ao = l.m_upper_open;
       bool bo = r.m_lower_open;

        if (m_am.eq(l.m_upper, r.m_lower)) {    
            if (ao && bo) {
                m_am.set(w, l.m_upper);   //  ...)(...  
                TRACE("nlsat_interval_set_pick", tout << "found w:"; m_am.display_decimal(tout, w) << "\n";);
                return true;
            }
            return false;  // ...)[... or ...](...
        } 
        SASSERT(m_am.lt(l.m_upper, r.m_lower));
        if (m_am.is_int(l.m_upper)) {
            if (ao) {
                TRACE("nlsat_interval_set_pick", tout << "found w:"; m_am.display_decimal(tout, w) << "\n";);
                m_am.set(w, l.m_upper);
                return true;
            }
            m_am.add(l.m_upper, 1, w);
            if (m_am.lt(w, r.m_lower) || (m_am.eq(w, r.m_lower) && bo)) {
                TRACE("nlsat_interval_set_pick", tout << "found w:"; m_am.display_decimal(tout, w) << "\n";);
                return true;
            }
            return false;
        }
        SASSERT(!m_am.is_int(l.m_upper));
        m_am.ceil(l.m_upper, w);
        if (m_am.lt(w, r.m_lower) || (m_am.eq(w, r.m_lower) && bo)) {
            TRACE("nlsat_interval_set_pick", tout << "found w:"; m_am.display_decimal(tout, w) << "\n";);
            return true;
        }
        return false;
    }

    bool has_int_in_the_gap(const interval &l, const interval &r, anum_manager & m_am) {
        TRACE("nlsat_interval_set_pick", tout << "l, r:"; display(tout, m_am, l); tout <<","; display(tout, m_am, r);  tout << "\n";);
        if (m_am.eq(l.m_upper, r.m_lower))  {
            /*  ...)(...  */            
            if (l.m_upper_open && r.m_lower_open && m_am.is_int(l.m_upper)) { 
                TRACE("nlsat_interval_set_pick", tout << "found a gap containing int \n";);
                return true;
            }
            return false;  // ...)[... or ...](...
        } 
        const auto& a = l.m_upper;
        const auto& b = r.m_lower;
        SASSERT(m_am.lt(a, b)); 
        scoped_anum t(m_am);
        m_am.add(a, 1, t);
        if (m_am.lt(t, b)) 
            return true;  // the length of the interval is greater than 1
        
        if (m_am.is_int(a)) { 
            if (l.m_upper_open) {
               TRACE("nlsat_interval_set_pick", tout << "found a gap containing int\n";);
               return true; 
               
            }
		
                // the only candidate now is a+1, becase a+2 is too large, and a+1 feasible only if 
                // b is int and r.m_lower_open
			SASSERT(!m_am.is_int(b)|| m_am.eq(b, t));
            return r.m_lower_open && m_am.is_int(b);
        }
        SASSERT(!m_am.is_int(a));
        m_am.ceil(a, t);
        bool ret = m_am.lt(t, b) || (m_am.eq(t, b) && r.m_lower_open);
        if (ret) {
            TRACE("nlsat_interval_set_pick", tout << "found a gap containing int\n";);            
        } else {
            TRACE("nlsat_interval_set_pick", tout << "cannot pick an int\n";);
        }
        return ret;
    }   

    bool interval_set_manager::is_int_full(interval_set const *s)  {
        if (s == nullptr)
            return false;
        unsigned num = s->m_num_intervals;
        if (s->m_intervals[0].m_lower_inf == false || s->m_intervals[num-1].m_upper_inf == false)
            return false;
        for (unsigned i = 1; i < num; i++) {
            auto& l = s->m_intervals[i - 1];  // (l) (r)
            auto& r = s->m_intervals[i];
            if (has_int_in_the_gap(l, r, m_am)) {
                return false;
            }
        }
        TRACE("nlsat_interval_set_pick", tout << "covers int:"; display(tout, s) << "\n";);
        return true;
     }
    
    
    bool interval_set_manager::pick_in_compliment_int_case(interval_set const * s, anum & w, bool randomize) {
        TRACE("nlsat_interval_set_pick", tout << "picking an int:"; display(tout, s) << "\n";);

        unsigned num  = s->m_num_intervals;
        SASSERT(s->m_intervals[0].m_lower_inf && s->m_intervals[num-1].m_upper_inf);
        int n = 0;
        scoped_anum ww(m_am);
        for (unsigned i = 1; i < num; i++) {
            const auto& l = s->m_intervals[i - 1];  // (l) (r)
            const auto& r = s->m_intervals[i];
            if (pick_in_compliment_int_case_l_r(l, r, ww, m_am)) {
                n++;
                if (randomize && (n == 1 || m_rand() % n == 0)) {
                    m_am.set(w, ww);
                    TRACE("nlsat_interval_set_pick", tout << "i:" << i << "\n";);
                }
            }
        }
        CTRACE("nlsat_interval_set_pick", n > 0, tout << "pick int:"; m_am.display_decimal(tout, w); tout <<  " in "; display(tout, s) << "\n";);
        return n > 0;
    }
    
    void interval_set_manager::pick_in_compliment_(interval_set const * s, bool is_int, anum & w, bool randomize) {
        TRACE("nlsat_interval_set_pick", tout << "start look into:"; display(tout, s)<<"\n";);
        SASSERT(!is_full(s));
        if (s == nullptr) {
            pick_randomly_with_no_restrictions(is_int, w, randomize);
            return;
        }
        unsigned n = 0;
        pick_in_unbounded_intervals(s, w, randomize, n);

        if (is_int) {
            if (n > 0) {
                SASSERT(m_am.is_int(w));
                return;
            }
            if (pick_in_compliment_int_case(s, w, randomize)) {
                SASSERT(! belongs_to(w, s, m_am));
                return;
            }

        }
        
        pick_in_non_trivial_gaps(s, w, randomize, n);
        if (n > 0)
            return;
        
        // Try to find a rational: todo - randomise
        unsigned irrational_i = UINT_MAX;
        for (unsigned i = 1; i < s->m_num_intervals; i++) {
            if (s->m_intervals[i-1].m_upper_open && s->m_intervals[i].m_lower_open) {
                SASSERT(m_am.eq(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower)); // otherwise we would have found it in the previous step
                if (m_am.is_rational(s->m_intervals[i-1].m_upper)) {                    
                    m_am.set(w, s->m_intervals[i-1].m_upper);
                    return;
                }
                if (irrational_i == UINT_MAX)
                    irrational_i = i - 1;
            }
        }

        SASSERT(irrational_i != UINT_MAX);
        // Last option: pick irrational witness :-(
        SASSERT(s->m_intervals[irrational_i].m_upper_open && s->m_intervals[irrational_i+1].m_lower_open);
        m_am.set(w, s->m_intervals[irrational_i].m_upper);
    }

    std::ostream& interval_set_manager::display(std::ostream & out, interval_set const * s) const {
        if (s == nullptr) {
            out << "{}";
            return out;
        }
        out << "{";
        for (unsigned i = 0; i < s->m_num_intervals; i++) {
            if (i > 0)
                out << ", ";
            nlsat::display(out, m_am, s->m_intervals[i]);
        }
        out << "}";
        if (s->m_full)
            out << "*";
        return out;
    }

};
