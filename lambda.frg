#lang forge

-- Syntax: terms
abstract sig Term {}

-- Forge doesn't allow repeated field names, so manually disambiguate
sig Var extends Term {} 
sig Abs extends Term {x: one Var, term: one Term}
sig App extends Term {l_term, r_term: one Term}


fun allSubterms[t: Term]: set Term {
    t.^(x + term + l_term + r_term)
}

pred wellFormed {
    -- no cycles
    all t: Term | t not in allSubterms[t]

    -- single root term
    some t: Term | all subterm: Term | subterm in allSubterms[t] or t = subterm

    -- variables should only be bound once
    all v: Var | no disj t1, t2: Abs | t1.x = v and t2.x = v

    -- left and right term should be different terms
    all t: App | t.l_term != t.r_term

    -- left and right terms should be disjoint, except for variables which can be shared
    all t1: Term | {
        some t1.l_term implies {
            some t1.r_term implies {
                {{ some v1: Var | v1 = t1.l_term } or { some v2: Var | v2 = t1.r_term }} 
                or {
                    t1.l_term != t1.r_term
                    no t2: Term | {
                        reachable[t1.l_term, t2, l_term, r_term] and
                            reachable[t1.r_term, t2, l_term, r_term]
                    }
                }
            }
        }
    }

}

pred combinator {
    -- check that there are no free variables
    all v: Var | {
        some a: Abs | { 
            -- v should always be defined!
            a.x = v
            -- v should be reachable from the defining abstraction term
            reachable[v, a, x, term, l_term, r_term]
            -- there should be no way to refer to v before it's defined
            // This condition is a little complex — it's phrased as such because
            // we want to make sure that terms that reference a variable are
            // always reachable from the abstraction statement.
            // Without this condition, we see terms that reference later-declared
            // variables, which does not constitute a combinator.
            all t: Term | {t.term = v or t.l_term = v or t.r_term = v} implies 
                { reachable[t, a, x, term, l_term, r_term] or t.x = v }
        }
    }
}


BigCombinator: run {
    wellFormed
    combinator
    some t: Term | { #(allSubterms[t] & Var) > 2 }
} for 8 Term

