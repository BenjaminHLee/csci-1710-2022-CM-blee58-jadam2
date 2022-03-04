#lang forge "cm" "srl35btbyptizwmm"

-- Syntax: terms
abstract sig Term {
    size: one Int,
    evaluated: set Term
}

-- Forge doesn't allow repeated field names, so manually disambiguate
sig Var extends Term {} 
sig Abs extends Term {x: one Var, term: one Term}
sig App extends Term {l_term, r_term: one Term}

one sig Eval {
    // Same order used in the notation, i.e. term[var := replacement] = result
    substituted : pfunc Term -> Var -> Term -> Term
}

fun allSubterms[t: Term]: set Term {
    t.^(x + term + l_term + r_term)
}

pred termSize {
    all v : Var | v.size = 1
    all abs : Abs | abs.size = add[abs.term.size, 1]
    all app : App | app.size = add[1, app.l_term.size, app.r_term.size]
}


pred substitutions {
    // for all substitutions it must hold that
    all replacement : Term, variable : Var | {
        all input : Var, output : Term | Eval.substituted[input, variable, replacement] = output implies {
            {input = variable => output = replacement else output = input}
        }
        all input : Abs, output : Term | Eval.substituted[input, variable, replacement] = output implies {
            // Abstractions substitute  to abstractions
            output in Abs
            // Substitution is applied to inner term
            output.term = Eval.substituted[input.term, variable, replacement]
        }
        all input: App, output: Term | Eval.substituted[input, variable, replacement] = output implies {
            // Applications substitute to applications
            output in App

            // recursively substitute each subterm
            output.l_term = Eval.substituted[input.l_term, variable, replacement]
            output.r_term = Eval.substituted[input.r_term, variable, replacement]
        }
    }
}

pred betaReduction[input : Term, output : Term] {
    input in App
    input.l_term in Abs
    output = Eval.substituted[input.l_term.term, input.l_term.x, input.r_term]
}

pred reductions {
    // For any term that reduces to another it must hold that
    all left, right : Term | right in left.evaluated implies {
        // it got there by reduction
        (some subt, subtReduced : Term | {
            subt in allSubterms[left]  
            subtReduced in allSubterms[right]
            betaReduction[subt, subtReduced]
        }
        // we can expand this later if we wan to allow alpha conversion for instance
        
        // Interesting question: should we allow these no-op "reductions"? If not `evaluated` must be `pfunc`
        // or left = right
        )
    }
}

pred evaluatesTo[from : Term, to : Term] {
    reachable[to, from, evaluated]
}

pred weakNormalize[input : Term] {
    // there exists a term
    some normal : Term | {
        // that our input term can reduce to (or is itself)
        {
            evaluatesTo[input, normal]

            no normal.evaluated
        } implies
        // such that there is no other term
        (no t2 : Term | {
            t2 != normal

            // which is smaller
            t2.size < normal.size or some t2.evaluated
            // and the input term can evalaute to
            evaluatesTo[input, t2]
        })

    }
}

pred wellFormed {
    -- no cycles

    -- single root term
    // some t: Term | all subterm: Term | subterm in allSubterms[t] or t = subterm

    one root : Term | {
        // No cycles in the root
        root not in allSubterms[root]

        all t : Term | some other : Term | (
            t = root
            or t in allSubterms[other]
            or (t in other.evaluated and t != other)
        )
    }

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

pred LambdaCalculus {
    wellFormed
    combinator
    reductions
    substitutions
}

test expect {
    emptyIsSat: {} is sat
    noFreeInCombinator: {
        wellFormed
        combinator
    } for 8 Term for {} is sat

    termSizeIsSat: {
        wellFormed
        combinator
        termSize
    } for 8 Term is sat
}

run {
    LambdaCalculus
    #evaluated > 3
} for exactly 8 Term

weaklyNormalizing: run {
    wellFormed
    combinator
    reductions
    substitutions
    termSize
    not (all t: Term | weakNormalize[t])
} for exactly 21 Term

expect{
    substitutionsAreSat: {
        wellFormed
        combinator
        substitutions
    } for 8 Term is sat

    reductionsAreSat: {
        wellFormed
        combinator
        reductions
        substitutions
        termSize
    } for 8 Term is sat
}

test expect {
    weaklyNormalizing: {
        {
            wellFormed
            combinator
            reductions
            substitutions
            termSize } 
        implies
            (all t : Term | weakNormalize[t])
    } for 8 Term is theorem
}

// run {
//     wellFormed
//     combinator
//     reductions
//     substitutions
// } for exactly 8 Term

// BigCombinator: run {
//     wellFormed
//     combinator
//     some t: Term | { #(allSubterms[t] & Var) > 2 }
// } for 8 Term

