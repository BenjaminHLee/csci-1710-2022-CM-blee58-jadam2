# Curiosity Modeling: Lambda Calculus
Anon IDs:
white_whale_floating@gmail.com
srl35btbyptizwmm@gmail.com	


## Model Introduction

We sought out to explore lambda calculus and its properties. `lambda.frg` contains a model of the untyped lambda calculus, including term definition, combinator generation, evaluation, and reduction. Our model generates lambda terms and valid reductions.

## Lambda Terms

The model is built upon `Term`s, which are intended to represent lambda terms. In accordance with [the untyped lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus), we define three types of `Term`s:

| Sig   |        Name | λ syntax | Description 
|-------|-------------|----------|-------------
| `Var` | Variable    | *x*      | A variable representing a value 
| `Abs` | Abstraction | *λx.M*   | Function definition, with argument *x* : Var and body *M* : Term 
| `App` | Application | (M N)    | Function application, with N : Term applied to M : Term 

The `wellFormed` predicate asserts that `Term`s have a tree shape (and as such that there is only one `Term`). While the `combinator` predicate asserts that the `Term` is a combinator (i.e. the lambda expression contains no free variables). With these two predicates, Forge will generate well-formed `Term`s that represent real well-formed lambda terms.

The model also includes a notion of term `size`, which simply corresponds to the number of subterms in any given `Term`.

## Substitution, Evaluation, and Reduction

While generating and validating lambda terms is interesting in and of itself, we're also interested in exploring the substitution, application, and evaluation of such terms. The `Eval` sig and its `substituted` pfunc represent valid substitutions of subexpressions, which the `betaReduction` predicate uses to constrain reductions to those that constitute valid β-reductions (which are analogous to a single step of function application). The `evaluated` set of a `Term` corresponds to the `Term`s that can be reached via evaluation of the `Term` in question.
