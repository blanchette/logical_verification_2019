# LoVe Lecture 8: Operational Semantics

In this and the next two lectures, we will see how to use Lean to specify the syntax and semantics of programming languages and to reason about the semantics


## Motivation

A formal semantics helps specify and reason about the programming language itself, and about individual programs

It can form the basis of verified compilers, interpreters, verifiers, static analyses, type systems, etc.

Without formal proofs, semantics, compilers, interpreters, verifiers, static analyses, type systems, etc., are **almost always wrong**

In this area, proof assistants are widely used—e.g. every year, about 10-20% of POPL papers are partially or totally formalized:

* Little machinery (background libraries, tactics) is needed to get started, beyond inductive types and predicates and recursive functions

* The proofs tend to have lots of cases, which is a good match for computers

* Proof assistants keep track of what needs to be changed when as extend the programming language with more features


## The WHILE Language

_WHILE_ is a minimalistic imperative language with the following grammar:

    S  ::=  skip                 -- no-op
         |  x := a               -- assignment
         |  S ; S                -- sequential composition
         |  if b then S else S   -- conditional statement
         |  while b do S         -- while loop

where `S` stands for a _statement_ (also called _command_ or _program_), `x` for a variable, `a` for an arithmetic expression, and `b` for a Boolean expression

Backronym: **W**eak **H**ypothetical **I**mperative **L**anguage **E**xample


## Deep vs. Shallow Embeddings

In our informal presentation, we deliberately leave the syntax of arithmetic and Boolean expressions unspecified

In Lean, we have the choice:

* We could use a type such as `aexp` from lecture 1.2 and similarly for Boolean expressions

* Supposing a state `s` is a function from variable names to values (`string → ℕ`), we could decide that an arithmetic expression is simply a function from states to natural numbers (`state → ℕ`) and a Boolean expression is a predicate (`state → Prop` or `state → bool`)

This corresponds to the difference between deep and shallow embeddings:

* A **deep embedding** of some syntax (expression, formula, program, etc.) consists of an abstract syntax tree specified in the proof assistant (e.g. `aexp`) with a semantics

* In contrast, a **shallow embedding** simply reuses the corresponding mechanisms from the logic (e.g. λ-terms, functions and predictate types)

A deep embedding allows us to reason explictly about the syntax (and the semantics)

A shallow embedding is more lightweight, because we can use it directly, without having to define a semantics

We will use a deep embedding of programs (which we find interesting), and shallow embeddings of assignments and Boolean expressions (which we find boring)

Examples:

    λs : state, s "x" + s "y" + 1   -- x + y + 1
    λs : state, s "a" ≠ s "b"       -- a ≠ b


## Big-Step Semantics

An _operational semantics_ correponds to an idealized, abstract interpreter (specified in a Prolog-like language)

Two main variants:

* big-step semantics

* small-step semantics

In a _big-step semantics_ (also called _natural semantics_), judgments have the form `(S, s) ⟹ s'`:

> Starting in a state `s`, executing `S` terminates in the state `s'`

Example:

    (x := x + y; y := 0,  [x ↦ 3, y ↦ 5])  ⟹  [x ↦ 8, y ↦ 0]

Derivation rules:

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Asn
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ s'   (S', s') ⟹ s''
    ——————————————————————————————— Seq
    (S ; S', s) ⟹ s''

    (S, s) ⟹ s'
    ——————————————————————————————— If-True   if s(b) = true
    (if b then S else S', s) ⟹ s'

    (S', s) ⟹ s'
    ——————————————————————————————— If-False   if s(b) = false
    (if b then S else S', s) ⟹ s'

    (S, s) ⟹ s'   (while b do S, s') ⟹ s''
    —————————————————————————————————————————— While-True   if s(b) = true
    (while b do S, s) ⟹ s''

    ————————————————————————— While-False   if s(b) = false
    (while b do S, s) ⟹ s

Above, `s(e)` denotes the value of expression `e` in state `s`

In Lean, the judgment corresponds to an inductive predicate, and the derivation rules correspond to the predicate's introduction rules

Using an inductive predicate as opposed to a recursive function allows us to cope with nontermination (e.g., a diverging `while`) and nondeterminism (e.g., in the exercise)


## Advantages and Disadvantages of Big-Step Semantics

Equipped with a big-step semantics, we can

* prove properties of the programming language, such as **equivalence proofs** between programs and **determinism**

* reason about **concrete programs**, proving theorems relating final states `s'` with initial states `s`

On the other hand, a big-step semantics

* does not let us reason about intermediate states

* does not let us express nontermination or interleaving (for multithreading)


## Small-Step Semantics

_Small-step semantics_ (also called _structural operational semantics_, _SOS_) solve the above issues

A judgment has the form `(S, s) ⇒ (S', s')`:

> Starting in a state `s`, executing one step of `S` leaves us in the state `s'`, with the program `S'` remaining to be executed

An execution is a finite or infinite chain `(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`

A pair `(S, s)` is called a _configuration_; it is _final_ if no transition of the form `(S, s) ⇒ _` is possible

Example:

       ([x ↦ 3, y ↦ 5],  x := x + y; y := 0)
    ⇒  ([x ↦ 8, y ↦ 5],  y := 0)
    ⇒  ([x ↦ 8, y ↦ 0],  skip)

Derivation rules:

    ————————————————————————————————— Asn
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ————————————————————————— Seq-Step
    (S ; T, s) ⇒ (S' ; T, s')

    —————————————————————— Seq-Skip
    (skip ; S, s) ⇒ (S, s)

    ————————————————————————————————— If-True   if s(b) = true
    (if b then S else S', s) ⇒ (S, s)

    —————————————————————————————————— If-False   if s(b) = false
    (if b then S else S', s) ⇒ (S', s)

    ————————————————————————————————————————————————————————————————— While
    (while b do S, s) ⟹ (if b then (S ; while b do S) else skip, s)

There is no rule for `skip` (why?)


## Advantages and Disadvantages of Small-Step Semantics

Equipped with a small-step semantics, we can _define_ a big-step semantics:

> `(S, s) ⟹ s'` if and only if `(S, s) ⇒* (skip, s')`

where `r*` denotes the reflexive transitive closure of a relation `r`

Alternatively, if we have already defined a big-step semantics, we can _prove_ the above equivalence theorem to _validate_ our definitions

We can prove that a configuration `(S, s)` is final if and only if `S = skip`; this ensures that we have not forgotten a derivation rule

The main disadvantage of small-step semantics is that we now have two relations, `⇒` and `⇒*`, and the derivation rules and proofs tend to be more complicated


## Demo

[`love08_operational_semantics_demo.lean`](../lean/love08_operational_semantics_demo.lean)
