# Formalization Projects

*Instead* of homeworks 9 and 10, you can do a verification project, worth 20 points

If you choose to do so, please send me ([j.c.blanchette@vu.nl](mailto:j.c.blanchette@vu.nl)) an email by the end of the week

For a fully successful project, we expect about 200 (or more) lines of Lean

Some ideas for projects

Computer science:

  * extended WHILE language with static arrays or other features

  * functional data structures (balanced trees, etc.)

  * functional algorithms (bubble sort, merge sort, [Tarjan's algorithm](https://arxiv.org/pdf/1810.11979.pdf), etc.)

  * compiler from expressions or imperative programs to e.g. stack machine

  * type systems (e.g. Benjamin Pierce's _Types and Programming Languages_)

  * security properties (e.g. Volpano–Smith-style noninterference analysis)

  * theory of first-order terms, including matching, term rewriting

  * automata theory

  * normalization of context-free grammars or regular expressions

  * process algebras and bisimilarity

  * soundness and possibly completeness of proof systems (e.g. Genzen's sequent calculus, natural deduction, tableaux)

  * separation logic

Mathematics:

  * graphs

  * combinatorics

  * number theory


# LoVe Lecture 9: Hoare Logic

We review a second way to specify the semantics of a programming language: Hoare logic

If operational semantics corresponds to an abstract interpreter, _Hoare logic_ (also called _axiomatic semantics_) corresponds to a verifier

Hoare logic is particularly convenient to reason about programs


## Hoare Triples

The basic judgments of Hoare logic are often called _Hoare triples_; they have the form

    {P} S {Q}

where `S` is a statement, and `P` and `Q` are logical formulas over the state variables

Intended meaning:

> If the _precondition_ `P` holds before `S` is executed and the execution terminates normally, the _postcondition_ `Q` holds at termination

This is a _partial correctness_ statement: The program is correct _if_ it terminates normally (i.e. no run-time error, no infinite loop or divergence)


## Introductory Examples

All of these Hoare triples are valid (with respect to the intended meaning):

* `{true} b := 4 {b = 4}`

* `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`

* `{b ≥ 0} b := b + 1 {b ≥ 1}`

* `{false} skip {b = 100}`

* `{true} while i ≠ 100 do i := i + 1 {i = 100}`


## Inference Rules

The following is a **complete** set of rules for reasoning about WHILE programs:

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Asn
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S ; S' {Q}

    {P ∧ b} S {Q}   {P ∧ ¬b} S' {Q}
    ——————————————————————————————— If
    {P} if b then S else S' {Q}

    {I ∧ b} S {I}
    ————————————————————————— While
    {I} while b do S {I ∧ ¬b}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` denotes `Q` with `x` replaced by `a`; here is another way to look at the `Asn` rule:

    ———————————————————— Asn
    {Q[a]} x := e {Q[x]}

where `[x]` factors out all occurrences of `x` in `Q`

In the `While` rule, `I` is called an _invariant_

Except for `Conseq`, the rules are syntax-driven


## Example Derivations

    —————————————————————— Asn   —————————————————————— Asn
    {a = 2} b := a {b = 2}       {b = 2} c := b {c = 2}
    ——————————————————————————————————————————————————— Seq
    {a = 2} b := a ; c := b {c = 2}


                     —————————————————————— Asn
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}


## Theoretical Properties

By giving a semantic characterization of a Hoare triple in terms of an operational semantics, we can prove soundness and completeness

* **Soundness**: If `{P} S {Q}` is derivable, `P s`, and `(S, s) ⟹ s'`, then `Q s'`

* **Completeness**: If `P s` and `(S, s) ⟹ s'` implies `Q s'` for all `s`, `s'`, then `{P} S {Q}` is derivable

Completeness means that any WHILE program that is partially correct semantically can be proved correct using the above rules


## Alternative, Semantic Definition of Hoare Triples

We can define Hoare triples _semantically_ in Lean; this is what we will do

We will also use predicates on states (`state → Prop`) to represent pre- and postconditions

The `Conseq` rule relies on an oracle to prove implications; if we use a proof assistant, Gödel's incompleteness theorem will (theoretically) limit which implications we can prove

Various _derived rules_ can be proved to be correct in terms of the standard rules (or directly in terms of the semantics)

For example, we can derive _linear_ rules for `skip`, `:=`, and `while`:

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Asn'
    {P} x := a {Q}

    {P ∧ b} S {P}   P ∧ ¬b → Q
    —————————————————————————— While'
    {P} while b do S {Q}


## Verification Condition Generators

_Verification condition generators_ (_VCGs_) are programs that apply Hoare logic rules automatically, producing _verification conditions_ (_VCs_) that must be proved by the user

The user must usually also provide strong enough loop invariants, as an annotation in their programs

We can use Lean's metaprogramming framework to define a simple VCG

Hundreds if not thousands of program verification tools are based on these principles; often these are based on an extension called [separation logic](https://en.wikipedia.org/wiki/Separation_logic)

VCGs typically work backwards from the postcondition, using backward rules (rules stated to have an arbitrary `Q` as their postcondition); this works well because `Asn` is backward


## Hoare Triples for Total Correctness

_Total correctness_ also asserts that the program terminates normally

_Hoare triples_ have the form

    [P] S [Q]

Intended meaning:

> If the _precondition_ `P` holds before `S` is executed, the execution terminates normally and the _postcondition_ `Q` holds in the final state

For deterministic programs, an equivalent formulation is as follows:

> If the _precondition_ `P` holds before `S` is executed, there exists a state in which execution terminates normally and the _postcondition_ `Q` holds in that state

Example:

* `[i ≤ 100] while i ≠ 100 do i := i + 1 [i = 100]`

In our WHILE language, this only affects while loops, which must now be annotated by a _variant_ `V` (a natural number that decreases with each iteration):

    [I ∧ b ∧ V = n] S [I ∧ V < n]
    ————————————————————————————— While
    [I] while b do S [I ∧ ¬b]

What is the variant in the last example?


## Demo

[`love09_hoare_logic_demo.lean`](../lean/love09_hoare_logic_demo.lean)
