# LoVe Lecture 7: Metaprogramming

Users can extend Lean with custom monadic tactics and tools

This kind of programming—programming the prover—is called metaprogramming


## Overview

Lean’s metaprogramming framework uses mostly the same notions and syntax as Lean’s input language itself

Abstract syntax trees _reflect_ internal data structures, e.g. for expressions (terms)

The prover's C++ internals are exposed through Lean interfaces, which we can use for accessing the current context and goal, unifying expressions, querying and modifying the environment, and setting attributes (e.g., `@[simp]`)

Most of Lean's predefined tactics are implemented in Lean (and not in C++)

Example applications:

* **proof goal transformations** (e.g., apply all safe introduction rules for connectives, put the goal in negation normal form)

* **heuristic proof search** (e.g., apply unsafe introduction rules for connectives and hypotheses with backtracking)

* **decision procedures** (e.g., for propositional logic, linear arithmetic)

* **definition generators** (e.g., Haskell-style `derive` for inductive types)

* **advisor tools** (e.g., lemma finders, counterexample generators)

* **exporters** (e.g., documentation generators)

* **ad hoc automation** (to avoid boilerplate or duplication)

Advantages of Lean's metaprogramming framework:

* Users (e.g. mathematicians) do not need to learn another programming language to write metaprograms; they can work with the same constructs and notation used to define ordinary objects in the prover's library

* Everything in that library is available for metaprogramming purposes (e.g. `ℤ`, `list`, algebraic structures)

* Metaprograms can be written and debugged in the same interactive environment, encouraging a style where formal libraries and supporting automation are developed at the same time

## Metaprograms and Metaconstants

Any executable Lean definition can be used as a metaprogram

In addition, we can put `meta` in front of a definition to indicate that is a _metadefinition_; these need not terminate but cannot be used in non-`meta` contexts

Metaprograms (whether defined with `meta` or not) can communicate with Lean through _metaconstants_, which are implemented in C++ and have no logical meaning (i.e., they are opaque names)

Important types:

* `tactic`: the tactic monad, which contains the proof state, the environment, etc.

* `name`: hierarchical names

* `expr`: terms, types, proofs are represented as abstract syntax trees


## The Tactic Monad

Tactics have access to

* the list of **goals** as metavariables (each metavariables has a type and a local context (hypothesis); they can optionally be instantiated)

* the **elaborator** (to elaborate expressions and compute their type)

* the **attributes** (e.g., the list of `simp` rules)

* the **environment**, containing all declarations and inductive types

Tactics can also produce trace messages

The tactic monad is an `alternative`, with `fail` and `<|>` (exercise 6)


## Expressions and Names

The reflected expression type:

    meta inductive expr
    | var      {} : nat → expr
    | sort     {} : level → expr
    | const    {} : name → list level → expr
    | mvar        : name → name → expr → expr
    | local_const : name → name → binder_info → expr → expr
    | app         : expr → expr → expr
    | lam         : name → binder_info → expr → expr → expr
    | pi          : name → binder_info → expr → expr → expr
    | elet        : name → expr → expr → expr → expr
    | macro       : macro_def → list expr → expr

We can create literal expressions conveniently using backticks (`):

* Expressions with a single backtick, `(e), must be fully elaborated

* Expressions with two backticks, ``(e), are pre-expressions: They may contain some holes to be filled in later, based on some context

* Expressions with three backticks, ```(e), are pre-expressions without name checking

For names:

* Names with a single backtick, `n, are not checked for existence

* Names with two backticks, ``n, are checked


## Demo

[`love07_metaprogramming_demo.lean`](../lean/love07_metaprogramming_demo.lean)
