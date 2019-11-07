# LoVe Lecture 4: Functional Programming

## Inductive Types

Recall the definition of type `nat` (= `ℕ`):

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

Mottos:

* **No junk**: The type contains no values beyond those expressible using the constructors

* **No confusion**: Values built in a different ways are different

For `nat` (= `ℕ`):

* "No junk" means that there exist no special values like, say, –1 or ε, that cannot be expressed using a finite combination of `zero` and `succ`

* "No confusion" is what ensures that `zero` ≠ `succ x`

In addition, inductive types are always finite; `succ (succ (succ …))` is not a value, because there exists no `x` such that `x = succ x`


## Example: Lists

An inductive polymorphic type constructed from `nil` and `cons`:

    inductive list (α : Type) : Type
    | nil {} : list
    | cons   : α → list → list

Aliases:

> `[]` = `nil`

> _x_ `::` _xs_ = `cons` _x_ _xs_

> `[` _x1_, … _xN_ `]` = `cons` _x1_ … (`cons` _xN_ `nil`)…)

Primitive recursion:

    def f : list α → …
    | []        := …
    | (x :: xs) := … x … xs … (f xs) …

Structural induction:

    lemma l :
      ∀x : list α, …
    | []        := …
    | (x :: xs) := … x … xs … (l xs) …

Pattern matching:

    match xs with
    | []      := …
    | x :: xs := …
    end


## General Pattern Maching within Terms

> `match` _term1_`,` …`,` _termM_ `with`
>
> `|` _pattern11_`,` …`,` _pattern1M_ `:=` _result1_
>
> ⋮
>
> `|` _patternN1_`,` …`,` _patternNM_ `:=` _resultN_
>
> `end`

`match` allows nonrecursive pattern matching in terms

Example:

    match n, xs with
    | 0,     _       := …
    | n + 1, []      := …
    | n + 1, x :: xs := …
    end

In contrast to pattern matching after `lemma` or `def`, the patterns are separated by commas (`,`), so parentheses are optional


## Example: Trees

Inductive types with constructors taking several recursive arguments define tree-like objects

_Binary trees_ have nodes with at most two children

Example:

    inductive btree (α : Type) : Type
    | empty {} : btree
    | node     : α → btree → btree → btree

The type `aexp` of arithmetic expressions was also an example of a tree data structure

The nodes of a tree, whether inner nodes or leaf nodes, often carry labels or other annotations

Inductive trees contain **no infinite branches**, not even cycles

This is less expressive than pointer- or reference-based data structures (in imperative languages) but easier to reason about

Recursive definitions (and proofs by induction) work roughly as for lists, but we may need to recurse (or invoke the induction hypothesis) on several child nodes


## New Tactics

### `by_cases`

> `by_cases` _proposition_

Performs a case analysis on a proposition

It is useful to reason about the condition in an `if` condition

### `cases`

> `cases` _variable_

Performs a case distinction on the specified variable, giving rise to as many subgoals as there are constructors in the definition of the variable's type.

Unlike `induction`, it does not produce induction hypotheses


## Demo

[`love04_functional_programming_demo.lean`](../lean/love04_functional_programming_demo.lean)
