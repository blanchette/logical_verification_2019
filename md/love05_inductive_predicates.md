# LoVe Lecture 5: Inductive Predicates

We introduce inductive predicates, which correspond to proof trees

Inductive predicates are reminiscent of the Horn clauses of Prolog, but Lean offers a much stronger logic

A possible view of Lean:

> Lean = typed functional programming + logic programming + more logic


## Introductory Examples

_Inductive predicates_, or (more precisely) _inductively defined propositions_, are familiar from mathematics—e.g.

> The set `E` of even natural numbers is defined as the smallest set closed under the following rules:
> * `0 ∈ E`
> * for every `n ∈ ℕ`, if `n ∈ E`, then `n + 2 ∈ E`

In Lean, we write

    inductive even : ℕ → Prop
    | zero    : even 0
    | add_two : ∀n : ℕ, even n → even (n + 2)

If this looks familiar, it is because it should

The command introduces a new unary predicate `even` (or, equivalently, a `ℕ`-indexed family of propositions)

By Curry–Howard, what we have effectively done is introduce a new unary type constructor, `even`

`even` is equipped with two constructors, `zero` and `add_two`, which can be used to build proof terms

`even` can be seen as a tree type, the trees being the corresponding proof terms (or proof trees)

Thanks to the **no junk** guarantee of inductive definitions, `zero` and `add_two` are the only two ways to construct `even`


## Logical Symbols

The truth values `false` and `true`, the connectives `∧` and `∨`, the `∃` quantifier, and the equality predicate `=` are all defined as inductive propositions or predicates:

    inductive false : Prop

    inductive true : Prop
    | intro : true

    inductive and (a b : Prop) : Prop
    | intro : a → b → and

    inductive or (a b : Prop) : Prop
    | intro_left : a → or
    | intro_right : b → or

    inductive Exists {α : Type} (p : α → Prop) : Prop
    | intro : ∀a : α, p a → Exists

    inductive eq {α : Type} : α → α → Prop
    | refl (a : α) : eq a a

The notations `∃x : α, p` and `x = y` are syntactic sugar for `Exists (λx : α, p)` and `eq x y`, respectively

In contrast, `∀` (= `Π`) and `→` are built directly into the logic


## Introduction and Elimination Rules

We saw in lecture 2 that the logical connectives and the `∃` quantifier are equipped with introduction and elimination rules

The same is true for arbitrary inductive predicates `p`

`p`’s constructors are introduction rules; they typically have the form `∀…, … → p …` and can be used to prove goals of the form `p …`

Elimination works the other way around: It extracts information from a lemma or
hypothesis of the form `p …`

Elimination takes various forms: pattern matching (at the top-level of a definition or lemma, or with `match`), the `cases` and `induction` tactics, or custom elimination rules (e.g., `and.elim_left`)

## Rule Induction

Just as we can perform induction on a term, we can perform induction on a proof term

This is sometimes called _rule induction_, because the induction is on the introduction rules (i.e., the constructors of the proof term)

Thanks to Curry–Howard, this works as expected


## Rule Inversion

Often it is convenient to rewrite concrete terms of the form `p (c …)`, where `c` is typically a constructor

We can state and prove an _inversion rule_ to support such eliminative reasoning

Format:

    ∀x y, p (c x y) → (∃…, … ∧ …) ∨ … ∨ (∃…, … ∧ …)

It can be useful to combine introduction and elimination into one lemma, which can be used for rewriting both hypotheses and goals:

    ∀x y, p (c x y) ↔ (∃…, … ∧ …) ∨ … ∨ (∃…, … ∧ …)

Example:

    ∀n : ℕ, even n ↔ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ even m


## Induction Pitfalls

Inductive predicates often have parameters that evolve through the induction

Pattern matching and `cases` handles this gracefully, but some care is necessary with `induction`

Please read Section 5.8 ("Induction Pitfalls") of the lecture notes for details


## Demo

[`love05_inductive_predicates_demo.lean`](../lean/love05_inductive_predicates_demo.lean)
