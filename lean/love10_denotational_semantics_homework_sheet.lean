/- LoVe Homework 10: Denotational Semantics -/

import .love10_denotational_semantics_demo

namespace LoVe

/- Denotational semantics are well suited to functional programming. In this
exercise, we will study some representations of functional programs in Lean and
their denotational semantics. -/

/- The `nondet` type represents functional programs that can perform
nondeterministic computations: A program can choose between many different
computation paths / return values. Returning no results at all is represented by
`fail`, and nondeterministic choice between two alternatives (identified by the
`bool` values `tt` and `ff`) is represented by `choice`. -/

inductive nondet (α : Type) : Type
| pure    : α → nondet
| fail {} : nondet
| choice  : (bool → nondet) → nondet

namespace nondet


/- Question 1: The `nondet` Monad -/

/- The `nondet` inductive type forms a monad. The `pure` operator is
`nondet.pure`; `bind` is as follows: -/

def bind {α β : Type} : nondet α → (α → nondet β) → nondet β
| (pure x)   f := f x
| fail       f := fail
| (choice k) f := choice (λb, bind (k b) f)

instance : has_pure nondet := { pure := @pure }
instance : has_bind nondet := { bind := @bind }

/- 1.1. Prove the monadic laws (lecture 6) for `nondet`.

Hint: To prove `f = g` from `∀x, f x = g x`, use the theorem `funext`. -/

lemma pure_bind {α β : Type} (x : α) (f : α → nondet β) :
  pure x >>= f = f x :=
sorry

lemma bind_pure {α : Type} :
  ∀mx : nondet α, mx >>= pure = mx
:= sorry

lemma bind_assoc {α β γ : Type} :
  ∀(mx : nondet α) (f : α → nondet β) (g : β → nondet γ),
    ((mx >>= f) >>= g) = (mx >>= (λa, f a >>= g))
:= sorry

/- The function `portmanteau` computes a portmanteau of two lists: A portmanteau
of `xs` and `ys` has `xs` as a prefix and `ys` as a suffix, and they overlap. We
use `starts_with xs ys` to test that `ys` has `xs` as a prefix. -/

def starts_with : list ℕ → list ℕ → bool
| (x :: xs) []        := ff
| []        ys        := tt
| (x :: xs) (y :: ys) := (x = y) && starts_with xs ys

#eval starts_with [1, 2] [1, 2, 3]
#eval starts_with [1, 2, 3] [1, 2]

def portmanteau : list ℕ → list ℕ → list (list ℕ)
| []        ys := []
| (x :: xs) ys :=
  list.map (list.cons x) (portmanteau xs ys) ++
  (if starts_with (x :: xs) ys then [ys] else [])

/- Here are some examples of portmanteaux: -/

#reduce portmanteau [0, 1, 2, 3] [2, 3, 4]
#reduce portmanteau [0, 1] [2, 3, 4]
#reduce portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/- 1.2 (**optional**). Translate the `portmanteau` program from the `list` monad
to the `nondet` monad. -/

def nondet_portmanteau : list ℕ → list ℕ → nondet (list ℕ)
:= sorry


/- Question 2: Nondeterminism, Denotationally -/

/- 2.1. Give a denotational semantics for `nondet`, mapping it into a `list` of
all results. `pure` returns one result, `fail` returns zero, and `choice`
combines the results of either alternative. -/

def list_sem {α : Type} : nondet α → list α
:= sorry

/- Check that the following lines give the same output as for `portmanteau`: -/

#reduce list_sem (nondet_portmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce list_sem (nondet_portmanteau [0, 1] [2, 3, 4])
#reduce list_sem (nondet_portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/- 2.2. Often, we are not interested in getting all outcomes, just the first
successful one. Give a semantics for `nondet` that produces the first successful
result, if any. -/

def option_sem {α : Type} : nondet α → option α
:= sorry

/- 2.3. Prove the theorem `list_option_compat` below, showing that the two
semantics you defined are compatible. -/

lemma head'_orelse_eq_head'_append {α : Type} (xs ys : list α) :
  (list.head' xs <|> list.head' ys) = list.head' (xs ++ ys) :=
by induction xs; simp

theorem list_option_compat {α : Type} :
  ∀mx : nondet α, option_sem mx = list.head' (list_sem mx)
:= sorry


/- Question 3 (**optional**). Nondeterminism, Operationally -/

/- We can define the following big-step operational semantics for `nondet`: -/

inductive big_step {α : Type} : nondet α → α → Prop
| pure {x : α} :
  big_step (pure x) x
| choice_l {k : bool → nondet α} {x : α} :
  big_step (k ff) x → big_step (choice k) x
| choice_r {k : bool → nondet α} {x : α} :
  big_step (k tt) x → big_step (choice k) x
-- there is no case for `fail`

notation mx `⟹` x := big_step mx x

/- 3.1 (**optional**). Prove the following lemma.

The lemma states that `choice` has the semantics of "angelic nondeterminism": If
there is a computational path that leads to some `x`, the `choice` operator will
produce this `x`. -/

lemma choice_existential {α : Type} (x : α) (k : bool → nondet α) :
  nondet.choice k ⟹ x ↔ ∃b, k b ⟹ x :=
sorry

/- 3.2 (**optional**). Prove the compatibility between denotational and
operational semantics. -/

theorem den_op_compat {α : Type} :
  ∀(x : α) (mx : nondet α), x ∈ list_sem mx ↔ mx ⟹ x
:= sorry

end nondet

end LoVe
