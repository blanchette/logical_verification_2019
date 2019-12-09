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

def bind {α β : Type} : nondet α → (α → nondet β) → nondet β
| (pure x)   f := f x
| fail       f := fail
| (choice k) f := choice (λb, bind (k b) f)

instance : has_pure nondet := { pure := @pure }
instance : has_bind nondet := { bind := @bind }

def starts_with : list ℕ → list ℕ → bool
| (x :: xs) []        := ff
| []        ys        := tt
| (x :: xs) (y :: ys) := (x = y) && starts_with xs ys

/- 1.2 (**optional**). Translate the `portmanteau` program from the `list` monad
to the `nondet` monad. -/

def nondet_portmanteau : list ℕ → list ℕ → nondet (list ℕ)
| []        ys := fail
| (x :: xs) ys :=
  choice (λb, if b then (if starts_with (x :: xs) ys then pure ys else fail)
    else nondet_portmanteau xs ys >>= λzs, pure (list.cons x zs))
    -- this line could also be `else (list.cons x <$> nondet_portmanteau xs ys)`


/- Question 2: Nondeterminism, Denotationally -/

def list_sem {α : Type} : nondet α → list α
| (pure x)   := [x]
| fail       := []
| (choice k) := list_sem (k ff) ++ list_sem (k tt)


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
begin
  apply iff.intro,
  { intro h,
    cases h,
    { use ff,
      assumption },
    { use tt,
      assumption } },
  { intro h,
    cases h,
    cases h_w,
    { apply big_step.choice_l,
      assumption },
    { apply big_step.choice_r,
      assumption } }
end

/- 3.2 (**optional**). Prove the compatibility between denotational and
operational semantics. -/

theorem den_op_compat {α : Type} :
  ∀(x : α) (mx : nondet α), x ∈ list_sem mx ↔ mx ⟹ x
| x (pure x')  :=
  begin
    apply iff.intro,
    { intro h,
      cases h;
        cases h,
      exact big_step.pure },
    { intro h,
      cases h,
      apply iff.elim_right list.mem_singleton,
      refl }
  end
| x fail       :=
  begin
    apply iff.intro;
      intro h;
      cases h
  end
| x (choice k) :=
  begin
    apply iff.intro,
    { intro h,
      cases iff.elim_left list.mem_append h,
      { apply big_step.choice_l,
        apply iff.elim_left (den_op_compat x (k ff)),
        assumption },
      { apply big_step.choice_r,
        apply iff.elim_left (den_op_compat x (k tt)),
        assumption } },
    { intro h,
      cases h;
        apply iff.elim_right list.mem_append,
      { apply or.intro_left,
        apply iff.elim_right (den_op_compat x (k ff)),
        assumption },
      { apply or.intro_right,
        apply iff.elim_right (den_op_compat x (k tt)),
        assumption } }
  end

end nondet

end LoVe
