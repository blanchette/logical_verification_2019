/- LoVe Exercise 10: Denotational Semantics -/

import .love10_denotational_semantics_demo

namespace LoVe


/- Question 1: Monotonicity -/

/- Prove the following two lemmas from the lecture. -/

lemma monotone_comp {α β : Type} [partial_order α] (f g : α → set (β × β))
    (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
sorry

lemma monotone_restrict {α β : Type} [partial_order α] (f : α → set (β × β))
    (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
sorry


/- Question 2: Kleene's Theorem -/

/- We can compute the fixpoint by iteration by taking the union of all finite
iterations of `f`:

    lfp f = ⋃n, f^^[n] ∅

where

    f^^[n] = f ∘ ⋯ ∘ f ∘ id

iterates the function `f` `n` times. However, the above characterization of
`lfp` only holds for continuous functions, a concept we will introduce below. -/

def iterate {α : Type} (f : α → α) : ℕ → α → α
| 0       a := a
| (n + 1) a := f (iterate n a)

notation f`^^[`n`]` := iterate f n

/- 2.1. Fill in the missing proofs below. -/

def Union {α : Type} (s : ℕ → set α) : set α :=
{a | ∃n, a ∈ s n}

lemma Union_le {α : Type} {s : ℕ → set α} (a : set α) (h : ∀i, s i ≤ a) :
  Union s ≤ a :=
sorry

/- A continuous function `f` is a function that commutes with the union of any
monotone sequence `s`: -/

def continuous {α : Type} (f : set α → set α) : Prop :=
∀s : ℕ → set α, monotone s → f (Union s) = Union (λn, f (s n))

/- We need to prove that each continuous function is monotone. To achieve this,
we will need the following sequence: -/

def bi_seq {α : Type} (a₁ a₂ : set α) : ℕ → set α
| 0       := a₁
| (n + 1) := a₂

/- For example, `bi_seq 0 1` is the sequence 0, 1, 1, 1, etc. -/

lemma monotone_bi_seq {α : Type} (a₁ a₂ : set α) (h : a₁ ≤ a₂) :
  monotone (bi_seq a₁ a₂)
| 0       0       _ := le_refl _
| 0       (n + 1) _ := h
| (n + 1) (m + 1) _ := le_refl _

lemma Union_bi_seq {α : Type} (a₁ a₂ : set α) (ha : a₁ ≤ a₂) :
  Union (bi_seq a₁ a₂) = a₂ :=
sorry

lemma monotone_of_continuous {α : Type} (f : set α → set α)
    (hf : continuous f) :
  monotone f :=
sorry

/- 2.2. Provide the following proof, using a similar case distinction as for
`monotone_bi_seq` above. -/

lemma monotone_iterate {α : Type} (f : set α → set α) (hf : monotone f) :
  monotone (λn, f^^[n] ∅)
:= sorry

/- 2.3. Prove the main theorem. A proof sketch is given below.

We break the proof into two proofs of inclusion.

Case 1. lfp f ≤ Union (λn, f^[n] ∅): The key is to use the lemma `lfp_le`
together with continuity of `f`.

Case 2. Union (λn, f^[n] ∅) ≤ lfp f: The lemma `Union_le` gives us a natural
number `i`, on which you can perform induction. You will also need the lemma
`lfp_eq` to unfold one iteration of `lfp f`. -/

lemma lfp_Kleene {α : Type} (f : set α → set α) (hf : continuous f) :
  complete_lattice.lfp f = Union (λn, f^^[n] ∅) :=
sorry


/- Question 3 (**optional**): Regular Expressions -/

inductive regex (α : Type) : Type
| empty     {} : regex
| nothing   {} : regex
| atom (a : α) : regex
| concat       : regex → regex → regex
| alt          : regex → regex → regex
| star         : regex → regex

/- 3.1 (**optional**). Define a translation of regular expressions to relations.
The idea is that an atom corresponds to a relation, concatenation corresponds to
composition of relations, and alternation is union. -/

def rel_of_regex {α : Type} : regex (set (α × α)) → set (α × α)
| regex.empty          := Id α
| _                    := sorry

/- 3.2 (**optional**). Prove the following recursive equation about your
definition. -/

lemma rel_of_regex_star {α : Type} (r : regex (set (α × α))) :
  rel_of_regex (regex.star r) =
  rel_of_regex (regex.alt (regex.concat r (regex.star r)) regex.empty) :=
sorry

end LoVe
