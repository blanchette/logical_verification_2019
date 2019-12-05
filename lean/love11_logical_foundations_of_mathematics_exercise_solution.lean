/- LoVe Exercise 11: Logical Foundations of Mathematics -/

import .love11_logical_foundations_of_mathematics_demo

namespace LoVe

universe variable u

set_option pp.beta true


/- Question 1: Subtypes -/

namespace my_vector

/- Recall the definition of vectors from the lecture: -/

#check vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer function is
truncated. -/

def list_add : list ℤ → list ℤ → list ℤ
| []        []        := []
| (x :: xs) (y :: ys) := (x + y) :: list_add xs ys
| []        (y :: ys) := []
| (x :: xs) []        := []

/- 1.1. Show that if the lists have the same length, the resulting list also has
that length. -/

lemma length_list_add :
  ∀(xs : list ℤ) (ys : list ℤ) (h : list.length xs = list.length ys),
    list.length (list_add xs ys) = list.length xs
| []        []        :=
  by simp [list_add]
| (x :: xs) (y :: ys) :=
  begin
    simp [list_add, length],
    intro h,
    rw length_list_add xs ys h
  end
| []        (y :: ys) :=
  begin
    intro h,
    cases h
  end
| (x :: xs) []        :=
  begin
    intro h,
    cases h
  end

/- 1.2. Define componentwise addition on vectors using `list_add` and
`length_list_add`. -/

def add {n : ℕ} : vector ℤ n → vector ℤ n → vector ℤ n :=
λx y, subtype.mk (list_add (subtype.val x) (subtype.val y))
  begin
    rw length_list_add,
    { exact subtype.property x },
    { rw [subtype.property x, subtype.property y] }
  end

/- 1.3. Show that `list_add` and `add` are commutative. -/

lemma list_add_comm :
  ∀(xs : list ℤ) (ys : list ℤ), list_add xs ys = list_add ys xs
| []        []        := by refl
| (x :: xs) (y :: ys) := by simp [list_add]; rw list_add_comm
| []        (y :: ys) := by refl
| (x :: xs) []        := by refl

lemma add_comm {n : ℕ} (x y : vector ℤ n) :
  add x y = add y x :=
begin
  apply subtype.eq,
  simp [add],
  apply list_add_comm
end

end my_vector


/- Question 2: Integers as Quotients -/

/- Recall the construction of integers from the lecture: -/

#check myℤ.rel
#check rel_iff
#check myℤ

/- 2.1. Define negation using `quotient.lift`. -/

def neg : myℤ → myℤ :=
quotient.lift (λpn, ⟦(prod.snd pn, prod.fst pn)⟧)
  begin
    intros a b h,
    cases a,
    cases b,
    apply quotient.sound,
    simp [rel_iff] at h ⊢,
    linarith
  end

/- 2.2. Prove the following lemmas. -/

lemma neg_mk (p n : ℕ) :
  neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
by refl

lemma myℤ.neg_neg (a : myℤ) :
  neg (neg a) = a :=
begin
  apply quotient.induction_on a,
  intro a,
  cases a,
  simp [neg_mk]
end


/- Question 3: Nonempty Types -/

/- In the lecture, we saw the inductive predicate `nonempty` that states that a
type has at least one element: -/

#print nonempty

/- 3.1. The purpose of this exercise is to think about what would happen if all
types had at least one element. To investigate this, we introduce this fact as
an axiom as follows. Introducing axioms should be generally avoided or done
with great care, since they can easily lead to contradictions, as we will
see. -/

axiom sort_nonempty (α : Sort u) :
  nonempty α

/- This axiom gives us a fact `sort_nonempty` without having to prove it. It
resembles a lemma proved by sorry, just without the warning. -/

#check sort_nonempty

/- Prove that this axiom leads to a contradiction, i.e., lets us derive
`false`. -/

lemma proof_of_false :
  false :=
by exact classical.choice (sort_nonempty false)

-- alternative proof:
lemma proof_of_false' :
  false :=
begin
  cases sort_nonempty false with h,
  exact h
end

/- 3.2 (**optional**). Prove that even the following weaker axiom leads to a
contradiction. Of course, you may not use the axiom or the lemma from 3.1.

Hint: Subtypes can help. -/

axiom all_nonempty_Type (α : Type u) :
  nonempty α

lemma proof_of_false₂ : false :=
begin
  let t : Type := {a : ℕ // false},
  have h : nonempty t := sort_nonempty t,
  let x : t := classical.choice h,
  exact subtype.property x
end

-- alternative proof:
lemma proof_of_false₂' : false :=
begin
  let t : Type := {a : ℕ // false},
  cases all_nonempty_Type t with x,
  exact subtype.property x
end


/- Question 4 (**optional**): Hilbert Choice -/

/- The following command enables noncomputable decidability on every `Prop`. The
`priority 0` attribute ensures this is used only when necessary; otherwise, it
would make some computable definitions noncomputable for Lean. -/

local attribute [instance, priority 0] classical.prop_decidable

/- 4.1 (**optional**). Prove the following lemma. -/

lemma exists_minimal_arg.aux (f : ℕ → ℕ) :
  ∀x n, f n = x → ∃n, ∀i, f n ≤ f i
| x n eq :=
  begin
    -- this works thanks to `classical.prop_decidable`
    by_cases (∃n', f n' < x),
    { cases h with n' h,
      exact exists_minimal_arg.aux _ n' rfl },
    { have h' : ∀n', x ≤ f n',
      { intro n',
        apply le_of_not_gt _,
        intro h',
        apply h,
        use n',
        exact h' },
      apply exists.intro n,
      rw eq,
      exact h' }
  end

/- Now this interesting lemma falls off: -/

lemma exists_minimal_arg (f : ℕ → ℕ) :
  ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
exists_minimal_arg.aux f _ 0 rfl

/- 4.2 (**optional**). Use what you learned in the lecture notes to define the
following function, which returns the (or an) index of the minimal element in
`f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
classical.some (exists_minimal_arg f)

/- 4.3 (**optional**). Prove the following characteristic lemma about your
definition. -/

lemma minimal_arg_spec (f : ℕ → ℕ) :
  ∀i : ℕ, f (minimal_arg f) ≤ f i :=
classical.some_spec (exists_minimal_arg f)

end LoVe
