/- LoVe Demo 13: Rational and Real Numbers -/

import .lovelib

namespace LoVe

set_option pp.beta true


/- Rational Numbers -/

structure fraction :=
(num           : ℤ)
(denom         : ℤ)
(denom_ne_zero : denom ≠ 0)

export fraction (num denom denom_ne_zero)

instance fraction.setoid : setoid fraction :=
{ r     := λa b, num a * denom b = num b * denom a,
  iseqv :=
    begin
      apply and.intro,
      { intros a, refl },
      apply and.intro,
      { intros a b h,
        cc },
      { intros a b c eq_ab eq_bc,
        apply eq_of_mul_eq_mul_right (denom_ne_zero b),
        cc }
    end }

lemma fraction.setoid_iff (a b : fraction) :
  a ≈ b ↔ num a * denom b = num b * denom a :=
by refl

def myℚ : Type :=
quotient fraction.setoid

def fraction.of_int (z : ℤ) : fraction :=
{ num           := z,
  denom         := 1,
  denom_ne_zero := by simp }

instance fraction.has_zero : has_zero fraction :=
{ zero := fraction.of_int 0 }

instance myℚ.has_zero : has_zero myℚ :=
{ zero := ⟦0⟧ }

instance fraction.has_one : has_one fraction :=
{ one := fraction.of_int 1 }

instance myℚ.has_one : has_one myℚ :=
{ one := ⟦1⟧ }

instance fraction.has_add : has_add fraction :=
{ add := λa b : fraction,
    { num           := num a * denom b + num b * denom a,
      denom         := denom a * denom b,
      denom_ne_zero :=
        begin
          apply mul_ne_zero,
          { exact (denom_ne_zero a) },
          { exact (denom_ne_zero b) }
        end } }

lemma fraction.add_num (a b : fraction) :
  num (a + b) = num a * denom b + num b * denom a :=
by refl

lemma fraction.add_denom (a b : fraction) :
  denom (a + b) = denom a * denom b :=
by refl

lemma fraction.add_equiv_add {a b c d : fraction} (hac : a ≈ c)
    (hbd : b ≈ d) :
  a + b ≈ c + d :=
begin
  simp [fraction.setoid_iff] at hac hbd,
  simp [fraction.setoid_iff],
  simp [fraction.add_num, fraction.add_denom],
  calc  (num a * denom b + num b * denom a)
          * (denom c * denom d)
      = num a * denom c * denom b * denom d
          + num b * denom d * denom a * denom c :
    by simp[add_mul]; ac_refl
  ... = num c * denom a * denom b * denom d
          + num d * denom b * denom a * denom c :
    by simp [hbd, hac]
  ... = (num c * denom d + num d * denom c)
          * (denom a * denom b) :
    by simp[add_mul]; ac_refl
end

instance myℚ.has_add : has_add myℚ :=
{ add := quotient.lift₂ (λa b, ⟦a + b⟧)
    begin
      intros a b c d hac hbd,
      apply quotient.sound,
      exact fraction.add_equiv_add hac hbd
    end }

instance fraction.has_neg : has_neg fraction :=
{ neg := λa,
  { num           := - num a,
    denom         := denom a,
    denom_ne_zero := denom_ne_zero a } }

lemma fraction.neg_num (a : fraction) :
  num (- a) = - num a :=
by refl

lemma fraction.neg_denom (a : fraction) :
  denom (- a) = denom a :=
by refl

lemma fraction.setoid_neg {a b : fraction} (hab : a ≈ b) :
  - a ≈ - b :=
begin
  simp [fraction.setoid_iff] at hab ⊢,
  simp [fraction.neg_num, fraction.neg_denom],
  exact hab
end

instance myℚ.has_neg : has_neg myℚ :=
{ neg := quotient.lift (λa, ⟦- a⟧)
    begin
      intros a b hab,
      apply quotient.sound,
      exact fraction.setoid_neg hab
    end }

instance fraction.has_mul : has_mul fraction :=
{ mul := λa b,
  { num           := num a * num b,
    denom         := denom a * denom b,
    denom_ne_zero :=
      mul_ne_zero (denom_ne_zero a)
        (denom_ne_zero b) } }

lemma fraction.mul_num (a b : fraction) :
  num (a * b) = num a * num b :=
by refl

lemma fraction.mul_denom (a b : fraction) :
  denom (a * b) =
  denom a * denom b :=
by refl

lemma fraction.setoid_mul {a b c d : fraction} (hac : a ≈ c)
    (hbd : b ≈ d) :
  a * b ≈ c * d :=
begin
  simp [fraction.setoid_iff] at hac hbd ⊢,
  simp [fraction.mul_num, fraction.mul_denom],
  cc
end

instance myℚ.has_mul : has_mul myℚ :=
{ mul := quotient.lift₂ (λa b, ⟦a * b⟧)
    begin
      intros a b c d hac hbd,
      apply quotient.sound,
      exact fraction.setoid_mul hac hbd
    end }

instance fraction.has_inv : has_inv fraction :=
{ inv :=
  λa, if ha : num a = 0 then 0 else
  { num           := denom a,
    denom         := num a,
    denom_ne_zero := ha } }

lemma fraction.inv_def (a : fraction) (ha : num a ≠ 0) :
  a⁻¹ = { num := denom a, denom := num a,
    denom_ne_zero := ha } :=
dif_neg ha

lemma fraction.inv_zero (a : fraction) (ha : num a = 0) :
  a⁻¹ = 0 :=
dif_pos ha

lemma fraction.inv_num (a : fraction) (ha : num a ≠ 0) :
  num (a⁻¹) = denom a :=
by rw [fraction.inv_def a ha]

lemma fraction.inv_denom (a : fraction) (ha : num a ≠ 0) :
  denom (a⁻¹) = num a :=
by rw [fraction.inv_def a ha]

lemma fraction.setoid_inv {a b : fraction} (hac : a ≈ b) :
  a⁻¹ ≈ b⁻¹ :=
begin
  by_cases ha : num a = 0,
  { by_cases hb : num b = 0,
    { simp [ha, hb, fraction.inv_zero] at hac ⊢ },
    { simp [ha, hb, fraction.setoid_iff, denom_ne_zero] at hac,
      cc } },
  { by_cases hb : num b = 0,
    { simp [fraction.setoid_iff, hb, denom_ne_zero] at hac,
      cc },
    { simp [fraction.setoid_iff, ha, hb,
            fraction.inv_num, fraction.inv_denom] at hac ⊢,
      cc } }
end

instance myℚ.has_inv : has_inv myℚ :=
{ inv := quotient.lift (λa, ⟦a⁻¹⟧)
    begin
      intros a b hab,
      apply quotient.sound,
      exact fraction.setoid_inv hab
    end }


/- Real Numbers -/

-- Definition of Cauchy sequences
def is_cau_seq (f : ℕ → ℚ) : Prop :=
∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

-- Type for Cauchy sequences
def cau_seq : Type :=
{f : ℕ → ℚ // is_cau_seq f}

def to_seq (f : cau_seq) : ℕ → ℚ := subtype.val f

-- The quotient relation on Cauchy sequences
instance cau_seq.setoid : setoid cau_seq :=
{ r     := λf g, ∀ε > 0, ∃N, ∀m ≥ N,
            abs (to_seq f m - to_seq g m) < ε,
  iseqv :=
    begin
      apply and.intro,
      { intros f ε hε,
        use 0,
        intros m hm,
        simp,
        exact hε },
      apply and.intro,
      { intros f g hfg ε hε,
        cases hfg ε hε with N hN,
        use N,
        intros m hm,
        rw [abs_sub],
        apply hN m hm },
      { intros f g h hfg hgh ε hε,
        cases hfg (ε / 2) (half_pos hε) with N₁ hN₁,
        cases hgh (ε / 2) (half_pos hε) with N₂ hN₂,
        use (max N₁ N₂),
        intros m hm,
        calc  abs (to_seq f m - to_seq h m)
            ≤ abs (to_seq f m - to_seq g m)
              + abs (to_seq g m - to_seq h m) :
          by apply abs_sub_le
        ... < ε / 2 + ε / 2 :
          add_lt_add (hN₁ m (le_of_max_le_left hm))
            (hN₂ m (le_of_max_le_right hm))
        ... = ε :
          by simp }
    end }

lemma cau_seq.setoid_iff (f g : cau_seq) :
  f ≈ g ↔
  ∀ε > 0, ∃N, ∀m ≥ N, abs (to_seq f m - to_seq g m) < ε :=
by refl

def myℝ : Type :=
quotient cau_seq.setoid

-- Constant Cauchy sequences
def cau_seq.const (q : ℚ) : cau_seq :=
subtype.mk (λn, q)
  begin
    rw is_cau_seq,
    intros ε hε,
    use 0,
    simp,
    exact hε
  end

instance myℝ.has_zero : has_zero myℝ :=
{ zero := ⟦cau_seq.const 0⟧ }

instance myℝ.has_one : has_one myℝ :=
{ one := ⟦cau_seq.const 1⟧ }

instance cau_seq.has_add : has_add cau_seq :=
{ add := λf g, subtype.mk (λn, to_seq f n + to_seq g n) sorry }
-- We omit the proof that the addition of two Cauchy sequences
-- is again a Cauchy sequence.

lemma cau_seq.add_equiv_add {f₁ f₂ g₁ g₂ : cau_seq}
    (hf : f₁ ≈ f₂) (hg : g₁ ≈ g₂) :
  f₁ + g₁ ≈ f₂ + g₂ :=
begin
  rw [cau_seq.setoid_iff],
  intros ε₀ hε₀,
  rw [cau_seq.setoid_iff] at hf hg,
  cases hf (ε₀ / 2) (half_pos hε₀) with Nf hNf,
  cases hg (ε₀ / 2) (half_pos hε₀) with Ng hNg,
  use max Nf Ng,
  intros m hm,
  calc  abs (to_seq (f₁ + g₁) m - to_seq (f₂ + g₂) m)
      = abs ((to_seq f₁ m + to_seq g₁ m)
           - (to_seq f₂ m + to_seq g₂ m)) :
    by refl
  ... = abs ((to_seq f₁ m - to_seq f₂ m)
           + (to_seq g₁ m - to_seq g₂ m)) :
    by simp
  ... ≤ abs (to_seq f₁ m - to_seq f₂ m)
      + abs (to_seq g₁ m - to_seq g₂ m) :
    by apply abs_add
  ... < ε₀ / 2 + ε₀ / 2 :
    add_lt_add (hNf m (le_of_max_le_left hm))
      (hNg m (le_of_max_le_right hm))
  ... = ε₀ :
    by simp
end

instance myℝ.has_add : has_add myℝ :=
{ add := quotient.lift₂ (λa b, ⟦a + b⟧)
    begin
      intros a b c d hac hbd,
      apply quotient.sound,
      exact cau_seq.add_equiv_add hac hbd,
    end }

lemma id_not_cau_seq :
  ¬ is_cau_seq (λn : ℕ, (n : ℚ)) :=
begin
  rw is_cau_seq,
  intro h,
  cases h 1 zero_lt_one with i hi,
  have := hi (i + 1),
  simp at this,
  linarith
end

end LoVe
