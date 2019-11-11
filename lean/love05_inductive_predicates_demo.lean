/- LoVe Demo 5: Inductive Predicates -/

import .love04_functional_programming_demo

namespace LoVe


/- Introductory Example -/

inductive even : ℕ → Prop
| zero    : even 0
| add_two : ∀n, even n → even (n + 2)


/- Logical Symbols -/

#print false
#print true
#print and
#print or
#print Exists
#print eq

#check nat.le.dest

lemma nat.le.dest2 :
  ∀n m : ℕ, n ≤ m → ∃k, k + n = m :=
begin
  intros n m h_gt,
  cases @nat.le.dest n m h_gt with k nk_eq_m,
  use k,
  linarith
end


/- Example: Full Binary Trees -/

#check btree

inductive is_full {α : Type} : btree α → Prop
| empty : is_full empty
| node (a : α) (l r : btree α) (hl : is_full l) (hr : is_full r)
    (empty_iff : l = empty ↔ r = empty) :
  is_full (node a l r)

inductive is_full₂ {α : Type} : btree α → Prop
| empty : is_full₂ empty
| node : ∀(a : α) (l r : btree α), is_full₂ l → is_full₂ r →
    (l = empty ↔ r = empty) →
  is_full₂ (node a l r)

lemma is_full_singleton {α : Type} (a : α) :
  is_full (node a empty empty) :=
begin
  apply is_full.node,
  repeat { apply is_full.empty },
  refl
end

lemma is_full_t0 :
  is_full t0 :=
is_full_singleton _

lemma is_full_t1 :
  is_full t1 :=
is_full_singleton _

lemma is_full_t2 :
  is_full t2 :=
begin
  rw t2,
  apply is_full.node,
  { exact is_full_t0 },
  { exact is_full_t1 },
  { simp [t0, t1] }
end

lemma is_full_mirror {α : Type} :
  ∀t : btree α, is_full t → is_full (mirror t)
| empty        := by intro; assumption
| (node a l r) :=
  begin
    intro full_t,
    cases full_t,
    rw mirror,
    apply is_full.node,
    repeat { apply is_full_mirror, assumption },
    simp [mirror_eq_empty_iff, *]
  end

lemma is_full_mirror₂ {α : Type} :
  ∀t : btree α, is_full t → is_full (mirror t)
| _ is_full.empty :=
  begin
    rw mirror,
    exact is_full.empty
  end
| _ (is_full.node a l r hl hr empty_iff) :=
  begin
    rw mirror,
    apply is_full.node,
    repeat { apply is_full_mirror₂, assumption },
    simp [mirror_eq_empty_iff, *]
  end

lemma is_full_node_iff {α : Type} (a : α) (l r : btree α) :
  is_full (node a l r) ↔
  is_full l ∧ is_full r ∧ (l = empty ↔ r = empty) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    cc },
  { intro h,
    apply is_full.node,
    repeat { cc } }
end

lemma is_full_mirror₃ {α : Type} :
  ∀t : btree α, is_full t → is_full (mirror t)
| _ is_full.empty                        :=
  by rw mirror; exact is_full.empty
| _ (is_full.node a l r hl hr empty_iff) :=
  by simp [mirror, is_full_node_iff, is_full_mirror₃ l hl,
    is_full_mirror₃ r hr, mirror_eq_empty_iff, empty_iff]


/- Example: Sorted Lists -/

inductive sorted : list ℕ → Prop
| nil : sorted []
| single {x : ℕ} : sorted [x]
| two_or_more {x y : ℕ} {xs : list ℕ} (xy : x ≤ y)
    (yxs : sorted (y :: xs)) :
  sorted (x :: y :: xs)

example :
  sorted [] :=
sorted.nil

example :
  sorted [2] :=
sorted.single

example :
  sorted [3, 5] :=
begin
  apply sorted.two_or_more,
  { linarith },
  { exact sorted.single }
end

example :
  sorted [3, 5] :=
sorted.two_or_more (by linarith) sorted.single

example :
  sorted [7, 9, 9, 11] :=
sorted.two_or_more (by linarith)
  (sorted.two_or_more (by linarith)
    (sorted.two_or_more (by linarith)
      sorted.single))

example :
  ¬ sorted [17, 13] :=
assume h : sorted [17, 13],
have 17 ≤ 13 :=
  match h with
  | sorted.two_or_more xy yxs := xy
  end,
have ¬ (17 ≤ 13) := by linarith,
show false, from by cc


/- Example: Well-formed and Ground First-Order Terms -/

inductive term (α β : Type) : Type
| var {} : β → term
| fn     : α → list term → term

export term (var fn)

inductive well_formed {α β : Type} (arity : α → ℕ) :
  term α β → Prop
| var (x : β) : well_formed (var x)
| fn (f : α) (ts : list (term α β))
    (hargs : ∀t ∈ ts, well_formed t)
    (hlen : list.length ts = arity f) :
  well_formed (fn f ts)

inductive variable_free {α β : Type} : term α β → Prop
| fn (f : α) (ts : list (term α β))
    (hargs : ∀t ∈ ts, variable_free t) :
  variable_free (fn f ts)


/- Example: Reflexive Transitive Closure -/

inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| base (a b : α) : r a b → rtc a b
| refl (a : α) : rtc a a
| trans (a b c : α) : rtc a b → rtc b c → rtc a c

lemma rtc_rtc_iff_rtc {α : Type} (r : α → α → Prop) (a b : α) :
  rtc (rtc r) a b ↔ rtc r a b :=
begin
  apply iff.intro,
  { intro h,
    induction h,
    case rtc.base : x y {
      assumption },
    case rtc.refl : x {
      apply rtc.refl },
    case rtc.trans : x y z {
      apply rtc.trans,
      assumption,
      assumption } },
  { intro h,
    apply rtc.base,
    assumption }
end

lemma rtc_rtc_eq_rtc {α : Type} (r : α → α → Prop) :
  rtc (rtc r) = rtc r :=
begin
  apply funext,
  intro a,
  apply funext,
  intro b,
  apply propext,
  apply rtc_rtc_iff_rtc
end


/- New Tactics -/

example {α : Type} (a b c d : α) (f : α → α → α)
    (hab : a = c) (hcd : b = d) :
  f a b = f c d :=
by cc

example (i : ℤ) (hagt : i > 5) :
  2 * i > 8 :=
by linarith

example (i : ℤ) :
  1 + (i + -1) = i :=
by norm_num

end LoVe
