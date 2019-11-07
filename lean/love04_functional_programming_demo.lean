/- LoVe Demo 4: Functional Programming -/

import .lovelib

namespace LoVe


/- Example: Lists -/

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

#check list.reverse

lemma reverse_append {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| []        ys := by simp [reverse]
| (x :: xs) ys := by simp [reverse, reverse_append xs]

lemma reverse_reverse {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| []        := by refl
| (x :: xs) :=
  by simp [reverse, reverse_append, reverse_reverse xs]

def map {α β : Type} (f : α → β) : list α → list β
| []        := []
| (x :: xs) := f x :: map xs

def map₂ {α β : Type} : (α → β) → list α → list β
| _ []        := []
| f (x :: xs) := f x :: map₂ f xs

#check list.map

lemma map_ident {α : Type} :
  ∀xs : list α, map (λx, x) xs = xs
| []        := by refl
| (x :: xs) := by simp [map, map_ident xs]

lemma map_ident₂ {α : Type} :
  ∀xs : list α, map (λx, x) xs = xs
| []        := by refl
| (x :: xs) :=
  have ih : map (λx, x) xs = xs := map_ident₂ xs,
  begin
    rw map,
    rw ih
  end

lemma map_ident₃ {α : Type} :
  ∀xs : list α, xs = map (λx, x) xs
| []        := by refl
| (x :: xs) :=
  have ih : _ := map_ident₃ xs,
  by rw [map, ←ih]

lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ) :
  ∀xs : list α, map (λx, g (f x)) xs = map g (map f xs)
| []        := by refl
| (x :: xs) := by simp [map, map_comp xs]

lemma map_append {α β : Type} (f : α → β) :
  ∀xs ys : list α, map f (xs ++ ys) = map f xs ++ map f ys
| []        ys := by refl
| (x :: xs) ys := by simp [map, map_append xs]

lemma map_reverse {α β : Type} (f : α → β) :
  ∀xs : list α, map f (reverse xs) = reverse (map f xs)
| []        := by refl
| (x :: xs) :=
  by simp [map, reverse, map_append, map_reverse xs]

def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := length xs + 1

#check list.length

def bcount {α : Type} (p : α → bool) : list α → ℕ
| []        := 0
| (x :: xs) :=
  match p x with
  | tt := bcount xs + 1
  | ff := bcount xs
  end

def bfilter {α : Type} (p : α → bool) : list α → list α
| []        := []
| (x :: xs) :=
  match p x with
  | tt := x :: bfilter xs
  | ff := bfilter xs
  end

def nth {α : Type} : list α → ℕ → option α
| []        _       := none
| (x :: _)  0       := some x
| (_ :: xs) (n + 1) := nth xs n

#check list.nth

lemma exists_nth {α : Type} :
  ∀(xs : list α) (n : ℕ), n < length xs → ∃a, nth xs n = some a
| []        _       h :=
  false.elim (not_le_of_gt h (nat.zero_le _))
| (x :: _)  0       _ := ⟨x, rfl⟩
| (_ :: xs) (n + 1) h :=
  have n_lt : n < length xs := lt_of_add_lt_add_right h,
  have ih : ∃a, nth xs n = some a := exists_nth xs n n_lt,
  by simp [nth, ih]

lemma lt_length_of_nth_some {α : Type} (a : α) :
  ∀(xs : list α) (n : ℕ), nth xs n = some a → n < length xs
| []        _       h := by contradiction
| (_ :: xs) 0       _ :=
  show 0 < length xs + 1, from
    lt_add_of_le_of_pos (nat.zero_le _) zero_lt_one
| (_ :: xs) (n + 1) h :=
  have ih : nth xs n = some a,
    by simp [nth] at h; assumption,
  show n + 1 < length xs + 1, from
    add_lt_add_right (lt_length_of_nth_some _ _ ih) 1

def tail {α : Type} (xs : list α) : list α :=
match xs with
| []      := []
| _ :: xs := xs
end

#check list.tail

def head {α : Type} (xs : list α) : option α :=
match xs with
| []     := none
| x :: _ := some x
end

#check list.head

def zip {α β : Type} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| []        _         := []
| (_ :: _)  []        := []

#check list.zip

lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys, map (λp : α × β, (f p.1, g p.2)) (zip xs ys) =
    zip (map f xs) (map g ys)
| (x :: xs) (y :: ys) :=
  begin
    simp [zip, map],
    exact (map_zip _ _)
  end
| []        _         := by refl
| (_ :: _)  []        := by refl

lemma min_add_add (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
have l + m ≤ l + n ↔ m ≤ n :=
begin
  rw add_comm l,
  rw add_comm l,
  apply nat.add_le_add_iff_le_right
end,
by by_cases m ≤ n; simp [min, *]

lemma length_zip {α β : Type} :
  ∀(xs : list α) (ys : list β),
    length (zip xs ys) = min (length xs) (length ys)
| (x :: xs) (y :: ys) :=
  by simp [zip, length, length_zip xs ys, min_add_add]
| []        _         := by refl
| (_ :: _)  []        := by refl

lemma injection_example {α : Type} (x y : α) (xs ys : list α)
    (h : list.cons x xs = list.cons y ys) :
  x = y ∧ xs = ys :=
begin
  cases h,
  apply and.intro,
  { refl },
  { refl }
end

lemma distinctness_example {α : Type} (x y : α) (xs ys : list α)
    (h : [] = y :: ys) :
  false :=
by cases h


/- Example: Binary Trees -/

inductive btree (α : Type) : Type
| empty {} : btree
| node     : α → btree → btree → btree

export btree (empty node)

def t0 : btree ℕ := node 0 empty empty
def t1 : btree ℕ := node 1 empty empty
def t2 : btree ℕ := node 2 t0 t1

def mirror {α : Type} : btree α → btree α
| empty        := empty
| (node a l r) := node a (mirror r) (mirror l)

lemma mirror_eq_empty_iff {α : Type} :
  ∀t : btree α, mirror t = empty ↔ t = empty
| empty        := by refl
| (node _ _ _) := by simp [mirror]

lemma mirror_mirror {α : Type} :
  ∀t : btree α, mirror (mirror t) = t
| empty        := by refl
| (node a l r) :=
  begin
    simp [mirror],
    apply and.intro,
    { apply mirror_mirror l },
    { apply mirror_mirror r }
  end


/- Example: Colors -/

structure rgb :=
(red green blue : ℕ)

structure rgba extends rgb :=
(alpha : ℕ)

#print rgb
#print rgba

#reduce rgb.mk 0xff 0xcc 0xff
#reduce ({red := 0xff, green := 0xcc, blue := 0xff} : rgb)
#reduce ({red := 0xff, green := 0xcc, blue := 0xff,
  alpha := 0x7f} : rgba)

def red : rgb := {red := 0xff, green := 0x00, blue := 0x00}
def semitransparent_red : rgba := {alpha := 0x7f, ..red}
def green : rgb := ⟨0x00, 0xff, 0x00⟩

#print red
#print semitransparent_red
#print green

def shuffle (c : rgb) : rgb :=
{red := c.green, green := c.blue, blue := c.red}

lemma shuffle_shuffle_shuffle (c : rgb) : 
  shuffle (shuffle (shuffle c)) = c :=
by cases c; refl

end LoVe
