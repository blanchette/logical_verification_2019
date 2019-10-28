/- LoVe Homework 1: Definitions and Lemma Statements -/

/- Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

import .lovelib

namespace LoVe


/- Question 1: Snoc -/

/- 1.1. Define the function `snoc` that appends a single element to the end of
a list. -/

def snoc {α : Type} : list α → α → list α
:= sorry

/- 1.2. Convince yourself that your definition of `snoc` works by testing it on
a few examples. -/

-- invoke `#reduce` or `#eval` here


/- Question 2: Map -/

/- 2.1. Define a generic `map` function that applies a function to every element
in a list. -/

def map {α : Type} {β : Type} (f : α → β) : list α → list β
:= sorry

/- 2.2. State the so-called functiorial properties of `map` as lemmas.
Schematically:

     map (λx, x) xs = xs
     map (λx, g (f x)) xs = map g (map f xs)

Make sure to state the second law as generally as possible, for arbitrary
types. -/

-- enter your lemma statements here


/- Question 3: λ-Terms -/

/- We start by declaring four new opaque types. -/

constants α β γ δ : Type

/- 3.1. Complete the following definitions, by providing terms with the expected
type. -/

def B : (α → β) → (γ → α) → γ → β :=
sorry

def S : (α → β → γ) → (α → β) → α → γ :=
sorry

def more_nonsense : ((α → β) → γ → δ) → γ → β → δ :=
sorry

def even_more_nonsense : (α → β) → (α → γ) → α → β → γ :=
sorry

/- 3.2 (**optional**). Complete the following definition.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
sorry

end LoVe
