/- LoVe Homework 1: Definitions and Lemma Statements -/

/- Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

import .lovelib

namespace LoVe


/- Question 3: λ-Terms -/

/- We start by declaring four new opaque types. -/

constants α β γ δ : Type

/- 3.2 (**optional**). Complete the following definition.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
λf, f (λg, g (λa, f (λx, a)))

end LoVe
