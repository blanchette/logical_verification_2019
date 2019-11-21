# LoVe Lecture 2: Tactical Proofs

 We see how to prove Lean lemmas using tactics, and we review the most important Lean tactics


## Tactic Mode

A tactic operates on a proof goal and either solves it or creates new subgoals

Tactics are a _backward_ (or _bottom-up_) proof mechanism: they start from the goal and break it down

Multiple tactics in sequence: `begin` _tactic1_`,` …`,` _tacticN_ `end`

Terminal tactic invocation: `by` _tactic_

Tactic composition: _tactic1_ `;` _tactic2_, where _tactic2_ is applied to all subgoals emerging from _tactic1_

The `{` … `}` combinator focuses on the first subgoal; the tactic inside must (fully) solve it


## Demo

[`love02_tactical_proofs_demo.lean`](../lean/love02_tactical_proofs_demo.lean)


## Basic Tactics

### `intro`(`s`)

* `intro` [_name_]
* `intros` [_name1_ … _nameN_]

Moves `∀`-quantified variables, or the assumptions of implications `→`, from the goal into the goal's hypotheses

### `apply`

* `apply` _lemma_

Matches the goal's conclusion with the conclusion of the specified lemma and adds the lemma's hypotheses as new goals

### `exact`

* `exact` _lemma_

Matches the goal's conclusion with the specified lemma, closing the goal

We can often use `apply` in such situations, but `exact` communicates our intentions better

### `assumption`

Finds a hypothesis from the local context that matches the goal's conclusion and applies it to solve the goal

### `refl`

Proves `l = r`, where the two sides are equal up to computation

Computation means unfolding of definitions, β-reduction (application of λ to an argument), projections, `let`, and more

The calculus of inductive constructions is a _computational logic_: logical formulas have computational content

### `ac_refl`

Proves `l = r`, where the two sides are equal up to associativity and commutativity

This works for binary operations that are registered as associative and commutative, e.g., `+` and `*` on `ℕ`

### `use`

* `use` [_term_]

Allows us to supply a witness for an existential quantifier


## Rewriting Tactics

The tactics below take an optional _position_ as argument:

* `at` `⊢`: applies to the conclusion
* `at` _hypothesis1_ … _hypothesisN_: applies to the specified hypotheses
* `at` `*`: applies to all possible hypotheses and to the conclusion

### `rw`

  * `rw` _lemma_ [`at` _position_]

Applies a single equation as a left-to-right rewrite rule, once

To apply an equation right-to-left, prefix its name with `←`

* `rw` `[`_lemma1_`,` …`, `_lemmaN_`]` [`at` _position_]

Abbreviates `rw` _lemma1_`,` …`,` `rw` _lemmaN_

### `simp`

  * `simp` [`at` _position_]

Applies a standard set of rewrite rules (the _simp set_) exhaustively

The set can be extended using the `@[simp]` attribute

It is generally more powerful than `rw` because it can rewrite terms containing variables bound by `λ`, `∀`, `∃`, etc.

  * `simp` `[`_lemma1_`,` …`,`_lemmaN_`]` [`at` _position_]

Same as above, except that the specified lemmas are temporarily added to the simp set

`*` (as a lemma name) represents all local hypotheses

`-` in front of a lemma name temporarily removes the lemma from the simp set

### `dunfold`

* `dunfold` _constant1_ … _constantN_ [`at` _position_]

Expands the definition of one or more constants that are specified without pattern matching (e.g., `not`)


## Induction Tactic

### `induction`

* `induction` _variable_

Performs structural induction on the specified variable

Gives rise to as many subgoals as there are constructors in the definition of the variable's type

Induction hypotheses are available as hypotheses in the subgoals corresponding to recursive constructors (e.g., `nat.succ`)


## Goal Management Tactics

### `rename`

* `rename` _constant-or-hypothesis_ _new-name_

Renames a local constant or hypothesis

### `clear`

* `clear` _constant-or-hypothesis1_ … _constant-or-hypothesisN_

Removes the specified local constants and hypotheses, as long as they are not used anywhere else in the goal


### `revert`

* `revert` _constant-or-hypothesis1_ … _constant-or-hypothesisN_

Performs the opposite of `intros`: Moves the specified local constants and hypotheses into the goal’s conclusion using universal quantification (`∀`) for constants and implication (`→`) for hypotheses


## Hints on How to Write Backward Proofs "Mindlessly"

For logic puzzles, we advocate a "mindless", "video game" style of backward reasoning that relies mostly on `intro`(`s`) and `apply`

Some heuristics that often work:

* If the goal's conclusion is an implication `φ → ψ`, invoke `intro hφ` to move `φ` into your hypotheses: `… (hφ : φ) ⊢ ψ`

* If the goal's conclusion is a universal quantification `∀x : σ, φ`, invoke `intro x` to move it into the local context: `… (x : σ) ⊢ ψ`

* Otherwise, look for a hypothesis or a lemma whose conclusion has the same shape as the goal's conclusion (possibly containing variables that can be matched against the goal), and `apply` it; for example, if the goal's conclusion is `⊢ ψ` and you have a hypothesis `hφψ : φ → ψ`, try `apply hφψ`

* A negated goal `⊢ ¬ φ` is definitionally equal to `⊢ φ → false`, so you can invoke `intro hφ` to produce the subgoal `hφ : φ ⊢ false`; expanding negation's definition by invoking `dunfold not` is often a good strategy

* Sometimes you can make progress by replacing the goal by `false`, by entering `apply false.elim`; as next step, you would typically `apply` a hypothesis of the form `φ → false` or `¬ φ`

* When you face several choices (e.g., between `or.intro_left` and `or.intro_right`), remember which choices you have made, and backtrack when you reach a dead end or have the impression you are not making any progress

* If you have difficulties carrying out a proof, it can be a good idea to check whether the goal actually is provable under the given assumptions; be also aware that even if you started with a provable lemma statement, it is possible that the goal is not provable (e.g., if you used "unsafe" rules such as `or.intro_left`)

It is hard to teach some of these things in class; there is no better way for you to learn this than by doing it, hence the importance of the exercises
