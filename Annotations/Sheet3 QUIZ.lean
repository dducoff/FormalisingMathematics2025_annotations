import Mathlib.Tactic -- import all the tactics
/-
[Attributions](foo)
[CS 22 Tactics](https://docs.cs22.io/tactics)
-/

/-!
# Tactics introduced in Sheet 3

* by_cases hP -- either hP ∨ h¬P
* by_contra `hnotGoal` -- FSOC: Assume the goal is false: `hnotGoal`. Reset the goal: `⊢ False`.
* change `goalEquivalent` -- The goal is definitionally equal to `goalEquivalent`
* change $1 at  -- `$2`is definitionally equal to `h`
-/

variable (P Q R : Prop)

-------------------------------------------------------------------------------
-- Property: not not Prop is equivalent to Prop, this is the double negation rule
-- Use `apply` tactic instead of the `have` tactic.
example : ¬ ¬ P → P := by
  intro hnotnotP
  by_contra hnotP -- FSOC: Assume the goal is False, `hnotP`, and set a new goal: `⊢ False`.
  change ¬P -> False at hnotnotP -- Rewrite the hypothesis: `enumerate` as: `¬P -> False`
  apply hnotnotP
  exact hnotP

-- Property: not not Prop is equivalent to Prop, this is the double negation rule
-- Use the `have` tactic instead of the `apply` tactic.
example : ¬ ¬ P → P := by
  intro hnotnotP
  by_contra hnotP -- FSOC: Assume the goal is False, `hnotP`, and set a new goal: `⊢ False`.
  change ¬P -> False at hnotnotP -- Rewrite the hypothesis: `enumerate` as: `¬P -> False`
  have hFalse : False := hnotnotP hnotP
  exact hFalse

#check And.intro
#check And
-------------------------------------------------------------------------------
-- Property: Not True is equivalent to False, this is the exclusion of th middle
example : ¬True → False := by

  sorry
-------------------------------------------------------------------------------
-- Property: Not False is equivalent to True, this is the exclusion of th middle
example : ¬False → True := by

  sorry
-------------------------------------------------------------------------------
-- Property: True is equivalent to Not False, this is the exclusion of the middle
example : True → ¬False := by

  sorry
-------------------------------------------------------------------------------
-- Property: A False premise implies anything
example : False → ¬True := by

  sorry
-------------------------------------------------------------------------------
-- Property: A False premise implies anything
example : False → ¬P := by

  sorry
-- ----------------------------------------------------------
-- Property: P ∧ ¬P implies anything
example : P → (¬P → False) := by

  sorry
-------------------------------------------------------------------------------
-- Property: p is equivalent to ¬¬P, the double negation rule
example : P → ¬¬P := by
  sorry
-- ----------------------------------------------------------
-- Property: the forward contrapositive rule
example : (P → Q) → ¬Q → ¬P := by
  sorry
-- ----------------------------------------------------------
-- Property: the backward contrapositive rule
example : (¬Q → ¬P) → P → Q := by
  sorry
-- ----------------------------------------------------------
-- The double negation rule for False
example : ¬¬False → False := by
  sorry
-- ----------------------------------------------------------
-- The double negation rule for a proposition O
example : ¬¬P → P := by
  sorry
