import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Secondary authors: Kevin Buzzard, Den Ducoff, Gemini 3

# Tactics introduced in Sheet 1:

* `apply` h            -- Given `h`, reduce the goal from the conclusion to the premise.
* `apply` h1 `at` `h2` -- Given `h1`, reduce `h2` from the conclusion to the premise.

* `exact` h            -- `QED`, `h` is a syntactic match to the goal.

* `intro` h            -- Reduce the goal to the conclusion by assuming the premise, `h`
* `intro` h1 ... hn    -- Reduce the goal to the conclusion by assuming the premises,
-/

variable (P Q R S T : Prop)

-------------------------------------------------------------------------------
-- By definition, a hypothesis, (hp : P), is true, : P
example (hP : P) : P := by

sorry
-------------------------------------------------------------------------------
-- Assume `Q` is true. Prove that `P → Q`. MP
example (hQ: Q) : P → Q := by

sorry
-------------------------------------------------------------------------------
-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (hPQ : P → Q) (hP : P) : Q := by

sorry
-------------------------------------------------------------------------------
-- Every proposition implies itself.
example : P → P := by

sorry
-------------------------------------------------------------------------------
-- apply a proof of conjuncts: P → Q → P ↔ (P ∧ Q) -> P
example : P → Q → P := by

sorry
-------------------------------------------------------------------------------
-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
--This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by

sorry
-------------------------------------------------------------------------------
/-- Property: `→` is transitive -/
lemma arrow_trans : (P → Q) → (Q → R) → P → R := by

sorry
-------------------------------------------------------------------------------
-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`,
-- then you will get two goals with the proof focus on the first goal.
-- An example of proof by cases
example : (P → Q → R) → (P → Q) → (P → R) := by

sorry
-------------------------------------------------------------------------------
/-- tactic pattern: apply chain -/
lemma ex_apply_chain : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by

sorry
-------------------------------------------------------------------------------
-- an example of an apply chain
example : (P → Q) → ((P → Q) → P) → Q := by

sorry
-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by

sorry
-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : ((Q → P) → P) → (Q → R) → (R → P) → P := by

sorry
-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : (((P → Q) → Q) → Q) → P → Q := by

sorry
-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example :
  (((P → Q → Q) → (P → Q) → Q) → R) →
    ((((P → P) → Q) → P → P → Q) → R) →
      (((P → P → Q) → (P → P) → Q) → R) → R := by

sorry
-- another approach in one line
example :
  (((P → Q → Q) → (P → Q) → Q) → R) →
    ((((P → P) → Q) → P → P → Q) → R) →
      (((P → P → Q) → (P → P) → Q) → R) → R := by
  tauto
