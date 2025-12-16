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
  exact hP -- `QED` `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- Assume `Q` is true. Prove that `P → Q`. MP
example (hQ : Q) : P → Q := by
  intro hP -- Reduce the goal to the conclusion by assuming the premise, `hP`
  exact hQ -- `QED`, `hQ` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ -- Given `hPQ`, reduce the goal from the conclusion to the premise.
  exact hP  -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- Every proposition implies itself.
example : P → P := by
  intro hP -- Reduce the goal to the conclusion by assuming the premise, `hP`
  exact hP -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- apply a proof of conjuncts: P → Q → P ↔ (P ∧ Q) -> P
example : P → Q → P := by
  intro hP hQ -- Reduce the goal to the conclusion by assuming the premise, `h`
  exact hP    -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
--This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  intros hP hPQ -- Reduce the goal to the conclusion by assuming the premises.
  apply hPQ     -- Given `hPQ`, reduce the goal from the conclusion to the premise.
  exact hP      -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
/-- Property: `→` is transitive -/
lemma arrow_trans : (P → Q) → (Q → R) → P → R := by
  intros hPQ hQR hP -- Reduce the goal to the conclusion by assuming the premises.
  apply hQR         -- Given `hQR`, reduce the goal from the conclusion to the premise.
  apply hPQ         -- Given `hPQ`, reduce the goal from the conclusion to the premise.
  exact hP          -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`,
-- then you will get two goals with the proof focus on the first goal.
-- An example of proof by cases
example : (P → Q → R) → (P → Q) → (P → R) := by
  intros hPQR hPQ hP -- Reduce the goal to the conclusion by assuming the premises.
  apply hPQR         -- Given `hPQR`, reduce the goal from the conclusion to the premise.
                     -- The premise is P -> Q, so two cases are required, P and QED.
                     -- case ⊢ P -----------------------------------------------------
  · exact hP           -- `QED`, `h` is a syntactic match to the goal.
                     -- case ⊢ Q -----------------------------------------------------
  · apply hPQ          -- Given `hPQ`, reduce the goal from the conclusion to the premise.
    exact hP           -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
/-- tactic pattern: apply chain -/
lemma ex_apply_chain : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intros hPR hSQ hRT hQR hS -- Reduce the goal to the conclusion by assuming the premises.
  apply hRT -- Given `hRT`, reduce the goal from the conclusion to the premise.
  apply hQR -- Given `hQR`, reduce the goal from the conclusion to the premise.
  apply hSQ -- Given `hSQ`, reduce the goal from the conclusion to the premise.
  exact hS  -- `QED`, `h` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- an example of an apply chain
example : (P → Q) → ((P → Q) → P) → Q := by
  intros hPQ h_PQ_P -- Reduce the goal to the conclusion by assuming the premises.
  apply hPQ         -- Given `hPQ`, reduce the goal from the conclusion to the premise.
  apply h_PQ_P      -- Given `h_PQ_P`, reduce the goal from the conclusion to the premise.
  exact hPQ         -- `QED`, `hPQ` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  -- Reduce the goal to the conclusion by assuming the premises.
  intros h_PQ_R h_QR_P h_RP_Q
  apply h_QR_P -- Given `h_QR_P`, reduce the goal from the conclusion to the premise.
  intro hQ     -- Reduce the goal to the conclusion by assuming the premise, `hQ`
  apply h_PQ_R -- Given `h_PQ_R`, reduce the goal from the conclusion to the premise.
  intro hP     -- Reduce the goal to the conclusion by assuming the premise, `hP`
  exact hQ     -- `QED`, `hQ` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intros h_QP_P hQR hRP -- Reduce the goal to the conclusion by assuming the premises.
  apply h_QP_P          -- Given `h_QP_P`, reduce the goal from the conclusion to the premise.
  intro hQ              -- Reduce the goal to the conclusion by assuming the premise, `hQ`
  apply h_QP_P          -- Given `hRP`, reduce the goal from the conclusion to the premise.
  intro hQ'             -- Reduce the goal to the conclusion by assuming the premise, `hQ'`
  apply hRP             -- Given `hRP`, reduce the goal from the conclusion to the premise.
  apply hQR             -- Given `hQR`, reduce the goal from the conclusion to the premise.
  exact hQ              -- `QED`, `hQ` is a syntactic match to the goal.



-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example : (((P → Q) → Q) → Q) → P → Q := by
  intros h_PQ_Q hP -- Reduce the goal to the conclusion by assuming the premises.
  apply h_PQ_Q     -- Given `h_PQ_Q`, reduce the goal from the conclusion to the premise.
  intro hPQ        -- Reduce the goal to the conclusion by assuming the premise, `hPQ`
  apply hPQ        -- Given `hPQ`, reduce the goal from the conclusion to the premise.
  exact hP         -- `QED`, `hP` is a syntactic match to the goal.

-------------------------------------------------------------------------------
-- an example of intro-apply tactic pattern
example :
  (((P → Q → Q) → (P → Q) → Q) → R) →
    ((((P → P) → Q) → P → P → Q) → R) →
      (((P → P → Q) → (P → P) → Q) → R) → R := by
  intros h1 h2 h3 -- Reduce the goal to the conclusion by assuming the premises.
  apply h2        -- Given `h2`, reduce the goal from the conclusion to the premise.
  intro h_PP_Q    -- Reduce the goal to the conclusion by assuming the premise, `h_PP_Q`
  intros hP hP'   -- Reduce the goal to the conclusion by assuming the premises.
  apply h_PP_Q    -- Given `h_PP_Q`, reduce the goal from the conclusion to the premise.
  intro hP''      -- Reduce the goal to the conclusion by assuming the premise, `hP''`
  exact hP        -- `QED`, `hP` is a syntactic match to the goal.

-- another approach in one line
example :
  (((P → Q → Q) → (P → Q) → Q) → R) →
    ((((P → P) → Q) → P → P → Q) → R) →
      (((P → P → Q) → (P → P) → Q) → R) → R := by
  tauto
