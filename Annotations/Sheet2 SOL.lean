import Mathlib.Tactic -- imports all the Lean tactics

/-!
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Secondary authors: Kevin Buzzard, Den Ducoff, Gemini 3

# Tactics introduced in Sheet 2

* `exfalso` -- FSOC: set the goal to be False
* `trivial` -- `QED` - it is axiomatic that `⊢ True ` reduces to `No goals`.
-/

variable (P Q R : Prop)

example : True := by
  trivial -- `QED`, it is axiomatic that  `⊢ True ` reduces to `No goals`.

example : True → True := by
  intro hT -- Reduce the goal to the conclusion by assuming the premise, `hT`
  exact hT -- `QED`, `hT` is a syntactic match to the goal.

example : False → True := by
  intro hF -- Reduce the goal to the conclusion by assuming the premise, `hF`
  trivial  -- `QED`, it is axiomatic that  `⊢ True ` reduces to `No goals`.

example : False → False := by
  intro hF -- Reduce the goal to the conclusion by assuming the premise, `hF`
  exact hF -- `QED`, `hF` is a syntactic match to the goal.

example : (True → False) → False := by
  intro hTF -- Reduce the goal to the conclusion by assuming the premise, `hTF`
  apply hTF -- Given `hTF`, reduce the goal from the conclusion to the premise.
  trivial   -- `QED`, it is axiomatic that  `⊢ True ` reduces to `No goals`.

example : False → P := by
  intro hF -- Reduce the goal to the conclusion by assuming the premise, `hF`
  exfalso  -- FSOC: set the goal to be False
  exact hF -- `QED`, `hF` is a syntactic match to the goal.

example : True → False → True → False → True → False := by
  intros hT hF hT' hF' hT'' -- Reduce the goal to the conclusion by assuming the premises.
  exact hF -- `QED`, `h` is a syntactic match to the goal.

example : P → (P → False) → False := by
  intros hP hPF -- Reduce the goal to the conclusion by assuming the premises.
  apply hPF     -- Given `hPF`, reduce the goal from the conclusion to the premise.
  exact hP      -- `QED`, `h` is a syntactic match to the goal.

example : (P → False) → P → Q := by
  intros hPF hP -- Reduce the goal to the conclusion by assuming the premises.
  exfalso       -- FSOC: set the goal to be False
  apply hPF     -- Given `hPF`, reduce the goal from the conclusion to the premise.
  exact hP      -- `QED`, `h` is a syntactic match to the goal.

example : (True → False) → P := by
  intro hTF -- Reduce the goal to the conclusion by assuming the premise, `hTF`
  exfalso   -- FSOC: set the goal to be False
  apply hTF -- Given `hTF`, reduce the goal from the conclusion to the premise.
  trivial   -- `QED`, it is axiomatic that  `⊢ True ` reduces to `No goals`.
