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

  sorry
example : True → True := by

  sorry
example : False → True := by

  sorry
example : False → False := by

  sorry
example : (True → False) → False := by

  sorry
example : False → P := by

  sorry
example : True → False → True → False → True → False := by

  sorry
example : P → (P → False) → False := by

  sorry
example : (P → False) → P → Q := by

  sorry
example : (True → False) → P := by

  sorry
