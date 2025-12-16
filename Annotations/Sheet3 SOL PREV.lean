import Mathlib.Tactic -- import all the tactics

/-!
# Tactics introduced in Sheet 3
* `by_cases` -- Split the goal into two cases: when it is True and when it is False.
   -- FSOC, set the goal to False and assume that its negation is True, `hnotG`.
* `by_contra hnotG`
* `change <equal goal>` -- The goal is definitionally equal to `<equal goal>`
* `change hEquiv at h` -- `hEqual`is definitionally equal to `h`
-/

variable (P Q R : Prop)

-------------------------------------------------------------------------------
-- Property: not not Prop is equivalent to Prop, this is the double negation rule
example : ¬ ¬ P → P := by
  intro hnotnotP
  -- FSOC, set the goal to False and assume that its negation is True, `hnotP`.
  by_contra hnotP
  -- `¬ P → False` is definitionally equal to `hnotnotP`.
  change ¬ P → False at hnotnotP
  apply hnotnotP -- apply `hnotnotP`, to replace the conclusion with the premise in the goal.
  exact hnotP

  --sorry
-------------------------------------------------------------------------------
-- Property: Not True is equivalent to False, this is the exclusion of th middle
example : ¬True → False := by
  intro hnotT
  -- `True -> False` is definitionally equal to `hnotT`.
  change True -> False at hnotT
  apply hnotT -- apply `hnotT`, to replace the conclusion with the premise in the goal.
  trivial -- The True goal is defined to be 'trivially true', QED

  --sorry
-------------------------------------------------------------------------------
-- Property: Not False is equivalent to True, this is the exclusion of th middle
example : ¬False → True := by
  intro hnotF
  -- `False -> False` is definitionally equal to `hnotF`.
  change False -> False at hnotF
  trivial -- The True goal is defined to be 'trivially true', QED

  --sorry
-------------------------------------------------------------------------------
-- Property: True is equivalent to Not False, this is the exclusion of the middle
example : True → ¬False := by
  intro hT
  change False -> False -- The goal is definitionally equal to `False -> False`
  intro hF
  exact hF

  --sorry
-------------------------------------------------------------------------------
-- Property: A False premise implies anything
example : False → ¬True := by
  intro hF
  change True -> False -- The goal is definitionally equal to `True -> False`
  intro hT
  exact hF

  --sorry
-------------------------------------------------------------------------------
-- Property: A False premise implies anything
example : False → ¬P := by
  intro hF
  change P -> False -- The goal is definitionally equal to `P -> False`
  intro hP
  exact hF

  --sorry
-- ----------------------------------------------------------
-- Property: P ∧ ¬P implies anything
example : P → (¬P → False) := by
  intro hP hnotP
  -- `P -> False` is definitionally equal to `hnotP`.
  change P -> False at hnotP
  apply hnotP -- apply `hnotP`, to replace the conclusion with the premise in the goal.
  exact hP

  --sorry
-------------------------------------------------------------------------------
-- Property: p is equivalent to ¬¬P, the double negation rule
example : P → ¬¬P := by
  intro hP
  change ¬P -> False -- The goal is definitionally equal to `¬P -> False`
  intro hnotP
  -- `P -> False` is definitionally equal to `hnotP`.
  change P -> False at hnotP
  apply hnotP -- apply `hnotP`, to replace the conclusion with the premise in the goal.
  exact hP

  --sorry
-- ----------------------------------------------------------
-- Property: the forward contrapositive rule
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnotQ
  -- `Q -> False` is definitionally equal to `hnotQ`.
  change P -> False
  intro hP
  -- Apply the implication, `hPQ `,
  -- to replace the premise term, `hP,`,  with the conclusion term.
  -- Rename the new conclusion term accordingly, `hQ`.
  apply hPQ at hP
  rename' hP => hQ
  -- `Q -> False` is definitionally equal to `hnotQ`.
  change Q -> False at hnotQ
  apply hnotQ -- apply `hnotQ`, to replace the conclusion with the premise in the goal.
  exact hQ

  --sorry
-- ----------------------------------------------------------
-- Property: the backward contrapositive rule
example : (¬Q → ¬P) → P → Q := by
  intro hnotQnotP hP
  -- FSOC, set the goal to False and assume that its negation is True, `hnotQ`.
  by_contra hnotQ
  -- Apply the implication, `hnotQnotP `,
  -- to replace the premise term, `hnotQ,`,  with the conclusion term.
  -- Rename the new conclusion term accordingly, `hnotP`.
  apply hnotQnotP at hnotQ
  rename' hnotQ => hnotP
  -- `P -> False` is definitionally equal to `hnotP`.
  change P -> False at hnotP
  apply hnotP -- apply `hnotP`, to replace the conclusion with the premise in the goal.
  exact hP

  --sorry
-- ----------------------------------------------------------
-- The double negation rule for False
example : ¬¬False → False := by
  intro hnotnotF
  -- `(¬False -> False)` is definitionally equal to `hnotnotF`.
  change (¬False -> False) at hnotnotF
  apply hnotnotF -- apply `hnotnotF`, to replace the conclusion with the premise in the goal.
  change False -> False -- The goal is definitionally equal to `False -> False`
  intro hF
  exact hF

  --sorry
-- ----------------------------------------------------------
-- The double negation rule for a proposition O
example : ¬¬P → P := by
  intro hnotnotP
  -- `¬P -> False` is definitionally equal to `hnotnotP`.
  change ¬P -> False at hnotnotP
  -- FSOC, set the goal to False and assume that its negation is True, `hnotP`.
  by_contra hnotP
  apply hnotnotP -- apply `hnotnotP`, to replace the conclusion with the premise in the goal.
  exact hnotP

--sorry
