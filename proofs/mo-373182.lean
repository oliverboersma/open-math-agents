import OMAStatements.S_mo_373182
import Mathlib

/-!
# MathOverflow 373182

Separability is transitive: since L/K is separable and a is separable over L, a is separable
over K (Mathlib's `IsSeparable.of_algebra_isSeparable_of_isSeparable`). A simple extension generated
by a separable element is separable (`IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`).
The infinite-degree hypothesis is not needed.
-/

theorem OMA.solution : type_of% @OMA.S_mo_373182.main := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ a ha
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K Ω).mpr
    (IsSeparable.of_algebra_isSeparable_of_isSeparable K ha)
