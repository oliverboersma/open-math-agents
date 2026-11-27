import Mathlib

/-!
# MathOverflow 373182

Source: https://mathoverflow.net/questions/373182
-/

namespace OMA.S_mo_373182



theorem main : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω]
      [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
      [IsAlgClosure K Ω] [Algebra.IsSeparable K L],
      ¬ FiniteDimensional K L → ∀ a : Ω, IsSeparable L a →
        Algebra.IsSeparable K (IntermediateField.adjoin K ({a} : Set Ω)) := by
  sorry

end OMA.S_mo_373182
