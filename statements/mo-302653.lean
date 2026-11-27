import Mathlib

/-!
# Compact subspaces of sober spaces

Source: https://mathoverflow.net/questions/302653
Credit: @eliayousf

Sobriety is the combination of the T0 property and Mathlib's QuasiSober
property, which say that every nonempty irreducible closed subset has a
unique generic point. Compactness is in the subspace topology and carries
no Hausdorff assumption. The statement expresses the affirmative answer
to the question, whose edit gives a counterexample.
-/

namespace OMA.S_mo_302653

theorem main : ∀ (X : Type) [TopologicalSpace X] [T0Space X] [QuasiSober X]
    (S : Set X), IsCompact S → T0Space S ∧ QuasiSober S := by
  sorry

end OMA.S_mo_302653
