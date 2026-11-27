import Mathlib

/-!
# The proposed bounds for the cosine sequence A327138

Source: https://oeis.org/A327138
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a327138

def rise (k : ℕ) : Prop :=
  0 < k ∧ Real.cos (2*(k:ℝ)) < Real.cos (2*k+2)

/-- An entry is indexed from one, by counting the qualifying positions up to it. -/
noncomputable def rank (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (k+1)).filter rise).card

theorem main : ∀ n k : ℕ, 1 ≤ n → rise k → rank k = n →
    (207:ℝ)/100 < n*Real.pi-k ∧ n*Real.pi-k < (308:ℝ)/100 := by
  sorry

end OMA.S_oeis_a327138
