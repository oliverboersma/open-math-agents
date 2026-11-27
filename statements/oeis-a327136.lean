import Mathlib

/-!
# Proposed bounds for the sine sequence A327136

Source: https://oeis.org/A327136
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a327136

def dip (k : ℕ) : Prop :=
  Real.sin (2*(k:ℝ)+2) < Real.sin (2*k) ∧
  Real.sin (2*(k:ℝ)+2) < Real.sin (2*k+4)

/-- Zero-based enumeration of the qualifying positions; the OEIS index is n+1. -/
noncomputable def term (n : ℕ) : ℕ := Nat.nth dip n

theorem main : ∀ n : ℕ, (1285:ℝ)/1000 < ((n:ℝ)+1)*Real.pi-term n ∧
    ((n:ℝ)+1)*Real.pi-term n < (1286:ℝ)/1000 := by
  sorry

end OMA.S_oeis_a327136
