import Mathlib

/-!
# OEIS A000247

Source: https://oeis.org/A000247
Credit: @willperacchio

This is L. Edson Jeffery's matrix identity. The rows and columns use zero-based
indices, so the source's entry numbered `n - 2` has index `n - 3`.
-/

open scoped Matrix

namespace OMA.S_oeis_a000247

/-- The off-diagonal neighbors and the last diagonal entry are ones. -/
def unitPrimitiveMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j =>
    if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i = j ∧ i.val + 1 = n) then 1 else 0

def a (n : ℕ) : ℕ := 2 ^ n - n - 2

theorem main : a 2 = 0 ∧
    ∀ (n : ℕ) (hn : 2 < n),
      ((unitPrimitiveMatrix n ^ n) *ᵥ (fun _ : Fin n => 1))
        ⟨n - 3, by omega⟩ = a n := by
  sorry

end OMA.S_oeis_a000247
