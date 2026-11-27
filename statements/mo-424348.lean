import Mathlib

/-!
# MathOverflow 424348

Source: https://mathoverflow.net/questions/424348
-/

namespace OMA.S_mo_424348

open Finset

theorem main : ∀ (n d : ℕ), 2 ≤ n → 1 ≤ d →
    ∀ v : Fin ((n - 1) * d) → Fin d → ℝ,
    (∀ e : Fin d ↪ Fin ((n - 1) * d), LinearIndependent ℝ (fun i => v (e i))) →
    ∀ (x : Fin n → Fin d → ℝ) (a b : Fin ((n - 1) * d) → Fin n),
    (∀ i, a i ≠ b i) →
    (∀ i, (∑ k, v i k * x (a i) k) = ∑ k, v i k * x (b i) k) →
    ∃ p q : Fin n, p ≠ q ∧ x p = x q := by
  sorry

end OMA.S_mo_424348
