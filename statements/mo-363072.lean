import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Data.Real.Basic

/-!
# Frobenius pairing with an optimal permutation

Lo Celso, MathOverflow question 363072, revised 15 June 2020.
Source: https://mathoverflow.net/questions/363072 (CC BY-SA 4.0).

A permutation set is the graph of a permutation. Ties in the maximum
assignment score and zero entries of either sign are allowed.
-/

namespace OMA.S_mo_363072

theorem main :
    ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 0) (hcol : ∀ j, ∑ i, A i j = 0)
    (hB : B ∈ doublyStochastic ℝ (Fin n)) (σ : Equiv.Perm (Fin n))
    (hon : ∀ i, 0 ≤ A i (σ i)) (hoff : ∀ i j, j ≠ σ i → A i j ≤ 0)
    (hmax : ∀ τ : Equiv.Perm (Fin n), ∑ i, B i (τ i) ≤ ∑ i, B i (σ i)),
    0 ≤ ∑ i, ∑ j, A i j * B i j := by
  sorry

end OMA.S_mo_363072
