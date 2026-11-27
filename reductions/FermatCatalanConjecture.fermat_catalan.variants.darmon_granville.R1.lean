import FormalConjectures.Wikipedia.FermatCatalanConjecture
import Mathlib

/-! Reduction of the Darmon-Granville theorem
(`FermatCatalanConjecture.fermat_catalan.variants.darmon_granville`) to the case where all
three exponents are at least 3 (`H1`) and the case where at least one exponent equals 2 and
all are at least 2 (`H2`). In `main`, we prove directly from `1/m + 1/n + 1/k < 1` and
positivity that `2 <= m`, `2 <= n`, and `2 <= k`. -/

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1

/-- Darmon-Granville when all three exponents are at least 3 and `1/m + 1/n + 1/k < 1`. -/
def H1 : Prop :=
  ∀ m n k : ℕ, 3 ≤ m → 3 ≤ n → 3 ≤ k → (1 / m : ℝ) + 1 / n + 1 / k < 1 →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ m + b ^ n = c ^ k ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime}.Finite

/-- Darmon-Granville when all exponents are at least 2, at least one exponent equals 2, and
`1/m + 1/n + 1/k < 1`. -/
def H2 : Prop :=
  ∀ m n k : ℕ, 2 ≤ m → 2 ≤ n → 2 ≤ k → (m = 2 ∨ n = 2 ∨ k = 2) →
    (1 / m : ℝ) + 1 / n + 1 / k < 1 →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ m + b ^ n = c ^ k ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime}.Finite

theorem main : H1 → H2 →
    type_of% @FermatCatalanConjecture.fermat_catalan.variants.darmon_granville := by
  intro h1 h2 m n k hm hn hk H
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    have h1n : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 hn_pos
    have h1k : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 hk_pos
    norm_num at H
    linarith
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    have h1m : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 hm_pos
    have h1k : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 hk_pos
    norm_num at H
    linarith
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    subst hk1
    have h1m : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 hm_pos
    have h1n : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 hn_pos
    norm_num at H
    linarith
  by_cases h2ex : m = 2 ∨ n = 2 ∨ k = 2
  · exact h2 m n k hm2 hn2 hk2 h2ex H
  · exact h1 m n k (by omega) (by omega) (by omega) H

end OMA.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1
