import OMAStatements.S_oeis_a003435
import Mathlib

namespace A003435

open OMA.S_oeis_a003435 in
lemma rec4 (k : ℕ) :
    (2 * ((k : ℚ) + 4) - 3) * a (k + 4) =
      2 * ((k : ℚ) + 4) * (4 * ((k : ℚ) + 4) ^ 2 - 8 * ((k : ℚ) + 4) + 5) * a (k + 3) +
        4 * ((k : ℚ) + 4 - 1) * ((k : ℚ) + 4) * (2 * ((k : ℚ) + 4) - 1) * a (k + 2) := by
  have hne : (2 * ((k : ℚ) + 4) - 3) ≠ 0 := by
    have : (0 : ℚ) ≤ (k : ℚ) := by positivity
    intro h; linarith
  have e : a (k + 4) =
      (2 * ((k : ℚ) + 4) * (4 * ((k : ℚ) + 4) ^ 2 - 8 * ((k : ℚ) + 4) + 5) * a (k + 3) +
        4 * ((k : ℚ) + 4 - 1) * ((k : ℚ) + 4) * (2 * ((k : ℚ) + 4) - 1) * a (k + 2)) /
        (2 * ((k : ℚ) + 4) - 3) := by
    rw [a]
  rw [e, mul_div_cancel₀ _ hne]

end A003435

theorem OMA.solution : type_of% @OMA.S_oeis_a003435.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h1 := A003435.rec4 (m + 1)
  have h2 := A003435.rec4 m
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  rw [show m + 1 + 4 = m + 5 from rfl, show m + 1 + 3 = m + 4 from rfl,
    show m + 1 + 2 = m + 3 from rfl] at h1
  push_cast at h1 h2 ⊢
  have hne : (2 * ((m : ℚ) + 5) - 3) ≠ 0 := by
    have : (0 : ℚ) ≤ (m : ℚ) := by positivity
    intro h; linarith
  have key : (2 * ((m : ℚ) + 5) - 3) *
      (OMA.S_oeis_a003435.a (m + 5) -
        (4 * ((m : ℚ) + 5) ^ 2 - 2 * ((m : ℚ) + 5) + 5) * OMA.S_oeis_a003435.a (m + 4) +
        2 * ((m : ℚ) + 5 - 1) * (4 * ((m : ℚ) + 5) - 17) * OMA.S_oeis_a003435.a (m + 3) +
        12 * ((m : ℚ) + 5 - 1) * ((m : ℚ) + 5 - 2) * OMA.S_oeis_a003435.a (m + 2)) = 0 := by
    linear_combination h1 - 3 * h2
  exact (mul_eq_zero.mp key).resolve_left hne
