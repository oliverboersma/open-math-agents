import OMAStatements.S_oeis_a203159
import Mathlib

open OMA.S_oeis_a203159

lemma OMA.pr (n : ℕ) : products (n + 1) =
    ((products n).1 * (2 * ((n : ℤ) + 1)), (products n).2 * (2 * ((n : ℤ) + 1)) + (products n).1) := rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a203159.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [a]
  rw [OMA.pr (m + 1), OMA.pr m]
  simp only
  push_cast
  ring
