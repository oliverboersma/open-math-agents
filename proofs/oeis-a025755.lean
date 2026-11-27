import OMAStatements.S_oeis_a025755
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a025755.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h2 : OMA.S_oeis_a025755.a (m + 2) =
      (100 : ℚ) ^ (m + 1) * (ascPochhammer ℚ (m + 1)).eval (9 / 10)
        / ((m + 1 + 1).factorial : ℚ) := rfl
  have h1 : OMA.S_oeis_a025755.a (m + 1) =
      (100 : ℚ) ^ m * (ascPochhammer ℚ m).eval (9 / 10) / ((m + 1).factorial : ℚ) := rfl
  rw [show m + 2 - 1 = m + 1 by omega, h2, h1, ascPochhammer_succ_eval,
    Nat.factorial_succ (m + 1)]
  have hf : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
