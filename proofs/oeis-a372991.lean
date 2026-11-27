import OMAStatements.S_oeis_a372991
import Mathlib

namespace A372991

open OMA.S_oeis_a372991 in
lemma pos (n : ℕ) : 0 < a n ∧ 0 < a (n + 1) := by
  induction n with
  | zero => constructor <;> simp [a]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [a]
    exact div_pos (by positivity) (mul_pos ih.2 ih.1)

open OMA.S_oeis_a372991 in
lemma prod (n : ℕ) : a (n + 2) * (a (n + 1) * a n) = ((2 * (n + 2)).factorial : ℚ) := by
  have h := pos n
  have h1 : a (n + 1) * a n ≠ 0 := (mul_pos h.2 h.1).ne'
  rw [a, div_mul_cancel₀ _ h1]

end A372991

theorem OMA.solution : type_of% @OMA.S_oeis_a372991.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : OMA.S_oeis_a372991.a (m + 3) *
      (OMA.S_oeis_a372991.a (m + 2) * OMA.S_oeis_a372991.a (m + 1)) =
      ((2 * (m + 3)).factorial : ℚ) := A372991.prod (m + 1)
  have h2 := A372991.prod m
  have hF : ((2 * (m + 3)).factorial : ℚ) =
      (2 * (m : ℚ) + 6) * (2 * (m : ℚ) + 5) * ((2 * (m + 2)).factorial : ℚ) := by
    rw [show 2 * (m + 3) = 2 * (m + 2) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hFpos : (0 : ℚ) < ((2 * (m + 2)).factorial : ℚ) := by positivity
  rw [Nat.add_sub_cancel]
  have key : OMA.S_oeis_a372991.a (m + 3) * ((2 * (m + 2)).factorial : ℚ) =
      (2 * (m : ℚ) + 6) * (2 * (m : ℚ) + 5) * OMA.S_oeis_a372991.a m *
        ((2 * (m + 2)).factorial : ℚ) := by
    calc OMA.S_oeis_a372991.a (m + 3) * ((2 * (m + 2)).factorial : ℚ)
        = OMA.S_oeis_a372991.a (m + 3) *
            (OMA.S_oeis_a372991.a (m + 2) * OMA.S_oeis_a372991.a (m + 1)) *
            OMA.S_oeis_a372991.a m := by rw [← h2]; ring
      _ = ((2 * (m + 3)).factorial : ℚ) * OMA.S_oeis_a372991.a m := by rw [h1]
      _ = _ := by rw [hF]; ring
  have h3 := mul_right_cancel₀ hFpos.ne' key
  rw [h3]
  push_cast
  ring
