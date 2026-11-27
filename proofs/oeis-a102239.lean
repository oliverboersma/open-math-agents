import OMAStatements.S_oeis_a102239
import Mathlib.Tactic

/-!
The geometric sum satisfies s(n+1) = 5*s(n)+1, so its parity alternates.
The parity correction then gives the asserted second-order recurrence.
-/
-- Credit: @dk8827

namespace OMA.A102239

open OMA.S_oeis_a102239

private theorem sum_succ (n : ℕ) : s (n + 1) = 1 + 5 * s n := by
  unfold s
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ', Nat.add_comm]

private theorem parity_succ (n : ℕ) : s (n + 1) % 2 = 1 - s n % 2 := by
  rw [sum_succ, Nat.add_mod 1 (5 * s n) 2, Nat.mul_mod 5 (s n) 2]
  have h : s n % 2 = 0 ∨ s n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private theorem cast_value (n : ℕ) :
    (a n : ℤ) = (s n : ℤ) + 1 - ((s n % 2 : ℕ) : ℤ) := by
  have hle : s n % 2 ≤ s n + 1 := (Nat.mod_le _ _).trans (Nat.le_succ _)
  simp [a, Int.ofNat_sub hle]

theorem solution_aux (n : ℕ) :
    (a (n + 2) : ℤ) = 4 * (a (n + 1) : ℤ) + 5 * (a n : ℤ) - 2 := by
  have h0 : (s (n + 1) : ℤ) = 1 + 5 * (s n : ℤ) := by exact_mod_cast sum_succ n
  have h1 : (s (n + 2) : ℤ) = 1 + 5 * (s (n + 1) : ℤ) := by exact_mod_cast sum_succ (n + 1)
  have hp0 := parity_succ n
  have hp1 : s (n + 2) % 2 = 1 - s (n + 1) % 2 := parity_succ (n + 1)
  have hp2 : s (n + 2) % 2 = s n % 2 := by omega
  simp only [cast_value, hp2, hp0, Int.ofNat_sub (show s n % 2 ≤ 1 by omega), Nat.cast_one]
  linarith

end OMA.A102239

theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := OMA.A102239.solution_aux
