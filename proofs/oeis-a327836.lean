import OMAStatements.S_oeis_a327836
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a327836.main := by
  intro n hn
  unfold OMA.S_oeis_a327836.a
  apply Nat.sInf_le
  show OMA.S_oeis_a327836.Good n (2 * (n + 1) ^ n)
  refine ⟨by positivity, ?_⟩
  have h0 : (((n + 1 : ℕ) : ℤ)) ∣ ((n : ℤ) ^ 2) - 1 := ⟨(n : ℤ) - 1, by push_cast; ring⟩
  have h1 := dvd_sub_pow_of_dvd_sub h0 n
  rw [one_pow, ← pow_mul] at h1
  have h2 : (((n + 1) ^ (n + 1) : ℕ) : ℤ) ∣ ((n ^ (2 * (n + 1) ^ n) : ℕ) : ℤ) - ((1 : ℕ) : ℤ) := by
    push_cast
    push_cast at h1
    exact h1
  exact (Nat.modEq_iff_dvd.mpr h2).symm
