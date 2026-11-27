import OMAStatements.S_oeis_a007091
import Mathlib

namespace OMA.A007091Proof

open OMA.S_oeis_a007091

/-- Decimal digit sum. -/
def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- All decimal digits are at most four. -/
def P (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d ≤ 4

theorem S_rec (n : ℕ) : S n = n % 10 + S (n / 10) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [S]
  · unfold S
    rw [Nat.digits_def' (by norm_num) h, List.sum_cons]

theorem P_rec (n : ℕ) : P n ↔ n % 10 ≤ 4 ∧ P (n / 10) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [P]
  · unfold P
    rw [Nat.digits_def' (by norm_num) h]
    simp

theorem key (n : ℕ) : S (2 * n) ≤ 2 * S n ∧ (S (2 * n) = 2 * S n ↔ P n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [S, P]
    have hq : n / 10 < n := by omega
    obtain ⟨ih1, ih2⟩ := ih (n / 10) hq
    rw [S_rec (2 * n), S_rec n, P_rec n]
    by_cases hr : n % 10 ≤ 4
    · have e1 : 2 * n % 10 = 2 * (n % 10) := by omega
      have e2 : 2 * n / 10 = 2 * (n / 10) := by omega
      rw [e1, e2]
      constructor
      · omega
      · constructor
        · intro h
          exact ⟨hr, ih2.mp (by omega)⟩
        · intro h
          have := ih2.mpr h.2
          omega
    · have e1 : 2 * n % 10 = 2 * (n % 10) - 10 := by omega
      have e2 : 2 * n / 10 = 2 * (n / 10) + 1 := by omega
      have e3 : S (2 * (n / 10) + 1) = S (2 * (n / 10)) + 1 := by
        rw [S_rec (2 * (n / 10) + 1), S_rec (2 * (n / 10))]
        have f1 : (2 * (n / 10) + 1) % 10 = 2 * (n / 10) % 10 + 1 := by omega
        have f2 : (2 * (n / 10) + 1) / 10 = 2 * (n / 10) / 10 := by omega
        rw [f1, f2]
        omega
      rw [e1, e2, e3]
      constructor
      · omega
      · constructor
        · intro h
          omega
        · intro h
          exact absurd h.1 hr

theorem range_iff (n : ℕ) : (∃ m, a m = n) ↔ P n := by
  constructor
  · rintro ⟨m, rfl⟩
    unfold a P
    have hlt : ∀ l ∈ Nat.digits 5 m, l < 10 := by
      intro l hl
      have := Nat.digits_lt_base (by norm_num) hl
      omega
    have hlast : ∀ h : Nat.digits 5 m ≠ [], (Nat.digits 5 m).getLast h ≠ 0 :=
      fun h => Nat.getLast_digit_ne_zero 5 (by
        intro hm
        subst hm
        simp at h)
    rw [Nat.digits_ofDigits 10 (by norm_num) _ hlt hlast]
    intro d hd
    have := Nat.digits_lt_base (by norm_num) hd
    omega
  · intro hP
    refine ⟨Nat.ofDigits 5 (Nat.digits 10 n), ?_⟩
    unfold a
    have hlt : ∀ l ∈ Nat.digits 10 n, l < 5 := by
      intro l hl
      have := hP l hl
      omega
    have hlast : ∀ h : Nat.digits 10 n ≠ [], (Nat.digits 10 n).getLast h ≠ 0 :=
      fun h => Nat.getLast_digit_ne_zero 10 (by
        intro hm
        subst hm
        simp at h)
    rw [Nat.digits_ofDigits 5 (by norm_num) _ hlt hlast, Nat.ofDigits_digits]

end OMA.A007091Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007091.main := by
  intro n
  rw [OMA.A007091Proof.range_iff]
  have h := (OMA.A007091Proof.key n).2
  unfold OMA.A007091Proof.S at h
  rw [← h]
  omega
