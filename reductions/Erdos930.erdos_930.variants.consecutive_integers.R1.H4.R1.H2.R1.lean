import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1
import Mathlib

/-! The explicit prime-counting estimate splits at the threshold of Dusart's inequality.
From 60184 on it is weaker than Dusart, Inégalités explicites pour psi(X), theta(X), pi(X)
et les nombres premiers, C. R. Math. Acad. Sci. Soc. R. Can. 21 (1999), Théorème 1.10:
pi(x) is at most x / (log x - 1.1) for x at least 60184. Below the threshold it is a finite
statement about the 30184 integers from 30000 to 60183, which can be certified by counting
primes and bounding logarithms on a geometric grid. -/

namespace OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1

/-- Dusart's upper bound for the prime counting function, at integers. -/
def H1 : Prop := ∀ k : ℕ, 60184 ≤ k →
  (k.primeCounting : ℝ) * (Real.log k - 11/10) ≤ k

/-- The finite range below Dusart's threshold. -/
def H2 : Prop := ∀ k : ℕ, 30000 ≤ k → k < 60184 →
  (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k

theorem main : H1 → H2 →
    OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1.H2 := by
  intro dusart finite k hk
  by_cases hlt : k < 60184
  · exact finite k hk hlt
  · have hk' : 60184 ≤ k := not_lt.1 hlt
    have h := dusart k hk'
    have hkr : (60184:ℝ) ≤ k := by exact_mod_cast hk'
    have h0 : Nat.primeCounting' k ≤ Nat.primeCounting k :=
      Nat.monotone_primeCounting' (Nat.le_succ k)
    have hcard : (k.primesBelow.card : ℝ) ≤ (k.primeCounting : ℝ) := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      exact_mod_cast h0
    have hlog : (6/5 : ℝ) ≤ Real.log k := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have h2 : Real.exp (6/5) ≤ Real.exp (1 + 1) := Real.exp_le_exp.2 (by norm_num)
      rw [Real.exp_add] at h2
      have h3 := Real.exp_one_lt_d9
      have h4 := Real.exp_pos 1
      have h5 := mul_lt_mul'' h3 h3 h4.le h4.le
      linarith
    calc (k.primesBelow.card : ℝ) * (Real.log k - 6/5)
        ≤ (k.primeCounting : ℝ) * (Real.log k - 6/5) :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
      _ ≤ (k.primeCounting : ℝ) * (Real.log k - 11/10) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ k := h

end OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1
