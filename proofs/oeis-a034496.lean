import OMAStatements.S_oeis_a034496
import Mathlib

/-!
# Proof of OEIS A034496 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a034496.main := by
  intro n
  have hdiv : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  have hfactor : OMA.S_oeis_a034496.a n = (1 + 2 ^ n) * (1 + 4 ^ n) := by
    calc
      OMA.S_oeis_a034496.a n = 1 + 2 ^ n + 4 ^ n + 8 ^ n := by
        rw [OMA.S_oeis_a034496.a, hdiv]
        simp
        ring
      _ = (1 + 2 ^ n) * (1 + 4 ^ n) := by
        rw [show (8 : ℕ) = 2 * 4 by decide, mul_pow]
        ring
  rw [hfactor, Nat.prime_mul_iff]
  have h₂ : 0 < (2 : ℕ) ^ n := by positivity
  have h₄ : 0 < (4 : ℕ) ^ n := by positivity
  omega
