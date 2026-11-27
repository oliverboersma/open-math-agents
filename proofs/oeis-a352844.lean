import OMAStatements.S_oeis_a352844
import Mathlib

/-!
# Proof of OEIS A352844 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a352844.main := by
  intro n
  refine ⟨2 ^ (n + 1), one_lt_pow₀ (by decide : (1 : ℕ) < 2) (Nat.succ_ne_zero n), ?_⟩
  have hs : OMA.S_oeis_a352844.sopfr (2 ^ (n + 1)) = 2 * (n + 1) := by
    simp only [OMA.S_oeis_a352844.sopfr,
      Nat.primeFactors_prime_pow (Nat.succ_ne_zero n) Nat.prime_two,
      Finset.sum_singleton, Nat.factorization_pow_self Nat.prime_two]
  have hd : (2 ^ (n + 1) : ℕ).divisors.card = n + 2 := by
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  rw [hs, hd]
  omega
