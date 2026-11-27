import OMAStatements.S_oeis_a071010
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
The two-square criterion gives a prime congruent to 3 modulo 4
with odd exponent. Pair consecutive terms of its geometric divisor
sum to see that this factor of sigma is divisible by four.
-/
-- Credit: @dk8827

namespace OMA.A071010

open Finset ArithmeticFunction

private theorem paired_sum (p r : ℕ) (hp : 4 ∣ p + 1) :
    4 ∣ ∑ i ∈ range (2 * r), p ^ i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega, sum_range_succ, sum_range_succ, add_assoc]
    rw [show p ^ (2 * r) + p ^ (2 * r + 1) = (p + 1) * p ^ (2 * r) by
      rw [pow_succ]
      ring]
    exact dvd_add ih (dvd_mul_of_dvd_left hp _)

theorem solution_aux (n : ℕ) (hn : ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2) :
    4 ∣ sigma 1 n := by
  have h0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, 0, by norm_num⟩
  have hex : ∃ p ∈ n.primeFactors, p % 4 = 3 ∧ ¬ Even (padicValNat p n) := by
    by_contra! h
    exact hn (Nat.eq_sq_add_sq_iff.mpr h)
  obtain ⟨p, hp, hp4, he⟩ := hex
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hodd : Odd (n.factorization p) := by
    rw [Nat.factorization_def n hprime]
    exact (Nat.even_or_odd _).resolve_left he
  obtain ⟨r, hr⟩ := hodd
  have hlength : n.factorization p + 1 = 2 * (r + 1) := by omega
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul h0]
  simp only [mul_one]
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun q => ∑ i ∈ range (n.factorization q + 1), q ^ i) hp)
  rw [hlength]
  exact paired_sum p (r + 1) (by omega)

end OMA.A071010

theorem OMA.solution : type_of% @OMA.S_oeis_a071010.main := OMA.A071010.solution_aux
