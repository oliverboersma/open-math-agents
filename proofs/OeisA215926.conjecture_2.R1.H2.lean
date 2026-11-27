import OMAReductions.R_OeisA215926_conjecture_2_R1

-- Step OeisA215926.conjecture_2.R1.H2
-- Credit: @caa1982

private lemma sum_divisors_two_pow (j : ℕ) :
    ∑ d ∈ (2 ^ j).divisors, d = 2 ^ (j + 1) - 1 := by
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    rw [pow_succ, pow_succ]
    omega

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hqlt
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (Nat.pow_pos (by decide)) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  have hcop : (2 ^ j).Coprime q :=
    ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left j
  have hsum : ∑ d ∈ (2 ^ j * q).divisors, d = (2 ^ (j + 1) - 1) * (q + 1) := by
    rw [hcop.sum_divisors_mul, sum_divisors_two_pow, hq.divisors,
        Finset.sum_pair hq.ne_one.symm, add_comm 1 q]
  have hge : 2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
    rw [hsum]
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    zify [h1]
    nlinarith
  omega
