import OMAStatements.S_oeis_a196200

-- Credit: @anmolspace. Sándor's 2005 paper credits the witness 39270 to L. Tóth.

open OMA.S_oeis_a196200

private lemma psi_family (k : ℕ) : psi (39270 * 2 ^ k) = 124416 * 2 ^ k := by
  have hf : (39270 * 2 ^ k).primeFactors = (39270 : ℕ).primeFactors := by
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.primeFactors_mul (by decide) (by positivity), Nat.primeFactors_pow_succ]
      decide +kernel
  have hden : (∏ p ∈ (39270 : ℕ).primeFactors, p) = 39270 := by decide +kernel
  have hnum : (∏ p ∈ (39270 : ℕ).primeFactors, (p + 1)) = 124416 := by decide +kernel
  rw [psi, hf, hden, hnum, Nat.mul_div_cancel_left _ (by decide), Nat.mul_comm]

private lemma totient_family (k : ℕ) : (124416 * 2 ^ k).totient = 41472 * 2 ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one]
    rw [show 124416 = 2 ^ (8 + 1) * 3 ^ (4 + 1) by decide,
      Nat.totient_mul (by decide), Nat.totient_prime_pow_succ (by decide),
      Nat.totient_prime_pow_succ (by decide)]
    decide
  | succ k ih =>
    have heven : Even (124416 * 2 ^ k) := (by decide : Even 124416).mul_right _
    rw [show 124416 * 2 ^ (k + 1) = 2 * (124416 * 2 ^ k) by rw [pow_succ]; ring,
      Nat.totient_two_mul_of_even heven, ih, pow_succ]
    ring

private lemma counterexamples (k : ℕ) :
    39270 * 2 ^ k < (psi (39270 * 2 ^ k)).totient := by
  rw [psi_family, totient_family]
  exact Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have hw : 39270 < (psi 39270).totient := by simpa using counterexamples 0
  exact (h 39270 (by decide)).not_gt hw
