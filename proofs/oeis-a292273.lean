import OMAStatements.S_oeis_a292273

-- Problem: oeis-a292273
-- Credit: @anmolspace
-- Proof: write n = 4q + r. I^(4q) = 1, so Re(μ(n) I^n) is μ(n), 0, -μ(n), 0 for r = 0, 1, 2, 3.
-- For r = 0, 4 ∣ n so n is not squarefree and μ(n) = 0; r odd gives 0; r = 2 gives -μ(n).

theorem OMA.solution : type_of% @OMA.S_oeis_a292273.main := by
  intro n hn
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hI : Complex.I ^ (4 * q) = 1 := by
    rw [show 4 * q = 2 * (2 * q) by ring, pow_mul, Complex.I_sq, pow_mul, neg_one_sq, one_pow]
  rw [pow_add, hI, one_mul]
  interval_cases r
  · have hmu : ArithmeticFunction.moebius (4 * q) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have h2 := hsq 2 ⟨q, by ring⟩
      exact absurd (Nat.isUnit_iff.mp h2) (by norm_num)
    simp [OMA.S_oeis_a292273.a, hmu]
  · have hodd : Odd (4 * q + 1) := ⟨2 * q, by ring⟩
    simp [OMA.S_oeis_a292273.a, hodd, Complex.mul_re]
  · have hev : ¬ Odd (4 * q + 2) := by
      rintro ⟨k, hk⟩
      omega
    simp [OMA.S_oeis_a292273.a, hev, Complex.mul_re, pow_two]
  · have hodd : Odd (4 * q + 3) := ⟨2 * q + 1, by ring⟩
    simp [OMA.S_oeis_a292273.a, hodd, Complex.mul_re, pow_succ, pow_two]
