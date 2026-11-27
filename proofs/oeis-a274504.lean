import OMAStatements.S_oeis_a274504

lemma OMA.a274504_fact : (14 : ℕ).factorization 2 = 1 := by
  rw [show (14 : ℕ) = 2 ^ 1 * 7 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

lemma OMA.a274504_kron (n : ℕ) :
    OMA.S_oeis_a274504.kronecker n 14 =
      ZMod.χ₈ ((n % 56 : ℕ) : ZMod 8) * jacobiSym ((n % 56 : ℕ) : ℤ) 7 := by
  unfold OMA.S_oeis_a274504.kronecker
  rw [OMA.a274504_fact]
  norm_num
  congr 1
  · congr 1
    rw [ZMod.natCast_eq_natCast_iff']
    omega
  · apply jacobiSym.mod_left'
    push_cast
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a274504.main := by
  intro p _
  rw [OMA.a274504_kron]
  have hr : p % 56 < 56 := Nat.mod_lt _ (by norm_num)
  generalize p % 56 = r at hr ⊢
  interval_cases r <;> simp <;> norm_num
