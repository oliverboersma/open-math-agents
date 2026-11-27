import OMAStatements.S_oeis_a179504

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a179504.main := by
  intro n hn
  obtain ⟨v, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.1 hn)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm.not_two_dvd_nat
  have hval : padicValNat 2 n = v := by
    rw [hnm, padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by simpa [Nat.dvd_prime Nat.prime_two] using hm.not_two_dvd_nat)]
    simp
  rw [hval]
  have h2n : 2 * n = 2 ^ (v + 1) * m := by rw [hnm]; ring
  have hmul : ∀ w : ℕ, sigma n (2 ^ w * m) = sigma n (2 ^ w) * sigma n m := fun w =>
    isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow_left _ hcop)
  have hs : ∀ w : ℕ, (sigma n (2 ^ w) : ℚ) = ∑ j ∈ Finset.range (w + 1), ((2 : ℚ) ^ n) ^ j := by
    intro w
    rw [sigma_apply_prime_pow Nat.prime_two]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm]
  have hX : (1 : ℚ) < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hgeom : (∑ j ∈ Finset.range (v + 1), ((2 : ℚ) ^ n) ^ j) * (2 ^ n - 1) = (2 ^ n) ^ (v + 1) - 1 :=
    geom_sum_mul _ _
  have hG : (0 : ℚ) < ∑ j ∈ Finset.range (v + 1), ((2 : ℚ) ^ n) ^ j :=
    Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩
  unfold OMA.S_oeis_a179504.a
  have e1 := hmul v
  rw [← hnm] at e1
  have e2 := hmul (v + 1)
  rw [← h2n] at e2
  rw [if_neg (by omega), e2, e1]
  push_cast
  rw [hs (v + 1), hs v, Finset.sum_range_succ _ (v + 1)]
  set G := ∑ j ∈ Finset.range (v + 1), ((2 : ℚ) ^ n) ^ j with hGdef
  set X : ℚ := 2 ^ n with hXdef
  have hden : (2 : ℚ) ^ (n * (v + 1)) - 1 = G * (X - 1) := by
    rw [hgeom, pow_mul]
  rw [hden]
  have hXm : X - 1 ≠ 0 := by linarith
  have hGm : G ≠ 0 := hG.ne'
  have e : X ^ (v + 1) = G * (X - 1) + 1 := by linarith
  rw [e]
  field_simp
  ring
