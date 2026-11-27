import OMAStatements.S_oeis_a346644

-- Problem: A346644: Least k >= 1 such that sigma(k)/tau(k) has denominator n or zero if no k exists.
-- Upstream: formal-conjectures statements/oeis-a346644.lean:0 (declaration OMA.S_oeis_a346644.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Construction. Write n = 2^v * u with u odd, G = 2^(2^v) - 1 and M = u * G, which is odd.
By Dirichlet's theorem there is a prime p with p = -1 mod 2 * M. Take
k = 2^(2^v - 1) * p^(M - 1). Then tau(k) = 2^v * M = n * G and sigma(k) = G * S with
S = 1 + p + ... + p^(M - 1). Modulo 2 * M the sum S is an alternating sum of an odd number
of terms, so S = 1 mod 2 * M and S is coprime to n. Hence sigma(k) / tau(k) = S / n in
lowest terms.
-/

theorem a346644_alt_sum (R : Type) [CommRing R] (t : ℕ) :
    ∑ j ∈ Finset.range (2 * t + 1), (-1 : R) ^ j = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : (-1 : R) ^ (2 * t + 1) = -1 := Odd.neg_one_pow ⟨t, rfl⟩
    have h2 : (-1 : R) ^ (2 * t + 1 + 1) = 1 := Even.neg_one_pow ⟨t + 1, by ring⟩
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, h2]
    ring

theorem a346644_two_geom (m : ℕ) : ∑ j ∈ Finset.range m, 2 ^ j = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Finset.sum_range_succ, ih, pow_succ]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a346644.main := by
  intro n hn
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hv1 : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  have hpow : 2 ≤ 2 ^ (2 ^ v) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ v) := Nat.pow_le_pow_right (by norm_num) hv1
  obtain ⟨G, hG⟩ : ∃ G, G + 1 = 2 ^ (2 ^ v) := ⟨2 ^ (2 ^ v) - 1, by omega⟩
  have hGpos : 0 < G := by omega
  have hGodd : Odd G := by
    have he : Even (2 ^ (2 ^ v)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    rw [← hG] at he
    rcases Nat.even_or_odd G with h | h
    · exact absurd he (by simpa using h.add_one)
    · exact h
  obtain ⟨M, hM⟩ : ∃ M, M = u * G := ⟨_, rfl⟩
  have hModd : Odd M := hM ▸ hu.mul hGodd
  have hMpos : 0 < M := hModd.pos
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 2 * M := ⟨2 * M - 1, by omega⟩
  have hcop : Nat.Coprime a (2 * M) := by
    rw [← ha]; simp
  obtain ⟨p, -, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 2 (q := 2 * M) (a := a) (by omega) hcop
  have hp2 : p % 2 = 1 := by
    have h := hpmod.of_mul_right M
    unfold Nat.ModEq at h
    omega
  have hpz : ((p : ℕ) : ZMod (2 * M)) = -1 := by
    rw [(ZMod.natCast_eq_natCast_iff p a (2 * M)).2 hpmod]
    have h1 : ((a + 1 : ℕ) : ZMod (2 * M)) = 0 := by
      rw [ha]; exact ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h1
    exact eq_neg_of_add_eq_zero_left h1
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ Finset.range M, p ^ j := ⟨_, rfl⟩
  have hS1 : ((S : ℕ) : ZMod (2 * M)) = 1 := by
    rw [hS]
    push_cast
    rw [hpz]
    obtain ⟨t, ht⟩ := hModd
    rw [ht]
    exact a346644_alt_sum _ t
  have hScop : Nat.Coprime S (2 * M) := by
    rw [← ZMod.isUnit_iff_coprime, hS1]
    exact isUnit_one
  have hScopn : Nat.Coprime S (2 ^ v * u) := by
    have h2 : Nat.Coprime S 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M) hScop
    have hu' : Nat.Coprime S u :=
      Nat.Coprime.coprime_dvd_right ⟨2 * G, by rw [hM]; ring⟩ hScop
    exact Nat.Coprime.mul_right (h2.pow_right v) hu'
  have hcopk : Nat.Coprime (2 ^ (2 ^ v - 1)) (p ^ (M - 1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have hk : 0 < 2 ^ (2 ^ v - 1) * p ^ (M - 1) := by
    have := hp.pos
    positivity
  have hcard : (2 ^ (2 ^ v - 1) * p ^ (M - 1)).divisors.card = 2 ^ v * M := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopk,
      ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      Nat.sub_add_cancel hv1, Nat.sub_add_cancel hMpos]
  have hsum : ∑ d ∈ (2 ^ (2 ^ v - 1) * p ^ (M - 1)).divisors, d = G * S := by
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopk,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_one_apply_prime_pow hp,
      Nat.sub_add_cancel hv1, Nat.sub_add_cancel hMpos, a346644_two_geom, ← hS, ← hG]
    simp
  refine ⟨2 ^ (2 ^ v - 1) * p ^ (M - 1), hk, ?_⟩
  unfold OMA.S_oeis_a346644.divisorMean
  rw [hsum, hcard]
  have hq : ((G * S : ℕ) : ℚ) / ((2 ^ v * M : ℕ) : ℚ)
      = ((S : ℤ) : ℚ) / (((2 ^ v * u : ℕ) : ℤ) : ℚ) := by
    have hG0 : (G : ℚ) ≠ 0 := by exact_mod_cast hGpos.ne'
    have hn0 : ((2 : ℚ) ^ v * (u : ℚ)) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hM]
    push_cast
    field_simp
  rw [hq]
  have h := Rat.den_div_eq_of_coprime (a := (S : ℤ)) (b := ((2 ^ v * u : ℕ) : ℤ))
    (by exact_mod_cast hn)
    (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hScopn)
  exact_mod_cast h
