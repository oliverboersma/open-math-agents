import OMAStatements.S_oeis_a336838
import Mathlib

-- Problem: A336838 (oeis-a336838): for consecutive primes p < q and odd e, (q+1)/2 divides the
-- reduced numerator of the mean of the divisors of q^e.
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: write e + 1 = 2M. The divisor sum of q^e is (q+1) * T with T = sum_{i<M} q^(2i),
-- and there are 2M divisors, so the mean is k * (T / M) with k = (q+1)/2 (q is odd since q > p >= 2).
-- It suffices that k is coprime to the reduced denominator of T / M. If a prime r divides k, then
-- q^2 = 1 mod r, and a geometric-sum lemma (sum_{i<m} x^i is divisible by r^j whenever x = 1 mod r
-- and r^j divides m, by splitting m = r * m') gives r^a | T for r^a the exact power of r in M.
-- Cancelling r^a, the denominator divides the r-free part of M, so r does not divide it.
-- Finally k * y has numerator divisible by k when k is coprime to the denominator of y.

namespace OMAProof336838

theorem geom_split (x a : ℕ) : ∀ b : ℕ,
    ∑ i ∈ Finset.range (a * b), x ^ i = (∑ i ∈ Finset.range a, x ^ i) * ∑ i ∈ Finset.range b, (x ^ a) ^ i
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, geom_split x a b, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add, ← pow_mul]
    ring

theorem dvd_sum_of_modEq (r x : ℕ) (hx : x ≡ 1 [MOD r]) : r ∣ ∑ i ∈ Finset.range r, x ^ i := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have h1 : (x : ZMod r) = 1 := by
    rw [← Nat.cast_one]; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx
  push_cast
  simp [h1]

theorem pow_dvd_geom (r : ℕ) : ∀ j m x : ℕ, x ≡ 1 [MOD r] → r ^ j ∣ m →
    r ^ j ∣ ∑ i ∈ Finset.range m, x ^ i
  | 0, _, _, _, _ => by simp
  | j + 1, m, x, hx, hm => by
    obtain ⟨c, rfl⟩ := hm
    have hsplit : r ^ (j + 1) * c = r * (r ^ j * c) := by ring
    rw [hsplit, geom_split, pow_succ', ]
    apply mul_dvd_mul (dvd_sum_of_modEq r x hx)
    apply pow_dvd_geom r j (r ^ j * c) (x ^ r)
    · simpa using hx.pow r
    · exact dvd_mul_right _ _

theorem num_dvd (k : ℕ) (y : ℚ) (h : Nat.Coprime k y.den) : (k : ℤ) ∣ ((k : ℚ) * y).num := by
  set z := (k : ℚ) * y with hz
  have e1 : (z.num : ℚ) * y.den = k * y.num * z.den := by
    have a1 := Rat.mul_den_eq_num z
    have a2 := Rat.mul_den_eq_num y
    rw [← a1, ← a2, hz]; ring
  have e2 : z.num * (y.den : ℤ) = k * y.num * z.den := by exact_mod_cast e1
  have hc : IsCoprime (k : ℤ) (y.den : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  exact hc.dvd_of_dvd_mul_right ⟨y.num * z.den, by rw [e2]; ring⟩

theorem den_dvd_nat (t c : ℕ) : ((t : ℚ) / (c : ℚ)).den ∣ c := by
  have h := Rat.den_dvd (t : ℤ) (c : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  exact_mod_cast h


theorem sq_modEq_one (q r : ℕ) (hq : 1 ≤ q) (h : r ∣ q + 1) : q ^ 2 ≡ 1 [MOD r] := by
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).mpr
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have : (q' + 1) ^ 2 - 1 = (q' + 1 + 1) * q' := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [this]
  exact Dvd.dvd.mul_right h _

theorem coprime_den (q k M : ℕ) (hq : 1 ≤ q) (hk : q + 1 = 2 * k) (hM : M ≠ 0) :
    Nat.Coprime k (((∑ i ∈ Finset.range M, (q ^ 2) ^ i : ℕ) : ℚ) / (M : ℚ)).den := by
  apply Nat.coprime_of_dvd
  intro r hr hrk hrden
  set T := ∑ i ∈ Finset.range M, (q ^ 2) ^ i with hT
  have hmod : q ^ 2 ≡ 1 [MOD r] :=
    sq_modEq_one q r hq (by rw [hk]; exact Dvd.dvd.mul_left hrk 2)
  have hTd : r ^ M.factorization r ∣ T := pow_dvd_geom r _ M (q ^ 2) hmod (Nat.ordProj_dvd M r)
  obtain ⟨t, ht⟩ := hTd
  set c := M / r ^ M.factorization r with hc
  have hMc : M = r ^ M.factorization r * c := (Nat.ordProj_mul_ordCompl_eq_self M r).symm
  have hpos : (r : ℚ) ^ M.factorization r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne_zero)
  have hc0 : c ≠ 0 := by
    intro h0; apply hM; rw [hMc, h0, mul_zero]
  have hy : ((T : ℕ) : ℚ) / (M : ℚ) = (t : ℚ) / (c : ℚ) := by
    have hc0' : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM
    rw [div_eq_div_iff hM0 hc0']
    have : T * c = t * M := by
      rw [ht]; nth_rewrite 2 [hMc]; ring
    exact_mod_cast this
  rw [hy] at hrden
  have h1 := dvd_trans hrden (den_dvd_nat t c)
  exact Nat.not_dvd_ordCompl hr hM h1

theorem solution : type_of% @OMA.S_oeis_a336838.main := by
  intro p q e hp hq hpq _ he
  obtain ⟨m, rfl⟩ := he
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, q + 1 = 2 * k := ⟨(q + 1) / 2, by omega⟩
  have hkdef : (q + 1) / 2 = k := by omega
  rw [hkdef]
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hsum : ∑ d ∈ (q ^ (2 * m + 1)).divisors, d =
      (q + 1) * ∑ i ∈ Finset.range (m + 1), (q ^ 2) ^ i := by
    rw [Nat.sum_divisors_prime_pow hq]
    have : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [this, geom_split]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
  have hcard : (q ^ (2 * m + 1)).divisors.card = 2 * (m + 1) := by
    rw [Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]; ring
  have hmean : OMA.S_oeis_a336838.divisorMean (q ^ (2 * m + 1)) =
      (k : ℚ) * (((∑ i ∈ Finset.range (m + 1), (q ^ 2) ^ i : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ)) := by
    unfold OMA.S_oeis_a336838.divisorMean
    rw [hsum, hcard, hk]
    generalize (∑ i ∈ Finset.range (m + 1), (q ^ 2) ^ i) = T
    push_cast
    field_simp
  rw [hmean]
  have h := num_dvd k _ (coprime_den q k (m + 1) hq1 hk (by omega))
  have h2 := Int.natAbs_dvd_natAbs.mpr h
  simpa using h2

end OMAProof336838

theorem OMA.solution : type_of% @OMA.S_oeis_a336838.main := OMAProof336838.solution
