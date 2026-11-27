import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

-- Step Erdos470.erdos_470.parts.ii.R2.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R2
-- Credit: @ivillar
-- Proof outline: sigma(n) = A > B = 2n gives abundance. If a set s of proper divisors summed to n,
-- its complement T would sum to A - B < q, so T avoids multiples of q and lies in the divisors of
-- 2^k p; its elements prime to p are divisors of 2^k (sum < 2^(k+1) < p), the rest are multiples
-- of p, so (A - B) % p < 2^(k+1), a contradiction. Every proper divisor 2^i p^a q^b is not abundant
-- by a direct bound on its divisor sum.

open Finset

namespace OMA.W3Erdos470R2H1

theorem sig_mul {m n : ℕ} (h : m.Coprime n) :
    (∑ i ∈ (m * n).divisors, i) = (∑ i ∈ m.divisors, i) * ∑ i ∈ n.divisors, i := by
  simp only [← ArithmeticFunction.sigma_one_apply]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

theorem sig_prime {p : ℕ} (hp : p.Prime) : (∑ i ∈ p.divisors, i) = p + 1 := by
  rw [hp.sum_divisors]

theorem sig_two_pow (i : ℕ) : (∑ x ∈ (2 ^ i).divisors, x) + 1 = 2 ^ (i + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction i with
  | zero => simp
  | succ j ih => rw [sum_range_succ, pow_succ 2 (j + 1)]; omega

theorem cop_two_pow {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (i : ℕ) : (2 ^ i).Coprime p :=
  Nat.Coprime.pow_left i ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))

theorem aux (s M K p q : ℕ) (hs : s + 1 = M) (hM : M ≤ K) (hp : 2 * K < p) (hq : 2 * K < q) :
    s * (p + 1) * (q + 1) ≤ M * p * q := by
  subst hs
  have h1 : 2 * K + 1 ≤ p := hp
  have h2 : 2 * K + 1 ≤ q := hq
  zify at *
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  have e2 := mul_le_mul_of_nonneg_right hM (show (0 : ℤ) ≤ p + q + 1 by positivity)
  nlinarith

theorem not_weird_of {d : ℕ} (h : 2 * d ≥ ∑ x ∈ d.divisors, x) : ¬ d.Weird := by
  rintro ⟨ha, -⟩
  rw [Nat.abundant_iff_sum_divisors] at ha
  omega

theorem key : ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
    (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q →
    2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p →
    Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  intro k p q hp hq hNp hNq hpq hAB hAq hmod
  set N := 2 ^ (k + 1) with hN
  have hK : N = 2 * 2 ^ k := by rw [hN, pow_succ]; ring
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2p : 2 < p := by omega
  have h2q : 2 < q := by omega
  have cp : (2 ^ k).Coprime p := cop_two_pow hp h2p k
  have cq : (2 ^ k * p).Coprime q :=
    Nat.Coprime.mul_left (cop_two_pow hq h2q k) ((Nat.coprime_primes hp hq).2 hpq)
  have s2k := sig_two_pow k
  -- sigma of n
  have hsig : (∑ i ∈ (2 ^ k * p * q).divisors, i) = (N - 1) * (p + 1) * (q + 1) := by
    rw [sig_mul cq, sig_mul cp, sig_prime hp, sig_prime hq]
    have : (∑ x ∈ (2 ^ k).divisors, x) = N - 1 := by omega
    rw [this]
  have hn0 : 2 ^ k * p * q ≠ 0 := by positivity
  have hB : N * p * q = 2 * (2 ^ k * p * q) := by rw [hK]; ring
  set A := (N - 1) * (p + 1) * (q + 1) with hA
  set n := 2 ^ k * p * q with hn
  have hpd : (∑ i ∈ n.properDivisors, i) + n = A := by
    rw [← hsig, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, hsig]
    omega
  · -- not pseudoperfect
    rintro ⟨-, s, hs, hsum⟩
    set T := n.properDivisors \ s with hT
    have hTs : (∑ i ∈ T, i) + n + n = A := by
      rw [← hpd, ← Finset.sum_sdiff hs, hsum]
    have hTq : ∀ d ∈ T, ¬ q ∣ d := by
      intro d hd hqd
      have hdn : d ∣ n := (Nat.mem_properDivisors.1 (Finset.sdiff_subset hd)).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)
      have h1 : d ≤ ∑ i ∈ T, i := Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) hd
      have h2 : q ≤ d := Nat.le_of_dvd hd0 hqd
      omega
    have hsplit := Finset.sum_filter_add_sum_filter_not T (fun d => p ∣ d) (fun i => i)
    have hdvd : p ∣ ∑ i ∈ T.filter (fun d => p ∣ d), i := Finset.dvd_sum (fun i hi => (Finset.mem_filter.1 hi).2)
    obtain ⟨y, hy⟩ := hdvd
    have hsub : T.filter (fun d => ¬ p ∣ d) ⊆ (2 ^ k).divisors := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdn : d ∣ n := (Nat.mem_properDivisors.1 (Finset.sdiff_subset hd.1)).1
      have c1 : d.Coprime q := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 (hTq d hd.1)))
      have c2 : d.Coprime p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd.2))
      have h3 : d ∣ 2 ^ k * p := c1.dvd_of_dvd_mul_right hdn
      have h4 : d ∣ 2 ^ k := c2.dvd_of_dvd_mul_right h3
      exact Nat.mem_divisors.2 ⟨h4, by positivity⟩
    have hle := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
    set x := ∑ i ∈ T.filter (fun d => ¬ p ∣ d), i with hx
    have hxN : x < N := by omega
    have hAB' : A - N * p * q = x + p * y := by omega
    rw [hAB', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  · -- proper divisors are not weird
    intro d hd
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨hdn, hdlt⟩ := hd
    obtain ⟨y, z, hy, hz, rfl⟩ := dvd_mul.1 hdn
    obtain ⟨u, v, hu, hv, rfl⟩ := dvd_mul.1 hy
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hu
    have si := sig_two_pow i
    have hMi : 2 ^ (i + 1) ≤ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hM2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    rcases (Nat.dvd_prime hp).1 hv with h1 | h1 <;> rcases (Nat.dvd_prime hq).1 hz with h2 | h2 <;>
      rw [h1, h2] at hdlt ⊢
    · apply not_weird_of
      simp only [mul_one]
      omega
    · apply not_weird_of
      rw [mul_one, sig_mul (cop_two_pow hq h2q i), sig_prime hq]
      set s := ∑ x ∈ (2 ^ i).divisors, x
      nlinarith
    · apply not_weird_of
      rw [mul_one, sig_mul (cop_two_pow hp h2p i), sig_prime hp]
      set s := ∑ x ∈ (2 ^ i).divisors, x
      nlinarith
    · apply not_weird_of
      have cpi : (2 ^ i * p).Coprime q :=
        Nat.Coprime.mul_left (cop_two_pow hq h2q i) ((Nat.coprime_primes hp hq).2 hpq)
      rw [sig_mul cpi, sig_mul (cop_two_pow hp h2p i), sig_prime hp, sig_prime hq]
      have hik : i < k := by
        rcases Nat.lt_or_ge i k with h | h
        · exact h
        · exfalso; have : i = k := by omega
          subst this; omega
      have hMk : 2 ^ (i + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := aux (∑ x ∈ (2 ^ i).divisors, x) (2 ^ (i + 1)) (2 ^ k) p q si hMk (by omega) (by omega)
      rw [hM2] at this
      linarith

end OMA.W3Erdos470R2H1

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := by
  unfold OMA.R_Erdos470_erdos_470_parts_ii_R2.H1
  exact OMA.W3Erdos470R2H1.key
