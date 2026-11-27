import OMAReductions.R_Erdos470_erdos_470_parts_ii_R3

-- The divisor-sum and proper-divisor bounds adapt the R2.H1 proof by ivillar.
-- The subset decomposition comes from biondadave’s proof of the conditional prime-gap variant.
open Finset

namespace OMA.PrimitiveWeirdDivisors

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

-- A set of divisors of 2^k * p * q sums to A0 + p * B + q * C, where A0 is a
-- sum of distinct divisors of 2^k.
lemma decomp (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (t : Finset ℕ)
    (ht : t ⊆ (2 ^ k * p * q).divisors) :
    ∃ A0 B C : ℕ, ∑ d ∈ t, d = A0 + p * B + q * C ∧ A0 + 1 ≤ 2 ^ (k + 1) := by
  have e1 : ∑ d ∈ t.filter (fun d => p ∣ d), d = p * ∑ d ∈ t.filter (fun d => p ∣ d), d / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have e2 : ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d =
      q * ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have hsub : (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d) ⊆ (2 ^ k).divisors := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨⟨hdt, hnp⟩, hnq⟩ := hd
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    have hcp : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    have hcq : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnq).symm
    have h1 : d ∣ 2 ^ k * p := Nat.Coprime.dvd_of_dvd_mul_right hcq hdn
    have h2 : d ∣ 2 ^ k := Nat.Coprime.dvd_of_dvd_mul_right hcp h1
    exact Nat.mem_divisors.mpr ⟨h2, by positivity⟩
  refine ⟨∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d,
    ∑ d ∈ t.filter (fun d => p ∣ d), d / p,
    ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q, ?_, ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not t (fun d => p ∣ d),
      ← Finset.sum_filter_add_sum_filter_not (t.filter (fun d => ¬ p ∣ d)) (fun d => q ∣ d),
      e1, e2]
    ring
  · calc ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d + 1
        ≤ ∑ d ∈ (2 ^ k).divisors, d + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) 1
      _ = 2 ^ (k + 1) := sig_two_pow k

theorem sigma_lt_threshold {N p q : ℕ} (hN : 0 < N) (hp : N < p) :
    (N - 1) * (p + 1) * (q + 1) < N * p * q + N * p := by
  have hN' : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hl : (N - 1) * (p + 1) < N * p := by
    nlinarith only [hp, hN', congrArg (fun t => t * p) hN']
  calc
    _ < (N * p) * (q + 1) := Nat.mul_lt_mul_of_pos_right hl (by omega)
    _ = _ := by ring

end OMA.PrimitiveWeirdDivisors

open OMA.PrimitiveWeirdDivisors

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R3.H1 := by
  intro k p q hp hq hNp hNq hpq hAB hblock
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
    have hp_bound : A < N * p * q + N * p := sigma_lt_threshold (by omega) hNp
    have hq_bound : A < N * p * q + N * q := by
      simpa only [hA, mul_right_comm] using
        (sigma_lt_threshold (q := p) (by omega) hNq)
    have hsub : T ⊆ n.divisors := fun _ hd =>
      Nat.properDivisors_subset_divisors (Finset.sdiff_subset hd)
    obtain ⟨a, b, c, habc, ha⟩ := decomp k p q hp hq T hsub
    have hb : b < N := by
      by_contra! h
      have := Nat.mul_le_mul_left p h
      rw [mul_comm p N] at this
      omega
    have hc : c < N := by
      by_contra! h
      have := Nat.mul_le_mul_left q h
      rw [mul_comm q N] at this
      omega
    apply hblock b c hb hc
    rw [mul_comm b p, mul_comm c q]
    constructor <;> omega
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
