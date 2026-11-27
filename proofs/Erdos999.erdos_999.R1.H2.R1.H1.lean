import OMAReductions.R_Erdos999_erdos_999_R1_H2_R1

-- Step H1 of the reduction Erdos999.erdos_999.R1.H2.R1: the overlap estimate of Pollington and
-- Vaughan (Lemma 5.3 of Koukoulopoulos and Maynard) on the circle.
-- Contents: Mertens-type upper bounds from the Chebyshev bound, a sieve bound for integers
-- coprime to a modulus weighted by n / phi(n), a Chinese remainder count for pairs of reduced
-- fractions at a given distance, and the resulting bound for the measure of the intersection
-- of two approximation sets.

namespace DSM

open Finset

-- Mertens, first theorem (upper bound): the sum of log p / p over primes up to n.
lemma sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ p ∈ Nat.primesLE n, p.Prime ∧ p ≤ n := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range] at hp
    exact ⟨hp.2, by omega⟩
  have ha : ∑ k ∈ Ioc 0 n, Real.log k ≤ n * Real.log n := by
    calc ∑ k ∈ Ioc 0 n, Real.log k ≤ ∑ _k ∈ Ioc 0 n, Real.log n := by
          apply Finset.sum_le_sum
          intro k hk
          have hk0 : 0 < k := (mem_Ioc.1 hk).1
          have hkn : k ≤ n := (mem_Ioc.1 hk).2
          exact Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkn)
      _ = n * Real.log n := by simp
  have hb : ∀ k ∈ Ioc 0 n,
      ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) ≤ Real.log k := by
    intro k hk
    have hk0 : 0 < k := (mem_Ioc.1 hk).1
    have hkn : k ≤ n := (mem_Ioc.1 hk).2
    rw [← Finset.sum_filter]
    have hfe : (Nat.primesLE n).filter (fun p => p ∣ k) = k.primeFactors := by
      ext p
      simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨_, hp⟩, hd⟩
        exact ⟨hp, hd, hk0.ne'⟩
      · rintro ⟨hp, hd, _⟩
        have := Nat.le_of_dvd hk0 hd
        exact ⟨⟨by omega, hp⟩, hd⟩
    rw [hfe]
    have hd := Nat.le_of_dvd hk0 (Nat.prod_primeFactors_dvd k)
    have hpos : (0 : ℝ) < ∏ p ∈ k.primeFactors, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    calc ∑ p ∈ k.primeFactors, Real.log p = Real.log (∏ p ∈ k.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log k := by
          apply Real.log_le_log hpos
          have hcast : ((∏ p ∈ k.primeFactors, p : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hd
          push_cast at hcast
          exact hcast
  have hc : ∑ k ∈ Ioc 0 n, ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) =
      ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
      mul_comm]
  have hd : ∀ p ∈ Nat.primesLE n,
      Real.log p * ((n : ℝ) / p - 1) ≤ Real.log p * ((n / p : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := (hmem p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    have h1 : (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n p).symm
    have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hpp.pos
    have h3 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]
      nlinarith
    linarith
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p
      ≤ n * Real.log n := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p
        = ∑ p ∈ Nat.primesLE n, Real.log p * ((n : ℝ) / p - 1) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          ring
      _ ≤ ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) := Finset.sum_le_sum hd
      _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) := hc.symm
      _ ≤ ∑ k ∈ Ioc 0 n, Real.log k := Finset.sum_le_sum hb
      _ ≤ n * Real.log n := ha
  have hfin : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤
      n * (Real.log n + Real.log 4) := by
    rw [mul_add]
    linarith
  exact le_of_mul_le_mul_left hfin hnR

-- Sums over primes up to N as sums over a range, convenient for induction.
lemma primesLE_sum (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE N, f p = ∑ p ∈ range (N + 1), (if p.Prime then f p else 0) := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]

-- Mertens, second theorem (upper bound), by discrete partial summation.
lemma sum_inv_primes_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤
      Real.log (Real.log N) + (3 - Real.log (Real.log 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ M : ℕ, 2 ≤ M →
      ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p - (∑ p ∈ Nat.primesLE M, Real.log p / p) / Real.log M ≤
        Real.log (Real.log M) - Real.log (Real.log 2) +
          Real.log 4 * (1 / Real.log 2 - 1 / Real.log M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have h2 : Nat.primesLE 2 = {2} := by decide
      rw [h2]
      simp only [Finset.sum_singleton, Nat.cast_ofNat]
      have : Real.log 2 / 2 / Real.log 2 = 1 / 2 := by field_simp
      rw [this]
      norm_num
    | succ M hM ih =>
      have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have hL : 0 < Real.log M := Real.log_pos (by linarith)
      have hL1 : 0 < Real.log ((M + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
      have hLL : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by push_cast; linarith)
      have hA := sum_log_div_le M (by omega)
      have hS1 : ∑ p ∈ Nat.primesLE (M + 1), (1 : ℝ) / p =
          ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p +
            (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) := by
        rw [primesLE_sum, primesLE_sum, Finset.sum_range_succ]
      have hA1 : ∑ p ∈ Nat.primesLE (M + 1), Real.log p / p =
          ∑ p ∈ Nat.primesLE M, Real.log p / p +
            (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) := by
        rw [primesLE_sum, primesLE_sum, Finset.sum_range_succ]
      have hcancel : (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) /
            Real.log ((M + 1 : ℕ) : ℝ) = 0 := by
        split_ifs
        · field_simp
          ring
        · simp
      have hstep : (∑ p ∈ Nat.primesLE M, Real.log p / p) *
          (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
          (Real.log (Real.log ((M + 1 : ℕ) : ℝ)) - Real.log (Real.log M)) +
            Real.log 4 * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) := by
        have hd0 : 0 ≤ 1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ) := by
          rw [sub_nonneg]
          exact one_div_le_one_div_of_le hL hLL
        have h1 : (∑ p ∈ Nat.primesLE M, Real.log p / p) *
            (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
            (Real.log M + Real.log 4) * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hA hd0
        have h2 : Real.log M * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
            Real.log (Real.log ((M + 1 : ℕ) : ℝ)) - Real.log (Real.log M) := by
          have hx : 0 < Real.log ((M + 1 : ℕ) : ℝ) / Real.log M := div_pos hL1 hL
          have h3 := Real.one_sub_inv_le_log_of_pos hx
          rw [Real.log_div hL1.ne' hL.ne'] at h3
          have e : Real.log M * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) =
              1 - (Real.log ((M + 1 : ℕ) : ℝ) / Real.log M)⁻¹ := by
            field_simp
          rw [e]
          exact h3
        nlinarith
      rw [hS1, hA1]
      have e : ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p +
            (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (∑ p ∈ Nat.primesLE M, Real.log p / p +
            (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0)) /
            Real.log ((M + 1 : ℕ) : ℝ) =
          (∑ p ∈ Nat.primesLE M, (1 : ℝ) / p -
            (∑ p ∈ Nat.primesLE M, Real.log p / p) / Real.log M) +
          (∑ p ∈ Nat.primesLE M, Real.log p / p) *
            (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) +
          ((if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) /
            Real.log ((M + 1 : ℕ) : ℝ)) := by
        ring
      rw [e, hcancel]
      linarith
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hA := sum_log_div_le N (by omega)
  have hk := key N hN
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h5 : (∑ p ∈ Nat.primesLE N, Real.log p / p) / Real.log N ≤ 1 + Real.log 4 / Real.log N := by
    rw [div_le_iff₀ hL]
    have : (1 + Real.log 4 / Real.log N) * Real.log N = Real.log N + Real.log 4 := by
      field_simp
    rw [this]
    exact hA
  have h6 : Real.log 4 * (1 / Real.log 2 - 1 / Real.log N) = 2 - Real.log 4 / Real.log N := by
    rw [h4]
    field_simp
  linarith

-- Mertens, third theorem (upper bound): the product of (1 - 1/p)^(-1) over primes up to N.
lemma prod_primes_le (N : ℕ) (hN : 2 ≤ N) :
    ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (4 - Real.log (Real.log 2)) * Real.log N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hmem : ∀ p ∈ Nat.primesLE N, p.Prime := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range] at hp
    exact hp.2
  have hterm : ∀ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (1 / (p : ℝ) + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).two_le
    have e : (1 - 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have h : (1 - 1 / (p : ℝ)) * (1 / ((p : ℝ) - 1) + 1) = 1 := by
        rw [one_sub_div hp0, div_add_one hp1, div_mul_div_comm]
        rw [div_eq_one_iff_eq (mul_ne_zero hp0 hp1)]
        ring
      exact inv_eq_of_mul_eq_one_right h
    rw [e]
    have := Real.add_one_le_exp (1 / ((p : ℝ) - 1))
    calc 1 / ((p : ℝ) - 1) + 1 ≤ Real.exp (1 / ((p : ℝ) - 1)) := this
      _ = Real.exp (1 / (p : ℝ) + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by ring_nf
  have htel : ∑ p ∈ Nat.primesLE N, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤ 1 := by
    rw [primesLE_sum]
    have h1 : ∀ M : ℕ, ∑ p ∈ range (M + 2),
        (if p.Prime then (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) else 0) ≤ 1 - 1 / ((M : ℝ) + 1) := by
      intro M
      induction M with
      | zero =>
        have : ∑ p ∈ range (0 + 2),
            (if p.Prime then (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          have hp2 : p < 2 := by simpa using hp
          rw [if_neg]
          intro hpr
          have := hpr.two_le
          omega
        rw [this]
        norm_num
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        have hle : (if (M + 2).Prime then (1 / (((M + 2 : ℕ) : ℝ) - 1) - 1 / ((M + 2 : ℕ) : ℝ))
            else 0) ≤ 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 2) := by
          split_ifs
          · push_cast
            apply le_of_eq
            ring
          · rw [sub_nonneg]
            exact one_div_le_one_div_of_le (by linarith) (by linarith)
        push_cast at hle ⊢
        have e2 : (M : ℝ) + 1 + 1 = M + 2 := by ring
        rw [e2]
        linarith
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 := h1 M
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith
  calc ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))⁻¹
      ≤ ∏ p ∈ Nat.primesLE N, Real.exp (1 / (p : ℝ) + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).two_le
          have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one (by linarith)]
            linarith
          positivity
        · exact hterm
    _ = Real.exp (∑ p ∈ Nat.primesLE N, (1 / (p : ℝ) + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)))) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.log (Real.log N) + (4 - Real.log (Real.log 2))) := by
        apply Real.exp_le_exp.2
        rw [Finset.sum_add_distrib]
        linarith [sum_inv_primes_le N hN]
    _ = Real.exp (4 - Real.log (Real.log 2)) * Real.log N := by
        rw [Real.exp_add, Real.exp_log hL]
        ring


-- The weight n / phi(n), written as a product over the primes dividing n.
noncomputable def HH (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹

-- The sifted weight: n / phi(n) on integers coprime to m, zero elsewhere.
noncomputable def FF (m n : ℕ) : ℝ := if Nat.Coprime n m then HH n else 0

lemma inv_factor_bounds (p : ℕ) (hp : p.Prime) :
    1 ≤ (1 - 1 / (p : ℝ))⁻¹ ∧ (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have h0 : 0 < 1 / (p : ℝ) := by positivity
  have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
  constructor
  · rw [← one_div, le_div_iff₀ hpos]
    linarith
  · rw [← one_div, div_le_iff₀ hpos]
    linarith

lemma HH_pos (n : ℕ) : 0 < HH n :=
  Finset.prod_pos (fun p hp => by
    have := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors hp)).1
    linarith)

lemma HH_one : HH 1 = 1 := by simp [HH]

lemma HH_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) : HH (a * b) = HH a * HH b := by
  unfold HH
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

lemma HH_prime_pow_mul (p j k : ℕ) (hp : p.Prime) (hj : 0 < j) (hk : 0 < k) :
    HH (p ^ j * k) ≤ 2 * HH k := by
  have hk1 := HH_pos k
  unfold HH at hk1 ⊢
  rw [Nat.primeFactors_mul (pow_pos hp.pos j).ne' hk.ne', Nat.primeFactors_prime_pow hj.ne' hp]
  by_cases hpk : p ∈ k.primeFactors
  · rw [Finset.union_eq_right.2 (Finset.singleton_subset_iff.2 hpk)]
    linarith
  · rw [Finset.prod_union (Finset.disjoint_singleton_left.2 hpk), Finset.prod_singleton]
    exact mul_le_mul_of_nonneg_right (inv_factor_bounds p hp).2 hk1.le

lemma FF_nonneg (m n : ℕ) : 0 ≤ FF m n := by
  unfold FF
  split_ifs
  · exact (HH_pos n).le
  · exact le_rfl

lemma FF_prime_pow_mul (m p j k : ℕ) (hp : p.Prime) (hj : 0 < j) (hk : 0 < k) :
    FF m (p ^ j * k) ≤ 2 * FF m k := by
  unfold FF
  by_cases h : Nat.Coprime (p ^ j * k) m
  · have hk2 : Nat.Coprime k m := Nat.Coprime.coprime_mul_left h
    rw [if_pos h, if_pos hk2]
    exact HH_prime_pow_mul p j k hp hj hk
  · rw [if_neg h]
    have := FF_nonneg m k
    unfold FF at this
    linarith

-- The logarithm trick: the sum of the sifted weights times log x is controlled by the
-- logarithmic sum, through the Chebyshev bound for the von Mangoldt summatory function.
lemma log_trick (m x : ℕ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 x, FF m n) * Real.log x ≤
      (2 * (Real.log 4 + 4) + 1) * x * ∑ n ∈ Ioc 0 x, FF m n / n := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hc0 : (0 : ℝ) ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have h1 : ∀ n ∈ Ioc 0 x, FF m n * Real.log x ≤ FF m n * Real.log n + x * (FF m n / n) := by
    intro n hn
    obtain ⟨hn0, hnx⟩ := mem_Ioc.1 hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlog : Real.log x - Real.log n ≤ x / n := by
      rw [← Real.log_div hxR.ne' hnR.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hxR hnR)
      linarith
    have hF := FF_nonneg m n
    have h3 : FF m n * (Real.log x - Real.log n) ≤ FF m n * (x / n) :=
      mul_le_mul_of_nonneg_left hlog hF
    have e : (x : ℝ) * (FF m n / n) = FF m n * ((x : ℝ) / n) := by ring
    rw [e]
    linarith
  have hlogn : ∀ n ∈ Ioc 0 x, Real.log n =
      ∑ d ∈ Ioc 0 x, (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := by
    intro n hn
    obtain ⟨hn0, hnx⟩ := mem_Ioc.1 hn
    rw [← ArithmeticFunction.vonMangoldt_sum, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn0, (Nat.le_of_dvd hn0 hd).trans hnx⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, hn0.ne'⟩
  have hswap : ∑ n ∈ Ioc 0 x, FF m n * Real.log n =
      ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d *
        ∑ n ∈ (Ioc 0 x).filter (fun n => d ∣ n), FF m n := by
    calc ∑ n ∈ Ioc 0 x, FF m n * Real.log n
        = ∑ n ∈ Ioc 0 x, ∑ d ∈ Ioc 0 x,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d * FF m n else 0) := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [hlogn n hn, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          split_ifs <;> ring
      _ = ∑ d ∈ Ioc 0 x, ∑ n ∈ Ioc 0 x,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d * FF m n else 0) := Finset.sum_comm
      _ = ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d *
            ∑ n ∈ (Ioc 0 x).filter (fun n => d ∣ n), FF m n := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
  have hmult : ∀ d ∈ Ioc 0 x, ∑ n ∈ (Ioc 0 x).filter (fun n => d ∣ n), FF m n =
      ∑ k ∈ Ioc 0 (x / d), FF m (d * k) := by
    intro d hd
    have hd0 : 0 < d := (mem_Ioc.1 hd).1
    symm
    apply Finset.sum_bij (fun k _ => d * k)
    · intro k hk
      obtain ⟨hk0, hkx⟩ := mem_Ioc.1 hk
      simp only [mem_filter, mem_Ioc]
      refine ⟨⟨Nat.mul_pos hd0 hk0, ?_⟩, dvd_mul_right d k⟩
      calc d * k ≤ d * (x / d) := Nat.mul_le_mul_left d hkx
        _ ≤ x := Nat.mul_div_le x d
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hd0 h
    · intro n hn
      simp only [mem_filter, mem_Ioc] at hn
      obtain ⟨⟨hn0, hnx⟩, k, rfl⟩ := hn
      refine ⟨k, ?_, rfl⟩
      rw [mem_Ioc]
      refine ⟨Nat.pos_of_ne_zero (fun h0 => ?_), (Nat.le_div_iff_mul_le hd0).2 ?_⟩
      · rw [h0, Nat.mul_zero] at hn0
        exact lt_irrefl 0 hn0
      · rwa [mul_comm]
    · intro _ _
      rfl
  have hpp : ∀ d ∈ Ioc 0 x,
      ArithmeticFunction.vonMangoldt d * ∑ k ∈ Ioc 0 (x / d), FF m (d * k) ≤
        ArithmeticFunction.vonMangoldt d * (2 * ∑ k ∈ Ioc 0 (x / d), FF m k) := by
    intro d _
    by_cases hΛ : ArithmeticFunction.vonMangoldt d = 0
    · rw [hΛ]
      simp
    · obtain ⟨p, j, hp, hj, rfl⟩ :=
        (isPrimePow_nat_iff d).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      exact FF_prime_pow_mul m p j k hp hj (mem_Ioc.1 hk).1
  have e1 : ∀ d ∈ Ioc 0 x, ∑ k ∈ Ioc 0 (x / d), FF m k =
      ∑ k ∈ Ioc 0 x, (if d * k ≤ x then FF m k else 0) := by
    intro d hd
    have hd0 := (mem_Ioc.1 hd).1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hk0, hk⟩
      have hdk : d * k ≤ x := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd0).1 hk
      exact ⟨⟨hk0, le_trans (Nat.le_mul_of_pos_left k hd0) hdk⟩, hdk⟩
    · rintro ⟨⟨hk0, _⟩, h⟩
      exact ⟨hk0, (Nat.le_div_iff_mul_le hd0).2 (by rwa [mul_comm])⟩
  have e2 : ∀ k ∈ Ioc 0 x, ∑ d ∈ Ioc 0 (x / k), ArithmeticFunction.vonMangoldt d =
      ∑ d ∈ Ioc 0 x, (if d * k ≤ x then ArithmeticFunction.vonMangoldt d else 0) := by
    intro k hk
    have hk0 := (mem_Ioc.1 hk).1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd0, hd⟩
      have hdk : d * k ≤ x := (Nat.le_div_iff_mul_le hk0).1 hd
      exact ⟨⟨hd0, le_trans (Nat.le_mul_of_pos_right d hk0) hdk⟩, hdk⟩
    · rintro ⟨⟨hd0, _⟩, h⟩
      exact ⟨hd0, (Nat.le_div_iff_mul_le hk0).2 h⟩
  have hhyp : ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d *
      (2 * ∑ k ∈ Ioc 0 (x / d), FF m k) =
      2 * ∑ k ∈ Ioc 0 x, FF m k * ∑ d ∈ Ioc 0 (x / k), ArithmeticFunction.vonMangoldt d := by
    calc ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d * (2 * ∑ k ∈ Ioc 0 (x / d), FF m k)
        = ∑ d ∈ Ioc 0 x, ∑ k ∈ Ioc 0 x,
            (if d * k ≤ x then 2 * (ArithmeticFunction.vonMangoldt d * FF m k) else 0) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          rw [e1 d hd, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          split_ifs <;> ring
      _ = ∑ k ∈ Ioc 0 x, ∑ d ∈ Ioc 0 x,
            (if d * k ≤ x then 2 * (ArithmeticFunction.vonMangoldt d * FF m k) else 0) :=
          Finset.sum_comm
      _ = 2 * ∑ k ∈ Ioc 0 x, FF m k * ∑ d ∈ Ioc 0 (x / k), ArithmeticFunction.vonMangoldt d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [e2 k hk, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          split_ifs <;> ring
  have hcheb : ∀ k ∈ Ioc 0 x, ∑ d ∈ Ioc 0 (x / k), ArithmeticFunction.vonMangoldt d ≤
      (Real.log 4 + 4) * ((x : ℝ) / k) := by
    intro k _
    have h := Chebyshev.psi_le_const_mul_self (x := ((x / k : ℕ) : ℝ)) (Nat.cast_nonneg _)
    rw [Chebyshev.psi, Nat.floor_natCast] at h
    exact h.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hc0)
  have h2 : ∑ n ∈ Ioc 0 x, FF m n * Real.log n ≤
      2 * (Real.log 4 + 4) * x * ∑ k ∈ Ioc 0 x, FF m k / k := by
    calc ∑ n ∈ Ioc 0 x, FF m n * Real.log n
        = ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d *
            ∑ k ∈ Ioc 0 (x / d), FF m (d * k) := by
          rw [hswap]
          exact Finset.sum_congr rfl (fun d hd => by rw [hmult d hd])
      _ ≤ ∑ d ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt d *
            (2 * ∑ k ∈ Ioc 0 (x / d), FF m k) := Finset.sum_le_sum hpp
      _ = 2 * ∑ k ∈ Ioc 0 x, FF m k * ∑ d ∈ Ioc 0 (x / k), ArithmeticFunction.vonMangoldt d :=
          hhyp
      _ ≤ 2 * ∑ k ∈ Ioc 0 x, FF m k * ((Real.log 4 + 4) * ((x : ℝ) / k)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hcheb k hk) (FF_nonneg m k)
      _ = 2 * (Real.log 4 + 4) * x * ∑ k ∈ Ioc 0 x, FF m k / k := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
  calc (∑ n ∈ Ioc 0 x, FF m n) * Real.log x = ∑ n ∈ Ioc 0 x, FF m n * Real.log x :=
        Finset.sum_mul ..
    _ ≤ ∑ n ∈ Ioc 0 x, (FF m n * Real.log n + x * (FF m n / n)) := Finset.sum_le_sum h1
    _ = ∑ n ∈ Ioc 0 x, FF m n * Real.log n + x * ∑ n ∈ Ioc 0 x, FF m n / n := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 * (Real.log 4 + 4) + 1) * x * ∑ n ∈ Ioc 0 x, FF m n / n := by
        have e : (2 * (Real.log 4 + 4) + 1) * x * ∑ n ∈ Ioc 0 x, FF m n / n =
            2 * (Real.log 4 + 4) * x * ∑ n ∈ Ioc 0 x, FF m n / n +
              x * ∑ n ∈ Ioc 0 x, FF m n / n := by ring
        rw [e]
        linarith


-- The local Euler factor of the function n -> FF m n / n at a prime p.
lemma GG_hasSum (m p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => FF m (p ^ k) / ((p ^ k : ℕ) : ℝ))
      (if p ∣ m then 1 else ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hgeo := hasSum_geometric_of_lt_one hr0 hr1
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    have hfun : (fun k : ℕ => FF m (p ^ k) / ((p ^ k : ℕ) : ℝ)) =
        fun k => if k = 0 then (1 : ℝ) else 0 := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [FF, HH_one]
      · rw [if_neg hk.ne']
        have hnc : ¬ Nat.Coprime (p ^ k) m := by
          rw [Nat.coprime_pow_left_iff hk]
          exact fun h => (hp.coprime_iff_not_dvd.1 h) hpm
        simp [FF, hnc]
    rw [hfun]
    exact hasSum_ite_eq 0 1
  · rw [if_neg hpm]
    have hfun : (fun k : ℕ => FF m (p ^ k) / ((p ^ k : ℕ) : ℝ)) =
        fun k => (1 - 1 / (p : ℝ))⁻¹ * (1 / (p : ℝ)) ^ k +
          (if k = 0 then 1 - (1 - 1 / (p : ℝ))⁻¹ else 0) := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [FF, HH_one]
      · rw [if_neg hk.ne', add_zero]
        have hc : Nat.Coprime (p ^ k) m := by
          rw [Nat.coprime_pow_left_iff hk]
          exact hp.coprime_iff_not_dvd.2 hpm
        have hH : HH (p ^ k) = (1 - 1 / (p : ℝ))⁻¹ := by
          unfold HH
          rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
        rw [FF, if_pos hc, hH]
        push_cast
        rw [one_div_pow, div_eq_mul_one_div]
    rw [hfun]
    have h1 := hgeo.mul_left ((1 - 1 / (p : ℝ))⁻¹)
    have h2 := hasSum_ite_eq (0 : ℕ) (1 - (1 - 1 / (p : ℝ))⁻¹)
    have h3 := h1.add h2
    have e : ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1 =
        (1 - 1 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ))⁻¹ + (1 - (1 - 1 / (p : ℝ))⁻¹) := by ring
    rw [e]
    exact h3

-- The logarithmic sum is bounded by the Euler product over the primes up to x.
lemma log_sum_le_prod (m x : ℕ) :
    ∑ n ∈ Ioc 0 x, FF m n / n ≤
      ∏ p ∈ Nat.primesLE x,
        (if p ∣ m then 1 else ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = FF m n / n := ⟨_, fun _ => rfl⟩
  have hg1 : g 1 = 1 := by
    rw [hg]
    simp [FF, HH_one]
  have hgmul : ∀ {a b : ℕ}, Nat.Coprime a b → g (a * b) = g a * g b := by
    intro a b hab
    rw [hg, hg, hg]
    have hF : FF m (a * b) = FF m a * FF m b := by
      unfold FF
      by_cases ha : Nat.Coprime a m
      · by_cases hb : Nat.Coprime b m
        · rw [if_pos (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩), if_pos ha, if_pos hb,
            HH_mul_coprime hab]
        · rw [if_neg (fun h => hb (Nat.coprime_mul_iff_left.1 h).2), if_neg hb, mul_zero]
      · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_left.1 h).1), if_neg ha, zero_mul]
    rw [hF]
    push_cast
    rw [mul_div_mul_comm]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖g (p ^ k)‖) := by
    intro p hp
    apply summable_norm_iff.2
    have hs := (GG_hasSum m p hp).summable
    simpa only [hg] using hs
  have hEP := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hgmul hsum (range (x + 1))).2
  have hind : HasSum ((Nat.factoredNumbers (range (x + 1)) : Set ℕ).indicator g)
      (∏ p ∈ range (x + 1) with p.Prime, ∑' k : ℕ, g (p ^ k)) :=
    hasSum_subtype_iff_indicator.1 hEP
  have hnn : ∀ n : ℕ, 0 ≤ g n := fun n => by
    rw [hg]
    exact div_nonneg (FF_nonneg m n) (Nat.cast_nonneg n)
  have hle := sum_le_hasSum (Ioc 0 x)
    (fun n _ => Set.indicator_nonneg (fun n _ => hnn n) n) hind
  have hlhs : ∑ n ∈ Ioc 0 x, (Nat.factoredNumbers (range (x + 1)) : Set ℕ).indicator g n =
      ∑ n ∈ Ioc 0 x, FF m n / n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hn0, hnx⟩ := mem_Ioc.1 hn
    rw [Set.indicator_of_mem, hg]
    rw [Nat.mem_factoredNumbers']
    intro p _ hpn
    exact mem_range.2 (Nat.lt_succ_of_le ((Nat.le_of_dvd hn0 hpn).trans hnx))
  have hrhs : ∏ p ∈ range (x + 1) with p.Prime, ∑' k : ℕ, g (p ^ k) =
      ∏ p ∈ Nat.primesLE x,
        (if p ∣ m then 1 else ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : p.Prime := (mem_filter.1 hp).2
    have hts := (GG_hasSum m p hpp).tsum_eq
    simpa only [hg] using hts
  rw [← hlhs, ← hrhs]
  exact hle

-- The sum of 1 / (p - 1)^2 over primes is at most 2.
lemma sum_inv_sq_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 / ((p : ℝ) - 1)) ^ 2 ≤ 2 := by
  rw [primesLE_sum]
  have h1 : ∀ M : ℕ, ∑ p ∈ range (M + 3),
      (if p.Prime then (1 / ((p : ℝ) - 1)) ^ 2 else 0) ≤ 2 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [Nat.prime_two]
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have hle : (if (M + 3).Prime then (1 / (((M + 3 : ℕ) : ℝ) - 1)) ^ 2 else 0) ≤
          1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 2) := by
        have hpos : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 2) := by
          rw [sub_nonneg]
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
        split_ifs
        · push_cast
          have e : (M : ℝ) + 3 - 1 = M + 2 := by ring
          rw [e, div_sub_div _ _ (by linarith) (by linarith), div_pow,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        · exact hpos
      push_cast at hle ⊢
      have e2 : (M : ℝ) + 1 + 1 = M + 2 := by ring
      rw [e2]
      linarith
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hz : ∑ p ∈ range (N + 1), (if p.Prime then (1 / ((p : ℝ) - 1)) ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hp2 : p < N + 1 := mem_range.1 hp
      rw [if_neg]
      intro hpr
      have := hpr.two_le
      omega
    rw [hz]
    norm_num
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
    have h2 := h1 M
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith

-- The sieve bound: integers up to x coprime to m, weighted by n / phi(n).
lemma sieve_bound (m x : ℕ) (hm : 0 < m) (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, FF m n ≤
      ((2 * (Real.log 4 + 4) + 1) * (Real.exp 2 * Real.exp (4 - Real.log (Real.log 2)))) * x *
        ∏ p ∈ m.primeFactors.filter (fun p => p ≤ x), (1 - 1 / (p : ℝ)) := by
  have hc0 : (0 : ℝ) ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hPpos : (0 : ℝ) < ∏ p ∈ m.primeFactors.filter (fun p => p ≤ x), (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  rcases hx.eq_or_lt with hx1 | hx2
  · -- x = 1
    subst hx1
    have hI : Ioc 0 1 = {1} := by decide
    have hfil : m.primeFactors.filter (fun p => p ≤ 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    rw [hI, Finset.sum_singleton, hfil, Finset.prod_empty]
    have hF1 : FF m 1 = 1 := by simp [FF, HH_one]
    rw [hF1]
    have h1 : (1 : ℝ) ≤ 2 * (Real.log 4 + 4) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ Real.exp 2 * Real.exp (4 - Real.log (Real.log 2)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : Real.log (Real.log 2) ≤ 0 := by
        apply Real.log_nonpos (Real.log_nonneg (by norm_num))
        have := Real.log_two_lt_d9
        linarith
      linarith
    have h3 : (1 : ℝ) ≤ (2 * (Real.log 4 + 4) + 1) *
        (Real.exp 2 * Real.exp (4 - Real.log (Real.log 2))) := by nlinarith
    push_cast
    linarith
  · have hx2R : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hxR : (0 : ℝ) < x := by linarith
    have hmemP : ∀ p ∈ Nat.primesLE x, p.Prime ∧ p ≤ x := by
      intro p hp
      simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range] at hp
      exact ⟨hp.2, by omega⟩
    -- the Euler factors against the Mertens product
    have hfac : ∀ p ∈ Nat.primesLE x,
        (if p ∣ m then 1 else ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1) ≤
          ((1 - 1 / (p : ℝ))⁻¹ * (if p ∣ m then (1 - 1 / (p : ℝ)) else 1)) *
            Real.exp ((1 / ((p : ℝ) - 1)) ^ 2) := by
      intro p hp
      have hpp := (hmemP p hp).1
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hb := inv_factor_bounds p hpp
      have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
        have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
        linarith
      have hu : (1 - 1 / (p : ℝ))⁻¹ - 1 = 1 / ((p : ℝ) - 1) := by
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have h : (1 - 1 / (p : ℝ)) * (1 / ((p : ℝ) - 1) + 1) = 1 := by
          rw [one_sub_div hp0, div_add_one hp1, div_mul_div_comm]
          rw [div_eq_one_iff_eq (mul_ne_zero hp0 hp1)]
          ring
        rw [inv_eq_of_mul_eq_one_right h]
        ring
      have hexp : 1 + (1 / ((p : ℝ) - 1)) ^ 2 ≤ Real.exp ((1 / ((p : ℝ) - 1)) ^ 2) := by
        linarith [Real.add_one_le_exp ((1 / ((p : ℝ) - 1)) ^ 2)]
      split_ifs
      · rw [inv_mul_cancel₀ hpos.ne', one_mul]
        linarith [sq_nonneg (1 / ((p : ℝ) - 1))]
      · rw [mul_one]
        have h1 : ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1 ≤
            (1 - 1 / (p : ℝ))⁻¹ * (1 + (1 / ((p : ℝ) - 1)) ^ 2) := by
          rw [← hu]
          nlinarith [hb.1, sq_nonneg ((1 - 1 / (p : ℝ))⁻¹ - 1)]
        exact h1.trans (mul_le_mul_of_nonneg_left hexp (by linarith [hb.1]))
    have hprod1 : ∏ p ∈ Nat.primesLE x,
        (if p ∣ m then 1 else ((1 - 1 / (p : ℝ))⁻¹) ^ 2 - (1 - 1 / (p : ℝ))⁻¹ + 1) ≤
        ∏ p ∈ Nat.primesLE x, (((1 - 1 / (p : ℝ))⁻¹ *
          (if p ∣ m then (1 - 1 / (p : ℝ)) else 1)) * Real.exp ((1 / ((p : ℝ) - 1)) ^ 2)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hb := inv_factor_bounds p (hmemP p hp).1
        split_ifs
        · norm_num
        · nlinarith [hb.1]
      · exact hfac
    have hfilter : (Nat.primesLE x).filter (fun p => p ∣ m) =
        m.primeFactors.filter (fun p => p ≤ x) := by
      ext p
      simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hpx, hp⟩, hd⟩
        exact ⟨⟨hp, hd, hm.ne'⟩, by omega⟩
      · rintro ⟨⟨hp, hd, _⟩, hpx⟩
        exact ⟨⟨by omega, hp⟩, hd⟩
    have hprod2 : ∏ p ∈ Nat.primesLE x, (((1 - 1 / (p : ℝ))⁻¹ *
          (if p ∣ m then (1 - 1 / (p : ℝ)) else 1)) * Real.exp ((1 / ((p : ℝ) - 1)) ^ 2)) =
        (∏ p ∈ Nat.primesLE x, (1 - 1 / (p : ℝ))⁻¹) *
          (∏ p ∈ m.primeFactors.filter (fun p => p ≤ x), (1 - 1 / (p : ℝ))) *
          Real.exp (∑ p ∈ Nat.primesLE x, (1 / ((p : ℝ) - 1)) ^ 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.exp_sum, ← hfilter,
        Finset.prod_filter]
    have hM := prod_primes_le x hx2
    have hM0 : (0 : ℝ) ≤ ∏ p ∈ Nat.primesLE x, (1 - 1 / (p : ℝ))⁻¹ :=
      Finset.prod_nonneg (fun p hp => by
        have hb := inv_factor_bounds p (hmemP p hp).1
        linarith [hb.1])
    have hE : Real.exp (∑ p ∈ Nat.primesLE x, (1 / ((p : ℝ) - 1)) ^ 2) ≤ Real.exp 2 :=
      Real.exp_le_exp.2 (sum_inv_sq_le x)
    have hT : ∑ n ∈ Ioc 0 x, FF m n / n ≤
        (Real.exp (4 - Real.log (Real.log 2)) * Real.log x) *
          (∏ p ∈ m.primeFactors.filter (fun p => p ≤ x), (1 - 1 / (p : ℝ))) * Real.exp 2 := by
      refine (log_sum_le_prod m x).trans (hprod1.trans ?_)
      rw [hprod2]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hM hPpos.le) hE (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hL.le) hPpos.le)
    have hlt := log_trick m x hx
    have hfin : (∑ n ∈ Ioc 0 x, FF m n) * Real.log x ≤
        (((2 * (Real.log 4 + 4) + 1) * (Real.exp 2 * Real.exp (4 - Real.log (Real.log 2)))) * x *
          ∏ p ∈ m.primeFactors.filter (fun p => p ≤ x), (1 - 1 / (p : ℝ))) * Real.log x := by
      refine hlt.trans ?_
      have hcx : (0 : ℝ) ≤ (2 * (Real.log 4 + 4) + 1) * x := by positivity
      have := mul_le_mul_of_nonneg_left hT hcx
      refine this.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_right hfin hL


-- Counting with a periodic predicate over a whole number of periods.
lemma card_filter_range_mul (P : ℕ → Prop) [DecidablePred P] (u : ℕ)
    (hP : Function.Periodic P u) (k : ℕ) :
    ((range (u * k)).filter P).card = k * ((range u).filter P).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : range (u * (k + 1)) = range (u * k) ∪ Ico (u * k) (u * k + u) := by
      ext s
      simp only [mem_range, mem_union, mem_Ico]
      rw [Nat.mul_succ]
      omega
    have hdisj : Disjoint (range (u * k)) (Ico (u * k) (u * k + u)) := by
      rw [Finset.disjoint_left]
      intro s hs hs2
      simp only [mem_range, mem_Ico] at hs hs2
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), ih,
      Nat.filter_Ico_card_eq_of_periodic _ _ _ hP, Nat.count_eq_card_filter_range]
    ring

-- Chinese remainder counting for two periodic predicates with coprime periods.
lemma card_filter_crt (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) (huv : Nat.Coprime u v)
    (hP : Function.Periodic P u) (hQ : Function.Periodic Q v) :
    ((range (u * v)).filter (fun s => P s ∧ Q s)).card =
      ((range u).filter P).card * ((range v).filter Q).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun s _ => (s % u, s % v))
  · intro s hs
    simp only [mem_filter, mem_range] at hs
    simp only [mem_product, mem_filter, mem_range]
    refine ⟨⟨Nat.mod_lt _ hu, ?_⟩, ⟨Nat.mod_lt _ hv, ?_⟩⟩
    · rw [hP.map_mod_nat]
      exact hs.2.1
    · rw [hQ.map_mod_nat]
      exact hs.2.2
  · intro s hs t ht h
    simp only [mem_filter, mem_range] at hs ht
    have h1 : s % u = t % u := (Prod.mk.inj h).1
    have h2 : s % v = t % v := (Prod.mk.inj h).2
    have h3 : s ≡ t [MOD u * v] := (Nat.modEq_and_modEq_iff_modEq_mul huv).1 ⟨h1, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h3 hs.1 ht.1
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_filter, mem_range] at hab
    obtain ⟨⟨ha, hPa⟩, ⟨hb, hQb⟩⟩ := hab
    have hk1 : ((Nat.chineseRemainder huv a b : ℕ)) % u = a := by
      have h := (Nat.chineseRemainder huv a b).prop.1
      unfold Nat.ModEq at h
      rw [h, Nat.mod_eq_of_lt ha]
    have hk2 : ((Nat.chineseRemainder huv a b : ℕ)) % v = b := by
      have h := (Nat.chineseRemainder huv a b).prop.2
      unfold Nat.ModEq at h
      rw [h, Nat.mod_eq_of_lt hb]
    have hklt := Nat.chineseRemainder_lt_mul huv a b hu.ne' hv.ne'
    refine ⟨(Nat.chineseRemainder huv a b : ℕ), ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨hklt, ?_, ?_⟩
      · rw [← hP.map_mod_nat, hk1]
        exact hPa
      · rw [← hQ.map_mod_nat, hk2]
        exact hQb
    · rw [hk1, hk2]

-- A family of periodic conditions at distinct primes, counted over one full period.
lemma card_filter_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (P : ℕ → ℕ → Prop)
    [∀ p, DecidablePred (P p)]
    (hP : ∀ p ∈ T, Function.Periodic (P p) p) (c : ℕ → ℕ)
    (hc : ∀ p ∈ T, ((range p).filter (P p)).card ≤ p - c p) :
    ((range (∏ p ∈ T, p)).filter (fun s => ∀ p ∈ T, P p s)).card ≤ ∏ p ∈ T, (p - c p) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hpT ih =>
    rw [Finset.prod_insert hpT, Finset.prod_insert hpT]
    have hpp : p.Prime := hT p (mem_insert_self p T)
    have hTp : ∀ q ∈ T, q.Prime := fun q hq => hT q (mem_insert_of_mem hq)
    have hco : Nat.Coprime p (∏ q ∈ T, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpp (hTp q hq)).2 (fun h => hpT (h ▸ hq))
    have hQ : Function.Periodic (fun s => ∀ q ∈ T, P q s) (∏ q ∈ T, q) := by
      intro s
      refine propext (forall₂_congr (fun q hq => ?_))
      have hper := (hP q (mem_insert_of_mem hq)).nat_mul ((∏ q ∈ T, q) / q) s
      rw [Nat.cast_id, Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ hq)] at hper
      rw [hper]
    have hfil : (range (p * ∏ q ∈ T, q)).filter (fun s => ∀ q ∈ insert p T, P q s) =
        (range (p * ∏ q ∈ T, q)).filter (fun s => P p s ∧ ∀ q ∈ T, P q s) := by
      apply Finset.filter_congr
      intro s _
      rw [Finset.forall_mem_insert]
    have hpos : 0 < ∏ q ∈ T, q := Finset.prod_pos (fun q hq => (hTp q hq).pos)
    rw [hfil, card_filter_crt (P p) (fun s => ∀ q ∈ T, P q s) p _ hpp.pos hpos hco
      (hP p (mem_insert_self p T)) hQ]
    exact Nat.mul_le_mul (hc p (mem_insert_self _ _))
      (ih hTp (fun q hq => hP q (mem_insert_of_mem hq)) (fun q hq => hc q (mem_insert_of_mem hq)))

-- The same count over any multiple of the product of the primes.
lemma card_filter_general (g : ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hg : (∏ p ∈ T, p) ∣ g) (P : ℕ → ℕ → Prop) [∀ p, DecidablePred (P p)]
    (hP : ∀ p ∈ T, Function.Periodic (P p) p) (c : ℕ → ℕ)
    (hc : ∀ p ∈ T, ((range p).filter (P p)).card ≤ p - c p) :
    ((range g).filter (fun s => ∀ p ∈ T, P p s)).card ≤
      (g / ∏ p ∈ T, p) * ∏ p ∈ T, (p - c p) := by
  have hQ : Function.Periodic (fun s => ∀ q ∈ T, P q s) (∏ q ∈ T, q) := by
    intro s
    refine propext (forall₂_congr (fun q hq => ?_))
    have hper := (hP q hq).nat_mul ((∏ q ∈ T, q) / q) s
    rw [Nat.cast_id, Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ hq)] at hper
    rw [hper]
  have hgeq : g = (∏ p ∈ T, p) * (g / ∏ p ∈ T, p) := (Nat.mul_div_cancel' hg).symm
  have h1 := card_filter_range_mul (fun s => ∀ q ∈ T, P q s) (∏ q ∈ T, q) hQ (g / ∏ p ∈ T, p)
  rw [← hgeq] at h1
  rw [h1]
  exact Nat.mul_le_mul_left _ (card_filter_primes T hT P hP c hc)


lemma not_dvd_of_coprime (p a m : ℕ) (hp : p.Prime) (h : Nat.Coprime a m) (hm : p ∣ m) :
    ¬ p ∣ a := by
  intro ha
  have h1 := Nat.dvd_gcd ha hm
  rw [h.gcd_eq_one] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

-- A linear congruence c t = -A modulo a prime not dividing c has a solution below p.
lemma exists_root (p : ℕ) (hp : p.Prime) (c : ℕ) (hc : ¬ p ∣ c) (A : ℤ) :
    ∃ t < p, (p : ℤ) ∣ A + c * t := by
  have hcop : Nat.Coprime c p := (hp.coprime_iff_not_dvd.2 hc).symm
  obtain ⟨y, hy⟩ := Int.mod_coprime hcop
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have h0 := Int.emod_nonneg (-A * y) hp0
  have h1 := Int.emod_lt_of_pos (-A * y) hpos
  refine ⟨((-A * y) % p).toNat, ?_, ?_⟩
  · omega
  · have ht : ((((-A * y) % p).toNat : ℕ) : ℤ) = (-A * y) % p := Int.toNat_of_nonneg h0
    rw [ht, Int.emod_def]
    obtain ⟨k, hk⟩ := hy.dvd
    exact ⟨A * k - c * ((-A * y) / p), by linear_combination A * hk⟩

-- At a prime p, the residues s below p avoiding the zeros of two linear forms.
lemma bad_count (p : ℕ) (hp : p.Prime) (a0 b0 : ℤ) (qq rr : ℕ) (hco : Nat.Coprime qq rr)
    (c : ℕ) (hc : c = 1 ∨ (c = 2 ∧ ¬ p ∣ qq ∧ ¬ p ∣ rr ∧ ¬ (p : ℤ) ∣ a0 * rr - b0 * qq)) :
    ((range p).filter (fun s : ℕ => ¬ ((p : ℤ) ∣ a0 + qq * s) ∧ ¬ ((p : ℤ) ∣ b0 + rr * s))).card
      ≤ p - c := by
  rcases hc with rfl | ⟨rfl, hq, hr, hn⟩
  · have hone : ∃ t < p, (p : ℤ) ∣ a0 + qq * t ∨ (p : ℤ) ∣ b0 + rr * t := by
      by_cases hq : p ∣ qq
      · have hr : ¬ p ∣ rr := fun hr => by
          have h1 := Nat.dvd_gcd hq hr
          rw [hco.gcd_eq_one] at h1
          exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
        obtain ⟨t, ht, hd⟩ := exists_root p hp rr hr b0
        exact ⟨t, ht, Or.inr hd⟩
      · obtain ⟨t, ht, hd⟩ := exists_root p hp qq hq a0
        exact ⟨t, ht, Or.inl hd⟩
    obtain ⟨t, ht, hd⟩ := hone
    have hsub : (range p).filter (fun s : ℕ => ¬ ((p : ℤ) ∣ a0 + qq * s) ∧
        ¬ ((p : ℤ) ∣ b0 + rr * s)) ⊆ (range p).erase t := by
      intro s hs
      rw [mem_filter] at hs
      rw [mem_erase]
      refine ⟨?_, hs.1⟩
      rintro rfl
      rcases hd with hd | hd
      · exact hs.2.1 hd
      · exact hs.2.2 hd
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_range.2 ht), Finset.card_range] at hcard
    exact hcard
  · obtain ⟨t1, ht1, hd1⟩ := exists_root p hp qq hq a0
    obtain ⟨t2, ht2, hd2⟩ := exists_root p hp rr hr b0
    have hne : t1 ≠ t2 := by
      rintro rfl
      apply hn
      have e : a0 * rr - b0 * qq = rr * (a0 + qq * t1) - qq * (b0 + rr * t1) := by ring
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left hd1 _) (Dvd.dvd.mul_left hd2 _)
    have hsub : (range p).filter (fun s : ℕ => ¬ ((p : ℤ) ∣ a0 + qq * s) ∧
        ¬ ((p : ℤ) ∣ b0 + rr * s)) ⊆ ((range p).erase t1).erase t2 := by
      intro s hs
      rw [mem_filter] at hs
      rw [mem_erase, mem_erase]
      refine ⟨?_, ?_, hs.1⟩
      · rintro rfl
        exact hs.2.2 hd2
      · rintro rfl
        exact hs.2.1 hd1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_erase.2 ⟨hne.symm, mem_range.2 ht2⟩),
      Finset.card_erase_of_mem (mem_range.2 ht1), Finset.card_range] at hcard
    omega

-- Pairs of residues (a mod q, b mod r), both units, with a r1 - b q1 congruent to n modulo
-- the least common multiple; here q = q1 g, r = r1 g with q1, r1 coprime.
def SolSet (qq rr g : ℕ) (n : ℤ) : Finset (ℕ × ℕ) :=
  (range (qq * g) ×ˢ range (rr * g)).filter (fun ab : ℕ × ℕ =>
    Nat.Coprime ab.1 (qq * g) ∧ Nat.Coprime ab.2 (rr * g) ∧
      ((qq * rr * g : ℕ) : ℤ) ∣ (ab.1 : ℤ) * rr - (ab.2 : ℤ) * qq - n)



-- A solution forces n to be coprime to q1 r1.
lemma sol_coprime (qq rr g : ℕ) (hco : Nat.Coprime qq rr) (n : ℤ) (ab : ℕ × ℕ)
    (h : ab ∈ SolSet qq rr g n) : Nat.Coprime n.natAbs (qq * rr) := by
  simp only [SolSet, mem_filter, mem_product, mem_range] at h
  obtain ⟨_, ha, hb, hd⟩ := h
  have hL1 : ∀ p : ℕ, p ∣ qq → (p : ℤ) ∣ ((qq * rr * g : ℕ) : ℤ) := fun p hq =>
    Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_right (Dvd.dvd.mul_right hq rr) g)
  have hL2 : ∀ p : ℕ, p ∣ rr → (p : ℤ) ∣ ((qq * rr * g : ℕ) : ℤ) := fun p hr =>
    Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_right (Dvd.dvd.mul_left hr qq) g)
  apply Nat.Coprime.mul_right
  · apply Nat.coprime_of_dvd
    intro p hp hpn hpq
    have hpn1 : (p : ℤ) ∣ n := Int.natCast_dvd.2 hpn
    have h1 : (p : ℤ) ∣ (ab.1 : ℤ) * rr - (ab.2 : ℤ) * qq - n := dvd_trans (hL1 p hpq) hd
    have h2 : (p : ℤ) ∣ (ab.2 : ℤ) * qq := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 hpq) _
    have h3 : (p : ℤ) ∣ (ab.1 : ℤ) * rr := by
      have h := dvd_add (dvd_add h1 hpn1) h2
      have e : (ab.1 : ℤ) * rr - (ab.2 : ℤ) * qq - n + n + (ab.2 : ℤ) * qq = (ab.1 : ℤ) * rr := by
        ring
      rwa [e] at h
    have h4 : p ∣ ab.1 * rr := by exact_mod_cast h3
    rcases (hp.dvd_mul).1 h4 with h5 | h5
    · exact not_dvd_of_coprime p ab.1 (qq * g) hp ha (Dvd.dvd.mul_right hpq g) h5
    · exact not_dvd_of_coprime p qq rr hp hco h5 hpq
  · apply Nat.coprime_of_dvd
    intro p hp hpn hpr
    have hpn1 : (p : ℤ) ∣ n := Int.natCast_dvd.2 hpn
    have h1 : (p : ℤ) ∣ (ab.1 : ℤ) * rr - (ab.2 : ℤ) * qq - n := dvd_trans (hL2 p hpr) hd
    have h2 : (p : ℤ) ∣ (ab.1 : ℤ) * rr := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 hpr) _
    have h3 : (p : ℤ) ∣ (ab.2 : ℤ) * qq := by
      have h := dvd_sub h2 (dvd_add h1 hpn1)
      have e : (ab.1 : ℤ) * rr - ((ab.1 : ℤ) * rr - (ab.2 : ℤ) * qq - n + n) = (ab.2 : ℤ) * qq := by
        ring
      rwa [e] at h
    have h4 : p ∣ ab.2 * qq := by exact_mod_cast h3
    rcases (hp.dvd_mul).1 h4 with h5 | h5
    · exact not_dvd_of_coprime p ab.2 (rr * g) hp hb (Dvd.dvd.mul_right hpr g) h5
    · exact not_dvd_of_coprime p qq rr hp hco hpr h5

-- Any two solutions differ by a multiple of (q1, r1), up to a common shift modulo g.
lemma sol_structure (qq rr g : ℕ) (hq : 0 < qq) (hr : 0 < rr) (hco : Nat.Coprime qq rr) (n : ℤ)
    (a0 b0 a b : ℕ) (h0 : (a0, b0) ∈ SolSet qq rr g n) (h : (a, b) ∈ SolSet qq rr g n) :
    ∃ σ τ : ℤ, (a : ℤ) - a0 = qq * σ ∧ (b : ℤ) - b0 = rr * τ ∧ (g : ℤ) ∣ σ - τ := by
  simp only [SolSet, mem_filter, mem_product, mem_range] at h0 h
  obtain ⟨_, _, _, hd0⟩ := h0
  obtain ⟨_, _, _, hd⟩ := h
  have hdiff : ((qq * rr * g : ℕ) : ℤ) ∣ ((a : ℤ) - a0) * rr - ((b : ℤ) - b0) * qq := by
    have h1 := dvd_sub hd hd0
    have e : (a : ℤ) * rr - (b : ℤ) * qq - n - ((a0 : ℤ) * rr - (b0 : ℤ) * qq - n) =
        ((a : ℤ) - a0) * rr - ((b : ℤ) - b0) * qq := by ring
    rwa [e] at h1
  have hcoZ : IsCoprime (qq : ℤ) (rr : ℤ) := Nat.isCoprime_iff_coprime.2 hco
  have hqL : (qq : ℤ) ∣ ((qq * rr * g : ℕ) : ℤ) := ⟨(rr : ℤ) * g, by push_cast; ring⟩
  have hrL : (rr : ℤ) ∣ ((qq * rr * g : ℕ) : ℤ) := ⟨(qq : ℤ) * g, by push_cast; ring⟩
  have h1 : (qq : ℤ) ∣ ((a : ℤ) - a0) * rr := by
    have h := dvd_add (dvd_trans hqL hdiff)
      (Dvd.intro_left ((b : ℤ) - b0) rfl : (qq : ℤ) ∣ ((b : ℤ) - b0) * qq)
    have e : ((a : ℤ) - a0) * rr - ((b : ℤ) - b0) * qq + ((b : ℤ) - b0) * qq =
        ((a : ℤ) - a0) * rr := by ring
    rwa [e] at h
  obtain ⟨σ, hσ⟩ := hcoZ.dvd_of_dvd_mul_right h1
  have h2 : (rr : ℤ) ∣ ((b : ℤ) - b0) * qq := by
    have h := dvd_sub (Dvd.intro_left ((a : ℤ) - a0) rfl : (rr : ℤ) ∣ ((a : ℤ) - a0) * rr)
      (dvd_trans hrL hdiff)
    have e : ((a : ℤ) - a0) * rr - (((a : ℤ) - a0) * rr - ((b : ℤ) - b0) * qq) =
        ((b : ℤ) - b0) * qq := by ring
    rwa [e] at h
  obtain ⟨τ, hτ⟩ := hcoZ.symm.dvd_of_dvd_mul_right h2
  refine ⟨σ, τ, hσ, hτ, ?_⟩
  rw [hσ, hτ] at hdiff
  have e : (qq : ℤ) * σ * rr - (rr : ℤ) * τ * qq = ((qq : ℤ) * rr) * (σ - τ) := by ring
  have e2 : ((qq * rr * g : ℕ) : ℤ) = ((qq : ℤ) * rr) * g := by push_cast; ring
  rw [e, e2] at hdiff
  have hne : ((qq : ℤ) * rr) ≠ 0 := by exact_mod_cast (Nat.mul_pos hq hr).ne'
  exact (mul_dvd_mul_iff_left hne).1 hdiff

-- The number of solutions is at most g times the product of the local densities.
lemma sol_card_le (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr)
    (hco : Nat.Coprime qq rr) (n : ℤ) :
    (SolSet qq rr g n).card ≤ (g / ∏ p ∈ g.primeFactors, p) *
      ∏ p ∈ g.primeFactors, (p - (if p ∣ qq * rr * n.natAbs then 1 else 2)) := by
  rcases (SolSet qq rr g n).eq_empty_or_nonempty with he | ⟨⟨a0, b0⟩, h0⟩
  · rw [he]
    simp
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hqZ : (qq : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmem0 := h0
  simp only [SolSet, mem_filter, mem_product, mem_range] at hmem0
  obtain ⟨_, _, _, hd0⟩ := hmem0
  have hinj : (SolSet qq rr g n).card ≤ ((range g).filter (fun s : ℕ => ∀ p ∈ g.primeFactors,
      (¬ ((p : ℤ) ∣ (a0 : ℤ) + qq * s) ∧ ¬ ((p : ℤ) ∣ (b0 : ℤ) + rr * s)))).card := by
    apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ((((ab.1 : ℤ) - a0) / qq) % g).toNat)
    · rintro ⟨a, b⟩ hab
      obtain ⟨σ, τ, hσ, hτ, hgd⟩ := sol_structure qq rr g hq hr hco n a0 b0 a b h0 hab
      have hmem := hab
      simp only [SolSet, Finset.coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hmem
      obtain ⟨_, hca, hcb, _⟩ := hmem
      have hdiv : ((a : ℤ) - a0) / qq = σ := by
        rw [hσ]
        exact Int.mul_ediv_cancel_left σ hqZ
      have hs0 := Int.emod_nonneg σ hgZ.ne'
      have hs1 := Int.emod_lt_of_pos σ hgZ
      have hcast : (((σ % g).toNat : ℕ) : ℤ) = σ % g := Int.toNat_of_nonneg hs0
      have hgs : (g : ℤ) ∣ σ - (((σ % g).toNat : ℕ) : ℤ) := by
        rw [hcast]
        exact Int.ModEq.dvd (Int.mod_modEq σ g)
      have hgt : (g : ℤ) ∣ τ - (((σ % g).toNat : ℕ) : ℤ) := by
        have h := dvd_sub hgs hgd
        have e : σ - (((σ % g).toNat : ℕ) : ℤ) - (σ - τ) = τ - (((σ % g).toNat : ℕ) : ℤ) := by ring
        rwa [e] at h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_range, hdiv]
      refine ⟨by omega, ?_⟩
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpgN : p ∣ g := Nat.dvd_of_mem_primeFactors hp
      have hpg : (p : ℤ) ∣ g := Int.natCast_dvd_natCast.2 hpgN
      constructor
      · intro hdvd
        have e : (a : ℤ) = (a0 : ℤ) + qq * (((σ % g).toNat : ℕ) : ℤ) +
            qq * (σ - (((σ % g).toNat : ℕ) : ℤ)) := by linear_combination hσ
        have hpa : (p : ℤ) ∣ (a : ℤ) := by
          rw [e]
          exact dvd_add hdvd (Dvd.dvd.mul_left (dvd_trans hpg hgs) _)
        exact not_dvd_of_coprime p a (qq * g) hpp hca (Dvd.dvd.mul_left hpgN qq)
          (Int.natCast_dvd_natCast.1 hpa)
      · intro hdvd
        have e : (b : ℤ) = (b0 : ℤ) + rr * (((σ % g).toNat : ℕ) : ℤ) +
            rr * (τ - (((σ % g).toNat : ℕ) : ℤ)) := by linear_combination hτ
        have hpb : (p : ℤ) ∣ (b : ℤ) := by
          rw [e]
          exact dvd_add hdvd (Dvd.dvd.mul_left (dvd_trans hpg hgt) _)
        exact not_dvd_of_coprime p b (rr * g) hpp hcb (Dvd.dvd.mul_left hpgN rr)
          (Int.natCast_dvd_natCast.1 hpb)
    · rintro ⟨a, b⟩ hab ⟨a2, b2⟩ hab2 heq
      obtain ⟨σ, τ, hσ, hτ, hgd⟩ := sol_structure qq rr g hq hr hco n a0 b0 a b h0 hab
      obtain ⟨σ2, τ2, hσ2, hτ2, hgd2⟩ := sol_structure qq rr g hq hr hco n a0 b0 a2 b2 h0 hab2
      have hmem := hab
      have hmem2 := hab2
      simp only [SolSet, Finset.coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hmem hmem2
      have hdiv : ((a : ℤ) - a0) / qq = σ := by
        rw [hσ]
        exact Int.mul_ediv_cancel_left σ hqZ
      have hdiv2 : ((a2 : ℤ) - a0) / qq = σ2 := by
        rw [hσ2]
        exact Int.mul_ediv_cancel_left σ2 hqZ
      simp only [hdiv, hdiv2] at heq
      have hmod : σ % g = σ2 % g := by
        have h1 := Int.toNat_of_nonneg (Int.emod_nonneg σ hgZ.ne')
        have h2 := Int.toNat_of_nonneg (Int.emod_nonneg σ2 hgZ.ne')
        rw [← h1, ← h2, heq]
      have hgσ : (g : ℤ) ∣ σ2 - σ := Int.ModEq.dvd hmod
      have hgτ : (g : ℤ) ∣ τ2 - τ := by
        have h := dvd_add (dvd_sub hgσ hgd2) hgd
        have e : σ2 - σ - (σ2 - τ2) + (σ - τ) = τ2 - τ := by ring
        rwa [e] at h
      have ha : a = a2 := by
        have hd : ((qq * g : ℕ) : ℤ) ∣ (a2 : ℤ) - a := by
          obtain ⟨k, hk⟩ := hgσ
          exact ⟨k, by push_cast; linear_combination hσ2 - hσ + (qq : ℤ) * hk⟩
        have habs : |(a2 : ℤ) - a| < ((qq * g : ℕ) : ℤ) := by
          rw [abs_lt]
          constructor <;> omega
        have hz := Int.eq_zero_of_abs_lt_dvd hd habs
        omega
      have hb : b = b2 := by
        have hd : ((rr * g : ℕ) : ℤ) ∣ (b2 : ℤ) - b := by
          obtain ⟨k, hk⟩ := hgτ
          exact ⟨k, by push_cast; linear_combination hτ2 - hτ + (rr : ℤ) * hk⟩
        have habs : |(b2 : ℤ) - b| < ((rr * g : ℕ) : ℤ) := by
          rw [abs_lt]
          constructor <;> omega
        have hz := Int.eq_zero_of_abs_lt_dvd hd habs
        omega
      rw [ha, hb]
  refine hinj.trans ?_
  apply card_filter_general g g.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (Nat.prod_primeFactors_dvd g)
    (fun p s => ¬ ((p : ℤ) ∣ (a0 : ℤ) + qq * s) ∧ ¬ ((p : ℤ) ∣ (b0 : ℤ) + rr * s))
  · intro p _ s
    have e1 : (a0 : ℤ) + qq * ((s + p : ℕ) : ℤ) = ((a0 : ℤ) + qq * s) + qq * p := by
      push_cast
      ring
    have e2 : (b0 : ℤ) + rr * ((s + p : ℕ) : ℤ) = ((b0 : ℤ) + rr * s) + rr * p := by
      push_cast
      ring
    show (¬ ((p : ℤ) ∣ (a0 : ℤ) + qq * ((s + p : ℕ) : ℤ)) ∧
      ¬ ((p : ℤ) ∣ (b0 : ℤ) + rr * ((s + p : ℕ) : ℤ))) =
      (¬ ((p : ℤ) ∣ (a0 : ℤ) + qq * s) ∧ ¬ ((p : ℤ) ∣ (b0 : ℤ) + rr * s))
    rw [e1, e2, dvd_add_left (Dvd.intro_left (qq : ℤ) rfl : (p : ℤ) ∣ (qq : ℤ) * p),
      dvd_add_left (Dvd.intro_left (rr : ℤ) rfl : (p : ℤ) ∣ (rr : ℤ) * p)]
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpgN : p ∣ g := Nat.dvd_of_mem_primeFactors hp
    apply bad_count p hpp a0 b0 qq rr hco
    by_cases hdiv : p ∣ qq * rr * n.natAbs
    · exact Or.inl (if_pos hdiv)
    · refine Or.inr ⟨if_neg hdiv, ?_, ?_, ?_⟩
      · exact fun h => hdiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right h rr) _)
      · exact fun h => hdiv (Dvd.dvd.mul_right (Dvd.dvd.mul_left h qq) _)
      · intro h
        apply hdiv
        apply Dvd.dvd.mul_left
        have hpL : (p : ℤ) ∣ ((qq * rr * g : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left hpgN _)
        have h1 := dvd_sub h (dvd_trans hpL hd0)
        have e : (a0 : ℤ) * rr - (b0 : ℤ) * qq - ((a0 : ℤ) * rr - (b0 : ℤ) * qq - n) = n := by ring
        rw [e] at h1
        exact Int.natCast_dvd.1 h1


-- A ball of radius d on the unit circle has measure at most 2 d.
lemma vol_ball_le (y : UnitAddCircle) (d : ℝ) (hd : 0 ≤ d) :
    (MeasureTheory.volume (Metric.ball y d)).toReal ≤ 2 * d := by
  calc (MeasureTheory.volume (Metric.ball y d)).toReal
      ≤ (MeasureTheory.volume (Metric.closedBall y d)).toReal :=
        ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
          (MeasureTheory.measure_mono Metric.ball_subset_closedBall)
    _ = (ENNReal.ofReal (min 1 (2 * d))).toReal := by
        rw [AddCircle.volume_closedBall (T := 1) (x := y) d]
    _ ≤ 2 * d := by
        rw [ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]
        exact min_le_right _ _

-- Two balls overlap in measure at most twice the smaller radius, and not at all when far apart.
lemma ball_inter_le (y z : UnitAddCircle) (d e : ℝ) (hd : 0 ≤ d) (he : 0 ≤ e) :
    (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal ≤
      2 * min d e * (if dist y z < d + e then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]
    have h1 : (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal ≤ 2 * d :=
      (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.measure_mono Set.inter_subset_left)).trans (vol_ball_le y d hd)
    have h2 : (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal ≤ 2 * e :=
      (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.measure_mono Set.inter_subset_right)).trans (vol_ball_le z e he)
    rcases le_total d e with hle | hle
    · rw [min_eq_left hle]
      exact h1
    · rw [min_eq_right hle]
      exact h2
  · rw [mul_zero]
    have hdisj : Disjoint (Metric.ball y d) (Metric.ball z e) :=
      Metric.ball_disjoint_ball (not_lt.1 h)
    rw [Set.disjoint_iff_inter_eq_empty.1 hdisj]
    simp

-- Summing a nonnegative function over the points of order q is at most summing it over
-- the fractions a / q with a below q and coprime to q.
lemma sum_order_le (q : ℕ) (hq : 0 < q) (F : UnitAddCircle → ℝ) (hF : ∀ y, 0 ≤ F y) :
    ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset, F y ≤
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        F ((((a : ℝ) / (q : ℝ) : ℝ)) : UnitAddCircle) := by
  have hsub : (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset ⊆
      ((range q).filter (fun a => Nat.Coprime a q)).image
        (fun a : ℕ => ((((a : ℝ) / (q : ℝ) : ℝ)) : UnitAddCircle)) := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    obtain ⟨m, hm, hg, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hq).1 hy
    rw [mem_image]
    exact ⟨m, mem_filter.2 ⟨mem_range.2 hm, hg⟩, by rw [mul_one]⟩
  calc ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset, F y
      ≤ ∑ y ∈ ((range q).filter (fun a => Nat.Coprime a q)).image
          (fun a : ℕ => ((((a : ℝ) / (q : ℝ) : ℝ)) : UnitAddCircle)), F y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hF y)
    _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          F ((((a : ℝ) / (q : ℝ) : ℝ)) : UnitAddCircle) :=
        Finset.sum_image_le_of_nonneg (fun y _ => hF y)

-- If two fractions are closer than eta on the circle, the numerator of their difference is
-- congruent modulo the least common multiple to an integer of absolute value below N.
lemma dist_lt_imp (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr) (a b : ℕ) (η : ℝ)
    (N : ℕ) (hN : η * ((qq * rr * g : ℕ) : ℝ) ≤ N)
    (hd : dist ((((a : ℝ) / ((qq * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle)
      ((((b : ℝ) / ((rr * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle) < η) :
    ∃ k ∈ range N, (((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ) ∨
      ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hqR : (0 : ℝ) < qq := by exact_mod_cast hq
  have hrR : (0 : ℝ) < rr := by exact_mod_cast hr
  have hLR : (0 : ℝ) < ((qq * rr * g : ℕ) : ℝ) := by
    push_cast
    positivity
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hd
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = round ((a : ℝ) / ((qq * g : ℕ) : ℝ) - (b : ℝ) / ((rr * g : ℕ) : ℝ)) :=
    ⟨_, rfl⟩
  rw [← hK] at hd
  have hreal : ((a : ℝ) / ((qq * g : ℕ) : ℝ) - (b : ℝ) / ((rr * g : ℕ) : ℝ) - (K : ℝ)) *
      ((qq * rr * g : ℕ) : ℝ) =
      (((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ) : ℤ) : ℝ) := by
    push_cast
    field_simp
  have habs : |(((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ) : ℤ) : ℝ)| < N := by
    rw [← hreal, abs_mul, abs_of_pos hLR]
    calc |(a : ℝ) / ((qq * g : ℕ) : ℝ) - (b : ℝ) / ((rr * g : ℕ) : ℝ) - (K : ℝ)| *
          ((qq * rr * g : ℕ) : ℝ) < η * ((qq * rr * g : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_right hd hLR
      _ ≤ N := hN
  have habsZ : |(a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ)| < (N : ℤ) := by
    exact_mod_cast habs
  refine ⟨((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ)).natAbs, ?_, ?_⟩
  · rw [mem_range]
    have h1 := Int.natCast_natAbs ((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ))
    omega
  · rcases Int.natAbs_eq ((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ)) with h | h
    · left
      rw [← h]
      exact ⟨K, by ring⟩
    · right
      have h2 : -((((a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ)).natAbs : ℕ) : ℤ) =
          (a : ℤ) * rr - (b : ℤ) * qq - K * ((qq * rr * g : ℕ) : ℤ) := by
        rw [h]
        simp
      rw [h2]
      exact ⟨K, by ring⟩

-- The number of solutions as a double sum over units.
lemma sol_card_eq_sum (qq rr g : ℕ) (n : ℤ) :
    ((SolSet qq rr g n).card : ℝ) =
      ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
        ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
          (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - n then (1 : ℝ) else 0) := by
  unfold SolSet
  rw [Finset.natCast_card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]
  by_cases ha : Nat.Coprime a (qq * g)
  · rw [if_pos ha]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : Nat.Coprime b (rr * g)
    · rw [if_pos hb]
      by_cases hdv : ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - n
      · rw [if_pos hdv, if_pos ⟨ha, hb, hdv⟩]
      · rw [if_neg hdv, if_neg (fun h => hdv h.2.2)]
    · rw [if_neg hb, if_neg (fun h => hb h.2.1)]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => ha h.1)]

-- Close pairs of points of orders q and r are counted by solutions of congruences.
lemma pairs_count_le (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr) (η : ℝ) (N : ℕ)
    (hN : η * ((qq * rr * g : ℕ) : ℝ) ≤ N) :
    ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hq hg)).toFinset,
      ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hr hg)).toFinset,
        (if dist y z < η then (1 : ℝ) else 0) ≤
      ∑ k ∈ range N, (((SolSet qq rr g (k : ℤ)).card : ℝ) + ((SolSet qq rr g (-(k : ℤ))).card : ℝ)) := by
  have hite : ∀ (y z : UnitAddCircle), (0 : ℝ) ≤ (if dist y z < η then (1 : ℝ) else 0) := by
    intro y z
    split_ifs <;> norm_num
  have h1 : ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ))
        (Nat.mul_pos hq hg)).toFinset,
      ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hr hg)).toFinset,
        (if dist y z < η then (1 : ℝ) else 0) ≤
      ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
        ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
          (if dist ((((a : ℝ) / ((qq * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle)
            ((((b : ℝ) / ((rr * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle) < η then (1 : ℝ) else 0) := by
    refine (sum_order_le (qq * g) (Nat.mul_pos hq hg) _
      (fun y => Finset.sum_nonneg (fun z _ => hite y z))).trans ?_
    apply Finset.sum_le_sum
    intro a _
    exact sum_order_le (rr * g) (Nat.mul_pos hr hg) _ (fun z => hite _ z)
  have h2 : ∀ a b : ℕ,
      (if dist ((((a : ℝ) / ((qq * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle)
        ((((b : ℝ) / ((rr * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle) < η then (1 : ℝ) else 0) ≤
      ∑ k ∈ range N,
        ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ) then (1 : ℝ) else 0) +
          (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
            then (1 : ℝ) else 0)) := by
    intro a b
    have hnn : ∀ k ∈ range N, (0 : ℝ) ≤
        ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ) then (1 : ℝ) else 0) +
          (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
            then (1 : ℝ) else 0)) := by
      intro k _
      apply add_nonneg <;> split_ifs <;> norm_num
    split_ifs with hd
    · obtain ⟨k, hk, hdvd⟩ := dist_lt_imp qq rr g hg hq hr a b η N hN hd
      refine le_trans ?_ (Finset.single_le_sum hnn hk)
      rcases hdvd with h | h
      · rw [if_pos h]
        have : (0 : ℝ) ≤ (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
            then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        linarith
      · rw [if_pos h]
        have : (0 : ℝ) ≤ (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ)
            then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        linarith
    · exact Finset.sum_nonneg hnn
  refine h1.trans ?_
  calc ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
        ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
          (if dist ((((a : ℝ) / ((qq * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle)
            ((((b : ℝ) / ((rr * g : ℕ) : ℝ) : ℝ)) : UnitAddCircle) < η then (1 : ℝ) else 0)
      ≤ ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
        ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
          ∑ k ∈ range N,
            ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ)
                then (1 : ℝ) else 0) +
              (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
                then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h2 a b))
    _ = ∑ k ∈ range N, (((SolSet qq rr g (k : ℤ)).card : ℝ) +
          ((SolSet qq rr g (-(k : ℤ))).card : ℝ)) := by
        simp only [sol_card_eq_sum]
        calc ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
              ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
                ∑ k ∈ range N,
                  ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ)
                      then (1 : ℝ) else 0) +
                    (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
                      then (1 : ℝ) else 0))
            = ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
              ∑ k ∈ range N,
                ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
                  ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ)
                      then (1 : ℝ) else 0) +
                    (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
                      then (1 : ℝ) else 0)) :=
              Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
          _ = ∑ k ∈ range N,
              ∑ a ∈ (range (qq * g)).filter (fun a => Nat.Coprime a (qq * g)),
                ∑ b ∈ (range (rr * g)).filter (fun b => Nat.Coprime b (rr * g)),
                  ((if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (k : ℤ)
                      then (1 : ℝ) else 0) +
                    (if ((qq * rr * g : ℕ) : ℤ) ∣ (a : ℤ) * rr - (b : ℤ) * qq - (-(k : ℤ))
                      then (1 : ℝ) else 0)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              simp only [Finset.sum_add_distrib]


lemma X_bounds (p : ℕ) (hp : p.Prime) :
    (0 : ℝ) < 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 ∧ (2 : ℝ) ≤ p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have h0 : 0 < 1 / (p : ℝ) := by positivity
  exact ⟨by linarith, by linarith, hp2⟩

-- The solution count in real form: g times a product of local densities.
lemma sol_card_real (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr)
    (hco : Nat.Coprime qq rr) (n : ℤ) :
    ((SolSet qq rr g n).card : ℝ) ≤ (if Nat.Coprime n.natAbs (qq * rr) then (1 : ℝ) else 0) *
      ((g : ℝ) * ∏ p ∈ g.primeFactors, ((1 - 1 / (p : ℝ)) *
        (if p ∣ qq * rr * n.natAbs then 1 else (1 - 1 / (p : ℝ))))) := by
  have hRnn : (0 : ℝ) ≤ (g : ℝ) * ∏ p ∈ g.primeFactors, ((1 - 1 / (p : ℝ)) *
      (if p ∣ qq * rr * n.natAbs then 1 else (1 - 1 / (p : ℝ)))) := by
    apply mul_nonneg (Nat.cast_nonneg g)
    apply Finset.prod_nonneg
    intro p hp
    obtain ⟨hpos, _, _⟩ := X_bounds p (Nat.prime_of_mem_primeFactors hp)
    apply mul_nonneg hpos.le
    split_ifs
    · norm_num
    · exact hpos.le
  rcases (SolSet qq rr g n).eq_empty_or_nonempty with he | ⟨ab, hab⟩
  · rw [he]
    simp only [card_empty, Nat.cast_zero]
    apply mul_nonneg _ hRnn
    split_ifs <;> norm_num
  · rw [if_pos (sol_coprime qq rr g hco n ab hab), one_mul]
    have h := sol_card_le qq rr g hg hq hr hco n
    have hcast : ((SolSet qq rr g n).card : ℝ) ≤ (((g / ∏ p ∈ g.primeFactors, p) *
        ∏ p ∈ g.primeFactors, (p - (if p ∣ qq * rr * n.natAbs then 1 else 2)) : ℕ) : ℝ) := by
      exact_mod_cast h
    refine hcast.trans ?_
    have hrad : (∏ p ∈ g.primeFactors, p) ∣ g := Nat.prod_primeFactors_dvd g
    have hradR : ((∏ p ∈ g.primeFactors, p : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.prod_pos
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)).ne'
    rw [Nat.cast_mul, Nat.cast_div hrad hradR, Nat.cast_prod, Nat.cast_prod, div_mul_eq_mul_div,
      mul_div_assoc, ← Finset.prod_div_distrib]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg g)
    apply Finset.prod_le_prod
    · intro p _
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro p hp
      obtain ⟨hpos, hle1, hp2⟩ := X_bounds p (Nat.prime_of_mem_primeFactors hp)
      have hp2N : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      by_cases hdv : p ∣ qq * rr * n.natAbs
      · rw [if_pos hdv, if_pos hdv, mul_one, Nat.cast_sub (by omega), Nat.cast_one, sub_div,
          div_self hp0]
      · rw [if_neg hdv, if_neg hdv, Nat.cast_sub hp2N, Nat.cast_ofNat, sub_div, div_self hp0]
        have e : (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) = 1 - 2 / p + (1 / (p : ℝ)) ^ 2 := by ring
        rw [e]
        nlinarith [sq_nonneg (1 / (p : ℝ))]

-- The local weight is controlled by the totient ratios of g and by k / phi(k).
lemma weight_le (qq rr g k : ℕ) (hk : 0 < k) :
    ∏ p ∈ g.primeFactors, ((1 - 1 / (p : ℝ)) *
        (if p ∣ qq * rr * k then 1 else (1 - 1 / (p : ℝ)))) ≤
      (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) * (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1)) * HH k := by
  have hstep : ∏ p ∈ g.primeFactors, (if p ∣ k then (1 - 1 / (p : ℝ))⁻¹ else 1) ≤ HH k := by
    rw [← Finset.prod_filter]
    unfold HH
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      rw [mem_filter] at hp
      exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2, hk.ne'⟩
    · intro p hp
      have h1 := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1)).1
      linarith
    · intro p hp _
      exact (inv_factor_bounds p (Nat.prime_of_mem_primeFactors hp)).1
  have hG0 : (0 : ℝ) ≤ (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
      (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1)) := by
    have h1 : (0 : ℝ) ≤ ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg (fun p hp => (X_bounds p (Nat.prime_of_mem_primeFactors hp)).1.le)
    have h2 : (0 : ℝ) ≤ ∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have hb := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors hp)).1
      split_ifs
      · linarith
      · norm_num
    exact mul_nonneg (mul_nonneg h1 h1) h2
  calc ∏ p ∈ g.primeFactors, ((1 - 1 / (p : ℝ)) *
        (if p ∣ qq * rr * k then 1 else (1 - 1 / (p : ℝ))))
      ≤ ∏ p ∈ g.primeFactors, ((1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) *
          (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1) *
          (if p ∣ k then (1 - 1 / (p : ℝ))⁻¹ else 1)) := by
        apply Finset.prod_le_prod
        · intro p hp
          obtain ⟨hpos, _, _⟩ := X_bounds p (Nat.prime_of_mem_primeFactors hp)
          apply mul_nonneg hpos.le
          split_ifs
          · norm_num
          · exact hpos.le
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          obtain ⟨hpos, hle1, _⟩ := X_bounds p hpp
          have hxu : (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
          have hu := (inv_factor_bounds p hpp).1
          by_cases h1 : p ∣ qq * rr
          · have hd : p ∣ qq * rr * k := Dvd.dvd.mul_right h1 k
            rw [if_pos hd, if_pos h1, mul_one]
            by_cases h2 : p ∣ k
            · rw [if_pos h2]
              have e : (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ *
                  (1 - 1 / (p : ℝ))⁻¹ = 1 := by
                rw [mul_assoc, mul_assoc, ← mul_assoc (1 - 1 / (p : ℝ)) ((1 - 1 / (p : ℝ))⁻¹), hxu,
                  one_mul, hxu]
              rw [e]
              exact hle1
            · rw [if_neg h2, mul_one, mul_assoc, hxu, mul_one]
          · by_cases h2 : p ∣ k
            · have hd : p ∣ qq * rr * k := Dvd.dvd.mul_left h2 _
              rw [if_pos hd, if_neg h1, if_pos h2, mul_one, mul_one, mul_assoc, hxu, mul_one]
            · have hd : ¬ p ∣ qq * rr * k := fun h => by
                rcases (hpp.dvd_mul).1 h with h3 | h3
                · exact h1 h3
                · exact h2 h3
              rw [if_neg hd, if_neg h1, if_neg h2, mul_one, mul_one]
    _ = (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) * (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1)) *
          ∏ p ∈ g.primeFactors, (if p ∣ k then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
        simp only [Finset.prod_mul_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep hG0

-- Summing the solution counts over the shifts k and -k below N.
lemma sol_sum_le (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr)
    (hco : Nat.Coprime qq rr) (N : ℕ) :
    ∑ k ∈ range N, (((SolSet qq rr g (k : ℤ)).card : ℝ) +
        ((SolSet qq rr g (-(k : ℤ))).card : ℝ)) ≤
      2 * ((if qq * rr = 1 then (1 : ℝ) else 0) *
        ((g : ℝ) * ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)))) +
      2 * ((g : ℝ) * ((∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1))) *
        ∑ k ∈ Ioc 0 (N - 1), FF (qq * rr) k) := by
  obtain ⟨GM, hGM⟩ : ∃ GM : ℝ, GM = (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1)) := ⟨_, rfl⟩
  rw [← hGM]
  have hGM0 : 0 ≤ GM := by
    rw [hGM]
    have h1 : (0 : ℝ) ≤ ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg (fun p hp => (X_bounds p (Nat.prime_of_mem_primeFactors hp)).1.le)
    have h2 : (0 : ℝ) ≤ ∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have hb := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors hp)).1
      split_ifs
      · linarith
      · norm_num
    exact mul_nonneg (mul_nonneg h1 h1) h2
  have hgR : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ k, f k = ((SolSet qq rr g (k : ℤ)).card : ℝ) +
      ((SolSet qq rr g (-(k : ℤ))).card : ℝ) := ⟨_, fun _ => rfl⟩
  simp only [← hf]
  have hf0 : ∀ k, 0 ≤ f k := fun k => by
    rw [hf]
    positivity
  -- the term k = 0
  have hzero : f 0 ≤ 2 * ((if qq * rr = 1 then (1 : ℝ) else 0) *
      ((g : ℝ) * ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)))) := by
    rw [hf]
    have h1 := sol_card_real qq rr g hg hq hr hco 0
    simp only [Int.natAbs_zero, Nat.mul_zero, dvd_zero, if_true, mul_one,
      Nat.coprime_zero_left] at h1
    simp only [Nat.cast_zero, neg_zero]
    linarith
  -- the terms k at least 1
  have hpos : ∀ k ∈ Ioc 0 (N - 1), f k ≤ 2 * ((g : ℝ) * GM * FF (qq * rr) k) := by
    intro k hk
    have hk0 : 0 < k := (mem_Ioc.1 hk).1
    have hW := weight_le qq rr g k hk0
    rw [← hGM] at hW
    have hbound : ∀ n : ℤ, n.natAbs = k →
        ((SolSet qq rr g n).card : ℝ) ≤ (g : ℝ) * GM * FF (qq * rr) k := by
      intro n hn
      have h1 := sol_card_real qq rr g hg hq hr hco n
      rw [hn] at h1
      refine h1.trans ?_
      unfold FF
      by_cases hc : Nat.Coprime k (qq * rr)
      · rw [if_pos hc, if_pos hc, one_mul]
        have e : (g : ℝ) * GM * HH k = (g : ℝ) * (GM * HH k) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hW hgR
      · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]
    rw [hf]
    have h1 := hbound (k : ℤ) (Int.natAbs_natCast k)
    have h2 := hbound (-(k : ℤ)) (by rw [Int.natAbs_neg, Int.natAbs_natCast])
    linarith
  have hsub : range N ⊆ insert 0 (Ioc 0 (N - 1)) := by
    intro k hk
    rw [mem_range] at hk
    rw [mem_insert, mem_Ioc]
    omega
  calc ∑ k ∈ range N, f k ≤ ∑ k ∈ insert 0 (Ioc 0 (N - 1)), f k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf0 k)
    _ = f 0 + ∑ k ∈ Ioc 0 (N - 1), f k := by
        rw [Finset.sum_insert (by simp)]
    _ ≤ 2 * ((if qq * rr = 1 then (1 : ℝ) else 0) *
          ((g : ℝ) * ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)))) +
        ∑ k ∈ Ioc 0 (N - 1), 2 * ((g : ℝ) * GM * FF (qq * rr) k) :=
        add_le_add hzero (Finset.sum_le_sum hpos)
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]


-- A termwise identity between local factors, for a nonzero real x.
lemma term_id (x : ℝ) (hx : x ≠ 0) (A B C c : Prop) [Decidable A] [Decidable B] [Decidable C]
    [Decidable c] (hBC : ¬ (B ∧ C)) :
    (if A then x else 1) * (if A then x else 1) *
        (if A then (if B ∨ C then x⁻¹ else 1) else 1) *
        (if B ∨ C then (if c then x else 1) else 1) =
      (if B ∨ A then x else 1) * (if C ∨ A then x else 1) *
        (if B ∨ C then (if c then 1 else x⁻¹) else 1) := by
  by_cases hB : B
  · by_cases hC : C
    · exact absurd ⟨hB, hC⟩ hBC
    · by_cases hA : A <;> by_cases hc : c <;> simp [hA, hB, hC, hc] <;> try field_simp
  · by_cases hA : A <;> by_cases hC : C <;> by_cases hc : c <;> simp [hA, hB, hC, hc] <;>
      try field_simp

-- Prime factors of a divisor, as a filter of the prime factors of a multiple.
lemma pf_filter (n M : ℕ) (hM : M ≠ 0) (hn : n ∣ M) :
    n.primeFactors = M.primeFactors.filter (fun p => p ∣ n) := by
  ext p
  simp only [Nat.mem_primeFactors, mem_filter]
  constructor
  · rintro ⟨hp, hd, _⟩
    exact ⟨⟨hp, dvd_trans hd hn, hM⟩, hd⟩
  · rintro ⟨⟨hp, _, _⟩, hd⟩
    refine ⟨hp, hd, ?_⟩
    rintro rfl
    exact hM (Nat.eq_zero_of_zero_dvd hn)

-- The totient ratio as a product over prime factors.
lemma totient_ratio (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h : ((Nat.totient n : ℚ) : ℝ) =
      ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
    rw [Nat.totient_eq_mul_prod_factors n]
  push_cast at h
  rw [h]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_div_cancel_left₀ _ hnR]
  exact Finset.prod_congr rfl (fun p _ => by rw [one_div])

-- The product identity matching the local densities with the totient ratios.
lemma prod_identity (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr)
    (hco : Nat.Coprime qq rr) (c : ℕ → Prop) [DecidablePred c] :
    (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) * (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1)) *
        (∏ p ∈ (qq * rr).primeFactors.filter c, (1 - 1 / (p : ℝ))) =
      (∏ p ∈ (qq * g).primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ (rr * g).primeFactors, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ (qq * rr).primeFactors.filter (fun p => ¬ c p), (1 - 1 / (p : ℝ))⁻¹) := by
  have hM : qq * rr * g ≠ 0 := (Nat.mul_pos (Nat.mul_pos hq hr) hg).ne'
  have d1 : g ∣ qq * rr * g := Dvd.intro_left _ rfl
  have d2 : qq * rr ∣ qq * rr * g := Dvd.intro _ rfl
  have d3 : qq * g ∣ qq * rr * g := ⟨rr, by ring⟩
  have d4 : rr * g ∣ qq * rr * g := ⟨qq, by ring⟩
  rw [Finset.prod_filter, Finset.prod_filter, pf_filter g _ hM d1, pf_filter (qq * rr) _ hM d2,
    pf_filter (qq * g) _ hM d3, pf_filter (rr * g) _ hM d4]
  simp only [Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hx : (1 - 1 / (p : ℝ)) ≠ 0 := (X_bounds p hpp).1.ne'
  have hBC : ¬ (p ∣ qq ∧ p ∣ rr) := fun h => not_dvd_of_coprime p qq rr hpp hco h.2 h.1
  have key := term_id (1 - 1 / (p : ℝ)) hx (p ∣ g) (p ∣ qq) (p ∣ rr) (c p) hBC
  simp only [hpp.dvd_mul]
  by_cases hc : c p
  · simp only [hc, if_true, not_true_eq_false, if_false] at key ⊢
    exact key
  · simp only [hc, if_false, not_false_eq_true, if_true] at key ⊢
    exact key


-- The sieve constant.
noncomputable def CS : ℝ :=
  (2 * (Real.log 4 + 4) + 1) * (Real.exp 2 * Real.exp (4 - Real.log (Real.log 2)))

lemma CS_pos : 0 < CS := by
  unfold CS
  have h : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : (0 : ℝ) < Real.exp 2 * Real.exp (4 - Real.log (Real.log 2)) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have h3 : (0 : ℝ) < 2 * (Real.log 4 + 4) + 1 := by linarith
  exact mul_pos h3 h2

-- The general overlap estimate: for q = q1 g and r = r1 g with q1, r1 coprime and any radii
-- d, e, the total measure of the pairwise intersections of the balls of radius d around the
-- points of order q with the balls of radius e around the points of order r.
theorem overlap_general (qq rr g : ℕ) (hg : 0 < g) (hq : 0 < qq) (hr : 0 < rr)
    (hco : Nat.Coprime qq rr) (d e : ℝ) (hd : 0 ≤ d) (he : 0 ≤ e) :
    ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hq hg)).toFinset,
      ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hr hg)).toFinset,
        (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal ≤
      2 * min d e * (2 * ((if qq * rr = 1 then (1 : ℝ) else 0) * (Nat.totient g : ℝ)) +
        2 * (CS * ((d + e) * ((qq * rr * g : ℕ) : ℝ)) * (g : ℝ) *
          ((Nat.totient (qq * g) : ℝ) / ((qq * g : ℕ) : ℝ)) *
          ((Nat.totient (rr * g) : ℝ) / ((rr * g : ℕ) : ℝ)) *
          ∏ p ∈ (qq * rr).primeFactors.filter
            (fun p : ℕ => (d + e) * ((qq * rr * g : ℕ) : ℝ) ≤ p), (1 - 1 / (p : ℝ))⁻¹)) := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈(d + e) * ((qq * rr * g : ℕ) : ℝ)⌉₊ := ⟨_, rfl⟩
  have hx0 : 0 ≤ (d + e) * ((qq * rr * g : ℕ) : ℝ) := by positivity
  have hN : (d + e) * ((qq * rr * g : ℕ) : ℝ) ≤ N := by
    rw [hNdef]
    exact Nat.le_ceil _
  have hN1 : ((N - 1 : ℕ) : ℝ) ≤ (d + e) * ((qq * rr * g : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]
      simpa using hx0
    · have hlt := Nat.ceil_lt_add_one hx0
      rw [← hNdef] at hlt
      rw [Nat.cast_sub hpos, Nat.cast_one]
      linarith
  have hmin0 : 0 ≤ 2 * min d e := mul_nonneg (by norm_num) (le_min hd he)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  -- from measures to counts
  have s1 : ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ))
        (Nat.mul_pos hq hg)).toFinset,
      ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hr hg)).toFinset,
        (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal ≤
      2 * min d e * ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ))
        (Nat.mul_pos hq hg)).toFinset,
      ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) (Nat.mul_pos hr hg)).toFinset,
        (if dist y z < d + e then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    exact ball_inter_le y z d e hd he
  have s2 := pairs_count_le qq rr g hg hq hr (d + e) N hN
  have s3 := sol_sum_le qq rr g hg hq hr hco N
  -- names for the products
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨M1, hM1⟩ : ∃ M1 : ℝ, M1 =
      ∏ p ∈ g.primeFactors, (if p ∣ qq * rr then (1 - 1 / (p : ℝ))⁻¹ else 1) := ⟨_, rfl⟩
  obtain ⟨Tle, hTle⟩ : ∃ T : ℝ, T =
      ∏ p ∈ (qq * rr).primeFactors.filter (fun p => p ≤ N - 1), (1 - 1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Tgt, hTgt⟩ : ∃ T : ℝ, T = ∏ p ∈ (qq * rr).primeFactors.filter
      (fun p : ℕ => (d + e) * ((qq * rr * g : ℕ) : ℝ) ≤ p), (1 - 1 / (p : ℝ))⁻¹ := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact Finset.prod_nonneg (fun p hp => (X_bounds p (Nat.prime_of_mem_primeFactors hp)).1.le)
  have hM10 : 0 ≤ M1 := by
    rw [hM1]
    apply Finset.prod_nonneg
    intro p hp
    have hb := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors hp)).1
    split_ifs
    · linarith
    · norm_num
  have hTgt0 : 0 ≤ Tgt := by
    rw [hTgt]
    apply Finset.prod_nonneg
    intro p hp
    have hb := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1)).1
    linarith
  -- the sieve
  have s4 : ∑ k ∈ Ioc 0 (N - 1), FF (qq * rr) k ≤ CS * ((N - 1 : ℕ) : ℝ) * Tle := by
    rcases Nat.eq_zero_or_pos (N - 1) with h0 | hpos
    · rw [h0]
      simp
    · rw [hTle]
      unfold CS
      exact sieve_bound (qq * rr) (N - 1) (Nat.mul_pos hq hr) hpos
  -- the product identity
  have s5 := prod_identity qq rr g hg hq hr hco (fun p => p ≤ N - 1)
  have hfilt : (qq * rr).primeFactors.filter (fun p => ¬ (p ≤ N - 1)) =
      (qq * rr).primeFactors.filter
        (fun p : ℕ => (d + e) * ((qq * rr * g : ℕ) : ℝ) ≤ p) := by
    apply Finset.filter_congr
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    constructor
    · intro h
      have hNp : N ≤ p := by omega
      exact hN.trans (by exact_mod_cast hNp)
    · intro h hle
      have hNp : N ≤ p := by
        rw [hNdef]
        exact Nat.ceil_le.2 h
      omega
  rw [hfilt, ← hG, ← hM1, ← hTle, ← hTgt, ← totient_ratio (qq * g) (Nat.mul_pos hq hg),
    ← totient_ratio (rr * g) (Nat.mul_pos hr hg)] at s5
  have hgG : (g : ℝ) * G = (Nat.totient g : ℝ) := by
    rw [hG, ← totient_ratio g hg]
    field_simp
  rw [← hG, ← hM1] at s3
  -- assembling
  obtain ⟨Pq, hPq⟩ : ∃ P : ℝ, P = (Nat.totient (qq * g) : ℝ) / ((qq * g : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Pr, hPr⟩ : ∃ P : ℝ, P = (Nat.totient (rr * g) : ℝ) / ((rr * g : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hPq, ← hPr] at s5 ⊢
  rw [← hTgt]
  have hPq0 : 0 ≤ Pq := by
    rw [hPq]
    positivity
  have hPr0 : 0 ≤ Pr := by
    rw [hPr]
    positivity
  have hGM0 : 0 ≤ G * G * M1 := mul_nonneg (mul_nonneg hG0 hG0) hM10
  have key : (g : ℝ) * (G * G * M1) * ∑ k ∈ Ioc 0 (N - 1), FF (qq * rr) k ≤
      CS * ((d + e) * ((qq * rr * g : ℕ) : ℝ)) * (g : ℝ) * Pq * Pr * Tgt := by
    calc (g : ℝ) * (G * G * M1) * ∑ k ∈ Ioc 0 (N - 1), FF (qq * rr) k
        ≤ (g : ℝ) * (G * G * M1) * (CS * ((N - 1 : ℕ) : ℝ) * Tle) :=
          mul_le_mul_of_nonneg_left s4 (mul_nonneg hgR.le hGM0)
      _ = CS * ((N - 1 : ℕ) : ℝ) * (g : ℝ) * (G * G * M1 * Tle) := by ring
      _ = CS * ((N - 1 : ℕ) : ℝ) * (g : ℝ) * (Pq * Pr * Tgt) := by rw [s5]
      _ ≤ CS * ((d + e) * ((qq * rr * g : ℕ) : ℝ)) * (g : ℝ) * (Pq * Pr * Tgt) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg hPq0 hPr0) hTgt0)
          apply mul_le_mul_of_nonneg_right _ hgR.le
          exact mul_le_mul_of_nonneg_left hN1 CS_pos.le
      _ = CS * ((d + e) * ((qq * rr * g : ℕ) : ℝ)) * (g : ℝ) * Pq * Pr * Tgt := by ring
  refine s1.trans (mul_le_mul_of_nonneg_left ?_ hmin0)
  refine s2.trans (s3.trans ?_)
  rw [hgG]
  linarith


-- The approximation set as a finite union of balls.
lemma approx_biUnion (q : ℕ) (hq : 0 < q) (d : ℝ) :
    approxAddOrderOf UnitAddCircle q d =
      ⋃ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset,
        Metric.ball y d := by
  unfold approxAddOrderOf
  rw [Metric.thickening_eq_biUnion_ball]
  ext x
  simp

-- The measure of the intersection of two approximation sets is at most the sum over pairs.
lemma inter_le_sum (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (d e : ℝ) :
    (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q d ∩
        approxAddOrderOf UnitAddCircle r e)).toReal ≤
      ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset,
        ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hr).toFinset,
          (MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e)).toReal := by
  have hsub : approxAddOrderOf UnitAddCircle q d ∩ approxAddOrderOf UnitAddCircle r e ⊆
      ⋃ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset,
        ⋃ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hr).toFinset,
          (Metric.ball y d ∩ Metric.ball z e) := by
    rw [approx_biUnion q hq d, approx_biUnion r hr e]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨⟨y, hy, hxy⟩, ⟨z, hz, hxz⟩⟩ := hx
    exact ⟨y, hy, z, hz, hxy, hxz⟩
  have h1 : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q d ∩
      approxAddOrderOf UnitAddCircle r e) ≤
      ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset,
        ∑ z ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hr).toFinset,
          MeasureTheory.volume (Metric.ball y d ∩ Metric.ball z e) := by
    refine (MeasureTheory.measure_mono hsub).trans ?_
    refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro y _
    exact MeasureTheory.measure_biUnion_finset_le _ _
  have h2 := ENNReal.toReal_mono (by
    apply ENNReal.sum_ne_top.2
    intro y _
    apply ENNReal.sum_ne_top.2
    intro z _
    exact MeasureTheory.measure_ne_top _ _) h1
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_sum]
    intro z _
    exact MeasureTheory.measure_ne_top _ _
  · intro y _
    apply ENNReal.sum_ne_top.2
    intro z _
    exact MeasureTheory.measure_ne_top _ _

-- One inverse factor against one factor 1 + 1/p, with a square-summable correction.
lemma inv_factor_le (p : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ≤ (1 + 1 / (p : ℝ)) * Real.exp ((1 / ((p : ℝ) - 1)) ^ 2) := by
  obtain ⟨hpos, _, hp2⟩ := X_bounds p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hexp : 1 + (1 / ((p : ℝ) - 1)) ^ 2 ≤ Real.exp ((1 / ((p : ℝ) - 1)) ^ 2) := by
    linarith [Real.add_one_le_exp ((1 / ((p : ℝ) - 1)) ^ 2)]
  have hkey : 1 ≤ (1 + 1 / (p : ℝ)) * (1 + (1 / ((p : ℝ) - 1)) ^ 2) * (1 - 1 / (p : ℝ)) := by
    have e : (1 + 1 / (p : ℝ)) * (1 + (1 / ((p : ℝ) - 1)) ^ 2) * (1 - 1 / (p : ℝ)) =
        1 + (2 * (p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ (2 * (p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have h1 : (1 - 1 / (p : ℝ))⁻¹ ≤ (1 + 1 / (p : ℝ)) * (1 + (1 / ((p : ℝ) - 1)) ^ 2) := by
    rw [← one_div, div_le_iff₀ hpos]
    exact hkey
  exact h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))



-- The overlap estimate in the coordinates q = q1 g, r = r1 g.
lemma overlap_core (qq rr g : ℕ) (hg : 0 < g) (hqq0 : 0 < qq) (hrr0 : 0 < rr)
    (hco : Nat.Coprime qq rr) (hm1 : qq * rr ≠ 1) (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    (MeasureTheory.volume (approxAddOrderOf UnitAddCircle (qq * g) (a / ((qq * g : ℕ) : ℝ)) ∩
        approxAddOrderOf UnitAddCircle (rr * g) (b / ((rr * g : ℕ) : ℝ)))).toReal ≤
      8 * CS * Real.exp 2 * (((Nat.totient (qq * g) : ℝ) * a / ((qq * g : ℕ) : ℝ)) *
        ((Nat.totient (rr * g) : ℝ) * b / ((rr * g : ℕ) : ℝ))) *
        ∏ p ∈ (qq * rr).primeFactors.filter
          (fun p : ℕ => max (((rr * g : ℕ) : ℝ) * a) (((qq * g : ℕ) : ℝ) * b) / (g : ℝ) < p),
          (1 + 1 / (p : ℝ)) := by
  have hCS := CS_pos
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hQ0 : (0 : ℝ) < ((qq * g : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hqq0 hg
  have hR0 : (0 : ℝ) < ((rr * g : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hrr0 hg
  have hL0 : (0 : ℝ) < ((qq * rr * g : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hqq0 hrr0) hg
  have hLg : ((qq * rr * g : ℕ) : ℝ) * (g : ℝ) = ((qq * g : ℕ) : ℝ) * ((rr * g : ℕ) : ℝ) := by
    push_cast
    ring
  have h1 := inter_le_sum (qq * g) (rr * g) (Nat.mul_pos hqq0 hg) (Nat.mul_pos hrr0 hg)
    (a / ((qq * g : ℕ) : ℝ)) (b / ((rr * g : ℕ) : ℝ))
  have hd0 : 0 ≤ a / ((qq * g : ℕ) : ℝ) := div_nonneg ha0 hQ0.le
  have he0 : 0 ≤ b / ((rr * g : ℕ) : ℝ) := div_nonneg hb0 hR0.le
  have h2 := overlap_general qq rr g hg hqq0 hrr0 hco (a / ((qq * g : ℕ) : ℝ))
    (b / ((rr * g : ℕ) : ℝ)) hd0 he0
  rw [if_neg hm1, zero_mul, mul_zero, zero_add] at h2
  have h12 := h1.trans h2
  -- abstract the real quantities
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((qq * g : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((rr * g : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Lr, hLr⟩ : ∃ Lr : ℝ, Lr = ((qq * rr * g : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨fq, hfq⟩ : ∃ fq : ℝ, fq = (Nat.totient (qq * g) : ℝ) := ⟨_, rfl⟩
  obtain ⟨fr, hfr⟩ : ∃ fr : ℝ, fr = (Nat.totient (rr * g) : ℝ) := ⟨_, rfl⟩
  have hfq0 : 0 ≤ fq := by rw [hfq]; exact Nat.cast_nonneg _
  have hfr0 : 0 ≤ fr := by rw [hfr]; exact Nat.cast_nonneg _
  rw [← hQ, ← hR, ← hLr, ← hfq, ← hfr] at h12
  rw [← hQ, ← hR, ← hLr] at hLg
  rw [← hQ] at hQ0 hd0
  rw [← hR] at hR0 he0
  rw [← hLr] at hL0
  rw [← hQ, ← hR, ← hfq, ← hfr]
  have hP0 : (0 : ℝ) ≤ ∏ p ∈ (qq * rr).primeFactors.filter
      (fun p : ℕ => max (R * a) (Q * b) / (g : ℝ) < p), (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have hW0 : (0 : ℝ) ≤ (fq * a / Q) * (fr * b / R) := by positivity
  rcases (le_min hd0 he0).eq_or_lt with hmin | hmin
  · rw [← hmin, mul_zero, zero_mul] at h12
    exact h12.trans (mul_nonneg (mul_nonneg (by positivity) hW0) hP0)
  · have hdpos : 0 < a / Q := lt_of_lt_of_le hmin (min_le_left _ _)
    have hepos : 0 < b / R := lt_of_lt_of_le hmin (min_le_right _ _)
    have hD : max (R * a) (Q * b) / (g : ℝ) < (a / Q + b / R) * Lr := by
      have e1 : R * a / g = a / Q * Lr := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hgR.ne' hQ0.ne']
        linear_combination (-a) * hLg
      have e2 : Q * b / g = b / R * Lr := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hgR.ne' hR0.ne']
        linear_combination (-b) * hLg
      rw [← max_div_div_right hgR.le, e1, e2, add_mul]
      have p1 : 0 < a / Q * Lr := mul_pos hdpos hL0
      have p2 : 0 < b / R * Lr := mul_pos hepos hL0
      rcases le_total (a / Q * Lr) (b / R * Lr) with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    have hT : ∏ p ∈ (qq * rr).primeFactors.filter (fun p : ℕ => (a / Q + b / R) * Lr ≤ p),
          (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp 2 * ∏ p ∈ (qq * rr).primeFactors.filter
          (fun p : ℕ => max (R * a) (Q * b) / (g : ℝ) < p), (1 + 1 / (p : ℝ)) := by
      have hmemS : ∀ p ∈ (qq * rr).primeFactors.filter
          (fun p : ℕ => (a / Q + b / R) * Lr ≤ p), p.Prime :=
        fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
      calc ∏ p ∈ (qq * rr).primeFactors.filter (fun p : ℕ => (a / Q + b / R) * Lr ≤ p),
            (1 - 1 / (p : ℝ))⁻¹
          ≤ ∏ p ∈ (qq * rr).primeFactors.filter (fun p : ℕ => (a / Q + b / R) * Lr ≤ p),
            ((1 + 1 / (p : ℝ)) * Real.exp ((1 / ((p : ℝ) - 1)) ^ 2)) := by
            apply Finset.prod_le_prod
            · intro p hp
              have hb := (inv_factor_bounds p (hmemS p hp)).1
              linarith
            · intro p hp
              exact inv_factor_le p (hmemS p hp)
        _ = (∏ p ∈ (qq * rr).primeFactors.filter (fun p : ℕ => (a / Q + b / R) * Lr ≤ p),
            (1 + 1 / (p : ℝ))) * Real.exp (∑ p ∈ (qq * rr).primeFactors.filter
            (fun p : ℕ => (a / Q + b / R) * Lr ≤ p), (1 / ((p : ℝ) - 1)) ^ 2) := by
            rw [Finset.prod_mul_distrib, Real.exp_sum]
        _ ≤ (∏ p ∈ (qq * rr).primeFactors.filter
            (fun p : ℕ => max (R * a) (Q * b) / (g : ℝ) < p), (1 + 1 / (p : ℝ))) *
            Real.exp 2 := by
            apply mul_le_mul _ _ (Real.exp_pos _).le hP0
            · apply Finset.prod_le_prod_of_subset_of_one_le
              · intro p hp
                rw [mem_filter] at hp ⊢
                exact ⟨hp.1, lt_of_lt_of_le hD hp.2⟩
              · intro p _
                positivity
              · intro p _ _
                have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
                linarith
            · apply Real.exp_le_exp.2
              refine le_trans ?_ (sum_inv_sq_le (qq * rr))
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp
                have hpm := (mem_filter.1 hp).1
                have hpp := Nat.prime_of_mem_primeFactors hpm
                have hle := Nat.le_of_dvd (Nat.mul_pos hqq0 hrr0) (Nat.dvd_of_mem_primeFactors hpm)
                simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range]
                exact ⟨by omega, hpp⟩
              · intro p _ _
                positivity
        _ = _ := by ring
    have hminmax : min (a / Q) (b / R) * (a / Q + b / R) ≤ 2 * (a / Q * (b / R)) := by
      rcases le_total (a / Q) (b / R) with h | h
      · rw [min_eq_left h]
        nlinarith
      · rw [min_eq_right h]
        nlinarith
    obtain ⟨Tgt, hTgt⟩ : ∃ T : ℝ, T = ∏ p ∈ (qq * rr).primeFactors.filter
          (fun p : ℕ => (a / Q + b / R) * Lr ≤ p), (1 - 1 / (p : ℝ))⁻¹ := ⟨_, rfl⟩
    obtain ⟨Pp, hPp⟩ : ∃ T : ℝ, T = ∏ p ∈ (qq * rr).primeFactors.filter
          (fun p : ℕ => max (R * a) (Q * b) / (g : ℝ) < p), (1 + 1 / (p : ℝ)) := ⟨_, rfl⟩
    rw [← hTgt] at h12 hT
    rw [← hPp] at hT hP0 ⊢
    have hTgt0 : 0 ≤ Tgt := by
      rw [hTgt]
      apply Finset.prod_nonneg
      intro p hp
      have hb := (inv_factor_bounds p (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1)).1
      linarith
    refine h12.trans ?_
    have e1 : 2 * min (a / Q) (b / R) * (2 * (CS * ((a / Q + b / R) * Lr) * (g : ℝ) *
        (fq / Q) * (fr / R) * Tgt)) =
        (min (a / Q) (b / R) * (a / Q + b / R)) *
          (4 * CS * (Lr * (g : ℝ)) * (fq / Q) * (fr / R) * Tgt) := by ring
    rw [e1]
    have hbig0 : 0 ≤ 4 * CS * (Lr * (g : ℝ)) * (fq / Q) * (fr / R) * Tgt := by positivity
    refine (mul_le_mul_of_nonneg_right hminmax hbig0).trans ?_
    have e2 : 2 * (a / Q * (b / R)) * (4 * CS * (Lr * (g : ℝ)) * (fq / Q) * (fr / R) * Tgt) =
        8 * CS * ((fq * a / Q) * (fr * b / R)) * Tgt := by
      have hQne : Q ≠ 0 := hQ0.ne'
      have hRne : R ≠ 0 := hR0.ne'
      rw [hLg]
      field_simp
      ring
    rw [e2]
    have e3 : 8 * CS * Real.exp 2 * ((fq * a / Q) * (fr * b / R)) * Pp =
        8 * CS * ((fq * a / Q) * (fr * b / R)) * (Real.exp 2 * Pp) := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left hT (by positivity)

-- The overlap estimate for arbitrary nonnegative values a, b, with an explicit constant.
lemma overlap_all (q r : ℕ) (a b : ℝ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (a / q) ∩
        approxAddOrderOf UnitAddCircle r (b / r))).toReal ≤
      8 * CS * Real.exp 2 * (((Nat.totient q : ℝ) * a / q) * ((Nat.totient r : ℝ) * b / r)) *
        ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * a) ((q : ℝ) * b) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  obtain ⟨qq, hqq⟩ : ∃ qq, q = qq * Nat.gcd q r := ⟨q / Nat.gcd q r,
    (Nat.div_mul_cancel (Nat.gcd_dvd_left q r)).symm⟩
  obtain ⟨rr, hrr⟩ : ∃ rr, r = rr * Nat.gcd q r := ⟨r / Nat.gcd q r,
    (Nat.div_mul_cancel (Nat.gcd_dvd_right q r)).symm⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd q r := ⟨_, rfl⟩
  rw [← hgdef] at hqq hrr hg ⊢
  have hqq0 : 0 < qq := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.zero_mul] at hqq; omega)
  have hrr0 : 0 < rr := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.zero_mul] at hrr; omega)
  have hco : Nat.Coprime qq rr := by
    have h1 : Nat.gcd (qq * g) (rr * g) = g := by rw [← hqq, ← hrr, hgdef]
    rw [Nat.gcd_mul_right] at h1
    have h2 : Nat.gcd qq rr * g = 1 * g := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hg h2
  have hm1 : qq * rr ≠ 1 := by
    intro h
    have h1 : qq = 1 := Nat.eq_one_of_mul_eq_one_right h
    have h2 : rr = 1 := Nat.eq_one_of_mul_eq_one_left h
    apply hqr
    rw [hqq, hrr, h1, h2]
  have hdiv : q * r / g ^ 2 = qq * rr := by
    rw [hqq, hrr]
    have e : qq * g * (rr * g) = qq * rr * g ^ 2 := by ring
    rw [e]
    exact Nat.mul_div_cancel _ (pow_pos hg 2)
  rw [hdiv]
  clear hgdef hdiv hqr
  subst hqq
  subst hrr
  exact overlap_core qq rr g hg hqq0 hrr0 hco hm1 a b ha0 hb0

-- The overlap estimate of Pollington and Vaughan in the form used by Koukoulopoulos and Maynard.
theorem overlap_PV : ∃ C : ℝ, ∀ (q r : ℕ) (a b : ℝ), 0 < q → 0 < r → q ≠ r →
    0 ≤ a → a ≤ 1 / 2 → 0 ≤ b → b ≤ 1 / 2 →
    (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (a / q) ∩
        approxAddOrderOf UnitAddCircle r (b / r))).toReal ≤
      C * (((Nat.totient q : ℝ) * a / q) * ((Nat.totient r : ℝ) * b / r)) *
        ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * a) ((q : ℝ) * b) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) :=
  ⟨8 * CS * Real.exp 2, fun q r a b hq hr hqr ha0 _ hb0 _ => overlap_all q r a b hq hr hqr ha0 hb0⟩

end DSM

theorem OMA.solution : OMA.R_Erdos999_erdos_999_R1_H2_R1.H1 := DSM.overlap_PV
