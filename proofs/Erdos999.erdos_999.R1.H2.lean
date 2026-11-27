import OMAReductions.R_Erdos999_erdos_999_R1

-- Credit: @MrSeizy
-- The dyadic summation and the two estimates below are adapted from @chris01-dev's
-- reduction Erdos999.erdos_999.R1.H2.R1 and its merged H1 and H2 proofs.

-- Reduction of step H2 of Erdos999.erdos_999.R1 (the second moment bound) to the two inputs of
-- Koukoulopoulos and Maynard, Section 5: the overlap estimate of Pollington and Vaughan and their
-- Proposition 5.4. The dyadic summation argument is carried out here with scales 4^j and an
-- elementary bound for the sum of reciprocals of primes, so that Mertens is not needed.
namespace OMA.R_Erdos999_erdos_999_R1_H2_R1

open MeasureTheory Filter Set Metric
open scoped Topology

-- Odd primes below 2N+2 have reciprocal sum at most half the N-th harmonic number.
lemma sum_odd_primes_le (N : ℕ) :
    ∑ p ∈ Finset.range (2 * N + 2), (if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0) ≤
      (1 / 2) * ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  induction N with
  | zero =>
    simp only [Nat.zero_add, Finset.range_zero, Finset.sum_empty, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p hp
    have : p < 2 := Finset.mem_range.1 hp
    rw [if_neg]
    omega
  | succ N ih =>
    have e1 : 2 * (N + 1) + 2 = (2 * N + 2) + 1 + 1 := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) N, mul_add]
    have h2 : (if 3 ≤ 2 * N + 2 ∧ (2 * N + 2).Prime then (1 : ℝ) / ((2 * N + 2 : ℕ) : ℝ) else 0)
        = 0 := by
      rw [if_neg]
      rintro ⟨h3, hp⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ⟨N + 1, by ring⟩
      omega
    have h3 : (if 3 ≤ 2 * N + 2 + 1 ∧ (2 * N + 2 + 1).Prime
        then (1 : ℝ) / ((2 * N + 2 + 1 : ℕ) : ℝ) else 0) ≤ 1 / 2 * (1 / ((N : ℝ) + 1)) := by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      split_ifs
      · push_cast
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      · positivity
    rw [h2]
    linarith

-- Reciprocals of all primes below X, for X at most 2N+2.
lemma sum_primes_le (X N : ℕ) (hX : X ≤ 2 * N + 2) :
    ∑ p ∈ (Finset.range X).filter Nat.Prime, (1 : ℝ) / p ≤
      1 / 2 + (1 / 2) * ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  have hsub : (Finset.range X).filter Nat.Prime ⊆ (Finset.range (2 * N + 2)).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 hX)
  have h1 : ∑ p ∈ (Finset.range X).filter Nat.Prime, (1 : ℝ) / p ≤
      ∑ p ∈ (Finset.range (2 * N + 2)).filter Nat.Prime, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have h1 := h1.trans (le_of_eq (Finset.sum_filter _ _))
  have h2 : ∑ p ∈ Finset.range (2 * N + 2), (if p.Prime then (1 : ℝ) / p else 0) ≤
      ∑ p ∈ Finset.range (2 * N + 2), ((if p = 2 then (1 : ℝ) / 2 else 0) +
        (if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0)) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : p.Prime
    · rw [if_pos hp]
      rcases (Nat.succ_le_of_lt hp.one_lt).eq_or_lt with h | h
      · have h2 : p = 2 := h.symm
        rw [if_pos h2, if_neg (by omega), h2]
        norm_num
      · rw [if_neg (by omega), if_pos ⟨by omega, hp⟩]
        linarith
    · rw [if_neg hp]
      have : (0 : ℝ) ≤ if p = 2 then (1 : ℝ) / 2 else 0 := by split_ifs <;> norm_num
      have : (0 : ℝ) ≤ if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0 := by
        split_ifs <;> positivity
      linarith
  rw [Finset.sum_add_distrib] at h2
  have h3 : ∑ p ∈ Finset.range (2 * N + 2), (if p = 2 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  linarith [sum_odd_primes_le N]

-- The harmonic sum is at most 1 + log N.
lemma harmonic_sum_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
    unfold harmonic
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by rw [one_div])
  rw [e] at h
  exact h

-- Reciprocals of primes below 4^(j+1): the exponential is at most 6 * 2^j.
lemma exp_sum_primes_le (j : ℕ) :
    Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p) ≤ 6 * 2 ^ j := by
  have hX : 4 ^ (j + 1) ≤ 2 * (2 * 4 ^ j) + 2 := by
    rw [pow_succ]
    omega
  have h1 := sum_primes_le (4 ^ (j + 1)) (2 * 4 ^ j) hX
  have h2 := harmonic_sum_le (2 * 4 ^ j)
  have h3 : Real.log ((2 * 4 ^ j : ℕ) : ℝ) ≤ 2 * Real.log ((2 : ℝ) ^ (j + 1)) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    have e : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℝ) = 4 * 4 ^ j := by
      rw [Real.rpow_two]
      calc ((2 : ℝ) ^ (j + 1)) ^ 2 = ((2 : ℝ) ^ 2) ^ (j + 1) := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 4 ^ (j + 1) := by norm_num
        _ = 4 * 4 ^ j := by rw [pow_succ]; ring
    rw [e]
    push_cast
    have : (0 : ℝ) < 4 ^ j := by positivity
    linarith
  have h4 : ∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p ≤
      1 + Real.log ((2 : ℝ) ^ (j + 1)) := by
    linarith
  calc Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p)
      ≤ Real.exp (1 + Real.log ((2 : ℝ) ^ (j + 1))) := Real.exp_le_exp.2 h4
    _ = Real.exp 1 * (2 : ℝ) ^ (j + 1) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ 3 * (2 : ℝ) ^ (j + 1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [Real.exp_one_lt_d9]
    _ = 6 * 2 ^ j := by
      rw [pow_succ]
      ring

-- Reciprocals of the integers strictly between 4^j and 4^(j+1) sum to at most 3.
lemma sum_block_le (j : ℕ) :
    ∑ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) ≤ 3 := by
  have hpos : (0 : ℝ) < 4 ^ j := by positivity
  have h1 : ∀ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) ≤ 1 / 4 ^ j := by
    intro m hm
    have hm1 : 4 ^ j < m := (Finset.mem_Ioo.1 hm).1
    have hm2 : ((4 ^ j : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1.le
    push_cast at hm2
    exact one_div_le_one_div_of_le hpos hm2
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul] at h2
  refine h2.trans ?_
  have hc : ((4 ^ (j + 1) - 4 ^ j - 1 : ℕ) : ℝ) ≤ 3 * 4 ^ j := by
    have : 4 ^ (j + 1) - 4 ^ j - 1 ≤ 3 * 4 ^ j := by
      rw [pow_succ]
      omega
    exact_mod_cast this
  rw [mul_one_div, div_le_iff₀ hpos]
  exact hc

-- The pointwise bound behind the dyadic argument.
lemma prod_bound (n : ℕ) (D : ℝ) (J : ℕ) (hJ : n < 4 ^ J) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), (1 + 1 / (p : ℝ)) ≤
      Real.exp 13 + ∑ j ∈ Finset.range J,
        (if D ≤ (4 : ℝ) ^ j ∧
            10 ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
          then 6 * Real.exp 10 * 2 ^ j else 0) := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, ∀ t, L t =
      ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ) := ⟨_, fun _ => rfl⟩
  simp only [← hL]
  have hterm : ∀ j : ℕ, (0 : ℝ) ≤
      (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) := by
    intro j
    split_ifs <;> positivity
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J,
      (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) :=
    Finset.sum_nonneg (fun j _ => hterm j)
  have hP : ∏ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), (1 + 1 / (p : ℝ)) ≤
      Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _
      positivity
    · intro p _
      linarith [Real.add_one_le_exp (1 / (p : ℝ))]
  -- splitting the sum over primes above D at a threshold X
  have hsplit : ∀ X : ℝ, ∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ) ≤
      ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter (fun p : ℕ => (p : ℝ) < X),
        1 / (p : ℝ) + L X := by
    intro X
    rw [← Finset.sum_filter_add_sum_filter_not (n.primeFactors.filter (fun p : ℕ => D < p))
      (fun p : ℕ => (p : ℝ) < X)]
    apply add_le_add le_rfl
    rw [hL]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, not_lt] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    · intro p _ _
      positivity
  by_cases h1 : 10 ≤ L 1
  · obtain ⟨j, hjJ, hj0, hjmax⟩ : ∃ j, j ≤ J ∧ 10 ≤ L ((4 : ℝ) ^ j) ∧
        ∀ k, j < k → k ≤ J → ¬ (10 ≤ L ((4 : ℝ) ^ k)) := by
      refine ⟨Nat.findGreatest (fun j => 10 ≤ L ((4 : ℝ) ^ j)) J, Nat.findGreatest_le J, ?_, ?_⟩
      · exact Nat.findGreatest_spec (P := fun j => 10 ≤ L ((4 : ℝ) ^ j)) (Nat.zero_le J)
          (by simpa using h1)
      · intro k hk hkJ
        exact Nat.findGreatest_is_greatest hk hkJ
    have hLJ : L ((4 : ℝ) ^ J) = 0 := by
      rw [hL]
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      simp only [Finset.mem_filter] at hp
      have hpn : p ≤ n := Nat.le_of_mem_primeFactors hp.1
      have : (p : ℝ) < (4 : ℝ) ^ J := by exact_mod_cast lt_of_le_of_lt hpn hJ
      linarith [hp.2]
    have hjlt : j < J := by
      rcases hjJ.eq_or_lt with h | h
      · rw [h, hLJ] at hj0
        linarith
      · exact h
    have hj1 : L ((4 : ℝ) ^ (j + 1)) < 10 := not_le.1 (hjmax (j + 1) (lt_add_one j) hjlt)
    have hs := hsplit ((4 : ℝ) ^ (j + 1))
    by_cases hD : D ≤ (4 : ℝ) ^ j
    · -- the pair lies in the exceptional set at scale 4^j
      have hfirst : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter
          (fun p : ℕ => (p : ℝ) < (4 : ℝ) ^ (j + 1)), 1 / (p : ℝ) ≤
          ∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          refine ⟨?_, Nat.prime_of_mem_primeFactors hp.1.1⟩
          have := hp.2
          exact_mod_cast this
        · intro p _ _
          positivity
      have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
          6 * Real.exp 10 * 2 ^ j := by
        calc Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ))
            ≤ Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p + 10) :=
              Real.exp_le_exp.2 (by linarith)
          _ = Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p) *
              Real.exp 10 := Real.exp_add _ _
          _ ≤ 6 * 2 ^ j * Real.exp 10 :=
              mul_le_mul_of_nonneg_right (exp_sum_primes_le j) (Real.exp_pos _).le
          _ = 6 * Real.exp 10 * 2 ^ j := by ring
      have hmem : (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0)
          ≤ ∑ j ∈ Finset.range J,
            (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) :=
        Finset.single_le_sum (f := fun j : ℕ =>
          (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0))
          (fun j _ => hterm j) (Finset.mem_range.2 hjlt)
      rw [if_pos ⟨hD, hj0⟩] at hmem
      linarith [Real.exp_pos (13 : ℝ)]
    · -- D is above 4^j: the product is bounded
      have hD' : (4 : ℝ) ^ j < D := not_le.1 hD
      have hfirst : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter
          (fun p : ℕ => (p : ℝ) < (4 : ℝ) ^ (j + 1)), 1 / (p : ℝ) ≤
          ∑ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
          constructor
          · have : ((4 ^ j : ℕ) : ℝ) < (p : ℝ) := by
              push_cast
              linarith [hp.1.2]
            exact_mod_cast this
          · have := hp.2
            exact_mod_cast this
        · intro p _ _
          positivity
      have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
          Real.exp 13 := Real.exp_le_exp.2 (by linarith [sum_block_le j])
      linarith
  · have hle : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ) ≤ L 1 := by
      rw [hL]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        refine ⟨hp.1, ?_⟩
        have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).one_lt.le
        exact_mod_cast this
      · intro p _ _
        positivity
    have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
        Real.exp 13 := Real.exp_le_exp.2 (by linarith)
    linarith

-- Bookkeeping for the double sum.
lemma sum_split (S : Finset ℕ) (A W : ℕ → ℕ → ℝ) (c e : ℝ) (J : ℕ) (b : ℕ → ℝ)
    (T : ℕ → ℕ → ℕ → ℝ) :
    ∑ q ∈ S, ∑ r ∈ S, (A q r + c * (e * W q r + ∑ j ∈ Finset.range J, b j * T j q r)) =
      ∑ q ∈ S, ∑ r ∈ S, A q r + c * (e * ∑ q ∈ S, ∑ r ∈ S, W q r +
        ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r) := by
  have h3 : ∑ q ∈ S, ∑ r ∈ S, ∑ j ∈ Finset.range J, b j * T j q r =
      ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r := by
    calc ∑ q ∈ S, ∑ r ∈ S, ∑ j ∈ Finset.range J, b j * T j q r
        = ∑ q ∈ S, ∑ j ∈ Finset.range J, ∑ r ∈ S, b j * T j q r :=
          Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
      _ = ∑ j ∈ Finset.range J, ∑ q ∈ S, ∑ r ∈ S, b j * T j q r := Finset.sum_comm
      _ = ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r := by
          simp only [Finset.mul_sum]
  rw [← h3]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add]

-- (1) Overlap estimate of Pollington and Vaughan (1990, pp. 195-196), Lemma 5.3 of
-- Koukoulopoulos and Maynard, on the circle: for distinct denominators q, r with values
-- a, b in [0, 1/2], the measure of the intersection of the two approximation sets is at most
-- a constant times the product of the weights times the product of (1 + 1/p) over the primes
-- p dividing q r / gcd(q, r)^2 that exceed max(r a, q b) / gcd(q, r).
def H1 : Prop :=
  ∃ C : ℝ, ∀ (q r : ℕ) (a b : ℝ), 0 < q → 0 < r → q ≠ r →
    0 ≤ a → a ≤ 1 / 2 → 0 ≤ b → b ≤ 1 / 2 →
    (volume (approxAddOrderOf UnitAddCircle q (a / q) ∩
        approxAddOrderOf UnitAddCircle r (b / r))).toReal ≤
      C * (((Nat.totient q : ℝ) * a / q) * ((Nat.totient r : ℝ) * b / r)) *
        ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * a) ((q : ℝ) * b) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ))

-- (2) Proposition 5.4 of Koukoulopoulos and Maynard: for values in [0, 1/2], a finite set of
-- denominators of total weight between 1 and 2 and any t at least 1, the pairs (v, w) with
-- max(w psi(v), v psi(w)) at most t gcd(v, w) and with the primes p at least t dividing
-- v w / gcd(v, w)^2 having reciprocal sum at least 10 carry total weight at most C / t.
def H2 : Prop :=
  ∃ C : ℝ, ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1 / 2) →
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) →
      1 ≤ ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q →
      ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q ≤ 2 →
      ∀ t : ℝ, 1 ≤ t →
        ∑ v ∈ S, ∑ w ∈ S,
          (if max ((w : ℝ) * ψ v) ((v : ℝ) * ψ w) / (Nat.gcd v w : ℝ) ≤ t ∧
              10 ≤ ∑ p ∈ (v * w / (Nat.gcd v w) ^ 2).primeFactors.filter
                (fun p : ℕ => t ≤ p), 1 / (p : ℝ)
            then ((Nat.totient v : ℝ) * ψ v / v) * ((Nat.totient w : ℝ) * ψ w / w)
            else 0) ≤ C / t

theorem main : H1 → H2 → OMA.R_Erdos999_erdos_999_R1.H2 := by
  rintro ⟨C1, h1⟩ ⟨C2, h2⟩
  refine ⟨4 + max C1 0 * (Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0), ?_⟩
  intro ψ hψ S hS hS1 hS2
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ q, w q = (Nat.totient q : ℝ) * ψ q / q := ⟨_, fun _ => rfl⟩
  have hw0 : ∀ q, 0 ≤ w q := fun q => by
    rw [hw]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q).1) (Nat.cast_nonneg _)
  have hSa : 1 ≤ ∑ q ∈ S, w q := by simpa only [hw] using hS1
  have hSb : ∑ q ∈ S, w q ≤ 2 := by simpa only [hw] using hS2
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ q ∈ S, ∀ r ∈ S, q * r / (Nat.gcd q r) ^ 2 < 4 ^ J := by
    refine ⟨(S.sup id) ^ 2 + 1, ?_⟩
    intro q hq r hr
    have hqs : q ≤ S.sup id := Finset.le_sup (f := id) hq
    have hrs : r ≤ S.sup id := Finset.le_sup (f := id) hr
    calc q * r / (Nat.gcd q r) ^ 2 ≤ q * r := Nat.div_le_self _ _
      _ ≤ S.sup id * S.sup id := Nat.mul_le_mul hqs hrs
      _ = (S.sup id) ^ 2 := (sq _).symm
      _ < (S.sup id) ^ 2 + 1 := Nat.lt_succ_self _
      _ ≤ 4 ^ ((S.sup id) ^ 2 + 1) := (Nat.lt_pow_self (by norm_num)).le
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℕ → ℝ, ∀ j q r, T j q r =
      (if max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) ≤ (4 : ℝ) ^ j ∧
          10 ≤ ∑ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
            (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
        then w q * w r else 0) := ⟨_, fun _ _ _ => rfl⟩
  have hT0 : ∀ j q r, 0 ≤ T j q r := by
    intro j q r
    rw [hT]
    split_ifs
    · exact mul_nonneg (hw0 q) (hw0 r)
    · exact le_rfl
  have hK2 : ∀ j : ℕ, ∑ q ∈ S, ∑ r ∈ S, T j q r ≤ max C2 0 / 4 ^ j := by
    intro j
    have h := h2 ψ hψ S hS hS1 hS2 ((4 : ℝ) ^ j) (one_le_pow₀ (by norm_num))
    simp only [hT, hw]
    exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpt : ∀ q ∈ S, ∀ r ∈ S,
      (volume (approxAddOrderOf UnitAddCircle q (ψ q / q) ∩
        approxAddOrderOf UnitAddCircle r (ψ r / r))).toReal ≤
      (if q = r then 2 * w q else 0) + max C1 0 * (Real.exp 13 * (w q * w r) +
        ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r) := by
    intro q hq r hr
    have hsumT : 0 ≤ ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hT0 j q r))
    have hrest : 0 ≤ max C1 0 * (Real.exp 13 * (w q * w r) +
        ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r) :=
      mul_nonneg (le_max_right _ _) (add_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (hw0 q) (hw0 r))) hsumT)
    by_cases hqr : q = r
    · subst hqr
      rw [Set.inter_self, if_pos rfl]
      have hq0 := hS q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hδ0 : 0 ≤ ψ q / q := div_nonneg (hψ q).1 hqR.le
      have hδ1 : 2 * (ψ q / q) * q ≤ 1 := by
        have : 2 * (ψ q / q) * q = 2 * ψ q := by field_simp
        rw [this]
        linarith [(hψ q).2]
      have hv : (volume (approxAddOrderOf UnitAddCircle q (ψ q / q))).toReal = 2 * w q := by
        rw [OMA.R_Erdos999_erdos_999_R1.volume_approx_eq q hq0 _ hδ0 hδ1, ENNReal.toReal_mul,
          ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by linarith), hw]
        ring
      linarith
    · rw [if_neg hqr, zero_add]
      have hK1 := h1 q r (ψ q) (ψ r) (hS q hq) (hS r hr) hqr (hψ q).1 (hψ q).2 (hψ r).1 (hψ r).2
      rw [← hw q, ← hw r] at hK1
      have hpb := prod_bound (q * r / (Nat.gcd q r) ^ 2)
        (max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ)) J (hJ q hq r hr)
      have hww : 0 ≤ w q * w r := mul_nonneg (hw0 q) (hw0 r)
      have hP0 : 0 ≤ ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) := Finset.prod_nonneg (fun p _ => by positivity)
      refine hK1.trans ?_
      have step1 : C1 * (w q * w r) * ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) ≤ max C1 0 * (w q * w r) * (Real.exp 13 + ∑ j ∈ Finset.range J,
            (if max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) ≤ (4 : ℝ) ^ j ∧
              10 ≤ ∑ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
                (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
            then 6 * Real.exp 10 * 2 ^ j else 0)) := by
        apply mul_le_mul _ hpb hP0 (mul_nonneg (le_max_right _ _) hww)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hww
      refine step1.trans (le_of_eq ?_)
      rw [mul_assoc, mul_add, Finset.mul_sum, mul_comm (w q * w r) (Real.exp 13)]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      rw [hT]
      split_ifs <;> ring
  calc ∑ q ∈ S, ∑ r ∈ S, (volume (approxAddOrderOf UnitAddCircle q (ψ q / q) ∩
        approxAddOrderOf UnitAddCircle r (ψ r / r))).toReal
      ≤ ∑ q ∈ S, ∑ r ∈ S, ((if q = r then 2 * w q else 0) + max C1 0 *
          (Real.exp 13 * (w q * w r) +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r)) :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hpt q hq r hr))
    _ = ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) + max C1 0 *
          (Real.exp 13 * ∑ q ∈ S, ∑ r ∈ S, w q * w r +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r) :=
        sum_split S (fun q r => if q = r then 2 * w q else 0) (fun q r => w q * w r) _ _ J
          (fun j => 6 * Real.exp 10 * 2 ^ j) T
    _ ≤ 4 + max C1 0 * (Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0) := by
        have hA : ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) ≤ 4 := by
          have : ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) = ∑ q ∈ S, 2 * w q :=
            Finset.sum_congr rfl (fun q hq => by rw [Finset.sum_ite_eq, if_pos hq])
          rw [this, ← Finset.mul_sum]
          linarith
        have hB : ∑ q ∈ S, ∑ r ∈ S, w q * w r ≤ 4 := by
          rw [← Finset.sum_mul_sum]
          nlinarith [Finset.sum_nonneg (fun q (_ : q ∈ S) => hw0 q)]
        have hC : ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
            12 * Real.exp 10 * max C2 0 := by
          have hterm : ∀ j ∈ Finset.range J,
              (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
                6 * Real.exp 10 * max C2 0 * (1 / 2) ^ j := by
            intro j _
            have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
              rw [← mul_pow]
              norm_num
            calc (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r
                ≤ (6 * Real.exp 10 * 2 ^ j) * (max C2 0 / 4 ^ j) :=
                  mul_le_mul_of_nonneg_left (hK2 j) (by positivity)
              _ = 6 * Real.exp 10 * max C2 0 * (1 / 2) ^ j := by
                  rw [h4, one_div, inv_pow]
                  field_simp
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [← Finset.mul_sum]
          have hg := sum_geometric_two_le J
          have hc : 0 ≤ 6 * Real.exp 10 * max C2 0 :=
            mul_nonneg (by positivity) (le_max_right _ _)
          nlinarith
        have hc1 : 0 ≤ max C1 0 := le_max_right _ _
        have hin : Real.exp 13 * ∑ q ∈ S, ∑ r ∈ S, w q * w r +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
            Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0 :=
          add_le_add (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) hC
        exact add_le_add hA (mul_le_mul_of_nonneg_left hin hc1)

end OMA.R_Erdos999_erdos_999_R1_H2_R1

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

-- Step H2 of the reduction Erdos999.erdos_999.R1.H2.R1: Proposition 5.4 of Koukoulopoulos and
-- Maynard, proved along the lines of Hauke, Vazquez Saez and Walker (Proving the Duffin-Schaeffer
-- conjecture without GCD graphs, arXiv 2404.15123), with exponent 3/4 written in fourth-power
-- form so that no fractional powers are needed.
-- Contents: geometric row sums and the fourth root; the decay lemma for measures on pairs of
-- valuations; anatomy lemmas by the Rankin trick; weighted systems and the removal of one
-- prime; concentration of the valuations of a minimal counterexample around an integer N;
-- the minimum degree property of a smallest near counterexample; the resolution of structured
-- systems; the induction on the number of primes; the deduction of the proposition.

namespace DSK

open Finset

-- For fixed i, at most two indices j are at a given distance d from i.
lemma dist_fiber (i d : ℕ) (s : Finset ℕ) :
    (s.filter (fun j => Nat.dist i j = d)).card ≤ 2 := by
  have hsub : s.filter (fun j => Nat.dist i j = d) ⊆ {i + d, i - d} := by
    intro j hj
    rw [mem_filter] at hj
    have h := hj.2
    unfold Nat.dist at h
    rw [mem_insert, mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

-- A finite geometric tail.
lemma geo_tail (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (d0 M : ℕ) :
    ∑ d ∈ Ico d0 M, l ^ d ≤ l ^ d0 / (1 - l) := by
  have hpos : 0 < 1 - l := by linarith
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg h0 _)
  have hgs := mul_neg_geom_sum l (M - d0)
  rw [← one_div, le_div_iff₀ hpos]
  have hp : 0 ≤ l ^ (M - d0) := pow_nonneg h0 _
  nlinarith

-- Row sums of powers of l by distance from i, restricted to distance at least d0.
lemma row_sum (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (i n d0 : ℕ) :
    ∑ j ∈ (range n).filter (fun j => d0 ≤ Nat.dist i j), l ^ (Nat.dist i j) ≤
      2 * l ^ d0 / (1 - l) := by
  have hmaps : ∀ j ∈ (range n).filter (fun j => d0 ≤ Nat.dist i j),
      Nat.dist i j ∈ Ico d0 (i + n + 1) := by
    intro j hj
    rw [mem_filter, mem_range] at hj
    rw [mem_Ico]
    refine ⟨hj.2, ?_⟩
    unfold Nat.dist
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ d ∈ Ico d0 (i + n + 1),
      ∑ j ∈ ((range n).filter (fun j => d0 ≤ Nat.dist i j)).filter (fun j => Nat.dist i j = d),
        l ^ (Nat.dist i j) ≤ 2 * l ^ d := by
    intro d _
    have e : ∑ j ∈ ((range n).filter (fun j => d0 ≤ Nat.dist i j)).filter
        (fun j => Nat.dist i j = d), l ^ (Nat.dist i j) =
        ∑ _j ∈ ((range n).filter (fun j => d0 ≤ Nat.dist i j)).filter
        (fun j => Nat.dist i j = d), l ^ d := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(mem_filter.1 hj).2]
    rw [e, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
    exact_mod_cast dist_fiber i d _
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [← Finset.mul_sum, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (geo_tail l h0 h1 d0 _) (by norm_num)

-- The fourth root, as an iterated square root.
noncomputable def r4 (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

lemma r4_nonneg (x : ℝ) : 0 ≤ r4 x := Real.sqrt_nonneg _

lemma r4_pow (x : ℝ) (hx : 0 ≤ x) : r4 x ^ 4 = x := by
  unfold r4
  have h1 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2]

lemma r4_mono {x y : ℝ} (h : x ≤ y) : r4 x ≤ r4 y :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

-- Comparing fourth powers of nonnegative reals.
lemma le_of_pow4_le {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 4 ≤ y ^ 4) : x ≤ y := by
  by_contra hcon
  have hlt : y < x := not_le.1 hcon
  have : y ^ 4 < x ^ 4 := pow_lt_pow_left₀ hlt hy (by norm_num)
  linarith

-- The telescoping inequality for n^(-1/4).
lemma r4_tele (n : ℕ) (hn : 1 ≤ n) :
    r4 (1 / ((n : ℝ) + 1)) ^ 5 ≤ 4 * (r4 (1 / (n : ℝ)) - r4 (1 / ((n : ℝ) + 1))) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = r4 (1 / (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = r4 (1 / ((n : ℝ) + 1)) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha4 : a ^ 4 = 1 / (n : ℝ) := by rw [ha]; exact r4_pow _ (by positivity)
  have hb4 : b ^ 4 = 1 / ((n : ℝ) + 1) := by rw [hb]; exact r4_pow _ (by positivity)
  have ha0 : 0 ≤ a := by rw [ha]; exact r4_nonneg _
  have hb0 : 0 ≤ b := by rw [hb]; exact r4_nonneg _
  have hba : b ≤ a := by
    rw [ha, hb]
    apply r4_mono
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hapos : 0 < a := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h] at ha4
      have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      rw [← ha4] at this
      norm_num at this
    · exact h
  -- a^4 - b^4 = a^4 b^4
  have hkey : a ^ 4 - b ^ 4 = a ^ 4 * b ^ 4 := by
    rw [ha4, hb4]
    field_simp
    ring
  have hfac : a ^ 4 - b ^ 4 ≤ (a - b) * (4 * a ^ 3) := by
    have e : a ^ 4 - b ^ 4 = (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have h1 : a ^ 2 * b ≤ a ^ 3 := by nlinarith [sq_nonneg a]
    have h2 : a * b ^ 2 ≤ a ^ 3 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha0 hb0]
    have h3 : b ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hb0 hba 3
    linarith
  -- a b^4 ≤ 4 (a - b)
  have h4 : a * b ^ 4 ≤ 4 * (a - b) := by
    have h5 : a ^ 3 * (a * b ^ 4) ≤ a ^ 3 * (4 * (a - b)) := by
      have e1 : a ^ 3 * (a * b ^ 4) = a ^ 4 * b ^ 4 := by ring
      have e2 : a ^ 3 * (4 * (a - b)) = (a - b) * (4 * a ^ 3) := by ring
      rw [e1, e2, ← hkey]
      exact hfac
    exact le_of_mul_le_mul_left h5 (pow_pos hapos 3)
  have h6 : b ^ 5 ≤ a * b ^ 4 := by
    have e : b ^ 5 = b * b ^ 4 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hba (pow_nonneg hb0 4)
  linarith

-- Summing the fifth powers of n^(-1/4) over n above N.
lemma r4_sum (N M : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc N M, r4 (1 / (n : ℝ)) ^ 5 ≤ 4 * r4 (1 / (N : ℝ)) := by
  have key : ∀ M, N ≤ M → ∑ n ∈ Ioc N M, r4 (1 / (n : ℝ)) ^ 5 ≤
      4 * (r4 (1 / (N : ℝ)) - r4 (1 / (M : ℝ))) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top hM]
      have ht := r4_tele M (by omega)
      push_cast
      linarith
  rcases le_total N M with h | h
  · have := key M h
    have h2 := r4_nonneg (1 / (M : ℝ))
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have h2 := r4_nonneg (1 / (N : ℝ))
    linarith


-- Double sums of powers of l by distance, with the row index pinned at k.
lemma sum_row_fixed (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (k n d0 : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n,
      (if i = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) ≤ 2 * l ^ d0 / (1 - l) := by
  have hR : (0 : ℝ) ≤ 2 * l ^ d0 / (1 - l) :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (by linarith)
  have hinner : ∀ i ∈ range n, ∑ j ∈ range n,
      (if i = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) =
      if i = k then ∑ j ∈ (range n).filter (fun j => d0 ≤ Nat.dist k j), l ^ (Nat.dist k j)
        else 0 := by
    intro i _
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      simp
    · rw [if_neg hik]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hik h.1)]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  split_ifs
  · exact row_sum l h0 h1 k n d0
  · exact hR

-- The same with the column index pinned at k.
lemma sum_col_fixed (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (k n d0 : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n,
      (if j = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) ≤ 2 * l ^ d0 / (1 - l) := by
  rw [Finset.sum_comm]
  have h := sum_row_fixed l h0 h1 k n d0
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.dist_comm i j]

-- Double sums weighted by a nonnegative function of the row index.
lemma sum_weight_row (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (n d0 : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ∑ i ∈ range n, ∑ j ∈ range n,
      (if d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a i else 0) ≤
      (∑ i ∈ range n, a i) * (2 * l ^ d0 / (1 - l)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have e : ∑ j ∈ range n, (if d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a i else 0) =
      a i * ∑ j ∈ (range n).filter (fun j => d0 ≤ Nat.dist i j), l ^ (Nat.dist i j) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · ring
    · rfl
  rw [e]
  exact mul_le_mul_of_nonneg_left (row_sum l h0 h1 i n d0) (ha i)

-- Double sums weighted by a nonnegative function of the column index.
lemma sum_weight_col (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) (n d0 : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ∑ i ∈ range n, ∑ j ∈ range n,
      (if d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a j else 0) ≤
      (∑ j ∈ range n, a j) * (2 * l ^ d0 / (1 - l)) := by
  rw [Finset.sum_comm]
  have h := sum_weight_row l h0 h1 n d0 a ha
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.dist_comm i j]

-- Terms of a sequence whose fourth powers sum to 1 are at most 1.
lemma le_one_of_sum_pow4 (n : ℕ) (u : ℕ → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hU : ∑ i ∈ range n, u i ^ 4 = 1) (i : ℕ) (hi : i ∈ range n) : u i ≤ 1 := by
  have h := Finset.single_le_sum (f := fun i => u i ^ 4) (fun i _ => pow_nonneg (hu0 i) 4) hi
  rw [hU] at h
  apply le_of_pow4_le zero_le_one
  simpa using h

-- The elementary inequality (x y)^3 ≤ (x^4 + y^4) / 2 on the unit square.
lemma cube_le (x y : ℝ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (x * y) ^ 3 ≤ (x ^ 4 + y ^ 4) / 2 := by
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ 1 := by nlinarith
  have h1 : (x * y) ^ 3 ≤ (x * y) ^ 2 := by
    have e : (x * y) ^ 3 = (x * y) * (x * y) ^ 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (x * y)]
  have h2 : (x * y) ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  linarith

-- Part A: the total mass is at most 40 times the constant in the bilinear bound.
lemma decay_a (n : ℕ) (m : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (l κ c1 : ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hU : ∑ i ∈ range n, u i ^ 4 = 1) (hV : ∑ j ∈ range n, v j ^ 4 = 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 17 / 20) (hκ0 : 0 ≤ κ) (hκ3 : κ ≤ 3) (hc1 : 0 ≤ c1)
    (hb : ∀ i ∈ range n, ∀ j ∈ range n,
      m i j ≤ c1 * κ * l ^ (Nat.dist i j) * (u i * v j) ^ 3) :
    ∑ i ∈ range n, ∑ j ∈ range n, m i j ≤ c1 * 40 := by
  have hl : l < 1 := by linarith
  have hG : 2 * l ^ 0 / (1 - l) ≤ 40 / 3 := by
    rw [pow_zero, mul_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hpt : ∀ i ∈ range n, ∀ j ∈ range n, m i j ≤
      c1 * 3 / 2 * ((if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * u i ^ 4 else 0) +
        (if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * v j ^ 4 else 0)) := by
    intro i hi j hj
    rw [if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)]
    have hui := le_one_of_sum_pow4 n u hu0 hU i hi
    have hvj := le_one_of_sum_pow4 n v hv0 hV j hj
    have hc := cube_le (u i) (v j) (hu0 i) (hv0 j) hui hvj
    have hlp : 0 ≤ l ^ (Nat.dist i j) := pow_nonneg hl0 _
    have hcube0 : 0 ≤ (u i * v j) ^ 3 := pow_nonneg (mul_nonneg (hu0 i) (hv0 j)) 3
    calc m i j ≤ c1 * κ * l ^ (Nat.dist i j) * (u i * v j) ^ 3 := hb i hi j hj
      _ ≤ c1 * 3 * l ^ (Nat.dist i j) * ((u i ^ 4 + v j ^ 4) / 2) := by
          apply mul_le_mul _ hc hcube0 (by positivity)
          apply mul_le_mul_of_nonneg_right _ hlp
          exact mul_le_mul_of_nonneg_left hκ3 hc1
      _ = _ := by ring
  have h1 := sum_weight_row l hl0 hl n 0 (fun i => u i ^ 4) (fun i => pow_nonneg (hu0 i) 4)
  have h2 := sum_weight_col l hl0 hl n 0 (fun i => v i ^ 4) (fun i => pow_nonneg (hv0 i) 4)
  rw [hU] at h1
  rw [hV] at h2
  calc ∑ i ∈ range n, ∑ j ∈ range n, m i j
      ≤ ∑ i ∈ range n, ∑ j ∈ range n, c1 * 3 / 2 *
          ((if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * u i ^ 4 else 0) +
            (if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * v j ^ 4 else 0)) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpt i hi j hj))
    _ = c1 * 3 / 2 * (∑ i ∈ range n, ∑ j ∈ range n,
          (if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * u i ^ 4 else 0) +
          ∑ i ∈ range n, ∑ j ∈ range n,
          (if 0 ≤ Nat.dist i j then l ^ (Nat.dist i j) * v j ^ 4 else 0)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ c1 * 3 / 2 * (1 * (2 * l ^ 0 / (1 - l)) + 1 * (2 * l ^ 0 / (1 - l))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ ≤ c1 * 40 := by nlinarith


-- Part B: concentration of the mass near one diagonal point (k, k) when l is small.
set_option maxHeartbeats 2000000 in
lemma decay_b (n : ℕ) (m : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (l κ : ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hU : ∑ i ∈ range n, u i ^ 4 = 1) (hV : ∑ j ∈ range n, v j ^ 4 = 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1 / 100) (hκ1 : 1 ≤ κ) (hκ3 : κ ≤ 3)
    (hsum : ∑ i ∈ range n, ∑ j ∈ range n, m i j = 1)
    (hb : ∀ i ∈ range n, ∀ j ∈ range n,
      m i j ≤ (if i = j then 1 else κ) * l ^ (Nat.dist i j) * (u i * v j) ^ 3) :
    ∃ k ∈ range n, ∑ i ∈ range n, ∑ j ∈ range n,
      (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0) ≤
        (18 * 144 ^ 3 + 1296 * 144 ^ 5) * l ^ 5 := by
  have hl : l < 1 := by linarith
  have h1l : 0 < 1 - l := by linarith
  have hn : (range n).Nonempty := by
    rw [Finset.nonempty_range_iff]
    rintro rfl
    simp at hU
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (range n) (fun i => u i * v i) hn
  refine ⟨k, hk, ?_⟩
  have hu1 := le_one_of_sum_pow4 n u hu0 hU
  have hv1 := le_one_of_sum_pow4 n v hv0 hV
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = u k * v k := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg (hu0 k) (hv0 k)
  have hρu : ρ ≤ u k := by
    rw [hρ]
    nlinarith [hu0 k, hv0 k, hv1 k hk]
  have hρv : ρ ≤ v k := by
    rw [hρ]
    nlinarith [hu0 k, hv0 k, hu1 k hk]
  have hρ1 : ρ ≤ 1 := hρu.trans (hu1 k hk)
  have hbern : 1 - 4 * (1 - ρ) ≤ ρ ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (1 - ρ)) (by positivity : (0 : ℝ) ≤ ρ ^ 2 + 2 * ρ + 3)]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ i, a i = if i = k then 0 else u i ^ 4 := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℕ → ℝ, ∀ i, b i = if i = k then 0 else v i ^ 4 := ⟨_, fun _ => rfl⟩
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    rw [ha]
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (hu0 i) 4
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    rw [hbd]
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (hv0 i) 4
  have hasum : ∑ i ∈ range n, a i ≤ 4 * (1 - ρ) := by
    have e : ∑ i ∈ range n, a i = ∑ i ∈ range n, u i ^ 4 - u k ^ 4 := by
      rw [← Finset.sum_erase_add _ _ hk, ← Finset.sum_erase_add (range n) (fun i => u i ^ 4) hk,
        ha k, if_pos rfl]
      have e2 : ∑ i ∈ (range n).erase k, a i = ∑ i ∈ (range n).erase k, u i ^ 4 :=
        Finset.sum_congr rfl (fun i hi => by rw [ha, if_neg (Finset.ne_of_mem_erase hi)])
      rw [e2]
      ring
    rw [e, hU]
    have h4 : ρ ^ 4 ≤ u k ^ 4 := pow_le_pow_left₀ hρ0 hρu 4
    linarith
  have hbsum : ∑ i ∈ range n, b i ≤ 4 * (1 - ρ) := by
    have e : ∑ i ∈ range n, b i = ∑ i ∈ range n, v i ^ 4 - v k ^ 4 := by
      rw [← Finset.sum_erase_add _ _ hk, ← Finset.sum_erase_add (range n) (fun i => v i ^ 4) hk,
        hbd k, if_pos rfl]
      have e2 : ∑ i ∈ (range n).erase k, b i = ∑ i ∈ (range n).erase k, v i ^ 4 :=
        Finset.sum_congr rfl (fun i hi => by rw [hbd, if_neg (Finset.ne_of_mem_erase hi)])
      rw [e2]
      ring
    rw [e, hV]
    have h4 : ρ ^ 4 ≤ v k ^ 4 := pow_le_pow_left₀ hρ0 hρv 4
    linarith
  -- the largest value away from k
  obtain ⟨σ, hσ0, hσ1, hσu, hσv, hσ4⟩ : ∃ σ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧
      (∀ i ∈ range n, i ≠ k → u i ≤ σ) ∧ (∀ i ∈ range n, i ≠ k → v i ≤ σ) ∧
      σ ^ 4 ≤ 4 * (1 - ρ) := by
    rcases ((range n).erase k).eq_empty_or_nonempty with he | hne
    · refine ⟨0, le_rfl, zero_le_one, ?_, ?_, ?_⟩
      · intro i hi hik
        have hmem : i ∈ (range n).erase k := Finset.mem_erase.2 ⟨hik, hi⟩
        rw [he] at hmem
        simp at hmem
      · intro i hi hik
        have hmem : i ∈ (range n).erase k := Finset.mem_erase.2 ⟨hik, hi⟩
        rw [he] at hmem
        simp at hmem
      · have : (0 : ℝ) ^ 4 = 0 := by norm_num
        rw [this]
        linarith
    · obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image _ (fun i => max (u i) (v i)) hne
      have hi0m := Finset.mem_erase.1 hi0
      refine ⟨max (u i0) (v i0), le_max_of_le_left (hu0 i0),
        max_le (hu1 i0 hi0m.2) (hv1 i0 hi0m.2), ?_, ?_, ?_⟩
      · intro i hi hik
        exact (le_max_left _ _).trans (hmax i (Finset.mem_erase.2 ⟨hik, hi⟩))
      · intro i hi hik
        exact (le_max_right _ _).trans (hmax i (Finset.mem_erase.2 ⟨hik, hi⟩))
      · rcases max_choice (u i0) (v i0) with h | h
        · rw [h]
          have e : u i0 ^ 4 = a i0 := by rw [ha, if_neg hi0m.1]
          rw [e]
          exact (Finset.single_le_sum (fun i _ => ha0 i) hi0m.2).trans hasum
        · rw [h]
          have e : v i0 ^ 4 = b i0 := by rw [hbd, if_neg hi0m.1]
          rw [e]
          exact (Finset.single_le_sum (fun i _ => hb0 i) hi0m.2).trans hbsum
  -- the bilinear bound with the constant κ everywhere
  have hbκ : ∀ i ∈ range n, ∀ j ∈ range n,
      m i j ≤ κ * (l ^ (Nat.dist i j) * (u i * v j) ^ 3) := by
    intro i hi j hj
    have h := hb i hi j hj
    have hnn : 0 ≤ l ^ (Nat.dist i j) * (u i * v j) ^ 3 :=
      mul_nonneg (pow_nonneg hl0 _) (pow_nonneg (mul_nonneg (hu0 i) (hv0 j)) 3)
    refine h.trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hnn
    split_ifs
    · exact hκ1
    · exact le_rfl
  -- the four-term majorant
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℕ → ℕ → ℕ → ℝ, ∀ d0 d1 i j, R d0 d1 i j =
      σ ^ 3 * (if i = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) +
      σ ^ 3 * (if j = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) +
      σ ^ 2 / 2 * (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a i else 0) +
      σ ^ 2 / 2 * (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * b j else 0) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  have hR0 : ∀ d0 d1 i j, 0 ≤ R d0 d1 i j := by
    intro d0 d1 i j
    rw [hR]
    have hlp : 0 ≤ l ^ (Nat.dist i j) := pow_nonneg hl0 _
    have t1 : (0 : ℝ) ≤ (if i = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) := by
      split_ifs
      · exact hlp
      · exact le_rfl
    have t2 : (0 : ℝ) ≤ (if j = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0) := by
      split_ifs
      · exact hlp
      · exact le_rfl
    have t3 : (0 : ℝ) ≤ (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a i else 0) := by
      split_ifs
      · exact mul_nonneg hlp (ha0 i)
      · exact le_rfl
    have t4 : (0 : ℝ) ≤ (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * b j else 0) := by
      split_ifs
      · exact mul_nonneg hlp (hb0 j)
      · exact le_rfl
    have hs3 : 0 ≤ σ ^ 3 := pow_nonneg hσ0 3
    have hs2 : 0 ≤ σ ^ 2 / 2 := by positivity
    have := mul_nonneg hs3 t1
    have := mul_nonneg hs3 t2
    have := mul_nonneg hs2 t3
    have := mul_nonneg hs2 t4
    linarith
  have hcore : ∀ (d0 d1 : ℕ), ∀ i ∈ range n, ∀ j ∈ range n, ¬ (i = k ∧ j = k) →
      (i = k → d0 ≤ Nat.dist i j) → (j = k → d0 ≤ Nat.dist i j) → d1 ≤ Nat.dist i j →
      l ^ (Nat.dist i j) * (u i * v j) ^ 3 ≤ R d0 d1 i j := by
    intro d0 d1 i hi j hj hnot h1 h2 hd1
    have hlp : 0 ≤ l ^ (Nat.dist i j) := pow_nonneg hl0 _
    rw [hR, if_pos hd1, if_pos hd1]
    have t3 : 0 ≤ σ ^ 2 / 2 * (l ^ (Nat.dist i j) * a i) :=
      mul_nonneg (by positivity) (mul_nonneg hlp (ha0 i))
    have t4 : 0 ≤ σ ^ 2 / 2 * (l ^ (Nat.dist i j) * b j) :=
      mul_nonneg (by positivity) (mul_nonneg hlp (hb0 j))
    by_cases hik : i = k
    · have hjk : j ≠ k := fun h => hnot ⟨hik, h⟩
      rw [if_pos ⟨hik, h1 hik⟩, if_neg (fun h => hjk h.1), mul_zero, add_zero]
      have hvj := hσv j hj hjk
      have hc : (u i * v j) ^ 3 ≤ σ ^ 3 := by
        apply pow_le_pow_left₀ (mul_nonneg (hu0 i) (hv0 j))
        calc u i * v j ≤ 1 * v j := mul_le_mul_of_nonneg_right (hu1 i hi) (hv0 j)
          _ = v j := one_mul _
          _ ≤ σ := hvj
      have h3 : l ^ (Nat.dist i j) * (u i * v j) ^ 3 ≤ σ ^ 3 * l ^ (Nat.dist i j) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hc hlp
      linarith
    · by_cases hjk : j = k
      · rw [if_neg (fun h => hik h.1), if_pos ⟨hjk, h2 hjk⟩, mul_zero, zero_add]
        have hui := hσu i hi hik
        have hc : (u i * v j) ^ 3 ≤ σ ^ 3 := by
          apply pow_le_pow_left₀ (mul_nonneg (hu0 i) (hv0 j))
          calc u i * v j ≤ u i * 1 := mul_le_mul_of_nonneg_left (hv1 j hj) (hu0 i)
            _ = u i := mul_one _
            _ ≤ σ := hui
        have h3 : l ^ (Nat.dist i j) * (u i * v j) ^ 3 ≤ σ ^ 3 * l ^ (Nat.dist i j) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hc hlp
        linarith
      · rw [if_neg (fun h => hik h.1), if_neg (fun h => hjk h.1), ha i, if_neg hik, hbd j,
          if_neg hjk]
        simp only [mul_zero, zero_add]
        have hui := hσu i hi hik
        have hvj := hσv j hj hjk
        have h6 : (u i * v j) ^ 3 ≤ σ ^ 2 * ((u i ^ 4 + v j ^ 4) / 2) := by
          have e : (u i * v j) ^ 3 = (u i * v j) * (u i * v j) ^ 2 := by ring
          rw [e]
          have hA : u i * v j ≤ σ ^ 2 := by nlinarith [hu0 i, hv0 j]
          have hB : (u i * v j) ^ 2 ≤ (u i ^ 4 + v j ^ 4) / 2 := by
            nlinarith [sq_nonneg (u i ^ 2 - v j ^ 2)]
          exact mul_le_mul hA hB (sq_nonneg _) (sq_nonneg σ)
        have h7 := mul_le_mul_of_nonneg_left h6 hlp
        have e2 : l ^ (Nat.dist i j) * (σ ^ 2 * ((u i ^ 4 + v j ^ 4) / 2)) =
            σ ^ 2 / 2 * (l ^ (Nat.dist i j) * u i ^ 4) +
            σ ^ 2 / 2 * (l ^ (Nat.dist i j) * v j ^ 4) := by ring
        rw [e2] at h7
        exact h7
  -- summing the majorant
  have hRsum : ∀ d0 d1 : ℕ, ∑ i ∈ range n, ∑ j ∈ range n, R d0 d1 i j ≤
      2 * σ ^ 3 * (2 * l ^ d0 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ d1 / (1 - l)) := by
    intro d0 d1
    have s1 := sum_row_fixed l hl0 hl k n d0
    have s2 := sum_col_fixed l hl0 hl k n d0
    have s3 := sum_weight_row l hl0 hl n d1 a ha0
    have s4 := sum_weight_col l hl0 hl n d1 b hb0
    have hG1 : (0 : ℝ) ≤ 2 * l ^ d1 / (1 - l) :=
      div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hl0 _)) h1l.le
    have s3b : (∑ i ∈ range n, a i) * (2 * l ^ d1 / (1 - l)) ≤
        4 * (1 - ρ) * (2 * l ^ d1 / (1 - l)) := mul_le_mul_of_nonneg_right hasum hG1
    have s4b : (∑ i ∈ range n, b i) * (2 * l ^ d1 / (1 - l)) ≤
        4 * (1 - ρ) * (2 * l ^ d1 / (1 - l)) := mul_le_mul_of_nonneg_right hbsum hG1
    have hs3 : 0 ≤ σ ^ 3 := pow_nonneg hσ0 3
    have hs2 : 0 ≤ σ ^ 2 / 2 := by positivity
    have e : ∑ i ∈ range n, ∑ j ∈ range n, R d0 d1 i j =
        σ ^ 3 * (∑ i ∈ range n, ∑ j ∈ range n,
          (if i = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0)) +
        σ ^ 3 * (∑ i ∈ range n, ∑ j ∈ range n,
          (if j = k ∧ d0 ≤ Nat.dist i j then l ^ (Nat.dist i j) else 0)) +
        σ ^ 2 / 2 * (∑ i ∈ range n, ∑ j ∈ range n,
          (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * a i else 0)) +
        σ ^ 2 / 2 * (∑ i ∈ range n, ∑ j ∈ range n,
          (if d1 ≤ Nat.dist i j then l ^ (Nat.dist i j) * b j else 0)) := by
      simp only [hR, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e]
    have m1 := mul_le_mul_of_nonneg_left s1 hs3
    have m2 := mul_le_mul_of_nonneg_left s2 hs3
    have m3 := mul_le_mul_of_nonneg_left (s3.trans s3b) hs2
    have m4 := mul_le_mul_of_nonneg_left (s4.trans s4b) hs2
    have e5 : 2 * σ ^ 3 * (2 * l ^ d0 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ d1 / (1 - l)) =
        σ ^ 3 * (2 * l ^ d0 / (1 - l)) + σ ^ 3 * (2 * l ^ d0 / (1 - l)) +
        σ ^ 2 / 2 * (4 * (1 - ρ) * (2 * l ^ d1 / (1 - l))) +
        σ ^ 2 / 2 * (4 * (1 - ρ) * (2 * l ^ d1 / (1 - l))) := by ring
    rw [e5]
    linarith
  -- geometric constants
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have hG1 : 2 * l ^ 1 / (1 - l) ≤ 3 * l := by
    rw [pow_one, div_le_iff₀ h1l]
    nlinarith
  have hG2 : 2 * l ^ 2 / (1 - l) ≤ 3 * l ^ 2 := by
    rw [div_le_iff₀ h1l]
    nlinarith
  have hG0 : 2 * l ^ 0 / (1 - l) ≤ 3 := by
    rw [pow_zero, mul_one, div_le_iff₀ h1l]
    linarith
  -- the diagonal
  have hdiag : ∑ i ∈ range n, m i i ≤ ρ := by
    have hpt : ∀ i ∈ range n, m i i ≤ ρ * ((u i ^ 4 + v i ^ 4) / 2) := by
      intro i hi
      have h := hb i hi i hi
      rw [if_pos rfl, one_mul, Nat.dist_self, pow_zero, one_mul] at h
      refine h.trans ?_
      have e : (u i * v i) ^ 3 = (u i * v i) * (u i * v i) ^ 2 := by ring
      rw [e]
      have hA : u i * v i ≤ ρ := by
        rw [hρ]
        exact hkmax i hi
      have hB : (u i * v i) ^ 2 ≤ (u i ^ 4 + v i ^ 4) / 2 := by
        nlinarith [sq_nonneg (u i ^ 2 - v i ^ 2)]
      exact mul_le_mul hA hB (sq_nonneg _) hρ0
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hU, hV]
    norm_num
  -- the off-diagonal part
  have hoff : ∑ i ∈ range n, ∑ j ∈ range n, (if i = j then 0 else m i j) ≤
      κ * (2 * σ ^ 3 * (2 * l ^ 1 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 1 / (1 - l))) := by
    have hpt : ∀ i ∈ range n, ∀ j ∈ range n, (if i = j then 0 else m i j) ≤ κ * R 1 1 i j := by
      intro i hi j hj
      split_ifs with hij
      · exact mul_nonneg (by linarith) (hR0 1 1 i j)
      · have hd : 1 ≤ Nat.dist i j := Nat.dist_pos_of_ne hij
        have hc := hcore 1 1 i hi j hj (fun h => hij (h.1.trans h.2.symm)) (fun _ => hd)
          (fun _ => hd) hd
        exact (hbκ i hi j hj).trans (mul_le_mul_of_nonneg_left hc (by linarith))
    calc ∑ i ∈ range n, ∑ j ∈ range n, (if i = j then 0 else m i j)
        ≤ ∑ i ∈ range n, ∑ j ∈ range n, κ * R 1 1 i j :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpt i hi j hj))
      _ = κ * ∑ i ∈ range n, ∑ j ∈ range n, R 1 1 i j := by
          simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hRsum 1 1) (by linarith)
  have hsplit : ∑ i ∈ range n, ∑ j ∈ range n, m i j =
      ∑ i ∈ range n, m i i + ∑ i ∈ range n, ∑ j ∈ range n, (if i = j then 0 else m i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have e : ∑ j ∈ range n, m i j = ∑ j ∈ range n,
        ((if i = j then m i j else 0) + (if i = j then 0 else m i j)) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hi]
  -- consequences for δ = 1 - ρ and σ
  have hδ0 : 0 ≤ 1 - ρ := by linarith
  have hs3 : 0 ≤ σ ^ 3 := pow_nonneg hσ0 3
  have hs2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hs21 : σ ^ 2 ≤ 1 := by nlinarith
  have hδ : 1 - ρ ≤ 36 * l * σ ^ 3 := by
    have h1 : 1 - ρ ≤ κ * (2 * σ ^ 3 * (2 * l ^ 1 / (1 - l)) +
        4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 1 / (1 - l))) := by
      have := hsum
      rw [hsplit] at this
      linarith
    have h2 : 2 * σ ^ 3 * (2 * l ^ 1 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 1 / (1 - l)) ≤
        2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l) := by
      have a1 := mul_le_mul_of_nonneg_left hG1 (by positivity : (0 : ℝ) ≤ 2 * σ ^ 3)
      have a2 := mul_le_mul_of_nonneg_left hG1
        (mul_nonneg (mul_nonneg (by norm_num) hδ0) hs2 : (0 : ℝ) ≤ 4 * (1 - ρ) * σ ^ 2)
      linarith
    have h3 : 0 ≤ 2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l) := by positivity
    have h4 : κ * (2 * σ ^ 3 * (2 * l ^ 1 / (1 - l)) +
        4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 1 / (1 - l))) ≤
        3 * (2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l)) := by
      calc κ * (2 * σ ^ 3 * (2 * l ^ 1 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 1 / (1 - l)))
          ≤ κ * (2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l)) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ ≤ 3 * (2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l)) :=
            mul_le_mul_of_nonneg_right hκ3 h3
    have h5 : (1 - ρ) * (σ ^ 2 * l) ≤ (1 - ρ) * (1 / 100) := by
      have h6 : σ ^ 2 * l ≤ 1 * (1 / 100) := mul_le_mul hs21 hl1 hl0 (by norm_num)
      exact mul_le_mul_of_nonneg_left (by linarith) hδ0
    have e : 3 * (2 * σ ^ 3 * (3 * l) + 4 * (1 - ρ) * σ ^ 2 * (3 * l)) =
        18 * (l * σ ^ 3) + 36 * ((1 - ρ) * (σ ^ 2 * l)) := by ring
    have hls : 0 ≤ l * σ ^ 3 := mul_nonneg hl0 hs3
    have eg : 36 * l * σ ^ 3 = 36 * (l * σ ^ 3) := by ring
    rw [eg]
    linarith
  have hσl : σ ≤ 144 * l := by
    rcases hσ0.eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · have h1 : σ * σ ^ 3 ≤ (144 * l) * σ ^ 3 := by
        have e : σ * σ ^ 3 = σ ^ 4 := by ring
        have e2 : (144 * l) * σ ^ 3 = 4 * (36 * l * σ ^ 3) := by ring
        rw [e, e2]
        linarith
      exact le_of_mul_le_mul_right h1 (pow_pos hpos 3)
  -- the tail
  have htail : ∑ i ∈ range n, ∑ j ∈ range n,
      (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0) ≤
      κ * (2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l))) := by
    have hpt : ∀ i ∈ range n, ∀ j ∈ range n,
        (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0) ≤ κ * R 2 0 i j := by
      intro i hi j hj
      split_ifs with hcond
      · have hnot : ¬ (i = k ∧ j = k) := by
          rintro ⟨rfl, rfl⟩
          rw [Nat.dist_self] at hcond
          omega
        have h1 : i = k → 2 ≤ Nat.dist i j := by
          rintro rfl
          rw [Nat.dist_self, Nat.zero_add, Nat.dist_comm] at hcond
          exact hcond
        have h2 : j = k → 2 ≤ Nat.dist i j := by
          rintro rfl
          rw [Nat.dist_self, Nat.add_zero] at hcond
          exact hcond
        have hc := hcore 2 0 i hi j hj hnot h1 h2 (Nat.zero_le _)
        exact (hbκ i hi j hj).trans (mul_le_mul_of_nonneg_left hc (by linarith))
      · exact mul_nonneg (by linarith) (hR0 2 0 i j)
    calc ∑ i ∈ range n, ∑ j ∈ range n, (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)
        ≤ ∑ i ∈ range n, ∑ j ∈ range n, κ * R 2 0 i j :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpt i hi j hj))
      _ = κ * ∑ i ∈ range n, ∑ j ∈ range n, R 2 0 i j := by
          simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hRsum 2 0) (by linarith)
  refine htail.trans ?_
  -- final arithmetic
  have hσ3 : σ ^ 3 ≤ 144 ^ 3 * l ^ 3 := by
    have := pow_le_pow_left₀ hσ0 hσl 3
    rw [mul_pow] at this
    exact this
  have hσ2 : σ ^ 2 ≤ 144 ^ 2 * l ^ 2 := by
    have := pow_le_pow_left₀ hσ0 hσl 2
    rw [mul_pow] at this
    exact this
  have hl3 : 0 ≤ l ^ 3 := pow_nonneg hl0 3
  have hδ2 : 1 - ρ ≤ 36 * 144 ^ 3 * l ^ 4 := by
    have h1 : 36 * l * σ ^ 3 ≤ 36 * l * (144 ^ 3 * l ^ 3) :=
      mul_le_mul_of_nonneg_left hσ3 (by positivity)
    have e : 36 * l * ((144 : ℝ) ^ 3 * l ^ 3) = 36 * 144 ^ 3 * l ^ 4 := by ring
    linarith
  have t1 : 2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) ≤ 2 * (144 ^ 3 * l ^ 3) * (3 * l ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hσ3 (by norm_num)) hG2
      (div_nonneg (by positivity) h1l.le) (by positivity)
  have t2 : 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l)) ≤
      4 * (36 * 144 ^ 3 * l ^ 4) * (144 ^ 2 * l ^ 2) * 3 := by
    apply mul_le_mul _ hG0 (div_nonneg (by positivity) h1l.le) (by positivity)
    apply mul_le_mul _ hσ2 hs2 (by positivity)
    exact mul_le_mul_of_nonneg_left hδ2 (by norm_num)
  have hl6 : l ^ 6 ≤ l ^ 5 := by
    have e : l ^ 6 = l ^ 5 * l := by ring
    rw [e]
    have : 0 ≤ l ^ 5 := pow_nonneg hl0 5
    nlinarith
  have hin0 : 0 ≤ 2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) +
      4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l)) := by
    have a1 : 0 ≤ 2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) h1l.le)
    have a2 : 0 ≤ 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ0) hs2)
        (div_nonneg (by positivity) h1l.le)
    linarith
  calc κ * (2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) + 4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l)))
      ≤ 3 * (2 * σ ^ 3 * (2 * l ^ 2 / (1 - l)) +
          4 * (1 - ρ) * σ ^ 2 * (2 * l ^ 0 / (1 - l))) := mul_le_mul_of_nonneg_right hκ3 hin0
    _ ≤ 3 * (2 * (144 ^ 3 * l ^ 3) * (3 * l ^ 2) +
          4 * (36 * 144 ^ 3 * l ^ 4) * (144 ^ 2 * l ^ 2) * 3) := by linarith
    _ = 18 * 144 ^ 3 * l ^ 5 + 1296 * 144 ^ 5 * l ^ 6 := by ring
    _ ≤ (18 * 144 ^ 3 + 1296 * 144 ^ 5) * l ^ 5 := by
        have h7 := mul_le_mul_of_nonneg_left hl6 (by norm_num : (0 : ℝ) ≤ 1296 * 144 ^ 5)
        linarith


-- The anatomy sum: reciprocals of the primes at least t dividing n.
noncomputable def anat (t : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ)

-- The Rankin weights.
noncomputable def hh (t : ℝ) (p : ℕ) : ℝ := Real.exp (16 * t / p) - 1

lemma anat_nonneg (t : ℝ) (n : ℕ) : 0 ≤ anat t n :=
  Finset.sum_nonneg (fun p _ => by positivity)

lemma hh_nonneg (t : ℝ) (ht : 0 ≤ t) (p : ℕ) : 0 ≤ hh t p := by
  unfold hh
  have : (0 : ℝ) ≤ 16 * t / p := by positivity
  linarith [Real.one_le_exp this]

lemma hh_le (t : ℝ) (ht : 0 ≤ t) (p : ℕ) (hp0 : 0 < p) (hp : t ≤ p) :
    hh t p ≤ 16 * Real.exp 16 * t / p := by
  unfold hh
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hu0 : (0 : ℝ) ≤ 16 * t / p := by positivity
  have hu16 : 16 * t / (p : ℝ) ≤ 16 := by
    rw [div_le_iff₀ hpR]
    nlinarith
  have h1 := Real.add_one_le_exp (-(16 * t / (p : ℝ)))
  have hpos := Real.exp_pos (16 * t / (p : ℝ))
  have h2 : Real.exp (-(16 * t / (p : ℝ))) * Real.exp (16 * t / (p : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp (16 * t / (p : ℝ)) - 1 ≤ 16 * t / p * Real.exp (16 * t / (p : ℝ)) := by
    nlinarith
  have h4 : Real.exp (16 * t / (p : ℝ)) ≤ Real.exp 16 := Real.exp_le_exp.2 hu16
  have h5 : 16 * t / p * Real.exp (16 * t / (p : ℝ)) ≤ 16 * t / p * Real.exp 16 :=
    mul_le_mul_of_nonneg_left h4 hu0
  have e : 16 * Real.exp 16 * t / p = 16 * t / p * Real.exp 16 := by ring
  rw [e]
  linarith

-- Reciprocal squares over an interval of integers starting at N.
lemma sum_inv_sq_Ico (N M : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ico N M, 1 / (n : ℝ) ^ 2 ≤ 2 / (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have key : ∀ M : ℕ, N ≤ M → ∑ n ∈ Ico N M, 1 / (n : ℝ) ^ 2 ≤ 2 / (N : ℝ) - 2 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM]
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast le_trans hN hM
      have hstep : 1 / (M : ℝ) ^ 2 ≤ 2 / (M : ℝ) - 2 / ((M + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases le_total N M with h | h
  · have h1 := key M h
    have h2 : (0 : ℝ) ≤ 2 / (M : ℝ) := by positivity
    linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

-- The total Rankin weight over any finite set of integers at least t.
lemma sum_hh_le (t : ℝ) (ht : 1 ≤ t) (P : Finset ℕ) (hP : ∀ p ∈ P, t ≤ p) :
    ∑ p ∈ P, hh t p / p ≤ 32 * Real.exp 16 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    have h := hP p hp
    have : (0 : ℝ) < p := by linarith
    exact_mod_cast this
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈t⌉₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.one_le_iff_ne_zero.2 (fun h => by
      have := Nat.ceil_eq_zero.1 h
      linarith)
  have htN : t ≤ N := by
    rw [hN]
    exact Nat.le_ceil t
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsub : P ⊆ Ico N (P.sup id + 1) := by
    intro p hp
    rw [mem_Ico]
    refine ⟨?_, Nat.lt_succ_of_le (Finset.le_sup (f := id) hp)⟩
    rw [hN]
    exact Nat.ceil_le.2 (hP p hp)
  have h1 : ∀ p ∈ P, hh t p / p ≤ 16 * Real.exp 16 * t * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpos p hp
    have h := hh_le t ht0 p (hpos p hp) (hP p hp)
    have h2 := div_le_div_of_nonneg_right h hpR.le
    refine h2.trans (le_of_eq ?_)
    field_simp
  calc ∑ p ∈ P, hh t p / p ≤ ∑ p ∈ P, 16 * Real.exp 16 * t * (1 / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum h1
    _ = 16 * Real.exp 16 * t * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 16 * Real.exp 16 * t * ∑ p ∈ Ico N (P.sup id + 1), 1 / (p : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ 16 * Real.exp 16 * t * (2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_Ico N _ hN1) (by positivity)
    _ ≤ 32 * Real.exp 16 := by
        have h3 : t * (2 / (N : ℝ)) ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ hNR]
          linarith
        have h4 : (0 : ℝ) ≤ 16 * Real.exp 16 := by positivity
        nlinarith

lemma prod_hh_le (t : ℝ) (ht : 1 ≤ t) (P : Finset ℕ) (hP : ∀ p ∈ P, t ≤ p) :
    ∏ p ∈ P, (1 + hh t p / p) ≤ Real.exp (32 * Real.exp 16) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  calc ∏ p ∈ P, (1 + hh t p / p) ≤ ∏ p ∈ P, Real.exp (hh t p / p) := by
        apply Finset.prod_le_prod
        · intro p _
          have := hh_nonneg t ht0 p
          positivity
        · intro p _
          linarith [Real.add_one_le_exp (hh t p / p)]
    _ = Real.exp (∑ p ∈ P, hh t p / p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (32 * Real.exp 16) := Real.exp_le_exp.2 (sum_hh_le t ht P hP)

-- The Rankin step: an integer with a large anatomy sum has a large product of weights.
lemma rankin (t c : ℝ) (ht : 0 ≤ t) (n : ℕ) (h : c ≤ anat t n) :
    1 ≤ Real.exp (-(16 * c * t)) *
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ p), (1 + hh t p) := by
  have e : ∏ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ p), (1 + hh t p) =
      Real.exp (16 * t * anat t n) := by
    unfold anat hh
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p _
    have e2 : 16 * t * (1 / (p : ℝ)) = 16 * t / p := by ring
    rw [e2]
    ring
  rw [e, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith [mul_nonneg ht (sub_nonneg.2 h)]


-- Reindexing a sum over the multiples of q up to x.
lemma sum_multiples (q x : ℕ) (hq : 0 < q) (G : ℕ → ℝ) :
    ∑ n ∈ (Ioc 0 x).filter (fun n => q ∣ n), G n = ∑ m ∈ Ioc 0 (x / q), G (q * m) := by
  symm
  apply Finset.sum_bij (fun k _ => q * k)
  · intro k hk
    obtain ⟨hk0, hkx⟩ := mem_Ioc.1 hk
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨Nat.mul_pos hq hk0, ?_⟩, dvd_mul_right q k⟩
    calc q * k ≤ q * (x / q) := Nat.mul_le_mul_left q hkx
      _ ≤ x := Nat.mul_div_le x q
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hq h
  · intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨hn0, hnx⟩, k, rfl⟩ := hn
    refine ⟨k, ?_, rfl⟩
    rw [mem_Ioc]
    refine ⟨Nat.pos_of_ne_zero (fun h0 => ?_), (Nat.le_div_iff_mul_le hq).2 ?_⟩
    · rw [h0, Nat.mul_zero] at hn0
      exact lt_irrefl 0 hn0
    · rwa [mul_comm]
  · intro _ _
    rfl

-- Divisibility of q m by the primes of a set not containing the prime q.
lemma filter_dvd_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) (hq : q.Prime)
    (hqP : q ∉ P) (m : ℕ) :
    P.filter (fun p => p ∣ q * m) = P.filter (fun p => p ∣ m) := by
  apply Finset.filter_congr
  intro p hp
  have hpp := hP p hp
  constructor
  · intro h
    rcases (hpp.dvd_mul).1 h with h1 | h1
    · exfalso
      have e := (Nat.prime_dvd_prime_iff_eq hpp hq).1 h1
      exact hqP (e ▸ hp)
    · exact h1
  · exact fun h => Dvd.dvd.mul_left h q

-- Splitting the product at a new prime q.
lemma prod_insert_split (P : Finset ℕ) (q : ℕ) (hqP : q ∉ P) (h : ℕ → ℝ) (n : ℕ) :
    ∏ p ∈ (insert q P).filter (fun p => p ∣ n), (1 + h p) =
      (∏ p ∈ P.filter (fun p => p ∣ n), (1 + h p)) +
        (if q ∣ n then h q * ∏ p ∈ P.filter (fun p => p ∣ n), (1 + h p) else 0) := by
  rw [Finset.filter_insert]
  split_ifs with hqn
  · rw [Finset.prod_insert (fun hmem => hqP (Finset.mem_of_mem_filter q hmem))]
    ring
  · ring

-- Summing the multiplicative weights over the integers up to x.
lemma sum_prod_div (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : ℕ → ℝ) (hh0 : ∀ p, 0 ≤ h p) :
    ∀ x : ℕ, ∑ n ∈ Ioc 0 x, ∏ p ∈ P.filter (fun p => p ∣ n), (1 + h p) ≤
      (x : ℝ) * ∏ p ∈ P, (1 + h p / p) := by
  induction P using Finset.induction_on with
  | empty =>
    intro x
    simp
  | insert q P hqP ih =>
    intro x
    have hq : q.Prime := hP q (mem_insert_self q P)
    have hPP : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have ihP := ih hPP
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hprod0 : 0 ≤ ∏ p ∈ P, (1 + h p / p) :=
      Finset.prod_nonneg (fun p _ => by
        have := hh0 p
        positivity)
    have e1 : ∑ n ∈ Ioc 0 x, ∏ p ∈ (insert q P).filter (fun p => p ∣ n), (1 + h p) =
        ∑ n ∈ Ioc 0 x, ∏ p ∈ P.filter (fun p => p ∣ n), (1 + h p) +
          h q * ∑ m ∈ Ioc 0 (x / q), ∏ p ∈ P.filter (fun p => p ∣ q * m), (1 + h p) := by
      rw [← sum_multiples q x hq.pos (fun n => ∏ p ∈ P.filter (fun p => p ∣ n), (1 + h p)),
        Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [prod_insert_split P q hqP h n]
    have hsecond : ∑ m ∈ Ioc 0 (x / q), ∏ p ∈ P.filter (fun p => p ∣ q * m), (1 + h p) ≤
        ((x : ℝ) / q) * ∏ p ∈ P, (1 + h p / p) := by
      have h1 := ihP (x / q)
      have h2 : ∑ m ∈ Ioc 0 (x / q), ∏ p ∈ P.filter (fun p => p ∣ q * m), (1 + h p) =
          ∑ m ∈ Ioc 0 (x / q), ∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [filter_dvd_mul P hPP q hq hqP m]
      rw [h2]
      exact h1.trans (mul_le_mul_of_nonneg_right Nat.cast_div_le hprod0)
    rw [e1, Finset.prod_insert hqP]
    have h1 := ihP x
    have h2 := mul_le_mul_of_nonneg_left hsecond (hh0 q)
    have e2 : (x : ℝ) * ((1 + h q / q) * ∏ p ∈ P, (1 + h p / p)) =
        (x : ℝ) * ∏ p ∈ P, (1 + h p / p) + h q * ((x : ℝ) / q * ∏ p ∈ P, (1 + h p / p)) := by
      field_simp
    rw [e2]
    linarith

-- Counting the integers up to x with a large anatomy sum.
lemma anat_count (x : ℕ) (t c : ℝ) (ht : 1 ≤ t) :
    (((Ioc 0 x).filter (fun n => c ≤ anat t n)).card : ℝ) ≤
      Real.exp (32 * Real.exp 16) * x * Real.exp (-(16 * c * t)) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = (Ioc 0 x).filter (fun p : ℕ => p.Prime ∧ t ≤ p) :=
    ⟨_, rfl⟩
  have hPp : ∀ p ∈ P, p.Prime := by
    intro p hp
    rw [hPdef, mem_filter] at hp
    exact hp.2.1
  have hPt : ∀ p ∈ P, t ≤ p := by
    intro p hp
    rw [hPdef, mem_filter] at hp
    exact hp.2.2
  have hfil : ∀ n ∈ Ioc 0 x, n.primeFactors.filter (fun p : ℕ => t ≤ p) =
      P.filter (fun p => p ∣ n) := by
    intro n hn
    obtain ⟨hn0, hnx⟩ := mem_Ioc.1 hn
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, hPdef, mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hd, _⟩, htp⟩
      exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd hn0 hd).trans hnx⟩, hp, htp⟩, hd⟩
    · rintro ⟨⟨_, hp, htp⟩, hd⟩
      exact ⟨⟨hp, hd, hn0.ne'⟩, htp⟩
  calc (((Ioc 0 x).filter (fun n => c ≤ anat t n)).card : ℝ)
      = ∑ n ∈ Ioc 0 x, (if c ≤ anat t n then (1 : ℝ) else 0) := Finset.natCast_card_filter _ _
    _ ≤ ∑ n ∈ Ioc 0 x, Real.exp (-(16 * c * t)) *
          ∏ p ∈ P.filter (fun p => p ∣ n), (1 + hh t p) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [← hfil n hn]
        split_ifs with hc
        · exact rankin t c ht0 n hc
        · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun p _ => by
            have := hh_nonneg t ht0 p
            linarith))
    _ = Real.exp (-(16 * c * t)) * ∑ n ∈ Ioc 0 x, ∏ p ∈ P.filter (fun p => p ∣ n), (1 + hh t p) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(16 * c * t)) * ((x : ℝ) * ∏ p ∈ P, (1 + hh t p / p)) :=
        mul_le_mul_of_nonneg_left (sum_prod_div P hPp (hh t) (hh_nonneg t ht0) x)
          (Real.exp_pos _).le
    _ ≤ Real.exp (-(16 * c * t)) * ((x : ℝ) * Real.exp (32 * Real.exp 16)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (prod_hh_le t ht P hPt) (Nat.cast_nonneg x)
    _ = _ := by ring


-- Reindexing a sum over the divisors of q M that are multiples of q.
lemma sum_divisors_mul (q M : ℕ) (hq : 0 < q) (hM : 0 < M) (F : ℕ → ℝ) :
    ∑ m ∈ (q * M).divisors.filter (fun m => q ∣ m), F m = ∑ m ∈ M.divisors, F (q * m) := by
  symm
  apply Finset.sum_bij (fun m _ => q * m)
  · intro m hm
    rw [Nat.mem_divisors] at hm
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left q hm.1, (Nat.mul_pos hq hM).ne'⟩, dvd_mul_right q m⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hq h
  · intro n hn
    rw [mem_filter, Nat.mem_divisors] at hn
    obtain ⟨⟨hd, _⟩, k, rfl⟩ := hn
    refine ⟨k, ?_, rfl⟩
    rw [Nat.mem_divisors]
    exact ⟨(Nat.mul_dvd_mul_iff_left hq).1 hd, hM.ne'⟩
  · intro _ _
    rfl

-- The divisor sum of the multiplicative weights against the totient.
lemma div_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : ℕ → ℝ) (hh0 : ∀ p, 0 ≤ h p) :
    ∀ M : ℕ, 0 < M →
      ∑ m ∈ M.divisors, (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) *
          (Nat.totient (M / m) : ℝ) ≤
        (M : ℝ) * ∏ p ∈ P.filter (fun p => p ∣ M), (1 + h p / p) := by
  induction P using Finset.induction_on with
  | empty =>
    intro M hM
    simp only [Finset.filter_empty, Finset.prod_empty, one_mul, mul_one]
    rw [Nat.sum_div_divisors M (fun d => (Nat.totient d : ℝ))]
    have h1 := Nat.sum_totient M
    have h2 : ((M.divisors.sum Nat.totient : ℕ) : ℝ) = (M : ℝ) := by rw [h1]
    rw [Nat.cast_sum] at h2
    exact h2.le
  | insert q P hqP ih =>
    intro M hM
    have hq : q.Prime := hP q (mem_insert_self q P)
    have hPP : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have ihP := ih hPP
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have e1 : ∑ m ∈ M.divisors, (∏ p ∈ (insert q P).filter (fun p => p ∣ m), (1 + h p)) *
          (Nat.totient (M / m) : ℝ) =
        ∑ m ∈ M.divisors, (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) *
          (Nat.totient (M / m) : ℝ) +
          h q * ∑ m ∈ M.divisors.filter (fun m => q ∣ m),
            (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) * (Nat.totient (M / m) : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      rw [prod_insert_split P q hqP h m]
      split_ifs <;> ring
    rw [e1]
    have h1 := ihP M hM
    by_cases hqM : q ∣ M
    · obtain ⟨M', rfl⟩ := hqM
      have hM' : 0 < M' := Nat.pos_of_ne_zero (fun h0 => by
        rw [h0, Nat.mul_zero] at hM
        exact lt_irrefl 0 hM)
      have e2 : ∑ m ∈ (q * M').divisors.filter (fun m => q ∣ m),
            (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) * (Nat.totient (q * M' / m) : ℝ) =
          ∑ m ∈ M'.divisors, (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) *
            (Nat.totient (M' / m) : ℝ) := by
        rw [sum_divisors_mul q M' hq.pos hM' (fun m =>
          (∏ p ∈ P.filter (fun p => p ∣ m), (1 + h p)) * (Nat.totient (q * M' / m) : ℝ))]
        apply Finset.sum_congr rfl
        intro m _
        rw [filter_dvd_mul P hPP q hq hqP m, Nat.mul_div_mul_left _ _ hq.pos]
      rw [e2]
      have h2 := ihP M' hM'
      have hsub : ∏ p ∈ P.filter (fun p => p ∣ M'), (1 + h p / p) ≤
          ∏ p ∈ P.filter (fun p => p ∣ q * M'), (1 + h p / p) := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · intro p hp
          rw [mem_filter] at hp ⊢
          exact ⟨hp.1, Dvd.dvd.mul_left hp.2 q⟩
        · intro p _
          have := hh0 p
          positivity
        · intro p _ _
          have h0 : 0 ≤ h p / p := div_nonneg (hh0 p) (Nat.cast_nonneg p)
          linarith
      have hins : (insert q P).filter (fun p => p ∣ q * M') =
          insert q (P.filter (fun p => p ∣ q * M')) := by
        rw [Finset.filter_insert, if_pos (dvd_mul_right q M')]
      rw [hins, Finset.prod_insert (fun hmem => hqP (Finset.mem_of_mem_filter q hmem))]
      have h3 := mul_le_mul_of_nonneg_left
        (h2.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg M'))) (hh0 q)
      push_cast at h1 ⊢
      have e3 : ((q : ℝ) * M') * ((1 + h q / q) *
          ∏ p ∈ P.filter (fun p => p ∣ q * M'), (1 + h p / p)) =
          (q : ℝ) * M' * ∏ p ∈ P.filter (fun p => p ∣ q * M'), (1 + h p / p) +
          h q * ((M' : ℝ) * ∏ p ∈ P.filter (fun p => p ∣ q * M'), (1 + h p / p)) := by
        field_simp
      rw [e3]
      linarith
    · have hempty : M.divisors.filter (fun m => q ∣ m) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro m hm hqm
        exact hqM (dvd_trans hqm (Nat.dvd_of_mem_divisors hm))
      rw [hempty, Finset.sum_empty, mul_zero, add_zero, Finset.filter_insert, if_neg hqM]
      exact h1

-- The divisor form of the anatomy lemma, for the totient.
lemma anat_div (M : ℕ) (hM : 0 < M) (t c : ℝ) (ht : 1 ≤ t) :
    ∑ m ∈ M.divisors.filter (fun m => c ≤ anat t m), (Nat.totient (M / m) : ℝ) ≤
      Real.exp (32 * Real.exp 16) * M * Real.exp (-(16 * c * t)) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = M.primeFactors.filter (fun p : ℕ => t ≤ p) :=
    ⟨_, rfl⟩
  have hPp : ∀ p ∈ P, p.Prime := by
    intro p hp
    rw [hPdef, mem_filter] at hp
    exact Nat.prime_of_mem_primeFactors hp.1
  have hPt : ∀ p ∈ P, t ≤ p := by
    intro p hp
    rw [hPdef, mem_filter] at hp
    exact hp.2
  have hfil : ∀ m ∈ M.divisors, m.primeFactors.filter (fun p : ℕ => t ≤ p) =
      P.filter (fun p => p ∣ m) := by
    intro m hm
    have hmd := Nat.dvd_of_mem_divisors hm
    have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, hPdef]
    constructor
    · rintro ⟨⟨hp, hd, _⟩, htp⟩
      exact ⟨⟨⟨hp, dvd_trans hd hmd, hM.ne'⟩, htp⟩, hd⟩
    · rintro ⟨⟨⟨hp, _, _⟩, htp⟩, hd⟩
      exact ⟨⟨hp, hd, hm0⟩, htp⟩
  calc ∑ m ∈ M.divisors.filter (fun m => c ≤ anat t m), (Nat.totient (M / m) : ℝ)
      = ∑ m ∈ M.divisors, (if c ≤ anat t m then (Nat.totient (M / m) : ℝ) else 0) :=
        Finset.sum_filter _ _
    _ ≤ ∑ m ∈ M.divisors, Real.exp (-(16 * c * t)) *
          ((∏ p ∈ P.filter (fun p => p ∣ m), (1 + hh t p)) * (Nat.totient (M / m) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [← hfil m hm]
        have hφ : (0 : ℝ) ≤ Nat.totient (M / m) := Nat.cast_nonneg _
        have hprod0 : (0 : ℝ) ≤ ∏ p ∈ m.primeFactors.filter (fun p : ℕ => t ≤ p), (1 + hh t p) :=
          Finset.prod_nonneg (fun p _ => by
            have := hh_nonneg t ht0 p
            linarith)
        split_ifs with hc
        · have hr := rankin t c ht0 m hc
          calc (Nat.totient (M / m) : ℝ) = 1 * (Nat.totient (M / m) : ℝ) := (one_mul _).symm
            _ ≤ (Real.exp (-(16 * c * t)) *
                ∏ p ∈ m.primeFactors.filter (fun p : ℕ => t ≤ p), (1 + hh t p)) *
                (Nat.totient (M / m) : ℝ) := mul_le_mul_of_nonneg_right hr hφ
            _ = _ := by ring
        · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hprod0 hφ)
    _ = Real.exp (-(16 * c * t)) * ∑ m ∈ M.divisors,
          (∏ p ∈ P.filter (fun p => p ∣ m), (1 + hh t p)) * (Nat.totient (M / m) : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(16 * c * t)) *
          ((M : ℝ) * ∏ p ∈ P.filter (fun p => p ∣ M), (1 + hh t p / p)) :=
        mul_le_mul_of_nonneg_left (div_sum_le P hPp (hh t) (hh_nonneg t ht0) M hM)
          (Real.exp_pos _).le
    _ ≤ Real.exp (-(16 * c * t)) * ((M : ℝ) * Real.exp (32 * Real.exp 16)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left
          (prod_hh_le t ht _ (fun p hp => hPt p (Finset.mem_of_mem_filter p hp)))
          (Nat.cast_nonneg M)
    _ = _ := by ring


-- Weights attached to a nonnegative function psi: phi(v) psi(v) / v.
noncomputable def wt (ψ : ℕ → ℝ) (v : ℕ) : ℝ := (Nat.totient v : ℝ) * ψ v / v

noncomputable def mu (ψ : ℕ → ℝ) (V : Finset ℕ) : ℝ := ∑ v ∈ V, wt ψ v

noncomputable def muE (ψ θ : ℕ → ℝ) (E : Finset (ℕ × ℕ)) : ℝ :=
  ∑ e ∈ E, wt ψ e.1 * wt θ e.2

-- The anatomy sum of a pair: primes at least t dividing v w / gcd(v, w)^2.
noncomputable def Lp (t : ℝ) (v w : ℕ) : ℝ := anat t (v * w / (Nat.gcd v w) ^ 2)

-- Admissible pairs.
def Adm (ψ θ : ℕ → ℝ) (t C : ℝ) (e : ℕ × ℕ) : Prop :=
  0 < e.1 ∧ 0 < e.2 ∧ (e.2 : ℝ) * ψ e.1 ≤ (Nat.gcd e.1 e.2 : ℝ) ∧
    (e.1 : ℝ) * θ e.2 ≤ (Nat.gcd e.1 e.2 : ℝ) ∧ C ≤ Lp t e.1 e.2

-- The primes dividing some element of V or W.
def PP (V W : Finset ℕ) : Finset ℕ := (V ∪ W).biUnion Nat.primeFactors

lemma wt_nonneg (ψ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (v : ℕ) : 0 ≤ wt ψ v := by
  unfold wt
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ v)) (Nat.cast_nonneg _)

lemma mu_nonneg (ψ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (V : Finset ℕ) : 0 ≤ mu ψ V :=
  Finset.sum_nonneg (fun v _ => wt_nonneg ψ hψ v)

lemma muE_nonneg (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ v, 0 ≤ θ v)
    (E : Finset (ℕ × ℕ)) : 0 ≤ muE ψ θ E :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (wt_nonneg ψ hψ e.1) (wt_nonneg θ hθ e.2))

lemma mu_mono (ψ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) {V V2 : Finset ℕ} (h : V ⊆ V2) :
    mu ψ V ≤ mu ψ V2 :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun v _ _ => wt_nonneg ψ hψ v)

lemma muE_mono (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ v, 0 ≤ θ v)
    {E E2 : Finset (ℕ × ℕ)} (h : E ⊆ E2) : muE ψ θ E ≤ muE ψ θ E2 :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun e _ _ => mul_nonneg (wt_nonneg ψ hψ e.1) (wt_nonneg θ hθ e.2))

-- The trivial bound: the weight of a set of pairs is at most the product of the weights.
lemma muE_le_mul (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ v, 0 ≤ θ v)
    (V W : Finset ℕ) (E : Finset (ℕ × ℕ)) (hE : E ⊆ V ×ˢ W) :
    muE ψ θ E ≤ mu ψ V * mu θ W := by
  have h1 := muE_mono ψ θ hψ hθ hE
  refine h1.trans (le_of_eq ?_)
  unfold muE mu
  rw [Finset.sum_product, Finset.sum_mul_sum]

-- Decomposition of a positive integer at a prime.
lemma val_decomp (p v i : ℕ) (hp : p.Prime) (hv : 0 < v) (hi : v.factorization p = i) :
    v = p ^ i * (v / p ^ i) ∧ Nat.Coprime p (v / p ^ i) ∧ 0 < v / p ^ i := by
  subst hi
  exact ⟨(Nat.ordProj_mul_ordCompl_eq_self v p).symm, Nat.coprime_ordCompl hp hv.ne',
    Nat.ordCompl_pos p hv.ne'⟩

lemma val_mul (p i v : ℕ) (hp : p.Prime) (hv : 0 < v) (hco : Nat.Coprime p v) :
    (p ^ i * v).factorization p = i ∧ (p ^ i * v) / p ^ i = v := by
  constructor
  · rw [Nat.factorization_mul (pow_pos hp.pos i).ne' hv.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hco), add_zero]
  · exact Nat.mul_div_cancel_left _ (pow_pos hp.pos i)

-- The gcd after splitting off the powers of p.
lemma gcd_pow_mul (p i j v w : ℕ) (hv : Nat.Coprime p v) (hw : Nat.Coprime p w) :
    Nat.gcd (p ^ i * v) (p ^ j * w) = p ^ (min i j) * Nat.gcd v w := by
  rcases le_total i j with h | h
  · rw [min_eq_left h]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, mul_assoc, Nat.gcd_mul_left]
    congr 1
    exact Nat.Coprime.gcd_mul_left_cancel_right w (Nat.Coprime.pow_left d hv)
  · rw [min_eq_right h]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, mul_assoc, Nat.gcd_mul_left]
    congr 1
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel_right v (Nat.Coprime.pow_left d hw),
      Nat.gcd_comm]

-- The quotient v w / gcd(v, w)^2 after splitting off the powers of p.
lemma quot_pow_mul (p i j v w : ℕ) (hp : p.Prime) (hv0 : 0 < v)
    (hv : Nat.Coprime p v) (hw : Nat.Coprime p w) :
    (p ^ i * v) * (p ^ j * w) / (Nat.gcd (p ^ i * v) (p ^ j * w)) ^ 2 =
      p ^ (Nat.dist i j) * (v * w / (Nat.gcd v w) ^ 2) := by
  rw [gcd_pow_mul p i j v w hv hw]
  have hg : 0 < Nat.gcd v w := Nat.gcd_pos_of_pos_left w hv0
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left v w
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right v w
  have hvw : v * w = (Nat.gcd v w) ^ 2 * (a * b) := by
    calc v * w = (Nat.gcd v w * a) * (Nat.gcd v w * b) := by rw [← ha, ← hb]
      _ = (Nat.gcd v w) ^ 2 * (a * b) := by ring
  have h1 : v * w / (Nat.gcd v w) ^ 2 = a * b := by
    rw [hvw]
    exact Nat.mul_div_cancel_left _ (pow_pos hg 2)
  rw [h1]
  have hexp : i + j = 2 * min i j + Nat.dist i j := by
    unfold Nat.dist
    rcases le_total i j with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      omega
  have h2 : (p ^ i * v) * (p ^ j * w) =
      (p ^ (min i j) * Nat.gcd v w) ^ 2 * (p ^ (Nat.dist i j) * (a * b)) := by
    have e1 : (p ^ i * v) * (p ^ j * w) = p ^ (i + j) * (v * w) := by ring
    rw [e1, hexp, hvw]
    ring
  rw [h2]
  exact Nat.mul_div_cancel_left _ (pow_pos (Nat.mul_pos (pow_pos hp.pos _) hg) 2)

-- Removing a power of p changes the anatomy sum by at most 1 / t.
lemma anat_pow_mul (p D n : ℕ) (hp : p.Prime) (hn : 0 < n) (t : ℝ) (ht : 1 ≤ t) :
    anat t (p ^ D * n) ≤ anat t n + (if D = 0 then 0 else 1 / t) := by
  by_cases hD : D = 0
  · subst hD
    simp
  · rw [if_neg hD]
    unfold anat
    rw [Nat.primeFactors_mul (pow_pos hp.pos D).ne' hn.ne', Nat.primeFactors_prime_pow hD hp,
      Finset.filter_union]
    have hnn : ∀ x : ℕ, (0 : ℝ) ≤ 1 / (x : ℝ) := fun x => by positivity
    have h1 := Finset.sum_union_inter (s₁ := ({p} : Finset ℕ).filter (fun q : ℕ => t ≤ q))
      (s₂ := n.primeFactors.filter (fun q : ℕ => t ≤ q)) (f := fun q : ℕ => 1 / (q : ℝ))
    have h2 : (0 : ℝ) ≤ ∑ q ∈ ({p} : Finset ℕ).filter (fun q : ℕ => t ≤ q) ∩
        n.primeFactors.filter (fun q : ℕ => t ≤ q), 1 / (q : ℝ) :=
      Finset.sum_nonneg (fun q _ => hnn q)
    have h3 : ∑ q ∈ ({p} : Finset ℕ).filter (fun q : ℕ => t ≤ q), 1 / (q : ℝ) ≤ 1 / t := by
      rw [Finset.filter_singleton]
      split_ifs with htp
      · rw [Finset.sum_singleton]
        exact one_div_le_one_div_of_le (by linarith) htp
      · rw [Finset.sum_empty]
        positivity
    linarith


-- The main claim, in fourth-power form, for systems with at most n primes.
def Claim (p0 n : ℕ) : Prop :=
  ∀ (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ)),
    (∀ v, 0 ≤ ψ v) → (∀ w, 0 ≤ θ w) → 1 ≤ t → (∀ v ∈ V, 0 < v) → (∀ w ∈ W, 0 < w) →
    E ⊆ V ×ˢ W → (∀ e ∈ E, Adm ψ θ t C e) → (PP V W).card ≤ n →
    muE ψ θ E ^ 4 ≤ ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) *
      (mu ψ V * mu θ W) ^ 3 * Real.exp (-(3 * C * t))

-- The weight after removing the prime power p^i and rescaling by p^a.
lemma wt_removal (p i a : ℕ) (hp : p.Prime) (ψ : ℕ → ℝ) (v : ℕ) (hv : 0 < v)
    (hco : Nat.Coprime p v) :
    wt (fun x => (p : ℝ) ^ a * ψ (p ^ i * x)) v =
      (p : ℝ) ^ a * (((p ^ i : ℕ) : ℝ) / (Nat.totient (p ^ i) : ℝ)) * wt ψ (p ^ i * v) := by
  unfold wt
  rw [Nat.totient_mul (Nat.Coprime.pow_left i hco)]
  have hpi : (0 : ℝ) < ((p ^ i : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos i
  have hφ : (0 : ℝ) < (Nat.totient (p ^ i) : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (pow_pos hp.pos i)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have e : (((p ^ i * v : ℕ)) : ℝ) = ((p ^ i : ℕ) : ℝ) * (v : ℝ) := by push_cast; ring
  rw [e, Nat.cast_mul]
  field_simp

lemma mu_removal (p i a : ℕ) (hp : p.Prime) (ψ : ℕ → ℝ) (V : Finset ℕ)
    (hV : ∀ v ∈ V, 0 < v) :
    mu (fun x => (p : ℝ) ^ a * ψ (p ^ i * x))
        ((V.filter (fun v => v.factorization p = i)).image (fun v => v / p ^ i)) =
      (p : ℝ) ^ a * (((p ^ i : ℕ) : ℝ) / (Nat.totient (p ^ i) : ℝ)) *
        mu ψ (V.filter (fun v => v.factorization p = i)) := by
  unfold mu
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [mem_filter] at hv
    obtain ⟨e1, hco, hpos⟩ := val_decomp p v i hp (hV v hv.1) hv.2
    rw [wt_removal p i a hp ψ (v / p ^ i) hpos hco, ← e1]
  · intro v1 h1 v2 h2 heq
    rw [Finset.mem_coe, mem_filter] at h1 h2
    obtain ⟨e1, _, _⟩ := val_decomp p v1 i hp (hV v1 h1.1) h1.2
    obtain ⟨e2, _, _⟩ := val_decomp p v2 i hp (hV v2 h2.1) h2.2
    have heq2 : v1 / p ^ i = v2 / p ^ i := heq
    rw [e1, e2, heq2]

lemma muE_removal (p i j a b : ℕ) (hp : p.Prime) (ψ θ : ℕ → ℝ) (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, 0 < e.1 ∧ 0 < e.2) :
    muE (fun x => (p : ℝ) ^ a * ψ (p ^ i * x)) (fun x => (p : ℝ) ^ b * θ (p ^ j * x))
        ((E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)).image
          (fun e => (e.1 / p ^ i, e.2 / p ^ j))) =
      ((p : ℝ) ^ a * (((p ^ i : ℕ) : ℝ) / (Nat.totient (p ^ i) : ℝ))) *
        ((p : ℝ) ^ b * (((p ^ j : ℕ) : ℝ) / (Nat.totient (p ^ j) : ℝ))) *
        muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) := by
  unfold muE
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro e he
    rw [mem_filter] at he
    obtain ⟨e1, hco1, hpos1⟩ := val_decomp p e.1 i hp (hE e he.1).1 he.2.1
    obtain ⟨e2, hco2, hpos2⟩ := val_decomp p e.2 j hp (hE e he.1).2 he.2.2
    simp only
    rw [wt_removal p i a hp ψ (e.1 / p ^ i) hpos1 hco1,
      wt_removal p j b hp θ (e.2 / p ^ j) hpos2 hco2, ← e1, ← e2]
    ring
  · intro x hx y hy heq
    rw [Finset.mem_coe, mem_filter] at hx hy
    obtain ⟨e1, _, _⟩ := val_decomp p x.1 i hp (hE x hx.1).1 hx.2.1
    obtain ⟨e2, _, _⟩ := val_decomp p x.2 j hp (hE x hx.1).2 hx.2.2
    obtain ⟨e3, _, _⟩ := val_decomp p y.1 i hp (hE y hy.1).1 hy.2.1
    obtain ⟨e4, _, _⟩ := val_decomp p y.2 j hp (hE y hy.1).2 hy.2.2
    have h1 : x.1 / p ^ i = y.1 / p ^ i := (Prod.mk.inj heq).1
    have h2 : x.2 / p ^ j = y.2 / p ^ j := (Prod.mk.inj heq).2
    apply Prod.ext
    · rw [e1, e3, h1]
    · rw [e2, e4, h2]

-- Admissibility survives the removal of the prime p, at the cost of 1 / t when i ≠ j.
lemma adm_removal (p i j : ℕ) (hp : p.Prime) (ψ θ : ℕ → ℝ) (t C : ℝ) (ht : 1 ≤ t)
    (e : ℕ × ℕ) (hA : Adm ψ θ t C e) (hi : e.1.factorization p = i)
    (hj : e.2.factorization p = j) :
    Adm (fun x => (p : ℝ) ^ (j - i) * ψ (p ^ i * x)) (fun x => (p : ℝ) ^ (i - j) * θ (p ^ j * x))
      t (C - (if i = j then 0 else 1 / t)) (e.1 / p ^ i, e.2 / p ^ j) := by
  obtain ⟨hv0, hw0, hψb, hθb, hL⟩ := hA
  obtain ⟨e1, hco1, hpos1⟩ := val_decomp p e.1 i hp hv0 hi
  obtain ⟨e2, hco2, hpos2⟩ := val_decomp p e.2 j hp hw0 hj
  obtain ⟨v, hv⟩ : ∃ v, v = e.1 / p ^ i := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = e.2 / p ^ j := ⟨_, rfl⟩
  rw [← hv] at e1 hco1 hpos1 ⊢
  rw [← hw] at e2 hco2 hpos2 ⊢
  have hgcd := gcd_pow_mul p i j v w hco1 hco2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmin : (0 : ℝ) < (p : ℝ) ^ (min i j) := pow_pos hpR _
  rw [e1, e2] at hψb hθb hL
  rw [hgcd] at hψb hθb
  refine ⟨hpos1, hpos2, ?_, ?_, ?_⟩
  · -- the bound for psi
    simp only
    have hsplit : (p : ℝ) ^ j = (p : ℝ) ^ (min i j) * (p : ℝ) ^ (j - i) := by
      rw [← pow_add]
      congr 1
      rcases le_total i j with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega
    have h1 : (p : ℝ) ^ (min i j) * ((w : ℝ) * ((p : ℝ) ^ (j - i) * ψ (p ^ i * v))) ≤
        (p : ℝ) ^ (min i j) * (Nat.gcd v w : ℝ) := by
      have e3 : (p : ℝ) ^ (min i j) * ((w : ℝ) * ((p : ℝ) ^ (j - i) * ψ (p ^ i * v))) =
          ((p ^ j * w : ℕ) : ℝ) * ψ (p ^ i * v) := by
        push_cast
        rw [hsplit]
        ring
      rw [e3]
      refine hψb.trans (le_of_eq ?_)
      push_cast
      ring
    exact le_of_mul_le_mul_left h1 hmin
  · simp only
    have hsplit : (p : ℝ) ^ i = (p : ℝ) ^ (min i j) * (p : ℝ) ^ (i - j) := by
      rw [← pow_add]
      congr 1
      rcases le_total i j with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega
    have h1 : (p : ℝ) ^ (min i j) * ((v : ℝ) * ((p : ℝ) ^ (i - j) * θ (p ^ j * w))) ≤
        (p : ℝ) ^ (min i j) * (Nat.gcd v w : ℝ) := by
      have e3 : (p : ℝ) ^ (min i j) * ((v : ℝ) * ((p : ℝ) ^ (i - j) * θ (p ^ j * w))) =
          ((p ^ i * v : ℕ) : ℝ) * θ (p ^ j * w) := by
        push_cast
        rw [hsplit]
        ring
      rw [e3]
      refine hθb.trans (le_of_eq ?_)
      push_cast
      ring
    exact le_of_mul_le_mul_left h1 hmin
  · simp only
    unfold Lp at hL ⊢
    rw [quot_pow_mul p i j v w hp hpos1 hco1 hco2] at hL
    have hg : 0 < Nat.gcd v w := Nat.gcd_pos_of_pos_left w hpos1
    have hn : 0 < v * w / (Nat.gcd v w) ^ 2 := by
      apply Nat.div_pos _ (pow_pos hg 2)
      have h1 : Nat.gcd v w ∣ v := Nat.gcd_dvd_left v w
      have h2 : Nat.gcd v w ∣ w := Nat.gcd_dvd_right v w
      rw [sq]
      exact Nat.le_of_dvd (Nat.mul_pos hpos1 hpos2) (Nat.mul_dvd_mul h1 h2)
    have h3 := anat_pow_mul p (Nat.dist i j) (v * w / (Nat.gcd v w) ^ 2) hp hn t ht
    have h4 : (if Nat.dist i j = 0 then (0 : ℝ) else 1 / t) = (if i = j then 0 else 1 / t) := by
      by_cases hij : i = j
      · rw [if_pos hij, if_pos (Nat.dist_eq_zero hij)]
      · rw [if_neg hij, if_neg (fun h => hij (Nat.eq_of_dist_eq_zero h))]
    rw [h4] at h3
    linarith


-- After removing p, the remaining primes lie in the old set without p.
lemma PP_removal (p i j : ℕ) (hp : p.Prime) (V W : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
    (hW : ∀ w ∈ W, 0 < w) :
    PP ((V.filter (fun v => v.factorization p = i)).image (fun v => v / p ^ i))
        ((W.filter (fun w => w.factorization p = j)).image (fun w => w / p ^ j)) ⊆
      (PP V W).erase p := by
  intro q hq
  unfold PP at hq ⊢
  rw [mem_biUnion] at hq
  obtain ⟨x, hx, hqx⟩ := hq
  rw [mem_erase, mem_biUnion]
  have hqp := Nat.prime_of_mem_primeFactors hqx
  have hqd := Nat.dvd_of_mem_primeFactors hqx
  rw [mem_union] at hx
  rcases hx with hx | hx
  · rw [mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [mem_filter] at hv
    obtain ⟨e1, hco, hpos⟩ := val_decomp p v i hp (hV v hv.1) hv.2
    constructor
    · rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hco hqd
    · refine ⟨v, mem_union_left _ hv.1, ?_⟩
      rw [Nat.mem_primeFactors]
      refine ⟨hqp, ?_, (hV v hv.1).ne'⟩
      rw [e1]
      exact Dvd.dvd.mul_left hqd _
  · rw [mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [mem_filter] at hw
    obtain ⟨e1, hco, hpos⟩ := val_decomp p w j hp (hW w hw.1) hw.2
    constructor
    · rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hco hqd
    · refine ⟨w, mem_union_right _ hw.1, ?_⟩
      rw [Nat.mem_primeFactors]
      refine ⟨hqp, ?_, (hW w hw.1).ne'⟩
      rw [e1]
      exact Dvd.dvd.mul_left hqd _

-- The arithmetic core of the removal step.
lemma removal_arith (X A Y K Ex pD : ℝ) (hX : 0 < X) (hpD : 0 < pD) (hpX : pD ≤ X)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hY : 0 ≤ Y) (hEx : 0 ≤ Ex)
    (h : (X * A) ^ 4 ≤ K * (X * Y) ^ 3 * Ex) :
    A ^ 4 ≤ K * Y ^ 3 * Ex * (1 / pD) := by
  have h1 : X ^ 3 * (X * A ^ 4) ≤ X ^ 3 * (K * Y ^ 3 * Ex) := by
    have e1 : X ^ 3 * (X * A ^ 4) = (X * A) ^ 4 := by ring
    have e2 : X ^ 3 * (K * Y ^ 3 * Ex) = K * (X * Y) ^ 3 * Ex := by ring
    rw [e1, e2]
    exact h
  have h2 : X * A ^ 4 ≤ K * Y ^ 3 * Ex := le_of_mul_le_mul_left h1 (pow_pos hX 3)
  have hR : 0 ≤ K * Y ^ 3 * Ex := mul_nonneg (mul_nonneg hK (pow_nonneg hY 3)) hEx
  have hA4 : 0 ≤ A ^ 4 := pow_nonneg hA 4
  have h3 : pD * A ^ 4 ≤ K * Y ^ 3 * Ex := (mul_le_mul_of_nonneg_right hpX hA4).trans h2
  rw [mul_one_div, le_div_iff₀ hpD]
  linarith

-- The bound for the part of the system with given valuations at p, from the claim for fewer
-- primes.
lemma removal_bound (p0 n : ℕ) (IH : ∀ m < n, Claim p0 m)
    (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 0 < v)
    (hW : ∀ w ∈ W, 0 < w) (hE : E ⊆ V ×ˢ W) (hA : ∀ e ∈ E, Adm ψ θ t C e)
    (hcard : (PP V W).card ≤ n) (p : ℕ) (hpP : p ∈ PP V W) (i j : ℕ) :
    muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) ^ 4 ≤
      (if p ≤ p0 then ((10 : ℝ) ^ 12)⁻¹ else 1) *
        ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) *
        (mu ψ (V.filter (fun v => v.factorization p = i)) *
          mu θ (W.filter (fun w => w.factorization p = j))) ^ 3 *
        (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) *
        (1 / (p : ℝ) ^ (Nat.dist i j)) := by
  have hp : p.Prime := by
    unfold PP at hpP
    rw [mem_biUnion] at hpP
    obtain ⟨x, _, hx⟩ := hpP
    exact Nat.prime_of_mem_primeFactors hx
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  obtain ⟨Vt, hVt⟩ : ∃ Vt : Finset ℕ, Vt =
      (V.filter (fun v => v.factorization p = i)).image (fun v => v / p ^ i) := ⟨_, rfl⟩
  obtain ⟨Wt, hWt⟩ : ∃ Wt : Finset ℕ, Wt =
      (W.filter (fun w => w.factorization p = j)).image (fun w => w / p ^ j) := ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ Et : Finset (ℕ × ℕ), Et =
      (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)).image
        (fun e => (e.1 / p ^ i, e.2 / p ^ j)) := ⟨_, rfl⟩
  have hEpos : ∀ e ∈ E, 0 < e.1 ∧ 0 < e.2 := fun e he => ⟨(hA e he).1, (hA e he).2.1⟩
  have hPPsub := PP_removal p i j hp V W hV hW
  rw [← hVt, ← hWt] at hPPsub
  have hcardt : (PP Vt Wt).card < n := by
    have h1 := Finset.card_le_card hPPsub
    rw [Finset.card_erase_of_mem hpP] at h1
    have h2 : 0 < (PP V W).card := Finset.card_pos.2 ⟨p, hpP⟩
    omega
  have hfiltcard : ((PP Vt Wt).filter (fun q => q ≤ p0)).card + (if p ≤ p0 then 1 else 0) ≤
      ((PP V W).filter (fun q => q ≤ p0)).card := by
    have hsub2 : (PP Vt Wt).filter (fun q => q ≤ p0) ⊆
        ((PP V W).filter (fun q => q ≤ p0)).erase p := by
      intro q hq
      rw [mem_filter] at hq
      have h1 := hPPsub hq.1
      rw [mem_erase] at h1 ⊢
      exact ⟨h1.1, mem_filter.2 ⟨h1.2, hq.2⟩⟩
    have h1 := Finset.card_le_card hsub2
    split_ifs with hpp0
    · rw [Finset.card_erase_of_mem (mem_filter.2 ⟨hpP, hpp0⟩)] at h1
      have h2 : 0 < ((PP V W).filter (fun q => q ≤ p0)).card :=
        Finset.card_pos.2 ⟨p, mem_filter.2 ⟨hpP, hpp0⟩⟩
      omega
    · have h2 := Finset.card_erase_le (s := (PP V W).filter (fun q => q ≤ p0)) (a := p)
      omega
  have hIH := IH (PP Vt Wt).card hcardt Vt Wt (fun x => (p : ℝ) ^ (j - i) * ψ (p ^ i * x))
    (fun x => (p : ℝ) ^ (i - j) * θ (p ^ j * x)) t (C - (if i = j then 0 else 1 / t)) Et
    (fun x => mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (hψ _))
    (fun x => mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (hθ _)) ht
    (by
      intro v hv
      rw [hVt, mem_image] at hv
      obtain ⟨v0, hv0, rfl⟩ := hv
      rw [mem_filter] at hv0
      exact (val_decomp p v0 i hp (hV v0 hv0.1) hv0.2).2.2)
    (by
      intro w hw
      rw [hWt, mem_image] at hw
      obtain ⟨w0, hw0, rfl⟩ := hw
      rw [mem_filter] at hw0
      exact (val_decomp p w0 j hp (hW w0 hw0.1) hw0.2).2.2)
    (by
      intro e he
      rw [hEt, mem_image] at he
      obtain ⟨e0, he0, rfl⟩ := he
      rw [mem_filter] at he0
      have hmem := hE he0.1
      rw [mem_product] at hmem ⊢
      rw [hVt, hWt]
      exact ⟨mem_image.2 ⟨e0.1, mem_filter.2 ⟨hmem.1, he0.2.1⟩, rfl⟩,
        mem_image.2 ⟨e0.2, mem_filter.2 ⟨hmem.2, he0.2.2⟩, rfl⟩⟩)
    (by
      intro e he
      rw [hEt, mem_image] at he
      obtain ⟨e0, he0, rfl⟩ := he
      rw [mem_filter] at he0
      exact adm_removal p i j hp ψ θ t C ht e0 (hA e0 he0.1) he0.2.1 he0.2.2)
    le_rfl
  rw [hEt, hVt, hWt, muE_removal p i j (j - i) (i - j) hp ψ θ E hEpos,
    mu_removal p i (j - i) hp ψ V hV, mu_removal p j (i - j) hp θ W hW] at hIH
  rw [← hVt, ← hWt] at hIH
  -- names for the real quantities
  obtain ⟨Xi, hXi⟩ : ∃ Xi : ℝ, Xi = (p : ℝ) ^ (j - i) *
      (((p ^ i : ℕ) : ℝ) / (Nat.totient (p ^ i) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Xj, hXj⟩ : ∃ Xj : ℝ, Xj = (p : ℝ) ^ (i - j) *
      (((p ^ j : ℕ) : ℝ) / (Nat.totient (p ^ j) : ℝ)) := ⟨_, rfl⟩
  have hratio : ∀ k : ℕ, (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) / (Nat.totient (p ^ k) : ℝ) := by
    intro k
    have hφ : (0 : ℝ) < (Nat.totient (p ^ k) : ℝ) := by
      exact_mod_cast Nat.totient_pos.2 (pow_pos hp.pos k)
    rw [le_div_iff₀ hφ, one_mul]
    exact_mod_cast Nat.totient_le (p ^ k)
  have hXi1 : (p : ℝ) ^ (j - i) ≤ Xi := by
    rw [hXi]
    have h1 := hratio i
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ (j - i) := pow_nonneg hpR.le _
    nlinarith
  have hXj1 : (p : ℝ) ^ (i - j) ≤ Xj := by
    rw [hXj]
    have h1 := hratio j
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ (i - j) := pow_nonneg hpR.le _
    nlinarith
  have hpa : (0 : ℝ) < (p : ℝ) ^ (j - i) := pow_pos hpR _
  have hpb : (0 : ℝ) < (p : ℝ) ^ (i - j) := pow_pos hpR _
  have hXi0 : 0 < Xi := lt_of_lt_of_le hpa hXi1
  have hXj0 : 0 < Xj := lt_of_lt_of_le hpb hXj1
  have hpD : (p : ℝ) ^ (Nat.dist i j) = (p : ℝ) ^ (j - i) * (p : ℝ) ^ (i - j) := by
    rw [← pow_add]
    congr 1
    unfold Nat.dist
    omega
  have hpX : (p : ℝ) ^ (Nat.dist i j) ≤ Xi * Xj := by
    rw [hpD]
    exact mul_le_mul hXi1 hXj1 hpb.le hXi0.le
  rw [← hXi, ← hXj] at hIH
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = muE ψ θ
      (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) := ⟨_, rfl⟩
  obtain ⟨Y1, hY1⟩ : ∃ Y : ℝ, Y = mu ψ (V.filter (fun v => v.factorization p = i)) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y : ℝ, Y = mu θ (W.filter (fun w => w.factorization p = j)) := ⟨_, rfl⟩
  rw [← hAdef, ← hY1, ← hY2] at hIH ⊢
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact muE_nonneg ψ θ hψ hθ _
  have hY10 : 0 ≤ Y1 := by
    rw [hY1]
    exact mu_nonneg ψ hψ _
  have hY20 : 0 ≤ Y2 := by
    rw [hY2]
    exact mu_nonneg θ hθ _
  -- the exponential factor
  have hexp : Real.exp (-(3 * (C - (if i = j then 0 else 1 / t)) * t)) =
      Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3) := by
    have ht0 : t ≠ 0 := by linarith
    split_ifs
    · rw [sub_zero, mul_one]
    · rw [← Real.exp_add]
      congr 1
      field_simp
      ring
  rw [hexp] at hIH
  have hEx0 : 0 ≤ Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3) := by
    apply mul_nonneg (Real.exp_pos _).le
    split_ifs
    · norm_num
    · exact (Real.exp_pos _).le
  have hM1 : (1 : ℝ) ≤ (10 : ℝ) ^ 12 := by norm_num
  have hK0 : (0 : ℝ) ≤ ((10 : ℝ) ^ 12) ^ (p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card) := by
    positivity
  have hIH2 : (Xi * Xj * A) ^ 4 ≤
      ((10 : ℝ) ^ 12) ^ (p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card) *
        (Xi * Xj * (Y1 * Y2)) ^ 3 *
        (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) := by
    have e : Xi * Xj * (Y1 * Y2) = Xi * Y1 * (Xj * Y2) := by ring
    rw [e]
    exact hIH
  have hres := removal_arith (Xi * Xj) A (Y1 * Y2) _ _ ((p : ℝ) ^ (Nat.dist i j))
    (mul_pos hXi0 hXj0) (pow_pos hpR _) hpX hA0 hK0 (mul_nonneg hY10 hY20) hEx0 hIH2
  refine hres.trans ?_
  -- compare the powers of 10^12
  have hK : ((10 : ℝ) ^ 12) ^ (p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card) ≤
      (if p ≤ p0 then ((10 : ℝ) ^ 12)⁻¹ else 1) *
        ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) := by
    split_ifs with hpp0
    · rw [if_pos hpp0] at hfiltcard
      have h1 : p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card + 1 ≤
          p0 + ((PP V W).filter (fun q => q ≤ p0)).card := by omega
      have h2 := pow_le_pow_right₀ hM1 h1
      rw [pow_succ] at h2
      rw [inv_mul_eq_div, le_div_iff₀ (by norm_num)]
      exact h2
    · rw [if_neg hpp0] at hfiltcard
      rw [one_mul]
      exact pow_le_pow_right₀ hM1 (by omega)
  have hrest : 0 ≤ (Y1 * Y2) ^ 3 *
      (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) *
      (1 / (p : ℝ) ^ (Nat.dist i j)) := by
    apply mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hY10 hY20) 3) hEx0)
    positivity
  calc ((10 : ℝ) ^ 12) ^ (p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card) * (Y1 * Y2) ^ 3 *
        (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) *
        (1 / (p : ℝ) ^ (Nat.dist i j))
      = ((10 : ℝ) ^ 12) ^ (p0 + ((PP Vt Wt).filter (fun q => q ≤ p0)).card) * ((Y1 * Y2) ^ 3 *
        (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) *
        (1 / (p : ℝ) ^ (Nat.dist i j))) := by ring
    _ ≤ ((if p ≤ p0 then ((10 : ℝ) ^ 12)⁻¹ else 1) *
        ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card)) * ((Y1 * Y2) ^ 3 *
        (Real.exp (-(3 * C * t)) * (if i = j then 1 else Real.exp 3)) *
        (1 / (p : ℝ) ^ (Nat.dist i j))) := mul_le_mul_of_nonneg_right hK hrest
    _ = _ := by ring


-- Partition of a sum over pairs by the valuations at p of the two coordinates.
lemma sum_partition_pairs (p n : ℕ) (E : Finset (ℕ × ℕ)) (F : ℕ × ℕ → ℝ)
    (hn : ∀ e ∈ E, e.1.factorization p < n ∧ e.2.factorization p < n) :
    ∑ e ∈ E, F e = ∑ i ∈ range n, ∑ j ∈ range n,
      ∑ e ∈ E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j), F e := by
  have hmaps : ∀ e ∈ E, (e.1.factorization p, e.2.factorization p) ∈ range n ×ˢ range n := by
    intro e he
    rw [mem_product, mem_range, mem_range]
    exact hn e he
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro e _
  rw [Prod.mk.injEq]

-- Partition of a sum over integers by the valuation at p.
lemma sum_partition (p n : ℕ) (V : Finset ℕ) (F : ℕ → ℝ)
    (hn : ∀ v ∈ V, v.factorization p < n) :
    ∑ v ∈ V, F v = ∑ i ∈ range n, ∑ v ∈ V.filter (fun v => v.factorization p = i), F v := by
  have hmaps : ∀ v ∈ V, v.factorization p ∈ range n := by
    intro v hv
    rw [mem_range]
    exact hn v hv
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]

-- The fourth root of 1 / p is at most 17/20 for p at least 2.
lemma r4_le_of_two (p : ℕ) (hp : 2 ≤ p) : r4 (1 / (p : ℝ)) ≤ 17 / 20 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply le_of_pow4_le (by norm_num)
  rw [r4_pow _ (by positivity)]
  have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
  calc 1 / (p : ℝ) ≤ 1 / 2 := h1
    _ ≤ (17 / 20 : ℝ) ^ 4 := by norm_num

-- The fourth root of 1 / p is at most 1/100 for p at least 10^8.
lemma r4_le_of_large (p : ℕ) (hp : 10 ^ 8 ≤ p) : r4 (1 / (p : ℝ)) ≤ 1 / 100 := by
  have hpR : (10 : ℝ) ^ 8 ≤ p := by exact_mod_cast hp
  apply le_of_pow4_le (by norm_num)
  rw [r4_pow _ (by positivity)]
  have h1 : 1 / (p : ℝ) ≤ 1 / 10 ^ 8 := one_div_le_one_div_of_le (by norm_num) hpR
  calc 1 / (p : ℝ) ≤ 1 / 10 ^ 8 := h1
    _ ≤ (1 / 100 : ℝ) ^ 4 := by norm_num

lemma exp_three_quarters_bounds : 1 ≤ Real.exp (3 / 4) ∧ Real.exp (3 / 4) ≤ 3 := by
  constructor
  · exact Real.one_le_exp (by norm_num)
  · have h1 : Real.exp (3 / 4) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    have h2 := Real.exp_one_lt_d9
    linarith


-- Positivity facts for a system violating the claimed bound.
lemma fail_pos (K : ℝ) (hK : 0 < K) (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (Ex : ℝ) (hEx : 0 < Ex)
    (E : Finset (ℕ × ℕ)) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (hE : E ⊆ V ×ˢ W)
    (hfail : K * (mu ψ V * mu θ W) ^ 3 * Ex < muE ψ θ E ^ 4) :
    0 < muE ψ θ E ∧ 0 < mu ψ V ∧ 0 < mu θ W := by
  have hT0 := muE_nonneg ψ θ hψ hθ E
  have ha0 := mu_nonneg ψ hψ V
  have hb0 := mu_nonneg θ hθ W
  have hle := muE_le_mul ψ θ hψ hθ V W E hE
  have hZ : 0 ≤ K * (mu ψ V * mu θ W) ^ 3 * Ex :=
    mul_nonneg (mul_nonneg hK.le (pow_nonneg (mul_nonneg ha0 hb0) 3)) hEx.le
  have hT : 0 < muE ψ θ E := by
    rcases hT0.eq_or_lt with h | h
    · rw [← h] at hfail
      norm_num at hfail
      linarith
    · exact h
  have hab : 0 < mu ψ V * mu θ W := lt_of_lt_of_le hT hle
  refine ⟨hT, ?_, ?_⟩
  · rcases ha0.eq_or_lt with h | h
    · rw [← h, zero_mul] at hab
      exact absurd hab (lt_irrefl 0)
    · exact h
  · rcases hb0.eq_or_lt with h | h
    · rw [← h, mul_zero] at hab
      exact absurd hab (lt_irrefl 0)
    · exact h

-- The bilinear bound for the normalized masses.
lemma bilinear_bound (p0 n : ℕ) (IH : ∀ m < n, Claim p0 m)
    (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 0 < v)
    (hW : ∀ w ∈ W, 0 < w) (hE : E ⊆ V ×ˢ W) (hA : ∀ e ∈ E, Adm ψ θ t C e)
    (hcard : (PP V W).card ≤ n)
    (hfail : ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) *
      (mu ψ V * mu θ W) ^ 3 * Real.exp (-(3 * C * t)) < muE ψ θ E ^ 4)
    (p : ℕ) (hpP : p ∈ PP V W) (i j : ℕ) :
    muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) /
        muE ψ θ E ≤
      (if p ≤ p0 then 1 / 1000 else 1) * (if i = j then 1 else Real.exp (3 / 4)) *
        r4 (1 / (p : ℝ)) ^ (Nat.dist i j) *
        (r4 (mu ψ (V.filter (fun v => v.factorization p = i)) / mu ψ V) *
          r4 (mu θ (W.filter (fun w => w.factorization p = j)) / mu θ W)) ^ 3 := by
  have hp : p.Prime := by
    unfold PP at hpP
    rw [mem_biUnion] at hpP
    obtain ⟨x, _, hx⟩ := hpP
    exact Nat.prime_of_mem_primeFactors hx
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K =
      ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    positivity
  rw [← hK] at hfail
  obtain ⟨hT, ha, hb⟩ := fail_pos K hKpos V W ψ θ _ (Real.exp_pos _) E hψ hθ hE hfail
  have hRB := removal_bound p0 n IH V W ψ θ t C E hψ hθ ht hV hW hE hA hcard p hpP i j
  rw [← hK] at hRB
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = muE ψ θ
      (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) := ⟨_, rfl⟩
  obtain ⟨Y1, hY1⟩ : ∃ Y : ℝ, Y = mu ψ (V.filter (fun v => v.factorization p = i)) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y : ℝ, Y = mu θ (W.filter (fun w => w.factorization p = j)) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = muE ψ θ E := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = mu ψ V := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = mu θ W := ⟨_, rfl⟩
  rw [← hAdef, ← hY1, ← hY2] at hRB ⊢
  rw [← hTdef, ← hadef, ← hbdef] at hfail ⊢
  rw [← hTdef] at hT
  rw [← hadef] at ha
  rw [← hbdef] at hb
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact muE_nonneg ψ θ hψ hθ _
  have hY10 : 0 ≤ Y1 := by
    rw [hY1]
    exact mu_nonneg ψ hψ _
  have hY20 : 0 ≤ Y2 := by
    rw [hY2]
    exact mu_nonneg θ hθ _
  have hα0 : 0 ≤ Y1 / a := div_nonneg hY10 ha.le
  have hβ0 : 0 ≤ Y2 / b := div_nonneg hY20 hb.le
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = (if p ≤ p0 then (1 : ℝ) / 1000 else 1) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (if i = j then (1 : ℝ) else Real.exp (3 / 4)) := ⟨_, rfl⟩
  rw [← hc1, ← hκ]
  have hc10 : 0 ≤ c1 := by
    rw [hc1]
    split_ifs <;> norm_num
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    split_ifs
    · norm_num
    · exact (Real.exp_pos _).le
  have hc14 : c1 ^ 4 = (if p ≤ p0 then ((10 : ℝ) ^ 12)⁻¹ else 1) := by
    rw [hc1]
    split_ifs <;> norm_num
  have hκ4 : κ ^ 4 = (if i = j then 1 else Real.exp 3) := by
    rw [hκ]
    split_ifs
    · norm_num
    · rw [← Real.exp_nat_mul]
      norm_num
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = r4 (1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = r4 (Y1 / a) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = r4 (Y2 / b) := ⟨_, rfl⟩
  rw [← hl, ← hu, ← hv]
  have hl4 : l ^ 4 = 1 / (p : ℝ) := by
    rw [hl]
    exact r4_pow _ (by positivity)
  have hu4 : u ^ 4 = Y1 / a := by
    rw [hu]
    exact r4_pow _ hα0
  have hv4 : v ^ 4 = Y2 / b := by
    rw [hv]
    exact r4_pow _ hβ0
  have hl0 : 0 ≤ l := by
    rw [hl]
    exact r4_nonneg _
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact r4_nonneg _
  have hv0 : 0 ≤ v := by
    rw [hv]
    exact r4_nonneg _
  have hRHS0 : 0 ≤ c1 * κ * l ^ (Nat.dist i j) * (u * v) ^ 3 := by positivity
  apply le_of_pow4_le hRHS0
  have hRHS4 : (c1 * κ * l ^ (Nat.dist i j) * (u * v) ^ 3) ^ 4 =
      c1 ^ 4 * κ ^ 4 * (1 / (p : ℝ)) ^ (Nat.dist i j) * ((Y1 / a) * (Y2 / b)) ^ 3 := by
    have e : (c1 * κ * l ^ (Nat.dist i j) * (u * v) ^ 3) ^ 4 =
        c1 ^ 4 * κ ^ 4 * (l ^ 4) ^ (Nat.dist i j) * (u ^ 4 * v ^ 4) ^ 3 := by ring
    rw [e, hl4, hu4, hv4]
  rw [hRHS4, hc14, hκ4, div_pow, div_le_iff₀ (pow_pos hT 4)]
  -- A^4 ≤ G * ((Y1 Y2)^3 * K * Ex) and K (a b)^3 Ex < T^4
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (if p ≤ p0 then ((10 : ℝ) ^ 12)⁻¹ else 1) *
      (if i = j then 1 else Real.exp 3) * (1 / (p : ℝ)) ^ (Nat.dist i j) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hG]
    apply mul_nonneg (mul_nonneg _ _) (by positivity)
    · split_ifs <;> norm_num
    · split_ifs
      · norm_num
      · exact (Real.exp_pos _).le
  have h1 : A ^ 4 ≤ G * ((Y1 * Y2) ^ 3 * (K * Real.exp (-(3 * C * t)))) := by
    refine hRB.trans (le_of_eq ?_)
    rw [hG, one_div_pow]
    ring
  have h2 : (Y1 * Y2) ^ 3 * (K * Real.exp (-(3 * C * t))) ≤
      ((Y1 / a) * (Y2 / b)) ^ 3 * T ^ 4 := by
    have e : (Y1 * Y2) ^ 3 * (K * Real.exp (-(3 * C * t))) =
        ((Y1 / a) * (Y2 / b)) ^ 3 * (K * (a * b) ^ 3 * Real.exp (-(3 * C * t))) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hfail.le (pow_nonneg (mul_nonneg hα0 hβ0) 3)
  calc A ^ 4 ≤ G * ((Y1 * Y2) ^ 3 * (K * Real.exp (-(3 * C * t)))) := h1
    _ ≤ G * (((Y1 / a) * (Y2 / b)) ^ 3 * T ^ 4) := mul_le_mul_of_nonneg_left h2 hG0
    _ = _ := by
        rw [hG]
        ring


-- For a system violating the claim, every prime exceeds p0 and the mass concentrates on
-- valuations within distance one of a common value k.
lemma prime_step (p0 n : ℕ) (hp0 : 10 ^ 8 ≤ p0) (IH : ∀ m < n, Claim p0 m)
    (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 0 < v)
    (hW : ∀ w ∈ W, 0 < w) (hE : E ⊆ V ×ˢ W) (hA : ∀ e ∈ E, Adm ψ θ t C e)
    (hcard : (PP V W).card ≤ n)
    (hfail : ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) *
      (mu ψ V * mu θ W) ^ 3 * Real.exp (-(3 * C * t)) < muE ψ θ E ^ 4)
    (p : ℕ) (hpP : p ∈ PP V W) :
    p0 < p ∧ ∃ k : ℕ, muE ψ θ (E.filter (fun e =>
        2 ≤ Nat.dist (e.1.factorization p) k + Nat.dist (e.2.factorization p) k)) ≤
      (18 * 144 ^ 3 + 1296 * 144 ^ 5) * r4 (1 / (p : ℝ)) ^ 5 * muE ψ θ E := by
  have hp : p.Prime := by
    unfold PP at hpP
    rw [mem_biUnion] at hpP
    obtain ⟨x, _, hx⟩ := hpP
    exact Nat.prime_of_mem_primeFactors hx
  have hKpos : (0 : ℝ) < ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) := by
    positivity
  obtain ⟨hT, ha, hb⟩ := fail_pos _ hKpos V W ψ θ _ (Real.exp_pos _) E hψ hθ hE hfail
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, n1 = (V ∪ W).sup (fun x => x.factorization p) + 1 := ⟨_, rfl⟩
  have hnV : ∀ v ∈ V, v.factorization p < n1 := by
    intro v hv
    rw [hn1]
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun x => x.factorization p) (mem_union_left _ hv))
  have hnW : ∀ w ∈ W, w.factorization p < n1 := by
    intro w hw
    rw [hn1]
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun x => x.factorization p) (mem_union_right _ hw))
  have hnE : ∀ e ∈ E, e.1.factorization p < n1 ∧ e.2.factorization p < n1 := by
    intro e he
    have hmem := hE he
    rw [mem_product] at hmem
    exact ⟨hnV _ hmem.1, hnW _ hmem.2⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℕ → ℝ, ∀ i j, m i j =
      muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) /
        muE ψ θ E := ⟨_, fun _ _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ i, u i =
      r4 (mu ψ (V.filter (fun v => v.factorization p = i)) / mu ψ V) := ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ j, v j =
      r4 (mu θ (W.filter (fun w => w.factorization p = j)) / mu θ W) := ⟨_, fun _ => rfl⟩
  have hu0 : ∀ i, 0 ≤ u i := fun i => by
    rw [hu]
    exact r4_nonneg _
  have hv0 : ∀ i, 0 ≤ v i := fun i => by
    rw [hv]
    exact r4_nonneg _
  have hU : ∑ i ∈ range n1, u i ^ 4 = 1 := by
    have e : ∀ i ∈ range n1, u i ^ 4 =
        mu ψ (V.filter (fun v => v.factorization p = i)) / mu ψ V := by
      intro i _
      rw [hu]
      exact r4_pow _ (div_nonneg (mu_nonneg ψ hψ _) ha.le)
    have hpart : ∑ i ∈ range n1, mu ψ (V.filter (fun v => v.factorization p = i)) = mu ψ V :=
      (sum_partition p n1 V (wt ψ) hnV).symm
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, hpart]
    exact div_self ha.ne'
  have hVs : ∑ j ∈ range n1, v j ^ 4 = 1 := by
    have e : ∀ j ∈ range n1, v j ^ 4 =
        mu θ (W.filter (fun w => w.factorization p = j)) / mu θ W := by
      intro j _
      rw [hv]
      exact r4_pow _ (div_nonneg (mu_nonneg θ hθ _) hb.le)
    have hpart : ∑ j ∈ range n1, mu θ (W.filter (fun w => w.factorization p = j)) = mu θ W :=
      (sum_partition p n1 W (wt θ) hnW).symm
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, hpart]
    exact div_self hb.ne'
  have hpartE : ∑ i ∈ range n1, ∑ j ∈ range n1,
      muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j)) =
      muE ψ θ E :=
    (sum_partition_pairs p n1 E (fun e => wt ψ e.1 * wt θ e.2) hnE).symm
  have hsum : ∑ i ∈ range n1, ∑ j ∈ range n1, m i j = 1 := by
    simp only [hm, ← Finset.sum_div]
    rw [hpartE]
    exact div_self hT.ne'
  have hbil : ∀ i j, m i j ≤ (if p ≤ p0 then 1 / 1000 else 1) *
      (if i = j then 1 else Real.exp (3 / 4)) * r4 (1 / (p : ℝ)) ^ (Nat.dist i j) *
      (u i * v j) ^ 3 := by
    intro i j
    rw [hm, hu, hv]
    exact bilinear_bound p0 n IH V W ψ θ t C E hψ hθ ht hV hW hE hA hcard hfail p hpP i j
  obtain ⟨hκ1, hκ3⟩ := exp_three_quarters_bounds
  have hl0 := r4_nonneg (1 / (p : ℝ))
  by_cases hpp0 : p ≤ p0
  · exfalso
    have hda := decay_a n1 m u v (r4 (1 / (p : ℝ))) (Real.exp (3 / 4)) (1 / 1000) hu0 hv0 hU hVs
      hl0 (r4_le_of_two p hp.two_le) (by linarith) hκ3 (by norm_num) (by
        intro i _ j _
        have h := hbil i j
        rw [if_pos hpp0] at h
        refine h.trans ?_
        have hX : 0 ≤ r4 (1 / (p : ℝ)) ^ (Nat.dist i j) * (u i * v j) ^ 3 :=
          mul_nonneg (pow_nonneg hl0 _) (pow_nonneg (mul_nonneg (hu0 i) (hv0 j)) 3)
        have hk : (if i = j then (1 : ℝ) else Real.exp (3 / 4)) ≤ Real.exp (3 / 4) := by
          split_ifs
          · exact hκ1
          · exact le_rfl
        calc 1 / 1000 * (if i = j then (1 : ℝ) else Real.exp (3 / 4)) *
              r4 (1 / (p : ℝ)) ^ (Nat.dist i j) * (u i * v j) ^ 3
            = 1 / 1000 * ((if i = j then (1 : ℝ) else Real.exp (3 / 4)) *
              (r4 (1 / (p : ℝ)) ^ (Nat.dist i j) * (u i * v j) ^ 3)) := by ring
          _ ≤ 1 / 1000 * (Real.exp (3 / 4) *
              (r4 (1 / (p : ℝ)) ^ (Nat.dist i j) * (u i * v j) ^ 3)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_right hk hX
          _ = _ := by ring)
    rw [hsum] at hda
    norm_num at hda
  · have hpgt : p0 < p := not_le.1 hpp0
    refine ⟨hpgt, ?_⟩
    have hl1 : r4 (1 / (p : ℝ)) ≤ 1 / 100 := r4_le_of_large p (by omega)
    obtain ⟨k, _, htail⟩ := decay_b n1 m u v (r4 (1 / (p : ℝ))) (Real.exp (3 / 4)) hu0 hv0 hU hVs
      hl0 hl1 hκ1 hκ3 hsum (by
        intro i _ j _
        have h := hbil i j
        rw [if_neg hpp0, one_mul] at h
        exact h)
    refine ⟨k, ?_⟩
    have e1 : muE ψ θ (E.filter (fun e =>
        2 ≤ Nat.dist (e.1.factorization p) k + Nat.dist (e.2.factorization p) k)) =
        ∑ i ∈ range n1, ∑ j ∈ range n1, (if 2 ≤ Nat.dist i k + Nat.dist j k then
          muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j))
          else 0) := by
      unfold muE
      rw [Finset.sum_filter, sum_partition_pairs p n1 E _ hnE]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hc : 2 ≤ Nat.dist i k + Nat.dist j k
      · rw [if_pos hc]
        apply Finset.sum_congr rfl
        intro e he
        rw [mem_filter] at he
        rw [he.2.1, he.2.2, if_pos hc]
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro e he
        rw [mem_filter] at he
        rw [he.2.1, he.2.2, if_neg hc]
    have e2 : ∑ i ∈ range n1, ∑ j ∈ range n1, (if 2 ≤ Nat.dist i k + Nat.dist j k then
          muE ψ θ (E.filter (fun e => e.1.factorization p = i ∧ e.2.factorization p = j))
          else 0) =
        muE ψ θ E * ∑ i ∈ range n1, ∑ j ∈ range n1,
          (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · rw [hm]
        field_simp
      · rw [mul_zero]
    rw [e1, e2]
    calc muE ψ θ E * ∑ i ∈ range n1, ∑ j ∈ range n1,
          (if 2 ≤ Nat.dist i k + Nat.dist j k then m i j else 0)
        ≤ muE ψ θ E * ((18 * 144 ^ 3 + 1296 * 144 ^ 5) * r4 (1 / (p : ℝ)) ^ 5) :=
          mul_le_mul_of_nonneg_left htail hT.le
      _ = _ := by ring


-- The fourth root of a fourth power.
lemma r4_pow_self (y : ℝ) (hy : 0 ≤ y) : r4 (y ^ 4) = y := by
  apply le_antisymm
  · apply le_of_pow4_le hy
    rw [r4_pow _ (by positivity)]
  · apply le_of_pow4_le (r4_nonneg _)
    rw [r4_pow _ (by positivity)]

-- The valuations of a product of prime powers.
lemma factorization_prod_pow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ S, p ^ k p).factorization q = if q ∈ S then k q else 0 := by
  rw [Nat.factorization_prod (fun p hp => (pow_pos (hS p hp).pos _).ne'), Finsupp.finsetSum_apply]
  have e : ∀ p ∈ S, (p ^ k p).factorization q = if p = q then k p else 0 := by
    intro p hp
    rw [Nat.Prime.factorization_pow (hS p hp), Finsupp.single_apply]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']

-- A violating system contains a subsystem of at least half the mass whose valuations all lie
-- within total distance one of those of a fixed integer N.
lemma structure_star (p0 k0 n : ℕ) (hk0 : 8 * (18 * 144 ^ 3 + 1296 * 144 ^ 5) ≤ k0)
    (hp0 : p0 = k0 ^ 4) (IH : ∀ m < n, Claim p0 m)
    (V W : Finset ℕ) (ψ θ : ℕ → ℝ) (t C : ℝ) (E : Finset (ℕ × ℕ))
    (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (ht : 1 ≤ t) (hV : ∀ v ∈ V, 0 < v)
    (hW : ∀ w ∈ W, 0 < w) (hE : E ⊆ V ×ˢ W) (hA : ∀ e ∈ E, Adm ψ θ t C e)
    (hcard : (PP V W).card ≤ n)
    (hfail : ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) *
      (mu ψ V * mu θ W) ^ 3 * Real.exp (-(3 * C * t)) < muE ψ θ E ^ 4) :
    ∃ N : ℕ, 0 < N ∧ ∃ Es : Finset (ℕ × ℕ), Es ⊆ E ∧ muE ψ θ E ≤ 2 * muE ψ θ Es ∧
      ∀ e ∈ Es, ∀ q : ℕ, q.Prime →
        Nat.dist (e.1.factorization q) (N.factorization q) +
          Nat.dist (e.2.factorization q) (N.factorization q) ≤ 1 := by
  have hk100 : 100 ≤ k0 := by
    refine le_trans ?_ hk0
    norm_num
  have hp0big : 10 ^ 8 ≤ p0 := by
    rw [hp0]
    calc 10 ^ 8 = 100 ^ 4 := by norm_num
      _ ≤ k0 ^ 4 := Nat.pow_le_pow_left hk100 4
  have hT0 := muE_nonneg ψ θ hψ hθ E
  have hPprime : ∀ p ∈ PP V W, p.Prime := by
    intro p hp
    unfold PP at hp
    rw [mem_biUnion] at hp
    obtain ⟨x, _, hx⟩ := hp
    exact Nat.prime_of_mem_primeFactors hx
  have hstep := fun p (hp : p ∈ PP V W) => prime_step p0 n hp0big IH V W ψ θ t C E hψ hθ ht hV hW
    hE hA hcard hfail p hp
  choose! k hk using (fun p (hp : p ∈ PP V W) => (hstep p hp).2)
  refine ⟨∏ p ∈ PP V W, p ^ k p, Finset.prod_pos (fun p hp => pow_pos (hPprime p hp).pos _),
    E.filter (fun e => ∀ p ∈ PP V W,
      Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1),
    Finset.filter_subset _ _, ?_, ?_⟩
  · -- the mass bound
    have hsplit := Finset.sum_filter_add_sum_filter_not E (fun e => ∀ p ∈ PP V W,
      Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1)
      (fun e => wt ψ e.1 * wt θ e.2)
    have hbad : ∑ e ∈ E.filter (fun e => ¬ ∀ p ∈ PP V W,
        Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1),
        wt ψ e.1 * wt θ e.2 ≤
        ∑ p ∈ PP V W, muE ψ θ (E.filter (fun e =>
          2 ≤ Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p))) := by
      unfold muE
      rw [Finset.sum_filter]
      have e2 : ∑ p ∈ PP V W, ∑ e ∈ E.filter (fun e =>
          2 ≤ Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p)),
          wt ψ e.1 * wt θ e.2 =
          ∑ e ∈ E, ∑ p ∈ PP V W, (if 2 ≤ Nat.dist (e.1.factorization p) (k p) +
            Nat.dist (e.2.factorization p) (k p) then wt ψ e.1 * wt θ e.2 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_filter]
      rw [e2]
      apply Finset.sum_le_sum
      intro e _
      have hw : 0 ≤ wt ψ e.1 * wt θ e.2 := mul_nonneg (wt_nonneg ψ hψ _) (wt_nonneg θ hθ _)
      have hnn : ∀ p ∈ PP V W, (0 : ℝ) ≤ (if 2 ≤ Nat.dist (e.1.factorization p) (k p) +
          Nat.dist (e.2.factorization p) (k p) then wt ψ e.1 * wt θ e.2 else 0) := by
        intro p _
        split_ifs
        · exact hw
        · exact le_rfl
      by_cases hc : ∀ p ∈ PP V W,
          Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1
      · rw [if_neg (not_not.2 hc)]
        exact Finset.sum_nonneg hnn
      · rw [if_pos hc]
        have hex : ∃ p ∈ PP V W, 2 ≤ Nat.dist (e.1.factorization p) (k p) +
            Nat.dist (e.2.factorization p) (k p) := by
          by_contra hcon
          apply hc
          intro p hp
          by_contra h1
          exact hcon ⟨p, hp, by omega⟩
        obtain ⟨p, hp, hp2⟩ := hex
        refine le_trans ?_ (Finset.single_le_sum hnn hp)
        rw [if_pos hp2]
    have hsumr : ∑ p ∈ PP V W, r4 (1 / (p : ℝ)) ^ 5 ≤ 4 * (1 / (k0 : ℝ)) := by
      have hsub : PP V W ⊆ Ioc p0 ((PP V W).sup id) := by
        intro p hp
        rw [mem_Ioc]
        exact ⟨(hstep p hp).1, Finset.le_sup (f := id) hp⟩
      have h1 : ∑ p ∈ PP V W, r4 (1 / (p : ℝ)) ^ 5 ≤
          ∑ p ∈ Ioc p0 ((PP V W).sup id), r4 (1 / (p : ℝ)) ^ 5 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => pow_nonneg (r4_nonneg _) 5)
      have h2 := r4_sum p0 ((PP V W).sup id) (by omega)
      have h3 : r4 (1 / (p0 : ℝ)) = 1 / (k0 : ℝ) := by
        have hk0R : (0 : ℝ) ≤ 1 / (k0 : ℝ) := by positivity
        have e : (1 : ℝ) / (p0 : ℝ) = (1 / (k0 : ℝ)) ^ 4 := by
          rw [hp0]
          push_cast
          rw [one_div_pow]
        rw [e]
        exact r4_pow_self _ hk0R
      rw [h3] at h2
      exact h1.trans h2
    have hbad2 : ∑ p ∈ PP V W, muE ψ θ (E.filter (fun e =>
          2 ≤ Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p))) ≤
        muE ψ θ E / 2 := by
      have h1 : ∑ p ∈ PP V W, muE ψ θ (E.filter (fun e =>
          2 ≤ Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p))) ≤
          ∑ p ∈ PP V W, (18 * 144 ^ 3 + 1296 * 144 ^ 5) * r4 (1 / (p : ℝ)) ^ 5 * muE ψ θ E :=
        Finset.sum_le_sum hk
      have e : ∑ p ∈ PP V W, (18 * 144 ^ 3 + 1296 * 144 ^ 5) * r4 (1 / (p : ℝ)) ^ 5 *
          muE ψ θ E = (18 * 144 ^ 3 + 1296 * 144 ^ 5) * muE ψ θ E *
            ∑ p ∈ PP V W, r4 (1 / (p : ℝ)) ^ 5 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [e] at h1
      have hk0R : (8 : ℝ) * (18 * 144 ^ 3 + 1296 * 144 ^ 5) ≤ k0 := by exact_mod_cast hk0
      have hk0pos : (0 : ℝ) < k0 := by linarith
      have h2 : (18 * 144 ^ 3 + 1296 * 144 ^ 5) * muE ψ θ E *
          ∑ p ∈ PP V W, r4 (1 / (p : ℝ)) ^ 5 ≤
          (18 * 144 ^ 3 + 1296 * 144 ^ 5) * muE ψ θ E * (4 * (1 / (k0 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsumr (by positivity)
      have h3 : (18 * 144 ^ 3 + 1296 * 144 ^ 5 : ℝ) * (4 * (1 / (k0 : ℝ))) ≤ 1 / 2 := by
        rw [mul_one_div, mul_div_assoc', div_le_iff₀ hk0pos]
        linarith
      have h4 : (18 * 144 ^ 3 + 1296 * 144 ^ 5) * muE ψ θ E * (4 * (1 / (k0 : ℝ))) =
          muE ψ θ E * ((18 * 144 ^ 3 + 1296 * 144 ^ 5 : ℝ) * (4 * (1 / (k0 : ℝ)))) := by ring
      have h5 := mul_le_mul_of_nonneg_left h3 hT0
      linarith
    have htot : muE ψ θ E = muE ψ θ (E.filter (fun e => ∀ p ∈ PP V W,
        Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1)) +
        ∑ e ∈ E.filter (fun e => ¬ ∀ p ∈ PP V W,
        Nat.dist (e.1.factorization p) (k p) + Nat.dist (e.2.factorization p) (k p) ≤ 1),
        wt ψ e.1 * wt θ e.2 := hsplit.symm
    linarith
  · -- the arithmetic structure
    intro e he q hq
    rw [mem_filter] at he
    rw [factorization_prod_pow (PP V W) hPprime k q]
    by_cases hqP : q ∈ PP V W
    · rw [if_pos hqP]
      exact he.2 q hqP
    · rw [if_neg hqP]
      have hmem := hE he.1
      rw [mem_product] at hmem
      have h1 : e.1.factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        apply hqP
        unfold PP
        rw [mem_biUnion]
        exact ⟨e.1, mem_union_left _ hmem.1, Nat.mem_primeFactors.2 ⟨hq, hd, (hV _ hmem.1).ne'⟩⟩
      have h2 : e.2.factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        apply hqP
        unfold PP
        rw [mem_biUnion]
        exact ⟨e.2, mem_union_right _ hmem.2, Nat.mem_primeFactors.2 ⟨hq, hd, (hW _ hmem.2).ne'⟩⟩
      rw [h1, h2]
      simp [Nat.dist]


-- A polynomial form of the inequality (1 - 3s/4)^4 ≥ (1 - s)^3.
lemma bern_poly (a x : ℝ) : a * (a - x) ^ 3 ≤ (a - 3 / 4 * x) ^ 4 := by
  have e : (a - 3 / 4 * x) ^ 4 - a * (a - x) ^ 3 =
      x ^ 2 * (3 / 8 * (a - 11 / 12 * x) ^ 2 + 1 / 768 * x ^ 2) := by ring
  have h : 0 ≤ x ^ 2 * (3 / 8 * (a - 11 / 12 * x) ^ 2 + 1 / 768 * x ^ 2) := by positivity
  linarith

-- Removing a vertex of small degree keeps the defining inequality of a near counterexample.
lemma removal_Q (Z0 A a b x g A2 a2 b2 : ℝ) (hZ : 0 ≤ Z0) (hA : Z0 * (a * b) ^ 3 < A ^ 4)
    (hA0 : 0 ≤ A) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hg : g * a < 3 / 4 * A) (hA2 : A2 = A - x * g) (ha2 : a2 ≤ a - x) (ha20 : 0 ≤ a2)
    (hb2 : b2 ≤ b) (hb20 : 0 ≤ b2) (hg0 : 0 ≤ g) : Z0 * (a2 * b2) ^ 3 < A2 ^ 4 := by
  have hApos : 0 < A := by
    rcases hA0.eq_or_lt with h | h
    · rw [← h] at hg
      have : 0 ≤ g * a := mul_nonneg hg0 ha0
      linarith
    · exact h
  rcases ha0.eq_or_lt with ha | ha
  · -- a = 0
    have hx : x = 0 := by linarith
    have ha2z : a2 = 0 := by linarith
    rw [hA2, hx, ha2z]
    simp only [zero_mul, sub_zero]
    have : (0 : ℝ) ^ 3 = 0 := by norm_num
    rw [this, mul_zero]
    positivity
  · have hpoly := bern_poly a x
    have hbase : 0 < a - 3 / 4 * x := by linarith
    have h1 : A * (a - 3 / 4 * x) ≤ A2 * a := by
      rw [hA2]
      have h2 : x * (g * a) ≤ x * (3 / 4 * A) := mul_le_mul_of_nonneg_left hg.le hx0
      nlinarith
    have h3 : (A * (a - 3 / 4 * x)) ^ 4 ≤ (A2 * a) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hA0 hbase.le) h1 4
    have hax : 0 ≤ a - x := by linarith
    have h4 : (a2 * b2) ^ 3 ≤ ((a - x) * b) ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg ha20 hb20) (mul_le_mul ha2 hb2 hb20 hax) 3
    have h5 : Z0 * (a2 * b2) ^ 3 * a ^ 4 ≤ Z0 * (a * b) ^ 3 * (a - 3 / 4 * x) ^ 4 := by
      have h6 : Z0 * (a2 * b2) ^ 3 * a ^ 4 ≤ Z0 * ((a - x) * b) ^ 3 * a ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hZ) (by positivity)
      have e : Z0 * ((a - x) * b) ^ 3 * a ^ 4 = Z0 * (a * b) ^ 3 * (a * (a - x) ^ 3) := by ring
      rw [e] at h6
      have h7 : Z0 * (a * b) ^ 3 * (a * (a - x) ^ 3) ≤ Z0 * (a * b) ^ 3 * (a - 3 / 4 * x) ^ 4 :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg hZ (pow_nonneg (mul_nonneg ha0 hb0) 3))
      linarith
    have h8 : Z0 * (a * b) ^ 3 * (a - 3 / 4 * x) ^ 4 < A ^ 4 * (a - 3 / 4 * x) ^ 4 :=
      mul_lt_mul_of_pos_right hA (pow_pos hbase 4)
    have h9 : A ^ 4 * (a - 3 / 4 * x) ^ 4 ≤ A2 ^ 4 * a ^ 4 := by
      have e1 : A ^ 4 * (a - 3 / 4 * x) ^ 4 = (A * (a - 3 / 4 * x)) ^ 4 := by ring
      have e2 : A2 ^ 4 * a ^ 4 = (A2 * a) ^ 4 := by ring
      rw [e1, e2]
      exact h3
    have h10 : Z0 * (a2 * b2) ^ 3 * a ^ 4 < A2 ^ 4 * a ^ 4 := by linarith
    exact lt_of_mul_lt_mul_right h10 (by positivity)

-- The mass of the pairs through a fixed first coordinate.
lemma muE_fiber_fst (ψ θ : ℕ → ℝ) (F : Finset (ℕ × ℕ)) (v : ℕ) :
    muE ψ θ (F.filter (fun e => e.1 = v)) =
      wt ψ v * mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) := by
  unfold muE mu
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro e he
    rw [(mem_filter.1 he).2]
  · intro e1 h1 e2 h2 heq
    rw [Finset.mem_coe, mem_filter] at h1 h2
    exact Prod.ext (h1.2.trans h2.2.symm) heq

lemma muE_fiber_snd (ψ θ : ℕ → ℝ) (F : Finset (ℕ × ℕ)) (w : ℕ) :
    muE ψ θ (F.filter (fun e => e.2 = w)) =
      mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) * wt θ w := by
  unfold muE mu
  rw [Finset.sum_image, Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro e he
    rw [(mem_filter.1 he).2]
  · intro e1 h1 e2 h2 heq
    rw [Finset.mem_coe, mem_filter] at h1 h2
    exact Prod.ext heq (h1.2.trans h2.2.symm)



-- Removing a first coordinate of small degree preserves the near counterexample inequality.
lemma remove_fst (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (Z0 : ℝ) (hZ : 0 ≤ Z0)
    (F : Finset (ℕ × ℕ)) (v : ℕ) (hv : v ∈ F.image Prod.fst)
    (hQ : Z0 * (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) ^ 3 < muE ψ θ F ^ 4)
    (hg : mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) * mu ψ (F.image Prod.fst) <
      3 / 4 * muE ψ θ F) :
    Z0 * (mu ψ ((F.filter (fun e => ¬ e.1 = v)).image Prod.fst) *
        mu θ ((F.filter (fun e => ¬ e.1 = v)).image Prod.snd)) ^ 3 <
      muE ψ θ (F.filter (fun e => ¬ e.1 = v)) ^ 4 := by
  have hA0 := muE_nonneg ψ θ hψ hθ F
  have ha0 := mu_nonneg ψ hψ (F.image Prod.fst)
  have hb0 := mu_nonneg θ hθ (F.image Prod.snd)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun e => e.1 = v)
    (fun e => wt ψ e.1 * wt θ e.2)
  have hA2 : muE ψ θ (F.filter (fun e => ¬ e.1 = v)) = muE ψ θ F -
      wt ψ v * mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) := by
    rw [← muE_fiber_fst]
    unfold muE
    linarith
  have hsub1 : (F.filter (fun e => ¬ e.1 = v)).image Prod.fst ⊆ (F.image Prod.fst).erase v := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    rw [mem_filter] at he
    exact mem_erase.2 ⟨he.2, mem_image.2 ⟨e, he.1, rfl⟩⟩
  have ha2 : mu ψ ((F.filter (fun e => ¬ e.1 = v)).image Prod.fst) ≤
      mu ψ (F.image Prod.fst) - wt ψ v := by
    refine (mu_mono ψ hψ hsub1).trans (le_of_eq ?_)
    unfold mu
    rw [Finset.sum_erase_eq_sub hv]
  have hb2 : mu θ ((F.filter (fun e => ¬ e.1 = v)).image Prod.snd) ≤
      mu θ (F.image Prod.snd) :=
    mu_mono θ hθ (Finset.image_subset_image (Finset.filter_subset _ _))
  have hxa : wt ψ v ≤ mu ψ (F.image Prod.fst) :=
    Finset.single_le_sum (f := fun x => wt ψ x) (fun x _ => wt_nonneg ψ hψ x) hv
  have hx0 := wt_nonneg ψ hψ v
  have hg0 := mu_nonneg θ hθ ((F.filter (fun e => e.1 = v)).image Prod.snd)
  have ha20 := mu_nonneg ψ hψ ((F.filter (fun e => ¬ e.1 = v)).image Prod.fst)
  have hb20 := mu_nonneg θ hθ ((F.filter (fun e => ¬ e.1 = v)).image Prod.snd)
  obtain ⟨A2, hA2d⟩ : ∃ A2 : ℝ, A2 = muE ψ θ (F.filter (fun e => ¬ e.1 = v)) := ⟨_, rfl⟩
  obtain ⟨a2, ha2d⟩ : ∃ a2 : ℝ, a2 = mu ψ ((F.filter (fun e => ¬ e.1 = v)).image Prod.fst) :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2 : ℝ, b2 = mu θ ((F.filter (fun e => ¬ e.1 = v)).image Prod.snd) :=
    ⟨_, rfl⟩
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = muE ψ θ F := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = mu ψ (F.image Prod.fst) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = mu θ (F.image Prod.snd) := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = wt ψ v := ⟨_, rfl⟩
  rw [← hA2d, ← ha2d, ← hb2d]
  rw [← hA2d, ← hgd, ← hAd, ← hxd] at hA2
  rw [← ha2d, ← had, ← hxd] at ha2
  rw [← hb2d, ← hbd] at hb2
  rw [← hxd, ← had] at hxa
  rw [← hgd, ← had, ← hAd] at hg
  rw [← had, ← hbd, ← hAd] at hQ
  rw [← hAd] at hA0
  rw [← had] at ha0
  rw [← hbd] at hb0
  rw [← hxd] at hx0
  rw [← hgd] at hg0
  rw [← ha2d] at ha20
  rw [← hb2d] at hb20
  exact removal_Q Z0 A a b x g A2 a2 b2 hZ hQ hA0 ha0 hb0 hx0 hxa hg hA2 ha2 ha20 hb2 hb20 hg0

-- The same for a second coordinate.
lemma remove_snd (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (Z0 : ℝ) (hZ : 0 ≤ Z0)
    (F : Finset (ℕ × ℕ)) (w : ℕ) (hw : w ∈ F.image Prod.snd)
    (hQ : Z0 * (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) ^ 3 < muE ψ θ F ^ 4)
    (hg : mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) * mu θ (F.image Prod.snd) <
      3 / 4 * muE ψ θ F) :
    Z0 * (mu ψ ((F.filter (fun e => ¬ e.2 = w)).image Prod.fst) *
        mu θ ((F.filter (fun e => ¬ e.2 = w)).image Prod.snd)) ^ 3 <
      muE ψ θ (F.filter (fun e => ¬ e.2 = w)) ^ 4 := by
  have hA0 := muE_nonneg ψ θ hψ hθ F
  have ha0 := mu_nonneg ψ hψ (F.image Prod.fst)
  have hb0 := mu_nonneg θ hθ (F.image Prod.snd)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun e => e.2 = w)
    (fun e => wt ψ e.1 * wt θ e.2)
  have hA2 : muE ψ θ (F.filter (fun e => ¬ e.2 = w)) = muE ψ θ F -
      wt θ w * mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) := by
    rw [mul_comm, ← muE_fiber_snd]
    unfold muE
    linarith
  have hsub1 : (F.filter (fun e => ¬ e.2 = w)).image Prod.snd ⊆ (F.image Prod.snd).erase w := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    rw [mem_filter] at he
    exact mem_erase.2 ⟨he.2, mem_image.2 ⟨e, he.1, rfl⟩⟩
  have hb2 : mu θ ((F.filter (fun e => ¬ e.2 = w)).image Prod.snd) ≤
      mu θ (F.image Prod.snd) - wt θ w := by
    refine (mu_mono θ hθ hsub1).trans (le_of_eq ?_)
    unfold mu
    rw [Finset.sum_erase_eq_sub hw]
  have ha2 : mu ψ ((F.filter (fun e => ¬ e.2 = w)).image Prod.fst) ≤
      mu ψ (F.image Prod.fst) :=
    mu_mono ψ hψ (Finset.image_subset_image (Finset.filter_subset _ _))
  have hxb : wt θ w ≤ mu θ (F.image Prod.snd) :=
    Finset.single_le_sum (f := fun x => wt θ x) (fun x _ => wt_nonneg θ hθ x) hw
  have hx0 := wt_nonneg θ hθ w
  have hg0 := mu_nonneg ψ hψ ((F.filter (fun e => e.2 = w)).image Prod.fst)
  have ha20 := mu_nonneg ψ hψ ((F.filter (fun e => ¬ e.2 = w)).image Prod.fst)
  have hb20 := mu_nonneg θ hθ ((F.filter (fun e => ¬ e.2 = w)).image Prod.snd)
  obtain ⟨A2, hA2d⟩ : ∃ A2 : ℝ, A2 = muE ψ θ (F.filter (fun e => ¬ e.2 = w)) := ⟨_, rfl⟩
  obtain ⟨a2, ha2d⟩ : ∃ a2 : ℝ, a2 = mu ψ ((F.filter (fun e => ¬ e.2 = w)).image Prod.fst) :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2 : ℝ, b2 = mu θ ((F.filter (fun e => ¬ e.2 = w)).image Prod.snd) :=
    ⟨_, rfl⟩
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = muE ψ θ F := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = mu ψ (F.image Prod.fst) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = mu θ (F.image Prod.snd) := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = wt θ w := ⟨_, rfl⟩
  rw [← hA2d, ← ha2d, ← hb2d]
  rw [← hA2d, ← hgd, ← hAd, ← hxd] at hA2
  rw [← hb2d, ← hbd, ← hxd] at hb2
  rw [← ha2d, ← had] at ha2
  rw [← hxd, ← hbd] at hxb
  rw [← hgd, ← hbd, ← hAd] at hg
  rw [← had, ← hbd, ← hAd] at hQ
  rw [← hAd] at hA0
  rw [← had] at ha0
  rw [← hbd] at hb0
  rw [← hxd] at hx0
  rw [← hgd] at hg0
  rw [← ha2d] at ha20
  rw [← hb2d] at hb20
  have hQ2 : Z0 * (b * a) ^ 3 < A ^ 4 := by
    rw [mul_comm b a]
    exact hQ
  have hres := removal_Q Z0 A b a x g A2 b2 a2 hZ hQ2 hA0 hb0 ha0 hx0 hxb hg hA2 hb2 hb20 ha2
    ha20 hg0
  rw [mul_comm a2 b2]
  exact hres

-- A near counterexample contains one with the minimum degree property on both sides.
lemma min_degree (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (Z0 : ℝ) (hZ : 0 ≤ Z0)
    (Es : Finset (ℕ × ℕ))
    (hQ : Z0 * (mu ψ (Es.image Prod.fst) * mu θ (Es.image Prod.snd)) ^ 3 < muE ψ θ Es ^ 4) :
    ∃ F : Finset (ℕ × ℕ), F ⊆ Es ∧
      Z0 * (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) ^ 3 < muE ψ θ F ^ 4 ∧
      (∀ v ∈ F.image Prod.fst, 3 / 4 * muE ψ θ F ≤
        mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) * mu ψ (F.image Prod.fst)) ∧
      (∀ w ∈ F.image Prod.snd, 3 / 4 * muE ψ θ F ≤
        mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) * mu θ (F.image Prod.snd)) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Finset (ℕ × ℕ)), ∀ F, F ∈ S ↔ (F ⊆ Es ∧
      Z0 * (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) ^ 3 < muE ψ θ F ^ 4) := by
    classical
    exact ⟨Es.powerset.filter (fun F =>
      Z0 * (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) ^ 3 < muE ψ θ F ^ 4),
      fun F => by rw [mem_filter, mem_powerset]⟩
  have hS : S.Nonempty := ⟨Es, (hSdef Es).2 ⟨Finset.Subset.refl _, hQ⟩⟩
  obtain ⟨F, hF, hmin⟩ := Finset.exists_min_image S Finset.card hS
  rw [hSdef] at hF
  refine ⟨F, hF.1, hF.2, ?_, ?_⟩
  · intro v hv
    by_contra hcon
    have hg := not_le.1 hcon
    obtain ⟨e0, he0, he0v⟩ := mem_image.1 hv
    have hQ2 := remove_fst ψ θ hψ hθ Z0 hZ F v hv hF.2 hg
    have hmem : F.filter (fun e => ¬ e.1 = v) ∈ S :=
      (hSdef _).2 ⟨(Finset.filter_subset _ _).trans hF.1, hQ2⟩
    have hcard : (F.filter (fun e => ¬ e.1 = v)).card < F.card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 ⟨e0, he0, fun h => h he0v⟩)
    exact absurd (hmin _ hmem) (not_le.2 hcard)
  · intro w hw
    by_contra hcon
    have hg := not_le.1 hcon
    obtain ⟨e0, he0, he0w⟩ := mem_image.1 hw
    have hQ2 := remove_snd ψ θ hψ hθ Z0 hZ F w hw hF.2 hg
    have hmem : F.filter (fun e => ¬ e.2 = w) ∈ S :=
      (hSdef _).2 ⟨(Finset.filter_subset _ _).trans hF.1, hQ2⟩
    have hcard : (F.filter (fun e => ¬ e.2 = w)).card < F.card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 ⟨e0, he0, fun h => h he0w⟩)
    exact absurd (hmin _ hmem) (not_le.2 hcard)


-- The parts of v above and below a reference integer N.
def vp (N v : ℕ) : ℕ := v / Nat.gcd v N

def vm (N v : ℕ) : ℕ := N / Nat.gcd v N

lemma vp_pos (N v : ℕ) (hv : 0 < v) : 0 < vp N v :=
  Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_left v N)) (Nat.gcd_pos_of_pos_left N hv)

lemma vm_pos (N v : ℕ) (hN : 0 < N) : 0 < vm N v :=
  Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right v N)) (Nat.gcd_pos_of_pos_right v hN)

lemma vm_dvd (N v : ℕ) : vm N v ∣ N := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v N)

lemma v_mul_vm (N v : ℕ) : v * vm N v = N * vp N v := by
  unfold vp vm
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left v N
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right v N
  rcases Nat.eq_zero_or_pos (Nat.gcd v N) with h0 | hpos
  · rw [h0]
    simp
  · have e1 : v / Nat.gcd v N = a := Nat.div_eq_of_eq_mul_right hpos ha
    have e2 : N / Nat.gcd v N = b := Nat.div_eq_of_eq_mul_right hpos hb
    rw [e1, e2]
    calc v * b = (Nat.gcd v N * a) * b := by rw [← ha]
      _ = (Nat.gcd v N * b) * a := by ring
      _ = N * a := by rw [← hb]

lemma N_div_vm (N v : ℕ) (hN : 0 < N) : N / vm N v = Nat.gcd v N := by
  unfold vm
  exact Nat.div_div_self (Nat.gcd_dvd_right v N) hN.ne'

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

-- The totient ratio decreases along divisibility.
lemma totient_ratio_mono (g v : ℕ) (hv : 0 < v) (hg : g ∣ v) :
    (Nat.totient v : ℝ) * g ≤ (Nat.totient g : ℝ) * v := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hv
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hX : ∀ p ∈ v.primeFactors, (0 : ℝ) ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have h0 : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hsub : g.primeFactors ⊆ v.primeFactors := Nat.primeFactors_mono hg hv.ne'
  have h1 : ∏ p ∈ v.primeFactors, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_sdiff hsub]
    have h2 : ∏ p ∈ v.primeFactors \ g.primeFactors, (1 - 1 / (p : ℝ)) ≤ 1 :=
      Finset.prod_le_one (fun p hp => (hX p (Finset.mem_sdiff.1 hp).1).1)
        (fun p hp => (hX p (Finset.mem_sdiff.1 hp).1).2)
    have h3 : (0 : ℝ) ≤ ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg (fun p hp => (hX p (hsub hp)).1)
    exact (mul_le_mul_of_nonneg_right h2 h3).trans (le_of_eq (one_mul _))
  rw [← totient_ratio v hv, ← totient_ratio g hg0, div_le_div_iff₀ hvR hgR] at h1
  exact h1


-- Under the structure condition, gcd(v, w) N = gcd(v, N) gcd(w, N).
lemma gcd_structure (v w N : ℕ) (hv : 0 < v) (hw : 0 < w) (hN : 0 < N)
    (hs : ∀ q : ℕ, q.Prime → Nat.dist (v.factorization q) (N.factorization q) +
      Nat.dist (w.factorization q) (N.factorization q) ≤ 1) :
    Nat.gcd v w * N = Nat.gcd v N * Nat.gcd w N := by
  have hg1 : Nat.gcd v w ≠ 0 := (Nat.gcd_pos_of_pos_left w hv).ne'
  have hg2 : Nat.gcd v N ≠ 0 := (Nat.gcd_pos_of_pos_left N hv).ne'
  have hg3 : Nat.gcd w N ≠ 0 := (Nat.gcd_pos_of_pos_left N hw).ne'
  apply Nat.eq_of_factorization_eq (mul_ne_zero hg1 hN.ne') (mul_ne_zero hg2 hg3)
  intro q
  rw [Nat.factorization_mul hg1 hN.ne', Nat.factorization_mul hg2 hg3, Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_gcd hv.ne' hw.ne', Nat.factorization_gcd hv.ne' hN.ne',
    Nat.factorization_gcd hw.ne' hN.ne', Finsupp.inf_apply, Finsupp.inf_apply, Finsupp.inf_apply]
  by_cases hq : q.Prime
  · have h := hs q hq
    unfold Nat.dist at h
    rw [min_def, min_def, min_def]
    split_ifs <;> omega
  · rw [Nat.factorization_eq_zero_of_not_prime v hq, Nat.factorization_eq_zero_of_not_prime w hq,
      Nat.factorization_eq_zero_of_not_prime N hq]
    simp

-- The bound psi(v) ≤ 1 / (v^- w^+) for an admissible structured pair.
lemma psi_bound (ψ : ℕ → ℝ) (v w N : ℕ) (hv : 0 < v) (hw : 0 < w) (hN : 0 < N)
    (hs : ∀ q : ℕ, q.Prime → Nat.dist (v.factorization q) (N.factorization q) +
      Nat.dist (w.factorization q) (N.factorization q) ≤ 1)
    (hψ : (w : ℝ) * ψ v ≤ (Nat.gcd v w : ℝ)) :
    ψ v * ((vm N v : ℝ) * (vp N w : ℝ)) ≤ 1 := by
  have hid := gcd_structure v w N hv hw hN hs
  have e1 : vm N v * Nat.gcd v N = N := Nat.div_mul_cancel (Nat.gcd_dvd_right v N)
  have e2 : vp N w * Nat.gcd w N = w := Nat.div_mul_cancel (Nat.gcd_dvd_left w N)
  have hg2 : (0 : ℝ) < (Nat.gcd v N : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left N hv
  have hg3 : (0 : ℝ) < (Nat.gcd w N : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left N hw
  have hgvw : (0 : ℝ) < (Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ) := mul_pos hg2 hg3
  have e1R : (vm N v : ℝ) * (Nat.gcd v N : ℝ) = N := by exact_mod_cast e1
  have e2R : (vp N w : ℝ) * (Nat.gcd w N : ℝ) = w := by exact_mod_cast e2
  have hidR : (Nat.gcd v w : ℝ) * N = (Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ) := by
    exact_mod_cast hid
  have key : ψ v * ((vm N v : ℝ) * (vp N w : ℝ)) * ((Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ)) ≤
      1 * ((Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ)) := by
    calc ψ v * ((vm N v : ℝ) * (vp N w : ℝ)) * ((Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ))
        = ψ v * (((vm N v : ℝ) * (Nat.gcd v N : ℝ)) * ((vp N w : ℝ) * (Nat.gcd w N : ℝ))) := by
          ring
      _ = ((w : ℝ) * ψ v) * N := by
          rw [e1R, e2R]
          ring
      _ ≤ (Nat.gcd v w : ℝ) * N := mul_le_mul_of_nonneg_right hψ (Nat.cast_nonneg N)
      _ = 1 * ((Nat.gcd v N : ℝ) * (Nat.gcd w N : ℝ)) := by rw [hidR, one_mul]
  exact le_of_mul_le_mul_right key hgvw

-- Divisibility of the upper and lower parts by a prime, from the valuations.
lemma dvd_vp_of_lt (q v N : ℕ) (hq : q.Prime) (hv : 0 < v) (hN : 0 < N)
    (h : N.factorization q < v.factorization q) : q ∣ vp N v := by
  rw [hq.dvd_iff_one_le_factorization (vp_pos N v hv).ne']
  unfold vp
  rw [Nat.factorization_div (Nat.gcd_dvd_left v N), Finsupp.tsub_apply,
    Nat.factorization_gcd hv.ne' hN.ne', Finsupp.inf_apply]
  rw [min_def]
  split_ifs <;> omega

lemma dvd_vm_of_lt (q v N : ℕ) (hq : q.Prime) (hv : 0 < v) (hN : 0 < N)
    (h : v.factorization q < N.factorization q) : q ∣ vm N v := by
  rw [hq.dvd_iff_one_le_factorization (vm_pos N v hN).ne']
  unfold vm
  rw [Nat.factorization_div (Nat.gcd_dvd_right v N), Finsupp.tsub_apply,
    Nat.factorization_gcd hv.ne' hN.ne', Finsupp.inf_apply]
  rw [min_def]
  split_ifs <;> omega

-- Anatomy sums over a union of sets of primes.
lemma anat_union_le (t : ℝ) (S1 S2 : Finset ℕ) :
    ∑ p ∈ (S1 ∪ S2).filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ) ≤
      ∑ p ∈ S1.filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ) +
        ∑ p ∈ S2.filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ) := by
  rw [Finset.filter_union]
  have h1 := Finset.sum_union_inter (s₁ := S1.filter (fun p : ℕ => t ≤ p))
    (s₂ := S2.filter (fun p : ℕ => t ≤ p)) (f := fun p : ℕ => 1 / (p : ℝ))
  have h2 : (0 : ℝ) ≤ ∑ p ∈ S1.filter (fun p : ℕ => t ≤ p) ∩ S2.filter (fun p : ℕ => t ≤ p),
      1 / (p : ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
  linarith

-- The anatomy sum of a structured pair splits over the four parts.
lemma anat_split (v w N : ℕ) (hv : 0 < v) (hw : 0 < w) (hN : 0 < N)
    (hs : ∀ q : ℕ, q.Prime → Nat.dist (v.factorization q) (N.factorization q) +
      Nat.dist (w.factorization q) (N.factorization q) ≤ 1) (t : ℝ) :
    Lp t v w ≤ anat t (vp N v) + anat t (vm N v) + anat t (vp N w) + anat t (vm N w) := by
  have hg : 0 < Nat.gcd v w := Nat.gcd_pos_of_pos_left w hv
  have hdiv : (Nat.gcd v w) ^ 2 ∣ v * w := by
    rw [sq]
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_left v w) (Nat.gcd_dvd_right v w)
  have hn0 : v * w / (Nat.gcd v w) ^ 2 ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hv hw) hdiv) (pow_pos hg 2)
  have hsub : (v * w / (Nat.gcd v w) ^ 2).primeFactors ⊆
      (vp N v).primeFactors ∪ (vm N v).primeFactors ∪ (vp N w).primeFactors ∪
        (vm N w).primeFactors := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have h1 : 1 ≤ (v * w / (Nat.gcd v w) ^ 2).factorization q :=
      (hqp.dvd_iff_one_le_factorization hn0).1 hqd
    have h2 : (v * w / (Nat.gcd v w) ^ 2).factorization q + 2 * (Nat.gcd v w).factorization q =
        v.factorization q + w.factorization q := by
      have e := Nat.div_mul_cancel hdiv
      have e2 : (v * w / (Nat.gcd v w) ^ 2 * (Nat.gcd v w) ^ 2).factorization q =
          (v * w).factorization q := by rw [e]
      rw [Nat.factorization_mul hn0 (pow_pos hg 2).ne', Nat.factorization_mul hv.ne' hw.ne',
        Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
        smul_eq_mul] at e2
      exact e2
    have h3 : (Nat.gcd v w).factorization q = min (v.factorization q) (w.factorization q) := by
      rw [Nat.factorization_gcd hv.ne' hw.ne', Finsupp.inf_apply]
    have h4 := hs q hqp
    unfold Nat.dist at h4
    have h5 : N.factorization q < v.factorization q ∨ v.factorization q < N.factorization q ∨
        N.factorization q < w.factorization q ∨ w.factorization q < N.factorization q := by
      rw [h3, min_def] at h2
      split_ifs at h2 <;> omega
    simp only [mem_union, Nat.mem_primeFactors]
    rcases h5 with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hqp, dvd_vp_of_lt q v N hqp hv hN h, (vp_pos N v hv).ne'⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hqp, dvd_vm_of_lt q v N hqp hv hN h, (vm_pos N v hN).ne'⟩))
    · exact Or.inl (Or.inr ⟨hqp, dvd_vp_of_lt q w N hqp hw hN h, (vp_pos N w hw).ne'⟩)
    · exact Or.inr ⟨hqp, dvd_vm_of_lt q w N hqp hw hN h, (vm_pos N w hN).ne'⟩
  unfold Lp anat
  have h1 : ∑ p ∈ (v * w / (Nat.gcd v w) ^ 2).primeFactors.filter (fun p : ℕ => t ≤ p),
      1 / (p : ℝ) ≤ ∑ p ∈ ((vp N v).primeFactors ∪ (vm N v).primeFactors ∪
        (vp N w).primeFactors ∪ (vm N w).primeFactors).filter (fun p : ℕ => t ≤ p),
        1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hsub)
      (fun p _ _ => by positivity)
  have h2 := anat_union_le t ((vp N v).primeFactors ∪ (vm N v).primeFactors ∪
    (vp N w).primeFactors) (vm N w).primeFactors
  have h3 := anat_union_le t ((vp N v).primeFactors ∪ (vm N v).primeFactors)
    (vp N w).primeFactors
  have h4 := anat_union_le t (vp N v).primeFactors (vm N v).primeFactors
  linarith


-- The pair (v^+, v^-) determines v.
lemma vp_vm_inj (N : ℕ) (hN : 0 < N) (v1 v2 : ℕ) (h1 : vp N v1 = vp N v2)
    (h2 : vm N v1 = vm N v2) : v1 = v2 := by
  have e1 := v_mul_vm N v1
  have e2 := v_mul_vm N v2
  rw [h1, h2] at e1
  exact Nat.eq_of_mul_eq_mul_right (vm_pos N v2 hN) (e1.trans e2.symm)

-- The basic termwise bound: phi(v) / (v v^-) ≤ phi(N / v^-) / N.
lemma term_bound (N v : ℕ) (hN : 0 < N) (hv : 0 < v) :
    (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) ≤ (Nat.totient (N / vm N v) : ℝ) / N := by
  rw [N_div_vm N v hN]
  have hmono := totient_ratio_mono (Nat.gcd v N) v hv (Nat.gcd_dvd_left v N)
  have e : (vm N v : ℝ) * (Nat.gcd v N : ℝ) = N := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right v N)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hvm : (0 : ℝ) < vm N v := by exact_mod_cast vm_pos N v hN
  rw [div_le_div_iff₀ (mul_pos hvR hvm) hNR]
  calc (Nat.totient v : ℝ) * N
      = ((Nat.totient v : ℝ) * (Nat.gcd v N : ℝ)) * (vm N v : ℝ) := by
        rw [← e]
        ring
    _ ≤ ((Nat.totient (Nat.gcd v N) : ℝ) * (v : ℝ)) * (vm N v : ℝ) :=
        mul_le_mul_of_nonneg_right hmono hvm.le
    _ = (Nat.totient (Nat.gcd v N) : ℝ) * ((v : ℝ) * (vm N v : ℝ)) := by ring

-- Sums over a set of integers with bounded upper part, reparametrized by (v^+, v^-).
lemma param_sum (N : ℕ) (hN : 0 < N) (U : Finset ℕ) (hU : ∀ v ∈ U, 0 < v) (X : ℕ)
    (hX : ∀ v ∈ U, vp N v ≤ X) (P : ℕ → ℕ → Prop) [∀ m d, Decidable (P m d)] :
    ∑ v ∈ U, (if P (vp N v) (vm N v) then
        (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) else 0) ≤
      ∑ m ∈ Ioc 0 X, ∑ d ∈ N.divisors,
        (if P m d then (Nat.totient (N / d) : ℝ) / N else 0) := by
  have h1 : ∀ v ∈ U, (if P (vp N v) (vm N v) then
      (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) else 0) ≤
      (if P (vp N v) (vm N v) then (Nat.totient (N / vm N v) : ℝ) / N else 0) := by
    intro v hv
    split_ifs
    · exact term_bound N v hN (hU v hv)
    · exact le_rfl
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_product (s := Ioc 0 X) (t := N.divisors)
    (f := fun x : ℕ × ℕ => if P x.1 x.2 then (Nat.totient (N / x.2) : ℝ) / N else 0)]
  have himg : ∑ v ∈ U, (if P (vp N v) (vm N v) then (Nat.totient (N / vm N v) : ℝ) / N else 0) =
      ∑ x ∈ U.image (fun v => (vp N v, vm N v)),
        (if P x.1 x.2 then (Nat.totient (N / x.2) : ℝ) / N else 0) := by
    rw [Finset.sum_image]
    intro v1 _ v2 _ heq
    exact vp_vm_inj N hN v1 v2 (Prod.mk.inj heq).1 (Prod.mk.inj heq).2
  rw [himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
    rw [mem_product, mem_Ioc, Nat.mem_divisors]
    exact ⟨⟨vp_pos N v (hU v hv), hX v hv⟩, vm_dvd N v, hN.ne'⟩
  · intro x _ _
    split_ifs
    · positivity
    · exact le_rfl

-- The divisor sum of the totient, normalized.
lemma totient_div_sum (N : ℕ) (hN : 0 < N) :
    ∑ d ∈ N.divisors, (Nat.totient (N / d) : ℝ) / N = 1 := by
  rw [← Finset.sum_div, Nat.sum_div_divisors N (fun d => (Nat.totient d : ℝ))]
  have h1 := Nat.sum_totient N
  have h2 : ((N.divisors.sum Nat.totient : ℕ) : ℝ) = (N : ℝ) := by rw [h1]
  rw [Nat.cast_sum] at h2
  rw [h2]
  exact div_self (by exact_mod_cast hN.ne')

-- No condition: the sum is at most X.
lemma param_all (N : ℕ) (hN : 0 < N) (U : Finset ℕ) (hU : ∀ v ∈ U, 0 < v) (X : ℕ)
    (hX : ∀ v ∈ U, vp N v ≤ X) :
    ∑ v ∈ U, (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) ≤ X := by
  have h := param_sum N hN U hU X hX (fun _ _ => True)
  simp only [if_true] at h
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun m _ => totient_div_sum N hN)]
  simp

-- Condition on the lower part: gain from the divisor anatomy lemma.
lemma param_minus (N : ℕ) (hN : 0 < N) (U : Finset ℕ) (hU : ∀ v ∈ U, 0 < v) (X : ℕ)
    (hX : ∀ v ∈ U, vp N v ≤ X) (t c : ℝ) (ht : 1 ≤ t) :
    ∑ v ∈ U, (if c ≤ anat t (vm N v) then
        (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) else 0) ≤
      (X : ℝ) * (Real.exp (32 * Real.exp 16) * Real.exp (-(16 * c * t))) := by
  have h := param_sum N hN U hU X hX (fun _ d => c ≤ anat t d)
  refine h.trans ?_
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hin : ∀ m ∈ Ioc 0 X, ∑ d ∈ N.divisors,
      (if c ≤ anat t d then (Nat.totient (N / d) : ℝ) / N else 0) ≤
      Real.exp (32 * Real.exp 16) * Real.exp (-(16 * c * t)) := by
    intro m _
    rw [← Finset.sum_filter, ← Finset.sum_div, div_le_iff₀ hNR]
    refine (anat_div N hN t c ht).trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hin).trans (le_of_eq ?_)
  simp

-- Condition on the upper part: gain from the counting anatomy lemma.
lemma param_plus (N : ℕ) (hN : 0 < N) (U : Finset ℕ) (hU : ∀ v ∈ U, 0 < v) (X : ℕ)
    (hX : ∀ v ∈ U, vp N v ≤ X) (t c : ℝ) (ht : 1 ≤ t) :
    ∑ v ∈ U, (if c ≤ anat t (vp N v) then
        (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) else 0) ≤
      (X : ℝ) * (Real.exp (32 * Real.exp 16) * Real.exp (-(16 * c * t))) := by
  have h := param_sum N hN U hU X hX (fun m _ => c ≤ anat t m)
  refine h.trans ?_
  have hin : ∀ m ∈ Ioc 0 X, ∑ d ∈ N.divisors,
      (if c ≤ anat t m then (Nat.totient (N / d) : ℝ) / N else 0) =
      (if c ≤ anat t m then (1 : ℝ) else 0) := by
    intro m _
    split_ifs
    · exact totient_div_sum N hN
    · simp
  rw [Finset.sum_congr rfl hin, ← Finset.natCast_card_filter]
  refine (anat_count X t c ht).trans (le_of_eq ?_)
  ring


-- Summing over pairs by second coordinate, then over the first coordinates in the fibre.
lemma sum_by_snd (F : Finset (ℕ × ℕ)) (G : ℕ → ℕ → ℝ) :
    ∑ e ∈ F, G e.1 e.2 = ∑ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, G v w := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := F.image Prod.snd)
    (fun e he => Finset.mem_image_of_mem _ he)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    rw [(mem_filter.1 he).2]
  · intro e1 h1 e2 h2 heq
    rw [Finset.mem_coe, mem_filter] at h1 h2
    exact Prod.ext heq (h1.2.trans h2.2.symm)

-- Summing over pairs by first coordinate.
lemma sum_by_fst (F : Finset (ℕ × ℕ)) (G : ℕ × ℕ → ℝ) :
    ∑ e ∈ F, G e = ∑ v ∈ F.image Prod.fst, ∑ e ∈ F.filter (fun e => e.1 = v), G e := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := F.image Prod.fst)
    (fun e he => Finset.mem_image_of_mem _ he)]

-- A double sum with product structure, bounded through inner and outer estimates.
lemma double_bound (F : Finset (ℕ × ℕ)) (a b I J Xw : ℕ → ℝ) (X0 KI KJ : ℝ)
    (hb : ∀ w, 0 ≤ b w) (hJ : ∀ w, 0 ≤ J w) (hX0 : 0 < X0) (hKI : 0 ≤ KI)
    (hXw : ∀ w ∈ F.image Prod.snd, 0 < Xw w)
    (hin : ∀ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, I v * a v ≤ Xw w * KI)
    (hout : ∑ w ∈ F.image Prod.snd, J w * b w ≤ X0 * KJ) :
    ∑ e ∈ F, (I e.1 * J e.2) * ((a e.1 / X0) * (b e.2 / Xw e.2)) ≤ KI * KJ := by
  rw [sum_by_snd F (fun v w => (I v * J w) * ((a v / X0) * (b w / Xw w)))]
  have h1 : ∀ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst,
        (I v * J w) * ((a v / X0) * (b w / Xw w)) ≤ (KI / X0) * (J w * b w) := by
    intro w hw
    have hxw := hXw w hw
    have e : ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst,
        (I v * J w) * ((a v / X0) * (b w / Xw w)) =
        (J w * b w / (X0 * Xw w)) *
          ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, I v * a v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      field_simp
    rw [e]
    have h2 : 0 ≤ J w * b w / (X0 * Xw w) :=
      div_nonneg (mul_nonneg (hJ w) (hb w)) (mul_pos hX0 hxw).le
    calc (J w * b w / (X0 * Xw w)) *
          ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, I v * a v
        ≤ (J w * b w / (X0 * Xw w)) * (Xw w * KI) := mul_le_mul_of_nonneg_left (hin w hw) h2
      _ = (KI / X0) * (J w * b w) := by
          field_simp
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  calc (KI / X0) * ∑ w ∈ F.image Prod.snd, J w * b w
      ≤ (KI / X0) * (X0 * KJ) := mul_le_mul_of_nonneg_left hout (div_nonneg hKI hX0.le)
    _ = KI * KJ := by
        field_simp


-- Resolution of a structured system with the minimum degree property.
set_option maxHeartbeats 2000000 in
lemma resolution (ψ θ : ℕ → ℝ) (hψ : ∀ v, 0 ≤ ψ v) (hθ : ∀ w, 0 ≤ θ w) (t C : ℝ) (ht : 1 ≤ t)
    (N : ℕ) (hN : 0 < N) (F : Finset (ℕ × ℕ)) (hA : ∀ e ∈ F, Adm ψ θ t C e)
    (hs : ∀ e ∈ F, ∀ q : ℕ, q.Prime →
      Nat.dist (e.1.factorization q) (N.factorization q) +
        Nat.dist (e.2.factorization q) (N.factorization q) ≤ 1)
    (hd1 : ∀ v ∈ F.image Prod.fst, 3 / 4 * muE ψ θ F ≤
      mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) * mu ψ (F.image Prod.fst))
    (hd2 : ∀ w ∈ F.image Prod.snd, 3 / 4 * muE ψ θ F ≤
      mu ψ ((F.filter (fun e => e.2 = w)).image Prod.fst) * mu θ (F.image Prod.snd)) :
    9 / 16 * muE ψ θ F ^ 2 ≤ (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) *
      (4 * (Real.exp (32 * Real.exp 16) * Real.exp (-(4 * max C 0 * t)))) := by
  have hA0 := muE_nonneg ψ θ hψ hθ F
  have ha0 := mu_nonneg ψ hψ (F.image Prod.fst)
  have hb0 := mu_nonneg θ hθ (F.image Prod.snd)
  rcases F.eq_empty_or_nonempty with hF | hF
  · have hz : muE ψ θ F = 0 := by
      rw [hF]
      unfold muE
      simp
    rw [hz]
    have : (0 : ℝ) ≤ (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) *
        (4 * (Real.exp (32 * Real.exp 16) * Real.exp (-(4 * max C 0 * t)))) := by positivity
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max C 0 / 4 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    have := le_max_right C 0
    positivity
  obtain ⟨Kae, hKae⟩ : ∃ K : ℝ, K = Real.exp (32 * Real.exp 16) * Real.exp (-(16 * c * t)) :=
    ⟨_, rfl⟩
  have hKae0 : 0 ≤ Kae := by
    rw [hKae]
    positivity
  have hKae_eq : Real.exp (32 * Real.exp 16) * Real.exp (-(4 * max C 0 * t)) = Kae := by
    rw [hKae, hc]
    congr 2
    ring
  rw [hKae_eq]
  have hpos1 : ∀ e ∈ F, 0 < e.1 := fun e he => (hA e he).1
  have hpos2 : ∀ e ∈ F, 0 < e.2 := fun e he => (hA e he).2.1
  have hWne : (F.image Prod.snd).Nonempty := hF.image _
  obtain ⟨w0, hw0, hw0X⟩ := Finset.exists_mem_eq_sup (F.image Prod.snd) hWne (vp N)
  obtain ⟨X0n, hX0n⟩ : ∃ X0 : ℕ, X0 = (F.image Prod.snd).sup (vp N) := ⟨_, rfl⟩
  obtain ⟨Xw, hXwdef⟩ : ∃ Xw : ℕ → ℕ, ∀ w, Xw w =
      ((F.filter (fun e => e.2 = w)).image Prod.fst).sup (vp N) := ⟨_, fun _ => rfl⟩
  have hXw_le : ∀ w, ∀ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, vp N v ≤ Xw w := by
    intro w v hv
    rw [hXwdef]
    exact Finset.le_sup (f := vp N) hv
  have hXw_pos : ∀ w ∈ F.image Prod.snd, 0 < Xw w := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_image.1 hw
    have hmem : e.1 ∈ (F.filter (fun x => x.2 = e.2)).image Prod.fst :=
      mem_image.2 ⟨e, mem_filter.2 ⟨he, rfl⟩, rfl⟩
    exact lt_of_lt_of_le (vp_pos N e.1 (hpos1 e he)) (hXw_le _ _ hmem)
  have hXw_att : ∀ e ∈ F, ∃ v0, (v0, e.2) ∈ F ∧ vp N v0 = Xw e.2 := by
    intro e he
    have hne : ((F.filter (fun x => x.2 = e.2)).image Prod.fst).Nonempty :=
      ⟨e.1, mem_image.2 ⟨e, mem_filter.2 ⟨he, rfl⟩, rfl⟩⟩
    obtain ⟨v0, hv0, hv0X⟩ := Finset.exists_mem_eq_sup _ hne (vp N)
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hv0
    rw [mem_filter] at hx
    refine ⟨x.1, ?_, ?_⟩
    · have e1 : (x.1, e.2) = x := Prod.ext rfl hx.2.symm
      rw [e1]
      exact hx.1
    · rw [hXwdef]
      exact hv0X.symm
  have hX0_le : ∀ w ∈ F.image Prod.snd, vp N w ≤ X0n := by
    intro w hw
    rw [hX0n]
    exact Finset.le_sup (f := vp N) hw
  have hw0eq : vp N w0 = X0n := by
    rw [hX0n]
    exact hw0X.symm
  have hw0pos : 0 < w0 := by
    obtain ⟨e, he, rfl⟩ := mem_image.1 hw0
    exact hpos2 e he
  have hX0pos : 0 < X0n := by
    rw [← hw0eq]
    exact vp_pos N w0 hw0pos
  have hX0R : (0 : ℝ) < X0n := by exact_mod_cast hX0pos
  obtain ⟨a, had⟩ : ∃ a : ℕ → ℝ, ∀ v, a v =
      (Nat.totient v : ℝ) / ((v : ℝ) * (vm N v : ℝ)) := ⟨_, fun _ => rfl⟩
  have ha_nn : ∀ v, 0 ≤ a v := fun v => by
    rw [had]
    positivity
  -- the weight bound for one coordinate
  have hwt : ∀ (φf : ℕ → ℝ) (x : ℕ) (Xn : ℕ), 0 < x → 0 < Xn → 0 ≤ φf x →
      φf x * ((vm N x : ℝ) * (Xn : ℝ)) ≤ 1 → wt φf x ≤ a x / Xn := by
    intro φf x Xn hx hXn hφ0 hbd
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hvmR : (0 : ℝ) < vm N x := by exact_mod_cast vm_pos N x hN
    have hXnR : (0 : ℝ) < Xn := by exact_mod_cast hXn
    unfold wt
    rw [had, div_div, div_le_div_iff₀ hxR (by positivity)]
    have e : (Nat.totient x : ℝ) * φf x * ((x : ℝ) * (vm N x : ℝ) * (Xn : ℝ)) =
        (Nat.totient x : ℝ) * (x : ℝ) * (φf x * ((vm N x : ℝ) * (Xn : ℝ))) := by ring
    rw [e]
    calc (Nat.totient x : ℝ) * (x : ℝ) * (φf x * ((vm N x : ℝ) * (Xn : ℝ)))
        ≤ (Nat.totient x : ℝ) * (x : ℝ) * 1 := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = (Nat.totient x : ℝ) * (x : ℝ) := mul_one _
  have hterm : ∀ e ∈ F, (e.1, w0) ∈ F →
      wt ψ e.1 * wt θ e.2 ≤ (a e.1 / X0n) * (a e.2 / Xw e.2) := by
    intro e he hew0
    have hv := hpos1 e he
    have hw := hpos2 e he
    have hAd := hA _ hew0
    have h1 := psi_bound ψ e.1 w0 N hv hw0pos hN (hs _ hew0) hAd.2.2.1
    rw [hw0eq] at h1
    obtain ⟨v0, hv0F, hv0X⟩ := hXw_att e he
    have hAd2 := hA _ hv0F
    have hv0pos : 0 < v0 := hAd2.1
    have hs2 := hs _ hv0F
    have h2 := psi_bound θ e.2 v0 N hw hv0pos hN (fun q hq => by
      have h3 := hs2 q hq
      simp only at h3
      omega) (by
      rw [Nat.gcd_comm]
      exact hAd2.2.2.2.1)
    rw [hv0X] at h2
    have hXwp : 0 < Xw e.2 := hXw_pos e.2 (mem_image.2 ⟨e, he, rfl⟩)
    have b1 := hwt ψ e.1 X0n hv hX0pos (hψ _) h1
    have b2 := hwt θ e.2 (Xw e.2) hw hXwp (hθ _) h2
    exact mul_le_mul b1 b2 (wt_nonneg θ hθ _) (div_nonneg (ha_nn _) (Nat.cast_nonneg _))
  -- Step A
  obtain ⟨Sig0, hSig0⟩ : ∃ S : ℝ, S = ∑ v ∈ (F.filter (fun e => e.2 = w0)).image Prod.fst,
      wt ψ v * mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) := ⟨_, rfl⟩
  have hsubG : (F.filter (fun e => e.2 = w0)).image Prod.fst ⊆ F.image Prod.fst :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hStepA : 9 / 16 * muE ψ θ F ^ 2 ≤
      mu θ (F.image Prod.snd) * (mu ψ (F.image Prod.fst) * Sig0) := by
    have hA1 := hd2 w0 hw0
    have hA2 : 3 / 4 * muE ψ θ F * mu ψ ((F.filter (fun e => e.2 = w0)).image Prod.fst) ≤
        mu ψ (F.image Prod.fst) * Sig0 := by
      rw [hSig0, Finset.mul_sum]
      unfold mu
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      have h3 := hd1 v (hsubG hv)
      have h4 := mul_le_mul_of_nonneg_left h3 (wt_nonneg ψ hψ v)
      unfold mu at h4
      linarith
    have h5 : 3 / 4 * muE ψ θ F * (3 / 4 * muE ψ θ F) ≤ 3 / 4 * muE ψ θ F *
        (mu ψ ((F.filter (fun e => e.2 = w0)).image Prod.fst) * mu θ (F.image Prod.snd)) :=
      mul_le_mul_of_nonneg_left hA1 (by positivity)
    have h6 := mul_le_mul_of_nonneg_left hA2 hb0
    nlinarith
  -- Step B
  have hStepB : Sig0 ≤ ∑ e ∈ F, (a e.1 / X0n) * (a e.2 / Xw e.2) := by
    have hT0 : ∀ e : ℕ × ℕ, (0 : ℝ) ≤ (a e.1 / X0n) * (a e.2 / Xw e.2) := fun e =>
      mul_nonneg (div_nonneg (ha_nn _) (Nat.cast_nonneg _))
        (div_nonneg (ha_nn _) (Nat.cast_nonneg _))
    rw [hSig0, sum_by_fst F (fun e => (a e.1 / X0n) * (a e.2 / Xw e.2))]
    have h1 : ∀ v ∈ (F.filter (fun e => e.2 = w0)).image Prod.fst,
        wt ψ v * mu θ ((F.filter (fun e => e.1 = v)).image Prod.snd) ≤
        ∑ e ∈ F.filter (fun e => e.1 = v), (a e.1 / X0n) * (a e.2 / Xw e.2) := by
      intro v hv
      rw [← muE_fiber_fst]
      unfold muE
      apply Finset.sum_le_sum
      intro e he
      rw [mem_filter] at he
      apply hterm e he.1
      obtain ⟨x, hx, hxv⟩ := mem_image.1 hv
      rw [mem_filter] at hx
      have e1 : (e.1, w0) = x := Prod.ext (he.2.trans hxv.symm) hx.2.symm
      rw [e1]
      exact hx.1
    refine (Finset.sum_le_sum h1).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubG
      (fun v _ _ => Finset.sum_nonneg (fun e _ => hT0 e))
  -- Step C
  obtain ⟨I1, hI1⟩ : ∃ I : ℕ → ℝ, ∀ v, I v = if c ≤ anat t (vp N v) then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I : ℕ → ℝ, ∀ v, I v = if c ≤ anat t (vm N v) then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have hI1nn : ∀ v, 0 ≤ I1 v := fun v => by
    rw [hI1]
    split_ifs <;> norm_num
  have hI2nn : ∀ v, 0 ≤ I2 v := fun v => by
    rw [hI2]
    split_ifs <;> norm_num
  have hind : ∀ e ∈ F, 1 ≤ I1 e.1 + I2 e.1 + I1 e.2 + I2 e.2 := by
    intro e he
    have hsplit := anat_split e.1 e.2 N (hpos1 e he) (hpos2 e he) hN (hs e he) t
    have hC := (hA e he).2.2.2.2
    have hsum0 : 0 ≤ anat t (vp N e.1) + anat t (vm N e.1) + anat t (vp N e.2) +
        anat t (vm N e.2) := by
      have := anat_nonneg t (vp N e.1)
      have := anat_nonneg t (vm N e.1)
      have := anat_nonneg t (vp N e.2)
      have := anat_nonneg t (vm N e.2)
      linarith
    have h4c : 4 * c ≤ anat t (vp N e.1) + anat t (vm N e.1) + anat t (vp N e.2) +
        anat t (vm N e.2) := by
      rw [hc]
      have : max C 0 ≤ anat t (vp N e.1) + anat t (vm N e.1) + anat t (vp N e.2) +
          anat t (vm N e.2) := max_le (hC.trans hsplit) hsum0
      linarith
    have n1 := hI1nn e.1
    have n2 := hI2nn e.1
    have n3 := hI1nn e.2
    have n4 := hI2nn e.2
    by_cases c1 : c ≤ anat t (vp N e.1)
    · have : I1 e.1 = 1 := by rw [hI1, if_pos c1]
      linarith
    · by_cases c2 : c ≤ anat t (vm N e.1)
      · have : I2 e.1 = 1 := by rw [hI2, if_pos c2]
        linarith
      · by_cases c3 : c ≤ anat t (vp N e.2)
        · have : I1 e.2 = 1 := by rw [hI1, if_pos c3]
          linarith
        · by_cases c4 : c ≤ anat t (vm N e.2)
          · have : I2 e.2 = 1 := by rw [hI2, if_pos c4]
            linarith
          · exfalso
            have := not_le.1 c1
            have := not_le.1 c2
            have := not_le.1 c3
            have := not_le.1 c4
            linarith
  -- inner and outer estimates
  have hGpos : ∀ w ∈ F.image Prod.snd, ∀ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst,
      0 < v := by
    intro w _ v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
    exact hpos1 x (mem_filter.1 hx).1
  have hWpos : ∀ w ∈ F.image Prod.snd, 0 < w := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
    exact hpos2 x hx
  have hXwR : ∀ w ∈ F.image Prod.snd, (0 : ℝ) < ((Xw w : ℕ) : ℝ) := by
    intro w hw
    exact_mod_cast hXw_pos w hw
  have in_all : ∀ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, (1 : ℝ) * a v ≤
        ((Xw w : ℕ) : ℝ) * 1 := by
    intro w hw
    have h := param_all N hN _ (hGpos w hw) (Xw w) (hXw_le w)
    simp only [one_mul, mul_one, had]
    exact h
  have in_plus : ∀ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, I1 v * a v ≤
        ((Xw w : ℕ) : ℝ) * Kae := by
    intro w hw
    have h := param_plus N hN _ (hGpos w hw) (Xw w) (hXw_le w) t c ht
    rw [← hKae] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro v _
    rw [hI1, had]
    split_ifs <;> simp
  have in_minus : ∀ w ∈ F.image Prod.snd,
      ∑ v ∈ (F.filter (fun e => e.2 = w)).image Prod.fst, I2 v * a v ≤
        ((Xw w : ℕ) : ℝ) * Kae := by
    intro w hw
    have h := param_minus N hN _ (hGpos w hw) (Xw w) (hXw_le w) t c ht
    rw [← hKae] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro v _
    rw [hI2, had]
    split_ifs <;> simp
  have out_all : ∑ w ∈ F.image Prod.snd, (1 : ℝ) * a w ≤ (X0n : ℝ) * 1 := by
    have h := param_all N hN _ hWpos X0n hX0_le
    simp only [one_mul, mul_one, had]
    exact h
  have out_plus : ∑ w ∈ F.image Prod.snd, I1 w * a w ≤ (X0n : ℝ) * Kae := by
    have h := param_plus N hN _ hWpos X0n hX0_le t c ht
    rw [← hKae] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro v _
    rw [hI1, had]
    split_ifs <;> simp
  have out_minus : ∑ w ∈ F.image Prod.snd, I2 w * a w ≤ (X0n : ℝ) * Kae := by
    have h := param_minus N hN _ hWpos X0n hX0_le t c ht
    rw [← hKae] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro v _
    rw [hI2, had]
    split_ifs <;> simp
  have one_nn : ∀ w : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) w := fun _ => zero_le_one
  have db1 := double_bound F a a I1 (fun _ => (1 : ℝ)) (fun w => ((Xw w : ℕ) : ℝ)) (X0n : ℝ) Kae 1
    ha_nn one_nn hX0R hKae0 hXwR in_plus out_all
  have db2 := double_bound F a a I2 (fun _ => (1 : ℝ)) (fun w => ((Xw w : ℕ) : ℝ)) (X0n : ℝ) Kae 1
    ha_nn one_nn hX0R hKae0 hXwR in_minus out_all
  have db3 := double_bound F a a (fun _ => (1 : ℝ)) I1 (fun w => ((Xw w : ℕ) : ℝ)) (X0n : ℝ) 1 Kae
    ha_nn hI1nn hX0R zero_le_one hXwR in_all out_plus
  have db4 := double_bound F a a (fun _ => (1 : ℝ)) I2 (fun w => ((Xw w : ℕ) : ℝ)) (X0n : ℝ) 1 Kae
    ha_nn hI2nn hX0R zero_le_one hXwR in_all out_minus
  have hStepC : ∑ e ∈ F, (a e.1 / X0n) * (a e.2 / Xw e.2) ≤ 4 * Kae := by
    have hpt : ∀ e ∈ F, (a e.1 / X0n) * (a e.2 / Xw e.2) ≤
        (I1 e.1 * 1) * ((a e.1 / X0n) * (a e.2 / Xw e.2)) +
        (I2 e.1 * 1) * ((a e.1 / X0n) * (a e.2 / Xw e.2)) +
        (1 * I1 e.2) * ((a e.1 / X0n) * (a e.2 / Xw e.2)) +
        (1 * I2 e.2) * ((a e.1 / X0n) * (a e.2 / Xw e.2)) := by
      intro e he
      have hT0 : (0 : ℝ) ≤ (a e.1 / X0n) * (a e.2 / Xw e.2) :=
        mul_nonneg (div_nonneg (ha_nn _) (Nat.cast_nonneg _))
          (div_nonneg (ha_nn _) (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_right (hind e he) hT0
      linarith
    refine (Finset.sum_le_sum hpt).trans ?_
    simp only [Finset.sum_add_distrib]
    linarith
  calc 9 / 16 * muE ψ θ F ^ 2 ≤ mu θ (F.image Prod.snd) * (mu ψ (F.image Prod.fst) * Sig0) :=
        hStepA
    _ ≤ mu θ (F.image Prod.snd) * (mu ψ (F.image Prod.fst) * (4 * Kae)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hStepB.trans hStepC) ha0) hb0
    _ = _ := by ring


-- The Rankin constant is at most 3^B once B is at least 32 * 3^16.
lemma Ka_bound (B : ℕ) (hB : 32 * 3 ^ 16 ≤ B) : Real.exp (32 * Real.exp 16) ≤ (3 : ℝ) ^ B := by
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h16 : Real.exp 16 ≤ 3 ^ 16 := by
    have e : Real.exp 16 = Real.exp 1 ^ 16 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he 16
  have h1 : 32 * Real.exp 16 ≤ (B : ℝ) := by
    have h2 : ((32 * 3 ^ 16 : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    push_cast at h2
    linarith
  calc Real.exp (32 * Real.exp 16) ≤ Real.exp (B : ℝ) := Real.exp_le_exp.2 h1
    _ = Real.exp 1 ^ B := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 3 ^ B := pow_le_pow_left₀ (Real.exp_pos 1).le he B

-- The final arithmetic contradiction.
lemma final_arith (K Ex E4 A X Ka : ℝ) (hK : 1024 / 9 * Ka ≤ K) (hKa : 0 < Ka) (hEx : 0 < Ex)
    (hE4 : 0 < E4) (hE : E4 ≤ Ex) (hA0 : 0 ≤ A) (hX0 : 0 ≤ X) (htriv : A ≤ X)
    (hQ : K * Ex / 16 * X ^ 3 < A ^ 4) (hres : 9 / 16 * A ^ 2 ≤ X * (4 * (Ka * E4))) : False := by
  have hKpos : 0 < K := by
    have : 0 < 1024 / 9 * Ka := by positivity
    linarith
  obtain ⟨Z0, hZ0⟩ : ∃ Z0 : ℝ, Z0 = K * Ex / 16 := ⟨_, rfl⟩
  rw [← hZ0] at hQ
  have hZ0pos : 0 < Z0 := by
    rw [hZ0]
    positivity
  have hApos : 0 < A := by
    rcases hA0.eq_or_lt with h | h
    · rw [← h] at hQ
      have : 0 ≤ Z0 * X ^ 3 := mul_nonneg hZ0pos.le (pow_nonneg hX0 3)
      norm_num at hQ
      linarith
    · exact h
  have hXpos : 0 < X := lt_of_lt_of_le hApos htriv
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 64 / 9 * Ka * E4 := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    positivity
  have hA2 : A ^ 2 ≤ G * X := by
    rw [hG]
    linarith
  have h1 : Z0 < X := by
    have hA4 : A ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ hA0 htriv 4
    have h : Z0 * X ^ 3 < X * X ^ 3 := by
      have e : X * X ^ 3 = X ^ 4 := by ring
      rw [e]
      linarith
    exact lt_of_mul_lt_mul_right h (pow_nonneg hX0 3)
  have h2 : Z0 * X < G ^ 2 := by
    have hA4 : A ^ 4 ≤ (G * X) ^ 2 := by
      have e : A ^ 4 = (A ^ 2) ^ 2 := by ring
      rw [e]
      exact pow_le_pow_left₀ (sq_nonneg A) hA2 2
    have h : (Z0 * X) * X ^ 2 < G ^ 2 * X ^ 2 := by
      have e1 : (Z0 * X) * X ^ 2 = Z0 * X ^ 3 := by ring
      have e2 : G ^ 2 * X ^ 2 = (G * X) ^ 2 := by ring
      rw [e1, e2]
      linarith
    exact lt_of_mul_lt_mul_right h (sq_nonneg X)
  have h3 : Z0 * Z0 < G * G := by
    have h4 : Z0 * Z0 < Z0 * X := mul_lt_mul_of_pos_left h1 hZ0pos
    have e : G * G = G ^ 2 := by ring
    rw [e]
    linarith
  have h4 : Z0 < G := by
    by_contra hcon
    have hle : G ≤ Z0 := not_lt.1 hcon
    have := mul_le_mul hle hle hGpos.le hZ0pos.le
    linarith
  -- K * Ex / 16 < 64/9 * Ka * E4 ≤ 64/9 * Ka * Ex
  rw [hZ0, hG] at h4
  have h5 : 64 / 9 * Ka * E4 ≤ 64 / 9 * Ka * Ex :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have h6 : K * Ex < 1024 / 9 * Ka * Ex := by linarith
  have h7 : K < 1024 / 9 * Ka := lt_of_mul_lt_mul_right h6 hEx.le
  linarith

-- The main claim for all n, once p0 is a large fourth power.
theorem claim_all (p0 k0 : ℕ) (hk0 : 8 * (18 * 144 ^ 3 + 1296 * 144 ^ 5) ≤ k0)
    (hp0 : p0 = k0 ^ 4) : ∀ n, Claim p0 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V W ψ θ t C E hψ hθ ht hV hW hE hA hcard
    by_contra hcon
    have hfail := not_le.1 hcon
    obtain ⟨N, hN, Es, hEs, hmass, hstr⟩ := structure_star p0 k0 n hk0 hp0 IH V W ψ θ t C E hψ hθ
      ht hV hW hE hA hcard hfail
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K =
        ((10 : ℝ) ^ 12) ^ (p0 + ((PP V W).filter (fun q => q ≤ p0)).card) := ⟨_, rfl⟩
    rw [← hK] at hfail
    have hKpos : 0 < K := by
      rw [hK]
      positivity
    obtain ⟨Ex, hEx⟩ : ∃ Ex : ℝ, Ex = Real.exp (-(3 * C * t)) := ⟨_, rfl⟩
    rw [← hEx] at hfail
    have hExpos : 0 < Ex := by
      rw [hEx]
      exact Real.exp_pos _
    obtain ⟨hT, ha, hb⟩ := fail_pos K hKpos V W ψ θ Ex hExpos E hψ hθ hE hfail
    -- the half-mass subsystem is a near counterexample
    have hsubV : Es.image Prod.fst ⊆ V := by
      intro v hv
      obtain ⟨e, he, rfl⟩ := mem_image.1 hv
      exact (mem_product.1 (hE (hEs he))).1
    have hsubW : Es.image Prod.snd ⊆ W := by
      intro w hw
      obtain ⟨e, he, rfl⟩ := mem_image.1 hw
      exact (mem_product.1 (hE (hEs he))).2
    have hQ : K * Ex / 16 * (mu ψ (Es.image Prod.fst) * mu θ (Es.image Prod.snd)) ^ 3 <
        muE ψ θ Es ^ 4 := by
      have h1 : mu ψ (Es.image Prod.fst) * mu θ (Es.image Prod.snd) ≤ mu ψ V * mu θ W :=
        mul_le_mul (mu_mono ψ hψ hsubV) (mu_mono θ hθ hsubW) (mu_nonneg θ hθ _) ha.le
      have h2 : (mu ψ (Es.image Prod.fst) * mu θ (Es.image Prod.snd)) ^ 3 ≤
          (mu ψ V * mu θ W) ^ 3 :=
        pow_le_pow_left₀ (mul_nonneg (mu_nonneg ψ hψ _) (mu_nonneg θ hθ _)) h1 3
      have h3 : muE ψ θ E ^ 4 ≤ (2 * muE ψ θ Es) ^ 4 := pow_le_pow_left₀ hT.le hmass 4
      have h4 : (2 * muE ψ θ Es) ^ 4 = 16 * muE ψ θ Es ^ 4 := by ring
      have h5 : K * Ex / 16 * (mu ψ (Es.image Prod.fst) * mu θ (Es.image Prod.snd)) ^ 3 ≤
          K * Ex / 16 * (mu ψ V * mu θ W) ^ 3 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h6 : K * Ex / 16 * (mu ψ V * mu θ W) ^ 3 = (K * (mu ψ V * mu θ W) ^ 3 * Ex) / 16 := by
        ring
      linarith
    obtain ⟨F, hFs, hQF, hd1, hd2⟩ := min_degree ψ θ hψ hθ (K * Ex / 16) (by positivity) Es hQ
    have hres := resolution ψ θ hψ hθ t C ht N hN F (fun e he => hA e (hEs (hFs he)))
      (fun e he => hstr e (hFs he)) hd1 hd2
    have htriv := muE_le_mul ψ θ hψ hθ (F.image Prod.fst) (F.image Prod.snd) F (by
      intro e he
      rw [mem_product]
      exact ⟨mem_image.2 ⟨e, he, rfl⟩, mem_image.2 ⟨e, he, rfl⟩⟩)
    -- the size of K
    have hk0p0 : k0 ≤ p0 := by
      rw [hp0]
      have h1 : 1 ≤ k0 := by
        refine le_trans ?_ hk0
        norm_num
      calc k0 = k0 ^ 1 := (pow_one k0).symm
        _ ≤ k0 ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
    have hB : 32 * 3 ^ 16 ≤ p0 := by
      refine le_trans ?_ hk0p0
      refine le_trans ?_ hk0
      norm_num
    have hKa := Ka_bound p0 hB
    have hKbig : 1024 / 9 * Real.exp (32 * Real.exp 16) ≤ K := by
      have h1 : ((10 : ℝ) ^ 12) ^ p0 ≤ K := by
        rw [hK]
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
      have h2 : (1024 : ℝ) * 3 ^ p0 ≤ ((10 : ℝ) ^ 12) ^ p0 := by
        have h3 : (1024 : ℝ) ≤ 1024 ^ p0 := by
          have hp1 : 1 ≤ p0 := by
            refine le_trans ?_ hB
            norm_num
          calc (1024 : ℝ) = 1024 ^ 1 := (pow_one _).symm
            _ ≤ 1024 ^ p0 := pow_le_pow_right₀ (by norm_num) hp1
        have h4 : (1024 : ℝ) ^ p0 * 3 ^ p0 = (1024 * 3) ^ p0 := (mul_pow _ _ _).symm
        have h5 : ((1024 : ℝ) * 3) ^ p0 ≤ ((10 : ℝ) ^ 12) ^ p0 :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) p0
        have h6 : (0 : ℝ) ≤ 3 ^ p0 := by positivity
        calc (1024 : ℝ) * 3 ^ p0 ≤ 1024 ^ p0 * 3 ^ p0 := mul_le_mul_of_nonneg_right h3 h6
          _ = (1024 * 3) ^ p0 := h4
          _ ≤ ((10 : ℝ) ^ 12) ^ p0 := h5
      have h7 : 1024 / 9 * Real.exp (32 * Real.exp 16) ≤ 1024 * 3 ^ p0 := by
        have h8 : (0 : ℝ) ≤ Real.exp (32 * Real.exp 16) := (Real.exp_pos _).le
        nlinarith
      linarith
    have hE4 : Real.exp (-(4 * max C 0 * t)) ≤ Ex := by
      rw [hEx]
      apply Real.exp_le_exp.2
      have h1 : C ≤ max C 0 := le_max_left _ _
      have h2 : 0 ≤ max C 0 := le_max_right _ _
      have ht0 : 0 ≤ t := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 ht0, mul_nonneg h2 ht0]
    exact final_arith K Ex (Real.exp (-(4 * max C 0 * t))) (muE ψ θ F)
      (mu ψ (F.image Prod.fst) * mu θ (F.image Prod.snd)) (Real.exp (32 * Real.exp 16)) hKbig
      (Real.exp_pos _) hExpos (Real.exp_pos _) hE4 (muE_nonneg ψ θ hψ hθ F)
      (mul_nonneg (mu_nonneg ψ hψ _) (mu_nonneg θ hθ _)) htriv hQF hres


-- The arithmetic behind the deduction of the proposition from the main claim.
lemma prop_arith (A m t P Q ex Kc : ℝ) (_hA : 0 ≤ A) (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (ht : 1 ≤ t)
    (hex : 0 < ex) (hte : t ^ 6 * ex ≤ 1) (hKc0 : 0 ≤ Kc) (hKP : Kc ≤ P) (hPQ : P ≤ Q ^ 4)
    (hQ : 0 ≤ Q) (h : (A / t ^ 2) ^ 4 ≤ Kc * ((m / t) * (m / t)) ^ 3 * ex) :
    A ≤ 3 * Q / t := by
  have ht0 : 0 < t := by linarith
  apply le_of_pow4_le (by positivity)
  have h1 : A ^ 4 = (A / t ^ 2) ^ 4 * t ^ 8 := by
    field_simp
  have h2 : Kc * ((m / t) * (m / t)) ^ 3 * ex * t ^ 8 = Kc * m ^ 6 * (t ^ 2 * ex) := by
    field_simp
  have h3 : A ^ 4 ≤ Kc * m ^ 6 * (t ^ 2 * ex) := by
    rw [h1, ← h2]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hm6 : m ^ 6 ≤ 64 := by
    have := pow_le_pow_left₀ hm0 hm2 6
    norm_num at this
    exact this
  have hP0 : 0 ≤ P := le_trans hKc0 hKP
  have h4 : Kc * m ^ 6 * (t ^ 2 * ex) ≤ P * 64 * (t ^ 2 * ex) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hKP hm6 (by positivity) hP0
  have h5 : (3 * Q / t) ^ 4 = 81 * Q ^ 4 / t ^ 4 := by
    field_simp
    ring
  rw [h5, le_div_iff₀ (by positivity)]
  have h6 : A ^ 4 * t ^ 4 ≤ P * 64 * (t ^ 2 * ex) * t ^ 4 :=
    mul_le_mul_of_nonneg_right (h3.trans h4) (by positivity)
  have h7 : P * 64 * (t ^ 2 * ex) * t ^ 4 = 64 * P * (t ^ 6 * ex) := by ring
  have h8 : 64 * P * (t ^ 6 * ex) ≤ 64 * P * 1 := mul_le_mul_of_nonneg_left hte (by positivity)
  have hQ4 : 0 ≤ Q ^ 4 := by positivity
  linarith

-- Proposition 5.4 of Koukoulopoulos and Maynard.
theorem prop54 : ∃ C : ℝ, ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1 / 2) →
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) →
      1 ≤ ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q →
      ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q ≤ 2 →
      ∀ t : ℝ, 1 ≤ t →
        ∑ v ∈ S, ∑ w ∈ S,
          (if max ((w : ℝ) * ψ v) ((v : ℝ) * ψ w) / (Nat.gcd v w : ℝ) ≤ t ∧
              10 ≤ ∑ p ∈ (v * w / (Nat.gcd v w) ^ 2).primeFactors.filter
                (fun p : ℕ => t ≤ p), 1 / (p : ℝ)
            then ((Nat.totient v : ℝ) * ψ v / v) * ((Nat.totient w : ℝ) * ψ w / w)
            else 0) ≤ C / t := by
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, k0 = 8 * (18 * 144 ^ 3 + 1296 * 144 ^ 5) := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℕ, p0 = k0 ^ 4 := ⟨_, rfl⟩
  have hclaim := claim_all p0 k0 (le_of_eq hk0.symm) hp0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (10 : ℝ) ^ 12 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hM]
    norm_num
  refine ⟨3 * M ^ (p0 + 1), ?_⟩
  intro ψ hψ S hS _ hS2 t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (ℕ × ℕ), E = (S ×ˢ S).filter (fun e : ℕ × ℕ =>
      max ((e.2 : ℝ) * ψ e.1) ((e.1 : ℝ) * ψ e.2) / (Nat.gcd e.1 e.2 : ℝ) ≤ t ∧
        10 ≤ ∑ p ∈ (e.1 * e.2 / (Nat.gcd e.1 e.2) ^ 2).primeFactors.filter
          (fun p : ℕ => t ≤ p), 1 / (p : ℝ)) := ⟨_, rfl⟩
  have hsum : ∑ v ∈ S, ∑ w ∈ S,
      (if max ((w : ℝ) * ψ v) ((v : ℝ) * ψ w) / (Nat.gcd v w : ℝ) ≤ t ∧
          10 ≤ ∑ p ∈ (v * w / (Nat.gcd v w) ^ 2).primeFactors.filter
            (fun p : ℕ => t ≤ p), 1 / (p : ℝ)
        then ((Nat.totient v : ℝ) * ψ v / v) * ((Nat.totient w : ℝ) * ψ w / w)
        else 0) = muE ψ ψ E := by
    rw [hEdef]
    unfold muE wt
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hsum]
  have hψ0 : ∀ v, 0 ≤ ψ v := fun v => (hψ v).1
  have hψt0 : ∀ v, 0 ≤ ψ v / t := fun v => div_nonneg (hψ0 v) ht0.le
  have hAdm : ∀ e ∈ E, Adm (fun v => ψ v / t) (fun v => ψ v / t) t 10 e := by
    intro e he
    rw [hEdef, mem_filter, mem_product] at he
    obtain ⟨⟨h1, h2⟩, hD, hL⟩ := he
    have hg : (0 : ℝ) < (Nat.gcd e.1 e.2 : ℝ) := by
      exact_mod_cast Nat.gcd_pos_of_pos_left _ (hS _ h1)
    rw [div_le_iff₀ hg] at hD
    have hl := le_max_left ((e.2 : ℝ) * ψ e.1) ((e.1 : ℝ) * ψ e.2)
    have hr := le_max_right ((e.2 : ℝ) * ψ e.1) ((e.1 : ℝ) * ψ e.2)
    refine ⟨hS _ h1, hS _ h2, ?_, ?_, ?_⟩
    · simp only
      rw [mul_div_assoc', div_le_iff₀ ht0]
      linarith [mul_comm t (Nat.gcd e.1 e.2 : ℝ)]
    · simp only
      rw [mul_div_assoc', div_le_iff₀ ht0]
      linarith [mul_comm t (Nat.gcd e.1 e.2 : ℝ)]
    · unfold Lp anat
      exact hL
  have hE : E ⊆ S ×ˢ S := by
    rw [hEdef]
    exact Finset.filter_subset _ _
  have hcl := hclaim (PP S S).card S S (fun v => ψ v / t) (fun v => ψ v / t) t 10 E hψt0 hψt0 ht
    hS hS hE hAdm le_rfl
  have hwt : ∀ v, wt (fun v => ψ v / t) v = wt ψ v / t := by
    intro v
    unfold wt
    field_simp
  have hmu : mu (fun v => ψ v / t) S = mu ψ S / t := by
    unfold mu
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun v _ => hwt v)
  have hmuE : muE (fun v => ψ v / t) (fun v => ψ v / t) E = muE ψ ψ E / t ^ 2 := by
    unfold muE
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    rw [hwt, hwt]
    field_simp
  rw [hmu, hmuE, ← hM] at hcl
  have hm2 : mu ψ S ≤ 2 := by
    unfold mu wt
    exact hS2
  have hm0 := mu_nonneg ψ hψ0 S
  have hA0 := muE_nonneg ψ ψ hψ0 hψ0 E
  have hcard : ((PP S S).filter (fun q => q ≤ p0)).card ≤ p0 + 1 := by
    calc ((PP S S).filter (fun q => q ≤ p0)).card ≤ (range (p0 + 1)).card :=
          Finset.card_le_card (fun q hq => by
            rw [mem_filter] at hq
            exact mem_range.2 (Nat.lt_succ_of_le hq.2))
      _ = p0 + 1 := Finset.card_range _
  have hKP : M ^ (p0 + ((PP S S).filter (fun q => q ≤ p0)).card) ≤ M ^ (2 * p0 + 1) :=
    pow_le_pow_right₀ hM1 (by omega)
  have hPQ : M ^ (2 * p0 + 1) ≤ (M ^ (p0 + 1)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hM1 (by omega)
  have hte : t ^ 6 * Real.exp (-(3 * 10 * t)) ≤ 1 := by
    have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h2 : t ^ 6 ≤ Real.exp t ^ 6 := pow_le_pow_left₀ ht0.le h1 6
    have h3 : Real.exp t ^ 6 = Real.exp (6 * t) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h4 : Real.exp (6 * t) ≤ Real.exp (3 * 10 * t) := Real.exp_le_exp.2 (by linarith)
    have h5 : Real.exp (3 * 10 * t) * Real.exp (-(3 * 10 * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h6 : t ^ 6 ≤ Real.exp (3 * 10 * t) := by linarith
    calc t ^ 6 * Real.exp (-(3 * 10 * t)) ≤ Real.exp (3 * 10 * t) * Real.exp (-(3 * 10 * t)) :=
          mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = 1 := h5
  have hM0 : 0 ≤ M := by linarith
  exact prop_arith (muE ψ ψ E) (mu ψ S) t (M ^ (2 * p0 + 1)) (M ^ (p0 + 1))
    (Real.exp (-(3 * 10 * t))) (M ^ (p0 + ((PP S S).filter (fun q => q ≤ p0)).card)) hA0 hm0 hm2
    ht (Real.exp_pos _) hte (pow_nonneg hM0 _) hKP hPQ (pow_nonneg hM0 _) hcl

end DSK

theorem OMA.solution : OMA.R_Erdos999_erdos_999_R1.H2 :=
  OMA.R_Erdos999_erdos_999_R1_H2_R1.main DSM.overlap_PV DSK.prop54
