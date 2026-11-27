import OMAReductions.R_Erdos683_erdos_683_variant_erdos_log_R1

-- Step Erdos683.erdos_683.variant.erdos_log.R1.H2: hypothesis H2 of reduction Erdos683.erdos_683.variant.erdos_log.R1
-- Credit: @ptc-prover-bot

/-!
Erdős's elementary range n > k^(3/2): if every prime factor of C(n,k) were below x = k log k / 20,
then (n/(2k))^k ≤ C(n,k) ≤ n^(number of primes ≤ x), because every prime power dividing C(n,k)
is at most n; the number of primes up to x is at most 2 log 4 · x / log x + √x (from
θ(x) ≤ x log 4), which is below 0.24 k, whereas the left side needs at least 0.3 k of them.
-/

open Finset Real

namespace OMA.Erdos683H2

/-- Chebyshev-type upper bound from θ(N) ≤ N log 4. -/
lemma card_S_le (N : ℕ) (hN : 2 ≤ N) :
    (((Ioc 0 N).filter Nat.Prime).card : ℝ) ≤ 2 * Real.log 4 * N / Real.log N + Real.sqrt N := by
  classical
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  set big := ((Ioc 0 N).filter Nat.Prime).filter (fun p => N < p * p)
  set small := ((Ioc 0 N).filter Nat.Prime).filter (fun p => ¬ N < p * p)
  have hsplit : ((Ioc 0 N).filter Nat.Prime).card = big.card + small.card := (card_filter_add_card_filter_not _).symm
  -- small primes are ≤ √N
  have hsmall : (small.card : ℝ) ≤ Real.sqrt N := by
    have hsub : small ⊆ Icc 1 (Nat.sqrt N) := by
      intro p hp
      simp only [small, mem_filter, mem_Ioc] at hp
      rw [mem_Icc]; push Not at hp
      exact ⟨hp.1.1.1, Nat.le_sqrt.mpr hp.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    calc (small.card : ℝ) ≤ Nat.sqrt N := by exact_mod_cast this
      _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  -- big primes have log p > log N / 2, and Σ log p ≤ θ(N) ≤ N log 4
  have hbig : (big.card : ℝ) * (Real.log N / 2) ≤ Real.log 4 * N := by
    have hθ : ∑ p ∈ big, Real.log p ≤ Real.log 4 * N := by
      calc ∑ p ∈ big, Real.log p ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Real.log p :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ => by
              have := (mem_filter.mp hp).2; exact Real.log_nonneg (by exact_mod_cast this.one_lt.le))
        _ = Chebyshev.theta N := by simp [Chebyshev.theta]
        _ ≤ Real.log 4 * N := Chebyshev.theta_le_log4_mul_x (by positivity)
    calc (big.card : ℝ) * (Real.log N / 2) = ∑ p ∈ big, Real.log N / 2 := by simp [sum_const]
      _ ≤ ∑ p ∈ big, Real.log p := by
          apply sum_le_sum; intro p hp
          have h1 : N < p * p := (mem_filter.mp hp).2
          have hp0 : (0 : ℝ) < p := by
            have := (mem_filter.mp (mem_filter.mp hp).1).2; exact_mod_cast this.pos
          have h2 : (N : ℝ) < (p : ℝ) * p := by exact_mod_cast h1
          have := Real.log_lt_log (by positivity) h2
          rw [Real.log_mul hp0.ne' hp0.ne'] at this
          linarith
      _ ≤ Real.log 4 * N := hθ
  have hbig' : (big.card : ℝ) ≤ 2 * Real.log 4 * N / Real.log N := by
    rw [le_div_iff₀ hlogN]; linarith
  rw [hsplit]; push_cast; linarith

/-- If every prime factor of C(n,k) is ≤ x then C(n,k) ≤ n ^ (number of primes ≤ x). -/
lemma choose_le_pow (n k x : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (h : ∀ p ∈ (n.choose k).primeFactors, p ≤ x) : n.choose k ≤ n ^ ((Ioc 0 x).filter Nat.Prime).card := by
  have hc : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  calc n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p :=
        (Nat.factorization_prod_pow_eq_self hc).symm
    _ ≤ ∏ p ∈ (n.choose k).primeFactors, n :=
        prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le hn)
    _ = n ^ (n.choose k).primeFactors.card := prod_const _
    _ ≤ n ^ ((Ioc 0 x).filter Nat.Prime).card := by
        apply Nat.pow_le_pow_right hn
        apply card_le_card; intro p hp
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨(Nat.prime_of_mem_primeFactors hp).pos, h p hp⟩, Nat.prime_of_mem_primeFactors hp⟩

/-- (n/(2k))^k ≤ C(n,k) for 1 ≤ k ≤ n/2. -/
lemma choose_ge (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n / 2) :
    ((n : ℝ) / (2 * k)) ^ k ≤ n.choose k := by
  have h := Nat.pow_le_choose (α := ℝ) k n
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hsub : ((n + 1 - k : ℕ) : ℝ) ≥ (n : ℝ) / 2 := by
    have : k ≤ n := by omega
    rw [Nat.cast_sub (by omega)]; push_cast
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast (show 2 * k ≤ n by omega)
    linarith
  calc ((n : ℝ) / (2 * k)) ^ k = ((n : ℝ) / 2) ^ k / (k : ℝ) ^ k := by rw [div_pow, div_pow, mul_pow, div_div]
    _ ≤ ((n + 1 - k : ℕ) : ℝ) ^ k / k.factorial := by
        apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hsub k)
          (by exact_mod_cast Nat.factorial_pos k) hfac
    _ ≤ n.choose k := h

lemma le_P {n k p : ℕ} (hp : p ∈ (n.choose k).primeFactors) : p ≤ Erdos683.P n k :=
  Finset.le_sup (f := id) hp

/-- The range n > k^(3/2): P(n,k) ≥ k log k / 20 once log k ≥ 20. -/
theorem large (n k : ℕ) (hK : Real.exp 20 ≤ k) (hkn : k ≤ n / 2) (hnk : k ^ 3 < n ^ 2) :
    (k : ℝ) * Real.log k / 20 ≤ Erdos683.P n k := by
  by_contra hlt
  push Not at hlt
  have hk0 : (1 : ℝ) < k := by linarith [Real.add_one_le_exp (20 : ℝ)]
  have hexp : (121 : ℝ) ≤ Real.exp 20 := by
    have h10 := Real.add_one_le_exp (10 : ℝ)
    have : Real.exp 20 = Real.exp 10 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hlogk : 20 ≤ Real.log k := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hK
  set y : ℝ := (k : ℝ) * Real.log k / 20 with hy
  set x : ℕ := ⌊y⌋₊ with hx
  have hky : (k : ℝ) ≤ y := by rw [hy, le_div_iff₀ (by norm_num)]; nlinarith
  have hkx : k ≤ x := Nat.le_floor hky
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) < k := by linarith [Real.add_one_le_exp 20]
    exact_mod_cast this.le
  have hn0 : 0 < n := by omega
  have hall : ∀ p ∈ (n.choose k).primeFactors, p ≤ x := by
    intro p hp
    apply Nat.le_floor
    have := le_P hp
    have : (p : ℝ) ≤ Erdos683.P n k := by exact_mod_cast this
    linarith
  have hC := choose_le_pow n k x hn0 (by omega) hall
  have hge := choose_ge n k (by omega) hkn
  -- logs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkR : (0 : ℝ) < k := by linarith
  have hlog1 : (k : ℝ) * Real.log ((n : ℝ) / (2 * k)) ≤ ((Ioc 0 x).filter Nat.Prime).card * Real.log n := by
    have h1 : ((n : ℝ) / (2 * k)) ^ k ≤ (n : ℝ) ^ ((Ioc 0 x).filter Nat.Prime).card := by
      calc ((n : ℝ) / (2 * k)) ^ k ≤ n.choose k := hge
        _ ≤ ((n ^ ((Ioc 0 x).filter Nat.Prime).card : ℕ) : ℝ) := by exact_mod_cast hC
        _ = (n : ℝ) ^ ((Ioc 0 x).filter Nat.Prime).card := by push_cast; ring
    have hpos : 0 < ((n : ℝ) / (2 * k)) ^ k := by positivity
    have := Real.log_le_log hpos h1
    rwa [Real.log_pow, Real.log_pow] at this
  -- at most (6/25) k primes up to x
  have hxR : (k : ℝ) ≤ x := by exact_mod_cast hkx
  have hx2 : 2 ≤ x := by omega
  have hxy : (x : ℝ) ≤ y := Nat.floor_le (by positivity)
  have hS := card_S_le x hx2
  have hlogx : Real.log k ≤ Real.log x := Real.log_le_log hkR hxR
  have hlog4 : Real.log 4 < (13863/10000 : ℝ) := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hA : 2 * Real.log 4 * x / Real.log x ≤ Real.log 4 / 10 * k := by
    have hl : 0 < Real.log k := by linarith
    calc 2 * Real.log 4 * x / Real.log x ≤ 2 * Real.log 4 * y / Real.log k := by
          apply div_le_div₀ (by positivity) (by nlinarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)])
            hl hlogx
      _ = Real.log 4 / 10 * k := by rw [hy]; field_simp; ring
  have hB : Real.sqrt x ≤ k / 10 := by
    have hlogle : Real.log k ≤ 2 * Real.sqrt k := by
      have := Real.log_le_rpow_div (le_of_lt hkR) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [Real.sqrt_eq_rpow]; linarith
    have hsq : 10 ≤ Real.sqrt k := by
      rw [show (10 : ℝ) = Real.sqrt 100 by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hyk : y ≤ ((k : ℝ) / 10) ^ 2 := by
      rw [hy]
      have : Real.log k ≤ k / 5 := by
        have := Real.sq_sqrt hkR.le
        nlinarith
      nlinarith
    calc Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
      _ ≤ Real.sqrt (((k : ℝ) / 10) ^ 2) := Real.sqrt_le_sqrt hyk
      _ = k / 10 := Real.sqrt_sq (by positivity)
  have hSk : (((Ioc 0 x).filter Nat.Prime).card : ℝ) ≤ (6/25 : ℝ) * k := by nlinarith
  -- log(n/(2k)) ≥ (9/20 : ℝ) log n
  have hlogn : 3 * Real.log k < 2 * Real.log n := by
    have : ((k : ℝ)) ^ 3 < (n : ℝ) ^ 2 := by exact_mod_cast hnk
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_pow, Real.log_pow] at this
  have hlog2 : Real.log 2 < (7/10 : ℝ) := by have := Real.log_two_lt_d9; linarith
  have hquot : (3/10 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / (2 * k)) := by
    rw [Real.log_div hnR.ne' (by positivity), Real.log_mul (by norm_num) hkR.ne']
    push_cast
    linarith
  have hLn : 0 < Real.log n := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hquot hkR.le, mul_le_mul_of_nonneg_right hSk hLn.le]

end OMA.Erdos683H2

theorem OMA.solution : OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.H2 :=
  fun n k hK hkn hnk => OMA.Erdos683H2.large n k hK hkn hnk
