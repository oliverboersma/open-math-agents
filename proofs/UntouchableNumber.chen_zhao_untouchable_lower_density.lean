import FormalConjectures.Wikipedia.UntouchableNumber
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Chebyshev

/-! Quantitative lower density of nonaliquot numbers.

The divisor-class count follows Chen and Zhao, Nonaliquot numbers, Theorem 1
(Publ. Math. Debrecen 78, 2011). Several sieve and aliquot lemmas are adapted
from the proof of Erdős 418 in open-math-agents PR #2148.
-/

open Filter Finset
open scoped Topology BigOperators ArithmeticFunction.sigma

namespace OMA.ChenZhao

open ArithmeticFunction.vonMangoldt in
private theorem primeReciprocalDiverges {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0) := by
  intro hs
  let g (x : ℝ) (n : ℕ) := (x - 1) * (residueClass a n / (n : ℝ) ^ x)
  let b (n : ℕ) := (if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0) +
    (if n.Prime then 0 else residueClass a n) / (n : ℝ)
  have hb : Summable b := hs.add (summable_residueClass_non_primes_div a)
  have he : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), x ∈ Set.Ioc 1 2 := by
    exact Ioc_mem_nhdsGT (by norm_num)
  have hbound {x : ℝ} (hx : x ∈ Set.Ioc 1 2) (n : ℕ) : ‖g x n‖ ≤ b n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [g, b]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnp : (0 : ℝ) < n := by positivity
    have hx0 : 0 ≤ x - 1 := sub_nonneg.mpr hx.1.le
    have hg : 0 ≤ g x n := by
      exact mul_nonneg hx0 (div_nonneg (residueClass_nonneg a n) (by positivity))
    rw [Real.norm_of_nonneg hg]
    by_cases hpr : n.Prime
    · by_cases hna : (n : ZMod q) = a
      · have hlog : 0 ≤ (x - 1) * Real.log n := mul_nonneg hx0 (Real.log_nonneg hn1)
        have hExp := Real.add_one_le_exp ((x - 1) * Real.log n)
        have hd : 0 < (n : ℝ) ^ x := by positivity
        have hrpow : (n : ℝ) ^ x = (n : ℝ) * Real.exp ((x - 1) * Real.log n) := by
          calc
            _ = (n : ℝ) ^ (1 + (x - 1)) := by ring_nf
            _ = _ := by rw [Real.rpow_add hnp, Real.rpow_one,
              Real.rpow_def_of_pos hnp, mul_comm (Real.log n)]
        simp only [b, hpr, hna, and_self, if_true, zero_div, add_zero]
        dsimp only [g]
        have hres : residueClass a n = Real.log n := by
          simp [residueClass, hna, ArithmeticFunction.vonMangoldt_apply_prime hpr]
        rw [hres, ← mul_div_assoc, inv_eq_one_div, div_le_div_iff₀ hd hnp, hrpow]
        nlinarith
      · simp [g, b, hpr, hna]
    · simp only [b, hpr, false_and, if_false, zero_add]
      calc
        g x n ≤ residueClass a n / (n : ℝ) ^ x :=
          mul_le_of_le_one_left (div_nonneg (residueClass_nonneg a n) (by positivity))
            (by linarith [hx.2])
        _ ≤ residueClass a n / (n : ℝ) := by
          apply div_le_div_of_nonneg_left (residueClass_nonneg a n) hnp
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hx.1.le
  have hpoint (n : ℕ) : Tendsto (g · n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [g]
    have hc : Continuous (g · n) := by
      have hpow : Continuous (fun x : ℝ => (n : ℝ) ^ x) :=
        Real.continuous_const_rpow (by exact_mod_cast hn.ne')
      exact (continuous_id.sub continuous_const).mul
        (continuous_const.div hpow (fun _ => by positivity))
    simpa [g] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have ht : Tendsto (fun x => ∑' n, g x n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb hpoint
      (he.mono fun x hx n => hbound hx n)
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hL : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (q.totient : ℝ)⁻¹ - C * (x - 1) ≤ ∑' n, g x n := by
    filter_upwards [he] with x hx
    have hx' : 0 < x - 1 := sub_pos.mpr hx.1
    have hh := mul_le_mul_of_nonneg_left (hC hx) hx'.le
    rw [mul_sub, mul_div_cancel₀ _ hx'.ne', ← tsum_mul_left] at hh
    simpa only [g, mul_comm (x - 1) C] using hh
  have hlt : Tendsto (fun x : ℝ => (q.totient : ℝ)⁻¹ - C * (x - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    have hc : Continuous (fun x : ℝ => (q.totient : ℝ)⁻¹ - C * (x - 1)) := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hbad := le_of_tendsto_of_tendsto hlt ht hL
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast q.totient.pos_of_neZero
  exact (not_lt_of_ge hbad) (inv_pos.mpr hpos)

private theorem totientReal (n : ℕ) :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

-- A finite set of primes outside any prescribed set can have arbitrarily small
-- product of the factors 1 - 1/p, by divergence of the prime reciprocal sum.
private theorem smallTotient {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (excluded : Finset ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ v : ℕ, 0 < v ∧ (∀ p ∈ v.primeFactors, (p : ZMod q) = a ∧ p ∉ excluded) ∧
      (v.totient : ℝ) < c * v := by
  classical
  let primeRecip (p : ℕ) : ℝ := if p.Prime ∧ (p : ZMod q) = a then (p : ℝ)⁻¹ else 0
  let remaining (p : ℕ) : ℝ := if p.Prime ∧ (p : ZMod q) = a ∧ p ∉ excluded then (p : ℝ)⁻¹ else 0
  let discarded (p : ℕ) : ℝ := if p ∈ excluded then primeRecip p else 0
  have hdiscard : Summable discarded :=
    summable_of_ne_finset_zero (s := excluded) fun p hp => by simp [discarded, hp]
  have hnot : ¬ Summable remaining := by
    intro h
    apply primeReciprocalDiverges ha
    convert h.add hdiscard using 1
    funext p
    by_cases hpr : p.Prime <;> by_cases hp : p ∈ excluded <;>
      by_cases hpa : (p : ZMod q) = a <;> simp [remaining, discarded, primeRecip, hpr, hp, hpa]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, -Real.log c < ∑ p ∈ s, remaining p := by
    by_contra! h
    exact hnot (summable_of_sum_le (fun p => by
      dsimp [remaining]
      split <;> positivity) h)
  let primes := s.filter fun (p : ℕ) => p.Prime ∧ (p : ZMod q) = a ∧ p ∉ excluded
  have hprime (p : ℕ) (hp : p ∈ primes) : p.Prime := (mem_filter.mp hp).2.1
  have hsum : -Real.log c < ∑ p ∈ primes, (p : ℝ)⁻¹ := by
    simpa only [primes, sum_filter, remaining] using hs
  let q := ∏ p ∈ primes, p
  have hq : 0 < q := prod_pos (fun p hp => (hprime p hp).pos)
  have hqf : q.primeFactors = primes := Nat.primeFactors_prod hprime
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hqf]
    exact fun p hp => (mem_filter.mp hp).2.2
  · have bound : ∏ p ∈ primes, (1 - (p : ℝ)⁻¹) < c := by
      calc
        _ ≤ ∏ p ∈ primes, Real.exp (-(p : ℝ)⁻¹) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_lt.le
            exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
          · intro p hp
            simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(p : ℝ)⁻¹)
        _ = Real.exp (-(∑ p ∈ primes, (p : ℝ)⁻¹)) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
        _ < c := by
          rw [← Real.exp_log hc]
          exact Real.exp_lt_exp.mpr (by linarith)
    rw [totientReal, hqf, mul_comm c]
    exact mul_lt_mul_of_pos_left bound (by exact_mod_cast hq)

private def coprimeUpTo (q x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => q.Coprime n

private theorem cardCoprimeUpTo {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (coprimeUpTo q x).card ≤ (x / q + 1) * q.totient := by
  let residues := (range q).filter fun r => q.Coprime r
  have hres : residues.card = q.totient := (Nat.totient_eq_card_coprime q).symm
  rw [← hres, ← card_range (x / q + 1), ← card_product]
  apply card_le_card_of_injOn (fun n => (n / q, n % q))
  · intro n hn
    have hn' := mem_filter.mp (show n ∈ coprimeUpTo q x from hn)
    have hx : n ≤ x := (mem_Icc.mp hn'.1).2
    have hr : q.Coprime (n % q) := by
      change q.gcd (n % q) = 1
      rw [Nat.gcd_comm q (n % q), ← Nat.gcd_rec q n]
      exact hn'.2
    exact mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hx)),
       mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq), hr⟩⟩
  · intro a ha b hb e
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    change a / q = b / q at e₁
    change a % q = b % q at e₂
    simpa only [Nat.mod_add_div] using congrArg₂ (fun d r => r + q * d) e₁ e₂

private theorem eventuallyCoprime {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c)
    (ht : (q.totient : ℝ) ≤ (c / 2) * q) :
    ∀ᶠ x : ℕ in atTop, ((coprimeUpTo q x).card : ℝ) ≤ c * x := by
  filter_upwards [eventually_ge_atTop q] with x hx
  have hbound : (x / q + 1) * q ≤ 2 * x := by
    rw [add_mul, one_mul, two_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x q) hx
  calc
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * (q.totient : ℝ) := by
      exact_mod_cast cardCoprimeUpTo hq x
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * ((c / 2) * q) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (c / 2) * (((x / q + 1 : ℕ) : ℝ) * q) := by ring
    _ ≤ (c / 2) * (2 * x) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by positivity)
    _ = c * x := by ring

private theorem commonPrime {q n : ℕ} (hq : q ≠ 0) (hn : n ≠ 0) (h : ¬ q.Coprime n) :
    ∃ p ∈ q.primeFactors, p ∈ n.primeFactors := by
  obtain ⟨p, hp, hpq, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩⟩

private theorem cardMultiples {d : ℕ} (hd : 0 < d) (x : ℕ) :
    ((Icc 1 x).filter fun n => d ∣ n).card ≤ x / d := by
  have hquot : (Icc 1 (x / d)).card = x / d := by simp [Nat.card_Icc]
  rw [← hquot]
  apply card_le_card_of_injOn (fun n => n / d)
  · intro n hn
    obtain ⟨hnI, hnD⟩ := mem_filter.mp (show n ∈ (Icc 1 x).filter (fun j => d ∣ j) from hn)
    have hnP : 0 < n := (mem_Icc.mp hnI).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnP hnD) hd,
      Nat.div_le_div_right (mem_Icc.mp hnI).2⟩
  · intro a ha b hb h
    have haD := (mem_filter.mp (show a ∈ (Icc 1 x).filter (fun j => d ∣ j) from ha)).2
    have hbD := (mem_filter.mp (show b ∈ (Icc 1 x).filter (fun j => d ∣ j) from hb)).2
    simpa only [Nat.div_mul_cancel haD, Nat.div_mul_cancel hbD] using congrArg (· * d) h

open scoped ArithmeticFunction.sigma

private def squareMultiple (P x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => ∃ p ∈ Icc P x, p ^ 2 ∣ n

-- A tail of the convergent p-series bounds the frequency of large square divisors.
private theorem largeSquareDivisors {c : ℝ} (hc : 0 < c) :
    ∃ P : ℕ, 3 ≤ P ∧ ∀ x : ℕ, ((squareMultiple P x).card : ℝ) ≤ c * x := by
  classical
  let f : ℕ → ℝ := fun p => 1 / (p : ℝ) ^ 2
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr (by decide)
  have htail : Tendsto (fun P : ℕ => ∑' i : ℕ, f (i + P)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∑' i, f i)).sub hf.hasSum.tendsto_sum_nat
    rw [sub_self] at h
    refine h.congr fun P => ?_
    linarith [hf.sum_add_tsum_nat_add P]
  obtain ⟨P, hP, hsmall⟩ := ((eventually_ge_atTop 3).and (htail.eventually_lt_const hc)).exists
  refine ⟨P, hP, fun x => ?_⟩
  let T := fun i : ℕ => (Icc 1 x).filter fun n => (i + P) ^ 2 ∣ n
  have hincl : squareMultiple P x ⊆ (range (x + 1)).biUnion T := by
    intro n hn
    obtain ⟨hn, p, hp, hd⟩ := mem_filter.mp hn
    obtain ⟨hp₁, hp₂⟩ := mem_Icc.mp hp
    refine mem_biUnion.mpr ⟨p - P, mem_range.mpr (by omega), mem_filter.mpr ⟨hn, ?_⟩⟩
    simpa only [Nat.sub_add_cancel hp₁] using hd
  have hcard : (squareMultiple P x).card ≤ ∑ i ∈ range (x + 1), (T i).card :=
    (card_le_card hincl).trans card_biUnion_le
  have hterm (i : ℕ) : ((T i).card : ℝ) ≤ (x : ℝ) * f (i + P) := by
    have hm : 0 < (i + P) ^ 2 := by positivity
    have hd : ((T i).card : ℝ) ≤ ((x / ((i + P) ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast cardMultiples hm x
    refine hd.trans ?_
    dsimp [f]
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast Nat.div_mul_le_self x ((i + P) ^ 2)
  calc
    _ ≤ ∑ i ∈ range (x + 1), ((T i).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ i ∈ range (x + 1), (x : ℝ) * f (i + P) := sum_le_sum fun i _ => hterm i
    _ = (x : ℝ) * (∑ i ∈ range (x + 1), f (i + P)) := by rw [mul_sum]
    _ ≤ (x : ℝ) * (∑' i : ℕ, f (i + P)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (summable_nat_add_iff P).2 hf |>.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ c * x := by rw [mul_comm c]; gcongr

private def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

private theorem sigmaEq (n : ℕ) : σ 1 n = aliquot n + n := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  rfl

private theorem scaleAliquot (k t : ℕ) (ht : 0 < t) : t * aliquot k ≤ aliquot (k * t) := by
  let f : ℕ → ℕ := fun d => d * t
  have hf : Function.Injective f := fun a b h => Nat.eq_of_mul_eq_mul_right ht h
  have hs : k.properDivisors.image f ⊆ (k * t).properDivisors := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    obtain ⟨had, hal⟩ := Nat.mem_properDivisors.mp ha
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right had t, Nat.mul_lt_mul_of_pos_right hal ht⟩
  calc
    _ = ∑ d ∈ k.properDivisors.image f, d := by
      rw [sum_image (fun a _ b _ h => hf h), aliquot, mul_sum]
      exact sum_congr rfl fun i _ => Nat.mul_comm t i
    _ ≤ aliquot (k * t) := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

private theorem factorizationEvenOfOddSigma {n : ℕ} (hn : Odd n) (hs : Odd (σ 1 n))
    (p : ℕ) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun e => hn.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactors hp)
  have hodd := hpr.odd_of_ne_two hp2
  let e := n.factorization p
  let f := fun q => σ 1 (q ^ n.factorization q)
  have hf : f p ∣ σ 1 n := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0]
    exact dvd_prod_of_mem f hp
  have hos : Odd (f p) := Nat.not_even_iff_odd.mp fun he => hs.not_two_dvd_nat (he.two_dvd.trans hf)
  change Odd (σ 1 (p ^ e)) at hos
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpr, odd_sum_iff_odd_card_odd] at hos
  have hall : (range (e + 1)).filter (fun i => Odd (p ^ i)) = range (e + 1) :=
    filter_true_of_mem fun i _ => hodd.pow
  rw [hall, card_range] at hos
  have hm := Nat.odd_iff.mp hos
  change Even e
  rw [Nat.even_iff]
  omega

private theorem oddPreimageSquare {n : ℕ} (hn : Odd n) (hs : 2 ∣ aliquot n) :
    ∃ r : ℕ, n = r ^ 2 := by
  have hsigma : Odd (σ 1 n) := by
    rw [sigmaEq]
    exact (even_iff_two_dvd.mpr hs).add_odd hn
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← prod_pow]
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn0
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have hp' := Nat.even_iff.mp (factorizationEvenOfOddSigma hn hsigma p hp)
      omega

private theorem primeSquareAliquot {p : ℕ} (hp : p.Prime) : aliquot (p ^ 2) = p + 1 := by
  have hs := sigmaEq (p ^ 2)
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at hs
  simp [sum_range_succ] at hs
  omega

private theorem compositeSquareAliquot {k r : ℕ} (hk : 2 ≤ k) (hr : k * k ≤ r)
    (hnp : ¬ r.Prime) : k * r ≤ aliquot (r ^ 2) := by
  have hr₂ : 2 ≤ r := (hk.trans (Nat.le_mul_of_pos_right _ (by omega))).trans hr
  obtain ⟨a, had, ha₂, hal⟩ := Nat.exists_dvd_of_not_prime2 hr₂ hnp
  obtain ⟨b, hb⟩ := had
  have hb₂ : 2 ≤ b := by
    by_contra! hh
    interval_cases b <;> simp_all
  let d := max a b
  have hd : d ∣ r := by
    rcases le_total a b with h | h
    · rw [show d = b from max_eq_right h, hb, mul_comm]
      exact dvd_mul_right _ _
    · rw [show d = a from max_eq_left h, hb]
      exact dvd_mul_right _ _
  have hdr : d < r := by
    apply max_lt hal
    rw [hb, mul_comm]
    exact lt_mul_of_one_lt_right (by omega) (by omega)
  have hkd : k ≤ d := by
    by_contra! hh
    have hab : a * b < k * k := Nat.mul_lt_mul_of_lt_of_lt (lt_of_le_of_lt (le_max_left ..) hh)
      (lt_of_le_of_lt (le_max_right ..) hh)
    omega
  have hmem : d * r ∈ (r ^ 2).properDivisors := by
    rw [pow_two]
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right hd r,
      Nat.mul_lt_mul_of_pos_right hdr (by omega)⟩
  exact (Nat.mul_le_mul_right r hkd).trans (single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem)

private theorem castDivLe (x : ℕ) {k : ℕ} (hk : 0 < k) : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / k := by
  rw [le_div_iff₀ (by exact_mod_cast hk)]
  exact_mod_cast Nat.div_mul_le_self x k

open scoped Classical in
private def badSigma (q x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => ¬ q ∣ σ 1 n

private theorem eventuallyBadSigma {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ((badSigma q x).card : ℝ) ≤ c * x := by
  let _ : NeZero q := ⟨hq.ne'⟩
  obtain ⟨P, _, hsq⟩ := largeSquareDivisors (half_pos hc)
  obtain ⟨v, hv, hprimes, htot⟩ := smallTotient
    (show IsUnit (-1 : ZMod q) from isUnit_one.neg) (range P) (half_pos (half_pos hc))
  filter_upwards [eventuallyCoprime hv (half_pos hc) htot.le] with x hcop
  have hsub : badSigma q x ⊆ coprimeUpTo v x ∪ squareMultiple P x := by
    intro n hn
    obtain ⟨hnI, hnS⟩ := mem_filter.mp hn
    have hn0 : 0 < n := (mem_Icc.mp hnI).1
    by_cases hcv : v.Coprime n
    · exact mem_union_left _ (mem_filter.mpr ⟨hnI, hcv⟩)
    obtain ⟨p, hpv, hpn⟩ := commonPrime hv.ne' hn0.ne' hcv
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hpd := Nat.dvd_of_mem_primeFactors hpn
    have hpP : P ≤ p := Nat.le_of_not_gt fun hpP => (hprimes p hpv).2 (mem_range.mpr hpP)
    by_cases hps : p ^ 2 ∣ n
    · exact mem_union_right _ (mem_filter.mpr
        ⟨hnI, p, mem_Icc.mpr ⟨hpP, (Nat.le_of_dvd hn0 hpd).trans (mem_Icc.mp hnI).2⟩, hps⟩)
    exfalso
    apply hnS
    have he : n.factorization p = 1 := by
      have hlo := (hp.dvd_iff_one_le_factorization hn0.ne').mp hpd
      have hhi := mt (hp.pow_dvd_iff_le_factorization hn0.ne').mpr hps
      omega
    have hqdp : q ∣ p + 1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      push_cast
      rw [(hprimes p hpv).1, neg_add_cancel]
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0.ne']
    apply dvd_trans _ (dvd_prod_of_mem (fun r => σ 1 (r ^ n.factorization r)) hpn)
    rw [he, ArithmeticFunction.sigma_one_apply_prime_pow hp]
    simpa [sum_range_succ, add_comm] using hqdp
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  calc
    _ ≤ ((coprimeUpTo v x).card : ℝ) + ((squareMultiple P x).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (c / 2) * x + (c / 2) * x := add_le_add hcop (hsq x)
    _ = c * x := by ring

private def oddValues (k x : ℕ) : Finset ℕ :=
  ((Nat.primesLE x).image fun r => r + 1) ∪ ((Icc 1 (x / k)).image fun r => aliquot (r ^ 2))

private theorem mem_oddValues {k x m : ℕ} (hk : 2 ≤ k) (hx : k ^ 3 ≤ x)
    (hm : Odd m) (hpos : 0 < aliquot m) (he : Even (aliquot m)) (hle : aliquot m ≤ x) :
    aliquot m ∈ oddValues k x := by
  obtain ⟨r, hr⟩ := oddPreimageSquare hm he.two_dvd
  have hr0 : 0 < r := by
    by_contra! hh
    have : r = 0 := by omega
    simp [this] at hr
    simp [hr, aliquot] at hpos
  subst m
  by_cases hp : r.Prime
  · have hv := primeSquareAliquot hp
    exact mem_union_left _ (mem_image.mpr ⟨r, Nat.mem_primesLE.mpr ⟨by omega, hp⟩, hv.symm⟩)
  · have hrx : r ≤ x / k := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
      by_cases hh : k * k ≤ r
      · exact (by simpa [Nat.mul_comm] using compositeSquareAliquot hk hh hp :
          r * k ≤ aliquot (r ^ 2)).trans hle
      · calc
          r * k ≤ (k * k) * k := Nat.mul_le_mul_right _ (by omega)
          _ = k ^ 3 := by ring
          _ ≤ x := hx
    exact mem_union_right _ (mem_image.mpr ⟨r, mem_Icc.mpr ⟨hr0, hrx⟩, rfl⟩)

private theorem eventually_prime_count_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ((Nat.primesLE x).card : ℝ) ≤ c * x := by
  have h := tendsto_natCast_atTop_atTop (R := ℝ)
  have hl := Real.tendsto_log_atTop.comp h
  filter_upwards [h.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)),
    hl.eventually_ge_atTop ((Real.log 4 + 1) / c), eventually_ge_atTop (2 : ℕ)] with x hx hlog hx2
  have hpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlog' := (div_le_iff₀ hc).mp hlog
  change Real.log 4 + 1 ≤ Real.log (x : ℝ) * c at hlog'
  rw [Nat.floor_natCast] at hx
  calc
    _ = (Nat.primeCounting x : ℝ) := by rw [Nat.primesLE_card_eq_primeCounting]
    _ ≤ (Real.log 4 + 1) * x / Real.log x := hx
    _ ≤ c * x := (div_le_iff₀ hpos).mpr (by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_right hlog' (Nat.cast_nonneg (α := ℝ) x))

private theorem eventually_odd_count_small {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ x : ℕ in atTop,
      k ^ 3 ≤ x ∧ ((oddValues k x).card : ℝ) ≤ c * x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 (2 / c))
  have hk₂ : 2 ≤ k := by
    exact_mod_cast (le_max_left (2 : ℝ) (2 / c)).trans hk.le
  have hkinv : 1 / (k : ℝ) ≤ c / 2 := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hbig := (div_lt_iff₀ hc).mp ((le_max_right (2 : ℝ) (2 / c)).trans_lt hk)
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  refine ⟨k, hk₂, ?_⟩
  filter_upwards [eventually_ge_atTop (k ^ 3), eventually_prime_count_small (half_pos hc)]
    with x hx hp
  refine ⟨hx, ?_⟩
  have hcard : (oddValues k x).card ≤ (Nat.primesLE x).card + x / k := by
    apply (card_union_le _ _).trans
    refine Nat.add_le_add card_image_le (card_image_le.trans ?_)
    simp [Nat.card_Icc]
  calc
    _ ≤ ((Nat.primesLE x).card : ℝ) + ((x / k : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (c / 2) * x + (x : ℝ) / k := add_le_add hp (castDivLe x (by omega))
    _ ≤ c * x := by
      have ht := mul_le_mul_of_nonneg_right hkinv (Nat.cast_nonneg (α := ℝ) x)
      rw [div_mul_eq_mul_div, one_mul] at ht
      linarith

private theorem castDivSubOne (x : ℕ) {q : ℕ} (hq : 0 < q) :
    (x : ℝ) / q - 1 ≤ ((x / q : ℕ) : ℝ) := by
  have h := Nat.mod_add_div x q
  have hm := Nat.mod_lt x hq
  have h' : (x : ℝ) ≤ (q : ℝ) * ((x / q : ℕ) + 1) := by
    exact_mod_cast (show x ≤ q * (x / q + 1) by rw [Nat.mul_succ]; omega)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have h'' := (div_le_iff₀ hq').mpr (by linarith : (x : ℝ) ≤ ((x / q : ℕ) + 1) * q)
  linarith

private theorem cardCoprimeMultiple (q k : ℕ) :
    (coprimeUpTo q (q * k)).card = q.totient * k := by
  induction k with
  | zero => simp [coprimeUpTo]
  | succ k ih =>
    have hsplit : Icc 1 (q * (k + 1)) =
        Icc 1 (q * k) ∪ Ico (q * k + 1) (q * k + 1 + q) := by
      ext n
      simp only [mem_Icc, mem_union, mem_Ico, Nat.mul_succ]
      omega
    have hd : Disjoint
        ((Icc 1 (q * k)).filter fun n => q.Coprime n)
        ((Ico (q * k + 1) (q * k + 1 + q)).filter fun n => q.Coprime n) := by
      rw [Finset.disjoint_left]
      intro n hn hm
      have h₁ := (mem_Icc.mp (mem_filter.mp hn).1).2
      have h₂ := (mem_Ico.mp (mem_filter.mp hm).1).1
      omega
    rw [coprimeUpTo, hsplit, filter_union, card_union_of_disjoint hd,
      Nat.filter_coprime_Ico_eq_totient, ← coprimeUpTo, ih, Nat.mul_succ]

private theorem cardCoprimeAtLeast (q x : ℕ) :
    q.totient * (x / q) ≤ (coprimeUpTo q x).card := by
  rw [← cardCoprimeMultiple]
  apply card_le_card
  intro n hn
  obtain ⟨h, hc⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp h).1,
    (mem_Icc.mp h).2.trans (Nat.mul_comm q (x / q) ▸ Nat.div_mul_le_self x q)⟩, hc⟩

private def goodDivisors (q : ℕ) : Finset ℕ :=
  q.divisors.filter (fun d => Even d ∧ d < aliquot d)

private noncomputable def term (q d : ℕ) : ℝ :=
  (q / d).totient / (q : ℝ) * ((aliquot d : ℝ) - d) / aliquot d

private def classValues (q d x : ℕ) : Finset ℕ :=
  (coprimeUpTo (q / d) (x / d)).image (fun m => d * m)

private def regularValues (q d x : ℕ) : Finset ℕ :=
  (coprimeUpTo (q / d) (x / aliquot d)).image (fun m => aliquot (d * m))

private theorem class_mem {q d y x : ℕ} (h : y ∈ classValues q d x) (hd : d ∣ q) :
    0 < y ∧ y ≤ x ∧ q.gcd y = d := by
  obtain ⟨m, hm, rfl⟩ := mem_image.mp h
  obtain ⟨hmI, hmC⟩ := mem_filter.mp hm
  obtain ⟨hm0, hmx⟩ := mem_Icc.mp hmI
  have hd0 : 0 < d := by
    by_contra! H
    have : d = 0 := by omega
    subst d
    simp at hmx
    omega
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      d * m ≤ d * (x / d) := Nat.mul_le_mul_left _ hmx
      _ ≤ x := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  · have hq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
    change (q / d).gcd m = 1 at hmC
    conv_lhs => rw [hq]
    rw [Nat.gcd_mul_left, hmC, mul_one]

private theorem card_classes {q d : ℕ} (hq : 0 < q) (hd : d ∈ goodDivisors q) (x : ℕ) :
    term q d * x - 2 * ((q / d).totient : ℝ) ≤
      (((classValues q d x) \ (regularValues q d x)).card : ℝ) := by
  obtain ⟨hdD, _, hds⟩ := mem_filter.mp hd
  have hdq := Nat.dvd_of_mem_divisors hdD
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  let a := q / d
  let s := aliquot d
  have hs : 0 < s := by omega
  have hda : d * a = q := Nat.mul_div_cancel' hdq
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h, mul_zero] at hda
    omega
  let A := classValues q d x
  let B := regularValues q d x
  have hA : (a.totient : ℝ) * ((x : ℝ) / q - 1) ≤ A.card := by
    have hb := cardCoprimeAtLeast a (x / d)
    rw [Nat.div_div_eq_div_mul, hda] at hb
    have hc : A.card = (coprimeUpTo a (x / d)).card := by
      exact card_image_of_injective _ (fun y z hh => Nat.eq_of_mul_eq_mul_left hd0 hh)
    rw [hc]
    exact (mul_le_mul_of_nonneg_left (castDivSubOne x hq) (by positivity)).trans
      (by exact_mod_cast hb)
  have hB : (B.card : ℝ) ≤ (a.totient : ℝ) * ((x : ℝ) / (s * a) + 1) := by
    have hb : B.card ≤ (x / s / a + 1) * a.totient :=
      card_image_le.trans (cardCoprimeUpTo ha (x / s))
    rw [Nat.div_div_eq_div_mul] at hb
    calc
      _ ≤ (((x / (s * a) : ℕ) : ℝ) + 1) * (a.totient : ℝ) := by exact_mod_cast hb
      _ ≤ _ := by
        rw [mul_comm (a.totient : ℝ)]
        gcongr
        simpa only [Nat.cast_mul] using castDivLe x (show 0 < s * a by positivity)
  have hAB : (A.card : ℝ) ≤ ((A \ B).card : ℝ) + B.card := by
    have hh : A.card ≤ ((A \ B) ∪ B).card :=
      card_le_card (fun m hm => by
        by_cases h : m ∈ B
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hm,h⟩))
    exact_mod_cast hh.trans (card_union_le _ _)
  have heq : term q d * x =
      (a.totient : ℝ) * ((x : ℝ) / q - (x : ℝ) / (s * a)) := by
    have hd' : (0 : ℝ) < d := by positivity
    have hs' : (0 : ℝ) < s := by positivity
    have ha' : (0 : ℝ) < a := by positivity
    have hda' : (d : ℝ) * a = (q : ℝ) := by exact_mod_cast hda
    change (a.totient : ℝ) / q * ((s : ℝ) - d) / s * x = _
    rw [← hda']
    field_simp
  rw [heq]
  change _ ≤ ((A \ B).card : ℝ)
  linarith

private theorem gcd_sum_zero {q y m : ℕ} (h : q ∣ y + m) : q.gcd y = q.gcd m := by
  have hy : q.gcd y ∣ q := Nat.gcd_dvd_left _ _
  have hm : q.gcd m ∣ q := Nat.gcd_dvd_left _ _
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd hy ?_
    have hp := Nat.dvd_sub (hy.trans h) (Nat.gcd_dvd_right q y)
    simpa only [Nat.add_sub_cancel_left] using hp
  · refine Nat.dvd_gcd hm ?_
    have hp := Nat.dvd_sub (hm.trans h) (Nat.gcd_dvd_right q m)
    simpa only [Nat.add_sub_cancel_right] using hp

private theorem mem_regularValues {q d m x : ℕ} (hq : q ∣ σ 1 m)
    (hdq : d ∣ q) (hd : 0 < d) (hm : 0 < m) (hx : aliquot m ≤ x)
    (hgcd : q.gcd (aliquot m) = d) (hs : 0 < aliquot d) :
    aliquot m ∈ regularValues q d x := by
  rw [sigmaEq] at hq
  have hg := (gcd_sum_zero hq).symm.trans hgcd
  obtain ⟨t, ht⟩ : d ∣ m := hg ▸ Nat.gcd_dvd_right q m
  have ht0 : 0 < t := by rw [ht] at hm; exact Nat.pos_of_mul_pos_left hm
  have hc : (q / d).Coprime t := by
    rw [ht, ← Nat.mul_div_cancel' hdq, Nat.gcd_mul_left] at hg
    exact Nat.eq_of_mul_eq_mul_left hd (hg.trans (Nat.mul_one d).symm)
  have hscale := scaleAliquot d t ht0
  rw [← ht] at hscale
  exact mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_Icc.mpr ⟨ht0,
    (Nat.le_div_iff_mul_le hs).mpr (hscale.trans hx)⟩, hc⟩, congrArg aliquot ht.symm⟩

private def candidateValues (q x : ℕ) : Finset ℕ :=
  (goodDivisors q).biUnion (fun d => classValues q d x \ regularValues q d x)

private theorem count_candidates {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (∑ d ∈ goodDivisors q, term q d) * (x : ℝ) -
      ∑ d ∈ goodDivisors q, 2 * ((q / d).totient : ℝ) ≤ (candidateValues q x).card := by
  have hp : (goodDivisors q : Set ℕ).PairwiseDisjoint
      (fun d => classValues q d x \ regularValues q d x) := by
    intro a ha b hb hab
    change Disjoint (classValues q a x \ regularValues q a x)
      (classValues q b x \ regularValues q b x)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have hga := (class_mem (mem_sdiff.mp hya).1
      (Nat.dvd_of_mem_divisors (mem_filter.mp ha).1)).2.2
    have hgb := (class_mem (mem_sdiff.mp hyb).1
      (Nat.dvd_of_mem_divisors (mem_filter.mp hb).1)).2.2
    exact hab (hga.symm.trans hgb)
  rw [candidateValues, card_biUnion hp, Nat.cast_sum, sum_mul, ← sum_sub_distrib]
  exact sum_le_sum (fun d hd => card_classes hq hd x)

private noncomputable def untouchablesUpTo (x : ℕ) : Finset ℕ :=
  open Classical in (Icc 1 x).filter (fun n => n.IsUntouchable)

private theorem eventual_untouchable_count {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      ((∑ d ∈ goodDivisors q, term q d) - c) * (x : ℝ) -
        ∑ d ∈ goodDivisors q, 2 * ((q / d).totient : ℝ) ≤ (untouchablesUpTo x).card := by
  classical
  have hscale : Tendsto (fun x : ℕ => 2 * x) atTop atTop :=
    tendsto_atTop_mono (fun x => by dsimp [id]; omega) tendsto_id
  obtain ⟨k, hk, hodd⟩ := eventually_odd_count_small (half_pos hc)
  filter_upwards [hscale.eventually (eventuallyBadSigma hq (c := c / 4) (by positivity)),
    hodd] with x hs ho
  let B := (badSigma q (2 * x)).image aliquot
  let D := oddValues k x
  have hb : (B.card : ℝ) ≤ (c / 4) * ((2 * x : ℕ) : ℝ) := by
    have hcard : (B.card : ℝ) ≤ (badSigma q (2 * x)).card := by
      exact_mod_cast (card_image_le : B.card ≤ (badSigma q (2 * x)).card)
    exact hcard.trans hs
  have hsubset : candidateValues q x ⊆ untouchablesUpTo x ∪ (B ∪ D) := by
    intro y hy
    obtain ⟨d, hd, hy⟩ := mem_biUnion.mp hy
    obtain ⟨hyA, hyB⟩ := mem_sdiff.mp hy
    have hdD := (mem_filter.mp hd).1
    have hdq := Nat.dvd_of_mem_divisors hdD
    have hd0 := Nat.pos_of_dvd_of_pos hdq hq
    have hds := (mem_filter.mp hd).2.2
    obtain ⟨hy0, hyX, hg⟩ := class_mem hyA hdq
    have hye : Even y :=
      even_iff_two_dvd.mpr ((mem_filter.mp hd).2.1.two_dvd.trans
        (hg ▸ Nat.gcd_dvd_right q y))
    by_cases hu : y.IsUntouchable
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hy0, hyX⟩, hu⟩)
    apply mem_union_right
    have hpre : ∃ m : ℕ, aliquot m = y := by
      simpa only [Nat.IsUntouchable, not_not, aliquot] using hu
    obtain ⟨m, hm⟩ := hpre
    have hm0 : 0 < m := by
      by_contra! h
      simp [show m = 0 by omega, aliquot] at hm
      omega
    by_cases hme : Even m
    · have hmX : m ≤ 2 * x := by
        obtain ⟨u, he⟩ := hme.two_dvd
        have h := scaleAliquot 2 u (by omega)
        rw [← he, show aliquot 2 = 1 by decide, mul_one, hm] at h
        omega
      by_cases hdiv : q ∣ σ 1 m
      · exfalso
        apply hyB
        rw [← hm] at hg hyX ⊢
        exact mem_regularValues hdiv hdq hd0 hm0 hyX hg (by omega)
      · exact mem_union_left _ (mem_image.mpr ⟨m, mem_filter.mpr
          ⟨mem_Icc.mpr ⟨hm0, hmX⟩, hdiv⟩, hm⟩)
    · exact mem_union_right _ (hm ▸ mem_oddValues hk ho.1 (Nat.not_even_iff_odd.mp hme)
        (hm ▸ hy0) (hm ▸ hye) (hm ▸ hyX))
  have hcard : (candidateValues q x).card ≤ (untouchablesUpTo x).card +
      (B.card + D.card) := (card_le_card hsubset).trans ((card_union_le _ _).trans
        (Nat.add_le_add_left (card_union_le _ _) _))
  have hh : ((candidateValues q x).card : ℝ) ≤ (untouchablesUpTo x).card +
      ((B.card : ℝ) + D.card) := by exact_mod_cast hcard
  push_cast at hb
  linarith [count_candidates hq x, ho.2]

private def modulusFactors : List (ℕ × ℕ) :=
  [(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1),
    (23, 1), (29, 1), (31, 1), (37, 1)]

private def productModulus : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: rest => p ^ a * productModulus rest

private def scale : ℕ := 10 ^ 12

private def divisorSumPrimePower (p k : ℕ) : ℕ := (p ^ (k + 1) - 1) / (p - 1)

private def totientPrimePower (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => p ^ k * (p - 1)

private def lowerWeight (q d s t : ℕ) : ℕ :=
  if d % 2 = 0 then scale * t * (s - 2 * d) / (q * (s - d)) else 0

private def evaluateWeights (q : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ
  | [], d, s, t => lowerWeight q d s t
  | (p, a) :: rest, d, s, t => ((List.range (a + 1)).map fun k =>
      evaluateWeights q rest (d * p ^ k) (s * divisorSumPrimePower p k)
        (t * totientPrimePower p (a - k))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem numeric_bound :
    60000100000 ≤ evaluateWeights (productModulus modulusFactors) modulusFactors 1 1 1 := by
  decide +kernel

private def ValidFactors : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, _) :: rest => p.Prime ∧ p.Coprime (productModulus rest) ∧ ValidFactors rest

private theorem factors_valid : ValidFactors modulusFactors := by
  norm_num [modulusFactors, ValidFactors, productModulus, Nat.Coprime]

private theorem productModulus_pos {L : List (ℕ × ℕ)} (hL : ValidFactors L) :
    0 < productModulus L := by
  induction L with
  | nil => decide
  | cons head rest ih =>
    obtain ⟨p, a⟩ := head
    obtain ⟨hp, _, hr⟩ := hL
    exact Nat.mul_pos (pow_pos hp.pos _) (ih hr)

private theorem sumDivisorsCoprime {s t : ℕ} (hs : 0 < s) (ht : 0 < t) (h : s.Coprime t)
    (f : ℕ → ℕ) :
    (∑ a ∈ s.divisors, ∑ b ∈ t.divisors, f (a * b)) = ∑ c ∈ (s * t).divisors, f c := by
  rw [← sum_product']
  refine sum_bij' (fun a _ => a.1 * a.2) (fun c _ => (c.gcd s, c.gcd t)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1,h2⟩ := mem_product.mp ha
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul
      (Nat.dvd_of_mem_divisors h1) (Nat.dvd_of_mem_divisors h2), (Nat.mul_pos hs ht).ne'⟩
  · intro c _
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hs.ne'⟩,
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, ht.ne'⟩⟩
  · intro a ha
    obtain ⟨h1,h2⟩ := mem_product.mp ha
    have h1d := Nat.dvd_of_mem_divisors h1
    have h2d := Nat.dvd_of_mem_divisors h2
    apply Prod.ext
    · exact mul_comm a.1 a.2 ▸ Nat.gcd_mul_of_coprime_of_dvd
        (h.symm.of_dvd_left h2d) h1d
    · exact Nat.gcd_mul_of_coprime_of_dvd (h.of_dvd_left h1d) h2d
  · intro c hc
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr (Nat.dvd_of_mem_divisors hc)
  · intros
    rfl

private def certifiedWeight (q d : ℕ) : ℕ :=
  lowerWeight q d (σ 1 d) ((q / d).totient)

private theorem listSumRange (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

private theorem evaluateWeights_eq {L : List (ℕ × ℕ)} (hL : ValidFactors L)
    {q : ℕ} (d w : ℕ) (hd : 0 < d) (hw : 0 < w)
    (hq : q = d * w * productModulus L)
    (hdc : d.Coprime (productModulus L)) (hwc : w.Coprime (productModulus L)) :
    evaluateWeights q L d (σ 1 d) w.totient =
      ∑ i ∈ (productModulus L).divisors, certifiedWeight q (d * i) := by
  induction L generalizing d w with
  | nil =>
    have hqw : q / d = w := by
      rw [hq, productModulus, mul_one, Nat.mul_div_cancel_left _ hd]
    simp [evaluateWeights, productModulus, certifiedWeight, hqw]
  | cons head L ih =>
    obtain ⟨p, a⟩ := head
    obtain ⟨hp, hpr, htail⟩ := hL
    let r := productModulus L
    have hr : 0 < r := productModulus_pos htail
    have hpc : (p ^ a).Coprime r := hpr.pow_left _
    change q = d * w * (p ^ a * r) at hq
    change d.Coprime (p ^ a * r) at hdc
    change w.Coprime (p ^ a * r) at hwc
    simp only [evaluateWeights, productModulus, listSumRange]
    rw [← sumDivisorsCoprime (pow_pos hp.pos _) hr hpc, Nat.sum_divisors_prime_pow hp]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ a := by have := mem_range.mp hk; omega
    have hda : d.Coprime (p ^ k) := (hdc.of_dvd_right (dvd_mul_right _ _)).of_dvd_right
      (Nat.pow_dvd_pow _ hk')
    have hwa : w.Coprime (p ^ (a - k)) := (hwc.of_dvd_right (dvd_mul_right _ _)).of_dvd_right
      (Nat.pow_dvd_pow _ (by omega))
    have hdr : (d * p ^ k).Coprime r :=
      (hdc.of_dvd_right (dvd_mul_left _ _)).mul_left (hpr.pow_left _)
    have hwr : (w * p ^ (a - k)).Coprime r :=
      (hwc.of_dvd_right (dvd_mul_left _ _)).mul_left (hpr.pow_left _)
    have hnews : σ 1 (d * p ^ k) = σ 1 d * divisorSumPrimePower p k := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hda,
        ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
      rfl
    have hnewt : (w * p ^ (a - k)).totient =
        w.totient * totientPrimePower p (a - k) := by
      rw [Nat.totient_mul hwa]
      cases h : a - k with
      | zero => simp [totientPrimePower]
      | succ e => rw [Nat.totient_prime_pow_succ hp]; rfl
    have hnq : q = (d * p ^ k) * (w * p ^ (a - k)) * productModulus L := by
      calc
        q = d * w * (p ^ a * r) := hq
        _ = d * w * ((p ^ k * p ^ (a - k)) * r) := by rw [← pow_add, Nat.add_sub_cancel' hk']
        _ = _ := by dsimp [r]; ac_rfl
    rw [← hnews, ← hnewt,
      ih htail (d * p ^ k) (w * p ^ (a - k)) (Nat.mul_pos hd (pow_pos hp.pos _))
        (Nat.mul_pos hw (pow_pos hp.pos _)) hnq hdr hwr]
    exact sum_congr rfl fun i _ => by rw [mul_assoc]

private theorem weight_le {q : ℕ} (hq : 0 < q) (d : ℕ) :
    (certifiedWeight q d : ℝ) ≤
      if Even d ∧ d < aliquot d then (scale : ℝ) * term q d else 0 := by
  have hσ := sigmaEq d
  by_cases he : Even d
  · have he' := Nat.even_iff.mp he
    by_cases hs : d < aliquot d
    · have hf : 0 < q * aliquot d := Nat.mul_pos hq (by omega)
      have hb := castDivLe (scale * (q / d).totient * (aliquot d - d)) hf
      have h₁ : σ 1 d - d = aliquot d := by omega
      have h₂ : σ 1 d - 2 * d = aliquot d - d := by omega
      simp only [certifiedWeight, lowerWeight, he', if_true, h₁, h₂, he, hs, and_self]
      push_cast [Nat.cast_sub hs.le] at hb
      apply hb.trans_eq
      unfold term
      rw [div_mul_eq_mul_div]
      field_simp
    · have h₂ : σ 1 d - 2 * d = 0 := by omega
      simp [certifiedWeight, lowerWeight, he, he', hs, h₂]
  · have he' := mt Nat.even_iff.mpr he
    simp [certifiedWeight, lowerWeight, he, he']

private theorem certified_lower_bound :
    (600001 / 10000000 : ℝ) ≤
      ∑ d ∈ goodDivisors (productModulus modulusFactors), term (productModulus modulusFactors) d := by
  let q := productModulus modulusFactors
  have hq : 0 < q := productModulus_pos factors_valid
  have heval : evaluateWeights q modulusFactors 1 1 1 =
      ∑ d ∈ q.divisors, certifiedWeight q d := by
    simpa using evaluateWeights_eq factors_valid (q := q) 1 1 (by decide) (by decide)
      (by simp [q]) (by simp) (by simp)
  have hsum : ((∑ d ∈ q.divisors, certifiedWeight q d : ℕ) : ℝ) ≤
      (scale : ℝ) * (∑ d ∈ goodDivisors q, term q d) := by
    rw [Nat.cast_sum, goodDivisors, mul_sum]
    simp only [sum_filter]
    exact sum_le_sum (fun d _ => weight_le hq d)
  have hnum : (60000100000 : ℝ) ≤ ((∑ d ∈ q.divisors, certifiedWeight q d : ℕ) : ℝ) := by
    exact_mod_cast (heval ▸ numeric_bound)
  have h := hnum.trans hsum
  norm_num [scale] at h
  change (600001 / 10000000 : ℝ) ≤ ∑ d ∈ goodDivisors q, term q d
  linarith
private theorem countInIio (x : ℕ) : (untouchablesUpTo x).card ≤
    ({n : ℕ | n.IsUntouchable} ∩ Set.Iio (x + 1)).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.finite_Iio _ |>.subset Set.inter_subset_right)
  intro n hn
  obtain ⟨hI, hU⟩ := mem_filter.mp (show n ∈ untouchablesUpTo x from hn)
  exact ⟨hU, Nat.lt_succ_of_le (mem_Icc.mp hI).2⟩

end OMA.ChenZhao

open OMA.ChenZhao

theorem OMA.solution : type_of% @UntouchableNumber.chen_zhao_untouchable_lower_density := by
  classical
  let q := productModulus modulusFactors
  let S : Set ℕ := {n | n.IsUntouchable}
  let e := ∑ d ∈ goodDivisors q, 2 * ((q / d).totient : ℝ)
  let c : ℝ := 1 / 100000000
  have hq : 0 < q := productModulus_pos factors_valid
  have hc : 0 < c := by norm_num [c]
  have hmain := eventual_untouchable_count hq hc
  have hcompute : (600001 / 10000000 : ℝ) ≤ ∑ d ∈ goodDivisors q, term q d :=
    certified_lower_bound
  have hlower : ∀ᶠ x : ℕ in atTop, (6 / 100 : ℝ) * ((x : ℝ) + 1) ≤
      (untouchablesUpTo x).card := by
    have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((e + 6 / 100) / c)
    filter_upwards [hmain, hlarge] with x hx hxlarge
    have he : e + 6 / 100 ≤ c * (x : ℝ) := by
      rw [mul_comm c]
      exact (div_le_iff₀ hc).mp hxlarge
    have hcoef : (6 / 100 : ℝ) + c ≤ (∑ d ∈ goodDivisors q, term q d) - c := by
      dsimp [c]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) x)
    change ((∑ d ∈ goodDivisors q, term q d) - c) * (x : ℝ) - e ≤ _ at hx
    calc
      _ ≤ (6 / 100 + c) * (x : ℝ) - e := by nlinarith only [he]
      _ ≤ _ := (sub_le_sub_right hmul e).trans hx
  change (6 / 100 : ℝ) ≤ S.lowerDensity
  unfold Set.lowerDensity
  rw [Filter.liminf_eq]
  have hb : BddAbove {r : ℝ | ∀ᶠ n : ℕ in atTop, r ≤ S.partialDensity Set.univ n} := by
    refine ⟨1, fun r hr => ?_⟩
    obtain ⟨n, hn⟩ := (show ∀ᶠ n : ℕ in atTop, r ≤ S.partialDensity Set.univ n from hr).exists
    exact hn.trans (Set.partialDensity_le_one _ _ _)
  apply le_csSup hb
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlower
  refine eventually_atTop.mpr ⟨K + 1, fun n hn => ?_⟩
  let x := n - 1
  have hnx : n = x + 1 := by dsimp [x]; omega
  have hx : K ≤ x := by dsimp [x]; omega
  have hcard : (6 / 100 : ℝ) * ((x : ℝ) + 1) ≤ ((S ∩ Set.Iio (x + 1)).ncard : ℝ) :=
    (hK x hx).trans (by exact_mod_cast countInIio x)
  have hden : (Set.Iio (x + 1)).ncard = x + 1 := by simp
  rw [hnx]
  change (6 / 100 : ℝ) ≤ ((S ∩ Set.univ ∩ Set.Iio (x + 1)).ncard : ℝ) /
    ((Set.univ ∩ Set.Iio (x + 1)).ncard : ℝ)
  simp only [Set.inter_univ, Set.univ_inter, hden, Nat.cast_add, Nat.cast_one]
  exact (le_div_iff₀ (by positivity)).mpr hcard
