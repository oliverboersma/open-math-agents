import FormalConjectures.ErdosProblems.«420»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# A one-sided sieve reduction for Erdős 420(ii)

The factorial increment estimate follows Erdős, Graham, Ivić and Pomerance,
On the number of divisors of n!, Theorem 2. The protected progression and
rough cluster inputs follow the Plasma AI formalization and its proof blueprint
at https://raw.githubusercontent.com/plasma-ai/erdos-420/main/blueprint/proof.md.
The manuscript by Codex at Jordan Pollard's request also uses protected prime
multiples and an upper sieve over a whole slab. Here the upper sieve only counts
positions to the left of each anchor. The proof bounds upward increments
directly, including when the moving endpoint advances by two.
-/

namespace OMA.R_Erdos420_erdos_420_parts_ii_R1

open Finset Filter
open scoped ArithmeticFunction.sigma Topology

private noncomputable def L (n : ℕ) : ℝ := Real.log (σ 0 n.factorial : ℝ)

private noncomputable def gain (x : ℕ) : ℝ := L x - L (x - 1)

private noncomputable def primeGain (x : ℕ) : ℝ :=
  ∑ p ∈ x.primeFactors with x < p ^ 2, Real.log (1 + (p : ℝ) / x)

private lemma gain_nonneg (x : ℕ) : 0 ≤ gain x := by
  unfold gain L
  apply sub_nonneg.mpr
  have hpos : (0 : ℝ) < (σ 0 (x - 1).factorial : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero _)
  apply Real.log_le_log hpos
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
    (Nat.factorial_dvd_factorial (Nat.sub_le _ _)))

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (by omega : Nat.log p n < Nat.log p n + 2)]
  have h₁ : 1 ∈ Ico 1 (Nat.log p n + 2) := by simp
  simpa using single_le_sum (f := fun i ↦ n / p ^ i) (fun _ _ ↦ Nat.zero_le _) h₁

private lemma factorization_factorial_of_lt_sq {p n : ℕ} (hp : p.Prime) (h : n < p ^ 2) :
    n.factorial.factorization p = n / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' two_ne_zero h)]
  simp

private lemma log_count_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log (σ 0 n : ℝ) = ∑ p ∈ n.primeFactors, Real.log (n.factorization p + 1 : ℝ) := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn]
  push_cast
  rw [Real.log_prod (fun _ _ ↦ by positivity)]

private lemma gain_eq_sum {x : ℕ} (hx : 0 < x) :
    gain x = ∑ p ∈ x.primeFactors,
      (Real.log (1 + (x.factorization p : ℝ) / ((x - 1).factorial.factorization p + 1))) := by
  let P := x.factorial.primeFactors
  have hmul : x.factorial = x * (x - 1).factorial := by
    cases x with
    | zero => omega
    | succ x => simpa using Nat.factorial_succ x
  have hfact (p : ℕ) : x.factorial.factorization p =
      x.factorization p + (x - 1).factorial.factorization p := by
    nth_rw 1 [hmul]
    rw [Nat.factorization_mul (Nat.ne_of_gt hx) (Nat.factorial_ne_zero _)]
    rfl
  have hsub : (x - 1).factorial.primeFactors ⊆ P :=
    Nat.primeFactors_mono (Nat.factorial_dvd_factorial (Nat.sub_le x 1)) (Nat.factorial_ne_zero _)
  have hxsub : x.primeFactors ⊆ P :=
    Nat.primeFactors_mono (hmul ▸ dvd_mul_right x (x - 1).factorial) (Nat.factorial_ne_zero _)
  have hs : (∑ p ∈ (x - 1).factorial.primeFactors,
      Real.log ((x - 1).factorial.factorization p + 1 : ℝ)) =
      ∑ p ∈ P, Real.log ((x - 1).factorial.factorization p + 1 : ℝ) := by
    refine sum_subset hsub fun p _ hp ↦ ?_
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [hp]
  rw [gain, L, L, log_count_factorization _ (Nat.factorial_ne_zero _),
    log_count_factorization _ (Nat.factorial_ne_zero _), hs, ← sum_sub_distrib]
  rw [sum_subset hxsub (fun p _ hp ↦ ?_)]
  · refine sum_congr rfl fun p _ ↦ ?_
    rw [← Real.log_div (by positivity) (by positivity), hfact]
    push_cast
    congr 1
    field_simp
    ring
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [hp]

private lemma factorization_single_of_large {p x : ℕ} (hx : x ≠ 0) (hp : p.Prime)
    (hd : p ∣ x) (hlarge : x < p ^ 2) : x.factorization p = 1 := by
  have hpos := (hp.dvd_iff_one_le_factorization hx).mp hd
  have hlt : x.factorization p < 2 := by
    by_contra! hh
    exact (not_le_of_gt hlarge) (Nat.le_of_dvd (Nat.pos_of_ne_zero hx)
      ((hp.pow_dvd_iff_le_factorization hx).2 hh))
  omega

private lemma div_sub_eq {x p a : ℕ} (hx : 0 < x) (hp : 0 < p) (ha : x = p * a) :
    (x - 1) / p + 1 = a := by
  have hlo : (a - 1) * p ≤ x - 1 := by
    rw [Nat.sub_mul, Nat.one_mul, mul_comm a p, ← ha]
    omega
  have hhi : x - 1 < a * p := by rw [mul_comm, ← ha]; omega
  have h₁ := (Nat.le_div_iff_mul_le hp).2 hlo
  have h₂ := (Nat.div_lt_iff_lt_mul hp).2 hhi
  omega

private lemma denom_lower {x p : ℕ} (hx : 0 < x) (hp : p.Prime) (hd : p ∣ x) :
    (x : ℝ) / p ≤ ((x - 1).factorial.factorization p : ℝ) + 1 := by
  obtain ⟨a, ha⟩ := hd
  have hxdiv : (x : ℝ) / p = a := by
    rw [ha, Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hp.ne_zero)
  rw [hxdiv, ← div_sub_eq hx hp.pos ha, Nat.cast_add, Nat.cast_one]
  gcongr
  exact_mod_cast div_le_factorization_factorial hp (x - 1)

private lemma gain_prime_term {x p : ℕ} (hx : 0 < x) (hp : p.Prime) (hd : p ∣ x)
    (hlarge : x < p ^ 2) :
    Real.log (1 + (x.factorization p : ℝ) / ((x - 1).factorial.factorization p + 1)) =
      Real.log (1 + (p : ℝ) / x) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [factorization_single_of_large (Nat.ne_of_gt hx) hp hd hlarge,
    factorization_factorial_of_lt_sq hp (lt_of_le_of_lt (Nat.sub_le _ _) hlarge)]
  obtain ⟨a, ha⟩ := hd
  rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, div_sub_eq hx hp.pos ha, ha, Nat.cast_mul]
  rw [div_mul_cancel_left₀ hpR.ne', Nat.cast_one, one_div]

private lemma sum_factorization_le (x : ℕ) :
    ∑ p ∈ x.primeFactors, (x.factorization p : ℝ) ≤ 2 * Real.log x := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have h : (∑ p ∈ x.primeFactors, (x.factorization p : ℝ)) * (1 / 2) ≤ Real.log x := by
    conv_rhs => rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    rw [sum_mul]
    apply sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hlog2.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le))
  linarith

private theorem gain_bounds {x : ℕ} (hx : 0 < x) :
    primeGain x ≤ gain x ∧ gain x ≤ primeGain x + 2 * Real.log x / Real.sqrt x := by
  let f (p : ℕ) : ℝ :=
    Real.log (1 + (x.factorization p : ℝ) / ((x - 1).factorial.factorization p + 1))
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hbig : (∑ p ∈ x.primeFactors with x < p ^ 2, f p) = primeGain x := by
    unfold primeGain
    refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_filter, Nat.mem_primeFactors] at hp
    exact gain_prime_term hx hp.1.1 hp.1.2.1 hp.2
  have hsmall : (∑ p ∈ x.primeFactors with ¬x < p ^ 2, f p)
      ≤ 2 * Real.log x / Real.sqrt x := by
    have hsqrt := Real.sqrt_pos.2 hxR
    calc
      _ ≤ ∑ p ∈ x.primeFactors with ¬x < p ^ 2, (x.factorization p : ℝ) / Real.sqrt x := by
        apply sum_le_sum
        intro p hp
        rw [mem_filter, Nat.mem_primeFactors, not_lt] at hp
        have hpR : (0 : ℝ) < p := by exact_mod_cast hp.1.1.pos
        have hpsq : (p : ℝ) ^ 2 ≤ x := by exact_mod_cast hp.2
        have hps : (p : ℝ) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt hxR.le]
        have hden : Real.sqrt x ≤ ((x - 1).factorial.factorization p : ℝ) + 1 := by
          refine le_trans ?_ (denom_lower hx hp.1.1 hp.1.2.1)
          rw [le_div_iff₀ hpR]
          exact (mul_le_mul_of_nonneg_left hps hsqrt.le).trans_eq (Real.mul_self_sqrt hxR.le)
        let z : ℝ := (x.factorization p : ℝ) / ((x - 1).factorial.factorization p + 1)
        have hz : Real.log (1 + z) ≤ z := by
          have h := Real.log_le_sub_one_of_pos (x := 1 + z) (by dsimp [z]; positivity)
          linarith
        exact hz.trans (div_le_div_of_nonneg_left (by positivity) hsqrt hden)
      _ ≤ ∑ p ∈ x.primeFactors, (x.factorization p : ℝ) / Real.sqrt x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by
        rw [← sum_div]
        exact div_le_div_of_nonneg_right (sum_factorization_le x) hsqrt.le
  have hsmall0 : 0 ≤ (∑ p ∈ x.primeFactors with ¬x < p ^ 2, f p) := by
    apply sum_nonneg
    intro p _
    apply Real.log_nonneg
    exact le_add_of_nonneg_right (by positivity)
  rw [gain_eq_sum hx]
  change _ ≤ ∑ p ∈ x.primeFactors, f p ∧ (∑ p ∈ x.primeFactors, f p) ≤ _
  rw [← sum_filter_add_sum_filter_not _ (fun p ↦ x < p ^ 2), hbig]
  constructor <;> linarith


private noncomputable def window (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊

private noncomputable def endpoint (n : ℕ) : ℕ := n + window n

private noncomputable def error (x : ℕ) : ℝ := 2 * Real.log x / Real.sqrt x

private noncomputable def score (n : ℕ) : ℝ := Real.log (Erdos420.F (fun x ↦ Real.log x) n)

private lemma primeGain_nonneg (x : ℕ) : 0 ≤ primeGain x := by
  unfold primeGain
  exact sum_nonneg fun _ _ ↦ Real.log_nonneg (le_add_of_nonneg_right (by positivity))

private lemma sum_backward_difference {a b : ℕ} (h : a ≤ b) (f : ℕ → ℝ) :
    ∑ x ∈ Ioc a b, (f x - f (x - 1)) = f b - f a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top hab, ih]
    simp

private lemma sum_gain {a b : ℕ} (h : a ≤ b) :
    ∑ x ∈ Ioc a b, gain x = L b - L a :=
  sum_backward_difference h L

private lemma score_eq_sum (n : ℕ) : score n = ∑ x ∈ Ioc n (endpoint n), gain x := by
  have hpos (y : ℕ) : 0 < (σ 0 y.factorial : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero y)
  rw [sum_gain (b := endpoint n) (Nat.le_add_right _ _)]
  exact Real.log_div (hpos (endpoint n)).ne' (hpos n).ne'

private lemma error_nonneg (x : ℕ) : 0 ≤ error x :=
  div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) (Real.sqrt_nonneg _)

private lemma error_tendsto : Tendsto error atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1/2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have h' := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h'' := h'.const_mul (2 : ℝ)
  unfold error
  simpa [Real.sqrt_eq_rpow, mul_div_assoc] using h''

private lemma window_mono : Monotone window := by
  intro a b hab
  apply Nat.floor_mono
  by_cases ha : a = 0
  · subst a
    simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha) (by exact_mod_cast hab)

private lemma endpoint_mono : Monotone endpoint :=
  fun _ _ h ↦ Nat.add_le_add h (window_mono h)

private lemma window_le (n : ℕ) : window n ≤ n := by
  cases n with
  | zero => simp [window]
  | succ n =>
    apply Nat.floor_le_of_le
    have h := Real.log_le_sub_one_of_pos (x := ((n + 1 : ℕ) : ℝ)) (by positivity)
    linarith

private lemma window_tendsto : Tendsto window atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma endpoint_succ_le (n : ℕ) : endpoint (n + 1) ≤ endpoint n + 2 := by
  have hwin : window (n + 1) ≤ window n + 1 := by
    cases n with
    | zero => simp [window]
    | succ n =>
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlog : Real.log (((n + 1) + 1 : ℕ) : ℝ) <
          Real.log (n + 1 : ℕ) + 1 := by
        have harg : 1 < (((n + 1) + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          rw [one_lt_div hn]
          push_cast
          linarith
        have harg' : (((n + 1) + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hn]
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) n]
        have hl := Real.log_lt_sub_one_of_pos (x :=
          (((n + 1) + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) (by positivity) (ne_of_gt harg)
        rw [Real.log_div (by positivity) hn.ne'] at hl
        linarith
      apply Nat.le_of_lt_succ
      apply (Nat.floor_lt (Real.log_natCast_nonneg _)).2
      have hf : Real.log (n + 1 : ℕ) < (window (n + 1) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (show Real.log (((n + 1) + 1 : ℕ) : ℝ) < (window (n + 1) : ℝ) + 1 + 1 by linarith)
  unfold endpoint
  omega

private lemma large_prime_card (x : ℕ) :
    (x.primeFactors.filter (fun p ↦ x < p ^ 2)).card ≤ 1 := by
  apply card_le_one_iff.mpr
  intro p q hp hq
  by_contra hne
  rw [mem_filter, Nat.mem_primeFactors] at hp hq
  have hcop := (Nat.coprime_primes hp.1.1 hq.1.1).2 hne
  have hpq : p * q ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hp.1.2.2)
    (hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1)
  rcases le_total p q with h | h
  · exact (not_le_of_gt hp.2) ((by simpa [pow_two] using Nat.mul_le_mul_left p h :
      p ^ 2 ≤ p * q).trans hpq)
  · exact (not_le_of_gt hq.2) ((by simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q h :
      q ^ 2 ≤ p * q).trans hpq)

private lemma primeGain_le_of_no_small {x K : ℕ} (hK : 0 < K)
    (h : ∀ p d : ℕ, p.Prime → x < p ^ 2 → x = d * p → K < d) :
    primeGain x ≤ 1 / (K : ℝ) := by
  unfold primeGain
  calc
    _ ≤ ∑ _p ∈ x.primeFactors with x < _p ^ 2, (1 / (K : ℝ)) := by
      apply sum_le_sum
      intro p hp
      rw [mem_filter, Nat.mem_primeFactors] at hp
      obtain ⟨d, hd⟩ := hp.1.2.1
      rw [mul_comm] at hd
      have hdK := h p d hp.1.1 hp.2 hd
      have hratio : (p : ℝ) / x = 1 / d := by
        rw [hd, Nat.cast_mul, mul_comm (d : ℝ), div_mul_cancel_left₀ (by exact_mod_cast hp.1.1.ne_zero : (p : ℝ) ≠ 0)]
        exact (one_div _).symm
      rw [hratio]
      have hlog := Real.log_le_sub_one_of_pos (x := 1 + 1 / (d : ℝ)) (by positivity)
      have hfrac : 1 / (d : ℝ) ≤ 1 / (K : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hK) (by exact_mod_cast hdK.le)
      linarith
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      calc _ ≤ (1 : ℝ) * (1 / (K : ℝ)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast large_prime_card x) (by positivity)
           _ = _ := one_mul _

private lemma primeGain_mul_ge {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (hkp : k < p) :
    Real.log (1 + 1 / (k : ℝ)) ≤ primeGain (k * p) := by
  have hmem : p ∈ (k * p).primeFactors.filter (fun q ↦ k * p < q ^ 2) := by
    rw [mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hp, dvd_mul_left p k, Nat.mul_ne_zero hk.ne' hp.ne_zero⟩, ?_⟩
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_right hkp hp.pos
  have h := single_le_sum (f := fun q : ℕ ↦ Real.log (1 + (q : ℝ) / (↑(k * p) : ℝ)))
    (fun _ _ ↦ Real.log_nonneg (le_add_of_nonneg_right (by positivity))) hmem
  have hratio : (p : ℝ) / (↑(k * p) : ℝ) = 1 / k := by
    rw [Nat.cast_mul, mul_comm (k : ℝ), div_mul_cancel_left₀ (by exact_mod_cast hp.ne_zero : (p : ℝ) ≠ 0)]
    exact (one_div _).symm
  rwa [hratio] at h

private lemma window_error_tendsto :
    Tendsto (fun n ↦ ∑ x ∈ Ioc n (endpoint n), error x) atTop (𝓝 0) := by
  have hlimit :
      Tendsto (fun n : ℕ ↦ 4 * (Real.log n)^2 / Real.sqrt n) atTop (𝓝 0) := by
    have haux := isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1/2)
    have h := haux.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Real.sqrt_eq_rpow, Real.rpow_natCast, mul_div_assoc] using h.const_mul (4 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall fun n ↦ sum_nonneg fun x _ ↦ error_nonneg x) ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hsqrt := Real.sqrt_pos.2 hnR
  calc
    _ ≤ ∑ _x ∈ Ioc n (endpoint n), 4 * Real.log n / Real.sqrt n := by
      apply sum_le_sum
      intro x hx
      rw [mem_Ioc] at hx
      have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
      have hxle : (x : ℝ) ≤ 2 * (n : ℝ) := by
        have hw := window_le n
        have h : x ≤ 2 * n := by unfold endpoint at hx; omega
        exact_mod_cast h
      have hlog : Real.log x ≤ 2 * Real.log n := by
        have h := Real.log_le_log hxR hxle
        rw [Real.log_mul (by norm_num) hnR.ne'] at h
        have h2 := Real.log_le_log (x := 2) (y := (n : ℝ)) (by norm_num) (by exact_mod_cast hn)
        linarith
      have hsn : Real.sqrt n ≤ Real.sqrt x := Real.sqrt_le_sqrt (by exact_mod_cast hx.1.le)
      unfold error
      refine (div_le_div_of_nonneg_left (by positivity) hsqrt hsn).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) hsqrt.le
    _ = (window n : ℝ) * (4 * Real.log n / Real.sqrt n) := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Ioc]
      simp [endpoint]
    _ ≤ _ := by
      calc
        _ ≤ Real.log n * (4 * Real.log n / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hlogn) (by positivity)
        _ = _ := by ring


private lemma score_succ_le (n : ℕ) :
    score (n + 1) ≤ score n + ∑ x ∈ Ioc (endpoint n) (endpoint (n + 1)), gain x := by
  rw [score_eq_sum, score_eq_sum, sum_gain (b := endpoint (n + 1)) (Nat.le_add_right _ _),
    sum_gain (b := endpoint n) (Nat.le_add_right _ _), sum_gain (endpoint_mono (Nat.le_succ _))]
  have h := gain_nonneg (n + 1)
  simp [gain] at h
  linarith

private lemma endpoint_bracket {T U : ℕ} (hT : 0 < T) (hU : T ≤ endpoint U) :
    ∃ j, j + 1 ≤ U ∧ endpoint j < T ∧ T ≤ endpoint (j + 1) := by
  classical
  have hex : ∃ n, T ≤ endpoint n := ⟨U, hU⟩
  have hmin := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hmin
    have hzero : endpoint 0 = 0 := by simp [endpoint, window]
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨j, ?_, ?_, ?_⟩
  · have h := Nat.find_min' hex hU
    omega
  · exact not_le.1 (Nat.find_min hex (by omega))
  · simpa [← Nat.succ_eq_add_one, ← hj] using hmin

private lemma endpoint_window_brackets {A B : ℕ} (hB : 0 < B) (hw : B ≤ window A) :
    ∃ n₀ n₁ : ℕ, n₀ < n₁ ∧ n₁ ≤ A ∧ A - 1 ≤ endpoint n₀ ∧ endpoint n₀ ≤ A ∧
      A + B ≤ endpoint n₁ ∧ endpoint n₁ ≤ A + B + 1 := by
  obtain ⟨n₀, _, hlo₀, hhi₀⟩ :=
    endpoint_bracket (T := A + 1) (U := A + 1) (by omega) (Nat.le_add_right _ _)
  obtain ⟨j, hjA, hloj, hhij⟩ := endpoint_bracket (T := A + B) (U := A) (by omega)
    (by unfold endpoint; omega)
  have h₀ := endpoint_succ_le n₀
  have h₁ := endpoint_succ_le j
  have hlt : n₀ < j + 1 := by
    by_contra! h
    have hh := endpoint_mono h
    omega
  exact ⟨n₀, j + 1, hlt, hjA, by omega, by omega, hhij, by omega⟩

private lemma score_upper {n a b : ℕ} (ha : a ≤ n) (hb : endpoint n ≤ b) :
    score n ≤ (∑ x ∈ Ioc a b, primeGain x) + (∑ x ∈ Ioc n (endpoint n), error x) := by
  rw [score_eq_sum]
  have h : (∑ x ∈ Ioc n (endpoint n), gain x) ≤
      ∑ x ∈ Ioc n (endpoint n), (primeGain x + error x) := by
    apply sum_le_sum
    intro x hx
    rw [mem_Ioc] at hx
    exact (gain_bounds (show 0 < x by omega)).2
  rw [sum_add_distrib] at h
  refine h.trans (add_le_add_left ?_ _)
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ ↦ primeGain_nonneg x)
  intro x hx
  rw [mem_Ioc] at hx ⊢
  omega

private lemma score_lower_of_prime_offsets {k u n B : ℕ} (b : Finset ℕ)
    (hk : 0 < k) (hku : k < u) (hn : n ≤ k * u) (hend : k * u + B ≤ endpoint n)
    (hb : ∀ j ∈ b, 0 < j ∧ k * j ≤ B) :
    ((b.filter (fun j ↦ (u + j).Prime)).card : ℝ) * Real.log (1 + 1 / (k : ℝ)) ≤ score n := by
  classical
  let S := b.filter (fun j ↦ (u + j).Prime)
  let e : ℕ ↪ ℕ := ⟨fun j ↦ k * (u + j), fun i j h ↦
    Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left hk h)⟩
  rw [score_eq_sum]
  calc
    _ = ∑ _j ∈ S, Real.log (1 + 1 / (k : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ S, gain (e j) := by
      apply sum_le_sum
      intro j hj
      rw [mem_filter] at hj
      have hp := primeGain_mul_ge hk hj.2 (show k < u + j by omega)
      exact hp.trans (gain_bounds (Nat.mul_pos hk hj.2.pos)).1
    _ = ∑ x ∈ S.map e, gain x := (sum_map S e gain).symm
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ ↦ gain_nonneg x)
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hx
      rw [mem_filter] at hj
      rw [mem_Ioc]
      change n < k * (u + j) ∧ k * (u + j) ≤ endpoint n
      rw [Nat.mul_add]
      obtain ⟨hjp, hjB⟩ := hb j hj.1
      have hkj := Nat.mul_pos hk hjp
      omega

private lemma first_crossing {n₀ n₁ : ℕ} {y δ : ℝ} (hle : n₀ ≤ n₁)
    (hlo : score n₀ < y) (hhi : y ≤ score n₁)
    (hj : ∀ j, n₀ ≤ j → j < n₁ → score (j + 1) ≤ score j + δ) :
    ∃ n, y ≤ score n ∧ score n < y + δ := by
  classical
  have hex : ∃ n, n₀ ≤ n ∧ y ≤ score n := ⟨n₁, hle, hhi⟩
  let n := Nat.find hex
  have hn : n₀ ≤ n ∧ y ≤ score n := Nat.find_spec hex
  have hmax : n ≤ n₁ := Nat.find_min' hex ⟨hle, hhi⟩
  have hn₀ : n₀ < n := by
    by_contra! hh
    have heq : n = n₀ := by omega
    rw [heq] at hn
    exact (not_le_of_gt hlo) hn.2
  have hpred : score (n - 1) < y := by
    refine lt_of_not_ge fun hc ↦ ?_
    exact Nat.find_min hex (show n - 1 < n by omega) ⟨by omega, hc⟩
  have h := hj (n - 1) (by omega) (by omega)
  rw [show n - 1 + 1 = n by omega] at h
  exact ⟨n, hn.2, by linarith⟩

private lemma jump_upper {A B n₀ n₁ K j : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 < K) (h₂ : 2 * (1 / (K : ℝ) + δ) ≤ 4 * δ)
    (hstart : A - 1 ≤ endpoint n₀) (hfinish : endpoint n₁ ≤ A + B + 1)
    (hlo : n₀ ≤ j) (hhi : j < n₁)
    (hA : 0 < A) (herr : ∀ x ≥ A, error x ≤ δ)
    (hsmall : ∀ x ∈ Icc A (A + B + 1),
      ∀ p d : ℕ, p.Prime → x < p ^ 2 → x = d * p → K < d) :
    score (j + 1) ≤ score j + 4 * δ := by
  refine (score_succ_le j).trans (add_le_add_right ?_ _)
  calc
    _ ≤ ∑ _x ∈ Ioc (endpoint j) (endpoint (j + 1)), (1 / (K : ℝ) + δ) := by
      apply sum_le_sum
      intro x hx
      rw [mem_Ioc] at hx
      have h₀ := endpoint_mono hlo
      have h₁ := endpoint_mono (show j + 1 ≤ n₁ by omega)
      have hx' : x ∈ Icc A (A + B + 1) := by
        rw [mem_Icc]
        omega
      have hxA : A ≤ x := (mem_Icc.1 hx').1
      exact (gain_bounds (hA.trans_le hxA)).2.trans
        (add_le_add (primeGain_le_of_no_small hK (hsmall x hx')) (herr x hxA))
    _ ≤ 2 * (1 / (K : ℝ) + δ) := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Ioc]
      have h := endpoint_succ_le j
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show endpoint (j + 1) - endpoint j ≤ 2 by omega)
    _ ≤ _ := h₂


private def Admissible (b : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ j ∈ b, ¬ p ∣ a + j

private def ModulusOK (b : Finset ℕ) (X M a : ℕ) : Prop :=
  0 < M ∧ a < M ∧ Squarefree M ∧ (M : ℝ) ≤ (X : ℝ) ^ (1 / 64 : ℝ) ∧
    (∀ q ∈ M.primeFactors, (q : ℝ) ≤ Real.log X / 2) ∧
    ∀ j ∈ b, (a + j).Coprime M

private def anchors (X M a : ℕ) : Finset ℕ :=
  (Icc X (2 * X)).filter (fun u ↦ u % M = a)

private noncomputable def roughAnchors (b : Finset ℕ) (ρ : ℝ) (X M a : ℕ) : Finset ℕ := by
  classical
  exact (anchors X M a).filter (fun u ↦
    ∀ j ∈ b, ∀ p ∈ (u + j).primeFactors, (X : ℝ) ^ ρ < (p : ℝ))

private noncomputable def goodAnchors (b : Finset ℕ) (ρ : ℝ) (m X M a : ℕ) : Finset ℕ :=
  (roughAnchors b ρ X M a).filter (fun u ↦ m ≤ (b.filter (fun j ↦ (u + j).Prime)).card)

private noncomputable def scale (b : Finset ℕ) (X M : ℕ) : ℝ :=
  (X : ℝ) / ((M : ℝ) * (1 + Real.log X) ^ b.card)

private noncomputable def span (k X : ℕ) : ℕ := window (4 * k * X) + 1

private noncomputable def lowCut (b : Finset ℕ) (X : ℕ) : ℕ :=
  ⌊(Real.log (Real.log (X : ℝ))) ^ (b.card + 3)⌋₊ + 1

private noncomputable def highCut (X : ℕ) : ℕ := ⌊(Real.log (X : ℝ)) ^ 2⌋₊ + 1

private noncomputable def leftWindow (k X u : ℕ) : Finset ℕ :=
  Ioc (k * u - span k X) (k * u)

private def HasCofactor (x d : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x < p ^ 2 ∧ x = d * p

private noncomputable def pairCount (b : Finset ℕ) (ρ : ℝ) (k X M a d : ℕ) : ℕ := by
  classical
  exact ∑ u ∈ roughAnchors b ρ X M a,
    ((leftWindow k X u).filter (fun x ↦ HasCofactor x d)).card

private def Covered (M K x : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ K < q ∧ q ^ 2 < x ∧ q ∣ x

/-- Quantitative Maynard clusters with rough detectors in a growing progression. -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m → ∃ b : Finset ℕ, Admissible b ∧ (∀ j ∈ b, 0 < j) ∧
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ᶠ X : ℕ in atTop, ∀ M a : ℕ,
      ModulusOK b X M a → c * scale b X M ≤ (goodAnchors b ρ m X M a).card

/-- A uniform upper sieve for rough detectors and a prime quotient to their left. -/
def H2 : Prop :=
  ∀ (b : Finset ℕ), (∀ j ∈ b, 0 < j) →
    ∀ (k : ℕ), 0 < k → ∀ ρ η : ℝ, 0 < ρ → 0 < η →
      ∀ᶠ X : ℕ in atTop, ∀ M a : ℕ, ModulusOK b X M a →
        ∀ d ∈ Ioc (lowCut b X) (highCut X),
          (pairCount b ρ k X M a d : ℝ) ≤
            η * scale b X M * ((lowCut b X : ℝ) / d + 1 / (1 + Real.log (highCut X)))

/-- A covering progression preserving the detector offsets. -/
def H3 : Prop :=
  ∀ (b : Finset ℕ), Admissible b → (∀ j ∈ b, 0 < j) →
    ∀ (k : ℕ), 0 < k → ∀ K B : ℕ, (∀ j ∈ b, k * j ≤ B) →
      ∀ᶠ X : ℕ in atTop, ∃ M a : ℕ, ModulusOK b X M a ∧
        ∀ u ∈ anchors X M a,
          (∀ x ∈ leftWindow k X u, Covered M (lowCut b X) x) ∧
          (∀ x ∈ Icc (k * u) (k * u + B + 1),
            (∀ j ∈ b, x ≠ k * (u + j)) → Covered M K x)

lemma cofactor_gt_of_cover {M K x d : ℕ} (hcover : Covered M K x)
    (h : HasCofactor x d) : K < d := by
  obtain ⟨q, hq, _, hKq, hqx, hqd⟩ := hcover
  obtain ⟨p, hp, hpbig, hxp⟩ := h
  have hne : q ≠ p := by
    intro heq
    subst q
    omega
  rw [hxp] at hqd
  have hd : q ∣ d := (hq.dvd_mul.mp hqd).resolve_right
    (fun hqp ↦ hne ((Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one))
  have hx : 0 < x := (Nat.zero_le _).trans_lt hqx
  have hd0 : 0 < d := by
    by_contra! hn
    have hdz : d = 0 := by omega
    simp [hdz] at hxp
    omega
  exact hKq.trans_le (Nat.le_of_dvd hd0 hd)

private noncomputable def cofactorMass (L D x : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ Ioc L D, if HasCofactor x d then 1 / (d : ℝ) else 0

private noncomputable def truncatedTail (L D k X u : ℕ) : ℝ :=
  ∑ x ∈ leftWindow k X u, cofactorMass L D x

private lemma cofactorMass_nonneg (L D x : ℕ) : 0 ≤ cofactorMass L D x := by
  unfold cofactorMass
  exact sum_nonneg fun _ _ ↦ by split <;> positivity

private lemma primeGain_le_cofactorMass {L D x M : ℕ} (hD : 0 < D) (hcover : Covered M L x) :
    primeGain x ≤ cofactorMass L D x + 1 / (D : ℝ) := by
  classical
  let P := x.primeFactors.filter (fun p ↦ x < p ^ 2)
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp⟩ := hP
    have hsing : P = {p} := eq_singleton_iff_unique_mem.mpr
      ⟨hp, fun q hq ↦ card_le_one_iff.mp (large_prime_card x) hq hp⟩
    change p ∈ x.primeFactors.filter (fun q ↦ x < q ^ 2) at hp
    rw [mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨d, hd⟩ := hp.1.2.1
    rw [mul_comm] at hd
    have hhas : HasCofactor x d := ⟨p, hp.1.1, hp.2, hd⟩
    have hdL := cofactor_gt_of_cover hcover hhas
    have hratio : (p : ℝ) / x = 1 / d := by
      rw [hd, Nat.cast_mul, mul_comm (d : ℝ),
        div_mul_cancel_left₀ (by exact_mod_cast hp.1.1.ne_zero : (p : ℝ) ≠ 0), one_div]
    have hlog : primeGain x ≤ 1 / (d : ℝ) := by
      change (∑ q ∈ P, Real.log (1 + (q : ℝ) / x)) ≤ _
      rw [hsing, sum_singleton, hratio]
      have h := Real.log_le_sub_one_of_pos (x := 1 + 1 / (d : ℝ)) (by positivity)
      linarith
    by_cases hdD : d ≤ D
    · have hterm : 1 / (d : ℝ) ≤ cofactorMass L D x := by
        unfold cofactorMass
        have h := single_le_sum
          (f := fun j : ℕ ↦ if HasCofactor x j then 1 / (j : ℝ) else 0)
          (fun j (_ : j ∈ Ioc L D) ↦ by split <;> positivity)
          (mem_Ioc.mpr ⟨hdL, hdD⟩)
        simpa [hhas] using h
      exact hlog.trans (hterm.trans (le_add_of_nonneg_right (by positivity)))
    · have hterm : 1 / (d : ℝ) ≤ 1 / (D : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hD) (by exact_mod_cast (by omega : D ≤ d))
      exact hlog.trans (hterm.trans (le_add_of_nonneg_left (cofactorMass_nonneg L D x)))
  · have hP' : P = ∅ := not_nonempty_iff_eq_empty.mp hP
    change (∑ p ∈ P, Real.log (1 + (p : ℝ) / x)) ≤ _
    rw [hP', sum_empty]
    exact add_nonneg (cofactorMass_nonneg L D x) (by positivity)

private lemma tail_upper {L D k X u M : ℕ} (hD : 0 < D)
    (hcover : ∀ x ∈ leftWindow k X u, Covered M L x) :
    (∑ x ∈ leftWindow k X u, primeGain x) ≤
      truncatedTail L D k X u + (span k X : ℝ) / D := by
  calc
    _ ≤ ∑ x ∈ leftWindow k X u, (cofactorMass L D x + 1 / (D : ℝ)) :=
      sum_le_sum (fun x hx ↦ primeGain_le_cofactorMass hD (hcover x hx))
    _ ≤ _ := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      unfold truncatedTail
      refine add_le_add_right ?_ _
      simp only [div_eq_mul_inv, one_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold leftWindow
      rw [Nat.card_Ioc]
      exact_mod_cast (show k * u - (k * u - span k X) ≤ span k X by omega)

private lemma sum_truncatedTail_eq (b : Finset ℕ) (ρ : ℝ) (L D k X M a : ℕ) :
    (∑ u ∈ roughAnchors b ρ X M a, truncatedTail L D k X u) =
      ∑ d ∈ Ioc L D, (pairCount b ρ k X M a d : ℝ) * (1 / (d : ℝ)) := by
  classical
  let U := roughAnchors b ρ X M a
  calc
    _ = ∑ u ∈ U, ∑ d ∈ Ioc L D, ∑ x ∈ leftWindow k X u,
          if HasCofactor x d then 1 / (d : ℝ) else 0 := by
      apply sum_congr rfl
      intro u _
      unfold truncatedTail cofactorMass
      rw [sum_comm]
    _ = ∑ d ∈ Ioc L D, ∑ u ∈ U, ∑ x ∈ leftWindow k X u,
          if HasCofactor x d then 1 / (d : ℝ) else 0 := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d _
      unfold pairCount
      rw [Nat.cast_sum, sum_mul]
      apply sum_congr rfl
      intro u _
      rw [← sum_filter, sum_const, nsmul_eq_mul]

private lemma pair_weight_sum {L D : ℕ} (hL : 0 < L) :
    (∑ d ∈ Ioc L D, ((L : ℝ) / d + 1 / (1 + Real.log D)) * (1 / d)) ≤ 2 := by
  have hlog : 0 < 1 + Real.log (D : ℝ) := by linarith [Real.log_natCast_nonneg D]
  have hterm (d : ℕ) :
      ((L : ℝ) / d + 1 / (1 + Real.log D)) * (1 / d) =
        (L : ℝ) * ((d : ℝ)^2)⁻¹ + (1 + Real.log D)⁻¹ * (d : ℝ)⁻¹ := by
    rw [one_div, one_div, add_mul, div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc]
  simp_rw [hterm, sum_add_distrib, ← mul_sum]
  have hsq : (∑ d ∈ Ioc L D, ((d : ℝ)^2)⁻¹) ≤ (L : ℝ)⁻¹ := by
    by_cases hLD : L ≤ D
    · calc
        _ ≤ ∑ d ∈ Ioc L D, (- (d : ℝ)⁻¹ - (- ((d - 1 : ℕ) : ℝ)⁻¹)) := by
          apply sum_le_sum
          intro d hd
          have hd₀ := (mem_Ioc.mp hd).1
          have hdn : 0 < d - 1 := by omega
          have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
          have hdp' : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hdn
          have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
            rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
          have hpos' : 0 < (d : ℝ) - 1 := hcast ▸ hdp'
          rw [hcast]
          field_simp [hdp.ne', hpos'.ne']
          nlinarith
        _ = - (D : ℝ)⁻¹ - (- (L : ℝ)⁻¹) :=
          sum_backward_difference hLD (fun d ↦ - (d : ℝ)⁻¹)
        _ ≤ _ := by linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) D)]
    · rw [Ioc_eq_empty (by omega), sum_empty]
      positivity
  have hharm : (∑ d ∈ Ioc L D, (d : ℝ)⁻¹) ≤ 1 + Real.log D := by
    by_cases hLD : L ≤ D
    · calc
        _ ≤ ∑ d ∈ Ioc L D, (Real.log d - Real.log (d - 1 : ℕ)) := by
          apply sum_le_sum
          intro d hd
          have hd₀ := (mem_Ioc.mp hd).1
          have hdn : 0 < d - 1 := by omega
          have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
          have hdp' : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hdn
          have h := Real.one_sub_inv_le_log_of_pos (div_pos hdp hdp')
          rw [Real.log_div hdp.ne' hdp'.ne', inv_div,
            Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one] at h
          have heq : 1 - ((d : ℝ) - 1) / d = (d : ℝ)⁻¹ := by
            field_simp
            ring
          rwa [heq, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub (show 1 ≤ d by omega)] at h
        _ = Real.log D - Real.log L := sum_backward_difference hLD (fun d ↦ Real.log d)
        _ ≤ _ := by linarith [Real.log_natCast_nonneg L]
    · rw [Ioc_eq_empty (by omega), sum_empty]
      exact hlog.le
  calc
    _ ≤ (L : ℝ) * (L : ℝ)⁻¹ + (1 + Real.log D)⁻¹ * (1 + Real.log D) :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity))
        (mul_le_mul_of_nonneg_left hharm (by positivity))
    _ = _ := by
      have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [mul_inv_cancel₀ hLR, inv_mul_cancel₀ hlog.ne']
      ring

private lemma scale_pos {b : Finset ℕ} {X M : ℕ} (hX : 0 < X) (hM : 0 < M) :
    0 < scale b X M := by
  unfold scale
  have h : 0 < 1 + Real.log (X : ℝ) := by linarith [Real.log_natCast_nonneg X]
  positivity

private lemma find_good_anchor {b : Finset ℕ} {ρ c δ : ℝ} {m k X M a : ℕ}
    (hc : 0 < c) (hδ : 0 < δ) (hX : 0 < X) (hM : 0 < M)
    (hmany : c * scale b X M ≤ (goodAnchors b ρ m X M a).card)
    (hpair : ∀ d ∈ Ioc (lowCut b X) (highCut X),
      (pairCount b ρ k X M a d : ℝ) ≤
        (c * δ / 4) * scale b X M * ((lowCut b X : ℝ) / d + 1 / (1 + Real.log (highCut X)))) :
    ∃ u ∈ goodAnchors b ρ m X M a, truncatedTail (lowCut b X) (highCut X) k X u < δ := by
  classical
  let L := lowCut b X
  let D := highCut X
  let S := goodAnchors b ρ m X M a
  let T := truncatedTail L D k X
  have hS : S ⊆ roughAnchors b ρ X M a := filter_subset _ _
  have hnorm := scale_pos (b := b) hX hM
  have hη : 0 ≤ (c * δ / 4) * scale b X M := by positivity
  change ∃ u ∈ S, T u < δ
  by_contra! hall
  have hlo : c * scale b X M * δ ≤ ∑ u ∈ S, T u := by
    calc
      _ ≤ (S.card : ℝ) * δ := mul_le_mul_of_nonneg_right hmany hδ.le
      _ = ∑ _u ∈ S, δ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hall
  have hupper : (∑ u ∈ S, T u) ≤ ((c * δ / 4) * scale b X M) * 2 := by
    calc
      _ ≤ ∑ u ∈ roughAnchors b ρ X M a, T u :=
        sum_le_sum_of_subset_of_nonneg hS
          (fun u _ _ ↦ sum_nonneg (fun x _ ↦ cofactorMass_nonneg L D x))
      _ = ∑ d ∈ Ioc L D, (pairCount b ρ k X M a d : ℝ) * (1 / (d : ℝ)) :=
        sum_truncatedTail_eq b ρ L D k X M a
      _ ≤ ∑ d ∈ Ioc L D, ((c * δ / 4) * scale b X M) *
          (((L : ℝ) / d + 1 / (1 + Real.log D)) * (1 / (d : ℝ))) := by
        apply sum_le_sum
        intro d hd
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hpair d hd) (by positivity)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (pair_weight_sum (L := L) (D := D) (by simp [L, lowCut])) hη
  have hpos : 0 < (c * scale b X M) * δ := by positivity
  nlinarith [hlo.trans hupper]


private lemma span_div_cut_eventually (k : ℕ) (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, (span k X : ℝ) / highCut X ≤ δ := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (Real.log (4 * (k : ℝ))), hlog.eventually_ge_atTop (3 / δ)] with
    X hX h₁ h₂ h₃
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hcut : 0 < (highCut X : ℝ) := by unfold highCut; positivity
  have hcut' : (Real.log (X : ℝ)) ^ 2 ≤ (highCut X : ℝ) := by
    simpa [highCut] using (Nat.lt_floor_add_one ((Real.log (X : ℝ)) ^ 2)).le
  have hspan : (span k X : ℝ) ≤ 3 * Real.log X := by
    unfold span window
    push_cast
    have harg : Real.log ((4 : ℝ) * k * X) = Real.log (4 * (k : ℝ)) + Real.log X :=
      Real.log_mul (by positivity) hXR.ne'
    have h := Nat.floor_le (Real.log_natCast_nonneg (4 * k * X))
    push_cast at h
    linarith
  rw [div_le_iff₀ hcut]
  calc
    _ ≤ 3 * Real.log X := hspan
    _ ≤ δ * (Real.log (X : ℝ)) ^ 2 := by
      have hz := (div_le_iff₀ hδ).mp h₃
      nlinarith [mul_le_mul_of_nonneg_right hz (show 0 ≤ Real.log (X : ℝ) by linarith)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcut' hδ.le

private lemma no_small_entry {k K u B M : ℕ} {b : Finset ℕ} (hKk : K < k) (hku : k ^ 2 ≤ k * u)
    (hcover : ∀ x ∈ Icc (k * u) (k * u + B + 1),
      (∀ j ∈ b, x ≠ k * (u + j)) → Covered M K x) :
    ∀ x ∈ Icc (k * u) (k * u + B + 1), ∀ p d : ℕ,
      p.Prime → x < p ^ 2 → x = d * p → K < d := by
  intro x hx p d hp hpx hxp
  by_cases hex : ∃ j ∈ b, x = k * (u + j)
  · obtain ⟨j, _, hxj⟩ := hex
    have hA := (mem_Icc.1 hx).1
    have hpk : k < p := by
      by_contra! hle
      have h := Nat.pow_le_pow_left hle 2
      omega
    have hpd : p ∣ k * (u + j) := by rw [← hxj, hxp]; exact dvd_mul_left _ _
    have hn : ¬ p ∣ k := fun h ↦
      (not_le_of_gt hpk) (Nat.le_of_dvd (by omega) h)
    obtain ⟨v, hv⟩ := (hp.dvd_mul.mp hpd).resolve_left hn
    have hv₀ : 0 < v := by
      by_contra! he
      have hz : v = 0 := by omega
      simp [hz] at hv
      have hk₀ : 0 < k := by omega
      have hu₀ : 0 < u := by
        by_contra! hu
        have huz : u = 0 := by omega
        simp [huz, hk₀.ne'] at hku
      omega
    have hd : k * v = d := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      rw [mul_assoc, mul_comm v p, ← hv, ← hxj, hxp]
    have hle : k ≤ k * v := by
      calc k = k * 1 := (mul_one k).symm
           _ ≤ _ := Nat.mul_le_mul_left k (by omega)
    omega
  · exact cofactor_gt_of_cover (hcover x hx (fun j hj he ↦ hex ⟨j, hj, he⟩))
      ⟨p, hp, hpx, hxp⟩

private theorem approx_score (h1 : H1) (h2 : H2) (h3 : H3) {y ε : ℝ}
    (hy : 0 < y) (hε : 0 < ε) :
    ∃ n, y ≤ score n ∧ score n < y + ε := by
  classical
  let δ := min (y / 4) (ε / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδy : 3 * δ < y := by
    have hd : δ ≤ y / 4 := min_le_left _ _
    linarith
  have hδε : 4 * δ ≤ ε := by
    have hd : δ ≤ ε / 4 := min_le_right _ _
    linarith
  obtain ⟨K₀, hK₀⟩ := exists_nat_one_div_lt hδ
  let K := K₀ + 1
  let k := K + 1
  have hK : 0 < K := by simp [K]
  have hk : 0 < k := by simp [k]
  have hKinv : (1 : ℝ) / K < δ := by simpa [K] using hK₀
  let g := Real.log (1 + 1 / (k : ℝ))
  have hg : 0 < g := by
    apply Real.log_pos
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    linarith [one_div_pos.mpr hkR]
  obtain ⟨m, hm⟩ := exists_nat_gt (y / g)
  have hmg : y < (m : ℝ) * g := (div_lt_iff₀ hg).mp hm
  have hm₀ : 0 < m := by
    by_contra! h
    have hz : m = 0 := by omega
    simp [hz] at hmg
    linarith
  obtain ⟨b, hbAdm, hbPos, ρ, c, hρ, hc, hmany⟩ := h1 m hm₀
  let B := k * b.sup id + 1
  have hB : 0 < B := by simp [B]
  have hbB : ∀ j ∈ b, k * j ≤ B := by
    intro j hj
    have hle : j ≤ b.sup id := le_sup (f := id) hj
    exact (Nat.mul_le_mul_left k hle).trans (Nat.le_succ _)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((error_tendsto.eventually (gt_mem_nhds hδ)).and
      (window_error_tendsto.eventually (gt_mem_nhds hδ)))
  obtain ⟨X, hmX, hpX, hcovX, hspan, hwX, hXlarge⟩ :=
    (hmany.and ((h2 b hbPos k hk ρ (c * δ / 4) hρ (by positivity)).and
      ((h3 b hbAdm hbPos k hk K B hbB).and ((span_div_cut_eventually k hk hδ).and
        ((window_tendsto.eventually_ge_atTop B).and
          (eventually_ge_atTop (max (k ^ 2 + 1) (2 * N + 2)))))))).exists
  obtain ⟨M, a, hM, hcover⟩ := hcovX
  have hXk := (le_max_left (k ^ 2 + 1) (2 * N + 2)).trans hXlarge
  have hXN := (le_max_right (k ^ 2 + 1) (2 * N + 2)).trans hXlarge
  have hX : 0 < X := by omega
  obtain ⟨u, hu, htail⟩ := find_good_anchor hc hδ hX hM.1 (hmX _ _ hM) (hpX _ _ hM)
  have hprime : m ≤ (b.filter (fun j ↦ (u + j).Prime)).card := by
    unfold goodAnchors at hu
    exact (mem_filter.mp hu).2
  have hu' : u ∈ anchors X M a := by
    unfold goodAnchors roughAnchors at hu
    exact (mem_filter.mp (mem_filter.mp hu).1).1
  obtain ⟨hleft, hright⟩ := hcover u hu'
  have huX := mem_Icc.mp (mem_filter.mp hu').1
  let A := k * u
  have huA : u ≤ A := by
    calc u = 1 * u := (one_mul u).symm
         _ ≤ _ := Nat.mul_le_mul_right u (by omega)
  have hXA : X ≤ A := huX.1.trans huA
  have hA : 0 < A := hX.trans_le hXA
  have hAmax : A ≤ 4 * k * X := by
    calc A ≤ k * (2 * X) := Nat.mul_le_mul_left k huX.2
         _ ≤ 4 * k * X := by rw [show 4 * k * X = 2 * (k * (2 * X)) by ring]; omega
  obtain ⟨n₀, n₁, hn, hn₁, he₀, he₀', he₁, he₁'⟩ :=
    endpoint_window_brackets hB (hwX.trans (window_mono hXA))
  have hn₀ : A - span k X ≤ n₀ := by
    have hwin := window_mono ((hn.le.trans hn₁).trans hAmax)
    unfold endpoint at he₀
    unfold span
    omega
  have hN₀ : N ≤ n₀ := by
    have hwin := window_le n₀
    unfold endpoint at he₀
    omega
  have hstart : score n₀ < y := by
    have hscore := score_upper hn₀ he₀'
    have ht := tail_upper (D := highCut X) (by simp [highCut]) hleft
    change (∑ x ∈ Ioc (A - span k X) A, primeGain x) ≤ _ at ht
    have hE := (hN n₀ hN₀).2
    linarith
  have hfinish : y ≤ score n₁ := by
    have hku : k < u := by
      have hk2 : k ≤ k ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul_right k (show 1 ≤ k by omega)
      omega
    have hlo := score_lower_of_prime_offsets b hk hku hn₁ he₁ (fun j hj ↦ ⟨hbPos j hj, hbB j hj⟩)
    have hreal : (m : ℝ) ≤ (↑((b.filter (fun j ↦ (u + j).Prime)).card) : ℝ) := by
      exact_mod_cast hprime
    exact hmg.le.trans ((mul_le_mul_of_nonneg_right hreal hg.le).trans hlo)
  have hs := no_small_entry (show K < k by simp [k]) (show k ^ 2 ≤ A by omega) hright
  have hE : ∀ x ≥ A, error x ≤ δ := by
    intro x hx
    exact (hN x (show N ≤ x by omega)).1.le
  obtain ⟨n, hlow, hhigh⟩ := first_crossing hn.le hstart hfinish
    (fun j hj hj' ↦ jump_upper hδ.le hK (by linarith) he₀ he₁' hj hj' hA hE hs)
  exact ⟨n, hlow, hhigh.trans_le (add_le_add_right hδε y)⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos420.erdos_420.parts.ii := by
  intro h1 h2 h3 y hy
  have hy' : 1 < y := hy
  have hy₀ : 0 < y := zero_lt_one.trans hy'
  have hcl : Real.log y ∈ closure (Set.range score) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hlo, hhi⟩ := approx_score h1 h2 h3 (Real.log_pos hy') hε
    refine ⟨score n, ⟨n, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have himage := image_closure_subset_closure_image (s := Set.range score) Real.continuous_exp
  have hrange : Real.exp '' Set.range score ⊆ Set.range (Erdos420.F fun n ↦ Real.log n) := by
    rintro _ ⟨_z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (Real.exp_log (zero_lt_one.trans_le (Erdos420.one_le_F _ _))).symm⟩
  exact closure_mono hrange (himage ⟨Real.log y, hcl, Real.exp_log hy₀⟩)

end OMA.R_Erdos420_erdos_420_parts_ii_R1
