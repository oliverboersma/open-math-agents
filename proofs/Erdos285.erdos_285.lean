import FormalConjectures.ErdosProblems.«285»
import Mathlib

/-!
Croot's short-interval unit-fraction theorem is ported from Will Howe
(@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions, commit
c58a7d45114c3af27e6abb19dcfca9d82b49b4a1. Used under Apache-2.0.
The underlying theorem and argument are due to Ernest S. Croot III,
On unit fractions with denominators in short intervals, Acta Arith. 99 (2001).
The finite lower bound was proved by @Rahul-007afk in open-math-agents PR 521.
The proof of the exact-cardinality upper bound below is new. For a given t,
the identity 1/(t(t+1)m) = 1/(t(2t+1)m) + 1/((t+1)(2t+1)m) raises the
cardinality by one. Almost all denominators in Croot's interval are present,
so sufficiently many disjoint replacements are available for every large k.
Credit: @marcusbuffett.
-/
section
/-!
# Basic definitions for the formalization of Croot's theorem

* `Croot.recipSum S = ∑_{n ∈ S} 1/n` as a rational number;
* `Croot.PPSmooth y n`: every prime power exactly dividing `n` is at most `y`.
-/

open Finset

namespace Croot

/-- The sum of reciprocals of a finite set of natural numbers, as a rational number. -/
def recipSum (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

@[simp] lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

lemma recipSum_union {S T : Finset ℕ} (h : Disjoint S T) :
    recipSum (S ∪ T) = recipSum S + recipSum T := by
  simp [recipSum, sum_union h]

lemma recipSum_sdiff {S T : Finset ℕ} (h : T ⊆ S) :
    recipSum (S \ T) = recipSum S - recipSum T := by
  have := sum_sdiff (f := fun n : ℕ => (1 : ℚ) / n) h
  simp only [recipSum]
  linarith

lemma recipSum_nonneg (S : Finset ℕ) : 0 ≤ recipSum S :=
  sum_nonneg fun _ _ => by positivity

lemma recipSum_mono {S T : Finset ℕ} (h : S ⊆ T) : recipSum S ≤ recipSum T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- `n` is `y`-prime-power-smooth: every prime power `p ^ v_p(n)` with `p ∣ n` is `≤ y`. -/
def PPSmooth (y n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ y

instance (y : ℕ) : DecidablePred (PPSmooth y) := fun n => by
  unfold PPSmooth; infer_instance

lemma ppSmooth_one (y : ℕ) : PPSmooth y 1 := by simp [PPSmooth]

lemma PPSmooth.mono {y y' n : ℕ} (h : PPSmooth y n) (hy : y ≤ y') : PPSmooth y' n :=
  fun p hp => (h p hp).trans hy

lemma PPSmooth.of_dvd {y n d : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) (hd : d ∣ n) :
    PPSmooth y d := by
  intro p hp
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono hd hn hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  calc p ^ d.factorization p ≤ p ^ n.factorization p :=
        Nat.pow_le_pow_right hpp.pos ((Nat.factorization_le_iff_dvd hd0 hn).2 hd p)
    _ ≤ y := h p hpn

/-- A `y`-pp-smooth positive integer divides `lcm(1, …, y)`. -/
lemma PPSmooth.dvd_lcmUpto {y n : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) :
    n ∣ Nat.lcmUpto y := by
  rw [← Nat.factorization_le_iff_dvd hn (Nat.lcmUpto_ne_zero y)]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_lcmUpto y hpp]
    exact Nat.le_log_of_pow_le hpp.one_lt (h p hp)
  · have : n.factorization p = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [this]

/-- Divisors of `lcm(1, …, y)` are `y`-pp-smooth. -/
lemma ppSmooth_of_dvd_lcmUpto {y n : ℕ} (hn : n ∣ Nat.lcmUpto y) : PPSmooth y n := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hle : n.factorization p ≤ p.log y := by
    rw [← Nat.factorization_lcmUpto y hpp]
    exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp) |>.symm
      |> fun h => by
        intro h0; subst h0; simp at hp) (Nat.lcmUpto_ne_zero y)).2 hn p
  calc p ^ n.factorization p ≤ p ^ p.log y := Nat.pow_le_pow_right hpp.pos hle
    _ ≤ y := by
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        have : (Nat.lcmUpto 0) = 1 := by simp [Nat.lcmUpto]
        rw [this, Nat.dvd_one] at hn
        subst hn; simp at hp
      · exact Nat.pow_log_le_self p hy.ne'

/-- The least common multiple of `y`-pp-smooth numbers is `y`-pp-smooth. -/
lemma ppSmooth_lcm {y : ℕ} {S : Finset ℕ} (hS : ∀ n ∈ S, PPSmooth y n) (h0 : 0 ∉ S) :
    PPSmooth y (S.lcm id) := by
  apply ppSmooth_of_dvd_lcmUpto
  apply Finset.lcm_dvd
  intro n hn
  exact (hS n hn).dvd_lcmUpto (fun h => h0 (h ▸ hn))

/-- The reduced denominator of `∑_{n∈S} 1/n` divides `lcm S`. -/
lemma den_recipSum_dvd {S : Finset ℕ} (hS : 0 ∉ S) : (recipSum S).den ∣ S.lcm id := by
  set L := S.lcm id with hLdef
  have hL0 : L ≠ 0 := by
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    simpa using hS
  have key : recipSum S = (((∑ n ∈ S, L / n : ℕ) : ℤ) : ℚ) / (((L : ℕ) : ℤ) : ℚ) := by
    simp only [Int.cast_natCast]
    rw [recipSum, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (fun h : n = 0 => hS (h ▸ hn))
    have hdvd : n ∣ L := Finset.dvd_lcm hn
    rw [Nat.cast_div hdvd hn0]
    have hL : (L : ℚ) ≠ 0 := by exact_mod_cast hL0
    field_simp
  have h := Rat.den_dvd ((∑ n ∈ S, L / n : ℕ) : ℤ) ((L : ℕ) : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [key]
  exact_mod_cast h

/-- The reduced denominator of a sum of reciprocals of `y`-pp-smooth numbers is `y`-pp-smooth. -/
lemma ppSmooth_den_recipSum {y : ℕ} {S : Finset ℕ} (hS : ∀ n ∈ S, PPSmooth y n) (h0 : 0 ∉ S) :
    PPSmooth y (recipSum S).den :=
  (ppSmooth_lcm hS h0).of_dvd (by
    rw [Ne, Finset.lcm_eq_zero_iff]; simpa using h0) (den_recipSum_dvd h0)

end Croot
end

section
/-!
# Harmonic sums over intervals

`∑_{n=N+1}^{M} 1/n` lies between `log((M+1)/(N+1))` and `log(M/N)`, and the
harmonic block `(N, M]` with `1 ≤ ∑ < 1 + 1/M` has `e N ≤ M ≤ e N + 3`.
-/

namespace Croot

open Real Finset

/-- Peeling off the top point of `(N, M + 1]`. -/
lemma recipSum_Ioc_succ {N M : ℕ} (h : N ≤ M) :
    recipSum (Ioc N (M + 1)) = recipSum (Ioc N M) + 1 / ((M : ℚ) + 1) := by
  rw [recipSum, Finset.sum_Ioc_succ_top h, recipSum]
  push_cast
  ring

/-- `(N, M]` is empty when `M ≤ N`. -/
lemma recipSum_Ioc_of_le {N M : ℕ} (h : M ≤ N) : recipSum (Ioc N M) = 0 := by
  rw [Finset.Ioc_eq_empty_of_le h, recipSum_empty]

/-- `1/(x+1) ≤ log (x+1) - log x` for `x > 0` (from `log t ≤ t - 1` at `t = x/(x+1)`). -/
lemma one_div_add_one_le_log_sub {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / (x + 1) by positivity)
  rw [Real.log_div hx.ne' (by positivity)] at h
  have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
  linarith

/-- `log (x+1) - log x ≤ 1/x` for `x > 0` (from `log t ≤ t - 1` at `t = (x+1)/x`). -/
lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- `∑_{n=N+1}^{M} 1/n ≤ log (M/N)`. -/
theorem recipSum_Ioc_le_log {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ((recipSum (Ioc N M) : ℚ) : ℝ) ≤ Real.log ((M : ℝ) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  induction M, hNM using Nat.le_induction with
  | base =>
    rw [recipSum_Ioc_of_le le_rfl, div_self hN0.ne', Real.log_one, Rat.cast_zero]
  | succ M hNM ih =>
    have hM0 : (0 : ℝ) < M := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast hN.trans hNM
      linarith
    have key := one_div_add_one_le_log_sub hM0
    rw [Real.log_div hM0.ne' hN0.ne'] at ih
    rw [recipSum_Ioc_succ hNM, Rat.cast_add, Real.log_div (by positivity) hN0.ne']
    push_cast
    linarith

/-- `log ((M+1)/(N+1)) ≤ ∑_{n=N+1}^{M} 1/n`. -/
theorem log_le_recipSum_Ioc {N M : ℕ} (hNM : N ≤ M) :
    Real.log (((M : ℝ) + 1) / ((N : ℝ) + 1)) ≤ ((recipSum (Ioc N M) : ℚ) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  induction M, hNM using Nat.le_induction with
  | base =>
    rw [recipSum_Ioc_of_le le_rfl, div_self hN0.ne', Real.log_one, Rat.cast_zero]
  | succ M hNM ih =>
    have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have key := log_add_one_sub_log_le hM0
    rw [Real.log_div hM0.ne' hN0.ne'] at ih
    rw [recipSum_Ioc_succ hNM, Rat.cast_add]
    push_cast
    rw [Real.log_div (by positivity) hN0.ne']
    linarith

/-- The harmonic block starting after `N`. -/
theorem exists_harmonic_block {N : ℕ} (hN : 1 ≤ N) : ∃ M : ℕ, N < M ∧
    1 ≤ recipSum (Ioc N M) ∧ recipSum (Ioc N M) < 1 + 1 / (M : ℚ) ∧
    Real.exp 1 * N ≤ M ∧ (M : ℝ) ≤ Real.exp 1 * N + 3 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  -- some `m` has `H((N, m]) ≥ 1`: take `m = 3N + 3`, so `(m+1)/(N+1) ≥ 3 > e`
  have hex : ∃ m : ℕ, 1 ≤ recipSum (Ioc N m) := by
    refine ⟨3 * N + 3, ?_⟩
    have h := log_le_recipSum_Ioc (N := N) (M := 3 * N + 3) (by omega)
    have h1 : (1 : ℝ) ≤ Real.log ((((3 * N + 3 : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      push_cast
      nlinarith
    have h2 : ((1 : ℚ) : ℝ) ≤ ((recipSum (Ioc N (3 * N + 3)) : ℚ) : ℝ) := by
      rw [Rat.cast_one]; exact h1.trans h
    exact_mod_cast h2
  -- `M` is the least such `m`
  obtain ⟨M, hM1, hmin⟩ : ∃ M, 1 ≤ recipSum (Ioc N M) ∧
      ∀ m < M, ¬ 1 ≤ recipSum (Ioc N m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hNM : N < M := by
    by_contra h
    rw [recipSum_Ioc_of_le (not_lt.1 h)] at hM1
    norm_num at hM1
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hNM' : N ≤ M' := by omega
  have hlt : recipSum (Ioc N M') < 1 := lt_of_not_ge (hmin M' (by omega))
  have hsucc := recipSum_Ioc_succ hNM'
  refine ⟨M' + 1, hNM, hM1, ?_, ?_, ?_⟩
  · -- minimality: `H((N, M]) = H((N, M - 1]) + 1/M < 1 + 1/M`
    rw [hsucc]
    push_cast
    linarith
  · -- upper bound: `1 ≤ H((N, M]) ≤ log (M / N)`, so `e ≤ M / N`
    have h := recipSum_Ioc_le_log hN hNM.le
    have h1 : ((1 : ℚ) : ℝ) ≤ ((recipSum (Ioc N (M' + 1)) : ℚ) : ℝ) := by exact_mod_cast hM1
    rw [Rat.cast_one] at h1
    have h2 : (1 : ℝ) ≤ Real.log (((M' + 1 : ℕ) : ℝ) / N) := h1.trans h
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hN0] at h2
    exact h2
  · -- lower bound at `M - 1`: `log (M/(N+1)) ≤ H((N, M - 1]) < 1`, so `M < e (N + 1)`
    have h := log_le_recipSum_Ioc hNM'
    have h1 : ((recipSum (Ioc N M') : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by exact_mod_cast hlt
    rw [Rat.cast_one] at h1
    have h2 : Real.log (((M' : ℝ) + 1) / ((N : ℝ) + 1)) < 1 := h.trans_lt h1
    rw [Real.log_lt_iff_lt_exp (by positivity), div_lt_iff₀ (by positivity)] at h2
    push_cast
    nlinarith

end Croot
end

section
/-!
# Chebyshev-strength prime estimates used in the proof

All results follow from Mathlib's Chebyshev bounds
(`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge'`, `Chebyshev.pi_le_log4_mul_div`).

Helper lemmas:
* `Croot.eventually_log_pow_le_mul_sqrt`: `(log x) ^ n ≤ ε √x` eventually;
* `Croot.exists_sum_inv_primePow_Ioc_le`: a dyadic-block bound
  `∑_{q ∈ (A, B], q prime power} 1/q ≤ 12 (log B - log A + 2) / log A` for `A₀ ≤ A ≤ B`,
  deduced from `Croot.eventually_card_primePow_le`.
-/

namespace Croot

open Real Finset Filter

/-- For every `n` and every `ε > 0`, eventually `(log x) ^ n ≤ ε √x`. -/
lemma eventually_log_pow_le_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ ε * √x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have e1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n)]
  have e2 : ‖x ^ (1 / 2 : ℝ)‖ = √x := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hx' : ‖Real.log x ^ (n : ℝ)‖ ≤ ε * ‖x ^ (1 / 2 : ℝ)‖ := hx
  rw [e1, e2] at hx'
  exact hx'

/-- For large `x` there are at least `x / (5 log x)` primes in `(x, 2.7 x]`. -/
theorem eventually_card_primes_Ioc_ge : ∀ᶠ x : ℝ in atTop,
    x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 : ℝ),
    eventually_log_pow_le_mul_sqrt 1 (ε := 1 / 2000) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hx hlogx hL2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hfl : ⌊x⌋₊ ≤ ⌊(27 / 10 : ℝ) * x⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta ((27 / 10 : ℝ) * x) = Chebyshev.theta x +
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Finset.sum_filter]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hsum : ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) *
        Real.log ((27 / 10 : ℝ) * x) := by
    have h := Finset.sum_le_card_nsmul ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log ((27 / 10 : ℝ) * x)) (by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hp'.1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * x :=
          le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
        exact Real.log_le_log hp_pos hp_le)
    rw [nsmul_eq_mul] at h
    exact h
  have hlow := Chebyshev.theta_ge' (x := (27 / 10 : ℝ) * x) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hlog4] at hup
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs3 : 3 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogx' : Real.log x ≤ 1 / 2000 * √x := by simpa using hlogx
  have hlog27 : Real.log ((27 / 10 : ℝ) * x) ≤ Real.log x + 17 / 10 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog27' : 0 ≤ Real.log ((27 / 10 : ℝ) * x) := Real.log_nonneg (by linarith)
  have hlogx2 : Real.log ((27 / 10 : ℝ) * x + 2) ≤ Real.log x + 2 := by
    have h3x := Real.log_le_log (by linarith) (show (27 / 10 : ℝ) * x + 2 ≤ 3 * x by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3x
    have : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hsqrt27 : √((27 / 10 : ℝ) * x) ≤ 2 * √x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx0]
  have hprod : √((27 / 10 : ℝ) * x) * Real.log ((27 / 10 : ℝ) * x) ≤
      (2 * √x) * (2 * Real.log x) :=
    mul_le_mul hsqrt27 (by linarith) hlog27' (by positivity)
  have hsL : √x * Real.log x ≤ √x * (1 / 2000 * √x) := mul_le_mul_of_nonneg_left hlogx' hs0
  have hsL3 : 3 ≤ √x * Real.log x := by nlinarith
  have hLsL : Real.log x ≤ √x * Real.log x := by nlinarith
  have hx2 : 693 / 1000 * x ≤ Real.log 2 * x := mul_le_mul_of_nonneg_right hl2lo.le hx0
  have hdiff : (48 / 100 : ℝ) * x ≤
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    linarith [hsplit, hlow, hup, hlogx2, hprod, hsL, hss, hsL3, hLsL, hx2]
  have hcard0 : (0 : ℝ) ≤ (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    positivity
  have hc1 := mul_le_mul_of_nonneg_left hlog27 hcard0
  have hc2 := mul_nonneg hcard0 (show (0 : ℝ) ≤ 5 / 2 * Real.log x - 17 / 4 by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith [hsum, hdiff, hc1, hc2]

/-- For large `x` the number of prime powers in `[1, x]` is at most `4 x / log x`. -/
theorem eventually_card_primePow_le : ∀ᶠ x : ℝ in atTop,
    (((Icc 1 ⌊x⌋₊).filter IsPrimePow).card : ℝ) ≤ 4 * x / Real.log x := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_log_pow_le_mul_sqrt 2 (ε := 1 / 10) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx2 hlog2 hL1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl2pos : 0 < Real.log 2 := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hIcc : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hcount := Chebyshev.sum_PrimePow_eq_sum_sum (fun _ => (1 : ℝ)) hx0
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcount
  have hK1 : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hl2pos, one_mul]
    exact Real.log_le_log (by norm_num) hx2
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hK1] at hcount
  simp only [Nat.cast_one, div_one, Real.rpow_one] at hcount
  have hπ : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) ≤
      Real.log 4 * x / Real.log √x + √x := by
    rw [← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_card_eq_primeCounting]
    exact Chebyshev.pi_le_log4_mul_div hx1
  have hrest : ∑ k ∈ Ioc 1 ⌊Real.log x / Real.log 2⌋₊,
      (((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime).card : ℝ) ≤
        (Real.log x / Real.log 2) * √x := by
    calc _ ≤ ∑ k ∈ Ioc 1 ⌊Real.log x / Real.log 2⌋₊, √x := by
          apply Finset.sum_le_sum
          intro k hk
          have hk2' : 2 ≤ k := (Finset.mem_Ioc.mp hk).1
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2'
          calc (((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime).card : ℝ)
              ≤ ((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).card : ℝ) := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = (⌊x ^ (1 / (k : ℝ))⌋₊ : ℝ) := by rw [Nat.card_Ioc, Nat.sub_zero]
            _ ≤ x ^ (1 / (k : ℝ)) := Nat.floor_le (Real.rpow_nonneg hx0 _)
            _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le
                (one_div_le_one_div_of_le (by norm_num) hk2)
            _ = √x := (Real.sqrt_eq_rpow x).symm
      _ = ((⌊Real.log x / Real.log 2⌋₊ - 1 : ℕ) : ℝ) * √x := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (Real.log x / Real.log 2) * √x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg x)
          calc ((⌊Real.log x / Real.log 2⌋₊ - 1 : ℕ) : ℝ)
              ≤ (⌊Real.log x / Real.log 2⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
            _ ≤ Real.log x / Real.log 2 := Nat.floor_le (div_nonneg hL0.le hl2pos.le)
  have hsqrt_log : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hsqrt_log, hlog4] at hπ
  have hπ' : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) ≤
      4 * Real.log 2 * x / Real.log x + √x := by
    have e : 2 * Real.log 2 * x / (Real.log x / 2) = 4 * Real.log 2 * x / Real.log x := by
      ring
    linarith [hπ, e]
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hdiv : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
    rw [div_le_iff₀ hl2pos]; nlinarith
  have key : √x + (Real.log x / Real.log 2) * √x ≤ (4 - 4 * Real.log 2) * x / Real.log x := by
    rw [le_div_iff₀ hL0]
    have h0 : (Real.log x / Real.log 2) * √x ≤ (2 * Real.log x) * √x :=
      mul_le_mul_of_nonneg_right hdiv hs0
    have h1 : (√x + (Real.log x / Real.log 2) * √x) * Real.log x ≤
        (√x + 2 * Real.log x * √x) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hL0.le
    have h2 : Real.log x ^ 2 * √x ≤ 1 / 10 * √x * √x := by
      have := mul_le_mul_of_nonneg_right hlog2 hs0
      linarith
    have h3 : 0 ≤ √x * Real.log x * (Real.log x - 1) :=
      mul_nonneg (mul_nonneg hs0 hL0.le) (by linarith)
    have h4 : Real.log 2 * x ≤ 7 / 10 * x := mul_le_mul_of_nonneg_right hl2hi.le hx0
    linarith [h1, h2, h3, h4, hss]
  rw [hIcc, hcount]
  have e2 : 4 * Real.log 2 * x / Real.log x + (4 - 4 * Real.log 2) * x / Real.log x =
      4 * x / Real.log x := by ring
  linarith [hπ', hrest, key, e2]

/-- Dyadic-block bound for reciprocal sums of prime powers. -/
lemma exists_sum_inv_primePow_Ioc_le : ∃ A₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → A ≤ B →
    ∑ q ∈ (Ioc A B).filter IsPrimePow, (1 : ℝ) / q ≤
      12 * (Real.log B - Real.log A + 2) / Real.log A := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp eventually_card_primePow_le
  refine ⟨max 2 ⌈X₀⌉₊, fun A B hA hAB => ?_⟩
  have hA2 : 2 ≤ A := le_trans (le_max_left _ _) hA
  have hAX : X₀ ≤ (A : ℝ) := by
    have h1 : ⌈X₀⌉₊ ≤ A := le_trans (le_max_right _ _) hA
    calc X₀ ≤ (⌈X₀⌉₊ : ℝ) := Nat.le_ceil X₀
      _ ≤ (A : ℝ) := by exact_mod_cast h1
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl2pos : 0 < Real.log 2 := by linarith
  have hab : Nat.log 2 A ≤ Nat.log 2 B := Nat.log_mono_right hAB
  have hmaps : ∀ q ∈ (Ioc A B).filter IsPrimePow,
      Nat.log 2 q ∈ Icc (Nat.log 2 A) (Nat.log 2 B) := by
    intro q hq
    have hq' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    exact Finset.mem_Icc.mpr ⟨Nat.log_mono_right hq'.1.le, Nat.log_mono_right hq'.2⟩
  have hblock : ∀ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B),
      ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q ≤
        8 / ((j + 1) * Real.log 2) := by
    intro j hj
    have hja : Nat.log 2 A ≤ j := (Finset.mem_Icc.mp hj).1
    have hX : X₀ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
      have h1 : A < 2 ^ (Nat.log 2 A).succ := Nat.lt_pow_succ_log_self (by norm_num) A
      have h2 : 2 ^ (Nat.log 2 A).succ ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (A : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le h1 h2).le
      linarith
    have hcnt := hX₀ _ hX
    rw [Nat.floor_natCast] at hcnt
    have hsub : ((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j) ⊆
        (Icc 1 (2 ^ (j + 1))).filter IsPrimePow := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, hq.1.2⟩
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
      rw [hq.2] at this
      exact this.le
    have hD : (0 : ℝ) < (j + 1) * Real.log 2 := mul_pos (by positivity) hl2pos
    have hlogpow : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = (j + 1) * Real.log 2 := by
      push_cast [Real.log_pow]; ring
    rw [hlogpow] at hcnt
    have hcard_le : ((((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j)).card : ℝ)
        ≤ (((Icc 1 (2 ^ (j + 1))).filter IsPrimePow).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    calc ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q
        ≤ ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / 2 ^ j := by
          apply Finset.sum_le_sum
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
          have hq0 : q ≠ 0 := by omega
          have h2q : 2 ^ j ≤ q := by
            have := Nat.pow_log_le_self 2 hq0
            rw [hq.2] at this
            exact this
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast h2q
      _ = ((((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j)).card : ℝ) / 2 ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ (4 * ((2 ^ (j + 1) : ℕ) : ℝ) / ((j + 1) * Real.log 2)) / 2 ^ j :=
          div_le_div_of_nonneg_right (le_trans hcard_le hcnt) (by positivity)
      _ = 8 / ((j + 1) * Real.log 2) := by
          rw [div_div, div_eq_div_iff (mul_pos hD (by positivity)).ne' hD.ne']
          push_cast
          ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlA : 0 < Real.log A := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hAlt : Real.log A < (Nat.log 2 A + 1) * Real.log 2 := by
    have h1 : A < 2 ^ (Nat.log 2 A + 1) := Nat.lt_pow_succ_log_self (by norm_num) A
    have h2 : (A : ℝ) < 2 ^ (Nat.log 2 A + 1) := by exact_mod_cast h1
    have := Real.log_lt_log hA0 h2
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hBge : (Nat.log 2 B : ℝ) * Real.log 2 ≤ Real.log B := by
    have h1 : 2 ^ (Nat.log 2 B) ≤ B := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ) ^ (Nat.log 2 B)) ≤ (B : ℝ) := by exact_mod_cast h1
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at this
    exact this
  have hab' : (Nat.log 2 A : ℝ) ≤ Nat.log 2 B := by exact_mod_cast hab
  calc ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B),
        ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q
      ≤ ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B), 8 / ((j + 1) * Real.log 2) :=
        Finset.sum_le_sum hblock
    _ ≤ ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B), 8 / ((Nat.log 2 A + 1) * Real.log 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hja : (Nat.log 2 A : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by positivity) hl2pos)
        exact mul_le_mul_of_nonneg_right (by linarith) hl2pos.le
    _ = ((Nat.log 2 B + 1 - Nat.log 2 A : ℕ) : ℝ) * (8 / ((Nat.log 2 A + 1) * Real.log 2)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ 12 * (Real.log B - Real.log A + 2) / Real.log A := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (by positivity) hl2pos) hlA]
        have h1 : ((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log 2 ≤
            Real.log B - Real.log A + 2 := by
          linarith [hBge, hAlt, hl2hi]
        have hu : (0 : ℝ) ≤ (Nat.log 2 B : ℝ) + 1 - Nat.log 2 A := by linarith
        have h2 := mul_le_mul_of_nonneg_left hAlt.le (mul_nonneg hu hl2pos.le)
        have h3 := mul_le_mul_of_nonneg_right h1
          (mul_pos (by positivity : (0 : ℝ) < (Nat.log 2 A : ℝ) + 1) hl2pos).le
        have h4 : (8 : ℝ) * (((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log A) ≤
            12 * Real.log 2 * (((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log A) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hu hlA.le)
        linarith [h2, h3, h4]

/-- The reciprocal sum of the prime powers in `(N / (log N)^4, 3 N]` tends to `0`. -/
theorem tendsto_sum_inv_primePow_Ioc :
    Tendsto (fun N : ℕ => ∑ q ∈ (Ioc ⌊(N : ℝ) / (Real.log N) ^ 4⌋₊ (3 * N)).filter IsPrimePow,
      (1 : ℝ) / q) atTop (nhds 0) := by
  obtain ⟨A₀, hA₀⟩ := exists_sum_inv_primePow_Ioc_le
  have hg : Tendsto (fun N : ℕ => 120 * (1 + Real.log (Real.log N)) / Real.log N)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h2 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h3 : Tendsto (fun t : ℝ => 120 * (t⁻¹ + Real.log t / t)) atTop
        (nhds (120 * (0 + 0))) := (h1.add h2).const_mul 120
    rw [add_zero, mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => 120 * (1 + Real.log t) / t) atTop (nhds 0) :=
      h3.congr fun t => by ring
    exact (h4.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity)
    ?_ hg
  have E1 : ∀ᶠ x : ℝ in atTop, 4 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 4
  have E2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 ≤ 1 * √x := eventually_log_pow_le_mul_sqrt 4 one_pos
  have E3 : ∀ᶠ x : ℝ in atTop, ((A₀ : ℝ) + 2) ^ 2 ≤ x := eventually_ge_atTop _
  have E4 : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 1 ≤ 1 / 16 * √(Real.log x) :=
    Real.tendsto_log_atTop.eventually (eventually_log_pow_le_mul_sqrt 1 (by norm_num))
  have E5 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hall := tendsto_natCast_atTop_atTop.eventually (E1.and (E2.and (E3.and (E4.and E5))))
  filter_upwards [hall] with N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hL4pos : 0 < Real.log N ^ 4 := by positivity
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0
  have hsq0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hsqrt_ge : (A₀ : ℝ) + 2 ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le h3
  have hA₀0 : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg _
  generalize hy : (N : ℝ) / Real.log N ^ 4 = y
  have hy_ge : √(N : ℝ) ≤ y := by
    rw [← hy, le_div_iff₀ hL4pos]
    have := mul_le_mul_of_nonneg_left h2 hsq0
    nlinarith
  have hy_le : y ≤ N := by
    rw [← hy]
    apply div_le_self hN0
    have : (1 : ℝ) ≤ Real.log N := by linarith
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
  have hy2 : 2 ≤ y := by linarith
  generalize hA : ⌊y⌋₊ = A
  have hA_ge : A₀ ≤ A := by
    rw [← hA]; apply Nat.le_floor; linarith
  have hA_real_le : (A : ℝ) ≤ y := by rw [← hA]; exact Nat.floor_le (by linarith)
  have hA_real_ge : y / 2 ≤ (A : ℝ) := by
    have := Nat.sub_one_lt_floor y
    rw [hA] at this
    linarith
  have hAB : A ≤ 3 * N := by
    have : (A : ℝ) ≤ 3 * N := by linarith
    exact_mod_cast this
  have hbound := hA₀ A (3 * N) hA_ge hAB
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA_ge : Real.log N - 4 * Real.log (Real.log N) - Real.log 2 ≤ Real.log A := by
    have h := Real.log_le_log (by linarith) hA_real_ge
    rw [Real.log_div (by linarith) (by norm_num), ← hy,
      Real.log_div (by linarith) (by positivity), Real.log_pow] at h
    push_cast at h
    linarith
  have hlog3N : Real.log ((3 * N : ℕ) : ℝ) = Real.log 3 + Real.log N := by
    push_cast
    exact Real.log_mul (by norm_num) (by linarith)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogL0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (Real.log N) ≤ Real.log N / 16 := by
    have hsqrtL : √(Real.log N) ≤ Real.log N :=
      (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
    rw [pow_one] at h4
    linarith
  have hlA_ge : Real.log N / 2 ≤ Real.log A := by linarith
  have hlA_pos : 0 < Real.log A := by linarith
  have hnum : Real.log ((3 * N : ℕ) : ℝ) - Real.log A + 2 ≤ 5 + 4 * Real.log (Real.log N) := by
    rw [hlog3N]; linarith
  calc _ ≤ 12 * (Real.log ((3 * N : ℕ) : ℝ) - Real.log A + 2) / Real.log A := hbound
    _ ≤ 120 * (1 + Real.log (Real.log N)) / Real.log N := by
      rw [div_le_div_iff₀ hlA_pos hL0]
      have k1 := mul_le_mul_of_nonneg_right hnum hL0.le
      have k2 := mul_le_mul_of_nonneg_left hlA_ge
        (by linarith : (0 : ℝ) ≤ 1 + Real.log (Real.log N))
      have k3 := mul_nonneg hlogL0 hL0.le
      linarith [k1, k2, k3]

end Croot
end

section
/-!
# Croot's Lemma 1: subset sums of inverses of primes cover all residues

For `n` large, if `R` is a set of at least `(log n)^{3.9}` primes in
`[(log n)^4/4, 3 (log n)^4]`, none dividing `n`, then every residue class modulo `n`
is a sum `∑_{r ∈ T} r⁻¹` over some subset `T ⊆ R`.

## Proof outline

Write `ψ = ZMod.stdAddChar` (`ψ x = exp (2πi x / n)`), `k = |R|` and `w = (log n)^{1/10}`, so
that `log n = w^10`, `(log n)^4 = w^40`, `(log n)^{3.9} = w^39`.

* `Lemma1Aux.exists_subset_sum_of_norm_prod_le` (Fourier criterion): by orthogonality,
  `∑_h ψ(-hc) ∏_{r∈R} (1 + ψ(h r⁻¹)) = n · #{T ⊆ R : ∑_{T} r⁻¹ = c}`; the `h = 0` term is
  `2^k`, so if every other term has norm `≤ 2^k / n` the count is positive.
* `Lemma1Aux.norm_one_add_stdAddChar_sq_le`: `‖1 + ψ x‖² ≤ 4 - 16 (t/n)²`, where `t` is the
  least absolute residue of `x` (from `cos θ ≤ 1 - 2θ²/π²` on `[-π, π]`).
* `Lemma1Aux.pow_card_le_of_primes_dvd`, `Lemma1Aux.card_bad_le` (pigeonhole): writing
  `t_r` for the least absolute residue of `h r⁻¹`, we have `r t_r = h + s_r n`; the primes with
  `|r t_r| ≤ L n` (`L = (log n)^{2.8} = w^28`) have `|s_r| ≤ L + 1`, and for each value of `s_r`
  the corresponding primes all divide the nonzero integer `h + s_r n` of size `< (L + 2) n`,
  so there are at most `2 log n` of them.  Hence at most `k/2` primes are bad.
* `Lemma1Aux.norm_prod_le`: each good prime has `|t_r| / n ≥ 1 / (3 w^12)`, so its factor
  satisfies `‖1 + ψ‖² ≤ 4 exp(-4/(9 w^24))`; multiplying gives
  `‖∏‖² ≤ 4^k exp(-(2/9) w^15) ≤ 4^k / n²`.
* `Lemma1Aux.ineq_*`: the elementary inequalities in `w` (valid for `w ≥ 10`).
-/

namespace Croot

open Real Finset Filter

namespace Lemma1Aux

/-! ### Step 1: the Fourier-analytic existence criterion -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- An additive character turns finite sums into products. -/
lemma stdAddChar_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ T, f i) = ∏ i ∈ T, ZMod.stdAddChar (f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier criterion: if every nontrivial frequency `h` gives a product of norm at most
`2^|R| / n`, then every residue class is a subset sum of the `u i`. -/
theorem exists_subset_sum_of_norm_prod_le {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (u : ι → ZMod n)
    (hbound : ∀ h : ZMod n, h ≠ 0 →
      ‖∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i))‖ ≤ 2 ^ R.card / n)
    (c : ZMod n) : ∃ T ⊆ R, ∑ i ∈ T, u i = c := by
  by_contra hne
  push Not at hne
  set F : ZMod n → ℂ := fun h =>
    ZMod.stdAddChar (-(h * c)) * ∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i)) with hF
  have hexpand : ∀ h : ZMod n,
      F h = ∑ T ∈ R.powerset, ZMod.stdAddChar (h * (∑ i ∈ T, u i - c)) := by
    intro h
    simp only [hF]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← stdAddChar_sum T (fun i => h * u i), ← AddChar.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  have key : ∑ h : ZMod n, F h = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hexpand h, Finset.sum_comm]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hT' : ∑ i ∈ T, u i - c ≠ 0 := sub_ne_zero.2 (hne T (Finset.mem_powerset.1 hT))
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ))
      (∑ i ∈ T, u i - c) (ZMod.isPrimitive_stdAddChar n)
    rw [if_neg hT', Nat.cast_zero] at this
    exact this
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod n))] at key
  have h0 : F 0 = 2 ^ R.card := by
    simp only [hF, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, Finset.prod_const]
    norm_num
  rw [h0] at key
  set S := ∑ h ∈ Finset.univ.erase (0 : ZMod n), F h with hS
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hSnorm : ‖S‖ ≤ ((n : ℝ) - 1) * (2 ^ R.card / n) := by
    calc ‖S‖ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), (2 ^ R.card / n : ℝ) := by
        refine Finset.sum_le_sum fun h hh => ?_
        simp only [hF]
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound h (Finset.ne_of_mem_erase hh)
    _ = ((n : ℝ) - 1) * (2 ^ R.card / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, nsmul_eq_mul, Nat.cast_sub NeZero.one_le, Nat.cast_one]
  have hSeq : S = -(2 : ℂ) ^ R.card := by linear_combination key
  rw [hSeq, norm_neg, norm_pow, Complex.norm_two] at hSnorm
  have h2 : (0 : ℝ) < 2 ^ R.card := by positivity
  have hlt : ((n : ℝ) - 1) * (2 ^ R.card / n) < 2 ^ R.card := by
    rw [mul_div_assoc', div_lt_iff₀ hn]
    nlinarith
  linarith

/-- `‖1 + e(x/n)‖² ≤ 4 - 16 (t/n)²`, where `t` is the least absolute residue of `x`. -/
lemma norm_one_add_stdAddChar_sq_le (x : ZMod n) :
    ‖1 + ZMod.stdAddChar x‖ ^ 2 ≤ 4 - 16 * ((x.valMinAbs : ℝ) / n) ^ 2 := by
  set t := x.valMinAbs with ht
  have hx : ((t : ℤ) : ZMod n) = x := ZMod.coe_valMinAbs x
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  set θ : ℝ := 2 * π * t / n with hθ
  have hpsi : ZMod.stdAddChar x = Complex.exp (θ * Complex.I) := by
    rw [← hx, ZMod.stdAddChar_coe]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hθbound : |θ| ≤ π := by
    obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc x
    have h1' : -(n : ℝ) < t * 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) * 2 ≤ n := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hn]
      nlinarith [pi_pos]
    · rw [hθ, div_le_iff₀ hn]
      nlinarith [pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθbound
  have hnorm : ‖1 + Complex.exp (θ * Complex.I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show (1 : ℂ) + (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
        = ↑(1 + Real.cos θ) + ↑(Real.sin θ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hpsi, hnorm]
  have : 2 / π ^ 2 * θ ^ 2 = 8 * ((t : ℝ) / n) ^ 2 := by
    rw [hθ]
    field_simp
    ring
  linarith

end Fourier

/-! ### Step 2: few primes of size `≥ y` divide a nonzero integer -/

lemma pow_card_le_of_primes_dvd (A : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hA : ∀ a ∈ A, a.Prime ∧ y ≤ a) (z : ℤ) (hz : z ≠ 0) (hdvd : ∀ a ∈ A, (a : ℤ) ∣ z) :
    y ^ A.card ≤ |(z : ℝ)| := by
  have h1 : ∏ a ∈ A, a ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hA a ha).1.prime
    · intro a ha
      exact Int.ofNat_dvd_left.1 (hdvd a ha)
  have h2 : ∏ a ∈ A, a ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  calc y ^ A.card = ∏ a ∈ A, y := (Finset.prod_const y).symm
  _ ≤ ∏ a ∈ A, (a : ℝ) := Finset.prod_le_prod (fun _ _ => hy) (fun a ha => (hA a ha).2)
  _ = ((∏ a ∈ A, a : ℕ) : ℝ) := by push_cast; rfl
  _ ≤ (z.natAbs : ℝ) := by exact_mod_cast h2
  _ = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The pigeonhole step: few `r` have `|r t_r|` small. -/
lemma card_bad_le (n H : ℕ) (hH0 : 0 < H) (hHn : H < n)
    (R : Finset ℕ) (y : ℝ) (hy : 1 ≤ y) (hR : ∀ r ∈ R, r.Prime ∧ y ≤ r)
    (t : ℕ → ℤ) (ht : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : (L + 2) * n < y ^ (m + 1)) :
    ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ) ≤ (2 * (L + 1) + 1) * m := by
  set M : ℤ := ⌊L + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by linarith)
  have hML : (M : ℝ) ≤ L + 1 := Int.floor_le _
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hHn)
  have hHnR : (H : ℝ) < n := by exact_mod_cast hHn
  have hH0R : (0 : ℝ) < H := by exact_mod_cast hH0
  -- each fibre is small
  have hfib : ∀ v ∈ Finset.Icc (-M) M,
      (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card ≤ m := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hvR : |(v : ℝ)| ≤ L + 1 := by
      rw [abs_le]
      have h1 : ((-M : ℤ) : ℝ) ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hv.2
      push_cast at h1
      constructor <;> linarith
    have hz : (H : ℤ) + n * v ≠ 0 := by
      intro h0
      have h0' : (H : ℝ) + n * v = 0 := by exact_mod_cast h0
      rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
      · nlinarith
      · have : (v : ℝ) ≤ -1 := by
          have : v ≤ -1 := by
            have : v < 0 := by exact_mod_cast hv0
            omega
          exact_mod_cast this
        nlinarith
    have hzabs : |(((H : ℤ) + n * v : ℤ) : ℝ)| < (L + 2) * n := by
      push_cast
      calc |(H : ℝ) + n * v| ≤ |(H : ℝ)| + |(n : ℝ) * v| := abs_add_le _ _
      _ = H + n * |(v : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hH0R.le, abs_of_nonneg hn.le]
      _ < n + n * (L + 1) := by nlinarith
      _ = (L + 2) * n := by ring
    have hpow := pow_card_le_of_primes_dvd (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) y
      (by linarith)
      (fun r hr => hR r (Finset.mem_filter.1 hr).1) _ hz (fun r hr => (Finset.mem_filter.1 hr).2)
    by_contra hcon
    push Not at hcon
    have : y ^ (m + 1) ≤ y ^ (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
      pow_le_pow_right₀ hy hcon
    linarith
  -- the bad set is covered by the fibres
  have hsub : R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) ⊆
      (Finset.Icc (-M) M).biUnion (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrR, hrbad⟩ := hr
    obtain ⟨v, hv⟩ := ht r hrR
    have hvR : ((r : ℝ) * t r - H) = n * v := by exact_mod_cast hv
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · have h1 : (n : ℝ) * |(v : ℝ)| < (L + 1) * n := by
        calc (n : ℝ) * |(v : ℝ)| = |(n : ℝ) * v| := by rw [abs_mul, abs_of_pos hn]
        _ = |(r : ℝ) * t r - H| := by rw [hvR]
        _ ≤ |(r : ℝ) * t r| + |(H : ℝ)| := abs_sub _ _
        _ < L * n + n := by rw [abs_of_nonneg hH0R.le]; linarith
        _ = (L + 1) * n := by ring
      have h2 : |(v : ℝ)| < L + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at h2
      rw [Finset.mem_Icc]
      constructor
      · have : -v ≤ M := Int.le_floor.2 (by push_cast; linarith)
        linarith
      · exact Int.le_floor.2 (by linarith)
    · rw [Finset.mem_filter]
      refine ⟨hrR, ⟨t r, ?_⟩⟩
      linear_combination -hv
  have hcard : (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card ≤ (2 * M.toNat + 1) * m := by
    calc (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card
        ≤ ((Finset.Icc (-M) M).biUnion
            (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, m := Finset.sum_le_sum hfib
    _ = (2 * M.toNat + 1) * m := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega
  have hMnat : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by
    have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
    exact_mod_cast this
  calc ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ)
      ≤ (((2 * M.toNat + 1) * m : ℕ) : ℝ) := by exact_mod_cast hcard
  _ = (2 * (M : ℝ) + 1) * m := by push_cast; rw [hMnat]
  _ ≤ (2 * (L + 1) + 1) * m := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

/-! ### Step 3: elementary inequalities for large `w` -/

lemma ineq_bad (w : ℝ) (hw : 10 ≤ w) :
    (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
  have h10 : 0 < w ^ 10 := by positivity
  have h28 : 6 ≤ w ^ 28 := by
    calc (6 : ℝ) ≤ 10 ^ 28 := by norm_num
    _ ≤ w ^ 28 := pow_le_pow_left₀ (by norm_num) hw 28
  have e1 : w ^ 38 = w ^ 28 * w ^ 10 := by ring
  have e2 : w ^ 39 = w * w ^ 38 := by ring
  have h38 : 6 * w ^ 10 ≤ w ^ 38 := by rw [e1]; nlinarith
  have h38' : 0 ≤ w ^ 38 := by positivity
  have h39 : 10 * w ^ 38 ≤ w ^ 39 := by rw [e2]; nlinarith
  have : (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) = 4 * w ^ 38 + 6 * w ^ 10 := by ring
  rw [this]
  linarith

lemma ineq_good (w : ℝ) (hw : 10 ≤ w) :
    2 * w ^ 10 ≤ (w ^ 39 / 2) * (4 / (9 * w ^ 24)) := by
  have hw0 : 0 < w := by linarith
  have e : (w ^ 39 / 2) * (4 / (9 * w ^ 24)) = 2 / 9 * w ^ 15 := by
    field_simp
    ring
  rw [e]
  have h5 : 9 ≤ w ^ 5 := by
    calc (9 : ℝ) ≤ 10 ^ 5 := by norm_num
    _ ≤ w ^ 5 := pow_le_pow_left₀ (by norm_num) hw 5
  have e2 : w ^ 15 = w ^ 5 * w ^ 10 := by ring
  rw [e2]
  have h10 : 0 < w ^ 10 := by positivity
  nlinarith

lemma ineq_exp (w : ℝ) (hw : 10 ≤ w) : w ^ 28 + 2 ≤ Real.exp (w ^ 10) := by
  have h := Real.pow_div_factorial_le_exp (w ^ 10) (by positivity) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have e : (w ^ 10) ^ 3 = w ^ 2 * w ^ 28 := by ring
  rw [e] at h
  have h2 : 100 ≤ w ^ 2 := by nlinarith
  have h28 : 1 ≤ w ^ 28 := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ w ^ 28)]

lemma ineq_e (w : ℝ) (hw : 10 ≤ w) : Real.exp 1 ≤ w ^ 40 / 4 := by
  have h := Real.exp_one_lt_three
  have : (10 : ℝ) ^ 40 ≤ w ^ 40 := pow_le_pow_left₀ (by norm_num) hw 40
  have h' : (3 : ℝ) ≤ 10 ^ 40 / 4 := by norm_num
  linarith

/-! ### Step 4: the bound on each nontrivial Fourier coefficient -/

theorem norm_prod_le (n : ℕ) [NeZero n] (w : ℝ) (hw : 10 ≤ w)
    (hn_exp : (n : ℝ) = Real.exp (w ^ 10))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ w ^ 40 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * w ^ 40)
    (hk : w ^ 39 ≤ R.card) (h : ZMod n) (hh : h ≠ 0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
  have hw0 : 0 < w := by linarith
  have hnpos : (0 : ℝ) < n := by rw [hn_exp]; exact Real.exp_pos _
  set H := h.val with hHdef
  have hH0 : 0 < H := ZMod.val_pos.2 hh
  have hHn : H < n := ZMod.val_lt h
  set t : ℕ → ℤ := fun r => (h * ((r : ZMod n))⁻¹).valMinAbs with htdef
  have hdiv : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H := by
    intro r hr
    have hcop : Nat.Coprime r n := ((hR r hr).1.coprime_iff_not_dvd).2 (hR r hr).2.1
    have h1 : (((r : ℤ) * t r : ℤ) : ZMod n) = ((H : ℤ) : ZMod n) := by
      push_cast
      simp only [htdef, ZMod.coe_valMinAbs, hHdef, ZMod.natCast_zmod_val]
      rw [mul_left_comm, ZMod.coe_mul_inv_eq_one r hcop, mul_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1.symm
  set L : ℝ := w ^ 28 with hLdef
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * w ^ 10⌋₊ := by
    have he := ineq_e w hw
    apply card_bad_le n H hH0 hHn R (w ^ 40 / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have hL2 : L + 2 ≤ n := by rw [hn_exp, hLdef]; exact ineq_exp w hw
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * w ^ 10) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * w ^ 10) < Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) ≤ (w ^ 40 / 4) ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he _
      linarith
    · have : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 0
        simp at this
        linarith [Real.add_one_le_exp 1]
      linarith
    · intro r hr
      exact ⟨(hR r hr).1, (hR r hr).2.2.1⟩
  have hBhalf : (B.card : ℝ) ≤ R.card / 2 := by
    have h1 : (⌊2 * w ^ 10⌋₊ : ℝ) ≤ 2 * w ^ 10 := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * w ^ 10⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * w ^ 10) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
      rw [hLdef]; exact ineq_bad w hw
    linarith
  have hGcard : w ^ 39 / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * w ^ 24) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * w ^ 40 := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * w ^ 12 * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : w ^ 28 * n < w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by
        calc w ^ 28 * (n : ℝ) = L * n := by rw [hLdef]
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * w ^ 40 * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * w ^ 24) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * w ^ 24) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * w ^ 24)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    rw [norm_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not R (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)]
    have hB' : ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 ^ B.card := by
      calc ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ ∏ r ∈ B, (4 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun r hr => hbad r (Finset.mem_filter.1 hr).1)
      _ = 4 ^ B.card := Finset.prod_const _
    have hG' : ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ (4 * Real.exp (-a)) ^ G.card := by
      calc ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
          ≤ ∏ r ∈ G, (4 * Real.exp (-a)) :=
            Finset.prod_le_prod (fun _ _ => by positivity) hgood
      _ = (4 * Real.exp (-a)) ^ G.card := Finset.prod_const _
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * w ^ 10)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * w ^ 10 ≤ G.card * a := by
        calc 2 * w ^ 10 ≤ (w ^ 39 / 2) * a := by rw [hadef]; exact ineq_good w hw
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    have e1 : Real.exp (w ^ 10) ^ 2 = Real.exp (2 * w ^ 10) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod

end Lemma1Aux

/-! ### Step 5: Croot's Lemma 1 -/

theorem lemma1 : ∀ᶠ n : ℕ in atTop, ∀ R : Finset ℕ,
    (∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ (Real.log n) ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * (Real.log n) ^ 4) →
    (Real.log n) ^ (39 / 10 : ℝ) ≤ R.card →
    ∀ c : ZMod n, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod n))⁻¹ = c := by
  have hw : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ (Real.log n) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 10
  filter_upwards [hw, eventually_ge_atTop 2] with n hwn hn2 R hR hk c
  have : NeZero n := ⟨by omega⟩
  set w := (Real.log n) ^ (1 / 10 : ℝ) with hwdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog : Real.log n = w ^ 10 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  have hn_exp : (n : ℝ) = Real.exp (w ^ 10) := by
    rw [← hlog, Real.exp_log hnpos]
  have h4 : (Real.log n) ^ 4 = w ^ 40 := by rw [hlog]; ring
  have h39 : (Real.log n) ^ (39 / 10 : ℝ) = w ^ 39 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  refine Lemma1Aux.exists_subset_sum_of_norm_prod_le R (fun r => ((r : ZMod n))⁻¹) ?_ c
  intro h hh
  refine Lemma1Aux.norm_prod_le n w hwn hn_exp R ?_ ?_ h hh
  · intro r hr
    obtain ⟨h1, h2, h3, h5⟩ := hR r hr
    rw [h4] at h3 h5
    exact ⟨h1, h2, h3, h5⟩
  · rw [← h39]
    exact hk

end Croot
end

section
/-!
# Existence of pp-smooth numbers in dyadic-type ranges, avoiding a prime

For large `y`, every real `Z` with `1/4 ≤ Z ≤ y ^ 12` and every prime `p`, there is a
`y`-pp-smooth `s` with `Z ≤ s ≤ 4 Z` and `p ∤ s`.

(Without an upper bound on `Z` the statement would be false: every `y`-pp-smooth number divides
`lcm(1, …, y)`.)

Construction: if `Z ≤ y/3` use a power of `2` (or of `3` when `p = 2`), or `1` if `Z < 1`;
otherwise multiply by a prime `P ∈ (y/3, y]` with `P ≠ p` taken from a fixed finite set `T`
of such primes (each used at most once) and recurse on `Z / P`.  Since `Z ≤ y ^ k ≤ (y/3) ^ (2k)`
for `y ≥ 9`, a set `T` of `2k` primes suffices, and for large `y` there are that many primes in
`(y/3, y]` by `Croot.eventually_card_primes_Ioc_ge`.

Main results:
* `Croot.exists_ppSmooth_coprime_pow`: the statement for `Z ≤ y ^ k`, any fixed `k`;
* `Croot.exists_ppSmooth_coprime`: the case `k = 12`.
-/

namespace Croot

open Real Finset Filter

/-- A positive integer `n ≤ y` is `y`-pp-smooth. -/
lemma ppSmooth_of_le {y n : ℕ} (hn : n ≠ 0) (h : n ≤ y) : PPSmooth y n := fun p _ =>
  (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)).trans h

/-- Multiplying a `y`-pp-smooth number by a new prime `P ≤ y` keeps it `y`-pp-smooth. -/
lemma PPSmooth.prime_mul {y s P : ℕ} (h : PPSmooth y s) (hs : s ≠ 0) (hP : P.Prime)
    (hPy : P ≤ y) (hPs : ¬ P ∣ s) : PPSmooth y (P * s) := by
  intro r hr
  rw [Nat.primeFactors_mul hP.ne_zero hs, Finset.mem_union, hP.primeFactors,
    Finset.mem_singleton] at hr
  rw [Nat.factorization_mul hP.ne_zero hs, Finsupp.add_apply]
  rcases hr with hrP | hr
  · subst hrP
    rw [hP.factorization_self, Nat.factorization_eq_zero_of_not_dvd hPs, add_zero, pow_one]
    exact hPy
  · have hrP : r ≠ P := fun hrP => hPs (by rw [← hrP]; exact Nat.dvd_of_mem_primeFactors hr)
    rw [hP.factorization, Finsupp.single_apply, if_neg (Ne.symm hrP), zero_add]
    exact h r hr

/-- Base case of the construction: for `1/4 ≤ Z ≤ y/3` take `1` or a power of `2` or `3`. -/
lemma exists_ppSmooth_base {y p : ℕ} (hp : p.Prime) {Z : ℝ} (hZ1 : 1 / 4 ≤ Z)
    (hZ2 : Z ≤ (y : ℝ) / 3) :
    ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s ∧
      ∀ r : ℕ, r.Prime → r ∣ s → r ≤ 3 := by
  rcases lt_or_ge Z 1 with hZ | hZ
  · refine ⟨1, by rw [Nat.cast_one]; exact hZ.le, by rw [Nat.cast_one]; linarith,
      ppSmooth_one y, hp.not_dvd_one, ?_⟩
    intro r hr hr1
    exact absurd hr1 hr.not_dvd_one
  · obtain ⟨q, hq, hq3, hqp⟩ : ∃ q : ℕ, q.Prime ∧ q ≤ 3 ∧ q ≠ p := by
      by_cases h : p = 2
      · exact ⟨3, Nat.prime_three, le_rfl, by omega⟩
      · exact ⟨2, Nat.prime_two, by norm_num, fun h' => h h'.symm⟩
    have hZ0 : (0 : ℝ) ≤ Z := by linarith
    have hn0 : ⌊Z⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊Z⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hZ)
      omega
    set a := Nat.log q ⌊Z⌋₊ with ha
    have h1 : ⌊Z⌋₊ < q ^ (a + 1) := Nat.lt_pow_succ_log_self hq.one_lt _
    have h2 : q ^ a ≤ ⌊Z⌋₊ := Nat.pow_log_le_self q hn0
    have hlo : Z ≤ ((q ^ (a + 1) : ℕ) : ℝ) := by
      have h1' : ⌊Z⌋₊ + 1 ≤ q ^ (a + 1) := h1
      have : ((⌊Z⌋₊ + 1 : ℕ) : ℝ) ≤ ((q ^ (a + 1) : ℕ) : ℝ) := by exact_mod_cast h1'
      have h3 := Nat.lt_floor_add_one Z
      push_cast at this ⊢
      linarith
    have hhi : ((q ^ (a + 1) : ℕ) : ℝ) ≤ 3 * Z := by
      have h4 : q ^ (a + 1) ≤ 3 * ⌊Z⌋₊ := by
        rw [pow_succ]
        calc q ^ a * q ≤ ⌊Z⌋₊ * 3 := Nat.mul_le_mul h2 hq3
          _ = 3 * ⌊Z⌋₊ := Nat.mul_comm _ _
      have h5 : (⌊Z⌋₊ : ℝ) ≤ Z := Nat.floor_le hZ0
      have : ((q ^ (a + 1) : ℕ) : ℝ) ≤ ((3 * ⌊Z⌋₊ : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at this ⊢
      linarith
    refine ⟨q ^ (a + 1), hlo, by linarith, ?_, ?_, ?_⟩
    · apply ppSmooth_of_le (pow_ne_zero _ hq.ne_zero)
      have : ((q ^ (a + 1) : ℕ) : ℝ) ≤ (y : ℝ) := by linarith
      exact_mod_cast this
    · intro hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm
    · intro r hr hdvd
      rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hdvd)]
      exact hq3

/-- The recursive construction, by induction on the finite set `T` of available primes in
`(y/3, y]`: each prime of `T` is used at most once, which keeps the exact prime powers `≤ y`. -/
lemma exists_ppSmooth_aux {y p : ℕ} (hp : p.Prime) (hy : 9 ≤ y) :
    ∀ T : Finset ℕ, (∀ P ∈ T, P.Prime ∧ (y : ℝ) / 3 < P ∧ P ≤ y ∧ P ≠ p) →
    ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ ((y : ℝ) / 3) ^ (T.card + 1) →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s ∧
        ∀ r : ℕ, r.Prime → r ∣ s → r ∈ T ∨ r ≤ 3 := by
  have hy9 : (9 : ℝ) ≤ y := by exact_mod_cast hy
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ Z hZ1 hZ2
    rw [Finset.card_empty, zero_add, pow_one] at hZ2
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := exists_ppSmooth_base hp hZ1 hZ2
    exact ⟨s, h1, h2, h3, h4, fun r hr hrs => Or.inr (h5 r hr hrs)⟩
  | insert P T hPT ih =>
    intro hT Z hZ1 hZ2
    by_cases hZ : Z ≤ (y : ℝ) / 3
    · obtain ⟨s, h1, h2, h3, h4, h5⟩ := exists_ppSmooth_base hp hZ1 hZ
      exact ⟨s, h1, h2, h3, h4, fun r hr hrs => Or.inr (h5 r hr hrs)⟩
    rw [not_le] at hZ
    obtain ⟨hPp, hPlo, hPhi, hPne⟩ := hT P (Finset.mem_insert_self P T)
    have hT' : ∀ P' ∈ T, P'.Prime ∧ (y : ℝ) / 3 < P' ∧ P' ≤ y ∧ P' ≠ p :=
      fun P' h => hT P' (Finset.mem_insert_of_mem h)
    have hPy : (P : ℝ) ≤ y := by exact_mod_cast hPhi
    have hP0 : (0 : ℝ) < P := by linarith
    have hP3 : 3 < P := by
      have : (3 : ℝ) < P := by linarith
      exact_mod_cast this
    rw [Finset.card_insert_of_notMem hPT] at hZ2
    have hZ'1 : 1 / 4 ≤ Z / P := by
      rw [le_div_iff₀ hP0]; linarith
    have hZ'2 : Z / P ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by
      rw [div_le_iff₀ hP0]
      have hpow0 : (0 : ℝ) ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by positivity
      calc Z ≤ ((y : ℝ) / 3) ^ (T.card + 1 + 1) := hZ2
        _ = ((y : ℝ) / 3) ^ (T.card + 1) * ((y : ℝ) / 3) := pow_succ _ _
        _ ≤ ((y : ℝ) / 3) ^ (T.card + 1) * P := mul_le_mul_of_nonneg_left hPlo.le hpow0
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := ih hT' (Z / P) hZ'1 hZ'2
    have hs0 : s ≠ 0 := by
      have : (0 : ℝ) < s := by linarith
      exact_mod_cast this.ne'
    have hPs : ¬ P ∣ s := by
      intro hdvd
      rcases h5 P hPp hdvd with h | h
      · exact hPT h
      · omega
    refine ⟨P * s, ?_, ?_, h3.prime_mul hs0 hPp hPhi hPs, ?_, ?_⟩
    · rw [div_le_iff₀ hP0] at h1
      push_cast
      linarith
    · push_cast
      calc (P : ℝ) * s ≤ P * (4 * (Z / P)) := mul_le_mul_of_nonneg_left h2 hP0.le
        _ = 4 * Z := by field_simp
    · intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact hPne ((Nat.prime_dvd_prime_iff_eq hp hPp).mp h).symm
      · exact h4 h
    · intro r hr hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · left
        rw [(Nat.prime_dvd_prime_iff_eq hr hPp).mp h]
        exact Finset.mem_insert_self P T
      · rcases h5 r hr h with h' | h'
        · exact Or.inl (Finset.mem_insert_of_mem h')
        · exact Or.inr h'

/-- For every `m`, eventually `m ≤ x / (5 log x)`. -/
lemma eventually_natCast_le_div_log (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, (m : ℝ) ≤ x / (5 * Real.log x) := by
  have hc : (0 : ℝ) < 1 / (5 * ((m : ℝ) + 1)) := by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc, eventually_ge_atTop (3 : ℝ)]
    with x hx hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log x ≤ 1 / (5 * ((m : ℝ) + 1)) * x := by
    have h := hx
    simp only [id, Real.norm_eq_abs] at h
    rwa [abs_of_pos hlog, abs_of_pos hx0] at h
  have h2 : 5 * ((m : ℝ) + 1) * Real.log x ≤ x := by
    calc 5 * ((m : ℝ) + 1) * Real.log x
        ≤ 5 * ((m : ℝ) + 1) * (1 / (5 * ((m : ℝ) + 1)) * x) := by gcongr
      _ = x := by field_simp
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- For every `m`, eventually there are at least `m` primes in `(⌊10 y / 27⌋, y] ⊆ (y/3, y]`. -/
lemma eventually_card_primes_third_ge (m : ℕ) : ∀ᶠ y : ℕ in atTop,
    m ≤ ((Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime).card := by
  have ht : Tendsto (fun y : ℕ => (10 / 27 : ℝ) * y) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [ht.eventually (eventually_card_primes_Ioc_ge.and
    (eventually_natCast_le_div_log m))] with y hy
  obtain ⟨h1, h2⟩ := hy
  have e : (27 / 10 : ℝ) * ((10 / 27 : ℝ) * y) = y := by ring
  rw [e, Nat.floor_natCast] at h1
  have : (m : ℝ) ≤ (((Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime).card : ℝ) := h2.trans h1
  exact_mod_cast this

/-- Existence of `y`-pp-smooth numbers in `[Z, 4 Z]` coprime to a given prime, for
`1/4 ≤ Z ≤ y ^ k` (any fixed exponent `k`) and all large `y`. -/
theorem exists_ppSmooth_coprime_pow (k : ℕ) : ∀ᶠ y : ℕ in atTop, ∀ p : ℕ, p.Prime →
    ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y : ℝ) ^ k →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s := by
  filter_upwards [eventually_card_primes_third_ge (2 * k + 1), eventually_ge_atTop 9]
    with y hcard hy9 p hp Z hZ1 hZ2
  have hy9' : (9 : ℝ) ≤ y := by exact_mod_cast hy9
  set S := (Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime with hS
  set T := S.erase p with hT
  have hTcard : 2 * k ≤ T.card := by
    have h : S.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
    omega
  have hTprop : ∀ P ∈ T, P.Prime ∧ (y : ℝ) / 3 < P ∧ P ≤ y ∧ P ≠ p := by
    intro P hP
    rw [hT, Finset.mem_erase, hS, Finset.mem_filter, Finset.mem_Ioc] at hP
    obtain ⟨hPp, ⟨hlo, hhi⟩, hprime⟩ := hP
    refine ⟨hprime, ?_, hhi, hPp⟩
    have h := (Nat.floor_lt (by positivity)).mp hlo
    linarith
  have hZ' : Z ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by
    have h3 : (1 : ℝ) ≤ (y : ℝ) / 3 := by linarith
    have hy0 : (0 : ℝ) ≤ y := by linarith
    calc Z ≤ (y : ℝ) ^ k := hZ2
      _ ≤ (((y : ℝ) / 3) ^ 2) ^ k := by
          apply pow_le_pow_left₀ hy0
          nlinarith
      _ = ((y : ℝ) / 3) ^ (2 * k) := by rw [← pow_mul]
      _ ≤ ((y : ℝ) / 3) ^ (T.card + 1) := pow_le_pow_right₀ h3 (by omega)
  obtain ⟨s, h1, h2, h3, h4, -⟩ := exists_ppSmooth_aux hp hy9 T hTprop Z hZ1 hZ'
  exact ⟨s, h1, h2, h3, h4⟩

/-- For large `y`, every prime `p` and every real `Z` with `1/4 ≤ Z ≤ y ^ 12`, there is a
`y`-pp-smooth `s` with `Z ≤ s ≤ 4 Z` and `p ∤ s`. -/
theorem exists_ppSmooth_coprime : ∀ᶠ y : ℕ in atTop, ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z →
    Z ≤ (y : ℝ) ^ 12 → ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s :=
  exists_ppSmooth_coprime_pow 12

end Croot
end

section
/-!
# The algebraic core of Croot's prime-power elimination step

Let `q = p ^ a` be a prime power and `x` a rational whose reduced denominator is `q * v'`
with `p ∤ v'`.  If `s` is coprime to `p` and `R'` is a set of primes different from `p` with
`∑_{r ∈ R'} r⁻¹ ≡ x.num · v'⁻¹ · s (mod q)`, then the reduced denominator of
`x - ∑_{r ∈ R'} 1/(q s r)` divides `lcm (v', s r : r ∈ R')`; in particular `p` no longer
appears in it.
-/

namespace Croot

open Finset

/-- If `x * L` is an integer divisible by `q` (with `L, q > 0`), then `(x / q).den ∣ L`. -/
lemma den_div_dvd_of_mul_eq {x : ℚ} {L q : ℕ} (hL : 0 < L) (hq : 0 < q) {W : ℤ}
    (hW : x * L = W) (hqW : (q : ℤ) ∣ W) : (x / q).den ∣ L := by
  obtain ⟨W', rfl⟩ := hqW
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hx : x / q = (W' : ℚ) / (L : ℤ) := by
    have : x = ((q : ℤ) * W' : ℤ) / (L : ℚ) := by
      field_simp
      exact_mod_cast hW
    rw [this]
    push_cast
    field_simp
  have h := Rat.den_dvd W' (L : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [hx]
  exact_mod_cast h

/-- Algebraic elimination step. -/
theorem den_sub_sum_dvd {p a : ℕ} (hp : p.Prime) (_ha : 0 < a) {x : ℚ} {v' : ℕ}
    (hden : x.den = p ^ a * v') (hv' : ¬ p ∣ v') {s : ℕ} (hs : 0 < s) (hps : ¬ p ∣ s)
    {R' : Finset ℕ} (hR' : ∀ r ∈ R', r.Prime ∧ r ≠ p)
    (hsum : ∑ r ∈ R', ((r : ZMod (p ^ a)))⁻¹ =
      (x.num : ZMod (p ^ a)) * ((v' : ZMod (p ^ a)))⁻¹ * (s : ZMod (p ^ a))) :
    (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r)).den ∣ (insert v' (R'.image (s * ·))).lcm id := by
  set q := p ^ a with hqdef
  set L := (insert v' (R'.image (s * ·))).lcm id with hLdef
  have hq0 : 0 < q := pow_pos hp.pos a
  have hv'0 : 0 < v' := by
    rcases Nat.eq_zero_or_pos v' with h | h
    · exfalso; have := x.den_pos; rw [hden, h, mul_zero] at this; exact lt_irrefl 0 this
    · exact h
  have hr0 : ∀ r ∈ R', 0 < r := fun r hr => (hR' r hr).1.pos
  have h0notin : 0 ∉ insert v' (R'.image (s * ·)) := by
    simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨hv'0.ne, fun r hr h => Nat.mul_ne_zero hs.ne' (hr0 r hr).ne' h⟩
  have hL0 : 0 < L := by
    apply Nat.pos_of_ne_zero
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    simpa using h0notin
  -- divisibility facts
  have hv'L : v' ∣ L := Finset.dvd_lcm (Finset.mem_insert_self _ _)
  have hsrL : ∀ r ∈ R', s * r ∣ L := fun r hr =>
    Finset.dvd_lcm (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hr))
  -- coprimality with q
  have hcop_v' : Nat.Coprime v' q := by
    rw [hqdef]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hv').symm
  have hcop_s : Nat.Coprime s q := by
    rw [hqdef]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hps).symm
  have hcop_r : ∀ r ∈ R', Nat.Coprime r q := by
    intro r hr
    rw [hqdef]
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes (hR' r hr).1 hp).2 (hR' r hr).2
  -- the integer W := (q x - ∑ 1/(s r)) * L
  set W : ℤ := x.num * ((L / v' : ℕ) : ℤ) - ∑ r ∈ R', ((L / (s * r) : ℕ) : ℤ) with hWdef
  have hqx : (q : ℚ) * x = (x.num : ℚ) / v' := by
    have hx : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
    have hden' : (x.den : ℚ) = (q : ℚ) * v' := by exact_mod_cast hden
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hv : (v' : ℚ) ≠ 0 := by exact_mod_cast hv'0.ne'
    conv_lhs => rw [← hx]
    rw [hden']
    field_simp
  have hmain : (q * (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r))) * L = W := by
    rw [hWdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [mul_sub, hqx, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Nat.cast_div hv'L (by exact_mod_cast hv'0.ne')]
      field_simp
    · refine Finset.sum_congr rfl fun r hr => ?_
      rw [Nat.cast_div (hsrL r hr) (by
        have := Nat.mul_ne_zero hs.ne' (hr0 r hr).ne'
        exact_mod_cast this)]
      have hq' : (q : ℚ) = (p : ℚ) ^ a := by rw [hqdef]; push_cast; ring
      rw [hq']
      have hpa : ((p : ℚ) ^ a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      have hsr : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
      have hrr : (r : ℚ) ≠ 0 := by exact_mod_cast (hr0 r hr).ne'
      push_cast
      field_simp
  -- q divides W, computed in ZMod q
  have hqW : (q : ℤ) ∣ W := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hv'u : (v' : ZMod q) * (v' : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one v' hcop_v'
    have hsu : (s : ZMod q) * (s : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one s hcop_s
    have hru : ∀ r ∈ R', (r : ZMod q) * (r : ZMod q)⁻¹ = 1 :=
      fun r hr => ZMod.coe_mul_inv_eq_one r (hcop_r r hr)
    -- L / v' ≡ L * v'⁻¹ and L / (s r) ≡ L * s⁻¹ * r⁻¹
    have hLv : ((L / v' : ℕ) : ZMod q) = (L : ZMod q) * (v' : ZMod q)⁻¹ := by
      have h1 : (v' : ZMod q) * ((L / v' : ℕ) : ZMod q) = (L : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hv'L]
      calc ((L / v' : ℕ) : ZMod q) = ((v' : ZMod q)⁻¹ * (v' : ZMod q)) * ((L / v' : ℕ) : ZMod q) := by
            rw [mul_comm ((v' : ZMod q)⁻¹), hv'u, one_mul]
        _ = (L : ZMod q) * (v' : ZMod q)⁻¹ := by rw [mul_assoc, h1, mul_comm]
    have hLsr : ∀ r ∈ R', ((L / (s * r) : ℕ) : ZMod q) =
        (L : ZMod q) * (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ := by
      intro r hr
      have h1 : (s : ZMod q) * (r : ZMod q) * ((L / (s * r) : ℕ) : ZMod q) = (L : ZMod q) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hsrL r hr)]
      calc ((L / (s * r) : ℕ) : ZMod q)
          = ((s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ * ((s : ZMod q) * (r : ZMod q))) *
              ((L / (s * r) : ℕ) : ZMod q) := by
            rw [show (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ * ((s : ZMod q) * (r : ZMod q)) =
                ((s : ZMod q) * (s : ZMod q)⁻¹) * ((r : ZMod q) * (r : ZMod q)⁻¹) by ring,
              hsu, hru r hr, one_mul, one_mul]
        _ = (L : ZMod q) * (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ := by
            rw [mul_assoc, h1]; ring
    rw [hWdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [hLv, Finset.sum_congr rfl hLsr]
    rw [show ∑ x ∈ R', (L : ZMod q) * (s : ZMod q)⁻¹ * (x : ZMod q)⁻¹ =
        (L : ZMod q) * (s : ZMod q)⁻¹ * ∑ x ∈ R', (x : ZMod q)⁻¹ by rw [Finset.mul_sum], hsum]
    have : (L : ZMod q) * (s : ZMod q)⁻¹ * ((x.num : ZMod q) * (v' : ZMod q)⁻¹ * (s : ZMod q)) =
        (L : ZMod q) * (v' : ZMod q)⁻¹ * (x.num : ZMod q) * ((s : ZMod q) * (s : ZMod q)⁻¹) := by
      ring
    rw [this, hsu]
    ring
  -- conclude
  have hfinal := den_div_dvd_of_mul_eq (x := q * (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r)))
    hL0 hq0 hmain hqW
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  rwa [mul_div_cancel_left₀ _ hq0'] at hfinal

end Croot
end

section
/-!
# Croot's Proposition 1: clearing large prime powers from the denominator

From the harmonic block `(N, M]` (with `e N ≤ M ≤ e N + 3`) we remove a set `D` of small
reciprocal mass so that the reduced denominator of `∑_{n ∈ (N,M] \ D} 1/n` is
`⌊N^{1/12}⌋`-pp-smooth.  We also keep `D` large enough (it contains all primes in `(N, M]`)
so that the residual `1 - ∑` is not too small.

## Proof outline

Write `H(S) = ∑_{n ∈ S} 1/n`, `I = (N, M]`, `Q = ⌊N / (log N)^4⌋`, `y₁ = ⌊N^{1/12}⌋`.

* `D₀ = bigPP N M Q` is the set of `n ∈ I` that are not `Q`-pp-smooth.  It contains every prime
  of `(N, 2.7 N]`, so `H(D₀) ≥ 1/(15 log N)` (`recipSum_bigPP_ge`), and every element of it is
  divisible by a prime power in `(Q, 3N]`, so `H(D₀) → 0` (`recipSum_bigPP_le`).
* Downward induction on the threshold `t` from `Q` to `y₁` (`clear_all`) maintaining
  `ClearInv`: if the denominator of `H(I \ D)` is `t`-pp-smooth but not `(t-1)`-pp-smooth, then
  `t = p^a` exactly divides it; we choose a `y₁`-pp-smooth `s ≈ N / (t (log t)^4)` coprime to
  `p` and a set `R` of `≥ (log t)^{3.9}` primes `r ∈ (N/(ts), 2.7 N/(ts)]` (`exists_s_R`), and
  Lemma 1 gives `T ⊆ R` such that removing `{t s r : r ∈ T}` kills the factor `p^a`
  (`den_sub_sum_dvd`), at a cost of at most `3 (log N)^4 / N` in mass (`step_main`).
* The total extra mass is `≤ #{prime powers ≤ Q} · 3 (log N)^4 / N → 0`.
-/

namespace Croot

open Real Finset Filter

namespace P1

/-! ## Arithmetic facts about pp-smoothness -/

lemma ppSmooth_prime {y r : ℕ} (hr : r.Prime) (hry : r ≤ y) : PPSmooth y r := by
  intro q hq
  rw [hr.primeFactors, Finset.mem_singleton] at hq
  subst hq
  rw [hr.factorization_self, pow_one]
  exact hry

lemma ppSmooth_primePow {y p a : ℕ} (hp : p.Prime) (h : p ^ a ≤ y) : PPSmooth y (p ^ a) := by
  intro q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hq' : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqprime hp).1
      (hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
  subst hq'
  rw [hqprime.factorization_pow, Finsupp.single_eq_same]
  exact h

lemma ppSmooth_mul_of_coprime {y a b : ℕ} (ha : PPSmooth y a) (hb : PPSmooth y b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : Nat.Coprime a b) : PPSmooth y (a * b) := by
  rw [← hab.lcm_eq_mul]
  exact ppSmooth_of_dvd_lcmUpto (Nat.lcm_dvd (ha.dvd_lcmUpto ha0) (hb.dvd_lcmUpto hb0))

lemma not_ppSmooth_primePow_mul {p a c : ℕ} (hp : p.Prime) (ha : 0 < a) (hc : c ≠ 0)
    (hpc : ¬ p ∣ c) : ¬ PPSmooth (p ^ a - 1) (p ^ a * c) := by
  intro h
  have hmem : p ∈ (p ^ a * c).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _,
      mul_ne_zero (pow_ne_zero _ hp.ne_zero) hc⟩
  have h1 := h p hmem
  have hfac : (p ^ a * c).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hc, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpc,
      add_zero]
  rw [hfac] at h1
  have : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.pos
  omega

lemma ppSmooth_sub_one_of_not_dvd {p a v : ℕ} (hp : p.Prime) (h : PPSmooth (p ^ a) v)
    (hv : ¬ p ∣ v) : PPSmooth (p ^ a - 1) v := by
  intro q hq
  have h1 := h q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqv := Nat.dvd_of_mem_primeFactors hq
  have hv0 : v ≠ 0 := (Nat.mem_primeFactors.1 hq).2.2
  have hqp : q ≠ p := fun e => hv (e ▸ hqv)
  have hne : q ^ v.factorization q ≠ p ^ a := by
    intro e
    have hk : v.factorization q ≠ 0 := (hqprime.factorization_pos_of_dvd hv0 hqv).ne'
    have : q ∣ p ^ a := e ▸ dvd_pow_self q hk
    exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).1 (hqprime.dvd_of_dvd_pow this))
  omega

lemma exists_primePow_eq_of_not_ppSmooth {t n : ℕ} (h : PPSmooth t n)
    (h' : ¬ PPSmooth (t - 1) n) : ∃ p ∈ n.primeFactors, p ^ n.factorization p = t := by
  simp only [PPSmooth, not_forall, not_le, exists_prop] at h'
  obtain ⟨p, hp, hlt⟩ := h'
  exact ⟨p, hp, le_antisymm (h p hp) (by omega)⟩

lemma card_primeFactors_le_log {s : ℕ} (hs : 0 < s) :
    (s.primeFactors.card : ℝ) ≤ Real.log s / Real.log 2 := by
  have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ s.primeFactors, p ≤ s := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
  have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  have := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at this

/-! ## Reciprocal sums -/

lemma recipSum_cast (S : Finset ℕ) : (recipSum S : ℝ) = ∑ n ∈ S, (1 : ℝ) / n := by
  simp [recipSum]

lemma recipSum_le_card_div {S : Finset ℕ} {N : ℕ} (hN : 0 < N) (h : ∀ n ∈ S, N < n) :
    (recipSum S : ℝ) ≤ S.card / N := by
  rw [recipSum_cast]
  calc ∑ n ∈ S, (1 : ℝ) / n ≤ ∑ n ∈ S, (1 : ℝ) / N := by
        apply Finset.sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le (by exact_mod_cast hN)
        exact_mod_cast (h n hn).le
    _ = S.card / N := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma card_multiples_Ioc_le {N M q : ℕ} (hq : 0 < q) :
    ((Ioc N M).filter (fun n => q ∣ n)).card ≤ M / q - N / q := by
  calc ((Ioc N M).filter (fun n => q ∣ n)).card
      ≤ ((Ioc (N / q) (M / q)).image (fun k => q * k)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
        rw [Finset.mem_image]
        refine ⟨k, Finset.mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
        · exact (Nat.div_lt_iff_lt_mul hq).2 (by rw [mul_comm]; exact h1)
        · exact (Nat.le_div_iff_mul_le hq).2 (by rw [mul_comm]; exact h2)
    _ ≤ (Ioc (N / q) (M / q)).card := Finset.card_image_le
    _ = M / q - N / q := Nat.card_Ioc _ _

lemma card_multiples_Ioc_le_real {N M q : ℕ} (hq : 0 < q) (hNM : N ≤ M) :
    (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) ≤ ((M : ℝ) - N) / q + 1 := by
  have h1 := card_multiples_Ioc_le (N := N) (M := M) hq
  have h2 : N / q ≤ M / q := Nat.div_le_div_right hNM
  have h3 : (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) ≤
      ((M / q : ℕ) : ℝ) - ((N / q : ℕ) : ℝ) := by
    rw [← Nat.cast_sub h2]; exact_mod_cast h1
  have h4 : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q := Nat.cast_div_le
  have h5 : (N : ℝ) / q - 1 < ((N / q : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor ((N : ℝ) / q)
    rwa [Nat.floor_div_eq_div] at this
  have : ((M : ℝ) - N) / q = (M : ℝ) / q - (N : ℝ) / q := sub_div _ _ _
  linarith

/-! ## The set of non-`Q`-pp-smooth elements of `(N, M]` -/

open Classical in
/-- The elements of `(N, M]` that are not `Q`-pp-smooth. -/
noncomputable def bigPP (N M Q : ℕ) : Finset ℕ := (Ioc N M).filter (fun n => ¬ PPSmooth Q n)

lemma mem_bigPP {N M Q n : ℕ} : n ∈ bigPP N M Q ↔ n ∈ Ioc N M ∧ ¬ PPSmooth Q n := by
  rw [bigPP, Finset.mem_filter]

lemma recipSum_bigPP_le {N M Q : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hM : M ≤ 3 * N) :
    (recipSum (bigPP N M Q) : ℝ) ≤
      2 * ∑ q ∈ (Ioc Q (3 * N)).filter IsPrimePow, (1 : ℝ) / q +
        (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) / N := by
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc Q (3 * N)).filter IsPrimePow := ⟨_, rfl⟩
  rw [← hP]
  -- each element of `bigPP` has an exact prime-power divisor in `P`
  have hex : ∀ n ∈ bigPP N M Q, ∃ q ∈ P, q ∣ n := by
    intro n hn
    rw [mem_bigPP, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn1, hn2⟩, hns⟩ := hn
    simp only [PPSmooth, not_forall, not_le, exists_prop] at hns
    obtain ⟨p, hp, hlt⟩ := hns
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hn0 : n ≠ 0 := by omega
    refine ⟨p ^ n.factorization p, ?_, Nat.ordProj_dvd n p⟩
    rw [hP, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hlt, ?_⟩, ?_⟩
    · exact (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)).trans (hn2.trans hM)
    · exact (isPrimePow_nat_iff _).2
        ⟨p, _, hpp, hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp), rfl⟩
  have hfirst : (recipSum (bigPP N M Q) : ℝ) ≤
      ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := by
    rw [recipSum_cast]
    calc ∑ n ∈ bigPP N M Q, (1 : ℝ) / n
        ≤ ∑ n ∈ bigPP N M Q, ∑ q ∈ P, (if q ∣ n then (1 : ℝ) / n else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨q, hq, hqn⟩ := hex n hn
          calc (1 : ℝ) / n = (if q ∣ n then (1 : ℝ) / n else 0) := by rw [if_pos hqn]
            _ ≤ ∑ q ∈ P, (if q ∣ n then (1 : ℝ) / n else 0) :=
              Finset.single_le_sum (f := fun q => if q ∣ n then (1 : ℝ) / n else 0)
                (fun q _ => by split_ifs <;> positivity) hq
      _ = ∑ q ∈ P, ∑ n ∈ bigPP N M Q, (if q ∣ n then (1 : ℝ) / n else 0) := Finset.sum_comm
      _ = ∑ q ∈ P, ∑ n ∈ (bigPP N M Q).filter (fun n => q ∣ n), (1 : ℝ) / n := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_filter]
      _ ≤ ∑ q ∈ P, ∑ n ∈ (Ioc N M).filter (fun n => q ∣ n), (1 : ℝ) / n := by
          apply Finset.sum_le_sum
          intro q _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset_filter _ (fun n hn => (mem_bigPP.1 hn).1)
          · intro _ _ _; positivity
      _ = ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := by
          simp only [recipSum_cast]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsecond : ∀ q ∈ P,
      (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) ≤ 2 / q + 1 / N := by
    intro q hq
    have hq0 : 0 < q := by
      rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hq; omega
    have h1 := recipSum_le_card_div hN (S := (Ioc N M).filter (fun n => q ∣ n))
      (fun n hn => (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1)
    have h2 := card_multiples_Ioc_le_real (N := N) (M := M) hq0 hNM
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hM' : (M : ℝ) ≤ 3 * N := by exact_mod_cast hM
    calc (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ)
        ≤ (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) / N := h1
      _ ≤ (((M : ℝ) - N) / q + 1) / N := by gcongr
      _ ≤ ((2 * N) / q + 1) / N := by gcongr; linarith
      _ = 2 / q + 1 / N := by field_simp
  calc (recipSum (bigPP N M Q) : ℝ)
      ≤ ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := hfirst
    _ ≤ ∑ q ∈ P, (2 / (q : ℝ) + 1 / N) := Finset.sum_le_sum hsecond
    _ = 2 * ∑ q ∈ P, (1 : ℝ) / q + (P.card : ℝ) / N := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      congr 1
      · exact Finset.sum_congr rfl fun q _ => by ring
      · ring

lemma recipSum_bigPP_ge {N M Q : ℕ} (hN : 0 < N) (hlogN : 0 < Real.log N) (hQN : Q ≤ N)
    (hM27 : (27 / 10 : ℝ) * N ≤ M) (hM3 : (M : ℝ) ≤ 3 * N)
    (hprime : (N : ℝ) / (5 * Real.log N) ≤
      (((Ioc ⌊(N : ℝ)⌋₊ ⌊(27 / 10 : ℝ) * N⌋₊).filter Nat.Prime).card : ℝ)) :
    1 / (15 * Real.log N) ≤ (recipSum (bigPP N M Q) : ℝ) := by
  rw [Nat.floor_natCast] at hprime
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc N ⌊(27 / 10 : ℝ) * N⌋₊).filter Nat.Prime :=
    ⟨_, rfl⟩
  rw [← hP] at hprime
  have hfl : ⌊(27 / 10 : ℝ) * N⌋₊ ≤ M := Nat.floor_le_of_le hM27
  have hPsub : P ⊆ bigPP N M Q := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    rw [mem_bigPP, Finset.mem_Ioc]
    refine ⟨⟨hp1, hp2.trans hfl⟩, fun hsm => ?_⟩
    have := hsm p (by rw [hpp.primeFactors]; exact Finset.mem_singleton_self p)
    rw [hpp.factorization_self, pow_one] at this
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∀ p ∈ P, (1 : ℝ) / (3 * N) ≤ 1 / (p : ℝ) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    apply one_div_le_one_div_of_le hp0
    have : (p : ℝ) ≤ M := by exact_mod_cast hp.1.2.trans hfl
    linarith
  have hl0 : Real.log N ≠ 0 := hlogN.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  calc 1 / (15 * Real.log N) = (N / (5 * Real.log N)) * (1 / (3 * N)) := by
        field_simp
        ring
    _ ≤ (P.card : ℝ) * (1 / (3 * N)) := by gcongr
    _ = ∑ p ∈ P, (1 : ℝ) / (3 * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ P, (1 : ℝ) / p := Finset.sum_le_sum hle
    _ = (recipSum P : ℝ) := (recipSum_cast P).symm
    _ ≤ (recipSum (bigPP N M Q) : ℝ) := by exact_mod_cast recipSum_mono hPsub

/-! ## The invariant of the elimination procedure -/

/-- The invariant at threshold `t`: `D₀ ⊆ D ⊆ (N, M]`, no element of `D` is `t`-pp-smooth,
the denominator of `H((N, M] \ D)` is `t`-pp-smooth, and the mass of `D` is controlled. -/
def ClearInv (N M Q : ℕ) (D₀ : Finset ℕ) (B : ℝ) (t : ℕ) (D : Finset ℕ) : Prop :=
  D₀ ⊆ D ∧ D ⊆ Ioc N M ∧ (∀ n ∈ D, ¬ PPSmooth t n) ∧
    PPSmooth t (recipSum (Ioc N M \ D)).den ∧
    (recipSum D : ℝ) ≤ (recipSum D₀ : ℝ) + (((Ioc t Q).filter IsPrimePow).card : ℝ) * B

lemma clearInv_base {N M Q : ℕ} {B : ℝ} : ClearInv N M Q (bigPP N M Q) B Q (bigPP N M Q) := by
  refine ⟨subset_rfl, fun n hn => (mem_bigPP.1 hn).1, fun n hn => (mem_bigPP.1 hn).2, ?_, ?_⟩
  · apply ppSmooth_den_recipSum
    · intro n hn
      rw [Finset.mem_sdiff] at hn
      by_contra h
      exact hn.2 (mem_bigPP.2 ⟨hn.1, h⟩)
    · intro h0
      rw [Finset.mem_sdiff, Finset.mem_Ioc] at h0
      omega
  · simp

lemma clearInv_sub_one {N M Q t : ℕ} {D₀ D : Finset ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hInv : ClearInv N M Q D₀ B t D) (hsm : PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den) :
    ClearInv N M Q D₀ B (t - 1) D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
  refine ⟨h1, h2, fun n hn hn' => h3 n hn (hn'.mono (Nat.sub_le _ _)), hsm, h5.trans ?_⟩
  have hc : ((Ioc t Q).filter IsPrimePow).card ≤ ((Ioc (t - 1) Q).filter IsPrimePow).card :=
    Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.sub_le _ _)))
  have hc' : (((Ioc t Q).filter IsPrimePow).card : ℝ) ≤
      ((Ioc (t - 1) Q).filter IsPrimePow).card := by exact_mod_cast hc
  linarith [mul_le_mul_of_nonneg_right hc' hB]

lemma clear_all {N M Q y₁ : ℕ} {D₀ : Finset ℕ} {B : ℝ}
    (hstep : ∀ t D, y₁ < t → t ≤ Q → ClearInv N M Q D₀ B t D →
      ∃ D', ClearInv N M Q D₀ B (t - 1) D')
    (hbase : ClearInv N M Q D₀ B Q D₀) :
    ∃ D, ClearInv N M Q D₀ B (Q - (Q - y₁)) D := by
  have key : ∀ j, j ≤ Q - y₁ → ∃ D, ClearInv N M Q D₀ B (Q - j) D := by
    intro j
    induction j with
    | zero => intro _; exact ⟨D₀, by rw [Nat.sub_zero]; exact hbase⟩
    | succ j ih =>
      intro hj
      obtain ⟨D, hD⟩ := ih (by omega)
      obtain ⟨D', hD'⟩ := hstep (Q - j) D (by omega) (by omega) hD
      exact ⟨D', by rwa [show Q - (j + 1) = Q - j - 1 by omega]⟩
  exact key _ le_rfl

/-! ## The analytic input of one elimination step -/

lemma exists_s_R {N M t y₁ p : ℕ} {x₀ : ℝ}
    (hprimes : ∀ x : ℝ, x₀ ≤ x → x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ))
    (hSE : ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y₁ : ℝ) ^ 12 →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y₁ s ∧ ¬ p ∣ s)
    (hy10 : (10 : ℝ) ≤ y₁) (hyt : (y₁ : ℝ) + 1 ≤ t) (hNy : (N : ℝ) < ((y₁ : ℝ) + 1) ^ 12)
    (hp : p.Prime) (hN0 : 0 < N)
    (hM : (27 / 10 : ℝ) * N ≤ M)
    (htN : (t : ℝ) ≤ N / Real.log N ^ 4)
    (hNt : Real.log N ≤ 12 * Real.log t)
    (hN1 : 1 < Real.log N)
    (ht4 : 4 ≤ t) (h3 : 3 * Real.log t ^ 4 < t) (hL1 : 1 ≤ Real.log t)
    (hLx : x₀ ≤ Real.log t ^ 4 / 4) (hL2 : 2 ≤ Real.log t ^ 4 / 4)
    (hcount : Real.log t ^ (39 / 10 : ℝ) ≤
      Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1) :
    ∃ s : ℕ, ∃ R : Finset ℕ, 0 < s ∧ ¬ p ∣ s ∧ PPSmooth y₁ s ∧
      (∀ r ∈ R, r.Prime ∧ ¬ r ∣ s ∧ r ≠ p ∧ N < t * s * r ∧ t * s * r ≤ M ∧ r < t ∧
        Real.log t ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * Real.log t ^ 4) ∧
      Real.log t ^ (39 / 10 : ℝ) ≤ R.card ∧ (R.card : ℝ) ≤ 3 * Real.log N ^ 4 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have ht4r : (4 : ℝ) ≤ t := by exact_mod_cast ht4
  have hlogN4 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ hN1.le
  have htN' : (t : ℝ) ≤ N := htN.trans (div_le_self hNr.le hlogN4)
  have hLN' : Real.log t ≤ Real.log N := Real.log_le_log ht0 htN'
  obtain ⟨L, hLdef⟩ : ∃ L, Real.log t = L := ⟨_, rfl⟩
  rw [hLdef] at h3 hL1 hLx hL2 hcount hNt hLN' ⊢
  have hL0 : 0 < L := by linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hL4N : L ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ hL0.le hLN' 4
  -- the parameter `Z`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = N / (t * L ^ 4) := ⟨_, rfl⟩
  have htL : 0 < (t : ℝ) * L ^ 4 := by positivity
  have hZpos : 0 < Z := by rw [hZ]; exact div_pos hNr htL
  have htZ : (t : ℝ) * L ^ 4 * Z = N := by rw [hZ]; field_simp
  have hZ1 : 1 ≤ Z := by
    rw [hZ, le_div_iff₀ htL, one_mul]
    calc (t : ℝ) * L ^ 4 ≤ N / Real.log N ^ 4 * Real.log N ^ 4 :=
          mul_le_mul htN hL4N (by positivity) (by positivity)
      _ = N := by field_simp
  -- `Z ≤ y₁ ^ 12`, as required by the existence of smooth numbers
  have hZy : Z ≤ (y₁ : ℝ) ^ 12 := by
    have hy0 : (0 : ℝ) < (y₁ : ℝ) + 1 := by linarith
    have h1 : Z * ((y₁ : ℝ) + 1) ≤ N := by
      have htt : (y₁ : ℝ) + 1 ≤ t * L ^ 4 := hyt.trans (le_mul_of_one_le_right ht0.le hL4)
      calc Z * ((y₁ : ℝ) + 1) ≤ Z * (t * L ^ 4) := mul_le_mul_of_nonneg_left htt hZpos.le
        _ = N := by rw [← htZ]; ring
    have h2 : Z < ((y₁ : ℝ) + 1) ^ 11 := by
      have : Z * ((y₁ : ℝ) + 1) < ((y₁ : ℝ) + 1) ^ 11 * ((y₁ : ℝ) + 1) := by
        calc Z * ((y₁ : ℝ) + 1) ≤ N := h1
          _ < ((y₁ : ℝ) + 1) ^ 12 := hNy
          _ = ((y₁ : ℝ) + 1) ^ 11 * ((y₁ : ℝ) + 1) := by ring
      exact lt_of_mul_lt_mul_right this hy0.le
    have h8 : 0 ≤ (y₁ : ℝ) ^ 11 := by positivity
    have h3 : ((y₁ : ℝ) + 1) ^ 11 ≤ (y₁ : ℝ) ^ 12 := by
      calc ((y₁ : ℝ) + 1) ^ 11 ≤ (11 / 10 * (y₁ : ℝ)) ^ 11 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 11
        _ = (11 / 10) ^ 11 * (y₁ : ℝ) ^ 11 := mul_pow _ _ _
        _ ≤ 3 * (y₁ : ℝ) ^ 11 := mul_le_mul_of_nonneg_right (by norm_num) h8
        _ ≤ (y₁ : ℝ) * (y₁ : ℝ) ^ 11 := mul_le_mul_of_nonneg_right (by linarith) h8
        _ = (y₁ : ℝ) ^ 12 := by ring
    linarith
  obtain ⟨s, hZs, hs4Z, hsy, hps⟩ := hSE p hp Z (by linarith) hZy
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hZpos hZs
  have hs0' : 0 < s := by exact_mod_cast hs0
  -- the parameter `X = N / (t s)`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = N / (t * s) := ⟨_, rfl⟩
  have hts : 0 < (t : ℝ) * s := by positivity
  have hXts : X * (t * s) = N := by rw [hX]; field_simp
  have hXle : X ≤ L ^ 4 := by
    rw [hX, div_le_iff₀ hts]
    calc (N : ℝ) = t * L ^ 4 * Z := htZ.symm
      _ ≤ t * L ^ 4 * s := by gcongr
      _ = L ^ 4 * (t * s) := by ring
  have hXge : L ^ 4 / 4 ≤ X := by
    rw [hX, le_div_iff₀ hts]
    calc L ^ 4 / 4 * (t * s) ≤ L ^ 4 / 4 * (t * (4 * Z)) := by gcongr
      _ = t * L ^ 4 * Z := by ring
      _ = N := htZ
  have hX2 : 2 ≤ X := hL2.trans hXge
  have hX0 : 0 < X := by linarith
  -- the primes in `(X, 2.7 X]`
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc ⌊X⌋₊ ⌊(27 / 10 : ℝ) * X⌋₊).filter Nat.Prime :=
    ⟨_, rfl⟩
  have hPcard : X / (5 * Real.log X) ≤ P.card := by
    rw [hP]; exact hprimes X (hLx.trans hXge)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogX' : Real.log X ≤ 4 * Real.log L := by
    simpa [Real.log_pow] using Real.log_le_log hX0 hXle
  have hPcard' : L ^ 4 / (80 * Real.log L) ≤ P.card := by
    calc L ^ 4 / (80 * Real.log L) = (L ^ 4 / 4) / (5 * (4 * Real.log L)) := by ring
      _ ≤ X / (5 * Real.log X) := div_le_div₀ hX0.le hXge (by linarith) (by linarith)
      _ ≤ P.card := hPcard
  -- remove the primes dividing `s`, and `p`
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, R = P.filter (fun r => ¬ r ∣ s ∧ r ≠ p) := ⟨_, rfl⟩
  have hPsub : P ⊆ R ∪ (s.primeFactors ∪ {p}) := by
    intro r hr
    by_cases h1 : r ∣ s
    · have hrp : r.Prime := by rw [hP, Finset.mem_filter] at hr; exact hr.2
      exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hrp, h1, hs0'.ne'⟩))
    · by_cases h2 : r = p
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.2 h2))
      · exact Finset.mem_union_left _ (by rw [hR]; exact Finset.mem_filter.2 ⟨hr, h1, h2⟩)
  have hcardP : (P.card : ℝ) ≤ R.card + s.primeFactors.card + 1 := by
    have h1 : P.card ≤ R.card + (s.primeFactors.card + 1) :=
      (Finset.card_le_card hPsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (by rw [Finset.card_singleton])) _))
    have h2 : (P.card : ℝ) ≤ R.card + (s.primeFactors.card + 1) := by exact_mod_cast h1
    linarith
  have hsN : (s : ℝ) ≤ N := by
    have htL4 : 4 ≤ (t : ℝ) * L ^ 4 := ht4r.trans (le_mul_of_one_le_right ht0.le hL4)
    have h4Z : 4 * Z ≤ N := by
      rw [hZ, mul_div_assoc', div_le_iff₀ htL]
      calc 4 * (N : ℝ) = N * 4 := by ring
        _ ≤ N * (t * L ^ 4) := mul_le_mul_of_nonneg_left htL4 hNr.le
    linarith
  have homega : (s.primeFactors.card : ℝ) ≤ 18 * L := by
    have h1 := card_primeFactors_le_log hs0'
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlogs : Real.log s ≤ 12 * L := (Real.log_le_log hs0 hsN).trans hNt
    calc (s.primeFactors.card : ℝ) ≤ Real.log s / Real.log 2 := h1
      _ ≤ 12 * L / (2 / 3) := div_le_div₀ (by linarith) hlogs (by norm_num) hlog2.le
      _ = 18 * L := by ring
  refine ⟨s, R, hs0', hps, hsy, ?_, ?_, ?_⟩
  · intro r hr
    rw [hR, Finset.mem_filter, hP, Finset.mem_filter, Finset.mem_Ioc] at hr
    obtain ⟨⟨⟨hr1, hr2⟩, hrp⟩, hrs, hrne⟩ := hr
    have hXr : X < r := (Nat.floor_lt hX0.le).1 hr1
    have hrX : (r : ℝ) ≤ 27 / 10 * X :=
      (Nat.cast_le.2 hr2).trans (Nat.floor_le (by positivity))
    refine ⟨hrp, hrs, hrne, ?_, ?_, ?_, ?_, ?_⟩
    · have : (N : ℝ) < t * s * r := by
        rw [← hXts]
        calc X * (t * s) < r * (t * s) := mul_lt_mul_of_pos_right hXr hts
          _ = t * s * r := by ring
      exact_mod_cast this
    · have : (t : ℝ) * s * r ≤ M := by
        calc (t : ℝ) * s * r ≤ t * s * (27 / 10 * X) := by gcongr
          _ = 27 / 10 * N := by rw [← hXts]; ring
          _ ≤ M := hM
      exact_mod_cast this
    · have : (r : ℝ) < t := by linarith
      exact_mod_cast this
    · linarith
    · linarith
  · linarith
  · have h1 : R.card ≤ (Ioc ⌊X⌋₊ ⌊(27 / 10 : ℝ) * X⌋₊).card := by
      rw [hR, hP]
      exact (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
    rw [Nat.card_Ioc] at h1
    have h2 : ⌊X⌋₊ ≤ ⌊(27 / 10 : ℝ) * X⌋₊ := Nat.floor_le_floor (by linarith)
    have h3' : (R.card : ℝ) ≤ (⌊(27 / 10 : ℝ) * X⌋₊ : ℝ) - ⌊X⌋₊ := by
      rw [← Nat.cast_sub h2]; exact_mod_cast h1
    have h4 : (⌊(27 / 10 : ℝ) * X⌋₊ : ℝ) ≤ 27 / 10 * X := Nat.floor_le (by positivity)
    have h5 : X - 1 < (⌊X⌋₊ : ℝ) := Nat.sub_one_lt_floor X
    linarith

/-! ## One elimination step -/

lemma step_main {N M Q y₁ t : ℕ} {D₀ D : Finset ℕ} {x₀ B : ℝ}
    (hprimes : ∀ x : ℝ, x₀ ≤ x → x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ))
    (hSE : ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y₁ : ℝ) ^ 12 →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y₁ s ∧ ¬ p ∣ s)
    (hy10 : (10 : ℝ) ≤ y₁) (hNy : (N : ℝ) < ((y₁ : ℝ) + 1) ^ 12)
    (hL1 : ∀ R : Finset ℕ, (∀ r ∈ R, r.Prime ∧ ¬ r ∣ t ∧ (Real.log t) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log t) ^ 4) → (Real.log t) ^ (39 / 10 : ℝ) ≤ R.card →
      ∀ c : ZMod t, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod t))⁻¹ = c)
    (hB : B = 3 * Real.log N ^ 4 / N)
    (hN0 : 0 < N)
    (hM : (27 / 10 : ℝ) * N ≤ M)
    (htN : (t : ℝ) ≤ N / Real.log N ^ 4)
    (hNt : Real.log N ≤ 12 * Real.log t)
    (hN1 : 1 < Real.log N)
    (hyt : y₁ < t) (htQ : t ≤ Q)
    (hconds : 4 ≤ t ∧ 3 * Real.log t ^ 4 < t ∧ 1 ≤ Real.log t ∧ x₀ ≤ Real.log t ^ 4 / 4 ∧
      2 ≤ Real.log t ^ 4 / 4 ∧
      Real.log t ^ (39 / 10 : ℝ) ≤
        Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1)
    (hInv : ClearInv N M Q D₀ B t D)
    (hns : ¬ PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den) :
    ∃ D', ClearInv N M Q D₀ B (t - 1) D' := by
  obtain ⟨ht4, h3, hL1', hLx, hL2, hcount⟩ := hconds
  obtain ⟨hD0, hDI, hDns, hsm, hmass⟩ := hInv
  obtain ⟨p, hpmem, hpt⟩ := exists_primePow_eq_of_not_ppSmooth hsm hns
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  -- the step data `s`, `R`
  have hyt' : (y₁ : ℝ) + 1 ≤ t := by exact_mod_cast hyt
  obtain ⟨s, R, hs0, hps, hsy, hR, hRcard, hRcard'⟩ :=
    exists_s_R hprimes hSE hy10 hyt' hNy hp hN0 hM htN hNt hN1 ht4 h3 hL1' hLx hL2 hcount
  obtain ⟨x, hx⟩ : ∃ x : ℚ, recipSum (Ioc N M \ D) = x := ⟨_, rfl⟩
  rw [hx] at hsm hns hpmem hpt
  have hden0 : x.den ≠ 0 := x.den_nz
  obtain ⟨a, ha_def⟩ : ∃ a, x.den.factorization p = a := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [← ha_def]; exact hp.factorization_pos_of_dvd hden0 (Nat.dvd_of_mem_primeFactors hpmem)
  rw [ha_def] at hpt
  obtain ⟨v', hv'_def⟩ : ∃ v', x.den / p ^ a = v' := ⟨_, rfl⟩
  have hden : x.den = p ^ a * v' := by
    rw [← hv'_def, ← ha_def]; exact (Nat.ordProj_mul_ordCompl_eq_self x.den p).symm
  have hv' : ¬ p ∣ v' := by
    rw [← hv'_def, ← ha_def]; exact Nat.not_dvd_ordCompl hp hden0
  subst hpt
  -- apply Lemma 1 modulo `p ^ a`
  have hRt : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ p ^ a ∧ (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 := by
    intro r hr
    obtain ⟨hrp, -, hrne, -, -, -, hr1, hr2⟩ := hR r hr
    refine ⟨hrp, fun hdvd => hrne ?_, hr1, hr2⟩
    exact (Nat.prime_dvd_prime_iff_eq hrp hp).1 (hrp.dvd_of_dvd_pow hdvd)
  obtain ⟨TR, hTR, hTsum⟩ := hL1 R hRt hRcard
    ((x.num : ZMod (p ^ a)) * ((v' : ZMod (p ^ a)))⁻¹ * (s : ZMod (p ^ a)))
  have hTR' : ∀ r ∈ TR, r.Prime ∧ ¬ r ∣ s ∧ r ≠ p ∧ N < p ^ a * s * r ∧
      p ^ a * s * r ≤ M ∧ r < p ^ a ∧ (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 :=
    fun r hr => hR r (hTR hr)
  have hpsr : ∀ r ∈ TR, ¬ p ∣ s * r := by
    intro r hr hdvd
    obtain ⟨hrp, -, hrne, -⟩ := hTR' r hr
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact hps h
    · exact hrne ((Nat.prime_dvd_prime_iff_eq hp hrp).1 h).symm
  have hsr0 : ∀ r ∈ TR, s * r ≠ 0 := fun r hr => mul_ne_zero hs0.ne' (hTR' r hr).1.ne_zero
  have hsr_smooth : ∀ r ∈ TR, PPSmooth (p ^ a - 1) (s * r) := by
    intro r hr
    obtain ⟨hrp, hrs, -, -, -, hrlt, -⟩ := hTR' r hr
    apply ppSmooth_mul_of_coprime (hsy.mono (by omega)) (ppSmooth_prime hrp (by omega))
      hs0.ne' hrp.ne_zero
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hrp).2 hrs)
  have hm_smooth : ∀ r ∈ TR, PPSmooth (p ^ a) (p ^ a * s * r) := by
    intro r hr
    rw [mul_assoc]
    exact ppSmooth_mul_of_coprime (ppSmooth_primePow hp le_rfl)
      ((hsr_smooth r hr).mono (Nat.sub_le _ _)) (pow_ne_zero _ hp.ne_zero) (hsr0 r hr)
      (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 (hpsr r hr)))
  have hm_ns : ∀ r ∈ TR, ¬ PPSmooth (p ^ a - 1) (p ^ a * s * r) := by
    intro r hr
    rw [mul_assoc]
    exact not_ppSmooth_primePow_mul hp ha (hsr0 r hr) (hpsr r hr)
  -- the removed set `T`
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = TR.image (fun r => p ^ a * s * r) := ⟨_, rfl⟩
  have hTsub : T ⊆ Ioc N M \ D := by
    intro m hm
    rw [hT, Finset.mem_image] at hm
    obtain ⟨r, hr, rfl⟩ := hm
    obtain ⟨-, -, -, hr1, hr2, -⟩ := hTR' r hr
    rw [Finset.mem_sdiff, Finset.mem_Ioc]
    exact ⟨⟨hr1, hr2⟩, fun hmD => hDns _ hmD (hm_smooth r hr)⟩
  have hinj : Set.InjOn (fun r => p ^ a * s * r) TR := by
    intro r₁ _ r₂ _ h
    have hpa : 0 < p ^ a * s := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hs0.ne')
    exact Nat.eq_of_mul_eq_mul_left hpa h
  have hrecipT : recipSum T = ∑ r ∈ TR, (1 : ℚ) / ((p : ℚ) ^ a * s * r) := by
    rw [hT, recipSum, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Nat.cast_mul, Nat.cast_pow]
  have hdisj : Disjoint D T := Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff
  have hnew : recipSum (Ioc N M \ (D ∪ T)) = x - ∑ r ∈ TR, (1 : ℚ) / ((p : ℚ) ^ a * s * r) := by
    have hset : Ioc N M \ (D ∪ T) = (Ioc N M \ D) \ T := by
      ext m
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
      tauto
    rw [hset, recipSum_sdiff hTsub, hrecipT, hx]
  -- the new denominator
  have hdvd := den_sub_sum_dvd hp ha hden hv' hs0 hps
    (fun r hr => ⟨(hTR' r hr).1, (hTR' r hr).2.2.1⟩) hTsum
  have hv'0 : v' ≠ 0 := by
    intro h; rw [h, mul_zero] at hden; exact hden0 hden
  have h0 : 0 ∉ insert v' (TR.image (s * ·)) := by
    intro h0
    rw [Finset.mem_insert, Finset.mem_image] at h0
    rcases h0 with h | ⟨r, hr, h⟩
    · exact hv'0 h.symm
    · exact hsr0 r hr h
  have hlcm_smooth : PPSmooth (p ^ a - 1) ((insert v' (TR.image (s * ·))).lcm id) := by
    apply ppSmooth_lcm _ h0
    intro n hn
    rw [Finset.mem_insert, Finset.mem_image] at hn
    rcases hn with rfl | ⟨r, hr, rfl⟩
    · apply ppSmooth_sub_one_of_not_dvd hp _ hv'
      exact hsm.of_dvd hden0 (by rw [hden]; exact dvd_mul_left _ _)
    · exact hsr_smooth r hr
  have hlcm0 : (insert v' (TR.image (s * ·))).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; simpa using h0
  -- the mass of `T`
  have hTmass : (recipSum T : ℝ) ≤ B := by
    have h1 := recipSum_le_card_div hN0 (S := T)
      (fun m hm => (Finset.mem_Ioc.1 (Finset.mem_sdiff.1 (hTsub hm)).1).1)
    have h2 : (T.card : ℝ) ≤ R.card := by
      have : T.card ≤ R.card := by
        rw [hT]; exact Finset.card_image_le.trans (Finset.card_le_card hTR)
      exact_mod_cast this
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [hB]
    calc (recipSum T : ℝ) ≤ T.card / N := h1
      _ ≤ R.card / N := by gcongr
      _ ≤ 3 * Real.log N ^ 4 / N := by gcongr
  have hcard : (((Ioc (p ^ a) Q).filter IsPrimePow).card : ℝ) + 1 ≤
      ((Ioc (p ^ a - 1) Q).filter IsPrimePow).card := by
    have hsub : insert (p ^ a) ((Ioc (p ^ a) Q).filter IsPrimePow) ⊆
        (Ioc (p ^ a - 1) Q).filter IsPrimePow := by
      intro m hm
      rw [Finset.mem_insert] at hm
      rcases hm with rfl | hm
      · rw [Finset.mem_filter, Finset.mem_Ioc]
        have := Nat.one_le_pow a p hp.pos
        refine ⟨⟨by omega, htQ⟩, ?_⟩
        exact (isPrimePow_nat_iff _).2 ⟨p, a, hp, ha, rfl⟩
      · rw [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
        exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩
    have hnotin : p ^ a ∉ (Ioc (p ^ a) Q).filter IsPrimePow := by
      intro h
      rw [Finset.mem_filter, Finset.mem_Ioc] at h
      exact lt_irrefl _ h.1.1
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotin] at this
    exact_mod_cast this
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨D ∪ T, hD0.trans Finset.subset_union_left,
    Finset.union_subset hDI (hTsub.trans Finset.sdiff_subset), ?_, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact fun h => hDns n hn (h.mono (Nat.sub_le _ _))
    · rw [hT, Finset.mem_image] at hn
      obtain ⟨r, hr, rfl⟩ := hn
      exact hm_ns r hr
  · rw [hnew]
    exact hlcm_smooth.of_dvd hlcm0 hdvd
  · rw [recipSum_union hdisj]
    push_cast
    linarith [mul_le_mul_of_nonneg_right hcard hB0]

/-! ## Asymptotic bookkeeping -/

lemma eventually_L_conds (x₀ : ℝ) : ∀ᶠ L : ℝ in atTop,
    1 ≤ L ∧ x₀ ≤ L ^ 4 / 4 ∧ 2 ≤ L ^ 4 / 4 ∧
    L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) - 18 * L - 1 := by
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).bound
    (by norm_num : (0 : ℝ) < 1 / 320)
  filter_upwards [h1, eventually_ge_atTop (4 * |x₀| + 8)] with L hL hL'
  have hx0 : x₀ ≤ |x₀| := le_abs_self x₀
  have habs : 0 ≤ |x₀| := abs_nonneg x₀
  have hL8 : 8 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hv : 0 < L ^ (39 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have huv : L ^ (1 / 10 : ℝ) * L ^ (39 / 10 : ℝ) = L ^ 4 := by
    rw [← Real.rpow_add hL0, show (1 / 10 : ℝ) + 39 / 10 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlog' : Real.log L ≤ L ^ (1 / 10 : ℝ) / 320 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos hu] at hL
    linarith
  have hv3 : L ^ 3 ≤ L ^ (39 / 10 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ L by linarith)
      (show ((3 : ℕ) : ℝ) ≤ 39 / 10 by norm_num)
    rwa [Real.rpow_natCast] at this
  have hL3 : 9 * L ≤ L ^ 3 := by
    have : L ^ 3 = L * L ^ 2 := by ring
    nlinarith
  have key : 4 * L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) := by
    rw [le_div_iff₀ (by positivity), ← huv]
    nlinarith [mul_le_mul_of_nonneg_left hlog' hv.le]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma eventually_three_log_pow_lt : ∀ᶠ x : ℝ in atTop, 3 * Real.log x ^ 4 < x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  simp only [id, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (by positivity), abs_of_pos hx0] at hx
  linarith

lemma eventually_t_conds (x₀ : ℝ) : ∀ᶠ t : ℕ in atTop,
    4 ≤ t ∧ 3 * Real.log t ^ 4 < t ∧ 1 ≤ Real.log t ∧ x₀ ≤ Real.log t ^ 4 / 4 ∧
    2 ≤ Real.log t ^ 4 / 4 ∧
    Real.log t ^ (39 / 10 : ℝ) ≤
      Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1 := by
  have hlog : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_L_conds x₀),
    tendsto_natCast_atTop_atTop.eventually eventually_three_log_pow_lt,
    eventually_ge_atTop 4] with t h1 h2 h3
  exact ⟨h3, h2, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩

lemma tendsto_div_log_pow_four : Tendsto (fun x : ℝ => x / Real.log x ^ 4) atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 4 / x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    positivity
  have h' : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩
  exact h'.inv_tendsto_nhdsGT_zero.congr (fun x => by simp [inv_div])

lemma eventually_N_conds (ε x₀ x₁ : ℝ) (y₀ T₀ : ℕ) : ∀ᶠ N : ℕ in atTop,
    12 ≤ N ∧ x₀ ≤ (N : ℝ) ∧ x₁ ≤ (N : ℝ) ∧ 48 / ε ≤ Real.log N ∧
    x₁ ≤ (N : ℝ) / Real.log N ^ 4 ∧ 24 / ε ≤ Real.log ((N : ℝ) / Real.log N ^ 4) ∧
    y₀ ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ ∧ T₀ ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ ∧
    10 ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ 4) atTop atTop :=
    tendsto_div_log_pow_four.comp hN
  have hy : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp hN)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [eventually_ge_atTop 12, hN.eventually_ge_atTop x₀, hN.eventually_ge_atTop x₁,
    hlog.eventually_ge_atTop (48 / ε), hx.eventually_ge_atTop x₁,
    (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop (24 / ε),
    hy.eventually_ge_atTop y₀, hy.eventually_ge_atTop T₀, hy.eventually_ge_atTop 10]
    with N h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end P1

/-! ## Proposition 1 -/

open P1 in
theorem prop1 (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
    Real.exp 1 * N ≤ M → (M : ℝ) ≤ Real.exp 1 * N + 3 →
    ∃ D ⊆ Ioc N M, (recipSum D : ℝ) ≤ ε ∧ 1 / (20 * Real.log N) ≤ (recipSum D : ℝ) ∧
      PPSmooth ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ (recipSum (Ioc N M \ D)).den := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 eventually_card_primes_Ioc_ge
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 eventually_card_primePow_le
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 exists_ppSmooth_coprime
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((eventually_t_conds x₀).and lemma1)
  have hS := (tendsto_order.1 tendsto_sum_inv_primePow_Ioc).2 (ε / 8) (by positivity)
  filter_upwards [hS, eventually_N_conds ε x₀ x₁ y₀ T₀] with N hSN hN
  obtain ⟨hN12, hNx₀, hNx₁, hlogN, hxx₁, hlogx, hyy₀, hyT₀, hy10⟩ := hN
  intro M hM1 hM2
  have he1 : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he2 : Real.exp 1 < 68 / 25 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hN0 : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hM27 : (27 / 10 : ℝ) * N ≤ M :=
    le_trans (mul_le_mul_of_nonneg_right he1.le (Nat.cast_nonneg N)) hM1
  have hM3 : (M : ℝ) ≤ 3 * N := by
    have := mul_le_mul_of_nonneg_right he2.le (Nat.cast_nonneg (α := ℝ) N)
    linarith
  have hM3' : M ≤ 3 * N := by exact_mod_cast hM3
  have hNM : N ≤ M := by
    have : (N : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hlogN1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hlogN0 : 0 < Real.log N := by linarith
  have hlogN4 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ hlogN1.le
  -- names for the main parameters
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ⌊(N : ℝ) / Real.log N ^ 4⌋₊ = Q := ⟨_, rfl⟩
  rw [hQ] at hSN
  have hNy : (N : ℝ) < ((⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ : ℕ) + 1 : ℝ) ^ 12 := by
    have h1 := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 12 : ℝ))
    have h2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num : (12 : ℕ) ≠ 0)
    rwa [← Real.rpow_natCast ((N : ℝ) ^ (1 / 12 : ℝ)) 12, ← Real.rpow_mul (Nat.cast_nonneg N),
      show (1 / 12 : ℝ) * ((12 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at h2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ℕ, ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ = y := ⟨_, rfl⟩
  rw [hy₁] at hyy₀ hyT₀ hy10 hNy ⊢
  have hy10' : (10 : ℝ) ≤ y₁ := by exact_mod_cast hy10
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 3 * Real.log N ^ 4 / N := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hQN : Q ≤ N := by
    rw [← hQ]
    exact Nat.floor_le_of_le (div_le_self (Nat.cast_nonneg _) hlogN4)
  -- the elimination procedure
  have hstep : ∀ t D, y₁ < t → t ≤ Q → ClearInv N M Q (bigPP N M Q) B t D →
      ∃ D', ClearInv N M Q (bigPP N M Q) B (t - 1) D' := by
    intro t D hyt htQ hInv
    by_cases hsm : PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den
    · exact ⟨D, clearInv_sub_one hB0 hInv hsm⟩
    · obtain ⟨hconds, hL1⟩ := hT₀ t (by omega)
      have htN : (t : ℝ) ≤ N / Real.log N ^ 4 := by
        have : (t : ℝ) ≤ Q := by exact_mod_cast htQ
        rw [← hQ] at this
        exact this.trans (Nat.floor_le (by positivity))
      have hNt : Real.log N ≤ 12 * Real.log t := by
        have h1 : (N : ℝ) ^ (1 / 12 : ℝ) < t := by
          have := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 12 : ℝ))
          rw [hy₁] at this
          have h2 : (y₁ : ℝ) + 1 ≤ t := by exact_mod_cast hyt
          linarith
        have h2 := Real.log_lt_log (by positivity) h1
        rw [Real.log_rpow (by positivity)] at h2
        linarith
      exact step_main hx₀ (hy₀ y₁ hyy₀) hy10' hNy hL1 hB hN0 hM27 htN hNt hlogN1 hyt htQ
        hconds hInv hsm
  obtain ⟨D, hD⟩ := clear_all hstep clearInv_base
  obtain ⟨hD0, hDI, -, hDsm, hDmass⟩ := hD
  refine ⟨D, hDI, ?_, ?_, hDsm.mono (by omega)⟩
  · -- the upper bound `H(D) ≤ ε`
    have hD0up := recipSum_bigPP_le (Q := Q) hN0 hNM hM3'
    have hlog3N : Real.log N ≤ Real.log (3 * N) :=
      Real.log_le_log (by positivity) (by linarith)
    have hPPset : (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) ≤
        4 * (3 * N) / Real.log (3 * N) := by
      have h1 := hx₁ ((3 * N : ℕ) : ℝ) (by push_cast; linarith)
      rw [Nat.floor_natCast] at h1
      have h2 : ((Ioc Q (3 * N)).filter IsPrimePow).card ≤
          ((Icc 1 (3 * N)).filter IsPrimePow).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        omega
      calc (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ)
          ≤ (((Icc 1 (3 * N)).filter IsPrimePow).card : ℝ) := by exact_mod_cast h2
        _ ≤ 4 * (3 * N) / Real.log (3 * N) := by push_cast at h1; exact h1
    have hεN : 48 ≤ Real.log N * ε := (div_le_iff₀ hε).1 hlogN
    have hPPN : (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) / N ≤ ε / 4 := by
      have hl3 : 0 < Real.log (3 * N) := by linarith
      have hNr0 : (0 : ℝ) < N := by positivity
      rw [div_le_iff₀ hNr0]
      calc (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) ≤ 4 * (3 * N) / Real.log (3 * N) :=
            hPPset
        _ ≤ ε / 4 * N := by
            rw [div_le_iff₀ hl3]
            nlinarith [mul_le_mul_of_nonneg_left hlog3N hε.le]
    have hbig : (recipSum (bigPP N M Q) : ℝ) ≤ ε / 2 := by linarith
    have hcardQ : (((Icc 1 Q).filter IsPrimePow).card : ℝ) ≤
        4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) := by
      have := hx₁ ((N : ℝ) / Real.log N ^ 4) hxx₁
      rwa [hQ] at this
    have hcardk : (((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card : ℝ) ≤
        ((Icc 1 Q).filter IsPrimePow).card := by
      have : ((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card ≤
          ((Icc 1 Q).filter IsPrimePow).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        omega
      exact_mod_cast this
    have hlogx0 : 0 < Real.log ((N : ℝ) / Real.log N ^ 4) := by
      have : 0 < 24 / ε := by positivity
      linarith
    have hkey : 4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) * B ≤
        ε / 2 := by
      have hNr0 : (N : ℝ) ≠ 0 := by positivity
      have hl0 : Real.log N ^ 4 ≠ 0 := by positivity
      have hlx : Real.log ((N : ℝ) / Real.log N ^ 4) ≠ 0 := hlogx0.ne'
      have h24 : 24 ≤ Real.log ((N : ℝ) / Real.log N ^ 4) * ε := (div_le_iff₀ hε).1 hlogx
      calc 4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) * B
          = 12 / Real.log ((N : ℝ) / Real.log N ^ 4) := by
            rw [hB]; field_simp; ring
        _ ≤ ε / 2 := by
            rw [div_le_iff₀ hlogx0]
            linarith
    have hfin : (((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card : ℝ) * B ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_right (hcardk.trans hcardQ) hB0).trans hkey
    linarith
  · -- the lower bound
    have hlow := recipSum_bigPP_ge (M := M) (Q := Q) hN0 hlogN0 hQN hM27 hM3 (hx₀ N hNx₀)
    have hmono : (recipSum (bigPP N M Q) : ℝ) ≤ recipSum D := by
      exact_mod_cast recipSum_mono hD0
    have : 1 / (20 * Real.log N) ≤ 1 / (15 * Real.log N) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

end Croot
end

section
/-!
# Finite Fourier analysis for subset sums of unit fractions

`eC t = exp (2 π i t)`.  For a finite set `Y` of positive integers dividing `P` and a rational
`x` with `x P ∈ ℤ`, summing `e(-h x) ∏_{m∈Y} (1 + e(h/m))` over any `P` consecutive integers `h`
counts (times `P`) the subsets `Z ⊆ Y` with `∑_{m∈Z} 1/m - x ∈ ℤ`.  We also record the
elementary estimates on the individual terms used in Croot's Proposition 2.
-/

namespace Croot

open Real Complex Finset

/-- `e(t) = exp(2 π i t)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-! ### Basic properties of `eC` -/

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_zero : eC 0 = 1 := by
  simp [eC]

lemma eC_eq_one_iff (t : ℝ) : eC t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h3 : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma eC_intCast (n : ℤ) : eC n = 1 := (eC_eq_one_iff _).2 ⟨n, rfl⟩

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma eC_re (t : ℝ) : (eC t).re = Real.cos (2 * π * t) := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma eC_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  unfold eC
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma eC_nat_mul (n : ℕ) (t : ℝ) : eC (n * t) = eC t ^ n := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1 + e(θ) = e(θ/2) · 2 cos(π θ)`. -/
lemma one_add_eC (θ : ℝ) :
    1 + eC θ = eC (θ / 2) * ((2 * Real.cos (π * θ) : ℝ) : ℂ) := by
  have h1 : ((2 * Real.cos (π * θ) : ℝ) : ℂ) =
      Complex.exp (((π * θ : ℝ) : ℂ) * I) + Complex.exp (-((π * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.two_cos]
    push_cast
    rfl
  rw [h1, mul_add]
  unfold eC
  rw [← Complex.exp_add, ← Complex.exp_add]
  have e1 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + ((π * θ : ℝ) : ℂ) * I = 2 * π * I * θ := by
    push_cast
    ring
  have e2 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + -((π * θ : ℝ) : ℂ) * I = 0 := by
    push_cast
    ring
  rw [e1, e2, Complex.exp_zero, add_comm]

lemma norm_one_add_eC (θ : ℝ) : ‖1 + eC θ‖ = 2 * |Real.cos (π * θ)| := by
  rw [one_add_eC, norm_mul, norm_eC, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_two]

lemma norm_one_add_eC_le_two (θ : ℝ) : ‖1 + eC θ‖ ≤ 2 := by
  calc ‖1 + eC θ‖ ≤ ‖(1 : ℂ)‖ + ‖eC θ‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, norm_eC]; norm_num

/-- `cos (π u) ≤ 1 - 4 u²` for `0 ≤ u ≤ 1/2`: Taylor bound for `u ≤ 3/10`, and
`cos (π u) = sin (π (1/2 - u)) ≤ π (1/2 - u)` for `u ≥ 3/10`. -/
lemma cos_pi_mul_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.cos (π * u) ≤ 1 - 4 * u ^ 2 := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rcases le_or_gt u (3 / 10) with hu | hu
  · have hpu : 0 ≤ π * u := by positivity
    have hx : |π * u| ≤ 1 := by
      rw [abs_of_nonneg hpu]
      nlinarith
    have hb := Real.cos_bound hx
    rw [abs_of_nonneg hpu] at hb
    have hb' := (abs_le.mp hb).2
    have hp2 : 9.85 ≤ π ^ 2 := by nlinarith
    have hp2' : π ^ 2 ≤ 9.93 := by nlinarith
    have hu2 : u ^ 2 ≤ 9 / 100 := by nlinarith
    have hu2' : 0 ≤ u ^ 2 := by positivity
    have hq1 : (u ^ 2) ^ 2 ≤ 9 / 100 * u ^ 2 := by nlinarith
    have hq2 : (π ^ 2) ^ 2 ≤ 9.93 ^ 2 := by nlinarith
    have h4 : (π * u) ^ 4 ≤ 9.93 ^ 2 * (9 / 100 * u ^ 2) := by
      have : (π * u) ^ 4 = (π ^ 2) ^ 2 * (u ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul hq2 hq1 (by positivity) (by positivity)
    have h5 : 9.85 * u ^ 2 ≤ (π * u) ^ 2 := by
      have : (π * u) ^ 2 = π ^ 2 * u ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hp2 hu2'
    nlinarith
  · have hc : Real.cos (π * u) = Real.sin (π / 2 - π * u) := (Real.sin_pi_div_two_sub _).symm
    rw [hc]
    have hs := Real.sin_le (by nlinarith : 0 ≤ π / 2 - π * u)
    have hm : 0 ≤ (1 / 2 - u) * (2 + 4 * u - π) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- If `θ` is at distance `≥ δ` from every integer, then `‖1 + e(θ)‖ ≤ 2 (1 - 4 δ²)`. -/
lemma norm_one_add_eC_le_of_far (θ δ : ℝ) (hδ : 0 ≤ δ) (hfar : ∀ j : ℤ, δ ≤ |θ - j|) :
    ‖1 + eC θ‖ ≤ 2 * (1 - 4 * δ ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, |θ - j| ≤ 1 / 2 := ⟨round θ, abs_sub_round θ⟩
  have hδd : δ ≤ |θ - j| := hfar j
  have heq : eC θ = eC (θ - j) := by
    conv_lhs => rw [show θ = (θ - j) + (j : ℝ) by ring]
    rw [eC_add, eC_intCast, mul_one]
  rw [heq, norm_one_add_eC]
  have hcos : |Real.cos (π * (θ - j))| = Real.cos (π * |θ - j|) := by
    rw [← Real.cos_abs (π * (θ - j)), abs_mul, abs_of_pos Real.pi_pos]
    apply abs_of_nonneg
    have hle : π * |θ - j| ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    have hge : 0 ≤ π * |θ - j| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith [Real.pi_pos]
  rw [hcos]
  have hc := cos_pi_mul_le |θ - j| (abs_nonneg _) hj
  have hsq : δ * δ ≤ |θ - j| * |θ - j| := mul_le_mul hδd hδd hδ (abs_nonneg _)
  nlinarith

/-! ### Integrality and the window sum -/

lemma recipSum_mul_natCast_int (Z : Finset ℕ) (P : ℕ) (hZ : ∀ m ∈ Z, m ∣ P) :
    ∃ z : ℤ, recipSum Z * P = z := by
  refine ⟨∑ m ∈ Z, ((P / m : ℕ) : ℤ), ?_⟩
  rw [recipSum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Int.cast_natCast, Nat.cast_div_charZero (hZ m hm)]
  ring

open scoped Classical in
/-- A complete geometric sum over a window of `P` consecutive integers. -/
lemma sum_Ico_eC (r : ℝ) (P : ℕ) (hr : eC (P * r) = 1) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      if ∃ k : ℤ, r = k then (P : ℂ) else 0 := by
  have hre : ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      ∑ k ∈ Finset.range P, eC ((h₀ : ℝ) * r) * eC r ^ k := by
    refine Finset.sum_nbij' (fun h => (h - h₀).toNat) (fun k => h₀ + k) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_Ico, Finset.mem_range] at hh ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh ⊢
      omega
    · intro k _
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh
      rw [← eC_nat_mul, ← eC_add]
      congr 1
      have h1 : (((h - h₀).toNat : ℕ) : ℝ) = (h : ℝ) - h₀ := by
        have : (((h - h₀).toNat : ℕ) : ℤ) = h - h₀ := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [h1]
      ring
  rw [hre, ← Finset.mul_sum]
  split_ifs with hk
  · obtain ⟨k, rfl⟩ := hk
    have e1 : eC (k : ℝ) = 1 := eC_intCast k
    have e2 : eC ((h₀ : ℝ) * k) = 1 := by
      rw [show ((h₀ : ℝ) * k) = ((h₀ * k : ℤ) : ℝ) by push_cast; ring]
      exact eC_intCast _
    simp [e1, e2]
  · have hne : eC r ≠ 1 := fun h1 => hk ((eC_eq_one_iff r).1 h1)
    rw [geom_sum_eq hne, ← eC_nat_mul, hr]
    simp

-- `hP` is part of the fixed statement but not needed (for `P = 0` both sides vanish).
open scoped Classical in
/-- The counting identity, over any window of `P` consecutive integers. -/
theorem fourier_count (Y : Finset ℕ) (P : ℕ) (hP : 0 < P) (hY : ∀ m ∈ Y, 0 < m ∧ m ∣ P)
    (x : ℚ) (hx : ∃ z : ℤ, x * P = z) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      (P : ℂ) * ((Y.powerset.filter (fun Z => ∃ k : ℤ, recipSum Z - x = k)).card : ℂ) := by
  -- expand the product over subsets and combine the exponentials
  have key : ∀ h : ℤ, eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      ∑ Z ∈ Y.powerset, eC ((h : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) := by
    intro h
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [← eC_sum, ← eC_add]
    congr 1
    simp only [recipSum, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_one_div]
    ring
  rw [Finset.sum_congr rfl fun h _ => key h, Finset.sum_comm, Finset.natCast_card_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  -- for each subset `Z`, `(recipSum Z - x) * P` is an integer
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := recipSum_mul_natCast_int Z P
    (fun m hm => (hY m (Finset.mem_powerset.1 hZ hm)).2)
  have hq : (recipSum Z - x) * P = ((w - z : ℤ) : ℚ) := by
    rw [sub_mul, hw, hz, Int.cast_sub]
  have hr' : (P : ℝ) * ((recipSum Z - x : ℚ) : ℝ) = ((w - z : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at this ⊢
    linarith
  have hr : eC ((P : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) = 1 := by
    rw [hr']
    exact eC_intCast _
  rw [sum_Ico_eC _ P hr h₀]
  have hiff : (∃ k : ℤ, ((recipSum Z - x : ℚ) : ℝ) = k) ↔ (∃ k : ℤ, recipSum Z - x = k) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by exact_mod_cast hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; push_cast; rfl⟩
  by_cases hc : ∃ k : ℤ, recipSum Z - x = k
  · rw [if_pos (hiff.2 hc), if_pos hc, mul_one]
  · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc, mul_zero]

/-- The `h = 0` term. -/
theorem term_zero (Y : Finset ℕ) (x : ℚ) :
    eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC (((0 : ℤ) : ℝ) / m)) = (2 : ℂ) ^ Y.card := by
  simp only [Int.cast_zero, zero_mul, neg_zero, zero_div, eC_zero, one_mul, Finset.prod_const]
  norm_num

/-- Terms with small `|h|` have nonnegative real part. -/
theorem re_term_nonneg (Y : Finset ℕ) (x : ℚ) (h : ℤ)
    (hY : ∀ m ∈ Y, 0 < m ∧ 2 * |(h : ℝ)| ≤ m)
    (hsmall : |(h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ))| ≤ 1 / 4) :
    0 ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))).re := by
  -- the term is `e(h (recipSum Y / 2 - x)) * ∏ 2 cos (π h / m)`
  simp_rw [one_add_eC]
  rw [Finset.prod_mul_distrib, ← eC_sum, ← mul_assoc, ← eC_add, ← Complex.ofReal_prod,
    Complex.re_mul_ofReal]
  apply mul_nonneg
  · rw [eC_re]
    have hsum : ∑ m ∈ Y, (h : ℝ) / m / 2 = (h : ℝ) * (∑ m ∈ Y, (1 : ℝ) / m) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hrs : ((recipSum Y : ℚ) : ℝ) = ∑ m ∈ Y, (1 : ℝ) / m := by
      simp only [recipSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hphi : -((h : ℝ) * (x : ℝ)) + ∑ m ∈ Y, (h : ℝ) / m / 2 =
        (h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ)) := by
      rw [hsum, hrs]
      ring
    rw [hphi]
    obtain ⟨h1, h2⟩ := abs_le.mp hsmall
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  · apply Finset.prod_nonneg
    intro m hm
    obtain ⟨hm0, hm1⟩ := hY m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have habs : |(h : ℝ) / m| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
      linarith
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    apply mul_nonneg (by norm_num)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]

/-- Norm bound: factors with `h/m` at distance `≥ δ` from every integer save `1 - 4 δ²`. -/
theorem norm_term_le (Y J : Finset ℕ) (hJ : J ⊆ Y) (x : ℚ) (h : ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2) (hfar : ∀ m ∈ J, ∀ j : ℤ, δ ≤ |(h : ℝ) / m - j|) :
    ‖eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))‖ ≤
      2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
  rw [norm_mul, norm_eC, one_mul, norm_prod, ← Finset.prod_sdiff hJ]
  have hc : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
  have h1 : ∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ 2 ^ (Y \ J).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun m _ => norm_one_add_eC_le_two _)
  have h2 : ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ (2 * (1 - 4 * δ ^ 2)) ^ J.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun m hm => norm_one_add_eC_le_of_far _ _ hδ (hfar m hm))
  calc (∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖) * ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖
      ≤ 2 ^ (Y \ J).card * (2 * (1 - 4 * δ ^ 2)) ^ J.card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = 2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Finset.card_sdiff_add_card_eq_card hJ]

end Croot
end

section
/-!
# Positive density of prime-power-smooth numbers in the ranges needed for Proposition 2

With `y = ⌊M^{1/5}⌋`:
* `y`-pp-smooth, `B`-rough integers have positive density in `(X, 2X]`,
  `X = M^{3/4} (log M)^4`;
* `y`-pp-smooth integers in `(M, (1+η) M]` have reciprocal mass `≫ η`.

Construction: products `p₁ ⋯ p_r · t` with the `pᵢ` taken from disjoint ranges of primes
inside `(y^α, y^β]` and a free cofactor `t < y^α` (so the factorization is unique);
Chebyshev bounds give `∑_{p ∈ range} 1/p ≫ 1`.
-/

namespace Croot

open Real Finset Filter

/-! ## Prime-power-smooth helpers -/

private lemma density_ppSmooth_of_le {y n : ℕ} (hn : n ≠ 0) (h : n ≤ y) : PPSmooth y n :=
  fun p _ => (Nat.ordProj_le p hn).trans h

private lemma PPSmooth.mul_coprime {y a b : ℕ} (ha : PPSmooth y a) (hb : PPSmooth y b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : Nat.Coprime a b) : PPSmooth y (a * b) :=
  ppSmooth_of_dvd_lcmUpto
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd hab (ha.dvd_lcmUpto ha0) (hb.dvd_lcmUpto hb0))

private lemma natCast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

/-! ## Reciprocal sums of primes over long ranges -/

/-- Over `(x, 2.7^K x]` the primes have reciprocal sum `≥ K / (14 L)` whenever
`log (2.7^K x) ≤ L` (Chebyshev, one block `(z, 2.7 z]` at a time). -/
private lemma exists_block_bound : ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ K : ℕ, ∀ L : ℝ, 0 < L →
    Real.log ((27 / 10 : ℝ) ^ K * x) ≤ L →
    (K : ℝ) / (14 * L) ≤
      ∑ p ∈ Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) ^ K * x⌋₊, (if p.Prime then (1 : ℝ) / p else 0) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp eventually_card_primes_Ioc_ge
  refine ⟨max X₁ 2, le_max_right _ _, fun x hx K => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxX : X₁ ≤ x := le_trans (le_max_left _ _) hx
  induction K with
  | zero =>
    intro L _ _
    simp
  | succ K ih =>
    intro L hL hlog
    have hcK : (1 : ℝ) ≤ (27 / 10 : ℝ) ^ K := one_le_pow₀ (by norm_num)
    have hz_eq : (27 / 10 : ℝ) ^ (K + 1) * x = (27 / 10 : ℝ) * ((27 / 10 : ℝ) ^ K * x) := by
      rw [pow_succ]; ring
    rw [hz_eq] at hlog ⊢
    generalize hz : (27 / 10 : ℝ) ^ K * x = z at ih hlog ⊢
    have hz2 : x ≤ z := by rw [← hz]; nlinarith
    have hzX : X₁ ≤ z := le_trans hxX hz2
    have hz0 : 0 < z := by linarith
    have hlogz : Real.log z ≤ L := le_trans (Real.log_le_log hz0 (by linarith)) hlog
    have h1 := ih L hL hlogz
    have hfl : ⌊x⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hz2
    have hfl2 : ⌊z⌋₊ ≤ ⌊(27 / 10 : ℝ) * z⌋₊ := Nat.floor_le_floor (by linarith)
    rw [← Finset.sum_Ioc_consecutive _ hfl hfl2]
    have hblock : 1 / (14 * L) ≤
        ∑ p ∈ Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊, (if p.Prime then (1 : ℝ) / p else 0) := by
      rw [← Finset.sum_filter]
      have hcnt := hX₁ z hzX
      have hlz : 0 < Real.log z := Real.log_pos (by linarith)
      calc 1 / (14 * L) ≤ 1 / (27 / 2 * Real.log z) := by
            apply one_div_le_one_div_of_le (by positivity); linarith
        _ = (z / (5 * Real.log z)) * (1 / ((27 / 10) * z)) := by
            field_simp; ring
        _ ≤ (((Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime).card : ℝ) *
              (1 / ((27 / 10) * z)) :=
            mul_le_mul_of_nonneg_right hcnt (by positivity)
        _ = ∑ p ∈ (Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime,
              (1 / ((27 / 10) * z) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ (Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpI := Finset.mem_Ioc.mp hp'.1
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
            have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * z :=
              le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
            exact one_div_le_one_div_of_le hp_pos hp_le
    rw [Nat.cast_succ, add_div]
    exact add_le_add h1 hblock

/-! ## Products of primes from consecutive ranges -/

/-- `prodSet b k`: products `p₁ ⋯ p_k` with `pᵢ` prime in `(b (i-1), b i]`. -/
private def prodSet (b : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => {1}
  | k + 1 => (((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k).image
      (fun x => x.1 * x.2)

private lemma mem_prodSet_succ {b : ℕ → ℕ} {k n : ℕ} : n ∈ prodSet b (k + 1) ↔
    ∃ p, (b k < p ∧ p ≤ b (k + 1)) ∧ p.Prime ∧ ∃ P ∈ prodSet b k, n = p * P := by
  simp only [prodSet, Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨p, P⟩, ⟨⟨hp1, hp2⟩, hP⟩, rfl⟩
    exact ⟨p, hp1, hp2, P, hP, rfl⟩
  · rintro ⟨p, hp1, hp2, P, hP, rfl⟩
    exact ⟨⟨p, P⟩, ⟨⟨hp1, hp2⟩, hP⟩, rfl⟩

private lemma prodSet_spec {b : ℕ → ℕ} (hb : Monotone b) (k : ℕ) : ∀ P ∈ prodSet b k,
    0 < P ∧ (∀ q, q.Prime → q ∣ P → b 0 < q ∧ q ≤ b k) ∧ (b 0 + 1) ^ k ≤ P ∧
      P ≤ b k ^ k ∧ PPSmooth (b k) P := by
  induction k with
  | zero =>
    intro P hP
    simp only [prodSet, Finset.mem_singleton] at hP
    subst hP
    refine ⟨one_pos, fun q hq hq1 => ?_, by simp, by simp, ppSmooth_one _⟩
    exact absurd (Nat.le_of_dvd one_pos hq1) (by have := hq.two_le; omega)
  | succ k ih =>
    intro n hn
    obtain ⟨p, ⟨hp1, hp2⟩, hp, P, hP, rfl⟩ := mem_prodSet_succ.mp hn
    obtain ⟨hP0, hPq, hPlo, hPhi, hPs⟩ := ih P hP
    have hbk : b k ≤ b (k + 1) := hb (Nat.le_succ k)
    have hb0 : b 0 ≤ b k := hb (Nat.zero_le k)
    have hpP : ¬ p ∣ P := fun h => by have := (hPq p hp h).2; omega
    refine ⟨Nat.mul_pos hp.pos hP0, ?_, ?_, ?_, ?_⟩
    · intro q hq hqd
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
        subst this; omega
      · have := hPq q hq h; omega
    · rw [pow_succ']
      exact Nat.mul_le_mul (by omega) hPlo
    · rw [pow_succ']
      exact Nat.mul_le_mul hp2 (le_trans hPhi (Nat.pow_le_pow_left hbk k))
    · exact PPSmooth.mul_coprime (density_ppSmooth_of_le hp.ne_zero hp2) (hPs.mono hbk) hp.ne_zero
        hP0.ne' ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpP)

private lemma prodSet_sum_ge {b : ℕ → ℕ} (hb : Monotone b) {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ)
    (hR : ∀ i < k, σ ≤ ∑ p ∈ Ioc (b i) (b (i + 1)), (if p.Prime then (1 : ℝ) / p else 0)) :
    σ ^ k ≤ ∑ P ∈ prodSet b k, (1 : ℝ) / P := by
  induction k with
  | zero => simp [prodSet]
  | succ k ih =>
    have ih' := ih (fun i hi => hR i (by omega))
    have hk := hR k (by omega)
    rw [← Finset.sum_filter] at hk
    have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
        ↑(((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k) := by
      rintro ⟨p, P⟩ hx ⟨p', P'⟩ hx' heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_Ioc] at hx hx'
      simp only at heq
      have hp := hx.1.2
      have hp' := hx'.1.2
      have hP'q := (prodSet_spec hb k P' hx'.2).2.1
      have hdvd : p ∣ p' * P' := heq ▸ dvd_mul_right p P
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · have hpp := (Nat.prime_dvd_prime_iff_eq hp hp').mp h
        subst hpp
        have := Nat.eq_of_mul_eq_mul_left hp.pos heq
        subst this; rfl
      · have := (hP'q p hp h).2; omega
    show σ ^ (k + 1) ≤ ∑ P ∈ (((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k).image
      (fun x => x.1 * x.2), (1 : ℝ) / P
    rw [Finset.sum_image hinj, Finset.sum_product]
    have e : ∑ x ∈ (Ioc (b k) (b (k + 1))).filter Nat.Prime, ∑ y ∈ prodSet b k,
        (1 : ℝ) / ((x * y : ℕ) : ℝ) =
        (∑ x ∈ (Ioc (b k) (b (k + 1))).filter Nat.Prime, (1 : ℝ) / x) *
          ∑ y ∈ prodSet b k, (1 : ℝ) / y := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [Nat.cast_mul, one_div_mul_one_div]
    rw [e, pow_succ']
    exact mul_le_mul hk ih' (pow_nonneg hσ k) (le_trans hσ hk)

/-! ## Unique decomposition `n = P * t` -/

private lemma sigma_mul_injOn {T : Finset ℕ} {I : ℕ → Finset ℕ} (hT : ∀ P ∈ T, 0 < P)
    (hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ I P', Nat.Coprime P t) :
    Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ↑(T.sigma I) := by
  rintro ⟨P, t⟩ hx ⟨P', t'⟩ hx' heq
  simp only [Finset.mem_coe, Finset.mem_sigma] at hx hx'
  simp only at heq
  have h1 : P ∣ P' := (hcop P hx.1 P' hx'.1 t' hx'.2).dvd_of_dvd_mul_right
    (heq ▸ dvd_mul_right P t)
  have h2 : P' ∣ P := (hcop P' hx'.1 P hx.1 t hx.2).dvd_of_dvd_mul_right
    (heq.symm ▸ dvd_mul_right P' t')
  have hPP := Nat.dvd_antisymm h1 h2
  subst hPP
  have := Nat.eq_of_mul_eq_mul_left (hT P hx.1) heq
  subst this; rfl

private lemma recipSum_cast (S : Finset ℕ) : ((recipSum S : ℚ) : ℝ) = ∑ n ∈ S, (1 : ℝ) / n := by
  simp [recipSum]

/-- Five consecutive ranges `(b i, b (i+1)]` above `x₀`, each of prime reciprocal sum
`≥ 1/5040`, ending below `x₀ u` (for `u` large and `u ≤ x₀`). -/
private lemma exists_ranges : ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ u : ℝ, U₀ ≤ u → ∀ x₀ : ℝ, u ≤ x₀ → x₀ ≤ u ^ 17 →
    ∃ b : ℕ → ℕ, Monotone b ∧ x₀ < (b 0 : ℝ) + 1 ∧ (b 5 : ℝ) ≤ x₀ * u ∧
      ∀ i < 5, (1 / 5040 : ℝ) ≤
        ∑ p ∈ Ioc (b i) (b (i + 1)), (if p.Prime then (1 : ℝ) / p else 0) := by
  obtain ⟨X₀, hX₀2, hX₀⟩ := exists_block_bound
  refine ⟨max X₀ (Real.exp 20), le_trans hX₀2 (le_max_left _ _), fun u hu x₀ hux hxu => ?_⟩
  have huX : X₀ ≤ u := le_trans (le_max_left _ _) hu
  have hue : Real.exp 20 ≤ u := le_trans (le_max_right _ _) hu
  have hu2 : 2 ≤ u := le_trans hX₀2 huX
  have hu0 : 0 < u := by linarith
  have hlogu : 20 ≤ Real.log u := by
    rw [← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hue
  have hx0 : 0 < x₀ := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊Real.log u / 10⌋₊ := ⟨_, rfl⟩
  have hK2 : Real.log u / 20 ≤ (K : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.log u / 10); rw [← hK] at this; linarith
  have hK1 : (K : ℝ) ≤ Real.log u / 10 := by rw [hK]; exact Nat.floor_le (by positivity)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (27 / 10 : ℝ) ^ K := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hc ▸ one_le_pow₀ (by norm_num)
  have hc0 : 0 < c := by linarith
  have hc5 : c ^ 5 ≤ u := by
    rw [← Real.log_le_log_iff (pow_pos hc0 5) hu0, Real.log_pow, hc, Real.log_pow]
    have h1 : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    push_cast
    linarith
  refine ⟨fun i => ⌊c ^ i * x₀⌋₊, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hij) hx0.le)
  · simp only [pow_zero, one_mul]
    exact Nat.lt_floor_add_one x₀
  · refine le_trans (Nat.floor_le (mul_nonneg (pow_pos hc0 5).le hx0.le)) ?_
    rw [mul_comm x₀ u]
    exact mul_le_mul_of_nonneg_right hc5 hx0.le
  · intro i hi
    have hci : c ^ (i + 1) * x₀ ≤ u * x₀ :=
      mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_right₀ hc1 (by omega)) hc5) hx0.le
    have hxi : X₀ ≤ c ^ i * x₀ := by
      have h1 : 1 ≤ c ^ i := one_le_pow₀ hc1
      nlinarith
    have heq : c ^ (i + 1) * x₀ = (27 / 10 : ℝ) ^ K * (c ^ i * x₀) := by
      rw [pow_succ, hc]; ring
    have hlogL : Real.log ((27 / 10 : ℝ) ^ K * (c ^ i * x₀)) ≤ 18 * Real.log u := by
      rw [← heq]
      have h18 : c ^ (i + 1) * x₀ ≤ u ^ 18 := by
        have : u * x₀ ≤ u * u ^ 17 := mul_le_mul_of_nonneg_left hxu hu0.le
        calc c ^ (i + 1) * x₀ ≤ u * x₀ := hci
          _ ≤ u * u ^ 17 := this
          _ = u ^ 18 := by ring
      have := Real.log_le_log (mul_pos (pow_pos hc0 _) hx0) h18
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hmain := hX₀ (c ^ i * x₀) hxi K (18 * Real.log u) (by positivity) hlogL
    show (1 / 5040 : ℝ) ≤ ∑ p ∈ Ioc ⌊c ^ i * x₀⌋₊ ⌊c ^ (i + 1) * x₀⌋₊,
      (if p.Prime then (1 : ℝ) / p else 0)
    rw [heq]
    refine le_trans ?_ hmain
    rw [le_div_iff₀ (by positivity)]
    linarith

/-- Core of `mass_smooth_ge`: the products `P * t`, `t ∈ (M/P, A/P]`, are distinct `y`-pp-smooth
elements of `(M, A]` and carry reciprocal mass `≥ (η/4) ∑_{P ∈ T} 1/P`. -/
private lemma mass_core {M A y b0 : ℕ} {η : ℝ} (T : Finset ℕ)
    (hT : ∀ P ∈ T, 0 < P ∧ (∀ q, q.Prime → q ∣ P → b0 < q) ∧ PPSmooth y P)
    (hb0y : b0 ≤ y) (hPbig : ∀ P ∈ T, A < P * (b0 + 1))
    (hPsmall : ∀ P ∈ T, 4 * (P : ℝ) ≤ η * M)
    (hA1 : (1 + η) * (M : ℝ) - 1 < A) (hA2 : A ≤ 2 * M) (hMpos : 0 < M) :
    (η / 4) * ∑ P ∈ T, (1 : ℝ) / P ≤ ∑ n ∈ (Ioc M A).filter (PPSmooth y), (1 : ℝ) / n := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have ht : ∀ P ∈ T, ∀ t ∈ Ioc (M / P) (A / P), 0 < t ∧ t ≤ b0 ∧ M < P * t ∧ P * t ≤ A := by
    intro P hP t htI
    have hP0 := (hT P hP).1
    rw [Finset.mem_Ioc] at htI
    have h1 : M < t * P := (Nat.div_lt_iff_lt_mul hP0).mp htI.1
    have h2 : t * P ≤ A := (Nat.le_div_iff_mul_le hP0).mp htI.2
    have h3 := hPbig P hP
    rw [mul_comm t P] at h1 h2
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_, h1, h2⟩
    by_contra hcon
    push Not at hcon
    have : P * (b0 + 1) ≤ P * t := Nat.mul_le_mul_left P hcon
    omega
  have hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ Ioc (M / P') (A / P'), Nat.Coprime P t := by
    intro P hP P' hP' t htI
    obtain ⟨ht0, htb, _, _⟩ := ht P' hP' t htI
    obtain ⟨_, hPq, _⟩ := hT P hP
    apply Nat.coprime_of_dvd
    intro k hk hkP hkt
    have := hPq k hk hkP
    have := Nat.le_of_dvd ht0 hkt
    omega
  have hinner : ∀ P ∈ T, (η / 4) * (1 / (P : ℝ)) ≤
      ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / ((P * t : ℕ) : ℝ) := by
    intro P hP
    have hP0 := (hT P hP).1
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
    have hsmall := hPsmall P hP
    have hterm : ∀ t ∈ Ioc (M / P) (A / P),
        (1 : ℝ) / (2 * M) ≤ (1 : ℝ) / ((P * t : ℕ) : ℝ) := by
      intro t htI
      obtain ⟨ht0, _, _, hhi⟩ := ht P hP t htI
      apply one_div_le_one_div_of_le (by exact_mod_cast Nat.mul_pos hP0 ht0)
      have : P * t ≤ 2 * M := le_trans hhi hA2
      exact_mod_cast this
    have hcard : η * M / (2 * P) ≤ ((Ioc (M / P) (A / P)).card : ℝ) := by
      rw [Nat.card_Ioc]
      have e1 := natCast_sub_ge (A / P) (M / P)
      have e2 : (A : ℝ) / P - 1 < ((A / P : ℕ) : ℝ) := by
        rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
      have e3 : ((M / P : ℕ) : ℝ) ≤ (M : ℝ) / P := Nat.cast_div_le
      have e4 : ((1 + η) * M - 1) / P ≤ (A : ℝ) / P := div_le_div_of_nonneg_right hA1.le hPr.le
      have e5 : 1 / (P : ℝ) ≤ 1 := by
        rw [div_le_one hPr]; exact_mod_cast hP0
      have e6 : 4 ≤ η * M / P := by rw [le_div_iff₀ hPr]; linarith
      have e7 : ((1 + η) * M - 1) / P = M / P + η * M / P - 1 / P := by ring
      have e8 : η * M / (2 * P) = η * M / P / 2 := by ring
      linarith
    calc (η / 4) * (1 / (P : ℝ)) = (η * M / (2 * P)) * (1 / (2 * M)) := by
          field_simp; ring
      _ ≤ ((Ioc (M / P) (A / P)).card : ℝ) * (1 / (2 * M)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / (2 * M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hinj := sigma_mul_injOn (T := T) (I := fun P => Ioc (M / P) (A / P))
    (fun P hP => (hT P hP).1) hcop
  have hsub : (T.sigma fun P => Ioc (M / P) (A / P)).image
      (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ⊆ (Ioc M A).filter (PPSmooth y) := by
    intro n hn
    obtain ⟨⟨P, t⟩, hx, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_sigma] at hx
    obtain ⟨ht0, htb, hlo, hhi⟩ := ht P hx.1 t hx.2
    obtain ⟨hP0, _, hPs⟩ := hT P hx.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, ?_⟩
    exact PPSmooth.mul_coprime hPs (density_ppSmooth_of_le ht0.ne' (le_trans htb hb0y)) hP0.ne'
      ht0.ne' (hcop P hx.1 P hx.1 t hx.2)
  calc (η / 4) * ∑ P ∈ T, (1 : ℝ) / P = ∑ P ∈ T, (η / 4) * (1 / (P : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ P ∈ T, ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / ((P * t : ℕ) : ℝ) :=
        Finset.sum_le_sum hinner
    _ = ∑ x ∈ T.sigma (fun P => Ioc (M / P) (A / P)), (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) :=
        (Finset.sum_sigma T (fun P => Ioc (M / P) (A / P))
          (fun x => (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ))).symm
    _ = ∑ n ∈ (T.sigma fun P => Ioc (M / P) (A / P)).image
          (fun x : (_ : ℕ) × ℕ => x.1 * x.2), (1 : ℝ) / n :=
        (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / n) hinj).symm
    _ ≤ ∑ n ∈ (Ioc M A).filter (PPSmooth y), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- Core of `card_smoothRough_ge`: the products `P * (Q k + 1)` are distinct `y`-pp-smooth,
`B`-rough elements of `(N₀, 2 N₀]`, at least `(N₀ / 2Q) ∑_{P ∈ T} 1/P` of them. -/
private lemma card_core {N0 B y b0 : ℕ} (T : Finset ℕ)
    (hT : ∀ P ∈ T, 0 < P ∧ (∀ q, q.Prime → q ∣ P → b0 < q) ∧ PPSmooth y P)
    (hb0y : b0 ≤ y) (hBb : B ≤ b0) (hPbig : ∀ P ∈ T, 2 * N0 < P * (b0 + 1))
    (hPsmall : ∀ P ∈ T, 4 * ((P : ℝ) * B.factorial) ≤ N0) :
    ((N0 : ℝ) / (2 * B.factorial)) * ∑ P ∈ T, (1 : ℝ) / P ≤
      (((Ioc N0 (2 * N0)).filter (fun n => PPSmooth y n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n)).card : ℝ) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = B.factorial := ⟨_, rfl⟩
  rw [← hQ] at hPsmall ⊢
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.factorial_pos B
  obtain ⟨I, hI⟩ : ∃ I : ℕ → Finset ℕ, I = fun P =>
      (Ioo (N0 / (P * Q)) (2 * N0 / (P * Q))).image (fun k => Q * k + 1) := ⟨_, rfl⟩
  have ht : ∀ P ∈ T, ∀ t ∈ I P, 0 < t ∧ t ≤ b0 ∧ N0 < P * t ∧ P * t ≤ 2 * N0 ∧
      ∀ p, p.Prime → p ≤ B → ¬ p ∣ t := by
    intro P hP t htI
    rw [hI] at htI
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp htI
    rw [Finset.mem_Ioo] at hk
    have hP0 := (hT P hP).1
    have hPQ : 0 < P * Q := Nat.mul_pos hP0 hQ1
    have h1 : N0 < k * (P * Q) := (Nat.div_lt_iff_lt_mul hPQ).mp hk.1
    have h2 : (k + 1) * (P * Q) ≤ 2 * N0 := (Nat.le_div_iff_mul_le hPQ).mp hk.2
    have h3 : P * (Q * k + 1) = k * (P * Q) + P := by ring
    have h4 : P ≤ P * Q := Nat.le_mul_of_pos_right P hQ1
    have h5 : (k + 1) * (P * Q) = k * (P * Q) + P * Q := by ring
    have hlo : N0 < P * (Q * k + 1) := by omega
    have hhi : P * (Q * k + 1) ≤ 2 * N0 := by omega
    refine ⟨Nat.succ_pos _, ?_, hlo, hhi, ?_⟩
    · by_contra hcon
      push Not at hcon
      have : P * (b0 + 1) ≤ P * (Q * k + 1) := Nat.mul_le_mul_left P hcon
      have := hPbig P hP
      omega
    · intro p hp hpB hpt
      have hpQ : p ∣ Q := hQ ▸ Nat.dvd_factorial hp.pos hpB
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hpQ k)).mp hpt
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ I P', Nat.Coprime P t := by
    intro P hP P' hP' t htI
    obtain ⟨ht0, htb, _, _, _⟩ := ht P' hP' t htI
    obtain ⟨_, hPq, _⟩ := hT P hP
    apply Nat.coprime_of_dvd
    intro k hk hkP hkt
    have := hPq k hk hkP
    have := Nat.le_of_dvd ht0 hkt
    omega
  have hIcard : ∀ P ∈ T, (N0 : ℝ) / (2 * P * Q) ≤ ((I P).card : ℝ) := by
    intro P hP
    have hP0 := (hT P hP).1
    have hPQ : 0 < P * Q := Nat.mul_pos hP0 hQ1
    have hPQr : (0 : ℝ) < (P : ℝ) * Q := by exact_mod_cast hPQ
    have hinjk : Function.Injective (fun k : ℕ => Q * k + 1) := fun a b h =>
      Nat.eq_of_mul_eq_mul_left hQ1 (Nat.add_right_cancel h)
    rw [hI, Finset.card_image_of_injective _ hinjk, Nat.card_Ioo]
    have e1 := natCast_sub_ge (2 * N0 / (P * Q) - N0 / (P * Q)) 1
    have e2 := natCast_sub_ge (2 * N0 / (P * Q)) (N0 / (P * Q))
    have e3 : ((2 * N0 : ℕ) : ℝ) / ((P * Q : ℕ) : ℝ) - 1 < ((2 * N0 / (P * Q) : ℕ) : ℝ) := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
    have e4 : ((N0 / (P * Q) : ℕ) : ℝ) ≤ ((N0 : ℕ) : ℝ) / ((P * Q : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at e1 e2 e3 e4 ⊢
    have e5 : 4 ≤ (N0 : ℝ) / (P * Q) := by rw [le_div_iff₀ hPQr]; linarith [hPsmall P hP]
    have e6 : (N0 : ℝ) / (2 * P * Q) = (N0 : ℝ) / (P * Q) / 2 := by ring
    have e7 : (2 * N0 : ℝ) / (P * Q) = 2 * ((N0 : ℝ) / (P * Q)) := by ring
    linarith
  have hinj := sigma_mul_injOn (T := T) (I := I) (fun P hP => (hT P hP).1) hcop
  have hsub : (T.sigma I).image (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ⊆
      (Ioc N0 (2 * N0)).filter (fun n => PPSmooth y n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) := by
    intro n hn
    obtain ⟨⟨P, t⟩, hx, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_sigma] at hx
    obtain ⟨ht0, htb, hlo, hhi, hrough⟩ := ht P hx.1 t hx.2
    obtain ⟨hP0, hPq, hPs⟩ := hT P hx.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, ?_, ?_⟩
    · exact PPSmooth.mul_coprime hPs (density_ppSmooth_of_le ht0.ne' (le_trans htb hb0y)) hP0.ne'
        ht0.ne' (hcop P hx.1 P hx.1 t hx.2)
    · intro p hpB hp hpd
      rw [Finset.mem_Iic] at hpB
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · have := hPq p hp h; omega
      · exact hrough p hp hpB h
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ1
  calc ((N0 : ℝ) / (2 * Q)) * ∑ P ∈ T, (1 : ℝ) / P = ∑ P ∈ T, (N0 : ℝ) / (2 * P * Q) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have : (P : ℝ) ≠ 0 := by exact_mod_cast (hT P hP).1.ne'
        field_simp
    _ ≤ ∑ P ∈ T, ((I P).card : ℝ) := Finset.sum_le_sum hIcard
    _ = (((T.sigma I).image (fun x : (_ : ℕ) × ℕ => x.1 * x.2)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_sigma]
        push_cast
        rfl
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- `y`-pp-smooth, `B`-rough integers in `(X, 2X]` with `X = M^{3/4} (log M)^4`. -/
theorem card_smoothRough_ge (B : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
    c * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) ≤
      (((Ioc ⌊(M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4⌋₊
          ⌊2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)⌋₊).filter
        (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n)).card : ℝ) := by
  obtain ⟨U₀, hU₀2, hU₀⟩ := exists_ranges
  have hQ1 : 1 ≤ B.factorial := Nat.factorial_pos B
  have hQr : (1 : ℝ) ≤ B.factorial := by exact_mod_cast hQ1
  refine ⟨(1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)), by positivity, ?_⟩
  have hu : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hu.eventually_ge_atTop (max U₀ (max (B : ℝ) (4 * (B.factorial : ℝ) + 1))),
    hu.eventually (eventually_log_pow_le_mul_sqrt 4 (ε := 1 / 10 ^ 9) (by norm_num))]
    with M hM hlog4
  generalize hu_def : (M : ℝ) ^ (1 / 100 : ℝ) = u at hM hlog4
  have huU : U₀ ≤ u := le_trans (le_max_left _ _) hM
  have huB : (B : ℝ) ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have huQ : 4 * (B.factorial : ℝ) + 1 ≤ u :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hu2 : 2 ≤ u := le_trans hU₀2 huU
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hu100 : u ^ 100 = (M : ℝ) := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hy : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 20 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have h34 : (M : ℝ) ^ (3 / 4 : ℝ) = u ^ 75 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hlogM : Real.log M = 100 * Real.log u := by
    rw [← hu100, Real.log_pow]; push_cast; ring
  have hlogu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num) hu2
    linarith [Real.log_two_gt_d9]
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (M : ℝ) ^ (3 / 4 : ℝ) * Real.log M ^ 4 := ⟨_, rfl⟩
  rw [← hXdef]
  have hXu : X = u ^ 75 * (100 * Real.log u) ^ 4 := by rw [hXdef, h34, hlogM]
  have hX_lo : u ^ 75 ≤ X := by
    rw [hXu]
    have : 1 ≤ (100 * Real.log u) ^ 4 := one_le_pow₀ (by linarith)
    exact le_mul_of_one_le_right (pow_pos hu0 75).le this
  have hsq : √u ≤ u := by
    rw [Real.sqrt_le_left hu0.le]; nlinarith
  have hX_hi : 2 * X < u ^ 80 := by
    rw [hXu]
    have h1 : (100 * Real.log u) ^ 4 = 10 ^ 8 * Real.log u ^ 4 := by ring
    rw [h1]
    have h2 : 10 ^ 8 * Real.log u ^ 4 ≤ u / 10 := by
      calc 10 ^ 8 * Real.log u ^ 4 ≤ 10 ^ 8 * (1 / 10 ^ 9 * √u) := by gcongr
        _ = √u / 10 := by ring
        _ ≤ u / 10 := by linarith
    have h75 : 0 < u ^ 75 := pow_pos hu0 75
    have h4 := mul_le_mul_of_nonneg_left h2 h75.le
    have h3 : u ≤ u ^ 5 := le_self_pow₀ hu1 (by norm_num)
    have h5 := mul_lt_mul_of_pos_left (show u / 5 < u ^ 5 by linarith) h75
    calc 2 * (u ^ 75 * (10 ^ 8 * Real.log u ^ 4)) ≤ 2 * (u ^ 75 * (u / 10)) := by linarith
      _ = u ^ 75 * (u / 5) := by ring
      _ < u ^ 75 * u ^ 5 := h5
      _ = u ^ 80 := by ring
  have hux : u ≤ u ^ 16 := le_self_pow₀ hu1 (by norm_num)
  have hx17 : u ^ 16 ≤ u ^ 17 := pow_le_pow_right₀ hu1 (by norm_num)
  obtain ⟨b, hbmono, hb0, hb5, hR⟩ := hU₀ u huU (u ^ 16) hux hx17
  have hb4 : (b 4 : ℝ) ≤ u ^ 17 := by
    have h1 : (b 4 : ℝ) ≤ b 5 := by exact_mod_cast hbmono (by norm_num : 4 ≤ 5)
    have h2 : u ^ 16 * u = u ^ 17 := by ring
    linarith
  have hb4y : b 4 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
    rw [hy]; apply Nat.le_floor
    exact le_trans hb4 (pow_le_pow_right₀ hu1 (by norm_num))
  have hb04 : b 0 ≤ b 4 := hbmono (by norm_num)
  have hBb : B ≤ b 0 := by
    have h1 : (B : ℝ) < b 0 + 1 := by linarith
    have h2 : B < b 0 + 1 := by exact_mod_cast h1
    omega
  have hTsum := prodSet_sum_ge hbmono (by norm_num : (0 : ℝ) ≤ 1 / 5040) 4
    (fun i hi => hR i (by omega))
  have hTspec := prodSet_spec hbmono 4
  have hX0 : 0 ≤ X := le_trans (pow_pos hu0 75).le hX_lo
  have hN0le : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0
  have hN0gt : X - 1 < ⌊X⌋₊ := Nat.sub_one_lt_floor X
  have hN1 : (1 : ℝ) ≤ ⌊X⌋₊ := by
    have : u ≤ u ^ 75 := le_self_pow₀ hu1 (by norm_num)
    linarith
  have hPbig : ∀ P ∈ prodSet b 4, 2 * ⌊X⌋₊ < P * (b 0 + 1) := by
    intro P hP
    obtain ⟨_, _, hlo, _, _⟩ := hTspec P hP
    have hlo' : ((b 0 : ℝ) + 1) ^ 4 ≤ P := by exact_mod_cast hlo
    have h5 : (u ^ 16) ^ 5 < ((b 0 : ℝ) + 1) ^ 5 :=
      pow_lt_pow_left₀ hb0 (by positivity) (by norm_num)
    have : (2 * ⌊X⌋₊ : ℝ) < P * ((b 0 : ℝ) + 1) := by
      calc (2 * ⌊X⌋₊ : ℝ) ≤ 2 * X := by linarith
        _ < u ^ 80 := hX_hi
        _ = (u ^ 16) ^ 5 := by ring
        _ < ((b 0 : ℝ) + 1) ^ 5 := h5
        _ = ((b 0 : ℝ) + 1) ^ 4 * ((b 0 : ℝ) + 1) := by ring
        _ ≤ P * ((b 0 : ℝ) + 1) := mul_le_mul_of_nonneg_right hlo' (by positivity)
    exact_mod_cast this
  have hPsmall : ∀ P ∈ prodSet b 4, 4 * ((P : ℝ) * B.factorial) ≤ ⌊X⌋₊ := by
    intro P hP
    obtain ⟨_, _, _, hhi, _⟩ := hTspec P hP
    have hhi' : (P : ℝ) ≤ (b 4 : ℝ) ^ 4 := by exact_mod_cast hhi
    have h68 : (P : ℝ) ≤ u ^ 68 := by
      calc (P : ℝ) ≤ (b 4 : ℝ) ^ 4 := hhi'
        _ ≤ (u ^ 17) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb4 4
        _ = u ^ 68 := by ring
    have hQ0 : (0 : ℝ) ≤ B.factorial := by positivity
    have h7 : u ≤ u ^ 7 := le_self_pow₀ hu1 (by norm_num)
    have h68' : 1 ≤ u ^ 68 := one_le_pow₀ hu1
    have k1 : (4 * (B.factorial : ℝ) + 1) * u ^ 68 ≤ u ^ 75 := by
      calc (4 * (B.factorial : ℝ) + 1) * u ^ 68 ≤ u * u ^ 68 :=
            mul_le_mul_of_nonneg_right huQ (by positivity)
        _ ≤ u ^ 7 * u ^ 68 := mul_le_mul_of_nonneg_right h7 (by positivity)
        _ = u ^ 75 := by ring
    have k2 : (P : ℝ) * B.factorial ≤ u ^ 68 * B.factorial :=
      mul_le_mul_of_nonneg_right h68 hQ0
    linarith
  have hcore := card_core (N0 := ⌊X⌋₊) (B := B) (y := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊) (b0 := b 0)
    (prodSet b 4)
    (fun P hP => ⟨(hTspec P hP).1, fun q hq hqP => ((hTspec P hP).2.1 q hq hqP).1,
      ((hTspec P hP).2.2.2.2).mono hb4y⟩)
    (le_trans hb04 hb4y) hBb hPbig hPsmall
  have h2N : 2 * ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := by
    apply Nat.le_floor; push_cast; linarith
  have hsub : (Ioc ⌊X⌋₊ (2 * ⌊X⌋₊)).filter (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
        ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) ⊆
      (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
        ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right h2N)
  calc (1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)) * X
      ≤ (1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)) * (2 * ⌊X⌋₊) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = ((⌊X⌋₊ : ℝ) / (2 * B.factorial)) * (1 / 5040) ^ 4 := by ring
    _ ≤ ((⌊X⌋₊ : ℝ) / (2 * B.factorial)) * ∑ P ∈ prodSet b 4, (1 : ℝ) / P :=
        mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ ≤ _ := hcore
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- `y`-pp-smooth integers in `(M, (1+η) M]` have reciprocal mass `≥ κ η`. -/
theorem mass_smooth_ge : ∃ κ : ℝ, 0 < κ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ M : ℕ in atTop,
    κ * η ≤ ((recipSum ((Ioc M ⌊(1 + η) * M⌋₊).filter
      (PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊)) : ℚ) : ℝ) := by
  obtain ⟨U₀, hU₀2, hU₀⟩ := exists_ranges
  refine ⟨(1 / 5040 : ℝ) ^ 5 / 4, by positivity, fun η hη hη1 => ?_⟩
  have hu : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hu.eventually_ge_atTop (max U₀ (4 / η))] with M hM
  generalize hu_def : (M : ℝ) ^ (1 / 100 : ℝ) = u at hM
  have huU : U₀ ≤ u := le_trans (le_max_left _ _) hM
  have hu4 : 4 / η ≤ u := le_trans (le_max_right _ _) hM
  have hu2 : 2 ≤ u := le_trans hU₀2 huU
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hu100 : u ^ 100 = (M : ℝ) := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hy : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 20 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hMpos : (0 : ℝ) < M := by rw [← hu100]; positivity
  have hux : u ≤ u ^ 17 := le_self_pow₀ hu1 (by norm_num)
  obtain ⟨b, hbmono, hb0, hb5, hR⟩ := hU₀ u huU (u ^ 17) hux le_rfl
  have hb5' : (b 5 : ℝ) ≤ u ^ 18 := by
    have h2 : u ^ 17 * u = u ^ 18 := by ring
    linarith
  have hb5y : b 5 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
    rw [hy]
    apply Nat.le_floor
    exact le_trans hb5' (pow_le_pow_right₀ hu1 (by norm_num))
  have hb05 : b 0 ≤ b 5 := hbmono (by norm_num)
  have hTsum := prodSet_sum_ge hbmono (by norm_num : (0 : ℝ) ≤ 1 / 5040) 5 hR
  have hTspec := prodSet_spec hbmono 5
  have hA1 : (1 + η) * (M : ℝ) - 1 < (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hA2 : ⌊(1 + η) * (M : ℝ)⌋₊ ≤ 2 * M := by
    have h1 : (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) ≤ (1 + η) * M :=
      Nat.floor_le (mul_nonneg (by linarith) hM0)
    have h2 : (1 + η) * (M : ℝ) ≤ 2 * M := by nlinarith
    have : (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) ≤ 2 * M := le_trans h1 h2
    exact_mod_cast this
  have hPbig : ∀ P ∈ prodSet b 5, ⌊(1 + η) * (M : ℝ)⌋₊ < P * (b 0 + 1) := by
    intro P hP
    obtain ⟨_, _, hlo, _, _⟩ := hTspec P hP
    have hlo' : ((b 0 : ℝ) + 1) ^ 5 ≤ P := by exact_mod_cast hlo
    have h6 : (u ^ 17) ^ 6 < ((b 0 : ℝ) + 1) ^ 6 :=
      pow_lt_pow_left₀ hb0 (by positivity) (by norm_num)
    have hu2' : 4 ≤ u ^ 2 := by nlinarith
    have h4M : 4 * (M : ℝ) ≤ u ^ 2 * u ^ 100 := by
      rw [hu100]; exact mul_le_mul_of_nonneg_right hu2' hM0
    have : (2 * M : ℝ) < P * ((b 0 : ℝ) + 1) := by
      calc (2 * M : ℝ) < u ^ 2 * u ^ 100 := by linarith
        _ = (u ^ 17) ^ 6 := by ring
        _ < ((b 0 : ℝ) + 1) ^ 6 := h6
        _ = ((b 0 : ℝ) + 1) ^ 5 * ((b 0 : ℝ) + 1) := by ring
        _ ≤ P * ((b 0 : ℝ) + 1) := mul_le_mul_of_nonneg_right hlo' (by positivity)
    have h2M : 2 * M < P * (b 0 + 1) := by exact_mod_cast this
    omega
  have hPsmall : ∀ P ∈ prodSet b 5, 4 * (P : ℝ) ≤ η * M := by
    intro P hP
    obtain ⟨_, _, _, hhi, _⟩ := hTspec P hP
    have hhi' : (P : ℝ) ≤ (b 5 : ℝ) ^ 5 := by exact_mod_cast hhi
    have h90 : (P : ℝ) ≤ u ^ 90 := by
      calc (P : ℝ) ≤ (b 5 : ℝ) ^ 5 := hhi'
        _ ≤ (u ^ 18) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb5' 5
        _ = u ^ 90 := by ring
    have h1 : 4 ≤ u * η := (div_le_iff₀ hη).mp hu4
    have h2 : u ≤ u ^ 10 := le_self_pow₀ hu1 (by norm_num)
    have hηu : 4 ≤ η * u ^ 10 := by
      have := mul_le_mul_of_nonneg_left h2 hη.le
      linarith
    have h3 : 4 * u ^ 90 ≤ η * u ^ 10 * u ^ 90 :=
      mul_le_mul_of_nonneg_right hηu (pow_pos hu0 90).le
    calc 4 * (P : ℝ) ≤ 4 * u ^ 90 := by linarith
      _ ≤ η * u ^ 10 * u ^ 90 := h3
      _ = η * M := by rw [← hu100]; ring
  have hcore := mass_core (M := M) (A := ⌊(1 + η) * (M : ℝ)⌋₊)
    (y := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊) (b0 := b 0) (η := η) (prodSet b 5)
    (fun P hP => ⟨(hTspec P hP).1, fun q hq hqP => ((hTspec P hP).2.1 q hq hqP).1,
      ((hTspec P hP).2.2.2.2).mono hb5y⟩)
    (le_trans hb05 hb5y) hPbig hPsmall hA1 hA2 (by exact_mod_cast hMpos)
  rw [recipSum_cast]
  calc (1 / 5040 : ℝ) ^ 5 / 4 * η = (η / 4) * (1 / 5040) ^ 5 := by ring
    _ ≤ (η / 4) * ∑ P ∈ prodSet b 5, (1 : ℝ) / P :=
        mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ ≤ _ := hcore

end Croot
end

section
/-!
# The core of Croot's Proposition 2 and the far-point lemma (Croot's Lemma 4, modified)

For `n` in the set `G` of pp-smooth rough integers near `X = M^{3/4} (log M)^4` and for each
prime `p ≤ y = ⌊M^{1/5}⌋` we construct `m = n · p^{a-e} · ℓ₁ ℓ₂ k ∈ (M, (1+η)M]` which is
`y`-pp-smooth and divisible by `n` and by `p^{⌊log_p y⌋}`.  The cofactor `m / n` lies in the
small set `cofSet B m`, which bounds how many `n` can produce the same `m`.  The far-point lemma
shows that for `M/2 ≤ |h| ≤ P/2` each core contains an element with no multiple near `h`.
-/

namespace Croot

open Real Finset Filter

/-- Prime powers dividing `m`. -/
def ppDivs (m : ℕ) : Finset ℕ := (Finset.Icc 1 m).filter (fun q => IsPrimePow q ∧ q ∣ m)

/-- The allowed cofactors `q · ℓ₁ · ℓ₂ · k` (with `q ∈ {1} ∪ ppDivs m`, `ℓᵢ ∣ m` prime, `k ≤ B`). -/
def cofSet (B m : ℕ) : Finset ℕ :=
  ((insert 1 (ppDivs m)) ×ˢ (m.primeFactors ×ˢ (m.primeFactors ×ˢ Finset.Icc 1 B))).image
    (fun t => t.1 * t.2.1 * t.2.2.1 * t.2.2.2)

namespace CoreAux

/-! ### Counting helpers -/

/-- `Ω(m) ≤ log₂ m`. -/
lemma sum_factorization_le_log (m : ℕ) (hm : m ≠ 0) :
    ∑ p ∈ m.primeFactors, m.factorization p ≤ Nat.log 2 m := by
  apply Nat.le_log_of_pow_le one_lt_two
  have hprod := Nat.prod_factorization_pow_eq_self hm
  rw [Finsupp.prod, Nat.support_factorization] at hprod
  calc 2 ^ (∑ p ∈ m.primeFactors, m.factorization p)
      = ∏ p ∈ m.primeFactors, 2 ^ m.factorization p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
        apply Finset.prod_le_prod'
        intro p hp
        exact Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
    _ = m := hprod

lemma card_primeFactors_le_log (m : ℕ) : m.primeFactors.card ≤ Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  calc m.primeFactors.card = ∑ p ∈ m.primeFactors, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        exact hpp.factorization_pos_of_dvd hpos.ne' (Nat.dvd_of_mem_primeFactors hp)
    _ ≤ Nat.log 2 m := sum_factorization_le_log m hpos.ne'

lemma card_ppDivs_le (m : ℕ) (hm : m ≠ 0) : (ppDivs m).card ≤ Nat.log 2 m := by
  have hsub : ppDivs m ⊆ m.primeFactors.biUnion
      (fun p => (Finset.Icc 1 (m.factorization p)).image (fun j => p ^ j)) := by
    intro q hq
    simp only [ppDivs, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqm⟩, hpp, hqd⟩ := hq
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hp, (dvd_pow_self p hk.ne').trans hqd, hm⟩
    · rw [Finset.mem_image]
      refine ⟨k, ?_, rfl⟩
      rw [Finset.mem_Icc]
      exact ⟨hk, (hp.pow_dvd_iff_le_factorization hm).1 hqd⟩
  calc (ppDivs m).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
        apply Finset.sum_le_sum
        intro p _
        refine Finset.card_image_le.trans ?_
        simp
    _ ≤ Nat.log 2 m := sum_factorization_le_log m hm

lemma card_cofSet_le (B m : ℕ) (hm : m ≠ 0) :
    (cofSet B m).card ≤ (Nat.log 2 m + 2) ^ 3 * B := by
  unfold cofSet
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Nat.card_Icc,
    Nat.add_sub_cancel]
  have h1 : (insert 1 (ppDivs m)).card ≤ Nat.log 2 m + 2 :=
    (Finset.card_insert_le _ _).trans (by have := card_ppDivs_le m hm; omega)
  have h2 : m.primeFactors.card ≤ Nat.log 2 m + 2 :=
    (card_primeFactors_le_log m).trans (by omega)
  calc (insert 1 (ppDivs m)).card * (m.primeFactors.card * (m.primeFactors.card * B))
      ≤ (Nat.log 2 m + 2) * ((Nat.log 2 m + 2) * ((Nat.log 2 m + 2) * B)) := by
        gcongr
    _ = (Nat.log 2 m + 2) ^ 3 * B := by ring

end CoreAux

/-- Few `n` can give the same `m`. -/
theorem card_fiber_le (B m : ℕ) (hm : 0 < m) (S : Finset ℕ) :
    (S.filter (fun n => n ∣ m ∧ m / n ∈ cofSet B m)).card ≤ (Nat.log 2 m + 2) ^ 3 * B := by
  refine le_trans ?_ (CoreAux.card_cofSet_le B m hm.ne')
  apply Finset.card_le_card_of_injOn (fun n => m / n)
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    exact hn.2.2
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    simp only at hab
    rw [← Nat.div_div_self ha.2.1 hm.ne', ← Nat.div_div_self hb.2.1 hm.ne', hab]

/-- A finite set of positive `y`-pp-smooth integers containing, for every prime `p ≤ y`, a
multiple of `p ^ ⌊log_p y⌋` has least common multiple `lcm(1, …, y)`. -/
theorem lcm_eq_lcmUpto (C : Finset ℕ) (y : ℕ) (hC : ∀ m ∈ C, 0 < m ∧ PPSmooth y m)
    (hfull : ∀ p : ℕ, p.Prime → p ≤ y → ∃ m ∈ C, p ^ Nat.log p y ∣ m) :
    C.lcm id = Nat.lcmUpto y := by
  have h0 : C.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    exact (hC x hx).1.ne' hx0
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro m hm
    exact (hC m hm).2.dvd_lcmUpto (hC m hm).1.ne'
  · rw [← Nat.factorization_le_iff_dvd (Nat.lcmUpto_ne_zero y) h0]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_lcmUpto y hp]
      by_cases hpy : p ≤ y
      · obtain ⟨m, hmC, hdvd⟩ := hfull p hp hpy
        have : p ^ Nat.log p y ∣ C.lcm id := hdvd.trans (Finset.dvd_lcm hmC)
        exact (hp.pow_dvd_iff_le_factorization h0).1 this
      · rw [Nat.log_of_lt (by omega)]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _

/-- Far-point lemma: if all elements of `C` are multiples of `n > 2W` and `W < |h|`,
`|h| + W < lcm C`, then some `m ∈ C` has no multiple within distance `< W` of `h`. -/
theorem exists_far (C : Finset ℕ) (n : ℕ) (W : ℝ) (h : ℤ) (hne : C.Nonempty)
    (_hpos : ∀ m ∈ C, 0 < m) (hdiv : ∀ m ∈ C, n ∣ m) (_hW : 0 ≤ W) (hn : 2 * W < n)
    (hh1 : W < |(h : ℝ)|) (hh2 : |(h : ℝ)| + W < ((C.lcm id : ℕ) : ℝ)) :
    ∃ m ∈ C, ∀ j : ℤ, W ≤ |(h : ℝ) - j * m| := by
  by_contra hcon
  push Not at hcon
  choose! J hJ using hcon
  obtain ⟨m₀, hm₀⟩ := hne
  set z : ℤ := J m₀ * (m₀ : ℤ) with hz
  have hzR : (z : ℝ) = (J m₀ : ℝ) * (m₀ : ℝ) := by rw [hz]; push_cast; ring
  have hz_near : |(h : ℝ) - z| < W := by rw [hzR]; exact hJ m₀ hm₀
  have key : ∀ m ∈ C, J m * (m : ℤ) = z := by
    intro m hm
    have h1 := hJ m hm
    have hdvd : (n : ℤ) ∣ J m * m - z := by
      apply dvd_sub
      · exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hdiv m hm)) _
      · exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hdiv m₀ hm₀)) _
    have habs : |J m * (m : ℤ) - z| < n := by
      have hR : |((J m * (m : ℤ) - z : ℤ) : ℝ)| < (n : ℝ) := by
        have e : ((J m * (m : ℤ) - z : ℤ) : ℝ)
            = -(((h : ℝ) - (J m : ℝ) * (m : ℝ)) - ((h : ℝ) - z)) := by
          push_cast; ring
        rw [e, abs_neg]
        calc |((h : ℝ) - (J m : ℝ) * (m : ℝ)) - ((h : ℝ) - z)|
            ≤ |(h : ℝ) - (J m : ℝ) * (m : ℝ)| + |(h : ℝ) - z| := abs_sub _ _
          _ < W + W := add_lt_add h1 hz_near
          _ < n := by linarith
      exact_mod_cast hR
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz_near
    simp at hz_near
    linarith
  have hLdvd : C.lcm id ∣ z.natAbs := by
    apply Finset.lcm_dvd
    intro m hm
    show m ∣ z.natAbs
    exact Int.natCast_dvd.1 ⟨J m, by rw [← key m hm]; ring⟩
  have hle : C.lcm id ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz0) hLdvd
  have hleR : ((C.lcm id : ℕ) : ℝ) ≤ |(z : ℝ)| := by
    have : ((C.lcm id : ℕ) : ℝ) ≤ ((z.natAbs : ℕ) : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hzh : |(z : ℝ)| ≤ |(h : ℝ)| + |(h : ℝ) - z| := by
    have := abs_sub_abs_le_abs_sub (z : ℝ) (h : ℝ)
    rw [abs_sub_comm (z : ℝ) (h : ℝ)] at this
    linarith
  linarith

namespace CoreAux

/-! ### Analytic helpers -/

lemma eventually_ten_log_le_sqrt : ∀ᶠ x : ℝ in atTop, 10 * Real.log x ≤ Real.sqrt x := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 / 2 by norm_num)).bound
    (show (0:ℝ) < 1 / 10 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
  linarith

/-- Supply of primes in `(x, 2.7 x]` avoiding a small exceptional set. -/
lemma exists_prime_avoid : ∃ x₀ : ℝ, 0 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ,
    ((E.card : ℝ)) ^ 2 ≤ x → ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((eventually_card_primes_Ioc_ge.and eventually_ten_log_le_sqrt).and
      (eventually_ge_atTop (2:ℝ)))
  refine ⟨max x₀ 0, le_max_right _ _, fun x hx E hE => ?_⟩
  obtain ⟨⟨hcard, hlog⟩, hx2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hE' : (E.card : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (Nat.cast_nonneg _) (by linarith)).2 hE
  have hlt : (E.card : ℝ) < (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    have h1 : (E.card : ℝ) * (5 * Real.log x) < x := by
      calc (E.card : ℝ) * (5 * Real.log x) ≤ Real.sqrt x * (Real.sqrt x / 2) :=
            mul_le_mul hE' (by linarith) (by positivity) hs0
        _ = x / 2 := by linear_combination (1 / 2 : ℝ) * hsx
        _ < x := by linarith
    calc (E.card : ℝ) < x / (5 * Real.log x) := by
          rw [lt_div_iff₀ (by positivity)]; exact h1
      _ ≤ _ := hcard
  have hlt' : E.card < ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card := by
    exact_mod_cast hlt
  obtain ⟨ℓ, hℓP, hℓE⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hℓP
  obtain ⟨⟨h1, h2⟩, hℓ⟩ := hℓP
  refine ⟨ℓ, hℓ, ?_, ?_, hℓE⟩
  · have h3 := Nat.lt_floor_add_one x
    have h1' : (⌊x⌋₊ : ℝ) + 1 ≤ ℓ := by exact_mod_cast Nat.succ_le_of_lt h1
    linarith
  · have h3 := Nat.floor_le (show (0:ℝ) ≤ 27 / 10 * x by linarith)
    have h2' : (ℓ : ℝ) ≤ (⌊(27 / 10 : ℝ) * x⌋₊ : ℝ) := by exact_mod_cast h2
    linarith

lemma eventually_log_pow_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 8 ≤ c * x ^ ((1 : ℝ) / 20) := by
  have h := (isLittleO_log_rpow_rpow_atTop (8 : ℝ) (show (0:ℝ) < 1 / 20 by norm_num)).bound hc
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  have h8 : Real.log x ^ (8 : ℝ) = Real.log x ^ (8 : ℕ) := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h8] at hx
  exact hx

lemma natLog2_le (n : ℕ) (hn : n ≠ 0) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log n := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

lemma exists_k_not_dvd {p : ℕ} (hp : p.Prime) {t η : ℝ} (ht : 0 ≤ t) (hηt : 2 ≤ η * t) :
    ∃ k : ℕ, 1 ≤ k ∧ ¬ p ∣ k ∧ t < k ∧ (k : ℝ) ≤ (1 + η) * t := by
  have h1 := Nat.lt_floor_add_one t
  have h2 := Nat.floor_le ht
  by_cases hdvd : p ∣ ⌊t⌋₊ + 1
  · refine ⟨⌊t⌋₊ + 1 + 1, by omega, ?_, ?_, ?_⟩
    · intro h
      have h' : p ∣ 1 := (Nat.dvd_add_right hdvd).1 h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h')
    · push_cast; linarith
    · push_cast; linarith
  · refine ⟨⌊t⌋₊ + 1, by omega, hdvd, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

/-! ### Arithmetic helpers -/

lemma ppSmooth_mul_coprime {y a b : ℕ} (hab : Nat.Coprime a b) (ha : PPSmooth y a)
    (hb : PPSmooth y b) : PPSmooth y (a * b) := by
  intro q hq
  rw [Nat.Coprime.primeFactors_mul hab, Finset.mem_union] at hq
  rw [Nat.factorization_mul_apply_of_coprime hab]
  rcases hq with hqa | hqb
  · have hb0 : b.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqb
      exact (Nat.prime_of_mem_primeFactors hqa).one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
          (Nat.dvd_of_mem_primeFactors hqa) hab) hqb)
    rw [hb0, add_zero]; exact ha q hqa
  · have ha0 : a.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqa
      exact (Nat.prime_of_mem_primeFactors hqb).one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqa hab)
          (Nat.dvd_of_mem_primeFactors hqb))
    rw [ha0, zero_add]; exact hb q hqb

lemma ppSmooth_prime {y ℓ : ℕ} (hℓ : ℓ.Prime) (hℓy : ℓ ≤ y) : PPSmooth y ℓ := by
  intro q hq
  rw [hℓ.primeFactors, Finset.mem_singleton] at hq
  subst hq
  rw [hℓ.factorization_self, pow_one]; exact hℓy

lemma ppSmooth_of_le {y k : ℕ} (hk : k ≤ y) : PPSmooth y k := by
  intro q hq
  exact (Nat.ordProj_le q (Nat.mem_primeFactors.1 hq).2.2).trans hk

lemma ppSmooth_prime_pow {y p a : ℕ} (hp : p.Prime) (hpa : p ^ a ≤ y) : PPSmooth y (p ^ a) := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hq' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).1 (hqp.dvd_of_dvd_pow hqd)
  subst hq'
  rw [hp.factorization_pow, Finsupp.single_eq_same]
  exact hpa

lemma cop_mul {a b c : ℕ} (h1 : Nat.Coprime a c) (h2 : Nat.Coprime b c) :
    Nat.Coprime (a * b) c := Nat.coprime_mul_iff_left.2 ⟨h1, h2⟩

lemma core_arith {B y n p ℓ₁ ℓ₂ k : ℕ} (hn : 0 < n) (hsm : PPSmooth y n)
    (hrough : ∀ q, q.Prime → q ≤ B → ¬ q ∣ n) (hp : p.Prime)
    (hℓ₁ : ℓ₁.Prime) (hℓ₂ : ℓ₂.Prime) (hℓ₁n : ¬ ℓ₁ ∣ n) (hℓ₂n : ¬ ℓ₂ ∣ n)
    (hℓ₁p : ℓ₁ ≠ p) (hℓ₂p : ℓ₂ ≠ p) (hℓ₁₂ : ℓ₁ ≠ ℓ₂) (hℓ₁B : B < ℓ₁) (hℓ₂B : B < ℓ₂)
    (hℓ₁y : ℓ₁ ≤ y) (hℓ₂y : ℓ₂ ≤ y) (hk1 : 1 ≤ k) (hkB : k ≤ B) (hBy : B ≤ y)
    (hpk : ¬ p ∣ k) (hy0 : y ≠ 0) :
    PPSmooth y (n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k)) ∧
    n ∣ n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) ∧
    p ^ Nat.log p y ∣ n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) ∧
    n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) / n ∈
      cofSet B (n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k)) := by
  set a := Nat.log p y with ha
  set e := n.factorization p with he
  have hea : e ≤ a := by
    by_cases hpn : p ∣ n
    · exact Nat.le_log_of_pow_le hp.one_lt (hsm p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩))
    · rw [he, Nat.factorization_eq_zero_of_not_dvd hpn]; exact Nat.zero_le _
  set m := n * (p ^ (a - e) * ℓ₁ * ℓ₂ * k) with hm
  have hk0 : k ≠ 0 := by omega
  have hm0 : m ≠ 0 := by
    rw [hm]
    apply Nat.mul_ne_zero hn.ne'
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero)
      hℓ₁.ne_zero) hℓ₂.ne_zero) hk0
  set n' := n / p ^ e with hn'
  have hn_eq : p ^ e * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hn'dvd : n' ∣ n := Nat.ordCompl_dvd n p
  have hm_eq : m = p ^ a * n' * ℓ₁ * ℓ₂ * k := by
    calc m = (p ^ e * n') * (p ^ (a - e) * ℓ₁ * ℓ₂ * k) := by rw [hm, hn_eq]
      _ = p ^ (e + (a - e)) * n' * ℓ₁ * ℓ₂ * k := by rw [pow_add]; ring
      _ = p ^ a * n' * ℓ₁ * ℓ₂ * k := by rw [Nat.add_sub_cancel' hea]
  -- coprimality facts
  have hc_p_ℓ₁ : Nat.Coprime p ℓ₁ := (Nat.coprime_primes hp hℓ₁).2 (Ne.symm hℓ₁p)
  have hc_p_ℓ₂ : Nat.Coprime p ℓ₂ := (Nat.coprime_primes hp hℓ₂).2 (Ne.symm hℓ₂p)
  have hc_ℓ₁_ℓ₂ : Nat.Coprime ℓ₁ ℓ₂ := (Nat.coprime_primes hℓ₁ hℓ₂).2 hℓ₁₂
  have hc_p_n' : Nat.Coprime p n' := Nat.coprime_ordCompl hp hn.ne'
  have hc_n'_ℓ₁ : Nat.Coprime n' ℓ₁ := Nat.Coprime.symm
    ((Nat.Prime.coprime_iff_not_dvd hℓ₁).2 (fun h => hℓ₁n (h.trans hn'dvd)))
  have hc_n'_ℓ₂ : Nat.Coprime n' ℓ₂ := Nat.Coprime.symm
    ((Nat.Prime.coprime_iff_not_dvd hℓ₂).2 (fun h => hℓ₂n (h.trans hn'dvd)))
  have hc_p_k : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
  have hc_ℓ₁_k : Nat.Coprime ℓ₁ k := (Nat.Prime.coprime_iff_not_dvd hℓ₁).2 (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)
  have hc_ℓ₂_k : Nat.Coprime ℓ₂ k := (Nat.Prime.coprime_iff_not_dvd hℓ₂).2 (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)
  have hc_n'_k : Nat.Coprime n' k := Nat.coprime_of_dvd (fun q hq hqn' hqk => by
    have hqB : q ≤ B := (Nat.le_of_dvd (by omega) hqk).trans hkB
    exact hrough q hq hqB (hqn'.trans hn'dvd))
  -- smoothness
  have hsm_m : PPSmooth y m := by
    rw [hm_eq]
    have hpa : p ^ a ≤ y := Nat.pow_log_le_self p hy0
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_of_le (hkB.trans hBy))
    · exact cop_mul (cop_mul (cop_mul (Nat.Coprime.pow_left a hc_p_k) hc_n'_k) hc_ℓ₁_k) hc_ℓ₂_k
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_prime hℓ₂ hℓ₂y)
    · exact cop_mul (cop_mul (Nat.Coprime.pow_left a hc_p_ℓ₂) hc_n'_ℓ₂) hc_ℓ₁_ℓ₂
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_prime hℓ₁ hℓ₁y)
    · exact cop_mul (Nat.Coprime.pow_left a hc_p_ℓ₁) hc_n'_ℓ₁
    exact ppSmooth_mul_coprime (Nat.Coprime.pow_left a hc_p_n') (ppSmooth_prime_pow hp hpa)
      (hsm.of_dvd hn.ne' hn'dvd)
  have hdiv : m / n = p ^ (a - e) * ℓ₁ * ℓ₂ * k := by
    rw [hm]; exact Nat.mul_div_cancel_left _ hn
  have hmem : p ^ (a - e) * ℓ₁ * ℓ₂ * k ∈ cofSet B m := by
    unfold cofSet
    rw [Finset.mem_image]
    refine ⟨(p ^ (a - e), ℓ₁, ℓ₂, k), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hae : a - e = 0
      · left; rw [hae, pow_zero]
      · right
        unfold ppDivs
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hd : p ^ (a - e) ∣ m := Dvd.intro (n * ℓ₁ * ℓ₂ * k) (by rw [hm]; ring)
        exact ⟨⟨Nat.one_le_pow _ _ hp.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd⟩,
          hp.isPrimePow.pow hae, hd⟩
    · exact Nat.mem_primeFactors.2
        ⟨hℓ₁, Dvd.intro (n * p ^ (a - e) * ℓ₂ * k) (by rw [hm]; ring), hm0⟩
    · exact Nat.mem_primeFactors.2
        ⟨hℓ₂, Dvd.intro (n * p ^ (a - e) * ℓ₁ * k) (by rw [hm]; ring), hm0⟩
    · exact ⟨hk1, hkB⟩
  refine ⟨hsm_m, ⟨_, hm⟩, ?_, ?_⟩
  · rw [hm_eq]; exact Dvd.intro (n' * ℓ₁ * ℓ₂ * k) (by ring)
  · rw [hdiv]; exact hmem

lemma core_W_bounds {u L D W : ℝ} (hu0 : 0 < u) (hL1 : 1 ≤ L) (hD_lo : u ^ 30 * L ^ 4 < D)
    (hD_hi : D ≤ 2 * L ^ 4 * u ^ 38) (hWD : W * D = u ^ 40) (hWpos : 0 < W) :
    u ^ 2 ≤ 2 * L ^ 4 * W ∧ W < u ^ 10 := by
  constructor
  · have h1 : u ^ 2 * u ^ 38 ≤ (2 * L ^ 4 * W) * u ^ 38 := by
      calc u ^ 2 * u ^ 38 = W * D := by rw [hWD]; ring
        _ ≤ W * (2 * L ^ 4 * u ^ 38) := mul_le_mul_of_nonneg_left hD_hi hWpos.le
        _ = (2 * L ^ 4 * W) * u ^ 38 := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  · have h1 : (W * L ^ 4) * u ^ 30 < u ^ 10 * u ^ 30 := by
      calc (W * L ^ 4) * u ^ 30 = W * (u ^ 30 * L ^ 4) := by ring
        _ < W * D := mul_lt_mul_of_pos_left hD_lo hWpos
        _ = u ^ 10 * u ^ 30 := by rw [hWD]; ring
    have h2 : W * L ^ 4 < u ^ 10 := lt_of_mul_lt_mul_right h1 (by positivity)
    have h3 : W ≤ W * L ^ 4 := le_mul_of_one_le_right hWpos.le (one_le_pow₀ hL1)
    linarith

lemma core_s_bounds {η x₀ b u L W s : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hx₀ : 0 ≤ x₀)
    (hb : 0 ≤ b) (hu0 : 0 < u) (hL1 : 1 ≤ L)
    (hC : 117 * (x₀ + b + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    (hW_lo : u ^ 2 ≤ 2 * L ^ 4 * W) (hW_hi : W < u ^ 10) (hWpos : 0 < W)
    (hs_pos : 0 < s) (hsV : s * s = η * W / 8) :
    27 / 10 * (x₀ + b + 16 * L ^ 2) ≤ s ∧ s ≤ u ^ 5 := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hK0 : 0 ≤ x₀ + b + 16 * L ^ 2 := by positivity
  have hK_le : x₀ + b + 16 * L ^ 2 ≤ (x₀ + b + 16) * L ^ 2 := by
    nlinarith [mul_nonneg hx₀ (sub_nonneg.2 hL2), mul_nonneg hb (sub_nonneg.2 hL2)]
  constructor
  · have h1 : η * u ^ 2 ≤ 16 * L ^ 4 * (s * s) := by
      rw [hsV]; nlinarith [mul_le_mul_of_nonneg_left hW_lo hη.le]
    have h2 : (x₀ + b + 16 * L ^ 2) ^ 2 ≤ ((x₀ + b + 16) * L ^ 2) ^ 2 :=
      pow_le_pow_left₀ hK0 hK_le 2
    have h3 : (27 / 10 * (x₀ + b + 16 * L ^ 2)) ^ 2 * (16 * L ^ 4) ≤ s ^ 2 * (16 * L ^ 4) := by
      calc (27 / 10 * (x₀ + b + 16 * L ^ 2)) ^ 2 * (16 * L ^ 4)
          = 11664 / 100 * (x₀ + b + 16 * L ^ 2) ^ 2 * L ^ 4 := by ring
        _ ≤ 11664 / 100 * ((x₀ + b + 16) * L ^ 2) ^ 2 * L ^ 4 := by gcongr
        _ = 11664 / 100 * (x₀ + b + 16) ^ 2 * L ^ 8 := by ring
        _ ≤ 117 * (x₀ + b + 16) ^ 2 * L ^ 8 := by gcongr; norm_num
        _ ≤ η * u ^ 2 := hC
        _ ≤ 16 * L ^ 4 * (s * s) := h1
        _ = s ^ 2 * (16 * L ^ 4) := by ring
    exact le_of_pow_le_pow_left₀ two_ne_zero hs_pos.le
      (le_of_mul_le_mul_right h3 (by positivity))
  · have h1 : s ^ 2 ≤ (u ^ 5) ^ 2 := by
      have : η * W ≤ W := by nlinarith
      nlinarith [hW_hi]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h1

lemma core_n_le_M {η x₀ b u L : ℝ} {n M : ℕ} (hη1 : η ≤ 1) (hx₀ : 0 ≤ x₀) (hb : 0 ≤ b)
    (hu1 : 1 ≤ u) (hL1 : 1 ≤ L) (hC : 117 * (x₀ + b + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    (hn2 : (n : ℝ) ≤ 2 * (u ^ 30 * L ^ 4)) (hM : (M : ℝ) = u ^ 40) : n ≤ M := by
  have h2L : 2 * L ^ 4 ≤ u ^ 10 := by
    have h16 : (16:ℝ) ^ 2 ≤ (x₀ + b + 16) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hL8 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    have hu2 : u ^ 2 ≤ u ^ 10 := pow_le_pow_right₀ hu1 (by norm_num)
    have hL8' : 0 ≤ L ^ 8 := by positivity
    have h3 : (16:ℝ) ^ 2 * L ^ 8 ≤ (x₀ + b + 16) ^ 2 * L ^ 8 :=
      mul_le_mul_of_nonneg_right h16 hL8'
    have hηu : η * u ^ 2 ≤ u ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hη1) (sq_nonneg u)]
    linarith
  have : (n : ℝ) ≤ M := by
    rw [hM]
    calc (n:ℝ) ≤ 2 * (u ^ 30 * L ^ 4) := hn2
      _ = (2 * L ^ 4) * u ^ 30 := by ring
      _ ≤ u ^ 10 * u ^ 30 := by gcongr
      _ = u ^ 40 := by ring
  exact_mod_cast this

lemma card_pf_sq_le {n M : ℕ} {L : ℝ} (hn0 : 0 < n) (hnM : n ≤ M) (hLM : Real.log M ≤ L)
    (hL1 : 1 ≤ L) : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ 16 * L ^ 2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have h1 := natLog2_le n hn0.ne'
  have h2 : Real.log n ≤ Real.log M := Real.log_le_log hnR (by exact_mod_cast hnM)
  have h3 : (n.primeFactors.card : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast card_primeFactors_le_log n
  have h4 : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ≤ 4 * L := by push_cast; linarith
  calc (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ (4 * L) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h4 2
    _ = 16 * L ^ 2 := by ring

/-- Choice of the two auxiliary primes `ℓ₁ ∈ (10s/27, s]` and `ℓ₂ ∈ (s²/ℓ₁, 2.7 s²/ℓ₁]`. -/
lemma core_two_primes {x₀ s : ℝ}
    (hprime : ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ, ((E.card : ℝ)) ^ 2 ≤ x →
      ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E)
    (hs_pos : 0 < s) {n : ℕ} (hn0 : 0 < n) (p : ℕ) (hx₀ : x₀ ≤ 10 * s / 27)
    (hcard : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ 10 * s / 27) :
    ∃ ℓ₁ ℓ₂ : ℕ, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ¬ ℓ₁ ∣ n ∧ ¬ ℓ₂ ∣ n ∧ ℓ₁ ≠ p ∧ ℓ₂ ≠ p ∧ ℓ₁ ≠ ℓ₂ ∧
      10 * s / 27 < ℓ₁ ∧ 10 * s / 27 < ℓ₂ ∧ (ℓ₁ : ℝ) ≤ s ∧ (ℓ₂ : ℝ) ≤ 729 / 100 * s ∧
      s * s < (ℓ₁ : ℝ) * ℓ₂ ∧ (ℓ₁ : ℝ) * ℓ₂ ≤ 27 / 10 * (s * s) := by
  have hcardE : ∀ E : Finset ℕ, E.card ≤ n.primeFactors.card + 2 → ∀ x : ℝ,
      10 * s / 27 ≤ x → ((E.card : ℝ)) ^ 2 ≤ x := by
    intro E hE x hx
    have h1 : (E.card : ℝ) ≤ ((n.primeFactors.card + 2 : ℕ) : ℝ) := by exact_mod_cast hE
    calc (E.card : ℝ) ^ 2 ≤ (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      _ ≤ 10 * s / 27 := hcard
      _ ≤ x := hx
  obtain ⟨ℓ₁, hℓ₁, hℓ₁x, hℓ₁s, hℓ₁E⟩ := hprime (10 * s / 27) hx₀ (insert p n.primeFactors)
    (hcardE _ ((Finset.card_insert_le _ _).trans (by omega)) _ le_rfl)
  rw [Finset.mem_insert, not_or] at hℓ₁E
  obtain ⟨hℓ₁p, hℓ₁n⟩ := hℓ₁E
  have hℓ₁R : (ℓ₁ : ℝ) ≤ s := by linarith
  have hℓ₁pos : (0:ℝ) < ℓ₁ := by exact_mod_cast hℓ₁.pos
  have hsx₂ : s ≤ s * s / ℓ₁ := by
    rw [le_div_iff₀ hℓ₁pos]
    exact mul_le_mul_of_nonneg_left hℓ₁R hs_pos.le
  have hx₁x₂ : 10 * s / 27 ≤ s * s / ℓ₁ := le_trans (by linarith) hsx₂
  obtain ⟨ℓ₂, hℓ₂, hℓ₂x, hℓ₂le, hℓ₂E⟩ := hprime (s * s / ℓ₁) (hx₀.trans hx₁x₂)
    (insert ℓ₁ (insert p n.primeFactors))
    (hcardE _ (by
      have h1 := Finset.card_insert_le ℓ₁ (insert p n.primeFactors)
      have h2 := Finset.card_insert_le p n.primeFactors
      omega) _ hx₁x₂)
  rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hℓ₂E
  obtain ⟨hℓ₂ℓ₁, hℓ₂p, hℓ₂n⟩ := hℓ₂E
  have hℓ₁ne : (ℓ₁ : ℝ) ≠ 0 := hℓ₁pos.ne'
  refine ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, fun h => hℓ₁n (Nat.mem_primeFactors.2 ⟨hℓ₁, h, hn0.ne'⟩),
    fun h => hℓ₂n (Nat.mem_primeFactors.2 ⟨hℓ₂, h, hn0.ne'⟩), hℓ₁p, hℓ₂p, Ne.symm hℓ₂ℓ₁,
    hℓ₁x, lt_of_le_of_lt hx₁x₂ hℓ₂x, hℓ₁R, ?_, ?_, ?_⟩
  · have h1 : s * s / ℓ₁ ≤ s * s / (10 * s / 27) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ₁x.le
    have h2 : s * s / (10 * s / 27) = 27 / 10 * s := by field_simp
    calc (ℓ₂ : ℝ) ≤ 27 / 10 * (s * s / ℓ₁) := hℓ₂le
      _ ≤ 27 / 10 * (s * s / (10 * s / 27)) := by gcongr
      _ = 729 / 100 * s := by rw [h2]; ring
  · have h1 := hℓ₂x
    rw [div_lt_iff₀ hℓ₁pos] at h1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hℓ₂le hℓ₁pos.le
    calc (ℓ₁ : ℝ) * ℓ₂ ≤ ℓ₁ * (27 / 10 * (s * s / ℓ₁)) := h1
      _ = 27 / 10 * (s * s) := by field_simp

/-- The deterministic construction behind `core_exists`, with all `M` large facts as
hypotheses. Here `u = M^{1/40}`, `L = log M`, `y = ⌊u^8⌋`. -/
lemma core_det {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hprime : ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ, ((E.card : ℝ)) ^ 2 ≤ x →
      ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E)
    {B y M : ℕ} {u L : ℝ} (hB : 16 / η ≤ B) (hBy : B ≤ y)
    (hy1 : (y : ℝ) ≤ u ^ 8) (hy2 : ∀ ℓ : ℕ, (ℓ : ℝ) ≤ u ^ 8 → ℓ ≤ y)
    (hM : (M : ℝ) = u ^ 40) (hu : 2 ≤ u) (hL1 : 1 ≤ L) (hLM : Real.log M ≤ L)
    (hC : 117 * (x₀ + B + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    {n : ℕ} (hn1 : u ^ 30 * L ^ 4 < n) (hn2 : (n : ℝ) ≤ 2 * (u ^ 30 * L ^ 4))
    (hsm : PPSmooth y n) (hrough : ∀ q, q.Prime → q ≤ B → ¬ q ∣ n)
    {p : ℕ} (hp : p.Prime) (hpy : p ≤ y) :
    ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth y m ∧
      n ∣ m ∧ p ^ Nat.log p y ∣ m ∧ m / n ∈ cofSet B m := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hB0 : (0:ℝ) ≤ B := Nat.cast_nonneg B
  have hnR : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn1
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hy0 : y ≠ 0 := by have := hp.two_le; omega
  -- the cofactor `r = p ^ (a - e)`
  set r := p ^ (Nat.log p y - n.factorization p) with hr
  have hr1R : (1:ℝ) ≤ r := by exact_mod_cast Nat.one_le_pow _ _ hp.pos
  have hry : r ≤ y :=
    le_trans (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)) (Nat.pow_log_le_self p hy0)
  have hryR : (r:ℝ) ≤ u ^ 8 := le_trans (by exact_mod_cast hry) hy1
  -- `D = n r` and `W = M / D`
  set D : ℝ := (n : ℝ) * r with hD
  have hDpos : 0 < D := by positivity
  have hD_lo : u ^ 30 * L ^ 4 < D := by
    calc u ^ 30 * L ^ 4 < n := hn1
      _ = n * 1 := (mul_one _).symm
      _ ≤ D := mul_le_mul_of_nonneg_left hr1R hnR.le
  have hD_hi : D ≤ 2 * L ^ 4 * u ^ 38 := by
    calc D = n * r := rfl
      _ ≤ (2 * (u ^ 30 * L ^ 4)) * u ^ 8 := mul_le_mul hn2 hryR (by positivity) (by positivity)
      _ = 2 * L ^ 4 * u ^ 38 := by ring
  set W : ℝ := (M : ℝ) / D with hW
  have hWD : W * D = u ^ 40 := by rw [hW, div_mul_cancel₀ _ hDpos.ne', hM]
  have hWpos : 0 < W := by rw [hW, hM]; positivity
  obtain ⟨hW_lo, hW_hi⟩ := core_W_bounds hu0 hL1 hD_lo hD_hi hWD hWpos
  -- `s = √(ηW/8)`
  obtain ⟨s, hs_pos, hsV⟩ : ∃ s : ℝ, 0 < s ∧ s * s = η * W / 8 :=
    ⟨Real.sqrt (η * W / 8), Real.sqrt_pos.2 (by positivity), Real.mul_self_sqrt (by positivity)⟩
  obtain ⟨hs_lo, hs_hi⟩ :=
    core_s_bounds hη hη1 hx₀ hB0 hu0 hL1 hC hW_lo hW_hi hWpos hs_pos hsV
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hnM : n ≤ M := core_n_le_M hη1 hx₀ hB0 hu1 hL1 hC hn2 hM
  have hcard := card_pf_sq_le hn0 hnM hLM hL1
  -- the two primes
  obtain ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, hℓ₁n, hℓ₂n, hℓ₁p, hℓ₂p, hℓ₁₂, hℓ₁x, hℓ₂x, hℓ₁R, hℓ₂R, hP_lo,
    hP_hi⟩ := core_two_primes hprime hs_pos hn0 p (by linarith only [hs_lo, hB0, hL2])
      (by linarith only [hs_lo, hB0, hx₀, hcard])
  -- the integer `k`
  set P : ℝ := (ℓ₁ : ℝ) * ℓ₂ with hP
  have hPpos : 0 < P := lt_trans (mul_pos hs_pos hs_pos) hP_lo
  have hηW : η * W = 8 * (s * s) := by rw [hsV]; ring
  have hηt : 2 ≤ η * (W / P) := by
    rw [← mul_div_assoc, le_div_iff₀ hPpos, hηW]
    nlinarith only [hP_hi, mul_pos hs_pos hs_pos]
  have ht_hi : W / P < 8 / η := by
    rw [div_lt_div_iff₀ hPpos hη]
    nlinarith only [hP_lo, hηW]
  have ht0 : 0 ≤ W / P := by positivity
  obtain ⟨k, hk1, hpk, htk, hk_hi⟩ := exists_k_not_dvd hp ht0 hηt
  have hkB : k ≤ B := by
    have h1 : (k : ℝ) ≤ B := by
      have h2 : (1 + η) * (W / P) ≤ 2 * (W / P) := by
        nlinarith only [mul_le_mul_of_nonneg_right hη1 ht0]
      calc (k : ℝ) ≤ (1 + η) * (W / P) := hk_hi
        _ ≤ 2 * (W / P) := h2
        _ ≤ 2 * (8 / η) := by linarith only [ht_hi]
        _ = 16 / η := by ring
        _ ≤ B := hB
    exact_mod_cast h1
  have hBx₁ : (B : ℝ) ≤ 10 * s / 27 := by linarith only [hs_lo, hx₀, hL2]
  have hℓ₁B : B < ℓ₁ := by exact_mod_cast lt_of_le_of_lt hBx₁ hℓ₁x
  have hℓ₂B : B < ℓ₂ := by exact_mod_cast lt_of_le_of_lt hBx₁ hℓ₂x
  have hu58 : u ^ 5 ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hℓ₁y : ℓ₁ ≤ y := hy2 ℓ₁ (by linarith only [hℓ₁R, hs_hi, hu58])
  have hℓ₂y : ℓ₂ ≤ y := hy2 ℓ₂ (by
    have hu3 : (8:ℝ) ≤ u ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    calc (ℓ₂ : ℝ) ≤ 729 / 100 * s := hℓ₂R
      _ ≤ 729 / 100 * u ^ 5 := by gcongr
      _ ≤ u ^ 3 * u ^ 5 := by gcongr; linarith only [hu3]
      _ = u ^ 8 := by ring)
  obtain ⟨hsm', hdvd1, hdvd2, hcof⟩ := core_arith hn0 hsm hrough hp hℓ₁ hℓ₂ hℓ₁n hℓ₂n
    hℓ₁p hℓ₂p hℓ₁₂ hℓ₁B hℓ₂B hℓ₁y hℓ₂y hk1 hkB hBy hpk hy0
  have hmR : ((n * (r * ℓ₁ * ℓ₂ * k) : ℕ) : ℝ) = D * (P * k) := by
    rw [hD, hP]; push_cast; ring
  have hPt : P * (W / P) = W := by field_simp
  refine ⟨n * (r * ℓ₁ * ℓ₂ * k), ?_, ?_, hsm', hdvd1, hdvd2, hcof⟩
  · have h1 : (M : ℝ) < ((n * (r * ℓ₁ * ℓ₂ * k) : ℕ) : ℝ) := by
      rw [hmR]
      calc (M : ℝ) = D * (P * (W / P)) := by rw [hPt, hM, ← hWD]; ring
        _ < D * (P * k) := by gcongr
    exact_mod_cast h1
  · rw [hmR]
    calc D * (P * k) ≤ D * (P * ((1 + η) * (W / P))) := by gcongr
      _ = (1 + η) * (D * (P * (W / P))) := by ring
      _ = (1 + η) * (W * D) := by rw [hPt]; ring
      _ = (1 + η) * M := by rw [hWD, hM]

end CoreAux

/-- Construction of the core elements. -/
theorem core_exists (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∀ᶠ M : ℕ in atTop,
    ∀ n : ℕ, (M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4 < n →
      (n : ℝ) ≤ 2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) →
      PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n → (∀ p ∈ Finset.Iic ⌈16 / η⌉₊, p.Prime → ¬ p ∣ n) →
      ∀ p : ℕ, p.Prime → p ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ →
        ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ m ∧
          n ∣ m ∧ p ^ Nat.log p ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ ∣ m ∧ m / n ∈ cofSet ⌈16 / η⌉₊ m := by
  obtain ⟨x₀, hx₀, hprime⟩ := CoreAux.exists_prime_avoid
  set B := ⌈16 / η⌉₊ with hBdef
  have hB : 16 / η ≤ (B : ℝ) := Nat.le_ceil _
  have hK0 : 0 < 117 * (x₀ + (B : ℝ) + 16) ^ 2 := by positivity
  have hev1 := CoreAux.eventually_log_pow_le (η / (117 * (x₀ + (B : ℝ) + 16) ^ 2))
    (div_pos hη hK0)
  have hev2 : ∀ᶠ x : ℝ in atTop, max 2 (B : ℝ) ≤ x ^ ((1 : ℝ) / 40) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have hev3 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev1.and (hev2.and hev3))] with M hM
  obtain ⟨h1, h2, h3⟩ := hM
  intro n hn1 hn2 hsm hrough p hp hpy
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set u : ℝ := (M : ℝ) ^ ((1 : ℝ) / 40) with hu
  have hpow : ∀ k : ℕ, (M : ℝ) ^ ((1 : ℝ) / 40 * (k : ℝ)) = u ^ k :=
    fun k => Real.rpow_mul_natCast hM0 _ _
  have e30 : (M : ℝ) ^ (3 / 4 : ℝ) = u ^ 30 := by rw [← hpow 30]; norm_num
  have e8 : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 8 := by rw [← hpow 8]; norm_num
  have e2 : (M : ℝ) ^ ((1 : ℝ) / 20) = u ^ 2 := by rw [← hpow 2]; norm_num
  have e40 : (M : ℝ) = u ^ 40 := by rw [← hpow 40]; norm_num
  rw [e30] at hn1 hn2
  rw [e8] at hsm hpy ⊢
  rw [e2] at h1
  have hu2 : 2 ≤ u := le_trans (le_max_left _ _) h2
  have huB : (B : ℝ) ≤ u := le_trans (le_max_right _ _) h2
  have hu1 : 1 ≤ u := by linarith
  have hC : 117 * (x₀ + B + 16) ^ 2 * Real.log M ^ 8 ≤ η * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    calc 117 * (x₀ + B + 16) ^ 2 * Real.log M ^ 8
        = 117 * (x₀ + B + 16) ^ 2 * (Real.log M ^ 8) := by ring
      _ ≤ 117 * (x₀ + B + 16) ^ 2 * (η / (117 * (x₀ + B + 16) ^ 2) * u ^ 2) := this
      _ = η * u ^ 2 := by field_simp
  have hu8 : u ≤ u ^ 8 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hBy : B ≤ ⌊u ^ 8⌋₊ := Nat.le_floor (by linarith)
  exact CoreAux.core_det hη hη1 hx₀ hprime hB hBy (Nat.floor_le (by positivity))
    (fun ℓ hℓ => Nat.le_floor hℓ) e40 hu2 h3 le_rfl hC hn1 hn2 hsm
    (fun q hq hqB => hrough q (Finset.mem_Iic.2 hqB) hq) hp hpy

end Croot
end

section
/-!
# Elementary asymptotic facts used in the assembly of Croot's theorem

All statements are of the form for all sufficiently large `M` (or `N`); they only involve
powers, logarithms, `exp`, `Nat.log`, floors and `Nat.lcmUpto` (bounded via Chebyshev's
elementary estimates `2 ^ n ≤ (n + 1) lcm(1..n)` and `ψ(n) ≤ π(n) log n`).
-/

namespace Croot

open Real Finset Filter

namespace AsymAux

/-! ### Generic eventual bounds along `ℕ` -/

lemma ev_rpow_ge {s : ℝ} (hs : 0 < s) (C : ℝ) : ∀ᶠ M : ℕ in atTop, C ≤ (M : ℝ) ^ s :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hs).eventually_ge_atTop C)

lemma ev_log_ge (C : ℝ) : ∀ᶠ M : ℕ in atTop, C ≤ Real.log (M : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop C)

/-- `(log M)^n ≤ c M^s` eventually, for any `s > 0` and `c > 0`. -/
lemma ev_log_pow_le (n : ℕ) {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop, Real.log (M : ℝ) ^ n ≤ c * (M : ℝ) ^ s := by
  have h : ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ c * x ^ s := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).bound hc,
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.rpow_natCast]
    have h2 : ‖x ^ s‖ = x ^ s := Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)
    calc Real.log x ^ n = ‖Real.log x ^ (n : ℝ)‖ := h1.symm
      _ ≤ c * ‖x ^ s‖ := hx
      _ = c * x ^ s := by rw [h2]
  exact tendsto_natCast_atTop_atTop.eventually h

/-! ### Numerical facts about logarithms -/

lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h2 : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
  linarith

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma log_four_le_three : Real.log 4 ≤ 3 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  linarith

/-! ### The individual clauses of `prop2_eventually`, for a real variable `x` -/

lemma clause2 {x : ℝ} (hx : 0 < x) (hL : 2 ≤ Real.log x) :
    2 * x ^ (3 / 4 : ℝ) < x ^ (3 / 4 : ℝ) * Real.log x ^ 4 := by
  have h1 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have h2 : (2 : ℝ) ^ 4 ≤ Real.log x ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]

lemma clause3 {x : ℝ} (hx : 0 < x) (h4 : 3 ≤ x ^ (1 / 4 : ℝ)) :
    x ^ (3 / 4 : ℝ) < x / 2 := by
  have e : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have h1 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  nlinarith [mul_le_mul_of_nonneg_left h4 h1.le]

/-- Clause 4: written with `w = x^{1/420}`, it reduces to `12 (log x)^4 ≤ w`. -/
lemma clause4 {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hy : y ≤ x ^ (1 / 5 : ℝ))
    (hL : 1 ≤ Real.log x) (hw1 : 1 ≤ x ^ (1 / 420 : ℝ))
    (hkey : Real.log x ^ 4 ≤ 1 / 12 * x ^ (1 / 420 : ℝ)) :
    (2 * (x ^ (3 / 4 : ℝ) * Real.log x ^ 4) + 1) * (y + 1) / x ≤ x ^ (-(1 / 21 : ℝ)) / 2 := by
  have e1 : x ^ (3 / 4 : ℝ) = (x ^ (1 / 420 : ℝ)) ^ (315 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e2 : x ^ (1 / 5 : ℝ) = (x ^ (1 / 420 : ℝ)) ^ (84 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e5 : x ^ (-(1 / 21 : ℝ)) / 2 * x = (x ^ (1 / 420 : ℝ)) ^ (400 : ℕ) / 2 := by
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hx.ne', ← Real.rpow_natCast,
      ← Real.rpow_mul hx.le]
    norm_num
  rw [div_le_iff₀ hx, e5, e1]
  rw [e2] at hy
  generalize Real.log x = L at hL hkey ⊢
  generalize x ^ (1 / 420 : ℝ) = w at hw1 hkey hy ⊢
  have hA : 1 ≤ w ^ 315 * L ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hw1) (one_le_pow₀ hL)
  have hC : 1 ≤ w ^ 84 := one_le_pow₀ hw1
  have hw0 : 0 ≤ w := by linarith
  calc (2 * (w ^ 315 * L ^ 4) + 1) * (y + 1)
      ≤ (3 * (w ^ 315 * L ^ 4)) * (2 * w ^ 84) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    _ = w ^ 399 * (6 * L ^ 4) := by ring
    _ ≤ w ^ 399 * (w / 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = w ^ 400 / 2 := by ring

lemma clause5 {x η : ℝ} (hx : 0 < x) (hη : 0 < η) (h3 : x ^ (3 / 4 : ℝ) < x / 2) :
    x ^ (3 / 4 : ℝ) / ((1 + η) * x) ≤ 1 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hη hx]

/-- Clause 6, via Chebyshev's lower bound `ψ(u) ≥ (u - 1) log 2 - log (u + 2)`. -/
lemma clause6 {x : ℝ} (hx : 0 < x) (hu : 12 ≤ x ^ (1 / 5 : ℝ))
    (hlog : Real.log x ≤ 1 / 4 * x ^ (1 / 5 : ℝ)) :
    2 * x ^ (3 / 4 : ℝ) < (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
  have hu0 : 0 < x ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hx _
  have hP : (0 : ℝ) < (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have hpsi : (x ^ (1 / 5 : ℝ) - 1) * Real.log 2 - Real.log (x ^ (1 / 5 : ℝ) + 2) ≤
      Real.log (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto, ← Chebyshev.psi_eq_psi_coe_floor]
    exact Chebyshev.psi_ge' hu0.le
  have hlog2 := log_two_ge_half
  have hlog2' := log_two_le_one
  have hlu : Real.log (x ^ (1 / 5 : ℝ)) = 1 / 5 * Real.log x := Real.log_rpow hx _
  have hmul : Real.log (2 * x ^ (1 / 5 : ℝ)) = Real.log 2 + Real.log (x ^ (1 / 5 : ℝ)) :=
    Real.log_mul two_ne_zero hu0.ne'
  have hlu2 : Real.log (x ^ (1 / 5 : ℝ) + 2) ≤ Real.log (2 * x ^ (1 / 5 : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have ha0 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hlhs : Real.log (2 * x ^ (3 / 4 : ℝ)) = Real.log 2 + 3 / 4 * Real.log x := by
    rw [Real.log_mul two_ne_zero ha0.ne', Real.log_rpow hx]
  rw [← Real.log_lt_log_iff (by positivity) hP, hlhs]
  have hprod : 0 ≤ (x ^ (1 / 5 : ℝ) - 1) * (Real.log 2 - 1 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- The algebraic core of clause 7 (with `r = x^{1/20}`). -/
lemma clause7_core {x L D η cG B : ℝ} (hx : 0 < x) (hη : 0 < η) (hη1 : η ≤ 1) (hcG : 0 < cG)
    (hB : 0 < B) (hL : 1 ≤ L) (hD0 : 0 < D) (hD : D ≤ 27 * L ^ 3 * B)
    (hr : 216 * B / cG ≤ x ^ (1 / 20 : ℝ)) :
    8 * x ^ (1 / 5 : ℝ) ≤
      4 * (x ^ (3 / 4 : ℝ) / ((1 + η) * x)) ^ 2 * (cG * (x ^ (3 / 4 : ℝ) * L ^ 4)) / D := by
  have e_a : x ^ (3 / 4 : ℝ) = (x ^ (1 / 20 : ℝ)) ^ (15 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e_u : x ^ (1 / 5 : ℝ) = (x ^ (1 / 20 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e_x : x = (x ^ (1 / 20 : ℝ)) ^ (20 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hr0 : 0 < x ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [e_a, e_u]
  generalize x ^ (1 / 20 : ℝ) = r at e_x hr hr0 ⊢
  subst e_x
  rw [div_le_iff₀ hcG] at hr
  have key : 4 * (r ^ 15 / ((1 + η) * (r ^ 20))) ^ 2 * (cG * (r ^ 15 * L ^ 4)) / D
      = 4 * cG * r ^ 5 * L ^ 4 / ((1 + η) ^ 2 * D) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hη' : 1 + η ≠ 0 := by positivity
    have hD' : D ≠ 0 := hD0.ne'
    field_simp
  rw [key, le_div_iff₀ (by positivity)]
  have h1 : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have h2 : (1 + η) ^ 2 * D ≤ 4 * (27 * L ^ 3 * B) := mul_le_mul h1 hD hD0.le (by norm_num)
  have h3 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
  calc 8 * r ^ 4 * ((1 + η) ^ 2 * D) ≤ 8 * r ^ 4 * (4 * (27 * L ^ 3 * B)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * (216 * B) * r ^ 4 * L ^ 3 := by ring
    _ ≤ 4 * (216 * B) * r ^ 4 * L ^ 4 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 4 * (r * cG) * r ^ 4 * L ^ 4 := by gcongr
    _ = 4 * cG * r ^ 5 * L ^ 4 := by ring

/-- Clause 7: `log (2 P) ≤ log 2 + ψ(M^{1/5}) ≤ 8 M^{1/5}`, while the exponent is
`≥ cG M^{1/4} (log M)^4 / D` with `D ≤ 27 (log M)^3 B`. -/
lemma clause7 {η cG : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hcG : 0 < cG) {B : ℕ} (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) (hL : 4 ≤ Real.log M) (hr : 216 * B / cG ≤ (M : ℝ) ^ (1 / 20 : ℝ))
    (hu1 : 1 ≤ (M : ℝ) ^ (1 / 5 : ℝ)) :
    Real.exp (-(4 * ((M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M)) ^ 2 *
        (cG * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)) /
        (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ))) ≤
      1 / (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) := by
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the size of `Nat.log 2 (2 M)`
  have hk : ((Nat.log 2 (2 * M) : ℕ) : ℝ) ≤ 1 + 2 * Real.log M := by
    have h1 := Real.natLog_le_logb (2 * M) 2
    have h2 : Real.logb ((2 : ℕ) : ℝ) ((2 * M : ℕ) : ℝ) = 1 + Real.log M / Real.log 2 := by
      rw [Real.logb, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hx.ne', add_div,
        div_self hlog2pos.ne']
    have h3 : Real.log M / Real.log 2 ≤ 2 * Real.log M := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [mul_le_mul_of_nonneg_left log_two_ge_half (by linarith : (0 : ℝ) ≤ Real.log M)]
    rw [h2] at h1
    linarith
  have hD0 : (0 : ℝ) < (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ) := by
    have : 0 < (Nat.log 2 (2 * M) + 2) ^ 3 * B := by positivity
    exact_mod_cast this
  have hD : (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ) ≤ 27 * Real.log M ^ 3 * B := by
    push_cast
    have h1 : ((Nat.log 2 (2 * M) : ℕ) : ℝ) + 2 ≤ 3 * Real.log M := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    calc (((Nat.log 2 (2 * M) : ℕ) : ℝ) + 2) ^ 3 * B ≤ (3 * Real.log M) ^ 3 * B :=
          mul_le_mul_of_nonneg_right h2 hB'.le
      _ = 27 * Real.log M ^ 3 * B := by ring
  have hcore := clause7_core hx hη hη1 hcG hB' (by linarith) hD0 hD hr
  -- `log (2 P) ≤ 8 M^{1/5}`
  have hP : (0 : ℝ) < (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have h2P : (0 : ℝ) < 2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by linarith
  have hPlog : Real.log (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) ≤
      8 * (M : ℝ) ^ (1 / 5 : ℝ) := by
    rw [Real.log_mul two_ne_zero hP.ne', ← Chebyshev.psi_eq_log_lcmUpto,
      ← Chebyshev.psi_eq_psi_coe_floor]
    have h1 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx.le (1 / 5 : ℝ))
    have h3 : (Real.log 4 + 4) * (M : ℝ) ^ (1 / 5 : ℝ) ≤ 7 * (M : ℝ) ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [log_four_le_three]) (by positivity)
    linarith [log_two_le_one]
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le h2P ((Real.log_le_iff_le_exp h2P).mp (hPlog.trans hcore))

end AsymAux

open AsymAux

/-- All for `M` large facts used in the proof of Proposition 2. -/
lemma prop2_eventually (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (cG : ℝ) (hcG : 0 < cG) (B : ℕ)
    (hB : 0 < B) : ∀ᶠ M : ℕ in atTop,
    0 < M ∧
    2 * (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4 ∧
    (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) / 2 ∧
    (2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) + 1) * ((⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) + 1)
      / M ≤ (M : ℝ) ^ (-(1 / 21 : ℝ)) / 2 ∧
    (M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M) ≤ 1 / 2 ∧
    2 * (M : ℝ) ^ (3 / 4 : ℝ) < (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) ∧
    Real.exp (-(4 * ((M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M)) ^ 2 *
        (cG * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)) /
        (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ))) ≤
      1 / (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) ∧
    2 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
  filter_upwards [eventually_gt_atTop 0, ev_log_ge 4,
    ev_rpow_ge (s := 1 / 4) (by norm_num) 3,
    ev_rpow_ge (s := 1 / 5) (by norm_num) 12,
    ev_rpow_ge (s := 1 / 420) (by norm_num) 1,
    ev_log_pow_le 4 (s := 1 / 420) (by norm_num) (c := 1 / 12) (by norm_num),
    ev_log_pow_le 1 (s := 1 / 5) (by norm_num) (c := 1 / 4) (by norm_num),
    ev_rpow_ge (s := 1 / 20) (by norm_num) (216 * B / cG)]
    with M hM hL h4 h5 h420 hkey hlog5 h20
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) / 2 := clause3 hx h4
  rw [pow_one] at hlog5
  refine ⟨hM, clause2 hx (by linarith), h3,
    clause4 hx (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) (by linarith) h420 hkey,
    clause5 hx hη h3, clause6 hx h5 hlog5, clause7 hη hη1 hcG hB hM hL h20 (by linarith),
    Nat.le_floor ?_⟩
  exact_mod_cast (show (2 : ℝ) ≤ (M : ℝ) ^ (1 / 5 : ℝ) by linarith)

/-- The residual `x` produced by Proposition 1 is not too small for Proposition 2. -/
lemma main_eventually : ∀ᶠ N : ℕ in atTop,
    1 / (N : ℝ) + (N : ℝ) ^ (-(1 / 21 : ℝ)) ≤ 1 / (20 * Real.log N) := by
  filter_upwards [eventually_ge_atTop 3,
    ev_log_pow_le 1 (s := 1 / 21) (by norm_num) (c := 1 / 40) (by norm_num),
    ev_log_pow_le 1 (s := 1) (by norm_num) (c := 1 / 40) (by norm_num)] with N hN h1 h2
  have hx : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  rw [pow_one] at h1 h2
  rw [Real.rpow_one] at h2
  have hw : 0 < (N : ℝ) ^ (1 / 21 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith)]
  have e1 : 1 / (N : ℝ) ≤ 1 / (40 * Real.log N) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : ((N : ℝ) ^ (1 / 21 : ℝ))⁻¹ ≤ 1 / (40 * Real.log N) := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have e3 : 1 / (40 * Real.log N) + 1 / (40 * Real.log N) = 1 / (20 * Real.log N) := by
    ring
  linarith

end Croot
end

section
/-!
# Croot's Proposition 2: exact representation by smooth numbers in a short interval

For fixed `η ∈ (0, 1]` there is `c > 0` such that for all large `M`, every rational
`x ∈ [M^{-1/21}, c]` whose reduced denominator is `⌊M^{1/5}⌋`-pp-smooth is a sum of
reciprocals of distinct integers in `(M, (1 + η) M]`.

Proof: build `Ỹ = Core ∪ Fill` of `⌊M^{1/5}⌋`-pp-smooth integers in `(M, (1+η)M]` with
`2x ≤ H(Ỹ) < 2x + 1/M`, and show by finite Fourier analysis modulo `P = lcm(1..y)` that some
subset `Z ⊆ Ỹ` has `H(Z) = x`.
-/

namespace Croot

open Real Finset Filter

/-! ## Greedy filling -/

/-- Greedy filling: adding elements `> M` one at a time we can land in `[T, T + 1/M)`. -/
lemma greedy_fill (M : ℕ) (F0 : Finset ℕ) (hF0 : ∀ m ∈ F0, M < m) (b T : ℚ)
    (hb : b ≤ T) (htot : T ≤ b + recipSum F0) :
    ∃ F ⊆ F0, T ≤ b + recipSum F ∧ b + recipSum F < T + 1 / ((M : ℚ) + 1) := by
  induction F0 using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simpa using htot
    · simp only [recipSum_empty, add_zero]
      have : (0 : ℚ) < 1 / ((M : ℚ) + 1) := by positivity
      linarith
  | insert a F0 ha ih =>
    have hF0' : ∀ m ∈ F0, M < m := fun m hm => hF0 m (Finset.mem_insert_of_mem hm)
    have haM : M < a := hF0 a (Finset.mem_insert_self a F0)
    have hins : recipSum (insert a F0) = 1 / (a : ℚ) + recipSum F0 := by
      simp [recipSum, Finset.sum_insert ha]
    by_cases hT : T ≤ b + recipSum F0
    · obtain ⟨F, hF, h1, h2⟩ := ih hF0' hT
      exact ⟨F, hF.trans (Finset.subset_insert _ _), h1, h2⟩
    · push Not at hT
      refine ⟨insert a F0, le_rfl, ?_, ?_⟩
      · rw [hins] at htot ⊢; linarith
      · rw [hins]
        have ha1 : (1 : ℚ) / a ≤ 1 / ((M : ℚ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast haM
        linarith

/-! ## Small auxiliary facts -/

lemma abs_le_of_mem_window {P : ℕ} {h : ℤ} (hh : h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ))
    (-((P / 2 : ℕ) : ℤ) + P)) : |(h : ℝ)| ≤ (P : ℝ) / 2 := by
  rw [Finset.mem_Ico] at hh
  obtain ⟨h1, h2⟩ := hh
  have hP2 : ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self P 2
  have hP2' : (P : ℝ) - ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 + 1 / 2 := by
    have : (P : ℝ) ≤ 2 * ((P / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show P ≤ 2 * (P / 2) + 1 by omega)
    linarith
  have h1' : -((P / 2 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
  have h2' : (h : ℝ) + 1 ≤ -((P / 2 : ℕ) : ℝ) + P := by
    have : h + 1 ≤ -((P / 2 : ℕ) : ℤ) + P := h2
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

lemma zero_mem_window {P : ℕ} (hP : 0 < P) :
    (0 : ℤ) ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P) := by
  rw [Finset.mem_Ico]
  have : P / 2 < P := Nat.div_lt_self hP (by norm_num)
  constructor <;> omega

lemma card_window (P : ℕ) :
    (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card = P := by
  rw [Int.card_Ico]
  simp

/-- A set of integers `> M` has reciprocal sum at most `#S / M`. -/
lemma recipSum_le_card_div {S : Finset ℕ} {M : ℕ} (hM : 0 < M) (h : ∀ m ∈ S, M < m) :
    ((recipSum S : ℚ) : ℝ) ≤ S.card / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [recipSum, Rat.cast_sum]
  calc ∑ n ∈ S, (((1 : ℚ) / n : ℚ) : ℝ) ≤ ∑ _n ∈ S, (1 : ℝ) / M := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : (M : ℝ) ≤ n := by exact_mod_cast (h n hn).le
        push_cast
        exact one_div_le_one_div_of_le hM' hn'
    _ = S.card / M := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- If a finite sum of complex numbers equals `P * c` with `c` a natural number and the sum of
the real parts is positive, then `c > 0`. -/
lemma pos_of_sum_eq_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) (P c : ℕ)
    (h : ∑ i ∈ s, f i = (P : ℂ) * (c : ℂ)) (hpos : 0 < ∑ i ∈ s, (f i).re) : 0 < c := by
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have h3 : ((P : ℂ) * (c : ℂ)).re = (P : ℝ) * c := by simp
  rw [h3] at h2
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, mul_zero] at h2
    linarith
  · exact hc

/-! ## The proposition -/

set_option maxHeartbeats 2000000 in
theorem prop2 (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
    ∀ x : ℚ, (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ x → (x : ℝ) ≤ c →
      PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ x.den →
      ∃ Y ⊆ Ioc M ⌊(1 + η) * M⌋₊, recipSum Y = x := by
  set B : ℕ := ⌈16 / η⌉₊ with hBdef
  have hB : 0 < B := Nat.ceil_pos.2 (by positivity)
  obtain ⟨cG, hcG, hGcard⟩ := card_smoothRough_ge B
  obtain ⟨κ, hκ, hmass⟩ := mass_smooth_ge
  refine ⟨min (κ * η / 2) (1 / 8), lt_min (by positivity) (by norm_num), ?_⟩
  filter_upwards [core_exists η hη hη1, hGcard, hmass η hη hη1,
    prop2_eventually η hη hη1 cG hcG B hB] with M hcore hGM hmassM hev
  obtain ⟨hM0, hX2, hWM, hCAsmall, hδhalf, hPbig, hdecay, hy2⟩ := hev
  intro x hx1 hx2 hxden
  set y : ℕ := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ with hydef
  set W : ℝ := (M : ℝ) ^ (3 / 4 : ℝ) with hWdef
  set X : ℝ := W * (Real.log M) ^ 4 with hXdef
  set P : ℕ := Nat.lcmUpto y with hPdef
  set U : ℕ := ⌊(1 + η) * M⌋₊ with hUdef
  set D : ℕ := (Nat.log 2 (2 * M) + 2) ^ 3 * B with hDdef
  set G : Finset ℕ := (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
    (fun n => PPSmooth y n ∧ ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) with hGdef
  set Pr : Finset ℕ := (Finset.Iic y).filter Nat.Prime with hPrdef
  set Sm : Finset ℕ := (Ioc M U).filter (PPSmooth y) with hSmdef
  -- basic positivity facts
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hW0 : 0 < W := Real.rpow_pos_of_pos hMr _
  have hX0 : 0 < X := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hMr _) hx1
  have hxc : (x : ℝ) ≤ κ * η / 2 := hx2.trans (min_le_left _ _)
  have hx8 : (x : ℝ) ≤ 1 / 8 := hx2.trans (min_le_right _ _)
  have hPpos : 0 < P := Nat.lcmUpto_pos y
  have hPr' : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hD : 0 < D := Nat.mul_pos (by positivity) hB
  have h2M : (1 + η) * (M : ℝ) ≤ 2 * M := by nlinarith
  -- the core elements
  have hcore' : ∀ n p, n ∈ G → p ∈ Pr → ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧
      PPSmooth y m ∧ n ∣ m ∧ p ^ Nat.log p y ∣ m ∧ m / n ∈ cofSet B m := by
    intro n p hn hp
    rw [hGdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [hPrdef, Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨⟨hn1, hn2⟩, hn3, hn4⟩ := hn
    have hXn : X < n := (Nat.floor_lt hX0.le).1 hn1
    have hn2X : (n : ℝ) ≤ 2 * X := (Nat.cast_le.2 hn2).trans (Nat.floor_le (by positivity))
    exact hcore n hXn hn2X hn3 hn4 p hp.2 hp.1
  choose! mf hmf using hcore'
  set CA : Finset ℕ := G.biUnion (fun n => Pr.image (mf n)) with hCAdef
  have hCAmem : ∀ m ∈ CA, ∃ n ∈ G, ∃ p ∈ Pr, mf n p = m := by
    intro m hm
    rw [hCAdef, Finset.mem_biUnion] at hm
    obtain ⟨n, hn, hm⟩ := hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨n, hn, p, hp, rfl⟩
  have hCAprop : ∀ m ∈ CA, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth y m := by
    intro m hm
    obtain ⟨n, hn, p, hp, rfl⟩ := hCAmem m hm
    obtain ⟨h1, h2, h3, -⟩ := hmf n p hn hp
    exact ⟨h1, h2, h3⟩
  have hCASm : CA ⊆ Sm := by
    intro m hm
    obtain ⟨h1, h2, h3⟩ := hCAprop m hm
    rw [hSmdef, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩
  have h2Pr : 2 ∈ Pr := by
    rw [hPrdef, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨hy2, Nat.prime_two⟩
  have hlcm : ∀ n ∈ G, (Pr.image (mf n)).lcm id = P := by
    intro n hn
    rw [hPdef]
    apply lcm_eq_lcmUpto
    · intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
      obtain ⟨h1, -, h3, -⟩ := hmf n p hn hp
      exact ⟨lt_of_le_of_lt (Nat.zero_le _) h1, h3⟩
    · intro p hp hpy
      have hpPr : p ∈ Pr := by
        rw [hPrdef, Finset.mem_filter, Finset.mem_Iic]
        exact ⟨hpy, hp⟩
      exact ⟨mf n p, Finset.mem_image_of_mem _ hpPr, (hmf n p hn hpPr).2.2.2.2.1⟩
  -- the reciprocal mass of the core is small
  have hGle : (G.card : ℝ) ≤ 2 * X := by
    have h1 : G.card ≤ ⌊2 * X⌋₊ :=
      calc G.card ≤ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).card := Finset.card_filter_le _ _
        _ = ⌊2 * X⌋₊ - ⌊X⌋₊ := Nat.card_Ioc _ _
        _ ≤ ⌊2 * X⌋₊ := Nat.sub_le _ _
    calc (G.card : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * X := Nat.floor_le (by positivity)
  have hPrle : (Pr.card : ℝ) ≤ (y : ℝ) + 1 := by
    have : Pr.card ≤ y + 1 :=
      calc Pr.card ≤ (Finset.Iic y).card := Finset.card_filter_le _ _
        _ = y + 1 := Nat.card_Iic y
    exact_mod_cast this
  have hCAcard : (CA.card : ℝ) ≤ (2 * X + 1) * ((y : ℝ) + 1) := by
    have h1 : CA.card ≤ G.card * Pr.card :=
      calc CA.card ≤ ∑ n ∈ G, (Pr.image (mf n)).card := Finset.card_biUnion_le
        _ ≤ ∑ _n ∈ G, Pr.card := Finset.sum_le_sum fun n _ => Finset.card_image_le
        _ = G.card * Pr.card := by rw [Finset.sum_const, smul_eq_mul]
    calc (CA.card : ℝ) ≤ (G.card : ℝ) * Pr.card := by exact_mod_cast h1
      _ ≤ (2 * X + 1) * ((y : ℝ) + 1) :=
        mul_le_mul (by linarith) hPrle (by positivity) (by positivity)
  have hCAmass : ((recipSum CA : ℚ) : ℝ) ≤ (x : ℝ) / 2 := by
    calc ((recipSum CA : ℚ) : ℝ) ≤ CA.card / M :=
          recipSum_le_card_div hM0 (fun m hm => (hCAprop m hm).1)
      _ ≤ (2 * X + 1) * ((y : ℝ) + 1) / M := div_le_div_of_nonneg_right hCAcard hMr.le
      _ ≤ (M : ℝ) ^ (-(1 / 21 : ℝ)) / 2 := hCAsmall
      _ ≤ (x : ℝ) / 2 := by linarith
  -- greedy filling with further smooth numbers
  have hSmM : ∀ m ∈ Sm, M < m ∧ m ≤ U ∧ PPSmooth y m := by
    intro m hm
    rw [hSmdef, Finset.mem_filter, Finset.mem_Ioc] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  have hb : recipSum CA ≤ 2 * x := by
    have : ((recipSum CA : ℚ) : ℝ) ≤ ((2 * x : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have htot : 2 * x ≤ recipSum CA + recipSum (Sm \ CA) := by
    rw [recipSum_sdiff hCASm]
    have : ((2 * x : ℚ) : ℝ) ≤ ((recipSum Sm : ℚ) : ℝ) := by push_cast; linarith
    have : 2 * x ≤ recipSum Sm := by exact_mod_cast this
    linarith
  obtain ⟨F, hFsub, hF1, hF2⟩ := greedy_fill M (Sm \ CA)
    (fun m hm => (hSmM m (Finset.mem_sdiff.1 hm).1).1) (recipSum CA) (2 * x) hb htot
  set Yt : Finset ℕ := CA ∪ F with hYtdef
  have hdisj : Disjoint CA F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    exact (Finset.mem_sdiff.1 (hFsub haF)).2 ha
  have hYtsum : recipSum Yt = recipSum CA + recipSum F := recipSum_union hdisj
  have hYtSm : Yt ⊆ Sm := Finset.union_subset hCASm (hFsub.trans Finset.sdiff_subset)
  have hH1 : 2 * (x : ℝ) ≤ ((recipSum Yt : ℚ) : ℝ) := by
    have : 2 * x ≤ recipSum Yt := by rw [hYtsum]; exact hF1
    exact_mod_cast this
  have hH2 : ((recipSum Yt : ℚ) : ℝ) < 2 * (x : ℝ) + 1 / ((M : ℝ) + 1) := by
    have h' : recipSum Yt < 2 * x + 1 / ((M : ℚ) + 1) := by rw [hYtsum]; exact hF2
    have h'' : ((recipSum Yt : ℚ) : ℝ) < ((2 * x + 1 / ((M : ℚ) + 1) : ℚ) : ℝ) :=
      Rat.cast_lt.2 h'
    push_cast at h''
    exact h''
  have hYtdvd : ∀ m ∈ Yt, 0 < m ∧ m ∣ P := by
    intro m hm
    obtain ⟨h1, -, h3⟩ := hSmM m (hYtSm hm)
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le M) h1
    exact ⟨hm0, h3.dvd_lcmUpto hm0.ne'⟩
  have hxP : ∃ z : ℤ, x * P = z := by
    have hdvd : x.den ∣ P := hxden.dvd_lcmUpto x.den_ne_zero
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨x.num * k, ?_⟩
    rw [hk]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  -- Fourier analysis
  have key := fourier_count Yt P hPpos hYtdvd x hxP (-((P / 2 : ℕ) : ℤ))
  set A : ℝ := 2 ^ Yt.card / (2 * P) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P),
      -A ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
    intro h hh
    have habs : |(h : ℝ)| ≤ (P : ℝ) / 2 := abs_le_of_mem_window hh
    by_cases hsm : |(h : ℝ)| ≤ W
    · -- small frequencies: nonnegative real part
      have hnn := re_term_nonneg Yt x h (fun m hm => by
        have h1 := (hSmM m (hYtSm hm)).1
        have h1' : (M : ℝ) < m := by exact_mod_cast h1
        exact ⟨lt_of_le_of_lt (Nat.zero_le M) h1, by linarith⟩) (by
        rw [abs_mul]
        have h0 : 0 ≤ ((recipSum Yt : ℚ) : ℝ) / 2 - x := by linarith
        rw [abs_of_nonneg h0]
        have h3 : ((recipSum Yt : ℚ) : ℝ) / 2 - x ≤ 1 / (2 * ((M : ℝ) + 1)) := by
          have e : 1 / (2 * ((M : ℝ) + 1)) = (1 / ((M : ℝ) + 1)) / 2 := by field_simp
          rw [e]
          linarith
        calc |(h : ℝ)| * (((recipSum Yt : ℚ) : ℝ) / 2 - x) ≤ W * (1 / (2 * ((M : ℝ) + 1))) :=
              mul_le_mul hsm h3 h0 hW0.le
          _ ≤ 1 / 4 := by
              rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith)
      linarith
    · -- large frequencies: some factor is far from `1`, for many cores
      push Not at hsm
      have hfar : ∀ n ∈ G, ∃ m ∈ Pr.image (mf n), ∀ j : ℤ, W ≤ |(h : ℝ) - j * m| := by
        intro n hn
        have hnX : X < n := by
          have hn' := hn
          rw [hGdef, Finset.mem_filter, Finset.mem_Ioc] at hn'
          exact (Nat.floor_lt hX0.le).1 hn'.1.1
        apply exists_far (Pr.image (mf n)) n W h
        · exact ⟨mf n 2, Finset.mem_image_of_mem _ h2Pr⟩
        · intro m hm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
          exact lt_of_le_of_lt (Nat.zero_le M) (hmf n p hn hp).1
        · intro m hm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
          exact (hmf n p hn hp).2.2.2.1
        · exact hW0.le
        · linarith
        · exact hsm
        · rw [hlcm n hn]
          linarith
      choose! g hg using hfar
      set J : Finset ℕ := G.image g with hJdef
      have hJCA : J ⊆ CA := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_biUnion.2 ⟨n, hn, (hg n hn).1⟩
      have hJsub : J ⊆ Yt := hJCA.trans Finset.subset_union_left
      have hJcard : G.card ≤ D * J.card := by
        apply Finset.card_le_mul_card_image
        intro b hb
        obtain ⟨hbM, hbU, -⟩ := hCAprop b (hJCA hb)
        have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le M) hbM
        have hb2 : b ≤ 2 * M := by
          have : (b : ℝ) ≤ 2 * M := by linarith
          exact_mod_cast this
        refine le_trans (Finset.card_le_card ?_) ((card_fiber_le B b hb0 G).trans ?_)
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          obtain ⟨hnG, hgn⟩ := hn
          obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (hg n hnG).1
          obtain ⟨-, -, -, hdvd, -, hcof⟩ := hmf n p hnG hp
          rw [hpe, hgn] at hdvd hcof
          exact ⟨hnG, hdvd, hcof⟩
        · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
            (Nat.add_le_add_right (Nat.log_mono_right hb2) 2) 3)
      set δ : ℝ := W / ((1 + η) * M) with hδdef
      have hδ0 : 0 ≤ δ := by positivity
      have hnorm := norm_term_le Yt J hJsub x h δ hδ0 hδhalf (by
        intro m hm j
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        have hfarn := (hg n hn).2 j
        obtain ⟨hgM, hgU, -⟩ := hCAprop (g n) (hJCA (Finset.mem_image_of_mem g hn))
        have hgpos : (0 : ℝ) < g n := by
          have : (M : ℝ) < g n := by exact_mod_cast hgM
          linarith
        have hgne : (g n : ℝ) ≠ 0 := hgpos.ne'
        have e : (h : ℝ) / (g n) - j = ((h : ℝ) - j * g n) / g n := by
          rw [sub_div, mul_div_cancel_right₀ _ hgne]
        rw [e, abs_div, abs_of_pos hgpos]
        calc δ = W / ((1 + η) * M) := rfl
          _ ≤ W / g n := div_le_div_of_nonneg_left hW0.le hgpos hgU
          _ ≤ |(h : ℝ) - j * g n| / g n := div_le_div_of_nonneg_right hfarn hgpos.le)
      have hpow : (1 - 4 * δ ^ 2) ^ J.card ≤ 1 / (2 * (P : ℝ)) := by
        have hδ2 : δ * δ ≤ 1 / 2 * (1 / 2) := mul_le_mul hδhalf hδhalf hδ0 (by norm_num)
        have h1 : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
        have h2 : 1 - 4 * δ ^ 2 ≤ Real.exp (-(4 * δ ^ 2)) := by
          have := Real.add_one_le_exp (-(4 * δ ^ 2))
          linarith
        have hJr : cG * X ≤ (D : ℝ) * J.card := by
          have : (G.card : ℝ) ≤ (D : ℝ) * J.card := by exact_mod_cast hJcard
          linarith
        have hDr : (0 : ℝ) < D := by exact_mod_cast hD
        calc (1 - 4 * δ ^ 2) ^ J.card ≤ Real.exp (-(4 * δ ^ 2)) ^ J.card :=
              pow_le_pow_left₀ h1 h2 _
          _ = Real.exp (J.card * (-(4 * δ ^ 2))) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (-(4 * δ ^ 2 * (cG * X) / D)) := by
              apply Real.exp_le_exp.2
              have h3 : cG * X / D ≤ J.card := by
                rw [div_le_iff₀ hDr]
                linarith
              have h4 : 0 ≤ 4 * δ ^ 2 := by positivity
              have h5 := mul_le_mul_of_nonneg_left h3 h4
              have e : 4 * δ ^ 2 * (cG * X) / D = 4 * δ ^ 2 * (cG * X / D) := by ring
              rw [e]
              linarith
          _ ≤ 1 / (2 * P) := hdecay
      have hre := (abs_le.1 (Complex.abs_re_le_norm
        (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))))).1
      have h2pos : (0 : ℝ) ≤ 2 ^ Yt.card := by positivity
      have h6 := mul_le_mul_of_nonneg_left hpow h2pos
      have eA : A = 2 ^ Yt.card * (1 / (2 * (P : ℝ))) := by rw [hAdef]; ring
      linarith
  have hsumpos : 0 < ∑ h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P),
      (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
    rw [← Finset.add_sum_erase _ _ (zero_mem_window hPpos)]
    have h0 : (eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC (((0 : ℤ) : ℝ) / m))).re
        = 2 ^ Yt.card := by
      rw [term_zero]
      rw [show (2 : ℂ) ^ Yt.card = ((2 ^ Yt.card : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    rw [h0]
    have hcard : (((Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card : ℝ)
        ≤ P := by
      have : ((Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card ≤ P := by
        calc _ ≤ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card :=
              Finset.card_erase_le
          _ = P := card_window P
      exact_mod_cast this
    have hlow : -(A * P) ≤ ∑ h ∈ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0,
        (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
      calc -(A * P) ≤ -(A * ((Finset.Ico (-((P / 2 : ℕ) : ℤ))
            (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card) := by
            have := mul_le_mul_of_nonneg_left hcard hA0
            linarith
        _ = ∑ _h ∈ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0, (-A) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ _ := Finset.sum_le_sum fun h hh => hterm h (Finset.mem_of_mem_erase hh)
    have eAP : A * P = 2 ^ Yt.card / 2 := by
      rw [hAdef]
      field_simp
    have : (0 : ℝ) < 2 ^ Yt.card := by positivity
    linarith
  have hc := pos_of_sum_eq_mul _ _ P _ key hsumpos
  obtain ⟨Z, hZ⟩ := Finset.card_pos.1 hc
  classical
  rw [Finset.mem_filter, Finset.mem_powerset] at hZ
  obtain ⟨hZsub, k, hk⟩ := hZ
  have hk0 : k = 0 := by
    have hZnn : 0 ≤ recipSum Z := recipSum_nonneg Z
    have hZle : recipSum Z ≤ recipSum Yt := recipSum_mono hZsub
    have hx8q : x ≤ 1 / 8 := by
      have : ((x : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by push_cast; exact hx8
      exact Rat.cast_le.1 this
    have hxq : 0 < x := by exact_mod_cast hxpos
    have hM1 : (1 : ℚ) / ((M : ℚ) + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (1 : ℚ) ≤ M := by exact_mod_cast hM0
      linarith
    have hYtq : recipSum Yt < 2 * x + 1 / ((M : ℚ) + 1) := by rw [hYtsum]; exact hF2
    have h1 : (k : ℚ) < 1 := by rw [← hk]; linarith
    have h2 : (-1 : ℚ) < k := by rw [← hk]; linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    omega
  refine ⟨Z, fun m hm => ?_, ?_⟩
  · have := hYtSm (hZsub hm)
    rw [hSmdef, Finset.mem_filter] at this
    exact this.1
  · have : recipSum Z - x = 0 := by rw [hk, hk0]; simp
    linarith

end Croot
end

section
/-!
# Croot's theorem on unit fractions with denominators in short intervals

This file assembles the proof of the case `r = 1` of the Main Theorem of

  E. S. Croot III, *On unit fractions with denominators in short intervals*,
  Acta Arith. 99 (2001), 99–114,

and derives the answers to the questions of Erdős and Graham (Old and New Problems and Results
in Combinatorial Number Theory, 1980, p. 33; Erdős problem #286; Justin Sun Prize JSP-000243):

* `Croot.croot_upper`: for every `ε > 0` and all large `N` there are distinct integers in
  `(N, (e + ε) N]` whose reciprocals sum to `1`;
* `Croot.croot_lower`: conversely any such set inside `(N, U]` forces `U ≥ e N`;
* `Croot.tendsto_shortestEnd`: the shortest interval `(N, U]` containing distinct integers
  whose reciprocals sum to one has `U / N → e`;
* `Croot.erdos_graham_q1`, `Croot.liminf_ratio_eq_exp_one` (with `Croot.infinite_admissible_ratio_le`,
  `Croot.finite_admissible_ratio_le`): infinitely many representations `1 = ∑ 1/xᵢ`
  (`2 ≤ x₁ < ⋯ < x_k`) with `x_k / x₁` bounded, and `liminf x_k / x₁ = e`.
-/

namespace Croot

open Real Finset Filter

/-- The denominator of `1 - q` divides that of `q`. -/
lemma den_one_sub_dvd (q : ℚ) : (1 - q).den ∣ q.den := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have key : 1 - q = (((q.den : ℤ) - q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast
    rw [sub_div, div_self hq, Rat.num_div_den]
  have h := Rat.den_dvd ((q.den : ℤ) - q.num) (q.den : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [key]
  exact_mod_cast h

/-- **Croot's theorem** (the case `r = 1` of the Main Theorem of [Croot 2001], with an `o(1)`
error term): for every `ε > 0` and every sufficiently large `N` there is a finite set of
(distinct) integers in `(N, (e + ε) N]` whose reciprocals sum to `1`. -/
theorem croot_upper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    ∃ X ⊆ Ioc N ⌊(Real.exp 1 + ε) * N⌋₊, recipSum X = 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set η : ℝ := min 1 (ε / (2 * Real.exp 1)) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : η * Real.exp 1 ≤ ε / 2 := by
    have h : η ≤ ε / (2 * Real.exp 1) := min_le_right _ _
    calc η * Real.exp 1 ≤ ε / (2 * Real.exp 1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h he.le
      _ = ε / 2 := by field_simp
  obtain ⟨c, hc, hprop2⟩ := prop2 η hη hη1
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hprop2
  filter_upwards [prop1 (c / 2) (by positivity), main_eventually, Filter.eventually_ge_atTop M₀,
    Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop ⌈12 / ε⌉₊]
    with N hP1 hmain hNM₀ hN1 hNε
  obtain ⟨M, hNM, hH1, hH2, hM1, hM2⟩ := exists_harmonic_block hN1
  obtain ⟨D, hDsub, hDmass, hDlow, hDsmooth⟩ := hP1 M hM1 hM2
  have hqeq : recipSum (Ioc N M \ D) = recipSum (Ioc N M) - recipSum D := recipSum_sdiff hDsub
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hMr : (N : ℝ) ≤ M := by exact_mod_cast hNM.le
  -- the residual `x = 1 - H((N, M] \ D)`
  have hx_le : ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) ≤ c := by
    have h1 : 1 - recipSum (Ioc N M \ D) ≤ recipSum D := by rw [hqeq]; linarith
    have h1' : ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) ≤ ((recipSum D : ℚ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hx_ge : (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) := by
    have h1 : recipSum D - 1 / (M : ℚ) ≤ 1 - recipSum (Ioc N M \ D) := by
      rw [hqeq]; linarith
    have h1' : ((recipSum D : ℚ) : ℝ) - 1 / (M : ℝ) ≤ ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h1
      push_cast at this ⊢
      exact this
    have hM1' : 1 / (M : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le (by positivity) hMr
    have hMN : (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 21 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hMr (by norm_num)
    linarith
  have hx_den : PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ (1 - recipSum (Ioc N M \ D)).den := by
    have h1 : PPSmooth ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ (1 - recipSum (Ioc N M \ D)).den :=
      hDsmooth.of_dvd (Rat.den_ne_zero _) (den_one_sub_dvd _)
    apply h1.mono
    apply Nat.floor_le_floor
    calc (N : ℝ) ^ (1 / 12 : ℝ) ≤ (M : ℝ) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hMr (by norm_num)
      _ ≤ (M : ℝ) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  obtain ⟨Y, hYsub, hYsum⟩ := hM₀ M (by omega) _ hx_ge hx_le hx_den
  -- the final interval bound `(1 + η) M ≤ (e + ε) N`
  have h12 : 12 / ε ≤ (N : ℝ) := Nat.ceil_le.1 hNε
  have h6 : 6 ≤ ε / 2 * N := by
    have h := mul_le_mul_of_nonneg_left h12 (by positivity : (0 : ℝ) ≤ ε / 2)
    have e : ε / 2 * (12 / ε) = 6 := by field_simp; ring
    linarith
  have hηN : η * Real.exp 1 * N ≤ ε / 2 * N := mul_le_mul_of_nonneg_right hηe (by positivity)
  have hbound : (1 + η) * (M : ℝ) ≤ (Real.exp 1 + ε) * N := by
    have h1 : (1 + η) * (M : ℝ) ≤ (1 + η) * (Real.exp 1 * N + 3) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    have e : (1 + η) * (Real.exp 1 * N + 3) = Real.exp 1 * N + η * Real.exp 1 * N + 3 + 3 * η := by
      ring
    nlinarith
  have hU : ⌊(1 + η) * (M : ℝ)⌋₊ ≤ ⌊(Real.exp 1 + ε) * N⌋₊ := Nat.floor_le_floor hbound
  have hMU : M ≤ ⌊(Real.exp 1 + ε) * N⌋₊ := by
    apply Nat.le_floor
    have : (M : ℝ) ≤ (1 + η) * M := by nlinarith
    linarith
  refine ⟨(Ioc N M \ D) ∪ Y, ?_, ?_⟩
  · intro m hm
    rcases Finset.mem_union.1 hm with hm | hm
    · have h1 := (Finset.mem_sdiff.1 hm).1
      rw [Finset.mem_Ioc] at h1 ⊢
      exact ⟨h1.1, h1.2.trans hMU⟩
    · have h1 := hYsub hm
      rw [Finset.mem_Ioc] at h1 ⊢
      exact ⟨hNM.trans h1.1, h1.2.trans hU⟩
  · have hdisj : Disjoint (Ioc N M \ D) Y := by
      rw [Finset.disjoint_left]
      intro a ha haY
      have h1 := (Finset.mem_sdiff.1 ha).1
      have h2 := hYsub haY
      rw [Finset.mem_Ioc] at h1 h2
      omega
    rw [recipSum_union hdisj, hYsum]
    ring


end Croot
end


open Finset Filter Real
namespace Dense285

lemma times_inj {a : ℕ} (ha : 0 < a) : Function.Injective (fun m : ℕ => a*m) :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_left ha h

lemma split_mass {t m : ℕ} (ht : 0 < t) (hm : 0 < m) :
    (1 : ℝ) / ((t*(t+1)*m : ℕ) : ℝ) =
    1 / ((t*(2*t+1)*m : ℕ) : ℝ) + 1 / (((t+1)*(2*t+1)*m : ℕ) : ℝ) := by
  push_cast
  field_simp
  <;> ring

/-- Replace a chosen collection of denominators by pairs in two disjoint intervals. -/
lemma replace {t U : ℕ} (ht : 0 < t) (X V : Finset ℕ)
    (hX : ∀ x ∈ X, 0 < x ∧ x ≤ U)
    (hV : ∀ m ∈ V, t*(t+1)*m ∈ X)
    (hR : ∀ m ∈ V, U < t*(2*t+1)*m)
    (hsep : ∀ m ∈ V, ∀ n ∈ V, t*(2*t+1)*m < (t+1)*(2*t+1)*n)
    {Z : ℕ} (hZ : U ≤ Z) (hL : ∀ m ∈ V, (t+1)*(2*t+1)*m ≤ Z) :
    ∃ Y : Finset ℕ, Y.card = X.card + V.card ∧
      (∀ y ∈ Y, 0 < y ∧ y ≤ Z) ∧
      (∑ y ∈ Y, (1:ℝ)/y) = ∑ x ∈ X, (1:ℝ)/x := by
  classical
  let D := V.image (fun m => t*(t+1)*m)
  let R := V.image (fun m => t*(2*t+1)*m)
  let L := V.image (fun m => (t+1)*(2*t+1)*m)
  have hD : D ⊆ X := by simpa [D, image_subset_iff] using hV
  have dR : Disjoint (X \ D) R := by
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hy
    exact (hR m hm).not_ge (hX _ (mem_sdiff.mp hx).1).2
  have dL : Disjoint ((X \ D) ∪ R) L := by
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hy
    rcases mem_union.mp hx with hx | hx
    · exact (lt_trans (hR n hn) (hsep n hn n hn)).not_ge (hX _ (mem_sdiff.mp hx).1).2
    · obtain ⟨m,hm,heq⟩ := mem_image.mp hx
      exact (hsep m hm n hn).ne heq
  have iD := times_inj (a := t*(t+1)) (by positivity)
  have iR := times_inj (a := t*(2*t+1)) (by positivity)
  have iL := times_inj (a := (t+1)*(2*t+1)) (by positivity)
  refine ⟨((X \ D) ∪ R) ∪ L, ?_, ?_, ?_⟩
  · rw [card_union_of_disjoint dL, card_union_of_disjoint dR, card_sdiff_of_subset hD,
        card_image_of_injective _ iD, card_image_of_injective _ iR, card_image_of_injective _ iL]
    have hc := card_le_card hD
    rw [card_image_of_injective _ iD] at hc
    omega
  · intro y hy
    rcases mem_union.mp hy with hy | hy
    · rcases mem_union.mp hy with hy | hy
      · obtain ⟨hp,hu⟩ := hX _ (mem_sdiff.mp hy).1
        exact ⟨hp,hu.trans hZ⟩
      · obtain ⟨m,hm,rfl⟩ := mem_image.mp hy
        exact ⟨Nat.zero_le _ |>.trans_lt (hR m hm), (hsep m hm m hm).le.trans (hL m hm)⟩
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp hy
      exact ⟨(Nat.zero_le _).trans_lt ((hR m hm).trans (hsep m hm m hm)), hL m hm⟩
  · rw [sum_union dL, sum_union dR, ← sum_sdiff hD]
    have eq : (∑ m ∈ V, (1:ℝ) / (t*(2*t+1)*m : ℕ)) +
          (∑ m ∈ V, (1:ℝ) / ((t+1)*(2*t+1)*m : ℕ)) =
          ∑ m ∈ V, (1:ℝ) / (t*(t+1)*m : ℕ) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro m hm
      apply (split_mass ht _).symm
      by_contra! h
      have := hR m hm
      simp [Nat.eq_zero_of_le_zero h] at this
    dsimp only [L,R,D]
    rw [sum_image (fun _ _ _ _ h => iD h), sum_image (fun _ _ _ _ h => iR h),
      sum_image (fun _ _ _ _ h => iL h)]
    linarith

/-- Bad multiplicities inject into the missing denominators. -/
lemma enough {a : ℕ} (ha : 0<a) (W I X : Finset ℕ)
    (hw : ∀ m ∈ W, a*m ∈ I) :
    W.card ≤ (W.filter fun m => a*m ∈ X).card + (I \ X).card := by
  classical
  let G := W.filter fun m => a*m ∈ X
  have sub : ((W \ G).image fun m => a*m) ⊆ I \ X := by
    intro x hx
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hx
    obtain ⟨hm,hg⟩ := mem_sdiff.mp hm
    exact mem_sdiff.mpr ⟨hw m hm, fun hx => hg (mem_filter.mpr ⟨hm,hx⟩)⟩
  have hc := card_le_card sub
  rw [card_image_of_injective _ (times_inj ha), card_sdiff_of_subset (filter_subset _ _)] at hc
  dsimp [G] at *
  omega
end Dense285


open Finset Filter Real
namespace Dense285

lemma adjust {t b n K : ℕ} (ht : 2≤t) (hb : 0<b)
    (hn : 2*n ≤ t*(2*t+1)*(t*b))
    (X : Finset ℕ) (hx : X ⊆ Ioc n (t*(2*t+1)*(t*b)))
    (h1 : (∑ x ∈ X,(1:ℝ)/x)=1)
    (hk : X.card ≤ K)
    (hbudget : K-X.card + (Ioc n (t*(2*t+1)*(t*b)) \ X).card ≤ b) :
    ∃ Y : Finset ℕ, Y.card=K ∧
      (∀ y ∈ Y, 0<y ∧ y≤(t+1)*(2*t+1)*((t+1)*b)) ∧ (∑ y ∈ Y,(1:ℝ)/y)=1 := by
  classical
  have ht0 : 0<t := by omega
  let W := Ioc (t*b) ((t+1)*b)
  have count : W.card=b := by simp [W, Nat.card_Ioc, Nat.add_mul]
  have lo : n ≤ t*(t+1)*(t*b) := by
    have : t*(2*t+1)*(t*b) ≤ 2*(t*(t+1)*(t*b)) := by
      nlinarith only [Nat.zero_le (t*(t*b))]
    omega
  have hi : t*(t+1)*((t+1)*b) ≤ t*(2*t+1)*(t*b) := by
    have hh : (t+1)*(t+1) ≤ (2*t+1)*t := by nlinarith [Nat.mul_le_mul_right t ht]
    calc
      _ = t*((t+1)*(t+1))*b := by ring
      _ ≤ t*((2*t+1)*t)*b := by gcongr
      _ = _ := by ring
  have hw : ∀ m ∈ W, t*(t+1)*m ∈ Ioc n (t*(2*t+1)*(t*b)) := by
    intro m hm
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hm
    exact mem_Ioc.mpr ⟨lo.trans_lt (Nat.mul_lt_mul_of_pos_left hl (by positivity)),
      (Nat.mul_le_mul_left _ hu).trans hi⟩
  have good := enough (a:=t*(t+1)) (by positivity) W _ X hw
  rw [count] at good
  obtain ⟨V,hV,card⟩ := exists_subset_card_eq (s := W.filter (fun m => t*(t+1)*m ∈ X))
    (show K-X.card ≤ _ by omega)
  have data := fun {m} (hm : m ∈ V) => mem_filter.mp (hV hm)
  have sep : ∀ m ∈ V, ∀ m' ∈ V, t*(2*t+1)*m < (t+1)*(2*t+1)*m' := by
    intro m hm m' hm'
    calc
      _ ≤ t*(2*t+1)*((t+1)*b) := Nat.mul_le_mul_left _ (mem_Ioc.mp (data hm).1).2
      _ = (t+1)*(2*t+1)*(t*b) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left (mem_Ioc.mp (data hm').1).1 (by positivity)
  obtain ⟨Y,hy,hy',hsum⟩ := replace (show 0<t by omega) X V (U:=t*(2*t+1)*(t*b))
    (fun x hx' => ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp (hx hx')).1,(mem_Ioc.mp (hx hx')).2⟩)
    (fun _ hm => (data hm).2)
    (fun m hm => Nat.mul_lt_mul_of_pos_left (mem_Ioc.mp (data hm).1).1 (by positivity))
    sep (Z:=(t+1)*(2*t+1)*((t+1)*b)) (by gcongr <;> omega)
    (fun m hm => Nat.mul_le_mul_left _ (mem_Ioc.mp (data hm).1).2)
  exact ⟨Y,by omega,hy',hsum.trans h1⟩

end Dense285

open Finset Filter Real
namespace Dense285

lemma missing {N U : ℕ} (hN : 0 < N) (hU : N ≤ U) (X : Finset ℕ) (hX : X ⊆ Ioc N U)
    (h1 : (∑ x ∈ X, (1:ℝ)/x) = 1)
    (harm : (∑ x ∈ Ioc N U, (1:ℝ)/x) ≤ log ((U:ℝ)/N)) :
    (((Ioc N U \ X).card:ℕ):ℝ) ≤ ((U:ℝ)/N)*((U:ℝ)/exp 1-N) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hu : (0:ℝ)<U := by exact_mod_cast (hN.trans_le hU)
  have hh := Real.log_le_sub_one_of_pos (x := ((U:ℝ)/N)/exp 1) (by positivity)
  rw [Real.log_div (by positivity) (exp_pos _).ne', Real.log_exp] at hh
  have hm : (((Ioc N U \ X).card:ℕ):ℝ) / U ≤ ∑ x ∈ Ioc N U \ X, (1:ℝ)/x := by
    calc
      _ = ∑ x ∈ Ioc N U \ X, (1:ℝ)/U := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        obtain ⟨hp,hle⟩ := mem_Ioc.mp (mem_sdiff.mp hx).1
        apply one_div_le_one_div_of_le (by exact_mod_cast hN.trans hp)
        exact_mod_cast hle
  have hadd := sum_sdiff hX (f := fun x : ℕ => (1:ℝ)/x)
  rw [h1] at hadd
  have hbound : (((Ioc N U \ X).card:ℕ):ℝ) / U ≤ ((U:ℝ)/N)/exp 1 - 1 := by linarith
  have hbound' := (div_le_iff₀ hu).mp hbound
  calc
    _ ≤ _ := hbound'
    _ = _ := by field_simp <;> ring

/-- Croot's interval contains all but a small fraction of one block of multiplicities. -/
lemma blocks (short : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
    ∃ X ⊆ Ioc n ⌊(exp 1+ε)*n⌋₊, (∑ x ∈ X, (1:ℝ)/x)=1)
    (harm : ∀ {n u : ℕ}, 0<n → n≤u → (∑ x ∈ Ioc n u, (1:ℝ)/x) ≤ log ((u:ℝ)/n))
    {C : ℕ} (hc : 3 ≤ C) :
    let q : ℝ := C/exp 1 - 1/100
    ∀ᶠ b : ℕ in atTop, let n := ⌊q*b⌋₊
      ∃ X ⊆ Ioc n (C*b), (∑ x ∈ X, (1:ℝ)/x)=1 ∧
        (((Ioc n (C*b) \ X).card:ℕ):ℝ) ≤ (b:ℝ)/8 := by
  dsimp only
  let q : ℝ := C/exp 1 - 1/100
  have hc' : (3:ℝ) ≤ C := by exact_mod_cast hc
  have he := Real.exp_one_gt_two
  have he' := Real.exp_one_lt_three
  have hep := exp_pos (1:ℝ)
  have hq4 : (C:ℝ)/4 < q := by
    dsimp [q]
    have h3 : (C:ℝ)/3 < (C:ℝ)/exp 1 := by
      apply div_lt_div_of_pos_left (by positivity) hep he'
    linarith
  have hq : 0<q := by linarith
  let ε := (C:ℝ)/q-exp 1
  have heq : q * exp 1 = C - exp 1/100 := by dsimp [q]; field_simp <;> ring
  have hε : 0<ε := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hq).mpr
    linarith [mul_comm q (exp 1)]
  have ht : Tendsto (fun b : ℕ => ⌊q*b⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop hq)
  have hlarge : ∀ᶠ b : ℕ in atTop, (1:ℝ)/(q-C/4) ≤ b := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [ht.eventually (short ε hε), ht.eventually_ge_atTop 1, hlarge, eventually_ge_atTop 100] with b hb hn hb' hb100
  let n := ⌊q*b⌋₊
  change 1 ≤ n at hn
  have hbl : (100:ℝ)≤b := by exact_mod_cast hb100
  have hn₁ : (n:ℝ) ≤ q*b := Nat.floor_le (by positivity)
  have hn₂ : q*b < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have h4 : (C:ℝ)*b ≤ 4*n := by
    have := (div_le_iff₀ (sub_pos.mpr hq4)).mp hb'
    nlinarith
  have hnu : n ≤ C*b := by
    have hqC : q ≤ C := by
      dsimp [q]
      have hh : (C:ℝ)/exp 1 ≤ C := (div_le_iff₀ hep).mpr (by nlinarith)
      linarith
    exact_mod_cast hn₁.trans (mul_le_mul_of_nonneg_right hqC (Nat.cast_nonneg b))
  obtain ⟨X,hX,h1⟩ := hb
  have hub : ⌊(exp 1+ε)*n⌋₊ ≤ C*b := by
    apply Nat.floor_le_of_le
    push_cast
    calc
      _ ≤ (exp 1+ε)*(q*b) := mul_le_mul_of_nonneg_left hn₁ (by positivity)
      _ = _ := by dsimp [ε]; field_simp; ring
  have hX' : X ⊆ Ioc n (C*b) := fun x hx => mem_Ioc.mpr
    ⟨(mem_Ioc.mp (hX hx)).1, (mem_Ioc.mp (hX hx)).2.trans hub⟩
  refine ⟨X,hX',h1,?_⟩
  have hm := missing hn hnu X hX' h1 (harm hn hnu)
  push_cast at hm
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  have hrat : (C:ℝ)*b/n ≤ 4 := (div_le_iff₀ hnpos).mpr (by linarith)
  have hgap : (C:ℝ)*b/exp 1-n ≤ (b:ℝ)/100+1 := by
    dsimp [q] at hn₂
    linarith only [hn₂, show (C:ℝ)*b/exp 1 - b/100 = ((C:ℝ)/exp 1-1/100)*b by ring]
  calc
    _ ≤ _ := hm
    _ ≤ 4*((b:ℝ)/100+1) := mul_le_mul hrat hgap (by
      have h := hn₁
      dsimp [q] at h
      linarith only [h, Nat.cast_nonneg (α:=ℝ) b, show (C:ℝ)*b/exp 1 - b/100 = ((C:ℝ)/exp 1-1/100)*b by ring]) (by norm_num)
    _ ≤ _ := by linarith
end Dense285

open Finset Filter Real
namespace Dense285
lemma upper (short : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
    ∃ X ⊆ Ioc n ⌊(exp 1+ε)*n⌋₊, (∑ x ∈ X, (1:ℝ)/x)=1)
    (harm : ∀ {n u : ℕ}, 0<n → n≤u → (∑ x ∈ Ioc n u, (1:ℝ)/x) ≤ log ((u:ℝ)/n))
    {t : ℕ} (ht : 2 ≤ t) :
    ∀ᶠ K : ℕ in atTop, ∃ Y : Finset ℕ, Y.card = K ∧
      (∀ y ∈ Y, 0<y ∧ (y:ℝ) ≤ (1+1/(t:ℝ))^2*(exp 1/(exp 1-1))*K) ∧
      (∑ y ∈ Y, (1:ℝ)/y)=1 := by
  classical
  let C := t*(2*t+1)*t
  have ht0 : 0<t := by omega
  have hc : 3≤C := by dsimp [C]; nlinarith [Nat.mul_le_mul_right (2*t+1) ht, Nat.mul_le_mul_left (t*(2*t+1)) ht]
  let q : ℝ := C/exp 1 - 1/100
  let P : ℝ := C-q+1/4
  have he := exp_one_gt_two
  have hep := exp_pos (1:ℝ)
  have hc' : (3:ℝ)≤C := by exact_mod_cast hc
  have hq : 0<q := by
    dsimp [q]
    have : 1/100 < (C:ℝ)/exp 1 := (lt_div_iff₀ hep).mpr (by linarith [exp_one_lt_three])
    linarith
  have hq2 : 2*q ≤ C := by
    dsimp [q]
    have hh : (C:ℝ)/exp 1 ≤ C/2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) he.le
    linarith
  have hp : 0<P := by dsimp [P]; linarith
  let B (K : ℕ) := ⌊(1/P)*(K:ℝ)⌋₊
  have htB : Tendsto B atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by positivity : 0<1/P))
  have hbig : ∀ᶠ b : ℕ in atTop, 4*P+8 ≤ (b:ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [htB.eventually (blocks short harm hc), htB.eventually hbig, htB.eventually_ge_atTop 1] with K hblk hbig hB
  let b := B K
  let n := ⌊q*b⌋₊
  change 4*P+8 ≤ (b:ℝ) at hbig
  change 0<b at hB
  obtain ⟨X,hX,h1,hmiss⟩ := hblk
  change X ⊆ Ioc n (C*b) at hX
  change (((Ioc n (C*b) \ X).card:ℕ):ℝ) ≤ (b:ℝ)/8 at hmiss
  have hnlo : (n:ℝ) ≤ q*b := Nat.floor_le (by positivity)
  have hnhi : q*b < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hblo : (b:ℝ) ≤ (1/P)*K := Nat.floor_le (by positivity)
  have hbhi : (1/P)*K < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hklo : P*b ≤ K := by
    have := mul_le_mul_of_nonneg_left hblo hp.le
    simpa [← mul_assoc, hp.ne'] using this
  have hkhi : (K:ℝ) < P*((b:ℝ)+1) := by
    have := mul_lt_mul_of_pos_left hbhi hp
    simpa [← mul_assoc, hp.ne'] using this
  have hn2 : 2*n ≤ C*b := by
    have hh := mul_le_mul_of_nonneg_right hq2 (Nat.cast_nonneg b)
    exact_mod_cast (show 2*(n:ℝ) ≤ C*b by linarith only [hh,hnlo, show (2*q)*(b:ℝ)=2*(q*b) by ring])
  have hnu : n ≤ C*b := by omega
  have hcI : (Ioc n (C*b)).card = C*b-n := Nat.card_Ioc _ _
  have hmx : X.card+(Ioc n (C*b) \ X).card=C*b-n := by
    rw [card_sdiff_of_subset hX, ← hcI]; have := card_le_card hX; omega
  have hcX : (X.card:ℝ)+((Ioc n (C*b) \ X).card:ℝ)=(C:ℝ)*b-n := by
    apply eq_sub_of_add_eq
    exact_mod_cast (show X.card+(Ioc n (C*b) \ X).card + n = C*b by omega)
  have hkx : X.card ≤ K := by
    dsimp [P] at hklo
    have hh := Nat.cast_nonneg (α:=ℝ) (Ioc n (C*b) \ X).card
    exact_mod_cast (show (X.card:ℝ) ≤ K by nlinarith only [hklo,hnhi,hcX,hh,hbig,hp])
  have hbud : K-X.card+(Ioc n (C*b) \ X).card ≤ b := by
    rw [← Nat.cast_le (α:=ℝ), Nat.cast_add, Nat.cast_sub hkx]
    dsimp [P] at hkhi
    nlinarith only [hkhi,hnlo,hcX,hmiss,hbig,show P=(C:ℝ)-q+1/4 by rfl]
  have hC : C*b=t*(2*t+1)*(t*b) := by dsimp [C]; ring
  rw [hC] at hn2 hX hbud
  obtain ⟨Y,hy,hy',hs⟩ := adjust ht hB hn2 X hX h1 hkx hbud
  refine ⟨Y,hy,?_,hs⟩
  intro y hY
  obtain ⟨hpos,hmax⟩ := hy' y hY
  refine ⟨hpos,?_⟩
  have ht' : (0:ℝ)<t := by exact_mod_cast ht0
  have he' : 0<exp 1-1 := by linarith
  have hratio : ((C:ℝ)*b) ≤ (exp 1/(exp 1-1))*K := by
    have hh : ((C:ℝ)-C/exp 1)*b ≤ K := by
      dsimp [P,q] at hklo
      nlinarith only [hklo,Nat.cast_nonneg (α:=ℝ) b]
    have := mul_le_mul_of_nonneg_right hh hep.le
    rw [div_mul_eq_mul_div, le_div_iff₀ he']
    convert this using 1 <;> field_simp <;> ring
  have hz : (((t+1)*(2*t+1)*((t+1)*b):ℕ):ℝ)=(1+1/(t:ℝ))^2*((C:ℝ)*b) := by
    dsimp [C]; push_cast; field_simp <;> ring
  calc
    _ ≤ _ := (Nat.cast_le (α:=ℝ)).mpr hmax
    _ = _ := hz
    _ ≤ _ := by rw [mul_assoc]; gcongr
end Dense285

open Filter Finset Real
open scoped Topology
/-- A strictly increasing sequence of naturals indexed by `Fin (k + 1)` gains at least one per
step. -/
lemma OMA.strictMono_gap {k : ℕ} (n : Fin (k + 1) → ℕ) (hn : StrictMono n) :
    ∀ d : ℕ, ∀ i j : Fin (k + 1), i.val + d = j.val → n i + d ≤ n j := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by omega)
    rw [this]
    omega
  | succ d ih =>
    intro i j hij
    have hlt : i.val + 1 < k + 1 := by have := j.isLt; omega
    have h1 : n i < n ⟨i.val + 1, hlt⟩ := hn (by rw [Fin.lt_def]; simp)
    have h2 := ih ⟨i.val + 1, hlt⟩ j (by simp; omega)
    omega

/-- `1 / x` dominates the increment of the logarithm. -/
lemma OMA.log_step (x : ℝ) (hx : 0 < x) : Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h1 : Real.log ((x + 1) / x) ≤ (x + 1) / x - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hx)] at h1
  have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- The key inequality. If `1` is a sum of `k + 1` distinct unit fractions with largest
denominator `N`, then the denominators are at most `N - k, …, N`, so the sum is at least
`log ((N + 1) / (N - k))`, whence `N + 1 ≤ e * (N - k)`. -/
lemma OMA.key {k : ℕ} (n : Fin (k + 1) → ℕ) (hn : StrictMono n) (h0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    Real.exp 1 * ((k : ℝ) + 1) - (Real.exp 1 - 1) ≤ (Real.exp 1 - 1) * (n (Fin.last k) : ℝ) := by
  have hpos : ∀ i, 1 ≤ n i := by
    intro i
    by_contra hcon
    exact h0 ⟨i, by omega⟩
  have hgap : ∀ i : Fin (k + 1), n i + (k - i.val) ≤ n (Fin.last k) := by
    intro i
    exact OMA.strictMono_gap n hn (k - i.val) i (Fin.last k) (by have := i.isLt; simp; omega)
  have hNk : k + 1 ≤ n (Fin.last k) := by
    have h1 := hgap 0
    have h2 := hpos 0
    simp at h1
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = n (Fin.last k) - k := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hterm : ∀ i : Fin (k + 1),
      Real.log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ) + ((i.val : ℕ) : ℝ)) ≤
        (1 : ℝ) / n i := by
    intro i
    have hle : n i ≤ m + i.val := by have := hgap i; have := i.isLt; omega
    have hle' : (n i : ℝ) ≤ (m : ℝ) + (i.val : ℝ) := by exact_mod_cast hle
    have hni : (0 : ℝ) < n i := by exact_mod_cast hpos i
    have hx : (0 : ℝ) < (m : ℝ) + (i.val : ℝ) := by linarith
    have h1 := OMA.log_step ((m : ℝ) + (i.val : ℝ)) hx
    have h2 : (1 : ℝ) / ((m : ℝ) + (i.val : ℝ)) ≤ 1 / n i :=
      one_div_le_one_div_of_le hni hle'
    have h3 : (m : ℝ) + ((i.val + 1 : ℕ) : ℝ) = (m : ℝ) + (i.val : ℝ) + 1 := by
      push_cast; ring
    rw [h3]
    linarith
  have hsumle : ∑ i : Fin (k + 1),
      (Real.log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ) + ((i.val : ℕ) : ℝ))) ≤
        ∑ i : Fin (k + 1), (1 : ℝ) / n i :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have htel : ∑ i : Fin (k + 1),
      (Real.log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ) + ((i.val : ℕ) : ℝ))) =
        Real.log ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ) + ((0 : ℕ) : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => Real.log ((m : ℝ) + ((i + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ) + ((i : ℕ) : ℝ)))
      (k + 1)]
    exact Finset.sum_range_sub (fun i : ℕ => Real.log ((m : ℝ) + ((i : ℕ) : ℝ))) (k + 1)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlog : Real.log ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) ≤ 1 + Real.log (m : ℝ) := by
    have e0 : (m : ℝ) + ((0 : ℕ) : ℝ) = m := by simp
    rw [htel, e0] at hsumle
    linarith
  have hexp : (m : ℝ) + ((k + 1 : ℕ) : ℝ) ≤ Real.exp 1 * m := by
    have hpos' : (0 : ℝ) < (m : ℝ) + ((k + 1 : ℕ) : ℝ) := by positivity
    calc (m : ℝ) + ((k + 1 : ℕ) : ℝ) = Real.exp (Real.log ((m : ℝ) + ((k + 1 : ℕ) : ℝ))) :=
          (Real.exp_log hpos').symm
      _ ≤ Real.exp (1 + Real.log (m : ℝ)) := Real.exp_le_exp.2 hlog
      _ = Real.exp 1 * m := by rw [Real.exp_add, Real.exp_log hmpos]
  have hmN : (m : ℝ) = (n (Fin.last k) : ℝ) - (k : ℝ) := by
    rw [hm, Nat.cast_sub (by omega)]
  rw [hmN] at hexp
  push_cast at hexp
  nlinarith [hexp]


namespace Dense285
lemma finish (upper : ∀ {t : ℕ}, 2 ≤ t →
    ∀ᶠ K : ℕ in atTop, ∃ Y : Finset ℕ, Y.card = K ∧
      (∀ y ∈ Y, 0<y ∧ (y:ℝ) ≤ (1+1/(t:ℝ))^2*(exp 1/(exp 1-1))*K) ∧
      (∑ y ∈ Y, (1:ℝ)/y)=1) : type_of% @Erdos285.erdos_285 := by
  classical
  intro f S hS h
  let a := exp 1/(exp 1-1)
  have he := exp_one_gt_two
  have he' : 0<exp 1-1 := by linarith
  have ha : 0<a := by dsimp [a]; positivity
  let o (k : ℕ) : ℝ := if k ∈ S then f k/(a*((k:ℝ)+1))-1 else 0
  refine ⟨o,?_,?_⟩
  · change o =o[atTop] (fun _ : ℕ => (1:ℝ))
    rw [Asymptotics.isLittleO_one_iff, Metric.tendsto_nhds]
    intro ε hε
    have ht : Tendsto (fun t : ℕ => (1+1/(t:ℝ))^2) atTop (𝓝 1) := by
      simpa only [add_zero, one_pow] using
        ((tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))).pow 2
    obtain ⟨t,ht2,htε⟩ := ((eventually_ge_atTop 2).and
      (ht.eventually_lt_const (show 1<1+ε by linarith))).exists
    have hub := (tendsto_add_atTop_nat 1).eventually (upper ht2)
    have grow : Tendsto (fun k : ℕ => a*((k:ℝ)+1)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))).const_mul_atTop ha
    filter_upwards [hub,grow.eventually_gt_atTop (1/ε)] with k hkU hkLarge
    rw [Real.dist_eq, sub_zero]
    by_cases hk : k ∈ S
    · obtain ⟨Y,hY,hmax,hs⟩ := hkU
      let n := Y.orderEmbOfFin hY
      have h0 : 0 ∉ Set.range n := by
        rintro ⟨i,hi⟩
        exact (hmax _ (Y.orderEmbOfFin_mem hY i)).1.ne' hi
      have hsum : 1=∑ i, (1:ℝ)/(n i) := by
        calc
          _ = ∑ x ∈ Y, (1:ℝ)/x := hs.symm
          _ = _ := by
            conv_lhs => rw [← Y.image_orderEmbOfFin_univ hY]
            rw [sum_image (fun _ _ _ _ heq => n.injective heq)]
      have hf := (h k hk).2 (show n (Fin.last k) ∈ _ from ⟨n,n.strictMono,h0,hsum,rfl⟩)
      have hmax' := (hmax _ (Y.orderEmbOfFin_mem hY (Fin.last k))).2
      have hu : (f k:ℝ) ≤ (1+1/(t:ℝ))^2*(a*((k:ℝ)+1)) := by
        push_cast at hmax'
        rw [← mul_assoc]
        exact (Nat.cast_le.mpr hf).trans hmax'
      obtain ⟨m,hm,hm0,hms,hmf⟩ := (h k hk).1
      have hl := OMA.key m hm hm0 hms
      rw [hmf] at hl
      have hl' : a*((k:ℝ)+1)-1 ≤ f k := by
        dsimp [a]
        rw [div_mul_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ he']
        linarith
      have hp : 0<a*((k:ℝ)+1) := by positivity
      have hsmall := (div_lt_iff₀ hε).mp hkLarge
      simp only [o, if_pos hk, abs_lt]
      constructor
      · rw [lt_sub_iff_add_lt, lt_div_iff₀ hp]
        nlinarith only [hl',hsmall]
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]
        linarith only [hu, mul_lt_mul_of_pos_right htε hp]
    · simpa [o,hk] using hε
  · intro k hk
    simp only [o, if_pos hk]
    change (f k:ℝ) = (1+((f k:ℝ)/(a*((k:ℝ)+1))-1))*exp 1/(exp 1-1)*((k:ℝ)+1)
    dsimp [a]; field_simp <;> ring
end Dense285

theorem OMA.solution : type_of% @Erdos285.erdos_285 := by
  apply Dense285.finish
  apply Dense285.upper
  · intro ε hε
    filter_upwards [Croot.croot_upper ε hε] with n hn
    obtain ⟨X,hX,h1⟩ := hn
    refine ⟨X,hX,?_⟩
    have hh := congrArg (fun q : ℚ => (q:ℝ)) h1
    simpa [Croot.recipSum] using hh
  · intro n u hn hu
    have hh := Croot.recipSum_Ioc_le_log hn hu
    simpa [Croot.recipSum] using hh
