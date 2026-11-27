import FormalConjectures.ErdosProblems.«50»
import Mathlib

/-!
Adapted for the pinned Lean and Mathlib versions from the Apache-2.0 project
https://github.com/ChironTheCentaur/rh-lab-erdos50/tree/5f908e5325b283e6449a224a197a42a35c9458fb
Copyright 2026 Sky (ChironTheCentaur). Mathematical result due to Paul Erdős.
The bundled Zeta23 development is Copyright 2026 Anthropic, PBC, Apache-2.0.
Its Euler–Maclaurin and Mertens modules derive from PrimeNumberTheoremAnd
and Mathlib under Apache-2.0 with original notices below.
License: https://www.apache.org/licenses/LICENSE-2.0
-/
-- Zeta23.FromPNTPlus.EulerMaclaurin
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


/- We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/


open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2


lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp)
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

-- Zeta23.FromPNTPlus.Mertens
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mertens.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Original authors per that project's blueprint (Euler–Maclaurin and Mertens
sections drawn from Leo Goldmakher, "A quick proof of Mertens' theorem",
https://web.williams.edu/Mathematics/lg5/mertens.pdf).

Declarations ported (source lines 1–371):
  Mertens.sum_Ioc_one_eq_sum_Ioc_zero, Mertens.sum_log_eq, Mertens.sum_log_le,
  Mertens.integral_log_le, Mertens.sum_log_ge, Mertens.sum_log_eq_log_factorial,
  Mertens.sum_log_eq_sum_mangoldt, Mertens.E₁Λ, Mertens.sum_mangoldt_div_eq,
  Mertens.E₁Λ.ge, Mertens.E₁Λ.le, Mertens.sum_mangoldt_div_eq_log,
  Mertens.E₁Λ.bounded'.

Local modifications:
  * the source's `section EulerMaclaurin` (B1 ... sum_eq_integral_add_integral_deriv)
    now lives in Zeta23/FromPNTPlus/EulerMaclaurin.lean (re-ported from upstream
    v4.32.2, where that section was split out of Mertens.lean into its own file),
    imported here;
  * dropped `import Architect` and all `@[blueprint ...]` attributes and
    `blueprint_comment` blocks (blueprint tooling we do not vendor); statement
    text retained as plain docstrings on the main theorems;
  * dropped three root-level helpers unused by the ported region (each is
    referenced only past our truncation point): Filter.EventuallyEq.iff_eventually,
    Real.inv_log_eq_o_one, Real.one_eq_o_log_log — nothing is injected into the
    Real or Filter namespaces by this file;
  * dropped a stray `#check ArithmeticFunction.vonMangoldt_sum`;
  * truncated after E₁Λ.bounded' (everything later — the sorry'd E₁Λ.bounded,
    the prime-form/second/third theorems — is not ported; no sorry enters);
  * added the closing `end Mertens`.
Modified 2026 by Anthropic PBC.
-/




namespace Mertens


open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

/-- For any `x ≥ 1`, `∑ n ≤ x, log n = x log x - ({x} - 1/2) log x - x + 1 + ∫ t in 1..x, ({t} - 1/2)/t`. -/
theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)

/-- For any `x ≥ 1`, `∑ n ≤ x, log n ≤ x log x`. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

/-- For any `x ≥ 1`, `∑ n ≤ x, log n ≥ x log x - 2x`. -/
theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

/-- For any `x`, `∑ n ≤ x, log n = log ⌊x⌋!`. -/
theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind


/-- For any `x`, `∑ n ≤ x, log n = ∑ d ≤ x, Λ(d) ⌊x/d⌋`. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

/-- The remainder term in Mertens' first theorem (von Mangoldt form): `E₁Λ x = ∑ d ≤ x, Λ(d)/d - log x`. -/
noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

/-- For any `x ≥ 1`, `E₁Λ x ≥ -2`. -/
theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by positivity)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring


/-- For any `x ≥ 1`, `E₁Λ x ≤ log 4 + 4`. -/
theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

/-- Mertens' first theorem (von Mangoldt form): for `x ≥ 1`, `|∑ d ≤ x, Λ(d)/d - log x| ≤ log 4 + 4`. -/
theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

end Mertens
end

-- Zeta23.Defs
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/

open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/- ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/

/-- Paper Fourier transform / h_f :  paperFT f z = ∫ u, f u * exp (I * z * u)  for complex z
([Notation]; [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u)e^{izu} du"). -/
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))

/- ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-- l := log(T/2π)  [Notation]. -/
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

/-- ℓ₁ := l + 2 log 2 − 1, "so that N(T,2T) = Tℓ₁/2π + O(l)"  [Notation]. -/
def ell1 (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1

/-- H(λ) := 2 − 1/λ − λ/3  [eq:Fdef]; H(1) = 2/3. -/
def Hfun (x : ℝ) : ℝ := 2 - 1 / x - x / 3

/-- F(λ) := λ / (1 + λ²/3)  [eq:Fdef]; F(1) = 3/4. -/
def Ffun (x : ℝ) : ℝ := x / (1 + x ^ 2 / 3)

/-- D₀ := T^{1/2}  [eq:D0]. -/
def D0 (T : ℝ) : ℝ := Real.sqrt T

/-- I := [T, 2T]  [Notation]. -/
def Iwin (T : ℝ) : Set ℝ := Icc T (2 * T)

/-- I' := (T − D₀, 2T + D₀]  [eq:D0]. -/
def Iprime (T : ℝ) : Set ℝ := Ioc (T - D0 T) (2 * T + D0 T)

lemma Hfun_one : Hfun 1 = 2 / 3 := by norm_num [Hfun]
lemma Ffun_one : Ffun 1 = 3 / 4 := by norm_num [Ffun]

/- ## 2. The densities μ, Π_X, P_X, ν_X  [eq:mudef]–[eq:nudef]

Paper, verbatim: "Define, for τ ∈ ℝ and X = e^L > 1, s := 1/2 + iτ,
  μ(τ)   := (1/2π) Re Γ'/Γ(1/4 + iτ/2) − (log π)/(2π),                      [eq:mudef]
  Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π) Re (X^s − 1)/s,                           [eq:Pidef]
  P_X(τ) := −(1/π) Σ_{n≤X} Λ(n)/√n · cos(τ log n),                           [eq:Pdef]
  ν_X    := μ + Π_X + P_X."                                                   [eq:nudef]
-/

/-- μ(τ) := (1/2π)·Re (Γ'/Γ)(1/4 + iτ/2) − log π /(2π)   [eq:mudef].
Complex.digamma = logDeriv Gamma = Γ'/Γ (Mathlib Gamma/Digamma.lean). -/
def mu (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)

/-- Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π)·Re((X^s − 1)/s),  s = 1/2 + iτ  [eq:Pidef]
("the terms h_k(±i/2) coming from the pole of ζ … rewritten as the density Π_X"). -/
def PiX (X : ℝ) (τ : ℝ) : ℝ :=
  let s : ℂ := 1 / 2 + Complex.I * τ
  1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re

/-- P_X(τ) := −(1/π) Σ_{n ≤ X} Λ(n) n^{−1/2} cos(τ log n)  [eq:Pdef]. Sum over n ∈ Finset.Ioc 0 ⌊X⌋₊
(same indexing as Mathlib's Chebyshev.psi; Λ vanishes off prime powers; the n = 1 term is 0). -/
def PX (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n) / Real.sqrt n * Real.cos (τ * Real.log n)

/-- ν_X := μ + Π_X + P_X  [eq:nudef]. -/
def nuX (X : ℝ) (τ : ℝ) : ℝ := mu τ + PiX X τ + PX X τ

/- ## 3. Abstract zero configurations  [Results], [subsec:weil], §4 closing paragraph -/

/-- γ_ρ := (ρ − 1/2)/i = γ − i(β − 1/2), "so that ρ = 1/2 + iγ_ρ, |Im γ_ρ| < 1/2, and γ_ρ ∈ ℝ iff
β = 1/2"  [Notation]. -/
def gammaOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

/-- The reflection ρ ↦ 1 − ρ̄ (same ordinate γ, mirrored β)  [subsec:weil]. -/
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- An abstract zero configuration: a set (carrier) of DISTINCT points ρ = β+iγ in the closed
strip 0 ≤ β ≤ 1 (the instances built from the zeros of ζ and of L(s,χ) lie in the open strip) with
multiplicities mult ρ ≥ 1, locally finite in the ordinate, and
invariant under ρ ↦ 1−ρ̄ with equal multiplicity. Paper §4 (after prop:zeroside), verbatim:
"Inequalities (eq:zeroside) hold for every locally finite multiset of points in the strip 0<β<1
that is invariant under ρ ↦ 1−ρ̄ and satisfies N(t+1)−N(t) ≪ log(t+3); they contain no
arithmetic."  [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄;
multiplicities agree …)".  The quantitative local count N(t+1)−N(t) ≤ A₀ log(t+3) is not part of
this structure; it is a field of PaperInputs (H-RvM) in Zeta23/Hypotheses.lean.
Distinct points (the set) and multiplicities (the function) are deliberately separate objects. -/
structure ZeroConfig where
  /-- the set 𝒵 of distinct zeros -/
  carrier : Set ℂ
  /-- multiplicity m_ρ (value irrelevant off carrier) -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  /-- local finiteness in the ordinate: finitely many zeros with T₁ < γ ≤ T₂ -/
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace ZeroConfig

variable (Z : ZeroConfig)

/-- {ρ ∈ 𝒵 : T₁ < γ ≤ T₂}, γ = Im ρ (positive-ordinate window convention of [Results]; NOT |γ|). -/
def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- on-line points: β = 1/2. -/
def onLine : Set ℂ := {ρ | ρ.re = 1 / 2}

/-- simple points: m_ρ = 1. -/
def simple : Set ℂ := {ρ | Z.mult ρ = 1}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} counted WITH multiplicity  [Results]. -/
def N (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ

/-- N_d(T₁,T₂) := same, each distinct point counted once  [Results]. -/
def Nd (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂).ncard

/-- N₀(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITH multiplicity  [Results]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ onLine, Z.mult ρ

/-- N₀*(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITHOUT multiplicity  [Results]. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}  [Results]. -/
def N0s (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine ∩ Z.simple).ncard

/-- Nˢ(T₁,T₂) := number of simple zeros (any β) with T₁ < γ ≤ T₂  [Results]. -/
def Ns (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ Z.simple).ncard

/-- Summand of Weil's form: m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))  [eq:Wdef]. -/
def Wsummand (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))

/-- W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)), "Σ_ρ runs over the DISTINCT nontrivial zeros (of
either sign of γ) and the multiplicity is written explicitly"  [eq:Wdef]. As a tsum over the
subtype of carrier; absolute convergence is part of hypothesis H-EF. -/
def W (f g : ℝ → ℂ) : ℂ := ∑' ρ : Z.carrier, Z.Wsummand f g ρ

end ZeroConfig

/- ## 4. The test family  [subsec:family] -/

/-- "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)"  [subsec:family]. -/
structure TaperProfile (ϱ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 ϱ
  monotone : Monotone ϱ
  eq_zero : ∀ x ≤ 0, ϱ x = 0
  eq_one : ∀ x ≥ 1, ϱ x = 1

/-- Fixed (T-independent) parameters: the profile ϱ, the exponent λ (lam; X = (T/2π)^λ), and the
ramp width w ([eq:wrange]: 1 ≤ w ≤ L/8; §6 takes w := 1). T is always a separate argument. -/
structure Params where
  ϱ : ℝ → ℝ
  lam : ℝ
  w : ℝ

/-- Standing assumptions on the fixed parameters: ϱ a taper profile, 0 < λ ≤ 1, w ≥ 1.
(The upper bound w ≤ L/8 of [eq:wrange] depends on T and is stated where used.) -/
structure Params.Valid (P : Params) : Prop where
  taper : TaperProfile P.ϱ
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w

namespace Params

variable (P : Params) (T : ℝ)

/-- L := λ·l  [Notation]. -/
def L : ℝ := P.lam * l T

/-- X := e^L = (T/2π)^λ  [Notation]. -/
def X : ℝ := Real.exp (P.L T)

/-- λ₁ := L/ℓ₁ = λ + O(1/l)  [Notation], [eq:ratio]. Not the same as λ. -/
def lam1 : ℝ := P.L T / ell1 T

/-- grid step h := 2π/L  [eq:fk]. -/
def hgrid : ℝ := 2 * Real.pi / P.L T

/-- d := ⌊T/h⌋ = ⌊LT/2π⌋  [eq:fk]. -/
def d : ℕ := ⌊P.L T * T / (2 * Real.pi)⌋₊

/-- τ_k := T + k h (k ∈ ℤ)  [eq:fk]. -/
def tau (k : ℤ) : ℝ := T + k * P.hgrid T

/-- the taper φ(u) := ϱ((L/2 − |u|)/w)  [eq:phidef]; supp φ = [−L/2, L/2] exactly. -/
def phi (u : ℝ) : ℝ := P.ϱ ((P.L T / 2 - |u|) / P.w)

/-- a := L⁻¹ ∫ φ²  [eq:abdef]. -/
def a : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 2

/-- b := L⁻¹ ∫ φ⁴  [eq:abdef]. -/
def b : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 4

/-- φ̂(z) for complex z (paper convention, = h_φ(z)). -/
def phiHat (z : ℂ) : ℂ := paperFT (fun u => (P.phi T u : ℂ)) z

/-- φ̂ on the real line as a real number ("φ̂ and Φ are real, even, entire"); = Re of phiHat.
That the imaginary part vanishes is proved in Taper.lean, not assumed. -/
def phiHatR (r : ℝ) : ℝ := (P.phiHat T (r : ℂ)).re

/-- Φ := (φ²)^  [eq:PhigA], complex argument. -/
def Phi (z : ℂ) : ℂ := paperFT (fun u => (((P.phi T u) ^ 2 : ℝ) : ℂ)) z

/-- Φ on the real line as a real number; Φ(0) = aL. -/
def PhiR (r : ℝ) : ℝ := (P.Phi T (r : ℂ)).re

/-- (v ⋆ v)(y) := ∫ v(u) v(u+y) du  [eq:PhigA]. -/
def autocorr (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, v u * v (u + y)

/-- g := φ² ⋆ φ²  [eq:PhigA]; Φ² = ĝ on ℝ, g(0) = bL. -/
def g (y : ℝ) : ℝ := autocorr (fun u => (P.phi T u) ^ 2) y

/-- A_φ := φ ⋆ φ  [eq:PhigA]; φ̂² = (A_φ)^. -/
def Aphi (y : ℝ) : ℝ := autocorr (P.phi T) y

/-- c_ϱ := 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ (≥ 4)  [eq:phinorms]. -/
def crho : ℝ :=
  4 * (⨆ x : ℝ, |deriv P.ϱ x|) + 4 * ∫ x : ℝ, |deriv (deriv P.ϱ) x|

/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))  [eq:psidef]; at r = 0 the paper's value is L (2/0 = ∞), which
Lean's 2/0 = 0 would get wrong, hence the explicit case. -/
def psi (r : ℝ) : ℝ := if r = 0 then P.L T else min (P.L T) (min (2 / |r|) (P.crho / (P.w * r ^ 2)))

/-- f_k(u) := φ(u) e^{−iτ_k u}  [eq:fk]; h_{f_k}(z) = φ̂(z − τ_k). -/
def fk (k : ℤ) (u : ℝ) : ℂ := (P.phi T u : ℂ) * Complex.exp (-(Complex.I * P.tau T k * u))

/-- ℰ_T := w/L + (l² + X) log l /(T l) + T^{λ/2 − 1}  [thm:traces]. -/
def calE : ℝ :=
  P.w / P.L T + (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) + T ^ (P.lam / 2 - 1)

/- ### The prime-side matrix (second expression in [eq:Gdef]) -/

/-- G_{kl} via the PRIME side: ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ, X = e^L  [eq:Gdef, 2nd expression],
for arbitrary integer indices k, l. Real-valued. -/
def Gentry (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * nuX (P.X T) τ

/-- The d×d prime-side matrix G = (G_{kl})_{0≤k,l<d} as a complex matrix (entries are real;
complex so that RHLinalg's RCLike lemmas and the zero-side matrix share one type). -/
def Gp : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.Gentry T (k : ℤ) (l : ℤ) : ℂ)

/-- tr G̃ as the real number L⁻¹ Σ_{k<d} G_{kk} (what §5 computes)  [prop:trace]. -/
def trGtilde : ℝ := (P.L T)⁻¹ * ∑ k : Fin (P.d T), P.Gentry T k k

/-- tr G̃² = Σ_{k,l<d} G̃_{kl}² (= ‖G̃‖_F², G real symmetric)  [sec:prime intro]. -/
def trGtildeSq : ℝ := (P.L T)⁻¹ ^ 2 * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), P.Gentry T k l ^ 2

/-- scaling to tilde units M ↦ M/L  [eq:Gdef], [eq:AE]  (G̃, Ã, Ẽ). -/
def tilde {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.L T)⁻¹ : ℂ) • M

/-- scaling to hat units M ↦ M/(aL²)  [eq:hatunits]  (Ĝ, Â, Ê). Not to be mixed with tilde
units. -/
def hat {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.a T * P.L T ^ 2)⁻¹ : ℂ) • M

end Params

/- ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/

namespace ZeroConfig

/-- zero-side summand m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l). -/
def Gsummand (Z : ZeroConfig) (P : Params) (T : ℝ) (k l : ℤ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * P.phiHat T (gammaOf ρ - P.tau T k) * P.phiHat T (gammaOf ρ - P.tau T l)

/-- G_{kl} := W(f_k,f_l) = Σ_ρ m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:Gdef, 1st expression] (zero side;
tsum over all distinct zeros). H-EF gives Z.Gz P T = P.Gp T. -/
def Gz (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑' ρ : Z.carrier, Z.Gsummand P T k l ρ

/-- 𝒵(I') := distinct zeros with ordinate γ ∈ I' = (T−D₀, 2T+D₀]  [§4 Block structure]. -/
def ZIprime (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.window (T - D0 T) (2 * T + D0 T)

/-- A_{kl} := Σ_{ρ : γ ∈ I'} m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:AE] (a FINITE sum, finsum). -/
def Az (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ

/-- E := G − A  [eq:AE] (the tail: zeros with γ ∉ I', INCLUDING negative ordinates). -/
def Ez (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  Z.Gz P T - Z.Az P T

/-- 𝒮₁: β = 1/2 and m_ρ = 1, within 𝒵(I'). s₁ := #𝒮₁  [§4 Block structure]. -/
def S1 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ Z.simple
/-- 𝒮₂: β = 1/2 and m_ρ ≥ 2, within 𝒵(I'). s₂ := #𝒮₂. -/
def S2 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}
/-- off-line points of 𝒵(I') (β ≠ 1/2); 𝒫 = unordered pairs {ρ, 1−ρ̄} of these, #offLine = 2p. -/
def offLine (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ {ρ | ρ.re ≠ 1 / 2}

/-- s₁ := #𝒮₁. -/
def s1 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S1 T).ncard
/-- s₂ := #𝒮₂. -/
def s2 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S2 T).ncard
/-- p := number of unordered off-line pairs {ρ,1−ρ̄} in 𝒵(I'); #offLine = 2p. -/
def p (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.offLine T).ncard / 2

/-- N(I') := N(T−D₀, 2T+D₀)  [eq:Ncount]. -/
def NIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N (T - D0 T) (2 * T + D0 T)
/-- N_on(I') := Σ_{ρ ∈ 𝒮₁ ∪ 𝒮₂} m_ρ  [§4]. -/
def NonIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N0 (T - D0 T) (2 * T + D0 T)

end ZeroConfig

end Zeta23
end
end

-- Zeta23.Hypotheses
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — the hypothesis ("axiom") boundary.

Canonical text: the paper.

PRINCIPLE: the fields of PaperInputs are PUBLISHED, CLASSICAL inputs,
stated in the paper's own form with the paper's equation labels. Everything the paper itself derives
(lem:poisson, prop:block, prop:tail, [eq:PiPfacts], [eq:Bdef], prop:trace, thm:traces, §6, taper facts
[eq:phinorms]–[eq:psiints], …) is a proof obligation and must NOT be added here. There are NO Lean
axiom declarations anywhere in this project: hypotheses are fields of the Prop-valued structure
PaperInputs, which every headline theorem takes as an explicit argument, so #print axioms stays at
{propext, Classical.choice, Quot.sound} and the trust boundary is exactly this file.

Every field below: docstring = paper label + verbatim paper statement + literature source + any
deviation in shape (∃-constant form unless the constant is load-bearing).
-/

open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/- ## H-EF — Weil's explicit formula in the paper's spectral form  [prop:EF], [eq:EF], [eq:Wdef] -/

/-- **H-EF** [prop:EF]/[eq:EF], verbatim: "Let f,g ∈ C_c²(ℝ) with supp f, supp g ⊂ [−L/2, L/2]. Then
    W(f,g) = ∫_ℝ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,   X = e^L."
where [eq:Wdef] "W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)) … converges absolutely; here and below
Σ_ρ runs over the distinct nontrivial zeros (of either sign of γ) and the multiplicity is written
explicitly", h_f = paperFT f, and ν_X = μ + Π_X + P_X is Zeta23.nuX [eq:mudef]–[eq:nudef].
Source: Weil 1952 via [IK04, Theorem 5.12]; the paper's Appendix A [app:EF] derives this exact
normalisation from the literature form [eq:EFstd]. Zeta23/ExplicitFormula.lean proves
(literature form) → ExplicitFormulaPaper.
Shape notes: (i) quantified over every L > 0 (so X = e^L > 1 as the paper requires); (ii) the support
hypothesis is carried explicitly (without it the statement is false); (iii) the
absolute convergence of W and of the right-hand integral ("all integrals absolutely convergent",
App. A) are asserted as part of the package, since Lean's tsum/integral of a non-convergent
expression is 0; (iv) C_c² is rendered as ContDiff ℝ 2 + tsupport ⊆ [−L/2, L/2] (compact). -/
def ExplicitFormulaPaper (Z : ZeroConfig) : Prop :=
  ∀ (L : ℝ), 0 < L → ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    tsupport f ⊆ Icc (-(L / 2)) (L / 2) → tsupport g ⊆ Icc (-(L / 2)) (L / 2) →
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)

/- ## H-RvM — Riemann–von Mangoldt + local zero count  [eq:RvM], [prop:tail] first line -/

/-- **H-RvM**.
* main [eq:RvM], verbatim: "By the Riemann–von Mangoldt formula, with l := log(T/2π),
  N(T,2T) = (T/2π)(l + 2 log 2 − 1) + O(log T)."  (ell1 T = l T + 2 log 2 − 1.) Source: [Tit86, Thm 9.4].
* local_count [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such that N(t+1) − N(t) ≤ A₀ log(t+3)
  for all t ≥ 0" — "classical [Tit86, Theorem 9.2]".
  Deviation (deliberate): stated two-sided, for all real t with
  log(|t|+3), i.e. also for windows of negative ordinate. The paper's proof of prop:tail bounds the
  zeros with γ ≤ 0 using the γ ↦ −γ symmetry of the zero set, which it states in [subsec:weil] but
  which is not a field of ZeroConfig; the two-sided local count is an equally classical consequence
  of [Tit86, 9.2] + that symmetry and removes the extra seam obligation. -/
structure RiemannVonMangoldt (Z : ZeroConfig) : Prop where
  main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
  local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/- ## H-cheb — Chebyshev–Mertens  [lem:cheb], [eq:cheb1], [eq:cheb2] -/

/-- **H-cheb** [lem:cheb], verbatim: "For x ≥ 2,
  Σ_{n≤x} Λ(n) ≪ x,  Σ_{n≤x} Λ(n)/√n ≤ 3√x (x ≥ x₀),  Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,
  Σ_{n≤x} Λ(n)² ≪ x log x,                                                          [eq:cheb1]
  Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),  Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).
                                                                                    [eq:cheb2]"
Source: [MV07, §2.2] (Chebyshev, Mertens; partial summation). Sums are over n ∈ Finset.Ioc 0 ⌊x⌋₊
(Mathlib's Chebyshev.psi indexing); Λ = ArithmeticFunction.vonMangoldt; the n = 1 terms vanish
(Λ 1 = 0; in cheb1c Lean reads 0/0 as 0). Each ≪ / O(·) is an ∃ C; cheb1b keeps the paper's
literal constant 3 with threshold x₀. Zeta23/Chebyshev.lean proves these fields. -/
structure ChebyshevMertens : Prop where
  cheb1a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ≤ C * x
  cheb1b : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x
  cheb1c : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤ C * Real.sqrt x / Real.log x
  cheb1d : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ C * x * Real.log x
  cheb2a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n - Real.log x ^ 2 / 2| ≤ C * Real.log x
  cheb2b : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
      ≤ C * Real.log x ^ 2

/- ## H-MV — Montgomery–Vaughan weighted Hilbert inequality  [lem:MV] -/

/-- The weighted ("generalised") Hilbert inequality with constant C [lem:MV], verbatim:
"Let λ_1,…,λ_R be distinct real numbers, δ_r := min_{s≠r} |λ_r − λ_s|, and x_r, z_r ∈ ℂ. Then
  |Σ_{r≠s} x_r conj(z_s)/(λ_r − λ_s)| ≤ (3π/2) (Σ_r |x_r|²/δ_r)^{1/2} (Σ_r |z_r|²/δ_r)^{1/2}."
Source: [MV74, Theorem 2] for z = x (the paper citation); the bilinear form is derived in the paper by a
3-line operator-norm argument. "Any absolute constant in place of 3π/2 would suffice below."
Shape notes: index set = any Fintype ι with DecidableEq; distinctness = injectivity of freq; instead
of δ_r := min_{s≠r}|λ_r−λ_s| (undefined for R = 1) we allow ANY admissible weights 0 < δ_r ≤
|λ_r − λ_s| (s ≠ r) — equivalent to the paper's statement since the right side is antitone in δ.
The bilinear (x,z) form is assumed directly (it is what prop:PP/prop:cross consume). -/
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)

/- ## H-Γ — Stirling-type facts for μ  [eq:mufacts], [eq:muints] -/

/-- **H-Γ** [eq:mufacts], verbatim: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
  μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²),  μ'(τ) ≪ |τ|⁻¹  (|τ| ≥ 1)"
("(eq:mufacts) is Stirling's formula and Re Γ'/Γ(σ+it) = −γ_E + Σ_{n≥0}(1/(n+1) − (n+σ)/((n+σ)²+t²))"),
and the pure-Γ halves of [eq:muints]:
  "∫_T^{2T} μ(τ) dτ = Tℓ₁/(2π) + O(1/T)",   "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))".
(The remaining clause of [eq:muints], "= N(T,2T) + O(l)", is [eq:RvM] and is NOT restated here.)
Source: Stirling for Γ'/Γ (e.g. [MV07, App. C]). This structure only STATES the facts; they are
proved in Zeta23/GammaFacts/Complete.lean (`gammaFacts : GammaFacts`, via the digamma series and a
vertical-line Stirling estimate in Zeta23/GammaFacts/*). "increasing" is rendered as MonotoneOn on [0,∞)
(nondecreasing), which is all prop:trace's Riemann-sum comparison uses. -/
structure GammaFacts : Prop where
  even : ∀ τ : ℝ, mu (-τ) = mu τ
  smooth : ContDiff ℝ ∞ mu
  monotoneOn : MonotoneOn mu (Ici 0)
  mu_zero_le : ∀ τ : ℝ, mu 0 ≤ mu τ
  neg_one_lt_mu_zero : -1 < mu 0
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv mu τ| ≤ C / |τ|
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

/- ## The bundle -/

/-- The published analytic inputs of the paper ([thm:A]: "besides these it uses only Weil's explicit
formula, Stirling's formula for Γ'/Γ, the Riemann–von Mangoldt formula (eq:RvM) and the bound
N(t+1)−N(t) ≪ log(t+3)" + "Chebyshev–Mertens estimates … and the Montgomery–Vaughan generalised
Hilbert inequality"), stated for an abstract zero configuration Z. Every headline theorem takes
(H : PaperInputs Z) explicitly. -/
structure PaperInputs (Z : ZeroConfig) : Prop where
  /-- H-EF  [prop:EF]/[eq:EF] -/
  EF : ExplicitFormulaPaper Z
  /-- H-RvM [eq:RvM] + local count [prop:tail] -/
  RvM : RiemannVonMangoldt Z
  /-- H-cheb [lem:cheb] -/
  cheb : ChebyshevMertens
  /-- H-MV [lem:MV], ∃ absolute constant -/
  MV : ∃ C : ℝ, 0 < C ∧ MVHilbert C
  /-- H-Γ [eq:mufacts] + Γ-halves of [eq:muints] -/
  Gamma : GammaFacts

end Zeta23
end
end

-- Zeta23.Chebyshev
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Chebyshev.lean — discharge of the Chebyshev-type hypothesis H-cheb.

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line", Lemma [lem:cheb], displays [eq:cheb1]–[eq:cheb2]:

  "For x ≥ 2,
     Σ_{n≤x} Λ(n) ≪ x,   Σ_{n≤x} Λ(n)/√n ≤ 3√x  (x ≥ x₀),
     Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,   Σ_{n≤x} Λ(n)² ≪ x log x,    [eq:cheb1]
     Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),
     Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).       [eq:cheb2]"

H-cheb is classical [MV07 §2.2].  All sums here run over n ∈ Finset.Ioc 0 ⌊x⌋₊,
matching Mathlib's `Chebyshev.psi`.  The ≪-bounds are stated with explicit
existential constants; the paper's "≤ 3√x eventually" is provided in the robust
∃-constant form (the constant is not load-bearing downstream — [eq:Bdef] only
needs *some* B = l + C√X).

The two [eq:cheb2] asymptotics need Mertens' first theorem
Σ_{n≤x} Λ(n)/n = log x + O(1), which is not in Mathlib; it is supplied by
`mertensFirst` below, via Zeta23/FromPNTPlus/Mertens.lean.

Everything else comes from Mathlib (NumberTheory.Chebyshev ψ-bounds +
elementary induction/splitting arguments).
-/

namespace Zeta23
namespace Cheb

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

/- ## [eq:cheb1], first bound: Σ_{n≤x} Λ(n) ≪ x -/

/-- [eq:cheb1].1: Σ_{n≤x} Λ(n) ≪ x, with Mathlib's explicit Chebyshev constant. -/
theorem sum_vonMangoldt_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/- ## [eq:cheb1], second bound: Σ_{n≤x} Λ(n)/√n ≪ √x -/


section Cheb1b

open MeasureTheory intervalIntegral

private lemma sum_Icc_eq_sum_Ioc {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, c k = ∑ k ∈ Ioc 0 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc, zero_add]

private lemma psi_eq_sum_Icc' (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  rw [sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊]; rfl

/-- Abel summation specialised to Σ_{n≤x} Λ(n)/√n, in terms of ψ. -/
private lemma abel_sqrt {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      = x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        + 2⁻¹ * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t := fun t ht =>
    Real.differentiableAt_rpow_const_of_ne _ (by nlinarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ)))
      = fun t : ℝ => -(2⁻¹ : ℝ) * t ^ (-(2⁻¹ : ℝ) - 1) := Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) (Set.Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ) ^ (-(2⁻¹ : ℝ)) * Λ k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hrw : (k : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]
      norm_num
    rw [hrw, div_eq_mul_inv, mul_comm]
  rw [hL, psi_eq_sum_Icc'] at habel
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t
        * ∑ k ∈ Icc 0 ⌊t⌋₊, (fun n => Λ n) k)
      = -(2⁻¹ : ℝ) * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hderiv]
    rw [← psi_eq_sum_Icc' t]
    ring
  rw [habel, hI]
  ring

/-- The tail integral bound: ∫₁ˣ t^{-3/2} ψ(t) dt ≤ log 4·(2√x − 2) + (log x)². -/
private lemma integral_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
      ≤ Real.log 4 * (2 * Real.sqrt x - 2) + Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  -- the explicit dominating integrand
  set g : ℝ → ℝ := fun t => Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) with hg
  have hcont_g : ContinuousOn g (Set.Icc 1 x) := by
    apply ContinuousOn.add
    · exact continuousOn_const.mul fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
    · refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
  -- step 1: pointwise comparison with g on Ioc 1 x
  have hpoint : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ g t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hψ : Chebyshev.psi t ≤ Real.log 4 * t + 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_le ht1
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
        ≤ t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t) :=
          mul_le_mul_of_nonneg_left hψ hrnn
      _ = g t := by
          rw [hg]
          have e1 : t ^ (-(2⁻¹ : ℝ) - 1) * t = t ^ (-(2⁻¹ : ℝ)) := by
            rw [← Real.rpow_add_one ht0.ne']
            ring_nf
          have e2 : t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t = t⁻¹ := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0, ← Real.rpow_neg_one t]
            norm_num
          calc t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t)
              = Real.log 4 * (t ^ (-(2⁻¹ : ℝ) - 1) * t)
                + 2 * ((t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t) * Real.log t) := by ring
            _ = Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) := by
                rw [e1, e2]; ring
  -- step 2: integrability of both sides on Ioc 1 x
  have hint_g : IntegrableOn g (Set.Ioc 1 x) :=
    (hcont_g.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmeas_f : AEStronglyMeasurable (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (volume.restrict (Set.Ioc 1 x)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (ContinuousOn.aestronglyMeasurable (fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [(Set.mem_Ioc.mp ht).1] : t ≠ 0))).continuousWithinAt)
        measurableSet_Ioc)
    · exact (Chebyshev.psi_mono.measurable.aestronglyMeasurable).restrict
  have hint_f : IntegrableOn (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (Set.Ioc 1 x) := by
    refine Integrable.mono' (g := fun _ => (Real.log 4 + 4) * x)
      (integrableOn_const (by simp)) hmeas_f ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have h1 : t ^ (-(2⁻¹ : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have h2 : (0 : ℝ) ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have h3 : Chebyshev.psi t ≤ (Real.log 4 + 4) * x :=
      le_trans (Chebyshev.psi_mono ht.2) (Chebyshev.psi_le_const_mul_self hx0.le)
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn h2)]
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ 1 * Chebyshev.psi t :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Chebyshev.psi t := one_mul _
      _ ≤ (Real.log 4 + 4) * x := h3
  -- step 3: compare, then evaluate ∫ g
  refine le_trans (setIntegral_mono_on hint_f hint_g measurableSet_Ioc hpoint) ?_
  rw [← intervalIntegral.integral_of_le hx]
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.log 4 * t ^ (-(2⁻¹ : ℝ))) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact continuousOn_const.mul fun t ht =>
      (Real.continuousAt_rpow_const t _
        (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hi2 : IntervalIntegrable (fun t : ℝ => 2 * (Real.log t * t⁻¹)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
  rw [hg]
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hv1 : ∫ t in (1:ℝ)..x, t ^ (-(2⁻¹ : ℝ)) = 2 * Real.sqrt x - 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(2⁻¹)))]
    rw [Real.one_rpow]
    rw [Real.sqrt_eq_rpow]
    norm_num
    ring
  have hv2 : ∫ t in (1:ℝ)..x, Real.log t * t⁻¹ = Real.log x ^ 2 / 2 := by
    have hftc : ∀ t ∈ Set.uIcc (1:ℝ) x,
        HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log t * t⁻¹) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by nlinarith [ht.1]
      have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
      have heq : Real.log t * t⁻¹ = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
        push_cast
        ring
      rw [heq]
      exact h
    have hint : IntervalIntegrable (fun t : ℝ => Real.log t * t⁻¹) volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx]
      refine ContinuousOn.mul ?_ ?_
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
    simp [Real.log_one]
  rw [hv1, hv2]
  ring_nf
  nlinarith [Real.sqrt_nonneg x, Real.log_nonneg hx]

end Cheb1b

/-- Precise partial-summation bound: Σ_{n≤x} Λ(n)/√n ≤ 2 log 4·√x + 2 log x + (log x)²/2. -/
theorem sum_vonMangoldt_div_sqrt_le_precise {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ 2 * Real.log 4 * Real.sqrt x + 2 * Real.log x + Real.log x ^ 2 / 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [abel_sqrt hx]
  have h1 : x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
      ≤ Real.log 4 * Real.sqrt x + 2 * Real.log x := by
    have hψ := Chebyshev.psi_le hx
    have hnn : (0 : ℝ) ≤ x ^ (-(2⁻¹ : ℝ)) := Real.rpow_nonneg hx0.le _
    have e1 : x ^ (-(2⁻¹ : ℝ)) * x = Real.sqrt x := by
      rw [← Real.rpow_add_one hx0.ne', Real.sqrt_eq_rpow]; norm_num
    have e2 : x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
    calc x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        ≤ x ^ (-(2⁻¹ : ℝ)) * (Real.log 4 * x + 2 * Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_left hψ hnn
      _ = Real.log 4 * (x ^ (-(2⁻¹ : ℝ)) * x)
          + 2 * (x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x) * Real.log x := by ring
      _ = Real.log 4 * Real.sqrt x + 2 * Real.log x := by rw [e1, e2]; ring
  have h2 := integral_tail_bound hx
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h2]

/-- [eq:cheb1].2, all-x form: Σ_{n≤x} Λ(n)/√n ≤ (2 log 4 + 16)·√x for x ≥ 1. -/
theorem sum_vonMangoldt_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ (2 * Real.log 4 + 16) * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h := sum_vonMangoldt_div_sqrt_le_precise hx
  have hq : x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hlog : Real.log x ≤ 4 * x ^ ((4 : ℝ)⁻¹) := by
    have h4 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 4⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h4
    linarith
  have h14 : x ^ ((4 : ℝ)⁻¹) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hlognn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hsq : Real.log x ^ 2 ≤ 16 * Real.sqrt x := by nlinarith [hlog, hlognn, hq, h14nn]
  have h2log : 2 * Real.log x ≤ 8 * Real.sqrt x := by nlinarith [hlog, h14, h14nn]
  nlinarith [h, hsq, h2log]

/-- [eq:cheb1].2 with the threshold explicit (effective version): the witness of
`sum_vonMangoldt_div_sqrt_le_three` is `x₀ = max 1 ((48/(3 − 2 log 4))⁴)` (≤ 2.0·10⁹). -/
theorem sum_vonMangoldt_div_sqrt_le_three_explicit {x : ℝ}
    (hx : max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4) ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x := by
  have hlog4lt : Real.log 4 < 3 / 2 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h2]; nlinarith [Real.log_two_lt_d9]
  set c : ℝ := 3 - 2 * Real.log 4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hx' : max 1 ((48 / c) ^ 4) ≤ x := by rw [hc]; exact hx

  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx'
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h := sum_vonMangoldt_div_sqrt_le_precise hx1
  have hlog8 : Real.log x ≤ 8 * x ^ ((8 : ℝ)⁻¹) := by
    have h8 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 8⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h8
    linarith
  have h18nn : (0 : ℝ) ≤ x ^ ((8 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hq8 : x ^ ((8 : ℝ)⁻¹) * x ^ ((8 : ℝ)⁻¹) = x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hsq : Real.log x ^ 2 ≤ 64 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, Real.log_nonneg hx1, hq8, h18nn]
  have h84 : x ^ ((8 : ℝ)⁻¹) ≤ x ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hbound : 2 * Real.log x + Real.log x ^ 2 / 2 ≤ 48 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, hsq, h84]
  have hxc : (48 / c) ^ 4 ≤ x := le_trans (le_max_right _ _) hx'
  have h48nn : (0 : ℝ) ≤ 48 / c := by positivity
  have hx14 : 48 / c ≤ x ^ ((4 : ℝ)⁻¹) := by
    have hmono := Real.rpow_le_rpow (by positivity) hxc (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rwa [← Real.rpow_natCast (48 / c) 4, ← Real.rpow_mul h48nn,
      (by norm_num : ((4 : ℕ) : ℝ) * (4 : ℝ)⁻¹ = 1), Real.rpow_one] at hmono
  have hsqrt : Real.sqrt x = x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hkey : 48 * x ^ ((4 : ℝ)⁻¹) ≤ c * Real.sqrt x := by
    rw [hsqrt]
    have hc48 : c * (48 / c) = 48 := by field_simp
    have h1 : (48 : ℝ) ≤ c * x ^ ((4 : ℝ)⁻¹) := by
      have h2 := mul_le_mul_of_nonneg_left hx14 hcpos.le
      rwa [hc48] at h2
    calc 48 * x ^ ((4 : ℝ)⁻¹) ≤ (c * x ^ ((4 : ℝ)⁻¹)) * x ^ ((4 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h14nn
      _ = c * (x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹)) := by ring
  nlinarith [h, hbound, hkey, hc]

/-- [eq:cheb1].2, the paper's literal form (∃-version; witness = the explicit threshold above). -/
theorem sum_vonMangoldt_div_sqrt_le_three :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x :=
  ⟨max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4), fun _ hx => sum_vonMangoldt_div_sqrt_le_three_explicit hx⟩

/- ## [eq:cheb1], third bound: Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x -/

/-- Σ_{n≤N} 1/√n ≤ 2√N (elementary induction). -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hs : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hm1
    have h1 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    have h2 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt hm1.le
    have key : 1 / Real.sqrt ((m : ℝ) + 1) ≤
        2 * Real.sqrt ((m : ℝ) + 1) - 2 * Real.sqrt (m : ℝ) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)),
        Real.sqrt_nonneg (m : ℝ), Real.sqrt_nonneg ((m : ℝ) + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, key]

/-- [eq:cheb1].3: Σ_{n≤x} Λ(n)/(√n log n) ≤ C·√x/log x for x ≥ 2.
(The n = 1 summand is 0 in Lean: Λ 1 = 0.) -/
theorem sum_vonMangoldt_div_sqrt_mul_log_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤
      (4 * Real.log 4 + 40) * Real.sqrt x / Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  set R : ℕ := ⌊Real.sqrt x⌋₊ with hR
  have hsqx : Real.sqrt x ≤ x := (Real.sqrt_le_left hx0.le).mpr (by nlinarith)
  have hRle : R ≤ ⌊x⌋₊ := Nat.floor_le_floor hsqx
  have hsplit : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n))
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le R) hRle
  rw [← hsplit]
  -- part 1: n ≤ R = ⌊√x⌋
  have hpart1 : ∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 * Real.sqrt R := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_one_div_sqrt_le R)
    obtain ⟨hn0, _⟩ := Finset.mem_Ioc.mp hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [vonMangoldt_apply_one]
    · have hncast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h2.trans_lt' one_lt_two
      have hlogn : (0 : ℝ) < Real.log n := Real.log_pos hncast
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
      calc Λ n / (Real.sqrt n * Real.log n)
          ≤ Real.log n / (Real.sqrt n * Real.log n) := by
            gcongr
            exact vonMangoldt_le_log
        _ = 1 / Real.sqrt n := by field_simp
  have hq : x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hsqR : Real.sqrt R ≤ x ^ ((4 : ℝ)⁻¹) := by
    have h1 : Real.sqrt (R : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
      Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg x))
    have h2 : Real.sqrt (Real.sqrt x) = x ^ ((4 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * x ^ ((4 : ℝ)⁻¹) := by
    have h4 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 4⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h4
    linarith
  -- part 2: √x < n ≤ x
  have hS := sum_vonMangoldt_div_sqrt_le hx1
  have hsub : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
    · exact Finset.Ioc_subset_Ioc (Nat.zero_le R) le_rfl
    · exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hpart2 : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    have step : ∀ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ 2 / Real.log x * (Λ n / Real.sqrt n) := by
      intro n hn
      obtain ⟨hnR, _⟩ := Finset.mem_Ioc.mp hn
      have hsx : Real.sqrt x < (n : ℝ) := by
        have := Nat.lt_floor_add_one (Real.sqrt x)
        have hn1 : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnR
        rw [hR] at hn1
        linarith
      have hsx0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hsx0 hsx
      have hlogn : Real.log x / 2 ≤ Real.log n := by
        have := Real.log_le_log hsx0 hsx.le
        rwa [Real.log_sqrt hx0.le] at this
      have hlogn0 : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by positivity) hlogn
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
      have ha : (0 : ℝ) ≤ Λ n / Real.sqrt n := div_nonneg hΛ hsn.le
      have hL2 : (0 : ℝ) < Real.log x / 2 := by positivity
      calc Λ n / (Real.sqrt n * Real.log n)
          = (Λ n / Real.sqrt n) / Real.log n := by rw [div_div]
        _ ≤ (Λ n / Real.sqrt n) / (Real.log x / 2) := by
            rw [div_le_div_iff₀ hlogn0 hL2]
            exact mul_le_mul_of_nonneg_left hlogn ha
        _ = 2 / Real.log x * (Λ n / Real.sqrt n) := by
            rw [div_div_eq_mul_div]
            ring
    calc ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ ∑ n ∈ Ioc R ⌊x⌋₊, 2 / Real.log x * (Λ n / Real.sqrt n) :=
          Finset.sum_le_sum step
      _ = 2 / Real.log x * ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n := by
          rw [Finset.mul_sum]
      _ ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
          have h2l : (0 : ℝ) ≤ 2 / Real.log x := by positivity
          exact mul_le_mul_of_nonneg_left (le_trans hsub hS) h2l
  -- assemble: multiply through by log x
  rw [le_div_iff₀ hlx]
  have e2 : 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x
      = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    field_simp
  have hp1log : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 8 * Real.sqrt x := by
    have step1 : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ (2 * Real.sqrt R) * Real.log x :=
      mul_le_mul_of_nonneg_right hpart1 hlx.le
    have step2 : (2 * Real.sqrt R) * Real.log x ≤ (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) := by
      have hsR0 : (0 : ℝ) ≤ Real.sqrt R := Real.sqrt_nonneg _
      nlinarith [hsqR, hlog, hlx, h14nn]
    have step3 : (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) = 8 * Real.sqrt x := by
      rw [← hq]; ring
    linarith
  have hp2log : (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    calc (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x :=
          mul_le_mul_of_nonneg_right hpart2 hlx.le
      _ = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := e2
  have hfin : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      = (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        + (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x := by ring
  rw [hfin]
  nlinarith [hp1log, hp2log]

/- ## [eq:cheb1], fourth bound: Σ_{n≤x} Λ(n)² ≪ x log x -/

/-- [eq:cheb1].4: Σ_{n≤x} Λ(n)² ≤ (log 4 + 4)·x·log x, from Λ(n) ≤ log n ≤ log x. -/
theorem sum_vonMangoldt_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have h0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  have key : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n) * Real.log x := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.mpr hnN) (Nat.floor_le h0)
    have h1 : Λ n ≤ Real.log x :=
      le_trans vonMangoldt_le_log (Real.log_le_log (by exact_mod_cast hn0) hnx)
    calc Λ n ^ 2 = Λ n * Λ n := pow_two _
      _ ≤ Λ n * Real.log x := mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg
  refine key.trans ?_
  have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self h0
  have h3 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h4 : (0 : ℝ) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n :=
    Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  calc (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n) * Real.log x
      ≤ ((Real.log 4 + 4) * x) * Real.log x := mul_le_mul_of_nonneg_right h2 h3
    _ = (Real.log 4 + 4) * x * Real.log x := by ring


/- ## [eq:cheb2]: the two Mertens-type asymptotics

Mertens' first theorem Σ_{n≤x} Λ(n)/n = log x + O(1) is supplied by
`Mertens.sum_mangoldt_div_eq_log` (see
Zeta23/FromPNTPlus/Mertens.lean), so both [eq:cheb2] bounds are unconditional. -/

section Cheb2

open MeasureTheory

/-- Mertens' first theorem (von Mangoldt form): |Σ_{n≤x} Λ(n)/n − log x| ≤ log 4 + 4
for x ≥ 1.  Paper [lem:cheb] cites it as "Mertens' formula"; classical [MV07 §2.2]. -/
theorem mertensFirst {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ Real.log 4 + 4 :=
  Mertens.sum_mangoldt_div_eq_log hx

/-- Partial sums of Λ(n)/n, in the Icc form produced by Abel summation. -/
private noncomputable def Msum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k / k

/-- Partial sums of Λ(n)²/n, in the Icc form produced by Abel summation. -/
private noncomputable def M2sum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k ^ 2 / k

private lemma Msum_eq_Ioc (t : ℝ) : Msum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊

private lemma M2sum_eq_Ioc (t : ℝ) : M2sum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k ^ 2 / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊

private lemma Msum_mono : Monotone Msum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

private lemma M2sum_mono : Monotone M2sum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

private lemma Msum_nonneg (t : ℝ) : 0 ≤ Msum t :=
  Finset.sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

private lemma M2sum_nonneg (t : ℝ) : 0 ≤ M2sum t :=
  Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

/-- Abel summation with f = log, c n = Λ n / n. -/
private lemma abel_log_Msum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  rw [hL, hR] at habel
  rw [habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [Real.deriv_log]
  rfl

/-- Abel summation with f = log, c n = Λ n ^ 2 / n. -/
private lemma abel_log_M2sum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n ^ 2 / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n ^ 2 / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n ^ 2 / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  rw [hL, hR] at habel
  rw [habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [Real.deriv_log]
  rfl

private lemma integral_inv_Ioc {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
  rw [← intervalIntegral.integral_of_le hx, integral_inv ?h]
  · rw [div_one]
  case h =>
    rw [Set.uIcc_of_le hx]
    intro h
    rw [Set.mem_Icc] at h
    linarith [h.1]

private lemma integral_inv_mul_log {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t = Real.log x ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (t⁻¹ * Real.log t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
    have heq : t⁻¹ * Real.log t = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

private lemma integral_inv_mul_log_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t ^ 2 = Real.log x ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
    (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 3 / 3) (t⁻¹ * Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 3).div_const 3
    have heq : t⁻¹ * Real.log t ^ 2 = ((3 : ℕ) : ℝ) * Real.log t ^ (3 - 1) * t⁻¹ / 3 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t ^ 2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ (hlogcont.pow 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

/-- Integrability of t⁻¹·M on (1, x] for a monotone nonnegative M. -/
private lemma integrableOn_inv_mul_mono {M : ℝ → ℝ} (hmono : Monotone M)
    (hnn : ∀ t, 0 ≤ M t) {x : ℝ} (_hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * M t) (Set.Ioc 1 x) := by
  refine Integrable.mono' (g := fun _ => M x)
    (integrableOn_const (by simp)) ?_ ?_
  · exact (measurable_inv.mul hmono.measurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hti : t⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; linarith
    have h0 : (0 : ℝ) ≤ t⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hnn t))]
    calc t⁻¹ * M t ≤ 1 * M t := mul_le_mul_of_nonneg_right hti (hnn t)
      _ = M t := one_mul _
      _ ≤ M x := hmono ht.2

/-- Partial summation step: Σ_{n≤x} log n · Λ(n)/n = (log x)²/2 + O(log x). -/
private lemma sum_log_mul_vonMangoldt_div_bound {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)) - Real.log x ^ 2 / 2|
      ≤ 2 * (Real.log 4 + 4) * Real.log x := by
  set K : ℝ := Real.log 4 + 4 with hK
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hMert : ∀ t : ℝ, 1 ≤ t → |Msum t - Real.log t| ≤ K := fun t ht => by
    rw [Msum_eq_Ioc]
    exact mertensFirst ht
  have habel := abel_log_Msum hx
  have hint_log : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_M : IntegrableOn (fun t : ℝ => t⁻¹ * Msum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono Msum_mono Msum_nonneg hx
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_diff : IntegrableOn (fun t : ℝ => t⁻¹ * (Msum t - Real.log t)) (Set.Ioc 1 x) :=
    ((hint_M.sub hint_log).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t)
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by
    rw [← MeasureTheory.integral_add hint_log hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| ≤ K * Real.log x := by
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (Msum t - Real.log t)‖ ≤ K * t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t⁻¹),
        mul_comm K t⁻¹]
      exact mul_le_mul_of_nonneg_left (hMert t ht1) (by positivity)
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
        ≤ ∫ t in Set.Ioc 1 x, K * t⁻¹ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le (hint_inv.const_mul K) hb
      _ = K * ∫ t in Set.Ioc 1 x, t⁻¹ := MeasureTheory.integral_const_mul K _
      _ = K * Real.log x := by rw [integral_inv_Ioc hx]
  have hMx : |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ K := mertensFirst hx
  rw [habel, hsplit, integral_inv_mul_log hx]
  have harr : Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n)
        - (Real.log x ^ 2 / 2 + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t))
        - Real.log x ^ 2 / 2
      = Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by ring
  rw [harr]
  have h1 : |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)| ≤ Real.log x * K := by
    rw [abs_mul, abs_of_nonneg hlx]
    exact mul_le_mul_of_nonneg_left hMx hlx
  calc |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
      ≤ |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)|
        + |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| := abs_sub _ _
    _ ≤ Real.log x * K + K * Real.log x := add_le_add h1 hE
    _ = 2 * K * Real.log x := by ring

/- ### The proper-prime-power defect

[lem:cheb] proof: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) (the two differ
only at proper prime powers)".  The defect Σ_{n≤x} Λ(n)(log n − Λ(n))/n is
supported on prime powers pᵏ with k ≥ 2, where its value is (k−1)log²p/pᵏ;
summing over all p, k bounds it by an absolute constant. -/

private lemma sum_k_mul_half_pow_aux (K : ℕ) :
    (∑ k ∈ Icc 1 K, (k : ℝ) * (2⁻¹) ^ k) + ((K : ℝ) + 2) * (2⁻¹) ^ K ≤ 2 := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hp : ((2 : ℝ)⁻¹) ^ (m + 1) = ((2 : ℝ)⁻¹) ^ m * (2 : ℝ)⁻¹ := pow_succ _ _
    push_cast
    nlinarith [ih, hp, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) m]

private lemma sum_k_mul_half_pow_le (K : ℕ) :
    ∑ k ∈ Icc 1 K, (k : ℝ) * (2⁻¹) ^ k ≤ 2 := by
  have h := sum_k_mul_half_pow_aux K
  nlinarith [h, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) K,
    (by positivity : (0 : ℝ) ≤ (K : ℝ) + 2)]

/-- log²m/m² ≤ 64·(m^{7/4})⁻¹ for m ≥ 2 (via log m ≤ 8·m^{1/8}). -/
private lemma log_sq_div_sq_le {m : ℕ} (hm : 2 ≤ m) :
    Real.log m ^ 2 / (m : ℝ) ^ 2 ≤ 64 * ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlog : Real.log m ≤ 8 * (m : ℝ) ^ ((8 : ℝ)⁻¹) := by
    have h8 := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 8⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h8
    linarith
  have h18nn : (0 : ℝ) ≤ (m : ℝ) ^ ((8 : ℝ)⁻¹) := Real.rpow_nonneg hm0.le _
  have hq8 : (m : ℝ) ^ ((8 : ℝ)⁻¹) * (m : ℝ) ^ ((8 : ℝ)⁻¹) = (m : ℝ) ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hm0]; norm_num
  have hsq : Real.log m ^ 2 ≤ 64 * (m : ℝ) ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog, Real.log_nonneg hm1, hq8, h18nn]
  have e : (m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2 = ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
    rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_sub hm0, ← Real.rpow_neg hm0.le]
    norm_num
  calc Real.log m ^ 2 / (m : ℝ) ^ 2
      ≤ 64 * (m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2 := by gcongr
    _ = 64 * ((m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2) := by ring
    _ = 64 * ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by rw [e]

/-- Per-term bound for the defect: (k−1)·log²p/pᵏ ≤ 256·k·2⁻ᵏ·(p^{7/4})⁻¹. -/
private lemma defect_term_le {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) :
    ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
      ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · rw [← hk1]
    norm_num
    positivity
  · have hk2' : 2 ≤ k := hk2
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hsplitpow : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hgepow : (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ (k - 2) :=
      pow_le_pow_left₀ (by norm_num) hp2 _
    have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ k := by
      rw [hsplitpow]
      gcongr
    have hnum_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) * Real.log p ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have h1 : ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
        ≤ ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2)) := by
      gcongr
    have e1 : ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2))
        = (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
      field_simp
    have e2 : ((2 : ℝ) ^ (k - 2))⁻¹ = 4 * ((2 : ℝ) ^ k)⁻¹ := by
      have h4 : (2 : ℝ) ^ (k - 2) * 4 = 2 ^ k := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [← h4, mul_inv]
      field_simp
    have hfac_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹ :=
      mul_nonneg (by linarith) (by positivity)
    have hAP : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ :=
      mul_nonneg (by positivity) (by positivity)
    calc ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
        ≤ ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2)) := h1
      _ = (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (Real.log p ^ 2 / (p : ℝ) ^ 2) := e1
      _ ≤ (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (64 * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) :=
          mul_le_mul_of_nonneg_left (log_sq_div_sq_le hp.two_le) hfac_nn
      _ = (((k : ℝ) - 1) * (4 * ((2 : ℝ) ^ k)⁻¹)) * (64 * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) := by
          rw [e2]
      _ ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
          rw [inv_pow]
          nlinarith [hAP]

/-- the telescoping step: for 2 ≤ m, (m^{7/4})⁻¹ ≤ 2(1/√(m−1) − 1/√m). -/
lemma rpow_inv_le_telescope {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm2 : (2:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm10 : (0:ℝ) < (m : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((m:ℝ) - 1) := Real.sqrt_pos.mpr hm10
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hmono : Real.sqrt ((m:ℝ) - 1) ≤ Real.sqrt m := Real.sqrt_le_sqrt (by linarith)
  have h1 : Real.sqrt m * Real.sqrt m = (m:ℝ) := Real.mul_self_sqrt hm0.le
  have h2 : Real.sqrt ((m:ℝ) - 1) * Real.sqrt ((m:ℝ) - 1) = (m:ℝ) - 1 := Real.mul_self_sqrt hm10.le
  have hprod : (Real.sqrt m - Real.sqrt ((m:ℝ) - 1)) * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) = 1 := by
    nlinarith [h1, h2]
  have hdiff : 1 / Real.sqrt ((m:ℝ) - 1) - 1 / Real.sqrt m
      = 1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))) := by
    rw [div_sub_div _ _ hs.ne' hsm.ne', one_mul, mul_one]
    rw [show Real.sqrt m - Real.sqrt ((m:ℝ) - 1)
        = 1 / (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) from by
      rw [eq_div_iff (by positivity)]
      exact hprod]
    rw [div_div]
    ring_nf
  have hsq : Real.sqrt m = (m:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow m
  have h32 : (m:ℝ) ^ ((3:ℝ)/2) = (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
    norm_num
  have hden : Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
      ≤ 2 * (m:ℝ) ^ ((3:ℝ)/2) := by
    calc Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
        ≤ Real.sqrt m * Real.sqrt m * (2 * Real.sqrt m) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hmono hsm.le) (by linarith)
            (by positivity) (by positivity)
      _ = 2 * ((m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2)) := by
          rw [hsq]
          ring
      _ = 2 * (m:ℝ) ^ ((3:ℝ)/2) := by rw [h32]
  have h74 : (m:ℝ) ^ ((3:ℝ)/2) ≤ (m:ℝ) ^ ((7:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [hdiff]
  calc ((m:ℝ) ^ ((7:ℝ)/4))⁻¹ = 1 / ((m:ℝ) ^ ((7:ℝ)/4)) := (one_div _).symm
    _ ≤ 1 / ((m:ℝ) ^ ((3:ℝ)/2)) := one_div_le_one_div_of_le (by positivity) h74
    _ = 2 * (1 / (2 * (m:ℝ) ^ ((3:ℝ)/2))) := by
        field_simp
    _ ≤ 2 * (1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact one_div_le_one_div_of_le (by positivity) hden

/-- partial sums with remainder: Σ_{m ≤ N} (m^{7/4})⁻¹ ≤ 3 − 2/√N for N ≥ 1. -/
lemma sum_range_rpow_inv_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.range (N + 1), ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 - 2 / Real.sqrt N := by
  induction N with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hN with h1 | h1
      · -- n + 1 = 1, i.e. n = 0: range 2 = {0, 1}
        have hn0 : n = 0 := by omega
        subst hn0
        norm_num [Finset.sum_range_succ, Real.sqrt_one]
      · -- n ≥ 1
        have hn1 : 1 ≤ n := by omega
        have htel := rpow_inv_le_telescope (m := n + 1) (by omega)
        have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
        rw [hcast] at htel
        rw [Finset.sum_range_succ]
        have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
        have hs1 : 0 < Real.sqrt ((n:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hc2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        calc ∑ m ∈ Finset.range (n + 1), ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹
              + (((n + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 4))⁻¹
            ≤ (3 - 2 / Real.sqrt n) + 2 * (1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
              exact add_le_add (ih hn1) htel
          _ = 3 - 2 / Real.sqrt ((n:ℝ) + 1) := by
              rw [hc2]
              field_simp
              ring
          _ = 3 - 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by rw [hc2]

/-- Σ' m⁻⁷ᐟ⁴ ≤ 3. -/
lemma tsum_rpow_neg_seven_quarters_le :
    ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 := by
  refine tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rcases Nat.eq_zero_or_pos M with h0 | hM
    · subst h0
      norm_num [Finset.sum_range_succ]
    · refine le_trans (sum_range_rpow_inv_le hM) ?_
      have : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM)
      have h2 : 0 < 2 / Real.sqrt M := by positivity
      linarith

/-- The defect sum bounded by the explicit numeral 1537 = 512·3 + 1 (effective version;
uses the √-telescoping bound ζ-style Σ' m^{−7/4} ≤ 3 above). -/
lemma defect_bounded_explicit : ∀ x : ℝ,
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ 1537 := by
  intro x
  have hsum74 : Summable (fun m : ℕ => ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set B : ℝ := ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ with hB
  have hBnn : (0 : ℝ) ≤ B := tsum_nonneg fun m => by positivity
  have hB3 : B ≤ 3 := by
    rw [hB]
    exact tsum_rpow_neg_seven_quarters_le
  rcases lt_or_ge x 0 with hxneg | hx0
  · rw [Nat.floor_of_nonpos hxneg.le]
    simp only [Finset.Ioc_self, Finset.sum_empty]
    positivity
  have hvanish : ∀ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≠ 0 → IsPrimePow n := by
    intro n _ hne
    by_contra hnot
    rw [vonMangoldt_eq_zero_iff.mpr hnot] at hne
    simp at hne
  rw [← Finset.sum_filter_of_ne hvanish,
    Chebyshev.sum_PrimePow_eq_sum_sum (fun n => Λ n * (Real.log n - Λ n) / n) hx0]
  have hinner : ∀ k ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ))
        ≤ 256 * B * ((k : ℝ) * (2⁻¹) ^ k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : k ≠ 0 := by omega
    have hstep : ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ)
        ≤ ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hΛ : Λ (p ^ k) = Real.log p := by
        rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hpp]
      have hlg : Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log p := by
        rw [Nat.cast_pow, Real.log_pow]
      have heq : Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ)
          = ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k := by
        rw [hΛ, hlg, Nat.cast_pow]
        ring
      rw [heq]
      exact defect_term_le hk1 hpp
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    have hs : (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) ≤ B :=
      hsum74.sum_le_tsum _ fun i _ => by positivity
    calc 256 * ((k : ℝ) * (2⁻¹) ^ k)
          * (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹)
        ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * B :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 256 * B * ((k : ℝ) * (2⁻¹) ^ k) := by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have h2 := sum_k_mul_half_pow_le ⌊Real.log x / Real.log 2⌋₊
  nlinarith [h2, hBnn, hB3]

/-- The defect sum is bounded by an absolute constant (from the explicit bound). -/
private lemma defect_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ C :=
  ⟨1537, by norm_num, defect_bounded_explicit⟩

/-- [eq:cheb2].1 with the constant explicit: C2a = 2(log 4 + 4) + 1537/log 2 (≤ 2230). -/
theorem sum_vonMangoldt_sq_div_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2|
      ≤ (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x := by
  set CD : ℝ := 1537 with hCDdef
  have hCD : ∀ y : ℝ, ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (Real.log n - Λ n) / n ≤ CD := by
    intro y
    rw [hCDdef]
    exact defect_bounded_explicit y
  have hCD0 : (0:ℝ) < CD := by rw [hCDdef]; norm_num
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  intro x hx
  show _ ≤ (2 * (Real.log 4 + 4) + CD / Real.log 2) * Real.log x
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 := abs_le.mp (sum_log_mul_vonMangoldt_div_bound hx1)
  have hdiff : (∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n))
        - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hD0 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n :=
    Finset.sum_nonneg fun n _ =>
      div_nonneg (mul_nonneg vonMangoldt_nonneg (sub_nonneg.mpr vonMangoldt_le_log))
        (Nat.cast_nonneg n)
  have hDle := hCD x
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hCDlog : CD ≤ CD / Real.log 2 * Real.log x := by
    have hkey : CD / Real.log 2 * Real.log 2 = CD := div_mul_cancel₀ CD hlog2pos.ne'
    calc CD = CD / Real.log 2 * Real.log 2 := hkey.symm
      _ ≤ CD / Real.log 2 * Real.log x :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hnn : (0 : ℝ) ≤ CD / Real.log 2 * Real.log x :=
    mul_nonneg (by positivity) (Real.log_nonneg hx1)
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]

/-- [eq:cheb2].1: Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x).
Paper [lem:cheb]: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) ..., and partial
summation from Mertens' formula gives Σ_{n≤x} Λ(n) log n/n = ½log²x + O(log x)."
(From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2| ≤ C * Real.log x := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_eq_explicit⟩

/-- [eq:cheb2].2 with the constant explicit: C2b = C2a/2 + 1/log 2. -/
theorem sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
        Real.log x ^ 3 / 6|
      ≤ ((2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
  set C2 : ℝ := 2 * (Real.log 4 + 4) + 1537 / Real.log 2 with hC2def
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hC2 : ∀ y : ℝ, 2 ≤ y → |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n ^ 2 / n) - Real.log y ^ 2 / 2|
      ≤ C2 * Real.log y := by
    intro y hy
    rw [hC2def]
    exact sum_vonMangoldt_sq_div_eq_explicit y hy
  have hC20 : (0:ℝ) < C2 := by
    rw [hC2def]
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  intro x hx
  show _ ≤ (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  -- the target sum equals ∫ t⁻¹ M2sum t
  have habel := abel_log_M2sum hx1
  have hident : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
      = ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
    have e1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
        = Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n)
          - ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e1, habel]
    ring
  rw [hident]
  -- pointwise bound for the error density on (1, x]
  have hM2b : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      |M2sum t - Real.log t ^ 2 / 2| ≤ C2 * Real.log t + 1 := by
    intro t ht
    have hlt0 : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht.1.le
    rcases le_or_gt 2 t with h2 | h2
    · have h := hC2 t h2
      rw [M2sum_eq_Ioc]
      have hC2log : (0 : ℝ) ≤ C2 * Real.log t := mul_nonneg hC20.le hlt0
      calc |(∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n ^ 2 / n) - Real.log t ^ 2 / 2| ≤ C2 * Real.log t := h
        _ ≤ C2 * Real.log t + 1 := by linarith
    · have ht1 : (1 : ℝ) < t := ht.1
      have hfl : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ t)]
        constructor
        · exact_mod_cast ht1.le
        · exact_mod_cast (by linarith : t < 1 + 1)
      have hM20 : M2sum t = 0 := by
        rw [M2sum_eq_Ioc, hfl]
        rw [show Finset.Ioc 0 1 = {1} from rfl]
        simp [vonMangoldt_apply_one]
      rw [hM20, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hlt2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) h2.le
      have hl21 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
      nlinarith [mul_nonneg hC20.le hlt0]
  -- integrabilities
  have hcont_logsq : IntegrableOn (fun t : ℝ => t⁻¹ * (Real.log t ^ 2 / 2)) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
      (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    refine ContinuousOn.mul ?_ ((hlogcont.pow 2).div_const 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_M2 : IntegrableOn (fun t : ℝ => t⁻¹ * M2sum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono M2sum_mono M2sum_nonneg hx1
  have hint_diff : IntegrableOn
      (fun t : ℝ => t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)) (Set.Ioc 1 x) :=
    ((hint_M2.sub hcont_logsq).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2))
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by
    rw [← MeasureTheory.integral_add hcont_logsq hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hval : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2) = Real.log x ^ 3 / 6 := by
    have e : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2)
        = ∫ t in Set.Ioc 1 x, (t⁻¹ * Real.log t ^ 2) * (1 / 2) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
    rw [e, MeasureTheory.integral_mul_const, integral_inv_mul_log_sq hx1]
    ring
  -- error bound
  have hint_invlog : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := by
    have hg_int : IntegrableOn (fun t : ℝ => C2 * (t⁻¹ * Real.log t) + t⁻¹) (Set.Ioc 1 x) :=
      (hint_invlog.const_mul C2).add hint_inv
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)‖ ≤ C2 * (t⁻¹ * Real.log t) + t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have hti : (0 : ℝ) ≤ t⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hti]
      calc t⁻¹ * |M2sum t - Real.log t ^ 2 / 2| ≤ t⁻¹ * (C2 * Real.log t + 1) :=
            mul_le_mul_of_nonneg_left (hM2b t ht) hti
        _ = C2 * (t⁻¹ * Real.log t) + t⁻¹ := by ring
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
        ≤ ∫ t in Set.Ioc 1 x, (C2 * (t⁻¹ * Real.log t) + t⁻¹) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le hg_int hb
      _ = C2 * (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t) + ∫ t in Set.Ioc 1 x, t⁻¹ := by
          rw [MeasureTheory.integral_add (hint_invlog.const_mul C2) hint_inv,
            MeasureTheory.integral_const_mul]
      _ = C2 * (Real.log x ^ 2 / 2) + Real.log x := by
          rw [integral_inv_mul_log hx1, integral_inv_Ioc hx1]
  -- assemble
  rw [hsplit, hval]
  have harr : Real.log x ^ 3 / 6
        + (∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2))
        - Real.log x ^ 3 / 6
      = ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by ring
  rw [harr]
  have hlogx2 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    nlinarith [hlx]
  calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := hE
    _ ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x ^ 2 / Real.log 2 := by linarith
    _ = (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
        field_simp

/-- [eq:cheb2].2: Σ_{n≤x} (Λ(n)²/n)(log x − log n) = (log x)³/6 + O((log x)²).
Paper [lem:cheb]: "The second formula is ∫₁ˣ (Σ_{n≤t} Λ(n)²/n) dt/t."  (From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_mul_log_sub_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
          Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit⟩

/-- The full H-cheb package [lem:cheb], instantiating the
`Zeta23.ChebyshevMertens` hypothesis structure of Hypotheses.lean.  Everything is
unconditional: Mathlib's Chebyshev ψ-bound + Abel summation + the Mertens
theorem (Zeta23/FromPNTPlus/Mertens.lean). -/
theorem chebyshevMertens : ChebyshevMertens where
  cheb1a := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_le (by linarith)⟩
  cheb1b := sum_vonMangoldt_div_sqrt_le_three
  cheb1c := ⟨4 * Real.log 4 + 40, fun x hx => sum_vonMangoldt_div_sqrt_mul_log_le hx⟩
  cheb1d := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_sq_le (by linarith)⟩
  cheb2a := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_eq
    exact ⟨C, fun x hx => h x hx⟩
  cheb2b := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_mul_log_sub_eq
    exact ⟨C, fun x hx => h x hx⟩

end Cheb2

end Cheb
end Zeta23
end

-- LeanClassics.MertensSecond
section
/-
Mertens' first and second theorems over primes:
  ∑_{p ≤ x} log p / p = log x + O(1),
  ∑_{p ≤ x} 1/p = log log x + B + O(1/log x) for a constant B.

Proof. zeta23 has the first theorem in von Mangoldt form, |∑_{n ≤ x} Λ(n)/n − log x| ≤ log 4 + 4
(`Zeta23.Cheb.mertensFirst`). Abel summation of e(n) = Λ(n) − 1_prime(n) log n against 1/t, whose partial sums
are ψ − θ = O(√t) (Mathlib's `Chebyshev.psi_sub_theta_le_mul_sqrt`), shows the prime powers p^k with
k ≥ 2 contribute O(1). Abel summation of c(p) = log p/p against 1/log t then gives
  ∑_{p ≤ x} 1/p = S(x)/log x + ∫₂ˣ S(t)/(t log²t) dt,  S(t) = ∑_{p ≤ t} log p/p = log t + R(t), |R| ≤ K,
and ∫₂ˣ dt/(t log t) = log log x − log log 2, while ∫ R(t)/(t log²t) converges on (2, ∞) with tail
≤ K/log x since ∫ₓ^∞ dt/(t log²t) = 1/log x.
-/

open Real Finset Filter Asymptotics MeasureTheory Set
open ArithmeticFunction hiding log

noncomputable section

namespace LeanClassics.MertensSecond

/-- `c(n) = log n / n` on primes, `0` otherwise. -/
def c (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

/-- `e(n) = Λ(n) − 1_prime(n) log n`. -/
def e (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n else 0

/-- `S(t) = ∑_{p ≤ t} log p / p`. -/
def S (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k

lemma e_sum (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, e k = Chebyshev.psi t - Chebyshev.theta t := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, ← Finset.sum_sub_distrib]
  rfl

lemma S_eq (t : ℝ) : S t = ∑ p ∈ Finset.Icc 0 ⌊t⌋₊ with p.Prime, Real.log p / p := by
  rw [S, Finset.sum_filter]; rfl

/-- `0 ≤ ψ − θ ≤ C √t` with `C ≥ 0`. -/
lemma psi_sub_theta_bound : ∃ C, 0 ≤ C ∧ ∀ t, 0 ≤ t →
    0 ≤ Chebyshev.psi t - Chebyshev.theta t ∧ Chebyshev.psi t - Chebyshev.theta t ≤ C * √t := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, fun t ht => ⟨by linarith [Chebyshev.theta_le_psi t], ?_⟩⟩
  exact (hC t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

/-- Prime powers `p^k`, `k ≥ 2`, contribute `O(1)` to `∑ Λ(n)/n`. -/
lemma lambda_sub_S_bound : ∃ D, ∀ x : ℝ, 2 ≤ x →
    |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k / k) - S x| ≤ D := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_theta_bound
  refine ⟨3 * C, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have habel := sum_mul_eq_sub_integral_mul₁ e (f := fun t : ℝ => t⁻¹)
    (by simp [e]) (by simp [e]) x
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      refine ContinuousOn.integrableOn_Icc fun t ht => ?_
      have ht0 : t ≠ 0 := by linarith [ht.1]
      refine ContinuousAt.continuousWithinAt ?_
      have : deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ := funext fun _ => deriv_inv
      rw [this]
      exact (((continuous_pow 2 : Continuous fun s : ℝ => s ^ 2).continuousAt).inv₀
        (pow_ne_zero 2 ht0)).neg)
  have hlhs : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ((k : ℝ)⁻¹) * e k
      = (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k / k) - S x := by
    rw [S, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [e, c]
    split_ifs <;> ring
  rw [hlhs] at habel
  simp only [e_sum] at habel
  rw [habel]
  -- the boundary term
  have hb := hC x hx0.le
  have h1 : |x⁻¹ * (Chebyshev.psi x - Chebyshev.theta x)| ≤ C := by
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hx0.le) hb.1), inv_mul_le_iff₀ hx0]
    have hs : √x ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    nlinarith [hb.2, mul_le_mul_of_nonneg_left hs hC0]
  -- the integral term
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-(3 : ℝ) / 2)) (Set.Ioc 2 x) := by
    have := (intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := -(3 : ℝ) / 2) (a := 2) (b := x)
      (Or.inr (by rw [Set.uIcc_of_le hx]; intro h; linarith [h.1]))).const_mul C
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp this
  have h2 : ‖∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => t⁻¹) t
      * (Chebyshev.psi t - Chebyshev.theta t)‖ ≤ ∫ t in Set.Ioc 2 x, C * t ^ (-(3 : ℝ) / 2) := by
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := by linarith [ht.1]
    have hbt := hC t ht0.le
    rw [deriv_inv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity),
      abs_of_nonneg hbt.1]
    calc (t ^ 2)⁻¹ * (Chebyshev.psi t - Chebyshev.theta t) ≤ (t ^ 2)⁻¹ * (C * √t) :=
          mul_le_mul_of_nonneg_left hbt.2 (by positivity)
      _ = C * t ^ (-(3 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, show -(3 : ℝ) / 2 = 1 / 2 - 2 by norm_num,
            Real.rpow_sub ht0, Real.rpow_two]
          field_simp
  have h3 : ∫ t in Set.Ioc 2 x, C * t ^ (-(3 : ℝ) / 2) ≤ 2 * C := by
    rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, by rw [Set.uIcc_of_le hx]; intro h; linarith [h.1]⟩)]
    have hx' : 0 ≤ x ^ (-(3 : ℝ) / 2 + 1) := Real.rpow_nonneg hx0.le _
    have h2' : (2 : ℝ) ^ (-(3 : ℝ) / 2 + 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have e : (x ^ (-(3 : ℝ) / 2 + 1) - 2 ^ (-(3 : ℝ) / 2 + 1)) / (-(3 : ℝ) / 2 + 1)
        = 2 * (2 ^ (-(3 : ℝ) / 2 + 1) - x ^ (-(3 : ℝ) / 2 + 1)) := by ring
    rw [e]
    nlinarith
  rw [Real.norm_eq_abs] at h2
  have := abs_sub (x⁻¹ * (Chebyshev.psi x - Chebyshev.theta x))
    (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t))
  linarith

/-- **Mertens' first theorem over primes**: `∑_{p ≤ x} log p / p = log x + O(1)`. -/
theorem S_sub_log_bound : ∃ K, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x → |S x - Real.log x| ≤ K := by
  obtain ⟨D, hD⟩ := lambda_sub_S_bound
  refine ⟨Real.log 4 + 4 + |D|, by positivity, fun x hx => ?_⟩
  have h1 := Zeta23.Cheb.mertensFirst (x := x) (by linarith)
  have hIcc : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k / k
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]; simp
  have h2 := hD x hx
  rw [hIcc] at h2
  have := abs_sub_le (S x) (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n)
    (Real.log x)
  rw [abs_sub_comm] at h2
  linarith [le_abs_self D]

/-- **Mertens' first theorem over primes**, as a `IsBigO` statement. -/
theorem sum_log_div_prime_sub_log_isBigO :
    (fun x : ℝ => (∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, Real.log p / p) - Real.log x)
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  obtain ⟨K, -, hK⟩ := S_sub_log_bound
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [← S_eq, Real.norm_eq_abs, norm_one, mul_one]
  exact hK x hx

/- ### Mertens' second theorem -/

lemma S_measurable : Measurable S := by
  have : S = (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, c k) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

lemma hasDerivAt_neg_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) (t⁻¹ / Real.log t ^ 2) t := by
  have hl := (Real.log_pos ht).ne'
  have := ((Real.hasDerivAt_log (by linarith)).inv hl).neg
  exact this.congr_deriv (by ring)

lemma tendsto_neg_inv_log : Tendsto (fun t => -(Real.log t)⁻¹) atTop (nhds 0) := by
  simpa using (tendsto_log_atTop.inv_tendsto_atTop).neg

lemma integrableOn_tail {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t => t⁻¹ / Real.log t ^ 2) (Ioi x) :=
  integrableOn_Ioi_deriv_of_nonneg ((hasDerivAt_neg_inv_log hx).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_neg_inv_log (hx.trans ht))
    (fun t ht => by have : 0 < t := (by linarith [show x < t from ht]); positivity)
    tendsto_neg_inv_log

lemma integral_tail {x : ℝ} (hx : 1 < x) :
    ∫ t in Ioi x, t⁻¹ / Real.log t ^ 2 = (Real.log x)⁻¹ := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_neg_inv_log hx).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_neg_inv_log (hx.trans ht))
    (fun t ht => by have : 0 < t := (by linarith [show x < t from ht]); positivity)
    tendsto_neg_inv_log]
  ring

/-- `h(t) = R(t)/(t log²t)` with `R = S − log`. -/
def h (t : ℝ) : ℝ := t⁻¹ * (S t - Real.log t) / Real.log t ^ 2

lemma h_measurable : Measurable h :=
  (measurable_inv.mul (S_measurable.sub Real.measurable_log)).div (Real.measurable_log.pow_const 2)

lemma integrableOn_h {K : ℝ} (hK : ∀ x : ℝ, 2 ≤ x → |S x - Real.log x| ≤ K) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn h (Ioi x) := by
  refine Integrable.mono' ((integrableOn_tail (by linarith)).const_mul K)
    h_measurable.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht2 : 2 ≤ t := by linarith [show x < t from ht]
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  rw [h, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (inv_pos.mpr (by linarith)),
    abs_of_pos (by positivity : 0 < Real.log t ^ 2), mul_div_assoc', mul_comm K]
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (hK t ht2) (by positivity)) (inv_nonneg.mpr (by linarith))

/-- Mertens' second theorem with an explicit error: `|∑_{p ≤ x} 1/p − log log x − B| ≤ K/log x`
for `x ≥ 2`. -/
theorem sum_inv_prime_explicit : ∃ B K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ)) - Real.log (Real.log x) - B|
      ≤ K / Real.log x := by
  obtain ⟨K, hK0, hK⟩ := S_sub_log_bound
  set I := ∫ t in Ioi 2, h t with hI
  refine ⟨1 - Real.log (Real.log 2) + I, 2 * K, by positivity, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  -- Abel summation against 1/log t
  have habel := sum_mul_eq_sub_integral_mul₁ c (f := fun t : ℝ => (Real.log t)⁻¹)
    (by simp [c]) (by simp [c]) x
    (fun z hz => by
      have hz1 : 1 < z := by linarith [hz.1]
      exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hz1).ne').differentiableAt)
    (by
      refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ ↦ ContinuousWithinAt.congr ?_
        (fun _ _ ↦ deriv_inv_log_apply) deriv_inv_log_apply
      have : z ≠ 0 := by linarith
      have : Real.log z ^ 2 ≠ 0 := by
        refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
      exact ContinuousAt.continuousWithinAt <| by fun_prop)
  have hlhs : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log k)⁻¹ * c k
      = ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]
    split_ifs with hk
    · have : Real.log k ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hk.pos)
        (by exact_mod_cast hk.ne_one)
      field_simp
    · simp
  rw [hlhs] at habel
  simp only [deriv_inv_log_apply,
    show ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = S t from fun _ => rfl] at habel
  rw [habel]
  -- split the integral
  have hsplitfun : ∀ t ∈ Ioc (2 : ℝ) x, -t⁻¹ / Real.log t ^ 2 * S t = -(t⁻¹ / Real.log t + h t) := by
    intro t ht
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [h]; field_simp; ring
  have hA : IntegrableOn (fun t : ℝ => t⁻¹ / Real.log t) (Ioc 2 x) := by
    refine (ContinuousOn.integrableOn_Icc fun t ht => ?_).mono_set Ioc_subset_Icc_self
    have : t ≠ 0 := by linarith [ht.1]
    have : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hH2 := integrableOn_h hK (le_refl 2)
  have hHx := integrableOn_h hK hx
  have hJ : ∫ t in Ioc 2 x, -t⁻¹ / Real.log t ^ 2 * S t
      = -((∫ t in Ioc 2 x, t⁻¹ / Real.log t) + ∫ t in Ioc 2 x, h t) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hsplitfun, integral_neg,
      integral_add hA (hH2.mono_set Ioc_subset_Ioi_self)]
  have hLL : ∫ t in Ioc 2 x, t⁻¹ / Real.log t = Real.log (Real.log x) - Real.log (Real.log 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (Real.log t))
      (fun t ht => ?_) ?_
    · have ht1 : 1 < t := by
        rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
      have hl := (Real.log_pos ht1).ne'
      exact ((Real.hasDerivAt_log (by linarith)).log hl).congr_deriv (by field_simp)
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have : t ≠ 0 := by linarith [ht.1]
      have : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hU : ∫ t in Ioi 2, h t = (∫ t in Ioc 2 x, h t) + ∫ t in Ioi x, h t := by
    rw [← Ioc_union_Ioi_eq_Ioi hx, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hH2.mono_set Ioc_subset_Ioi_self) hHx]
  have hT : |∫ t in Ioi x, h t| ≤ K * (Real.log x)⁻¹ := by
    have hb : ‖∫ t in Ioi x, h t‖ ≤ ∫ t in Ioi x, K * (t⁻¹ / Real.log t ^ 2) := by
      refine norm_integral_le_of_norm_le ((integrableOn_tail hx1).const_mul K) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht2 : 2 ≤ t := by linarith [show x < t from ht]
      have hl : 0 < Real.log t := Real.log_pos (by linarith)
      rw [h, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (inv_pos.mpr (by linarith)),
        abs_of_pos (by positivity : 0 < Real.log t ^ 2), mul_div_assoc]
      calc t⁻¹ * (|S t - Real.log t| / Real.log t ^ 2) ≤ t⁻¹ * (K / Real.log t ^ 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hK t ht2) (by positivity))
              (inv_nonneg.mpr (by linarith))
        _ = K * (t⁻¹ / Real.log t ^ 2) := by ring
    rw [integral_const_mul, integral_tail hx1, Real.norm_eq_abs] at hb
    exact hb
  have hR : |(Real.log x)⁻¹ * (S x - Real.log x)| ≤ K * (Real.log x)⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hlx), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK x hx) (inv_nonneg.mpr hlx.le)
  have hSx : (Real.log x)⁻¹ * S x = 1 + (Real.log x)⁻¹ * (S x - Real.log x) := by
    field_simp; ring
  rw [hJ, hLL, hSx, div_eq_mul_inv]
  have key : 1 + (Real.log x)⁻¹ * (S x - Real.log x)
      - -((Real.log (Real.log x) - Real.log (Real.log 2)) + ∫ t in Ioc 2 x, h t)
      - Real.log (Real.log x) - (1 - Real.log (Real.log 2) + I)
      = (Real.log x)⁻¹ * (S x - Real.log x) - ∫ t in Ioi x, h t := by
    rw [hI, hU]; ring
  rw [key]
  have := abs_sub ((Real.log x)⁻¹ * (S x - Real.log x)) (∫ t in Ioi x, h t)
  linarith

/-- **Mertens' second theorem**: `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
theorem sum_inv_prime_sub_log_log_isBigO : ∃ B : ℝ,
    (fun x : ℝ => (∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ))
      - Real.log (Real.log x) - B) =O[atTop] fun x : ℝ => 1 / Real.log x := by
  obtain ⟨B, K, -, hK⟩ := sum_inv_prime_explicit
  refine ⟨B, IsBigO.of_bound K ?_⟩
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.log x),
    ← div_eq_mul_one_div]
  exact hK x hx

end LeanClassics.MertensSecond
end
end

-- LeanClassics.MertensThird
section
/-
Mertens' third theorem: ∏_{p ≤ x} (1 − 1/p)⁻¹ ~ e^γ log x, and Mertens' constant
∑_{p ≤ x} 1/p − log log x → γ + ∑_p (log(1 − 1/p) + 1/p).

Proof. Mertens' second theorem (`MertensSecond.sum_inv_prime_explicit`) gives P(x) = ∑_{p ≤ x} 1/p =
log log x + B + r(x), |r(x)| ≤ K/log x. For σ = 1 + ε > 1, Abel summation gives
∑_p p^{−σ} = ε ∫₂^∞ t^{−σ} P(t) dt. Substituting t = e^u and u = v/ε,
  ε ∫₂^∞ t^{−σ}(P(t) − B) dt = ∫_{ε log 2}^∞ e^{−v}(log v − log ε + r(e^{v/ε})) dv
    = −γ − log ε + o(1),
using ∫₀^∞ e^{−v} log v dv = Γ′(1) = −γ (Mathlib's `eulerMascheroniConstant_eq_neg_deriv` and
`hasDerivAt_GammaIntegral`) and dominated convergence for the r-term. So ∑_p p^{−σ} = B − γ − log ε + o(1).
The Euler product gives log ζ(σ) = ∑_p p^{−σ} + ∑_p δ(p^{−σ}), δ(y) = −log(1 − y) − y, and
log ζ(σ) + log ε → 0 because (s − 1)ζ(s) → 1. With ∑_p δ(p^{−σ}) → E = ∑_p δ(1/p), B + E = γ.
Then ∑_{p ≤ x} −log(1 − 1/p) = P(x) + ∑_{p ≤ x} δ(1/p) → log log x + γ, and exponentiate.
-/

open Real Finset Filter Asymptotics MeasureTheory Set Topology

noncomputable section

namespace LeanClassics.MertensThird

/- ### `∫₀^∞ e^{−v} log v dv = −γ` -/

lemma integral_exp_neg_mul_log :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v = -Real.eulerMascheroniConstant := by
  have hD := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
  have hev : Complex.GammaIntegral =ᶠ[𝓝 (1 : ℂ)] Complex.Gamma := by
    have : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hG := (hD.congr_of_eventuallyEq hev.symm)
  have hR : HasDerivAt Real.Gamma
      ((∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))).re) 1 := by
    exact hG.real_of_complex
  have hint : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t)))
      = ((∫ t : ℝ in Ioi 0, Real.exp (-t) * Real.log t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [sub_self, Complex.cpow_zero, one_mul]
    push_cast; ring
  rw [hint, Complex.ofReal_re] at hR
  rw [Real.eulerMascheroniConstant_eq_neg_deriv, hR.deriv, neg_neg]

/-- `f(v) = e^{−v} log v`. -/
def fγ (v : ℝ) : ℝ := Real.exp (-v) * Real.log v

lemma abs_log_le {v : ℝ} (hv : 0 < v) : |Real.log v| ≤ 2 * v ^ (-(1 : ℝ) / 2) + v := by
  have hw : 0 ≤ v ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hv.le _
  rcases le_or_gt 1 v with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos hv]
  · rw [abs_of_neg (Real.log_neg hv h1)]
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hv (-(1 : ℝ) / 2))
    rw [Real.log_rpow hv] at h
    linarith

lemma integrableOn_fγ : IntegrableOn fγ (Ioi 0) := by
  have h1 := (Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)).const_mul 2
  have h2 := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  refine Integrable.mono' (h1.add h2)
    (((Real.measurable_exp.comp measurable_neg).mul Real.measurable_log).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
  have hv0 : 0 < v := hv
  have e1 : v ^ ((1 : ℝ) / 2 - 1) = v ^ (-(1 : ℝ) / 2) := by norm_num
  have e2 : v ^ ((2 : ℝ) - 1) = v := by norm_num
  simp only [Pi.add_apply, e1, e2]
  rw [fγ, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := mul_le_mul_of_nonneg_left (abs_log_le hv0) (Real.exp_pos (-v)).le
  linarith

lemma tendsto_integral_Ioi_fγ :
    Tendsto (fun c => ∫ v in Ioi c, fγ v) (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  rw [← integral_exp_neg_mul_log]
  have hI : Integrable fγ (volume.restrict (Ioi 0)) := integrableOn_fγ
  have key : (fun c => ∫ v in Ioi 0, (Ioi c).indicator fγ v) =ᶠ[𝓝[>] (0 : ℝ)]
      fun c => ∫ v in Ioi c, fγ v := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (le_of_lt (show (0 : ℝ) < c from hc)))]
  refine Tendsto.congr' key ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖fγ v‖)
    (Eventually.of_forall fun c => (hI.indicator measurableSet_Ioi).aestronglyMeasurable)
    (Eventually.of_forall fun c => Eventually.of_forall fun v => norm_indicator_le_norm_self _ _)
    hI.norm ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < v from hv)] with c hc
  exact (Set.indicator_of_mem (show v ∈ Set.Ioi c from hc.2) fγ).symm

/- ### The Abelian limit -/

/-- `P(t) = ∑_{p ≤ t} 1/p`. -/
def P (t : ℝ) : ℝ := ∑ p ∈ Finset.Icc 0 ⌊t⌋₊ with p.Prime, (1 / p : ℝ)

lemma P_measurable : Measurable P := by
  have : P = (fun n : ℕ => ∑ p ∈ Finset.Icc 0 n with p.Prime, (1 / p : ℝ)) ∘ (fun t : ℝ => ⌊t⌋₊) :=
    rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

lemma P_nonneg (t : ℝ) : 0 ≤ P t := Finset.sum_nonneg fun _ _ => by positivity

section
variable {B K : ℝ} (hK0 : 0 ≤ K)
  (hBK : ∀ x : ℝ, 2 ≤ x → |P x - Real.log (Real.log x) - B| ≤ K / Real.log x)

/-- `r(u) = P(e^u) − B − log u`. -/
def r (B : ℝ) (u : ℝ) : ℝ := P (Real.exp u) - B - Real.log u

lemma r_measurable (B : ℝ) : Measurable (r B) :=
  ((P_measurable.comp Real.measurable_exp).sub measurable_const).sub Real.measurable_log

include hBK in
lemma abs_r_le {u : ℝ} (hu : Real.log 2 ≤ u) : |r B u| ≤ K / u := by
  have h2 : 2 ≤ Real.exp u := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu
  have := hBK (Real.exp u) h2
  rw [Real.log_exp] at this
  rw [r, show P (Real.exp u) - B - Real.log u = P (Real.exp u) - Real.log u - B by ring]
  exact this

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

include hK0 hBK in
/-- The substituted form: for `ε > 0`,
`ε ∫₂^∞ t^{−(1+ε)}(P(t) − B) dt + log ε = ∫_{c}^∞ e^{−v} log v dv + log ε (1 − e^{−c}) + R_ε`
with `c = ε log 2` and `R_ε = ∫_{c}^∞ e^{−v} r(v/ε) dv`. -/
lemma eps_identity {ε : ℝ} (hε : 0 < ε) :
    ε * (∫ t in Ioi 2, t ^ (-(1 + ε)) * (P t - B)) + Real.log ε
      = (∫ v in Ioi (ε * Real.log 2), fγ v)
        + Real.log ε * (1 - Real.exp (-(ε * Real.log 2)))
        + ∫ v in Ioi (ε * Real.log 2), Real.exp (-v) * r B (v / ε) := by
  set a := Real.log 2 with ha
  have ha0 : 0 < a := log_two_pos'
  set Q : ℝ → ℝ := fun u => P (Real.exp u) - B with hQ
  -- t = e^u
  have h1 : ∫ t in Ioi 2, t ^ (-(1 + ε)) * (P t - B)
      = ∫ u in Ioi a, Real.exp (-(ε * u)) * Q u := by
    rw [← integral_comp_log_Ioi (fun u => Real.exp (-(ε * u)) * Q u) (by norm_num : (0 : ℝ) < 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    simp only [hQ, smul_eq_mul, Real.exp_log ht0]
    rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add ht0, Real.rpow_neg_one,
      Real.rpow_def_of_pos ht0]
    ring_nf
  -- u = v/ε
  have h2 : ∫ u in Ioi a, Real.exp (-(ε * u)) * Q u
      = ε⁻¹ * ∫ v in Ioi (ε * a), Real.exp (-v) * Q (v / ε) := by
    rw [← smul_eq_mul, ← integral_comp_mul_left_Ioi (fun v => Real.exp (-v) * Q (v / ε)) a hε]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [mul_div_cancel_left₀ _ hε.ne']
  -- split
  have hint1 : IntegrableOn fγ (Ioi (ε * a)) :=
    integrableOn_fγ.mono_set (Set.Ioi_subset_Ioi (by positivity))
  have hint2 : IntegrableOn (fun v => Real.log ε * Real.exp (-v)) (Ioi (ε * a)) :=
    (integrableOn_exp_neg_Ioi _).const_mul _
  have hint3 : IntegrableOn (fun v => Real.exp (-v) * r B (v / ε)) (Ioi (ε * a)) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi (ε * a)).const_mul (K / a))
      ((Real.measurable_exp.comp measurable_neg).mul
        ((r_measurable B).comp (measurable_id.div_const ε))).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have hv' : a < v / ε := by rw [lt_div_iff₀ hε]; linarith [show ε * a < v from hv]
    have hr := abs_r_le hBK hv'.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right (hr.trans ?_) (Real.exp_pos _).le
    exact div_le_div_of_nonneg_left hK0 ha0 hv'.le
  have h3 : ∫ v in Ioi (ε * a), Real.exp (-v) * Q (v / ε)
      = (∫ v in Ioi (ε * a), fγ v) - (∫ v in Ioi (ε * a), Real.log ε * Real.exp (-v))
        + ∫ v in Ioi (ε * a), Real.exp (-v) * r B (v / ε) := by
    have e : ∫ v in Ioi (ε * a), Real.exp (-v) * Q (v / ε)
        = ∫ v in Ioi (ε * a), ((fγ v - Real.log ε * Real.exp (-v))
          + Real.exp (-v) * r B (v / ε)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      have hv0 : 0 < v := lt_trans (by positivity) hv
      simp only [hQ, r, fγ, Real.log_div hv0.ne' hε.ne']
      ring
    rw [e, integral_add (f := fun v => fγ v - Real.log ε * Real.exp (-v)) (hint1.sub hint2) hint3,
      integral_sub hint1 hint2]
  rw [h1, h2, h3, integral_const_mul, integral_exp_neg_Ioi, ← mul_assoc, mul_inv_cancel₀ hε.ne',
    one_mul]
  ring

include hK0 hBK in
theorem tendsto_eps_integral :
    Tendsto (fun ε => ε * (∫ t in Ioi 2, t ^ (-(1 + ε)) * (P t - B)) + Real.log ε) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  set a := Real.log 2 with ha
  have ha0 : 0 < a := log_two_pos'
  have hid : (fun ε => (∫ v in Ioi (ε * a), fγ v) + Real.log ε * (1 - Real.exp (-(ε * a)))
      + ∫ v in Ioi (ε * a), Real.exp (-v) * r B (v / ε)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ε * (∫ t in Ioi 2, t ^ (-(1 + ε)) * (P t - B)) + Real.log ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (eps_identity hK0 hBK hε).symm
  refine Tendsto.congr' hid ?_
  rw [show -Real.eulerMascheroniConstant = -Real.eulerMascheroniConstant + 0 + 0 by ring]
  have hc : Tendsto (fun ε : ℝ => ε * a) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => ε * a) (𝓝 0) (𝓝 (0 * a)) := tendsto_id.mul_const a
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hε ha0
  refine ((tendsto_integral_Ioi_fγ.comp hc).add ?_).add ?_
  · -- log ε (1 − e^{−εa}) → 0
    have hml : Tendsto (fun ε : ℝ => a * |ε * Real.log ε|) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝 0) (𝓝 (0 * Real.log 0)) :=
        Real.continuous_mul_log.tendsto 0
      rw [zero_mul] at h0
      simpa using (h0.abs.const_mul a).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hml
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hx : 0 ≤ ε * a := by positivity
    have e1 : 1 - Real.exp (-(ε * a)) ≤ ε * a := by linarith [Real.add_one_le_exp (-(ε * a))]
    have e2 : 0 ≤ 1 - Real.exp (-(ε * a)) := by
      have : Real.exp (-(ε * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg e2, abs_mul, abs_of_pos hε0]
    calc |Real.log ε| * (1 - Real.exp (-(ε * a))) ≤ |Real.log ε| * (ε * a) :=
          mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
      _ = a * (ε * |Real.log ε|) := by ring
  · -- dominated convergence for the remainder
    have hI : Integrable (fun v => K / a * Real.exp (-v)) (volume.restrict (Ioi 0)) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have key : (fun ε => ∫ v in Ioi 0, (Ioi (ε * a)).indicator
        (fun v => Real.exp (-v) * r B (v / ε)) v) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => ∫ v in Ioi (ε * a), Real.exp (-v) * r B (v / ε) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : 0 < ε := hε
      rw [setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by positivity))]
    refine Tendsto.congr' key ?_
    have hD := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun _ : ℝ => (0 : ℝ))
      (F := fun ε v => (Ioi (ε * a)).indicator (fun v => Real.exp (-v) * r B (v / ε)) v)
      (fun v => K / a * Real.exp (-v))
      (Eventually.of_forall fun ε => (Measurable.indicator
        ((Real.measurable_exp.comp measurable_neg).mul
          ((r_measurable B).comp (measurable_id.div_const ε))) measurableSet_Ioi).aestronglyMeasurable)
      ?_ hI ?_
    · rwa [integral_zero] at hD
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : 0 < ε := hε
      refine Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ Ioi (ε * a)
      · rw [Set.indicator_of_mem hv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
          mul_comm]
        have hv' : a < v / ε := by rw [lt_div_iff₀ hε0]; linarith [show ε * a < v from hv]
        refine mul_le_mul_of_nonneg_right ((abs_r_le hBK hv'.le).trans ?_) (Real.exp_pos _).le
        exact div_le_div_of_nonneg_left hK0 ha0 hv'.le
      · rw [Set.indicator_of_notMem hv, norm_zero]; positivity
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : 0 < v := hv
      have hlim : Tendsto (fun ε : ℝ => K * Real.exp (-v) / v * ε) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => K * Real.exp (-v) / v * ε) (𝓝 0)
            (𝓝 (K * Real.exp (-v) / v * 0)) := tendsto_id.const_mul _
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : 0 < ε := hε
      by_cases hvm : v ∈ Ioi (ε * a)
      · rw [Set.indicator_of_mem hvm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hv' : a < v / ε := by rw [lt_div_iff₀ hε0]; linarith [show ε * a < v from hvm]
        have hr := abs_r_le hBK hv'.le
        calc Real.exp (-v) * |r B (v / ε)| ≤ Real.exp (-v) * (K / (v / ε)) :=
              mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
          _ = K * Real.exp (-v) / v * ε := by field_simp
      · rw [Set.indicator_of_notMem hvm, norm_zero]; positivity

end

/- ### Abel summation to infinity -/

/-- `a_σ(n) = n^{−σ}` on primes. -/
def aσ (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-σ) else 0

lemma summable_aσ {σ : ℝ} (hσ : 1 < σ) : Summable (aσ σ) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).of_nonneg_of_le
    (fun n => by unfold aσ; split_ifs <;> positivity) (fun n => ?_)
  unfold aσ; split_ifs <;> [exact le_rfl; positivity]

section
variable {B K : ℝ} (hK0 : 0 ≤ K)
  (hBK : ∀ x : ℝ, 2 ≤ x → |P x - Real.log (Real.log x) - B| ≤ K / Real.log x)

include hK0 hBK in
lemma P_le_log {t : ℝ} (ht : 2 ≤ t) : P t ≤ Real.log t + (|B| + K / Real.log 2) := by
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have h1 := (abs_le.mp (hBK t ht)).2
  have h2 := Real.log_le_sub_one_of_pos hlt
  have h3 : K / Real.log t ≤ K / Real.log 2 :=
    div_le_div_of_nonneg_left hK0 log_two_pos' (Real.log_le_log (by norm_num) ht)
  linarith [le_abs_self B]

include hK0 hBK in
lemma integrableOn_rpow_mul_P {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => t ^ (-(1 + ε)) * P t) (Ioi 2) := by
  set C0 := |B| + K / Real.log 2
  have hC0 : 0 ≤ C0 := by have := log_two_pos'; positivity
  have hi1 := (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + ε / 2) < -1)
    (by norm_num : (0 : ℝ) < 2)).const_mul (2 / ε)
  have hi2 := (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + ε) < -1)
    (by norm_num : (0 : ℝ) < 2)).const_mul C0
  refine Integrable.mono' (hi1.add hi2)
    (((measurable_id.pow_const _).mul P_measurable).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht2 : 2 ≤ t := le_of_lt ht
  have ht0 : 0 < t := by linarith
  have hP := P_le_log hK0 hBK ht2
  have hlog := Real.log_le_rpow_div ht0.le (by positivity : 0 < ε / 2)
  have hw : 0 < t ^ (-(1 + ε)) := Real.rpow_pos_of_pos ht0 _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw, abs_of_nonneg (P_nonneg t)]
  have e : t ^ (-(1 + ε)) * (t ^ (ε / 2) / (ε / 2)) = 2 / ε * t ^ (-(1 + ε / 2)) := by
    rw [mul_div_assoc', ← Real.rpow_add ht0]
    field_simp
    ring_nf
  calc t ^ (-(1 + ε)) * P t ≤ t ^ (-(1 + ε)) * (t ^ (ε / 2) / (ε / 2) + C0) :=
        mul_le_mul_of_nonneg_left (by linarith) hw.le
    _ = 2 / ε * t ^ (-(1 + ε / 2)) + C0 * t ^ (-(1 + ε)) := by rw [mul_add, e]; ring

include hK0 hBK in
/-- `∑_p p^{−(1+ε)} = ε ∫₂^∞ t^{−(1+ε)} P(t) dt`. -/
lemma tsum_aσ_eq {ε : ℝ} (hε : 0 < ε) :
    ∑' n, aσ (1 + ε) n = ε * ∫ t in Ioi 2, t ^ (-(1 + ε)) * P t := by
  set c₁ : ℕ → ℝ := fun n => if n.Prime then 1 / n else 0 with hc₁
  have hPsum : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c₁ k = P t := fun t => by
    rw [P, Finset.sum_filter]
  have hderiv : deriv (fun t : ℝ => t ^ (-ε)) = fun t => -ε * t ^ (-ε - 1) := Real.deriv_rpow_const' _
  have habel : ∀ N : ℕ, 2 ≤ N → ∑ k ∈ Finset.Icc 0 N, aσ (1 + ε) k
      = (N : ℝ) ^ (-ε) * P N + ε * ∫ t in (2 : ℝ)..N, t ^ (-(1 + ε)) * P t := by
    intro N hN
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h := sum_mul_eq_sub_integral_mul₁ c₁ (f := fun t : ℝ => t ^ (-ε))
      (by simp [hc₁]) (by simp [hc₁, Nat.not_prime_one]) (N : ℝ)
      (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1]))
      (by
        rw [hderiv]
        refine ContinuousOn.integrableOn_Icc fun t ht => ?_
        exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
          (Or.inl (by linarith [ht.1])))).continuousWithinAt)
    simp only [hPsum, hderiv] at h
    rw [Nat.floor_natCast] at h
    have hl : ∑ k ∈ Finset.Icc 0 N, (k : ℝ) ^ (-ε) * c₁ k = ∑ k ∈ Finset.Icc 0 N, aσ (1 + ε) k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc₁, aσ]
      split_ifs with hk
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
        rw [show -(1 + ε) = -ε + -1 by ring, Real.rpow_add hk0, Real.rpow_neg_one, one_div]
      · simp
    rw [hl] at h
    rw [h, intervalIntegral.integral_of_le hN', ← integral_const_mul, sub_eq_add_neg, ← integral_neg]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [show -ε - 1 = -(1 + ε) by ring]
    ring
  -- limits along N → ∞
  have hsum := (summable_aσ (by linarith : 1 < 1 + ε)).hasSum.tendsto_sum_nat
  have hL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, aσ (1 + ε) k) atTop
      (𝓝 (∑' n, aσ (1 + ε) n)) := by
    have := hsum.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun N => ?_
    simp [Function.comp, Nat.range_succ_eq_Icc_zero]
  have hint := integrableOn_rpow_mul_P hK0 hBK hε
  have hI := intervalIntegral_tendsto_integral_Ioi 2 hint tendsto_natCast_atTop_atTop
  have hB0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ε) * P N) atTop (𝓝 0) := by
    set C0 := |B| + K / Real.log 2
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
    have h2 := tendsto_rpow_neg_atTop hε
    have h3 : Tendsto (fun x : ℝ => Real.log x / x ^ ε + C0 * x ^ (-ε)) atTop (𝓝 0) := by
      simpa using h1.add (h2.const_mul C0)
    refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (by positivity) (P_nonneg _))
      ?_ (h3.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hP := P_le_log hK0 hBK hN'
    simp only [Function.comp]
    rw [Real.rpow_neg hN0.le, div_eq_mul_inv, mul_comm (Real.log N)]
    have : 0 ≤ ((N : ℝ) ^ ε)⁻¹ := by positivity
    nlinarith
  have hR : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ε) * P N + ε * ∫ t in (2 : ℝ)..N, t ^ (-(1 + ε)) * P t)
      atTop (𝓝 (0 + ε * ∫ t in Ioi 2, t ^ (-(1 + ε)) * P t)) := hB0.add (hI.const_mul ε)
  rw [zero_add] at hR
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (habel N hN).symm

end


/-- `−log(1 − p^{−σ})` on primes. -/
def lt (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then -Real.log (1 - (n : ℝ) ^ (-σ)) else 0

/-- `δ(p^{−σ}) = −log(1 − p^{−σ}) − p^{−σ}` on primes. -/
def dd (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then -Real.log (1 - (n : ℝ) ^ (-σ)) - (n : ℝ) ^ (-σ) else 0

lemma rpow_neg_le_inv {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 1 ≤ σ) :
    0 ≤ (n : ℝ) ^ (-σ) ∧ (n : ℝ) ^ (-σ) ≤ 1 / n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  refine ⟨by positivity, ?_⟩
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]

lemma abs_delta_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    |-Real.log (1 - y) - y| ≤ 2 * y ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := y) (by rw [abs_of_nonneg h0]; linarith) 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at h
  rw [abs_of_nonneg h0] at h
  rw [show -Real.log (1 - y) - y = -(y + Real.log (1 - y)) by ring, abs_neg]
  refine h.trans ?_
  rw [show y ^ (1 + 1) = y ^ 2 by ring, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sq_nonneg y) (by linarith : 0 ≤ 1 - 2 * y)]

lemma abs_dd_le {σ : ℝ} (hσ : 1 ≤ σ) (n : ℕ) : ‖dd σ n‖ ≤ 2 / (n : ℝ) ^ 2 := by
  unfold dd
  split_ifs with hp
  · obtain ⟨h0, h1⟩ := rpow_neg_le_inv hp.two_le hσ
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
    have h12 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    rw [Real.norm_eq_abs]
    refine (abs_delta_le h0 (h1.trans h12)).trans ?_
    have : ((n : ℝ) ^ (-σ)) ^ 2 ≤ (1 / n) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [div_pow, one_pow] at this
    calc 2 * ((n : ℝ) ^ (-σ)) ^ 2 ≤ 2 * (1 / (n : ℝ) ^ 2) := by linarith
      _ = 2 / (n : ℝ) ^ 2 := by ring
  · simp only [norm_zero]; positivity

lemma summable_bound : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
  have := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2
  simpa [div_eq_mul_inv] using this

lemma summable_dd {σ : ℝ} (hσ : 1 ≤ σ) : Summable (dd σ) :=
  Summable.of_norm_bounded summable_bound (abs_dd_le hσ)

lemma lt_eq (σ : ℝ) : lt σ = fun n => aσ σ n + dd σ n := by
  funext n; unfold lt aσ dd; split_ifs <;> ring

/-- `ζ(σ) = exp(∑_p −log(1 − p^{−σ}))` for real `σ > 1`. -/
lemma zeta_eq_exp {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta σ = ((Real.exp (∑' n, lt σ n) : ℝ) : ℂ) := by
  rw [← riemannZeta_eulerProduct_exp_log (s := σ) (by simpa using hσ), Complex.ofReal_exp,
    Complex.ofReal_tsum]
  congr 1
  have := tsum_subtype {p : ℕ | p.Prime} (fun n : ℕ => -Complex.log (1 - (n : ℂ) ^ (-(σ : ℂ))))
  refine this.trans (tsum_congr fun n => ?_)
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
    obtain ⟨h0, h1⟩ := rpow_neg_le_inv hp.two_le hσ.le
    have h12 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp), lt, if_pos hp,
      Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_neg, Complex.ofReal_natCast]
  · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp), lt, if_neg hp,
      Complex.ofReal_zero]

lemma tendsto_one_add : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
  rw [add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `log ζ(1 + ε) + log ε → 0`. -/
lemma tendsto_L_add_log :
    Tendsto (fun ε => (∑' n, lt (1 + ε) n) + Real.log ε) (𝓝[>] 0) (𝓝 0) := by
  have hg : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 1).comp tendsto_one_add
      rw [Complex.ofReal_one] at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  have h1 := (Complex.continuous_re.tendsto _).comp (riemannZeta_residue_one.comp hg)
  simp only [Complex.one_re] at h1
  have h2 := h1.log one_ne_zero
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp]
  rw [zeta_eq_exp (by linarith), show (((1 + ε : ℝ) : ℂ) - 1) = ((ε : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re, Real.log_mul hε.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `∑_p δ(p^{−(1+ε)}) → ∑_p δ(1/p)`. -/
lemma tendsto_tsum_dd :
    Tendsto (fun ε => ∑' n, dd (1 + ε) n) (𝓝[>] 0) (𝓝 (∑' n, dd 1 n)) := by
  refine tendsto_tsum_of_dominated_convergence summable_bound (fun k => ?_) ?_
  · unfold dd
    split_ifs with hp
    · have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      obtain ⟨_, h1⟩ := rpow_neg_le_inv hp.two_le le_rfl
      have hn2 : (2 : ℝ) ≤ k := by exact_mod_cast hp.two_le
      have h12 : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
      have hc : ContinuousAt (fun σ : ℝ => (k : ℝ) ^ (-σ)) 1 :=
        continuousAt_const.rpow continuousAt_neg (Or.inl hk)
      have hc2 : ContinuousAt (fun σ : ℝ => -Real.log (1 - (k : ℝ) ^ (-σ)) - (k : ℝ) ^ (-σ)) 1 :=
        ((continuousAt_const.sub hc).log (by
          intro h; change (1 : ℝ) - (k : ℝ) ^ (-(1 : ℝ)) = 0 at h; linarith)).neg.sub hc
      exact hc2.tendsto.comp tendsto_one_add
    · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact abs_dd_le (by linarith)


/- ### The constant -/

section
variable {B K : ℝ} (hK0 : 0 ≤ K)
  (hBK : ∀ x : ℝ, 2 ≤ x → |P x - Real.log (Real.log x) - B| ≤ K / Real.log x)

include hK0 hBK in
/-- `∑_p p^{−(1+ε)} + log ε → B − γ`. -/
lemma tendsto_tsum_aσ_add_log :
    Tendsto (fun ε => (∑' n, aσ (1 + ε) n) + Real.log ε) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant + B)) := by
  have h2 : Tendsto (fun ε : ℝ => B * (2 : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous (fun ε : ℝ => (2 : ℝ) ^ (-ε)) :=
      continuous_const.rpow continuous_neg (fun _ => Or.inl two_ne_zero)
    have := ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))).const_mul B
    simpa using this
  refine ((tendsto_eps_integral hK0 hBK).add h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [tsum_aσ_eq hK0 hBK hε]
  have hi1 := integrableOn_rpow_mul_P hK0 hBK hε
  have hi2 := (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + ε) < -1)
    (by norm_num : (0 : ℝ) < 2)).const_mul B
  have hsplit : ∫ t in Ioi 2, t ^ (-(1 + ε)) * (P t - B)
      = (∫ t in Ioi 2, t ^ (-(1 + ε)) * P t) - ∫ t in Ioi 2, B * t ^ (-(1 + ε)) := by
    rw [← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsplit, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by norm_num),
    show -(1 + ε) + 1 = -ε by ring]
  field_simp
  ring

include hK0 hBK in
/-- Mertens' constant: `B = γ − ∑_p δ(1/p)`. -/
lemma B_eq : B = Real.eulerMascheroniConstant - ∑' n, dd 1 n := by
  have h := (tendsto_tsum_aσ_add_log hK0 hBK).add tendsto_tsum_dd
  have h' : Tendsto (fun ε => (∑' n, lt (1 + ε) n) + Real.log ε) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant + B + ∑' n, dd 1 n)) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [lt_eq, (summable_aσ (by linarith)).tsum_add (summable_dd (by linarith))]
    ring
  have := tendsto_nhds_unique h' tendsto_L_add_log
  linarith

end

lemma dd_one (n : ℕ) : dd 1 n = if n.Prime then -Real.log (1 - 1 / n) - 1 / n else 0 := by
  unfold dd; rw [Real.rpow_neg_one, one_div]

/-- **Mertens' constant**: `∑_{p ≤ x} 1/p − log log x → γ + ∑_p (log(1 − 1/p) + 1/p)`. -/
theorem tendsto_sum_inv_prime_sub_log_log :
    Tendsto (fun x : ℝ => (∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ)) - Real.log (Real.log x))
      atTop (𝓝 (Real.eulerMascheroniConstant
        + ∑' n : ℕ, if n.Prime then Real.log (1 - 1 / n) + 1 / n else 0)) := by
  obtain ⟨B, K, hK0, hBK⟩ := MertensSecond.sum_inv_prime_explicit
  have hB := B_eq (B := B) hK0 hBK
  have hD : (∑' n : ℕ, if n.Prime then Real.log (1 - 1 / n) + 1 / n else 0) = -∑' n, dd 1 n := by
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [dd_one]; split_ifs <;> ring
  rw [hD, ← sub_eq_add_neg, ← hB]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK : Tendsto (fun x : ℝ => K / Real.log x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul K
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [eventually_ge_atTop 2] with x hx
  exact hBK x hx

/-- **Mertens' third theorem**: `∏_{p ≤ x} (1 − 1/p)⁻¹ / log x → e^γ`. -/
theorem tendsto_prod_div_log :
    Tendsto (fun x : ℝ => (∏ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹) / Real.log x)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  obtain ⟨B, K, hK0, hBK⟩ := MertensSecond.sum_inv_prime_explicit
  have hB := B_eq (B := B) hK0 hBK
  have hM := tendsto_sum_inv_prime_sub_log_log
  have hD : (∑' n : ℕ, if n.Prime then Real.log (1 - 1 / n) + 1 / n else 0) = -∑' n, dd 1 n := by
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [dd_one]; split_ifs <;> ring
  rw [hD] at hM
  have hpart : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, dd 1 n) atTop (𝓝 (∑' n, dd 1 n)) := by
    have h0 := (summable_dd le_rfl).hasSum.tendsto_sum_nat
    have h1 := h0.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
    refine h1.congr fun x => ?_
    simp [Function.comp, Nat.range_succ_eq_Icc_zero]
  have hsum := hM.add hpart
  rw [show Real.eulerMascheroniConstant + -∑' n, dd 1 n + ∑' n, dd 1 n
    = Real.eulerMascheroniConstant by ring] at hsum
  refine ((Real.continuous_exp.tendsto _).comp hsum).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hfac : ∀ p ∈ Finset.filter (fun p => p.Prime) (Finset.Icc 0 ⌊x⌋₊), 0 < (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have : 0 < 1 - 1 / (p : ℝ) := by linarith
    positivity
  have hprod := Finset.prod_pos hfac
  have hlog : Real.log (∏ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹)
      = (∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ)) + ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, dd 1 n := by
    have hdd : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, dd 1 n
        = ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (-Real.log (1 - 1 / (p : ℝ)) - 1 / p) := by
      simp only [dd_one]; rw [Finset.sum_filter]
    rw [Real.log_prod fun p hp => (hfac p hp).ne', hdd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_inv]; ring
  simp only [Function.comp]
  rw [show ∀ a b c : ℝ, a - b + c = (a + c) - b from fun a b c => by ring, ← hlog, Real.exp_sub,
    Real.exp_log hprod, Real.exp_log hlx]

end LeanClassics.MertensThird
end
end

-- Erdos50FC.AtE
section
/-
# Erdős #50 at the points `φ(m)/m` (rung R1)

For every `f` with `IsDistributionOfPhiRatio f` (formal-conjectures' wording) and every `m ≥ 1`, `f` has no
derivative at all, within `Icc 0 1`, at `t = φ(m)/m`. So the open statement `Erdos50.erdos_50` holds at every point
of `E = {φ(n)/n}`, including `t = 1`.

This is known mathematics (Erdős 1946, Thm 3, for `t = 1`; Toulmonde, Acta Arith. 121 (2006), for all of `E`, with
the exact asymptotic); the point here is the machine-checked version.

Proof (the "spike" to the left of `t`). Put `P = ∏_{p ≤ Y} p` with `Y ≥ m`. The integers `n = m·k` with
`1 ≤ k ≤ (N − 1)/m`, `k` coprime to `P`, `k ≥ 2` and `φ(k) ≥ (1 − ε)k` satisfy `t(1 − ε)n ≤ φ(n) < tn`.
Coprimality to `P` has density `ρ = φ(P)/P = ∏_{p ≤ Y}(1 − 1/p)`, and Markov's inequality on
`1 − φ(k)/k ≤ ∑_{p ∣ k} 1/p` (every such `p > Y`) removes at most a proportion `2/(εY)`. Hence
`f(t) − f(t(1 − ε)) ≥ (ρ − 2/(εY))/m`. With `Y ≈ ε⁻²` and Mertens' third theorem, `ρ ≫ 1/log(1/ε)`, so the
left difference quotient is `≫ 1/(ε log(1/ε)) → ∞`, which no derivative allows.
-/

open Filter Finset Real Topology
open scoped Nat

noncomputable section

namespace Erdos50
namespace AtE

/- ### Elementary inequalities -/

lemma one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hP0 : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hP1 : ∏ i ∈ s, (1 - a i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => by linarith [h1 i (mem_insert_of_mem hi)])
        (fun i hi => by linarith [h0 i (mem_insert_of_mem hi)])
    have ha0 := h0 j (mem_insert_self j s)
    have ha1 := h1 j (mem_insert_self j s)
    nlinarith

/-- `φ(k) = k ∏_{p ∣ k} (1 − 1/p)` over `ℝ`. -/
lemma totient_eq_mul_prod (k : ℕ) :
    (φ k : ℝ) = k * ∏ p ∈ k.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors k)
  simpa [one_div] using h

/-- `k − φ(k) ≤ k ∑_{p ∣ k} 1/p`. -/
lemma sub_totient_le (k : ℕ) :
    (k : ℝ) - φ k ≤ k * ∑ p ∈ k.primeFactors, 1 / (p : ℝ) := by
  rw [totient_eq_mul_prod]
  have h := one_sub_sum_le_prod k.primeFactors (fun p => 1 / (p : ℝ))
    (fun p _ => by positivity)
    (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).one_lt
      rw [div_le_one (by positivity)]
      exact_mod_cast this.le)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/- ### Partial densities as finset counts -/

lemma partialDensity_eq (T : Set ℕ) [DecidablePred (· ∈ T)] (N : ℕ) :
    T.partialDensity Set.univ N = (((Finset.range N).filter (· ∈ T)).card : ℝ) / N := by
  have h1 : (T ∩ Set.univ) ∩ Set.Iio N = ↑((Finset.range N).filter (· ∈ T)) := by
    ext n; simp [and_comm]
  have h2 : (Set.univ ∩ Set.Iio N : Set ℕ) = ↑(Finset.range N) := by
    ext n; simp
  simp only [Set.partialDensity, h1, h2, Set.ncard_coe_finset, Finset.card_range]

/- ### The primorial-type product `P_Y = ∏_{p ≤ Y} p` -/

/-- Primes up to `Y`, as the filter used in `LeanClassics.MertensThird`. -/
def primesTo (Y : ℕ) : Finset ℕ := (Finset.Icc 0 Y).filter Nat.Prime

/-- `P_Y = ∏_{p ≤ Y} p`. -/
def bigP (Y : ℕ) : ℕ := ∏ p ∈ primesTo Y, p

/-- `ρ_Y = ∏_{p ≤ Y} (1 − 1/p)`. -/
def rho (Y : ℕ) : ℝ := ∏ p ∈ primesTo Y, (1 - 1 / (p : ℝ))

lemma bigP_pos (Y : ℕ) : 0 < bigP Y :=
  Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

lemma primeFactors_bigP (Y : ℕ) : (bigP Y).primeFactors = primesTo Y :=
  Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2

lemma totient_bigP (Y : ℕ) : (φ (bigP Y) : ℝ) = bigP Y * rho Y := by
  rw [totient_eq_mul_prod, primeFactors_bigP, rho]

lemma rho_nonneg (Y : ℕ) : 0 ≤ rho Y :=
  Finset.prod_nonneg fun p hp => by
    have := (Finset.mem_filter.mp hp).2.one_lt
    have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast this.le
    linarith

lemma rho_le_one (Y : ℕ) : rho Y ≤ 1 :=
  Finset.prod_le_one (fun p hp => by
      have := (Finset.mem_filter.mp hp).2.one_lt
      have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast this.le
      linarith)
    (fun p _ => by have : (0 : ℝ) ≤ 1 / p := by positivity
                   linarith)

lemma prime_dvd_bigP {p Y : ℕ} (hp : p.Prime) (hpY : p ≤ Y) : p ∣ bigP Y :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hpY⟩, hp⟩)

/-- A prime factor of `k` coprime to `P_Y` exceeds `Y`. -/
lemma lt_of_mem_primeFactors {Y k p : ℕ} (hk : (bigP Y).Coprime k) (hp : p ∈ k.primeFactors) :
    Y < p := by
  by_contra h
  push_neg at h
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h1 : p ∣ Nat.gcd (bigP Y) k :=
    Nat.dvd_gcd (prime_dvd_bigP hpp h) (Nat.dvd_of_mem_primeFactors hp)
  rw [hk] at h1
  exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)

/- ### Counting integers coprime to `P` -/

lemma card_coprime_Ico (P q : ℕ) :
    ((Finset.Ico 1 (1 + q * P)).filter (P.Coprime ·)).card = q * φ P := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Finset.Ico 1 (1 + (q + 1) * P) =
        Finset.Ico 1 (1 + q * P) ∪ Finset.Ico (1 + q * P) (1 + q * P + P) := by
      rw [show 1 + (q + 1) * P = 1 + q * P + P by ring]
      exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)), ih,
      Nat.filter_coprime_Ico_eq_totient]
    ring

/-- At least `⌊M/P⌋ φ(P)` integers in `(0, M]` are coprime to `P`. -/
lemma card_coprime_Ioc_ge (P M : ℕ) (hP : 0 < P) :
    (M / P) * φ P ≤ ((Finset.Ioc 0 M).filter (P.Coprime ·)).card := by
  rw [← card_coprime_Ico]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [Finset.mem_Ioc]
  have := Nat.div_mul_le_self M P
  omega

/- ### Markov's inequality for the bad `k` -/

/-- `∑_{k ≤ M, (k,P_Y)=1} ∑_{p ∣ k} 1/p ≤ 2M/Y`. -/
lemma sum_sum_inv_le (Y M : ℕ) (hY : 1 ≤ Y) :
    ∑ k ∈ (Finset.Ioc 0 M).filter ((bigP Y).Coprime ·), ∑ p ∈ k.primeFactors, 1 / (p : ℝ) ≤
      2 * M / Y := by
  set A := (Finset.Ioc 0 M).filter ((bigP Y).Coprime ·)
  set T := (Finset.Ioc Y M).filter Nat.Prime
  -- each inner sum is dominated by a sum over `T` with a divisibility indicator
  have hstep : ∀ k ∈ A, ∑ p ∈ k.primeFactors, 1 / (p : ℝ) ≤
      ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkM : k ≤ M := (Finset.mem_Ioc.mp hk'.1).2
    have hsub : k.primeFactors ⊆ T := by
      intro p hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_mem_primeFactors hk'.2 hp, ?_⟩,
        Nat.prime_of_mem_primeFactors hp⟩
      exact (Nat.le_of_mem_primeFactors hp).trans hkM
    calc ∑ p ∈ k.primeFactors, 1 / (p : ℝ)
        = ∑ p ∈ k.primeFactors, (if p ∣ k then 1 / (p : ℝ) else 0) :=
          Finset.sum_congr rfl fun p hp => by rw [if_pos (Nat.dvd_of_mem_primeFactors hp)]
      _ ≤ ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  calc ∑ k ∈ A, ∑ p ∈ k.primeFactors, 1 / (p : ℝ)
      ≤ ∑ k ∈ A, ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) := Finset.sum_le_sum hstep
    _ = ∑ p ∈ T, ∑ k ∈ A, (if p ∣ k then 1 / (p : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ T, (M : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p := by
          exact_mod_cast (Finset.mem_filter.mp hp).2.pos
        rw [← Finset.sum_filter]
        have hcard : ((A.filter (p ∣ ·)).card : ℝ) ≤ (M : ℝ) / p := by
          have h1 : (A.filter (p ∣ ·)).card ≤ ((Finset.Ioc 0 M).filter (p ∣ ·)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
          rw [Nat.Ioc_filter_dvd_card_eq_div] at h1
          calc ((A.filter (p ∣ ·)).card : ℝ) ≤ ((M / p : ℕ) : ℝ) := by exact_mod_cast h1
            _ ≤ (M : ℝ) / p := Nat.cast_div_le
        rw [Finset.sum_const, nsmul_eq_mul]
        calc ((A.filter (p ∣ ·)).card : ℝ) * (1 / (p : ℝ))
            ≤ (M : ℝ) / p * (1 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = (M : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by field_simp
    _ = (M : ℝ) * ∑ p ∈ T, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ∑ i ∈ Finset.Ioo Y (M + 1), ((i : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Ioo.mpr ⟨this.1, by omega⟩
        · intro i _ _; positivity
    _ ≤ (M : ℝ) * (2 / (Y + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le Y (M + 1)) (Nat.cast_nonneg M)
    _ ≤ 2 * M / Y := by
        have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hY0]
        nlinarith [Nat.cast_nonneg (α := ℝ) M]

/-- The bad `k` (coprime to `P_Y` but `φ(k) < (1 − ε)k`) number at most `2M/(εY)`. -/
lemma card_bad_le (Y M : ℕ) (hY : 1 ≤ Y) {ε : ℝ} (hε : 0 < ε) :
    ε * (((Finset.Ioc 0 M).filter ((bigP Y).Coprime ·)).filter
      (fun k => (φ k : ℝ) < (1 - ε) * k)).card ≤ 2 * M / Y := by
  set A := (Finset.Ioc 0 M).filter ((bigP Y).Coprime ·)
  set B := A.filter (fun k => (φ k : ℝ) < (1 - ε) * k)
  have hB : ∀ k ∈ B, ε ≤ ∑ p ∈ k.primeFactors, 1 / (p : ℝ) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hk0 : (0 : ℝ) < k := by
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk'.1).1).1
    have h1 := sub_totient_le k
    have h2 := hk'.2
    by_contra hlt
    push_neg at hlt
    have : (k : ℝ) * ∑ p ∈ k.primeFactors, 1 / (p : ℝ) < k * ε := mul_lt_mul_of_pos_left hlt hk0
    nlinarith
  calc ε * (B.card : ℝ) = ∑ k ∈ B, ε := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ B, ∑ p ∈ k.primeFactors, 1 / (p : ℝ) := Finset.sum_le_sum hB
    _ ≤ ∑ k ∈ A, ∑ p ∈ k.primeFactors, 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => Finset.sum_nonneg fun p _ => by positivity
    _ ≤ 2 * M / Y := sum_sum_inv_le Y M hY

/- ### The spike to the left of `t = φ(m)/m` -/

/-- The good `k`. -/
def goodK (m N Y : ℕ) (ε : ℝ) : Finset ℕ :=
  (((Finset.Ioc 0 ((N - 1) / m)).filter ((bigP Y).Coprime ·)).filter
    (fun k => ¬ (φ k : ℝ) < (1 - ε) * k)).filter (fun k => k ≠ 1)

lemma card_goodK_ge (m N Y : ℕ) (hm : 0 < m) (hY : 1 ≤ Y) {ε : ℝ} (hε : 0 < ε)
    (ha : 2 / (ε * Y) ≤ rho Y) (hN : 1 ≤ N) :
    (N : ℝ) / m * (rho Y - 2 / (ε * Y)) - (bigP Y + 3) ≤ (goodK m N Y ε).card := by
  set M := (N - 1) / m
  set P := bigP Y
  set A := (Finset.Ioc 0 M).filter (P.Coprime ·)
  set B := A.filter (fun k => (φ k : ℝ) < (1 - ε) * k)
  set G := A.filter (fun k => ¬ (φ k : ℝ) < (1 - ε) * k)
  have hP : 0 < P := bigP_pos Y
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  -- |A| = |G| + |B|
  have hAGB : (A.card : ℝ) = G.card + B.card := by
    have := Finset.card_filter_add_card_filter_not (s := A)
      (fun k => (φ k : ℝ) < (1 - ε) * k)
    have h' : B.card + G.card = A.card := this
    rw [← h']; push_cast; ring
  -- |goodK| ≥ |G| − 1
  have hgood : (G.card : ℝ) - 1 ≤ (goodK m N Y ε).card := by
    have h := Finset.card_filter_add_card_filter_not (s := G) (fun k => k ≠ 1)
    have h1 : (G.filter (fun k => ¬ k ≠ 1)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, not_not] at ha hb
      rw [ha.2, hb.2]
    have h2 : (goodK m N Y ε) = G.filter (fun k => k ≠ 1) := rfl
    rw [h2]
    have : (G.card : ℝ) = (G.filter (fun k => k ≠ 1)).card + (G.filter (fun k => ¬ k ≠ 1)).card := by
      exact_mod_cast h.symm
    have h1' : ((G.filter (fun k => ¬ k ≠ 1)).card : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  -- |A| ≥ ⌊M/P⌋ φ(P) ≥ M ρ − P
  have hA : (M : ℝ) * rho Y - P ≤ A.card := by
    have h := card_coprime_Ioc_ge P M hP
    have h' : (((M / P : ℕ) : ℝ) * (φ P : ℝ)) ≤ A.card := by exact_mod_cast h
    rw [show (φ P : ℝ) = P * rho Y from totient_bigP Y] at h'
    have hq : (M : ℝ) / P - 1 ≤ ((M / P : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := M) hP
      rw [div_sub_one hPr.ne', div_le_iff₀ hPr]
      have : (M : ℝ) < ((M / P : ℕ) : ℝ) * P + P := by exact_mod_cast this
      linarith
    have hr0 := rho_nonneg Y
    have hr1 := rho_le_one Y
    have : ((M : ℝ) / P - 1) * (P * rho Y) ≤ ((M / P : ℕ) : ℝ) * (P * rho Y) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    have heq : ((M : ℝ) / P - 1) * (P * rho Y) = M * rho Y - P * rho Y := by
      field_simp
    nlinarith
  -- |B| ≤ 2M/(εY)
  have hB : (B.card : ℝ) ≤ 2 * M / Y / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact card_bad_le Y M hY hε
  -- bounds on M
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hM1 : (N : ℝ) / m - 2 ≤ M := by
    have h := Nat.lt_div_mul_add (a := N - 1) hm
    have h' : ((N - 1 : ℕ) : ℝ) < (M : ℝ) * m + m := by exact_mod_cast h
    rw [Nat.cast_sub hN] at h'
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_sub' hm'.ne', div_le_iff₀ hm']
    push_cast at h'
    nlinarith
  have hM2 : (M : ℝ) ≤ N / m := by
    rw [le_div_iff₀ hm']
    have : M * m ≤ N := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    exact_mod_cast this
  -- assemble
  set a := rho Y - 2 / (ε * Y)
  have ha0 : 0 ≤ a := by simp only [a]; linarith
  have hBa : (B.card : ℝ) ≤ M * (2 / (ε * Y)) := by
    calc (B.card : ℝ) ≤ 2 * M / Y / ε := hB
      _ = M * (2 / (ε * Y)) := by field_simp
  have hr1 := rho_le_one Y
  have key : (M : ℝ) * a - P - 1 ≤ (goodK m N Y ε).card := by
    simp only [a]; nlinarith
  have h2p : (0 : ℝ) ≤ 2 / (ε * Y) := by positivity
  have ha1 : a ≤ 1 := by simp only [a]; linarith
  have : (N : ℝ) / m * a - 2 ≤ M * a := by
    have h := mul_le_mul_of_nonneg_right hM1 ha0
    have h' : (N / m - 2 : ℝ) * a = N / m * a - 2 * a := by ring
    rw [h'] at h
    linarith
  linarith

/-- **The spike**: `f(t) − f(t(1 − ε)) ≥ (ρ_Y − 2/(εY))/m` at `t = φ(m)/m`, for `Y ≥ m`. -/
theorem spike (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {Y : ℕ} (hmY : m ≤ Y) (hY : 1 ≤ Y)
    (ha : 2 / (ε * Y) ≤ rho Y) :
    (rho Y - 2 / (ε * Y)) / m ≤ f ((φ m : ℝ) / m) - f ((φ m : ℝ) / m * (1 - ε)) := by
  classical
  set t : ℝ := (φ m : ℝ) / m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hφm : (0 : ℝ) < φ m := by exact_mod_cast Nat.totient_pos.mpr hm
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [div_le_one hm']; exact_mod_cast Nat.totient_le m
  have hc1 : t * (1 - ε) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht0 (by linarith), by nlinarith⟩
  have hc2 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have h1 := hf _ hc1
  have h2 := hf _ hc2
  set S1 : Set ℕ := {n : ℕ | (φ n : ℝ) < t * (1 - ε) * n}
  set S2 : Set ℕ := {n : ℕ | (φ n : ℝ) < t * n}
  have hdiff : Tendsto (fun N : ℕ => S2.partialDensity Set.univ N - S1.partialDensity Set.univ N)
      atTop (𝓝 (f t - f (t * (1 - ε)))) := h2.sub h1
  set a := rho Y - 2 / (ε * Y)
  -- the lower bound at each `N ≥ 1`
  have hlow : ∀ N : ℕ, 1 ≤ N → a / m - (bigP Y + 3) / N ≤
      S2.partialDensity Set.univ N - S1.partialDensity Set.univ N := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [partialDensity_eq, partialDensity_eq, ← sub_div]
    -- counting: filter S2 ⊇ filter S1 ∪ image of goodK, disjointly
    set F1 := (Finset.range N).filter (· ∈ S1)
    set F2 := (Finset.range N).filter (· ∈ S2)
    set C := (goodK m N Y ε).image (m * ·)
    have hCcard : C.card = (goodK m N Y ε).card :=
      Finset.card_image_of_injective _ fun x y h => Nat.eq_of_mul_eq_mul_left hm h
    have hmem : ∀ k ∈ goodK m N Y ε, m * k < N ∧ m * k ∈ S2 ∧ m * k ∉ S1 := by
      intro k hk
      simp only [goodK, Finset.mem_filter, Finset.mem_Ioc] at hk
      obtain ⟨⟨⟨⟨hk0, hkM⟩, hcop⟩, hgood⟩, hk1⟩ := hk
      have hk2 : 1 < k := by omega
      have hcopmk : m.Coprime k := by
        apply Nat.coprime_of_dvd
        intro p hp hpm hpk
        have hpY : p ≤ Y := (Nat.le_of_dvd hm hpm).trans hmY
        have h1 : p ∣ Nat.gcd (bigP Y) k := Nat.dvd_gcd (prime_dvd_bigP hp hpY) hpk
        rw [hcop] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hφ : (φ (m * k) : ℝ) = φ m * φ k := by
        rw [Nat.totient_mul hcopmk]; push_cast; ring
      have hφk : (φ k : ℝ) < k := by exact_mod_cast Nat.totient_lt k hk2
      have htm : t * ((m * k : ℕ) : ℝ) = φ m * k := by
        simp only [t]; push_cast; field_simp
      refine ⟨?_, ?_, ?_⟩
      · have : m * k ≤ m * ((N - 1) / m) := Nat.mul_le_mul_left m hkM
        have := Nat.mul_div_le (N - 1) m
        omega
      · show (φ (m * k) : ℝ) < t * ((m * k : ℕ) : ℝ)
        rw [hφ, htm]
        exact mul_lt_mul_of_pos_left hφk hφm
      · show ¬ (φ (m * k) : ℝ) < t * (1 - ε) * ((m * k : ℕ) : ℝ)
        rw [hφ, mul_assoc, mul_comm (1 - ε), ← mul_assoc, htm]
        push_neg at hgood ⊢
        nlinarith
    have hdisj : Disjoint F1 C := by
      rw [Finset.disjoint_left]
      intro n hn1 hnC
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hnC
      exact (hmem k hk).2.2 (Finset.mem_filter.mp hn1).2
    have hsub : F1 ∪ C ⊆ F2 := by
      intro n hn
      rcases Finset.mem_union.mp hn with h | h
      · have h' := Finset.mem_filter.mp h
        refine Finset.mem_filter.mpr ⟨h'.1, ?_⟩
        have hS : (φ n : ℝ) < t * (1 - ε) * n := h'.2
        show (φ n : ℝ) < t * n
        have : t * (1 - ε) * n ≤ t * n := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        linarith
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hmem k hk).1, (hmem k hk).2.1⟩
    have hcount : (F1.card : ℝ) + (goodK m N Y ε).card ≤ F2.card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hCcard] at this
      exact_mod_cast this
    have hK := card_goodK_ge m N Y hm hY hε0 ha hN
    rw [le_div_iff₀ hNr]
    have : (a / m - (bigP Y + 3) / N) * N = N / m * a - (bigP Y + 3) := by
      field_simp
    rw [this]
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun N : ℕ => a / m - (bigP Y + 3) / (N : ℝ)) atTop (𝓝 (a / m)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat ((bigP Y : ℝ) + 3)).const_sub (a / m)
    simpa using this
  exact le_of_tendsto_of_tendsto hlim hdiff (Filter.eventually_atTop.mpr ⟨1, hlow⟩)

end AtE
end Erdos50

end
end

-- Erdos50FC.Main
section
/-
# Erdős #50 holds at every point of `E = {φ(m)/m}` (rung R1)

`Erdos50.AtE.no_deriv_at_totient_ratio`: for every `f` with `IsDistributionOfPhiRatio f` and every `m ≥ 1`,
there is no `y` (positive or not) with `HasDerivWithinAt f y (Icc 0 1) (φ m / m)`.

`Erdos50.AtE.erdos_50_on_E` restates it in the shape of formal-conjectures' open `erdos_50`, restricted to
`x ∈ E`.
-/

open Filter Set Finset Real Topology
open scoped Nat

namespace Erdos50
namespace AtE

/-- Mertens' third theorem in the form used here: eventually `∏_{p ≤ x} (1 − 1/p) ≥ 1/(C log x)`. -/
lemma eventually_rho_ge :
    ∀ᶠ x : ℝ in atTop, 1 / ((Real.exp Real.eulerMascheroniConstant + 1) * Real.log x) ≤
      rho ⌊x⌋₊ := by
  have hM := LeanClassics.MertensThird.tendsto_prod_div_log
  have h1 := hM.eventually (gt_mem_nhds (lt_add_one (Real.exp Real.eulerMascheroniConstant)))
  filter_upwards [h1, eventually_gt_atTop (Real.exp 1)] with x hx hxe
  have hlog : 0 < Real.log x := Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  set Q := ∏ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹
  have hQ0 : 0 < Q := Finset.prod_pos fun p hp => by
    have := (Finset.mem_filter.mp hp).2.one_lt
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast this
    exact inv_pos.mpr (by linarith)
  have hrho : rho ⌊x⌋₊ = Q⁻¹ := by
    rw [rho, primesTo, ← Finset.prod_inv_distrib]
    simp only [inv_inv]
  rw [hrho, one_div]
  apply inv_anti₀ hQ0
  rw [div_lt_iff₀ hlog] at hx
  linarith

/-- **R1.** `f` has no derivative within `Icc 0 1` at any `t = φ(m)/m`, `m ≥ 1`. -/
theorem no_deriv_at_totient_ratio (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {m : ℕ} (hm : 0 < m) :
    ¬ ∃ y : ℝ, HasDerivWithinAt f y (Set.Icc 0 1) ((φ m : ℝ) / m) := by
  rintro ⟨y, hy⟩
  set t : ℝ := (φ m : ℝ) / m with ht_def
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one hm']; exact_mod_cast Nat.totient_le m
  set Cm := Real.exp Real.eulerMascheroniConstant + 1 with hCm
  have hCm0 : 0 < Cm := by positivity
  set B := 2 * Cm * (m * (|y| + 1) + 4) with hB
  have hB0 : 0 < B := by positivity
  -- (1) the derivative bounds the left increment: f t − f(t(1 − ε)) ≤ ε(|y| + 1)
  have hderiv : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f t - f (t * (1 - ε)) ≤ ε * (|y| + 1) := by
    have ho := (hasDerivWithinAt_iff_isLittleO.mp hy).def (zero_lt_one' ℝ)
    have hmap : Tendsto (fun ε : ℝ => t * (1 - ε)) (𝓝[>] 0) (𝓝[Set.Icc 0 1] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun ε : ℝ => t * (1 - ε)) (𝓝 0) (𝓝 (t * (1 - 0))) :=
          (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        exact ⟨mul_nonneg ht0 (by linarith [hε.2]), by nlinarith [hε.1, hε.2]⟩
    filter_upwards [hmap.eventually ho, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε hε01
    simp only [one_mul, Real.norm_eq_abs, smul_eq_mul] at hε
    have hd : t * (1 - ε) - t = -(t * ε) := by ring
    rw [hd, abs_neg, abs_of_nonneg (mul_nonneg ht0 hε01.1.le)] at hε
    have h1 := (abs_le.mp hε).1
    have h2 : t * ε * y ≤ t * ε * |y| :=
      mul_le_mul_of_nonneg_left (le_abs_self y) (mul_nonneg ht0 hε01.1.le)
    have h3 : t * ε * (|y| + 1) ≤ ε * (|y| + 1) := by
      have hprod : 0 ≤ ε * (|y| + 1) * (1 - t) :=
        mul_nonneg (mul_nonneg hε01.1.le (by positivity)) (sub_nonneg.mpr ht1)
      nlinarith [hprod]
    have h1' : f t - f (t * (1 - ε)) ≤ t * ε + t * ε * y := by
      have : f (t * (1 - ε)) - f t - -(t * ε) * y = f (t * (1 - ε)) - f t + t * ε * y := by ring
      rw [this] at h1
      linarith
    nlinarith
  -- (2) ε log(1/ε) → 0
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Real.log ε⁻¹ * B < 1 := by
    have hc : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have := Real.continuous_mul_log.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have : Tendsto (fun ε : ℝ => ε * Real.log ε⁻¹ * B) (𝓝[>] 0) (𝓝 0) := by
      have h := (hc.neg).mul_const B
      simp only [neg_zero, zero_mul] at h
      refine h.congr fun ε => ?_
      rw [Real.log_inv]; ring
    exact this.eventually (gt_mem_nhds one_pos)
  -- (3) x = ε⁻² → ∞
  have hx : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hmert := hx.eventually eventually_rho_ge
  have hbig := hx.eventually (eventually_ge_atTop ((m : ℝ) + 2))
  -- combine and pick one ε
  obtain ⟨ε, hdε, hgε, hmε, hbε, hε01⟩ :=
    (hderiv.and (hg.and (hmert.and (hbig.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)))))).exists
  set x := ε⁻¹ ^ 2 with hxdef
  set Y := ⌊x⌋₊
  have hε0 := hε01.1
  have hε1 := hε01.2
  have hx2 : 2 ≤ x := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hYx : x - 1 ≤ (Y : ℝ) := by
    have := Nat.lt_floor_add_one x; linarith
  have hmY : m ≤ Y := by
    apply Nat.le_floor
    linarith
  have hY1 : 1 ≤ Y := by
    apply Nat.le_floor; push_cast; linarith
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hεx : ε * x = ε⁻¹ := by
    simp only [hxdef]; field_simp
  -- 2/(εY) ≤ 4ε
  have hsmall : 2 / (ε * Y) ≤ 4 * ε := by
    rw [div_le_iff₀ (by positivity)]
    have hY2 : x / 2 ≤ (Y : ℝ) := by linarith
    have : ε * (x / 2) ≤ ε * Y := mul_le_mul_of_nonneg_left hY2 hε0.le
    have hεx' : ε * ε * x = 1 := by
      rw [mul_assoc, hεx, mul_inv_cancel₀ hε0.ne']
    nlinarith
  -- log x = 2 log ε⁻¹ > 0
  have hL : Real.log x = 2 * Real.log ε⁻¹ := by
    simp only [hxdef]; rw [Real.log_pow]; push_cast; ring
  have hL0 : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hε0, hε1⟩)
  have hρ : 1 / (Cm * (2 * Real.log ε⁻¹)) ≤ rho Y := by
    rw [← hL]; exact hmε
  have hρ' : 1 ≤ rho Y * (2 * Cm * Real.log ε⁻¹) := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  -- the spike hypothesis 2/(εY) ≤ ρ
  have hg' : ε * Real.log ε⁻¹ * (8 * Cm) < 1 := by
    have : 8 * Cm ≤ B := by
      simp only [hB]
      have : (0 : ℝ) ≤ m * (|y| + 1) := by positivity
      nlinarith
    have hpos : 0 ≤ ε * Real.log ε⁻¹ := by positivity
    nlinarith
  have ha : 2 / (ε * Y) ≤ rho Y := by
    refine hsmall.trans ?_
    -- 4ε ≤ ρ since 4ε · 2 Cm log ε⁻¹ < 1 ≤ ρ · 2 Cm log ε⁻¹
    have hK : 0 < 2 * Cm * Real.log ε⁻¹ := by positivity
    by_contra hlt
    push_neg at hlt
    have : rho Y * (2 * Cm * Real.log ε⁻¹) < 4 * ε * (2 * Cm * Real.log ε⁻¹) :=
      mul_lt_mul_of_pos_right hlt hK
    nlinarith
  -- the spike
  have hsp := spike f hf hm hε0 hε1.le hmY hY1 ha
  -- contradiction
  have hchain : rho Y ≤ m * (ε * (|y| + 1)) + 4 * ε := by
    have h := hsp.trans hdε
    rw [div_le_iff₀ hm'] at h
    nlinarith
  have hK : 0 < 2 * Cm * Real.log ε⁻¹ := by positivity
  have : 1 ≤ (m * (ε * (|y| + 1)) + 4 * ε) * (2 * Cm * Real.log ε⁻¹) :=
    hρ'.trans (mul_le_mul_of_nonneg_right hchain hK.le)
  have heq : (m * (ε * (|y| + 1)) + 4 * ε) * (2 * Cm * Real.log ε⁻¹) = ε * Real.log ε⁻¹ * B := by
    simp only [hB]; ring
  linarith

/-- **R1, in the shape of formal-conjectures' `erdos_50`**, for `x` in `E = {φ(m)/m : m ≥ 1}`. -/
theorem erdos_50_on_E : ∀ᵉ (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f),
    ¬∃ x ∈ Set.Icc (0 : ℝ) 1, (∃ m : ℕ, 0 < m ∧ x = (φ m : ℝ) / m) ∧
      ∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x := by
  intro f hf
  rintro ⟨x, -, ⟨m, hm, rfl⟩, y, -, hy⟩
  exact no_deriv_at_totient_ratio f hf hm ⟨y, hy⟩

end AtE
end Erdos50
end

-- Erdos50FC.Residual
section
/-
# Erdős #50 on a residual set (rung R3)

For every `f` with `IsDistributionOfPhiRatio f` (formal-conjectures' wording), the points `x ∈ [0,1]` at which the
upper right Dini derivative of `f` is `+∞` contain `G ∩ [0,1]` for a dense `G_δ` set `G ⊆ ℝ`: precisely, *residually
many* real `x` (`∀ᶠ x in residual ℝ`) satisfy
`x ∈ Icc 0 1 → ∀ M, ∃ t ∈ Icc 0 1, x < t < x + 1/(M+1), (f t − f x)/(t − x) > M`.
At such `x`, `f` has no derivative within `Icc 0 1` (of any value). So formal-conjectures' open `erdos_50` holds on a
comeagre subset of `[0,1]`.

Published incumbents say "dense set" (Erdős 1974, remark) and "dense continuum" (erdosproblemaday report, 2026-07-27,
unrefereed); comeagre is stronger, but routine for a monotone function with a dense set of one-sided infinite spikes,
so this is folklore-level made explicit, not new mathematics. It says nothing about Lebesgue measure: the trace of
the set on `[0,1]` is Lebesgue-null (`f` is monotone, so it has a finite derivative a.e.), and the open problem lives
on its complement.

Proof.
1. (`eventually_left_gt`) At `t = φ(m)/m`, for every `K`, eventually as `ε → 0⁺`, `K ε < f t − f (t(1 − ε))`
   (the R1 spike with `Y = ⌊ε⁻²⌋` and Mertens).
2. (`exists_left_interval`) Hence every `x` in a left interval `(t − r, t)` has `(f t − f x)/(t − x) > M`.
3. (`totient_ratio_dense`) `E = {φ(m)/m}` is dense in `[0,1]`: walk down the partial products of `(1 − 1/p)` over
   primes `p ≥ P₀` (steps `≤ 1/P₀`; they reach any `b > 0` because `∑ 1/p = ∞`).
4. So `U_M = interior {x : good at level M} ∪ (Icc 0 1)ᶜ` is open and dense, and Baire (`residual ℝ` is closed
   under countable intersections) finishes.
-/

open Filter Set Finset Real Topology
open scoped Nat

noncomputable section

namespace Erdos50
namespace Residual

open AtE

/- ### 1. The left spike beats every line -/

/-- At `t = φ(m)/m`, for every `K`, eventually as `ε → 0⁺`, `K ε < f t − f(t(1 − ε))`. -/
theorem eventually_left_gt (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {m : ℕ} (hm : 0 < m) (K : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε < f ((φ m : ℝ) / m) - f ((φ m : ℝ) / m * (1 - ε)) := by
  set t : ℝ := (φ m : ℝ) / m with ht_def
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set Cm := Real.exp Real.eulerMascheroniConstant + 1 with hCm
  have hCm0 : 0 < Cm := by positivity
  set B := 2 * Cm * (m * (|K| + 1) + 4) with hB
  have hB0 : 0 < B := by positivity
  -- ε log(1/ε) → 0
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Real.log ε⁻¹ * B < 1 := by
    have hc : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have := Real.continuous_mul_log.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have : Tendsto (fun ε : ℝ => ε * Real.log ε⁻¹ * B) (𝓝[>] 0) (𝓝 0) := by
      have h := (hc.neg).mul_const B
      simp only [neg_zero, zero_mul] at h
      refine h.congr fun ε => ?_
      rw [Real.log_inv]; ring
    exact this.eventually (gt_mem_nhds one_pos)
  have hx : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hmert := hx.eventually eventually_rho_ge
  have hbig := hx.eventually (eventually_ge_atTop ((m : ℝ) + 2))
  filter_upwards [hg, hmert, hbig, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hgε hmε hbε hε01
  by_contra hle
  push_neg at hle
  have hε0 := hε01.1
  have hε1 := hε01.2
  have hdε : f t - f (t * (1 - ε)) ≤ ε * (|K| + 1) := by
    have : K * ε ≤ ε * (|K| + 1) := by
      have := le_abs_self K
      nlinarith
    linarith
  set x := ε⁻¹ ^ 2 with hxdef
  set Y := ⌊x⌋₊
  have hx2 : 2 ≤ x := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hYx : x - 1 ≤ (Y : ℝ) := by
    have := Nat.lt_floor_add_one x; linarith
  have hmY : m ≤ Y := by
    apply Nat.le_floor
    linarith
  have hY1 : 1 ≤ Y := by
    apply Nat.le_floor; push_cast; linarith
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hεx : ε * x = ε⁻¹ := by
    simp only [hxdef]; field_simp
  have hsmall : 2 / (ε * Y) ≤ 4 * ε := by
    rw [div_le_iff₀ (by positivity)]
    have hY2 : x / 2 ≤ (Y : ℝ) := by linarith
    have : ε * (x / 2) ≤ ε * Y := mul_le_mul_of_nonneg_left hY2 hε0.le
    have hεx' : ε * ε * x = 1 := by
      rw [mul_assoc, hεx, mul_inv_cancel₀ hε0.ne']
    nlinarith
  have hL : Real.log x = 2 * Real.log ε⁻¹ := by
    simp only [hxdef]; rw [Real.log_pow]; push_cast; ring
  have hL0 : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hε0, hε1⟩)
  have hρ : 1 / (Cm * (2 * Real.log ε⁻¹)) ≤ rho Y := by
    rw [← hL]; exact hmε
  have hρ' : 1 ≤ rho Y * (2 * Cm * Real.log ε⁻¹) := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  have hg' : ε * Real.log ε⁻¹ * (8 * Cm) < 1 := by
    have : 8 * Cm ≤ B := by
      simp only [hB]
      have : (0 : ℝ) ≤ m * (|K| + 1) := by positivity
      nlinarith
    have hpos : 0 ≤ ε * Real.log ε⁻¹ := by positivity
    nlinarith
  have ha : 2 / (ε * Y) ≤ rho Y := by
    refine hsmall.trans ?_
    have hK : 0 < 2 * Cm * Real.log ε⁻¹ := by positivity
    by_contra hlt
    push_neg at hlt
    have : rho Y * (2 * Cm * Real.log ε⁻¹) < 4 * ε * (2 * Cm * Real.log ε⁻¹) :=
      mul_lt_mul_of_pos_right hlt hK
    nlinarith
  have hsp := spike f hf hm hε0 hε1.le hmY hY1 ha
  have hchain : rho Y ≤ m * (ε * (|K| + 1)) + 4 * ε := by
    have h := hsp.trans hdε
    rw [div_le_iff₀ hm'] at h
    nlinarith
  have hK : 0 < 2 * Cm * Real.log ε⁻¹ := by positivity
  have : 1 ≤ (m * (ε * (|K| + 1)) + 4 * ε) * (2 * Cm * Real.log ε⁻¹) :=
    hρ'.trans (mul_le_mul_of_nonneg_right hchain hK.le)
  have heq : (m * (ε * (|K| + 1)) + 4 * ε) * (2 * Cm * Real.log ε⁻¹) = ε * Real.log ε⁻¹ * B := by
    simp only [hB]; ring
  linarith

/- ### 2. Good points at level `M` -/

/-- `x` is good at level `M`: some `t ∈ [0,1]` with `x < t < x + 1/(M+1)` has difference quotient `> M`. -/
def good (f : ℝ → ℝ) (M : ℕ) : Set ℝ :=
  {x | ∃ t ∈ Icc (0 : ℝ) 1, x < t ∧ t < x + 1 / ((M : ℝ) + 1) ∧ (M : ℝ) < (f t - f x) / (t - x)}

/-- A whole left interval of `t = φ(m)/m` is good at level `M`. -/
theorem exists_left_interval (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {m : ℕ} (hm : 0 < m) (M : ℕ) :
    ∃ r > 0, Ioo ((φ m : ℝ) / m - r) ((φ m : ℝ) / m) ⊆ good f M := by
  set t : ℝ := (φ m : ℝ) / m with ht_def
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hφm : (0 : ℝ) < φ m := by exact_mod_cast Nat.totient_pos.mpr hm
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one hm']; exact_mod_cast Nat.totient_le m
  have hev := eventually_left_gt f hf hm ((M : ℝ) * t)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0 : (0 : ℝ) < u := hu
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  refine ⟨min (t * u) (1 / ((M : ℝ) + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hr1 := min_le_left (t * u) (1 / ((M : ℝ) + 1))
  have hr2 := min_le_right (t * u) (1 / ((M : ℝ) + 1))
  set ε := (t - x) / t with hε
  have hε0 : 0 < ε := div_pos (by linarith) ht0
  have hεu : ε < u := by
    rw [hε, div_lt_iff₀ ht0]; linarith
  have hxε : t * (1 - ε) = x := by
    rw [hε]; field_simp; ring
  have hgt := hsub ⟨hε0, hεu⟩
  simp only [Set.mem_setOf_eq] at hgt
  rw [hxε] at hgt
  have htx : 0 < t - x := by linarith
  refine ⟨t, ⟨ht0.le, ht1⟩, hx2, by linarith, ?_⟩
  rw [lt_div_iff₀ htx]
  have : (M : ℝ) * t * ε = M * (t - x) := by
    rw [hε]; field_simp
  linarith

/- ### 3. `E = {φ(m)/m}` is dense in `[0,1]` -/

/-- Primes in `[P, L)`. -/
def primesIco (P L : ℕ) : Finset ℕ := (Finset.Ico P L).filter Nat.Prime

/-- `s(P, L) = ∏_{P ≤ p < L} (1 − 1/p)`. -/
def sprod (P L : ℕ) : ℝ := ∏ p ∈ primesIco P L, (1 - 1 / (p : ℝ))

lemma sprod_eq_totient (P L : ℕ) :
    sprod P L = (φ (∏ p ∈ primesIco P L, p) : ℝ) / (∏ p ∈ primesIco P L, p : ℕ) := by
  have hpos : 0 < ∏ p ∈ primesIco P L, p :=
    Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hpf : (∏ p ∈ primesIco P L, p).primeFactors = primesIco P L :=
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2
  rw [totient_eq_mul_prod, hpf, sprod]
  have : ((∏ p ∈ primesIco P L, p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

lemma sprod_self (P : ℕ) : sprod P P = 1 := by
  simp [sprod, primesIco]

lemma sprod_succ_ge (P L : ℕ) (hP : 1 ≤ P) (hPL : P ≤ L) :
    sprod P L - 1 / (P : ℝ) ≤ sprod P (L + 1) := by
  have h0 : 0 ≤ sprod P L := Finset.prod_nonneg fun p hp => by
    have := (Finset.mem_filter.mp hp).2.one_lt
    have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast this.le
    linarith
  have h1 : sprod P L ≤ 1 := Finset.prod_le_one (fun p hp => by
      have := (Finset.mem_filter.mp hp).2.one_lt
      have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast this.le
      linarith)
    (fun p _ => by have : (0 : ℝ) ≤ 1 / p := by positivity
                   linarith)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  by_cases hL : L.Prime
  · have hins : primesIco P (L + 1) = insert L (primesIco P L) := by
      ext q
      simp only [primesIco, Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hq : q = L
        · left; exact hq
        · right; exact ⟨⟨h1, by omega⟩, h3⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨hPL, by omega⟩, hL⟩
        · exact ⟨⟨h1, by omega⟩, h3⟩
    have hnot : L ∉ primesIco P L := by simp [primesIco]
    have hs : sprod P (L + 1) = (1 - 1 / (L : ℝ)) * sprod P L := by
      unfold sprod; rw [hins, Finset.prod_insert hnot]
    rw [hs]
    have hLP : (1 : ℝ) / L ≤ 1 / P := by
      apply one_div_le_one_div_of_le hP0; exact_mod_cast hPL
    have : (1 - 1 / (L : ℝ)) * sprod P L = sprod P L - 1 / L * sprod P L := by ring
    rw [this]
    have : 1 / (L : ℝ) * sprod P L ≤ 1 / L := by
      have : (0 : ℝ) ≤ 1 / L := by positivity
      nlinarith
    linarith
  · have heq : primesIco P (L + 1) = primesIco P L := by
      ext q
      simp only [primesIco, Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
        · exact h
        · exact absurd (h ▸ h3) hL
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    have hs : sprod P (L + 1) = sprod P L := by unfold sprod; rw [heq]
    rw [hs]
    have : (0 : ℝ) ≤ 1 / P := by positivity
    linarith

/-- The partial products over primes `≥ P` fall below every `b > 0` (`∑ 1/p = ∞`). -/
lemma exists_sprod_lt (P : ℕ) {b : ℝ} (hb : 0 < b) : ∃ L, P ≤ L ∧ sprod P L < b := by
  -- partial sums of 1/p over primes diverge
  have hns : ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n)) :=
    not_summable_one_div_on_primes
  have hT : Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L,
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => Set.indicator_nonneg (fun n _ => by positivity) n)).mp hns
  set C : ℝ := ∑ n ∈ Finset.range P, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n
  obtain ⟨L, hL⟩ := (hT.eventually (eventually_ge_atTop (C + Real.log b⁻¹ + 1))).and
    (eventually_ge_atTop P) |>.exists
  refine ⟨L, hL.2, ?_⟩
  -- ∑_{P ≤ p < L} 1/p ≥ log(1/b) + 1
  have hsplit : ∑ n ∈ Finset.range L, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n =
      C + ∑ p ∈ primesIco P L, 1 / (p : ℝ) := by
    rw [← Finset.sum_range_add_sum_Ico _ hL.2]
    congr 1
    rw [primesIco, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime <;> simp [Set.indicator, hn]
  have hS : Real.log b⁻¹ + 1 ≤ ∑ p ∈ primesIco P L, 1 / (p : ℝ) := by linarith [hL.1]
  -- ∏ (1 − 1/p) ≤ exp(−∑ 1/p)
  have hexp : sprod P L ≤ Real.exp (-∑ p ∈ primesIco P L, 1 / (p : ℝ)) := by
    rw [sprod, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have := (Finset.mem_filter.mp hp).2.one_lt
      have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast this.le
      linarith
    · intro p _
      have := Real.add_one_le_exp (-(1 / (p : ℝ)))
      linarith
  calc sprod P L ≤ Real.exp (-∑ p ∈ primesIco P L, 1 / (p : ℝ)) := hexp
    _ ≤ Real.exp (-(Real.log b⁻¹ + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ < Real.exp (-(Real.log b⁻¹)) := Real.exp_lt_exp.mpr (by linarith)
    _ = b := by rw [Real.log_inv, neg_neg, Real.exp_log hb]

/-- **`E = {φ(m)/m : m ≥ 1}` is dense in `[0,1]`.** -/
theorem totient_ratio_dense {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ a < (φ m : ℝ) / m ∧ (φ m : ℝ) / m < b := by
  classical
  have hb0 : 0 < b := by linarith
  -- a step size 1/P < b − a
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / (b - a))
  have hba : 0 < b - a := by linarith
  have hP1 : 1 ≤ P := by
    have h1 : (0 : ℝ) < 1 / (b - a) := by positivity
    have h2 : (0 : ℝ) < P := lt_trans h1 hP
    have h3 : 0 < P := by exact_mod_cast h2
    omega
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
  have hstep : 1 / (P : ℝ) < b - a := by
    rw [div_lt_iff₀ hP0]
    rw [div_lt_iff₀ (by linarith)] at hP
    linarith
  have hex : ∃ L, P ≤ L ∧ sprod P L < b := exists_sprod_lt P hb0
  let L := Nat.find hex
  have hLspec : P ≤ L ∧ sprod P L < b := Nat.find_spec hex
  have hLP : P < L := by
    rcases Nat.lt_or_eq_of_le hLspec.1 with h | h
    · exact h
    · exfalso
      have := hLspec.2
      rw [← h, sprod_self] at this
      linarith
  obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hprev : ¬ (P ≤ L' ∧ sprod P L' < b) := Nat.find_min hex (by omega)
  have hPL' : P ≤ L' := by omega
  have hge : b ≤ sprod P L' := by
    by_contra h; push_neg at h; exact hprev ⟨hPL', h⟩
  have hlow := sprod_succ_ge P L' hP1 hPL'
  rw [← hL'] at hlow
  refine ⟨∏ p ∈ primesIco P L, p, Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos, ?_, ?_⟩
  · rw [← sprod_eq_totient]; linarith
  · rw [← sprod_eq_totient]; exact hLspec.2

/- ### 4. Baire -/

/-- The open sets `U_M`. -/
def U (f : ℝ → ℝ) (M : ℕ) : Set ℝ := interior (good f M) ∪ (Icc (0 : ℝ) 1)ᶜ

lemma isOpen_U (f : ℝ → ℝ) (M : ℕ) : IsOpen (U f M) :=
  isOpen_interior.union isClosed_Icc.isOpen_compl

lemma dense_U (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) (M : ℕ) : Dense (U f M) := by
  rw [dense_iff_inter_open]
  rintro V hV ⟨x0, hx0⟩
  by_cases hx0I : x0 ∈ Icc (0 : ℝ) 1
  swap
  · exact ⟨x0, hx0, Or.inr hx0I⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x0 hx0
  set a := max 0 (x0 - r / 2)
  set b := min 1 (x0 + r / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have hb1 : b ≤ 1 := min_le_left _ _
  have hab : a < b := by
    simp only [a, b]
    rcases hx0I with ⟨h0, h1⟩
    rcases le_total 0 (x0 - r / 2) with h | h
    · rw [max_eq_right h]
      rcases le_total 1 (x0 + r / 2) with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith
    · rw [max_eq_left h]
      rcases le_total 1 (x0 + r / 2) with h' | h'
      · rw [min_eq_left h']; norm_num
      · rw [min_eq_right h']; linarith
  have hax : x0 - r / 2 ≤ a := le_max_right _ _
  have hbx : b ≤ x0 + r / 2 := min_le_right _ _
  obtain ⟨m, hm, hat, htb⟩ := totient_ratio_dense ha0 hab hb1
  set t : ℝ := (φ m : ℝ) / m
  obtain ⟨r', hr', hsub⟩ := exists_left_interval f hf hm M
  have hint : Ioo (t - r') t ⊆ interior (good f M) := interior_maximal hsub isOpen_Ioo
  set x := max (t - r' / 2) ((a + t) / 2)
  have hx1 : t - r' < x := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hx2 : x < t := max_lt (by linarith) (by linarith)
  have hx3 : a < x := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨x, hball ?_, Or.inl (hint ⟨hx1, hx2⟩)⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/- ### 5. The results -/

/-- **R3 (Dini form).** Residually many `x` satisfy: if `x ∈ [0,1]`, then for every `M` some `t ∈ [0,1]` with
`x < t < x + 1/(M+1)` has `(f t − f x)/(t − x) > M`; i.e. the upper right Dini derivative of `f` at `x` is `+∞`. -/
theorem residual_dini (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) :
    ∀ᶠ x in residual ℝ, x ∈ Icc (0 : ℝ) 1 → ∀ M : ℕ, ∃ t ∈ Icc (0 : ℝ) 1,
      x < t ∧ t < x + 1 / ((M : ℝ) + 1) ∧ (M : ℝ) < (f t - f x) / (t - x) := by
  have hall : ∀ᶠ x in residual ℝ, ∀ M : ℕ, x ∈ U f M :=
    eventually_countable_forall.mpr fun M => residual_of_dense_open (isOpen_U f M) (dense_U f hf M)
  filter_upwards [hall] with x hx hxI M
  rcases hx M with h | h
  · exact (interior_subset h : x ∈ good f M)
  · exact absurd hxI h

/-- **R3 (no derivative).** Residually many `x` satisfy: if `x ∈ [0,1]`, `f` has no derivative at `x` within
`Icc 0 1` (of any value). -/
theorem residual_no_deriv (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) :
    ∀ᶠ x in residual ℝ, x ∈ Icc (0 : ℝ) 1 → ¬ ∃ y : ℝ, HasDerivWithinAt f y (Icc 0 1) x := by
  filter_upwards [residual_dini f hf] with x hx hxI
  rintro ⟨y, hy⟩
  have ho := (hasDerivWithinAt_iff_isLittleO.mp hy).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp ho
  obtain ⟨M, hM⟩ := exists_nat_gt (max (|y| + 1) (1 / δ))
  have hM1 : |y| + 1 < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hMd : 1 / δ < M := lt_of_le_of_lt (le_max_right _ _) hM
  obtain ⟨t, htI, hxt, htx, hq⟩ := hx hxI M
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsmall : t - x < δ := by
    have : 1 / ((M : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hM0]
      rw [div_lt_iff₀ hδ] at hMd
      nlinarith
    linarith
  have hmem : t ∈ Metric.ball x δ ∩ Icc 0 1 := by
    refine ⟨?_, htI⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h := hball hmem
  simp only [Set.mem_setOf_eq, one_mul, Real.norm_eq_abs, smul_eq_mul] at h
  have htx0 : 0 < t - x := by linarith
  rw [abs_of_pos htx0] at h
  have h1 := (abs_le.mp h).2
  rw [lt_div_iff₀ htx0] at hq
  have : y * (t - x) ≤ |y| * (t - x) := mul_le_mul_of_nonneg_right (le_abs_self y) htx0.le
  nlinarith

/-- **R3, in the shape of formal-conjectures' `erdos_50`**: residually many `x` are not a point of `[0,1]` where `f`
has a positive derivative within `Icc 0 1`. -/
theorem erdos_50_residual : ∀ᵉ (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f),
    ∀ᶠ x in residual ℝ, ¬ (x ∈ Icc (0 : ℝ) 1 ∧ ∃ y > 0, HasDerivWithinAt f y (Icc 0 1) x) := by
  intro f hf
  filter_upwards [residual_no_deriv f hf] with x hx
  rintro ⟨hxI, y, -, hy⟩
  exact hx hxI ⟨y, hy⟩

/-- **Density corollary**: every open subinterval of `[0,1]` contains a point where `f` has no derivative within
`Icc 0 1`. -/
theorem exists_no_deriv_in (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : ∃ x ∈ Ioo a b, ¬ ∃ y : ℝ, HasDerivWithinAt f y (Icc 0 1) x := by
  have hd : Dense {x : ℝ | x ∈ Icc (0 : ℝ) 1 → ¬ ∃ y : ℝ, HasDerivWithinAt f y (Icc 0 1) x} :=
    dense_of_mem_residual (residual_no_deriv f hf)
  obtain ⟨x, hx, hP⟩ := hd.inter_open_nonempty (Ioo a b) isOpen_Ioo ⟨(a + b) / 2, by constructor <;> linarith⟩
  exact ⟨x, hx, hP ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

end Residual
end Erdos50

end
end

-- Erdos50FC.Continuous
section
/-
# Erdős #50, rung R4a: the distribution function is continuous on `[0,1]`

For every `f` with `IsDistributionOfPhiRatio f` (formal-conjectures' wording), `ContinuousOn f (Icc 0 1)`. This is
the first conjunct of FC's `IsPurelySingularOn f (Icc 0 1)` (statement `erdos_50_singular`, Erdős 1939; continuity
itself is Schoenberg 1928). Known mathematics; the point is the machine-checked version from FC's hypothesis alone.

Proof (a Lévy-type "no atom" argument; nothing beyond `hf` is assumed).

Fix `N ≥ 2`, `Q = {p ≤ N prime}`, `T(n) = {p ∈ Q : p ∣ n}`, `h_T = ∏_{p∈T} (1 − 1/p)` and
`Z_T(c) = {n : T(n) = T, φ(n) < c n}`.

1. *Self-similarity* (`hd_selfsim`, `Z_selfsim`). For `p ∈ T`, `n ∈ Z_T(c)` iff `p ∣ n` and `n/p ∈ Z_T(c)` or
   `n/p ∈ Z_{T∖p}(c/(1 − 1/p))`. So the counting function satisfies `#W(b) = #W(⌈b/p⌉) + #U(⌈b/p⌉)`, and a
   contraction argument (`tendsto_of_contract`) gives `d(Z_T(c)) = d(Z_{T∖p}(c/(1−1/p)))/(p − 1)` whenever the
   right-hand density exists.
2. *Existence* (`Z_exists`). Induction on `j` with `c (1 + 1/N)^j > 1`: for `T ≠ ∅` use 1. one level down;
   `Z_∅(c) = S(c) ∖ ⋃_{T ≠ ∅} Z_T(c)` with `S(c) = {φ(n) < cn}` of density `f(c)` by `hf`. Closed form
   (`hd_Z_closed`): `d(Z_T(c)) = G(c/h_T)/∏_{p∈T}(p − 1)`, `G = d(Z_∅(·))`.
3. *The `h_T` are distinct* (`h_inj`): if `h_A = h_B` with `A, B` disjoint sets of primes then
   `φ(a) b = φ(b) a` for `a = ∏A`, `b = ∏B` coprime, so `a ∣ φ(a)`, `a = 1`.
4. *Band bound* (`band_le`). For `c > 0` and small `ε`, the intervals `[(c−ε)/h_T, (c+ε)/h_T)` are disjoint, so
   `F(c+ε) − F(c−ε) = ∑_T (G((c+ε)/h_T) − G((c−ε)/h_T))/∏(p−1) ≤ d(⋃_T bands) ≤ d{T(n) = ∅} = ∏_{p ≤ N}(1 − 1/p)`,
   which tends to 0 (`∑ 1/p = ∞`, R3's `exists_sprod_lt`).
5. *At `c = 0`* (`hd_S_small`): Markov on `∑_{p ∣ n, p > Y} 1/p` gives `d{φ(n) < εn} ≤ 4/Y` for `ε ≤ ρ_Y/2`.
-/

open Filter Finset Real Topology
open scoped Nat

noncomputable section

namespace Erdos50
namespace Cont

open AtE

/- ### 0. Densities: counting, finite additivity, monotonicity -/

/-- The counting function `#(S ∩ [0, b))`. -/
def cnt (S : Set ℕ) (b : ℕ) : ℕ := (S ∩ Set.Iio b).ncard

lemma finite_inter_Iio (S : Set ℕ) (b : ℕ) : (S ∩ Set.Iio b).Finite :=
  (Set.finite_Iio b).inter_of_right S

lemma pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
  have h2 : (Set.univ ∩ Set.Iio b : Set ℕ) = ↑(Finset.range b) := by ext n; simp
  simp only [Set.partialDensity, Set.inter_univ, h2, Set.ncard_coe_finset, Finset.card_range, cnt]

lemma hasDensity_iff (S : Set ℕ) (a : ℝ) :
    S.HasDensity a ↔ Tendsto (fun b : ℕ => (cnt S b : ℝ) / b) atTop (𝓝 a) := by
  unfold Set.HasDensity
  simp only [pd_eq]

lemma cnt_le (S : Set ℕ) (b : ℕ) : cnt S b ≤ b := by
  calc cnt S b ≤ (Set.Iio b).ncard := Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio b)
    _ = b := by
      rw [show (Set.Iio b : Set ℕ) = ↑(Finset.range b) by ext; simp, Set.ncard_coe_finset,
        Finset.card_range]

lemma cnt_mono {A B : Set ℕ} (h : A ⊆ B) (b : ℕ) : cnt A b ≤ cnt B b :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) (finite_inter_Iio B b)

lemma cnt_union {A B : Set ℕ} (h : Disjoint A B) (b : ℕ) : cnt (A ∪ B) b = cnt A b + cnt B b := by
  unfold cnt
  rw [Set.union_inter_distrib_right]
  exact Set.ncard_union_eq (h.mono Set.inter_subset_left Set.inter_subset_left)
    (finite_inter_Iio A b) (finite_inter_Iio B b)

lemma hd_union {A B : Set ℕ} {a b : ℝ} (hA : A.HasDensity a) (hB : B.HasDensity b) (h : Disjoint A B) :
    (A ∪ B).HasDensity (a + b) := by
  rw [hasDensity_iff] at *
  have := hA.add hB
  refine this.congr (fun x => ?_)
  rw [cnt_union h]; push_cast; ring

lemma hd_diff {A B : Set ℕ} {a b : ℝ} (hA : A.HasDensity a) (hB : B.HasDensity b) (h : B ⊆ A) :
    (A \ B).HasDensity (a - b) := by
  rw [hasDensity_iff] at *
  have := hA.sub hB
  refine this.congr (fun x => ?_)
  have hu : A = (A \ B) ∪ B := (Set.sdiff_union_of_subset h).symm
  have hc : cnt A x = cnt (A \ B) x + cnt B x := by
    conv_lhs => rw [hu]
    exact cnt_union Set.disjoint_sdiff_left x
  rw [hc]; push_cast; ring

lemma hd_le {A B : Set ℕ} {a b : ℝ} (hA : A.HasDensity a) (hB : B.HasDensity b) (h : A ⊆ B) : a ≤ b := by
  rw [hasDensity_iff] at *
  refine le_of_tendsto_of_tendsto' hA hB (fun x => ?_)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast cnt_mono h x

lemma hd_unique {A : Set ℕ} {a b : ℝ} (ha : A.HasDensity a) (hb : A.HasDensity b) : a = b :=
  tendsto_nhds_unique ha hb

lemma hd_nonneg {A : Set ℕ} {a : ℝ} (ha : A.HasDensity a) : 0 ≤ a := by
  rw [hasDensity_iff] at ha
  exact ge_of_tendsto' ha (fun x => by positivity)

lemma hd_empty : (∅ : Set ℕ).HasDensity 0 := by
  rw [hasDensity_iff]
  have : (fun b : ℕ => (cnt ∅ b : ℝ) / b) = fun _ => 0 := by
    funext b; simp [cnt]
  rw [this]; exact tendsto_const_nhds

lemma hd_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y : ι → Set ℕ) (d : ι → ℝ)
    (hY : ∀ i ∈ s, (Y i).HasDensity (d i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Y i) (Y j)) :
    (⋃ i ∈ s, Y i).HasDensity (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hd_empty
  | insert k s hk ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hk]
    refine hd_union (hY k (mem_insert_self k s))
      (ih (fun i hi => hY i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hdisj i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)) ?_
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hdisj k (mem_insert_self k s) i (mem_insert_of_mem hi) (by rintro rfl; exact hk hi)

/- ### 1. A contraction lemma and the self-similar density -/

lemma tendsto_of_contract (a r s : ℕ → ℝ) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ b, |a b| ≤ M)
    (hσ : Tendsto σ atTop atTop) {ρ τ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr : Tendsto r atTop (𝓝 ρ)) (hs : Tendsto s atTop (𝓝 τ))
    (h : ∀ᶠ b in atTop, a b = r b * (a (σ b) + s b)) :
    Tendsto a atTop (𝓝 (ρ * τ / (1 - ρ))) := by
  set v := ρ * τ / (1 - ρ) with hv_def
  have h1ρ : 0 < 1 - ρ := by linarith
  have hvfix : ρ * (v + τ) - v = 0 := by
    rw [hv_def]; field_simp; ring
  set θ := (1 + ρ) / 2 with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  have hrθ : ∀ᶠ b in atTop, |r b| ≤ θ := by
    have := hr.eventually (Ioo_mem_nhds (show -θ < ρ by linarith) (show ρ < θ by linarith))
    filter_upwards [this] with b hb
    exact abs_le.mpr ⟨hb.1.le, hb.2.le⟩
  -- error term
  set e : ℕ → ℝ := fun b => r b * (v + s b) - v
  have he : Tendsto e atTop (𝓝 0) := by
    have := (hr.mul ((tendsto_const_nhds (x := v)).add hs)).sub (tendsto_const_nhds (x := v))
    rw [hvfix] at this
    exact this
  have hrel : ∀ᶠ b in atTop, a b - v = r b * (a (σ b) - v) + e b := by
    filter_upwards [h] with b hb
    rw [hb]; simp only [e]; ring
  set B := M + |v|
  have hB : ∀ b, |a b - v| ≤ B := fun b => by
    calc |a b - v| ≤ |a b| + |v| := abs_sub _ _
      _ ≤ B := by linarith [hM b]
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η * (1 - θ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; have : 0 < 1 - θ := by linarith
                         positivity
  have heδ : ∀ᶠ b in atTop, |e b| ≤ δ := by
    have := he.eventually (Metric.closedBall_mem_nhds 0 hδ0)
    filter_upwards [this] with b hb
    simpa [Metric.mem_closedBall, Real.dist_eq] using hb
  have hclaim : ∀ k : ℕ, ∀ᶠ b in atTop, |a b - v| ≤ θ ^ k * B + δ / (1 - θ) := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall (fun b => ?_)
      have : 0 ≤ δ / (1 - θ) := by have : 0 < 1 - θ := by linarith
                                   positivity
      simp only [pow_zero, one_mul]
      linarith [hB b]
    | succ k ih =>
      have ih' := hσ.eventually ih
      filter_upwards [ih', hrθ, heδ, hrel] with b hb1 hb2 hb3 hb4
      rw [hb4]
      have h1θ : 0 < 1 - θ := by linarith
      calc |r b * (a (σ b) - v) + e b| ≤ |r b * (a (σ b) - v)| + |e b| := abs_add_le _ _
        _ = |r b| * |a (σ b) - v| + |e b| := by rw [abs_mul]
        _ ≤ θ * (θ ^ k * B + δ / (1 - θ)) + δ := by
            have := abs_nonneg (a (σ b) - v)
            have := abs_nonneg (r b)
            gcongr
        _ = θ ^ (k + 1) * B + δ / (1 - θ) := by
            field_simp; ring
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, θ ^ k * B < η / 2 := by
    by_cases hB0' : B = 0
    · exact ⟨0, by rw [hB0']; linarith⟩
    · have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB0')
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < η / 2 / B by positivity) hθ1
      refine ⟨k, ?_⟩
      rw [lt_div_iff₀ hBp] at hk
      exact hk
  filter_upwards [hclaim k] with b hb
  rw [Real.dist_eq]
  have : δ / (1 - θ) = η / 2 := by
    rw [hδ]; have : (1 - θ) ≠ 0 := by linarith
    field_simp
  linarith

/-- `#{n < b : n ∈ W} = #{m < ⌈b/p⌉ : m ∈ W ∪ U}` when `n ∈ W ↔ p ∣ n ∧ n/p ∈ W ∪ U`. -/
lemma cnt_selfsim {W U : Set ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hW : ∀ n, n ∈ W ↔ p ∣ n ∧ (n / p ∈ W ∨ n / p ∈ U)) (b : ℕ) :
    cnt W b = cnt (W ∪ U) ((b + p - 1) / p) := by
  have hp0 : 0 < p := by omega
  have himg : W ∩ Set.Iio b = (fun m => p * m) '' ((W ∪ U) ∩ Set.Iio ((b + p - 1) / p)) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_image, Set.mem_union]
    constructor
    · rintro ⟨hn, hnb⟩
      have h := (hW n).mp hn
      refine ⟨n / p, ⟨h.2, ?_⟩, Nat.mul_div_cancel' h.1⟩
      have hc := Nat.div_mul_cancel h.1
      have : n / p + 1 ≤ (b + p - 1) / p := by
        rw [Nat.le_div_iff_mul_le hp0, add_mul, one_mul, hc]; omega
      omega
    · rintro ⟨m, ⟨hm, hmb⟩, rfl⟩
      refine ⟨(hW (p * m)).mpr ⟨dvd_mul_right p m, by rwa [Nat.mul_div_cancel_left m hp0]⟩, ?_⟩
      have h1 : m + 1 ≤ (b + p - 1) / p := hmb
      rw [Nat.le_div_iff_mul_le hp0, add_mul, one_mul] at h1
      rw [mul_comm]
      set q := m * p
      omega
  unfold cnt
  rw [himg, Set.ncard_image_of_injective _ (fun x y hxy => Nat.eq_of_mul_eq_mul_left hp0 hxy)]


lemma hd_selfsim {W U : Set ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hW : ∀ n, n ∈ W ↔ p ∣ n ∧ (n / p ∈ W ∨ n / p ∈ U)) (hdisj : Disjoint W U) {u : ℝ}
    (hU : U.HasDensity u) : W.HasDensity (u / ((p : ℝ) - 1)) := by
  have hp0 : 0 < p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set σ : ℕ → ℕ := fun b => (b + p - 1) / p with hσdef
  have hσ : Tendsto σ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    refine ⟨B * p, fun b hb => ?_⟩
    simp only [hσdef]
    rw [Nat.le_div_iff_mul_le hp0]; omega
  -- bounds on σ b
  have hσup : ∀ b : ℕ, (σ b : ℝ) ≤ b / p + 1 := by
    intro b
    have h1 : (σ b : ℝ) ≤ ((b + p - 1 : ℕ) : ℝ) / p := Nat.cast_div_le
    have h2 : ((b + p - 1 : ℕ) : ℝ) ≤ b + p := by
      have : b + p - 1 ≤ b + p := by omega
      exact_mod_cast this
    calc (σ b : ℝ) ≤ ((b + p - 1 : ℕ) : ℝ) / p := h1
      _ ≤ (b + p) / p := by gcongr
      _ = b / p + 1 := by field_simp
  have hσlo : ∀ b : ℕ, (b : ℝ) / p ≤ σ b := by
    intro b
    have h := Nat.div_add_mod (b + p - 1) p
    have hm := Nat.mod_lt (b + p - 1) hp0
    have : b ≤ p * σ b := by simp only [hσdef]; omega
    rw [div_le_iff₀ (by positivity)]
    have : (b : ℝ) ≤ p * σ b := by exact_mod_cast this
    linarith
  set a : ℕ → ℝ := fun b => (cnt W b : ℝ) / b
  set r : ℕ → ℝ := fun b => (σ b : ℝ) / b
  set s : ℕ → ℝ := fun b => (cnt U (σ b) : ℝ) / σ b
  have hr : Tendsto r atTop (𝓝 (1 / p)) := by
    have hlo : Tendsto (fun b : ℕ => (1 / p : ℝ) - 0 * (1 / (b : ℝ))) atTop (𝓝 (1 / p)) := by
      simpa using (tendsto_const_nhds (x := (1 / p : ℝ)))
    have hup : Tendsto (fun b : ℕ => (1 / p : ℝ) + 1 / (b : ℝ)) atTop (𝓝 (1 / p)) := by
      simpa using (tendsto_const_nhds (x := (1 / p : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with b hb
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      simp only [r, zero_mul, sub_zero]
      rw [le_div_iff₀ hb']
      have := hσlo b
      calc 1 / (p : ℝ) * b = b / p := by ring
        _ ≤ σ b := this
    · filter_upwards [eventually_gt_atTop 0] with b hb
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      simp only [r]
      rw [div_le_iff₀ hb']
      have := hσup b
      calc (σ b : ℝ) ≤ b / p + 1 := this
        _ = (1 / p + 1 / b) * b := by field_simp
  have hs : Tendsto s atTop (𝓝 u) := by
    rw [hasDensity_iff] at hU
    exact hU.comp hσ
  have hrel : ∀ᶠ b in atTop, a b = r b * (a (σ b) + s b) := by
    filter_upwards [eventually_gt_atTop 0] with b hb
    have hσ0 : 0 < σ b := Nat.div_pos (by omega) hp0
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hσ' : (σ b : ℝ) ≠ 0 := by exact_mod_cast hσ0.ne'
    simp only [a, r, s]
    rw [cnt_selfsim hp hW b, cnt_union hdisj]
    change _ = ((((b + p - 1) / p : ℕ) : ℝ) / b) * (_ / (((b + p - 1) / p : ℕ) : ℝ) + _ / (((b + p - 1) / p : ℕ) : ℝ))
    have hσ'' : (((b + p - 1) / p : ℕ) : ℝ) ≠ 0 := hσ'
    push_cast
    field_simp
    rfl
  have hM : ∀ b, |a b| ≤ 1 := by
    intro b
    simp only [a]
    rw [abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [div_le_one (by exact_mod_cast hb)]; exact_mod_cast cnt_le W b
  have hρ1 : (1 / p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have := tendsto_of_contract a r s σ 1 hM hσ (by positivity) hρ1 hr hs hrel
  rw [hasDensity_iff]
  convert this using 2
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/- ### 2. The sets `Z_T(c)` -/

/-- `T(n) = {p ≤ N prime : p ∣ n}`. -/
def Tn (N n : ℕ) : Finset ℕ := (primesTo N).filter (· ∣ n)

/-- `h_T = ∏_{p ∈ T} (1 − 1/p)`. -/
def h (T : Finset ℕ) : ℝ := ∏ p ∈ T, (1 - 1 / (p : ℝ))

/-- `w_T = ∏_{p ∈ T} (p − 1)`. -/
def w (T : Finset ℕ) : ℝ := ∏ p ∈ T, ((p : ℝ) - 1)

/-- `S(c) = {n : φ(n) < c n}`. -/
def S (c : ℝ) : Set ℕ := {n | (φ n : ℝ) < c * n}

/-- `Z_T(c) = {n : T(n) = T, φ(n) < c n}`. -/
def Z (N : ℕ) (T : Finset ℕ) (c : ℝ) : Set ℕ := {n | Tn N n = T ∧ (φ n : ℝ) < c * n}

lemma prime_of_mem_primesTo {N p : ℕ} (hp : p ∈ primesTo N) : p.Prime := (Finset.mem_filter.mp hp).2

lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
  linarith

lemma h_pos {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : 0 < h T :=
  Finset.prod_pos fun p hp => one_sub_inv_pos (hT p hp)

lemma w_ge_one {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : 1 ≤ w T := by
  unfold w
  induction T using Finset.induction_on with
  | empty => simp
  | insert q T hq ih =>
    rw [Finset.prod_insert hq]
    have h1 := ih (fun p hp => hT p (mem_insert_of_mem hp))
    have : (2 : ℝ) ≤ q := by exact_mod_cast (hT q (mem_insert_self q T)).two_le
    nlinarith

lemma not_mem_Z_zero (N : ℕ) (T : Finset ℕ) (c : ℝ) : 0 ∉ Z N T c := by
  simp [Z]

lemma Tn_mul_of_dvd {N p m : ℕ} (hp : p ∈ primesTo N) (hpm : p ∣ m) : Tn N (p * m) = Tn N m := by
  ext q
  simp only [Tn, Finset.mem_filter]
  constructor
  · rintro ⟨hq, hqd⟩
    refine ⟨hq, ?_⟩
    rcases (Nat.Prime.dvd_mul (prime_of_mem_primesTo hq)).mp hqd with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq (prime_of_mem_primesTo hq) (prime_of_mem_primesTo hp)).mp h1
      subst this; exact hpm
    · exact h1
  · rintro ⟨hq, hqd⟩; exact ⟨hq, Dvd.dvd.mul_left hqd p⟩

lemma Tn_mul_of_not_dvd {N p m : ℕ} (hp : p ∈ primesTo N) :
    Tn N (p * m) = insert p (Tn N m) := by
  ext q
  simp only [Tn, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hq, hqd⟩
    rcases (Nat.Prime.dvd_mul (prime_of_mem_primesTo hq)).mp hqd with h1 | h1
    · left
      exact (Nat.prime_dvd_prime_iff_eq (prime_of_mem_primesTo hq) (prime_of_mem_primesTo hp)).mp h1
    · right; exact ⟨hq, h1⟩
  · rintro (rfl | ⟨hq, hqd⟩)
    · exact ⟨hp, dvd_mul_right _ _⟩
    · exact ⟨hq, Dvd.dvd.mul_left hqd p⟩

lemma mem_Tn {N p n : ℕ} : p ∈ Tn N n ↔ p ∈ primesTo N ∧ p ∣ n := Finset.mem_filter

/-- Membership of `p m` in `Z_T(c)`, for `p ∈ T`. -/
lemma mul_mem_Z {N p : ℕ} {T : Finset ℕ} (hT : T ⊆ primesTo N) (hpT : p ∈ T) (c : ℝ) (m : ℕ) :
    p * m ∈ Z N T c ↔ (m ∈ Z N T c ∨ m ∈ Z N (T.erase p) (c / (1 - 1 / (p : ℝ)))) := by
  have hpQ := hT hpT
  have hp := prime_of_mem_primesTo hpQ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos := one_sub_inv_pos hp
  by_cases hpm : p ∣ m
  · rw [show Z N T c = {n | Tn N n = T ∧ (φ n : ℝ) < c * n} from rfl]
    simp only [Z, Set.mem_ofPred_eq, Tn_mul_of_dvd hpQ hpm]
    have hne : Tn N m ≠ T.erase p := by
      intro h'
      have : p ∈ Tn N m := mem_Tn.mpr ⟨hpQ, hpm⟩
      rw [h'] at this; simp at this
    rw [Nat.totient_mul_of_prime_of_dvd hp hpm]
    push_cast
    have hp0 : (0 : ℝ) < p := by linarith
    constructor
    · rintro ⟨h1, h2⟩
      left; exact ⟨h1, by nlinarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by nlinarith⟩
      · exact absurd h1 hne
  · simp only [Z, Set.mem_ofPred_eq, Tn_mul_of_not_dvd (m := m) hpQ]
    have hpn : p ∉ Tn N m := fun h' => hpm (mem_Tn.mp h').2
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
    have hins : insert p (Tn N m) = T ↔ Tn N m = T.erase p := by
      constructor
      · rintro rfl; rw [Finset.erase_insert hpn]
      · rintro h'; rw [h', Finset.insert_erase hpT]
    rw [hins]
    have hTm : Tn N m ≠ T := fun h' => hpn (h' ▸ hpT)
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; simp
    push_cast [hcast]
    have hp0 : (0 : ℝ) < p := by linarith
    have hkey : ((p : ℝ) - 1) * φ m < c * (p * m) ↔ (φ m : ℝ) < c / (1 - 1 / p) * m := by
      have : c / (1 - 1 / (p : ℝ)) = c * p / (p - 1) := by
        field_simp
      rw [this, div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]
      constructor <;> intro h' <;> linarith
    constructor
    · rintro ⟨h1, h2⟩; right; exact ⟨h1, hkey.mp (by linarith)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 hTm
      · exact ⟨h1, by have := hkey.mpr h2; linarith⟩

lemma Z_selfsim {N p : ℕ} {T : Finset ℕ} (hT : T ⊆ primesTo N) (hpT : p ∈ T) (c : ℝ) (n : ℕ) :
    n ∈ Z N T c ↔ p ∣ n ∧ (n / p ∈ Z N T c ∨ n / p ∈ Z N (T.erase p) (c / (1 - 1 / (p : ℝ)))) := by
  have hpQ := hT hpT
  constructor
  · intro hn
    have hpn : p ∣ n := by
      have : p ∈ Tn N n := by rw [hn.1]; exact hpT
      exact (mem_Tn.mp this).2
    refine ⟨hpn, ?_⟩
    rw [← mul_mem_Z hT hpT c (n / p), Nat.mul_div_cancel' hpn]
    exact hn
  · rintro ⟨hpn, h'⟩
    rw [← mul_mem_Z hT hpT c (n / p), Nat.mul_div_cancel' hpn] at h'
    exact h'

lemma Z_disjoint_erase {N p : ℕ} {T : Finset ℕ} (hpT : p ∈ T) (c c' : ℝ) :
    Disjoint (Z N T c) (Z N (T.erase p) c') := by
  rw [Set.disjoint_left]
  rintro n ⟨h1, -⟩ ⟨h2, -⟩
  rw [h1] at h2
  have : p ∈ T.erase p := h2 ▸ hpT
  simp at this

/-- **Self-similarity**: `d Z_T(c) = d Z_{T∖p}(c/(1−1/p)) / (p − 1)`. -/
lemma hd_Z_insert {N p : ℕ} {T : Finset ℕ} (hT : T ⊆ primesTo N) (hpT : p ∈ T) (c : ℝ) {u : ℝ}
    (hu : (Z N (T.erase p) (c / (1 - 1 / (p : ℝ)))).HasDensity u) :
    (Z N T c).HasDensity (u / ((p : ℝ) - 1)) :=
  hd_selfsim (prime_of_mem_primesTo (hT hpT)).two_le (Z_selfsim hT hpT c) (Z_disjoint_erase hpT _ _) hu


/- ### 3. Base case: integers with no prime factor `≤ N` -/

lemma cnt_eq_card (A : Set ℕ) [DecidablePred (· ∈ A)] (b : ℕ) :
    cnt A b = ((Finset.range b).filter (· ∈ A)).card := by
  unfold cnt
  have : A ∩ Set.Iio b = ↑((Finset.range b).filter (· ∈ A)) := by ext n; simp [and_comm]
  rw [this, Set.ncard_coe_finset]

lemma card_coprime_range_mul (P k : ℕ) :
    ((Finset.range (k * P)).filter (P.Coprime ·)).card = k * φ P := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.range ((k + 1) * P) = Finset.range (k * P) ∪ Finset.Ico (k * P) (k * P + P) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, show (k + 1) * P = k * P + P by ring]
      exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (by
        rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive _ _ _)), ih,
      Nat.filter_coprime_Ico_eq_totient]
    ring

lemma hd_coprime {P : ℕ} (hP : 0 < P) : {n : ℕ | P.Coprime n}.HasDensity ((φ P : ℝ) / P) := by
  rw [hasDensity_iff]
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hcnt : ∀ b, cnt {n : ℕ | P.Coprime n} b = ((Finset.range b).filter (P.Coprime ·)).card := by
    intro b; rw [cnt_eq_card]; rfl
  have hlo : ∀ b : ℕ, ((b / P : ℕ) : ℝ) * φ P ≤ cnt {n : ℕ | P.Coprime n} b := by
    intro b
    rw [hcnt, ← Nat.cast_mul, ← card_coprime_range_mul]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr (Nat.div_mul_le_self b P)))
  have hup : ∀ b : ℕ, (cnt {n : ℕ | P.Coprime n} b : ℝ) ≤ ((b / P + 1 : ℕ) : ℝ) * φ P := by
    intro b
    rw [hcnt, ← Nat.cast_mul, ← card_coprime_range_mul]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr (by
        have := Nat.lt_div_mul_add (a := b) hP
        rw [add_mul, one_mul]; omega)))
  have hφ : (0 : ℝ) ≤ φ P := Nat.cast_nonneg _
  have hL : Tendsto (fun b : ℕ => (φ P : ℝ) / P - φ P * (1 / (b : ℝ))) atTop (𝓝 ((φ P : ℝ) / P)) := by
    simpa using (tendsto_const_nhds (x := (φ P : ℝ) / P)).sub
      ((tendsto_const_nhds (x := (φ P : ℝ))).mul tendsto_one_div_atTop_nhds_zero_nat)
  have hU : Tendsto (fun b : ℕ => (φ P : ℝ) / P + φ P * (1 / (b : ℝ))) atTop (𝓝 ((φ P : ℝ) / P)) := by
    simpa using (tendsto_const_nhds (x := (φ P : ℝ) / P)).add
      ((tendsto_const_nhds (x := (φ P : ℝ))).mul tendsto_one_div_atTop_nhds_zero_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [le_div_iff₀ hb']
    have h1 := hlo b
    have h2 : (b : ℝ) / P - 1 ≤ ((b / P : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := b) hP
      have : (b : ℝ) < ((b / P : ℕ) : ℝ) * P + P := by exact_mod_cast this
      rw [div_sub_one hP'.ne', div_le_iff₀ hP']; linarith
    have : ((φ P : ℝ) / P - φ P * (1 / b)) * b = ((b : ℝ) / P - 1) * φ P := by
      field_simp
    rw [this]
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [div_le_iff₀ hb']
    have h1 := hup b
    have h2 : ((b / P + 1 : ℕ) : ℝ) ≤ (b : ℝ) / P + 1 := by
      push_cast; have := (Nat.cast_div_le (m := b) (n := P) (α := ℝ)); linarith
    have : ((φ P : ℝ) / P + φ P * (1 / b)) * b = ((b : ℝ) / P + 1) * φ P := by
      field_simp
    rw [this]
    nlinarith

/-- Integers with no prime factor `≤ N`. -/
def C0 (N : ℕ) : Set ℕ := {n | Tn N n = ∅}

lemma C0_eq (N : ℕ) : C0 N = {n : ℕ | (bigP N).Coprime n} := by
  ext n
  simp only [C0, Set.mem_ofPred_eq, bigP, Nat.coprime_prod_left_iff, Tn, Finset.filter_eq_empty_iff]
  constructor
  · intro h p hp
    exact (Nat.Prime.coprime_iff_not_dvd (prime_of_mem_primesTo hp)).mpr (h hp)
  · intro h p hp
    exact (Nat.Prime.coprime_iff_not_dvd (prime_of_mem_primesTo hp)).mp (h p hp)

lemma hd_C0 (N : ℕ) : (C0 N).HasDensity (rho N) := by
  rw [C0_eq]
  have h := hd_coprime (bigP_pos N)
  have hP : ((bigP N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (bigP_pos N).ne'
  rwa [totient_bigP, mul_div_cancel_left₀ _ hP] at h

lemma two_mem_primesTo {N : ℕ} (hN : 2 ≤ N) : 2 ∈ primesTo N :=
  Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hN⟩, Nat.prime_two⟩

lemma Z_empty_eq_C0 {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc : 1 < c) : Z N ∅ c = C0 N := by
  ext n
  simp only [Z, C0, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have : 2 ∈ Tn N 0 := mem_Tn.mpr ⟨two_mem_primesTo hN, dvd_zero 2⟩
      rw [h] at this; simp at this
    · have h1 : (φ n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
      have h2 : (0 : ℝ) < n := by exact_mod_cast hn
      nlinarith

lemma Z_subset_C0 (N : ℕ) (c : ℝ) : Z N ∅ c ⊆ C0 N := fun _ h => h.1

lemma Z_mono (N : ℕ) (T : Finset ℕ) {c c' : ℝ} (hcc : c ≤ c') : Z N T c ⊆ Z N T c' := by
  rintro n ⟨h1, h2⟩
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  exact mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg n)

lemma Z_nonpos (N : ℕ) (T : Finset ℕ) {c : ℝ} (hc : c ≤ 0) : Z N T c = ∅ := by
  ext n
  simp only [Z, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  have : c * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg n)
  have : (0 : ℝ) ≤ φ n := Nat.cast_nonneg _
  linarith

lemma S_eq_iUnion (N : ℕ) (c : ℝ) : S c = ⋃ T ∈ (primesTo N).powerset, Z N T c := by
  ext n
  simp only [S, Z, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powerset, exists_prop]
  constructor
  · intro h; exact ⟨Tn N n, Finset.filter_subset _ _, rfl, h⟩
  · rintro ⟨T, -, -, h⟩; exact h

lemma Z_disjoint (N : ℕ) {T T' : Finset ℕ} (hTT : T ≠ T') (c c' : ℝ) : Disjoint (Z N T c) (Z N T' c') := by
  rw [Set.disjoint_left]
  rintro n ⟨h1, -⟩ ⟨h2, -⟩
  exact hTT (h1.symm.trans h2)

/- ### 4. Every `Z_T(c)` has a density -/

section Exist

variable {N : ℕ} (hN : 2 ≤ N) (hS : ∀ c : ℝ, ∃ v, (S c).HasDensity v)
include hN

lemma one_add_le_of_mem {p : ℕ} (hp : p ∈ primesTo N) : (1 + 1 / (N : ℝ)) * (1 - 1 / p) ≤ 1 := by
  have hpN : p ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesTo hp).two_le
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have key : (1 + 1 / (N : ℝ)) * (1 - 1 / p) = 1 - ((N : ℝ) - p + 1) / (N * p) := by
    field_simp; ring
  rw [key]
  have : 0 ≤ ((N : ℝ) - p + 1) / (N * p) := div_nonneg (by linarith) (by positivity)
  linarith

lemma base_exists : ∀ T ⊆ primesTo N, ∀ c : ℝ, 1 < c → ∃ v, (Z N T c).HasDensity v := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ c hc; exact ⟨rho N, (Z_empty_eq_C0 hN hc) ▸ hd_C0 N⟩
  | insert p T hp ih =>
    intro hT c hc
    have hpQ := hT (mem_insert_self p T)
    have hpos := one_sub_inv_pos (prime_of_mem_primesTo hpQ)
    have hlt : 1 - 1 / (p : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / p := by positivity
      linarith
    have hc' : 1 < c / (1 - 1 / (p : ℝ)) := by
      rw [lt_div_iff₀ hpos]; nlinarith
    obtain ⟨u, hu⟩ := ih ((Finset.subset_insert p T).trans hT) _ hc'
    rw [← Finset.erase_insert hp] at hu
    exact ⟨_, hd_Z_insert hT (mem_insert_self p T) c hu⟩

include hS in
lemma level_exists : ∀ j : ℕ, ∀ c : ℝ, 1 < c * (1 + 1 / (N : ℝ)) ^ j →
    ∀ T ⊆ primesTo N, ∃ v, (Z N T c).HasDensity v := by
  intro j
  induction j with
  | zero => intro c hc T hT; simp at hc; exact base_exists hN T hT c hc
  | succ j ih =>
    intro c hc T hT
    have hq : 1 < 1 + 1 / (N : ℝ) := lt_add_of_pos_right 1 (by positivity)
    have hc0 : 0 < c := by
      by_contra h0; push_neg at h0
      have : c * (1 + 1 / (N : ℝ)) ^ (j + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)
      linarith
    -- every nonempty `T` from one level down
    have hne : ∀ T ⊆ primesTo N, T ≠ ∅ → ∃ v, (Z N T c).HasDensity v := by
      intro T hT hT0
      obtain ⟨p, hpT⟩ := Finset.nonempty_iff_ne_empty.mpr hT0
      have hpQ := hT hpT
      have hpos := one_sub_inv_pos (prime_of_mem_primesTo hpQ)
      have hc' : 1 < c / (1 - 1 / (p : ℝ)) * (1 + 1 / (N : ℝ)) ^ j := by
        have h1 := one_add_le_of_mem hN hpQ
        have h2 : c * (1 + 1 / (N : ℝ)) ≤ c / (1 - 1 / (p : ℝ)) := by
          rw [le_div_iff₀ hpos]; nlinarith
        calc 1 < c * (1 + 1 / (N : ℝ)) ^ (j + 1) := hc
          _ = c * (1 + 1 / (N : ℝ)) * (1 + 1 / (N : ℝ)) ^ j := by ring
          _ ≤ c / (1 - 1 / (p : ℝ)) * (1 + 1 / (N : ℝ)) ^ j := by gcongr
      obtain ⟨u, hu⟩ := ih _ hc' (T.erase p) ((Finset.erase_subset p T).trans hT)
      exact ⟨_, hd_Z_insert hT hpT c hu⟩
    by_cases hT0 : T ≠ ∅
    · exact hne T hT hT0
    push_neg at hT0
    subst hT0
    set s := (primesTo N).powerset.erase ∅
    have hs : ∀ T ∈ s, ∃ v, (Z N T c).HasDensity v := fun T hT =>
      hne T (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)) (Finset.ne_of_mem_erase hT)
    choose! d hd using hs
    have hU := hd_biUnion s (fun T => Z N T c) d hd
      (fun i _ j _ hij => Z_disjoint N hij c c)
    obtain ⟨v, hv⟩ := hS c
    have hsub : (⋃ T ∈ s, Z N T c) ⊆ S c := by
      intro n hn
      rw [S_eq_iUnion N c]
      simp only [Set.mem_iUnion, exists_prop] at hn ⊢
      obtain ⟨T, hT, hn⟩ := hn
      exact ⟨T, Finset.mem_of_mem_erase hT, hn⟩
    have heq : Z N ∅ c = S c \ ⋃ T ∈ s, Z N T c := by
      ext n
      constructor
      · intro hn
        refine ⟨hn.2, ?_⟩
        simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
        intro T hT hnT
        exact Z_disjoint N (Finset.ne_of_mem_erase hT).symm c c |>.ne_of_mem hn hnT rfl
      · rintro ⟨hn, hn'⟩
        rw [S_eq_iUnion N c] at hn
        simp only [Set.mem_iUnion, exists_prop] at hn hn'
        obtain ⟨T, hT, hnT⟩ := hn
        by_cases h0 : T = ∅
        · exact h0 ▸ hnT
        · exact absurd ⟨T, Finset.mem_erase.mpr ⟨h0, hT⟩, hnT⟩ hn'
    exact ⟨_, heq ▸ hd_diff hv hU hsub⟩

include hS in
lemma Z_exists (T : Finset ℕ) (hT : T ⊆ primesTo N) (c : ℝ) : ∃ v, (Z N T c).HasDensity v := by
  by_cases hc : c ≤ 0
  · exact ⟨0, (Z_nonpos N T hc) ▸ hd_empty⟩
  push_neg at hc
  have hq : 1 < 1 + 1 / (N : ℝ) := lt_add_of_pos_right 1 (by positivity)
  obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually
    (eventually_gt_atTop (1 / c))).exists
  refine level_exists hN hS j c ?_ T hT
  rw [div_lt_iff₀ hc] at hj; linarith

end Exist

open Classical in
/-- `G(c) = d Z_∅(c)` (junk value `0` if it does not exist). -/
def G (N : ℕ) (c : ℝ) : ℝ := if h : ∃ v, (Z N ∅ c).HasDensity v then h.choose else 0

section Closed

variable {N : ℕ} (hN : 2 ≤ N) (hS : ∀ c : ℝ, ∃ v, (S c).HasDensity v)
include hN hS

lemma hd_G (c : ℝ) : (Z N ∅ c).HasDensity (G N c) := by
  have h := Z_exists hN hS ∅ (Finset.empty_subset _) c
  rw [G, dif_pos h]; exact h.choose_spec

lemma G_mono {c c' : ℝ} (hcc : c ≤ c') : G N c ≤ G N c' :=
  hd_le (hd_G hN hS c) (hd_G hN hS c') (Z_mono N ∅ hcc)

lemma G_le_rho (c : ℝ) : G N c ≤ rho N := hd_le (hd_G hN hS c) (hd_C0 N) (Z_subset_C0 N c)

/-- **Closed form**: `d Z_T(c) = G(c/h_T)/w_T`. -/
lemma hd_Z_closed : ∀ T ⊆ primesTo N, ∀ c : ℝ, (Z N T c).HasDensity (G N (c / h T) / w T) := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ c; simpa [h, w] using hd_G hN hS c
  | insert p T hp ih =>
    intro hT c
    have hpQ := hT (mem_insert_self p T)
    have hu := ih ((Finset.subset_insert p T).trans hT) (c / (1 - 1 / (p : ℝ)))
    rw [← Finset.erase_insert hp] at hu
    have := hd_Z_insert hT (mem_insert_self p T) c hu
    rw [Finset.erase_insert hp] at this
    convert this using 1
    rw [h, w, Finset.prod_insert hp, Finset.prod_insert hp, div_div, ← h, ← w, div_div]
    ring_nf

/-- `f(c) = ∑_T G(c/h_T)/w_T` (as densities of `S(c)`). -/
lemma hd_S_sum (c : ℝ) :
    (S c).HasDensity (∑ T ∈ (primesTo N).powerset, G N (c / h T) / w T) := by
  rw [S_eq_iUnion N c]
  exact hd_biUnion _ (fun T => Z N T c) _
    (fun T hT => hd_Z_closed hN hS T (Finset.mem_powerset.mp hT) c)
    (fun i _ j _ hij => Z_disjoint N hij c c)

end Closed


/- ### 5. The products `h_T` are pairwise distinct -/

lemma prod_anti {s t : Finset ℕ} (hst : s ⊆ t) (ht : ∀ p ∈ t, p.Prime) :
    ∏ p ∈ t, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  rw [← Finset.prod_sdiff hst]
  have h0 : 0 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p hp => (one_sub_inv_pos (ht p (hst hp))).le
  have h1 : ∏ p ∈ t \ s, (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p hp => (one_sub_inv_pos (ht p (Finset.sdiff_subset hp))).le)
      (fun p _ => by have : (0 : ℝ) ≤ 1 / p := by positivity
                     linarith)
  nlinarith

lemma h_eq_totient {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) :
    h A = (φ (∏ p ∈ A, p) : ℝ) / (∏ p ∈ A, p : ℕ) := by
  have hpos : 0 < ∏ p ∈ A, p := Finset.prod_pos fun p hp => (hA p hp).pos
  rw [totient_eq_mul_prod, Nat.primeFactors_prod hA, h]
  have : ((∏ p ∈ A, p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

lemma eq_empty_of_h_eq {A B : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime)
    (hAB : Disjoint A B) (heq : h A = h B) : A = ∅ := by
  set a := ∏ p ∈ A, p
  set b := ∏ p ∈ B, p
  have ha : 0 < a := Finset.prod_pos fun p hp => (hA p hp).pos
  have hb : 0 < b := Finset.prod_pos fun p hp => (hB p hp).pos
  have hcross : φ a * b = φ b * a := by
    rw [h_eq_totient hA, h_eq_totient hB,
      div_eq_div_iff (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')] at heq
    exact_mod_cast heq
  have hcop : Nat.Coprime a b :=
    Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes (hA p hp) (hB q hq)).mpr (fun hpq => by
        subst hpq; exact Finset.disjoint_left.mp hAB hp hq)
  have hdvd : a ∣ φ a * b := by rw [hcross]; exact dvd_mul_left a _
  have ha1 : a ∣ φ a := hcop.dvd_of_dvd_mul_right hdvd
  have hle : a ≤ φ a := Nat.le_of_dvd (Nat.totient_pos.mpr ha) ha1
  have ha_one : a = 1 := by
    by_contra hne
    have : 1 < a := by omega
    have := Nat.totient_lt a this
    omega
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have : p ∣ a := Finset.dvd_prod_of_mem _ hp
  rw [ha_one] at this
  exact (hA p hp).one_lt.ne' (Nat.dvd_one.mp this)

lemma h_inj {T T' : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hT' : ∀ p ∈ T', p.Prime) (heq : h T = h T') :
    T = T' := by
  have e1 : h T = h (T \ T') * h (T ∩ T') := by
    rw [h, h, h, ← Finset.prod_sdiff (Finset.inter_subset_left (s₁ := T) (s₂ := T')),
      Finset.sdiff_inter_self_left]
  have e2 : h T' = h (T' \ T) * h (T ∩ T') := by
    have : T' \ (T ∩ T') = T' \ T := by ext x; simp
    rw [h, h, h, ← Finset.prod_sdiff (Finset.inter_subset_right (s₁ := T) (s₂ := T')), this]
  have hC : 0 < h (T ∩ T') := h_pos fun p hp => hT p (Finset.mem_inter.mp hp).1
  have hAB : h (T \ T') = h (T' \ T) := by
    rw [e1, e2] at heq; exact mul_right_cancel₀ hC.ne' heq
  have hd : Disjoint (T \ T') (T' \ T) := by
    rw [Finset.disjoint_left]; intro x hx hx'; simp at hx hx'; exact hx.2 hx'.1
  have hA := eq_empty_of_h_eq (fun p hp => hT p (Finset.sdiff_subset hp))
    (fun p hp => hT' p (Finset.sdiff_subset hp)) hd hAB
  have hB := eq_empty_of_h_eq (fun p hp => hT' p (Finset.sdiff_subset hp))
    (fun p hp => hT p (Finset.sdiff_subset hp)) hd.symm hAB.symm
  exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hA)
    (Finset.sdiff_eq_empty_iff_subset.mp hB)

/- ### 6. The band bound -/

section Band

variable {N : ℕ} (hN : 2 ≤ N) (hS : ∀ c : ℝ, ∃ v, (S c).HasDensity v)
include hN hS

lemma band_le {c : ℝ} (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∑ T ∈ (primesTo N).powerset, (G N ((c + ε) / h T) - G N ((c - ε) / h T)) ≤ rho N := by
  set P := (primesTo N).powerset
  have hprime : ∀ T ∈ P, ∀ p ∈ T, p.Prime := fun T hT p hp =>
    prime_of_mem_primesTo (Finset.mem_powerset.mp hT hp)
  have tp : ∀ T : Finset ℕ, Tendsto (fun ε : ℝ => (c + ε) / h T) (𝓝[>] 0) (𝓝 (c / h T)) := by
    intro T
    have : Continuous (fun ε : ℝ => (c + ε) / h T) := (continuous_const.add continuous_id).div_const _
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have tm : ∀ T : Finset ℕ, Tendsto (fun ε : ℝ => (c - ε) / h T) (𝓝[>] 0) (𝓝 (c / h T)) := by
    intro T
    have : Continuous (fun ε : ℝ => (c - ε) / h T) := (continuous_const.sub continuous_id).div_const _
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpair : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ TT ∈ P ×ˢ P, TT.1 ≠ TT.2 →
      ((c + ε) / h TT.1 ≤ (c - ε) / h TT.2 ∨ (c + ε) / h TT.2 ≤ (c - ε) / h TT.1) := by
    rw [Filter.eventually_all_finset]
    rintro ⟨T, T'⟩ hTT
    obtain ⟨hT, hT'⟩ := Finset.mem_product.mp hTT
    by_cases he : T = T'
    · exact Eventually.of_forall (fun _ h' => absurd he h')
    have h1 := h_pos (hprime T hT)
    have h2 := h_pos (hprime T' hT')
    have hne : c / h T ≠ c / h T' := by
      intro hh
      apply he
      apply h_inj (hprime T hT) (hprime T' hT')
      rw [div_eq_div_iff h1.ne' h2.ne'] at hh
      exact (mul_left_cancel₀ hc.ne' hh).symm
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · filter_upwards [(tp T).eventually_lt (tm T') hlt] with ε hε _
      left; exact hε.le
    · filter_upwards [(tp T').eventually_lt (tm T) hlt] with ε hε _
      right; exact hε.le
  filter_upwards [hpair, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε := hε0
  set Y : Finset ℕ → Set ℕ := fun T => Z N ∅ ((c + ε) / h T) \ Z N ∅ ((c - ε) / h T)
  have hY : ∀ T ∈ P, (Y T).HasDensity (G N ((c + ε) / h T) - G N ((c - ε) / h T)) := by
    intro T hT
    exact hd_diff (hd_G hN hS _) (hd_G hN hS _) (Z_mono N ∅
      (div_le_div_of_nonneg_right (by linarith) (h_pos (hprime T hT)).le))
  have hdisj : ∀ T ∈ P, ∀ T' ∈ P, T ≠ T' → Disjoint (Y T) (Y T') := by
    intro T hT T' hT' hne
    rw [Set.disjoint_left]
    rintro n ⟨⟨hn0, hn1⟩, hn2⟩ ⟨⟨-, hn3⟩, hn4⟩
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases hε (T, T') (Finset.mem_product.mpr ⟨hT, hT'⟩) hne with hle | hle
    · apply hn4
      exact ⟨hn0, lt_of_lt_of_le hn1 (mul_le_mul_of_nonneg_right hle hn)⟩
    · apply hn2
      exact ⟨hn0, lt_of_lt_of_le hn3 (mul_le_mul_of_nonneg_right hle hn)⟩
  have hU := hd_biUnion P Y _ hY hdisj
  have hsub : (⋃ T ∈ P, Y T) ⊆ C0 N := by
    intro n hn
    simp only [Set.mem_iUnion, exists_prop] at hn
    obtain ⟨T, -, hnT⟩ := hn
    exact hnT.1.1
  exact hd_le hU (hd_C0 N) hsub

lemma sum_diff_le {c ε : ℝ} (hε : 0 ≤ ε) :
    (∑ T ∈ (primesTo N).powerset, G N ((c + ε) / h T) / w T) -
      ∑ T ∈ (primesTo N).powerset, G N ((c - ε) / h T) / w T ≤
    ∑ T ∈ (primesTo N).powerset, (G N ((c + ε) / h T) - G N ((c - ε) / h T)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro T hT
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => prime_of_mem_primesTo (Finset.mem_powerset.mp hT hp)
  rw [← sub_div]
  apply div_le_self _ (w_ge_one hprime)
  exact sub_nonneg.mpr (G_mono hN hS (div_le_div_of_nonneg_right (by linarith) (h_pos hprime).le))

end Band

/- ### 7. Near `c = 0`: Markov on the large prime factors -/

/-- `s_Y(n) = ∑_{p ∣ n, p > Y} 1/p`. -/
def sY (Y n : ℕ) : ℝ := ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ Y), 1 / (p : ℝ)

lemma sum_sY_le (Y M : ℕ) (hY : 1 ≤ Y) : ∑ n ∈ Finset.Ioc 0 M, sY Y n ≤ 2 * M / Y := by
  set A := Finset.Ioc 0 M
  set T := (Finset.Ioc Y M).filter Nat.Prime
  have hstep : ∀ k ∈ A, sY Y k ≤ ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) := by
    intro k hk
    have hkM : k ≤ M := (Finset.mem_Ioc.mp hk).2
    have hsub : k.primeFactors.filter (fun p => ¬ p ≤ Y) ⊆ T := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩,
        Nat.prime_of_mem_primeFactors hp'.1⟩
      exact (Nat.le_of_mem_primeFactors hp'.1).trans hkM
    calc sY Y k
        = ∑ p ∈ k.primeFactors.filter (fun p => ¬ p ≤ Y), (if p ∣ k then 1 / (p : ℝ) else 0) :=
          Finset.sum_congr rfl fun p hp => by
            rw [if_pos (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
      _ ≤ ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  calc ∑ k ∈ A, sY Y k
      ≤ ∑ k ∈ A, ∑ p ∈ T, (if p ∣ k then 1 / (p : ℝ) else 0) := Finset.sum_le_sum hstep
    _ = ∑ p ∈ T, ∑ k ∈ A, (if p ∣ k then 1 / (p : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ T, (M : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p := by
          exact_mod_cast (Finset.mem_filter.mp hp).2.pos
        rw [← Finset.sum_filter]
        have hcard : ((A.filter (p ∣ ·)).card : ℝ) ≤ (M : ℝ) / p := by
          have h1 := Nat.Ioc_filter_dvd_card_eq_div M p
          calc ((A.filter (p ∣ ·)).card : ℝ) = ((M / p : ℕ) : ℝ) := by exact_mod_cast h1
            _ ≤ (M : ℝ) / p := Nat.cast_div_le
        rw [Finset.sum_const, nsmul_eq_mul]
        calc ((A.filter (p ∣ ·)).card : ℝ) * (1 / (p : ℝ))
            ≤ (M : ℝ) / p * (1 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = (M : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by field_simp
    _ = (M : ℝ) * ∑ p ∈ T, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ∑ i ∈ Finset.Ioo Y (M + 1), ((i : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Ioo.mpr ⟨this.1, by omega⟩
        · intro i _ _; positivity
    _ ≤ (M : ℝ) * (2 / (Y + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le Y (M + 1)) (Nat.cast_nonneg M)
    _ ≤ 2 * M / Y := by
        have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hY0]
        nlinarith [Nat.cast_nonneg (α := ℝ) M]

lemma rho_pos (Y : ℕ) : 0 < rho Y := Finset.prod_pos fun p hp => one_sub_inv_pos (prime_of_mem_primesTo hp)

lemma totient_ge (Y n : ℕ) : (n : ℝ) * (rho Y * (1 - sY Y n)) ≤ φ n := by
  rw [totient_eq_mul_prod]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ Y)]
  set P1 := ∏ p ∈ n.primeFactors.filter (fun p => p ≤ Y), (1 - 1 / (p : ℝ))
  set P2 := ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ Y), (1 - 1 / (p : ℝ))
  have h1 : rho Y ≤ P1 := by
    apply prod_anti
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hp'.2⟩, hpr p hp'.1⟩
    · intro p hp; exact prime_of_mem_primesTo hp
  have h2 : 1 - sY Y n ≤ P2 := by
    apply one_sub_sum_le_prod
    · intro p _; positivity
    · intro p hp
      have := (hpr p (Finset.mem_filter.mp hp).1).one_lt
      rw [div_le_one (by positivity)]; exact_mod_cast this.le
  have h3 : 0 ≤ P2 := Finset.prod_nonneg fun p hp => (one_sub_inv_pos (hpr p (Finset.mem_filter.mp hp).1)).le
  have h4 := (rho_pos Y).le
  nlinarith

lemma hd_S_small (Y : ℕ) (hY : 1 ≤ Y) {ε v : ℝ} (hε : ε ≤ rho Y / 2) (hv : (S ε).HasDensity v) :
    v ≤ 4 / Y := by
  classical
  rw [hasDensity_iff] at hv
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  apply le_of_tendsto hv
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb', cnt_eq_card]
  set B := (Finset.Ioc 0 b).filter (fun n => (1 : ℝ) / 2 ≤ sY Y n)
  have hsub : (Finset.range b).filter (· ∈ S ε) ⊆ B := by
    intro n hn
    obtain ⟨hnb, hnS⟩ := Finset.mem_filter.mp hn
    have hnS' : (φ n : ℝ) < ε * n := hnS
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hnS'
      · exact h
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, (Finset.mem_range.mp hnb).le⟩, ?_⟩
    by_contra hlt
    push_neg at hlt
    have := totient_ge Y n
    have hr := rho_pos Y
    have : (n : ℝ) * (rho Y / 2) < n * (rho Y * (1 - sY Y n)) := by
      apply mul_lt_mul_of_pos_left _ hn0'; nlinarith
    nlinarith
  have hcard : (1 / 2 : ℝ) * B.card ≤ 2 * b / Y := by
    calc (1 / 2 : ℝ) * B.card = ∑ n ∈ B, (1 / 2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ B, sY Y n := Finset.sum_le_sum fun n hn => (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ Finset.Ioc 0 b, sY Y n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun n _ _ => Finset.sum_nonneg fun p _ => by positivity
      _ ≤ 2 * b / Y := sum_sY_le Y b hY
  have h1 : (((Finset.range b).filter (· ∈ S ε)).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card hsub
  have : (B.card : ℝ) ≤ 4 * b / Y := by
    have : (4 : ℝ) * b / Y = 2 * (2 * b / Y) := by ring
    rw [this]; linarith
  calc (((Finset.range b).filter (· ∈ S ε)).card : ℝ) ≤ 4 * b / Y := h1.trans this
    _ = 4 / Y * b := by ring

/- ### 8. Assembly -/

lemma hd_univ : (Set.univ : Set ℕ).HasDensity 1 := by
  rw [hasDensity_iff]
  have : ∀ b : ℕ, cnt Set.univ b = b := by
    intro b; unfold cnt
    rw [Set.univ_inter, show (Set.Iio b : Set ℕ) = ↑(Finset.range b) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [this]
  have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

lemma hd_zero : ({0} : Set ℕ).HasDensity 0 := by
  rw [hasDensity_iff]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat (fun b => by positivity) (fun b => ?_)
  have : cnt {0} b ≤ 1 := by
    unfold cnt
    calc ({0} ∩ Set.Iio b : Set ℕ).ncard ≤ ({0} : Set ℕ).ncard :=
          Set.ncard_le_ncard Set.inter_subset_left (Set.finite_singleton 0)
      _ = 1 := Set.ncard_singleton 0
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have h' : (cnt {0} b : ℝ) ≤ 1 := by
      have h := (Nat.cast_le (α := ℝ)).mpr this
      simpa using h
    exact div_le_div_of_nonneg_right h' (Nat.cast_nonneg _)

lemma S_nonpos {c : ℝ} (hc : c ≤ 0) : S c = ∅ := by
  ext n
  simp only [S, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  have : c * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg n)
  have : (0 : ℝ) ≤ φ n := Nat.cast_nonneg _
  linarith

lemma S_gt_one {c : ℝ} (hc : 1 < c) : S c = Set.univ \ {0} := by
  ext n
  simp only [S, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  constructor
  · rintro h rfl; simp at h
  · intro hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : (φ n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
    nlinarith

/-- FC's hypothesis gives a density of `S(c)` for every real `c`. -/
lemma hS_of_hf {f : ℝ → ℝ} (hf : IsDistributionOfPhiRatio f) : ∀ c : ℝ, ∃ v, (S c).HasDensity v := by
  intro c
  by_cases h0 : c < 0
  · exact ⟨0, (S_nonpos h0.le) ▸ hd_empty⟩
  by_cases h1 : 1 < c
  · exact ⟨1 - 0, (S_gt_one h1) ▸ hd_diff hd_univ hd_zero (Set.subset_univ _)⟩
  push_neg at h0 h1
  exact ⟨f c, hf c ⟨h0, h1⟩⟩

lemma exists_rho_lt {δ : ℝ} (hδ : 0 < δ) : ∃ N, 2 ≤ N ∧ rho N < δ := by
  obtain ⟨L, -, hL⟩ := Residual.exists_sprod_lt 0 hδ
  refine ⟨L + 2, by omega, lt_of_le_of_lt ?_ hL⟩
  apply prod_anti
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      by have := (Finset.mem_Ico.mp hp'.1).2; omega⟩, hp'.2⟩
  · intro p hp; exact prime_of_mem_primesTo hp

/-- **R4a.** For every `f` with `IsDistributionOfPhiRatio f`, `f` is continuous on `[0,1]`: the first conjunct of
FC's `IsPurelySingularOn f (Icc 0 1)`. -/
theorem continuousOn (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) : ContinuousOn f (Set.Icc 0 1) := by
  have hS := hS_of_hf hf
  choose F hF using hS
  have hfF : ∀ c ∈ Set.Icc (0 : ℝ) 1, f c = F c := fun c hc => hd_unique (hf c hc) (hF c)
  have hmono : ∀ {x y : ℝ}, x ≤ y → F x ≤ F y := fun {x y} hxy =>
    hd_le (hF x) (hF y) (fun n hn => lt_of_lt_of_le hn
      (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg n)))
  have hF0 : F 0 = 0 := hd_unique (hF 0) ((S_nonpos le_rfl) ▸ hd_empty)
  intro c hc
  rw [Metric.continuousWithinAt_iff]
  intro δ hδ
  rcases eq_or_lt_of_le hc.1 with hc0 | hc0
  · -- `c = 0`
    subst hc0
    obtain ⟨Y, hY⟩ := exists_nat_gt (4 / δ)
    have hY1 : 1 ≤ Y := by
      have : (0 : ℝ) < Y := lt_trans (by positivity) hY
      exact_mod_cast this
    have hYδ : 4 / (Y : ℝ) < δ := by
      have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
      rw [div_lt_iff₀ hY0]; rw [div_lt_iff₀ hδ] at hY; linarith
    refine ⟨rho Y / 2, by have := rho_pos Y; positivity, fun {x} hx hdx => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1] at hdx
    rw [Real.dist_eq, hfF x hx, hfF 0 hc, hF0, sub_zero]
    have hle : F x ≤ F (rho Y / 2) := hmono hdx.le
    have hsmall := hd_S_small Y hY1 le_rfl (hF (rho Y / 2))
    have hnn : 0 ≤ F x := hd_nonneg (hF x)
    rw [abs_of_nonneg hnn]
    linarith
  · -- `c > 0`
    obtain ⟨N, hN, hNδ⟩ := exists_rho_lt hδ
    have hS' : ∀ c : ℝ, ∃ v, (S c).HasDensity v := fun c => ⟨F c, hF c⟩
    obtain ⟨ε, hε, hε0⟩ := ((band_le hN hS' hc0).and self_mem_nhdsWithin).exists
    have hε0' : (0 : ℝ) < ε := hε0
    have hsum : ∀ x, F x = ∑ T ∈ (primesTo N).powerset, G N (x / h T) / w T :=
      fun x => hd_unique (hF x) (hd_S_sum hN hS' x)
    have hgap : F (c + ε) - F (c - ε) < δ := by
      rw [hsum, hsum]
      exact lt_of_le_of_lt ((sum_diff_le hN hS' hε0'.le).trans hε) hNδ
    refine ⟨ε, hε0', fun {x} hx hdx => ?_⟩
    rw [Real.dist_eq, abs_lt] at hdx
    rw [Real.dist_eq, hfF x hx, hfF c hc, abs_lt]
    have h1 : F (c - ε) ≤ F x := hmono (by linarith)
    have h2 : F x ≤ F (c + ε) := hmono (by linarith)
    have h3 : F (c - ε) ≤ F c := hmono (by linarith)
    have h4 : F c ≤ F (c + ε) := hmono (by linarith)
    constructor <;> linarith

/-- **R4a, in FC's vocabulary.** Given `hf`, FC's `erdos_50_singular` (`IsPurelySingularOn f (Icc 0 1)`) is
equivalent to its almost-everywhere part alone: the continuity conjunct is `continuousOn`. -/
theorem singular_iff_ae (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) :
    IsPurelySingularOn f (Set.Icc 0 1) ↔
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)), derivWithin f (Set.Icc 0 1) x = 0 :=
  ⟨fun h => h.2, fun h => ⟨continuousOn f hf, h⟩⟩

end Cont
end Erdos50
end
end

-- Erdos50FC.SingularAnalysis
section
/-
# Erdős #50, rung R4b-1: the real-analysis half of `f' = 0` a.e.

No number theory here.

* `ae_zero_of_covers`: a function monotone on `[0,1]` whose derivative puts at least a fixed fraction `c`
  of its total integral (up to `ε`) on sets of Lebesgue measure `≤ ε`, for every `ε > 0`, has
  `derivWithin f (Icc 0 1) = 0` a.e. on `[0,1]` (absolute continuity of the integral of `f' ∈ L¹`).
* `cover_ineq`: for `F x = ∑ᵢ aᵢ G(x/hᵢ)` with `G` monotone and constant on `(1,∞)`, writing
  `B = ∫₀¹ G'`: `∫₀¹ F' = (∑ aᵢ) B`, and on `U = ⋃_{i ∈ good} (hᵢ(1-ηᵢ), hᵢ)`,
  `∫_U F' ≥ ∑_{i∈good} aᵢ (B - (G(1-ηᵢ) - G 0))`, with `vol U ≤ ∑_{i∈good} hᵢ ηᵢ`.
  The copies `G(·/hᵢ)` all carry the same share `B` of derivative mass, which is the whole point.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Erdos50
namespace Sing

/- ### Part A: covers force `f' = 0` a.e. -/

lemma deriv_nonneg_of_monotoneOn {f : ℝ → ℝ} (hmono : MonotoneOn f (Icc 0 1)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ deriv f x := by
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact hmono.derivWithin_nonneg

lemma integrableOn_deriv {f : ℝ → ℝ} (hmono : MonotoneOn f (Icc 0 1)) :
    IntegrableOn (deriv f) (Ioo (0 : ℝ) 1) := by
  have h := (MonotoneOn.intervalIntegrable_deriv (a := 0) (b := 1)
    (by rwa [uIcc_of_le zero_le_one])).1
  exact h.mono_set Ioo_subset_Ioc_self

/-- **Covers force `f' = 0` a.e.** -/
theorem ae_zero_of_covers {f : ℝ → ℝ} (hmono : MonotoneOn f (Icc 0 1)) {c : ℝ} (hc : 0 < c)
    (hcov : ∀ ε > 0, ∃ U ⊆ Ioo (0 : ℝ) 1, MeasurableSet U ∧ volume U ≤ ENNReal.ofReal ε ∧
      c * (∫ x in Ioo (0 : ℝ) 1, deriv f x) - ε ≤ ∫ x in U, deriv f x) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), derivWithin f (Icc 0 1) x = 0 := by
  have hint := integrableOn_deriv hmono
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv f := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun x hx => deriv_nonneg_of_monotoneOn hmono hx
  set A := ∫ x in Ioo (0 : ℝ) 1, deriv f x with hA
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioo fun x hx => deriv_nonneg_of_monotoneOn hmono hx
  -- absolute continuity: `c * A ≤ δ'` for every `δ' > 0`
  have hsmall : ∀ δ' > 0, c * A ≤ δ' := by
    intro δ' hδ'
    have hfin : ∫⁻ x, ‖deriv f x‖ₑ ∂(volume.restrict (Ioo (0 : ℝ) 1)) ≠ ∞ :=
      (hasFiniteIntegral_iff_enorm.mp hint.2).ne
    obtain ⟨δ, hδ0, hδ⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin
      (ε := ENNReal.ofReal (δ' / 2)) (by simp [hδ'])
    obtain ⟨ε0, hε0, hε0δ⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ ENNReal.ofReal ε0 < δ := by
      obtain ⟨r, -, hr0, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ0
      exact ⟨r, ENNReal.ofReal_pos.mp hr0, hrδ⟩
    set ε := min ε0 (δ' / 2) with hε
    have hε0' : 0 < ε := lt_min hε0 (by linarith)
    obtain ⟨U, hUsub, hUm, hUvol, hUint⟩ := hcov ε hε0'
    have hμU : volume.restrict (Ioo (0 : ℝ) 1) U < δ := by
      rw [Measure.restrict_apply hUm]
      calc volume (U ∩ Ioo 0 1) ≤ volume U := measure_mono inter_subset_left
        _ ≤ ENNReal.ofReal ε := hUvol
        _ ≤ ENNReal.ofReal ε0 := ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ < δ := hε0δ
    have hl := hδ U hμU
    rw [Measure.restrict_restrict hUm, inter_eq_left.mpr hUsub] at hl
    have hle : ∫ x in U, deriv f x ≤ δ' / 2 := by
      have h1 : ‖∫ x in U, deriv f x‖ ≤ (∫⁻ x in U, ENNReal.ofReal ‖deriv f x‖).toReal :=
        norm_integral_le_lintegral_norm _
      have h2 : ∫⁻ x in U, ENNReal.ofReal ‖deriv f x‖ = ∫⁻ x in U, ‖deriv f x‖ₑ := by
        congr 1; ext x; exact ofReal_norm _
      rw [h2] at h1
      have h3 : (∫⁻ x in U, ‖deriv f x‖ₑ).toReal ≤ δ' / 2 := by
        rw [← ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ δ' / 2)]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hl.le
      linarith [le_abs_self (∫ x in U, deriv f x), Real.norm_eq_abs (∫ x in U, deriv f x)]
    have : ε ≤ δ' / 2 := min_le_right _ _
    linarith
  have hcA : c * A ≤ 0 := le_of_forall_pos_le_add fun δ' hδ' => by simpa using hsmall δ' hδ'
  have hA' : A = 0 := le_antisymm (by nlinarith) hA0
  have hz : deriv f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).mp hA'
  rw [← restrict_Ioo_eq_restrict_Icc]
  have hmem : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hz, hmem] with x hx hxm
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxm.1 hxm.2)]
  exact hx

/- ### Part B: the cover inequality for `F = ∑ᵢ aᵢ G(·/hᵢ)` -/

section PartB

variable {G : ℝ → ℝ}

lemma deriv_scale (G : ℝ → ℝ) (h x : ℝ) :
    deriv (fun y => G (y / h)) x = h⁻¹ * deriv G (x / h) := by
  have : (fun y => G (y / h)) = fun y => G (h⁻¹ * y) := by ext y; rw [div_eq_inv_mul]
  rw [this, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]

lemma mono_scale (hG : Monotone G) {h : ℝ} (hh : 0 < h) : Monotone fun y => G (y / h) :=
  fun _ _ hxy => hG (div_le_div_of_nonneg_right hxy hh.le)

lemma iint_deriv (hG : Monotone G) (u v : ℝ) : IntervalIntegrable (deriv G) volume u v :=
  (hG.monotoneOn _).intervalIntegrable_deriv

/-- `∫ᵤᵛ (G(·/h))' = ∫_{u/h}^{v/h} G'`. -/
lemma integral_deriv_scale (G : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (u v : ℝ) :
    ∫ x in u..v, deriv (fun y => G (y / h)) x = ∫ x in u / h..v / h, deriv G x := by
  simp_rw [deriv_scale]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div (f := deriv G) hh.ne',
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

lemma deriv_eq_zero_of_gt_one (hG1 : ∀ x y : ℝ, 1 < x → 1 < y → G x = G y) {x : ℝ} (hx : 1 < x) :
    deriv G x = 0 := by
  have : G =ᶠ[𝓝 x] fun _ => G x :=
    Filter.mem_of_superset (Ioi_mem_nhds hx) fun y hy => hG1 y x hy hx
  rw [this.deriv_eq, deriv_const]

variable {ι : Type*} (I : Finset ι) (a h : ι → ℝ)

/-- a.e. derivative of `F = ∑ᵢ aᵢ G(·/hᵢ)`. -/
lemma deriv_F_ae (hG : Monotone G) (hh : ∀ i ∈ I, 0 < h i) :
    ∀ᵐ x, deriv (fun y => ∑ i ∈ I, a i * G (y / h i)) x =
      ∑ i ∈ I, a i * deriv (fun y => G (y / h i)) x := by
  have hall : ∀ᵐ x, ∀ i ∈ I, DifferentiableAt ℝ (fun y => G (y / h i)) x :=
    (eventually_all_finset I).mpr fun i hi => (mono_scale hG (hh i hi)).ae_differentiableAt
  filter_upwards [hall] with x hx
  rw [deriv_fun_sum (fun i hi => (hx i hi).const_mul (a i))]
  exact Finset.sum_congr rfl fun i hi => deriv_const_mul _ (hx i hi)

lemma iint_term (hG : Monotone G) {hi : ℝ} (hh : 0 < hi) (ai u v : ℝ) :
    IntervalIntegrable (fun x => ai * deriv (fun y => G (y / hi)) x) volume u v :=
  (((mono_scale hG hh).monotoneOn _).intervalIntegrable_deriv).const_mul ai

/-- **(i)** `∫₀¹ F' = (∑ aᵢ) ∫₀¹ G'`. -/
lemma integral_F (hG : Monotone G) (hG1 : ∀ x y : ℝ, 1 < x → 1 < y → G x = G y)
    (hh : ∀ i ∈ I, 0 < h i) (hh1 : ∀ i ∈ I, h i ≤ 1) :
    ∫ x in (0 : ℝ)..1, deriv (fun y => ∑ i ∈ I, a i * G (y / h i)) x =
      (∑ i ∈ I, a i) * ∫ x in (0 : ℝ)..1, deriv G x := by
  rw [intervalIntegral.integral_congr_ae ((deriv_F_ae I a h hG hh).mono fun x hx _ => hx),
    intervalIntegral.integral_finsetSum (fun i hi => iint_term hG (hh i hi) _ _ _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_const_mul, integral_deriv_scale G (hh i hi), zero_div]
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (iint_deriv hG _ _) (iint_deriv hG _ _)]
  have h1 : 1 ≤ 1 / h i := by rw [le_div_iff₀ (hh i hi)]; simpa using hh1 i hi
  have hz : ∫ x in (1 : ℝ)..1 / h i, deriv G x = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro x hx
    rw [uIoo_of_le h1] at hx
    exact deriv_eq_zero_of_gt_one hG1 hx.1
  rw [hz, add_zero]

/-- The cover `U = ⋃_{i ∈ good} (hᵢ(1-ηᵢ), hᵢ)`. -/
def U (good : Finset ι) (h η : ι → ℝ) : Set ℝ := ⋃ i ∈ good, Ioo (h i * (1 - η i)) (h i)

lemma measurableSet_U (good : Finset ι) (h η : ι → ℝ) : MeasurableSet (U good h η) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ioo

lemma U_subset (good : Finset ι) (η : ι → ℝ) (hh : ∀ i ∈ good, 0 < h i) (hh1 : ∀ i ∈ good, h i ≤ 1)
    (hη : ∀ i ∈ good, η i < 1) : U good h η ⊆ Ioo 0 1 := by
  intro x hx
  simp only [U, mem_iUnion, mem_Ioo] at hx
  obtain ⟨i, hi, h1, h2⟩ := hx
  have := mul_pos (hh i hi) (sub_pos.mpr (hη i hi))
  exact ⟨by linarith, by linarith [hh1 i hi]⟩

lemma volume_U (good : Finset ι) (η : ι → ℝ) :
    volume (U good h η) ≤ ∑ i ∈ good, ENNReal.ofReal (h i * η i) := by
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Real.volume_Ioo]; apply le_of_eq; congr 1; ring

/-- **(ii)** the cover inequality. -/
lemma cover_ineq (hG : Monotone G) (hh : ∀ i ∈ I, 0 < h i) (hh1 : ∀ i ∈ I, h i ≤ 1)
    (ha : ∀ i ∈ I, 0 ≤ a i) (good : Finset ι) (hgood : good ⊆ I) (η : ι → ℝ)
    (hη0 : ∀ i ∈ good, 0 ≤ η i) (hη1 : ∀ i ∈ good, η i < 1) :
    ∑ i ∈ good, a i * ((∫ x in (0 : ℝ)..1, deriv G x) - (G (1 - η i) - G 0)) ≤
      ∫ x in U good h η, deriv (fun y => ∑ i ∈ I, a i * G (y / h i)) x := by
  have hUm := measurableSet_U good h η
  have hUs : U good h η ⊆ Icc 0 1 :=
    (U_subset h good η (fun i hi => hh i (hgood hi)) (fun i hi => hh1 i (hgood hi)) hη1).trans
      Ioo_subset_Icc_self
  have hInt : ∀ i ∈ I, IntegrableOn (fun x => a i * deriv (fun y => G (y / h i)) x) (Icc 0 1) := by
    intro i hi
    have := (iint_term hG (hh i hi) (a i) 0 1)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at this
    exact this
  have hnn : ∀ i ∈ I, ∀ x, 0 ≤ a i * deriv (fun y => G (y / h i)) x := fun i hi x =>
    mul_nonneg (ha i hi) (mono_scale hG (hh i hi)).deriv_nonneg
  rw [setIntegral_congr_ae hUm ((deriv_F_ae I a h hG hh).mono fun x hx _ => hx),
    integral_finsetSum _ (fun i hi => (hInt i hi).mono_set hUs)]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hgood fun i hi _ =>
    setIntegral_nonneg hUm fun x _ => hnn i hi x)
  refine Finset.sum_le_sum fun i hi => ?_
  have hiI := hgood hi
  have hhi := hh i hiI
  have hJ : Ioo (h i * (1 - η i)) (h i) ⊆ U good h η := by
    intro x hx; simp only [U, mem_iUnion]; exact ⟨i, hi, hx⟩
  have hle : h i * (1 - η i) ≤ h i := by nlinarith [hη0 i hi]
  calc a i * ((∫ x in (0 : ℝ)..1, deriv G x) - (G (1 - η i) - G 0))
      ≤ a i * ∫ x in (1 - η i)..1, deriv G x := by
        apply mul_le_mul_of_nonneg_left _ (ha i hiI)
        rw [← intervalIntegral.integral_interval_sub_left (iint_deriv hG 0 1) (iint_deriv hG 0 (1 - η i))]
        have hmem := (hG.monotoneOn (uIcc 0 (1 - η i))).intervalIntegral_deriv_mem_uIcc
        have hGle : G 0 ≤ G (1 - η i) := hG (by linarith [hη1 i hi])
        rw [uIcc_of_le (by linarith)] at hmem
        linarith [hmem.2]
    _ = ∫ x in Ioo (h i * (1 - η i)) (h i), a i * deriv (fun y => G (y / h i)) x := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
          intervalIntegral.integral_const_mul, integral_deriv_scale G hhi, mul_div_cancel_left₀ _ hhi.ne',
          div_self hhi.ne']
    _ ≤ ∫ x in U good h η, a i * deriv (fun y => G (y / h i)) x :=
        setIntegral_mono_set ((hInt i hiI).mono_set hUs)
          (Eventually.of_forall fun x => hnn i hiI x) (Eventually.of_forall hJ)

end PartB

end Sing
end Erdos50
end

-- LeanClassics.SquarefreeCount
section
/-
# Squarefree numbers: `#{n ≤ N squarefree} = 6N/π² + O(√N)`

`abs_card_squarefree_sub_le`: for `N ≥ 1`, `|#{1 ≤ n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`.

Proof. `μ(n)² = ∑_{d² ∣ n} μ(d)` (`sum_moebius_sq_dvd`, writing `n = b² a` with `a` squarefree,
so that `d² ∣ n ↔ d ∣ b`), hence `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`
(`sum_moebius_sq_eq`). Then `∑_d μ(d)/d² = 1/ζ(2) = 6/π²` (`tsum_moebius_div_sq`, from Mathlib's
`LSeries_zeta_mul_Lseries_moebius` and `riemannZeta_two`), whose tail beyond `M` is at most `1/M`
(`tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeCount

/-- With `a` squarefree, `d² ∣ b² a ↔ d ∣ b`. -/
lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0) :
    d * d ∣ b ^ 2 * a ↔ d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  constructor
  · intro h
    rw [← Nat.factorization_le_iff_dvd hd hb]
    rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)] at h
    intro p
    have hp := h p
    have h1 := ha.natFactorization_le_one p
    rw [Nat.factorization_mul hd hd, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
      Nat.factorization_pow] at hp
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
    omega
  · intro h
    exact (Nat.mul_dvd_mul h h).trans (by rw [sq]; exact Dvd.intro a rfl)

/-- `∑_{d² ∣ n} μ(d) = μ(n)²` for `n ≠ 0`. -/
lemma sum_moebius_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d * d ∣ n, (μ d : ℤ) = μ n ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hfil : n.divisors.filter (fun d => d * d ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hn h
      exact ⟨(sq_dvd_iff ha hb hd).mp (hab ▸ h), hb⟩
    · rintro ⟨h, -⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hb h
      have h2 := (sq_dvd_iff ha hb hd).mpr h
      rw [hab] at h2
      exact ⟨⟨(Dvd.intro d rfl).trans h2, hn⟩, h2⟩
  rw [hfil, moebius_sq]
  have hz : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f b) moebius_mul_coe_zeta
    simp only [coe_mul_zeta_apply, one_apply] at this
    exact this
  rw [hz]
  by_cases hb1 : b = 1
  · subst hb1
    simp only [one_pow, one_mul] at hab
    simp [hab ▸ ha]
  · have hns : ¬ Squarefree n := fun hs => hb1 (Nat.isUnit_iff.mp
      (hs b (by rw [← hab, sq]; exact Dvd.intro a rfl)))
    simp [hb1, hns]

/-- `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`. -/
lemma sum_moebius_sq_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (μ n : ℤ) ^ 2 =
      ∑ d ∈ Ioc 0 (Nat.sqrt N), (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
  have h1 : ∀ n ∈ Ioc 0 N, (μ n : ℤ) ^ 2 =
      ∑ d ∈ Ioc 0 N, if d * d ∣ n then (μ d : ℤ) else 0 := fun n hn => by
    have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
    rw [← sum_moebius_sq_dvd hn0, sum_ite, sum_const_zero, add_zero]
    congr 1
    ext d
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, h⟩
      have hd0 : d ≠ 0 := by rintro rfl; simp at h; exact hn0 h
      exact ⟨⟨Nat.pos_of_ne_zero hd0, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn).trans
        (mem_Ioc.mp hn).2⟩, h⟩
    · rintro ⟨⟨hd0, -⟩, h⟩
      exact ⟨⟨(Dvd.intro d rfl).trans h, hn0⟩, h⟩
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ d ∈ Ioc 0 N, (∑ n ∈ Ioc 0 N, if d * d ∣ n then (μ d : ℤ) else 0) =
      (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := fun d _ => by
    rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  rw [sum_congr rfl h2]
  symm
  refine sum_subset (Ioc_subset_Ioc_right (Nat.sqrt_le_self N)) fun d hd hnd => ?_
  have hd' : Nat.sqrt N < d := by
    simp only [mem_Ioc, not_and, not_le] at hd hnd; exact hnd hd.1
  have : N < d * d := by
    have := Nat.lt_succ_sqrt' N
    rw [sq] at this
    exact this.trans_le (Nat.mul_le_mul hd' hd')
  rw [Nat.div_eq_of_lt this]
  simp

/-- `∑ μ(d)/d² = 6/π²`. -/
lemma tsum_moebius_div_sq : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = 6 / π ^ 2 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hL : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (π : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hπ)]
    linear_combination (6 : ℂ) * h
  have hc : ((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) = LSeries (fun n => (μ n : ℂ)) 2 := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn]
    push_cast
    norm_cast
  have := hc.trans hL
  exact_mod_cast this

lemma summable_moebius_div_sq : Summable fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2 := by
  refine (Real.summable_one_div_nat_pow.mpr one_lt_two).of_norm_bounded fun d => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
  have : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  exact div_le_div_of_nonneg_right this (by positivity)

/-- `|∑ μ(d)/d² − ∑_{d ≤ M} μ(d)/d²| ≤ 1/M` for `M ≥ 1`. -/
lemma tail_le {M : ℕ} (hM : 1 ≤ M) :
    |6 / π ^ 2 - ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2| ≤ 1 / (M : ℝ) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2
  have e := summable_moebius_div_sq.sum_add_tsum_nat_add (M + 1)
  have hI : Ioc 0 M = Ico 1 (M + 1) := by ext; simp; omega
  have hR : ∑ d ∈ range (M + 1), f d = ∑ d ∈ Ioc 0 M, f d := by
    rw [sum_range_succ', hI, sum_Ico_eq_sum_range]
    simp [f, add_comm]
  rw [← tsum_moebius_div_sq, ← e, hR]
  simp only [add_sub_cancel_left]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : ∀ k : ℕ, |f (k + (M + 1))| ≤ 1 / ((k : ℝ) + M) - 1 / ((k : ℝ) + 1 + M) := fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + M := by positivity
    have h1 : |f (k + (M + 1))| ≤ 1 / (((k : ℝ) + 1 + M)) ^ 2 := by
      simp only [f, abs_div]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + (M + 1) : ℕ) : ℝ) ^ 2)]
      have : |(μ (k + (M + 1)) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      refine (div_le_div_of_nonneg_right this (by positivity)).trans (le_of_eq ?_)
      push_cast; ring_nf
    refine h1.trans ?_
    rw [div_sub_div _ _ hk.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsb : Summable fun k : ℕ => |f (k + (M + 1))| :=
    ((summable_nat_add_iff (M + 1)).mpr summable_moebius_div_sq).abs
  have hn := norm_tsum_le_tsum_norm (f := fun k => f (k + (M + 1)))
    (by simpa only [Real.norm_eq_abs] using hsb)
  simp only [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun n => ?_
  refine (sum_le_sum fun k _ => hb k).trans ?_
  have := sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + M)) n
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]
  simp only [Nat.cast_zero, zero_add, sub_le_self_iff]
  positivity

/-- **The number of squarefree `n ≤ N` is `6N/π² + O(√N)`**: for `N ≥ 1`,
`|#{n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`. -/
theorem abs_card_squarefree_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |((((Ioc 0 N).filter Squarefree).card : ℕ) : ℝ) - 6 * N / π ^ 2| ≤ 5 * √(N : ℝ) := by
  set M := Nat.sqrt N
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMs : (M : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hsM : √(N : ℝ) < M + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hNs : (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
  -- the count as a sum over `d ≤ M`
  have hcZ : ((((Ioc 0 N).filter Squarefree).card : ℕ) : ℤ) =
      ∑ d ∈ Ioc 0 M, (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
    rw [← sum_moebius_sq_eq, sum_congr rfl (fun n _ => moebius_sq), sum_boole]
  have hc : ((((Ioc 0 N).filter Squarefree).card : ℕ) : ℝ) =
      ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcZ
    push_cast at this
    exact this
  -- floor errors
  have hE : |(N : ℝ) * ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2 -
      ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)| ≤ M := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ d ∈ Ioc 0 M, |(N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) -
        (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)| ≤ 1 := fun d hd => by
      have hd0 : 0 < d * d := Nat.mul_pos (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).1
      have hdr : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast hd0
      have e : (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) - (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) =
          (μ d : ℝ) * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ)) := by
        push_cast; ring
      rw [e, abs_mul]
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hdm := Nat.div_add_mod N (d * d)
      have hlt : N % (d * d) < d * d := Nat.mod_lt _ hd0
      have eN : (N : ℝ) = ((d * d : ℕ) : ℝ) * ((N / (d * d) : ℕ) : ℝ) +
          ((N % (d * d) : ℕ) : ℝ) := by exact_mod_cast hdm.symm
      have hlt' : ((N % (d * d) : ℕ) : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast hlt
      have h0 : 0 ≤ (N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ) := by
        rw [sub_nonneg]; exact Nat.cast_div_le
      have h1 : (N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ) ≤ 1 := by
        rw [div_sub' hdr.ne', div_le_one hdr, eN]
        nlinarith
      rw [abs_of_nonneg h0]
      calc |(μ d : ℝ)| * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))
          ≤ 1 * 1 := mul_le_mul hμ h1 h0 zero_le_one
        _ = 1 := by ring
    refine (sum_le_sum this).trans ?_
    simp
  have hT := tail_le hM1
  -- `N/M ≤ 4M`
  have hNlt : (N : ℝ) < ((M : ℝ) + 1) ^ 2 := by
    rw [hNs]; exact pow_lt_pow_left₀ hsM (by positivity) (by norm_num)
  have hNM : (N : ℝ) / M ≤ 4 * M := by
    rw [div_le_iff₀ hMpos]; nlinarith
  set S := ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2
  set Q := ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)
  have key : Q - 6 * N / π ^ 2 = -((N : ℝ) * S - Q) - N * (6 / π ^ 2 - S) := by ring
  rw [hc, key]
  have h2 : |(N : ℝ) * (6 / π ^ 2 - S)| ≤ 4 * (M : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc (N : ℝ) * |6 / π ^ 2 - S| ≤ N * (1 / M) :=
          mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg N)
      _ = N / M := by ring
      _ ≤ 4 * (M : ℝ) := hNM
  calc |-((N : ℝ) * S - Q) - N * (6 / π ^ 2 - S)|
      ≤ |(N : ℝ) * S - Q| + |(N : ℝ) * (6 / π ^ 2 - S)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ ≤ (M : ℝ) + 4 * (M : ℝ) := add_le_add hE h2
    _ ≤ 5 * √(N : ℝ) := by linarith

end LeanClassics.SquarefreeCount
end
end

-- LeanClassics.TotientSum
section
/-
# `∑_{n ≤ N} φ(n) = 3N²/π² + O(N log N)`

`abs_sum_totient_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n) − 3N²/π²| ≤ N (log N + 1)`.

Proof. Möbius inversion of `∑_{d ∣ n} φ(d) = n` (Mathlib's `Nat.sum_totient` and
`sum_eq_iff_sum_mul_moebius_eq`) gives `φ = μ * id`, so
`∑_{n ≤ N} φ(n) = ∑_{a ≤ N} μ(a) K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `μ(a) N²/(2a²)` up to `N/(2a)`; the sum of these
errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`), and
`(N²/2) |6/π² − ∑_{a ≤ N} μ(a)/a²| ≤ N/2` (`SquarefreeCount.tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.TotientSum

open LeanClassics.SquarefreeCount (tail_le)

/-- `∑_{n ≤ N} φ(n) = ∑_{a ≤ N} μ(a) ∑_{b ≤ N/a} b`. -/
lemma sum_totient_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n.totient : ℤ) =
      ∑ a ∈ Ioc 0 N, (μ a : ℤ) * ∑ b ∈ Ioc 0 (N / a), (b : ℤ) := by
  set g : ArithmeticFunction ℤ := ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
    ArithmeticFunction ℤ)
  have hg : ∀ n, g n = (n : ℤ) := fun n => by simp [g]
  have hφ : ∀ n > 0, (((μ : ArithmeticFunction ℤ) * g) n) = (n.totient : ℤ) := by
    have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun n => (n.totient : ℤ))
      (g := fun n => (n : ℤ))).mp fun n _ => by exact_mod_cast Nat.sum_totient n
    intro n hn
    rw [mul_apply, ← h n hn]
    refine sum_congr rfl fun x _ => ?_
    rw [hg, Int.cast_id]
  rw [← sum_congr rfl fun n hn => hφ n (mem_Ioc.mp hn).1, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [hg]

lemma gauss (K : ℕ) : ∑ b ∈ Ioc 0 K, (b : ℝ) = K * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le K), ih]
    push_cast; ring

/-- `|K(K + 1)/2 − x²/2| ≤ x/2` for `K = ⌊x⌋`, `x = N/a ≥ 1`. -/
lemma term_le {N a : ℕ} (ha : a ∈ Ioc 0 N) :
    |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2|
      ≤ (N : ℝ) / a / 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
  set x := (N : ℝ) / a
  set K := ((N / a : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hKx : K ≤ x := Nat.cast_div_le
  have hx1 : 1 ≤ x := by
    rw [le_div_iff₀ ha0, one_mul]; exact_mod_cast (mem_Ioc.mp ha).2
  have hxK : x < K + 1 := by
    have hdm := Nat.div_add_mod N a
    have hlt : N % a < a := Nat.mod_lt _ (mem_Ioc.mp ha).1
    have eN : (N : ℝ) = a * K + ((N % a : ℕ) : ℝ) := by
      simp only [K]; exact_mod_cast hdm.symm
    have hlt' : ((N % a : ℕ) : ℝ) < a := by exact_mod_cast hlt
    simp only [x]
    rw [div_lt_iff₀ ha0, eN]
    nlinarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul (show x - 1 ≤ K by linarith) (le_of_lt hxK) (by linarith) hK0]
  · nlinarith [mul_le_mul hKx (show K + 1 ≤ x + 1 by linarith) (by linarith) (by linarith)]

/-- **`∑_{n ≤ N} φ(n) = 3N²/π² + O(N log N)`**: for `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} φ(n) − 3N²/π²| ≤ N (log N + 1)`. -/
theorem abs_sum_totient_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - 3 * (N : ℝ) ^ 2 / π ^ 2| ≤ N * (Real.log N + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΦ : ∑ n ∈ Ioc 0 N, (n.totient : ℝ) =
      ∑ a ∈ Ioc 0 N, (μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (sum_totient_eq N)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun a _ => ?_
    rw [gauss]
  set S := ∑ a ∈ Ioc 0 N, (μ a : ℝ) / (a : ℝ) ^ 2
  have hmain : |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - (N : ℝ) ^ 2 / 2 * S| ≤
      (N : ℝ) / 2 * (1 + Real.log N) := by
    rw [hΦ, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ a ∈ Ioc 0 N, |(μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) -
        (N : ℝ) ^ 2 / 2 * ((μ a : ℝ) / (a : ℝ) ^ 2)| ≤ (N : ℝ) / 2 * (1 / (a : ℝ)) :=
      fun a ha => by
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
      have e : (μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) -
          (N : ℝ) ^ 2 / 2 * ((μ a : ℝ) / (a : ℝ) ^ 2) = (μ a : ℝ) *
          (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2) := by
        field_simp
      rw [e, abs_mul]
      have hμ : |(μ a : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      calc |(μ a : ℝ)| * |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 -
            ((N : ℝ) / a) ^ 2 / 2| ≤ 1 * ((N : ℝ) / a / 2) :=
            mul_le_mul hμ (term_le ha) (abs_nonneg _) zero_le_one
        _ = (N : ℝ) / 2 * (1 / (a : ℝ)) := by ring
    refine (sum_le_sum hb).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hH : ∑ a ∈ Ioc 0 N, 1 / (a : ℝ) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, show Icc 1 N = Ioc 0 N by ext; simp; omega]
      push_cast
      simp [one_div]
    rw [hH]
    exact harmonic_le_one_add_log N
  have hT := tail_le hN
  have h2 : |(N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2| ≤ (N : ℝ) / 2 := by
    have e : (N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2 =
        -((N : ℝ) ^ 2 / 2 * (6 / π ^ 2 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |6 / π ^ 2 - S| ≤ (N : ℝ) ^ 2 / 2 * (1 / N) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (N : ℝ) / 2 := by field_simp
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - 3 * (N : ℝ) ^ 2 / π ^ 2|
      ≤ |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - (N : ℝ) ^ 2 / 2 * S| +
        |(N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) / 2 * (1 + Real.log N) + (N : ℝ) / 2 := add_le_add hmain h2
    _ ≤ N * (Real.log N + 1) := by nlinarith

end LeanClassics.TotientSum
end
end

-- LeanClassics.SigmaSum
section
/-
# `∑_{n ≤ N} σ(n) = π²N²/12 + O(N log N)`

`abs_sum_sigma_one_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n) − π²N²/12| ≤ N (log N + 1)`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `σ = ζ * id` (Mathlib's `zeta_mul_pow_eq_sigma`), so
`∑_{n ≤ N} σ(n) = ∑_{a ≤ N} K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `N²/(2a²)` up to `N/(2a)` (`TotientSum.term_le`);
the sum of these errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`),
and `(N²/2) |π²/6 − ∑_{a ≤ N} 1/a²| ≤ N/2` (`tail_le`, from Mathlib's `hasSum_zeta_two`).
-/

open Real Finset

noncomputable section

namespace LeanClassics.SigmaSum

open LeanClassics.TotientSum (gauss term_le)

/-- `∑_{n ≤ N} σ(n) = ∑_{a ≤ N} ∑_{b ≤ N/a} b`. -/
lemma sum_sigma_one_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ArithmeticFunction.sigma 1 n =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), b := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp ha).1.ne', one_mul]
  simp

/-- `|π²/6 − ∑_{d ≤ M} 1/d²| ≤ 1/M` for `M ≥ 1`. -/
lemma tail_le {M : ℕ} (hM : 1 ≤ M) :
    |π ^ 2 / 6 - ∑ d ∈ Ioc 0 M, 1 / (d : ℝ) ^ 2| ≤ 1 / (M : ℝ) := by
  set f : ℕ → ℝ := fun d => 1 / (d : ℝ) ^ 2
  have hs : Summable f := hasSum_zeta_two.summable
  have e := hs.sum_add_tsum_nat_add (M + 1)
  have hI : Ioc 0 M = Ico 1 (M + 1) := by ext; simp; omega
  have hR : ∑ d ∈ range (M + 1), f d = ∑ d ∈ Ioc 0 M, f d := by
    rw [sum_range_succ', hI, sum_Ico_eq_sum_range]
    simp [f, add_comm]
  rw [← hasSum_zeta_two.tsum_eq, ← e, hR]
  simp only [add_sub_cancel_left]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : ∀ k : ℕ, |f (k + (M + 1))| ≤ 1 / ((k : ℝ) + M) - 1 / ((k : ℝ) + 1 + M) := fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + M := by positivity
    have h1 : |f (k + (M + 1))| ≤ 1 / (((k : ℝ) + 1 + M)) ^ 2 := by
      simp only [f]
      rw [abs_of_nonneg (by positivity)]
      push_cast; ring_nf; rfl
    refine h1.trans ?_
    rw [div_sub_div _ _ hk.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsb : Summable fun k : ℕ => |f (k + (M + 1))| :=
    ((summable_nat_add_iff (M + 1)).mpr hs).abs
  have hn := norm_tsum_le_tsum_norm (f := fun k => f (k + (M + 1)))
    (by simpa only [Real.norm_eq_abs] using hsb)
  simp only [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun n => ?_
  refine (sum_le_sum fun k _ => hb k).trans ?_
  have := sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + M)) n
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]
  simp only [Nat.cast_zero, zero_add, sub_le_self_iff]
  positivity

theorem abs_sum_sigma_one_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - π ^ 2 * (N : ℝ) ^ 2 / 12| ≤
      N * (Real.log N + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsig : ∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) =
      ∑ a ∈ Ioc 0 N, (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) := by
    have := congrArg (fun z : ℕ => (z : ℝ)) (sum_sigma_one_eq N)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun a _ => ?_
    rw [gauss]
  set S := ∑ a ∈ Ioc 0 N, 1 / (a : ℝ) ^ 2
  have hmain : |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - (N : ℝ) ^ 2 / 2 * S| ≤
      (N : ℝ) / 2 * (1 + Real.log N) := by
    rw [hsig, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ a ∈ Ioc 0 N, |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 -
        (N : ℝ) ^ 2 / 2 * (1 / (a : ℝ) ^ 2)| ≤ (N : ℝ) / 2 * (1 / (a : ℝ)) :=
      fun a ha => by
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
      have e : (N : ℝ) ^ 2 / 2 * (1 / (a : ℝ) ^ 2) = ((N : ℝ) / a) ^ 2 / 2 := by
        field_simp
      rw [e]
      calc |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2|
          ≤ (N : ℝ) / a / 2 := term_le ha
        _ = (N : ℝ) / 2 * (1 / (a : ℝ)) := by ring
    refine (sum_le_sum hb).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hH : ∑ a ∈ Ioc 0 N, 1 / (a : ℝ) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, show Icc 1 N = Ioc 0 N by ext; simp; omega]
      push_cast
      simp [one_div]
    rw [hH]
    exact harmonic_le_one_add_log N
  have hT := tail_le hN
  have h2 : |(N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12| ≤ (N : ℝ) / 2 := by
    have e : (N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12 =
        -((N : ℝ) ^ 2 / 2 * (π ^ 2 / 6 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |π ^ 2 / 6 - S| ≤ (N : ℝ) ^ 2 / 2 * (1 / N) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (N : ℝ) / 2 := by field_simp
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - π ^ 2 * (N : ℝ) ^ 2 / 12|
      ≤ |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - (N : ℝ) ^ 2 / 2 * S| +
        |(N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) / 2 * (1 + Real.log N) + (N : ℝ) / 2 := add_le_add hmain h2
    _ ≤ N * (Real.log N + 1) := by nlinarith

end LeanClassics.SigmaSum
end
end

-- LeanClassics.RatioSums
section
/-
# `∑_{n ≤ N} φ(n)/n = 6N/π² + O(log N)` and `∑_{n ≤ N} σ(n)/n = π²N/6 + O(log N)`

`abs_sum_totient_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n)/n − 6N/π²| ≤ log N + 2`.

`abs_sum_sigma_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n)/n − π²N/6| ≤ log N + 2`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `φ(n)/n = ∑_{d ∣ n} μ(d)/d` (Möbius inversion of Mathlib's `Nat.sum_totient`) and
`σ(n)/n = ∑_{d ∣ n} 1/d` (Mathlib's `sigma_eq_sum_div`). For `|g(d)| ≤ 1/d`,
`∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N/d⌋` (Mathlib's `sum_Ioc_mul_eq_sum_sum`) is
`N ∑_{d ≤ N} g(d)/d` up to `∑_{d ≤ N} 1/d ≤ 1 + log N` (`floor_sum_le`). The remaining
`N |c − ∑_{d ≤ N} g(d)/d| ≤ 1` comes from `SquarefreeCount.tail_le` and `SigmaSum.tail_le`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.RatioSums

/-- `∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N/d⌋`. -/
lemma sum_sum_divisors (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d = ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
  let F : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else g d, if_pos rfl⟩
  have hF : ∀ d, d ≠ 0 → F d = g d := fun d hd => if_neg hd
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum F (ArithmeticFunction.zeta : _) N
  have hl : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d =
      (F * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := fun n _ => by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact sum_congr rfl fun d hd => (hF d (Nat.pos_of_mem_divisors hd).ne').symm
  rw [sum_congr rfl hl, h]
  refine sum_congr rfl fun d hd => ?_
  rw [hF d (mem_Ioc.mp hd).1.ne']
  congr 1
  rw [sum_congr rfl fun m hm => by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
      (mem_Ioc.mp hm).1.ne']]
  simp

/-- `φ(n)/n = ∑_{d ∣ n} μ(d)/d`. -/
lemma totient_div_eq {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) / n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun n => (n.totient : ℤ)) (g := fun n => (n : ℤ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n) n hn
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))] at h
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h'
  rw [← h', sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_div hdn hd0.ne']
  field_simp

/-- `σ(n)/n = ∑_{d ∣ n} 1/d`. -/
lemma sigma_div_eq {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  rw [ArithmeticFunction.sigma_eq_sum_div]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pow_one, Nat.cast_div hdn hd0.ne']
  field_simp

/-- For `|g(d)| ≤ 1/d`: `|∑_{d ≤ N} g(d) ⌊N/d⌋ − N ∑_{d ≤ N} g(d)/d| ≤ 1 + log N`. -/
lemma floor_sum_le (g : ℕ → ℝ) (hg : ∀ d, |g d| ≤ 1 / (d : ℝ)) (N : ℕ) :
    |∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) - N * ∑ d ∈ Ioc 0 N, g d / d| ≤
      1 + Real.log N := by
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ d ∈ Ioc 0 N, |g d * ((N / d : ℕ) : ℝ) - N * (g d / d)| ≤ 1 / (d : ℝ) :=
    fun d hd => by
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have e : g d * ((N / d : ℕ) : ℝ) - N * (g d / d) = g d * (((N / d : ℕ) : ℝ) - N / d) := by
      field_simp
    have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have h2 : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := N) hd0
      have h3 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      rw [div_sub_one hdr.ne', div_lt_iff₀ hdr]
      linarith
    rw [e, abs_mul]
    have h4 : |((N / d : ℕ) : ℝ) - N / d| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |g d| * |((N / d : ℕ) : ℝ) - N / d| ≤ 1 / (d : ℝ) * 1 :=
          mul_le_mul (hg d) h4 (abs_nonneg _) (by positivity)
      _ = 1 / (d : ℝ) := mul_one _
  refine (sum_le_sum hb).trans ?_
  have hH : ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, show Icc 1 N = Ioc 0 N by ext; simp; omega]
    push_cast
    simp [one_div]
  rw [hH]
  exact harmonic_le_one_add_log N

theorem abs_sum_totient_div_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - 6 * (N : ℝ) / π ^ 2| ≤ Real.log N + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / d
  have hg : ∀ d, |g d| ≤ 1 / (d : ℝ) := fun d => by
    simp only [g, abs_div, Nat.abs_cast]
    have : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact div_le_div_of_nonneg_right this (by positivity)
  have hs : ∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n = ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_sum_divisors]
    exact sum_congr rfl fun n hn => totient_div_eq (mem_Ioc.mp hn).1
  have hS : ∑ d ∈ Ioc 0 N, g d / d =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 := by
    refine sum_congr rfl fun d _ => ?_
    simp only [g]
    ring
  have h1 := floor_sum_le g hg N
  rw [← hs, hS] at h1
  have hT := LeanClassics.SquarefreeCount.tail_le hN
  set S := ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2
  have h2 : |N * S - 6 * (N : ℝ) / π ^ 2| ≤ 1 := by
    have e : N * S - 6 * (N : ℝ) / π ^ 2 = -(N * (6 / π ^ 2 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_pos hNr]
    calc (N : ℝ) * |6 / π ^ 2 - S| ≤ N * (1 / N) := mul_le_mul_of_nonneg_left hT hNr.le
      _ = 1 := by field_simp
  calc |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - 6 * (N : ℝ) / π ^ 2|
      ≤ |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - N * S| + |N * S - 6 * (N : ℝ) / π ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ (1 + Real.log N) + 1 := add_le_add h1 h2
    _ = Real.log N + 2 := by ring

theorem abs_sum_sigma_div_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - π ^ 2 * (N : ℝ) / 6| ≤
      Real.log N + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ := fun d => 1 / (d : ℝ)
  have hg : ∀ d, |g d| ≤ 1 / (d : ℝ) := fun d => by
    simp only [g]
    rw [abs_of_nonneg (by positivity)]
  have hs : ∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n =
      ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_sum_divisors]
    exact sum_congr rfl fun n hn => sigma_div_eq (mem_Ioc.mp hn).1
  have hS : ∑ d ∈ Ioc 0 N, g d / d = ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2 := by
    refine sum_congr rfl fun d _ => ?_
    simp only [g]
    ring
  have h1 := floor_sum_le g hg N
  rw [← hs, hS] at h1
  have hT := LeanClassics.SigmaSum.tail_le hN
  set S := ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2
  have h2 : |N * S - π ^ 2 * (N : ℝ) / 6| ≤ 1 := by
    have e : N * S - π ^ 2 * (N : ℝ) / 6 = -(N * (π ^ 2 / 6 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_pos hNr]
    calc (N : ℝ) * |π ^ 2 / 6 - S| ≤ N * (1 / N) := mul_le_mul_of_nonneg_left hT hNr.le
      _ = 1 := by field_simp
  calc |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - π ^ 2 * (N : ℝ) / 6|
      ≤ |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - N * S| +
        |N * S - π ^ 2 * (N : ℝ) / 6| := abs_sub_le _ _ _
    _ ≤ (1 + Real.log N) + 1 := add_le_add h1 h2
    _ = Real.log N + 2 := by ring

end LeanClassics.RatioSums
end
end

-- LeanClassics.ChebyshevIdentity
section
/-
# Chebyshev's identity `∑_{d ≤ N} Λ(d) ⌊N/d⌋ = log N!`

`sum_vonMangoldt_floor`: for every natural `N`, `∑_{1 ≤ d ≤ N} Λ(d) ⌊N/d⌋ = log N!`.

`abs_sum_vonMangoldt_floor_sub_le`: for `N ≥ 1`, `|∑_{d ≤ N} Λ(d) ⌊N/d⌋ − N log N| ≤ N`.

`sub_one_le_sum_vonMangoldt_div`: for `N ≥ 1`, `log N − 1 ≤ ∑_{d ≤ N} Λ(d)/d` (a one-sided bound
only).

Proof. `∑_{d ∣ n} Λ(d) = log n` (Mathlib's `vonMangoldt_sum`) and `RatioSums.sum_sum_divisors`
give the identity. `N! ≤ N^N` (Mathlib's `Nat.factorial_le_pow`) and `N^N/N! ≤ e^N`
(Mathlib's `Real.pow_div_factorial_le_exp`) give `N log N − N ≤ log N! ≤ N log N`. Since
`Λ ≥ 0` and `⌊N/d⌋ ≤ N/d`, `N ∑_{d ≤ N} Λ(d)/d ≥ log N!`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.ChebyshevIdentity

/-- `log N! = ∑_{n ≤ N} log n`. -/
lemma log_factorial_eq (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Real.log n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
      (by exact_mod_cast (Nat.factorial_pos N).ne'), ih, sum_Ioc_succ_top (Nat.zero_le N),
      add_comm]

/-- Chebyshev's identity: `∑_{d ≤ N} Λ(d) ⌊N/d⌋ = log N!`. -/
theorem sum_vonMangoldt_floor (N : ℕ) :
    ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) =
      Real.log (N.factorial : ℝ) := by
  rw [← LeanClassics.RatioSums.sum_sum_divisors (fun d => ArithmeticFunction.vonMangoldt d),
    log_factorial_eq]
  exact sum_congr rfl fun n _ => ArithmeticFunction.vonMangoldt_sum

/-- `N log N − N ≤ log N! ≤ N log N` for `N ≥ 1`. -/
lemma log_factorial_bounds {N : ℕ} (hN : 1 ≤ N) :
    N * Real.log N - N ≤ Real.log (N.factorial : ℝ) ∧
      Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  constructor
  · have h := Real.pow_div_factorial_le_exp (N : ℝ) hNr.le N
    rw [div_le_iff₀ hf] at h
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
    linarith
  · have h : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
    have h2 := Real.log_le_log hf h
    rwa [Real.log_pow] at h2

theorem abs_sum_vonMangoldt_floor_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) - N * Real.log N|
      ≤ N := by
  rw [sum_vonMangoldt_floor]
  obtain ⟨h1, h2⟩ := log_factorial_bounds hN
  rw [abs_le]
  constructor <;> linarith

theorem sub_one_le_sum_vonMangoldt_div {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d / d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (log_factorial_bounds hN).1
  rw [← sum_vonMangoldt_floor] at h1
  have h2 : ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) ≤
      N * ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d / d := by
    rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hdr : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    calc ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) ≤
          ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) := mul_le_mul_of_nonneg_left hle hΛ
      _ = N * (ArithmeticFunction.vonMangoldt d / d) := by ring
  have h3 : (N : ℝ) * (Real.log N - 1) ≤
      N * ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d / d := by
    linarith
  exact le_of_mul_le_mul_left h3 hNr

end LeanClassics.ChebyshevIdentity
end
end

-- LeanClassics.RobinMertensExplicit
section
/-
# Explicit Mertens-type bounds for the primorial bound (rung R2, session 2)

All unconditional, with explicit constants. `θ` and `ψ` are Mathlib's `Chebyshev.theta`, `Chebyshev.psi`;
`primesLE n` is the set of primes `≤ n`.

* `log_factorial_le`: `log n! ≤ n log n − n + (log n)/2 + 1` for `n ≥ 1` (Mathlib's Stirling sequence is
  antitone, with value `e/√2` at `1`).
* `sum_log_div_prime_le`: `∑_{p ≤ n} log p / p ≤ log n + 2/5` for `n ≥ 1000` (Legendre:
  `∑_p log p ⌊n/p⌋ ≤ ∑_d Λ(d) ⌊n/d⌋ = log n!`, `ChebyshevIdentity.sum_vonMangoldt_floor`; and
  `θ(n) ≤ n log 4`).
* `psi_ge`: `ψ(n) ≥ n log 2 − log(n + 1)` (Mathlib `Chebyshev.psi_ge`).
* `theta_ge_third`: `θ(n) ≥ n/3` for `n ≥ 2000` (with `|ψ − θ| ≤ 2 √x log x`,
  Mathlib `abs_psi_sub_theta_le_sqrt_mul_log`).
-/

open Real Finset

noncomputable section

namespace LeanClassics.RobinMertensExplicit

/- ### Stirling upper bound -/

theorem log_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ n * log n - n + log n / 2 + 1 := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, Nat.sub_add_cancel hn, zero_add] at hanti
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hanti
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < √(2 * n : ℝ) * (n / exp 1) ^ n := by positivity
  rw [div_le_iff₀ hD] at hanti
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := log_le_log hf hanti
  have hs2 : (0 : ℝ) < √2 := by positivity
  rw [log_mul (by positivity) hD.ne', log_mul (by positivity) (by positivity), log_div (by positivity)
    hs2.ne', log_exp, log_pow, log_div hn0.ne' (exp_pos 1).ne', log_exp, log_sqrt (by positivity),
    log_sqrt (by norm_num), log_mul (by norm_num) hn0.ne'] at h
  linarith

/- ### Mertens' first theorem, upper half -/

lemma real_div_le_floor_add_one (n p : ℕ) (hp : 0 < p) :
    (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hp']
  have h1 : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have h2 : n % p < p := Nat.mod_lt n hp
  have : (n : ℝ) = p * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : ((n % p : ℕ) : ℝ) ≤ p := by exact_mod_cast h2.le
  nlinarith

lemma sum_log_mul_floor_le_log_factorial (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p * ((n / p : ℕ) : ℝ) ≤ log (n.factorial : ℝ) := by
  rw [← ChebyshevIdentity.sum_vonMangoldt_floor]
  have hsub : Nat.primesLE n ⊆ Ioc 0 n := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    exact mem_Ioc.mpr ⟨hp.2.pos, hp.1⟩
  calc ∑ p ∈ Nat.primesLE n, log p * ((n / p : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesLE n, ArithmeticFunction.vonMangoldt p * ((n / p : ℕ) : ℝ) := by
        refine sum_congr rfl fun p hp => ?_
        rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2]
    _ ≤ ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

lemma log_le_div_hundred {x : ℝ} (hx : 1000 ≤ x) : log x ≤ x / 100 := by
  have h1000 : log (1000 : ℝ) ≤ 6.9081 := by
    have : log (1000 : ℝ) = 3 * (log 2 + log 5) := by
      rw [show (1000 : ℝ) = (2 * 5) ^ 3 by norm_num, log_pow, log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [this]; linarith [log_two_lt_d9, log_five_lt_d9]
  have h := log_le_sub_one_of_pos (show 0 < x / 1000 by linarith)
  rw [log_div (by linarith) (by norm_num)] at h
  linarith

/-- **Mertens' first theorem, explicit upper half**: `∑_{p ≤ n} log p/p ≤ log n + 2/5` for `n ≥ 1000`. -/
theorem sum_log_div_prime_le {n : ℕ} (hn : 1000 ≤ n) :
    ∑ p ∈ Nat.primesLE n, log p / p ≤ log n + 2 / 5 := by
  have hnr : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- `n · ∑ log p / p ≤ ∑ log p ⌊n/p⌋ + θ(n)`
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p ≤
      ∑ p ∈ Nat.primesLE n, log p * ((n / p : ℕ) : ℝ) + ∑ p ∈ Nat.primesLE n, log p := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have hpP := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hpP.one_lt.le)
    have := real_div_le_floor_add_one n p hpP.pos
    calc (n : ℝ) * (log p / p) = log p * ((n : ℝ) / p) := by ring
      _ ≤ log p * (((n / p : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left this hlog
      _ = _ := by ring
  have htheta : ∑ p ∈ Nat.primesLE n, log (p : ℝ) ≤ log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hfact := log_factorial_le (n := n) (by omega)
  have hleg := sum_log_mul_floor_le_log_factorial n
  have hlog4 : log (4 : ℝ) < 1.3863 := by
    have : log (4 : ℝ) = 2 * log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    rw [this]; linarith [log_two_lt_d9]
  have hsmall := log_le_div_hundred hnr
  -- combine: n A ≤ n log n − n + log n / 2 + 1 + n log 4 ≤ n (log n + 2/5)
  have hA : (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p ≤ n * (log n + 2 / 5) := by
    nlinarith
  exact le_of_mul_le_mul_left hA hn0

/- ### Chebyshev's lower bound for `θ` -/

theorem psi_ge (n : ℕ) : n * log 2 - log (n + 1) ≤ Chebyshev.psi n := Chebyshev.psi_ge n

/-- **`θ(n) ≥ n/3` for `n ≥ 2000`.** -/
theorem theta_ge_third {n : ℕ} (hn : 2000 ≤ n) : (n : ℝ) / 3 ≤ Chebyshev.theta n := by
  have hnr : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := psi_ge n
  have hd := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (n : ℝ)) (by linarith)
  have hd' : Chebyshev.psi n - Chebyshev.theta n ≤ 2 * √(n : ℝ) * log n := (le_abs_self _).trans hd
  set s := √(n : ℝ) with hs
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hss : s * s = n := mul_self_sqrt (by positivity)
  have hs44 : (44.7 : ℝ) ≤ s := by
    rw [hs, le_sqrt (by norm_num) (by positivity)]; linarith
  have hlogn : log (n : ℝ) = 2 * log s := by
    rw [← hss, log_mul (by positivity) (by positivity)]; ring
  have hlog45 : log (45 : ℝ) ≤ 3.807 := by
    have : log (45 : ℝ) = 2 * log 3 + log 5 := by
      rw [show (45 : ℝ) = 3 ^ 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]; norm_num
    rw [this]; linarith [log_three_lt_d9, log_five_lt_d9]
  have hlogs : log s ≤ 2.807 + s / 45 := by
    have h := log_le_sub_one_of_pos (show 0 < s / 45 by linarith)
    rw [log_div (by linarith) (by norm_num)] at h
    linarith
  have hlogn1 : log ((n : ℝ) + 1) ≤ 0.7 + 2 * log s := by
    have : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have h := log_le_log (by positivity) this
    rw [log_mul (by norm_num) (by positivity), hlogn] at h
    linarith [log_two_lt_d9]
  have hlog2 := log_two_gt_d9
  have hlogs0 : 0 ≤ log s := log_nonneg (by linarith)
  -- `θ ≥ n log 2 − log(n+1) − 4 s log s ≥ n/3`
  have hprod : s * log s ≤ 2.807 * s + s * s / 45 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogs hs0]
  have hls : log s ≤ s := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hnn : (n : ℝ) = s * s := hss.symm
  have key : (n : ℝ) / 3 ≤ n * log 2 - log ((n : ℝ) + 1) - 2 * s * log n := by
    rw [hlogn, hnn]
    rw [hnn] at hlogn1
    nlinarith
  linarith

end LeanClassics.RobinMertensExplicit
end
end

-- Erdos50FC.Singular
section
/-
# Erdős #50, rung R4b: `f' = 0` a.e. on `[0,1]` (Erdős 1939), hence FC's `erdos_50_singular`

The analysis half is
`Erdos50FC/SingularAnalysis.lean`; this file supplies the number theory and assembles.

For `N = y⁸`, R4a's decomposition `f(c) = ∑_{T ⊆ P_N} G_N(c/h_T)/w_T` is fed to `cover_ineq` with
`good = {T ⊆ P_y : ∑_{p∈T} log p ≤ 4 log y}`, `η_T = e^{-L_T}/y²`:
* good mass `∑_good 1/w_T ≥ (1/64)/ρ_N` (Markov on `L_T` with Mertens' first theorem, and
  `ρ_N/ρ_y ≥ 1/32` from Mertens' third);
* tail `G_N(1-η) ≤ 2/(Nη)` (Markov on `∑_{p ∣ n} 1/p`, all `p > N`);
* error and cover length `≪ log y / y`.
-/

open Filter Finset Real Topology MeasureTheory
open scoped Nat

namespace Erdos50
namespace Sing

open AtE Cont

/- ### 1. Sums over subsets of a set of primes -/

/-- `L_T = ∑_{p ∈ T} log p`. -/
noncomputable def L (T : Finset ℕ) : ℝ := ∑ p ∈ T, Real.log p

/-- `Q_P = ∏_{p ∈ P} (1 - 1/p)`. -/
noncomputable def Q (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

lemma Q_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 0 < Q P :=
  Finset.prod_pos fun p hp => one_sub_inv_pos (hP p hp)

lemma w_pos {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : 0 < w T :=
  lt_of_lt_of_le one_pos (w_ge_one hT)

lemma w_insert {q : ℕ} {T : Finset ℕ} (hq : q ∉ T) : w (insert q T) = ((q : ℝ) - 1) * w T := by
  rw [w, Finset.prod_insert hq, ← w]

lemma L_insert {q : ℕ} {T : Finset ℕ} (hq : q ∉ T) : L (insert q T) = Real.log q + L T := by
  rw [L, Finset.sum_insert hq, ← L]

lemma inv_Q_insert {q : ℕ} {P : Finset ℕ} (hq : q ∉ P) (hqp : q.Prime) :
    1 / Q (insert q P) = (1 + 1 / ((q : ℝ) - 1)) * (1 / Q P) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqp.one_lt
  rw [Q, Finset.prod_insert hq, ← Q]
  have : (1 : ℝ) - 1 / q ≠ 0 := (one_sub_inv_pos hqp).ne'
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hqsub : (q : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hq1.ne'
  by_cases hQ : Q P = 0
  · simp [hQ]
  field_simp [hq0, hqsub, hQ, this]
  ring

/-- `∑_{T ⊆ P} 1/w_T = 1/Q_P`. -/
lemma sum_inv_w (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ T ∈ P.powerset, 1 / w T = 1 / Q P := by
  induction P using Finset.induction_on with
  | empty => simp [w, Q]
  | insert q P hq ih =>
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have hqp := hP q (mem_insert_self q P)
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hqp.one_lt
    rw [Finset.sum_powerset_insert hq, inv_Q_insert hq hqp, ← ih hP', add_mul, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    have hqT : q ∉ T := fun h => hq (Finset.mem_powerset.mp hT h)
    rw [w_insert hqT]
    have := w_pos (fun p hp => hP' p (Finset.mem_powerset.mp hT hp))
    have : (q : ℝ) - 1 ≠ 0 := by linarith
    field_simp

/-- `∑_{T ⊆ P} L_T/w_T = (1/Q_P) ∑_{p ∈ P} log p / p`. -/
lemma sum_L_div_w (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ T ∈ P.powerset, L T / w T = (1 / Q P) * ∑ p ∈ P, Real.log p / p := by
  induction P using Finset.induction_on with
  | empty => simp [L]
  | insert q P hq ih =>
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have hqp := hP q (mem_insert_self q P)
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hqp.one_lt
    have hq0 : (q : ℝ) - 1 ≠ 0 := by linarith
    rw [Finset.sum_powerset_insert hq, inv_Q_insert hq hqp, Finset.sum_insert hq]
    have h2 : ∑ T ∈ P.powerset, L (insert q T) / w (insert q T) =
        (1 / ((q : ℝ) - 1)) * (∑ T ∈ P.powerset, L T / w T) +
          (Real.log q / ((q : ℝ) - 1)) * ∑ T ∈ P.powerset, 1 / w T := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hqT : q ∉ T := fun h => hq (Finset.mem_powerset.mp hT h)
      have := w_pos (fun p hp => hP' p (Finset.mem_powerset.mp hT hp))
      rw [w_insert hqT, L_insert hqT]
      field_simp
      ring
    rw [h2, ih hP', sum_inv_w P hP']
    have hq0' : (q : ℝ) ≠ 0 := by linarith
    field_simp
    ring

/-- Markov on `L_T`: the subsets with `L_T > t` carry `1/w`-mass at most `(1/Q_P)(∑ log p/p)/t`. -/
lemma sum_bad_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {t : ℝ} (ht : 0 < t) :
    ∑ T ∈ P.powerset.filter (fun T => t < L T), 1 / w T ≤
      (1 / Q P) * (∑ p ∈ P, Real.log p / p) / t := by
  rw [le_div_iff₀ ht, ← sum_L_div_w P hP, Finset.sum_mul]
  calc ∑ T ∈ P.powerset.filter (fun T => t < L T), 1 / w T * t
      ≤ ∑ T ∈ P.powerset.filter (fun T => t < L T), L T / w T := by
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hT1, hT2⟩ := Finset.mem_filter.mp hT
        have := w_pos (fun p hp => hP p (Finset.mem_powerset.mp hT1 hp))
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_div_of_nonneg_right hT2.le this.le
    _ ≤ ∑ T ∈ P.powerset, L T / w T := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun T hT _ => ?_
        have := w_pos (fun p hp => hP p (Finset.mem_powerset.mp hT hp))
        refine div_nonneg (Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p) this.le

/- ### 2. The tail law: `G_N(1-η) ≤ 2/(Nη)` -/

lemma totient_ge_of_Tn_empty {N n : ℕ} (hn : Tn N n = ∅) : (n : ℝ) * (1 - sY N n) ≤ φ n := by
  rw [totient_eq_mul_prod]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  have hfil : n.primeFactors.filter (fun p => ¬ p ≤ N) = n.primeFactors := by
    refine Finset.filter_true_of_mem fun p hp hpN => ?_
    have : p ∈ Tn N n := mem_Tn.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hpN⟩, Nat.prime_of_mem_primeFactors hp⟩,
      Nat.dvd_of_mem_primeFactors hp⟩
    rw [hn] at this; exact Finset.notMem_empty _ this
  rw [sY, hfil]
  apply one_sub_sum_le_prod
  · intro p _; positivity
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [div_le_one (by positivity)]; exact_mod_cast this.le

section Tail

variable {N : ℕ} (hN : 2 ≤ N) (hS : ∀ c : ℝ, ∃ v, (S c).HasDensity v)
include hN hS

lemma G_tail {η : ℝ} (hη : 0 < η) : G N (1 - η) ≤ 2 / (N * η) := by
  classical
  have hv := hd_G hN hS (1 - η)
  rw [hasDensity_iff] at hv
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply le_of_tendsto hv
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb', cnt_eq_card]
  set B := (Finset.Ioc 0 b).filter (fun n => η ≤ sY N n)
  have hsub : (Finset.range b).filter (· ∈ Z N ∅ (1 - η)) ⊆ B := by
    intro n hn
    obtain ⟨hnb, hnZ⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := fun h => not_mem_Z_zero N ∅ (1 - η) (h ▸ hnZ)
    obtain ⟨hT, hlt⟩ := hnZ
    have hn0' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,
      (Finset.mem_range.mp hnb).le⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have := totient_ge_of_Tn_empty hT
    have : (n : ℝ) * (1 - η) < n * (1 - sY N n) := mul_lt_mul_of_pos_left (by linarith) hn0'
    linarith
  have hcard : η * B.card ≤ 2 * b / N := by
    calc η * B.card = ∑ n ∈ B, η := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ B, sY N n := Finset.sum_le_sum fun n hn => (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ Finset.Ioc 0 b, sY N n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun n _ _ => Finset.sum_nonneg fun p _ => by positivity
      _ ≤ 2 * b / N := sum_sY_le N b (by omega)
  have h1 : (((Finset.range b).filter (· ∈ Z N ∅ (1 - η))).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 : (B.card : ℝ) ≤ 2 / (N * η) * b := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [div_mul_cancel₀ (2 * (b : ℝ)) hN0.ne']
  exact h1.trans h2

lemma G_nonneg (c : ℝ) : 0 ≤ G N c := hd_nonneg (hd_G hN hS c)

lemma G_const {x y : ℝ} (hx : 1 < x) (hy : 1 < y) : G N x = G N y := by
  have h1 := hd_G hN hS x
  have h2 := hd_G hN hS y
  rw [Z_empty_eq_C0 hN hx] at h1
  rw [Z_empty_eq_C0 hN hy] at h2
  exact (hd_unique h1 (hd_C0 N)).trans (hd_unique h2 (hd_C0 N)).symm

lemma G_monotone : Monotone (G N) := fun _ _ h => G_mono hN hS h

end Tail

/- ### 3. Mertens -/

lemma primesLE_eq (n : ℕ) : Nat.primesLE n = primesTo n := by
  ext p
  simp only [Nat.primesLE, Nat.primesBelow, primesTo, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, by omega⟩, h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨by omega, h2⟩

/-- Two-sided Mertens: eventually `(L/2) log x ≤ 1/ρ(⌊x⌋) ≤ 2 L log x`, `L = e^γ`. -/
lemma eventually_inv_rho :
    ∀ᶠ x : ℝ in atTop,
      Real.exp Real.eulerMascheroniConstant / 2 * Real.log x ≤ 1 / rho ⌊x⌋₊ ∧
      1 / rho ⌊x⌋₊ ≤ 2 * Real.exp Real.eulerMascheroniConstant * Real.log x := by
  have hM := LeanClassics.MertensThird.tendsto_prod_div_log
  set E := Real.exp Real.eulerMascheroniConstant
  have hE : 0 < E := Real.exp_pos _
  have h1 := hM.eventually (lt_mem_nhds (show E / 2 < E by linarith))
  have h2 := hM.eventually (gt_mem_nhds (show E < 2 * E by linarith))
  filter_upwards [h1, h2, eventually_gt_atTop (Real.exp 1)] with x hx1 hx2 hxe
  have hlog : 0 < Real.log x := Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hrho : 1 / rho ⌊x⌋₊ = ∏ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [rho, primesTo, Finset.prod_inv_distrib, one_div]
  rw [hrho]
  rw [lt_div_iff₀ hlog] at hx1
  rw [div_lt_iff₀ hlog] at hx2
  constructor <;> linarith

/- ### 4. Good mass, and `e^{±L_T}` -/

lemma one_le_log_of_ge {y : ℕ} (hy : 1000 ≤ y) : 1 ≤ Real.log y := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : (1000 : ℝ) ≤ y := by exact_mod_cast hy
  linarith [Real.exp_one_lt_d9]

/-- For `y ≥ 1000`: `∑_{T ⊆ P_y, L_T ≤ 4 log y} 1/w_T ≥ (1/2)/ρ_y`. -/
lemma good_mass {y : ℕ} (hy : 1000 ≤ y) :
    (1 / 2) * (1 / rho y) ≤
      ∑ T ∈ (primesTo y).powerset.filter (fun T => L T ≤ 4 * Real.log y), 1 / w T := by
  have hP : ∀ p ∈ primesTo y, p.Prime := fun p hp => prime_of_mem_primesTo hp
  have hQ : Q (primesTo y) = rho y := rfl
  have hly := one_le_log_of_ge hy
  have ht : 0 < 4 * Real.log y := by linarith
  have hbad := sum_bad_le (primesTo y) hP ht
  have hm := LeanClassics.RobinMertensExplicit.sum_log_div_prime_le hy
  rw [primesLE_eq] at hm
  have htot := sum_inv_w (primesTo y) hP
  rw [← Finset.sum_filter_add_sum_filter_not (primesTo y).powerset
    (fun T => L T ≤ 4 * Real.log y)] at htot
  simp only [not_le] at htot
  rw [hQ] at hbad htot
  have hr : 0 < 1 / rho y := by have := rho_pos y; positivity
  have hS0 : 0 ≤ ∑ p ∈ primesTo y, Real.log p / p :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hb2 : (1 / rho y) * (∑ p ∈ primesTo y, Real.log p / p) / (4 * Real.log y) ≤
      (1 / 2) * (1 / rho y) := by
    rw [div_le_iff₀ ht]
    nlinarith
  linarith

lemma exp_L {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : Real.exp (L T) = ∏ p ∈ T, (p : ℝ) := by
  rw [L, Real.exp_sum]
  exact Finset.prod_congr rfl fun p hp => Real.exp_log (by exact_mod_cast (hT p hp).pos)

lemma exp_neg_L_le {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : Real.exp (-L T) ≤ 1 / w T := by
  rw [Real.exp_neg, exp_L hT, w, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    have := (hT p hp).pos; positivity
  · intro p hp
    have h1 : (1 : ℝ) < p := by exact_mod_cast (hT p hp).one_lt
    exact inv_anti₀ (by linarith) (by linarith)

lemma h_le_one {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : h T ≤ 1 := by
  have := prod_anti (Finset.empty_subset T) hT
  simpa [h] using this

/- ### 5. Assembly -/

lemma monotoneOn_f (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) : MonotoneOn f (Set.Icc 0 1) :=
  fun c hc c' hc' hcc => hd_le (hf c hc) (hf c' hc') fun n (hn : (φ n : ℝ) < c * n) =>
    show (φ n : ℝ) < c' * n from lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg n))

lemma f_eq_F (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) {N : ℕ} (hN : 2 ≤ N) :
    Set.EqOn f (fun x => ∑ T ∈ (primesTo N).powerset, 1 / w T * G N (x / h T)) (Set.Icc 0 1) := by
  intro c hc
  have h1 : (S c).HasDensity (f c) := hf c hc
  rw [hd_unique h1 (hd_S_sum hN (hS_of_hf hf) c)]
  exact Finset.sum_congr rfl fun T _ => by rw [div_eq_inv_mul, one_div]

/-- **R4b.** `f' = 0` almost everywhere on `[0,1]` (Erdős 1939). -/
theorem ae_derivWithin_eq_zero (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), derivWithin f (Set.Icc 0 1) x = 0 := by
  have hS := hS_of_hf hf
  set E := Real.exp Real.eulerMascheroniConstant with hE_def
  have hE : 0 < E := Real.exp_pos _
  refine ae_zero_of_covers (monotoneOn_f f hf) (c := 1 / 64) (by norm_num) ?_
  intro ε hε
  have hev := eventually_inv_rho
  have h1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  have h2 := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0))).eventually hev
  obtain ⟨y, ⟨hy1a, -⟩, ⟨-, hy2b⟩, hy3, hy4⟩ :=
    (h1.and (h2.and ((eventually_ge_atTop 1000).and (eventually_ge_atTop ⌈64 * E / ε⌉₊)))).exists
  simp only [Function.comp_apply, Nat.floor_natCast] at hy1a hy2b
  set N := y ^ 8 with hN_def
  have hy0 : (1000 : ℝ) ≤ y := by exact_mod_cast hy3
  have hypos : (0 : ℝ) < y := by linarith
  have hN : 2 ≤ N := le_trans (by omega) (Nat.le_self_pow (by norm_num) y)
  have hNr : (N : ℝ) = (y : ℝ) ^ 8 := by simp [hN_def]
  have hlogN : Real.log (N : ℝ) = 8 * Real.log y := by rw [hNr, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ y := by linarith [Real.log_le_sub_one_of_pos hypos]
  have hlog1 := one_le_log_of_ge hy3
  have hyε : 64 * E / ε ≤ y := (Nat.le_ceil _).trans (by exact_mod_cast hy4)
  have hyε' : 64 * E ≤ ε * y := by rw [div_le_iff₀ hε] at hyε; linarith
  -- Mertens consequences
  set R := 1 / rho N with hR
  have hR0 : 0 < R := by have := rho_pos N; positivity
  have hRle : R ≤ 16 * E * y := by
    have := hy2b; rw [hlogN] at this; nlinarith
  have hry : (1 / 32) * R ≤ 1 / rho y := by
    have := hy2b; rw [hlogN] at this; nlinarith
  -- the data
  set I := (primesTo N).powerset with hI
  set good := (primesTo y).powerset.filter (fun T => L T ≤ 4 * Real.log y) with hgood_def
  set K : ℝ := (y : ℝ) ^ 2 with hK
  have hK1 : 1 < K := by rw [hK]; nlinarith
  set η : Finset ℕ → ℝ := fun T => Real.exp (-L T) / K with hη
  set F := fun x => ∑ T ∈ I, 1 / w T * G N (x / h T) with hF
  have hprI : ∀ T ∈ I, ∀ p ∈ T, p.Prime := fun T hT p hp =>
    prime_of_mem_primesTo (Finset.mem_powerset.mp hT hp)
  have hyN : primesTo y ⊆ primesTo N := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, h2⟩
    exact (Finset.mem_Icc.mp h1).2.trans (Nat.le_self_pow (by norm_num) y)
  have hgood : good ⊆ I := fun T hT =>
    Finset.mem_powerset.mpr ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1).trans hyN)
  have hhpos : ∀ T ∈ I, 0 < h T := fun T hT => h_pos (hprI T hT)
  have hh1 : ∀ T ∈ I, h T ≤ 1 := fun T hT => h_le_one (hprI T hT)
  have ha : ∀ T ∈ I, 0 ≤ 1 / w T := fun T hT => (one_div_pos.mpr (w_pos (hprI T hT))).le
  have hη0 : ∀ T ∈ good, 0 ≤ η T := fun T _ => by positivity
  have hη1 : ∀ T ∈ good, η T < 1 := fun T _ => by
    rw [hη, div_lt_one (by linarith)]
    calc Real.exp (-L T) ≤ 1 := Real.exp_le_one_iff.mpr (by
            simp only [neg_nonpos, L]
            exact Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p)
      _ < K := hK1
  have hGm := G_monotone hN hS
  have hGc : ∀ x y : ℝ, 1 < x → 1 < y → G N x = G N y := fun x y hx hy => G_const hN hS hx hy
  -- f = F on Ioo 0 1, so their derivatives agree there
  have hEq : Set.EqOn (deriv f) (deriv F) (Set.Ioo 0 1) :=
    ((f_eq_F f hf hN).mono Set.Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hUsub := U_subset h good η (fun T hT => hhpos T (hgood hT)) (fun T hT => hh1 T (hgood hT)) hη1
  have hUm := measurableSet_U good h η
  refine ⟨U good h η, hUsub, hUm, ?_, ?_⟩
  · -- length of the cover
    refine (volume_U h good η).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun T hT =>
      mul_nonneg (hhpos T (hgood hT)).le (hη0 T hT)]
    apply ENNReal.ofReal_le_ofReal
    calc ∑ T ∈ good, h T * η T ≤ ∑ T ∈ good, 1 / w T / K := by
          refine Finset.sum_le_sum fun T hT => ?_
          have hTI := hgood hT
          calc h T * η T ≤ η T := mul_le_of_le_one_left (hη0 T hT) (hh1 T hTI)
            _ ≤ 1 / w T / K := div_le_div_of_nonneg_right (exp_neg_L_le (hprI T hTI)) (by linarith)
      _ ≤ ∑ T ∈ I, 1 / w T / K :=
          Finset.sum_le_sum_of_subset_of_nonneg hgood fun T hT _ => div_nonneg (ha T hT) (by linarith)
      _ = R / K := by
          rw [← Finset.sum_div, hI, sum_inv_w _ fun p hp => prime_of_mem_primesTo hp]; rfl
      _ ≤ ε := by
          rw [div_le_iff₀ (by linarith), hK]
          nlinarith
  · -- the cover inequality
    have hci := cover_ineq I (fun T => 1 / w T) h hGm hhpos hh1 ha good hgood η hη0 hη1
    have hiF := integral_F I (fun T => 1 / w T) h hGm hGc hhpos hh1
    set B := ∫ x in (0 : ℝ)..1, deriv (G N) x with hB
    have hB0 : 0 ≤ B := by
      have hmem := (hGm.monotoneOn (Set.uIcc 0 1)).intervalIntegral_deriv_mem_uIcc
      have : G N 0 ≤ G N 1 := hGm zero_le_one
      rw [Set.uIcc_of_le (by linarith)] at hmem
      exact hmem.1
    have hsumI : ∑ T ∈ I, 1 / w T = R := by
      rw [hI, sum_inv_w _ fun p hp => prime_of_mem_primesTo hp]; rfl
    have hA : ∫ x in Set.Ioo (0 : ℝ) 1, deriv f x = R * B := by
      rw [setIntegral_congr_fun measurableSet_Ioo hEq, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one, hiF, hsumI]
    have hU : ∫ x in U good h η, deriv f x = ∫ x in U good h η, deriv F x :=
      setIntegral_congr_fun hUm fun x hx => hEq (hUsub hx)
    rw [hA, hU]
    refine le_trans ?_ hci
    -- per-T tail
    have htail : ∀ T ∈ good, G N (1 - η T) - G N 0 ≤ 2 / K := by
      intro T hT
      have hTI := hgood hT
      have hLT := (Finset.mem_filter.mp hT).2
      have hηpos : 0 < η T := by positivity
      have h0 := G_nonneg hN hS 0
      have ht := G_tail hN hS hηpos
      have hexp : 1 / (y : ℝ) ^ 4 ≤ Real.exp (-L T) := by
        rw [Real.exp_neg, one_div]
        apply inv_anti₀ (Real.exp_pos _)
        calc Real.exp (L T) ≤ Real.exp (4 * Real.log y) := Real.exp_le_exp.mpr hLT
          _ = (y : ℝ) ^ 4 := by
              rw [show 4 * Real.log (y : ℝ) = Real.log ((y : ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
                Real.exp_log (by positivity)]
      have hNη : K ≤ N * η T := by
        rw [hNr, hη, hK, mul_div_assoc']
        rw [le_div_iff₀ (by positivity)]
        have : (y : ℝ) ^ 8 * (1 / (y : ℝ) ^ 4) = (y : ℝ) ^ 4 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ (y : ℝ) ^ 8)]
      have : 2 / (N * η T) ≤ 2 / K := div_le_div_of_nonneg_left (by norm_num) (by linarith) hNη
      linarith
    have hgm := good_mass hy3
    have hgood_mass : (1 / 64) * R ≤ ∑ T ∈ good, 1 / w T := by linarith
    have herr : ∑ T ∈ good, 1 / w T * (G N (1 - η T) - G N 0) ≤ R * (2 / K) := by
      calc ∑ T ∈ good, 1 / w T * (G N (1 - η T) - G N 0) ≤ ∑ T ∈ good, 1 / w T * (2 / K) :=
            Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (htail T hT) (ha T (hgood hT))
        _ = (∑ T ∈ good, 1 / w T) * (2 / K) := by rw [Finset.sum_mul]
        _ ≤ (∑ T ∈ I, 1 / w T) * (2 / K) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg hgood fun T hT _ => ha T hT
        _ = R * (2 / K) := by rw [hsumI]
    have hRK : R * (2 / K) ≤ ε := by
      rw [hK, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hsplit : ∑ T ∈ good, 1 / w T * (B - (G N (1 - η T) - G N 0)) =
        B * ∑ T ∈ good, 1 / w T - ∑ T ∈ good, 1 / w T * (G N (1 - η T) - G N 0) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hgood_mass hB0]

/-- **FC's `erdos_50_singular`** (Erdős 1939), in FC's exact wording, for every `f` with
`IsDistributionOfPhiRatio f`. -/
theorem singular_distribution (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f) :
    IsPurelySingularOn f (Set.Icc 0 1) :=
  (singular_iff_ae f hf).mpr (ae_derivWithin_eq_zero f hf)

end Sing
end Erdos50
end

theorem OMA.solution : type_of% @Erdos50.erdos_50_singular :=
  Erdos50.Sing.singular_distribution

/-
Apache 2.0 distribution notices from the source package:

Erdos50 (standalone package)
Copyright 2026 Sky (GitHub: ChironTheCentaur)

The original work in this package (Erdos50FC/, LeanClassics/, Erdos50.lean, check.py, AxiomAudit.lean,
PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

The definitions `IsDistributionOfPhiRatio` and `IsPurelySingularOn`, the statement of `erdos_50_singular`, and the
definitions `Set.partialDensity` and `Set.HasDensity` (Erdos50FC/Statement.lean) are copied verbatim from
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/50.lean and
FormalConjecturesForMathlib/Data/Set/Density.lean, commit ea8e3e19), Copyright The Formal Conjectures Authors,
licensed under the Apache License, Version 2.0.

Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0
(LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1. It is not relicensed.

Mathlib and the Lean toolchain packages are fetched at build time and are not included.

Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems
Copyright 2026 Anthropic, PBC

This product is licensed under the Apache License, Version 2.0 (see LICENSE).

This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
(source file, upstream commit, original copyright line) and a description of the local modifications.
Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.

This product depends on, but does not include, Lean 4 (https://github.com/leanprover/lean4) and
mathlib4 with its standard dependency set — fetched by the build tool from their public repositories at the
revisions pinned in lake-manifest.json: batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient and
plausible are released under the Apache License, Version 2.0; Cli (leanprover/lean4-cli) is released under the
MIT License (Copyright (c) 2021 Marc Huisinga). None of these dependencies is included in this repository.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
