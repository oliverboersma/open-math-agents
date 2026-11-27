import OMAReductions.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1
import Mathlib

/- The Mertens estimates and the logarithmic first moment below are adapted from @Ciphore’s merged proof of the singularity theorem. Original notices follow. -/
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

namespace Iso50
open Filter Finset Real Topology
open scoped Classical
noncomputable def primesTo (x : ℕ) := (Finset.Icc 0 x).filter Nat.Prime
noncomputable def rho (x : ℕ) : ℝ := ∏ p ∈ primesTo x, (1-1/(p:ℝ))
noncomputable def w (T : Finset ℕ) : ℝ := ∏ p ∈ T, ((p:ℝ)-1)
lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
  linarith

noncomputable def L (T : Finset ℕ) : ℝ := ∑ p ∈ T, Real.log p

/-- `Q_P = ∏_{p ∈ P} (1 - 1/p)`. -/
noncomputable def Q (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

lemma Q_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 0 < Q P :=
  Finset.prod_pos fun p hp => one_sub_inv_pos (hP p hp)

lemma w_pos {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : 0 < w T :=
  Finset.prod_pos fun p hp => sub_pos.mpr (by exact_mod_cast (hT p hp).one_lt)
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

lemma exp_L {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : Real.exp (L T) = ∏ p ∈ T, (p : ℝ) := by
  rw [L, Real.exp_sum]
  exact Finset.prod_congr rfl fun p hp => Real.exp_log (by exact_mod_cast (hT p hp).pos)

lemma rho_pos (b : ℕ) : 0 < rho b := Q_pos fun _ hp => (mem_filter.mp hp).2

lemma factors_strip {b y : ℕ} (hby : b≤y) :
    Q ((Ioc b y).filter Nat.Prime) * rho b = rho y := by
  have h : primesTo b ⊆ primesTo y := by
    intro p hp
    obtain ⟨hm,hp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,(mem_Icc.mp hm).2.trans hby⟩,hp⟩
  have eq : (Ioc b y).filter Nat.Prime = primesTo y \ primesTo b := by
    apply Finset.ext
    intro p
    constructor
    · intro h
      obtain ⟨v,hp⟩ := mem_filter.mp h
      obtain ⟨hb,hy⟩ := mem_Ioc.mp v
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,hy⟩,hp⟩,
        fun h => hb.not_ge (mem_Icc.mp (mem_filter.mp h).1).2⟩
    · intro h
      obtain ⟨hy,hn⟩ := mem_sdiff.mp h
      obtain ⟨hy,hp⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,(mem_Icc.mp hy).2⟩,hp⟩
      exact lt_of_not_ge (fun hb => hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,hb⟩,hp⟩))
  rw [eq,Q,rho,rho,prod_sdiff h]

lemma weight_factor {U T : Finset ℕ} (hu : ∀ p ∈ U, Nat.Prime p) (ht : T ⊆ U) :
    (∏ p ∈ T, 1/(p:ℝ)) * (∏ p ∈ U \ T, (1-1/(p:ℝ))) = Q U * (1/w T) := by
  have e (p : ℕ) (hp : p∈T) : 1/(p:ℝ) = (1-1/p)/((p:ℝ)-1) := by
    have hp' : (1:ℝ)<p := by exact_mod_cast (hu p (ht hp)).one_lt
    field_simp [sub_ne_zero.mpr hp'.ne']
  calc
    _ = (∏ p ∈ T, ((1-1/(p:ℝ))/((p:ℝ)-1))) * (∏ p ∈ U \ T, (1-1/(p:ℝ))) := by
      rw [prod_congr rfl e]
    _ = ((∏ p ∈ U \ T, (1-1/(p:ℝ))) * (∏ p ∈ T, (1-1/(p:ℝ)))) / w T := by
      rw [prod_div_distrib,w]; ring
    _ = _ := by rw [prod_sdiff ht,Q]; ring

lemma mass_small_nonempty (M : Finset ℕ) (hm : ∀ p ∈ M, p.Prime) {y : ℕ}
    (hl : 0 < log y) (hsum : ∑ p ∈ M, log p / p ≤ 2*log y) (he : Q M ≤ 1/4) :
    1/(4*Q M) ≤ ∑ T ∈ (M.powerset.filter (fun T => L T ≤ 4*log y)).erase ∅, 1/w T := by
  classical
  have hq := Q_pos hm
  have hmom := sum_bad_le M hm (by linarith : 0<4*log y)
  have rest : ∑ T ∈ M.powerset.filter (fun T => 4*log y < L T), 1/w T ≤ (1/2)*(1/Q M) := by
    apply hmom.trans
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0≤1/Q M)]
  let G := M.powerset.filter fun T => L T ≤ 4*log y
  have h0 : ∅ ∈ G := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [L,hl.le]⟩
  have eq := sum_erase_add (s := G) (fun T => 1/w T) h0
  have hw0 : w ∅ = 1 := by simp [w]
  rw [hw0,div_one] at eq
  have allw := sum_inv_w M hm
  rw [← sum_filter_add_sum_filter_not M.powerset (fun T => L T ≤ 4*log y)] at allw
  simp only [not_le] at allw
  have h4 : (4:ℝ)≤1/Q M := (le_div_iff₀ hq).mpr (by linarith)
  change _ ≤ ∑ T ∈ G.erase ∅, 1/w T
  change (∑ T ∈ G, 1/w T) + _ = _ at allw
  rw [show 1/(4*Q M) = (1/4)*(1/Q M) by ring]
  linarith

lemma choose_scale (b : ℕ) (hb : 2 ≤ b) (M₀ : ℕ) :
    ∃ y : ℕ, b ≤ y ∧ M₀ ≤ y ∧ 0 < log y ∧
      (∑ p ∈ primesTo y, log p / p) ≤ 2*log y ∧
      Q ((Ioc b y).filter Nat.Prime) ≤ 1/4 ∧
      Q ((Ioc b y).filter Nat.Prime) ≤ 80*Q ((Ioc b (y^20)).filter Nat.Prime) := by
  let E := exp eulerMascheroniConstant
  have he : 0<E := exp_pos _
  have hbρ := rho_pos b
  have natmer : ∀ᶠ n : ℕ in atTop, E/2*log n ≤ 1/rho n ∧ 1/rho n ≤ 2*E*log n := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_inv_rho] with n hn
    simpa [E] using hn
  obtain ⟨Y,hY⟩ := eventually_atTop.mp natmer
  obtain ⟨C,_,hc⟩ := LeanClassics.MertensSecond.S_sub_log_bound
  have lg : Tendsto (fun n : ℕ => log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨y,hy,hlog⟩ := ((eventually_ge_atTop (max (max b M₀) Y)).and
    (lg.eventually_ge_atTop (max C ((4/rho b)/(E/2))))).exists
  have hby : b≤y := (le_max_left b M₀).trans ((le_max_left ..).trans hy)
  have hy2 : 2≤y := hb.trans hby
  have hy' : (2:ℝ) ≤ y := by exact_mod_cast hy2
  have ly : 0<log y := log_pos (by linarith)
  have hy20 : y ≤ y^20 := Nat.le_self_pow (by decide) y
  have hmin := hY y ((le_max_right ..).trans hy)
  have hmax := (hY (y^20) (((le_max_right ..).trans hy).trans hy20)).2
  rw [Nat.cast_pow,Real.log_pow] at hmax
  have hsoft := (abs_le.mp (hc (y:ℝ) hy')).2
  rw [LeanClassics.MertensSecond.S_eq,Nat.floor_natCast] at hsoft
  have hsum : (∑ p ∈ primesTo y, log p/p) ≤ 2*log y := by
    dsimp only [primesTo]
    linarith [(le_max_left ..).trans hlog]
  have hbase := (div_le_iff₀ (by positivity : 0<E/2)).mp ((le_max_right ..).trans hlog)
  have rel : 4/rho b ≤ 1/rho y := le_trans (by linarith only [hbase]) hmin.1
  have lo := (div_le_div_iff₀ hbρ (rho_pos y)).mp rel
  rw [← factors_strip hby] at lo
  have small : Q ((Ioc b y).filter Nat.Prime) ≤ 1/4 := by
    apply le_of_mul_le_mul_right (a := rho b) _ hbρ
    linarith only [lo]
  have up : 1/rho (y^20) ≤ 80/rho y := by
    calc
      _ ≤ _ := hmax
      _ = 80*(E/2*log y) := by push_cast; ring
      _ ≤ 80*(1/rho y) := mul_le_mul_of_nonneg_left hmin.1 (by norm_num)
      _ = _ := by ring
  have ratio := (div_le_div_iff₀ (rho_pos (y^20)) (rho_pos y)).mp up
  rw [←factors_strip hby,←factors_strip (hby.trans hy20)] at ratio
  refine ⟨y,hby,(le_max_right b M₀).trans ((le_max_left ..).trans hy),ly,hsum,small,?_⟩
  apply le_of_mul_le_mul_right (a:=rho b) _ hbρ
  linarith only [ratio]

end Iso50

open Iso50 Filter Finset Real
open scoped Classical

theorem OMA.solution : OMA.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1.H1 := by
  classical
  refine ⟨1/320,by norm_num,by norm_num,?_⟩
  intro b hb
  obtain ⟨y,hby,hprod,hl,hlog,hsm,hr⟩ := choose_scale b hb (∏ p ∈ (range (b+1)).filter Nat.Prime,p)
  refine ⟨y,hby,hprod,?_⟩
  let M := (Ioc b y).filter Nat.Prime
  let U := (Ioc b (y^20)).filter Nat.Prime
  have mp (p) (hp:p∈M) : Nat.Prime p := (mem_filter.mp hp).2
  have up (p) (hp:p∈U) : Nat.Prime p := (mem_filter.mp hp).2
  have hmu : M ⊆ U := by
    intro p hp
    obtain ⟨h,prime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp h).1,(mem_Ioc.mp h).2.trans
      (Nat.le_self_pow (by decide : 20 ≠ 0) y)⟩,prime⟩
  have hmy : M ⊆ primesTo y := by
    intro p hp
    obtain ⟨h,prime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,(mem_Ioc.mp h).2⟩,prime⟩
  have hmom : (∑ p ∈ M, log p/p) ≤ 2*log y :=
    (sum_le_sum_of_subset_of_nonneg hmy fun p _ _ => div_nonneg (log_natCast_nonneg _) (Nat.cast_nonneg _)).trans hlog
  let F := (M.powerset.filter (fun T => L T ≤ 4*log y)).erase ∅
  let G := U.powerset.filter fun T => T.Nonempty ∧ (∀ p ∈ T,p≤y) ∧ (∏ p ∈ T,p)≤y^4
  have sub : F ⊆ G := by
    intro T hT
    obtain ⟨hne,hT'⟩ := mem_erase.mp hT
    obtain ⟨hsub,hs⟩ := mem_filter.mp hT'
    have ht := mem_powerset.mp hsub
    have htp : ∀ p ∈ T, Nat.Prime p := fun p h => mp p (ht h)
    have bound := exp_le_exp.mpr hs
    have hy0 : (0:ℝ)<y := by exact_mod_cast (by omega : 0<y)
    rw [exp_L htp,show 4*log (y:ℝ) = (4:ℕ)*log (y:ℝ) by norm_num,exp_nat_mul,exp_log hy0] at bound
    rw [← Nat.cast_prod,←Nat.cast_pow] at bound
    exact mem_filter.mpr ⟨mem_powerset.mpr (ht.trans hmu),nonempty_iff_ne_empty.mpr hne,
      fun p hp => (mem_Ioc.mp (mem_filter.mp (ht hp)).1).2,by exact_mod_cast bound⟩
  have mass : 1/(4*Q M) ≤ ∑ T ∈ F, 1/w T := mass_small_nonempty M mp hl hmom hsm
  have qM := Q_pos mp
  have qU := Q_pos up
  have cmp : (1/320:ℝ) ≤ Q U*(1/(4*Q M)) := by
    rw [←mul_div_assoc,mul_one,le_div_iff₀ (by positivity)]
    change Q M ≤ 80*Q U at hr
    linarith only [hr]
  have bigger : (∑ T ∈ F, 1/w T) ≤ ∑ T ∈ G, 1/w T :=
    sum_le_sum_of_subset_of_nonneg sub fun T ht _ =>
      one_div_nonneg.mpr (w_pos (fun p hp => up p (mem_powerset.mp (mem_filter.mp ht).1 hp))).le
  calc
    (1/320:ℝ) ≤ Q U * (∑ T ∈ G, 1/w T) := cmp.trans (mul_le_mul_of_nonneg_left (mass.trans bigger) qU.le)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr _ fun T ht => (weight_factor up (mem_powerset.mp (mem_filter.mp ht).1)).symm
      ext T
      simp only [G,U,mem_filter]

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
