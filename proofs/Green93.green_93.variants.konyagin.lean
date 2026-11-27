-- Adapted from github.com/ckkogler/odlyzko-poonen-lean (commit e79540e23d591907eed55268f1ada10340d1de69), (c) 2026 Constantin Kogler, BSD Zero Clause License (0BSD).
-- Reuses the project's Breuillard–Varjú proof of the unconditional Odlyzko–Poonen limit (arXiv:2609.26771) to deduce Konyagin's bound.
-- Modules concatenated, comments stripped, and Finset.mem_antidiagonal qualified; bridge to Green93.irreducibleProb at the end.
import FormalConjectures.GreensOpenProblems.«93»
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.Associated
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Polynomial

namespace OdlyzkoPoonen
lemma nat_div_ge_half_real_ratio {m q : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    (m : ℝ) / (2 * (q : ℝ)) ≤ ((m / q : ℕ) : ℝ) := by
  have hk : 1 ≤ m / q := Nat.div_pos hqm hq
  have hkR : (1 : ℝ) ≤ (m / q : ℕ) := by exact_mod_cast hk
  have hr : ((m % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt m hq
  have he : ((m % q : ℕ) : ℝ) + (q : ℝ) * ((m / q : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Nat.mod_add_div m q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqk : (q : ℝ) ≤ (q : ℝ) * ((m / q : ℕ) : ℝ) :=
    le_mul_of_one_le_right hqR.le hkR
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  nlinarith
lemma sparse_quotient_lower {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (hqm : q ≤ n - 1) {K : ℝ} (hK : 0 < K) (hlog : 1 ≤ Real.log (n : ℝ))
    (hqupper : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4) :
    (n : ℝ) / (64 * K * Real.log (n : ℝ) ^ 4) ≤ (((n - 1) / q : ℕ) : ℝ) := by
  have hlog0 : 0 < Real.log (n : ℝ) := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    linarith
  calc
    _ = ((n : ℝ) / 2) / (2 * (16 * K * Real.log (n : ℝ) ^ 4)) := by ring
    _ ≤ ((n - 1 : ℕ) : ℝ) / (2 * (16 * K * Real.log (n : ℝ) ^ 4)) :=
      div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ ((n - 1 : ℕ) : ℝ) / (2 * (q : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hqupper (by norm_num))
    _ ≤ _ := nat_div_ge_half_real_ratio hq hqm
lemma half_pow_sparse_quotient_le_exp {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (hqm : q ≤ n - 1) {K : ℝ} (hK : 0 < K) (hlog : 1 ≤ Real.log (n : ℝ))
    (hqupper : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4) :
    (1 / 2 : ℝ) ^ ((n - 1) / q) ≤
      Real.exp (-(Real.log 2 / (64 * K)) * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  have hcount := sparse_quotient_lower hn hq hqm hK hlog hqupper
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    _ = Real.exp ((((n - 1) / q : ℕ) : ℝ) * Real.log (1 / 2 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = Real.exp (-((((n - 1) / q : ℕ) : ℝ) * Real.log 2)) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      congr 1
      ring
    _ ≤ Real.exp (-((n : ℝ) / (64 * K * Real.log (n : ℝ) ^ 4) * Real.log 2)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_right hcount hlog2.le)
    _ = _ := by congr 1; ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology
lemma eventually_geometric_quarter_le_exp {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᶠ n : ℕ in atTop, b ^ ((n - 1) / 4) ≤
      Real.exp (-(-Real.log b / 16) * (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 5] with n hn
  have hquot := nat_div_ge_half_real_ratio (by norm_num : 0 < 4)
    (by omega : 4 ≤ n - 1)
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (n : ℝ) / 16 ≤ (((n - 1) / 4 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hquot
    norm_num at hquot
    linarith
  have hlog : Real.log b < 0 := Real.log_neg hb0 hb1
  calc
    _ = Real.exp ((((n - 1) / 4 : ℕ) : ℝ) * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hb0]
    _ ≤ Real.exp (((n : ℝ) / 16) * Real.log b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hk hlog.le)
    _ = _ := by congr 1; ring
lemma geometric_quarter_isBigO_rpow {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (A : ℝ) :
    (fun n : ℕ ↦ b ^ ((n - 1) / 4)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have hc : 0 < -Real.log b / 16 := div_pos (neg_pos.mpr (Real.log_neg hb0 hb1)) (by norm_num)
  have hexp : (fun n : ℕ ↦ Real.exp (-(-Real.log b / 16) * (n : ℝ))) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
    simpa only [Function.comp_def] using
      ((isLittleO_exp_neg_mul_rpow_atTop hc (-A)).comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).isBigO
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans hexp
  filter_upwards [eventually_geometric_quarter_le_exp hb0 hb1] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb0.le _),
    abs_of_nonneg (Real.exp_pos _).le] using hn
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics Real
open scoped Topology
lemma log_nat_pow_isLittleO_nat (d : ℕ) :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using h
lemma tendsto_log_nat_pow_div_nat (d : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ d / (n : ℝ)) atTop (𝓝 0) :=
  (log_nat_pow_isLittleO_nat d).tendsto_div_nhds_zero
lemma exists_threshold_logarithmic_prime_scale (K : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ Real.log (n : ℝ) ∧ 64 * K * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ 64 * K * Real.log (n : ℝ) ^ 4 / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using (tendsto_log_nat_pow_div_nat 4).const_mul (64 * K)
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
      64 * K * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, hl.eventually_ge_atTop 1,
      ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn hlog hsmall
    refine ⟨hn, hlog, ?_⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simpa only [one_mul] using (div_le_iff₀ hn0).mp hsmall
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨max 2 N, le_max_left _ _, fun n hn ↦ (hN n ((le_max_right _ _).trans hn)).2⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
open scoped Topology
lemma eventually_log_pow_le_nat_div_log_pow (B : ℝ) {a : ℝ} (ha : 0 < a) (r s : ℕ) :
    ∀ᶠ n : ℕ in atTop, B * Real.log (n : ℝ) ^ r ≤
      a * (n : ℝ) / Real.log (n : ℝ) ^ s := by
  have ht : Tendsto (fun n : ℕ ↦ B * Real.log (n : ℝ) ^ (r + s) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using (tendsto_log_nat_pow_div_nat (r + s)).const_mul B
  filter_upwards [eventually_ge_atTop 2, ht.eventually_le_const ha] with n hn hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  apply (le_div_iff₀ (pow_pos hlog s)).mpr
  rw [mul_assoc, ← pow_add]
  exact (div_le_iff₀ hn0).mp hsmall
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology
lemma eventually_exp_cutoff_cost_le_rpow {a C A : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (4 * (⌈C * Real.log (n : ℝ)⌉₊ : ℝ) ^ 2 -
        a * (n : ℝ) / Real.log (n : ℝ) ^ 4) ≤ (n : ℝ) ^ (-A) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, ht.eventually_ge_atTop 1,
    eventually_log_pow_le_nat_div_log_pow (4 * (C + 1) ^ 2 + A) ha 2 4] with n hn hlog hdom
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hC hlog0)
  have hupper : (⌈C * Real.log (n : ℝ)⌉₊ : ℝ) ≤ (C + 1) * Real.log (n : ℝ) := by
    nlinarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg ⌈C * Real.log (n : ℝ)⌉₊) hupper 2
  have hlogsq : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hAlog := mul_le_mul_of_nonneg_left hlogsq hA
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  nlinarith
lemma two_rpow_neg_half_ceil_log_le {n : ℕ} (hn : 0 < n) (A : ℝ) :
    (2 : ℝ) ^ (-(⌈(2 * A / Real.log 2) * Real.log (n : ℝ)⌉₊ : ℝ) / 2) ≤
      (n : ℝ) ^ (-A) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil ((2 * A / Real.log 2) * Real.log (n : ℝ))
  have h := mul_le_mul_of_nonneg_left hceil hl2.le
  have he : Real.log 2 * ((2 * A / Real.log 2) * Real.log (n : ℝ)) =
      2 * A * Real.log (n : ℝ) := by field_simp
  rw [he] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  apply Real.exp_le_exp.mpr
  nlinarith
lemma isBigO_rpow_of_reciprocal_finite_bound {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hbound : ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      f n ≤ Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
        6 * (2 : ℝ) ^ (-(L : ℝ) / 2)) (A : ℝ) (hA : 0 < A) :
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  let C := 2 * A / Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine Asymptotics.isBigO_iff.mpr ⟨7, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1,
    eventually_exp_cutoff_cost_le_rpow ha hC hA.le] with n hn hn1 hfirst
  have hfinite := hbound n hn ⌈C * Real.log (n : ℝ)⌉₊
  have htail := two_rpow_neg_half_ceil_log_le (by omega : 0 < n) A
  change (2 : ℝ) ^ (-(⌈C * Real.log (n : ℝ)⌉₊ : ℝ) / 2) ≤ (n : ℝ) ^ (-A) at htail
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-A))]
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma monic_or_neg_monic_of_dvd_monic {J P : ℤ[X]} (hP : P.Monic) (hdiv : J ∣ P) :
    J.Monic ∨ (-J).Monic := by
  obtain ⟨Q, hQ⟩ := hdiv
  have he : J.leadingCoeff * Q.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hQ, hP.leadingCoeff]
  have hu : IsUnit J.leadingCoeff := isUnit_iff_dvd_one.mpr ⟨Q.leadingCoeff, he.symm⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · exact Or.inl h
  · right
    change (-J).leadingCoeff = 1
    rw [leadingCoeff_neg, h]
    norm_num
lemma irreducible_map_rat_of_dvd_monic {J P : ℤ[X]} (hP : P.Monic) (hdiv : J ∣ P)
    (hirr : Irreducible J) : Irreducible (J.map (Int.castRingHom ℚ)) := by
  rcases monic_or_neg_monic_of_dvd_monic hP hdiv with hJ | hJ
  · exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hJ.isPrimitive).mp hirr
  · have hi : Irreducible (-J) := (Associated.refl J).neg_right.irreducible hirr
    have hm := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hJ.isPrimitive).mp hi
    have hn := (Associated.refl ((-J).map (Int.castRingHom ℚ))).neg_right.irreducible hm
    simpa only [Polynomial.map_neg, neg_neg] using hn
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_monic_rational_irreducible_divisor {P : ℤ[X]} (hP : P.Monic)
    (hdegree : 0 < P.natDegree) :
    ∃ J : ℤ[X], J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧ J ∣ P := by
  have hunit : ¬ IsUnit P := by
    intro h
    have he := hP.isUnit_iff.mp h
    simp [he] at hdegree
  obtain ⟨J, hirr, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hunit hP.ne_zero
  rcases monic_or_neg_monic_of_dvd_monic hP hdiv with hJ | hJ
  · exact ⟨J, hJ, irreducible_map_rat_of_dvd_monic hP hdiv hirr, hdiv⟩
  · have hneg : Irreducible (-J) := (Associated.refl J).neg_right.irreducible hirr
    exact ⟨-J, hJ, irreducible_map_rat_of_dvd_monic hP hdiv.neg_left hneg, hdiv.neg_left⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def IsBinary (p : ℤ[X]) : Prop := ∀ k, p.coeff k = 0 ∨ p.coeff k = 1
structure HasBinaryEndpoints (n : ℕ) (p : ℤ[X]) : Prop where
  monic : p.Monic
  degree : p.natDegree = n
  constant : p.coeff 0 = 1
  binary : IsBinary p
lemma IsBinary.coeff_nonneg {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    0 ≤ p.coeff k := by
  rcases hp k with h | h <;> simp [h]
lemma IsBinary.coeff_le_one {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    p.coeff k ≤ 1 := by
  rcases hp k with h | h <;> simp [h]
lemma IsBinary.coeff_sq {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    p.coeff k ^ 2 = p.coeff k := by
  rcases hp k with h | h <;> simp [h]
lemma isBinary_iff_coeff_sq (p : ℤ[X]) :
    IsBinary p ↔ ∀ k, p.coeff k ^ 2 = p.coeff k := by
  constructor
  · exact fun hp ↦ hp.coeff_sq
  · intro hp k
    have h : p.coeff k * (p.coeff k - 1) = 0 := by nlinarith [hp k]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
lemma HasBinaryEndpoints.ne_zero {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p ≠ 0 := hp.monic.ne_zero
lemma HasBinaryEndpoints.coeff_degree {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.coeff n = 1 := by
  rw [← hp.degree]
  exact hp.monic
lemma HasBinaryEndpoints.coeff_eq_zero_above {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hk : n < k) : p.coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (hp.degree ▸ hk)
lemma HasBinaryEndpoints.natTrailingDegree {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.natTrailingDegree = 0 := by
  exact Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hp.constant]; norm_num))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma sum_range_pow_lt_pow_of_two_le {r : ℝ} (hr : 2 ≤ r) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) < r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hr0 : 0 ≤ r := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr (pow_nonneg hr0 n)
    nlinarith
lemma monic_root_norm_lt_two {p : ℂ[X]} (hp : p.Monic)
    (hc : ∀ k < p.natDegree, ‖p.coeff k‖ ≤ 1) {z : ℂ} (hz : p.eval z = 0) :
    ‖z‖ < 2 := by
  have he : (∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i) + z ^ p.natDegree = 0 := by
    rw [← hz, eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hs : (∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i) = -z ^ p.natDegree :=
    eq_neg_of_add_eq_zero_left he
  have hle : ‖z‖ ^ p.natDegree ≤ ∑ i ∈ Finset.range p.natDegree, ‖z‖ ^ i := by
    calc
      _ = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ := by
        rw [hs, norm_neg, norm_pow]
      _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hc i (Finset.mem_range.mp hi))
            (pow_nonneg (norm_nonneg z) i)
  by_contra hn
  exact (not_lt_of_ge hle) (sum_range_pow_lt_pow_of_two_le (le_of_not_gt hn) p.natDegree)
lemma HasBinaryEndpoints.root_norm_lt_two {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {z : ℂ} (hz : p.eval₂ (Int.castRingHom ℂ) z = 0) :
    ‖z‖ < 2 := by
  apply monic_root_norm_lt_two (hp.monic.map (Int.castRingHom ℂ))
  · intro k _
    rw [coeff_map]
    rcases hp.binary k with hk | hk <;> simp [hk]
  · simpa only [eval_map] using hz
lemma HasBinaryEndpoints.divisor_root_norm_lt_two {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hdvd : J ∣ p) {z : ℂ}
    (hz : J.eval₂ (Int.castRingHom ℂ) z = 0) : ‖z‖ < 2 := by
  apply hp.root_norm_lt_two
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, eval₂_mul, hz, zero_mul]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma norm_coeff_mul_X_sub_C_le {p : ℂ[X]} {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ k, ‖p.coeff k‖ ≤ B) (z : ℂ) (k : ℕ) :
    ‖((X - C z) * p).coeff k‖ ≤ (1 + ‖z‖) * B := by
  rw [sub_mul, coeff_sub, coeff_C_mul]
  have hx : ‖(X * p).coeff k‖ ≤ B := by
    cases k with
    | zero => simpa only [coeff_X_mul_zero, norm_zero] using hB
    | succ k => simpa only [coeff_X_mul] using hp k
  calc
    _ ≤ ‖(X * p).coeff k‖ + ‖z * p.coeff k‖ := norm_sub_le _ _
    _ ≤ B + ‖z‖ * B := add_le_add hx (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp k) (norm_nonneg z))
    _ = _ := by ring
lemma norm_coeff_prod_X_sub_C_le (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ 2) (k : ℕ) :
    ‖((s.map (fun z ↦ X - C z)).prod).coeff k‖ ≤ (3 : ℝ) ^ s.card := by
  revert hs k
  induction s using Multiset.induction_on with
  | empty =>
    intro _ k
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | @cons z s ih =>
    intro hs k
    have hz : ‖z‖ ≤ 2 := hs z (Multiset.mem_cons_self z s)
    have hrest : ∀ w ∈ s, ‖w‖ ≤ 2 :=
      fun w hw ↦ hs w (Multiset.mem_cons_of_mem hw)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc
      _ ≤ (1 + ‖z‖) * (3 : ℝ) ^ s.card :=
        norm_coeff_mul_X_sub_C_le (by positivity) (ih hrest) z k
      _ ≤ 3 * (3 : ℝ) ^ s.card :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := mul_comm _ _
lemma monic_coeff_norm_le_of_roots_le_two {p : ℂ[X]} (hp : p.Monic)
    (hr : ∀ z ∈ p.roots, ‖z‖ ≤ 2) (k : ℕ) :
    ‖p.coeff k‖ ≤ (3 : ℝ) ^ p.natDegree := by
  have he := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have h := norm_coeff_prod_X_sub_C_le p.roots hr k
  rw [← he, IsAlgClosed.card_roots_eq_natDegree] at h
  exact h
lemma HasBinaryEndpoints.monic_divisor_coeff_abs_le {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (k : ℕ) :
    |J.coeff k| ≤ (3 : ℤ) ^ J.natDegree := by
  have hm := hJ.map (Int.castRingHom ℂ)
  have hr : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 2 := by
    intro z hz
    have he : (J.map (Int.castRingHom ℂ)).eval z = 0 := (mem_roots hm.ne_zero).mp hz
    rw [eval_map] at he
    exact (hp.divisor_root_norm_lt_two hdvd he).le
  have h := monic_coeff_norm_le_of_roots_le_two hm hr k
  rw [coeff_map, hJ.natDegree_map] at h
  change ‖(J.coeff k : ℂ)‖ ≤ (3 : ℝ) ^ J.natDegree at h
  rw [Complex.norm_intCast] at h
  exact_mod_cast h
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
noncomputable def monicPolynomialOfCoefficients {h : ℕ} (w : Fin h → ℤ) : ℤ[X] :=
  X ^ h + ∑ i : Fin h, C (w i) * X ^ i.val
lemma monic_eq_polynomialOfCoefficients {p : ℤ[X]} (hp : p.Monic) :
    p = monicPolynomialOfCoefficients (fun i : Fin p.natDegree ↦ p.coeff i.val) := by
  unfold monicPolynomialOfCoefficients
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ C (p.coeff i) * X ^ i) p.natDegree]
  calc
    p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
      p.as_sum_range_C_mul_X_pow
    _ = _ := by rw [Finset.sum_range_succ, hp.coeff_natDegree, C_1, one_mul, add_comm]
noncomputable def boundedMonicFamily (h H : ℕ) : Finset ℤ[X] :=
  Finset.univ.image (fun w : Fin h → {z : ℤ // z ∈ Finset.Icc (-(H : ℤ)) H} ↦
    monicPolynomialOfCoefficients (fun i ↦ (w i).val))
lemma card_bounded_integer_interval (H : ℕ) :
    (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
  rw [Int.card_Icc]
  omega
lemma card_boundedMonicFamily_le (h H : ℕ) :
    (boundedMonicFamily h H).card ≤ (2 * H + 1) ^ h := by
  unfold boundedMonicFamily
  calc
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
        card_bounded_integer_interval, Fintype.card_fin]
lemma mem_boundedMonicFamily_of_coeff_bound {h H : ℕ} {p : ℤ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = h) (hc : ∀ k < h, |p.coeff k| ≤ (H : ℤ)) :
    p ∈ boundedMonicFamily h H := by
  let w : Fin h → {z : ℤ // z ∈ Finset.Icc (-(H : ℤ)) H} := fun i ↦
    ⟨p.coeff i.val, Finset.mem_Icc.mpr (abs_le.mp (hc i.val i.isLt))⟩
  apply Finset.mem_image.mpr
  refine ⟨w, Finset.mem_univ _, ?_⟩
  have he := monic_eq_polynomialOfCoefficients hp
  rw [hdeg] at he
  exact he.symm
lemma HasBinaryEndpoints.monic_divisor_mem_boundedFamily {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) :
    J ∈ boundedMonicFamily J.natDegree (3 ^ J.natDegree) := by
  apply mem_boundedMonicFamily_of_coeff_bound hJ rfl
  intro k _
  exact_mod_cast hp.monic_divisor_coeff_abs_le hJ hdvd k
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma bounded_coefficient_choices_le_three_pow (h : ℕ) :
    (2 * (3 : ℝ) ^ h + 1) ^ h ≤ (3 : ℝ) ^ ((h + 1) * h) := by
  calc
    _ ≤ ((3 : ℝ) ^ (h + 1)) ^ h := by
      apply pow_le_pow_left₀ (by positivity)
      rw [pow_succ]
      have hpow : (1 : ℝ) ≤ 3 ^ h := one_le_pow₀ (by norm_num)
      nlinarith
    _ = _ := (pow_mul _ _ _).symm
lemma divisor_count_summand_le_exp {h L : ℕ} (hh : 1 ≤ h) (hL : h ≤ L) :
    (2 * (3 : ℝ) ^ h + 1) ^ h ≤ Real.exp (3 * (L : ℝ) ^ 2) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hLR : (h : ℝ) ≤ L := by exact_mod_cast hL
  have hprod : (((h + 1) * h : ℕ) : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by
    push_cast
    have hsq := mul_le_mul hLR hLR (Nat.cast_nonneg h) (Nat.cast_nonneg L)
    nlinarith [sq_nonneg ((h : ℝ) - 1)]
  have hlog : Real.log 3 ≤ 3 / 2 := by linarith [Real.log_three_lt_d9]
  calc
    _ ≤ (3 : ℝ) ^ ((h + 1) * h) := bounded_coefficient_choices_le_three_pow h
    _ = Real.exp (((h + 1) * h : ℕ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (3 * (L : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (((h + 1) * h : ℕ) : ℝ) * (3 / 2) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ _ := by nlinarith
lemma sum_divisor_counts_le_exp (L : ℕ) :
    (∑ h ∈ Finset.Icc 1 L, (2 * (3 : ℝ) ^ h + 1) ^ h) ≤
      Real.exp (4 * (L : ℝ) ^ 2) := by
  have hLe : (L : ℝ) ≤ Real.exp ((L : ℝ) ^ 2) := by
    calc
      _ ≤ (L : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg ((L : ℝ) - 1), show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
      _ ≤ _ := Real.add_one_le_exp _
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 L, Real.exp (3 * (L : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro h hh
      exact divisor_count_summand_le_exp (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hh).2
    _ = (L : ℝ) * Real.exp (3 * (L : ℝ) ^ 2) := by simp
    _ ≤ Real.exp ((L : ℝ) ^ 2) * Real.exp (3 * (L : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hLe (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
noncomputable def smallDivisorCandidates (L : ℕ) : Finset ℤ[X] :=
  (Finset.Icc 1 L).biUnion (fun h ↦ boundedMonicFamily h (3 ^ h))
lemma HasBinaryEndpoints.monic_divisor_mem_candidates {n L : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p)
    (hpos : 1 ≤ J.natDegree) (hL : J.natDegree ≤ L) : J ∈ smallDivisorCandidates L := by
  exact Finset.mem_biUnion.mpr ⟨J.natDegree, Finset.mem_Icc.mpr ⟨hpos, hL⟩,
    hp.monic_divisor_mem_boundedFamily hJ hdvd⟩
lemma card_smallDivisorCandidates_le_sum (L : ℕ) :
    (smallDivisorCandidates L).card ≤ ∑ h ∈ Finset.Icc 1 L, (2 * 3 ^ h + 1) ^ h := by
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun h _ ↦ card_boundedMonicFamily_le h (3 ^ h)))
lemma card_smallDivisorCandidates_le_exp (L : ℕ) :
    ((smallDivisorCandidates L).card : ℝ) ≤ Real.exp (4 * (L : ℝ) ^ 2) := by
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 L, (2 * (3 : ℝ) ^ h + 1) ^ h := by
      exact_mod_cast card_smallDivisorCandidates_le_sum L
    _ ≤ _ := sum_divisor_counts_le_exp L
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasBinaryEndpoints.eval_real_ge_one {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ p.eval₂ (Int.castRingHom ℝ) t := by
  rw [eval₂_eq_sum_range]
  change 1 ≤ ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k : ℝ) * t ^ k
  have hs := Finset.single_le_sum
    (f := fun k ↦ (p.coeff k : ℝ) * t ^ k)
    (fun k _ ↦ mul_nonneg (by exact_mod_cast hp.binary.coeff_nonneg k) (pow_nonneg ht k))
    (Finset.mem_range.mpr (Nat.zero_lt_succ p.natDegree))
  simpa only [hp.constant, Int.cast_one, pow_zero, mul_one] using hs
lemma HasBinaryEndpoints.eval_real_pos {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {t : ℝ} (ht : 0 ≤ t) :
    0 < p.eval₂ (Int.castRingHom ℝ) t :=
  lt_of_lt_of_le (by norm_num) (hp.eval_real_ge_one ht)
lemma monic_exists_positive_root_of_constant_neg {p : ℝ[X]} (hp : p.Monic)
    (h0 : p.coeff 0 < 0) : ∃ t : ℝ, 0 < t ∧ p.eval t = 0 := by
  have hdeg : 0 < p.natDegree := by
    by_contra hn
    have hz : p.natDegree = 0 := by omega
    have hc := hp.coeff_natDegree
    rw [hz] at hc
    rw [hc] at h0
    linarith
  have hlim := p.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp hdeg) (by rw [hp.leadingCoeff]; norm_num)
  obtain ⟨b, hb⟩ := Filter.Eventually.exists_forall_of_atTop (hlim.eventually_gt_atTop 0)
  have hc0 : (0 : ℝ) ≤ max 1 b := le_trans (by norm_num) (le_max_left 1 b)
  have hce : 0 < p.eval (max 1 b) := hb _ (le_max_right 1 b)
  have he0 : p.eval 0 < 0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  obtain ⟨t, ht, hroot⟩ := intermediate_value_Icc hc0 p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval (max 1 b)) from ⟨he0.le, hce.le⟩)
  refine ⟨t, ?_, hroot⟩
  by_contra hpos
  have hz : t = 0 := le_antisymm (le_of_not_gt hpos) ht.1
  rw [hz] at hroot
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def ReducibleOverRat (p : ℤ[X]) : Prop :=
  ¬ Irreducible (p.map (Int.castRingHom ℚ))
lemma monic_reducibleOverRat_iff {p : ℤ[X]} (hp : p.Monic) :
    ReducibleOverRat p ↔ ¬ Irreducible p := by
  unfold ReducibleOverRat
  exact not_congr (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp.isPrimitive).symm
lemma monic_factors_of_reducibleOverRat {p : ℤ[X]} (hp : p.Monic)
    (hdegree : 0 < p.natDegree) (hred : ReducibleOverRat p) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      0 < a.natDegree ∧ 0 < b.natDegree := by
  classical
  have hn : p ≠ 1 := by
    intro he
    simp [he] at hdegree
  have hi := (monic_reducibleOverRat_iff hp).mp hred
  have hf : ¬ ∀ a b : ℤ[X], a.Monic → b.Monic → a * b = p →
      a.natDegree = 0 ∨ b.natDegree = 0 := by
    intro h
    exact hi (hp.irreducible_iff_natDegree.mpr ⟨hn, h⟩)
  push Not at hf
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hf
  exact ⟨a, b, ha, hb, hab.symm, Nat.pos_of_ne_zero had, Nat.pos_of_ne_zero hbd⟩
lemma HasBinaryEndpoints.monic_factors_of_reducible {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 1 ≤ n) (hred : ReducibleOverRat p) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      0 < a.natDegree ∧ 0 < b.natDegree :=
  monic_factors_of_reducibleOverRat hp.monic (by rw [hp.degree]; omega) hred
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def HasCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 0 < k ∧ cyclotomic k ℤ ∣ p
def HasHigherCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 2 ≤ k.totient ∧ cyclotomic k ℤ ∣ p
lemma HasCyclotomicDivisor.of_dvd {p q : ℤ[X]} (hp : HasCyclotomicDivisor p)
    (hdvd : p ∣ q) : HasCyclotomicDivisor q := by
  obtain ⟨k, hk, hkp⟩ := hp
  exact ⟨k, hk, hkp.trans hdvd⟩
lemma HasHigherCyclotomicDivisor.hasCyclotomicDivisor {p : ℤ[X]}
    (hp : HasHigherCyclotomicDivisor p) : HasCyclotomicDivisor p := by
  obtain ⟨k, hk, hd⟩ := hp
  exact ⟨k, Nat.totient_pos.mp (by omega), hd⟩
lemma cyclotomic_dvd_iff_rational (k : ℕ) (p : ℤ[X]) :
    cyclotomic k ℤ ∣ p ↔ cyclotomic k ℚ ∣ p.map (Int.castRingHom ℚ) := by
  rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (cyclotomic.isPrimitive k ℤ),
    map_cyclotomic_int]
lemma HasBinaryEndpoints.eval_int_one_pos {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : 0 < p.eval 1 := by
  have h := hp.eval_real_pos (t := 1) (by norm_num)
  rw [eval₂_at_one] at h
  change (0 : ℝ) < ((p.eval 1 : ℤ) : ℝ) at h
  exact_mod_cast h
lemma HasBinaryEndpoints.not_cyclotomic_one_dvd {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : ¬ cyclotomic 1 ℤ ∣ p := by
  intro hd
  have hz : IsRoot p (1 : ℤ) := by
    apply dvd_iff_isRoot.mp
    simpa only [cyclotomic_one, C_1] using hd
  have hpos := hp.eval_int_one_pos
  change p.eval 1 = 0 at hz
  omega
lemma cyclotomic_two_dvd_iff_minus_one (p : ℤ[X]) :
    cyclotomic 2 ℤ ∣ p ↔ p.eval (-1) = 0 := by
  simpa [cyclotomic_two, IsRoot.def] using (dvd_iff_isRoot (p := p) (a := (-1 : ℤ)))
lemma HasBinaryEndpoints.cyclotomic_alternative {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcyc : HasCyclotomicDivisor p) :
    HasHigherCyclotomicDivisor p ∨ p.eval (-1) = 0 := by
  obtain ⟨k, hk, hd⟩ := hcyc
  by_cases hhigh : 2 ≤ k.totient
  · exact Or.inl ⟨k, hhigh, hd⟩
  have ht : k.totient = 1 := by have := Nat.totient_pos.mpr hk; omega
  rcases Nat.totient_eq_one_iff.mp ht with rfl | rfl
  · exact False.elim (hp.not_cyclotomic_one_dvd hd)
  · exact Or.inr ((cyclotomic_two_dvd_iff_minus_one p).mp hd)
lemma HasBinaryEndpoints.hasCyclotomicDivisor_iff {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    HasCyclotomicDivisor p ↔ HasHigherCyclotomicDivisor p ∨ p.eval (-1) = 0 := by
  refine ⟨hp.cyclotomic_alternative, ?_⟩
  rintro (h | h)
  · exact h.hasCyclotomicDivisor
  · exact ⟨2, by norm_num, (cyclotomic_two_dvd_iff_minus_one p).mpr h⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma reverse_natDegree_of_constant_ne_zero {R : Type*} [Semiring R]
    {p : R[X]} (h : p.coeff 0 ≠ 0) : p.reverse.natDegree = p.natDegree := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero]
lemma reverse_reverse_of_constant_ne_zero {R : Type*} [Semiring R]
    {p : R[X]} (h : p.coeff 0 ≠ 0) : p.reverse.reverse = p := by
  unfold Polynomial.reverse
  rw [show (p.reflect p.natDegree).natDegree = p.natDegree from
    reverse_natDegree_of_constant_ne_zero h]
  exact Polynomial.reflect_reflect
lemma IsBinary.reverse {p : ℤ[X]} (hp : IsBinary p) : IsBinary p.reverse := by
  intro k
  rw [Polynomial.coeff_reverse]
  exact hp _
lemma HasBinaryEndpoints.reverse {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : HasBinaryEndpoints n p.reverse := by
  have hc : p.coeff 0 ≠ 0 := by rw [hp.constant]; norm_num
  refine ⟨?_, ?_, ?_, hp.binary.reverse⟩
  · change p.reverse.leadingCoeff = 1
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff_eq_coeff_zero hc,
      hp.constant]
  · rw [reverse_natDegree_of_constant_ne_zero hc, hp.degree]
  · rw [Polynomial.coeff_zero_reverse]
    exact hp.monic
lemma HasBinaryEndpoints.reverse_reverse {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.reverse.reverse = p :=
  reverse_reverse_of_constant_ne_zero (by rw [hp.constant]; norm_num)
noncomputable def autocorrelation (p : ℤ[X]) : ℤ[X] := p * p.reverse
lemma autocorrelation_reverse {p : ℤ[X]} (hp : p.coeff 0 ≠ 0) :
    autocorrelation p.reverse = autocorrelation p := by
  simp only [autocorrelation, reverse_reverse_of_constant_ne_zero hp, mul_comm]
lemma autocorrelation_mul (a b : ℤ[X]) :
    autocorrelation (a * b) = autocorrelation a * autocorrelation b := by
  simp only [autocorrelation, Polynomial.reverse_mul_of_domain]
  ring
lemma autocorrelation_factor_reverse (a : ℤ[X]) {b : ℤ[X]} (hb : b.coeff 0 ≠ 0) :
    autocorrelation (a * b.reverse) = autocorrelation (a * b) := by
  rw [autocorrelation_mul, autocorrelation_reverse hb, autocorrelation_mul]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
noncomputable def reducePolynomial (r : ℕ) (p : ℤ[X]) : (ZMod r)[X] :=
  p.map (Int.castRingHom (ZMod r))
lemma coeff_reducePolynomial (r : ℕ) (p : ℤ[X]) (k : ℕ) :
    (reducePolynomial r p).coeff k = (p.coeff k : ZMod r) := by
  simp [reducePolynomial]
lemma reducePolynomial_mul (r : ℕ) (p q : ℤ[X]) :
    reducePolynomial r (p * q) = reducePolynomial r p * reducePolynomial r q := by
  simp [reducePolynomial]
noncomputable def zeroOneLift (p : (ZMod 2)[X]) : ℤ[X] :=
  p.sum (fun k c ↦ monomial k (c.val : ℤ))
lemma coeff_zeroOneLift (p : (ZMod 2)[X]) (k : ℕ) :
    (zeroOneLift p).coeff k = ((p.coeff k).val : ℤ) := by
  classical
  simp only [zeroOneLift, sum_def, finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k ∈ p.support
  · simp only [Finset.sum_ite_eq', if_pos hk]
  · have hc : p.coeff k = 0 := notMem_support_iff.mp hk
    simp only [Finset.sum_ite_eq', if_neg hk, hc, ZMod.val_zero, Nat.cast_zero]
lemma zeroOneLift_binary (p : (ZMod 2)[X]) : IsBinary (zeroOneLift p) := by
  intro k
  rw [coeff_zeroOneLift]
  have h := (p.coeff k).val_lt
  have : (p.coeff k).val = 0 ∨ (p.coeff k).val = 1 := by omega
  rcases this with h | h <;> simp [h]
lemma reduce_zeroOneLift (p : (ZMod 2)[X]) :
    reducePolynomial 2 (zeroOneLift p) = p := by
  ext k
  simp [coeff_reducePolynomial, coeff_zeroOneLift]
lemma zeroOneLift_reduce {p : ℤ[X]} (hp : IsBinary p) :
    zeroOneLift (reducePolynomial 2 p) = p := by
  ext k
  rw [coeff_zeroOneLift, coeff_reducePolynomial]
  rcases hp k with h | h <;>
    simp only [h, Int.cast_zero, Int.cast_one, ZMod.val_zero, ZMod.val_one,
      Nat.cast_zero, Nat.cast_one]
lemma zeroOneLift_injective : Function.Injective zeroOneLift := by
  intro p q h
  simpa only [reduce_zeroOneLift] using congrArg (reducePolynomial 2) h
lemma IsBinary.eq_of_reduce_eq {p q : ℤ[X]} (hp : IsBinary p) (hq : IsBinary q)
    (h : reducePolynomial 2 p = reducePolynomial 2 q) : p = q := by
  simpa only [zeroOneLift_reduce hp, zeroOneLift_reduce hq] using congrArg zeroOneLift h
lemma support_zeroOneLift (p : (ZMod 2)[X]) :
    (zeroOneLift p).support = p.support := by
  ext k
  simp only [mem_support_iff, coeff_zeroOneLift]
  constructor
  · intro h hc
    apply h
    rw [hc]
    rfl
  · intro h hc
    apply h
    apply (ZMod.val_eq_zero _).mp
    exact_mod_cast hc
lemma natDegree_zeroOneLift (p : (ZMod 2)[X]) :
    (zeroOneLift p).natDegree = p.natDegree := by
  apply le_antisymm <;> apply natDegree_le_natDegree <;> apply degree_mono
  · rw [support_zeroOneLift]
  · rw [support_zeroOneLift]
lemma zeroOneLift_reverse (p : (ZMod 2)[X]) :
    zeroOneLift p.reverse = (zeroOneLift p).reverse := by
  ext k
  simp only [coeff_zeroOneLift, coeff_reverse, natDegree_zeroOneLift]
lemma IsBinary.natDegree_reduce {p : ℤ[X]} (hp : IsBinary p) :
    (reducePolynomial 2 p).natDegree = p.natDegree := by
  rw [← natDegree_zeroOneLift, zeroOneLift_reduce hp]
lemma IsBinary.reduce_reverse {p : ℤ[X]} (hp : IsBinary p) :
    reducePolynomial 2 p.reverse = (reducePolynomial 2 p).reverse := by
  ext k
  simp only [coeff_reducePolynomial, coeff_reverse, hp.natDegree_reduce]
def CongruentMod (r : ℕ) (p q : ℤ[X]) : Prop :=
  reducePolynomial r p = reducePolynomial r q
lemma congruentMod_iff_coeff_dvd (r : ℕ) (p q : ℤ[X]) :
    CongruentMod r p q ↔ ∀ k, (r : ℤ) ∣ p.coeff k - q.coeff k := by
  unfold CongruentMod
  rw [Polynomial.ext_iff]
  simp only [coeff_reducePolynomial]
  constructor
  · intro h k
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).mp (h k).symm
  · intro h k
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).mpr (h k)).symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma monic_reduce_natDegree (r : ℕ) [Nontrivial (ZMod r)] {p : ℤ[X]} (hp : p.Monic) :
    (reducePolynomial r p).natDegree = p.natDegree :=
  hp.natDegree_map (Int.castRingHom (ZMod r))
lemma monic_reduce_reverse (r : ℕ) [Nontrivial (ZMod r)] {p : ℤ[X]} (hp : p.Monic) :
    reducePolynomial r p.reverse = (reducePolynomial r p).reverse := by
  ext k
  simp only [coeff_reducePolynomial, coeff_reverse, monic_reduce_natDegree r hp]
lemma reducePolynomial_dvd (r : ℕ) {a b : ℤ[X]} (hab : a ∣ b) :
    reducePolynomial r a ∣ reducePolynomial r b := by
  obtain ⟨q, hq⟩ := hab
  exact ⟨reducePolynomial r q, by rw [hq, reducePolynomial_mul]⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma coeff_autocorrelation_middle (p : ℤ[X]) :
    (autocorrelation p).coeff p.natDegree =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i ^ 2 := by
  rw [autocorrelation, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ p.coeff i * p.reverse.coeff j)]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i ≤ p.natDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.sub_le _ _),
    Nat.sub_sub_self h, pow_two]
lemma eval_one_eq_sum_coeff (p : ℤ[X]) :
    p.eval 1 = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
  simp [Polynomial.eval_eq_sum_range]
lemma int_mul_sub_one_nonneg (z : ℤ) : 0 ≤ z * (z - 1) := by
  by_cases hz : z ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos hz (by omega)
  · exact mul_nonneg (by omega) (by omega)
lemma isBinary_of_sum_sq_eq_sum (q : ℤ[X])
    (hq : (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i ^ 2) =
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) : IsBinary q := by
  have hz : (∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (q.coeff i - 1)) = 0 := by
    simp_rw [mul_sub, mul_one, ← pow_two]
    rw [Finset.sum_sub_distrib, hq, sub_self]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.range (q.natDegree + 1)) ↦
      int_mul_sub_one_nonneg (q.coeff i))).mp hz
  intro k
  by_cases hk : k ≤ q.natDegree
  · rcases mul_eq_zero.mp (hall k (Finset.mem_range.mpr (by omega))) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
lemma IsBinary.of_autocorrelation_eq {p q : ℤ[X]} (hp : IsBinary p)
    (hdegree : q.natDegree = p.natDegree)
    (hc : autocorrelation q = autocorrelation p) (he : q.eval 1 = p.eval 1) :
    IsBinary q := by
  apply isBinary_of_sum_sq_eq_sum
  calc
    (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i ^ 2) =
        (autocorrelation q).coeff q.natDegree := (coeff_autocorrelation_middle q).symm
    _ = (autocorrelation p).coeff p.natDegree := by rw [hc, hdegree]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i ^ 2 :=
      coeff_autocorrelation_middle p
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hp.coeff_sq i
    _ = p.eval 1 := (eval_one_eq_sum_coeff p).symm
    _ = q.eval 1 := he.symm
    _ = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i := eval_one_eq_sum_coeff q
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma eval_one_reverse (p : ℤ[X]) : p.reverse.eval 1 = p.eval 1 := by
  letI : Invertible (1 : ℤ) := invertibleOne
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℤ) (1 : ℤ) p
  simpa using h
lemma IsBinary.factor_reverse {p a b : ℤ[X]} (hp : IsBinary p)
    (h0 : p.coeff 0 ≠ 0) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    IsBinary (a * b.reverse) := by
  have hb0 : b.coeff 0 ≠ 0 := by
    rw [hab, Polynomial.mul_coeff_zero] at h0
    exact (mul_ne_zero_iff.mp h0).2
  have hbr : b.reverse ≠ 0 := by simpa using hb.ne_zero
  apply hp.of_autocorrelation_eq
  · rw [Polynomial.natDegree_mul ha.ne_zero hbr,
      reverse_natDegree_of_constant_ne_zero hb0, hab,
      Polynomial.natDegree_mul ha.ne_zero hb.ne_zero]
  · rw [autocorrelation_factor_reverse a hb0, hab]
  · rw [Polynomial.eval_mul, eval_one_reverse, hab, Polynomial.eval_mul]
lemma HasBinaryEndpoints.factor_constants {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    a.coeff 0 = 1 ∧ b.coeff 0 = 1 := by
  have h0 : p.coeff 0 ≠ 0 := by rw [hp.constant]; norm_num
  have hq := hp.binary.factor_reverse h0 ha hb hab
  have hc : a.coeff 0 * b.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, ← hab, hp.constant]
  have ha0 : a.coeff 0 = 1 := by
    have h := hq 0
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_reverse, hb.leadingCoeff,
      mul_one] at h
    rcases h with h | h
    · rw [h, zero_mul] at hc
      norm_num at hc
    · exact h
  exact ⟨ha0, by simpa [ha0] using hc⟩
lemma HasBinaryEndpoints.factor_reverse {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    HasBinaryEndpoints n (a * b.reverse) := by
  obtain ⟨ha0, hb0⟩ := hp.factor_constants ha hb hab
  have hbc : b.coeff 0 ≠ 0 := by rw [hb0]; norm_num
  have hbr : b.reverse ≠ 0 := by simpa using hb.ne_zero
  have hbmonic : b.reverse.Monic := by
    change b.reverse.leadingCoeff = 1
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff_eq_coeff_zero hbc, hb0]
  refine ⟨ha.mul hbmonic, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul ha.ne_zero hbr,
      reverse_natDegree_of_constant_ne_zero hbc,
      ← Polynomial.natDegree_mul ha.ne_zero hb.ne_zero, ← hab, hp.degree]
  · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_reverse, hb.leadingCoeff,
      ha0, mul_one]
  · exact hp.binary.factor_reverse (by rw [hp.constant]; norm_num) ha hb hab
lemma factor_reverse_eq_iff {a b : ℤ[X]} (ha : a ≠ 0) :
    a * b.reverse = a * b ↔ b = b.reverse := by
  constructor
  · intro h
    exact (mul_left_cancel₀ ha h).symm
  · intro h
    exact congrArg (fun q ↦ a * q) h.symm
lemma factor_reverse_eq_reverse_iff {a b : ℤ[X]} (hb : b ≠ 0) :
    a * b.reverse = (a * b).reverse ↔ a = a.reverse := by
  rw [Polynomial.reverse_mul_of_domain]
  have hbr : b.reverse ≠ 0 := by simpa using hb
  constructor
  · intro h
    exact mul_right_cancel₀ hbr h
  · intro h
    exact congrArg (fun q ↦ q * b.reverse) h
theorem binary_factor_reversal {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    a.coeff 0 = 1 ∧ b.coeff 0 = 1 ∧ HasBinaryEndpoints n (a * b.reverse) ∧
      autocorrelation (a * b.reverse) = autocorrelation p ∧
      (a * b.reverse = p ↔ b = b.reverse) ∧
      (a * b.reverse = p.reverse ↔ a = a.reverse) := by
  obtain ⟨ha0, hb0⟩ := hp.factor_constants ha hb hab
  refine ⟨ha0, hb0, hp.factor_reverse ha hb hab, ?_, ?_, ?_⟩
  · rw [autocorrelation_factor_reverse a (by rw [hb0]; norm_num), hab]
  · rw [hab]
    exact factor_reverse_eq_iff ha.ne_zero
  · rw [hab]
    exact factor_reverse_eq_reverse_iff hb.ne_zero
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
def bitValue (b : Bool) : ℤ := if b then 1 else 0
lemma bitValue_binary (b : Bool) : bitValue b = 0 ∨ bitValue b = 1 := by
  cases b <;> simp [bitValue]
lemma bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitValue]
noncomputable def interiorPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  ∑ i : Fin m, C (bitValue (w i)) * X ^ (i.val + 1)
lemma coeff_interiorPolynomial {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (interiorPolynomial w).coeff (i.val + 1) = bitValue (w i) := by
  classical
  simp only [interiorPolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hji : j.val + 1 ≠ i.val + 1 := by
      intro h
      exact hj (Fin.ext (by omega))
    have hij : i.val ≠ j.val := by intro h; exact hj (Fin.ext h.symm)
    simp [hij]
  · simp
lemma coeff_interiorPolynomial_outside {m : ℕ} (w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (interiorPolynomial w).coeff k = 0 := by
  classical
  simp only [interiorPolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val + 1 ≠ k := by
    have := i.isLt
    rcases hk with hk | hk <;> omega
  simp [Ne.symm hi]
noncomputable def wordPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  1 + interiorPolynomial w + X ^ (m + 1)
lemma coeff_wordPolynomial_zero {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).coeff 0 = 1 := by
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w 0 (Or.inl rfl)]
lemma coeff_wordPolynomial_top {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).coeff (m + 1) = 1 := by
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w (m + 1) (Or.inr (by omega))]
lemma coeff_wordPolynomial_internal {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (wordPolynomial w).coeff (i.val + 1) = bitValue (w i) := by
  have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial, hi]
lemma coeff_wordPolynomial_above {m : ℕ} (w : Fin m → Bool) {k : ℕ}
    (hk : m + 1 < k) : (wordPolynomial w).coeff k = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hkm : m + 1 ≠ k := by omega
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w k (Or.inr (by omega)), hk0, Ne.symm hkm]
lemma wordPolynomial_injective {m : ℕ} : Function.Injective (@wordPolynomial m) := by
  intro v w h
  funext i
  apply bitValue_injective
  have hc := congrArg (fun p : ℤ[X] ↦ p.coeff (i.val + 1)) h
  simpa only [coeff_wordPolynomial_internal] using hc
lemma natDegree_wordPolynomial {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun k hk ↦ coeff_wordPolynomial_above w hk)
  · rw [coeff_wordPolynomial_top]
    norm_num
lemma wordPolynomial_endpoints {m : ℕ} (w : Fin m → Bool) :
    HasBinaryEndpoints (m + 1) (wordPolynomial w) := by
  refine ⟨?_, natDegree_wordPolynomial w, coeff_wordPolynomial_zero w, ?_⟩
  · change (wordPolynomial w).coeff (wordPolynomial w).natDegree = 1
    rw [natDegree_wordPolynomial, coeff_wordPolynomial_top]
  · intro k
    by_cases hk0 : k = 0
    · exact Or.inr (by rw [hk0, coeff_wordPolynomial_zero])
    by_cases hkt : k = m + 1
    · exact Or.inr (by rw [hkt, coeff_wordPolynomial_top])
    by_cases hk : k < m + 1
    · let i : Fin m := ⟨k - 1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      rw [← hi, coeff_wordPolynomial_internal]
      exact bitValue_binary _
    · exact Or.inl (coeff_wordPolynomial_above w (by omega))
lemma exists_wordPolynomial_eq {m : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints (m + 1) p) : ∃ w : Fin m → Bool, wordPolynomial w = p := by
  classical
  let w : Fin m → Bool := fun i ↦ decide (p.coeff (i.val + 1) = 1)
  have hw (i : Fin m) : bitValue (w i) = p.coeff (i.val + 1) := by
    rcases hp.binary (i.val + 1) with h | h <;> simp [w, bitValue, h]
  refine ⟨w, ?_⟩
  ext k
  by_cases hk0 : k = 0
  · rw [hk0, coeff_wordPolynomial_zero, hp.constant]
  by_cases hkt : k = m + 1
  · rw [hkt, coeff_wordPolynomial_top, hp.coeff_degree]
  by_cases hk : k < m + 1
  · let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [← hi, coeff_wordPolynomial_internal, hw]
  · rw [coeff_wordPolynomial_above w (by omega), hp.coeff_eq_zero_above (by omega)]
noncomputable def binaryFamily (m : ℕ) : Finset ℤ[X] :=
  Finset.univ.image (@wordPolynomial m)
lemma mem_binaryFamily_iff {m : ℕ} {p : ℤ[X]} :
    p ∈ binaryFamily m ↔ HasBinaryEndpoints (m + 1) p := by
  classical
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact wordPolynomial_endpoints w
  · intro hp
    obtain ⟨w, rfl⟩ := exists_wordPolynomial_eq hp
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
lemma card_binaryFamily (m : ℕ) : (binaryFamily m).card = 2 ^ m := by
  classical
  rw [binaryFamily, Finset.card_image_of_injective _ wordPolynomial_injective]
  simp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
structure HasF2Endpoints (n : ℕ) (p : (ZMod 2)[X]) : Prop where
  monic : p.Monic
  degree : p.natDegree = n
  constant : p.coeff 0 = 1
lemma HasBinaryEndpoints.reduce {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : HasF2Endpoints n (reducePolynomial 2 p) := by
  refine ⟨hp.monic.map _, hp.binary.natDegree_reduce.trans hp.degree, ?_⟩
  rw [coeff_reducePolynomial, hp.constant]
  norm_num
lemma HasF2Endpoints.lift {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : HasBinaryEndpoints n (zeroOneLift p) := by
  refine ⟨?_, (natDegree_zeroOneLift p).trans hp.degree, ?_, zeroOneLift_binary p⟩
  · change (zeroOneLift p).coeff (zeroOneLift p).natDegree = 1
    rw [natDegree_zeroOneLift, coeff_zeroOneLift]
    have hc : p.coeff p.natDegree = 1 := hp.monic
    rw [hc]
    norm_num [ZMod.val_one]
  · rw [coeff_zeroOneLift, hp.constant]
    norm_num [ZMod.val_one]
lemma zeroOneLift_endpoints_iff {n : ℕ} {p : (ZMod 2)[X]} :
    HasBinaryEndpoints n (zeroOneLift p) ↔ HasF2Endpoints n p := by
  constructor
  · intro hp
    simpa only [reduce_zeroOneLift] using hp.reduce
  · exact HasF2Endpoints.lift
lemma HasF2Endpoints.reverse {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : HasF2Endpoints n p.reverse := by
  apply zeroOneLift_endpoints_iff.mp
  rw [zeroOneLift_reverse]
  exact hp.lift.reverse
lemma HasF2Endpoints.mul {d e : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b) :
    HasF2Endpoints (d + e) (a * b) := by
  refine ⟨ha.monic.mul hb.monic, ?_, ?_⟩
  · rw [natDegree_mul ha.monic.ne_zero hb.monic.ne_zero, ha.degree, hb.degree]
  · rw [mul_coeff_zero, ha.constant, hb.constant, one_mul]
noncomputable def f2WordPolynomial {m : ℕ} (w : Fin m → Bool) : (ZMod 2)[X] :=
  reducePolynomial 2 (wordPolynomial w)
lemma f2WordPolynomial_endpoints {m : ℕ} (w : Fin m → Bool) :
    HasF2Endpoints (m + 1) (f2WordPolynomial w) :=
  (wordPolynomial_endpoints w).reduce
lemma f2WordPolynomial_injective {m : ℕ} :
    Function.Injective (@f2WordPolynomial m) := by
  intro v w h
  apply wordPolynomial_injective
  exact (wordPolynomial_endpoints v).binary.eq_of_reduce_eq
    (wordPolynomial_endpoints w).binary h
lemma exists_f2WordPolynomial_eq {m : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (m + 1) p) :
    ∃ w : Fin m → Bool, f2WordPolynomial w = p := by
  obtain ⟨w, hw⟩ := exists_wordPolynomial_eq hp.lift
  refine ⟨w, ?_⟩
  unfold f2WordPolynomial
  rw [hw, reduce_zeroOneLift]
noncomputable def f2Family (m : ℕ) : Finset (ZMod 2)[X] :=
  Finset.univ.image (@f2WordPolynomial m)
lemma mem_f2Family_iff {m : ℕ} {p : (ZMod 2)[X]} :
    p ∈ f2Family m ↔ HasF2Endpoints (m + 1) p := by
  classical
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact f2WordPolynomial_endpoints w
  · intro hp
    obtain ⟨w, rfl⟩ := exists_f2WordPolynomial_eq hp
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
lemma card_f2Family (m : ℕ) : (f2Family m).card = 2 ^ m := by
  classical
  rw [f2Family, Finset.card_image_of_injective _ f2WordPolynomial_injective]
  simp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def bitToF2 (b : Bool) : ZMod 2 := if b then 1 else 0
def f2ToBit (c : ZMod 2) : Bool := decide (c = 1)
lemma bitToF2_eq_int_cast (b : Bool) : bitToF2 b = (bitValue b : ZMod 2) := by
  cases b <;> rfl
lemma f2ToBit_bitToF2 (b : Bool) : f2ToBit (bitToF2 b) = b := by
  cases b <;> rfl
lemma bitToF2_f2ToBit (c : ZMod 2) : bitToF2 (f2ToBit c) = c := by
  fin_cases c <;> rfl
def bitF2Equiv : Bool ≃ ZMod 2 where
  toFun := bitToF2
  invFun := f2ToBit
  left_inv := f2ToBit_bitToF2
  right_inv := bitToF2_f2ToBit
lemma bitToF2_xor (b c : Bool) :
    bitToF2 (Bool.xor b c) = bitToF2 b + bitToF2 c := by
  cases b <;> cases c <;> rfl
lemma bitToF2_not (b : Bool) : bitToF2 (!b) = bitToF2 b + 1 := by
  cases b <;> rfl
lemma f2ToBit_add_one (c : ZMod 2) : f2ToBit (c + 1) = !(f2ToBit c) := by
  fin_cases c <;> rfl
lemma f2ToBit_eq_false_iff (c : ZMod 2) : f2ToBit c = false ↔ c = 0 := by
  fin_cases c
  · change (false = false ↔ (0 : ZMod 2) = 0)
    simp
  · change (true = false ↔ (1 : ZMod 2) = 0)
    simp
lemma f2ToBit_eq_true_iff (c : ZMod 2) : f2ToBit c = true ↔ c = 1 := by
  simp [f2ToBit]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasF2Endpoints.coeff_degree {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : p.coeff n = 1 := by
  rw [← hp.degree]
  exact hp.monic
lemma HasF2Endpoints.coeff_eq_zero_above {n k : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hk : n < k) : p.coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [hp.degree]; exact hk)
lemma coeff_f2WordPolynomial_internal {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    (f2WordPolynomial w).coeff (i.val + 1) = bitToF2 (w i) := by
  rw [f2WordPolynomial, coeff_reducePolynomial, coeff_wordPolynomial_internal,
    ← bitToF2_eq_int_cast]
lemma f2WordPolynomial_ext {n : ℕ} {p q : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) (hq : HasF2Endpoints (n + 1) q)
    (h : ∀ i : Fin n, p.coeff (i.val + 1) = q.coeff (i.val + 1)) : p = q := by
  ext k
  by_cases hk0 : k = 0
  · rw [hk0, hp.constant, hq.constant]
  by_cases hkt : k = n + 1
  · subst k
    rw [← hp.degree]
    change p.leadingCoeff = q.coeff p.natDegree
    rw [hp.monic.leadingCoeff, hp.degree, ← hq.degree]
    exact hq.monic.symm
  by_cases hk : k < n + 1
  · let i : Fin n := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    simpa only [hi] using h i
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hp.degree]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [hq.degree]; omega)]
lemma reverse_f2WordPolynomial {n : ℕ} (w : Fin n → Bool) :
    (f2WordPolynomial w).reverse = f2WordPolynomial (fun i ↦ w i.rev) := by
  apply f2WordPolynomial_ext (f2WordPolynomial_endpoints w).reverse
    (f2WordPolynomial_endpoints _)
  intro i
  rw [coeff_reverse, (f2WordPolynomial_endpoints w).degree,
    revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega)]
  have hi : n + 1 - (i.val + 1) = i.rev.val + 1 := by
    rw [Fin.val_rev]
    have := i.isLt
    omega
  rw [hi, coeff_f2WordPolynomial_internal, coeff_f2WordPolynomial_internal]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma f2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl
lemma f2_monic_of_ne_zero {p : (ZMod 2)[X]} (hp : p ≠ 0) : p.Monic :=
  f2_eq_one_of_ne_zero (leadingCoeff_ne_zero.mpr hp)
lemma f2_endpoints_of_constant {p : (ZMod 2)[X]} (hp : p.coeff 0 = 1) :
    HasF2Endpoints p.natDegree p := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hp
    exact zero_ne_one hp
  exact ⟨f2_monic_of_ne_zero hp0, rfl, hp⟩
lemma HasF2Endpoints.factor_endpoints {n : ℕ} {p a b : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hab : p = a * b) :
    HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      a.natDegree + b.natDegree = n := by
  have hc : a.coeff 0 * b.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hab, hp.constant]
  have hac : a.coeff 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact zero_ne_one hc
  have hbc : b.coeff 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact zero_ne_one hc
  have ha := f2_endpoints_of_constant (f2_eq_one_of_ne_zero hac)
  have hb := f2_endpoints_of_constant (f2_eq_one_of_ne_zero hbc)
  refine ⟨ha, hb, ?_⟩
  rw [← natDegree_mul ha.monic.ne_zero hb.monic.ne_zero, ← hab, hp.degree]
lemma HasF2Endpoints.reverse_reverse {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : p.reverse.reverse = p :=
  reverse_reverse_of_constant_ne_zero (by rw [hp.constant]; exact one_ne_zero)
lemma HasF2Endpoints.eq_one_of_degree_zero {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints 0 p) : p = 1 := by
  ext k
  by_cases hk : k = 0
  · rw [hk, hp.constant, coeff_one_zero]
  · rw [hp.coeff_eq_zero_above (by omega), coeff_one, if_neg hk]
lemma HasF2Endpoints.degree_pos_of_nonreciprocal {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hne : p ≠ p.reverse) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  rw [hn] at hp
  have heq := hp.eq_one_of_degree_zero
  apply hne
  rw [heq]
  simpa only [C_1] using (Polynomial.reverse_C (1 : ZMod 2)).symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_coprime_endpoint_factors {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G) :
    ∃ a b t : (ZMod 2)[X],
      F = a * b ∧ G = a * t ∧
      HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      HasF2Endpoints t.natDegree t ∧ IsCoprime b t ∧
      a.natDegree + b.natDegree = n ∧ a.natDegree + t.natDegree = n := by
  let a := GCDMonoid.gcd F G
  let b := F / a
  let t := G / a
  have ha : a ≠ 0 := gcd_ne_zero_of_left hF.monic.ne_zero
  have hFb : F = a * b := (EuclideanDomain.mul_div_cancel' ha (gcd_dvd_left F G)).symm
  have hGt : G = a * t := (EuclideanDomain.mul_div_cancel' ha (gcd_dvd_right F G)).symm
  obtain ⟨hA, hB, hdegF⟩ := hF.factor_endpoints hFb
  obtain ⟨_, hT, hdegG⟩ := hG.factor_endpoints hGt
  exact ⟨a, b, t, hFb, hGt, hA, hB, hT,
    isCoprime_div_gcd_div_gcd hG.monic.ne_zero, hdegF, hdegG⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma f2_reverse_dvd_reverse {a b : (ZMod 2)[X]} (hab : a ∣ b) :
    a.reverse ∣ b.reverse := by
  obtain ⟨q, rfl⟩ := hab
  rw [reverse_mul_of_domain]
  exact dvd_mul_right _ _
lemma HasF2Endpoints.divisor_endpoints {n : ℕ} {p a : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (ha : a ∣ p) : HasF2Endpoints a.natDegree a := by
  obtain ⟨b, hb⟩ := ha
  exact (hp.factor_endpoints hb).1
lemma HasF2Endpoints.gcd_reverse_endpoints {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) :
    HasF2Endpoints (GCDMonoid.gcd p p.reverse).natDegree (GCDMonoid.gcd p p.reverse) :=
  hp.divisor_endpoints (gcd_dvd_left p p.reverse)
lemma HasF2Endpoints.gcd_reverse_degree_le {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : (GCDMonoid.gcd p p.reverse).natDegree ≤ n := by
  simpa only [hp.degree] using
    natDegree_le_of_dvd (gcd_dvd_left p p.reverse) hp.monic.ne_zero
lemma HasF2Endpoints.gcd_reverse_reciprocal {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) :
    (GCDMonoid.gcd p p.reverse).reverse = GCDMonoid.gcd p p.reverse := by
  let g := GCDMonoid.gcd p p.reverse
  have hg : HasF2Endpoints g.natDegree g := hp.gcd_reverse_endpoints
  have hgp : g.reverse ∣ p := by
    have h := f2_reverse_dvd_reverse (gcd_dvd_right p p.reverse)
    simpa only [hp.reverse_reverse] using h
  have hgr : g.reverse ∣ p.reverse :=
    f2_reverse_dvd_reverse (gcd_dvd_left p p.reverse)
  have hdvd : g.reverse ∣ g := dvd_gcd hgp hgr
  exact (eq_of_monic_of_dvd_of_natDegree_le hg.reverse.monic hg.monic hdvd
    (by rw [hg.reverse.degree])).symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasBinaryEndpoints.monic_divisor_constant {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) : J.coeff 0 = 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have hqmonic : q.Monic := hJ.of_mul_monic_left (by rw [← hq]; exact hp.monic)
  exact (hp.factor_constants hJ hqmonic hq).1
lemma HasBinaryEndpoints.monic_divisor_reduce_endpoints {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) :
    HasF2Endpoints J.natDegree (reducePolynomial 2 J) := by
  refine ⟨hJ.map _, monic_reduce_natDegree 2 hJ, ?_⟩
  rw [coeff_reducePolynomial, hp.monic_divisor_constant hJ hdvd, Int.cast_one]
lemma monic_reciprocal_reduce_dvd_gcd {p J : ℤ[X]}
    (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    reducePolynomial 2 J ∣
      GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse := by
  have hl := reducePolynomial_dvd 2 hdvd
  have hr := f2_reverse_dvd_reverse hl
  rw [← monic_reduce_reverse 2 hJ, hrec] at hr
  exact dvd_gcd hl hr
lemma HasBinaryEndpoints.reciprocal_divisor_degree_le_gcd {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    J.natDegree ≤
      (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree := by
  have h := natDegree_le_of_dvd (monic_reciprocal_reduce_dvd_gcd hJ hdvd hrec)
    hp.reduce.gcd_reverse_endpoints.monic.ne_zero
  simpa only [monic_reduce_natDegree 2 hJ] using h
theorem monic_reciprocal_divisor_reduction {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    HasF2Endpoints J.natDegree (reducePolynomial 2 J) ∧
      (reducePolynomial 2 J).natDegree = J.natDegree ∧
      (reducePolynomial 2 J).reverse = reducePolynomial 2 J ∧
      reducePolynomial 2 J ∣
        GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse := by
  refine ⟨hp.monic_divisor_reduce_endpoints hJ hdvd, monic_reduce_natDegree 2 hJ,
    ?_, monic_reciprocal_reduce_dvd_gcd hJ hdvd hrec⟩
  rw [← monic_reduce_reverse 2 hJ, hrec]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def lowerWordIndex {n : ℕ} (i : Fin (n / 2)) : Fin n :=
  ⟨i.val, by have := i.isLt; omega⟩
def upperWordIndex {n : ℕ} (i : Fin (n / 2)) : Fin n :=
  (lowerWordIndex i).rev
def centerWordIndex {n : ℕ} (i : Fin (n % 2)) : Fin n :=
  ⟨n / 2 + i.val, by have := i.isLt; omega⟩
lemma lowerWordIndex_val {n : ℕ} (i : Fin (n / 2)) :
    (lowerWordIndex i).val = i.val := rfl
lemma upperWordIndex_val {n : ℕ} (i : Fin (n / 2)) :
    (upperWordIndex i).val = n - (i.val + 1) := by
  simp [upperWordIndex, lowerWordIndex, Fin.val_rev]
lemma lowerWordIndex_lt_half {n : ℕ} (i : Fin (n / 2)) :
    (lowerWordIndex i).val < n / 2 := i.isLt
lemma half_le_upperWordIndex {n : ℕ} (i : Fin (n / 2)) :
    n / 2 ≤ (upperWordIndex i).val := by
  rw [upperWordIndex_val]
  have := i.isLt
  omega
lemma upperWordIndex_rev {n : ℕ} (i : Fin (n / 2)) :
    (upperWordIndex i).rev = lowerWordIndex i := by
  simp [upperWordIndex]
lemma centerWordIndex_val {n : ℕ} (i : Fin (n % 2)) :
    (centerWordIndex i).val = n / 2 := by
  have := i.isLt
  have : i.val = 0 := by omega
  simp [centerWordIndex, this]
lemma centerWordIndex_rev {n : ℕ} (i : Fin (n % 2)) :
    (centerWordIndex i).rev = centerWordIndex i := by
  apply Fin.ext
  rw [Fin.val_rev, centerWordIndex_val]
  have := i.isLt
  omega
lemma center_index_of_not_outer {n : ℕ} (i : Fin n)
    (hl : ¬ i.val < n / 2) (hu : ¬ i.rev.val < n / 2) :
    i.val - n / 2 < n % 2 := by
  have := i.isLt
  rw [Fin.val_rev] at hu
  omega
end OdlyzkoPoonen

namespace OdlyzkoPoonen
noncomputable def uniformProbability {α : Type*} [Fintype α] (E : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card α
lemma uniformProbability_false {α : Type*} [Fintype α] :
    uniformProbability (fun _ : α ↦ False) = 0 := by
  classical
  simp [uniformProbability]
lemma uniformProbability_true {α : Type*} [Fintype α] [Nonempty α] :
    uniformProbability (fun _ : α ↦ True) = 1 := by
  classical
  simp [uniformProbability, Fintype.card_ne_zero]
lemma uniformProbability_nonneg {α : Type*} [Fintype α] (E : α → Prop) :
    0 ≤ uniformProbability E := by
  unfold uniformProbability
  positivity
lemma uniformProbability_mono {α : Type*} [Fintype α] {E F : α → Prop}
    (h : ∀ a, E a → F a) : uniformProbability E ≤ uniformProbability F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h a (Finset.mem_filter.mp ha).2⟩
lemma uniformProbability_le_one {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    uniformProbability E ≤ 1 := by
  calc
    uniformProbability E ≤ uniformProbability (fun _ : α ↦ True) :=
      uniformProbability_mono (fun _ _ ↦ trivial)
    _ = 1 := uniformProbability_true
lemma uniformProbability_product {α β : Type*} [Fintype α] [Fintype β]
    (E : α → Prop) (F : β → Prop) :
    uniformProbability (fun p : α × β ↦ E p.1 ∧ F p.2) =
      uniformProbability E * uniformProbability F := by
  classical
  letI : DecidablePred (fun p : α × β ↦ E p.1 ∧ F p.2) :=
    fun _ ↦ Classical.propDecidable _
  have h : Finset.univ.filter (fun p : α × β ↦ E p.1 ∧ F p.2) =
      (Finset.univ.filter E) ×ˢ (Finset.univ.filter F) := by
    ext p
    simp
  unfold uniformProbability
  rw [h, Finset.card_product, Fintype.card_prod]
  push_cast
  ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma uniformProbability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) :
    uniformProbability (fun a ↦ E (e a)) = uniformProbability E := by
  classical
  have h : Fintype.card {a : α // E (e a)} = Fintype.card {b : β // E b} :=
    Fintype.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))
  unfold uniformProbability
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, h, Fintype.card_congr e]
lemma uniformProbability_bijective {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β} (hf : Function.Bijective f) (E : β → Prop) :
    uniformProbability (fun a ↦ E (f a)) = uniformProbability E :=
  uniformProbability_equiv (Equiv.ofBijective f hf) E
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators Classical
noncomputable def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α
lemma uniformAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformAverage f ≤ uniformAverage g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ ↦ h a)
lemma uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    uniformAverage (fun a ↦ f (e a)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]
lemma uniformAverage_bijective {α β : Type*} [Fintype α] [Fintype β]
    {e : α → β} (he : Function.Bijective e) (f : β → ℝ) :
    uniformAverage (fun a ↦ f (e a)) = uniformAverage f :=
  uniformAverage_equiv (Equiv.ofBijective e he) f
lemma uniformAverage_product {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformAverage (fun p : α × β ↦ f p.1 p.2) =
      uniformAverage (fun a ↦ uniformAverage (f a)) := by
  unfold uniformAverage
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card α : ℝ)]
lemma uniformProbability_eq_average_indicator {α : Type*} [Fintype α]
    (E : α → Prop) :
    uniformProbability E = uniformAverage (fun a ↦ if E a then 1 else 0) := by
  classical
  simp [uniformProbability, uniformAverage]
lemma uniformProbability_product_eq_average {α β : Type*} [Fintype α] [Fintype β]
    (E : α → β → Prop) :
    uniformProbability (fun p : α × β ↦ E p.1 p.2) =
      uniformAverage (fun a ↦ uniformProbability (E a)) := by
  rw [uniformProbability_eq_average_indicator,
    uniformAverage_product (fun a b ↦ if E a b then 1 else 0)]
  congr 1
  funext a
  exact (uniformProbability_eq_average_indicator (E a)).symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def assembleOppositeWord {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin n) : Bool :=
  if hl : i.val < n / 2 then u ⟨i.val, hl⟩
  else if hu : i.rev.val < n / 2 then
    Bool.xor (u ⟨i.rev.val, hu⟩) (c ⟨i.rev.val, hu⟩)
  else z ⟨i.val - n / 2, center_index_of_not_outer i hl hu⟩
lemma assembleOppositeWord_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    assembleOppositeWord u c z (lowerWordIndex i) = u i := by
  unfold assembleOppositeWord
  split
  · rfl
  · rename_i h
    exact (h (lowerWordIndex_lt_half i)).elim
lemma assembleOppositeWord_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    assembleOppositeWord u c z (upperWordIndex i) = Bool.xor (u i) (c i) := by
  simp only [assembleOppositeWord, dif_neg (not_lt.mpr (half_le_upperWordIndex i)),
    upperWordIndex_rev, lowerWordIndex_val, dif_pos i.isLt]
lemma assembleOppositeWord_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    assembleOppositeWord u c z (centerWordIndex i) = z i := by
  simp only [assembleOppositeWord, centerWordIndex_rev, centerWordIndex_val,
    lt_self_iff_false, dite_false]
  congr 1
  apply Fin.ext
  have := i.isLt
  omega
lemma assembleOppositeWord_recover {n : ℕ} (w : Fin n → Bool) :
    assembleOppositeWord (fun i ↦ w (lowerWordIndex i))
      (fun i ↦ Bool.xor (w (lowerWordIndex i)) (w (upperWordIndex i)))
      (fun i ↦ w (centerWordIndex i)) = w := by
  funext i
  unfold assembleOppositeWord
  split_ifs with hl hu
  · rfl
  · dsimp only
    have h : upperWordIndex ⟨i.rev.val, hu⟩ = i := by
      change i.rev.rev = i
      exact Fin.rev_rev i
    rw [h]
    cases w (lowerWordIndex ⟨i.rev.val, hu⟩) <;> cases w i <;> rfl
  · dsimp only
    congr 1
    apply Fin.ext
    change n / 2 + (i.val - n / 2) = i.val
    omega
def oppositeWordEquiv (n : ℕ) : (Fin n → Bool) ≃
    (Fin (n / 2) → Bool) × ((Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) where
  toFun w := ⟨fun i ↦ Bool.xor (w (lowerWordIndex i)) (w (upperWordIndex i)),
    fun i ↦ w (centerWordIndex i), fun i ↦ w (lowerWordIndex i)⟩
  invFun p := assembleOppositeWord p.2.2 p.1 p.2.1
  left_inv := assembleOppositeWord_recover
  right_inv := by
    rintro ⟨c, z, u⟩
    apply Prod.ext
    · funext i
      change Bool.xor (assembleOppositeWord u c z (lowerWordIndex i))
        (assembleOppositeWord u c z (upperWordIndex i)) = c i
      rw [assembleOppositeWord_lower, assembleOppositeWord_upper]
      cases u i <;> cases c i <;> rfl
    · apply Prod.ext
      · funext i
        exact assembleOppositeWord_center u c z i
      · funext i
        exact assembleOppositeWord_lower u c z i
lemma uniformProbability_oppositeWord (n : ℕ) (E : (Fin n → Bool) → Prop) :
    uniformProbability E =
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        uniformAverage (fun z : Fin (n % 2) → Bool ↦
          uniformProbability (fun u : Fin (n / 2) → Bool ↦ E (assembleOppositeWord u c z)))) := by
  rw [← uniformProbability_equiv (oppositeWordEquiv n).symm E]
  change uniformProbability (fun p : (Fin (n / 2) → Bool) ×
      ((Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) ↦
      E (assembleOppositeWord p.2.2 p.1 p.2.1)) = _
  rw [uniformProbability_product_eq_average
    (fun (c : Fin (n / 2) → Bool)
      (p : (Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) ↦
      E (assembleOppositeWord p.2 c p.1))]
  congr 1
  funext c
  exact uniformProbability_product_eq_average (fun (z : Fin (n % 2) → Bool) (u : Fin (n / 2) → Bool) ↦
    E (assembleOppositeWord u c z))
end OdlyzkoPoonen

open scoped Classical
namespace OdlyzkoPoonen
noncomputable def binaryProbability (m : ℕ) (E : Polynomial ℤ → Prop) : ℝ :=
  uniformProbability (fun w : Fin m → Bool ↦ E (wordPolynomial w))
lemma binaryProbability_eq_count (m : ℕ) (E : Polynomial ℤ → Prop) :
    binaryProbability m E = ((binaryFamily m).filter E).card / (2 : ℝ) ^ m := by
  classical
  have h : (Finset.univ.filter (fun w : Fin m → Bool ↦ E (wordPolynomial w))).image
      wordPolynomial = (binaryFamily m).filter E := by
    ext p
    simp only [binaryFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  rw [binaryProbability, uniformProbability, ← h,
    Finset.card_image_of_injective _ wordPolynomial_injective]
  simp
lemma binaryProbability_endpoints (m : ℕ) :
    binaryProbability m (HasBinaryEndpoints (m + 1)) = 1 := by
  unfold binaryProbability
  have h : (fun w : Fin m → Bool ↦ HasBinaryEndpoints (m + 1) (wordPolynomial w)) =
      (fun _ ↦ True) := by
    funext w
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ wordPolynomial_endpoints w⟩
  rw [h, uniformProbability_true]
end OdlyzkoPoonen

open scoped Classical
namespace OdlyzkoPoonen
noncomputable def f2Probability (m : ℕ) (E : Polynomial (ZMod 2) → Prop) : ℝ :=
  uniformProbability (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))
lemma f2Probability_eq_count (m : ℕ) (E : Polynomial (ZMod 2) → Prop) :
    f2Probability m E = ((f2Family m).filter E).card / (2 : ℝ) ^ m := by
  classical
  have h : (Finset.univ.filter (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))).image
      f2WordPolynomial = (f2Family m).filter E := by
    ext p
    simp only [f2Family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  rw [f2Probability, uniformProbability, ← h,
    Finset.card_image_of_injective _ f2WordPolynomial_injective]
  simp
lemma f2Probability_eq_binaryProbability (m : ℕ) (E : Polynomial (ZMod 2) → Prop) :
    f2Probability m E = binaryProbability m (fun p ↦ E (reducePolynomial 2 p)) := rfl
lemma f2Probability_endpoints (m : ℕ) :
    f2Probability m (HasF2Endpoints (m + 1)) = 1 := by
  unfold f2Probability
  have h : (fun w : Fin m → Bool ↦ HasF2Endpoints (m + 1) (f2WordPolynomial w)) =
      (fun _ ↦ True) := by
    funext w
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ f2WordPolynomial_endpoints w⟩
  rw [h, uniformProbability_true]
noncomputable def f2PairProbability (m l : ℕ)
    (E : Polynomial (ZMod 2) → Polynomial (ZMod 2) → Prop) : ℝ :=
  uniformProbability (fun w : (Fin m → Bool) × (Fin l → Bool) ↦
    E (f2WordPolynomial w.1) (f2WordPolynomial w.2))
lemma f2PairProbability_product (m l : ℕ)
    (E F : Polynomial (ZMod 2) → Prop) :
    f2PairProbability m l (fun a b ↦ E a ∧ F b) =
      f2Probability m E * f2Probability l F := by
  unfold f2PairProbability f2Probability
  exact uniformProbability_product
    (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))
    (fun w : Fin l → Bool ↦ F (f2WordPolynomial w))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
noncomputable def pairedPolynomial {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) : (ZMod 2)[X] :=
  f2WordPolynomial (assembleOppositeWord u c z)
lemma pairedPolynomial_endpoints {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) : HasF2Endpoints (n + 1) (pairedPolynomial u c z) :=
  f2WordPolynomial_endpoints _
lemma coeff_pairedPolynomial_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z).coeff (i.val + 1) = bitToF2 (u i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (lowerWordIndex i)
  simpa only [pairedPolynomial, lowerWordIndex_val, assembleOppositeWord_lower] using h
lemma coeff_pairedPolynomial_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z).coeff (n + 1 - (i.val + 1)) = bitToF2 (u i) + bitToF2 (c i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (upperWordIndex i)
  have hi : (upperWordIndex i).val + 1 = n + 1 - (i.val + 1) := by
    rw [upperWordIndex_val]
    have := i.isLt
    omega
  simpa only [pairedPolynomial, hi, assembleOppositeWord_upper, bitToF2_xor] using h
lemma coeff_pairedPolynomial_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    (pairedPolynomial u c z).coeff (n / 2 + 1) = bitToF2 (z i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (centerWordIndex i)
  simpa only [pairedPolynomial, centerWordIndex_val, assembleOppositeWord_center] using h
lemma coeff_paired_sum_reverse_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (i.val + 1) =
      bitToF2 (c i) := by
  rw [coeff_add, coeff_reverse, (pairedPolynomial_endpoints u c z).degree,
    revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega),
    coeff_pairedPolynomial_lower, coeff_pairedPolynomial_upper]
  exact CharTwo.add_cancel_left _ _
lemma coeff_add_reverse_opposite {n k : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hk : k ≤ n) :
    (p + p.reverse).coeff (n - k) = (p + p.reverse).coeff k := by
  simp only [coeff_add, coeff_reverse, hp.degree, revAt_le hk,
    revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk, add_comm]
lemma coeff_paired_sum_reverse_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (n + 1 - (i.val + 1)) =
      bitToF2 (c i) := by
  rw [coeff_add_reverse_opposite (pairedPolynomial_endpoints u c z)
    (show i.val + 1 ≤ n + 1 by have := i.isLt; omega), coeff_paired_sum_reverse_lower]
lemma coeff_paired_sum_reverse_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (n / 2 + 1) = 0 := by
  have hn : n + 1 - (n / 2 + 1) = n / 2 + 1 := by have := i.isLt; omega
  rw [coeff_add, coeff_reverse, (pairedPolynomial_endpoints u c z).degree,
    revAt_le (show n / 2 + 1 ≤ n + 1 by omega), hn]
  exact CharTwo.add_self_eq_zero _
lemma f2Probability_eq_paired_average (n : ℕ) (E : (ZMod 2)[X] → Prop) :
    f2Probability n E =
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        uniformAverage (fun z : Fin (n % 2) → Bool ↦
          uniformProbability (fun u : Fin (n / 2) → Bool ↦ E (pairedPolynomial u c z)))) :=
  uniformProbability_oppositeWord n (fun w ↦ E (f2WordPolynomial w))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasF2Endpoints.reverse_eq_iff_lower {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) :
    p.reverse = p ↔ ∀ i : Fin (n / 2), p.coeff (i.val + 1) = p.coeff (n + 1 - (i.val + 1)) := by
  constructor
  · intro h i
    have heq := congrArg (fun q : (ZMod 2)[X] ↦ q.coeff (i.val + 1)) h
    rw [coeff_reverse, hp.degree,
      revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega)] at heq
    exact heq.symm
  · intro h
    apply f2WordPolynomial_ext hp.reverse hp
    intro j
    have hj := j.isLt
    rw [coeff_reverse, hp.degree, revAt_le (show j.val + 1 ≤ n + 1 by omega)]
    by_cases hl : j.val < n / 2
    · exact (h ⟨j.val, hl⟩).symm
    · by_cases hu : n - (j.val + 1) < n / 2
      · let i : Fin (n / 2) := ⟨n - (j.val + 1), hu⟩
        have hi : i.val + 1 = n + 1 - (j.val + 1) := by dsimp [i]; omega
        have hi' : n + 1 - (i.val + 1) = j.val + 1 := by dsimp [i]; omega
        have hh := h i
        rw [hi', hi] at hh
        exact hh
      · have hc : n + 1 - (j.val + 1) = j.val + 1 := by omega
        rw [hc]
lemma pairedPolynomial_reverse_eq_iff {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) :
    (pairedPolynomial u c z).reverse = pairedPolynomial u c z ↔ ∀ i, c i = false := by
  rw [(pairedPolynomial_endpoints u c z).reverse_eq_iff_lower]
  simp only [coeff_pairedPolynomial_lower, coeff_pairedPolynomial_upper]
  apply forall_congr'
  intro i
  cases c i <;> simp [bitToF2]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
noncomputable def prescribedBitsEquiv {ι : Type*} (s : Finset ι) (v : ι → Bool) :
    {w : ι → Bool // ∀ i ∈ s, w i = v i} ≃ ({i : ι // i ∉ s} → Bool) := by
  classical
  refine {
    toFun := fun w i ↦ w.val i.val
    invFun := fun w ↦ ⟨fun i ↦ if hi : i ∈ s then v i else w ⟨i, hi⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro i hi
    exact dif_pos hi
  · intro w
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simpa only [dif_pos hi] using (w.property i hi).symm
    · simp only [dif_neg hi]
  · intro w
    funext i
    simp only [dif_neg i.property]
lemma card_prescribedBits {n : ℕ} (s : Finset (Fin n)) (v : Fin n → Bool) :
    Fintype.card {w : Fin n → Bool // ∀ i ∈ s, w i = v i} = 2 ^ (n - s.card) := by
  classical
  rw [Fintype.card_congr (prescribedBitsEquiv s v)]
  simp [Fintype.card_subtype_compl]
lemma uniformProbability_prescribedBits {n : ℕ} (s : Finset (Fin n))
    (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, w i = v i) =
      (1 / 2 : ℝ) ^ s.card := by
  classical
  have hs : s.card ≤ n := by simpa using Finset.card_le_univ s
  unfold uniformProbability
  rw [← Fintype.card_subtype, card_prescribedBits]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - s.card) * 2 ^ s.card := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  rw [hpow, one_div_pow]
  field_simp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (t : ℝ) :
    uniformAverage (fun _ : α ↦ t) = t := by
  unfold uniformAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ t (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
lemma uniformAverage_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {t : ℝ} (h : ∀ a, f a ≤ t) : uniformAverage f ≤ t := by
  calc
    _ ≤ uniformAverage (fun _ : α ↦ t) := uniformAverage_mono h
    _ = t := uniformAverage_const t
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
lemma f2Probability_reciprocal (n : ℕ) :
    f2Probability n (fun p ↦ p.reverse = p) = (1 / 2 : ℝ) ^ (n / 2) := by
  classical
  rw [f2Probability_eq_paired_average]
  simp_rw [pairedPolynomial_reverse_eq_iff, uniformProbability_eq_average_indicator,
    uniformAverage_const]
  rw [← uniformProbability_eq_average_indicator]
  simpa only [Finset.mem_univ, forall_true_left, Finset.card_univ,
    Fintype.card_fin] using
    (uniformProbability_prescribedBits (Finset.univ : Finset (Fin (n / 2)))
      (fun _ ↦ false))
lemma card_reciprocal_f2Family (n : ℕ) :
    ((f2Family n).filter (fun p ↦ p.reverse = p)).card = 2 ^ ((n + 1) / 2) := by
  classical
  letI : DecidablePred (fun p : (ZMod 2)[X] ↦ p.reverse = p) :=
    fun _ ↦ Classical.propDecidable _
  have h := f2Probability_reciprocal n
  rw [f2Probability_eq_count, one_div_pow] at h
  have hpow : (2 : ℝ) ^ n = 2 ^ ((n + 1) / 2) * 2 ^ (n / 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : (((f2Family n).filter (fun p ↦ p.reverse = p)).card : ℝ) =
      (2 : ℝ) ^ ((n + 1) / 2) := by
    have heq := (div_eq_iff (show (2 : ℝ) ^ n ≠ 0 by positivity)).mp h
    rw [hpow] at heq
    field_simp at heq
    exact heq
  norm_cast at hc
  convert hc using 1
  congr 1
  ext p
  simp only [Finset.mem_filter]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
noncomputable def f2EndpointFamily (h : ℕ) : Finset (ZMod 2)[X] :=
  if h = 0 then {1} else f2Family (h - 1)
lemma mem_f2EndpointFamily_iff {h : ℕ} {p : (ZMod 2)[X]} :
    p ∈ f2EndpointFamily h ↔ HasF2Endpoints h p := by
  cases h with
  | zero =>
    simp only [f2EndpointFamily, ite_true, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨monic_one, natDegree_one, coeff_one_zero⟩
    · exact HasF2Endpoints.eq_one_of_degree_zero
  | succ n =>
    simp only [f2EndpointFamily, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    exact mem_f2Family_iff
lemma card_f2EndpointFamily (h : ℕ) :
    (f2EndpointFamily h).card = if h = 0 then 1 else 2 ^ (h - 1) := by
  by_cases hh : h = 0
  · simp [f2EndpointFamily, hh]
  · simp only [f2EndpointFamily, if_neg hh, card_f2Family]
lemma f2EndpointFamily_nonempty (h : ℕ) : (f2EndpointFamily h).Nonempty := by
  rw [← Finset.card_pos, card_f2EndpointFamily]
  split_ifs <;> positivity
lemma card_f2EndpointFamily_le (h : ℕ) : (f2EndpointFamily h).card ≤ 2 ^ h := by
  rw [card_f2EndpointFamily]
  split_ifs with hh
  · simp [hh]
  · exact Nat.pow_le_pow_right (by omega) (Nat.sub_le h 1)
lemma card_reciprocal_f2EndpointFamily (h : ℕ) :
    ((f2EndpointFamily h).filter (fun p ↦ p.reverse = p)).card = 2 ^ (h / 2) := by
  cases h with
  | zero =>
    have hr : (1 : (ZMod 2)[X]).reverse = 1 := by
      simpa only [C_1] using Polynomial.reverse_C (1 : ZMod 2)
    have hf : ((f2EndpointFamily 0).filter (fun p ↦ p.reverse = p)) = {1} := by
      ext p
      simp only [Finset.mem_filter, f2EndpointFamily, ite_true, Finset.mem_singleton]
      exact ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, by simpa only [hp] using hr⟩⟩
    rw [hf]
    norm_num
  | succ n =>
    simpa only [f2EndpointFamily, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
      using card_reciprocal_f2Family n
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
lemma HasF2Endpoints.not_dvd_of_degree_lt {n h : ℕ} {p J : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hJ : HasF2Endpoints h J) (hnh : n < h) : ¬ J ∣ p := by
  intro hdvd
  have hle := natDegree_le_of_dvd hdvd hp.monic.ne_zero
  rw [hp.degree, hJ.degree] at hle
  omega
lemma HasF2Endpoints.exists_endpoint_quotient {n h : ℕ} {p J : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hJ : HasF2Endpoints h J) (hdvd : J ∣ p) :
    ∃ q : (ZMod 2)[X], HasF2Endpoints (n - h) q ∧ p = J * q := by
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨_, hQ, hdeg⟩ := hp.factor_endpoints hq
  refine ⟨q, ⟨hQ.monic, ?_, hQ.constant⟩, hq⟩
  rw [hJ.degree] at hdeg
  omega
lemma card_endpoint_multiples_le {n h : ℕ} {J : (ZMod 2)[X]}
    (hJ : HasF2Endpoints h J) :
    ((f2EndpointFamily n).filter (fun p ↦ J ∣ p)).card ≤ 2 ^ (n - h) := by
  have hsub : (f2EndpointFamily n).filter (fun p ↦ J ∣ p) ⊆
      (f2EndpointFamily (n - h)).image (fun q ↦ J * q) := by
    intro p hp
    obtain ⟨hp, hdvd⟩ := Finset.mem_filter.mp hp
    obtain ⟨q, hq, heq⟩ := (mem_f2EndpointFamily_iff.mp hp).exists_endpoint_quotient hJ hdvd
    exact Finset.mem_image.mpr ⟨q, mem_f2EndpointFamily_iff.mpr hq, heq.symm⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (card_f2EndpointFamily_le (n - h)))
lemma f2Probability_divisible_eq_zero {n h : ℕ} {J : (ZMod 2)[X]}
    (hn : 1 ≤ n) (hJ : HasF2Endpoints h J) (hnh : n < h) :
    f2Probability (n - 1) (fun p ↦ J ∣ p) = 0 := by
  have hf : (f2Family (n - 1)).filter (fun p ↦ J ∣ p) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hdvd⟩ := Finset.mem_filter.mp hp
    have hep := mem_f2Family_iff.mp hp
    rw [Nat.sub_add_cancel hn] at hep
    exact hep.not_dvd_of_degree_lt hJ hnh hdvd
  rw [f2Probability_eq_count, hf, Finset.card_empty, Nat.cast_zero, zero_div]
lemma f2Probability_divisible_le {n h : ℕ} {J : (ZMod 2)[X]}
    (hn : 1 ≤ n) (hJ : HasF2Endpoints h J) :
    f2Probability (n - 1) (fun p ↦ J ∣ p) ≤ 2 / (2 : ℝ) ^ h := by
  by_cases hhn : h ≤ n
  · have hc := card_endpoint_multiples_le (n := n) hJ
    have hn0 : n ≠ 0 := by omega
    simp only [f2EndpointFamily, if_neg hn0] at hc
    rw [f2Probability_eq_count]
    calc
      _ ≤ (2 : ℝ) ^ (n - h) / 2 ^ (n - 1) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = 2 / (2 : ℝ) ^ h := by
        apply (div_eq_div_iff (by positivity) (by positivity)).2
        calc
          _ = (2 : ℝ) ^ n := by rw [← pow_add, Nat.sub_add_cancel hhn]
          _ = 2 * (2 : ℝ) ^ (n - 1) := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
  · rw [f2Probability_divisible_eq_zero hn hJ (by omega)]
    positivity
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma uniformAverage_sum {α β : Type*} [Fintype α] [Fintype β] (f : β → α → ℝ) :
    uniformAverage (fun a ↦ ∑ b, f b a) = ∑ b, uniformAverage (f b) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]
lemma uniformAverage_mul_right {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformAverage (fun a ↦ f a * c) = uniformAverage f * c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring
lemma uniformProbability_exists_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (E : β → α → Prop) :
    uniformProbability (fun a ↦ ∃ b, E b a) ≤ ∑ b, uniformProbability (E b) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_sum]
  apply uniformAverage_mono
  intro a
  by_cases h : ∃ b, E b a
  · rw [if_pos h]
    obtain ⟨b, hb⟩ := h
    have hle := Finset.single_le_sum
      (f := fun b ↦ if E b a then (1 : ℝ) else 0)
      (fun _ _ ↦ by positivity) (Finset.mem_univ b)
    simpa only [if_pos hb] using hle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
lemma uniformProbability_product_bound {α β : Type*} [Fintype α] [Fintype β]
    (F : α → Prop) (E : α → β → Prop) (c : ℝ)
    (h : ∀ a, F a → uniformProbability (E a) ≤ c) :
    uniformProbability (fun v : α × β ↦ F v.1 ∧ E v.1 v.2) ≤ uniformProbability F * c := by
  classical
  rw [uniformProbability_product_eq_average (fun (a : α) (b : β) ↦ F a ∧ E a b)]
  calc
    _ ≤ uniformAverage (fun a : α ↦ (if F a then 1 else 0) * c) := by
      apply uniformAverage_mono
      intro a
      by_cases ha : F a
      · have heq : (fun b : β ↦ F a ∧ E a b) = E a := by funext b; simp [ha]
        rw [heq, if_pos ha, one_mul]
        exact h a ha
      · have heq : (fun b : β ↦ F a ∧ E a b) = (fun _ : β ↦ False) := by funext b; simp [ha]
        rw [heq, uniformProbability_false, if_neg ha, zero_mul]
    _ = _ := by
      rw [uniformAverage_mul_right, ← uniformProbability_eq_average_indicator]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma uniformAverage_finset_sum {α β : Type*} [Fintype α]
    (s : Finset β) (f : β → α → ℝ) :
    uniformAverage (fun a ↦ ∑ b ∈ s, f b a) = ∑ b ∈ s, uniformAverage (f b) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]
lemma uniformProbability_exists_mem_le_sum {α β : Type*} [Fintype α]
    (s : Finset β) (E : β → α → Prop) :
    uniformProbability (fun a ↦ ∃ b ∈ s, E b a) ≤ ∑ b ∈ s, uniformProbability (E b) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_finset_sum]
  apply uniformAverage_mono
  intro a
  by_cases h : ∃ b ∈ s, E b a
  · rw [if_pos h]
    obtain ⟨b, hbs, hb⟩ := h
    have hle := Finset.single_le_sum
      (f := fun b ↦ if E b a then (1 : ℝ) else 0)
      (fun _ _ ↦ by positivity) hbs
    simpa only [if_pos hb] using hle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
lemma uniformProbability_exists_mem_le_card_mul {α β : Type*} [Fintype α]
    (s : Finset β) (E : β → α → Prop) (c : ℝ)
    (h : ∀ b ∈ s, uniformProbability (E b) ≤ c) :
    uniformProbability (fun a ↦ ∃ b ∈ s, E b a) ≤ s.card * c := by
  calc
    _ ≤ ∑ b ∈ s, uniformProbability (E b) := uniformProbability_exists_mem_le_sum s E
    _ ≤ ∑ _b ∈ s, c := Finset.sum_le_sum h
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
def HasReciprocalF2Divisor (h : ℕ) (p : (ZMod 2)[X]) : Prop :=
  ∃ J : (ZMod 2)[X], HasF2Endpoints h J ∧ J.reverse = J ∧ J ∣ p
lemma hasReciprocalF2Divisor_iff_mem {h : ℕ} {p : (ZMod 2)[X]} :
    HasReciprocalF2Divisor h p ↔
      ∃ J ∈ (f2EndpointFamily h).filter (fun J ↦ J.reverse = J), J ∣ p := by
  simp only [HasReciprocalF2Divisor, Finset.mem_filter, mem_f2EndpointFamily_iff]
  tauto
lemma f2Probability_reciprocal_divisor_le {n : ℕ} (hn : 1 ≤ n) (h : ℕ) :
    f2Probability (n - 1) (HasReciprocalF2Divisor h) ≤
      (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) := by
  unfold f2Probability
  simp_rw [hasReciprocalF2Divisor_iff_mem]
  have hbound := uniformProbability_exists_mem_le_card_mul
    ((f2EndpointFamily h).filter (fun J ↦ J.reverse = J))
    (fun (J : (ZMod 2)[X]) (w : Fin (n - 1) → Bool) ↦ J ∣ f2WordPolynomial w)
    (2 / (2 : ℝ) ^ h) (by
      intro J hJ
      exact f2Probability_divisible_le hn
        (mem_f2EndpointFamily_iff.mp (Finset.mem_filter.mp hJ).1))
  rw [card_reciprocal_f2EndpointFamily] at hbound
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound
lemma HasF2Endpoints.exists_reciprocal_divisor_of_gcd_degree {n L : ℕ}
    {p : (ZMod 2)[X]} (hp : HasF2Endpoints n p)
    (hL : L ≤ (GCDMonoid.gcd p p.reverse).natDegree) :
    ∃ h ∈ Finset.Icc L n, HasReciprocalF2Divisor h p := by
  refine ⟨(GCDMonoid.gcd p p.reverse).natDegree,
    Finset.mem_Icc.mpr ⟨hL, hp.gcd_reverse_degree_le⟩, ?_⟩
  exact ⟨GCDMonoid.gcd p p.reverse, hp.gcd_reverse_endpoints,
    hp.gcd_reverse_reciprocal, gcd_dvd_left p p.reverse⟩
lemma f2Probability_gcd_degree_le_sum {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    f2Probability (n - 1)
      (fun p ↦ L ≤ (GCDMonoid.gcd p p.reverse).natDegree) ≤
      ∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) := by
  unfold f2Probability
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ h ∈ Finset.Icc L n, HasReciprocalF2Divisor h (f2WordPolynomial w)) := by
      apply uniformProbability_mono
      intro w hw
      have hp := f2WordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      exact hp.exists_reciprocal_divisor_of_gcd_degree hw
    _ ≤ ∑ h ∈ Finset.Icc L n,
        uniformProbability (fun w : Fin (n - 1) → Bool ↦
          HasReciprocalF2Divisor h (f2WordPolynomial w)) :=
      uniformProbability_exists_mem_le_sum (Finset.Icc L n)
        (fun (h : ℕ) (w : Fin (n - 1) → Bool) ↦
          HasReciprocalF2Divisor h (f2WordPolynomial w))
    _ ≤ _ := Finset.sum_le_sum (fun h _ ↦ f2Probability_reciprocal_divisor_le hn h)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
noncomputable def reciprocalGeometricTail (L : ℕ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ (L / 2) + 4 * (1 / 2 : ℝ) ^ ((L + 1) / 2)
lemma reciprocal_counting_summand (h : ℕ) :
    (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) =
      2 * (1 / 2 : ℝ) ^ ((h + 1) / 2) := by
  have hp : (2 : ℝ) ^ h = 2 ^ (h / 2) * 2 ^ ((h + 1) / 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp, one_div_pow]
  field_simp
lemma reciprocalGeometricTail_nonneg (L : ℕ) : 0 ≤ reciprocalGeometricTail L := by
  unfold reciprocalGeometricTail
  positivity
lemma reciprocalGeometricTail_succ (L : ℕ) :
    reciprocalGeometricTail L =
      2 * (1 / 2 : ℝ) ^ ((L + 1) / 2) + reciprocalGeometricTail (L + 1) := by
  unfold reciprocalGeometricTail
  rw [show (L + 1 + 1) / 2 = L / 2 + 1 by omega, pow_succ]
  ring
lemma sum_reciprocal_tail_range (L k : ℕ) :
    (∑ i ∈ Finset.range k, 2 * (1 / 2 : ℝ) ^ ((L + i + 1) / 2)) +
      reciprocalGeometricTail (L + k) = reciprocalGeometricTail L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht := reciprocalGeometricTail_succ (L + k)
    rw [show L + (k + 1) = L + k + 1 by omega]
    linarith
lemma sum_reciprocal_counting_le_tail (L n : ℕ) :
    (∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h)) ≤
      reciprocalGeometricTail L := by
  simp_rw [reciprocal_counting_summand]
  have hs : Finset.Icc L n = Finset.Ico L (n + 1) := by ext h; simp
  rw [hs, Finset.sum_Ico_eq_sum_range]
  have heq := sum_reciprocal_tail_range L (n + 1 - L)
  have hnonneg := reciprocalGeometricTail_nonneg (L + (n + 1 - L))
  linarith
lemma two_rpow_neg_half_even (r : ℕ) :
    (2 : ℝ) ^ (-((2 * r : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) ^ r := by
  have he : -((2 * r : ℕ) : ℝ) / 2 = -(r : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]
lemma two_rpow_neg_half_odd (r : ℕ) :
    (2 : ℝ) ^ (-((2 * r + 1 : ℕ) : ℝ) / 2) =
      (1 / 2 : ℝ) ^ r / Real.sqrt 2 := by
  have he : -((2 * r + 1 : ℕ) : ℝ) / 2 = -(r : ℝ) + -(1 / 2 : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num),
    Real.rpow_natCast, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
    one_div_pow, one_div, div_eq_mul_inv]
lemma reciprocalGeometricTail_even (r : ℕ) :
    reciprocalGeometricTail (2 * r) = 6 * (1 / 2 : ℝ) ^ r := by
  unfold reciprocalGeometricTail
  rw [show (2 * r) / 2 = r by omega, show (2 * r + 1) / 2 = r by omega]
  ring
lemma reciprocalGeometricTail_odd (r : ℕ) :
    reciprocalGeometricTail (2 * r + 1) = 4 * (1 / 2 : ℝ) ^ r := by
  unfold reciprocalGeometricTail
  rw [show (2 * r + 1) / 2 = r by omega,
    show (2 * r + 1 + 1) / 2 = r + 1 by omega, pow_succ]
  ring
lemma reciprocalGeometricTail_le_rpow (L : ℕ) :
    reciprocalGeometricTail L ≤ 6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  have hpar : L = 2 * (L / 2) ∨ L = 2 * (L / 2) + 1 := by omega
  rcases hpar with he | ho
  · conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [reciprocalGeometricTail_even, two_rpow_neg_half_even]
  · conv_lhs => rw [ho]
    conv_rhs => rw [ho]
    rw [reciprocalGeometricTail_odd, two_rpow_neg_half_odd]
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsle : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    have hc : (4 : ℝ) ≤ 6 / Real.sqrt 2 := by
      apply (le_div_iff₀ hs).2
      linarith
    calc
      _ ≤ (6 / Real.sqrt 2) * (1 / 2 : ℝ) ^ (L / 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
lemma sum_reciprocal_counting_le_rpow (L n : ℕ) :
    (∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h)) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  (sum_reciprocal_counting_le_tail L n).trans (reciprocalGeometricTail_le_rpow L)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma f2Probability_gcd_degree_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    f2Probability (n - 1)
      (fun p ↦ L ≤ (GCDMonoid.gcd p p.reverse).natDegree) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  (f2Probability_gcd_degree_le_sum hn L).trans (sum_reciprocal_counting_le_rpow L n)
theorem reciprocal_gcd_probability {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (fun p ↦
      L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  f2Probability_gcd_degree_le hn L
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def HasLargeReciprocalIntegerDivisor (L : ℕ) (p : ℤ[X]) : Prop :=
  ∃ J : ℤ[X], J.Monic ∧ J ∣ p ∧ J.reverse = J ∧ L ≤ J.natDegree
lemma HasBinaryEndpoints.gcd_degree_of_large_reciprocal_divisor {n L : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (h : HasLargeReciprocalIntegerDivisor L p) :
    L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree := by
  obtain ⟨J, hJ, hdvd, hrec, hL⟩ := h
  exact hL.trans (hp.reciprocal_divisor_degree_le_gcd hJ hdvd hrec)
lemma binaryProbability_large_reciprocal_divisor_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (HasLargeReciprocalIntegerDivisor L) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      exact hp.gcd_degree_of_large_reciprocal_divisor hw
    _ ≤ _ := reciprocal_gcd_probability hn L
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasBinaryEndpoints.reciprocal_divisor_candidate_alternative {n L : ℕ} {P : ℤ[X]}
    (hP : HasBinaryEndpoints n P) (hrec : HasLargeReciprocalIntegerDivisor 1 P)
    (hcyc : ¬ HasCyclotomicDivisor P) :
    (∃ J ∈ smallDivisorCandidates L, Irreducible (J.map (Int.castRingHom ℚ)) ∧
      ¬ HasCyclotomicDivisor J ∧ J ∣ P) ∨ HasLargeReciprocalIntegerDivisor L P := by
  obtain ⟨D, hD, hDP, hDrec, hDpos⟩ := hrec
  by_cases hDL : D.natDegree ≤ L
  · obtain ⟨J, hJ, hirr, hJD⟩ := exists_monic_rational_irreducible_divisor hD hDpos
    have hJP : J ∣ P := hJD.trans hDP
    have hdeg : J.natDegree ≤ L := (natDegree_le_of_dvd hJD hD.ne_zero).trans hDL
    have hpos : 0 < J.natDegree := by
      have h := hirr.natDegree_pos
      rwa [hJ.natDegree_map] at h
    have hJcyc : ¬ HasCyclotomicDivisor J := by
      rintro ⟨k, hk, hdiv⟩
      exact hcyc ⟨k, hk, hdiv.trans hJP⟩
    exact Or.inl ⟨J, hP.monic_divisor_mem_candidates hJ hJP hpos hdeg, hirr, hJcyc, hJP⟩
  · exact Or.inr ⟨D, hD, hDP, hDrec, by omega⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma mahler_log_lower_of_parameter_budget {L k n s S B m : ℝ}
    (hL : 1 ≤ L) (hlog : 3040 ≤ Real.log L)
    (hk : L ≤ k) (hkup : k ≤ 2 * L)
    (hn : L ^ 2 * Real.log L ≤ n)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2)
    (hS : S ≤ 256 * L ^ 4 * Real.log L)
    (hB : 0 ≤ B) (hBup : B ≤ 20 * L) (hm : 0 ≤ m)
    (hmain : k * n / 2 ≤ (k ^ 2 + k + 2 * s) * B + (k + s) * (k + S) * m) :
    1 / (18576 * L ^ 3) ≤ m := by
  have hL0 : 0 < L := by linarith
  have hl1 : 1 ≤ Real.log L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hA : k ^ 2 + k + 2 * s ≤ 38 * L ^ 2 := by
    have hk2 : k ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hk0 hkup 2
    nlinarith
  have hks : k + s ≤ 18 * L ^ 2 := by linarith
  have hL4 : L ≤ L ^ 4 * Real.log L := by
    calc
      L = L ^ 1 := by simp
      _ ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hl1
  have hkS : k + S ≤ 258 * L ^ 4 * Real.log L := by linarith
  have hcost : (k ^ 2 + k + 2 * s) * B ≤ 760 * L ^ 3 := by
    calc
      _ ≤ (38 * L ^ 2) * (20 * L) := mul_le_mul hA hBup hB (by positivity)
      _ = _ := by ring
  have hcoeff : (k + s) * (k + S) ≤ 4644 * L ^ 6 * Real.log L := by
    calc
      _ ≤ (k + s) * (258 * L ^ 4 * Real.log L) :=
        mul_le_mul_of_nonneg_left hkS (by linarith)
      _ ≤ (18 * L ^ 2) * (258 * L ^ 4 * Real.log L) :=
        mul_le_mul_of_nonneg_right hks (by positivity)
      _ = _ := by ring
  have hlower : L ^ 3 * Real.log L / 2 ≤ k * n / 2 := by
    have hnn : 0 ≤ n := (by positivity : 0 ≤ L ^ 2 * Real.log L).trans hn
    have h := mul_le_mul hk hn (by positivity : 0 ≤ L ^ 2 * Real.log L) hk0
    nlinarith
  have hmain' : L ^ 3 * Real.log L / 2 ≤
      760 * L ^ 3 + (4644 * L ^ 6 * Real.log L) * m := by
    exact hlower.trans (hmain.trans (add_le_add hcost (mul_le_mul_of_nonneg_right hcoeff hm)))
  have hquarter : 760 * L ^ 3 ≤ L ^ 3 * Real.log L / 4 := by
    have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ L ^ 3)
    nlinarith
  apply (div_le_iff₀ (show 0 < 18576 * L ^ 3 by positivity)).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < L ^ 3 * Real.log L by positivity)).mp
  nlinarith [hmain', hquarter]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma mahler_parameter_ceil_bounds {L : ℝ} (hL : 1 ≤ L)
    (hlog : 3040 ≤ Real.log L) :
    L ≤ (⌈L⌉₊ : ℝ) ∧ (⌈L⌉₊ : ℝ) ≤ 2 * L ∧
      L ^ 2 * Real.log L ≤ (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ∧
      (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ≤ 2 * L ^ 2 * Real.log L ∧
      L ≤ (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ∧
      1 < (⌈L ^ 2 * Real.log L⌉₊ : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog1 : 1 ≤ Real.log L := by linarith
  have hsq : L ≤ L ^ 2 := by nlinarith
  have hscale : L ≤ L ^ 2 * Real.log L :=
    hsq.trans (le_mul_of_one_le_right (sq_nonneg L) hlog1)
  have hn := Nat.le_ceil (L ^ 2 * Real.log L)
  have hkupper := Nat.ceil_lt_add_one hL0
  have hnupper := Nat.ceil_lt_add_one (hL0.trans hscale)
  have hlarge : 2 ≤ L ^ 2 * Real.log L := by
    have := mul_le_mul_of_nonneg_left hlog (sq_nonneg L)
    nlinarith
  exact ⟨Nat.le_ceil L, by linarith, hn, by linarith,
    hscale.trans hn, by linarith⟩
lemma mahler_prime_scale_log_lower {L n : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hn : L ^ 2 * Real.log L ≤ n) :
    2 * Real.log L ≤ Real.log n := by
  have hL0 : 0 < L := by linarith
  have hsq : L ^ 2 ≤ n := (le_mul_of_one_le_right (sq_nonneg L) hlog).trans hn
  simpa only [Real.log_pow, Nat.cast_ofNat] using
    Real.log_le_log (sq_pos_of_pos hL0) hsq
lemma mahler_prime_card_budget {L n s : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hn : L ^ 2 * Real.log L ≤ n)
    (hnup : n ≤ 2 * L ^ 2 * Real.log L)
    (hs : s ≤ 16 * n / Real.log n) : s ≤ 16 * L ^ 2 := by
  have hlogn := mahler_prime_scale_log_lower hL hlog hn
  have hpos : 0 < Real.log n := by linarith
  apply hs.trans
  apply (div_le_iff₀ hpos).mpr
  have h := mul_le_mul_of_nonneg_left hlogn (show 0 ≤ 16 * L ^ 2 by positivity)
  nlinarith
lemma mahler_prime_sum_budget {L n s S : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hnup : n ≤ 2 * L ^ 2 * Real.log L)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2) (hS : S ≤ s * (8 * n)) :
    S ≤ 256 * L ^ 4 * Real.log L := by
  calc
    S ≤ s * (8 * n) := hS
    _ ≤ s * (8 * (2 * L ^ 2 * Real.log L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnup (by norm_num)) hs
    _ ≤ (16 * L ^ 2) * (8 * (2 * L ^ 2 * Real.log L)) :=
      mul_le_mul_of_nonneg_right hsup (by positivity)
    _ = _ := by ring
lemma mahler_bad_prime_log_budget {d L n : ℝ} (hd : 0 < d)
    (hLd : Real.log d = L) (hL : 1 ≤ L) (hlog : 3040 ≤ Real.log L)
    (hn : L ^ 2 * Real.log L ≤ n) : Real.log (2 * d ^ 4) ≤ n / 2 := by
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow, hLd]
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hsq : L ≤ L ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hlog (sq_nonneg L)
  norm_num at htwo ⊢
  nlinarith
lemma mahler_node_log_budget {d L k s : ℝ} (hd : 1 ≤ d)
    (hLd : Real.log d = L) (hL : 1 ≤ L) (hk : L ≤ k) (hkup : k ≤ 2 * L)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2) :
    0 ≤ Real.log (d * (k + s)) ∧ Real.log (d * (k + s)) ≤ 20 * L := by
  have hd0 : 0 < d := by linarith
  have hL0 : 0 < L := by linarith
  have hks : 1 ≤ k + s := by linarith
  have hks0 : 0 < k + s := by linarith
  have hsq : L ≤ L ^ 2 := by nlinarith
  have hksup : k + s ≤ 18 * L ^ 2 := by linarith
  refine ⟨Real.log_nonneg (by nlinarith), ?_⟩
  rw [Real.log_mul hd0.ne' hks0.ne', hLd]
  have hb := Real.log_le_log hks0 hksup
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hL0.ne'), Real.log_pow] at hb
  have h18 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18)
  have hl := Real.log_le_sub_one_of_pos hL0
  norm_num at hb h18
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma taylor_X_sub_C_self {R : Type*} [CommRing R] (a : R) :
    taylor a (X - C a) = X := by simp
lemma taylor_coeff_pow_X_sub_C_mul {R : Type*} [CommRing R]
    (a : R) (r k : ℕ) (Q : R[X]) :
    (taylor a ((X - C a) ^ r * Q)).coeff k =
      if r ≤ k then (taylor a Q).coeff (k - r) else 0 := by
  rw [taylor_mul, taylor_pow, taylor_X_sub_C_self, coeff_X_pow_mul']
lemma hasseDeriv_eval_pow_X_sub_C_mul {R : Type*} [CommRing R]
    (a : R) (r : ℕ) (Q : R[X]) :
    (hasseDeriv r ((X - C a) ^ r * Q)).eval a = Q.eval a := by
  rw [← taylor_coeff, taylor_coeff_pow_X_sub_C_mul]
  simp
lemma hasseDeriv_eval_pow_X_sub_C_mul_of_lt {R : Type*} [CommRing R]
    (a : R) {r k : ℕ} (hkr : k < r) (Q : R[X]) :
    (hasseDeriv k ((X - C a) ^ r * Q)).eval a = 0 := by
  rw [← taylor_coeff, taylor_coeff_pow_X_sub_C_mul, if_neg (not_le.mpr hkr)]
lemma prod_X_sub_C_factor_at {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) :
    (∏ i ∈ s, (X - C (x i))) =
      (X - C a) ^ (s.filter (fun i ↦ x i = a)).card *
        ∏ i ∈ s.filter (fun i ↦ x i ≠ a), (X - C (x i)) := by
  conv_lhs => rw [← Finset.prod_filter_mul_prod_filter_not s (fun i ↦ x i = a)
    (fun i ↦ (X - C (x i) : R[X]))]
  congr 1
  calc
    _ = ∏ _i ∈ s.filter (fun i ↦ x i = a), (X - C a : R[X]) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by rw [Finset.prod_const]
lemma hasseDeriv_prod_X_sub_C_eval_multiplicity {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) :
    (hasseDeriv (s.filter (fun i ↦ x i = a)).card
      (∏ i ∈ s, (X - C (x i)))).eval a =
      ∏ i ∈ s.filter (fun i ↦ x i ≠ a), (a - x i) := by
  rw [prod_X_sub_C_factor_at s x a, hasseDeriv_eval_pow_X_sub_C_mul]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
lemma hasseDeriv_prod_X_sub_C_eval_eq_zero_of_lt {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) {k : ℕ}
    (hk : k < (s.filter (fun i ↦ x i = a)).card) :
    (hasseDeriv k (∏ i ∈ s, (X - C (x i)))).eval a = 0 := by
  rw [prod_X_sub_C_factor_at s x a]
  exact hasseDeriv_eval_pow_X_sub_C_mul_of_lt a hk _
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
def rootPrefixPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : R[X] := ∏ i ∈ Finset.Iio j, (X - C (x i))
def rootPrefixMultiplicity {R : Type*} {n : ℕ} (x : Fin n → R) (i : Fin n) : ℕ :=
  ((Finset.Iio i).filter (fun j ↦ x j = x i)).card
def confluentVandermonde {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ (j.val.choose (rootPrefixMultiplicity x i) : R) *
    x i ^ (j.val - rootPrefixMultiplicity x i)
lemma rootPrefixPolynomial_monic {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : (rootPrefixPolynomial x j).Monic := by
  exact monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (x i))
lemma rootPrefixPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (x : Fin n → R) (j : Fin n) : (rootPrefixPolynomial x j).natDegree = j.val := by
  rw [rootPrefixPolynomial, natDegree_finsetProd_X_sub_C_eq_card, Fin.card_Iio]
lemma rootPrefixMultiplicity_le {R : Type*} {n : ℕ} (x : Fin n → R) (i : Fin n) :
    rootPrefixMultiplicity x i ≤ i.val := by
  rw [rootPrefixMultiplicity, ← Fin.card_Iio i]
  exact Finset.card_filter_le _ _
lemma rootPrefixMultiplicity_lt_later_count {R : Type*} {n : ℕ}
    (x : Fin n → R) {i j : Fin n} (hij : i < j) :
    rootPrefixMultiplicity x i < ((Finset.Iio j).filter (fun k ↦ x k = x i)).card := by
  have hi : i ∉ (Finset.Iio i).filter (fun k ↦ x k = x i) := by simp
  have hsub : insert i ((Finset.Iio i).filter (fun k ↦ x k = x i)) ⊆
      (Finset.Iio j).filter (fun k ↦ x k = x i) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp [hij]
    · obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij), he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi] at hc
  exact hc
lemma hasseDeriv_eval_eq_sum_fin {R : Type*} [CommRing R] (a : R) (k : ℕ)
    {n : ℕ} (P : R[X]) (hP : P.natDegree < n) :
    (hasseDeriv k P).eval a =
      ∑ j : Fin n, (j.val.choose k : R) * a ^ (j.val - k) * P.coeff j.val := by
  conv_lhs => rw [P.as_sum_range' n hP]
  rw [map_sum, eval_finsetSum, Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (j.choose k : R) * a ^ (j - k) * P.coeff j)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [hasseDeriv_monomial, eval_monomial]
  ring
lemma confluentVandermonde_mul_coefficients {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (P : Fin n → R[X]) (hP : ∀ j, (P j).natDegree < n) :
    confluentVandermonde x * Matrix.of (fun i j : Fin n ↦ (P j).coeff i.val) =
      Matrix.of (fun i j ↦ (hasseDeriv (rootPrefixMultiplicity x i) (P j)).eval (x i)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [hasseDeriv_eval_eq_sum_fin _ _ _ (hP j)]
  rfl
lemma confluentVandermonde_newton_lowerTriangular {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) :
    (Matrix.of (fun i j : Fin n ↦ (hasseDeriv (rootPrefixMultiplicity x i)
      (rootPrefixPolynomial x j)).eval (x i))).IsLowerTriangular := by
  intro i j hij
  exact hasseDeriv_prod_X_sub_C_eval_eq_zero_of_lt _ _ _
    (rootPrefixMultiplicity_lt_later_count x hij)
lemma confluentVandermonde_newton_diagonal {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) (i : Fin n) :
    (hasseDeriv (rootPrefixMultiplicity x i) (rootPrefixPolynomial x i)).eval (x i) =
      ∏ j ∈ (Finset.Iio i).filter (fun j ↦ x j ≠ x i), (x i - x j) := by
  exact hasseDeriv_prod_X_sub_C_eval_multiplicity _ _ _
lemma det_confluentVandermonde {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (x : Fin n → R) :
    (confluentVandermonde x).det =
      ∏ i : Fin n, ∏ j ∈ (Finset.Iio i).filter (fun j ↦ x j ≠ x i), (x i - x j) := by
  have hc : (Matrix.of (fun i j : Fin n ↦ (rootPrefixPolynomial x j).coeff i.val)).det = 1 :=
    Matrix.det_matrixOfPolynomials _ (rootPrefixPolynomial_natDegree x) (rootPrefixPolynomial_monic x)
  have he := congrArg Matrix.det (confluentVandermonde_mul_coefficients x
    (rootPrefixPolynomial x) (fun j ↦ (rootPrefixPolynomial_natDegree x j).trans_lt j.isLt))
  rw [Matrix.det_mul, hc, mul_one,
    Matrix.det_of_isLowerTriangular _ (confluentVandermonde_newton_lowerTriangular x)] at he
  rw [he]
  exact Finset.prod_congr rfl (fun i _ ↦ confluentVandermonde_newton_diagonal x i)
lemma det_confluentVandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x : Fin n → R) : (confluentVandermonde x).det ≠ 0 := by
  rw [det_confluentVandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (Finset.mem_filter.mp hj).2.symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma norm_det_le_factorial_mul_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℝ) (hA : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ (n.factorial : ℝ) * ∏ i, b i := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, b i := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      rw [norm_mul, hs, one_mul, norm_prod]
      calc
        _ ≤ ∏ i, b (σ i) := Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hA _ _)
        _ = _ := Equiv.prod_comp σ b
    _ = _ := by simp [Fintype.card_perm]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma norm_confluentVandermonde_entry_le {n : ℕ} (x : Fin n → ℂ) (i j : Fin n) :
    ‖confluentVandermonde x i j‖ ≤
      (n : ℝ) ^ rootPrefixMultiplicity x i * (max 1 ‖x i‖) ^ n := by
  have hc : ((j.val.choose (rootPrefixMultiplicity x i) : ℕ) : ℝ) ≤
      (n : ℝ) ^ rootPrefixMultiplicity x i := by
    exact_mod_cast (Nat.choose_le_pow j.val (rootPrefixMultiplicity x i)).trans
      (Nat.pow_le_pow_left j.isLt.le _)
  have hm : ‖x i‖ ^ (j.val - rootPrefixMultiplicity x i) ≤ (max 1 ‖x i‖) ^ n := by
    calc
      _ ≤ (max 1 ‖x i‖) ^ (j.val - rootPrefixMultiplicity x i) :=
        pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) ((Nat.sub_le _ _).trans j.isLt.le)
  simp only [confluentVandermonde, norm_mul, Complex.norm_natCast, norm_pow]
  exact mul_le_mul hc hm (by positivity) (by positivity)
lemma norm_det_confluentVandermonde_le {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ≤
      (n.factorial : ℝ) * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := by
  have h := norm_det_le_factorial_mul_prod (confluentVandermonde x)
    (fun i ↦ (n : ℝ) ^ rootPrefixMultiplicity x i * (max 1 ‖x i‖) ^ n)
    (norm_confluentVandermonde_entry_le x)
  simpa only [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow, mul_assoc] using h
lemma norm_det_confluentVandermonde_le_power {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ≤
      (n : ℝ) ^ (n + ∑ i, rootPrefixMultiplicity x i) * (∏ i, max 1 ‖x i‖) ^ n := by
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc
    _ ≤ (n.factorial : ℝ) * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := norm_det_confluentVandermonde_le x
    _ ≤ (n : ℝ) ^ n * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := by gcongr
    _ = _ := by rw [pow_add]
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open scoped BigOperators Classical
lemma card_repeated_family {ι β : Type*} [Fintype ι] [Fintype β] (w : ι → ℕ) :
    Fintype.card (Σ t, Fin (w t) × β) = Fintype.card β * ∑ t, w t := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, Nat.mul_comm]
lemma repeated_root_fiber_count {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2)) (t : ι) (a : β) :
    (Finset.univ.filter (fun j : (Σ t, Fin (w t) × β) ↦ x j.1 j.2.2 = x t a)).card = w t := by
  have hxy (u : ι) (b : β) : x u b = x t a ↔ u = t ∧ b = a := by
    constructor
    · intro he
      exact Prod.mk.inj (hx he)
    · rintro ⟨rfl, rfl⟩
      rfl
  have he := Finset.sum_boole (R := ℕ)
    (fun j : (Σ t, Fin (w t) × β) ↦ x j.1 j.2.2 = x t a) Finset.univ
  simp only [Nat.cast_id] at he
  rw [← he]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, hxy]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u hu hut
    simp [hut]
  · simp
lemma rootPrefixMultiplicity_repeated_le {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2))
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β)) (i : Fin n) :
    rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i ≤ w (e i).1 := by
  have he := e.sum_comp (fun j : (Σ t, Fin (w t) × β) ↦
    if x j.1 j.2.2 = x (e i).1 (e i).2.2 then (1 : ℕ) else 0)
  simp only [Finset.sum_boole, Nat.cast_id] at he
  rw [repeated_root_fiber_count w x hx] at he
  calc
    _ ≤ (Finset.univ.filter (fun j ↦ x (e j).1 (e j).2.2 = x (e i).1 (e i).2.2)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ = _ := he
lemma sum_rootPrefixMultiplicity_repeated_le {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2))
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β)) :
    (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      Fintype.card β * ∑ t, w t ^ 2 := by
  calc
    _ ≤ ∑ i : Fin n, w (e i).1 :=
      Finset.sum_le_sum (fun i _ ↦ rootPrefixMultiplicity_repeated_le w x hx e i)
    _ = ∑ j : (Σ t, Fin (w t) × β), w j.1 := e.sum_comp (fun j ↦ w j.1)
    _ = _ := by
      simp only [Fintype.sum_sigma, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
lemma card_repeated_option_family {ι β : Type*} [Fintype ι] [Fintype β] (k : ℕ) :
    Fintype.card (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β) =
      Fintype.card β * (k + Fintype.card ι) := by
  rw [card_repeated_family]
  simp [Fintype.sum_option]
end OdlyzkoPoonen

open Polynomial
namespace OdlyzkoPoonen
noncomputable def polynomialRootPowers {R : Type*} [CommRing R]
    (p : R[X]) (k : ℕ) : R[X] :=
  (p.map (Polynomial.C : R →+* R[X])).resultant
    (Polynomial.C (X : R[X]) - X ^ k) p.natDegree k
theorem polynomialRootPowers_eq_prod_of_splits {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p.Splits) (k : ℕ) :
    polynomialRootPowers p k = C (p.leadingCoeff ^ k) *
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod := by
  have hs := hp.map (Polynomial.C : R →+* R[X])
  have hd : (C (X : R[X]) - X ^ k).natDegree ≤ k := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have h := resultant_eq_prod_eval (p.map (Polynomial.C : R →+* R[X]))
    (C (X : R[X]) - X ^ k) k hd hs
  rw [natDegree_map_eq_of_injective C_injective] at h
  rw [polynomialRootPowers, h]
  rw [leadingCoeff_map_of_injective C_injective,
    hp.roots_map_of_injective C_injective]
  simp only [← map_pow, Multiset.map_map, Function.comp_apply,
    eval_sub, eval_C, eval_pow, eval_X]
theorem polynomialRootPowers_eq_prod (p : ℂ[X]) (k : ℕ) :
    polynomialRootPowers p k = C (p.leadingCoeff ^ k) *
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod :=
  polynomialRootPowers_eq_prod_of_splits p (IsAlgClosed.splits p) k
theorem polynomialRootPowers_leadingCoeff_of_splits {R : Type*}
    [CommRing R] [IsDomain R] (p : R[X]) (hp : p.Splits) (k : ℕ) :
    (polynomialRootPowers p k).leadingCoeff = p.leadingCoeff ^ k := by
  rw [polynomialRootPowers_eq_prod_of_splits p hp k, leadingCoeff_mul, leadingCoeff_C,
    (monic_multiset_prod_of_monic p.roots (fun z ↦ X - C (z ^ k))
      (fun z _ ↦ monic_X_sub_C (z ^ k))).leadingCoeff, mul_one]
theorem polynomialRootPowers_natDegree_of_splits {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) (hs : p.Splits) (k : ℕ) :
    (polynomialRootPowers p k).natDegree = p.natDegree := by
  rw [polynomialRootPowers_eq_prod_of_splits p hs k,
    natDegree_C_mul (pow_ne_zero k (leadingCoeff_ne_zero.mpr hp))]
  have he : p.roots.map (fun z ↦ X - C (z ^ k)) =
      (p.roots.map (fun z ↦ z ^ k)).map (fun z ↦ X - C z) := by
    rw [Multiset.map_map]
    rfl
  rw [he, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map,
    ← hs.natDegree_eq_card_roots]
theorem polynomialRootPowers_dvd_pow_of_dvd_comp {p q : ℂ[X]} (hp : p ≠ 0)
    (k : ℕ) (hd : p ∣ q.comp (X ^ k)) :
    polynomialRootPowers p k ∣ q ^ p.natDegree := by
  have hroot (z : ℂ) (hz : z ∈ p.roots) : X - C (z ^ k) ∣ q := by
    apply dvd_iff_isRoot.mpr
    have h := ((mem_roots hp).mp hz).dvd hd
    simpa only [IsRoot, eval_comp, eval_pow, eval_X] using h
  have hprod := Multiset.prod_dvd_prod_of_dvd
    (fun z : ℂ ↦ X - C (z ^ k)) (fun _ : ℂ ↦ q) hroot
  have hdiv : (p.roots.map (fun z ↦ X - C (z ^ k))).prod ∣ q ^ p.natDegree := by
    simpa only [Multiset.map_const', Multiset.prod_replicate,
      ← (IsAlgClosed.splits p).natDegree_eq_card_roots] using hprod
  rw [polynomialRootPowers_eq_prod]
  have hu : IsUnit (C (p.leadingCoeff ^ k)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero k (leadingCoeff_ne_zero.mpr hp)))
  have hc : C (p.leadingCoeff ^ k) * (p.roots.map (fun z ↦ X - C (z ^ k))).prod ∣
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod := by
    simpa using mul_dvd_mul (isUnit_iff_dvd_one.mp hu) (dvd_refl
      ((p.roots.map (fun z ↦ X - C (z ^ k))).prod))
  exact hc.trans hdiv
theorem polynomialRootPowers_mahlerMeasure (p : ℂ[X]) (k : ℕ) :
    (polynomialRootPowers p k).mahlerMeasure = p.mahlerMeasure ^ k := by
  rw [polynomialRootPowers_eq_prod, Polynomial.mahlerMeasure_mul,
    Polynomial.mahlerMeasure_const, norm_pow,
    Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod, Multiset.map_map]
  simp only [Function.comp_apply, Polynomial.mahlerMeasure_X_sub_C, norm_pow]
  have hm (z : ℂ) : max 1 (‖z‖ ^ k) = (max 1 ‖z‖) ^ k := by
    rcases le_total ‖z‖ 1 with hz | hz
    · rw [max_eq_left hz, one_pow, max_eq_left (pow_le_one₀ (norm_nonneg _) hz)]
    · rw [max_eq_right hz, max_eq_right (one_le_pow₀ hz)]
  simp_rw [hm]
  rw [Multiset.prod_map_pow, Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    mul_pow]
theorem polynomialRootPowers_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (p : R[X]) (k : ℕ) :
    (polynomialRootPowers p k).map φ = polynomialRootPowers (p.map φ) k := by
  unfold polynomialRootPowers
  change (Polynomial.mapRingHom φ)
    ((p.map C).resultant (C (X : R[X]) - X ^ k) p.natDegree k) = _
  rw [← resultant_map_map _ _ _ _ (Polynomial.mapRingHom φ),
    natDegree_map_eq_of_injective hφ]
  have hc : (Polynomial.mapRingHom φ).comp (Polynomial.C : R →+* R[X]) =
      (Polynomial.C : S →+* S[X]).comp φ := by
    ext a
    simp
  congr 1
  · rw [Polynomial.map_map, Polynomial.map_map, hc]
  · simp only [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]
theorem polynomialRootPowers_isRoot {p : ℂ[X]} (hp : p ≠ 0)
    {z : ℂ} (hz : p.IsRoot z) (k : ℕ) :
    (polynomialRootPowers p k).IsRoot (z ^ k) := by
  apply dvd_iff_isRoot.mp
  rw [polynomialRootPowers_eq_prod]
  apply dvd_mul_of_dvd_right
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨z, (mem_roots hp).mpr hz, rfl⟩)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma max_one_norm_pow (z : ℂ) (q : ℕ) :
    max 1 ‖z ^ q‖ = (max 1 ‖z‖) ^ q := by
  rw [norm_pow]
  by_cases h : ‖z‖ ≤ 1
  · rw [max_eq_left h, max_eq_left (pow_le_one₀ (norm_nonneg z) h), one_pow]
  · have h' : 1 ≤ ‖z‖ := le_of_not_ge h
    rw [max_eq_right h', max_eq_right (one_le_pow₀ h')]
lemma prod_max_one_norm_mono {s t : Multiset ℂ} (hst : s ≤ t) :
    (s.map (fun z ↦ max 1 ‖z‖)).prod ≤ (t.map (fun z ↦ max 1 ‖z‖)).prod := by
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  rw [Multiset.map_add, Multiset.prod_add]
  exact le_mul_of_one_le_right
    (Multiset.prod_map_nonneg (fun _ _ ↦ (by positivity)))
    (Multiset.one_le_prod_map (fun z _ ↦ le_max_left 1 ‖z‖))
lemma roots_pow_le_of_dvd_expand {J R : ℂ[X]} {q : ℕ}
    (hJ : J ≠ 0) (hR : R ≠ 0) (hsimple : J.roots.Nodup)
    (hsep : ∀ z ∈ J.roots, ∀ w ∈ J.roots, z ^ q = w ^ q → z = w)
    (hdvd : J ∣ expand ℂ q R) :
    J.roots.map (fun z ↦ z ^ q) ≤ R.roots := by
  apply (Multiset.le_iff_subset (Multiset.Nodup.map_on hsep hsimple)).mpr
  intro a ha
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
  apply (mem_roots hR).mpr
  have hzero := ((mem_roots hJ).mp hz).dvd hdvd
  simpa only [IsRoot.def, expand_eval] using hzero
lemma mahlerMeasure_pow_le_of_dvd_expand {J R : ℂ[X]} (q : ℕ)
    (hJ : J.Monic) (hR : 1 ≤ ‖R.leadingCoeff‖) (hsimple : J.roots.Nodup)
    (hsep : ∀ z ∈ J.roots, ∀ w ∈ J.roots, z ^ q = w ^ q → z = w)
    (hdvd : J ∣ expand ℂ q R) :
    J.mahlerMeasure ^ q ≤ R.mahlerMeasure := by
  have hR0 : R ≠ 0 := by intro h; norm_num [h] at hR
  have hle := roots_pow_le_of_dvd_expand hJ.ne_zero hR0 hsimple hsep hdvd
  calc
    J.mahlerMeasure ^ q = (J.roots.map (fun z ↦ max 1 ‖z ^ q‖)).prod := by
      rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hJ.leadingCoeff, norm_one,
        one_mul]
      simp_rw [max_one_norm_pow]
      exact Multiset.prod_map_pow.symm
    _ = ((J.roots.map (fun z ↦ z ^ q)).map (fun z ↦ max 1 ‖z‖)).prod := by
      simp only [Multiset.map_map, Function.comp_def]
    _ ≤ (R.roots.map (fun z ↦ max 1 ‖z‖)).prod := prod_max_one_norm_mono hle
    _ ≤ R.mahlerMeasure :=
      prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff hR
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma prod_max_norm_root_powers {β : Type*} [Fintype β] (α : β → ℂ) (r : ℕ) :
    (∏ a, max 1 ‖α a ^ r‖) = (∏ a, max 1 ‖α a‖) ^ r := by
  simp only [max_one_norm_pow, Finset.prod_pow]
lemma prod_max_norm_eq_mahler_of_factorization {β : Type*} [Fintype β]
    (α : β → ℂ) {f : ℂ[X]} (hf : f = ∏ a, (X - C (α a))) :
    (∏ a, max 1 ‖α a‖) = f.mahlerMeasure := by
  rw [hf]
  simp only [Finset.prod_eq_multiset_prod]
  rw [prod_mahlerMeasure_eq_mahlerMeasure_prod]
  simp only [Multiset.map_map, Function.comp_def, mahlerMeasure_X_sub_C]
lemma prod_max_norm_repeated_root_powers {ι β : Type*} [Fintype ι] [Fintype β]
    (w r : ι → ℕ) (α : β → ℂ) {f : ℂ[X]}
    (hf : f = ∏ a, (X - C (α a))) {n : ℕ}
    (e : Fin n ≃ (Σ t, Fin (w t) × β)) :
    (∏ i, max 1 ‖α (e i).2.2 ^ r (e i).1‖) =
      f.mahlerMeasure ^ (∑ t, r t * w t) := by
  calc
    _ = ∏ j : (Σ t, Fin (w t) × β), max 1 ‖α j.2.2 ^ r j.1‖ :=
      e.prod_comp (fun j ↦ max 1 ‖α j.2.2 ^ r j.1‖)
    _ = ∏ t, (∏ a, max 1 ‖α a ^ r t‖) ^ w t := by
      simp only [Fintype.prod_sigma, Fintype.prod_prod_type, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = ∏ t, f.mahlerMeasure ^ (r t * w t) := by
      simp only [prod_max_norm_root_powers, prod_max_norm_eq_mahler_of_factorization α hf,
        ← pow_mul]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
lemma prod_max_norm_option_root_powers {ι β : Type*} [Fintype ι] [Fintype β]
    (k : ℕ) (p : ι → ℕ) (α : β → ℂ) {f : ℂ[X]}
    (hf : f = ∏ a, (X - C (α a))) {n : ℕ}
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β)) :
    (∏ i, max 1 ‖α (e i).2.2 ^ (e i).1.elim 1 p‖) =
      f.mahlerMeasure ^ (k + ∑ i, p i) := by
  rw [prod_max_norm_repeated_root_powers (fun t : Option ι ↦ t.elim k (fun _ ↦ 1))
    (fun t ↦ t.elim 1 p) α hf e]
  simp [Fintype.sum_option]
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma exists_injective_complex_root_family {f : ℂ[X]} (hf : f.Monic)
    (hn : f.roots.Nodup) :
    ∃ x : Fin f.natDegree → ℂ, Function.Injective x ∧
      (∀ i, x i ∈ f.roots) ∧ f = ∏ i, (X - C (x i)) := by
  let S := f.roots.toFinset
  have hc : Fintype.card S = f.natDegree := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hn,
      ← (IsAlgClosed.splits f).natDegree_eq_card_roots]
  let e : Fin f.natDegree ≃ S := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(fun i ↦ (e i : ℂ)), Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · intro i
    exact Multiset.mem_toFinset.mp (e i).property
  · calc
      f = (f.roots.map (fun z ↦ X - C z)).prod :=
        (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
      _ = ∏ z ∈ S, (X - C z) := by
        rw [Finset.prod_eq_multiset_prod]
        dsimp [S]
        rw [hn.dedup]
      _ = ∏ z : S, (X - C (z : ℂ)) := (Finset.prod_coe_sort _ _).symm
      _ = ∏ i : Fin f.natDegree, (X - C (e i : ℂ)) :=
        (e.prod_comp (fun z : S ↦ (X - C (z : ℂ)))).symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma root_ne_zero_of_constant_ne_zero {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hP : P.coeff 0 ≠ 0) {x : K}
    (hx : x ∈ P.rootSet K) : x ≠ 0 := by
  intro hx0
  have he := aeval_eq_zero_of_mem_rootSet hx
  rw [hx0] at he
  apply hP
  apply (algebraMap F K).injective
  rw [map_zero (algebraMap F K), coeff_zero_eq_aeval_zero']
  exact he
lemma exists_algEquiv_map_root {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) {x y : K} (hx : x ∈ P.rootSet K)
    (hy : y ∈ P.rootSet K) : ∃ σ : K ≃ₐ[F] K, σ x = y := by
  apply minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic y)
  rw [← minpoly.eq_of_irreducible_of_monic hirr
    (aeval_eq_zero_of_mem_rootSet hy) hmonic]
  exact aeval_eq_zero_of_mem_rootSet hx
lemma algEquiv_map_mem_rootSet {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {x : K}
    (hx : x ∈ P.rootSet K) : σ x ∈ P.rootSet K :=
  rootSet_mapsTo σ.toAlgHom hx
lemma exists_algEquiv_map_primitiveRoot {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {r : ℕ} (hr : 0 < r) {x y : K}
    (hx : IsPrimitiveRoot x r) (hy : IsPrimitiveRoot y r) :
    ∃ σ : K ≃ₐ[ℚ] K, σ x = y := by
  apply minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic y)
  rw [← cyclotomic_eq_minpoly_rat hy hr, cyclotomic_eq_minpoly_rat hx hr]
  exact minpoly.aeval ℚ x
lemma rootSet_nonempty_of_splits_of_irreducible {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hmonic : P.Monic) (hirr : Irreducible P)
    (hsplit : (P.map (algebraMap F K)).Splits) : (P.rootSet K).Nonempty := by
  have hdegree : (P.map (algebraMap F K)).natDegree ≠ 0 := by
    rw [natDegree_map_eq_of_injective (algebraMap F K).injective]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (degree_ne_of_natDegree_ne hdegree)
  refine ⟨x, hmonic.mem_rootSet.mpr ?_⟩
  simpa only [eval_map, aeval_def] using hx
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma pow_injective_of_no_positive_power_eq_one {K : Type*} [Field K] {a : K}
    (ha : a ≠ 0) (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) :
    Function.Injective (fun k : ℕ ↦ a ^ k) := by
  intro m n he
  change a ^ m = a ^ n at he
  wlog hmn : m ≤ n generalizing m n
  · exact (this he.symm (le_of_not_ge hmn)).symm
  by_contra hne
  have hlt : m < n := lt_of_le_of_ne hmn hne
  have hpow : a ^ m * a ^ (n - m) = a ^ m * 1 := by
    rw [← pow_add, Nat.add_sub_of_le hmn, ← he, mul_one]
  exact hno (n - m) (Nat.sub_pos_of_lt hlt) (mul_left_cancel₀ (pow_ne_zero _ ha) hpow)
lemma algEquiv_iterated_power_relation {F K : Type*} [Field F] [Field K]
    [Algebra F K] (σ : K ≃ₐ[F] K) {a : K} {r s : ℕ}
    (h : (σ a) ^ s = a ^ r) (m : ℕ) :
    ((σ ^ m) a) ^ (s ^ m) = a ^ (r ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      _ = (σ (((σ ^ m) a) ^ (s ^ m))) ^ s := by
        rw [pow_succ' σ, AlgEquiv.mul_apply, pow_succ s, pow_mul, map_pow]
      _ = (σ (a ^ (r ^ m))) ^ s := by rw [ih]
      _ = ((σ a) ^ s) ^ (r ^ m) := by rw [map_pow, pow_right_comm]
      _ = a ^ (r ^ (m + 1)) := by rw [h, ← pow_mul, pow_succ']
lemma exists_positive_algEquiv_power_fix_root {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {a : K} (ha : a ∈ P.rootSet K) :
    ∃ m : ℕ, 0 < m ∧ (σ ^ m) a = a := by
  classical
  let ρ : (K ≃ₐ[F] K) →* Equiv.Perm (P.rootSet K) :=
    MulAction.toPermHom _ _
  refine ⟨orderOf (ρ σ), orderOf_pos _, ?_⟩
  have h : ρ (σ ^ orderOf (ρ σ)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  have hx := congrArg (fun τ : Equiv.Perm (P.rootSet K) ↦ (τ ⟨a, ha⟩).val) h
  exact hx
lemma eq_exponents_of_periodic_algEquiv_power_relation {F K : Type*} [Field F]
    [Field K] [Algebra F K] (σ : K ≃ₐ[F] K) {a : K} (ha : a ≠ 0)
    (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) {r s m : ℕ} (hm : 0 < m)
    (hperiod : (σ ^ m) a = a) (h : (σ a) ^ s = a ^ r) : r = s := by
  have he := algEquiv_iterated_power_relation σ h m
  rw [hperiod] at he
  have hnat := pow_injective_of_no_positive_power_eq_one ha hno he
  exact (Nat.pow_left_injective hm.ne' hnat).symm
lemma eq_exponents_of_conjugate_root_powers {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {a b : K}
    (ha : a ∈ P.rootSet K) (hb : b ∈ P.rootSet K)
    (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) {r s : ℕ} (he : a ^ r = b ^ s) : r = s := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_root hmonic hirr ha hb
  obtain ⟨m, hm, hperiod⟩ := exists_positive_algEquiv_power_fix_root σ ha
  exact eq_exponents_of_periodic_algEquiv_power_relation σ
    (root_ne_zero_of_constant_ne_zero hconst ha) hno hm hperiod (by rw [hσ]; exact he.symm)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma root_pow_ne_one_of_no_cyclotomic {K : Type*} [Field K] [CharZero K]
    {J : ℤ[X]} (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hcyc : ¬ HasCyclotomicDivisor J) {a : K}
    (ha : a ∈ (J.map (Int.castRingHom ℚ)).rootSet K) {r : ℕ} (hr : 0 < r) :
    a ^ r ≠ 1 := by
  intro he
  have hfinite : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, he⟩
  have horder := hfinite.orderOf_pos
  have hmin : J.map (Int.castRingHom ℚ) = minpoly ℚ a :=
    minpoly.eq_of_irreducible_of_monic hirr (aeval_eq_zero_of_mem_rootSet ha) (hmonic.map _)
  have heq : cyclotomic (orderOf a) ℚ = J.map (Int.castRingHom ℚ) :=
    (cyclotomic_eq_minpoly_rat (IsPrimitiveRoot.orderOf a) horder).trans hmin.symm
  apply hcyc
  refine ⟨orderOf a, horder, (cyclotomic_dvd_iff_rational _ _).mpr ?_⟩
  rw [heq]
lemma eq_exponents_of_noncyclotomic_root_powers {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {a b : K}
    (ha : a ∈ (J.map (Int.castRingHom ℚ)).rootSet K)
    (hb : b ∈ (J.map (Int.castRingHom ℚ)).rootSet K) {r s : ℕ}
    (he : a ^ r = b ^ s) : r = s := by
  apply eq_exponents_of_conjugate_root_powers (hmonic.map _) hirr ?_ ha hb
    (fun k hk ↦ root_pow_ne_one_of_no_cyclotomic hmonic hirr hcyc ha hk) he
  simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma eq_exponents_of_noncyclotomic_complex_root_powers {J : ℤ[X]}
    (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hconst : J.coeff 0 ≠ 0) (hcyc : ¬ HasCyclotomicDivisor J) {a b : ℂ}
    (ha : a ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hb : b ∈ (J.map (Int.castRingHom ℂ)).roots) {r s : ℕ}
    (he : a ^ r = b ^ s) : r = s := by
  let P : ℚ[X] := J.map (Int.castRingHom ℚ)
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  have hmap : P.map (algebraMap ℚ ℂ) = J.map (Int.castRingHom ℂ) := by
    dsimp [P]
    rw [Polynomial.map_map]
    congr 1
  have ha' : a ∈ P.rootSet ℂ := by
    change a ∈ (P.map (algebraMap ℚ ℂ)).roots.toFinset
    rw [hmap]
    exact Multiset.mem_toFinset.mpr ha
  have hb' : b ∈ P.rootSet ℂ := by
    change b ∈ (P.map (algebraMap ℚ ℂ)).roots.toFinset
    rw [hmap]
    exact Multiset.mem_toFinset.mpr hb
  let j : P.SplittingField →ₐ[ℚ] ℂ := SplittingField.lift P (IsAlgClosed.splits _)
  have himage := (SplittingField.splits P).image_rootSet j
  rw [← himage] at ha' hb'
  obtain ⟨x, hx, rfl⟩ := ha'
  obtain ⟨y, hy, rfl⟩ := hb'
  apply eq_exponents_of_noncyclotomic_root_powers hmonic hirr hconst hcyc hx hy
  apply j.injective
  change j (x ^ r) = j (y ^ s)
  rw [map_pow, map_pow]
  exact he
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma polynomialRootPowers_complex_ne_zero {P : ℂ[X]} (hP : P ≠ 0) (r : ℕ) :
    polynomialRootPowers P r ≠ 0 := by
  intro hz
  have hl := polynomialRootPowers_leadingCoeff_of_splits P (IsAlgClosed.splits P) r
  rw [hz, leadingCoeff_zero] at hl
  exact (pow_ne_zero r (leadingCoeff_ne_zero.mpr hP)) hl.symm
lemma polynomialRootPowers_complex_roots {P : ℂ[X]} (hP : P ≠ 0) (r : ℕ) :
    (polynomialRootPowers P r).roots = P.roots.map (fun a ↦ a ^ r) := by
  rw [polynomialRootPowers_eq_prod, roots_C_mul _ (pow_ne_zero r (leadingCoeff_ne_zero.mpr hP))]
  have he : P.roots.map (fun a ↦ X - C (a ^ r)) =
      (P.roots.map (fun a ↦ a ^ r)).map (fun a ↦ X - C a) := by
    rw [Multiset.map_map]
    rfl
  rw [he, roots_multiset_prod_X_sub_C]
lemma rootPowers_isCoprime_of_distinct_exponents {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {r s : ℕ} (hrs : r ≠ s) :
    IsCoprime (polynomialRootPowers (J.map (Int.castRingHom ℂ)) r)
      (polynomialRootPowers (J.map (Int.castRingHom ℂ)) s) := by
  have hJ : J.map (Int.castRingHom ℂ) ≠ 0 := (hmonic.map _).ne_zero
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro z
  by_contra! h
  have hz₁ : z ∈ (polynomialRootPowers (J.map (Int.castRingHom ℂ)) r).roots := by
    apply (mem_roots (polynomialRootPowers_complex_ne_zero hJ r)).mpr
    exact h.1
  have hz₂ : z ∈ (polynomialRootPowers (J.map (Int.castRingHom ℂ)) s).roots := by
    apply (mem_roots (polynomialRootPowers_complex_ne_zero hJ s)).mpr
    exact h.2
  rw [polynomialRootPowers_complex_roots hJ] at hz₁ hz₂
  obtain ⟨a, ha, he₁⟩ := Multiset.mem_map.mp hz₁
  obtain ⟨b, hb, he₂⟩ := Multiset.mem_map.mp hz₂
  exact hrs (eq_exponents_of_noncyclotomic_complex_root_powers
    hmonic hirr hconst hcyc ha hb (he₁.trans he₂.symm))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma comp_X_pow_eq_pow_zmod {p : ℕ} (hp : p.Prime) (f : (ZMod p)[X]) :
    f.comp (X ^ p) = f ^ p := by
  let : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.frobenius_zmod, Polynomial.map_id,
    Polynomial.expand_eq_comp_X_pow] using Polynomial.map_frobenius_expand p f
lemma prime_C_dvd_comp_X_pow_sub_pow (J : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    C (p : ℤ) ∣ J.comp (X ^ p) - J ^ p := by
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have hz : (J.comp (X ^ p) - J ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_X, comp_X_pow_eq_pow_zmod hp, sub_self]
  have hc := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) hz
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Int.coe_castRingHom] using hc
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma resultant_map_injective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (f g : R[X]) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map]
lemma monic_resultant_right_degree {R : Type*} [CommRing R] {f : R[X]}
    (hf : f.Monic) (g : R[X]) {n : ℕ} (hn : g.natDegree ≤ n) :
    resultant f g f.natDegree n = resultant f g := by
  have he : n = g.natDegree + (n - g.natDegree) := by omega
  rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp [hf.coeff_natDegree]
lemma pow_dvd_resultant_of_C_dvd_sub_mul {R : Type*} [CommRing R]
    {f g h : R[X]} (hf : f.Monic) {c : R} (hc : C c ∣ g - f * h) :
    c ^ f.natDegree ∣ resultant f g := by
  let N := g.natDegree + (h.natDegree + f.natDegree)
  have hpad := monic_resultant_right_degree hf g (n := N) (by dsimp [N]; omega)
  have he := resultant_add_mul_right f (g - f * h) h f.natDegree N
    (by dsimp [N]; omega) le_rfl
  rw [sub_add_cancel] at he
  rw [← hpad, he]
  obtain ⟨v, hv⟩ := hc
  rw [hv, resultant_C_mul_right]
  exact dvd_mul_right _ _
lemma prime_pow_degree_dvd_resultant_comp_X_pow {J : ℤ[X]} (hJ : J.Monic)
    {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ^ J.natDegree ∣ resultant J (J.comp (X ^ p)) := by
  apply pow_dvd_resultant_of_C_dvd_sub_mul (h := J ^ (p - 1)) hJ
  have he : J * J ^ (p - 1) = J ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
  rw [he]
  exact prime_C_dvd_comp_X_pow_sub_pow J hp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma polynomialRootPowers_complex_monic {f : ℂ[X]} (hf : f.Monic) (r : ℕ) :
    (polynomialRootPowers f r).Monic := by
  rw [Monic, polynomialRootPowers_leadingCoeff_of_splits f (IsAlgClosed.splits f)]
  simp [hf.leadingCoeff]
lemma polynomialRootPowers_one_complex {f : ℂ[X]} (hf : f.Monic) :
    polynomialRootPowers f 1 = f := by
  rw [polynomialRootPowers_eq_prod]
  simp only [pow_one, hf.leadingCoeff, map_one, one_mul]
  exact ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).symm
lemma polynomialRootPowers_int_monic {J : ℤ[X]} (hJ : J.Monic) (r : ℕ) :
    (polynomialRootPowers J r).Monic := by
  apply Polynomial.monic_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)
  rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]
  exact polynomialRootPowers_complex_monic (hJ.map _) r
lemma polynomialRootPowers_int_natDegree {J : ℤ[X]} (hJ : J.Monic) (r : ℕ) :
    (polynomialRootPowers J r).natDegree = J.natDegree := by
  rw [← natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
    polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
    polynomialRootPowers_natDegree_of_splits (hJ.map (Int.castRingHom ℂ)).ne_zero
      (IsAlgClosed.splits _) r,
    natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]
lemma resultant_rootPowers_eq_comp_complex {f : ℂ[X]} (hf : f.Monic)
    (g : ℂ[X]) (r : ℕ) :
    resultant (polynomialRootPowers f r) g = resultant f (g.comp (X ^ r)) := by
  rw [resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    (polynomialRootPowers_complex_monic hf r).leadingCoeff, hf.leadingCoeff,
    polynomialRootPowers_complex_roots hf.ne_zero]
  simp [Multiset.map_map, Polynomial.eval_comp]
lemma resultant_rootPowers_eq_comp_int {J : ℤ[X]} (hJ : J.Monic)
    (Q : ℤ[X]) (r : ℕ) :
    resultant (polynomialRootPowers J r) Q = resultant J (Q.comp (X ^ r)) := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  apply hinj
  rw [← resultant_map_injective _ hinj, ← resultant_map_injective _ hinj,
    polynomialRootPowers_map _ hinj, Polynomial.map_comp,
    Polynomial.map_pow, Polynomial.map_X]
  exact resultant_rootPowers_eq_comp_complex (hJ.map _) _ r
lemma prime_pow_degree_dvd_rootPower_resultant {J : ℤ[X]} (hJ : J.Monic)
    {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ^ J.natDegree ∣ resultant (polynomialRootPowers J p) J := by
  rw [resultant_rootPowers_eq_comp_int hJ]
  exact prime_pow_degree_dvd_resultant_comp_X_pow hJ hp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma complex_roots_nodup_of_rational_irreducible {J : ℤ[X]}
    (hJ : Irreducible (J.map (Int.castRingHom ℚ))) :
    (J.map (Int.castRingHom ℂ)).roots.Nodup := by
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  rw [← heq]
  exact nodup_roots hJ.separable.map
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma polynomialRootPowers_prod_X_sub_C {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (r : ℕ) :
    polynomialRootPowers (∏ i, (X - C (x i))) r = ∏ i, (X - C (x i ^ r)) := by
  have hm : (∏ i, (X - C (x i))).Monic :=
    monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C _)
  have hr : (∏ i, (X - C (x i))).roots = Finset.univ.val.map x := by
    convert roots_multiset_prod_X_sub_C (Finset.univ.val.map x) using 1
    ·
      simp only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]
  rw [polynomialRootPowers_eq_prod, hm.leadingCoeff, one_pow, map_one, one_mul, hr]
  simp only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]
lemma exists_integer_root_family {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) :
    ∃ x : Fin J.natDegree → ℂ, Function.Injective x ∧
      (∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots) ∧
      J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i)) := by
  have h := exists_injective_complex_root_family (hJ.map (Int.castRingHom ℂ))
    (complex_roots_nodup_of_rational_irreducible hirr)
  rwa [hJ.natDegree_map] at h
lemma root_power_family_factorization {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (x : ι → ℂ)
    (hf : J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i))) (r : ℕ) :
    (polynomialRootPowers J r).map (Int.castRingHom ℂ) =
      ∏ i, (X - C (x i ^ r)) := by
  rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ)
    from Int.cast_injective), hf, polynomialRootPowers_prod_X_sub_C]
lemma root_power_family_injective {ι : Type*} {J : ℤ[X]} (x : ι → ℂ)
    (hx : Function.Injective x) (hmem : ∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots)
    {r : ℕ} (hr : ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ r = b ^ r → a = b) :
    Function.Injective (fun i ↦ x i ^ r) := by
  intro i j he
  exact hx (hr _ (hmem i) _ (hmem j) he)
lemma root_power_families_disjoint {ι : Type*} {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) (x : ι → ℂ)
    (hmem : ∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots)
    {r s : ℕ} (hrs : r ≠ s) (i j : ι) : x i ^ r ≠ x j ^ s := by
  intro he
  exact hrs (eq_exponents_of_noncyclotomic_complex_root_powers
    hJ hirr hconst hcyc (hmem i) (hmem j) he)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma option_prime_exponents_injective {ι : Type*} (p : ι → ℕ)
    (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime) :
    Function.Injective (fun t : Option ι ↦ t.elim 1 p) := by
  intro t u he
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some i => exact False.elim ((hp i).ne_one he.symm)
  | some i =>
    cases u with
    | none => exact False.elim ((hp i).ne_one he)
    | some j => exact congrArg some (hpinj he)
lemma root_power_pair_injective {ι β : Type*} {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) (r : ι → ℕ) (hr : Function.Injective r)
    (α : β → ℂ) (hα : Function.Injective α)
    (hmem : ∀ a, α a ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hsep : ∀ t, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ r t = b ^ r t → a = b) :
    Function.Injective (fun z : ι × β ↦ α z.2 ^ r z.1) := by
  rintro ⟨t, a⟩ ⟨u, b⟩ he
  have htu : t = u := hr (eq_exponents_of_noncyclotomic_complex_root_powers
    hJ hirr hconst hcyc (hmem a) (hmem b) he)
  subst u
  have hab : a = b := hα (hsep t _ (hmem a) _ (hmem b) he)
  subst b
  rfl
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma root_power_determinant_upper_bound {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (α : Fin J.natDegree → ℂ) (hα : Function.Injective α)
    (hmem : ∀ j, α j ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hfac : J.map (Int.castRingHom ℂ) = ∏ j, (X - C (α j)))
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree)) :
    ‖(confluentVandermonde (fun i ↦ α (e i).2.2 ^ ((e i).1.elim 1 p))).det‖ ≤
      (n : ℝ) ^ (J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι)) *
        (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ (n * (k + ∑ i, p i)) := by
  let w (t : Option ι) := t.elim k (fun _ ↦ 1)
  let r (t : Option ι) := t.elim 1 p
  let x (t : Option ι) (a : Fin J.natDegree) := α a ^ r t
  have hx : Function.Injective (fun z : Option ι × Fin J.natDegree ↦ x z.1 z.2) := by
    apply root_power_pair_injective hJ hirr hconst hcyc r
      (option_prime_exponents_injective p hpinj hp) α hα hmem
    intro t
    cases t with
    | none => simp [r]
    | some i => exact hsep i
  have hdim : n = J.natDegree * (k + Fintype.card ι) := by
    have h := (Fintype.card_congr e).trans (card_repeated_option_family k)
    simpa only [Fintype.card_fin] using h
  have hcount : (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      J.natDegree * (k ^ 2 + Fintype.card ι) := by
    simpa only [w, Fintype.card_fin, Fintype.sum_option, Option.elim_none,
      Option.elim_some, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_id] using sum_rootPrefixMultiplicity_repeated_le w x hx e
  have hexp : n + (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι) := by
    calc
      _ ≤ n + J.natDegree * (k ^ 2 + Fintype.card ι) := Nat.add_le_add_left hcount n
      _ = _ := by rw [hdim]; ring
  have hupper := norm_det_confluentVandermonde_le_power
    (fun i ↦ α (e i).2.2 ^ (e i).1.elim 1 p)
  rw [prod_max_norm_option_root_powers k p α hfac e, ← pow_mul,
    Nat.mul_comm (k + ∑ i, p i) n] at hupper
  exact hupper.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast hn) hexp)
    (pow_nonneg (mahlerMeasure_nonneg _) _))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma prod_symmetric_eq_lower_sq {ι M : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [CommMonoid M] (f : ι → ι → M) (hsym : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 1) :
    (∏ i, ∏ j, f i j) = (∏ i, ∏ j ∈ Finset.Iio i, f i j) ^ 2 := by
  classical
  have hf (i j : ι) : f i j =
      (if j < i then f i j else 1) * (if i < j then f i j else 1) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h]
  have he : (∏ i, ∏ j, if i < j then f i j else 1) =
      ∏ i, ∏ j, if j < i then f i j else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    (∏ i, ∏ j, f i j) = ∏ i, ∏ j,
        ((if j < i then f i j else 1) * (if i < j then f i j else 1)) := by
      exact Finset.prod_congr rfl (fun i _ ↦ Finset.prod_congr rfl (fun j _ ↦ hf i j))
    _ = (∏ i, ∏ j, if j < i then f i j else 1) *
        (∏ i, ∏ j, if i < j then f i j else 1) := by
      simp only [Finset.prod_mul_distrib]
    _ = (∏ i, ∏ j, if j < i then f i j else 1) ^ 2 := by rw [he, pow_two]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp only [← Finset.prod_filter]
      congr 1
      ext j
      simp
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open scoped BigOperators Classical
lemma norm_det_confluentVandermonde_sq {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ^ 2 =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [prod_symmetric_eq_lower_sq _
    (fun i j ↦ by
      by_cases h : x i = x j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev])
    (fun i ↦ by simp), det_confluentVandermonde, norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_prod, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : x j = x i
  · rw [if_neg (not_not_intro h), if_pos h.symm]
  · rw [if_pos h, if_neg (Ne.symm h)]
lemma norm_det_confluentVandermonde_sq_equiv {ι : Type*} [Fintype ι]
    {n : ℕ} (e : Fin n ≃ ι) (x : ι → ℂ) :
    ‖(confluentVandermonde (x ∘ e)).det‖ ^ 2 =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [norm_det_confluentVandermonde_sq]
  simp only [Function.comp_apply]
  calc
    _ = ∏ i : Fin n, ∏ j : ι,
        if x (e i) = x j then (1 : ℝ) else ‖x (e i) - x j‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact e.prod_comp (fun j : ι ↦ if x (e i) = x j then (1 : ℝ) else ‖x (e i) - x j‖)
    _ = _ := e.prod_comp (fun i : ι ↦ ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma prod_repeated_pairs {ι M : Type*} [Fintype ι] [CommMonoid M]
    {β : ι → Type*} [∀ t, Fintype (β t)] (w : ι → ℕ)
    (F : ∀ t, β t → ∀ u, β u → M) :
    (∏ i : (Σ t, Fin (w t) × β t), ∏ j : (Σ t, Fin (w t) × β t),
      F i.1 i.2.2 j.1 j.2.2) =
      ∏ t, ∏ u, (∏ a, ∏ b, F t a u b) ^ (w t * w u) := by
  simp only [Fintype.prod_sigma, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  apply Finset.prod_congr rfl
  intro t ht
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro u hu
  rw [Finset.prod_pow, ← pow_mul, Nat.mul_comm]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma nat_le_norm_intCast_of_dvd {a : ℕ} {z : ℤ} (hd : (a : ℤ) ∣ z) (hz : z ≠ 0) :
    (a : ℝ) ≤ ‖(z : ℂ)‖ := by
  have h := Int.natAbs_le_of_dvd_ne_zero hd hz
  have he : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [he]
  exact_mod_cast h
lemma one_le_norm_resultant_int {J Q : ℤ[X]}
    (hc : IsCoprime (J.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ))) :
    1 ≤ ‖resultant (J.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ))‖ := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hne := resultant_ne_zero _ _ hc
  rw [resultant_map_injective _ hinj] at hne ⊢
  have hz : resultant J Q ≠ 0 := by
    intro hz
    exact hne (by rw [hz, map_zero])
  simpa only [Int.coe_castRingHom, Nat.cast_one] using
    nat_le_norm_intCast_of_dvd (a := 1) (by simp) hz
lemma prime_pow_degree_le_norm_rootPower_resultant {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ J.natDegree ≤
      ‖resultant (polynomialRootPowers (J.map (Int.castRingHom ℂ)) p)
        (J.map (Int.castRingHom ℂ))‖ := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hc := rootPowers_isCoprime_of_distinct_exponents hJ hirr hconst hcyc hp.ne_one
  rw [polynomialRootPowers_one_complex (hJ.map _)] at hc
  have hne := resultant_ne_zero _ _ hc
  rw [← polynomialRootPowers_map _ hinj, resultant_map_injective _ hinj] at hne ⊢
  have hz : resultant (polynomialRootPowers J p) J ≠ 0 := by
    intro hz
    exact hne (by rw [hz, map_zero])
  have hd : ((p ^ J.natDegree : ℕ) : ℤ) ∣ resultant (polynomialRootPowers J p) J := by
    simpa only [Nat.cast_pow] using prime_pow_degree_dvd_rootPower_resultant hJ hp
  simpa only [Int.coe_castRingHom, Nat.cast_pow] using nat_le_norm_intCast_of_dvd hd hz
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma resultant_prod_X_sub_C {ι R : Type*} [Fintype ι] [CommRing R] [IsDomain R]
    (x : ι → R) (Q : R[X]) :
    resultant (∏ i, (X - C (x i))) Q = ∏ i, Q.eval (x i) := by
  rw [resultant_prod_left _ _ _ _ (by simp) le_rfl]
  simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl]
lemma norm_resultant_eq_root_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) {f g : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) (hg : g = ∏ j, (X - C (y j))) :
    ‖resultant f g‖ = ∏ i, ∏ j, ‖x i - y j‖ := by
  rw [hf, resultant_prod_X_sub_C, hg, norm_prod]
  simp only [eval_prod, eval_sub, eval_X, eval_C, norm_prod]
lemma eval_derivative_prod_X_sub_C {ι R : Type*} [Fintype ι] [CommRing R]
    (x : ι → R) (hx : Function.Injective x) (i : ι) :
    (derivative (∏ j, (X - C (x j)))).eval (x i) =
      ∏ j, if x i = x j then (1 : R) else x i - x j := by
  have hc : (Finset.univ.filter (fun j ↦ x j = x i)).card = 1 := by
    have he : Finset.univ.filter (fun j ↦ x j = x i) = {i} := by
      ext j
      simp [hx.eq_iff]
    rw [he, Finset.card_singleton]
  have h := hasseDeriv_prod_X_sub_C_eval_multiplicity Finset.univ x (x i)
  rw [hc, hasseDeriv_one, Finset.prod_filter] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases he : x j = x i
  · rw [if_neg (not_not_intro he), if_pos he.symm]
  · rw [if_pos he, if_neg (Ne.symm he)]
lemma norm_resultant_derivative_eq_root_product {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) {f : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) :
    ‖resultant f f.derivative‖ =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [hf, resultant_prod_X_sub_C, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [eval_derivative_prod_X_sub_C x hx, norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma norm_det_confluent_eq_resultant_product {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ t, Fintype (β t)] (w : ι → ℕ)
    (x : ∀ t, β t → ℂ) (f : ι → ℂ[X])
    (hf : ∀ t, f t = ∏ a, (X - C (x t a)))
    (hx : ∀ t, Function.Injective (x t))
    (hdisj : ∀ t u, t ≠ u → ∀ a b, x t a ≠ x u b)
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β t)) :
    ‖(confluentVandermonde (fun i ↦ x (e i).1 (e i).2.2)).det‖ ^ 2 =
      ∏ t, ∏ u, (if t = u then ‖resultant (f t) (f t).derivative‖
        else ‖resultant (f t) (f u)‖) ^ (w t * w u) := by
  have he := norm_det_confluentVandermonde_sq_equiv e (fun i ↦ x i.1 i.2.2)
  simp only [Function.comp_def] at he
  rw [he, prod_repeated_pairs w (fun t a u b ↦
      if x t a = x u b then (1 : ℝ) else ‖x t a - x u b‖)]
  apply Finset.prod_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro u hu
  congr 1
  by_cases htu : t = u
  · subst u
    rw [if_pos rfl, norm_resultant_derivative_eq_root_product _ (hx t) (hf t)]
  · rw [if_neg htu, norm_resultant_eq_root_product _ _ (hf t) (hf u)]
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    exact if_neg (hdisj t u htu a b)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma option_symmetric_prod_lower {ι : Type*} [Fintype ι]
    (A : Option ι → Option ι → ℝ) (hA : ∀ t u, 1 ≤ A t u)
    (hsym : ∀ t u, A t u = A u t) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ i, c i ≤ A (some i) none) :
    (∏ i, c i) ^ 2 ≤ ∏ t, ∏ u, A t u := by
  classical
  let B : Option ι → Option ι → ℝ := fun t u ↦
    match t, u with
    | none, some i => c i
    | some i, none => c i
    | _, _ => 1
  have hB0 (t u : Option ι) : 0 ≤ B t u := by
    cases t <;> cases u <;> simp [B, hc0]
  have hBA (t u : Option ι) : B t u ≤ A t u := by
    cases t with
    | none =>
      cases u with
      | none => exact hA _ _
      | some i => simpa only [B, hsym none (some i)] using hc i
    | some i =>
      cases u with
      | none => exact hc i
      | some j => exact hA _ _
  have h : (∏ t, ∏ u, B t u) ≤ ∏ t, ∏ u, A t u := Finset.prod_le_prod (fun t _ ↦ Finset.prod_nonneg (fun u _ ↦ hB0 t u))
    (fun t _ ↦ Finset.prod_le_prod (fun u _ ↦ hB0 t u) (fun u _ ↦ hBA t u))
  have he : (∏ t, ∏ u, B t u) = (∏ i, c i) ^ 2 := by
    simp [Fintype.prod_option, B, pow_two]
  rwa [he] at h
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma one_le_norm_derivative_resultant_of_integer_root_family
    {ι : Type*} [Fintype ι] (J : ℤ[X]) (x : ι → ℂ)
    (hx : Function.Injective x)
    (hJ : J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i))) :
    1 ≤ ‖resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative‖ := by
  have hpos : 0 < ‖resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative‖ := by
    rw [norm_resultant_derivative_eq_root_product x hx hJ]
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    split_ifs with he
    · exact zero_lt_one
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have he : resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative = ((resultant J J.derivative : ℤ) : ℂ) := by
    rw [derivative_map, resultant_map_injective _ hinj]
    rfl
  rw [he] at hpos ⊢
  have hz : resultant J J.derivative ≠ 0 := by
    intro hz
    simp only [hz, Int.cast_zero, norm_zero, lt_self_iff_false] at hpos
  simpa only [Nat.cast_one] using nat_le_norm_intCast_of_dvd (a := 1) (by simp) hz
lemma root_families_disjoint_of_isCoprime {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) {f g : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) (hg : g = ∏ j, (X - C (y j)))
    (hc : IsCoprime f g) (i : ι) (j : κ) : x i ≠ y j := by
  intro he
  have hfz : f.eval (x i) = 0 := by
    rw [hf, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hgz : g.eval (x i) = 0 := by
    rw [hg, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [he]
  have h := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mp hc (x i)
  exact h.elim (fun h ↦ h hfz) (fun h ↦ h hgz)
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma norm_resultant_comm (f g : ℂ[X]) : ‖resultant f g‖ = ‖resultant g f‖ := by
  rw [resultant_comm]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
lemma norm_det_confluent_ge_cross_product {ι : Type*} [Fintype ι]
    {β : Option ι → Type*} [∀ t, Fintype (β t)] (k : ℕ)
    (J : Option ι → ℤ[X]) (x : ∀ t, β t → ℂ)
    (hf : ∀ t, (J t).map (Int.castRingHom ℂ) = ∏ a, (X - C (x t a)))
    (hx : ∀ t, Function.Injective (x t))
    (hcop : ∀ t u, t ≠ u → IsCoprime ((J t).map (Int.castRingHom ℂ))
      ((J u).map (Int.castRingHom ℂ)))
    {n : ℕ} (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β t)) :
    (∏ i : ι, ‖resultant ((J (some i)).map (Int.castRingHom ℂ))
      ((J none).map (Int.castRingHom ℂ))‖) ^ (2 * k) ≤
      ‖(confluentVandermonde (fun i ↦ x (e i).1 (e i).2.2)).det‖ ^ 2 := by
  let f (t : Option ι) := (J t).map (Int.castRingHom ℂ)
  let w (t : Option ι) := t.elim k (fun _ ↦ 1)
  let A (t u : Option ι) : ℝ :=
    (if t = u then ‖resultant (f t) (f t).derivative‖
      else ‖resultant (f t) (f u)‖) ^ (w t * w u)
  have hA (t u : Option ι) : 1 ≤ A t u := by
    apply one_le_pow₀
    by_cases htu : t = u
    · subst u
      rw [if_pos rfl]
      exact one_le_norm_derivative_resultant_of_integer_root_family (J t) (x t) (hx t) (hf t)
    · rw [if_neg htu]
      exact one_le_norm_resultant_int (hcop t u htu)
  have hsym (t u : Option ι) : A t u = A u t := by
    by_cases htu : t = u
    · subst u; rfl
    · simp only [A, if_neg htu, if_neg (Ne.symm htu)]
      rw [norm_resultant_comm, Nat.mul_comm]
  have h := option_symmetric_prod_lower A hA hsym
    (fun i ↦ ‖resultant (f (some i)) (f none)‖ ^ k)
    (fun i ↦ pow_nonneg (norm_nonneg _) _)
    (fun i ↦ by simp [A, w])
  have he := norm_det_confluent_eq_resultant_product w x f hf hx
    (fun t u htu a b ↦ root_families_disjoint_of_isCoprime
      (x t) (x u) (hf t) (hf u) (hcop t u htu) a b) e
  rw [he]
  simpa only [Finset.prod_pow, ← pow_mul, Nat.mul_comm k 2, A, f] using h
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma root_power_determinant_lower_bound {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (α : Fin J.natDegree → ℂ) (hα : Function.Injective α)
    (hmem : ∀ j, α j ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hfac : J.map (Int.castRingHom ℂ) = ∏ j, (X - C (α j)))
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    (k : ℕ) {n : ℕ}
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree)) :
    (∏ i, (p i : ℝ)) ^ (2 * J.natDegree * k) ≤
      ‖(confluentVandermonde (fun i ↦
        α (e i).2.2 ^ ((e i).1.elim 1 p))).det‖ ^ 2 := by
  let r (t : Option ι) := t.elim 1 p
  let f (t : Option ι) := polynomialRootPowers J (r t)
  let x (t : Option ι) (a : Fin J.natDegree) := α a ^ r t
  have hr : Function.Injective r := by
    intro t u he
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some i => exact False.elim ((hp i).ne_one he.symm)
    | some i =>
      cases u with
      | none => exact False.elim ((hp i).ne_one he)
      | some j => exact congrArg some (hpinj he)
  have hf (t : Option ι) : (f t).map (Int.castRingHom ℂ) =
      ∏ a, (X - C (x t a)) := root_power_family_factorization α hfac (r t)
  have hx (t : Option ι) : Function.Injective (x t) := by
    cases t with
    | none => simpa only [x, r, Option.elim_none, pow_one] using hα
    | some i => exact root_power_family_injective α hα hmem (hsep i)
  have hcop (t u : Option ι) (htu : t ≠ u) :
      IsCoprime ((f t).map (Int.castRingHom ℂ)) ((f u).map (Int.castRingHom ℂ)) := by
    simp only [f, polynomialRootPowers_map _
      (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]
    exact rootPowers_isCoprime_of_distinct_exponents hJ hirr hconst hcyc
      (fun he ↦ htu (hr he))
  have hdet := norm_det_confluent_ge_cross_product k f x hf hx hcop e
  have hpbound (i : ι) : (p i : ℝ) ^ J.natDegree ≤
      ‖resultant ((f (some i)).map (Int.castRingHom ℂ))
        ((f none).map (Int.castRingHom ℂ))‖ := by
    change (p i : ℝ) ^ J.natDegree ≤
      ‖resultant ((polynomialRootPowers J (p i)).map (Int.castRingHom ℂ))
        ((polynomialRootPowers J 1).map (Int.castRingHom ℂ))‖
    rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ)
      from Int.cast_injective), polynomialRootPowers_map _
      (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
      polynomialRootPowers_one_complex (hJ.map _)]
    exact prime_pow_degree_le_norm_rootPower_resultant hJ hirr hconst hcyc (hp i)
  have hprod : (∏ i, (p i : ℝ) ^ J.natDegree) ≤
      ∏ i, ‖resultant ((f (some i)).map (Int.castRingHom ℂ))
        ((f none).map (Int.castRingHom ℂ))‖ :=
    Finset.prod_le_prod (fun i _ ↦ by positivity) (fun i _ ↦ hpbound i)
  have hpow := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ ↦ by positivity)) hprod (2 * k)
  rw [Finset.prod_pow, ← pow_mul] at hpow
  have he : J.natDegree * (2 * k) = 2 * J.natDegree * k := by ring
  rw [he] at hpow
  exact hpow.trans hdet
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma prime_family_mahler_power_inequality {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    {k : ℕ} (hk : 0 < k) :
    (∏ i, (p i : ℝ)) ^ (2 * J.natDegree * k) ≤
      (((J.natDegree * (k + Fintype.card ι) : ℕ) : ℝ) ^
          (J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι)) *
        (J.map (Int.castRingHom ℂ)).mahlerMeasure ^
          (J.natDegree * (k + Fintype.card ι) * (k + ∑ i, p i))) ^ 2 := by
  obtain ⟨α, hα, hmem, hfac⟩ := exists_integer_root_family hJ hirr
  let n := J.natDegree * (k + Fintype.card ι)
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hn : 1 ≤ n := Nat.mul_pos hd (Nat.add_pos_left hk _)
  have hc : Fintype.card (Σ t : Option ι,
      Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree) = n := by
    simpa only [Fintype.card_fin] using card_repeated_option_family (β := Fin J.natDegree) k
  let e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree) :=
    (Fintype.equivFinOfCardEq hc).symm
  have hl := root_power_determinant_lower_bound hJ hirr hconst hcyc p hpinj hp
    α hα hmem hfac hsep k e
  have hu := root_power_determinant_upper_bound hJ hirr hconst hcyc p hpinj hp
    α hα hmem hfac hsep k hn e
  exact hl.trans (pow_le_pow_left₀ (norm_nonneg _) hu 2)
lemma prime_family_mahler_log_inequality {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * (∑ i, Real.log (p i : ℝ)) ≤
      ((k : ℝ) ^ 2 + k + 2 * (Fintype.card ι : ℝ)) *
          Real.log ((J.natDegree : ℝ) * (k + (Fintype.card ι : ℝ))) +
        ((k : ℝ) + Fintype.card ι) * (k + ∑ i, (p i : ℝ)) *
          Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hd : 0 < (J.natDegree : ℝ) := by
    have h := hirr.natDegree_pos
    rw [hJ.natDegree_map] at h
    exact_mod_cast h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hprod : 0 < ∏ i, (p i : ℝ) :=
    Finset.prod_pos (fun i _ ↦ by exact_mod_cast (hp i).pos)
  have hM : 0 < (J.map (Int.castRingHom ℂ)).mahlerMeasure :=
    mahlerMeasure_pos_of_ne_zero (hJ.map _).ne_zero
  have hN : 0 < (J.natDegree : ℝ) * (k + (Fintype.card ι : ℝ)) := by positivity
  have hNcast : (0 : ℝ) < ((J.natDegree * (k + Fintype.card ι) : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using hN
  have hbound := prime_family_mahler_power_inequality hJ hirr hconst hcyc p hpinj hp hsep hk
  have hlog := Real.log_le_log (pow_pos hprod _) hbound
  simp only [Real.log_pow] at hlog
  rw [Real.log_mul (pow_ne_zero _ hNcast.ne') (pow_ne_zero _ hM.ne'), Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_prod (fun i _ ↦ by exact_mod_cast (hp i).ne_zero)] at hlog
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sum] at hlog
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * (J.natDegree : ℝ) by positivity)).mp
  convert! hlog using 1 <;> ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma primitiveRoot_mul_of_coprime {M : Type*} [CommMonoid M]
    {x y : M} {r s : ℕ} (hx : IsPrimitiveRoot x r) (hy : IsPrimitiveRoot y s)
    (hrs : r.Coprime s) : IsPrimitiveRoot (x * y) (r * s) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hc : (orderOf x).Coprime (orderOf y) := by
    rwa [← hx.eq_orderOf, ← hy.eq_orderOf]
  rw [(Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime hc,
    ← hx.eq_orderOf, ← hy.eq_orderOf]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma coprime_odd_or_odd {a b : ℕ} (h : a.Coprime b) : Odd a ∨ Odd b := by
  by_cases ha : Odd a
  · exact Or.inl ha
  · right
    have he : 2 ∣ a := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ha)
    exact (h.of_dvd_left he).odd_of_left
lemma order_le_totient_sq_with_odd (n : ℕ) :
    n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p e hp
    cases e with
    | zero => simp
    | succ e =>
      rw [Nat.totient_prime_pow_succ hp]
      have hx : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      by_cases hp2 : p = 2
      · subst p
        simp only [Nat.reduceSub, mul_one, pow_succ]
        constructor
        · nlinarith
        · intro ho
          have ht := Nat.odd_mul.mp ho
          norm_num at ht
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hs : p ≤ (p - 1) ^ 2 := by
          have he : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
          nlinarith
        have hx2 : p ^ e ≤ (p ^ e) ^ 2 := by nlinarith
        have hstrong : p ^ (e + 1) ≤ (p ^ e * (p - 1)) ^ 2 := by
          rw [pow_succ, mul_pow]
          exact Nat.mul_le_mul hx2 hs
        exact ⟨by omega, fun _ ↦ hstrong⟩
  · intro a b _ _ hab ha hb
    rw [Nat.totient_mul hab, mul_pow]
    constructor
    · rcases coprime_odd_or_odd hab with hoa | hob
      · have h := Nat.mul_le_mul (ha.2 hoa) hb.1
        nlinarith
      · have h := Nat.mul_le_mul ha.1 (hb.2 hob)
        nlinarith
    · intro ho
      exact Nat.mul_le_mul (ha.2 (Nat.odd_mul.mp ho).1) (hb.2 (Nat.odd_mul.mp ho).2)
lemma order_le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 :=
  (order_le_totient_sq_with_odd n).1
lemma odd_order_le_totient_sq {n : ℕ} (hn : Odd n) : n ≤ n.totient ^ 2 :=
  (order_le_totient_sq_with_odd n).2 hn
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
def polynomialRootRatios {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : F[X]) : Finset K := by
  classical
  exact ((P.aroots K).toFinset ×ˢ (P.aroots K).toFinset).image (fun ab ↦ ab.1 / ab.2)
lemma mem_polynomialRootRatios {F K : Type*} [Field F] [Field K] [Algebra F K]
    {P : F[X]} {z : K} : z ∈ polynomialRootRatios P ↔
      ∃ a ∈ P.rootSet K, ∃ b ∈ P.rootSet K, a / b = z := by
  classical
  rw [polynomialRootRatios, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, he⟩
lemma card_polynomialRootRatios_le {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : F[X]) : (polynomialRootRatios (K := K) P).card ≤ P.natDegree ^ 2 := by
  classical
  have hcard : (P.aroots K).toFinset.card ≤ P.natDegree :=
    (Multiset.toFinset_card_le _).trans P.card_roots_map_le_natDegree
  calc
    _ ≤ ((P.aroots K).toFinset ×ˢ (P.aroots K).toFinset).card := Finset.card_image_le
    _ = ((P.aroots K).toFinset.card) ^ 2 := by rw [Finset.card_product]; ring
    _ ≤ _ := Nat.pow_le_pow_left hcard 2
lemma algEquiv_map_mem_polynomialRootRatios {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {z : K}
    (hz : z ∈ polynomialRootRatios P) : σ z ∈ polynomialRootRatios P := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polynomialRootRatios.mp hz
  exact mem_polynomialRootRatios.mpr ⟨σ a, algEquiv_map_mem_rootSet σ ha,
    σ b, algEquiv_map_mem_rootSet σ hb, (map_div₀ σ a b).symm⟩
lemma primitiveRoots_subset_polynomialRootRatios {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    primitiveRoots r K ⊆ polynomialRootRatios P := by
  intro y hy
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_primitiveRoot hr hprim
    ((mem_primitiveRoots hr).mp hy)
  rw [← hσ]
  exact algEquiv_map_mem_polynomialRootRatios σ hz
lemma totient_le_degree_sq_of_primitive_root_ratio {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    r.totient ≤ P.natDegree ^ 2 := by
  rw [← hprim.card_primitiveRoots]
  exact (Finset.card_le_card (primitiveRoots_subset_polynomialRootRatios hr hz hprim)).trans
    (card_polynomialRootRatios_le P)
lemma order_le_two_degree_four_of_primitive_root_ratio {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    r ≤ 2 * P.natDegree ^ 4 := by
  have ht := totient_le_degree_sq_of_primitive_root_ratio hr hz hprim
  have hsq := Nat.pow_le_pow_left ht 2
  have ho := order_le_two_totient_sq r
  nlinarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
def HasRootRatioOrder {F : Type*} [Field F] (P : F[X]) (K : Type*) [Field K]
    [Algebra F K] (r : ℕ) : Prop :=
  ∃ z ∈ polynomialRootRatios (K := K) P, IsPrimitiveRoot z r
lemma hasRootRatioOrder_one {F K : Type*} [Field F] [Field K] [Algebra F K]
    {P : F[X]} (hconst : P.coeff 0 ≠ 0) (hne : (P.rootSet K).Nonempty) :
    HasRootRatioOrder P K 1 := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨1, mem_polynomialRootRatios.mpr ⟨a, ha, a, ha, ?_⟩, IsPrimitiveRoot.one⟩
  exact div_self (root_ne_zero_of_constant_ne_zero hconst ha)
lemma HasRootRatioOrder.mul_of_coprime {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {r s : ℕ}
    (hr : HasRootRatioOrder P K r) (hs : HasRootRatioOrder P K s)
    (hrs : r.Coprime s) : HasRootRatioOrder P K (r * s) := by
  obtain ⟨z, hz, hzr⟩ := hr
  obtain ⟨w, hw, hws⟩ := hs
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polynomialRootRatios.mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_polynomialRootRatios.mp hw
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_root hmonic hirr hc ha
  have hds := algEquiv_map_mem_rootSet σ hd
  have hs' : IsPrimitiveRoot (a / σ d) s := by
    simpa only [map_div₀, hσ] using hws.map_of_injective σ.injective
  have hm := primitiveRoot_mul_of_coprime hzr.inv hs' hrs
  have ha0 := root_ne_zero_of_constant_ne_zero hconst ha
  have hb0 := root_ne_zero_of_constant_ne_zero hconst hb
  have hd0 := root_ne_zero_of_constant_ne_zero hconst hds
  have he : (a / b)⁻¹ * (a / σ d) = b / σ d := by field_simp
  rw [he] at hm
  exact ⟨b / σ d, mem_polynomialRootRatios.mpr ⟨b, hb, σ d, hds, rfl⟩, hm⟩
lemma hasRootRatioOrder_prod_primes {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) (t : Finset ℕ)
    (hprime : ∀ p ∈ t, p.Prime) (horder : ∀ p ∈ t, HasRootRatioOrder P K p) :
    HasRootRatioOrder P K (∏ p ∈ t, p) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hasRootRatioOrder_one hconst hne
  | @insert p t hp ih =>
    rw [Finset.prod_insert hp]
    apply HasRootRatioOrder.mul_of_coprime hmonic hirr hconst
      (horder p (Finset.mem_insert_self _ _))
      (ih (fun q hq ↦ hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ horder q (Finset.mem_insert_of_mem hq)))
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes (hprime p (Finset.mem_insert_self _ _))
      (hprime q (Finset.mem_insert_of_mem hq))).mpr
    intro he
    exact hp (he ▸ hq)
lemma prime_bad_power_hasRootRatioOrder {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hconst : P.coeff 0 ≠ 0) {p : ℕ}
    (hp : p.Prime) (hbad : ¬ Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    HasRootRatioOrder P K p := by
  classical
  simp only [Set.InjOn, not_forall] at hbad
  obtain ⟨a, ha, b, hb, he, hne⟩ := hbad
  have hb0 := root_ne_zero_of_constant_ne_zero hconst hb
  refine ⟨a / b, mem_polynomialRootRatios.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
  apply isPrimitiveRoot_of_mem_nthRootsFinset hp
  · apply (mem_nthRootsFinset hp.pos 1).mpr
    rw [div_pow, he, div_self (pow_ne_zero _ hb0)]
  · intro h
    exact hne (((div_eq_iff hb0).mp h).trans (one_mul b))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
open scoped Topology
lemma tendsto_log_div_sqrt_atTop :
    Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [← Real.sqrt_eq_rpow] using h
lemma eventually_theta_ge_half_log_two_mul :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Tendsto (fun x : ℝ ↦ (Real.log 2 + Real.log 3) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).const_mul
        (Real.log 2 + Real.log 3)
  have hl : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hc.eventually_le_const (by positivity : 0 < Real.log 2 / 6),
    hl.eventually_le_const (by positivity : 0 < Real.log 2 / 6),
    tendsto_log_div_sqrt_atTop.eventually_le_const (by positivity : 0 < Real.log 2 / 12)]
    with x hx hcx hlx hsx
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hc' := (div_le_iff₀ hx0).mp hcx
  have hl' := (div_le_iff₀ hx0).mp hlx
  have hs' := (div_le_iff₀ hs0).mp hsx
  have hsbound : 2 * Real.sqrt x * Real.log x ≤ (Real.log 2 / 6) * x := by
    calc
      _ ≤ 2 * Real.sqrt x * ((Real.log 2 / 12) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = (Real.log 2 / 6) * (Real.sqrt x) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx0.le]
  have hshift : Real.log (x + 2) ≤ Real.log 3 + Real.log x := by
    have h := Real.log_le_log (by linarith : 0 < x + 2)
      (by linarith : x + 2 ≤ 3 * x)
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne'] at h
  have htheta := Chebyshev.theta_ge' hx
  nlinarith
lemma eventually_theta_eight_mul_sub_ge :
    ∀ᶠ x : ℝ in atTop, x ≤ Chebyshev.theta (8 * x) - Chebyshev.theta x := by
  have ht : Tendsto (fun x : ℝ ↦ 8 * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 8)).mpr tendsto_id
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    ht.eventually eventually_theta_ge_half_log_two_mul] with x hx hlower
  have hupper := Chebyshev.theta_le_log4_mul_x hx
  rw [hlog4] at hupper
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hx]
lemma exists_threshold_theta_eight_mul_sub_ge :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      x ≤ Chebyshev.theta (8 * x) - Chebyshev.theta x := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp eventually_theta_eight_mul_sub_ge
  exact ⟨max 1 x₀, le_max_left _ _, fun x hx ↦ hx₀ x ((le_max_right _ _).trans hx)⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
def primesInInterval (a b : ℕ) : Finset ℕ := Nat.primesLE b \ Nat.primesLE a
def primeIntervalProduct (a b : ℕ) : ℕ := ∏ p ∈ primesInInterval a b, p
lemma mem_primesInInterval {a b p : ℕ} :
    p ∈ primesInInterval a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp only [primesInInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hb, hp⟩, ha⟩
    exact ⟨hp, lt_of_not_ge (fun hpa ↦ ha ⟨hpa, hp⟩), hb⟩
  · rintro ⟨hp, ha, hb⟩
    exact ⟨⟨hb, hp⟩, by omega⟩
lemma primeIntervalProduct_pos (a b : ℕ) : 0 < primeIntervalProduct a b := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_primesInInterval.mp hp).1.pos
lemma log_primeIntervalProduct {a b : ℕ} (hab : a ≤ b) :
    Real.log (primeIntervalProduct a b : ℝ) =
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) := by
  rw [primeIntervalProduct, Nat.cast_prod, Real.log_prod]
  · rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hab)
  · intro p hp
    exact_mod_cast (mem_primesInInterval.mp hp).1.ne_zero
lemma primeIntervalProduct_dvd {a b B : ℕ}
    (hdiv : ∀ p ∈ primesInInterval a b, p ∣ B) : primeIntervalProduct a b ∣ B := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hne
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (mem_primesInInterval.mp hp).1
      (mem_primesInInterval.mp hq).1).mpr hne
  · exact hdiv
lemma exists_prime_in_interval_not_dvd {a b B : ℕ} (hB : 0 < B)
    (hprod : B < primeIntervalProduct a b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧ ¬ p ∣ B := by
  by_contra! h
  have hd : primeIntervalProduct a b ∣ B := primeIntervalProduct_dvd (fun p hp ↦
    h p (mem_primesInInterval.mp hp).1 (mem_primesInInterval.mp hp).2.1
      (mem_primesInInterval.mp hp).2.2)
  exact (not_lt_of_ge (Nat.le_of_dvd hB hd)) hprod
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
lemma eventually_exp_le_primeIntervalProduct :
    ∀ᶠ n : ℕ in atTop, Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ) := by
  filter_upwards [eventually_theta_eight_mul_sub_ge.natCast_atTop] with n hn
  have hp : (0 : ℝ) < (primeIntervalProduct n (8 * n) : ℝ) :=
    Nat.cast_pos.mpr (primeIntervalProduct_pos _ _)
  apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log hp)
  rw [log_primeIntervalProduct (by omega : n ≤ 8 * n)]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn
lemma exists_threshold_exp_le_primeIntervalProduct :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_exp_le_primeIntervalProduct
  exact ⟨max 1 n₀, le_max_left _ _, fun n hn ↦ hn₀ n ((le_max_right _ _).trans hn)⟩
lemma exists_prime_in_interval_not_dvd_of_log_lt {n B : ℕ} (hB : 0 < B)
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (B : ℝ) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧ ¬ p ∣ B := by
  apply exists_prime_in_interval_not_dvd hB
  have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hlt : (B : ℝ) < (primeIntervalProduct n (8 * n) : ℝ) := by
    calc
      _ = Real.exp (Real.log (B : ℝ)) := (Real.exp_log hBpos).symm
      _ < Real.exp (n : ℝ) := Real.exp_lt_exp.mpr hlog
      _ ≤ _ := hgrowth
  exact_mod_cast hlt
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma exists_prime_separating_root_powers_of_product_lt {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hlarge : 2 * P.natDegree ^ 4 < ∏ p ∈ t, p) :
    ∃ p ∈ t, Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  classical
  by_contra! hbad
  have horder : HasRootRatioOrder P K (∏ p ∈ t, p) :=
    hasRootRatioOrder_prod_primes hmonic hirr hconst hne t hprime
      (fun p hp ↦ prime_bad_power_hasRootRatioOrder hconst (hprime p hp) (hbad p hp))
  obtain ⟨z, hz, hprim⟩ := horder
  have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)
  exact (not_lt_of_ge (order_le_two_degree_four_of_primitive_root_ratio hpos hz hprim)) hlarge
lemma exists_prime_in_interval_separating_root_powers {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) {a b : ℕ}
    (hlarge : 2 * P.natDegree ^ 4 < primeIntervalProduct a b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧
      Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  obtain ⟨p, hp, hinj⟩ := exists_prime_separating_root_powers_of_product_lt
    hmonic hirr hconst hne (primesInInterval a b)
    (fun p hp ↦ (mem_primesInInterval.mp hp).1) hlarge
  exact ⟨p, (mem_primesInInterval.mp hp).1, (mem_primesInInterval.mp hp).2.1,
    (mem_primesInInterval.mp hp).2.2, hinj⟩
lemma exists_prime_separating_root_powers_of_log_lt {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hsplit : (P.map (algebraMap ℚ K)).Splits) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (P.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  apply exists_prime_in_interval_separating_root_powers hmonic hirr hconst
    (rootSet_nonempty_of_splits_of_irreducible hmonic hirr hsplit)
  have hd : (0 : ℝ) < (P.natDegree : ℝ) := Nat.cast_pos.mpr hirr.natDegree_pos
  have hlt : 2 * (P.natDegree : ℝ) ^ 4 < (primeIntervalProduct n (8 * n) : ℝ) := by
    calc
      _ = Real.exp (Real.log (2 * (P.natDegree : ℝ) ^ 4)) :=
        (Real.exp_log (by positivity)).symm
      _ < Real.exp (n : ℝ) := Real.exp_lt_exp.mpr hlog
      _ ≤ _ := hgrowth
  exact_mod_cast hlt
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_prime_separating_complex_roots_of_log_lt {P : ℚ[X]}
    (hmonic : P.Monic) (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (P.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      Set.InjOn (fun x : ℂ ↦ x ^ p) (P.rootSet ℂ) := by
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  obtain ⟨p, hp, hnp, hpn, hinj⟩ := exists_prime_separating_root_powers_of_log_lt
    (K := P.SplittingField) hmonic hirr hconst (SplittingField.splits P) hgrowth hlog
  refine ⟨p, hp, hnp, hpn, ?_⟩
  let j : P.SplittingField →ₐ[ℚ] ℂ := SplittingField.lift P (IsAlgClosed.splits _)
  have himage := (SplittingField.splits P).image_rootSet j
  intro z hz w hw he
  rw [← himage] at hz hw
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hw
  apply congrArg j
  apply hinj ha hb
  apply j.injective
  change j (a ^ p) = j (b ^ p)
  rw [map_pow, map_pow]
  exact he
lemma exists_prime_separating_integer_polynomial_roots_of_log_lt {J : ℤ[X]}
    (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hconst : J.coeff 0 ≠ 0) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (J.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ p = w ^ p → z = w := by
  have hconstQ : (J.map (Int.castRingHom ℚ)).coeff 0 ≠ 0 := by
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst
  have hlogQ : Real.log (2 * ((J.map (Int.castRingHom ℚ)).natDegree : ℝ) ^ 4) < n := by
    rwa [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective
      (Int.castRingHom ℚ))]
  obtain ⟨p, hp, hnp, hpn, hinj⟩ := exists_prime_separating_complex_roots_of_log_lt
    (hmonic.map _) hirr hconstQ hgrowth hlogQ
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  refine ⟨p, hp, hnp, hpn, ?_⟩
  intro z hz w hw he
  apply hinj ?_ ?_ he
  · change z ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
    rw [heq]
    exact Multiset.mem_toFinset.mpr hz
  · change w ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
    rw [heq]
    exact Multiset.mem_toFinset.mpr hw
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
def RootPowerSeparates (J : ℤ[X]) (p : ℕ) : Prop :=
  ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
    ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p = b ^ p → a = b
lemma prod_bad_root_power_primes_le {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic) (hirr : Irreducible P)
    (hconst : P.coeff 0 ≠ 0) (hne : (P.rootSet K).Nonempty)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    (∏ p ∈ t, p) ≤ 2 * P.natDegree ^ 4 := by
  have ho := hasRootRatioOrder_prod_primes hmonic hirr hconst hne t hprime
    (fun p hp ↦ prime_bad_power_hasRootRatioOrder hconst (hprime p hp) (hbad p hp))
  obtain ⟨z, hz, hprim⟩ := ho
  exact order_le_two_degree_four_of_primitive_root_ratio
    (Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)) hz hprim
lemma root_power_injOn_transfer {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] {P : F[X]}
    (hs : (P.map (algebraMap F K)).Splits) (j : K →ₐ[F] L) {p : ℕ}
    (hinj : Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    Set.InjOn (fun x : L ↦ x ^ p) (P.rootSet L) := by
  have himage := hs.image_rootSet j
  intro z hz w hw he
  rw [← himage] at hz hw
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hw
  apply congrArg j
  apply hinj ha hb
  apply j.injective
  change j (a ^ p) = j (b ^ p)
  rw [map_pow, map_pow]
  exact he
lemma prod_bad_complex_root_power_primes_le {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ Set.InjOn (fun x : ℂ ↦ x ^ p) (P.rootSet ℂ)) :
    (∏ p ∈ t, p) ≤ 2 * P.natDegree ^ 4 := by
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  apply prod_bad_root_power_primes_le (K := P.SplittingField) hmonic hirr hconst
    (rootSet_nonempty_of_splits_of_irreducible hmonic hirr (SplittingField.splits P)) t hprime
  intro p hp hinj
  exact hbad p hp (root_power_injOn_transfer (SplittingField.splits P)
    (SplittingField.lift P (IsAlgClosed.splits _)) hinj)
lemma prod_bad_integer_root_power_primes_le {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ RootPowerSeparates J p) :
    (∏ p ∈ t, p) ≤ 2 * J.natDegree ^ 4 := by
  have hconstQ : (J.map (Int.castRingHom ℚ)).coeff 0 ≠ 0 := by
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have h := prod_bad_complex_root_power_primes_le (hmonic.map _) hirr hconstQ t hprime
    (fun p hp hinj ↦ hbad p hp (fun a ha b hb he ↦ hinj
      (by change a ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
          rw [heq]; exact Multiset.mem_toFinset.mpr ha)
      (by change b ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
          rw [heq]; exact Multiset.mem_toFinset.mpr hb) he))
  rwa [hmonic.natDegree_map] at h
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma card_mul_log_lower_le_prime_weight {a b : ℕ} (ha : 0 < a) {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (t.card : ℝ) * Real.log (a : ℝ) ≤ ∑ p ∈ t, Real.log (p : ℝ) := by
  calc
    _ = ∑ _p ∈ t, Real.log (a : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun p hp ↦ Real.log_le_log (by exact_mod_cast ha)
      (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).2.1.le))
lemma prime_weight_le_card_mul_log_upper {a b : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ (t.card : ℝ) * Real.log (b : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ t, Real.log (b : ℝ) := Finset.sum_le_sum (fun p hp ↦
      Real.log_le_log (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).1.pos)
        (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).2.2))
    _ = _ := by simp
lemma sum_primes_le_card_mul_upper {a b : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (∑ p ∈ t, p) ≤ t.card * b := by
  calc
    _ ≤ ∑ _p ∈ t, b := Finset.sum_le_sum (fun p hp ↦ (mem_primesInInterval.mp (ht hp)).2.2)
    _ = _ := by simp
lemma prime_weight_le_sixteen_mul {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval n (8 * n)) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ 16 * (n : ℝ) := by
  have hsub : t ⊆ Nat.primesLE (8 * n) := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := mem_primesInInterval.mp (ht hp)
    exact Nat.mem_primesLE.mpr ⟨hhi, hprime⟩
  have hweight : (∑ p ∈ t, Real.log (p : ℝ)) ≤ Chebyshev.theta (8 * n : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hpt
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have htheta := Chebyshev.theta_le_log4_mul_x (by positivity : (0 : ℝ) ≤ (8 * n : ℕ))
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num at hlog2 ⊢
    linarith
  calc
    _ ≤ Chebyshev.theta (8 * n : ℕ) := hweight
    _ ≤ Real.log 4 * (8 * n : ℕ) := htheta
    _ ≤ 2 * (8 * n : ℕ) := mul_le_mul_of_nonneg_right hlog4 (by positivity)
    _ = _ := by push_cast; ring
lemma card_prime_family_le {n : ℕ} (hn : 1 < n) {t : Finset ℕ}
    (ht : t ⊆ primesInInterval n (8 * n)) :
    (t.card : ℝ) ≤ 16 * (n : ℝ) / Real.log (n : ℝ) := by
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))).mpr
  exact (card_mul_log_lower_le_prime_weight (by omega) ht).trans (prime_weight_le_sixteen_mul ht)
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
def goodRootPowerPrimes (J : ℤ[X]) (a b : ℕ) : Finset ℕ :=
  (primesInInterval a b).filter (RootPowerSeparates J)
lemma mem_goodRootPowerPrimes {J : ℤ[X]} {a b p : ℕ} :
    p ∈ goodRootPowerPrimes J a b ↔
      p.Prime ∧ a < p ∧ p ≤ b ∧ RootPowerSeparates J p := by
  simp only [goodRootPowerPrimes, Finset.mem_filter, mem_primesInInterval]
  tauto
lemma goodRootPowerPrimes_subset (J : ℤ[X]) (a b : ℕ) :
    goodRootPowerPrimes J a b ⊆ primesInInterval a b := Finset.filter_subset _ _
lemma sum_log_bad_root_power_primes_le {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ RootPowerSeparates J p) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (2 * (J.natDegree : ℝ) ^ 4) := by
  have hpos : (0 : ℝ) < ((∏ p ∈ t, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)
  have hbound : ((∏ p ∈ t, p : ℕ) : ℝ) ≤ 2 * (J.natDegree : ℝ) ^ 4 := by
    exact_mod_cast prod_bad_integer_root_power_primes_le hJ hirr hconst t hprime hbad
  have h := Real.log_le_log hpos hbound
  rw [Nat.cast_prod, Real.log_prod (fun p hp ↦ by exact_mod_cast (hprime p hp).ne_zero)] at h
  exact h
lemma good_root_power_prime_weight_lower {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    {n : ℕ} (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ)) :
    (n : ℝ) - Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤
      ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ) := by
  have hfull : (n : ℝ) ≤ ∑ p ∈ primesInInterval n (8 * n), Real.log (p : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hgrowth
    rw [Real.log_exp, primeIntervalProduct, Nat.cast_prod,
      Real.log_prod (fun p hp ↦ by exact_mod_cast (mem_primesInInterval.mp hp).1.ne_zero)] at h
    exact h
  have hbad := sum_log_bad_root_power_primes_le hJ hirr hconst
    ((primesInInterval n (8 * n)).filter (fun p ↦ ¬ RootPowerSeparates J p))
    (fun p hp ↦ (mem_primesInInterval.mp (Finset.mem_filter.mp hp).1).1)
    (fun p hp ↦ (Finset.mem_filter.mp hp).2)
  have he := Finset.sum_filter_add_sum_filter_not (primesInInterval n (8 * n))
    (RootPowerSeparates J) (fun p ↦ Real.log (p : ℝ))
  change _ ≤ ∑ p ∈ (primesInInterval n (8 * n)).filter (RootPowerSeparates J), Real.log (p : ℝ)
  linarith
lemma card_goodRootPowerPrimes_le (J : ℤ[X]) {n : ℕ} (hn : 1 < n) :
    ((goodRootPowerPrimes J n (8 * n)).card : ℝ) ≤
      16 * (n : ℝ) / Real.log (n : ℝ) :=
  card_prime_family_le hn (goodRootPowerPrimes_subset J n (8 * n))
lemma sum_goodRootPowerPrimes_le (J : ℤ[X]) (n : ℕ) :
    (∑ p ∈ goodRootPowerPrimes J n (8 * n), p) ≤
      (goodRootPowerPrimes J n (8 * n)).card * (8 * n) :=
  sum_primes_le_card_mul_upper (goodRootPowerPrimes_subset J n (8 * n))
lemma exists_threshold_good_root_power_prime_weight :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ n : ℕ, N ≤ n → Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 →
        (n : ℝ) / 2 ≤ ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ) := by
  obtain ⟨N, hN, hgrowth⟩ := exists_threshold_exp_le_primeIntervalProduct
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst n hn hlog
  have h := good_root_power_prime_weight_lower hJ hirr hconst
    (hgrowth n ((le_max_right _ _).trans hn))
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma one_le_norm_leadingCoeff_int_map {P : ℤ[X]} (hP : P ≠ 0) :
    1 ≤ ‖(P.map (Int.castRingHom ℂ)).leadingCoeff‖ := by
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, eq_intCast]
  norm_cast
  exact Int.one_le_abs (leadingCoeff_ne_zero.mpr hP)
lemma int_mahlerMeasure_le_of_dvd {J P : ℤ[X]} (hd : J ∣ P) (hP : P ≠ 0) :
    (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨R, rfl⟩ := hd
  have hR : R ≠ 0 := right_ne_zero_of_mul hP
  rw [Polynomial.map_mul, mahlerMeasure_mul]
  exact le_mul_of_one_le_right (mahlerMeasure_nonneg _)
    (one_le_mahlerMeasure_of_ne_zero hR)
lemma one_lt_mahlerMeasure_of_no_cyclotomic {J : ℤ[X]}
    (hdegree : 0 < J.natDegree) (hX : ¬ X ∣ J)
    (hcyclotomic : ¬ HasCyclotomicDivisor J) :
    1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hJ : J ≠ 0 := by intro h; simp [h] at hdegree
  have hle := one_le_mahlerMeasure_of_ne_zero hJ
  apply lt_of_le_of_ne hle
  intro heq
  exact hcyclotomic (cyclotomic_dvd_of_mahlerMeasure_eq_one heq.symm hX
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hdegree)))
lemma log_mahlerMeasure_pos_of_no_cyclotomic {J : ℤ[X]}
    (hdegree : 0 < J.natDegree) (hX : ¬ X ∣ J)
    (hcyclotomic : ¬ HasCyclotomicDivisor J) :
    0 < Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  exact Real.log_pos (one_lt_mahlerMeasure_of_no_cyclotomic hdegree hX hcyclotomic)
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial Filter
open scoped BigOperators Classical Topology
lemma quantitative_mahler_of_large_log_degree {N : ℕ}
    (hweight : ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ n : ℕ, N ≤ n → Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 →
        (n : ℝ) / 2 ≤ ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ))
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (hL : 1 ≤ Real.log (J.natDegree : ℝ))
    (hlog : 3040 ≤ Real.log (Real.log (J.natDegree : ℝ)))
    (hNL : (N : ℝ) ≤ Real.log (J.natDegree : ℝ)) :
    1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) ≤
      Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  let L := Real.log (J.natDegree : ℝ)
  let k : ℕ := ⌈L⌉₊
  let n : ℕ := ⌈L ^ 2 * Real.log L⌉₊
  let t := goodRootPowerPrimes J n (8 * n)
  obtain ⟨hklo, hkup, hnlo, hnup, hLn, hn1⟩ := mahler_parameter_ceil_bounds hL hlog
  have hk : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by dsimp [k, L]; linarith
    exact_mod_cast this
  have hnN : N ≤ n := by
    have : (N : ℝ) ≤ (n : ℝ) := hNL.trans hLn
    exact_mod_cast this
  have hn : 1 < n := by exact_mod_cast hn1
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hdreal : 0 < (J.natDegree : ℝ) := by exact_mod_cast hd
  have hbad : Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 :=
    mahler_bad_prime_log_budget hdreal rfl hL hlog hnlo
  have hw : (n : ℝ) / 2 ≤ ∑ p ∈ t, Real.log (p : ℝ) :=
    hweight hJ hirr hconst n hnN hbad
  have hlog1 : 1 ≤ Real.log L := by dsimp [L]; linarith
  have hs : (t.card : ℝ) ≤ 16 * L ^ 2 :=
    mahler_prime_card_budget hL hlog1 hnlo hnup (card_goodRootPowerPrimes_le J hn)
  have hsum : (∑ p ∈ t, (p : ℝ)) ≤ (t.card : ℝ) * (8 * (n : ℝ)) := by
    have h : ((∑ p ∈ t, p : ℕ) : ℝ) ≤ ((t.card * (8 * n) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (sum_goodRootPowerPrimes_le J n)
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h
  have hS : (∑ p ∈ t, (p : ℝ)) ≤ 256 * L ^ 4 * Real.log L :=
    mahler_prime_sum_budget hL hlog1 hnup (Nat.cast_nonneg _) hs hsum
  have hd1 : (1 : ℝ) ≤ J.natDegree := by exact_mod_cast hd
  obtain ⟨hB, hBup⟩ := mahler_node_log_budget hd1 rfl hL hklo hkup (Nat.cast_nonneg _) hs
  have hp : ∀ p : t, (p : ℕ).Prime :=
    fun p ↦ (mem_goodRootPowerPrimes.mp p.property).1
  have hsep : ∀ p : t, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ (p : ℕ) = b ^ (p : ℕ) → a = b :=
    fun p ↦ (mem_goodRootPowerPrimes.mp p.property).2.2.2
  have hmain := prime_family_mahler_log_inequality hJ hirr hconst hcyc
    (fun p : t ↦ (p : ℕ)) Subtype.val_injective hp hsep hk
  have hwcoe : (∑ p : t, Real.log ((p : ℕ) : ℝ)) = ∑ p ∈ t, Real.log (p : ℝ) := by
    exact Finset.sum_coe_sort t (fun p : ℕ ↦ Real.log (p : ℝ))
  rw [hwcoe] at hmain
  simp only [Fintype.card_coe, Finset.sum_coe_sort] at hmain
  have hlower : (k : ℝ) * (n : ℝ) / 2 ≤ (k : ℝ) * ∑ p ∈ t, Real.log (p : ℝ) := by
    have := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  exact mahler_log_lower_of_parameter_budget hL hlog hklo hkup hnlo
    (Nat.cast_nonneg _) hs hS hB hBup
    (Real.log_nonneg (one_le_mahlerMeasure_of_ne_zero hJ.ne_zero)) (hlower.trans hmain)
lemma exists_threshold_quantitative_mahler_large_degree :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      (¬ HasCyclotomicDivisor J) → D ≤ J.natDegree →
        1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) ≤
          Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨N, _hN, hw⟩ := exists_threshold_good_root_power_prime_weight
  have ht : Tendsto (fun d : ℕ ↦ Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htt : Tendsto (fun d : ℕ ↦ Real.log (Real.log (d : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp ht
  have he : ∀ᶠ d : ℕ in atTop, 2 ≤ d ∧ 1 ≤ Real.log (d : ℝ) ∧
      3040 ≤ Real.log (Real.log (d : ℝ)) ∧ (N : ℝ) ≤ Real.log (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop 1,
      htt.eventually_ge_atTop 3040, ht.eventually_ge_atTop (N : ℝ)] with d hd hl hll hn
    exact ⟨hd, hl, hll, hn⟩
  obtain ⟨D, hD⟩ := eventually_atTop.mp he
  refine ⟨max 2 D, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst hcyc hdeg
  obtain ⟨_, hl, hll, hn⟩ := hD J.natDegree ((le_max_right _ _).trans hdeg)
  exact quantitative_mahler_of_large_log_degree hw hJ hirr hconst hcyc hl hll hn
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped NNReal
lemma exists_pos_le_on_finite {α : Type*} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (hpos : ∀ a ∈ s, 0 < f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ s, ε ≤ f a := by
  by_cases hn : s.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image s f hs hn
    exact ⟨f a, hpos a ha, hmin⟩
  · exact ⟨1, zero_lt_one, fun a ha ↦ (hn ⟨a, ha⟩).elim⟩
lemma exists_pos_log_mahler_gap_bounded_degree (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ J : ℤ[X], J.natDegree ≤ d →
      1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure →
      ε ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  let s : Set ℤ[X] := {J | J.natDegree ≤ d ∧
    (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure}
  have hs : s.Finite := (finite_mahlerMeasure_le d (2 : ℝ≥0)).subset
    (fun J h ↦ ⟨h.1, h.2.1⟩)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_on_finite hs
    (fun J ↦ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure)
    (fun _ h ↦ Real.log_pos h.2.2)
  refine ⟨min δ (Real.log 2), lt_min hδ (Real.log_pos (by norm_num)), ?_⟩
  intro J hdeg hM
  by_cases hsmall : (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2
  · exact (min_le_left _ _).trans (hδle J ⟨hdeg, hsmall, hM⟩)
  · exact (min_le_right _ _).trans (Real.log_le_log (by norm_num) (le_of_not_ge hsmall))
lemma exists_pos_noncyclotomic_log_mahler_gap_bounded_degree (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ J : ℤ[X], 0 < J.natDegree → J.natDegree ≤ d →
      (¬ X ∣ J) → (¬ HasCyclotomicDivisor J) →
      ε ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨ε, hε, hgap⟩ := exists_pos_log_mahler_gap_bounded_degree d
  exact ⟨ε, hε, fun J hpos hdeg hX hcyc ↦
    hgap J hdeg (one_lt_mahlerMeasure_of_no_cyclotomic hpos hX hcyc)⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial Filter
open scoped Topology
lemma exists_uniform_quantitative_log_mahler_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      (¬ HasCyclotomicDivisor J) → ∀ n : ℕ, N ≤ n → J.natDegree ≤ n →
        c / Real.log (n : ℝ) ^ 3 ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨D, hD, hlarge⟩ := exists_threshold_quantitative_mahler_large_degree
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_noncyclotomic_log_mahler_gap_bounded_degree D
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨min (1 / 18576) ε, lt_min (by norm_num) hε, max 2 N, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst hcyc n hn hdn
  have hlogn : 1 ≤ Real.log (n : ℝ) := hN n ((le_max_right _ _).trans hn)
  have hlogn0 : 0 < Real.log (n : ℝ) := by linarith
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  by_cases hbig : D ≤ J.natDegree
  · have hd2 : 2 ≤ J.natDegree := hD.trans hbig
    have hlogd : 0 < Real.log (J.natDegree : ℝ) := Real.log_pos (by exact_mod_cast hd2)
    have hlogs : Real.log (J.natDegree : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdn)
    calc
      min (1 / 18576) ε / Real.log (n : ℝ) ^ 3 ≤
          (1 / 18576) / Real.log (n : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (1 / 18576) / Real.log (J.natDegree : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ hlogd.le hlogs 3)
      _ = 1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) := by rw [div_div]
      _ ≤ _ := hlarge hJ hirr hconst hcyc hbig
  · have hX : ¬ X ∣ J := fun h ↦ hconst (X_dvd_iff.mp h)
    have hgap := hsmall J hd (by omega) hX hcyc
    apply le_trans _ hgap
    apply (div_le_iff₀ (pow_pos hlogn0 3)).mpr
    exact (min_le_right _ _).trans
      (le_mul_of_one_le_right hε.le (one_le_pow₀ hlogn))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma logarithmic_prime_scale_ge {C K L D : ℝ} (hC : 0 ≤ C) (hK : 2 * C ≤ K)
    (hL : 1 ≤ L) (hD : D ≤ L) : C * (1 + D) ≤ K * L ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  calc
    C * (1 + D) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = (2 * C) * L := by ring
    _ ≤ K * L := mul_le_mul_of_nonneg_right hK (by linarith)
    _ ≤ K * L ^ 4 := mul_le_mul_of_nonneg_left
      (by simpa using pow_le_pow_right₀ hL (show 1 ≤ 4 by norm_num)) hK0
lemma log_lt_prime_mul_log_of_mahler_gap {c K L M : ℝ} (hc : 0 < c)
    (hK : 1 / c ≤ K) (hL : 1 ≤ L) {q : ℕ} (hq : K * L ^ 4 < (q : ℝ))
    (hM : c / L ^ 3 ≤ Real.log M) : L < (q : ℝ) * Real.log M := by
  have hL0 : 0 < L := by linarith
  have hKc : 1 ≤ K * c := (div_le_iff₀ hc).mp hK
  have heq : (K * L ^ 4) * (c / L ^ 3) = (K * c) * L := by
    field_simp
  calc
    L ≤ (K * c) * L := by nlinarith
    _ = (K * L ^ 4) * (c / L ^ 3) := heq.symm
    _ < (q : ℝ) * (c / L ^ 3) := mul_lt_mul_of_pos_right hq (by positivity)
    _ ≤ (q : ℝ) * Real.log M := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_uniform_logarithmic_root_power_prime :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℤ[X], J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ s : ℝ, C * (1 + Real.log (J.natDegree : ℝ)) ≤ s →
      ∃ p : ℕ, p.Prime ∧ s < (p : ℝ) ∧ (p : ℝ) ≤ 16 * s ∧
        ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
        ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ p = w ^ p → z = w := by
  obtain ⟨n₀, hn₀, hgrowth⟩ := exists_threshold_exp_le_primeIntervalProduct
  refine ⟨max 5 (n₀ : ℝ), by positivity, ?_⟩
  intro J hmonic hirr hconst s hs
  have hdegree : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rw [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective
      (Int.castRingHom ℚ))] at h
    exact h
  have hd : (0 : ℝ) < (J.natDegree : ℝ) := Nat.cast_pos.mpr hdegree
  have hlogd : 0 ≤ Real.log (J.natDegree : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hdegree)
  have hC : (5 : ℝ) ≤ max 5 (n₀ : ℝ) := le_max_left _ _
  have hN : (n₀ : ℝ) ≤ max 5 (n₀ : ℝ) := le_max_right _ _
  have hsC : max 5 (n₀ : ℝ) ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hn : n₀ ≤ ⌈s⌉₊ := by exact_mod_cast hN.trans (hsC.trans hceil)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log (2 * (J.natDegree : ℝ) ^ 4) < (⌈s⌉₊ : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hd.ne'), Real.log_pow]
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (by linarith : 0 ≤ 1 + Real.log (J.natDegree : ℝ))]
  obtain ⟨p, hp, hnp, hpn, hsep⟩ :=
    exists_prime_separating_integer_polynomial_roots_of_log_lt
      hmonic hirr hconst (hgrowth _ hn) hlog
  refine ⟨p, hp, hceil.trans_lt (by exact_mod_cast hnp), ?_, hsep⟩
  have hceilupper := Nat.ceil_lt_add_one hs0
  have hpn' : (p : ℝ) ≤ 8 * (⌈s⌉₊ : ℝ) := by exact_mod_cast hpn
  nlinarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma IsBinary.norm_coeff_sub_le_one {P Q : ℤ[X]} (hP : IsBinary P)
    (hQ : IsBinary Q) (k : ℕ) :
    ‖((P - Q).map (Int.castRingHom ℂ)).coeff k‖ ≤ 1 := by
  rcases hP k with hp | hp <;> rcases hQ k with hq | hq <;>
    simp [coeff_map, coeff_sub, hp, hq]
lemma coeff_wordPolynomial_sub_outside {m : ℕ} (v w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (wordPolynomial v - wordPolynomial w).coeff k = 0 := by
  rw [coeff_sub]
  rcases hk with rfl | hk
  · simp only [coeff_wordPolynomial_zero, sub_self]
  · by_cases ht : k = m + 1
    · subst k
      simp only [coeff_wordPolynomial_top, sub_self]
    · rw [coeff_wordPolynomial_above v (by omega),
        coeff_wordPolynomial_above w (by omega), sub_self]
lemma support_wordPolynomial_sub_map_subset {m : ℕ} (v w : Fin m → Bool) :
    ((wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)).support ⊆
      Finset.Icc 1 m := by
  intro k hk
  by_contra h
  have hout : k = 0 ∨ m < k := by simp only [Finset.mem_Icc] at h; omega
  have hz := coeff_wordPolynomial_sub_outside v w k hout
  exact (mem_support_iff.mp hk) (by simp only [coeff_map, hz, map_zero])
lemma mahlerMeasure_wordPolynomial_sub_le {m : ℕ} (v w : Fin m → Bool) :
    ((wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)).mahlerMeasure ≤
      Real.sqrt (m : ℝ) := by
  classical
  let P := (wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)
  have hc (k : ℕ) : ‖P.coeff k‖ ^ 2 ≤ (1 : ℝ) := by
    have h := (wordPolynomial_endpoints v).binary.norm_coeff_sub_le_one
      (wordPolynomial_endpoints w).binary k
    change ‖P.coeff k‖ ≤ 1 at h
    nlinarith [norm_nonneg (P.coeff k)]
  have hcard : P.support.card ≤ m := by
    have h := Finset.card_le_card (support_wordPolynomial_sub_map_subset v w)
    simpa [P, Nat.card_Icc] using h
  calc
    P.mahlerMeasure ≤ Real.sqrt (∑ k ∈ P.support, ‖P.coeff k‖ ^ 2) :=
      mahlerMeasure_le_sqrt_sum_sq_norm_coeff P
    _ ≤ Real.sqrt (∑ _k ∈ P.support, (1 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun k _ ↦ hc k)
    _ = Real.sqrt (P.support.card : ℝ) := by simp
    _ ≤ Real.sqrt (m : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcard
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma expand_contract_of_coeff_eq_zero {R : Type*} [CommSemiring R]
    {q : ℕ} (hq : 0 < q) (P : R[X])
    (hs : ∀ k, ¬ q ∣ k → P.coeff k = 0) :
    expand R q (contract q P) = P := by
  ext k
  rw [coeff_expand hq, coeff_contract (ne_of_gt hq)]
  split_ifs with hk
  · rw [Nat.div_mul_cancel hk]
  · exact (hs k hk).symm
lemma coeff_wordPolynomial_sub_eq_zero_of_not_dvd {m q : ℕ}
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i)
    {k : ℕ} (hk : ¬ q ∣ k) :
    (wordPolynomial v - wordPolynomial w).coeff k = 0 := by
  by_cases hout : k = 0 ∨ m < k
  · exact coeff_wordPolynomial_sub_outside v w k hout
  · have hkpos : 0 < k := by omega
    have hkle : k ≤ m := by omega
    let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [coeff_sub, ← hi, coeff_wordPolynomial_internal, coeff_wordPolynomial_internal]
    rw [hfixed i (by simpa only [hi] using hk), sub_self]
lemma sparse_word_difference_expand {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) :
    expand ℤ q (contract q (wordPolynomial v - wordPolynomial w)) =
      wordPolynomial v - wordPolynomial w := by
  exact expand_contract_of_coeff_eq_zero hq _
    (fun _ hk ↦ coeff_wordPolynomial_sub_eq_zero_of_not_dvd v w hfixed hk)
lemma sparse_word_difference_contract_ne_zero {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) (hne : v ≠ w) :
    contract q (wordPolynomial v - wordPolynomial w) ≠ 0 := by
  intro hzero
  have heq := sparse_word_difference_expand hq v w hfixed
  rw [hzero, map_zero] at heq
  exact hne (wordPolynomial_injective (sub_eq_zero.mp heq.symm))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma norm_coeff_contract_word_difference_le_one {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) (k : ℕ) :
    ‖((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).coeff k‖ ≤ 1 := by
  have h := (wordPolynomial_endpoints v).binary.norm_coeff_sub_le_one
    (wordPolynomial_endpoints w).binary (k * q)
  simpa only [coeff_map, coeff_contract (ne_of_gt hq)] using h
lemma support_contract_word_difference_map_subset {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) :
    ((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).support ⊆ Finset.Icc 1 (m / q) := by
  intro k hk
  have hn : (wordPolynomial v - wordPolynomial w).coeff (k * q) ≠ 0 := by
    intro hz
    exact (mem_support_iff.mp hk) (by
      simp only [coeff_map, coeff_contract (ne_of_gt hq), hz, map_zero])
  have hkpos : 1 ≤ k := by
    by_contra h
    have heq : k = 0 := by omega
    apply hn
    exact coeff_wordPolynomial_sub_outside v w (k * q) (Or.inl (by simp [heq]))
  have hbound : k * q ≤ m := by
    by_contra h
    exact hn (coeff_wordPolynomial_sub_outside v w (k * q) (Or.inr (by omega)))
  exact Finset.mem_Icc.mpr ⟨hkpos, (Nat.le_div_iff_mul_le hq).mpr hbound⟩
lemma mahlerMeasure_contract_word_difference_le {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) :
    ((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).mahlerMeasure ≤ Real.sqrt ((m / q : ℕ) : ℝ) := by
  classical
  let P := (contract q (wordPolynomial v - wordPolynomial w)).map (Int.castRingHom ℂ)
  have hc (k : ℕ) : ‖P.coeff k‖ ^ 2 ≤ (1 : ℝ) := by
    have h := norm_coeff_contract_word_difference_le_one hq v w k
    change ‖P.coeff k‖ ≤ 1 at h
    nlinarith [norm_nonneg (P.coeff k)]
  have hcard : P.support.card ≤ m / q := by
    have h := Finset.card_le_card (support_contract_word_difference_map_subset hq v w)
    simpa [P, Nat.card_Icc] using h
  calc
    P.mahlerMeasure ≤ Real.sqrt (∑ k ∈ P.support, ‖P.coeff k‖ ^ 2) :=
      mahlerMeasure_le_sqrt_sum_sq_norm_coeff P
    _ ≤ Real.sqrt (∑ _k ∈ P.support, (1 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun k _ ↦ hc k)
    _ = Real.sqrt (P.support.card : ℝ) := by simp
    _ ≤ Real.sqrt ((m / q : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcard
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma word_eq_of_sparse_divisibility {m q : ℕ} (hq : 0 < q) {J : ℤ[X]}
    (hJ : J.Monic) (hsimple : (J.map (Int.castRingHom ℂ)).roots.Nodup)
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q)
    (v w : Fin m → Bool) (hv : J ∣ wordPolynomial v) (hw : J ∣ wordPolynomial w)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) : v = w := by
  by_contra hne
  let R := contract q (wordPolynomial v - wordPolynomial w)
  have hR : R ≠ 0 := sparse_word_difference_contract_ne_zero hq v w hfixed hne
  have hd : J ∣ expand ℤ q R := by
    rw [sparse_word_difference_expand hq v w hfixed]
    exact dvd_sub hv hw
  have hmap : J.map (Int.castRingHom ℂ) ∣ expand ℂ q (R.map (Int.castRingHom ℂ)) := by
    simpa only [map_expand] using Polynomial.map_dvd (Int.castRingHom ℂ) hd
  have hlow := mahlerMeasure_pow_le_of_dvd_expand q (hJ.map _)
    (one_le_norm_leadingCoeff_int_map hR) hsimple hsep hmap
  have hupp := mahlerMeasure_contract_word_difference_le hq v w
  exact (not_lt_of_ge (hlow.trans hupp)) hlarge
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma card_sparse_internal_positions (m q : ℕ) :
    Nat.card {i : Fin m // q ∣ i.val + 1} = m / q := by
  rw [Nat.card_eq_fintype_card]
  let s : Finset ℕ := (Finset.range m).filter (fun k ↦ q ∣ k + 1)
  let e : {i : Fin m // q ∣ i.val + 1} ≃ s :=
    { toFun := fun i ↦ ⟨i.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr i.val.isLt, i.property⟩⟩
      invFun := fun k ↦ ⟨⟨k.val, Finset.mem_range.mp (Finset.mem_filter.mp k.property).1⟩,
        (Finset.mem_filter.mp k.property).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    _ = Fintype.card s :=
      Fintype.card_congr e
    _ = m / q := by simpa only [Fintype.card_coe] using Nat.card_multiples m q
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators Classical
lemma uniformProbability_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (E : ∀ i, α i → Prop) :
    uniformProbability (fun w : ∀ i, α i ↦ ∀ i, E i (w i)) =
      ∏ i, uniformProbability (E i) := by
  classical
  let e : (∀ i, {a : α i // E i a}) ≃ {w : ∀ i, α i // ∀ i, E i (w i)} :=
    { toFun := fun w ↦ ⟨fun i ↦ (w i).val, fun i ↦ (w i).property⟩
      invFun := fun w i ↦ ⟨w.val i, w.property i⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc := Fintype.card_congr e
  unfold uniformProbability
  simp only [← Fintype.card_subtype]
  rw [← hc, Fintype.card_pi, Fintype.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]
lemma uniformProbability_pi_eq_le {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc : ∀ i y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (y : ∀ i, β i) :
    uniformProbability (fun w : ∀ i, α i ↦ ∀ i, f i (w i) = y i) ≤ ∏ i, c i := by
  rw [uniformProbability_pi (fun i a ↦ f i a = y i)]
  exact Finset.prod_le_prod (fun _ _ ↦ uniformProbability_nonneg _)
    (fun i _ ↦ hc i (y i))
lemma uniformProbability_fiber_unique_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [Nonempty γ] {α β : ι → Type*} [∀ i, Fintype (α i)]
    (E : γ → (∀ i, α i) → Prop) (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (hunique : ∀ x w v, E x w → E x v → ∀ i, f i (w i) = f i (v i)) :
    uniformProbability (fun v : γ × (∀ i, α i) ↦ E v.1 v.2) ≤ ∏ i, c i := by
  classical
  rw [uniformProbability_product_eq_average]
  calc
    _ ≤ uniformAverage (fun _ : γ ↦ ∏ i, c i) := by
      apply uniformAverage_mono
      intro x
      by_cases he : ∃ v, E x v
      · obtain ⟨v, hv⟩ := he
        calc
          _ ≤ uniformProbability (fun w : ∀ i, α i ↦ ∀ i, f i (w i) = f i (v i)) :=
            uniformProbability_mono (fun w hw ↦ hunique x w v hw hv)
          _ ≤ _ := uniformProbability_pi_eq_le f c hc (fun i ↦ f i (v i))
      · have hf : E x = (fun _ ↦ False) := by
          funext w
          exact propext ⟨fun hw ↦ he ⟨w, hw⟩, False.elim⟩
        rw [hf, uniformProbability_false]
        exact Finset.prod_nonneg (fun i _ ↦ hc0 i)
    _ = _ := uniformAverage_const _
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators Classical
lemma uniformProbability_selected_coordinates_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (s : ι → Prop) (E : (∀ i, α i) → Prop)
    (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc0 : ∀ i, s i → 0 ≤ c i)
    (hc : ∀ i, s i → ∀ y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (hunique : ∀ w v, E w → E v → (∀ i, ¬s i → w i = v i) →
      ∀ i, s i → f i (w i) = f i (v i)) :
    uniformProbability E ≤ ∏ i : {i : ι // s i}, c i.val := by
  letI : DecidableEq {i : ι // s i} := Classical.decEq _
  letI : DecidableEq {i : ι // ¬s i} := Classical.decEq _
  let γ := ∀ i : {i : ι // ¬s i}, α i.val
  let δ := ∀ i : {i : ι // s i}, α i.val
  let e : (∀ i, α i) ≃ γ × δ :=
    (Equiv.piEquivPiSubtypeProd s α).trans (Equiv.prodComm _ _)
  calc
    _ = uniformProbability (fun v : γ × δ ↦ E (e.symm v)) :=
      (uniformProbability_equiv (α := γ × δ) (β := ∀ i, α i) e.symm E).symm
    _ ≤ _ := by
      apply uniformProbability_fiber_unique_le
        (fun x w ↦ E (e.symm (x, w)))
        (fun (i : {i : ι // s i}) ↦ f i.val) (fun i ↦ c i.val)
        (fun i ↦ hc0 i.val i.property) (fun i ↦ hc i.val i.property)
      intro x w v hw hv i
      have h := hunique (e.symm (x, w)) (e.symm (x, v)) hw hv
        (fun j hj ↦ by simp [e, Equiv.piEquivPiSubtypeProd, hj]) i.val i.property
      simpa [e, Equiv.piEquivPiSubtypeProd, i.property] using h
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma uniformProbability_bool_eq (b : Bool) :
    uniformProbability (fun a : Bool ↦ a = b) = (1 / 2 : ℝ) := by
  letI : DecidablePred (fun a : Bool ↦ a = b) := fun _ ↦ Classical.propDecidable _
  have hfilter : Finset.univ.filter (fun a : Bool ↦ a = b) = {b} := by
    ext a
    simp
  rw [uniformProbability, hfilter]
  norm_num
lemma binaryProbability_divisible_le_sparse {m q : ℕ} (hq : 0 < q) {J : ℤ[X]}
    (hJ : J.Monic) (hsimple : (J.map (Int.castRingHom ℂ)).roots.Nodup)
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q) :
    binaryProbability m (fun P ↦ J ∣ P) ≤ (1 / 2 : ℝ) ^ (m / q) := by
  letI : DecidablePred (fun i : Fin m ↦ q ∣ i.val + 1) :=
    fun _ ↦ Classical.propDecidable _
  calc
    _ ≤ ∏ _i : {i : Fin m // q ∣ i.val + 1}, (1 / 2 : ℝ) := by
      apply uniformProbability_selected_coordinates_le
        (fun i : Fin m ↦ q ∣ i.val + 1) (fun w ↦ J ∣ wordPolynomial w)
        (fun _ (a : Bool) ↦ a) (fun _ ↦ (1 / 2 : ℝ))
      · intro _ _; norm_num
      · intro _ _ b; exact (uniformProbability_bool_eq b).le
      · intro v w hv hw hfixed i _
        exact congrFun (word_eq_of_sparse_divisibility hq hJ hsimple hsep hlarge
          v w hv hw hfixed) i
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_sparse_internal_positions]
lemma binaryProbability_rational_irreducible_divisible_le_sparse {m q : ℕ}
    (hq : 0 < q) {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q) :
    binaryProbability m (fun P ↦ J ∣ P) ≤ (1 / 2 : ℝ) ^ (m / q) := by
  exact binaryProbability_divisible_le_sparse hq hJ
    (complex_roots_nodup_of_rational_irreducible hirr) hsep hlarge
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma binaryProbability_divisible_eq_zero_of_constant (m : ℕ) {J : ℤ[X]}
    (hJ : J.Monic) (h0 : J.coeff 0 ≠ 1) :
    binaryProbability m (fun p ↦ J ∣ p) = 0 := by
  have hf (w : Fin m → Bool) : ¬ J ∣ wordPolynomial w := by
    intro hd
    exact h0 ((wordPolynomial_endpoints w).monic_divisor_constant hJ hd)
  simp [binaryProbability, uniformProbability, hf]
lemma binaryProbability_divisible_eq_zero_of_degree {n : ℕ} (hn : 1 ≤ n)
    {J : ℤ[X]} (hdegree : n < J.natDegree) :
    binaryProbability (n - 1) (fun p ↦ J ∣ p) = 0 := by
  have hf (w : Fin (n - 1) → Bool) : ¬ J ∣ wordPolynomial w := by
    intro hd
    have hle := natDegree_le_of_dvd hd (wordPolynomial_endpoints w).ne_zero
    rw [natDegree_wordPolynomial, Nat.sub_add_cancel hn] at hle
    omega
  simp [binaryProbability, uniformProbability, hf]
lemma binaryProbability_monic_divisible_le {n : ℕ} (hn : 1 ≤ n)
    {J : ℤ[X]} (hJ : J.Monic) :
    binaryProbability (n - 1) (fun p ↦ J ∣ p) ≤ 2 / (2 : ℝ) ^ J.natDegree := by
  by_cases h0 : J.coeff 0 = 1
  · have hred : HasF2Endpoints J.natDegree (reducePolynomial 2 J) := by
      refine ⟨hJ.map _, monic_reduce_natDegree 2 hJ, ?_⟩
      rw [coeff_reducePolynomial, h0, Int.cast_one]
    calc
      _ ≤ f2Probability (n - 1) (fun p ↦ reducePolynomial 2 J ∣ p) := by
        apply uniformProbability_mono
        intro w hw
        exact reducePolynomial_dvd 2 hw
      _ ≤ _ := f2Probability_divisible_le hn hred
  · rw [binaryProbability_divisible_eq_zero_of_constant _ hJ h0]
    positivity
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_uniform_noncyclotomic_monic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], J.Monic → Irreducible (J.map (Int.castRingHom ℚ)) →
        (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨C, hC, hprime⟩ := exists_uniform_logarithmic_root_power_prime
  obtain ⟨c, hc, N₀, hN₀, hmahler⟩ := exists_uniform_quantitative_log_mahler_bound
  let K := max (2 * C) (1 / c)
  have hK : 0 < K := (by positivity : 0 < 2 * C).trans_le (le_max_left _ _)
  have hKC : 2 * C ≤ K := le_max_left _ _
  have hKc : 1 / c ≤ K := le_max_right _ _
  obtain ⟨N₁, hN₁, hscale⟩ := exists_threshold_logarithmic_prime_scale K
  refine ⟨Real.log 2 / (64 * K), div_pos (Real.log_pos (by norm_num)) (by positivity),
    max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn J hJ hirr hcyc
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hN₁.trans hn₁
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hconst : J.coeff 0 = 1
  swap
  · rw [binaryProbability_divisible_eq_zero_of_constant _ hJ hconst]
    exact (Real.exp_pos _).le
  by_cases hdeg : J.natDegree ≤ n
  swap
  · rw [binaryProbability_divisible_eq_zero_of_degree (by omega : 1 ≤ n) (by omega : n < J.natDegree)]
    exact (Real.exp_pos _).le
  have hconst0 : J.coeff 0 ≠ 0 := by rw [hconst]; norm_num
  obtain ⟨hlog, hsmall⟩ := hscale n hn₁
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hlogs : Real.log (J.natDegree : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdeg)
  have hthreshold : C * (1 + Real.log (J.natDegree : ℝ)) ≤ K * Real.log (n : ℝ) ^ 4 :=
    logarithmic_prime_scale_ge hC.le hKC hlog hlogs
  obtain ⟨q, hq, hqlo, hqhi, hsep⟩ :=
    hprime J hJ hirr hconst0 (K * Real.log (n : ℝ) ^ 4) hthreshold
  have hqhi' : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4 := by nlinarith [hqhi]
  have hqm : q ≤ n - 1 := by
    have h : (q : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith
    exact_mod_cast h
  have hM : c / Real.log (n : ℝ) ^ 3 ≤
      Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure :=
    hmahler hJ hirr hconst0 hcyc n hn₀ hdeg
  have hnM : (n : ℝ) < (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q := by
    apply (Real.lt_pow_iff_log_lt hn0 (mahlerMeasure_pos_of_ne_zero (hJ.map _).ne_zero)).mpr
    exact log_lt_prime_mul_log_of_mahler_gap hc hKc hlog hqlo hM
  have hroot : Real.sqrt ((((n - 1) / q : ℕ) : ℝ)) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hn0.le, ?_⟩
    have hfloor : ((((n - 1) / q : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.div_le_self (n - 1) q).trans (Nat.sub_le n 1)
    nlinarith
  exact (binaryProbability_rational_irreducible_divisible_le_sparse hq.pos hJ hirr
    hsep (hroot.trans_lt hnM)).trans (half_pow_sparse_quotient_le_exp hn2 hq.pos hqm hK hlog hqhi')
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma exists_uniform_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible (J.map (Int.castRingHom ℚ)) →
        (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨a, ha, N, hN, hbound⟩ := exists_uniform_noncyclotomic_monic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn J hirr hcyc
  by_cases hex : ∃ w : Fin (n - 1) → Bool, J ∣ wordPolynomial w
  · obtain ⟨w, hw⟩ := hex
    rcases monic_or_neg_monic_of_dvd_monic (wordPolynomial_endpoints w).monic hw with hJ | hJ
    · exact hbound n hn J hJ hirr hcyc
    · have hirr' : Irreducible ((-J).map (Int.castRingHom ℚ)) := by
        simpa only [Polynomial.map_neg] using (Associated.refl (J.map (Int.castRingHom ℚ))).neg_right.irreducible hirr
      have hcyc' : ¬ HasCyclotomicDivisor (-J) := by
        rintro ⟨k, hk, hdiv⟩
        exact hcyc ⟨k, hk, dvd_neg.mp hdiv⟩
      simpa only [neg_dvd] using hbound n hn (-J) hJ hirr' hcyc'
  · have hf : ∀ w : Fin (n - 1) → Bool, ¬ J ∣ wordPolynomial w := by simpa using hex
    have hz : binaryProbability (n - 1) (fun P ↦ J ∣ P) = 0 := by
      simp [binaryProbability, uniformProbability, hf]
    rw [hz]
    exact (Real.exp_pos _).le
lemma exists_uniform_integer_irreducible_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible J → (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨a, ha, N, hN, hbound⟩ := exists_uniform_noncyclotomic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn J hirr hcyc
  by_cases hex : ∃ w : Fin (n - 1) → Bool, J ∣ wordPolynomial w
  · obtain ⟨w, hw⟩ := hex
    exact hbound n hn J
      (irreducible_map_rat_of_dvd_monic (wordPolynomial_endpoints w).monic hw hirr) hcyc
  · have hf : ∀ w : Fin (n - 1) → Bool, ¬ J ∣ wordPolynomial w := by simpa using hex
    have hz : binaryProbability (n - 1) (fun P ↦ J ∣ P) = 0 := by
      simp [binaryProbability, uniformProbability, hf]
    rw [hz]
    exact (Real.exp_pos _).le
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma uniformAverage_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun a ↦ f a + g a) = uniformAverage f + uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_add_distrib, add_div]
lemma uniformAverage_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun a ↦ f a - g a) = uniformAverage f - uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib, sub_div]
lemma uniformProbability_or_le_add {α : Type*} [Fintype α] (E F : α → Prop) :
    uniformProbability (fun a ↦ E a ∨ F a) ≤ uniformProbability E + uniformProbability F := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_add]
  apply uniformAverage_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he, hf]
lemma uniformProbability_sub_of_imp {α : Type*} [Fintype α] (E F : α → Prop)
    (h : ∀ a, F a → E a) :
    uniformProbability E - uniformProbability F = uniformProbability (fun a ↦ E a ∧ ¬ F a) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_sub]
  congr 1
  funext a
  by_cases hf : F a
  · simp [hf, h a hf]
  · simp [hf]
lemma binaryProbability_or_le_add (m : ℕ) (E F : Polynomial ℤ → Prop) :
    binaryProbability m (fun p ↦ E p ∨ F p) ≤ binaryProbability m E + binaryProbability m F :=
  uniformProbability_or_le_add (fun w ↦ E (wordPolynomial w)) (fun w ↦ F (wordPolynomial w))
end OdlyzkoPoonen

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
lemma exists_noncyclotomic_reciprocal_finite_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      binaryProbability (n - 1) (fun P ↦
        HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) ≤
        Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
          6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  obtain ⟨a, ha, N, hN, hfactor⟩ := exists_uniform_noncyclotomic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn L
  let t := (smallDivisorCandidates L).filter (fun J ↦
    Irreducible (J.map (Int.castRingHom ℚ)) ∧ ¬ HasCyclotomicDivisor J)
  have hn1 : 1 ≤ n := by omega
  have hsub : binaryProbability (n - 1) (fun P ↦
      HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) ≤
      binaryProbability (n - 1) (fun P ↦
        (∃ J ∈ t, J ∣ P) ∨ HasLargeReciprocalIntegerDivisor L P) := by
    apply uniformProbability_mono
    intro w hw
    rcases (wordPolynomial_endpoints w).reciprocal_divisor_candidate_alternative hw.1 hw.2 with h | h
    · obtain ⟨J, hmem, hirr, hcyc, hdiv⟩ := h
      exact Or.inl ⟨J, Finset.mem_filter.mpr ⟨hmem, hirr, hcyc⟩, hdiv⟩
    · exact Or.inr h
  have hsmall : binaryProbability (n - 1) (fun P ↦ ∃ J ∈ t, J ∣ P) ≤
      (t.card : ℝ) * Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
    apply uniformProbability_exists_mem_le_card_mul t
    intro J hJ
    obtain ⟨_, hirr, hcyc⟩ := Finset.mem_filter.mp hJ
    exact hfactor n hn J hirr hcyc
  have hcard : (t.card : ℝ) ≤ Real.exp (4 * (L : ℝ) ^ 2) := by
    have h : t.card ≤ (smallDivisorCandidates L).card := Finset.card_filter_le _ _
    exact (by exact_mod_cast h : (t.card : ℝ) ≤ (smallDivisorCandidates L).card).trans
      (card_smallDivisorCandidates_le_exp L)
  have hsmall' : binaryProbability (n - 1) (fun P ↦ ∃ J ∈ t, J ∣ P) ≤
      Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
    calc
      _ ≤ (t.card : ℝ) * Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := hsmall
      _ ≤ Real.exp (4 * (L : ℝ) ^ 2) *
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact hsub.trans ((binaryProbability_or_le_add _ _ _).trans
    (add_le_add hsmall' (binaryProbability_large_reciprocal_divisor_le hn1 L)))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
lemma binaryProbability_reciprocal_noncyclotomic_isBigO (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  obtain ⟨a, ha, N, _hN, hfinite⟩ := exists_noncyclotomic_reciprocal_finite_bound
  exact isBigO_rpow_of_reciprocal_finite_bound (fun _ ↦ uniformProbability_nonneg _)
    ha hfinite A hA
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma cancel_common_autocorrelation_factor {d : ℕ} {a b t : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a)
    (h : (a * b) * (a * b).reverse = (a * t) * (a * t).reverse) :
    b * b.reverse = t * t.reverse := by
  apply mul_left_cancel₀ (mul_ne_zero ha.monic.ne_zero ha.reverse.monic.ne_zero)
  calc
    (a * a.reverse) * (b * b.reverse) = (a * b) * (a * b).reverse := by
      rw [reverse_mul_of_domain]
      ring
    _ = (a * t) * (a * t).reverse := h
    _ = (a * a.reverse) * (t * t.reverse) := by
      rw [reverse_mul_of_domain]
      ring
lemma coprime_equal_autocorrelation_reverse {e : ℕ} {b t : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (ht : HasF2Endpoints e t)
    (hcop : IsCoprime b t) (h : b * b.reverse = t * t.reverse) : t = b.reverse := by
  have hdiv : b ∣ t * t.reverse := by rw [← h]; exact dvd_mul_right _ _
  have hbdiv : b ∣ t.reverse := hcop.dvd_of_dvd_mul_left hdiv
  have heq : t.reverse = b := eq_of_monic_of_dvd_of_natDegree_le
    hb.monic ht.reverse.monic hbdiv (by rw [ht.reverse.degree, hb.degree])
  simpa only [ht.reverse_reverse] using congrArg Polynomial.reverse heq
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma equal_autocorrelation_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) :
    ∃ a b : (ZMod 2)[X],
      HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      F = a * b ∧ G = a * b.reverse ∧ a.natDegree + b.natDegree = n := by
  obtain ⟨a, b, t, hFb, hGt, ha, hb, ht, hcop, hdegF, hdegG⟩ :=
    exists_coprime_endpoint_factors hF hG
  have hbt : t.natDegree = b.natDegree := by omega
  have ht' : HasF2Endpoints b.natDegree t := ⟨ht.monic, hbt, ht.constant⟩
  have hcancel : b * b.reverse = t * t.reverse := by
    apply cancel_common_autocorrelation_factor ha
    simpa only [← hFb, ← hGt] using h
  have hrev := coprime_equal_autocorrelation_reverse hb ht' hcop hcancel
  exact ⟨a, b, ha, hb, hFb, by simpa only [hrev] using hGt, hdegF⟩
lemma nontrivial_companion_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) (hne : G ≠ F) (hrev : G ≠ F.reverse) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ 1 ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      F = a * b ∧ G = a * b.reverse ∧ a ≠ a.reverse ∧ b ≠ b.reverse := by
  obtain ⟨a, b, ha, hb, hFb, hGb, hdeg⟩ := equal_autocorrelation_factorization hF hG h
  have hna : a ≠ a.reverse := by
    intro heq
    apply hrev
    rw [hGb, hFb, reverse_mul_of_domain, ← heq]
  have hnb : b ≠ b.reverse := by
    intro heq
    apply hne
    rw [hGb, ← heq, ← hFb]
  exact ⟨a.natDegree, b.natDegree, a, b,
    ha.degree_pos_of_nonreciprocal hna, hb.degree_pos_of_nonreciprocal hnb,
    hdeg, ha, hb, hFb, hGb, hna, hnb⟩
lemma ordered_companion_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) (hne : G ≠ F) (hrev : G ≠ F.reverse) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ d ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      F = a * b ∧ a ≠ a.reverse ∧ b ≠ b.reverse ∧
      (G = a * b.reverse ∨ G.reverse = a * b.reverse) := by
  obtain ⟨d, e, a, b, hd, he, hdeg, ha, hb, hFb, hGb, hna, hnb⟩ :=
    nontrivial_companion_factorization hF hG h hne hrev
  by_cases hde : d ≤ e
  · exact ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hFb, hna, hnb, Or.inl hGb⟩
  · refine ⟨e, d, b, a, he, by omega, by omega, hb, ha, ?_, hnb, hna, Or.inr ?_⟩
    · simpa only [mul_comm] using hFb
    · rw [hGb, reverse_mul_of_domain, hb.reverse_reverse, mul_comm]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma CongruentMod.of_dvd {r s : ℕ} {p q : ℤ[X]}
    (h : CongruentMod s p q) (hrs : r ∣ s) : CongruentMod r p q := by
  apply (congruentMod_iff_coeff_dvd r p q).mpr
  intro k
  have hcast : (r : ℤ) ∣ (s : ℤ) := by exact_mod_cast hrs
  exact hcast.trans ((congruentMod_iff_coeff_dvd s p q).mp h k)
def HasModFourCompanion (n : ℕ) (p : ℤ[X]) : Prop :=
  ∃ q : ℤ[X], HasBinaryEndpoints n q ∧ q ≠ p ∧ q ≠ p.reverse ∧
    CongruentMod 4 (autocorrelation p) (autocorrelation q)
lemma binary_autocorrelations_reduce_eq {p q : ℤ[X]} (hp : IsBinary p) (hq : IsBinary q)
    (h : CongruentMod 4 (autocorrelation p) (autocorrelation q)) :
    reducePolynomial 2 p * (reducePolynomial 2 p).reverse =
      reducePolynomial 2 q * (reducePolynomial 2 q).reverse := by
  have h2 := h.of_dvd (by norm_num : 2 ∣ 4)
  change reducePolynomial 2 (p * p.reverse) = reducePolynomial 2 (q * q.reverse) at h2
  simpa only [reducePolynomial_mul, hp.reduce_reverse, hq.reduce_reverse] using h2
lemma HasModFourCompanion.factorization {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcomp : HasModFourCompanion n p) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ d ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      p = zeroOneLift (a * b) ∧ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse))) := by
  obtain ⟨q, hq, hne, hrev, hcong⟩ := hcomp
  have hn2 : reducePolynomial 2 q ≠ reducePolynomial 2 p := by
    intro h
    exact hne (hq.binary.eq_of_reduce_eq hp.binary h)
  have hr2 : reducePolynomial 2 q ≠ (reducePolynomial 2 p).reverse := by
    intro h
    apply hrev
    apply hq.binary.eq_of_reduce_eq hp.binary.reverse
    simpa only [hp.binary.reduce_reverse] using h
  obtain ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hFab, hna, _, hGab⟩ :=
    ordered_companion_factorization hp.reduce hq.reduce
      (binary_autocorrelations_reduce_eq hp.binary hq.binary hcong) hn2 hr2
  have hpab : p = zeroOneLift (a * b) := by
    simpa only [zeroOneLift_reduce hp.binary] using congrArg zeroOneLift hFab
  refine ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hpab, hna, ?_⟩
  rw [← hpab]
  rcases hGab with hGab | hGab
  · have hqab : q = zeroOneLift (a * b.reverse) := by
      simpa only [zeroOneLift_reduce hq.binary] using congrArg zeroOneLift hGab
    simpa only [← hqab] using hcong
  · have hqab : q.reverse = zeroOneLift (a * b.reverse) := by
      simpa only [zeroOneLift_reverse, zeroOneLift_reduce hq.binary] using
        congrArg zeroOneLift hGab
    rw [← hqab, autocorrelation_reverse (by rw [hq.constant]; exact one_ne_zero)]
    exact hcong
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma HasBinaryEndpoints.companion_or_reciprocal_of_reducible {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 1 ≤ n) (hred : ReducibleOverRat p) :
    HasModFourCompanion n p ∨ HasLargeReciprocalIntegerDivisor 1 p := by
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hp.monic_factors_of_reducible hn hred
  by_cases har : a = a.reverse
  · exact Or.inr ⟨a, ha, ⟨b, hab⟩, har.symm, had⟩
  by_cases hbr : b = b.reverse
  · exact Or.inr ⟨b, hb, ⟨a, by rw [hab, mul_comm]⟩, hbr.symm, hbd⟩
  obtain ⟨_, _, hq, hcorr, heq, hrev⟩ := binary_factor_reversal hp ha hb hab
  refine Or.inl ⟨a * b.reverse, hq, ?_, ?_, ?_⟩
  · exact fun h ↦ hbr (heq.mp h)
  · exact fun h ↦ har (hrev.mp h)
  · change reducePolynomial 4 (autocorrelation p) = reducePolynomial 4 (autocorrelation (a * b.reverse))
    exact congrArg (reducePolynomial 4) hcorr.symm
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma monic_reducibleOverRat_of_integer_root {p : ℤ[X]} (hp : p.Monic)
    (hdegree : 2 ≤ p.natDegree) {t : ℤ} (hroot : p.eval t = 0) :
    ReducibleOverRat p := by
  intro hi
  have hr : IsRoot (p.map (Int.castRingHom ℚ)) ((Int.castRingHom ℚ) t) := by
    change (p.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) t) = 0
    rw [eval_map_apply, hroot, map_zero]
  have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hr)
  rw [hp.natDegree_map] at hd
  change p.natDegree = 1 at hd
  omega
lemma HasBinaryEndpoints.reducible_of_minus_one {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 2 ≤ n) (hroot : p.eval (-1) = 0) :
    ReducibleOverRat p :=
  monic_reducibleOverRat_of_integer_root hp.monic (by rwa [hp.degree]) hroot
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma lifted_factor_autocorrelation_congruent_two (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) :
    CongruentMod 2 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse))) := by
  simp only [CongruentMod, autocorrelation, reducePolynomial_mul,
    ← zeroOneLift_reverse, reduce_zeroOneLift]
  rw [reverse_mul_of_domain, reverse_mul_of_domain,
    reverse_reverse_of_constant_ne_zero hb]
  ring
lemma lifted_factor_autocorrelation_even (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) (k : ℕ) :
    (2 : ℤ) ∣ (autocorrelation (zeroOneLift (a * b))).coeff k -
      (autocorrelation (zeroOneLift (a * b.reverse))).coeff k :=
  (congruentMod_iff_coeff_dvd _ _ _).mp
    (lifted_factor_autocorrelation_congruent_two a b hb) k
lemma four_dvd_iff_two_dvd_half {t : ℤ} (ht : 2 ∣ t) :
    4 ∣ t ↔ 2 ∣ t / 2 := by
  obtain ⟨u, rfl⟩ := ht
  rw [Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  change 2 * 2 ∣ 2 * u ↔ 2 ∣ u
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)
noncomputable def halfCoefficientDifference (p q : ℤ[X]) (k : ℕ) : ZMod 2 :=
  (((p.coeff k - q.coeff k) / 2 : ℤ) : ZMod 2)
lemma halfCoefficientDifference_eq_zero_iff {p q : ℤ[X]} {k : ℕ}
    (h : (2 : ℤ) ∣ p.coeff k - q.coeff k) :
    halfCoefficientDifference p q k = 0 ↔ (4 : ℤ) ∣ p.coeff k - q.coeff k := by
  rw [halfCoefficientDifference, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (four_dvd_iff_two_dvd_half h).symm
lemma congruent_four_iff_half_differences_zero {p q : ℤ[X]}
    (h : CongruentMod 2 p q) :
    CongruentMod 4 p q ↔ ∀ k, halfCoefficientDifference p q k = 0 := by
  rw [congruentMod_iff_coeff_dvd]
  have he := (congruentMod_iff_coeff_dvd _ _ _).mp h
  exact forall_congr' (fun k ↦ (halfCoefficientDifference_eq_zero_iff (he k)).symm)
noncomputable def autocorrelationDiscrepancy (a b : (ZMod 2)[X]) (k : ℕ) : ZMod 2 :=
  halfCoefficientDifference (autocorrelation (zeroOneLift (a * b)))
    (autocorrelation (zeroOneLift (a * b.reverse))) k
lemma lifted_factor_congruent_four_iff (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) :
    CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse))) ↔
    ∀ k, autocorrelationDiscrepancy a b k = 0 :=
  congruent_four_iff_half_differences_zero
    (lifted_factor_autocorrelation_congruent_two a b hb)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma coeff_autocorrelation_le (p : ℤ[X]) {k : ℕ} (hk : k ≤ p.natDegree) :
    (autocorrelation p).coeff k =
      ∑ i ∈ Finset.range (k + 1), p.coeff i * p.coeff (p.natDegree - k + i) := by
  rw [autocorrelation, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ p.coeff i * p.reverse.coeff j)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by omega),
    show p.natDegree - (k - i) = p.natDegree - k + i by omega]
lemma HasBinaryEndpoints.coeff_autocorrelation_outer {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hk0 : 0 < k) (hk : k ≤ n) :
    (autocorrelation p).coeff k = p.coeff k + p.coeff (n - k) +
      ∑ i ∈ Finset.Ico 1 k, p.coeff i * p.coeff (n - k + i) := by
  rw [coeff_autocorrelation_le p (by rw [hp.degree]; exact hk), hp.degree]
  have hs := Finset.sum_range_add_sum_Ico
    (fun i ↦ p.coeff i * p.coeff (n - k + i)) (show 1 ≤ k by omega)
  rw [Finset.sum_range_succ, ← hs]
  simp only [Finset.sum_range_one, Nat.add_zero, Nat.sub_add_cancel hk,
    hp.constant, hp.coeff_degree, one_mul, mul_one]
  ring
lemma HasBinaryEndpoints.autocorrelation_outer_difference {n k : ℕ} {p q : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hq : HasBinaryEndpoints n q)
    (hk0 : 0 < k) (hk : k ≤ n)
    (hleft : ∀ i < k, p.coeff i = q.coeff i)
    (hright : ∀ i < k, p.coeff (n - i) = q.coeff (n - i)) :
    (autocorrelation p).coeff k - (autocorrelation q).coeff k =
      p.coeff k + p.coeff (n - k) - q.coeff k - q.coeff (n - k) := by
  have hs : (∑ i ∈ Finset.Ico 1 k, p.coeff i * p.coeff (n - k + i)) =
      ∑ i ∈ Finset.Ico 1 k, q.coeff i * q.coeff (n - k + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi0, hik⟩ := Finset.mem_Ico.mp hi
    rw [hleft i hik, show n - k + i = n - (k - i) by omega,
      hright (k - i) (by omega)]
  rw [hp.coeff_autocorrelation_outer hk0 hk, hq.coeff_autocorrelation_outer hk0 hk, hs]
  ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def AgreeOnOuter {R : Type*} [Semiring R] (n k : ℕ) (p q : R[X]) : Prop :=
  (∀ i ≤ k, p.coeff i = q.coeff i) ∧
  (∀ i ≤ k, p.coeff (n - i) = q.coeff (n - i))
lemma AgreeOnOuter.mono {R : Type*} [Semiring R] {n k l : ℕ} {p q : R[X]}
    (h : AgreeOnOuter n k p q) (hl : l ≤ k) : AgreeOnOuter n l p q :=
  ⟨fun i hi ↦ h.1 i (hi.trans hl), fun i hi ↦ h.2 i (hi.trans hl)⟩
lemma coeff_mul_right_eq_of_prefix {R : Type*} [Semiring R] (a : R[X])
    {b b' : R[X]} {k : ℕ} (h : ∀ i ≤ k, b.coeff i = b'.coeff i) :
    (a * b).coeff k = (a * b').coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [h ij.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega)]
lemma AgreeOnOuter.autocorrelation {n k : ℕ} {p q : ℤ[X]}
    (h : AgreeOnOuter n k p q) (hp : p.natDegree = n) (hq : q.natDegree = n)
    (hk : k ≤ n) : (autocorrelation p).coeff k = (autocorrelation q).coeff k := by
  rw [coeff_autocorrelation_le p (by rw [hp]; exact hk),
    coeff_autocorrelation_le q (by rw [hq]; exact hk), hp, hq]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [h.1 i hik, show n - k + i = n - (k - i) by omega, h.2 (k - i) (by omega)]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma AgreeOnOuter.reverse {n k : ℕ} {p q : (ZMod 2)[X]}
    (h : AgreeOnOuter n k p q) (hp : HasF2Endpoints n p) (hq : HasF2Endpoints n q)
    (hk : k ≤ n) : AgreeOnOuter n k p.reverse q.reverse := by
  constructor
  · intro i hi
    simpa only [coeff_reverse, hp.degree, hq.degree, revAt_le (hi.trans hk)] using h.2 i hi
  · intro i hi
    simpa only [coeff_reverse, hp.degree, hq.degree, revAt_le (Nat.sub_le n i),
      Nat.sub_sub_self (hi.trans hk)] using h.1 i hi
lemma AgreeOnOuter.mul_left {d e k : ℕ} {a b b' : (ZMod 2)[X]}
    (h : AgreeOnOuter e k b b') (ha : HasF2Endpoints d a)
    (hb : HasF2Endpoints e b) (hb' : HasF2Endpoints e b') (hk : k ≤ e) :
    AgreeOnOuter (d + e) k (a * b) (a * b') := by
  constructor
  · intro i hi
    exact coeff_mul_right_eq_of_prefix a (fun j hj ↦ h.1 j (hj.trans hi))
  · intro i hi
    have hr := h.reverse hb hb' hk
    have he := coeff_mul_right_eq_of_prefix a.reverse (fun j hj ↦ hr.1 j (hj.trans hi))
    rw [← reverse_mul_of_domain, ← reverse_mul_of_domain] at he
    simpa only [coeff_reverse, (ha.mul hb).degree, (ha.mul hb').degree,
      revAt_le (show i ≤ d + e by omega)] using he
lemma AgreeOnOuter.zeroOneLift {n k : ℕ} {p q : (ZMod 2)[X]}
    (h : AgreeOnOuter n k p q) : AgreeOnOuter n k (zeroOneLift p) (zeroOneLift q) := by
  constructor
  · intro i hi
    rw [coeff_zeroOneLift, coeff_zeroOneLift, h.1 i hi]
  · intro i hi
    rw [coeff_zeroOneLift, coeff_zeroOneLift, h.2 i hi]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def DependsOnEarlier {n : ℕ} (t : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (v w : Fin n → Bool),
    (∀ j, j < i → v j = w j) → t v i = t w i
def triangularBitMap {n : ℕ} (t : (Fin n → Bool) → Fin n → Bool)
    (w : Fin n → Bool) (i : Fin n) : Bool :=
  Bool.xor (w i) (t w i)
lemma triangularBitMap_injective {n : ℕ} {t : (Fin n → Bool) → Fin n → Bool}
    (ht : DependsOnEarlier t) : Function.Injective (triangularBitMap t) := by
  intro v w h
  have hp : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i = w i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      have he : t v i = t w i := ht i v w (fun j hj ↦
        ih j.val (by simpa only [← hik, Fin.lt_def] using hj) j rfl)
      have hx := congrFun h i
      change Bool.xor (v i) (t v i) = Bool.xor (w i) (t w i) at hx
      rw [he] at hx
      cases hv : v i <;> cases hw : w i <;> cases htwi : t w i <;>
        simp_all
  funext i
  exact hp i.val i rfl
lemma triangularBitMap_bijective {n : ℕ} {t : (Fin n → Bool) → Fin n → Bool}
    (ht : DependsOnEarlier t) : Function.Bijective (triangularBitMap t) := by
  have hi := triangularBitMap_injective ht
  exact ⟨hi, Finite.surjective_of_injective hi⟩
lemma uniformProbability_triangularBitMap {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t)
    (E : (Fin n → Bool) → Prop) :
    uniformProbability (fun w ↦ E (triangularBitMap t w)) = uniformProbability E :=
  uniformProbability_bijective (triangularBitMap_bijective ht) E
lemma uniformProbability_triangular_prescribedBits {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t)
    (s : Finset (Fin n)) (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦
      ∀ i ∈ s, triangularBitMap t w i = v i) = (1 / 2 : ℝ) ^ s.card :=
  (uniformProbability_triangularBitMap ht (fun z ↦ ∀ i ∈ s, z i = v i)).trans
    (uniformProbability_prescribedBits s v)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def DependsOnPrefix {n : ℕ} (D : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (v w : Fin n → Bool),
    (∀ j, j ≤ i → v j = w j) → D v i = D w i
def TogglesOn {n : ℕ} (s : Finset (Fin n))
    (D : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ i ∈ s, ∀ w, D (Function.update w i (!(w i))) i = !(D w i)
def freshBitCorrection {n : ℕ} (s : Finset (Fin n))
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ s then Bool.xor (w i) (D w i) else false
lemma freshBitCorrection_dependsOnEarlier {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) : DependsOnEarlier (freshBitCorrection s D) := by
  intro i v w hprev
  by_cases hi : i ∈ s
  · simp only [freshBitCorrection, if_pos hi]
    by_cases he : v i = w i
    · have hd : D v i = D w i := hp i v w (by
        intro j hj
        rcases lt_or_eq_of_le hj with hj | rfl
        · exact hprev j hj
        · exact he)
      rw [he, hd]
    · have hwi : w i = !(v i) := by
        cases hv : v i <;> cases hw : w i <;> simp_all
      have hu : D (Function.update v i (w i)) i = D w i := hp i _ w (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · rw [Function.update_of_ne hji]
          exact hprev j (lt_of_le_of_ne hj hji))
      rw [hwi, hf i hi v] at hu
      rw [hwi, ← hu]
      cases v i <;> cases D v i <;> rfl
  · simp only [freshBitCorrection, if_neg hi]
lemma triangular_freshBitCorrection_active {n : ℕ} {s : Finset (Fin n)}
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool)
    {i : Fin n} (hi : i ∈ s) :
    triangularBitMap (freshBitCorrection s D) w i = D w i := by
  simp only [triangularBitMap, freshBitCorrection, if_pos hi]
  cases w i <;> cases D w i <;> rfl
lemma triangular_freshBitCorrection_inactive {n : ℕ} {s : Finset (Fin n)}
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool)
    {i : Fin n} (hi : i ∉ s) :
    triangularBitMap (freshBitCorrection s D) w i = w i := by
  simp [triangularBitMap, freshBitCorrection, hi]
lemma uniformProbability_freshBitConstraints {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, D w i = v i) =
      (1 / 2 : ℝ) ^ s.card := by
  have he : (fun w : Fin n → Bool ↦ ∀ i ∈ s,
      triangularBitMap (freshBitCorrection s D) w i = v i) =
      (fun w ↦ ∀ i ∈ s, D w i = v i) := by
    funext w
    apply propext
    exact forall_congr' (fun i ↦ forall_congr' (fun hi ↦ by
      rw [triangular_freshBitCorrection_active D w hi]))
  rw [← he]
  exact uniformProbability_triangular_prescribedBits
    (freshBitCorrection_dependsOnEarlier hp hf) s v
lemma uniformProbability_all_outputs_zero_le {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i, D w i = false) ≤
      (1 / 2 : ℝ) ^ s.card := by
  calc
    _ ≤ uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, D w i = false) :=
      uniformProbability_mono (fun _ h i _ ↦ h i)
    _ = _ := uniformProbability_freshBitConstraints hp hf (fun _ ↦ false)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma autocorrelationDiscrepancy_eq_of_outer {d e k : ℕ} {a b b' : (ZMod 2)[X]}
    (h : AgreeOnOuter e k b b') (ha : HasF2Endpoints d a)
    (hb : HasF2Endpoints e b) (hb' : HasF2Endpoints e b') (hk : k ≤ e) :
    autocorrelationDiscrepancy a b k = autocorrelationDiscrepancy a b' k := by
  have hP := (h.mul_left ha hb hb' hk).zeroOneLift.autocorrelation
    (ha.mul hb).lift.degree (ha.mul hb').lift.degree (show k ≤ d + e by omega)
  have hQ := ((h.reverse hb hb' hk).mul_left ha hb.reverse hb'.reverse hk).zeroOneLift.autocorrelation
    (ha.mul hb.reverse).lift.degree (ha.mul hb'.reverse).lift.degree (show k ≤ d + e by omega)
  unfold autocorrelationDiscrepancy halfCoefficientDifference
  rw [hP, hQ]
lemma pairedPolynomial_agreeOnOuter {n : ℕ} {u u' c : Fin (n / 2) → Bool}
    (z z' : Fin (n % 2) → Bool) {i : Fin (n / 2)}
    (h : ∀ j ≤ i, u j = u' j) :
    AgreeOnOuter (n + 1) (i.val + 1) (pairedPolynomial u c z) (pairedPolynomial u' c z') := by
  have hp := pairedPolynomial_endpoints u c z
  have hq := pairedPolynomial_endpoints u' c z'
  constructor
  · intro k hk
    by_cases hk0 : k = 0
    · rw [hk0, hp.constant, hq.constant]
    · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
      have hj : j.val + 1 = k := by dsimp [j]; omega
      have hji : j ≤ i := by change j.val ≤ i.val; dsimp [j]; omega
      rw [← hj, coeff_pairedPolynomial_lower, coeff_pairedPolynomial_lower, h j hji]
  · intro k hk
    by_cases hk0 : k = 0
    · simp only [hk0, Nat.sub_zero, hp.coeff_degree, hq.coeff_degree]
    · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
      have hj : j.val + 1 = k := by dsimp [j]; omega
      have hji : j ≤ i := by change j.val ≤ i.val; dsimp [j]; omega
      rw [← hj, coeff_pairedPolynomial_upper, coeff_pairedPolynomial_upper, h j hji]
noncomputable def pairedDiscrepancy {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool)
    (u : Fin (n / 2) → Bool) (i : Fin (n / 2)) : Bool :=
  f2ToBit (autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1))
lemma pairedDiscrepancy_eq_of_prefix {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) {u u' c : Fin (n / 2) → Bool}
    (z z' : Fin (n % 2) → Bool) {i : Fin (n / 2)} (h : ∀ j ≤ i, u j = u' j) :
    pairedDiscrepancy a c z u i = pairedDiscrepancy a c z' u' i := by
  apply congrArg f2ToBit
  exact autocorrelationDiscrepancy_eq_of_outer (pairedPolynomial_agreeOnOuter z z' h)
    ha (pairedPolynomial_endpoints u c z) (pairedPolynomial_endpoints u' c z')
    (by have := i.isLt; omega)
lemma pairedDiscrepancy_dependsOnPrefix {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    DependsOnPrefix (pairedDiscrepancy a c z) := by
  intro i u u' h
  exact pairedDiscrepancy_eq_of_prefix ha z z h
lemma pairedDiscrepancy_center_independent {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c u : Fin (n / 2) → Bool)
    (z z' : Fin (n % 2) → Bool) : pairedDiscrepancy a c z u = pairedDiscrepancy a c z' u := by
  funext i
  exact pairedDiscrepancy_eq_of_prefix ha z z' (fun _ _ ↦ rfl)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma halfCoefficientDifference_change {p q p' q' : ℤ[X]} {k : ℕ} {s : ℤ}
    (he : (2 : ℤ) ∣ p.coeff k - q.coeff k)
    (hc : p'.coeff k - q'.coeff k = (p.coeff k - q.coeff k) + 2 * s) :
    halfCoefficientDifference p' q' k - halfCoefficientDifference p q k =
      (s : ZMod 2) := by
  obtain ⟨u, hu⟩ := he
  have hu' : p'.coeff k - q'.coeff k = 2 * (u + s) := by
    rw [hc, hu]
    ring
  simp only [halfCoefficientDifference, hu, hu',
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  push_cast
  ring
lemma halfAutocorrelation_change_of_complementation {n k : ℕ} {p q p' q' : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hq : HasBinaryEndpoints n q)
    (hp' : HasBinaryEndpoints n p') (hq' : HasBinaryEndpoints n q')
    (hk0 : 0 < k) (hk : k ≤ n)
    (he : CongruentMod 2 (autocorrelation p) (autocorrelation q))
    (hpl : ∀ i < k, p'.coeff i = p.coeff i)
    (hpr : ∀ i < k, p'.coeff (n - i) = p.coeff (n - i))
    (hql : ∀ i < k, q'.coeff i = q.coeff i)
    (hqr : ∀ i < k, q'.coeff (n - i) = q.coeff (n - i))
    (hpk : p'.coeff k = 1 - p.coeff k)
    (hpnk : p'.coeff (n - k) = 1 - p.coeff (n - k))
    (hqk : q'.coeff k = 1 - q.coeff k)
    (hqnk : q'.coeff (n - k) = 1 - q.coeff (n - k)) :
    halfCoefficientDifference (autocorrelation p') (autocorrelation q') k -
        halfCoefficientDifference (autocorrelation p) (autocorrelation q) k =
      ((p.coeff k + p.coeff (n - k) + q.coeff k + q.coeff (n - k) : ℤ) : ZMod 2) := by
  have hpd := hp'.autocorrelation_outer_difference hp hk0 hk hpl hpr
  have hqd := hq'.autocorrelation_outer_difference hq hk0 hk hql hqr
  rw [hpk, hpnk] at hpd
  rw [hqk, hqnk] at hqd
  have hx := halfCoefficientDifference_change
    ((congruentMod_iff_coeff_dvd _ _ _).mp he k)
    (s := q.coeff k + q.coeff (n - k) - p.coeff k - p.coeff (n - k))
    (p' := autocorrelation p') (q' := autocorrelation q') (by linarith)
  rw [hx]
  push_cast
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
noncomputable def togglePair (e k : ℕ) (b : (ZMod 2)[X]) : (ZMod 2)[X] :=
  b + (X ^ k + X ^ (e - k))
lemma HasF2Endpoints.togglePair {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    HasF2Endpoints e (togglePair e k b) := by
  have hsmall : (X ^ k + X ^ (e - k) : (ZMod 2)[X]).natDegree < b.natDegree := by
    rw [hb.degree]
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    simp only [natDegree_X_pow]
    exact max_lt (by omega) (by omega)
  refine ⟨hb.monic.add_of_left (degree_lt_degree hsmall),
    (natDegree_add_eq_left_of_natDegree_lt hsmall).trans hb.degree, ?_⟩
  simp [OdlyzkoPoonen.togglePair, hb.constant, coeff_X_pow, show (0 : ℕ) ≠ k by omega,
    show (0 : ℕ) ≠ e - k by omega]
lemma reverse_togglePair {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    (togglePair e k b).reverse = togglePair e k b.reverse := by
  have ht := hb.togglePair hk0 hk
  unfold Polynomial.reverse
  rw [ht.degree, hb.degree]
  simp only [togglePair, reflect_add, reflect_monomial,
    revAt_le (show k ≤ e by omega), revAt_le (Nat.sub_le e k),
    Nat.sub_sub_self (show k ≤ e by omega)]
  rw [add_comm (X ^ (e - k)) (X ^ k)]
lemma coeff_mul_togglePair_before (a b : (ZMod 2)[X]) {e k i : ℕ}
    (hk : 2 * k < e) (hi : i < k) :
    (a * togglePair e k b).coeff i = (a * b).coeff i := by
  simp [togglePair, mul_add, coeff_mul_X_pow',
    show ¬ k ≤ i by omega, show ¬ e - k ≤ i by omega]
lemma coeff_mul_togglePair_at (a b : (ZMod 2)[X]) {e k : ℕ}
    (hk : 2 * k < e) (ha : a.coeff 0 = 1) :
    (a * togglePair e k b).coeff k = (a * b).coeff k + 1 := by
  simp [togglePair, mul_add, coeff_mul_X_pow', ha, show ¬ e - k ≤ k by omega]
lemma coeff_mul_togglePair_opposite {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) :
    (a * togglePair e k b).coeff (d + e - k) = (a * b).coeff (d + e - k) + 1 := by
  have h := coeff_mul_togglePair_at a.reverse b.reverse hk ha.reverse.constant
  rw [← reverse_togglePair hb hk0 hk, ← reverse_mul_of_domain,
    ← reverse_mul_of_domain] at h
  simpa only [coeff_reverse, (ha.mul (hb.togglePair hk0 hk)).degree,
    (ha.mul hb).degree, revAt_le (show k ≤ d + e by omega)] using h
lemma coeff_mul_togglePair_opposite_before {d e k i : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) (hi : i < k) :
    (a * togglePair e k b).coeff (d + e - i) = (a * b).coeff (d + e - i) := by
  have h := coeff_mul_togglePair_before a.reverse b.reverse hk hi
  rw [← reverse_togglePair hb hk0 hk, ← reverse_mul_of_domain,
    ← reverse_mul_of_domain] at h
  simpa only [coeff_reverse, (ha.mul (hb.togglePair hk0 hk)).degree,
    (ha.mul hb).degree, revAt_le (show i ≤ d + e by omega)] using h
lemma togglePair_togglePair (e k : ℕ) (b : (ZMod 2)[X]) :
    togglePair e k (togglePair e k b) = b := by
  unfold togglePair
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
lemma togglePair_add_reverse {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    togglePair e k b + (togglePair e k b).reverse = b + b.reverse := by
  rw [reverse_togglePair hb hk0 hk]
  unfold togglePair
  calc
    _ = b + b.reverse + ((X ^ k + X ^ (e - k)) + (X ^ k + X ^ (e - k))) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma int_val_add_one_zmod_two (c : ZMod 2) :
    ((c + 1).val : ℤ) = 1 - (c.val : ℤ) := by
  fin_cases c <;> rfl
lemma asymmetry_product_coeff {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b) (hk : k ≤ d + e) :
    ((a + a.reverse) * (b + b.reverse)).coeff k =
      (a * b).coeff k + (a * b).coeff (d + e - k) +
        (a * b.reverse).coeff k + (a * b.reverse).coeff (d + e - k) := by
  have he : (a + a.reverse) * (b + b.reverse) =
      a * b + (a * b).reverse + a * b.reverse + (a * b.reverse).reverse := by
    rw [reverse_mul_of_domain, reverse_mul_of_domain,
      reverse_reverse_of_constant_ne_zero (by rw [hb.constant]; norm_num)]
    ring
  rw [he]
  simp only [coeff_add, coeff_reverse, (ha.mul hb).degree,
    (ha.mul hb.reverse).degree, revAt_le hk]
lemma autocorrelationDiscrepancy_togglePair {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) :
    autocorrelationDiscrepancy a (togglePair e k b) k -
        autocorrelationDiscrepancy a b k =
      ((a + a.reverse) * (b + b.reverse)).coeff k := by
  have hbn : b.coeff 0 ≠ 0 := by rw [hb.constant]; norm_num
  calc
    _ = (((zeroOneLift (a * b)).coeff k + (zeroOneLift (a * b)).coeff (d + e - k) +
          (zeroOneLift (a * b.reverse)).coeff k +
          (zeroOneLift (a * b.reverse)).coeff (d + e - k) : ℤ) : ZMod 2) := by
      unfold autocorrelationDiscrepancy
      rw [reverse_togglePair hb hk0 hk]
      apply halfAutocorrelation_change_of_complementation
        (ha.mul hb).lift (ha.mul hb.reverse).lift
        (ha.mul (hb.togglePair hk0 hk)).lift
        (ha.mul (hb.reverse.togglePair hk0 hk)).lift hk0 (by omega)
        (lifted_factor_autocorrelation_congruent_two a b hbn)
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_before a b hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_opposite_before ha hb hk0 hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_before a b.reverse hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift,
          coeff_mul_togglePair_opposite_before ha hb.reverse hk0 hk hi]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift, coeff_mul_togglePair_at a b hk ha.constant,
          int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift, coeff_mul_togglePair_opposite ha hb hk0 hk,
          int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift,
          coeff_mul_togglePair_at a b.reverse hk ha.constant, int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift,
          coeff_mul_togglePair_opposite ha hb.reverse hk0 hk, int_val_add_one_zmod_two]
    _ = _ := by
      rw [asymmetry_product_coeff ha hb (by omega)]
      simp only [coeff_zeroOneLift, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma pairedPolynomial_update {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    pairedPolynomial (Function.update u i (!(u i))) c z =
      togglePair (n + 1) (i.val + 1) (pairedPolynomial u c z) := by
  classical
  have hi := i.isLt
  have ht : 2 * (i.val + 1) < n + 1 := by omega
  apply f2WordPolynomial_ext (pairedPolynomial_endpoints _ c z)
    ((pairedPolynomial_endpoints u c z).togglePair (by omega) ht)
  intro j
  have hj := j.isLt
  by_cases hl : j.val < n / 2
  · let l : Fin (n / 2) := ⟨j.val, hl⟩
    change (pairedPolynomial _ c z).coeff (l.val + 1) = _
    rw [coeff_pairedPolynomial_lower]
    change _ = (togglePair (n + 1) (i.val + 1) (pairedPolynomial u c z)).coeff (l.val + 1)
    simp only [togglePair, coeff_add, coeff_pairedPolynomial_lower, coeff_X_pow]
    have hupper : l.val + 1 ≠ n + 1 - (i.val + 1) := by have := l.isLt; omega
    by_cases hli : l = i
    · rw [hli] at hupper ⊢
      simp only [Function.update_self, bitToF2_not, ite_true,
        if_neg hupper, add_zero]
    · have hlow : l.val + 1 ≠ i.val + 1 := by
        intro h
        exact hli (Fin.ext (by omega))
      simp only [Function.update_of_ne hli, if_neg hlow, if_neg hupper,
        add_zero]
  · by_cases hu : n - (j.val + 1) < n / 2
    · let l : Fin (n / 2) := ⟨n - (j.val + 1), hu⟩
      have heq : j.val + 1 = n + 1 - (l.val + 1) := by dsimp [l]; omega
      rw [heq, coeff_pairedPolynomial_upper]
      simp only [togglePair, coeff_add, coeff_pairedPolynomial_upper, coeff_X_pow]
      have hlower : n + 1 - (l.val + 1) ≠ i.val + 1 := by have := l.isLt; omega
      by_cases hli : l = i
      · rw [hli] at hlower ⊢
        simp only [Function.update_self, bitToF2_not, if_neg hlower,
          ite_true, zero_add]
        rw [add_right_comm]
      · have hupper : n + 1 - (l.val + 1) ≠ n + 1 - (i.val + 1) := by
          intro h
          have := l.isLt
          exact hli (Fin.ext (by omega))
        simp only [Function.update_of_ne hli, if_neg hlower, if_neg hupper,
          add_zero]
    · have heq : j.val + 1 = n / 2 + 1 := by omega
      let l : Fin (n % 2) := ⟨0, by omega⟩
      rw [heq, coeff_pairedPolynomial_center _ c z l]
      simp only [togglePair, coeff_add, coeff_pairedPolynomial_center u c z l, coeff_X_pow]
      have hlower : n / 2 + 1 ≠ i.val + 1 := by omega
      have hupper : n / 2 + 1 ≠ n + 1 - (i.val + 1) := by have := l.isLt; omega
      simp only [if_neg hlower, if_neg hupper, add_zero]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma paired_sum_reverse_eq {n : ℕ} (u u' c : Fin (n / 2) → Bool)
    (z z' : Fin (n % 2) → Bool) :
    pairedPolynomial u c z + (pairedPolynomial u c z).reverse =
      pairedPolynomial u' c z' + (pairedPolynomial u' c z').reverse := by
  have hp := pairedPolynomial_endpoints u c z
  have hq := pairedPolynomial_endpoints u' c z'
  ext k
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [coeff_add, hp.constant, hp.reverse.constant, hq.constant, hq.reverse.constant]
  by_cases hkt : k = n + 1
  · rw [hkt]
    simp only [coeff_add, hp.coeff_degree, hp.reverse.coeff_degree,
      hq.coeff_degree, hq.reverse.coeff_degree]
  by_cases hk : k < n + 1
  · by_cases hl : k - 1 < n / 2
    · let i : Fin (n / 2) := ⟨k - 1, hl⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      rw [← hi, coeff_paired_sum_reverse_lower u c z i,
        coeff_paired_sum_reverse_lower u' c z' i]
    · by_cases hu : n - k < n / 2
      · let i : Fin (n / 2) := ⟨n - k, hu⟩
        have hi : n + 1 - (i.val + 1) = k := by dsimp [i]; omega
        rw [← hi, coeff_paired_sum_reverse_upper u c z i,
          coeff_paired_sum_reverse_upper u' c z' i]
      · have hi : k = n / 2 + 1 := by omega
        let j : Fin (n % 2) := ⟨0, by omega⟩
        rw [hi, coeff_paired_sum_reverse_center u c z j,
          coeff_paired_sum_reverse_center u' c z' j]
  · have hkn : n + 1 < k := by omega
    simp only [coeff_add, hp.coeff_eq_zero_above hkn, hp.reverse.coeff_eq_zero_above hkn,
      hq.coeff_eq_zero_above hkn, hq.reverse.coeff_eq_zero_above hkn]
noncomputable def pairSumPolynomial {n : ℕ} (c : Fin (n / 2) → Bool) : (ZMod 2)[X] :=
  pairedPolynomial (fun _ ↦ false) c (fun _ ↦ false) +
    (pairedPolynomial (fun _ ↦ false) c (fun _ ↦ false)).reverse
lemma paired_sum_reverse_eq_pairSumPolynomial {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) :
    pairedPolynomial u c z + (pairedPolynomial u c z).reverse = pairSumPolynomial c :=
  paired_sum_reverse_eq u (fun _ ↦ false) c z (fun _ ↦ false)
lemma coeff_pairSumPolynomial_lower {n : ℕ} (c : Fin (n / 2) → Bool) (i : Fin (n / 2)) :
    (pairSumPolynomial c).coeff (i.val + 1) = bitToF2 (c i) :=
  coeff_paired_sum_reverse_lower (fun _ ↦ false) c (fun _ ↦ false) i
lemma pairSumPolynomial_injective {n : ℕ} : Function.Injective (@pairSumPolynomial n) := by
  intro c d h
  funext i
  apply bitF2Equiv.injective
  change bitToF2 (c i) = bitToF2 (d i)
  have hi := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff (i.val + 1)) h
  simpa only [coeff_pairSumPolynomial_lower] using hi
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
noncomputable def activeDiscrepancyIndices {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) : Finset (Fin (n / 2)) :=
  Finset.univ.filter (fun i ↦ ((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1) = 1)
lemma pairedDiscrepancy_togglesOn {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    TogglesOn (activeDiscrepancyIndices a c) (pairedDiscrepancy a c z) := by
  classical
  intro i hi u
  have hi1 : ((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1) = 1 :=
    (Finset.mem_filter.mp hi).2
  have ht := autocorrelationDiscrepancy_togglePair ha (pairedPolynomial_endpoints u c z)
    (show 0 < i.val + 1 by omega) (show 2 * (i.val + 1) < n + 1 by have := i.isLt; omega)
  rw [paired_sum_reverse_eq_pairSumPolynomial, hi1] at ht
  have heq := (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  simp only [pairedDiscrepancy, pairedPolynomial_update, heq, f2ToBit_add_one]
lemma paired_discrepancies_zero_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    uniformProbability (fun u : Fin (n / 2) → Bool ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1) = 0) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  have h := uniformProbability_all_outputs_zero_le
    (pairedDiscrepancy_dependsOnPrefix ha c z) (pairedDiscrepancy_togglesOn ha c z)
  simpa only [pairedDiscrepancy, f2ToBit_eq_false_iff] using h
lemma paired_discrepancies_zero_fiber_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) :
    uniformProbability (fun v : (Fin (n % 2) → Bool) × (Fin (n / 2) → Bool) ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial v.2 c v.1) (i.val + 1) = 0) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  rw [uniformProbability_product_eq_average
    (fun (z : Fin (n % 2) → Bool) (u : Fin (n / 2) → Bool) ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1) = 0)]
  exact uniformAverage_le (fun z ↦ paired_discrepancies_zero_probability_le ha c z)
lemma paired_factor_congruence_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    uniformProbability (fun u : Fin (n / 2) → Bool ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * pairedPolynomial u c z)))
        (autocorrelation (zeroOneLift (a * (pairedPolynomial u c z).reverse)))) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  apply le_trans (uniformProbability_mono (fun u h i ↦ ?_))
    (paired_discrepancies_zero_probability_le ha c z)
  have hb : (pairedPolynomial u c z).coeff 0 ≠ 0 := by
    rw [(pairedPolynomial_endpoints u c z).constant]
    exact one_ne_zero
  exact (lifted_factor_congruent_four_iff a _ hb).mp h (i.val + 1)
lemma f2_factor_congruence_probability_le_average {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) :
    f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card) := by
  rw [f2Probability_eq_paired_average]
  apply uniformAverage_mono
  intro c
  exact uniformAverage_le (fun z ↦ paired_factor_congruence_probability_le ha c z)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma bitToF2_eq_zero_iff (b : Bool) : bitToF2 b = 0 ↔ b = false := by
  cases b <;> simp [bitToF2]
lemma bitToF2_eq_one_iff (b : Bool) : bitToF2 b = 1 ↔ b = true := by
  cases b <;> simp [bitToF2]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def FirstTrueAt {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Prop :=
  w i = true ∧ ∀ j < i, w j = false
lemma firstTrueAt_iff_prescribed {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    FirstTrueAt w i ↔ ∀ j ∈ Finset.Iic i, w j = if j = i then true else false := by
  constructor
  · rintro ⟨hi, hprev⟩ j hj
    have hji := Finset.mem_Iic.mp hj
    by_cases heq : j = i
    · simpa only [heq, ite_true] using hi
    · simpa only [if_neg heq] using hprev j (lt_of_le_of_ne hji heq)
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h i (Finset.mem_Iic.mpr le_rfl)
    · intro j hj
      simpa only [if_neg (ne_of_lt hj)] using h j (Finset.mem_Iic.mpr hj.le)
lemma uniformProbability_firstTrueAt {n : ℕ} (i : Fin n) :
    uniformProbability (fun w : Fin n → Bool ↦ FirstTrueAt w i) =
      (1 / 2 : ℝ) ^ (i.val + 1) := by
  simp only [firstTrueAt_iff_prescribed]
  rw [uniformProbability_prescribedBits, Fin.card_Iic]
lemma FirstTrueAt.unique {n : ℕ} {w : Fin n → Bool} {i j : Fin n}
    (hi : FirstTrueAt w i) (hj : FirstTrueAt w j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hf := hj.2 i h
    rw [hi.1] at hf
    contradiction
  · exact h
  · have hf := hi.2 j h
    rw [hj.1] at hf
    contradiction
lemma exists_firstTrueAt_iff {n : ℕ} (w : Fin n → Bool) :
    (∃ i, FirstTrueAt w i) ↔ ¬ ∀ i, w i = false := by
  classical
  constructor
  · rintro ⟨i, hi⟩ h
    have := h i
    rw [hi.1] at this
    contradiction
  · intro h
    have hex : ∃ i, w i = true := by
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      cases heq : w i
      · exact (hi heq).elim
      · rfl
    let s := Finset.univ.filter (fun i ↦ w i = true)
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
    intro j hj
    cases heq : w j
    · rfl
    · have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      exact (not_lt_of_ge (s.min'_le j hmem) hj).elim
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def FirstAsymmetryAt (p : (ZMod 2)[X]) (j : ℕ) : Prop :=
  (p + p.reverse).coeff j = 1 ∧ ∀ k < j, (p + p.reverse).coeff k = 0
lemma firstAsymmetryAt_paired_iff {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    FirstAsymmetryAt (pairedPolynomial u c z) (i.val + 1) ↔ FirstTrueAt c i := by
  constructor
  · rintro ⟨hi, hprev⟩
    rw [coeff_paired_sum_reverse_lower, bitToF2_eq_one_iff] at hi
    refine ⟨hi, ?_⟩
    intro j hj
    apply (bitToF2_eq_zero_iff _).mp
    rw [← coeff_paired_sum_reverse_lower u c z j]
    exact hprev (j.val + 1) (by have : j.val < i.val := hj; omega)
  · rintro ⟨hi, hprev⟩
    refine ⟨?_, ?_⟩
    · rw [coeff_paired_sum_reverse_lower, bitToF2_eq_one_iff]
      exact hi
    · intro k hk
      by_cases hk0 : k = 0
      · rw [hk0, coeff_add, (pairedPolynomial_endpoints u c z).constant,
          (pairedPolynomial_endpoints u c z).reverse.constant]
        exact CharTwo.add_self_eq_zero _
      · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
        have hj : j.val + 1 = k := by dsimp [j]; omega
        rw [← hj, coeff_paired_sum_reverse_lower, bitToF2_eq_zero_iff]
        apply hprev j
        change j.val < i.val
        dsimp [j]
        omega
lemma FirstAsymmetryAt.unique {p : (ZMod 2)[X]} {i j : ℕ}
    (hi : FirstAsymmetryAt p i) (hj : FirstAsymmetryAt p j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hf := hj.2 i h
    rw [hi.1] at hf
    exact (one_ne_zero hf).elim
  · exact h
  · have hf := hi.2 j h
    rw [hj.1] at hf
    exact (one_ne_zero hf).elim
lemma FirstAsymmetryAt.ne_reverse {p : (ZMod 2)[X]} {j : ℕ}
    (h : FirstAsymmetryAt p j) : p ≠ p.reverse := by
  intro hp
  have hi := h.1
  rw [← hp, CharTwo.add_self_eq_zero, coeff_zero] at hi
  exact zero_ne_one hi
lemma HasF2Endpoints.exists_firstAsymmetry {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) (hne : p ≠ p.reverse) :
    ∃ i : Fin (n / 2), FirstAsymmetryAt p (i.val + 1) := by
  obtain ⟨w, rfl⟩ := exists_f2WordPolynomial_eq hp
  let v := oppositeWordEquiv n w
  have hw : pairedPolynomial v.2.2 v.1 v.2.1 = f2WordPolynomial w := by
    change f2WordPolynomial ((oppositeWordEquiv n).symm (oppositeWordEquiv n w)) = _
    rw [Equiv.symm_apply_apply]
  have hc : ¬ ∀ i, v.1 i = false := by
    intro hc
    have hr := (pairedPolynomial_reverse_eq_iff v.2.2 v.1 v.2.1).mpr hc
    rw [hw] at hr
    exact hne hr.symm
  obtain ⟨i, hi⟩ := (exists_firstTrueAt_iff v.1).mpr hc
  refine ⟨i, ?_⟩
  rw [← hw]
  exact (firstAsymmetryAt_paired_iff v.2.2 v.1 v.2.1 i).mpr hi
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma exists_X_pow_factor_of_initial_one {R : Type*} [Semiring R]
    {p : R[X]} {j : ℕ} (hprev : ∀ k < j, p.coeff k = 0) (hj : p.coeff j = 1) :
    ∃ q : R[X], p = X ^ j * q ∧ q.coeff 0 = 1 := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hprev
  refine ⟨q, hq, ?_⟩
  have h := coeff_X_pow_mul q j 0
  rw [zero_add, ← hq, hj] at h
  exact h.symm
lemma coeff_mul_zero_through_initial {R : Type*} [Semiring R]
    {p c : R[X]} {j k : ℕ} (hprev : ∀ i < j, p.coeff i = 0)
    (hc : c.coeff 0 = 0) (hk : k ≤ j) : (p * c).coeff k = 0 := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hprev
  rw [hq, mul_assoc, coeff_X_pow_mul']
  by_cases hjk : j ≤ k
  · have heq : k = j := by omega
    simp only [heq, Nat.sub_self, mul_coeff_zero, hc, mul_zero, ite_self]
  · exact if_neg hjk
lemma coeff_mul_after_X_pow_factor {R : Type*} [Semiring R]
    {p q : R[X]} (c : R[X]) {j : ℕ} (h : p = X ^ j * q) (r : ℕ) :
    (p * c).coeff (j + r) = (q * c).coeff r := by
  rw [h, mul_assoc, Nat.add_comm j r, coeff_X_pow_mul]
lemma coeff_mul_constant_one {R : Type*} [CommSemiring R]
    (q c : R[X]) (hq : q.coeff 0 = 1) (k : ℕ) :
    (q * c).coeff k = c.coeff k + ∑ i ∈ Finset.range k, c.coeff i * q.coeff (k - i) := by
  rw [mul_comm q c, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ c.coeff i * q.coeff j),
    Finset.sum_range_succ]
  simp only [Nat.sub_self, hq, mul_one]
  exact add_comm _ _
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
noncomputable def f2InteriorPolynomial {m : ℕ} (w : Fin m → Bool) : (ZMod 2)[X] :=
  reducePolynomial 2 (interiorPolynomial w)
lemma coeff_f2InteriorPolynomial {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (f2InteriorPolynomial w).coeff (i.val + 1) = bitToF2 (w i) := by
  rw [f2InteriorPolynomial, coeff_reducePolynomial, coeff_interiorPolynomial,
    ← bitToF2_eq_int_cast]
lemma coeff_f2InteriorPolynomial_outside {m : ℕ} (w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (f2InteriorPolynomial w).coeff k = 0 := by
  rw [f2InteriorPolynomial, coeff_reducePolynomial, coeff_interiorPolynomial_outside w k hk,
    Int.cast_zero]
lemma coeff_f2InteriorPolynomial_zero {m : ℕ} (w : Fin m → Bool) :
    (f2InteriorPolynomial w).coeff 0 = 0 :=
  coeff_f2InteriorPolynomial_outside w 0 (Or.inl rfl)
lemma f2InteriorPolynomial_prefix {m : ℕ} {v w : Fin m → Bool} {i : Fin m}
    (h : ∀ j < i, v j = w j) {k : ℕ} (hk : k < i.val + 1) :
    (f2InteriorPolynomial v).coeff k = (f2InteriorPolynomial w).coeff k := by
  by_cases hk0 : k = 0
  · rw [hk0, coeff_f2InteriorPolynomial_zero, coeff_f2InteriorPolynomial_zero]
  · let j : Fin m := ⟨k - 1, by have := i.isLt; omega⟩
    have hj : j.val + 1 = k := by dsimp [j]; omega
    rw [← hj, coeff_f2InteriorPolynomial, coeff_f2InteriorPolynomial]
    congr 1
    apply h j
    change j.val < i.val
    dsimp [j]
    omega
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
def trueBitCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i ↦ w i = true)).card
lemma pow_trueBitCount_eq_prod {n : ℕ} (w : Fin n → Bool) (t : ℝ) :
    t ^ trueBitCount w = ∏ i, if w i then t else 1 := by
  simp [trueBitCount, Finset.prod_ite]
lemma sum_pow_trueBitCount (n : ℕ) (t : ℝ) :
    (∑ w : Fin n → Bool, t ^ trueBitCount w) = (1 + t) ^ n := by
  have h := Finset.sum_prod_piFinset (ι := Fin n) (Finset.univ : Finset Bool)
    (fun _ b ↦ if b then t else 1)
  rw [Fintype.piFinset_univ] at h
  simpa [pow_trueBitCount_eq_prod, add_comm] using h
lemma uniformAverage_pow_trueBitCount (n : ℕ) (t : ℝ) :
    uniformAverage (fun w : Fin n → Bool ↦ t ^ trueBitCount w) =
      ((1 + t) / 2) ^ n := by
  rw [uniformAverage, sum_pow_trueBitCount]
  simp [div_pow]
lemma uniformAverage_half_pow_trueBitCount (n : ℕ) :
    uniformAverage (fun w : Fin n → Bool ↦ (1 / 2 : ℝ) ^ trueBitCount w) =
      (3 / 4 : ℝ) ^ n := by
  rw [uniformAverage_pow_trueBitCount]
  norm_num
lemma uniformAverage_triangular_half_weight {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t) :
    uniformAverage (fun w : Fin n → Bool ↦
      (1 / 2 : ℝ) ^ trueBitCount (triangularBitMap t w)) = (3 / 4 : ℝ) ^ n :=
  (uniformAverage_bijective (triangularBitMap_bijective ht)
    (fun w ↦ (1 / 2 : ℝ) ^ trueBitCount w)).trans
    (uniformAverage_half_pow_trueBitCount n)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma f2ToBit_add (x y : ZMod 2) : f2ToBit (x + y) = Bool.xor (f2ToBit x) (f2ToBit y) := by
  apply bitF2Equiv.injective
  change bitToF2 (f2ToBit (x + y)) = bitToF2 (Bool.xor (f2ToBit x) (f2ToBit y))
  rw [bitToF2_f2ToBit, bitToF2_xor, bitToF2_f2ToBit, bitToF2_f2ToBit]
noncomputable def coefficientConvolution {m : ℕ} (q : (ZMod 2)[X])
    (w : Fin m → Bool) (i : Fin m) : Bool :=
  f2ToBit ((q * f2InteriorPolynomial w).coeff (i.val + 1))
noncomputable def coefficientConvolutionCorrection {m : ℕ} (q : (ZMod 2)[X])
    (w : Fin m → Bool) (i : Fin m) : Bool :=
  f2ToBit (∑ k ∈ Finset.range (i.val + 1),
    (f2InteriorPolynomial w).coeff k * q.coeff (i.val + 1 - k))
lemma coefficientConvolutionCorrection_dependsOnEarlier {m : ℕ} (q : (ZMod 2)[X]) :
    DependsOnEarlier (@coefficientConvolutionCorrection m q) := by
  intro i v w h
  apply congrArg f2ToBit
  apply Finset.sum_congr rfl
  intro k hk
  rw [f2InteriorPolynomial_prefix h (Finset.mem_range.mp hk)]
lemma coefficientConvolution_eq_triangular {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) (w : Fin m → Bool) :
    coefficientConvolution q w = triangularBitMap (coefficientConvolutionCorrection q) w := by
  funext i
  unfold coefficientConvolution triangularBitMap coefficientConvolutionCorrection
  rw [coeff_mul_constant_one q _ hq, coeff_f2InteriorPolynomial, f2ToBit_add,
    f2ToBit_bitToF2]
lemma coefficientConvolution_bijective {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) : Function.Bijective (@coefficientConvolution m q) := by
  have heq : @coefficientConvolution m q = triangularBitMap (coefficientConvolutionCorrection q) :=
    funext (coefficientConvolution_eq_triangular hq)
  rw [heq]
  exact triangularBitMap_bijective (coefficientConvolutionCorrection_dependsOnEarlier q)
lemma uniformAverage_coefficientConvolution_half_weight {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) :
    uniformAverage (fun w : Fin m → Bool ↦
      (1 / 2 : ℝ) ^ trueBitCount (coefficientConvolution q w)) = (3 / 4 : ℝ) ^ m := by
  simp only [coefficientConvolution_eq_triangular hq]
  exact uniformAverage_triangular_half_weight (coefficientConvolutionCorrection_dependsOnEarlier q)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def wordPrefix {m r : ℕ} (hr : r ≤ m) (w : Fin m → Bool) : Fin r → Bool :=
  fun i ↦ w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
def prefixWordEquiv {m r : ℕ} (hr : r ≤ m) :
    (Fin m → Bool) ≃ (Fin r → Bool) × (Fin (m - r) → Bool) where
  toFun w := ⟨wordPrefix hr w, fun i ↦ w ⟨r + i.val, by have := i.isLt; omega⟩⟩
  invFun v i := if hi : i.val < r then v.1 ⟨i.val, hi⟩
    else v.2 ⟨i.val - r, by have := i.isLt; omega⟩
  left_inv w := by
    funext i
    dsimp only [wordPrefix]
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      dsimp only
      omega
  right_inv v := by
    apply Prod.ext
    · funext i
      dsimp only [wordPrefix]
      split
      · rfl
      · rename_i h
        exact (h i.isLt).elim
    · funext i
      dsimp only
      rw [dif_neg (show ¬ r + i.val < r by omega)]
      apply congrArg v.2
      apply Fin.ext
      dsimp only
      omega
lemma uniformAverage_wordPrefix {m r : ℕ} (hr : r ≤ m) (f : (Fin r → Bool) → ℝ) :
    uniformAverage (fun w : Fin m → Bool ↦ f (wordPrefix hr w)) = uniformAverage f := by
  calc
    _ = uniformAverage (fun v : (Fin r → Bool) × (Fin (m - r) → Bool) ↦ f v.1) :=
      uniformAverage_equiv (prefixWordEquiv hr) (fun v ↦ f v.1)
    _ = _ := by
      rw [uniformAverage_product (fun (v : Fin r → Bool) (_ : Fin (m - r) → Bool) ↦ f v)]
      simp only [uniformAverage_const]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma coeff_pairSumPolynomial_zero {n : ℕ} (c : Fin (n / 2) → Bool) :
    (pairSumPolynomial c).coeff 0 = 0 := by
  unfold pairSumPolynomial
  rw [coeff_add, (pairedPolynomial_endpoints _ c _).constant,
    (pairedPolynomial_endpoints _ c _).reverse.constant]
  exact CharTwo.add_self_eq_zero _
lemma pairSumPolynomial_prefix {n r : ℕ} (hr : r ≤ n / 2) (c : Fin (n / 2) → Bool)
    {k : ℕ} (hk : k ≤ r) :
    (pairSumPolynomial c).coeff k = (f2InteriorPolynomial (wordPrefix hr c)).coeff k := by
  by_cases hk0 : k = 0
  · rw [hk0, coeff_pairSumPolynomial_zero, coeff_f2InteriorPolynomial_zero]
  · let i : Fin r := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [← hi, coeff_f2InteriorPolynomial]
    change (pairSumPolynomial c).coeff (i.val + 1) =
      bitToF2 (c ⟨i.val, lt_of_lt_of_le i.isLt hr⟩)
    exact coeff_pairSumPolynomial_lower c ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
end OdlyzkoPoonen

namespace OdlyzkoPoonen
def shiftedWordIndex {m j : ℕ} (hj : j ≤ m) (i : Fin (m - j)) : Fin m :=
  ⟨j + i.val, by have := i.isLt; omega⟩
lemma shiftedWordIndex_injective {m j : ℕ} (hj : j ≤ m) :
    Function.Injective (shiftedWordIndex hj) := by
  intro i k h
  apply Fin.ext
  have hval := congrArg Fin.val h
  change j + i.val = j + k.val at hval
  omega
lemma trueBitCount_eq_shifted {m j : ℕ} (hj : j ≤ m) (w : Fin m → Bool)
    (hzero : ∀ i : Fin m, i.val < j → w i = false) :
    trueBitCount w = trueBitCount (fun i : Fin (m - j) ↦ w (shiftedWordIndex hj i)) := by
  classical
  unfold trueBitCount
  symm
  apply Finset.card_bij (fun i _ ↦ shiftedWordIndex hj i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ k _ h
    exact shiftedWordIndex_injective hj h
  · intro i hi
    have htrue := (Finset.mem_filter.mp hi).2
    have hji : j ≤ i.val := by
      by_contra h
      have hf := hzero i (by omega)
      rw [htrue] at hf
      contradiction
    let k : Fin (m - j) := ⟨i.val - j, by have := i.isLt; omega⟩
    have heq : shiftedWordIndex hj k = i := by
      apply Fin.ext
      dsimp [shiftedWordIndex, k]
      omega
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    change w (shiftedWordIndex hj k) = true
    rw [heq]
    exact htrue
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
noncomputable def exposureSlopeWord {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) (i : Fin (n / 2)) : Bool :=
  f2ToBit (((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1))
lemma activeDiscrepancyIndices_card {n : ℕ} (a : (ZMod 2)[X]) (c : Fin (n / 2) → Bool) :
    (activeDiscrepancyIndices a c).card = trueBitCount (exposureSlopeWord a c) := by
  simp only [activeDiscrepancyIndices, trueBitCount, exposureSlopeWord, f2ToBit_eq_true_iff]
lemma exposureSlopeWord_zero_before {n j : ℕ} {a : (ZMod 2)[X]}
    (ha : FirstAsymmetryAt a j) (c : Fin (n / 2) → Bool) {i : Fin (n / 2)}
    (hi : i.val + 1 ≤ j) : exposureSlopeWord a c i = false := by
  apply (f2ToBit_eq_false_iff _).mpr
  exact coeff_mul_zero_through_initial ha.2 (coeff_pairSumPolynomial_zero c) hi
lemma exposureSlopeWord_shifted {n j : ℕ} {a q : (ZMod 2)[X]}
    (hj : j ≤ n / 2) (hfactor : a + a.reverse = X ^ j * q)
    (c : Fin (n / 2) → Bool) (i : Fin (n / 2 - j)) :
    exposureSlopeWord a c (shiftedWordIndex hj i) =
      coefficientConvolution q (wordPrefix (Nat.sub_le (n / 2) j) c) i := by
  apply congrArg f2ToBit
  change ((a + a.reverse) * pairSumPolynomial c).coeff (j + i.val + 1) =
    (q * f2InteriorPolynomial (wordPrefix (Nat.sub_le (n / 2) j) c)).coeff (i.val + 1)
  rw [Nat.add_assoc, coeff_mul_after_X_pow_factor _ hfactor]
  apply coeff_mul_right_eq_of_prefix
  intro k hk
  apply pairSumPolynomial_prefix
  have := i.isLt
  omega
lemma uniformAverage_active_discrepancy_weight {n j : ℕ} {a : (ZMod 2)[X]}
    (ha : FirstAsymmetryAt a j) (hj : j ≤ n / 2) :
    uniformAverage (fun c : Fin (n / 2) → Bool ↦
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card) = (3 / 4 : ℝ) ^ (n / 2 - j) := by
  obtain ⟨q, hfactor, hq⟩ := exists_X_pow_factor_of_initial_one ha.2 ha.1
  have hcount (c : Fin (n / 2) → Bool) :
      (activeDiscrepancyIndices a c).card =
        trueBitCount (coefficientConvolution q (wordPrefix (Nat.sub_le (n / 2) j) c)) := by
    rw [activeDiscrepancyIndices_card, trueBitCount_eq_shifted hj _
      (fun i hi ↦ exposureSlopeWord_zero_before ha c (by omega))]
    congr 1
    funext i
    exact exposureSlopeWord_shifted hj hfactor c i
  simp only [hcount]
  exact (uniformAverage_wordPrefix (Nat.sub_le (n / 2) j)
    (fun w : Fin (n / 2 - j) → Bool ↦ (1 / 2 : ℝ) ^ trueBitCount (coefficientConvolution q w))).trans
    (uniformAverage_coefficientConvolution_half_weight hq)
lemma f2_factor_congruence_probability_le_of_firstAsymmetry {d n j : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hfirst : FirstAsymmetryAt a j) (hj : j ≤ n / 2) :
    f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤ (3 / 4 : ℝ) ^ (n / 2 - j) :=
  (f2_factor_congruence_probability_le_average ha).trans_eq
    (uniformAverage_active_discrepancy_weight hfirst hj)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma f2Probability_firstAsymmetryAt {n : ℕ} (i : Fin (n / 2)) :
    f2Probability n (fun p ↦ FirstAsymmetryAt p (i.val + 1)) =
      (1 / 2 : ℝ) ^ (i.val + 1) := by
  rw [f2Probability_eq_paired_average]
  simp only [firstAsymmetryAt_paired_iff]
  simp_rw [uniformProbability_eq_average_indicator, uniformAverage_const]
  rw [← uniformProbability_eq_average_indicator, uniformProbability_firstTrueAt]
lemma HasF2Endpoints.exists_firstAsymmetry_range {d : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints d p) (hd : 0 < d) (hne : p ≠ p.reverse) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ (d - 1) / 2 ∧ FirstAsymmetryAt p j := by
  cases d with
  | zero => omega
  | succ n =>
    obtain ⟨i, hi⟩ := hp.exists_firstAsymmetry hne
    exact ⟨i.val + 1, by omega, by have := i.isLt; omega, hi⟩
lemma f2Probability_firstAsymmetryAt_of_range {n j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ n / 2) :
    f2Probability n (fun p ↦ FirstAsymmetryAt p j) = (1 / 2 : ℝ) ^ j := by
  let i : Fin (n / 2) := ⟨j - 1, by omega⟩
  have hi : i.val + 1 = j := by dsimp [i]; omega
  simpa only [hi] using f2Probability_firstAsymmetryAt i
lemma HasF2Endpoints.reverse_eq_of_degree_le_two {d : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints d p) (hd0 : 0 < d) (hd : d ≤ 2) : p.reverse = p := by
  by_contra h
  obtain ⟨j, hj0, hj, _⟩ := hp.exists_firstAsymmetry_range hd0 (Ne.symm h)
  omega
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma asymmetry_weight_factor {m j : ℕ} (hj : j ≤ m) :
    (1 / 2 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j) =
      (3 / 4 : ℝ) ^ m * (2 / 3 : ℝ) ^ j := by
  have h : (1 / 2 : ℝ) = (3 / 4) * (2 / 3) := by norm_num
  rw [h, mul_pow, mul_right_comm, ← pow_add, show j + (m - j) = m by omega]
lemma sum_two_thirds_positive (s : ℕ) :
    (∑ i ∈ Finset.range s, (2 / 3 : ℝ) ^ (i + 1)) = 2 * (1 - (2 / 3 : ℝ) ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring
lemma sum_two_thirds_positive_le_two (s : ℕ) :
    (∑ i : Fin s, (2 / 3 : ℝ) ^ (i.val + 1)) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (2 / 3 : ℝ) ^ (i + 1)) s,
    sum_two_thirds_positive]
  have h : 0 ≤ (2 / 3 : ℝ) ^ s := by positivity
  linarith
lemma asymmetry_geometric_sum_le {s m : ℕ} (hs : s ≤ m) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1) * (3 / 4 : ℝ) ^ (m - (i.val + 1))) ≤
      2 * (3 / 4 : ℝ) ^ m := by
  have hterm (i : Fin s) : i.val + 1 ≤ m := by have := i.isLt; omega
  simp_rw [asymmetry_weight_factor (hterm _)]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (3 / 4 : ℝ) ^ m * 2 := mul_le_mul_of_nonneg_left (sum_two_thirds_positive_le_two s) (by positivity)
    _ = _ := mul_comm _ _
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma f2PairProbability_first_asymmetry_contribution {s n : ℕ}
    (i : Fin (s / 2)) (hi : i.val + 1 ≤ n / 2) :
    f2PairProbability s n (fun a b ↦ FirstAsymmetryAt a (i.val + 1) ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      (1 / 2 : ℝ) ^ (i.val + 1) * (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
  let F (u : Fin s → Bool) : Prop := FirstAsymmetryAt (f2WordPolynomial u) (i.val + 1)
  let C (u : Fin s → Bool) (v : Fin n → Bool) : Prop :=
    CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * f2WordPolynomial v)))
      (autocorrelation (zeroOneLift (f2WordPolynomial u * (f2WordPolynomial v).reverse)))
  have hfiber (u : Fin s → Bool) (hu : F u) :
      uniformProbability (C u) ≤ (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
    change f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * b)))
        (autocorrelation (zeroOneLift (f2WordPolynomial u * b.reverse)))) ≤ _
    exact f2_factor_congruence_probability_le_of_firstAsymmetry
      (f2WordPolynomial_endpoints u) hu hi
  have hprob : uniformProbability F = (1 / 2 : ℝ) ^ (i.val + 1) := by
    change f2Probability s (fun a ↦ FirstAsymmetryAt a (i.val + 1)) = _
    exact f2Probability_firstAsymmetryAt i
  have h := uniformProbability_product_bound F C
    ((3 / 4 : ℝ) ^ (n / 2 - (i.val + 1))) hfiber
  rw [hprob] at h
  exact h
lemma f2PairProbability_factor_congruence_le {s n : ℕ} (hs : s ≤ n) :
    f2PairProbability s n (fun a b ↦ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      2 * (3 / 4 : ℝ) ^ (n / 2) := by
  classical
  unfold f2PairProbability
  let C (u : Fin s → Bool) (v : Fin n → Bool) : Prop :=
    CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * f2WordPolynomial v)))
      (autocorrelation (zeroOneLift (f2WordPolynomial u * (f2WordPolynomial v).reverse)))
  let F (i : Fin (s / 2)) (u : Fin s → Bool) : Prop :=
    FirstAsymmetryAt (f2WordPolynomial u) (i.val + 1)
  have hhalf : s / 2 ≤ n / 2 := Nat.div_le_div_right hs
  change uniformProbability (fun v : (Fin s → Bool) × (Fin n → Bool) ↦
    f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧ C v.1 v.2) ≤ _
  calc
    _ ≤ uniformProbability (fun v : (Fin s → Bool) × (Fin n → Bool) ↦
        ∃ i : Fin (s / 2), F i v.1 ∧ C v.1 v.2) := by
      apply uniformProbability_mono
      intro v hv
      obtain ⟨i, hi⟩ := (f2WordPolynomial_endpoints v.1).exists_firstAsymmetry hv.1
      exact ⟨i, hi, hv.2⟩
    _ ≤ ∑ i : Fin (s / 2), uniformProbability
        (fun v : (Fin s → Bool) × (Fin n → Bool) ↦ F i v.1 ∧ C v.1 v.2) :=
      uniformProbability_exists_le_sum
        (fun (i : Fin (s / 2)) (v : (Fin s → Bool) × (Fin n → Bool)) ↦ F i v.1 ∧ C v.1 v.2)
    _ ≤ ∑ i : Fin (s / 2), (1 / 2 : ℝ) ^ (i.val + 1) *
        (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : i.val + 1 ≤ n / 2 := by have := i.isLt; omega
      simpa only [f2PairProbability, F, C] using
        f2PairProbability_first_asymmetry_contribution (n := n) i hi
    _ ≤ _ := asymmetry_geometric_sum_le hhalf
theorem factor_pair_congruence_probability (d e : ℕ) (hd : 1 ≤ d) (hde : d ≤ e) :
    f2PairProbability (d - 1) (e - 1) (fun a b ↦ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      2 * (3 / 4 : ℝ) ^ ((e - 1) / 2) := by
  exact f2PairProbability_factor_congruence_le (by omega)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma uniformProbability_exists_image_le {α β γ : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → γ) (g : β → γ) (hg : Function.Injective g) (E : α → Prop) :
    uniformProbability (fun b : β ↦ ∃ a : α, E a ∧ g b = f a) ≤
      uniformProbability E * ((Fintype.card α : ℝ) / Fintype.card β) := by
  classical
  letI : DecidablePred E := fun _ ↦ Classical.propDecidable _
  letI : DecidablePred (fun b : β ↦ ∃ a : α, E a ∧ g b = f a) :=
    fun _ ↦ Classical.propDecidable _
  have hcard : (Finset.univ.filter (fun b : β ↦ ∃ a : α, E a ∧ g b = f a)).card ≤
      (Finset.univ.filter E).card := by
    calc
      _ = ((Finset.univ.filter (fun b : β ↦ ∃ a : α, E a ∧ g b = f a)).image g).card :=
        (Finset.card_image_of_injective _ hg).symm
      _ ≤ ((Finset.univ.filter E).image f).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨a, ha, heq⟩ := (Finset.mem_filter.mp hb).2
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, heq.symm⟩
      _ ≤ _ := Finset.card_image_le
  unfold uniformProbability
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ ((Finset.univ.filter E).card : ℝ) / Fintype.card β :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = _ := by field_simp
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
def HasFactorWitness (d e : ℕ) (p : ℤ[X]) : Prop :=
  ∃ a b : (ZMod 2)[X], HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
    p = zeroOneLift (a * b) ∧ a ≠ a.reverse ∧
    CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse)))
lemma hasFactorWitness_iff_words {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (p : ℤ[X]) :
    HasFactorWitness d e p ↔
      ∃ v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool),
        (f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧
          CongruentMod 4
            (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)))
            (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * (f2WordPolynomial v.2).reverse)))) ∧
        p = zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2) := by
  constructor
  · rintro ⟨a, b, ha, hb, hp, hna, hcong⟩
    have ha' : HasF2Endpoints ((d - 1) + 1) a := by simpa only [Nat.sub_add_cancel hd] using ha
    have hb' : HasF2Endpoints ((e - 1) + 1) b := by simpa only [Nat.sub_add_cancel he] using hb
    obtain ⟨u, rfl⟩ := exists_f2WordPolynomial_eq ha'
    obtain ⟨v, rfl⟩ := exists_f2WordPolynomial_eq hb'
    exact ⟨⟨u, v⟩, ⟨hna, hcong⟩, hp⟩
  · rintro ⟨⟨u, v⟩, ⟨hna, hcong⟩, hp⟩
    refine ⟨f2WordPolynomial u, f2WordPolynomial v, ?_, ?_, hp, hna, hcong⟩
    · simpa only [Nat.sub_add_cancel hd] using f2WordPolynomial_endpoints u
    · simpa only [Nat.sub_add_cancel he] using f2WordPolynomial_endpoints v
lemma factor_pair_word_card_ratio {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (Fintype.card ((Fin (d - 1) → Bool) × (Fin (e - 1) → Bool)) : ℝ) /
      Fintype.card (Fin (d + e - 1) → Bool) = (1 / 2 : ℝ) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, show d + e - 1 = (d - 1 + (e - 1)) + 1 by omega, pow_succ]
  field_simp
lemma binaryProbability_factor_witness_le {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    binaryProbability (d + e - 1) (HasFactorWitness d e) ≤
      (3 / 4 : ℝ) ^ ((e - 1) / 2) := by
  have he : 1 ≤ e := hd.trans hde
  let E (v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool)) : Prop :=
    f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧
      CongruentMod 4
        (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)))
        (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * (f2WordPolynomial v.2).reverse)))
  have hbound := uniformProbability_exists_image_le
    (fun v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool) ↦
      zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2))
    (@wordPolynomial (d + e - 1)) wordPolynomial_injective E
  rw [factor_pair_word_card_ratio hd he] at hbound
  have hevent : binaryProbability (d + e - 1) (HasFactorWitness d e) =
      uniformProbability (fun w : Fin (d + e - 1) → Bool ↦
        ∃ v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool),
          E v ∧ wordPolynomial w = zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)) := by
    unfold binaryProbability
    congr 1
    funext w
    exact propext (hasFactorWitness_iff_words hd he (wordPolynomial w))
  have hpair : uniformProbability E ≤ 2 * (3 / 4 : ℝ) ^ ((e - 1) / 2) :=
    factor_pair_congruence_probability d e hd hde
  rw [hevent]
  calc
    _ ≤ uniformProbability E * (1 / 2 : ℝ) := hbound
    _ ≤ (2 * (3 / 4 : ℝ) ^ ((e - 1) / 2)) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hpair (by norm_num)
    _ = _ := by ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
lemma HasModFourCompanion.exists_factor_witness {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcomp : HasModFourCompanion n p) :
    ∃ i : Fin (n / 2), HasFactorWitness (i.val + 1) (n - (i.val + 1)) p := by
  obtain ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hpab, hna, hcong⟩ := hcomp.factorization hp
  let i : Fin (n / 2) := ⟨d - 1, by omega⟩
  have hi : i.val + 1 = d := by dsimp [i]; omega
  have he : n - (i.val + 1) = e := by omega
  refine ⟨i, ?_⟩
  rw [hi, show n - d = e by omega]
  exact ⟨a, b, ha, hb, hpab, hna, hcong⟩
lemma binaryProbability_companion_le_split_sum (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
      ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2) := by
  unfold binaryProbability
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ i : Fin (n / 2), HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w)) := by
      apply uniformProbability_mono
      intro w hw
      have hp : HasBinaryEndpoints n (wordPolynomial w) := by
        simpa only [Nat.sub_add_cancel hn] using wordPolynomial_endpoints w
      exact hw.exists_factor_witness hp
    _ ≤ ∑ i : Fin (n / 2), uniformProbability (fun w : Fin (n - 1) → Bool ↦
        HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w)) :=
      uniformProbability_exists_le_sum
        (fun (i : Fin (n / 2)) (w : Fin (n - 1) → Bool) ↦
          HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := i.isLt
      have hd : 1 ≤ i.val + 1 := by omega
      have hde : i.val + 1 ≤ n - (i.val + 1) := by omega
      have hsum : i.val + 1 + (n - (i.val + 1)) = n := by omega
      have hbound := binaryProbability_factor_witness_le hd hde
      rw [hsum] at hbound
      exact hbound
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma sum_range_floor_half_even (s : ℕ) (q : ℝ) :
    (∑ i ∈ Finset.range (2 * s), q ^ (i / 2)) = 2 * ∑ i ∈ Finset.range s, q ^ i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show (2 * s + 1) / 2 = s by omega, show (2 * s) / 2 = s by omega,
      Finset.sum_range_succ]
    ring
lemma sum_three_quarters_range (s : ℕ) :
    (∑ i ∈ Finset.range s, (3 / 4 : ℝ) ^ i) = 4 * (1 - (3 / 4 : ℝ) ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring
lemma sum_floor_half_three_quarters_le_eight (s : ℕ) :
    (∑ i : Fin s, (3 / 4 : ℝ) ^ (i.val / 2)) ≤ 8 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (3 / 4 : ℝ) ^ (i / 2)) s]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 * s), (3 / 4 : ℝ) ^ (i / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ ↦ by positivity)
    _ = 2 * ∑ i ∈ Finset.range s, (3 / 4 : ℝ) ^ i := sum_range_floor_half_even s _
    _ ≤ 8 := by
      rw [sum_three_quarters_range]
      have h : 0 ≤ (3 / 4 : ℝ) ^ s := by positivity
      linarith
lemma companion_split_exponent_lower {n : ℕ} (i : Fin (n / 2)) :
    (n - 1) / 4 ≤ (n - (i.val + 1) - 1) / 2 := by
  have := i.isLt
  omega
lemma companion_split_exponent_reversed {n : ℕ} (i : Fin (n / 2)) :
    (n - 1) / 4 + i.val / 2 ≤ (n - (i.rev.val + 1) - 1) / 2 := by
  rw [Fin.val_rev]
  have := i.isLt
  omega
lemma companion_split_exponent_fiber_card_le_two (n k : ℕ) :
    (Finset.univ.filter (fun i : Fin (n / 2) ↦ (n - (i.val + 1) - 1) / 2 = k)).card ≤ 2 := by
  classical
  let f : Fin (n / 2) → ℕ := fun i ↦ n - (i.val + 1) - 1
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    dsimp [f] at h
    omega
  have hsub : (Finset.univ.filter (fun i : Fin (n / 2) ↦ f i / 2 = k)).image f ⊆
      {2 * k, 2 * k + 1} := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    have heq : f i = 2 * k ∨ f i = 2 * k + 1 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using heq
  calc
    _ = ((Finset.univ.filter (fun i : Fin (n / 2) ↦ f i / 2 = k)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ ({2 * k, 2 * k + 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 2 := by simp
lemma companion_split_sum_le_eight (n : ℕ) :
    (∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2)) ≤
      8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  have hrev := Equiv.sum_comp (@Fin.revPerm (n / 2))
    (fun i : Fin (n / 2) ↦ (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2))
  rw [← hrev]
  calc
    _ ≤ ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - 1) / 4 + i.val / 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (companion_split_exponent_reversed i)
    _ = (3 / 4 : ℝ) ^ ((n - 1) / 4) * ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ (i.val / 2) := by
      simp only [pow_add, Finset.mul_sum]
    _ ≤ (3 / 4 : ℝ) ^ ((n - 1) / 4) * 8 :=
      mul_le_mul_of_nonneg_left (sum_floor_half_three_quarters_le_eight _) (by positivity)
    _ = _ := mul_comm _ _
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma companion_split_sum_eq_Icc (n : ℕ) :
    (∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2)) =
      ∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2) := by
  symm
  have hset : Finset.Icc 1 (n / 2) = Finset.Ico 1 (n / 2 + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range
    (fun d : ℕ ↦ (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) 1 (n / 2 + 1), Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (3 / 4 : ℝ) ^ ((n - (i + 1) - 1) / 2)) (n / 2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm 1 i]
theorem mod_four_companion_probability (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
        (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ∧
      (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ≤
        8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  rw [← companion_split_sum_eq_Icc]
  exact ⟨binaryProbability_companion_le_split_sum n hn, companion_split_sum_le_eight n⟩
lemma mod_four_companion_probability_le (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
      8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) :=
  (mod_four_companion_probability n hn).1.trans (mod_four_companion_probability n hn).2
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma reducible_without_cyclotomic_probability_le {n : ℕ} (hn : 1 ≤ n) :
    binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) ≤
      binaryProbability (n - 1) (HasModFourCompanion n) +
        binaryProbability (n - 1) (fun p ↦
          HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p) := by
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦ HasModFourCompanion n p ∨
        (HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p)) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      rcases hp.companion_or_reciprocal_of_reducible hn hw.1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hw.2⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _
lemma reducible_sub_minus_one_probability_eq {n : ℕ} (hn : 2 ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) =
        binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ p.eval (-1) ≠ 0) := by
  apply uniformProbability_sub_of_imp
  intro w hw
  have hp := wordPolynomial_endpoints w
  rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hp
  exact hp.reducible_of_minus_one hn hw
lemma reducible_sub_minus_one_probability_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) := by
  rw [reducible_sub_minus_one_probability_eq hn]
  exact uniformProbability_nonneg _
lemma reducible_sub_minus_one_probability_le {n : ℕ} (hn : 2 ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ≤
        binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) +
          binaryProbability (n - 1) HasHigherCyclotomicDivisor := by
  rw [reducible_sub_minus_one_probability_eq hn]
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        (ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) ∨ HasHigherCyclotomicDivisor p) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hp
      by_cases hc : HasCyclotomicDivisor (wordPolynomial w)
      · rcases hp.cyclotomic_alternative hc with h | h
        · exact Or.inr h
        · exact False.elim (hw.2 h)
      · exact Or.inl ⟨hw.1, hc⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _
lemma reducible_probability_reduction {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ∧
      binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ≤
          8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) +
            binaryProbability (n - 1) (fun p ↦
              HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p) +
            binaryProbability (n - 1) HasHigherCyclotomicDivisor := by
  refine ⟨reducible_sub_minus_one_probability_nonneg hn, ?_⟩
  have h₁ := reducible_sub_minus_one_probability_le hn
  have h₂ := reducible_without_cyclotomic_probability_le (show 1 ≤ n by omega)
  have h₃ := mod_four_companion_probability_le n (by omega)
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
lemma binaryProbability_companion_isBigO (A : ℝ) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (HasModFourCompanion n)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have h := (geometric_quarter_isBigO_rpow (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) A).const_mul_left 8
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp0 : 0 ≤ binaryProbability (n - 1) (HasModFourCompanion n) := uniformProbability_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (show (0 : ℝ) ≤ 8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) by positivity)]
    using mod_four_companion_probability_le n hn
lemma binaryProbability_reducible_noncyclotomic_isBigO (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have h := (binaryProbability_companion_isBigO A).add
    (binaryProbability_reciprocal_noncyclotomic_isBigO A hA)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hprob := reducible_without_cyclotomic_probability_le hn
  have hnonneg : 0 ≤ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P) := uniformProbability_nonneg _
  have hsum : 0 ≤ binaryProbability (n - 1) (HasModFourCompanion n) +
      binaryProbability (n - 1) (fun P ↦
        HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hsum] using hprob
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators Classical
def groupWordEquiv {ι κ : Type*} (f : ι → κ) :
    (ι → Bool) ≃ (∀ j : κ, {i : ι // f i = j} → Bool) :=
  Equiv.piCongrFiberwise (f := f) (fun _ ↦ Equiv.refl _)
lemma groupWordEquiv_apply {ι κ : Type*} (f : ι → κ) (w : ι → Bool)
    (j : κ) (i : {i : ι // f i = j}) : groupWordEquiv f w j i = w i.val := rfl
lemma uniformProbability_groupWord {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (E : (∀ j : κ, {i : ι // f i = j} → Bool) → Prop) :
    uniformProbability (fun w : ι → Bool ↦ E (groupWordEquiv f w)) =
      uniformProbability E := uniformProbability_equiv (groupWordEquiv f) E
lemma uniformProbability_groupWord_pi {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (E : ∀ j : κ, ({i : ι // f i = j} → Bool) → Prop) :
    uniformProbability (fun w : ι → Bool ↦ ∀ j, E j (fun i ↦ w i.val)) =
      ∏ j, uniformProbability (E j) := by
  calc
    _ = uniformProbability (fun v : ∀ j : κ, {i : ι // f i = j} → Bool ↦ ∀ j, E j (v j)) :=
      uniformProbability_groupWord f _
    _ = _ := uniformProbability_pi E
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped Classical
noncomputable def booleanWordFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun w := Finset.univ.filter (fun i ↦ w i = true)
  invFun s i := decide (i ∈ s)
  left_inv w := by
    funext i
    cases hi : w i <;> simp [hi]
  right_inv s := by
    ext i
    simp
lemma trueBitCount_eq_card (n : ℕ) (w : Fin n → Bool) :
    trueBitCount w = (booleanWordFinsetEquiv n w).card := rfl
lemma uniformProbability_trueBitCount (n k : ℕ) :
    uniformProbability (fun w : Fin n → Bool ↦ trueBitCount w = k) =
      (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  classical
  simp_rw [trueBitCount_eq_card]
  rw [uniformProbability_equiv (booleanWordFinsetEquiv n)
    (fun s : Finset (Fin n) ↦ s.card = k)]
  unfold uniformProbability
  rw [← Fintype.card_subtype, Fintype.card_finset_len]
  simp only [Fintype.card_fin, Fintype.card_finset,
    Nat.cast_pow, Nat.cast_ofNat]
lemma uniformProbability_trueBitCount_eq_zero {n k : ℕ} (h : n < k) :
    uniformProbability (fun w : Fin n → Bool ↦ trueBitCount w = k) = 0 := by
  rw [uniformProbability_trueBitCount, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_div]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators
def alternatingComplement {m : ℕ} (w : Fin m → Bool) (i : Fin m) : Bool :=
  if i.val % 2 = 1 then !(w i) else w i
lemma alternatingComplement_involutive (m : ℕ) :
    Function.Involutive (@alternatingComplement m) := by
  intro w
  funext i
  simp only [alternatingComplement]
  split_ifs <;> simp
lemma alternatingComplement_bijective (m : ℕ) :
    Function.Bijective (@alternatingComplement m) :=
  (alternatingComplement_involutive m).bijective
lemma sum_bitValue_eq_trueBitCount {m : ℕ} (w : Fin m → Bool) :
    (∑ i, bitValue (w i)) = (trueBitCount w : ℤ) := by
  simp [bitValue, trueBitCount]
lemma sum_odd_position_indicators (m : ℕ) :
    (∑ i ∈ Finset.range m, if i % 2 = 1 then (1 : ℤ) else 0) = (m / 2 : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega
lemma signed_bitValue (i : ℕ) (b : Bool) :
    bitValue b * (-1 : ℤ) ^ (i + 1) =
      (if i % 2 = 1 then 1 else 0) -
        bitValue (if i % 2 = 1 then !b else b) := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have he : (i + 1) % 2 = 1 := by omega
    cases b <;> simp [hi, he, bitValue]
  · have he : (i + 1) % 2 = 0 := by omega
    cases b <;> simp [hi, he, bitValue]
lemma eval_wordPolynomial_minus_one {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).eval (-1) =
      1 + (-1 : ℤ) ^ (m + 1) + (m / 2 : ℕ) -
        (trueBitCount (alternatingComplement w) : ℤ) := by
  have hs : (∑ i : Fin m, bitValue (w i) * (-1 : ℤ) ^ (i.val + 1)) =
      (m / 2 : ℕ) - (trueBitCount (alternatingComplement w) : ℤ) := by
    simp_rw [signed_bitValue]
    rw [Finset.sum_sub_distrib]
    change (∑ i : Fin m, if i.val % 2 = 1 then (1 : ℤ) else 0) -
      (∑ i : Fin m, bitValue (alternatingComplement w i)) = _
    rw [sum_bitValue_eq_trueBitCount,
      Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if i % 2 = 1 then (1 : ℤ) else 0) m,
      sum_odd_position_indicators]
  simp only [wordPolynomial, interiorPolynomial, eval_add, eval_one, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X]
  rw [hs]
  ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped Nat
noncomputable def centralBinomialMass (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / 4 ^ n
lemma centralBinomialMass_pos (n : ℕ) : 0 < centralBinomialMass n := by
  unfold centralBinomialMass
  exact div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos n)) (by positivity)
lemma centralBinomialMass_eq_choose (n : ℕ) :
    centralBinomialMass n = ((2 * n).choose n : ℝ) / (2 : ℝ) ^ (2 * n) := by
  rw [centralBinomialMass, Nat.centralBinom_eq_two_mul_choose, pow_mul]
  norm_num
lemma centralBinomialMass_wallis_identity (n : ℕ) :
    Real.Wallis.W n * ((2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2) = 1 := by
  have hf : (Nat.centralBinom n : ℝ) * (n ! : ℝ) ^ 2 = ((2 * n)! : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have hn : 2 * n - n = n := by omega
    rw [hn, ← Nat.centralBinom_eq_two_mul_choose] at h
    exact_mod_cast (by simpa [pow_two, mul_assoc] using h :
      Nat.centralBinom n * n ! ^ 2 = (2 * n)!)
  have hp : (2 : ℝ) ^ (4 * n) = (4 ^ n) ^ 2 := by
    calc
      (2 : ℝ) ^ (4 * n) = ((2 : ℝ) ^ 4) ^ n := pow_mul _ _ _
      _ = ((4 : ℝ) ^ 2) ^ n := by norm_num
      _ = ((4 : ℝ) ^ n) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  rw [Real.Wallis.W_eq_factorial_ratio, ← hf, hp, centralBinomialMass]
  have hc : (Nat.centralBinom n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero n)
  have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
lemma centralBinomialMass_sq_lower (n : ℕ) :
    2 / (Real.pi * (2 * (n : ℝ) + 1)) ≤ centralBinomialMass n ^ 2 := by
  have hw := Real.Wallis.W_le n
  have hi := centralBinomialMass_wallis_identity n
  have hmul := mul_le_mul_of_nonneg_right hw
    (show 0 ≤ (2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2 by positivity)
  rw [hi] at hmul
  apply (div_le_iff₀ (by positivity : 0 < Real.pi * (2 * (n : ℝ) + 1))).mpr
  nlinarith
lemma centralBinomialMass_sq_upper_aux (n : ℕ) :
    Real.pi * (2 * (n : ℝ) + 1) ^ 2 * centralBinomialMass n ^ 2 ≤
      4 * ((n : ℝ) + 1) := by
  have hw := Real.Wallis.le_W n
  have hi := centralBinomialMass_wallis_identity n
  have hmul := mul_le_mul_of_nonneg_right hw
    (show 0 ≤ (2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2 by positivity)
  rw [hi] at hmul
  have hn : 0 < 2 * (n : ℝ) + 2 := by positivity
  have h : Real.pi * (2 * (n : ℝ) + 1) ^ 2 * centralBinomialMass n ^ 2 /
      (2 * (2 * (n : ℝ) + 2)) ≤ 1 := by
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hh := (div_le_one (by positivity : 0 < 2 * (2 * (n : ℝ) + 2))).mp h
  nlinarith
lemma centralBinomialMass_sq_upper {n : ℕ} (hn : 1 ≤ n) :
    centralBinomialMass n ^ 2 ≤ 1 / (Real.pi * (n : ℝ)) := by
  have hu := centralBinomialMass_sq_upper_aux n
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ (mul_pos Real.pi_pos hn0)).mpr
  have hc : 0 ≤ Real.pi * centralBinomialMass n ^ 2 := by positivity
  have h : 4 * ((n : ℝ) + 1) *
      (centralBinomialMass n ^ 2 * (Real.pi * (n : ℝ))) ≤
      4 * ((n : ℝ) + 1) * 1 := by nlinarith
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp h
lemma centralBinomialMass_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    centralBinomialMass n ≤ 1 / Real.sqrt (Real.pi * (n : ℝ)) := by
  have h := Real.sqrt_le_sqrt (centralBinomialMass_sq_upper hn)
  simpa [Real.sqrt_sq (centralBinomialMass_pos n).le, Real.sqrt_div] using h
lemma centralBinomialMass_abs_sub_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    |centralBinomialMass n - 1 / Real.sqrt (Real.pi * (n : ℝ))| ≤
      (1 / Real.sqrt (Real.pi * (n : ℝ))) / (2 * (n : ℝ) + 1) := by
  let t : ℝ := 1 / Real.sqrt (Real.pi * (n : ℝ))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hn0
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ^ 2 = 1 / (Real.pi * (n : ℝ)) := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hp.le, one_pow]
  have hu : centralBinomialMass n ≤ t := centralBinomialMass_le_sqrt hn
  have hl := centralBinomialMass_sq_lower n
  have hi : t ^ 2 - 2 / (Real.pi * (2 * (n : ℝ) + 1)) =
      t ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [ht2]
    field_simp
    ring
  have hs : t ^ 2 - centralBinomialMass n ^ 2 ≤ t ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [← hi]
    linarith
  have hmul : t * (t - centralBinomialMass n) ≤ t ^ 2 / (2 * (n : ℝ) + 1) := by
    nlinarith [mul_nonneg (centralBinomialMass_pos n).le (sub_nonneg.mpr hu)]
  have he : t ^ 2 / (2 * (n : ℝ) + 1) = t * (t / (2 * (n : ℝ) + 1)) := by ring
  rw [he] at hmul
  have hd := (mul_le_mul_iff_right₀ ht).mp hmul
  change |centralBinomialMass n - t| ≤ t / (2 * (n : ℝ) + 1)
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma inverse_sqrt_pi_le {x : ℝ} (hx : 0 < x) :
    1 / Real.sqrt (Real.pi * x) ≤ 1 / Real.sqrt x := by
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hx)
  apply Real.sqrt_le_sqrt
  calc
    x = 1 * x := by ring
    _ ≤ Real.pi * x := mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) hx.le
lemma sqrt_two_div_double (x : ℝ) :
    Real.sqrt (2 / (Real.pi * (2 * x))) = 1 / Real.sqrt (Real.pi * x) := by
  have he : 2 / (Real.pi * (2 * x)) = 1 / (Real.pi * x) := by ring
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_one]
lemma sqrt_odd_degree_comparison {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / Real.sqrt (Real.pi * x) - Real.sqrt (2 / (Real.pi * (2 * x + 1))) ∧
      1 / Real.sqrt (Real.pi * x) - Real.sqrt (2 / (Real.pi * (2 * x + 1))) ≤
        (1 / Real.sqrt (Real.pi * x)) / (2 * x + 1) := by
  let t := 1 / Real.sqrt (Real.pi * x)
  let u := Real.sqrt (2 / (Real.pi * (2 * x + 1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht2 : t ^ 2 = 1 / (Real.pi * x) := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt (by positivity), one_pow]
  have hu2 : u ^ 2 = 2 / (Real.pi * (2 * x + 1)) := by
    dsimp [u]
    rw [Real.sq_sqrt (by positivity)]
  have hd : 2 / (Real.pi * (2 * x + 1)) ≤ 1 / (Real.pi * x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.pi_pos]
  have hut : u ≤ t := by nlinarith
  have hs : t ^ 2 - u ^ 2 = t ^ 2 / (2 * x + 1) := by
    rw [ht2, hu2]
    field_simp
    ring
  have hmul : t * (t - u) ≤ t ^ 2 / (2 * x + 1) := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hut)]
  have he : t ^ 2 / (2 * x + 1) = t * (t / (2 * x + 1)) := by ring
  rw [he] at hmul
  exact ⟨sub_nonneg.mpr hut, (mul_le_mul_iff_right₀ ht).mp hmul⟩
lemma inverse_three_halves_comparison {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 3 * x) :
    3 / (x * Real.sqrt x) ≤ 18 / (y * Real.sqrt y) := by
  have hs : Real.sqrt y ≤ 2 * Real.sqrt x := by
    have hxs := Real.sq_sqrt hx.le
    have hys := Real.sq_sqrt hy.le
    have hxp := Real.sqrt_nonneg x
    have hyp := Real.sqrt_nonneg y
    nlinarith
  have hm : y * Real.sqrt y ≤ 6 * (x * Real.sqrt x) := by
    calc
      y * Real.sqrt y ≤ (3 * x) * (2 * Real.sqrt x) :=
        mul_le_mul hyx hs (Real.sqrt_nonneg y) (by positivity)
      _ = 6 * (x * Real.sqrt x) := by ring
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith
lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) = 1 / (x * Real.sqrt x) := by
  rw [show (-3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hx.le,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators
lemma uniformProbability_trueBitCount_le_central {m r : ℕ}
    (hm : m ≤ 2 * r) (hr : 2 * r ≤ m + 1) (k : ℕ) :
    uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = k) ≤
      2 * centralBinomialMass r := by
  have hc : m.choose k ≤ Nat.centralBinom r :=
    (Nat.choose_le_choose k hm).trans (Nat.choose_le_centralBinom k r)
  have hp : (2 : ℝ) ^ (2 * r) ≤ 2 * (2 : ℝ) ^ m := by
    calc
      (2 : ℝ) ^ (2 * r) ≤ 2 ^ (m + 1) := by gcongr; norm_num
      _ = 2 * (2 : ℝ) ^ m := by rw [pow_succ]; ring
  rw [uniformProbability_trueBitCount]
  calc
    _ ≤ (Nat.centralBinom r : ℝ) / (2 : ℝ) ^ m := by gcongr
    _ ≤ (2 * (Nat.centralBinom r : ℝ)) / (2 : ℝ) ^ (2 * r) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Nat.centralBinom r))
      nlinarith
    _ = 2 * centralBinomialMass r := by
      rw [centralBinomialMass_eq_choose, Nat.centralBinom_eq_two_mul_choose]
      ring
lemma uniformProbability_trueBitCount_le_sqrt (m k : ℕ) :
    uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = k) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  by_cases hm : m = 0
  · subst m
    calc
      _ ≤ 1 := uniformProbability_le_one _
      _ ≤ _ := by norm_num
  let r := (m + 1) / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hmr : m ≤ 2 * r := by dsimp [r]; omega
  have hrm : 2 * r ≤ m + 1 := by dsimp [r]; omega
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hms : Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt (r : ℝ) := by
    have he : (m : ℝ) + 1 ≤ 4 * (r : ℝ) := by exact_mod_cast (show m + 1 ≤ 4 * r by omega)
    have h₁ := Real.sq_sqrt hm1.le
    have h₂ := Real.sq_sqrt hr0.le
    have h₃ := Real.sqrt_nonneg ((m : ℝ) + 1)
    have h₄ := Real.sqrt_nonneg (r : ℝ)
    nlinarith
  calc
    _ ≤ 2 * centralBinomialMass r := uniformProbability_trueBitCount_le_central hmr hrm k
    _ ≤ 2 * (1 / Real.sqrt (Real.pi * (r : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (centralBinomialMass_le_sqrt hr) (by norm_num)
    _ ≤ 2 / Real.sqrt (r : ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (inverse_sqrt_pi_le hr0) (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ 4 / Real.sqrt ((m : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
lemma uniformProbability_bitValue_sum_le (m : ℕ) (z : ℤ) :
    uniformProbability (fun w : Fin m → Bool ↦ (∑ i, bitValue (w i)) = z) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  calc
    _ ≤ uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = z.toNat) := by
      apply uniformProbability_mono
      intro w hw
      rw [sum_bitValue_eq_trueBitCount] at hw
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hw
    _ ≤ _ := uniformProbability_trueBitCount_le_sqrt m z.toNat
lemma uniformProbability_shifted_bitValue_sum_le (m : ℕ) (a z : ℤ) :
    uniformProbability (fun w : Fin m → Bool ↦ a + ∑ i, bitValue (w i) = z) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  calc
    _ ≤ uniformProbability (fun w : Fin m → Bool ↦ (∑ i, bitValue (w i)) = z - a) := by
      apply uniformProbability_mono
      intro w hw
      omega
    _ ≤ _ := uniformProbability_bitValue_sum_le m (z - a)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped BigOperators Classical
lemma uniformProbability_finite_bit_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a z : ℤ) :
    uniformProbability (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) = z) ≤
      4 / Real.sqrt ((Fintype.card ι : ℝ) + 1) := by
  let e := Fintype.equivFin ι
  let ew : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) :=
    { toFun := fun w i ↦ w (e i)
      invFun := fun w i ↦ w (e.symm i)
      left_inv := fun w ↦ by funext i; simp
      right_inv := fun w ↦ by funext i; simp }
  calc
    _ = uniformProbability
        (fun w : Fin (Fintype.card ι) → Bool ↦ a + ∑ i : ι, bitValue (w (e i)) = z) :=
      (uniformProbability_equiv ew (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) = z)).symm
    _ = uniformProbability
        (fun w : Fin (Fintype.card ι) → Bool ↦ a + ∑ i, bitValue (w i) = z) := by
      congr 1
      funext w
      rw [e.sum_comp (fun i ↦ bitValue (w i))]
    _ ≤ _ := uniformProbability_shifted_bitValue_sum_le _ a z
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open scoped Classical
lemma card_positive_residue_class_ge (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    m / k ≤ Fintype.card {i : Fin m // (i.val + 1) % k = r.val} := by
  let a := if r.val = 0 then k - 1 else r.val - 1
  have ha : a < k := by dsimp [a]; split_ifs <;> have := r.isLt <;> omega
  have har : (a + 1) % k = r.val := by
    dsimp [a]
    split_ifs with hr
    · rw [Nat.sub_add_cancel hk, Nat.mod_self, hr]
    · rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt r.isLt]
  let e : Fin (m / k) → {i : Fin m // (i.val + 1) % k = r.val} := fun j ↦
    ⟨⟨a + k * j.val, by
        have h₁ := Nat.mul_le_mul_left k (show j.val + 1 ≤ m / k by omega)
        have h₂ := Nat.mul_div_le m k
        nlinarith⟩, by
      change (a + k * j.val + 1) % k = r.val
      calc
        _ = ((a + 1) + k * j.val) % k := by congr 1; omega
        _ = (a + 1) % k := by simp
        _ = _ := har⟩
  have he : Function.Injective e := by
    intro i j hij
    have h := congrArg (fun x ↦ x.val.val) hij
    dsimp [e] at h
    apply Fin.ext
    nlinarith
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he
lemma card_positive_residue_class_add_one_ge (m : ℕ) {k : ℕ}
    (hk : 0 < k) (r : Fin k) :
    (m + 1 : ℝ) / k ≤
      (Fintype.card {i : Fin m // (i.val + 1) % k = r.val} : ℝ) + 1 := by
  have hc := card_positive_residue_class_ge m hk r
  have hd : m + 1 ≤ k * (m / k + 1) := by
    have := Nat.mod_lt m hk
    have := Nat.mod_add_div m k
    nlinarith
  have hm : m + 1 ≤ k * (Fintype.card {i : Fin m // (i.val + 1) % k = r.val} + 1) :=
    hd.trans (Nat.mul_le_mul_left k (by omega))
  apply (div_le_iff₀ (by exact_mod_cast hk)).mpr
  exact_mod_cast (by simpa only [mul_comm] using hm)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma X_pow_sub_one_dvd_pow_sub_residue (k n : ℕ) :
    (X ^ k - 1 : ℤ[X]) ∣ X ^ n - X ^ (n % k) := by
  have h : (X ^ k - 1 : ℤ[X]) ∣ (X ^ k) ^ (n / k) - 1 := by
    simpa only [one_pow] using sub_dvd_pow_sub_pow (X ^ k : ℤ[X]) 1 (n / k)
  have he : (X ^ (n % k) : ℤ[X]) * ((X ^ k) ^ (n / k) - 1) =
      X ^ n - X ^ (n % k) := by
    rw [mul_sub, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [← he]
  exact dvd_mul_of_dvd_right h _
noncomputable def wordResiduePolynomial {m : ℕ} (k : ℕ) (w : Fin m → Bool) : ℤ[X] :=
  1 + (∑ i, C (bitValue (w i)) * X ^ ((i.val + 1) % k)) + X ^ ((m + 1) % k)
lemma wordPolynomial_sub_residue_dvd {m : ℕ} (k : ℕ) (w : Fin m → Bool) :
    (X ^ k - 1 : ℤ[X]) ∣ wordPolynomial w - wordResiduePolynomial k w := by
  have he : wordPolynomial w - wordResiduePolynomial k w =
      (∑ i : Fin m, C (bitValue (w i)) *
        (X ^ (i.val + 1) - X ^ ((i.val + 1) % k))) +
        (X ^ (m + 1) - X ^ ((m + 1) % k)) := by
    simp only [wordPolynomial, interiorPolynomial, wordResiduePolynomial, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [he]
  apply dvd_add
  · exact Finset.dvd_sum (fun i _ ↦ dvd_mul_of_dvd_right
      (X_pow_sub_one_dvd_pow_sub_residue k (i.val + 1)) _)
  · exact X_pow_sub_one_dvd_pow_sub_residue k (m + 1)
lemma cyclotomic_dvd_wordResiduePolynomial_iff {m : ℕ} (k : ℕ) (w : Fin m → Bool) :
    cyclotomic k ℤ ∣ wordResiduePolynomial k w ↔ cyclotomic k ℤ ∣ wordPolynomial w := by
  have hd := dvd_trans (cyclotomic.dvd_X_pow_sub_one k ℤ)
    (wordPolynomial_sub_residue_dvd k w)
  constructor
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd
def residueEndpointShift (m k r : ℕ) : ℤ :=
  (if r = 0 then 1 else 0) + (if r = (m + 1) % k then 1 else 0)
lemma coeff_wordResiduePolynomial {m : ℕ} (k : ℕ) (w : Fin m → Bool) (r : ℕ) :
    (wordResiduePolynomial k w).coeff r = residueEndpointShift m k r +
      ∑ i : {i : Fin m // (i.val + 1) % k = r}, bitValue (w i.val) := by
  have hs : (∑ i : Fin m, bitValue (w i) * (if r = (i.val + 1) % k then 1 else 0)) =
      ∑ i : {i : Fin m // (i.val + 1) % k = r}, bitValue (w i.val) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp [eq_comm]) _
  simp only [wordResiduePolynomial, coeff_add, finsetSum_coeff, coeff_C_mul,
    coeff_X_pow, coeff_one, hs, residueEndpointShift]
  ring
lemma coeff_wordResiduePolynomial_above {m k : ℕ} (hk : 0 < k)
    (w : Fin m → Bool) {r : ℕ} (hr : k ≤ r) :
    (wordResiduePolynomial k w).coeff r = 0 := by
  have hr0 : r ≠ 0 := by omega
  have ht : r ≠ (m + 1) % k := by have := Nat.mod_lt (m + 1) hk; omega
  have hi (i : Fin m) : r ≠ (i.val + 1) % k := by
    have := Nat.mod_lt (i.val + 1) hk
    omega
  simp [wordResiduePolynomial, coeff_add, finsetSum_coeff, coeff_C_mul,
    coeff_X_pow, coeff_one, hr0, ht, hi]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma eq_of_dvd_of_high_coefficients_eq {R : Type*} [CommRing R] [IsDomain R]
    {J P Q : R[X]} (hJ : J ≠ 0) (hP : J ∣ P) (hQ : J ∣ Q)
    (hcoeff : ∀ i, J.natDegree ≤ i → P.coeff i = Q.coeff i) : P = Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_dvd_of_degree_lt (dvd_sub hP hQ)
  rw [degree_eq_natDegree hJ, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sub, hcoeff i hi, sub_self]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
def residueIndex {m k : ℕ} (hk : 0 < k) (i : Fin m) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
def residueFiberEquiv (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    {i : Fin m // residueIndex hk i = r} ≃ {i : Fin m // (i.val + 1) % k = r.val} where
  toFun i := ⟨i.val, congrArg Fin.val i.property⟩
  invFun i := ⟨i.val, Fin.ext i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def residueBlockCoefficient (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (w : {i : Fin m // residueIndex hk i = r} → Bool) : ℤ :=
  residueEndpointShift m k r.val + ∑ i, bitValue (w i)
lemma coeff_wordResiduePolynomial_eq_block {m k : ℕ} (hk : 0 < k)
    (w : Fin m → Bool) (r : Fin k) :
    (wordResiduePolynomial k w).coeff r.val =
      residueBlockCoefficient m hk r (groupWordEquiv (residueIndex hk) w r) := by
  rw [coeff_wordResiduePolynomial]
  unfold residueBlockCoefficient
  congr 1
  exact ((residueFiberEquiv m hk r).sum_comp (fun i ↦ bitValue (w i.val))).symm
lemma coeff_wordResiduePolynomial_grouped {m k : ℕ} (hk : 0 < k)
    (w : ∀ r : Fin k, {i : Fin m // residueIndex hk i = r} → Bool) (r : Fin k) :
    (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm w)).coeff r.val =
      residueBlockCoefficient m hk r (w r) := by
  simpa only [Equiv.apply_symm_apply] using
    coeff_wordResiduePolynomial_eq_block hk ((groupWordEquiv (residueIndex hk)).symm w) r
lemma card_residueIndex_fiber_add_one_ge (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    (m + 1 : ℝ) / k ≤
      (Fintype.card {i : Fin m // residueIndex hk i = r} : ℝ) + 1 := by
  rw [Fintype.card_congr (residueFiberEquiv m hk r)]
  exact card_positive_residue_class_add_one_ge m hk r
lemma uniformProbability_residueBlockCoefficient_le (m : ℕ) {k : ℕ}
    (hk : 0 < k) (r : Fin k) (z : ℤ) :
    uniformProbability (fun w ↦ residueBlockCoefficient m hk r w = z) ≤
      4 / Real.sqrt (((m : ℝ) + 1) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ ≤ 4 / Real.sqrt ((Fintype.card {i : Fin m // residueIndex hk i = r} : ℝ) + 1) :=
      uniformProbability_finite_bit_sum_le (residueEndpointShift m k r.val) z
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact Real.sqrt_le_sqrt (card_residueIndex_fiber_add_one_ge m hk r)
lemma cyclotomic_dvd_determines_low_residue_coefficients {m k : ℕ} (hk : 0 < k)
    (v w : Fin m → Bool) (hv : cyclotomic k ℤ ∣ wordPolynomial v)
    (hw : cyclotomic k ℤ ∣ wordPolynomial w)
    (hhigh : ∀ r : Fin k, k.totient ≤ r.val →
      (wordResiduePolynomial k v).coeff r.val = (wordResiduePolynomial k w).coeff r.val) :
    wordResiduePolynomial k v = wordResiduePolynomial k w := by
  apply eq_of_dvd_of_high_coefficients_eq (cyclotomic.monic k ℤ).ne_zero
    ((cyclotomic_dvd_wordResiduePolynomial_iff k v).mpr hv)
    ((cyclotomic_dvd_wordResiduePolynomial_iff k w).mpr hw)
  intro i hi
  rw [natDegree_cyclotomic] at hi
  by_cases hik : i < k
  · exact hhigh ⟨i, hik⟩ hi
  · rw [coeff_wordResiduePolynomial_above hk v (by omega),
      coeff_wordResiduePolynomial_above hk w (by omega)]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma binaryProbability_cyclotomic_residue_bound (m : ℕ) {k : ℕ} (hk : 0 < k) :
    binaryProbability m (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (4 / Real.sqrt (((m : ℝ) + 1) / k)) ^ k.totient := by
  letI : DecidablePred (fun r : Fin k ↦ r.val < k.totient) :=
    fun _ ↦ Classical.propDecidable _
  let α := fun r : Fin k ↦ {i : Fin m // residueIndex hk i = r} → Bool
  let e : (Fin m → Bool) ≃ (∀ r, α r) := groupWordEquiv (residueIndex hk)
  let E := fun w : ∀ r, α r ↦ cyclotomic k ℤ ∣ wordPolynomial (e.symm w)
  let c : ℝ := 4 / Real.sqrt (((m : ℝ) + 1) / k)
  have hunique (v w : ∀ r, α r) (hv : E v) (hw : E w)
      (hhigh : ∀ r : Fin k, ¬r.val < k.totient → v r = w r) :
      ∀ r : Fin k, r.val < k.totient →
        residueBlockCoefficient m hk r (v r) = residueBlockCoefficient m hk r (w r) := by
    have hpoly := cyclotomic_dvd_determines_low_residue_coefficients hk
      (e.symm v) (e.symm w) hv hw (fun r hr ↦ by
        change (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm v)).coeff r.val =
          (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm w)).coeff r.val
        rw [coeff_wordResiduePolynomial_grouped, coeff_wordResiduePolynomial_grouped,
          hhigh r (by omega)])
    intro r _
    have heq := congrArg (fun p : ℤ[X] ↦ p.coeff r.val) hpoly
    simpa only [e, coeff_wordResiduePolynomial_grouped] using heq
  calc
    _ = uniformProbability E := by
      exact (uniformProbability_equiv e.symm
        (fun w : Fin m → Bool ↦ cyclotomic k ℤ ∣ wordPolynomial w)).symm
    _ ≤ ∏ r : {r : Fin k // r.val < k.totient}, c := by
      exact uniformProbability_selected_coordinates_le
        (fun r : Fin k ↦ r.val < k.totient) E
        (fun r ↦ residueBlockCoefficient m hk r) (fun _ ↦ c)
        (fun _ _ ↦ by dsimp [c]; positivity)
        (fun r _ z ↦ uniformProbability_residueBlockCoefficient_le m hk r z) hunique
    _ = _ := by
      let er : {r : Fin k // r.val < k.totient} ≃ Fin k.totient :=
        { toFun := fun r ↦ ⟨r.val.val, r.property⟩
          invFun := fun r ↦ ⟨⟨r.val, lt_of_lt_of_le r.isLt (Nat.totient_le k)⟩, r.isLt⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr er, Fintype.card_fin]
lemma binaryProbability_cyclotomic_residue_bound_degree {n k : ℕ}
    (hn : 1 ≤ n) (hk : 0 < k) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient := by
  have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simpa only [hnR] using binaryProbability_cyclotomic_residue_bound (n - 1) hk
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical
lemma HasBinaryEndpoints.cyclotomic_order_le {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hd : cyclotomic k ℤ ∣ p) : k ≤ 2 * n ^ 2 := by
  have hdegree := natDegree_le_of_dvd hd hp.ne_zero
  rw [natDegree_cyclotomic, hp.degree] at hdegree
  calc
    k ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
    _ ≤ _ := by gcongr
lemma binaryProbability_cyclotomic_divisible_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      2 / (2 : ℝ) ^ k.totient := by
  simpa only [natDegree_cyclotomic] using
    binaryProbability_monic_divisible_le hn (cyclotomic.monic k ℤ)
lemma binaryProbability_high_cyclotomic_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, 0 < k ∧ L ≤ k.totient ∧ cyclotomic k ℤ ∣ p) ≤
      4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  let s := (Finset.Icc 1 (2 * n ^ 2)).filter (fun k ↦ L ≤ k.totient)
  have hc : s.card ≤ 2 * n ^ 2 := by
    calc
      _ ≤ (Finset.Icc 1 (2 * n ^ 2)).card := Finset.card_filter_le _ _
      _ = _ := by simp
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hL, hd⟩
      have ho := (wordPolynomial_endpoints w).cyclotomic_order_le hd
      rw [Nat.sub_add_cancel hn] at ho
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, ho⟩, hL⟩, hd⟩
    _ ≤ (s.card : ℝ) * (2 / (2 : ℝ) ^ L) := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      have hL := (Finset.mem_filter.mp hk).2
      calc
        _ ≤ 2 / (2 : ℝ) ^ k.totient := binaryProbability_cyclotomic_divisible_le hn k
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_right₀ (by norm_num) hL
    _ ≤ (2 * (n : ℝ) ^ 2) * (2 / (2 : ℝ) ^ L) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma residue_atom_scale_sq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (4 / Real.sqrt (x / y)) ^ 2 = 16 * y / x := by
  rw [div_pow, Real.sq_sqrt (div_nonneg hx.le hy.le)]
  field_simp
  norm_num
lemma residue_atom_scale_le_cutoff {x y L : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hL : 0 ≤ L) (hyL : y ≤ 2 * L ^ 2) :
    4 / Real.sqrt (x / y) ≤ 8 * L / Real.sqrt x := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [residue_atom_scale_sq hx hy, div_pow, mul_pow, Real.sq_sqrt hx.le]
  apply div_le_div_of_nonneg_right _ hx.le
  nlinarith
lemma residue_order_count_mul_cube {x L : ℝ} (hx : 0 < x) :
    (2 * L ^ 2) * (8 * L / Real.sqrt x) ^ 3 =
      1024 * L ^ 5 / (x * Real.sqrt x) := by
  have hs : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
    rw [pow_succ, Real.sq_sqrt hx.le]
  rw [div_pow, hs]
  ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
lemma binaryProbability_cyclotomic_degree_two_fixed_le {n k : ℕ} (hn : 1 ≤ n)
    (hk : k.totient = 2) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤ 128 / (n : ℝ) := by
  have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have horder : k ≤ 8 := by simpa [hk] using order_le_two_totient_sq k
  calc
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient :=
      binaryProbability_cyclotomic_residue_bound_degree hn hk0
    _ = 16 * (k : ℝ) / n := by rw [hk, residue_atom_scale_sq hnR hkR]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hnR.le
      have : (k : ℝ) ≤ 8 := by exact_mod_cast horder
      linarith
lemma binaryProbability_cyclotomic_degree_two_le {n : ℕ} (hn : 1 ≤ n) :
    binaryProbability (n - 1) (fun p ↦ ∃ k, k.totient = 2 ∧ cyclotomic k ℤ ∣ p) ≤
      1024 / (n : ℝ) := by
  let s := (Finset.Icc 1 8).filter (fun k : ℕ ↦ k.totient = 2)
  have hc : s.card ≤ 8 := by
    calc
      _ ≤ (Finset.Icc 1 8 : Finset ℕ).card := Finset.card_filter_le _ _
      _ = _ := by norm_num
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
      have ho : k ≤ 8 := by simpa [hk] using order_le_two_totient_sq k
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk0, ho⟩, hk⟩, hd⟩
    _ ≤ (s.card : ℝ) * (128 / (n : ℝ)) := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      exact binaryProbability_cyclotomic_degree_two_fixed_le hn (Finset.mem_filter.mp hk).2
    _ ≤ 8 * (128 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical
lemma binaryProbability_cyclotomic_intermediate_fixed_le {n k L : ℕ}
    (hn : 1 ≤ n) (hk : 3 ≤ k.totient) (hkL : k.totient < L)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
  have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have horder : k ≤ 2 * L ^ 2 := by
    calc
      _ ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
      _ ≤ _ := by gcongr
  have hbase : 4 / Real.sqrt ((n : ℝ) / k) ≤ 8 * (L : ℝ) / Real.sqrt (n : ℝ) :=
    residue_atom_scale_le_cutoff hnR hkR (Nat.cast_nonneg L) (by exact_mod_cast horder)
  calc
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient :=
      binaryProbability_cyclotomic_residue_bound_degree hn hk0
    _ ≤ (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ k.totient := by gcongr
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) hsmall hk
lemma binaryProbability_cyclotomic_intermediate_le {n L : ℕ} (hn : 1 ≤ n)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, 3 ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p) ≤
      1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  let s := (Finset.Icc 1 (2 * L ^ 2)).filter
    (fun k : ℕ ↦ 3 ≤ k.totient ∧ k.totient < L)
  have hc : s.card ≤ 2 * L ^ 2 := by
    calc
      _ ≤ (Finset.Icc 1 (2 * L ^ 2)).card := Finset.card_filter_le _ _
      _ = _ := by simp
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hkL, hd⟩
      have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
      have ho : k ≤ 2 * L ^ 2 := by
        calc
          _ ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
          _ ≤ _ := by gcongr
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk0, ho⟩, hk, hkL⟩, hd⟩
    _ ≤ (s.card : ℝ) * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      exact binaryProbability_cyclotomic_intermediate_fixed_le hn h.1 h.2 hsmall
    _ ≤ (2 * (L : ℝ) ^ 2) * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := residue_order_count_mul_cube (by exact_mod_cast (show 0 < n by omega))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Polynomial
lemma binaryProbability_higher_cyclotomic_range_sum {n L : ℕ} (hn : 1 ≤ n)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤
      1024 / (n : ℝ) + 1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) +
        4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  let E₂ := fun p : ℤ[X] ↦ ∃ k, k.totient = 2 ∧ cyclotomic k ℤ ∣ p
  let Eₘ := fun p : ℤ[X] ↦ ∃ k, 3 ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p
  let Eₕ := fun p : ℤ[X] ↦ ∃ k, 0 < k ∧ L ≤ k.totient ∧ cyclotomic k ℤ ∣ p
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦ E₂ p ∨ Eₘ p ∨ Eₕ p) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      by_cases htwo : k.totient = 2
      · exact Or.inl ⟨k, htwo, hd⟩
      · by_cases hL : k.totient < L
        · exact Or.inr (Or.inl ⟨k, by omega, hL, hd⟩)
        · exact Or.inr (Or.inr ⟨k, Nat.totient_pos.mp (by omega), by omega, hd⟩)
    _ ≤ binaryProbability (n - 1) E₂ +
        (binaryProbability (n - 1) Eₘ + binaryProbability (n - 1) Eₕ) := by
      exact (binaryProbability_or_le_add (n - 1) E₂ (fun p ↦ Eₘ p ∨ Eₕ p)).trans
        (add_le_add le_rfl (binaryProbability_or_le_add (n - 1) Eₘ Eₕ))
    _ ≤ 1024 / (n : ℝ) +
        (1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) +
          4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L) :=
      add_le_add (binaryProbability_cyclotomic_degree_two_le hn)
        (add_le_add (binaryProbability_cyclotomic_intermediate_le hn hsmall)
          (binaryProbability_high_cyclotomic_le hn L))
    _ = _ := by ring
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma natLog_two_le_real_log_div {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hp : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hl
lemma nat_pow_le_two_pow_log_multiple (n a : ℕ) :
    n ^ a ≤ 2 ^ (a * (Nat.log 2 n + 1)) := by
  have h : n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
  calc
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ a := Nat.pow_le_pow_left h a
    _ = _ := by rw [← pow_mul, Nat.mul_comm]
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
open scoped Topology
def cyclotomicDegreeCutoff (n : ℕ) : ℕ := 8 * (Nat.log 2 n + 1)
lemma cyclotomicDegreeCutoff_pos (n : ℕ) : 0 < cyclotomicDegreeCutoff n := by
  unfold cyclotomicDegreeCutoff
  omega
lemma pow_eight_le_two_pow_cyclotomicDegreeCutoff (n : ℕ) :
    (n : ℝ) ^ 8 ≤ (2 : ℝ) ^ cyclotomicDegreeCutoff n := by
  exact_mod_cast nat_pow_le_two_pow_log_multiple n 8
lemma cyclotomicDegreeCutoff_le_log {n : ℕ} (hn : 1 ≤ n) :
    (cyclotomicDegreeCutoff n : ℝ) ≤ (8 / Real.log 2) * Real.log (n : ℝ) + 8 := by
  have h := natLog_two_le_real_log_div hn
  simp only [cyclotomicDegreeCutoff, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  calc
    _ ≤ 8 * (Real.log (n : ℝ) / Real.log 2 + 1) := by gcongr
    _ = _ := by ring
lemma cyclotomicDegreeCutoff_isBigO_log :
    (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Asymptotics.isBigO_iff.mpr ⟨8 / Real.log 2 + 8, ?_⟩
  filter_upwards [eventually_ge_atTop 1, ht.eventually_ge_atTop 1] with n hn hlog
  have hL0 : (0 : ℝ) ≤ (cyclotomicDegreeCutoff n : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg (show 0 ≤ Real.log (n : ℝ) by linarith)]
  calc
    _ ≤ (8 / Real.log 2) * Real.log (n : ℝ) + 8 := cyclotomicDegreeCutoff_le_log hn
    _ ≤ _ := by nlinarith
lemma log_nat_pow_isLittleO_sqrt (d : ℕ) :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h
lemma cyclotomicDegreeCutoff_pow_isLittleO_sqrt (d : ℕ) :
    (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) :=
  (cyclotomicDegreeCutoff_isBigO_log.pow d).trans_isLittleO (log_nat_pow_isLittleO_sqrt d)
lemma tendsto_cyclotomicDegreeCutoff_pow_div_sqrt (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ) ^ d / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
  (cyclotomicDegreeCutoff_pow_isLittleO_sqrt d).tendsto_div_nhds_zero
lemma eventually_cyclotomic_cutoff_scale_le_one :
    ∀ᶠ n : ℕ in atTop, 8 * (cyclotomicDegreeCutoff n : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
  have ht : Tendsto
      (fun n : ℕ ↦ 8 * (cyclotomicDegreeCutoff n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (tendsto_cyclotomicDegreeCutoff_pow_div_sqrt 1).const_mul 8
  exact ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
open scoped Topology
lemma cyclotomic_cutoff_tail_le {n : ℕ} (hn : 1 ≤ n) :
    4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ cyclotomicDegreeCutoff n ≤ 4 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 6)
  calc
    _ ≤ 4 * (n : ℝ) ^ 2 / (n : ℝ) ^ 8 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_eight_le_two_pow_cyclotomicDegreeCutoff n)
    _ = 4 / (n : ℝ) ^ 6 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hnR hp
lemma eventually_binaryProbability_higher_cyclotomic_le :
    ∀ᶠ n : ℕ in atTop,
      binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤ 2052 / (n : ℝ) := by
  have hcut := (tendsto_cyclotomicDegreeCutoff_pow_div_sqrt 5).eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop 1, eventually_cyclotomic_cutoff_scale_le_one, hcut]
    with n hn hs hL
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmid : 1024 * (cyclotomicDegreeCutoff n : ℝ) ^ 5 /
      ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 1024 / (n : ℝ) := by
    calc
      _ = (1024 / (n : ℝ)) *
          ((cyclotomicDegreeCutoff n : ℝ) ^ 5 / Real.sqrt (n : ℝ)) := by ring
      _ ≤ (1024 / (n : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ 1024 / (n : ℝ) + 1024 * (cyclotomicDegreeCutoff n : ℝ) ^ 5 /
        ((n : ℝ) * Real.sqrt (n : ℝ)) +
          4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ cyclotomicDegreeCutoff n :=
      binaryProbability_higher_cyclotomic_range_sum hn hs
    _ ≤ 1024 / (n : ℝ) + 1024 / (n : ℝ) + 4 / (n : ℝ) :=
      add_le_add (add_le_add le_rfl hmid) (cyclotomic_cutoff_tail_le hn)
    _ = _ := by ring
theorem exists_threshold_higher_cyclotomic_bound :
    ∃ N : ℕ, ∀ n ≥ N,
      0 ≤ binaryProbability (n - 1) HasHigherCyclotomicDivisor ∧
        binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤ 2052 / (n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_binaryProbability_higher_cyclotomic_le
  exact ⟨N, fun n hn ↦ ⟨uniformProbability_nonneg _, hN n hn⟩⟩
theorem binaryProbability_higher_cyclotomic_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) HasHigherCyclotomicDivisor) =O[atTop]
      (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨2052, ?_⟩
  filter_upwards [eventually_binaryProbability_higher_cyclotomic_le] with n hn
  have hp0 : 0 ≤ binaryProbability (n - 1) HasHigherCyclotomicDivisor :=
    uniformProbability_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (show 0 ≤ 1 / (n : ℝ) by positivity), mul_one_div] using hn
lemma tendsto_higher_cyclotomic_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) HasHigherCyclotomicDivisor)
      atTop (𝓝 0) :=
  binaryProbability_higher_cyclotomic_isBigO.trans_tendsto
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma uniformProbability_alternatingComplement {m : ℕ}
    (E : (Fin m → Bool) → Prop) :
    uniformProbability (fun w ↦ E (alternatingComplement w)) = uniformProbability E :=
  uniformProbability_bijective (alternatingComplement_bijective m) E
lemma eval_wordPolynomial_minus_one_odd (r : ℕ) (w : Fin (2 * r) → Bool) :
    (wordPolynomial w).eval (-1) =
      (r : ℤ) - (trueBitCount (alternatingComplement w) : ℤ) := by
  have hd : 2 * r / 2 = r := by omega
  have hp : (-1 : ℤ) ^ (2 * r + 1) = -1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    have h : (2 * r + 1) % 2 = 1 := by omega
    rw [h, pow_one]
  rw [eval_wordPolynomial_minus_one, hd, hp]
  ring
lemma eval_wordPolynomial_minus_one_even {r : ℕ} (hr : 1 ≤ r)
    (w : Fin (2 * r - 1) → Bool) :
    (wordPolynomial w).eval (-1) =
      (r + 1 : ℤ) - (trueBitCount (alternatingComplement w) : ℤ) := by
  have hd : (2 * r - 1) / 2 = r - 1 := by omega
  have he : 2 * r - 1 + 1 = 2 * r := by omega
  have hp : (-1 : ℤ) ^ (2 * r) = 1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    have h : (2 * r) % 2 = 0 := by omega
    rw [h, pow_zero]
  rw [eval_wordPolynomial_minus_one, he, hd, hp]
  have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  rw [hcast]
  ring
theorem binaryProbability_minus_one_odd (r : ℕ) :
    binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r).choose r : ℝ) / (2 : ℝ) ^ (2 * r) := by
  unfold binaryProbability
  have he : (fun w : Fin (2 * r) → Bool ↦ (wordPolynomial w).eval (-1) = 0) =
      (fun w ↦ trueBitCount (alternatingComplement w) = r) := by
    funext w
    apply propext
    rw [eval_wordPolynomial_minus_one_odd]
    omega
  rw [he, uniformProbability_alternatingComplement
    (fun w : Fin (2 * r) → Bool ↦ trueBitCount w = r), uniformProbability_trueBitCount]
theorem binaryProbability_minus_one_even {r : ℕ} (hr : 1 ≤ r) :
    binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r - 1).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r - 1) := by
  unfold binaryProbability
  have he : (fun w : Fin (2 * r - 1) → Bool ↦ (wordPolynomial w).eval (-1) = 0) =
      (fun w ↦ trueBitCount (alternatingComplement w) = r + 1) := by
    funext w
    apply propext
    rw [eval_wordPolynomial_minus_one_even hr]
    omega
  rw [he, uniformProbability_alternatingComplement
    (fun w : Fin (2 * r - 1) → Bool ↦ trueBitCount w = r + 1),
    uniformProbability_trueBitCount]
lemma binaryProbability_minus_one_degree_one :
    binaryProbability 0 (fun p ↦ p.eval (-1) = 0) = 1 := by
  simpa using binaryProbability_minus_one_odd 0
lemma binaryProbability_minus_one_degree_two :
    binaryProbability 1 (fun p ↦ p.eval (-1) = 0) = 0 := by
  simpa using binaryProbability_minus_one_even (r := 1) (by omega)
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma adjacent_even_choose_identity {r : ℕ} (hr : 1 ≤ r) :
    2 * ((r : ℝ) + 1) * ((2 * r - 1).choose (r + 1) : ℝ) =
      ((r : ℝ) - 1) * ((2 * r).choose r : ℝ) := by
  have he : 2 * r - 1 + 1 = 2 * r := by omega
  have hd : 2 * r - 1 - r = r - 1 := by omega
  have hd' : 2 * r - r = r := by omega
  have h₁ := Nat.choose_mul_succ_eq (2 * r - 1) r
  rw [he, hd'] at h₁
  have h₂ := Nat.choose_succ_right_eq (2 * r - 1) r
  rw [hd] at h₂
  have h₁' : ((2 * r - 1).choose r : ℝ) * (2 * (r : ℝ)) =
      ((2 * r).choose r : ℝ) * (r : ℝ) := by exact_mod_cast h₁
  have h₂' : ((2 * r - 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1) =
      ((2 * r - 1).choose r : ℝ) * ((r : ℝ) - 1) := by
    have hc : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr]
      norm_num
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) h₂
    push_cast at h
    rwa [hc] at h
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  apply (mul_left_cancel₀ hr0)
  calc
    (r : ℝ) * (2 * ((r : ℝ) + 1) * ((2 * r - 1).choose (r + 1) : ℝ)) =
        (2 * (r : ℝ)) * (((2 * r - 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1)) := by ring
    _ = (2 * (r : ℝ)) * (((2 * r - 1).choose r : ℝ) * ((r : ℝ) - 1)) := by rw [h₂']
    _ = (((2 * r - 1).choose r : ℝ) * (2 * (r : ℝ))) * ((r : ℝ) - 1) := by ring
    _ = (((2 * r).choose r : ℝ) * (r : ℝ)) * ((r : ℝ) - 1) := by rw [h₁']
    _ = (r : ℝ) * (((r : ℝ) - 1) * ((2 * r).choose r : ℝ)) := by ring
lemma binaryProbability_minus_one_odd_eq_central (r : ℕ) :
    binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) = centralBinomialMass r := by
  rw [binaryProbability_minus_one_odd, centralBinomialMass_eq_choose]
lemma binaryProbability_minus_one_even_eq_central {r : ℕ} (hr : 1 ≤ r) :
    binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) =
      ((r : ℝ) - 1) / ((r : ℝ) + 1) * centralBinomialMass r := by
  rw [binaryProbability_minus_one_even hr, centralBinomialMass_eq_choose]
  have hp : (2 : ℝ) ^ (2 * r) = 2 * (2 : ℝ) ^ (2 * r - 1) := by
    have he : 2 * r = (2 * r - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  have h := adjacent_even_choose_identity hr
  rw [hp]
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma binaryProbability_minus_one_even_error {r : ℕ} (hr : 1 ≤ r) :
    |binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (2 * (r : ℝ))))| ≤
        3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let c := centralBinomialMass r
  let t := 1 / Real.sqrt (Real.pi * (r : ℝ))
  let a := ((r : ℝ) - 1) / ((r : ℝ) + 1)
  have hc : 0 ≤ c := (centralBinomialMass_pos r).le
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hct : c ≤ t := centralBinomialMass_le_sqrt hr
  have herror : t - c ≤ t / (2 * (r : ℝ) + 1) := by
    have h := centralBinomialMass_abs_sub_sqrt_le hr
    change |c - t| ≤ t / (2 * (r : ℝ) + 1) at h
    rw [abs_of_nonpos (sub_nonpos.mpr hct)] at h
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hac : a * c ≤ c := by
    have h := mul_le_mul_of_nonneg_right ha1 hc
    simpa only [one_mul] using h
  have ha : 1 - a = 2 / ((r : ℝ) + 1) := by
    dsimp [a]
    field_simp
    ring
  have hd : t - a * c ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t := by
    calc
      t - a * c = (t - c) + (1 - a) * c := by ring
      _ = (t - c) + 2 / ((r : ℝ) + 1) * c := by rw [ha]
      _ ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t :=
        add_le_add herror (mul_le_mul_of_nonneg_left hct (by positivity))
  have hd1 : t / (2 * (r : ℝ) + 1) ≤ t / (r : ℝ) :=
    div_le_div_of_nonneg_left ht hr0 (by linarith)
  have hd2 : 2 / ((r : ℝ) + 1) * t ≤ 2 * (t / (r : ℝ)) := by
    calc
      2 / ((r : ℝ) + 1) * t = (2 * t) / ((r : ℝ) + 1) := by ring
      _ ≤ (2 * t) / (r : ℝ) := div_le_div_of_nonneg_left (by positivity) hr0 (by linarith)
      _ = 2 * (t / (r : ℝ)) := by ring
  have hdt : t - a * c ≤ 3 * t / (r : ℝ) := by
    calc
      t - a * c ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t := hd
      _ ≤ t / (r : ℝ) + 2 * (t / (r : ℝ)) := add_le_add hd1 hd2
      _ = 3 * t / (r : ℝ) := by ring
  have ht' : t ≤ 1 / Real.sqrt (r : ℝ) := inverse_sqrt_pi_le hr0
  have hbound : 3 * t / (r : ℝ) ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
    calc
      3 * t / (r : ℝ) ≤ 3 * (1 / Real.sqrt (r : ℝ)) / (r : ℝ) := by gcongr
      _ = 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by ring
  rw [binaryProbability_minus_one_even_eq_central hr, sqrt_two_div_double]
  change |a * c - t| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr (hac.trans hct))]
  linarith
lemma binaryProbability_minus_one_odd_error {r : ℕ} (hr : 1 ≤ r) :
    |binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (2 * (r : ℝ) + 1)))| ≤
        3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let c := centralBinomialMass r
  let t := 1 / Real.sqrt (Real.pi * (r : ℝ))
  let u := Real.sqrt (2 / (Real.pi * (2 * (r : ℝ) + 1)))
  have huc : u ≤ c := by
    have h := Real.sqrt_le_sqrt (centralBinomialMass_sq_lower r)
    simpa [Real.sqrt_sq (centralBinomialMass_pos r).le, u, c] using h
  have hct : c ≤ t := centralBinomialMass_le_sqrt hr
  have htu : t - u ≤ t / (2 * (r : ℝ) + 1) := (sqrt_odd_degree_comparison hr0).2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t ≤ 1 / Real.sqrt (r : ℝ) := inverse_sqrt_pi_le hr0
  have hd : t / (2 * (r : ℝ) + 1) ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
    calc
      t / (2 * (r : ℝ) + 1) ≤ t / (r : ℝ) :=
        div_le_div_of_nonneg_left ht hr0 (by linarith)
      _ ≤ (1 / Real.sqrt (r : ℝ)) / (r : ℝ) := by gcongr
      _ = 1 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by ring
      _ ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by gcongr; norm_num
  rw [binaryProbability_minus_one_odd_eq_central]
  change |c - u| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr huc)]
  linarith
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter
open scoped Topology
lemma binaryProbability_minus_one_error_bound {n : ℕ} (hn : 3 ≤ n) :
    |binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))| ≤
        18 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  let r := n / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnr : n ≤ 3 * r := by dsimp [r]; omega
  have hscale : 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) ≤
      18 / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
    inverse_three_halves_comparison hr0 hn0 (by exact_mod_cast hnr)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn' : n = 2 * r := by dsimp [r]; omega
    simpa only [hn', Nat.cast_mul, Nat.cast_ofNat] using
      (binaryProbability_minus_one_even_error hr).trans hscale
  · have hn' : n = 2 * r + 1 := by dsimp [r]; omega
    simpa only [hn', Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (binaryProbability_minus_one_odd_error hr).trans hscale
theorem binaryProbability_minus_one_error_rpow {n : ℕ} (hn : 3 ≤ n) :
    |binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))| ≤ 18 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [rpow_neg_three_halves hn0, mul_one_div]
  exact binaryProbability_minus_one_error_bound hn
theorem binaryProbability_minus_one_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨18, eventually_atTop.mpr ⟨3, ?_⟩⟩
  intro n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    using binaryProbability_minus_one_error_rpow hn
lemma tendsto_minus_one_leading_term :
    Tendsto (fun n : ℕ ↦ Real.sqrt (2 / (Real.pi * (n : ℝ)))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ ↦ 2 / (Real.pi * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos)
  simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hd
lemma tendsto_minus_one_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := 3 / 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have he := binaryProbability_minus_one_asymptotic.trans_tendsto hp
  simpa only [sub_add_cancel, add_zero] using he.add tendsto_minus_one_leading_term
end OdlyzkoPoonen

namespace OdlyzkoPoonen
lemma uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    uniformProbability (fun a ↦ ¬ E a) = 1 - uniformProbability E := by
  have h := uniformProbability_sub_of_imp (fun _ : α ↦ True) E (fun _ _ ↦ trivial)
  simpa only [uniformProbability_true, true_and] using h.symm
lemma binaryProbability_irreducible_eq_one_sub_reducible (m : ℕ) :
    binaryProbability m (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ))) =
      1 - binaryProbability m ReducibleOverRat := by
  simpa only [binaryProbability, ReducibleOverRat, not_not] using
    uniformProbability_not (fun w : Fin m → Bool ↦ ReducibleOverRat (wordPolynomial w))
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology
lemma binaryProbability_reducible_excess_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0)) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  have hnoncyc : (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    simpa only [Real.rpow_neg_one, one_div] using
      binaryProbability_reducible_noncyclotomic_isBigO 1 zero_lt_one
  have h := hnoncyc.add binaryProbability_higher_cyclotomic_isBigO
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hsum : 0 ≤ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P) +
        binaryProbability (n - 1) HasHigherCyclotomicDivisor :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (reducible_sub_minus_one_probability_nonneg hn), abs_of_nonneg hsum]
    using reducible_sub_minus_one_probability_le hn
theorem exists_reducible_probability_excess_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 ≤ binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ∧
      binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ≤ C / (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := binaryProbability_reducible_excess_isBigO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
  refine ⟨C, hC, max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnonneg := reducible_sub_minus_one_probability_nonneg hn2
  refine ⟨hnonneg, ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity), mul_one_div]
    using hN n ((le_max_right _ _).trans hn)
lemma nat_rpow_neg_three_halves_isBigO_inverse :
    (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (-3 / 2 : ℝ) ≤ -1)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity), Real.rpow_neg_one, one_div] using h
theorem binaryProbability_reducible_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  have h := binaryProbability_reducible_excess_isBigO.add
    (binaryProbability_minus_one_asymptotic.trans nat_rpow_neg_three_halves_isBigO_inverse)
  simpa only [Pi.add_apply, sub_add_sub_cancel] using h
lemma tendsto_reducible_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat) atTop (𝓝 0) := by
  have he := binaryProbability_reducible_excess_isBigO.trans_tendsto
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [sub_add_cancel, add_zero] using he.add tendsto_minus_one_probability
theorem odlyzko_poonen_irreducibility :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 - binaryProbability (n - 1) ReducibleOverRat)
      atTop (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub tendsto_reducible_probability
  simpa only [binaryProbability_irreducible_eq_one_sub_reducible, sub_zero] using h
end OdlyzkoPoonen

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology
theorem irreducibility_and_reducibility_asymptotic :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) ∧
    ((fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ))) :=
  ⟨odlyzko_poonen_irreducibility, binaryProbability_reducible_asymptotic⟩
end OdlyzkoPoonen


section Bridge93
open Polynomial Filter
open scoped Topology BigOperators

namespace OdlyzkoPoonen

lemma wordPolynomial_monic_bridge {m : ℕ} (w : Fin m → Bool) : (wordPolynomial w).Monic := by
  have hle : (wordPolynomial w).natDegree ≤ m + 1 :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => coeff_wordPolynomial_above w hk)
  have hge : m + 1 ≤ (wordPolynomial w).natDegree :=
    le_natDegree_of_ne_zero (by rw [coeff_wordPolynomial_top]; exact one_ne_zero)
  have hd : (wordPolynomial w).natDegree = m + 1 := le_antisymm hle hge
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [hd, coeff_wordPolynomial_top]

def bridgeEmbed {m : ℕ} (w : Fin m → Bool) : Fin (m + 1) → Fin (1 + 1) :=
  Fin.cons 1 (fun i => if w i then 1 else 0)

lemma monicPoly_bridgeEmbed {m : ℕ} (w : Fin m → Bool) :
    Green93.monicPoly (fun j => ((bridgeEmbed w j : Fin (1 + 1)) : ℕ)) = wordPolynomial w := by
  unfold Green93.monicPoly wordPolynomial interiorPolynomial
  rw [Fin.sum_univ_succ]
  have h0 : ((bridgeEmbed w 0 : Fin (1 + 1)) : ℕ) = 1 := rfl
  have hs : ∀ i : Fin m, ((bridgeEmbed w i.succ : Fin (1 + 1)) : ℕ) = if w i then 1 else 0 := by
    intro i
    simp only [bridgeEmbed, Fin.cons_succ]
    cases w i <;> rfl
  simp only [h0, hs, Fin.val_zero, Fin.val_succ, pow_zero, mul_one, Nat.cast_one, map_one, bitValue]
  have : ∀ i : Fin m, (C ((if w i then 1 else 0 : ℕ) : ℤ) : ℤ[X]) = C (if w i then (1 : ℤ) else 0) := by
    intro i; cases w i <;> simp
  simp only [this]
  ring

lemma bridgeEmbed_injective {m : ℕ} : Function.Injective (@bridgeEmbed m) := by
  intro v w h
  funext i
  have := congrFun h i.succ
  simp only [bridgeEmbed, Fin.cons_succ] at this
  cases hv : v i <;> cases hw : w i <;> simp_all

lemma fin_two_ne_zero_eq_one : ∀ x : Fin (1 + 1), x ≠ 0 → x = 1 := by decide
lemma fin_two_ne_one_eq_zero : ∀ x : Fin (1 + 1), x ≠ 1 → x = 0 := by decide

lemma coeff_zero_monicPoly_succ {m : ℕ} (a : Fin (m + 1) → ℕ) :
    (Green93.monicPoly a).coeff 0 = (a 0 : ℤ) := by
  unfold Green93.monicPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff, Fin.sum_univ_succ]
  simp only [coeff_C_mul, coeff_X_pow, Fin.val_zero, Fin.val_succ]
  simp

lemma irreducibleProb_one_succ (m : ℕ) :
    Green93.irreducibleProb 1 (m + 1) =
      binaryProbability m (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ))) := by
  classical
  have hS0 : (Finset.univ.filter fun a : Fin (m + 1) → Fin (1 + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0) =
      (Finset.univ : Finset (Fin m → Bool)).image bridgeEmbed := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      rw [coeff_zero_monicPoly_succ] at h
      have ha0 : a 0 = 1 := by
        have : a 0 ≠ 0 := fun h' => h (by rw [h']; rfl)
        exact fin_two_ne_zero_eq_one _ this
      refine ⟨fun i => decide (a i.succ = 1), ?_⟩
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [bridgeEmbed, ha0]
      · simp only [bridgeEmbed, Fin.cons_succ]
        by_cases hi : a i.succ = 1
        · simp [hi]
        · have : a i.succ = 0 := fin_two_ne_one_eq_zero _ hi
          simp [this]
    · rintro ⟨w, rfl⟩
      rw [monicPoly_bridgeEmbed, coeff_wordPolynomial_zero]
      exact one_ne_zero
  have hS1 : (Finset.univ.filter fun a : Fin (m + 1) → Fin (1 + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))) =
      (Finset.univ.filter fun w : Fin m → Bool ↦
        Irreducible ((wordPolynomial w).map (Int.castRingHom ℚ))).image bridgeEmbed := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h0, hirr⟩
      have : a ∈ (Finset.univ : Finset (Fin m → Bool)).image bridgeEmbed := by
        rw [← hS0]; simpa using h0
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp this
      refine ⟨w, ?_, rfl⟩
      rw [monicPoly_bridgeEmbed] at hirr
      exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        (wordPolynomial_monic_bridge w).isPrimitive).mp hirr
    · rintro ⟨w, hw, rfl⟩
      rw [monicPoly_bridgeEmbed, coeff_wordPolynomial_zero]
      exact ⟨one_ne_zero, (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        (wordPolynomial_monic_bridge w).isPrimitive).mpr hw⟩
  unfold Green93.irreducibleProb
  rw [hS0, hS1, Finset.card_image_of_injective _ bridgeEmbed_injective,
    Finset.card_image_of_injective _ bridgeEmbed_injective, binaryProbability]
  unfold uniformProbability
  simp

theorem irreducibleProb_one_tendsto :
    Tendsto (fun n : ℕ ↦ Green93.irreducibleProb 1 n) atTop (𝓝 1) := by
  refine (odlyzko_poonen_irreducibility).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [irreducibleProb_one_succ]
  simp

end OdlyzkoPoonen
end Bridge93

open Filter in
theorem OMA.solution : type_of% @Green93.green_93.variants.konyagin := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have hprob : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < Green93.irreducibleProb 1 n :=
    (tendsto_order.1 OdlyzkoPoonen.irreducibleProb_one_tendsto).1 _ hhalf
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hprob, hlog.eventually_ge_atTop 1] with n hp hl
  have hlpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hl
  refine ((div_le_iff₀ hlpos).2 ?_).trans hp.le
  linarith
