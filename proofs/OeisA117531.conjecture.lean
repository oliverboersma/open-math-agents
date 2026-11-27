import FormalConjectures.OEIS.«117531»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds


/-!
# Composite entries in the prime rows of OEIS A117531

For the nth prime p and n > 13, at least one of the n values k² − k + p
is composite. We prove the needed direction of the Rabinowitsch criterion
using the Minkowski bound and then apply the class-number-one classification.
See P. Ribenboim, Euler's Famous Prime Generating Polynomial and the Class
Number of Imaginary Quadratic Fields (1988), section G.

Ondrej Kutal gave the Heegner-number argument in OEIS A117531. The earlier
Lean proof at github.com/TheSil/A117531_conjecture assumes the Stark–Heegner
classification. We discharge that assumption here.

The classification and ideal-norm lemmas below are the tenth-discriminant
formalization as ported by Steven Enamakel in project PR 3263. The prime
size estimate and the descent shortening the composite witness are from
Marcus Buffett's reduction in project PR 2717.
-/

/- Adapted from github.com/DrMurphyIsIn/tenth-discriminant (commit 9078b2bbf205e494b659035465b73e3451738463), determinant/formalization (modules ELEM.* and the vendored CN1.*), (c) the tenth-discriminant authors (DrMurphyIsIn and contributors), Apache-2.0. Proof route: Green and van Dijk derivative determinant, elementary companion of twinheterodox/tenth-discriminant. Ported from Lean v4.34.1 to v4.33.1 (comments stripped, simp lemma tags inlined, bridge to the site statement added). -/
section
open QuadraticAlgebra
namespace ELEM
def cq (q : ℕ) : ℕ := (q + 1) / 4
abbrev OK (c : ℕ) : Type := QuadraticAlgebra ℤ (-(c : ℤ)) 1
abbrev Fp2 (c p : ℕ) : Type := QuadraticAlgebra (ZMod p) (-(c : ZMod p)) 1
def IsInert (c p : ℕ) : Prop := ∀ r : ZMod p, r ^ 2 ≠ -(c : ZMod p) + 1 * r
instance instFactField {c p : ℕ} [h : Fact (IsInert c p)] :
    Fact (∀ r : ZMod p, r ^ 2 ≠ -(c : ZMod p) + 1 * r) := h
def IsSplit (q p : ℕ) : Prop := ¬ IsInert (cq q) p ∧ p ≠ q
noncomputable def A (x : ℕ) : ℝ := ∑ p ∈ Nat.primesLE x, Real.log p / p
open scoped Classical in
noncomputable def Iinert (q x : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE x).filter (fun p => IsInert (cq q) p), Real.log p / p
open scoped Classical in
noncomputable def Splus (q : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p => IsSplit q p), Real.log p / p
noncomputable def B : ℝ := ∑' p : Nat.Primes, Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ 2
def Sof (R : ℕ) : ℕ := R / 12
def Jof (R : ℕ) : ℕ := (R + 47) / 48
noncomputable def A0 (q R : ℕ) : ℕ := ⌈Real.sqrt (R * Real.sqrt q)⌉₊
noncomputable def B0 (q R : ℕ) : ℕ := ⌈Real.sqrt (R / Real.sqrt q)⌉₊
abbrev Row (R : ℕ) : Type := Fin R × Fin (Sof R)
abbrev Node (q R : ℕ) : Type := Fin (2 * A0 q R + 1) × Fin (2 * B0 q R + 1)
abbrev Col (q R : ℕ) : Type := Node q R × Fin (Jof R)
noncomputable def node (q R : ℕ) (n : Node q R) : OK (cq q) :=
  ⟨(n.1 : ℤ) - A0 q R, (n.2 : ℤ) - B0 q R⟩
noncomputable def M (q R : ℕ) : Matrix (Row R) (Col q R) (OK (cq q)) :=
  fun rs zk =>
    ((rs.1 : ℕ).descFactorial (zk.2 : ℕ) : OK (cq q)) * node q R zk.1 ^ ((rs.1 : ℕ) - zk.2) *
      star (node q R zk.1) ^ (rs.2 : ℕ)
noncomputable def minor (q R : ℕ) (f : Row R → Col q R) : OK (cq q) :=
  ((M q R).submatrix id f).det
noncomputable def Delta (q R : ℕ) (f : Row R → Col q R) : ℝ :=
  ((QuadraticAlgebra.norm (minor q R f) : ℤ) : ℝ)
end ELEM
end

section
open Real
namespace ELEM
structure AnalyticSetting (q : ℕ) : Prop where
  large : 32768 ≤ q
  prime : q.Prime
  mod_eight : q % 8 = 3
  inert_of_lt : ∀ p : ℕ, p.Prime → 4 * p < q → IsInert (cq q) p
  rep : ∀ p : ℕ, p.Prime → ¬ IsInert (cq q) p →
    ∃ a b : ℤ, a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p
def LemmaTwoA : Prop :=
  ∀ m : ℕ, 2 ≤ m → Real.log m - 7 / 3 < A m ∧ A m < Real.log m + 3 / 2
def LemmaTwoTheta : Prop :=
  ∀ x : ℝ, 1 ≤ x → Chebyshev.theta x < 3 / 2 * x
def LemmaTwoB : Prop :=
  Summable (fun p : Nat.Primes => Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ 2) ∧ B < 2 / 3
def SplitBound : Prop :=
  ∀ q : ℕ, AnalyticSetting q → ∀ X : ℝ, (q : ℝ) / 4 ≤ X →
    Splus q X ≤ 4 / (5 * √(q : ℝ)) * Real.log X ^ 2 + 4 * (Real.log q + 1) / q
def AuxPrime : Prop :=
  ∀ q : ℕ, AnalyticSetting q → ∃ R : ℕ, R.Prime ∧ IsInert (cq q) R ∧ q ^ 4 < R ∧ R ≤ q ^ 5
def Nonvanishing : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∃ f : Row R → Col q R, minor q R f ≠ 0
def SizeBound : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∀ f : Row R → Col q R, minor q R f ≠ 0 →
      Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R) ≤
        9 / 16 * Real.log R + 25 / 96 * Real.log q + 25 / 24 * Real.log 2 + 6 * Real.log R / R
def DivisibilityBound : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∀ f : Row R → Col q R, minor q R f ≠ 0 →
      Iinert q R - Iinert q R / (2 * Sof R) - 79 / 18 ≤
        Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R)
def Endpoint : Prop :=
  ∀ q R S A I Sp Y : ℝ, 32768 ≤ q → q ^ 4 < R → R ≤ q ^ 5 → R / 13 ≤ S → 0 < S → 0 ≤ Sp →
    A = I + Sp + Real.log q / q →
    Real.log R - 7 / 3 < A → A < Real.log R + 3 / 2 →
    Sp ≤ 4 / (5 * √q) * Real.log R ^ 2 + 4 * (Real.log q + 1) / q →
    Y ≤ 9 / 16 * Real.log R + 25 / 96 * Real.log q + 25 / 24 * Real.log 2 + 6 * Real.log R / R →
    I - I / (2 * S) - 79 / 18 ≤ Y →
    False
def Sieve : Prop :=
  ∀ k < 4096, 8 < 8 * k + 3 →
    8 * k + 3 ∈ ({11, 19, 43, 67, 163} : Finset ℕ) ∨
      ∃ p ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), 4 * p < 8 * k + 3 ∧
        ∃ y < p, (y ^ 2 + (p - 1) * y + (8 * k + 3 + 1) / 4) % p = 0
end ELEM
end

section
namespace CN1.Foundations
open NumberField Module Polynomial
def disc (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m
def principalForm (m : ℕ) (x y : ℤ) : ℤ :=
  if m % 4 = 3 then x ^ 2 + x * y + ((m + 1) / 4 : ℕ) * y ^ 2 else x ^ 2 + m * y ^ 2
variable {K : Type*} [Field K] [NumberField K]
noncomputable def omega (m : ℕ) (α : K) : K := if m % 4 = 3 then (1 + α) / 2 else α
lemma disc_of_three_mod_four {m : ℕ} (h : m % 4 = 3) : disc m = m := by simp [disc, h]
lemma disc_of_not_three_mod_four {m : ℕ} (h : m % 4 ≠ 3) : disc m = 4 * m := by simp [disc, h]
lemma omega_of_three_mod_four {m : ℕ} (α : K) (h : m % 4 = 3) : omega m α = (1 + α) / 2 := by
  simp [omega, h]
lemma omega_of_not_three_mod_four {m : ℕ} (α : K) (h : m % 4 ≠ 3) : omega m α = α := by
  simp [omega, h]
lemma principalForm_of_three_mod_four {m : ℕ} (h : m % 4 = 3) (x y : ℤ) :
    principalForm m x y = x ^ 2 + x * y + ((m + 1) / 4 : ℕ) * y ^ 2 := by
  simp [principalForm, h]
lemma principalForm_of_not_three_mod_four {m : ℕ} (h : m % 4 ≠ 3) (x y : ℤ) :
    principalForm m x y = x ^ 2 + m * y ^ 2 := by
  simp [principalForm, h]
lemma squarefree_not_four_dvd {m : ℕ} (hm : Squarefree m) : ¬ 4 ∣ m := fun h ↦ by
  have := Nat.isUnit_iff.mp (hm 2 (by simpa using h))
  omega
lemma squarefree_mod_four_ne_zero {m : ℕ} (hm : Squarefree m) : m % 4 ≠ 0 :=
  fun h ↦ squarefree_not_four_dvd hm (Nat.dvd_of_mod_eq_zero h)
section FieldModel
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
include hα in
lemma alpha_ne_zero (hm : m ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h : (m : K) = 0 := by rw [← neg_eq_zero, ← hα]; simp
  exact hm (by exact_mod_cast h)
include hα in
lemma linearIndependent_one_alpha (hm : m ≠ 0) : LinearIndependent ℚ ![(1 : K), α] := by
  rw [linearIndependent_fin2]
  refine ⟨by simpa using alpha_ne_zero hα hm, fun a ha ↦ ?_⟩
  change a • α = 1 at ha
  have h2 : ((a : K)) ^ 2 * α ^ 2 = 1 := by rw [← mul_pow, ← Rat.smul_def, ha, one_pow]
  rw [hα] at h2
  have h3 : ((a ^ 2 * (-(m : ℚ)) : ℚ) : K) = ((1 : ℚ) : K) := by push_cast; exact h2
  have h4 : a ^ 2 * (-(m : ℚ)) = 1 := Rat.cast_injective h3
  have h5 : (0 : ℚ) ≤ a ^ 2 := sq_nonneg a
  have h6 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  nlinarith
variable (hK : finrank ℚ K = 2) (hm : m ≠ 0)
include hα hK hm
noncomputable def qBasis : Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_alpha hα hm) (by simp [hK])
lemma qBasis_zero : qBasis hα hK hm 0 = 1 := by simp [qBasis]
lemma qBasis_one : qBasis hα hK hm 1 = α := by simp [qBasis]
lemma qBasis_repr (x : K) (c : Fin 2 → ℚ) (h : x = (c 0 : K) + (c 1 : K) * α) :
    (qBasis hα hK hm).repr x = c := by
  conv_rhs => rw [← (qBasis hα hK hm).repr_sum_self c]
  congr 1
  rw [h, Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]
theorem exists_rat_add_rat_mul_alpha (x : K) : ∃ a b : ℚ, x = (a : K) + (b : K) * α := by
  refine ⟨(qBasis hα hK hm).repr x 0, (qBasis hα hK hm).repr x 1, ?_⟩
  conv_lhs => rw [← (qBasis hα hK hm).sum_repr x]
  rw [Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]
theorem rat_add_rat_mul_alpha_inj {a b a' b' : ℚ}
    (h : (a : K) + (b : K) * α = (a' : K) + (b' : K) * α) : a = a' ∧ b = b' := by
  have h1 := qBasis_repr hα hK hm ((a : K) + (b : K) * α) ![a, b] (by simp)
  have h2 := qBasis_repr hα hK hm ((a' : K) + (b' : K) * α) ![a', b'] (by simp)
  rw [h, h2] at h1
  exact ⟨by simpa using (congrFun h1 0).symm, by simpa using (congrFun h1 1).symm⟩
lemma leftMulMatrix_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.leftMulMatrix (qBasis hα hK hm) ((a : K) + (b : K) * α) =
      !![a, -(m : ℚ) * b; b, a] := by
  set B := qBasis hα hK hm with hB
  have h0 : B.repr (((a : K) + (b : K) * α) * B 0) = ![a, b] := by
    rw [hB, qBasis_zero, mul_one]
    exact qBasis_repr hα hK hm _ _ (by simp)
  have h1 : B.repr (((a : K) + (b : K) * α) * B 1) = ![-(m : ℚ) * b, a] := by
    rw [hB, qBasis_one]
    refine qBasis_repr hα hK hm _ _ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (b : K) * hα
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, h0, h1]
theorem trace_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.trace ℚ K ((a : K) + (b : K) * α) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.trace_fin_two_of]
  ring
theorem norm_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.norm ℚ ((a : K) + (b : K) * α) = a ^ 2 + m * b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.det_fin_two_of]
  ring
end FieldModel
section RingOfIntegers
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
include hα in
theorem omega_isIntegral : IsIntegral ℤ (omega m α) := by
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℤ) ∣ (m : ℤ) + 1 := by omega
    refine ⟨X ^ 2 - X + C c, by monicity!, ?_⟩
    have hcK : (c : K) * 4 = (m : K) + 1 := by exact_mod_cast (by linarith : (c : ℤ) * 4 = m + 1)
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, algebraMap_int_eq,
      Int.coe_castRingHom]
    linear_combination (1 / 4 : K) * hα + (1 / 4 : K) * hcK
  · exact IsIntegral.of_pow two_pos (hα ▸ (isIntegral_natCast m).neg)
include hα in
theorem isIntegral_int_add_int_mul_omega (x y : ℤ) :
    IsIntegral ℤ ((x : K) + (y : K) * omega m α) :=
  (isIntegral_intCast x).add ((isIntegral_intCast y).mul (omega_isIntegral hα))
lemma exists_int_eq_two_mul_of_sq {m : ℕ} (hm : Squarefree m) {b : ℚ} {k : ℤ}
    (h : (m : ℚ) * (2 * b) ^ 2 = k) : ∃ v : ℤ, (v : ℚ) = 2 * b := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne_zero
  have hint : IsIntegral ℤ ((m : ℚ) * (2 * b)) := by
    refine IsIntegral.of_pow two_pos ?_
    have : ((m : ℚ) * (2 * b)) ^ 2 = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_intCast _
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hw
  have hw2 : w ^ 2 = m * k := by
    have : ((w ^ 2 : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [hw]; linear_combination (m : ℚ) * h
    exact_mod_cast this
  have hdvd : (m : ℤ) ∣ w :=
    ((Int.squarefree_natCast.mpr hm).dvd_pow_iff_dvd two_ne_zero).mp ⟨k, hw2⟩
  obtain ⟨v, hv⟩ := hdvd
  refine ⟨v, mul_left_cancel₀ hm0 ?_⟩
  rw [← hw, hv]; push_cast; ring
lemma zmod_four_three (t v : ZMod 4) (h : t ^ 2 + 3 * v ^ 2 = 0) : 2 * (t - v) = 0 := by
  revert t v; decide
lemma zmod_four_one (t v : ZMod 4) (h : t ^ 2 + v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide
lemma zmod_four_two (t v : ZMod 4) (h : t ^ 2 + 2 * v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide
variable (hK : finrank ℚ K = 2) (hm : Squarefree m)
include hα hK hm in
theorem exists_int_add_int_mul_omega_of_isIntegral {x : K} (hx : IsIntegral ℤ x) :
    ∃ u v : ℤ, x = (u : K) + (v : K) * omega m α := by
  have hm0 := hm.ne_zero
  obtain ⟨a, b, rfl⟩ := exists_rat_add_rat_mul_alpha hα hK hm0 x
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hx)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (K := ℚ) hx)
  rw [trace_rat_add_rat_mul_alpha hα hK hm0] at ht
  rw [norm_rat_add_rat_mul_alpha hα hK hm0] at hn
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at ht hn
  obtain ⟨v, hv⟩ := exists_int_eq_two_mul_of_sq hm (b := b) (k := 4 * n - t ^ 2)
    (by push_cast; rw [hn, ht]; ring)
  have h4 : (4 : ℤ) ∣ t ^ 2 + m * v ^ 2 := by
    refine ⟨n, ?_⟩
    have : ((t ^ 2 + m * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast; rw [hv, ht, hn]; ring
    exact_mod_cast this
  have h4' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
  push_cast at h4'
  have ht' : (t : K) = 2 * (a : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) ht
  have hv' : (v : K) = 2 * (b : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) hv
  unfold omega
  split_ifs with h3
  · have hm4 : ((m : ℕ) : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, h3]; rfl
    rw [hm4] at h4'
    have key := zmod_four_three _ _ h4'
    have h2 : (2 : ℤ) ∣ t - v := by
      have : ((2 * (t - v) : ℤ) : ZMod 4) = 0 := by push_cast; exact key
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
      omega
    obtain ⟨u, hu⟩ := h2
    refine ⟨u, v, ?_⟩
    have hu' : (t : K) - (v : K) = 2 * (u : K) := by exact_mod_cast hu
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu'
  · have h12 : m % 4 = 1 ∨ m % 4 = 2 := by have := squarefree_mod_four_ne_zero hm; omega
    have h2 : (2 : ℤ) ∣ t ∧ (2 : ℤ) ∣ v := by
      have key : 2 * (t : ZMod 4) = 0 ∧ 2 * (v : ZMod 4) = 0 := by
        rcases h12 with h1 | h1
        · have hm4 : ((m : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4, one_mul] at h4'
          exact zmod_four_one _ _ h4'
        · have hm4 : ((m : ℕ) : ZMod 4) = 2 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4] at h4'
          exact zmod_four_two _ _ h4'
      constructor
      · have : ((2 * t : ℤ) : ZMod 4) = 0 := by push_cast; exact key.1
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
      · have : ((2 * v : ℤ) : ZMod 4) = 0 := by push_cast; exact key.2
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := h2
    refine ⟨u, w, ?_⟩
    have hu' : (t : K) = 2 * (u : K) := by exact_mod_cast hu
    have hw' : (v : K) = 2 * (w : K) := by exact_mod_cast hw
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu' + (α / 2) * hw'
include hα hK in
theorem int_add_int_mul_omega_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : K) + (v : K) * omega m α = (u' : K) + (v' : K) * omega m α) : u = u' ∧ v = v' := by
  unfold omega at h
  split_ifs at h with h3
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    have hv : v = v' := by
      have : (v : ℚ) = v' := by linarith
      exact_mod_cast this
    refine ⟨?_, hv⟩
    have : (u : ℚ) = u' := by rw [hv] at h1; linarith
    exact_mod_cast this
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
noncomputable def omegaInt : 𝓞 K := ⟨omega m α, omega_isIntegral hα⟩
lemma coe_omegaInt : (omegaInt hα : K) = omega m α := rfl
lemma coe_int_add_int_mul_omegaInt (u v : ℤ) :
    (((u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα : 𝓞 K) : K) = (u : K) + (v : K) * omega m α := by
  rw [RingOfIntegers.coe_eq_algebraMap]; simp [coe_omegaInt]
include hα hK hm in
theorem exists_int_add_int_mul_omegaInt (z : 𝓞 K) :
    ∃ u v : ℤ, z = (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα := by
  obtain ⟨u, v, h⟩ := exists_int_add_int_mul_omega_of_isIntegral hα hK hm z.isIntegral_coe
  exact ⟨u, v, RingOfIntegers.ext (by rw [coe_int_add_int_mul_omegaInt]; exact h)⟩
include hα hK in
theorem int_add_int_mul_omegaInt_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα = (u' : 𝓞 K) + (v' : 𝓞 K) * omegaInt hα) :
    u = u' ∧ v = v' := by
  apply int_add_int_mul_omega_inj hα hK hm0
  rw [← coe_int_add_int_mul_omegaInt hα, ← coe_int_add_int_mul_omegaInt hα, h]
noncomputable def intBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (v := ![1, omegaInt hα])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h : (s : 𝓞 K) + (t : 𝓞 K) * omegaInt hα =
          ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * omegaInt hα := by
        simpa [zsmul_eq_mul] using hst
      exact int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h)
    (by
      rintro z -
      rw [Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
      refine ⟨![u, v], ?_⟩
      rw [huv, Fin.sum_univ_two]
      simp [zsmul_eq_mul])
lemma intBasis_zero : intBasis hα hK hm 0 = 1 := by simp [intBasis]
lemma intBasis_one : intBasis hα hK hm 1 = omegaInt hα := by simp [intBasis]
end RingOfIntegers
section NormForm
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm0 : m ≠ 0)
include hα hK hm0 in
theorem norm_int_add_int_mul_omega (x y : ℤ) :
    Algebra.norm ℚ ((x : K) + (y : K) * omega m α) = (principalForm m x y : ℚ) := by
  unfold omega principalForm
  split_ifs with h3
  · have e : (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by push_cast; ring
    rw [e, norm_rat_add_rat_mul_alpha hα hK hm0]
    obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hcq : (m : ℚ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination ((y : ℚ) ^ 2 / 4) * hcq
  · have e : (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by push_cast; ring
    rw [e, norm_rat_add_rat_mul_alpha hα hK hm0]
    push_cast; ring
include hα hK hm0 in
theorem trace_int_add_int_mul_omega (x y : ℤ) :
    Algebra.trace ℚ K ((x : K) + (y : K) * omega m α) =
      if m % 4 = 3 then (2 * x + y : ℚ) else (2 * x : ℚ) := by
  unfold omega
  split_ifs with h3
  · have e : (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]; ring
  · have e : (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]
include hα hK hm0 in
theorem norm_int_eq_principalForm {z : 𝓞 K} {x y : ℤ}
    (h : z = (x : 𝓞 K) + (y : 𝓞 K) * omegaInt hα) :
    Algebra.norm ℤ z = principalForm m x y := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int, h, coe_int_add_int_mul_omegaInt, norm_int_add_int_mul_omega hα hK hm0]
theorem principalForm_nonneg (m : ℕ) (x y : ℤ) : 0 ≤ principalForm m x y := by
  unfold principalForm
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have hc1 : (1 : ℤ) ≤ c := by omega
    nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
  · positivity
theorem principalForm_eq_one {m : ℕ} (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {x y : ℤ}
    (h : principalForm m x y = 1) : y = 0 ∧ (x = 1 ∨ x = -1) := by
  have hm0 := hm.ne_zero
  unfold principalForm at h
  split_ifs at h with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc'] at h
    have hm7 : (7 : ℤ) ≤ m := by omega
    have hcz : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    have hy : y = 0 := by
      by_contra hy
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : (1 : ℤ) ≤ y ^ 2 := by omega
      nlinarith [sq_nonneg (2 * x + y)]
    subst hy
    refine ⟨rfl, Int.eq_one_or_neg_one_of_mul_eq_one (v := x) ?_⟩
    nlinarith
  · have hm2 : (2 : ℤ) ≤ m := by omega
    have hy : y = 0 := by
      by_contra hy
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : (1 : ℤ) ≤ y ^ 2 := by omega
      nlinarith
    subst hy
    refine ⟨rfl, Int.eq_one_or_neg_one_of_mul_eq_one (v := x) ?_⟩
    nlinarith
end NormForm
section Units
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm : Squarefree m)
include hα hK hm in
theorem coe_unit_eq_one_or_neg_one (hm1 : m ≠ 1) (hm3 : m ≠ 3) (ε : (𝓞 K)ˣ) :
    (ε : 𝓞 K) = 1 ∨ (ε : 𝓞 K) = -1 := by
  obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm (ε : 𝓞 K)
  have hN : IsUnit (Algebra.norm ℤ (ε : 𝓞 K)) := ε.isUnit.map (Algebra.norm ℤ)
  rw [norm_int_eq_principalForm hα hK hm.ne_zero huv] at hN
  have hQ : principalForm m u v = 1 := by
    rcases Int.isUnit_iff.mp hN with h | h
    · exact h
    · have := principalForm_nonneg m u v; omega
  obtain ⟨rfl, hu⟩ := principalForm_eq_one hm hm1 hm3 hQ
  rw [huv]
  rcases hu with rfl | rfl
  · left; simp
  · right; simp
include hα hK hm in
theorem eq_one_or_neg_one_of_norm_eq_one (hm1 : m ≠ 1) (hm3 : m ≠ 3) {z : 𝓞 K}
    (h : Algebra.norm ℤ z = 1) : z = 1 ∨ z = -1 := by
  obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  rw [norm_int_eq_principalForm hα hK hm.ne_zero huv] at h
  obtain ⟨rfl, hu⟩ := principalForm_eq_one hm hm1 hm3 h
  rw [huv]
  rcases hu with rfl | rfl
  · left; simp
  · right; simp
end Units
end CN1.Foundations
end

section
namespace CN1.Foundations
open ZMod
open DirichletCharacter (changeLevel changeLevel_eq_cast_of_dvd changeLevel_eq_cast_of_dvd')
section JacobiChar
lemma jacobiSym_val_eq (n : ℕ) [NeZero n] (a : ZMod n) (k : ℤ) (hk : (k : ZMod n) = a) :
    jacobiSym a.val n = jacobiSym k n := by
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff']
  simp [hk]
noncomputable def jacobiChar (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun a := (jacobiSym a.val n : ℂ)
  map_one' := by
    show (jacobiSym (1 : ZMod n).val n : ℂ) = 1
    rw [jacobiSym_val_eq n 1 1 (by simp), jacobiSym.one_left]; simp
  map_mul' a b := by
    show (jacobiSym (a * b).val n : ℂ) = (jacobiSym a.val n : ℂ) * (jacobiSym b.val n : ℂ)
    rw [jacobiSym_val_eq n (a * b) (a.val * b.val) (by simp), jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' a ha := by
    show (jacobiSym a.val n : ℂ) = 0
    have hc : ¬ Nat.Coprime a.val n := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have : jacobiSym a.val n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hc
    rw [this]; simp
lemma jacobiChar_apply (n : ℕ) [NeZero n] (a : ZMod n) :
    jacobiChar n a = (jacobiSym a.val n : ℂ) := rfl
theorem jacobiChar_intCast (n : ℕ) [NeZero n] (k : ℤ) :
    jacobiChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  rw [jacobiChar_apply, jacobiSym_val_eq n _ k rfl]
theorem jacobiChar_natCast (n : ℕ) [NeZero n] (k : ℕ) :
    jacobiChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  rw [← Int.cast_natCast, jacobiChar_intCast]
theorem jacobiChar_isQuadratic (n : ℕ) [NeZero n] : (jacobiChar n).IsQuadratic := by
  intro a
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy a.val n with h | h | h <;> rw [h] <;> norm_num
end JacobiChar
noncomputable def chi4 : DirichletCharacter ℂ 4 := χ₄.ringHomComp (Int.castRingHom ℂ)
noncomputable def chi8 : DirichletCharacter ℂ 8 := χ₈.ringHomComp (Int.castRingHom ℂ)
noncomputable def chi8' : DirichletCharacter ℂ 8 := χ₈'.ringHomComp (Int.castRingHom ℂ)
lemma chi4_apply (a : ZMod 4) : chi4 a = (χ₄ a : ℂ) := rfl
lemma chi8_apply (a : ZMod 8) : chi8 a = (χ₈ a : ℂ) := rfl
lemma chi8'_apply (a : ZMod 8) : chi8' a = (χ₈' a : ℂ) := rfl
lemma chi4_isQuadratic : chi4.IsQuadratic := isQuadratic_χ₄.comp _
lemma chi8_isQuadratic : chi8.IsQuadratic := isQuadratic_χ₈.comp _
lemma chi8'_isQuadratic : chi8'.IsQuadratic := isQuadratic_χ₈'.comp _
section Quadratic
variable {R : Type*} [CommRing R]
lemma isQuadratic_changeLevel {n N : ℕ} (h : n ∣ N) {ψ : DirichletCharacter R n}
    (hψ : ψ.IsQuadratic) : (changeLevel h ψ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [changeLevel_eq_cast_of_dvd]
    exact hψ _
  · left; exact MulChar.map_nonunit _ ha
lemma isQuadratic_mul {M : Type*} [CommMonoid M] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [MulChar.mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']
lemma isQuadratic_one {M : Type*} [CommMonoid M] [Nontrivial R] :
    (1 : MulChar M R).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · right; left; exact MulChar.one_apply ha
  · left; exact MulChar.map_nonunit _ ha
end Quadratic
section Kronecker
variable {m : ℕ}
lemma four_dvd_disc (h3 : m % 4 ≠ 3) : 4 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_right 4 m
lemma dvd_disc (h3 : m % 4 ≠ 3) : m ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_left m 4
lemma eight_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : 8 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨m / 2, by omega⟩
lemma half_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : m / 2 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨8, by omega⟩
noncomputable def kroneckerChar (m : ℕ) : DirichletCharacter ℂ (disc m) :=
  if h0 : m = 0 then 1
  else if h3 : m % 4 = 3 then
    changeLevel (dvd_of_eq (disc_of_three_mod_four h3).symm) (@jacobiChar m ⟨h0⟩)
  else if h2 : m % 2 = 1 then
    changeLevel (four_dvd_disc h3) chi4 * changeLevel (dvd_disc h3) (@jacobiChar m ⟨h0⟩)
  else
    changeLevel (eight_dvd_disc h3 (by omega)) (if m / 2 % 4 = 1 then chi8' else chi8) *
      changeLevel (half_dvd_disc h3 (by omega)) (@jacobiChar (m / 2) ⟨by omega⟩)
theorem kroneckerChar_apply_of_three_mod_four (h3 : m % 4 = 3) {a : ℤ}
    (ha : IsCoprime a (disc m)) : kroneckerChar m (a : ZMod (disc m)) = (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  simp only [kroneckerChar, h0, h3, ↓reduceDIte]
  rw [changeLevel_eq_cast_of_dvd' _ _ ha, jacobiChar_intCast]
theorem kroneckerChar_apply_of_one_mod_four (h1 : m % 4 = 1) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) = (χ₄ a : ℂ) * (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2 : m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast, chi4_apply]
theorem kroneckerChar_apply_of_two_mod_four (h2 : m % 4 = 2) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) =
      (if m / 2 % 4 = 1 then (χ₈' a : ℂ) else (χ₈ a : ℂ)) * (jacobiSym a (m / 2) : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2' : ¬ m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2', ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast]
  split_ifs <;> rfl
theorem kroneckerChar_isQuadratic (m : ℕ) : (kroneckerChar m).IsQuadratic := by
  by_cases h0 : m = 0
  · simp only [kroneckerChar, h0, ↓reduceDIte]
    exact isQuadratic_one
  have : NeZero m := ⟨h0⟩
  by_cases h3 : m % 4 = 3
  · simp only [kroneckerChar, h0, h3, ↓reduceDIte]
    exact isQuadratic_changeLevel _ (jacobiChar_isQuadratic m)
  by_cases h2 : m % 2 = 1
  · simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    exact isQuadratic_mul (isQuadratic_changeLevel _ chi4_isQuadratic)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic m))
  · have : NeZero (m / 2) := ⟨by omega⟩
    simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    refine isQuadratic_mul (isQuadratic_changeLevel _ ?_)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic (m / 2)))
    split_ifs
    · exact chi8'_isQuadratic
    · exact chi8_isQuadratic
lemma squarefree_mod_four_cases (hm : Squarefree m) : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
  have := squarefree_mod_four_ne_zero hm; omega
theorem kroneckerChar_neg_one (hm : Squarefree m) : kroneckerChar m (-1) = -1 := by
  have hcop : IsCoprime (-1 : ℤ) (disc m : ℤ) := isCoprime_one_left.neg_left
  have hcast : (-1 : ZMod (disc m)) = ((-1 : ℤ) : ZMod (disc m)) := by simp
  rw [hcast]
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · rw [kroneckerChar_apply_of_one_mod_four h1 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), χ₄_nat_one_mod_four h1,
      χ₄_int_three_mod_four (by decide)]
    simp
  · rw [kroneckerChar_apply_of_two_mod_four h2 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega))]
    have hm' : m / 2 % 4 = 1 ∨ m / 2 % 4 = 3 := by omega
    rcases hm' with h | h
    · rw [if_pos h, χ₄_nat_one_mod_four h, χ₈'_int_eq_if_mod_eight]
      norm_num
    · rw [if_neg (by omega), χ₄_nat_three_mod_four h, χ₈_int_eq_if_mod_eight]
      norm_num
  · rw [kroneckerChar_apply_of_three_mod_four h3 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), χ₄_nat_three_mod_four h3]
    simp
theorem kroneckerChar_ne_one (hm : Squarefree m) : kroneckerChar m ≠ 1 := by
  intro h
  have h1 := kroneckerChar_neg_one hm
  rw [h, MulChar.one_apply isUnit_one.neg] at h1
  norm_num at h1
section Values
variable {p : ℕ} [hp : Fact p.Prime]
lemma jacobiSym_eq_legendreSym_neg_of_three_mod_four (h3 : m % 4 = 3) (hp2 : p ≠ 2) :
    jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym]
  rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.mpr (by omega)),
      χ₄_nat_one_mod_four h1, one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h3, χ₄_nat_three_mod_four h1,
      neg_one_mul]
lemma chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four (h1 : m % 4 = 1) (hp2 : p ≠ 2) :
    χ₄ p * jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : _root_.Odd p := hp.out.odd_of_ne_two hp2
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym.quadratic_reciprocity_one_mod_four' hpodd h1]
lemma chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four (h2 : m % 4 = 2) (hp2 : p ≠ 2) :
    (if m / 2 % 4 = 1 then χ₈' p else χ₈ p) * jacobiSym p (m / 2) = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hm : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by push_cast; omega
  have hm'odd : _root_.Odd (m / 2) := Nat.odd_iff.mpr (by omega)
  rw [hm, neg_mul_eq_neg_mul, legendreSym.mul, legendreSym.at_neg_two hp2,
    jacobiSym.legendreSym.to_jacobiSym]
  have hm' : m / 2 % 4 = 1 ∨ m / 2 % 4 = 3 := by omega
  rcases hm' with h | h
  · rw [if_pos h, jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hpodd) h]
  · rw [if_neg (by omega)]
    have h8 : χ₈' (p : ZMod 8) = χ₄ (p : ZMod 4) * χ₈ (p : ZMod 8) := by
      have := χ₈'_int_eq_χ₄_mul_χ₈ (p : ℤ)
      simpa using this
    rw [h8]
    rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hm'odd, χ₄_nat_one_mod_four h1, one_mul]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h, χ₄_nat_three_mod_four h1]
      ring
theorem kroneckerChar_apply_prime_of_ne_two (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = (legendreSym p (-(m : ℤ)) : ℂ) := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  rw [← Int.cast_natCast (R := ZMod (disc m))]
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · rw [kroneckerChar_apply_of_one_mod_four h1 hcop,
      ← chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four h1 hp2]
    push_cast
    try rfl
  · rw [kroneckerChar_apply_of_two_mod_four h2 hcop,
      ← chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four h2 hp2]
    split_ifs <;> push_cast <;> try rfl
  · rw [kroneckerChar_apply_of_three_mod_four h3 hcop,
      ← jacobiSym_eq_legendreSym_neg_of_three_mod_four h3 hp2]
theorem kroneckerChar_apply_two (h3 : m % 4 = 3) :
    kroneckerChar m (2 : ZMod (disc m)) = (χ₈ (m : ZMod 8) : ℂ) := by
  have hodd : _root_.Odd m := Nat.odd_iff.mpr (by omega)
  have hcop : IsCoprime (2 : ℤ) (disc m : ℤ) := by
    rw [disc_of_three_mod_four h3]
    have : IsCoprime ((2 : ℕ) : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast this
  have hcast : (2 : ZMod (disc m)) = ((2 : ℤ) : ZMod (disc m)) := by simp
  rw [hcast, kroneckerChar_apply_of_three_mod_four h3 hcop, jacobiSym.at_two hodd]
lemma neg_natCast_ne_zero_of_not_dvd_disc (hpd : ¬ p ∣ disc m) : (-(m : ZMod p)) ≠ 0 := by
  rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  refine hpd (h.trans ?_)
  unfold disc; split_ifs
  · exact dvd_rfl
  · exact dvd_mul_left m 4
theorem kroneckerChar_apply_prime_eq_one_iff (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔ IsSquare (-(m : ZMod p)) := by
  rw [kroneckerChar_apply_prime_of_ne_two hm hp2 hpd]
  have hne : ((-(m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact neg_natCast_ne_zero_of_not_dvd_disc hpd
  have := legendreSym.eq_one_iff p hne
  push_cast at this
  rw [← this]
  norm_cast
theorem kroneckerChar_apply_prime_eq_neg_one_iff (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = -1 ↔ ¬ IsSquare (-(m : ZMod p)) := by
  rw [kroneckerChar_apply_prime_of_ne_two hm hp2 hpd]
  have := legendreSym.eq_neg_one_iff p (a := -(m : ℤ))
  push_cast at this
  rw [← this]
  norm_cast
end Values
end Kronecker
end CN1.Foundations
end

section
namespace CN1.Foundations
open NumberField Polynomial Ideal
def bInt (m : ℕ) : ℤ := if m % 4 = 3 then -1 else 0
def cInt (m : ℕ) : ℤ := if m % 4 = 3 then ((m + 1) / 4 : ℕ) else m
theorem bInt_sq_sub_four_mul_cInt (m : ℕ) : bInt m ^ 2 - 4 * cInt m = -(disc m : ℤ) := by
  unfold bInt cInt disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring
section Setup
variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)
include hα hK hm in
theorem adjoin_omegaInt_eq_top : Algebra.adjoin ℤ {omegaInt hα} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))
include hα hK hm in
theorem exponent_omegaInt_eq_one : RingOfIntegers.exponent (omegaInt hα) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (adjoin_omegaInt_eq_top hα hK hm)
include hα hK hm in
theorem not_dvd_exponent_omegaInt (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (omegaInt hα) := by
  rw [exponent_omegaInt_eq_one hα hK hm]; exact hp.out.not_dvd_one
include hα in
theorem minpoly_rat_omega (hm0 : m ≠ 0) :
    minpoly ℚ (omega m α) = X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ) := by
  have hmpos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ)).natDegree = 2 := by
        compute_degree!
      rw [hdeg]; decide
    · intro x hx
      rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
      unfold bInt cInt at hx
      split_ifs at hx with h3
      · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
        have hc' : ((m + 1) / 4 : ℕ) = c := by omega
        rw [hc'] at hx
        push_cast at hx
        have hcq : (m : ℚ) + 1 = 4 * c := by exact_mod_cast hc
        nlinarith [sq_nonneg (2 * x - 1)]
      · push_cast at hx
        nlinarith [sq_nonneg x]
  · rw [map_add, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_C, eq_ratCast, eq_ratCast]
    unfold omega bInt cInt
    split_ifs with h3
    · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
      have hc' : ((m + 1) / 4 : ℕ) = c := by omega
      rw [hc']
      push_cast
      have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
      linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
    · push_cast
      linear_combination hα
  · monicity!
include hα in
theorem minpoly_int_omegaInt (hm0 : m ≠ 0) :
    minpoly ℤ (omegaInt hα) = X ^ 2 + C (bInt m) * X + C (cInt m) := by
  rw [← RingOfIntegers.minpoly_coe, coe_omegaInt]
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (omega_isIntegral hα),
    minpoly_rat_omega hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
include hα hK in
theorem minpoly_omegaInt (hm0 : m ≠ 0) :
    minpoly ℤ (omegaInt hα) =
      if m % 4 = 3 then X ^ 2 - X + C (((m + 1) / 4 : ℕ) : ℤ) else X ^ 2 + C (m : ℤ) := by
  rw [minpoly_int_omegaInt hα hm0]
  unfold bInt cInt
  split_ifs <;> simp <;> ring
section Prime
variable (p : ℕ) [hp : Fact p.Prime]
include hα in
theorem minpoly_omegaInt_map (hm0 : m ≠ 0) :
    (minpoly ℤ (omegaInt hα)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p) := by
  rw [minpoly_int_omegaInt hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
lemma quad_eq_mul_of_root (b c r : ZMod p) (hr : r ^ 2 + b * r + c = 0) :
    X ^ 2 + C b * X + C c = (X - C r) * (X - C (-b - r)) := by
  have hc : c = -(r ^ 2) - b * r := by linear_combination hr
  rw [hc]
  simp only [map_sub, map_neg, map_mul, map_pow]
  ring
lemma natDegree_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).natDegree = 2 := by
  compute_degree!
lemma monic_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).Monic := by
  monicity!
lemma irreducible_quad_of_no_root (b c : ZMod p) (h : ∀ x : ZMod p, x ^ 2 + b * x + c ≠ 0) :
    Irreducible (X ^ 2 + C b * X + C c) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_quad]; decide
  · intro x hx
    apply h x
    rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
    exact hx
include hα hK hm in
theorem monicFactorsMod_of_root {r : ZMod p} (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X - C r, X - C (-(bInt m : ZMod p) - r)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero, quad_eq_mul_of_root p _ _ r hr,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, (monic_X_sub_C _).normalize_eq_self,
    Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
include hα hK hm in
theorem monicFactorsMod_of_no_root
    (h : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_quad_of_no_root p _ _ h),
    (monic_quad p _ _).normalize_eq_self, Multiset.toFinset_singleton]
include hα hK hm in
theorem ncard_primesOver_eq_card_monicFactorsMod :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard =
      (RingOfIntegers.monicFactorsMod (omegaInt hα) p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)),
    Nat.card_eq_finsetCard]
include hα hK hm in
theorem inertiaDeg_eq_natDegree {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    P.inertiaDeg ℤ =
      ((Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩ :
        (ZMod p)[X])).natDegree := by
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (not_dvd_exponent_omegaInt hα hK hm p) (e ⟨P, hP⟩).2
  rwa [Subtype.coe_eta, e.symm_apply_apply] at this
lemma root_ne_other_root (hpd : ¬ p ∣ disc m) {r : ZMod p}
    (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) : r ≠ -(bInt m : ZMod p) - r := by
  intro heq
  apply hpd
  rw [← ZMod.natCast_eq_zero_iff]
  have hdisc : (bInt m : ZMod p) ^ 2 - 4 * (cInt m : ZMod p) = -(disc m : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) (bInt_sq_sub_four_mul_cInt m)
  linear_combination hdisc + (-(2 * r + (bInt m : ZMod p))) * heq + 4 * hr
lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
theorem exists_root_iff_isSquare (hp2 : p ≠ 2) :
    (∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0) ↔ IsSquare (-(m : ZMod p)) := by
  have h2 := two_ne_zero_of_ne_two p hp2
  unfold bInt cInt
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hc4 : (m : ZMod p) + 1 = 4 * c := by
      have := congrArg (Nat.cast (R := ZMod p)) hc
      push_cast at this
      exact this
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨2 * x - 1, by linear_combination (-4 : ZMod p) * hx + (-1 : ZMod p) * hc4⟩
    · rintro ⟨y, hy⟩
      refine ⟨(y + 1) * 2⁻¹, ?_⟩
      have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have h4 : (4 : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have key : (4 : ZMod p) * (((y + 1) * 2⁻¹) ^ 2 + -1 * ((y + 1) * 2⁻¹) + c) = 0 := by
        linear_combination ((y + 1) ^ 2 * (2 * 2⁻¹ + 1)) * hi + (-2 * (y + 1)) * hi
          + (-1 : ZMod p) * hy + (-1 : ZMod p) * hc4
      exact (mul_eq_zero.mp key).resolve_left h4
  · push_cast
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by linear_combination -hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by linear_combination -hy⟩
theorem exists_root_two_iff (h3 : m % 4 = 3) :
    (∃ x : ZMod 2, x ^ 2 + (bInt m : ZMod 2) * x + cInt m = 0) ↔ m % 8 = 7 := by
  unfold bInt cInt
  rw [if_pos h3, if_pos h3]
  obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
  have hc' : ((m + 1) / 4 : ℕ) = c := by omega
  rw [hc']
  have key : ∀ c' : ZMod 2, (∃ x : ZMod 2, x ^ 2 + ((-1 : ℤ) : ZMod 2) * x + ((c' : ZMod 2)) = 0) ↔
      c' = 0 := by decide
  rw [show ((c : ℤ) : ZMod 2) = ((c : ℕ) : ZMod 2) from Int.cast_natCast c, key,
    ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  omega
include hm in
theorem kroneckerChar_eq_one_iff_exists_root (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔
      ∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h3 : m % 4 = 3 := by
      by_contra h3
      exact hpd (by rw [disc_of_not_three_mod_four h3]; exact ⟨2 * m, by ring⟩)
    rw [exists_root_two_iff h3, show ((2 : ℕ) : ZMod (disc m)) = 2 from Nat.cast_ofNat,
      kroneckerChar_apply_two h3, ZMod.χ₈_nat_eq_if_mod_eight]
    have h8 : m % 8 = 3 ∨ m % 8 = 7 := by omega
    rcases h8 with h | h
    · rw [if_neg (by omega), if_neg (by omega)]
      norm_num
      omega
    · rw [if_neg (by omega), if_pos (by omega)]
      norm_num
      exact h
  · rw [kroneckerChar_apply_prime_eq_one_iff hm hp2 hpd, exists_root_iff_isSquare p hp2]
theorem kroneckerChar_eq_one_or_neg_one (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ∨ kroneckerChar m (p : ZMod (disc m)) = -1 := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  have hne : kroneckerChar m (p : ZMod (disc m)) ≠ 0 := by
    rw [← Int.cast_natCast (R := ZMod (disc m))]
    exact (DirichletCharacter.apply_ne_zero_iff _ _).mpr hcop
  rcases kroneckerChar_isQuadratic m (p : ZMod (disc m)) with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h
include hα hK hm in
theorem ncard_primesOver_eq_two_of_kroneckerChar_eq_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 := by
  obtain ⟨r, hr⟩ := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mp h1
  have hF := monicFactorsMod_of_root hα hK hm p hr
  have hne : X - C r ≠ X - C (-(bInt m : ZMod p) - r) := by
    intro h
    exact root_ne_other_root p hpd hr (C_inj.mp (sub_right_injective h))
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF]
    exact Finset.card_pair_eq_two_iff.mpr hne
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h, natDegree_X_sub_C]
include hα hK hm in
theorem ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 := by
  have hno : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0 := by
    intro x hx
    have := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mpr ⟨x, hx⟩
    rw [h1] at this
    norm_num at this
  have hF := monicFactorsMod_of_no_root hα hK hm p hno
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF, Finset.card_singleton]
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_singleton] at hmem
    rw [hmem, natDegree_quad]
include hα hK hm in
theorem ncard_primesOver_eq_two_iff (hpd : ¬ p ∣ disc m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ↔ kroneckerChar m (p : ZMod (disc m)) = 1 := by
  rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
  · simp only [h, iff_true]
    exact (ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h).1
  · rw [h, (ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h).1]
    norm_num
include hα hK hm in
theorem ncard_primesOver_eq_one_iff (hpd : ¬ p ∣ disc m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ↔ kroneckerChar m (p : ZMod (disc m)) = -1 := by
  rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
  · rw [h, (ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h).1]
    norm_num
  · simp only [h, iff_true]
    exact (ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h).1
include hα hK hm in
theorem exists_prime_absNorm_eq_of_kroneckerChar_eq_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = 1) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ absNorm P = p := by
  obtain ⟨hcard, hdeg⟩ := ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h1
  obtain ⟨P, hP⟩ := Set.nonempty_of_ncard_ne_zero (s := primesOver (span {(p : ℤ)}) (𝓞 K))
    (by rw [hcard]; norm_num)
  have := hP.1
  have := hP.2
  refine ⟨P, hP.1, ?_⟩
  rw [← Ideal.pow_inertiaDeg p P, hdeg P hP, pow_one]
end Prime
end Setup
end CN1.Foundations
end

section
namespace CN1.Foundations
open NumberField Module
variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : finrank ℚ K = 2)
include hα hK in
theorem trace_int_eq (hm0 : m ≠ 0) {z : 𝓞 K} {x y : ℤ}
    (h : z = (x : 𝓞 K) + (y : 𝓞 K) * omegaInt hα) :
    Algebra.trace ℤ (𝓞 K) z = if m % 4 = 3 then 2 * x + y else 2 * x := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_trace_int, h, coe_int_add_int_mul_omegaInt, trace_int_add_int_mul_omega hα hK hm0]
  split_ifs <;> push_cast <;> ring
include hα in
theorem omegaInt_sq :
    omegaInt hα ^ 2 = ((if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ) : ℤ) : 𝓞 K) +
      ((if m % 4 = 3 then 1 else 0 : ℤ) : 𝓞 K) * omegaInt hα := by
  apply RingOfIntegers.ext
  rw [coe_int_add_int_mul_omegaInt, RingOfIntegers.coe_eq_algebraMap, map_pow,
    ← RingOfIntegers.coe_eq_algebraMap, coe_omegaInt]
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
  · push_cast
    linear_combination hα
include hα hK in
theorem discr_eq (hm : Squarefree m) : NumberField.discr K = -(disc m : ℤ) := by
  have hm0 := hm.ne_zero
  rw [← NumberField.discr_eq_discr K (intBasis hα hK hm), Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, intBasis_zero, intBasis_one,
    one_mul, mul_one]
  have h1 : Algebra.trace ℤ (𝓞 K) (1 : 𝓞 K) = if m % 4 = 3 then 2 * 1 + 0 else 2 * 1 :=
    trace_int_eq hα hK hm0 (x := 1) (y := 0) (by simp)
  have h2 : Algebra.trace ℤ (𝓞 K) (omegaInt hα) = if m % 4 = 3 then 2 * 0 + 1 else 2 * 0 :=
    trace_int_eq hα hK hm0 (x := 0) (y := 1) (by simp)
  have h3 : Algebra.trace ℤ (𝓞 K) (omegaInt hα * omegaInt hα) =
      if m % 4 = 3 then 2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) +
        (if m % 4 = 3 then 1 else 0) else
        2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) :=
    trace_int_eq hα hK hm0 (by rw [← sq, omegaInt_sq hα])
  rw [h1, h2, h3]
  unfold disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring
end CN1.Foundations
end

section
namespace CN1.Finite
def tOf (m : ℕ) : ℕ := if m % 4 = 3 then 1 else 0
def cOf (m : ℕ) : ℕ := if m % 4 = 3 then (m + 1) / 4 else m
def dOf (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m
theorem tOf_eq_zero_or_one (m : ℕ) : tOf m = 0 ∨ tOf m = 1 := by
  unfold tOf; split_ifs <;> simp
theorem four_mul_cOf (m : ℕ) : 4 * cOf m = dOf m + tOf m ^ 2 := by
  unfold cOf dOf tOf; split_ifs with h <;> norm_num <;> omega
theorem le_dOf (m : ℕ) : m ≤ dOf m := by
  unfold dOf; split_ifs <;> omega
theorem tOf_of_mod (m : ℕ) (h : m % 4 = 3) : tOf m = 1 := by simp [tOf, h]
theorem four_mul_cOf_of_mod (m : ℕ) (h : m % 4 = 3) : 4 * cOf m = m + 1 := by
  simp only [cOf, h, if_true]; omega
theorem dOf_of_mod (m : ℕ) (h : m % 4 = 3) : dOf m = m := by simp [dOf, h]
end CN1.Finite
end

section
namespace CN1.Finite
theorem four_mul_form (t c x y : ℤ) :
    4 * (x ^ 2 + t * x * y + c * y ^ 2) = (2 * x + t * y) ^ 2 + (4 * c - t ^ 2) * y ^ 2 := by
  ring
theorem form_nonneg {t c : ℤ} (hd : 0 ≤ 4 * c - t ^ 2) (x y : ℤ) :
    0 ≤ x ^ 2 + t * x * y + c * y ^ 2 := by
  have h := four_mul_form t c x y
  nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd (sq_nonneg y)]
theorem not_prime_eq_sq {p : ℕ} (hp : p.Prime) (x : ℤ) : (p : ℤ) ≠ x ^ 2 := by
  intro h
  have h' : p = x.natAbs ^ 2 := by
    have : (p : ℤ) = (x.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq]; exact h
    exact_mod_cast this
  have hdvd : x.natAbs ∣ p := ⟨x.natAbs, by rw [h']; ring⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1] at h'; exact hp.one_lt.ne' (by simpa using h')
  · rw [h1] at h'
    have := hp.two_le
    nlinarith
theorem not_form_eq_prime {t c : ℤ} (ht : t = 0 ∨ t = 1) {p : ℕ} (hp : p.Prime)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) (x y : ℤ)
    (h : x ^ 2 + t * x * y + c * y ^ 2 = p) : False := by
  have h4 := four_mul_form t c x y
  rw [h] at h4
  have hp0 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    exact not_prime_eq_sq hp x (by linarith)
  · have hy1 : 1 ≤ y ^ 2 := by
      have := Int.one_le_abs hy
      nlinarith [sq_abs y]
    have hd0 : 0 ≤ 4 * c - t ^ 2 := by linarith
    have hsq : (2 * x + t * y) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd0 (sub_nonneg.mpr hy1)]
    have hy2 : y ^ 2 = 1 := by
      have hdpos : 0 < 4 * c - t ^ 2 := by linarith
      have : (4 * c - t ^ 2) * (y ^ 2 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hdpos.ne'
      · linarith
    have hlin : 2 * x + t * y = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    have hy' : y = 1 ∨ y = -1 :=
      Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← sq]; exact hy2)
    rcases ht with rfl | rfl
    ·
      have hx : x = 0 := by linarith
      subst hx
      rw [hy2] at h
      apply hpc
      linarith
    ·
      rcases hy' with rfl | rfl <;> omega
end CN1.Finite
end

section
open NumberField Ideal Module Polynomial
namespace CN1.Finite
variable {K : Type*} [Field K] [NumberField K]
structure QuadInt (K : Type*) [Field K] [NumberField K] (t c : ℤ) where
  θ : 𝓞 K
  adjoin_eq_top : Algebra.adjoin ℤ {θ} = ⊤
  minpoly_eq : minpoly ℤ θ = X ^ 2 - C t * X + C c
  norm_eq : ∀ x y : ℤ, Algebra.norm ℤ ((x : 𝓞 K) + (y : 𝓞 K) * θ) = x ^ 2 + t * x * y + c * y ^ 2
theorem QuadInt.exists_eq_add_mul {t c : ℤ} (D : QuadInt K t c) (β : 𝓞 K) :
    ∃ x y : ℤ, β = (x : 𝓞 K) + (y : 𝓞 K) * D.θ := by
  have hβmem : β ∈ Algebra.adjoin ℤ {D.θ} := by rw [D.adjoin_eq_top]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβmem
  obtain ⟨f, hf⟩ := hβmem
  set g := minpoly ℤ D.θ with hg
  have hgm : g.Monic := minpoly.monic D.θ.isIntegral
  have h2 : g.natDegree = 2 := by rw [hg, D.minpoly_eq]; compute_degree!
  have hg1 : g ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hdeg : (f %ₘ g).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f hgm hg1
    omega
  obtain ⟨a, b, hr⟩ : ∃ a b : ℤ, f %ₘ g = C b * X + C a :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hdeg⟩
  refine ⟨a, b, ?_⟩
  change (aeval D.θ) f = β at hf
  have hg0 : aeval D.θ g = 0 := by rw [hg]; exact minpoly.aeval ℤ D.θ
  rw [← hf]
  conv_lhs => rw [← modByMonic_add_div f g]
  rw [map_add, map_mul, hg0, zero_mul, add_zero, hr]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  simp only [algebraMap_int_eq, eq_intCast]
  ring
theorem classNumber_ne_one_of_witness {t c : ℤ} (D : QuadInt K t c) (ht : t = 0 ∨ t = 1)
    (p : ℕ) (hp : p.Prime) (y : ℤ) (hy : (p : ℤ) ∣ y ^ 2 - t * y + c)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) : classNumber K ≠ 1 := by
  intro h1
  haveI := Fact.mk hp
  haveI hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top]
    exact hp.not_dvd_one
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  have hQ : (X - C y).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod D.θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff hmap0, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, D.minpoly_eq]
    have hy' : ((y ^ 2 - t * y + c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
    simp only [IsRoot.def, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C]
    simp only [eq_intCast]
    push_cast at hy'
    linear_combination hy'
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  haveI hPprime : P.IsPrime := hPmem.1
  haveI hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  have hPnorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]
  obtain ⟨β, hβ⟩ := Submodule.IsPrincipal.principal P
  rw [hβ, Ideal.submodule_span_eq, absNorm_span_singleton] at hPnorm
  obtain ⟨x, y', hxy⟩ := D.exists_eq_add_mul β
  rw [hxy, D.norm_eq] at hPnorm
  have hd0 : 0 ≤ 4 * c - t ^ 2 := by
    have : (0 : ℤ) ≤ p := by positivity
    linarith
  have hQnn := form_nonneg hd0 x y'
  have hform : x ^ 2 + t * x * y' + c * y' ^ 2 = p := by
    rcases Int.natAbs_eq_iff.mp hPnorm with h | h
    · exact h
    · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
      linarith
  exact not_form_eq_prime ht hp hb hpc x y' hform
def IsWitness (m p y : ℕ) : Prop :=
  p.Prime ∧ tOf m * y ≤ y ^ 2 + cOf m ∧ p ∣ y ^ 2 + cOf m - tOf m * y ∧ 4 * p ≤ dOf m ∧
    p ≠ cOf m
theorem classNumber_ne_one_of_isWitness {m p y : ℕ} (D : QuadInt K (tOf m) (cOf m))
    (hw : IsWitness m p y) : classNumber K ≠ 1 := by
  obtain ⟨hp, hle, hdvd, hb, hpc⟩ := hw
  have h4 : (4 * cOf m : ℤ) = dOf m + (tOf m : ℤ) ^ 2 := by exact_mod_cast four_mul_cOf m
  have hb' : (4 * p : ℤ) ≤ dOf m := by exact_mod_cast hb
  refine classNumber_ne_one_of_witness D ?_ p hp y ?_ (by linarith) (by exact_mod_cast hpc)
  · rcases tOf_eq_zero_or_one m with h | h <;> simp [h]
  · have := Int.natCast_dvd_natCast.mpr hdvd
    rw [Nat.cast_sub hle] at this
    push_cast at this
    convert this using 1
    ring
def SqfBelow (m : ℕ) : Prop := ∀ k ∈ Finset.Icc 2 26, ¬ k * k ∣ m
instance : DecidablePred SqfBelow := fun m =>
  inferInstanceAs (Decidable (∀ k ∈ Finset.Icc 2 26, ¬ k * k ∣ m))
theorem sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m) : SqfBelow m := by
  intro k hk h
  have := Nat.isUnit_iff.mp (hm k h)
  rw [Finset.mem_Icc] at hk
  omega
end CN1.Finite
end

section
open NumberField NumberField.InfinitePlace Ideal Module Real Nat
namespace CN1.Finite
variable {K : Type*} [Field K] [NumberField K]
theorem le_two_thirds_sqrt_of_le_minkowski (hK : finrank ℚ K = 2) {d : ℕ}
    (hdisc : |discr K| ≤ (d : ℤ)) {N : ℕ}
    (hle : (N : ℝ) ≤ (4 / π) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|)) :
    (N : ℝ) ≤ 2 / 3 * √(d : ℝ) := by
  have hr2 : nrComplexPlaces K ≤ 1 := by
    have := card_add_two_mul_card_eq_rank K
    omega
  have h1 : (1 : ℝ) ≤ 4 / π := by
    rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
  have hpi : (4 / π : ℝ) ≤ 4 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_gt_three.le
  have hpow : (4 / π : ℝ) ^ nrComplexPlaces K ≤ 4 / 3 :=
    (pow_le_pow_right₀ h1 hr2).trans (by rw [pow_one]; exact hpi)
  have hsqrt : √|(discr K : ℝ)| ≤ √(d : ℝ) := by
    apply Real.sqrt_le_sqrt
    rw [← Int.cast_abs]
    exact_mod_cast hdisc
  have hM : (4 / π : ℝ) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|) ≤ 2 / 3 * √(d : ℝ) := by
    rw [hK]
    have key := mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    norm_num [Nat.factorial]
    nlinarith [key]
  exact hle.trans hM
theorem nat_lt_of_le_two_thirds_sqrt {N d B : ℕ} (hN : (N : ℝ) ≤ 2 / 3 * √(d : ℝ))
    (hB : 4 * d < 9 * B ^ 2) : N < B := by
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hB
    · exact h
  have hB0' : (0 : ℝ) < 3 * B / 2 := by positivity
  have hs : √(d : ℝ) < 3 * B / 2 := by
    rw [Real.sqrt_lt' hB0']
    have : (4 * d : ℝ) < 9 * (B : ℝ) ^ 2 := by exact_mod_cast hB
    nlinarith
  have : (N : ℝ) < B := by nlinarith
  exact_mod_cast this
theorem absNorm_maximal_cases (hK : finrank ℚ K = 2) (P : Ideal (𝓞 K)) [hP : P.IsMaximal] :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P ∧
      (absNorm P = q ∨ (absNorm P = q ^ 2 ∧ P = span {(q : 𝓞 K)})) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 K ⧸ P)
  obtain ⟨n, hqprime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P) q
  have hN : absNorm P = q ^ (n : ℕ) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hqmem : (q : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  have hle : span {(q : 𝓞 K)} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmem)
  have hspan : absNorm (span {(q : 𝓞 K)}) = q ^ 2 := by
    rw [absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK, Int.natAbs_pow, Int.natAbs_natCast]
  have hdvd := absNorm_dvd_absNorm_of_le hle
  rw [hN, hspan, Nat.pow_dvd_pow_iff_le_right hqprime.one_lt] at hdvd
  refine ⟨q, hqprime, hqmem, ?_⟩
  rcases (show (n : ℕ) = 1 ∨ (n : ℕ) = 2 by have := n.pos; omega) with h | h
  · left; rw [hN, h, pow_one]
  · right
    refine ⟨by rw [hN, h], ?_⟩
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
    have hmul := congrArg absNorm hC
    rw [map_mul, hspan, hN, h] at hmul
    have hC1 : absNorm C = 1 := by
      have hq0 : 0 < q ^ 2 := pow_pos hqprime.pos 2
      have : q ^ 2 * absNorm C = q ^ 2 * 1 := by rw [mul_one]; exact hmul.symm
      exact Nat.eq_of_mul_eq_mul_left hq0 this
    rw [absNorm_eq_one_iff] at hC1
    rw [hC, hC1, mul_top]
theorem not_absNorm_eq_of_no_root (θ : 𝓞 K) (t c : ℤ)
    (hθ : θ ^ 2 = (t : 𝓞 K) * θ - (c : 𝓞 K))
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (q : ℕ) (hq : q.Prime) (hN : absNorm P = q)
    (hroot : ∀ z : ZMod q, z ^ 2 - (t : ZMod q) * z + (c : ZMod q) ≠ 0) : False := by
  haveI := Fact.mk hq
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = q := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← absNorm_apply, hN]
  haveI : CharP (𝓞 K ⧸ P) q := charP_of_card_eq_prime hcard
  let f : ZMod q →+* 𝓞 K ⧸ P := ZMod.castHom dvd_rfl _
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P θ)
  apply hroot z
  apply f.injective
  have hθ' := congrArg (Ideal.Quotient.mk P) hθ
  simp only [map_pow, map_sub, map_mul, map_intCast] at hθ'
  rw [map_add, map_sub, map_mul, map_pow, map_zero, hz, map_intCast, map_intCast, hθ']
  ring
theorem exists_theta {m : ℕ} (hm3 : m % 4 = 3) (α : K) (hα : α ^ 2 = -(m : K)) :
    ∃ θ : 𝓞 K, θ ^ 2 = ((tOf m : ℤ) : 𝓞 K) * θ - ((cOf m : ℤ) : 𝓞 K) := by
  have ht : tOf m = 1 := tOf_of_mod m hm3
  have hc : 4 * cOf m = m + 1 := four_mul_cOf_of_mod m hm3
  have hcK : (4 : K) * (cOf m : K) = (m : K) + 1 := by exact_mod_cast hc
  set ω : K := (1 + α) / 2 with hω
  have hω2 : ω ^ 2 = ω - (cOf m : K) := by
    have key : (4 : K) * ω ^ 2 = 4 * (ω - (cOf m : K)) := by
      simp only [hω]
      linear_combination hα + hcK
    exact mul_left_cancel₀ (by norm_num : (4 : K) ≠ 0) key
  have hint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (cOf m : ℤ), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    rw [hω2]; ring
  refine ⟨IsIntegralClosure.mk' (𝓞 K) ω hint, ?_⟩
  apply IsIntegralClosure.algebraMap_injective (𝓞 K) ℤ K
  simp only [map_pow, map_sub, map_mul, map_intCast, IsIntegralClosure.algebraMap_mk']
  rw [ht]
  push_cast
  rw [hω2]; ring
theorem classNumber_eq_one_of_mem_nine (hK : finrank ℚ K = 2) (m : ℕ)
    (hm : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ))
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hdisc : |discr K| ≤ (dOf m : ℤ)) :
    classNumber K = 1 := by
  obtain ⟨α, hα⟩ := hsq
  rw [classNumber_eq_one_iff]
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun I hI hle ↦ ?_
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  haveI hmax : (I : Ideal (𝓞 K)).IsMaximal := hI.isMaximal hI0
  have hbound := le_two_thirds_sqrt_of_le_minkowski hK hdisc hle
  obtain ⟨q, hq, -, hcase⟩ := absNorm_maximal_cases hK (I : Ideal (𝓞 K))
  rcases hcase with hN | ⟨-, hspan⟩
  · exfalso
    rw [hN] at hbound
    have h2 := hq.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 3) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 3) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 5) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 6) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 9) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
  · rw [hspan]
    exact ⟨⟨_, rfl⟩⟩
end CN1.Finite
end

section
namespace CN1.Finite
theorem w_5 : IsWitness 5 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_6 : IsWitness 6 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_10 : IsWitness 10 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_13 : IsWitness 13 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_14 : IsWitness 14 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_15 : IsWitness 15 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_17 : IsWitness 17 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_21 : IsWitness 21 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_22 : IsWitness 22 13 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_23 : IsWitness 23 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_26 : IsWitness 26 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_29 : IsWitness 29 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_30 : IsWitness 30 11 5 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_31 : IsWitness 31 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_33 : IsWitness 33 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_34 : IsWitness 34 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_35 : IsWitness 35 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_37 : IsWitness 37 19 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_38 : IsWitness 38 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_39 : IsWitness 39 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_41 : IsWitness 41 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_42 : IsWitness 42 13 6 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_46 : IsWitness 46 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_47 : IsWitness 47 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_51 : IsWitness 51 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_53 : IsWitness 53 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_55 : IsWitness 55 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_57 : IsWitness 57 11 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_58 : IsWitness 58 31 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_59 : IsWitness 59 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_61 : IsWitness 61 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_62 : IsWitness 62 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_65 : IsWitness 65 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_66 : IsWitness 66 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_69 : IsWitness 69 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_70 : IsWitness 70 17 7 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_71 : IsWitness 71 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_73 : IsWitness 73 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_74 : IsWitness 74 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_77 : IsWitness 77 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_78 : IsWitness 78 19 6 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_79 : IsWitness 79 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_82 : IsWitness 82 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_83 : IsWitness 83 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_85 : IsWitness 85 11 5 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_86 : IsWitness 86 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_87 : IsWitness 87 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_89 : IsWitness 89 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_91 : IsWitness 91 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_93 : IsWitness 93 17 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
def chunk1 : List ℕ := [5, 6, 10, 13, 14, 15, 17, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37, 38, 39, 41, 42, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 69, 70, 71, 73, 74, 77, 78, 79, 82, 83, 85, 86, 87, 89, 91, 93]
theorem exists_witness_chunk1 : ∀ m ∈ chunk1, ∃ p y : ℕ, IsWitness m p y := by
  intro m hm
  simp only [chunk1, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, _, w_5⟩, ⟨_, _, w_6⟩, ⟨_, _, w_10⟩, ⟨_, _, w_13⟩, ⟨_, _, w_14⟩, ⟨_, _, w_15⟩, ⟨_, _, w_17⟩, ⟨_, _, w_21⟩, ⟨_, _, w_22⟩, ⟨_, _, w_23⟩, ⟨_, _, w_26⟩, ⟨_, _, w_29⟩, ⟨_, _, w_30⟩, ⟨_, _, w_31⟩, ⟨_, _, w_33⟩, ⟨_, _, w_34⟩, ⟨_, _, w_35⟩, ⟨_, _, w_37⟩, ⟨_, _, w_38⟩, ⟨_, _, w_39⟩, ⟨_, _, w_41⟩, ⟨_, _, w_42⟩, ⟨_, _, w_46⟩, ⟨_, _, w_47⟩, ⟨_, _, w_51⟩, ⟨_, _, w_53⟩, ⟨_, _, w_55⟩, ⟨_, _, w_57⟩, ⟨_, _, w_58⟩, ⟨_, _, w_59⟩, ⟨_, _, w_61⟩, ⟨_, _, w_62⟩, ⟨_, _, w_65⟩, ⟨_, _, w_66⟩, ⟨_, _, w_69⟩, ⟨_, _, w_70⟩, ⟨_, _, w_71⟩, ⟨_, _, w_73⟩, ⟨_, _, w_74⟩, ⟨_, _, w_77⟩, ⟨_, _, w_78⟩, ⟨_, _, w_79⟩, ⟨_, _, w_82⟩, ⟨_, _, w_83⟩, ⟨_, _, w_85⟩, ⟨_, _, w_86⟩, ⟨_, _, w_87⟩, ⟨_, _, w_89⟩, ⟨_, _, w_91⟩, ⟨_, _, w_93⟩]
end CN1.Finite
end

section
namespace CN1.Finite
theorem w_94 : IsWitness 94 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_95 : IsWitness 95 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_97 : IsWitness 97 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_101 : IsWitness 101 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_102 : IsWitness 102 23 6 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_103 : IsWitness 103 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_105 : IsWitness 105 11 4 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_106 : IsWitness 106 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_107 : IsWitness 107 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_109 : IsWitness 109 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_110 : IsWitness 110 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_111 : IsWitness 111 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_113 : IsWitness 113 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_114 : IsWitness 114 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_115 : IsWitness 115 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_118 : IsWitness 118 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_119 : IsWitness 119 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_122 : IsWitness 122 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_123 : IsWitness 123 11 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_127 : IsWitness 127 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_129 : IsWitness 129 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_130 : IsWitness 130 23 10 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_131 : IsWitness 131 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_133 : IsWitness 133 13 6 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_134 : IsWitness 134 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_137 : IsWitness 137 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_138 : IsWitness 138 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_139 : IsWitness 139 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_141 : IsWitness 141 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_142 : IsWitness 142 11 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_143 : IsWitness 143 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_145 : IsWitness 145 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_146 : IsWitness 146 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_149 : IsWitness 149 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_151 : IsWitness 151 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_154 : IsWitness 154 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_155 : IsWitness 155 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_157 : IsWitness 157 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_158 : IsWitness 158 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_159 : IsWitness 159 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_161 : IsWitness 161 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_167 : IsWitness 167 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_179 : IsWitness 179 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_183 : IsWitness 183 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_187 : IsWitness 187 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_191 : IsWitness 191 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_195 : IsWitness 195 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_199 : IsWitness 199 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_203 : IsWitness 203 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_211 : IsWitness 211 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
def chunk2 : List ℕ := [94, 95, 97, 101, 102, 103, 105, 106, 107, 109, 110, 111, 113, 114, 115, 118, 119, 122, 123, 127, 129, 130, 131, 133, 134, 137, 138, 139, 141, 142, 143, 145, 146, 149, 151, 154, 155, 157, 158, 159, 161, 167, 179, 183, 187, 191, 195, 199, 203, 211]
theorem exists_witness_chunk2 : ∀ m ∈ chunk2, ∃ p y : ℕ, IsWitness m p y := by
  intro m hm
  simp only [chunk2, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, _, w_94⟩, ⟨_, _, w_95⟩, ⟨_, _, w_97⟩, ⟨_, _, w_101⟩, ⟨_, _, w_102⟩, ⟨_, _, w_103⟩, ⟨_, _, w_105⟩, ⟨_, _, w_106⟩, ⟨_, _, w_107⟩, ⟨_, _, w_109⟩, ⟨_, _, w_110⟩, ⟨_, _, w_111⟩, ⟨_, _, w_113⟩, ⟨_, _, w_114⟩, ⟨_, _, w_115⟩, ⟨_, _, w_118⟩, ⟨_, _, w_119⟩, ⟨_, _, w_122⟩, ⟨_, _, w_123⟩, ⟨_, _, w_127⟩, ⟨_, _, w_129⟩, ⟨_, _, w_130⟩, ⟨_, _, w_131⟩, ⟨_, _, w_133⟩, ⟨_, _, w_134⟩, ⟨_, _, w_137⟩, ⟨_, _, w_138⟩, ⟨_, _, w_139⟩, ⟨_, _, w_141⟩, ⟨_, _, w_142⟩, ⟨_, _, w_143⟩, ⟨_, _, w_145⟩, ⟨_, _, w_146⟩, ⟨_, _, w_149⟩, ⟨_, _, w_151⟩, ⟨_, _, w_154⟩, ⟨_, _, w_155⟩, ⟨_, _, w_157⟩, ⟨_, _, w_158⟩, ⟨_, _, w_159⟩, ⟨_, _, w_161⟩, ⟨_, _, w_167⟩, ⟨_, _, w_179⟩, ⟨_, _, w_183⟩, ⟨_, _, w_187⟩, ⟨_, _, w_191⟩, ⟨_, _, w_195⟩, ⟨_, _, w_199⟩, ⟨_, _, w_203⟩, ⟨_, _, w_211⟩]
end CN1.Finite
end

section
namespace CN1.Finite
theorem w_215 : IsWitness 215 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_219 : IsWitness 219 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_223 : IsWitness 223 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_227 : IsWitness 227 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_231 : IsWitness 231 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_235 : IsWitness 235 13 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_239 : IsWitness 239 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_247 : IsWitness 247 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_251 : IsWitness 251 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_255 : IsWitness 255 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_259 : IsWitness 259 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_263 : IsWitness 263 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_267 : IsWitness 267 23 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_271 : IsWitness 271 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_283 : IsWitness 283 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_287 : IsWitness 287 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_291 : IsWitness 291 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_295 : IsWitness 295 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_299 : IsWitness 299 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_303 : IsWitness 303 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_307 : IsWitness 307 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_311 : IsWitness 311 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_319 : IsWitness 319 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_323 : IsWitness 323 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_327 : IsWitness 327 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_331 : IsWitness 331 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_335 : IsWitness 335 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_339 : IsWitness 339 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_347 : IsWitness 347 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_355 : IsWitness 355 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_359 : IsWitness 359 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_367 : IsWitness 367 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_371 : IsWitness 371 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_379 : IsWitness 379 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_383 : IsWitness 383 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_391 : IsWitness 391 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_395 : IsWitness 395 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_399 : IsWitness 399 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_403 : IsWitness 403 11 5 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_407 : IsWitness 407 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_411 : IsWitness 411 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_415 : IsWitness 415 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_419 : IsWitness 419 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_427 : IsWitness 427 17 4 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_431 : IsWitness 431 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_435 : IsWitness 435 11 4 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_439 : IsWitness 439 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_443 : IsWitness 443 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_447 : IsWitness 447 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_451 : IsWitness 451 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
def chunk3 : List ℕ := [215, 219, 223, 227, 231, 235, 239, 247, 251, 255, 259, 263, 267, 271, 283, 287, 291, 295, 299, 303, 307, 311, 319, 323, 327, 331, 335, 339, 347, 355, 359, 367, 371, 379, 383, 391, 395, 399, 403, 407, 411, 415, 419, 427, 431, 435, 439, 443, 447, 451]
theorem exists_witness_chunk3 : ∀ m ∈ chunk3, ∃ p y : ℕ, IsWitness m p y := by
  intro m hm
  simp only [chunk3, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, _, w_215⟩, ⟨_, _, w_219⟩, ⟨_, _, w_223⟩, ⟨_, _, w_227⟩, ⟨_, _, w_231⟩, ⟨_, _, w_235⟩, ⟨_, _, w_239⟩, ⟨_, _, w_247⟩, ⟨_, _, w_251⟩, ⟨_, _, w_255⟩, ⟨_, _, w_259⟩, ⟨_, _, w_263⟩, ⟨_, _, w_267⟩, ⟨_, _, w_271⟩, ⟨_, _, w_283⟩, ⟨_, _, w_287⟩, ⟨_, _, w_291⟩, ⟨_, _, w_295⟩, ⟨_, _, w_299⟩, ⟨_, _, w_303⟩, ⟨_, _, w_307⟩, ⟨_, _, w_311⟩, ⟨_, _, w_319⟩, ⟨_, _, w_323⟩, ⟨_, _, w_327⟩, ⟨_, _, w_331⟩, ⟨_, _, w_335⟩, ⟨_, _, w_339⟩, ⟨_, _, w_347⟩, ⟨_, _, w_355⟩, ⟨_, _, w_359⟩, ⟨_, _, w_367⟩, ⟨_, _, w_371⟩, ⟨_, _, w_379⟩, ⟨_, _, w_383⟩, ⟨_, _, w_391⟩, ⟨_, _, w_395⟩, ⟨_, _, w_399⟩, ⟨_, _, w_403⟩, ⟨_, _, w_407⟩, ⟨_, _, w_411⟩, ⟨_, _, w_415⟩, ⟨_, _, w_419⟩, ⟨_, _, w_427⟩, ⟨_, _, w_431⟩, ⟨_, _, w_435⟩, ⟨_, _, w_439⟩, ⟨_, _, w_443⟩, ⟨_, _, w_447⟩, ⟨_, _, w_451⟩]
end CN1.Finite
end

section
namespace CN1.Finite
theorem w_455 : IsWitness 455 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_463 : IsWitness 463 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_467 : IsWitness 467 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_471 : IsWitness 471 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_479 : IsWitness 479 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_483 : IsWitness 483 11 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_487 : IsWitness 487 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_491 : IsWitness 491 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_499 : IsWitness 499 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_503 : IsWitness 503 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_511 : IsWitness 511 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_515 : IsWitness 515 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_519 : IsWitness 519 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_523 : IsWitness 523 7 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_527 : IsWitness 527 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_535 : IsWitness 535 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_543 : IsWitness 543 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_547 : IsWitness 547 11 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_551 : IsWitness 551 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_555 : IsWitness 555 13 6 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_559 : IsWitness 559 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_563 : IsWitness 563 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_571 : IsWitness 571 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_579 : IsWitness 579 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_583 : IsWitness 583 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_587 : IsWitness 587 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_591 : IsWitness 591 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_595 : IsWitness 595 13 5 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_599 : IsWitness 599 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_607 : IsWitness 607 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_611 : IsWitness 611 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_615 : IsWitness 615 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_619 : IsWitness 619 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_623 : IsWitness 623 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_627 : IsWitness 627 13 4 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_631 : IsWitness 631 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_635 : IsWitness 635 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_643 : IsWitness 643 7 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_647 : IsWitness 647 2 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
theorem w_651 : IsWitness 651 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
def chunk4 : List ℕ := [455, 463, 467, 471, 479, 483, 487, 491, 499, 503, 511, 515, 519, 523, 527, 535, 543, 547, 551, 555, 559, 563, 571, 579, 583, 587, 591, 595, 599, 607, 611, 615, 619, 623, 627, 631, 635, 643, 647, 651]
theorem exists_witness_chunk4 : ∀ m ∈ chunk4, ∃ p y : ℕ, IsWitness m p y := by
  intro m hm
  simp only [chunk4, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, _, w_455⟩, ⟨_, _, w_463⟩, ⟨_, _, w_467⟩, ⟨_, _, w_471⟩, ⟨_, _, w_479⟩, ⟨_, _, w_483⟩, ⟨_, _, w_487⟩, ⟨_, _, w_491⟩, ⟨_, _, w_499⟩, ⟨_, _, w_503⟩, ⟨_, _, w_511⟩, ⟨_, _, w_515⟩, ⟨_, _, w_519⟩, ⟨_, _, w_523⟩, ⟨_, _, w_527⟩, ⟨_, _, w_535⟩, ⟨_, _, w_543⟩, ⟨_, _, w_547⟩, ⟨_, _, w_551⟩, ⟨_, _, w_555⟩, ⟨_, _, w_559⟩, ⟨_, _, w_563⟩, ⟨_, _, w_571⟩, ⟨_, _, w_579⟩, ⟨_, _, w_583⟩, ⟨_, _, w_587⟩, ⟨_, _, w_591⟩, ⟨_, _, w_595⟩, ⟨_, _, w_599⟩, ⟨_, _, w_607⟩, ⟨_, _, w_611⟩, ⟨_, _, w_615⟩, ⟨_, _, w_619⟩, ⟨_, _, w_623⟩, ⟨_, _, w_627⟩, ⟨_, _, w_631⟩, ⟨_, _, w_635⟩, ⟨_, _, w_643⟩, ⟨_, _, w_647⟩, ⟨_, _, w_651⟩]
end CN1.Finite
end

section
open NumberField
namespace CN1.Finite
def nonHeegner190 : List ℕ := chunk1 ++ chunk2 ++ chunk3 ++ chunk4
theorem length_nonHeegner190 : nonHeegner190.length = 190 := by decide +kernel
theorem exists_witness_of_mem : ∀ m ∈ nonHeegner190, ∃ p y : ℕ, IsWitness m p y := by
  unfold nonHeegner190
  exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨exists_witness_chunk1, exists_witness_chunk2⟩, exists_witness_chunk3⟩, exists_witness_chunk4⟩
theorem mem_nonHeegner190 : ∀ m ∈ Finset.range 653, SqfBelow m → dOf m ≤ 652 →
    m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) → m ∈ nonHeegner190 := by
  decide +kernel
theorem classNumber_ne_one_of_quadInt {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (D : QuadInt K (tOf m) (cOf m)) (hm : Squarefree m) (hd : dOf m ≤ 652)
    (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : classNumber K ≠ 1 := by
  have hrange : m ∈ Finset.range 653 := Finset.mem_range.mpr (by have := le_dOf m; omega)
  obtain ⟨p, y, hw⟩ :=
    exists_witness_of_mem m (mem_nonHeegner190 m hrange (sqfBelow_of_squarefree hm) hd hnine)
  exact classNumber_ne_one_of_isWitness D hw
end CN1.Finite
end

section
open NumberField Module Polynomial CN1.Foundations
namespace CN1.Finite
variable {K : Type*} [Field K] [NumberField K]
theorem disc_eq_dOf (m : ℕ) : disc m = dOf m := rfl
theorem principalForm_eq (m : ℕ) (x y : ℤ) :
    principalForm m x y = x ^ 2 + (tOf m : ℤ) * x * y + (cOf m : ℤ) * y ^ 2 := by
  unfold principalForm tOf cOf
  split_ifs <;> push_cast <;> ring
theorem bInt_eq (m : ℕ) : bInt m = -(tOf m : ℤ) := by
  unfold bInt tOf; split_ifs <;> simp
theorem cInt_eq (m : ℕ) : cInt m = (cOf m : ℤ) := by
  unfold cInt cOf; split_ifs <;> simp
noncomputable def quadIntOfFoundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) {α : K}
    (hα : α ^ 2 = -(m : K)) : QuadInt K (tOf m) (cOf m) where
  θ := omegaInt hα
  adjoin_eq_top := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
    exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Algebra.self_mem_adjoin_singleton ℤ _))
  minpoly_eq := by
    rw [minpoly_int_omegaInt hα hm.ne_zero, bInt_eq, cInt_eq, map_neg, neg_mul, sub_eq_add_neg]
  norm_eq := fun x y => by
    rw [norm_int_eq_principalForm hα hK hm.ne_zero rfl, principalForm_eq]
theorem classNumber_ne_one_of_foundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : dOf m ≤ 652) (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) :
    classNumber K ≠ 1 := by
  obtain ⟨α, hα⟩ := hsq
  exact classNumber_ne_one_of_quadInt (quadIntOfFoundations hK hm hα) hm hd hnine
theorem classNumber_eq_one_of_foundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hnine : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : classNumber K = 1 := by
  obtain ⟨α, hα⟩ := hsq
  exact classNumber_eq_one_of_mem_nine hK m hnine ⟨α, hα⟩
    (by rw [discr_eq hα hK hm, abs_neg, Nat.abs_cast, disc_eq_dOf])
end CN1.Finite
end

section
open NumberField Module Polynomial Ideal CN1.Finite CN1.Foundations
namespace ELEM
theorem not_isInert_of_dvd {c p : ℕ} {y : ℤ} (hy : (p : ℤ) ∣ y ^ 2 - y + c) : ¬ IsInert c p := by
  intro h
  apply h (y : ZMod p)
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hy
  push_cast at this
  linear_combination this
theorem exists_dvd_of_not_isInert {c p : ℕ} (hp : p.Prime) (h : ¬ IsInert c p) :
    ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - y + c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  simp only [IsInert, not_forall, not_not] at h
  obtain ⟨r, hr⟩ := h
  refine ⟨(r.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination hr
theorem not_isInert_of_dvd_q {p q : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hq : q % 4 = 3)
    (hpq : p ∣ q) : ¬ IsInert (cq q) p := by
  set y : ℤ := (((p + 1) / 2 : ℕ) : ℤ) with hy
  have h2 : 2 * y = p + 1 := by
    have : 2 * ((p + 1) / 2) = p + 1 := by omega
    rw [hy]; exact_mod_cast this
  have h4 : 4 * (cq q : ℤ) = q + 1 := by
    have : 4 * cq q = q + 1 := by unfold cq; omega
    exact_mod_cast this
  have hid : 4 * (y ^ 2 - y + cq q) = (p : ℤ) ^ 2 + q := by
    linear_combination (2 * y + (p : ℤ) + 1) * h2 - 2 * h2 + h4
  have hdvd4 : (p : ℤ) ∣ 4 * (y ^ 2 - y + cq q) := by
    rw [hid]
    exact dvd_add (dvd_pow_self _ two_ne_zero) (Int.natCast_dvd_natCast.mpr hpq)
  have hcop : IsCoprime (p : ℤ) 4 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p 4 := by
      have h2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
      simpa using Nat.Coprime.pow_right 2 h2'
    simpa [Int.gcd] using this
  exact not_isInert_of_dvd (hcop.dvd_of_dvd_mul_left hdvd4)
variable {K : Type*} [Field K] [NumberField K]
theorem exists_form_eq_of_root {t c : ℤ} (D : QuadInt K t c) (hd0 : 0 ≤ 4 * c - t ^ 2)
    (p : ℕ) (hp : p.Prime) (y : ℤ) (hy : (p : ℤ) ∣ y ^ 2 - t * y + c) (h1 : classNumber K = 1) :
    ∃ x y' : ℤ, x ^ 2 + t * x * y' + c * y' ^ 2 = p := by
  have := Fact.mk hp
  have hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top]
    exact hp.not_dvd_one
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  have hQ : (X - C y).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod D.θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff hmap0, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, D.minpoly_eq]
    have hy' : ((y ^ 2 - t * y + c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
    simp only [IsRoot.def, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C]
    simp only [eq_intCast]
    push_cast at hy'
    linear_combination hy'
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  have hPprime : P.IsPrime := hPmem.1
  have hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  have hPnorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]
  obtain ⟨β, hβ⟩ := Submodule.IsPrincipal.principal P
  rw [hβ, Ideal.submodule_span_eq, absNorm_span_singleton] at hPnorm
  obtain ⟨x, y', hxy⟩ := D.exists_eq_add_mul β
  rw [hxy, D.norm_eq] at hPnorm
  have hQnn := form_nonneg hd0 x y'
  refine ⟨x, y', ?_⟩
  rcases Int.natAbs_eq_iff.mp hPnorm with h | h
  · exact h
  · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
    linarith
theorem isWitness_two_of_not_mod_four {m : ℕ} (h : m % 4 ≠ 3) (h3 : 3 ≤ m) :
    IsWitness m 2 (m % 2) := by
  simp only [IsWitness, tOf, cOf, dOf, h, ite_false, zero_mul, Nat.sub_zero]
  refine ⟨Nat.prime_two, Nat.zero_le _, ?_, by omega, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;> rw [h2] <;> omega
theorem isWitness_two_of_mod_eight {m : ℕ} (h : m % 8 = 7) (h15 : 15 ≤ m) : IsWitness m 2 0 := by
  have h4 : m % 4 = 3 := by omega
  simp only [IsWitness, tOf, cOf, dOf, h4, ite_true]
  refine ⟨Nat.prime_two, by simp, ?_, by omega, by omega⟩
  simp only [mul_zero, Nat.sub_zero]
  omega
theorem classNumber_ne_one_of_lt (hS : Sieve) (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hd : dOf m < 32768)
    (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : classNumber K ≠ 1 := by
  obtain ⟨α, hα⟩ := hsq
  have D := quadIntOfFoundations hK hm hα
  have hm0 : m ≠ 0 := hm.ne_zero
  have hm1 : m ≠ 1 := fun h => hnine (by simp [h])
  have hm2 : m ≠ 2 := fun h => hnine (by simp [h])
  have hm3 : m ≠ 3 := fun h => hnine (by simp [h])
  have hm7 : m ≠ 7 := fun h => hnine (by simp [h])
  by_cases h4 : m % 4 = 3
  · by_cases h8 : m % 8 = 7
    · exact classNumber_ne_one_of_isWitness D (isWitness_two_of_mod_eight h8 (by omega))
    ·
      have h83 : m % 8 = 3 := by omega
      have hdm : dOf m = m := dOf_of_mod m h4
      have hk : m / 8 < 4096 := by omega
      have hmk : 8 * (m / 8) + 3 = m := by omega
      rcases hS (m / 8) hk (by omega) with hmem | ⟨p, hpL, hp4, y, hyp, hroot⟩
      · exact absurd (by rw [hmk] at hmem; simp at hmem ⊢; omega) hnine
      · rw [hmk] at hp4 hroot
        have hp : p.Prime := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpL
          rcases hpL with h | h | h | h | h | h | h | h | h | h <;> subst h <;> norm_num
        have hp1 : 1 ≤ p := hp.one_lt.le
        have hyy : y ≤ y ^ 2 := by
          rcases Nat.eq_zero_or_pos y with h0 | h0
          · simp [h0]
          · calc y = y ^ 1 := (pow_one y).symm
              _ ≤ y ^ 2 := Nat.pow_le_pow_right h0 (by norm_num)
        have hpy : y ≤ p * y := Nat.le_mul_of_pos_left y hp1
        have hsub : (p - 1) * y = p * y - y := by rw [Nat.sub_one_mul]
        have hc : cOf m = (m + 1) / 4 := by simp [cOf, h4]
        have ht : tOf m = 1 := tOf_of_mod m h4
        refine classNumber_ne_one_of_isWitness D (p := p) (y := y) ⟨hp, ?_, ?_, ?_, ?_⟩
        · rw [ht, one_mul]; omega
        · rw [ht, one_mul, hc]
          have hdvd : p ∣ y ^ 2 + (p - 1) * y + (m + 1) / 4 := Nat.dvd_of_mod_eq_zero hroot
          have hdvd' := Nat.dvd_sub hdvd (Dvd.intro y rfl : p ∣ p * y)
          rw [hsub] at hdvd'
          generalize y ^ 2 = Y2 at hdvd' hyy ⊢
          generalize p * y = PY at hdvd' hpy ⊢
          have : Y2 + (PY - y) + (m + 1) / 4 - PY = Y2 + (m + 1) / 4 - y := by omega
          rwa [this] at hdvd'
        · rw [hdm]; omega
        · rw [hc]; omega
  · exact classNumber_ne_one_of_isWitness D (isWitness_two_of_not_mod_four h4 (by omega))
theorem analyticSetting_of_classNumber_eq_one (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hge : 32768 ≤ dOf m) (h1 : classNumber K = 1) :
    AnalyticSetting (dOf m) := by
  obtain ⟨α, hα⟩ := hsq
  have D := quadIntOfFoundations hK hm hα
  have h4 : m % 4 = 3 := by
    by_contra h4
    have : 3 ≤ m := by simp only [dOf, h4, ite_false] at hge; omega
    exact classNumber_ne_one_of_isWitness D (isWitness_two_of_not_mod_four h4 this) h1
  have hdm : dOf m = m := dOf_of_mod m h4
  rw [hdm] at hge ⊢
  have h8 : m % 8 = 3 := by
    by_contra h8
    exact classNumber_ne_one_of_isWitness D (isWitness_two_of_mod_eight (by omega) (by omega)) h1
  have ht : (tOf m : ℤ) = 1 := by rw [tOf_of_mod m h4]; rfl
  have hc : (cOf m : ℤ) = (cq m : ℤ) := by simp [cOf, cq, h4]
  have h4c : 4 * (cq m : ℤ) = m + 1 := by
    have : 4 * cq m = m + 1 := by unfold cq; omega
    exact_mod_cast this
  have hinert : ∀ p : ℕ, p.Prime → 4 * p < m → IsInert (cq m) p := by
    intro p hp hp4
    by_contra hni
    obtain ⟨y, hy⟩ := exists_dvd_of_not_isInert hp hni
    refine classNumber_ne_one_of_witness D (tOf_eq_zero_or_one m |>.imp
      (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h)) p hp y ?_ ?_ ?_ h1
    · rw [ht, hc]; simpa using hy
    · rw [ht, hc, h4c]; push_cast; omega
    · rw [hc]
      have : p < cq m := by unfold cq; omega
      exact_mod_cast this.ne
  refine ⟨hge, ?_, h8, hinert, ?_⟩
  ·
    by_contra hnp
    have hm1 : m ≠ 1 := by omega
    have hpp : (Nat.minFac m).Prime := Nat.minFac_prime hm1
    have hsq' : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have hp2 : Nat.minFac m % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · have : 2 ∣ m := h ▸ Nat.minFac_dvd m
        omega
      · exact h
    have hp4 : 4 * Nat.minFac m < m := by
      have := hpp.two_le
      nlinarith
    exact not_isInert_of_dvd_q hpp hp2 h4 (Nat.minFac_dvd m) (hinert _ hpp hp4)
  ·
    intro p hp hni
    obtain ⟨y, hy⟩ := exists_dvd_of_not_isInert hp hni
    have hd0 : 0 ≤ 4 * (cOf m : ℤ) - (tOf m : ℤ) ^ 2 := by rw [ht, hc, h4c]; push_cast; omega
    obtain ⟨x, y', hxy⟩ := exists_form_eq_of_root D hd0 p hp y (by rw [ht, hc]; simpa using hy) h1
    exact ⟨x, y', by rw [ht, hc] at hxy; linear_combination hxy⟩
theorem A_eq_decomp {q R : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (hqR : q ≤ R) :
    A R = Iinert q R + Splus q R + Real.log q / q := by
  classical
  have hq2 : q % 2 = 1 := by omega
  have hqni : ¬ IsInert (cq q) q := not_isInert_of_dvd_q hq hq2 hq4 dvd_rfl
  unfold A Iinert Splus
  rw [Nat.floor_natCast]
  set P := Nat.primesLE R
  set g : ℕ → ℝ := fun p => Real.log p / p
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => IsInert (cq q) p) g,
    ← Finset.sum_filter_add_sum_filter_not (P.filter fun p => ¬ IsInert (cq q) p) (fun p => p ≠ q) g]
  have hs : (P.filter fun p => ¬ IsInert (cq q) p).filter (fun p => p ≠ q) =
      P.filter (fun p => IsSplit q p) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, IsSplit, and_assoc]
  have hr : (P.filter fun p => ¬ IsInert (cq q) p).filter (fun p => ¬ p ≠ q) = {q} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton, ne_eq, not_not]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨⟨by simp [P, Nat.primesLE, Nat.primesBelow, hq]; omega, hqni⟩, rfl⟩
  rw [hs, hr, Finset.sum_singleton, add_assoc]
theorem Splus_nonneg (q : ℕ) (X : ℝ) : 0 ≤ Splus q X := by
  unfold Splus
  exact Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
theorem false_of_analyticSetting (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    {q : ℕ} (hset : AnalyticSetting q) : False := by
  obtain ⟨R, hRp, hRi, hR4, hR5⟩ := hL3 q hset
  obtain ⟨f, hf⟩ := hNV q R hset hRp hRi hR4 hR5
  have hY1 := h11 q R hset hRp hRi hR4 hR5 f hf
  have hY2 := h14 q R hset hRp hRi hR4 hR5 f hf
  have hq0 : 32768 ≤ q := hset.large
  have hqq4 : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
  have hRbig : 156 ≤ R := by omega
  have hqR : q ≤ R := by omega
  have hAR := hA R (by omega)
  have hSp := h8 q hset (R : ℝ) (by
    have : (q : ℝ) ≤ R := by exact_mod_cast hqR
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith)
  have hdec := A_eq_decomp hset.prime (by have := hset.mod_eight; omega) hqR
  have hS13 : (R : ℝ) / 13 ≤ (Sof R : ℝ) := by
    have : R ≤ 13 * Sof R := by unfold Sof; omega
    have : (R : ℝ) ≤ 13 * (Sof R : ℝ) := by exact_mod_cast this
    linarith
  have hS0 : (0 : ℝ) < (Sof R : ℝ) := by
    have : 0 < Sof R := by unfold Sof; omega
    exact_mod_cast this
  exact hE q R (Sof R) (A R) (Iinert q R) (Splus q R)
    (Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R))
    (by exact_mod_cast hq0) (by exact_mod_cast hR4) (by exact_mod_cast hR5) hS13 hS0
    (Splus_nonneg q R) hdec hAR.1 hAR.2 hSp hY1 hY2
theorem dOf_lt_of_classNumber_eq_one (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h1 : classNumber K = 1) : dOf m < 32768 := by
  by_contra hge
  exact false_of_analyticSetting hA h8 hL3 hNV h11 h14 hE
    (analyticSetting_of_classNumber_eq_one hK hm hsq (by omega) h1)
theorem classNumber_eq_one_iff_of_hyps (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    (hS : Sieve)
    (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) := by
  refine ⟨fun h1 => ?_, classNumber_eq_one_of_foundations hK hm hsq⟩
  by_contra hnine
  rcases lt_or_ge (dOf m) 32768 with hlt | hge
  · exact classNumber_ne_one_of_lt hS hK hm hsq hlt hnine h1
  · exact false_of_analyticSetting hA h8 hL3 hNV h11 h14 hE
      (analyticSetting_of_classNumber_eq_one hK hm hsq hge h1)
end ELEM
end

section
namespace ELEM.Primes
open Real
theorem log_four_eq : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
theorem log_four_lt_three_halves : log 4 < 3 / 2 := by
  rw [log_four_eq]
  linarith [log_two_lt_d9]
theorem log_three_lt : log 3 < 5 / 3 * log 2 := by
  have h : log ((3 : ℝ) ^ 3) < log ((2 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith
theorem log_five_lt : log 5 < 7 / 3 * log 2 := by
  have h : log ((5 : ℝ) ^ 3) < log ((2 : ℝ) ^ 7) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith
theorem three_halves_lt_log_seven : 3 / 2 < log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h3 : exp 3 < 49 := by
    have he : exp 3 = exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    have h1 := exp_one_lt_d9
    have h0 := (exp_pos 1).le
    calc exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by gcongr
      _ < 49 := by norm_num
  have hsq : exp (3 / 2) ^ 2 = exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [exp_pos (3 / 2)]
end ELEM.Primes
end

section
namespace ELEM.Primes
open Real Finset
theorem theta_lt_three_halves_mul {x : ℝ} (hx : 0 < x) : Chebyshev.theta x < 3 / 2 * x :=
  (Chebyshev.theta_le_log4_mul_x hx.le).trans_lt
    (mul_lt_mul_of_pos_right log_four_lt_three_halves hx)
theorem sum_log_le_theta {s : Finset ℕ} {n : ℕ} (hs : s ⊆ Nat.primesLE n) :
    ∑ p ∈ s, log (p : ℝ) ≤ Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  exact sum_le_sum_of_subset_of_nonneg hs fun p _ _ => log_natCast_nonneg p
theorem sum_log_lt_three_halves_mul {s : Finset ℕ} {n : ℕ} (hs : s ⊆ Nat.primesLE n)
    (hn : 0 < n) : ∑ p ∈ s, log (p : ℝ) < 3 / 2 * n :=
  (sum_log_le_theta hs).trans_lt (theta_lt_three_halves_mul (by exact_mod_cast hn))
end ELEM.Primes
end

section
namespace ELEM.Primes
open Real Finset
noncomputable def sumLogDivSqBound : ℝ :=
  log 2 / 4 + log 3 / 9 + log 5 / 25 + (log 5 + 1) / 10
theorem sumLogDivSqBound_lt : sumLogDivSqBound < 2 / 3 := by
  unfold sumLogDivSqBound
  linarith [log_three_lt, log_five_lt, log_two_lt_d9]
theorem two_mul_log_div_sq_le {n : ℝ} (hn : 7 ≤ n) :
    2 * (log n / n ^ 2) ≤ (log (n - 2) + 1) / (n - 2) - (log n + 1) / n := by
  have ha : 0 < n - 2 := by linarith
  have hn0 : 0 < n := by linarith
  have h1 : (n - 2) * log n - 2 ≤ (n - 2) * log (n - 2) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hn0 ha)
    rw [Real.log_div hn0.ne' ha.ne'] at h
    have h' : n / (n - 2) - 1 = 2 / (n - 2) := by field_simp; ring
    rw [h'] at h
    have h'' := mul_le_mul_of_nonneg_left h ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at h''
    nlinarith
  have hl : 3 / 2 ≤ log n :=
    (three_halves_lt_log_seven.trans_le (Real.log_le_log (by norm_num) hn)).le
  have h2 : n ≤ (n - 2) * log n := by nlinarith
  have key : (n - 2) * ((n - 2) * (2 * log n + (log n + 1) * n)) ≤
      (n - 2) * ((log (n - 2) + 1) * n ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg n)]
  have key' : (n - 2) * (2 * log n + (log n + 1) * n) ≤ (log (n - 2) + 1) * n ^ 2 :=
    le_of_mul_le_mul_left key ha
  have hq : (2 * log n + (log n + 1) * n) / n ^ 2 ≤ (log (n - 2) + 1) / (n - 2) := by
    rw [div_le_div_iff₀ (by positivity) ha]
    linarith
  have he : (2 * log n + (log n + 1) * n) / n ^ 2 = 2 * (log n / n ^ 2) + (log n + 1) / n := by
    field_simp
  linarith
theorem sum_odd_tail_le (K : ℕ) :
    ∑ k ∈ range K, log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2 ≤
      (log 5 + 1) / 10 := by
  set G : ℕ → ℝ := fun k => (log ((2 * k + 5 : ℕ) : ℝ) + 1) / ((2 * k + 5 : ℕ) : ℝ) with hG
  have hstep : ∀ k, 2 * (log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2) ≤
      G k - G (k + 1) := by
    intro k
    have h7 : (7 : ℝ) ≤ ((2 * k + 7 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
    have h := two_mul_log_div_sq_le h7
    have e1 : ((2 * k + 7 : ℕ) : ℝ) - 2 = ((2 * k + 5 : ℕ) : ℝ) := by push_cast; ring
    have e2 : ((2 * (k + 1) + 5 : ℕ) : ℝ) = ((2 * k + 7 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at h
    simp only [hG, e2]
    exact h
  have htel := Finset.sum_range_sub' G K
  have hGK : 0 ≤ G K := by
    simp only [hG]
    have : (1 : ℝ) ≤ ((2 * K + 5 : ℕ) : ℝ) := by push_cast; linarith [K.cast_nonneg (α := ℝ)]
    exact div_nonneg (by linarith [Real.log_nonneg this]) (by linarith)
  have hG0 : G 0 = (log 5 + 1) / 5 := by norm_num [hG]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ range K) => hstep k
  rw [← Finset.mul_sum, htel, hG0] at hsum
  linarith
theorem sum_log_div_sq_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, log (p : ℝ) / (p : ℝ) ^ 2 ≤ sumLogDivSqBound := by
  set f : ℕ → ℝ := fun p => log (p : ℝ) / (p : ℝ) ^ 2 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => div_nonneg (log_natCast_nonneg p) (sq_nonneg _)
  set K := s.sup id + 1
  set img := (range K).image (fun k => 2 * k + 7)
  have hsub : s ⊆ {2, 3, 5} ∪ img := by
    intro p hp
    have hpp := hs p hp
    have hle : p ≤ s.sup id := Finset.le_sup (f := id) hp
    rcases hpp.eq_two_or_odd' with h2 | hodd
    · simp [h2]
    · by_cases h35 : p = 3 ∨ p = 5
      · rcases h35 with h | h <;> simp [h]
      · have h7 : 7 ≤ p := by
          have h2le := hpp.two_le
          obtain ⟨j, hj⟩ := hodd
          push Not at h35
          have h4 : p ≠ 4 := by omega
          have h6 : p ≠ 6 := by omega
          omega
        apply Finset.mem_union_right
        simp only [img, Finset.mem_image, Finset.mem_range]
        obtain ⟨j, hj⟩ := hodd
        refine ⟨(p - 7) / 2, by omega, by omega⟩
  have hdisj : Disjoint ({2, 3, 5} : Finset ℕ) img := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [img, Finset.mem_image] at hb
    obtain ⟨k, _, rfl⟩ := hb
    simp at ha
  have hinj : Set.InjOn (fun k => 2 * k + 7) (range K : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  calc ∑ p ∈ s, f p ≤ ∑ p ∈ {2, 3, 5} ∪ img, f p :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf0 p
    _ = ∑ p ∈ ({2, 3, 5} : Finset ℕ), f p + ∑ p ∈ img, f p := sum_union hdisj
    _ = (log 2 / 4 + log 3 / 9 + log 5 / 25) +
          ∑ k ∈ range K, log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2 := by
        rw [sum_image hinj]
        simp only [hf]
        norm_num
        ring
    _ ≤ (log 2 / 4 + log 3 / 9 + log 5 / 25) + (log 5 + 1) / 10 := by
        linarith [sum_odd_tail_le K]
    _ = sumLogDivSqBound := by unfold sumLogDivSqBound; ring
theorem sum_log_div_sq_lt_two_thirds {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, log (p : ℝ) / (p : ℝ) ^ 2 < 2 / 3 :=
  (sum_log_div_sq_le hs).trans_lt sumLogDivSqBound_lt
theorem summable_log_div_sq :
    Summable fun p : Nat.Primes => log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
  refine summable_of_sum_le (c := sumLogDivSqBound)
    (fun p => div_nonneg (log_natCast_nonneg _) (sq_nonneg _)) fun u => ?_
  have h := sum_log_div_sq_le (s := u.map (Function.Embedding.subtype _))
    (by intro p hp; obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp; exact q.2)
  exact (Finset.sum_map u (Function.Embedding.subtype _)
    fun p : ℕ => log (p : ℝ) / (p : ℝ) ^ 2).symm.trans_le h
theorem tsum_log_div_sq_lt_two_thirds :
    ∑' p : Nat.Primes, log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 2 / 3 := by
  refine lt_of_le_of_lt ?_ sumLogDivSqBound_lt
  refine tsum_le_of_sum_le' ?_ fun u => ?_
  · unfold sumLogDivSqBound
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    have h5 := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    positivity
  · have h := sum_log_div_sq_le (s := u.map (Function.Embedding.subtype _))
      (by intro p hp; obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp; exact q.2)
    exact (Finset.sum_map u (Function.Embedding.subtype _)
    fun p : ℕ => log (p : ℝ) / (p : ℝ) ^ 2).symm.trans_le h
end ELEM.Primes
end

section
namespace ELEM.Primes
open Nat hiding log
open Real Finset
theorem log_factorial_eq_sum (m : ℕ) :
    log ((m ! : ℕ) : ℝ) = ∑ p ∈ primesLE m, ((m !).factorization p : ℝ) * log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  refine Finsupp.sum_of_support_subset _ ?_ _ (fun p _ => by simp)
  intro p hp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  exact mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp.1).mp hp.2.1, hp.1⟩
theorem factorization_factorial_mul_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (p - 1) * (m !).factorization p ≤ m := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial]
  exact Nat.sub_le _ _
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m / p ≤ (m !).factorization p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hb : Nat.log p m < m + 1 := Nat.lt_succ_of_lt (Nat.log_lt_self p hm.ne')
  rw [Nat.factorization_factorial hp hb]
  have h1 : 1 ∈ Ico 1 (m + 1) := by simp; omega
  have := Finset.single_le_sum (f := fun i => m / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this
theorem factorization_factorial_mul_log_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((m !).factorization p : ℝ) * log (p : ℝ) ≤
      m * (log (p : ℝ) / p) + 2 * m * (log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hl : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hv : ((p : ℝ) - 1) * ((m !).factorization p : ℝ) ≤ m := by
    have := (Nat.cast_le (α := ℝ)).mpr (factorization_factorial_mul_le hp m)
    rwa [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at this
  have hdiv : ((m !).factorization p : ℝ) ≤ m / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ hp1]; linarith
  have hfrac : (m : ℝ) / ((p : ℝ) - 1) ≤ m / p + 2 * m / (p : ℝ) ^ 2 := by
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hp0 : (0 : ℝ) < p := by linarith
    rw [div_add_div _ _ hp0.ne' (by positivity), div_le_div_iff₀ hp1 (by positivity)]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hp2), mul_nonneg (mul_nonneg hm hp0.le)
      (sub_nonneg.mpr hp2)]
  calc ((m !).factorization p : ℝ) * log (p : ℝ) ≤ (m / p + 2 * m / (p : ℝ) ^ 2) * log p :=
        mul_le_mul_of_nonneg_right (hdiv.trans hfrac) hl
    _ = m * (log (p : ℝ) / p) + 2 * m * (log (p : ℝ) / (p : ℝ) ^ 2) := by ring
theorem mul_log_div_sub_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m * (log (p : ℝ) / p) - log (p : ℝ) ≤ ((m !).factorization p : ℝ) * log (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hfl : (m : ℝ) / p - 1 ≤ ((m / p : ℕ) : ℝ) := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have hv : (m : ℝ) / p - 1 ≤ ((m !).factorization p : ℝ) :=
    hfl.trans (by exact_mod_cast div_le_factorization_factorial hp m)
  calc m * (log (p : ℝ) / p) - log (p : ℝ) = ((m : ℝ) / p - 1) * log p := by ring
    _ ≤ ((m !).factorization p : ℝ) * log (p : ℝ) := mul_le_mul_of_nonneg_right hv hl
theorem mul_log_sub_le_log_factorial (m : ℕ) :
    (m : ℝ) * log m - m ≤ log ((m ! : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hf0 : (0 : ℝ) < (m ! : ℕ) := by exact_mod_cast m.factorial_pos
  have h := Real.pow_div_factorial_le_exp (m : ℝ) hm0.le m
  have h' := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div (by positivity) hf0.ne', Real.log_pow] at h'
  linarith
theorem log_factorial_le_mul_log (m : ℕ) : log ((m ! : ℕ) : ℝ) ≤ m * log m := by
  have hf0 : (0 : ℝ) < (m ! : ℕ) := by exact_mod_cast m.factorial_pos
  have h : ((m ! : ℕ) : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have := Real.log_le_log hf0 h
  rwa [Real.log_pow] at this
theorem log_sub_lt_sum_log_div {m : ℕ} (hm : 1 ≤ m) :
    log (m : ℝ) - 7 / 3 < ∑ p ∈ primesLE m, log (p : ℝ) / p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB := sum_log_div_sq_lt_two_thirds (s := primesLE m) fun p hp => prime_of_mem_primesLE hp
  have hsum : log ((m ! : ℕ) : ℝ) ≤
      m * ∑ p ∈ primesLE m, log (p : ℝ) / p +
        2 * m * ∑ p ∈ primesLE m, log (p : ℝ) / (p : ℝ) ^ 2 := by
    rw [log_factorial_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p hp =>
      factorization_factorial_mul_log_le (prime_of_mem_primesLE hp) m
  have hlow := mul_log_sub_le_log_factorial m
  have : (m : ℝ) * (log m - 7 / 3) < m * ∑ p ∈ primesLE m, log (p : ℝ) / p := by
    nlinarith
  exact lt_of_mul_lt_mul_left this hm0.le
theorem sum_log_div_lt_log_add {m : ℕ} (hm : 1 ≤ m) :
    ∑ p ∈ primesLE m, log (p : ℝ) / p < log (m : ℝ) + 3 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ := sum_log_lt_three_halves_mul (s := primesLE m) (n := m) (subset_refl _) hm
  have hsum : m * ∑ p ∈ primesLE m, log (p : ℝ) / p - ∑ p ∈ primesLE m, log (p : ℝ) ≤
      log ((m ! : ℕ) : ℝ) := by
    rw [log_factorial_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun p hp => mul_log_div_sub_le (prime_of_mem_primesLE hp) m
  have hup := log_factorial_le_mul_log m
  have : (m : ℝ) * ∑ p ∈ primesLE m, log (p : ℝ) / p < m * (log m + 3 / 2) := by
    nlinarith
  exact lt_of_mul_lt_mul_left this hm0.le
theorem sum_Ioc_eq_sub {m n : ℕ} (hmn : m ≤ n) :
    ∑ p ∈ (Ioc m n).filter Nat.Prime, log (p : ℝ) / p =
      ∑ p ∈ primesLE n, log (p : ℝ) / p - ∑ p ∈ primesLE m, log (p : ℝ) / p := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not (primesLE n) (fun p => m < p)]
  congr 2
  · ext p
    by_cases hp : p.Prime <;> simp only [mem_filter, mem_Ioc, mem_primesLE, hp, and_true,
      and_false, false_and]
    omega
  · ext p
    by_cases hp : p.Prime <;> simp only [mem_filter, mem_primesLE, not_lt, hp, and_true,
      and_false, false_and]
    omega
theorem log_sub_log_sub_lt_sum_Ioc {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    log (n : ℝ) - log (m : ℝ) - 23 / 6 < ∑ p ∈ (Ioc m n).filter Nat.Prime, log (p : ℝ) / p := by
  rw [sum_Ioc_eq_sub hmn]
  linarith [log_sub_lt_sum_log_div (hm.trans hmn), sum_log_div_lt_log_add hm]
theorem sum_log_div_lt_log_add_of_subset {s : Finset ℕ} {n : ℕ} (hs : s ⊆ primesLE n)
    (hn : 1 ≤ n) : ∑ p ∈ s, log (p : ℝ) / p < log (n : ℝ) + 3 / 2 :=
  (sum_le_sum_of_subset_of_nonneg hs fun p _ _ =>
    div_nonneg (log_natCast_nonneg p) p.cast_nonneg).trans_lt (sum_log_div_lt_log_add hn)
end ELEM.Primes
end

section
namespace ELEM.Primes
theorem lemmaTwoTheta : ELEM.LemmaTwoTheta := fun _ hx =>
  theta_lt_three_halves_mul (by linarith)
theorem lemmaTwoA : ELEM.LemmaTwoA := fun _ hm =>
  ⟨log_sub_lt_sum_log_div (by omega), sum_log_div_lt_log_add (by omega)⟩
theorem lemmaTwoB : ELEM.LemmaTwoB :=
  ⟨summable_log_div_sq, tsum_log_div_sq_lt_two_thirds⟩
end ELEM.Primes
end

section
namespace ELEM.Count
open Real Finset
theorem integral_sqrt_one_sub_sq_zero_one : ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) = π / 4 := by
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a := (-1 : ℝ)) (b := 0) (c := 1) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hneg : ∫ x in (-1 : ℝ)..0, √(1 - x ^ 2) = ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun x : ℝ => √(1 - x ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  rw [integral_sqrt_one_sub_sq, hneg] at hsplit
  linarith
theorem integral_sqrt_sub_mul_sq {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∫ s in (0 : ℝ)..√(A / κ), √(A - κ * s ^ 2) = π * A / (4 * √κ) := by
  rcases hA.eq_or_lt with rfl | hA'
  · simp
  set β := √(A / κ) with hβ
  have hβpos : 0 < β := Real.sqrt_pos.mpr (div_pos hA' hκ)
  have hβsq : β ^ 2 = A / κ := Real.sq_sqrt (div_pos hA' hκ).le
  have key := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun s : ℝ => √(A - κ * s ^ 2)) β
  simp only [mul_zero, mul_one, smul_eq_mul] at key
  rw [← key]
  have hpt : ∀ x : ℝ, √(A - κ * (β * x) ^ 2) = √A * √(1 - x ^ 2) := by
    intro x
    rw [← Real.sqrt_mul hA]
    congr 1
    have : κ * (β * x) ^ 2 = A * x ^ 2 := by
      rw [mul_pow, hβsq]; field_simp
    rw [this]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq_zero_one, hβ,
    Real.sqrt_div hA]
  have hsA : √A * √A = A := Real.mul_self_sqrt hA
  have hsk : 0 < √κ := Real.sqrt_pos.mpr hκ
  calc √A / √κ * (√A * (π / 4)) = π * (√A * √A) / (4 * √κ) := by ring
    _ = π * A / (4 * √κ) := by rw [hsA]
variable {q : ℕ}
theorem four_mul_cq (hq : AnalyticSetting q) : 4 * (cq q : ℤ) = q + 1 := by
  have h := hq.mod_eight
  have : 4 * ((q + 1) / 4) = q + 1 := by omega
  unfold cq
  exact_mod_cast this
theorem four_mul_norm (hq : AnalyticSetting q) (a b : ℤ) :
    4 * (a ^ 2 + a * b + (cq q : ℤ) * b ^ 2) = (2 * a + b) ^ 2 + q * b ^ 2 := by
  linear_combination b ^ 2 * four_mul_cq hq
theorem exists_rep_pos (hq : AnalyticSetting q) {p : ℕ} (hp : p.Prime) (hs : IsSplit q p) :
    ∃ a b : ℤ, 1 ≤ b ∧ a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := hq.rep p hp hs.1
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · exact ⟨-a, -b, by omega, by rw [← hab]; ring⟩
  · exfalso
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : (p : ℤ) = a * a := by rw [← hab]; ring
    rcases hpi.irreducible.isUnit_or_isUnit h1 with hu | hu <;>
    · rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
      · have : (p : ℤ) = 1 := by rw [h1]; norm_num
        exact hp.one_lt.ne' (by exact_mod_cast this)
  · exact ⟨a, b, hb, hab⟩
theorem two_mul_add_ne_zero (hq : AnalyticSetting q) {p : ℕ} (hp : p.Prime) (hs : IsSplit q p)
    {a b : ℤ} (hab : a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p) : 2 * a + b ≠ 0 := by
  intro h0
  have hb : b = -2 * a := by omega
  have h4 := four_mul_cq hq
  have hpq : (p : ℤ) = q * a ^ 2 := by
    subst hb; linear_combination -hab + a ^ 2 * h4
  have hdvd : q ∣ p := by
    have : (q : ℤ) ∣ p := ⟨a ^ 2, hpq⟩
    exact_mod_cast this
  exact hs.2 ((Nat.prime_dvd_prime_iff_eq hq.prime hp).mp hdvd).symm
noncomputable def rowW (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := √(4 * t - q * ((i : ℝ) + 1) ^ 2)
noncomputable def rowLo (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := (-((i : ℝ) + 1) - rowW q t i) / 2
noncomputable def rowHi (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := (-((i : ℝ) + 1) + rowW q t i) / 2
noncomputable def box (q : ℕ) (t : ℝ) : Finset (Σ _ : ℕ, ℤ) :=
  (range ⌊√(4 * t / q)⌋₊).sigma fun i => Icc ⌈rowLo q t i⌉ ⌊rowHi q t i⌋
def normAt (q : ℕ) (x : Σ _ : ℕ, ℤ) : ℤ :=
  x.2 ^ 2 + x.2 * ((x.1 : ℤ) + 1) + (cq q : ℤ) * ((x.1 : ℤ) + 1) ^ 2
theorem card_Icc_ceil_floor_le {lo hi : ℝ} (h : lo ≤ hi) :
    ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) ≤ hi - lo + 1 := by
  by_cases hle : ⌈lo⌉ ≤ ⌊hi⌋ + 1
  · have hc := Int.card_Icc_of_le _ _ hle
    have h1 : ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) = ((⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) : ℝ) := by
      rw [← hc]; norm_cast
    rw [h1]; push_cast
    linarith [Int.floor_le hi, Int.le_ceil lo]
  · have : (Icc ⌈lo⌉ ⌊hi⌋).card = 0 := by
      rw [Int.card_Icc]; omega
    rw [this]; push_cast; linarith
theorem card_box_le (q : ℕ) (t : ℝ) :
    ((box q t).card : ℝ) ≤ ∑ i ∈ range ⌊√(4 * t / q)⌋₊, (rowW q t i + 1) := by
  rw [box, card_sigma]; push_cast
  refine sum_le_sum fun i _ => ?_
  have hw : 0 ≤ rowW q t i := Real.sqrt_nonneg _
  have := card_Icc_ceil_floor_le (lo := rowLo q t i) (hi := rowHi q t i)
    (by unfold rowLo rowHi; linarith)
  unfold rowLo rowHi at this ⊢
  linarith
theorem sum_rowW_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    ∑ i ∈ range ⌊√(4 * t / q)⌋₊, (rowW q t i + 1) ≤ π * t / √q + 2 * √t / √q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  set β := √(4 * t / q) with hβ
  set n := ⌊β⌋₊
  have hnβ : (n : ℝ) ≤ β := Nat.floor_le (Real.sqrt_nonneg _)
  set g : ℝ → ℝ := fun s => √(4 * t - q * s ^ 2) with hg
  have hgc : Continuous g := by fun_prop
  have hanti : AntitoneOn g (Set.Icc 0 (0 + n)) := by
    intro x hx y hy hxy
    simp only [hg]
    apply Real.sqrt_le_sqrt
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    nlinarith
  have hsum := hanti.sum_le_integral
  simp only [zero_add] at hsum
  have hrow : ∑ i ∈ range n, rowW q t i = ∑ i ∈ range n, g (↑(i + 1)) := by
    refine sum_congr rfl fun i _ => ?_
    simp [rowW, hg]
  have hint : ∫ x in (0 : ℝ)..n, g x ≤ ∫ x in (0 : ℝ)..β, g x := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (a := 0) (b := (n : ℝ)) (c := β) (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    have hnn : 0 ≤ ∫ x in (n : ℝ)..β, g x :=
      intervalIntegral.integral_nonneg hnβ fun x _ => Real.sqrt_nonneg _
    linarith
  have harea : ∫ x in (0 : ℝ)..β, g x = π * (4 * t) / (4 * √q) :=
    integral_sqrt_sub_mul_sq (by linarith) hq0
  have hβ' : β = 2 * √t / √q := by
    rw [hβ, Real.sqrt_div (by linarith), Real.sqrt_mul (by norm_num)]
    congr 2
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [sum_add_distrib, hrow]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have : π * (4 * t) / (4 * √q) = π * t / √q := by field_simp
  linarith
open scoped Classical in
theorem card_split_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    (((Icc 0 ⌊t⌋₊).filter fun k => k.Prime ∧ IsSplit q k).card : ℝ) ≤
      π * t / (2 * √q) + √t / √q := by
  set P := (Icc 0 ⌊t⌋₊).filter fun k => k.Prime ∧ IsSplit q k
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  have hfib : ∀ p ∈ P, 2 ≤ ((box q t).filter fun x => normAt q x = p).card := by
    intro p hpP
    obtain ⟨hpI, hp, hs⟩ := by simpa [P] using hpP
    obtain ⟨a, b, hb, hab⟩ := exists_rep_pos hq hp hs
    have hne := two_mul_add_ne_zero hq hp hs hab
    have h4 := four_mul_norm hq a b
    rw [hab] at h4
    have hpt : (p : ℝ) ≤ t := (Nat.cast_le.mpr hpI).trans (Nat.floor_le ht)
    have h4r : 4 * (p : ℝ) = (2 * (a : ℝ) + b) ^ 2 + q * (b : ℝ) ^ 2 := by exact_mod_cast h4
    set i := (b - 1).toNat with hi
    have hib : ((i : ℤ) + 1) = b := by rw [hi, Int.toNat_of_nonneg (by omega)]; ring
    have hibr : ((i : ℝ) + 1) = b := by exact_mod_cast hib
    have hrow : i ∈ range ⌊√(4 * t / q)⌋₊ := by
      rw [mem_range, Nat.lt_iff_add_one_le]
      apply Nat.le_floor
      push_cast
      rw [hibr]
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hq0]
      nlinarith [sq_nonneg (2 * (a : ℝ) + b)]
    have hcol : ∀ a' : ℤ, (2 * (a' : ℝ) + b) ^ 2 ≤ 4 * t - q * (b : ℝ) ^ 2 →
        a' ∈ Icc ⌈rowLo q t i⌉ ⌊rowHi q t i⌋ := by
      intro a' ha'
      have habs := Real.abs_le_sqrt ha'
      rw [abs_le] at habs
      rw [mem_Icc, Int.ceil_le, Int.le_floor]
      unfold rowLo rowHi rowW
      rw [hibr]
      constructor <;> linarith
    have hm1 : (⟨i, a⟩ : Σ _ : ℕ, ℤ) ∈ (box q t).filter fun x => normAt q x = p := by
      rw [mem_filter, box, mem_sigma]
      refine ⟨⟨hrow, hcol a (by linarith)⟩, ?_⟩
      simp only [normAt, hib]; exact hab
    have hm2 : (⟨i, -a - b⟩ : Σ _ : ℕ, ℤ) ∈ (box q t).filter fun x => normAt q x = p := by
      rw [mem_filter, box, mem_sigma]
      refine ⟨⟨hrow, hcol (-a - b) (by push_cast; nlinarith)⟩, ?_⟩
      simp only [normAt, hib]; rw [← hab]; ring
    have h12 : (⟨i, a⟩ : Σ _ : ℕ, ℤ) ≠ ⟨i, -a - b⟩ := by
      intro h
      have : a = -a - b := by simpa using h
      exact hne (by omega)
    exact one_lt_card.mpr ⟨_, hm1, _, hm2, h12⟩
  have hdisj : (P : Set ℕ).PairwiseDisjoint fun p => (box q t).filter fun x => normAt q x = p := by
    intro p _ p' _ hpp'
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro x _ h1 h2
    exact hpp' (by rw [h1] at h2; exact_mod_cast h2)
  have hsub : (P.biUnion fun p => (box q t).filter fun x => normAt q x = p) ⊆ box q t :=
    biUnion_subset.mpr fun p _ => filter_subset _ _
  have h2P : 2 * P.card ≤ (box q t).card := by
    calc 2 * P.card = ∑ p ∈ P, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ P, ((box q t).filter fun x => normAt q x = p).card := sum_le_sum hfib
      _ = (P.biUnion fun p => (box q t).filter fun x => normAt q x = p).card :=
          (card_biUnion hdisj).symm
      _ ≤ (box q t).card := card_le_card hsub
  have h2P' : 2 * (P.card : ℝ) ≤ (box q t).card := by exact_mod_cast h2P
  have := (card_box_le q t).trans (sum_rowW_le hq ht)
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have e : π * t / (2 * √q) + √t / √q = (π * t / √q + 2 * √t / √q) / 2 := by field_simp
  rw [e]
  linarith
end ELEM.Count
end

section
namespace ELEM.Count
open Real Finset MeasureTheory
variable {q : ℕ}
open scoped Classical in
noncomputable def splitInd (q : ℕ) (k : ℕ) : ℝ := if k.Prime ∧ IsSplit q k then 1 else 0
noncomputable def countBound (q : ℕ) (t : ℝ) : ℝ := π * t / (2 * √q) + √t / √q
noncomputable def antiderivH (q : ℕ) (t : ℝ) : ℝ :=
  π / (2 * √q) * (log t - log t ^ 2 / 2) + 2 * (log t + 1) / (√q * √t)
theorem sum_splitInd_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k ≤ countBound q t := by
  classical
  have h := card_split_le hq ht
  unfold splitInd countBound
  rw [sum_boole]
  convert h
theorem sum_splitInd_nonneg (q : ℕ) (t : ℝ) : 0 ≤ ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k :=
  sum_nonneg fun k _ => by unfold splitInd; split_ifs <;> norm_num
theorem hasDerivAt_log_div {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => log x / x) ((1 - log t) / t ^ 2) t := by
  have := (Real.hasDerivAt_log ht.ne').div (hasDerivAt_id' t) ht.ne'
  convert this using 1 <;> try rfl
  field_simp
theorem hasDerivAt_antiderivH (hq0 : (0 : ℝ) < q) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (antiderivH q) ((1 - log t) / t ^ 2 * countBound q t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hst : 0 < √t := Real.sqrt_pos.mpr ht
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have h1 := ((hl.sub ((hl.pow 2).div_const 2)).const_mul (π / (2 * √(q : ℝ))))
  have h2 := ((hl.add_const 1).const_mul 2).div (hs.const_mul (√(q : ℝ)))
    (mul_ne_zero hsq.ne' hst.ne')
  have := h1.add h2
  unfold antiderivH
  convert this using 1 <;> try rfl
  unfold countBound
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 := ⟨√t, hst, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  generalize log (s ^ 2) = L
  field_simp
  ring
theorem boundary_identity (hq0 : (0 : ℝ) < q) {t : ℝ} (ht : 0 < t) :
    log t / t * countBound q t - antiderivH q t =
      π / (4 * √q) * log t ^ 2 - (log t + 2) / (√q * √t) := by
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  unfold countBound antiderivH
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨√t, Real.sqrt_pos.mpr ht, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  generalize log (s ^ 2) = L
  field_simp
  ring
open scoped Classical in
theorem split_weight_le (hq : AnalyticSetting q) {a b : ℝ} (ha : exp 1 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun k => k.Prime ∧ IsSplit q k), log (p : ℝ) / p ≤
      π / (4 * √q) * (log b ^ 2 - log a ^ 2 + 2 * log a) + 2 * (log a + 1) / (√q * √a) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have ha0 : 0 < a := (exp_pos 1).trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hloga : 1 ≤ log a := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) ha
  set f : ℝ → ℝ := fun x => log x / x with hf
  have hderiv : ∀ t, 0 < t → deriv f t = (1 - log t) / t ^ 2 :=
    fun t ht => (hasDerivAt_log_div ht).deriv
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_log_div (hpos t ht)).differentiableAt
  have hcont : ContinuousOn (fun t => (1 - log t) / t ^ 2) (Set.Icc a b) := by
    refine ContinuousOn.div (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht => ?_))
      (continuousOn_pow 2) fun t ht => (pow_pos (hpos t ht) 2).ne'
    exact (hpos t ht).ne'
  have hf_int : IntegrableOn (deriv f) (Set.Icc a b) :=
    (hcont.integrableOn_Icc).congr_fun (fun t ht => (hderiv t (hpos t ht)).symm) measurableSet_Icc
  have abel := sum_mul_eq_sub_sub_integral_mul (splitInd q) ha0.le hab hf_diff hf_int
  have hlhs : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun k => k.Prime ∧ IsSplit q k), log (p : ℝ) / p =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * splitInd q k := by
    rw [sum_filter]
    refine sum_congr rfl fun k _ => ?_
    simp only [hf, splitInd]
    split_ifs <;> simp
  rw [hlhs, abel]
  set N : ℝ → ℝ := fun t => ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k with hN
  have hGc : ContinuousOn (countBound q) (Set.Icc a b) := by
    unfold countBound; fun_prop
  have hint_G : IntegrableOn (fun t => deriv f t * countBound q t) (Set.Icc a b) :=
    hf_int.mul_continuousOn hGc isCompact_Icc
  have hint_N : IntegrableOn (fun t => deriv f t * N t) (Set.Icc a b) :=
    integrableOn_mul_sum_Icc (splitInd q) ha0.le hf_int
  have hmono : ∫ t in Set.Ioc a b, deriv f t * countBound q t ≤
      ∫ t in Set.Ioc a b, deriv f t * N t := by
    refine setIntegral_mono_on (hint_G.mono_set Set.Ioc_subset_Icc_self)
      (hint_N.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ha0.trans ht.1
    have hd : deriv f t ≤ 0 := by
      rw [hderiv t ht0]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
      have : log a ≤ log t := log_le_log ha0 ht.1.le
      linarith
    exact mul_le_mul_of_nonpos_left (sum_splitInd_le hq ht0.le) hd
  have hftc : ∫ t in Set.Ioc a b, deriv f t * countBound q t = antiderivH q b - antiderivH q a := by
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      rw [hderiv t (hpos t ht)]
      exact hasDerivAt_antiderivH hq0 (hpos t ht)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint_G
  have hfb : 0 ≤ f b := div_nonneg (log_nonneg (by linarith [one_le_exp (zero_le_one' ℝ)])) hb0.le
  have hfa : 0 ≤ f a := div_nonneg (by linarith) ha0.le
  have hNb : f b * N b ≤ f b * countBound q b :=
    mul_le_mul_of_nonneg_left (sum_splitInd_le hq hb0.le) hfb
  have hNa : 0 ≤ f a * N a := mul_nonneg hfa (sum_splitInd_nonneg q a)
  have hid := boundary_identity hq0 hb0
  have hHa : antiderivH q a =
      π / (4 * √q) * (2 * log a - log a ^ 2) + 2 * (log a + 1) / (√q * √a) := by
    unfold antiderivH; ring
  have hdrop : 0 ≤ (log b + 2) / (√q * √b) := by
    have : 0 ≤ log b := log_nonneg (by linarith [one_le_exp (zero_le_one' ℝ)])
    positivity
  simp only [hf] at hid hNb hNa ⊢
  have : π / (4 * √q) * (log b ^ 2 - log a ^ 2 + 2 * log a) =
      π / (4 * √q) * log b ^ 2 + π / (4 * √q) * (2 * log a - log a ^ 2) := by ring
  linarith
end ELEM.Count
end

section
namespace ELEM.Count
open Real Finset
variable {q : ℕ}
theorem exp_one_lt_three : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
theorem pi_lt_sixteen_fifths : π < 16 / 5 := lt_trans pi_lt_d2 (by norm_num)
theorem two_lt_log_eight : 2 < log 8 := by
  rw [lt_log_iff_exp_lt (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
  have := exp_one_lt_d9
  have h0 := exp_pos 1
  nlinarith
open scoped Classical in
theorem splus_eq_sum_Ioc (hq : AnalyticSetting q) (X : ℝ) :
    Splus q X = ∑ p ∈ (Ioc ⌊(q : ℝ) / 4⌋₊ ⌊X⌋₊).filter (fun k => k.Prime ∧ IsSplit q k),
      log (p : ℝ) / p := by
  unfold Splus
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  have hfl : ⌊(q : ℝ) / 4⌋₊ = q / 4 := by
    exact_mod_cast Nat.floor_div_eq_div (K := ℝ) q 4
  simp only [mem_filter, Nat.mem_primesLE, mem_Ioc, hfl]
  constructor
  · rintro ⟨⟨hpX, hp⟩, hs⟩
    refine ⟨⟨?_, hpX⟩, hp, hs⟩
    have h4 : ¬ 4 * p < q := fun h => hs.1 (hq.inert_of_lt p hp h)
    have h8 := hq.mod_eight
    have : 4 * p ≠ q := by omega
    omega
  · rintro ⟨⟨_, hpX⟩, hp, hs⟩
    exact ⟨⟨hpX, hp⟩, hs⟩
theorem splitBound : ELEM.SplitBound := by
  intro q hq X hX
  have hq32 : (32768 : ℝ) ≤ q := by exact_mod_cast hq.large
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  set a : ℝ := (q : ℝ) / 4 with ha_def
  have ha8 : 8 ≤ a := by rw [ha_def]; linarith
  have ha : exp 1 ≤ a := by linarith [exp_one_lt_three]
  have h7 := split_weight_le hq ha hX
  rw [← splus_eq_sum_Ioc hq X] at h7
  have hloga : 2 ≤ log a := (two_lt_log_eight.trans_le (log_le_log (by norm_num) ha8)).le
  have hlogaq : log a ≤ log q := log_le_log (by linarith) (by rw [ha_def]; linarith)
  have hsqa : √(q : ℝ) * √a = q / 2 := by
    rw [ha_def, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_div_assoc, Real.mul_self_sqrt hq0.le]
  rw [hsqa] at h7
  have hX2 : 0 ≤ log X ^ 2 := sq_nonneg _
  have hfirst : π / (4 * √q) * (log X ^ 2 - log a ^ 2 + 2 * log a) ≤ 4 / (5 * √q) * log X ^ 2 := by
    have hneg : log X ^ 2 - log a ^ 2 + 2 * log a ≤ log X ^ 2 := by nlinarith
    have hπ := pi_lt_sixteen_fifths
    have hc : π / (4 * √q) ≤ 4 / (5 * √q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc π / (4 * √q) * (log X ^ 2 - log a ^ 2 + 2 * log a)
        ≤ π / (4 * √q) * log X ^ 2 :=
          mul_le_mul_of_nonneg_left hneg (div_nonneg pi_pos.le (by positivity))
      _ ≤ 4 / (5 * √q) * log X ^ 2 := mul_le_mul_of_nonneg_right hc hX2
  have hsecond : 2 * (log a + 1) / ((q : ℝ) / 2) ≤ 4 * (log q + 1) / q := by
    rw [div_le_div_iff₀ (by positivity) hq0]
    nlinarith
  linarith
end ELEM.Count
end

section
namespace ELEM.Count
open Real Finset
variable {q : ℕ}
theorem log_div_sqrt_le {x₀ x : ℝ} (hx₀ : 0 < x₀) (h2 : 2 ≤ log x₀) (hx : x₀ ≤ x) :
    log x / √x ≤ log x₀ / √x₀ := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have hr : 0 < x / x₀ := div_pos hx0 hx₀
  set s := √(x / x₀) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact (one_le_div hx₀).mpr hx
  have hsx : √x = √x₀ * s := by
    rw [hs, ← Real.sqrt_mul hx₀.le, mul_div_cancel₀ _ hx₀.ne']
  have hlog : log x = log x₀ + 2 * log s := by
    have : x = x₀ * s ^ 2 := by rw [hs, Real.sq_sqrt hr.le]; field_simp
    rw [this, log_mul hx₀.ne' (pow_pos hs0 2).ne', log_pow]; push_cast; ring
  have hls : log s ≤ s - 1 := log_le_sub_one_of_pos hs0
  have hsq0 : 0 < √x₀ := Real.sqrt_pos.mpr hx₀
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) hsq0, hsx, hlog]
  have : log x₀ + 2 * log s ≤ s * log x₀ := by nlinarith
  nlinarith
theorem log_q0 : log (32768 : ℝ) = 15 * log 2 := by
  rw [show (32768 : ℝ) = 2 ^ 15 by norm_num, log_pow]; norm_num
theorem log_q0_bounds : 207 / 20 < log (32768 : ℝ) ∧ log (32768 : ℝ) < 21 / 2 := by
  rw [log_q0]
  constructor
  · linarith [log_two_gt_d9]
  · linarith [log_two_lt_d9]
theorem sqrt_q0_gt : 180 < √(32768 : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num
theorem log_div_sqrt_lt (hq : (32768 : ℝ) ≤ q) : log q / √q < 7 / 120 := by
  obtain ⟨hl, hu⟩ := log_q0_bounds
  have h := log_div_sqrt_le (by norm_num) (by linarith) hq
  refine h.trans_lt ?_
  have hs := sqrt_q0_gt
  rw [div_lt_iff₀ (by linarith)]
  linarith
theorem auxPrime : ELEM.AuxPrime := by
  classical
  intro q hq
  by_contra hno
  push Not at hno
  have hq32 : (32768 : ℝ) ≤ q := by exact_mod_cast hq.large
  have hq1 : 1 ≤ q := hq.prime.one_lt.le
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  set L := log (q : ℝ) with hL
  have hset : (Ioc (q ^ 4) (q ^ 5)).filter Nat.Prime =
      (Ioc ⌊((q ^ 4 : ℕ) : ℝ)⌋₊ ⌊((q ^ 5 : ℕ) : ℝ)⌋₊).filter (fun k => k.Prime ∧ IsSplit q k) := by
    rw [Nat.floor_natCast, Nat.floor_natCast]
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h4, h5⟩, hp⟩
      refine ⟨⟨h4, h5⟩, hp, fun hin => ?_, ?_⟩
      · exact absurd (hno p hp hin h4) (not_lt.mpr h5)
      · rintro rfl
        have : p ≤ p ^ 4 := Nat.le_self_pow (by norm_num) p
        omega
    · rintro ⟨h, hp, _⟩
      exact ⟨h, hp⟩
  have hlow := ELEM.Primes.log_sub_log_sub_lt_sum_Ioc (m := q ^ 4) (n := q ^ 5)
    (Nat.one_le_pow _ _ (by omega)) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have ha : exp 1 ≤ ((q ^ 4 : ℕ) : ℝ) := by
    push_cast
    have : (q : ℝ) ≤ (q : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    linarith [exp_one_lt_three]
  have hab : ((q ^ 4 : ℕ) : ℝ) ≤ ((q ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by norm_num)
  have hup := split_weight_le hq ha hab
  rw [← hset] at hup
  have h4 : log ((q ^ 4 : ℕ) : ℝ) = 4 * L := by push_cast; rw [log_pow]; norm_num [hL]
  have h5 : log ((q ^ 5 : ℕ) : ℝ) = 5 * L := by push_cast; rw [log_pow]; norm_num [hL]
  have hs4 : √((q ^ 4 : ℕ) : ℝ) = (q : ℝ) ^ 2 := by
    push_cast
    rw [show (q : ℝ) ^ 4 = ((q : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [h4, h5, hs4] at hup
  rw [h4, h5] at hlow
  obtain ⟨hl0, _⟩ := log_q0_bounds
  have hLq : 207 / 20 < L := hl0.trans_le (log_le_log (by norm_num) hq32)
  have hr : L ≤ 7 / 120 * √q := by
    have := log_div_sqrt_lt hq32
    rw [div_lt_iff₀ hsq] at this
    linarith
  have hu : 180 ≤ √(q : ℝ) := sqrt_q0_gt.le.trans (Real.sqrt_le_sqrt hq32)
  have hπ := pi_lt_sixteen_fifths
  have hT1 : π / (4 * √q) * ((5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L)) ≤ 41 / 90 * L := by
    have hpos : 0 ≤ (5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L) := by nlinarith
    calc π / (4 * √q) * ((5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L))
        = π * (9 * L ^ 2 + 8 * L) / (4 * √q) := by ring
      _ ≤ 41 / 90 * L := by
          rw [div_le_iff₀ (by positivity)]
          have h9 : 9 * L ^ 2 + 8 * L ≤ (21 / 40 + 2 / 45) * L * √q := by nlinarith
          have hp0 : 0 ≤ 9 * L ^ 2 + 8 * L := by nlinarith
          have : π * (9 * L ^ 2 + 8 * L) ≤ 16 / 5 * (9 * L ^ 2 + 8 * L) :=
            mul_le_mul_of_nonneg_right hπ.le hp0
          nlinarith
  have hT2 : 2 * (4 * L + 1) / (√q * (q : ℝ) ^ 2) ≤ L / 1000 := by
    have hq2 : (32768 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hK : 10000 ≤ √q * (q : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith
end ELEM.Count
end

section

end

section
open QuadraticAlgebra Polynomial
namespace ELEM
variable {c p : ℕ}
def redHom (c p : ℕ) : OK c →+* Fp2 c p where
  toFun z := ⟨(z.re : ZMod p), (z.im : ZMod p)⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp
theorem redHom_re (z : OK c) : (redHom c p z).re = (z.re : ZMod p) := rfl
theorem redHom_im (z : OK c) : (redHom c p z).im = (z.im : ZMod p) := rfl
theorem redHom_star (z : OK c) : redHom c p (star z) = star (redHom c p z) := by
  ext <;> simp [redHom_re, redHom_im]
theorem natCast_dvd_of_redHom_eq_zero {w : OK c} (h : redHom c p w = 0) : (p : OK c) ∣ w := by
  have hre : (w.re : ZMod p) = 0 := by simpa [redHom_re, redHom_im] using congrArg QuadraticAlgebra.re h
  have him : (w.im : ZMod p) = 0 := by simpa [redHom_re, redHom_im] using congrArg QuadraticAlgebra.im h
  rw [show (p : OK c) = algebraMap ℤ (OK c) (p : ℤ) by simp, algebraMap_dvd_iff]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hre,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him⟩
section field
variable [hp : Fact p.Prime] [hi : Fact (IsInert c p)]
instance : CharP (Fp2 c p) p := charP_of_injective_algebraMap algebraMap_injective p
theorem star_omega_eq : star (ω : Fp2 c p) = 1 - ω := by
  ext <;> simp
theorem omega_sq_eq : (ω : Fp2 c p) ^ 2 = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + ω := by
  ext <;> simp [pow_two]
theorem omega_pow_ne_omega : (ω : Fp2 c p) ^ p ≠ ω := by
  intro h
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set F := Fp2 c p
  set ι := algebraMap (ZMod p) F
  have hP : (X ^ p - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hp.out.one_lt
  have hnot : (ω : F) ∉ Finset.univ.image ι := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x hx
    have := congrArg QuadraticAlgebra.im hx
    rw [show (ι x).im = 0 from rfl, omega_im] at this
    exact zero_ne_one this
  set Z : Finset F := insert ω (Finset.univ.image ι)
  have hcard : Z.card = p + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ algebraMap_injective,
      Finset.card_univ, ZMod.card]
  have hsub : Z.val ⊆ (X ^ p - X : F[X]).roots := by
    intro z hz
    rw [mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← map_pow, ZMod.pow_card]
  have := card_le_degree_of_subset_roots hsub
  rw [hcard, FiniteField.X_pow_card_sub_X_natDegree_eq F hp.out.one_lt] at this
  omega
theorem omega_pow_eq_star : (ω : Fp2 c p) ^ p = star ω := by
  set u := (ω : Fp2 c p) ^ p with hu
  have hu2 : u ^ 2 = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + u := by
    calc u ^ 2 = ((ω : Fp2 c p) ^ 2) ^ p := by rw [hu, ← pow_mul, ← pow_mul, mul_comm]
      _ = (algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + ω) ^ p := by rw [omega_sq_eq]
      _ = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) ^ p + (ω : Fp2 c p) ^ p :=
          add_pow_char _ _ _
      _ = _ := by rw [← map_pow, ZMod.pow_card]
  have hprod : (u - ω) * (u - star ω) = 0 := by
    rw [star_omega_eq]
    linear_combination hu2 - omega_sq_eq (c := c) (p := p)
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) omega_pow_ne_omega
  · exact sub_eq_zero.mp h
theorem pow_char_eq_star (w : Fp2 c p) : w ^ p = star w := by
  have hw : w = algebraMap (ZMod p) (Fp2 c p) w.re + algebraMap (ZMod p) (Fp2 c p) w.im * ω := by
    ext <;> simp
  rw [hw, add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card,
    omega_pow_eq_star]
  ext <;> simp
end field
theorem frobenius_dvd (hp : p.Prime) (hi : IsInert c p) (z : OK c) :
    (p : OK c) ∣ z ^ p - star z := by
  have := Fact.mk hp
  have := Fact.mk hi
  apply natCast_dvd_of_redHom_eq_zero
  rw [map_sub, map_pow, redHom_star, pow_char_eq_star, sub_self]
end ELEM
end

section
namespace ELEM
open Matrix Module
theorem exists_det_submatrix_ne_zero {K : Type*} [Field K] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] (A : Matrix m n K) (hA : LinearIndependent K A.row) :
    ∃ f : m → n, Function.Injective f ∧ (A.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card m = Fintype.card κ := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan,
      ← rank_eq_finrank_span_cols, hA.rank_matrix]
  let e : m ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hcol : (A.submatrix id (a ∘ e)).col = A.col ∘ a ∘ e := by
    ext j i; rfl
  have hli' : LinearIndependent K (A.submatrix id (a ∘ e)).col := by
    rw [hcol]; exact hli.comp e e.injective
  exact ((isUnit_iff_isUnit_det _).mp (linearIndependent_cols_iff_isUnit.mp hli')).ne_zero
theorem det_submatrix_ne_zero_of_map {S F : Type*} [CommRing S] [CommRing F] (φ : S →+* F)
    {m n : Type*} [Fintype m] [DecidableEq m] (A : Matrix m n S) (f : m → n)
    (h : ((A.map φ).submatrix id f).det ≠ 0) : (A.submatrix id f).det ≠ 0 := by
  intro h0
  apply h
  rw [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
theorem exists_det_submatrix_ne_zero_of_map {S F : Type*} [CommRing S] [Field F] (φ : S →+* F)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n S)
    (hA : LinearIndependent F (A.map φ).row) :
    ∃ f : m → n, Function.Injective f ∧ (A.submatrix id f).det ≠ 0 := by
  obtain ⟨f, hf, hdet⟩ := exists_det_submatrix_ne_zero (A.map φ) hA
  exact ⟨f, hf, det_submatrix_ne_zero_of_map φ A f hdet⟩
end ELEM
end

section
namespace ELEM
open Polynomial
theorem le_rootMultiplicity_of_iterate_derivative {K : Type*} [Field K] {G : K[X]}
    (hG : G ≠ 0) {t : K} {J : ℕ} (hJ : ∀ m, m < J → m ≠ 0 → (m : K) ≠ 0)
    (hvan : ∀ k < J, (derivative^[k] G).eval t = 0) : J ≤ G.rootMultiplicity t := by
  rcases J with _ | n
  · exact Nat.zero_le _
  · refine Nat.succ_le_of_lt
      (lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hG
        (fun m hm => hvan m (Nat.lt_succ_of_le hm)) ?_)
    intro m hm hm0
    exact mem_nonZeroDivisors_of_ne_zero (hJ m (Nat.lt_succ_of_le hm) hm0)
theorem card_mul_le_natDegree_of_iterate_derivative {K : Type*} [Field K] {G : K[X]}
    (hG : G ≠ 0) (Z : Finset K) {J : ℕ} (hJ : ∀ m, m < J → m ≠ 0 → (m : K) ≠ 0)
    (hvan : ∀ z ∈ Z, ∀ k < J, (derivative^[k] G).eval z = 0) :
    Z.card * J ≤ G.natDegree := by
  classical
  have hle : J • Z.val ≤ G.roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, count_roots]
    by_cases ha : a ∈ Z
    · rw [Multiset.count_eq_one_of_mem Z.nodup ha, mul_one]
      exact le_rootMultiplicity_of_iterate_derivative hG hJ (hvan a ha)
    · rw [Multiset.count_eq_zero_of_notMem ha, mul_zero]
      exact Nat.zero_le _
  calc Z.card * J = Multiset.card (J • Z.val) := by
        rw [Multiset.card_nsmul, mul_comm]; rfl
    _ ≤ Multiset.card G.roots := Multiset.card_le_card hle
    _ ≤ G.natDegree := card_roots' G
theorem eq_zero_of_iterate_derivative_charP {K : Type*} [Field K] (p : ℕ) [CharP K p]
    {G : K[X]} (Z : Finset K) {J : ℕ} (hJp : J ≤ p) (hdeg : G.natDegree < Z.card * J)
    (hvan : ∀ z ∈ Z, ∀ k < J, (derivative^[k] G).eval z = 0) : G = 0 := by
  by_contra hG
  refine absurd (card_mul_le_natDegree_of_iterate_derivative hG Z ?_ hvan) (not_le.mpr hdeg)
  intro m hm hm0 h
  rw [CharP.cast_eq_zero_iff K p] at h
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h
  omega
theorem descFactorial_add_mul_cast {K : Type*} [CommRing K] (R : ℕ) [CharP K R]
    (r s k : ℕ) : (((r + R * s).descFactorial k : ℕ) : K) = ((r.descFactorial k : ℕ) : K) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, ih]
    by_cases hk : k ≤ r
    · rw [show r + R * s - k = (r - k) + R * s by omega, Nat.cast_add, Nat.cast_mul,
        CharP.cast_eq_zero K R, zero_mul, add_zero]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, mul_zero, mul_zero]
theorem eval_iterate_derivative_X_pow_add_mul {K : Type*} [CommRing K] (R : ℕ) [CharP K R]
    (r s k : ℕ) (x : K) :
    (derivative^[k] (X ^ (r + R * s) : K[X])).eval x
      = ((r.descFactorial k : ℕ) : K) * x ^ (r - k) * (x ^ R) ^ s := by
  rw [iterate_derivative_X_pow_eq_natCast_mul, eval_mul, eval_natCast, eval_pow, eval_X,
    descFactorial_add_mul_cast R]
  by_cases hk : k ≤ r
  · rw [show r + R * s - k = (r - k) + R * s by omega, pow_add, pow_mul, mul_assoc]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp
def derivMatrix {K : Type*} [CommRing K] {ι : Type*} (R S J : ℕ) (x w : ι → K) :
    Matrix (Fin R × Fin S) (ι × Fin J) K :=
  fun p c => (((p.1 : ℕ).descFactorial c.2 : ℕ) : K) * x c.1 ^ ((p.1 : ℕ) - c.2)
    * w c.1 ^ (p.2 : ℕ)
theorem add_mul_injective {R S : ℕ} {p q : Fin R × Fin S}
    (h : (p.1 : ℕ) + R * p.2 = q.1 + R * q.2) : p = q := by
  have hR : 0 < R := p.1.pos
  have h1 : (p.1 : ℕ) = q.1 := by
    have := congrArg (· % R) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt q.1.isLt]
      using this
  have h2 : (p.2 : ℕ) = q.2 := by
    have := congrArg (· / R) h
    simpa [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt p.1.isLt, Nat.div_eq_of_lt q.1.isLt]
      using this
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)
theorem derivMatrix_rows_linearIndependent {K : Type*} [Field K] (R : ℕ) [CharP K R]
    {S J : ℕ} {ι : Type*} [Fintype ι] (hJR : J ≤ R) (hRS : R * S ≤ Fintype.card ι * J)
    (x : ι → K) (hx : Function.Injective x) :
    LinearIndependent K (derivMatrix R S J x (fun i => x i ^ R)).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hRS0 : 0 < R * S := Nat.mul_pos p.1.pos p.2.pos
  let G : K[X] := ∑ q : Fin R × Fin S, C (g q) * X ^ ((q.1 : ℕ) + R * q.2)
  have hval : ∀ i : ι, ∀ k : Fin J, (derivative^[k] G).eval (x i) = 0 := by
    intro i k
    have h1 := congrFun hg (i, k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← h1, iterate_derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [iterate_derivative_C_mul, eval_mul, eval_C, eval_iterate_derivative_X_pow_add_mul R]
    simp only [Matrix.row, derivMatrix, mul_assoc]
  have hdeg : G.natDegree < (Finset.univ.image x).card * J := by
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := R * S - 1) ?_)
      (by omega)
    intro q _
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have hq1 := q.1.isLt
    have hq2 := q.2.isLt
    have : R * (q.2 : ℕ) + R ≤ R * S := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq2
    omega
  have hG : G = 0 := by
    refine eq_zero_of_iterate_derivative_charP R _ hJR hdeg ?_
    intro z hz k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hval i ⟨k, hk⟩
  have hcoeff := congrArg (fun P : K[X] => P.coeff ((p.1 : ℕ) + R * p.2)) hG
  simp only [G, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
  rw [Finset.sum_eq_single p] at hcoeff
  · simpa using hcoeff
  · intro q _ hqp
    split_ifs with h
    · exact absurd (add_mul_injective h).symm hqp
    · exact mul_zero _
  · intro hp; exact absurd (Finset.mem_univ p) hp
end ELEM
end

section
open QuadraticAlgebra
namespace ELEM
theorem Jof_le {R : ℕ} (hR : 1 ≤ R) : Jof R ≤ R := by
  unfold Jof; omega
theorem le_A0_mul_B0 {q : ℕ} (R : ℕ) (hq : 0 < q) : R ≤ A0 q R * B0 q R := by
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have key : (R : ℝ) ≤ (A0 q R : ℝ) * B0 q R := by
    calc (R : ℝ) = √((R : ℝ) * √q) * √((R : ℝ) / √q) := by
          rw [← Real.sqrt_mul (by positivity),
            show (R : ℝ) * √q * (R / √q) = R * R by field_simp, Real.sqrt_mul_self hR0]
      _ ≤ A0 q R * B0 q R :=
          mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast key
theorem four_mul_le_card_node {q : ℕ} (R : ℕ) (hq : 0 < q) :
    4 * R ≤ Fintype.card (Node q R) := by
  have h := le_A0_mul_B0 R hq
  simp only [Node, Fintype.card_prod, Fintype.card_fin]
  nlinarith
theorem R_mul_Sof_le {q : ℕ} (R : ℕ) (hq : 0 < q) :
    R * Sof R ≤ Fintype.card (Node q R) * Jof R := by
  have hn := four_mul_le_card_node R hq
  have h12 : 12 * Sof R ≤ R := by unfold Sof; omega
  have h48 : R ≤ 48 * Jof R := by unfold Jof; omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 48 by norm_num)
  calc 48 * (R * Sof R) = 4 * R * (12 * Sof R) := by ring
    _ ≤ 4 * R * R := Nat.mul_le_mul_left _ h12
    _ ≤ Fintype.card (Node q R) * (48 * Jof R) := Nat.mul_le_mul hn h48
    _ = 48 * (Fintype.card (Node q R) * Jof R) := by ring
theorem two_ceil_sqrt_add_one_le {x : ℝ} {R : ℕ} (hx : 16 * x ≤ (R : ℝ) ^ 2)
    (hR : 6 ≤ R) : 2 * ⌈√x⌉₊ + 1 ≤ R := by
  have hR6 : (6 : ℝ) ≤ R := by exact_mod_cast hR
  have hs : √x ≤ (R : ℝ) / 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : ((R : ℝ) / 4) ^ 2 = (R : ℝ) ^ 2 / 16 := by ring
    rw [this]; linarith
  have hc : (⌈√x⌉₊ : ℝ) < √x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have : ((2 * ⌈√x⌉₊ + 1 : ℕ) : ℝ) < R := by push_cast; linarith
  exact (by exact_mod_cast this : 2 * ⌈√x⌉₊ + 1 < R).le
theorem sixteen_mul_lt {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 16 * q < R ∧ 16 ≤ R := by
  have h9 : 9 ≤ q * q := Nat.mul_le_mul hq hq
  have h27 : 27 ≤ q * q * q := Nat.mul_le_mul h9 hq
  have h4 : q ^ 4 = q * q * q * q := by ring
  have : 16 * q ≤ q * q * q * q := Nat.mul_le_mul_right q (by omega)
  constructor <;> nlinarith
theorem two_A0_add_one_le {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 2 * A0 q R + 1 ≤ R := by
  obtain ⟨h16q, h16⟩ := sixteen_mul_lt hq hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hsq : √(q : ℝ) ≤ q :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ q by omega)))
  have h16q' : (16 : ℝ) * q < R := by exact_mod_cast h16q
  have hmain : 16 * ((R : ℝ) * √q) ≤ (R : ℝ) ^ 2 := by
    have : 16 * √(q : ℝ) ≤ R := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hR0]
  exact two_ceil_sqrt_add_one_le hmain (by omega)
theorem two_B0_add_one_le {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 2 * B0 q R + 1 ≤ R := by
  obtain ⟨-, h16⟩ := sixteen_mul_lt hq hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have h16' : (16 : ℝ) ≤ R := by exact_mod_cast h16
  have h1 : (1 : ℝ) ≤ √(q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    rw [one_pow]; exact_mod_cast (show 1 ≤ q by omega)
  have hdiv : (R : ℝ) / √q ≤ R := div_le_self hR0 h1
  have hmain : 16 * ((R : ℝ) / √q) ≤ (R : ℝ) ^ 2 := by nlinarith
  exact two_ceil_sqrt_add_one_le hmain (by omega)
theorem redHom_node_injective {q R : ℕ} (hA : 2 * A0 q R + 1 ≤ R) (hB : 2 * B0 q R + 1 ≤ R) :
    Function.Injective (fun n : Node q R => redHom (cq q) R (node q R n)) := by
  intro n n' h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  simp only [redHom_re, redHom_im, node] at hre him
  push_cast at hre him
  rw [sub_left_inj] at hre him
  have h1 := n.1.isLt
  have h1' := n'.1.isLt
  have h2 := n.2.isLt
  have h2' := n'.2.isLt
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    at hre him
  exact Prod.ext (Fin.ext hre) (Fin.ext him)
end ELEM
end

section
open QuadraticAlgebra
namespace ELEM
theorem map_redHom_M (q R : ℕ) [Fact R.Prime] [Fact (IsInert (cq q) R)] :
    (M q R).map (redHom (cq q) R) =
      derivMatrix R (Sof R) (Jof R) (fun n => redHom (cq q) R (node q R n))
        (fun n => redHom (cq q) R (node q R n) ^ R) := by
  refine Matrix.ext fun rs zk => ?_
  simp only [Matrix.map_apply, M, derivMatrix, map_mul, map_pow, map_natCast, redHom_star,
    pow_char_eq_star]
theorem nonvanishing : Nonvanishing := by
  intro q R hq hR hi h4 _h5
  have := Fact.mk hR
  have := Fact.mk hi
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq.large
  have hLI : LinearIndependent (Fp2 (cq q) R) ((M q R).map (redHom (cq q) R)).row := by
    rw [map_redHom_M]
    exact derivMatrix_rows_linearIndependent R (Jof_le hR.one_lt.le)
      (R_mul_Sof_le R (by omega)) _
      (redHom_node_injective (two_A0_add_one_le hq3 h4) (two_B0_add_one_le hq3 h4))
  obtain ⟨f, -, hf⟩ := exists_det_submatrix_ne_zero_of_map (redHom (cq q) R) (M q R) hLI
  exact ⟨f, hf⟩
end ELEM
end

section
open Matrix Equiv Finset
namespace ELEM.Size
theorem norm_det_le_factorial_mul_prod {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ ((Fintype.card n).factorial : ℝ) * ∏ i, b i := by
  calc ‖A.det‖ = ‖∑ σ : Perm n, Perm.sign σ • ∏ i, A (σ i) i‖ := by rw [det_apply]
    _ ≤ ∑ σ : Perm n, ‖Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, ‖A (σ i) i‖ := by
        refine sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h, norm_prod]
    _ ≤ ∑ σ : Perm n, ∏ i, b (σ i) := by
        gcongr with σ _ i _
        exact hb (σ i) i
    _ = ∑ _σ : Perm n, ∏ i, b i := by
        refine sum_congr rfl fun σ _ => ?_
        exact Equiv.prod_comp σ b
    _ = ((Fintype.card n).factorial : ℝ) * ∏ i, b i := by
        simp [Fintype.card_perm]
end ELEM.Size
end

section
open QuadraticAlgebra
namespace ELEM.Size
noncomputable def psi (c : ℕ) : ℂ := ⟨1 / 2, Real.sqrt (4 * c - 1) / 2⟩
theorem psi_mul_psi {c : ℕ} (hc : 1 ≤ c) :
    psi c * psi c = (-(c : ℤ)) • (1 : ℂ) + (1 : ℤ) • psi c := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hs : Real.sqrt (4 * c - 1) * Real.sqrt (4 * c - 1) = 4 * c - 1 :=
    Real.mul_self_sqrt (by linarith)
  apply Complex.ext
  · simp [psi, zsmul_eq_mul]
    linarith
  · simp [psi, zsmul_eq_mul]
    ring
noncomputable def emb (c : ℕ) (hc : 1 ≤ c) : OK c →ₐ[ℤ] ℂ :=
  QuadraticAlgebra.lift ⟨psi c, psi_mul_psi hc⟩
theorem emb_apply {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    emb c hc z = (z.re : ℂ) + (z.im : ℂ) * psi c := by
  simp [emb, zsmul_eq_mul]
theorem normSq_emb {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    Complex.normSq (emb c hc z) = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hs : Real.sqrt (4 * c - 1) * Real.sqrt (4 * c - 1) = 4 * c - 1 :=
    Real.mul_self_sqrt (by linarith)
  rw [emb_apply, Complex.normSq_apply, QuadraticAlgebra.norm_def]
  simp only [psi, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  push_cast
  linear_combination ((z.im : ℝ) ^ 2 / 4) * hs
theorem norm_emb_sq {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    ‖emb c hc z‖ ^ 2 = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  rw [← normSq_emb hc z, Complex.normSq_eq_norm_sq]
theorem norm_emb_star {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    ‖emb c hc (star z)‖ = ‖emb c hc z‖ := by
  have h : ‖emb c hc (star z)‖ ^ 2 = ‖emb c hc z‖ ^ 2 := by
    rw [norm_emb_sq, norm_emb_sq, QuadraticAlgebra.norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
end ELEM.Size
end

section
open QuadraticAlgebra Finset
namespace ELEM.Size
theorem cq_four_mul {q : ℕ} (h : q % 8 = 3) : 4 * cq q = q + 1 := by
  unfold cq; omega
theorem two_mul_sum_le (R S : ℕ) :
    2 * ∑ i : Fin R × Fin S, ((i.1 : ℕ) + (i.2 : ℕ)) ≤ R * S * (R + S) := by
  have hR := Finset.sum_range_id_mul_two R
  have hS := Finset.sum_range_id_mul_two S
  have eR : ∑ i : Fin R, (i : ℕ) = ∑ i ∈ range R, i := Fin.sum_univ_eq_sum_range (fun i => i) R
  have eS : ∑ i : Fin S, (i : ℕ) = ∑ i ∈ range S, i := Fin.sum_univ_eq_sum_range (fun i => i) S
  have hsum : ∑ i : Fin R × Fin S, ((i.1 : ℕ) + (i.2 : ℕ)) =
      S * ∑ i : Fin R, (i : ℕ) + R * ∑ i : Fin S, (i : ℕ) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.mul_sum]
  rw [hsum, eR, eS]
  have h1 : R * (R - 1) ≤ R * R := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : S * (S - 1) ≤ S * S := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith
noncomputable def Tof (q R : ℕ) : ℝ := 2 * Real.sqrt (R * Real.sqrt q)
theorem params {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) :
    181 ≤ Real.sqrt q ∧ 100 ≤ Real.sqrt (R / Real.sqrt q) ∧
      Real.sqrt (R * Real.sqrt q) = Real.sqrt (R / Real.sqrt q) * Real.sqrt q ∧
      10000 * Real.sqrt q ≤ R := by
  have hqR : (32768 : ℝ) ≤ q := by exact_mod_cast hq
  have hq4R : (q : ℝ) ^ 4 < R := by exact_mod_cast hq4
  set u : ℝ := Real.sqrt q with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = q := Real.sq_sqrt (by positivity)
  have hu181 : 181 ≤ u := by nlinarith
  have huq : u ≤ q := by nlinarith
  have hq3 : (10000 : ℝ) ≤ (q : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hqR 3
    norm_num at this; linarith
  have hRu : 10000 * u ≤ R := by
    have : 10000 * (q : ℝ) ≤ (q : ℝ) ^ 4 := by nlinarith
    linarith
  have ht0 : 0 ≤ Real.sqrt (R / u) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (R / u) ^ 2 = R / u := Real.sq_sqrt (by positivity)
  refine ⟨hu181, ?_, ?_, hRu⟩
  · have h : (10000 : ℝ) ≤ R / u := by rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  · have h : (Real.sqrt (R / u) * u) ^ 2 = R * u := by
      rw [mul_pow, ht2]; field_simp
    rw [← h, Real.sqrt_sq (mul_nonneg ht0 hu0)]
theorem one_le_Tof {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) : 1 ≤ Tof q R := by
  obtain ⟨hu, ht, hst, -⟩ := params hq hq4
  unfold Tof; rw [hst]; nlinarith
theorem Tof_le {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) : Tof q R ≤ R := by
  obtain ⟨hu, -, -, hRu⟩ := params hq hq4
  have hs0 : 0 ≤ Real.sqrt (R * Real.sqrt q) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (R * Real.sqrt q) ^ 2 = R * Real.sqrt q :=
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  unfold Tof
  nlinarith
theorem log_Tof {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) :
    Real.log (Tof q R) = Real.log 2 + Real.log R / 2 + Real.log q / 4 := by
  obtain ⟨hu, -, -, hRu⟩ := params hq hq4
  have hR : (0 : ℝ) < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt (R * Real.sqrt q) := Real.sqrt_pos.mpr (by positivity)
  unfold Tof
  rw [Real.log_mul (by norm_num) hs.ne', Real.log_sqrt (by positivity),
    Real.log_mul hR.ne' (by positivity), Real.log_sqrt hq0.le]
  ring
theorem node_sq_le {u t a b c : ℝ} (hu : 181 ≤ u) (ht : 100 ≤ t) (hc : c = (u ^ 2 + 1) / 4)
    (ha : a ^ 2 ≤ (t * u + 1) ^ 2) (hb : b ^ 2 ≤ (t + 1) ^ 2) :
    a * a + 1 * a * b - (-c) * b * b ≤ (2 * (t * u)) ^ 2 := by
  have hab : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcb : c * b ^ 2 ≤ c * (t + 1) ^ 2 := mul_le_mul_of_nonneg_left hb hc0
  have hp : 18100 ≤ t * u := by nlinarith
  have e1 : 12 * (t * u) ≤ (t * u) ^ 2 := by nlinarith
  have e2 : 2 * u ^ 2 * t ≤ (t * u) ^ 2 := by
    have : 0 ≤ u ^ 2 * t := by positivity
    nlinarith
  have e3 : u ^ 2 ≤ (t * u) ^ 2 := by nlinarith
  have e4 : 3 * t ^ 2 ≤ (t * u) ^ 2 := by
    have h3 : 3 ≤ u ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h3 (sq_nonneg t)
    nlinarith
  have e5 : 6 * t + 9 ≤ (t * u) ^ 2 := by nlinarith
  have hnum : 3 / 2 * (t * u + 1) ^ 2 + ((u ^ 2 + 3) / 4) * (t + 1) ^ 2 ≤ 4 * (t * u) ^ 2 := by
    nlinarith
  rw [hc] at hcb
  nlinarith
theorem sq_sub_le {x A s : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * A) (hA : A < s + 1) :
    (x - A) ^ 2 ≤ (s + 1) ^ 2 := by
  have h1 : (x - A) ^ 2 ≤ A ^ 2 := by nlinarith
  nlinarith
theorem norm_node_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (n : Node q R) : ‖emb (cq q) hc1 (node q R n)‖ ≤ Tof q R := by
  obtain ⟨hu, ht, hst, -⟩ := params hq hq4
  have hcR : 4 * (cq q : ℝ) = q + 1 := by exact_mod_cast cq_four_mul hq8
  have hu2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : (cq q : ℝ) = (Real.sqrt q ^ 2 + 1) / 4 := by rw [hu2]; linarith
  have hi : ((n.1 : ℕ) : ℝ) ≤ 2 * (A0 q R : ℝ) := by
    have := n.1.isLt; exact_mod_cast (by omega : (n.1 : ℕ) ≤ 2 * A0 q R)
  have hj : ((n.2 : ℕ) : ℝ) ≤ 2 * (B0 q R : ℝ) := by
    have := n.2.isLt; exact_mod_cast (by omega : (n.2 : ℕ) ≤ 2 * B0 q R)
  have hA0 : (A0 q R : ℝ) < Real.sqrt (R * Real.sqrt q) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hB0 : (B0 q R : ℝ) < Real.sqrt (R / Real.sqrt q) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  rw [hst] at hA0
  have ha := sq_sub_le (Nat.cast_nonneg _) hi hA0
  have hb := sq_sub_le (Nat.cast_nonneg _) hj hB0
  have key : ((QuadraticAlgebra.norm (node q R n) : ℤ) : ℝ) ≤ Tof q R ^ 2 := by
    rw [QuadraticAlgebra.norm_def]
    unfold Tof
    rw [hst]
    simp only [node]
    push_cast
    exact node_sq_le hu ht hc ha hb
  rw [← norm_emb_sq hc1] at key
  have hT0 : 0 ≤ Tof q R := by unfold Tof; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hT0 two_ne_zero).mp key
noncomputable def rowBound (q R : ℕ) (i : Row R) : ℝ :=
  Tof q R ^ ((i.1 : ℕ) + (i.2 : ℕ)) * ((R : ℝ) / Tof q R) ^ Jof R
theorem entry_real_le {R T e : ℝ} {r s k J Rn : ℕ} (hRn : (Rn : ℝ) = R) (hT1 : 1 ≤ T)
    (hRT : 1 ≤ R / T) (he0 : 0 ≤ e) (he : e ≤ T) (hr : r < Rn) (hk : k ≤ J) :
    ((r.descFactorial k : ℕ) : ℝ) * e ^ (r - k) * e ^ s ≤ T ^ (r + s) * (R / T) ^ J := by
  have hT0 : 0 < T := by linarith
  have hR0 : 0 ≤ R := by
    have := (le_div_iff₀ hT0).mp hRT
    linarith
  by_cases hkr : k ≤ r
  · have hd : ((r.descFactorial k : ℕ) : ℝ) ≤ R ^ k := by
      have h1 : r.descFactorial k ≤ r ^ k := Nat.descFactorial_le_pow r k
      have h2 : r ^ k ≤ Rn ^ k := Nat.pow_le_pow_left hr.le k
      rw [← hRn]; exact_mod_cast h1.trans h2
    have hRk : R ^ k = (R / T) ^ k * T ^ k := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hT0.ne')]
    have hpow : T ^ (r - k) * T ^ k = T ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    calc ((r.descFactorial k : ℕ) : ℝ) * e ^ (r - k) * e ^ s
        ≤ R ^ k * T ^ (r - k) * T ^ s := by
          have h1 := pow_le_pow_left₀ he0 he (r - k)
          have h2 := pow_le_pow_left₀ he0 he s
          have h3 : 0 ≤ R ^ k := pow_nonneg hR0 k
          have h4 : 0 ≤ T ^ (r - k) := by positivity
          exact mul_le_mul (mul_le_mul hd h1 (by positivity) h3) h2 (by positivity)
            (mul_nonneg h3 h4)
      _ = (R / T) ^ k * (T ^ (r - k) * T ^ k) * T ^ s := by rw [hRk]; ring
      _ = (R / T) ^ k * T ^ (r + s) := by rw [hpow, pow_add]; ring
      _ ≤ (R / T) ^ J * T ^ (r + s) := by
          gcongr
      _ = T ^ (r + s) * (R / T) ^ J := by ring
  · have hd : r.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hd]
    have : 0 ≤ T ^ (r + s) * (R / T) ^ J := by positivity
    simpa using this
theorem norm_entry_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (f : Row R → Col q R) (i j : Row R) :
    ‖emb (cq q) hc1 (M q R i (f j))‖ ≤ rowBound q R i := by
  have hT1 := one_le_Tof hq hq4
  have hTR := Tof_le hq hq4
  have hRT : 1 ≤ (R : ℝ) / Tof q R := by rw [le_div_iff₀ (by linarith)]; linarith
  have he := norm_node_le hq hq8 hq4 hc1 (f j).1
  unfold M rowBound
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_emb_star, Complex.norm_natCast]
  exact entry_real_le rfl hT1 hRT (norm_nonneg _) he i.1.isLt ((f j).2.isLt).le
theorem norm_minor_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (f : Row R → Col q R) :
    ‖emb (cq q) hc1 (minor q R f)‖ ≤
      ((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i := by
  have h := norm_det_le_factorial_mul_prod
    ((emb (cq q) hc1 : OK (cq q) →+* ℂ).mapMatrix ((M q R).submatrix id f)) (rowBound q R)
    (fun i j => norm_entry_le hq hq8 hq4 hc1 f i j)
  have hcard : Fintype.card (Row R) = R * Sof R := by simp [Row]
  rw [hcard, ← RingHom.map_det] at h
  exact h
theorem log_rowBound {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) (i : Row R) :
    Real.log (rowBound q R i) = (((i.1 : ℕ) + (i.2 : ℕ) : ℕ) : ℝ) * Real.log (Tof q R) +
      (Jof R : ℝ) * (Real.log R - Real.log (Tof q R)) := by
  have hT0 : 0 < Tof q R := by linarith [one_le_Tof hq hq4]
  have hR0 : (0 : ℝ) < R := by linarith [Tof_le hq hq4]
  unfold rowBound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div hR0.ne' hT0.ne']
theorem one_le_rowBound {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) (i : Row R) :
    1 ≤ rowBound q R i := by
  have hT1 := one_le_Tof hq hq4
  have hTR := Tof_le hq hq4
  have hRT : 1 ≤ (R : ℝ) / Tof q R := by rw [le_div_iff₀ (by linarith)]; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) (one_le_pow₀ hRT)
theorem log_Delta_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (f : Row R → Col q R) :
    Real.log (Delta q R f) ≤
      2 * (Real.log ((R * Sof R).factorial : ℝ) + ∑ i, Real.log (rowBound q R i)) := by
  have hc1 : 1 ≤ cq q := by have := cq_four_mul hq8; omega
  have hD := norm_minor_le hq hq8 hq4 hc1 f
  have hb1 := one_le_rowBound hq hq4
  have hprod1 : 1 ≤ ∏ i, rowBound q R i := by
    exact Finset.one_le_prod (fun i _ => hb1 i)
  have hfac1 : (1 : ℝ) ≤ ((R * Sof R).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hP1 := one_le_mul_of_one_le_of_one_le hfac1 hprod1
  have hlogP : Real.log (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) =
      Real.log ((R * Sof R).factorial : ℝ) + ∑ i, Real.log (rowBound q R i) := by
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_prod (fun i _ => (by linarith [hb1 i] : rowBound q R i ≠ 0))]
  rw [← hlogP]
  have hDelta : Delta q R f = ‖emb (cq q) hc1 (minor q R f)‖ ^ 2 := by
    rw [norm_emb_sq]; rfl
  have hle : Delta q R f ≤ (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) ^ 2 := by
    rw [hDelta]; exact pow_le_pow_left₀ (norm_nonneg _) hD 2
  rcases (show (0 : ℝ) ≤ Delta q R f by rw [hDelta]; positivity).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    have := Real.log_nonneg hP1
    linarith
  · calc Real.log (Delta q R f)
        ≤ Real.log ((((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) ^ 2) :=
          Real.log_le_log h0 hle
      _ = 2 * Real.log (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) := by
          rw [Real.log_pow]; norm_num
theorem final_arith {R S J lR lT lN sm lF lB Y l2 lq : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hS12 : S * 12 ≤ R) (hJ48 : J * 48 ≤ R + 47) (hlT0 : 0 ≤ lT) (hlTR : lT ≤ lR)
    (hlN : lN ≤ 2 * lR) (hsm : 2 * sm ≤ R * S * (R + S)) (hlF : lF ≤ R * S * lN)
    (hlB : lB = sm * lT + R * S * (J * (lR - lT)))
    (hY : Y ≤ 2 * (lF + lB)) (hlT : lT = l2 + lR / 2 + lq / 4) :
    Y / (R ^ 2 * S) ≤ 9 / 16 * lR + 25 / 96 * lq + 25 / 24 * l2 + 6 * lR / R := by
  rw [div_le_iff₀ (by positivity)]
  have hRS0 : 0 ≤ R * S := by positivity
  have pa : 2 * lF ≤ 4 * (R * S * lR) := by nlinarith
  have pb : 2 * sm * lT ≤ 13 / 12 * (R ^ 2 * S * lT) := by
    have h1 := mul_le_mul_of_nonneg_right hsm hlT0
    have h2 : R * S * (R + S) ≤ 13 / 12 * (R ^ 2 * S) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hlT0
    linarith
  have pc : 2 * (R * S * (J * (lR - lT))) ≤ R ^ 2 * S * (lR - lT) / 24 + 2 * (R * S * lR) := by
    have hd : 0 ≤ lR - lT := by linarith
    have h1 : J ≤ R / 48 + 1 := by linarith
    have h2 : 0 ≤ R * S * (lR - lT) := mul_nonneg hRS0 hd
    have h3 : 0 ≤ R * S * lT := mul_nonneg hRS0 hlT0
    have h4 := mul_le_mul_of_nonneg_left h1 h2
    nlinarith
  have hrhs : (9 / 16 * lR + 25 / 96 * lq + 25 / 24 * l2 + 6 * lR / R) * (R ^ 2 * S) =
      R ^ 2 * S * (25 / 24 * lT + lR / 24) + 6 * (R * S * lR) := by
    rw [hlT]; field_simp; ring
  rw [hrhs, hlB] at *
  nlinarith
theorem sizeBound : ELEM.SizeBound := by
  intro q R hq _hRp _hRi hq4 _hR5 f _hf
  have hq0 := hq.large
  have hq8 := hq.mod_eight
  have hT1 := one_le_Tof hq0 hq4
  have hTR := Tof_le hq0 hq4
  have hR0 : (0 : ℝ) < R := by linarith
  have hS1 : 1 ≤ Sof R := by
    have h : (12 : ℝ) ≤ R := by
      obtain ⟨hu, -, -, hRu⟩ := params hq0 hq4
      linarith
    have : 12 ≤ R := by exact_mod_cast h
    unfold Sof; omega
  have hSpos : (0 : ℝ) < Sof R := by exact_mod_cast hS1
  have hS12 : (Sof R : ℝ) * 12 ≤ R := by exact_mod_cast Nat.div_mul_le_self R 12
  have hJ48 : (Jof R : ℝ) * 48 ≤ R + 47 := by
    have : (R + 47) / 48 * 48 ≤ R + 47 := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hNR : ((R * Sof R : ℕ) : ℝ) = R * Sof R := by push_cast; ring
  have hNpos : (0 : ℝ) < ((R * Sof R : ℕ) : ℝ) := by rw [hNR]; positivity
  have hlogfac : Real.log ((R * Sof R).factorial : ℝ) ≤
      (R : ℝ) * Sof R * Real.log ((R * Sof R : ℕ) : ℝ) := by
    have h : ((R * Sof R).factorial : ℝ) ≤ ((R * Sof R : ℕ) : ℝ) ^ (R * Sof R) := by
      exact_mod_cast Nat.factorial_le_pow _
    calc Real.log ((R * Sof R).factorial : ℝ)
        ≤ Real.log (((R * Sof R : ℕ) : ℝ) ^ (R * Sof R)) := Real.log_le_log (by positivity) h
      _ = (R : ℝ) * Sof R * Real.log ((R * Sof R : ℕ) : ℝ) := by
          rw [Real.log_pow, hNR]
  have hlN : Real.log ((R * Sof R : ℕ) : ℝ) ≤ 2 * Real.log R := by
    have h : ((R * Sof R : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by
      rw [hNR]
      have : (Sof R : ℝ) ≤ R := by linarith
      nlinarith
    calc Real.log ((R * Sof R : ℕ) : ℝ) ≤ Real.log ((R : ℝ) ^ 2) := Real.log_le_log hNpos h
      _ = 2 * Real.log R := by rw [Real.log_pow]; norm_num
  have hsumb : ∑ i : Row R, Real.log (rowBound q R i) =
      ((∑ i : Row R, ((i.1 : ℕ) + (i.2 : ℕ)) : ℕ) : ℝ) * Real.log (Tof q R) +
        (R : ℝ) * Sof R * ((Jof R : ℝ) * (Real.log R - Real.log (Tof q R))) := by
    simp only [log_rowBound hq0 hq4, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp [Row, Finset.sum_add_distrib]
    ring
  have hsum2 : 2 * ((∑ i : Row R, ((i.1 : ℕ) + (i.2 : ℕ)) : ℕ) : ℝ) ≤
      (R : ℝ) * Sof R * (R + Sof R) := by
    exact_mod_cast two_mul_sum_le R (Sof R)
  exact final_arith hR0 hSpos hS12 hJ48 (Real.log_nonneg hT1)
    (Real.log_le_log (by linarith) hTR) hlN hsum2 hlogfac hsumb (log_Delta_le hq0 hq8 hq4 f)
    (log_Tof hq0 hq4)
end ELEM.Size
end

section
open Matrix
namespace ELEM.Divisibility
theorem det_eq_one_of_fst_unitriangular {K : Type*} [CommRing K] {R S : ℕ}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) K) (hdiag : ∀ i, U i i = 1)
    (hlow : ∀ i j, i ≠ j → ¬ (j.1 < i.1) → U i j = 0) : U.det = 1 := by
  classical
  let e : Fin R × Fin S ≃ Lex (Fin R × Fin S) := toLex
  rw [← det_reindex_self e U]
  have htri : (reindex e e U).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp only [reindex_apply, submatrix_apply]
    apply hlow
    · intro h
      exact (ne_of_lt hij') (e.symm.injective h)
    · intro h
      have h1 : (ofLex j).1 < (ofLex i).1 := h
      rcases Prod.Lex.lt_iff.mp hij' with h2 | ⟨h2, -⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
      · exact absurd (h2 ▸ h1) (lt_irrefl _)
  rw [det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [reindex_apply, submatrix_apply]
  exact hdiag _
theorem det_submatrix_mul_of_fst_unitriangular {K : Type*} [CommRing K] {R S : ℕ} {ι : Type*}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) K) (hdiag : ∀ i, U i i = 1)
    (hlow : ∀ i j, i ≠ j → ¬ (j.1 < i.1) → U i j = 0)
    (M : Matrix (Fin R × Fin S) ι K) (f : Fin R × Fin S → ι) :
    ((U * M).submatrix id f).det = (M.submatrix id f).det := by
  have h : (U * M).submatrix id f = U * M.submatrix id f := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, det_eq_one_of_fst_unitriangular U hdiag hlow, one_mul]
theorem pow_sum_dvd_det {K : Type*} [CommRing K] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m K) (x : K) (e : m → ℕ) (h : ∀ i j, x ^ e i ∣ A i j) :
    x ^ (∑ i, e i) ∣ A.det := by
  rw [det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  apply Dvd.dvd.mul_left
  rw [← Equiv.sum_comp σ e, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => h (σ i) i
end ELEM.Divisibility
end

section
open Polynomial QuadraticAlgebra Finset
namespace ELEM.Divisibility
section poly
variable {K : Type*} [CommRing K]
theorem iterate_derivative_add' (k : ℕ) (a b : K[X]) :
    derivative^[k] (a + b) = derivative^[k] a + derivative^[k] b := by
  simp_rw [← Module.End.pow_apply, map_add]
theorem pow_dvd_eval_iterate_derivative (p : ℕ) {z t : K} (hz : (p : K) ∣ z ^ p - t) :
    ∀ (h k : ℕ) (G : K[X]), (p : K) ^ h ∣ (derivative^[k] (G * (X ^ p - C t) ^ h)).eval z := by
  intro h
  induction h with
  | zero => intro k G; simp
  | succ h ih =>
    intro k
    induction k with
    | zero =>
      intro G
      simp only [Function.iterate_zero, id_eq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hz _) _
    | succ k ihk =>
      intro G
      have hd : derivative (G * (X ^ p - C t) ^ (h + 1)) =
          derivative G * (X ^ p - C t) ^ (h + 1) +
            C (p : K) * ((G * C ((h + 1 : ℕ) : K) * X ^ (p - 1)) * (X ^ p - C t) ^ h) := by
        rw [derivative_mul, derivative_pow, derivative_sub, derivative_X_pow, derivative_C,
          Nat.add_one_sub_one]
        ring
      rw [Function.iterate_succ_apply, hd, iterate_derivative_add', iterate_derivative_C_mul,
        eval_add, eval_mul, eval_C]
      exact dvd_add (ihk _) (by rw [pow_succ']; exact mul_dvd_mul_left _ (ih k _))
theorem expand_row (p r s h : ℕ) (hph : p * h ≤ r) (t : K) :
    C (t ^ s) * X ^ (r - p * h) * (X ^ p - C t) ^ h =
      ∑ i ∈ range (h + 1), C ((-1) ^ i * (h.choose i : K) * t ^ (s + i)) * X ^ (r - p * i) := by
  rw [show (X ^ p - C t : K[X]) = -C t + X ^ p by ring, add_pow, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hih : i ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hpi : p * i ≤ p * h := Nat.mul_le_mul_left p hih
  have hsplit : r - p * i = (r - p * h) + p * (h - i) := by
    rw [Nat.mul_sub]
    generalize p * i = a at *
    generalize p * h = b at *
    omega
  rw [hsplit]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, pow_add, pow_mul]
  ring
theorem eval_iterate_derivative_row (p r s h k : ℕ) (hph : p * h ≤ r) (z t : K) :
    (derivative^[k] (C (t ^ s) * X ^ (r - p * h) * (X ^ p - C t) ^ h)).eval z =
      ∑ i ∈ range (h + 1), (-1) ^ i * (h.choose i : K) *
        (((r - p * i).descFactorial k : ℕ) * z ^ (r - p * i - k) * t ^ (s + i)) := by
  rw [expand_row p r s h hph, iterate_derivative_sum, eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_natCast_mul, eval_mul, eval_C,
    eval_mul, eval_natCast, eval_pow, eval_X]
  ring
end poly
def hgt (p S r s : ℕ) : ℕ := min (r / p) (S - 1 - s)
theorem mul_hgt_le (p S r s : ℕ) : p * hgt p S r s ≤ r :=
  (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le r p)
def Umat (K : Type*) [CommRing K] (R S p : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) K :=
  fun a b =>
    if (a.2 : ℕ) ≤ b.2 ∧ (b.2 : ℕ) - a.2 ≤ hgt p S a.1 a.2 ∧ (b.1 : ℕ) + p * ((b.2 : ℕ) - a.2) = a.1
    then (-1) ^ ((b.2 : ℕ) - a.2) * ((hgt p S a.1 a.2).choose ((b.2 : ℕ) - a.2) : K) else 0
theorem Umat_diag (K : Type*) [CommRing K] (R S p : ℕ) (a : Fin R × Fin S) :
    Umat K R S p a a = 1 := by
  simp [Umat]
theorem Umat_low (K : Type*) [CommRing K] (R S p : ℕ) (hp : 0 < p) (a b : Fin R × Fin S)
    (hab : a ≠ b) (hlt : ¬ (b.1 < a.1)) : Umat K R S p a b = 0 := by
  unfold Umat
  rw [if_neg]
  rintro ⟨h1, -, h3⟩
  rcases Nat.eq_zero_or_pos ((b.2 : ℕ) - a.2) with h0 | h0
  · apply hab
    rw [h0, mul_zero, add_zero] at h3
    exact Prod.ext (Fin.ext h3.symm) (Fin.ext (by omega))
  · apply hlt
    have : 0 < p * ((b.2 : ℕ) - a.2) := Nat.mul_pos hp h0
    show (b.1 : ℕ) < a.1
    omega
variable (q R : ℕ)
noncomputable def Mtil (p : ℕ) : Matrix (Row R) (Col q R) (OK (cq q)) := fun rs zk =>
  (derivative^[zk.2] (C (star (node q R zk.1) ^ (rs.2 : ℕ)) *
      X ^ ((rs.1 : ℕ) - p * hgt p (Sof R) rs.1 rs.2) *
      (X ^ p - C (star (node q R zk.1))) ^ hgt p (Sof R) rs.1 rs.2)).eval (node q R zk.1)
theorem sum_fst_Umat_mul (p : ℕ) (rs : Row R) (zk : Col q R) (y : Fin (Sof R)) :
    ∑ x : Fin R, Umat (OK (cq q)) R (Sof R) p rs (x, y) * M q R (x, y) zk =
      if (rs.2 : ℕ) ≤ y ∧ (y : ℕ) - rs.2 ≤ hgt p (Sof R) rs.1 rs.2 then
        (-1) ^ ((y : ℕ) - rs.2) * ((hgt p (Sof R) rs.1 rs.2).choose ((y : ℕ) - rs.2) : OK (cq q)) *
          ((((rs.1 : ℕ) - p * ((y : ℕ) - rs.2)).descFactorial zk.2 : ℕ) *
            node q R zk.1 ^ ((rs.1 : ℕ) - p * ((y : ℕ) - rs.2) - zk.2) *
            star (node q R zk.1) ^ (y : ℕ))
      else 0 := by
  obtain ⟨r, s⟩ := rs
  set h := hgt p (Sof R) r s
  split_ifs with hc
  · have hle : p * ((y : ℕ) - s) ≤ r :=
      (Nat.mul_le_mul_left p hc.2).trans (mul_hgt_le p (Sof R) r s)
    have hlt : (r : ℕ) - p * ((y : ℕ) - s) < R := by omega
    rw [sum_eq_single ⟨(r : ℕ) - p * ((y : ℕ) - s), hlt⟩]
    · rw [Umat, if_pos ⟨hc.1, hc.2, by simp only; omega⟩]
      rfl
    · intro x _ hx
      rw [Umat, if_neg, zero_mul]
      rintro ⟨-, -, h3⟩
      apply hx
      ext
      simp only at h3 ⊢
      omega
    · simp
  · refine sum_eq_zero fun x _ => ?_
    rw [Umat, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩), zero_mul]
theorem Umat_mul_M (p : ℕ) : Umat (OK (cq q)) R (Sof R) p * M q R = Mtil q R p := by
  refine Matrix.ext fun rs zk => ?_
  obtain ⟨r, s⟩ := rs
  set h := hgt p (Sof R) r s with hh
  rw [Matrix.mul_apply, Fintype.sum_prod_type, sum_comm]
  simp_rw [sum_fst_Umat_mul q R p (r, s) zk]
  rw [Mtil, eval_iterate_derivative_row p r s h zk.2 (mul_hgt_le p (Sof R) r s)]
  set F : ℕ → OK (cq q) := fun y =>
    if (s : ℕ) ≤ y ∧ y - s ≤ h then
      (-1) ^ (y - s) * (h.choose (y - s) : OK (cq q)) *
        ((((r : ℕ) - p * (y - s)).descFactorial zk.2 : ℕ) *
          node q R zk.1 ^ ((r : ℕ) - p * (y - s) - zk.2) * star (node q R zk.1) ^ y)
    else 0 with hF
  have hS : (s : ℕ) + (h + 1) ≤ Sof R := by
    have : h ≤ Sof R - 1 - s := min_le_right _ _
    have := s.isLt
    omega
  refine (Fin.sum_univ_eq_sum_range F (Sof R)).trans ?_
  have hsub : Ico (s : ℕ) (s + (h + 1)) ⊆ range (Sof R) := by
    intro y hy
    simp only [mem_Ico] at hy
    simp only [mem_range]
    omega
  rw [← sum_subset hsub]
  · rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [hF]
    simp only [Nat.add_sub_cancel_left, le_add_iff_nonneg_right, zero_le, true_and, hi', if_true]
  · intro y _ hy
    simp only [mem_Ico, not_and, not_lt] at hy
    rw [hF]
    simp only
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := hy h1
    omega
theorem minor_eq_det_Mtil {p : ℕ} (hp : 0 < p) (f : Row R → Col q R) :
    minor q R f = ((Mtil q R p).submatrix id f).det := by
  rw [minor, ← Umat_mul_M q R p, det_submatrix_mul_of_fst_unitriangular _ (Umat_diag _ _ _ p)
    (Umat_low _ _ _ p hp)]
theorem pow_dvd_minor {p : ℕ} (hp : p.Prime) (hi : IsInert (cq q) p) (f : Row R → Col q R) :
    (p : OK (cq q)) ^ (∑ i : Row R, hgt p (Sof R) i.1 i.2) ∣ minor q R f := by
  classical
  rw [minor_eq_det_Mtil q R hp.pos]
  refine pow_sum_dvd_det _ _ (fun i : Row R => hgt p (Sof R) i.1 i.2) fun i j => ?_
  exact pow_dvd_eval_iterate_derivative p (frobenius_dvd hp hi _) _ _ _
theorem pow_two_mul_dvd_norm_minor {p : ℕ} (hp : p.Prime) (hi : IsInert (cq q) p)
    (f : Row R → Col q R) :
    (p : ℤ) ^ (2 * ∑ i : Row R, hgt p (Sof R) i.1 i.2) ∣ QuadraticAlgebra.norm (minor q R f) := by
  obtain ⟨y, hy⟩ := pow_dvd_minor q R hp hi f
  rw [hy, map_mul, map_pow, QuadraticAlgebra.norm_natCast, ← pow_mul]
  exact dvd_mul_right _ _
end ELEM.Divisibility
end

section
open Finset
namespace ELEM.Divisibility
theorem two_mul_sum_range_id_real (n : ℕ) : 2 * ∑ j ∈ range n, (j : ℝ) = n * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring
theorem two_mul_sum_min_ge (k S : ℕ) :
    2 * (S : ℝ) * k - (k : ℝ) ^ 2 - k ≤ 2 * ∑ j ∈ range S, ((min k j : ℕ) : ℝ) := by
  rcases le_total S k with hSk | hkS
  · have : ∑ j ∈ range S, ((min k j : ℕ) : ℝ) = ∑ j ∈ range S, (j : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_right (by have := mem_range.mp hj; omega)]
    rw [this, two_mul_sum_range_id_real]
    have : (S : ℝ) ≤ k := by exact_mod_cast hSk
    nlinarith
  · rw [← sum_range_add_sum_Ico _ hkS]
    have h1 : ∑ j ∈ range k, ((min k j : ℕ) : ℝ) = ∑ j ∈ range k, (j : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_right (by have := mem_range.mp hj; omega)]
    have h2 : ∑ j ∈ Ico k S, ((min k j : ℕ) : ℝ) = ∑ j ∈ Ico k S, (k : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_left (mem_Ico.mp hj).1]
    rw [h1, h2, mul_add, two_mul_sum_range_id_real, sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub hkS]
    ring_nf
    exact le_refl _
theorem floor_sum_ge (p : ℕ) (hp : 0 < p) (R : ℕ) :
    (R : ℝ) * ((R : ℝ) - p) ≤ 2 * p * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rcases lt_or_ge R p with hRp | hRp
    · have h0 : 0 ≤ ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
      have : ((R : ℝ) - p) < 0 := by
        have : (R : ℝ) < p := by exact_mod_cast hRp
        linarith
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      nlinarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hRp
      have hm : m < p + m := by omega
      have ihm := ih m hm
      rw [sum_range_add]
      have hzero : ∑ x ∈ range p, ((x / p : ℕ) : ℝ) = 0 :=
        sum_eq_zero fun x hx => by rw [Nat.div_eq_of_lt (mem_range.mp hx), Nat.cast_zero]
      have hstep : ∀ x : ℕ, (((p + x) / p : ℕ) : ℝ) = ((x / p : ℕ) : ℝ) + 1 := fun x => by
        rw [add_comm p x, Nat.add_div_right x hp, Nat.cast_add, Nat.cast_one]
      rw [hzero, sum_congr rfl fun x _ => hstep x, sum_add_distrib, sum_const, card_range,
        nsmul_eq_mul, mul_one, Nat.cast_add]
      nlinarith
theorem sum_range_sq_le (R : ℕ) : ∑ r ∈ range R, ((r : ℝ)) ^ 2 ≤ (R : ℝ) ^ 3 / 3 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith
theorem sum_range_le (R : ℕ) : ∑ r ∈ range R, (r : ℝ) ≤ (R : ℝ) ^ 2 / 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith
theorem two_mul_sum_hgt_ge (p R S : ℕ) (hp : 0 < p) :
    (S : ℝ) * R * (R - p) / p - (R : ℝ) ^ 3 / (3 * p ^ 2) - (R : ℝ) ^ 2 / (2 * p) ≤
      2 * ∑ i : Fin R × Fin S, (hgt p S i.1 i.2 : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hrow : ∀ r : Fin R, ∑ s : Fin S, (hgt p S r s : ℝ) =
      ((∑ j ∈ range S, min ((r : ℕ) / p) j : ℕ) : ℝ) := by
    intro r
    rw [← Nat.cast_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun s => hgt p S r s) S]
    exact sum_range_reflect (fun j => min ((r : ℕ) / p) j) S
  have hper : ∀ r : ℕ, 2 * (S : ℝ) * ((r / p : ℕ) : ℝ) - ((r : ℝ) / p) ^ 2 - (r : ℝ) / p ≤
      2 * ((∑ j ∈ range S, min (r / p) j : ℕ) : ℝ) := by
    intro r
    have hk0 : (0 : ℝ) ≤ ((r / p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk : ((r / p : ℕ) : ℝ) ≤ (r : ℝ) / p := Nat.cast_div_le
    generalize r / p = k at hk hk0 ⊢
    have h1 := two_mul_sum_min_ge k S
    rw [Nat.cast_sum]
    nlinarith
  rw [Fintype.sum_prod_type]
  simp_rw [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun r => ((∑ j ∈ range S, min (r / p) j : ℕ) : ℝ)) R]
  have hfl : (R : ℝ) * (R - p) ≤ 2 * p * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) :=
    floor_sum_ge p hp R
  have hsum := sum_le_sum fun r (_ : r ∈ range R) => hper r
  rw [← mul_sum] at hsum
  have e1 : ∑ r ∈ range R, (2 * (S : ℝ) * ((r / p : ℕ) : ℝ) - ((r : ℝ) / p) ^ 2 - (r : ℝ) / p) =
      2 * S * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) - (∑ r ∈ range R, (r : ℝ) ^ 2) / p ^ 2 -
        (∑ r ∈ range R, (r : ℝ)) / p := by
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_div, sum_div]
    simp only [div_pow]
  rw [e1] at hsum
  have a1 : (S : ℝ) * R * (R - p) / p ≤ 2 * S * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hp']
    have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    nlinarith
  have a2 : (∑ r ∈ range R, (r : ℝ) ^ 2) / p ^ 2 ≤ (R : ℝ) ^ 3 / (3 * p ^ 2) := by
    rw [show (R : ℝ) ^ 3 / (3 * p ^ 2) = (R : ℝ) ^ 3 / 3 / p ^ 2 by ring]
    exact div_le_div_of_nonneg_right (sum_range_sq_le R) (by positivity)
  have a3 : (∑ r ∈ range R, (r : ℝ)) / p ≤ (R : ℝ) ^ 2 / (2 * p) := by
    rw [show (R : ℝ) ^ 2 / (2 * p) = (R : ℝ) ^ 2 / 2 / p by ring]
    exact div_le_div_of_nonneg_right (sum_range_le R) hp'.le
  linarith
end ELEM.Divisibility
end

section
open Finset Real
namespace ELEM.Divisibility
theorem norm_pos_of_ne_zero {c : ℕ} (hc : 1 ≤ c) {z : OK c} (hz : z ≠ 0) :
    0 < QuadraticAlgebra.norm z := by
  rw [QuadraticAlgebra.norm_def]
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  rcases eq_or_ne z.im 0 with him | him
  · have hre : z.re ≠ 0 := by
      intro hre
      exact hz (QuadraticAlgebra.ext hre him)
    rw [him]
    simp only [mul_zero, sub_zero, add_zero]
    exact mul_self_pos.mpr hre
  · have h1 : 0 < z.im * z.im := mul_self_pos.mpr him
    nlinarith [sq_nonneg (2 * z.re + z.im)]
variable (q R : ℕ)
theorem divisibility_of_subset (hq : AnalyticSetting q) (hq4 : q ^ 4 < R)
    (f : Row R → Col q R) (hf : minor q R f ≠ 0) (P : Finset ℕ) (hPR : P ⊆ Nat.primesLE R)
    (hPi : ∀ p ∈ P, IsInert (cq q) p) :
    (∑ p ∈ P, Real.log p / p) - (∑ p ∈ P, Real.log p / p) / (2 * Sof R) - 79 / 18 ≤
      Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R) := by
  classical
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hPR hp)
  have hR : 144 ≤ R := by
    have h1 : 32768 ≤ q := hq.large
    have : 144 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h1 4)
    omega
  have hS0 : 0 < Sof R := by unfold Sof; omega
  have hS13 : R ≤ 13 * Sof R := by unfold Sof; omega
  set S := Sof R with hSdef
  set H : ℕ → ℕ := fun p => ∑ i : Row R, hgt p (Sof R) i.1 i.2 with hH
  set N := QuadraticAlgebra.norm (minor q R f) with hN
  have hc : 1 ≤ cq q := by unfold cq; have := hq.large; omega
  have hNpos : 0 < N := norm_pos_of_ne_zero hc hf
  have hdvd : ∏ p ∈ P, (p : ℤ) ^ (2 * H p) ∣ N := by
    refine Finset.prod_dvd_of_coprime ?_ fun p hp => pow_two_mul_dvd_norm_minor q R (hPp p hp)
      (hPi p hp) f
    intro p hp p' hp' hne
    exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hPp p hp) (hPp p' hp')).mpr hne)).pow
  have hle : ∏ p ∈ P, (p : ℤ) ^ (2 * H p) ≤ N := Int.le_of_dvd hNpos hdvd
  have hpow : ∀ p ∈ P, (0 : ℝ) < (p : ℝ) ^ (2 * H p) := fun p hp =>
    pow_pos (by exact_mod_cast (hPp p hp).pos) _
  have hlog : ∑ p ∈ P, 2 * (H p : ℝ) * Real.log p ≤ Real.log (Delta q R f) := by
    have e : ∑ p ∈ P, 2 * (H p : ℝ) * Real.log p = Real.log (∏ p ∈ P, (p : ℝ) ^ (2 * H p)) := by
      rw [Real.log_prod (fun p hp => (hpow p hp).ne')]
      refine sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
      push_cast
      ring
    rw [e, Delta]
    refine Real.log_le_log (prod_pos hpow) ?_
    rw [← hN]
    exact_mod_cast hle
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS0
  have hterm : ∀ p ∈ P,
      (S : ℝ) * R ^ 2 * (Real.log p / p) - S * R * Real.log p - (R : ℝ) ^ 3 / 3 * (Real.log p / p ^ 2)
        - (R : ℝ) ^ 2 / 2 * (Real.log p / p) ≤ 2 * (H p : ℝ) * Real.log p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPp p hp).pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hPp p hp).one_lt.le)
    have h13 := two_mul_sum_hgt_ge p R S (hPp p hp).pos
    have hHc : (H p : ℝ) = ∑ i : Fin R × Fin S, (hgt p S i.1 i.2 : ℝ) := by
      rw [hH]
      push_cast
      rfl
    rw [← hHc] at h13
    have e : (S : ℝ) * R ^ 2 * (Real.log p / p) - S * R * Real.log p -
        (R : ℝ) ^ 3 / 3 * (Real.log p / p ^ 2) - (R : ℝ) ^ 2 / 2 * (Real.log p / p) =
        ((S : ℝ) * R * (R - p) / p - (R : ℝ) ^ 3 / (3 * p ^ 2) - (R : ℝ) ^ 2 / (2 * p)) *
          Real.log p := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h13 hlogp
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    ← mul_sum] at hsum
  have hθ : ∑ p ∈ P, Real.log p < 3 / 2 * R :=
    ELEM.Primes.sum_log_lt_three_halves_mul hPR (by omega)
  have hB : ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2 < 2 / 3 :=
    ELEM.Primes.sum_log_div_sq_lt_two_thirds hPp
  have hI : 0 ≤ ∑ p ∈ P, Real.log p / p := sum_nonneg fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPp p hp).one_lt.le)) (Nat.cast_nonneg _)
  set I := ∑ p ∈ P, Real.log p / p
  set θ := ∑ p ∈ P, Real.log p
  set B := ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2
  have t1 : (S : ℝ) * R * θ ≤ S * R * (3 / 2 * R) :=
    mul_le_mul_of_nonneg_left hθ.le (by positivity)
  have t2 : (R : ℝ) ^ 3 / 3 * B ≤ (R : ℝ) ^ 3 / 3 * (2 / 3) :=
    mul_le_mul_of_nonneg_left hB.le (by positivity)
  have t3 : (R : ℝ) ^ 3 ≤ (R : ℝ) ^ 2 * (13 * S) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hS13) (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have e : (I - I / (2 * S) - 79 / 18) * ((R : ℝ) ^ 2 * S) =
      S * R ^ 2 * I - (R : ℝ) ^ 2 / 2 * I - 79 / 18 * R ^ 2 * S := by
    field_simp
  rw [e]
  nlinarith
end ELEM.Divisibility
namespace ELEM
theorem divisibilityBound : DivisibilityBound := by
  classical
  intro q R hq _ _ hq4 _ f hf
  unfold Iinert
  exact Divisibility.divisibility_of_subset q R hq hq4 f hf _ (filter_subset _ _)
    fun p hp => (mem_filter.mp hp).2
end ELEM
end

section
open Real
namespace ELEM.Endpoint
theorem le_sqrt_of_large {q : ℝ} (hq : 32768 ≤ q) : (181 : ℝ) ≤ √q :=
  (Real.le_sqrt (by norm_num) (by linarith)).2 (by norm_num; linarith)
theorem two_log_181_lt : 2 * Real.log 181 < 15 * Real.log 2 := by
  have h : Real.log ((181 : ℝ) ^ 2) < Real.log ((2 : ℝ) ^ 15) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h
theorem log_le_of_large {q : ℝ} (hq : 32768 ≤ q) : Real.log q ≤ 7 / 120 * √q := by
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hu0 : 0 < √q := by linarith
  have hlog : Real.log q = 2 * Real.log √q := by
    rw [Real.log_sqrt (by linarith)]; ring
  have hdiv : Real.log (√q / 181) = Real.log √q - Real.log 181 :=
    Real.log_div hu0.ne' (by norm_num)
  have hle : Real.log (√q / 181) ≤ √q / 181 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h181 := two_log_181_lt
  have h2 := Real.log_two_lt_d9
  rw [hlog]
  linarith
theorem sqrt_le_div_of_large {q : ℝ} (hq : 32768 ≤ q) : √q ≤ q / 181 := by
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hsq : √q * √q = q := Real.mul_self_sqrt (by linarith)
  rw [le_div_iff₀ (by norm_num)]
  nlinarith
theorem log_le_mul_of_large {q : ℝ} (hq : 32768 ≤ q) : Real.log q ≤ 7 / 21720 * q := by
  have h1 := log_le_of_large hq
  have h2 := sqrt_le_div_of_large hq
  linarith
end ELEM.Endpoint
end

section
open Real
namespace ELEM.Endpoint
theorem final_comparison :
    121 / 18 + 25 / 24 * (0.6931471808 : ℝ) + 1 / 25 < 1783 / 2400 * (15 * 0.6931471803) := by
  norm_num
theorem companion_comparison :
    (846 / 575 : ℚ) < 143 / 96 ∧ (143 / 96 : ℚ) - 846 / 575 = 1009 / 55200 := by
  norm_num
theorem endpoint : ELEM.Endpoint := by
  intro q R S A I Sp Y hq hR4 hR5 hS hS0 hSp hA hA1 hA2 hSpb hY1 hY2
  have hq0 : 0 < q := by linarith
  have hq4 : 0 < q ^ 4 := by positivity
  have hR0 : 0 < R := lt_trans hq4 hR4
  have hL : 15 * Real.log 2 ≤ Real.log q := by
    have h : Real.log ((2 : ℝ) ^ 15) ≤ Real.log q :=
      (Real.log_le_log_iff (by norm_num) hq0).2 (by norm_num; linarith)
    rwa [Real.log_pow] at h
  have hl2lo := Real.log_two_gt_d9
  have hl2hi := Real.log_two_lt_d9
  have hL0 : 0 ≤ Real.log q := by linarith
  have hx4 : 4 * Real.log q < Real.log R := by
    have h := Real.log_lt_log hq4 hR4
    rwa [Real.log_pow] at h
  have hx5 : Real.log R ≤ 5 * Real.log q := by
    have h := (Real.log_le_log_iff hR0 (by positivity)).2 hR5
    rwa [Real.log_pow] at h
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hu0 : 0 < √q := by linarith
  have hLu : Real.log q ≤ 7 / 120 * √q := log_le_of_large hq
  have hLq : Real.log q ≤ 7 / 21720 * q := log_le_mul_of_large hq
  have hxq : Real.log R ≤ q := by linarith
  have hq1000 : 1000 * q ≤ q ^ 4 := by
    have h3 : (1000 : ℝ) ≤ q ^ 3 := by
      have : (32768 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
      linarith
    have : q ^ 4 = q * q ^ 3 := by ring
    rw [this]
    nlinarith
  have hRq : 1000 * q < R := lt_of_le_of_lt hq1000 hR4
  set v : ℝ := 4 / (5 * √q) with hv
  have hv0 : 0 < v := by positivity
  have hvL : v * Real.log q ≤ 7 / 150 := by
    have h : v * Real.log q ≤ v * (7 / 120 * √q) := mul_le_mul_of_nonneg_left hLu hv0.le
    have e : v * (7 / 120 * √q) = 7 / 150 := by
      rw [hv]; field_simp; ring
    linarith
  have hquad : v * Real.log R ^ 2 ≤ 21 / 50 * Real.log R - 14 / 15 * Real.log q := by
    have hd : 0 ≤ Real.log R - 4 * Real.log q := by linarith
    have hs : v * (Real.log R + 4 * Real.log q) ≤ 21 / 50 := by
      have : v * (Real.log R + 4 * Real.log q) ≤ v * (9 * Real.log q) :=
        mul_le_mul_of_nonneg_left (by linarith) hv0.le
      linarith
    have p1 := mul_le_mul_of_nonneg_left hs hd
    have p2 := mul_le_mul_of_nonneg_left hvL hL0
    have e : v * Real.log R ^ 2 =
        (Real.log R - 4 * Real.log q) * (v * (Real.log R + 4 * Real.log q)) +
          16 * (Real.log q * (v * Real.log q)) := by ring
    rw [e]
    linarith
  have hE1 : 4 * (Real.log q + 1) / q ≤ 1 / 100 := by
    rw [div_le_iff₀ hq0]; linarith
  have hE2 : Real.log q / q ≤ 1 / 100 := by
    rw [div_le_iff₀ hq0]; linarith
  have hE3 : 6 * Real.log R / R ≤ 1 / 100 := by
    rw [div_le_iff₀ hR0]; linarith
  have hLq0 : 0 ≤ Real.log q / q := div_nonneg hL0 hq0.le
  have hI : I < Real.log R + 3 / 2 := by linarith
  have hE4 : I / (2 * S) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hfin := final_comparison
  linarith
end ELEM.Endpoint
end

section

end

section
namespace ELEM.Sieve
open CN1.Finite
def sievePrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def survivors : List ℕ := [11, 19, 43, 67, 163]
def HasRoot (p c : ℕ) : Prop := ∃ y, y < p ∧ (y ^ 2 + (p - 1) * y + c) % p = 0
instance (p c : ℕ) : Decidable (HasRoot p c) :=
  inferInstanceAs (Decidable (∃ y, y < p ∧ (y ^ 2 + (p - 1) * y + c) % p = 0))
def SieveHit (P : List ℕ) (q : ℕ) : Prop := ∃ p ∈ P, 4 * p < q ∧ HasRoot p ((q + 1) / 4)
instance (P : List ℕ) (q : ℕ) : Decidable (SieveHit P q) :=
  inferInstanceAs (Decidable (∃ p ∈ P, 4 * p < q ∧ HasRoot p ((q + 1) / 4)))
def SieveOK (S P : List ℕ) (q : ℕ) : Prop := q ∈ S ∨ SieveHit P q
instance (S P : List ℕ) (q : ℕ) : Decidable (SieveOK S P q) :=
  inferInstanceAs (Decidable (q ∈ S ∨ SieveHit P q))
theorem prime_of_mem_sievePrimes {p : ℕ} (hp : p ∈ sievePrimes) : p.Prime := by
  simp only [sievePrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
theorem isWitness_of_sieveHit {m : ℕ} (hm : m % 4 = 3) (h : SieveHit sievePrimes m) :
    ∃ p y, IsWitness m p y := by
  obtain ⟨p, hpP, hpq, y, hyp, hroot⟩ := h
  have hp := prime_of_mem_sievePrimes hpP
  have ht : tOf m = 1 := tOf_of_mod m hm
  have hc : cOf m = (m + 1) / 4 := by simp [cOf, hm]
  have hd : dOf m = m := dOf_of_mod m hm
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hsplit : y ^ 2 + (p - 1) * y + (m + 1) / 4 = (y ^ 2 + (m + 1) / 4 - y) + p * y := by
    have : (p - 1) * y = p * y - y := Nat.sub_one_mul p y
    have : y ≤ p * y := Nat.le_mul_of_pos_left y hp1
    omega
  refine ⟨p, y, hp, ?_, ?_, ?_, ?_⟩
  · rw [ht, hc]; omega
  · rw [ht, hc, one_mul]
    have h0 : p ∣ y ^ 2 + (p - 1) * y + (m + 1) / 4 := Nat.dvd_of_mod_eq_zero hroot
    rw [hsplit] at h0
    exact (Nat.dvd_add_left (Dvd.intro y rfl)).mp h0
  · rw [hd]; omega
  · rw [hc]; omega
theorem isWitness_two_of_mod_four_ne_three {m : ℕ} (h : m % 4 ≠ 3) (hm : 3 ≤ m) :
    IsWitness m 2 (m % 2) := by
  have ht : tOf m = 0 := by simp [tOf, h]
  have hc : cOf m = m := by simp [cOf, h]
  have hd : dOf m = 4 * m := by simp [dOf, h]
  refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
  · rw [ht, zero_mul]; exact Nat.zero_le _
  · rw [ht, hc, zero_mul, Nat.sub_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;> rw [h2] <;> omega
  · rw [hd]; omega
  · rw [hc]; omega
theorem isWitness_two_of_mod_eight_eq_seven {m : ℕ} (h : m % 8 = 7) (hm : 15 ≤ m) :
    IsWitness m 2 0 := by
  have h4 : m % 4 = 3 := by omega
  have ht : tOf m = 1 := tOf_of_mod m h4
  have hc : cOf m = (m + 1) / 4 := by simp [cOf, h4]
  have hd : dOf m = m := dOf_of_mod m h4
  refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
  · rw [ht, mul_zero]; exact Nat.zero_le _
  · rw [ht, hc, mul_zero, Nat.sub_zero]; omega
  · rw [hd]; omega
  · rw [hc]; omega
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk0 : ∀ k < 512, 8 < 8 * (512 * 0 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 0 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk1 : ∀ k < 512, 8 < 8 * (512 * 1 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 1 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk2 : ∀ k < 512, 8 < 8 * (512 * 2 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 2 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk3 : ∀ k < 512, 8 < 8 * (512 * 3 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 3 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk4 : ∀ k < 512, 8 < 8 * (512 * 4 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 4 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk5 : ∀ k < 512, 8 < 8 * (512 * 5 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 5 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk6 : ∀ k < 512, 8 < 8 * (512 * 6 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 6 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieveOK_chunk7 : ∀ k < 512, 8 < 8 * (512 * 7 + k) + 3 →
    SieveOK survivors sievePrimes (8 * (512 * 7 + k) + 3) := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
open CN1.Finite
theorem sieveOK_of_lt {q : ℕ} (hq : q < 32768) (h3 : q % 8 = 3) (h8 : 8 < q) :
    SieveOK survivors sievePrimes q := by
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 512 ∧ q = 8 * (512 * i + j) + 3 :=
    ⟨q / 8 / 512, q / 8 % 512, Nat.mod_lt _ (by norm_num), by omega⟩
  have hi : i < 8 := by omega
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sieveOK_chunk0 j hj h8
  · exact sieveOK_chunk1 j hj h8
  · exact sieveOK_chunk2 j hj h8
  · exact sieveOK_chunk3 j hj h8
  · exact sieveOK_chunk4 j hj h8
  · exact sieveOK_chunk5 j hj h8
  · exact sieveOK_chunk6 j hj h8
  · exact sieveOK_chunk7 j hj h8
theorem exists_isWitness_of_dOf_lt {m : ℕ} (hm0 : m ≠ 0) (hd : dOf m < 32768)
    (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : ∃ p y, IsWitness m p y := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnine
  obtain ⟨h1, h2, h3, h7, h11, h19, h43, h67, h163⟩ := hnine
  by_cases h4 : m % 4 = 3
  · rw [dOf_of_mod m h4] at hd
    by_cases h87 : m % 8 = 7
    · exact ⟨2, 0, isWitness_two_of_mod_eight_eq_seven h87 (by omega)⟩
    · rcases sieveOK_of_lt hd (by omega) (by omega) with hs | hs
      · simp only [survivors, List.mem_cons, List.not_mem_nil, or_false] at hs
        omega
      · exact isWitness_of_sieveHit h4 hs
  · exact ⟨2, m % 2, isWitness_two_of_mod_four_ne_three h4 (by omega)⟩
theorem not_sieveHit_survivors : ∀ q ∈ survivors, ¬ SieveHit sievePrimes q := by
  decide +kernel
end ELEM.Sieve
end

section
namespace ELEM.Sieve
theorem sieve : ELEM.Sieve := by
  intro k hk h8
  rcases sieveOK_of_lt (q := 8 * k + 3) (by omega) (by omega) h8 with hs | hs
  · left
    simp only [survivors, List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hs
  · right
    exact hs
end ELEM.Sieve
end

section
open NumberField
namespace CN1
theorem classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) :=
  ELEM.classNumber_eq_one_iff_of_hyps ELEM.Primes.lemmaTwoA ELEM.Count.splitBound
    ELEM.Count.auxPrime ELEM.nonvanishing ELEM.Size.sizeBound ELEM.divisibilityBound ELEM.Endpoint.endpoint
    ELEM.Sieve.sieve K hK m hm hsq
end CN1
end

section Bridge
open Polynomial NumberField

theorem OMABridge_monic (d : ℤ) : (X ^ 2 - C (d : ℚ) : ℚ[X]).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by norm_num)

theorem OMABridge_deg (d : ℤ) : (X ^ 2 - C (d : ℚ) : ℚ[X]).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

theorem OMABridge_irred (d : ℤ) (hd : d < 0) : Irreducible (X ^ 2 - C (d : ℚ) : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [OMABridge_deg]; simp
  · intro x hx
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    have h1 : x ^ 2 = (d : ℚ) := sub_eq_zero.mp hx
    have h2 : (d : ℚ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg x]

end Bridge

namespace OMA.PrimeRow
open CN1.Finite CN1.Foundations NumberField Polynomial Ideal

/-- A root modulo a smaller prime supplies a composite entry in the long row. -/
lemma inert_of_row {p : ℕ} (row : ∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime)
    {q : ℕ} (hq : q.Prime) (hqp : q < p) : ELEM.IsInert p q := by
  have : NeZero q := ⟨hq.ne_zero⟩
  intro z hz
  let t := (-z).val
  have ht : t < q := ZMod.val_lt _
  have hcast : (t : ZMod q) = -z := ZMod.natCast_zmod_val _
  have hdiv : q ∣ t * (t + 1) + p := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    rw [hcast]
    linear_combination hz)
  exact Nat.not_prime_of_dvd_of_lt hdiv hq.two_le (by omega) (row t (by omega))

/-- A composite discriminant has a small ramified prime, excluded by the row. -/
lemma prime_discriminant {p m : ℕ} (hp : 41 < p) (hm : m + 1 = 4*p)
    (inert : ∀ q : ℕ, q.Prime → q < p → ELEM.IsInert p q) : m.Prime := by
  by_contra h
  have hfac := Nat.minFac_prime (show m ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (show 0 < m by omega) h
  have hsmall : m.minFac < p := by
    by_contra! hge
    nlinarith [Nat.mul_self_le_mul_self hge, Nat.mul_le_mul_right p (show 4 ≤ p by omega)]
  have hodd : m.minFac % 2 = 1 := by
    rcases hfac.eq_two_or_odd with he | he
    · have hd := Nat.minFac_dvd m
      rw [he] at hd
      omega
    · exact he
  have hsplit := ELEM.not_isInert_of_dvd_q hfac hodd (show m % 4 = 3 by omega) (Nat.minFac_dvd m)
  have hc : ELEM.cq m = p := by unfold ELEM.cq; omega
  exact hsplit (hc ▸ inert _ hfac hsmall)

/-- By Minkowski, the only possible obstruction is a small prime ideal of prime
norm. Its residue field would contain a root of the row polynomial. -/
lemma class_number_one {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {p m : ℕ} (hp : 41 < p) (hm : m + 1 = 4*p) (hsq : Squarefree m)
    {α : K} (hα : α ^ 2 = -(m : K))
    (inert : ∀ q : ℕ, q.Prime → q < p → ELEM.IsInert p q) : classNumber K = 1 := by
  have hm4 : m % 4 = 3 := by omega
  have hdisc : |discr K| ≤ (m : ℤ) := by
    rw [discr_eq hα hK hsq, abs_neg, Nat.abs_cast, disc_eq_dOf, dOf_of_mod m hm4]
  obtain ⟨θ, hθ⟩ := exists_theta hm4 α hα
  have ht : tOf m = 1 := tOf_of_mod m hm4
  have hc : cOf m = p := by simp only [cOf, hm4, if_true]; omega
  rw [NumberField.classNumber_eq_one_iff]
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun I hI hle ↦ ?_
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have : (I : Ideal (𝓞 K)).IsMaximal := hI.isMaximal hI0
  have hbound := le_two_thirds_sqrt_of_le_minkowski hK hdisc hle
  obtain ⟨q, hq, -, hcases⟩ := absNorm_maximal_cases hK (I : Ideal (𝓞 K))
  rcases hcases with hN | ⟨-, hspan⟩
  · exfalso
    rw [hN] at hbound
    have hqp : q < p := nat_lt_of_le_two_thirds_sqrt hbound (by nlinarith [Nat.mul_le_mul_left p (show 16 ≤ p by omega)])
    apply not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN
    intro z hz
    apply inert q hq hqp z
    rw [ht, hc] at hz
    push_cast at hz
    linear_combination hz
  · rw [hspan]
    exact ⟨⟨_, rfl⟩⟩

lemma bad_entry {p : ℕ} (hp : 41 < p) : ∃ t : ℕ, t + 1 < p ∧ ¬ (t*(t+1)+p).Prime := by
  by_contra! row
  let m := 4*p-1
  have hm : m + 1 = 4*p := by dsimp [m]; omega
  have hinert := fun q (hq : q.Prime) (hqp : q < p) => inert_of_row row hq hqp
  have hsq := (prime_discriminant hp hm hinert).squarefree
  let d : ℤ := -(m : ℤ)
  have hd : d < 0 := by dsimp [d]; omega
  let f : ℚ[X] := X ^ 2 - C (d : ℚ)
  let : Fact (Irreducible f) := ⟨OMABridge_irred d hd⟩
  let K := AdjoinRoot f
  have hK : Module.finrank ℚ K = 2 := by
    rw [(AdjoinRoot.powerBasis' (OMABridge_monic d)).finrank]
    exact OMABridge_deg d
  have hα : (AdjoinRoot.root f) ^ 2 = -(m : K) := by
    have h := AdjoinRoot.eval₂_root f
    change eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) (X ^ 2 - C (d : ℚ)) = 0 at h
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    rw [h, map_intCast]
    simp [d, K]
  have hclass := class_number_one hK hp hm hsq hα hinert
  have hex := (CN1.classNumber_eq_one_iff K hK m hsq ⟨_, hα⟩).mp hclass
  simp only [Finset.mem_insert, Finset.mem_singleton] at hex
  omega

lemma prime_size (n : ℕ) (hn : 13 < n) : Nat.nth Nat.Prime (n - 1) ≤ 3 * n ^ 2 := by
  let m := 3 * n ^ 2
  have hn' : (14 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 1 < m := by dsimp [m]; nlinarith
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ((m : ℝ) + 1) ≤ n + 2 := by
    have harg : (m : ℝ) + 1 ≤ (2 * (n : ℝ)) ^ 2 := by
      dsimp [m]; push_cast; nlinarith
    have h := Real.log_le_log (by positivity) harg
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h
    have h₂ := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / 2 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h₂
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hlogm : Real.log m ≤ n + 2 := (Real.log_le_log (by positivity) (by linarith : (m : ℝ) ≤ m + 1)).trans hlog
  have hπ := (div_le_iff₀ (Real.log_pos hm')).mp (Chebyshev.pi_ge m)
  have hc : n ≤ Nat.primeCounting m := by
    by_contra! h
    have hh : (Nat.primeCounting m : ℝ) ≤ n := by exact_mod_cast h.le
    have hz := mul_le_mul hh hlogm (Real.log_pos hm').le (by positivity)
    have hl : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hw := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    dsimp only [m] at hw hπ hlog hz
    push_cast at hw hπ hlog hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg n)]
  have hlt : n - 1 < Nat.count Nat.Prime (m + 1) := by
    change n - 1 < Nat.primeCounting m
    omega
  exact Nat.le_of_lt_succ ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp hlt)

lemma shorten {p n : ℕ} (hp : 41 < p) (hpn : p ≤ 3 * n ^ 2)
    (hw : ∃ x : ℕ, x + 1 < p ∧ ¬ (x * (x + 1) + p).Prime) :
    ∃ t < n, ¬ (t * (t + 1) + p).Prime := by
  let t := Nat.find hw
  obtain ⟨htp, hbad⟩ := Nat.find_spec hw
  change t + 1 < p at htp
  change ¬ (t * (t + 1) + p).Prime at hbad
  let v := t * (t + 1) + p
  let q := v.minFac
  have hq2 : 2 ≤ q := (Nat.minFac_prime (show v ≠ 1 by dsimp [v]; omega)).two_le
  have hs : q ^ 2 ≤ v := Nat.minFac_sq_le_self (by dsimp [v]; omega) hbad
  have hqp : q < p := by
    dsimp only [v] at hs
    by_contra! hh
    nlinarith [Nat.mul_self_le_mul_self hh,
      Nat.mul_le_mul (show t ≤ p - 2 by omega) (show t + 1 ≤ p - 1 by omega),
      show p - 2 + 2 = p by omega, show p - 1 + 1 = p by omega]
  let r := t % q
  let s := q - 1 - r
  have hr : r < q := Nat.mod_lt _ (by omega)
  have hsum : s + 1 + r = q := by dsimp [s]; omega
  have hz : (t : ZMod q) * (t + 1) + p = 0 := by
    have hv := (ZMod.natCast_eq_zero_iff v q).mpr (Nat.minFac_dvd v)
    simpa [v] using hv
  have hrz : (r : ZMod q) = t := ZMod.natCast_mod t q
  have hsz : (s : ZMod q) + 1 + r = 0 := by
    exact_mod_cast (show ((s + 1 + r : ℕ) : ZMod q) = 0 by rw [hsum]; simp)
  have hsmall (b : ℕ) (hb : b < q) (hbz : (b : ZMod q) * (b + 1) + p = 0) : t ≤ b := by
    have hd : q ∣ b * (b + 1) + p := (ZMod.natCast_eq_zero_iff _ q).mp (by simpa using hbz)
    have hnp := Nat.not_prime_of_dvd_of_lt hd hq2 (show q < b * (b + 1) + p by omega)
    by_contra! h
    exact Nat.find_min hw h ⟨by omega, hnp⟩
  have htr := hsmall r hr (by rwa [hrz])
  have hts := hsmall s (by omega) (by
    rw [← hrz] at hz
    linear_combination hz + (s - (r : ZMod q)) * hsz)
  have hq : 2*t+1 ≤ q := by omega
  have hh := Nat.mul_self_le_mul_self hq
  refine ⟨t, ?_, hbad⟩
  by_contra! hn
  dsimp [v] at hs
  nlinarith [Nat.mul_self_le_mul_self hn]

end OMA.PrimeRow

open OMA.PrimeRow in
theorem OMA.solution : type_of% @OeisA117531.conjecture := by
  intro n hn
  let p := Nat.nth Nat.Prime (n - 1)
  have h41 : Nat.nth Nat.Prime 12 = 41 := by
    have hc : Nat.count Nat.Prime 41 = 12 := by decide
    rw [← hc]
    exact Nat.nth_count (by decide)
  have hlarge : 41 < p := h41 ▸ Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 12 < n - 1 by omega)
  have hw := bad_entry hlarge
  obtain ⟨t, ht, hbad⟩ := shorten hlarge (prime_size n hn) hw
  have ht' : (t + 1)^2 - (t+1) = t*(t+1) := by
    rw [pow_two, Nat.add_mul, one_mul, Nat.add_sub_cancel]
  unfold OeisA117531.a
  change ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + p).Prime).card < n
  have hsub : ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + p).Prime) ⊂ Finset.Icc 1 n := by
    apply Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
    exact ⟨t+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp [ht', hbad]⟩
  simpa using Finset.card_lt_card hsub
