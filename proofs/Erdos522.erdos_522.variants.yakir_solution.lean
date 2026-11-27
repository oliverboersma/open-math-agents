import FormalConjectures.ErdosProblems.«522»
import Mathlib.Probability.HasLaw

import Mathlib
/-! Yakir’s quantitative Kac estimate. The sign-concentration proof is adapted from
Sebastien Kawada, chreia/erdos-522 at c261d2e4754f, under Apache-2.0.
Copyright (c) 2026 Sebastien Kawada. Modified for the project Lean pin. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace Fluctuations
noncomputable section
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
def Prob (μ : Measure Ω) (s : Set Ω) : ℝ := (μ s).toReal
def randomPolynomial (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.monomial j (ξ j ω : ℂ)
def zeroCount (ξ : ℕ → Ω → ℝ) (n : ℕ) (r : ℝ) (ω : Ω) : ℕ :=
  ((randomPolynomial ξ n ω).roots.filter (fun z => ‖z‖ ≤ r)).card
def discrepancy (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (zeroCount ξ n 1 ω : ℝ) - (n : ℝ) / 2
def IsIID (μ : Measure Ω) (ξ : ℕ → Ω → ℝ) : Prop :=
  (∀ j, AEMeasurable (ξ j) μ) ∧ iIndepFun ξ μ ∧
  ∀ j, IdentDistrib (ξ j) (ξ 0) μ μ
def rademacherLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)
def IsRademacherSequence (μ : Measure Ω) (ξ : ℕ → Ω → ℝ) : Prop :=
  IsIID μ ξ ∧ Measure.map (ξ 0) μ = rademacherLaw
def sineKernel (u : ℝ) : ℝ := Real.sinc (u / 2)
end
end Fluctuations
end

section
open Finset
open scoped BigOperators FinsetFamily
namespace Fluctuations.SarkozySzemeredi
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem centralBinom_square_bound (n : ℕ) :
    (n.centralBinom : ℝ) ^ 2 * (n + 1) ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hr : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hfac : 4 * (2 * (n : ℝ) + 1)^2 * ((n : ℝ) + 2) ≤
        16 * ((n : ℝ) + 1)^3 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfac (sq_nonneg (n.centralBinom : ℝ))
    have hi := mul_le_mul_of_nonneg_left ih (show 0 ≤ 16 * ((n : ℝ) + 1)^2 by positivity)
    have hr2 := congrArg (fun t : ℝ => t^2) hr
    have hcancel : ((n : ℝ) + 1)^2 * (((n + 1).centralBinom : ℝ)^2 * ((n : ℝ)+2)) ≤
        ((n : ℝ) + 1)^2 * (16 * 16^n) := by
      nlinarith
    have h := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn1)).mp hcancel
    convert! h using 1 <;> push_cast <;> ring
theorem middle_choose_square_bound (n : ℕ) :
    ((n.choose (n / 2) : ℕ) : ℝ)^2 * (n + 1) ≤ 2 * (4 : ℝ)^n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := centralBinom_square_bound m
    have hc : ((2*m).choose (2*m/2) : ℝ) = (m.centralBinom : ℝ) := by
      simp [Nat.centralBinom_eq_two_mul_choose]
    rw [hc, pow_mul]
    norm_num only [show (4 : ℝ)^2 = 16 by norm_num]
    push_cast
    nlinarith [sq_nonneg (m.centralBinom : ℝ)]
  · have h := centralBinom_square_bound m
    have hc : (2*m+1).choose ((2*m+1)/2) ≤ 2*m.centralBinom := by
      rw [show (2*m+1)/2 = m by omega]
      by_cases hm : m = 0
      · simp [hm]
      · rw [Nat.choose_succ_left _ _ (Nat.pos_of_ne_zero hm)]
        have h1 := Nat.choose_le_centralBinom (m-1) m
        have h2 := Nat.choose_le_centralBinom m m
        omega
    have hcr : ((2*m+1).choose ((2*m+1)/2) : ℝ) ≤ 2*(m.centralBinom : ℝ) := by
      exact_mod_cast hc
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (2*m+1).choose ((2*m+1)/2)) hcr
    have hmul := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ 2*(m:ℝ)+2 by positivity)
    rw [show (4 : ℝ)^(2*m+1) = 16^m*4 by rw [pow_add, pow_mul]; norm_num]
    push_cast
    nlinarith
open MeasureTheory
open scoped ENNReal
end Fluctuations.SarkozySzemeredi
end

section
noncomputable section
open scoped BigOperators
open MeasureTheory Polynomial
namespace Fluctuations
def coefficientPolynomial {R : Type*} [Semiring R] (n : ℕ) (a : Fin (n + 1) → R) :
    Polynomial R := ∑ j : Fin (n + 1), Polynomial.monomial j.val (a j)
theorem coefficientPolynomial_natDegree_le {R : Type*} [Semiring R]
    (n : ℕ) (a : Fin (n + 1) → R) : (coefficientPolynomial n a).natDegree ≤ n := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le (a j)).trans (Nat.le_of_lt_succ j.isLt)
theorem map_coefficientPolynomial {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (n : ℕ) (a : Fin (n + 1) → R) :
    (coefficientPolynomial n a).map φ = coefficientPolynomial n (fun j => φ (a j)) := by
  simp only [coefficientPolynomial, Polynomial.map_sum, Polynomial.map_monomial]
theorem randomPolynomial_eq_map_coefficientPolynomial {Ω : Type*}
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomPolynomial ξ n ω =
      (coefficientPolynomial n (fun j => ξ j.val ω)).map (algebraMap ℝ ℂ) := by
  rw [map_coefficientPolynomial, coefficientPolynomial]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => Polynomial.monomial j (ξ j ω : ℂ)) (n + 1)).symm
end Fluctuations
end
end

section
open Polynomial
namespace Polynomial
noncomputable section
theorem Splits.roots_reverse_filter {K : Type*} [Field K] [DecidableEq K] (f : Polynomial K)
    (hf : f.Splits) :
    f.reverse.roots = (f.roots.filter (fun z => z ≠ 0)).map (fun z => z⁻¹) := by
  classical
  induction hf using Submonoid.closure_induction with
  | mem p hp =>
    obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp
    · simp
    · have hr : (X + C a : Polynomial K).reverse = 1 + C a * X := by
        simp only [reverse, natDegree_X_add_C, reflect_add, reflect_one_X,
          reflect_C, pow_one]
      rw [hr]
      by_cases ha : a = 0
      · simp [ha]
      · have he : (1 + C a * X : Polynomial K) = C a * (X - C (-(a⁻¹))) := by
          rw [mul_sub, ← C_mul]
          simp [ha]
          ring
        rw [he, roots_C_mul _ ha]
        simp [Multiset.filter_singleton, ha]
  | one =>
    rw [show (1 : K[X]) = C 1 by simp, reverse_C]
    simp
  | mul f g _ _ hf hg =>
    by_cases hf0 : f = 0
    · simp [hf0]
    by_cases hg0 : g = 0
    · simp [hg0]
    have hfr : f.reverse ≠ 0 := fun h => hf0 (reverse_eq_zero.mp h)
    have hgr : g.reverse ≠ 0 := fun h => hg0 (reverse_eq_zero.mp h)
    rw [reverse_mul_of_domain, roots_mul (mul_ne_zero hfr hgr),
      roots_mul (mul_ne_zero hf0 hg0), Multiset.filter_add, Multiset.map_add, hf, hg]
end
end Polynomial
end

section
open Polynomial
open scoped BigOperators
namespace Fluctuations
noncomputable section
theorem coefficientPolynomial_coeff_fin {R : Type*} [Semiring R]
    (n : ℕ) (a : Fin (n + 1) → R) (j : Fin (n + 1)) :
    (coefficientPolynomial n a).coeff j.val = a j := by
  classical
  simp [coefficientPolynomial, Polynomial.coeff_monomial,
    ← Fin.ext_iff]
theorem reflect_coefficientPolynomial {R : Type*} [Semiring R]
    (n : ℕ) (a : Fin (n + 1) → R) :
    (coefficientPolynomial n a).reflect n = coefficientPolynomial n (fun j => a j.rev) := by
  ext k
  rw [Polynomial.coeff_reflect]
  by_cases hk : k ≤ n
  · rw [Polynomial.revAt_le hk]
    let j : Fin (n + 1) := ⟨k, by omega⟩
    have hrev : j.rev.val = n - k := by simp [j]
    rw [← hrev, coefficientPolynomial_coeff_fin]
    change _ = (coefficientPolynomial n (fun i => a i.rev)).coeff j.val
    rw [coefficientPolynomial_coeff_fin]
  · have hnk : n < k := by omega
    rw [Polynomial.revAt_eq_self_of_lt hnk,
      Polynomial.coeff_eq_zero_of_natDegree_lt ((coefficientPolynomial_natDegree_le n a).trans_lt hnk),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((coefficientPolynomial_natDegree_le n (fun i => a i.rev)).trans_lt hnk)]
theorem coefficientPolynomial_natDegree_eq {R : Type*} [Semiring R]
    (n : ℕ) (a : Fin (n + 1) → R) (hn : a (Fin.last n) ≠ 0) :
    (coefficientPolynomial n a).natDegree = n := by
  apply le_antisymm (coefficientPolynomial_natDegree_le n a)
  apply Polynomial.le_natDegree_of_ne_zero
  have hc : (coefficientPolynomial n a).coeff n = a (Fin.last n) :=
    coefficientPolynomial_coeff_fin n a (Fin.last n)
  rwa [hc]
theorem reverse_coefficientPolynomial {R : Type*} [Semiring R]
    (n : ℕ) (a : Fin (n + 1) → R) (hn : a (Fin.last n) ≠ 0) :
    (coefficientPolynomial n a).reverse = coefficientPolynomial n (fun j => a j.rev) := by
  rw [Polynomial.reverse, coefficientPolynomial_natDegree_eq n a hn,
    reflect_coefficientPolynomial]
end
end Fluctuations
end

section
open Complex Metric Polynomial Set
namespace Erdos522.PolynomialCircle
noncomputable section
theorem logDeriv_eq_sum (p : ℂ[X]) {z : ℂ} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      (p.roots.map fun a => (z - a)⁻¹).sum := by
  simpa only [one_div] using
    (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz
theorem subInv_circleIntegrable {c a : ℂ} {R : ℝ}
    (ha : a ∉ sphere c |R|) :
    CircleIntegrable (fun z : ℂ => (z - a)⁻¹) c R := by
  exact circleIntegrable_sub_inv_iff.mpr (Or.inr ha)
theorem integral_subInv_inside {c a : ℂ} {R : ℝ} (ha : a ∈ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball ha
theorem integral_subInv_outside {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∉ closedBall c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  have hne : ∀ z ∈ closure (ball c R), z - a ≠ 0 := by
    intro z hz hza
    apply ha
    have : z = a := sub_eq_zero.mp hza
    subst z
    exact closure_ball_subset_closedBall hz
  exact ((differentiable_id.diffContOnCl.sub_const a).inv hne).circleIntegral_eq_zero hR
private theorem sum_subInv_circleIntegrable {roots : Multiset ℂ}
    {c : ℂ} {R : ℝ} (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    CircleIntegrable (fun z => (roots.map fun a => (z - a)⁻¹).sum) c R := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact circleIntegrable_const 0 c R
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail := ih (fun b hb => hroots b (Multiset.mem_cons_of_mem hb))
      apply (circleIntegrable_congr ?_).mpr (ha.add htail)
      intro z hz
      simp only [Multiset.map_cons, Multiset.sum_cons, Pi.add_apply]
theorem integral_sum_subInv {roots : Multiset ℂ} {c : ℂ} {R : ℝ}
    (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    (∮ z in C(c, R), (roots.map fun a => (z - a)⁻¹).sum) =
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail : ∀ b ∈ roots, b ∉ sphere c |R| :=
        fun b hb => hroots b (Multiset.mem_cons_of_mem hb)
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [circleIntegral.integral_add ha (sum_subInv_circleIntegrable htail), ih htail]
theorem integral_logDeriv_eq_sum {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (p.roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  have hroots : ∀ a ∈ p.roots, a ∉ sphere c |R| := by
    intro a haRoot haSphere
    rw [abs_of_nonneg hR] at haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  calc
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
        ∮ z in C(c, R), (p.roots.map fun a => (z - a)⁻¹).sum := by
      apply circleIntegral.integral_congr hR
      intro z hz
      exact logDeriv_eq_sum p (hboundary z hz)
    _ = _ := integral_sum_subInv hroots
end
end Erdos522.PolynomialCircle
open Complex Set
namespace Erdos522.PolynomialCircle
noncomputable section
end
end Erdos522.PolynomialCircle
open Complex Metric Polynomial Set
namespace Erdos522.PolynomialCircle
noncomputable section
noncomputable def rootsInDisc (p : ℂ[X]) (c : ℂ) (R : ℝ) : ℕ := by
  classical
  exact p.roots.countP fun a => a ∈ ball c R
theorem integral_subInv_outside_of_not_mem {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (haSphere : a ∉ sphere c R) (haBall : a ∉ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  apply integral_subInv_outside hR
  intro hclosed
  apply haSphere
  rw [mem_sphere]
  rw [mem_closedBall] at hclosed
  exact le_antisymm hclosed (not_lt.mp (haBall ∘ mem_ball.mpr))
theorem integral_logDeriv_eq_rootCount {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (rootsInDisc p c R : ℂ) * (2 * Real.pi * I) := by
  classical
  rw [integral_logDeriv_eq_sum hp hR hboundary]
  have hroot : ∀ a ∈ p.roots, a ∉ sphere c R := by
    intro a haRoot haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  have hsum : ∀ roots : Multiset ℂ,
      (∀ a ∈ roots, a ∉ sphere c R) →
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum =
        (roots.countP (fun a => a ∈ ball c R) : ℂ) * (2 * Real.pi * I) := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons a roots ih =>
        intro hnone
        have ha := hnone a (Multiset.mem_cons_self a roots)
        have htail : ∀ b ∈ roots, b ∉ sphere c R :=
          fun b hb => hnone b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih htail]
        by_cases hin : a ∈ ball c R
        · rw [if_pos hin, integral_subInv_inside hin]
          push_cast
          ring
        · rw [if_neg hin, integral_subInv_outside_of_not_mem hR ha hin]
          simp
  simpa only [rootsInDisc] using hsum p.roots hroot
theorem argumentPrinciple {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (2 * Real.pi * I)⁻¹ *
        ∮ z in C(c, R), p.derivative.eval z / p.eval z =
      (rootsInDisc p c R : ℂ) := by
  rw [integral_logDeriv_eq_rootCount hp hR hboundary]
  field_simp [Real.pi_ne_zero]
end
end Erdos522.PolynomialCircle
open Complex Metric Polynomial Set
namespace Erdos522.PolynomialCircle
noncomputable section
def affineHomotopy (f g : ℂ[X]) (t : ℝ) : ℂ[X] :=
  g + C (t : ℂ) * (f - g)
namespace affineHomotopy
@[simp]
theorem zero (f g : ℂ[X]) : affineHomotopy f g 0 = g := by
  simp [affineHomotopy]
@[simp]
theorem one (f g : ℂ[X]) : affineHomotopy f g 1 = f := by
  simp [affineHomotopy]
@[simp]
theorem eval (f g : ℂ[X]) (t : ℝ) (z : ℂ) :
    (affineHomotopy f g t).eval z =
      g.eval z + (t : ℂ) * (f.eval z - g.eval z) := by
  simp [affineHomotopy]
@[simp]
theorem derivative (f g : ℂ[X]) (t : ℝ) :
    (affineHomotopy f g t).derivative =
      affineHomotopy f.derivative g.derivative t := by
  simp [affineHomotopy]
end affineHomotopy
end
end Erdos522.PolynomialCircle
open Complex Metric Polynomial Set
namespace Erdos522.PolynomialCircle
noncomputable section
end
end Erdos522.PolynomialCircle
namespace Erdos522
noncomputable section
open scoped Classical
end
end Erdos522
end

section
open Complex Metric Polynomial Set
namespace Fluctuations.PolynomialCircle
open Erdos522.PolynomialCircle
noncomputable section
theorem rootsInDisc_eq_closedCount {p : Polynomial ℂ} (hp : p ≠ 0) {r : ℝ}
    (hboundary : ∀ z : ℂ, ‖z‖ = r → p.eval z ≠ 0) :
    rootsInDisc p 0 r = (p.roots.filter (fun z => ‖z‖ ≤ r)).card := by
  classical
  unfold rootsInDisc
  rw [Multiset.countP_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  have hne : ‖z‖ ≠ r := fun heq => hboundary z heq ((Polynomial.mem_roots hp).mp hz)
  simp only [Metric.mem_ball, dist_zero_right]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩
theorem argumentPrinciple_closed {p : Polynomial ℂ} (hp : p ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (hboundary : ∀ z : ℂ, ‖z‖ = r → p.eval z ≠ 0) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(0, r), p.derivative.eval z / p.eval z) =
      ((p.roots.filter (fun z => ‖z‖ ≤ r)).card : ℂ) := by
  have hb : ∀ z ∈ sphere (0 : ℂ) r, p.eval z ≠ 0 := by
    intro z hz
    exact hboundary z (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)
  rw [argumentPrinciple hp hr hb, rootsInDisc_eq_closedCount hp hboundary]
end
end Fluctuations.PolynomialCircle
namespace Fluctuations
noncomputable section
variable {Ω : Type*}
end
end Fluctuations
end

section
noncomputable section
open scoped BigOperators
namespace Polynomial
theorem card_roots_filter_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (P : R → Prop) [DecidablePred P] :
    (p.roots.filter P).card ≤ p.natDegree :=
  (Multiset.card_le_card (Multiset.filter_le P p.roots)).trans p.card_roots'
end Polynomial
namespace Fluctuations
variable {Ω : Type*}
theorem randomPolynomial_natDegree_le (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (randomPolynomial ξ n ω).natDegree ≤ n := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
theorem zeroCount_le (ξ : ℕ → Ω → ℝ) (n : ℕ) (r : ℝ) (ω : Ω) :
    zeroCount ξ n r ω ≤ n :=
  (Polynomial.card_roots_filter_le_natDegree _ _).trans
    (randomPolynomial_natDegree_le ξ n ω)
theorem abs_discrepancy_le (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |discrepancy ξ n ω| ≤ (n : ℝ) / 2 := by
  have hcount : (zeroCount ξ n 1 ω : ℝ) ≤ n := by
    exact_mod_cast zeroCount_le ξ n 1 ω
  have hnonneg : (0 : ℝ) ≤ zeroCount ξ n 1 ω := by positivity
  unfold discrepancy
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Fluctuations
end
end

section
open MeasureTheory ProbabilityTheory
namespace Fluctuations
noncomputable section
theorem iid_fin_map_eq_pi {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsIID μ ξ) (m : ℕ) (e : Fin m → ℕ) (he : Function.Injective e) :
    μ.map (fun ω j => ξ (e j) ω) = Measure.pi (fun _ : Fin m => μ.map (ξ 0)) := by
  have hind : iIndepFun (fun j : Fin m => ξ (e j)) μ :=
    iIndepFun.precomp he hξ.2.1
  rw [iIndepFun.map_fun_eq_pi_map (f := fun j : Fin m => ξ (e j))
    (fun j => hξ.1 (e j)) hind]
  congr 1
  funext j
  exact (hξ.2.2 (e j)).map_eq
end
end Fluctuations
end

section
open MeasureTheory ProbabilityTheory Polynomial
namespace Fluctuations
noncomputable section
def finiteCoefficientSequence (n k : ℕ) (a : Fin (n + 1) → ℝ) : ℝ :=
  if h : k < n + 1 then a ⟨k, h⟩ else 0
@[simp]
theorem finiteCoefficientSequence_fin (n : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → ℝ) : finiteCoefficientSequence n j.val a = a j := by
  simp [finiteCoefficientSequence, j.isLt]
theorem randomPolynomial_finiteCoefficientSequence (n : ℕ) (a : Fin (n + 1) → ℝ) :
    randomPolynomial (finiteCoefficientSequence n) n a =
      coefficientPolynomial n (fun j => (a j : ℂ)) := by
  rw [randomPolynomial_eq_map_coefficientPolynomial, map_coefficientPolynomial]
  simp only [finiteCoefficientSequence_fin]
  rfl
theorem discrepancy_finiteCoefficientSequence {Ω : Type*}
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    discrepancy (finiteCoefficientSequence n) n (fun j => ξ j.val ω) =
      discrepancy ξ n ω := by
  unfold discrepancy zeroCount
  rw [randomPolynomial_finiteCoefficientSequence,
    randomPolynomial_eq_map_coefficientPolynomial, map_coefficientPolynomial]
  rfl
end
end Fluctuations
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Fluctuations
noncomputable section
theorem rademacher_ae_all_values {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∀ᵐ ω ∂μ, ∀ j, ξ j ω = 1 ∨ ξ j ω = -1 := by
  apply ae_all_iff.mpr
  intro j
  have hm : μ.map (ξ j) = rademacherLaw := (hξ.1.2.2 j).map_eq.trans hξ.2
  have hs : ∀ᵐ x ∂rademacherLaw, x = 1 ∨ x = -1 := by
    simp [rademacherLaw]
  rw [← hm] at hs
  exact ae_of_ae_map (hξ.1.1 j) hs
end
end Fluctuations
end

section
open MeasureTheory ProbabilityTheory Polynomial Classical
open scoped ENNReal BigOperators
namespace Fluctuations.SignPolynomialDivisibility
noncomputable section
def signVectors (m : ℕ) : Finset (Fin m → ℝ) :=
  Fintype.piFinset (fun _ => {1, -1})
@[simp] theorem mem_signVectors {m : ℕ} (a : Fin m → ℝ) :
    a ∈ signVectors m ↔ ∀ j, a j = 1 ∨ a j = -1 := by
  simp [signVectors, Fintype.mem_piFinset]
@[simp] theorem card_signVectors (m : ℕ) :
    (signVectors m).card = 2 ^ m := by
  norm_num [signVectors, Fintype.card_piFinset]
theorem signVector_mass (m : ℕ) (a : Fin m → ℝ) (ha : a ∈ signVectors m) :
    (Measure.pi (fun _ : Fin m => rademacherLaw)) {a} = (2 : ℝ≥0∞)⁻¹ ^ m := by
  have : IsProbabilityMeasure rademacherLaw := ⟨by
    norm_num [rademacherLaw]
    exact ENNReal.inv_two_add_inv_two⟩
  rw [Measure.pi_singleton]
  have hcoord : ∀ j, rademacherLaw {a j} = (2 : ℝ≥0∞)⁻¹ := by
    intro j
    rcases (mem_signVectors a).mp ha j with hj | hj <;> norm_num [hj, rademacherLaw, Pi.single_apply]
  simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem signVector_subset_mass (m : ℕ) (s : Finset (Fin m → ℝ))
    (hs : s ⊆ signVectors m) :
    (Measure.pi (fun _ : Fin m => rademacherLaw)) s =
      (s.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
  rw [← sum_measure_singleton]
  calc
    _ = ∑ _a ∈ s, (2 : ℝ≥0∞)⁻¹ ^ m := by
      apply Finset.sum_congr rfl
      intro a ha
      exact signVector_mass m a (hs ha)
    _ = _ := by simp
theorem finite_sign_event_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ) (P : (Fin m → ℝ) → Prop) :
    μ {ω | P (fun j => ξ j.val ω)} =
      ((((signVectors m).filter P).card : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
  classical
  let v : Ω → Fin m → ℝ := fun ω j => ξ j.val ω
  let s := (signVectors m).filter P
  have hv : AEMeasurable v μ := aemeasurable_pi_lambda _ (fun j => hξ.1.1 j.val)
  have hae : {ω | P (v ω)} =ᵐ[μ] v ⁻¹' (s : Set (Fin m → ℝ)) := by
    filter_upwards [rademacher_ae_all_values μ ξ hξ] with ω hω
    change P (v ω) = (v ω ∈ s)
    simp only [s, Finset.mem_filter, mem_signVectors]
    exact propext ⟨fun h => ⟨fun j => hω j.val, h⟩, fun h => h.2⟩
  change μ {ω | P (v ω)} = _
  rw [measure_congr hae, ← Measure.map_apply_of_aemeasurable hv s.finite_toSet.measurableSet]
  have hmap : μ.map v = Measure.pi (fun _ : Fin m => rademacherLaw) := by
    rw [show v = (fun ω j => ξ (Fin.val j) ω) from rfl,
      iid_fin_map_eq_pi μ ξ hξ.1 m Fin.val Fin.val_injective, hξ.2]
  rw [hmap]
  exact signVector_subset_mass m s (Finset.filter_subset P (signVectors m))
end
end Fluctuations.SignPolynomialDivisibility
end

section
open Polynomial Classical
open scoped ComplexConjugate
namespace Fluctuations.SignNoncyclotomicAssembly
noncomputable section
theorem rootMultiplicity_reverse (p : ℂ[X]) (z : ℂ) (hz : z ≠ 0) :
    p.reverse.rootMultiplicity z = p.rootMultiplicity z⁻¹ := by
  rw [← count_roots, (IsAlgClosed.splits p).roots_reverse_filter]
  conv_lhs => arg 1; rw [← inv_inv z]
  rw [Multiset.count_map_eq_count' _ _ inv_injective,
    Multiset.count_filter_of_pos (p := fun w : ℂ => w ≠ 0) (inv_ne_zero hz), count_roots]
theorem real_rootMultiplicity_conj (p : ℝ[X]) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).rootMultiplicity (conj z) =
      (p.map (algebraMap ℝ ℂ)).rootMultiplicity z := by
  have hm : (p.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = p.map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp
  have h := Polynomial.eq_rootMultiplicity_map (p := p.map (algebraMap ℝ ℂ))
    (f := starRingEnd ℂ) (star_injective) z
  rw [hm] at h
  exact h.symm
open SignPolynomialDivisibility
theorem unequal_sign_pair_fixed (a b c d : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hab : a ≠ b) (he : c-d = a-b) : c = a ∧ d = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num at *
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem finite_sign_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ) (F : (Fin m → ℝ) → ℝ) :
    (∫ ω, F (fun j => ξ j.val ω) ∂μ) =
      (2:ℝ)⁻¹^m * ∑ a ∈ signVectors m, F a := by
  let v : Ω → Fin m → ℝ := fun ω j => ξ j.val ω
  let ν := μ.map v
  have hv : AEMeasurable v μ := aemeasurable_pi_lambda _ (fun j => hξ.1.1 j.val)
  have hsupport : ∀ᵐ a ∂ν, a ∈ (signVectors m : Set (Fin m → ℝ)) := by
    apply (ae_map_iff hv (signVectors m).measurableSet).mpr
    filter_upwards [rademacher_ae_all_values μ ξ hξ] with ω hω
    exact (mem_signVectors _).mpr (fun j => hω j.val)
  have hrestrict : ν.restrict (signVectors m : Set (Fin m → ℝ)) = ν :=
    Measure.restrict_eq_self_of_ae_mem hsupport
  have hF : Integrable F ν := by
    have hi : IntegrableOn F (signVectors m : Set (Fin m → ℝ)) ν := IntegrableOn.finset
    rwa [IntegrableOn, hrestrict] at hi
  have hmass (a : Fin m → ℝ) (ha : a ∈ signVectors m) : ν.real {a} = (2:ℝ)⁻¹^m := by
    have hmap : ν = Measure.pi (fun _ : Fin m => rademacherLaw) := by
      dsimp [ν,v]
      rw [iid_fin_map_eq_pi μ ξ hξ.1 m Fin.val Fin.val_injective, hξ.2]
    rw [measureReal_def, hmap, signVector_mass m a ha]
    norm_num
  change (∫ ω, F (v ω) ∂μ) = _
  rw [← integral_map hv hF.aestronglyMeasurable]
  change (∫ a, F a ∂ν) = _
  rw [← hrestrict, setIntegral_finset _ (by simpa only [IntegrableOn, hrestrict] using hF)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hmass a ha]
  rfl
end
end Fluctuations.SignNoncyclotomicAssembly
end

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace Fluctuations
lemma left_cell_integral_error {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ t ∈ Icc a b, |f a - f t| ≤ L * (b - a)) :
    |(b - a) * f a - ∫ t in a..b, f t| ≤ L * (b - a) ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := L * (b - a)) (f := fun t => f a - f t) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs] using hbound t ⟨ht.1.le, ht.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hf,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at h
  convert! h using 1
  ring
lemma uniform_left_riemann_error {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Icc 0 1)) (n : ℕ) (hn : 0 < n) :
    |(∑ j ∈ Finset.range n, f ((j : ℝ) / n)) / n - ∫ t in (0 : ℝ)..1, f t| ≤
      (L : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let a : ℕ → ℝ := fun j => (j : ℝ) / n
  have hab (j : ℕ) : a j ≤ a (j + 1) := by
    dsimp [a]
    exact div_le_div_of_nonneg_right (by norm_num) hn0.le
  have hcell (j : ℕ) (hj : j < n) : Icc (a j) (a (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor
    · exact (div_nonneg (Nat.cast_nonneg _) hn0.le).trans ht.1
    · apply ht.2.trans
      dsimp [a]
      exact (div_le_one hn0).mpr (by exact_mod_cast hj)
  have hi (j : ℕ) (hj : j < n) : IntervalIntegrable f volume (a j) (a (j + 1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hab j)]
    exact hf.continuousOn.mono (hcell j hj)
  have hlen (j : ℕ) : a (j + 1) - a j = 1 / n := by dsimp [a]; push_cast; ring
  have herr (j : ℕ) (hj : j < n) :
      |f (a j) / n - ∫ t in a j..a (j + 1), f t| ≤ (L : ℝ) / (n : ℝ) ^ 2 := by
    have he := left_cell_integral_error (hab j) (hi j hj) (L := (L : ℝ)) (by
      intro t ht
      have h := hf.dist_le_mul (a j) (hcell j hj ⟨le_rfl, hab j⟩) t (hcell j hj ht)
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [ht.1] : a j - t ≤ 0)] at h
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) L.coe_nonneg))
    rw [hlen] at he
    have he1 : (1 / (n : ℝ)) * f (a j) = f (a j) / n := by ring
    have he2 : (L : ℝ) * (1 / (n : ℝ)) ^ 2 = (L : ℝ) / (n : ℝ) ^ 2 := by ring
    rw [he1, he2] at he
    exact he
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hi
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a, hn.ne']
  rw [ha0, han] at hsum
  calc
    _ = |∑ j ∈ Finset.range n, (f (a j) / n - ∫ t in a j..a (j + 1), f t)| := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
    _ ≤ ∑ j ∈ Finset.range n, |f (a j) / n - ∫ t in a j..a (j + 1), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, (L : ℝ) / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum fun j hj => herr j (Finset.mem_range.mp hj)
    _ = (L : ℝ) / n := by simp; field_simp
lemma uniform_closed_riemann_error {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Icc 0 1)) (n : ℕ) (hn : 0 < n) :
    |(∑ j ∈ Finset.range (n + 1), f ((j : ℝ) / n)) / n - ∫ t in (0 : ℝ)..1, f t| ≤
      ((L : ℝ) + |f 1|) / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Finset.sum_range_succ, add_div, div_self hn0.ne']
  have heq : (∑ j ∈ Finset.range n, f ((j : ℝ) / n)) / n + f 1 / n -
      ∫ t in (0 : ℝ)..1, f t =
      ((∑ j ∈ Finset.range n, f ((j : ℝ) / n)) / n - ∫ t in (0 : ℝ)..1, f t) + f 1 / n := by ring
  rw [heq]
  calc
    _ ≤ |(∑ j ∈ Finset.range n, f ((j : ℝ) / n)) / n - ∫ t in (0 : ℝ)..1, f t| + |f 1 / n| :=
      abs_add_le _ _
    _ ≤ (L : ℝ) / n + |f 1 / n| := add_le_add (uniform_left_riemann_error hf n hn) (le_refl _)
    _ = _ := by rw [abs_div, abs_of_pos hn0]; ring
end Fluctuations
end
end

section
noncomputable section
open Set
open scoped NNReal
namespace Fluctuations.FourierApproximation
def weightedCosine (k : ℕ) (u t : ℝ) : ℝ :=
  (t - 1 / 2) ^ k * Real.cos ((t - 1 / 2) * u)
def weightedSine (k : ℕ) (u t : ℝ) : ℝ :=
  (t - 1 / 2) ^ k * Real.sin ((t - 1 / 2) * u)
lemma half_shift_abs_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |t - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
lemma weightedCosine_abs_le_one (k : ℕ) (u : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |weightedCosine k u t| ≤ 1 := by
  rw [weightedCosine, abs_mul, abs_pow]
  have hpow : |t - 1 / 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (half_shift_abs_le_one ht)
  simpa using mul_le_mul hpow (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
lemma weightedSine_abs_le_one (k : ℕ) (u : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |weightedSine k u t| ≤ 1 := by
  rw [weightedSine, abs_mul, abs_pow]
  have hpow : |t - 1 / 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (half_shift_abs_le_one ht)
  simpa using mul_le_mul hpow (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
lemma hasDerivAt_weightedCosine (k : ℕ) (u t : ℝ) :
    HasDerivAt (weightedCosine k u)
      ((k : ℝ) * (t - 1 / 2) ^ (k - 1) * Real.cos ((t - 1 / 2) * u) -
        (t - 1 / 2) ^ k * u * Real.sin ((t - 1 / 2) * u)) t := by
  have hd := (((hasDerivAt_id t).sub_const (1 / 2)).pow k).mul
    (((hasDerivAt_id t).sub_const (1 / 2)).mul_const u).cos
  simp only [id_eq, Pi.pow_apply, mul_one, one_mul] at hd
  convert! hd using 1
  ring
lemma weightedCosine_deriv_bound (k : ℕ) (u : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(k : ℝ) * (t - 1 / 2) ^ (k - 1) * Real.cos ((t - 1 / 2) * u) -
      (t - 1 / 2) ^ k * u * Real.sin ((t - 1 / 2) * u)| ≤ (k : ℝ) + |u| := by
  have hfirst : |(k : ℝ) * (t - 1 / 2) ^ (k - 1) * Real.cos ((t - 1 / 2) * u)| ≤ k := by
    rw [mul_assoc, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact (mul_le_mul_of_nonneg_left (weightedCosine_abs_le_one (k-1) u ht) (Nat.cast_nonneg k)).trans_eq (mul_one _)
  have hsecond : |(t - 1 / 2) ^ k * u * Real.sin ((t - 1 / 2) * u)| ≤ |u| := by
    rw [show (t - 1 / 2) ^ k * u * Real.sin ((t - 1 / 2) * u) = u * weightedSine k u t by unfold weightedSine; ring,
      abs_mul]
    exact (mul_le_mul_of_nonneg_left (weightedSine_abs_le_one k u ht) (abs_nonneg u)).trans_eq (mul_one _)
  exact (abs_sub _ _).trans (add_le_add hfirst hsecond)
lemma weightedCosine_lipschitzOn (k : ℕ) (u : ℝ) :
    LipschitzOnWith ⟨(k : ℝ) + |u|, by positivity⟩ (weightedCosine k u) (Icc 0 1) := by
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_weightedCosine k u t).hasDerivWithinAt)
  intro t ht
  exact_mod_cast weightedCosine_deriv_bound k u ht
end Fluctuations.FourierApproximation
end
end

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Fluctuations.SignedCrossings
def branchArgument (x y : ℝ) : ℝ := Real.arctan (-x / y)
def angularVelocity (x y dx dy : ℝ) : ℝ := (x * dy - y * dx) / (x ^ 2 + y ^ 2)
def crossingOrientation (x dy : ℝ) : ℝ :=
  (SignType.sign x : ℝ) * (SignType.sign dy : ℝ)
lemma crossingOrientation_eq_real_sign (x dy : ℝ) :
    crossingOrientation x dy = Real.sign x * Real.sign dy := by
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
    rcases lt_trichotomy dy 0 with hd | hd | hd <;>
    simp_all [crossingOrientation, sign_neg, sign_pos, Real.sign_of_neg, Real.sign_of_pos]
lemma angularVelocity_eq_im_div (x y dx dy : ℝ) :
    angularVelocity x y dx dy = ((⟨dx, dy⟩ : ℂ) / (⟨x, y⟩ : ℂ)).im := by
  simp only [angularVelocity, Complex.div_im, Complex.normSq_apply]
  ring
lemma abs_branchArgument_lt (x y : ℝ) : |branchArgument x y| < Real.pi / 2 := by
  exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
lemma hasDerivAt_branchArgument {X Y : ℝ → ℝ} {t dx dy : ℝ}
    (hX : HasDerivAt X dx t) (hY : HasDerivAt Y dy t) (hy : Y t ≠ 0) :
    HasDerivAt (fun s => branchArgument (X s) (Y s))
      (angularVelocity (X t) (Y t) dx dy) t := by
  have h := ((hX.neg).div hY hy).arctan
  convert! h using 1
  · unfold angularVelocity
    dsimp only [Pi.div_apply, Pi.neg_apply]
    have hs : X t ^ 2 + Y t ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (X t)]
    field_simp
    ring
lemma branchArgument_eq_atan_sub_sign {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    branchArgument x y = Real.arctan (y / x) -
      Real.pi / 2 * (SignType.sign x : ℝ) * (SignType.sign y : ℝ) := by
  have hform : branchArgument x y = -Real.arctan ((y / x)⁻¹) := by
    simp [branchArgument, inv_div, neg_div, Real.arctan_neg]
  rw [hform]
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · rw [Real.arctan_inv_of_pos (div_pos_of_neg_of_neg hy hx), sign_neg hx, sign_neg hy]
    norm_num
  · rw [Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hy hx), sign_neg hx, sign_pos hy]
    norm_num
  · rw [Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hy hx), sign_pos hx, sign_neg hy]
    norm_num
  · rw [Real.arctan_inv_of_pos (div_pos hy hx), sign_pos hx, sign_pos hy]
    norm_num
lemma eventually_sign_eq_of_continuousAt {X : ℝ → ℝ} {t : ℝ}
    (hX : ContinuousAt X t) (hx : X t ≠ 0) :
    ∀ᶠ s in 𝓝 t, SignType.sign (X s) = SignType.sign (X t) := by
  rcases hx.lt_or_gt with hx | hx
  · filter_upwards [hX.tendsto.eventually_lt_const hx] with s hs
    rw [sign_neg hs, sign_neg hx]
  · filter_upwards [hX.tendsto.eventually_const_lt hx] with s hs
    rw [sign_pos hs, sign_pos hx]
lemma intervalIntegrable_angularVelocity
    (X Y DX DY : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hDX : ContinuousOn DX (Icc a b)) (hDY : ContinuousOn DY (Icc a b))
    (hne : ∀ t ∈ Icc a b, X t ≠ 0 ∨ Y t ≠ 0) :
    IntervalIntegrable (fun t => angularVelocity (X t) (Y t) (DX t) (DY t)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply ((hX.mul hDY).sub (hY.mul hDX)).div ((hX.pow 2).add (hY.pow 2))
  intro t ht
  change X t ^ 2 + Y t ^ 2 ≠ 0
  rcases hne t ht with h | h <;> nlinarith [sq_nonneg (X t), sq_nonneg (Y t), sq_pos_of_ne_zero h]
end Fluctuations.SignedCrossings
end
end

section
open MeasureTheory Polynomial Complex
open scoped Topology
noncomputable section
namespace Fluctuations.PolynomialCircle
def unitCircleCurve (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  p.eval (circleMap 0 1 t)
def unitCircleCurveDerivative (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  (circleMap 0 1 t * I) * p.derivative.eval (circleMap 0 1 t)
lemma unitCircleCurve_eq_exp (p : Polynomial ℂ) (t : ℝ) :
    unitCircleCurve p t = p.eval (Complex.exp (I * (t : ℂ))) := by
  simp [unitCircleCurve, circleMap, mul_comm I]
lemma hasDerivAt_unitCircleCurve (p : Polynomial ℂ) (t : ℝ) :
    HasDerivAt (unitCircleCurve p) (unitCircleCurveDerivative p t) t := by
  exact (p.hasDerivAt (circleMap 0 1 t)).scomp t (hasDerivAt_circleMap 0 1 t)
lemma deriv_unitCircleCurve (p : Polynomial ℂ) (t : ℝ) :
    deriv (unitCircleCurve p) t = unitCircleCurveDerivative p t :=
  (hasDerivAt_unitCircleCurve p t).deriv
lemma continuous_unitCircleCurve (p : Polynomial ℂ) : Continuous (unitCircleCurve p) :=
  p.continuous.comp (continuous_circleMap 0 1)
lemma continuous_unitCircleCurveDerivative (p : Polynomial ℂ) :
    Continuous (unitCircleCurveDerivative p) :=
  ((continuous_circleMap 0 1).mul_const I).mul
    (p.derivative.continuous.comp (continuous_circleMap 0 1))
lemma unitCircleCurve_ne_zero (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) (t : ℝ) :
    unitCircleCurve p t ≠ 0 :=
  hboundary _ (by simp [norm_circleMap_zero])
lemma continuous_unitCircle_logDerivative (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    Continuous (fun t => unitCircleCurveDerivative p t / unitCircleCurve p t) :=
  (continuous_unitCircleCurveDerivative p).div (continuous_unitCircleCurve p)
    (unitCircleCurve_ne_zero p hboundary)
lemma intervalIntegrable_unitCircle_logDerivative (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun t => unitCircleCurveDerivative p t / unitCircleCurve p t)
      volume a b :=
  (continuous_unitCircle_logDerivative p hboundary).intervalIntegrable a b
lemma circleIntegral_eq_integral_unitCircle_logDerivative (p : Polynomial ℂ) :
    (∮ z in C(0, 1), p.derivative.eval z / p.eval z) =
      ∫ t in 0..2 * Real.pi, unitCircleCurveDerivative p t / unitCircleCurve p t := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [deriv_circleMap, smul_eq_mul, unitCircleCurveDerivative, unitCircleCurve]
  ring
theorem normalized_integral_unitCircle_argumentRate_eq_closedCount
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    (2 * Real.pi)⁻¹ *
      (∫ t in 0..2 * Real.pi, (deriv (unitCircleCurve p) t / unitCircleCurve p t).im) =
        ((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) := by
  classical
  simp only [deriv_unitCircleCurve]
  have him := Complex.imCLM.intervalIntegral_comp_comm
    (intervalIntegrable_unitCircle_logDerivative p hboundary 0 (2 * Real.pi))
  simp only [Complex.imCLM_apply] at him
  rw [him]
  have h := argumentPrinciple_closed hp zero_le_one hboundary
  rw [circleIntegral_eq_integral_unitCircle_logDerivative] at h
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hi := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * I) * z) h
  simp only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at hi
  rw [hi]
  simp [Complex.mul_im, mul_assoc, Real.pi_ne_zero]
def phaseVelocity (n : ℕ) : ℂ := -(n : ℂ) / 2 * I
def phaseFactor (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (phaseVelocity n * (t : ℂ))
lemma phaseFactor_eq_exp (n : ℕ) (t : ℝ) :
    phaseFactor n t = Complex.exp (-I * (n : ℂ) * (t : ℂ) / 2) := by
  unfold phaseFactor phaseVelocity
  congr 1
  ring
lemma hasDerivAt_phaseFactor (n : ℕ) (t : ℝ) :
    HasDerivAt (phaseFactor n) (phaseFactor n t * phaseVelocity n) t := by
  simpa only [phaseFactor, ofRealCLM_apply, ofReal_one, mul_one] using!
    ((ofRealCLM.hasDerivAt (x := t)).const_mul (phaseVelocity n)).cexp
lemma phaseFactor_ne_zero (n : ℕ) (t : ℝ) : phaseFactor n t ≠ 0 :=
  Complex.exp_ne_zero _
lemma continuous_phaseFactor (n : ℕ) : Continuous (phaseFactor n) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_phaseFactor n t).continuousAt)
def rotatedCircleCurve (n : ℕ) (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  phaseFactor n t * unitCircleCurve p t
def rotatedCircleCurveDerivative (n : ℕ) (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  phaseFactor n t * (unitCircleCurveDerivative p t + phaseVelocity n * unitCircleCurve p t)
lemma hasDerivAt_rotatedCircleCurve (n : ℕ) (p : Polynomial ℂ) (t : ℝ) :
    HasDerivAt (rotatedCircleCurve n p) (rotatedCircleCurveDerivative n p t) t := by
  unfold rotatedCircleCurve rotatedCircleCurveDerivative
  convert! (hasDerivAt_phaseFactor n t).mul (hasDerivAt_unitCircleCurve p t) using 1
  ring
lemma deriv_rotatedCircleCurve (n : ℕ) (p : Polynomial ℂ) (t : ℝ) :
    deriv (rotatedCircleCurve n p) t = rotatedCircleCurveDerivative n p t :=
  (hasDerivAt_rotatedCircleCurve n p t).deriv
lemma continuous_rotatedCircleCurveDerivative (n : ℕ) (p : Polynomial ℂ) :
    Continuous (rotatedCircleCurveDerivative n p) :=
  (continuous_phaseFactor n).mul ((continuous_unitCircleCurveDerivative p).add
    ((continuous_unitCircleCurve p).const_mul (phaseVelocity n)))
lemma rotatedCircleCurve_ne_zero (n : ℕ) (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) (t : ℝ) :
    rotatedCircleCurve n p t ≠ 0 :=
  mul_ne_zero (phaseFactor_ne_zero n t) (unitCircleCurve_ne_zero p hboundary t)
lemma rotatedCircle_logDerivative_eq (n : ℕ) (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) (t : ℝ) :
    rotatedCircleCurveDerivative n p t / rotatedCircleCurve n p t =
      unitCircleCurveDerivative p t / unitCircleCurve p t + phaseVelocity n := by
  unfold rotatedCircleCurveDerivative rotatedCircleCurve
  field_simp [phaseFactor_ne_zero n t, unitCircleCurve_ne_zero p hboundary t]
lemma rotatedCircle_argumentRate_eq (n : ℕ) (p : Polynomial ℂ)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) (t : ℝ) :
    (deriv (rotatedCircleCurve n p) t / rotatedCircleCurve n p t).im =
      (deriv (unitCircleCurve p) t / unitCircleCurve p t).im - (n : ℝ) / 2 := by
  rw [deriv_rotatedCircleCurve, deriv_unitCircleCurve,
    rotatedCircle_logDerivative_eq n p hboundary t]
  simp [phaseVelocity, Complex.mul_im, sub_eq_add_neg, neg_div]
theorem normalized_integral_rotated_argumentRate_eq_closedCount_sub
    (n : ℕ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    (2 * Real.pi)⁻¹ *
      (∫ t in 0..2 * Real.pi,
        (deriv (rotatedCircleCurve n p) t / rotatedCircleCurve n p t).im) =
        ((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 := by
  classical
  simp_rw [rotatedCircle_argumentRate_eq n p hboundary]
  have hrate : IntervalIntegrable
      (fun t => (deriv (unitCircleCurve p) t / unitCircleCurve p t).im)
      volume 0 (2 * Real.pi) := by
    simp only [deriv_unitCircleCurve]
    exact (Complex.continuous_im.comp (continuous_unitCircle_logDerivative p hboundary)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hrate (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_sub,
    normalized_integral_unitCircle_argumentRate_eq_closedCount p hp hboundary]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
end Fluctuations.PolynomialCircle
namespace Fluctuations
end Fluctuations
end
end

section
open MeasureTheory ProbabilityTheory Polynomial Complex
open scoped BigOperators
namespace Fluctuations
noncomputable section
def centeredFrequency (n : ℕ) (j : Fin (n + 1)) : ℝ := (j.val : ℝ) - n / 2
lemma centeredFrequency_rev (n : ℕ) (j : Fin (n + 1)) :
    centeredFrequency n j.rev = -centeredFrequency n j := by
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  have hrev : j.rev.val = n - j.val := by simp only [Fin.val_rev]; omega
  simp only [centeredFrequency, hrev, Nat.cast_sub hj]
  ring
def centeredCosineSum (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ j, a j * Real.cos (centeredFrequency n j * t)
def centeredSineSum (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ j, a j * Real.sin (centeredFrequency n j * t)
lemma centeredCosineSum_reverse (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) :
    centeredCosineSum n (fun j => a j.rev) t = centeredCosineSum n a t := by
  unfold centeredCosineSum
  have h := Equiv.sum_comp (Fin.revPerm : Fin (n + 1) ≃ Fin (n + 1))
    (fun j => a j * Real.cos (centeredFrequency n j * t))
  simpa only [Fin.revPerm_apply, centeredFrequency_rev, neg_mul, Real.cos_neg] using h
lemma centeredSineSum_reverse (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) :
    centeredSineSum n (fun j => a j.rev) t = -centeredSineSum n a t := by
  unfold centeredSineSum
  have h := Equiv.sum_comp (Fin.revPerm : Fin (n + 1) ≃ Fin (n + 1))
    (fun j => a j * Real.sin (centeredFrequency n j * t))
  simp only [Fin.revPerm_apply, centeredFrequency_rev, neg_mul, Real.sin_neg,
    mul_neg, Finset.sum_neg_distrib] at h
  linarith
lemma rotated_randomPolynomial_eq_exp_sum {Ω : Type*}
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    PolynomialCircle.rotatedCircleCurve n (randomPolynomial ξ n ω) t =
      ∑ j : Fin (n + 1), (ξ j.val ω : ℂ) *
        Complex.exp ((centeredFrequency n j * t : ℝ) * I) := by
  rw [PolynomialCircle.rotatedCircleCurve, PolynomialCircle.unitCircleCurve_eq_exp]
  simp only [randomPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  change Complex.exp _ * ((ξ j.val ω : ℂ) * Complex.exp _) = _
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [PolynomialCircle.phaseVelocity, centeredFrequency, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring
lemma rotated_randomPolynomial_coordinates {Ω : Type*}
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    (PolynomialCircle.rotatedCircleCurve n (randomPolynomial ξ n ω) t).re =
      centeredCosineSum n (fun j => ξ j.val ω) t ∧
    (PolynomialCircle.rotatedCircleCurve n (randomPolynomial ξ n ω) t).im =
      centeredSineSum n (fun j => ξ j.val ω) t := by
  rw [rotated_randomPolynomial_eq_exp_sum]
  simp only [centeredCosineSum, centeredSineSum, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  trivial
end
end Fluctuations
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Fluctuations
noncomputable section
def centeredDirichletKernel (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), Real.cos (centeredFrequency n j * t)
lemma centeredDirichletKernel_zero (n : ℕ) : centeredDirichletKernel n 0 = n + 1 := by
  simp [centeredDirichletKernel]
lemma sin_mul_centeredDirichletKernel (n : ℕ) (t : ℝ) :
    Real.sin (t / 2) * centeredDirichletKernel n t = Real.sin ((n + 1 : ℝ) * t / 2) := by
  have h := Real.sin_mul_sum_cos (n + 1) t (-(n : ℝ) * t / 2)
  rw [← Fin.sum_univ_eq_sum_range] at h
  have he (j : Fin (n + 1)) : t * (j.val : ℝ) + -(n : ℝ) * t / 2 =
      centeredFrequency n j * t := by unfold centeredFrequency; ring
  simp_rw [he] at h
  have hh : (((n + 1 : ℕ) : ℝ) - 1) * t / 2 + -(n : ℝ) * t / 2 = 0 := by
    push_cast
    ring
  rw [hh, Real.cos_zero, mul_one] at h
  simpa only [centeredDirichletKernel, Nat.cast_add, Nat.cast_one] using h
lemma centeredDirichletKernel_eq_quotient (n : ℕ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    centeredDirichletKernel n t = Real.sin ((n + 1 : ℝ) * t / 2) / Real.sin (t / 2) := by
  apply (eq_div_iff ht).mpr
  rw [mul_comm]
  exact sin_mul_centeredDirichletKernel n t
lemma abs_centeredDirichletKernel_le_inv_sin (n : ℕ) {t : ℝ}
    (ht : Real.sin (t / 2) ≠ 0) :
    |centeredDirichletKernel n t| ≤ 1 / |Real.sin (t / 2)| := by
  rw [centeredDirichletKernel_eq_quotient n ht, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
lemma centeredCosineGram (n : ℕ) (s t : ℝ) :
    (∑ j : Fin (n + 1), Real.cos (centeredFrequency n j * s) *
      Real.cos (centeredFrequency n j * t)) =
    (centeredDirichletKernel n (s - t) + centeredDirichletKernel n (s + t)) / 2 := by
  unfold centeredDirichletKernel
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring
lemma centeredSineGram (n : ℕ) (s t : ℝ) :
    (∑ j : Fin (n + 1), Real.sin (centeredFrequency n j * s) *
      Real.sin (centeredFrequency n j * t)) =
    (centeredDirichletKernel n (s - t) - centeredDirichletKernel n (s + t)) / 2 := by
  unfold centeredDirichletKernel
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring
lemma centeredCosineNormSq (n : ℕ) (t : ℝ) :
    (∑ j : Fin (n + 1), Real.cos (centeredFrequency n j * t) ^ 2) =
      ((n + 1 : ℝ) + centeredDirichletKernel n (2 * t)) / 2 := by
  simpa only [← pow_two, sub_self, centeredDirichletKernel_zero, ← two_mul] using
    centeredCosineGram n t t
lemma centeredSineNormSq (n : ℕ) (t : ℝ) :
    (∑ j : Fin (n + 1), Real.sin (centeredFrequency n j * t) ^ 2) =
      ((n + 1 : ℝ) - centeredDirichletKernel n (2 * t)) / 2 := by
  simpa only [← pow_two, sub_self, centeredDirichletKernel_zero, ← two_mul] using
    centeredSineGram n t t
lemma centeredTrigNormSq_lower (n : ℕ) {t : ℝ} (ht : Real.sin t ≠ 0)
    (hbulk : 1 / |Real.sin t| ≤ (n + 1 : ℝ) / 2) :
    (n + 1 : ℝ) / 4 ≤ ∑ j : Fin (n + 1), Real.cos (centeredFrequency n j * t) ^ 2 ∧
    (n + 1 : ℝ) / 4 ≤ ∑ j : Fin (n + 1), Real.sin (centeredFrequency n j * t) ^ 2 := by
  have hh : Real.sin ((2 * t) / 2) ≠ 0 := by simpa using ht
  have h := abs_centeredDirichletKernel_le_inv_sin n hh
  have hbound : |centeredDirichletKernel n (2 * t)| ≤ (n + 1 : ℝ) / 2 := by
    exact h.trans (by simpa using hbulk)
  rw [centeredCosineNormSq, centeredSineNormSq]
  have := abs_le.mp hbound
  constructor <;> linarith
end
end Fluctuations
end

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace Fluctuations.FourierApproximation
lemma weightedCosine_riemann_error (k n : ℕ) (hn : 0 < n) (u : ℝ) :
    |(∑ j ∈ Finset.range (n + 1), weightedCosine k u ((j : ℝ) / n)) / n -
      ∫ t in (0 : ℝ)..1, weightedCosine k u t| ≤ ((k : ℝ) + |u| + 1) / n := by
  apply (uniform_closed_riemann_error (weightedCosine_lipschitzOn k u) n hn).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact add_le_add (le_refl _) (weightedCosine_abs_le_one k u ⟨by norm_num, le_rfl⟩)
lemma integral_weightedCosine_zero (u : ℝ) :
    (∫ t in (0 : ℝ)..1, weightedCosine 0 u t) = sineKernel u := by
  by_cases hu : u = 0
  · subst u
    simp [weightedCosine, sineKernel]
  have hd (t : ℝ) : HasDerivAt (fun t => Real.sin ((t - 1 / 2) * u) / u)
      (weightedCosine 0 u t) t := by
    have h := ((((hasDerivAt_id t).sub_const (1 / 2)).mul_const u).sin).div_const u
    simpa [weightedCosine, hu] using h
  have hi : IntervalIntegrable (weightedCosine 0 u) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (weightedCosine_lipschitzOn 0 u).continuousOn
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [h, sineKernel, Real.sinc_of_ne_zero (div_ne_zero hu (by norm_num))]
  rw [show (1 - 1 / 2 : ℝ) * u = u / 2 by ring,
    show (0 - 1 / 2 : ℝ) * u = -(u / 2) by ring, Real.sin_neg]
  ring
lemma sum_weightedCosine_zero (n : ℕ) (hn : 0 < n) (u : ℝ) :
    (∑ j ∈ Finset.range (n + 1), weightedCosine 0 u ((j : ℝ) / n)) =
      centeredDirichletKernel n (u / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Fin.sum_univ_eq_sum_range]
  unfold centeredDirichletKernel
  apply Finset.sum_congr rfl
  intro j _
  simp only [weightedCosine, pow_zero, one_mul, centeredFrequency]
  congr 1
  field_simp
lemma scaled_centeredDirichletKernel_error_global (n : ℕ) (hn : 0 < n) (u : ℝ) :
    |(n : ℝ)⁻¹ * centeredDirichletKernel n (u / n) - sineKernel u| ≤
      (1 + |u|) / n := by
  have h := weightedCosine_riemann_error 0 n hn u
  rw [sum_weightedCosine_zero n hn u, integral_weightedCosine_zero] at h
  calc
    _ = |centeredDirichletKernel n (u / n) / (n : ℝ) - sineKernel u| := by congr 1; ring
    _ ≤ ((0 : ℝ) + |u| + 1) / n := by simpa only [Nat.cast_zero] using h
    _ = _ := by ring
end Fluctuations.FourierApproximation
end
end

section
open Set
namespace Fluctuations.BulkAngles
noncomputable section
lemma sin_lower_of_away_endpoints {ε u : ℝ} (hε : 0 ≤ ε)
    (hlo : ε ≤ u) (hhi : u ≤ Real.pi - ε) :
    (2 / Real.pi) * ε ≤ Real.sin u := by
  by_cases hu : u ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hlo (by positivity)).trans
      (Real.mul_le_sin (hε.trans hlo) hu)
  · have hv0 : 0 ≤ Real.pi - u := by linarith
    have hv : Real.pi - u ≤ Real.pi / 2 := by linarith
    have hh := Real.mul_le_sin hv0 hv
    rw [Real.sin_pi_sub] at hh
    exact (mul_le_mul_of_nonneg_left (by linarith : ε ≤ Real.pi - u) (by positivity)).trans hh
lemma sin_scaled_lower {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Icc Real.pi (Real.pi * n - Real.pi)) :
    2 / (n : ℝ) ≤ Real.sin (t / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := sin_lower_of_away_endpoints (ε := Real.pi / n) (u := t / n)
    (by positivity) (div_le_div_of_nonneg_right ht.1 hn'.le)
    (by
      apply (div_le_iff₀ hn').mpr
      field_simp
      nlinarith [ht.2])
  have he : (2 / Real.pi) * (Real.pi / n) = 2 / (n : ℝ) := by field_simp
  rwa [he] at h
lemma bulk_sine_inverse_bound {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Icc Real.pi (Real.pi * n - Real.pi)) :
    Real.sin (t / n) ≠ 0 ∧ 1 / |Real.sin (t / n)| ≤ (n + 1 : ℝ) / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs := sin_scaled_lower hn ht
  have hp : 0 < Real.sin (t / n) := (by positivity : (0 : ℝ) < 2 / n).trans_le hs
  refine ⟨hp.ne', ?_⟩
  rw [abs_of_pos hp]
  have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 / n) hs
  have he : 1 / (2 / (n : ℝ)) = n / 2 := by field_simp
  rw [he] at hh
  linarith
end
end Fluctuations.BulkAngles
end

section
noncomputable section
open Set
open scoped BigOperators
namespace Fluctuations.FourierApproximation
lemma abs_weighted_sum_le_partial_sum_bound (w g : ℕ → ℝ) (n : ℕ) {M : ℝ}
    (hpartial : ∀ m : ℕ, m ≤ n + 1 → |∑ j ∈ Finset.range m, g j| ≤ M) :
    |∑ j ∈ Finset.range (n + 1), w j * g j| ≤
      M * (|w n| + ∑ j ∈ Finset.range n, |w (j + 1) - w j|) := by
  have he := Finset.sum_range_by_parts w g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ |w n * ∑ j ∈ Finset.range (n + 1), g j| +
        |∑ j ∈ Finset.range n, (w (j+1) - w j) * ∑ i ∈ Finset.range (j+1), g i| := abs_sub _ _
    _ ≤ |w n| * M + ∑ j ∈ Finset.range n, |w (j+1) - w j| * M := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpartial (n+1) le_rfl) (abs_nonneg _)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpartial (j+1) (by have := Finset.mem_range.mp hj; omega)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring
lemma abs_partial_cosine_sum_bound (m : ℕ) (θ α : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) :
    |∑ j ∈ Finset.range m, Real.cos (θ * j + α)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h := Real.sin_mul_sum_cos m θ α
  have he : (∑ j ∈ Finset.range m, Real.cos (θ * j + α)) =
      (Real.sin (m * θ / 2) * Real.cos (((m : ℝ) - 1) * θ / 2 + α)) / Real.sin (θ / 2) := by
    exact (eq_div_iff hθ).mpr (by simpa only [mul_comm] using h)
  rw [he, abs_div, abs_mul]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa using mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
lemma frequency_power_total_variation (k n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n,
      |(((j + 1 : ℕ) : ℝ) / n - 1 / 2) ^ k - ((j : ℝ) / n - 1 / 2) ^ k|) ≤ k := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmem {j : ℕ} (hj : j ≤ n) : (j : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    exact ⟨by positivity, (div_le_one hn0).mpr (by exact_mod_cast hj)⟩
  have hterm (j : ℕ) (hj : j < n) :
      |(((j + 1 : ℕ) : ℝ) / n - 1 / 2) ^ k - ((j : ℝ) / n - 1 / 2) ^ k| ≤ (k : ℝ) / n := by
    have h := (weightedCosine_lipschitzOn k 0).dist_le_mul
      (((j+1 : ℕ) : ℝ) / n) (hmem (by omega)) ((j : ℝ) / n) (hmem (by omega))
    simp only [weightedCosine, mul_zero, Real.cos_zero, mul_one, abs_zero, add_zero,
      Real.dist_eq] at h
    have he : (((j+1 : ℕ) : ℝ) / n) - ((j : ℝ) / n) = 1 / n := by push_cast; ring
    rw [he, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at h
    change |(((j + 1 : ℕ) : ℝ) / n - 1 / 2) ^ k - ((j : ℝ) / n - 1 / 2) ^ k| ≤
      (k : ℝ) * (1 / n) at h
    simpa only [mul_one_div] using h
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (k : ℝ) / n :=
      Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.mp hj)
    _ = k := by simp; field_simp
lemma frequency_weighted_sum_bound (g : ℕ → ℝ) (k n : ℕ) (hn : 0 < n) {M : ℝ}
    (hM : 0 ≤ M) (hpartial : ∀ m : ℕ, m ≤ n + 1 → |∑ j ∈ Finset.range m, g j| ≤ M) :
    |∑ j ∈ Finset.range (n + 1), ((j : ℝ) / n - 1 / 2) ^ k * g j| ≤ M * (1 + k) := by
  apply (abs_weighted_sum_le_partial_sum_bound (fun j => ((j : ℝ) / n - 1 / 2) ^ k) g n hpartial).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply add_le_add _ (frequency_power_total_variation k n hn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_self hn0, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (by norm_num)
lemma abs_weightedCosine_sum_decay (k n : ℕ) (hn : 0 < n) (u : ℝ)
    (hu : Real.sin ((u / (n : ℝ)) / 2) ≠ 0) :
    |(∑ j ∈ Finset.range (n + 1), weightedCosine k u ((j : ℝ) / n)) / n| ≤
      ((k : ℝ) + 1) / ((n : ℝ) * |Real.sin ((u / n) / 2)|) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : (∑ j ∈ Finset.range (n + 1), weightedCosine k u ((j : ℝ) / n)) =
      ∑ j ∈ Finset.range (n+1), ((j : ℝ) / n - 1 / 2) ^ k * Real.cos ((u / n) * j + (-u / 2)) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold weightedCosine
    congr 2
    ring
  rw [heq, abs_div, abs_of_pos hn0]
  have h := frequency_weighted_sum_bound (fun j => Real.cos ((u / n) * j + (-u / 2))) k n hn
    (by positivity : 0 ≤ 1 / |Real.sin ((u / (n : ℝ)) / 2)|)
    (fun m _ => abs_partial_cosine_sum_bound m (u / n) (-u / 2) hu)
  apply (div_le_div_of_nonneg_right h hn0.le).trans_eq
  ring
lemma scaled_sine_denominator_lower (n : ℕ) (hn : 0 < n) {ε u : ℝ}
    (hε : 0 < ε) (hlo : ε ≤ |u|) (hhi : |u| ≤ 2 * Real.pi * n - ε) :
    ε / Real.pi ≤ (n : ℝ) * |Real.sin ((u / n) / 2)| := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs := BulkAngles.sin_lower_of_away_endpoints
    (ε := ε / (2 * n)) (u := |u| / (2 * n)) (by positivity)
    (div_le_div_of_nonneg_right hlo (by positivity)) (by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
      field_simp
      nlinarith [hhi])
  have he1 : (2 / Real.pi) * (ε / (2 * (n : ℝ))) = (ε / Real.pi) / n := by ring
  rw [he1] at hs
  have he2 : |Real.sin (|u| / (2 * (n : ℝ)))| = |Real.sin ((u / n) / 2)| := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu, show u / (2 * (n : ℝ)) = (u / n) / 2 by ring]
    · rw [abs_of_neg (lt_of_not_ge hu), show -u / (2 * (n : ℝ)) = -((u / n) / 2) by ring,
        Real.sin_neg, abs_neg]
  have hb := hs.trans (le_abs_self _)
  rw [he2] at hb
  exact (div_le_iff₀ hn0).mp hb |>.trans_eq (mul_comm _ _)
lemma abs_weightedCosine_sum_bulk_decay (k n : ℕ) (hn : 0 < n) {ε u : ℝ}
    (hε : 0 < ε) (hlo : ε ≤ |u|) (hhi : |u| ≤ 2 * Real.pi * n - ε) :
    |(∑ j ∈ Finset.range (n + 1), weightedCosine k u ((j : ℝ) / n)) / n| ≤
      Real.pi * ((k : ℝ) + 1) / ε := by
  have hden := scaled_sine_denominator_lower n hn hε hlo hhi
  have hd : 0 < (n : ℝ) * |Real.sin ((u / n) / 2)| :=
    (div_pos hε Real.pi_pos).trans_le hden
  have hs : Real.sin ((u / (n : ℝ)) / 2) ≠ 0 := by
    intro heq
    simp [heq] at hd
  apply (abs_weightedCosine_sum_decay k n hn u hs).trans
  calc
    _ ≤ ((k : ℝ) + 1) / (ε / Real.pi) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hε Real.pi_pos) hden
    _ = _ := by field_simp
end Fluctuations.FourierApproximation
end
end

section
noncomputable section
open Set
open scoped BigOperators
namespace Fluctuations.NormalizedTrigKernel
open FourierApproximation
def scaledDirichlet (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * centeredDirichletKernel n (u / n)
lemma scaledDirichlet_error (n : ℕ) (hn : 0 < n) (u : ℝ) :
    |scaledDirichlet n u - sineKernel u| ≤ (1 + |u|) / n :=
  scaled_centeredDirichletKernel_error_global n hn u
lemma scaledDirichlet_bulk_bound (n : ℕ) (hn : 0 < n) {ε u : ℝ}
    (hε : 0 < ε) (hlo : ε ≤ |u|) (hhi : |u| ≤ 2 * Real.pi * n - ε) :
    |scaledDirichlet n u| ≤ Real.pi / ε := by
  have h := abs_weightedCosine_sum_bulk_decay 0 n hn hε hlo hhi
  rw [sum_weightedCosine_zero n hn u] at h
  simpa [scaledDirichlet, div_eq_mul_inv, mul_comm] using h
end Fluctuations.NormalizedTrigKernel
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace Fluctuations.SineEvaluationGram
open NormalizedTrigKernel
def offset (i : Fin 8) : ℝ := 2 * Real.pi * (i.val + 1)
def coefficient (n : ℕ) (x : ℝ) (j : Fin (n+1)) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 (fun i => Real.sin (centeredFrequency n j * ((x + offset i) / n)))
def gram (n : ℕ) (x : ℝ) (i l : Fin 8) : ℝ :=
  (∑ j, coefficient n x j i * coefficient n x j l) / n
lemma offset_bounds (i : Fin 8) : 2*Real.pi ≤ offset i ∧ offset i ≤ 16*Real.pi := by
  have hi : (i.val : ℝ) ≤ 7 := by exact_mod_cast (show i.val ≤ 7 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [offset]
  constructor <;> nlinarith [Real.pi_pos]
lemma offset_sub_bound (i l : Fin 8) : |offset i - offset l| ≤ 14*Real.pi := by
  have hi := offset_bounds i
  have hl := offset_bounds l
  exact abs_le.mpr ⟨by linarith, by linarith⟩
lemma offset_add_bound (i l : Fin 8) : |offset i + offset l| ≤ 32*Real.pi := by
  have hi := offset_bounds i
  have hl := offset_bounds l
  rw [abs_of_pos (by linarith [Real.pi_pos] : 0 < offset i + offset l)]
  linarith
lemma sineKernel_two_pi_int (k : ℤ) :
    sineKernel (2*Real.pi*k) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, sineKernel]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp only [hk, ite_false]
    rw [sineKernel,
      show 2*Real.pi*(k : ℝ)/2 = (k : ℝ)*Real.pi by ring,
      Real.sinc_of_ne_zero (mul_ne_zero hk' Real.pi_ne_zero), Real.sin_int_mul_pi]
    simp
lemma sineKernel_offset_sub (i l : Fin 8) :
    sineKernel (offset i - offset l) = if i = l then 1 else 0 := by
  have he : offset i - offset l = 2*Real.pi*(((i.val : ℤ)-l.val : ℤ) : ℝ) := by
    dsimp [offset]
    push_cast
    ring
  rw [he, sineKernel_two_pi_int]
  have hi : (i.val : ℤ) - l.val = 0 ↔ i = l := by
    rw [sub_eq_zero, Int.natCast_inj, Fin.val_inj]
  simp only [hi]
lemma sineKernel_offset_add (i l : Fin 8) : sineKernel (offset i + offset l) = 0 := by
  have he : offset i + offset l = 2*Real.pi*(((i.val : ℤ)+l.val+2 : ℤ) : ℝ) := by
    dsimp [offset]
    push_cast
    ring
  rw [he, sineKernel_two_pi_int]
  simp only [show (i.val : ℤ)+l.val+2 ≠ 0 by omega, ite_false]
lemma scaledDirichlet_two_pi_shift (n : ℕ) (hn : 0 < n) (u : ℝ) :
    scaledDirichlet n (2*Real.pi*n + u) = (-1 : ℝ)^n * scaledDirichlet n u := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (j : Fin (n+1)) :
      centeredFrequency n j * ((2*Real.pi*n+u)/n) =
        (centeredFrequency n j * (u/n) + j.val*(2*Real.pi)) - n*Real.pi := by
    dsimp [centeredFrequency]
    field_simp
    ring
  simp only [scaledDirichlet, centeredDirichletKernel, he,
    Real.cos_sub_nat_mul_pi, Real.cos_add_nat_mul_two_pi, ← Finset.mul_sum]
  ring
lemma gram_formula (n : ℕ) (x : ℝ) (i l : Fin 8) :
    gram n x i l =
      (scaledDirichlet n (offset i-offset l) -
        scaledDirichlet n (2*x+offset i+offset l))/2 := by
  have h := centeredSineGram n ((x+offset i)/n) ((x+offset l)/n)
  change (∑ j, coefficient n x j i * coefficient n x j l) = _ at h
  rw [show (x+offset i)/n - (x+offset l)/n = (offset i-offset l)/n by ring,
    show (x+offset i)/n + (x+offset l)/n = (2*x+offset i+offset l)/n by ring] at h
  unfold gram
  rw [h, scaledDirichlet, scaledDirichlet]
  ring
lemma coefficient_norm_le (n : ℕ) (x : ℝ) (j : Fin (n+1)) :
    ‖coefficient n x j‖ ≤ 8 := by
  have hsq : ‖coefficient n x j‖^2 ≤ 8 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 8, (1 : ℝ) := by
        apply sum_le_sum
        intro i _
        change |Real.sin _|^2 ≤ 1
        exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)
      _ = 8 := by norm_num
  nlinarith [norm_nonneg (coefficient n x j)]
lemma scaledDirichlet_offset_sub_error (n : ℕ) (hn : 0 < n) (i l : Fin 8) :
    |scaledDirichlet n (offset i-offset l) - (if i=l then 1 else 0)| ≤
      (1+14*Real.pi)/n := by
  rw [← sineKernel_offset_sub]
  apply (scaledDirichlet_error n hn _).trans
  exact div_le_div_of_nonneg_right
    (add_le_add le_rfl (offset_sub_bound i l)) (Nat.cast_nonneg n)
lemma scaledDirichlet_offset_add_bound (n : ℕ) (hn : 0 < n) (i l : Fin 8) :
    |scaledDirichlet n (offset i+offset l)| ≤ (1+32*Real.pi)/n := by
  have h := scaledDirichlet_error n hn (offset i+offset l)
  rw [sineKernel_offset_add, sub_zero] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add le_rfl (offset_add_bound i l)) (Nat.cast_nonneg n))
lemma gram_entry_error (n : ℕ) (hn : 0 < n) (x B : ℝ) (i l : Fin 8)
    (hB : |scaledDirichlet n (2*x+offset i+offset l)| ≤ B) :
    |gram n x i l - (if i=l then 1/2 else 0)| ≤ ((1+14*Real.pi)/n+B)/2 := by
  have he : gram n x i l - (if i=l then 1/2 else 0) =
      ((scaledDirichlet n (offset i-offset l) - (if i=l then 1 else 0)) -
        scaledDirichlet n (2*x+offset i+offset l))/2 := by
    rw [gram_formula]
    split_ifs <;> ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ)≤2)
  exact (abs_sub _ _).trans (add_le_add (scaledDirichlet_offset_sub_error n hn i l) hB)
lemma gram_bulk_entry_bound (n : ℕ) (hn : 0 < n)
    (hlarge : 256*(1+23*Real.pi) ≤ (n : ℝ)) (x : ℝ)
    (hx : x ∈ Set.Icc (256*Real.pi) (Real.pi*n-256*Real.pi)) (i l : Fin 8) :
    |gram n x i l - (if i=l then 1/2 else 0)| ≤ 1/256 := by
  have harg : 0 < 2*x+offset i+offset l := by
    have hi := offset_bounds i
    have hl := offset_bounds l
    nlinarith [hx.1, Real.pi_pos]
  have hreflect : |scaledDirichlet n (2*x+offset i+offset l)| ≤ 1/256 := by
    have h := scaledDirichlet_bulk_bound n hn (ε := 256*Real.pi)
      (u := 2*x+offset i+offset l) (by positivity) (by
        rw [abs_of_pos harg]
        nlinarith [hx.1, (offset_bounds i).1, (offset_bounds l).1, Real.pi_pos]) (by
        rw [abs_of_pos harg]
        nlinarith [hx.2, (offset_bounds i).2, (offset_bounds l).2, Real.pi_pos])
    convert! h using 1
    field_simp
  have hnonosc : (1+14*Real.pi)/(n : ℝ) ≤ 1/256 := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hn)]
    nlinarith [Real.pi_pos]
  apply (gram_entry_error n hn x (1/256) i l hreflect).trans
  linarith
lemma gram_endpoint_entry_bound (n : ℕ) (hn : 0 < n)
    (hlarge : 256*(1+23*Real.pi) ≤ (n : ℝ)) (x : ℝ)
    (hx : x=0 ∨ x=Real.pi*n) (i l : Fin 8) :
    |gram n x i l - (if i=l then 1/2 else 0)| ≤ 1/256 := by
  have hreflect : |scaledDirichlet n (2*x+offset i+offset l)| ≤ (1+32*Real.pi)/n := by
    rcases hx with rfl | rfl
    · simpa using scaledDirichlet_offset_add_bound n hn i l
    · rw [show 2*(Real.pi*(n : ℝ))+offset i+offset l =
        2*Real.pi*n+(offset i+offset l) by ring, scaledDirichlet_two_pi_shift n hn]
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        scaledDirichlet_offset_add_bound n hn i l
  apply (gram_entry_error n hn x ((1+32*Real.pi)/n) i l hreflect).trans
  rw [show ((1+14*Real.pi)/(n : ℝ)+(1+32*Real.pi)/n)/2 =
    (1+23*Real.pi)/n by ring, div_le_iff₀ (Nat.cast_pos.mpr hn)]
  nlinarith
def AdmissibleBase (n : ℕ) (x : ℝ) : Prop :=
  x=0 ∨ x=Real.pi*n ∨ x ∈ Set.Icc (256*Real.pi) (Real.pi*n-256*Real.pi)
lemma gram_entry_bound (n : ℕ) (hn : 0 < n)
    (hlarge : 256*(1+23*Real.pi) ≤ (n : ℝ)) (x : ℝ)
    (hx : AdmissibleBase n x) (i l : Fin 8) :
    |gram n x i l - (if i=l then 1/2 else 0)| ≤ 1/256 := by
  rcases hx with hx | hx | hx
  · exact gram_endpoint_entry_bound n hn hlarge x (Or.inl hx) i l
  · exact gram_endpoint_entry_bound n hn hlarge x (Or.inr hx) i l
  · exact gram_bulk_entry_bound n hn hlarge x hx i l
lemma gram_quadratic (n : ℕ) (x : ℝ) (u : EuclideanSpace ℝ (Fin 8)) :
    (∑ j, (inner ℝ (coefficient n x j) u)^2)/n =
      ∑ i, ∑ l, u i * gram n x i l * u l := by
  have hs (j : Fin (n+1)) : (inner ℝ (coefficient n x j) u)^2 =
      ∑ i, ∑ l, u i * (coefficient n x j i * coefficient n x j l) * u l := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial, pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro l _
    ring
  simp only [hs, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  simp only [gram, div_eq_mul_inv, sum_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  ring
theorem coefficient_gram_lower (n : ℕ) (hn : 0 < n)
    (hlarge : 256*(1+23*Real.pi) ≤ (n : ℝ)) (x : ℝ)
    (hx : AdmissibleBase n x) (u : EuclideanSpace ℝ (Fin 8)) :
    (1/4 : ℝ)*n*‖u‖^2 ≤ ∑ j, (inner ℝ (coefficient n x j) u)^2 := by
  have hdiag : (∑ i, ∑ l : Fin 8, u i*(if i=l then (1/2 : ℝ) else 0)*u l) =
      ‖u‖^2/2 := by
    rw [EuclideanSpace.norm_sq_eq, sum_div]
    simp only [Real.norm_eq_abs, sq_abs, mul_ite, ite_mul, mul_zero, zero_mul,
      sum_ite_eq, mem_univ, ite_true]
    apply sum_congr rfl
    intro i _
    ring
  have heq : (∑ j, (inner ℝ (coefficient n x j) u)^2)/n - ‖u‖^2/2 =
      ∑ i, ∑ l, u i*(gram n x i l-(if i=l then (1/2 : ℝ) else 0))*u l := by
    rw [gram_quadratic]
    simp only [mul_sub, sub_mul, sum_sub_distrib]
    rw [hdiag]
  have hterm (i l : Fin 8) :
      |u i*(gram n x i l-(if i=l then (1/2 : ℝ) else 0))*u l| ≤
        ‖u‖*(1/256)*‖u‖ := by
    have hi : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hl : |u l| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u l
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul hi (gram_entry_bound n hn hlarge x hx i l) (abs_nonneg _) (norm_nonneg _))
      hl (abs_nonneg _) (by positivity)
  have herr : |(∑ j, (inner ℝ (coefficient n x j) u)^2)/n - ‖u‖^2/2| ≤
      ‖u‖^2/4 := by
    rw [heq]
    calc
      _ ≤ ∑ i, |∑ l, u i*(gram n x i l-(if i=l then (1/2 : ℝ) else 0))*u l| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ l, |u i*(gram n x i l-(if i=l then (1/2 : ℝ) else 0))*u l| :=
        sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 8, ∑ _l : Fin 8, ‖u‖*(1/256)*‖u‖ :=
        sum_le_sum (fun i _ => sum_le_sum (fun l _ => hterm i l))
      _ = _ := by simp; ring
  have hlow : ‖u‖^2/4 ≤ (∑ j, (inner ℝ (coefficient n x j) u)^2)/n := by
    have h := (abs_le.mp herr).1
    linarith
  have h := (le_div_iff₀ (Nat.cast_pos.mpr hn)).mp hlow
  nlinarith
end Fluctuations.SineEvaluationGram
end
end

section
open Finset
open scoped BigOperators
namespace Fluctuations.UniformBasisInverse
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def synthesis (v : ι → E) : EuclideanSpace ℝ ι →L[ℝ] E :=
  (Fintype.linearCombination ℝ v).toContinuousLinearMap.comp
    (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap
theorem synthesis_apply (v : ι → E) (x : EuclideanSpace ℝ ι) :
    synthesis v x = ∑ i, x i • v i := by
  rfl
theorem continuous_synthesis_apply :
    Continuous (fun p : (ι → E) × EuclideanSpace ℝ ι => synthesis p.1 p.2) := by
  simp only [synthesis_apply]
  fun_prop
theorem exists_uniform_synthesis_lower_bound (S : Set (ι → E)) (hS : IsCompact S)
    (hlin : ∀ v ∈ S, LinearIndependent ℝ v) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ v ∈ S, ∀ x : EuclideanSpace ℝ ι,
      μ * ‖x‖ ≤ ‖synthesis v x‖ := by
  let Q : Set ((ι → E) × EuclideanSpace ℝ ι) := S ×ˢ Metric.sphere 0 1
  have hQ : IsCompact Q := hS.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun p : (ι → E) × EuclideanSpace ℝ ι =>
      ‖synthesis p.1 p.2‖) Q := continuous_synthesis_apply.norm.continuousOn
  have hpos : ∀ p ∈ Q, 0 < ‖synthesis p.1 p.2‖ := by
    rintro ⟨v, x⟩ ⟨hv, hx⟩
    apply norm_pos_iff.mpr
    intro he
    have hx0 : x = 0 := by
      ext i
      exact (Fintype.linearIndependent_iff.mp (hlin v hv))
        (fun i => x i) (by simpa [synthesis_apply] using he) i
    simp [hx0] at hx
  obtain ⟨μ, hμ, hbound⟩ := hQ.exists_forall_le' hcont hpos
  refine ⟨μ, hμ, ?_⟩
  intro v hv x
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxnorm),
        inv_mul_cancel₀ hxnorm.ne']
    have hb := hbound (v, ‖x‖⁻¹ • x) ⟨hv, by simpa using hunit⟩
    simp only [map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxnorm)] at hb
    have hh := mul_le_mul_of_nonneg_right hb hxnorm.le
    calc
      μ * ‖x‖ ≤ (‖x‖⁻¹ * ‖synthesis v x‖) * ‖x‖ := hh
      _ = ‖synthesis v x‖ := by field_simp
def SeparatedTuple {r : ℕ} (d : ℝ) (v : Fin r → E) : Prop :=
  ∀ i, ∀ t : Fin r → ℝ,
    d ≤ ‖v i - ∑ j, (if j < i then t j else 0) • v j‖
def boundedSeparatedTuples (r : ℕ) (K d : ℝ) : Set (Fin r → E) :=
  {v | (∀ i, ‖v i‖ ≤ K) ∧ SeparatedTuple d v}
theorem isClosed_separatedTuples (r : ℕ) (d : ℝ) :
    IsClosed {v : Fin r → E | SeparatedTuple d v} := by
  simp only [SeparatedTuple, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro t
  apply isClosed_le continuous_const
  fun_prop
theorem isCompact_boundedSeparatedTuples [ProperSpace E] (r : ℕ) (K d : ℝ) :
    IsCompact (boundedSeparatedTuples (E := E) r K d) := by
  have hc := isCompact_univ_pi (fun _ : Fin r => isCompact_closedBall (0 : E) K)
  have hi := hc.inter_right (isClosed_separatedTuples (E := E) r d)
  simpa [boundedSeparatedTuples, Set.pi, Metric.mem_closedBall, dist_zero_right, Set.inter_def] using hi
theorem SeparatedTuple.linearIndependent {r : ℕ} {d : ℝ} (hd : 0 < d)
    {v : Fin r → E} (hv : SeparatedTuple d v) : LinearIndependent ℝ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  by_contra hi
  let A : Finset (Fin r) := univ.filter (fun j => t j ≠ 0)
  have hA : A.Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let k := A.max' hA
  have hk : t k ≠ 0 := (mem_filter.mp (max'_mem A hA)).2
  have htail (j : Fin r) (hkj : k < j) : t j = 0 := by
    by_contra hj
    have hle := le_max' A j (mem_filter.mpr ⟨mem_univ j, hj⟩)
    exact (not_le_of_gt hkj) hle
  have hcomb : v k - ∑ j, (if j < k then -(t j / t k) else 0) • v j = 0 := by
    have hsum := sum_erase_add univ (fun j => t j • v j) (mem_univ k)
    have herase : (∑ j ∈ univ.erase k, t j • v j) =
        ∑ j, (if j < k then t j else 0) • v j := by
      rw [← sum_erase_add univ (fun j => (if j < k then t j else 0) • v j) (mem_univ k)]
      simp only [lt_self_iff_false, ite_false, zero_smul, add_zero]
      apply sum_congr rfl
      intro j hj
      by_cases hjk : j < k
      · simp [hjk]
      · have hkj : k < j := lt_of_le_of_ne (le_of_not_gt hjk) (Ne.symm (mem_erase.mp hj).1)
        simp [hjk, htail j hkj]
    rw [herase, ht] at hsum
    have hh := congrArg (fun x : E => (t k)⁻¹ • x) hsum
    have hnormalize : ∑ j, (if j < k then -(t j / t k) else 0) • v j =
        -((t k)⁻¹ • ∑ j, (if j < k then t j else 0) • v j) := by
      rw [smul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro j hj
      split_ifs
      · simpa only [neg_smul, div_eq_mul_inv, mul_smul] using
          congrArg Neg.neg (smul_comm (t j) ((t k)⁻¹) (v j))
      · simp
    rw [hnormalize]
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hk, one_smul, smul_zero] at hh
    simpa [sub_neg_eq_add, add_comm] using hh
  have hb := hv k (fun j => -(t j / t k))
  rw [hcomb, norm_zero] at hb
  exact (not_le_of_gt hd) hb
theorem exists_uniform_coordinate_inverse [FiniteDimensional ℝ E]
    (r : ℕ) (K d : ℝ) (hd : 0 < d) (hdim : Module.finrank ℝ E = r) :
    ∃ T : ℝ, 0 < T ∧ ∀ v : Fin r → E,
      (∀ i, ‖v i‖ ≤ K) → SeparatedTuple d v →
      ∃ L : E ≃L[ℝ] EuclideanSpace ℝ (Fin r),
        ‖L.toContinuousLinearMap‖ ≤ T ∧ ∀ i, L (v i) = EuclideanSpace.single i 1 := by
  let S := boundedSeparatedTuples (E := E) r K d
  obtain ⟨μ, hμ, hbound⟩ := exists_uniform_synthesis_lower_bound S
    (isCompact_boundedSeparatedTuples r K d)
    (fun v hv => hv.2.linearIndependent hd)
  refine ⟨μ⁻¹, inv_pos.mpr hμ, ?_⟩
  intro v hnorm hsep
  have hlin := hsep.linearIndependent hd
  have hinj : Function.Injective (synthesis v) :=
    hlin.fintypeLinearCombination_injective.comp (EuclideanSpace.equiv (Fin r) ℝ).injective
  let e : EuclideanSpace ℝ (Fin r) ≃ₗ[ℝ] E :=
    (synthesis v).toLinearMap.linearEquivOfInjective hinj (by simpa using hdim.symm)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin r) := e.toContinuousLinearEquiv.symm
  have hLeval (x : E) : synthesis v (L x) = x := e.apply_symm_apply x
  have hLsymm (x : EuclideanSpace ℝ (Fin r)) : L.symm x = synthesis v x := rfl
  refine ⟨L, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound L.toContinuousLinearMap (inv_pos.mpr hμ).le
    intro x
    change ‖L x‖ ≤ μ⁻¹ * ‖x‖
    have hb := hbound v ⟨hnorm, hsep⟩ (L x)
    rw [hLeval] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hμ]
    nlinarith
  · intro i
    apply L.symm.injective
    rw [L.symm_apply_apply, hLsymm, synthesis_apply]
    simp
end Fluctuations.UniformBasisInverse
end

section
open Finset
open scoped BigOperators
namespace Fluctuations.GramGroupExtraction
variable {α E : Type*} [Fintype α] [DecidableEq α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem gram_threshold_card (a : α → E) (K d B : ℝ)
    (ha : ∀ j, ‖a j‖ ≤ K)
    (u : E) (hu : ‖u‖ = 1)
    (hgram : B ≤ ∑ j, (inner ℝ (a j) u)^2) :
    B - Fintype.card α * d^2 ≤
      ((univ.filter (fun j => d ≤ |inner ℝ (a j) u|)).card : ℝ) * K^2 := by
  classical
  let H := univ.filter (fun j => d ≤ |inner ℝ (a j) u|)
  have hbound (j : α) : (inner ℝ (a j) u)^2 ≤
      (if j ∈ H then K^2 else 0) + d^2 := by
    have hj := (abs_real_inner_le_norm (a j) u).trans (by simpa [hu] using ha j)
    by_cases hjH : j ∈ H
    · simp only [hjH, ite_true]
      have hh : (inner ℝ (a j) u)^2 ≤ K^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hj 2
      nlinarith [sq_nonneg d]
    · have hsmall : |inner ℝ (a j) u| < d := by
        simpa [H, not_le] using hjH
      simp only [hjH, ite_false]
      have hh := pow_le_pow_left₀ (abs_nonneg (inner ℝ (a j) u)) hsmall.le 2
      simpa only [zero_add, sq_abs] using hh
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset α)) => hbound j)
  have hsum : (∑ j, ((if j ∈ H then K^2 else 0) + d^2)) =
      (H.card : ℝ) * K^2 + Fintype.card α * d^2 := by
    simp [sum_add_distrib]
  rw [hsum] at hs
  dsimp [H] at hs
  linarith
theorem gram_threshold_many (a : α → E) (C0 K κ n : ℝ)
    (hC0 : 0 < C0) (hK : 0 < K) (hκ : 0 < κ)
    (hm : (Fintype.card α : ℝ) ≤ C0 * n) (ha : ∀ j, ‖a j‖ ≤ K)
    (hgram : ∀ u : E, κ * n * ‖u‖^2 ≤ ∑ j, (inner ℝ (a j) u)^2)
    (u : E) (hu : ‖u‖ = 1) :
    κ / (2*K^2) * n ≤
      ((univ.filter (fun j => Real.sqrt (κ/(2*C0)) ≤ |inner ℝ (a j) u|)).card : ℝ) := by
  have hd : 0 ≤ κ / (2*C0) := by positivity
  have hs := gram_threshold_card a K (Real.sqrt (κ/(2*C0))) (κ*n)
    ha u hu (by simpa [hu] using hgram u)
  rw [Real.sq_sqrt hd] at hs
  have hh := mul_le_mul_of_nonneg_right hm hd
  have hcancel : C0 * n * (κ/(2*C0)) = κ*n/2 := by field_simp
  rw [hcancel] at hh
  have hpos : 0 < 2*K^2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith
omit [InnerProductSpace ℝ E] in
theorem exists_finite_norm_cover [ProperSpace E] (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Z : Finset E, Z.Nonempty ∧ ∀ x : E, ‖x‖ ≤ K → ∃ z ∈ Z, ‖x - z‖ < η / 2 := by
  classical
  obtain ⟨Z, hZsub, hZfin, hcover⟩ :=
    (isCompact_closedBall (0 : E) K).finite_cover_balls (half_pos hη)
  have hc (x : E) (hx : ‖x‖ ≤ K) : ∃ z ∈ Z, ‖x - z‖ < η / 2 := by
    have hh := hcover (show x ∈ Metric.closedBall (0 : E) K by simpa using hx)
    simpa only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm, exists_prop] using hh
  obtain ⟨z, hz, hz0⟩ := hc 0 (by simpa using hK)
  refine ⟨hZfin.toFinset, ⟨z, by simpa using hz⟩, ?_⟩
  intro x hx
  simpa using hc x hx
omit [Fintype α] [DecidableEq α] [InnerProductSpace ℝ E] in
theorem exists_large_close_subfamily (a : α → E) (H : Finset α) (hH : H.Nonempty)
    (Z : Finset E) (hZ : Z.Nonempty) (η : ℝ)
    (hcover : ∀ j ∈ H, ∃ z ∈ Z, ‖a j - z‖ < η / 2) :
    ∃ J : Finset α, J ⊆ H ∧
      (H.card : ℝ) / Z.card ≤ J.card ∧
      ∃ j₀ ∈ J, ∀ j ∈ J, ‖a j - a j₀‖ < η := by
  classical
  let C (z : E) := H.filter (fun j => ‖a j - z‖ < η / 2)
  have hsub : H ⊆ Z.biUnion C := by
    intro j hj
    obtain ⟨z, hz, hjz⟩ := hcover j hj
    exact mem_biUnion.mpr ⟨z, hz, mem_filter.mpr ⟨hj, hjz⟩⟩
  obtain ⟨z, hz, hmax⟩ := exists_max_image Z (fun z => (C z).card) hZ
  have hcard : H.card ≤ Z.card * (C z).card := by
    calc
      H.card ≤ (Z.biUnion C).card := card_le_card hsub
      _ ≤ ∑ z ∈ Z, (C z).card := card_biUnion_le
      _ ≤ ∑ _z ∈ Z, (C z).card := sum_le_sum (fun z' hz' => hmax z' hz')
      _ = _ := by simp
  have hC : (C z).Nonempty := by
    apply card_pos.mp
    by_contra h
    have hzcard : (C z).card = 0 := Nat.eq_zero_of_not_pos h
    rw [hzcard, mul_zero] at hcard
    exact (not_le_of_gt (card_pos.mpr hH)) hcard
  obtain ⟨j₀, hj₀⟩ := hC
  refine ⟨C z, filter_subset _ _, ?_, j₀, hj₀, ?_⟩
  · have hp : (0 : ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZ
    rw [div_le_iff₀ hp]
    exact_mod_cast (by simpa only [mul_comm] using hcard)
  · intro j hj
    have hjz := (mem_filter.mp hj).2
    have hj₀z := (mem_filter.mp hj₀).2
    have ht := norm_add_le (a j - z) (z - a j₀)
    rw [sub_add_sub_cancel] at ht
    rw [norm_sub_rev z (a j₀)] at ht
    linarith
theorem exists_unit_normal_to_prefix [FiniteDimensional ℝ E]
    {r : ℕ} (hdim : Module.finrank ℝ E = r) (v : Fin r → E) (k : Fin r) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ i < k, inner ℝ (v i) u = 0 := by
  classical
  let V := Submodule.span ℝ ((Iio k).image v : Set E)
  have hdimV : Module.finrank ℝ V < Module.finrank ℝ E := by
    calc
      Module.finrank ℝ V ≤ ((Iio k).image v).card := finrank_span_finset_le_card _
      _ ≤ (Iio k).card := card_image_le
      _ = k.val := Fin.card_Iio k
      _ < Module.finrank ℝ E := by simp [hdim]
  have hV : V ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hdimV
    exact (lt_irrefl _) hdimV
  have horth : Vᗮ ≠ ⊥ := by
    intro h
    exact hV ((Submodule.orthogonal_eq_bot_iff (K := V)).mp h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  refine ⟨‖w‖⁻¹ • w, norm_smul_inv_norm hw0, ?_⟩
  intro i hik
  have hvi : v i ∈ V := Submodule.subset_span (mem_image.mpr ⟨i, mem_Iio.mpr hik, rfl⟩)
  have hiw := Submodule.inner_right_of_mem_orthogonal hvi hw
  simp [inner_smul_right, hiw]
private theorem previous_combination_update {r : ℕ} (v : Fin r → E)
    (i k : Fin r) (hik : i ≤ k) (w : E) (t : Fin r → ℝ) :
    (∑ j, (if j < i then t j else 0) • (Function.update v k w) j) =
      ∑ j, (if j < i then t j else 0) • v j := by
  classical
  apply sum_congr rfl
  intro j hj
  by_cases hji : j < i
  · have hjk : j ≠ k := by
      intro h
      subst j
      exact (not_lt_of_ge hik) hji
    simp [hji, Function.update_of_ne hjk]
  · simp [hji]
private theorem projection_separates_prefix {r : ℕ} (v : Fin r → E)
    (k : Fin r) (u w : E) (hu : ‖u‖ = 1)
    (horth : ∀ i < k, inner ℝ (v i) u = 0) (d : ℝ)
    (hw : d ≤ |inner ℝ w u|) (t : Fin r → ℝ) :
    d ≤ ‖w - ∑ j, (if j < k then t j else 0) • v j‖ := by
  have hzero : inner ℝ (∑ j, (if j < k then t j else 0) • v j) u = 0 := by
    rw [sum_inner]
    apply sum_eq_zero
    intro j hj
    by_cases hjk : j < k
    · simp [hjk, real_inner_smul_left, horth j hjk]
    · simp [hjk]
  have hh := abs_real_inner_le_norm (w - ∑ j, (if j < k then t j else 0) • v j) u
  rw [inner_sub_left, hzero, sub_zero, hu, mul_one] at hh
  exact hw.trans hh
omit [DecidableEq α] in
private theorem disjoint_projection_filter (a : α → E) (J : Finset α)
    (v u : E) (η d : ℝ) (hu : ‖u‖ = 1) (horth : inner ℝ v u = 0)
    (hclose : ∀ j ∈ J, ‖a j - v‖ < η) (hηd : η ≤ d) :
    Disjoint J (univ.filter (fun j => d ≤ |inner ℝ (a j) u|)) := by
  apply disjoint_left.mpr
  intro j hj hjH
  have hbig := (mem_filter.mp hjH).2
  have hsmall := abs_real_inner_le_norm (a j - v) u
  rw [inner_sub_left, horth, sub_zero, hu, mul_one] at hsmall
  exact (not_lt_of_ge hbig) ((hsmall.trans_lt (hclose j hj)).trans_le hηd)
omit [DecidableEq α] in
theorem exists_separated_groups_of_many_projections [FiniteDimensional ℝ E]
    (r : ℕ) (hdim : Module.finrank ℝ E = r) (a : α → E)
    (K d η b n : ℝ) (hηd : η ≤ d) (hb : 0 < b) (hn : 0 < n)
    (ha : ∀ j, ‖a j‖ ≤ K) (Z : Finset E) (hZ : Z.Nonempty)
    (hcover : ∀ j, ∃ z ∈ Z, ‖a j - z‖ < η/2)
    (hmany : ∀ u : E, ‖u‖ = 1 → b*n ≤
      ((univ.filter (fun j => d ≤ |inner ℝ (a j) u|)).card : ℝ)) :
    ∃ v : Fin r → E, ∃ J : Fin r → Finset α,
      (∀ i, ‖v i‖ ≤ K) ∧
      (∀ i, b / Z.card * n ≤ (J i).card) ∧
      (∀ i, ∀ j ∈ J i, ‖a j - v i‖ < η) ∧
      (∀ i j, i ≠ j → Disjoint (J i) (J j)) ∧
      UniformBasisInverse.SeparatedTuple d v := by
  classical
  let P (k : ℕ) : Prop :=
    ∃ v : Fin r → E, ∃ J : Fin r → Finset α,
      (∀ i, i.val < k → ‖v i‖ ≤ K) ∧
      (∀ i, i.val < k → b / Z.card * n ≤ (J i).card) ∧
      (∀ i, i.val < k → ∀ j ∈ J i, ‖a j - v i‖ < η) ∧
      (∀ i, i.val < k → ∀ j, j.val < k → i ≠ j → Disjoint (J i) (J j)) ∧
      (∀ i, i.val < k → ∀ t : Fin r → ℝ,
        d ≤ ‖v i - ∑ j, (if j < i then t j else 0) • v j‖)
  have hP : ∀ k, k ≤ r → P k := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨fun _ => 0, fun _ => ∅, ?_⟩
      simp
    | succ k ih =>
      intro hk
      obtain ⟨v, J, hv, hcard, hclose, hdisj, hsep⟩ := ih (by omega)
      let i₀ : Fin r := ⟨k, by omega⟩
      obtain ⟨u, hu, horth⟩ := exists_unit_normal_to_prefix hdim v i₀
      let H := univ.filter (fun j => d ≤ |inner ℝ (a j) u|)
      have hmanyu : b*n ≤ (H.card : ℝ) := hmany u hu
      have hH : H.Nonempty := by
        apply card_pos.mp
        have hpos : (0 : ℝ) < H.card := (mul_pos hb hn).trans_le hmanyu
        exact_mod_cast hpos
      obtain ⟨J₀, hJH, hJcard, j₀, hj₀, hJclose⟩ :=
        exists_large_close_subfamily a H hH Z hZ η (fun j _ => hcover j)
      have hnewcard : b / Z.card * n ≤ (J₀.card : ℝ) := by
        have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZ
        calc
          b / Z.card * n = (b*n) / Z.card := by ring
          _ ≤ (H.card : ℝ) / Z.card := div_le_div_of_nonneg_right hmanyu hZpos.le
          _ ≤ _ := hJcard
      have hnewsep (t : Fin r → ℝ) :
          d ≤ ‖a j₀ - ∑ j, (if j < i₀ then t j else 0) • v j‖ :=
        projection_separates_prefix v i₀ u (a j₀) hu horth d
          (mem_filter.mp (hJH hj₀)).2 t
      have hnewdisj (i : Fin r) (hi : i.val < k) : Disjoint (J i) J₀ := by
        have hii : i < i₀ := hi
        exact (disjoint_projection_filter a (J i) (v i) u η d hu
          (horth i hii) (hclose i hi) hηd).mono_right hJH
      refine ⟨Function.update v i₀ (a j₀), Function.update J i₀ J₀, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases he : i = i₀
        · subst i; simpa using ha j₀
        · have hik : i.val < k := by
            have hne : i.val ≠ k := fun h => he (Fin.ext h)
            omega
          simpa [Function.update_of_ne he] using hv i hik
      · intro i hi
        by_cases he : i = i₀
        · subst i; simpa using hnewcard
        · have hik : i.val < k := by
            have hne : i.val ≠ k := fun h => he (Fin.ext h)
            omega
          simpa [Function.update_of_ne he] using hcard i hik
      · intro i hi j hj
        by_cases he : i = i₀
        · subst i
          simpa using hJclose j (by simpa using hj)
        · have hik : i.val < k := by
            have hne : i.val ≠ k := fun h => he (Fin.ext h)
            omega
          simpa [Function.update_of_ne he] using hclose i hik j (by simpa [he] using hj)
      · intro i hi j hj hij
        by_cases hie : i = i₀
        · subst i
          have hjne : j ≠ i₀ := Ne.symm hij
          have hjk : j.val < k := by
            have hne : j.val ≠ k := fun h => hjne (Fin.ext h)
            omega
          simpa [Function.update_of_ne hjne] using (hnewdisj j hjk).symm
        · by_cases hje : j = i₀
          · subst j
            have hik : i.val < k := by
              have hne : i.val ≠ k := fun h => hie (Fin.ext h)
              omega
            simpa [Function.update_of_ne hie] using hnewdisj i hik
          · have hik : i.val < k := by
              have hne : i.val ≠ k := fun h => hie (Fin.ext h)
              omega
            have hjk : j.val < k := by
              have hne : j.val ≠ k := fun h => hje (Fin.ext h)
              omega
            simpa [Function.update_of_ne hie, Function.update_of_ne hje] using
              hdisj i hik j hjk hij
      · intro i hi t
        by_cases he : i = i₀
        · subst i
          rw [Function.update_self, previous_combination_update v i₀ i₀ le_rfl]
          exact hnewsep t
        · have hik : i.val < k := by
            have hne : i.val ≠ k := fun h => he (Fin.ext h)
            omega
          rw [Function.update_of_ne he,
            previous_combination_update v i i₀ (show i ≤ i₀ from le_of_lt hik)]
          exact hsep i hik t
  obtain ⟨v, J, hv, hcard, hclose, hdisj, hsep⟩ := hP r le_rfl
  exact ⟨v, J, (fun i => hv i i.isLt), (fun i => hcard i i.isLt),
    (fun i => hclose i i.isLt), (fun i j hij => hdisj i i.isLt j j.isLt hij),
    (fun i => hsep i i.isLt)⟩
theorem exists_near_coordinate_groups [FiniteDimensional ℝ E]
    (r : ℕ) (hr : 0 < r) (hdim : Module.finrank ℝ E = r)
    (C0 K κ : ℝ) (hC0 : 0 < C0) (hK : 0 < K) (hκ : 0 < κ) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (m : ℕ) (n : ℝ) (a : Fin m → E), 0 < n →
        (m : ℝ) ≤ C0*n → (∀ j, ‖a j‖ ≤ K) →
        (∀ u : E, κ*n*‖u‖^2 ≤ ∑ j, (inner ℝ (a j) u)^2) →
        ∃ J : Fin r → Finset (Fin m),
        ∃ L : E ≃L[ℝ] EuclideanSpace ℝ (Fin r),
          (∀ i, c*n ≤ (J i).card) ∧
          (∀ i j, i ≠ j → Disjoint (J i) (J j)) ∧
          ‖L.toContinuousLinearMap‖ ≤ T ∧
          ∀ i j, j ∈ J i → ∀ l,
            |(L (a j)) l - (if i = l then 1 else 0)| ≤ 1/(4*(r : ℝ)) := by
  classical
  let d := Real.sqrt (κ/(2*C0))
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨T, hT, hinverse⟩ :=
    UniformBasisInverse.exists_uniform_coordinate_inverse (E := E) r K d hd hdim
  let η := min (d/2) ((1/(4*(r : ℝ)))/T)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hη : 0 < η := lt_min (half_pos hd) (by positivity)
  have hηd : η ≤ d := (min_le_left _ _).trans (by linarith)
  have hTη : T*η ≤ 1/(4*(r : ℝ)) := by
    have hh := (le_div_iff₀ hT).mp (min_le_right (d/2) ((1/(4*(r : ℝ)))/T))
    simpa only [η, mul_comm] using hh
  obtain ⟨Z, hZ, hcover⟩ := exists_finite_norm_cover (E := E) K η hK.le hη
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZ
  let b := κ/(2*K^2)
  have hb : 0 < b := by positivity
  refine ⟨b/Z.card, T, div_pos hb hZpos, hT, ?_⟩
  intro m n a hn hm ha hgram
  have hmany (u : E) (hu : ‖u‖ = 1) :
      b*n ≤ ((univ.filter (fun j => d ≤ |inner ℝ (a j) u|)).card : ℝ) := by
    exact gram_threshold_many a C0 K κ n hC0 hK hκ (by simpa using hm) ha hgram u hu
  obtain ⟨v, J, hv, hcard, hclose, hdisj, hsep⟩ :=
    exists_separated_groups_of_many_projections r hdim a K d η b n hηd hb hn ha Z hZ
      (fun j => hcover (a j) (ha j)) hmany
  obtain ⟨L, hLnorm, hLv⟩ := hinverse v hv hsep
  refine ⟨J, L, hcard, hdisj, hLnorm, ?_⟩
  intro i j hj l
  have hcoord := PiLp.norm_apply_le (L (a j - v i)) l
  have he : (L (a j - v i)) l = (L (a j)) l - (if i = l then 1 else 0) := by
    simp [map_sub, hLv, PiLp.single_apply, eq_comm]
  rw [he, Real.norm_eq_abs] at hcoord
  apply hcoord.trans
  calc
    ‖L (a j - v i)‖ ≤ ‖L.toContinuousLinearMap‖ * ‖a j - v i‖ :=
      L.toContinuousLinearMap.le_opNorm _
    _ ≤ T*η := mul_le_mul hLnorm (hclose i j hj).le (norm_nonneg _) hT.le
    _ ≤ _ := hTη
end Fluctuations.GramGroupExtraction
end

section
open Finset
open scoped BigOperators
namespace Fluctuations.SignProductChain
def chainPrefix {q : ℕ} (p : Equiv.Perm (Fin q)) (k : ℕ) : Finset (Fin q) :=
  (univ.filter (fun j => j.val < k)).map p.toEmbedding
def chainPerms {q : ℕ} (s : Finset (Fin q)) : Finset (Equiv.Perm (Fin q)) :=
  univ.filter (fun p => chainPrefix p s.card = s)
theorem card_chainPrefix {q k : ℕ} (p : Equiv.Perm (Fin q)) (hk : k ≤ q) :
    (chainPrefix p k).card = k := by
  rw [chainPrefix, card_map]
  symm
  calc
    k = (univ : Finset (Fin k)).card := (card_fin k).symm
    _ = (univ.filter (fun j : Fin q => j.val < k)).card := by
      apply card_bij (fun j _ => (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin q))
      · intro j hj
        simp
      · intro i hi j hj hij
        exact Fin.ext (congrArg (fun x : Fin q => x.val) hij)
      · intro j hj
        exact ⟨⟨j.val, (mem_filter.mp hj).2⟩, mem_univ _, rfl⟩
theorem chainPrefix_mono {q : ℕ} (p : Equiv.Perm (Fin q)) {k l : ℕ} (hkl : k ≤ l) :
    chainPrefix p k ⊆ chainPrefix p l := by
  apply map_subset_map.mpr
  intro j hj
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hj).2 hkl⟩
theorem comparable_of_mem_chainPerms {q : ℕ} {s t : Finset (Fin q)}
    {p : Equiv.Perm (Fin q)} (hs : p ∈ chainPerms s) (ht : p ∈ chainPerms t) :
    s ⊆ t ∨ t ⊆ s := by
  obtain h | h := le_total s.card t.card
  · exact Or.inl ((mem_filter.mp hs).2 ▸ (mem_filter.mp ht).2 ▸ chainPrefix_mono p h)
  · exact Or.inr ((mem_filter.mp ht).2 ▸ (mem_filter.mp hs).2 ▸ chainPrefix_mono p h)
theorem chainPrefix_trans {q : ℕ} (p e : Equiv.Perm (Fin q)) (k : ℕ) :
    chainPrefix (p.trans e) k = (chainPrefix p k).map e.toEmbedding := by
  simp [chainPrefix, map_map]
theorem card_chainPerms_eq {q : ℕ} (s t : Finset (Fin q)) (hst : s.card = t.card) :
    (chainPerms s).card = (chainPerms t).card := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  apply card_bij (fun p _ => p.trans e)
  · intro p hp
    simp only [chainPerms, mem_filter, mem_univ, true_and] at hp ⊢
    rw [chainPrefix_trans, ← hst, hp, he]
  · intro p hp p' hp' h
    apply Equiv.ext
    intro j
    exact e.injective (Equiv.congr_fun h j)
  · intro p hp
    refine ⟨p.trans e.symm, ?_, ?_⟩
    · simp only [chainPerms, mem_filter, mem_univ, true_and] at hp ⊢
      rw [chainPrefix_trans, hst, hp, ← he]
      simp [map_map]
    · ext j
      simp
theorem chainPerms_mul_choose {q : ℕ} (s : Finset (Fin q)) :
    (chainPerms s).card * q.choose s.card = q.factorial := by
  have hcard : ∀ p : Equiv.Perm (Fin q), (chainPrefix p s.card).card = s.card :=
    fun p => card_chainPrefix p (by simpa using s.card_le_univ)
  have h := card_eq_sum_card_fiberwise
    (s := (univ : Finset (Equiv.Perm (Fin q))))
    (t := powersetCard s.card (univ : Finset (Fin q)))
    (f := fun p => chainPrefix p s.card) (by
      intro p hp
      exact mem_powersetCard.mpr ⟨subset_univ _, hcard p⟩)
  have hsum : (∑ t ∈ powersetCard s.card (univ : Finset (Fin q)),
      (univ.filter (fun p : Equiv.Perm (Fin q) => chainPrefix p s.card = t)).card) =
      q.choose s.card * (chainPerms s).card := by
    calc
      _ = (powersetCard s.card (univ : Finset (Fin q))).card * (chainPerms s).card := by
        apply sum_const_nat
        intro t ht
        have hts : t.card = s.card := (mem_powersetCard.mp ht).2
        rw [← hts]
        exact card_chainPerms_eq t s hts
      _ = _ := by simp
  rw [hsum] at h
  simpa [Fintype.card_perm, mul_comm] using h.symm
theorem product_chain_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (F : Finset (∀ i, Finset (Fin (q i))))
    (hF : ∀ s ∈ F, ∀ t ∈ F, (∀ i, s i ⊆ t i ∨ t i ⊆ s i) → s = t) :
    F.card ≤ ∏ i, (q i).choose (q i / 2) := by
  classical
  let C : (∀ i, Finset (Fin (q i))) → Finset (∀ i, Equiv.Perm (Fin (q i))) :=
    fun s => Fintype.piFinset (fun i => chainPerms (s i))
  have hdisjoint : (F : Set (∀ i, Finset (Fin (q i)))).PairwiseDisjoint C := by
    intro s hs t ht hst
    apply disjoint_left.mpr
    intro p hps hpt
    apply hst
    apply hF s hs t ht
    intro i
    exact comparable_of_mem_chainPerms
      (Fintype.mem_piFinset.mp hps i) (Fintype.mem_piFinset.mp hpt i)
  have htotal : (∑ s ∈ F, ∏ i, (chainPerms (s i)).card) ≤ ∏ i, (q i).factorial := by
    have h := (F.biUnion C).card_le_univ
    rw [card_biUnion hdisjoint] at h
    simpa [C, Fintype.card_piFinset, Fintype.card_pi, Fintype.card_perm] using h
  have hpoint (s : ∀ i, Finset (Fin (q i))) :
      (∏ i, (q i).factorial) ≤
        (∏ i, (chainPerms (s i)).card) * (∏ i, (q i).choose (q i / 2)) := by
    rw [← prod_mul_distrib]
    apply prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i hi
    rw [← chainPerms_mul_choose (s i)]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_middle _ _)
  have hcount : F.card * (∏ i, (q i).factorial) ≤
      (∏ i, (q i).factorial) * (∏ i, (q i).choose (q i / 2)) := by
    calc
      F.card * (∏ i, (q i).factorial) = ∑ _s ∈ F, ∏ i, (q i).factorial := by simp
      _ ≤ ∑ s ∈ F, (∏ i, (chainPerms (s i)).card) *
          (∏ i, (q i).choose (q i / 2)) := sum_le_sum (fun s _ => hpoint s)
      _ = (∑ s ∈ F, ∏ i, (chainPerms (s i)).card) *
          (∏ i, (q i).choose (q i / 2)) := (sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ htotal
  have hpos : 0 < ∏ i, (q i).factorial := prod_pos (fun i _ => Nat.factorial_pos _)
  exact Nat.le_of_mul_le_mul_left (by simpa only [mul_comm F.card] using hcount) hpos
theorem middle_product_square_bound {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (N : ℕ) (hN : N ≤ ∏ i, (q i).choose (q i / 2)) :
    (N : ℝ)^2 * (∏ i, ((q i : ℝ) + 1)) ≤
      (2 : ℝ)^(Fintype.card ι) * 4^(∑ i, q i) := by
  have hc : (N : ℝ) ≤ ∏ i, ((q i).choose (q i / 2) : ℝ) := by
    exact_mod_cast hN
  calc
    (N : ℝ)^2 * (∏ i, ((q i : ℝ) + 1)) ≤
        (∏ i, ((q i).choose (q i / 2) : ℝ))^2 * (∏ i, ((q i : ℝ) + 1)) := by
      gcongr
    _ = ∏ i, (((q i).choose (q i / 2) : ℝ)^2 * ((q i : ℝ) + 1)) := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ ∏ i, (2 * (4 : ℝ)^(q i)) := by
      apply prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact SarkozySzemeredi.middle_choose_square_bound (q i)
    _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, prod_pow_eq_pow_sum]
end Fluctuations.SignProductChain
end

section
open Finset
open scoped BigOperators
namespace Fluctuations.SignVectorSmallBall
theorem comparable_sum_error {α : Type*} [DecidableEq α]
    (s t : Finset α) (a : α → ℝ) (c ε : ℝ)
    (ha : ∀ j, |a j - c| ≤ ε) (hcomp : s ⊆ t ∨ t ⊆ s) :
    |((∑ j ∈ s, a j) - (∑ j ∈ t, a j)) - ((s.card : ℝ) - t.card) * c| ≤
      ε * |(s.card : ℝ) - t.card| := by
  have haux (u v : Finset α) (huv : u ⊆ v) :
      |((∑ j ∈ v, a j) - (∑ j ∈ u, a j)) - ((v.card : ℝ) - u.card) * c| ≤
        ε * ((v.card : ℝ) - u.card) := by
    have hsum := sum_sdiff (f := fun j => a j - c) huv
    have hcard : ((v \ u).card : ℝ) = (v.card : ℝ) - u.card := by
      rw [card_sdiff_of_subset huv, Nat.cast_sub (card_le_card huv)]
    calc
      _ = |∑ j ∈ v \ u, (a j - c)| := by
        congr 1
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum ⊢
        rw [hcard] at hsum ⊢
        linarith
      _ ≤ ∑ j ∈ v \ u, |a j - c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ v \ u, ε := sum_le_sum (fun j _ => ha j)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, hcard]; ring
  rcases hcomp with hst | hts
  · have h := haux s t hst
    have hc : (s.card : ℝ) ≤ t.card := by exact_mod_cast card_le_card hst
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    convert! h using 1
    · rw [← abs_neg]
      congr 1
      ring
    · ring
  · have h := haux t s hts
    have hc : (t.card : ℝ) ≤ s.card := by exact_mod_cast card_le_card hts
    simpa only [abs_of_nonneg (sub_nonneg.mpr hc)] using h
def subsetSum {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (a : ∀ i, Fin (q i) → ι → ℝ) (s : ∀ i, Finset (Fin (q i))) (l : ι) : ℝ :=
  ∑ i, ∑ j ∈ s i, a i j l
theorem near_coordinate_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j l, |a i j l - (if i = l then 1 else 0)| ≤ ε)
    (s t : ∀ i, Finset (Fin (q i))) (hst : s ≠ t)
    (hcomp : ∀ i, s i ⊆ t i ∨ t i ⊆ s i) :
    ∃ l, 3 / 4 ≤ |subsetSum q a s l - subsetSum q a t l| := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
  have hcards : (s i).card ≠ (t i).card := by
    intro he
    apply hi
    rcases hcomp i with h | h
    · exact eq_of_subset_of_card_le h he.ge
    · exact (eq_of_subset_of_card_le h he.le).symm
  let Δ : ι → ℝ := fun i => (s i).card - (t i).card
  have hΔi : 1 ≤ |Δ i| := by
    rcases lt_or_gt_of_ne hcards with h | h
    · have hh : ((s i).card : ℝ) + 1 ≤ (t i).card := by exact_mod_cast h
      dsimp [Δ]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : ((t i).card : ℝ) + 1 ≤ (s i).card := by exact_mod_cast h
      dsimp [Δ]
      rw [abs_of_nonneg (by linarith)]
      linarith
  obtain ⟨l, hl, hmax⟩ := exists_max_image univ (fun j => |Δ j|) ⟨i, mem_univ i⟩
  have hD : 1 ≤ |Δ l| := hΔi.trans (hmax i (mem_univ i))
  have he : |subsetSum q a s l - subsetSum q a t l - Δ l| ≤
      ε * (Fintype.card ι) * |Δ l| := by
    calc
      _ = |∑ i, (((∑ j ∈ s i, a i j l) - (∑ j ∈ t i, a i j l)) -
          Δ i * (if i = l then 1 else 0))| := by
        congr 1
        simp [sum_sub_distrib, subsetSum, mul_ite]
      _ ≤ ∑ i, |((∑ j ∈ s i, a i j l) - (∑ j ∈ t i, a i j l)) -
          Δ i * (if i = l then 1 else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ε * |Δ i| := by
        apply sum_le_sum
        intro i hi
        exact comparable_sum_error (s i) (t i) (fun j => a i j l) _ ε
          (fun j => ha i j l) (hcomp i)
      _ ≤ ∑ _i : ι, ε * |Δ l| := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hmax i hi) hε
      _ = _ := by simp; ring
  have he' : |subsetSum q a s l - subsetSum q a t l - Δ l| ≤ |Δ l| / 4 :=
    he.trans (by nlinarith [mul_le_mul_of_nonneg_right hεr (abs_nonneg (Δ l))])
  have ht := abs_sub_abs_le_abs_sub (Δ l) (subsetSum q a s l - subsetSum q a t l)
  rw [abs_sub_comm (Δ l)] at ht
  exact ⟨l, by linarith⟩
def signSum {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (a : ∀ i, Fin (q i) → ι → ℝ) (s : ∀ i, Finset (Fin (q i))) (l : ι) : ℝ :=
  2 * subsetSum q a s l - subsetSum q a (fun _ => univ) l
theorem signSum_eq_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ)
    (s : ∀ i, Finset (Fin (q i))) (l : ι) :
    signSum q a s l = ∑ i, ∑ j, if j ∈ s i then a i j l else -a i j l := by
  classical
  simp only [signSum, subsetSum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have hsum := sum_add_sum_compl (s i) (fun j => a i j l)
  rw [sum_ite]
  simp only [filter_mem_eq_inter, univ_inter, sum_neg_distrib]
  have hcompl : univ.filter (fun j => j ∉ s i) = (s i)ᶜ := by ext j; simp
  rw [hcompl, ← mul_sum]
  linarith
theorem near_coordinate_sign_family_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j l, |a i j l - (if i = l then 1 else 0)| ≤ ε)
    (F : Finset (∀ i, Finset (Fin (q i)))) (z : ι → ℝ)
    (hF : ∀ s ∈ F, ∀ l, |signSum q a s l - z l| ≤ 1 / 2) :
    F.card ≤ ∏ i, (q i).choose (q i / 2) := by
  apply SignProductChain.product_chain_bound
  intro s hs t ht hcomp
  by_contra hst
  obtain ⟨l, hl⟩ := near_coordinate_separation q a ε hε hεr ha s t hst hcomp
  have hs' := abs_le.mp (hF s hs l)
  have ht' := abs_le.mp (hF t ht l)
  simp only [signSum] at hs' ht'
  have hsmall : |subsetSum q a s l - subsetSum q a t l| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith
theorem near_coordinate_sign_small_ball_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j l, |a i j l - (if i = l then 1 else 0)| ≤ ε)
    (F : Finset (∀ i, Finset (Fin (q i)))) (z : ι → ℝ)
    (hF : ∀ s ∈ F, ∀ l, |signSum q a s l - z l| ≤ 1 / 2) :
    ((F.card : ℝ) / 2^(∑ i, q i))^2 * (∏ i, ((q i : ℝ) + 1)) ≤
      (2 : ℝ)^(Fintype.card ι) := by
  have hsq := SignProductChain.middle_product_square_bound q F.card
    (near_coordinate_sign_family_bound q a ε hε hεr ha F z hF)
  have hp : (0 : ℝ) < 2^(∑ i, q i) := by positivity
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hp)]
  convert! hsq using 1
  rw [← pow_mul, mul_comm (∑ i, q i), pow_mul]
  norm_num
theorem near_coordinate_sign_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j l, |a i j l - (if i = l then 1 else 0)| ≤ ε)
    (F : Finset (∀ i, Finset (Fin (q i)))) (z : ι → ℝ)
    (hF : ∀ s ∈ F, ∀ l, |signSum q a s l - z l| ≤ 1 / 2)
    (c n : ℝ) (hc : 0 < c) (hn : 0 < n) (hq : ∀ i, c * n ≤ (q i : ℝ) + 1) :
    (F.card : ℝ) / 2^(∑ i, q i) ≤
      (2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2) := by
  have hsq := near_coordinate_sign_small_ball_square q a ε hε hεr ha F z hF
  have hcn : 0 < c * n := mul_pos hc hn
  have hp : (c * n)^(Fintype.card ι) ≤ ∏ i, ((q i : ℝ) + 1) := by
    calc
      _ = ∏ _i : ι, c * n := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => hcn.le) (fun i _ => hq i)
  have hsq' : ((F.card : ℝ) / 2^(∑ i, q i))^2 * (c * n)^(Fintype.card ι) ≤
      (2 : ℝ)^(Fintype.card ι) := by
    exact (mul_le_mul_of_nonneg_left hp (sq_nonneg _)).trans hsq
  have hR : ((2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2))^2 =
      (2 / (c * n))^(Fintype.card ι) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show ((Fintype.card ι : ℝ) / 2) * (2 : ℝ) = (Fintype.card ι : ℝ) by ring,
      Real.rpow_natCast]
  have hB : ((F.card : ℝ) / 2^(∑ i, q i))^2 ≤
      ((2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2))^2 := by
    rw [hR, div_pow (2 : ℝ) (c * n), le_div_iff₀ (pow_pos hcn _)]
    exact hsq'
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hB
theorem near_coordinate_sign_small_ball_with_remainder
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (q : ι → ℕ) (a : ∀ i, Fin (q i) → ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j l, |a i j l - (if i = l then 1 else 0)| ≤ ε)
    (b : β → ι → ℝ) (F : Finset ((∀ i, Finset (Fin (q i))) × β)) (z : ι → ℝ)
    (hF : ∀ p ∈ F, ∀ l, |signSum q a p.1 l + b p.2 l - z l| ≤ 1 / 2)
    (c n : ℝ) (hc : 0 < c) (hn : 0 < n) (hq : ∀ i, c * n ≤ (q i : ℝ) + 1) :
    (F.card : ℝ) / (2^(∑ i, q i) * Fintype.card β) ≤
      (2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2) := by
  classical
  let G (y : β) : Finset (∀ i, Finset (Fin (q i))) :=
    (F.filter (fun p => p.2 = y)).image Prod.fst
  have hGcard (y : β) : (G y).card = (F.filter (fun p => p.2 = y)).card := by
    apply card_image_of_injOn
    intro p hp p' hp' h
    exact Prod.ext h ((mem_filter.mp hp).2.trans (mem_filter.mp hp').2.symm)
  have hG (y : β) : (G y).card / (2 : ℝ)^(∑ i, q i) ≤
      (2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2) := by
    apply near_coordinate_sign_small_ball q a ε hε hεr ha (G y)
      (fun l => z l - b y l) _ c n hc hn hq
    intro s hs l
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
    have hpy := (mem_filter.mp hp).2
    have h := hF p (mem_filter.mp hp).1 l
    rw [hpy] at h
    convert! h using 2; ring
  have hsum : (F.card : ℝ) = ∑ y, ((G y).card : ℝ) := by
    have h := card_eq_sum_card_fiberwise
      (s := F) (t := (univ : Finset β)) (f := Prod.snd) (by simp)
    simp only [← hGcard] at h
    exact_mod_cast h
  have hp : (0 : ℝ) < 2^(∑ i, q i) := by positivity
  have hb : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (mul_pos hp hb), hsum]
  calc
    _ ≤ ∑ _y : β, (2 / (c * n)) ^ ((Fintype.card ι : ℝ) / 2) *
        (2 : ℝ)^(∑ i, q i) := by
      apply sum_le_sum
      intro y hy
      exact (div_le_iff₀ hp).mp (hG y)
    _ = _ := by simp; ring
end Fluctuations.SignVectorSmallBall
end

section
open Finset
open scoped BigOperators
namespace Fluctuations.BoundedGramSignSmallBall
variable {α ι E : Type*} [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]
theorem disjoint_group_sign_small_ball
    (J : ι → Finset α) (hJ : ∀ i j, i ≠ j → Disjoint (J i) (J j))
    (a : α → ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hεr : ε * Fintype.card ι ≤ 1 / 4)
    (ha : ∀ i j, j ∈ J i → ∀ l, |a j l - (if i = l then 1 else 0)| ≤ ε)
    (F : Finset (Finset α)) (z : ι → ℝ)
    (hF : ∀ S ∈ F, ∀ l, |(∑ j, if j ∈ S then a j l else -a j l) - z l| ≤ 1/2)
    (c n : ℝ) (hc : 0 < c) (hn : 0 < n)
    (hq : ∀ i, c*n ≤ (J i).card + 1) :
    (F.card : ℝ) / 2^(Fintype.card α) ≤
      (2/(c*n)) ^ ((Fintype.card ι : ℝ)/2) := by
  classical
  let U : Finset α := univ.biUnion J
  let R : Finset α := Uᶜ
  let q : ι → ℕ := fun i => (J i).card
  let e (i : ι) : Fin (q i) ≃ J i := (J i).equivFin.symm
  let encode (S : Finset α) : (∀ i, Finset (Fin (q i))) × Finset R :=
    (fun i => univ.filter (fun k => (e i k).val ∈ S), S.subtype (· ∈ R))
  have hinj : Function.Injective encode := by
    intro S T h
    ext j
    by_cases hj : j ∈ U
    · obtain ⟨i, _, hji⟩ := mem_biUnion.mp hj
      let k := (e i).symm ⟨j, hji⟩
      have hk : (e i k).val = j := by simp [k]
      have he := congrArg (fun p => k ∈ p.1 i) h
      simpa [encode, hk] using he
    · have hjR : j ∈ R := by simpa [R] using hj
      have he := congrArg (fun p => (⟨j, hjR⟩ : R) ∈ p.2) h
      simpa [encode] using he
  have hpair : ((univ : Finset ι) : Set ι).PairwiseDisjoint J := by
    intro i _ j _ hij
    exact hJ i j hij
  have hcard : (∑ i, q i) + R.card = Fintype.card α := by
    have hU : U.card = ∑ i, q i := by simpa [U, q] using card_biUnion hpair
    simpa only [R, hU] using card_add_card_compl U
  let a' (i : ι) (k : Fin (q i)) (l : ι) := a (e i k).val l
  let b (S : Finset R) (l : ι) := ∑ j : R, if j ∈ S then a j.val l else -a j.val l
  have hsum (S : Finset α) (l : ι) :
      SignVectorSmallBall.signSum q a' (encode S).1 l + b (encode S).2 l =
        ∑ j, if j ∈ S then a j l else -a j l := by
    rw [SignVectorSmallBall.signSum_eq_sum_ite]
    have hi (i : ι) :
        (∑ k, if k ∈ (encode S).1 i then a' i k l else -a' i k l) =
          ∑ j ∈ J i, if j ∈ S then a j l else -a j l := by
      simp only [encode, mem_filter, mem_univ, true_and, a']
      rw [(e i).sum_comp (fun j => if j.val ∈ S then a j.val l else -a j.val l)]
      exact sum_coe_sort (J i) (fun j => if j ∈ S then a j l else -a j l)
    simp only [hi]
    have hb : b (encode S).2 l = ∑ j ∈ R, if j ∈ S then a j l else -a j l := by
      simp only [b, encode, mem_subtype]
      exact sum_coe_sort R (fun j => if j ∈ S then a j l else -a j l)
    rw [hb, ← sum_biUnion hpair]
    exact sum_add_sum_compl U _
  have hbound := SignVectorSmallBall.near_coordinate_sign_small_ball_with_remainder
    q a' ε hε hεr (fun i k l => ha i (e i k).val (e i k).property l)
    b (F.image encode) z (by
      intro p hp l
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hp
      rw [hsum]
      exact hF S hS l) c n hc hn hq
  have hden : (2 : ℝ)^(∑ i, q i) * Fintype.card (Finset R) =
      2^(Fintype.card α) := by
    rw [Fintype.card_finset, Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_add, hcard]
  rw [hden, card_image_of_injective _ hinj] at hbound
  exact hbound
def vectorSignSum [AddCommGroup E] (a : α → E) (S : Finset α) : E :=
  ∑ j, if j ∈ S then a j else -a j
theorem exists_bounded_gram_sign_small_ball
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℕ) (hr : 0 < r) (hdim : Module.finrank ℝ E = r)
    (C0 K κ : ℝ) (hC0 : 0 < C0) (hK : 0 < K) (hκ : 0 < κ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (m : ℕ) (n : ℝ) (a : Fin m → E) (z : E), 0 < n →
        (m : ℝ) ≤ C0*n → (∀ j, ‖a j‖ ≤ K) →
        (∀ u : E, κ*n*‖u‖^2 ≤ ∑ j, (inner ℝ (a j) u)^2) →
        (((univ : Finset (Finset (Fin m))).filter
          (fun S => ‖vectorSignSum a S - z‖ ≤ ρ)).card : ℝ) / 2^m ≤
          C * n^(-(r : ℝ)/2) := by
  classical
  obtain ⟨c, T, hc, hT, hextract⟩ :=
    GramGroupExtraction.exists_near_coordinate_groups (E := E)
      r hr hdim C0 K κ hC0 hK hκ
  refine ⟨1/(8*T), (2/c)^((r : ℝ)/2), by positivity, by positivity, ?_⟩
  intro m n a z hn hm ha hgram
  obtain ⟨J, L, hsize, hdisj, hL, hnear⟩ := hextract m n a hn hm ha hgram
  let F : Finset (Finset (Fin m)) :=
    univ.filter (fun S => ‖vectorSignSum a S - z‖ ≤ 1/(8*T))
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoord (S : Finset (Fin m)) (hS : S ∈ F) (l : Fin r) :
      |(∑ j, if j ∈ S then (L (a j)) l else -(L (a j)) l) - (L z) l| ≤ 1/2 := by
    have hnorm := (mem_filter.mp hS).2
    let f : E →L[ℝ] ℝ := (EuclideanSpace.proj l).comp L.toContinuousLinearMap
    have he : (L (vectorSignSum a S - z)) l =
        (∑ j, if j ∈ S then (L (a j)) l else -(L (a j)) l) - (L z) l := by
      change f (vectorSignSum a S - z) = _
      simp only [map_sub, vectorSignSum, map_sum, apply_ite, map_neg]
      rfl
    have hsmall := PiLp.norm_apply_le (L (vectorSignSum a S - z)) l
    rw [he, Real.norm_eq_abs] at hsmall
    apply hsmall.trans
    calc
      ‖L (vectorSignSum a S - z)‖ ≤
          ‖L.toContinuousLinearMap‖ * ‖vectorSignSum a S - z‖ :=
        L.toContinuousLinearMap.le_opNorm _
      _ ≤ T * (1/(8*T)) := mul_le_mul hL hnorm (norm_nonneg _) hT.le
      _ ≤ 1/2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 8*T)]
        linarith
  have hbound := disjoint_group_sign_small_ball J hdisj (fun j l => (L (a j)) l)
    (1/(4*(r : ℝ))) (by positivity) (by
      simp only [Fintype.card_fin]
      field_simp
      norm_num)
    hnear F (fun l => (L z) l) hcoord c n hc hn (fun i => by linarith [hsize i])
  have hscale : (2/(c*n))^((r : ℝ)/2) =
      (2/c)^((r : ℝ)/2) * n^(-(r : ℝ)/2) := by
    rw [show 2/(c*n) = (2/c)/n by ring, Real.div_rpow (by positivity) hn.le,
      show -(r : ℝ)/2 = -((r : ℝ)/2) by ring, Real.rpow_neg hn.le, div_eq_mul_inv]
  simpa only [Fintype.card_fin, hscale] using hbound
end Fluctuations.BoundedGramSignSmallBall
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Fluctuations.GaussianComplex
noncomputable section
variable {ι : Type*} [Fintype ι]
def linearForm (b : ι → ℂ) (x : ι → ℝ) : ℂ := ∑ i, b i * (x i : ℂ)
lemma norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  have hn := congrArg norm (Complex.two_sin (x := z))
  simp only [norm_mul, Complex.norm_I, mul_one] at hn
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at h
  norm_num at hn
  simp only [neg_mul] at h
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith
lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  have hn := congrArg norm (Complex.two_cos (x := z))
  simp only [norm_mul] at hn
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at h
  norm_num at hn
  simp only [neg_mul] at h
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith
lemma norm_trig_sq_le_exp_two_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 ≤ Real.exp (2 * |z.im|) ∧
    ‖Complex.cos z‖ ^ 2 ≤ Real.exp (2 * |z.im|) := by
  have hs := sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le |>.mpr (norm_sin_le_exp_abs_im z)
  have hc := sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le |>.mpr (norm_cos_le_exp_abs_im z)
  rw [← Real.exp_nat_mul] at hs hc
  norm_num at hs hc
  exact ⟨hs, hc⟩
lemma abs_scaledFrequency_le_half {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) :
    |centeredFrequency n j / n| ≤ (1 : ℝ) / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hj : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  rw [abs_div, abs_of_pos hn', div_le_iff₀ hn', abs_le]
  unfold centeredFrequency
  constructor <;> nlinarith [show (0 : ℝ) ≤ j.val from Nat.cast_nonneg _]
lemma norm_scaled_trig_sq_le {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) (z : ℂ) :
    ‖Complex.sin ((centeredFrequency n j / n : ℝ) * z)‖ ^ 2 ≤ Real.exp |z.im| ∧
    ‖Complex.cos ((centeredFrequency n j / n : ℝ) * z)‖ ^ 2 ≤ Real.exp |z.im| := by
  have hh : 2 * |(((centeredFrequency n j / n : ℝ) : ℂ) * z).im| ≤ |z.im| := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
    have h := mul_le_mul_of_nonneg_right (abs_scaledFrequency_le_half hn j) (abs_nonneg z.im)
    linarith
  exact ⟨(norm_trig_sq_le_exp_two_abs_im _).1.trans (Real.exp_le_exp.mpr hh),
    (norm_trig_sq_le_exp_two_abs_im _).2.trans (Real.exp_le_exp.mpr hh)⟩
def scaledSineField (n : ℕ) (x : Fin (n + 1) → ℝ) (z : ℂ) : ℂ :=
  linearForm (fun j => Complex.sin ((centeredFrequency n j / n : ℝ) * z) / (Real.sqrt n : ℂ)) x
lemma differentiable_scaledSineField (n : ℕ) (x : Fin (n + 1) → ℝ) :
    Differentiable ℂ (scaledSineField n x) := by
  unfold scaledSineField linearForm
  fun_prop
lemma scaledSineField_ofReal (n : ℕ) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    scaledSineField n x (t : ℂ) = (centeredSineSum n x (t / n) / Real.sqrt n : ℝ) := by
  simp only [scaledSineField, linearForm, centeredSineSum, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : ((centeredFrequency n j / n : ℝ) : ℂ) * (t : ℂ) =
      (centeredFrequency n j : ℂ) * (t / n) := by push_cast; ring
  push_cast at he ⊢
  rw [he]
  ring
end
end Fluctuations.GaussianComplex
end

section
noncomputable section
open Finset MeasureTheory ProbabilityTheory Classical
open scoped BigOperators ENNReal
namespace Fluctuations.SignSineEvaluation
open SineEvaluationGram SignPolynomialDivisibility
def signVector {m : ℕ} (S : Finset (Fin m)) (j : Fin m) : ℝ :=
  if j ∈ S then 1 else -1
lemma signVector_injective (m : ℕ) : Function.Injective (@signVector m) := by
  intro S T h
  ext j
  have he := congrFun h j
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp_all [signVector] <;> norm_num at he
lemma image_signVector (m : ℕ) :
    (univ : Finset (Finset (Fin m))).image signVector = signVectors m := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨S, _, rfl⟩ := mem_image.mp ha
    exact (mem_signVectors _).mpr (fun j => by
      by_cases hj : j ∈ S <;> simp [signVector, hj])
  · intro ha
    refine mem_image.mpr ⟨univ.filter (fun j => a j = 1), mem_univ _, ?_⟩
    funext j
    rcases (mem_signVectors _).mp ha j with hj | hj <;> norm_num [signVector, hj]
lemma card_sign_property (m : ℕ) (P : (Fin m → ℝ) → Prop) :
    ((signVectors m).filter P).card =
      ((univ : Finset (Finset (Fin m))).filter (fun S => P (signVector S))).card := by
  classical
  rw [← image_signVector m, filter_image, card_image_of_injective _ (signVector_injective m)]
theorem finite_sign_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ) (P : (Fin m → ℝ) → Prop) :
    Prob μ {ω | P (fun j => ξ j.val ω)} =
      (((univ : Finset (Finset (Fin m))).filter
        (fun S => P (signVector S))).card : ℝ) / 2^m := by
  classical
  unfold Prob
  rw [finite_sign_event_measure μ ξ hξ m P, card_sign_property]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, div_eq_mul_inv]
def evaluation (n : ℕ) (a : Fin (n+1) → ℝ) (x : ℝ) : EuclideanSpace ℝ (Fin 8) :=
  ∑ j, a j • coefficient n x j
lemma evaluation_apply (n : ℕ) (a : Fin (n+1) → ℝ) (x : ℝ) (i : Fin 8) :
    evaluation n a x i = centeredSineSum n a ((x+offset i)/n) := by
  change (EuclideanSpace.proj i) (∑ j, a j • coefficient n x j) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, centeredSineSum]
  rfl
lemma vectorSignSum_eq_evaluation (n : ℕ) (x : ℝ) (S : Finset (Fin (n+1))) :
    BoundedGramSignSmallBall.vectorSignSum (coefficient n x) S =
      evaluation n (signVector S) x := by
  unfold BoundedGramSignSmallBall.vectorSignSum evaluation
  apply sum_congr rfl
  intro j _
  by_cases hj : j ∈ S <;> simp [signVector, hj]
lemma evaluation_apply_norm (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (x : ℝ) (i : Fin 8) :
    |evaluation n a x i| = Real.sqrt n *
      ‖GaussianComplex.scaledSineField n a ((x+offset i : ℝ) : ℂ)‖ := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  rw [evaluation_apply, GaussianComplex.scaledSineField_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  field_simp
lemma norm_le_eight_mul (u : EuclideanSpace ℝ (Fin 8)) (b : ℝ) (hb : 0 ≤ b)
    (hu : ∀ i, |u i| ≤ b) : ‖u‖ ≤ 8*b := by
  have hsq : ‖u‖^2 ≤ 8*b^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 8, b^2 := by
        apply sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hu i) 2
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 8*b)).mp
  nlinarith [sq_nonneg b]
theorem exists_evaluation_small_ball :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ n : ℕ, 0 < n → 256*(1+23*Real.pi) ≤ (n : ℝ) →
      ∀ x : ℝ, AdmissibleBase n x →
      (((univ : Finset (Finset (Fin (n+1)))).filter
        (fun S => ‖evaluation n (signVector S) x‖ ≤ ρ)).card : ℝ) / 2^(n+1) ≤
          C*(n : ℝ)^(-4 : ℝ) := by
  obtain ⟨ρ, C, hρ, hC, h⟩ := BoundedGramSignSmallBall.exists_bounded_gram_sign_small_ball
    (E := EuclideanSpace ℝ (Fin 8)) 8 (by norm_num) (by simp)
    2 8 (1/4) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro n hn hlarge x hx
  have hcount : ((n+1 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (show n+1 ≤ 2*n by omega)
  have h' := h (n+1) n (coefficient n x) 0 (Nat.cast_pos.mpr hn) hcount
    (coefficient_norm_le n x) (coefficient_gram_lower n hn hlarge x hx)
  simpa only [sub_zero, vectorSignSum_eq_evaluation, Nat.cast_ofNat,
    show -(8 : ℝ)/2 = -4 by norm_num] using h'
end Fluctuations.SignSineEvaluation
end
end

section
open MeasureTheory MeromorphicOn Metric
namespace Fluctuations
noncomputable section
theorem localJensen_le_of_size_bounds {f : ℂ → ℂ} {c : ℂ} {r R M s : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (hupper : M ≤ Real.exp s) (hlower : Real.exp (-s) ≤ ‖f c‖) :
    ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
      2 * s / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hc : 0 < ‖f c‖ := (Real.exp_pos _).trans_le hlower
  have hJ := AnalyticOnNhd.sum_divisor_le (f := f) (c := c)
    (r := r) (R := R) (M := M) (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hR] using hrR) hM
    (by simpa [abs_of_pos hR] using hf) (norm_pos_iff.mp hc)
    (by simpa [abs_of_pos hR] using hbound)
  have hlogM : Real.log M ≤ s := by
    simpa using Real.log_le_log (by linarith : 0 < M) hupper
  have hlogc : -s ≤ Real.log ‖f c‖ := by
    simpa using Real.log_le_log (Real.exp_pos _) hlower
  rw [abs_of_pos hr, Real.log_div (by linarith : M ≠ 0) hc.ne'] at hJ
  exact hJ.trans (div_le_div_of_nonneg_right
    (show Real.log M - Real.log ‖f c‖ ≤ 2 * s by linarith)
    (Real.log_pos ((one_lt_div hr).mpr hrR)).le)
end
end Fluctuations
end

section
open MeromorphicOn MeasureTheory Metric
open scoped BigOperators
namespace Fluctuations.AnalyticZeroCount
noncomputable section
lemma divisor_ge_one_of_zero {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hne : f ≠ 0) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) (hfz : f z = 0) :
    (1 : ℤ) ≤ divisor f U z := by
  have hntop : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    exact hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf).mp htop)
  have hnzero : analyticOrderAt f z ≠ 0 := (hf z).analyticOrderAt_ne_zero.mpr hfz
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    exact hnzero hk.symm
  have hU : AnalyticOnNhd ℂ f U := fun w _ => hf w
  rw [hU.divisor_apply hz, ← hk]
  change (1 : ℤ) ≤ (k : ℤ)
  exact_mod_cast hkpos
lemma finite_zeros_in_compact {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hne : f ≠ 0) {U : Set ℂ} (hU : IsCompact U) :
    Set.Finite {z | z ∈ U ∧ f z = 0} := by
  apply ((divisor f U).finiteSupport hU).subset
  intro z hz
  change divisor f U z ≠ 0
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) (divisor_ge_one_of_zero hf hne hz.1 hz.2))
lemma finite_real_zeros_in_compact {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hne : f ≠ 0) {U : Set ℂ} (hU : IsCompact U) :
    Set.Finite {t : ℝ | (t : ℂ) ∈ U ∧ f (t : ℂ) = 0} :=
  (finite_zeros_in_compact hf hne hU).preimage Complex.ofReal_injective.injOn
end
end Fluctuations.AnalyticZeroCount
end

section
noncomputable section
open Finset MeasureTheory ProbabilityTheory MeromorphicOn Metric Classical
open scoped BigOperators ENNReal
namespace Fluctuations.SignSineOccupancy
open SineEvaluationGram SignSineEvaluation SignPolynomialDivisibility
def diskMultiplicity (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℤ :=
  ∑ᶠ z, divisor f (closedBall c r) z
lemma divisor_sum_mono {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {U V : Set ℂ} (hU : IsCompact U) (hV : IsCompact V) (hUV : U ⊆ V) :
    (∑ᶠ z, divisor f U z) ≤ ∑ᶠ z, divisor f V z := by
  have hfu : AnalyticOnNhd ℂ f U := fun z _ => hf z
  have hfv : AnalyticOnNhd ℂ f V := fun z _ => hf z
  classical
  let T := ((divisor f U).finiteSupport hU).toFinset ∪ ((divisor f V).finiteSupport hV).toFinset
  rw [finsum_eq_sum_of_support_toFinset_subset _ ((divisor f U).finiteSupport hU) (show _ ⊆ T from Finset.subset_union_left),
      finsum_eq_sum_of_support_toFinset_subset _ ((divisor f V).finiteSupport hV) (show _ ⊆ T from Finset.subset_union_right)]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : z ∈ U
  · rw [hfu.meromorphicOn.divisor_apply hz, hfv.meromorphicOn.divisor_apply (hUV hz)]
  · rw [(divisor f U).apply_eq_zero_of_notMem hz]
    exact hfv.divisor_nonneg z
lemma diskMultiplicity_mono {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {c d : ℂ} {r R : ℝ} (h : closedBall c r ⊆ closedBall d R) :
    diskMultiplicity f c r ≤ diskMultiplicity f d R :=
  divisor_sum_mono hf (isCompact_closedBall c r) (isCompact_closedBall d R) h
lemma norm_scaledSineField_le (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (z : ℂ) :
    ‖GaussianComplex.scaledSineField n a z‖ ≤
      2*Real.sqrt n*Real.exp (|z.im|/2) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have htrig (j : Fin (n+1)) :
      ‖Complex.sin ((centeredFrequency n j / n : ℝ)*z)‖ ≤ Real.exp (|z.im|/2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
    have he : Real.exp (|z.im|/2)^2 = Real.exp |z.im| := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    rw [he]
    exact (GaussianComplex.norm_scaled_trig_sq_le hn j z).1
  have hc : ((n : ℝ)+1)/Real.sqrt n ≤ 2*Real.sqrt n := by
    rw [div_le_iff₀ hs]
    nlinarith [Real.sq_sqrt hn0.le]
  unfold GaussianComplex.scaledSineField GaussianComplex.linearForm
  calc
    _ ≤ ∑ j, ‖Complex.sin ((centeredFrequency n j / n : ℝ)*z) /
          (Real.sqrt n : ℂ) * (a j : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (n+1), Real.exp (|z.im|/2)/Real.sqrt n := by
      apply sum_le_sum
      intro j _
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (div_le_div_of_nonneg_right (htrig j) hs.le) (ha j)
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ = (((n : ℝ)+1)/Real.sqrt n)*Real.exp (|z.im|/2) := by simp; ring
    _ ≤ _ := by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hc (Real.exp_pos (|z.im|/2)).le
def endpointCutoff : ℝ := 256*Real.pi+1
def evaluationRadius : ℝ := endpointCutoff+16*Real.pi+1
def jensenScale (n : ℕ) : ℝ := (evaluationRadius+2)*Real.log ((n : ℝ)+2)
def localThreshold (n : ℕ) : ℝ := 2*jensenScale n/Real.log 2
lemma evaluationRadius_pos : 0 < evaluationRadius := by
  dsimp [evaluationRadius, endpointCutoff]
  positivity
lemma disk_subset_evaluation_disk (x r : ℝ) (hr : r ≤ endpointCutoff) (i : Fin 8) :
    closedBall (x : ℂ) r ⊆ closedBall ((x+offset i : ℝ) : ℂ) evaluationRadius := by
  apply closedBall_subset_closedBall'
  have hd : dist (x : ℂ) ((x+offset i : ℝ) : ℂ) = offset i := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hi := (offset_bounds i).1
    rw [show x-(x+offset i) = -(offset i) by ring, abs_neg,
      abs_of_pos (by linarith [Real.pi_pos] : 0 < offset i)]
  rw [hd]
  dsimp [evaluationRadius]
  linarith [(offset_bounds i).2]
lemma log_degree_lower (n : ℕ) (hn : 0 < n) : 1 ≤ Real.log ((n : ℝ)+2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ (n : ℝ)+2 by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using h
lemma majorant_le_exp_jensenScale (n : ℕ) (hn : 0 < n) :
    2*Real.sqrt n*Real.exp evaluationRadius ≤ Real.exp (jensenScale n) := by
  have hlog := log_degree_lower n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ)+2 := by
    nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg (n : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp 1*Real.exp (Real.log ((n : ℝ)+2))*Real.exp evaluationRadius := by
      rw [Real.exp_log (by positivity : 0 < (n : ℝ)+2)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul htwo hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (1+Real.log ((n : ℝ)+2)+evaluationRadius) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp [jensenScale]
      nlinarith [mul_nonneg evaluationRadius_pos.le (sub_nonneg.mpr hlog)]
lemma norm_on_evaluation_sphere (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (x : ℝ) (i : Fin 8) (z : ℂ)
    (hz : z ∈ sphere ((x+offset i : ℝ) : ℂ) (2*evaluationRadius)) :
    ‖GaussianComplex.scaledSineField n a z‖ ≤
      2*Real.sqrt n*Real.exp evaluationRadius := by
  have him : |z.im| ≤ 2*evaluationRadius := by
    have h := Complex.abs_im_le_norm (z-((x+offset i : ℝ) : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    have hd : ‖z-((x+offset i : ℝ) : ℂ)‖ = 2*evaluationRadius := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    exact h.trans_eq hd
  apply (norm_scaledSineField_le n hn a ha z).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
lemma one_le_majorant (n : ℕ) (hn : 0 < n) :
    1 ≤ 2*Real.sqrt n*Real.exp evaluationRadius := by
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    simpa only [Real.sqrt_one] using h
  have he : (1 : ℝ) ≤ Real.exp evaluationRadius :=
    Real.one_le_exp_iff.mpr evaluationRadius_pos.le
  nlinarith
lemma small_values_of_overcrowding (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (x r : ℝ) (hr : r ≤ endpointCutoff)
    (hbad : localThreshold n <
      (diskMultiplicity (GaussianComplex.scaledSineField n a) (x : ℂ) r : ℝ))
    (i : Fin 8) :
    ‖GaussianComplex.scaledSineField n a ((x+offset i : ℝ) : ℂ)‖ <
      Real.exp (-jensenScale n) := by
  by_contra hsmall
  have hJ := localJensen_le_of_size_bounds
    (f := GaussianComplex.scaledSineField n a)
    (c := ((x+offset i : ℝ) : ℂ)) (r := evaluationRadius) (R := 2*evaluationRadius)
    (M := 2*Real.sqrt n*Real.exp evaluationRadius) (s := jensenScale n)
    evaluationRadius_pos (by linarith [evaluationRadius_pos]) (one_le_majorant n hn)
    (fun z _ => (GaussianComplex.differentiable_scaledSineField n a).analyticAt z)
    (norm_on_evaluation_sphere n hn a ha x i)
    (majorant_le_exp_jensenScale n hn) (le_of_not_gt hsmall)
  have hratio : 2*evaluationRadius/evaluationRadius = 2 := by
    field_simp [evaluationRadius_pos.ne']
  rw [hratio] at hJ
  have hmono := diskMultiplicity_mono
    (fun z => (GaussianComplex.differentiable_scaledSineField n a).analyticAt z)
    (disk_subset_evaluation_disk x r hr i)
  have hmono' : (diskMultiplicity (GaussianComplex.scaledSineField n a) (x : ℂ) r : ℝ) ≤
      (diskMultiplicity (GaussianComplex.scaledSineField n a)
        ((x+offset i : ℝ) : ℂ) evaluationRadius : ℝ) := by exact_mod_cast hmono
  exact (not_lt_of_ge (hmono'.trans hJ)) hbad
def diskBad (n : ℕ) (a : Fin (n+1) → ℝ) (x r : ℝ) : Prop :=
  GaussianComplex.scaledSineField n a = 0 ∨
    localThreshold n < (diskMultiplicity (GaussianComplex.scaledSineField n a) (x : ℂ) r : ℝ)
lemma evaluation_norm_of_diskBad (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (x r : ℝ) (hr : r ≤ endpointCutoff)
    (hbad : diskBad n a x r) :
    ‖evaluation n a x‖ ≤ 8*(Real.sqrt n*Real.exp (-jensenScale n)) := by
  apply norm_le_eight_mul _ _ (by positivity)
  intro i
  rw [evaluation_apply_norm n hn a x i]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rcases hbad with hzero | hcount
  · rw [hzero]
    simp only [Pi.zero_apply, norm_zero]
    exact (Real.exp_pos _).le
  · exact (small_values_of_overcrowding n hn a ha x r hr hcount i).le
lemma evaluation_scale_le (n : ℕ) (hn : 0 < n) :
    8*(Real.sqrt n*Real.exp (-jensenScale n)) ≤ 8/Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hlog := log_degree_lower n hn
  have hscale : Real.log ((n : ℝ)+2) ≤ jensenScale n := by
    dsimp [jensenScale]
    nlinarith [mul_nonneg evaluationRadius_pos.le (by linarith :
      0 ≤ Real.log ((n : ℝ)+2))]
  have he : Real.exp (-jensenScale n) ≤ 1/((n : ℝ)+2) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg hscale)
    simpa only [Real.exp_neg, Real.exp_log (by positivity : 0 < (n : ℝ)+2),
      one_div] using h
  calc
    _ ≤ 8*(Real.sqrt n*(1/((n : ℝ)+2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hs.le) (by norm_num)
    _ = (8*Real.sqrt n)/((n : ℝ)+2) := by ring
    _ ≤ 8/Real.sqrt n := by
      rw [div_le_div_iff₀ (by positivity : 0 < (n : ℝ)+2) hs]
      nlinarith [Real.sq_sqrt hn0.le]
lemma evaluation_norm_le_of_diskBad (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (x r ρ : ℝ) (hρ : 0 < ρ)
    (hr : r ≤ endpointCutoff) (hnρ : 64/ρ^2 ≤ (n : ℝ)) (hbad : diskBad n a x r) :
    ‖evaluation n a x‖ ≤ ρ := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : (ρ*Real.sqrt n)^2 = ρ^2*n := by rw [mul_pow, Real.sq_sqrt hn0.le]
  have hlarge : (64 : ℝ) ≤ (n : ℝ)*ρ^2 := (div_le_iff₀ (sq_pos_of_pos hρ)).mp hnρ
  have hprod : (8 : ℝ) ≤ ρ*Real.sqrt n := by nlinarith [mul_pos hρ hs]
  exact ((evaluation_norm_of_diskBad n hn a ha x r hr hbad).trans
    (evaluation_scale_le n hn)).trans ((div_le_iff₀ hs).mpr hprod)
theorem exists_disk_bad_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x : ℝ, AdmissibleBase n x → ∀ r : ℝ, r ≤ endpointCutoff →
      (((univ : Finset (Finset (Fin (n+1)))).filter
        (fun S => diskBad n (signVector S) x r)).card : ℝ) / 2^(n+1) ≤
          C*(n : ℝ)^(-4 : ℝ) := by
  obtain ⟨ρ, C, hρ, hC, hsmall⟩ := exists_evaluation_small_ball
  obtain ⟨n0, hn0⟩ := exists_nat_gt (max (256*(1+23*Real.pi)) (64/ρ^2))
  refine ⟨C, hC, n0, ?_⟩
  intro n hn x hx r hr
  have hncast : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 256*(1+23*Real.pi) ≤ (n : ℝ) :=
    (le_max_left _ _).trans (hn0.le.trans hncast)
  have hnρ : 64/ρ^2 ≤ (n : ℝ) := (le_max_right _ _).trans (hn0.le.trans hncast)
  have hnpos : 0 < n := by
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (by positivity : 0 < 256*(1+23*Real.pi)) hlarge
    exact_mod_cast hp
  apply le_trans _ (hsmall n hnpos hlarge x hx)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro S hS
  exact mem_filter.mpr ⟨mem_univ _, evaluation_norm_le_of_diskBad n hnpos (signVector S)
    (fun j => by by_cases hj : j ∈ S <;> norm_num [signVector, hj]) x r ρ hρ hr hnρ
    (mem_filter.mp hS).2⟩
def cellCenter (k : ℕ) : ℝ := k+1/2
def bulkCells (n : ℕ) : Finset ℕ :=
  (range (Nat.ceil (Real.pi*n)+1)).filter (fun k =>
    cellCenter k ∈ Set.Icc (256*Real.pi) (Real.pi*n-256*Real.pi))
lemma bulkCells_admissible (n k : ℕ) (hk : k ∈ bulkCells n) :
    AdmissibleBase n (cellCenter k) := Or.inr (Or.inr (mem_filter.mp hk).2)
lemma bulkCells_card_le (n : ℕ) (hn : 0 < n) :
    ((bulkCells n).card : ℝ) ≤ (Real.pi+2)*n := by
  have hc : (bulkCells n).card ≤ Nat.ceil (Real.pi*n)+1 := by
    exact (card_le_card (filter_subset _ _)).trans_eq (card_range _)
  have hc' : ((bulkCells n).card : ℝ) ≤ (Nat.ceil (Real.pi*n) : ℝ)+1 := by exact_mod_cast hc
  have he := Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.pi*(n : ℝ))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith
lemma floor_mem_bulkCells (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc endpointCutoff (Real.pi*n-endpointCutoff)) :
    Nat.floor t ∈ bulkCells n := by
  have hb : 0 < endpointCutoff := by dsimp [endpointCutoff]; positivity
  have ht0 : 0 ≤ t := hb.le.trans ht.1
  have hf := Nat.floor_le ht0
  have hf' := Nat.lt_floor_add_one t
  have hc := Nat.le_ceil (Real.pi*(n : ℝ))
  have hnat : Nat.floor t ≤ Nat.ceil (Real.pi*n) := by
    have hh : (Nat.floor t : ℝ) ≤ (Nat.ceil (Real.pi*n) : ℝ) := by linarith [ht.2]
    exact_mod_cast hh
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (by omega), ?_⟩
  dsimp [cellCenter, endpointCutoff] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
lemma real_cell_subset_disk (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k+1)) :
    (t : ℂ) ∈ closedBall (cellCenter k : ℂ) 1 := by
  rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  dsimp [cellCenter]
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
def occupancyBad (n : ℕ) (a : Fin (n+1) → ℝ) : Prop :=
  diskBad n a 0 endpointCutoff ∨ diskBad n a (Real.pi*n) endpointCutoff ∨
    ∃ k ∈ bulkCells n, diskBad n a (cellCenter k) 1
theorem exists_occupancy_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      Prob μ {ω | occupancyBad n (fun j => ξ j.val ω)} ≤ C*(n : ℝ)^(-3 : ℝ) := by
  obtain ⟨C, hC, n0, hlocal⟩ := exists_disk_bad_bound
  refine ⟨(Real.pi+4)*C, by positivity, max n0 1, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by have := (le_max_right n0 1).trans hn; omega
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  let a (ω : Ω) : Fin (n+1) → ℝ := fun j => ξ j.val ω
  have hprob (x : ℝ) (hx : AdmissibleBase n x) (r : ℝ) (hr : r ≤ endpointCutoff) :
      Prob μ {ω | diskBad n (a ω) x r} ≤ C*(n : ℝ)^(-4 : ℝ) := by
    rw [finite_sign_probability μ ξ hξ (n+1) (fun v => diskBad n v x r)]
    exact hlocal n hn0 x hx r hr
  have hzero := hprob 0 (Or.inl rfl) endpointCutoff le_rfl
  have hpi := hprob (Real.pi*n) (Or.inr (Or.inl rfl)) endpointCutoff le_rfl
  have hbulk : Prob μ {ω | ∃ k ∈ bulkCells n, diskBad n (a ω) (cellCenter k) 1} ≤
      (bulkCells n).card*(C*(n : ℝ)^(-4 : ℝ)) := by
    have he : {ω | ∃ k ∈ bulkCells n, diskBad n (a ω) (cellCenter k) 1} =
        ⋃ k ∈ bulkCells n, {ω | diskBad n (a ω) (cellCenter k) 1} := by ext; simp
    rw [he]
    apply (measureReal_biUnion_finset_le (μ := μ) (bulkCells n)
      (fun k => {ω | diskBad n (a ω) (cellCenter k) 1})).trans
    calc
      _ ≤ ∑ _k ∈ bulkCells n, C*(n : ℝ)^(-4 : ℝ) := by
        apply sum_le_sum
        intro k hk
        exact hprob (cellCenter k) (bulkCells_admissible n k hk) 1
          (by dsimp [endpointCutoff]; linarith [Real.pi_pos])
      _ = _ := by simp
  have he : {ω | occupancyBad n (a ω)} =
      {ω | diskBad n (a ω) 0 endpointCutoff} ∪
        ({ω | diskBad n (a ω) (Real.pi*n) endpointCutoff} ∪
          {ω | ∃ k ∈ bulkCells n, diskBad n (a ω) (cellCenter k) 1}) := by
    rfl
  change Prob μ {ω | occupancyBad n (a ω)} ≤ _
  rw [he]
  have hu := measureReal_union_le (μ := μ)
    {ω | diskBad n (a ω) 0 endpointCutoff}
    ({ω | diskBad n (a ω) (Real.pi*n) endpointCutoff} ∪
      {ω | ∃ k ∈ bulkCells n, diskBad n (a ω) (cellCenter k) 1})
  have hu' := measureReal_union_le (μ := μ)
    {ω | diskBad n (a ω) (Real.pi*n) endpointCutoff}
    {ω | ∃ k ∈ bulkCells n, diskBad n (a ω) (cellCenter k) 1}
  apply hu.trans
  apply (add_le_add le_rfl hu').trans
  apply (add_le_add hzero (add_le_add hpi hbulk)).trans
  have hcard : ((bulkCells n).card : ℝ)+2 ≤ (Real.pi+4)*n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    nlinarith [bulkCells_card_le n hnpos]
  calc
    _ = (((bulkCells n).card : ℝ)+2)*(C*(n : ℝ)^(-4 : ℝ)) := by ring
    _ ≤ ((Real.pi+4)*n)*(C*(n : ℝ)^(-4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((Real.pi+4)*C)*((n : ℝ)*(n : ℝ)^(-4 : ℝ)) := by ring
    _ = _ := by
      have hp : (n : ℝ)*(n : ℝ)^(-4 : ℝ) = (n : ℝ)^(-3 : ℝ) := by
        simpa only [Real.rpow_one, show (1 : ℝ)+(-4) = -3 by norm_num] using
          (Real.rpow_add hnreal 1 (-4)).symm
      rw [hp]
def realIntervalMultiplicity (f : ℂ → ℂ) (a b : ℝ) : ℤ :=
  ∑ᶠ z, divisor f (Complex.ofReal '' Set.Icc a b) z
lemma realIntervalMultiplicity_le_disk {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (a b : ℝ) (c : ℂ) (r : ℝ)
    (h : ∀ t ∈ Set.Icc a b, (t : ℂ) ∈ closedBall c r) :
    realIntervalMultiplicity f a b ≤ diskMultiplicity f c r := by
  apply divisor_sum_mono hf (isCompact_Icc.image Complex.continuous_ofReal)
    (isCompact_closedBall c r)
  rintro z ⟨t, ht, rfl⟩
  exact h t ht
lemma real_interval_zeros_finite {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hne : f ≠ 0) (a b : ℝ) :
    Set.Finite {t : ℝ | t ∈ Set.Icc a b ∧ f (t : ℂ) = 0} := by
  apply (AnalyticZeroCount.finite_real_zeros_in_compact hf hne
    (isCompact_Icc.image Complex.continuous_ofReal)).subset
  intro t ht
  exact ⟨⟨t, ht.1, rfl⟩, ht.2⟩
lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [hf.divisor_apply hz]
  cases ho : analyticOrderAt f z <;> simp [analyticOrderNatAt, ho]
theorem not_occupancyBad_spec (n : ℕ) (a : Fin (n+1) → ℝ) (hg : ¬occupancyBad n a) :
    GaussianComplex.scaledSineField n a ≠ 0 ∧
    (∀ k ∈ bulkCells n,
      (realIntervalMultiplicity (GaussianComplex.scaledSineField n a) k (k+1) : ℝ) ≤
        localThreshold n) ∧
    ((realIntervalMultiplicity (GaussianComplex.scaledSineField n a) 0 endpointCutoff +
      realIntervalMultiplicity (GaussianComplex.scaledSineField n a)
        (Real.pi*n-endpointCutoff) (Real.pi*n) : ℤ) : ℝ) ≤ 2*localThreshold n := by
  have hzero : ¬diskBad n a 0 endpointCutoff := fun h => hg (Or.inl h)
  have hpi : ¬diskBad n a (Real.pi*n) endpointCutoff := fun h => hg (Or.inr (Or.inl h))
  have han : ∀ z, AnalyticAt ℂ (GaussianComplex.scaledSineField n a) z := fun z =>
    (GaussianComplex.differentiable_scaledSineField n a).analyticAt z
  refine ⟨(fun h => hzero (Or.inl h)), ?_, ?_⟩
  · intro k hk
    have hcount : (diskMultiplicity (GaussianComplex.scaledSineField n a) (cellCenter k : ℂ) 1 : ℝ) ≤
        localThreshold n := le_of_not_gt (fun h => hg (Or.inr (Or.inr ⟨k, hk, Or.inr h⟩)))
    have hm := realIntervalMultiplicity_le_disk han k (k+1) (cellCenter k : ℂ) 1
      (real_cell_subset_disk k)
    exact (show (realIntervalMultiplicity (GaussianComplex.scaledSineField n a) k (k+1) : ℝ) ≤
      (diskMultiplicity (GaussianComplex.scaledSineField n a) (cellCenter k : ℂ) 1 : ℝ) by
      exact_mod_cast hm).trans hcount
  · have h0count : (diskMultiplicity (GaussianComplex.scaledSineField n a) 0 endpointCutoff : ℝ) ≤
        localThreshold n := le_of_not_gt (fun h => hzero (Or.inr h))
    have hpicount : (diskMultiplicity (GaussianComplex.scaledSineField n a)
        ((Real.pi*n : ℝ) : ℂ) endpointCutoff : ℝ) ≤
        localThreshold n := le_of_not_gt (fun h => hpi (Or.inr h))
    have h0 := realIntervalMultiplicity_le_disk han 0 endpointCutoff 0 endpointCutoff (by
      intro t ht
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2)
    have hp := realIntervalMultiplicity_le_disk han (Real.pi*n-endpointCutoff) (Real.pi*n)
      ((Real.pi*n : ℝ) : ℂ) endpointCutoff (by
        intro t ht
        rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [ht.1], by
          have hb : 0 < endpointCutoff := by dsimp [endpointCutoff]; positivity
          linarith [ht.2]⟩)
    have h0' : (realIntervalMultiplicity (GaussianComplex.scaledSineField n a) 0 endpointCutoff : ℝ) ≤
        (diskMultiplicity (GaussianComplex.scaledSineField n a) 0 endpointCutoff : ℝ) := by exact_mod_cast h0
    have hp' : (realIntervalMultiplicity (GaussianComplex.scaledSineField n a)
        (Real.pi*n-endpointCutoff) (Real.pi*n) : ℝ) ≤
        (diskMultiplicity (GaussianComplex.scaledSineField n a)
        ((Real.pi*n : ℝ) : ℂ) endpointCutoff : ℝ) := by exact_mod_cast hp
    push_cast
    linarith
end Fluctuations.SignSineOccupancy
end
end

section
noncomputable section
open Finset Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Fluctuations.SignActivityFiber
open SignPolynomialDivisibility SignNoncyclotomicAssembly GaussianComplex
def freeIndices (n : ℕ) (a : Fin (n+1) → ℝ) : Finset (Fin (n+1)) :=
  univ.filter (fun j => j ≤ j.rev ∧ a j = a j.rev)
def sameSineFiber (n : ℕ) (a b : Fin (n+1) → ℝ) : Prop :=
  ∀ j, b j - b j.rev = a j - a j.rev
def fillFree (n : ℕ) (a : Fin (n+1) → ℝ)
    (v : {j // j ∈ freeIndices n a} → ℝ) (j : Fin (n+1)) : ℝ :=
  if h : j ∈ freeIndices n a then v ⟨j,h⟩
  else if h : j.rev ∈ freeIndices n a then v ⟨j.rev,h⟩ else a j
lemma middle_mem_freeIndices (n : ℕ) (a : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (hj : j = j.rev) : j ∈ freeIndices n a := by
  simp [freeIndices, ← hj]
lemma fillFree_at_free (n : ℕ) (a : Fin (n+1) → ℝ)
    (v : {j // j ∈ freeIndices n a} → ℝ) (j : {j // j ∈ freeIndices n a}) :
    fillFree n a v j.val = v j := by
  simp [fillFree, j.property]
lemma fillFree_signs (n : ℕ) (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1))
    (v : {j // j ∈ freeIndices n a} → ℝ) (hv : ∀ j, v j = 1 ∨ v j = -1) :
    fillFree n a v ∈ signVectors (n+1) := by
  apply (mem_signVectors _).mpr
  intro j
  unfold fillFree
  split_ifs
  · exact hv _
  · exact hv _
  · exact (mem_signVectors _).mp ha j
lemma fillFree_sameSineFiber (n : ℕ) (a : Fin (n+1) → ℝ)
    (v : {j // j ∈ freeIndices n a} → ℝ) :
    sameSineFiber n a (fillFree n a v) := by
  intro j
  by_cases hj : j = j.rev
  · simp only [← hj, sub_self]
  by_cases hfree : j ∈ freeIndices n a
  · have haeq := (mem_filter.mp hfree).2.2
    have hnot : j.rev ∉ freeIndices n a := by
      intro hr
      exact hj (le_antisymm (mem_filter.mp hfree).2.1
        (by simpa only [Fin.rev_rev] using (mem_filter.mp hr).2.1))
    simp only [fillFree, hfree, hnot, dite_true, dite_false, Fin.rev_rev, sub_self, haeq]
  · by_cases hr : j.rev ∈ freeIndices n a
    · have haeq := (mem_filter.mp hr).2.2
      simp only [Fin.rev_rev] at haeq
      simp only [fillFree, hfree, hr, dite_true, dite_false, Fin.rev_rev, sub_self, haeq]
    · simp only [fillFree, hfree, hr, dite_false, Fin.rev_rev]
lemma fillFree_injective (n : ℕ) (a : Fin (n+1) → ℝ) :
    Function.Injective (fillFree n a) := by
  intro v w h
  funext j
  simpa only [fillFree_at_free] using congrFun h j.val
lemma fiber_eq_of_free_eq (n : ℕ) (a b c : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) (hb : b ∈ signVectors (n+1))
    (hc : c ∈ signVectors (n+1))
    (hab : sameSineFiber n a b) (hac : sameSineFiber n a c)
    (he : ∀ j ∈ freeIndices n a, b j = c j) : b = c := by
  have ha' := (mem_signVectors a).mp ha
  have hb' := (mem_signVectors b).mp hb
  have hc' := (mem_signVectors c).mp hc
  funext j
  by_cases hja : a j = a j.rev
  · have hbj : b j = b j.rev := by linarith [hab j]
    have hcj : c j = c j.rev := by linarith [hac j]
    rcases le_total j j.rev with hj | hj
    · exact he j (by simp [freeIndices, hj, hja])
    · rw [hbj, hcj]
      exact he j.rev (by simpa [freeIndices] using And.intro hj hja.symm)
  · obtain ⟨hba, _⟩ := unequal_sign_pair_fixed _ _ _ _
      (ha' j) (ha' j.rev) (hb' j) (hb' j.rev) hja (hab j)
    obtain ⟨hca, _⟩ := unequal_sign_pair_fixed _ _ _ _
      (ha' j) (ha' j.rev) (hc' j) (hc' j.rev) hja (hac j)
    exact hba.trans hca.symm
lemma fillFree_image_eq_fiber (n : ℕ) (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) :
    (Fintype.piFinset (fun _ : {j // j ∈ freeIndices n a} => ({1,-1} : Finset ℝ))).image
      (fillFree n a) = (signVectors (n+1)).filter (sameSineFiber n a) := by
  ext b
  constructor
  · intro hb
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
    apply mem_filter.mpr
    exact ⟨fillFree_signs n a ha v (by simpa [Fintype.mem_piFinset] using hv),
      fillFree_sameSineFiber n a v⟩
  · intro hb
    obtain ⟨hb,hf⟩ := mem_filter.mp hb
    let v : {j // j ∈ freeIndices n a} → ℝ := fun j => b j.val
    have hv : ∀ j, v j = 1 ∨ v j = -1 := fun j => (mem_signVectors _).mp hb j.val
    refine mem_image.mpr ⟨v, by simpa [Fintype.mem_piFinset] using hv, ?_⟩
    exact fiber_eq_of_free_eq n a _ b ha (fillFree_signs n a ha v hv) hb
      (fillFree_sameSineFiber n a v) hf (fun j hj => fillFree_at_free n a v ⟨j,hj⟩)
lemma card_sine_fiber (n : ℕ) (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) :
    ((signVectors (n+1)).filter (sameSineFiber n a)).card =
      2 ^ (freeIndices n a).card := by
  rw [← fillFree_image_eq_fiber n a ha,
    card_image_of_injective _ (fillFree_injective n a)]
  norm_num [Fintype.card_piFinset]
lemma average_on_sine_fiber (n : ℕ) (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) (g : (Fin (n+1) → ℝ) → ℝ) :
    (∑ b ∈ (signVectors (n+1)).filter (sameSineFiber n a), g b) /
        ((signVectors (n+1)).filter (sameSineFiber n a)).card =
      (∑ v ∈ Fintype.piFinset (fun _ : {j // j ∈ freeIndices n a} =>
          ({1,-1} : Finset ℝ)), g (fillFree n a v)) / (2 : ℝ)^(freeIndices n a).card := by
  rw [card_sine_fiber n a ha, ← fillFree_image_eq_fiber n a ha,
    sum_image (fun _ _ _ _ h => fillFree_injective n a h)]
  norm_num
lemma sameSineFiber_symm (n : ℕ) (a b : Fin (n+1) → ℝ)
    (h : sameSineFiber n a b) : sameSineFiber n b a := fun j => (h j).symm
lemma freeIndices_eq_of_sameSineFiber (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hab : sameSineFiber n a b) : freeIndices n a = freeIndices n b := by
  ext j
  have h : a j = a j.rev ↔ b j = b j.rev := by constructor <;> intro hj <;> linarith [hab j]
  simp only [freeIndices, mem_filter, mem_univ, true_and, h]
lemma antisymmetric_linearForm_eq (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hab : sameSineFiber n a b) (w : Fin (n+1) → ℂ)
    (hw : ∀ j, w j.rev = -w j) : linearForm w b = linearForm w a := by
  have hrev (c : Fin (n+1) → ℝ) :
      (∑ j, w j * (c j.rev : ℂ)) = -(∑ j, w j * (c j : ℂ)) := by
    have hr := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n+1)))
      (fun j => w j * (c j.rev : ℂ))
    simpa only [Fin.revPerm_apply, Fin.rev_rev, hw, neg_mul, sum_neg_distrib] using hr.symm
  have hd (c : Fin (n+1) → ℝ) :
      (∑ j, w j * ((c j-c j.rev : ℝ) : ℂ)) = 2*linearForm w c := by
    simp only [Complex.ofReal_sub, mul_sub, sum_sub_distrib, hrev, linearForm]
    ring
  have he : (∑ j, w j * ((b j-b j.rev : ℝ) : ℂ)) =
      ∑ j, w j * ((a j-a j.rev : ℝ) : ℂ) := sum_congr rfl (fun j _ => by rw [hab j])
  rw [hd, hd] at he
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he
lemma scaledSineField_eq_of_sameSineFiber (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hab : sameSineFiber n a b) : scaledSineField n b = scaledSineField n a := by
  funext z
  apply antisymmetric_linearForm_eq n a b hab
  intro j
  simp only [centeredFrequency_rev, neg_div, Complex.ofReal_neg, neg_mul, Complex.sin_neg]
lemma occupancyBad_congr (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hab : sameSineFiber n a b) :
    SignSineOccupancy.occupancyBad n b ↔ SignSineOccupancy.occupancyBad n a := by
  unfold SignSineOccupancy.occupancyBad SignSineOccupancy.diskBad
  rw [scaledSineField_eq_of_sameSineFiber n a b hab]
end Fluctuations.SignActivityFiber
end
end

section
open MeasureTheory Polynomial Complex
open scoped BigOperators
namespace Fluctuations.PolynomialCircle
noncomputable section
lemma norm_phaseFactor (n : ℕ) (t : ℝ) : ‖phaseFactor n t‖ = 1 := by
  simp [phaseFactor, phaseVelocity, Complex.norm_exp, Complex.mul_re]
lemma norm_rotatedCircleCurve (n : ℕ) (p : Polynomial ℂ) (t : ℝ) :
    ‖rotatedCircleCurve n p t‖ = ‖p.eval (circleMap 0 1 t)‖ := by
  rw [rotatedCircleCurve, norm_mul, norm_phaseFactor, one_mul]
  rfl
lemma integral_norm_sq_rotatedCircleCurve (n : ℕ) (p : Polynomial ℂ) :
    (∫ t in 0..2 * Real.pi, ‖rotatedCircleCurve n p t‖ ^ 2) =
      (2 * Real.pi) * ∑ k ∈ p.support, ‖p.coeff k‖ ^ 2 := by
  simp_rw [norm_rotatedCircleCurve]
  have h := p.sum_sq_norm_coeff_eq_circleAverage
  rw [Real.circleAverage_def, smul_eq_mul] at h
  rw [h]
  exact (mul_inv_cancel_left₀ Real.two_pi_pos.ne' _).symm
lemma sum_sq_norm_coeff_ofFn {N : ℕ} (a : Fin N → ℂ) :
    (∑ k ∈ (Polynomial.ofFn N a).support, ‖(Polynomial.ofFn N a).coeff k‖ ^ 2) =
      ∑ k, ‖a k‖ ^ 2 := by
  classical
  have h := Polynomial.sum_fin (fun _ (z : ℂ) => ‖z‖ ^ 2) (by simp)
    (Polynomial.ofFn_degree_lt a)
  calc
    _ = ∑ k : Fin N, ‖(Polynomial.ofFn N a).coeff k.val‖ ^ 2 := by
      simpa only [Polynomial.sum_def] using h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.ofFn_coeff_eq_val_of_lt a k.isLt]
lemma integral_norm_sq_rotated_ofFn {N : ℕ} (a : Fin N → ℂ) (n : ℕ) :
    (∫ t in 0..2 * Real.pi, ‖rotatedCircleCurve n (Polynomial.ofFn N a) t‖ ^ 2) =
      (2 * Real.pi) * ∑ k, ‖a k‖ ^ 2 := by
  rw [integral_norm_sq_rotatedCircleCurve, sum_sq_norm_coeff_ofFn]
def carrierDerivativePolynomial (n : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C I * (Polynomial.X * p.derivative - Polynomial.C ((n : ℂ) / 2) * p)
lemma rotatedCircleCurveDerivative_eq (n : ℕ) (p : Polynomial ℂ) (t : ℝ) :
    rotatedCircleCurveDerivative n p t = rotatedCircleCurve n (carrierDerivativePolynomial n p) t := by
  simp only [rotatedCircleCurveDerivative, rotatedCircleCurve, unitCircleCurveDerivative,
    unitCircleCurve, carrierDerivativePolynomial, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, phaseVelocity]
  ring
lemma carrierDerivativePolynomial_coeff (n : ℕ) (p : Polynomial ℂ) (k : ℕ) :
    (carrierDerivativePolynomial n p).coeff k = I * ((k : ℂ) - (n : ℂ) / 2) * p.coeff k := by
  cases k with
  | zero => simp [carrierDerivativePolynomial]; ring
  | succ k =>
    simp only [carrierDerivativePolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring
lemma carrierDerivativePolynomial_ofFn {N : ℕ} (n : ℕ) (a : Fin N → ℂ) :
    carrierDerivativePolynomial n (Polynomial.ofFn N a) =
      Polynomial.ofFn N (fun j => I * ((j.val : ℂ) - (n : ℂ) / 2) * a j) := by
  classical
  ext k
  rw [carrierDerivativePolynomial_coeff]
  by_cases hk : k < N
  · simp [Polynomial.ofFn_coeff_eq_val_of_lt, hk]
  · simp [Polynomial.ofFn_coeff_eq_zero_of_ge, Nat.le_of_not_gt hk]
lemma integral_norm_sq_rotated_ofFn_derivative {N : ℕ} (a : Fin N → ℂ) (n : ℕ) :
    (∫ t in 0..2 * Real.pi, ‖rotatedCircleCurveDerivative n (Polynomial.ofFn N a) t‖ ^ 2) =
      (2 * Real.pi) * ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * ‖a k‖ ^ 2 := by
  simp_rw [rotatedCircleCurveDerivative_eq, carrierDerivativePolynomial_ofFn]
  rw [integral_norm_sq_rotated_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have he : (k.val : ℂ) - (n : ℂ) / 2 = (((k.val : ℝ) - (n : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he]
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
def scaledRotatedCurve (n : ℕ) (p : Polynomial ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt n : ℂ)⁻¹ * rotatedCircleCurve n p (x / n)
def scaledRotatedCurveDerivative (n : ℕ) (p : Polynomial ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt n : ℂ)⁻¹ * (n : ℂ)⁻¹ * rotatedCircleCurveDerivative n p (x / n)
lemma hasDerivAt_scaledRotatedCurve (n : ℕ) (p : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (scaledRotatedCurve n p) (scaledRotatedCurveDerivative n p x) x := by
  have h := ((hasDerivAt_rotatedCircleCurve n p (x / n)).scomp x
    ((hasDerivAt_id x).div_const (n : ℝ))).const_mul (Real.sqrt n : ℂ)⁻¹
  convert! h using 1
  · simp only [scaledRotatedCurveDerivative, Complex.real_smul, one_div, ofReal_inv,
      ofReal_natCast]
    ring
lemma continuous_scaledRotatedCurve (n : ℕ) (p : Polynomial ℂ) :
    Continuous (scaledRotatedCurve n p) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_scaledRotatedCurve n p x).continuousAt
lemma continuous_scaledRotatedCurveDerivative (n : ℕ) (p : Polynomial ℂ) :
    Continuous (scaledRotatedCurveDerivative n p) := by
  exact ((continuous_rotatedCircleCurveDerivative n p).comp
    (continuous_id.div_const (n : ℝ))).const_mul _
lemma integral_norm_sq_scaledRotated_ofFn {N n : ℕ} (hn : 0 < n) (a : Fin N → ℂ) :
    (∫ x in 0..2 * Real.pi * n, ‖scaledRotatedCurve n (Polynomial.ofFn N a) x‖ ^ 2) =
      (2 * Real.pi) * ∑ k, ‖a k‖ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  simp_rw [scaledRotatedCurve, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div
      (fun t => ‖rotatedCircleCurve n (Polynomial.ofFn N a) t‖ ^ 2) hn0]
  simp only [zero_div, mul_div_cancel_right₀ _ hn0, smul_eq_mul,
    integral_norm_sq_rotated_ofFn]
  field_simp
lemma integral_norm_sq_scaledRotated_ofFn_derivative {N n : ℕ} (hn : 0 < n)
    (a : Fin N → ℂ) :
    (∫ x in 0..2 * Real.pi * n,
      ‖scaledRotatedCurveDerivative n (Polynomial.ofFn N a) x‖ ^ 2) =
      (2 * Real.pi) / (n : ℝ) ^ 2 *
        ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * ‖a k‖ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  simp_rw [scaledRotatedCurveDerivative, norm_mul, norm_inv, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div
      (fun t => ‖rotatedCircleCurveDerivative n (Polynomial.ofFn N a) t‖ ^ 2) hn0]
  simp only [zero_div, mul_div_cancel_right₀ _ hn0, smul_eq_mul,
    integral_norm_sq_rotated_ofFn_derivative]
  field_simp
lemma centeredFrequency_sq_le (n : ℕ) (k : Fin (n + 1)) :
    ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by
  have hk : (k.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk)]
lemma integral_norm_sq_scaledRotated_derivative_le {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℂ) :
    (∫ x in 0..2 * Real.pi * n,
      ‖scaledRotatedCurveDerivative n (Polynomial.ofFn (n + 1) a) x‖ ^ 2) ≤
      (Real.pi / 2) * ∑ k, ‖a k‖ ^ 2 := by
  rw [integral_norm_sq_scaledRotated_ofFn_derivative hn]
  have hh : (∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * ‖a k‖ ^ 2) ≤
      ((n : ℝ) ^ 2 / 4) * ∑ k, ‖a k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (centeredFrequency_sq_le n k) (sq_nonneg _)
  calc
    _ ≤ (2 * Real.pi) / (n : ℝ) ^ 2 * (((n : ℝ) ^ 2 / 4) * ∑ k, ‖a k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
      field_simp
      ring
lemma integral_scaledRotated_energy_le {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℂ) :
    (∫ x in 0..2 * Real.pi * n,
      ‖scaledRotatedCurve n (Polynomial.ofFn (n + 1) a) x‖ ^ 2 +
      ‖scaledRotatedCurveDerivative n (Polynomial.ofFn (n + 1) a) x‖ ^ 2) ≤
      (5 * Real.pi / 2) * ∑ k, ‖a k‖ ^ 2 := by
  have hI1 : IntervalIntegrable
      (fun x => ‖scaledRotatedCurve n (Polynomial.ofFn (n + 1) a) x‖ ^ 2)
      volume 0 (2 * Real.pi * n) :=
    ((continuous_scaledRotatedCurve n _).norm.pow 2).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun x => ‖scaledRotatedCurveDerivative n (Polynomial.ofFn (n + 1) a) x‖ ^ 2)
      volume 0 (2 * Real.pi * n) :=
    ((continuous_scaledRotatedCurveDerivative n _).norm.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hI1 hI2, integral_norm_sq_scaledRotated_ofFn hn]
  have h := integral_norm_sq_scaledRotated_derivative_le hn a
  linarith
lemma hasDerivAt_scaledRotated_projection (φ : ℂ →L[ℝ] ℝ)
    (n : ℕ) (p : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (fun y => φ (scaledRotatedCurve n p y))
      (φ (scaledRotatedCurveDerivative n p x)) x :=
  φ.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_scaledRotatedCurve n p x)
lemma integral_scaledRotated_projection_energy_le (φ : ℂ →L[ℝ] ℝ)
    (hφ : ∀ z, |φ z| ≤ ‖z‖) {n : ℕ} (hn : 0 < n) (a : Fin (n + 1) → ℂ) :
    (∫ x in 0..2 * Real.pi * n,
      φ (scaledRotatedCurve n (Polynomial.ofFn (n + 1) a) x) ^ 2 +
      φ (scaledRotatedCurveDerivative n (Polynomial.ofFn (n + 1) a) x) ^ 2) ≤
      (5 * Real.pi / 2) * ∑ k, ‖a k‖ ^ 2 := by
  have hs (z : ℂ) : φ z ^ 2 ≤ ‖z‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hφ z) 2
  apply le_trans _ (integral_scaledRotated_energy_le hn a)
  apply intervalIntegral.integral_mono (by positivity)
    ((((φ.continuous.comp (continuous_scaledRotatedCurve n _)).pow 2).add
      ((φ.continuous.comp (continuous_scaledRotatedCurveDerivative n _)).pow 2)).intervalIntegrable _ _)
    ((((continuous_scaledRotatedCurve n _).norm.pow 2).add
      ((continuous_scaledRotatedCurveDerivative n _).norm.pow 2)).intervalIntegrable _ _)
  intro x
  exact add_le_add (hs _) (hs _)
lemma integral_scaledRotated_re_energy_le {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℂ) :
    (∫ x in 0..2 * Real.pi * n,
      (scaledRotatedCurve n (Polynomial.ofFn (n + 1) a) x).re ^ 2 +
      (scaledRotatedCurveDerivative n (Polynomial.ofFn (n + 1) a) x).re ^ 2) ≤
      (5 * Real.pi / 2) * ∑ k, ‖a k‖ ^ 2 :=
  integral_scaledRotated_projection_energy_le Complex.reCLM Complex.abs_re_le_norm hn a
lemma rotated_ofFn_eq_exp_sum {N : ℕ} (a : Fin N → ℂ) (n : ℕ) (t : ℝ) :
    rotatedCircleCurve n (Polynomial.ofFn N a) t =
      ∑ j, a j * Complex.exp ((((j.val : ℝ) - (n : ℝ) / 2) * t : ℝ) * I) := by
  rw [rotatedCircleCurve, unitCircleCurve_eq_exp, Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  change Complex.exp _ * (a j * Complex.exp _) = _
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [phaseVelocity, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring
lemma rotated_ofFn_real_coordinates (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) :
    (rotatedCircleCurve n (Polynomial.ofFn (n + 1) (fun j => (a j : ℂ))) t).re =
      centeredCosineSum n a t ∧
    (rotatedCircleCurve n (Polynomial.ofFn (n + 1) (fun j => (a j : ℂ))) t).im =
      centeredSineSum n a t := by
  rw [rotated_ofFn_eq_exp_sum]
  simp only [centeredCosineSum, centeredSineSum, centeredFrequency, Complex.re_sum,
    Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  trivial
lemma scaledRotated_ofFn_real_coordinates (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ) :
    (scaledRotatedCurve n (Polynomial.ofFn (n + 1) (fun j => (a j : ℂ))) x).re =
      centeredCosineSum n a (x / n) / Real.sqrt n ∧
    (scaledRotatedCurve n (Polynomial.ofFn (n + 1) (fun j => (a j : ℂ))) x).im =
      centeredSineSum n a (x / n) / Real.sqrt n := by
  have h := rotated_ofFn_real_coordinates n a (x / n)
  simp only [scaledRotatedCurve, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h.1, h.2]
  constructor <;> ring
end
end Fluctuations.PolynomialCircle
end

section
open Set MeasureTheory
open scoped BigOperators
namespace Fluctuations.SobolevSampling
noncomputable section
theorem sq_sub_le_energy (f g : ℝ → ℝ) {a b x y : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x ^ 2 - f y ^ 2| ≤ ∫ t in a..b, (f t ^ 2 + g t ^ 2) := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun t => f t ^ 2 + g t ^ 2) (Icc a b) :=
    (hfc.pow 2).add (hg.pow 2)
  have hEi : IntervalIntegrable (fun t => f t ^ 2 + g t ^ 2) volume a b :=
    hEc.intervalIntegrable_of_Icc (hx.1.trans hx.2)
  have hdir (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      |f v ^ 2 - f u ^ 2| ≤ ∫ t in a..b, (f t ^ 2 + g t ^ 2) := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hloc : |f v ^ 2 - f u ^ 2| ≤ ∫ t in u..v, (f t ^ 2 + g t ^ 2) := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le huv
        ((hfc.pow 2).mono hsub)
      · intro t ht
        exact ((hf t (hsub ⟨ht.1.le, ht.2.le⟩)).pow 2).differentiableAt.differentiableWithinAt
      · filter_upwards [] with t ht
        rw [((hf t (hsub ⟨ht.1.le, ht.2.le⟩)).pow 2).deriv]
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Real.norm_eq_abs]
        apply abs_le.mpr
        constructor <;> nlinarith [sq_nonneg (f t + g t), sq_nonneg (f t - g t)]
      · exact (hEc.mono hsub).intervalIntegrable_of_Icc huv
    exact hloc.trans (intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))) hEi)
  rcases le_total x y with hxy | hyx
  · simpa only [abs_sub_comm] using hdir x y hx hy hxy
  · exact hdir y x hy hx hyx
theorem sq_le_two_energy (f g : ℝ → ℝ) {a x : ℝ}
    (hf : ∀ t ∈ Icc a (a + 1), HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Icc a (a + 1)))
    (hx : x ∈ Icc a (a + 1)) :
    f x ^ 2 ≤ 2 * ∫ t in a..a + 1, (f t ^ 2 + g t ^ 2) := by
  have hfc : ContinuousOn f (Icc a (a + 1)) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hab : a ≤ a + 1 := by linarith
  have hfi : IntervalIntegrable (fun t => f t ^ 2) volume a (a + 1) :=
    (hfc.pow 2).intervalIntegrable_of_Icc hab
  have hEi : IntervalIntegrable (fun t => f t ^ 2 + g t ^ 2) volume a (a + 1) :=
    ((hfc.pow 2).add (hg.pow 2)).intervalIntegrable_of_Icc hab
  let E := ∫ t in a..a + 1, (f t ^ 2 + g t ^ 2)
  have hpoint (y : ℝ) (hy : y ∈ Icc a (a + 1)) : f x ^ 2 ≤ f y ^ 2 + E := by
    have h := (le_abs_self (f x ^ 2 - f y ^ 2)).trans (sq_sub_le_energy f g hf hg hx hy)
    dsimp [E]
    linarith
  have hmean := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x ^ 2) volume a (a + 1))
    (hfi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const] at hmean
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul] at hmean
  have hE : (∫ t in a..a + 1, f t ^ 2) ≤ E := by
    apply intervalIntegral.integral_mono_on hab hfi hEi
    intro t ht
    exact le_add_of_nonneg_right (sq_nonneg _)
  dsimp [E] at *
  linarith
theorem sum_sq_le_cell_energy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f g : ℝ → ℝ) (a : κ → ℝ) (t : ι → ℝ) (cell : ι → κ) (H : ℕ)
    (hf : ∀ j, ∀ x ∈ Icc (a j) (a j + 1), HasDerivAt f (g x) x)
    (hg : ∀ j, ContinuousOn g (Icc (a j) (a j + 1)))
    (ht : ∀ i, t i ∈ Icc (a (cell i)) (a (cell i) + 1))
    (hocc : ∀ j, (Finset.univ.filter (fun i => cell i = j)).card ≤ H) :
    (∑ i, f (t i) ^ 2) ≤
      2 * (H : ℝ) * ∑ j, ∫ x in a j..a j + 1, (f x ^ 2 + g x ^ 2) := by
  classical
  let E (j : κ) := ∫ x in a j..a j + 1, (f x ^ 2 + g x ^ 2)
  have hE (j : κ) : 0 ≤ E j := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro x
    positivity
  rw [← Finset.sum_fiberwise Finset.univ cell (fun i => f (t i) ^ 2)]
  calc
    (∑ j, ∑ i ∈ Finset.univ.filter (fun i => cell i = j), f (t i) ^ 2)
      ≤ ∑ j, 2 * (H : ℝ) * E j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (∑ i ∈ Finset.univ.filter (fun i => cell i = j), f (t i) ^ 2)
            ≤ ∑ i ∈ Finset.univ.filter (fun i => cell i = j), 2 * E j := by
              apply Finset.sum_le_sum
              intro i hi
              have hij : cell i = j := (Finset.mem_filter.mp hi).2
              apply sq_le_two_energy f g (hf j) (hg j)
              simpa only [hij] using ht i
          _ = ((Finset.univ.filter (fun i => cell i = j)).card : ℝ) * (2 * E j) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (H : ℝ) * (2 * E j) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hocc j) (mul_nonneg (by norm_num) (hE j))
          _ = 2 * (H : ℝ) * E j := by ring
    _ = 2 * (H : ℝ) * ∑ j, E j := (Finset.mul_sum ..).symm
theorem sum_cell_integral_le_overlap {κ : Type*} [Fintype κ]
    (E : ℝ → ℝ) (c : κ → ℝ) (a b : ℝ) (K : ℕ)
    (hab : a ≤ b) (hE : IntegrableOn E (Ioc a b))
    (hE0 : ∀ x ∈ Ioc a b, 0 ≤ E x)
    (hleft : ∀ j, a ≤ c j) (hright : ∀ j, c j + 1 ≤ b)
    (hcover : ∀ x ∈ Ioc a b,
      (Finset.univ.filter (fun j => x ∈ Ioc (c j) (c j + 1))).card ≤ K) :
    (∑ j, ∫ x in c j..c j + 1, E x) ≤ (K : ℝ) * ∫ x in a..b, E x := by
  classical
  have hsub (j : κ) : Ioc (c j) (c j + 1) ⊆ Ioc a b :=
    Ioc_subset_Ioc (hleft j) (hright j)
  have hind (j : κ) : IntegrableOn ((Ioc (c j) (c j + 1)).indicator E) (Ioc a b) :=
    hE.indicator measurableSet_Ioc
  have heq (j : κ) : (∫ x in c j..c j + 1, E x) =
      ∫ x in Ioc a b, (Ioc (c j) (c j + 1)).indicator E x := by
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (hsub j)]
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun j hj => hind j), intervalIntegral.integral_of_le hab,
    ← integral_const_mul]
  apply setIntegral_mono_on (integrable_finsetSum _ (fun j hj => hind j))
    (hE.const_mul (K : ℝ)) measurableSet_Ioc
  intro x hx
  simp only [Set.indicator_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcover x hx) (hE0 x hx)
theorem sum_sq_le_cover_energy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f g : ℝ → ℝ) (c : κ → ℝ) (a b : ℝ) (H K : ℕ)
    (t : ι → ℝ) (cell : ι → κ)
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a b))
    (hleft : ∀ j, a ≤ c j) (hright : ∀ j, c j + 1 ≤ b)
    (ht : ∀ i, t i ∈ Icc (c (cell i)) (c (cell i) + 1))
    (hocc : ∀ j, (Finset.univ.filter (fun i => cell i = j)).card ≤ H)
    (hcover : ∀ x ∈ Ioc a b,
      (Finset.univ.filter (fun j => x ∈ Ioc (c j) (c j + 1))).card ≤ K) :
    (∑ i, f (t i) ^ 2) ≤
      2 * (H : ℝ) * (K : ℝ) * ∫ x in a..b, (f x ^ 2 + g x ^ 2) := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hEc := (hfc.pow 2).add (hg.pow 2)
  have hsub (j : κ) : Icc (c j) (c j + 1) ⊆ Icc a b :=
    Icc_subset_Icc (hleft j) (hright j)
  have hsamp := sum_sq_le_cell_energy f g c t cell H
    (fun j x hx => hf x (hsub j hx)) (fun j => hg.mono (hsub j)) ht hocc
  have hsum := sum_cell_integral_le_overlap (fun x => f x ^ 2 + g x ^ 2) c a b K hab
    (hEc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun x hx => add_nonneg (sq_nonneg _) (sq_nonneg _)) hleft hright hcover
  calc
    _ ≤ 2 * (H : ℝ) * ∑ j, ∫ x in c j..c j + 1, (f x ^ 2 + g x ^ 2) := hsamp
    _ ≤ 2 * (H : ℝ) * ((K : ℝ) * ∫ x in a..b, (f x ^ 2 + g x ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
end
end Fluctuations.SobolevSampling
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Fluctuations.GaussianHolder
noncomputable section
theorem abs_real_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
end
end Fluctuations.GaussianHolder
end

section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
namespace Fluctuations.GaussianHolder
noncomputable section
lemma measure_abs_ge_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |X ω|} ⊆ {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    intro ω hω
    rcases le_total 0 (X ω) with hp | hn
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, abs_of_nonneg hp] using hω)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, abs_of_nonpos hn] using hω)
  calc
    μ.real {ω | u ≤ |X ω|} ≤ μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) :=
      measureReal_mono hset
    _ ≤ μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-u ^ 2 / (2 * c)) + Real.exp (-u ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hu) (hX.neg.measure_ge_le hu)
    _ = 2 * Real.exp (-u ^ 2 / (2 * c)) := by ring
end
end Fluctuations.GaussianHolder
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Fluctuations.GaussianSampling
noncomputable section
def rowNormSq {ι κ : Type*} [Fintype κ] (B : ι → κ → ℝ) (i : ι) : ℝ :=
  ∑ j, B i j ^ 2
def normalizedRow {ι κ : Type*} [Fintype κ] (B : ι → κ → ℝ) (i : ι) (j : κ) : ℝ :=
  B i j / Real.sqrt (rowNormSq B i)
lemma normalizedRow_eval {ι κ : Type*} [Fintype κ] (B : ι → κ → ℝ) (i : ι)
    (w : κ → ℝ) :
    (∑ j, normalizedRow B i j * w j) =
      (∑ j, B i j * w j) / Real.sqrt (rowNormSq B i) := by
  simp only [normalizedRow, div_mul_eq_mul_div, Finset.sum_div]
lemma normalizedRow_forward_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → κ → ℝ) {c M : ℝ} (hc : 0 < c)
    (hvar : ∀ i, c ≤ rowNormSq B i)
    (hframe : ∀ w : κ → ℝ, (∑ i, (∑ j, B i j * w j) ^ 2) ≤ M * ∑ j, w j ^ 2)
    (w : κ → ℝ) :
    (∑ i, (∑ j, normalizedRow B i j * w j) ^ 2) ≤ (M / c) * ∑ j, w j ^ 2 := by
  calc
    _ = ∑ i, (∑ j, B i j * w j) ^ 2 / rowNormSq B i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [normalizedRow_eval, div_pow, Real.sq_sqrt (hc.le.trans (hvar i))]
    _ ≤ ∑ i, (∑ j, B i j * w j) ^ 2 / c := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_left (sq_nonneg _) hc (hvar i)
    _ = (∑ i, (∑ j, B i j * w j) ^ 2) / c := (Finset.sum_div ..).symm
    _ ≤ (M * ∑ j, w j ^ 2) / c := div_le_div_of_nonneg_right (hframe w) hc.le
    _ = _ := by ring
def scaledCosineRow (n : ℕ) (t : ℝ) (j : Fin (n + 1)) : ℝ :=
  Real.cos (centeredFrequency n j * (t / n)) / Real.sqrt n
lemma scaledCosineRow_eval (n : ℕ) (t : ℝ) (w : Fin (n + 1) → ℝ) :
    (∑ j, scaledCosineRow n t j * w j) =
      (PolynomialCircle.scaledRotatedCurve n
        (Polynomial.ofFn (n + 1) (fun j => (w j : ℂ))) t).re := by
  rw [(PolynomialCircle.scaledRotated_ofFn_real_coordinates n w t).1]
  simp only [scaledCosineRow, centeredCosineSum, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
lemma scaledCosineRow_sampling_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {n : ℕ} (hn : 0 < n)
    (t : ι → ℝ) (cell : ι → κ) (starts : κ → ℝ) (H K : ℕ)
    (hleft : ∀ j, 0 ≤ starts j)
    (hright : ∀ j, starts j + 1 ≤ 2 * Real.pi * n)
    (ht : ∀ i, t i ∈ Icc (starts (cell i)) (starts (cell i) + 1))
    (hocc : ∀ j, (Finset.univ.filter (fun i => cell i = j)).card ≤ H)
    (hcover : ∀ x ∈ Ioc (0 : ℝ) (2 * Real.pi * n),
      (Finset.univ.filter (fun j => x ∈ Ioc (starts j) (starts j + 1))).card ≤ K)
    (w : Fin (n + 1) → ℝ) :
    (∑ i, (∑ j, scaledCosineRow n (t i) j * w j) ^ 2) ≤
      (5 * Real.pi * H * K) * ∑ j, w j ^ 2 := by
  let p := Polynomial.ofFn (n + 1) (fun j => (w j : ℂ))
  let f := fun x => (PolynomialCircle.scaledRotatedCurve n p x).re
  let g := fun x => (PolynomialCircle.scaledRotatedCurveDerivative n p x).re
  have hsample := SobolevSampling.sum_sq_le_cover_energy f g starts 0
    (2 * Real.pi * n) H K t cell (by positivity)
    (fun x _ => PolynomialCircle.hasDerivAt_scaledRotated_projection Complex.reCLM n p x)
    ((Complex.continuous_re.comp
      (PolynomialCircle.continuous_scaledRotatedCurveDerivative n p)).continuousOn)
    hleft hright ht hocc hcover
  have henergy : (∫ x in 0..2 * Real.pi * n, f x ^ 2 + g x ^ 2) ≤
      (5 * Real.pi / 2) * ∑ j, w j ^ 2 := by
    simpa only [f, g, p, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      PolynomialCircle.integral_scaledRotated_re_energy_le hn (fun j => (w j : ℂ))
  simp_rw [scaledCosineRow_eval]
  calc
    _ ≤ 2 * (H : ℝ) * (K : ℝ) * ∫ x in 0..2 * Real.pi * n, (f x ^ 2 + g x ^ 2) := hsample
    _ ≤ 2 * (H : ℝ) * (K : ℝ) * ((5 * Real.pi / 2) * ∑ j, w j ^ 2) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring
lemma real_sign_div_pos (x : ℝ) {c : ℝ} (hc : 0 < c) :
    Real.sign (x / c) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, Real.sign_of_neg (div_neg_of_neg_of_pos hx hc)]
  · subst x; simp
  · rw [Real.sign_of_pos hx, Real.sign_of_pos (div_pos hx hc)]
lemma sign_normalizedRow_eval {ι κ : Type*} [Fintype κ]
    (B : ι → κ → ℝ) (i : ι) (hi : 0 < rowNormSq B i) (w : κ → ℝ) :
    Real.sign (∑ j, normalizedRow B i j * w j) = Real.sign (∑ j, B i j * w j) := by
  rw [normalizedRow_eval, real_sign_div_pos _ (Real.sqrt_pos.mpr hi)]
lemma scaledCosineRow_normSq_lower {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : Real.sin (t / n) ≠ 0)
    (hbulk : 1 / |Real.sin (t / n)| ≤ (n + 1 : ℝ) / 2) :
    (1 : ℝ) / 4 ≤ ∑ j, scaledCosineRow n t j ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [scaledCosineRow, div_pow, Real.sq_sqrt hn'.le, ← Finset.sum_div]
  apply (le_div_iff₀ hn').mpr
  exact (by nlinarith : (1 : ℝ) / 4 * n ≤ (n + 1 : ℝ) / 4).trans
    (centeredTrigNormSq_lower n ht hbulk).1
end
end Fluctuations.GaussianSampling
end

section
noncomputable section
open scoped BigOperators
open Classical
namespace Fluctuations.SignConditionalRows
open SignActivityFiber
def conditionalCosineRow (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ)
    (j : {j // j ∈ freeIndices n a}) : ℝ :=
  (if j.val = j.val.rev then 1 else 2) * GaussianSampling.scaledCosineRow n x j.val
def conditionalCosineVariance (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : {j // j ∈ freeIndices n a}, conditionalCosineRow n a x j ^ 2
def maskBad (n : ℕ) (a : Fin (n + 1) → ℝ) : Prop :=
  ∃ x ∈ Set.Icc SignSineOccupancy.endpointCutoff
    (Real.pi * n - SignSineOccupancy.endpointCutoff),
      conditionalCosineVariance n a x < 1 / 8
end Fluctuations.SignConditionalRows
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace Fluctuations.RademacherConcentration
lemma integral_exp_mul_rademacher (t : ℝ) :
    (∫ x : ℝ, Real.exp (t*x) ∂rademacherLaw) = Real.cosh t := by
  rw [rademacherLaw, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, mul_one, mul_neg]
    norm_num
    rw [Real.cosh_eq]
    ring
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)
lemma rademacher_id_hasSubgaussianMGF : HasSubgaussianMGF (id : ℝ → ℝ) 1 rademacherLaw where
  integrable_exp_mul t := by
    unfold rademacherLaw
    exact ((integrable_dirac (by finiteness)).smul_measure (by norm_num)).add_measure
      ((integrable_dirac (by finiteness)).smul_measure (by norm_num))
  mgf_le t := by
    change (∫ x : ℝ, Real.exp (t*x) ∂rademacherLaw) ≤ Real.exp ((1:NNReal)*t^2/2)
    rw [integral_exp_mul_rademacher]
    simpa using Real.cosh_le_exp_half_sq t
lemma hasSubgaussianMGF_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X rademacherLaw μ) :
    HasSubgaussianMGF X 1 μ := by
  have h := rademacher_id_hasSubgaussianMGF
  rw [← hX.map_eq] at h
  exact HasSubgaussianMGF.of_map (X := id) (Y := X) hX.aemeasurable h
lemma finite_sum_hasSubgaussianMGF {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) rademacherLaw μ) (hi : iIndepFun X μ)
    (s : Finset ι) (b : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, b i*X i ω)
      (∑ i ∈ s, Real.toNNReal ((b i)^2)) μ := by
  have hind := hi.comp (fun i x => b i*x) (fun _ => by fun_prop)
  apply HasSubgaussianMGF.sum_of_iIndepFun hind
  intro i _
  have h := (hasSubgaussianMGF_of_hasLaw (hX i)).const_mul (b i)
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  convert! h.mgf_le t using 1
  · simp only [Real.coe_toNNReal', max_eq_left (sq_nonneg (b i))]
    congr 2
    change (b i)^2 * t^2 = ((b i)^2 * 1) * t^2
    ring
lemma finite_sum_abs_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) rademacherLaw μ) (hi : iIndepFun X μ)
    (s : Finset ι) (b : ι → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |∑ i ∈ s, b i*X i ω|} ≤
      2*Real.exp (-u^2/(2*∑ i ∈ s, (b i)^2)) := by
  have h := GaussianHolder.measure_abs_ge_le_of_hasSubgaussianMGF μ
    (finite_sum_hasSubgaussianMGF hX hi s b) hu
  change μ.real {ω | u ≤ |∑ i ∈ s, b i * X i ω|} ≤
    2 * Real.exp (-u^2 / (2 * (↑(∑ i ∈ s, Real.toNNReal ((b i)^2)) : ℝ))) at h
  simpa only [NNReal.coe_sum, Real.coe_toNNReal', max_eq_left (sq_nonneg _)] using h
end Fluctuations.RademacherConcentration
end
end

section
noncomputable section
open Finset MeasureTheory ProbabilityTheory Classical
open scoped BigOperators
namespace Fluctuations.SignActivityMask
open SignPolynomialDivisibility
lemma sign_square_eq_one {m : ℕ} (a : Fin m → ℝ) (ha : a ∈ signVectors m)
    (j : Fin m) : a j ^ 2 = 1 := by
  rcases (mem_signVectors a).mp ha j with h | h <;> rw [h] <;> norm_num
theorem pair_product_filter_card (n : ℕ)
    (P : ({j : Fin (n + 1) // j < j.rev} → ℝ) → Prop) :
    ((signVectors (n + 1)).filter
      (fun a : Fin (n + 1) → ℝ => P (fun j => a j.val * a j.val.rev))).card =
    ((signVectors (n + 1)).filter
      (fun a : Fin (n + 1) → ℝ => P (fun j => a j.val.rev))).card := by
  classical
  let T : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun a j =>
    if j.rev < j then a j * a j.rev else a j
  have hsign (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1)) :
      T a ∈ signVectors (n + 1) := by
    apply (mem_signVectors _).mpr
    intro j
    by_cases hj : j.rev < j
    · rcases (mem_signVectors a).mp ha j with h | h <;>
        rcases (mem_signVectors a).mp ha j.rev with h' | h' <;>
        simp [T, hj, h, h']
    · simpa only [T, hj, ite_false] using (mem_signVectors a).mp ha j
  have hinvol (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1)) :
      T (T a) = a := by
    funext j
    by_cases hj : j.rev < j
    · have hr : ¬j < j.rev := not_lt_of_gt hj
      simp only [T, hj, ite_true, Fin.rev_rev, hr, ite_false]
      rw [mul_assoc, ← sq, sign_square_eq_one a ha j.rev, mul_one]
    · simp only [T, hj, ite_false]
  have hright (a : Fin (n + 1) → ℝ) (j : {j : Fin (n + 1) // j < j.rev}) :
      T a j.val.rev = a j.val * a j.val.rev := by
    simp only [T, Fin.rev_rev, j.property, ite_true, mul_comm]
  apply Finset.card_bij (fun a _ => T a)
  · intro a ha
    obtain ⟨ha, hP⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨hsign a ha, by simpa only [hright] using hP⟩
  · intro a ha b hb he
    have ha' := (mem_filter.mp ha).1
    have hb' := (mem_filter.mp hb).1
    calc
      a = T (T a) := (hinvol a ha').symm
      _ = T (T b) := congrArg T he
      _ = b := hinvol b hb'
  · intro b hb
    obtain ⟨hb, hP⟩ := mem_filter.mp hb
    refine ⟨T b, mem_filter.mpr ⟨hsign b hb, ?_⟩, hinvol b hb⟩
    have he : (fun j : {j : Fin (n + 1) // j < j.rev} =>
        T b j.val * T b j.val.rev) = (fun j => b j.val.rev) := by
      funext j
      rw [← hright, hinvol b hb]
    rwa [he]
theorem pair_product_event_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ)
    (P : ({j : Fin (n + 1) // j < j.rev} → ℝ) → Prop) :
    Prob μ {ω | P (fun j => ξ j.val.val ω * ξ j.val.rev.val ω)} =
      Prob μ {ω | P (fun j => ξ j.val.rev.val ω)} := by
  unfold Prob
  rw [finite_sign_event_measure μ ξ hξ (n + 1)
      (fun a => P (fun j => a j.val * a j.val.rev)),
    finite_sign_event_measure μ ξ hξ (n + 1) (fun a => P (fun j => a j.val.rev)),
    pair_product_filter_card]
theorem pair_product_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ)
    (b : {j : Fin (n + 1) // j < j.rev} → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Prob μ {ω | u ≤ |∑ j, b j * (ξ j.val.val ω * ξ j.val.rev.val ω)|} ≤
      2 * Real.exp (-u ^ 2 / (2 * ∑ j, b j ^ 2)) := by
  rw [pair_product_event_probability μ ξ hξ n
    (fun a => u ≤ |∑ j, b j * a j|)]
  have hi : Function.Injective
      (fun j : {j : Fin (n + 1) // j < j.rev} => j.val.rev.val) := by
    intro i j he
    apply Subtype.ext
    exact Fin.rev_involutive.injective (Fin.val_injective he)
  have hLaw (j : {j : Fin (n + 1) // j < j.rev}) :
      HasLaw (ξ j.val.rev.val) rademacherLaw μ :=
    ⟨hξ.1.1 _, (hξ.1.2.2 _).map_eq.trans hξ.2⟩
  simpa only [Prob, Measure.real] using RademacherConcentration.finite_sum_abs_tail hLaw
    (hξ.1.2.1.precomp hi) Finset.univ b hu
lemma sum_symmetric_eq_pairs_middle (n : ℕ) (f : Fin (n + 1) → ℝ)
    (hf : ∀ j, f j.rev = f j) :
    (∑ j, f j) =
      2 * (∑ j : {j : Fin (n + 1) // j < j.rev}, f j.val) +
        ∑ j : {j : Fin (n + 1) // j = j.rev}, f j.val := by
  classical
  let lo := (univ : Finset (Fin (n + 1))).filter (fun j => j < j.rev)
  let hi := (univ : Finset (Fin (n + 1))).filter (fun j => j.rev < j)
  let mid := (univ : Finset (Fin (n + 1))).filter (fun j => j = j.rev)
  have hpair : ∑ j ∈ hi, f j = ∑ j ∈ lo, f j := by
    apply sum_bij (fun j _ => j.rev)
    · intro j hj
      simpa only [lo, hi, mem_filter, mem_univ, true_and, Fin.rev_rev] using hj
    · intro i _ j _ he
      exact Fin.rev_involutive.injective he
    · intro j hj
      refine ⟨j.rev, ?_, Fin.rev_rev j⟩
      simpa only [lo, hi, mem_filter, mem_univ, true_and, Fin.rev_rev] using hj
    · intro j _
      exact (hf j).symm
  have hsplit : (∑ j, f j) = (∑ j ∈ lo, f j) + (∑ j ∈ hi, f j) + ∑ j ∈ mid, f j := by
    simp only [lo, hi, mid, sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rcases lt_trichotomy j j.rev with hj | hj | hj
    · simp [hj, not_lt_of_gt hj, hj.ne]
    · have hlo : ¬j < j.rev := by rw [← hj]; exact lt_irrefl _
      have hhi : ¬j.rev < j := by rw [← hj]; exact lt_irrefl _
      simp only [hlo, hhi, ite_false, zero_add]
      rw [if_pos hj]
    · simp [hj, not_lt_of_gt hj, hj.ne']
  rw [hpair] at hsplit
  have hlo : (∑ j : {j : Fin (n + 1) // j < j.rev}, f j.val) = ∑ j ∈ lo, f j := by
    exact (sum_subtype lo (by intro j; simp [lo]) f).symm
  have hmid : (∑ j : {j : Fin (n + 1) // j = j.rev}, f j.val) = ∑ j ∈ mid, f j := by
    exact (sum_subtype mid (by intro j; simp [mid]) f).symm
  rw [hlo, hmid]
  linarith
lemma lower_pair_card_le (n : ℕ) :
    (Fintype.card {j : Fin (n + 1) // j < j.rev} : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
  have he := sum_symmetric_eq_pairs_middle n (fun _ => (1 : ℝ)) (by simp)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one] at he
  have hm : (0 : ℝ) ≤ Fintype.card {j : Fin (n + 1) // j = j.rev} := Nat.cast_nonneg _
  linarith
lemma equal_sign_activity (x y : ℝ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    (if x = y then (1 : ℝ) else 0) = (1 + x * y) / 2 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
theorem actual_mask_deviation_point_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    Prob μ {ω | (1 / 16 : ℝ) ≤ |∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
        (ξ j.val.val ω * ξ j.val.rev.val ω)|} ≤ 2 * Real.exp (-(n : ℝ) / 2048) := by
  classical
  let b : {j : Fin (n + 1) // j < j.rev} → ℝ := fun j =>
    2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcoeff (j : {j : Fin (n + 1) // j < j.rev}) : |b j| ≤ 2 / n := by
    have hcos : Real.cos (centeredFrequency n j.val * (x / n)) ^ 2 ≤ 1 := by
      nlinarith [Real.cos_le_one (centeredFrequency n j.val * (x / n)),
        Real.neg_one_le_cos (centeredFrequency n j.val * (x / n))]
    rw [abs_of_nonneg (by dsimp [b]; positivity : 0 ≤ b j)]
    exact (mul_le_mul_of_nonneg_left hcos (by positivity)).trans_eq (mul_one _)
  have hcard : (Fintype.card {j : Fin (n + 1) // j < j.rev} : ℝ) ≤ n := by
    have hc := lower_pair_card_le n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hproxy : (∑ j, b j ^ 2) ≤ 4 / n := by
    calc
      _ ≤ ∑ _j : {j : Fin (n + 1) // j < j.rev}, (2 / (n : ℝ)) ^ 2 := by
        apply sum_le_sum
        intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (b j)) (hcoeff j) 2
      _ = (Fintype.card {j : Fin (n + 1) // j < j.rev} : ℝ) * (2 / n) ^ 2 := by simp
      _ ≤ (n : ℝ) * (2 / n) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = 4 / n := by field_simp; ring
  have hnonneg : (0 : ℝ) ≤ ∑ j, b j ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hzero : (∑ j, b j ^ 2) = 0
  · have hbzero (j : {j : Fin (n + 1) // j < j.rev}) : b j = 0 := by
      have hj := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (b j))).mp hzero j (mem_univ j)
      exact sq_eq_zero_iff.mp hj
    have he : {ω | (1 / 16 : ℝ) ≤ |∑ j, b j * (ξ j.val.val ω * ξ j.val.rev.val ω)|} = ∅ := by
      ext ω
      simp only [hbzero, zero_mul, sum_const_zero, abs_zero]
      norm_num
    change Prob μ {ω | (1 / 16 : ℝ) ≤ |∑ j, b j * (ξ j.val.val ω * ξ j.val.rev.val ω)|} ≤ _
    rw [he]
    simp only [Prob, measure_empty, ENNReal.toReal_zero]
    positivity
  · have hpos : 0 < ∑ j, b j ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have htail := pair_product_sum_abs_tail μ ξ hξ n b (by norm_num : (0 : ℝ) ≤ 1 / 16)
    have hfrac : (n : ℝ) / 2048 ≤ (1 / 16 : ℝ) ^ 2 / (2 * ∑ j, b j ^ 2) := by
      calc
        _ = (1 / 16 : ℝ) ^ 2 / (2 * (4 / n)) := by field_simp; ring
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hproxy (by norm_num))
    have hexp : Real.exp (-(1 / 16 : ℝ) ^ 2 / (2 * ∑ j, b j ^ 2)) ≤
        Real.exp (-(n : ℝ) / 2048) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hfrac
    exact htail.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))
end Fluctuations.SignActivityMask
end
end

section
noncomputable section
open Finset Classical
open scoped BigOperators
namespace Fluctuations.SignConditionalRows
open SignActivityFiber SignActivityMask SignPolynomialDivisibility
lemma sum_eq_pairs_middle (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∑ j, f j) =
      (∑ j : {j : Fin (n + 1) // j < j.rev}, (f j.val + f j.val.rev)) +
        ∑ j : {j : Fin (n + 1) // j = j.rev}, f j.val := by
  have he := sum_symmetric_eq_pairs_middle n (fun j => f j + f j.rev)
    (by intro j; simp only [Fin.rev_rev, add_comm])
  have hr := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1))) f
  simp only [Fin.revPerm_apply] at hr
  rw [sum_add_distrib, hr] at he
  have hm : (∑ j : {j : Fin (n + 1) // j = j.rev}, (f j.val + f j.val.rev)) =
      2 * ∑ j : {j : Fin (n + 1) // j = j.rev}, f j.val := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← j.property]
    ring
  rw [hm] at he
  linarith
lemma sum_free_eq_pairs_middle (n : ℕ) (a : Fin (n + 1) → ℝ)
    (f : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ j, f j) =
      (∑ j : {j : Fin (n + 1) // j < j.rev},
        if h : a j.val = a j.val.rev then
          f ⟨j.val, by simp [freeIndices, j.property.le, h]⟩ else 0) +
      ∑ j : {j : Fin (n + 1) // j = j.rev},
        f ⟨j.val, middle_mem_freeIndices n a j.val j.property⟩ := by
  let F : Fin (n + 1) → ℝ := fun j => if h : j ∈ freeIndices n a then f ⟨j,h⟩ else 0
  have hs : (∑ j, f j) = ∑ j : Fin (n + 1), F j := by
    calc
      _ = ∑ j : {j // j ∈ freeIndices n a}, F j.val := by
        apply sum_congr rfl
        intro j _
        simp only [F, j.property, dite_true]
      _ = ∑ j ∈ freeIndices n a, F j := sum_coe_sort _ _
      _ = _ := sum_subset (subset_univ _) (by
        intro j _ hj
        simp only [F, hj, dite_false])
  rw [hs, sum_eq_pairs_middle]
  congr 1
  · apply sum_congr rfl
    intro j _
    have hr : j.val.rev ∉ freeIndices n a := by
      intro h
      have hh := (mem_filter.mp h).2.1
      simp only [Fin.rev_rev] at hh
      exact (not_le_of_gt j.property) hh
    simp only [F, hr, dite_false, add_zero]
    by_cases hj : a j.val = a j.val.rev
    · have hf : j.val ∈ freeIndices n a := by simp [freeIndices, j.property.le, hj]
      simp only [hf, hj, dite_true]
    · have hf : j.val ∉ freeIndices n a := by simp [freeIndices, hj]
      simp only [hf, hj, dite_false]
  · apply sum_congr rfl
    intro j _
    simp only [F, middle_mem_freeIndices n a j.val j.property, dite_true]
lemma symmetric_row_fillFree_eval (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1))
    (w : Fin (n + 1) → ℝ) (hw : ∀ j, w j.rev = w j)
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ j, w j * fillFree n a u j) =
      ∑ j : {j // j ∈ freeIndices n a},
        ((if j.val = j.val.rev then 1 else 2) * w j.val) * u j := by
  rw [sum_eq_pairs_middle, sum_free_eq_pairs_middle]
  congr 1
  · apply sum_congr rfl
    intro j _
    have hr : j.val.rev ∉ freeIndices n a := by
      intro h
      have hh := (mem_filter.mp h).2.1
      simp only [Fin.rev_rev] at hh
      exact (not_le_of_gt j.property) hh
    have hm : j.val ≠ j.val.rev := ne_of_lt j.property
    by_cases hj : a j.val = a j.val.rev
    · have hf : j.val ∈ freeIndices n a := by simp [freeIndices, j.property.le, hj]
      simp only [fillFree, hf, hr, dite_true, dite_false, Fin.rev_rev, hw, hj,
        hm, ite_false]
      ring
    · have hf : j.val ∉ freeIndices n a := by simp [freeIndices, hj]
      have hz : a j.val + a j.val.rev = 0 := by
        rcases (mem_signVectors a).mp ha j.val with h | h <;>
          rcases (mem_signVectors a).mp ha j.val.rev with h' | h' <;> simp_all
      simp only [fillFree, hf, hr, dite_false, Fin.rev_rev, hw, hj]
      rw [← mul_add, hz, mul_zero]
  · apply sum_congr rfl
    intro j _
    have hf := middle_mem_freeIndices n a j.val j.property
    simp only [fillFree, hf, dite_true]
    rw [if_pos j.property, one_mul]
lemma conditionalCosineRow_eval (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (x : ℝ)
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ j, conditionalCosineRow n a x j * u j) =
      (PolynomialCircle.scaledRotatedCurve n
        (Polynomial.ofFn (n + 1) (fun j => (fillFree n a u j : ℂ))) x).re := by
  rw [← GaussianSampling.scaledCosineRow_eval]
  exact (symmetric_row_fillFree_eval n a ha (GaussianSampling.scaledCosineRow n x)
    (by intro j; simp only [GaussianSampling.scaledCosineRow, centeredFrequency_rev,
      neg_mul, Real.cos_neg]) u).symm
lemma conditionalCosineVariance_pairs (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ) :
    conditionalCosineVariance n a x =
      (∑ j : {j : Fin (n + 1) // j < j.rev},
        if a j.val = a j.val.rev then
          4 * GaussianSampling.scaledCosineRow n x j.val ^ 2 else 0) +
      ∑ j : {j : Fin (n + 1) // j = j.rev},
        GaussianSampling.scaledCosineRow n x j.val ^ 2 := by
  rw [conditionalCosineVariance, sum_free_eq_pairs_middle]
  congr 1
  · apply sum_congr rfl
    intro j _
    by_cases hj : a j.val = a j.val.rev
    · simp only [hj, dite_true, ite_true, conditionalCosineRow,
        (ne_of_lt j.property), ite_false]
      ring
    · simp only [hj, dite_false, ite_false]
  · apply sum_congr rfl
    intro j _
    dsimp only [conditionalCosineRow]
    rw [if_pos j.property, one_mul]
lemma conditionalCosineVariance_deviation (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (x : ℝ) :
    conditionalCosineVariance n a x -
        (∑ j : Fin (n + 1), GaussianSampling.scaledCosineRow n x j ^ 2) =
      ∑ j : {j : Fin (n + 1) // j < j.rev},
        (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
          (a j.val * a j.val.rev) := by
  have hmean := sum_symmetric_eq_pairs_middle n
    (fun j => GaussianSampling.scaledCosineRow n x j ^ 2)
    (by intro j; simp only [GaussianSampling.scaledCosineRow, centeredFrequency_rev,
      neg_mul, Real.cos_neg])
  have hpair (j : {j : Fin (n + 1) // j < j.rev}) :
      (if a j.val = a j.val.rev then
          4 * GaussianSampling.scaledCosineRow n x j.val ^ 2 else 0) =
        2 * GaussianSampling.scaledCosineRow n x j.val ^ 2 +
          (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
            (a j.val * a j.val.rev) := by
    have he := equal_sign_activity (a j.val) (a j.val.rev)
      ((mem_signVectors a).mp ha j.val) ((mem_signVectors a).mp ha j.val.rev)
    have hscale : 2 * GaussianSampling.scaledCosineRow n x j.val ^ 2 =
        2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2 := by
      simp only [GaussianSampling.scaledCosineRow, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    rw [← hscale]
    have hleft : (if a j.val = a j.val.rev then
        4 * GaussianSampling.scaledCosineRow n x j.val ^ 2 else 0) =
        4 * GaussianSampling.scaledCosineRow n x j.val ^ 2 *
          (if a j.val = a j.val.rev then (1 : ℝ) else 0) := by
      split_ifs <;> ring
    rw [hleft, he]
    ring
  rw [conditionalCosineVariance_pairs, hmean]
  simp_rw [hpair]
  rw [sum_add_distrib, ← mul_sum]
  ring
lemma conditionalCosineVariance_eq_of_sameSineFiber (n : ℕ)
    (a b : Fin (n + 1) → ℝ) (hab : sameSineFiber n a b) (x : ℝ) :
    conditionalCosineVariance n b x = conditionalCosineVariance n a x := by
  rw [conditionalCosineVariance_pairs, conditionalCosineVariance_pairs]
  congr 1
  apply sum_congr rfl
  intro j _
  have he : b j.val = b j.val.rev ↔ a j.val = a j.val.rev := by
    constructor <;> intro h <;> linarith [hab j.val]
  simp only [he]
lemma maskBad_congr (n : ℕ) (a b : Fin (n + 1) → ℝ)
    (hab : sameSineFiber n a b) : maskBad n b ↔ maskBad n a := by
  unfold maskBad
  simp only [conditionalCosineVariance_eq_of_sameSineFiber n a b hab]
lemma exists_free_coordinate_lift (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (u : {j // j ∈ freeIndices n a} → ℝ) :
    ∃ c : Fin (n + 1) → ℝ,
      (∀ x, (∑ j, conditionalCosineRow n a x j * u j) =
        ∑ j, GaussianSampling.scaledCosineRow n x j * c j) ∧
      (∑ j, c j ^ 2) ≤ 2 * ∑ j, u j ^ 2 := by
  let c : Fin (n + 1) → ℝ := fun j => fillFree n a u j - fillFree n a (fun _ => 0) j
  refine ⟨c, ?_, ?_⟩
  · intro x
    have he := symmetric_row_fillFree_eval n a ha (GaussianSampling.scaledCosineRow n x)
      (by intro j; simp only [GaussianSampling.scaledCosineRow, centeredFrequency_rev,
        neg_mul, Real.cos_neg]) u
    have hz := symmetric_row_fillFree_eval n a ha (GaussianSampling.scaledCosineRow n x)
      (by intro j; simp only [GaussianSampling.scaledCosineRow, centeredFrequency_rev,
        neg_mul, Real.cos_neg]) (fun _ => 0)
    simp only [mul_zero, sum_const_zero] at hz
    simp only [c, mul_sub, sum_sub_distrib, hz, sub_zero]
    exact he.symm
  · rw [sum_eq_pairs_middle, sum_free_eq_pairs_middle, mul_add, mul_sum]
    apply add_le_add
    · apply sum_le_sum
      intro j _
      have hr : j.val.rev ∉ freeIndices n a := by
        intro h
        have hh := (mem_filter.mp h).2.1
        simp only [Fin.rev_rev] at hh
        exact (not_le_of_gt j.property) hh
      by_cases hj : a j.val = a j.val.rev
      · have hf : j.val ∈ freeIndices n a := by simp [freeIndices, j.property.le, hj]
        simp only [c, fillFree, hf, hr, dite_true, dite_false, Fin.rev_rev, hj, sub_zero]
        exact le_of_eq (by ring)
      · have hf : j.val ∉ freeIndices n a := by simp [freeIndices, hj]
        simp only [c, fillFree, hf, hr, dite_false, Fin.rev_rev, hj, sub_self, mul_zero]
        norm_num
    · rw [mul_sum]
      apply sum_le_sum
      intro j _
      have hf := middle_mem_freeIndices n a j.val j.property
      simp only [c, fillFree, hf, dite_true, sub_zero]
      nlinarith [sq_nonneg (u ⟨j.val,hf⟩)]
lemma conditionalCosineRow_sampling_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {n : ℕ} (hn : 0 < n) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1))
    (t : ι → ℝ) (cell : ι → κ) (starts : κ → ℝ) (H K : ℕ)
    (hleft : ∀ j, 0 ≤ starts j)
    (hright : ∀ j, starts j + 1 ≤ 2 * Real.pi * n)
    (ht : ∀ i, t i ∈ Set.Icc (starts (cell i)) (starts (cell i) + 1))
    (hocc : ∀ j, (Finset.univ.filter (fun i => cell i = j)).card ≤ H)
    (hcover : ∀ x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi * n),
      (Finset.univ.filter (fun j => x ∈ Set.Ioc (starts j) (starts j + 1))).card ≤ K)
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ i, (∑ j, conditionalCosineRow n a (t i) j * u j) ^ 2) ≤
      (10 * Real.pi * H * K) * ∑ j, u j ^ 2 := by
  obtain ⟨c, he, hc⟩ := exists_free_coordinate_lift n a ha u
  simp_rw [he]
  exact (GaussianSampling.scaledCosineRow_sampling_bound hn t cell starts H K
    hleft hright ht hocc hcover c).trans (by
      calc
        _ ≤ (5 * Real.pi * H * K) * (2 * ∑ j, u j ^ 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring)
lemma conditionalCosineRow_normalized_sampling_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1))
    (t : ι → ℝ) (cell : ι → κ) (starts : κ → ℝ) (H K : ℕ)
    (hleft : ∀ j, 0 ≤ starts j)
    (hright : ∀ j, starts j + 1 ≤ 2 * Real.pi * n)
    (ht : ∀ i, t i ∈ Set.Icc (starts (cell i)) (starts (cell i) + 1))
    (hocc : ∀ j, (Finset.univ.filter (fun i => cell i = j)).card ≤ H)
    (hcover : ∀ x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi * n),
      (Finset.univ.filter (fun j => x ∈ Set.Ioc (starts j) (starts j + 1))).card ≤ K)
    (hvar : ∀ i, (1 : ℝ) / 8 ≤ conditionalCosineVariance n a (t i))
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ i, (∑ j, GaussianSampling.normalizedRow
      (fun i => conditionalCosineRow n a (t i)) i j * u j) ^ 2) ≤
        (80 * Real.pi * H * K) * ∑ j, u j ^ 2 := by
  have he := GaussianSampling.normalizedRow_forward_bound
    (fun i => conditionalCosineRow n a (t i)) (by norm_num : (0 : ℝ) < 1 / 8)
    hvar (conditionalCosineRow_sampling_bound hn a ha t cell starts H K
      hleft hright ht hocc hcover) u
  convert! he using 1
  ring
lemma conditionalCosineVariance_le_two_normSq (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ) :
    conditionalCosineVariance n a x ≤
      2 * ∑ j : Fin (n + 1), GaussianSampling.scaledCosineRow n x j ^ 2 := by
  rw [conditionalCosineVariance_pairs,
    sum_symmetric_eq_pairs_middle n (fun j => GaussianSampling.scaledCosineRow n x j ^ 2)
      (by intro j; simp only [GaussianSampling.scaledCosineRow, centeredFrequency_rev,
        neg_mul, Real.cos_neg]), mul_add, ← mul_assoc, mul_sum]
  apply add_le_add
  · apply sum_le_sum
    intro j _
    split_ifs
    · ring_nf
      exact le_refl _
    · positivity
  · have hmid : 0 ≤ ∑ j : {j : Fin (n + 1) // j = j.rev},
        GaussianSampling.scaledCosineRow n x j.val ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
lemma conditionalCosineVariance_le_four {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (x : ℝ) : conditionalCosineVariance n a x ≤ 4 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmean : (∑ j : Fin (n + 1), GaussianSampling.scaledCosineRow n x j ^ 2) ≤ 2 := by
    calc
      _ ≤ ∑ _j : Fin (n + 1), 1 / (n : ℝ) := by
        apply sum_le_sum
        intro j _
        simp only [GaussianSampling.scaledCosineRow, div_pow, Real.sq_sqrt hn'.le]
        apply div_le_div_of_nonneg_right _ hn'.le
        nlinarith [Real.cos_le_one (centeredFrequency n j * (x / n)),
          Real.neg_one_le_cos (centeredFrequency n j * (x / n))]
      _ = ((n : ℝ) + 1) / n := by simp [div_eq_mul_inv]
      _ ≤ 2 := (div_le_iff₀ hn').mpr (by linarith)
  exact (conditionalCosineVariance_le_two_normSq n a x).trans (by linarith)
lemma cosine_mean_bulk_lower {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Icc SignSineOccupancy.endpointCutoff
      (Real.pi * n - SignSineOccupancy.endpointCutoff)) :
    (1 : ℝ) / 4 ≤ ∑ j : Fin (n + 1), GaussianSampling.scaledCosineRow n x j ^ 2 := by
  have hcut : Real.pi ≤ SignSineOccupancy.endpointCutoff := by
    dsimp [SignSineOccupancy.endpointCutoff]
    linarith [Real.pi_pos]
  have hb : x ∈ Set.Icc Real.pi (Real.pi * n - Real.pi) :=
    ⟨hcut.trans hx.1, by linarith [hx.2]⟩
  obtain ⟨hs, hi⟩ := BulkAngles.bulk_sine_inverse_bound hn hb
  exact GaussianSampling.scaledCosineRow_normSq_lower hn hs hi
lemma not_maskBad_spec (n : ℕ) (a : Fin (n + 1) → ℝ) (hg : ¬maskBad n a)
    (x : ℝ) (hx : x ∈ Set.Icc SignSineOccupancy.endpointCutoff
      (Real.pi * n - SignSineOccupancy.endpointCutoff)) :
    (1 : ℝ) / 8 ≤ conditionalCosineVariance n a x := by
  exact le_of_not_gt (fun h => hg ⟨x,hx,h⟩)
end Fluctuations.SignConditionalRows
end
end

section
noncomputable section
open Finset Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Fluctuations.SignActivityMask
open SignPolynomialDivisibility SignConditionalRows SignActivityFiber
lemma scaled_centeredFrequency_abs_le_half {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) :
    |centeredFrequency n j / n| ≤ (1 : ℝ) / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hn').mpr
    dsimp [centeredFrequency]
    nlinarith
  · apply (div_le_iff₀ hn').mpr
    dsimp [centeredFrequency]
    nlinarith
lemma scaled_cosine_sq_lipschitz {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) (x y : ℝ) :
    |Real.cos (centeredFrequency n j * (x / n)) ^ 2 -
      Real.cos (centeredFrequency n j * (y / n)) ^ 2| ≤ (1 / 2 : ℝ) * |x - y| := by
  let u := centeredFrequency n j * (x / n)
  let v := centeredFrequency n j * (y / n)
  have he : Real.cos u ^ 2 - Real.cos v ^ 2 =
      (Real.cos (2 * u) - Real.cos (2 * v)) / 2 := by
    nlinarith [Real.cos_two_mul u, Real.cos_two_mul v]
  change |Real.cos u ^ 2 - Real.cos v ^ 2| ≤ _
  rw [he, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hd : 2 * u - 2 * v = 2 * (centeredFrequency n j / n) * (x - y) := by
    dsimp [u,v]
    ring
  calc
    _ ≤ |2 * u - 2 * v| / 2 :=
      div_le_div_of_nonneg_right (Real.abs_cos_sub_cos_le (2 * u) (2 * v)) (by norm_num)
    _ = |centeredFrequency n j / n| * |x - y| := by
      rw [hd, abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) * |x - y| :=
      mul_le_mul_of_nonneg_right (scaled_centeredFrequency_abs_le_half hn j) (abs_nonneg _)
lemma actual_mask_deviation_lipschitz {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1)) (x y : ℝ) :
    |(∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
        (a j.val * a j.val.rev)) -
      (∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (y / n)) ^ 2) *
        (a j.val * a j.val.rev))| ≤ |x - y| := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : (Fintype.card {j : Fin (n + 1) // j < j.rev} : ℝ) ≤ n := by
    linarith [lower_pair_card_le n]
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j : {j : Fin (n + 1) // j < j.rev},
      |(2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
        (a j.val * a j.val.rev) -
        (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (y / n)) ^ 2) *
          (a j.val * a j.val.rev)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : {j : Fin (n + 1) // j < j.rev}, (1 / (n : ℝ)) * |x - y| := by
      apply sum_le_sum
      intro j _
      have hp : |a j.val * a j.val.rev| = 1 := by
        rcases (mem_signVectors a).mp ha j.val with h | h <;>
          rcases (mem_signVectors a).mp ha j.val.rev with h' | h' <;> norm_num [h,h']
      rw [← sub_mul, ← mul_sub, abs_mul, abs_mul, hp, abs_of_pos (by positivity : 0 < 2 / (n : ℝ)), mul_one]
      calc
        _ ≤ (2 / (n : ℝ)) * ((1 / 2 : ℝ) * |x - y|) :=
          mul_le_mul_of_nonneg_left (scaled_cosine_sq_lipschitz hn j.val x y) (by positivity)
        _ = _ := by ring
    _ = (Fintype.card {j : Fin (n + 1) // j < j.rev} : ℝ) * ((1 / (n : ℝ)) * |x - y|) := by simp
    _ ≤ (n : ℝ) * ((1 / (n : ℝ)) * |x - y|) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp
lemma exists_bulk_mask_net (n : ℕ) :
    ∃ N : ℕ, ∃ t : Fin N → ℝ,
      (N : ℝ) ≤ 128 * Real.pi * n + 1 ∧
      (∀ k, t k ∈ Set.Icc SignSineOccupancy.endpointCutoff
        (Real.pi * n - SignSineOccupancy.endpointCutoff)) ∧
      ∀ x ∈ Set.Icc SignSineOccupancy.endpointCutoff
        (Real.pi * n - SignSineOccupancy.endpointCutoff),
        ∃ k, |x - t k| ≤ (1 : ℝ) / 128 := by
  let L := SignSineOccupancy.endpointCutoff
  let R := Real.pi * n - L
  by_cases hb : L ≤ R
  · let N := ⌊128 * (R - L)⌋₊ + 1
    let t : Fin N → ℝ := fun k => L + (k.val : ℝ) / 128
    have hnonneg : 0 ≤ 128 * (R - L) := by linarith
    have hL : 0 ≤ L := by dsimp [L,SignSineOccupancy.endpointCutoff]; positivity
    refine ⟨N,t,?_,?_,?_⟩
    · have hf := Nat.floor_le hnonneg
      dsimp [N,R]
      push_cast
      nlinarith
    · intro k
      have hk : k.val ≤ ⌊128 * (R - L)⌋₊ := Nat.le_of_lt_succ k.isLt
      have hk' : (k.val : ℝ) ≤ (⌊128 * (R - L)⌋₊ : ℝ) := by exact_mod_cast hk
      have hf := Nat.floor_le hnonneg
      change L ≤ t k ∧ t k ≤ R
      dsimp [t]
      constructor
      · exact le_add_of_nonneg_right (by positivity)
      · linarith
    · intro x hx
      change L ≤ x ∧ x ≤ R at hx
      let k : Fin N := ⟨⌊128 * (x - L)⌋₊, Nat.lt_succ_of_le (Nat.floor_mono (by linarith :
        128 * (x - L) ≤ 128 * (R - L)))⟩
      have hf := Nat.floor_le (by linarith [hx.1] : 0 ≤ 128 * (x - L))
      have hf' := Nat.lt_floor_add_one (128 * (x - L))
      refine ⟨k,?_⟩
      change |x - (L + (⌊128 * (x - L)⌋₊ : ℝ) / 128)| ≤ _
      rw [abs_of_nonneg (by linarith)]
      linarith
  · refine ⟨0,fun k => Fin.elim0 k,?_,?_,?_⟩
    · norm_num only [Nat.cast_zero]
      positivity
    · intro k
      exact Fin.elim0 k
    · intro x hx
      change L ≤ x ∧ x ≤ R at hx
      exact (hb (hx.1.trans hx.2)).elim
lemma maskBad_implies_net_deviation {n N : ℕ} (hn : 0 < n)
    (t : Fin N → ℝ)
    (ht : ∀ k, t k ∈ Set.Icc SignSineOccupancy.endpointCutoff
      (Real.pi * n - SignSineOccupancy.endpointCutoff))
    (hnet : ∀ x ∈ Set.Icc SignSineOccupancy.endpointCutoff
      (Real.pi * n - SignSineOccupancy.endpointCutoff),
      ∃ k, |x - t k| ≤ (1 : ℝ) / 128)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1))
    (hbad : maskBad n a) :
    ∃ k, (1 / 16 : ℝ) ≤ |∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (t k / n)) ^ 2) *
        (a j.val * a j.val.rev)| := by
  obtain ⟨x,hx,hxv⟩ := hbad
  obtain ⟨k,hk⟩ := hnet x hx
  have hxmean := cosine_mean_bulk_lower hn hx
  have htmean := cosine_mean_bulk_lower hn (ht k)
  have hlarge : (1 / 8 : ℝ) < |∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
        (a j.val * a j.val.rev)| := by
    rw [← conditionalCosineVariance_deviation n a ha x]
    rw [abs_of_neg (by linarith)]
    linarith
  refine ⟨k, le_of_not_gt ?_⟩
  intro hsmall
  have hd := actual_mask_deviation_lipschitz hn a ha x (t k)
  have htri := abs_add_le
    ((∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (x / n)) ^ 2) *
        (a j.val * a j.val.rev)) -
      (∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (t k / n)) ^ 2) *
        (a j.val * a j.val.rev)))
    (∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (t k / n)) ^ 2) *
        (a j.val * a j.val.rev))
  rw [sub_add_cancel] at htri
  linarith
theorem actual_mask_bad_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ) (hn : 0 < n) :
    Prob μ {ω | maskBad n (fun j => ξ j.val ω)} ≤
      2 * (128 * Real.pi * n + 1) * Real.exp (-(n : ℝ) / 2048) := by
  obtain ⟨N,t,hN,ht,hnet⟩ := exists_bulk_mask_net n
  let a : Ω → Fin (n + 1) → ℝ := fun ω j => ξ j.val ω
  have he : Prob μ {ω | maskBad n (a ω)} =
      Prob μ {ω | a ω ∈ signVectors (n + 1) ∧ maskBad n (a ω)} := by
    unfold Prob
    rw [finite_sign_event_measure μ ξ hξ (n + 1) (maskBad n),
      finite_sign_event_measure μ ξ hξ (n + 1)
        (fun v => v ∈ signVectors (n + 1) ∧ maskBad n v)]
    congr 3
    congr 1
    ext v
    simp only [mem_filter]
    tauto
  let E : Fin N → Set Ω := fun k => {ω | (1 / 16 : ℝ) ≤
    |∑ j : {j : Fin (n + 1) // j < j.rev},
      (2 / (n : ℝ) * Real.cos (centeredFrequency n j.val * (t k / n)) ^ 2) *
        (ξ j.val.val ω * ξ j.val.rev.val ω)|}
  have hsub : {ω | a ω ∈ signVectors (n + 1) ∧ maskBad n (a ω)} ⊆ ⋃ k, E k := by
    intro ω hω
    obtain ⟨k,hk⟩ := maskBad_implies_net_deviation hn t ht hnet (a ω) hω.1 hω.2
    exact Set.mem_iUnion.mpr ⟨k,hk⟩
  have htail (k : Fin N) : μ.real (E k) ≤ 2 * Real.exp (-(n : ℝ) / 2048) :=
    actual_mask_deviation_point_tail μ ξ hξ n hn (t k)
  change Prob μ {ω | maskBad n (a ω)} ≤ _
  rw [he]
  apply (measureReal_mono hsub).trans
  apply (measureReal_iUnion_fintype_le (μ := μ) E).trans
  calc
    _ ≤ ∑ _k : Fin N, 2 * Real.exp (-(n : ℝ) / 2048) :=
      sum_le_sum (fun k _ => htail k)
    _ = (N : ℝ) * (2 * Real.exp (-(n : ℝ) / 2048)) := by simp
    _ ≤ (128 * Real.pi * n + 1) * (2 * Real.exp (-(n : ℝ) / 2048)) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring
theorem actual_mask_bad_probability_le_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ) (hn : 0 < n) :
    Prob μ {ω | maskBad n (fun j => ξ j.val ω)} ≤
      (48 * (128 * Real.pi + 1) * 2048 ^ 4) * (n : ℝ) ^ (-3 : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : ((n : ℝ) / 2048) ^ 4 / 24 ≤ Real.exp ((n : ℝ) / 2048) := by
    have h := Real.pow_div_factorial_le_exp ((n : ℝ) / 2048) (by positivity : 0 ≤ (n : ℝ) / 2048) 4
    norm_num at h
    exact h
  have he : Real.exp (-(n : ℝ) / 2048) ≤ 24 * 2048 ^ 4 / (n : ℝ) ^ 4 := by
    calc
      _ = 1 / Real.exp ((n : ℝ) / 2048) := by
        rw [show -(n : ℝ) / 2048 = -((n : ℝ) / 2048) by ring, Real.exp_neg]
        simp only [one_div]
      _ ≤ 1 / (((n : ℝ) / 2048) ^ 4 / 24) :=
        one_div_le_one_div_of_le (by positivity) hpow
      _ = _ := by field_simp
  have hc : 2 * (128 * Real.pi * n + 1) ≤ 2 * ((128 * Real.pi + 1) * n) := by
    nlinarith
  have hrpow : (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 := by
    rw [Real.rpow_neg hn'.le]
    norm_num [Real.rpow_natCast,one_div]
  apply (actual_mask_bad_probability_le μ ξ hξ n hn).trans
  calc
    _ ≤ (2 * ((128 * Real.pi + 1) * n)) * (24 * 2048 ^ 4 / (n : ℝ) ^ 4) :=
      mul_le_mul hc he (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [hrpow]; field_simp; ring
end Fluctuations.SignActivityMask
end
end

section
noncomputable section
open Finset Classical
open scoped BigOperators
namespace Fluctuations.SignConditionalRows
open SignActivityFiber SignPolynomialDivisibility BoundedGramSignSmallBall
lemma exists_scalar_interval_small_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (n : ℝ) (b : Fin m → ℝ) (z R : ℝ),
      0 < n → (m : ℝ) ≤ 2 * n → (∀ j, |b j| ≤ 2) →
      n / 8 ≤ ∑ j, b j ^ 2 → 0 ≤ R →
      (((univ : Finset (Finset (Fin m))).filter
        (fun S => |vectorSignSum b S - z| ≤ R)).card : ℝ) / 2 ^ m ≤
          C * (R + 1) * n ^ (-(1 : ℝ) / 2) := by
  obtain ⟨ρ,C,hρ,hC,hball⟩ := exists_bounded_gram_sign_small_ball (E := ℝ)
    1 (by norm_num) (Module.finrank_self ℝ) 2 2 (1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C * (2 / ρ + 1), by positivity, ?_⟩
  intro m n b z R hn hm hb hgram hR
  have hpoint (u : ℝ) : (((univ : Finset (Finset (Fin m))).filter
      (fun S => |vectorSignSum b S - u| ≤ ρ)).card : ℝ) / 2 ^ m ≤
        C * n ^ (-(1 : ℝ) / 2) := by
    have hg (v : ℝ) : (1 / 8 : ℝ) * n * ‖v‖ ^ 2 ≤
        ∑ j, (inner ℝ (b j) v) ^ 2 := by
      simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs, mul_pow,
        ← sum_mul]
      nlinarith [mul_le_mul_of_nonneg_right hgram (sq_nonneg v)]
    simpa only [Real.norm_eq_abs, Nat.cast_one] using
      hball m n b u hn hm (by simpa only [Real.norm_eq_abs] using hb) hg
  let N := ⌊2 * R / ρ⌋₊ + 1
  let center : Fin N → ℝ := fun k => z - R + (k.val : ℝ) * ρ
  have hN : (N : ℝ) ≤ 2 * R / ρ + 1 := by
    dsimp [N]
    push_cast
    have hf := Nat.floor_le (by positivity : 0 ≤ 2 * R / ρ)
    linarith
  have hcover (y : ℝ) (hy : |y - z| ≤ R) : ∃ k : Fin N, |y - center k| ≤ ρ := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hy
    let k : Fin N := ⟨⌊(y - (z - R)) / ρ⌋₊, Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith : y - (z - R) ≤ 2 * R) hρ.le))⟩
    have hf := Nat.floor_le (div_nonneg (by linarith : 0 ≤ y - (z - R)) hρ.le)
    have hf' := Nat.lt_floor_add_one ((y - (z - R)) / ρ)
    have hlo' : (⌊(y - (z - R)) / ρ⌋₊ : ℝ) * ρ ≤ y - (z - R) :=
      (le_div_iff₀ hρ).mp hf
    have hhi' : y - (z - R) < ((⌊(y - (z - R)) / ρ⌋₊ : ℝ) + 1) * ρ :=
      (div_lt_iff₀ hρ).mp hf'
    refine ⟨k,?_⟩
    change |y - (z - R + (⌊(y - (z - R)) / ρ⌋₊ : ℝ) * ρ)| ≤ ρ
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  let F := (univ : Finset (Finset (Fin m))).filter (fun S => |vectorSignSum b S - z| ≤ R)
  let B : Fin N → Finset (Finset (Fin m)) := fun k =>
    univ.filter (fun S => |vectorSignSum b S - center k| ≤ ρ)
  have hsub : F ⊆ univ.biUnion B := by
    intro S hS
    obtain ⟨k,hk⟩ := hcover (vectorSignSum b S) (mem_filter.mp hS).2
    exact mem_biUnion.mpr ⟨k,mem_univ k,mem_filter.mpr ⟨mem_univ S,hk⟩⟩
  have hcards : (F.card : ℝ) ≤ ∑ k : Fin N, ((B k).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  change (F.card : ℝ) / 2 ^ m ≤ _
  calc
    _ ≤ (∑ k : Fin N, ((B k).card : ℝ)) / 2 ^ m :=
      div_le_div_of_nonneg_right hcards (by positivity)
    _ = ∑ k : Fin N, ((B k).card : ℝ) / 2 ^ m := sum_div ..
    _ ≤ ∑ _k : Fin N, C * n ^ (-(1 : ℝ) / 2) :=
      sum_le_sum (fun k _ => hpoint (center k))
    _ = (N : ℝ) * (C * n ^ (-(1 : ℝ) / 2)) := by simp
    _ ≤ (2 * R / ρ + 1) * (C * n ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ (C * (2 / ρ + 1)) * (R + 1) * n ^ (-(1 : ℝ) / 2) := by
      have hh : 2 * R / ρ + 1 ≤ (2 / ρ + 1) * (R + 1) := by
        have hp : 0 ≤ 2 / ρ := by positivity
        rw [show 2 * R / ρ = (2 / ρ) * R by ring]
        nlinarith
      calc
        _ ≤ ((2 / ρ + 1) * (R + 1)) * (C * n ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hh (by positivity)
        _ = _ := by ring
lemma scaled_conditionalCosineRow_abs_le_two {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (x : ℝ) (j : {j // j ∈ freeIndices n a}) :
    |Real.sqrt n * conditionalCosineRow n a x j| ≤ 2 := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have he : Real.sqrt n * conditionalCosineRow n a x j =
      (if j.val = j.val.rev then 1 else 2) *
        Real.cos (centeredFrequency n j.val * (x / n)) := by
    simp only [conditionalCosineRow, GaussianSampling.scaledCosineRow]
    field_simp
  rw [he]
  split_ifs
  · simpa only [one_mul] using (Real.abs_cos_le_one _).trans (by norm_num : (1 : ℝ) ≤ 2)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.abs_cos_le_one (centeredFrequency n j.val * (x / n))]
lemma free_card_le_two_degree {n : ℕ} (hn : 0 < n) (a : Fin (n + 1) → ℝ) :
    ((freeIndices n a).card : ℝ) ≤ 2 * n := by
  have hc : (freeIndices n a).card ≤ n + 1 := by
    simpa only [Fintype.card_fin] using card_le_univ (freeIndices n a)
  have hc' : ((freeIndices n a).card : ℝ) ≤ n + 1 := by exact_mod_cast hc
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith
lemma scaled_conditionalCosineRow_sq_sum {n m : ℕ} (a : Fin (n + 1) → ℝ)
    (x : ℝ) (e : Fin m ≃ {j // j ∈ freeIndices n a}) :
    (∑ j : Fin m, (Real.sqrt n * conditionalCosineRow n a x (e j)) ^ 2) =
      n * conditionalCosineVariance n a x := by
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← mul_sum]
  rw [Equiv.sum_comp e (fun j => conditionalCosineRow n a x j ^ 2)]
  rfl
lemma exists_normalized_conditional_row_small_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin (n + 1) → ℝ) (x : ℝ)
      (m : ℕ) (e : Fin m ≃ {j // j ∈ freeIndices n a}) (z r : ℝ),
      0 < n → (1 : ℝ) / 8 ≤ conditionalCosineVariance n a x → 0 ≤ r →
      (((univ : Finset (Finset (Fin m))).filter
        (fun S => |vectorSignSum
          (fun j => conditionalCosineRow n a x (e j) /
            Real.sqrt (conditionalCosineVariance n a x)) S - z| ≤ r)).card : ℝ) / 2 ^ m ≤
          C * (r + (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C,hC,hinterval⟩ := exists_scalar_interval_small_ball
  refine ⟨2*C, by positivity, ?_⟩
  intro n a x m e z r hn hvar hr
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hvpos : 0 < conditionalCosineVariance n a x := lt_of_lt_of_le (by norm_num) hvar
  have hsv : 0 < Real.sqrt (conditionalCosineVariance n a x) := Real.sqrt_pos.mpr hvpos
  let scale := Real.sqrt (n : ℝ) * Real.sqrt (conditionalCosineVariance n a x)
  let b : Fin m → ℝ := fun j => Real.sqrt n * conditionalCosineRow n a x (e j)
  let v : Fin m → ℝ := fun j => conditionalCosineRow n a x (e j) /
    Real.sqrt (conditionalCosineVariance n a x)
  have hs : 0 < scale := mul_pos hsn hsv
  have hm : (m : ℝ) ≤ 2 * n := by
    have he : m = (freeIndices n a).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e
    rw [he]
    exact free_card_le_two_degree hn a
  have hb : ∀ j, |b j| ≤ 2 := fun j => scaled_conditionalCosineRow_abs_le_two hn a x (e j)
  have hg : (n : ℝ) / 8 ≤ ∑ j, b j ^ 2 := by
    change _ ≤ ∑ j, (Real.sqrt n * conditionalCosineRow n a x (e j)) ^ 2
    rw [scaled_conditionalCosineRow_sq_sum a x e]
    nlinarith [mul_le_mul_of_nonneg_left hvar hn'.le]
  have hbound := hinterval m n b (scale*z) (scale*r) hn' hm hb hg (mul_nonneg hs.le hr)
  have heval (S : Finset (Fin m)) : vectorSignSum b S = scale * vectorSignSum v S := by
    simp only [vectorSignSum, mul_sum]
    apply sum_congr rfl
    intro j _
    have he : b j = scale * v j := by
      dsimp [b,scale,v]
      field_simp
    by_cases hj : j ∈ S
    · simp only [hj, ite_true, he]
    · simp only [hj, ite_false, he, mul_neg]
  have hf : ((univ : Finset (Finset (Fin m))).filter
      (fun S => |vectorSignSum b S - scale*z| ≤ scale*r)) =
      univ.filter (fun S => |vectorSignSum v S-z| ≤ r) := by
    apply filter_congr
    intro S _
    rw [heval, ← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_iff_right₀ hs
  rw [hf] at hbound
  change (((univ : Finset (Finset (Fin m))).filter
      (fun S => |vectorSignSum v S-z| ≤ r)).card : ℝ) / 2 ^ m ≤ _
  apply hbound.trans
  have hsvupper : Real.sqrt (conditionalCosineVariance n a x) ≤ 2 := by
    exact (Real.sqrt_le_sqrt (conditionalCosineVariance_le_four hn a x)).trans_eq (by norm_num)
  have hscale : scale ≤ 2 * Real.sqrt (n : ℝ) := by
    dsimp [scale]
    nlinarith [mul_le_mul_of_nonneg_left hsvupper hsn.le]
  have hp : (n : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (n : ℝ) := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hn'.le,
      ← Real.sqrt_eq_rpow, one_div]
  have hprod : (scale*r+1) * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
      2 * (r + (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
    calc
      _ ≤ (2 * Real.sqrt (n : ℝ) * r + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hscale hr])
          (Real.rpow_nonneg hn'.le _)
      _ = 2*r+(n : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [hp]
        field_simp
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hn'.le (-(1 : ℝ) / 2)]
  calc
    _ = C * ((scale*r+1) * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
    _ ≤ C * (2 * (r + (n : ℝ) ^ (-(1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hprod hC.le
    _ = _ := by ring
end Fluctuations.SignConditionalRows
end
end

section
namespace Fluctuations.SignedCrossings
noncomputable section
theorem exists_partition_of_finite_zeros (Y : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hfinite : Set.Finite {t | t ∈ Set.Icc a b ∧ Y t = 0}) :
    ∃ n : ℕ, ∃ knots : ℕ → ℝ, 1 ≤ n ∧ knots 0 = a ∧ knots n = b ∧
      (∀ i < n, knots i < knots (i + 1)) ∧
      (∀ i ≤ n, knots i ∈ Set.Icc a b) ∧
      ∀ i < n, ∀ t ∈ Set.Ioo (knots i) (knots (i + 1)), Y t ≠ 0 := by
  classical
  let s := insert a (insert b hfinite.toFinset)
  have ha : a ∈ s := by simp [s]
  have hb : b ∈ s := by simp [s]
  have hcard : 1 < s.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab.ne⟩
  have hbound : ∀ t ∈ s, t ∈ Set.Icc a b := by
    intro t ht
    simp only [s, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact ht.1
  let e := s.orderEmbOfFin rfl
  let knots : ℕ → ℝ := fun i => if hi : i < s.card then e ⟨i, hi⟩ else b
  have hk (i : ℕ) (hi : i < s.card) : knots i = e ⟨i, hi⟩ := by
    simp [knots, hi]
  have hknots : ∀ i < s.card, knots i ∈ Set.Icc a b := by
    intro i hi
    rw [hk i hi]
    exact hbound _ (s.orderEmbOfFin_mem rfl _)
  have hmin : knots 0 = a := by
    rw [hk 0 (by omega)]
    change s.orderEmbOfFin rfl ⟨0, _⟩ = a
    rw [Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (s.min'_le a ha) (hbound _ (s.min'_mem _)).1
  have hmax : knots (s.card - 1) = b := by
    rw [hk (s.card - 1) (by omega)]
    change s.orderEmbOfFin rfl ⟨s.card - 1, _⟩ = b
    rw [Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm (hbound _ (s.max'_mem _)).2 (s.le_max' b hb)
  refine ⟨s.card - 1, knots, by omega, hmin, hmax, ?_, ?_, ?_⟩
  · intro i hi
    rw [hk i (by omega), hk (i + 1) (by omega)]
    exact e.strictMono (by simp)
  · intro i hi
    exact hknots i (by omega)
  · intro i hi t ht hyt
    have hit : i < s.card := by omega
    have his : i + 1 < s.card := by omega
    have htbound : t ∈ Set.Icc a b :=
      ⟨(hknots i hit).1.trans ht.1.le, ht.2.le.trans (hknots (i + 1) his).2⟩
    have hts : t ∈ s := by
      simp only [s, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact Or.inr (Or.inr ⟨htbound, hyt⟩)
    obtain ⟨j, hj⟩ : ∃ j : Fin s.card, e j = t := by
      change t ∈ Set.range e
      rw [show Set.range e = (s : Set ℝ) from s.range_orderEmbOfFin rfl]
      exact hts
    rw [hk i hit, hk (i + 1) his, ← hj] at ht
    have hl : (⟨i, hit⟩ : Fin s.card) < j := e.lt_iff_lt.mp ht.1
    have hu : j < (⟨i + 1, his⟩ : Fin s.card) := e.lt_iff_lt.mp ht.2
    have hl' : i < j.val := hl
    have hu' : j.val < i + 1 := hu
    omega
end
end Fluctuations.SignedCrossings
end

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Fluctuations.FiniteOrderCrossings
open SignedCrossings
lemma analyticOrderAt_real_restriction {f : ℂ → ℂ} {t : ℝ}
    (hf : AnalyticAt ℂ f (t : ℂ)) (hfinite : analyticOrderAt f (t : ℂ) ≠ ⊤)
    (hreal : ∀ s : ℝ, (f (s : ℂ)).im = 0) :
    analyticOrderAt (fun s : ℝ => (f (s : ℂ)).re) t =
      analyticOrderAt f (t : ℂ) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hcast : Tendsto Complex.ofReal (𝓝 t) (𝓝 (t : ℂ)) :=
    Complex.continuous_ofReal.tendsto t
  have hfact := hcast.eventually hfactor
  have him : ∀ᶠ (s : ℝ) in 𝓝[≠] t, (g (s : ℂ)).im = 0 := by
    filter_upwards [hfact.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs hst
    have hm : (s - t) ^ analyticOrderNatAt f (t : ℂ) ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hst)
    have he := congrArg Complex.im hs
    simp only [smul_eq_mul, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hreal] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hm
  have hcont : ContinuousAt (fun s : ℝ => (g (s : ℂ)).im) t :=
    Complex.continuous_im.continuousAt.comp (hg.continuousAt.comp hcast)
  have hzero : (g (t : ℂ)).im = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (by filter_upwards [him] with s hs using hs.symm))
  have hgre : (g (t : ℂ)).re ≠ 0 := by
    intro he
    exact hg0 (Complex.ext he hzero)
  have han : AnalyticAt ℝ (fun s : ℝ => (f (s : ℂ)).re) t :=
    (Complex.reCLM.analyticAt (f (t : ℂ))).comp (f := fun s : ℝ => f (s : ℂ))
      (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt t))
  have hgan : AnalyticAt ℝ (fun s : ℝ => (g (s : ℂ)).re) t :=
    (Complex.reCLM.analyticAt (g (t : ℂ))).comp (f := fun s : ℝ => g (s : ℂ))
      (hg.restrictScalars.comp (Complex.ofRealCLM.analyticAt t))
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  apply han.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun s => (g (s : ℂ)).re, hgan, hgre, ?_⟩
  filter_upwards [hfact] with s hs
  have he := congrArg Complex.re hs
  simpa only [smul_eq_mul, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he
lemma eventually_sign_right_of_power_factor {Y g : ℝ → ℝ} {t : ℝ} {m : ℕ}
    (hg : ContinuousAt g t) (hg0 : g t ≠ 0)
    (hY : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s) :
    ∀ᶠ s in 𝓝[>] t, SignType.sign (Y s) = SignType.sign (g t) := by
  filter_upwards [hY.filter_mono nhdsWithin_le_nhds,
    (eventually_sign_eq_of_continuousAt hg hg0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hsg hst
  rw [hs, sign_mul, sign_pow, sign_pos (sub_pos.mpr hst), one_pow, one_mul, hsg]
lemma eventually_sign_left_of_power_factor {Y g : ℝ → ℝ} {t : ℝ} {m : ℕ}
    (hg : ContinuousAt g t) (hg0 : g t ≠ 0)
    (hY : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s) :
    ∀ᶠ s in 𝓝[<] t,
      SignType.sign (Y s) = (-1 : SignType) ^ m * SignType.sign (g t) := by
  filter_upwards [hY.filter_mono nhdsWithin_le_nhds,
    (eventually_sign_eq_of_continuousAt hg hg0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hsg hst
  rw [hs, sign_mul, sign_pow, sign_neg (sub_neg.mpr hst), hsg]
lemma exists_real_power_factor {Y : ℝ → ℝ} {t : ℝ}
    (hY : AnalyticAt ℝ Y t) (hfinite : analyticOrderAt Y t ≠ ⊤) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g t ∧ g t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ analyticOrderNatAt Y t * g s := by
  simpa only [smul_eq_mul, Filter.EventuallyEq] using hY.analyticOrderAt_ne_top.mp hfinite
lemma tendsto_branchArgument_right_of_power_factor {X Y g : ℝ → ℝ} {t : ℝ} {m : ℕ}
    (hX : ContinuousAt X t) (hY : ContinuousAt Y t)
    (hg : ContinuousAt g t) (hx : X t ≠ 0) (hy : Y t = 0) (hg0 : g t ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s) :
    Tendsto (fun s => branchArgument (X s) (Y s)) (𝓝[>] t)
      (𝓝 (-(Real.pi / 2) * crossingOrientation (X t) (g t))) := by
  have hbase := (Real.continuous_arctan.continuousAt.comp (hY.div hX hx)).tendsto
  simp only [Function.comp_apply, Pi.div_apply] at hbase
  have ht := (hbase.mono_left (nhdsWithin_le_nhds : 𝓝[>] t ≤ 𝓝 t)).sub_const
    (Real.pi / 2 * (SignType.sign (X t) : ℝ) * (SignType.sign (g t) : ℝ))
  simp only [hy, zero_div, Real.arctan_zero, zero_sub] at ht
  have hsignX := (eventually_sign_eq_of_continuousAt hX hx).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] t ≤ 𝓝 t)
  have hsignY := eventually_sign_right_of_power_factor hg hg0 hfactor
  have heq : (fun s => Real.arctan (Y s / X s) -
      Real.pi / 2 * (SignType.sign (X t) : ℝ) * (SignType.sign (g t) : ℝ)) =ᶠ[𝓝[>] t]
      (fun s => branchArgument (X s) (Y s)) := by
    filter_upwards [hsignX, hsignY] with s hsX hsY
    have hx' : X s ≠ 0 := sign_ne_zero.mp (by rw [hsX]; exact sign_ne_zero.mpr hx)
    have hy' : Y s ≠ 0 := sign_ne_zero.mp (by rw [hsY]; exact sign_ne_zero.mpr hg0)
    rw [branchArgument_eq_atan_sub_sign hx' hy', hsX, hsY]
  convert! ht.congr' heq using 1
  simp [crossingOrientation, mul_assoc]
lemma tendsto_branchArgument_left_of_power_factor {X Y g : ℝ → ℝ} {t : ℝ} {m : ℕ}
    (hX : ContinuousAt X t) (hY : ContinuousAt Y t)
    (hg : ContinuousAt g t) (hx : X t ≠ 0) (hy : Y t = 0) (hg0 : g t ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s) :
    Tendsto (fun s => branchArgument (X s) (Y s)) (𝓝[<] t)
      (𝓝 (-(Real.pi / 2) * (-1 : ℝ) ^ m * crossingOrientation (X t) (g t))) := by
  have hbase := (Real.continuous_arctan.continuousAt.comp (hY.div hX hx)).tendsto
  simp only [Function.comp_apply, Pi.div_apply] at hbase
  have ht := (hbase.mono_left (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t)).sub_const
    (Real.pi / 2 * (SignType.sign (X t) : ℝ) *
      ((-1 : ℝ) ^ m * (SignType.sign (g t) : ℝ)))
  simp only [hy, zero_div, Real.arctan_zero, zero_sub] at ht
  have hsignX := (eventually_sign_eq_of_continuousAt hX hx).filter_mono
    (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t)
  have hsignY := eventually_sign_left_of_power_factor hg hg0 hfactor
  have heq : (fun s => Real.arctan (Y s / X s) -
      Real.pi / 2 * (SignType.sign (X t) : ℝ) *
        ((-1 : ℝ) ^ m * (SignType.sign (g t) : ℝ))) =ᶠ[𝓝[<] t]
      (fun s => branchArgument (X s) (Y s)) := by
    filter_upwards [hsignX, hsignY] with s hsX hsY
    have hx' : X s ≠ 0 := sign_ne_zero.mp (by rw [hsX]; exact sign_ne_zero.mpr hx)
    have hn : (-1 : SignType) ^ m * SignType.sign (g t) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by decide)) (sign_ne_zero.mpr hg0)
    have hy' : Y s ≠ 0 := sign_ne_zero.mp (by rw [hsY]; exact hn)
    rw [branchArgument_eq_atan_sub_sign hx' hy', hsX, hsY, SignType.coe_mul,
      SignType.coe_pow]
    rfl
  convert! ht.congr' heq using 1
  simp only [crossingOrientation]
  ring_nf
lemma finite_order_branch_jump (x a : ℝ) (m : ℕ) :
    -(Real.pi / 2) * (-1 : ℝ) ^ m * crossingOrientation x a -
      (-(Real.pi / 2) * crossingOrientation x a) =
        Real.pi * (if Odd m then crossingOrientation x a else 0) := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow, if_neg (Nat.not_odd_iff_even.mpr hm)]
    ring_nf
  · rw [hm.neg_one_pow, if_pos hm]
    ring_nf
lemma crossingOrientation_mul_real {r : ℝ} (hr : r ≠ 0) (x a : ℝ) :
    crossingOrientation (r * x) (r * a) = crossingOrientation x a := by
  unfold crossingOrientation
  rw [sign_mul, sign_mul, SignType.coe_mul, SignType.coe_mul]
  rcases hr.lt_or_gt with hr | hr
  · rw [sign_neg hr]
    norm_num
  · rw [sign_pos hr]
    norm_num
lemma abs_branchArgument_limit_le {X Y : ℝ → ℝ} {l : Filter ℝ} [NeBot l] {a : ℝ}
    (ha : Tendsto (fun s => branchArgument (X s) (Y s)) l (𝓝 a)) :
    |a| ≤ Real.pi / 2 := by
  exact le_of_tendsto' ha.abs (fun s => (abs_branchArgument_lt (X s) (Y s)).le)
private lemma sum_limit_segments (r l : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range n, (l (i + 1) - r i)) =
      l n - r 0 + ∑ i ∈ Finset.Ico 1 n, (l i - r i) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hn]
    ring_nf
theorem integral_angularVelocity_finite_limits
    (X Y DX DY : ℝ → ℝ) (knots r l : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hstep : ∀ i < n, knots i < knots (i + 1))
    (hX : ∀ t, HasDerivAt X (DX t) t) (hY : ∀ t, HasDerivAt Y (DY t) t)
    (hzero : ∀ i < n, ∀ t ∈ Ioo (knots i) (knots (i + 1)), Y t ≠ 0)
    (hr : ∀ i ≤ n, Tendsto (fun t => branchArgument (X t) (Y t))
      (𝓝[>] (knots i)) (𝓝 (r i)))
    (hl : ∀ i ≤ n, Tendsto (fun t => branchArgument (X t) (Y t))
      (𝓝[<] (knots i)) (𝓝 (l i)))
    (hint : ∀ i < n, IntervalIntegrable
      (fun t => angularVelocity (X t) (Y t) (DX t) (DY t)) volume
      (knots i) (knots (i + 1))) :
    (∫ t in knots 0..knots n, angularVelocity (X t) (Y t) (DX t) (DY t)) =
      l n - r 0 + ∑ i ∈ Finset.Ico 1 n, (l i - r i) := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  calc
    _ = ∑ i ∈ Finset.range n, (l (i + 1) - r i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (hstep i hi')
        (fun t ht => hasDerivAt_branchArgument (hX t) (hY t) (hzero i hi' t ht))
        (hint i hi') (hr i (by omega)) (hl (i + 1) (by omega))
    _ = _ := sum_limit_segments r l hn
theorem abs_integral_div_two_pi_sub_finite_jumps_le_half
    (X Y DX DY : ℝ → ℝ) (knots r l w : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hstep : ∀ i < n, knots i < knots (i + 1))
    (hX : ∀ t, HasDerivAt X (DX t) t) (hY : ∀ t, HasDerivAt Y (DY t) t)
    (hDX : Continuous DX) (hDY : Continuous DY)
    (hne : ∀ t ∈ Icc (knots 0) (knots n), X t ≠ 0 ∨ Y t ≠ 0)
    (hzero : ∀ i < n, ∀ t ∈ Ioo (knots i) (knots (i + 1)), Y t ≠ 0)
    (hr : ∀ i ≤ n, Tendsto (fun t => branchArgument (X t) (Y t))
      (𝓝[>] (knots i)) (𝓝 (r i)))
    (hl : ∀ i ≤ n, Tendsto (fun t => branchArgument (X t) (Y t))
      (𝓝[<] (knots i)) (𝓝 (l i)))
    (hjump : ∀ i ∈ Finset.Ico 1 n, l i - r i = Real.pi * w i) :
    |(∫ t in knots 0..knots n, angularVelocity (X t) (Y t) (DX t) (DY t)) /
      (2 * Real.pi) - (1 / 2 : ℝ) * ∑ i ∈ Finset.Ico 1 n, w i| ≤ 1 / 2 := by
  have hmono : ∀ j : ℕ, j ≤ n → ∀ i ≤ j, knots i ≤ knots j := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have he : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      intro hj i hi
      by_cases he : i = j + 1
      · subst i
        exact le_rfl
      · exact (ih (by omega) i (by omega)).trans (hstep j (by omega)).le
  have hint : ∀ i < n, IntervalIntegrable
      (fun t => angularVelocity (X t) (Y t) (DX t) (DY t)) volume
      (knots i) (knots (i + 1)) := by
    intro i hi
    apply intervalIntegrable_angularVelocity X Y DX DY (hstep i hi).le
      (continuous_iff_continuousAt.mpr (fun t => (hX t).continuousAt)).continuousOn
      (continuous_iff_continuousAt.mpr (fun t => (hY t).continuousAt)).continuousOn
      hDX.continuousOn hDY.continuousOn
    intro t ht
    exact hne t ⟨(hmono i (by omega) 0 (by omega)).trans ht.1,
      ht.2.trans (hmono n le_rfl (i + 1) (by omega))⟩
  rw [integral_angularVelocity_finite_limits X Y DX DY knots r l hn hstep hX hY
    hzero hr hl hint]
  have hsum : ∑ i ∈ Finset.Ico 1 n, (l i - r i) =
      Real.pi * ∑ i ∈ Finset.Ico 1 n, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hjump i hi)
  rw [hsum]
  have he : (l n - r 0 + Real.pi * ∑ i ∈ Finset.Ico 1 n, w i) / (2 * Real.pi) -
      (1 / 2 : ℝ) * ∑ i ∈ Finset.Ico 1 n, w i = (l n - r 0) / (2 * Real.pi) := by
    field_simp
    ring_nf
  rw [he, abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hlb := abs_branchArgument_limit_le (hl n le_rfl)
  have hrb := abs_branchArgument_limit_le (hr 0 (by omega))
  have hb : |l n - r 0| ≤ Real.pi := by
    have ht := abs_sub (l n) (r 0)
    linarith
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  linarith
theorem abs_integral_div_two_pi_sub_finite_order_crossings_le_half
    (X Y DX DY : ℝ → ℝ) (knots : ℕ → ℝ) (g : ℕ → ℝ → ℝ)
    {n : ℕ} (hn : 1 ≤ n)
    (hstep : ∀ i < n, knots i < knots (i + 1))
    (hX : ∀ t, HasDerivAt X (DX t) t) (hY : ∀ t, HasDerivAt Y (DY t) t)
    (hDX : Continuous DX) (hDY : Continuous DY)
    (hne : ∀ t ∈ Icc (knots 0) (knots n), X t ≠ 0 ∨ Y t ≠ 0)
    (hzero : ∀ i < n, ∀ t ∈ Ioo (knots i) (knots (i + 1)), Y t ≠ 0)
    (hknots : ∀ i ≤ n, knots i ∈ Icc (knots 0) (knots n))
    (hfactor : ∀ i ≤ n, Y (knots i) = 0 →
      ContinuousAt (g i) (knots i) ∧ g i (knots i) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (knots i), Y s =
        (s - knots i) ^ analyticOrderNatAt Y (knots i) * g i s) :
    |(∫ t in knots 0..knots n, angularVelocity (X t) (Y t) (DX t) (DY t)) /
      (2 * Real.pi) - (1 / 2 : ℝ) * ∑ i ∈ Finset.Ico 1 n,
        (if Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i)) then
          crossingOrientation (X (knots i)) (g i (knots i)) else 0)| ≤ 1 / 2 := by
  classical
  let r : ℕ → ℝ := fun i => if Y (knots i) = 0 then
    -(Real.pi / 2) * crossingOrientation (X (knots i)) (g i (knots i))
    else branchArgument (X (knots i)) (Y (knots i))
  let l : ℕ → ℝ := fun i => if Y (knots i) = 0 then
    -(Real.pi / 2) * (-1 : ℝ) ^ analyticOrderNatAt Y (knots i) *
      crossingOrientation (X (knots i)) (g i (knots i))
    else branchArgument (X (knots i)) (Y (knots i))
  apply abs_integral_div_two_pi_sub_finite_jumps_le_half X Y DX DY knots r l
    (fun i => if Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i)) then
      crossingOrientation (X (knots i)) (g i (knots i)) else 0)
    hn hstep hX hY hDX hDY hne hzero
  · intro i hi
    by_cases hy : Y (knots i) = 0
    · obtain ⟨hg, hg0, hf⟩ := hfactor i hi hy
      have hx := (hne (knots i) (hknots i hi)).resolve_right (not_not.mpr hy)
      simpa only [r, if_pos hy] using
        tendsto_branchArgument_right_of_power_factor (hX _).continuousAt
          (hY _).continuousAt hg hx hy hg0 hf
    · have hc : ContinuousAt (fun s => branchArgument (X s) (Y s)) (knots i) :=
        Real.continuous_arctan.continuousAt.comp
          ((hX _).continuousAt.neg.div (hY _).continuousAt hy)
      simpa only [r, if_neg hy] using
        hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (knots i) ≤ 𝓝 (knots i))
  · intro i hi
    by_cases hy : Y (knots i) = 0
    · obtain ⟨hg, hg0, hf⟩ := hfactor i hi hy
      have hx := (hne (knots i) (hknots i hi)).resolve_right (not_not.mpr hy)
      simpa only [l, if_pos hy] using
        tendsto_branchArgument_left_of_power_factor (hX _).continuousAt
          (hY _).continuousAt hg hx hy hg0 hf
    · have hc : ContinuousAt (fun s => branchArgument (X s) (Y s)) (knots i) :=
        Real.continuous_arctan.continuousAt.comp
          ((hX _).continuousAt.neg.div (hY _).continuousAt hy)
      simpa only [l, if_neg hy] using
        hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] (knots i) ≤ 𝓝 (knots i))
  · intro i _
    by_cases hy : Y (knots i) = 0
    · simpa only [r, l, if_pos hy, hy, true_and] using
        finite_order_branch_jump (X (knots i)) (g i (knots i))
          (analyticOrderNatAt Y (knots i))
    · simp only [r, l, if_neg hy, hy, false_and, ite_false, sub_self, mul_zero]
theorem exists_finite_order_crossing_bound
    (X Y DX DY : ℝ → ℝ) (knots : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hstep : ∀ i < n, knots i < knots (i + 1))
    (hX : ∀ t, HasDerivAt X (DX t) t) (hY : ∀ t, HasDerivAt Y (DY t) t)
    (hDX : Continuous DX) (hDY : Continuous DY)
    (hne : ∀ t ∈ Icc (knots 0) (knots n), X t ≠ 0 ∨ Y t ≠ 0)
    (hzero : ∀ i < n, ∀ t ∈ Ioo (knots i) (knots (i + 1)), Y t ≠ 0)
    (hknots : ∀ i ≤ n, knots i ∈ Icc (knots 0) (knots n))
    (han : ∀ i ≤ n, Y (knots i) = 0 → AnalyticAt ℝ Y (knots i))
    (hfinite : ∀ i ≤ n, Y (knots i) = 0 → analyticOrderAt Y (knots i) ≠ ⊤) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ i ≤ n, Y (knots i) = 0 →
        AnalyticAt ℝ (g i) (knots i) ∧ g i (knots i) ≠ 0 ∧
        ∀ᶠ s in 𝓝 (knots i), Y s =
          (s - knots i) ^ analyticOrderNatAt Y (knots i) * g i s) ∧
      |(∫ t in knots 0..knots n, angularVelocity (X t) (Y t) (DX t) (DY t)) /
        (2 * Real.pi) - (1 / 2 : ℝ) * ∑ i ∈ Finset.Ico 1 n,
          (if Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i)) then
            crossingOrientation (X (knots i)) (g i (knots i)) else 0)| ≤ 1 / 2 := by
  classical
  choose! g hg using fun (i : ℕ) (hi : i ≤ n) (hy : Y (knots i) = 0) =>
    exists_real_power_factor (han i hi hy) (hfinite i hi hy)
  refine ⟨g, hg, ?_⟩
  apply abs_integral_div_two_pi_sub_finite_order_crossings_le_half
    X Y DX DY knots g hn hstep hX hY hDX hDY hne hzero hknots
  intro i hi hy
  exact ⟨(hg i hi hy).1.continuousAt, (hg i hi hy).2⟩
end Fluctuations.FiniteOrderCrossings
end
end

section
noncomputable section
open Polynomial Complex Finset Filter Set
open scoped BigOperators Topology
namespace Fluctuations.UnitCircleBoundaryFactorization
lemma exp_circle_sub_exp_circle (t θ : ℝ) :
    Complex.exp (I * (t : ℂ)) - Complex.exp (I * (θ : ℂ)) =
      2 * I * Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) *
        (Real.sin ((t - θ) / 2) : ℂ) := by
  have hplus : Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) *
      Complex.exp (((t : ℂ) - (θ : ℂ)) / 2 * I) = Complex.exp (I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hminus : Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) *
      Complex.exp (-(((t : ℂ) - (θ : ℂ)) / 2) * I) = Complex.exp (I * (θ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [Complex.ofReal_sin, Complex.sin, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_ofNat]
  calc
    _ = Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) *
        Complex.exp (((t : ℂ) - (θ : ℂ)) / 2 * I) -
      Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) *
        Complex.exp (-(((t : ℂ) - (θ : ℂ)) / 2) * I) := by rw [hplus, hminus]
    _ = _ := by
      ring_nf
      simp only [I_sq]
      ring
lemma rotated_circle_difference (t θ : ℝ) :
    Complex.exp (-I * (t : ℂ) / 2) *
      (Complex.exp (I * (t : ℂ)) - Complex.exp (I * (θ : ℂ))) =
        (2 * I * Complex.exp (I * (θ : ℂ) / 2)) *
          (Real.sin ((t - θ) / 2) : ℂ) := by
  have he : Complex.exp (-I * (t : ℂ) / 2) *
      Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2) =
        Complex.exp (I * (θ : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [exp_circle_sub_exp_circle]
  calc
    _ = 2 * I * (Complex.exp (-I * (t : ℂ) / 2) *
      Complex.exp (I * ((t : ℂ) + (θ : ℂ)) / 2)) *
        (Real.sin ((t - θ) / 2) : ℂ) := by ring
    _ = _ := by rw [he]
lemma exp_I_arg_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (I * (Complex.arg z : ℂ)) = z := by
  simpa only [hz, Complex.ofReal_one, one_mul, mul_one, mul_comm] using
    Complex.norm_mul_exp_arg_mul_I z
lemma rotated_boundary_product (R : Multiset ℂ)
    (hnorm : ∀ z ∈ R, ‖z‖ = 1) (t : ℝ) :
    Complex.exp (-I * (R.card : ℂ) * (t : ℂ) / 2) *
      (R.map (fun z => Complex.exp (I * (t : ℂ)) - z)).prod =
        (R.map (fun z => 2 * I * Complex.exp (I * (Complex.arg z : ℂ) / 2))).prod *
          ((R.map (fun z => Real.sin ((t - Complex.arg z) / 2))).prod : ℂ) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | @cons z R ih =>
    have hz : ‖z‖ = 1 := hnorm z (by simp)
    have hR : ∀ w ∈ R, ‖w‖ = 1 := fun w hw => hnorm w (by simp [hw])
    have he : Complex.exp (-I * ((R.card : ℂ) + 1) * (t : ℂ) / 2) =
        Complex.exp (-I * (R.card : ℂ) * (t : ℂ) / 2) *
          Complex.exp (-I * (t : ℂ) / 2) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one, Multiset.map_cons,
      Multiset.prod_cons, Complex.ofReal_mul]
    rw [he]
    calc
      _ = (Complex.exp (-I * (t : ℂ) / 2) *
          (Complex.exp (I * (t : ℂ)) - Complex.exp (I * (Complex.arg z : ℂ)))) *
        (Complex.exp (-I * (R.card : ℂ) * (t : ℂ) / 2) *
          (R.map (fun w => Complex.exp (I * (t : ℂ)) - w)).prod) := by
            rw [exp_I_arg_of_norm_eq_one hz]
            ring
      _ = _ := by
        rw [rotated_circle_difference, ih hR]
        ring
lemma boundary_phase_constant_ne_zero (R : Multiset ℂ) :
    (R.map (fun z => 2 * I * Complex.exp (I * (Complex.arg z : ℂ) / 2))).prod ≠ 0 := by
  induction R using Multiset.induction_on with
  | empty => simp
  | @cons z R ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (Complex.exp_ne_zero _)) ih
lemma eval_boundary_product (R : Multiset ℂ) (z : ℂ) :
    ((R.map (fun w => X - C w)).prod).eval z =
      (R.map (fun w => z - w)).prod := by
  change (evalRingHom z) ((R.map (fun w => X - C w)).prod) = _
  rw [map_multiset_prod, Multiset.map_map]
  simp
lemma rotated_curve_boundary_factorization
    (p q : Polynomial ℂ) (R : Multiset ℂ) (n : ℕ)
    (hR : ∀ z ∈ R, ‖z‖ = 1) (hB : R.card ≤ n)
    (hfactor : p = (R.map (fun z => X - C z)).prod * q) (t : ℝ) :
    PolynomialCircle.rotatedCircleCurve n p t =
      ((R.map (fun z => Real.sin ((t - Complex.arg z) / 2))).prod : ℂ) *
        ((R.map (fun z => 2 * I * Complex.exp (I * (Complex.arg z : ℂ) / 2))).prod *
          PolynomialCircle.rotatedCircleCurve (n - R.card) q t) := by
  have hphase : Complex.exp (-I * (n : ℂ) * (t : ℂ) / 2) =
      Complex.exp (-I * (R.card : ℂ) * (t : ℂ) / 2) *
        Complex.exp (-I * ((n - R.card : ℕ) : ℂ) * (t : ℂ) / 2) := by
    rw [← Complex.exp_add, Nat.cast_sub hB]
    congr 1
    ring
  simp only [PolynomialCircle.rotatedCircleCurve, PolynomialCircle.phaseFactor_eq_exp,
    PolynomialCircle.unitCircleCurve_eq_exp, hfactor, eval_mul, eval_boundary_product]
  rw [hphase]
  calc
    _ = (Complex.exp (-I * (R.card : ℂ) * (t : ℂ) / 2) *
        (R.map (fun z => Complex.exp (I * (t : ℂ)) - z)).prod) *
      (Complex.exp (-I * ((n - R.card : ℕ) : ℂ) * (t : ℂ) / 2) *
        q.eval (Complex.exp (I * (t : ℂ)))) := by ring
    _ = _ := by
      rw [rotated_boundary_product R hR]
      ring
lemma logDerivative_const_mul_rotated (m : ℕ) (q : Polynomial ℂ)
    (C₀ : ℂ) (hC : C₀ ≠ 0) (t : ℝ) :
    deriv (fun s => C₀ * PolynomialCircle.rotatedCircleCurve m q s) t /
      (C₀ * PolynomialCircle.rotatedCircleCurve m q t) =
        deriv (PolynomialCircle.rotatedCircleCurve m q) t /
          PolynomialCircle.rotatedCircleCurve m q t := by
  rw [((PolynomialCircle.hasDerivAt_rotatedCircleCurve m q t).const_mul C₀).deriv,
    PolynomialCircle.deriv_rotatedCircleCurve]
  exact mul_div_mul_left _ _ hC
theorem normalized_integral_quotient_curve
    (m : ℕ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → q.eval z ≠ 0)
    (C₀ : ℂ) (hC : C₀ ≠ 0) :
    (2 * Real.pi)⁻¹ *
      (∫ t in 0..2 * Real.pi,
        (deriv (fun s => C₀ * PolynomialCircle.rotatedCircleCurve m q s) t /
          (C₀ * PolynomialCircle.rotatedCircleCurve m q t)).im) =
            ((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (m : ℝ) / 2 := by
  simp_rw [logDerivative_const_mul_rotated m q C₀ hC]
  exact PolynomialCircle.normalized_integral_rotated_argumentRate_eq_closedCount_sub
    m q hq hboundary
theorem exists_boundary_root_quotient (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧
      p = ((p.roots.filter (fun z => ‖z‖ = 1)).map (fun z => X - C z)).prod * q ∧
      q.roots = p.roots.filter (fun z => ‖z‖ ≠ 1) ∧
      (∀ z : ℂ, ‖z‖ = 1 → q.eval z ≠ 0) ∧
      p.natDegree = (p.roots.filter (fun z => ‖z‖ = 1)).card + q.natDegree ∧
      (p.roots.filter (fun z => ‖z‖ ≤ 1)).card =
        (q.roots.filter (fun z => ‖z‖ ≤ 1)).card +
          (p.roots.filter (fun z => ‖z‖ = 1)).card := by
  classical
  let R := p.roots.filter (fun z => ‖z‖ = 1)
  have hdvd : (R.map (fun z => X - C z)).prod ∣ p :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hp R).mpr (Multiset.filter_le _ _)
  obtain ⟨q, he⟩ := hdvd
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at he
    exact hp he
  have hroots : p.roots = R + q.roots := by
    rw [he, roots_mul (he ▸ hp), roots_multiset_prod_X_sub_C]
  have hsplit : R + p.roots.filter (fun z => ‖z‖ ≠ 1) = p.roots :=
    Multiset.filter_add_not (fun z => ‖z‖ = 1) p.roots
  have hremain : q.roots = p.roots.filter (fun z => ‖z‖ ≠ 1) :=
    add_left_cancel (hroots.symm.trans hsplit.symm)
  refine ⟨q, hq, he, hremain, ?_, ?_, ?_⟩
  · intro z hz hqz
    have hm : z ∈ q.roots := (mem_roots hq).mpr hqz
    rw [hremain] at hm
    exact (Multiset.mem_filter.mp hm).2 hz
  · change p.natDegree = R.card + q.natDegree
    conv_lhs => rw [he]
    rw [(monic_multisetProd_X_sub_C R).natDegree_mul' hq,
      natDegree_multiset_prod_X_sub_C_eq_card]
  · change (p.roots.filter (fun z => ‖z‖ ≤ 1)).card =
      (q.roots.filter (fun z => ‖z‖ ≤ 1)).card + R.card
    have hR : R.filter (fun z => ‖z‖ ≤ 1) = R := by
      apply Multiset.filter_eq_self.mpr
      intro z hz
      exact ((Multiset.mem_filter.mp hz).2 : ‖z‖ = 1).le
    rw [hroots, Multiset.filter_add, hR, Multiset.card_add]
    exact Nat.add_comm _ _
lemma quotient_nominal_degree_bound (p q : Polynomial ℂ) (n B : ℕ)
    (hdegree : p.natDegree ≤ n) (hsplit : p.natDegree = B + q.natDegree) :
    B ≤ n ∧ q.natDegree ≤ n - B := by
  omega
lemma discrepancy_boundary_shift (n B N M : ℕ)
    (hB : B ≤ n) (hcount : N = M + B) :
    (N : ℝ) - (n : ℝ) / 2 =
      ((M : ℝ) - ((n - B : ℕ) : ℝ) / 2) + (B : ℝ) / 2 := by
  rw [hcount, Nat.cast_add, Nat.cast_sub hB]
  ring
end Fluctuations.UnitCircleBoundaryFactorization
end
end

section
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace Fluctuations.FiniteOrderCrossingComparison
open SignedCrossings FiniteOrderCrossings
lemma real_analytic_order_finite {Y : ℝ → ℝ} (hY : ∀ t, AnalyticAt ℝ Y t)
    (hne : Y ≠ 0) (t : ℝ) : analyticOrderAt Y t ≠ ⊤ := by
  intro htop
  exact hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero t hY).mp htop)
lemma real_analytic_zeros_finite {Y : ℝ → ℝ} (hY : ∀ t, AnalyticAt ℝ Y t)
    (hne : Y ≠ 0) (a b : ℝ) : Set.Finite {t | t ∈ Icc a b ∧ Y t = 0} := by
  have hglobal : AnalyticOnNhd ℝ Y univ := fun t _ => hY t
  rcases hglobal.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
    with hz | hnz
  · exact False.elim (hne (funext (fun t => hz (mem_univ t))))
  · have ht : {t | Y t ≠ 0} ∈ Filter.codiscreteWithin (Icc a b) :=
      hnz.filter_mono (Filter.codiscreteWithin_mono (subset_univ _))
    apply (isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin ht).subset
    intro t ht
    exact ⟨ht.1, fun hn => hn ht.2⟩
lemma exists_real_power_factors {Y : ℝ → ℝ} (hY : ∀ t, AnalyticAt ℝ Y t)
    (hne : Y ≠ 0) :
    ∃ g : ℝ → ℝ → ℝ, ∀ t, AnalyticAt ℝ (g t) t ∧ g t t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ analyticOrderNatAt Y t * g t s := by
  classical
  have hex (t : ℝ) := exists_real_power_factor (hY t) (real_analytic_order_finite hY hne t)
  exact Classical.axiomOfChoice hex
lemma power_factor_value_unique {Y g h : ℝ → ℝ} {t : ℝ} {m : ℕ}
    (hg : ContinuousAt g t) (hh : ContinuousAt h t)
    (hfactorG : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s)
    (hfactorH : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * h s) : g t = h t := by
  have he : g =ᶠ[𝓝[≠] t] h := by
    filter_upwards [hfactorG.filter_mono nhdsWithin_le_nhds,
      hfactorH.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hsG hsH hst
    exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hst)) (hsG.symm.trans hsH)
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (hh.tendsto.mono_left nhdsWithin_le_nhds) he
lemma analyticOrderAt_mul_nonzero_real {R Y : ℝ → ℝ} {t : ℝ}
    (hR : AnalyticAt ℝ R t) (hY : AnalyticAt ℝ Y t) (hr : R t ≠ 0) :
    analyticOrderAt (fun s => R s * Y s) t = analyticOrderAt Y t := by
  change analyticOrderAt (R * Y) t = _
  rw [analyticOrderAt_mul hR hY, hR.analyticOrderAt_eq_zero.mpr hr, zero_add]
lemma analyticOrderNatAt_mul_nonzero_real {R Y : ℝ → ℝ} {t : ℝ}
    (hR : AnalyticAt ℝ R t) (hY : AnalyticAt ℝ Y t) (hr : R t ≠ 0) :
    analyticOrderNatAt (fun s => R s * Y s) t = analyticOrderNatAt Y t := by
  simp only [analyticOrderNatAt, analyticOrderAt_mul_nonzero_real hR hY hr]
lemma crossingOrientation_power_factor_mul_real {Y R g h : ℝ → ℝ}
    {t x : ℝ} {m : ℕ} (hR : ContinuousAt R t) (hg : ContinuousAt g t)
    (hh : ContinuousAt h t) (hr : R t ≠ 0)
    (hfactorG : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g s)
    (hfactorH : ∀ᶠ s in 𝓝 t, R s * Y s = (s - t) ^ m * h s) :
    crossingOrientation (R t * x) (h t) = crossingOrientation x (g t) := by
  have hfactor : ∀ᶠ s in 𝓝 t,
      R s * Y s = (s - t) ^ m * (R s * g s) := by
    filter_upwards [hfactorG] with s hs
    rw [hs]
    ring
  have he := power_factor_value_unique hh (hR.mul hg) hfactorH hfactor
  rw [he]
  exact crossingOrientation_mul_real hr x (g t)
lemma abs_crossingOrientation_le_one (x a : ℝ) : |crossingOrientation x a| ≤ 1 := by
  unfold crossingOrientation
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
    rcases lt_trichotomy a 0 with ha | ha | ha <;>
    simp [hx, ha, sign_pos, sign_neg]
lemma finite_order_weight_mul_real {X XG Y YG R gY gG : ℝ → ℝ} {t : ℝ}
    (hprod : ∀ s, Y s = R s * YG s) (hX : X t = R t * XG t)
    (hR : AnalyticAt ℝ R t) (hYG : AnalyticAt ℝ YG t) (hr : R t ≠ 0)
    (hfactorY : Y t = 0 → ContinuousAt gY t ∧ gY t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ analyticOrderNatAt Y t * gY s)
    (hfactorG : YG t = 0 → ContinuousAt gG t ∧ gG t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, YG s = (s - t) ^ analyticOrderNatAt YG t * gG s) :
    (if Y t = 0 ∧ Odd (analyticOrderNatAt Y t) then
      crossingOrientation (X t) (gY t) else 0) =
    (if YG t = 0 ∧ Odd (analyticOrderNatAt YG t) then
      crossingOrientation (XG t) (gG t) else 0) := by
  have horder : analyticOrderNatAt Y t = analyticOrderNatAt YG t := by
    rw [show Y = (fun s => R s * YG s) from funext hprod]
    exact analyticOrderNatAt_mul_nonzero_real hR hYG hr
  by_cases hyG : YG t = 0
  · have hy : Y t = 0 := by rw [hprod t, hyG, mul_zero]
    obtain ⟨hgY, _, hfY⟩ := hfactorY hy
    obtain ⟨hgG, _, hfG⟩ := hfactorG hyG
    have hfor : ∀ᶠ s in 𝓝 t,
        R s * YG s = (s - t) ^ analyticOrderNatAt YG t * gY s := by
      filter_upwards [hfY] with s hs
      simpa only [hprod s, horder] using hs
    have hor : crossingOrientation (X t) (gY t) =
        crossingOrientation (XG t) (gG t) := by
      rw [hX]
      exact crossingOrientation_power_factor_mul_real hR.continuousAt hgG hgY hr hfG hfor
    simp only [hy, hyG, horder, true_and, hor]
  · have hy : Y t ≠ 0 := by rw [hprod t]; exact mul_ne_zero hr hyG
    simp only [hy, hyG, false_and, ite_false]
lemma abs_weight_difference_at_real_factor_zero
    {X XG Y YG R : ℝ → ℝ} (aY aG : ℝ) {t : ℝ}
    (hX : X t = R t * XG t) (hr : R t = 0) :
    |(if Y t = 0 ∧ Odd (analyticOrderNatAt Y t) then
        crossingOrientation (X t) aY else 0) -
      (if YG t = 0 ∧ Odd (analyticOrderNatAt YG t) then
        crossingOrientation (XG t) aG else 0)| ≤ 1 := by
  have hx : X t = 0 := by rw [hX, hr, zero_mul]
  simp only [hx, crossingOrientation, sign_zero, SignType.coe_zero, zero_mul,
    ite_self, zero_sub, abs_neg]
  split_ifs
  · exact abs_crossingOrientation_le_one (XG t) aG
  · norm_num
theorem finite_order_crossing_sum_mul_real {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (loc : ι → ℝ) (X XG Y YG R : ℝ → ℝ)
    (gY gG : ι → ℝ → ℝ)
    (hprod : ∀ s, Y s = R s * YG s)
    (hX : ∀ i ∈ S, X (loc i) = R (loc i) * XG (loc i))
    (hR : ∀ i ∈ S, AnalyticAt ℝ R (loc i))
    (hYG : ∀ i ∈ S, AnalyticAt ℝ YG (loc i))
    (hfactorY : ∀ i ∈ S, Y (loc i) = 0 →
      ContinuousAt (gY i) (loc i) ∧ gY i (loc i) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (loc i), Y s =
        (s - loc i) ^ analyticOrderNatAt Y (loc i) * gY i s)
    (hfactorG : ∀ i ∈ S, YG (loc i) = 0 →
      ContinuousAt (gG i) (loc i) ∧ gG i (loc i) ≠ 0 ∧
      ∀ᶠ s in 𝓝 (loc i), YG s =
        (s - loc i) ^ analyticOrderNatAt YG (loc i) * gG i s) :
    |(∑ i ∈ S, if Y (loc i) = 0 ∧ Odd (analyticOrderNatAt Y (loc i)) then
        crossingOrientation (X (loc i)) (gY i (loc i)) else 0) -
      (∑ i ∈ S, if YG (loc i) = 0 ∧ Odd (analyticOrderNatAt YG (loc i)) then
        crossingOrientation (XG (loc i)) (gG i (loc i)) else 0)| ≤
          ((S.filter (fun i => R (loc i) = 0)).card : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ S, if R (loc i) = 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hr : R (loc i) = 0
      · simpa only [if_pos hr] using
          abs_weight_difference_at_real_factor_zero
            (gY i (loc i)) (gG i (loc i)) (hX i hi) hr
      · have he := finite_order_weight_mul_real hprod (hX i hi) (hR i hi) (hYG i hi)
          hr (hfactorY i hi) (hfactorG i hi)
        rw [he, sub_self, abs_zero, if_neg hr]
    _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
end Fluctuations.FiniteOrderCrossingComparison
end
end

section
noncomputable section
open Polynomial Complex Finset Filter Set
open scoped Topology BigOperators
namespace Fluctuations.CommonBoundaryCrossings
open PolynomialCircle UnitCircleBoundaryFactorization FiniteOrderCrossingComparison
  FiniteOrderCrossings SignedCrossings
lemma analyticAt_real_boundary_product (R : Multiset ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s => (R.map (fun z => Real.sin ((s - Complex.arg z) / 2))).prod) t := by
  induction R using Multiset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) t)
  | @cons z R ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : AnalyticAt ℝ (fun s => Real.sin ((s - Complex.arg z) / 2)) t).mul ih
lemma analyticAt_entire_rotated_curve (m : ℕ) (q : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => Complex.exp (-I * (m : ℂ) * w / 2) *
      q.eval (Complex.exp (I * w))) z := by
  have hp : AnalyticAt ℂ (fun w => q.eval w) (Complex.exp (I * z)) :=
    (AnalyticOnNhd.eval_polynomial q) (Complex.exp (I * z)) (mem_univ _)
  exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-I * (m : ℂ) * w / 2)) z).mul
    (hp.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (I * w)) z) rfl)
lemma analyticAt_im_const_mul_rotated (m : ℕ) (q : Polynomial ℂ) (C₀ : ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s => (C₀ * rotatedCircleCurve m q s).im) t := by
  have hcomplex := (analyticAt_const (𝕜 := ℂ) (v := C₀)).mul
    (analyticAt_entire_rotated_curve m q (t : ℂ))
  have hreal := hcomplex.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  have him := (Complex.imCLM.analyticAt
    (C₀ * (Complex.exp (-I * (m : ℂ) * (t : ℂ) / 2) * q.eval (Complex.exp (I * (t : ℂ)))))).comp
      (f := fun s : ℝ => C₀ * (Complex.exp (-I * (m : ℂ) * (s : ℂ) / 2) *
        q.eval (Complex.exp (I * (s : ℂ))))) hreal
  simpa only [Function.comp_def, Complex.imCLM_apply, rotatedCircleCurve,
    phaseFactor_eq_exp, unitCircleCurve_eq_exp] using him
lemma sine_product_zero_imp_boundary_eval_zero (R : Multiset ℂ)
    (hR : ∀ z ∈ R, ‖z‖ = 1) {t : ℝ}
    (ht : (R.map (fun z => Real.sin ((t - Complex.arg z) / 2))).prod = 0) :
    ((R.map (fun z => X - C z)).prod).eval (Complex.exp (I * (t : ℂ))) = 0 := by
  rw [eval_boundary_product]
  have he := rotated_boundary_product R hR t
  rw [ht, Complex.ofReal_zero, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _)
lemma card_sine_product_zero_locations_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (loc : ι → ℝ) (R : Multiset ℂ)
    (hR : ∀ z ∈ R, ‖z‖ = 1) (hinj : Set.InjOn loc (S : Set ι))
    (hmem : ∀ i ∈ S, loc i ∈ Ioo 0 (2 * Real.pi))
    (hzero : ∀ i ∈ S,
      (R.map (fun z => Real.sin ((loc i - Complex.arg z) / 2))).prod = 0) :
    S.card ≤ R.card := by
  classical
  let f : ι → ℂ := fun i => Complex.exp (I * (loc i : ℂ))
  have hf : Set.InjOn f (S : Set ι) := by
    intro i hi j hj he
    apply hinj hi hj
    apply injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) one_ne_zero
      (a := (0 : ℝ)) (b := 2 * Real.pi) (by simp)
      (show loc i ∈ Ico 0 (2 * Real.pi) from ⟨(hmem i hi).1.le, (hmem i hi).2⟩)
      (show loc j ∈ Ico 0 (2 * Real.pi) from ⟨(hmem j hj).1.le, (hmem j hj).2⟩)
    simpa only [f, circleMap, Complex.ofReal_one, one_mul, zero_add, mul_comm I] using he
  have hsub : (S.image f).val ⊆ R := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    rw [← roots_multiset_prod_X_sub_C R]
    apply (mem_roots (monic_multisetProd_X_sub_C R).ne_zero).mpr
    exact sine_product_zero_imp_boundary_eval_zero R hR (hzero i hi)
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hf).symm
    _ ≤ R.card := Multiset.card_le_card (Finset.val_le_iff_val_subset.mpr hsub)
theorem exists_actual_closed_count_crossing_comparison
    (n : ℕ) (p : Polynomial ℂ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ n)
    (hY : (fun t : ℝ => (rotatedCircleCurve n p t).im) ≠ 0) :
    ∃ m : ℕ, ∃ knots : ℕ → ℝ, ∃ g : ℕ → ℝ → ℝ,
      1 ≤ m ∧ knots 0 = 0 ∧ knots m = 2 * Real.pi ∧
      (∀ i < m, knots i < knots (i + 1)) ∧
      (∀ i ≤ m, knots i ∈ Icc 0 (2 * Real.pi)) ∧
      (∀ i < m, ∀ t ∈ Ioo (knots i) (knots (i + 1)),
        (rotatedCircleCurve n p t).im ≠ 0) ∧
      (∀ i ≤ m, (rotatedCircleCurve n p (knots i)).im = 0 →
        AnalyticAt ℝ (g i) (knots i) ∧ g i (knots i) ≠ 0 ∧
        ∀ᶠ s in 𝓝 (knots i), (rotatedCircleCurve n p s).im =
          (s - knots i) ^
            analyticOrderNatAt (fun t => (rotatedCircleCurve n p t).im) (knots i) * g i s) ∧
      |((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
        (1 / 2 : ℝ) * ∑ i ∈ Finset.Ico 1 m,
          (if (rotatedCircleCurve n p (knots i)).im = 0 ∧
              Odd (analyticOrderNatAt (fun t => (rotatedCircleCurve n p t).im) (knots i)) then
            crossingOrientation (rotatedCircleCurve n p (knots i)).re (g i (knots i)) else 0)| ≤
              1 / 2 + ((p.roots.filter (fun z => ‖z‖ = 1)).card : ℝ) := by
  classical
  obtain ⟨q, hq, hpq, _, hboundary, hdeg, hcount⟩ := exists_boundary_root_quotient p hp
  let R := p.roots.filter (fun z => ‖z‖ = 1)
  let C₀ := (R.map (fun z => 2 * I * Complex.exp (I * (Complex.arg z : ℂ) / 2))).prod
  let RF : ℝ → ℝ := fun t => (R.map (fun z => Real.sin ((t - Complex.arg z) / 2))).prod
  let Z : ℝ → ℂ := rotatedCircleCurve n p
  let G : ℝ → ℂ := fun t => C₀ * rotatedCircleCurve (n - R.card) q t
  let DG : ℝ → ℂ := fun t => C₀ * rotatedCircleCurveDerivative (n - R.card) q t
  have hR : ∀ z ∈ R, ‖z‖ = 1 := fun z hz => (Multiset.mem_filter.mp hz).2
  have hB : R.card ≤ n := (quotient_nominal_degree_bound p q n R.card hdegree hdeg).1
  have hC : C₀ ≠ 0 := boundary_phase_constant_ne_zero R
  have hidentity (t : ℝ) : Z t = (RF t : ℂ) * G t :=
    rotated_curve_boundary_factorization p q R n hR hB hpq t
  have hYprod (t : ℝ) : (Z t).im = RF t * (G t).im := by
    rw [hidentity]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hXprod (t : ℝ) : (Z t).re = RF t * (G t).re := by
    rw [hidentity]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hYanalytic (t : ℝ) : AnalyticAt ℝ (fun s => (Z s).im) t := by
    simpa only [one_mul] using analyticAt_im_const_mul_rotated n p 1 t
  have hGanalytic (t : ℝ) : AnalyticAt ℝ (fun s => (G s).im) t :=
    analyticAt_im_const_mul_rotated (n - R.card) q C₀ t
  have hGim : (fun t => (G t).im) ≠ 0 := by
    intro hzero
    apply hY
    funext t
    change (Z t).im = 0
    rw [hYprod, congrFun hzero t]
    simp only [Pi.zero_apply, mul_zero]
  have hG (t : ℝ) : HasDerivAt G (DG t) t :=
    (hasDerivAt_rotatedCircleCurve (n - R.card) q t).const_mul C₀
  have hDG : Continuous DG :=
    continuous_const.mul (continuous_rotatedCircleCurveDerivative (n - R.card) q)
  obtain ⟨m, knots, hm, hstart, hend, hstep, hk, hz⟩ :=
    exists_partition_of_finite_zeros (fun t => (Z t).im) (by positivity)
      (real_analytic_zeros_finite hYanalytic hY 0 (2 * Real.pi))
  have hstrict : StrictMonoOn knots (Set.Iic m) := strictMonoOn_Iic_of_lt_succ hstep
  obtain ⟨gY, hgY⟩ := exists_real_power_factors hYanalytic hY
  obtain ⟨gG, hgG, hbound⟩ := exists_finite_order_crossing_bound
    (fun t => (G t).re) (fun t => (G t).im)
    (fun t => (DG t).re) (fun t => (DG t).im) knots hm hstep
    (fun t => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hG t))
    (fun t => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hG t))
    (Complex.continuous_re.comp hDG) (Complex.continuous_im.comp hDG)
    (by
      intro t _
      by_cases hr : (G t).re = 0
      · right
        intro hi
        exact mul_ne_zero hC (rotatedCircleCurve_ne_zero (n - R.card) q hboundary t)
          (Complex.ext hr hi)
      · exact Or.inl hr)
    (by
      intro i hi t ht he
      exact hz i hi t ht (by rw [hYprod, he, mul_zero]))
    (by simpa only [hstart, hend] using hk)
    (fun i _ _ => hGanalytic (knots i))
    (fun i _ _ => real_analytic_order_finite hGanalytic hGim (knots i))
  have hsum := finite_order_crossing_sum_mul_real (Finset.Ico 1 m) knots
    (fun t => (Z t).re) (fun t => (G t).re) (fun t => (Z t).im) (fun t => (G t).im)
    RF (fun i => gY (knots i)) gG hYprod (fun i _ => hXprod (knots i))
    (fun i _ => analyticAt_real_boundary_product R (knots i))
    (fun i _ => hGanalytic (knots i))
    (fun i _ _ => ⟨(hgY (knots i)).1.continuousAt, (hgY (knots i)).2⟩)
    (fun i hi hy => ⟨(hgG i (by have := Finset.mem_Ico.mp hi; omega) hy).1.continuousAt,
      (hgG i (by have := Finset.mem_Ico.mp hi; omega) hy).2⟩)
  have hcard : ((Finset.Ico 1 m).filter (fun i => RF (knots i) = 0)).card ≤ R.card := by
    apply card_sine_product_zero_locations_le _ knots R hR
    · apply hstrict.injOn.mono
      intro i hi
      exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2.le
    · intro i hi
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi0, him⟩ := Finset.mem_Ico.mp hi
      refine ⟨?_, ?_⟩
      · rw [← hstart]
        exact hstrict (by simp) him.le (by omega)
      · rw [← hend]
        exact hstrict him.le (by simp) him
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hsumB := hsum.trans (show
      (((Finset.Ico 1 m).filter (fun i => RF (knots i) = 0)).card : ℝ) ≤ (R.card : ℝ) by
        exact_mod_cast hcard)
  have hquot := normalized_integral_quotient_curve (n - R.card) q hq hboundary C₀ hC
  have hquot' : (∫ t in 0..2 * Real.pi, (DG t / G t).im) / (2 * Real.pi) =
      ((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - ((n - R.card : ℕ) : ℝ) / 2 := by
    change (2 * Real.pi)⁻¹ * (∫ t in 0..2 * Real.pi, (deriv G t / G t).im) = _ at hquot
    simp_rw [(hG _).deriv] at hquot
    simpa only [div_eq_mul_inv, mul_comm] using hquot
  have hbound' : |((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
      ((n - R.card : ℕ) : ℝ) / 2 - (1 / 2 : ℝ) *
        ∑ i ∈ Finset.Ico 1 m,
          (if (G (knots i)).im = 0 ∧
              Odd (analyticOrderNatAt (fun t => (G t).im) (knots i)) then
            crossingOrientation (G (knots i)).re (gG i (knots i)) else 0)| ≤ 1 / 2 := by
    simpa only [hstart, hend, angularVelocity_eq_im_div, Complex.eta, hquot'] using hbound
  refine ⟨m, knots, (fun i => gY (knots i)), hm, hstart, hend, hstep, hk, hz, ?_, ?_⟩
  · intro i _ _
    exact hgY (knots i)
  · have hshift := discrepancy_boundary_shift n R.card
      (p.roots.filter (fun z => ‖z‖ ≤ 1)).card
      (q.roots.filter (fun z => ‖z‖ ≤ 1)).card hB hcount
    let SY := ∑ i ∈ Finset.Ico 1 m,
      if (Z (knots i)).im = 0 ∧ Odd (analyticOrderNatAt (fun t => (Z t).im) (knots i)) then
        crossingOrientation (Z (knots i)).re (gY (knots i) (knots i)) else 0
    let SG := ∑ i ∈ Finset.Ico 1 m,
      if (G (knots i)).im = 0 ∧ Odd (analyticOrderNatAt (fun t => (G t).im) (knots i)) then
        crossingOrientation (G (knots i)).re (gG i (knots i)) else 0
    change |((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
      (1 / 2 : ℝ) * SY| ≤ 1 / 2 + (R.card : ℝ)
    rw [hshift]
    have he : ((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
        ((n - R.card : ℕ) : ℝ) / 2 + (R.card : ℝ) / 2 - (1 / 2 : ℝ) * SY =
      (((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
        ((n - R.card : ℕ) : ℝ) / 2 - (1 / 2 : ℝ) * SG) +
          (SG - SY) / 2 + (R.card : ℝ) / 2 := by ring
    rw [he]
    have hs : |(SG - SY) / 2| ≤ (R.card : ℝ) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact (abs_sub_comm SG SY).trans_le hsumB
    have hBabs : |(R.card : ℝ) / 2| = (R.card : ℝ) / 2 := abs_of_nonneg (by positivity)
    have ht₁ := abs_add_le
      ((((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
        ((n - R.card : ℕ) : ℝ) / 2 - (1 / 2 : ℝ) * SG) + (SG - SY) / 2)
      ((R.card : ℝ) / 2)
    have ht₂ := abs_add_le
      (((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
        ((n - R.card : ℕ) : ℝ) / 2 - (1 / 2 : ℝ) * SG) ((SG - SY) / 2)
    change |((q.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) -
      ((n - R.card : ℕ) : ℝ) / 2 - (1 / 2 : ℝ) * SG| ≤ 1 / 2 at hbound'
    rw [hBabs] at ht₁
    linarith
end Fluctuations.CommonBoundaryCrossings
end
end

section
open MeasureTheory ProbabilityTheory Polynomial Complex
open scoped BigOperators
namespace Fluctuations.AntiReciprocal
noncomputable section
lemma rotated_coefficientPolynomial_coordinates (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) :
    (PolynomialCircle.rotatedCircleCurve n (coefficientPolynomial n (fun j => (a j : ℂ))) t).re =
      centeredCosineSum n a t ∧
    (PolynomialCircle.rotatedCircleCurve n (coefficientPolynomial n (fun j => (a j : ℂ))) t).im =
      centeredSineSum n a t := by
  simpa only [randomPolynomial_finiteCoefficientSequence, finiteCoefficientSequence_fin] using
    rotated_randomPolynomial_coordinates (finiteCoefficientSequence n) n a t
def antiReciprocalPolynomial (n : ℕ) (a : Fin (n + 1) → ℝ) : Polynomial ℂ :=
  coefficientPolynomial n (fun j => ((a j - a j.rev : ℝ) : ℂ))
lemma antiReciprocalPolynomial_eq_sub_reflect (n : ℕ) (a : Fin (n + 1) → ℝ) :
    antiReciprocalPolynomial n a =
      coefficientPolynomial n (fun j => (a j : ℂ)) -
      (coefficientPolynomial n (fun j => (a j : ℂ))).reflect n := by
  rw [reflect_coefficientPolynomial]
  simp [antiReciprocalPolynomial, coefficientPolynomial, Polynomial.monomial_sub,
    Finset.sum_sub_distrib]
lemma antiReciprocalPolynomial_natDegree_le (n : ℕ) (a : Fin (n + 1) → ℝ) :
    (antiReciprocalPolynomial n a).natDegree ≤ n :=
  coefficientPolynomial_natDegree_le _ _
lemma rotated_antiReciprocalPolynomial (n : ℕ) (a : Fin (n + 1) → ℝ) (t : ℝ) :
    PolynomialCircle.rotatedCircleCurve n (antiReciprocalPolynomial n a) t =
      ((2 * centeredSineSum n a t : ℝ) : ℂ) * I := by
  have h := rotated_coefficientPolynomial_coordinates n (fun j => a j - a j.rev) t
  have hR := centeredCosineSum_reverse n a t
  have hI := centeredSineSum_reverse n a t
  simp only [centeredCosineSum, centeredSineSum, sub_mul, Finset.sum_sub_distrib] at hR hI h
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self]
    change (PolynomialCircle.rotatedCircleCurve n
      (coefficientPolynomial n (fun j => ((a j - a j.rev : ℝ) : ℂ))) t).re = 0
    rw [h.1, hR, sub_self]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, I_re, I_im,
      mul_one, mul_zero, add_zero]
    change (PolynomialCircle.rotatedCircleCurve n
      (coefficientPolynomial n (fun j => ((a j - a j.rev : ℝ) : ℂ))) t).im = _
    rw [h.2, hI]
    simp only [centeredSineSum]
    ring
end
end Fluctuations.AntiReciprocal
end

section
noncomputable section
open Set
open scoped BigOperators Classical
namespace Fluctuations.CenteredTrigReflection
lemma cosine_mode_reflection (n : ℕ) (j : Fin (n+1)) (θ : ℝ) :
    Real.cos (centeredFrequency n j * (2*Real.pi-θ)) =
      (-1 : ℝ)^n * Real.cos (centeredFrequency n j*θ) := by
  have he : centeredFrequency n j * (2*Real.pi-θ) =
      (j.val : ℝ)*(2*Real.pi) - (centeredFrequency n j*θ + n*Real.pi) := by
    unfold centeredFrequency
    ring
  rw [he, Real.cos_nat_mul_two_pi_sub, Real.cos_add_nat_mul_pi]
lemma sine_mode_reflection (n : ℕ) (j : Fin (n+1)) (θ : ℝ) :
    Real.sin (centeredFrequency n j * (2*Real.pi-θ)) =
      -((-1 : ℝ)^n * Real.sin (centeredFrequency n j*θ)) := by
  have he : centeredFrequency n j * (2*Real.pi-θ) =
      (j.val : ℝ)*(2*Real.pi) - (centeredFrequency n j*θ + n*Real.pi) := by
    unfold centeredFrequency
    ring
  rw [he, Real.sin_nat_mul_two_pi_sub, Real.sin_add_nat_mul_pi]
lemma cosine_sum_reflection (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) :
    centeredCosineSum n a (2*Real.pi-θ) = (-1 : ℝ)^n * centeredCosineSum n a θ := by
  simp only [centeredCosineSum, cosine_mode_reflection, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma sine_sum_reflection (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) :
    centeredSineSum n a (2*Real.pi-θ) = -((-1 : ℝ)^n * centeredSineSum n a θ) := by
  simp only [centeredSineSum, sine_mode_reflection, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring
end Fluctuations.CenteredTrigReflection
end
end

section
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace Fluctuations.FiniteOrderReflection
open SignedCrossings FiniteOrderCrossings FiniteOrderCrossingComparison
lemma analyticOrderNatAt_reflection {Y : ℝ → ℝ} {c r t : ℝ}
    (hY : AnalyticAt ℝ Y t) (hr : r ≠ 0)
    (hreflect : ∀ s, Y (c - s) = -r * Y s) :
    analyticOrderNatAt Y (c - t) = analyticOrderNatAt Y t := by
  have hmap : AnalyticAt ℝ (fun s : ℝ => c - s) t := by fun_prop
  have hderiv : deriv (fun s : ℝ => c - s) t ≠ 0 := by
    have hd : HasDerivAt (fun s : ℝ => c - s) (-1) t := by
      convert! ((hasDerivAt_const t c).sub (hasDerivAt_id t)) using 1
      norm_num
    rw [hd.deriv]
    norm_num
  have he := analyticOrderAt_comp_of_deriv_ne_zero (f := Y) hmap hderiv
  have hfun : (Y ∘ fun s => c - s) = (fun s => -r * Y s) := funext hreflect
  rw [hfun] at he
  have he' := analyticOrderAt_mul_nonzero_real
    (R := fun _ : ℝ => -r) analyticAt_const hY (neg_ne_zero.mpr hr)
  rw [he'] at he
  exact congrArg ENat.toNat he.symm
lemma power_factor_value_reflection {Y g₀ g₁ : ℝ → ℝ} {c r t : ℝ} {m : ℕ}
    (hm : Odd m) (hg₀ : ContinuousAt g₀ t) (hg₁ : ContinuousAt g₁ (c - t))
    (hreflect : ∀ s, Y (c - s) = -r * Y s)
    (hfactor₀ : ∀ᶠ s in 𝓝 t, Y s = (s - t) ^ m * g₀ s)
    (hfactor₁ : ∀ᶠ s in 𝓝 (c - t), Y s = (s - (c - t)) ^ m * g₁ s) :
    g₁ (c - t) = r * g₀ t := by
  have hmap : ContinuousAt (fun s : ℝ => c - s) t := by fun_prop
  have hleft : ∀ᶠ s in 𝓝 t,
      Y (c - s) = (s - t) ^ m * (-r * g₀ s) := by
    filter_upwards [hfactor₀] with s hs
    rw [hreflect, hs]
    ring
  have hright : ∀ᶠ s in 𝓝 t,
      Y (c - s) = (s - t) ^ m * ((-1 : ℝ) ^ m * g₁ (c - s)) := by
    filter_upwards [hmap.tendsto.eventually hfactor₁] with s hs
    rw [show c - s - (c - t) = -(s - t) by ring, neg_pow] at hs
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  have he := power_factor_value_unique (continuousAt_const.mul hg₀)
    (continuousAt_const.mul (hg₁.comp hmap)) hleft hright
  rw [hm.neg_one_pow] at he
  change -r * g₀ t = -1 * g₁ (c - t) at he
  nlinarith
lemma finite_order_weight_reflection {X Y : ℝ → ℝ} (g : ℝ → ℝ → ℝ) {c r t : ℝ}
    (hY : AnalyticAt ℝ Y t) (hr : r ≠ 0)
    (hX : X (c - t) = r * X t) (hreflect : ∀ s, Y (c - s) = -r * Y s)
    (hfactor : ∀ u, Y u = 0 → AnalyticAt ℝ (g u) u ∧ g u u ≠ 0 ∧
      ∀ᶠ s in 𝓝 u, Y s = (s - u) ^ analyticOrderNatAt Y u * g u s) :
    (if Y (c - t) = 0 ∧ Odd (analyticOrderNatAt Y (c - t)) then
      crossingOrientation (X (c - t)) (g (c - t) (c - t)) else 0) =
    (if Y t = 0 ∧ Odd (analyticOrderNatAt Y t) then
      crossingOrientation (X t) (g t t) else 0) := by
  have hord := analyticOrderNatAt_reflection hY hr hreflect
  by_cases hy : Y t = 0
  · have hyr : Y (c - t) = 0 := by rw [hreflect, hy, mul_zero]
    by_cases hm : Odd (analyticOrderNatAt Y t)
    · have hf₀ := hfactor t hy
      have hf₁ := hfactor (c - t) hyr
      have he := power_factor_value_reflection hm hf₀.1.continuousAt hf₁.1.continuousAt
        hreflect hf₀.2.2 (by simpa only [hord] using hf₁.2.2)
      simp only [hy, hyr, hord, hm, and_self, ite_true]
      rw [hX, he]
      exact crossingOrientation_mul_real hr (X t) (g t t)
    · simp only [hy, hyr, hord, hm, and_false, ite_false]
  · have hyr : Y (c - t) ≠ 0 := by
      rw [hreflect]
      exact mul_ne_zero (neg_ne_zero.mpr hr) hy
    simp only [hy, hyr, false_and, ite_false]
lemma interior_zero_is_knot (Y : ℝ → ℝ) (knots : ℕ → ℝ) (m : ℕ)
    {a b t : ℝ} (hstart : knots 0 = a) (hend : knots m = b)
    (hz : ∀ i < m, ∀ u ∈ Ioo (knots i) (knots (i + 1)), Y u ≠ 0)
    (ht : t ∈ Ioo a b) (hyt : Y t = 0) :
    ∃ i ∈ Finset.Ico 1 m, knots i = t := by
  classical
  have hex : ∃ k : ℕ, t ≤ knots k ∧ k ≤ m :=
    ⟨m, by rw [hend]; exact ht.2.le, le_rfl⟩
  let k := Nat.find hex
  have hk : t ≤ knots k ∧ k ≤ m := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, hstart] at hk
    linarith [ht.1, hk.1]
  have hprev : knots (k - 1) < t := by
    by_contra h
    have hn := Nat.find_min hex (show k - 1 < Nat.find hex by change k - 1 < k; omega)
    exact hn ⟨le_of_not_gt h, by omega⟩
  have he : knots k = t := by
    by_contra hne
    have hlt : t < knots k := lt_of_le_of_ne hk.1 (Ne.symm hne)
    apply hz (k - 1) (by omega) t ⟨hprev, ?_⟩ hyt
    simpa only [Nat.sub_add_cancel hkpos] using hlt
  have hkm : k < m := by
    by_contra h
    have hke : k = m := by omega
    rw [hke, hend] at he
    linarith [ht.2]
  exact ⟨k, Finset.mem_Ico.mpr ⟨hkpos, hkm⟩, he⟩
lemma exists_partition_zero_finset (Y : ℝ → ℝ) (knots : ℕ → ℝ) (m : ℕ)
    {a b : ℝ} (hstart : knots 0 = a) (hend : knots m = b)
    (hstep : ∀ i < m, knots i < knots (i + 1))
    (hz : ∀ i < m, ∀ u ∈ Ioo (knots i) (knots (i + 1)), Y u ≠ 0) :
    ∃ S : Finset ℝ, (∀ t, t ∈ S ↔ t ∈ Ioo a b ∧ Y t = 0) ∧
      ∀ w : ℝ → ℝ, (∀ t, Y t ≠ 0 → w t = 0) →
        ∑ i ∈ Finset.Ico 1 m, w (knots i) = ∑ t ∈ S, w t := by
  classical
  let J := (Finset.Ico 1 m).filter (fun i => Y (knots i) = 0)
  let S := J.image knots
  have hstrict : StrictMonoOn knots (Set.Iic m) := strictMonoOn_Iic_of_lt_succ hstep
  refine ⟨S, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hi, hy⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi0, him⟩ := Finset.mem_Ico.mp hi
      refine ⟨⟨?_, ?_⟩, hy⟩
      · rw [← hstart]
        exact hstrict (by simp) him.le hi0
      · rw [← hend]
        exact hstrict him.le (by simp) him
    · rintro ⟨ht, hy⟩
      obtain ⟨i, hi, he⟩ := interior_zero_is_knot Y knots m hstart hend hz ht hy
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, he ▸ hy⟩, he⟩
  · intro w hw
    change _ = ∑ t ∈ J.image knots, w t
    rw [Finset.sum_image]
    · exact (Finset.sum_filter_of_ne (fun i _ hwi => by
        by_contra hy
        exact hwi (hw (knots i) hy))).symm
    · intro i hi j hj he
      exact hstrict.injOn (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2.le
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2.le he
lemma finite_reflection_half_sum (S : Finset ℝ) (c : ℝ) (w : ℝ → ℝ)
    (hS : ∀ t, c - t ∈ S ↔ t ∈ S) (hw : ∀ t, w (c - t) = w t)
    (hmid : |w (c / 2)| ≤ 1) :
    |(∑ t ∈ S, w t) / 2 - ∑ t ∈ S.filter (fun t => t < c / 2), w t| ≤ 1 / 2 := by
  classical
  have hpair : ∑ t ∈ S.filter (fun t => c / 2 < t), w t =
      ∑ t ∈ S.filter (fun t => t < c / 2), w t := by
    apply Finset.sum_bij (fun t _ => c - t)
    · intro t ht
      obtain ⟨ht, hlt⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(hS t).mpr ht, by linarith⟩
    · intro t _ u _ he
      linarith
    · intro t ht
      obtain ⟨ht, hlt⟩ := Finset.mem_filter.mp ht
      refine ⟨c - t, Finset.mem_filter.mpr ⟨(hS t).mpr ht, by linarith⟩, ?_⟩
      ring
    · intro t _
      exact (hw t).symm
  have hsplit : ∑ t ∈ S, w t =
      (∑ t ∈ S.filter (fun t => t < c / 2), w t) +
      (∑ t ∈ S.filter (fun t => c / 2 < t), w t) +
        (if c / 2 ∈ S then w (c / 2) else 0) := by
    have hpoint : ∀ t ∈ S, w t =
        (if t < c / 2 then w t else 0) + (if c / 2 < t then w t else 0) +
          (if t = c / 2 then w t else 0) := by
      intro t _
      rcases lt_trichotomy t (c / 2) with ht | ht | ht
      · simp [ht, not_lt_of_gt ht, ht.ne]
      · subst t
        simp
      · simp [ht, not_lt_of_gt ht, ht.ne']
    calc
      _ = ∑ t ∈ S, ((if t < c / 2 then w t else 0) +
          (if c / 2 < t then w t else 0) + (if t = c / 2 then w t else 0)) :=
        Finset.sum_congr rfl hpoint
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_ite_eq']
  rw [hpair] at hsplit
  have he : (∑ t ∈ S, w t) / 2 - ∑ t ∈ S.filter (fun t => t < c / 2), w t =
      (if c / 2 ∈ S then w (c / 2) else 0) / 2 := by rw [hsplit]; ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  split_ifs <;> simp_all
end Fluctuations.FiniteOrderReflection
end
end

section
noncomputable section
open Polynomial Finset Filter
open scoped BigOperators Topology
namespace Fluctuations.PolynomialMultiplicity
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
lemma analyticOrderAt_eval (p : Polynomial 𝕜) (hp : p ≠ 0) (z : 𝕜) :
    analyticOrderAt (fun w => p.eval w) z = (p.rootMultiplicity z : ℕ∞) := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp z
  have hpa : AnalyticAt 𝕜 (fun w => p.eval w) z :=
    (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)
  apply hpa.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun w => q.eval w,
    (AnalyticOnNhd.eval_polynomial q) z (Set.mem_univ z), ?_, ?_⟩
  · exact fun hz => hq (Polynomial.dvd_iff_isRoot.mpr hz)
  · apply Eventually.of_forall
    intro w
    calc
      p.eval w = ((X - C z) ^ p.rootMultiplicity z * q).eval w :=
        congrArg (fun r : Polynomial 𝕜 => r.eval w) hpq
      _ = (w-z) ^ p.rootMultiplicity z • q.eval w := by
        simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
lemma sum_rootMultiplicity_le (p : Polynomial 𝕜) (S : Finset 𝕜) :
    ∑ z ∈ S, p.rootMultiplicity z ≤ p.natDegree := by
  classical
  calc
    ∑ z ∈ S, p.rootMultiplicity z = ∑ z ∈ S ∩ p.roots.toFinset, p.roots.count z := by
      rw [sum_subset (inter_subset_left : S ∩ p.roots.toFinset ⊆ S)]
      · simp only [Polynomial.count_roots]
      · intro z hz hz'
        have hn : z ∉ p.roots := by simpa [hz] using hz'
        exact Multiset.count_eq_zero.mpr hn
    _ ≤ ∑ z ∈ p.roots.toFinset, p.roots.count z :=
      sum_le_sum_of_subset (inter_subset_right)
    _ = p.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := Polynomial.card_roots' p
end Fluctuations.PolynomialMultiplicity
end
end

section
noncomputable section
open Polynomial Finset Filter Complex
open scoped BigOperators Topology
namespace Fluctuations.SignSineTotalMultiplicity
open AntiReciprocal GaussianComplex
private lemma entire_eq_of_eq_on_real {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (hfg : ∀ t : ℝ, f t = g t) : f = g := by
  have ht : Tendsto Complex.ofReal (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  apply AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hf z) (fun z _ => hg z)
  exact ht.frequently (Eventually.of_forall hfg).frequently
lemma rotated_antiReciprocalPolynomial_scaled_real (n : ℕ) (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (t : ℝ) :
    Complex.exp (-I*(t : ℂ)/2) *
      (antiReciprocalPolynomial n a).eval (Complex.exp (I*(t : ℂ)/n)) =
      (2*(Real.sqrt n : ℂ)*I) * scaledSineField n a t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have he := rotated_antiReciprocalPolynomial n a (t/n)
  rw [PolynomialCircle.rotatedCircleCurve, PolynomialCircle.phaseFactor_eq_exp,
    PolynomialCircle.unitCircleCurve_eq_exp] at he
  simp only [Complex.ofReal_div, Complex.ofReal_natCast] at he
  have hp : -I*(n : ℂ)*((t : ℂ)/n)/2 = -I*(t : ℂ)/2 := by field_simp
  rw [hp] at he
  rw [show I*((t : ℂ)/n) = I*(t : ℂ)/n by ring] at he
  rw [he, scaledSineField_ofReal]
  push_cast
  field_simp
lemma rotated_antiReciprocalPolynomial_scaled (n : ℕ) (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (z : ℂ) :
    Complex.exp (-I*z/2) *
      (antiReciprocalPolynomial n a).eval (Complex.exp (I*z/n)) =
      (2*(Real.sqrt n : ℂ)*I) * scaledSineField n a z := by
  have hpoly : AnalyticOnNhd ℂ (fun w => (antiReciprocalPolynomial n a).eval w) Set.univ :=
    AnalyticOnNhd.eval_polynomial _
  have hfield : ∀ w, AnalyticAt ℂ (scaledSineField n a) w :=
    (differentiable_scaledSineField n a).analyticAt
  have he := entire_eq_of_eq_on_real
    (f := fun w => Complex.exp (-I*w/2) *
      (antiReciprocalPolynomial n a).eval (Complex.exp (I*w/n)))
    (g := fun w => (2*(Real.sqrt n : ℂ)*I) * scaledSineField n a w)
    (fun w => (by
      have hp := hpoly (Complex.exp (I*w/n)) (Set.mem_univ _)
      exact (by fun_prop : AnalyticAt ℂ (fun w => Complex.exp (-I*w/2)) w).mul
        (hp.comp_of_eq (by fun_prop :
          AnalyticAt ℂ (fun v : ℂ => Complex.exp (I*v/n)) w) rfl)))
    (fun w => (analyticAt_const).mul (hfield w))
    (rotated_antiReciprocalPolynomial_scaled_real n hn a)
  exact congrFun he z
lemma antiReciprocalPolynomial_ne_zero (n : ℕ) (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (hf : scaledSineField n a ≠ 0) :
    antiReciprocalPolynomial n a ≠ 0 := by
  intro hp
  apply hf
  funext z
  have he := rotated_antiReciprocalPolynomial_scaled n hn a z
  rw [hp, eval_zero, mul_zero] at he
  have hs : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  exact (mul_eq_zero.mp he.symm).resolve_left (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) I_ne_zero)
lemma analyticOrderAt_scaledSineField (n : ℕ) (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (hf : scaledSineField n a ≠ 0) (z : ℂ) :
    analyticOrderAt (scaledSineField n a) z =
      ((antiReciprocalPolynomial n a).rootMultiplicity (Complex.exp (I*z/n)) : ℕ∞) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hphase : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-I*w/2)) z := by fun_prop
  have hexp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (I*w/n)) z := by fun_prop
  have hpoly : AnalyticAt ℂ (fun w => (antiReciprocalPolynomial n a).eval w)
      (Complex.exp (I*z/n)) := (AnalyticOnNhd.eval_polynomial _) _ (Set.mem_univ _)
  have hcomp := hpoly.comp_of_eq hexp rfl
  have hfield := (differentiable_scaledSineField n a).analyticAt z
  have hd : deriv (fun w : ℂ => Complex.exp (I*w/n)) z ≠ 0 := by
    have hd' : HasDerivAt (fun w : ℂ => Complex.exp (I*w/n))
        (Complex.exp (I*z/n)*(I/n)) z := by
      simpa using ((hasDerivAt_id z).const_mul I |>.div_const (n : ℂ) |>.cexp)
    rw [hd'.deriv]
    exact mul_ne_zero (Complex.exp_ne_zero _) (div_ne_zero I_ne_zero hn0)
  have he := congrArg (fun f : ℂ → ℂ => analyticOrderAt f z)
    (funext (rotated_antiReciprocalPolynomial_scaled n hn a))
  change analyticOrderAt ((fun w => Complex.exp (-I*w/2)) *
      ((fun w => (antiReciprocalPolynomial n a).eval w) ∘
        (fun w => Complex.exp (I*w/n)))) z =
    analyticOrderAt ((fun _ => 2*(Real.sqrt n : ℂ)*I) * scaledSineField n a) z at he
  rw [analyticOrderAt_mul hphase hcomp,
    analyticOrderAt_mul analyticAt_const hfield,
    hphase.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _),
    analyticAt_const.analyticOrderAt_eq_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) hs) I_ne_zero),
    zero_add, zero_add, analyticOrderAt_comp_of_deriv_ne_zero hexp hd,
    PolynomialMultiplicity.analyticOrderAt_eval _
      (antiReciprocalPolynomial_ne_zero n hn a hf)] at he
  exact he.symm
lemma analyticOrderNatAt_scaledSineField (n : ℕ) (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (hf : scaledSineField n a ≠ 0) (z : ℂ) :
    analyticOrderNatAt (scaledSineField n a) z =
      (antiReciprocalPolynomial n a).rootMultiplicity (Complex.exp (I*z/n)) := by
  simp [analyticOrderNatAt, analyticOrderAt_scaledSineField n hn a hf z]
lemma scaled_circle_injOn (n : ℕ) (hn : 0 < n) :
    Set.InjOn (fun t : ℝ => Complex.exp (I*(t : ℂ)/n)) (Set.Icc 0 (Real.pi*n)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmap (t : ℝ) : Complex.exp (I*(t : ℂ)/n) = circleMap 0 1 (t/n) := by
    simp only [circleMap, Complex.ofReal_one, one_mul, zero_add,
      Complex.ofReal_div, Complex.ofReal_natCast]
    congr 1
    ring
  have hrange (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi*n)) : t/n ∈ Set.Ico 0 (2*Real.pi) := by
    refine ⟨div_nonneg ht.1 hn0.le, ?_⟩
    have hpi : t/n ≤ Real.pi := (div_le_iff₀ hn0).mpr ht.2
    linarith [Real.pi_pos]
  intro s hs t ht he
  have hd := injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) one_ne_zero
    (a := (0 : ℝ)) (b := 2*Real.pi) (by simp) (hrange s hs) (hrange t ht)
    (by simpa only [← hmap] using he)
  exact (div_left_inj' hn0.ne').mp hd
lemma sum_real_orders_le_degree (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (hf : scaledSineField n a ≠ 0) (S : Finset ℝ)
    (hS : ∀ t ∈ S, t ∈ Set.Icc 0 (Real.pi*n)) :
    ∑ t ∈ S, analyticOrderNatAt (scaledSineField n a) (t : ℂ) ≤ n := by
  classical
  let g : ℝ → ℂ := fun t => Complex.exp (I*(t : ℂ)/n)
  have hi : Set.InjOn g (S : Set ℝ) := (scaled_circle_injOn n hn).mono (by
    intro t ht
    exact hS t ht)
  calc
    _ = ∑ z ∈ S.image g, (antiReciprocalPolynomial n a).rootMultiplicity z := by
      rw [sum_image hi]
      exact sum_congr rfl (fun t _ => analyticOrderNatAt_scaledSineField n hn a hf t)
    _ ≤ (antiReciprocalPolynomial n a).natDegree :=
      PolynomialMultiplicity.sum_rootMultiplicity_le _ _
    _ ≤ n := antiReciprocalPolynomial_natDegree_le n a
lemma realIntervalMultiplicity_eq_sum {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (a b : ℝ) (S : Finset ℝ)
    (hS : ∀ t, t ∈ S ↔ t ∈ Set.Icc a b ∧ f (t : ℂ) = 0) :
    SignSineOccupancy.realIntervalMultiplicity f a b =
      ∑ t ∈ S, (analyticOrderNatAt f (t : ℂ) : ℤ) := by
  classical
  let U : Set ℂ := Complex.ofReal '' Set.Icc a b
  have ha : AnalyticOnNhd ℂ f U := fun z _ => hf z
  have hsupport : Function.support (MeromorphicOn.divisor f U) ⊆
      ((S.image Complex.ofReal : Finset ℂ) : Set ℂ) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := (MeromorphicOn.divisor f U).supportWithinDomain hz
    have hzero : f (t : ℂ) = 0 := by
      by_contra hne
      have ho := (hf (t : ℂ)).analyticOrderAt_eq_zero.mpr hne
      have hd : MeromorphicOn.divisor f U (t : ℂ) = 0 := by
        rw [SignSineOccupancy.divisor_eq_analyticOrderNatAt ha ⟨t, ht, rfl⟩]
        simp [analyticOrderNatAt, ho]
      exact hz hd
    exact mem_image.mpr ⟨t, (hS t).mpr ⟨ht, hzero⟩, rfl⟩
  change (∑ᶠ z, MeromorphicOn.divisor f U z) = _
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport,
    sum_image (fun _ _ _ _ h => Complex.ofReal_injective h)]
  apply sum_congr rfl
  intro t ht
  exact SignSineOccupancy.divisor_eq_analyticOrderNatAt ha ⟨t, ((hS t).mp ht).1, rfl⟩
end Fluctuations.SignSineTotalMultiplicity
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace Fluctuations.MultiplicityEnumeration
theorem exists_order_enumeration (S : Finset ℝ) (order : ℝ → ℕ) (b : ℝ → ℝ)
    (hpos : ∀ t ∈ S, 0 < order t) (hb : ∀ t ∈ S, |b t| ≤ 1) :
    ∃ N : ℕ, ∃ loc : Fin N → ℝ, ∃ orientation : Fin N → ℝ,
      N = ∑ t ∈ S, order t ∧
      (∀ i, loc i ∈ S) ∧ (∀ i, |orientation i| ≤ 1) ∧
      (∀ i, orientation i = 0 ∨ orientation i = b (loc i)) ∧
      (∀ F : ℝ → ℝ, ∑ i, F (loc i) = ∑ t ∈ S, (order t : ℝ) * F t) ∧
      (∀ F : ℝ → ℝ, ∑ i, orientation i * F (loc i) = ∑ t ∈ S, b t * F t) := by
  classical
  let I := Σ t : {t // t ∈ S}, Fin (order t.val)
  let N := Fintype.card I
  let e : Fin N ≃ I := (Fintype.equivFin I).symm
  let loc : Fin N → ℝ := fun i => (e i).1.val
  let orientation : Fin N → ℝ := fun i =>
    if (e i).2.val = 0 then b (loc i) else 0
  refine ⟨N, loc, orientation, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [N, I]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort S order
  · intro i
    exact (e i).1.property
  · intro i
    dsimp only [orientation]
    split_ifs
    · exact hb _ (e i).1.property
    · norm_num
  · intro i
    dsimp only [orientation]
    split_ifs <;> simp
  · intro F
    change (∑ i : Fin N, (fun q : I => F q.1.val) (e i)) = _
    rw [Equiv.sum_comp e (fun q : I => F q.1.val), Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact Finset.sum_coe_sort S (fun t => (order t : ℝ) * F t)
  · intro F
    change (∑ i : Fin N, (fun q : I =>
      (if q.2.val = 0 then b q.1.val else 0) * F q.1.val) (e i)) = _
    rw [Equiv.sum_comp e (fun q : I =>
      (if q.2.val = 0 then b q.1.val else 0) * F q.1.val), Fintype.sum_sigma]
    have hfirst (t : {t // t ∈ S}) :
        ∑ k : Fin (order t.val), (if k.val = 0 then b t.val else 0) * F t.val =
          b t.val * F t.val := by
      let first : Fin (order t.val) := ⟨0, hpos t.val t.property⟩
      apply Finset.sum_eq_single first
      · intro k _ hk
        have hk0 : k.val ≠ 0 := by
          intro he
          exact hk (Fin.ext he)
        simp [hk0]
      · simp
    simp_rw [hfirst]
    exact Finset.sum_coe_sort S (fun t => b t * F t)
end Fluctuations.MultiplicityEnumeration
end
end

section
open Set MeasureTheory
open scoped BigOperators
namespace Fluctuations.IntegerCells
noncomputable section
abbrev CellIndex (T : ℝ) := Fin (⌊T - 1⌋₊ + 1)
def cellStart {T : ℝ} (j : CellIndex T) : ℝ := j.val
def assignedCell {T : ℝ} (t : ℝ) (ht : t ≤ T - 1) : CellIndex T :=
  ⟨⌊t⌋₊, Nat.lt_succ_of_le (Nat.floor_mono ht)⟩
lemma cellStart_nonneg {T : ℝ} (j : CellIndex T) : 0 ≤ cellStart j :=
  Nat.cast_nonneg _
lemma cellStart_add_one_le {T : ℝ} (hT : 1 ≤ T) (j : CellIndex T) :
    cellStart j + 1 ≤ T := by
  have hj : j.val ≤ ⌊T - 1⌋₊ := Nat.le_of_lt_succ j.isLt
  have h := (Nat.cast_le.mpr hj : (j.val : ℝ) ≤ (⌊T - 1⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ T - 1))
  dsimp [cellStart]
  linarith
lemma mem_assigned_cell {T : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T - 1) :
    t ∈ Icc (cellStart (assignedCell t ht)) (cellStart (assignedCell t ht) + 1) :=
  ⟨Nat.floor_le ht0, (Nat.lt_floor_add_one t).le⟩
lemma overlap_at_most_one (T x : ℝ) :
    (Finset.univ.filter (fun j : CellIndex T => x ∈ Ioc (cellStart j) (cellStart j + 1))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · have hh : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    have hh' : x ≤ (i.val : ℝ) + 1 := hi'.2
    have hj'' : (j.val : ℝ) < x := hj'.1
    linarith
  · exact hij
  · have hh : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hij
    have hh' : x ≤ (j.val : ℝ) + 1 := hj'.2
    have hi'' : (i.val : ℝ) < x := hi'.1
    linarith
end
end Fluctuations.IntegerCells
end

section
noncomputable section
open Finset Classical Set
open scoped BigOperators
namespace Fluctuations.SignRetainedZeroSampling
open GaussianComplex SignSineOccupancy SignSineTotalMultiplicity
open SignActivityFiber SignConditionalRows
lemma scaled_sine_order_pos {n : ℕ} (hn : 0 < n) (a : Fin (n + 1) → ℝ)
    (hf : scaledSineField n a ≠ 0) (t : ℝ) (ht : scaledSineField n a (Complex.ofReal t) = 0) :
    0 < analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) := by
  have hfinite : analyticOrderAt (scaledSineField n a) (Complex.ofReal t) ≠ ⊤ := by
    rw [analyticOrderAt_scaledSineField n hn a hf]
    simp
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  by_contra h
  have hz : analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
  have ho : analyticOrderAt (scaledSineField n a) (Complex.ofReal t) = 0 := by
    rw [← hcast,hz]
    rfl
  exact ((differentiable_scaledSineField n a).analyticAt (z := Complex.ofReal t)).analyticOrderAt_eq_zero.mp ho ht
lemma sum_scaled_sine_orders_le_interval (n : ℕ) (a : Fin (n + 1) → ℝ)
    (hf : scaledSineField n a ≠ 0) (l r : ℝ) (T : Finset ℝ)
    (hT : ∀ t ∈ T, t ∈ Icc l r ∧ scaledSineField n a (Complex.ofReal t) = 0) :
    (∑ t ∈ T, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ)) ≤
      (realIntervalMultiplicity (scaledSineField n a) l r : ℝ) := by
  have han : ∀ z, AnalyticAt ℂ (scaledSineField n a) z :=
    (differentiable_scaledSineField n a).analyticAt
  have hfin := real_interval_zeros_finite han hf l r
  let U := hfin.toFinset
  have hU (t : ℝ) : t ∈ U ↔ t ∈ Icc l r ∧ scaledSineField n a (Complex.ofReal t) = 0 :=
    hfin.mem_toFinset
  have hsub : T ⊆ U := fun t ht => (hU t).mpr (hT t ht)
  have he := realIntervalMultiplicity_eq_sum han l r U hU
  have heR : (realIntervalMultiplicity (scaledSineField n a) l r : ℝ) =
      ∑ t ∈ U, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) := by
    rw [he]
    push_cast
    rfl
  rw [heR]
  exact_mod_cast (sum_le_sum_of_subset hsub :
    (∑ t ∈ T, analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t)) ≤
      ∑ t ∈ U, analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t))
lemma repeated_retained_cell_card_le {n N : ℕ}
    (a : Fin (n + 1) → ℝ) (hg : ¬occupancyBad n a) (T : Finset ℝ)
    (hT : ∀ t ∈ T, t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) ∧
      scaledSineField n a (Complex.ofReal t) = 0)
    (loc : Fin N → ℝ) (hloc : ∀ i, loc i ∈ T)
    (hsum : ∀ F : ℝ → ℝ, (∑ i, F (loc i)) =
      ∑ t ∈ T, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) * F t)
    (j : IntegerCells.CellIndex (2 * Real.pi * n))
    (hinterior : ∀ i, loc i ≤ 2 * Real.pi * n - 1) :
    (univ.filter (fun i => IntegerCells.assignedCell (loc i) (hinterior i) = j)).card ≤
      Nat.ceil (localThreshold n) := by
  obtain ⟨hf,hcells,_⟩ := not_occupancyBad_spec n a hg
  let A := univ.filter (fun i => IntegerCells.assignedCell (loc i) (hinterior i) = j)
  by_cases hA : A.Nonempty
  · obtain ⟨i,hi⟩ := hA
    have he : Nat.floor (loc i) = j.val := by
      exact congrArg Fin.val (mem_filter.mp hi).2
    have hj : j.val ∈ bulkCells n := by
      rw [← he]
      have ht := (hT (loc i) (hloc i)).1
      exact floor_mem_bulkCells n (loc i) ⟨ht.1.le,ht.2.le⟩
    have hcards : (A.card : ℝ) = ∑ i : Fin N, if Nat.floor (loc i) = j.val then (1 : ℝ) else 0 := by
      have hpred (i : Fin N) : IntegerCells.assignedCell (loc i) (hinterior i) = j ↔
          Nat.floor (loc i) = j.val := by
        exact Fin.ext_iff
      have hfilters : A = univ.filter (fun i => Nat.floor (loc i) = j.val) := by
        ext i
        simp only [A,mem_filter,hpred]
      rw [hfilters]
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [hsum (fun t => if Nat.floor t = j.val then (1 : ℝ) else 0)] at hcards
    have hsumcell : (A.card : ℝ) =
        ∑ t ∈ T.filter (fun t => Nat.floor t = j.val),
          (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) := by
      rw [hcards,Finset.sum_filter]
      apply sum_congr rfl
      intro t _
      split_ifs <;> simp only [mul_one,mul_zero]
    have hinc (t : ℝ) (ht : t ∈ T.filter (fun t => Nat.floor t = j.val)) :
        t ∈ Icc (j.val : ℝ) (j.val+1) ∧ scaledSineField n a (Complex.ofReal t) = 0 := by
      obtain ⟨htT,htfloor⟩ := mem_filter.mp ht
      have hbulk := (hT t htT).1
      have hpos : 0 ≤ t := by
        have hcut : 0 < endpointCutoff := by dsimp [endpointCutoff]; positivity
        linarith [hbulk.1]
      have hlo := Nat.floor_le hpos
      have hhi := Nat.lt_floor_add_one t
      rw [htfloor] at hlo hhi
      exact ⟨⟨hlo,hhi.le⟩,(hT t htT).2⟩
    have hbound := sum_scaled_sine_orders_le_interval n a hf j.val (j.val+1)
      (T.filter (fun t => Nat.floor t = j.val)) hinc
    rw [← hsumcell] at hbound
    have hc := (hbound.trans (hcells j.val hj)).trans (Nat.le_ceil (localThreshold n))
    exact_mod_cast hc
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _
lemma exists_actual_retained_row_family (n : ℕ) (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ SignPolynomialDivisibility.signVectors (n + 1))
    (hg : ¬occupancyBad n a) (hm : ¬maskBad n a) (β : ℝ → ℝ) (hβ : ∀ t, |β t| ≤ 1) :
    ∃ S : Finset ℝ, ∃ N : ℕ, ∃ loc b : Fin N → ℝ,
      (∀ t, t ∈ S ↔ t ∈ Icc 0 (Real.pi*n) ∧ scaledSineField n a (Complex.ofReal t) = 0) ∧
      N = ∑ t ∈ S.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)),
        analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) ∧
      N ≤ n ∧
      (∀ i, loc i ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) ∧
        scaledSineField n a (Complex.ofReal (loc i)) = 0) ∧
      (∀ i, |b i| ≤ 1) ∧
      (∀ F : ℝ → ℝ, (∑ i, F (loc i)) =
        ∑ t ∈ S.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)),
          (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) * F t) ∧
      (∀ F : ℝ → ℝ, (∑ i, b i * F (loc i)) =
        ∑ t ∈ S.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)), β t * F t) ∧
      ∀ u : {j // j ∈ freeIndices n a} → ℝ,
        (∑ i, (∑ j, GaussianSampling.normalizedRow
          (fun i => conditionalCosineRow n a (loc i)) i j * u j) ^ 2) ≤
            (80 * Real.pi * Nat.ceil (localThreshold n)) * ∑ j, u j ^ 2 := by
  have hf := (not_occupancyBad_spec n a hg).1
  have han : ∀ z, AnalyticAt ℂ (scaledSineField n a) z :=
    (differentiable_scaledSineField n a).analyticAt
  have hfin := real_interval_zeros_finite han hf 0 (Real.pi*n)
  let S := hfin.toFinset
  have hS (t : ℝ) : t ∈ S ↔ t ∈ Icc 0 (Real.pi*n) ∧ scaledSineField n a (Complex.ofReal t) = 0 :=
    hfin.mem_toFinset
  let T := S.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff))
  have hT (t : ℝ) (ht : t ∈ T) : t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) ∧
      scaledSineField n a (Complex.ofReal t) = 0 :=
    ⟨(mem_filter.mp ht).2,((hS t).mp (mem_filter.mp ht).1).2⟩
  obtain ⟨N,loc,b,hN,hloc,hb,_,hsum,hbsum⟩ := MultiplicityEnumeration.exists_order_enumeration T
    (fun t => analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t)) β
    (fun t ht => scaled_sine_order_pos hn a hf t (hT t ht).2) (fun t _ => hβ t)
  have hNle : N ≤ n := by
    rw [hN]
    exact sum_real_orders_le_degree n hn a hf T (fun t ht => ((hS t).mp (mem_filter.mp ht).1).1)
  have hbulk (i : Fin N) : loc i ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) :=
    (hT (loc i) (hloc i)).1
  have hloc0 (i : Fin N) : 0 ≤ loc i := by
    have hcut : 0 < endpointCutoff := by dsimp [endpointCutoff]; positivity
    linarith [(hbulk i).1]
  have hinterior (i : Fin N) : loc i ≤ 2 * Real.pi * n - 1 := by
    have hcut : 1 ≤ endpointCutoff := by dsimp [endpointCutoff]; linarith [Real.pi_pos]
    have hpn : 0 ≤ Real.pi*(n : ℝ) := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    linarith [(hbulk i).2]
  let cell : Fin N → IntegerCells.CellIndex (2 * Real.pi * n) := fun i =>
    IntegerCells.assignedCell (loc i) (hinterior i)
  have hH : ∀ j, (univ.filter (fun i => cell i = j)).card ≤ Nat.ceil (localThreshold n) :=
    fun j => repeated_retained_cell_card_le a hg T hT loc hloc hsum j hinterior
  have hpn1 : 1 ≤ 2 * Real.pi * n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.two_le_pi]
  refine ⟨S,N,loc,b,hS,hN,hNle,(fun i => hT (loc i) (hloc i)),hb,hsum,hbsum,?_⟩
  intro u
  have he := conditionalCosineRow_normalized_sampling_bound hn a ha loc cell IntegerCells.cellStart
    (Nat.ceil (localThreshold n)) 1 IntegerCells.cellStart_nonneg
    (IntegerCells.cellStart_add_one_le hpn1)
    (fun i => IntegerCells.mem_assigned_cell (hloc0 i) (hinterior i)) hH
    (fun x _ => IntegerCells.overlap_at_most_one _ x)
    (fun i => not_maskBad_spec n a hm (loc i) ⟨(hbulk i).1.le,(hbulk i).2.le⟩) u
  simpa only [Nat.cast_one,mul_one] using he
end Fluctuations.SignRetainedZeroSampling
end
end

section
noncomputable section
open Polynomial Complex Classical
open scoped BigOperators
namespace Fluctuations.SignBoundaryMultiplicityCharging
open AntiReciprocal SignPolynomialDivisibility SignNoncyclotomicAssembly
lemma unit_rootMultiplicity_le_antiReciprocal (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (hanti : antiReciprocalPolynomial n a ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (coefficientPolynomial n (fun j => (a j : ℂ))).rootMultiplicity z ≤
      (antiReciprocalPolynomial n a).rootMultiplicity z := by
  let p : ℂ[X] := coefficientPolynomial n (fun j => (a j : ℂ))
  let q : ℝ[X] := coefficientPolynomial n a
  have hmap : q.map (algebraMap ℝ ℂ) = p := by
    rw [map_coefficientPolynomial]
    rfl
  have hlast : (a (Fin.last n) : ℂ) ≠ 0 := by
    rcases (mem_signVectors a).mp ha (Fin.last n) with h | h <;> rw [h] <;> norm_num
  have hreflect : p.reflect n = p.reverse := by
    rw [reflect_coefficientPolynomial, reverse_coefficientPolynomial n _ hlast]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hm : p.reverse.rootMultiplicity z = p.rootMultiplicity z := by
    rw [rootMultiplicity_reverse _ _ hz0, Complex.inv_eq_conj hz, ← hmap,
      real_rootMultiplicity_conj]
  change p.rootMultiplicity z ≤ _
  rw [le_rootMultiplicity_iff hanti, antiReciprocalPolynomial_eq_sub_reflect]
  apply dvd_sub (pow_rootMultiplicity_dvd _ _)
  rw [hreflect, ← hm]
  exact pow_rootMultiplicity_dvd _ _
lemma boundary_roots_le_antiReciprocal_common (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (hanti : antiReciprocalPolynomial n a ≠ 0) :
    (coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter (fun z => ‖z‖ = 1) ≤
      (antiReciprocalPolynomial n a).roots.filter
        (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧ ‖z‖ = 1) := by
  apply Multiset.le_iff_count.mpr
  intro z
  simp only [Multiset.count_filter]
  by_cases hz : ‖z‖ = 1
  · by_cases hp : (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0
    · simp only [hz,hp,true_and,ite_true,Polynomial.count_roots]
      exact unit_rootMultiplicity_le_antiReciprocal n a ha hanti z hz
    · simp only [hz,hp,false_and,ite_true,ite_false,Polynomial.count_roots,
        rootMultiplicity_eq_zero hp,le_refl]
  · simp only [hz,and_false,ite_false,le_refl]
lemma real_unit_roots_conj (p : ℝ[X]) :
    ((p.map (algebraMap ℝ ℂ)).roots.filter (fun z => ‖z‖ = 1)).map (starRingEnd ℂ) =
      (p.map (algebraMap ℝ ℂ)).roots.filter (fun z => ‖z‖ = 1) := by
  apply Multiset.ext.mpr
  intro z
  have he := Multiset.count_map_eq_count' (starRingEnd ℂ)
    ((p.map (algebraMap ℝ ℂ)).roots.filter (fun z => ‖z‖ = 1)) star_injective (starRingEnd ℂ z)
  have hzz : starRingEnd ℂ (starRingEnd ℂ z) = z := star_star z
  rw [hzz] at he
  rw [he]
  simp only [Multiset.count_filter,Complex.norm_conj,Polynomial.count_roots,
    real_rootMultiplicity_conj]
lemma conjugation_stable_card_le_two_upper (R : Multiset ℂ)
    (hR : R.map (starRingEnd ℂ) = R) :
    R.card ≤ 2 * (R.filter (fun z => 0 ≤ z.im)).card := by
  have he : (R.map (starRingEnd ℂ)).filter (fun z => ¬0 ≤ z.im) =
      (R.filter (fun z => 0 < z.im)).map (starRingEnd ℂ) := by
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro z _
    simp only [Function.comp_apply,Complex.conj_im]
    constructor <;> intro h <;> linarith
  rw [hR] at he
  have hc := congrArg Multiset.card he
  rw [Multiset.card_map] at hc
  have hsplit := congrArg Multiset.card (Multiset.filter_add_not (fun z : ℂ => 0 ≤ z.im) R)
  rw [Multiset.card_add] at hsplit
  have hle := Multiset.card_le_card (Multiset.monotone_filter_right R
    (fun z (hz : 0 < z.im) => hz.le))
  omega
lemma boundary_card_le_two_upper_common (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : a ∈ signVectors (n + 1)) (hanti : antiReciprocalPolynomial n a ≠ 0) :
    ((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card ≤
    2 * ((antiReciprocalPolynomial n a).roots.filter
      (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧
        ‖z‖ = 1 ∧ 0 ≤ z.im)).card := by
  let q : ℝ[X] := coefficientPolynomial n a
  have hmap : q.map (algebraMap ℝ ℂ) = coefficientPolynomial n (fun j => (a j : ℂ)) := by
    rw [map_coefficientPolynomial]
    rfl
  have hconj := real_unit_roots_conj q
  rw [hmap] at hconj
  have hhalf := conjugation_stable_card_le_two_upper _ hconj
  have hle := Multiset.card_le_card (Multiset.filter_le_filter (fun z : ℂ => 0 ≤ z.im)
    (boundary_roots_le_antiReciprocal_common n a ha hanti))
  have he : ((antiReciprocalPolynomial n a).roots.filter
      (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧ ‖z‖ = 1)).filter
        (fun z => 0 ≤ z.im) =
      (antiReciprocalPolynomial n a).roots.filter
        (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧
          ‖z‖ = 1 ∧ 0 ≤ z.im) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z _
    tauto
  rw [he] at hle
  exact hhalf.trans (Nat.mul_le_mul_left 2 hle)
lemma upper_common_card_le_real_orders (n : ℕ) (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (hf : GaussianComplex.scaledSineField n a ≠ 0)
    (S : Finset ℝ) (hS : ∀ t, t ∈ S ↔ t ∈ Set.Icc 0 (Real.pi*n) ∧
      GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0) :
    ((antiReciprocalPolynomial n a).roots.filter
      (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧
        ‖z‖ = 1 ∧ 0 ≤ z.im)).card ≤
    ∑ t ∈ S.filter (fun t : ℝ => (coefficientPolynomial n (fun j => (a j : ℂ))).eval
      (Complex.exp (I*(Complex.ofReal t)/n)) = 0),
        analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t) := by
  let R := (antiReciprocalPolynomial n a).roots.filter
    (fun z => (coefficientPolynomial n (fun j => (a j : ℂ))).eval z = 0 ∧
      ‖z‖ = 1 ∧ 0 ≤ z.im)
  let g : ℝ → ℂ := fun t => Complex.exp (I*(Complex.ofReal t)/n)
  let T := S.filter (fun t => (coefficientPolynomial n (fun j => (a j : ℂ))).eval (g t) = 0)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hanti := SignSineTotalMultiplicity.antiReciprocalPolynomial_ne_zero n hn a hf
  have hsub : R.toFinset ⊆ T.image g := by
    intro z hz
    have hzR : z ∈ R := Multiset.mem_toFinset.mp hz
    obtain ⟨hzroot,hzp,hzn,hzi⟩ := Multiset.mem_filter.mp hzR
    let t : ℝ := (n : ℝ) * Complex.arg z
    have ht : t ∈ Set.Icc 0 (Real.pi*n) := by
      refine ⟨mul_nonneg hn'.le (Complex.arg_nonneg_iff.mpr hzi), ?_⟩
      dsimp [t]
      nlinarith [mul_le_mul_of_nonneg_left (Complex.arg_le_pi z) hn'.le]
    have hgz : g t = z := by
      have he := UnitCircleBoundaryFactorization.exp_I_arg_of_norm_eq_one hzn
      dsimp [g,t]
      push_cast
      convert! he using 1
      congr 1
      field_simp
    have hzanti : (antiReciprocalPolynomial n a).eval z = 0 := (mem_roots hanti).mp hzroot
    have hfield : GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0 := by
      have he := SignSineTotalMultiplicity.rotated_antiReciprocalPolynomial_scaled n hn a (Complex.ofReal t)
      change Complex.exp (-I*(Complex.ofReal t)/2) * (antiReciprocalPolynomial n a).eval (g t) =
        (2*(Real.sqrt n : ℂ)*I) * GaussianComplex.scaledSineField n a (Complex.ofReal t) at he
      rw [hgz,hzanti,mul_zero] at he
      have hc : (2*(Real.sqrt n : ℂ)*I) ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero (by norm_num) _) I_ne_zero
        exact_mod_cast (Real.sqrt_pos.mpr hn').ne'
      exact (mul_eq_zero.mp he.symm).resolve_left hc
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨(hS t).mpr ⟨ht,hfield⟩,
      by rw [hgz]; exact hzp⟩,hgz⟩
  have hi : Set.InjOn g (T : Set ℝ) :=
    (SignSineTotalMultiplicity.scaled_circle_injOn n hn).mono (by
      intro t ht
      exact ((hS t).mp (Finset.mem_filter.mp ht).1).1)
  change R.card ≤ _
  calc
    R.card = ∑ z ∈ R.toFinset, (antiReciprocalPolynomial n a).rootMultiplicity z := by
      rw [← Multiset.toFinset_sum_count_eq R]
      apply Finset.sum_congr rfl
      intro z hz
      obtain ⟨_,hzp,hzn,hzi⟩ := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)
      simp only [R,Multiset.count_filter,hzp,hzn,hzi,and_self,ite_true,Polynomial.count_roots]
    _ ≤ ∑ z ∈ T.image g, (antiReciprocalPolynomial n a).rootMultiplicity z :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∑ t ∈ T, analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t) := by
      rw [Finset.sum_image hi]
      apply Finset.sum_congr rfl
      intro t _
      exact (SignSineTotalMultiplicity.analyticOrderNatAt_scaledSineField n hn a hf t).symm
lemma boundary_card_le_two_common_real_orders (n : ℕ) (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1))
    (hf : GaussianComplex.scaledSineField n a ≠ 0) (S : Finset ℝ)
    (hS : ∀ t, t ∈ S ↔ t ∈ Set.Icc 0 (Real.pi*n) ∧
      GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0) :
    ((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card ≤
    2 * ∑ t ∈ S.filter (fun t : ℝ => (coefficientPolynomial n (fun j => (a j : ℂ))).eval
      (Complex.exp (I*(Complex.ofReal t)/n)) = 0),
        analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t) := by
  exact (boundary_card_le_two_upper_common n a ha
    (SignSineTotalMultiplicity.antiReciprocalPolynomial_ne_zero n hn a hf)).trans
    (Nat.mul_le_mul_left 2 (upper_common_card_le_real_orders n hn a hf S hS))
lemma boundary_card_le_retained_common_add_endpoints (n : ℕ) (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1))
    (hf : GaussianComplex.scaledSineField n a ≠ 0) (S : Finset ℝ)
    (hS : ∀ t, t ∈ S ↔ t ∈ Set.Icc 0 (Real.pi*n) ∧
      GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0)
    (hbulk : SignSineOccupancy.endpointCutoff ≤ Real.pi*n-SignSineOccupancy.endpointCutoff) :
    (((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card : ℝ) ≤
    2 * (∑ t ∈ S.filter (fun t : ℝ =>
        t ∈ Set.Ioo SignSineOccupancy.endpointCutoff (Real.pi*n-SignSineOccupancy.endpointCutoff) ∧
        (coefficientPolynomial n (fun j => (a j : ℂ))).eval (Complex.exp (I*Complex.ofReal t/n)) = 0),
      (analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t) : ℝ)) +
    2 * ((SignSineOccupancy.realIntervalMultiplicity (GaussianComplex.scaledSineField n a)
      0 SignSineOccupancy.endpointCutoff +
      SignSineOccupancy.realIntervalMultiplicity (GaussianComplex.scaledSineField n a)
        (Real.pi*n-SignSineOccupancy.endpointCutoff) (Real.pi*n) : ℤ) : ℝ) := by
  let L := SignSineOccupancy.endpointCutoff
  let R := Real.pi*n-L
  let order : ℝ → ℕ := fun t => analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t)
  let P : ℝ → Prop := fun t => (coefficientPolynomial n (fun j => (a j : ℂ))).eval
    (Complex.exp (I*Complex.ofReal t/n)) = 0
  have hdecomp : (∑ t ∈ S.filter P, order t) ≤
      (∑ t ∈ S.filter (fun t => t ∈ Set.Ioo L R ∧ P t), order t) +
      (∑ t ∈ S.filter (fun t => t ≤ L), order t) +
      ∑ t ∈ S.filter (fun t => R ≤ t), order t := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    by_cases hp : P t
    · by_cases hb : t ∈ Set.Ioo L R
      · simp only [hp,hb,and_self,ite_true]
        omega
      · by_cases hl : t ≤ L
        · simp only [hp,hb,hl,false_and,ite_true,ite_false,zero_add]
          omega
        · have hr : R ≤ t := le_of_not_gt (fun ht => hb ⟨lt_of_not_ge hl,ht⟩)
          simp only [hp,hb,hl,hr,false_and,ite_true,ite_false,zero_add]
          omega
    · simp only [hp,and_false,ite_false,zero_add]
      exact Nat.zero_le _
  have hB := boundary_card_le_two_common_real_orders n hn a ha hf S hS
  have hBret : ((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card ≤
      2 * (∑ t ∈ S.filter (fun t => t ∈ Set.Ioo L R ∧ P t), order t) +
      2 * ((∑ t ∈ S.filter (fun t => t ≤ L), order t) +
        ∑ t ∈ S.filter (fun t => R ≤ t), order t) := by
    change _ ≤ 2 * ∑ t ∈ S.filter P, order t at hB
    omega
  have hL0 : 0 ≤ L := by dsimp [L,SignSineOccupancy.endpointCutoff]; positivity
  have hLpi : L ≤ Real.pi*n := by change L ≤ R at hbulk; dsimp [R] at hbulk; linarith
  have hR0 : 0 ≤ R := hL0.trans hbulk
  have hleft (t : ℝ) : t ∈ S.filter (fun t => t ≤ L) ↔
      t ∈ Set.Icc 0 L ∧ GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0 := by
    simp only [Finset.mem_filter,hS,Set.mem_Icc]
    constructor
    · rintro ⟨⟨⟨ht0,_⟩,hz⟩,htL⟩
      exact ⟨⟨ht0,htL⟩,hz⟩
    · rintro ⟨⟨ht0,htL⟩,hz⟩
      exact ⟨⟨⟨ht0,htL.trans hLpi⟩,hz⟩,htL⟩
  have hright (t : ℝ) : t ∈ S.filter (fun t => R ≤ t) ↔
      t ∈ Set.Icc R (Real.pi*n) ∧ GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0 := by
    simp only [Finset.mem_filter,hS,Set.mem_Icc]
    constructor
    · rintro ⟨⟨⟨_,htpi⟩,hz⟩,htR⟩
      exact ⟨⟨htR,htpi⟩,hz⟩
    · rintro ⟨⟨htR,htpi⟩,hz⟩
      exact ⟨⟨⟨hR0.trans htR,htpi⟩,hz⟩,htR⟩
  have han : ∀ z, AnalyticAt ℂ (GaussianComplex.scaledSineField n a) z :=
    (GaussianComplex.differentiable_scaledSineField n a).analyticAt
  have hel := SignSineTotalMultiplicity.realIntervalMultiplicity_eq_sum han 0 L
    (S.filter (fun t => t ≤ L)) hleft
  have her := SignSineTotalMultiplicity.realIntervalMultiplicity_eq_sum han R (Real.pi*n)
    (S.filter (fun t => R ≤ t)) hright
  have hfloat : (((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card : ℝ) ≤
      2 * (∑ t ∈ S.filter (fun t => t ∈ Set.Ioo L R ∧ P t), (order t : ℝ)) +
      2 * ((∑ t ∈ S.filter (fun t => t ≤ L), (order t : ℝ)) +
        ∑ t ∈ S.filter (fun t => R ≤ t), (order t : ℝ)) := by
    exact_mod_cast hBret
  change _ ≤ 2 * (∑ t ∈ S.filter (fun t => t ∈ Set.Ioo L R ∧ P t), (order t : ℝ)) +
    2 * ((SignSineOccupancy.realIntervalMultiplicity (GaussianComplex.scaledSineField n a) 0 L +
      SignSineOccupancy.realIntervalMultiplicity (GaussianComplex.scaledSineField n a) R (Real.pi*n) : ℤ) : ℝ)
  rw [hel,her]
  push_cast
  exact hfloat
lemma boundary_card_good_le_retained_common (n : ℕ) (hn : 0 < n)
    (a : Fin (n + 1) → ℝ) (ha : a ∈ signVectors (n + 1))
    (hg : ¬SignSineOccupancy.occupancyBad n a) (S : Finset ℝ)
    (hS : ∀ t, t ∈ S ↔ t ∈ Set.Icc 0 (Real.pi*n) ∧
      GaussianComplex.scaledSineField n a (Complex.ofReal t) = 0)
    (hbulk : SignSineOccupancy.endpointCutoff ≤ Real.pi*n-SignSineOccupancy.endpointCutoff) :
    (((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
      (fun z => ‖z‖ = 1)).card : ℝ) ≤
    2 * (∑ t ∈ S.filter (fun t : ℝ =>
        t ∈ Set.Ioo SignSineOccupancy.endpointCutoff (Real.pi*n-SignSineOccupancy.endpointCutoff) ∧
        (coefficientPolynomial n (fun j => (a j : ℂ))).eval (Complex.exp (I*Complex.ofReal t/n)) = 0),
      (analyticOrderNatAt (GaussianComplex.scaledSineField n a) (Complex.ofReal t) : ℝ)) +
      4 * SignSineOccupancy.localThreshold n := by
  obtain ⟨hf,_,hends⟩ := SignSineOccupancy.not_occupancyBad_spec n a hg
  have hB := boundary_card_le_retained_common_add_endpoints n hn a ha hf S hS hbulk
  linarith
end Fluctuations.SignBoundaryMultiplicityCharging
end
end

section
noncomputable section
open Filter Set Polynomial Complex
open scoped Topology BigOperators
namespace Fluctuations.HalfFiniteOrderCrossings
open PolynomialCircle CommonBoundaryCrossings SignedCrossings
open FiniteOrderCrossings FiniteOrderCrossingComparison FiniteOrderReflection
theorem exists_reflected_half_comparison (n : ℕ) (p : Polynomial ℂ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ n)
    (hY : (fun t => (rotatedCircleCurve n p t).im) ≠ 0)
    (hXreflection : ∀ t, (rotatedCircleCurve n p (2 * Real.pi - t)).re =
      (-1 : ℝ) ^ n * (rotatedCircleCurve n p t).re)
    (hYreflection : ∀ t, (rotatedCircleCurve n p (2 * Real.pi - t)).im =
      -((-1 : ℝ) ^ n) * (rotatedCircleCurve n p t).im) :
    ∃ S : Finset ℝ, ∃ g : ℝ → ℝ → ℝ,
      (∀ t, t ∈ S ↔ t ∈ Ioo 0 Real.pi ∧ (rotatedCircleCurve n p t).im = 0) ∧
      (∀ t, AnalyticAt ℝ (g t) t ∧ g t t ≠ 0 ∧
        ∀ᶠ s in 𝓝 t, (rotatedCircleCurve n p s).im =
          (s - t) ^ analyticOrderNatAt (fun u => (rotatedCircleCurve n p u).im) t * g t s) ∧
      |((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
        ∑ t ∈ S, (if Odd (analyticOrderNatAt (fun u => (rotatedCircleCurve n p u).im) t) then
          crossingOrientation (rotatedCircleCurve n p t).re (g t t) else 0)| ≤
            1 + ((p.roots.filter (fun z => ‖z‖ = 1)).card : ℝ) := by
  classical
  let Y : ℝ → ℝ := fun t => (rotatedCircleCurve n p t).im
  let X : ℝ → ℝ := fun t => (rotatedCircleCurve n p t).re
  have han (t : ℝ) : AnalyticAt ℝ Y t := by
    simpa only [one_mul] using analyticAt_im_const_mul_rotated n p 1 t
  obtain ⟨g, hg⟩ := exists_real_power_factors han hY
  obtain ⟨m, knots, gk, hm, hstart, hend, hstep, _, hz, hgk, hcomparison⟩ :=
    exists_actual_closed_count_crossing_comparison n p hp hdeg hY
  obtain ⟨T, hT, hsumT⟩ := exists_partition_zero_finset Y knots m hstart hend hstep hz
  let w : ℝ → ℝ := fun t => if Y t = 0 ∧ Odd (analyticOrderNatAt Y t) then
    crossingOrientation (X t) (g t t) else 0
  have hsum : (∑ i ∈ Finset.Ico 1 m,
      if Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i)) then
        crossingOrientation (X (knots i)) (gk i (knots i)) else 0) = ∑ t ∈ T, w t := by
    rw [← hsumT w (by intro t ht; simp [w, ht])]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i))
    · have hf := hgk i (Finset.mem_Ico.mp hi).2.le h.1
      have he := power_factor_value_unique hf.1.continuousAt (hg (knots i)).1.continuousAt
        hf.2.2 (hg (knots i)).2.2
      simp only [w, h, he]
    · simp only [w, h, ite_false]
  have hreflection (t : ℝ) : 2 * Real.pi - t ∈ T ↔ t ∈ T := by
    rw [hT, hT]
    have hyref : Y (2 * Real.pi - t) = -((-1 : ℝ) ^ n) * Y t := hYreflection t
    rw [hyref]
    have hr : -((-1 : ℝ) ^ n) ≠ 0 := by simp
    simp only [mul_eq_zero, hr, false_or]
    constructor <;> rintro ⟨ht, hy⟩ <;> exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hy⟩
  have hwreflection (t : ℝ) : w (2 * Real.pi - t) = w t :=
    finite_order_weight_reflection g (han t) (by simp : (-1 : ℝ) ^ n ≠ 0)
      (hXreflection t) hYreflection (fun t _ => hg t)
  have hwbound (t : ℝ) : |w t| ≤ 1 := by
    dsimp only [w]
    split_ifs
    · exact abs_crossingOrientation_le_one _ _
    · norm_num
  have hhalf := finite_reflection_half_sum T (2 * Real.pi) w hreflection hwreflection
    (hwbound ((2 * Real.pi) / 2))
  let S := T.filter (fun t => t < Real.pi)
  have hS (t : ℝ) : t ∈ S ↔ t ∈ Ioo 0 Real.pi ∧ Y t = 0 := by
    simp only [S, Finset.mem_filter, hT, mem_Ioo]
    constructor
    · rintro ⟨⟨⟨h0, _⟩, hy⟩, hpi⟩
      exact ⟨⟨h0, hpi⟩, hy⟩
    · rintro ⟨⟨h0, hpi⟩, hy⟩
      exact ⟨⟨⟨h0, by linarith [Real.pi_pos]⟩, hy⟩, hpi⟩
  have hSsum : (∑ t ∈ T.filter (fun t => t < (2 * Real.pi) / 2), w t) =
      ∑ t ∈ S, (if Odd (analyticOrderNatAt Y t) then crossingOrientation (X t) (g t t) else 0) := by
    simp only [show 2 * Real.pi / 2 = Real.pi by ring]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [w, (hS t).mp ht |>.2, true_and]
  change |((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
      (1 / 2 : ℝ) * (∑ i ∈ Finset.Ico 1 m,
        if Y (knots i) = 0 ∧ Odd (analyticOrderNatAt Y (knots i)) then
          crossingOrientation (X (knots i)) (gk i (knots i)) else 0)| ≤ _ at hcomparison
  rw [hsum] at hcomparison
  rw [hSsum] at hhalf
  refine ⟨S, g, hS, hg, ?_⟩
  have he : ((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
      (∑ t ∈ S, if Odd (analyticOrderNatAt Y t) then crossingOrientation (X t) (g t t) else 0) =
      (((p.roots.filter (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
        (1 / 2 : ℝ) * ∑ t ∈ T, w t) +
      ((∑ t ∈ T, w t) / 2 - ∑ t ∈ S,
        if Odd (analyticOrderNatAt Y t) then crossingOrientation (X t) (g t t) else 0) := by ring
  change |_ - ∑ t ∈ S, if Odd (analyticOrderNatAt Y t) then
    crossingOrientation (X t) (g t t) else 0| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)
theorem exists_actual_half_comparison (n : ℕ) (a : Fin (n + 1) → ℝ)
    (hp : coefficientPolynomial n (fun j => (a j : ℂ)) ≠ 0)
    (hY : centeredSineSum n a ≠ 0) :
    ∃ S : Finset ℝ, ∃ g : ℝ → ℝ → ℝ,
      (∀ t, t ∈ S ↔ t ∈ Ioo 0 Real.pi ∧ centeredSineSum n a t = 0) ∧
      (∀ t, AnalyticAt ℝ (g t) t ∧ g t t ≠ 0 ∧
        ∀ᶠ s in 𝓝 t, centeredSineSum n a s =
          (s - t) ^ analyticOrderNatAt (centeredSineSum n a) t * g t s) ∧
      |(((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
          (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ) / 2 -
        ∑ t ∈ S, (if Odd (analyticOrderNatAt (centeredSineSum n a) t) then
          crossingOrientation (centeredCosineSum n a t) (g t t) else 0)| ≤
            1 + (((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
              (fun z => ‖z‖ = 1)).card : ℝ) := by
  have hXcoord (t : ℝ) := (AntiReciprocal.rotated_coefficientPolynomial_coordinates n a t).1
  have hYcoord (t : ℝ) := (AntiReciprocal.rotated_coefficientPolynomial_coordinates n a t).2
  have he := exists_reflected_half_comparison n
    (coefficientPolynomial n (fun j => (a j : ℂ))) hp
    (coefficientPolynomial_natDegree_le _ _) (by simpa only [hYcoord] using hY)
    (by simpa only [hXcoord] using CenteredTrigReflection.cosine_sum_reflection n a)
    (by simpa only [hYcoord, neg_mul] using CenteredTrigReflection.sine_sum_reflection n a)
  simpa only [hXcoord, hYcoord] using he
end Fluctuations.HalfFiniteOrderCrossings
end
end

section
noncomputable section
open Finset Classical Set Filter
open scoped BigOperators Topology
namespace Fluctuations.SignFiberCrossings
open GaussianComplex SignActivityFiber SignPolynomialDivisibility
open FiniteOrderCrossings FiniteOrderCrossingComparison HalfFiniteOrderCrossings
open SignSineTotalMultiplicity SignRetainedZeroSampling SignSineOccupancy
lemma centeredSineSum_eq_of_sameSineFiber {n : ℕ} (hn : 0 < n)
    (a b : Fin (n+1) → ℝ) (hab : sameSineFiber n a b) :
    centeredSineSum n b = centeredSineSum n a := by
  funext t
  have he := congrArg Complex.re (congrFun
    (scaledSineField_eq_of_sameSineFiber n a b hab) (Complex.ofReal ((n : ℝ)*t)))
  rw [scaledSineField_ofReal,scaledSineField_ofReal] at he
  simp only [Complex.ofReal_re,mul_div_cancel_left₀ t
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))] at he
  exact (div_left_inj' (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne').mp he
lemma centeredSineSum_ne_zero {n : ℕ} (hn : 0 < n) (a : Fin (n+1) → ℝ)
    (hf : scaledSineField n a ≠ 0) : centeredSineSum n a ≠ 0 := by
  have hfinite : analyticOrderAt (scaledSineField n a) (0 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_scaledSineField n hn a hf]
    simp
  have he := analyticOrderAt_real_restriction
    ((differentiable_scaledSineField n a).analyticAt (z := (0 : ℂ))) hfinite
    (fun s => by rw [scaledSineField_ofReal]; exact Complex.ofReal_im _)
  intro hz
  have hreal : (fun s : ℝ => (scaledSineField n a (s : ℂ)).re) = 0 := by
    funext s
    rw [scaledSineField_ofReal,hz]
    simp
  rw [hreal] at he
  simp only [Complex.ofReal_zero] at he
  apply hfinite
  rw [← he]
  exact analyticOrderAt_eq_top.mpr (Eventually.of_forall (fun _ => rfl))
lemma sign_coefficientPolynomial_ne_zero (n : ℕ) (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) : coefficientPolynomial n (fun j => (a j : ℂ)) ≠ 0 := by
  intro hp
  have he := congrArg (fun p : Polynomial ℂ => p.coeff (Fin.last n).val) hp
  rw [coefficientPolynomial_coeff_fin,Polynomial.coeff_zero] at he
  have ha0 : a (Fin.last n) ≠ 0 := by
    rcases (mem_signVectors a).mp ha (Fin.last n) with h | h <;> simp [h]
  exact ha0 (Complex.ofReal_eq_zero.mp he)
theorem exists_actual_uniform_half_crossing {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1))
    (hf : scaledSineField n a ≠ 0) :
    ∃ U : Finset ℝ, ∃ β : ℝ → ℝ,
      (∀ t, t ∈ U ↔ t ∈ Ioo 0 Real.pi ∧ centeredSineSum n a t = 0) ∧
      (∀ t, |β t| ≤ 1) ∧
      ∀ b ∈ signVectors (n+1), sameSineFiber n a b →
        |(((coefficientPolynomial n (fun j => (b j : ℂ))).roots.filter
            (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2 -
          ∑ t ∈ U, β t * Real.sign (centeredCosineSum n b t)| ≤
          1 + (((coefficientPolynomial n (fun j => (b j : ℂ))).roots.filter
            (fun z => ‖z‖ = 1)).card : ℝ) := by
  obtain ⟨U,g,hU,hg,_⟩ := exists_actual_half_comparison n a
    (sign_coefficientPolynomial_ne_zero n a ha) (centeredSineSum_ne_zero hn a hf)
  let β : ℝ → ℝ := fun t => if Odd (analyticOrderNatAt (centeredSineSum n a) t)
    then Real.sign (g t t) else 0
  have hβ (t : ℝ) : |β t| ≤ 1 := by
    dsimp only [β]
    split_ifs
    · exact GaussianHolder.abs_real_sign_le_one _
    · norm_num
  refine ⟨U,β,hU,hβ,?_⟩
  intro b hb hab
  have hY := centeredSineSum_eq_of_sameSineFiber hn a b hab
  obtain ⟨V,h,hV,hh,hcomp⟩ := exists_actual_half_comparison n b
    (sign_coefficientPolynomial_ne_zero n b hb) (by rw [hY]; exact centeredSineSum_ne_zero hn a hf)
  have hVU : V = U := by
    ext t
    rw [hV,hU,hY]
  have hh' : ∀ t, AnalyticAt ℝ (h t) t ∧ h t t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, centeredSineSum n a s =
        (s-t)^analyticOrderNatAt (centeredSineSum n a) t * h t s := by
    simpa only [hY] using hh
  have hleading (t : ℝ) : h t t = g t t :=
    power_factor_value_unique (hh' t).1.continuousAt (hg t).1.continuousAt
      (hh' t).2.2 (hg t).2.2
  rw [hVU,hY] at hcomp
  convert! hcomp using 2
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [β,hleading,SignedCrossings.crossingOrientation_eq_real_sign]
  split_ifs <;> ring
lemma scaledSineField_eq_zero_iff {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (t : ℝ) :
    scaledSineField n a (Complex.ofReal t) = 0 ↔ centeredSineSum n a (t/n) = 0 := by
  rw [scaledSineField_ofReal,Complex.ofReal_eq_zero,div_eq_zero_iff]
  simp only [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne',or_false]
theorem exists_actual_scaled_uniform_half_crossing {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1))
    (hf : scaledSineField n a ≠ 0) :
    ∃ T : Finset ℝ, ∃ β : ℝ → ℝ,
      (∀ t, t ∈ T ↔ t ∈ Ioo 0 (Real.pi*n) ∧ scaledSineField n a (Complex.ofReal t) = 0) ∧
      (∀ t, |β t| ≤ 1) ∧
      ∀ b ∈ signVectors (n+1), sameSineFiber n a b →
        |(((coefficientPolynomial n (fun j => (b j : ℂ))).roots.filter
            (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2 -
          ∑ t ∈ T, β t * Real.sign (centeredCosineSum n b (t/n))| ≤
          1 + (((coefficientPolynomial n (fun j => (b j : ℂ))).roots.filter
            (fun z => ‖z‖ = 1)).card : ℝ) := by
  obtain ⟨U,β,hU,hβ,hcomp⟩ := exists_actual_uniform_half_crossing hn a ha hf
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let T := U.image (fun t => (n : ℝ)*t)
  have hT (t : ℝ) : t ∈ T ↔ t ∈ Ioo 0 (Real.pi*n) ∧ scaledSineField n a (Complex.ofReal t) = 0 := by
    rw [scaledSineField_eq_zero_iff hn]
    constructor
    · intro ht
      obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
      obtain ⟨hsI,hsY⟩ := (hU s).mp hs
      simp only [mul_div_cancel_left₀ s hnR.ne']
      exact ⟨⟨mul_pos hnR hsI.1,by nlinarith [mul_lt_mul_of_pos_left hsI.2 hnR]⟩,hsY⟩
    · rintro ⟨ht,hy⟩
      apply mem_image.mpr
      refine ⟨t/n,(hU _).mpr ⟨⟨div_pos ht.1 hnR,(div_lt_iff₀ hnR).mpr ht.2⟩,hy⟩,?_⟩
      exact mul_div_cancel₀ t hnR.ne'
  refine ⟨T,(fun t => β (t/n)),hT,(fun t => hβ (t/n)),?_⟩
  intro b hb hab
  have he : (∑ t ∈ T, β (t/n) * Real.sign (centeredCosineSum n b (t/n))) =
      ∑ s ∈ U, β s * Real.sign (centeredCosineSum n b s) := by
    rw [show T = U.image (fun t => (n : ℝ)*t) from rfl,Finset.sum_image
      (fun s _ t _ h => mul_left_cancel₀ hnR.ne' h)]
    simp only [mul_div_cancel_left₀ _ hnR.ne']
  rw [he]
  exact hcomp b hb hab
lemma retained_crossing_endpoint_error {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (hf : scaledSineField n a ≠ 0)
    (T : Finset ℝ)
    (hT : ∀ t ∈ T, t ∈ Ioo 0 (Real.pi*n) ∧ scaledSineField n a (Complex.ofReal t) = 0)
    (w : ℝ → ℝ) (hw : ∀ t, |w t| ≤ 1) :
    |(∑ t ∈ T, w t) - ∑ t ∈ T.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)), w t| ≤
      (realIntervalMultiplicity (scaledSineField n a) 0 endpointCutoff : ℝ) +
        (realIntervalMultiplicity (scaledSineField n a) (Real.pi*n-endpointCutoff) (Real.pi*n) : ℝ) := by
  let A := T.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff))
  let E := T \ A
  have he : (∑ t ∈ T, w t) - ∑ t ∈ A, w t = ∑ t ∈ E, w t := by
    have hs := Finset.sum_sdiff (f := w) (show A ⊆ T from filter_subset _ _)
    change (∑ t ∈ E, w t) + (∑ t ∈ A, w t) = ∑ t ∈ T, w t at hs
    linarith
  have horder (t : ℝ) (ht : t ∈ E) : |w t| ≤
      (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) := by
    have htT := (mem_sdiff.mp ht).1
    have hp := scaled_sine_order_pos hn a hf t (hT t htT).2
    exact (hw t).trans (by exact_mod_cast hp)
  let EL := E.filter (fun t => t ≤ endpointCutoff)
  let ER := E.filter (fun t => endpointCutoff < t)
  have hEL (t : ℝ) (ht : t ∈ EL) : t ∈ Icc 0 endpointCutoff ∧ scaledSineField n a (Complex.ofReal t) = 0 :=
    ⟨⟨(hT t (mem_sdiff.mp (mem_filter.mp ht).1).1).1.1.le,(mem_filter.mp ht).2⟩,
      (hT t (mem_sdiff.mp (mem_filter.mp ht).1).1).2⟩
  have hER (t : ℝ) (ht : t ∈ ER) : t ∈ Icc (Real.pi*n-endpointCutoff) (Real.pi*n) ∧
      scaledSineField n a (Complex.ofReal t) = 0 := by
    obtain ⟨htE,htL⟩ := mem_filter.mp ht
    obtain ⟨htT,htA⟩ := mem_sdiff.mp htE
    have htR : Real.pi*n-endpointCutoff ≤ t := by
      by_contra h
      exact htA (mem_filter.mpr ⟨htT,⟨htL,lt_of_not_ge h⟩⟩)
    exact ⟨⟨htR,(hT t htT).1.2.le⟩,(hT t htT).2⟩
  have hsplit : (∑ t ∈ E, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ)) =
      (∑ t ∈ EL, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ)) +
        ∑ t ∈ ER, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) := by
    simpa only [EL,ER,not_le] using (sum_filter_add_sum_filter_not E (fun t => t ≤ endpointCutoff)
      (fun t => (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ))).symm
  change |_ - ∑ t ∈ A, w t| ≤ _
  rw [he]
  calc
    _ ≤ ∑ t ∈ E, |w t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ E, (analyticOrderNatAt (scaledSineField n a) (Complex.ofReal t) : ℝ) := sum_le_sum horder
    _ = _ := hsplit
    _ ≤ _ := add_le_add (sum_scaled_sine_orders_le_interval n a hf 0 endpointCutoff EL hEL)
      (sum_scaled_sine_orders_le_interval n a hf (Real.pi*n-endpointCutoff) (Real.pi*n) ER hER)
lemma common_root_cosine_eq_zero (n : ℕ) (a : Fin (n+1) → ℝ) (t : ℝ)
    (hz : (coefficientPolynomial n (fun j => (a j : ℂ))).eval
      (Complex.exp (Complex.I*Complex.ofReal t/n)) = 0) :
    centeredCosineSum n a (t/n) = 0 := by
  have he := (AntiReciprocal.rotated_coefficientPolynomial_coordinates n a (t/n)).1
  rw [PolynomialCircle.rotatedCircleCurve,PolynomialCircle.unitCircleCurve_eq_exp] at he
  have harg : Complex.I*((t/n : ℝ) : ℂ) = Complex.I*Complex.ofReal t/n := by
    push_cast; ring
  rw [harg,hz,mul_zero,Complex.zero_re] at he
  exact he.symm
theorem exists_actual_fiber_count_rows {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1))
    (hg : ¬occupancyBad n a) (hm : ¬SignConditionalRows.maskBad n a)
    (hbulk : endpointCutoff ≤ Real.pi*n-endpointCutoff) :
    ∃ N : ℕ, ∃ loc b : Fin N → ℝ,
      N ≤ n ∧
      (∀ i, loc i ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) ∧
        scaledSineField n a (Complex.ofReal (loc i)) = 0) ∧
      (∀ i, |b i| ≤ 1) ∧
      (∀ u : {j // j ∈ freeIndices n a} → ℝ,
        (∑ i, (∑ j, GaussianSampling.normalizedRow
          (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i j * u j)^2) ≤
            (80*Real.pi*Nat.ceil (localThreshold n))*∑ j, u j^2) ∧
      ∀ c ∈ signVectors (n+1), sameSineFiber n a c →
        |(((coefficientPolynomial n (fun j => (c j : ℂ))).roots.filter
          (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2 -
          ∑ i, b i*Real.sign (centeredCosineSum n c (loc i/n))| ≤
          1+6*localThreshold n+2*∑ i, if centeredCosineSum n c (loc i/n) = 0 then (1 : ℝ) else 0 := by
  obtain ⟨hf,_,hends⟩ := not_occupancyBad_spec n a hg
  obtain ⟨T,β,hT,hβ,hcross⟩ := exists_actual_scaled_uniform_half_crossing hn a ha hf
  obtain ⟨S,N,loc,b,hS,_,hN,hloc,hb,hsum,hbsum,hframe⟩ :=
    exists_actual_retained_row_family n hn a ha hg hm β hβ
  let A := S.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff))
  have hcut : 0 < endpointCutoff := by dsimp [endpointCutoff]; positivity
  have hA : A = T.filter (fun t => t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)) := by
    ext t
    simp only [A,mem_filter,hS,hT,Set.mem_Icc,Set.mem_Ioo]
    constructor
    · rintro ⟨⟨⟨_,_⟩,hz⟩,htL,htR⟩
      exact ⟨⟨⟨by linarith,by linarith⟩,hz⟩,htL,htR⟩
    · rintro ⟨⟨⟨ht0,htpi⟩,hz⟩,htL,htR⟩
      exact ⟨⟨⟨ht0.le,htpi.le⟩,hz⟩,htL,htR⟩
  refine ⟨N,loc,b,hN,hloc,hb,hframe,?_⟩
  intro c hc hac
  have hfield := scaledSineField_eq_of_sameSineFiber n a c hac
  have hgc : ¬occupancyBad n c := by
    rw [occupancyBad_congr n a c hac]
    exact hg
  have hSc (t : ℝ) : t ∈ S ↔ t ∈ Icc 0 (Real.pi*n) ∧ scaledSineField n c (Complex.ofReal t) = 0 := by
    rw [hfield]
    exact hS t
  let w : ℝ → ℝ := fun t => β t*Real.sign (centeredCosineSum n c (t/n))
  have hw (t : ℝ) : |w t| ≤ 1 := by
    dsimp only [w]
    rw [abs_mul]
    exact (mul_le_mul (hβ t) (GaussianHolder.abs_real_sign_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hend := retained_crossing_endpoint_error hn a hf T (fun t ht => (hT t).mp ht) w hw
  rw [← hA] at hend
  have hsigned : (∑ i, b i*Real.sign (centeredCosineSum n c (loc i/n))) = ∑ t ∈ A, w t :=
    hbsum (fun t => Real.sign (centeredCosineSum n c (t/n)))
  have hcomp := hcross c hc hac
  have hcomp' : |(((coefficientPolynomial n (fun j => (c j : ℂ))).roots.filter
      (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2 - ∑ i, b i*Real.sign (centeredCosineSum n c (loc i/n))| ≤
      1+(((coefficientPolynomial n (fun j => (c j : ℂ))).roots.filter
        (fun z => ‖z‖ = 1)).card : ℝ)+2*localThreshold n := by
    rw [hsigned]
    have htri := abs_sub_le (((coefficientPolynomial n (fun j => (c j : ℂ))).roots.filter
      (fun z => ‖z‖ ≤ 1)).card - (n : ℝ)/2) (∑ t ∈ T, w t) (∑ t ∈ A, w t)
    change |_ - ∑ t ∈ T, w t| ≤ _ at hcomp
    push_cast at hends
    linarith
  have hB := SignBoundaryMultiplicityCharging.boundary_card_good_le_retained_common n hn c hc hgc S hSc hbulk
  have hcommon : (∑ t ∈ S.filter (fun t : ℝ =>
      t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff) ∧
      (coefficientPolynomial n (fun j => (c j : ℂ))).eval (Complex.exp (Complex.I*Complex.ofReal t/n)) = 0),
      (analyticOrderNatAt (scaledSineField n c) (Complex.ofReal t) : ℝ)) ≤
        ∑ i, if centeredCosineSum n c (loc i/n) = 0 then (1 : ℝ) else 0 := by
    rw [hsum (fun t => if centeredCosineSum n c (t/n) = 0 then (1 : ℝ) else 0)]
    rw [Finset.sum_filter,Finset.sum_filter]
    apply sum_le_sum
    intro t _
    by_cases ht : t ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)
    · by_cases hz : (coefficientPolynomial n (fun j => (c j : ℂ))).eval
          (Complex.exp (Complex.I*Complex.ofReal t/n)) = 0
      · simp only [ht,hz,and_self,ite_true,common_root_cosine_eq_zero n c t hz,mul_one,hfield]
        exact le_refl _
      · simp only [ht,hz,and_false,ite_false,ite_true]
        split_ifs <;> positivity
    · simp only [ht,false_and,ite_false]
      exact le_refl _
  linarith
lemma normalized_free_cosine_sign {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1)) (x : ℝ)
    (hV : 0 < SignConditionalRows.conditionalCosineVariance n a x)
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    Real.sign (∑ j, GaussianSampling.normalizedRow
      (fun t => SignConditionalRows.conditionalCosineRow n a t) x j*u j) =
      Real.sign (centeredCosineSum n (fillFree n a u) (x/n)) := by
  rw [GaussianSampling.sign_normalizedRow_eval _ x hV,
    SignConditionalRows.conditionalCosineRow_eval n a ha,
    (PolynomialCircle.scaledRotated_ofFn_real_coordinates n (fillFree n a u) x).1]
  exact GaussianSampling.real_sign_div_pos _ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
lemma normalized_free_cosine_zero {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1)) (x : ℝ)
    (hV : 0 < SignConditionalRows.conditionalCosineVariance n a x)
    (u : {j // j ∈ freeIndices n a} → ℝ) :
    (∑ j, GaussianSampling.normalizedRow
      (fun t => SignConditionalRows.conditionalCosineRow n a t) x j*u j) = 0 ↔
      centeredCosineSum n (fillFree n a u) (x/n) = 0 := by
  rw [GaussianSampling.normalizedRow_eval,SignConditionalRows.conditionalCosineRow_eval n a ha,
    (PolynomialCircle.scaledRotated_ofFn_real_coordinates n (fillFree n a u) x).1]
  change (_/Real.sqrt (SignConditionalRows.conditionalCosineVariance n a x)) = 0 ↔ _
  rw [div_eq_zero_iff,div_eq_zero_iff]
  simp only [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne',
    (Real.sqrt_pos.mpr hV).ne',or_false]
theorem exists_actual_free_row_count_consumer {n : ℕ} (hn : 0 < n)
    (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1))
    (hg : ¬occupancyBad n a) (hm : ¬SignConditionalRows.maskBad n a)
    (hbulk : endpointCutoff ≤ Real.pi*n-endpointCutoff) :
    ∃ N : ℕ, ∃ loc b : Fin N → ℝ,
      N ≤ n ∧
      (∀ i, loc i ∈ Ioo endpointCutoff (Real.pi*n-endpointCutoff)) ∧
      (∀ i, |b i| ≤ 1) ∧
      (∀ i, (1 : ℝ)/8 ≤ SignConditionalRows.conditionalCosineVariance n a (loc i)) ∧
      (∀ u : {j // j ∈ freeIndices n a} → ℝ,
        (∑ i, (∑ j, GaussianSampling.normalizedRow
          (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i j*u j)^2) ≤
            (80*Real.pi*Nat.ceil (localThreshold n))*∑ j, u j^2) ∧
      ∀ u : {j // j ∈ freeIndices n a} → ℝ, (∀ j, u j = 1 ∨ u j = -1) →
        |(((coefficientPolynomial n (fun j => (fillFree n a u j : ℂ))).roots.filter
          (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2 -
          ∑ i, b i*Real.sign (∑ j, GaussianSampling.normalizedRow
            (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i j*u j)| ≤
          1+6*localThreshold n+2*∑ i, if (∑ j, GaussianSampling.normalizedRow
            (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i j*u j) = 0
              then (1 : ℝ) else 0 := by
  obtain ⟨N,loc,b,hN,hloc,hb,hframe,hcount⟩ := exists_actual_fiber_count_rows hn a ha hg hm hbulk
  have hV (i : Fin N) : (1 : ℝ)/8 ≤ SignConditionalRows.conditionalCosineVariance n a (loc i) :=
    SignConditionalRows.not_maskBad_spec n a hm (loc i) ⟨(hloc i).1.1.le,(hloc i).1.2.le⟩
  refine ⟨N,loc,b,hN,(fun i => (hloc i).1),hb,hV,hframe,?_⟩
  intro u hu
  have he := hcount (fillFree n a u) (fillFree_signs n a ha u hu) (fillFree_sameSineFiber n a u)
  have hsg (i : Fin N) := normalized_free_cosine_sign hn a ha (loc i)
    (lt_of_lt_of_le (by norm_num) (hV i)) u
  have hz (i : Fin N) := normalized_free_cosine_zero hn a ha (loc i)
    (lt_of_lt_of_le (by norm_num) (hV i)) u
  simp only [← hsg,← hz] at he
  simpa only [GaussianSampling.normalizedRow,GaussianSampling.rowNormSq] using he
end Fluctuations.SignFiberCrossings
end
end

section
noncomputable section
open Finset Classical
open scoped BigOperators
namespace Fluctuations.FiniteCubeConvexTransport
def cubeAverage {m : ℕ} (f : (Fin m → Bool) → ℝ) : ℝ :=
  (Fintype.card (Fin m → Bool) : ℝ)⁻¹ * ∑ x, f x
def supportedWeight {m : ℕ} (A : Finset (Fin m → Bool))
    (w : (Fin m → Bool) → ℝ) : Prop :=
  (∀ y, 0 ≤ w y) ∧ (∑ y, w y) = 1 ∧ (∀ y, y ∉ A → w y = 0)
def mismatchCost {m : ℕ} (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ i, (∑ y, w y * (if x i = y i then 0 else 1)) ^ 2
end Fluctuations.FiniteCubeConvexTransport
end
end

section
noncomputable section
open Set
open scoped BigOperators
namespace Fluctuations.FiniteCubeConvexTransport
lemma entropy_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    -r * Real.log r ≤ (1-r^2)/2 := by
  let h : ℝ → ℝ := fun x => 1-x^2+2*x*Real.log x
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt h (2*(Real.log x+1-x)) x := by
    convert! ((hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).pow 2)).add
      (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).const_mul 2) using 1
    · funext u
      simp only [h, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]
      ring
    · simp only [id_eq]
      field_simp
      ring
  have ha : AntitoneOn h (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (by simpa only [interior_Ioi, mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
      rw [(hd x hx0).deriv]
      linarith [Real.log_le_sub_one_of_pos hx0]
  have hh := ha hr (by norm_num : (1 : ℝ) ∈ Ioi 0) hr1
  dsimp [h] at hh
  rw [Real.log_one] at hh
  nlinarith
lemma two_fiber_exp_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.exp (-r*Real.log r+(1-r)^2/4) ≤ (3-r)/(1+r) := by
  have he : -r*Real.log r+(1-r)^2/4 ≤ 1-r := by
    nlinarith [entropy_bound hr hr1, sq_nonneg (1-r)]
  calc
    _ ≤ Real.exp (1-r) := Real.exp_le_exp.mpr he
    _ ≤ (2+(1-r))/(2-(1-r)) :=
      Real.exp_le_two_add_div_two_sub (by linarith) (by linarith)
    _ = (3-r)/(1+r) := by congr 1 <;> ring
lemma empty_fiber_exp_bound : Real.exp (1/4 : ℝ) ≤ 3 := by
  have h := Real.exp_le_two_add_div_two_sub
    (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) < 2)
  norm_num at h ⊢
  linarith
lemma mixture_square_le {r a b : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ((1-r)*a+r*b)^2 ≤ (1-r)*a^2+r*b^2 := by
  have h := mul_nonneg (mul_nonneg hr (sub_nonneg.mpr hr1)) (sq_nonneg (a-b))
  nlinarith
lemma finite_exponential_holder_bound {ι : Type*} [Fintype ι]
    (w f g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {r u v : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 < u) (hv : 0 < v)
    (hf : (∑ i, w i * Real.exp (f i)) ≤ u)
    (hg : (∑ i, w i * Real.exp (g i)) ≤ v) :
    (∑ i, w i * Real.exp ((1-r)*f i+r*g i)) ≤
      Real.exp ((1-r)*Real.log u+r*Real.log v) := by
  have hs : 0 ≤ 1-r := sub_nonneg.mpr hr1
  have hp (i : ι) :
      Real.exp ((1-r)*(f i-Real.log u)+r*(g i-Real.log v)) ≤
        (1-r)*(Real.exp (f i)/u)+r*(Real.exp (g i)/v) := by
    have h := convexOn_exp.2 (Set.mem_univ (f i-Real.log u))
      (Set.mem_univ (g i-Real.log v)) hs hr (by ring : 1-r+r=1)
    simpa only [smul_eq_mul, Real.exp_sub, Real.exp_log hu,
      Real.exp_log hv] using h
  have hsum :
      (∑ i, w i * Real.exp ((1-r)*(f i-Real.log u)+r*(g i-Real.log v))) ≤ 1 := by
    calc
      _ ≤ ∑ i, w i * ((1-r)*(Real.exp (f i)/u)+r*(Real.exp (g i)/v)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i))
      _ = (1-r)*((∑ i, w i*Real.exp (f i))/u)+
          r*((∑ i, w i*Real.exp (g i))/v) := by
        simp only [mul_add, Finset.sum_add_distrib, div_eq_mul_inv]
        simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
      _ ≤ (1-r)*1+r*1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left ((div_le_one hu).mpr hf) hs)
          (mul_le_mul_of_nonneg_left ((div_le_one hv).mpr hg) hr)
      _ = 1 := by ring
  calc
    _ = Real.exp ((1-r)*Real.log u+r*Real.log v) *
        ∑ i, w i*Real.exp ((1-r)*(f i-Real.log u)+r*(g i-Real.log v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp ((1-r)*Real.log u+r*Real.log v)*1 :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := mul_one _
lemma two_fiber_average_bound {p₀ p₁ : ℝ} (h₀ : 0 < p₀) (h₁ : 0 < p₁)
    (hp : p₁ ≤ p₀) :
    (p₀⁻¹+Real.exp ((1-p₁/p₀)^2/4)*
      Real.exp ((1-p₁/p₀)*Real.log (p₀⁻¹)+(p₁/p₀)*Real.log (p₁⁻¹)))/2 ≤
      2/(p₀+p₁) := by
  have hr : 0 < p₁/p₀ := div_pos h₁ h₀
  have hr1 : p₁/p₀ ≤ 1 := (div_le_one h₀).mpr hp
  have he : Real.exp ((1-p₁/p₀)^2/4)*
      Real.exp ((1-p₁/p₀)*Real.log (p₀⁻¹)+(p₁/p₀)*Real.log (p₁⁻¹)) =
      p₀⁻¹*Real.exp (-(p₁/p₀)*Real.log (p₁/p₀)+(1-p₁/p₀)^2/4) := by
    rw [← Real.exp_add]
    calc
      _ = Real.exp (-Real.log p₀+
          (-(p₁/p₀)*Real.log (p₁/p₀)+(1-p₁/p₀)^2/4)) := by
        congr 1
        rw [Real.log_inv, Real.log_inv, Real.log_div h₁.ne' h₀.ne']
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log h₀]
  rw [he]
  calc
    _ ≤ (p₀⁻¹+p₀⁻¹*((3-p₁/p₀)/(1+p₁/p₀)))/2 := by
      gcongr
      exact two_fiber_exp_bound hr hr1
    _ = 2/(p₀+p₁) := by
      field_simp
      ring
end Fluctuations.FiniteCubeConvexTransport
end
end

section
noncomputable section
open Finset Classical
open scoped BigOperators
namespace Fluctuations.FiniteCubeConvexTransport
lemma cubeAverage_nonneg {m : ℕ} {f : (Fin m → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ cubeAverage f := by
  exact mul_nonneg (by positivity) (sum_nonneg (fun x _ => hf x))
lemma cubeAverage_mono {m : ℕ} {f g : (Fin m → Bool) → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage f ≤ cubeAverage g := by
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun x _ => h x)) (by positivity)
lemma cubeAverage_const (m : ℕ) (a : ℝ) :
    cubeAverage (fun _ : Fin m → Bool => a) = a := by
  simp [cubeAverage]
lemma cubeAverage_add {m : ℕ} (f g : (Fin m → Bool) → ℝ) :
    cubeAverage (fun x => f x+g x) = cubeAverage f+cubeAverage g := by
  simp only [cubeAverage, sum_add_distrib, mul_add]
lemma cubeAverage_mul {m : ℕ} (a : ℝ) (f : (Fin m → Bool) → ℝ) :
    cubeAverage (fun x => a*f x) = a*cubeAverage f := by
  simp only [cubeAverage, ← mul_sum]
  ring
lemma cube_sum_cons {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∑ x, f x) = (∑ x, f (Fin.cons false x))+(∑ x, f (Fin.cons true x)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp f]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _
lemma cubeAverage_cons {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    cubeAverage f = (cubeAverage (fun x => f (Fin.cons false x))+
      cubeAverage (fun x => f (Fin.cons true x)))/2 := by
  simp only [cubeAverage, cube_sum_cons, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, pow_succ, Nat.cast_mul]
  field_simp
lemma cubeAverage_exponential_holder {m : ℕ}
    (f g : (Fin m → Bool) → ℝ) {r u v : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 < u) (hv : 0 < v)
    (hf : cubeAverage (fun x => Real.exp (f x)) ≤ u)
    (hg : cubeAverage (fun x => Real.exp (g x)) ≤ v) :
    cubeAverage (fun x => Real.exp ((1-r)*f x+r*g x)) ≤
      Real.exp ((1-r)*Real.log u+r*Real.log v) := by
  rw [cubeAverage, mul_sum]
  apply finite_exponential_holder_bound
    (fun _ => (Fintype.card (Fin m → Bool) : ℝ)⁻¹) f g
    (fun _ => by positivity) hr hr1 hu hv
  · simpa only [← mul_sum, cubeAverage] using hf
  · simpa only [← mul_sum, cubeAverage] using hg
lemma mismatchCost_nonneg {m : ℕ} (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) : 0 ≤ mismatchCost x w := by
  exact sum_nonneg (fun i _ => sq_nonneg _)
lemma mismatchCost_zero_dimension (x : Fin 0 → Bool)
    (w : (Fin 0 → Bool) → ℝ) : mismatchCost x w = 0 := by
  simp [mismatchCost]
lemma supportedWeight_lift {m : ℕ} (A : Finset (Fin (m+1) → Bool))
    (B : Finset (Fin m → Bool)) (b : Bool) (w : (Fin m → Bool) → ℝ)
    (hw : supportedWeight B w) (hA : ∀ y ∈ B, Fin.cons b y ∈ A) :
    supportedWeight A (fun y => if y 0=b then w (Fin.tail y) else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    dsimp only
    split_ifs
    · exact hw.1 _
    · exact le_rfl
  · rw [cube_sum_cons]
    cases b <;> simp [hw.2.1]
  · intro y hy
    dsimp only
    split_ifs with hb
    · apply hw.2.2
      intro hB
      apply hy
      have h := hA (Fin.tail y) hB
      simpa only [← hb, Fin.cons_self_tail] using h
    · rfl
lemma mismatchCost_lift {m : ℕ} (b c : Bool) (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) (hw : (∑ y, w y)=1) :
    mismatchCost (Fin.cons c x) (fun y => if y 0=b then w (Fin.tail y) else 0) =
      mismatchCost x w + (if c=b then 0 else 1) := by
  cases b <;> cases c <;>
    simp [mismatchCost, Fin.sum_univ_succ, cube_sum_cons, hw, add_comm]
lemma supportedWeight_mixture {m : ℕ} (A : Finset (Fin m → Bool))
    (w₀ w₁ : (Fin m → Bool) → ℝ) (h₀ : supportedWeight A w₀)
    (h₁ : supportedWeight A w₁) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    supportedWeight A (fun y => (1-r)*w₀ y+r*w₁ y) := by
  refine ⟨fun y => add_nonneg (mul_nonneg (sub_nonneg.mpr hr1) (h₀.1 y))
    (mul_nonneg hr (h₁.1 y)), ?_, ?_⟩
  · simp only [sum_add_distrib, ← mul_sum, h₀.2.1, h₁.2.1]
    ring
  · intro y hy
    simp only [h₀.2.2 y hy, h₁.2.2 y hy, mul_zero, add_zero]
lemma cubeAverage_indicator {m : ℕ} (A : Finset (Fin m → Bool)) :
    cubeAverage (fun y => if y∈A then 1 else 0) =
      (Fintype.card (Fin m → Bool) : ℝ)⁻¹*(A.card : ℝ) := by
  simp [cubeAverage]
lemma cubeAverage_indicator_pos {m : ℕ} {A : Finset (Fin m → Bool)}
    (hA : A.Nonempty) : 0 < cubeAverage (fun y => if y∈A then 1 else 0) := by
  rw [cubeAverage_indicator]
  exact mul_pos (by positivity) (Nat.cast_pos.mpr hA.card_pos)
lemma nonempty_of_cubeAverage_indicator_pos {m : ℕ} {A : Finset (Fin m → Bool)}
    (hA : 0 < cubeAverage (fun y => if y∈A then 1 else 0)) : A.Nonempty := by
  by_contra hn
  have h : A=∅ := not_nonempty_iff_eq_empty.mp hn
  simp [h, cubeAverage] at hA
lemma mismatchCost_lift_mixture_le {m : ℕ} (b : Bool) (x : Fin m → Bool)
    (w₀ w₁ : (Fin m → Bool) → ℝ) (h₀ : (∑ y, w₀ y)=1)
    (_h₁ : (∑ y, w₁ y)=1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    mismatchCost (Fin.cons (!b) x) (fun y =>
      (1-r)*(if y 0=b then w₀ (Fin.tail y) else 0)+
      r*(if y 0=(!b) then w₁ (Fin.tail y) else 0)) ≤
      (1-r)*mismatchCost x w₀+r*mismatchCost x w₁+(1-r)^2 := by
  have hscale (a : ℝ) (w : (Fin m → Bool) → ℝ) (i : Fin m) :
      (∑ y, if x i=y i then 0 else a*w y) =
        a*(∑ y, if x i=y i then 0 else w y) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    split_ifs <;> simp
  have he : mismatchCost (Fin.cons (!b) x) (fun y =>
      (1-r)*(if y 0=b then w₀ (Fin.tail y) else 0)+
      r*(if y 0=(!b) then w₁ (Fin.tail y) else 0)) =
      (1-r)^2+∑ i, ((1-r)*(∑ y, w₀ y*(if x i=y i then 0 else 1))+
        r*(∑ y, w₁ y*(if x i=y i then 0 else 1)))^2 := by
    cases b <;> simp [mismatchCost, Fin.sum_univ_succ, cube_sum_cons,
      ← mul_sum, h₀, hscale, add_comm]
  rw [he]
  have hsum := sum_le_sum (fun (i : Fin m) (_ : i∈univ) =>
    mixture_square_le (a := ∑ y, w₀ y*(if x i=y i then 0 else 1))
      (b := ∑ y, w₁ y*(if x i=y i then 0 else 1)) hr hr1)
  apply (add_le_add (le_refl ((1-r)^2)) hsum).trans_eq
  simp only [sum_add_distrib, ← mul_sum, mismatchCost]
  ring
lemma cubeAverage_cons_bool {m : ℕ} (b : Bool)
    (f : (Fin (m+1) → Bool) → ℝ) :
    cubeAverage f = (cubeAverage (fun x => f (Fin.cons b x))+
      cubeAverage (fun x => f (Fin.cons (!b) x)))/2 := by
  cases b
  · exact cubeAverage_cons f
  · rw [cubeAverage_cons]
    simp only [Bool.not_true]
    congr 1
    exact add_comm _ _
lemma cubeAverage_lift_mixture_exp_le {m : ℕ} (b : Bool)
    (Q₀ Q₁ : (Fin m → Bool) → (Fin m → Bool) → ℝ)
    (h₀ : ∀ x, (∑ y, Q₀ x y)=1) (h₁ : ∀ x, (∑ y, Q₁ x y)=1)
    {r u v : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 < u) (hv : 0 < v)
    (hb₀ : cubeAverage (fun x => Real.exp (mismatchCost x (Q₀ x)/4)) ≤ u)
    (hb₁ : cubeAverage (fun x => Real.exp (mismatchCost x (Q₁ x)/4)) ≤ v) :
    cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons (!b) x) (fun y =>
      (1-r)*(if y 0=b then Q₀ x (Fin.tail y) else 0)+
      r*(if y 0=(!b) then Q₁ x (Fin.tail y) else 0))/4)) ≤
    Real.exp ((1-r)^2/4)*Real.exp ((1-r)*Real.log u+r*Real.log v) := by
  calc
    _ ≤ cubeAverage (fun x => Real.exp ((1-r)^2/4)*
        Real.exp ((1-r)*(mismatchCost x (Q₀ x)/4)+r*(mismatchCost x (Q₁ x)/4))) := by
      apply cubeAverage_mono
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mismatchCost_lift_mixture_le b x (Q₀ x) (Q₁ x) (h₀ x) (h₁ x) hr hr1
      linarith
    _ = Real.exp ((1-r)^2/4)*cubeAverage
        (fun x => Real.exp ((1-r)*(mismatchCost x (Q₀ x)/4)+r*(mismatchCost x (Q₁ x)/4))) :=
      cubeAverage_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cubeAverage_exponential_holder _ _ hr hr1 hu hv hb₀ hb₁) (Real.exp_pos _).le
lemma transport_step_nonempty {m : ℕ} (A : Finset (Fin (m+1) → Bool))
    (B₀ B₁ : Finset (Fin m → Bool)) (b : Bool)
    (hA₀ : ∀ y∈B₀, Fin.cons b y∈A) (hA₁ : ∀ y∈B₁, Fin.cons (!b) y∈A)
    (Q₀ Q₁ : (Fin m → Bool) → (Fin m → Bool) → ℝ)
    (hw₀ : ∀ x, supportedWeight B₀ (Q₀ x))
    (hw₁ : ∀ x, supportedWeight B₁ (Q₁ x))
    {p₀ p₁ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : p₁ ≤ p₀)
    (hb₀ : cubeAverage (fun x => Real.exp (mismatchCost x (Q₀ x)/4)) ≤ p₀⁻¹)
    (hb₁ : cubeAverage (fun x => Real.exp (mismatchCost x (Q₁ x)/4)) ≤ p₁⁻¹) :
    ∃ Q : (Fin (m+1) → Bool) → (Fin (m+1) → Bool) → ℝ,
      (∀ x, supportedWeight A (Q x)) ∧
      cubeAverage (fun x => Real.exp (mismatchCost x (Q x)/4)) ≤ 2/(p₀+p₁) := by
  let r : ℝ := p₁/p₀
  have hr : 0 ≤ r := (div_pos hp₁ hp₀).le
  have hr1 : r ≤ 1 := (div_le_one hp₀).mpr hp
  have hnot : (!b) ≠ b := by cases b <;> decide
  let Q : (Fin (m+1) → Bool) → (Fin (m+1) → Bool) → ℝ := fun x y =>
    if x 0=b then (if y 0=b then Q₀ (Fin.tail x) (Fin.tail y) else 0)
    else (1-r)*(if y 0=b then Q₀ (Fin.tail x) (Fin.tail y) else 0)+
      r*(if y 0=(!b) then Q₁ (Fin.tail x) (Fin.tail y) else 0)
  refine ⟨Q, ?_, ?_⟩
  · intro x
    by_cases hx : x 0=b
    · simp only [Q, hx, ite_true]
      exact supportedWeight_lift A B₀ b (Q₀ (Fin.tail x)) (hw₀ _) hA₀
    · simp only [Q, hx, ite_false]
      exact supportedWeight_mixture A _ _
        (supportedWeight_lift A B₀ b (Q₀ (Fin.tail x)) (hw₀ _) hA₀)
        (supportedWeight_lift A B₁ (!b) (Q₁ (Fin.tail x)) (hw₁ _) hA₁) hr hr1
  · have he₀ : cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons b x) (Q (Fin.cons b x))/4)) ≤ p₀⁻¹ := by
      simpa only [Q, Fin.cons_zero, ite_true, Fin.tail_cons,
        mismatchCost_lift b b _ _ (hw₀ _).2.1, ite_true, add_zero] using hb₀
    have he₁ : cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons (!b) x) (Q (Fin.cons (!b) x))/4)) ≤
        Real.exp ((1-r)^2/4)*Real.exp ((1-r)*Real.log (p₀⁻¹)+r*Real.log (p₁⁻¹)) := by
      simp only [Q, Fin.cons_zero, hnot, ite_false, Fin.tail_cons]
      exact cubeAverage_lift_mixture_exp_le b Q₀ Q₁
        (fun x => (hw₀ x).2.1) (fun x => (hw₁ x).2.1) hr hr1
        (inv_pos.mpr hp₀) (inv_pos.mpr hp₁) hb₀ hb₁
    calc
      _ = (cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons b x) (Q (Fin.cons b x))/4))+
          cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons (!b) x) (Q (Fin.cons (!b) x))/4)))/2 :=
        cubeAverage_cons_bool b _
      _ ≤ (p₀⁻¹+Real.exp ((1-r)^2/4)*Real.exp ((1-r)*Real.log (p₀⁻¹)+r*Real.log (p₁⁻¹)))/2 := by
        gcongr
      _ ≤ 2/(p₀+p₁) := two_fiber_average_bound hp₀ hp₁ hp
lemma transport_step_empty {m : ℕ} (A : Finset (Fin (m+1) → Bool))
    (B : Finset (Fin m → Bool)) (b : Bool)
    (hA : ∀ y∈B, Fin.cons b y∈A)
    (Q₀ : (Fin m → Bool) → (Fin m → Bool) → ℝ)
    (hw₀ : ∀ x, supportedWeight B (Q₀ x))
    {p : ℝ} (hp : 0 < p)
    (hb : cubeAverage (fun x => Real.exp (mismatchCost x (Q₀ x)/4)) ≤ p⁻¹) :
    ∃ Q : (Fin (m+1) → Bool) → (Fin (m+1) → Bool) → ℝ,
      (∀ x, supportedWeight A (Q x)) ∧
      cubeAverage (fun x => Real.exp (mismatchCost x (Q x)/4)) ≤ 2/p := by
  have hnot : (!b) ≠ b := by cases b <;> decide
  let Q : (Fin (m+1) → Bool) → (Fin (m+1) → Bool) → ℝ := fun x y =>
    if y 0=b then Q₀ (Fin.tail x) (Fin.tail y) else 0
  refine ⟨Q, fun x => supportedWeight_lift A B b (Q₀ (Fin.tail x)) (hw₀ _) hA, ?_⟩
  have he₀ : cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons b x) (Q (Fin.cons b x))/4)) ≤ p⁻¹ := by
    simpa only [Q, Fin.tail_cons, mismatchCost_lift b b _ _ (hw₀ _).2.1,
      ite_true, add_zero] using hb
  have he₁ : cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons (!b) x) (Q (Fin.cons (!b) x))/4)) ≤
      Real.exp (1/4 : ℝ)*p⁻¹ := by
    simp only [Q, Fin.tail_cons, mismatchCost_lift b (!b) _ _ (hw₀ _).2.1,
      hnot, ite_false]
    have he : (fun x => Real.exp ((mismatchCost x (Q₀ x)+1)/4)) =
        (fun x => Real.exp (1/4 : ℝ)*Real.exp (mismatchCost x (Q₀ x)/4)) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, cubeAverage_mul]
    exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
  calc
    _ = (cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons b x) (Q (Fin.cons b x))/4))+
        cubeAverage (fun x => Real.exp (mismatchCost (Fin.cons (!b) x) (Q (Fin.cons (!b) x))/4)))/2 :=
      cubeAverage_cons_bool b _
    _ ≤ (p⁻¹+Real.exp (1/4 : ℝ)*p⁻¹)/2 := by gcongr
    _ ≤ (p⁻¹+3*p⁻¹)/2 := by
      gcongr
      exact empty_fiber_exp_bound
    _ = 2/p := by ring
theorem cube_transport_kernel (m : ℕ) (A : Finset (Fin m → Bool)) (hA : A.Nonempty) :
    ∃ Q : (Fin m → Bool) → (Fin m → Bool) → ℝ,
      (∀ x, supportedWeight A (Q x)) ∧
      cubeAverage (fun x => Real.exp (mismatchCost x (Q x)/4)) ≤
        (cubeAverage (fun y => if y∈A then 1 else 0))⁻¹ := by
  induction m with
  | zero =>
      have hall (y : Fin 0 → Bool) : y∈A := by
        obtain ⟨a, ha⟩ := hA
        simpa only [Subsingleton.elim y a] using ha
      refine ⟨fun _ _ => 1, ?_, ?_⟩
      · intro x
        refine ⟨fun _ => zero_le_one, ?_, ?_⟩
        · simp
        · intro y hy
          exact (hy (hall y)).elim
      · have hind : (fun y : Fin 0 → Bool => if y∈A then (1 : ℝ) else 0) =
            (fun _ => 1) := by
          funext y
          simp only [hall y, ite_true]
        simp only [mismatchCost_zero_dimension, zero_div, Real.exp_zero,
          hind, cubeAverage_const, inv_one, le_refl]
  | succ m ih =>
      let B : Bool → Finset (Fin m → Bool) := fun b => univ.filter (fun y => Fin.cons b y∈A)
      have hstep (b : Bool)
          (hp : cubeAverage (fun y => if y∈B (!b) then 1 else 0) ≤
            cubeAverage (fun y => if y∈B b then 1 else 0)) :
          ∃ Q : (Fin (m+1) → Bool) → (Fin (m+1) → Bool) → ℝ,
            (∀ x, supportedWeight A (Q x)) ∧
            cubeAverage (fun x => Real.exp (mismatchCost x (Q x)/4)) ≤
              (cubeAverage (fun y => if y∈A then 1 else 0))⁻¹ := by
        let p₀ : ℝ := cubeAverage (fun y => if y∈B b then 1 else 0)
        let p₁ : ℝ := cubeAverage (fun y => if y∈B (!b) then 1 else 0)
        have hmass : cubeAverage (fun y => if y∈A then (1 : ℝ) else 0) = (p₀+p₁)/2 := by
          simpa only [p₀, p₁, B, mem_filter, mem_univ, true_and] using
            cubeAverage_cons_bool b (fun y => if y∈A then (1 : ℝ) else 0)
        have hp₀ : 0 < p₀ := by
          have hpos := cubeAverage_indicator_pos hA
          rw [hmass] at hpos
          change p₁ ≤ p₀ at hp
          linarith
        obtain ⟨Q₀, hw₀, hb₀⟩ := ih (B b) (nonempty_of_cubeAverage_indicator_pos hp₀)
        have hA₀ : ∀ y∈B b, Fin.cons b y∈A := fun y hy => (mem_filter.mp hy).2
        have hA₁ : ∀ y∈B (!b), Fin.cons (!b) y∈A := fun y hy => (mem_filter.mp hy).2
        by_cases hB₁ : (B (!b)).Nonempty
        · have hp₁ : 0 < p₁ := cubeAverage_indicator_pos hB₁
          obtain ⟨Q₁, hw₁, hb₁⟩ := ih (B (!b)) hB₁
          obtain ⟨Q, hw, hb⟩ := transport_step_nonempty A (B b) (B (!b)) b hA₀ hA₁
            Q₀ Q₁ hw₀ hw₁ hp₀ hp₁ hp hb₀ hb₁
          refine ⟨Q, hw, hb.trans_eq ?_⟩
          rw [hmass, inv_div]
        · have hp₁ : p₁=0 := by
            have he : B (!b)=∅ := not_nonempty_iff_eq_empty.mp hB₁
            dsimp [p₁]
            simp [he, cubeAverage_const]
          obtain ⟨Q, hw, hb⟩ := transport_step_empty A (B b) b hA₀ Q₀ hw₀ hp₀ hb₀
          refine ⟨Q, hw, hb.trans_eq ?_⟩
          rw [hmass, hp₁, add_zero, inv_div]
      by_cases hp : cubeAverage (fun y => if y∈B true then (1 : ℝ) else 0) ≤
          cubeAverage (fun y => if y∈B false then 1 else 0)
      · exact hstep false hp
      · exact hstep true (le_of_not_ge hp)
end Fluctuations.FiniteCubeConvexTransport
end
end

section
noncomputable section
open Finset Classical
open scoped BigOperators
namespace Fluctuations.FiniteCubeConvexTransport
lemma sign_coordinate_difference {m : ℕ} (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) (hw : (∑ y, w y)=1) (i : Fin m) :
    (if x i then (1 : ℝ) else -1)-∑ y, w y*(if y i then (1 : ℝ) else -1) =
      2*(if x i then (1 : ℝ) else -1)*(∑ y, w y*(if x i=y i then 0 else 1)) := by
  have he (y : Fin m → Bool) :
      (if x i then (1 : ℝ) else -1)-(if y i then (1 : ℝ) else -1) =
        2*(if x i then (1 : ℝ) else -1)*(if x i=y i then (0 : ℝ) else 1) := by
    cases hxi : x i <;> cases hyi : y i <;> norm_num
  calc
    _ = ∑ y, w y*((if x i then (1 : ℝ) else -1)-(if y i then (1 : ℝ) else -1)) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw, one_mul]
    _ = ∑ y, 2*(if x i then (1 : ℝ) else -1)*(w y*(if x i=y i then 0 else 1)) := by
      apply sum_congr rfl
      intro y _
      rw [he y]
      ring
    _ = _ := (mul_sum _ _ _).symm
lemma sign_distance_squared {m : ℕ} (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) (hw : (∑ y, w y)=1) :
    ‖(WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin m))-
      ∑ y, w y • WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)‖^2 =
      4*mismatchCost x w := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have he (i : Fin m) :
      (∑ y, w y • (WithLp.toLp 2 (fun j => if y j then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin m))) i =
        ∑ y, w y*(if y i then (1 : ℝ) else -1) := by
    change (WithLp.ofLp (∑ y, w y • WithLp.toLp 2 (fun j => if y j then (1 : ℝ) else -1))) i = _
    rw [WithLp.ofLp_sum]
    simp
  simp only [PiLp.sub_apply, he, sign_coordinate_difference x w hw]
  rw [mismatchCost, mul_sum]
  apply sum_congr rfl
  intro i _
  cases hxi : x i <;> norm_num <;> ring
lemma sign_distance_eq {m : ℕ} (x : Fin m → Bool)
    (w : (Fin m → Bool) → ℝ) (hw : (∑ y, w y)=1) :
    ‖(WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin m))-
      ∑ y, w y • WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)‖ =
      2*Real.sqrt (mismatchCost x w) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sign_distance_squared x w hw]
  nlinarith [Real.sq_sqrt (mismatchCost_nonneg x w)]
lemma convex_lipschitz_geometry {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L a : ℝ}
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (A : Finset (Fin m → Bool))
    (hA : ∀ y∈A, F (WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)) ≤ a)
    (x : Fin m → Bool) (w : (Fin m → Bool) → ℝ) (hw : supportedWeight A w) :
    F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))-a ≤
      2*L*Real.sqrt (mismatchCost x w) := by
  let e : (Fin m → Bool) → EuclideanSpace ℝ (Fin m) :=
    fun y => WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)
  let z : EuclideanSpace ℝ (Fin m) := ∑ y, w y • e y
  have hz : F z ≤ a := by
    calc
      _ ≤ ∑ y, w y*F (e y) := by
        simpa only [smul_eq_mul] using
          hF.map_sum_le (fun y (_ : y∈univ) => hw.1 y) hw.2.1
            (fun y (_ : y∈univ) => Set.mem_univ (e y))
      _ ≤ ∑ y, w y*a := by
        apply sum_le_sum
        intro y _
        by_cases hy : y∈A
        · exact mul_le_mul_of_nonneg_left (hA y hy) (hw.1 y)
        · simp only [hw.2.2 y hy, zero_mul, le_refl]
      _ = a := by rw [← sum_mul, hw.2.1, one_mul]
  have hd : ‖e x-z‖=2*Real.sqrt (mismatchCost x w) := sign_distance_eq x w hw.2.1
  have hh := (le_abs_self (F (e x)-F z)).trans (hLip (e x) z)
  rw [hd] at hh
  dsimp only [e] at hh
  nlinarith
lemma convex_cost_lower {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L a t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (A : Finset (Fin m → Bool))
    (hA : ∀ y∈A, F (WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)) ≤ a)
    (x : Fin m → Bool) (w : (Fin m → Bool) → ℝ) (hw : supportedWeight A w)
    (hx : a+t ≤ F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))) :
    t^2/(16*L^2) ≤ mismatchCost x w/4 := by
  have hg := convex_lipschitz_geometry F hF hLip A hA x w hw
  have hh : t ≤ 2*L*Real.sqrt (mismatchCost x w) := by linarith
  have hs : t^2 ≤ 4*L^2*mismatchCost x w := by
    calc
      _ ≤ (2*L*Real.sqrt (mismatchCost x w))^2 := sq_le_sq₀ ht (by positivity) |>.mpr hh
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (mismatchCost_nonneg x w)]
        ring
  apply (div_le_iff₀ (by positivity : 0 < 16*L^2)).mpr
  nlinarith
lemma cube_exponential_markov {m : ℕ} (f : (Fin m → Bool) → ℝ)
    (B : Finset (Fin m → Bool)) (t : ℝ) (hB : ∀ x∈B, t ≤ f x) :
    cubeAverage (fun x => if x∈B then 1 else 0) ≤
      Real.exp (-t)*cubeAverage (fun x => Real.exp (f x)) := by
  have hm : Real.exp t*cubeAverage (fun x => if x∈B then 1 else 0) ≤
      cubeAverage (fun x => Real.exp (f x)) := by
    rw [← cubeAverage_mul]
    apply cubeAverage_mono
    intro x
    by_cases hx : x∈B
    · simp only [hx, ite_true, mul_one]
      exact Real.exp_le_exp.mpr (hB x hx)
    · simp only [hx, ite_false, mul_zero]
      exact (Real.exp_pos _).le
  calc
    _ = Real.exp (-t)*(Real.exp t*cubeAverage (fun x => if x∈B then 1 else 0)) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
theorem convex_sublevel_separation {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L a t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (A B : Finset (Fin m → Bool))
    (hA : ∀ y∈A, F (WithLp.toLp 2 (fun i => if y i then (1 : ℝ) else -1)) ≤ a)
    (hB : ∀ x∈B, a+t ≤ F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))) :
    cubeAverage (fun y => if y∈A then 1 else 0)*
      cubeAverage (fun x => if x∈B then 1 else 0) ≤ Real.exp (-t^2/(16*L^2)) := by
  by_cases hn : A.Nonempty
  · obtain ⟨Q, hw, hQ⟩ := cube_transport_kernel m A hn
    have hm := cube_exponential_markov (fun x => mismatchCost x (Q x)/4) B
      (t^2/(16*L^2)) (fun x hx => convex_cost_lower F hF hL ht hLip A hA x (Q x) (hw x) (hB x hx))
    have hh := hm.trans (mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le)
    have hp := cubeAverage_indicator_pos hn
    calc
      _ ≤ cubeAverage (fun y => if y∈A then 1 else 0)*
          (Real.exp (-(t^2/(16*L^2)))*(cubeAverage (fun y => if y∈A then 1 else 0))⁻¹) :=
        mul_le_mul_of_nonneg_left hh hp.le
      _ = _ := by rw [mul_left_comm, mul_inv_cancel₀ hp.ne', mul_one]; congr 1; ring
  · have he : A=∅ := not_nonempty_iff_eq_empty.mp hn
    simpa [he, cubeAverage_const] using (Real.exp_pos (-t^2/(16*L^2))).le
theorem convex_upper_median_tail {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L M t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (hMedian : (1/2 : ℝ) ≤ cubeAverage (fun x =>
      if F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)) ≤ M then 1 else 0)) :
    cubeAverage (fun x => if M+t ≤ F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))
      then 1 else 0) ≤ 2*Real.exp (-t^2/(16*L^2)) := by
  let e : (Fin m → Bool) → EuclideanSpace ℝ (Fin m) :=
    fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)
  let A : Finset (Fin m → Bool) := univ.filter (fun x => F (e x)≤M)
  let B : Finset (Fin m → Bool) := univ.filter (fun x => M+t≤F (e x))
  have hs := convex_sublevel_separation F hF hL ht hLip A B
    (fun _ hy => (mem_filter.mp hy).2) (fun _ hx => (mem_filter.mp hx).2)
  simp only [A, B, mem_filter, mem_univ, true_and] at hs
  have hp : 0 ≤ cubeAverage (fun x => if M+t≤F (e x) then (1 : ℝ) else 0) :=
    cubeAverage_nonneg (fun x => by split_ifs <;> norm_num)
  dsimp only [e] at hs hp
  nlinarith
theorem convex_lower_median_tail {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L M t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (hMedian : (1/2 : ℝ) ≤ cubeAverage (fun x =>
      if M ≤ F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)) then 1 else 0)) :
    cubeAverage (fun x => if F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)) ≤ M-t
      then 1 else 0) ≤ 2*Real.exp (-t^2/(16*L^2)) := by
  let e : (Fin m → Bool) → EuclideanSpace ℝ (Fin m) :=
    fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)
  let A : Finset (Fin m → Bool) := univ.filter (fun x => F (e x)≤M-t)
  let B : Finset (Fin m → Bool) := univ.filter (fun x => M≤F (e x))
  have hs := convex_sublevel_separation F hF hL ht hLip A B
    (fun _ hy => (mem_filter.mp hy).2) (fun _ hx => by
      have h := (mem_filter.mp hx).2
      linarith)
  simp only [A, B, mem_filter, mem_univ, true_and] at hs
  have hp : 0 ≤ cubeAverage (fun x => if F (e x)≤M-t then (1 : ℝ) else 0) :=
    cubeAverage_nonneg (fun x => by split_ifs <;> norm_num)
  dsimp only [e] at hs hp
  nlinarith
theorem exists_cube_median {m : ℕ} (f : (Fin m → Bool) → ℝ) :
    ∃ M : ℝ,
      (1/2 : ℝ) ≤ cubeAverage (fun x => if f x≤M then 1 else 0) ∧
      (1/2 : ℝ) ≤ cubeAverage (fun x => if M≤f x then 1 else 0) := by
  let T : Finset (Fin m → Bool) := univ.filter (fun z =>
    (1/2 : ℝ) ≤ cubeAverage (fun x => if f x≤f z then 1 else 0))
  obtain ⟨z, _, hz⟩ := exists_max_image (univ : Finset (Fin m → Bool)) f univ_nonempty
  have hzT : z∈T := by
    simp only [T, mem_filter, mem_univ, true_and]
    have he : (fun x => if f x≤f z then (1 : ℝ) else 0) = fun _ => 1 := by
      funext x
      simp [hz x (mem_univ x)]
    rw [he, cubeAverage_const]
    norm_num
  obtain ⟨a, ha, hmin⟩ := exists_min_image T f ⟨z, hzT⟩
  refine ⟨f a, (mem_filter.mp ha).2, ?_⟩
  by_contra hupper
  have hupper' : cubeAverage (fun x => if f a≤f x then (1 : ℝ) else 0)<1/2 :=
    lt_of_not_ge hupper
  let S : Finset (Fin m → Bool) := univ.filter (fun x => f x<f a)
  have hpartition : cubeAverage (fun x => if x∈S then (1 : ℝ) else 0)+
      cubeAverage (fun x => if f a≤f x then (1 : ℝ) else 0)=1 := by
    rw [← cubeAverage_add]
    have he : (fun x => (if x∈S then (1 : ℝ) else 0)+
        (if f a≤f x then (1 : ℝ) else 0)) = fun _ => 1 := by
      funext x
      simp only [S, mem_filter, mem_univ, true_and]
      split_ifs <;> linarith
    rw [he, cubeAverage_const]
  have hS : (1/2 : ℝ)<cubeAverage (fun x => if x∈S then (1 : ℝ) else 0) := by
    linarith
  obtain ⟨b, hb, hmax⟩ := exists_max_image S f
    (nonempty_of_cubeAverage_indicator_pos (by linarith [hS]))
  have hbT : b∈T := by
    simp only [T, mem_filter, mem_univ, true_and]
    have hle := cubeAverage_mono (f := fun x => if x∈S then (1 : ℝ) else 0)
      (g := fun x => if f x≤f b then (1 : ℝ) else 0) (fun x => by
        by_cases hx : x∈S
        · simp [hx, hmax x hx]
        · simp only [hx, ite_false]
          split_ifs <;> norm_num)
    linarith
  have hsmall := (mem_filter.mp hb).2
  have hlarge := hmin b hbT
  exact (not_lt_of_ge hlarge) hsmall
theorem convex_absolute_median_tail {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L M t : ℝ} (hL : 0<L) (ht : 0≤t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖)
    (hLower : (1/2 : ℝ) ≤ cubeAverage (fun x =>
      if F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))≤M then 1 else 0))
    (hUpper : (1/2 : ℝ) ≤ cubeAverage (fun x =>
      if M≤F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1)) then 1 else 0)) :
    cubeAverage (fun x => if t≤|F (WithLp.toLp 2
      (fun i => if x i then (1 : ℝ) else -1))-M| then 1 else 0) ≤
      4*Real.exp (-t^2/(16*L^2)) := by
  have hu := convex_upper_median_tail F hF hL ht hLip hLower
  have hl := convex_lower_median_tail F hF hL ht hLip hUpper
  have hle := cubeAverage_mono (f := fun x => if t≤|F (WithLp.toLp 2
      (fun i => if x i then (1 : ℝ) else -1))-M| then (1 : ℝ) else 0)
    (g := fun x => (if M+t≤F (WithLp.toLp 2
      (fun i => if x i then (1 : ℝ) else -1)) then (1 : ℝ) else 0)+
      (if F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))≤M-t
        then (1 : ℝ) else 0)) (fun x => by
      split_ifs with h₁ h₂ h₃ <;> try norm_num
      exfalso
      have ha : |F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))-M|<t :=
        abs_lt.mpr (by constructor <;> linarith)
      exact (not_lt_of_ge h₁) ha)
  rw [cubeAverage_add] at hle
  linarith
lemma finite_slab_bound (N : ℕ) {u : ℝ} (hu : u≤(N : ℝ)+1) :
    u≤1+∑ k∈range N, if (k : ℝ)+1≤u then (1 : ℝ) else 0 := by
  induction N with
  | zero => simpa using hu
  | succ N ih =>
    rw [sum_range_succ]
    by_cases h : u≤(N : ℝ)+1
    · have hh := ih h
      split_ifs <;> linarith
    · have hsmall : ∀ k∈range N, (k : ℝ)+1≤u := by
        intro k hk
        have hk' : (k : ℝ)<N := by exact_mod_cast mem_range.mp hk
        linarith
      have he : (∑ k∈range N, if (k : ℝ)+1≤u then (1 : ℝ) else 0)=(N : ℝ) := by
        calc
          _ = ∑ _k∈range N, (1 : ℝ) := sum_congr rfl (fun k hk => by simp [hsmall k hk])
          _ = (N : ℝ) := by simp
      have hlast : (N : ℝ)+1≤u := by linarith
      simp only [he, hlast, ite_true]
      push_cast at hu
      linarith
lemma cubeAverage_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin m → Bool) → ℝ) :
    cubeAverage (fun x => ∑ i∈s, f i x)=∑ i∈s, cubeAverage (f i) := by
  unfold cubeAverage
  rw [sum_comm, mul_sum]
theorem cube_mean_abs_of_median_tail {m : ℕ} (f : (Fin m → Bool) → ℝ)
    {L M : ℝ} (hL : 0<L)
    (htail : ∀ t : ℝ, 0≤t → cubeAverage (fun x => if t≤|f x-M| then 1 else 0) ≤
      4*Real.exp (-t^2/(16*L^2))) :
    cubeAverage (fun x => |f x-M|) ≤ 36*L := by
  let u : (Fin m → Bool) → ℝ := fun x => |f x-M|/(4*L)
  obtain ⟨a, _, ha⟩ := exists_max_image (univ : Finset (Fin m → Bool)) u univ_nonempty
  obtain ⟨N, hN⟩ := exists_nat_ge (u a)
  have hbound := cubeAverage_mono (f := u)
    (g := fun x => 1+∑ k∈range N, if (k : ℝ)+1≤u x then (1 : ℝ) else 0)
    (fun x => finite_slab_bound N (by have hh := ha x (mem_univ x); linarith))
  rw [cubeAverage_add, cubeAverage_const, cubeAverage_sum] at hbound
  have htail' (k : ℕ) : cubeAverage (fun x => if (k : ℝ)+1≤u x then (1 : ℝ) else 0) ≤
      4*(1/2 : ℝ)^k := by
    have hevent (x : Fin m → Bool) : ((k : ℝ)+1≤u x) ↔ 4*L*((k : ℝ)+1)≤|f x-M| := by
      dsimp [u]
      rw [le_div_iff₀ (by positivity)]
      constructor <;> intro h <;> nlinarith
    have he : -(4*L*((k : ℝ)+1))^2/(16*L^2) = -((k : ℝ)+1)^2 := by
      field_simp
      ring
    have ht := htail (4*L*((k : ℝ)+1)) (by positivity)
    simp only [← hevent, he] at ht
    have hexp : Real.exp (-((k : ℝ)+1)^2) ≤ (1/2 : ℝ)^k := by
      calc
        _ ≤ Real.exp ((k : ℝ)*(-1)) := Real.exp_le_exp.mpr (by
          have hk : 0≤(k : ℝ) := Nat.cast_nonneg k
          nlinarith [sq_nonneg (k : ℝ)])
        _ = Real.exp (-1)^k := Real.exp_nat_mul (-1) k
        _ ≤ (1/2 : ℝ)^k := by
          apply pow_le_pow_left₀ (Real.exp_pos _).le
          rw [Real.exp_neg]
          have hp := Real.add_one_le_exp (1 : ℝ)
          simpa only [one_div] using one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ)<2) (show 2≤Real.exp 1 by linarith)
    exact ht.trans (by nlinarith)
  have hsum := sum_le_sum (fun k (_ : k∈range N) => htail' k)
  rw [← mul_sum] at hsum
  have hu : cubeAverage u≤9 := by
    have hg := sum_geometric_two_le N
    linarith
  have he : (fun x => |f x-M|) = fun x => (4*L)*u x := by
    funext x
    dsimp [u]
    field_simp
  rw [he, cubeAverage_mul]
  nlinarith
lemma abs_cubeAverage_le {m : ℕ} (f : (Fin m → Bool) → ℝ) :
    |cubeAverage f|≤cubeAverage (fun x => |f x|) := by
  unfold cubeAverage
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
lemma cube_mean_median_distance {m : ℕ} (f : (Fin m → Bool) → ℝ)
    {L M : ℝ} (h : cubeAverage (fun x => |f x-M|)≤36*L) :
    |cubeAverage f-M|≤36*L := by
  have he : cubeAverage (fun x => f x-M)=cubeAverage f-M := by
    simp only [sub_eq_add_neg, cubeAverage_add, cubeAverage_const]
  rw [← he]
  exact (abs_cubeAverage_le _).trans h
theorem cube_centered_tail_large {m : ℕ} (f : (Fin m → Bool) → ℝ)
    {L M t : ℝ} (hL : 0<L) (ht : 72*L≤t)
    (htail : ∀ s : ℝ, 0≤ s → cubeAverage (fun x => if s≤|f x-M| then 1 else 0) ≤
      4*Real.exp (-s^2/(16*L^2))) :
    cubeAverage (fun x => if t≤|f x-cubeAverage f| then 1 else 0) ≤
      4*Real.exp (-t^2/(64*L^2)) := by
  have hmean := cube_mean_median_distance f (cube_mean_abs_of_median_tail f hL htail)
  have hle := cubeAverage_mono (f := fun x => if t≤|f x-cubeAverage f| then (1 : ℝ) else 0)
    (g := fun x => if t/2≤|f x-M| then (1 : ℝ) else 0) (fun x => by
      split_ifs with hx hy <;> try norm_num
      exfalso
      have habs := abs_sub_le (f x) M (cubeAverage f)
      have hsym : |M-cubeAverage f|=|cubeAverage f-M| := abs_sub_comm _ _
      rw [hsym] at habs
      linarith)
  have hhalf : 0≤t/2 := by linarith
  have he : -(t/2)^2/(16*L^2) = -t^2/(64*L^2) := by ring
  exact hle.trans (by simpa only [he] using htail (t/2) hhalf)
theorem convex_centered_tail {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    {L t : ℝ} (hL : 0<L) (ht : 0≤t)
    (hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖) :
    cubeAverage (fun x => if t≤|F (WithLp.toLp 2
      (fun i => if x i then (1 : ℝ) else -1))-
      cubeAverage (fun y => F (WithLp.toLp 2
        (fun i => if y i then (1 : ℝ) else -1)))| then 1 else 0) ≤
      (4*Real.exp 81)*Real.exp (-t^2/(64*L^2)) := by
  let f : (Fin m → Bool) → ℝ := fun x =>
    F (WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else -1))
  obtain ⟨M, hlo, hhi⟩ := exists_cube_median f
  have htail (s : ℝ) (hs : 0≤ s) := convex_absolute_median_tail F hF hL hs hLip hlo hhi
  change cubeAverage (fun x => if t≤|f x-cubeAverage f| then (1 : ℝ) else 0)≤_
  by_cases hlarge : 72*L≤t
  · have hb := cube_centered_tail_large f hL hlarge htail
    have hexp := Real.one_le_exp (show (0 : ℝ)≤81 by norm_num)
    have hp := Real.exp_pos (-t^2/(64*L^2))
    nlinarith
  · have hone : cubeAverage (fun x => if t≤|f x-cubeAverage f| then (1 : ℝ) else 0)≤1 := by
      calc
        _ ≤ cubeAverage (fun _ : Fin m → Bool => (1 : ℝ)) :=
          cubeAverage_mono (fun x => by split_ifs <;> norm_num)
        _ = 1 := cubeAverage_const m 1
    have hden : 0<64*L^2 := by positivity
    have hsquare : t^2≤81*(64*L^2) := by
      have htl : t≤72*L := le_of_not_ge hlarge
      nlinarith
    have he : 0≤81+(-t^2/(64*L^2)) := by
      have hd := (div_le_iff₀ hden).mpr hsquare
      rw [neg_div]
      linarith
    have hx := Real.one_le_exp he
    rw [Real.exp_add] at hx
    have hp := Real.exp_pos (81 : ℝ)
    have hq := Real.exp_pos (-t^2/(64*L^2))
    nlinarith
end Fluctuations.FiniteCubeConvexTransport
end
end

section
noncomputable section
open Finset Classical Set
open scoped BigOperators
namespace Fluctuations.SignClippedConvexity
lemma weighted_relu_convex {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (w s : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (δ : ℝ) (hδ : 0 < δ) :
    ConvexOn ℝ univ (fun z : EuclideanSpace ℝ (Fin m) =>
      ∑ i, w i*max 0 ((∑ j, v i j*z j)+s i)/δ) := by
  refine ⟨convex_univ,?_⟩
  intro z _ z' _ a b ha hb hab
  simp only [smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply sum_le_sum
  intro i _
  have he : (∑ j, v i j*(a • z+b • z') j)+s i =
      a*((∑ j, v i j*z j)+s i)+b*((∑ j, v i j*z' j)+s i) := by
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,mul_add,sum_add_distrib]
    simp_rw [mul_left_comm (v i _) a,mul_left_comm (v i _) b]
    rw [← mul_sum,← mul_sum]
    linear_combination -(s i)*hab
  have hmax : max 0 ((∑ j, v i j*(a • z+b • z') j)+s i) ≤
      a*max 0 ((∑ j, v i j*z j)+s i)+b*max 0 ((∑ j, v i j*z' j)+s i) := by
    apply max_le
    · positivity
    · rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (hw i)) hδ.le
  convert! h using 1; ring
lemma weighted_relu_lipschitz {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (w s : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (M : ℝ) (hM : 0 ≤ M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ z z' : EuclideanSpace ℝ (Fin m),
      |(∑ i, w i*max 0 ((∑ j, v i j*z j)+s i)/δ) -
        ∑ i, w i*max 0 ((∑ j, v i j*z' j)+s i)/δ| ≤
          (Real.sqrt ((N : ℝ)*M)/δ)*‖z-z'‖ := by
  intro z z'
  let d : Fin N → ℝ := fun i => ∑ j, v i j*(z j-z' j)
  have hd (i : Fin N) : ((∑ j, v i j*z j)+s i)-((∑ j, v i j*z' j)+s i) = d i := by
    dsimp only [d]
    simp only [mul_sub,sum_sub_distrib]
    ring
  have hpiece (i : Fin N) : |w i*max 0 ((∑ j, v i j*z j)+s i)/δ -
      w i*max 0 ((∑ j, v i j*z' j)+s i)/δ| ≤ |d i|/δ := by
    rw [← sub_div,← mul_sub,abs_div,abs_mul,abs_of_nonneg (hw i).1,abs_of_pos hδ]
    apply div_le_div_of_nonneg_right _ hδ.le
    have hr : |max 0 ((∑ j, v i j*z j)+s i)-max 0 ((∑ j, v i j*z' j)+s i)| ≤ |d i| := by
      have hr := abs_max_sub_max_le_abs
        ((∑ j, v i j*z j)+s i) ((∑ j, v i j*z' j)+s i) 0
      rw [max_comm _ 0,max_comm _ 0,hd] at hr
      exact hr
    exact (mul_le_mul_of_nonneg_left hr (hw i).1).trans
      (by nlinarith [(hw i).2,abs_nonneg (d i)])
  have hq : (∑ i, |d i|)^2 ≤ (N : ℝ)*(M*‖z-z'‖^2) := by
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _i : Fin N => (1 : ℝ)) (fun i => |d i|)
    simp only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sq_abs] at hcs
    have hf := hframe (fun j => z j-z' j)
    have he : (∑ j, (z j-z' j)^2) = ‖z-z'‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [he] at hf
    exact hcs.trans (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg N))
  have hsum : (∑ i, |d i|) ≤ Real.sqrt ((N : ℝ)*M)*‖z-z'‖ := by
    have hsq := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hM)
    have hnon : 0 ≤ ∑ i, |d i| := sum_nonneg (fun _ _ => abs_nonneg _)
    have hsprod : (Real.sqrt ((N : ℝ)*M)*‖z-z'‖)^2 = (N : ℝ)*(M*‖z-z'‖^2) := by
      rw [mul_pow,hsq]; ring
    exact (sq_le_sq₀ hnon (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      (hq.trans_eq hsprod.symm)
  calc
    _ ≤ ∑ i, |w i*max 0 ((∑ j, v i j*z j)+s i)/δ -
        w i*max 0 ((∑ j, v i j*z' j)+s i)/δ| := by
      rw [← sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |d i|/δ := sum_le_sum (fun i _ => hpiece i)
    _ = (∑ i, |d i|)/δ := (sum_div ..).symm
    _ ≤ (Real.sqrt ((N : ℝ)*M)*‖z-z'‖)/δ := div_le_div_of_nonneg_right hsum hδ.le
    _ = _ := by ring
lemma weighted_relu_centered_tail {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (w s : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (M : ℝ) (hM : 0 < M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t) :
    let f : (Fin m → Bool) → ℝ := fun x =>
      ∑ i, w i*max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+s i)/δ
    FiniteCubeConvexTransport.cubeAverage (fun x => if t ≤ |f x-FiniteCubeConvexTransport.cubeAverage f|
      then 1 else 0) ≤ (4*Real.exp 81)*Real.exp (-(t^2*δ^2)/(64*((N : ℝ)+1)*M)) := by
  let F : EuclideanSpace ℝ (Fin m) → ℝ := fun z =>
    ∑ i, w i*max 0 ((∑ j, v i j*z j)+s i)/δ
  let L := Real.sqrt (((N : ℝ)+1)*M)/δ
  have hL : 0 < L := by dsimp only [L]; positivity
  have hLip : ∀ z z', |F z-F z'| ≤ L*‖z-z'‖ := by
    intro z z'
    apply (weighted_relu_lipschitz v w s hw M hM.le hframe δ hδ z z').trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hδ.le
    exact Real.sqrt_le_sqrt (by nlinarith)
  have he := FiniteCubeConvexTransport.convex_centered_tail F
    (weighted_relu_convex v w s (fun i => (hw i).1) δ hδ) hL ht hLip
  have hexp : -t^2/(64*L^2) = -(t^2*δ^2)/(64*((N : ℝ)+1)*M) := by
    dsimp only [L]
    rw [div_pow,Real.sq_sqrt (by positivity : 0 ≤ ((N : ℝ)+1)*M)]
    field_simp
  simpa only [F,hexp] using he
lemma relu_neg_identity (x : ℝ) : max 0 (-x) = max 0 x-x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left (by linarith),max_eq_right h]; ring
  · rw [max_eq_right (by linarith),max_eq_left h]; ring
lemma clipped_sign_odd (δ x : ℝ) (hδ : 0 < δ) :
    (max 0 (-x+δ)-max 0 (-x-δ))/δ-1 =
      -((max 0 (x+δ)-max 0 (x-δ))/δ-1) := by
  rw [show -x+δ = -(x-δ) by ring,show -x-δ = -(x+δ) by ring,
    relu_neg_identity,relu_neg_identity]
  field_simp
  ring
lemma clipped_trapezoid_even (δ x : ℝ) :
    (max 0 (-x+2*δ)-max 0 (-x+δ)-max 0 (-x-δ)+max 0 (-x-2*δ))/δ =
      (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ := by
  rw [show -x+2*δ = -(x-2*δ) by ring,show -x+δ = -(x-δ) by ring,
    show -x-δ = -(x+δ) by ring,show -x-2*δ = -(x+2*δ) by ring]
  simp only [relu_neg_identity]
  ring
lemma clipped_scalar_bounds_nonneg (δ x : ℝ) (hδ : 0 < δ) (hx : 0 ≤ x) :
    let h := (max 0 (x+δ)-max 0 (x-δ))/δ-1
    let k := (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ
    0 ≤ k ∧ k ≤ 1 ∧ (|x| ≤ δ → k = 1) ∧
      (2*δ ≤ |x| → k = 0) ∧ |Real.sign x-h| ≤ k := by
  dsimp only
  rw [abs_of_nonneg hx]
  by_cases hsmall : x ≤ δ
  · have hh : (max 0 (x+δ)-max 0 (x-δ))/δ-1 = x/δ := by
      rw [max_eq_right (by linarith),max_eq_left (by linarith)]
      field_simp
      ring
    have hk : (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ = 1 := by
      rw [max_eq_right (by linarith),max_eq_right (by linarith),
        max_eq_left (by linarith),max_eq_left (by linarith)]
      field_simp
      ring
    rw [hh,hk]
    refine ⟨by norm_num,by norm_num,(fun _ => rfl),?_,?_⟩
    · intro h; exfalso; linarith
    · rcases eq_or_lt_of_le hx with hz | hp
      · rw [← hz]; simp
      · rw [Real.sign_of_pos hp,abs_of_nonneg (by
          have h : x/δ ≤ 1 := (div_le_iff₀ hδ).mpr (by simpa using hsmall)
          linarith)]
        linarith [div_nonneg hx hδ.le]
  · have hlarge : δ < x := lt_of_not_ge hsmall
    have hh : (max 0 (x+δ)-max 0 (x-δ))/δ-1 = 1 := by
      rw [max_eq_right (by linarith),max_eq_right (by linarith)]
      field_simp
      ring
    rw [hh,Real.sign_of_pos (by linarith : 0 < x)]
    by_cases hmid : x ≤ 2*δ
    · have hk : (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ = (2*δ-x)/δ := by
        rw [max_eq_right (by linarith),max_eq_right (by linarith),
          max_eq_right (by linarith),max_eq_left (by linarith)]
        ring
      rw [hk]
      refine ⟨div_nonneg (by linarith) hδ.le,(div_le_iff₀ hδ).mpr (by linarith),?_,?_,?_⟩
      · intro h; exfalso; linarith
      · intro h
        rw [show 2*δ-x = 0 by linarith,zero_div]
      · norm_num only [sub_self,abs_zero]
        exact div_nonneg (by linarith) hδ.le
    · have hk : (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ = 0 := by
        rw [max_eq_right (by linarith),max_eq_right (by linarith),
          max_eq_right (by linarith),max_eq_right (by linarith)]
        ring
      rw [hk]
      refine ⟨le_refl _,by norm_num,?_,(fun _ => rfl),by norm_num⟩
      intro h; exfalso; linarith
lemma clipped_scalar_bounds (δ x : ℝ) (hδ : 0 < δ) :
    let h := (max 0 (x+δ)-max 0 (x-δ))/δ-1
    let k := (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ
    0 ≤ k ∧ k ≤ 1 ∧ (|x| ≤ δ → k = 1) ∧
      (2*δ ≤ |x| → k = 0) ∧ |Real.sign x-h| ≤ k := by
  rcases le_total 0 x with hx | hx
  · exact clipped_scalar_bounds_nonneg δ x hδ hx
  · have he := clipped_scalar_bounds_nonneg δ (-x) hδ (by linarith)
    dsimp only at he ⊢
    rw [clipped_trapezoid_even δ x,clipped_sign_odd δ x hδ,Real.sign_neg,abs_neg] at he
    have ha (r s : ℝ) : |-r-(-s)| = |r-s| := by
      rw [show -r-(-s) = -(r-s) by ring,abs_neg]
    rw [ha] at he
    exact he
lemma clipped_count_bound {N : ℕ} (b x : Fin N → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (δ D B : ℝ) (hδ : 0 < δ)
    (hcount : |D-∑ i, b i*Real.sign (x i)| ≤ B+2*∑ i, if x i = 0 then (1 : ℝ) else 0) :
    |D| ≤ |∑ i, b i*((max 0 (x i+δ)-max 0 (x i-δ))/δ-1)| +
      3*∑ i, (max 0 (x i+2*δ)-max 0 (x i+δ)-max 0 (x i-δ)+max 0 (x i-2*δ))/δ+B := by
  let h (u : ℝ) := (max 0 (u+δ)-max 0 (u-δ))/δ-1
  let k (u : ℝ) := (max 0 (u+2*δ)-max 0 (u+δ)-max 0 (u-δ)+max 0 (u-2*δ))/δ
  have he : |(∑ i, b i*Real.sign (x i))-∑ i, b i*h (x i)| ≤ ∑ i, k (x i) := by
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i _
    rw [← mul_sub,abs_mul]
    have hp := clipped_scalar_bounds δ (x i) hδ
    change 0 ≤ k (x i) ∧ _ ∧ _ ∧ _ ∧ |Real.sign (x i)-h (x i)| ≤ k (x i) at hp
    exact (mul_le_mul_of_nonneg_left hp.2.2.2.2 (abs_nonneg (b i))).trans
      (by nlinarith [hb i,hp.1])
  have hz : (∑ i, if x i = 0 then (1 : ℝ) else 0) ≤ ∑ i, k (x i) := by
    apply sum_le_sum
    intro i _
    have hp := clipped_scalar_bounds δ (x i) hδ
    by_cases hi : x i = 0
    · rw [if_pos hi]
      have hk := hp.2.2.1 (by rw [hi]; simpa using hδ.le)
      exact le_of_eq hk.symm
    · rw [if_neg hi]
      exact hp.1
  have htri := abs_add_le (D-∑ i, b i*Real.sign (x i)) (∑ i, b i*Real.sign (x i))
  have htri' := abs_add_le ((∑ i, b i*Real.sign (x i))-∑ i, b i*h (x i)) (∑ i, b i*h (x i))
  rw [sub_add_cancel] at htri htri'
  change |D| ≤ |∑ i, b i*h (x i)|+3*∑ i, k (x i)+B
  linarith
lemma clipped_linear_cube_mean_zero {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (b : Fin N → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    FiniteCubeConvexTransport.cubeAverage (fun x : Fin m → Bool => ∑ i,
      b i*((max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))/δ-1)) = 0 := by
  let e : Equiv.Perm (Fin m → Bool) :=
    { toFun := fun x j => !(x j)
      invFun := fun x j => !(x j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro x; funext j; simp }
  let Q : (Fin m → Bool) → ℝ := fun x => ∑ i,
    b i*((max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))/δ-1)
  have hQ (x : Fin m → Bool) : Q (e x) = -Q x := by
    have heval (i : Fin N) : (∑ j, v i j*(if e x j then (1 : ℝ) else -1)) =
        -(∑ j, v i j*(if x j then (1 : ℝ) else -1)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      change v i j*(if !(x j) then (1 : ℝ) else -1) = -(v i j*(if x j then (1 : ℝ) else -1))
      cases x j <;> simp
    dsimp only [Q]
    simp only [heval,clipped_sign_odd δ _ hδ,mul_neg,sum_neg_distrib]
  have hs := Equiv.sum_comp e Q
  simp only [hQ,sum_neg_distrib] at hs
  have hz : (∑ x, Q x) = 0 := by linarith
  change FiniteCubeConvexTransport.cubeAverage Q = 0
  rw [FiniteCubeConvexTransport.cubeAverage,hz,mul_zero]
lemma cube_scalar_interval_average {m : ℕ} (b : Fin m → ℝ) (z r : ℝ) :
    FiniteCubeConvexTransport.cubeAverage (fun x : Fin m → Bool =>
      if |(∑ j, b j*(if x j then (1 : ℝ) else -1))-z| ≤ r then 1 else 0) =
        (((univ : Finset (Finset (Fin m))).filter
          (fun S => |BoundedGramSignSmallBall.vectorSignSum b S-z| ≤ r)).card : ℝ)/2^m := by
  let e : Finset (Fin m) ≃ (Fin m → Bool) :=
    { toFun := fun S j => decide (j ∈ S)
      invFun := fun x => univ.filter (fun j => x j)
      left_inv := by intro S; ext j; simp
      right_inv := by intro x; funext j; cases hx : x j <;> simp [hx] }
  let f : (Fin m → Bool) → ℝ := fun x =>
    if |(∑ j, b j*(if x j then (1 : ℝ) else -1))-z| ≤ r then 1 else 0
  have he (S : Finset (Fin m)) : f (e S) =
      if |BoundedGramSignSmallBall.vectorSignSum b S-z| ≤ r then 1 else 0 := by
    have hv : (∑ j, b j*(if e S j then (1 : ℝ) else -1)) =
        BoundedGramSignSmallBall.vectorSignSum b S := by
      dsimp only [e,BoundedGramSignSmallBall.vectorSignSum]
      apply sum_congr rfl
      intro j _
      change b j*(if decide (j ∈ S) then (1 : ℝ) else -1) = if j ∈ S then b j else -b j
      by_cases hj : j ∈ S <;> simp [hj]
    change (if |(∑ j, b j*(if e S j then (1 : ℝ) else -1))-z| ≤ r then (1 : ℝ) else 0) = _
    rw [hv]
  rw [FiniteCubeConvexTransport.cubeAverage,← Equiv.sum_comp e f]
  simp only [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [← Finset.sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  rw [div_eq_mul_inv]
  push_cast
  exact mul_comm _ _
lemma exists_actual_normalized_cube_small_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin (n+1) → ℝ) (x : ℝ)
      (m : ℕ) (e : Fin m ≃ {j // j ∈ SignActivityFiber.freeIndices n a}) (z r : ℝ),
      0 < n → (1 : ℝ)/8 ≤ SignConditionalRows.conditionalCosineVariance n a x → 0 ≤ r →
      FiniteCubeConvexTransport.cubeAverage (fun u : Fin m → Bool =>
        if |(∑ j, GaussianSampling.normalizedRow
          (fun t => SignConditionalRows.conditionalCosineRow n a t) x (e j)*
          (if u j then (1 : ℝ) else -1))-z| ≤ r then 1 else 0) ≤
            C*(r+(n : ℝ)^(-(1 : ℝ)/2)) := by
  obtain ⟨C,hC,hsmall⟩ := SignConditionalRows.exists_normalized_conditional_row_small_ball
  refine ⟨C,hC,?_⟩
  intro n a x m e z r hn hV hr
  rw [cube_scalar_interval_average]
  exact hsmall n a x m e z r hn hV hr
lemma exists_actual_trapezoid_cube_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin (n+1) → ℝ) (N : ℕ) (loc : Fin N → ℝ)
      (m : ℕ) (e : Fin m ≃ {j // j ∈ SignActivityFiber.freeIndices n a}) (δ : ℝ),
      0 < n → N ≤ n →
      (∀ i, (1 : ℝ)/8 ≤ SignConditionalRows.conditionalCosineVariance n a (loc i)) → 0 < δ →
      let v := fun i j => GaussianSampling.normalizedRow
        (fun t => SignConditionalRows.conditionalCosineRow n a t) (loc i) (e j)
      let k := fun x => (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ
      FiniteCubeConvexTransport.cubeAverage (fun u : Fin m → Bool =>
        ∑ i, k (∑ j, v i j*(if u j then (1 : ℝ) else -1))) ≤
          C*((n : ℝ)*δ+Real.sqrt n) := by
  obtain ⟨C,hC,hsmall⟩ := exists_actual_normalized_cube_small_ball
  refine ⟨2*C,by positivity,?_⟩
  intro n a N loc m e δ hn hN hV hδ
  let v := fun i j => GaussianSampling.normalizedRow
    (fun t => SignConditionalRows.conditionalCosineRow n a t) (loc i) (e j)
  let k := fun x => (max 0 (x+2*δ)-max 0 (x+δ)-max 0 (x-δ)+max 0 (x-2*δ))/δ
  have hk (x : ℝ) : k x ≤ if |x| ≤ 2*δ then (1 : ℝ) else 0 := by
    have hp := clipped_scalar_bounds δ x hδ
    split_ifs with hx
    · exact hp.2.1
    · exact le_of_eq (hp.2.2.2.1 (le_of_lt (lt_of_not_ge hx)))
  have hmean : FiniteCubeConvexTransport.cubeAverage (fun u : Fin m → Bool =>
      ∑ i, k (∑ j, v i j*(if u j then (1 : ℝ) else -1))) ≤
        (N : ℝ)*C*(2*δ+(n : ℝ)^(-(1 : ℝ)/2)) := by
    rw [FiniteCubeConvexTransport.cubeAverage_sum]
    calc
      _ ≤ ∑ _i : Fin N, C*(2*δ+(n : ℝ)^(-(1 : ℝ)/2)) := by
        apply sum_le_sum
        intro i _
        apply (FiniteCubeConvexTransport.cubeAverage_mono (fun u => hk _)).trans
        simpa only [sub_zero] using hsmall n a (loc i) m e 0 (2*δ) hn (hV i) (by positivity)
      _ = _ := by simp; ring
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNR : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hs : (n : ℝ)*(n : ℝ)^(-(1 : ℝ)/2) = Real.sqrt n := by
    rw [show -(1 : ℝ)/2 = -((1 : ℝ)/2) by ring,Real.rpow_neg hnR.le,← Real.sqrt_eq_rpow]
    apply mul_right_cancel₀ (Real.sqrt_pos.mpr hnR).ne'
    rw [mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr hnR).ne',mul_one,← pow_two,Real.sq_sqrt hnR.le]
  change FiniteCubeConvexTransport.cubeAverage (fun u => ∑ i, k (∑ j, v i j*(if u j then (1 : ℝ) else -1))) ≤ _
  apply hmean.trans
  have he : (n : ℝ)*C*(2*δ+(n : ℝ)^(-(1 : ℝ)/2)) =
      C*(2*(n : ℝ)*δ+Real.sqrt n) := by linear_combination C*hs
  calc
    _ ≤ (n : ℝ)*C*(2*δ+(n : ℝ)^(-(1 : ℝ)/2)) := by gcongr
    _ = _ := he
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
lemma finite_piece_centered_tail {r m : ℕ} (hr : 0 < r)
    (f : Fin r → (Fin m → Bool) → ℝ) (c : Fin r → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (t A : ℝ) (htail : ∀ i, FiniteCubeConvexTransport.cubeAverage
      (fun x => if t ≤ |f i x-FiniteCubeConvexTransport.cubeAverage (f i)| then 1 else 0) ≤ A) :
    let F := fun x => ∑ i, c i*f i x
    FiniteCubeConvexTransport.cubeAverage (fun x =>
      if (r : ℝ)*t ≤ |F x-FiniteCubeConvexTransport.cubeAverage F| then 1 else 0) ≤ r*A := by
  let F := fun x => ∑ i, c i*f i x
  have hmean : FiniteCubeConvexTransport.cubeAverage F =
      ∑ i, c i*FiniteCubeConvexTransport.cubeAverage (f i) := by
    rw [FiniteCubeConvexTransport.cubeAverage_sum]
    simp only [FiniteCubeConvexTransport.cubeAverage_mul]
  have he (x : Fin m → Bool) : F x-FiniteCubeConvexTransport.cubeAverage F =
      ∑ i, c i*(f i x-FiniteCubeConvexTransport.cubeAverage (f i)) := by
    rw [hmean]
    dsimp only [F]
    simp only [mul_sub,sum_sub_distrib]
  have hpoint (x : Fin m → Bool) : (if (r : ℝ)*t ≤ |F x-FiniteCubeConvexTransport.cubeAverage F|
      then (1 : ℝ) else 0) ≤ ∑ i, if t ≤ |f i x-FiniteCubeConvexTransport.cubeAverage (f i)|
      then (1 : ℝ) else 0 := by
    by_cases hx : (r : ℝ)*t ≤ |F x-FiniteCubeConvexTransport.cubeAverage F|
    · rw [if_pos hx]
      have hex : ∃ i, t ≤ |f i x-FiniteCubeConvexTransport.cubeAverage (f i)| := by
        by_contra hn
        push Not at hn
        have hs : |F x-FiniteCubeConvexTransport.cubeAverage F| ≤
            ∑ i, |f i x-FiniteCubeConvexTransport.cubeAverage (f i)| := by
          rw [he]
          apply (abs_sum_le_sum_abs _ _).trans
          apply sum_le_sum
          intro i _
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)).trans_eq (one_mul _)
        have hlt := sum_lt_sum_of_nonempty (s := univ)
          (show (univ : Finset (Fin r)).Nonempty from ⟨⟨0,hr⟩,mem_univ _⟩)
          (fun i _ => hn i)
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hlt
        linarith
      obtain ⟨i,hi⟩ := hex
      have hsum := single_le_sum (f := fun j => if t ≤ |f j x-FiniteCubeConvexTransport.cubeAverage (f j)|
        then (1 : ℝ) else 0) (fun _ _ => by split_ifs <;> norm_num) (mem_univ i)
      simpa only [hi,ite_true] using hsum
    · rw [if_neg hx]
      exact sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  apply (FiniteCubeConvexTransport.cubeAverage_mono hpoint).trans
  rw [FiniteCubeConvexTransport.cubeAverage_sum]
  calc
    _ ≤ ∑ _i : Fin r, A := sum_le_sum (fun i _ => htail i)
    _ = _ := by simp
lemma weighted_relu_piece_sum_tail {r N m : ℕ} (hr : 0 < r)
    (v : Fin N → Fin m → ℝ) (w s : Fin r → Fin N → ℝ)
    (hw : ∀ k i, 0 ≤ w k i ∧ w k i ≤ 1) (c : Fin r → ℝ) (hc : ∀ k, |c k| ≤ 1)
    (M : ℝ) (hM : 0 < M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t) :
    let f := fun k (x : Fin m → Bool) =>
      ∑ i, w k i*max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+s k i)/δ
    let F := fun x => ∑ k, c k*f k x
    FiniteCubeConvexTransport.cubeAverage (fun x =>
      if (r : ℝ)*t ≤ |F x-FiniteCubeConvexTransport.cubeAverage F| then 1 else 0) ≤
        ((r : ℝ)*4*Real.exp 81)*Real.exp (-(t^2*δ^2)/(64*((N : ℝ)+1)*M)) := by
  apply (finite_piece_centered_tail hr _ c hc t _
    (fun k => weighted_relu_centered_tail v (w k) (s k) (hw k) M hM hframe δ hδ t ht)).trans_eq
  ring
lemma clipped_crossing_cube_tail {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (b : Fin N → ℝ) (hb : ∀ i, |b i| ≤ 1) (M : ℝ) (hM : 0 < M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t) :
    let Q := fun x : Fin m → Bool => ∑ i, b i*
      ((max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))/δ-1)
    FiniteCubeConvexTransport.cubeAverage (fun x => if 4*t ≤ |Q x| then 1 else 0) ≤
      (16*Real.exp 81)*Real.exp (-(t^2*δ^2)/(64*((N : ℝ)+1)*M)) := by
  let Q := fun x : Fin m → Bool => ∑ i, b i*
    ((max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))/δ-1)
  let w : Fin 4 → Fin N → ℝ := ![(fun i => max 0 (b i)),(fun i => max 0 (b i)),
    (fun i => max 0 (-b i)),(fun i => max 0 (-b i))]
  let s : Fin 4 → Fin N → ℝ := ![(fun _ => δ),(fun _ => -δ),(fun _ => δ),(fun _ => -δ)]
  let c : Fin 4 → ℝ := ![1,-1,-1,1]
  let f := fun k (x : Fin m → Bool) =>
    ∑ i, w k i*max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+s k i)/δ
  let F := fun x => ∑ k, c k*f k x
  have hw : ∀ k i, 0 ≤ w k i ∧ w k i ≤ 1 := by
    intro k i
    have hb' := abs_le.mp (hb i)
    fin_cases k <;> dsimp only [w] <;>
      exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩
  have hc : ∀ k, |c k| ≤ 1 := by intro k; fin_cases k <;> norm_num [c]
  have hdecomp (x : Fin m → Bool) : F x = Q x+∑ i, b i := by
    dsimp only [F]
    rw [Fin.sum_univ_four]
    dsimp only [c,f,w,s,Q]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,one_mul,neg_one_mul,← sub_eq_add_neg]
    change (∑ i : Fin N, (_ : ℝ))-(∑ i : Fin N, (_ : ℝ))-(∑ i : Fin N, (_ : ℝ))+
      (∑ i : Fin N, (_ : ℝ)) = (∑ i : Fin N, (_ : ℝ))+(∑ i : Fin N, (_ : ℝ))
    simp only [← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have hp := relu_neg_identity (b i)
    field_simp
    linear_combination -(max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))*hp
  have hQ := clipped_linear_cube_mean_zero v b δ hδ
  have hmean : FiniteCubeConvexTransport.cubeAverage F = ∑ i, b i := by
    rw [show F = (fun x => Q x+∑ i, b i) from funext hdecomp]
    rw [FiniteCubeConvexTransport.cubeAverage_add,hQ,FiniteCubeConvexTransport.cubeAverage_const,zero_add]
  have he := weighted_relu_piece_sum_tail (by norm_num : 0 < 4) v w s hw c hc M hM hframe δ hδ t ht
  change FiniteCubeConvexTransport.cubeAverage (fun x => if (4 : ℝ)*t ≤
    |F x-FiniteCubeConvexTransport.cubeAverage F| then 1 else 0) ≤ _ at he
  simp only [hmean,hdecomp,add_sub_cancel_right] at he
  norm_num only [Nat.cast_ofNat] at he
  simpa only [Q,show (4 : ℝ)*4 = 16 by norm_num] using he
lemma trapezoid_cube_centered_tail {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t) :
    let K := fun x : Fin m → Bool => ∑ i,
      (max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+2*δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ)+
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-2*δ))/δ
    FiniteCubeConvexTransport.cubeAverage (fun x => if 4*t ≤
      |K x-FiniteCubeConvexTransport.cubeAverage K| then 1 else 0) ≤
        (16*Real.exp 81)*Real.exp (-(t^2*δ^2)/(64*((N : ℝ)+1)*M)) := by
  let K := fun x : Fin m → Bool => ∑ i,
    (max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+2*δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ)+
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-2*δ))/δ
  let w : Fin 4 → Fin N → ℝ := fun _ _ => 1
  let s : Fin 4 → Fin N → ℝ := ![(fun _ => 2*δ),(fun _ => δ),(fun _ => -δ),(fun _ => -2*δ)]
  let c : Fin 4 → ℝ := ![1,-1,-1,1]
  let f := fun k (x : Fin m → Bool) =>
    ∑ i, w k i*max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+s k i)/δ
  let F := fun x => ∑ k, c k*f k x
  have hdecomp : F = K := by
    funext x
    dsimp only [F]
    rw [Fin.sum_univ_four]
    dsimp only [c,f,w,s,K]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,one_mul,neg_one_mul,← sub_eq_add_neg,
      ← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring_nf
  have he := weighted_relu_piece_sum_tail (by norm_num : 0 < 4) v w s
    (by intro _ _; norm_num [w]) c (by intro k; fin_cases k <;> norm_num [c]) M hM hframe δ hδ t ht
  change FiniteCubeConvexTransport.cubeAverage (fun x => if (4 : ℝ)*t ≤
    |F x-FiniteCubeConvexTransport.cubeAverage F| then 1 else 0) ≤ _ at he
  rw [hdecomp] at he
  norm_num only [Nat.cast_ofNat] at he
  simpa only [K,show (4 : ℝ)*4 = 16 by norm_num] using he
lemma count_cube_tail_of_actual_rows {N m : ℕ} (v : Fin N → Fin m → ℝ)
    (b : Fin N → ℝ) (hb : ∀ i, |b i| ≤ 1) (M : ℝ) (hM : 0 < M)
    (hframe : ∀ u : Fin m → ℝ, (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2)
    (D : (Fin m → Bool) → ℝ) (B : ℝ)
    (hcount : ∀ x, |D x-∑ i, b i*Real.sign (∑ j, v i j*(if x j then (1 : ℝ) else -1))| ≤
      B+2*∑ i, if (∑ j, v i j*(if x j then (1 : ℝ) else -1)) = 0 then (1 : ℝ) else 0)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t) :
    let K := fun x : Fin m → Bool => ∑ i,
      (max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+2*δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ)+
        max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-2*δ))/δ
    FiniteCubeConvexTransport.cubeAverage (fun x =>
      if B+3*FiniteCubeConvexTransport.cubeAverage K+16*t < |D x| then 1 else 0) ≤
        (32*Real.exp 81)*Real.exp (-(t^2*δ^2)/(64*((N : ℝ)+1)*M)) := by
  let K := fun x : Fin m → Bool => ∑ i,
    (max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+2*δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ)+
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-2*δ))/δ
  let Q := fun x : Fin m → Bool => ∑ i, b i*
    ((max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ))/δ-1)
  have hbound (x : Fin m → Bool) : |D x| ≤ |Q x|+3*K x+B :=
    clipped_count_bound b _ hb δ (D x) B hδ (hcount x)
  have hpoint (x : Fin m → Bool) : (if B+3*FiniteCubeConvexTransport.cubeAverage K+16*t < |D x|
      then (1 : ℝ) else 0) ≤ (if 4*t ≤ |Q x| then (1 : ℝ) else 0)+
        (if 4*t ≤ |K x-FiniteCubeConvexTransport.cubeAverage K| then (1 : ℝ) else 0) := by
    by_cases hD : B+3*FiniteCubeConvexTransport.cubeAverage K+16*t < |D x|
    · rw [if_pos hD]
      by_cases hQ : 4*t ≤ |Q x|
      · rw [if_pos hQ]
        split_ifs <;> norm_num
      · rw [if_neg hQ,zero_add]
        by_cases hK : 4*t ≤ |K x-FiniteCubeConvexTransport.cubeAverage K|
        · rw [if_pos hK]
        · exfalso
          have hq := lt_of_not_ge hQ
          have hk := lt_of_not_ge hK
          have hdiff := le_abs_self (K x-FiniteCubeConvexTransport.cubeAverage K)
          linarith [hbound x]
    · rw [if_neg hD]
      split_ifs <;> norm_num
  apply (FiniteCubeConvexTransport.cubeAverage_mono hpoint).trans
  rw [FiniteCubeConvexTransport.cubeAverage_add]
  have hQ := clipped_crossing_cube_tail v b hb M hM hframe δ hδ t ht
  have hK := trapezoid_cube_centered_tail v M hM hframe δ hδ t ht
  change FiniteCubeConvexTransport.cubeAverage (fun x => if 4*t ≤ |Q x| then (1 : ℝ) else 0) ≤ _ at hQ
  change FiniteCubeConvexTransport.cubeAverage (fun x => if 4*t ≤
    |K x-FiniteCubeConvexTransport.cubeAverage K| then (1 : ℝ) else 0) ≤ _ at hK
  nlinarith
theorem exists_actual_good_fiber_count_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin (n+1) → ℝ)
      (m : ℕ) (e : Fin m ≃ {j // j ∈ SignActivityFiber.freeIndices n a}),
      0 < n → a ∈ SignPolynomialDivisibility.signVectors (n+1) →
      ¬SignSineOccupancy.occupancyBad n a → ¬SignConditionalRows.maskBad n a →
      SignSineOccupancy.endpointCutoff ≤ Real.pi*n-SignSineOccupancy.endpointCutoff →
      ∀ (δ t : ℝ), 0 < δ → 0 ≤ t →
      FiniteCubeConvexTransport.cubeAverage (fun x : Fin m → Bool =>
        if 1+6*SignSineOccupancy.localThreshold n+3*C*((n : ℝ)*δ+Real.sqrt n)+16*t <
          |(((coefficientPolynomial n (fun j =>
            (SignActivityFiber.fillFree n a (fun k => if x (e.symm k) then (1 : ℝ) else -1) j : ℂ))).roots.filter
            (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2| then 1 else 0) ≤
              (32*Real.exp 81)*Real.exp (-(t^2*δ^2)/
                (64*((n : ℝ)+1)*(80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)))) := by
  obtain ⟨C,hC,hsmall⟩ := exists_actual_trapezoid_cube_mean_bound
  refine ⟨C,hC,?_⟩
  intro n a m e hn ha hg hm hbulk δ t hδ ht
  obtain ⟨N,loc,b,hN,_,hb,hV,hframe,hcount⟩ :=
    SignFiberCrossings.exists_actual_free_row_count_consumer hn a ha hg hm hbulk
  let v : Fin N → Fin m → ℝ := fun i j => GaussianSampling.normalizedRow
    (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i (e j)
  let M : ℝ := 80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)
  let D : (Fin m → Bool) → ℝ := fun x =>
    (((coefficientPolynomial n (fun j =>
      (SignActivityFiber.fillFree n a (fun k => if x (e.symm k) then (1 : ℝ) else -1) j : ℂ))).roots.filter
      (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2
  have hM : 0 < M := by dsimp only [M]; positivity
  have hreindex (i : Fin N) (u : Fin m → ℝ) :
      (∑ k, GaussianSampling.normalizedRow
        (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i k*u (e.symm k)) = ∑ j, v i j*u j := by
    have he := Equiv.sum_comp e (fun k => GaussianSampling.normalizedRow
      (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i k*u (e.symm k))
    simpa only [e.symm_apply_apply,v] using he.symm
  have hframe' (u : Fin m → ℝ) : (∑ i, (∑ j, v i j*u j)^2) ≤ M*∑ j, u j^2 := by
    have he := hframe (fun k => u (e.symm k))
    have hes := Equiv.sum_comp e (fun k => u (e.symm k)^2)
    simp only [e.symm_apply_apply] at hes
    rw [← hes] at he
    simp only [hreindex] at he
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
    dsimp only [M]
    nlinarith [Real.pi_pos]
  have hcount' (x : Fin m → Bool) : |D x-∑ i, b i*Real.sign (∑ j, v i j*(if x j then (1 : ℝ) else -1))| ≤
      (1+6*SignSineOccupancy.localThreshold n)+2*∑ i,
        if (∑ j, v i j*(if x j then (1 : ℝ) else -1)) = 0 then (1 : ℝ) else 0 := by
    have he := hcount (fun k => if x (e.symm k) then (1 : ℝ) else -1)
      (by intro k; split_ifs <;> simp)
    have hr (i : Fin N) : (∑ k, GaussianSampling.normalizedRow
        (fun i => SignConditionalRows.conditionalCosineRow n a (loc i)) i k*
        (if x (e.symm k) then (1 : ℝ) else -1)) =
        ∑ j, v i j*(if x j then (1 : ℝ) else -1) :=
      hreindex i (fun j => if x j then (1 : ℝ) else -1)
    simpa only [hr,D] using he
  let K := fun x : Fin m → Bool => ∑ i,
    (max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+2*δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))+δ)-
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-δ)+
      max 0 ((∑ j, v i j*(if x j then (1 : ℝ) else -1))-2*δ))/δ
  have hK : FiniteCubeConvexTransport.cubeAverage K ≤ C*((n : ℝ)*δ+Real.sqrt n) := by
    simpa only [K,v,GaussianSampling.normalizedRow,GaussianSampling.rowNormSq] using
      hsmall n a N loc m e δ hn hN hV hδ
  have he := count_cube_tail_of_actual_rows v b hb M hM hframe' D
    (1+6*SignSineOccupancy.localThreshold n) hcount' δ hδ t ht
  change FiniteCubeConvexTransport.cubeAverage (fun x =>
    if 1+6*SignSineOccupancy.localThreshold n+3*FiniteCubeConvexTransport.cubeAverage K+16*t < |D x|
    then (1 : ℝ) else 0) ≤ _ at he
  have hpoint (x : Fin m → Bool) : (if 1+6*SignSineOccupancy.localThreshold n+
      3*C*((n : ℝ)*δ+Real.sqrt n)+16*t < |D x| then (1 : ℝ) else 0) ≤
      if 1+6*SignSineOccupancy.localThreshold n+3*FiniteCubeConvexTransport.cubeAverage K+16*t < |D x|
      then (1 : ℝ) else 0 := by
    split_ifs <;> try norm_num
    exfalso
    linarith
  apply ((FiniteCubeConvexTransport.cubeAverage_mono hpoint).trans he).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hNR : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hdenN : 0 < 64*((N : ℝ)+1)*M := by positivity
  have hdenn : 0 < 64*((n : ℝ)+1)*M := by positivity
  change -(t^2*δ^2)/(64*((N : ℝ)+1)*M) ≤ -(t^2*δ^2)/(64*((n : ℝ)+1)*M)
  rw [div_le_div_iff₀ hdenN hdenn]
  nlinarith [sq_nonneg t,sq_nonneg δ,mul_nonneg (sq_nonneg t) (sq_nonneg δ),
    mul_nonneg (show 0 ≤ (n : ℝ)-N by linarith) (mul_nonneg hM.le (mul_nonneg (sq_nonneg t) (sq_nonneg δ)))]
end Fluctuations.SignClippedConvexity
end
end

section
open MeasureTheory Set
open scoped ENNReal
namespace Fluctuations.ExponentialTailMoment
noncomputable section
lemma integral_exp_derivative (a x : ℝ) :
    (∫ u in (0 : ℝ)..x, a * Real.exp (a * u)) = Real.exp (a * x) - 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => Real.exp (a * u))
    (f' := fun u : ℝ => a * Real.exp (a * u))
    (a := 0) (b := x)
    (fun u _ => by simpa [mul_comm] using ((hasDerivAt_id u).const_mul a).exp)
    (show IntervalIntegrable (fun u : ℝ => a * Real.exp (a * u)) volume 0 x from
      (by fun_prop : Continuous (fun u : ℝ => a * Real.exp (a * u))).intervalIntegrable 0 x)
  simpa only [mul_zero, Real.exp_zero] using h
lemma lintegral_decay_kernel {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (A * a * Real.exp (-a * u))) = ENNReal.ofReal A := by
  have hi : IntegrableOn (fun u : ℝ => A * a * Real.exp (-a * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).const_mul (A * a)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun u => by positivity)),
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -a < 0) 0]
  congr 1
  simp
  field_simp
lemma lintegral_exp_sub_one_le_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < |X ω|} ≤ A * Real.exp (-(2 * a) * u)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * |X ω|) - 1) ∂μ) ≤ ENNReal.ofReal A := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall (fun ω => abs_nonneg (X ω))) hX.abs
    (g := fun u => a * Real.exp (a * u))
    (fun t _ => (by fun_prop : Continuous (fun u : ℝ => a * Real.exp (a * u))).intervalIntegrable 0 t)
    (Filter.Eventually.of_forall (fun u => by positivity))
  simp only [integral_exp_derivative] at h
  rw [h, ← lintegral_decay_kernel ha hA]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have ht : μ {ω | u < |X ω|} ≤ ENNReal.ofReal (A * Real.exp (-(2 * a) * u)) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ A * Real.exp (-(2 * a) * u))]
      using htail u hu.le
  calc
    _ ≤ ENNReal.ofReal (A * Real.exp (-(2 * a) * u)) *
        ENNReal.ofReal (a * Real.exp (a * u)) := mul_le_mul' ht le_rfl
    _ = ENNReal.ofReal (A * a * Real.exp (-a * u)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * Real.exp (-(2 * a) * u))]
      congr 1
      calc
        _ = A * a * (Real.exp (-(2 * a) * u) * Real.exp (a * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
lemma integrable_exp_and_integral_le_of_double_rate_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < |X ω|} ≤ A * Real.exp (-(2 * a) * u)) :
    Integrable (fun ω => Real.exp (a * |X ω|)) μ ∧
      (∫ ω, Real.exp (a * |X ω|) ∂μ) ≤ 1 + A := by
  have hb := lintegral_exp_sub_one_le_of_tail μ X hX ha hA htail
  have hn : 0 ≤ᵐ[μ] (fun ω => Real.exp (a * |X ω|) - 1) :=
    Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg ha.le (abs_nonneg _))))
  have hm : AEStronglyMeasurable (fun ω => Real.exp (a * |X ω|) - 1) μ :=
    ((hX.abs.const_mul a).exp.sub_const 1).aestronglyMeasurable
  have hi : Integrable (fun ω => Real.exp (a * |X ω|) - 1) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp
      (ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top))
  have he : Integrable (fun ω => Real.exp (a * |X ω|)) μ := by
    convert! hi.add (integrable_const (1 : ℝ)) using 1
    ext ω
    simp only [Pi.add_apply, sub_add_cancel]
  have hmean : (∫ ω, Real.exp (a * |X ω|) - 1 ∂μ) ≤ A := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hb
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp hb
  have hid := integral_sub he (integrable_const (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hid
  exact ⟨he, by linarith⟩
lemma integrable_exp_and_integral_le_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < |X ω|} ≤ A * Real.exp (-u / K)) :
    Integrable (fun ω => Real.exp (|X ω| / (2 * K))) μ ∧
      (∫ ω, Real.exp (|X ω| / (2 * K)) ∂μ) ≤ 1 + A := by
  have h := integrable_exp_and_integral_le_of_double_rate_tail μ X hX
    (a := 1 / (2 * K)) (by positivity) hA (fun u hu => by
      convert! htail u hu using 1
      congr 2
      field_simp)
  simpa only [one_div_mul_eq_div] using h
end
end Fluctuations.ExponentialTailMoment
end

section
noncomputable section
open Finset Classical Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Fluctuations.SignConditionalCountMoments
open FiniteCubeConvexTransport
lemma cubeAverage_eq_uniform_integral {m : ℕ} (f : (Fin m → Bool) → ℝ) :
    cubeAverage f = ∫ x, f x ∂(PMF.uniformOfFintype (Fin m → Bool)).toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,← mul_sum]
  rfl
lemma uniform_real_event_eq_cubeAverage {m : ℕ} (P : (Fin m → Bool) → Prop) :
    (PMF.uniformOfFintype (Fin m → Bool)).toMeasure.real {x | P x} =
      cubeAverage (fun x => if P x then 1 else 0) := by
  rw [cubeAverage_eq_uniform_integral]
  have hs : MeasurableSet {x : Fin m → Bool | P x} := Set.Finite.measurableSet (Set.toFinite _)
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (integral_indicator_one hs).symm
lemma cube_second_moment_of_gaussian_tail {m : ℕ} (f : (Fin m → Bool) → ℝ)
    (L A : ℝ) (hL : 0 < L) (hA : 0 ≤ A)
    (htail : ∀ t : ℝ, 0 ≤ t → cubeAverage (fun x => if t < |f x| then 1 else 0) ≤
      A*Real.exp (-t^2/L^2)) :
    cubeAverage (fun x => f x^2) ≤ 2*(1+A)*L^2 := by
  let μ := (PMF.uniformOfFintype (Fin m → Bool)).toMeasure
  let X : (Fin m → Bool) → ℝ := fun x => f x^2
  have hX : AEMeasurable X μ := (measurable_of_finite X).aemeasurable
  have htailX (u : ℝ) (hu : 0 ≤ u) : μ.real {x | u < |X x|} ≤ A*Real.exp (-u/L^2) := by
    rw [uniform_real_event_eq_cubeAverage]
    have hp (x : Fin m → Bool) : (if u < |X x| then (1 : ℝ) else 0) ≤
        if Real.sqrt u < |f x| then (1 : ℝ) else 0 := by
      by_cases hx : u < |X x|
      · rw [if_pos hx]
        have hs : Real.sqrt u < |f x| := by
          apply (sq_lt_sq₀ (Real.sqrt_nonneg u) (abs_nonneg _)).mp
          rw [Real.sq_sqrt hu,sq_abs]
          simpa only [X,abs_of_nonneg (sq_nonneg (f x))] using hx
        rw [if_pos hs]
      · rw [if_neg hx]
        split_ifs <;> norm_num
    apply (cubeAverage_mono hp).trans
    simpa only [Real.sq_sqrt hu] using htail (Real.sqrt u) (Real.sqrt_nonneg u)
  obtain ⟨hi,hmean⟩ := ExponentialTailMoment.integrable_exp_and_integral_le_of_exponential_tail
    μ X hX (sq_pos_of_pos hL) hA htailX
  have hpoint (x : Fin m → Bool) : X x ≤ 2*L^2*Real.exp (|X x|/(2*L^2)) := by
    have he := Real.add_one_le_exp (|X x|/(2*L^2))
    have hd : |X x|/(2*L^2) ≤ Real.exp (|X x|/(2*L^2)) := by linarith
    have hm := (div_le_iff₀ (by positivity : 0 < 2*L^2)).mp hd
    have hnon : 0 ≤ X x := sq_nonneg _
    rw [abs_of_nonneg hnon] at hm ⊢
    simpa only [mul_comm] using hm
  rw [cubeAverage_eq_uniform_integral]
  change (∫ x, X x ∂μ) ≤ _
  calc
    _ ≤ ∫ x, 2*L^2*Real.exp (|X x|/(2*L^2)) ∂μ :=
      integral_mono (Integrable.of_finite) (hi.const_mul _) hpoint
    _ = 2*L^2*(∫ x, Real.exp (|X x|/(2*L^2)) ∂μ) := integral_const_mul _ _
    _ ≤ 2*L^2*(1+A) := mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring
lemma cube_second_moment_of_shifted_gaussian_tail {m : ℕ} (D : (Fin m → Bool) → ℝ)
    (B L A : ℝ) (hB : 0 ≤ B) (hL : 0 < L) (hA : 0 ≤ A)
    (htail : ∀ t : ℝ, 0 ≤ t → cubeAverage (fun x => if B+t < |D x| then 1 else 0) ≤
      A*Real.exp (-t^2/L^2)) :
    cubeAverage (fun x => D x^2) ≤ 2*B^2+4*(1+A)*L^2 := by
  let E : (Fin m → Bool) → ℝ := fun x => max 0 (|D x|-B)
  have hE : ∀ t : ℝ, 0 ≤ t → cubeAverage (fun x => if t < |E x| then 1 else 0) ≤
      A*Real.exp (-t^2/L^2) := by
    intro t ht
    have hp (x : Fin m → Bool) : t < |E x| ↔ B+t < |D x| := by
      rw [abs_of_nonneg (show 0 ≤ E x from le_max_left _ _)]
      change t < max 0 (|D x|-B) ↔ _
      rw [lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h; exact Or.inr (by linarith)
    simpa only [hp] using htail t ht
  have hmoment := cube_second_moment_of_gaussian_tail E L A hL hA hE
  have hpoint (x : Fin m → Bool) : D x^2 ≤ 2*B^2+2*E x^2 := by
    have he : |D x| ≤ B+E x := by dsimp only [E]; linarith [le_max_right 0 (|D x|-B)]
    have hn : 0 ≤ E x := le_max_left _ _
    have hs : (B-E x)^2 ≥ 0 := sq_nonneg _
    have hsq := (sq_le_sq₀ (abs_nonneg (D x)) (add_nonneg hB hn)).mpr he
    rw [sq_abs] at hsq
    nlinarith
  apply (cubeAverage_mono hpoint).trans
  rw [cubeAverage_add,cubeAverage_const,cubeAverage_mul]
  linarith
theorem exists_actual_good_fiber_count_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin (n+1) → ℝ)
      (m : ℕ) (e : Fin m ≃ {j // j ∈ SignActivityFiber.freeIndices n a}),
      0 < n → a ∈ SignPolynomialDivisibility.signVectors (n+1) →
      ¬SignSineOccupancy.occupancyBad n a → ¬SignConditionalRows.maskBad n a →
      SignSineOccupancy.endpointCutoff ≤ Real.pi*n-SignSineOccupancy.endpointCutoff →
      ∀ δ : ℝ, 0 < δ →
      cubeAverage (fun x : Fin m → Bool =>
        ((((coefficientPolynomial n (fun j =>
          (SignActivityFiber.fillFree n a (fun k => if x (e.symm k) then (1 : ℝ) else -1) j : ℂ))).roots.filter
          (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2)^2) ≤
        2*(1+6*SignSineOccupancy.localThreshold n+3*C*((n : ℝ)*δ+Real.sqrt n))^2+
          (65536*(1+32*Real.exp 81)*80*Real.pi)*((n : ℝ)+1)*
            ((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2 := by
  obtain ⟨C,hC,htail⟩ := SignClippedConvexity.exists_actual_good_fiber_count_tail
  refine ⟨C,hC,?_⟩
  intro n a m e hn ha hg hm hbulk δ hδ
  let M : ℝ := 80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)
  let B : ℝ := 1+6*SignSineOccupancy.localThreshold n+3*C*((n : ℝ)*δ+Real.sqrt n)
  let L : ℝ := 128*Real.sqrt (((n : ℝ)+1)*M)/δ
  let D : (Fin m → Bool) → ℝ := fun x =>
    (((coefficientPolynomial n (fun j =>
      (SignActivityFiber.fillFree n a (fun k => if x (e.symm k) then (1 : ℝ) else -1) j : ℂ))).roots.filter
      (fun z => ‖z‖ ≤ 1)).card : ℝ) - (n : ℝ)/2
  have hM : 0 < M := by dsimp only [M]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hH : 0 ≤ SignSineOccupancy.localThreshold n := by
    have hlog : 0 < Real.log ((n : ℝ)+2) := Real.log_pos (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold SignSineOccupancy.localThreshold SignSineOccupancy.jensenScale
    have hrad := SignSineOccupancy.evaluationRadius_pos
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hraw (u : ℝ) (hu : 0 ≤ u) : cubeAverage (fun x => if B+u < |D x| then 1 else 0) ≤
      (32*Real.exp 81)*Real.exp (-u^2/L^2) := by
    have he := htail n a m e hn ha hg hm hbulk δ (u/16) hδ (by positivity)
    have hshift : 16*(u/16) = u := by ring
    change cubeAverage (fun x => if B+16*(u/16) < |D x| then (1 : ℝ) else 0) ≤ _ at he
    rw [hshift] at he
    have hexp : -((u/16)^2*δ^2)/(64*((n : ℝ)+1)*M) = -u^2/L^2 := by
      dsimp only [L]
      simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)*M)]
      field_simp
      ring
    simpa only [M,hexp] using he
  have he := cube_second_moment_of_shifted_gaussian_tail D B L (32*Real.exp 81) hB hL (by positivity) hraw
  change cubeAverage (fun x => D x^2) ≤ _
  convert! he using 1
  dsimp only [B,L,M]
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)*
    (80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)))]
  ring
end Fluctuations.SignConditionalCountMoments
end
end

section
noncomputable section
open Finset Classical Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Fluctuations.SignFiberAverage
open SignActivityFiber SignPolynomialDivisibility SignNoncyclotomicAssembly FiniteCubeConvexTransport
lemma sum_sine_fiber_averages (n : ℕ) (g : (Fin (n+1) → ℝ) → ℝ) :
    (∑ a ∈ signVectors (n+1),
      (∑ b ∈ (signVectors (n+1)).filter (sameSineFiber n a), g b)/
        (((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ)) =
      ∑ a ∈ signVectors (n+1), g a := by
  have hexpand (a : Fin (n+1) → ℝ) :
      (∑ b ∈ (signVectors (n+1)).filter (sameSineFiber n a), g b)/
        (((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ) =
      ∑ b ∈ signVectors (n+1), if sameSineFiber n a b then
        g b/(((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ) else 0 := by
    rw [sum_div,Finset.sum_filter]
  simp only [hexpand]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  have hcard (a : Fin (n+1) → ℝ) (ha : a ∈ signVectors (n+1)) (hab : sameSineFiber n a b) :
      ((signVectors (n+1)).filter (sameSineFiber n a)).card =
        ((signVectors (n+1)).filter (sameSineFiber n b)).card := by
    rw [card_sine_fiber n a ha,card_sine_fiber n b hb,freeIndices_eq_of_sameSineFiber n a b hab]
  have hrel (a : Fin (n+1) → ℝ) : sameSineFiber n a b ↔ sameSineFiber n b a :=
    ⟨sameSineFiber_symm n a b,sameSineFiber_symm n b a⟩
  have he : (∑ a ∈ signVectors (n+1), if sameSineFiber n a b then
      g b/(((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ) else 0) =
      ∑ a ∈ (signVectors (n+1)).filter (sameSineFiber n b),
        g b/(((signVectors (n+1)).filter (sameSineFiber n b)).card : ℝ) := by
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro a ha
    by_cases hab : sameSineFiber n a b
    · rw [if_pos hab,if_pos ((hrel a).mp hab),hcard a ha hab]
    · rw [if_neg hab,if_neg (by simpa only [← hrel a] using hab)]
  rw [he,sum_const,nsmul_eq_mul]
  have hc : (0 : ℝ) < ((signVectors (n+1)).filter (sameSineFiber n b)).card := by
    rw [card_sine_fiber n b hb]
    positivity
  field_simp
lemma free_sign_cubeAverage_eq {n m : ℕ} (a : Fin (n+1) → ℝ)
    (e : Fin m ≃ {j // j ∈ freeIndices n a}) (g : ({j // j ∈ freeIndices n a} → ℝ) → ℝ) :
    cubeAverage (fun x : Fin m → Bool => g (fun j => if x (e.symm j) then (1 : ℝ) else -1)) =
      (∑ u ∈ Fintype.piFinset (fun _ : {j // j ∈ freeIndices n a} => ({1,-1} : Finset ℝ)), g u)/
        (2 : ℝ)^(freeIndices n a).card := by
  let ψ : (Fin m → Bool) → ({j // j ∈ freeIndices n a} → ℝ) :=
    fun x j => if x (e.symm j) then (1 : ℝ) else -1
  have hinj : Function.Injective ψ := by
    intro x y h
    funext j
    have he := congrFun h (e j)
    simp only [ψ,e.symm_apply_apply] at he
    cases hx : x j <;> cases hy : y j <;> simp_all
    all_goals norm_num at he
  have himage : (univ : Finset (Fin m → Bool)).image ψ =
      Fintype.piFinset (fun _ : {j // j ∈ freeIndices n a} => ({1,-1} : Finset ℝ)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨x,_,rfl⟩ := mem_image.mp hu
      simp only [Fintype.mem_piFinset,Finset.mem_insert,Finset.mem_singleton]
      intro j
      dsimp only [ψ]
      split_ifs <;> simp
    · intro hu
      have hs : ∀ j, u j = 1 ∨ u j = -1 := by
        simpa only [Fintype.mem_piFinset,Finset.mem_insert,Finset.mem_singleton] using hu
      refine mem_image.mpr ⟨(fun j => decide (u (e j) = 1)),mem_univ _,?_⟩
      funext j
      dsimp only [ψ]
      simp only [e.apply_symm_apply]
      rcases hs j with h | h <;> norm_num [h]
  have hsum : (∑ x : Fin m → Bool, g (ψ x)) =
      ∑ u ∈ Fintype.piFinset (fun _ : {j // j ∈ freeIndices n a} => ({1,-1} : Finset ℝ)), g u := by
    rw [← himage,sum_image (fun _ _ _ _ h => hinj h)]
  have hm : m = (freeIndices n a).card := by
    have he := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_coe] using he
  rw [cubeAverage]
  change (Fintype.card (Fin m → Bool) : ℝ)⁻¹*(∑ x, g (ψ x)) = _
  rw [hsum]
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,hm,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv]
  exact mul_comm _ _
lemma sine_fiber_average_eq_cubeAverage {n m : ℕ} (a : Fin (n+1) → ℝ)
    (ha : a ∈ signVectors (n+1)) (e : Fin m ≃ {j // j ∈ freeIndices n a})
    (g : (Fin (n+1) → ℝ) → ℝ) :
    (∑ b ∈ (signVectors (n+1)).filter (sameSineFiber n a), g b)/
      (((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ) =
      cubeAverage (fun x : Fin m → Bool =>
        g (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1))) := by
  rw [average_on_sine_fiber n a ha g]
  exact (free_sign_cubeAverage_eq a e (fun u => g (fillFree n a u))).symm
lemma finite_average_le_of_sine_fiber_averages (n : ℕ)
    (g : (Fin (n+1) → ℝ) → ℝ) (K : ℝ)
    (hK : ∀ a ∈ signVectors (n+1),
      (∑ b ∈ (signVectors (n+1)).filter (sameSineFiber n a), g b)/
        (((signVectors (n+1)).filter (sameSineFiber n a)).card : ℝ) ≤ K) :
    (2 : ℝ)⁻¹^(n+1)*(∑ a ∈ signVectors (n+1), g a) ≤ K := by
  rw [← sum_sine_fiber_averages n g]
  have hs := sum_le_sum (fun a ha => hK a ha)
  have hsum : (∑ _a ∈ signVectors (n+1), K) = (2 : ℝ)^(n+1)*K := by
    rw [sum_const,nsmul_eq_mul,card_signVectors]
    push_cast
    rfl
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2 : ℝ)⁻¹^(n+1))).trans
  rw [hsum,← mul_assoc,← mul_pow,inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),one_pow,one_mul]
lemma finite_sign_event_indicator_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ) (P : (Fin m → ℝ) → Prop) :
    Prob μ {ω | P (fun j => ξ j.val ω)} =
      ∫ ω, if P (fun j => ξ j.val ω) then (1 : ℝ) else 0 ∂μ := by
  unfold Prob
  rw [finite_sign_event_measure μ ξ hξ m P,finite_sign_integral μ ξ hξ m (fun a => if P a then (1 : ℝ) else 0)]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  exact mul_comm _ _
lemma finite_sign_integral_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ) (f g : (Fin m → ℝ) → ℝ)
    (hfg : ∀ a ∈ signVectors m, f a ≤ g a) :
    (∫ ω, f (fun j => ξ j.val ω) ∂μ) ≤ ∫ ω, g (fun j => ξ j.val ω) ∂μ := by
  rw [finite_sign_integral μ ξ hξ m f,finite_sign_integral μ ξ hξ m g]
  exact mul_le_mul_of_nonneg_left (sum_le_sum hfg) (by positivity)
lemma integral_on_good_le_of_cube_averages {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ)
    (G : (Fin (n+1) → ℝ) → Prop)
    (hG : ∀ a b, sameSineFiber n a b → (G b ↔ G a))
    (g : (Fin (n+1) → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hgood : ∀ a ∈ signVectors (n+1), G a → ∀ (m : ℕ)
      (e : Fin m ≃ {j // j ∈ freeIndices n a}),
      cubeAverage (fun x : Fin m → Bool =>
        g (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1))) ≤ K) :
    (∫ ω, if G (fun j => ξ j.val ω) then g (fun j => ξ j.val ω) else 0 ∂μ) ≤ K := by
  rw [finite_sign_integral μ ξ hξ (n+1) (fun a => if G a then g a else 0)]
  apply finite_average_le_of_sine_fiber_averages
  intro a ha
  let m := Fintype.card {j // j ∈ freeIndices n a}
  let e : Fin m ≃ {j // j ∈ freeIndices n a} := (Fintype.equivFin _).symm
  rw [sine_fiber_average_eq_cubeAverage a ha e (fun b => if G b then g b else 0)]
  by_cases hGa : G a
  · have hf : (fun x : Fin m → Bool =>
        if G (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1)) then
          g (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1)) else 0) =
        (fun x : Fin m → Bool => g (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1))) := by
      funext x
      rw [if_pos ((hG a _ (fillFree_sameSineFiber n a _)).mpr hGa)]
    rw [hf]
    exact hgood a ha hGa m e
  · have hf : (fun x : Fin m → Bool =>
        if G (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1)) then
          g (fillFree n a (fun j => if x (e.symm j) then (1 : ℝ) else -1)) else 0) = (fun _ => 0) := by
      funext x
      rw [if_neg (by
        rw [hG a _ (fillFree_sameSineFiber n a _)]
        exact hGa)]
    rw [hf,cubeAverage_const]
    exact hK
lemma integral_good_bad_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ)
    (G : (Fin m → ℝ) → Prop) (g : (Fin m → ℝ) → ℝ) :
    (∫ ω, g (fun j => ξ j.val ω) ∂μ) =
      (∫ ω, if G (fun j => ξ j.val ω) then g (fun j => ξ j.val ω) else 0 ∂μ)+
      ∫ ω, if G (fun j => ξ j.val ω) then 0 else g (fun j => ξ j.val ω) ∂μ := by
  rw [finite_sign_integral μ ξ hξ m g,finite_sign_integral μ ξ hξ m (fun a => if G a then g a else 0),
    finite_sign_integral μ ξ hξ m (fun a => if G a then 0 else g a),← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp
lemma integral_bad_bounded_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (m : ℕ)
    (G : (Fin m → ℝ) → Prop) (g : (Fin m → ℝ) → ℝ) (R : ℝ)
    (hbound : ∀ a ∈ signVectors m, g a ≤ R) :
    (∫ ω, if G (fun j => ξ j.val ω) then 0 else g (fun j => ξ j.val ω) ∂μ) ≤
      R*Prob μ {ω | ¬G (fun j => ξ j.val ω)} := by
  rw [finite_sign_event_indicator_integral μ ξ hξ m (fun a => ¬G a)]
  have hp (a : Fin m → ℝ) (ha : a ∈ signVectors m) :
      (if G a then 0 else g a) ≤ R*(if ¬G a then (1 : ℝ) else 0) := by
    by_cases hGa : G a <;> simp only [hGa,not_true_eq_false,not_false_eq_true,ite_true,ite_false,mul_zero,mul_one]
    · exact le_refl _
    · exact hbound a ha
  apply (finite_sign_integral_mono μ ξ hξ m _ _ hp).trans_eq
  have hi := finite_sign_integral μ ξ hξ m (fun a => if ¬G a then (1 : ℝ) else 0)
  change (∫ ω, if ¬G (fun j => ξ j.val ω) then (1 : ℝ) else 0 ∂μ) = _ at hi
  rw [finite_sign_integral μ ξ hξ m (fun a => R*(if ¬G a then (1 : ℝ) else 0))]
  calc
    _ = R*((2 : ℝ)⁻¹^m*∑ a ∈ signVectors m, if ¬G a then (1 : ℝ) else 0) := by
      rw [← mul_sum]
      ring
    _ = _ := congrArg (fun r : ℝ => R*r) hi.symm
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  split_ifs <;> rfl
end Fluctuations.SignFiberAverage
end
end

section
noncomputable section
open Finset Classical Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Fluctuations.SignUnconditionalCountEstimates
open SignFiberAverage SignActivityFiber SignPolynomialDivisibility FiniteCubeConvexTransport
lemma bulk_overlap_of_large_degree (n : ℕ) (hn : 514 ≤ n) :
    SignSineOccupancy.endpointCutoff ≤ Real.pi*n-SignSineOccupancy.endpointCutoff := by
  have hn' : (514 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.two_le_pi
  dsimp [SignSineOccupancy.endpointCutoff]
  nlinarith [mul_le_mul_of_nonneg_left hn' Real.pi_pos.le]
lemma actual_good_fiber_invariant (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hab : sameSineFiber n a b) :
    (¬SignSineOccupancy.occupancyBad n b ∧ ¬SignConditionalRows.maskBad n b) ↔
      (¬SignSineOccupancy.occupancyBad n a ∧ ¬SignConditionalRows.maskBad n a) := by
  rw [occupancyBad_congr n a b hab,SignConditionalRows.maskBad_congr n a b hab]
lemma actual_finite_discrepancy_eq (n : ℕ) (a : Fin (n+1) → ℝ) :
    discrepancy (finiteCoefficientSequence n) n a =
      (((coefficientPolynomial n (fun j => (a j : ℂ))).roots.filter
        (fun z => ‖z‖ ≤ 1)).card : ℝ)-(n : ℝ)/2 := by
  unfold discrepancy zeroCount
  rw [randomPolynomial_finiteCoefficientSequence]
lemma actual_finite_discrepancy_square_le (n : ℕ) (a : Fin (n+1) → ℝ) :
    discrepancy (finiteCoefficientSequence n) n a ^ 2 ≤ (n : ℝ)^2/4 := by
  have h := abs_discrepancy_le (finiteCoefficientSequence n) n a
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ n/2)).mpr h
  rw [sq_abs] at hs
  nlinarith
theorem exists_actual_combined_bad_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 514 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      Prob μ {ω | ¬(¬SignSineOccupancy.occupancyBad n (fun j => ξ j.val ω) ∧
        ¬SignConditionalRows.maskBad n (fun j => ξ j.val ω))} ≤ C*(n : ℝ)^(-3 : ℝ) := by
  obtain ⟨C,hC,n0,htail⟩ := SignSineOccupancy.exists_occupancy_tail μ ξ hξ
  refine ⟨C+48*(128*Real.pi+1)*2048^4,by positivity,max n0 514,le_max_right _ _,?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hnn : 0 < n := by have := (le_max_right n0 514).trans hn; omega
  have he : {ω | ¬(¬SignSineOccupancy.occupancyBad n (fun j => ξ j.val ω) ∧
        ¬SignConditionalRows.maskBad n (fun j => ξ j.val ω))} =
      {ω | SignSineOccupancy.occupancyBad n (fun j => ξ j.val ω)} ∪
        {ω | SignConditionalRows.maskBad n (fun j => ξ j.val ω)} := by ext ω; simp only [Set.mem_union,Set.mem_ofPred_eq]; tauto
  rw [he]
  have hu := measureReal_union_le (μ := μ)
    {ω | SignSineOccupancy.occupancyBad n (fun j => ξ j.val ω)}
    {ω | SignConditionalRows.maskBad n (fun j => ξ j.val ω)}
  apply hu.trans
  have ht := add_le_add (htail n hn0)
    (SignActivityMask.actual_mask_bad_probability_le_rpow μ ξ hξ n hnn)
  change Prob μ _+Prob μ _ ≤ _
  apply ht.trans_eq
  ring
theorem exists_actual_unconditional_count_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ Cs Cb : ℝ, 0 < Cs ∧ 0 < Cb ∧ ∃ n0 : ℕ, 514 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ δ t : ℝ, 0 < δ → 0 ≤ t →
      Prob μ {ω | 1+6*SignSineOccupancy.localThreshold n+
        3*Cs*((n : ℝ)*δ+Real.sqrt n)+16*t < |discrepancy ξ n ω|} ≤
      (32*Real.exp 81)*Real.exp (-(t^2*δ^2)/
        (64*((n : ℝ)+1)*(80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1))))+
          Cb*(n : ℝ)^(-3 : ℝ) := by
  obtain ⟨Cs,hCs,htail⟩ := SignClippedConvexity.exists_actual_good_fiber_count_tail
  obtain ⟨Cb,hCb,n0,hn0,hbad⟩ := exists_actual_combined_bad_tail μ ξ hξ
  refine ⟨Cs,Cb,hCs,hCb,n0,hn0,?_⟩
  intro n hn δ t hδ ht
  let G : (Fin (n+1) → ℝ) → Prop := fun a =>
    ¬SignSineOccupancy.occupancyBad n a ∧ ¬SignConditionalRows.maskBad n a
  let : DecidablePred G := fun a => Classical.propDecidable (G a)
  let T := 1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n)+16*t
  let g : (Fin (n+1) → ℝ) → ℝ := fun a =>
    if T < |discrepancy (finiteCoefficientSequence n) n a| then 1 else 0
  let K := (32*Real.exp 81)*Real.exp (-(t^2*δ^2)/
    (64*((n : ℝ)+1)*(80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1))))
  have hnn : 0 < n := by omega
  have hg : (∫ ω, if G (fun j => ξ j.val ω) then g (fun j => ξ j.val ω) else 0 ∂μ) ≤ K := by
    apply integral_on_good_le_of_cube_averages μ ξ hξ n G
      (actual_good_fiber_invariant n) g K (by dsimp only [K]; positivity)
    intro a ha hGa m e
    have he := htail n a m e hnn ha hGa.1 hGa.2 (bulk_overlap_of_large_degree n (hn0.trans hn)) δ t hδ ht
    simpa only [g,T,K,actual_finite_discrepancy_eq] using he
  have hb := integral_bad_bounded_le μ ξ hξ (n+1) G g 1 (by
    intro a _
    dsimp only [g]
    split_ifs <;> norm_num)
  have hs := integral_good_bad_split μ ξ hξ (n+1) G g
  have hf := finite_sign_event_indicator_integral μ ξ hξ (n+1)
    (fun a => T < |discrepancy (finiteCoefficientSequence n) n a|)
  have hprob : Prob μ {ω | T < |discrepancy ξ n ω|} = ∫ ω, g (fun j => ξ j.val ω) ∂μ := by
    simpa only [g,discrepancy_finiteCoefficientSequence] using hf
  change Prob μ {ω | T < |discrepancy ξ n ω|} ≤ K+Cb*(n : ℝ)^(-3 : ℝ)
  rw [hprob,hs]
  apply add_le_add hg
  apply hb.trans
  simpa only [G,one_mul] using hbad n hn
theorem exists_actual_unconditional_count_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ Cs Cb : ℝ, 0 < Cs ∧ 0 < Cb ∧ ∃ n0 : ℕ, 514 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ δ : ℝ, 0 < δ →
      (∫ ω, discrepancy ξ n ω ^ 2 ∂μ) ≤
      2*(1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n))^2+
        (65536*(1+32*Real.exp 81)*80*Real.pi)*((n : ℝ)+1)*
          ((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2+
            ((n : ℝ)^2/4)*(Cb*(n : ℝ)^(-3 : ℝ)) := by
  obtain ⟨Cs,hCs,hmoment⟩ := SignConditionalCountMoments.exists_actual_good_fiber_count_second_moment
  obtain ⟨Cb,hCb,n0,hn0,hbad⟩ := exists_actual_combined_bad_tail μ ξ hξ
  refine ⟨Cs,Cb,hCs,hCb,n0,hn0,?_⟩
  intro n hn δ hδ
  let G : (Fin (n+1) → ℝ) → Prop := fun a =>
    ¬SignSineOccupancy.occupancyBad n a ∧ ¬SignConditionalRows.maskBad n a
  let : DecidablePred G := fun a => Classical.propDecidable (G a)
  let g : (Fin (n+1) → ℝ) → ℝ := fun a => discrepancy (finiteCoefficientSequence n) n a^2
  let K := 2*(1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n))^2+
    (65536*(1+32*Real.exp 81)*80*Real.pi)*((n : ℝ)+1)*
      ((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2
  have hnn : 0 < n := by omega
  have hg : (∫ ω, if G (fun j => ξ j.val ω) then g (fun j => ξ j.val ω) else 0 ∂μ) ≤ K := by
    apply integral_on_good_le_of_cube_averages μ ξ hξ n G
      (actual_good_fiber_invariant n) g K (by dsimp only [K]; positivity)
    intro a ha hGa m e
    have he := hmoment n a m e hnn ha hGa.1 hGa.2 (bulk_overlap_of_large_degree n (hn0.trans hn)) δ hδ
    simpa only [g,K,actual_finite_discrepancy_eq] using he
  have hb := integral_bad_bounded_le μ ξ hξ (n+1) G g ((n : ℝ)^2/4)
    (fun a _ => actual_finite_discrepancy_square_le n a)
  have hs := integral_good_bad_split μ ξ hξ (n+1) G g
  have he : (∫ ω, discrepancy ξ n ω^2 ∂μ) = ∫ ω, g (fun j => ξ j.val ω) ∂μ := by
    simp only [g,discrepancy_finiteCoefficientSequence]
  change (∫ ω, discrepancy ξ n ω^2 ∂μ) ≤ K+((n : ℝ)^2/4)*(Cb*(n : ℝ)^(-3 : ℝ))
  rw [he,hs]
  apply add_le_add hg
  apply hb.trans
  exact mul_le_mul_of_nonneg_left (hbad n hn) (by positivity)
end Fluctuations.SignUnconditionalCountEstimates
end
end

section
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Fluctuations.SignCountOptimization
open SignUnconditionalCountEstimates
lemma quartic_scale_identities (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt x))^2 = Real.sqrt x ∧
    (Real.sqrt (Real.sqrt x))^4 = x ∧
    (Real.sqrt (Real.sqrt x))^3 = x^(3/4 : ℝ) ∧
    (Real.sqrt (Real.sqrt x))^6 = x^(3/2 : ℝ) := by
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg x)
  refine ⟨h2,?_,?_,?_⟩
  · rw [show (Real.sqrt (Real.sqrt x))^4 = ((Real.sqrt (Real.sqrt x))^2)^2 by ring,h2,Real.sq_sqrt hx]
  · rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx,← Real.rpow_natCast,
      ← Real.rpow_mul hx]
    norm_num
  · rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx,← Real.rpow_natCast,
      ← Real.rpow_mul hx]
    norm_num
lemma log_shift_le_four_sqrt (x : ℝ) (hx : 1 ≤ x) : Real.log (x+2) ≤ 4*Real.sqrt x := by
  have h := Real.log_le_rpow_div (by linarith : 0 ≤ x+2) (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at h
  have hs : Real.sqrt (x+2) ≤ 2*Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ x)]
    nlinarith
  linarith
lemma threshold_constant_pos :
    0 < 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2 := by
  have hr := SignSineOccupancy.evaluationRadius_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity
lemma localThreshold_eq_log (n : ℕ) :
    SignSineOccupancy.localThreshold n =
      (2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2)*Real.log ((n : ℝ)+2) := by
  dsimp [SignSineOccupancy.localThreshold,SignSineOccupancy.jensenScale]
  ring
lemma localThreshold_and_ceil_bound (n : ℕ) (hlog : 1 ≤ Real.log ((n : ℝ)+2)) :
    0 ≤ SignSineOccupancy.localThreshold n ∧
    (Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1 ≤
      (2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2+2)*Real.log ((n : ℝ)+2) := by
  have hc := threshold_constant_pos
  have hH : 0 ≤ SignSineOccupancy.localThreshold n := by rw [localThreshold_eq_log]; positivity
  refine ⟨hH,?_⟩
  have hceil := Nat.ceil_lt_add_one hH
  rw [localThreshold_eq_log] at hceil ⊢
  nlinarith
lemma smoothing_threshold_bound (n : ℕ) (hn : 1 ≤ (n : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (s : ℝ) (hs : 1 ≤ s) :
    1+6*SignSineOccupancy.localThreshold n+
      3*C*((n : ℝ)*(s/Real.sqrt (Real.sqrt n))+Real.sqrt n) ≤
    (1+24*(2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2)+6*C)*
      ((Real.sqrt (Real.sqrt n))^3*s) := by
  let q := Real.sqrt (Real.sqrt (n : ℝ))
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hn)
  obtain ⟨hq2,hq4,_,_⟩ := quartic_scale_identities (n : ℝ) (by linarith)
  change q^2 = Real.sqrt (n : ℝ) at hq2
  change q^4 = (n : ℝ) at hq4
  have hnd : (n : ℝ)*(s/q) = q^3*s := by rw [← hq4]; field_simp
  have hqs : 1 ≤ q*s := by
    calc
      1 = 1*1 := by ring
      _ ≤ q*s := mul_le_mul hq hs (by norm_num) (by linarith)
  have hqscale : q^2 ≤ q^3*s := by nlinarith [mul_nonneg (sq_nonneg q) (by linarith : 0 ≤ q*s-1)]
  have hscale : 1 ≤ q^3*s := by nlinarith [sq_nonneg (q-1)]
  have hlogb := log_shift_le_four_sqrt (n : ℝ) hn
  rw [← hq2] at hlogb
  have hc := threshold_constant_pos
  rw [localThreshold_eq_log]
  change 1+6*((2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2)*Real.log ((n : ℝ)+2))+
    3*C*((n : ℝ)*(s/q)+Real.sqrt n) ≤ _
  rw [hnd]
  have hroot : Real.sqrt (n : ℝ) ≤ q^3*s := hq2.symm.trans_le hqscale
  have hHb := mul_le_mul_of_nonneg_left hlogb hc.le
  have hCs := mul_le_mul_of_nonneg_left hroot hC
  have hqH := mul_le_mul_of_nonneg_left hqscale hc.le
  nlinarith
lemma actual_tail_smoothing_estimate (n : ℕ) (hn : 1 ≤ (n : ℝ))
    (hlog : 1 ≤ Real.log ((n : ℝ)+2)) :
    let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
    let D := 128*80*Real.pi*(h+2)
    let b := Real.sqrt (3*D)
    let q := Real.sqrt (Real.sqrt (n : ℝ))
    let r := Real.sqrt (Real.log ((n : ℝ)+2))
    Real.exp (-((b*q^3*r)^2*(r/q)^2)/
      (64*((n : ℝ)+1)*(80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)))) ≤
      (n : ℝ)^(-3 : ℝ) := by
  dsimp only
  let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
  let D := 128*80*Real.pi*(h+2)
  let b := Real.sqrt (3*D)
  let q := Real.sqrt (Real.sqrt (n : ℝ))
  let r := Real.sqrt (Real.log ((n : ℝ)+2))
  let l := Real.log ((n : ℝ)+2)
  let d := 64*((n : ℝ)+1)*(80*Real.pi*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1))
  have hh : 0 < h := threshold_constant_pos
  have hD : 0 < D := by dsimp only [D]; positivity
  have hn0 : (0 : ℝ) < n := by linarith
  have hq : 0 < q := by dsimp only [q]; positivity
  have hl : 0 < l := by dsimp only [l]; linarith
  have hr2 : r^2 = l := Real.sq_sqrt hl.le
  have hq4 : q^4 = (n : ℝ) := (quartic_scale_identities (n : ℝ) hn0.le).2.1
  have hb2 : b^2 = 3*D := Real.sq_sqrt (by positivity)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hceil := (localThreshold_and_ceil_bound n hlog).2
  change (Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1 ≤ (h+2)*l at hceil
  have hdl : d ≤ D*(n : ℝ)*l := by
    dsimp only [d,D]
    have hx1 : (n : ℝ)+1 ≤ 2*n := by linarith
    have h1 := mul_le_mul hx1 hceil (by positivity : 0 ≤ (Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1) (by positivity : (0 : ℝ) ≤ 2*n)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 64*80*Real.pi)]
  have hnum : (b*q^3*r)^2*(r/q)^2 = 3*D*(n : ℝ)*l^2 := by
    rw [div_pow]
    field_simp
    rw [hb2,hq4,show r^4 = l^2 by rw [show r^4 = (r^2)^2 by ring,hr2]]
  have hex : 3*l ≤ ((b*q^3*r)^2*(r/q)^2)/d := by
    apply (le_div_iff₀ hd).mpr
    rw [hnum]
    have he := mul_le_mul_of_nonneg_left hdl (by positivity : 0 ≤ 3*l)
    nlinarith
  have hlogn : Real.log (n : ℝ) ≤ l := Real.log_le_log hn0 (by linarith)
  change Real.exp (-((b*q^3*r)^2*(r/q)^2)/d) ≤ _
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith
theorem exists_eventual_actual_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Prob μ {ω | A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) <
        |discrepancy ξ n ω|} ≤ C*(n : ℝ)^(-3 : ℝ) := by
  obtain ⟨Cs,Cb,hCs,hCb,n0,hn0,htail⟩ := exists_actual_unconditional_count_tail μ ξ hξ
  let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
  let D := 128*80*Real.pi*(h+2)
  let b := Real.sqrt (3*D)
  let A := 1+24*h+6*Cs+16*b
  have hh : 0 < h := threshold_constant_pos
  have hD : 0 < D := by dsimp only [D]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨A,32*Real.exp 81+Cb,by dsimp only [A]; positivity,by positivity,?_⟩
  have htop : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ)+2) tendsto_natCast_atTop_atTop
  have hlogev := (Real.tendsto_log_atTop.comp htop).eventually_ge_atTop (1 : ℝ)
  filter_upwards [eventually_ge_atTop n0,hlogev] with n hn hlog
  have hn1 : 1 ≤ (n : ℝ) := by
    have hnNat : 1 ≤ n := by omega
    exact_mod_cast hnNat
  let q := Real.sqrt (Real.sqrt (n : ℝ))
  let r := Real.sqrt (Real.log ((n : ℝ)+2))
  have hq : 0 < q := by dsimp only [q]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr hlog
  have hscale := (quartic_scale_identities (n : ℝ) (by linarith)).2.2.1
  change q^3 = (n : ℝ)^(3/4 : ℝ) at hscale
  have hthreshold := smoothing_threshold_bound n hn1 Cs hCs.le r hr1
  have hthreshold' : 1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*(r/q)+Real.sqrt n)+16*(b*q^3*r) ≤
      A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
    rw [← hscale]
    dsimp only [A]
    change _ ≤ (1+24*h+6*Cs+16*b)*(q^3*r)
    change _ ≤ (1+24*h+6*Cs)*(q^3*r) at hthreshold
    nlinarith
  have hp := measureReal_mono (μ := μ) (show
      {ω | A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) < |discrepancy ξ n ω|} ⊆
      {ω | 1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*(r/q)+Real.sqrt n)+16*(b*q^3*r) < |discrepancy ξ n ω|} from
      fun ω hω => lt_of_le_of_lt hthreshold' hω)
  apply hp.trans
  apply (htail n hn (r/q) (b*q^3*r) (by positivity) (by positivity)).trans
  have he := actual_tail_smoothing_estimate n hn1 hlog
  change Real.exp (-((b*q^3*r)^2*(r/q)^2)/_) ≤ (n : ℝ)^(-3 : ℝ) at he
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 32*Real.exp 81)
  nlinarith
set_option maxHeartbeats 800000 in
lemma actual_second_moment_smoothing_estimate (n : ℕ) (hn : 1 ≤ (n : ℝ))
    (hlog : 1 ≤ Real.log ((n : ℝ)+2)) (Cs Cb : ℝ) (hCs : 0 ≤ Cs) (hCb : 0 ≤ Cb) :
    let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
    let B := 1+24*h+6*Cs
    let K := 65536*(1+32*Real.exp 81)*80*Real.pi
    let q := Real.sqrt (Real.sqrt (n : ℝ))
    let r := Real.sqrt (Real.log ((n : ℝ)+2))
    let δ := Real.sqrt r/q
    2*(1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n))^2+
      K*((n : ℝ)+1)*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2+
        ((n : ℝ)^2/4)*(Cb*(n : ℝ)^(-3 : ℝ)) ≤
    (2*B^2+2*K*(h+2)+Cb)*((n : ℝ)^(3/2 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
  dsimp only
  let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
  let B := 1+24*h+6*Cs
  let K := 65536*(1+32*Real.exp 81)*80*Real.pi
  let q := Real.sqrt (Real.sqrt (n : ℝ))
  let r := Real.sqrt (Real.log ((n : ℝ)+2))
  let s := Real.sqrt r
  let δ := s/q
  let l := Real.log ((n : ℝ)+2)
  have hh : 0 < h := threshold_constant_pos
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hn0 : (0 : ℝ) < n := by linarith
  have hq : 0 < q := by dsimp only [q]; positivity
  have hq1 : 1 ≤ q := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hn)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr hlog
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hr1
  have hs2 : s^2 = r := Real.sq_sqrt hr.le
  have hr2 : r^2 = l := Real.sq_sqrt (by linarith)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨_,hq4,_,hq6⟩ := quartic_scale_identities (n : ℝ) hn0.le
  change q^4 = (n : ℝ) at hq4
  change q^6 = (n : ℝ)^(3/2 : ℝ) at hq6
  have ht := smoothing_threshold_bound n hn Cs hCs s hs1
  change 1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n) ≤ B*(q^3*s) at ht
  have ht0 : 0 ≤ 1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n) := by
    have hH := (localThreshold_and_ceil_bound n hlog).1
    positivity
  have hts := (sq_le_sq₀ ht0 (by positivity : 0 ≤ B*(q^3*s))).mpr ht
  have hts' : (1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n))^2 ≤ B^2*q^6*r := by
    convert! hts using 1
    rw [mul_pow,mul_pow,hs2]
    ring
  have hceil := (localThreshold_and_ceil_bound n hlog).2
  change (Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1 ≤ (h+2)*l at hceil
  have hn1 : (n : ℝ)+1 ≤ 2*n := by linarith
  have hprod := mul_le_mul hn1 hceil (by positivity : 0 ≤ (Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1) (by positivity : (0 : ℝ) ≤ 2*n)
  have hframe : (((n : ℝ)+1)*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1))/δ^2 ≤ 2*(h+2)*q^6*r := by
    apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
    apply hprod.trans_eq
    change (2*(n : ℝ))*((h+2)*l) = (2*(h+2)*q^6*r)*(s/q)^2
    field_simp
    rw [hs2,← hq4,← hr2]
    ring
  have hframe' := mul_le_mul_of_nonneg_left hframe hK.le
  have hbad : (n : ℝ)^2*(n : ℝ)^(-3 : ℝ) ≤ 1 := by
    have he := Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (-3 : ℝ) ≤ -2)
    apply (mul_le_mul_of_nonneg_left he (sq_nonneg (n : ℝ))).trans_eq
    rw [Real.rpow_neg hn0.le,show (2 : ℝ) = (2 : ℕ) by norm_num,Real.rpow_natCast]
    exact mul_inv_cancel₀ (by positivity)
  have htarg : 1 ≤ q^6*r := by
    have hpow : 1 ≤ q^6 := one_le_pow₀ hq1
    nlinarith [mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ q^6)]
  have hbad' : ((n : ℝ)^2/4)*(Cb*(n : ℝ)^(-3 : ℝ)) ≤ Cb*(q^6*r) := by
    have he := mul_le_mul_of_nonneg_left hbad hCb
    have ht' := mul_le_mul_of_nonneg_left htarg hCb
    nlinarith [mul_nonneg hCb (Real.rpow_nonneg hn0.le (-3 : ℝ))]
  change 2*(1+6*SignSineOccupancy.localThreshold n+3*Cs*((n : ℝ)*δ+Real.sqrt n))^2+
    K*((n : ℝ)+1)*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2+
    ((n : ℝ)^2/4)*(Cb*(n : ℝ)^(-3 : ℝ)) ≤ (2*B^2+2*K*(h+2)+Cb)*((n : ℝ)^(3/2 : ℝ)*r)
  rw [← hq6]
  have hfr : K*((n : ℝ)+1)*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1)/δ^2 =
      K*((((n : ℝ)+1)*((Nat.ceil (SignSineOccupancy.localThreshold n) : ℝ)+1))/δ^2) := by ring
  rw [hfr]
  calc
    _ ≤ 2*(B^2*q^6*r)+K*(2*(h+2)*q^6*r)+Cb*(q^6*r) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hts' (by norm_num)) hframe') hbad'
    _ = _ := by ring
theorem exists_eventual_actual_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, discrepancy ξ n ω^2 ∂μ) ≤
        C*((n : ℝ)^(3/2 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
  obtain ⟨Cs,Cb,hCs,hCb,n0,hn0,hmoment⟩ := exists_actual_unconditional_count_second_moment μ ξ hξ
  let h := 2*(SignSineOccupancy.evaluationRadius+2)/Real.log 2
  let B := 1+24*h+6*Cs
  let K := 65536*(1+32*Real.exp 81)*80*Real.pi
  have hh : 0 < h := threshold_constant_pos
  refine ⟨2*B^2+2*K*(h+2)+Cb,by dsimp only [K]; positivity,?_⟩
  have htop : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ)+2) tendsto_natCast_atTop_atTop
  have hlogev := (Real.tendsto_log_atTop.comp htop).eventually_ge_atTop (1 : ℝ)
  filter_upwards [eventually_ge_atTop n0,hlogev] with n hn hlog
  have hn1 : 1 ≤ (n : ℝ) := by
    have hnNat : 1 ≤ n := by omega
    exact_mod_cast hnNat
  let δ := Real.sqrt (Real.sqrt (Real.log ((n : ℝ)+2)))/Real.sqrt (Real.sqrt (n : ℝ))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  apply (hmoment n hn δ hδ).trans
  exact actual_second_moment_smoothing_estimate n hn1 hlog Cs Cb hCs.le hCb.le
end Fluctuations.SignCountOptimization
end
end

section
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Fluctuations.SignAllDegreeCountRate
open SignCountOptimization SignFiberAverage
lemma shifted_log_scale_lower_bound (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt (Real.log 3) ≤ (n : ℝ)^p*Real.sqrt (Real.log ((n : ℝ)+2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (Real.log 3) ≤ Real.sqrt (Real.log ((n : ℝ)+2)) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith))
  have hr := Real.one_le_rpow hn1 hp
  exact hs.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hr)
lemma native_second_moment_le_quarter_degree {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) (n : ℕ) :
    (∫ ω, discrepancy ξ n ω^2 ∂μ) ≤ (n : ℝ)^2/4 := by
  have he := finite_sign_integral_mono μ ξ hξ (n+1)
    (fun a => discrepancy (finiteCoefficientSequence n) n a^2)
    (fun _ => (n : ℝ)^2/4)
    (fun a _ => SignUnconditionalCountEstimates.actual_finite_discrepancy_square_le n a)
  simpa only [discrepancy_finiteCoefficientSequence,integral_const,probReal_univ,one_smul] using he
theorem exists_actual_all_degree_count_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hξ : IsRademacherSequence μ ξ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Prob μ {ω | A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) <
        |discrepancy ξ n ω|} ≤ C*(n : ℝ)^(-3 : ℝ) ∧
      (∫ ω, discrepancy ξ n ω^2 ∂μ) ≤
        C*((n : ℝ)^(3/2 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
  obtain ⟨At,Ct,hAt,hCt,ht⟩ := exists_eventual_actual_tail μ ξ hξ
  obtain ⟨Cm,hCm,hm⟩ := exists_eventual_actual_second_moment μ ξ hξ
  obtain ⟨N,hN⟩ := eventually_atTop.1 (ht.and hm)
  let r := Real.sqrt (Real.log 3)
  let A := At+(N : ℝ)/(2*r)
  let C := Ct+Cm+(N : ℝ)^2/(4*r)
  have hr : 0 < r := by dsimp only [r]; exact Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAA : At ≤ A := by
    have hz : 0 ≤ (N : ℝ)/(2*r) := by positivity
    dsimp only [A]
    linarith
  have hCCt : Ct ≤ C := by
    have hz : 0 ≤ (N : ℝ)^2/(4*r) := by positivity
    dsimp only [C]
    linarith
  have hCCm : Cm ≤ C := by
    have hz : 0 ≤ (N : ℝ)^2/(4*r) := by positivity
    dsimp only [C]
    linarith
  refine ⟨A,C,hA,hC,?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := shifted_log_scale_lower_bound n hn (3/4 : ℝ) (by norm_num)
  have hlm := shifted_log_scale_lower_bound n hn (3/2 : ℝ) (by norm_num)
  change r ≤ (n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2)) at hl
  change r ≤ (n : ℝ)^(3/2 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2)) at hlm
  by_cases hlarge : N ≤ n
  · obtain ⟨htn,hmn⟩ := hN n hlarge
    constructor
    · have he := measureReal_mono (μ := μ) (show
        {ω | A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) < |discrepancy ξ n ω|} ⊆
        {ω | At*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) < |discrepancy ξ n ω|} from
        fun ω hω => lt_of_le_of_lt (mul_le_mul_of_nonneg_right hAA (by positivity)) hω)
      exact he.trans (htn.trans (mul_le_mul_of_nonneg_right hCCt (Real.rpow_nonneg hn0.le _)))
    · apply hmn.trans
      exact mul_le_mul_of_nonneg_right hCCm (by positivity)
  · have hsmall : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
    have htbound : (n : ℝ)/2 ≤ A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
      have hc : (N : ℝ)/(2*r) ≤ A := by dsimp only [A]; linarith
      have hm1 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (N : ℝ)/(2*r))
      have hm2 := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2)))
      have he : (N : ℝ)/(2*r)*r = (N : ℝ)/2 := by field_simp
      rw [he] at hm1
      linarith
    constructor
    · have he : {ω | A*((n : ℝ)^(3/4 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) < |discrepancy ξ n ω|} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hd := abs_discrepancy_le ξ n ω
        exact (not_lt_of_ge (hd.trans htbound)) hω
      rw [he]
      simp only [Prob,measure_empty,ENNReal.toReal_zero]
      positivity
    · apply (native_second_moment_le_quarter_degree μ ξ hξ n).trans
      have hc : (N : ℝ)^2/(4*r) ≤ C := by dsimp only [C]; linarith
      have hm1 := mul_le_mul_of_nonneg_left hlm (by positivity : 0 ≤ (N : ℝ)^2/(4*r))
      have hm2 := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (n : ℝ)^(3/2 : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2)))
      have he : (N : ℝ)^2/(4*r)*r = (N : ℝ)^2/4 := by field_simp
      rw [he] at hm1
      have hnN := (sq_le_sq₀ hn0.le (Nat.cast_nonneg N)).mpr hsmall
      linarith
end Fluctuations.SignAllDegreeCountRate
end
end

section
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Fluctuations
variable {Ω : Type*} [MeasurableSpace Ω]
def signFluctuationScale (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (3 / 4 : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))
theorem signRate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → ℝ) (hξ : IsRademacherSequence μ ξ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Prob μ {ω | A * signFluctuationScale n < |discrepancy ξ n ω|} ≤
        C * Real.rpow (n : ℝ) (-3 : ℝ) ∧
      (∫ ω, discrepancy ξ n ω ^ 2 ∂μ) ≤
        C * Real.rpow (n : ℝ) (3 / 2 : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) := by
  simpa only [signFluctuationScale,Real.rpow_eq_pow,mul_assoc] using
    SignAllDegreeCountRate.exists_actual_all_degree_count_rate μ ξ hξ
end Fluctuations
end
end

section
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace Fluctuations
universe u
namespace SignsAnyCoupling
instance isProbabilityMeasure_rademacherLaw : IsProbabilityMeasure rademacherLaw :=
  ⟨by
    norm_num [rademacherLaw]
    exact ENNReal.inv_two_add_inv_two⟩
theorem coordinate_isRademacherSequence :
    IsRademacherSequence (Measure.infinitePi fun _ : ℕ => rademacherLaw)
      (fun j (ω : ℕ → ℝ) => ω j) := by
  have hmap (j : ℕ) : Measure.map (fun ω : ℕ → ℝ => ω j)
      (Measure.infinitePi fun _ : ℕ => rademacherLaw) = rademacherLaw :=
    Measure.infinitePi_map_eval _ j
  exact ⟨⟨fun j => (measurable_pi_apply j).aemeasurable,
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id),
    fun j => ⟨(measurable_pi_apply j).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [hmap, hmap]⟩⟩, hmap 0⟩
theorem measure_signVector_mem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (Y : Fin (n + 1) → Ω → ℝ) (hind : iIndepFun Y μ)
    (hlaw : ∀ j, HasLaw (Y j) rademacherLaw μ) (T : Set (Fin (n + 1) → ℝ)) :
    μ {ω | (fun j => Y j ω) ∈ T} =
      Measure.pi (fun _ : Fin (n + 1) => rademacherLaw)
        (T ∩ ↑(SignPolynomialDivisibility.signVectors (n + 1))) := by
  set S : Set (Fin (n + 1) → ℝ) := ↑(SignPolynomialDivisibility.signVectors (n + 1)) with hSdef
  have hX : AEMeasurable (fun ω j => Y j ω) μ :=
    aemeasurable_pi_lambda _ fun j => (hlaw j).aemeasurable
  have hmap : μ.map (fun ω j => Y j ω) = Measure.pi (fun _ : Fin (n + 1) => rademacherLaw) := by
    rw [hind.map_fun_eq_pi_map fun j => (hlaw j).aemeasurable]
    congr 1
    funext j
    exact (hlaw j).map_eq
  have hS : ∀ᵐ ω ∂μ, (fun j => Y j ω) ∈ S := by
    have hj : ∀ j, ∀ᵐ ω ∂μ, Y j ω = 1 ∨ Y j ω = -1 := by
      intro j
      have hs : ∀ᵐ x ∂rademacherLaw, x = 1 ∨ x = -1 := by
        simp [rademacherLaw]
      rw [← (hlaw j).map_eq] at hs
      exact ae_of_ae_map (hlaw j).aemeasurable hs
    filter_upwards [ae_all_iff.mpr hj] with ω hω
    rw [hSdef, Finset.mem_coe, SignPolynomialDivisibility.mem_signVectors]
    exact hω
  have hTS : MeasurableSet (T ∩ S) :=
    ((SignPolynomialDivisibility.signVectors (n + 1)).finite_toSet.subset
      Set.inter_subset_right).measurableSet
  calc μ {ω | (fun j => Y j ω) ∈ T} = μ ((fun ω j => Y j ω) ⁻¹' (T ∩ S)) := by
        apply measure_congr
        filter_upwards [hS] with ω hω
        exact propext ⟨fun h => ⟨h, hω⟩, fun h => h.1⟩
    _ = _ := by rw [← Measure.map_apply_of_aemeasurable hX hTS, hmap]
end SignsAnyCoupling
open SignsAnyCoupling
theorem sign_tail_uniform : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ξ : ℕ → Ω → ℝ) (n : ℕ), 1 ≤ n →
      iIndepFun (fun j : Fin (n + 1) => ξ j) μ →
      (∀ j, j ≤ n → HasLaw (ξ j) rademacherLaw μ) →
      Prob μ {ω | A * signFluctuationScale n < |discrepancy ξ n ω|} ≤
        C * Real.rpow (n : ℝ) (-3 : ℝ) := by
  let P₀ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => rademacherLaw
  let ξ₀ : ℕ → (ℕ → ℝ) → ℝ := fun j ω => ω j
  have hξ₀ : IsRademacherSequence P₀ ξ₀ := coordinate_isRademacherSequence
  obtain ⟨A, C, hA, hC, hrate⟩ := signRate P₀ ξ₀ hξ₀
  refine ⟨A, C, hA, hC, fun μ _ ξ n hn hind hlaw => ?_⟩
  let T : Set (Fin (n + 1) → ℝ) :=
    {a | A * signFluctuationScale n < |discrepancy (finiteCoefficientSequence n) n a|}
  have hevent : {ω | A * signFluctuationScale n < |discrepancy ξ n ω|} =
      {ω | (fun j : Fin (n + 1) => ξ j ω) ∈ T} := by
    ext ω
    show A * signFluctuationScale n < |discrepancy ξ n ω| ↔
      A * signFluctuationScale n < |discrepancy (finiteCoefficientSequence n) n (fun j => ξ j ω)|
    rw [discrepancy_finiteCoefficientSequence]
  have hevent₀ : {ω | A * signFluctuationScale n < |discrepancy ξ₀ n ω|} =
      {ω | (fun j : Fin (n + 1) => ξ₀ j ω) ∈ T} := by
    ext ω
    show A * signFluctuationScale n < |discrepancy ξ₀ n ω| ↔
      A * signFluctuationScale n < |discrepancy (finiteCoefficientSequence n) n (fun j => ξ₀ j ω)|
    rw [discrepancy_finiteCoefficientSequence]
  have hμ := measure_signVector_mem μ n (fun j => ξ j) hind
    (fun j => hlaw j (Nat.lt_succ_iff.mp j.isLt)) T
  have h₀ := measure_signVector_mem P₀ n (fun j => ξ₀ j)
    (hξ₀.1.2.1.precomp Fin.val_injective)
    (fun j => ⟨hξ₀.1.1 j, (hξ₀.1.2.2 j).map_eq.trans hξ₀.2⟩) T
  have hrate' := (hrate n hn).1
  unfold Prob at hrate' ⊢
  rw [hevent, hμ, ← h₀, ← hevent₀]
  exact hrate'
end Fluctuations
end
end
/- Transfer real random-sign bounds to the complex-coefficient model of Erdős 522. -/

namespace OMA.Yakir522

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal Classical

private theorem coin_card : Measure.count ({-1, 1} : Set ℂ) = 2 := by
  rw [Measure.count_apply_finite _ (Set.toFinite _)]
  have h : (Set.toFinite ({-1, 1} : Set ℂ)).toFinset = {-1, 1} := by ext z; simp
  rw [h, Finset.card_pair (by norm_num)]
  norm_num

private theorem complex_sign_law :
    ProbabilityTheory.cond Measure.count ({-1,1} : Set ℂ) =
      (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℂ) + (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℂ) := by
  rw [ProbabilityTheory.cond, coin_card]
  rw [show ({-1,1} : Set ℂ) = {1} ∪ {-1} by ext z; simp [or_comm]]
  rw [Measure.restrict_union (by simp; norm_num : Disjoint ({1} : Set ℂ) {-1}) (measurableSet_singleton _)]
  simp [Measure.restrict_singleton, smul_add, one_div]

private theorem sign_real {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (f : Erdos522.KacCoefficients ({-1, 1} : Set ℂ) Ω) (j : ℕ) :
    HasLaw (fun ω => (f j ω).re)
      ((1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) ℙ ∧
      ∀ᵐ ω, ((f j ω).re : ℂ) = f j ω := by
  have hm : AEMeasurable (f j) ℙ := (f.h_unif j).aemeasurable (by rw [coin_card]; norm_num) (by rw [coin_card]; norm_num)
  have he : (ℙ : Measure Ω).map (f j) = _ := (f.h_unif j).trans complex_sign_law
  have hr := Complex.continuous_re.measurable
  constructor
  · refine ⟨hr.comp_aemeasurable hm, ?_⟩
    change Measure.map (Complex.re ∘ f j) ℙ = _
    rw [← AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hm, he,
      Measure.map_add _ _ hr, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' hr, Measure.map_dirac' hr]
    simp
  · apply ae_of_ae_map (p := fun z : ℂ => (z.re : ℂ) = z) hm
    rw [he]
    simp

/-- The fluctuation scale is eventually strictly below the threshold in Yakir's theorem. -/
theorem scale (A : ℝ) (hA : 0 < A) : ∀ᶠ n : ℕ in atTop,
    A * ((n : ℝ)^(3/4 : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))) < (n : ℝ)^(9/10 : ℝ) := by
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 3/10)).bound
    (by positivity : 0 < 1 / (4*A^2))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hl, eventually_ge_atTop 2]
    with n hn h2
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast h2
  have hpos : 0 < (n:ℝ) := by linarith
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ n by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (Real.rpow_nonneg hpos.le _)] at hn
  have hL : Real.log ((n:ℝ) + 2) ≤ 2 * Real.log n := by
    apply (Real.log_le_log (by positivity) (show (n:ℝ)+2 ≤ (n:ℝ)^2 by nlinarith)).trans
    rw [Real.log_pow]; norm_num
  have hr := Real.rpow_pos_of_pos hpos (3/20 : ℝ)
  have hsplit : ((n:ℝ)^(3/20 : ℝ))^2 = (n:ℝ)^(3/10 : ℝ) := by
    rw [← Real.rpow_mul_natCast hpos.le]; norm_num
  have hlog2 := Real.log_nonneg (show (1:ℝ) ≤ n+2 by linarith)
  have hcoef : 0 < 4*A^2 := by positivity
  have hbound : 4*A^2 * Real.log n ≤ (n:ℝ)^(3/10 : ℝ) := by
    have hb := (le_div_iff₀ hcoef).mp (show Real.log n ≤ (n:ℝ)^(3/10 : ℝ)/(4*A^2) by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hn); linarith
  have hroot : A * Real.sqrt (Real.log ((n:ℝ)+2)) < (n:ℝ)^(3/20 : ℝ) := by
    by_contra! nh
    have hs := mul_self_le_mul_self hr.le nh
    nlinarith only [hs, hsplit, Real.sq_sqrt hlog2, hbound, mul_le_mul_of_nonneg_left hL (sq_nonneg A), sq_pos_of_pos hr]
  calc
    _ = (n:ℝ)^(3/4:ℝ) * (A * Real.sqrt (Real.log ((n:ℝ)+2))) := by ring
    _ < (n:ℝ)^(3/4:ℝ) * (n:ℝ)^(3/20:ℝ) := mul_lt_mul_of_pos_left hroot (by positivity)
    _ = _ := by rw [← Real.rpow_add hpos]; norm_num

/-- The signed discrepancy of the closed disk root count for real coefficient functions. -/
noncomputable def discrepancy {Ω : Type*} (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let p : Polynomial ℂ := ∑ i ∈ Finset.range (n+1), Polynomial.monomial i ((ξ i ω : ℝ) : ℂ)
  ((p.roots.filter fun z => ‖z‖ ≤ 1).card : ℝ) - (n:ℝ)/2

/-- Apply a uniform real random-sign tail bound to every complex Kac model. -/
theorem from_tail
    (ht : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ξ : ℕ → Ω → ℝ) (n : ℕ), 1 ≤ n →
        iIndepFun (fun j : Fin (n+1) => ξ j) μ →
        (∀ j, j ≤ n → HasLaw (ξ j)
          ((1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) μ) →
        (μ {ω | A * ((n:ℝ)^(3/4:ℝ) * Real.sqrt (Real.log ((n:ℝ)+2))) < |discrepancy ξ n ω|}).toReal ≤
          C * (n:ℝ)^(-3:ℝ)) : type_of% @Erdos522.erdos_522.variants.yakir_solution.{u} := by
  obtain ⟨A, C, hA, hC, htail⟩ := ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp (scale A hA)
  refine ⟨fun n => if K ≤ n then C * (n:ℝ)^(-3:ℝ) else 1, ?_, ?_⟩
  · have hlim := (tendsto_rpow_neg_atTop (by norm_num : 0 < (3:ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply (show Tendsto (fun n : ℕ => C * (n:ℝ)^(-(3:ℝ))) atTop (𝓝 0) by
      simpa using hlim.const_mul C).congr'
    filter_upwards [eventually_ge_atTop K] with n hn
    simp [hn]
  · intro Ω _ _ n hn f
    by_cases hnK : K ≤ n
    · simp only [if_pos hnK]
      let ξ (j : ℕ) (ω : Ω) := (f j ω).re
      have hind : iIndepFun (fun j : Fin (n+1) => ξ j) ℙ :=
        (f.h_indep.comp (fun _ => Complex.re) (fun _ => Complex.continuous_re.measurable)).precomp Fin.val_injective
      have tail := htail (ℙ : Measure Ω) ξ n (by omega) hind (fun j _ => (sign_real f j).1)
      apply le_trans _ tail
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [ae_all_iff.mpr (fun j => (sign_real f j).2)] with ω hω
      intro hbad
      change (n:ℝ)^(9/10:ℝ) ≤ |((f.roots n ω).countP (· ∈ Metric.closedBall 0 1) : ℝ) - (n:ℝ)/2| at hbad
      have he : (∑ i ∈ Finset.range (n+1), Polynomial.monomial i (((ξ i ω):ℝ):ℂ)) =
          f.polynomial n ω := Finset.sum_congr rfl (fun i _ => congrArg (Polynomial.monomial i) (hω i))
      change _ < |discrepancy ξ n ω|
      apply (hK n hnK).trans_le
      simpa only [Erdos522.KacCoefficients.roots, discrepancy, he, Multiset.countP_eq_card_filter,
        Metric.mem_closedBall, dist_zero_right] using hbad
    · simpa [hnK] using (show (ℙ _).toReal ≤ 1 from by
        rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) (prob_le_one))

end OMA.Yakir522

theorem OMA.solution : type_of% @Erdos522.erdos_522.variants.yakir_solution :=
  OMA.Yakir522.from_tail Fluctuations.sign_tail_uniform

/- Source and modifications


The concentration estimate is excerpted and adapted from Sebastien Kawada's
chreia/erdos-522, revision c261d2e4754f4eacf7548f4cde346199dede6454.
https://github.com/chreia/erdos-522
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
PolynomialRouche, adapted from hex-roots-mathlib, is copyright (c) 2026
Lean FRO, LLC. All rights reserved. Author: Kim Morrison. Modifications
copyright (c) 2026 Sebastien Kawada. Both are licensed under Apache 2.0.
This version selects and combines the dependencies of sign_tail_uniform,
adapts proofs to Lean 4.33.1, and transfers that estimate to the catalogue's
complex coefficients and different deviation threshold.

Upstream project's NOTICE (some components are not included in this excerpt):
Universal Radial Laws for Random Polynomials: Erdős Problem #522 and
Non-Universal Fluctuations. Lean formalization
Copyright 2026 Sebastien Kawada

This product is licensed under the Apache License, Version 2.0. It includes
the following software by other authors, each licensed under the Apache
License, Version 2.0, and ported to Lean 4.34 for this formalization:

  ProbabilityApproximation, by Asher Yan
  https://github.com/Polarnova/ProbabilityApproximation
  upstream release v0.9.6, revision c89fba908a33ba741836407f43c67609e2d05279
  in lean/vendor/ProbabilityApproximation

  SLT (Statistical Learning Theory in Lean 4), by Yuanhe Zhang, Jason D. Lee,
  Fanghui Liu and contributors
  https://github.com/YuanheZ/lean-stat-learning-theory
  upstream revision 482a1a56daf792b33afe8cf7f07f127dc0af8640
  in lean/vendor/SLT

It also includes files adapted from:

  hex-roots-mathlib, Copyright 2026 Lean FRO, LLC, by Kim Morrison
  https://github.com/leanprover/hex-roots-mathlib
  commit 9bcfb127d85e33c877d3e68d19385b115d7d45b9
  in lean/Erdos522/Stability/PolynomialRouche.lean
  (license in lean/third_party/hex-roots-mathlib/LICENSE)

  Mathlib, Copyright 2023 Sébastien Gouëzel
  https://github.com/leanprover-community/mathlib4
  commit 5ed2965256430c3649e86755f9576b54eca72435
  a construction adapted in lean/Fluctuations/Probability/GaussianRadialIntegrability.lean

It also includes definitions and a statement copied from:

  formal-conjectures, Copyright 2025 The Formal Conjectures Authors
  https://github.com/google-deepmind/formal-conjectures
  commit 2424bb480c590237ffbb2cc831ae4cb8977e045a
  in lean/Erdos522/Bridge/FormalConjectures.lean

Each of these files keeps its original copyright notice. Erdos522Web.lean
gathers the sources of the proof of Erdős Problem #522 in one file and keeps
the copyright notice of each.


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

   Copyright 2026 Sebastien Kawada

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
