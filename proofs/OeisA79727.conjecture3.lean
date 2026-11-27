import FormalConjectures.OEIS.«79727»
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Bala's third conjecture on the cubes of central binomial coefficients

The main theorem is `BalaThird.conjecture3`. The elliptic congruence is
`BalaElliptic.eligible`. The final declaration matches the registry target.
Credit: @MuncyIO. Proof developed with OpenAI Codex.
-/
namespace BalaAudit

open PowerSeries

section Coefficients
variable {R : Type*} [CommRing R] {f v : PowerSeries R} {p : R} {q : ℕ}

/-- Below q, multiplying m times supplies m factors of p. -/
theorem below (hf : ∀ i < q, p ∣ coeff i f) (m : ℕ) :
    ∀ n < q, p ^ m ∣ coeff n (f ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro n hn
    rw [pow_succ p, pow_succ f, coeff_mul]
    apply Finset.dvd_sum
    intro ij hij
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    exact mul_dvd_mul (ih ij.1 (by omega)) (hf ij.2 (by omega))

/-- At q the same bound holds for powers m ≥ 2 because both endpoint terms vanish. -/
theorem at_boundary (hf : ∀ i < q, p ∣ coeff i f) (h0 : constantCoeff f = 0)
    (m : ℕ) : p ^ (m + 2) ∣ coeff q (f ^ (m + 2)) := by
  rw [pow_succ p, pow_succ f, coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · simp [hi, coeff_zero_eq_constantCoeff_apply, h0]
  by_cases hj : ij.2 = 0
  · simp [hj, coeff_zero_eq_constantCoeff_apply, h0]
  exact mul_dvd_mul (below hf (m+1) ij.1 (by omega)) (hf ij.2 (by omega))

/-- If U=fV, V(0)=1, and the lower coefficients of f and the positive
coefficients of V vanish modulo p, then U_q=f_q modulo p². -/
theorem numerator_precision (hf : ∀ i < q, p ∣ coeff i f)
    (hv : ∀ j, 0 < j → j ≤ q → p ∣ coeff j v) (h0 : coeff 0 v = 1) :
    p ^ 2 ∣ coeff q (f * v) - coeff q f := by
  classical
  rw [coeff_mul]
  have hm : (q, 0) ∈ Finset.HasAntidiagonal.antidiagonal q := Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero q)
  rw [← Finset.sum_erase_add _ _ hm]
  simp only [h0, mul_one, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro ij hij
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
  have hj : 0 < ij.2 := by
    by_contra! hz
    exact hne (Prod.ext (by omega) (by omega))
  rw [pow_two]
  exact mul_dvd_mul (hf ij.1 (by omega)) (hv ij.2 hj (by omega))

end Coefficients

/-- Coprime polynomial coordinates satisfying f(1/t)=1/f(t) have leading
numerator coefficient of square one when the denominator at zero is one.
The crossed product is the polynomial form of the rational-function identity. -/
theorem reciprocal_square {K : Type*} [Field K] {q : ℕ}
    (U V : Polynomial K) (hu : U ≠ 0) (hc : IsCoprime U V)
    (hdeg : U.natDegree = q) (hvdeg : V.natDegree ≤ q) (hv0 : V.coeff 0 = 1)
    (hs : U * U.reflect q = V * V.reflect q) : (U.coeff q)^2 = 1 := by
  have hd : U ∣ V.reflect q := hc.dvd_of_dvd_mul_left (hs ▸ dvd_mul_right U _)
  obtain ⟨B,hB⟩ := hd
  have hR : V.reflect q ≠ 0 := by
    intro hz
    have hV := Polynomial.reflect_eq_zero_iff.mp hz
    simp [hV] at hv0
  have hB0 : B ≠ 0 := by
    intro hz
    simp only [hz, mul_zero] at hB
    exact hR hB
  have hbound : (V.reflect q).natDegree ≤ q :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hvdeg)
  rw [hB, Polynomial.natDegree_mul hu hB0, hdeg] at hbound
  have hconst := Polynomial.eq_C_of_natDegree_le_zero (p := B) (by omega)
  let c := B.coeff 0
  have hb : V.reflect q = U * Polynomial.C c := hB.trans (congrArg (U * ·) hconst)
  have hcanc : U.reflect q = V * Polynomial.C c := by
    apply mul_left_cancel₀ hu
    rw [hs,hb]
    ring
  have h1 := congrArg (fun A : Polynomial K => A.coeff q) hb
  have h2 := congrArg (fun A : Polynomial K => A.coeff 0) hcanc
  simp [Polynomial.coeff_mul_C, hv0] at h1 h2
  simpa only [pow_two, ← h2] using h1.symm

/-- Dividing the m-th logarithm term can cost at most m-2 powers of p. -/
theorem log_denominator (p m : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hm : 2 ≤ m) :
    padicValNat p m + 2 ≤ m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  have bound (n : ℕ) : 2+n < p^(n+1) := by
    induction n with
    | zero => simpa using (show 2 < p by omega)
    | succ n ih =>
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul (by omega : 3 ≤ p) (by omega : n+3 ≤ p^(n+1))]
  by_contra! hh
  have hd : p^(k+1) ∣ 2+k := (pow_dvd_pow p (by omega : k+1 ≤ padicValNat p (2+k))).trans
    pow_padicValNat_dvd
  exact (Nat.not_le_of_lt (bound k)) (Nat.le_of_dvd (by omega) hd)

/-- Extract the finite nonlinear tail directly from the formal-series identity. -/
theorem coefficient_identity {K : Type*} [Field K] (L f : PowerSeries K) (c : K)
    (h0 : constantCoeff f = 0) (hL0 : coeff 0 L = 0) (hL1 : coeff 1 L = 1)
    (h : L.subst f = C c * L) (n : ℕ) :
    c * coeff n L = coeff n f + ∑ m ∈ Finset.Icc 2 n, coeff m L * coeff n (f^m) := by
  classical
  have hh := congrArg (coeff n) h
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0), coeff_C_mul] at hh
  simp only [smul_eq_mul] at hh
  have hs : Function.support (fun m => coeff m L * coeff n (f^m)) ⊆
      (↑(insert 1 (Finset.Icc 2 n)) : Set ℕ) := by
    intro m hm
    change coeff m L * coeff n (f^m) ≠ 0 at hm
    change m ∈ insert 1 (Finset.Icc 2 n)
    by_cases he : m = 0
    · simp [he,hL0] at hm
    by_cases hle : m ≤ n
    · simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    · obtain ⟨g,hg⟩ := X_dvd_iff.mpr h0
      simp [hg, mul_pow, coeff_X_pow_mul', hle] at hm
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_insert (by simp)] at hh
  simpa [hL1] using hh.symm

section Logarithm
variable {K : Type*} [Field K] [CharZero K] (R : Subring K) {p : ℕ} [Fact p.Prime]

/-- A coefficient divisible by p^m gives an integral p²-multiple even after
division by m. The coefficient ring only needs inverses for integers prime to p. -/
theorem integral_log_term (hp : 3 ≤ p)
    (units : ∀ u : ℕ, ¬ p ∣ u → (u : K)⁻¹ ∈ R)
    (m : ℕ) (hm : 2 ≤ m) (b a : R) (ha : (p : R)^m ∣ a) :
    ∃ z : R, (b : K) * (a : K) / (m : K) = (p : K)^2 * (z : K) := by
  let d := padicValNat p m
  let u := Nat.divMaxPow m p
  obtain ⟨w,hw⟩ := ha
  have hde : d+2 ≤ m := log_denominator p m hp hm
  have hdu : p^d*u = m := Nat.pow_padicValNat_mul_divMaxPow p m
  have hu : ¬ p ∣ u := Nat.not_dvd_divMaxPow (by omega) (by omega)
  have huK : (u : K) ≠ 0 := by
    exact_mod_cast (show u ≠ 0 from fun hz => hu (hz ▸ dvd_zero p))
  let invU : R := ⟨(u : K)⁻¹, units u hu⟩
  use b*w*(p:R)^(m-(d+2))*invU
  have hmK : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  apply (div_eq_iff hmK).mpr
  have he : m = 2+(m-(d+2))+d := by omega
  have hpow : (p : K)^m = (p:K)^2 * (p:K)^(m-(d+2)) * (p:K)^d := by
    conv_lhs => rw [he]
    simp only [pow_add]
  have hmcast : (p:K)^d * (u:K) = (m:K) := by exact_mod_cast hdu
  rw [hw, ← hmcast]
  push_cast
  change _ = (p:K)^2 * (b * (w:K) * (p:K)^(m-(d+2)) * (u:K)⁻¹) * _
  rw [hpow]
  field_simp

/-- The combined nonlinear part of the formal logarithm at a critical degree. -/
theorem log_tail (hp : 3 ≤ p)
    (units : ∀ u : ℕ, ¬ p ∣ u → (u : K)⁻¹ ∈ R)
    (q : ℕ) (f : PowerSeries R) (b : ℕ → R)
    (hf : ∀ i < q, (p:R) ∣ coeff i f) (h0 : constantCoeff f = 0) :
    ∃ total : R, (∑ m ∈ Finset.Icc 2 q,
      (b m : K) * ((coeff (R := R) q (f^m) : R) : K) / (m:K)) =
      (p:K)^2 * (total:K) := by
  classical
  let S := Finset.Icc 2 q
  have terms (m : ℕ) (hm : m ∈ S) : ∃ z : R,
      (b m : K) * ((coeff (R := R) q (f^m) : R) : K) / (m:K) = (p:K)^2 * (z:K) := by
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    apply integral_log_term R hp units m hm2
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hm2
    rw [hk, Nat.add_comm 2 k]
    exact at_boundary hf h0 k
  choose z hz using terms
  let total : R := ∑ m ∈ S.attach, z m.1 m.2
  have hsum : (∑ m ∈ S, (b m : K) * ((coeff (R := R) q (f^m) : R) : K) / (m:K)) =
      (p:K)^2 * (total:K) := by
    rw [← Finset.sum_attach]
    unfold total
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => hz m.1 m.2)
  exact ⟨total,hsum⟩

/-- The order dichotomy for elliptic multiplication, combined with the
degree-p coefficient of L(f)=pL, forces the supersingular branch when p∣b_p. -/
theorem supersingular_coefficients (hp : 3 ≤ p)
    (units : ∀ u : ℕ, ¬ p ∣ u → (u : K)⁻¹ ∈ R)
    (f : PowerSeries R) (b : ℕ → R)
    (h0 : constantCoeff f = 0) (hb : (p:R) ∣ b p)
    (order : ((∀ i < p, (p:R) ∣ coeff i f) ∧ ¬ (p:R) ∣ coeff p f) ∨
      (∀ i < p^2, (p:R) ∣ coeff i f))
    (hlog : (b p : K) = ((coeff (R := R) p f : R) : K) +
      ∑ m ∈ Finset.Icc 2 p, (b m : K) *
        ((coeff (R := R) p (f^m) : R) : K) / (m:K)) :
    ∀ i < p^2, (p:R) ∣ coeff i f := by
  rcases order with ⟨hlo,hpcoeff⟩ | hss
  · obtain ⟨z,hz⟩ := log_tail R hp units p f b hlo h0
    rw [hz] at hlog
    obtain ⟨w,hw⟩ := hb
    exfalso
    apply hpcoeff
    use w-(p:R)*z
    apply Subtype.ext
    have hcast := congrArg (fun a : R => (a : K)) hw
    push_cast at hcast ⊢
    linear_combination hcast - hlog
  · exact hss

/-- The coefficient-of-degree-p² consequence of L(f)=pL, given the
good-reduction coefficient conditions on f and V. Here b(m) is the coefficient
of the invariant differential, so L has coefficient b(m)/m. -/
theorem logarithm_precision (hp : 3 ≤ p)
    (units : ∀ u : ℕ, ¬ p ∣ u → (u : K)⁻¹ ∈ R)
    (f v : PowerSeries R) (b : ℕ → R)
    (hf : ∀ i < p^2, (p:R) ∣ coeff i f) (h0 : constantCoeff f = 0)
    (hv : ∀ j, 0 < j → j ≤ p^2 → (p:R) ∣ coeff j v) (hv0 : coeff 0 v = 1)
    (hlog : (b (p^2) : K) / p = ((coeff (R := R) (p^2) f : R) : K) +
      ∑ m ∈ Finset.Icc 2 (p^2), (b m : K) * ((coeff (R := R) (p^2) (f^m) : R) : K) / (m:K)) :
    (p:R)^3 ∣ b (p^2) - p * coeff (p^2) (f*v) := by
  obtain ⟨total,hsum⟩ := log_tail R hp units (p^2) f b hf h0
  obtain ⟨c,hc⟩ := numerator_precision hf hv hv0
  use total-c
  have hlog' := hlog
  rw [hsum] at hlog'
  have hn : (p:K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hlog'' := (div_eq_iff hn).mp hlog'
  apply Subtype.ext
  have hcast := congrArg (fun a : R => (a : K)) hc
  push_cast at hcast ⊢
  linear_combination hlog'' - (p:K) * hcast

end Logarithm

/-- The Weierstrass equation is Y²=(X−2x)(X−2)(X+2). -/
def cubic {R : Type*} [CommRing R] (x : R) : WeierstrassCurve.Affine R :=
  ⟨0, -2*x, 0, -4, 8*x⟩

theorem cubic_discriminant {R : Type*} [CommRing R] (x : R) :
    (cubic x).Δ = 2^12*(x^2-1)^2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, cubic]
  ring

theorem cubic_isElliptic {R : Type*} [CommRing R] (x : R)
    (h2 : IsUnit (2:R)) (hx : IsUnit (x^2-1)) : (cubic x).IsElliptic := by
  constructor
  rw [cubic_discriminant]
  exact (h2.pow 12).mul (hx.pow 2)

/-- Independent check of reciprocity using the cubic chord law. For T=(2,0)
and P=(X,Y), the product t(P)t(T−P) is one on the common affine chart.
The conclusion clears the denominators in t=2(X−2x)/Y. -/
theorem reciprocal_chart {K : Type*} [Field K] [DecidableEq K] [CharZero K] (x X Y : K)
    (hX : X ≠ 2) (hE : Y^2 = (X-2*x)*(X^2-4)) :
    let W := cubic x
    let slope := W.slope 2 X 0 (W.negY X Y)
    let X' := W.addX 2 X slope
    let Y' := W.addY 2 X 0 slope
    4 * (X-2*x) * (X'-2*x) = Y * Y' := by
  let s := Y/(2-X)
  have hden : 2-X ≠ 0 := sub_ne_zero.mpr hX.symm
  have hs : (cubic x).slope 2 X 0 ((cubic x).negY X Y) = s := by
    simp [WeierstrassCurve.Affine.slope_of_X_ne hX.symm, cubic, s]
  have hcoord : (cubic x).addX 2 X s = 2 - 8*(1-x)/(2-X) := by
    simp only [WeierstrassCurve.Affine.addX, cubic, s, zero_mul, add_zero]
    field_simp
    linear_combination hE
  dsimp only
  rw [hs]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, hcoord]
  change _ = Y * (-(s * ((2-8*(1-x)/(2-X))-2) + 0) - 0 * _ - 0)
  dsimp [s]
  field_simp
  linear_combination 8*(x-1)*hE

/-- The companion reflection T₀−P for T₀=(2x,0) preserves t.
This is the cleared-denominator form of t(T₀−P)=t(P). -/
theorem deck_chart {K : Type*} [Field K] [DecidableEq K] (x X Y : K)
    (hX : 2*x ≠ X) :
    let W := cubic x
    let e := 2*x
    let l := W.slope e X 0 (W.negY X Y)
    let X' := W.addX e X l
    let Y' := W.addY e X 0 l
    (X'-e)*Y = (X-e)*Y' := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_X_ne hX]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, cubic, zero_mul, sub_zero, zero_sub,
    neg_neg, add_zero]
  have hn : 2*x-X ≠ 0 := sub_ne_zero.mpr hX
  field_simp
  ring

/-- A reflection P ↦ T−P with 2T=0 commutes with odd multiplication. -/
theorem odd_commutes_reflection {G : Type*} [AddCommGroup G] (T P : G)
    (hT : 2 • T = 0) (n : ℕ) (hn : Odd n) : n • (T-P) = T - n • P := by
  obtain ⟨k,rfl⟩ := hn
  rw [nsmul_sub, add_smul, one_smul, mul_comm 2 k, mul_smul, hT, smul_zero, zero_add]

/-- On the chart t ≠ 0, the substituted coordinates give an actual point
of Y²=(X−2x)(X²−4), and tY=2(X−2x) recovers the local parameter. -/
theorem cubic_chart {K : Type*} [Field K] [CharZero K] (x t y : K) (ht : t ≠ 0)
    (hc : y^2 = 1-2*x*t^2+t^4) :
    let X := 2*(y+1)/t^2
    let Y := t*(X^2-4)/2
    Y^2 = (X-2*x)*(X^2-4) ∧ t*Y = 2*(X-2*x) := by
  let X := 2*(y+1)/t^2
  have h : t^2*(X^2-4) = 4*(X-2*x) := by
    dsimp [X]
    field_simp
    linear_combination 4*hc
  change (t*(X^2-4)/2)^2 = _ ∧ t*(t*(X^2-4)/2) = _
  constructor
  · linear_combination ((X^2-4)/4)*h
  · linear_combination h/2

/-- Squaring εp modulo p³ gives p² modulo p⁴ when ε²=1. -/
theorem square_precision {R : Type*} [CommRing R] (p e b : R)
    (hs : e^2 = 1) (hb : p^3 ∣ b-e*p) : p^4 ∣ b^2-p^2 := by
  obtain ⟨k,hk⟩ := hb
  use 2*e*k+p^2*k^2
  have he : b = e*p+p^3*k := by linear_combination hk
  rw [he]
  linear_combination p^2*hs

/-- Conditional elliptic reduction. The hypotheses are geometric or normalization
data for the multiplication map. The conclusion has the desired fourth power.
The theorem does not assume either of the Legendre congruences at degree p². -/
theorem elliptic_arithmetic {K : Type*} [Field K] [CharZero K] (R : Subring K)
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (units : ∀ u : ℕ, ¬ p ∣ u → (u : K)⁻¹ ∈ R)
    (f v : PowerSeries R) (L : PowerSeries K) (b : ℕ → R)
    (hf0 : constantCoeff f = 0) (hv0 : coeff 0 v = 1)
    (hb1 : b 1 = 1) (hbp : (p:R) ∣ b p)
    (hL : ∀ m, coeff m L = (b m : K) / (m:K))
    (hMul : L.subst (PowerSeries.map R.subtype f) = C (p:K) * L)
    (order : ((∀ i < p, (p:R) ∣ coeff i f) ∧ ¬ (p:R) ∣ coeff p f) ∨
      (∀ i < p^2, (p:R) ∣ coeff i f))
    (good : (∀ i < p^2, (p:R) ∣ coeff i f) →
      ∀ j, 0 < j → j ≤ p^2 → (p:R) ∣ coeff j v)
    (U V : Polynomial K) (hu : U ≠ 0) (hc : IsCoprime U V)
    (hdegree : U.natDegree = p^2) (hvdegree : V.natDegree ≤ p^2) (hV : V.coeff 0 = 1)
    (hrec : U * U.reflect (p^2) = V * V.reflect (p^2))
    (hnum : U.coeff (p^2) = ((coeff (R := R) (p^2) (f*v) : R) : K)) :
    (p:R)^4 ∣ (b (p^2))^2 - (p:R)^2 := by
  have hn : (p:K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hzero : constantCoeff (PowerSeries.map R.subtype f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,hf0]
    rfl
  have hcoeff (n : ℕ) : (p:K) * ((b n:K)/(n:K)) =
      ((coeff (R := R) n f : R) : K) + ∑ m ∈ Finset.Icc 2 n,
        (b m:K) * ((coeff (R := R) n (f^m) : R) : K) / (m:K) := by
    have he := coefficient_identity L (PowerSeries.map R.subtype f) (p:K) hzero
      (by simp [hL]) (by simp [hL,hb1]) hMul n
    simp only [hL, ← map_pow, coeff_map, Subring.coe_subtype, div_mul_eq_mul_div] at he
    exact he
  have hs := supersingular_coefficients R hp units f b hf0 hbp order (by
    simpa [mul_div_cancel₀ _ hn, mul_div_assoc', hn] using hcoeff p)
  have hd := logarithm_precision R hp units f v b hs hf0 (good hs) hv0 (by
    rw [← hcoeff (p^2)]
    push_cast
    field_simp)
  have he := reciprocal_square U V hu hc hdegree hvdegree hV hrec
  rw [hnum] at he
  apply square_precision (p:R) (coeff (p^2) (f*v)) (b (p^2))
  · exact_mod_cast he
  · simpa only [mul_comm (p:R)] using hd

/-- An upper-half units digit forces a carry in k+k. -/
theorem upper_half_carry (p k : ℕ) [Fact p.Prime] (h : p ≤ 2*(k%p)) :
    p ∣ (2*k).choose k := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr := Nat.mod_lt k hp
  have h2 : (2*k)%p = (2*(k%p))%p := by simp [two_mul, Nat.add_mod]
  have hrem : 2*(k%p)-p < p := by omega
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hrem] at h2
  have hn : (2*k)%p < k%p := by omega
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2*k) (k := k) (p := p)
  rw [Nat.choose_eq_zero_of_lt hn, zero_mul] at hl
  exact Nat.dvd_of_mod_eq_zero hl

/-- Exact recurrence used by the kernel to check specific eligible primes. -/
def partialSum : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | n+1 =>
    let previous := partialSum n
    let c := (2*(2*n+1)*previous.1)/(n+1)
    (c,previous.2+c^3)

theorem partialSum_spec (n : ℕ) :
    partialSum n = (Nat.centralBinom n, OeisA79727.a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialSum, ih, ← Nat.succ_mul_centralBinom_succ, Nat.mul_div_cancel_left _
      (Nat.succ_pos _)]
    unfold OeisA79727.a
    rw [Finset.sum_range_succ (n := n+1)]
    rfl

def caseAt (p : ℕ) : Prop :=
  OeisA79727.a ((p^2-1)/2) ≡ p^2 [MOD p^4]

private theorem case_of_eval (p : ℕ)
    (h : (partialSum ((p^2-1)/2)).2 % p^4 = p^2 % p^4) : caseAt p := by
  simpa only [partialSum_spec, caseAt, Nat.ModEq] using h

set_option maxRecDepth 10000 in
theorem small_cases : caseAt 3 ∧ caseAt 5 ∧ caseAt 13 ∧ caseAt 17 ∧ caseAt 19 := by
  exact ⟨case_of_eval 3 (by decide +kernel), case_of_eval 5 (by decide +kernel),
    case_of_eval 13 (by decide +kernel), case_of_eval 17 (by decide +kernel),
    case_of_eval 19 (by decide +kernel)⟩

end BalaAudit

/- Coefficient calculations on cubics in odd characteristic. -/
namespace BalaHasse
open Polynomial
noncomputable section

variable {k : Type*} [Field k]

/-- Evaluate the degree-N homogenization at (G,X). -/
def pull (G F : k[X]) (N : ℕ) : k[X] :=
  MvPolynomial.aeval ![G,X] (F.homogenize N)

theorem pull_pow (G F : k[X]) (d n : ℕ) (hd : F.natDegree ≤ d) :
    pull G (F^n) (d*n) = (pull G F d)^n := by
  induction n with
  | zero => simp [pull, homogenize_one]
  | succ n ih =>
    rw [Nat.mul_succ, pow_succ F, pull, homogenize_mul _ _ _ hd, map_mul, ← pull, ih, pow_succ]
    · rfl
    · exact (natDegree_pow_le.trans (Nat.mul_le_mul_left n hd)).trans (by rw [Nat.mul_comm])

private theorem euler_coeff (U : k[X]) (i : ℕ) :
    (X*U.derivative).coeff i = (i:k)*U.coeff i := by
  cases i with
  | zero => simp
  | succ i => rw [coeff_X_mul, coeff_derivative, mul_comm]; simp

private theorem residue_monomial (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : k[X]) (g0 : G.coeff 0=1) {N j : ℕ} (hN : p-1 ≤ N) (hmax : N < 2*p-1)
    (hj : j ≤ N) :
    (G^j * X^(N-j) * (G-X*G.derivative)).coeff (N-(p-1)) =
       if j=p-1 then 1 else 0 := by
  have pp := (Fact.out : p.Prime).pos
  rw [mul_right_comm (G^j), coeff_mul_X_pow']
  split_ifs with hle he he
  · rw [he, Nat.sub_self]
    simp [g0]
    rw [coeff_zero_eq_eval_zero,eval_pow,← coeff_zero_eq_eval_zero,g0,one_pow]
  · let i := N-(p-1)-(N-j)
    have hi : j+1 = p+i := by dsimp [i]; omega
    have hnon : (↑(j+1):k) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff k p]
      rintro ⟨w,hw⟩
      by_cases hw0 : w=0
      · simp [hw0] at hw
      by_cases hw1 : w=1
      · simp [hw1] at hw; omega
      have := Nat.mul_le_mul_left p (show 2 ≤ w by omega)
      omega
    have hid : C (↑(j+1):k) * (G^j*(G-X*G.derivative)) =
        C (↑(j+1):k) * G^(j+1) - X*(G^(j+1)).derivative := by
      rw [derivative_pow_succ, pow_succ, Nat.cast_add_one, map_add, map_one, C_eq_natCast]
      ring
    have hc := congrArg (fun H : k[X] => H.coeff i) hid
    simp only [coeff_C_mul,coeff_sub,euler_coeff] at hc
    have hi' : (↑(j+1):k) = (i:k) := by rw [hi,Nat.cast_add,CharP.cast_eq_zero,zero_add]
    rw [← hi', sub_self] at hc
    exact (mul_eq_zero.mp hc).resolve_left hnon
  · omega
  · rfl

/-- The coefficient of degree p-1 of a polynomial of degree below 2p-1 is
unchanged under a monic substitution u ↦ u G(1/u), with its derivative factor.
All expressions are reversed to ordinary polynomials in X=1/u. -/
theorem residue_pull (p : ℕ) [Fact p.Prime] [CharP k p] (G F : k[X]) (N : ℕ)
    (g0 : G.coeff 0=1) (hdeg : F.natDegree ≤ N) (hN : p-1 ≤ N) (hmax : N<2*p-1) :
    ((pull G F N)*(G-X*G.derivative)).coeff (N-(p-1)) = F.coeff (p-1) := by
  classical
  unfold pull
  conv_lhs => rw [F.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hdeg)]
  rw [homogenize_finsetSum, map_sum, Finset.sum_mul, finsetSum_coeff]
  rw [Finset.sum_eq_single (p-1)]
  · simp [homogenize_C_mul, homogenize_X_pow hN,
      mul_assoc (C _), coeff_C_mul, residue_monomial p G g0 hN hmax hN]
  · intro j hj hjne
    have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp [homogenize_C_mul,homogenize_X_pow hj', mul_assoc (C _),
      coeff_C_mul,residue_monomial p G g0 hN hmax hj',hjne]
  · simp [hN]

def cubicPoly (a b c : k) : k[X] := X^3+C a*X^2+C b*X+C c

def H (h : ℕ) (a b c : k) : k := ((cubicPoly a b c)^h).coeff (2*h)

private theorem cubic_degree (a b c : k) : (cubicPoly a b c).natDegree ≤ 3 := by
  unfold cubicPoly
  compute_degree!

private theorem pull_cubic (G : k[X]) (a b c : k) :
    pull G (cubicPoly a b c) 3 = G^3+C a*G^2*X+C b*G*X^2+C c*X^3 := by
  simp [pull,cubicPoly,homogenize_add,homogenize_C_mul,homogenize_X,homogenize_C]
  ring

private theorem H_coeff (p h : ℕ) [Fact p.Prime] [CharP k p] (ph : p=2*h+1)
    (G : k[X]) (g0 : G.coeff 0 = 1) (a b c : k) :
    ((G^3+C a*G^2*X+C b*G*X^2+C c*X^3)^h*(G-X*G.derivative)).coeff h =
      H h a b c := by
  have hh := residue_pull p G ((cubicPoly a b c)^h) (3*h) g0
    ((natDegree_pow_le.trans (Nat.mul_le_mul_left h (cubic_degree a b c))).trans
      (by rw [Nat.mul_comm])) (by omega) (by omega)
  rw [pull_pow _ _ _ _ (cubic_degree ..), pull_cubic] at hh
  simpa only [show 3*h-2*h=h by omega,show p-1=2*h by omega,H] using hh

theorem H_reverse (p h : ℕ) [Fact p.Prime] [CharP k p] (ph : p=2*h+1) (a b c : k) :
    ((1+C a*X+C b*X^2+C c*X^3)^h).coeff h = H h a b c := by
  simpa using H_coeff p h ph 1 (by simp) a b c

/-- Translation of the abscissa does not change the Hasse coefficient. -/
theorem H_shift (p h : ℕ) [Fact p.Prime] [CharP k p] (ph : p=2*h+1) (a b c r : k) :
    H h (a+3*r) (b+2*a*r+3*r^2) (c+b*r+a*r^2+r^3) = H h a b c := by
  let G : k[X] := 1+C r*X
  have h0 : G.coeff 0=1 := by simp [G]
  have d : G-X*G.derivative=1 := by simp [G]
  have e : G^3+C a*G^2*X+C b*G*X^2+C c*X^3 =
      1+C (a+3*r)*X+C (b+2*a*r+3*r^2)*X^2+C (c+b*r+a*r^2+r^3)*X^3 := by
    simp [G,map_ofNat]
    ring
  have z := H_coeff p h ph G h0 a b c
  rw [d,mul_one,e,H_reverse p h ph] at z
  exact z

/-- Hasse invariance under the normalized degree-two isogeny
u ↦ u + a + b/u, proved by coefficient extraction in characteristic p. -/
theorem H_quotient (p h : ℕ) [Fact p.Prime] [CharP k p] (ph : p=2*h+1) (a b : k) :
    H h (-2*a) (a^2-4*b) 0 = H h a b 0 := by
  let G : k[X] := 1+C a*X+C b*X^2
  let D : k[X] := 1-C b*X^2
  have h0 : G.coeff 0=1 := by simp [G,coeff_zero_eq_eval_zero]
  have hd : G-X*G.derivative=D := by simp [G,D]; ring
  have he : G^3+C (-2*a)*G^2*X+C (a^2-4*b)*G*X^2+C (0:k)*X^3=G*D^2 := by
    simp [G,D,map_ofNat]; ring
  have z := H_coeff p h ph G h0 (-2*a) (a^2-4*b) 0
  rw [he,hd,mul_pow,mul_assoc,← pow_mul,← pow_succ,← ph] at z
  rw [← z, ← H_reverse p h ph a b 0]
  simp only [map_zero,zero_mul,add_zero]
  change (G^h*(1-C b*X^2)^p).coeff h = (G^h).coeff h
  rw [sub_pow_char,one_pow,mul_sub,mul_one,coeff_sub,mul_pow,← pow_mul,
    ← mul_assoc,coeff_mul_X_pow',if_neg (by omega),sub_zero]


private theorem scaled_coeff (F : k[X]) (r : k) (n : ℕ) :
    (F.comp (C r*X)).coeff n = r^n * F.coeff n := by
  induction F using Polynomial.induction_on' with
  | add f g hf hg => simp [add_comp,coeff_add,hf,hg,mul_add]
  | monomial j a =>
    rw [monomial_comp, mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
      coeff_C_mul, coeff_X_pow, coeff_monomial]
    split_ifs <;> simp_all [mul_comm]

theorem H_scale (p h : ℕ) [Fact p.Prime] [CharP k p] (ph : p=2*h+1) (a b r : k) :
    H h (r*a) (r^2*b) 0 = r^h * H h a b 0 := by
  rw [← H_reverse p h ph, ← H_reverse p h ph]
  simp only [map_zero,zero_mul,add_zero]
  have e : (1+C a*X+C b*X^2).comp (C r*X) = 1+C (r*a)*X+C (r^2*b)*X^2 := by
    simp; ring
  rw [← e, ← pow_comp, scaled_coeff]

theorem inert_seven (p : ℕ) [Fact p.Prime] (eligible : OeisA3625.A p) :
    legendreSym p (-7) = -1 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two eligible.1).mpr hp2
  have h7 : legendreSym 7 p = -1 := by
    rw [legendreSym.mod]
    have he : (p:ℤ)%7 = ((p%7:ℕ):ℤ) := by norm_cast
    change legendreSym 7 ((p:ℤ)%7) = -1
    rw [he]
    rcases eligible.2 with h|h|h <;> rw [h] <;> norm_num
  have qr := legendreSym.quadratic_reciprocity' (p:=7) (q:=p) (by decide) hp2
  norm_cast at qr
  rw [legendreSym.at_neg hp2 7, ZMod.χ₄_eq_neg_one_pow hodd, qr, h7]
  norm_num only [Nat.reduceDiv]
  change (-1:ℤ)^(p/2)*((-1:ℤ)^(3*(p/2))*(-1)) = -1
  rw [← mul_assoc, ← pow_add, show p/2+3*(p/2)=2*(2*(p/2)) by omega,pow_mul]
  norm_num

/-- A square root of −7 is negated by Frobenius at precisely the inert
residue classes used here. -/
theorem frobenius_sqrt (p h : ℕ) [Fact p.Prime] [CharP k p]
    (eligible : OeisA3625.A p) (ph : p=2*h+1) (s : k) (hs : s^2 = -7) :
    s^p = -s := by
  have he := legendreSym.eq_pow p (-7)
  rw [inert_seven p eligible, show p/2=h by omega] at he
  have hm := congrArg (ZMod.castHom (by rfl : p ∣ p) k) he
  have hc : (-7:k)^h = -1 := by
    simp only [map_pow,map_intCast] at hm
    exact_mod_cast hm.symm
  rw [ph,pow_succ,pow_mul,hs,hc,neg_one_mul]


/-- The specific cubic Y²=(X−2x)(X²−4), x=3√−7, has vanishing Hasse
coefficient at every eligible prime. No short-sum vanishing theorem is used. -/
theorem eligible_cubic_hasse (p h : ℕ) [Fact p.Prime] [CharP k p]
    (eligible : OeisA3625.A p) (ph : p=2*h+1) (s : k) (hs : s^2 = -7) :
    H h (-2*(3*s)) (-4) (8*(3*s)) = 0 := by
  let x := 3*s
  let a := (1-s)/2
  let r := (-3-s)/2
  have hp2 : p ≠ 2 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hp7 : p ≠ 7 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hn (n : ℕ) (hn : n.Prime) (hne : p ≠ n) : (n:k) ≠ 0 :=
    (CharP.cast_eq_zero_iff k p n).not.mpr (fun hd => hne ((Nat.prime_dvd_prime_iff_eq eligible.1 hn).mp hd))
  have ht : (2:k) ≠ 0 := by simpa using hn 2 (by decide) hp2
  have hseven : (7:k) ≠ 0 := by simpa using hn 7 (by decide) hp7
  have hs0 : s ≠ 0 := by rintro rfl; simp_all
  have hfour : (4:k) ≠ 0 := by rw [show (4:k)=2*2 by ring]; exact mul_ne_zero ht ht
  have ha : a^2 = r := by dsimp [a,r]; linear_combination (norm := (field_simp; ring)) (1/4:k)*hs
  have haf : a^p = (1+s)/2 := by
    change (frobenius k p) ((1-s)/2) = _
    rw [map_div₀, map_sub, map_one, map_ofNat, frobenius_def, frobenius_sqrt p h eligible ph s hs, sub_neg_eq_add]
  have hd : r^h ≠ 1 := by
    intro hr
    rw [← ha, ← pow_mul] at hr
    have t : a^p=a := by rw [ph,pow_succ,hr,one_mul]
    rw [haf] at t
    change (1+s)/2=(1-s)/2 at t
    have zz : (2:k)*s=0 := by linear_combination (norm := (field_simp; ring)) 2*t
    exact hs0 ((mul_eq_zero.mp zz).resolve_left ht)
  let W := H h (-2*x) (-4) (8*x)
  have plus : H h (6-2*x) (8*(1-x)) 0 = W := by
    convert H_shift p h ph (-2*x) (-4) (8*x) 2 using 2 <;> ring
  have minus : H h (-6-2*x) (8*(1+x)) 0 = W := by
    convert H_shift p h ph (-2*x) (-4) (8*x) (-2) using 2 <;> ring
  have ha' : -2*(6-2*x) = r*(-6-2*x) := by dsimp [r,x]; linear_combination (norm := (field_simp; ring)) -3*hs
  have hb' : (6-2*x)^2-4*(8*(1-x)) = r^2*(8*(1+x)) := by
    dsimp [r,x]; linear_combination (norm := (field_simp; ring)) (-2*(3*s+1))*hs
  have he := H_quotient p h ph (6-2*x) (8*(1-x))
  rw [ha',hb',H_scale p h ph,plus,minus] at he
  have hz : (r^h-1)*W=0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd)

/-- Vanishing on the isogenous cubic whose quadratic factor is the Jacobi
quartic in the variable t². -/
theorem eligible_quadratic_hasse (p h : ℕ) [Fact p.Prime] [CharP k p]
    (eligible : OeisA3625.A p) (ph : p=2*h+1) (s : k) (hs : s^2= -7) :
    H h (-2*(3*s)) 1 0 = 0 := by
  let x := 3*s
  have hz := eligible_cubic_hasse p h eligible ph s hs
  have sh := H_shift p h ph (-2*x) (-4) (8*x) (2*x)
  have e : H h (-2*(-2*x)) ((-2*x)^2-4*1) 0 = H h (-2*x) (-4) (8*x) := by
    convert sh using 2 <;> ring
  rw [← H_quotient p h ph, e]
  exact hz


end
end BalaHasse

/- Reduction of the Jacobi quartic and its invariant differential. -/
namespace BalaReduction
open PowerSeries

/-- A smooth special fiber exists for every eligible prime, over its algebraic closure. -/
theorem eligible_special_fiber (p : ℕ) (eligible : OeisA3625.A p) :
    let _ : Fact p.Prime := ⟨eligible.1⟩
    ∃ x : AlgebraicClosure (ZMod p), x^2 = -63 ∧ (BalaAudit.cubic x).IsElliptic := by
  let _ : Fact p.Prime := ⟨eligible.1⟩
  let F := AlgebraicClosure (ZMod p)
  obtain ⟨x,hx⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (-63) (by decide : 0 < 2)
  have hp2 : p ≠ 2 := by
    intro he; subst p; norm_num [OeisA3625.A] at eligible
  have h2p : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq eligible.1 Nat.prime_two).mp hd)
  have h2 : (2:F) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero_iff F p 2).not.mpr h2p
  refine ⟨x,hx, BalaAudit.cubic_isElliptic x h2.isUnit ?_⟩
  rw [hx, show (-63:F)-1 = -(2:F)^6 by norm_num]
  exact (h2.isUnit.pow 6).neg

/-- The quartic whose inverse square root gives the invariant differential. -/
noncomputable def quartic {k : Type*} [CommRing k] (x : k) : Polynomial k :=
  1 - Polynomial.C (2*x)*Polynomial.X^2 + Polynomial.X^4

private theorem quartic_degree {k : Type*} [CommRing k] (x : k) :
    (quartic x).natDegree ≤ 4 := by
  unfold quartic
  compute_degree!

private theorem fresh_coeff_zero {k : Type*} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : PowerSeries k) {i : ℕ} (hi : ¬ p ∣ i) : coeff i (B^p) = 0 := by
  have hp := (Fact.out : p.Prime).ne_zero
  have he : map (frobenius k p) (expand p hp B) = B^p :=
    MvPowerSeries.map_frobenius_expand p hp
  rw [← he, coeff_map, coeff_expand_of_not_dvd p hp B hi, map_zero]

theorem differential_extract {k : Type*} [CommRing k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (h : ℕ) (ph : p=2*h+1) (x : k) (B : PowerSeries k)
    (hsqrt : (quartic x : PowerSeries k)*B^2=1) (n : ℕ) (hn : p ∣ n+1) :
    coeff n B = ((quartic x)^h).coeff (p-1) * coeff (n-(p-1)) (B^p) := by
  let A := (quartic x)^h
  have hdeg : A.natDegree ≤ 4*h :=
    (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul (by rfl) (quartic_degree x))) |>.trans
      (by rw [Nat.mul_comm])
  have hsplit : B = (A : PowerSeries k)*B^p := by
    dsimp [A]
    rw [ph, pow_succ, pow_mul, ← mul_assoc, Polynomial.coe_pow, ← mul_pow, hsqrt, one_pow, one_mul]
  have hextract (n : ℕ) (hn : p ∣ n+1) :
      coeff n B = A.coeff (p-1) * coeff (n-(p-1)) (B^p) := by
    conv_lhs => rw [hsplit, coeff_mul]
    have hpos : 0 < p := (Fact.out : p.Prime).pos
    have hle : p-1 ≤ n := by have := Nat.le_of_dvd (by omega) hn; omega
    let ij := (p-1,n-(p-1))
    rw [Finset.sum_eq_single ij]
    · simp [ij,Polynomial.coeff_coe]
    · intro ab hab hne
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      by_cases hd : p ∣ ab.2
      · have hda : p ∣ ab.1+1 := by
          have eq : n+1 = (ab.1+1)+ab.2 := by omega
          rwa [eq, Nat.dvd_add_left hd] at hn
        have hlarge : 4*h < ab.1 := by
          by_contra! hb
          obtain ⟨d,hd'⟩ := hda
          have hd2 : d < 2 := by
            by_contra! h
            have := Nat.mul_le_mul_left p h
            omega
          have hd1 : d = 1 := by
            rcases (show d = 0 ∨ d = 1 by omega) with hd0 | hd1
            · rw [hd0,mul_zero] at hd'; omega
            · exact hd1
          rw [hd1,mul_one] at hd'
          apply hne
          exact Prod.ext (by dsimp [ij]; omega) (by dsimp [ij]; omega)
        simp [Polynomial.coeff_coe,Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlarge)]
      · rw [fresh_coeff_zero p B hd, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by dsimp [ij]; omega)))
  exact hextract n hn

/-- In characteristic p, one vanishing coefficient of the differential forces
every coefficient with index congruent to p−1 modulo p to vanish. -/
theorem differential_vanishing {k : Type*} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h : ℕ) (ph : p=2*h+1) (x : k) (B : PowerSeries k)
    (hsqrt : (quartic x : PowerSeries k)*B^2=1) (hb0 : coeff 0 B = 1)
    (hshort : coeff (p-1) B = 0) :
    ∀ n, p ∣ n+1 → coeff n B = 0 := by
  let A := (quartic x)^h
  have hextract := differential_extract p h ph x B hsqrt
  have hpos := (Fact.out : p.Prime).pos
  have hbase := hextract (p-1) (by simp [Nat.sub_add_cancel (by omega : 1 ≤ p)])
  have ha : A.coeff (p-1) = 0 := by
    simpa [hshort,coeff_zero_eq_constantCoeff_apply, show constantCoeff B = 1 from (coeff_zero_eq_constantCoeff_apply B) ▸ hb0] using hbase.symm
  intro n hn
  rw [hextract n hn, ha, zero_mul]

/-- Algebraic construction of the normalized reciprocal square root over any
coefficient ring in which two is a unit, including the special fiber. -/
theorem inverse_sqrt {R : Type*} [CommRing R] (Q : PowerSeries R)
    (hQ : constantCoeff Q=1) (hu : IsUnit (2:R)) :
    ∃ B : PowerSeries R, constantCoeff B=1 ∧ Q*B^2=1 := by
  obtain ⟨u,hu'⟩ := hu
  let v : R := ↑u⁻¹
  have hv : (2:R)*v=1 := by rw [← hu']; exact u.mul_inv
  let Z := C (v^2) * (1-Q)
  have hz : constantCoeff Z=0 := by simp [Z,hQ]
  let S := map (Nat.castRingHom R) catalanSeries
  have hcat : S^2*X+1=S := by
    simpa [S] using congrArg (map (Nat.castRingHom R)) catalanSeries_sq_mul_X_add_one
  let sub := substAlgHom (R := R) (S := R) (HasSubst.of_constantCoeff_zero' hz)
  let T := sub S
  have hT : T^2*Z+1=T := by
    have he := congrArg sub hcat
    simpa [T,sub,substAlgHom_X] using he
  let Y := 1-2*Z*T
  have hY : constantCoeff Y=1 := by simp [Y,hz]
  have hZ : 4*Z=1-Q := by
    have hv' : (4:R)*v^2=1 := by linear_combination (2*v+1)*hv
    have he := congrArg (C (R:=R)) hv'
    simp only [map_mul,map_pow,map_ofNat,map_one] at he
    dsimp [Z]
    rw [map_pow]
    linear_combination ((1:PowerSeries R)-Q)*he
  have hs : Y^2=Q := by
    dsimp [Y]
    linear_combination 4*Z*hT - hZ
  use invOfUnit Y 1
  constructor
  · simp [constantCoeff_invOfUnit]
  · rw [← hs,← mul_pow,mul_invOfUnit _ _ (by simpa using hY),one_pow]

/-- For Bala's quartic this is the Hasse coefficient of its invariant differential. -/
theorem quartic_hasse (p h : ℕ) [Fact p.Prime] {k : Type*} [Field k] [CharP k p]
    (eligible : OeisA3625.A p) (ph : p=2*h+1) (s : k) (hs : s^2 = -7) :
    ((quartic (3*s))^h).coeff (p-1) = 0 := by
  let G : Polynomial k := 1+Polynomial.C (-2*(3*s))*Polynomial.X+Polynomial.X^2
  have he : quartic (3*s) = Polynomial.expand k 2 G := by
    dsimp [G,quartic]; simp [Polynomial.expand_eq_comp_X_pow]; ring
  rw [he,← map_pow,show p-1=2*h by omega,Polynomial.coeff_expand_mul' (by decide : 0<2)]
  have hh := BalaHasse.H_reverse p h ph (-2*(3*s)) 1 0
  rw [BalaHasse.eligible_quadratic_hasse p h eligible ph s hs] at hh
  simpa [G] using hh

/-- The special fiber and an actual normalized invariant differential, with
every Cartier coefficient vanishing. No geometric or logarithm hypotheses. -/
theorem eligible_reduction (p : ℕ) (eligible : OeisA3625.A p) :
    let _ : Fact p.Prime := ⟨eligible.1⟩
    ∃ (x : AlgebraicClosure (ZMod p)) (B : PowerSeries (AlgebraicClosure (ZMod p))),
      x^2= -63 ∧ (BalaAudit.cubic x).IsElliptic ∧ constantCoeff B=1 ∧
      (quartic x : PowerSeries _) * B^2=1 ∧ ∀ n, p ∣ n+1 → coeff n B=0 := by
  let _ : Fact p.Prime := ⟨eligible.1⟩
  let F := AlgebraicClosure (ZMod p)
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (k:=F) (-7) (by decide : 0<2)
  have hp2 : p ≠ 2 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two eligible.1).mpr hp2
  have ph : p=2*(p/2)+1 := by omega
  have two : (2:F) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero_iff F p 2).not.mpr
      (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq eligible.1 Nat.prime_two).mp hd))
  have hx : (3*s)^2= -63 := by linear_combination 9*hs
  obtain ⟨B,h0,he⟩ := inverse_sqrt (quartic (3*s) : PowerSeries F)
    (by simp [quartic]) two.isUnit
  refine ⟨3*s,B,hx,BalaAudit.cubic_isElliptic _ two.isUnit ?_,h0,he,?_⟩
  · rw [hx,show (-63:F)-1 = -(2:F)^6 by ring]
    exact (two.isUnit.pow 6).neg
  · intro n hn
    rw [differential_extract p (p/2) ph (3*s) B he n hn,
      quartic_hasse p (p/2) eligible ph s hs,zero_mul]

section Lift
variable {K : Type*} [Field K] [CharZero K] (R : Subring K)
variable {k : Type*} [CommRing k] {p : ℕ} [Fact p.Prime] [CharP k p]

omit [CharP k p] in
/-- Below p² an index divisible by p has exactly one factor of p. Thus the
Cartier vanishing supplies every missing denominator in the truncated logarithm. -/
theorem truncated_log_integral (ρ : R →+* k)
    (ker : ∀ a : R, ρ a = 0 ↔ (p:R) ∣ a)
    (units : ∀ u : ℕ, ¬p ∣ u → (u:K)⁻¹ ∈ R)
    (b : ℕ → R) (hv : ∀ n, p ∣ n+1 → ρ (b (n+1)) = 0)
    (n : ℕ) (hn : n < p^2) : (b n : K) / (n:K) ∈ R := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  by_cases hd : p ∣ n
  · obtain ⟨u,hu⟩ := hd
    have hu0 : u ≠ 0 := by rintro rfl; simp_all
    have hup : u < p := by
      rw [pow_two,hu] at hn
      exact (Nat.mul_lt_mul_left (Fact.out : p.Prime).pos).mp hn
    have hi := units u (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hu0) hup)
    have hd' : (p:R) ∣ b n := (ker _).mp (by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      exact hv j ⟨u,hu⟩)
    obtain ⟨w,hw⟩ := hd'
    have he : (b n : K)/(n:K) = (w:K)*(u:K)⁻¹ := by
      have hp0 : (p:K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      rw [hw,hu]
      push_cast
      field_simp
    rw [he]
    exact R.mul_mem w.property hi
  · simpa only [div_eq_mul_inv] using R.mul_mem (b n).property (units n hd)

/-- This bypasses the geometric height dichotomy. A logarithm integral through
degree q−1 with unit linear term forces its p-series to vanish there modulo p. -/
theorem order_from_log (hp : 3 ≤ p) (units : ∀ u : ℕ, ¬p ∣ u → (u:K)⁻¹ ∈ R)
    (q : ℕ) (f : PowerSeries R) (L : PowerSeries K) (b : ℕ → R)
    (hf0 : constantCoeff f = 0) (hb1 : b 1 = 1)
    (hL : ∀ m, coeff m L = (b m:K)/(m:K))
    (hmul : L.subst (PowerSeries.map R.subtype f) = C (p:K)*L)
    (hint : ∀ m < q, coeff m L ∈ R) :
    ∀ n < q, (p:R) ∣ coeff n f := by
  have hzero : constantCoeff (PowerSeries.map R.subtype f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,hf0]
    rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hl := BalaAudit.coefficient_identity L (PowerSeries.map R.subtype f) (p:K) hzero
      (by simp [hL]) (by simp [hL,hb1]) hmul n
    simp only [← map_pow, coeff_map, Subring.coe_subtype] at hl
    obtain ⟨z,hz⟩ := BalaAudit.log_tail R hp units n f b
      (fun j hj => ih j hj (hj.trans hn)) hf0
    simp_rw [hL, div_mul_eq_mul_div] at hl
    rw [hz] at hl
    let a : R := ⟨coeff n L, hint n hn⟩
    use a-(p:R)*z
    apply Subtype.ext
    push_cast
    change _ = (p:K)*(coeff n L - (p:K)*(z:K))
    rw [hL]
    linear_combination -hl

/-- For the quartic, reduction of the differential and the logarithm identity
alone force divisibility of every coefficient of [p] below p². -/
theorem quartic_order (ρ : R →+* k) (ker : ∀ a : R, ρ a = 0 ↔ (p:R) ∣ a)
    (hp : 3 ≤ p) (h : ℕ) (ph : p=2*h+1)
    (units : ∀ u : ℕ, ¬p ∣ u → (u:K)⁻¹ ∈ R)
    (x : k) (B : PowerSeries k) (hsqrt : (quartic x : PowerSeries k)*B^2=1)
    (f : PowerSeries R) (L : PowerSeries K) (b : ℕ → R)
    (hb : ∀ n, coeff n B = ρ (b (n+1)))
    (hf0 : constantCoeff f=0) (hb1 : b 1=1) (hbp : (p:R) ∣ b p)
    (hL : ∀ m, coeff m L = (b m:K)/(m:K))
    (hmul : L.subst (PowerSeries.map R.subtype f) = C (p:K)*L) :
    ∀ n < p^2, (p:R) ∣ coeff n f := by
  have hv := differential_vanishing p h ph x B hsqrt (by simp [hb,hb1])
    (by rw [hb,Nat.sub_add_cancel (by omega : 1 ≤ p)]; exact (ker _).mpr hbp)
  apply order_from_log R hp units _ f L b hf0 hb1 hL hmul
  intro n hn
  rw [hL]
  exact truncated_log_integral R ρ ker units b (fun j hj => hb j ▸ hv j hj) n hn

end Lift

end BalaReduction

/- Concrete coefficient ring for the unramified quadratic calculation. -/
namespace BalaLocalRing
open scoped Padic QuadraticAlgebra
noncomputable section

abbrev Quad (A : Type*) [CommRing A] := QuadraticAlgebra A (-7) 0

variable (p : ℕ) [Fact p.Prime]

theorem irreducible_residue (hp : OeisA3625.A p) :
    ∀ t : ZMod p, t^2 ≠ -7 + 0*t := by
  intro t ht
  have h := (legendreSym.eq_neg_one_iff p).mp (BalaHasse.inert_seven p hp)
  apply h
  use t
  simpa [sq] using ht.symm

theorem irreducible_local (hp : OeisA3625.A p) :
    ∀ t : ℚ_[p], t^2 ≠ -7 + 0*t := by
  intro t ht
  simp only [zero_mul,add_zero] at ht
  have hn : ‖t‖ ≤ 1 := by
    have h := congrArg norm ht
    rw [norm_pow, norm_neg] at h
    have hb : ‖(7:ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p:=p) 7
    nlinarith [norm_nonneg t]
  let z : ℤ_[p] := ⟨t,hn⟩
  have hz : z^2 = -7 := by apply Subtype.ext; exact ht
  have hred := congrArg (PadicInt.toZMod (p:=p)) hz
  exact irreducible_residue p hp _ (by simpa only [map_pow,map_neg,map_ofNat,zero_mul,add_zero] using hred)

def changeBase {A C : Type*} [CommRing A] [CommRing C] (e : A →+* C) :
    Quad A →+* Quad C where
  toFun z := ⟨e z.re,e z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp [map_ofNat]

def embed : Quad ℤ_[p] →+* Quad ℚ_[p] := changeBase (PadicInt.Coe.ringHom (p:=p))

theorem embed_injective : Function.Injective (embed p) := by
  intro z w he
  exact QuadraticAlgebra.ext
    (Subtype.ext (congrArg QuadraticAlgebra.re he)) (Subtype.ext (congrArg QuadraticAlgebra.im he))

abbrev localRing := (embed p).range

def localEquiv : Quad ℤ_[p] ≃+* localRing p :=
  RingEquiv.ofLeftInverse (embed_injective p).hasLeftInverse.choose_spec

def reduce : localRing p →+* Quad (ZMod p) :=
  (changeBase PadicInt.toZMod).comp (localEquiv p).symm.toRingHom

private theorem base_kernel (t : ℤ_[p]) : PadicInt.toZMod t=0 ↔ (p:ℤ_[p]) ∣ t := by
  rw [← RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem reduce_kernel (z : localRing p) : reduce p z=0 ↔ (p:localRing p) ∣ z := by
  obtain ⟨u,rfl⟩ := (localEquiv p).surjective z
  change changeBase PadicInt.toZMod ((localEquiv p).symm (localEquiv p u))=0 ↔ _
  rw [RingEquiv.symm_apply_apply]
  constructor
  · intro he
    obtain ⟨r,hr⟩ := (base_kernel p _).mp (congrArg QuadraticAlgebra.re he)
    obtain ⟨i,hi⟩ := (base_kernel p _).mp (congrArg QuadraticAlgebra.im he)
    have h : u = (p : Quad ℤ_[p])*⟨r,i⟩ := by ext <;> simp [hr,hi]
    use localEquiv p ⟨r,i⟩
    conv_lhs => rw [h,map_mul,map_natCast]
  · rintro ⟨w,hw⟩
    have h := congrArg (reduce p) hw
    have hh : PadicInt.toZMod u.re = 0 ∧ PadicInt.toZMod u.im = 0 := by simpa [reduce,changeBase] using h
    exact QuadraticAlgebra.ext hh.1 hh.2

theorem inverse_mem (hp : OeisA3625.A p) (n : ℕ) (hn : ¬p ∣ n) :
    let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨irreducible_local p hp⟩
    (n : Quad ℚ_[p])⁻¹ ∈ localRing p := by
  let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨irreducible_local p hp⟩
  have hc := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn
  have hn1 := (Padic.norm_natCast_eq_one_iff (p:=p)).mpr hc
  let w : ℤ_[p] := ⟨(n : ℚ_[p])⁻¹, by simp [norm_inv,hn1]⟩
  use (⟨w,0⟩ : Quad ℤ_[p])
  apply eq_inv_of_mul_eq_one_left
  ext <;> simp [embed,changeBase,w]
  change (n:ℚ_[p])⁻¹*(n:ℚ_[p])=1
  exact inv_mul_cancel₀ (by exact_mod_cast (show n≠0 from fun hz => hn (hz ▸ dvd_zero p)))

end
end BalaLocalRing

/- The p-series defined by the logarithm of the Jacobi quartic. -/
namespace BalaFormalMultiplication
open PowerSeries
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Formal integration with constant term zero. -/
def primitive (B : PowerSeries K) : PowerSeries K :=
  mk fun n => coeff (n-1) B / (n:K)

theorem derivative_primitive (B : PowerSeries K) : derivative K (primitive B) = B := by
  ext n
  rw [coeff_derivative,primitive, coeff_mk,Nat.add_sub_cancel]
  push_cast
  field_simp

/-- The n-fold multiplication parameter for the law with logarithm L. -/
def multiple (L : PowerSeries K) (h1 : IsUnit (coeff 1 L)) (n : ℕ) :=
  (L.substInvOfIsUnit h1).subst (C (n:K)*L)

omit [CharZero K] in
theorem multiple_spec (L : PowerSeries K) (h0 : constantCoeff L=0)
    (h1 : IsUnit (coeff 1 L)) (n : ℕ) :
    constantCoeff (multiple L h1 n)=0 ∧ L.subst (multiple L h1 n)=C (n:K)*L := by
  have hinner : constantCoeff (C (n:K)*L)=0 := by simp [h0]
  have hi := HasSubst.of_constantCoeff_zero' hinner
  constructor
  · exact constantCoeff_subst_eq_zero hinner _ (constantCoeff_substInvOfIsUnit ..)
  · unfold multiple
    rw [← subst_comp_subst_apply (HasSubst.substInvOfIsUnit L h1) hi,
      subst_substInvOfIsUnit_right L h0 h1, subst_X hi]

omit [CharZero K] in
/-- A normalized logarithm integral below q gives p-divisibility of the actual
coefficients of its p-series there, even before integrality of the full series
is known. -/
theorem low_multiple (R : Subring K) (p q : ℕ) (L : PowerSeries K)
    (h0 : constantCoeff L=0) (h1 : coeff 1 L=1)
    (hint : ∀ m<q, coeff m L ∈ R) :
    ∀ n<q, ∃ a : R, coeff n (multiple L (h1 ▸ isUnit_one) p) = (p:K)*(a:K) := by
  let f := multiple L (h1 ▸ isUnit_one) p
  obtain ⟨hf0,hmul⟩ := multiple_spec L h0 (h1 ▸ isUnit_one) p
  let J := Submodule.span R {(p:K)}
  have mem (x : K) : x ∈ J ↔ ∃ a : R, x=(p:K)*(a:K) := by
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,ha.symm.trans (mul_comm _ _)⟩
    · rintro ⟨a,rfl⟩
      exact ⟨a,mul_comm _ _⟩
  have inside {x : K} (hx : x ∈ J) : x ∈ R := by
    obtain ⟨a,rfl⟩ := (mem _).mp hx
    exact R.mul_mem (by exact_mod_cast (p:R).property) a.property
  have prod {x y : K} (hx : x ∈ R) (hy : y ∈ J) : x*y ∈ J :=
    J.smul_mem (⟨x,hx⟩ : R) hy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have lower (i : ℕ) (hi : i < n) : coeff i f ∈ J :=
      (mem _).mpr (ih i hi (hi.trans hn))
    have powers (m i : ℕ) (hm : 0 < m) (hi : i < n) : coeff i (f^m) ∈ J := by
      induction m generalizing i with
      | zero => omega
      | succ m ih' =>
        rcases Nat.eq_zero_or_pos m with rfl | hm'
        · simpa using lower i hi
        rw [pow_succ,coeff_mul]
        apply J.sum_mem
        intro ab hab
        have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
        exact prod (inside (ih' _ hm' (by omega))) (lower _ (by omega))
    have boundary (m : ℕ) (hm : 2 ≤ m) : coeff n (f^m) ∈ J := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
      rw [pow_succ,coeff_mul]
      apply J.sum_mem
      intro ab hab
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      by_cases ha : ab.1=0
      · simp [ha,coeff_zero_eq_constantCoeff_apply,show constantCoeff f=0 from hf0,
          show j ≠ 0 by omega]
      by_cases hb : ab.2=0
      · simp [hb,coeff_zero_eq_constantCoeff_apply,show constantCoeff f=0 from hf0]
      exact prod (inside (powers j _ (by omega) (by omega))) (lower _ (by omega))
    have hh := BalaAudit.coefficient_identity L f (p:K) hf0
      (by simpa [coeff_zero_eq_constantCoeff_apply] using h0) h1 hmul n
    apply (mem _).mp
    rw [show coeff n f = (p:K)*coeff n L -
        ∑ m ∈ Finset.Icc 2 n, coeff m L * coeff n (f^m) by linear_combination hh.symm]
    apply J.sub_mem
    · exact (mem _).mpr ⟨⟨_,hint n hn⟩,rfl⟩
    · apply J.sum_mem
      intro i hi
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
      exact prod (hint _ (hhi.trans_lt hn)) (boundary _ hlo)

/-- For each eligible prime the actual logarithm-defined multiplication
parameter of the lifted quartic has p-divisible coefficients below degree p².
The field, coefficient ring, differential, logarithm and parameter are all
constructed in the proof. -/
theorem eligible_multiplication (p : ℕ) (eligible : OeisA3625.A p) :
    let _ : Fact p.Prime := ⟨eligible.1⟩
    let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_local p eligible⟩
    let R := BalaLocalRing.localRing p
    let F := BalaLocalRing.Quad ℚ_[p]
    ∃ (s : R) (B : PowerSeries R) (L f : PowerSeries F),
      s^2= -7 ∧ constantCoeff B=1 ∧
      (BalaReduction.quartic (3*s) : PowerSeries R)*B^2=1 ∧
      L=primitive (map R.subtype B) ∧ constantCoeff f=0 ∧ L.subst f=C (p:F)*L ∧
      (∀ n<p^2, ∃ a : R, coeff n f=(p:F)*(a:F)) ∧
      ∀ n, p ∣ n+1 → (p:R) ∣ coeff n B := by
  let _ : Fact p.Prime := ⟨eligible.1⟩
  let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_local p eligible⟩
  let _ : Fact (∀ t : ZMod p, t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_residue p eligible⟩
  let R := BalaLocalRing.localRing p
  let F := BalaLocalRing.Quad ℚ_[p]
  let k := BalaLocalRing.Quad (ZMod p)
  let _ : CharP k p := charP_of_injective_ringHom (algebraMap (ZMod p) k).injective p
  let ρ := BalaLocalRing.reduce p
  let s : R := BalaLocalRing.localEquiv p QuadraticAlgebra.omega
  have hs' : (QuadraticAlgebra.omega : BalaLocalRing.Quad ℤ_[p])^2= -7 := by
    rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; ext <;> rfl
  have hs : s^2= -7 := by simpa [s,map_ofNat] using congrArg (BalaLocalRing.localEquiv p) hs'
  have hres : (ρ s)^2= -7 := by simpa [map_ofNat] using congrArg ρ hs
  have hp2 : p ≠ 2 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two eligible.1).mpr hp2
  let h := p/2
  have ph : p=2*h+1 := by dsimp [h]; omega
  have hnd : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq eligible.1 Nat.prime_two).mp h)
  have htwo : IsUnit (2:R) := by
    let v : R := ⟨(2:F)⁻¹,by exact_mod_cast BalaLocalRing.inverse_mem p eligible 2 hnd⟩
    apply isUnit_iff_exists_inv.mpr
    use v
    apply Subtype.ext
    change (2:F)*(2:F)⁻¹=1
    exact mul_inv_cancel₀ (by norm_num)
  obtain ⟨B,h0,hB⟩ := BalaReduction.inverse_sqrt
    (BalaReduction.quartic (3*s) : PowerSeries R) (by simp [BalaReduction.quartic]) htwo
  have hQ : (BalaReduction.quartic (3*(ρ s)) : PowerSeries k)*(map ρ B)^2=1 := by
    have coeQ {A : Type} [CommRing A] (x : A) : (BalaReduction.quartic x : PowerSeries A) =
        1-C (2*x)*X^2+X^4 := by
      simp only [BalaReduction.quartic,Polynomial.coe_add,Polynomial.coe_sub,Polynomial.coe_mul,
        Polynomial.coe_pow,Polynomial.coe_C,Polynomial.coe_one,Polynomial.coe_X]
    have ht := congrArg (map ρ) hB
    rw [coeQ (3*s)] at ht
    rw [coeQ (3*ρ s)]
    simp only [map_mul,map_add,map_sub,map_C,map_pow,map_X,map_one,map_ofNat] at ht
    simpa only [map_mul,map_ofNat] using ht
  have hdiff (n : ℕ) (hn : p ∣ n+1) : coeff n (map ρ B)=0 := by
    rw [BalaReduction.differential_extract p h ph _ _ hQ n hn,
      BalaReduction.quartic_hasse p h eligible ph _ hres,zero_mul]
  let L := primitive (map R.subtype B)
  have hl0 : constantCoeff L=0 := by rw [← coeff_zero_eq_constantCoeff_apply]; simp [L,primitive]
  have hl1 : coeff 1 L=1 := by simp [L,primitive,coeff_zero_eq_constantCoeff_apply,h0]
  have hli (m : ℕ) (hm : m<p^2) : coeff m L ∈ R := by
    simp only [L,primitive,coeff_mk,coeff_map]
    apply BalaReduction.truncated_log_integral R ρ (BalaLocalRing.reduce_kernel p)
      (BalaLocalRing.inverse_mem p eligible) (fun j => coeff (j-1) B) _ m hm
    intro n hn
    simpa [coeff_map] using hdiff n hn
  let f := multiple L (hl1 ▸ isUnit_one) p
  obtain ⟨hf0,hf⟩ := multiple_spec L hl0 (hl1 ▸ isUnit_one) p
  refine ⟨s,B,L,f,hs,h0,hB,rfl,hf0,hf,low_multiple R p _ L hl0 hl1 hli,?_⟩
  intro n hn
  apply (BalaLocalRing.reduce_kernel p _).mp
  simpa only [coeff_map] using hdiff n hn

end
end BalaFormalMultiplication

/- Jacobi addition in the parameter at the origin. -/
namespace BalaJacobi
open PowerSeries
noncomputable section

def q {A : Type*} [CommRing A] (x t : A) := 1-2*x*t^2+t^4
def tangent {A : Type*} [CommRing A] (x t : A) := 2*t^3-2*x*t
def num {A : Type*} [CommRing A] (u v z w : A) := u*w+z*v
def den {A : Type*} [CommRing A] (u z : A) := 1-u^2*z^2
def ordNum {A : Type*} [CommRing A] (x u v z w : A) :=
  (v*w+z*tangent x u)*den u z+2*u*z^2*v*num u v z w

theorem ord_symm {A : Type*} [CommRing A] (x u v z w : A)
    (hu : v^2=q x u) (hz : w^2=q x z) :
    ordNum x u v z w = ordNum x z w u v := by
  unfold ordNum den num tangent
  unfold q at hu hz
  linear_combination 2*u*z^3*hu - 2*z*u^3*hz

theorem addition_equation {A : Type*} [CommRing A] (x u v z w : A)
    (hu : v^2=q x u) (hz : w^2=q x z) :
    (ordNum x u v z w)^2 = (den u z)^4 -
      2*x*(num u v z w)^2*(den u z)^2 + (num u v z w)^4 := by
  unfold ordNum tangent den num
  unfold q at hu hz
  grind

variable {K : Type*} [Field K] [CharZero K]

/-- An arc through (0,1) having a specified constant speed in the invariant differential. -/
structure Arc (x : K) (B : (PowerSeries K)) (n : K) (u v : (PowerSeries K)) : Prop where
  zero : constantCoeff u = 0
  one : constantCoeff v = 1
  curve : v^2=q (C x) u
  speed : derivative K u=C n*v*B

theorem Arc.ordinate {x n : K} {B u v : (PowerSeries K)} (a : Arc x B n u v) :
    derivative K v=C n*tangent (C x) u*B := by
  have hd := congrArg (derivative K) a.curve
  have d2 : derivative K (2:(PowerSeries K))=0 := by rw [show (2:(PowerSeries K))=C (2:K) by rw [map_ofNat]]; exact derivative_C
  simp [q,d2,Derivation.leibniz,smul_eq_mul,a.speed] at hd
  have hv : v ≠ 0 := by intro h; simpa [h] using a.one
  apply mul_left_cancel₀ (mul_ne_zero (by intro hh; have := congrArg constantCoeff hh; norm_num [map_ofNat] at this : (2:(PowerSeries K)) ≠ 0) hv)
  unfold tangent
  linear_combination hd

def addT (u v z w : (PowerSeries K)) := num u v z w * (den u z)⁻¹
def addY (x : K) (u v z w : (PowerSeries K)) := ordNum (C x) u v z w * ((den u z)⁻¹)^2

theorem Arc.add {x n m : K} {B u v z w : (PowerSeries K)} (a : Arc x B n u v) (b : Arc x B m z w) :
    Arc x B (n+m) (addT u v z w) (addY x u v z w) := by
  have hD : constantCoeff (den u z)=1 := by simp [den,a.zero,b.zero]
  have hi := PowerSeries.mul_inv_cancel (den u z) (by rw [hD]; exact one_ne_zero)
  have hc := addition_equation (C x) u v z w a.curve b.curve
  have hs := ord_symm (C x) u v z w a.curve b.curve
  constructor
  · simp [addT,num,a.zero,b.zero]
  · simp [addY,ordNum,num,tangent,constantCoeff_inv,hD,a.zero,a.one,b.zero,b.one]
  · unfold addY addT q
    calc
      _ = (ordNum (C x) u v z w)^2 * ((den u z)⁻¹)^4 := by ring
      _ = _ := by
        rw [hc]
        linear_combination (1+(den u z)*(den u z)⁻¹+((den u z)*(den u z)⁻¹)^2+
           ((den u z)*(den u z)⁻¹)^3-2*C x*(num u v z w)^2*((den u z)⁻¹)^2*
             (1+(den u z)*(den u z)⁻¹))*hi
  · unfold addT addY
    rw [map_add]
    simp only [Derivation.leibniz,smul_eq_mul,PowerSeries.derivative_inv']
    have dnum : derivative K (num u v z w) =
        C n*B*(v*w+z*tangent (C x) u) + C m*B*(w*v+u*tangent (C x) z) := by
      simp [num,Derivation.leibniz,smul_eq_mul,a.speed,b.speed,a.ordinate,b.ordinate]; ring
    have dden : derivative K (den u z) =
        -(C n*B*(2*u*z^2*v)+C m*B*(2*z*u^2*w)) := by
      simp [den,Derivation.leibniz,smul_eq_mul,a.speed,b.speed]; ring
    rw [dnum,dden]
    have ea : ordNum (C x) u v z w =
        (v*w+z*tangent (C x) u)*den u z+2*u*z^2*v*num u v z w := rfl
    have eb : ordNum (C x) u v z w =
        (w*v+u*tangent (C x) z)*den u z+2*z*u^2*w*num u v z w := by
      rw [hs]; simp only [ordNum,den,num]; ring
    linear_combination -(C n*B*((den u z)⁻¹)^2)*ea -
      (C m*B*((den u z)⁻¹)^2)*eb -
      (C n*B*(v*w+z*tangent (C x) u)+C m*B*(w*v+u*tangent (C x) z))*(den u z)⁻¹*hi

omit [CharZero K] in
theorem Arc.neg {x n : K} {B u v : (PowerSeries K)} (a : Arc x B n u v) : Arc x B (-n) (-u) v := by
  refine ⟨by simp [a.zero],a.one,?_,?_⟩
  · rw [a.curve]; unfold q; ring
  · simp [a.speed]

omit [CharZero K] in
/-- Differential addition and subtraction for the squared parameter. -/
theorem add_product {x n m : K} {B u v z w : (PowerSeries K)} (a : Arc x B n u v) (b : Arc x B m z w) :
    addT u v z w * addT u v (-z) w * den u z = u^2-z^2 := by
  have hi := PowerSeries.mul_inv_cancel (den u z) (by simp [den,a.zero,b.zero])
  have e : num u v z w*num u v (-z) w=(u^2-z^2)*den u z := by
    unfold num den
    have eu := a.curve
    have ez := b.curve
    unfold q at eu ez
    linear_combination u^2*ez-z^2*eu
  have hn : den u (-z)=den u z := by unfold den; ring
  unfold addT
  rw [hn]
  calc
    _ = num u v z w*num u v (-z) w*(den u z)⁻¹*((den u z)*(den u z)⁻¹) := by ring
    _ = _ := by rw [e,hi,mul_one,mul_assoc,hi,mul_one]

omit [CharZero K] in
private theorem subst_one_at {u B : (PowerSeries K)} (hu : constantCoeff u=0) (hb : constantCoeff B=1) :
    constantCoeff (B.subst u)=1 := by
  have hi := HasSubst.of_constantCoeff_zero' hu
  have h := constantCoeff_subst_eq_zero hu (B-1) (by simp [hb])
  rw [← coe_substAlgHom hi,map_sub,map_one,map_sub,map_one,sub_eq_zero] at h
  simpa only [coe_substAlgHom,constantCoeff.eq_def] using h

omit [CharZero K] in
private theorem subst_quartic {u B : (PowerSeries K)} {x : K} (hu : constantCoeff u=0)
    (hb : q (C x) (X:(PowerSeries K))*B^2=1) : q (C x) u*(B.subst u)^2=1 := by
  let φ := substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' hu)
  have hx : φ (X:(PowerSeries K))=u := substAlgHom_X _
  have hc : φ (C x)=C x := by simpa only [φ,coe_substAlgHom,C,constantCoeff.eq_def] using (subst_C (a:=u) x)
  have h := congrArg φ hb
  simp only [q,map_sub,map_one,map_add,map_pow,map_mul,map_ofNat,hx,hc] at h
  simpa only [φ,coe_substAlgHom,q] using h

theorem Arc.normalized {x n : K} {B u v : (PowerSeries K)} (a : Arc x B n u v)
    (h0 : constantCoeff B=1) (hb : q (C x) (X:(PowerSeries K))*B^2=1) : v*(B.subst u)=1 := by
  have hs : (v*(B.subst u))^2=1 := by rw [mul_pow,a.curve,subst_quartic a.zero hb]
  rcases sq_eq_one_iff.mp hs with ht|ht
  · exact ht
  · have hh := congrArg constantCoeff ht
    rw [map_mul,a.one,subst_one_at a.zero h0,map_neg,map_one,one_mul] at hh
    exfalso; exact (by norm_num : (1:K) ≠ -1) hh

theorem Arc.logarithm {x n : K} {B u v : (PowerSeries K)} (a : Arc x B n u v)
    (h0 : constantCoeff B=1) (hb : q (C x) (X:(PowerSeries K))*B^2=1) :
    (BalaFormalMultiplication.primitive B).subst u=C n*BalaFormalMultiplication.primitive B := by
  have hL : constantCoeff (BalaFormalMultiplication.primitive B)=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [BalaFormalMultiplication.primitive]
  apply derivative.ext
  · rw [derivative_subst (HasSubst.of_constantCoeff_zero' a.zero)]
    simp only [Derivation.leibniz,smul_eq_mul,derivative_C,mul_zero,add_zero,
      BalaFormalMultiplication.derivative_primitive,a.speed]
    linear_combination C n*B*(a.normalized h0 hb)
  · rw [map_mul,hL,mul_zero]
    exact constantCoeff_subst_eq_zero a.zero _ hL

theorem Arc.parameter {x : K} {n : ℕ} {B u v : (PowerSeries K)} (a : Arc x B (n:K) u v)
    (h0 : constantCoeff B=1) (hb : q (C x) (X:(PowerSeries K))*B^2=1)
    (h1 : IsUnit (coeff 1 (BalaFormalMultiplication.primitive B))) :
    u = BalaFormalMultiplication.multiple (BalaFormalMultiplication.primitive B) h1 n := by
  let L := BalaFormalMultiplication.primitive B
  have hl0 : constantCoeff L=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [L,BalaFormalMultiplication.primitive]
  have hi := HasSubst.of_constantCoeff_zero' a.zero
  have e : L.subst u=C (n:K)*L := a.logarithm h0 hb
  unfold BalaFormalMultiplication.multiple
  change u=(L.substInvOfIsUnit h1).subst (C (n:K)*L)
  rw [← e,← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl0) hi,
    subst_substInvOfIsUnit_left L hl0 h1,subst_X hi]

theorem multiple_arc {x : K} (B : (PowerSeries K)) (h0 : constantCoeff B=1)
    (hb : q (C x) (X:(PowerSeries K))*B^2=1) (h1 : IsUnit (coeff 1 (BalaFormalMultiplication.primitive B)))
    (n : ℕ) : let u := BalaFormalMultiplication.multiple (BalaFormalMultiplication.primitive B) h1 n
              ∃ v, Arc x B (n:K) u v := by
  let L := BalaFormalMultiplication.primitive B
  let u := BalaFormalMultiplication.multiple L h1 n
  have hl0 : constantCoeff L=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [L,BalaFormalMultiplication.primitive]
  obtain ⟨hu,hm⟩ := BalaFormalMultiplication.multiple_spec L hl0 h1 n
  change constantCoeff u=0 at hu
  change L.subst u=C (n:K)*L at hm
  let v := q (C x) u*(B.subst u)
  have hunit : v*(B.subst u)=1 := by
    dsimp [v]; rw [mul_assoc,← sq,subst_quartic hu hb]
  refine ⟨v,hu,?_,?_,?_⟩
  · simp [v,q,hu,subst_one_at hu h0]
  · change (q (C x) u*(B.subst u))^2=q (C x) u
    linear_combination q (C x) u*subst_quartic hu hb
  · have hd := congrArg (derivative K) hm
    rw [derivative_subst (HasSubst.of_constantCoeff_zero' hu)] at hd
    simp only [L,BalaFormalMultiplication.derivative_primitive,Derivation.leibniz,
      smul_eq_mul,derivative_C,mul_zero,add_zero] at hd
    change derivative K u=C (n:K)*v*B
    linear_combination v*hd-derivative K u*hunit

/-- Doubling and differential addition for every logarithm-defined multiple.
All factors are cleared, so the formulas also apply at the origin. -/
theorem recurrences {x : K} (B : (PowerSeries K)) (h0 : constantCoeff B=1)
    (hb : q (C x) (X:(PowerSeries K))*B^2=1) (h1 : IsUnit (coeff 1 (BalaFormalMultiplication.primitive B))) :
    let f := BalaFormalMultiplication.multiple (BalaFormalMultiplication.primitive B) h1
    f 0=0 ∧ f 1=X ∧ ∀ m : ℕ,
      (f (2*m))^2*(1-(f m)^4)^2=4*(f m)^2*q (C x) (f m) ∧
      f (2*m+1)*X*(1-(f (m+1))^2*(f m)^2)=(f (m+1))^2-(f m)^2 := by
  let f := BalaFormalMultiplication.multiple (BalaFormalMultiplication.primitive B) h1
  have az : Arc x B ((0:ℕ):K) (0:(PowerSeries K)) 1 := by constructor <;> simp [q]
  have aX : Arc x B ((1:ℕ):K) (X:(PowerSeries K)) (q (C x) X*B) := by
    constructor
    · simp
    · simp [q,h0]
    · linear_combination q (C x) (X:(PowerSeries K))*hb
    · simp; rw [mul_assoc,← sq,hb]
  have e1 : f 1=X := (aX.parameter h0 hb h1).symm
  refine ⟨(az.parameter h0 hb h1).symm,e1,?_⟩
  intro m
  obtain ⟨w,b⟩ := multiple_arc B h0 hb h1 m
  obtain ⟨y,c⟩ := multiple_arc B h0 hb h1 (m+1)
  change Arc x B (m:K) (f m) w at b
  change Arc x B ((m+1:ℕ):K) (f (m+1)) y at c
  have add := b.add b
  rw [show (m:K)+m=((2*m:ℕ):K) by push_cast; ring] at add
  have plus := c.add b
  rw [show ((m+1:ℕ):K)+m=((2*m+1:ℕ):K) by push_cast; ring] at plus
  have minus := c.add b.neg
  rw [show ((m+1:ℕ):K)+ -(m:K)=((1:ℕ):K) by push_cast; ring] at minus
  constructor
  · have ht := add.parameter h0 hb h1
    change addT (f m) w (f m) w=f (2*m) at ht
    have hi := PowerSeries.mul_inv_cancel (den (f m) (f m)) (by simp [den,b.zero])
    have he : f (2*m)*den (f m) (f m)=2*f m*w := by
      rw [← ht]; unfold addT num
      linear_combination 2*f m*w*hi
    have hd : den (f m) (f m)=1-(f m)^4 := by unfold den; ring
    rw [← hd,← mul_pow,he,← b.curve]; ring
  · have he := add_product c b
    rw [plus.parameter h0 hb h1,minus.parameter h0 hb h1] at he
    change f (2*m+1)*f 1*den (f (m+1)) (f m)=_ at he
    rwa [e1] at he

end
end BalaJacobi

/- Integral polynomial representatives for the Jacobi multiplication recurrences. -/
namespace BalaDivision
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R]
/-- A polynomial with a specified upper degree, including leading zero coefficients. -/
structure Form (R : Type*) [CommRing R] (d : ℕ) where
  val : R[X]
  bound : val.natDegree ≤ d

namespace Form
variable {d e : ℕ}
theorem ext {a b : Form R d} (h : a.val=b.val) : a=b := by cases a; cases b; congr
def rev (a : Form R d) : Form R d :=
  ⟨a.val.reflect d,natDegree_reflect_le.trans (max_le le_rfl a.bound)⟩
def mul (a : Form R d) (b : Form R e) : Form R (d+e) :=
  ⟨a.val*b.val,natDegree_mul_le.trans (Nat.add_le_add a.bound b.bound)⟩
def add (a b : Form R d) : Form R d :=
  ⟨a.val+b.val,(natDegree_add_le ..).trans (max_le a.bound b.bound)⟩
def sub (a b : Form R d) : Form R d :=
  ⟨a.val-b.val,(natDegree_sub_le ..).trans (max_le a.bound b.bound)⟩
def scale (c : R) (a : Form R d) : Form R d :=
  ⟨C c*a.val,(natDegree_C_mul_le ..).trans a.bound⟩
def X : Form R 1 := ⟨Polynomial.X,natDegree_X_le⟩
def one (d : ℕ) : Form R d := ⟨1,by simp⟩
@[simp] theorem rev_rev (a : Form R d) : a.rev.rev=a := Form.ext reflect_reflect
@[simp] theorem rev_mul (a : Form R d) (b : Form R e) : (a.mul b).rev=a.rev.mul b.rev :=
  ext (reflect_mul _ _ a.bound b.bound)
@[simp] theorem rev_add (a b : Form R d) : (a.add b).rev=a.rev.add b.rev := ext (reflect_add ..)
@[simp] theorem rev_sub (a b : Form R d) : (a.sub b).rev=a.rev.sub b.rev := ext (reflect_sub ..)
@[simp] theorem rev_scale (c : R) (a : Form R d) : (a.scale c).rev=a.rev.scale c := ext (reflect_C_mul ..)
@[simp] theorem rev_X : (X : Form R 1).rev=one 1 := ext reflect_one_X
@[simp] theorem rev_one : (one 1 : Form R 1).rev=X := by rw [← rev_X,rev_rev]
end Form


abbrev P (R : Type*) [CommRing R] (d : ℕ) := Form R d × Form R d
def Reflects {d : ℕ} (a : P R d) (even : Bool) :=
  if even then a.1.rev=a.1 ∧ a.2.rev=a.2 else a.1.rev=a.2 ∧ a.2.rev=a.1

def double {d : ℕ} (x : R) (a : P R d) : P R ((d+d)+(d+d)) :=
  let n := a.1
  let v := a.2
  let n2 := n.mul n
  let v2 := v.mul v
  let nv := n.mul v
  let t := (v2.sub (nv.scale (2*x))).add n2
  let b := v2.sub n2
  ⟨(nv.mul t).scale 4,b.mul b⟩

theorem double_reflects {d : ℕ} (x : R) (a : P R d) (e : Bool) (h : Reflects a e) :
    Reflects (double x a) true := by
  cases e <;> simp only [Reflects,Bool.false_eq_true,if_false,if_true] at h ⊢ <;>
    obtain ⟨hn,hv⟩ := h <;> simp only [double,Form.rev_scale,Form.rev_mul,
        Form.rev_sub,Form.rev_add,hn,hv] <;>
    constructor <;> first | trivial | (apply Form.ext; dsimp [Form.mul,Form.sub,Form.add,Form.scale]; ring)

/-- Difference numerator and denominator for two adjacent indices, in that order. -/
def difference {d e : ℕ} (a : P R d) (b : P R e) : P R (d+e) :=
  ((a.1.mul b.2).sub (a.2.mul b.1),(a.2.mul b.2).sub (a.1.mul b.1))

theorem difference_reflects {d e : ℕ} (a : P R d) (b : P R e) (j : Bool)
    (ha : Reflects a j) (hb : Reflects b (!j)) :
    let pair := difference a b
    pair.1.rev=pair.2 ∨ pair.1.rev.val= -pair.2.val := by
  cases j <;> simp only [Reflects,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_true,if_false] at ha hb <;>
    obtain ⟨ha1,ha2⟩ := ha <;> obtain ⟨hb1,hb2⟩ := hb <;>
    simp only [difference,Form.rev_sub,Form.rev_mul,ha1,ha2,hb1,hb2]
  · exact Or.inl trivial
  · right; dsimp [Form.sub]; ring

/-- Remove the factor X at one end of a reciprocal pair; this reduces its padded degree by one. -/
theorem strip {d : ℕ} (a b : Form R (1+d)) (h0 : a.val.coeff 0=0)
    (hrev : a.rev=b ∨ a.rev.val= -b.val) :
    ∃ u v : Form R d, a.val=Polynomial.X*u.val ∧ v.val=b.val ∧
      (u.rev=v ∨ u.rev.val= -v.val) := by
  let u : Form R d := ⟨a.val.divX,by rw [natDegree_divX_eq_natDegree_tsub_one]; have := a.bound; omega⟩
  have ha : a.val=Polynomial.X*u.val := by simpa [u,h0] using (X_mul_divX_add a.val).symm
  have e : a.rev.val=u.rev.val := by
    change reflect (1+d) a.val=reflect d u.val
    rw [ha,reflect_mul _ _ natDegree_X_le u.bound,reflect_one_X,one_mul]
  rcases hrev with hp|hm
  · have hv : u.rev.val=b.val := e.symm.trans (congrArg Form.val hp)
    exact ⟨u,u.rev,ha,hv,Or.inl rfl⟩
  · have hv : u.rev.val= -b.val := e.symm.trans hm
    let v : Form R d := ⟨b.val,by rw [← neg_neg b.val,← hv,natDegree_neg]; exact u.rev.bound⟩
    exact ⟨u,v,ha,rfl,Or.inr hv⟩

def Normal {d : ℕ} (a : P R d) := a.1.val.eval 0=0 ∧ a.2.val.eval 0=1

variable {K : Type*} [Field K]

/-- Lists polynomials in t² as power series in t. -/
def ev (ι : R →+* K) : R[X] →+* (PowerSeries K) := eval₂RingHom (PowerSeries.C.comp ι) (PowerSeries.X^2)

structure Rep (ι : R →+* K) (u : (PowerSeries K)) (d : ℕ) (even : Bool) (a : P R d) : Prop where
  normal : Normal a
  mirror : Reflects a even
  equation : u^2*ev ι a.2.val=ev ι a.1.val

theorem rep_double {ι : R →+* K} {d : ℕ} {even : Bool} {u v : (PowerSeries K)} {a : P R d}
    (x : R) (r : Rep ι u d even a)
    (h : v^2*(1-u^4)^2=4*u^2*BalaJacobi.q (PowerSeries.C (ι x)) u) :
    Rep ι v _ true (double x a) := by
  obtain ⟨hn,hd⟩ := r.normal
  refine ⟨?_,double_reflects x a even r.mirror,?_⟩
  · simp [Normal,double,Form.scale,Form.mul,Form.sub,Form.add,hn,hd]
  · have ec (c : R) : ev ι (C c)=PowerSeries.C (ι c) := by simp [ev]
    simp only [double,Form.mul,Form.add,Form.sub,Form.scale,map_mul,map_add,map_sub,ec,← r.equation,
      map_ofNat] 
    unfold BalaJacobi.q at h
    linear_combination (ev ι a.2.val)^4*h

/-- The signed pair for an odd index gives the unsigned pair of its square. -/
def oddPair {d : ℕ} (u v : Form R d) : P R (1+(d+d)) :=
  (Form.X.mul (u.mul u),(Form.one 1).mul (v.mul v))

theorem rep_odd {ι : R →+* K} {d : ℕ} (u v : Form R d) {f : (PowerSeries K)}
    (hv : v.val.eval 0=1) (hr : u.rev=v ∨ u.rev.val= -v.val)
    (eqn : f*ev ι v.val=PowerSeries.X*ev ι u.val) : Rep ι f _ false (oddPair u v) := by
  have ht : (PowerSeries.X:(PowerSeries K))^2=ev ι Polynomial.X := by simp [ev]
  refine ⟨?_,?_,?_⟩
  · simp [Normal,oddPair,Form.X,Form.one,Form.mul,hv]
  · change (oddPair u v).1.rev=(oddPair u v).2 ∧ (oddPair u v).2.rev=(oddPair u v).1
    suffices hi : (oddPair u v).1.rev=(oddPair u v).2 from ⟨hi,by rw [← hi,Form.rev_rev]⟩
    simp only [oddPair,Form.rev_mul,Form.rev_X]
    rcases hr with hr|hr
    · rw [hr]
    · apply Form.ext
      dsimp only [Form.mul]; rw [hr]; ring
  · simp only [oddPair,Form.mul,Form.one,Form.X,map_mul,one_mul,← ht]
    linear_combination (f*ev ι v.val+PowerSeries.X*ev ι u.val)*eqn

theorem difference_eq {ι : R →+* K} {d e : ℕ} {j : Bool} {a : P R d} {b : P R e}
    {u v f : (PowerSeries K)} (ha : Rep ι u d j a) (hb : Rep ι v e (!j) b)
    (h : f*PowerSeries.X*(1-u^2*v^2)=u^2-v^2) :
    let t := difference a b
    t.1.val.eval 0=0 ∧ t.2.val.eval 0=1 ∧
    f*PowerSeries.X*ev ι t.2.val=ev ι t.1.val := by
  obtain ⟨an,ad⟩ := ha.normal
  obtain ⟨bn,bd⟩ := hb.normal
  simp only [difference,Form.sub,Form.mul,eval_sub,eval_mul,an,ad,bn,bd,
    zero_mul,mul_zero,one_mul,sub_zero,map_sub,map_mul,← ha.equation,← hb.equation]
  refine ⟨trivial,trivial,?_⟩
  linear_combination ev ι a.2.val*ev ι b.2.val*h

/-- A reciprocal certificate with the sign retained before squaring. -/
def OddCert (ι : R →+* K) (f : (PowerSeries K)) (d : ℕ) :=
  ∃ u v : Form R d, v.val.eval 0=1 ∧ (u.rev=v ∨ u.rev.val= -v.val) ∧
    f*ev ι v.val=PowerSeries.X*ev ι u.val

private theorem strip_eq {ι : R →+* K} {k l : ℕ} (p : P R k) {f : (PowerSeries K)} (len : k=1+l)
    (an : p.1.val.eval 0=0) (ad : p.2.val.eval 0=1)
    (eqn : f*PowerSeries.X*ev ι p.2.val=ev ι p.1.val)
    (hr : p.1.rev=p.2 ∨ p.1.rev.val= -p.2.val) : OddCert ι f l := by
  subst k
  obtain ⟨U,V,hh,hv,hs⟩ := strip p.1 p.2 (by simpa only [coeff_zero_eq_eval_zero] using an) hr
  refine ⟨U,V,hv ▸ ad,hs,?_⟩
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=K))
  rw [hv]
  rw [hh,map_mul] at eqn
  have hx : ev ι Polynomial.X=(PowerSeries.X:(PowerSeries K))^2 := by simp [ev]
  rw [hx] at eqn
  linear_combination eqn

theorem difference_cert {ι : R →+* K} {d e l : ℕ} {j : Bool} {a : P R d} {b : P R e}
    {u v f : (PowerSeries K)} (ha : Rep ι u d j a) (hb : Rep ι v e (!j) b)
    (len : d+e=1+l) (h : f*PowerSeries.X*(1-u^2*v^2)=u^2-v^2) :
    OddCert ι f l := by
  obtain ⟨an,ad,eqn⟩ := difference_eq ha hb h
  have hr := difference_reflects a b j ha.mirror hb.mirror
  exact strip_eq (difference a b) len an ad eqn hr

/-- Normalized odd multiplication has reciprocal numerator and denominator
of the required degree, over the original coefficient ring. -/
theorem all_indices (ι : R →+* K) (x : R) (f : ℕ → (PowerSeries K)) (h1 : f 1=PowerSeries.X)
    (rec : ∀ m : ℕ, (f (2*m))^2*(1-(f m)^4)^2=4*(f m)^2*BalaJacobi.q (PowerSeries.C (ι x)) (f m) ∧
      f (2*m+1)*PowerSeries.X*(1-(f (m+1))^2*(f m)^2)=(f (m+1))^2-(f m)^2) (n : ℕ) :
    0<n → (∃ a : P R (n^2), Rep ι (f n) _ (decide (n%2=0)) a) ∧
      (n%2=1 → OddCert ι (f n) (n^2/2)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases base : n=1
    · subst n
      have hc : OddCert ι (f 1) 0 := by
        refine ⟨Form.one 0,Form.one 0,by simp [Form.one],Or.inl ?_,?_⟩
        · apply Form.ext; simp [Form.one,Form.rev,reflect_one]
        · simp [Form.one,h1]
      obtain ⟨u,v,hv,hr,eqn⟩ := id hc
      exact ⟨⟨_,rep_odd u v hv hr eqn⟩,fun _ => hc⟩
    let m := n/2
    have hm : 0 < m := by dsimp [m]; omega
    have hlt : m < n := by dsimp [m]; omega
    obtain ⟨⟨b,rb⟩,_⟩ := ih m hlt hm
    by_cases even : n%2=0
    · have hn' : n=2*m := by dsimp [m]; omega
      have len : (m^2+m^2)+(m^2+m^2)=n^2 := by rw [hn']; ring
      refine ⟨?_,by omega⟩
      have dbl := rep_double x rb (rec m).1
      rw [← hn'] at dbl
      rw [← len]
      simp only [even,decide_true]
      exact ⟨_,dbl⟩
    · have hn' : n=2*m+1 := by dsimp [m]; omega
      obtain ⟨⟨a,ra⟩,_⟩ := ih (m+1) (by omega) (by omega)
      have parity : decide (m%2=0)= !(decide ((m+1)%2=0)) := by
        by_cases h : m%2=0 <;> simp [h,show (m+1)%2=0 ↔ ¬m%2=0 by omega]
      rw [parity] at rb
      have he : n^2=2*(2*m^2+2*m)+1 := by rw [hn']; ring
      have len : (m+1)^2+m^2=1+n^2/2 := by
        have e : (m+1)^2+m^2=1+(2*m^2+2*m) := by ring
        omega
      have hc := difference_cert ra rb len (rec m).2
      rw [← hn'] at hc
      obtain ⟨u,v,hv,hr,eqn⟩ := id hc
      have hrp := rep_odd u v hv hr eqn
      refine ⟨?_,fun _ => hc⟩
      have e : n^2=1+(n^2/2+n^2/2) := by omega
      -- Transport only the polynomial pair, keeping the index of f fixed.
      have ex : ∃ a : P R (1+(n^2/2+n^2/2)), Rep ι (f n) _ false a := ⟨_,hrp⟩
      rw [← e] at ex
      simpa [even] using ex

end
end BalaDivision

/- The all-prime elliptic congruence for the normalized quartic differential. -/
namespace BalaElliptic
open PowerSeries
noncomputable section

variable {K : Type*} [Field K] (R : Subring K)

private theorem ev_expand (P : Polynomial R) :
    BalaDivision.ev R.subtype P=map R.subtype (Polynomial.expand R 2 P : PowerSeries R) := by
  induction P using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add,Polynomial.coe_add,ha,hb]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [BalaDivision.ev,Polynomial.expand_eq_comp_X_pow]

/-- Lift the full multiplication series to the integral ring and recover the
top coefficient and the denominator divisibility from signed reciprocity. -/
theorem integral_coordinates {f : PowerSeries K} {p d : ℕ}
    (cert : BalaDivision.OddCert R.subtype f d)
    (low : ∀ i < 2*d+1, ∃ a : R, coeff i f=(p:K)*(a:K)) :
    ∃ g V : PowerSeries R, map R.subtype g=f ∧ coeff 0 V=1 ∧
      (∀ i < 2*d+1, (p:R) ∣ coeff i g) ∧
      (∀ j, 0<j → j≤2*d+1 → (p:R) ∣ coeff j V) ∧
      (coeff (2*d+1) (g*V))^2=1 := by
  obtain ⟨u,v,h0,hr,eqn⟩ := cert
  let U := Polynomial.X * Polynomial.expand R 2 u.val
  let V := Polynomial.expand R 2 v.val
  have hv0 : coeff 0 (V:PowerSeries R)=1 := by
    rw [Polynomial.coeff_coe,show V=Polynomial.expand R 2 v.val from rfl,
      Polynomial.coeff_expand (by decide),if_pos (dvd_zero _),Nat.zero_div,
      Polynomial.coeff_zero_eq_eval_zero,h0]
  have hv : constantCoeff (V:PowerSeries R)=1 := by rwa [← coeff_zero_eq_constantCoeff_apply]
  let g := (U:PowerSeries R)*(V:PowerSeries R).invOfUnit 1
  have hg : g*(V:PowerSeries R)=(U:PowerSeries R) := by
    rw [show g=_ from rfl,mul_assoc,invOfUnit_mul _ _ hv,mul_one]
  have hm : map R.subtype g=f := by
    have he : f*map R.subtype (V:PowerSeries R)=map R.subtype (U:PowerSeries R) := by
      simpa only [U,V,Polynomial.coe_mul,Polynomial.coe_X,map_mul,map_X,← ev_expand] using eqn
    have hv' : map R.subtype (V:PowerSeries R)≠0 := by
      intro hz
      have hc := congrArg (coeff 0) hz
      rw [coeff_map,hv0,map_one] at hc
      simp at hc
    apply mul_right_cancel₀ hv'
    rw [← map_mul,hg,he]
  have hl (i : ℕ) (hi : i<2*d+1) : (p:R) ∣ coeff i g := by
    obtain ⟨a,ha⟩ := low i hi
    use a
    apply Subtype.ext
    rw [← hm,coeff_map] at ha
    change ((coeff i g : R):K)=(p:K)*(a:K)
    exact ha
  have hU (i : ℕ) (hi : i<2*d+1) : (p:R) ∣ U.coeff i := by
    rw [← Polynomial.coeff_coe,← hg,coeff_mul]
    apply Finset.dvd_sum
    intro ab hab
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    exact dvd_mul_of_dvd_left (hl _ (by omega)) _
  have coeffU (j : ℕ) : U.coeff (2*j+1)=u.val.coeff j := by
    rw [show U=_ from rfl,Polynomial.coeff_X_mul,Polynomial.coeff_expand_mul' (by decide)]
  have mirror (j : ℕ) (hj : j≤d) : u.val.coeff (d-j)=v.val.coeff j ∨
      u.val.coeff (d-j)= -(v.val.coeff j) := by
    rcases hr with ht|ht
    · left
      have h := congrArg (fun t : BalaDivision.Form R d => t.val.coeff j) ht
      simpa [BalaDivision.Form.rev,Polynomial.revAt_le hj] using h
    · right
      have h := congrArg (fun t : Polynomial R => t.coeff j) ht
      simpa [BalaDivision.Form.rev,Polynomial.revAt_le hj] using h
  refine ⟨g,(V:PowerSeries R),hm,hv0,hl,?_,?_⟩
  · intro j hj hle
    rw [Polynomial.coeff_coe,show V=_ from rfl,Polynomial.coeff_expand (by decide)]
    split_ifs with even
    · have hj' : 0<j/2 ∧ j/2≤d := by omega
      have hh := hU (2*(d-j/2)+1) (by omega)
      rw [coeffU] at hh
      rcases mirror (j/2) hj'.2 with ht|ht <;> simpa [ht] using hh
    · exact dvd_zero _
  · rw [hg,Polynomial.coeff_coe,coeffU]
    have he := mirror 0 (Nat.zero_le d)
    rw [Nat.sub_zero,Polynomial.coeff_zero_eq_eval_zero,h0] at he
    rcases he with he|he <;> simp [he]

variable [CharZero K]

set_option maxHeartbeats 500000 in
theorem quartic_precision {p : ℕ} [Fact p.Prime] (hp : 3≤p) (odd : p%2=1)
    (units : ∀ n : ℕ, ¬p ∣ n → (n:K)⁻¹ ∈ R)
    (x : R) (B : PowerSeries R) (B0 : constantCoeff B=1)
    (BE : (BalaReduction.quartic x : PowerSeries R)*B^2=1)
    (f : PowerSeries K) (f0 : constantCoeff f=0)
    (hm : (BalaFormalMultiplication.primitive (map R.subtype B)).subst f=
      C (p:K)*BalaFormalMultiplication.primitive (map R.subtype B))
    (low : ∀ n < p^2, ∃ a : R, coeff n f=(p:K)*(a:K)) :
    (p:R)^4 ∣ (coeff (p^2-1) B)^2-(p:R)^2 := by
  let b := map R.subtype B
  let L := BalaFormalMultiplication.primitive b
  have hB0 : constantCoeff b=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply,show b=_ from rfl,coeff_map,
      coeff_zero_eq_constantCoeff_apply,B0,map_one]
  have hL0 : constantCoeff L=0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [L,BalaFormalMultiplication.primitive]
  have hL1 : coeff 1 L=1 := by simp [L,BalaFormalMultiplication.primitive,coeff_zero_eq_constantCoeff_apply,hB0]
  have h1 : IsUnit (coeff 1 L) := hL1 ▸ isUnit_one
  have hq : BalaJacobi.q (C (R.subtype x)) X*b^2=1 := by
    have hQ : (BalaReduction.quartic x : PowerSeries R) = 1-C (2*x)*X^2+X^4 := by
      simp only [BalaReduction.quartic,Polynomial.coe_add,Polynomial.coe_sub,Polynomial.coe_mul,
        Polynomial.coe_pow,Polynomial.coe_C,Polynomial.coe_one,Polynomial.coe_X]
    rw [hQ] at BE
    have h := congrArg (map R.subtype) BE
    simp only [map_mul,map_add,map_sub,map_C,map_pow,map_X,map_one] at h
    simpa only [b,BalaJacobi.q,map_mul,map_ofNat] using h
  let F := BalaFormalMultiplication.multiple L h1
  have hf : F p=f := by
    change (L.substInvOfIsUnit h1).subst (C (p:K)*L)=f
    change L.subst f=C (p:K)*L at hm
    rw [← hm,← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hL0)
      (HasSubst.of_constantCoeff_zero' f0),subst_substInvOfIsUnit_left L hL0 h1,
      subst_X (HasSubst.of_constantCoeff_zero' f0)]
  obtain ⟨_,one,rec⟩ := BalaJacobi.recurrences b hB0 hq h1
  have hc := ((BalaDivision.all_indices R.subtype x F one rec p (by omega)).2 odd)
  rw [hf] at hc
  have d : 2*(p^2/2)+1=p^2 := by
    have hp' : p=2*(p/2)+1 := by omega
    have e : p^2=2*(2*(p/2)^2+2*(p/2))+1 := by
      conv_lhs => rw [hp']
      ring
    omega
  obtain ⟨g,V,hg,hV,hlo,hpos,htop⟩ := integral_coordinates R hc (d ▸ low)
  rw [d] at hlo hpos htop
  have hg0 : constantCoeff g=0 := by
    have he := congrArg (coeff 0) hg
    rw [coeff_map,coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,f0] at he
    apply R.subtype_injective
    rw [map_zero]
    exact he
  let c := fun n : ℕ => coeff (n-1) B
  have hL (n : ℕ) : coeff n L=(c n:K)/(n:K) := by simp [L,b,c,BalaFormalMultiplication.primitive]
  have he := BalaAudit.coefficient_identity L f (p:K) f0 (by
    rwa [coeff_zero_eq_constantCoeff_apply]) hL1 hm (p^2)
  rw [← hg] at he
  simp only [hL,← map_pow,coeff_map,Subring.coe_subtype,div_mul_eq_mul_div] at he
  have hlog := BalaAudit.logarithm_precision R hp units g V c hlo hg0 hpos hV (by
    rw [← he]; push_cast; field_simp)
  apply BalaAudit.square_precision (p:R) (coeff (p^2) (g*V)) _ htop
  simpa only [mul_comm (p:R)] using hlog

/-- With only the eligibility hypothesis, the normalized differential on the
lift at x²=−63 satisfies the degree-p² squared congruence. -/
theorem eligible (p : ℕ) (eligible : OeisA3625.A p) :
    let _ : Fact p.Prime := ⟨eligible.1⟩
    let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_local p eligible⟩
    let R := BalaLocalRing.localRing p
    ∃ (x : R) (B : PowerSeries R), x^2= -63 ∧ constantCoeff B=1 ∧
      (BalaReduction.quartic x : PowerSeries R)*B^2=1 ∧ ((p:R)^4 ∣ (coeff (p^2-1) B)^2-(p:R)^2) ∧
      ∀ n, p ∣ n+1 → (p:R) ∣ coeff n B := by
  let _ : Fact p.Prime := ⟨eligible.1⟩
  let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_local p eligible⟩
  let R := BalaLocalRing.localRing p
  obtain ⟨s,B,L,f,hs,B0,BE,rfl,f0,hm,low,cartier⟩ := BalaFormalMultiplication.eligible_multiplication p eligible
  have hne : p≠2 := by rintro rfl; norm_num [OeisA3625.A] at eligible
  have hp := eligible.1.two_le
  refine ⟨3*s,B,?_,B0,BE,quartic_precision R (by omega)
    ((Nat.Prime.mod_two_eq_one_iff_ne_two eligible.1).mpr hne)
    (BalaLocalRing.inverse_mem p eligible) (3*s) B B0 BE f f0 hm low,cartier⟩
  linear_combination 9*hs

end
end BalaElliptic

/- Identification of the normalized quartic differential with the Legendre recurrence. -/
namespace BalaLegendre
open PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Legendre values in characteristic zero, normalized by P₀=1 and P₁=x. -/
def value (x : K) : ℕ → K
  | 0 => 1
  | 1 => x
  | n+2 => (((2*(n:K)+3)*x)*value x (n+1)-((n:K)+1)*value x n)/((n:K)+2)

private theorem euler_coeff (B : PowerSeries K) (n : ℕ) :
    coeff n (X*derivative K B)=(n:K)*coeff n B := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [← pow_one (X:PowerSeries K),coeff_X_pow_mul,coeff_derivative]
    push_cast; ring

theorem generating_coeff (x : K) (B : PowerSeries K) (h0 : constantCoeff B=1)
    (hq : BalaJacobi.q (C x) X*B^2=1) (n : ℕ) : coeff (2*n) B=value x n := by
  let D := X*derivative K B
  have hd := congrArg (derivative K) hq
  have d2 : derivative K (2:PowerSeries K)=0 := by
    rw [show (2:PowerSeries K)=C (2:K) by rw [map_ofNat]]; exact derivative_C
  simp [BalaJacobi.q,Derivation.leibniz,smul_eq_mul,d2] at hd
  have hn : B ≠ 0 := by intro he; simp [he] at h0
  have two : (2:PowerSeries K) ≠ 0 := by
    intro he; have h := congrArg constantCoeff he; norm_num [map_ofNat] at h
  have h : D+X^4*(D+C (2:K)*B)=C (2*x)*(X^2*(D+B)) := by
    apply mul_left_cancel₀ (mul_ne_zero two hn)
    dsimp [D]; rw [map_mul,map_ofNat]
    linear_combination X*hd
  have atN (i : ℕ) := congrArg (coeff i) h
  have hD (i : ℕ) : coeff i D=(i:K)*coeff i B := euler_coeff B i
  have eqn (k : ℕ) :
      ((k:K)+4)*coeff (k+4) B+((k:K)+2)*coeff k B =
        (2*x)*((k:K)+3)*coeff (k+2) B := by
    have e := atN (k+4)
    simp only [map_add,coeff_C_mul,coeff_X_pow_mul',show 4≤k+4 by omega,
      show 2≤k+4 by omega,if_true,show k+4-4=k by omega,show k+4-2=k+2 by omega,
      hD,Nat.cast_add,Nat.cast_ofNat] at e
    linear_combination e
  induction n using Nat.twoStepInduction with
  | zero => simpa [value,coeff_zero_eq_constantCoeff_apply] using h0
  | one =>
    have e := atN 2
    simp only [map_add,coeff_C_mul,coeff_X_pow_mul',show ¬4≤2 by decide,if_false,
      show 2≤2 by decide,if_true,Nat.sub_self,hD,Nat.cast_zero,zero_add,
      add_zero,Nat.cast_ofNat,coeff_zero_eq_constantCoeff_apply,h0,mul_one] at e
    change coeff 2 B=x
    linear_combination e/2
  | more n ha hb =>
    rw [value,eq_div_iff (by exact_mod_cast (by omega : n+2≠0))]
    rw [← ha,← hb]
    have hh := eqn (2*n)
    push_cast at hh
    rw [show 2*(n+2)=2*n+4 by omega,show 2*(n+1)=2*n+2 by omega]
    linear_combination hh/2

end
end BalaLegendre

/- A terminating square identity for the Legendre polynomials. -/
namespace BalaClausen
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def term (K : Type*) [Field K] (n k : ℕ) : K :=
  (Nat.centralBinom k:K)^2*((n+k).choose (2*k):K)

theorem down (n k : ℕ) : term K n k =
    ((n:K)+1-k)/((n:K)+k+1)*term K (n+1) k := by
  have hp : (n:K)+k+1 ≠ 0 := by exact_mod_cast (by omega : n+k+1 ≠ 0)
  by_cases hk : 2*k≤n+k+1
  · have e := congrArg (fun a : ℕ => (a:K)) (Nat.choose_mul_succ_eq (n+k) (2*k))
    push_cast [Nat.cast_sub hk] at e
    unfold term
    rw [show n+1+k=n+k+1 by omega]
    field_simp
    linear_combination (Nat.centralBinom k:K)^2*e
  · unfold term
    rw [Nat.choose_eq_zero_of_lt (by omega : n+k<2*k),
      Nat.choose_eq_zero_of_lt (by omega : n+1+k<2*k)]
    simp

theorem diagonal (n k : ℕ) : term K n k =
    ((k:K)+1)^3/(2*(2*(k:K)+1)*((n:K)+k+2)*((n:K)+k+1))*term K (n+1) (k+1) := by
  let c := (Nat.centralBinom k:K)
  let d := (Nat.centralBinom (k+1):K)
  let a := ((n+k).choose (2*k):K)
  let b := ((n+k+1).choose (2*k+1):K)
  let e := ((n+k+2).choose (2*k+2):K)
  have hcd : ((k:K)+1)*d=2*(2*(k:K)+1)*c := by dsimp [c,d]; exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hab : ((n:K)+k+1)*a=b*(2*(k:K)+1) := by dsimp [a,b]; exact_mod_cast Nat.add_one_mul_choose_eq (n+k) (2*k)
  have hbe : ((n:K)+k+2)*b=e*(2*(k:K)+2) := by
    simpa only [b,e,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,add_assoc,one_add_one_eq_two] using
      congrArg (fun i : ℕ => (i:K)) (Nat.add_one_mul_choose_eq (n+k+1) (2*k+1))
  unfold term
  rw [show n+1+(k+1)=n+k+2 by omega,show 2*(k+1)=2*k+2 by omega]
  change c^2*a=_*(d^2*e)
  have hk : 2*(k:K)+1 ≠ 0 := by exact_mod_cast (by omega : 2*k+1 ≠ 0)
  have hn1 : (n:K)+k+1 ≠ 0 := by exact_mod_cast (by omega : n+k+1 ≠ 0)
  have hn2 : (n:K)+k+2 ≠ 0 := by exact_mod_cast (by omega : n+k+2 ≠ 0)
  have hk1 : (k:K)+1 ≠ 0 := by exact_mod_cast (by omega : k+1 ≠ 0)
  have hd : d=2*(2*(k:K)+1)*c/((k:K)+1) := (eq_div_iff hk1).mpr (by linear_combination hcd)
  have ha : a=b*(2*(k:K)+1)/((n:K)+k+1) := (eq_div_iff hn1).mpr (by linear_combination hab)
  have hb : b=e*(2*(k:K)+2)/((n:K)+k+2) := (eq_div_iff hn2).mpr (by linear_combination hbe)
  rw [hd,ha,hb]
  field_simp

private def a (n : K) := 2*n+3
private def b (n : K) := 2*n+5
private def w (n : K) := a n*b n-(n+2)^2

set_option maxHeartbeats 2000000 in
theorem term_rec (n k : ℕ) :
    ((n:K)+3)^2*a (n:K)*term K (n+3) (k+1) =
      w (n:K)*(b (n:K)*term K (n+2) (k+1)-a (n:K)*term K (n+1) (k+1))+
      4*a (n:K)*b (n:K)*(b (n:K)*term K (n+2) k-a (n:K)*term K (n+1) k)+
      ((n:K)+1)^2*b (n:K)*term K n (k+1) := by
  rw [down n (k+1),down (n+1) (k+1),down (n+2) (k+1),down (n+1) k,diagonal (n+2) k]
  push_cast
  unfold w a b
  have z2 : (n:K)+k+2≠0 := by exact_mod_cast (by omega : n+k+2≠0)
  have z3 : (n:K)+k+3≠0 := by exact_mod_cast (by omega : n+k+3≠0)
  have z4 : (n:K)+k+4≠0 := by exact_mod_cast (by omega : n+k+4≠0)
  have zk : 2*(k:K)+1≠0 := by exact_mod_cast (by omega : 2*k+1≠0)
  simp only [show (n:K)+2+(k+1)+1=n+k+4 by ring,
    show (n:K)+1+(k+1)+1=n+k+3 by ring,show (n:K)+(k+1)+1=n+k+2 by ring,
    show (n:K)+1+k+1=n+k+2 by ring,show (n:K)+2+k+2=n+k+4 by ring,
    show (n:K)+2+k+1=n+k+3 by ring]
  field_simp [z2,z3,z4,zk]
  ring


def F (K : Type*) [Field K] (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range (n+1), monomial k (term K n k)

theorem coeff_F (n k : ℕ) : (F K n).coeff k=term K n k := by
  classical
  simp only [F,finsetSum_coeff,coeff_monomial]
  by_cases hk : k≤n
  · simp [Finset.mem_range,show k<n+1 by omega]
  · have h : (n+k).choose (2*k)=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [Finset.mem_range,show ¬k<n+1 by omega,term,h]

private def combo (K : Type*) [Field K] (n : ℕ) : K[X] :=
  C (b (n:K))*F K (n+2) - C (a (n:K))*F K (n+1)

private theorem coeff_combo (n k : ℕ) : (combo K n).coeff k=
    b (n:K)*term K (n+2) k-a (n:K)*term K (n+1) k := by
  simp [combo,coeff_sub,coeff_C_mul,coeff_F]

theorem polynomial_rec (n : ℕ) :
    C (((n:K)+3)^2*a (n:K))*F K (n+3) =
      C (w (n:K))*combo K n+C (4*a (n:K)*b (n:K))*(X*combo K n)+
        C (((n:K)+1)^2*b (n:K))*F K n := by
  ext k
  cases k with
  | zero =>
    simp only [coeff_C_mul,coeff_add,coeff_X_mul_zero,coeff_combo,coeff_F,term,
      Nat.centralBinom_zero,Nat.choose_zero_right,Nat.cast_one,one_pow,mul_one,mul_zero,add_zero]
    unfold w a b; ring
  | succ k =>
    simpa only [coeff_C_mul,coeff_add,coeff_X_mul,coeff_combo,coeff_F] using term_rec (K:=K) n k

private def weighted (x : K) (n : ℕ) := (F K n).eval ((x^2-1)/4)

private theorem weighted_rec (x : K) (n : ℕ) :
    ((n:K)+3)^2*a (n:K)*weighted x (n+3) =
      (a (n:K)*b (n:K)*x^2-((n:K)+2)^2)*
        (b (n:K)*weighted x (n+2)-a (n:K)*weighted x (n+1))+
        ((n:K)+1)^2*b (n:K)*weighted x n := by
  have e := congrArg (Polynomial.eval ((x^2-1)/4)) (polynomial_rec (K:=K) n)
  simp only [eval_mul,eval_add,eval_C,eval_X,combo,eval_sub] at e
  dsimp [weighted]
  unfold w at e
  linear_combination e

private theorem square_rec (x : K) (n : ℕ) :
    ((n:K)+3)^2*a (n:K)*(BalaLegendre.value x (n+3))^2 =
      (a (n:K)*b (n:K)*x^2-((n:K)+2)^2)*
        (b (n:K)*(BalaLegendre.value x (n+2))^2-a (n:K)*(BalaLegendre.value x (n+1))^2)+
        ((n:K)+1)^2*b (n:K)*(BalaLegendre.value x n)^2 := by
  rw [show BalaLegendre.value x (n+3) =
      (((2*((n+1:ℕ):K)+3)*x)*BalaLegendre.value x (n+2)-(((n+1:ℕ):K)+1)*BalaLegendre.value x (n+1))/
        (((n+1:ℕ):K)+2) from rfl,show BalaLegendre.value x (n+2) = _ from (BalaLegendre.value.eq_3 x n)]
  unfold a b
  push_cast
  rw [show (n:K)+1+2=n+3 by ring]
  have h2 : (n:K)+2 ≠ 0 := by exact_mod_cast (by omega : n+2≠0)
  have h3 : (n:K)+3 ≠ 0 := by exact_mod_cast (by omega : n+3≠0)
  field_simp [h2,h3]
  ring

theorem square_identity (x : K) (n : ℕ) :
    (BalaLegendre.value x n)^2 = (F K n).eval ((x^2-1)/4) := by
  change _=weighted x n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n<3
    · interval_cases n <;>
        norm_num [weighted,F,Finset.sum_range_succ,term,Nat.centralBinom,BalaLegendre.value,
          Polynomial.eval_add,Polynomial.eval_monomial,Nat.choose] <;> ring
    · obtain ⟨m,rfl⟩ : ∃ m,n=m+3 := ⟨n-3,by omega⟩
      have e := square_rec x m
      rw [ih (m+2) (by omega),ih (m+1) (by omega),ih m (by omega),← weighted_rec x m] at e
      apply mul_left_cancel₀ _ e
      unfold a
      exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by omega : m+3≠0)))
        (by exact_mod_cast (by omega : 2*m+3≠0))


end
end BalaClausen

/- The integer weighted sum and its residues obtained from the elliptic congruence. -/
namespace BalaWeighted
open PowerSeries
noncomputable section

def sum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n+1), (Nat.centralBinom k:ℤ)^2*((n+k).choose (2*k):ℤ)*(-16)^k

variable {K : Type*} [Field K] [CharZero K]

theorem square (x : K) (hx : x^2= -63) (n : ℕ) : (sum n:K)=(BalaLegendre.value x n)^2 := by
  rw [BalaClausen.square_identity,hx]
  norm_num
  simp [sum,BalaClausen.F,Polynomial.eval_finsetSum,Polynomial.eval_monomial,BalaClausen.term]

/-- Exact rational weight multiplying the cube of the central binomial. -/
def weight (K : Type*) [Field K] (d k : ℕ) : K :=
  ∏ j ∈ Finset.range k, (1-((d:K)/(2*(j:K)+1))^2)

theorem weighted_term (n k : ℕ) :
    BalaClausen.term K n k*(-16)^k=(Nat.centralBinom k:K)^3*weight K (2*n+1) k := by
  induction k with
  | zero => simp [BalaClausen.term,weight]
  | succ k ih =>
    have z1 : (k:K)+1 ≠ 0 := by exact_mod_cast (by omega : k+1≠0)
    have z2 : (n:K)+k+1 ≠ 0 := by exact_mod_cast (by omega : n+k+1≠0)
    have z3 : (n:K)+k+2 ≠ 0 := by exact_mod_cast (by omega : n+k+2≠0)
    have z4 : 2*(k:K)+1 ≠ 0 := by exact_mod_cast (by omega : 2*k+1≠0)
    have hd := BalaClausen.diagonal (K:=K) n k
    have hu : BalaClausen.term K (n+1) (k+1) =
        (2*(2*(k:K)+1)*((n:K)+k+2)*((n:K)+k+1))/((k:K)+1)^3*BalaClausen.term K n k := by
      rw [hd]; field_simp
    have hcentral : (Nat.centralBinom (k+1):K) =
        2*(2*(k:K)+1)/((k:K)+1)*(Nat.centralBinom k:K) := by
      have h := congrArg (fun a : ℕ => (a:K)) (Nat.succ_mul_centralBinom_succ k)
      push_cast at h
      field_simp
      linear_combination h
    rw [BalaClausen.down n (k+1),hu,hcentral,pow_succ]
    rw [show weight K (2*n+1) (k+1) =
      weight K (2*n+1) k*(1-(((2*n+1:ℕ):K)/(2*(k:K)+1))^2) from Finset.prod_range_succ ..]
    push_cast
    rw [show (n:K)+(k+1)+1=n+k+2 by ring]
    have hc : (Nat.centralBinom k:K) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero k
    have hw : weight K (2*n+1) k=BalaClausen.term K n k*(-16)^k/(Nat.centralBinom k:K)^3 :=
      (eq_div_iff (pow_ne_zero 3 hc)).mpr (by linear_combination ih.symm)
    rw [hw]
    have hfac : 1-((2*(n:K)+1)/(2*(k:K)+1))^2 =
        (-4*((n:K)-k)*((n:K)+k+1))/(2*(k:K)+1)^2 := by
      rw [div_pow,sub_div' (by exact pow_ne_zero 2 z4)]
      congr 1
      ring
    rw [hfac]
    field_simp [z1,z2,z3,z4,hc]
    ring

theorem weighted_sum (n : ℕ) : (sum n:K)=∑ k ∈ Finset.range (n+1),
    (Nat.centralBinom k:K)^3*weight K (2*n+1) k := by
  simp only [sum,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_neg,Int.cast_ofNat]
  exact Finset.sum_congr rfl fun k _ => weighted_term n k

/-- Divisibility of a rational integer descends from our concrete quadratic ring. -/
theorem descend (p m : ℕ) [Fact p.Prime] (z : ℤ)
    (h : (p:BalaLocalRing.localRing p)^m ∣ (z:BalaLocalRing.localRing p)) :
    (p:ℤ)^m ∣ z := by
  let φ := (BalaLocalRing.changeBase (PadicInt.toZModPow (p:=p) m)).comp (BalaLocalRing.localEquiv p).symm.toRingHom
  obtain ⟨v,hv⟩ := h
  have he := congrArg φ hv
  simp only [map_intCast,map_mul,map_pow,map_natCast] at he
  have hp : (p:BalaLocalRing.Quad (ZMod (p^m)))^m=0 := by
    have hh := congrArg (algebraMap (ZMod (p^m)) (BalaLocalRing.Quad (ZMod (p^m)))) (ZMod.natCast_self (p^m))
    change (algebraMap (ZMod (p^m)) (BalaLocalRing.Quad (ZMod (p^m)))) ((p^m:ℕ):ZMod (p^m))=_ at hh
    rw [map_natCast,map_zero,Nat.cast_pow] at hh
    exact hh
  rw [hp,zero_mul] at he
  have hz : (z:ZMod (p^m))=0 := by simpa using congrArg QuadraticAlgebra.re he
  simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^m)).mp hz

theorem eligible (p : ℕ) (hp : OeisA3625.A p) :
    (p:ℤ)^4 ∣ sum ((p^2-1)/2)-(p:ℤ)^2 ∧
      ∀ n, p ∣ 2*n+1 → (p:ℤ)^2 ∣ sum n := by
  let _ : Fact p.Prime := ⟨hp.1⟩
  let _ : Fact (∀ t : ℚ_[p], t^2 ≠ -7+0*t) := ⟨BalaLocalRing.irreducible_local p hp⟩
  let R := BalaLocalRing.localRing p
  let F := BalaLocalRing.Quad ℚ_[p]
  obtain ⟨x,B,hx,B0,hQ,hb,cartier⟩ := BalaElliptic.eligible p hp
  have hx' : (x:F)^2= -63 := by exact_mod_cast congrArg R.subtype hx
  have hQ' : BalaJacobi.q (C (x:F)) X*(map R.subtype B)^2=1 := by
    have e : (BalaReduction.quartic x : PowerSeries R)=1-C (2*x)*X^2+X^4 := by
      simp only [BalaReduction.quartic,Polynomial.coe_add,Polynomial.coe_sub,Polynomial.coe_mul,
        Polynomial.coe_pow,Polynomial.coe_C,Polynomial.coe_one,Polynomial.coe_X]
    rw [e] at hQ
    have h := congrArg (map R.subtype) hQ
    simp only [map_mul,map_add,map_sub,map_C,map_pow,map_X,map_one] at h
    simpa only [BalaJacobi.q,map_mul,map_ofNat,Subring.coe_subtype] using h
  have h0 : constantCoeff (map R.subtype B)=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,B0,map_one]
  have e (n : ℕ) : (sum n:R)=(coeff (2*n) B)^2 := by
    apply R.subtype_injective
    rw [map_intCast,map_pow,square (x:F) hx',← BalaLegendre.generating_coeff (x:F) _ h0 hQ' n,coeff_map]
  have ne : p≠2 := by rintro rfl; norm_num [OeisA3625.A] at hp
  have odd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp.1).mpr ne
  have par : p^2%2=1 := by rw [Nat.pow_mod,odd]
  constructor
  · apply descend p
    push_cast
    rw [e,show 2*((p^2-1)/2)=p^2-1 by omega]
    exact hb
  · intro n hn
    apply descend p
    rw [e]
    exact pow_dvd_pow_of_dvd (cartier _ hn) 2

end
end BalaWeighted

/- Odd denominator factors are reduced only after cancelling their factor of p. -/
namespace BalaWeightsMod
noncomputable section
variable (p : ℕ) [Fact p.Prime]

def invInt (t : ℕ) : ℤ_[p] := if ht : p ∣ t then 0 else
  ⟨(t:ℚ_[p])⁻¹,by
    have h := (Padic.norm_natCast_eq_one_iff (p:=p)).mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ht)
    simp [norm_inv,h]⟩

theorem inv_spec {t : ℕ} (h : ¬p ∣ t) : PadicInt.Coe.ringHom (invInt p t)=(t:ℚ_[p])⁻¹ := by
  simp [invInt,h]; rfl

def ratio (c j : ℕ) : ℤ_[p] := if p ∣ 2*j+1 then (c:ℤ_[p])*invInt p ((2*j+1)/p)
  else (p:ℤ_[p])*c*invInt p (2*j+1)

theorem coe_ratio (c j : ℕ) (hlt : 2*j+1<p^2) :
    ((ratio p c j : ℤ_[p]):ℚ_[p])=((p*c:ℕ):ℚ_[p])/(2*(j:ℚ_[p])+1) := by
  let t := 2*j+1
  have hp := (Fact.out : p.Prime).pos
  have ht : 0<t := by dsimp [t]; omega
  have htz : (t:ℚ_[p])≠0 := by exact_mod_cast ht.ne'
  change (↑(if p ∣ t then (c:ℤ_[p])*invInt p (t/p) else (p:ℤ_[p])*c*invInt p t):ℚ_[p])=_
  rw [show 2*(j:ℚ_[p])+1=(t:ℚ_[p]) by simp [t],Nat.cast_mul]
  split_ifs with hd
  · have he := Nat.div_mul_cancel hd
    have hunit : ¬p ∣ t/p := by
      intro hh
      have hh' : p^2 ∣ t := by rw [← he,pow_two]; exact mul_dvd_mul hh dvd_rfl
      exact (not_le_of_gt hlt) (Nat.le_of_dvd ht hh')
    have hu : ((t/p:ℕ):ℚ_[p])≠0 := by exact_mod_cast (show t/p≠0 from fun ez => hunit (ez ▸ dvd_zero _))
    have he' := congrArg (fun a : ℕ => (a:ℚ_[p])) he
    simp only [Nat.cast_mul] at he'
    change PadicInt.Coe.ringHom ((c:ℤ_[p])*invInt p (t/p))=_
    rw [map_mul,map_natCast,inv_spec p hunit]
    field_simp
    linear_combination (c:ℚ_[p])*he'.symm
  · change PadicInt.Coe.ringHom ((p:ℤ_[p])*(c:ℤ_[p])*invInt p t)=_
    rw [map_mul,map_mul,map_natCast,map_natCast,inv_spec p hd,div_eq_mul_inv]


def unit (m t : ℕ) : ZMod (p^m) := PadicInt.toZModPow m (invInt p t)

def rmod (m c j : ℕ) : ZMod (p^m) := if p ∣ 2*j+1 then (c:ZMod (p^m))*unit p m ((2*j+1)/p)
  else (p:ZMod (p^m))*c*unit p m (2*j+1)

def W (m c k : ℕ) : ZMod (p^m) := ∏ j ∈ Finset.range k, (1-(rmod p m c j)^2)

theorem W_succ (m c k : ℕ) : W p m c (k+1)=W p m c k*(1-(rmod p m c k)^2) := Finset.prod_range_succ ..

theorem unit_spec (m t : ℕ) (h : ¬p ∣ t) : (t:ZMod (p^m))*unit p m t=1 := by
  have ht : (t:ℚ_[p])≠0 := by exact_mod_cast (show t≠0 from fun ez => h (ez ▸ dvd_zero _))
  have hh : (t:ℤ_[p])*invInt p t=1 := by
    apply Subtype.ext
    change PadicInt.Coe.ringHom ((t:ℤ_[p])*invInt p t)=1
    rw [map_mul,map_natCast,inv_spec p h,mul_inv_cancel₀ ht]
  simpa only [map_natCast,map_mul,map_one,unit] using congrArg (PadicInt.toZModPow m) hh

theorem sum_mod (m c n : ℕ) (hd : 2*n+1=p*c) (hb : 2*n+1≤p^2) :
    (BalaWeighted.sum n : ZMod (p^m)) =
      ∑ k ∈ Finset.range (n+1), (Nat.centralBinom k:ZMod (p^m))^3*W p m c k := by
  let w (k : ℕ) : ℤ_[p] := ∏ j ∈ Finset.range k, (1-(ratio p c j)^2)
  have hw (k : ℕ) (hk : k≤n) : ((w k:ℤ_[p]):ℚ_[p])=BalaWeighted.weight ℚ_[p] (2*n+1) k := by
    change PadicInt.Coe.ringHom (w k)=_
    simp only [w,BalaWeighted.weight,map_prod,map_sub,map_one,map_pow,hd]
    apply Finset.prod_congr rfl
    intro j hj
    change 1-((ratio p c j:ℤ_[p]):ℚ_[p])^2=_
    rw [coe_ratio p c j (by have h := Finset.mem_range.mp hj; omega)]
  have hh : (BalaWeighted.sum n:ℤ_[p])=∑ k ∈ Finset.range (n+1), (Nat.centralBinom k:ℤ_[p])^3*w k := by
    apply Subtype.ext
    change PadicInt.Coe.ringHom (BalaWeighted.sum n:ℤ_[p])=PadicInt.Coe.ringHom _
    simp only [map_intCast,map_sum,map_mul,map_pow,map_natCast]
    rw [BalaWeighted.weighted_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change _ = _ * ((w k:ℤ_[p]):ℚ_[p])
    rw [hw k (by have := Finset.mem_range.mp hk; omega)]
  have hg (j : ℕ) : PadicInt.toZModPow m (ratio p c j)=rmod p m c j := by
    unfold ratio rmod unit; split_ifs <;> simp
  simpa only [w,W,map_intCast,map_sum,map_mul,map_pow,map_natCast,map_prod,map_sub,map_one,hg] using
    congrArg (PadicInt.toZModPow m) hh

omit [Fact p.Prime] in
theorem nil (m : ℕ) : (p:ZMod (p^m))^m=0 := by rw [← Nat.cast_pow,ZMod.natCast_self]

omit [Fact p.Prime] in
theorem lower_unit (a r : ℕ) (hr : 2*r+1 < p) : ¬p ∣ 2*(p*a+r)+1 := by
  rw [show 2*(p*a+r)+1=p*(2*a)+(2*r+1) by ring,Nat.dvd_add_right (dvd_mul_right p _)]
  exact Nat.not_dvd_of_pos_of_lt (by omega) hr

theorem short_W (c k : ℕ) (hc : c=1 ∨ c=3) (hk : 2*k≤p*c-1) (hp : 3<p)
    (odd : p%2=1) : W p 2 c k = if 2*k<p then 1 else 1-(c:ZMod (p^2))^2 := by
  induction k with
  | zero => simp [W,show 0<p by omega]
  | succ k ih =>
    rw [W_succ,ih (by omega)]
    by_cases mid : 2*k+1=p
    · rw [if_pos (by omega : 2*k<p),if_neg (by omega : ¬2*(k+1)<p)]
      have hu : unit p 2 1=1 := by simpa using unit_spec p 2 1 ((Fact.out : p.Prime).not_dvd_one)
      simp [rmod,mid,Nat.div_self (Fact.out : p.Prime).pos,hu]
    · have hnd : ¬p ∣ 2*k+1 := by
        rintro ⟨j,hj⟩
        have h3 : j<3 := by
          by_contra! he
          have hle := Nat.mul_le_mul_left p he
          rcases hc with rfl|rfl <;> omega
        interval_cases j <;> omega
      have ht : (rmod p 2 c k)^2=0 := by
        rw [rmod,if_neg hnd,mul_pow,mul_pow,nil,zero_mul,zero_mul]
      rw [ht,sub_zero,mul_one]
      have : 2*k<p ↔ 2*(k+1)<p := by omega
      simp only [this]

theorem long_step (a r : ℕ) (hr : 2*r+1 < p) :
    W p 4 p (p*a+r+1)=W p 4 p (p*a+r) := by
  rw [W_succ,rmod,if_neg (lower_unit p a r hr)]
  have he : ((p:ZMod (p^4))*p*unit p 4 (2*(p*a+r)+1))^2=0 := by
    linear_combination (unit p 4 (2*(p*a+r)+1))^2*nil p 4
  rw [he,sub_zero,mul_one]

theorem long_multiple (k : ℕ) : (p:ZMod (p^4))^2 ∣ W p 4 p k-1 := by
  induction k with
  | zero => simp [W]
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih
    have hr : (p:ZMod (p^4)) ∣ rmod p 4 p k := by
      unfold rmod; split_ifs <;> simp [mul_assoc]
    obtain ⟨u,hu⟩ := hr
    rw [W_succ,hu]
    use v-W p 4 p k*u^2
    linear_combination hv

end
end BalaWeightsMod

/- Lower half-block sums modulo p². -/
namespace BalaBlocks
noncomputable section
open BalaWeightsMod
variable (p : ℕ) [Fact p.Prime]

def block (p a l : ℕ) := ∑ r ∈ Finset.range l, (p*a+r).centralBinom^3

private def lin {R : Type*} [CommRing R] (z g h : R) := g+z*h
private theorem lin_mul {R : Type*} [CommRing R] {z : R} (hz : z^2=0) (a b c d : R) :
    lin z a b*lin z c d=lin z (a*c) (a*d+b*c) := by unfold lin; linear_combination b*d*hz

theorem affine_entry (r : ℕ) (hr : r<p) :
    ∃ g h : (ZMod (p^2)), ∀ a : ℕ, ((p*a+r).centralBinom:(ZMod (p^2)))=
      ((p*a).centralBinom:(ZMod (p^2)))*lin ((p:(ZMod (p^2)))*a) g h := by
  induction r with
  | zero => exact ⟨1,0,by simp [lin]⟩
  | succ r ih =>
    obtain ⟨g,h,ih⟩ := ih (by omega)
    let v := unit p 2 (r+1)
    let t : (ZMod (p^2)) := r+1
    let j : (ZMod (p^2)) := 2*r+1
    have tv : t*v=1 := by
      simpa only [t,v,Nat.cast_add,Nat.cast_one] using unit_spec p 2 (r+1)
        (Nat.not_dvd_of_pos_of_lt (by omega) hr)
    let s := (2*j)*v
    let u := (2*j)*(-v^2)+4*v
    refine ⟨g*s,g*u+h*s,?_⟩
    intro a
    let z : (ZMod (p^2)) := (p:(ZMod (p^2)))*a
    have hz : z^2=0 := by simp [z,mul_pow,nil p 2]
    have hi : lin z t 1*lin z v (-v^2)=1 := by
      rw [lin_mul hz]; unfold lin
      linear_combination (1-z*v)*tv
    have he : lin z t 1*((p*a+(r+1)).centralBinom:(ZMod (p^2)))=
        lin z (2*j) 4*((p*a+r).centralBinom:(ZMod (p^2))) := by
      have hh := congrArg (fun i : ℕ => (i:(ZMod (p^2)))) (Nat.succ_mul_centralBinom_succ (p*a+r))
      push_cast at hh
      unfold lin; dsimp [z,t,j]
      linear_combination hh
    change _=_*lin z _ _
    calc
      _ = (lin z t 1*((p*a+(r+1)).centralBinom:(ZMod (p^2))))*lin z v (-v^2) := by rw [mul_right_comm,hi,one_mul]
      _ = ((p*a).centralBinom:(ZMod (p^2)))*(lin z g h*(lin z (2*j) 4*lin z v (-v^2))) := by rw [he,ih]; ring
      _ = _ := by rw [lin_mul hz,lin_mul hz]

theorem affine_block (l : ℕ) (hl : l≤p) :
    ∃ g h : (ZMod (p^2)), ∀ a : ℕ, (block p a l:(ZMod (p^2)))=((p*a).centralBinom:(ZMod (p^2)))^3*lin ((p:(ZMod (p^2)))*a) g h := by
  induction l with
  | zero => exact ⟨0,0,by simp [block,lin]⟩
  | succ l ih =>
    obtain ⟨g,h,ih⟩ := ih (by omega)
    obtain ⟨b,c,he⟩ := affine_entry p l (by omega)
    refine ⟨g+b^3,h+3*b^2*c,?_⟩
    intro a
    let z : (ZMod (p^2)) := (p:(ZMod (p^2)))*a
    have hz : z^2=0 := by simp [z,mul_pow,nil p 2]
    have cub : (lin z b c)^3=lin z (b^3) (3*b^2*c) := by
      rw [pow_succ (lin z b c) 2,pow_two (lin z b c),lin_mul hz,lin_mul hz]; unfold lin; ring
    rw [show block p a (l+1)=block p a l+(p*a+l).centralBinom^3 from Finset.sum_range_succ ..,
      Nat.cast_add,Nat.cast_pow,ih,he,mul_pow]
    change _ + _*(lin z b c)^3=_
    rw [cub]; unfold lin; dsimp [z]; ring

theorem carry_zero {a r : ℕ} (hr : r<p) (hc : p≤2*r) :
    ((p*a+r).centralBinom:(ZMod (p^2)))^3=0 := by
  have h := BalaAudit.upper_half_carry p (p*a+r) (by simpa [Nat.mod_eq_of_lt hr] using hc)
  obtain ⟨z,hz⟩ := h
  change (((2*(p*a+r)).choose (p*a+r):ℕ):(ZMod (p^2)))^3=0
  rw [hz,Nat.cast_mul,mul_pow,show (p:(ZMod (p^2)))^3=(p:(ZMod (p^2)))^2*p by ring,nil p 2,zero_mul,zero_mul]

/-- The two short elliptic congruences isolate the first and second lower half-block. -/
theorem first_two (elig : OeisA3625.A p) (hp : 3<p) :
    (block p 0 (p/2+1):(ZMod (p^2)))=0 ∧ (block p 1 (p/2+1):(ZMod (p^2)))=0 := by
  let h := p/2
  have odd := (Nat.Prime.mod_two_eq_one_iff_ne_two elig.1).mpr (by omega)
  have ph : 2*h+1=p := by dsimp [h]; omega
  have zero (n c : ℕ) (hc : c=1 ∨ c=3) (e : 2*n+1=p*c) :
      (∑ k ∈ Finset.range (n+1), (k.centralBinom:(ZMod (p^2)))^3*
        (if 2*k<p then 1 else 1-(c:(ZMod (p^2)))^2))=0 := by
    have hdiv := (BalaWeighted.eligible p elig).2 n (by rw [e]; exact dvd_mul_right _ _)
    have hz : (BalaWeighted.sum n:(ZMod (p^2)))=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdiv)
    rw [sum_mod p 2 c n e (by rcases hc with rfl|rfl <;> nlinarith)] at hz
    convert hz using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [short_W p c k hc (by have := Finset.mem_range.mp hk; omega) hp odd]
  have z0 := zero h 1 (Or.inl rfl) (by omega)
  have z1 := zero (p+h) 3 (Or.inr rfl) (by omega)
  have e0 (k : ℕ) (hk : k∈Finset.range (h+1)) : 2*k<p := by have := Finset.mem_range.mp hk; omega
  have h0 : ∑ k ∈ Finset.range (h+1), (k.centralBinom:(ZMod (p^2)))^3=0 := by
    convert z0 using 1
    exact Finset.sum_congr rfl fun k hk => by rw [if_pos (e0 k hk),mul_one]
  have first : (block p 0 (h+1):(ZMod (p^2)))=0 := by simpa [block] using h0
  refine ⟨first,?_⟩
  let T (k : ℕ) : (ZMod (p^2)) := (k.centralBinom:(ZMod (p^2)))^3*(if 2*k<p then 1 else 1-(3:(ZMod (p^2)))^2)
  change ∑ k ∈ Finset.range (p+h+1), T k=0 at z1
  rw [Nat.add_assoc,Finset.sum_range_add] at z1
  have pref : ∑ k ∈ Finset.range p,T k=0 := by
    have eq : h+1+(p-(h+1))=p := by omega
    rw [show Finset.range p=Finset.range (h+1+(p-(h+1))) from congrArg Finset.range eq.symm,Finset.sum_range_add]
    have sm : ∑ k ∈ Finset.range (h+1),T k=0 := by
      convert h0 using 1
      exact Finset.sum_congr rfl fun k hk => by simp [T,e0 k hk]
    rw [sm,zero_add]
    apply Finset.sum_eq_zero
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have he := carry_zero p (a:=0) (r:=h+1+r) (by omega) (by omega)
    simpa [T] using mul_eq_zero_of_left (by simpa using he : ((h+1+r).centralBinom:(ZMod (p^2)))^3=0)
      (if 2*(h+1+r)<p then (1:(ZMod (p^2))) else 1-(3:(ZMod (p^2)))^2)
  rw [pref,zero_add] at z1
  have hsecond : (block p 1 (h+1):(ZMod (p^2)))*(-8)=0 := by
    convert z1 using 1
    simp only [block,Nat.mul_one,Nat.cast_sum,Nat.cast_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp [T,show ¬2*(p+k)<p by omega]; ring
  have hu : IsUnit (8:(ZMod (p^2))) := by
    have htwo : IsUnit (2:(ZMod (p^2))) := (ZMod.isUnit_natCast_iff_not_dvd_pow elig.1 (by decide : 0<2)).mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p))
    convert htwo.pow 3 using 1; ring
  exact (hu.neg.mul_left_inj).mp (by simpa using hsecond)

theorem lower (elig : OeisA3625.A p) (hp : 3<p) (a : ℕ) : p^2 ∣ block p a (p/2+1) := by
  obtain ⟨h0,h1⟩ := first_two p elig hp
  obtain ⟨g,h,hg⟩ := affine_block p (p/2+1) (by omega)
  rw [hg] at h0 h1
  simp [lin] at h0
  have luc := Choose.choose_mul_mul_modEq_choose_nat (p:=p) (a:=2) (b:=1)
  have hcp : ¬p ∣ p.centralBinom := by
    intro hd
    change p ∣ (2*p).choose p at hd
    simp only [Nat.mul_one,mul_comm p 2,show (2:ℕ).choose 1=2 by decide] at luc
    have he := luc.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) (Nat.modEq_zero_iff_dvd.mp he)
  have hu := ((ZMod.isUnit_natCast_iff_not_dvd_pow elig.1 (by decide : 0<2)).mpr hcp).pow 3
  simp only [Nat.cast_one,lin,h0,zero_add,mul_one] at h1
  have hv : (p:(ZMod (p^2)))*h=0 := (hu.mul_right_inj).mp (by simpa using h1)
  apply (ZMod.natCast_eq_zero_iff ..).mp
  rw [hg]; simp [lin,h0,mul_right_comm (p:(ZMod (p^2))) (a:(ZMod (p^2))) h,hv]

end
end BalaBlocks

/- Bala’s third conjecture on cubed central binomial coefficients. -/
namespace BalaThird
noncomputable section

theorem comparison (p : ℕ) (elig : OeisA3625.A p) (hp : 3<p) :
    (BalaWeighted.sum ((p^2-1)/2):ZMod (p^4))=(OeisA79727.a ((p^2-1)/2):ZMod (p^4)) := by
  let _ : Fact p.Prime := ⟨elig.1⟩
  let h := p/2
  let N := (p^2-1)/2
  let W := BalaWeightsMod.W p 4 p
  let T (k : ℕ) : ZMod (p^4) := (k.centralBinom:ZMod (p^4))^3*(W k-1)
  have odd := (Nat.Prime.mod_two_eq_one_iff_ne_two elig.1).mpr (by omega)
  have ph : p=2*h+1 := by dsimp [h]; omega
  have p2 : p^2=2*(p*h+h)+1 := by
    conv_lhs => rw [ph]
    conv_rhs => rw [ph]
    ring
  have en : N=p*h+h := by dsimp [N]; omega
  have same (a r : ℕ) (hr : r≤h) : W (p*a+r)=W (p*a) := by
    induction r with
    | zero => simp
    | succ r ih => exact (BalaWeightsMod.long_step p a r (by omega)).trans (ih (by omega))
  have lower (a : ℕ) : ∑ r ∈ Finset.range (h+1), T (p*a+r)=0 := by
    have hh : ∑ r ∈ Finset.range (h+1), T (p*a+r)=
        (BalaBlocks.block p a (h+1):ZMod (p^4))*(W (p*a)-1) := by
      simp only [BalaBlocks.block,Nat.cast_sum,Nat.cast_pow,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only [T]
      rw [same a r (by have := Finset.mem_range.mp hr; omega)]
    rw [hh]
    obtain ⟨d,hd⟩ := BalaBlocks.lower p elig hp a
    obtain ⟨v,hv⟩ := BalaWeightsMod.long_multiple p (p*a)
    change W (p*a)-1=(p:ZMod (p^4))^2*v at hv
    rw [hd,hv,Nat.cast_mul,Nat.cast_pow]
    linear_combination (d:ZMod (p^4))*v*BalaWeightsMod.nil p 4
  have upper (a r : ℕ) (hr : r<p) (hh : h<r) : T (p*a+r)=0 := by
    have hc := BalaAudit.upper_half_carry p (p*a+r) (by
      simpa [Nat.mod_eq_of_lt hr] using (show p≤2*r by omega))
    obtain ⟨z,hz⟩ := hc
    change (p*a+r).centralBinom=p*z at hz
    obtain ⟨v,hv⟩ := BalaWeightsMod.long_multiple p (p*a+r)
    change W (p*a+r)-1=(p:ZMod (p^4))^2*v at hv
    dsimp only [T]
    rw [hz,Nat.cast_mul,hv]
    linear_combination (p:ZMod (p^4))*(z:ZMod (p^4))^3*v*BalaWeightsMod.nil p 4
  have full (a : ℕ) : ∑ r ∈ Finset.range p,T (p*a+r)=0 := by
    rw [show Finset.range p=Finset.range ((h+1)+(p-(h+1))) from congrArg Finset.range (by omega)]
    rw [Finset.sum_range_add,lower,zero_add]
    apply Finset.sum_eq_zero
    intro r hr
    have := Finset.mem_range.mp hr
    exact upper a (h+1+r) (by omega) (by omega)
  have prefixSum (a : ℕ) : ∑ k ∈ Finset.range (p*a),T k=0 := by
    induction a with
    | zero => simp
    | succ a ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,zero_add,full]
  have ht : ∑ k ∈ Finset.range (N+1), T k=0 := by
    rw [en,Nat.add_assoc,Finset.sum_range_add,prefixSum,zero_add,lower]
  change (BalaWeighted.sum N:ZMod (p^4))=(OeisA79727.a N:ZMod (p^4))
  rw [BalaWeightsMod.sum_mod p 4 p N (by rw [en,← p2,pow_two]) (by rw [en,← p2])]
  simp only [OeisA79727.a,Nat.cast_sum,Nat.cast_pow,← Nat.centralBinom_eq_two_mul_choose]
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  convert ht using 1
  apply Finset.sum_congr rfl
  intro k _
  unfold T W
  ring

/-- The statement uses the sequence and prime predicate from Formal Conjectures. -/
theorem conjecture3 (p : ℕ) (hp : OeisA3625.A p) :
    OeisA79727.a ((p^2-1)/2) ≡ p^2 [MOD p^4] := by
  by_cases small : p=3
  · subst p; exact BalaAudit.small_cases.1
  have big : 3<p := by
    have h2 := hp.1.two_le
    have hn : p≠2 := by rintro rfl; norm_num [OeisA3625.A] at hp
    omega
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  rw [← comparison p hp big,Nat.cast_pow]
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^4)).mpr
    (by simpa using (BalaWeighted.eligible p hp).1 :
      ((p^4:ℕ):ℤ) ∣ BalaWeighted.sum ((p^2-1)/2)-(p:ℤ)^2)
  push_cast at h
  exact sub_eq_zero.mp h

end
end BalaThird

theorem OMA.solution : type_of% @OeisA79727.conjecture3 := by
  exact BalaThird.conjecture3
