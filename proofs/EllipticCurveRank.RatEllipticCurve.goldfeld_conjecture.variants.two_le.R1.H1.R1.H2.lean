import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1
import Mathlib

/-!
Square multiples of twist parameters give isomorphic rational point groups.
For a short Weierstrass curve, scaling coordinates by (u^2,u^3) scales the
coefficients by (u^4,u^6). The construction below checks nonsingularity,
the tangent and secant formulas, and bijectivity of the resulting group map.
Credit: @rgoldman73-dev. Thanks to @MakisChristou for the coordinate-check note.
-/

namespace OMA.TwistScaling
open WeierstrassCurve WeierstrassCurve.Affine

private def shortCurve (A B : ℚ) : Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }

private lemma scale_nonsingular_iff {A B u x y : ℚ} (hu : u ≠ 0) :
    (shortCurve (u ^ 4 * A) (u ^ 6 * B)).Nonsingular (u ^ 2 * x) (u ^ 3 * y) ↔
      (shortCurve A B).Nonsingular x y := by
  simp only [nonsingular_iff', equation_iff, shortCurve, zero_mul, mul_zero,
    add_zero, zero_sub]
  have heq : (u ^ 3 * y) ^ 2 = (u ^ 2 * x) ^ 3 + u ^ 4 * A * (u ^ 2 * x) + u ^ 6 * B ↔
      y ^ 2 = x ^ 3 + A * x + B := by
    calc
      _ ↔ u ^ 6 * y ^ 2 = u ^ 6 * (x ^ 3 + A * x + B) := by ring_nf
      _ ↔ _ := mul_right_inj' (pow_ne_zero 6 hu)
  rw [heq]
  have hx : -(3 * (u ^ 2 * x) ^ 2 + u ^ 4 * A) = u ^ 4 * (-(3 * x ^ 2 + A)) := by ring
  have hy : 2 * (u ^ 3 * y) = u ^ 3 * (2 * y) := by ring
  rw [hx, hy]
  simp [pow_ne_zero _ hu]

private lemma scale_slope {A B u : ℚ} (hu : u ≠ 0) (x₁ x₂ y₁ y₂ : ℚ) :
    (shortCurve (u ^ 4 * A) (u ^ 6 * B)).slope (u ^ 2 * x₁) (u ^ 2 * x₂)
        (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (shortCurve A B).slope x₁ x₂ y₁ y₂ := by
  simp only [Affine.slope, negY, shortCurve, zero_mul, mul_zero, add_zero, sub_zero]
  have hy : u ^ 3 * y₁ = -(u ^ 3 * y₂) ↔ y₁ = -y₂ := by
    rw [← mul_neg, mul_right_inj' (pow_ne_zero 3 hu)]
  simp only [mul_right_inj' (pow_ne_zero 2 hu), hy]
  split_ifs
  · simp
  · calc
      _ = (u ^ 3 * (u * (3 * x₁ ^ 2 + A))) / (u ^ 3 * (y₁ - -y₁)) := by
        congr 1 <;> ring
      _ = _ := by rw [mul_div_mul_left _ _ (pow_ne_zero 3 hu), mul_div_assoc]
  · calc
      _ = (u ^ 2 * (u * (y₁ - y₂))) / (u ^ 2 * (x₁ - x₂)) := by
        congr 1 <;> ring
      _ = _ := by rw [mul_div_mul_left _ _ (pow_ne_zero 2 hu), mul_div_assoc]

private def scalePoint (A B u : ℚ) (hu : u ≠ 0) :
    (shortCurve A B).Point → (shortCurve (u ^ 4 * A) (u ^ 6 * B)).Point
  | .zero => .zero
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) ((scale_nonsingular_iff hu).mpr h)

private lemma scalePoint_add (A B u : ℚ) (hu : u ≠ 0)
    (P Q : (shortCurve A B).Point) :
    scalePoint A B u hu (P + Q) = scalePoint A B u hu P + scalePoint A B u hu Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      have hvertical :
          (u ^ 2 * x₁ = u ^ 2 * x₂ ∧
            u ^ 3 * y₁ = (shortCurve (u ^ 4 * A) (u ^ 6 * B)).negY (u ^ 2 * x₂) (u ^ 3 * y₂)) ↔
          (x₁ = x₂ ∧ y₁ = (shortCurve A B).negY x₂ y₂) := by
        simp only [negY, shortCurve, zero_mul, sub_zero, ← mul_neg,
          mul_right_inj' (pow_ne_zero 2 hu), mul_right_inj' (pow_ne_zero 3 hu)]
      by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A B).negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        change 0 = Point.some _ _ _ + Point.some _ _ _
        rw [Point.add_of_Y_eq (hvertical.mpr hxy).1 (hvertical.mpr hxy).2]
      · have hxy' := mt hvertical.mp hxy
        rw [Point.add_some hxy]
        change Point.some _ _ _ = Point.some _ _ _ + Point.some _ _ _
        rw [Point.add_some hxy']
        simp only [Point.some.injEq]
        constructor
        · rw [scale_slope hu]
          simp only [addX, shortCurve]
          ring
        · rw [scale_slope hu]
          simp only [addY, negY, negAddY, addX, shortCurve]
          ring

private def scaleHom (A B u : ℚ) (hu : u ≠ 0) :
    (shortCurve A B).Point →+ (shortCurve (u ^ 4 * A) (u ^ 6 * B)).Point where
  toFun := scalePoint A B u hu
  map_zero' := rfl
  map_add' := scalePoint_add A B u hu

private lemma scalePoint_bijective (A B u : ℚ) (hu : u ≠ 0) :
    Function.Bijective (scalePoint A B u hu) := by
  constructor
  · intro P Q he
    cases P with
    | zero => cases Q <;> cases he; rfl
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => cases he
      | some x₂ y₂ h₂ =>
        have hh := Point.some.inj he
        simp only [Point.some.injEq]
        exact ⟨(mul_right_inj' (pow_ne_zero 2 hu)).mp hh.1,
          (mul_right_inj' (pow_ne_zero 3 hu)).mp hh.2⟩
  · intro Q
    cases Q with
    | zero => exact ⟨.zero, rfl⟩
    | some x y h =>
      have hx : u ^ 2 * (x / u ^ 2) = x := by field_simp
      have hy : u ^ 3 * (y / u ^ 3) = y := by field_simp
      have hn : (shortCurve A B).Nonsingular (x / u ^ 2) (y / u ^ 3) :=
        (scale_nonsingular_iff hu).mp (by simpa only [hx, hy] using h)
      refine ⟨.some _ _ hn, ?_⟩
      simpa only [scalePoint, Point.some.injEq] using And.intro hx hy

private noncomputable def scaleEquiv (A B u : ℚ) (hu : u ≠ 0) :
    (shortCurve A B).Point ≃+ (shortCurve (u ^ 4 * A) (u ^ 6 * B)).Point :=
  AddEquiv.ofBijective (scaleHom A B u hu) (scalePoint_bijective A B u hu)

end OMA.TwistScaling

open OMA.TwistScaling in
theorem OMA.solution : OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1.H2 := by
  intro E a b _ha hb
  have hu : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hbase : E.quadraticTwist (a : ℤ) =
      shortCurve ((a : ℚ) ^ 2 * E.A) ((a : ℚ) ^ 3 * E.B) := by
    ext <;> simp [EllipticCurveRank.RatEllipticCurve.quadraticTwist, shortCurve]
  have hscaled : E.quadraticTwist ((b ^ 2 * a : ℕ) : ℤ) =
      shortCurve ((b : ℚ) ^ 4 * ((a : ℚ) ^ 2 * E.A))
        ((b : ℚ) ^ 6 * ((a : ℚ) ^ 3 * E.B)) := by
    ext <;> simp [EllipticCurveRank.RatEllipticCurve.quadraticTwist, shortCurve] <;> ring
  rw [hscaled, hbase]
  exact ⟨(scaleEquiv _ _ _ hu).symm⟩
