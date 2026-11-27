import FormalConjectures.Paper.DeGiorgi

/-!
# The derivative quotients in the 3D De Giorgi theorem

The three analytic inputs are the quadratic energy growth bound on balls
for monotone bounded solutions, the weak divergence-form equation for each
derivative quotient, and the 3D weighted Liouville theorem. The remaining
argument proves the affine hyperplane structure of each level set directly
from constant derivative quotients.

See Ambrosio and Cabré (2000), https://doi.org/10.1090/S0894-0347-00-00345-3.
-/

namespace OMA.R_DeGiorgi_DeGiorgi_three_R1

open EuclideanGeometry InnerProductSpace MeasureTheory Set

private theorem hyperplanes_of_constant_quotient (u : ℝ^3 → ℝ)
    (hu : Differentiable ℝ u)
    (hv : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single 0 1))
    (c1 c2 : ℝ)
    (hw1 : ∀ x, fderiv ℝ u x (EuclideanSpace.single 1 1) =
      c1 * fderiv ℝ u x (EuclideanSpace.single 0 1))
    (hw2 : ∀ x, fderiv ℝ u x (EuclideanSpace.single 2 1) =
      c2 * fderiv ℝ u x (EuclideanSpace.single 0 1)) :
    DeGiorgi.HasHyperplaneLevelSets u := by
  let e0 : ℝ^3 := EuclideanSpace.single 0 1
  let e1 : ℝ^3 := EuclideanSpace.single 1 1
  let e2 : ℝ^3 := EuclideanSpace.single 2 1
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L : ℝ^3 →ₗ[ℝ] ℝ := b.coord 0 + c1 • b.coord 1 + c2 • b.coord 2
  have hL (d : ℝ^3) : L d = d 0 + c1 * d 1 + c2 * d 2 := by
    simp [L, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hL0 : L e0 = 1 := by simp [hL, e0]
  have hbasis (d : ℝ^3) : d = d 0 • e0 + d 1 • e1 + d 2 • e2 := by
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  have hgradient (x d : ℝ^3) :
      fderiv ℝ u x d = fderiv ℝ u x e0 * L d := by
    conv_lhs => rw [hbasis d]
    rw [map_add, map_add, map_smul, map_smul, map_smul, hL]
    change d 0 * fderiv ℝ u x e0 + d 1 * fderiv ℝ u x e1 + d 2 * fderiv ℝ u x e2 =
      fderiv ℝ u x e0 * (d 0 + c1 * d 1 + c2 * d 2)
    rw [show fderiv ℝ u x e1 = c1 * fderiv ℝ u x e0 from hw1 x,
        show fderiv ℝ u x e2 = c2 * fderiv ℝ u x e0 from hw2 x]
    ring
  have hline (x d : ℝ^3) (t : ℝ) :
      HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t := by
    exact (hu _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))
  have hsame (x z : ℝ^3) (h : L x = L z) : u x = u z := by
    have hd : L (z - x) = 0 := by rw [map_sub, h, sub_self]
    have hconst (t : ℝ) : deriv (fun s : ℝ => u (x + s • (z - x))) t = 0 := by
      rw [(hline x (z - x) t).deriv, hgradient, hd, mul_zero]
    have h01 := is_const_of_deriv_eq_zero
      (fun t => (hline x (z - x) t).differentiableAt) hconst 0 1
    simpa [add_comm] using h01
  have hdifferent (x z : ℝ^3) (h : u x = u z) : L x = L z := by
    let t := L x - L z
    have hLz : L (z + t • e0) = L x := by
      rw [map_add, map_smul, hL0]
      simp [t]
    have hu0 : u (z + t • e0) = u z := (hsame _ _ hLz).trans h
    have hinj : Function.Injective (fun s : ℝ => u (z + s • e0)) := by
      apply StrictMono.injective
      apply strictMono_of_deriv_pos
      intro s
      rw [(hline z e0 s).deriv]
      exact hv _
    have ht : t = 0 := hinj (by simpa using hu0)
    exact sub_eq_zero.mp ht
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨AffineSubspace.mk' x L.ker, ?_, ?_⟩
  · ext z
    change u z = u x ↔ z ∈ AffineSubspace.mk' x L.ker
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ⟨hdifferent z x, hsame z x⟩
  · have hsurj : Function.Surjective L := fun r => ⟨r • e0, by simp [hL0]⟩
    have hdim := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace_fin] at hdim
    simp only [Module.finrank_self] at hdim
    rw [AffineSubspace.direction_mk']
    omega

/-- Quadratic energy growth bound on balls of radius R for partial derivatives
of monotone bounded solutions in dimension 3. -/
def H1 : Prop :=
  ∀ (u : ℝ^3 → ℝ) (i : Fin 3),
    DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤ C * R ^ 2

/-- The weak divergence-form equation for each derivative quotient, tested against
compactly supported functions. -/
def H2 : Prop :=
  ∀ (u : ℝ^3 → ℝ) (i : Fin 3),
    DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    let v := fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)
    let w := fun x => fderiv ℝ u x (EuclideanSpace.single i 1)
    let q := fun x => w x / v x
    ∀ η : ℝ^3 → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0

/-- The 3D weighted Liouville theorem of Ambrosio and Cabré: if v > 0 and v * q
has O(R^2) L^2-energy growth on balls of radius R, any weak solution to
div(v^2 grad q) = 0 on R^3 is constant. -/
def H3 : Prop :=
  ∀ (v q : ℝ^3 → ℝ),
    ContDiff ℝ 1 v → ContDiff ℝ 1 q → (∀ x, 0 < v x) →
    (∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q x) ^ 2) ≤ C * R ^ 2) →
    (∀ η : ℝ^3 → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0) →
    ∃ c : ℝ, ∀ x, q x = c

theorem main : H1 → H2 → H3 → type_of% @DeGiorgi.DeGiorgi_three := by
  intro hbound hequation hliouville u ⟨hu, hup⟩
  let v := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 0 1)
  let w1 := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 1 1)
  let w2 := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 2 1)
  let q1 := fun x : ℝ^3 => w1 x / v x
  let q2 := fun x : ℝ^3 => w2 x / v x
  have hud : Differentiable ℝ u := hu.regular.differentiable (by norm_num)
  have hv : ∀ x, 0 < v x := by
    intro x
    simpa only [(hud x).lineDeriv_eq_fderiv] using hup x
  have hder : ContDiff ℝ 1 (fderiv ℝ u) := hu.regular.fderiv_right (by norm_num)
  have hvC : ContDiff ℝ 1 v := hder.clm_apply contDiff_const
  have hw1C : ContDiff ℝ 1 w1 := hder.clm_apply contDiff_const
  have hw2C : ContDiff ℝ 1 w2 := hder.clm_apply contDiff_const
  have hq1C : ContDiff ℝ 1 q1 := hw1C.div hvC fun x => (hv x).ne'
  have hq2C : ContDiff ℝ 1 q2 := hw2C.div hvC fun x => (hv x).ne'
  have hmul1 (x : ℝ^3) : v x * q1 x = w1 x := by
    dsimp [q1]
    field_simp [(hv x).ne']
  have hmul2 (x : ℝ^3) : v x * q2 x = w2 x := by
    dsimp [q2]
    field_simp [(hv x).ne']
  obtain ⟨C1, hC1⟩ := hbound u 1 hu hup
  obtain ⟨C2, hC2⟩ := hbound u 2 hu hup
  have hbounded1 : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q1 x) ^ 2) ≤ C * R ^ 2 := by
    refine ⟨C1, fun R hR => ?_⟩
    simp only [hmul1]
    exact hC1 R hR
  have hbounded2 : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q2 x) ^ 2) ≤ C * R ^ 2 := by
    refine ⟨C2, fun R hR => ?_⟩
    simp only [hmul2]
    exact hC2 R hR
  obtain ⟨c1, hc1⟩ := hliouville v q1 hvC hq1C hv hbounded1 (hequation u 1 hu hup)
  obtain ⟨c2, hc2⟩ := hliouville v q2 hvC hq2C hv hbounded2 (hequation u 2 hu hup)
  refine hyperplanes_of_constant_quotient u hud hv c1 c2
    (fun x => (div_eq_iff (hv x).ne').mp (hc1 x))
    (fun x => (div_eq_iff (hv x).ne').mp (hc2 x))

end OMA.R_DeGiorgi_DeGiorgi_three_R1
