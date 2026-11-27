import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1
import Mathlib

/-!
An orbit-separating even map would realize the real tautological line on a
compact subset of three-space. For its complexification, a nonzero section
would give a nowhere-zero odd complex function on the sphere by pairing
the section with its real unit representative.

The first input is the line-bundle consequence of Alexander duality:
degree-two integral Čech cohomology of a compact subset of R³ is
torsion-free, and the complexification of a real line has tensor square
trivial. The second input is the planar Borsuk–Ulam obstruction.
-/
namespace OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1

/-- A real rank-one orthogonal projection over a compact subset of three-space
has a nowhere-zero continuous section after complexification. -/
def H1 : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsCompact K →
  ∀ P : K → Fin 3 → Fin 3 → ℝ, Continuous P →
  (∀ k, ∃ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ i j, P k i j = x.val i * x.val j) →
  ∃ s : K → Fin 3 → ℂ, Continuous s ∧ ∀ k, s k ≠ 0 ∧
    ∀ i, ∑ j, (P k i j : ℂ) * s k j = s k i

/-- An odd continuous complex function on the two-sphere has a zero. -/
def H2 : Prop :=
  ∀ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ, Continuous f →
    (∀ x y, x.val = -y.val → f x = -f y) → ∃ x, f x=0

theorem main : H1 → H2 → OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1.H2 := by
  classical
  intro hsphere hzero g hg heven
  by_contra hn
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let K := Set.range g
  let q : S → K := Set.rangeFactorization g
  have hq : Continuous q := hg.subtype_mk _
  have hsur : Function.Surjective q := Set.rangeFactorization_surjective
  have hcompact : IsCompact K := isCompact_range hg
  have hsep (x y : S) (h : g x=g y) : x=y ∨ x.val = -y.val := by
    by_cases hxy : x=y
    · exact Or.inl hxy
    · exact Or.inr (by by_contra h'; exact hn ⟨x,y,h,hxy,h'⟩)
  let rep (k : K) : S := k.property.choose
  have hrep (k : K) : g (rep k)=k.val := k.property.choose_spec
  let P (k : K) (i j : Fin 3) := (rep k).val i * (rep k).val j
  have hP (x : S) (i j : Fin 3) : P (q x) i j = x.val i * x.val j := by
    rcases hsep (rep (q x)) x (hrep _) with h|h
    · simp [P,h]
    · simp [P,h]
  have hPc : Continuous P := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hsur hq).continuous_iff.mpr
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x : S => P (q x) i j)
    simp only [hP]
    fun_prop
  obtain ⟨s,hsc,hs⟩ := hsphere K hcompact P hPc (fun k => ⟨rep k,fun _ _ => rfl⟩)
  let f (x : S) : ℂ := ∑ j, (x.val j : ℂ) * s (q x) j
  have hfc : Continuous f := by unfold f; fun_prop
  have hfodd (x y : S) (h : x.val = -y.val) : f x = -f y := by
    have hqxy : q x=q y := Subtype.ext (heven x y h)
    simp [f,hqxy,h,Finset.sum_neg_distrib]
  obtain ⟨x,hx⟩ := hzero f hfc hfodd
  apply (hs (q x)).1
  ext i
  change s (q x) i = 0
  calc
    s (q x) i = ∑ j, (P (q x) i j : ℂ)*s (q x) j := ((hs _).2 i).symm
    _ = (x.val i : ℂ)*f x := by
      unfold f
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hP,Complex.ofReal_mul,mul_assoc]
    _ = 0 := by rw [hx,mul_zero]

end OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1
