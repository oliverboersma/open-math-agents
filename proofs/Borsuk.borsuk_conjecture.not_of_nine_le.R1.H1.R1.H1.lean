import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1
import Mathlib

/-! Explicit coordinates for the trace-free rank-one projector, as in the
nine-dimensional Borsuk construction of OpenAI. The three diagonal coordinates
are the nonconstant rows of the order-four Hadamard matrix, divided by two. -/
open Real Finset
open scoped RealInnerProductSpace
namespace BorsukProjector
/-- Three orthonormal trace-free diagonal coordinates, followed by the six
off-diagonal coordinates of the symmetric rank-one projector. -/
private noncomputable def projector (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 9) :=
  !₂[(x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2)/2,
     (x 0 ^ 2 - x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2)/2,
     (x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 + x 3 ^ 2)/2,
     sqrt 2 * (x 0*x 1), sqrt 2 * (x 0*x 2), sqrt 2 * (x 0*x 3),
     sqrt 2 * (x 1*x 2), sqrt 2 * (x 1*x 3), sqrt 2 * (x 2*x 3)]

private lemma projector_inner (x y : EuclideanSpace ℝ (Fin 4)) :
    ⟪projector x,projector y⟫ = ⟪x,y⟫^2 - ‖x‖^2*‖y‖^2/4 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp [projector,PiLp.inner_apply,Fin.sum_univ_succ,Real.inner_apply]
  ring_nf
  norm_num

private lemma sphere_norm {x : EuclideanSpace ℝ (Fin 4)} (hx : ‖x‖=1) :
    ‖projector x‖^2 = 3/4 := by
  have h := projector_inner x x
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hx] at h
  norm_num at h ⊢
  exact h

theorem exists_projector : ∃ f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 9),
    (∀ x, ‖x‖=1 → ‖f x‖^2=3/4) ∧ ∀ x y, ‖x‖=1 → ‖y‖=1 →
    dist (f x) (f y)^2 = 2*(1-⟪x,y⟫^2) := by
  refine ⟨projector,fun _ h => sphere_norm h,?_⟩
  intro x y hx hy
  rw [dist_eq_norm,norm_sub_sq_real,sphere_norm hx,sphere_norm hy,projector_inner,hx,hy]
  ring
end BorsukProjector

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1.H1 :=
  BorsukProjector.exists_projector
