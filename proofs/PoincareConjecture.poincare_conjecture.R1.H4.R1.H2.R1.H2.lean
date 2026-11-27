import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1
import Mathlib

/-! The inverse function theorem in boundaryless manifold charts. -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace ManifoldInverse

private theorem local_inverse {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B]
    {f : A → B} (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (x : A)
    (hd : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x)) :
    ∃ e : OpenPartialHomeomorph A B, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm (f x) := by
  let a := chartAt (EuclideanSpace ℝ (Fin 3)) x
  let b := chartAt (EuclideanSpace ℝ (Fin 3)) (f x)
  let g := b ∘ f ∘ a.symm
  have hax : x ∈ a.source := mem_chart_source _ _
  have hbx : f x ∈ b.source := mem_chart_source _ _
  have hgx : g (a x) = b (f x) := by simp [g, a.left_inv hax]
  have hgd : ContDiffAt ℝ ∞ g (a x) := by
    have h := (contMDiffAt_iff.mp (hf x)).2
    simpa [g, a, b, extChartAt_coe, extChartAt_coe_symm, contDiffWithinAt_univ] using h
  have hf' := (hgd.differentiableAt (by simp)).hasFDerivAt
  have hfM : HasMFDerivAt (𝓡 3) (𝓡 3) f x (fderiv ℝ g (a x)) := by
    refine ⟨(hf x).continuousAt, ?_⟩
    have hrange : Set.range (𝓡 3) = Set.univ := by simp
    rw [hrange]
    change HasFDerivWithinAt g (fderiv ℝ g (a x)) univ (a x)
    exact hf'.hasFDerivWithinAt
  rw [hfM.mfderiv] at hd
  let L := (LinearEquiv.ofBijective (fderiv ℝ g (a x)).toLinearMap hd).toContinuousLinearEquiv
  have hL : HasFDerivAt g (L : _ →L[ℝ] _) (a x) :=
    hf'
  let p := hgd.toOpenPartialHomeomorph g hL (by simp)
  have hpx : a x ∈ p.source := hgd.mem_toOpenPartialHomeomorph_source hL _
  have hpx' : p (a x) = b (f x) := hgx
  let e₀ := a.trans (p.trans b.symm)
  let e := e₀.restrOpen (f ⁻¹' b.source) (b.open_source.preimage hf.continuous)
  have hex : x ∈ e.source := by
    simp [e, e₀, hax, hpx, hpx', hbx, b.map_source hbx]
  have heq : EqOn f e e.source := by
    intro y hy
    have hys : y ∈ a.source := hy.1.1
    have hby : f y ∈ b.source := hy.2
    change f y = b.symm (g (a y))
    rw [show g (a y) = b (f y) by simp [g, a.left_inv hys], b.left_inv hby]
  have hba : ContMDiffAt (𝓡 3) (𝓡 3) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓡 3) (n := ∞) (x := f x)).contMDiffAt (b.open_source.mem_nhds hbx)
  have hpa : ContMDiffAt (𝓡 3) (𝓡 3) ∞ p.symm (b (f x)) := by
    rw [← hgx]
    exact (hgd.to_localInverse hL (by simp)).contMDiffAt
  have hpa' : p.symm (b (f x)) = a x := by rw [← hpx']; exact p.left_inv hpx
  have hat : a x ∈ a.target := a.map_source hax
  have haa : ContMDiffAt (𝓡 3) (𝓡 3) ∞ a.symm (p.symm (b (f x))) := by
    rw [hpa']
    exact (contMDiffOn_chart_symm (I := 𝓡 3) (n := ∞) (x := x)).contMDiffAt (a.open_target.mem_nhds hat)
  refine ⟨e, hex, heq, ?_⟩
  change ContMDiffAt (𝓡 3) (𝓡 3) ∞ (a.symm ∘ p.symm ∘ b) (f x)
  exact haa.comp (f x) (hpa.comp (f x) hba)

theorem local_diffeomorph (A B : Type) [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B] (f : A → B)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hd : ∀ x, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := by
  intro x
  obtain ⟨e, hex, heq, _⟩ := local_inverse hf x (hd x)
  have hforward : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := hf.contMDiffOn.congr heq.symm
  have hinverse : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    intro y hy
    have hyx : e.symm y ∈ e.source := e.map_target hy
    have heval : f (e.symm y) = y := (heq hyx).trans (e.right_inv hy)
    obtain ⟨e', hx', heq', hsmooth⟩ := local_inverse hf (e.symm y) (hd (e.symm y))
    rw [heval] at hsmooth
    have hev : ∀ᶠ w in 𝓝 y, w ∈ e.target ∧ e.symm w ∈ e'.source :=
      (show ∀ᶠ w in 𝓝 y, w ∈ e.target from e.open_target.mem_nhds hy).and
        ((e.continuousAt_symm hy) (e'.open_source.mem_nhds hx'))
    have hequiv : (e.symm : B → A) =ᶠ[𝓝 y] e'.symm := hev.mono fun w hw => by
      have h₁ : e' (e.symm w) = w :=
        (heq' hw.2).symm.trans ((heq (e.map_target hw.1)).trans (e.right_inv hw.1))
      change e.symm w = e'.symm w
      calc
        _ = e'.symm (e' (e.symm w)) := (e'.left_inv hw.2).symm
        _ = _ := congrArg e'.symm h₁
    exact (hsmooth.congr_of_eventuallyEq hequiv).contMDiffWithinAt
  exact ⟨⟨e.toPartialEquiv, e.open_source, e.open_target, hforward, hinverse⟩, hex, heq⟩

end ManifoldInverse

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1.H2 :=
  ManifoldInverse.local_diffeomorph