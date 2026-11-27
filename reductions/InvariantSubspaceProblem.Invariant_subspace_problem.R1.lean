import FormalConjectures.Wikipedia.InvariantSubspaceProblem
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Denumerable

/-!
An infinite-dimensional separable complex Hilbert space is isometric to
the square-summable complex sequences. On that space a noninjective
scalar shift gives an eigenline, and a shift with nondense range gives
a nontrivial closed invariant subspace.
-/

namespace OMA.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1

open scoped lp

def H1 : Prop :=
  ∀ (T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) (z : ℂ),
    (¬ Function.Injective (T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) ∨
      ¬ DenseRange (T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ))) →
    Nonempty (InvariantSubspaceProblem.ClosedInvariantSubspace T)

def H2 : Prop :=
  ∀ T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
    (∀ z : ℂ, Function.Injective (T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) ∧
      DenseRange (T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ))) →
    Nonempty (InvariantSubspaceProblem.ClosedInvariantSubspace T)

section Proof

open Function InvariantSubspaceProblem

private theorem sequence_model (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H]
    (hfinite : ¬ FiniteDimensional ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ)) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let B (i : w) : Set H := Metric.ball (b i) (1 / 2)
  have hSep : Pairwise (Disjoint on B) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := Metric.mem_ball.mp hxi
    have hj := Metric.mem_ball.mp hxj
    have hdist := dist_triangle_left (b i) (b j) x
    have hs : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ) (b i) (b j), b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,
        b.orthonormal.inner_eq_zero hij]
      norm_num
    nlinarith [dist_nonneg (x := b i) (y := b j)]
  let _ : Countable w := hSep.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  have hInf : ¬ Finite w := by
    intro h
    let _ := Fintype.ofFinite w
    exact hfinite b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  let _ : Infinite w := not_finite_iff_infinite.mp hInf
  let _ : Denumerable w := Classical.choice (nonempty_denumerable w)
  let e := Denumerable.eqv w
  let v (i : ℕ) := b (e.symm i)
  have hv : Orthonormal ℂ v := b.orthonormal.comp e.symm e.symm.injective
  have hrange : Set.range v = Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [v]⟩
  have hspan : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [hrange, b.dense_span]
  exact ⟨(HilbertBasis.mk hv hspan).repr⟩

private theorem pullback_solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : H ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ)) (T : H →L[ℂ] H)
    (V : ClosedInvariantSubspace
      (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap))) :
    Nonempty (ClosedInvariantSubspace T) := by
  let S := V.toSubspace.comap e.toLinearEquiv.toLinearMap
  have hSbot : S ≠ ⊥ := by
    intro hs
    apply V.ne_bot
    apply Submodule.comap_injective_of_surjective e.surjective
    simpa only [S, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr e.injective] using hs
  have hStop : S ≠ ⊤ := by
    intro hs
    apply V.ne_top
    apply Submodule.comap_injective_of_surjective e.surjective
    simpa only [S, Submodule.comap_top] using hs
  refine ⟨⟨S, hSbot, hStop, V.is_closed.preimage e.continuous, ?_⟩⟩
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  change e (T x) ∈ V.toSubspace
  have hx' : e x ∈ V.toSubspace := hx
  have hm := V.is_fixed (Submodule.mem_map_of_mem hx')
  simpa using hm

theorem main : H1 → H2 → type_of% @InvariantSubspaceProblem.Invariant_subspace_problem := by
  intro badShift difficultCase H _ _ _ _ hdim T
  by_cases hfinite : FiniteDimensional ℂ H
  · exact Invariant_subspace_problem_finite_dimensional hfinite hdim T
  obtain ⟨e⟩ := sequence_model H hfinite
  let U := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  suffices h : Nonempty (ClosedInvariantSubspace U) by
    obtain ⟨V⟩ := h
    exact pullback_solution e T V
  by_cases hgood : ∀ z : ℂ, Function.Injective (U - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) ∧
      DenseRange (U - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ))
  · exact difficultCase U hgood
  obtain ⟨z, hz⟩ := not_forall.mp hgood
  exact badShift U z (not_and_or.mp hz)

end Proof

end OMA.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1
