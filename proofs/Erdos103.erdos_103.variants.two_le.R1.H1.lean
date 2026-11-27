import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1
import Mathlib

/-! Label the points, place one point of a competitor at the origin,
and minimize the maximum of the finitely many distances on a compact set. -/

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

namespace OMA.DiameterMinimizers

set_option maxHeartbeats 1000000 in
theorem exists_minimizer (n : ℕ) : ∃ A : Finset ℝ², IsMinimiser n A := by
  cases n with
  | zero =>
    refine ⟨∅,⟨?_,?_⟩⟩
    · simp [separatedSets, Metric.IsSeparated']
    · intro B _
      simpa using (Metric.diam_nonneg (s := (B : Set ℝ²)))
  | succ n =>
    let radius : ℝ := n+1
    let S : Set (Fin (n+1) → ℝ²) :=
      {f | ∀ i j, i ≠ j → 1 ≤ dist (f i) (f j)}
    let T := S ∩ Metric.closedBall 0 radius
    have contCoord (i : Fin (n+1)) : Continuous (fun f : Fin (n+1) → ℝ² => f i) :=
      continuous_apply i
    have hRadius : 0 ≤ radius := by dsimp [radius]; positivity
    have hS : IsClosed S := by
      dsimp [S]
      simp_rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro _
      exact isClosed_le continuous_const ((contCoord i).dist (contCoord j))
    have hT : IsCompact T := (isCompact_closedBall _ _).inter_left hS
    let pairs : Finset (Fin (n+1) × Fin (n+1)) := univ
    have hPairs : pairs.Nonempty := ⟨(0,0),mem_univ _⟩
    let cost (f : Fin (n+1) → ℝ²) : ℝ := pairs.sup' hPairs fun ij => dist (f ij.1) (f ij.2)
    have cost_pair (f : Fin (n+1) → ℝ²) (i j : Fin (n+1)) :
        dist (f i) (f j) ≤ cost f :=
      Finset.le_sup' (f := fun ij : Fin (n+1) × Fin (n+1) => dist (f ij.1) (f ij.2))
        (show (i,j) ∈ pairs from mem_univ _)
    have hCont : Continuous cost := by
      apply Continuous.finset_sup'_apply hPairs
      intro ij _
      exact (contCoord ij.1).dist (contCoord ij.2)
    have cost_diam (f : Fin (n+1) → ℝ²) : cost f = Metric.diam (Set.range f) := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro ij _
        exact Metric.dist_le_diam_of_mem (Set.finite_range f).isBounded ⟨_,rfl⟩ ⟨_,rfl⟩
      · apply Metric.diam_le_of_forall_dist_le ((dist_nonneg (x:=f 0) (y:=f 0)).trans (cost_pair f 0 0))
        rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
        exact cost_pair f i j
    let f₀ (i : Fin (n+1)) : ℝ² := EuclideanSpace.single 0 (i.val : ℝ)
    have hFdist (i j : Fin (n+1)) : dist (f₀ i) (f₀ j) = |(i.val:ℝ)-(j.val:ℝ)| := by
      rw [show dist (f₀ i) (f₀ j) = dist (i.val:ℝ) (j.val:ℝ)
        from PiLp.dist_single_same 2 (fun _ : Fin 2 => ℝ) 0 _ _, Real.dist_eq]
    have hFi (i : Fin (n+1)) : (i.val:ℝ) ≤ radius := by
      dsimp [radius]
      exact_mod_cast (show i.val ≤ n+1 by omega)
    have hUpper (i j : Fin (n+1)) : dist (f₀ i) (f₀ j) ≤ radius := by
      rw [hFdist]
      exact abs_le.mpr ⟨by linarith [hFi j, show (0:ℝ) ≤ (i.val:ℝ) by positivity],
        by linarith [hFi i, show (0:ℝ) ≤ (j.val:ℝ) by positivity]⟩
    have hf₀ : f₀ ∈ T := by
      constructor
      · intro i j hij
        rw [hFdist]
        have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hij' with hlt|hlt
        · have hh : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hh : (j.val:ℝ)+1 ≤ (i.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
          rw [abs_of_nonneg (by linarith)]
          linarith
      · rw [Metric.mem_closedBall, dist_pi_le_iff hRadius]
        intro i
        have hZero : f₀ 0 = 0 := by simp [f₀]
        simpa only [hZero,Pi.zero_apply] using hUpper i 0
    obtain ⟨f,hf,hMin⟩ := hT.exists_isMinOn ⟨f₀,hf₀⟩ hCont.continuousOn
    have hcost₀ : cost f₀ ≤ radius := by
      apply Finset.sup'_le
      intro ij _
      exact hUpper ij.1 ij.2
    have hcost : cost f ≤ radius := (hMin hf₀).trans hcost₀
    have hInjective : Function.Injective f := by
      intro i j hEq
      by_contra h
      have hh := hf.1 i j h
      simp only [hEq,dist_self] at hh
      linarith
    let A : Finset ℝ² := univ.image f
    have hA : (A : Set ℝ²) = Set.range f := by
      ext x
      simp [A]
    refine ⟨A,⟨⟨?_,?_⟩,?_⟩⟩
    · simp [A,card_image_of_injective _ hInjective]
    · rw [hA]
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
      have hh := hf.1 i j (fun h => hij (congrArg f h))
      change (1:ℝ≥0∞) ≤ edist (f i) (f j)
      rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg]
      exact hh
    · intro B hB
      change Metric.diam (A:Set ℝ²) ≤ Metric.diam (B:Set ℝ²)
      rw [hA,←cost_diam]
      by_cases hLarge : radius ≤ Metric.diam (B:Set ℝ²)
      · exact hcost.trans hLarge
      have hCard : B.card = n+1 := hB.1
      let e : Fin (n+1) ≃ B := (equivFinOfCardEq hCard).symm
      let g (i : Fin (n+1)) : ℝ² := (e i : ℝ²) - (e 0 : ℝ²)
      have hDist (i j : Fin (n+1)) :
          dist (g i) (g j) = dist (e i : ℝ²) (e j : ℝ²) := dist_sub_right ..
      have hBound (i j : Fin (n+1)) : dist (g i) (g j) ≤ Metric.diam (B : Set ℝ²) := by
        rw [hDist]
        exact Metric.dist_le_diam_of_mem B.finite_toSet.isBounded (e i).property (e j).property
      have hg : g ∈ T := by
        constructor
        · intro i j hij
          rw [hDist]
          have hij' : (e i : ℝ²) ≠ (e j : ℝ²) := fun h => hij (e.injective (Subtype.ext h))
          have hh := hB.2 (e i).property (e j).property hij'
          change (1:ℝ≥0∞) ≤ edist (e i : ℝ²) (e j : ℝ²) at hh
          rwa [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hh
        · rw [Metric.mem_closedBall,dist_pi_le_iff hRadius]
          intro i
          have hZero : g 0 = 0 := sub_self _
          simpa only [hZero,Pi.zero_apply] using (hBound i 0).trans (le_of_not_ge hLarge)
      refine (hMin hg).trans ?_
      apply Finset.sup'_le
      intro ij _
      exact hBound ij.1 ij.2

end OMA.DiameterMinimizers

theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1.H1 :=
  Eventually.of_forall OMA.DiameterMinimizers.exists_minimizer
