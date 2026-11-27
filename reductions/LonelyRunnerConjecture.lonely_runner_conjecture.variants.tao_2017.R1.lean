import FormalConjectures.Wikipedia.LonelyRunnerConjecture
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Split the proof by the number of speed pairs whose reduced ratio has small height.
The dense case uses the arithmetic estimate in Hu and Jing, arXiv:2610.23790,
Theorem 7.2. The sparse case uses their pair estimate and dilation argument
in Sections 3, 4, and 8. Both bounds concern overlap at radius 1/(2n).
At this radius the total mass of the bad sets is one, so their uncovered
mass equals the integral of the excess multiplicity. That integral is
bounded above by the sum of the overlapping parts of the bad sets.
-/

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1

open MeasureTheory MeasureTheory.Measure Function Metric Set Filter LonelyRunnerConjecture

theorem cover_overlap_bound {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (μ : Measure α) [IsFiniteMeasure μ] (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i, μ.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)) ≤
      2 * ((∑ i, μ.real (A i)) - μ.real (⋃ i, A i)) := by
  classical
  let D := disjointed A
  let R (i : ι) := A i \ D i
  let U := ⋃ i, R i
  have hD (i : ι) : MeasurableSet (D i) := by
    change MeasurableSet (disjointed A i)
    rw [disjointed_eq_inter_compl]
    exact (hA i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hA j).compl)
  have hd : Pairwise (Disjoint on D) := disjoint_disjointed A
  have hsub (i : ι) : D i ⊆ A i := disjointed_subset A i
  have hU : MeasurableSet U := MeasurableSet.iUnion fun i => (hA i).diff (hD i)
  have hover (i : ι) : A i ∩ (⋃ j, ⋃ (_ : j ≠ i), A j) ⊆ (D i ∩ U) ∪ R i := by
    rintro x ⟨hxA, hx⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨hne, hxj⟩ := mem_iUnion.mp hj
    by_cases hxi : x ∈ D i
    · have hxnj : x ∉ D j := fun hxD => (disjoint_left.mp (hd hne.symm)) hxi hxD
      exact Or.inl ⟨hxi, mem_iUnion.mpr ⟨j, hxj, hxnj⟩⟩
    · exact Or.inr ⟨hxA, hxi⟩
  have hdis : Pairwise (Disjoint on fun i => D i ∩ U) := fun _ _ hij =>
    (hd hij).mono inter_subset_left inter_subset_left
  have hmass : (∑ i, μ.real (D i ∩ U)) ≤ μ.real U := by
    rw [← measureReal_iUnion_fintype hdis (fun i => (hD i).inter hU)]
    exact measureReal_mono (iUnion_subset fun _ => inter_subset_right)
  have hsum : (∑ i, μ.real (R i)) = (∑ i, μ.real (A i)) - μ.real (⋃ i, A i) := by
    have hsplit (i : ι) : μ.real (R i) + μ.real (D i) = μ.real (A i) := by
      have he := measureReal_sdiff_add_inter (μ := μ) (s := A i) (hD i)
      rwa [inter_eq_right.mpr (hsub i)] at he
    have hsplitSum := Finset.sum_congr (show (Finset.univ : Finset ι) = Finset.univ from rfl)
      (fun i _ => hsplit i)
    rw [Finset.sum_add_distrib, ← measureReal_iUnion_fintype hd hD] at hsplitSum
    change (∑ i, μ.real (R i)) + μ.real (⋃ i, disjointed A i) = (∑ i, μ.real (A i)) at hsplitSum
    rw [iUnion_disjointed] at hsplitSum
    linarith
  calc
    (∑ i, μ.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)) ≤
        ∑ i, (μ.real (D i ∩ U) + μ.real (R i)) := by
      exact Finset.sum_le_sum fun i _ =>
        (measureReal_mono (hover i)).trans (measureReal_union_le _ _)
    _ ≤ 2 * ∑ i, μ.real (R i) := by
      rw [Finset.sum_add_distrib]
      have hb : μ.real U ≤ ∑ i, μ.real (R i) := measureReal_iUnion_fintype_le R
      linarith
    _ = _ := by rw [hsum]

theorem exists_lonely_time_of_overlap {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0)
    (hover : 2 * ((n : ℝ) * (2 * d) - 1) <
      ∑ i, volume.real (((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d) ∩ ⋃ j, ⋃ (_ : j ≠ i), ((fun t : UnitAddCircle => v j • t) ⁻¹' closedBall 0 d))) :
    ∃ t : UnitAddCircle, ∀ i, d ≤ dist (v i • t) 0 := by
  by_contra! h
  have hm (i : Fin n) : MeasurePreserving (fun t : UnitAddCircle => v i • t) volume volume :=
    measurePreserving_zsmul volume (hv i)
  have hcover : (⋃ i, ((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d)) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨i, hi⟩ := h t
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change v i • t ∈ closedBall (0 : UnitAddCircle) d
    exact mem_closedBall.mpr (le_of_lt hi)
  have hmass (i : Fin n) : volume.real (((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d)) ≤ 2 * d := by
    unfold Measure.real
    rw [(hm i).measure_preimage measurableSet_closedBall.nullMeasurableSet,
      AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by positivity))]
    exact min_le_right _ _
  have htotal : (∑ i, volume.real (((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d))) ≤ (n : ℝ) * (2 * d) := by
    calc
      (∑ i, volume.real (((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d))) ≤ ∑ _i : Fin n, (2 * d) :=
        Finset.sum_le_sum fun i _ => hmass i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hupper := cover_overlap_bound volume (fun i : Fin n => ((fun t : UnitAddCircle => v i • t) ⁻¹' closedBall 0 d))
    (fun i => (hm i).measurable measurableSet_closedBall)
  rw [hcover, show volume.real (univ : Set UnitAddCircle) = 1 by
    simp [Measure.real, AddCircle.measure_univ]] at hupper
  linarith

theorem signed_speeds_of_positive {n : ℕ} {d : ℝ}
    (hpos : ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
      ∃ t : UnitAddCircle, ∀ i, d ≤ dist ((v i : ℤ) • t) 0)
    (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0) :
    ∃ t : UnitAddCircle, ∀ i, d ≤ dist (v i • t) 0 := by
  classical
  let s : Finset ℕ := Finset.univ.image fun i : Fin n => (v i).natAbs - 1
  have hs : s.card ≤ n := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (v i).natAbs - 1))
  obtain ⟨S, hS, hcard⟩ := Infinite.exists_superset_card_eq s n hs
  let e := (S.equivFinOfCardEq hcard).symm
  let w : Fin n ↪ ℕ := ⟨fun j => (e j).val + 1, by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact Nat.add_right_cancel hij⟩
  obtain ⟨t, ht⟩ := hpos w (fun i => Nat.zero_lt_succ _)
  refine ⟨t, fun i => ?_⟩
  have hi : (v i).natAbs - 1 ∈ S := hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let a : S := ⟨(v i).natAbs - 1, hi⟩
  have hw : w (e.symm a) = (v i).natAbs := by
    change (e (e.symm a)).val + 1 = _
    rw [Equiv.apply_symm_apply]
    change (v i).natAbs - 1 + 1 = (v i).natAbs
    exact Nat.sub_add_cancel (Int.natAbs_pos.mpr (hv i))
  have htime := ht (e.symm a)
  rw [hw] at htime
  rcases le_or_gt 0 (v i) with hi | hi
  · have he : ((v i).natAbs : ℤ) = v i := Int.natAbs_of_nonneg hi
    simpa only [he] using htime
  · have he : ((v i).natAbs : ℤ) = -(v i) := by
      simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (neg_nonneg.mpr hi.le)
    simpa only [he, neg_zsmul, dist_zero_right, norm_neg] using htime

private theorem time_of_baseline_overlap {n : ℕ} (hn : 0 < n) {k : ℝ} (hk : 0 < k)
    (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0)
    (hover : let A (i : Fin n) : Set UnitAddCircle :=
        (fun t => v i • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
      k ≤ ∑ i, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)) :
    ∃ t : UnitAddCircle, ∀ i, 1 / (2 * (n : ℝ)) + (k / 8) / n ≤ dist (v i • t) 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let d₀ : ℝ := 1 / (2 * (n : ℝ))
  let d : ℝ := d₀ + (k / 8) / n
  have hd : 0 ≤ d := by dsimp [d, d₀]; positivity
  have hd₀ : d₀ ≤ d := by dsimp [d]; linarith [show 0 ≤ (k / 8) / (n : ℝ) by positivity]
  let A (r : ℝ) (i : Fin n) : Set UnitAddCircle := (fun t => v i • t) ⁻¹' closedBall 0 r
  have hmono (i : Fin n) : A d₀ i ⊆ A d i :=
    preimage_mono (closedBall_subset_closedBall hd₀)
  have hsum :
      (∑ i, volume.real (A d₀ i ∩ ⋃ j, ⋃ (_ : j ≠ i), A d₀ j)) ≤
        ∑ i, volume.real (A d i ∩ ⋃ j, ⋃ (_ : j ≠ i), A d j) :=
    Finset.sum_le_sum fun i _ => measureReal_mono
      (inter_subset_inter (hmono i) (iUnion_mono fun j => iUnion_mono fun _ => hmono j))
  have hstrict : 2 * ((n : ℝ) * (2 * d) - 1) < k := by
    dsimp [d, d₀]
    field_simp
    nlinarith
  exact exists_lonely_time_of_overlap hd v hv (hstrict.trans_le (hover.trans hsum))

private theorem log_gain_le (x k : ℝ) (hx : Real.exp (Real.exp 1) ≤ x) (hk : 0 ≤ k) :
    k * Real.log x / (x^2 * Real.log (Real.log x)^2) ≤ k / x := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : Real.exp 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
  have hloglog : 1 ≤ Real.log (Real.log x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlog
  have hsq : (1 : ℝ) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
  have hxlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
  apply (div_le_div_iff₀ (by positivity) hxpos).2
  calc
    k * Real.log x * x ≤ k * x * x := by gcongr
    _ = k * x^2 := by ring
    _ ≤ k * (x^2 * Real.log (Real.log x)^2) := by
      rw [← mul_assoc]
      exact le_mul_of_one_le_right (by positivity) hsq

/-- Many pairs of velocities have reduced ratio height at most (64n). -/
def H1 : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
    n^2 ≤ 64 * ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
      ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64*n*Nat.gcd (v ij.1) (v ij.2)).card →
    let A (i : Fin n) : Set UnitAddCircle :=
      (fun t => (v i : ℤ) • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
    k ≤ ∑ i, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)

/-- Few pairs of velocities have reduced ratio height at most (64n). -/
def H2 : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
    64 * ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
      ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64*n*Nat.gcd (v ij.1) (v ij.2)).card < n^2 →
    let A (i : Fin n) : Set UnitAddCircle :=
      (fun t => (v i : ℤ) • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
    k ≤ ∑ i, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)

theorem main : H1 → H2 → type_of% @LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017 := by
  rintro ⟨k₁, hk₁, hdense⟩ ⟨k₂, hk₂, hsparse⟩
  let k := min k₁ k₂
  have hk : 0 < k := lt_min hk₁ hk₂
  refine ⟨k / 8, by positivity, ?_⟩
  have hcast : ∀ᶠ n : ℕ in atTop, Real.exp (Real.exp 1) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℕ), hcast] with n hn hnx
  have hnpos : 0 < n := by omega
  unfold deltaGap
  apply le_csInf
  · let w : Fin n ↪ ℤ := ⟨fun i => (i.val : ℤ) + 1, by
      intro i j h
      change (i.val : ℤ) + 1 = (j.val : ℤ) + 1 at h
      apply Fin.ext
      omega⟩
    exact ⟨deltaTuple w, w, fun i => by change (i.val : ℤ) + 1 ≠ 0; omega, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have ht := signed_speeds_of_positive (n := n)
      (d := 1 / (2 * (n : ℝ)) + (k / 8) / n) (fun w hw => by
        let A (i : Fin n) : Set UnitAddCircle :=
          (fun t => (w i : ℤ) • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
        have hh : k ≤ ∑ i, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j) := by
          by_cases h : n^2 ≤ 64 * ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
              ij.1 < ij.2 ∧ max (w ij.1) (w ij.2) ≤ 64*n*Nat.gcd (w ij.1) (w ij.2)).card
          · exact (min_le_left _ _).trans (hdense n hn w hw h)
          · exact (min_le_right _ _).trans (hsparse n hn w hw (lt_of_not_ge h))
        exact time_of_baseline_overlap hnpos hk (fun i => (w i : ℤ))
          (fun i => by exact_mod_cast (hw i).ne') hh) v hv
    unfold deltaTuple
    refine (add_le_add le_rfl (log_gain_le (n : ℝ) (k / 8) hnx (by positivity))).trans ?_
    apply le_csSup
    · refine ⟨1 / 2, ?_⟩
      rintro r ⟨t, htr⟩
      refine (htr ⟨0, hnpos⟩).trans ?_
      simpa [dist_zero_right] using AddCircle.norm_le_half_period (1 : ℝ) (by norm_num)
        (x := v ⟨0, hnpos⟩ • t)
    · exact ht

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1
