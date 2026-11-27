import OMAReductions.R_Erdos1207_erdos_1207_R1

-- Adapted from github.com/tadamcz/erdos1207 (commit 228fcd87a53ab2d7d925d2c849096dcc4438d96b), (c) 2026 Tom Adamczewski / Epoch AI, Apache-2.0.
-- The source proof was produced by a pre-release GPT-6 Astra (OpenAI) in the FrontierMath Erdos benchmark harness and is not refereed.
-- Ported from Lean v4.27.0 to the site pin (Lean v4.33.1); the file is comment-stripped and pruned to what this step needs.
-- Source licence notice: Apache License 2.0, copy in the source repository (LICENSE, NOTICE); local changes are the port edits only.
open Filter
open scoped EuclideanGeometry
theorem prod_cast_eq {ι : Type*} {s : Finset ι} {a : ι → ℤ} {m : ℤ} (R : Type*) [CommRing R]
    (h : ∏ i ∈ s, (4*a i+1) = m) : ∏ i ∈ s, (4*(a i : R)+1) = (m : R) := by
  have := congrArg (Int.cast : ℤ → R) h
  push_cast at this
  exact this
theorem prod_cast_eq' {ι : Type*} {s : Finset ι} {a : ι → ℤ} {b : ℤ} (R : Type*) [CommRing R]
    (h : ∏ i ∈ s, (4*a i+1) = 4*b+1) : ∏ i ∈ s, (4*(a i : R)+1) = 4*(b : R)+1 := by
  have := prod_cast_eq R h
  push_cast at this
  exact this
theorem prod_cast_eq'' {ι : Type*} {s : Finset ι} {a : ι → ℤ} {n : ℕ} (R : Type*) [CommRing R]
    (h : ∏ i ∈ s, (4*a i+1) = (n : ℤ)) : ∏ i ∈ s, (4*(a i : R)+1) = (n : R) := by
  have := prod_cast_eq R h
  push_cast at this
  exact this
theorem cast_eq_four_mul_add_one {R : Type*} [Ring R] {n : ℕ} {a : ℤ}
    (h : (n : ℤ) = 4*a+1) : (n : R) = 4*(a : R)+1 := by
  have := congrArg (Int.cast : ℤ → R) h
  push_cast at this
  exact this
open MeasureTheory
open scoped ENNReal
namespace BlichfeldtCounting

theorem overlap_le_card {G E : Type*} [AddGroup G] [AddAction G E]
    (s : Set E) (U : Finset G)
    (hU : ∀ g h : G, ∀ x : E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) (x : E) :
    (∑' g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) ≤ U.card := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro T
  have hc : (T.filter (fun g => g +ᵥ x ∈ s)).card ≤ U.card := by
    let V := T.filter (fun g => g +ᵥ x ∈ s)
    by_cases hV : V.Nonempty
    · obtain ⟨g₀,hg₀⟩ := hV
      have hg₀' := (Finset.mem_filter.mp hg₀).2
      apply Finset.card_le_card_of_injOn (fun g => g-g₀)
      · intro g hg
        exact hU g g₀ x (Finset.mem_filter.mp hg).2 hg₀'
      · intro g _ h _ heq
        exact sub_left_injective heq
    · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (Nat.zero_le _)
  have hs : (∑ g ∈ T, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) =
      ((T.filter (fun g => g +ᵥ x ∈ s)).card : ℝ≥0∞) := by
    simp only [Set.indicator_apply,Finset.sum_boole]
  rw [hs]
  exact_mod_cast hc

theorem measure_le_card_mul {G E : Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ : Measure E) [VAddInvariantMeasure G E μ]
    (F s : Set E) (hF : IsAddFundamentalDomain G F μ) (hs : MeasurableSet s)
    (U : Finset G)
    (hU : ∀ g h : G, ∀ x : E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) :
    μ s ≤ (U.card : ℝ≥0∞) * μ F := by
  have hm (g : G) : Measurable (fun x : E => s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) :=
    (measurable_const.indicator hs).comp (measurable_const_vadd g)
  calc
    μ s = ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      (lintegral_indicator_one hs).symm
    _ = ∑' g : G, ∫⁻ x in F, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      hF.lintegral_eq_tsum'' _
    _ = ∫⁻ x in F, ∑' g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      (lintegral_tsum (fun g => (hm g).aemeasurable)).symm
    _ ≤ ∫⁻ _x in F, (U.card : ℝ≥0∞) ∂μ :=
      lintegral_mono (overlap_le_card s U hU)
    _ = (U.card : ℝ≥0∞) * μ F := by simp

theorem cube_card_lower_bound {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (U : Finset L) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) :
    t^(Fintype.card ι) ≤ (U.card : ℝ) * ZLattice.covolume L := by
  classical
  letI : MeasurableVAdd L (ι → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  let s : Set (ι → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-t/2) (t/2))
  have hs : MeasurableSet s := MeasurableSet.pi (Set.to_countable _) (by intro i _; exact measurableSet_Icc)
  have hdiff : ∀ g h : L, ∀ x : ι → ℝ, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U := by
    intro g h x hg hh
    apply (hU _).mpr
    intro i
    have hg' := Set.mem_pi.mp hg i (Set.mem_univ i)
    have hh' := Set.mem_pi.mp hh i (Set.mem_univ i)
    change -t/2 ≤ (g : ι → ℝ) i + x i ∧ (g : ι → ℝ) i + x i ≤ t/2 at hg'
    change -t/2 ≤ (h : ι → ℝ) i + x i ∧ (h : ι → ℝ) i + x i ≤ t/2 at hh'
    change |(g : ι → ℝ) i - (h : ι → ℝ) i| ≤ t
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hm : volume s = (ENNReal.ofReal t)^(Fintype.card ι) := by
    rw [volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc]
    have he : t/2 - -t/2 = t := by ring
    simp only [he,Finset.prod_const,Finset.card_univ]
  have hfin : volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have h := measure_le_card_mul volume F s hF hs U hdiff
  have hreal := ENNReal.toReal_mono (by finiteness : (U.card : ℝ≥0∞)*volume F ≠ ⊤) h
  rw [hm,ENNReal.toReal_pow,ENNReal.toReal_ofReal ht,ENNReal.toReal_mul,ENNReal.toReal_natCast] at hreal
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hreal

end BlichfeldtCounting
open scoped Pointwise
namespace LogCubeDoubling

theorem sub_card_le {G ι Q : Type*} [AddCommGroup G] [DecidableEq G] [Fintype Q]
    (U : Finset G) (f : G →+ (ι → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f x i| ≤ t)
    (q : G → Q) (hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y) :
    (U-U).card ≤ Fintype.card Q * U.card := by
  classical
  let V : Finset G := U-U
  have hV : ∀ x ∈ V, ∀ i, |f x i| ≤ 2*t := by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
    calc
      |f (a-b) i| = |f a i-f b i| := by simp
      _ ≤ |f a i|+|f b i| := abs_sub _ _
      _ ≤ t+t := add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t := by ring
  have hf : ∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card := by
    intro c hc
    let T : Finset G := V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩ := Finset.mem_image.mp hc
    have hex : ∀ x ∈ T, ∃ z ∈ U, (5 : ℕ) • z = x-x₀ := by
      intro x hx
      obtain ⟨hx,hqx⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩ := hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he : 5 * f z i = f x i - f x₀ i := by
        have hh := congrArg (fun w => f w i) hz
        simpa using hh
      have hb : |f x i - f x₀ i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g : T → U := fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x : T) : (5 : ℕ) • (g x : G) = (x : G)-x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hh := congrArg (fun z : U => (5 : ℕ) • (z : G)) hxy
      try dsimp only at hh
      rw [hg,hg] at hh
      exact sub_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U-U).card ≤ U.card * (V.image q).card := Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card := Nat.mul_comm _ _

theorem int_cube_sub_card_le {ι κ : Type*} [Fintype ι]
    (U : Finset (ι → ℤ)) (f : (ι → ℤ) →+ (κ → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f x i| ≤ t) :
    (U-U).card ≤ 5^(Fintype.card ι) * U.card := by
  classical
  let q : (ι → ℤ) → (ι → ZMod 5) := fun x i => x i
  have hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y := by
    intro x y hxy
    refine ⟨fun i => (x i-y i)/5,?_⟩
    ext i
    have hdiv : (5 : ℤ) ∣ x i-y i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by
      rw [Int.cast_sub,sub_eq_zero]
      exact congrFun hxy i)
    simpa using Int.mul_ediv_cancel' hdiv
  simpa [Fintype.card_pi,ZMod.card] using sub_card_le U f t ht hU q hroot

end LogCubeDoubling
namespace LatticeCube
open scoped Pointwise

theorem finite_cube {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (t : ℝ) (ht : 0 ≤ t) : {x : L | ∀ i, |(x : ι → ℝ) i| ≤ t}.Finite := by
  letI : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hclosed : IsClosed (L : Set (ι → ℝ)) := by
    change IsClosed (L.toAddSubgroup : Set (ι → ℝ))
    exact AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall 0 t ∩ (L : Set (ι → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hclosed
  apply Set.Finite.of_finite_image (f := fun x : L => (x : ι → ℝ)) _ Subtype.val_injective.injOn
  apply hfin.subset
  rintro x ⟨y,hy,rfl⟩
  refine ⟨?_,y.property⟩
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg ht]
  simpa only [Real.norm_eq_abs, Set.mem_setOf_eq] using hy

theorem sub_card_le {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (U : Finset L) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) :
    (U-U).card ≤ 5^(Fintype.card ι) * U.card := by
  classical
  let e := (IsZLattice.basis L).equivFun
  let q : L → (ι → ZMod 5) := fun x i => e x i
  have hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y := by
    intro x y hxy
    refine ⟨e.symm (fun i => (e x i-e y i)/5),?_⟩
    apply e.injective
    ext i
    have hdiv : (5 : ℤ) ∣ e x i-e y i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by
      rw [Int.cast_sub,sub_eq_zero]
      exact congrFun hxy i)
    simpa using Int.mul_ediv_cancel' hdiv
  simpa [Fintype.card_pi,ZMod.card] using
    LogCubeDoubling.sub_card_le U L.subtype.toAddMonoidHom t ht hU q hroot

theorem exists_cube {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (t : ℝ) (ht : 0 ≤ t) :
    ∃ U : Finset L,
      (∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) ∧
      t^(Fintype.card ι) ≤ (U.card : ℝ)*ZLattice.covolume L ∧
      (U-U).card ≤ 5^(Fintype.card ι)*U.card := by
  classical
  let U := (finite_cube L t ht).toFinset
  have hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t := by simp [U]
  exact ⟨U,hU,BlichfeldtCounting.cube_card_lower_bound L U t ht hU,
    sub_card_le L U t ht hU⟩

end LatticeCube
namespace BalancedFiniteSets
open scoped BigOperators Pointwise

theorem linear_le_pow (r : ℕ) : 2*r+1 ≤ 3^r := by
  induction r with
  | zero => norm_num
  | succ r ih => rw [pow_succ]; nlinarith

theorem exists_balanced {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]
    (S : Finset G) (hS : S.Nonempty) (f : G →+ (ι → ℝ)) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ x ∈ S, ∀ i, |f x i| ≤ t) :
    ∃ W : Finset G, W.Nonempty ∧ S.card ≤ (2*Fintype.card ι+1)*W.card ∧
      ∀ w ∈ W, (∀ i, |f w i| ≤ 2*t) ∧ |∑ i, f w i| ≤ t := by
  classical
  let r := Fintype.card ι
  let q : G → ℤ := fun x => ⌊(∑ i, f x i)/t⌋
  have hq : ∀ x ∈ S, q x ∈ Finset.Icc (-(r : ℤ)) r := by
    intro x hx
    have hs : |∑ i, f x i| ≤ (r : ℝ)*t :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa [r] using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound x hx i)))
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      have hh := (abs_le.mp hs).1
      rw [le_div_iff₀ ht]
      simpa using hh
    · apply Int.floor_le_iff.mpr
      have hh := (div_le_iff₀ ht).mpr (abs_le.mp hs).2
      exact hh.trans_lt (by simp)
  have hqcard : (S.image q).card ≤ 2*r+1 := by
    have hs : S.image q ⊆ Finset.Icc (-(r : ℤ)) r := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact hq x hx
    have hc : (Finset.Icc (-(r : ℤ)) r).card = 2*r+1 := by rw [Int.card_Icc]; omega
    exact (Finset.card_le_card hs).trans_eq hc
  obtain ⟨c,hc,hmax⟩ := (S.image q).exists_max_image
    (fun c => (S.filter (fun x => q x = c)).card) (hS.image q)
  let V := S.filter (fun x => q x = c)
  obtain ⟨v,hv,hqv⟩ := Finset.mem_image.mp hc
  have hvV : v ∈ V := Finset.mem_filter.mpr ⟨hv,hqv⟩
  let W := V.image (fun x => x-v)
  have hW : W.Nonempty := (Finset.nonempty_iff_ne_empty.mpr (by
    exact Finset.ne_empty_of_mem hvV)).image _
  have hcW : W.card = V.card := Finset.card_image_iff.mpr (by
    intro a _ b _ h
    exact sub_left_injective h)
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW]
    exact (Finset.card_le_mul_card_image S V.card hmax).trans (by nlinarith [hqcard])
  · intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hx,hqc⟩ := Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · intro i
      simp only [map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])
    · have heq : q x = q v := hqc.trans hqv.symm
      have h₁ := Int.floor_le ((∑ i, f x i)/t)
      have h₂ := Int.lt_floor_add_one ((∑ i, f x i)/t)
      have h₃ := Int.floor_le ((∑ i, f v i)/t)
      have h₄ := Int.lt_floor_add_one ((∑ i, f v i)/t)
      change (q x : ℝ) ≤ _ at h₁
      change _ < (q x : ℝ)+1 at h₂
      change (q v : ℝ) ≤ _ at h₃
      change _ < (q v : ℝ)+1 at h₄
      rw [heq] at h₁ h₂
      have hh : |(∑ i, f x i)/t-(∑ i, f v i)/t| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
      rw [← sub_div,abs_div,abs_of_pos ht] at hh
      have hh' := (div_lt_iff₀ ht).mp hh
      simpa only [map_sub,Pi.sub_apply,Finset.sum_sub_distrib,one_mul] using hh'.le

end BalancedFiniteSets
namespace BalancedLattice
open scoped BigOperators

theorem exists_many {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (t : ℝ) (ht : 0 < t) :
    ∃ W : Finset L, W.Nonempty ∧
      (t/3)^(Fintype.card ι) ≤ (W.card : ℝ)*ZLattice.covolume L ∧
      ∀ w ∈ W, (∀ i, |(w : ι → ℝ) i| ≤ 2*t) ∧ |∑ i, (w : ι → ℝ) i| ≤ t := by
  classical
  obtain ⟨U,hU,hUcard,_⟩ := LatticeCube.exists_cube L t ht.le
  have hUpos : U.Nonempty := ⟨0,(hU 0).mpr (by simpa using fun _ : ι => ht.le)⟩
  obtain ⟨W,hW,hcard,hbound⟩ := BalancedFiniteSets.exists_balanced U hUpos L.subtype.toAddMonoidHom t ht
    (fun x hx => (hU x).mp hx)
  refine ⟨W,hW,?_,hbound⟩
  have hc : U.card ≤ 3^(Fintype.card ι)*W.card :=
    hcard.trans (Nat.mul_le_mul_right _ (BalancedFiniteSets.linear_le_pow _))
  have hh : t^(Fintype.card ι) ≤ (3 : ℝ)^(Fintype.card ι)*W.card*ZLattice.covolume L :=
    hUcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ZLattice.covolume_pos L).le)
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) _)).mpr
  nlinarith

end BalancedLattice
namespace BoundedUnits
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]

theorem exists_many (t : ℝ) (ht : 0 < t) :
    ∃ U : Finset (𝓞 K)ˣ, U.Nonempty ∧
      (t/3)^(NumberField.Units.rank K) ≤ (U.card : ℝ)*NumberField.Units.regulator K ∧
      ∀ u ∈ U, ∀ w : InfinitePlace K, |Real.log (w (u : K))| ≤ 2*t := by
  let L := NumberField.Units.unitLattice K
  have hlift : ∀ x : L, ∃ u : (𝓞 K)ˣ, NumberField.Units.logEmbedding K (Additive.ofMul u) = (x : logSpace K) := by
    intro x
    obtain ⟨a,_,ha⟩ := Submodule.mem_map.mp x.property
    exact ⟨a.toMul,ha⟩
  choose lift hlift using hlift
  have hinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    rw [← hlift x,← hlift y,hxy]
  obtain ⟨W,hW,hWcard,hWbound⟩ := BalancedLattice.exists_many L t ht
  let U := W.image lift
  have hc : U.card = W.card := Finset.card_image_of_injective _ hinj
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  refine ⟨U,hW.image lift,?_,?_⟩
  · simpa only [hc,hcard,NumberField.Units.regulator] using hWcard
  · intro u hu w
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    have hm : (1 : ℝ) ≤ mult w := by simp only [mult]; split_ifs <;> norm_num
    have hm0 : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have hle : |Real.log (w ((lift x : (𝓞 K)ˣ) : K))| ≤
        (mult w : ℝ)*|Real.log (w ((lift x : (𝓞 K)ˣ) : K))| :=
      le_mul_of_one_le_left (abs_nonneg _) hm
    by_cases hw : w = w₀
    · have hh := (hWbound x hx).2
      have hsum := sum_logEmbedding_component (lift x)
      rw [hlift x] at hsum
      rw [hsum,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)] at hh
      rw [← hw] at hh
      exact hle.trans (hh.trans (by linarith))
    · have hh := (hWbound x hx).1 ⟨w,hw⟩
      rw [← hlift x,logEmbedding_component,abs_mul,abs_of_nonneg hm0] at hh
      exact hle.trans hh

theorem exists_many_house_bounded (t : ℝ) (ht : 0 < t) :
    ∃ U : Finset (𝓞 K)ˣ, U.Nonempty ∧
      (t/3)^(NumberField.Units.rank K) ≤ (U.card : ℝ)*NumberField.Units.regulator K ∧
      ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ Real.exp (2*t) := by
  obtain ⟨U,hU,hcard,hbound⟩ := exists_many K t ht
  refine ⟨U,hU,hcard,?_⟩
  intro u hu σ
  have hh := hbound u hu (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : K)‖| ≤ 2*t at hh
  have hp : 0 < ‖σ (u : K)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  exact (Real.log_le_iff_le_exp hp).mp ((le_abs_self _).trans hh)

end BoundedUnits
namespace TotallyRealHeight
open NumberField NumberField.InfinitePlace
open scoped BigOperators

theorem scalar_bound (y : ℝ) (hy : 0 ≤ y) :
    2*y*|y^2-1| ≤ (max 1 y)^4 := by
  by_cases h : y ≤ 1
  · rw [max_eq_left h,abs_of_nonpos (by nlinarith : y^2-1 ≤ 0)]
    have hh : 0 ≤ y^2*(1-y^2) := mul_nonneg (sq_nonneg y) (by nlinarith)
    nlinarith [sq_nonneg (y^2+y-1)]
  · have h' : 1 ≤ y := le_of_not_ge h
    rw [max_eq_right h',abs_of_nonneg (by nlinarith : 0 ≤ y^2-1)]
    nlinarith [sq_nonneg (y^2-y-1)]

private theorem log_max_identity (x : ℝ) (hx : 0 < x) :
    2*Real.log (max 1 x) = |Real.log x| + Real.log x := by
  by_cases h : 1 ≤ x
  · rw [max_eq_right h,abs_of_nonneg (Real.log_nonneg h)]
    ring
  · have h' : x ≤ 1 := le_of_not_ge h
    rw [max_eq_left h',Real.log_one,abs_of_nonpos (Real.log_nonpos hx.le h')]
    ring

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

private theorem place_quad (w : InfinitePlace K) (x : K) :
    w (x^2-1) = |(w x)^2-1| := by
  have hw := IsTotallyReal.isReal w
  rw [← norm_embedding_of_isReal hw (x^2-1),← norm_embedding_of_isReal hw x]
  simp [map_sub,map_pow,Real.norm_eq_abs]

private theorem prod_places_ge_one (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ ∏ w : InfinitePlace K, w (a : K) := by
  have hp := InfinitePlace.prod_eq_abs_norm (a : K)
  simp only [IsTotallyReal.mult_eq,pow_one] at hp
  rw [hp,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

theorem height_product_bound (u : (𝓞 K)ˣ) (hu : (u : K)^2 ≠ 1) :
    (2 : ℝ)^(Fintype.card (InfinitePlace K)) ≤
      (∏ w : InfinitePlace K, max 1 (w (u : K)))^4 := by
  classical
  let a : 𝓞 K := (u : 𝓞 K)^2-1
  have ha : a ≠ 0 := by
    intro h
    have hh := congrArg (algebraMap (𝓞 K) K) h
    apply hu
    simpa [a,sub_eq_zero] using hh
  have hprod : 1 ≤ ∏ w : InfinitePlace K, w ((u : K)^2-1) := by
    simpa [a] using prod_places_ge_one K a ha
  have hunit : (∏ w : InfinitePlace K, w (u : K)) = 1 := by
    simpa only [IsTotallyReal.mult_eq,pow_one,NumberField.Units.norm,Rat.cast_one] using
      InfinitePlace.prod_eq_abs_norm (u : K)
  have hpoint (w : InfinitePlace K) :
      2*w (u : K)*w ((u : K)^2-1) ≤ (max 1 (w (u : K)))^4 := by
    rw [place_quad K]
    exact scalar_bound _ (apply_nonneg w _)
  have hp := Finset.prod_le_prod (s := Finset.univ)
    (fun w _ => mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg w _)) (apply_nonneg w _))
    (fun w _ => hpoint w)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow,hunit,mul_one] at hp
  exact (le_mul_of_one_le_right (by positivity) hprod).trans hp

theorem log_height_bound (u : (𝓞 K)ˣ) (hu : (u : K)^2 ≠ 1) :
    (Fintype.card (InfinitePlace K) : ℝ)*Real.log 2 ≤
      2*∑ w : InfinitePlace K, |Real.log (w (u : K))| := by
  classical
  have hp := height_product_bound K u hu
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^(Fintype.card (InfinitePlace K))) hp
  rw [Real.log_pow,Real.log_pow,Real.log_prod (fun w _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))] at hlog
  have hsum : (∑ w : InfinitePlace K, Real.log (w (u : K))) = 0 := by
    simpa only [IsTotallyReal.mult_eq,Nat.cast_one,one_mul] using NumberField.Units.sum_mult_mul_log u
  have hid : 2*(∑ w : InfinitePlace K, Real.log (max 1 (w (u : K)))) =
      ∑ w : InfinitePlace K, |Real.log (w (u : K))| := by
    rw [Finset.mul_sum]
    simp_rw [log_max_identity _ (NumberField.Units.pos_at_place u _)]
    rw [Finset.sum_add_distrib,hsum,add_zero]
  norm_num at hlog
  linarith

open NumberField.Units.dirichletUnitTheorem in

theorem small_log_cube_sq_eq_one (u : (𝓞 K)ˣ)
    (hsmall : ∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    (u : K)^2 = 1 := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 ≤ Real.log 2/8 := by positivity
  have hcard : (0 : ℝ) < Fintype.card (InfinitePlace K) := by exact_mod_cast Fintype.card_pos
  have hsum := sum_logEmbedding_component u
  simp only [logEmbedding_component,IsTotallyReal.mult_eq,Nat.cast_one,one_mul] at hsum hsmall
  let N := Fintype.card (InfinitePlace K)
  let S := ∑ i : {w : InfinitePlace K // w ≠ w₀}, |Real.log (i.val (u : K))|
  have hs : S ≤ N*(Real.log 2/8) := by
    calc
      S ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ)*(Real.log 2/8) := by
        simpa [S] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsmall i)
      _ ≤ N*(Real.log 2/8) := mul_le_mul_of_nonneg_right (by
        exact_mod_cast Fintype.card_subtype_le (fun w : InfinitePlace K => w ≠ w₀)) ht
  have hlast : |Real.log (w₀ (u : K))| ≤ S := by
    have hh := Finset.abs_sum_le_sum_abs
      (fun i : {w : InfinitePlace K // w ≠ w₀} => Real.log (i.val (u : K))) Finset.univ
    rw [hsum] at hh
    simpa [S] using hh
  have hall : (∑ w : InfinitePlace K, |Real.log (w (u : K))|) ≤ 2*N*(Real.log 2/8) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    change |Real.log (w₀ (u : K))| + S ≤ _
    linarith
  have hu : (u : K)^2 = 1 := by
    by_contra hu
    have hh := log_height_bound K u hu
    change (N : ℝ)*Real.log 2 ≤ _ at hh
    have hp : (0 : ℝ) < N*Real.log 2 := mul_pos hcard hlog
    linarith
  exact hu

theorem small_log_cube_trivial (u : (𝓞 K)ˣ)
    (hsmall : ∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    NumberField.Units.logEmbedding K (Additive.ofMul u) = 0 := by
  classical
  have hu := small_log_cube_sq_eq_one K u hsmall
  rcases sq_eq_one_iff.mp hu with hu | hu
  · ext i
    simp [NumberField.Units.logEmbedding,hu]
  · ext i
    have hv : i.val (-1 : K) = 1 := by
      rw [← norm_embedding_of_isReal (IsTotallyReal.isReal i.val)]
      simp
    simp [NumberField.Units.logEmbedding,hu,hv]

end TotallyRealHeight
open scoped Pointwise
namespace EmbeddingPacking

theorem card_le_of_separated_coordinates {α ι : Type*} [Fintype ι]
    (S : Finset α) (f : α → ι → ℝ) (R : ℕ)
    (hbound : ∀ a ∈ S, ∀ i, |f a i| ≤ R)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ i, 1 ≤ |f a i-f b i|) :
    S.card ≤ (2*R+1)^(Fintype.card ι) := by
  classical
  let box : Finset (ι → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(R : ℤ)) R)
  let g : α → ι → ℤ := fun a i => ⌊f a i⌋
  have hmaps : Set.MapsTo g (S : Set α) (box : Set (ι → ℤ)) := by
    intro a ha
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hb := abs_le.mp (hbound a ha i)
    constructor
    · exact Int.le_floor.mpr (by simpa using hb.1)
    · apply Int.floor_le_iff.mpr
      exact lt_of_le_of_lt hb.2 (by simp)
  have hinj : Set.InjOn g (S : Set α) := by
    intro a ha b hb heq
    by_contra hab
    obtain ⟨i,hi⟩ := hsep a ha b hb hab
    have hge : ⌊f a i⌋ = ⌊f b i⌋ := congrFun heq i
    have h₁ := Int.floor_le (f a i)
    have h₂ := Int.floor_le (f b i)
    have h₃ := Int.lt_floor_add_one (f a i)
    have h₄ := Int.lt_floor_add_one (f b i)
    rw [hge] at h₁ h₃
    have hlt : |f a i-f b i| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact hlt.not_ge hi
  have hc : box.card = (2*R+1)^(Fintype.card ι) := by
    simp only [box,Fintype.card_piFinset,Int.card_Icc]
    have hnat : ((R : ℤ)+1 - -(R : ℤ)).toNat = 2*R+1 := by omega
    simp only [hnat, Finset.prod_const, Finset.card_univ]
  exact hc ▸ Finset.card_le_card_of_injOn g hmaps hinj

theorem sumset_coordinate_bound {α ι : Type*} [AddCommGroup α] [DecidableEq α]
    (U : Finset α) (f : ι → α →+ ℝ) (R : ℝ)
    (hbound : ∀ u ∈ U, ∀ i, |f i u| ≤ R) (j : ℕ) :
    ∀ x ∈ j • U, ∀ i, |f i x| ≤ j*R := by
  classical
  induction j with
  | zero =>
    intro x hx i
    simp only [zero_nsmul,Finset.mem_zero] at hx
    subst x
    simp
  | succ j ih =>
    intro x hx i
    rw [add_nsmul,one_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    calc
      |f i (a+b)| = |f i a+f i b| := by rw [map_add]
      _ ≤ |f i a|+|f i b| := abs_add_le _ _
      _ ≤ j*R+R := add_le_add (ih a ha i) (hbound b hb i)
      _ = (j+1 : ℕ)*R := by push_cast; ring

theorem sumset_card_le {α ι : Type*} [AddCommGroup α] [DecidableEq α] [Fintype ι]
    (U : Finset α) (f : ι → α →+ ℝ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ i, |f i u| ≤ R)
    (hsep : ∀ a b : α, a ≠ b → ∃ i, 1 ≤ |f i a-f i b|) (j : ℕ) :
    (j • U).card ≤ ((2*R+1)*(j+1))^(Fintype.card ι) := by
  classical
  have hh : ∀ x ∈ j • U, ∀ i, |f i x| ≤ (j*R : ℕ) := by
    simpa only [Nat.cast_mul] using
      sumset_coordinate_bound U f (R : ℝ) hbound j
  have hc := card_le_of_separated_coordinates (j • U) (fun a i => f i a) (j*R)
    hh (fun a _ b _ hab => hsep a b hab)
  exact hc.trans (Nat.pow_le_pow_left (by nlinarith : 2*(j*R)+1 ≤ (2*R+1)*(j+1)) _)

end EmbeddingPacking
namespace TotallyRealUnitCounting
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

private noncomputable abbrev logU (u : (𝓞 K)ˣ) : logSpace K := NumberField.Units.logEmbedding K (Additive.ofMul u)

omit [IsTotallyReal K] in
private theorem log_div (u v : (𝓞 K)ˣ) : logU K (u/v) = logU K u-logU K v := by
  exact map_sub (NumberField.Units.logEmbedding K) (Additive.ofMul u) (Additive.ofMul v)

theorem coe_eq_or_neg_of_log_eq (u v : (𝓞 K)ˣ) (h : logU K u = logU K v) :
    (u : K) = (v : K) ∨ (u : K) = -(v : K) := by
  have hs := TotallyRealHeight.small_log_cube_sq_eq_one K (u/v) (by
    intro i
    change |logU K (u/v) i| ≤ _
    rw [log_div,h,sub_self]
    simp only [Pi.zero_apply,abs_zero]
    positivity)
  have hm : ((u/v : (𝓞 K)ˣ) : K)*(v : K) = (u : K) := by
    rw [← NumberField.Units.coe_mul,div_mul_cancel]
  rcases sq_eq_one_iff.mp hs with hh | hh
  · left
    simpa [hh] using hm.symm
  · right
    simpa [hh] using hm.symm

private theorem fiber_card_le_two (U : Finset (𝓞 K)ˣ) (y : logSpace K) :
    (U.filter (fun u => logU K u = y)).card ≤ 2 := by
  classical
  let V := U.filter (fun u => logU K u = y)
  by_cases hV : V.Nonempty
  · obtain ⟨v,hv⟩ := hV
    have hv' := (Finset.mem_filter.mp hv).2
    have hh : V.card ≤ ({(v : K),-(v : K)} : Finset K).card := by
      apply Finset.card_le_card_of_injOn (fun u : (𝓞 K)ˣ => (u : K))
      · intro u hu
        have he := coe_eq_or_neg_of_log_eq K u v ((Finset.mem_filter.mp hu).2.trans hv'.symm)
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using he
      · exact (NumberField.Units.coe_injective K).injOn
    exact hh.trans (Finset.card_insert_le _ _)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (by norm_num)

theorem card_le_of_log_bound (U : Finset (𝓞 K)ˣ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ i, |logU K u i| ≤ R*(Real.log 2/8)) :
    U.card ≤ 2*(2*R+1)^(NumberField.Units.rank K) := by
  classical
  let c : ℝ := Real.log 2/8
  have hc : 0 < c := by dsimp [c]; positivity
  let W := U.image (logU K)
  have hwbound : ∀ x ∈ W, ∀ i, |x i/c| ≤ R := by
    intro x hx i
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    rw [abs_div,abs_of_pos hc]
    exact (div_le_iff₀ hc).mpr (hbound u hu i)
  have hwsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∃ i, 1 ≤ |x i/c-y i/c| := by
    intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    by_contra! h
    have hs : ∀ i, |logU K (u/v) i| ≤ c := by
      intro i
      have hh := h i
      rw [← sub_div,abs_div,abs_of_pos hc] at hh
      have hh' := (div_lt_iff₀ hc).mp hh
      rw [log_div,Pi.sub_apply]
      linarith
    have hz := TotallyRealHeight.small_log_cube_trivial K (u/v) hs
    change logU K (u/v) = 0 at hz
    rw [log_div,sub_eq_zero] at hz
    exact hxy hz
  have hw := EmbeddingPacking.card_le_of_separated_coordinates W (fun x i => x i/c) R hwbound hwsep
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  rw [hcard] at hw
  exact (Finset.card_le_mul_card_image U 2 (fun y _ => fiber_card_le_two K U y)).trans (Nat.mul_le_mul_left 2 hw)

end TotallyRealUnitCounting
namespace RelativeNormLog
open NumberField NumberField.InfinitePlace
open scoped BigOperators Classical

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

noncomputable def unitNorm : (𝓞 L)ˣ →* (𝓞 K)ˣ := Units.map (RingOfIntegers.norm K)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp] theorem coe_unitNorm (u : (𝓞 L)ˣ) : ((unitNorm K L u : (𝓞 K)ˣ) : K) = Algebra.norm K (u : L) := rfl

omit [NumberField L] in

theorem log_bound (u : (𝓞 L)ˣ) (t : ℝ)
    (hbound : ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t) (w : InfinitePlace K) :
    |Real.log (w ((unitNorm K L u : (𝓞 K)ˣ) : K))| ≤ (Module.finrank K L : ℝ)*t := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  have he : w.embedding (Algebra.norm K (u : L)) = ∏ σ : L →ₐ[K] ℂ, σ (u : L) :=
    Algebra.norm_eq_prod_embeddings K ℂ (u : L)
  have hlog : Real.log (w ((unitNorm K L u : (𝓞 K)ˣ) : K)) =
      ∑ σ : L →ₐ[K] ℂ, Real.log ‖σ (u : L)‖ := by
    rw [← norm_embedding_eq,coe_unitNorm,he,norm_prod,Real.log_prod]
    intro σ _
    apply norm_ne_zero_iff.mpr
    exact fun h => NumberField.Units.coe_ne_zero u (σ.injective (by simpa using h))
  rw [hlog]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh : ∀ σ : L →ₐ[K] ℂ, |Real.log ‖σ (u : L)‖| ≤ t := by
    intro σ
    exact hbound (InfinitePlace.mk σ.toRingHom)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AlgHom.card] using
    Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hh σ)

end RelativeNormLog
namespace KernelFiber

theorem exists_large {G H ι : Type*} [CommGroup G] [CommGroup H]
    [DecidableEq G] [DecidableEq H] (S : Finset G) (hS : S.Nonempty)
    (N : G →* H) (f : Additive G →+ (ι → ℝ)) (t : ℝ)
    (hbound : ∀ x ∈ S, ∀ i, |f (Additive.ofMul x) i| ≤ t) :
    ∃ W : Finset G, W.Nonempty ∧ S.card ≤ (S.image N).card*W.card ∧
      ∀ w ∈ W, N w = 1 ∧ ∀ i, |f (Additive.ofMul w) i| ≤ 2*t := by
  classical
  obtain ⟨c,hc,hmax⟩ := (S.image N).exists_max_image
    (fun c => (S.filter (fun x => N x = c)).card) (hS.image N)
  let V := S.filter (fun x => N x = c)
  obtain ⟨v,hv,hNv⟩ := Finset.mem_image.mp hc
  have hvV : v ∈ V := Finset.mem_filter.mpr ⟨hv,hNv⟩
  let W := V.image (fun x => x/v)
  have hW : W.Nonempty := (show V.Nonempty from ⟨v,hvV⟩).image _
  have hcW : W.card = V.card := Finset.card_image_of_injective _ div_left_injective
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW,mul_comm]
    exact Finset.card_le_mul_card_image S V.card hmax
  · intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hx,hNx⟩ := Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · rw [map_div,hNx,hNv,div_self']
    · intro i
      rw [ofMul_div,map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])

end KernelFiber
namespace BoundedNormOne
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in

noncomputable def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w := Real.log (w (u.toMul : L))
  map_zero' := by simp; rfl
  map_add' := by intro u v; simp [Real.log_mul]; rfl

theorem exists_many (N : ℕ) (hN : 0 < N) :
    ∃ W : Finset (𝓞 L)ˣ, W.Nonempty ∧
      ((Real.log 2/8)*N/3)^(NumberField.Units.rank L) ≤
        2*(4*Module.finrank K L*N+1 : ℕ)^(NumberField.Units.rank K) *
          (W.card : ℝ)*NumberField.Units.regulator L ∧
      ∀ u ∈ W, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ 4*(Real.log 2/8)*N := by
  let t : ℝ := (Real.log 2/8)*N
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨S,hS,hcard,hbound⟩ := BoundedUnits.exists_many L t ht
  let nm := RelativeNormLog.unitNorm K L
  have him : (S.image nm).card ≤ 2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K) := by
    have hh := TotallyRealUnitCounting.card_le_of_log_bound K (S.image nm) (2*Module.finrank K L*N) (by
      intro u hu i
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have hn := RelativeNormLog.log_bound K L v (2*t) (hbound v hv) i.val
      change |NumberField.Units.logEmbedding K (Additive.ofMul (nm v)) i| ≤ _
      rw [logEmbedding_component,InfinitePlace.mult,if_pos (IsTotallyReal.isReal i.val)]
      simp only [Nat.cast_one,one_mul]
      convert hn using 1; push_cast; dsimp [t]; ring)
    convert hh using 1; congr 3; ring
  obtain ⟨W,hW,hWcard,hWbound⟩ := KernelFiber.exists_large S hS nm (fullLog L) (2*t) hbound
  refine ⟨W,hW,?_,?_⟩
  · have hc : S.card ≤ (2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K))*W.card :=
      hWcard.trans (Nat.mul_le_mul_right W.card him)
    have hr : 0 ≤ NumberField.Units.regulator L := (NumberField.Units.regulator_pos L).le
    exact hcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hr)
  · intro u hu
    refine ⟨(hWbound u hu).1,?_⟩
    intro w
    convert (hWbound u hu).2 w using 1
    · rfl
    · dsimp [t]; ring

end BoundedNormOne
namespace UnitResidues
open NumberField
open scoped Classical BigOperators

variable (L : Type*) [Field L] [NumberField L]

noncomputable def decomp (u : (𝓞 L)ˣ) : NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ℤ) :=
  Classical.choose (NumberField.Units.exist_unique_eq_mul_prod L u).exists

theorem decomp_spec (u : (𝓞 L)ˣ) :
    u = (decomp L u).1 * ∏ i, NumberField.Units.fundSystem L i ^ ((decomp L u).2 i) :=
  Classical.choose_spec (NumberField.Units.exist_unique_eq_mul_prod L u).exists

noncomputable def residue (u : (𝓞 L)ˣ) :
    NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
  ((decomp L u).1,fun i => (decomp L u).2 i)

theorem exists_fifth_root (u v : (𝓞 L)ˣ) (h : residue L u = residue L v) :
    ∃ z : (𝓞 L)ˣ, z^5 = u/v := by
  let a := (decomp L u).2
  let b := (decomp L v).2
  have hζ : (decomp L u).1 = (decomp L v).1 := by
    simpa only [residue] using congrArg Prod.fst h
  have hexp : ∀ i, (5 : ℤ) ∣ a i-b i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    rw [Int.cast_sub,sub_eq_zero]
    exact congrFun (congrArg Prod.snd h) i
  refine ⟨∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5),?_⟩
  calc
    (∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5))^5 =
        ∏ i, NumberField.Units.fundSystem L i ^ (a i-b i) := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_natCast,← zpow_mul]
      congr 1
      exact Int.ediv_mul_cancel (hexp i)
    _ = (∏ i, NumberField.Units.fundSystem L i ^ (a i)) /
        (∏ i, NumberField.Units.fundSystem L i ^ (b i)) := by
      simp only [zpow_sub,Finset.prod_mul_distrib,Finset.prod_inv_distrib,div_eq_mul_inv]
    _ = u/v := by
      conv_rhs => rw [decomp_spec L u,decomp_spec L v,hζ]
      dsimp only [a,b]
      rw [mul_div_mul_comm,div_self',one_mul]

end UnitResidues
open scoped Pointwise
namespace MultiplicativeLogCube

theorem div_card_le {G ι Q : Type*} [CommGroup G] [DecidableEq G] [Fintype Q]
    (U : Finset G) (f : Additive G →+ (ι → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f (Additive.ofMul x) i| ≤ t)
    (q : G → Q) (hroot : ∀ x y, q x = q y → ∃ z, z^5 = x/y) :
    (U/U).card ≤ Fintype.card Q * U.card := by
  classical
  let V : Finset G := U/U
  have hV : ∀ x ∈ V, ∀ i, |f (Additive.ofMul x) i| ≤ 2*t := by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_div.mp hx
    calc
      |f (Additive.ofMul (a/b)) i| = |f (Additive.ofMul a) i-f (Additive.ofMul b) i| := by simp
      _ ≤ |f (Additive.ofMul a) i|+|f (Additive.ofMul b) i| := abs_sub _ _
      _ ≤ t+t := add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t := by ring
  have hf : ∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card := by
    intro c hc
    let T : Finset G := V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩ := Finset.mem_image.mp hc
    have hex : ∀ x ∈ T, ∃ z ∈ U, z^5 = x/x₀ := by
      intro x hx
      obtain ⟨hx,hqx⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩ := hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he : 5 * f (Additive.ofMul z) i = f (Additive.ofMul x) i - f (Additive.ofMul x₀) i := by
        have hh := congrArg (fun w => f (Additive.ofMul w) i) hz
        simpa using hh
      have hb : |f (Additive.ofMul x) i - f (Additive.ofMul x₀) i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g : T → U := fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x : T) : (g x : G)^5 = (x : G)/x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hh := congrArg (fun z : U => (z : G)^5) hxy
      try dsimp only at hh
      rw [hg,hg] at hh
      exact div_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U/U).card ≤ U.card * (V.image q).card := Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card := Nat.mul_comm _ _

end MultiplicativeLogCube
noncomputable instance torsionFintypeInst (L : Type*) [Field L] [NumberField L] :
    Fintype (NumberField.Units.torsion L) := Fintype.ofFinite _
namespace UnitCubeDoubling
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators Pointwise

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]

omit [NumberField K] [NumberField L] in
noncomputable def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w := Real.log (w (u.toMul : L))
  map_zero' := by simp; rfl
  map_add' := by intro u v; simp [Real.log_mul]; rfl

theorem finite_fullLog (t : ℝ) :
    {u : (𝓞 L)ˣ | ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t}.Finite := by
  apply Set.Finite.of_finite_image (f := fun u : (𝓞 L)ˣ => (u : L)) ?_
    (NumberField.Units.coe_injective L).injOn
  apply (Embeddings.finite_of_norm_le L ℂ (Real.exp t)).subset
  rintro _ ⟨u,hu,rfl⟩
  refine ⟨u.val.isIntegral_coe,?_⟩
  intro σ
  have hh := hu (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : L)‖| ≤ t at hh
  have hp : 0 < ‖σ (u : L)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  exact (Real.log_le_iff_le_exp hp).mp ((le_abs_self _).trans hh)

variable [IsTotallyReal K]

theorem pow_five_eq_one (u : (𝓞 K)ˣ) (h : u^5 = 1) : u = 1 := by
  let σ : K →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace K))
  apply NumberField.Units.coe_injective K
  apply σ.injective
  have hh := congrArg (fun u : (𝓞 K)ˣ => σ (u : K)) h
  simp only [NumberField.Units.coe_pow,NumberField.Units.coe_one,map_pow,map_one] at hh ⊢
  exact (Odd.pow_inj (by decide : Odd 5)).mp (by simpa using hh)

theorem exists_cube (N : (𝓞 L)ˣ →* (𝓞 K)ˣ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ U : Finset (𝓞 L)ˣ,
      (∀ u, u ∈ U ↔ N u = 1 ∧ ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t) ∧
      (U/U).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*U.card := by
  let G := N.ker
  have hf : {u : G | ∀ w : InfinitePlace L, |Real.log (w ((u : (𝓞 L)ˣ) : L))| ≤ t}.Finite :=
    (finite_fullLog L t).preimage (Function.Injective.injOn Subtype.val_injective)
  let V : Finset G := hf.toFinset
  have hV (u : G) : u ∈ V ↔ ∀ w : InfinitePlace L, |Real.log (w ((u : (𝓞 L)ˣ) : L))| ≤ t := by
    exact Set.Finite.mem_toFinset hf
  let f : Additive G →+ (InfinitePlace L → ℝ) :=
    (fullLog L).comp N.ker.subtype.toAdditive
  let q : G → NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
    fun u => UnitResidues.residue L (u : (𝓞 L)ˣ)
  have hroot : ∀ x y : G, q x = q y → ∃ z : G, z^5 = x/y := by
    intro x y hxy
    obtain ⟨z,hz⟩ := UnitResidues.exists_fifth_root L (x : (𝓞 L)ˣ) (y : (𝓞 L)ˣ) hxy
    have hnz : N z = 1 := by
      apply pow_five_eq_one K
      rw [← map_pow,hz,map_div,x.property,y.property,div_self']
    exact ⟨⟨z,hnz⟩,Subtype.ext hz⟩
  have hcard := MultiplicativeLogCube.div_card_le V f t ht hV q hroot
  have hc : (V/V).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*V.card := by
    simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hcard
  let U := V.image N.ker.subtype
  refine ⟨U,?_,?_⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      exact ⟨v.property,(hV v).mp hv⟩
    · intro hu
      exact Finset.mem_image.mpr ⟨⟨u,hu.1⟩,(hV _).mpr hu.2,rfl⟩
  · dsimp only [U]
    rw [← Finset.image_div,Finset.card_image_of_injective (f := N.ker.subtype) _ Subtype.val_injective,
      Finset.card_image_of_injective (f := N.ker.subtype) _ Subtype.val_injective]
    exact hc

end UnitCubeDoubling
namespace NumberFieldPacking
open NumberField
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K]

noncomputable def coordinate (i : (K →+* ℂ) × Bool) : 𝓞 K →+ ℝ :=
  (2 : ℕ) • ((if i.2 then Complex.reAddGroupHom else Complex.imAddGroupHom).comp
    ((i.1.comp (algebraMap (𝓞 K) K)).toAddMonoidHom))

private theorem separated (a b : 𝓞 K) (hab : a ≠ b) :
    ∃ i, 1 ≤ |coordinate K i a-coordinate K i b| := by
  obtain ⟨σ,hσ⟩ := NumberField.exists_conjugate_one_le_norm (sub_ne_zero.mpr hab)
  have he := Complex.norm_le_abs_re_add_abs_im (σ ((a-b : 𝓞 K) : K))
  by_cases hr : 1 ≤ 2*|(σ ((a-b : 𝓞 K) : K)).re|
  · refine ⟨(σ,true),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hr
  · have hi : 1 ≤ 2*|(σ ((a-b : 𝓞 K) : K)).im| := by linarith
    refine ⟨(σ,false),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hi

variable [DecidableEq (𝓞 K)]

theorem sumset_card_le (U : Finset (𝓞 K)) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ R) (j : ℕ) :
    (j • U).card ≤ ((4*R+1)*(j+1))^(2*Module.finrank ℚ K) := by
  classical
  have hb : ∀ u ∈ U, ∀ i, |coordinate K i u| ≤ (2*R : ℕ) := by
    intro u hu ⟨σ,b⟩
    cases b
    · have hh := (Complex.abs_im_le_norm (σ (u : K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
    · have hh := (Complex.abs_re_le_norm (σ (u : K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
  have hc := EmbeddingPacking.sumset_card_le U (coordinate K) (2*R) hb (separated K) j
  simpa [Fintype.card_prod,NumberField.Embeddings.card,mul_comm,mul_left_comm,mul_assoc] using hc

theorem image_sumset_card_le (U : Finset (𝓞 K)) (σ₀ : K →+* ℂ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ R) (j : ℕ) :
    (j • U.image (σ₀.comp (algebraMap (𝓞 K) K))).card ≤
      ((4*R+1)*(j+1))^(2*Module.finrank ℚ K) := by
  classical
  rw [← Finset.image_nsmul]
  exact Finset.card_image_le.trans (sumset_card_le K U R hbound j)

end NumberFieldPacking
namespace TorsionCount
open NumberField
open scoped Classical Pointwise

theorem card_le (L : Type*) [Field L] [NumberField L] :
    Fintype.card (NumberField.Units.torsion L) ≤ 10^(2*Module.finrank ℚ L) := by
  let f : NumberField.Units.torsion L → 𝓞 L := fun u => (u : (𝓞 L)ˣ).val
  have hf : Function.Injective f := Units.val_injective.comp Subtype.val_injective
  let U := Finset.univ.image f
  have hU : U.card = Fintype.card (NumberField.Units.torsion L) := by
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ]
  have hb : ∀ u ∈ U, ∀ σ : L →+* ℂ, ‖σ (u : L)‖ ≤ (1 : ℕ) := by
    intro u hu σ
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
    simpa only [f,Nat.cast_one,InfinitePlace.apply] using
      ((NumberField.Units.mem_torsion L).mp v.property (InfinitePlace.mk σ)).le
  have hh := NumberFieldPacking.sumset_card_le L U 1 hb 1
  simpa only [one_nsmul,hU] using hh

end TorsionCount
namespace NormOneArithmetic

theorem lower_count (d r s R B : ℕ) (hd : 0 < d) (hR : 0 < R) (hB : 0 < B)
    (hr : r ≤ d) (hs : s ≤ d) (hgap : 4*s+d ≤ 4*r)
    (A : ℝ) (hA : 0 ≤ A)
    (h : (((864*R*B : ℕ)^4 : ℝ)/48)^r ≤
      2*(9*((864*R*B : ℕ)^4 : ℝ))^s*A*(R : ℝ)^d) :
    (B : ℝ)^d ≤ A := by
  let T := 864*R*B
  let N := T^4
  have hT : 0 < T := by dsimp [T]; positivity
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hsr : s ≤ r := by omega
  have hgap' : d ≤ 4*(r-s) := by omega
  have hm : (N : ℝ)^r ≤ 2*(48 : ℝ)^r*(9*(N : ℝ))^s*A*(R : ℝ)^d := by
    have h' : ((N : ℝ)/48)^r ≤ 2*(9*(N : ℝ))^s*A*(R : ℝ)^d := by
      simpa only [N,T,Nat.cast_pow] using h
    rw [div_pow] at h'
    have hh := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 48) r)).mp h'
    nlinarith only [hh]
  have hc : (N : ℝ)^(r-s) ≤ 2*(48 : ℝ)^r*(9 : ℝ)^s*A*(R : ℝ)^d := by
    apply le_of_mul_le_mul_left ?_ (pow_pos hN s)
    calc
      (N : ℝ)^s * (N : ℝ)^(r-s) = (N : ℝ)^r := by rw [← pow_add,Nat.add_sub_of_le hsr]
      _ ≤ _ := hm
      _ = _ := by rw [mul_pow]; ring
  have h48 : (48 : ℝ)^r ≤ 48^d := pow_le_pow_right₀ (by norm_num) hr
  have h9 : (9 : ℝ)^s ≤ 9^d := pow_le_pow_right₀ (by norm_num) hs
  have hu : (N : ℝ)^(r-s) ≤ 2*(432*(R : ℝ))^d*A := by
    calc
      (N : ℝ)^(r-s) ≤ _ := hc
      _ ≤ 2*(48 : ℝ)^d*9^d*A*(R : ℝ)^d := by gcongr
      _ = _ := by rw [show (432 : ℝ) = 48*9 by norm_num]; simp only [mul_pow]; ring
  have hl : 2*(432*(R : ℝ))^d*(B : ℝ)^d ≤ (N : ℝ)^(r-s) := by
    calc
      2*(432*(R : ℝ))^d*(B : ℝ)^d ≤ (2 : ℝ)^d*(432*(R : ℝ))^d*(B : ℝ)^d := by
        gcongr
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
      _ = ((2 : ℝ)*(432*(R : ℝ))*(B : ℝ))^d := by simp only [mul_pow]
      _ = (T : ℝ)^d := by congr 1; dsimp [T]; push_cast; ring
      _ ≤ (T : ℝ)^(4*(r-s)) := pow_le_pow_right₀ (by exact_mod_cast hT) hgap'
      _ = (N : ℝ)^(r-s) := by dsimp [N]; rw [Nat.cast_pow,pow_mul]
  exact le_of_mul_le_mul_left (hl.trans hu) (by positivity)

end NormOneArithmetic
namespace UnitRankBounds
open NumberField

theorem rank_le_degree (L : Type*) [Field L] [NumberField L] :
    NumberField.Units.rank L ≤ Module.finrank ℚ L := by
  have hh := InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [NumberField.Units.rank,InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

end UnitRankBounds
namespace UniformNormOne
open NumberField
open scoped Classical BigOperators Pointwise

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

theorem exists_many (R B : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L ≤ 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ W : Finset (𝓞 L)ˣ, W.Nonempty ∧ B^(Module.finrank ℚ L) ≤ W.card ∧
      ∀ u ∈ W, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
          4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ) := by
  let N := (864*R*B)^4
  have hN : 0 < N := by dsimp [N]; positivity
  obtain ⟨W,hW,hcard,hbound⟩ := BoundedNormOne.exists_many K L N hN
  refine ⟨W,hW,?_,?_⟩
  · have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
    have hr := UnitRankBounds.rank_le_degree L
    have hs : NumberField.Units.rank K ≤ Module.finrank ℚ L := by omega
    have hh : ((N : ℝ)/48)^(NumberField.Units.rank L) ≤
        2*(9*(N : ℝ))^(NumberField.Units.rank K)*(W.card : ℝ)*(R : ℝ)^(Module.finrank ℚ L) := by
      calc
        ((N : ℝ)/48)^(NumberField.Units.rank L) ≤
            ((Real.log 2/8)*N/3)^(NumberField.Units.rank L) := by
          apply pow_le_pow_left₀ (by positivity)
          have hl : (1 : ℝ)/48 ≤ Real.log 2/24 := by linarith [Real.log_two_gt_d9]
          nlinarith [mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg N)]
        _ ≤ _ := hcard
        _ ≤ _ := by
          have hr0 := (NumberField.Units.regulator_pos L).le
          have hnat : 4*Module.finrank K L*N+1 ≤ 9*N := by nlinarith
          have hb : (4*Module.finrank K L*N+1 : ℕ) ≤ (9*(N : ℝ)) := by exact_mod_cast hnat
          gcongr
    have hc := NormOneArithmetic.lower_count (Module.finrank ℚ L) (NumberField.Units.rank L)
      (NumberField.Units.rank K) R B hd hR hB hr hs hgap (W.card : ℝ) (Nat.cast_nonneg _)
      (by simpa only [N,Nat.cast_pow] using hh)
    exact_mod_cast hc
  · intro u hu
    simpa only [N,Nat.cast_pow] using hbound u hu

theorem exists_cube (R B : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L ≤ 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ U : Finset (𝓞 L)ˣ, U.Nonempty ∧ B^(Module.finrank ℚ L) ≤ U.card ∧
      (U/U).card ≤ 500^(Module.finrank ℚ L)*U.card ∧
      ∀ u ∈ U, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
          4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ) := by
  let t : ℝ := 4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨W,hW,hWcard,hWbound⟩ := exists_many K L R B hR hB hreg hrel hgap
  obtain ⟨U,hU,hcard⟩ := UnitCubeDoubling.exists_cube K L (RelativeNormLog.unitNorm K L) t ht
  have hsub : W ⊆ U := by intro u hu; exact (hU u).mpr (hWbound u hu)
  refine ⟨U,hW.mono hsub,hWcard.trans (Finset.card_le_card hsub),?_,fun u hu => (hU u).mp hu⟩
  have hp : (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L) ≤
      500^(Module.finrank ℚ L) := by
    calc
      _ ≤ 10^(2*Module.finrank ℚ L)*5^(Module.finrank ℚ L) :=
        Nat.mul_le_mul (TorsionCount.card_le L) (Nat.pow_le_pow_right (by norm_num) (UnitRankBounds.rank_le_degree L))
      _ = _ := by rw [pow_mul,← mul_pow]; norm_num
  exact hcard.trans (Nat.mul_le_mul_right _ hp)

end UniformNormOne
namespace QuadraticCircle
open NumberField
open scoped Classical BigOperators ComplexConjugate

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField L] in
theorem norm_eq_one (hdeg : Module.finrank K L = 2) (σ : L →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (x : L) (hx : Algebra.norm K x = 1) :
    ‖σ x‖ = 1 := by
  let φ : K →+* ℂ := σ.comp (algebraMap K L)
  letI : Algebra K ℂ := φ.toAlgebra
  let a : L →ₐ[K] ℂ := { σ with commutes' := fun _ => rfl }
  have hφ : ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b : L →ₐ[K] ℂ := { ComplexEmbedding.conjugate σ with
    commutes' := fun r => DFunLike.congr_fun hφ r }
  have hab : a ≠ b := by
    intro h
    apply hσ
    apply ComplexEmbedding.isReal_iff.mpr
    exact (congrArg AlgHom.toRingHom h).symm
  have hp : ({a,b} : Finset (L →ₐ[K] ℂ)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hab,AlgHom.card,hdeg])
  have he := Algebra.norm_eq_prod_embeddings K ℂ x
  rw [hx,map_one,← hp,Finset.prod_pair hab] at he
  have he' : (1 : ℂ) = σ x * conj (σ x) := he
  have hn := congrArg norm he'
  rw [norm_one,norm_mul,Complex.norm_conj] at hn
  nlinarith [norm_nonneg (σ x)]

end QuadraticCircle
namespace UniformDirections
open NumberField
open scoped Classical Pointwise

def houseBound (R B : ℕ) : ℕ := 2^((864*R*B)^4)

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in
theorem house_bound (R B : ℕ) (u : (𝓞 L)ˣ)
    (hlog : ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
      4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ)) (σ : L →+* ℂ) :
    ‖σ (u : L)‖ ≤ houseBound R B := by
  have hh := hlog (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : L)‖| ≤ _ at hh
  have hp : 0 < ‖σ (u : L)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  apply (Real.log_le_log_iff hp (by dsimp [houseBound]; positivity)).mp
  simp only [houseBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hl : 0 ≤ Real.log 2 := by positivity
  have hN : (0 : ℝ) ≤ (864*R*B : ℕ)^4 := by positivity
  have hm := mul_nonneg hl hN
  nlinarith [le_abs_self (Real.log ‖σ (u : L)‖)]

theorem exists_directions (R : ℕ) (hR : 0 < R)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L = 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L)
    (σ : L →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ V : Finset ℂ,
      (∀ v ∈ V, ‖v‖ = 1) ∧
      (16*500)^(2*Module.finrank ℚ L) ≤ V.card ∧
      (V/V).card ≤ 500^(2*Module.finrank ℚ L)*V.card ∧
      ∀ j : ℕ, (j • V).card ≤ ((4*houseBound R ((16*500)^2)+1)*(j+1))^(2*Module.finrank ℚ L) := by
  let B := (16*500)^2
  obtain ⟨U,hU,hcard,hdiv,hbound⟩ := UniformNormOne.exists_cube K L R B hR (by norm_num [B]) hreg hrel.le hgap
  let f : (𝓞 L)ˣ →* ℂ := (Units.coeHom ℂ).comp (NumberField.Units.complexEmbedding σ)
  have hf : Function.Injective f := σ.injective.comp (NumberField.Units.coe_injective L)
  let V := U.image f
  have hVcard : V.card = U.card := Finset.card_image_of_injective _ hf
  refine ⟨V,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    apply QuadraticCircle.norm_eq_one K L hrel σ hσ
    have hh := congrArg (fun u : (𝓞 K)ˣ => (u : K)) (hbound u hu).1
    exact hh
  · rw [hVcard]
    simpa only [B,pow_mul] using hcard
  · dsimp only [V]
    rw [← Finset.image_div,Finset.card_image_of_injective (f := f) _ hf,
      Finset.card_image_of_injective (f := f) _ hf]
    exact hdiv.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro j
    let A : Finset (𝓞 L) := U.image Units.val
    have hA : ∀ u ∈ A, ∀ τ : L →+* ℂ, ‖τ (u : L)‖ ≤ houseBound R B := by
      intro u hu τ
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      exact house_bound L R B a (hbound a ha).2 τ
    have he : A.image (σ.comp (algebraMap (𝓞 L) L)) = V := by
      rw [Finset.image_image]
      rfl
    rw [← he]
    exact NumberFieldPacking.image_sumset_card_le L A σ (houseBound R B) hA j

end UniformDirections
namespace ProductCounting
open scoped BigOperators

theorem card_le {ι : Type*} [Fintype ι] (S : Finset (ι → ℕ)) (B : ℕ)
    (hpos : ∀ x ∈ S, ∀ i, 0 < x i) (hprod : ∀ x ∈ S, ∏ i, x i ≤ B) :
    S.card ≤ 2^(Fintype.card ι) * B^2 := by
  classical
  let box : Finset (ι → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 B)
  let w : (ι → ℕ) → ℝ := fun x => ∏ i, ((x i : ℝ)^2)⁻¹
  have hs : S ⊆ box := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_Icc.mpr ⟨hpos x hx i,?_⟩
    have hp : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hpos x hx i)
    exact (Nat.le_of_dvd hp (Finset.dvd_prod_of_mem x (Finset.mem_univ i))).trans (hprod x hx)
  have hw (x : ι → ℕ) (hx : x ∈ S) : 1 ≤ (B : ℝ)^2*w x := by
    have hp : (0 : ℝ) < ∏ i, (x i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hpos x hx i)
    have hle : (∏ i, (x i : ℝ)) ≤ B := by exact_mod_cast hprod x hx
    dsimp only [w]
    rw [Finset.prod_inv_distrib,Finset.prod_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr (by nlinarith)
  have hsum : (∑ n ∈ Finset.Icc 1 B, ((n : ℝ)^2)⁻¹) ≤ 2 := by
    have hset : Finset.Icc 1 B = Finset.Ioo 0 (B+1) := by ext n; simp; omega
    simpa [hset] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (B+1))
  have hweight : ∑ x ∈ box, w x ≤ (2 : ℝ)^(Fintype.card ι) := by
    dsimp only [box,w]
    rw [Finset.sum_prod_piFinset (Finset.Icc 1 B) (fun (_ : ι) n => ((n : ℝ)^2)⁻¹)]
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod (s := (Finset.univ : Finset ι))
        (f := fun _ => ∑ n ∈ Finset.Icc 1 B, ((n : ℝ)^2)⁻¹) (g := fun _ => (2 : ℝ))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (fun _ _ => hsum)
  have hreal : (S.card : ℝ) ≤ (2 : ℝ)^(Fintype.card ι)*(B : ℝ)^2 := by
    calc
      (S.card : ℝ) = ∑ _x ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ S, (B : ℝ)^2*w x := Finset.sum_le_sum (fun x hx => hw x hx)
      _ = (B : ℝ)^2 * ∑ x ∈ S, w x := (Finset.mul_sum _ _ _).symm
      _ ≤ (B : ℝ)^2 * ∑ x ∈ box, w x := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by dsimp [w]; positivity)) (sq_nonneg _)
      _ ≤ (B : ℝ)^2 * (2 : ℝ)^(Fintype.card ι) := mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
      _ = _ := mul_comm _ _
  exact_mod_cast hreal

end ProductCounting
open scoped BigOperators
namespace PrimeMultiset

noncomputable def encode {ι : Type*} (s : Multiset (ℕ × ι)) (i : ι) : ℕ := by
  classical
  exact ((s.filter (fun a => a.2 = i)).map Prod.fst).prod

private theorem count_color {ι : Type*} [DecidableEq ι] (s : Multiset (ℕ × ι)) (a : ℕ × ι) :
    Multiset.count a.1 ((s.filter (fun x => x.2 = a.2)).map Prod.fst) = Multiset.count a s := by
  rw [Multiset.count_map,Multiset.filter_filter,Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro x _
  constructor
  · rintro ⟨h₁,h₂⟩
    exact Prod.ext h₁ h₂.symm
  · intro h
    subst x
    simp

theorem encode_injective {ι : Type*} (s t : Multiset (ℕ × ι))
    (hs : ∀ a ∈ s, a.1.Prime) (ht : ∀ a ∈ t, a.1.Prime)
    (he : encode s = encode t) : s = t := by
  classical
  have hn (v : Multiset (ℕ × ι)) (hv : ∀ a ∈ v, a.1.Prime) (i : ι) :
      UniqueFactorizationMonoid.normalizedFactors (encode v i) =
        ((v.filter (fun a => a.2 = i)).map Prod.fst) := by
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hp
    exact Nat.prime_iff.mp (hv a (Multiset.mem_filter.mp ha).1)
  apply Multiset.ext.mpr
  intro a
  have hh := congrArg UniqueFactorizationMonoid.normalizedFactors (congrFun he a.2)
  rw [hn s hs,hn t ht] at hh
  have hc := congrArg (Multiset.count a.1) hh
  rw [count_color s a,count_color t a] at hc
  exact hc

theorem prod_encode {ι : Type*} [Fintype ι] (s : Multiset (ℕ × ι)) :
    (∏ i, encode s i) = (s.map Prod.fst).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [encode]
  | @cons a s ih =>
    have hc (i : ι) : encode (a ::ₘ s) i = (if a.2 = i then a.1 else 1)*encode s i := by
      by_cases h : a.2 = i <;> simp [encode,h]
    simp_rw [hc]
    rw [Finset.prod_mul_distrib,ih]
    simp

theorem encode_pos {ι : Type*} (s : Multiset (ℕ × ι))
    (hs : ∀ a ∈ s, a.1.Prime) (i : ι) : 0 < encode s i := by
  classical
  apply Multiset.prod_pos
  intro p hp
  obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hp
  exact (hs a (Multiset.mem_filter.mp ha).1).pos

end PrimeMultiset
namespace NormedFactorCounting
open UniqueFactorizationMonoid
open scoped BigOperators

variable {α ι : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [NormalizationMonoid α] [Subsingleton αˣ]

noncomputable def primeFactors (a : α) : Multiset {p : α // Prime p} :=
  (normalizedFactors a).pmap (fun p hp => ⟨p,hp⟩) (fun p hp => prime_of_normalized_factor p hp)

omit [Subsingleton αˣ] in
private theorem map_primeFactors (a : α) :
    (primeFactors a).map Subtype.val = normalizedFactors a := by
  rw [primeFactors,Multiset.map_pmap,Multiset.pmap_eq_map]
  exact Multiset.map_id _

private theorem prod_primeFactors (a : α) (ha : a ≠ 0) :
    ((primeFactors a).map Subtype.val).prod = a := by
  rw [map_primeFactors]
  simpa only [associated_eq_eq] using prod_normalizedFactors ha

noncomputable def encode (c : {p : α // Prime p} → ℕ × ι) (a : α) : ι → ℕ :=
  PrimeMultiset.encode ((primeFactors a).map c)

theorem encode_injective (c : {p : α // Prime p} → ℕ × ι)
    (hc : Function.Injective c) (hp : ∀ p, (c p).1.Prime)
    {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (he : encode c a = encode c b) : a = b := by
  have hprime (x : α) : ∀ p ∈ (primeFactors x).map c, p.1.Prime := by
    intro p hpm
    obtain ⟨q,_,rfl⟩ := Multiset.mem_map.mp hpm
    exact hp q
  have hf := PrimeMultiset.encode_injective _ _ (hprime a) (hprime b) he
  have hpf := Multiset.map_injective hc hf
  have hn := congrArg (fun s : Multiset {p : α // Prime p} => (s.map Subtype.val).prod) hpf
  simpa only [prod_primeFactors a ha,prod_primeFactors b hb] using hn

theorem prod_encode_le [Fintype ι] (N : α →*₀ ℕ)
    (c : {p : α // Prime p} → ℕ × ι) (hN : ∀ p, (c p).1 ≤ N p.val)
    (a : α) (ha : a ≠ 0) : (∏ i, encode c a i) ≤ N a := by
  rw [encode,PrimeMultiset.prod_encode,Multiset.map_map]
  calc
    _ ≤ ((primeFactors a).map (fun p => N p.val)).prod :=
      Multiset.prod_map_le_prod_map _ _ (fun p _ => hN p)
    _ = N (((primeFactors a).map Subtype.val).prod) := by
      rw [← Multiset.prod_hom _ N,Multiset.map_map]
      rfl
    _ = N a := by rw [prod_primeFactors a ha]

theorem card_le [Fintype ι] (N : α →*₀ ℕ)
    (c : {p : α // Prime p} → ℕ × ι) (hc : Function.Injective c)
    (hp : ∀ p, (c p).1.Prime) (hN : ∀ p, (c p).1 ≤ N p.val)
    (S : Finset α) (B : ℕ) (hzero : ∀ a ∈ S, a ≠ 0) (hbound : ∀ a ∈ S, N a ≤ B) :
    S.card ≤ 2^(Fintype.card ι)*B^2 := by
  classical
  have he : (S.image (encode c)).card = S.card := Finset.card_image_iff.mpr (by
    intro a ha b hb hab
    exact encode_injective c hc hp (hzero a ha) (hzero b hb) hab)
  rw [← he]
  apply ProductCounting.card_le
  · intro x hx i
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    apply PrimeMultiset.encode_pos
    intro q hq
    obtain ⟨p,_,rfl⟩ := Multiset.mem_map.mp hq
    exact hp p
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact (prod_encode_le N c hN a (hzero a ha)).trans (hbound a ha)

end NormedFactorCounting
namespace IdealCounting
open NumberField
open scoped BigOperators

variable (K : Type*) [Field K] [NumberField K]

private abbrev PrimeIdeals := {P : Ideal (𝓞 K) // Prime P}

private def base (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p.val : ℤ)}

private theorem base_ne_bot (p : Nat.Primes) : base p ≠ ⊥ := by
  intro h
  have hp : (p.val : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
  exact p.property.ne_zero (by exact_mod_cast hp)

private instance base_maximal (p : Nat.Primes) : (base p).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast p.property.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp p.property)).isMaximal (base_ne_bot p)

private noncomputable def primeUnder (P : PrimeIdeals K) : Nat.Primes := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  letI : NeZero P.val := ⟨P.property.ne_zero⟩
  exact ⟨Ideal.absNorm (Ideal.under ℤ P.val),Nat.absNorm_under_prime P.val⟩

private theorem mem_fiber (P : PrimeIdeals K) :
    P.val ∈ primesOverFinset (base (primeUnder K P)) (𝓞 K) := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  have he : base (primeUnder K P) = Ideal.under ℤ P.val := Int.ideal_span_absNorm_eq_self _
  letI : P.val.LiesOver (base (primeUnder K P)) := by rw [he]; infer_instance
  exact (mem_primesOverFinset_iff (base_ne_bot _) _).mpr ⟨inferInstance,inferInstance⟩

private noncomputable def slot (p : Nat.Primes) :
    (primesOverFinset (base p) (𝓞 K)) ↪ Fin (Module.finrank ℚ K) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  change Fintype.card ↥(primesOverFinset (base p) (𝓞 K)) ≤ Fintype.card (Fin (Module.finrank ℚ K))
  rw [Fintype.card_coe,Fintype.card_fin]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (base_ne_bot p)

private noncomputable def toSigma : PrimeIdeals K ↪
    (Σ p : Nat.Primes, (primesOverFinset (base p) (𝓞 K))) where
  toFun P := ⟨primeUnder K P,⟨P.val,mem_fiber K P⟩⟩
  inj' := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun x => x.2.val) h

private noncomputable def code : PrimeIdeals K ↪ ℕ × Fin (Module.finrank ℚ K) :=
  (toSigma K).trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl Nat.Primes) (slot K)).trans
      ((Equiv.sigmaEquivProd Nat.Primes (Fin (Module.finrank ℚ K))).toEmbedding.trans
        (Function.Embedding.prodMap ⟨Subtype.val,Subtype.val_injective⟩ (Function.Embedding.refl _))))

private theorem code_prime (P : PrimeIdeals K) : ((code K) P).1.Prime :=
  (primeUnder K P).property

private theorem code_le_norm (P : PrimeIdeals K) : ((code K) P).1 ≤ Ideal.absNorm P.val := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  letI : NeZero P.val := ⟨P.property.ne_zero⟩
  have hp : (Ideal.under ℤ P.val).IsPrime := inferInstance
  have hp0 : Ideal.under ℤ P.val ≠ ⊥ := by
    intro h
    have hh := Nat.absNorm_under_prime P.val
    rw [h] at hh
    exact Nat.not_prime_zero (by simpa using hh)
  letI : (Ideal.under ℤ P.val).IsMaximal := hp.isMaximal hp0
  change Ideal.absNorm (Ideal.under ℤ P.val) ≤ _
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P.val (Ideal.under ℤ P.val) hp hp0]
  exact Nat.le_self_pow (Ideal.inertiaDeg_ne_zero (Ideal.under ℤ P.val) P.val) _

theorem card_le (S : Finset (Ideal (𝓞 K))) (B : ℕ)
    (hzero : ∀ I ∈ S, I ≠ ⊥) (hbound : ∀ I ∈ S, Ideal.absNorm I ≤ B) :
    S.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
  classical
  simpa using NormedFactorCounting.card_le Ideal.absNorm (code K) (code K).injective
    (code_prime K) (code_le_norm K) S B hzero hbound

end IdealCounting
open MeasureTheory
open scoped ENNReal BigOperators
namespace SimplexVolume

def simplex {ι : Type*} [Fintype ι] (a : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, -a ≤ x i) ∧ ∑ i, x i ≤ a}

theorem l1_bound {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ) (ha : 0 ≤ a)
    (x : ι → ℝ) (hx : x ∈ simplex a) :
    ∑ i, |x i| ≤ 3*(Fintype.card ι)*a := by
  classical
  have hp (i : ι) : |x i| ≤ x i+2*a := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1 i]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc' := mul_le_mul_of_nonneg_right hc ha
  linarith [hx.2]

theorem volume_le {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ) (ha : 0 ≤ a) :
    volume (simplex (ι := ι) a) ≤ ENNReal.ofReal ((18*a)^(Fintype.card ι)) := by
  classical
  let r := Fintype.card ι
  have hs : simplex (ι := ι) a ⊆ {x : ι → ℝ | ∑ i, |x i| ≤ 3*r*a} :=
    fun x hx => l1_bound a ha x hx
  have hv : volume {x : ι → ℝ | ∑ i, |x i| ≤ 3*r*a} =
      ENNReal.ofReal ((3*r*a)^r * (2^r / r.factorial)) := by
    have h := volume_sum_rpow_le ι (p := 1) le_rfl (3*r*a)
    simp only [Real.rpow_one,div_one,one_add_one_eq_two,Real.Gamma_two,mul_one,
      Real.Gamma_nat_eq_factorial] at h
    rw [h,← ENNReal.ofReal_pow (by positivity : 0 ≤ 3*(r : ℝ)*a),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3*(r : ℝ)*a)^r)]
  have he : (r : ℝ)^r / r.factorial ≤ (3 : ℝ)^r := by
    have h := Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg _) r
    have he' : Real.exp (r : ℝ) = (Real.exp 1)^r := by simpa only [mul_one] using Real.exp_nat_mul 1 r
    rw [he'] at h
    exact h.trans (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans (by norm_num)) r)
  have hb : (3*(r : ℝ)*a)^r * (2^r / r.factorial) ≤ (18*a)^r := by
    calc
      _ = (6*a)^r * ((r : ℝ)^r / r.factorial) := by rw [show (6 : ℝ) = 3*2 by norm_num]; simp only [mul_pow]; ring
      _ ≤ (6*a)^r * (3 : ℝ)^r := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  exact (measure_mono hs).trans (hv ▸ ENNReal.ofReal_le_ofReal hb)

end SimplexVolume
namespace LatticeCovering
open MeasureTheory
open scoped ENNReal Pointwise

theorem measure_fundamental_le {G E : Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ : Measure E) [VAddInvariantMeasure G E μ]
    (F S : Set E) (hF : IsAddFundamentalDomain G F μ)
    (hcover : ∀ x : E, ∃ g : G, g +ᵥ x ∈ S) : μ F ≤ μ S := by
  have hsub : F ⊆ ⋃ g : G, (g +ᵥ S) ∩ F := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x
    refine Set.mem_iUnion.mpr ⟨-g,?_,hx⟩
    exact ⟨g +ᵥ x,hg,neg_vadd_vadd g x⟩
  calc
    μ F ≤ μ (⋃ g : G, (g +ᵥ S) ∩ F) := measure_mono hsub
    _ ≤ ∑' g : G, μ ((g +ᵥ S) ∩ F) := measure_iUnion_le _
    _ = μ S := (hF.measure_eq_tsum S).symm

theorem covolume_le_of_simplex_cover {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (T : Finset (ι → ℝ)) (a : ℝ) (ha : 0 ≤ a)
    (hcover : ∀ x : ι → ℝ, ∃ g : L, ∃ t ∈ T,
      (g : ι → ℝ)+x-t ∈ SimplexVolume.simplex a) :
    ZLattice.covolume L ≤ T.card * (18*a)^(Fintype.card ι) := by
  classical
  letI : MeasurableVAdd L (ι → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  let S : Set (ι → ℝ) := ⋃ t : T, t.val +ᵥ SimplexVolume.simplex a
  have hs : ∀ x : ι → ℝ, ∃ g : L, g +ᵥ x ∈ S := by
    intro x
    obtain ⟨g,t,ht,hmem⟩ := hcover x
    refine ⟨g,Set.mem_iUnion.mpr ⟨⟨t,ht⟩,?_⟩⟩
    refine ⟨(g : ι → ℝ)+x-t,hmem,?_⟩
    change t+((g : ι → ℝ)+x-t) = (g : ι → ℝ)+x
    abel
  have hS : volume S ≤ (T.card : ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)) := by
    calc
      volume S ≤ ∑' t : T, volume (t.val +ᵥ SimplexVolume.simplex a) := measure_iUnion_le _
      _ = (T.card : ℝ≥0∞)*volume (SimplexVolume.simplex (ι := ι) a) := by simp [tsum_fintype]
      _ ≤ _ := mul_le_mul_right (SimplexVolume.volume_le a ha) _
  have h := (measure_fundamental_le volume F S hF hs).trans hS
  have hr := ENNReal.toReal_mono (by finiteness :
    (T.card : ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)) ≠ ⊤) h
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at hr
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hr

end LatticeCovering
namespace MinkowskiLogCover
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def extend (x : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ i, x i else x ⟨w,h⟩

private theorem extend_sum (x : logSpace K) : ∑ w, extend K x w = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have hs : (∑ i : {w : InfinitePlace K // w ≠ w₀}, extend K x i.val) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dif_neg i.property
  rw [hs]
  simp [extend]

private noncomputable def radii (t : ℝ) (x : logSpace K) (w : InfinitePlace K) : ℝ≥0 :=
  ⟨Real.exp (t+extend K x w/(mult w : ℝ)),(Real.exp_pos _).le⟩

private theorem radii_prod (t : ℝ) (x : logSpace K) :
    (∏ w : InfinitePlace K, (radii K t x w : ℝ≥0∞)^(mult w)) =
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)) := by
  classical
  have hreal : ((∏ w : InfinitePlace K, (radii K t x w)^(mult w) : ℝ≥0) : ℝ) =
      Real.exp ((Module.finrank ℚ K : ℝ)*t) := by
    have hr (w : InfinitePlace K) : ((radii K t x w : ℝ≥0) : ℝ) = Real.exp (t+extend K x w/(mult w : ℝ)) := rfl
    simp only [NNReal.coe_prod,NNReal.coe_pow,hr,← Real.exp_nat_mul]
    rw [← Real.exp_sum]
    congr 1
    have he (w : InfinitePlace K) : (mult w : ℝ)*(t+extend K x w/(mult w : ℝ)) =
        (mult w : ℝ)*t+extend K x w := by
      have hm : (mult w : ℝ) ≠ 0 := mult_coe_ne_zero
      field_simp
    simp_rw [he]
    rw [Finset.sum_add_distrib,extend_sum,add_zero,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hnn : (∏ w : InfinitePlace K, (radii K t x w)^(mult w) : ℝ≥0) =
      ⟨Real.exp ((Module.finrank ℚ K : ℝ)*t),(Real.exp_pos _).le⟩ := NNReal.eq hreal
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_finset_prod,hnn,ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
  rfl

theorem exists_integer (t : ℝ)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (x : logSpace K) : ∃ a : 𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a : K)) ≤ Real.exp ((Module.finrank ℚ K : ℝ)*t) ∧
      ∀ w : InfinitePlace K, (mult w : ℝ)*Real.log (w (a : K)) ≤
        extend K x w+(mult w : ℝ)*t := by
  classical
  obtain ⟨a,ha,hab⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := radii K t x)
    (by rw [convexBodyLT_volume,ENNReal.coe_finset_prod]; simp_rw [ENNReal.coe_pow]; rw [radii_prod]; exact hM)
  refine ⟨a,ha,?_,?_⟩
  · rw [mixedEmbedding.norm_apply]
    have hh : (∏ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (a : K))^(mult w)) ≤
        ∏ w : InfinitePlace K, (radii K t x w : ℝ)^(mult w) := by
      apply Finset.prod_le_prod
      · intro w _; exact pow_nonneg (normAtPlace_nonneg _ _) _
      · intro w _
        rw [normAtPlace_apply]
        exact pow_le_pow_left₀ (apply_nonneg w _) (hab w).le _
    apply hh.trans_eq
    have hp := congrArg ENNReal.toReal (radii_prod K t x)
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hp
  · intro w
    have hp : 0 < w (a : K) := pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha)
    have hl : Real.log (w (a : K)) < t+extend K x w/(mult w : ℝ) :=
      (Real.log_lt_iff_lt_exp hp).mpr (hab w)
    have hm : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have he := mul_le_mul_of_nonneg_left hl.le hm
    have hn : (mult w : ℝ) ≠ 0 := mult_coe_ne_zero
    refine he.trans (le_of_eq ?_)
    first | (field_simp; ring) | field_simp | ring | (rw [mul_add, mul_div_cancel₀ _ hn, add_comm])

end MinkowskiLogCover
namespace MinkowskiLogCover
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def fullLog (a : K) (w : InfinitePlace K) : ℝ :=
  (mult w : ℝ)*(Real.log (w a)-Real.log (mixedEmbedding.norm (mixedEmbedding K a))/(Module.finrank ℚ K : ℝ))

private theorem logMap_eq_fullLog (a : K) (i : {w : InfinitePlace K // w ≠ w₀}) :
    logMap (mixedEmbedding K a) i = fullLog K a i.val := by
  simp [logMap_apply,fullLog,div_eq_mul_inv]

private theorem fullLog_sum (a : K) (ha : a ≠ 0) : ∑ w, fullLog K a w = 0 := by
  have hs : Real.log (mixedEmbedding.norm (mixedEmbedding K a)) =
      ∑ w : InfinitePlace K, (mult w : ℝ)*Real.log (w a) := by
    rw [mixedEmbedding.norm_apply,Real.log_prod]
    · simp [normAtPlace_apply,Real.log_pow]
    · intro w _
      rw [normAtPlace_apply]
      exact pow_ne_zero _ ((pos_iff.mpr ha).ne')
  simp only [fullLog,mul_sub,Finset.sum_sub_distrib]
  rw [← hs,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  field_simp
  ring

private theorem integer_norm_ge_one (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (a : K)) := by
  rw [norm_eq_norm,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

theorem exists_approximation (t : ℝ) (ht : 0 ≤ t)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (x : logSpace K) : ∃ a : 𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a : K)) ≤ Real.exp ((Module.finrank ℚ K : ℝ)*t) ∧
      x-logMap (mixedEmbedding K (a : K)) ∈ SimplexVolume.simplex (2*t) := by
  obtain ⟨a,ha,hanorm,hbound⟩ := exists_integer K t hM x
  have hN : 0 ≤ Real.log (mixedEmbedding.norm (mixedEmbedding K (a : K))) :=
    Real.log_nonneg (integer_norm_ge_one K a ha)
  have hfull : ∀ w : InfinitePlace K, fullLog K (a : K) w ≤ extend K x w+2*t := by
    intro w
    have hm : (mult w : ℝ) ≤ 2 := by simp only [mult]; split_ifs <;> norm_num
    have hm0 : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
    have hn := mul_nonneg hm0 (div_nonneg hN hd)
    have hb := hbound w
    have hc := mul_le_mul_of_nonneg_right hm ht
    dsimp only [fullLog]
    nlinarith
  let δ : InfinitePlace K → ℝ := fun w => extend K x w-fullLog K (a : K) w
  have hid (i : {w : InfinitePlace K // w ≠ w₀}) :
      (x-logMap (mixedEmbedding K (a : K))) i = δ i.val := by
    rw [Pi.sub_apply,logMap_eq_fullLog]
    dsimp only [δ,extend]
    rw [dif_neg i.property]
  have hsum : δ w₀ + ∑ i : {w : InfinitePlace K // w ≠ w₀}, δ i.val = 0 := by
    rw [← Fintype.sum_eq_add_sum_subtype_ne δ w₀]
    dsimp only [δ]
    rw [Finset.sum_sub_distrib,extend_sum,fullLog_sum K (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha)]
    simp
  refine ⟨a,ha,hanorm,?_,?_⟩
  · intro i
    rw [hid]
    dsimp only [δ]
    linarith [hfull i.val]
  · simp_rw [hid]
    have hh := hfull w₀
    dsimp only [δ] at hsum ⊢
    linarith

end MinkowskiLogCover
namespace RegulatorUpper
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem norm_span_eq (a : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {a}) : ℝ) = mixedEmbedding.norm (mixedEmbedding K (a : K)) := by
  rw [Ideal.absNorm_span_singleton,norm_eq_norm,← Algebra.coe_norm_int]
  simp

theorem regulator_upper_bound_of_minkowski (t : ℝ) (ht : 0 ≤ t) (B : ℕ)
    (hrank : 0 < NumberField.Units.rank K)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (hB : Real.exp ((Module.finrank ℚ K : ℝ)*t) ≤ (B : ℝ)) :
    NumberField.Units.regulator K ≤
      (2 : ℝ)^(Module.finrank ℚ K)*(B : ℝ)^2*(36*t)^(NumberField.Units.rank K) := by
  classical
  let Iset : Finset (Ideal (𝓞 K)) := ((Ideal.finite_setOf_absNorm_le B).toFinset).filter
    (fun I => ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I)
  have hgen : ∀ I : Iset, ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I.val :=
    fun I => (Finset.mem_filter.mp I.property).2
  choose gen hgen0 hgenspan using hgen
  let T : Finset (logSpace K) := Iset.attach.image
    (fun I => logMap (mixedEmbedding K (gen I : K)))
  have hIcard : Iset.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
    apply IdealCounting.card_le
    · intro I hI
      obtain ⟨a,ha,rfl⟩ := (Finset.mem_filter.mp hI).2
      exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
    · intro I hI
      simpa using (Finset.mem_filter.mp hI).1
  have hTcard : T.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
    exact (Finset.card_image_le.trans_eq Finset.card_attach).trans hIcard
  have hcover : ∀ x : logSpace K, ∃ g : NumberField.Units.unitLattice K, ∃ z ∈ T,
      (g : logSpace K)+x-z ∈ SimplexVolume.simplex (2*t) := by
    intro x
    obtain ⟨a,ha,hanorm,haapprox⟩ := MinkowskiLogCover.exists_approximation K t ht hM x
    have hI : Ideal.span {a} ∈ Iset := by
      apply Finset.mem_filter.mpr
      refine ⟨(Set.Finite.mem_toFinset _).mpr ?_,a,ha,rfl⟩
      change Ideal.absNorm (Ideal.span {a}) ≤ B
      exact_mod_cast (show (Ideal.absNorm (Ideal.span {a}) : ℝ) ≤ B by
        rw [norm_span_eq]; exact hanorm.trans hB)
    let I : Iset := ⟨Ideal.span {a},hI⟩
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hgenspan I)
    have hmul : mixedEmbedding K (a : K) =
        mixedEmbedding K (u : K)*mixedEmbedding K (gen I : K) := by
      rw [← map_mul]
      congr 1
      have hh := congrArg (algebraMap (𝓞 K) K) hu
      simpa only [map_mul,mul_comm] using hh.symm
    have hn := MinkowskiLogCover.integer_norm_ge_one K (gen I) (hgen0 I)
    have hlog : logMap (mixedEmbedding K (a : K)) =
        NumberField.Units.logEmbedding K (Additive.ofMul u)+logMap (mixedEmbedding K (gen I : K)) := by
      rw [hmul,logMap_mul (by rw [norm_unit]; norm_num) ((lt_of_lt_of_le zero_lt_one hn).ne'),
        logMap_eq_logEmbedding]
    let lu : NumberField.Units.unitLattice K :=
      ⟨NumberField.Units.logEmbedding K (Additive.ofMul u),
        Submodule.mem_map.mpr ⟨Additive.ofMul u,Submodule.mem_top,rfl⟩⟩
    refine ⟨-lu,logMap (mixedEmbedding K (gen I : K)),?_,?_⟩
    · exact Finset.mem_image.mpr ⟨I,Finset.mem_attach _ _,rfl⟩
    · rw [hlog] at haapprox
      convert haapprox using 1
      change -(NumberField.Units.logEmbedding K (Additive.ofMul u))+x-
        logMap (mixedEmbedding K (gen I : K)) = _
      abel
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  letI : Nonempty {w : InfinitePlace K // w ≠ w₀} := Fintype.card_pos_iff.mp (hcard.symm ▸ hrank)
  have hc := LatticeCovering.covolume_le_of_simplex_cover (NumberField.Units.unitLattice K)
    T (2*t) (by positivity) hcover
  have hh : (T.card : ℝ) ≤ (2 : ℝ)^(Module.finrank ℚ K)*(B : ℝ)^2 := by exact_mod_cast hTcard
  apply hc.trans
  rw [hcard,show 18*(2*t) = 36*t by ring]
  exact mul_le_mul_of_nonneg_right hh (by positivity)

private theorem minkowskiBound_le (R : ℕ) (hR : 0 < R)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    minkowskiBound K 1 ≤ (2*(R : ℝ≥0∞))^(Module.finrank ℚ K) := by
  have hsqrt : (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞) ≤ (R : ℝ≥0∞)^(Module.finrank ℚ K) := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hh : Real.sqrt |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(Module.finrank ℚ K) :=
      Real.sqrt_le_iff.mpr ⟨by positivity,by simpa only [← pow_mul,mul_comm 2] using hD⟩
    simpa [Real.coe_sqrt,Int.norm_eq_abs] using hh
  rw [minkowskiBound,volume_fundamentalDomain_fractionalIdealLatticeBasis,
    volume_fundamentalDomain_latticeBasis,mixedEmbedding.finrank]
  simp only [Units.val_one,FractionalIdeal.absNorm_one,Rat.cast_one,ENNReal.ofReal_one,one_mul]
  have hi : (2⁻¹ : ℝ≥0∞)^(nrComplexPlaces K) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  calc
    _ ≤ (1*(R : ℝ≥0∞)^(Module.finrank ℚ K))*2^(Module.finrank ℚ K) := by gcongr
    _ = _ := by rw [one_mul,mul_pow,mul_comm]

theorem regulator_upper_bound_of_discriminant (R : ℕ) (hR : 0 < R)
    (hrank : 0 < NumberField.Units.rank K)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hT : (0 : ℝ) < 4*R := by positivity
  have hT1 : (1 : ℝ) ≤ 4*R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have ht : 0 ≤ Real.log (4*R : ℝ) := Real.log_nonneg hT1
  have hexp : Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ)) = (4*R : ℝ)^(Module.finrank ℚ K) := by
    rw [Real.exp_nat_mul,Real.exp_log hT]
  have hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ))) := by
    rw [hexp]
    have hpow : (2*(R : ℝ))^(Module.finrank ℚ K) < (4*(R : ℝ))^(Module.finrank ℚ K) :=
      pow_lt_pow_left₀ (by linarith) (by positivity) Module.finrank_pos.ne'
    have hpow' : (2*(R : ℝ≥0∞))^(Module.finrank ℚ K) < ENNReal.ofReal ((4*R : ℝ)^(Module.finrank ℚ K)) := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*R : ℝ)^(Module.finrank ℚ K))] using hpow
    have hfac : (1 : ℝ≥0∞) ≤ convexBodyLTFactor K := by exact_mod_cast one_le_convexBodyLTFactor K
    exact (minkowskiBound_le K R hR hD).trans_lt (hpow'.trans_le (le_mul_of_one_le_left (by positivity) hfac))
  have hB : Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ)) ≤ ((4*R)^(Module.finrank ℚ K) : ℕ) := by
    rw [hexp]
    push_cast
    rfl
  have h := regulator_upper_bound_of_minkowski K (Real.log (4*R : ℝ)) ht
    ((4*R)^(Module.finrank ℚ K)) hrank hM hB
  have hrankle : NumberField.Units.rank K ≤ Module.finrank ℚ K := by
    have hc := card_add_two_mul_card_eq_rank K
    simp only [NumberField.Units.rank,card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hlog : 36*Real.log (4*R : ℝ) ≤ 144*R := by linarith [Real.log_le_sub_one_of_pos hT]
  have hbase : (1 : ℝ) ≤ 144*R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hfactor : (36*Real.log (4*R : ℝ))^(NumberField.Units.rank K) ≤
      (144*R : ℝ)^(Module.finrank ℚ K) :=
    (pow_le_pow_left₀ (by positivity) hlog _).trans (pow_le_pow_right₀ hbase hrankle)
  apply h.trans
  push_cast
  calc
    _ ≤ (2 : ℝ)^(Module.finrank ℚ K)*((4*R : ℝ)^(Module.finrank ℚ K))^2*
        (144*R : ℝ)^(Module.finrank ℚ K) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
      rw [pow_right_comm,← mul_pow,← mul_pow]
      congr 1
      ring

theorem regulator_upper_bound (R : ℕ) (hR : 0 < R)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
  by_cases hr : NumberField.Units.rank K = 0
  · have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = 0 := by
      simpa [hr] using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
    letI : IsEmpty {w : InfinitePlace K // w ≠ w₀} := Fintype.card_eq_zero_iff.mp hcard
    have hreg : NumberField.Units.regulator K = 1 := by
      unfold NumberField.Units.regulator
      rw [ZLattice.covolume_eq_det _ (IsZLattice.basis _),Matrix.det_isEmpty,abs_one]
    rw [hreg]
    apply one_le_pow₀
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR1 3
    norm_num at hh
    linarith
  · exact regulator_upper_bound_of_discriminant K R hR (Nat.pos_of_ne_zero hr) hD

end RegulatorUpper
open scoped Pointwise Combinatorics.Additive ComplexConjugate
namespace DirectionCounting

set_option maxHeartbeats 1000000 in
theorem energy_eq_walk_sum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A U : Finset G) :
    E[A,U] = ∑ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card := by
  classical
  rw [Finset.addEnergy, Finset.card_filter]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := A) (t := U)]
  simp only [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have he (b : G) : a + u = b + v ↔ b = a + u - v := by
    constructor
    · intro h; exact eq_sub_iff_add_eq.mpr h.symm
    · intro h; exact (eq_sub_iff_add_eq.mp h).symm
  simp_rw [he]
  simp

set_option maxHeartbeats 1000000 in
theorem card_bound_of_walks {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A U : Finset G) (L : ℕ)
    (h : ∀ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤ L) :
    U.card ^ 2 * A.card ≤ (A + U).card * L := by
  have he : E[A,U] ≤ A.card * L := by
    rw [energy_eq_walk_sum]
    simpa using Finset.sum_le_sum (fun a ha => h a ha)
  have hc := Finset.le_card_add_mul_addEnergy A U
  have hh := hc.trans (Nat.mul_le_mul_left (A + U).card he)
  by_cases ha : A.card = 0
  · simp [ha]
  have hp : 0 < A.card := Nat.pos_of_ne_zero ha
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh]

set_option maxHeartbeats 1000000 in
theorem equal_chord_start (u p w : ℂ) (hw : w ≠ 0)
    (h₁ : ‖u‖ = ‖p‖) (h₂ : ‖u - w‖ = ‖u‖)
    (h₃ : ‖p - w‖ = ‖p‖) : p = u ∨ p = w - u := by
  have hn₁ : u * conj u = p * conj p := by rw [Complex.mul_conj', Complex.mul_conj', h₁]
  have hn₂ : (u-w) * conj (u-w) = u * conj u := by
    rw [Complex.mul_conj', Complex.mul_conj', h₂]
  have hn₃ : (p-w) * conj (p-w) = p * conj p := by
    rw [Complex.mul_conj', Complex.mul_conj', h₃]
  simp only [map_sub] at hn₂ hn₃
  have hh : (p-u) * (p+u-w) * conj w = 0 := by
    linear_combination u * hn₂ - p * hn₃ + w * hn₁
  have hw' : conj w ≠ 0 := by simpa using hw
  have hz := (mul_eq_zero.mp hh).resolve_right hw'
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

set_option maxHeartbeats 1000000 in
theorem chord_fiber_card_le_two (U : Finset ℂ) (r : ℝ)
    (hU : ∀ u ∈ U, ‖u‖ = r) (w : ℂ) (hw : w ≠ 0) :
    ((U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)).card ≤ 2 := by
  classical
  let F := (U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)
  by_cases he : F.Nonempty
  · obtain ⟨⟨u,v⟩, huv⟩ := he
    simp only [F, Finset.mem_filter, Finset.mem_product] at huv
    obtain ⟨⟨hu,hv⟩, huv'⟩ := huv
    have hs : F ⊆ {(u,v),(-v,-u)} := by
      rintro ⟨p,q⟩ hpq
      simp only [F, Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨⟨hp,hq⟩, hpq'⟩ := hpq
      have hv' : u-w = v := by rw [← huv']; abel
      have hq' : p-w = q := by rw [← hpq']; abel
      have hc := equal_chord_start u p w hw
        ((hU u hu).trans (hU p hp).symm)
        (by rw [hv', hU v hv, hU u hu])
        (by rw [hq', hU q hq, hU p hp])
      rcases hc with hc | hc
      · have hqv : q = v := by rw [← hq', hc, hv']
        simp [hc,hqv]
      · have hpv : p = -v := by rw [hc, ← huv']; abel
        have hqu : q = -u := by rw [← hq', hc]; abel
        simp [hpv,hqu]
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change F.card ≤ 2
    simp [hz]

set_option maxHeartbeats 1000000 in
theorem pinned_unique (A : Finset ℂ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    {a w v : ℂ} (ha : a ∈ A) (hw : w ≠ 0) (hv : v ≠ 0)
    (haw : a+w ∈ A) (hav : a+v ∈ A) (hn : ‖w‖ = ‖v‖) : w = v := by
  by_contra hne
  apply hA ha haw hav
    (by simpa using hw)
    (by simpa using hne)
    (by simpa using hv)
  apply Or.inr ∘ Or.inr
  simpa only [dist_self_add_left, dist_self_add_right] using hn.symm

set_option maxHeartbeats 1000000 in
theorem walk_bound (A U : Finset ℂ) (r : ℝ) (C : Finset ℝ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    (hU : ∀ u ∈ U, ‖u‖ = r)
    (hC : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C)
    {a : ℂ} (ha : a ∈ A) :
    ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤
      U.card + 2 * C.card := by
  classical
  let E := (U ×ˢ U).filter (fun uv => uv.1 ≠ uv.2 ∧ a+uv.1-uv.2 ∈ A)
  let color : ℂ × ℂ → ℝ := fun uv => ‖uv.1-uv.2‖
  have hf (c : ℝ) (hc : c ∈ E.image color) :
      (E.filter (fun uv => color uv = c)).card ≤ 2 := by
    obtain ⟨⟨u,v⟩, huv, he⟩ := Finset.mem_image.mp hc
    have huv' := huv
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv'
    have hw : u-v ≠ 0 := sub_ne_zero.mpr huv'.2.1
    have hs : E.filter (fun uv => color uv = c) ⊆
        (U ×ˢ U).filter (fun uv => uv.1 - uv.2 = u-v) := by
      rintro ⟨p,q⟩ hpq
      obtain ⟨hpq,hcol⟩ := Finset.mem_filter.mp hpq
      simp only [E, Finset.mem_filter, Finset.mem_product] at hpq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr hpq.1, ?_⟩
      apply pinned_unique A hA ha (sub_ne_zero.mpr hpq.2.1) hw
      · simpa only [add_sub_assoc] using hpq.2.2
      · simpa only [add_sub_assoc] using huv'.2.2
      · exact hcol.trans he.symm
    exact (Finset.card_le_card hs).trans (chord_fiber_card_le_two U r hU (u-v) hw)
  have hi : E.image color ⊆ C := by
    intro c hc
    obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hc
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv
    exact hC u huv.1.1 v huv.1.2 huv.2.1
  have he : E.card ≤ 2 * C.card :=
    (Finset.card_le_mul_card_image E 2 hf).trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hi))
  have hs : (U ×ˢ U).filter (fun uv => a+uv.1-uv.2 ∈ A) ⊆ U.diag ∪ E := by
    rintro ⟨u,v⟩ huv
    obtain ⟨huv,hmem⟩ := Finset.mem_filter.mp huv
    by_cases h : u = v
    · subst v
      exact Finset.mem_union_left _ (by simpa using (Finset.mem_product.mp huv).1)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huv,h,hmem⟩)
  calc
    _ ≤ (U.diag ∪ E).card := Finset.card_le_card hs
    _ ≤ U.diag.card + E.card := Finset.card_union_le _ _
    _ ≤ U.card + 2*C.card := by simpa using Nat.add_le_add_left he U.card

set_option maxHeartbeats 1000000 in
theorem isosceles_free_bound (A U : Finset ℂ) (r : ℝ) (C : Finset ℝ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    (hU : ∀ u ∈ U, ‖u‖ = r)
    (hC : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C) :
    U.card^2 * A.card ≤ (A+U).card * (U.card + 2*C.card) :=
  card_bound_of_walks A U _ (fun _ ha => walk_bound A U r C hA hU hC ha)

end DirectionCounting
namespace SumsetGrowth
open scoped Pointwise

theorem growth_cutoff (C : ℕ) : C * (4*C+5) < 2^(4*C+4) := by
  have hC : C+1 ≤ 2^C := Nat.lt_two_pow_self
  have hpow : (C+1)^2 ≤ (2^C)^2 := Nat.pow_le_pow_left hC 2
  have hbound : C*(4*C+5) < 8*(C+1)^2 := by nlinarith
  have hexp : 2*C+3 ≤ 4*C+4 := by omega
  calc
    C*(4*C+5) < 8*(C+1)^2 := hbound
    _ ≤ 8*(2^C)^2 := Nat.mul_le_mul_left 8 hpow
    _ = 2^(2*C+3) := by rw [pow_add, pow_mul']; norm_num; ring
    _ ≤ 2^(4*C+4) := Nat.pow_le_pow_right (by norm_num) hexp

theorem exists_small_step (f : ℕ → ℕ) (C d : ℕ) (hd : 0 < d)
    (hf : 0 < f 0) (hbound : f (4*C+4) ≤ (C*(4*C+5))^d) :
    ∃ j < 4*C+4, f (j+1) ≤ 2^d * f j := by
  by_contra! h
  have hlow : ∀ j ≤ 4*C+4, (2^d)^j ≤ f j := by
    intro j hj
    induction j with
    | zero => simp only [pow_zero]; omega
    | succ j ih =>
      have hj' : j < 4*C+4 := by omega
      calc
        (2^d)^(j+1) = 2^d * (2^d)^j := by rw [pow_succ'];
        _ ≤ 2^d * f j := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ f (j+1) := (h j hj').le
  have hlt := Nat.pow_lt_pow_left (growth_cutoff C) (Nat.ne_of_gt hd)
  have hcomm : (2^d)^(4*C+4) = (2^(4*C+4))^d := by rw [← pow_mul, ← pow_mul, mul_comm d]
  have hh := (hlow _ le_rfl).trans hbound
  rw [hcomm] at hh
  exact hlt.not_ge hh

theorem configuration_of_directions (U : Finset ℂ) (K C d : ℕ)
    (hd : 0 < d) (hK : 0 < K)
    (hunit : ∀ u ∈ U, ‖u‖ = 1)
    (hlarge : (16*K)^d ≤ U.card)
    (hquot : (U/U).card ≤ K^d * U.card)
    (hpacking : ∀ j ≤ 4*C+4, (j • U).card ≤ (C*(j+1))^d) :
    ∃ S : Finset ℂ, S.Nonempty ∧ S.card ≤ (C*(4*C+5))^d ∧
      ∀ A : Finset ℂ, A ⊆ S →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) →
        2^d * A.card ≤ S.card := by
  classical
  obtain ⟨j,hj,hstep⟩ := exists_small_step (fun j => (j • U).card) C d hd
    (by simp) (by simpa only [Nat.add_assoc] using hpacking (4*C+4) le_rfl)
  have hU : U.Nonempty := Finset.card_pos.mp ((by positivity : 0 < (16*K)^d).trans_le hlarge)
  let S : Finset ℂ := j • U
  have hS : S.Nonempty := by
    exact Finset.Nonempty.nsmul hU
  refine ⟨S,hS,(hpacking j hj.le).trans ?_,?_⟩
  · exact Nat.pow_le_pow_left (Nat.mul_le_mul_left C (by omega)) d
  intro A hAS hA
  let colors : Finset ℝ := (U/U).image (fun w => ‖1-w‖)
  have hc : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ colors := by
    intro u hu v hv _
    have hv0 : v ≠ 0 := by intro hv0; simpa [hv0] using hunit v hv
    have heq : ‖u-v‖ = ‖1-u/v‖ := by
      calc
        ‖u-v‖ = ‖(u/v-1)*v‖ := by congr 1; field_simp
        _ = ‖u/v-1‖ := by rw [norm_mul, hunit v hv, mul_one]
        _ = ‖1-u/v‖ := norm_sub_rev _ _
    rw [heq]
    exact Finset.mem_image.mpr ⟨u/v,Finset.div_mem_div hu hv,rfl⟩
  have hcol : colors.card ≤ K^d * U.card := (Finset.card_image_le).trans hquot
  have he := DirectionCounting.isosceles_free_bound A U 1 colors hA hunit hc
  have hadd : (A+U).card ≤ 2^d * S.card := by
    calc
      (A+U).card ≤ (S+U).card := Finset.card_le_card (Finset.add_subset_add hAS subset_rfl)
      _ = ((j+1) • U).card := by rw [add_nsmul, one_nsmul]
      _ ≤ 2^d * S.card := hstep
  have he' : U.card^2 * A.card ≤ 2^d * S.card * ((1+2*K^d)*U.card) :=
    he.trans (Nat.mul_le_mul hadd (by nlinarith [hcol]))
  have he'' : U.card * A.card ≤ 2^d * S.card * (1+2*K^d) := by
    apply (Nat.mul_le_mul_right_iff (Finset.card_pos.mpr hU)).mp
    nlinarith [he']
  have hKpow : 1 ≤ K^d := Nat.one_le_pow _ _ hK
  have hfour : 4 ≤ 4^d := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 4) hd
  have hcoef : 2^d * (2^d * (1+2*K^d)) ≤ U.card := by
    apply le_trans _ hlarge
    rw [mul_pow]
    have h16 : (16 : ℕ)^d = 2^d * 2^d * 4^d := by
      rw [← mul_pow, ← mul_pow]; norm_num
    rw [h16]
    calc
      _ = (2^d * 2^d) * (1+2*K^d) := by ring
      _ ≤ (2^d * 2^d) * (4^d * K^d) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have hh := Nat.mul_le_mul_right A.card hcoef
  have hh' := hh.trans he''
  have hp : 0 < 2^d * (1+2*K^d) := by positivity
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh']

end SumsetGrowth
open Filter
namespace Erdos1207

theorem P_le_of_configuration {d n m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : S.card = n)
    (h : ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      Set.IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m := by
  unfold P
  refine le_trans (Nat.sInf_le ⟨S, hS, rfl⟩) ?_
  apply csSup_le'
  rintro k ⟨A, hAS, hA, rfl⟩
  exact h A hAS hA

private theorem exists_injective_polynomial_eval {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℂ) (hp : Function.Injective p) :
    ∃ t : ℂ, Function.Injective (fun i => (p i).eval t) := by
  classical
  let q : Polynomial ℂ := ∏ ij ∈ (Finset.univ : Finset ι).offDiag, (p ij.1 - p ij.2)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    exact sub_ne_zero.mpr (hp.ne (Finset.mem_offDiag.mp hij).2.2)
  obtain ⟨t, ht⟩ : ∃ t : ℂ, q.eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (Polynomial.funext (by simpa using h))
  refine ⟨t, fun i j hij => ?_⟩
  by_contra hne
  apply ht
  dsimp only [q]
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := (i,j))
  · simp [hne]
  · simp [hij]

private theorem P_le_of_large_configuration {d n m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hn : n ≤ S.card)
    (h : ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      Set.IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hn
  exact P_le_of_configuration T hT fun A hAT hA => h A (hAT.trans hTS) hA

private theorem exists_injective_copies (S : Finset ℂ) (q : ℕ) :
    ∃ t : ℂ, Function.Injective
      (fun p : Fin q × S => (p.2 : ℂ) + (p.1.val : ℂ)*t) := by
  classical
  let p : Fin q × S → Polynomial ℂ := fun a =>
    Polynomial.C (a.2 : ℂ) + Polynomial.monomial 1 (a.1.val : ℂ)
  have hp : Function.Injective p := by
    intro a b hab
    have h0 := congrArg (fun f : Polynomial ℂ => f.coeff 0) hab
    have h1 := congrArg (fun f : Polynomial ℂ => f.coeff 1) hab
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_monomial, one_ne_zero, ↓reduceIte, add_zero] at h0
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial,
      one_ne_zero, ↓reduceIte, zero_add, Nat.cast_inj] at h1
    exact Prod.ext (Fin.ext h1) (Subtype.ext h0)
  obtain ⟨t,ht⟩ := exists_injective_polynomial_eval p hp
  refine ⟨t, ?_⟩
  simpa only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial,
    pow_one] using ht

theorem exists_replicated_configuration (S : Finset ℂ) (q M : ℕ)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    ∃ T : Finset ℂ, T.card = q*S.card ∧
      ∀ A : Finset ℂ, A ⊆ T →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ q*M := by
  classical
  obtain ⟨t,ht⟩ := exists_injective_copies S q
  let f : Fin q × S → ℂ := fun p => (p.2 : ℂ) + (p.1.val : ℂ)*t
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ht]
    simp
  intro A hAS hA
  obtain ⟨B,hB,rfl⟩ := Finset.subset_image_iff.mp hAS
  rw [Finset.card_image_of_injective _ ht]
  have hrow (i : Fin q) : (B.filter (fun p => p.1 = i)).card ≤ M := by
    let D := B.filter (fun p => p.1 = i)
    let C := D.image (fun p => (p.2 : ℂ))
    have hCsub : C ⊆ S := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact p.2.property
    have hmem (x : ℂ) (hx : x ∈ C) : x+(i.val : ℂ)*t ∈ B.image f := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
      have he : f p = (p.2 : ℂ) + (i.val : ℂ)*t := by simp [f,hi]
      exact he ▸ Finset.mem_image_of_mem f hp
    have hCfree : (C : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z := by
      intro x hx y hy z hz hxy hyz hxz hiso
      apply hA (hmem x hx) (hmem y hy) (hmem z hz)
        (by simpa using hxy) (by simpa using hyz) (by simpa using hxz)
      simpa only [IsIsosceles, dist_add_right] using hiso
    have hinj : Set.InjOn (fun p : Fin q × S => (p.2 : ℂ)) (D : Set (Fin q × S)) := by
      intro p hp r hr he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)
        (Subtype.ext he)
    have hc := hS C hCsub hCfree
    dsimp only [C] at hc
    rwa [Finset.card_image_of_injOn hinj] at hc
  have he : B.card = ∑ i : Fin q, (B.filter (fun p => p.1 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (by
      intro p hp
      exact Finset.mem_univ p.1)
  rw [he]
  calc
    _ ≤ ∑ _i : Fin q, M := Finset.sum_le_sum (fun i _ => hrow i)
    _ = q*M := by simp

theorem P_two_le_of_complex_configuration (S : Finset ℂ) (n M : ℕ)
    (hn : n ≤ S.card)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    P 2 n ≤ M := by
  classical
  let e := Complex.orthonormalBasisOneI.repr
  apply P_le_of_large_configuration (S.image e)
  · simpa only [Finset.card_image_of_injective _ e.injective] using hn
  · intro A hAS hA
    obtain ⟨B,hB,rfl⟩ := Finset.subset_image_iff.mp hAS
    rw [Finset.card_image_of_injective _ e.injective]
    apply hS B hB
    intro a ha b hb c hc hab hbc hac hiso
    apply hA (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
      (Finset.mem_image_of_mem _ hc) (e.injective.ne hab) (e.injective.ne hbc)
      (e.injective.ne hac)
    simpa only [IsIsosceles, e.dist_map] using hiso

theorem P_two_bound_by_replication (S : Finset ℂ) (hSpos : S.Nonempty) (M n : ℕ)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ (n + S.card) * M := by
  classical
  let q := n / S.card + 1
  obtain ⟨T,hT,hbound⟩ := exists_replicated_configuration S q M hS
  have hn : n ≤ T.card := by
    rw [hT, mul_comm]
    exact (Nat.lt_mul_div_succ n hSpos.card_pos).le
  have hp := P_two_le_of_complex_configuration T n (q*M) hn hbound
  calc
    S.card * P 2 n ≤ S.card * (q*M) := Nat.mul_le_mul_left _ hp
    _ = (S.card * (n / S.card) + S.card) * M := by dsimp [q]; ring
    _ ≤ (n+S.card)*M := by
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le n S.card) _)

theorem P_two_density_by_replication (S : Finset ℂ) (hSpos : S.Nonempty) (M n : ℕ)
    (hn : S.card ≤ n)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ 2*n*M := by
  have h := P_two_bound_by_replication S hSpos M n hS
  exact h.trans (Nat.mul_le_mul_right M (by omega))

theorem P_two_weighted_density_replication (S : Finset ℂ) (hSpos : S.Nonempty)
    (L n : ℕ) (hn : S.card ≤ n)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → L*A.card ≤ S.card) :
    L * P 2 n ≤ 2*n := by
  by_cases hL : L = 0
  · simp [hL]
  have hLpos := Nat.pos_of_ne_zero hL
  have h := P_two_density_by_replication S hSpos (S.card/L) n hn (by
    intro A hAS hA
    rw [Nat.le_div_iff_mul_le hLpos]
    simpa only [mul_comm] using hS A hAS hA)
  apply Nat.le_of_mul_le_mul_left (c := S.card) _ hSpos.card_pos
  calc
    S.card * (L * P 2 n) = L * (S.card * P 2 n) := by ring
    _ ≤ L * (2*n*(S.card/L)) := Nat.mul_le_mul_left L h
    _ = (2*n) * (L*(S.card/L)) := by ring
    _ ≤ (2*n) * S.card := Nat.mul_le_mul_left _ (Nat.mul_div_le S.card L)
    _ = S.card * (2*n) := by ring

private theorem power_saving_arithmetic (H d a n : ℕ)
    (hH : 0 < H) (hd : 3 ≤ d) (hn : 0 < n)
    (ha : 2^d * a ≤ 2*n) (hb : n ≤ 2^(2*H*d)) :
    (a : ℝ) < (n : ℝ)^(1 - 1/(4*H : ℝ)) := by
  let L := 4*H
  have hL : 0 < L := by dsimp [L]; omega
  have he : L+2*H*d < d*L := by dsimp [L]; nlinarith
  have hc : 2^L * 2^(2*H*d) < 2^(d*L) := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) he
  have hp : 2^(d*L) * a^L ≤ 2^L * n^L := by
    simpa only [mul_pow, ← pow_mul] using Nat.pow_le_pow_left ha L
  have hx : 2^(d*L) * (a^L*n) < 2^(d*L) * n^L := by
    calc
      _ = (2^(d*L) * a^L) * n := by ring
      _ ≤ (2^L * n^L) * n := Nat.mul_le_mul_right n hp
      _ = (2^L*n) * n^L := by ring
      _ ≤ (2^L * 2^(2*H*d)) * n^L :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
      _ < _ := Nat.mul_lt_mul_of_pos_right hc (pow_pos hn L)
  have hx' : a^L*n < n^L := (Nat.mul_lt_mul_left (by positivity : 0 < 2^(d*L))).mp hx
  have heL : L = (L-1)+1 := by omega
  have hnat : a^L < n^(L-1) := by
    have hen : n^L = n^(L-1)*n := by
      calc
        n^L = n^((L-1)+1) := congrArg (fun t : ℕ => n^t) heL
        _ = _ := pow_succ n (L-1)
    rw [hen] at hx'
    exact (Nat.mul_lt_mul_right hn).mp hx'
  have hreal : (a : ℝ)^L < (n : ℝ)^(L-1) := by exact_mod_cast hnat
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hexp : (1-1/(4*H : ℝ))*(L : ℝ) = ((L-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    have heq : (4*H : ℝ) = L := by simp [L]
    rw [heq]
    field_simp
  have hpow : ((n : ℝ)^(1-1/(4*H : ℝ)))^L = (n : ℝ)^(L-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hexp, Real.rpow_natCast]
  by_contra h
  have hle : (n : ℝ)^(1-1/(4*H : ℝ)) ≤ a := le_of_not_gt h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hle L
  rw [hpow] at hh
  exact hreal.not_ge hh

theorem power_saving_of_doubly_exponential_configurations
    (H : ℕ) (hH : 0 < H)
    (h : ∀ m : ℕ, ∃ S : Finset ℂ, S.Nonempty ∧ S.card ≤ 2^(H*2^m) ∧
      ∀ A : Finset ℂ, A ⊆ S →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) →
          2^(2^m) * A.card ≤ S.card) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  refine ⟨1/(4*H : ℝ), by positivity, Filter.eventually_atTop.2 ⟨2^(4*H), ?_⟩⟩
  intro n hn
  have hnpos : 0 < n := (by positivity : 0 < 2^(4*H)).trans_le hn
  let l := Nat.log 2 n
  let q := l/H
  let m := Nat.log 2 q
  let d := 2^m
  have hl : 4*H ≤ l := Nat.le_log_of_pow_le (by norm_num) hn
  have hq : 4 ≤ q := (Nat.le_div_iff_mul_le hH).mpr (by simpa only [mul_comm] using hl)
  have hm : 2 ≤ m := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hq)
  have hd : 3 ≤ d := by
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
    norm_num at hh
    exact (by norm_num : 3 ≤ 4).trans hh
  have hdq : d ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hqhigh : q+1 ≤ 2*d := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
    simpa only [pow_succ, mul_comm, Nat.lt_iff_add_one_le] using hh
  have hsmall : H*d ≤ l :=
    (Nat.mul_le_mul_left H hdq).trans (Nat.mul_div_le l H)
  have hlarge : l+1 ≤ 2*H*d := by
    have hh := Nat.lt_mul_div_succ l hH
    have hh' := Nat.mul_le_mul_left H hqhigh
    have : l < H*(2*d) := hh.trans_le hh'
    nlinarith
  obtain ⟨S,hSpos,hScard,hS⟩ := h m
  have hSn : S.card ≤ n := hScard.trans
    ((Nat.pow_le_pow_right (by norm_num : 0 < 2) hsmall).trans
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos)))
  have ha := P_two_weighted_density_replication S hSpos (2^d) n hSn hS
  have hb : n ≤ 2^(2*H*d) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hlarge)
  exact power_saving_arithmetic H d (P 2 n) n hH hd hnpos ha hb

end Erdos1207
namespace Erdos1207
open NumberField
open scoped Classical Pointwise

theorem power_saving_of_quadratic_field_family
    (K L : ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hreg : ∀ m, NumberField.Units.regulator (L m) ≤ (R : ℝ)^(Module.finrank ℚ (L m)))
    (hrel : ∀ m, Module.finrank (K m) (L m) = 2)
    (hgap : ∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex : ∀ m, ∃ σ : L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  let C := 4*UniformDirections.houseBound R ((16*500)^2)+1
  let H := (C*(4*C+5)+1)*2*D
  have hD : 0 < D := by have hh := hdegree 0; norm_num at hh; omega
  have hH : 0 < H := by dsimp [H]; positivity
  apply power_saving_of_doubly_exponential_configurations H hH
  intro m
  obtain ⟨σ,hσ⟩ := hcomplex m
  obtain ⟨U,hunit,hlarge,hdiv,hpacking⟩ := UniformDirections.exists_directions (K m) (L m) R hR
    (hreg m) (hrel m) (hgap m) σ hσ
  obtain ⟨S,hSpos,hScard,hS⟩ := SumsetGrowth.configuration_of_directions U 500 C
    (2*Module.finrank ℚ (L m)) (by have hh : 0 < Module.finrank ℚ (L m) := Module.finrank_pos; positivity) (by norm_num)
    hunit hlarge hdiv (fun j _ => hpacking j)
  refine ⟨S,hSpos,?_,?_⟩
  · calc
      S.card ≤ (C*(4*C+5))^(2*Module.finrank ℚ (L m)) := hScard
      _ ≤ (C*(4*C+5))^(2*(D*2^m)) := Nat.pow_le_pow_right (by dsimp [C]; positivity) (Nat.mul_le_mul_left 2 (hdegree m).2)
      _ ≤ (2^(C*(4*C+5)+1))^(2*(D*2^m)) := Nat.pow_le_pow_left (by
        have hh := Nat.lt_two_pow_self (n := C*(4*C+5)+1)
        omega) _
      _ = 2^(H*2^m) := by rw [← pow_mul]; congr 1; dsimp [H]; ring
  · intro A hAS hA
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by have hh := (hdegree m).1; omega))).trans
      (hS A hAS hA)

theorem power_saving_of_bounded_discriminant_family
    (K L : ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hdisc : ∀ m, |(NumberField.discr (L m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (L m)))
    (hrel : ∀ m, Module.finrank (K m) (L m) = 2)
    (hgap : ∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex : ∀ m, ∃ σ : L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  apply power_saving_of_quadratic_field_family K L (4608*R^3) D (by positivity) hdegree
    (fun m => ?_) hrel hgap hcomplex
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
    RegulatorUpper.regulator_upper_bound (L m) R hR (hdisc m)

end Erdos1207
namespace PureQuartic
open Polynomial NumberField
open scoped Classical

private theorem irred_int : Irreducible (X^4-C (5 : ℤ)) := by
  let P : Ideal ℤ := Ideal.span {5}
  have hmon : (X^4-C (5 : ℤ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P := P)
  · exact (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn4 : n < 4 := by simpa only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 4),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega : n ≠ 4)]
    by_cases hn0 : n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 4)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive

theorem irreducible : Irreducible (X^4-C (5 : ℚ)) := by
  have hh := ((monic_X_pow_sub_C (5 : ℤ) (by norm_num : (4 : ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp irred_int
  have h5 : (C (5 : ℚ)) = 5 := map_ofNat C 5
  rw [h5]; simpa using hh

noncomputable instance : Fact (Irreducible (X^4-C (5 : ℚ))) := ⟨irreducible⟩
abbrev F := AdjoinRoot (X^4-C (5 : ℚ))

noncomputable def alpha : F := AdjoinRoot.root (X^4-C (5 : ℚ))

theorem alpha_pow : alpha^4 = 5 := by
  have hh := AdjoinRoot.eval₂_root (X^4-C (5 : ℚ))
  simpa [alpha,sub_eq_zero] using hh

theorem degree : Module.finrank ℚ F = 4 := by
  rw [(AdjoinRoot.powerBasis irreducible.ne_zero).finrank,AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

noncomputable def rho : ℝ := Real.sqrt (Real.sqrt 5)

theorem rho_pos : 0 < rho := by dsimp [rho]; positivity

theorem rho_pow : rho^4 = 5 := by
  have h₁ : rho^2 = Real.sqrt 5 := Real.sq_sqrt (by positivity)
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

theorem real_roots (x : ℝ) (hx : x^4 = 5) : x = rho ∨ x = -rho := by
  have hs : (x^2)^2 = (rho^2)^2 := by nlinarith [rho_pow]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hh | hh
  · exact sq_eq_sq_iff_eq_or_eq_neg.mp hh
  · have hr : 0 < rho^2 := pow_pos rho_pos _
    nlinarith [sq_nonneg x]

noncomputable def realLift (x : ℝ) (hx : x^4 = 5) : F →+* ℂ :=
  Complex.ofRealHom.comp (AdjoinRoot.lift (f := X^4-C (5 : ℚ)) (algebraMap ℚ ℝ) x (by simp [hx]))

theorem realLift_alpha (x : ℝ) (hx : x^4 = 5) : realLift x hx alpha = (x : ℂ) := by
  simp [realLift,alpha,AdjoinRoot.lift_root]

theorem realLift_isReal (x : ℝ) (hx : x^4 = 5) : ComplexEmbedding.IsReal (realLift x hx) := by
  apply ComplexEmbedding.isReal_iff.mpr
  apply RingHom.ext
  intro a
  simp [ComplexEmbedding.conjugate_coe_eq,realLift]

theorem hom_ext {σ τ : F →+* ℂ} (h : σ alpha = τ alpha) : σ = τ :=
  AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) h

theorem real_embeddings (σ : F →+* ℂ) (hσ : ComplexEmbedding.IsReal σ) :
    σ = realLift rho rho_pow ∨ σ = realLift (-rho) (by nlinarith [rho_pow]) := by
  let φ : F →+* ℝ := hσ.embedding
  have hx : (φ alpha)^4 = 5 := by
    simpa only [map_pow,map_ofNat] using congrArg φ alpha_pow
  have hval := hσ.coe_embedding_apply alpha
  rcases real_roots (φ alpha) hx with h | h
  · left
    apply hom_ext
    rw [realLift_alpha,← hval]
    exact congrArg Complex.ofReal h
  · right
    apply hom_ext
    rw [realLift_alpha,← hval]
    exact congrArg Complex.ofReal h

theorem nrRealPlaces : InfinitePlace.nrRealPlaces F = 2 := by
  let p : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} := ⟨realLift rho rho_pow,realLift_isReal _ _⟩
  let n : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} := ⟨realLift (-rho) (by nlinarith [rho_pow]),realLift_isReal _ _⟩
  have hpn : p ≠ n := by
    intro h
    have he := congrArg (fun σ : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} => σ.val alpha) h
    change realLift rho rho_pow alpha = realLift (-rho) (by nlinarith [rho_pow]) alpha at he
    rw [realLift_alpha,realLift_alpha] at he
    have hr : rho = -rho := Complex.ofReal_injective he
    linarith [rho_pos]
  have huniv : (Finset.univ : Finset {σ : F →+* ℂ // ComplexEmbedding.IsReal σ}) = {p,n} := by
    ext σ
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    rcases real_embeddings σ.val σ.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [← InfinitePlace.card_real_embeddings,← Finset.card_univ,huniv,Finset.card_pair hpn]

end PureQuartic
namespace NegativeSquareRoot
open Polynomial NumberField
open scoped Classical

private theorem irred_int : Irreducible (X^2-C (5 : ℤ)) := by
  let P : Ideal ℤ := Ideal.span {5}
  have hmon : (X^2-C (5 : ℤ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P := P)
  · exact (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn2 : n < 2 := by simpa only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega : n ≠ 2)]
    by_cases hn0 : n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive

theorem irreducible_rat : Irreducible (X^2-C (5 : ℚ)) := by
  have hh := ((monic_X_pow_sub_C (5 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp irred_int
  have h5 : (C (5 : ℚ)) = 5 := map_ofNat C 5
  rw [h5]; simpa using hh

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

theorem exists_negative_embedding (a : K) (ha : a^2 = 5) :
    ∃ φ : K →+* ℝ, φ a = -Real.sqrt 5 := by
  have hmin : minpoly ℚ a = X^2-C (5 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic irreducible_rat (by simp [ha]) (monic_X_pow_sub_C _ (by norm_num))).symm
  have hroot : (-(Real.sqrt 5 : ℂ)) ∈ (minpoly ℚ a).rootSet ℂ := by
    rw [hmin,mem_rootSet_of_ne irreducible_rat.ne_zero]
    have hs : (Real.sqrt 5 : ℂ)^2 = 5 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    simpa only [aeval_sub,map_pow,aeval_X,aeval_C,map_ofNat,neg_sq,sub_eq_zero] using hs
  rw [← Embeddings.range_eval_eq_rootSet_minpoly K ℂ a] at hroot
  obtain ⟨σ,hσ⟩ := hroot
  change σ a = -(Real.sqrt 5 : ℂ) at hσ
  let hr := IsTotallyReal.complexEmbedding_isReal σ
  refine ⟨hr.embedding,?_⟩
  apply Complex.ofReal_injective
  rw [hr.coe_embedding_apply,hσ,Complex.ofReal_neg]

theorem nonsquare (a : K) (ha : a^2 = 5) : ∀ b : K, b^2 ≠ a := by
  obtain ⟨φ,hφ⟩ := exists_negative_embedding K a ha
  intro b hb
  have hh := congrArg φ hb
  rw [map_pow,hφ] at hh
  have hp : 0 < Real.sqrt 5 := by positivity
  nlinarith [sq_nonneg (φ b)]

theorem irreducible_quadratic (a : K) (ha : a^2 = 5) : Irreducible (X^2-C a) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (nonsquare K a ha)

end NegativeSquareRoot
namespace CompositumSignature
open NumberField
open scoped Classical BigOperators

variable (F K L : Type*) [Field F] [Field K] [Field L]
  [NumberField F] [NumberField K] [NumberField L]
  [Algebra F L] [Algebra K L] [FiniteDimensional F L] [IsTotallyReal K]

omit [NumberField F] [NumberField K] [NumberField L] [FiniteDimensional F L] in

theorem isReal_iff (hgen : Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤)
    (σ : L →+* ℂ) :
    ComplexEmbedding.IsReal σ ↔ ComplexEmbedding.IsReal (σ.comp (algebraMap F L)) := by
  refine ⟨fun h => h.comp _,fun h => ?_⟩
  let φ : K →+* ℂ := σ.comp (algebraMap K L)
  letI : Algebra K ℂ := φ.toAlgebra
  let a : L →ₐ[K] ℂ := { σ with commutes' := fun _ => rfl }
  have hφ : ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b : L →ₐ[K] ℂ := { ComplexEmbedding.conjugate σ with
    commutes' := fun r => DFunLike.congr_fun hφ r }
  have hab : b = a := AlgHom.ext_of_adjoin_eq_top hgen (by
    rintro _ ⟨x,rfl⟩
    exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.mp h) x)
  exact ComplexEmbedding.isReal_iff.mpr (congrArg AlgHom.toRingHom hab)

omit [NumberField K] [Algebra K L] [IsTotallyReal K] in

theorem card_extensions (φ : F →+* ℂ) :
    Fintype.card (ComplexEmbedding.Extension L φ) = Module.finrank F L := by
  letI : Algebra F ℂ := φ.toAlgebra
  let e : ComplexEmbedding.Extension L φ ≃ (L →ₐ[F] ℂ) :=
    { toFun σ := { σ.val with commutes' := fun r => (by haveI := σ.property; exact ComplexEmbedding.LiesOver.over_apply σ.val φ) }
      invFun σ := ⟨σ.toRingHom,⟨by ext r; exact σ.commutes r⟩⟩
      left_inv σ := by rfl
      right_inv σ := by rfl }
  exact (Fintype.card_congr e).trans (AlgHom.card F L ℂ)

omit [NumberField K] [Algebra K L] [IsTotallyReal K] in

theorem nrRealPlaces_mul
    (hreal : ∀ σ : L →+* ℂ, ComplexEmbedding.IsReal (σ.comp (algebraMap F L)) → ComplexEmbedding.IsReal σ) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L := by
  let e : {σ : L →+* ℂ // ComplexEmbedding.IsReal σ} ≃
      Σ φ : {φ : F →+* ℂ // ComplexEmbedding.IsReal φ}, ComplexEmbedding.Extension L φ.val :=
    { toFun σ := ⟨⟨σ.val.comp (algebraMap F L),σ.property.comp _⟩,⟨σ.val,⟨rfl⟩⟩⟩
      invFun p := ⟨p.2.val,hreal p.2.val (by
        haveI := p.2.property
        rw [ComplexEmbedding.LiesOver.over p.2.val p.1.val]; exact p.1.property)⟩
      left_inv σ := rfl
      right_inv p := by rcases p with ⟨⟨φ,hφ⟩,⟨σ,⟨hσ⟩⟩⟩; cases hσ; rfl }
  rw [← InfinitePlace.card_real_embeddings, Fintype.card_congr e,Fintype.card_sigma]
  simp only [card_extensions,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    InfinitePlace.card_real_embeddings,Nat.cast_id]

omit [NumberField K] in

theorem nrRealPlaces_compositum
    (hgen : Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L :=
  nrRealPlaces_mul F L (fun σ h => (isReal_iff F K L hgen σ).mpr h)

end CompositumSignature
namespace QuadraticDifferent
open NumberField Polynomial
open scoped Classical

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

set_option maxHeartbeats 1000000 in
theorem derivative_mem (x : 𝓞 L)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤)
    (p : (𝓞 K)[X]) (hp : aeval x p = 0) :
    aeval x p.derivative ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  obtain ⟨q,rfl⟩ := minpoly.isIntegrallyClosed_dvd (IsIntegralClosure.isIntegral (𝓞 K) L x) hp
  rw [derivative_mul,map_add,map_mul,map_mul,minpoly.aeval,zero_mul,add_zero]
  exact Ideal.mul_mem_right _ _ (aeval_derivative_mem_differentIdeal (𝓞 K) K L x hgen)

set_option maxHeartbeats 1000000 in
theorem two_mul_mem (a : 𝓞 K) (x : 𝓞 L)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a) :
    2*x ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hh := derivative_mem K L x hgen (X^2-C a) (by simp [hx])
  simpa only [derivative_sub,derivative_pow,derivative_X,derivative_C,pow_one,
    mul_one,sub_zero,map_mul,map_natCast,aeval_X,Nat.reduceSub,aeval_C,Nat.cast_ofNat,map_ofNat] using hh

end QuadraticDifferent
namespace IntegralNormBound
open NumberField
open scoped Classical BigOperators

variable (L : Type*) [Field L] [NumberField L]

theorem norm_span_eq_prod (x : 𝓞 L) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ (x : L)‖ := by
  have h := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : L))
  rw [← Algebra.coe_norm_int] at h
  simpa [Ideal.absNorm_span_singleton,norm_prod] using h

theorem norm_span_le (x : 𝓞 L) (H : ℝ)
    (hbound : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ H) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ H^(Module.finrank ℚ L) := by
  rw [norm_span_eq_prod]
  have hh := Finset.prod_le_prod (s := (Finset.univ : Finset (L →ₐ[ℚ] ℂ)))
    (fun σ _ => norm_nonneg (σ (x : L))) (fun σ _ => hbound σ.toRingHom)
  simpa only [Finset.prod_const,Finset.card_univ,AlgHom.card] using hh

end IntegralNormBound
namespace QuadraticDiscriminant
open NumberField
open scoped Classical BigOperators

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

theorem different_norm_le (a : 𝓞 K) (x : 𝓞 L) (hx0 : x ≠ 0)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (H : ℝ) (hhouse : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ H) :
    ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ) ≤ (2*H)^(Module.finrank ℚ L) := by
  have hm := QuadraticDifferent.two_mul_mem K L a x hgen hx
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
  have hpos : 0 < (Ideal.span ({2*x} : Set (𝓞 L))).absNorm := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (by norm_num) hx0
  have hle := Nat.le_of_dvd hpos hdvd
  apply (show ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ) ≤ (Ideal.span ({2*x} : Set (𝓞 L))).absNorm by
    exact_mod_cast hle).trans
  apply IntegralNormBound.norm_span_le L (2*x) (2*H)
  intro σ
  norm_num only [map_mul,map_ofNat,norm_mul,RCLike.norm_two]
  exact mul_le_mul_of_nonneg_left (hhouse σ) (by norm_num : (0 : ℝ) ≤ 2)

theorem discr_le (a : 𝓞 K) (x : 𝓞 L) (hx0 : x ≠ 0)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (hdeg : Module.finrank K L = 2) (R : ℕ)
    (hdisc : |(discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K))
    (hhouse : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ 2) :
    |(discr L : ℝ)| ≤ (2*(R : ℝ))^(2*Module.finrank ℚ L) := by
  have hdiff := different_norm_le K L a x hx0 hgen hx 2 hhouse
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have her : |(discr L : ℝ)| = ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ)*|(discr K : ℝ)|^2 := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_natAbs,Int.cast_abs,hdeg] using
      congrArg (fun n : ℕ => (n : ℝ)) he
  have hd := Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  rw [her]
  calc
    _ ≤ (4 : ℝ)^(Module.finrank ℚ L)*((R : ℝ)^(2*Module.finrank ℚ K))^2 := by
      gcongr
      simpa only [show (2 : ℝ)*2 = 4 by norm_num] using hdiff
    _ = (2*(R : ℝ))^(2*Module.finrank ℚ L) := by
      rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul,mul_pow]
      congr 2; omega

end QuadraticDiscriminant
namespace MixedExtension
open Polynomial NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] (a : K) [Fact (a^2 = 5)]

noncomputable instance : Fact (Irreducible (X^2-C a)) :=
  ⟨NegativeSquareRoot.irreducible_quadratic K a Fact.out⟩

abbrev L := AdjoinRoot (X^2-C a)

instance : Module.Finite K (L K a) := (monic_X_pow_sub_C a (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot

noncomputable instance : NumberField (L K a) := NumberField.of_module_finite K (L K a)

noncomputable def b : L K a := AdjoinRoot.root (X^2-C a)

theorem b_sq : (b K a)^2 = algebraMap K (L K a) a := root_X_pow_sub_C_pow 2 a

theorem b_pow : (b K a)^4 = 5 := by
  calc
    (b K a)^4 = ((b K a)^2)^2 := by ring
    _ = (algebraMap K (L K a) a)^2 := by rw [b_sq]
    _ = algebraMap K (L K a) (a^2) := (map_pow _ _ _).symm
    _ = 5 := by rw [show a^2 = 5 from Fact.out,map_ofNat]

theorem degree : Module.finrank K (L K a) = 2 := by
  rw [(AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out : Irreducible (X^2-C a)).ne_zero)).finrank,
    AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

theorem adjoin_b : Algebra.adjoin K {b K a} = ⊤ := by
  exact (AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out : Irreducible (X^2-C a)).ne_zero)).adjoin_gen_eq_top

noncomputable def quarticMap : PureQuartic.F →+* L K a :=
  AdjoinRoot.lift (algebraMap ℚ (L K a)) (b K a) (by simp [b_pow])

noncomputable instance quarticAlgebra : Algebra PureQuartic.F (L K a) := (quarticMap K a).toAlgebra

theorem quarticMap_alpha : algebraMap PureQuartic.F (L K a) PureQuartic.alpha = b K a := by
  change quarticMap K a PureQuartic.alpha = b K a
  simp [quarticMap,PureQuartic.alpha,AdjoinRoot.lift_root]

theorem compositum : Algebra.adjoin K (Set.range (algebraMap PureQuartic.F (L K a))) = ⊤ := by
  apply top_unique
  rw [← adjoin_b K a]
  apply Algebra.adjoin_mono
  exact Set.singleton_subset_iff.mpr ⟨PureQuartic.alpha,quarticMap_alpha K a⟩

theorem half_real : 2*InfinitePlace.nrRealPlaces (L K a) = Module.finrank ℚ (L K a) := by
  have hr := CompositumSignature.nrRealPlaces_compositum PureQuartic.F K (L K a) (compositum K a)
  rw [PureQuartic.nrRealPlaces] at hr
  have hd := Module.finrank_mul_finrank ℚ PureQuartic.F (L K a)
  rw [PureQuartic.degree] at hd
  omega

omit [NumberField K] [IsTotallyReal K] in
theorem integral_a : IsIntegral ℤ a := by
  refine ⟨X^2-C (5 : ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [show a^2 = 5 from Fact.out]

theorem integral_b : IsIntegral ℤ (b K a) := by
  refine ⟨X^4-C (5 : ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [b_pow]

noncomputable def intA : 𝓞 K := ⟨a,integral_a K a⟩
noncomputable def intB : 𝓞 (L K a) := ⟨b K a,integral_b K a⟩

theorem house_b (σ : L K a →+* ℂ) : ‖σ (b K a)‖ ≤ 2 := by
  have hp := congrArg (fun z : L K a => ‖σ z‖) (b_pow K a)
  simp only [map_pow,norm_pow,map_ofNat,RCLike.norm_ofNat] at hp
  have hn := norm_nonneg (σ (b K a))
  by_contra h
  have hh : 2 < ‖σ (b K a)‖ := lt_of_not_ge h
  have hsq : 4 < ‖σ (b K a)‖^2 := by nlinarith
  nlinarith [sq_nonneg (‖σ (b K a)‖^2-4)]

theorem discr_bound (R : ℕ)
    (hdisc : |(discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    |(discr (L K a) : ℝ)| ≤ (2*(R : ℝ))^(2*Module.finrank ℚ (L K a)) := by
  apply QuadraticDiscriminant.discr_le K (L K a) (intA K a) (intB K a) ?_
    (adjoin_b K a) ?_ (degree K a) R hdisc (house_b K a)
  · intro h
    have hb0 : b K a = 0 := congrArg (fun x : 𝓞 (L K a) => (x : L K a)) h
    have hp := b_pow K a
    rw [hb0] at hp
    norm_num at hp
  · apply RingOfIntegers.coe_injective
    exact b_sq K a

end MixedExtension
namespace UnitRankBounds
open NumberField
open NumberField.InfinitePlace
open scoped Classical

theorem gap_of_half_real (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
    (hdeg : Module.finrank K L = 2) (hhalf : 2*nrRealPlaces L = Module.finrank ℚ L) :
    4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L := by
  have hL := card_add_two_mul_card_eq_rank L
  have hK := IsTotallyReal.finrank K
  have hz := IsTotallyReal.nrComplexPlaces_eq_zero K
  have hd := Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  have hp : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [NumberField.Units.rank,NumberField.Units.rank,
    card_eq_nrRealPlaces_add_nrComplexPlaces,card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem exists_complex_of_half_real (L : Type*) [Field L] [NumberField L]
    (hhalf : 2*nrRealPlaces L = Module.finrank ℚ L) :
    ∃ σ : L →+* ℂ, ¬ ComplexEmbedding.IsReal σ := by
  have hL := card_add_two_mul_card_eq_rank L
  have hp : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hc : 0 < nrComplexPlaces L := by omega
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨w.val.embedding,isComplex_iff.mp w.property⟩

end UnitRankBounds
namespace Erdos1207
open NumberField
open scoped Classical

theorem power_saving_of_totally_real_family
    (K : ℕ → Type*) [∀ m, Field (K m)] [∀ m, NumberField (K m)] [∀ m, IsTotallyReal (K m)]
    (a : ∀ m, K m) (ha : ∀ m, (a m)^2 = 5)
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (K m) ∧ Module.finrank ℚ (K m) ≤ D*2^m)
    (hdisc : ∀ m, |(discr (K m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (K m))) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  letI : ∀ m, Fact ((a m)^2 = 5) := fun m => ⟨ha m⟩
  let L := fun m => MixedExtension.L (K m) (a m)
  have hrel (m : ℕ) : Module.finrank (K m) (L m) = 2 := MixedExtension.degree (K m) (a m)
  have hhalf (m : ℕ) : 2*InfinitePlace.nrRealPlaces (L m) = Module.finrank ℚ (L m) :=
    MixedExtension.half_real (K m) (a m)
  apply power_saving_of_bounded_discriminant_family K L (2*R) (2*D) (by positivity)
    (fun m => ?_) (fun m => ?_) hrel
    (fun m => UnitRankBounds.gap_of_half_real (K m) (L m) (hrel m) (hhalf m))
    (fun m => UnitRankBounds.exists_complex_of_half_real (L m) (hhalf m))
  · have he := Module.finrank_mul_finrank ℚ (K m) (L m)
    rw [hrel m] at he
    have hd := hdegree m
    constructor
    · omega
    · nlinarith
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      MixedExtension.discr_bound (K m) (a m) R (hdisc m)

end Erdos1207
namespace DiscriminantDescent
open NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem discr_pow_le :
    |(discr K : ℝ)|^(Module.finrank K L) ≤ |(discr L : ℝ)| := by
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hpos : 0 < (discr L).natAbs := Int.natAbs_pos.mpr (discr_ne_zero L)
  have hnorm : 1 ≤ Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) := by
    rw [he] at hpos
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt (Nat.pos_of_mul_pos_right hpos))
  have hh : (discr K).natAbs^(Module.finrank K L) ≤ (discr L).natAbs := by
    rw [he]
    exact Nat.le_mul_of_pos_left _ hnorm
  have hh' : ((discr K).natAbs : ℝ)^(Module.finrank K L) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'

theorem root_bound (R : ℝ) (hR : 0 ≤ R)
    (hL : |(discr L : ℝ)| ≤ R^(2*Module.finrank ℚ L)) :
    |(discr K : ℝ)| ≤ R^(2*Module.finrank ℚ K) := by
  have hpow := (discr_pow_le K L).trans hL
  have hd := Module.finrank_mul_finrank ℚ K L
  have hp : 0 < Module.finrank K L := Module.finrank_pos
  have he : R^(2*Module.finrank ℚ L) =
      (R^(2*Module.finrank ℚ K))^(Module.finrank K L) := by
    rw [← pow_mul,← hd]
    congr 1
    ring
  rw [he] at hpow
  exact le_of_pow_le_pow_left₀ hp.ne' (by positivity) hpow

end DiscriminantDescent
namespace PFieldDegrees
open IntermediateField

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_intermediate (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (m : ℕ) (hm : p^m ≤ Module.finrank K L) :
    ∃ E : IntermediateField K L, Module.finrank K E = p^m := by
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have hdegree : Module.finrank K L = p^a := (IsGalois.card_aut_eq_finrank K L).symm.trans ha
  have hma : m ≤ a := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hm.trans_eq hdegree)
  obtain ⟨H,hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Gal(L/K)) p
    (show p^(a-m) ∣ Nat.card Gal(L/K) by rw [ha]; exact pow_dvd_pow p (by omega))
  refine ⟨fixedField H,?_⟩
  have he := Module.finrank_mul_finrank K (fixedField H) L
  rw [finrank_fixedField_eq_card,hH,hdegree] at he
  have hh : p^a = p^m*p^(a-m) := by rw [← pow_add,Nat.add_sub_of_le hma]
  rw [hh] at he
  exact Nat.mul_right_cancel (show 0 < p^(a-m) from pow_pos (Fact.out : p.Prime).pos _) he

end PFieldDegrees
namespace Erdos1207
open NumberField
open scoped Classical

theorem power_saving_of_unbounded_galois_family
    (B : Type*) [Field B] [NumberField B] (a : B) (ha : a^2 = 5)
    (L : ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (R : ℕ) (hR : 0 < R)
    (hG : ∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree : ∀ m, 2^m ≤ Module.finrank B (L m))
    (hdisc : ∀ m, |(discr (L m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (L m))) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have he : ∀ m, ∃ E : IntermediateField B (L m), Module.finrank B E = 2^m :=
    fun m => PFieldDegrees.exists_intermediate B (L m) 2 (hG m) m (hdegree m)
  choose E hE using he
  letI (m : ℕ) : NumberField (E m) := NumberField.of_module_finite ℚ (E m)
  letI (m : ℕ) : IsTotallyReal (E m) := IsTotallyReal.of_algebra (E m) (L m)
  apply power_saving_of_totally_real_family (fun m => E m)
    (fun m => algebraMap B (E m) a) (fun m => ?_) R (Module.finrank ℚ B) hR
    (fun m => ?_) (fun m => DiscriminantDescent.root_bound (E m) (L m) (R : ℝ) (by positivity) (hdisc m))
  · rw [← map_pow,ha,map_ofNat]
  · have hd := Module.finrank_mul_finrank ℚ B (E m)
    rw [hE m] at hd
    have hpos : 0 < Module.finrank ℚ B := Module.finrank_pos
    constructor
    · rw [← hd]
      exact Nat.le_mul_of_pos_left _ hpos
    · exact hd.ge

end Erdos1207
namespace Erdos1207
open NumberField
open scoped Classical

theorem power_saving_of_unbounded_unramified_family
    (B : Type*) [Field B] [NumberField B] (a : B) (ha : a^2 = 5)
    (L : ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (hG : ∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree : ∀ m, 2^m ≤ Module.finrank B (L m))
    (hunram : ∀ m, differentIdeal (𝓞 B) (𝓞 (L m)) = ⊤) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  let R := (discr B).natAbs
  have hR : 0 < R := Int.natAbs_pos.mpr (discr_ne_zero B)
  apply power_saving_of_unbounded_galois_family B a ha L R hR hG hdegree
  intro m
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow B (𝓞 B) (L m) (𝓞 (L m))
  rw [hunram m,Ideal.absNorm_top,one_mul] at he
  have hexp : Module.finrank B (L m) ≤ 2*Module.finrank ℚ (L m) := by
    have hd := Module.finrank_mul_finrank ℚ B (L m)
    have hp : 0 < Module.finrank ℚ B := Module.finrank_pos
    have hh := Nat.le_mul_of_pos_left (Module.finrank B (L m)) hp
    omega
  have hb : (discr (L m)).natAbs ≤ R^(2*Module.finrank ℚ (L m)) := by
    rw [he]
    exact Nat.pow_le_pow_right hR hexp
  have hb' : ((discr (L m)).natAbs : ℝ) ≤ (R : ℝ)^(2*Module.finrank ℚ (L m)) := by exact_mod_cast hb
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hb'

end Erdos1207

theorem OMA.solution : OMA.R_Erdos1207_erdos_1207_R1.H1 := by
  unfold OMA.R_Erdos1207_erdos_1207_R1.H1
  intro B _ _ a ha L _ _ _ _ _ hG hdeg hun
  exact Erdos1207.power_saving_of_unbounded_unramified_family B a ha L hG hdeg hun
