import FormalConjectures.Millennium.Poincare
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
A two-disk description of a high-dimensional homotopy sphere. The exterior
of an open chart disk has a distinguished boundary sphere. Disk recognition
can preserve this boundary as a set with any parametrization: the radial
extension of its transition homeomorphism removes the twist before gluing.

The compactness and contractible-puncture inputs come from the R2 reduction
by @steveDOTdigital. For the disk-recognition statement, see Ancel and
Guilbault, Compact contractible n-manifolds have arc spines (n ≥ 5),
introduction, fact (8). That statement is retained as a hypothesis here.
-/

open Metric Set Function Topology
open scoped ContinuousMap

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3

theorem homeomorph_of_same_fibres {X M S : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace M] [T2Space M]
    [TopologicalSpace S] [T2Space S]
    (f : ContinuousMap X M) (g : ContinuousMap X S)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : ∀ x y : X, f x = f y ↔ g x = g y) :
    Nonempty (M ≃ₜ S) := by
  have qf : Topology.IsQuotientMap f := .of_surjective_continuous hf f.continuous
  have qg : Topology.IsQuotientMap g := .of_surjective_continuous hg g.continuous
  have hker : Setoid.ker f = Setoid.ker g := Setoid.ext hfg
  have e : Quotient (Setoid.ker f) ≃ₜ S := by
    rw [hker]
    exact qg.homeomorph
  exact ⟨qf.homeomorph.symm.trans e⟩

theorem homeomorph_of_two_pieces {A B M S : Type*}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B] [CompactSpace B]
    [TopologicalSpace M] [T2Space M] [TopologicalSpace S] [T2Space S]
    (f₀ : A → M) (f₁ : B → M) (g₀ : A → S) (g₁ : B → S)
    (cf₀ : Continuous f₀) (cf₁ : Continuous f₁)
    (cg₀ : Continuous g₀) (cg₁ : Continuous g₁)
    (if₀ : Function.Injective f₀) (if₁ : Function.Injective f₁)
    (ig₀ : Function.Injective g₀) (ig₁ : Function.Injective g₁)
    (hf : Function.Surjective (Sum.elim f₀ f₁))
    (hg : Function.Surjective (Sum.elim g₀ g₁))
    (hcross : ∀ a b, f₀ a = f₁ b ↔ g₀ a = g₁ b) :
    Nonempty (M ≃ₜ S) := by
  apply homeomorph_of_same_fibres
    (⟨Sum.elim f₀ f₁, cf₀.sumElim cf₁⟩ : ContinuousMap (A ⊕ B) M)
    (⟨Sum.elim g₀ g₁, cg₀.sumElim cg₁⟩ : ContinuousMap (A ⊕ B) S) hf hg
  rintro (a | b) (a' | b')
  · exact if₀.eq_iff.trans ig₀.eq_iff.symm
  · exact hcross a b'
  · exact ⟨fun h => ((hcross a' b).mp h.symm).symm,
      fun h => ((hcross a' b).mpr h.symm).symm⟩
  · exact if₁.eq_iff.trans ig₁.eq_iff.symm

/-- A homeomorphism of the unit sphere extends radially over the closed ball. -/
theorem extend_sphere_to_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    ∃ b : Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : E) 1,
      (∀ x, ‖(b x : E)‖ = ‖(x : E)‖) ∧
      ∀ y : Metric.sphere (0 : E) 1,
        (b ⟨y.val, Metric.sphere_subset_closedBall y.prop⟩ : E) = (e y : E) := by
  classical
  let X := (({0} : Set E)ᶜ : Set E)
  let polar := homeomorphUnitSphereProd E
  let g : X ≃ₜ X :=
    (polar.trans (e.prodCongr (Homeomorph.refl (Set.Ioi (0 : ℝ))))).trans polar.symm
  have polar_radius (x : X) : ((polar x).2 : ℝ) = ‖(x : E)‖ := by
    simp only [polar, homeomorphUnitSphereProd_apply_snd_coe]
  have norm_g (x : X) : ‖(g x : E)‖ = ‖(x : E)‖ := by
    rw [← polar_radius (g x), ← polar_radius x]
    change ((polar (polar.symm (e (polar x).1, (polar x).2))).2 : ℝ) = _
    rw [polar.apply_symm_apply]
  have norm_g_inv (x : X) : ‖(g.symm x : E)‖ = ‖(x : E)‖ := by
    simpa only [g.apply_symm_apply] using (norm_g (g.symm x)).symm
  let extend (h : X ≃ₜ X) (x : E) : E :=
    if hx : x = 0 then 0 else (h ⟨x, hx⟩ : E)
  have on_zero (h : X ≃ₜ X) : extend h 0 = 0 := by simp [extend]
  have on_nz (h : X ≃ₜ X) (x : X) : extend h x.val = (h x : E) := by
    have hx : x.val ≠ 0 := x.prop
    simp [extend, hx]
  have extend_inverse (h : X ≃ₜ X) : Function.LeftInverse (extend h.symm) (extend h) := by
    intro x
    by_cases hx : x = 0
    · simp only [hx, on_zero]
    · let z : X := ⟨x, hx⟩
      change extend h.symm (extend h z.val) = z.val
      rw [on_nz, on_nz, h.symm_apply_apply]
  have extend_norm (h : X ≃ₜ X) (hn : ∀ z : X, ‖(h z : E)‖ = ‖(z : E)‖) (x : E) :
      ‖extend h x‖ = ‖x‖ := by
    by_cases hx : x = 0
    · simp only [hx, on_zero]
    · let z : X := ⟨x, hx⟩
      change ‖extend h z.val‖ = ‖z.val‖
      rw [on_nz, hn]
  have extend_cont (h : X ≃ₜ X) (hn : ∀ z : X, ‖(h z : E)‖ = ‖(z : E)‖) :
      Continuous (extend h) := by
    have hU : ContinuousOn (extend h) X := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun z : X => extend h z.val)
      simpa only [on_nz, Function.comp_def] using
        (continuous_subtype_val.comp h.continuous : Continuous (Subtype.val ∘ h))
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      refine ⟨ε, hε, ?_⟩
      intro y hy
      simpa only [on_zero, dist_zero_right, extend_norm h hn] using hy
    · exact (hU x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)
  let G : E ≃ₜ E := {
    toFun := extend g
    invFun := extend g.symm
    left_inv := extend_inverse g
    right_inv := fun x => by simpa only [Homeomorph.symm_symm] using extend_inverse g.symm x
    continuous_toFun := extend_cont g norm_g
    continuous_invFun := extend_cont g.symm norm_g_inv }
  have hG (x : E) : ‖G x‖ = ‖x‖ := extend_norm g norm_g x
  let b : Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : E) 1 :=
    G.subtype (fun x => by
      simp only [mem_closedBall_zero_iff, hG])
  refine ⟨b, fun x => hG x.val, ?_⟩
  intro y
  have hy : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.prop
  let z : X := ⟨y.val, ne_zero_of_mem_unit_sphere y⟩
  have hdir : (polar z).1 = y := by
    apply Subtype.ext
    simp only [polar, homeomorphUnitSphereProd_apply_fst_coe, z, hy, inv_one, one_smul]
  have hr : ((polar z).2 : ℝ) = 1 := (polar_radius z).trans hy
  change extend g z.val = (e y : E)
  rw [on_nz]
  change ((homeomorphUnitSphereProd E).symm (e (polar z).1, (polar z).2) : E) = _
  rw [homeomorphUnitSphereProd_symm_apply_coe, hdir, hr, one_smul]

open Metric

/-- The upper and lower hemispheres are closed disks with identical boundary coordinates. -/
theorem hemisphereModel (n : ℕ) :
    ∃ u v : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      Continuous u ∧ Continuous v ∧ Function.Injective u ∧ Function.Injective v ∧
        (∀ x y, u x = v y ↔ x = y ∧ ‖x.val‖ = 1) ∧
        (∀ z, (∃ x, u x = z) ∨ (∃ y, v y = z)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin (n + 1))
  let D := closedBall (0 : E) 1
  let S := sphere (0 : F) 1
  let put (t : ℝ) (x : E) : F := WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t (fun i => x i))
  let tail (v : F) : E := WithLp.toLp 2 (fun i => v i.succ)
  have head_put (t : ℝ) (x : E) : (put t x) 0 = t := by
    exact Fin.cons_zero (α := fun _ : Fin (n + 1) => ℝ) t (fun i => x i)
  have tail_put (t : ℝ) (x : E) : tail (put t x) = x := by
    apply PiLp.ext
    intro i
    exact Fin.cons_succ (α := fun _ : Fin (n + 1) => ℝ) t (fun j => x j) i
  have reconstruct (v : F) : put (v 0) (tail v) = v := by
    apply PiLp.ext
    refine Fin.cases ?_ (fun i => ?_)
    · exact head_put _ _
    · exact Fin.cons_succ (α := fun _ : Fin (n + 1) => ℝ) (v 0) (fun j => v j.succ) i
  have sq_put (t : ℝ) (x : E) : ‖put t x‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq]
    change (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t (fun i => x i) 0) ^ 2 +
      (∑ i : Fin n, (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t (fun j => x j) i.succ) ^ 2) = _
    simp only [Fin.cons_zero, Fin.cons_succ]
  let height (x : D) := Real.sqrt (1 - ‖x.val‖ ^ 2)
  have height_sq (x : D) : (height x)^2 = 1 - ‖x.val‖ ^ 2 := by
    apply Real.sq_sqrt
    have hx : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    nlinarith [norm_nonneg x.val]
  have ch : Continuous height := Real.continuous_sqrt.comp
    (continuous_const.sub (continuous_subtype_val.norm.pow 2))
  let hem (c : ℝ) (hc : c^2 = 1) (x : D) : S :=
    ⟨put (c * height x) x.val, mem_sphere_zero_iff_norm.mpr (by
      have h := sq_put (c * height x) x.val
      rw [mul_pow, hc, one_mul, height_sq] at h
      nlinarith [norm_nonneg (put (c * height x) x.val)])⟩
  have continuous_hem (c : ℝ) (hc : c^2 = 1) : Continuous (hem c hc) := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
    apply continuous_pi
    refine Fin.cases ?_ (fun i => ?_)
    · change Continuous (fun x : D => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) (c * height x) (fun i => x.val i) 0)
      simp only [Fin.cons_zero]
      exact ch.const_mul c
    · change Continuous (fun x : D => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) (c * height x) (fun j => x.val j) i.succ)
      simp only [Fin.cons_succ]
      exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp
        (continuous_subtype_val : Continuous (fun x : D => (x.val : EuclideanSpace ℝ (Fin n))))
  have same_tail {c d : ℝ} {hc : c^2 = 1} {hd : d^2 = 1} {x y : D}
      (h : hem c hc x = hem d hd y) : x = y := by
    apply Subtype.ext
    simpa only [hem, tail_put] using congrArg (fun z : S => tail z.val) h
  let u := hem 1 (by norm_num)
  let v := hem (-1) (by norm_num)
  have hup : (1 : ℝ)^2 = 1 := by norm_num
  have hdn : (-1 : ℝ)^2 = 1 := by norm_num
  refine ⟨u, v, continuous_hem 1 hup, continuous_hem (-1) hdn, ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact same_tail (c := 1) (d := 1) (hc := hup) (hd := hup) (x := x) (y := y) h
  · intro x y h
    exact same_tail (c := -1) (d := -1) (hc := hdn) (hd := hdn) (x := x) (y := y) h
  · intro x y
    constructor
    · intro h
      have hxy : x = y := same_tail (c := 1) (d := -1) (hc := hup) (hd := hdn) (x := x) (y := y) h
      subst y
      have hh := congrArg (fun z : S => z.val 0) h
      change (put (1 * height x) x.val) 0 = (put (-1 * height x) x.val) 0 at hh
      rw [head_put, head_put] at hh
      have hzero : height x = 0 := by linarith
      have hs := height_sq x
      rw [hzero] at hs
      exact ⟨rfl, by nlinarith [norm_nonneg x.val]⟩
    · rintro ⟨hxy, hx⟩
      subst y
      apply Subtype.ext
      have hz : height x = 0 := by simp [height, hx]
      change put (1 * height x) x.val = put (-1 * height x) x.val
      simp [hz]
  · intro z
    have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    have hs := sq_put (z.val 0) (tail z.val)
    rw [reconstruct, hz] at hs
    have hb : ‖tail z.val‖ ≤ 1 := by nlinarith [sq_nonneg (z.val 0)]
    let x : D := ⟨tail z.val, mem_closedBall_zero_iff.mpr hb⟩
    have ht : height x = |z.val 0| := by
      change Real.sqrt (1 - ‖tail z.val‖ ^ 2) = |z.val 0|
      rw [show 1 - ‖tail z.val‖ ^ 2 = (z.val 0)^2 by linarith, Real.sqrt_sq_eq_abs]
    by_cases hpos : 0 ≤ z.val 0
    · left
      refine ⟨x, Subtype.ext ?_⟩
      change put (1 * height x) (tail z.val) = z.val
      simpa [ht, abs_of_nonneg hpos] using reconstruct z.val
    · right
      refine ⟨x, Subtype.ext ?_⟩
      change put (-1 * height x) (tail z.val) = z.val
      simpa [ht, abs_of_neg (lt_of_not_ge hpos)] using reconstruct z.val

/-- Every point has an open Euclidean chart whose inverse sends zero to that point. -/
theorem exists_centered_chart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (p : M) :
    ∃ χ : E → M, Topology.IsOpenEmbedding χ ∧ χ 0 = p := by
  let c := chartAt E p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds E p)
  let u : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall (c p) r
  have hs : u.source = Set.univ := OpenPartialHomeomorph.univBall_source _ _
  have ht : u.target = Metric.ball (c p) r := OpenPartialHomeomorph.univBall_target _ hr
  refine ⟨u.trans c.symm, (u.trans c.symm).isOpenEmbedding ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ u.source := hs.symm ▸ Set.mem_univ x
    exact ⟨hx, hball (ht ▸ u.map_source hx)⟩
  · change c.symm (u 0) = p
    rw [show u 0 = c p from OpenPartialHomeomorph.univBall_apply_zero _ _]
    exact c.left_inv (mem_chart_source E p)

open Metric
open scoped Topology

theorem contractible_closed_complement_of_chart_ball
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace M] [T2Space M]
    (χ : E → M) (hχ : Topology.IsOpenEmbedding χ)
    (hP : ContractibleSpace ↥(({χ 0} : Set M)ᶜ)) :
    ContractibleSpace ↥((χ '' ball 0 1)ᶜ) := by
  classical
  let P : Set M := ({χ 0} : Set M)ᶜ
  let K : Set M := (χ '' ball 0 1)ᶜ
  let C : Set M := χ '' closedBall 0 1
  have Cclosed : IsClosed C := ((isCompact_closedBall (0 : E) 1).image hχ.continuous).isClosed
  let e := hχ.toOpenPartialHomeomorph χ
  have right_inv {y : M} (hy : y ∈ Set.range χ) : χ (e.symm y) = y :=
    hχ.toOpenPartialHomeomorph_right_inv χ hy
  let rad (z : E) : E := max 1 ‖z‖⁻¹ • z
  have rad_id {z : E} (hz : 1 ≤ ‖z‖) : rad z = z := by
    simp only [rad, max_eq_left (inv_le_one_of_one_le₀ hz), one_smul]
  have rad_norm {z : E} (hn : z ≠ 0) : 1 ≤ ‖rad z‖ := by
    by_cases hz : 1 ≤ ‖z‖
    · simpa only [rad_id hz] using hz
    · have hpos := norm_pos_iff.mpr hn
      have hi := (one_le_inv₀ hpos).mpr (le_of_not_ge hz)
      change 1 ≤ ‖max 1 ‖z‖⁻¹ • z‖
      rw [max_eq_right hi, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
  have rad_cont {z : E} (hn : z ≠ 0) : ContinuousAt rad z :=
    (continuousAt_const.sup (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hn))).smul
      continuousAt_id
  let r (y : P) : M :=
    if y.val ∈ Set.range χ then χ (rad (e.symm y.val)) else y.val
  have outside_fixed (y : P) (hy : y.val ∈ K) : r y = y.val := by
    by_cases h : y.val ∈ Set.range χ
    · have hb : 1 ≤ ‖e.symm y.val‖ := by
        apply le_of_not_gt
        intro hz
        exact hy ⟨_, mem_ball_zero_iff.mpr hz, right_inv h⟩
      simp only [r, if_pos h, rad_id hb, right_inv h]
    · simp only [r, if_neg h]
  have nz (y : P) (hy : y.val ∈ Set.range χ) : e.symm y.val ≠ 0 := by
    intro hz
    have hn : y.val ≠ χ 0 := y.prop
    exact hn ((right_inv hy).symm.trans (congrArg χ hz))
  have r_mem (y : P) : r y ∈ K := by
    by_cases h : y.val ∈ Set.range χ
    · rintro ⟨z, hz, heq⟩
      have hrad : z = rad (e.symm y.val) := hχ.injective (by simpa only [r, if_pos h] using heq)
      rw [hrad] at hz
      exact (not_lt_of_ge (rad_norm (nz y h))) (mem_ball_zero_iff.mp hz)
    · rintro ⟨z, _, heq⟩
      exact h ⟨z, by simpa only [r, if_neg h] using heq⟩
  have ball_sub_C : χ '' ball 0 1 ⊆ C := Set.image_mono ball_subset_closedBall
  have r_cont : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y.val ∈ Set.range χ
    · have he : y.val ∈ e.symm.source := by
        change y.val ∈ (hχ.toOpenPartialHomeomorph χ).target
        rwa [hχ.toOpenPartialHomeomorph_target]
      have hc : ContinuousAt (fun x : P => χ (rad (e.symm x.val))) y :=
        hχ.continuous.continuousAt.comp (f := fun x : P => rad (e.symm x.val)) (x := y)
          ((rad_cont (nz y hy)).comp (f := fun x : P => e.symm x.val) (x := y)
            ((e.symm.continuousAt he).comp (f := fun x : P => x.val) (x := y)
              continuous_subtype_val.continuousAt))
      apply hc.congr_of_eventuallyEq
      filter_upwards [(hχ.isOpen_range.preimage continuous_subtype_val).mem_nhds hy] with x hx
      exact if_pos hx
    · have hyC : y.val ∈ Cᶜ := fun ⟨z, _, heq⟩ => hy ⟨z, heq⟩
      apply (continuous_subtype_val.continuousAt : ContinuousAt ((↑) : P → M) y).congr_of_eventuallyEq
      filter_upwards [(Cclosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hyC] with x hx
      exact outside_fixed x (fun hin => hx (ball_sub_C hin))
  have hKP : K ⊆ P := by
    intro y hy
    change y ≠ χ 0
    rintro rfl
    exact hy ⟨0, mem_ball_self zero_lt_one, rfl⟩
  let inc : ContinuousMap K P := ⟨Set.inclusion hKP, continuous_inclusion hKP⟩
  let ret : ContinuousMap P K := ⟨fun y => ⟨r y, r_mem y⟩, r_cont.subtype_mk _⟩
  have eqid : (ret.comp (ContinuousMap.id P)).comp inc = ContinuousMap.id K := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact outside_fixed (inc x) x.prop
  have : ContractibleSpace P := hP
  apply (contractible_iff_id_nullhomotopic K).mpr
  rw [← eqid]
  exact ((id_nullhomotopic P).comp_right ret).comp_left inc

theorem boundary_transition {S M : Type*} [TopologicalSpace S] [CompactSpace S]
    [TopologicalSpace M] [T2Space M] (p q : S → M)
    (hp : Continuous p) (hq : Continuous q) (ip : Injective p) (iq : Injective q)
    (hr : range p = range q) : ∃ t : S ≃ₜ S, ∀ s, p s = q (t s) := by
  let P := (hp.isClosedEmbedding ip).toIsEmbedding.toHomeomorph
  let Q := (hq.isClosedEmbedding iq).toIsEmbedding.toHomeomorph
  let T := P.trans ((Homeomorph.setCongr hr).trans Q.symm)
  refine ⟨T, fun s => ?_⟩
  have he : Q (T s) = Homeomorph.setCongr hr (P s) := Q.apply_symm_apply _
  exact (congrArg Subtype.val he).symm

/-- A disk exterior need only match the chart boundary as a set. -/
theorem sphere_of_disk_exterior {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    (χ : EuclideanSpace ℝ (Fin n) → M) (hχ : IsOpenEmbedding χ)
    (g : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → M)
    (hg : Continuous g) (ig : Injective g)
    (exterior : range g = (χ '' ball 0 1)ᶜ)
    (boundary : (g '' {x | ‖(x.val : EuclideanSpace ℝ (Fin n))‖ = 1}) =
      χ '' sphere 0 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := by
  let E := EuclideanSpace ℝ (Fin n)
  let D := closedBall (0 : E) 1
  let S := sphere (0 : E) 1
  let j : S → D := fun s => ⟨s.val, sphere_subset_closedBall s.prop⟩
  let f : D → M := fun x => χ x.val
  have cj : Continuous j := continuous_subtype_val.subtype_mk _
  have ij : Injective j := by
    intro s u h
    apply Subtype.ext
    exact congrArg (fun x : D => (x.val : E)) h
  have cf : Continuous f := hχ.continuous.comp continuous_subtype_val
  have if' : Injective f := hχ.injective.comp Subtype.val_injective
  have hr : range (g ∘ j) = range (f ∘ j) := by
    have hj : range j = {x : D | ‖(x.val : E)‖ = 1} := by
      ext x
      constructor
      · rintro ⟨s,rfl⟩
        exact mem_sphere_zero_iff_norm.mp s.prop
      · intro hx
        exact ⟨⟨x.val,mem_sphere_zero_iff_norm.mpr hx⟩,Subtype.ext rfl⟩
    calc
      range (g ∘ j) = g '' range j := Set.range_comp ..
      _ = χ '' sphere 0 1 := by rw [hj]; exact boundary
      _ = range (f ∘ j) := by
        change χ '' sphere 0 1 = range (χ ∘ (Subtype.val : S → E))
        rw [Set.range_comp, Subtype.range_coe]
  obtain ⟨t, ht⟩ := boundary_transition (g ∘ j) (f ∘ j) (hg.comp cj) (cf.comp cj)
    (ig.comp ij) (if'.comp ij) hr
  obtain ⟨b,_,hb⟩ := extend_sphere_to_ball t
  let k : D → M := g ∘ b.symm
  have ik : Injective k := ig.comp b.symm.injective
  have hsame (x : D) (hx : ‖(x.val : E)‖ = 1) : f x = k x := by
    let s : S := ⟨x.val,mem_sphere_zero_iff_norm.mpr hx⟩
    have hbx : b (j (t.symm s)) = x := by
      apply Subtype.ext
      exact (hb (t.symm s)).trans (congrArg Subtype.val (t.apply_symm_apply s))
    have htx : f (j (t (t.symm s))) = f x := congrArg (f ∘ j) (t.apply_symm_apply s)
    have h := (ht (t.symm s)).trans htx
    change f x = g (b.symm x)
    have hinv : b.symm x = j (t.symm s) := by rw [← hbx, b.symm_apply_apply]
    rw [hinv]
    exact h.symm
  have hcross (x y : D) : f x = k y ↔ x = y ∧ ‖(x.val : E)‖ = 1 := by
    constructor
    · intro h
      have he : k y ∈ (χ '' ball 0 1)ᶜ := exterior ▸ mem_range_self (b.symm y)
      have hx : ‖(x.val : E)‖ = 1 := by
        apply le_antisymm (mem_closedBall_zero_iff.mp x.prop)
        by_contra! hlt
        exact he (h ▸ ⟨x.val,mem_ball_zero_iff.mpr hlt,rfl⟩)
      exact ⟨ik ((hsame x hx).symm.trans h), hx⟩
    · rintro ⟨rfl,hx⟩
      exact hsame _ hx
  have covers : Surjective (Sum.elim f k) := by
    intro m
    by_cases h : m ∈ χ '' ball 0 1
    · obtain ⟨x,hx,rfl⟩ := h
      exact ⟨Sum.inl ⟨x,ball_subset_closedBall hx⟩,rfl⟩
    · have hmem : m ∈ range g := exterior.symm ▸ h
      obtain ⟨x,rfl⟩ := hmem
      exact ⟨Sum.inr (b x),congrArg g (b.symm_apply_apply x)⟩
  obtain ⟨u,v,cu,cv,iu,iv,hmodel,hall⟩ := hemisphereModel n
  apply homeomorph_of_two_pieces f k u v cf (hg.comp b.symm.continuous) cu cv
    if' ik iu iv covers
  · intro s
    rcases hall s with ⟨x,hx⟩ | ⟨y,hy⟩
    · exact ⟨Sum.inl x,hx⟩
    · exact ⟨Sum.inr y,hy⟩
  · exact fun x y => (hcross x y).trans (hmodel x y).symm

/-- A compact manifold with a contractible puncture has a compact, contractible
chart exterior. This connects the first step below to the first two steps of R2. -/
theorem chart_exterior_of_contractible_puncture {n : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (p : M) (hp : ContractibleSpace ↥(({p} : Set M)ᶜ)) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding χ ∧
      IsCompact (χ '' ball 0 1)ᶜ ∧ ContractibleSpace ↥((χ '' ball 0 1)ᶜ) := by
  obtain ⟨χ,hχ,h0⟩ := exists_centered_chart (EuclideanSpace ℝ (Fin n)) p
  rw [← h0] at hp
  exact ⟨χ,hχ,(hχ.isOpenMap _ isOpen_ball).isClosed_compl.isCompact,
    contractible_closed_complement_of_chart_ball χ hχ hp⟩

/-- A homotopy sphere has a chart ball with compact, contractible exterior. -/
def H1 : Prop := ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
    M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 →
    ∃ χ : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding χ ∧
      IsCompact (χ '' ball 0 1)ᶜ ∧ ContractibleSpace ↥((χ '' ball 0 1)ᶜ)

/-- Relative disk recognition. A compact contractible exterior of a round chart ball
admits a closed-disk parametrization carrying boundary onto boundary. -/
def H2 : Prop := ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
    ∀ χ : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding χ →
    IsCompact (χ '' ball 0 1)ᶜ → ContractibleSpace ↥((χ '' ball 0 1)ᶜ) →
    ∃ g : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → M,
      Continuous g ∧ Injective g ∧ range g = (χ '' ball 0 1)ᶜ ∧
      g '' {x | ‖x.val‖ = 1} = χ '' sphere 0 1

theorem main : H1 → H2 →
    type_of% @PoincareConjecture.poincare_conjecture.variants.dimension_ge_five := by
  intro hexterior hrecognize n hn M _ _ _ e
  obtain ⟨χ,hχ,hcompact,hcontract⟩ := hexterior n hn M e
  obtain ⟨g,hg,ig,hr,hb⟩ := hrecognize n hn M χ hχ hcompact hcontract
  exact sphere_of_disk_exterior χ hχ g hg ig hr hb

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3

