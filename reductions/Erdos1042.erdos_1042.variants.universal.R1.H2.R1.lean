import OMAReductions.R_Erdos1042_erdos_1042_variants_universal_R1
import Mathlib

/-! The level-curve case of Ghosh and Ramachandran, Proposition 2.3
(arXiv:2312.13673), formalized here via covering maps and simultaneous phase
recurrence. On a disk containing no critical values, each sheet has exactly
one root. For a monic P, arbitrarily large powers put all critical phases in
the right half-plane, so P^n+1 has maximal component count and every root
lies on the unit level curve of P. Helly reduces the remaining small-diameter
disk obstruction to an explicit triple. -/
open Polynomial Set Filter Metric
open scoped Topology
noncomputable section
namespace LemniscateCover
private theorem components_of_critical_values (p : ℂ[X]) (hmon : p.Monic)
    (hcrit : ∀ z, p.derivative.eval z = 0 → 1 ≤ ‖p.eval z‖) :
    Erdos1042.numComponents p = p.natDegree := by
  classical
  let D := ball (0 : ℂ) 1
  let U := p.eval ⁻¹' D
  let zeroD : D := ⟨0,by simp [D]⟩
  letI : ContractibleSpace D := contractibleSpace_ball (by norm_num : (0:ℝ)<1)
  letI : LocallyPathConnectedSpace D := isOpen_ball.locallyPathConnectedSpace
  have cov : IsCoveringMapOn p.eval D := p.isCoveringMapOn_eval.mono (by
    rintro w hw ⟨z,hz,rfl⟩
    exact (not_lt_of_ge (hcrit z hz)) (by simpa [D,mem_ball] using hw))
  let proj : U → D := D.restrictPreimage p.eval
  have cov' : IsCoveringMap proj := cov.isCoveringMap_restrictPreimage
  have lift (a : D) (z : ℂ) (hz : p.eval z = a) :
      ∃ g : C(D,ℂ), g a = z ∧ ∀ b : D, p.eval (g b) = b := by
    let inc : C(D,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
    obtain ⟨g,⟨hga,hg⟩,_⟩ := cov.existsUnique_continuousMap_lifts inc (a₀:=a) (e₀:=z) hz (fun b => b.property)
    exact ⟨g,hga,fun b => congrFun hg b⟩
  let R := p.roots.toFinset
  let A (z : R) := connectedComponentIn U (z:ℂ)
  have hzero (z : R) : p.eval (z:ℂ) = 0 := (mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.property)
  have hmem (z : R) : (z:ℂ) ∈ U := by change p.eval _ ∈ D; rw [hzero]; exact zeroD.property
  have inj : Function.Injective A := by
    intro x y he
    obtain ⟨g,hg0,hg⟩ := lift zeroD x (hzero x)
    let T := A x
    letI : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    let f (w : T) : U := ⟨w.val,connectedComponentIn_subset U _ w.property⟩
    let g' (b : D) : U := ⟨g b,show p.eval (g b) ∈ D from (hg b) ▸ b.property⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have hg' : Continuous g' := g.continuous.subtype_mk _
    have eqMap : proj ∘ (g' ∘ proj ∘ f) = proj ∘ f := by
      funext w
      apply Subtype.ext
      exact hg (proj (f w))
    let tx : T := ⟨(x:ℂ),mem_connectedComponentIn (hmem x)⟩
    let ty : T := ⟨(y:ℂ),by change (y:ℂ) ∈ A x; rw [he]; exact mem_connectedComponentIn (hmem y)⟩
    have hx : proj (f tx) = zeroD := Subtype.ext (hzero x)
    have hy : proj (f ty) = zeroD := Subtype.ext (hzero y)
    have heq := cov'.eq_of_comp_eq (hg'.comp (cov'.continuous.comp hf)) hf eqMap tx
      (show g' (proj (f tx)) = f tx by apply Subtype.ext; simpa [g',hx] using hg0)
    have hy' := congrArg Subtype.val (congrFun heq ty)
    change g (proj (f ty)) = (y:ℂ) at hy'
    rw [hy,hg0] at hy'
    exact Subtype.ext hy'
  have hcover : Erdos1047.componentsIn U = Set.range A := by
    ext T
    constructor
    · rintro ⟨z,hz,rfl⟩
      let a : D := ⟨p.eval z,hz⟩
      obtain ⟨g,hga,hg⟩ := lift a z rfl
      have hsub : Set.range g ⊆ U := by rintro _ ⟨b,rfl⟩; change p.eval (g b) ∈ D; rw [hg]; exact b.property
      have hx : z ∈ Set.range g := ⟨a,hga⟩
      have hconn := (isPreconnected_range g.continuous).subset_connectedComponentIn hx hsub
      let x : R := ⟨g zeroD,Multiset.mem_toFinset.mpr ((mem_roots hmon.ne_zero).mpr (hg zeroD))⟩
      exact ⟨x,(connectedComponentIn_eq (hconn (Set.mem_range_self zeroD))).symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x,hmem x,rfl⟩
  have hsep : p.Separable := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ p p.derivative).mpr
    intro z
    simp only [aeval_def,eval₂_id]
    by_cases hh : p.eval z = 0
    · right
      intro hd
      have H := hcrit z hd
      rw [hh,norm_zero] at H
      linarith
    · exact Or.inl hh
  have hU : Erdos1047.strictSublevelSet p 1 = U := by ext z; simp [U,D,Erdos1047.strictSublevelSet,mem_ball]
  change (Erdos1047.componentsIn _).ncard = _
  rw [hU,hcover,Set.ncard_range_of_injective inj]
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  change p.roots.toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),IsAlgClosed.card_roots_eq_natDegree]
end LemniscateCover
end
open Polynomial Set Filter Metric
open scoped Topology
noncomputable section
namespace LemniscateCover
private theorem recurrent_re {ι : Type*} [Fintype ι] (v : ι → ℂ) (N : ℕ) :
    ∃ n ≥ N, ∀ i, 0 ≤ ((v i)^n).re := by
  let u (i : ι) : Circle := Circle.exp (v i).arg
  obtain ⟨a,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => u^n)
  let d (j : ℕ) := φ (N+j) - φ j
  have hd (j : ℕ) : N ≤ d j := by have := hφ.add_le_nat N j; dsimp [d]; omega
  have hr (j : ℕ) : u^(d j) = u^(φ (N+j)) / u^(φ j) := by
    rw [div_eq_mul_inv,← pow_sub _ (hφ.monotone (by omega : j ≤ N+j))]
  have hlim' : Tendsto (fun j => u^(d j)) atTop (𝓝 1) := by
    simp_rw [hr]
    have hshift : Tendsto (fun j : ℕ => N+j) atTop atTop := tendsto_atTop.2 fun k => (eventually_ge_atTop k).mono fun j hj => by omega
    have H : Tendsto (fun j : ℕ => u^(φ (N+j)) / u^(φ j)) atTop (𝓝 (a/a)) := (hlim.comp hshift).div' hlim
    simpa using H
  have hre (i : ι) : ∀ᶠ j in atTop, 0 < (((u i)^(d j) : Circle) : ℂ).re := by
    have hc : Continuous (fun x : ι → Circle => ((x i : Circle):ℂ).re) :=
      Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_apply i))
    have h := (hc.tendsto 1).comp hlim'
    exact h.eventually (Ioi_mem_nhds (by simp : (0:ℝ) < (((1 : ι → Circle) i : Circle):ℂ).re))
  obtain ⟨j,hj⟩ := (Filter.eventually_all.mpr hre).exists
  refine ⟨d j,hd j,fun i => ?_⟩
  have hv : v i = (‖v i‖ : ℂ)*(u i : ℂ) := (Complex.norm_mul_exp_arg_mul_I (v i)).symm
  conv_rhs => rw [hv,mul_pow,← Complex.ofReal_pow,Complex.re_ofReal_mul]
  exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (hj i).le

private theorem lemniscate_case (G : Set ℂ) (P : ℂ[X]) (hP : P.Monic) (hdP : 0 < P.natDegree)
    (hlevel : ∀ z, ‖P.eval z‖=1 → z ∈ G) :
    ∃ᶠ m : ℕ in atTop, ∃ f : ℂ[X], Erdos1042.MonicWithRootsIn G m f ∧ Erdos1042.numComponents f=m := by
  classical
  rw [frequently_atTop]
  intro k
  let R := P.derivative.roots.toFinset
  obtain ⟨n,hn,hphase⟩ := recurrent_re (fun z : R => P.eval (z:ℂ)) (k+2)
  have hn0 : 0 < n := by omega
  have hd : 0 < (P^n).natDegree := by rw [natDegree_pow]; positivity
  let f := P^n + 1
  have hdm : f.natDegree = (P^n).natDegree := natDegree_add_eq_left_of_natDegree_lt (by simpa using hd)
  have hmon : f.Monic := (hP.pow n).add_of_left (degree_lt_degree (by simpa using hd : (1:ℂ[X]).natDegree < (P^n).natDegree))
  have hcrit (z : ℂ) (hz : f.derivative.eval z = 0) : 1 ≤ ‖f.eval z‖ := by
    have hzero : P.eval z = 0 ∨ P.derivative.eval z = 0 := by
      simpa [f,derivative_pow,show n ≠ 0 by omega,show n-1 ≠ 0 by omega] using hz
    rcases hzero with hzero | hzero
    · simp [f,hzero,show n≠0 by omega]
    · let i : R := ⟨z,Multiset.mem_toFinset.mpr ((mem_roots (derivative_ne_zero.mpr hdP.ne')).mpr hzero)⟩
      have hr : 0 ≤ ((P.eval z)^n).re := hphase i
      apply le_trans _ (Complex.re_le_norm _)
      simp [f,hr]
  refine ⟨f.natDegree,?_,f,⟨hmon,rfl,?_⟩,components_of_critical_values f hmon hcrit⟩
  · rw [hdm,natDegree_pow]
    nlinarith
  · intro z hz
    have he := (mem_roots hmon.ne_zero).mp hz
    have he' : (P.eval z)^n = -1 := by simpa [f,eq_neg_iff_add_eq_zero] using he
    have he'' : ‖P.eval z‖^n = 1 := by simpa using congrArg norm he'
    apply hlevel
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1) (by omega : n≠0)).mp (by simpa using he'')
end LemniscateCover
end

open Set Metric
private lemma LemniscateCover.obstructing_triangle (G : Set ℂ)
    (hd : ∀ z ∈ G, ∀ w ∈ G, dist z w ≤ 2) (hdisc : ∀ c : ℂ, ¬ G ⊆ closedBall c 1) :
    ∃ T : Finset ℂ, T.card = 3 ∧ (T:Set ℂ) ⊆ G ∧ ∀ c : ℂ, ¬ (T:Set ℂ) ⊆ closedBall c 1 := by
  classical
  let F (z : G) := closedBall (z:ℂ) 1
  have he : ¬ (⋂ z : G, F z).Nonempty := by
    rintro ⟨c,hc⟩
    apply hdisc c
    intro w hw
    have H := mem_iInter.mp hc (⟨w,hw⟩ : G)
    simpa [F,mem_closedBall,dist_comm] using H
  have small := mt (Convex.helly_theorem_compact' (𝕜:=ℝ) (F:=F)
    (fun _ => convex_closedBall _ _) (fun _ => isCompact_closedBall _ _)) he
  push_neg at small
  obtain ⟨I,hI,hn⟩ := small
  have hcard : I.card ≤ 3 := by simpa [Complex.finrank_real_complex] using hI
  have bad (c : ℂ) : ¬ ∀ i ∈ I, dist c (i:ℂ) ≤ 1 := by
    intro H
    have hi : c ∈ ⋂ i ∈ I, F i := by simp only [mem_iInter]; exact H
    exact (Set.not_nonempty_iff_eq_empty.mpr hn) ⟨c,hi⟩
  have size : I.card = 3 := by
    by_contra hs
    have hor : I.card=0 ∨ I.card=1 ∨ I.card=2 := by omega
    rcases hor with h | h | h
    · have he := Finset.card_eq_zero.mp h
      exact bad 0 (by simp [he])
    · obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp h
      exact bad x (by simp)
    · obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp h
      apply bad (midpoint ℝ (x:ℂ) (y:ℂ))
      have H := hd x x.property y y.property
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro i (rfl | rfl)
      · rw [dist_midpoint_left]
        norm_num
        linarith
      · rw [dist_midpoint_right]
        norm_num
        linarith
  let e : G ↪ ℂ := Function.Embedding.subtype _
  refine ⟨I.map e,by simpa using size,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    exact i.property
  · intro c hc
    apply bad c
    intro i hi
    exact (dist_comm c (i:ℂ)).trans_le (hc (Finset.mem_map.mpr ⟨i,hi,rfl⟩))


open Filter Set Metric Polynomial Erdos1042
noncomputable section
namespace OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1

/-- A diameter of at most two, with a specific three-point obstruction. -/
def H1 : Prop := ∀ (G : Set ℂ) (r : ℝ), 1 < r → r ≤ 2 →
  IsCompact G → transfiniteDiameter G = 1 → (0:ℂ) ∈ G → (r:ℂ) ∈ G →
  (∀ z ∈ G, ∀ w ∈ G, dist z w ≤ r) → (∃ z ∈ G, z.im ≠ 0) →
  ∀ T : Finset ℂ, T.card=3 → (T:Set ℂ) ⊆ G →
  (∀ c : ℂ, ¬ (T:Set ℂ) ⊆ closedBall c 1) → ((¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) ∧
  (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖=1 ∧ 1 ≤ s ∧
    ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G) ∧
  ¬ ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖=1 → z ∈ G) → (∃ᶠ n : ℕ in atTop, ∃ p : ℂ[X], MonicWithRootsIn G n p ∧
    ∀ z, p.derivative.eval z=0 → 1 ≤ ‖p.eval z‖)

/-- Two fixed diameter endpoints at distance strictly greater than two. -/
def H2 : Prop := ∀ (G : Set ℂ) (r : ℝ), 2 < r →
  IsCompact G → transfiniteDiameter G = 1 → (0:ℂ) ∈ G → (r:ℂ) ∈ G →
  (∀ z ∈ G, ∀ w ∈ G, dist z w ≤ r) → (∃ z ∈ G, z.im ≠ 0) →
  ((¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) ∧
  (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖=1 ∧ 1 ≤ s ∧
    ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G) ∧
  ¬ ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖=1 → z ∈ G) → (∃ᶠ n : ℕ in atTop, ∃ p : ℂ[X], MonicWithRootsIn G n p ∧
    ∀ z, p.derivative.eval z=0 → 1 ≤ ‖p.eval z‖)

theorem main : H1 → H2 → OMA.R_Erdos1042_erdos_1042_variants_universal_R1.H2 := by
  intro small wide G r hr hc hcap hz hb hd hp hdisc hseg hreg
  by_cases hlevel : ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖=1 → z ∈ G
  · obtain ⟨P,hP,hD,hL⟩ := hlevel
    exact LemniscateCover.lemniscate_case G P hP hD hL
  have ex : ((¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) ∧
  (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖=1 ∧ 1 ≤ s ∧
    ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G) ∧
  ¬ ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖=1 → z ∈ G) := ⟨hseg,hreg,hlevel⟩
  suffices H : (∃ᶠ n : ℕ in atTop, ∃ p : ℂ[X], MonicWithRootsIn G n p ∧
    ∀ z, p.derivative.eval z=0 → 1 ≤ ‖p.eval z‖) by
    exact H.mono fun n ⟨p,hp,hh⟩ => ⟨p,hp,(LemniscateCover.components_of_critical_values p hp.1 hh).trans hp.2.1⟩
  rcases le_or_gt r 2 with hl | hl
  · obtain ⟨T,hT,hsub,hbad⟩ := LemniscateCover.obstructing_triangle G (fun z h w hw => (hd z h w hw).trans hl) hdisc
    exact small G r hr hl hc hcap hz hb hd hp T hT hsub hbad ex
  · exact wide G r hl hc hcap hz hb hd hp ex
end OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1
end
