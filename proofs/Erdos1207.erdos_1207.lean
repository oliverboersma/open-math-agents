import FormalConjectures.ErdosProblems.«1207»
import Mathlib

/-!
# Erdos Problem 1207

The core of this file (namespace OMA1207 and the surrounding auxiliary namespaces) is adapted
from https://github.com/tadamcz/erdos1207 (commit 228fcd87), Apache License 2.0.
NOTICE of that work: Copyright 2026 Tom Adamczewski / Epoch AI. It includes two definitions
(Set.Triplewise and IsIsosceles) copied from Formal Conjectures, Copyright 2025 The Formal
Conjectures Authors, Apache License 2.0. The formal statement was given to the AI system by the
FrontierMath Erdos benchmark (LeanOpenProblems, Epoch AI, MIT License); the Lean proof was produced
by a pre-release version of GPT-6 Astra (OpenAI).
Changes made here: declarations not needed for the main theorem were removed; comments were
removed; local names were shortened and indentation halved to fit the 512 KiB file limit; the
namespace Erdos1207 became OMA1207 and Set.Triplewise / IsIsosceles were renamed to avoid
clashing with the upstream statement file; local notations, attribute and set_option commands were
rewritten into equivalent allowed forms; and the proofs were repaired for the current Lean and
Mathlib versions. The final section derives the upstream statement.
-/
open Filter
namespace Set
variable {α:Type*}
protected def OMATriplewise (s:Set α) (r:α → α → α → Prop):Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z
end Set
def OMAIsIsosceles {α:Type*} [Dist α] (p q r:α):Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q
noncomputable instance OMA1207.instFintypeUnitsTorsion (L:Type*) [Field L] [NumberField L] :
    Fintype (NumberField.Units.torsion L) :=
  Fintype.ofFinite _
instance OMA1207.instGroupAddAut {A:Type*} [Add A]:Group (AddAut A) where
  mul g h:=AddEquiv.trans h g
  one:=AddEquiv.refl _
  inv:=AddEquiv.symm
  mul_assoc _ _ _:=rfl
  one_mul _:=rfl
  mul_one _:=rfl
  inv_mul_cancel:=AddEquiv.self_trans_symm
namespace OMA1207
def IsIsoscelesFree {α:Type*} [Dist α] (A:Set α):Prop :=
  A.OMATriplewise fun x y z => ¬ OMAIsIsosceles x y z
noncomputable def P (d n:ℕ):ℕ :=
  sInf {m:ℕ | ∃ S:Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k:ℕ | ∃ A:Finset (EuclideanSpace ℝ (Fin d)),
      A ⊆ S ∧ IsIsoscelesFree (A:Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}}
end OMA1207
open MeasureTheory
open scoped ENNReal
namespace z8u
lemma zim {G E:Type*} [AddGroup G] [AddAction G E]
    (s:Set E) (U:Finset G)
    (hU:∀ g h:G, ∀ x:E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) (x:E) :
    (∑' g:G, s.indicator (fun _ => (1:ℝ≥0∞)) (g +ᵥ x)) ≤ U.card:=by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro T
  have hc:(T.filter (fun g => g +ᵥ x ∈ s)).card ≤ U.card:=by
    let V:=T.filter (fun g => g +ᵥ x ∈ s)
    by_cases hV:V.Nonempty
    · obtain ⟨g₀,hg₀⟩:=hV
      have hg₀':=(Finset.mem_filter.mp hg₀).2
      apply Finset.card_le_card_of_injOn (fun g => g-g₀)
      · intro g hg
        exact hU g g₀ x (Finset.mem_filter.mp hg).2 hg₀'
      · intro g _ h _ heq
        exact sub_left_injective heq
    · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (Nat.zero_le _)
  have hs:(∑ g ∈ T, s.indicator (fun _ => (1:ℝ≥0∞)) (g +ᵥ x)) =
      ((T.filter (fun g => g +ᵥ x ∈ s)).card:ℝ≥0∞):=by
    simp only [Set.indicator_apply,Finset.sum_boole]
  rw [hs]
  exact_mod_cast hc
lemma zf0 {G E:Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ:Measure E) [VAddInvariantMeasure G E μ]
    (F s:Set E) (hF:IsAddFundamentalDomain G F μ) (hs:MeasurableSet s)
    (U:Finset G)
    (hU:∀ g h:G, ∀ x:E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) :
    μ s ≤ (U.card:ℝ≥0∞) * μ F:=by
  have hm (g:G):Measurable (fun x:E => s.indicator (fun _ => (1:ℝ≥0∞)) (g +ᵥ x)) :=
    (measurable_const.indicator hs).comp (measurable_const_vadd g)
  calc
    μ s = ∫⁻ x, s.indicator (fun _ => (1:ℝ≥0∞)) x ∂μ :=
      (lintegral_indicator_one hs).symm
    _ = ∑' g:G, ∫⁻ x in F, s.indicator (fun _ => (1:ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      hF.lintegral_eq_tsum'' _
    _ = ∫⁻ x in F, ∑' g:G, s.indicator (fun _ => (1:ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      (lintegral_tsum (fun g => (hm g).aemeasurable)).symm
    _ ≤ ∫⁻ _x in F, (U.card:ℝ≥0∞) ∂μ :=
      lintegral_mono (zim s U hU)
    _ = (U.card:ℝ≥0∞) * μ F:=by simp
lemma zd5 {ι:Type*} [Fintype ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (U:Finset L) (t:ℝ) (ht:0 ≤ t)
    (hU:∀ x:L, x ∈ U ↔ ∀ i, |(x:ι → ℝ) i| ≤ t) :
    t^(Fintype.card ι) ≤ (U.card:ℝ) * ZLattice.covolume L:=by
  classical
  letI:MeasurableVAdd L (ι → ℝ) :=
    (inferInstance:MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI:VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance:VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b:=Module.Free.chooseBasis ℤ L
  let F:=ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF:IsAddFundamentalDomain L F volume:=ZLattice.isAddFundamentalDomain b volume
  let s:Set (ι → ℝ):=Set.pi Set.univ (fun _ => Set.Icc (-t/2) (t/2))
  have hs:MeasurableSet s:=MeasurableSet.pi (Set.to_countable _) (by intro i _; exact measurableSet_Icc)
  have hdiff:∀ g h:L, ∀ x:ι → ℝ, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U:=by
    intro g h x hg hh
    apply (hU _).mpr
    intro i
    have hg':=Set.mem_pi.mp hg i (Set.mem_univ i)
    have hh':=Set.mem_pi.mp hh i (Set.mem_univ i)
    change -t/2 ≤ (g:ι → ℝ) i + x i ∧ (g:ι → ℝ) i + x i ≤ t/2 at hg'
    change -t/2 ≤ (h:ι → ℝ) i + x i ∧ (h:ι → ℝ) i + x i ≤ t/2 at hh'
    change |(g:ι → ℝ) i - (h:ι → ℝ) i| ≤ t
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hm:volume s = (ENNReal.ofReal t)^(Fintype.card ι):=by
    rw [volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc]
    have he:t/2 - -t/2 = t:=by ring
    simp only [he,Finset.prod_const,Finset.card_univ]
  have hfin:volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have h:=zf0 volume F s hF hs U hdiff
  have hreal:=ENNReal.toReal_mono (by finiteness:(U.card:ℝ≥0∞)*volume F ≠ ⊤) h
  rw [hm,ENNReal.toReal_pow,ENNReal.toReal_ofReal ht,ENNReal.toReal_mul,ENNReal.toReal_natCast] at hreal
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hreal
end z8u
open scoped Pointwise
namespace zbv
lemma zci {G ι Q:Type*} [AddCommGroup G] [DecidableEq G] [Fintype Q]
    (U:Finset G) (f:G →+ (ι → ℝ)) (t:ℝ) (ht:0 ≤ t)
    (hU:∀ x, x ∈ U ↔ ∀ i, |f x i| ≤ t)
    (q:G → Q) (hroot:∀ x y, q x = q y → ∃ z, (5:ℕ) • z = x-y) :
    (U-U).card ≤ Fintype.card Q * U.card:=by
  classical
  let V:Finset G:=U-U
  have hV:∀ x ∈ V, ∀ i, |f x i| ≤ 2*t:=by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_sub.mp hx
    calc
      |f (a-b) i| = |f a i-f b i|:=by simp
      _ ≤ |f a i|+|f b i|:=abs_sub _ _
      _ ≤ t+t:=add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t:=by ring
  have hf:∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card:=by
    intro c hc
    let T:Finset G:=V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩:=Finset.mem_image.mp hc
    have hex:∀ x ∈ T, ∃ z ∈ U, (5:ℕ) • z = x-x₀:=by
      intro x hx
      obtain ⟨hx,hqx⟩:=Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩:=hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he:5 * f z i = f x i - f x₀ i:=by
        have hh:=congrArg (fun w => f w i) hz
        simpa using hh
      have hb:|f x i - f x₀ i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g:T → U:=fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x:T):(5:ℕ) • (g x:G) = (x:G)-x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj:Function.Injective g:=by
      intro x y hxy
      apply Subtype.ext
      have hh:=congrArg (fun z:U => (5:ℕ) • (z:G)) hxy
      try dsimp only at hh
      rw [hg,hg] at hh
      exact sub_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U-U).card ≤ U.card * (V.image q).card:=Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q:=Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card:=Nat.mul_comm _ _
end zbv
namespace zhf
open scoped Pointwise
lemma zm1 {ι:Type*} [Fintype ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (t:ℝ) (ht:0 ≤ t):{x:L | ∀ i, |(x:ι → ℝ) i| ≤ t}.Finite:=by
  letI:DiscreteTopology L.toAddSubgroup:=(inferInstance:DiscreteTopology L)
  have hclosed:IsClosed (L:Set (ι → ℝ)):=by
    change IsClosed (L.toAddSubgroup:Set (ι → ℝ))
    exact AddSubgroup.isClosed_of_discrete
  have hfin:(Metric.closedBall 0 t ∩ (L:Set (ι → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hclosed
  apply Set.Finite.of_finite_image (f:=fun x:L => (x:ι → ℝ)) _ Subtype.val_injective.injOn
  apply hfin.subset
  rintro x ⟨y,hy,rfl⟩
  refine ⟨?_,y.property⟩
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg ht]
  simpa only [Real.norm_eq_abs, Set.mem_ofPred_eq] using hy
lemma zci {ι:Type*} [Fintype ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (U:Finset L) (t:ℝ) (ht:0 ≤ t)
    (hU:∀ x:L, x ∈ U ↔ ∀ i, |(x:ι → ℝ) i| ≤ t) :
    (U-U).card ≤ 5^(Fintype.card ι) * U.card:=by
  classical
  let e:=(IsZLattice.basis L).equivFun
  let q:L → (ι → ZMod 5):=fun x i => e x i
  have hroot:∀ x y, q x = q y → ∃ z, (5:ℕ) • z = x-y:=by
    intro x y hxy
    refine ⟨e.symm (fun i => (e x i-e y i)/5),?_⟩
    apply e.injective
    ext i
    have hdiv:(5:ℤ) ∣ e x i-e y i:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by
      rw [Int.cast_sub,sub_eq_zero]
      exact congrFun hxy i)
    simpa using Int.mul_ediv_cancel' hdiv
  simpa [Fintype.card_pi,ZMod.card] using
    zbv.zci U L.subtype.toAddMonoidHom t ht hU q hroot
lemma z6z {ι:Type*} [Fintype ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (t:ℝ) (ht:0 ≤ t) :
    ∃ U:Finset L,
      (∀ x:L, x ∈ U ↔ ∀ i, |(x:ι → ℝ) i| ≤ t) ∧
      t^(Fintype.card ι) ≤ (U.card:ℝ)*ZLattice.covolume L ∧
      (U-U).card ≤ 5^(Fintype.card ι)*U.card:=by
  classical
  let U:=(zm1 L t ht).toFinset
  have hU:∀ x:L, x ∈ U ↔ ∀ i, |(x:ι → ℝ) i| ≤ t:=by simp [U]
  exact ⟨U,hU,z8u.zd5 L U t ht hU,
    zci L U t ht hU⟩
end zhf
namespace z5t
open scoped BigOperators Pointwise
lemma zke (r:ℕ):2*r+1 ≤ 3^r:=by
  induction r with
  | zero => norm_num
  | succ r ih => rw [pow_succ]; nlinarith
lemma zir {G ι:Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]
    (S:Finset G) (hS:S.Nonempty) (f:G →+ (ι → ℝ)) (t:ℝ) (ht:0 < t)
    (hbound:∀ x ∈ S, ∀ i, |f x i| ≤ t) :
    ∃ W:Finset G, W.Nonempty ∧ S.card ≤ (2*Fintype.card ι+1)*W.card ∧
      ∀ w ∈ W, (∀ i, |f w i| ≤ 2*t) ∧ |∑ i, f w i| ≤ t:=by
  classical
  let r:=Fintype.card ι
  let q:G → ℤ:=fun x => ⌊(∑ i, f x i)/t⌋
  have hq:∀ x ∈ S, q x ∈ Finset.Icc (-(r:ℤ)) r:=by
    intro x hx
    have hs:|∑ i, f x i| ≤ (r:ℝ)*t :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa [r] using (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hbound x hx i)))
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      have hh:=(abs_le.mp hs).1
      rw [le_div_iff₀ ht]
      simpa using hh
    · apply Int.floor_le_iff.mpr
      have hh:=(div_le_iff₀ ht).mpr (abs_le.mp hs).2
      exact hh.trans_lt (by simp)
  have hqcard:(S.image q).card ≤ 2*r+1:=by
    have hs:S.image q ⊆ Finset.Icc (-(r:ℤ)) r:=by
      intro z hz
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
      exact hq x hx
    have hc:(Finset.Icc (-(r:ℤ)) r).card = 2*r+1:=by rw [Int.card_Icc]; omega
    exact (Finset.card_le_card hs).trans_eq hc
  obtain ⟨c,hc,hmax⟩:=(S.image q).exists_max_image
    (fun c => (S.filter (fun x => q x = c)).card) (hS.image q)
  let V:=S.filter (fun x => q x = c)
  obtain ⟨v,hv,hqv⟩:=Finset.mem_image.mp hc
  have hvV:v ∈ V:=Finset.mem_filter.mpr ⟨hv,hqv⟩
  let W:=V.image (fun x => x-v)
  have hW:W.Nonempty:=(Finset.nonempty_iff_ne_empty.mpr (by
    exact Finset.ne_empty_of_mem hvV)).image _
  have hcW:W.card = V.card:=Finset.card_image_iff.mpr (by
    intro a _ b _ h
    exact sub_left_injective h)
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW]
    exact (Finset.card_le_mul_card_image S V.card hmax).trans (by nlinarith [hqcard])
  · intro w hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨hx,hqc⟩:=Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · intro i
      simp only [map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])
    · have heq:q x = q v:=hqc.trans hqv.symm
      have h₁:=Int.floor_le ((∑ i, f x i)/t)
      have h₂:=Int.lt_floor_add_one ((∑ i, f x i)/t)
      have h₃:=Int.floor_le ((∑ i, f v i)/t)
      have h₄:=Int.lt_floor_add_one ((∑ i, f v i)/t)
      change (q x:ℝ) ≤ _ at h₁
      change _ < (q x:ℝ)+1 at h₂
      change (q v:ℝ) ≤ _ at h₃
      change _ < (q v:ℝ)+1 at h₄
      rw [heq] at h₁ h₂
      have hh:|(∑ i, f x i)/t-(∑ i, f v i)/t| < 1:=abs_lt.mpr ⟨by linarith,by linarith⟩
      rw [← sub_div,abs_div,abs_of_pos ht] at hh
      have hh':=(div_lt_iff₀ ht).mp hh
      simpa only [map_sub,Pi.sub_apply,Finset.sum_sub_distrib,one_mul] using hh'.le
end z5t
namespace zc2
open scoped BigOperators
lemma z4o {ι:Type*} [Fintype ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (t:ℝ) (ht:0 < t) :
    ∃ W:Finset L, W.Nonempty ∧
      (t/3)^(Fintype.card ι) ≤ (W.card:ℝ)*ZLattice.covolume L ∧
      ∀ w ∈ W, (∀ i, |(w:ι → ℝ) i| ≤ 2*t) ∧ |∑ i, (w:ι → ℝ) i| ≤ t:=by
  classical
  obtain ⟨U,hU,hUcard,_⟩:=zhf.z6z L t ht.le
  have hUpos:U.Nonempty:=⟨0,(hU 0).mpr (by simpa using fun _:ι => ht.le)⟩
  obtain ⟨W,hW,hcard,hbound⟩:=z5t.zir U hUpos L.subtype.toAddMonoidHom t ht
    (fun x hx => (hU x).mp hx)
  refine ⟨W,hW,?_,hbound⟩
  have hc:U.card ≤ 3^(Fintype.card ι)*W.card :=
    hcard.trans (Nat.mul_le_mul_right _ (z5t.zke _))
  have hh:t^(Fintype.card ι) ≤ (3:ℝ)^(Fintype.card ι)*W.card*ZLattice.covolume L :=
    hUcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ZLattice.covolume_pos L).le)
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (by norm_num:(0:ℝ) < 3) _)).mpr
  nlinarith
end zc2
namespace zfz
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Classical
variable (K:Type*) [Field K] [NumberField K]
lemma z4o (t:ℝ) (ht:0 < t) :
    ∃ U:Finset (𝓞 K)ˣ, U.Nonempty ∧
      (t/3)^(NumberField.Units.rank K) ≤ (U.card:ℝ)*NumberField.Units.regulator K ∧
      ∀ u ∈ U, ∀ w:InfinitePlace K, |Real.log (w (u:K))| ≤ 2*t:=by
  let L:=NumberField.Units.unitLattice K
  have hlift:∀ x:L, ∃ u:(𝓞 K)ˣ, NumberField.Units.logEmbedding K (Additive.ofMul u) = (x:logSpace K):=by
    intro x
    obtain ⟨a,_,ha⟩:=Submodule.mem_map.mp x.property
    exact ⟨a.toMul,ha⟩
  choose lift hlift using hlift
  have hinj:Function.Injective lift:=by
    intro x y hxy
    apply Subtype.ext
    rw [← hlift x,← hlift y,hxy]
  obtain ⟨W,hW,hWcard,hWbound⟩:=zc2.z4o L t ht
  let U:=W.image lift
  have hc:U.card = W.card:=Finset.card_image_of_injective _ hinj
  have hcard:Fintype.card {w:InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K:=by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  refine ⟨U,hW.image lift,?_,?_⟩
  · simpa only [hc,hcard,NumberField.Units.regulator] using hWcard
  · intro u hu w
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hu
    have hm:(1:ℝ) ≤ mult w:=by simp only [mult]; split_ifs <;> norm_num
    have hm0:(0:ℝ) ≤ mult w:=Nat.cast_nonneg _
    have hle:|Real.log (w ((lift x:(𝓞 K)ˣ):K))| ≤
        (mult w:ℝ)*|Real.log (w ((lift x:(𝓞 K)ˣ):K))| :=
      le_mul_of_one_le_left (abs_nonneg _) hm
    by_cases hw:w = w₀
    · have hh:=(hWbound x hx).2
      have hsum:=sum_logEmbedding_component (lift x)
      rw [hlift x] at hsum
      rw [hsum,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)] at hh
      rw [← hw] at hh
      exact hle.trans (hh.trans (by linarith))
    · have hh:=(hWbound x hx).1 ⟨w,hw⟩
      rw [← hlift x,logEmbedding_component,abs_mul,abs_of_nonneg hm0] at hh
      exact hle.trans hh
end zfz
namespace z6n
open NumberField NumberField.InfinitePlace
open scoped BigOperators
lemma zld (y:ℝ) (hy:0 ≤ y) :
    2*y*|y^2-1| ≤ (max 1 y)^4:=by
  by_cases h:y ≤ 1
  · rw [max_eq_left h,abs_of_nonpos (by nlinarith:y^2-1 ≤ 0)]
    have hh:0 ≤ y^2*(1-y^2):=mul_nonneg (sq_nonneg y) (by nlinarith)
    nlinarith [sq_nonneg (y^2+y-1)]
  · have h':1 ≤ y:=le_of_not_ge h
    rw [max_eq_right h',abs_of_nonneg (by nlinarith:0 ≤ y^2-1)]
    nlinarith [sq_nonneg (y^2-y-1)]
private lemma zi0 (x:ℝ) (hx:0 < x) :
    2*Real.log (max 1 x) = |Real.log x| + Real.log x:=by
  by_cases h:1 ≤ x
  · rw [max_eq_right h,abs_of_nonneg (Real.log_nonneg h)]
    ring
  · have h':x ≤ 1:=le_of_not_ge h
    rw [max_eq_left h',Real.log_one,abs_of_nonpos (Real.log_nonpos hx.le h')]
    ring
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
private lemma zmm (w:InfinitePlace K) (x:K) :
    w (x^2-1) = |(w x)^2-1|:=by
  have hw:=IsTotallyReal.isReal w
  rw [← norm_embedding_of_isReal hw (x^2-1),← norm_embedding_of_isReal hw x]
  simp [map_sub,map_pow,Real.norm_eq_abs]
private lemma zf6 (a:𝓞 K) (ha:a ≠ 0) :
    1 ≤ ∏ w:InfinitePlace K, w (a:K):=by
  have hp:=InfinitePlace.prod_eq_abs_norm (a:K)
  simp only [IsTotallyReal.mult_eq,pow_one] at hp
  rw [hp,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)
lemma zdw (u:(𝓞 K)ˣ) (hu:(u:K)^2 ≠ 1) :
    (2:ℝ)^(Fintype.card (InfinitePlace K)) ≤
      (∏ w:InfinitePlace K, max 1 (w (u:K)))^4:=by
  classical
  let a:𝓞 K:=(u:𝓞 K)^2-1
  have ha:a ≠ 0:=by
    intro h
    have hh:=congrArg (algebraMap (𝓞 K) K) h
    apply hu
    simpa [a,sub_eq_zero] using hh
  have hprod:1 ≤ ∏ w:InfinitePlace K, w ((u:K)^2-1):=by
    simpa [a] using zf6 K a ha
  have hunit:(∏ w:InfinitePlace K, w (u:K)) = 1:=by
    simpa only [IsTotallyReal.mult_eq,pow_one,NumberField.Units.norm,Rat.cast_one] using
      InfinitePlace.prod_eq_abs_norm (u:K)
  have hpoint (w:InfinitePlace K) :
      2*w (u:K)*w ((u:K)^2-1) ≤ (max 1 (w (u:K)))^4:=by
    rw [zmm K]
    exact zld _ (apply_nonneg w _)
  have hp:=Finset.prod_le_prod (s:=Finset.univ)
    (fun w _ => mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg w _)) (apply_nonneg w _))
    (fun w _ => hpoint w)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow,hunit,mul_one] at hp
  exact (le_mul_of_one_le_right (by positivity) hprod).trans hp
lemma zhq (u:(𝓞 K)ˣ) (hu:(u:K)^2 ≠ 1) :
    (Fintype.card (InfinitePlace K):ℝ)*Real.log 2 ≤
      2*∑ w:InfinitePlace K, |Real.log (w (u:K))|:=by
  classical
  have hp:=zdw K u hu
  have hlog:=Real.log_le_log (by positivity:(0:ℝ) < 2^(Fintype.card (InfinitePlace K))) hp
  rw [Real.log_pow,Real.log_pow,Real.log_prod (fun w _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))] at hlog
  have hsum:(∑ w:InfinitePlace K, Real.log (w (u:K))) = 0:=by
    simpa only [IsTotallyReal.mult_eq,Nat.cast_one,one_mul] using NumberField.Units.sum_mult_mul_log u
  have hid:2*(∑ w:InfinitePlace K, Real.log (max 1 (w (u:K)))) =
      ∑ w:InfinitePlace K, |Real.log (w (u:K))|:=by
    rw [Finset.mul_sum]
    simp_rw [zi0 _ (NumberField.Units.pos_at_place u _)]
    rw [Finset.sum_add_distrib,hsum,add_zero]
  norm_num at hlog
  linarith
open NumberField.Units.dirichletUnitTheorem in
lemma z5z (u:(𝓞 K)ˣ)
    (hsmall:∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    (u:K)^2 = 1:=by
  classical
  have hlog:0 < Real.log 2:=Real.log_pos (by norm_num)
  have ht:0 ≤ Real.log 2/8:=by positivity
  have hcard:(0:ℝ) < Fintype.card (InfinitePlace K):=by exact_mod_cast Fintype.card_pos
  have hsum:=sum_logEmbedding_component u
  simp only [logEmbedding_component,IsTotallyReal.mult_eq,Nat.cast_one,one_mul] at hsum hsmall
  let N:=Fintype.card (InfinitePlace K)
  let S:=∑ i:{w:InfinitePlace K // w ≠ w₀}, |Real.log (i.val (u:K))|
  have hs:S ≤ N*(Real.log 2/8):=by
    calc
      S ≤ (Fintype.card {w:InfinitePlace K // w ≠ w₀}:ℝ)*(Real.log 2/8):=by
        simpa [S] using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hsmall i)
      _ ≤ N*(Real.log 2/8):=mul_le_mul_of_nonneg_right (by
        exact_mod_cast Fintype.card_subtype_le (fun w:InfinitePlace K => w ≠ w₀)) ht
  have hlast:|Real.log (w₀ (u:K))| ≤ S:=by
    have hh:=Finset.abs_sum_le_sum_abs
      (fun i:{w:InfinitePlace K // w ≠ w₀} => Real.log (i.val (u:K))) Finset.univ
    rw [hsum] at hh
    simpa [S] using hh
  have hall:(∑ w:InfinitePlace K, |Real.log (w (u:K))|) ≤ 2*N*(Real.log 2/8):=by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    change |Real.log (w₀ (u:K))| + S ≤ _
    linarith
  have hu:(u:K)^2 = 1:=by
    by_contra hu
    have hh:=zhq K u hu
    change (N:ℝ)*Real.log 2 ≤ _ at hh
    have hp:(0:ℝ) < N*Real.log 2:=mul_pos hcard hlog
    linarith
  exact hu
lemma zcf (u:(𝓞 K)ˣ)
    (hsmall:∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    NumberField.Units.logEmbedding K (Additive.ofMul u) = 0:=by
  classical
  have hu:=z5z K u hsmall
  rcases sq_eq_one_iff.mp hu with hu | hu
  · ext i
    simp [NumberField.Units.logEmbedding,hu]
  · ext i
    have hv:i.val (-1:K) = 1:=by
      rw [← norm_embedding_of_isReal (IsTotallyReal.isReal i.val)]
      simp
    simp [NumberField.Units.logEmbedding,hu,hv]
end z6n
open scoped Pointwise
namespace z73
lemma z4c {α ι:Type*} [Fintype ι]
    (S:Finset α) (f:α → ι → ℝ) (R:ℕ)
    (hbound:∀ a ∈ S, ∀ i, |f a i| ≤ R)
    (hsep:∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ i, 1 ≤ |f a i-f b i|) :
    S.card ≤ (2*R+1)^(Fintype.card ι):=by
  classical
  let box:Finset (ι → ℤ):=Fintype.piFinset (fun _ => Finset.Icc (-(R:ℤ)) R)
  let g:α → ι → ℤ:=fun a i => ⌊f a i⌋
  have hmaps:Set.MapsTo g (S:Set α) (box:Set (ι → ℤ)):=by
    intro a ha
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hb:=abs_le.mp (hbound a ha i)
    constructor
    · exact Int.le_floor.mpr (by simpa using hb.1)
    · apply Int.floor_le_iff.mpr
      exact lt_of_le_of_lt hb.2 (by simp)
  have hinj:Set.InjOn g (S:Set α):=by
    intro a ha b hb heq
    by_contra hab
    obtain ⟨i,hi⟩:=hsep a ha b hb hab
    have hge:⌊f a i⌋ = ⌊f b i⌋:=congrFun heq i
    have h₁:=Int.floor_le (f a i)
    have h₂:=Int.floor_le (f b i)
    have h₃:=Int.lt_floor_add_one (f a i)
    have h₄:=Int.lt_floor_add_one (f b i)
    rw [hge] at h₁ h₃
    have hlt:|f a i-f b i| < 1:=abs_lt.mpr ⟨by linarith,by linarith⟩
    exact hlt.not_ge hi
  have hc:box.card = (2*R+1)^(Fintype.card ι):=by
    simp only [box,Fintype.card_piFinset,Int.card_Icc]
    have hnat:((R:ℤ)+1 - -(R:ℤ)).toNat = 2*R+1:=by omega
    simp only [hnat, Finset.prod_const, Finset.card_univ]
  exact hc ▸ Finset.card_le_card_of_injOn g hmaps hinj
lemma zbn {α ι:Type*} [AddCommGroup α] [DecidableEq α]
    (U:Finset α) (f:ι → α →+ ℝ) (R:ℝ)
    (hbound:∀ u ∈ U, ∀ i, |f i u| ≤ R) (j:ℕ) :
    ∀ x ∈ j • U, ∀ i, |f i x| ≤ j*R:=by
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
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp hx
    calc
      |f i (a+b)| = |f i a+f i b|:=by rw [map_add]
      _ ≤ |f i a|+|f i b|:=abs_add_le _ _
      _ ≤ j*R+R:=add_le_add (ih a ha i) (hbound b hb i)
      _ = (j+1:ℕ)*R:=by push_cast; ring
lemma z62 {α ι:Type*} [AddCommGroup α] [DecidableEq α] [Fintype ι]
    (U:Finset α) (f:ι → α →+ ℝ) (R:ℕ)
    (hbound:∀ u ∈ U, ∀ i, |f i u| ≤ R)
    (hsep:∀ a b:α, a ≠ b → ∃ i, 1 ≤ |f i a-f i b|) (j:ℕ) :
    (j • U).card ≤ ((2*R+1)*(j+1))^(Fintype.card ι):=by
  classical
  have hh:∀ x ∈ j • U, ∀ i, |f i x| ≤ (j*R:ℕ):=by
    simpa only [Nat.cast_mul] using
      zbn U f (R:ℝ) hbound j
  have hc:=z4c (j • U) (fun a i => f i a) (j*R)
    hh (fun a _ b _ hab => hsep a b hab)
  exact hc.trans (Nat.pow_le_pow_left (by nlinarith:2*(j*R)+1 ≤ (2*R+1)*(j+1)) _)
end z73
namespace z6b
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
private noncomputable abbrev logU (u:(𝓞 K)ˣ):logSpace K:=NumberField.Units.logEmbedding K (Additive.ofMul u)
omit [IsTotallyReal K] in
private lemma log_div (u v:(𝓞 K)ˣ):logU K (u/v) = logU K u-logU K v:=by
  exact map_sub (NumberField.Units.logEmbedding K) (Additive.ofMul u) (Additive.ofMul v)
lemma zbh (u v:(𝓞 K)ˣ) (h:logU K u = logU K v) :
    (u:K) = (v:K) ∨ (u:K) = -(v:K):=by
  have hs:=z6n.z5z K (u/v) (by
    intro i
    change |logU K (u/v) i| ≤ _
    rw [log_div,h,sub_self]
    simp only [Pi.zero_apply,abs_zero]
    positivity)
  have hm:((u/v:(𝓞 K)ˣ):K)*(v:K) = (u:K):=by
    rw [← NumberField.Units.coe_mul,div_mul_cancel]
  rcases sq_eq_one_iff.mp hs with hh | hh
  · left
    simpa [hh] using hm.symm
  · right
    simpa [hh] using hm.symm
private lemma zgr (U:Finset (𝓞 K)ˣ) (y:logSpace K) :
    (U.filter (fun u => logU K u = y)).card ≤ 2:=by
  classical
  let V:=U.filter (fun u => logU K u = y)
  by_cases hV:V.Nonempty
  · obtain ⟨v,hv⟩:=hV
    have hv':=(Finset.mem_filter.mp hv).2
    have hh:V.card ≤ ({(v:K),-(v:K)}:Finset K).card:=by
      apply Finset.card_le_card_of_injOn (fun u:(𝓞 K)ˣ => (u:K))
      · intro u hu
        have he:=zbh K u v ((Finset.mem_filter.mp hu).2.trans hv'.symm)
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using he
      · exact (NumberField.Units.coe_injective K).injOn
    exact hh.trans (Finset.card_insert_le _ _)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (by norm_num)
lemma zdr (U:Finset (𝓞 K)ˣ) (R:ℕ)
    (hbound:∀ u ∈ U, ∀ i, |logU K u i| ≤ R*(Real.log 2/8)) :
    U.card ≤ 2*(2*R+1)^(NumberField.Units.rank K):=by
  classical
  let c:ℝ:=Real.log 2/8
  have hc:0 < c:=by dsimp [c]; positivity
  let W:=U.image (logU K)
  have hwbound:∀ x ∈ W, ∀ i, |x i/c| ≤ R:=by
    intro x hx i
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
    rw [abs_div,abs_of_pos hc]
    exact (div_le_iff₀ hc).mpr (hbound u hu i)
  have hwsep:∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∃ i, 1 ≤ |x i/c-y i/c|:=by
    intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hy
    by_contra! h
    have hs:∀ i, |logU K (u/v) i| ≤ c:=by
      intro i
      have hh:=h i
      rw [← sub_div,abs_div,abs_of_pos hc] at hh
      have hh':=(div_lt_iff₀ hc).mp hh
      rw [log_div,Pi.sub_apply]
      linarith
    have hz:=z6n.zcf K (u/v) hs
    change logU K (u/v) = 0 at hz
    rw [log_div,sub_eq_zero] at hz
    exact hxy hz
  have hw:=z73.z4c W (fun x i => x i/c) R hwbound hwsep
  have hcard:Fintype.card {w:InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K:=by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  rw [hcard] at hw
  exact (Finset.card_le_mul_card_image U 2 (fun y _ => zgr K U y)).trans (Nat.mul_le_mul_left 2 hw)
end z6b
namespace z3a
open NumberField NumberField.InfinitePlace
open scoped BigOperators Classical
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
noncomputable def z60:(𝓞 L)ˣ →* (𝓞 K)ˣ:=Units.map (RingOfIntegers.norm K)
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp] lemma zl8 (u:(𝓞 L)ˣ):((z60 K L u:(𝓞 K)ˣ):K) = Algebra.norm K (u:L):=rfl
omit [NumberField L] in
lemma log_bound (u:(𝓞 L)ˣ) (t:ℝ)
    (hbound:∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤ t) (w:InfinitePlace K) :
    |Real.log (w ((z60 K L u:(𝓞 K)ˣ):K))| ≤ (Module.finrank K L:ℝ)*t:=by
  letI:Algebra K ℂ:=w.embedding.toAlgebra
  have he:w.embedding (Algebra.norm K (u:L)) = ∏ σ:L →ₐ[K] ℂ, σ (u:L) :=
    Algebra.norm_eq_prod_embeddings K ℂ (u:L)
  have hlog:Real.log (w ((z60 K L u:(𝓞 K)ˣ):K)) =
      ∑ σ:L →ₐ[K] ℂ, Real.log ‖σ (u:L)‖:=by
    rw [← norm_embedding_eq,zl8,he,norm_prod,Real.log_prod]
    intro σ _
    apply norm_ne_zero_iff.mpr
    rw [← map_zero σ]; exact σ.injective.ne (NumberField.Units.coe_ne_zero u)
  rw [hlog]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh:∀ σ:L →ₐ[K] ℂ, |Real.log ‖σ (u:L)‖| ≤ t:=by
    intro σ
    exact hbound (InfinitePlace.mk σ.toRingHom)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AlgHom.card] using
    Finset.sum_le_sum (s:=Finset.univ) (fun σ _ => hh σ)
end z3a
namespace zhe
lemma zlc {G H ι:Type*} [CommGroup G] [CommGroup H]
    [DecidableEq G] [DecidableEq H] (S:Finset G) (hS:S.Nonempty)
    (N:G →* H) (f:Additive G →+ (ι → ℝ)) (t:ℝ)
    (hbound:∀ x ∈ S, ∀ i, |f (Additive.ofMul x) i| ≤ t) :
    ∃ W:Finset G, W.Nonempty ∧ S.card ≤ (S.image N).card*W.card ∧
      ∀ w ∈ W, N w = 1 ∧ ∀ i, |f (Additive.ofMul w) i| ≤ 2*t:=by
  classical
  obtain ⟨c,hc,hmax⟩:=(S.image N).exists_max_image
    (fun c => (S.filter (fun x => N x = c)).card) (hS.image N)
  let V:=S.filter (fun x => N x = c)
  obtain ⟨v,hv,hNv⟩:=Finset.mem_image.mp hc
  have hvV:v ∈ V:=Finset.mem_filter.mpr ⟨hv,hNv⟩
  let W:=V.image (fun x => x/v)
  have hW:W.Nonempty:=(show V.Nonempty from ⟨v,hvV⟩).image _
  have hcW:W.card = V.card:=Finset.card_image_of_injective _ div_left_injective
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW,mul_comm]
    exact Finset.card_le_mul_card_image S V.card hmax
  · intro w hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨hx,hNx⟩:=Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · rw [map_div,hNx,hNv,div_self']
    · intro i
      rw [ofMul_div,map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])
end zhe
namespace zcu
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in
noncomputable def z52:Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w:=Real.log (w (u.toMul:L))
  map_zero':=by simp; rfl
  map_add':=by intro u v; simp [Real.log_mul]; rfl
lemma z4o (N:ℕ) (hN:0 < N) :
    ∃ W:Finset (𝓞 L)ˣ, W.Nonempty ∧
      ((Real.log 2/8)*N/3)^(NumberField.Units.rank L) ≤
        2*(4*Module.finrank K L*N+1:ℕ)^(NumberField.Units.rank K) *
          (W.card:ℝ)*NumberField.Units.regulator L ∧
      ∀ u ∈ W, z3a.z60 K L u = 1 ∧
        ∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤ 4*(Real.log 2/8)*N:=by
  let t:ℝ:=(Real.log 2/8)*N
  have ht:0 < t:=by dsimp [t]; positivity
  obtain ⟨S,hS,hcard,hbound⟩:=zfz.z4o L t ht
  let nm:=z3a.z60 K L
  have him:(S.image nm).card ≤ 2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K):=by
    have hh:=z6b.zdr K (S.image nm) (2*Module.finrank K L*N) (by
      intro u hu i
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
      have hn:=z3a.log_bound K L v (2*t) (hbound v hv) i.val
      change |NumberField.Units.logEmbedding K (Additive.ofMul (nm v)) i| ≤ _
      rw [logEmbedding_component,InfinitePlace.mult,if_pos (IsTotallyReal.isReal i.val)]
      simp only [Nat.cast_one,one_mul]
      convert hn using 1; push_cast; dsimp [t]; ring)
    convert hh using 1; congr 3; ring
  obtain ⟨W,hW,hWcard,hWbound⟩:=zhe.zlc S hS nm (z52 L) (2*t) hbound
  refine ⟨W,hW,?_,?_⟩
  · have hc:S.card ≤ (2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K))*W.card :=
      hWcard.trans (Nat.mul_le_mul_right W.card him)
    have hr:0 ≤ NumberField.Units.regulator L:=(NumberField.Units.regulator_pos L).le
    exact hcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hr)
  · intro u hu
    refine ⟨(hWbound u hu).1,?_⟩
    intro w
    convert (hWbound u hu).2 w using 1 <;> first | (simp only [t]; ring) | rfl
end zcu
namespace zat
open NumberField
open scoped Classical BigOperators
variable (L:Type*) [Field L] [NumberField L]
noncomputable def decomp (u:(𝓞 L)ˣ):NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ℤ) :=
  Classical.choose (NumberField.Units.exist_unique_eq_mul_prod L u).exists
lemma zhc (u:(𝓞 L)ˣ) :
    u = (decomp L u).1 * ∏ i, NumberField.Units.fundSystem L i ^ ((decomp L u).2 i) :=
  Classical.choose_spec (NumberField.Units.exist_unique_eq_mul_prod L u).exists
noncomputable def residue (u:(𝓞 L)ˣ) :
    NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
  ((decomp L u).1,fun i => (decomp L u).2 i)
lemma zh6 (u v:(𝓞 L)ˣ) (h:residue L u = residue L v) :
    ∃ z:(𝓞 L)ˣ, z^5 = u/v:=by
  let a:=(decomp L u).2
  let b:=(decomp L v).2
  have hζ:(decomp L u).1 = (decomp L v).1:=by
    simpa only [residue] using congrArg Prod.fst h
  have hexp:∀ i, (5:ℤ) ∣ a i-b i:=by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    rw [Int.cast_sub,sub_eq_zero]
    exact congrFun (congrArg Prod.snd h) i
  refine ⟨∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5),?_⟩
  calc
    (∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5))^5 =
        ∏ i, NumberField.Units.fundSystem L i ^ (a i-b i):=by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_natCast,← zpow_mul]
      congr 1
      exact Int.ediv_mul_cancel (hexp i)
    _ = (∏ i, NumberField.Units.fundSystem L i ^ (a i)) /
        (∏ i, NumberField.Units.fundSystem L i ^ (b i)):=by
      simp only [zpow_sub,Finset.prod_mul_distrib,Finset.prod_inv_distrib,div_eq_mul_inv]
    _ = u/v:=by
      conv_rhs => rw [zhc L u,zhc L v,hζ]
      dsimp only [a,b]
      rw [mul_div_mul_comm,div_self',one_mul]
end zat
open scoped Pointwise
namespace z7c
lemma zlw {G ι Q:Type*} [CommGroup G] [DecidableEq G] [Fintype Q]
    (U:Finset G) (f:Additive G →+ (ι → ℝ)) (t:ℝ) (ht:0 ≤ t)
    (hU:∀ x, x ∈ U ↔ ∀ i, |f (Additive.ofMul x) i| ≤ t)
    (q:G → Q) (hroot:∀ x y, q x = q y → ∃ z, z^5 = x/y) :
    (U/U).card ≤ Fintype.card Q * U.card:=by
  classical
  let V:Finset G:=U/U
  have hV:∀ x ∈ V, ∀ i, |f (Additive.ofMul x) i| ≤ 2*t:=by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_div.mp hx
    calc
      |f (Additive.ofMul (a/b)) i| = |f (Additive.ofMul a) i-f (Additive.ofMul b) i|:=by simp
      _ ≤ |f (Additive.ofMul a) i|+|f (Additive.ofMul b) i|:=abs_sub _ _
      _ ≤ t+t:=add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t:=by ring
  have hf:∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card:=by
    intro c hc
    let T:Finset G:=V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩:=Finset.mem_image.mp hc
    have hex:∀ x ∈ T, ∃ z ∈ U, z^5 = x/x₀:=by
      intro x hx
      obtain ⟨hx,hqx⟩:=Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩:=hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he:5 * f (Additive.ofMul z) i = f (Additive.ofMul x) i - f (Additive.ofMul x₀) i:=by
        have hh:=congrArg (fun w => f (Additive.ofMul w) i) hz
        simpa using hh
      have hb:|f (Additive.ofMul x) i - f (Additive.ofMul x₀) i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g:T → U:=fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x:T):(g x:G)^5 = (x:G)/x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj:Function.Injective g:=by
      intro x y hxy
      apply Subtype.ext
      have hh:=congrArg (fun z:U => (z:G)^5) hxy
      try dsimp only at hh
      rw [hg,hg] at hh
      exact div_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U/U).card ≤ U.card * (V.image q).card:=Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q:=Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card:=Nat.mul_comm _ _
end z7c
namespace zbe
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators Pointwise
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
omit [NumberField K] [NumberField L] in
noncomputable def z52:Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w:=Real.log (w (u.toMul:L))
  map_zero':=by simp; rfl
  map_add':=by intro u v; simp [Real.log_mul]; rfl
lemma zjn (t:ℝ) :
    {u:(𝓞 L)ˣ | ∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤ t}.Finite:=by
  apply Set.Finite.of_finite_image (f:=fun u:(𝓞 L)ˣ => (u:L)) ?_
    (NumberField.Units.coe_injective L).injOn
  apply (Embeddings.finite_of_norm_le L ℂ (Real.exp t)).subset
  rintro _ ⟨u,hu,rfl⟩
  refine ⟨u.val.isIntegral_coe,?_⟩
  intro σ
  have hh:=hu (InfinitePlace.mk σ)
  change |Real.log ‖σ (u:L)‖| ≤ t at hh
  have hp:0 < ‖σ (u:L)‖:=norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  exact (Real.log_le_iff_le_exp hp).mp ((le_abs_self _).trans hh)
variable [IsTotallyReal K]
lemma zio (u:(𝓞 K)ˣ) (h:u^5 = 1):u = 1:=by
  let σ:K →+* ℝ:=InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀:InfinitePlace K))
  apply NumberField.Units.coe_injective K
  apply σ.injective
  have hh:=congrArg (fun u:(𝓞 K)ˣ => σ (u:K)) h
  simp only [NumberField.Units.coe_pow,NumberField.Units.coe_one,map_pow,map_one] at hh ⊢
  exact (Odd.pow_inj (by decide:Odd 5)).mp (by simpa using hh)
lemma z6z (N:(𝓞 L)ˣ →* (𝓞 K)ˣ) (t:ℝ) (ht:0 ≤ t) :
    ∃ U:Finset (𝓞 L)ˣ,
      (∀ u, u ∈ U ↔ N u = 1 ∧ ∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤ t) ∧
      (U/U).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*U.card:=by
  let G:=N.ker
  have hf:{u:G | ∀ w:InfinitePlace L, |Real.log (w ((u:(𝓞 L)ˣ):L))| ≤ t}.Finite :=
    (zjn L t).preimage (Function.Injective.injOn Subtype.val_injective)
  let V:Finset G:=hf.toFinset
  have hV (u:G):u ∈ V ↔ ∀ w:InfinitePlace L, |Real.log (w ((u:(𝓞 L)ˣ):L))| ≤ t:=by
    exact Set.Finite.mem_toFinset hf
  let f:Additive G →+ (InfinitePlace L → ℝ) :=
    (z52 L).comp N.ker.subtype.toAdditive
  let q:G → NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
    fun u => zat.residue L (u:(𝓞 L)ˣ)
  have hroot:∀ x y:G, q x = q y → ∃ z:G, z^5 = x/y:=by
    intro x y hxy
    obtain ⟨z,hz⟩:=zat.zh6 L (x:(𝓞 L)ˣ) (y:(𝓞 L)ˣ) hxy
    have hnz:N z = 1:=by
      apply zio K
      rw [← map_pow,hz,map_div,x.property,y.property,div_self']
    exact ⟨⟨z,hnz⟩,Subtype.ext hz⟩
  have hcard:=z7c.zlw V f t ht hV q hroot
  have hc:(V/V).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*V.card:=by
    simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hcard
  let U:=V.image N.ker.subtype
  refine ⟨U,?_,?_⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
      exact ⟨v.property,(hV v).mp hv⟩
    · intro hu
      exact Finset.mem_image.mpr ⟨⟨u,hu.1⟩,(hV _).mpr hu.2,rfl⟩
  · dsimp only [U]
    rw [← Finset.image_div,Finset.card_image_of_injective (f:=N.ker.subtype) _ Subtype.val_injective,
      Finset.card_image_of_injective (f:=N.ker.subtype) _ Subtype.val_injective]
    exact hc
end zbe
namespace z5p
open NumberField
open scoped Pointwise
variable (K:Type*) [Field K] [NumberField K]
noncomputable def coordinate (i:(K →+* ℂ) × Bool):𝓞 K →+ ℝ :=
  (2:ℕ) • ((if i.2 then Complex.reAddGroupHom else Complex.imAddGroupHom).comp
    ((i.1.comp (algebraMap (𝓞 K) K)).toAddMonoidHom))
private lemma separated (a b:𝓞 K) (hab:a ≠ b) :
    ∃ i, 1 ≤ |coordinate K i a-coordinate K i b|:=by
  obtain ⟨σ,hσ⟩:=NumberField.exists_conjugate_one_le_norm (sub_ne_zero.mpr hab)
  have he:=Complex.norm_le_abs_re_add_abs_im (σ ((a-b:𝓞 K):K))
  by_cases hr:1 ≤ 2*|(σ ((a-b:𝓞 K):K)).re|
  · refine ⟨(σ,true),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hr
  · have hi:1 ≤ 2*|(σ ((a-b:𝓞 K):K)).im|:=by linarith
    refine ⟨(σ,false),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hi
variable [DecidableEq (𝓞 K)]
lemma z62 (U:Finset (𝓞 K)) (R:ℕ)
    (hbound:∀ u ∈ U, ∀ σ:K →+* ℂ, ‖σ (u:K)‖ ≤ R) (j:ℕ) :
    (j • U).card ≤ ((4*R+1)*(j+1))^(2*Module.finrank ℚ K):=by
  classical
  have hb:∀ u ∈ U, ∀ i, |coordinate K i u| ≤ (2*R:ℕ):=by
    intro u hu ⟨σ,b⟩
    cases b
    · have hh:=(Complex.abs_im_le_norm (σ (u:K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num:(0:ℝ) ≤ 2))
    · have hh:=(Complex.abs_re_le_norm (σ (u:K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num:(0:ℝ) ≤ 2))
  have hc:=z73.z62 U (coordinate K) (2*R) hb (separated K) j
  simpa [Fintype.card_prod,NumberField.Embeddings.card,mul_comm,mul_left_comm,mul_assoc] using hc
lemma zdk (U:Finset (𝓞 K)) (σ₀:K →+* ℂ) (R:ℕ)
    (hbound:∀ u ∈ U, ∀ σ:K →+* ℂ, ‖σ (u:K)‖ ≤ R) (j:ℕ) :
    (j • U.image (σ₀.comp (algebraMap (𝓞 K) K))).card ≤
      ((4*R+1)*(j+1))^(2*Module.finrank ℚ K):=by
  classical
  rw [← Finset.image_nsmul]
  exact Finset.card_image_le.trans (z62 K U R hbound j)
end z5p
namespace zf4
open NumberField
open scoped Classical Pointwise
lemma card_le (L:Type*) [Field L] [NumberField L] :
    Fintype.card (NumberField.Units.torsion L) ≤ 10^(2*Module.finrank ℚ L):=by
  let f:NumberField.Units.torsion L → 𝓞 L:=fun u => (u:(𝓞 L)ˣ).val
  have hf:Function.Injective f:=Units.val_injective.comp Subtype.val_injective
  let U:=Finset.univ.image f
  have hU:U.card = Fintype.card (NumberField.Units.torsion L):=by
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ]
  have hb:∀ u ∈ U, ∀ σ:L →+* ℂ, ‖σ (u:L)‖ ≤ (1:ℕ):=by
    intro u hu σ
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hu
    simpa only [f,Nat.cast_one,InfinitePlace.apply] using
      ((NumberField.Units.mem_torsion L).mp v.property (InfinitePlace.mk σ)).le
  have hh:=z5p.z62 L U 1 hb 1
  simpa only [one_nsmul,hU] using hh
end zf4
namespace z9y
lemma zm8 (d r s R B:ℕ) (hd:0 < d) (hR:0 < R) (hB:0 < B)
    (hr:r ≤ d) (hs:s ≤ d) (hgap:4*s+d ≤ 4*r)
    (A:ℝ) (hA:0 ≤ A)
    (h:(((864*R*B:ℕ)^4:ℝ)/48)^r ≤
      2*(9*((864*R*B:ℕ)^4:ℝ))^s*A*(R:ℝ)^d) :
    (B:ℝ)^d ≤ A:=by
  let T:=864*R*B
  let N:=T^4
  have hT:0 < T:=by dsimp [T]; positivity
  have hN:(0:ℝ) < N:=by dsimp [N]; positivity
  have hsr:s ≤ r:=by omega
  have hgap':d ≤ 4*(r-s):=by omega
  have hm:(N:ℝ)^r ≤ 2*(48:ℝ)^r*(9*(N:ℝ))^s*A*(R:ℝ)^d:=by
    have h':((N:ℝ)/48)^r ≤ 2*(9*(N:ℝ))^s*A*(R:ℝ)^d:=by
      simpa only [N,T,Nat.cast_pow] using h
    rw [div_pow] at h'
    have hh:=(div_le_iff₀ (pow_pos (by norm_num:(0:ℝ) < 48) r)).mp h'
    nlinarith only [hh]
  have hc:(N:ℝ)^(r-s) ≤ 2*(48:ℝ)^r*(9:ℝ)^s*A*(R:ℝ)^d:=by
    apply le_of_mul_le_mul_left ?_ (pow_pos hN s)
    calc
      (N:ℝ)^s * (N:ℝ)^(r-s) = (N:ℝ)^r:=by rw [← pow_add,Nat.add_sub_of_le hsr]
      _ ≤ _:=hm
      _ = _:=by rw [mul_pow]; ring
  have h48:(48:ℝ)^r ≤ 48^d:=pow_le_pow_right₀ (by norm_num) hr
  have h9:(9:ℝ)^s ≤ 9^d:=pow_le_pow_right₀ (by norm_num) hs
  have hu:(N:ℝ)^(r-s) ≤ 2*(432*(R:ℝ))^d*A:=by
    calc
      (N:ℝ)^(r-s) ≤ _:=hc
      _ ≤ 2*(48:ℝ)^d*9^d*A*(R:ℝ)^d:=by gcongr
      _ = _:=by rw [show (432:ℝ) = 48*9 by norm_num]; simp only [mul_pow]; ring
  have hl:2*(432*(R:ℝ))^d*(B:ℝ)^d ≤ (N:ℝ)^(r-s):=by
    calc
      2*(432*(R:ℝ))^d*(B:ℝ)^d ≤ (2:ℝ)^d*(432*(R:ℝ))^d*(B:ℝ)^d:=by
        gcongr
        simpa using pow_le_pow_right₀ (by norm_num:(1:ℝ) ≤ 2) hd
      _ = ((2:ℝ)*(432*(R:ℝ))*(B:ℝ))^d:=by simp only [mul_pow]
      _ = (T:ℝ)^d:=by congr 1; dsimp [T]; push_cast; ring
      _ ≤ (T:ℝ)^(4*(r-s)):=pow_le_pow_right₀ (by exact_mod_cast hT) hgap'
      _ = (N:ℝ)^(r-s):=by dsimp [N]; rw [Nat.cast_pow,pow_mul]
  exact le_of_mul_le_mul_left (hl.trans hu) (by positivity)
end z9y
namespace z3i
open NumberField
lemma zd1 (L:Type*) [Field L] [NumberField L] :
    NumberField.Units.rank L ≤ Module.finrank ℚ L:=by
  have hh:=InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [NumberField.Units.rank,InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega
end z3i
namespace zd7
open NumberField
open scoped Classical BigOperators Pointwise
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
lemma z4o (R B:ℕ) (hR:0 < R) (hB:0 < B)
    (hreg:NumberField.Units.regulator L ≤ (R:ℝ)^(Module.finrank ℚ L))
    (hrel:Module.finrank K L ≤ 2)
    (hgap:4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ W:Finset (𝓞 L)ˣ, W.Nonempty ∧ B^(Module.finrank ℚ L) ≤ W.card ∧
      ∀ u ∈ W, z3a.z60 K L u = 1 ∧
        ∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤
          4*(Real.log 2/8)*((864*R*B:ℕ)^4:ℝ):=by
  let N:=(864*R*B)^4
  have hN:0 < N:=by dsimp [N]; positivity
  obtain ⟨W,hW,hcard,hbound⟩:=zcu.z4o K L N hN
  refine ⟨W,hW,?_,?_⟩
  · have hd:0 < Module.finrank ℚ L:=Module.finrank_pos
    have hr:=z3i.zd1 L
    have hs:NumberField.Units.rank K ≤ Module.finrank ℚ L:=by omega
    have hh:((N:ℝ)/48)^(NumberField.Units.rank L) ≤
        2*(9*(N:ℝ))^(NumberField.Units.rank K)*(W.card:ℝ)*(R:ℝ)^(Module.finrank ℚ L):=by
      calc
        ((N:ℝ)/48)^(NumberField.Units.rank L) ≤
            ((Real.log 2/8)*N/3)^(NumberField.Units.rank L):=by
          apply pow_le_pow_left₀ (by positivity)
          have hl:(1:ℝ)/48 ≤ Real.log 2/24:=by linarith [Real.log_two_gt_d9]
          nlinarith [mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg N)]
        _ ≤ _:=hcard
        _ ≤ _:=by
          have hr0:=(NumberField.Units.regulator_pos L).le
          have hnat:4*Module.finrank K L*N+1 ≤ 9*N:=by nlinarith
          have hb:(4*Module.finrank K L*N+1:ℕ) ≤ (9*(N:ℝ)):=by exact_mod_cast hnat
          gcongr
    have hc:=z9y.zm8 (Module.finrank ℚ L) (NumberField.Units.rank L)
      (NumberField.Units.rank K) R B hd hR hB hr hs hgap (W.card:ℝ) (Nat.cast_nonneg _)
      (by simpa only [N,Nat.cast_pow] using hh)
    exact_mod_cast hc
  · intro u hu
    simpa only [N,Nat.cast_pow] using hbound u hu
lemma z6z (R B:ℕ) (hR:0 < R) (hB:0 < B)
    (hreg:NumberField.Units.regulator L ≤ (R:ℝ)^(Module.finrank ℚ L))
    (hrel:Module.finrank K L ≤ 2)
    (hgap:4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ U:Finset (𝓞 L)ˣ, U.Nonempty ∧ B^(Module.finrank ℚ L) ≤ U.card ∧
      (U/U).card ≤ 500^(Module.finrank ℚ L)*U.card ∧
      ∀ u ∈ U, z3a.z60 K L u = 1 ∧
        ∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤
          4*(Real.log 2/8)*((864*R*B:ℕ)^4:ℝ):=by
  let t:ℝ:=4*(Real.log 2/8)*((864*R*B:ℕ)^4:ℝ)
  have ht:0 ≤ t:=by dsimp [t]; positivity
  obtain ⟨W,hW,hWcard,hWbound⟩:=z4o K L R B hR hB hreg hrel hgap
  obtain ⟨U,hU,hcard⟩:=zbe.z6z K L (z3a.z60 K L) t ht
  have hsub:W ⊆ U:=by intro u hu; exact (hU u).mpr (hWbound u hu)
  refine ⟨U,hW.mono hsub,hWcard.trans (Finset.card_le_card hsub),?_,fun u hu => (hU u).mp hu⟩
  have hp:(Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L) ≤
      500^(Module.finrank ℚ L):=by
    calc
      _ ≤ 10^(2*Module.finrank ℚ L)*5^(Module.finrank ℚ L) :=
        Nat.mul_le_mul (zf4.card_le L) (Nat.pow_le_pow_right (by norm_num) (z3i.zd1 L))
      _ = _:=by rw [pow_mul,← mul_pow]; norm_num
  exact hcard.trans (Nat.mul_le_mul_right _ hp)
end zd7
namespace zbu
open NumberField
open scoped Classical BigOperators ComplexConjugate
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
omit [NumberField L] in
lemma norm_eq_one (hdeg:Module.finrank K L = 2) (σ:L →+* ℂ)
    (hσ:¬ ComplexEmbedding.IsReal σ) (x:L) (hx:Algebra.norm K x = 1) :
    ‖σ x‖ = 1:=by
  let φ:K →+* ℂ:=σ.comp (algebraMap K L)
  letI:Algebra K ℂ:=φ.toAlgebra
  let a:L →ₐ[K] ℂ:={ σ with commutes':=fun _ => rfl }
  have hφ:ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b:L →ₐ[K] ℂ:={ ComplexEmbedding.conjugate σ with
    commutes':=fun r => DFunLike.congr_fun hφ r }
  have hab:a ≠ b:=by
    intro h
    apply hσ
    apply ComplexEmbedding.isReal_iff.mpr
    exact (congrArg AlgHom.toRingHom h).symm
  have hp:({a,b}:Finset (L →ₐ[K] ℂ)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hab,AlgHom.card,hdeg])
  have he:=Algebra.norm_eq_prod_embeddings K ℂ x
  rw [hx,map_one,← hp,Finset.prod_pair hab] at he
  have he':(1:ℂ) = σ x * conj (σ x):=he
  have hn:=congrArg norm he'
  rw [norm_one,norm_mul,Complex.norm_conj] at hn
  nlinarith [norm_nonneg (σ x)]
end zbu
namespace z6k
open NumberField
open scoped Classical Pointwise
def z5b (R B:ℕ):ℕ:=2^((864*R*B)^4)
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in
lemma zlz (R B:ℕ) (u:(𝓞 L)ˣ)
    (hlog:∀ w:InfinitePlace L, |Real.log (w (u:L))| ≤
      4*(Real.log 2/8)*((864*R*B:ℕ)^4:ℝ)) (σ:L →+* ℂ) :
    ‖σ (u:L)‖ ≤ z5b R B:=by
  have hh:=hlog (InfinitePlace.mk σ)
  change |Real.log ‖σ (u:L)‖| ≤ _ at hh
  have hp:0 < ‖σ (u:L)‖:=norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  apply (Real.log_le_log_iff hp (by dsimp [z5b]; positivity)).mp
  simp only [z5b,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hl:0 ≤ Real.log 2:=by positivity
  have hN:(0:ℝ) ≤ (864*R*B:ℕ)^4:=by positivity
  have hm:=mul_nonneg hl hN
  nlinarith [le_abs_self (Real.log ‖σ (u:L)‖)]
lemma zgt (R:ℕ) (hR:0 < R)
    (hreg:NumberField.Units.regulator L ≤ (R:ℝ)^(Module.finrank ℚ L))
    (hrel:Module.finrank K L = 2)
    (hgap:4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L)
    (σ:L →+* ℂ) (hσ:¬ ComplexEmbedding.IsReal σ) :
    ∃ V:Finset ℂ,
      (∀ v ∈ V, ‖v‖ = 1) ∧
      (16*500)^(2*Module.finrank ℚ L) ≤ V.card ∧
      (V/V).card ≤ 500^(2*Module.finrank ℚ L)*V.card ∧
      ∀ j:ℕ, (j • V).card ≤ ((4*z5b R ((16*500)^2)+1)*(j+1))^(2*Module.finrank ℚ L):=by
  let B:=(16*500)^2
  obtain ⟨U,hU,hcard,hdiv,hbound⟩:=zd7.z6z K L R B hR (by norm_num [B]) hreg hrel.le hgap
  let f:(𝓞 L)ˣ →* ℂ:=(Units.coeHom ℂ).comp (NumberField.Units.complexEmbedding σ)
  have hf:Function.Injective f:=σ.injective.comp (NumberField.Units.coe_injective L)
  let V:=U.image f
  have hVcard:V.card = U.card:=Finset.card_image_of_injective _ hf
  refine ⟨V,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hv
    apply zbu.norm_eq_one K L hrel σ hσ
    have hh:=congrArg (fun u:(𝓞 K)ˣ => (u:K)) (hbound u hu).1
    exact hh
  · rw [hVcard]
    simpa only [B,pow_mul] using hcard
  · dsimp only [V]
    rw [← Finset.image_div,Finset.card_image_of_injective (f:=f) _ hf,
      Finset.card_image_of_injective (f:=f) _ hf]
    exact hdiv.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro j
    let A:Finset (𝓞 L):=U.image Units.val
    have hA:∀ u ∈ A, ∀ τ:L →+* ℂ, ‖τ (u:L)‖ ≤ z5b R B:=by
      intro u hu τ
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hu
      exact zlz L R B a (hbound a ha).2 τ
    have he:A.image (σ.comp (algebraMap (𝓞 L) L)) = V:=by
      rw [Finset.image_image]
      rfl
    rw [← he]
    exact z5p.zdk L A σ (z5b R B) hA j
end z6k
namespace zc1
open scoped BigOperators
lemma card_le {ι:Type*} [Fintype ι] (S:Finset (ι → ℕ)) (B:ℕ)
    (hpos:∀ x ∈ S, ∀ i, 0 < x i) (hprod:∀ x ∈ S, ∏ i, x i ≤ B) :
    S.card ≤ 2^(Fintype.card ι) * B^2:=by
  classical
  let box:Finset (ι → ℕ):=Fintype.piFinset (fun _ => Finset.Icc 1 B)
  let w:(ι → ℕ) → ℝ:=fun x => ∏ i, ((x i:ℝ)^2)⁻¹
  have hs:S ⊆ box:=by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_Icc.mpr ⟨hpos x hx i,?_⟩
    have hp:0 < ∏ i, x i:=Finset.prod_pos (fun i _ => hpos x hx i)
    exact (Nat.le_of_dvd hp (Finset.dvd_prod_of_mem x (Finset.mem_univ i))).trans (hprod x hx)
  have hw (x:ι → ℕ) (hx:x ∈ S):1 ≤ (B:ℝ)^2*w x:=by
    have hp:(0:ℝ) < ∏ i, (x i:ℝ):=Finset.prod_pos (fun i _ => by exact_mod_cast hpos x hx i)
    have hle:(∏ i, (x i:ℝ)) ≤ B:=by exact_mod_cast hprod x hx
    dsimp only [w]
    rw [Finset.prod_inv_distrib,Finset.prod_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr (by nlinarith)
  have hsum:(∑ n ∈ Finset.Icc 1 B, ((n:ℝ)^2)⁻¹) ≤ 2:=by
    have hset:Finset.Icc 1 B = Finset.Ioo 0 (B+1):=by ext n; simp; omega
    simpa [hset] using (sum_Ioo_inv_sq_le (α:=ℝ) 0 (B+1))
  have hweight:∑ x ∈ box, w x ≤ (2:ℝ)^(Fintype.card ι):=by
    dsimp only [box,w]
    rw [Finset.sum_prod_piFinset (Finset.Icc 1 B) (fun (_:ι) n => ((n:ℝ)^2)⁻¹)]
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod (s:=(Finset.univ:Finset ι))
        (f:=fun _ => ∑ n ∈ Finset.Icc 1 B, ((n:ℝ)^2)⁻¹) (g:=fun _ => (2:ℝ))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (fun _ _ => hsum)
  have hreal:(S.card:ℝ) ≤ (2:ℝ)^(Fintype.card ι)*(B:ℝ)^2:=by
    calc
      (S.card:ℝ) = ∑ _x ∈ S, (1:ℝ):=by simp
      _ ≤ ∑ x ∈ S, (B:ℝ)^2*w x:=Finset.sum_le_sum (fun x hx => hw x hx)
      _ = (B:ℝ)^2 * ∑ x ∈ S, w x:=(Finset.mul_sum _ _ _).symm
      _ ≤ (B:ℝ)^2 * ∑ x ∈ box, w x:=mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by dsimp [w]; positivity)) (sq_nonneg _)
      _ ≤ (B:ℝ)^2 * (2:ℝ)^(Fintype.card ι):=mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
      _ = _:=mul_comm _ _
  exact_mod_cast hreal
end zc1
open scoped BigOperators
namespace PrimeMultiset
noncomputable def encode {ι:Type*} (s:Multiset (ℕ × ι)) (i:ι):ℕ:=by
  classical
  exact ((s.filter (fun a => a.2 = i)).map Prod.fst).prod
private lemma zhb {ι:Type*} [DecidableEq ι] (s:Multiset (ℕ × ι)) (a:ℕ × ι) :
    Multiset.count a.1 ((s.filter (fun x => x.2 = a.2)).map Prod.fst) = Multiset.count a s:=by
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
lemma encode_injective {ι:Type*} (s t:Multiset (ℕ × ι))
    (hs:∀ a ∈ s, a.1.Prime) (ht:∀ a ∈ t, a.1.Prime)
    (he:encode s = encode t):s = t:=by
  classical
  have hn (v:Multiset (ℕ × ι)) (hv:∀ a ∈ v, a.1.Prime) (i:ι) :
      UniqueFactorizationMonoid.normalizedFactors (encode v i) =
        ((v.filter (fun a => a.2 = i)).map Prod.fst):=by
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro p hp
    obtain ⟨a,ha,rfl⟩:=Multiset.mem_map.mp hp
    exact Nat.prime_iff.mp (hv a (Multiset.mem_filter.mp ha).1)
  apply Multiset.ext.mpr
  intro a
  have hh:=congrArg UniqueFactorizationMonoid.normalizedFactors (congrFun he a.2)
  rw [hn s hs,hn t ht] at hh
  have hc:=congrArg (Multiset.count a.1) hh
  rw [zhb s a,zhb t a] at hc
  exact hc
lemma zmd {ι:Type*} [Fintype ι] (s:Multiset (ℕ × ι)) :
    (∏ i, encode s i) = (s.map Prod.fst).prod:=by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [encode]
  | @cons a s ih =>
    have hc (i:ι):encode (a ::ₘ s) i = (if a.2 = i then a.1 else 1)*encode s i:=by
      by_cases h:a.2 = i <;> simp [encode,h]
    simp_rw [hc]
    rw [Finset.prod_mul_distrib,ih]
    simp
lemma zmx {ι:Type*} (s:Multiset (ℕ × ι))
    (hs:∀ a ∈ s, a.1.Prime) (i:ι):0 < encode s i:=by
  classical
  apply Multiset.prod_pos
  intro p hp
  obtain ⟨a,ha,rfl⟩:=Multiset.mem_map.mp hp
  exact (hs a (Multiset.mem_filter.mp ha).1).pos
end PrimeMultiset
namespace z7r
open UniqueFactorizationMonoid
open scoped BigOperators
variable {α ι:Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [NormalizationMonoid α] [Subsingleton αˣ]
noncomputable def primeFactors (a:α):Multiset {p:α // Prime p} :=
  (normalizedFactors a).pmap (fun p hp => ⟨p,hp⟩) (fun p hp => prime_of_normalized_factor p hp)
omit [Subsingleton αˣ] in
private lemma zi1 (a:α) :
    (primeFactors a).map Subtype.val = normalizedFactors a:=by
  rw [primeFactors,Multiset.map_pmap,Multiset.pmap_eq_map]
  exact Multiset.map_id _
private lemma prod_primeFactors (a:α) (ha:a ≠ 0) :
    ((primeFactors a).map Subtype.val).prod = a:=by
  rw [zi1]
  simpa only [associated_eq_eq] using prod_normalizedFactors ha
noncomputable def encode (c:{p:α // Prime p} → ℕ × ι) (a:α):ι → ℕ :=
  PrimeMultiset.encode ((primeFactors a).map c)
lemma encode_injective (c:{p:α // Prime p} → ℕ × ι)
    (hc:Function.Injective c) (hp:∀ p, (c p).1.Prime)
    {a b:α} (ha:a ≠ 0) (hb:b ≠ 0) (he:encode c a = encode c b):a = b:=by
  have hprime (x:α):∀ p ∈ (primeFactors x).map c, p.1.Prime:=by
    intro p hpm
    obtain ⟨q,_,rfl⟩:=Multiset.mem_map.mp hpm
    exact hp q
  have hf:=PrimeMultiset.encode_injective _ _ (hprime a) (hprime b) he
  have hpf:=Multiset.map_injective hc hf
  have hn:=congrArg (fun s:Multiset {p:α // Prime p} => (s.map Subtype.val).prod) hpf
  simpa only [prod_primeFactors a ha,prod_primeFactors b hb] using hn
lemma zjj [Fintype ι] (N:α →*₀ ℕ)
    (c:{p:α // Prime p} → ℕ × ι) (hN:∀ p, (c p).1 ≤ N p.val)
    (a:α) (ha:a ≠ 0):(∏ i, encode c a i) ≤ N a:=by
  rw [encode,PrimeMultiset.zmd,Multiset.map_map]
  calc
    _ ≤ ((primeFactors a).map (fun p => N p.val)).prod :=
      Multiset.prod_map_le_prod_map _ _ (fun p _ => hN p)
    _ = N (((primeFactors a).map Subtype.val).prod):=by
      rw [← Multiset.prod_hom _ N,Multiset.map_map]
      rfl
    _ = N a:=by rw [prod_primeFactors a ha]
lemma card_le [Fintype ι] (N:α →*₀ ℕ)
    (c:{p:α // Prime p} → ℕ × ι) (hc:Function.Injective c)
    (hp:∀ p, (c p).1.Prime) (hN:∀ p, (c p).1 ≤ N p.val)
    (S:Finset α) (B:ℕ) (hzero:∀ a ∈ S, a ≠ 0) (hbound:∀ a ∈ S, N a ≤ B) :
    S.card ≤ 2^(Fintype.card ι)*B^2:=by
  classical
  have he:(S.image (encode c)).card = S.card:=Finset.card_image_iff.mpr (by
    intro a ha b hb hab
    exact encode_injective c hc hp (hzero a ha) (hzero b hb) hab)
  rw [← he]
  apply zc1.card_le
  · intro x hx i
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    apply PrimeMultiset.zmx
    intro q hq
    obtain ⟨p,_,rfl⟩:=Multiset.mem_map.mp hq
    exact hp p
  · intro x hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    exact (zjj N c hN a (hzero a ha)).trans (hbound a ha)
end z7r

namespace z9l
open NumberField
open scoped BigOperators
variable (K:Type*) [Field K] [NumberField K]
private abbrev z5h:={P:Ideal (𝓞 K) // Prime P}
private def base (p:Nat.Primes):Ideal ℤ:=Ideal.span {(p.val:ℤ)}
private lemma zcb (p:Nat.Primes):base p ≠ ⊥:=by
  intro h
  have hp:(p.val:ℤ) = 0:=Ideal.span_singleton_eq_bot.mp h
  exact p.property.ne_zero (by exact_mod_cast hp)
private instance zo0 (p:Nat.Primes):(base p).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast p.property.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp p.property)).isMaximal (zcb p)
private noncomputable def z7q (P:z5h K):Nat.Primes:=by
  letI:P.val.IsPrime:=Ideal.isPrime_of_prime P.property
  letI:NeZero P.val:=⟨P.property.ne_zero⟩
  exact ⟨Ideal.absNorm (Ideal.under ℤ P.val),Nat.absNorm_under_prime P.val⟩
private lemma mem_fiber (P:z5h K) :
    P.val ∈ primesOverFinset (base (z7q K P)) (𝓞 K):=by
  letI:P.val.IsPrime:=Ideal.isPrime_of_prime P.property
  have he:base (z7q K P) = Ideal.under ℤ P.val:=Int.ideal_span_absNorm_eq_self _
  letI:P.val.LiesOver (base (z7q K P)):=by rw [he]; infer_instance
  exact (mem_primesOverFinset_iff (zcb _) _).mpr ⟨inferInstance,inferInstance⟩
private noncomputable def slot (p:Nat.Primes) :
    (primesOverFinset (base p) (𝓞 K)) ↪ Fin (Module.finrank ℚ K):=by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  change Fintype.card ↥(primesOverFinset (base p) (𝓞 K)) ≤ Fintype.card (Fin (Module.finrank ℚ K))
  rw [Fintype.card_coe,Fintype.card_fin]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (zcb p)
private noncomputable def toSigma:z5h K ↪
    (Σ p:Nat.Primes, (primesOverFinset (base p) (𝓞 K))) where
  toFun P:=⟨z7q K P,⟨P.val,mem_fiber K P⟩⟩
  inj':=by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun x => x.2.val) h
private noncomputable def code:z5h K ↪ ℕ × Fin (Module.finrank ℚ K) :=
  (toSigma K).trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl Nat.Primes) (slot K)).trans
      ((Equiv.sigmaEquivProd Nat.Primes (Fin (Module.finrank ℚ K))).toEmbedding.trans
        (Function.Embedding.prodMap ⟨Subtype.val,Subtype.val_injective⟩ (Function.Embedding.refl _))))
private lemma zmw (P:z5h K):((code K) P).1.Prime :=
  (z7q K P).property
private lemma zlh (P:z5h K):((code K) P).1 ≤ Ideal.absNorm P.val:=by
  letI:P.val.IsPrime:=Ideal.isPrime_of_prime P.property
  letI:NeZero P.val:=⟨P.property.ne_zero⟩
  have hp:(Ideal.under ℤ P.val).IsPrime:=inferInstance
  have hp0:Ideal.under ℤ P.val ≠ ⊥:=by
    intro h
    have hh:=Nat.absNorm_under_prime P.val
    rw [h] at hh
    exact Nat.not_prime_zero (by simpa using hh)
  letI:(Ideal.under ℤ P.val).IsMaximal:=hp.isMaximal hp0
  change Ideal.absNorm (Ideal.under ℤ P.val) ≤ _
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.val (Ideal.under ℤ P.val) hp hp0]
  exact Nat.le_self_pow (Ideal.inertiaDeg'_ne_zero (Ideal.under ℤ P.val) P.val) _
lemma card_le (S:Finset (Ideal (𝓞 K))) (B:ℕ)
    (hzero:∀ I ∈ S, I ≠ ⊥) (hbound:∀ I ∈ S, Ideal.absNorm I ≤ B) :
    S.card ≤ 2^(Module.finrank ℚ K)*B^2:=by
  classical
  simpa using z7r.card_le Ideal.absNorm (code K) (code K).injective
    (zmw K) (zlh K) S B hzero hbound
end z9l
open MeasureTheory
open scoped ENNReal BigOperators
namespace z3b
def simplex {ι:Type*} [Fintype ι] (a:ℝ):Set (ι → ℝ) :=
  {x | (∀ i, -a ≤ x i) ∧ ∑ i, x i ≤ a}
lemma znn {ι:Type*} [Fintype ι] [Nonempty ι] (a:ℝ) (ha:0 ≤ a)
    (x:ι → ℝ) (hx:x ∈ simplex a) :
    ∑ i, |x i| ≤ 3*(Fintype.card ι)*a:=by
  classical
  have hp (i:ι):|x i| ≤ x i+2*a:=by
    apply abs_le.mpr
    constructor <;> linarith [hx.1 i]
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hc:(1:ℝ) ≤ Fintype.card ι:=by exact_mod_cast Fintype.card_pos
  have hc':=mul_le_mul_of_nonneg_right hc ha
  linarith [hx.2]
lemma znb {ι:Type*} [Fintype ι] [Nonempty ι] (a:ℝ) (ha:0 ≤ a) :
    volume (simplex (ι:=ι) a) ≤ ENNReal.ofReal ((18*a)^(Fintype.card ι)):=by
  classical
  let r:=Fintype.card ι
  have hs:simplex (ι:=ι) a ⊆ {x:ι → ℝ | ∑ i, |x i| ≤ 3*r*a} :=
    fun x hx => znn a ha x hx
  have hv:volume {x:ι → ℝ | ∑ i, |x i| ≤ 3*r*a} =
      ENNReal.ofReal ((3*r*a)^r * (2^r / r.factorial)):=by
    have h:=volume_sum_rpow_le ι (p:=1) le_rfl (3*r*a)
    simp only [Real.rpow_one,div_one,one_add_one_eq_two,Real.Gamma_two,mul_one,
      Real.Gamma_nat_eq_factorial] at h
    rw [h,← ENNReal.ofReal_pow (by positivity:0 ≤ 3*(r:ℝ)*a),
      ← ENNReal.ofReal_mul (by positivity:0 ≤ (3*(r:ℝ)*a)^r)]
  have he:(r:ℝ)^r / r.factorial ≤ (3:ℝ)^r:=by
    have h:=Real.pow_div_factorial_le_exp (r:ℝ) (Nat.cast_nonneg _) r
    have he':Real.exp (r:ℝ) = (Real.exp 1)^r:=by simpa only [mul_one] using Real.exp_nat_mul 1 r
    rw [he'] at h
    exact h.trans (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans (by norm_num)) r)
  have hb:(3*(r:ℝ)*a)^r * (2^r / r.factorial) ≤ (18*a)^r:=by
    calc
      _ = (6*a)^r * ((r:ℝ)^r / r.factorial):=by rw [show (6:ℝ) = 3*2 by norm_num]; simp only [mul_pow]; ring
      _ ≤ (6*a)^r * (3:ℝ)^r:=mul_le_mul_of_nonneg_left he (by positivity)
      _ = _:=by rw [← mul_pow]; congr 1; ring
  exact (measure_mono hs).trans (hv ▸ ENNReal.ofReal_le_ofReal hb)
end z3b
namespace zc3
open MeasureTheory
open scoped ENNReal Pointwise
lemma zcj {G E:Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ:Measure E) [VAddInvariantMeasure G E μ]
    (F S:Set E) (hF:IsAddFundamentalDomain G F μ)
    (hcover:∀ x:E, ∃ g:G, g +ᵥ x ∈ S):μ F ≤ μ S:=by
  have hsub:F ⊆ ⋃ g:G, (g +ᵥ S) ∩ F:=by
    intro x hx
    obtain ⟨g,hg⟩:=hcover x
    refine Set.mem_iUnion.mpr ⟨-g,?_,hx⟩
    exact ⟨g +ᵥ x,hg,neg_vadd_vadd g x⟩
  calc
    μ F ≤ μ (⋃ g:G, (g +ᵥ S) ∩ F):=measure_mono hsub
    _ ≤ ∑' g:G, μ ((g +ᵥ S) ∩ F):=measure_iUnion_le _
    _ = μ S:=(hF.measure_eq_tsum S).symm
lemma z8k {ι:Type*} [Fintype ι] [Nonempty ι]
    (L:Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (T:Finset (ι → ℝ)) (a:ℝ) (ha:0 ≤ a)
    (hcover:∀ x:ι → ℝ, ∃ g:L, ∃ t ∈ T,
      (g:ι → ℝ)+x-t ∈ z3b.simplex a) :
    ZLattice.covolume L ≤ T.card * (18*a)^(Fintype.card ι):=by
  classical
  letI:MeasurableVAdd L (ι → ℝ) :=
    (inferInstance:MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI:VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance:VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b:=Module.Free.chooseBasis ℤ L
  let F:=ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF:IsAddFundamentalDomain L F volume:=ZLattice.isAddFundamentalDomain b volume
  let S:Set (ι → ℝ):=⋃ t:T, t.val +ᵥ z3b.simplex a
  have hs:∀ x:ι → ℝ, ∃ g:L, g +ᵥ x ∈ S:=by
    intro x
    obtain ⟨g,t,ht,hmem⟩:=hcover x
    refine ⟨g,Set.mem_iUnion.mpr ⟨⟨t,ht⟩,?_⟩⟩
    refine ⟨(g:ι → ℝ)+x-t,hmem,?_⟩
    change t+((g:ι → ℝ)+x-t) = (g:ι → ℝ)+x
    abel
  have hS:volume S ≤ (T.card:ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)):=by
    calc
      volume S ≤ ∑' t:T, volume (t.val +ᵥ z3b.simplex a):=measure_iUnion_le _
      _ = (T.card:ℝ≥0∞)*volume (z3b.simplex (ι:=ι) a):=by simp [tsum_fintype]
      _ ≤ _:=mul_le_mul_right (z3b.znb a ha) _
  have h:=(zcj volume F S hF hs).trans hS
  have hr:=ENNReal.toReal_mono (by finiteness :
    (T.card:ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)) ≠ ⊤) h
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at hr
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hr
end zc3
namespace z3x
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical
variable (K:Type*) [Field K] [NumberField K]
private noncomputable def extend (x:logSpace K) (w:InfinitePlace K):ℝ :=
  if h:w = w₀ then -∑ i, x i else x ⟨w,h⟩
private lemma ziw (x:logSpace K):∑ w, extend K x w = 0:=by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have hs:(∑ i:{w:InfinitePlace K // w ≠ w₀}, extend K x i.val) = ∑ i, x i:=by
    apply Finset.sum_congr rfl
    intro i _
    exact dif_neg i.property
  rw [hs]
  simp [extend]
private noncomputable def radii (t:ℝ) (x:logSpace K) (w:InfinitePlace K):ℝ≥0 :=
  ⟨Real.exp (t+extend K x w/(mult w:ℝ)),(Real.exp_pos _).le⟩
private lemma radii_coe (t:ℝ) (x:logSpace K) (w:InfinitePlace K) :
    ((radii K t x w:ℝ≥0):ℝ) = Real.exp (t+extend K x w/(mult w:ℝ)):=rfl
private lemma ziz (t:ℝ) (x:logSpace K) :
    (∏ w:InfinitePlace K, (radii K t x w:ℝ≥0∞)^(mult w)) =
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K:ℝ)*t)):=by
  classical
  have hreal:((∏ w:InfinitePlace K, (radii K t x w)^(mult w):ℝ≥0):ℝ) =
      Real.exp ((Module.finrank ℚ K:ℝ)*t):=by
    simp only [NNReal.coe_prod,NNReal.coe_pow,radii_coe,← Real.exp_nat_mul]
    rw [← Real.exp_sum]
    congr 1
    have he (w:InfinitePlace K):(mult w:ℝ)*(t+extend K x w/(mult w:ℝ)) =
        (mult w:ℝ)*t+extend K x w:=by
      have hm:(mult w:ℝ) ≠ 0:=mult_coe_ne_zero
      field_simp
    simp_rw [he]
    rw [Finset.sum_add_distrib,ziw,add_zero,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hnn:(∏ w:InfinitePlace K, (radii K t x w)^(mult w):ℝ≥0) =
      NNReal.mk (Real.exp ((Module.finrank ℚ K:ℝ)*t)) (Real.exp_pos _).le:=NNReal.eq hreal
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_finset_prod,hnn,ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
lemma zja (t:ℝ)
    (hM:minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K:ℝ)*t)))
    (x:logSpace K):∃ a:𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a:K)) ≤ Real.exp ((Module.finrank ℚ K:ℝ)*t) ∧
      ∀ w:InfinitePlace K, (mult w:ℝ)*Real.log (w (a:K)) ≤
        extend K x w+(mult w:ℝ)*t:=by
  classical
  obtain ⟨a,ha,hab⟩:=exists_ne_zero_mem_ringOfIntegers_lt K (f:=radii K t x)
    (by rw [convexBodyLT_volume,ENNReal.coe_finset_prod]; simp_rw [ENNReal.coe_pow]; rw [ziz]; exact hM)
  refine ⟨a,ha,?_,?_⟩
  · rw [mixedEmbedding.norm_apply]
    have hh:(∏ w:InfinitePlace K, normAtPlace w (mixedEmbedding K (a:K))^(mult w)) ≤
        ∏ w:InfinitePlace K, (radii K t x w:ℝ)^(mult w):=by
      apply Finset.prod_le_prod
      · intro w _; exact pow_nonneg (normAtPlace_nonneg _ _) _
      · intro w _
        rw [normAtPlace_apply]
        exact pow_le_pow_left₀ (apply_nonneg w _) (hab w).le _
    apply hh.trans_eq
    have hp:=congrArg ENNReal.toReal (ziz K t x)
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hp
  · intro w
    have hp:0 < w (a:K):=pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha)
    have hl:Real.log (w (a:K)) < t+extend K x w/(mult w:ℝ) :=
      (Real.log_lt_iff_lt_exp hp).mpr (hab w)
    have hm:(0:ℝ) ≤ mult w:=Nat.cast_nonneg _
    have he:=mul_le_mul_of_nonneg_left hl.le hm
    have hn:(mult w:ℝ) ≠ 0:=mult_coe_ne_zero
    rw [mul_add, mul_div_cancel₀ _ hn] at he
    linarith
end z3x
namespace z3x
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical
variable (K:Type*) [Field K] [NumberField K]
private noncomputable def z52 (a:K) (w:InfinitePlace K):ℝ :=
  (mult w:ℝ)*(Real.log (w a)-Real.log (mixedEmbedding.norm (mixedEmbedding K a))/(Module.finrank ℚ K:ℝ))
private lemma zgo (a:K) (i:{w:InfinitePlace K // w ≠ w₀}) :
    logMap (mixedEmbedding K a) i = z52 K a i.val:=by
  simp [logMap_apply,z52,div_eq_mul_inv]
private lemma zm3 (a:K) (ha:a ≠ 0):∑ w, z52 K a w = 0:=by
  have hs:Real.log (mixedEmbedding.norm (mixedEmbedding K a)) =
      ∑ w:InfinitePlace K, (mult w:ℝ)*Real.log (w a):=by
    rw [mixedEmbedding.norm_apply,Real.log_prod]
    · simp [normAtPlace_apply,Real.log_pow]
    · intro w _
      rw [normAtPlace_apply]
      exact pow_ne_zero _ ((pos_iff.mpr ha).ne')
  simp only [z52,mul_sub,Finset.sum_sub_distrib]
  rw [← hs,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hd:(Module.finrank ℚ K:ℝ) ≠ 0:=by exact_mod_cast Module.finrank_pos.ne'
  field_simp
  ring
private lemma z8c (a:𝓞 K) (ha:a ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (a:K)):=by
  rw [norm_eq_norm,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)
lemma zdx (t:ℝ) (ht:0 ≤ t)
    (hM:minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K:ℝ)*t)))
    (x:logSpace K):∃ a:𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a:K)) ≤ Real.exp ((Module.finrank ℚ K:ℝ)*t) ∧
      x-logMap (mixedEmbedding K (a:K)) ∈ z3b.simplex (2*t):=by
  obtain ⟨a,ha,hanorm,hbound⟩:=zja K t hM x
  have hN:0 ≤ Real.log (mixedEmbedding.norm (mixedEmbedding K (a:K))) :=
    Real.log_nonneg (z8c K a ha)
  have hfull:∀ w:InfinitePlace K, z52 K (a:K) w ≤ extend K x w+2*t:=by
    intro w
    have hm:(mult w:ℝ) ≤ 2:=by simp only [mult]; split_ifs <;> norm_num
    have hm0:(0:ℝ) ≤ mult w:=Nat.cast_nonneg _
    have hd:(0:ℝ) ≤ Module.finrank ℚ K:=Nat.cast_nonneg _
    have hn:=mul_nonneg hm0 (div_nonneg hN hd)
    have hb:=hbound w
    have hc:=mul_le_mul_of_nonneg_right hm ht
    dsimp only [z52]
    nlinarith
  let δ:InfinitePlace K → ℝ:=fun w => extend K x w-z52 K (a:K) w
  have hid (i:{w:InfinitePlace K // w ≠ w₀}) :
      (x-logMap (mixedEmbedding K (a:K))) i = δ i.val:=by
    rw [Pi.sub_apply,zgo]
    dsimp only [δ,extend]
    rw [dif_neg i.property]
  have hsum:δ w₀ + ∑ i:{w:InfinitePlace K // w ≠ w₀}, δ i.val = 0:=by
    rw [← Fintype.sum_eq_add_sum_subtype_ne δ w₀]
    dsimp only [δ]
    rw [Finset.sum_sub_distrib,ziw,zm3 K (a:K) (RingOfIntegers.coe_ne_zero_iff.mpr ha)]
    simp
  refine ⟨a,ha,hanorm,?_,?_⟩
  · intro i
    rw [hid]
    dsimp only [δ]
    linarith [hfull i.val]
  · simp_rw [hid]
    have hh:=hfull w₀
    dsimp only [δ] at hsum ⊢
    linarith
end z3x
namespace zd4
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical
variable (K:Type*) [Field K] [NumberField K]
private lemma zl7 (a:𝓞 K) :
    (Ideal.absNorm (Ideal.span {a}):ℝ) = mixedEmbedding.norm (mixedEmbedding K (a:K)):=by
  rw [Ideal.absNorm_span_singleton,norm_eq_norm,← Algebra.coe_norm_int]
  simp
lemma z6h (t:ℝ) (ht:0 ≤ t) (B:ℕ)
    (hrank:0 < NumberField.Units.rank K)
    (hM:minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K:ℝ)*t)))
    (hB:Real.exp ((Module.finrank ℚ K:ℝ)*t) ≤ (B:ℝ)) :
    NumberField.Units.regulator K ≤
      (2:ℝ)^(Module.finrank ℚ K)*(B:ℝ)^2*(36*t)^(NumberField.Units.rank K):=by
  classical
  let Iset:Finset (Ideal (𝓞 K)):=((Ideal.finite_setOfPred_absNorm_le B).toFinset).filter
    (fun I => ∃ a:𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I)
  have hgen:∀ I:Iset, ∃ a:𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I.val :=
    fun I => (Finset.mem_filter.mp I.property).2
  choose gen hgen0 hgenspan using hgen
  let T:Finset (logSpace K):=Iset.attach.image
    (fun I => logMap (mixedEmbedding K (gen I:K)))
  have hIcard:Iset.card ≤ 2^(Module.finrank ℚ K)*B^2:=by
    apply z9l.card_le
    · intro I hI
      obtain ⟨a,ha,rfl⟩:=(Finset.mem_filter.mp hI).2
      exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
    · intro I hI
      simpa using (Finset.mem_filter.mp hI).1
  have hTcard:T.card ≤ 2^(Module.finrank ℚ K)*B^2:=by
    exact (Finset.card_image_le.trans_eq Finset.card_attach).trans hIcard
  have hcover:∀ x:logSpace K, ∃ g:NumberField.Units.unitLattice K, ∃ z ∈ T,
      (g:logSpace K)+x-z ∈ z3b.simplex (2*t):=by
    intro x
    obtain ⟨a,ha,hanorm,haapprox⟩:=z3x.zdx K t ht hM x
    have hI:Ideal.span {a} ∈ Iset:=by
      apply Finset.mem_filter.mpr
      refine ⟨(Set.Finite.mem_toFinset _).mpr ?_,a,ha,rfl⟩
      change Ideal.absNorm (Ideal.span {a}) ≤ B
      exact_mod_cast (show (Ideal.absNorm (Ideal.span {a}):ℝ) ≤ B by
        rw [zl7]; exact hanorm.trans hB)
    let I:Iset:=⟨Ideal.span {a},hI⟩
    obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp (hgenspan I)
    have hmul:mixedEmbedding K (a:K) =
        mixedEmbedding K (u:K)*mixedEmbedding K (gen I:K):=by
      rw [← map_mul]
      congr 1
      have hh:=congrArg (algebraMap (𝓞 K) K) hu
      simpa only [map_mul,mul_comm] using hh.symm
    have hn:=z3x.z8c K (gen I) (hgen0 I)
    have hlog:logMap (mixedEmbedding K (a:K)) =
        NumberField.Units.logEmbedding K (Additive.ofMul u)+logMap (mixedEmbedding K (gen I:K)):=by
      rw [hmul,logMap_mul (by rw [norm_unit]; norm_num) ((lt_of_lt_of_le zero_lt_one hn).ne'),
        logMap_eq_logEmbedding]
    let lu:NumberField.Units.unitLattice K :=
      ⟨NumberField.Units.logEmbedding K (Additive.ofMul u),
        Submodule.mem_map.mpr ⟨Additive.ofMul u,Submodule.mem_top,rfl⟩⟩
    refine ⟨-lu,logMap (mixedEmbedding K (gen I:K)),?_,?_⟩
    · exact Finset.mem_image.mpr ⟨I,Finset.mem_attach _ _,rfl⟩
    · rw [hlog] at haapprox
      convert haapprox using 1
      change -(NumberField.Units.logEmbedding K (Additive.ofMul u))+x-
        logMap (mixedEmbedding K (gen I:K)) = _
      abel
  have hcard:Fintype.card {w:InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K:=by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  letI:Nonempty {w:InfinitePlace K // w ≠ w₀}:=Fintype.card_pos_iff.mp (hcard.symm ▸ hrank)
  have hc:=zc3.z8k (NumberField.Units.unitLattice K)
    T (2*t) (by positivity) hcover
  have hh:(T.card:ℝ) ≤ (2:ℝ)^(Module.finrank ℚ K)*(B:ℝ)^2:=by exact_mod_cast hTcard
  apply hc.trans
  rw [hcard,show 18*(2*t) = 36*t by ring]
  exact mul_le_mul_of_nonneg_right hh (by positivity)
private lemma zgf (R:ℕ) (hR:0 < R)
    (hD:|(NumberField.discr K:ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ K)) :
    minkowskiBound K 1 ≤ (2*(R:ℝ≥0∞))^(Module.finrank ℚ K):=by
  have hsqrt:(NNReal.sqrt ‖NumberField.discr K‖₊:ℝ≥0∞) ≤ (R:ℝ≥0∞)^(Module.finrank ℚ K):=by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hh:Real.sqrt |(NumberField.discr K:ℝ)| ≤ (R:ℝ)^(Module.finrank ℚ K) :=
      Real.sqrt_le_iff.mpr ⟨by positivity,by simpa only [← pow_mul,mul_comm 2] using hD⟩
    simpa [Real.coe_sqrt,Int.norm_eq_abs] using hh
  rw [minkowskiBound,volume_fundamentalDomain_fractionalIdealLatticeBasis,
    volume_fundamentalDomain_latticeBasis,mixedEmbedding.finrank]
  simp only [Units.val_one,FractionalIdeal.absNorm_one,Rat.cast_one,ENNReal.ofReal_one,one_mul]
  have hi:(2⁻¹:ℝ≥0∞)^(nrComplexPlaces K) ≤ 1:=pow_le_one₀ (by positivity) (by norm_num)
  calc
    _ ≤ (1*(R:ℝ≥0∞)^(Module.finrank ℚ K))*2^(Module.finrank ℚ K):=by gcongr
    _ = _:=by rw [one_mul,mul_pow,mul_comm]
lemma z5o (R:ℕ) (hR:0 < R)
    (hrank:0 < NumberField.Units.rank K)
    (hD:|(NumberField.discr K:ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R:ℝ)^3)^(Module.finrank ℚ K):=by
  have hRreal:(0:ℝ) < R:=by exact_mod_cast hR
  have hT:(0:ℝ) < 4*R:=by positivity
  have hT1:(1:ℝ) ≤ 4*R:=by
    have:(1:ℝ) ≤ R:=by exact_mod_cast hR
    linarith
  have ht:0 ≤ Real.log (4*R:ℝ):=Real.log_nonneg hT1
  have hexp:Real.exp ((Module.finrank ℚ K:ℝ)*Real.log (4*R:ℝ)) = (4*R:ℝ)^(Module.finrank ℚ K):=by
    rw [Real.exp_nat_mul,Real.exp_log hT]
  have hM:minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K:ℝ)*Real.log (4*R:ℝ))):=by
    rw [hexp]
    have hpow:(2*(R:ℝ))^(Module.finrank ℚ K) < (4*(R:ℝ))^(Module.finrank ℚ K) :=
      pow_lt_pow_left₀ (by linarith) (by positivity) Module.finrank_pos.ne'
    have hpow':(2*(R:ℝ≥0∞))^(Module.finrank ℚ K) < ENNReal.ofReal ((4*R:ℝ)^(Module.finrank ℚ K)):=by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simpa [ENNReal.toReal_ofReal (by positivity:0 ≤ (4*R:ℝ)^(Module.finrank ℚ K))] using hpow
    have hfac:(1:ℝ≥0∞) ≤ convexBodyLTFactor K:=by exact_mod_cast one_le_convexBodyLTFactor K
    exact (zgf K R hR hD).trans_lt (hpow'.trans_le (le_mul_of_one_le_left (by positivity) hfac))
  have hB:Real.exp ((Module.finrank ℚ K:ℝ)*Real.log (4*R:ℝ)) ≤ ((4*R)^(Module.finrank ℚ K):ℕ):=by
    rw [hexp]
    push_cast
    rfl
  have h:=z6h K (Real.log (4*R:ℝ)) ht
    ((4*R)^(Module.finrank ℚ K)) hrank hM hB
  have hrankle:NumberField.Units.rank K ≤ Module.finrank ℚ K:=by
    have hc:=card_add_two_mul_card_eq_rank K
    simp only [NumberField.Units.rank,card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hlog:36*Real.log (4*R:ℝ) ≤ 144*R:=by linarith [Real.log_le_sub_one_of_pos hT]
  have hbase:(1:ℝ) ≤ 144*R:=by
    have:(1:ℝ) ≤ R:=by exact_mod_cast hR
    linarith
  have hfactor:(36*Real.log (4*R:ℝ))^(NumberField.Units.rank K) ≤
      (144*R:ℝ)^(Module.finrank ℚ K) :=
    (pow_le_pow_left₀ (by positivity) hlog _).trans (pow_le_pow_right₀ hbase hrankle)
  apply h.trans
  push_cast
  calc
    _ ≤ (2:ℝ)^(Module.finrank ℚ K)*((4*R:ℝ)^(Module.finrank ℚ K))^2*
        (144*R:ℝ)^(Module.finrank ℚ K):=mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (4608*(R:ℝ)^3)^(Module.finrank ℚ K):=by
      rw [pow_right_comm,← mul_pow,← mul_pow]
      congr 1
      ring
lemma zde (R:ℕ) (hR:0 < R)
    (hD:|(NumberField.discr K:ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R:ℝ)^3)^(Module.finrank ℚ K):=by
  by_cases hr:NumberField.Units.rank K = 0
  · have hcard:Fintype.card {w:InfinitePlace K // w ≠ w₀} = 0:=by
      simpa [hr] using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
    letI:IsEmpty {w:InfinitePlace K // w ≠ w₀}:=Fintype.card_eq_zero_iff.mp hcard
    have hreg:NumberField.Units.regulator K = 1:=by
      unfold NumberField.Units.regulator
      rw [ZLattice.covolume_eq_det _ (IsZLattice.basis _),Matrix.det_isEmpty,abs_one]
    rw [hreg]
    apply one_le_pow₀
    have hR1:(1:ℝ) ≤ R:=by exact_mod_cast hR
    have hh:=pow_le_pow_left₀ (by norm_num:(0:ℝ) ≤ 1) hR1 3
    norm_num at hh
    linarith
  · exact z5o K R hR (Nat.pos_of_ne_zero hr) hD
end zd4
open scoped Pointwise Combinatorics.Additive ComplexConjugate
namespace za1
lemma zf3 {G:Type*} [AddCommGroup G] [DecidableEq G]
    (A U:Finset G) :
    E[A,U] = ∑ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card:=by
  classical
  rw [Finset.addEnergy, Finset.card_filter]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=A) (t:=U)]
  simp only [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have he (b:G):a + u = b + v ↔ b = a + u - v:=by
    constructor
    · intro h; exact eq_sub_iff_add_eq.mpr h.symm
    · intro h; exact (eq_sub_iff_add_eq.mp h).symm
  simp_rw [he]
  simp
lemma zes {G:Type*} [AddCommGroup G] [DecidableEq G]
    (A U:Finset G) (L:ℕ)
    (h:∀ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤ L) :
    U.card ^ 2 * A.card ≤ (A + U).card * L:=by
  have he:E[A,U] ≤ A.card * L:=by
    rw [zf3]
    simpa using Finset.sum_le_sum (fun a ha => h a ha)
  have hc:=Finset.le_card_add_mul_addEnergy A U
  have hh:=hc.trans (Nat.mul_le_mul_left (A + U).card he)
  by_cases ha:A.card = 0
  · simp [ha]
  have hp:0 < A.card:=Nat.pos_of_ne_zero ha
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh]
lemma zgw (u p w:ℂ) (hw:w ≠ 0)
    (h₁:‖u‖ = ‖p‖) (h₂:‖u - w‖ = ‖u‖)
    (h₃:‖p - w‖ = ‖p‖):p = u ∨ p = w - u:=by
  have hn₁:u * conj u = p * conj p:=by rw [Complex.mul_conj', Complex.mul_conj', h₁]
  have hn₂:(u-w) * conj (u-w) = u * conj u:=by
    rw [Complex.mul_conj', Complex.mul_conj', h₂]
  have hn₃:(p-w) * conj (p-w) = p * conj p:=by
    rw [Complex.mul_conj', Complex.mul_conj', h₃]
  simp only [map_sub] at hn₂ hn₃
  have hh:(p-u) * (p+u-w) * conj w = 0:=by
    linear_combination u * hn₂ - p * hn₃ + w * hn₁
  have hw':conj w ≠ 0:=by simpa using hw
  have hz:=(mul_eq_zero.mp hh).resolve_right hw'
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h
lemma zbg (U:Finset ℂ) (r:ℝ)
    (hU:∀ u ∈ U, ‖u‖ = r) (w:ℂ) (hw:w ≠ 0) :
    ((U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)).card ≤ 2:=by
  classical
  let F:=(U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)
  by_cases he:F.Nonempty
  · obtain ⟨⟨u,v⟩, huv⟩:=he
    simp only [F, Finset.mem_filter, Finset.mem_product] at huv
    obtain ⟨⟨hu,hv⟩, huv'⟩:=huv
    have hs:F ⊆ {(u,v),(-v,-u)}:=by
      rintro ⟨p,q⟩ hpq
      simp only [F, Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨⟨hp,hq⟩, hpq'⟩:=hpq
      have hv':u-w = v:=by rw [← huv']; abel
      have hq':p-w = q:=by rw [← hpq']; abel
      have hc:=zgw u p w hw
        ((hU u hu).trans (hU p hp).symm)
        (by rw [hv', hU v hv, hU u hu])
        (by rw [hq', hU q hq, hU p hp])
      rcases hc with hc | hc
      · have hqv:q = v:=by rw [← hq', hc, hv']
        simp [hc,hqv]
      · have hpv:p = -v:=by rw [hc, ← huv']; abel
        have hqu:q = -u:=by rw [← hq', hc]; abel
        simp [hpv,hqu]
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have hz:F = ∅:=Finset.not_nonempty_iff_eq_empty.mp he
    change F.card ≤ 2
    simp [hz]
lemma zk9 (A:Finset ℂ)
    (hA:(A:Set ℂ).OMATriplewise fun x y z => ¬ OMAIsIsosceles x y z)
    {a w v:ℂ} (ha:a ∈ A) (hw:w ≠ 0) (hv:v ≠ 0)
    (haw:a+w ∈ A) (hav:a+v ∈ A) (hn:‖w‖ = ‖v‖):w = v:=by
  by_contra hne
  apply hA ha haw hav
    (by simpa using hw)
    (by simpa using hne)
    (by simpa using hv)
  apply Or.inr ∘ Or.inr
  simpa only [dist_self_add_left, dist_self_add_right] using hn.symm
lemma zmn (A U:Finset ℂ) (r:ℝ) (C:Finset ℝ)
    (hA:(A:Set ℂ).OMATriplewise fun x y z => ¬ OMAIsIsosceles x y z)
    (hU:∀ u ∈ U, ‖u‖ = r)
    (hC:∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C)
    {a:ℂ} (ha:a ∈ A) :
    ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤
      U.card + 2 * C.card:=by
  classical
  let E:=(U ×ˢ U).filter (fun uv => uv.1 ≠ uv.2 ∧ a+uv.1-uv.2 ∈ A)
  let color:ℂ × ℂ → ℝ:=fun uv => ‖uv.1-uv.2‖
  have hf (c:ℝ) (hc:c ∈ E.image color) :
      (E.filter (fun uv => color uv = c)).card ≤ 2:=by
    obtain ⟨⟨u,v⟩, huv, he⟩:=Finset.mem_image.mp hc
    have huv':=huv
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv'
    have hw:u-v ≠ 0:=sub_ne_zero.mpr huv'.2.1
    have hs:E.filter (fun uv => color uv = c) ⊆
        (U ×ˢ U).filter (fun uv => uv.1 - uv.2 = u-v):=by
      rintro ⟨p,q⟩ hpq
      obtain ⟨hpq,hcol⟩:=Finset.mem_filter.mp hpq
      simp only [E, Finset.mem_filter, Finset.mem_product] at hpq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr hpq.1, ?_⟩
      apply zk9 A hA ha (sub_ne_zero.mpr hpq.2.1) hw
      · simpa only [add_sub_assoc] using hpq.2.2
      · simpa only [add_sub_assoc] using huv'.2.2
      · exact hcol.trans he.symm
    exact (Finset.card_le_card hs).trans (zbg U r hU (u-v) hw)
  have hi:E.image color ⊆ C:=by
    intro c hc
    obtain ⟨⟨u,v⟩, huv, rfl⟩:=Finset.mem_image.mp hc
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv
    exact hC u huv.1.1 v huv.1.2 huv.2.1
  have he:E.card ≤ 2 * C.card :=
    (Finset.card_le_mul_card_image E 2 hf).trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hi))
  have hs:(U ×ˢ U).filter (fun uv => a+uv.1-uv.2 ∈ A) ⊆ U.diag ∪ E:=by
    rintro ⟨u,v⟩ huv
    obtain ⟨huv,hmem⟩:=Finset.mem_filter.mp huv
    by_cases h:u = v
    · subst v
      exact Finset.mem_union_left _ (by simpa using (Finset.mem_product.mp huv).1)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huv,h,hmem⟩)
  calc
    _ ≤ (U.diag ∪ E).card:=Finset.card_le_card hs
    _ ≤ U.diag.card + E.card:=Finset.card_union_le _ _
    _ ≤ U.card + 2*C.card:=by simpa using Nat.add_le_add_left he U.card
lemma zdu (A U:Finset ℂ) (r:ℝ) (C:Finset ℝ)
    (hA:(A:Set ℂ).OMATriplewise fun x y z => ¬ OMAIsIsosceles x y z)
    (hU:∀ u ∈ U, ‖u‖ = r)
    (hC:∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C) :
    U.card^2 * A.card ≤ (A+U).card * (U.card + 2*C.card) :=
  zes A U _ (fun _ ha => zmn A U r C hA hU hC ha)
end za1
namespace zfo
open scoped Pointwise
lemma zkf (C:ℕ):C * (4*C+5) < 2^(4*C+4):=by
  have hC:C+1 ≤ 2^C:=Nat.lt_two_pow_self
  have hpow:(C+1)^2 ≤ (2^C)^2:=Nat.pow_le_pow_left hC 2
  have hbound:C*(4*C+5) < 8*(C+1)^2:=by nlinarith
  have hexp:2*C+3 ≤ 4*C+4:=by omega
  calc
    C*(4*C+5) < 8*(C+1)^2:=hbound
    _ ≤ 8*(2^C)^2:=Nat.mul_le_mul_left 8 hpow
    _ = 2^(2*C+3):=by rw [pow_add, pow_mul']; norm_num; ring
    _ ≤ 2^(4*C+4):=Nat.pow_le_pow_right (by norm_num) hexp
lemma zgg (f:ℕ → ℕ) (C d:ℕ) (hd:0 < d)
    (hf:0 < f 0) (hbound:f (4*C+4) ≤ (C*(4*C+5))^d) :
    ∃ j < 4*C+4, f (j+1) ≤ 2^d * f j:=by
  by_contra! h
  have hlow:∀ j ≤ 4*C+4, (2^d)^j ≤ f j:=by
    intro j hj
    induction j with
    | zero => simpa using Nat.succ_le_of_lt hf
    | succ j ih =>
      have hj':j < 4*C+4:=by omega
      calc
        (2^d)^(j+1) = 2^d * (2^d)^j:=by rw [pow_succ'];
        _ ≤ 2^d * f j:=Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ f (j+1):=(h j hj').le
  have hlt:=Nat.pow_lt_pow_left (zkf C) (Nat.ne_of_gt hd)
  have hcomm:(2^d)^(4*C+4) = (2^(4*C+4))^d:=by rw [← pow_mul, ← pow_mul, mul_comm d]
  have hh:=(hlow _ le_rfl).trans hbound
  rw [hcomm] at hh
  exact hlt.not_ge hh
lemma z91 (U:Finset ℂ) (K C d:ℕ)
    (hd:0 < d) (hK:0 < K)
    (hunit:∀ u ∈ U, ‖u‖ = 1)
    (hlarge:(16*K)^d ≤ U.card)
    (hquot:(U/U).card ≤ K^d * U.card)
    (hpacking:∀ j ≤ 4*C+4, (j • U).card ≤ (C*(j+1))^d) :
    ∃ S:Finset ℂ, S.Nonempty ∧ S.card ≤ (C*(4*C+5))^d ∧
      ∀ A:Finset ℂ, A ⊆ S →
        (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) →
        2^d * A.card ≤ S.card:=by
  classical
  obtain ⟨j,hj,hstep⟩:=zgg (fun j => (j • U).card) C d hd
    (by simp) (by simpa only [Nat.add_assoc] using hpacking (4*C+4) le_rfl)
  have hU:U.Nonempty:=Finset.card_pos.mp ((by positivity:0 < (16*K)^d).trans_le hlarge)
  let S:Finset ℂ:=j • U
  have hS:S.Nonempty:=by
    exact Finset.Nonempty.nsmul hU
  refine ⟨S,hS,(hpacking j hj.le).trans ?_,?_⟩
  · exact Nat.pow_le_pow_left (Nat.mul_le_mul_left C (by omega)) d
  intro A hAS hA
  let colors:Finset ℝ:=(U/U).image (fun w => ‖1-w‖)
  have hc:∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ colors:=by
    intro u hu v hv _
    have hv0:v ≠ 0:=by intro hv0; simpa [hv0] using hunit v hv
    have heq:‖u-v‖ = ‖1-u/v‖:=by
      calc
        ‖u-v‖ = ‖(u/v-1)*v‖:=by congr 1; field_simp
        _ = ‖u/v-1‖:=by rw [norm_mul, hunit v hv, mul_one]
        _ = ‖1-u/v‖:=norm_sub_rev _ _
    rw [heq]
    exact Finset.mem_image.mpr ⟨u/v,Finset.div_mem_div hu hv,rfl⟩
  have hcol:colors.card ≤ K^d * U.card:=(Finset.card_image_le).trans hquot
  have he:=za1.zdu A U 1 colors hA hunit hc
  have hadd:(A+U).card ≤ 2^d * S.card:=by
    calc
      (A+U).card ≤ (S+U).card:=Finset.card_le_card (Finset.add_subset_add hAS subset_rfl)
      _ = ((j+1) • U).card:=by rw [add_nsmul, one_nsmul]
      _ ≤ 2^d * S.card:=hstep
  have he':U.card^2 * A.card ≤ 2^d * S.card * ((1+2*K^d)*U.card) :=
    he.trans (Nat.mul_le_mul hadd (by nlinarith [hcol]))
  have he'':U.card * A.card ≤ 2^d * S.card * (1+2*K^d):=by
    apply (Nat.mul_le_mul_right_iff (Finset.card_pos.mpr hU)).mp
    nlinarith [he']
  have hKpow:1 ≤ K^d:=Nat.one_le_pow _ _ hK
  have hfour:4 ≤ 4^d:=by
    simpa using Nat.pow_le_pow_right (by norm_num:0 < 4) hd
  have hcoef:2^d * (2^d * (1+2*K^d)) ≤ U.card:=by
    apply le_trans _ hlarge
    rw [mul_pow]
    have h16:(16:ℕ)^d = 2^d * 2^d * 4^d:=by
      rw [← mul_pow, ← mul_pow]; norm_num
    rw [h16]
    calc
      _ = (2^d * 2^d) * (1+2*K^d):=by ring
      _ ≤ (2^d * 2^d) * (4^d * K^d):=Nat.mul_le_mul_left _ (by nlinarith)
      _ = _:=by ring
  have hh:=Nat.mul_le_mul_right A.card hcoef
  have hh':=hh.trans he''
  have hp:0 < 2^d * (1+2*K^d):=by positivity
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh']
end zfo
open Filter
namespace OMA1207
lemma zcx {d n m:ℕ}
    (S:Finset (EuclideanSpace ℝ (Fin d))) (hS:S.card = n)
    (h:∀ A:Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      IsIsoscelesFree (A:Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m:=by
  unfold P
  refine le_trans (Nat.sInf_le ⟨S, hS, rfl⟩) ?_
  apply csSup_le'
  rintro k ⟨A, hAS, hA, rfl⟩
  exact h A hAS hA
private lemma z70 {ι:Type*} [Fintype ι]
    (p:ι → Polynomial ℂ) (hp:Function.Injective p) :
    ∃ t:ℂ, Function.Injective (fun i => (p i).eval t):=by
  classical
  let q:Polynomial ℂ:=∏ ij ∈ (Finset.univ:Finset ι).offDiag, (p ij.1 - p ij.2)
  have hq:q ≠ 0:=by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    exact sub_ne_zero.mpr (hp.ne (Finset.mem_offDiag.mp hij).2.2)
  obtain ⟨t, ht⟩:∃ t:ℂ, q.eval t ≠ 0:=by
    by_contra h
    push_neg at h
    exact hq (Polynomial.funext (by simpa using h))
  refine ⟨t, fun i j hij => ?_⟩
  by_contra hne
  apply ht
  dsimp only [q]
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i:=(i,j))
  · simp [hne]
  · simp [hij]
private lemma z8s {d n m:ℕ}
    (S:Finset (EuclideanSpace ℝ (Fin d))) (hn:n ≤ S.card)
    (h:∀ A:Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      IsIsoscelesFree (A:Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m:=by
  obtain ⟨T, hTS, hT⟩:=Finset.exists_subset_card_eq hn
  exact zcx T hT fun A hAT hA => h A (hAT.trans hTS) hA
private lemma zbp (S:Finset ℂ) (q:ℕ) :
    ∃ t:ℂ, Function.Injective
      (fun p:Fin q × S => (p.2:ℂ) + (p.1.val:ℂ)*t):=by
  classical
  let p:Fin q × S → Polynomial ℂ:=fun a =>
    Polynomial.C (a.2:ℂ) + Polynomial.monomial 1 (a.1.val:ℂ)
  have hp:Function.Injective p:=by
    intro a b hab
    have h0:=congrArg (fun f:Polynomial ℂ => f.coeff 0) hab
    have h1:=congrArg (fun f:Polynomial ℂ => f.coeff 1) hab
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_monomial, one_ne_zero, ↓reduceIte, add_zero] at h0
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial,
      one_ne_zero, ↓reduceIte, zero_add, Nat.cast_inj] at h1
    exact Prod.ext (Fin.ext h1) (Subtype.ext h0)
  obtain ⟨t,ht⟩:=z70 p hp
  refine ⟨t, ?_⟩
  simpa only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial,
    pow_one] using ht
lemma z7e (S:Finset ℂ) (q M:ℕ)
    (hS:∀ A:Finset ℂ, A ⊆ S →
      (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → A.card ≤ M) :
    ∃ T:Finset ℂ, T.card = q*S.card ∧
      ∀ A:Finset ℂ, A ⊆ T →
        (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → A.card ≤ q*M:=by
  classical
  obtain ⟨t,ht⟩:=zbp S q
  let f:Fin q × S → ℂ:=fun p => (p.2:ℂ) + (p.1.val:ℂ)*t
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ht]
    simp
  intro A hAS hA
  obtain ⟨B,hB,rfl⟩:=Finset.subset_image_iff.mp hAS
  rw [Finset.card_image_of_injective _ ht]
  have hrow (i:Fin q):(B.filter (fun p => p.1 = i)).card ≤ M:=by
    let D:=B.filter (fun p => p.1 = i)
    let C:=D.image (fun p => (p.2:ℂ))
    have hCsub:C ⊆ S:=by
      intro x hx
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hx
      exact p.2.property
    have hmem (x:ℂ) (hx:x ∈ C):x+(i.val:ℂ)*t ∈ B.image f:=by
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨hp,hi⟩:=Finset.mem_filter.mp hp
      have he:f p = (p.2:ℂ) + (i.val:ℂ)*t:=by simp [f,hi]
      exact he ▸ Finset.mem_image_of_mem f hp
    have hCfree:(C:Set ℂ).OMATriplewise fun x y z => ¬ OMAIsIsosceles x y z:=by
      intro x hx y hy z hz hxy hyz hxz hiso
      apply hA (hmem x hx) (hmem y hy) (hmem z hz)
        (by simpa using hxy) (by simpa using hyz) (by simpa using hxz)
      simpa only [OMAIsIsosceles, dist_add_right] using hiso
    have hinj:Set.InjOn (fun p:Fin q × S => (p.2:ℂ)) (D:Set (Fin q × S)):=by
      intro p hp r hr he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)
        (Subtype.ext he)
    have hc:=hS C hCsub hCfree
    dsimp only [C] at hc
    rwa [Finset.card_image_of_injOn hinj] at hc
  have he:B.card = ∑ i:Fin q, (B.filter (fun p => p.1 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (by
      intro p hp
      exact Finset.mem_univ p.1)
  rw [he]
  calc
    _ ≤ ∑ _i:Fin q, M:=Finset.sum_le_sum (fun i _ => hrow i)
    _ = q*M:=by simp
lemma z6x (S:Finset ℂ) (n M:ℕ)
    (hn:n ≤ S.card)
    (hS:∀ A:Finset ℂ, A ⊆ S →
      (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → A.card ≤ M) :
    P 2 n ≤ M:=by
  classical
  let e:=Complex.orthonormalBasisOneI.repr
  apply z8s (S.image e)
  · simpa only [Finset.card_image_of_injective _ e.injective] using hn
  · intro A hAS hA
    obtain ⟨B,hB,rfl⟩:=Finset.subset_image_iff.mp hAS
    rw [Finset.card_image_of_injective _ e.injective]
    apply hS B hB
    intro a ha b hb c hc hab hbc hac hiso
    apply hA (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
      (Finset.mem_image_of_mem _ hc) (e.injective.ne hab) (e.injective.ne hbc)
      (e.injective.ne hac)
    simpa only [OMAIsIsosceles, e.dist_map] using hiso
lemma z9k (S:Finset ℂ) (hSpos:S.Nonempty) (M n:ℕ)
    (hS:∀ A:Finset ℂ, A ⊆ S →
      (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ (n + S.card) * M:=by
  classical
  let q:=n / S.card + 1
  obtain ⟨T,hT,hbound⟩:=z7e S q M hS
  have hn:n ≤ T.card:=by
    rw [hT, mul_comm]
    exact (Nat.lt_mul_div_succ n hSpos.card_pos).le
  have hp:=z6x T n (q*M) hn hbound
  calc
    S.card * P 2 n ≤ S.card * (q*M):=Nat.mul_le_mul_left _ hp
    _ = (S.card * (n / S.card) + S.card) * M:=by dsimp [q]; ring
    _ ≤ (n+S.card)*M:=by
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le n S.card) _)
lemma z8l (S:Finset ℂ) (hSpos:S.Nonempty) (M n:ℕ)
    (hn:S.card ≤ n)
    (hS:∀ A:Finset ℂ, A ⊆ S →
      (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ 2*n*M:=by
  have h:=z9k S hSpos M n hS
  exact h.trans (Nat.mul_le_mul_right M (by omega))
lemma z6p (S:Finset ℂ) (hSpos:S.Nonempty)
    (L n:ℕ) (hn:S.card ≤ n)
    (hS:∀ A:Finset ℂ, A ⊆ S →
      (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) → L*A.card ≤ S.card) :
    L * P 2 n ≤ 2*n:=by
  by_cases hL:L = 0
  · simp [hL]
  have hLpos:=Nat.pos_of_ne_zero hL
  have h:=z8l S hSpos (S.card/L) n hn (by
    intro A hAS hA
    rw [Nat.le_div_iff_mul_le hLpos]
    simpa only [mul_comm] using hS A hAS hA)
  apply Nat.le_of_mul_le_mul_left (c:=S.card) _ hSpos.card_pos
  calc
    S.card * (L * P 2 n) = L * (S.card * P 2 n):=by ring
    _ ≤ L * (2*n*(S.card/L)):=Nat.mul_le_mul_left L h
    _ = (2*n) * (L*(S.card/L)):=by ring
    _ ≤ (2*n) * S.card:=Nat.mul_le_mul_left _ (Nat.mul_div_le S.card L)
    _ = S.card * (2*n):=by ring
private lemma zbo (H d a n:ℕ)
    (hH:0 < H) (hd:3 ≤ d) (hn:0 < n)
    (ha:2^d * a ≤ 2*n) (hb:n ≤ 2^(2*H*d)) :
    (a:ℝ) < (n:ℝ)^(1 - 1/(4*H:ℝ)):=by
  let L:=4*H
  have hL:0 < L:=by dsimp [L]; omega
  have he:L+2*H*d < d*L:=by dsimp [L]; nlinarith
  have hc:2^L * 2^(2*H*d) < 2^(d*L):=by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) he
  have hp:2^(d*L) * a^L ≤ 2^L * n^L:=by
    simpa only [mul_pow, ← pow_mul] using Nat.pow_le_pow_left ha L
  have hx:2^(d*L) * (a^L*n) < 2^(d*L) * n^L:=by
    calc
      _ = (2^(d*L) * a^L) * n:=by ring
      _ ≤ (2^L * n^L) * n:=Nat.mul_le_mul_right n hp
      _ = (2^L*n) * n^L:=by ring
      _ ≤ (2^L * 2^(2*H*d)) * n^L :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
      _ < _:=Nat.mul_lt_mul_of_pos_right hc (pow_pos hn L)
  have hx':a^L*n < n^L:=(Nat.mul_lt_mul_left (by positivity:0 < 2^(d*L))).mp hx
  have heL:L = (L-1)+1:=by omega
  have hnat:a^L < n^(L-1):=by
    have hen:n^L = n^(L-1)*n:=by
      calc
        n^L = n^((L-1)+1):=congrArg (fun t:ℕ => n^t) heL
        _ = _:=pow_succ n (L-1)
    rw [hen] at hx'
    exact (Nat.mul_lt_mul_right hn).mp hx'
  have hreal:(a:ℝ)^L < (n:ℝ)^(L-1):=by exact_mod_cast hnat
  have hLp:(0:ℝ) < L:=by exact_mod_cast hL
  have hexp:(1-1/(4*H:ℝ))*(L:ℝ) = ((L-1:ℕ):ℝ):=by
    rw [Nat.cast_sub (by omega:1 ≤ L), Nat.cast_one]
    have heq:(4*H:ℝ) = L:=by simp [L]
    rw [heq]
    field_simp
  have hpow:((n:ℝ)^(1-1/(4*H:ℝ)))^L = (n:ℝ)^(L-1):=by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hexp, Real.rpow_natCast]
  by_contra h
  have hle:(n:ℝ)^(1-1/(4*H:ℝ)) ≤ a:=le_of_not_gt h
  have hh:=pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hle L
  rw [hpow] at hh
  exact hreal.not_ge hh
lemma z48
    (H:ℕ) (hH:0 < H)
    (h:∀ m:ℕ, ∃ S:Finset ℂ, S.Nonempty ∧ S.card ≤ 2^(H*2^m) ∧
      ∀ A:Finset ℂ, A ⊆ S →
        (A:Set ℂ).OMATriplewise (fun x y z => ¬ OMAIsIsosceles x y z) →
          2^(2^m) * A.card ≤ S.card) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  have hHr:(0:ℝ) < H:=by exact_mod_cast hH
  refine ⟨1/(4*H:ℝ), by positivity, Filter.eventually_atTop.2 ⟨2^(4*H), ?_⟩⟩
  intro n hn
  have hnpos:0 < n:=(by positivity:0 < 2^(4*H)).trans_le hn
  let l:=Nat.log 2 n
  let q:=l/H
  let m:=Nat.log 2 q
  let d:=2^m
  have hl:4*H ≤ l:=Nat.le_log_of_pow_le (by norm_num) hn
  have hq:4 ≤ q:=(Nat.le_div_iff_mul_le hH).mpr (by simpa only [mul_comm] using hl)
  have hm:2 ≤ m:=Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hq)
  have hd:3 ≤ d:=by
    have hh:=Nat.pow_le_pow_right (by norm_num:0 < 2) hm
    norm_num at hh
    exact (by norm_num:3 ≤ 4).trans hh
  have hdq:d ≤ q:=Nat.pow_log_le_self 2 (by omega)
  have hqhigh:q+1 ≤ 2*d:=by
    have hh:=Nat.lt_pow_succ_log_self (by norm_num:1 < 2) q
    simpa only [pow_succ, mul_comm, Nat.lt_iff_add_one_le] using hh
  have hsmall:H*d ≤ l :=
    (Nat.mul_le_mul_left H hdq).trans (Nat.mul_div_le l H)
  have hlarge:l+1 ≤ 2*H*d:=by
    have hh:=Nat.lt_mul_div_succ l hH
    have hh':=Nat.mul_le_mul_left H hqhigh
    have:l < H*(2*d):=hh.trans_le hh'
    nlinarith
  obtain ⟨S,hSpos,hScard,hS⟩:=h m
  have hSn:S.card ≤ n:=hScard.trans
    ((Nat.pow_le_pow_right (by norm_num:0 < 2) hsmall).trans
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos)))
  have ha:=z6p S hSpos (2^d) n hSn hS
  have hb:n ≤ 2^(2*H*d) :=
    (Nat.lt_pow_succ_log_self (by norm_num:1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by norm_num:0 < 2) hlarge)
  exact zbo H d (P 2 n) n hH hd hnpos ha hb
end OMA1207
namespace OMA1207
open scoped Pointwise
end OMA1207
namespace OMA1207
open NumberField
open scoped Classical Pointwise
lemma z5k
    (K L:ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D:ℕ) (hR:0 < R)
    (hdegree:∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hreg:∀ m, NumberField.Units.regulator (L m) ≤ (R:ℝ)^(Module.finrank ℚ (L m)))
    (hrel:∀ m, Module.finrank (K m) (L m) = 2)
    (hgap:∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex:∀ m, ∃ σ:L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  let C:=4*z6k.z5b R ((16*500)^2)+1
  let H:=(C*(4*C+5)+1)*2*D
  have hD:0 < D:=by have hh:=hdegree 0; norm_num at hh; omega
  have hH:0 < H:=by dsimp [H]; positivity
  apply z48 H hH
  intro m
  obtain ⟨σ,hσ⟩:=hcomplex m
  obtain ⟨U,hunit,hlarge,hdiv,hpacking⟩:=z6k.zgt (K m) (L m) R hR
    (hreg m) (hrel m) (hgap m) σ hσ
  obtain ⟨S,hSpos,hScard,hS⟩:=zfo.z91 U 500 C
    (2*Module.finrank ℚ (L m)) (by have hh:0 < Module.finrank ℚ (L m):=Module.finrank_pos; positivity) (by norm_num)
    hunit hlarge hdiv (fun j _ => hpacking j)
  refine ⟨S,hSpos,?_,?_⟩
  · calc
      S.card ≤ (C*(4*C+5))^(2*Module.finrank ℚ (L m)):=hScard
      _ ≤ (C*(4*C+5))^(2*(D*2^m)):=Nat.pow_le_pow_right (by dsimp [C]; positivity) (Nat.mul_le_mul_left 2 (hdegree m).2)
      _ ≤ (2^(C*(4*C+5)+1))^(2*(D*2^m)):=Nat.pow_le_pow_left (by
        have hh:=Nat.lt_two_pow_self (n:=C*(4*C+5)+1)
        omega) _
      _ = 2^(H*2^m):=by rw [← pow_mul]; congr 1; dsimp [H]; ring
  · intro A hAS hA
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by have hh:=(hdegree m).1; omega))).trans
      (hS A hAS hA)
lemma z4t
    (K L:ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D:ℕ) (hR:0 < R)
    (hdegree:∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hdisc:∀ m, |(NumberField.discr (L m):ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ (L m)))
    (hrel:∀ m, Module.finrank (K m) (L m) = 2)
    (hgap:∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex:∀ m, ∃ σ:L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  apply z5k K L (4608*R^3) D (by positivity) hdegree
    (fun m => ?_) hrel hgap hcomplex
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
    zd4.zde (L m) R hR (hdisc m)
end OMA1207
namespace z2b
open Polynomial NumberField
open scoped Classical
private lemma zfp:Irreducible (X^4-C (5:ℤ)):=by
  let P:Ideal ℤ:=Ideal.span {5}
  have hmon:(X^4-C (5:ℤ)).Monic:=monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P:=P)
  · exact (Ideal.span_singleton_prime (by norm_num:(5:ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn4:n < 4:=by simpa only [degree_X_pow_sub_C (by norm_num:(0:ℕ) < 4),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega:n ≠ 4)]
    by_cases hn0:n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num:(0:ℕ) < 4)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive
lemma irreducible:Irreducible (X^4-C (5:ℚ)):=by
  have hh:=((monic_X_pow_sub_C (5:ℤ) (by norm_num:(4:ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K:=ℚ)).mp zfp
  simpa [C_ofNat] using hh
noncomputable instance:Fact (Irreducible (X^4-C (5:ℚ))):=⟨irreducible⟩
abbrev F:=AdjoinRoot (X^4-C (5:ℚ))
noncomputable def alpha:F:=AdjoinRoot.root (X^4-C (5:ℚ))
lemma znd:alpha^4 = 5:=by
  have hh:=AdjoinRoot.eval₂_root (X^4-C (5:ℚ))
  simpa [alpha,sub_eq_zero] using hh
lemma degree:Module.finrank ℚ F = 4:=by
  rw [(AdjoinRoot.powerBasis irreducible.ne_zero).finrank,AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C
noncomputable def rho:ℝ:=Real.sqrt (Real.sqrt 5)
lemma rho_pos:0 < rho:=by dsimp [rho]; positivity
lemma z8g:rho^4 = 5:=by
  have h₁:rho^2 = Real.sqrt 5:=Real.sq_sqrt (by positivity)
  have h₂:=Real.sq_sqrt (by norm_num:(0:ℝ) ≤ 5)
  nlinarith
lemma zmo (x:ℝ) (hx:x^4 = 5):x = rho ∨ x = -rho:=by
  have hs:(x^2)^2 = (rho^2)^2:=by nlinarith [z8g]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hh | hh
  · exact sq_eq_sq_iff_eq_or_eq_neg.mp hh
  · have hr:0 < rho^2:=pow_pos rho_pos _
    nlinarith [sq_nonneg x]
noncomputable def z4p (x:ℝ) (hx:x^4 = 5):F →+* ℂ :=
  Complex.ofRealHom.comp (AdjoinRoot.lift (f:=X^4-C (5:ℚ)) (algebraMap ℚ ℝ) x (by simp [hx]))
lemma z61 (x:ℝ) (hx:x^4 = 5):z4p x hx alpha = (x:ℂ):=by
  simp [z4p,alpha,AdjoinRoot.lift_root]
lemma zbw (x:ℝ) (hx:x^4 = 5):ComplexEmbedding.IsReal (z4p x hx):=by
  apply ComplexEmbedding.isReal_iff.mpr
  apply RingHom.ext
  intro a
  simp [ComplexEmbedding.conjugate_coe_eq,z4p]
lemma hom_ext {σ τ:F →+* ℂ} (h:σ alpha = τ alpha):σ = τ :=
  AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) h
lemma zib (σ:F →+* ℂ) (hσ:ComplexEmbedding.IsReal σ) :
    σ = z4p rho z8g ∨ σ = z4p (-rho) (by nlinarith [z8g]):=by
  let φ:F →+* ℝ:=hσ.embedding
  have hx:(φ alpha)^4 = 5:=by
    simpa only [map_pow,map_ofNat] using congrArg φ znd
  have hval:=hσ.coe_embedding_apply alpha
  rcases zmo (φ alpha) hx with h | h
  · left
    apply hom_ext
    rw [z61,← hval]
    exact congrArg Complex.ofReal h
  · right
    apply hom_ext
    rw [z61,← hval]
    exact congrArg Complex.ofReal h
lemma nrRealPlaces:InfinitePlace.nrRealPlaces F = 2:=by
  let p:{σ:F →+* ℂ // ComplexEmbedding.IsReal σ}:=⟨z4p rho z8g,zbw _ _⟩
  let n:{σ:F →+* ℂ // ComplexEmbedding.IsReal σ}:=⟨z4p (-rho) (by nlinarith [z8g]),zbw _ _⟩
  have hpn:p ≠ n:=by
    intro h
    have he:=congrArg (fun σ:{σ:F →+* ℂ // ComplexEmbedding.IsReal σ} => σ.val alpha) h
    change z4p rho z8g alpha = z4p (-rho) (by nlinarith [z8g]) alpha at he
    rw [z61,z61] at he
    have hr:rho = -rho:=Complex.ofReal_injective he
    linarith [rho_pos]
  have huniv:(Finset.univ:Finset {σ:F →+* ℂ // ComplexEmbedding.IsReal σ}) = {p,n}:=by
    ext σ
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    rcases zib σ.val σ.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [← InfinitePlace.card_real_embeddings,← Finset.card_univ,huniv,Finset.card_pair hpn]
end z2b
namespace z9c
open Polynomial NumberField
open scoped Classical
private lemma zfp:Irreducible (X^2-C (5:ℤ)):=by
  let P:Ideal ℤ:=Ideal.span {5}
  have hmon:(X^2-C (5:ℤ)).Monic:=monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P:=P)
  · exact (Ideal.span_singleton_prime (by norm_num:(5:ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn2:n < 2:=by simpa only [degree_X_pow_sub_C (by norm_num:(0:ℕ) < 2),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega:n ≠ 2)]
    by_cases hn0:n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num:(0:ℕ) < 2)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive
lemma irreducible_rat:Irreducible (X^2-C (5:ℚ)):=by
  have hh:=((monic_X_pow_sub_C (5:ℤ) (by norm_num:(2:ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K:=ℚ)).mp zfp
  simpa [C_ofNat] using hh
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
lemma zah (a:K) (ha:a^2 = 5) :
    ∃ φ:K →+* ℝ, φ a = -Real.sqrt 5:=by
  have hmin:minpoly ℚ a = X^2-C (5:ℚ) :=
    (minpoly.eq_of_irreducible_of_monic irreducible_rat (by simp [ha]) (monic_X_pow_sub_C _ (by norm_num))).symm
  have hroot:(-(Real.sqrt 5:ℂ)) ∈ (minpoly ℚ a).rootSet ℂ:=by
    rw [hmin,mem_rootSet_of_ne irreducible_rat.ne_zero]
    have hs:(Real.sqrt 5:ℂ)^2 = 5:=by
      exact_mod_cast Real.sq_sqrt (by norm_num:(0:ℝ) ≤ 5)
    simpa only [aeval_sub,map_pow,aeval_X,aeval_C,map_ofNat,neg_sq,sub_eq_zero] using hs
  rw [← Embeddings.range_eval_eq_rootSet_minpoly K ℂ a] at hroot
  obtain ⟨σ,hσ⟩:=hroot
  change σ a = -(Real.sqrt 5:ℂ) at hσ
  let hr:=IsTotallyReal.complexEmbedding_isReal σ
  refine ⟨hr.embedding,?_⟩
  apply Complex.ofReal_injective
  rw [hr.coe_embedding_apply,hσ,Complex.ofReal_neg]
lemma nonsquare (a:K) (ha:a^2 = 5):∀ b:K, b^2 ≠ a:=by
  obtain ⟨φ,hφ⟩:=zah K a ha
  intro b hb
  have hh:=congrArg φ hb
  rw [map_pow,hφ] at hh
  have hp:0 < Real.sqrt 5:=by positivity
  nlinarith [sq_nonneg (φ b)]
lemma zcr (a:K) (ha:a^2 = 5):Irreducible (X^2-C a) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (nonsquare K a ha)
end z9c
namespace z81
open NumberField
open scoped Classical BigOperators
variable (F K L:Type*) [Field F] [Field K] [Field L]
  [NumberField F] [NumberField K] [NumberField L]
  [Algebra F L] [Algebra K L] [FiniteDimensional F L] [IsTotallyReal K]
omit [NumberField F] [NumberField K] [NumberField L] [FiniteDimensional F L] in
lemma isReal_iff (hgen:Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤)
    (σ:L →+* ℂ) :
    ComplexEmbedding.IsReal σ ↔ ComplexEmbedding.IsReal (σ.comp (algebraMap F L)):=by
  refine ⟨fun h => h.comp _,fun h => ?_⟩
  let φ:K →+* ℂ:=σ.comp (algebraMap K L)
  letI:Algebra K ℂ:=φ.toAlgebra
  let a:L →ₐ[K] ℂ:={ σ with commutes':=fun _ => rfl }
  have hφ:ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b:L →ₐ[K] ℂ:={ ComplexEmbedding.conjugate σ with
    commutes':=fun r => DFunLike.congr_fun hφ r }
  have hab:b = a:=AlgHom.ext_of_adjoin_eq_top hgen (by
    rintro _ ⟨x,rfl⟩
    exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.mp h) x)
  exact ComplexEmbedding.isReal_iff.mpr (congrArg AlgHom.toRingHom hab)
omit [NumberField K] [Algebra K L] [IsTotallyReal K] in
lemma zj9 (φ:F →+* ℂ) :
    Fintype.card (ComplexEmbedding.Extension L φ) = Module.finrank F L:=by
  letI:Algebra F ℂ:=φ.toAlgebra
  let e:ComplexEmbedding.Extension L φ ≃ (L →ₐ[F] ℂ) :=
    { toFun σ:={ σ.val with commutes':=fun r => DFunLike.congr_fun (ComplexEmbedding.Extension.comp_eq σ) r }
      invFun σ:=⟨σ.toRingHom,⟨by ext r; exact σ.commutes r⟩⟩
      left_inv σ:=by rfl
      right_inv σ:=by rfl }
  exact (Fintype.card_congr e).trans (AlgHom.card F L ℂ)
omit [NumberField K] [Algebra K L] [IsTotallyReal K] in
lemma zhp
    (hreal:∀ σ:L →+* ℂ, ComplexEmbedding.IsReal (σ.comp (algebraMap F L)) → ComplexEmbedding.IsReal σ) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L:=by
  let e:{σ:L →+* ℂ // ComplexEmbedding.IsReal σ} ≃
      Σ φ:{φ:F →+* ℂ // ComplexEmbedding.IsReal φ}, ComplexEmbedding.Extension L φ.val :=
    { toFun σ:=⟨⟨σ.val.comp (algebraMap F L),σ.property.comp _⟩,⟨σ.val,⟨rfl⟩⟩⟩
      invFun p:=⟨p.2.val,hreal p.2.val (by rw [ComplexEmbedding.Extension.comp_eq p.2]; exact p.1.property)⟩
      left_inv σ:=rfl
      right_inv p:=by rcases p with ⟨⟨φ,hφ⟩,⟨σ,⟨hσ⟩⟩⟩; cases hσ; rfl }
  rw [← InfinitePlace.card_real_embeddings, Fintype.card_congr e,Fintype.card_sigma]
  simp only [zj9,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    InfinitePlace.card_real_embeddings,Nat.cast_id]
omit [NumberField K] in
lemma zbk
    (hgen:Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L :=
  zhp F L (fun σ h => (isReal_iff F K L hgen σ).mpr h)
end z81
namespace z2n
open NumberField Polynomial
open scoped Classical
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
lemma z50 (x:𝓞 L)
    (hgen:Algebra.adjoin K {(x:L)} = ⊤)
    (p:(𝓞 K)[X]) (hp:aeval x p = 0) :
    aeval x p.derivative ∈ differentIdeal (𝓞 K) (𝓞 L):=by
  obtain ⟨q,rfl⟩:=minpoly.isIntegrallyClosed_dvd (IsIntegralClosure.isIntegral (𝓞 K) L x) hp
  rw [derivative_mul,map_add,map_mul,map_mul,minpoly.aeval,zero_mul,add_zero]
  exact Ideal.mul_mem_right _ _ (aeval_derivative_mem_differentIdeal (𝓞 K) K L x hgen)
lemma zha (a:𝓞 K) (x:𝓞 L)
    (hgen:Algebra.adjoin K {(x:L)} = ⊤) (hx:x^2 = algebraMap (𝓞 K) (𝓞 L) a) :
    2*x ∈ differentIdeal (𝓞 K) (𝓞 L):=by
  have hh:=z50 K L x hgen (X^2-C a) (by simp [hx])
  simpa only [derivative_sub,derivative_pow,derivative_X,derivative_C,pow_one,
    mul_one,sub_zero,map_mul,map_natCast,aeval_X,Nat.reduceSub,aeval_C,Nat.cast_ofNat,map_ofNat] using hh
end z2n
namespace zaf
open NumberField
open scoped Classical BigOperators
variable (L:Type*) [Field L] [NumberField L]
lemma zgs (x:𝓞 L) :
    (Ideal.absNorm (Ideal.span {x}):ℝ) = ∏ σ:L →ₐ[ℚ] ℂ, ‖σ (x:L)‖:=by
  have h:=congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x:L))
  rw [← Algebra.coe_norm_int] at h
  simpa [Ideal.absNorm_span_singleton,norm_prod] using h
lemma zlj (x:𝓞 L) (H:ℝ)
    (hbound:∀ σ:L →+* ℂ, ‖σ (x:L)‖ ≤ H) :
    (Ideal.absNorm (Ideal.span {x}):ℝ) ≤ H^(Module.finrank ℚ L):=by
  rw [zgs]
  have hh:=Finset.prod_le_prod (s:=(Finset.univ:Finset (L →ₐ[ℚ] ℂ)))
    (fun σ _ => norm_nonneg (σ (x:L))) (fun σ _ => hbound σ.toRingHom)
  simpa only [Finset.prod_const,Finset.card_univ,AlgHom.card] using hh
end zaf
namespace QuadraticDiscriminant
open NumberField
open scoped Classical BigOperators
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
lemma zgq (a:𝓞 K) (x:𝓞 L) (hx0:x ≠ 0)
    (hgen:Algebra.adjoin K {(x:L)} = ⊤) (hx:x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (H:ℝ) (hhouse:∀ σ:L →+* ℂ, ‖σ (x:L)‖ ≤ H) :
    ((differentIdeal (𝓞 K) (𝓞 L)).absNorm:ℝ) ≤ (2*H)^(Module.finrank ℚ L):=by
  have hm:=z2n.zha K L a x hgen hx
  have hdvd:=Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
  have hpos:0 < (Ideal.span ({2*x}:Set (𝓞 L))).absNorm:=by
    apply Nat.pos_of_ne_zero
    rw [ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (by norm_num) hx0
  have hle:=Nat.le_of_dvd hpos hdvd
  apply (show ((differentIdeal (𝓞 K) (𝓞 L)).absNorm:ℝ) ≤ (Ideal.span ({2*x}:Set (𝓞 L))).absNorm by
    exact_mod_cast hle).trans
  apply zaf.zlj L (2*x) (2*H)
  intro σ
  norm_num only [map_mul,map_ofNat,norm_mul,RCLike.norm_two]
  exact mul_le_mul_of_nonneg_left (hhouse σ) (by norm_num:(0:ℝ) ≤ 2)
lemma znr (a:𝓞 K) (x:𝓞 L) (hx0:x ≠ 0)
    (hgen:Algebra.adjoin K {(x:L)} = ⊤) (hx:x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (hdeg:Module.finrank K L = 2) (R:ℕ)
    (hdisc:|(discr K:ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ K))
    (hhouse:∀ σ:L →+* ℂ, ‖σ (x:L)‖ ≤ 2) :
    |(discr L:ℝ)| ≤ (2*(R:ℝ))^(2*Module.finrank ℚ L):=by
  have hdiff:=zgq K L a x hx0 hgen hx 2 hhouse
  have he:=natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have her:|(discr L:ℝ)| = ((differentIdeal (𝓞 K) (𝓞 L)).absNorm:ℝ)*|(discr K:ℝ)|^2:=by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_natAbs,Int.cast_abs,hdeg] using
      congrArg (fun n:ℕ => (n:ℝ)) he
  have hd:=Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  rw [her]
  calc
    _ ≤ (4:ℝ)^(Module.finrank ℚ L)*((R:ℝ)^(2*Module.finrank ℚ K))^2:=by
      gcongr
      simpa only [show (2:ℝ)*2 = 4 by norm_num] using hdiff
    _ = (2*(R:ℝ))^(2*Module.finrank ℚ L):=by
      rw [show (4:ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul,mul_pow]
      congr 2; omega
end QuadraticDiscriminant

namespace z54
open Polynomial NumberField
open scoped Classical
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K] (a:K) [Fact (a^2 = 5)]
noncomputable instance:Fact (Irreducible (X^2-C a)) :=
  ⟨z9c.zcr K a Fact.out⟩
abbrev L:=AdjoinRoot (X^2-C a)
instance:Module.Finite K (L K a):=(monic_X_pow_sub_C a (by norm_num:(2:ℕ) ≠ 0)).finite_adjoinRoot
noncomputable instance:NumberField (L K a):=NumberField.of_module_finite K (L K a)
noncomputable def b:L K a:=AdjoinRoot.root (X^2-C a)
lemma b_sq:(b K a)^2 = algebraMap K (L K a) a:=root_X_pow_sub_C_pow 2 a
lemma b_pow:(b K a)^4 = 5:=by
  calc
    (b K a)^4 = ((b K a)^2)^2:=by ring
    _ = (algebraMap K (L K a) a)^2:=by rw [b_sq]
    _ = algebraMap K (L K a) (a^2):=(map_pow _ _ _).symm
    _ = 5:=by rw [show a^2 = 5 from Fact.out,map_ofNat]
lemma degree:Module.finrank K (L K a) = 2:=by
  rw [(AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out:Irreducible (X^2-C a)).ne_zero)).finrank,
    AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C
lemma zlf:Algebra.adjoin K {b K a} = ⊤:=by
  exact (AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out:Irreducible (X^2-C a)).ne_zero)).adjoin_gen_eq_top
noncomputable def zdz:z2b.F →+* L K a :=
  AdjoinRoot.lift (algebraMap ℚ (L K a)) (b K a) (by simp [b_pow])
noncomputable instance zny:Algebra z2b.F (L K a):=(zdz K a).toAlgebra
lemma zi2:algebraMap z2b.F (L K a) z2b.alpha = b K a:=by
  change zdz K a z2b.alpha = b K a
  simp [zdz,z2b.alpha,AdjoinRoot.lift_root]
lemma compositum:Algebra.adjoin K (Set.range (algebraMap z2b.F (L K a))) = ⊤:=by
  apply top_unique
  rw [← zlf K a]
  apply Algebra.adjoin_mono
  exact Set.singleton_subset_iff.mpr ⟨z2b.alpha,zi2 K a⟩
lemma znk:2*InfinitePlace.nrRealPlaces (L K a) = Module.finrank ℚ (L K a):=by
  have hr:=z81.zbk z2b.F K (L K a) (compositum K a)
  rw [z2b.nrRealPlaces] at hr
  have hd:=Module.finrank_mul_finrank ℚ z2b.F (L K a)
  rw [z2b.degree] at hd
  omega
omit [NumberField K] [IsTotallyReal K] in
lemma zmy:IsIntegral ℤ a:=by
  refine ⟨X^2-C (5:ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [show a^2 = 5 from Fact.out]
lemma zmq:IsIntegral ℤ (b K a):=by
  refine ⟨X^4-C (5:ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [b_pow]
noncomputable def intA:𝓞 K:=⟨a,zmy K a⟩
noncomputable def intB:𝓞 (L K a):=⟨b K a,zmq K a⟩
lemma znw (σ:L K a →+* ℂ):‖σ (b K a)‖ ≤ 2:=by
  have hp:=congrArg (fun z:L K a => ‖σ z‖) (b_pow K a)
  simp only [map_pow,norm_pow,map_ofNat,RCLike.norm_ofNat] at hp
  have hn:=norm_nonneg (σ (b K a))
  by_contra h
  have hh:2 < ‖σ (b K a)‖:=lt_of_not_ge h
  have hsq:4 < ‖σ (b K a)‖^2:=by nlinarith
  nlinarith [sq_nonneg (‖σ (b K a)‖^2-4)]
lemma z8q (R:ℕ)
    (hdisc:|(discr K:ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ K)) :
    |(discr (L K a):ℝ)| ≤ (2*(R:ℝ))^(2*Module.finrank ℚ (L K a)):=by
  apply QuadraticDiscriminant.znr K (L K a) (intA K a) (intB K a) ?_
    (zlf K a) ?_ (degree K a) R hdisc (znw K a)
  · intro h
    have hb0:b K a = 0:=congrArg (fun x:𝓞 (L K a) => (x:L K a)) h
    have hp:=b_pow K a
    rw [hb0] at hp
    norm_num at hp
  · apply RingOfIntegers.coe_injective
    exact b_sq K a
end z54
namespace z3i
open NumberField
open NumberField.InfinitePlace
open scoped Classical
lemma zht (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
    (hdeg:Module.finrank K L = 2) (hhalf:2*nrRealPlaces L = Module.finrank ℚ L) :
    4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L:=by
  have hL:=card_add_two_mul_card_eq_rank L
  have hK:=IsTotallyReal.finrank K
  have hz:=IsTotallyReal.nrComplexPlaces_eq_zero K
  have hd:=Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  have hp:0 < Module.finrank ℚ K:=Module.finrank_pos
  rw [NumberField.Units.rank,NumberField.Units.rank,
    card_eq_nrRealPlaces_add_nrComplexPlaces,card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega
lemma z9d (L:Type*) [Field L] [NumberField L]
    (hhalf:2*nrRealPlaces L = Module.finrank ℚ L) :
    ∃ σ:L →+* ℂ, ¬ ComplexEmbedding.IsReal σ:=by
  have hL:=card_add_two_mul_card_eq_rank L
  have hp:0 < Module.finrank ℚ L:=Module.finrank_pos
  have hc:0 < nrComplexPlaces L:=by omega
  obtain ⟨w⟩:=Fintype.card_pos_iff.mp hc
  exact ⟨w.val.embedding,isComplex_iff.mp w.property⟩
end z3i
namespace OMA1207
open NumberField
open scoped Classical
lemma z65
    (K:ℕ → Type*) [∀ m, Field (K m)] [∀ m, NumberField (K m)] [∀ m, IsTotallyReal (K m)]
    (a:∀ m, K m) (ha:∀ m, (a m)^2 = 5)
    (R D:ℕ) (hR:0 < R)
    (hdegree:∀ m, 2^m ≤ Module.finrank ℚ (K m) ∧ Module.finrank ℚ (K m) ≤ D*2^m)
    (hdisc:∀ m, |(discr (K m):ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ (K m))) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  letI:∀ m, Fact ((a m)^2 = 5):=fun m => ⟨ha m⟩
  let L:=fun m => z54.L (K m) (a m)
  have hrel (m:ℕ):Module.finrank (K m) (L m) = 2:=z54.degree (K m) (a m)
  have hhalf (m:ℕ):2*InfinitePlace.nrRealPlaces (L m) = Module.finrank ℚ (L m) :=
    z54.znk (K m) (a m)
  apply z4t K L (2*R) (2*D) (by positivity)
    (fun m => ?_) (fun m => ?_) hrel
    (fun m => z3i.zht (K m) (L m) (hrel m) (hhalf m))
    (fun m => z3i.z9d (L m) (hhalf m))
  · have he:=Module.finrank_mul_finrank ℚ (K m) (L m)
    rw [hrel m] at he
    have hd:=hdegree m
    constructor
    · omega
    · nlinarith
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      z54.z8q (K m) (a m) R (hdisc m)
end OMA1207
namespace z87
open NumberField
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma zl5 :
    |(discr K:ℝ)|^(Module.finrank K L) ≤ |(discr L:ℝ)|:=by
  have he:=natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hpos:0 < (discr L).natAbs:=Int.natAbs_pos.mpr (discr_ne_zero L)
  have hnorm:1 ≤ Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)):=by
    rw [he] at hpos
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt (Nat.pos_of_mul_pos_right hpos))
  have hh:(discr K).natAbs^(Module.finrank K L) ≤ (discr L).natAbs:=by
    rw [he]
    exact Nat.le_mul_of_pos_left _ hnorm
  have hh':((discr K).natAbs:ℝ)^(Module.finrank K L) ≤ ((discr L).natAbs:ℝ):=by exact_mod_cast hh
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'
lemma zms (R:ℝ) (hR:0 ≤ R)
    (hL:|(discr L:ℝ)| ≤ R^(2*Module.finrank ℚ L)) :
    |(discr K:ℝ)| ≤ R^(2*Module.finrank ℚ K):=by
  have hpow:=(zl5 K L).trans hL
  have hd:=Module.finrank_mul_finrank ℚ K L
  have hp:0 < Module.finrank K L:=Module.finrank_pos
  have he:R^(2*Module.finrank ℚ L) =
      (R^(2*Module.finrank ℚ K))^(Module.finrank K L):=by
    rw [← pow_mul,← hd]
    congr 1
    ring
  rw [he] at hpow
  exact le_of_pow_le_pow_left₀ hp.ne' (by positivity) hpow
end z87
namespace zek
open IntermediateField
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
lemma zet (p:ℕ) [Fact p.Prime] (hG:IsPGroup p Gal(L/K))
    (m:ℕ) (hm:p^m ≤ Module.finrank K L) :
    ∃ E:IntermediateField K L, Module.finrank K E = p^m:=by
  obtain ⟨a,ha⟩:=hG.exists_card_eq
  have hdegree:Module.finrank K L = p^a:=(IsGalois.card_aut_eq_finrank K L).symm.trans ha
  have hma:m ≤ a:=(Nat.pow_le_pow_iff_right (Fact.out:p.Prime).one_lt).mp (hm.trans_eq hdegree)
  obtain ⟨H,hH⟩:=Sylow.exists_subgroup_card_pow_prime (G:=Gal(L/K)) p
    (show p^(a-m) ∣ Nat.card Gal(L/K) by rw [ha]; exact pow_dvd_pow p (by omega))
  refine ⟨fixedField H,?_⟩
  have he:=Module.finrank_mul_finrank K (fixedField H) L
  rw [finrank_fixedField_eq_card,hH,hdegree] at he
  have hh:p^a = p^m*p^(a-m):=by rw [← pow_add,Nat.add_sub_of_le hma]
  rw [hh] at he
  exact Nat.mul_right_cancel (show 0 < p^(a-m) from pow_pos (Fact.out:p.Prime).pos _) he
end zek
namespace OMA1207
open NumberField
open scoped Classical
lemma z5e
    (B:Type*) [Field B] [NumberField B] (a:B) (ha:a^2 = 5)
    (L:ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (R:ℕ) (hR:0 < R)
    (hG:∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree:∀ m, 2^m ≤ Module.finrank B (L m))
    (hdisc:∀ m, |(discr (L m):ℝ)| ≤ (R:ℝ)^(2*Module.finrank ℚ (L m))) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  letI:Fact (Nat.Prime 2):=⟨by norm_num⟩
  have he:∀ m, ∃ E:IntermediateField B (L m), Module.finrank B E = 2^m :=
    fun m => zek.zet B (L m) 2 (hG m) m (hdegree m)
  choose E hE using he
  letI (m:ℕ):NumberField (E m):=NumberField.of_module_finite ℚ (E m)
  letI (m:ℕ):IsTotallyReal (E m):=IsTotallyReal.of_algebra (E m) (L m)
  apply z65 (fun m => E m)
    (fun m => algebraMap B (E m) a) (fun m => ?_) R (Module.finrank ℚ B) hR
    (fun m => ?_) (fun m => z87.zms (E m) (L m) (R:ℝ) (by positivity) (hdisc m))
  · rw [← map_pow,ha,map_ofNat]
  · have hd:=Module.finrank_mul_finrank ℚ B (E m)
    rw [hE m] at hd
    have hpos:0 < Module.finrank ℚ B:=Module.finrank_pos
    constructor
    · rw [← hd]
      exact Nat.le_mul_of_pos_left _ hpos
    · exact hd.ge
end OMA1207
namespace OMA1207
open NumberField
open scoped Classical
lemma z4s
    (B:Type*) [Field B] [NumberField B] (a:B) (ha:a^2 = 5)
    (L:ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (hG:∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree:∀ m, 2^m ≤ Module.finrank B (L m))
    (hunram:∀ m, differentIdeal (𝓞 B) (𝓞 (L m)) = ⊤) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  let R:=(discr B).natAbs
  have hR:0 < R:=Int.natAbs_pos.mpr (discr_ne_zero B)
  apply z5e B a ha L R hR hG hdegree
  intro m
  have he:=natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow B (𝓞 B) (L m) (𝓞 (L m))
  rw [hunram m,Ideal.absNorm_top,one_mul] at he
  have hexp:Module.finrank B (L m) ≤ 2*Module.finrank ℚ (L m):=by
    have hd:=Module.finrank_mul_finrank ℚ B (L m)
    have hp:0 < Module.finrank ℚ B:=Module.finrank_pos
    have hh:=Nat.le_mul_of_pos_left (Module.finrank B (L m)) hp
    omega
  have hb:(discr (L m)).natAbs ≤ R^(2*Module.finrank ℚ (L m)):=by
    rw [he]
    exact Nat.pow_le_pow_right hR hexp
  have hb':((discr (L m)).natAbs:ℝ) ≤ (R:ℝ)^(2*Module.finrank ℚ (L m)):=by exact_mod_cast hb
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hb'
end OMA1207
namespace z3u
open scoped Classical
variable (A:Type*) [AddCommGroup A] (n:ℕ)
def mulN:A →ₗ[ℤ] A:=LinearMap.lsmul ℤ A (n:ℤ)
lemma zna (a:A):mulN A n a = (n:ℤ) • a:=rfl
noncomputable def congr {B:Type*} [AddCommGroup B] (e:A ≃ₗ[ℤ] B) :
    ModN A n ≃ₗ[ℤ] ModN B n :=
  Submodule.Quotient.equiv _ _ e (by
    ext b
    constructor
    · rintro ⟨a,⟨x,rfl⟩,rfl⟩
      exact ⟨e x, (e.map_smul (n:ℤ) x).symm⟩
    · rintro ⟨b,rfl⟩
      refine ⟨(n:ℤ) • e.symm b,⟨e.symm b,rfl⟩,?_⟩
      simp)
noncomputable def znq {B:Type*} [AddCommGroup B] (e:A ≃ₗ[ℤ] B) :
    (mulN A n).ker ≃ (mulN B n).ker :=
  e.toEquiv.subtypeEquiv (fun a => by
    change ((n:ℤ) • a = 0) ↔ ((n:ℤ) • e a = 0)
    rw [← e.map_smul, ← e.map_zero]
    exact e.injective.eq_iff.symm)
noncomputable def prod (B:Type*) [AddCommGroup B] :
    ModN (A × B) n ≃ₗ[ℤ] ModN A n × ModN B n:=by
  let f:A × B →ₗ[ℤ] ModN A n × ModN B n :=
    (mulN A n).range.mkQ.prodMap (mulN B n).range.mkQ
  have hf:Function.Surjective f:=by
    rintro ⟨x,y⟩
    obtain ⟨a,rfl⟩:=(mulN A n).range.mkQ_surjective x
    obtain ⟨b,rfl⟩:=(mulN B n).range.mkQ_surjective y
    exact ⟨(a,b),rfl⟩
  have hk:(mulN (A × B) n).range = f.ker:=by
    ext x
    change (∃ y, (n:ℤ) • y = x) ↔ f x = 0
    change (∃ y, (n:ℤ) • y = x) ↔
      ((Submodule.Quotient.mk x.1:ModN A n),
        (Submodule.Quotient.mk x.2:ModN B n)) = (0,0)
    rw [Prod.mk.injEq,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
      exact ⟨(a,b),Prod.ext ha hb⟩
  exact (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hf)
noncomputable def znx (B:Type*) [AddCommGroup B] :
    (mulN (A × B) n).ker ≃ (mulN A n).ker × (mulN B n).ker :=
  (Equiv.refl (A × B) |>.subtypeEquiv (fun x => by
    change ((n:ℤ) • x = 0) ↔ ((n:ℤ) • x.1 = 0 ∧ (n:ℤ) • x.2 = 0)
    exact Prod.ext_iff)).trans Equiv.subtypeProdEquivProd
lemma z82 [Finite A] :
    Nat.card (ModN A n) = Nat.card (mulN A n).ker:=by
  have h₁:=(mulN A n).range.card_eq_card_quotient_mul_card
  have h₂:=(mulN A n).ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr (mulN A n).quotKerEquivRange.toEquiv,mul_comm] at h₂
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h₁.symm.trans h₂)
variable [Module.Finite ℤ A]
noncomputable def zfl :
    A ≃ₗ[ℤ] (Submodule.torsion ℤ A) × (A ⧸ Submodule.torsion ℤ A):=by
  let hf:=Module.projective_lifting_property
    (Submodule.torsion ℤ A).mkQ LinearMap.id (Submodule.torsion ℤ A).mkQ_surjective
  let f:=Classical.choose hf
  have hf:(Submodule.torsion ℤ A).mkQ.comp f = LinearMap.id:=Classical.choose_spec hf
  exact (lequivProdOfRightSplitExact (Submodule.torsion ℤ A).injective_subtype
    (by rw [Submodule.range_subtype,Submodule.ker_mkQ]) hf).symm
lemma zf7 [NeZero n] :
    Nat.card (ModN A n) = n ^ Module.finrank ℤ A * Nat.card (mulN A n).ker:=by
  let T:=Submodule.torsion ℤ A
  let F:=A ⧸ T
  letI:Finite T:=Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  have hr:Module.finrank ℤ F = Module.finrank ℤ A:=by
    apply Nat.cast_injective (R:=Cardinal)
    rw [Module.finrank_eq_rank,Module.finrank_eq_rank]
    exact rank_quotient_eq_of_le_torsion le_rfl
  have hk:(mulN F n).ker = ⊥:=by
    ext x
    simp only [LinearMap.mem_ker,zna,Submodule.mem_bot]
    exact smul_eq_zero_iff_right (by exact_mod_cast NeZero.ne n)
  have hkc:Nat.card (mulN F n).ker = 1:=by
    rw [hk]
    exact Nat.card_unique
  have hc:Nat.card (ModN A n) = Nat.card (ModN T n) * Nat.card (ModN F n):=by
    rw [Nat.card_congr (congr A n (zfl A)).toEquiv,
      Nat.card_congr (prod T n F).toEquiv,Nat.card_prod]
  have htk:Nat.card (mulN A n).ker = Nat.card (mulN T n).ker:=by
    rw [Nat.card_congr (znq A n (zfl A)),
      Nat.card_congr (znx T n F),Nat.card_prod,hkc,mul_one]
  rw [hc,z82,ModN.natCard_eq,hr,htk,mul_comm]
lemma zly [NeZero n]:Finite (ModN A n):=by
  have:Finite (mulN A n).ker:=Module.finite_of_fg_torsion _ (by
    intro x
    refine ⟨⟨(n:ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast NeZero.ne n)⟩,?_⟩
    apply Subtype.ext
    exact x.property)
  exact Nat.finite_of_card_ne_zero (by
    rw [zf7]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne n)) (Nat.ne_of_gt Nat.card_pos))
end z3u
namespace z9
open scoped Classical
variable {A:Type*} [AddCommGroup A]
variable (σ:A →ₗ[ℤ] A) (hσ:σ.comp σ = LinearMap.id)
def plus:Submodule ℤ A:=(σ-LinearMap.id).ker
def minus:Submodule ℤ A:=(σ+LinearMap.id).ker
@[simp] lemma z1g (x:A):x ∈ plus σ ↔ σ x = x:=by
  simp [plus,sub_eq_zero]
@[simp] lemma zfx (x:A):x ∈ minus σ ↔ σ x+x = 0:=by
  simp [minus]
include hσ in
lemma involutive (x:A):σ (σ x) = x:=LinearMap.congr_fun hσ x
def norm:A →ₗ[ℤ] plus σ:=(σ+LinearMap.id).codRestrict (plus σ) (fun x => by
  rw [z1g]
  change σ (σ x+x) = σ x+x
  rw [map_add,involutive σ hσ]
  abel)
def double (V:Type*) [AddCommGroup V]:V →ₗ[ℤ] V:=LinearMap.lsmul ℤ V 2
@[simp] lemma zb5 (V:Type*) [AddCommGroup V] (x:V) :
    double V x = x+x:=by simp [double,two_smul]
def zgd:A →ₗ[ℤ] ModN (plus σ) 2 :=
  (LinearMap.range (double (plus σ))).mkQ.comp (norm σ hσ)
lemma zmb:(zgd σ hσ).ker = plus σ ⊔ minus σ:=by
  ext x
  change (zgd σ hσ x = 0) ↔ _
  change (Submodule.Quotient.mk (norm σ hσ x):(plus σ) ⧸ (double (plus σ)).range) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    have he:σ x+x = (y:A)+(y:A):=by
      have hh:=congrArg (fun y:plus σ => (y:A)) hy
      change ((double (plus σ) y:plus σ):A) = σ x + x at hh
      simpa only [zb5,Submodule.coe_add] using hh.symm
    refine Submodule.mem_sup.mpr ⟨y,y.property,x-y,?_,by abel⟩
    rw [zfx]
    have hyσ:σ (y:A) = y:=(z1g σ _).mp y.property
    calc
      σ (x-y)+(x-y) = (σ x+x)-(σ (y:A)+y):=by rw [map_sub]; abel
      _ = 0:=by rw [he,hyσ,sub_self]
  · intro hx
    obtain ⟨y,hy,z,hz,rfl⟩:=Submodule.mem_sup.mp hx
    refine ⟨⟨y,hy⟩,?_⟩
    apply Subtype.ext
    change ((double (plus σ)) ⟨y,hy⟩:A) = σ (y+z)+(y+z)
    rw [zb5,Submodule.coe_add,map_add]
    have hyσ:=(z1g σ y).mp hy
    have hzσ:=(zfx σ z).mp hz
    rw [hyσ]
    calc
      y+y = y+y+(σ z+z):=by rw [hzσ,add_zero]
      _ = y+σ z+(y+z):=by abel
lemma z57:(double (plus σ)).range ≤ (norm σ hσ).range:=by
  rintro x ⟨y,rfl⟩
  refine ⟨y,?_⟩
  apply Subtype.ext
  change σ (y:A)+(y:A) = ((double (plus σ)) y:A)
  rw [zb5,Submodule.coe_add,(z1g σ _).mp y.property]
noncomputable def zc4 :
    (A ⧸ (plus σ ⊔ minus σ)) ≃ₗ[ℤ]
      ((norm σ hσ).range.map (LinearMap.range (double (plus σ))).mkQ):=by
  have hr:(zgd σ hσ).range =
      (norm σ hσ).range.map (LinearMap.range (double (plus σ))).mkQ:=by
    exact LinearMap.range_comp (norm σ hσ) (LinearMap.range (double (plus σ))).mkQ
  exact (Submodule.quotEquivOfEq _ _ (zmb σ hσ).symm).trans
    ((zgd σ hσ).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))
lemma z8y :
    Nat.card (A ⧸ (plus σ ⊔ minus σ)) *
      Nat.card ((plus σ) ⧸ (norm σ hσ).range) = Nat.card (ModN (plus σ) 2):=by
  rw [Nat.card_congr (zc4 σ hσ).toEquiv]
  exact Submodule.card_quotient_mul_card_quotient (norm σ hσ).range
    (double (plus σ)).range (z57 σ hσ)
include hσ in
lemma z1t:(-σ).comp (-σ) = LinearMap.id:=by
  ext x
  simp only [LinearMap.comp_apply,LinearMap.neg_apply,map_neg,neg_neg,LinearMap.id_apply]
  exact involutive σ hσ x
@[simp] lemma zhu:plus (-σ) = minus σ:=by
  ext x
  rw [z1g,zfx,LinearMap.neg_apply]
  constructor
  · intro h
    calc
      σ x+x = σ x+(-σ x):=congrArg (σ x+·) h.symm
      _ = 0:=add_neg_cancel (σ x)
  · intro h
    apply neg_injective
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_left h
@[simp] lemma zne:minus (-σ) = plus σ:=by
  have h:=zhu (-σ)
  simpa only [neg_neg] using h.symm
end z9
namespace z9
open scoped Classical
open z3u
variable {A:Type*} [AddCommGroup A]
variable (σ:A →ₗ[ℤ] A) (hσ:σ.comp σ = LinearMap.id)
private lemma zas (x:A) (hfix:σ x = x) (hx:x+x=0) :
    -σ x = x:=by
  rw [hfix]
  exact (eq_neg_of_add_eq_zero_left hx).symm
noncomputable def zih :
    (mulN (plus σ) 2).ker ≃ (mulN (plus (-σ)) 2).ker where
  toFun x:=⟨⟨x.1.1, by
    rw [z1g,LinearMap.neg_apply]
    apply zas σ _ ((z1g σ _).mp x.1.2)
    have h:=congrArg Subtype.val x.2
    change (2:ℤ) • x.1.1 = 0 at h
    simpa only [two_zsmul] using h⟩,by
      apply Subtype.ext
      have h:=congrArg Subtype.val x.2
      exact h⟩
  invFun x:=⟨⟨x.1.1,by
    rw [z1g]
    have h:=congrArg Subtype.val x.2
    change (2:ℤ) • x.1.1 = 0 at h
    have hx:=zas (-σ) _ ((z1g (-σ) _).mp x.1.2)
      (by simpa only [two_zsmul] using h)
    simpa only [LinearMap.neg_apply,neg_neg] using hx⟩,by
      apply Subtype.ext
      have h:=congrArg Subtype.val x.2
      exact h⟩
  left_inv _:=rfl
  right_inv _:=rfl
variable [Module.Finite ℤ A]
lemma z7h:Finite ((plus σ) ⧸ (norm σ hσ).range):=by
  letI:Finite ((plus σ) ⧸ (double (plus σ)).range):=zly (plus σ) 2
  exact Finite.of_surjective (Submodule.factor (z57 σ hσ))
    (Submodule.factor_surjective (z57 σ hσ))
lemma zdv :
    Nat.card ((plus σ) ⧸ (norm σ hσ).range) * 2^Module.finrank ℤ (minus σ) =
      Nat.card ((plus (-σ)) ⧸ (norm (-σ) (z1t σ hσ)).range) *
        2^Module.finrank ℤ (plus σ):=by
  have hplus:=z8y σ hσ
  have hminus:=z8y (-σ) (z1t σ hσ)
  have hc :
      Nat.card ((plus σ) ⧸ (norm σ hσ).range) * Nat.card (ModN (plus (-σ)) 2) =
        Nat.card ((plus (-σ)) ⧸ (norm (-σ) (z1t σ hσ)).range) *
          Nat.card (ModN (plus σ) 2):=by
    rw [← hminus,← hplus]
    simp only [zhu,zne,sup_comm (minus σ)]
    ring
  rw [zf7,zf7] at hc
  have he:Nat.card (mulN (plus (-σ)) 2).ker = Nat.card (mulN (plus σ) 2).ker :=
    (Nat.card_congr (zih σ)).symm
  rw [he,← mul_assoc,← mul_assoc] at hc
  have ht:Finite (mulN (plus σ) 2).ker:=Module.finite_of_fg_torsion _ (by
    intro x
    refine ⟨⟨2,by simp⟩,?_⟩
    apply Subtype.ext
    exact x.property)
  have h:=Nat.eq_of_mul_eq_mul_right Nat.card_pos hc
  have hr:Module.finrank ℤ (plus (-σ)) = Module.finrank ℤ (minus σ) :=
    (LinearEquiv.ofEq _ _ (zhu σ)).finrank_eq
  rwa [hr] at h
include hσ in
lemma zez :
    Module.finrank ℤ (plus σ) + Module.finrank ℤ (minus σ) = Module.finrank ℤ A:=by
  have hk:(norm σ hσ).ker = minus σ:=by
    ext x
    change (norm σ hσ x = 0) ↔ σ x+x = 0
    exact Subtype.ext_iff
  have h₁:=(norm σ hσ).ker.finrank_quotient_add_finrank
  rw [(norm σ hσ).quotKerEquivRange.finrank_eq,hk] at h₁
  have h₂:=(norm σ hσ).range.finrank_quotient_add_finrank
  letI:=z7h σ hσ
  have hz:Module.finrank ℤ ((plus σ) ⧸ (norm σ hσ).range) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  rw [hz,zero_add] at h₂
  rwa [h₂] at h₁
end z9
namespace z17
open z9
open scoped Classical
variable {U A B:Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
structure Sequence (U A B:Type*) [AddCommGroup U] [AddCommGroup A] [AddCommGroup B] where
  i:U →ₗ[ℤ] A
  p:A →ₗ[ℤ] B
  hi:Function.Injective i
  hp:Function.Surjective p
  exact:i.range = p.ker
  u:U →ₗ[ℤ] U
  a:A →ₗ[ℤ] A
  b:B →ₗ[ℤ] B
  hu:u.comp u = LinearMap.id
  ha:a.comp a = LinearMap.id
  hb:b.comp b = LinearMap.id
  iu:∀ x, i (u x) = a (i x)
  pa:∀ x, p (a x) = b (p x)
variable (S:Sequence U A B)
@[simp] lemma p_i (u:U):S.p (S.i u) = 0:=by
  have h:S.i u ∈ S.p.ker:=S.exact ▸ LinearMap.mem_range_self S.i u
  exact h
noncomputable def factor {C D F:Type*} [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (p:C →ₗ[ℤ] D) (hp:Function.Surjective p) (f:C →ₗ[ℤ] F) (h:p.ker ≤ f.ker) :
    D →ₗ[ℤ] F :=
  (p.ker.liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
@[simp] lemma z7i {C D F:Type*} [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (p:C →ₗ[ℤ] D) (hp:Function.Surjective p) (f:C →ₗ[ℤ] F) (h:p.ker ≤ f.ker) (x:C) :
    factor p hp f h (p x) = f x:=by
  change p.ker.liftQ f h ((p.quotKerEquivOfSurjective hp).symm (p x)) = _
  rw [← p.quotKerEquivOfSurjective_apply_mk hp x,LinearEquiv.symm_apply_apply]
  rfl
def z3e:Submodule ℤ A:=(plus S.b).comap S.p
def zdb:z3e S →ₗ[ℤ] plus S.b :=
  (S.p.domRestrict (z3e S)).codRestrict _ (fun x => x.property)
lemma z6g:Function.Surjective (zdb S):=by
  intro y
  obtain ⟨x,hx⟩:=S.hp y.1
  refine ⟨⟨x,?_⟩,Subtype.ext hx⟩
  change S.p x ∈ plus S.b
  rw [hx]
  exact y.property
def z2m:plus S.a →ₗ[ℤ] plus S.b :=
  (S.p.domRestrict (plus S.a)).codRestrict _ (fun x => by
    rw [z1g]
    change S.b (S.p x.1) = S.p x.1
    rw [← S.pa,(z1g S.a _).mp x.property])
private def z9v:z3e S →ₗ[ℤ] A :=
  (LinearMap.id-S.a).domRestrict (z3e S)
private lemma za9 (x:z3e S):z9v S x ∈ S.i.range:=by
  rw [S.exact]
  change S.p (x.1-S.a x.1) = 0
  rw [map_sub,S.pa,(z1g S.b _).mp x.property,sub_self]
noncomputable def z2y:z3e S →ₗ[ℤ] U :=
  (LinearEquiv.ofInjective S.i S.hi).symm.toLinearMap.comp
    ((z9v S).codRestrict S.i.range (za9 S))
@[simp] lemma z3l (x:z3e S) :
    S.i (z2y S x) = x.1-S.a x.1:=by
  change ((LinearEquiv.ofInjective S.i S.hi)
    ((LinearEquiv.ofInjective S.i S.hi).symm ⟨z9v S x,za9 S x⟩)).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl
private lemma zd3 (x:z3e S):z2y S x ∈ plus (-S.u):=by
  rw [z1g,LinearMap.neg_apply]
  apply S.hi
  rw [map_neg,S.iu,z3l,map_sub,involutive S.a S.ha]
  abel
noncomputable def zfc:z3e S →ₗ[ℤ] plus (-S.u) :=
  (z2y S).codRestrict _ (zd3 S)
abbrev H1:=plus (-S.u) ⧸ (norm (-S.u) (z1t S.u S.hu)).range
noncomputable def zid:z3e S →ₗ[ℤ] H1 S :=
  (norm (-S.u) (z1t S.u S.hu)).range.mkQ.comp (zfc S)
private lemma zkx:(zdb S).ker ≤ (zid S).ker:=by
  intro x hx
  have hpx:S.p x.1 = 0:=congrArg Subtype.val hx
  obtain ⟨u,hu⟩:=S.exact.symm ▸ (show x.1 ∈ S.p.ker from hpx)
  change Submodule.Quotient.mk (zfc S x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply S.hi
  change S.i (-S.u u+u) = S.i (z2y S x)
  rw [z3l]
  rw [map_add,map_neg,S.iu,hu]
  abel
noncomputable def connecting:plus S.b →ₗ[ℤ] H1 S :=
  factor (zdb S) (z6g S) (zid S) (zkx S)
@[simp] lemma z7u (x:z3e S) :
    connecting S (zdb S x) = Submodule.Quotient.mk (zfc S x) :=
  z7i _ _ _ _ x
lemma z8d:(connecting S).ker = (z2m S).range:=by
  ext y
  obtain ⟨x,rfl⟩:=z6g S y
  change connecting S (zdb S x) = 0 ↔ _
  rw [z7u,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u,hu⟩
    have hdu:S.i u-S.a (S.i u) = x.1-S.a x.1:=by
      have h:=congrArg (fun z:plus (-S.u) => S.i z.1) hu
      change S.i (-S.u u+u) = S.i (z2y S x) at h
      rw [map_add,map_neg,S.iu,z3l] at h
      convert h using 1 <;> abel
    have hz:x.1-S.i u ∈ plus S.a:=by
      rw [z1g,map_sub]
      calc
        S.a x.1-S.a (S.i u) = S.a x.1+(S.i u-S.a (S.i u))-S.i u:=by abel
        _ = S.a x.1+(x.1-S.a x.1)-S.i u:=by rw [hdu]
        _ = x.1-S.i u:=by abel
    refine ⟨⟨x.1-S.i u,hz⟩,Subtype.ext ?_⟩
    change S.p (x.1-S.i u) = S.p x.1
    rw [map_sub,p_i,sub_zero]
  · rintro ⟨z,hz⟩
    have hpz:S.p z.1 = S.p x.1:=congrArg Subtype.val hz
    have hxz:x.1-z.1 ∈ S.p.ker:=by rw [LinearMap.mem_ker,map_sub,hpz,sub_self]
    obtain ⟨u,hu⟩:=S.exact.symm ▸ hxz
    refine ⟨u,?_⟩
    apply Subtype.ext
    apply S.hi
    change S.i (-S.u u+u) = S.i (z2y S x)
    rw [z3l]
    rw [map_add,map_neg,S.iu,hu,map_sub,(z1g S.a _).mp z.property]
    abel
lemma z35
    (h90:∀ z:A, -S.a z = z → ∃ x, x-S.a x = z) :
    Function.Surjective (connecting S):=by
  intro c
  obtain ⟨u,rfl⟩:=(norm (-S.u) (z1t S.u S.hu)).range.mkQ_surjective c
  have hu:-S.a (S.i u.1) = S.i u.1:=by
    have hf:=(z1g (-S.u) _).mp u.property
    change -S.u u.1 = u.1 at hf
    rw [← S.iu,← map_neg,hf]
  obtain ⟨x,hx⟩:=h90 (S.i u.1) hu
  have hpx:x ∈ z3e S:=by
    change S.p x ∈ plus S.b
    rw [z1g]
    have h:=congrArg S.p hx
    rw [map_sub,S.pa,p_i] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨zdb S ⟨x,hpx⟩,?_⟩
  rw [z7u]
  congr 1
  apply Subtype.ext
  apply S.hi
  exact (z3l S ⟨x,hpx⟩).trans hx
end z17
namespace z17
open z9
open scoped Classical
variable {U A B:Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S:Sequence U A B)
def Sequence.neg:Sequence U A B where
  i:=S.i
  p:=S.p
  hi:=S.hi
  hp:=S.hp
  exact:=S.exact
  u:=-S.u
  a:=-S.a
  b:=-S.b
  hu:=z1t S.u S.hu
  ha:=z1t S.a S.ha
  hb:=z1t S.b S.hb
  iu x:=by change S.i (-S.u x) = -S.a (S.i x); rw [map_neg,S.iu]
  pa x:=by change S.p (-S.a x) = -S.b (S.p x); rw [map_neg,S.pa]
variable (h90:∀ z:A, -S.a z = z → ∃ x, x-S.a x = z)
include h90 in
lemma z6c :
    (connecting S.neg).ker = (norm (-S.b) (z1t S.b S.hb)).range:=by
  rw [z8d]
  ext y
  constructor
  · rintro ⟨a,ha⟩
    have ha':-S.a a.1 = a.1:=(z1g (-S.a) _).mp a.property
    obtain ⟨x,hx⟩:=h90 a.1 ha'
    refine ⟨S.p x,Subtype.ext ?_⟩
    have h:=congrArg Subtype.val ha
    change S.p a.1 = y.1 at h
    change -S.b (S.p x)+S.p x = y.1
    rw [← h,← hx,map_sub,S.pa]
    abel
  · rintro ⟨b,rfl⟩
    obtain ⟨a,ha⟩:=S.hp b
    have hm:a-S.a a ∈ plus S.neg.a:=by
      rw [z1g]
      change -S.a (a-S.a a) = a-S.a a
      rw [map_sub,involutive S.a S.ha]
      abel
    refine ⟨⟨a-S.a a,hm⟩,Subtype.ext ?_⟩
    change S.p (a-S.a a) = -S.b b+b
    rw [map_sub,S.pa,ha]
    abel
abbrev z7l:=plus (-S.b) ⧸ (norm (-S.b) (z1t S.b S.hb)).range
noncomputable def z6m:z7l S →ₗ[ℤ] H1 S.neg :=
  (norm (-S.b) (z1t S.b S.hb)).range.liftQ (connecting S.neg)
    (le_of_eq (z6c S h90).symm)
lemma z2p:Function.Injective (z6m S h90):=by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (z6c S h90).symm
include h90 in
lemma zga [Finite (H1 S.neg)] :
    Nat.card (z7l S) ≤ Nat.card (H1 S.neg) :=
  Nat.card_le_card_of_injective _ (z2p S h90)
end z17
namespace z17
open z9
open scoped Classical
variable {U A B:Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S:Sequence U A B)
def z8e:plus S.u →ₗ[ℤ] plus S.a :=
  (S.i.domRestrict (plus S.u)).codRestrict _ (fun x => by
    rw [z1g]
    change S.a (S.i x.1) = S.i x.1
    rw [← S.iu,(z1g S.u _).mp x.property])
lemma zfw:Function.Injective (z8e S):=by
  intro x y h
  exact Subtype.ext (S.hi (congrArg Subtype.val h))
lemma zlo:(z2m S).ker = (z8e S).range:=by
  ext x
  constructor
  · intro hx
    have hpx:S.p x.1 = 0:=congrArg Subtype.val hx
    obtain ⟨u,hu⟩:=S.exact.symm ▸ (show x.1 ∈ S.p.ker from hpx)
    have huf:u ∈ plus S.u:=by
      rw [z1g]
      apply S.hi
      rw [S.iu,hu,(z1g S.a _).mp x.property]
    exact ⟨⟨u,huf⟩,Subtype.ext hu⟩
  · rintro ⟨u,rfl⟩
    apply Subtype.ext
    exact p_i S u.1
lemma zgp (j:A →ₗ[ℤ] B) (hj:Function.Injective j) (V:Submodule ℤ A) :
    Nat.card (B ⧸ V.map j) = Nat.card (A ⧸ V) * Nat.card (B ⧸ j.range):=by
  let f:=(V.map j).mkQ.comp j
  have hk:f.ker = V:=by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ,Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr hj,sup_bot_eq]
  have hr:f.range = j.range.map (V.map j).mkQ:=LinearMap.range_comp _ _
  have he:(A ⧸ V) ≃ₗ[ℤ] (j.range.map (V.map j).mkQ) :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))
  rw [Nat.card_congr he.toEquiv]
  exact (Submodule.card_quotient_mul_card_quotient j.range (V.map j) (by rintro _ ⟨a,ha,rfl⟩; exact ⟨a,rfl⟩)).symm
end z17
namespace z17
open z9
open scoped Classical
variable {U A B:Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S:Sequence U A B)
lemma z6i (hc:Function.Surjective (connecting S.neg))
    (u:plus S.u):∃ x:A, x+S.a x = S.i u.1:=by
  let u':plus (-S.neg.u):=⟨u.1,by
    rw [z1g]
    change -(-S.u u.1) = u.1
    simpa only [neg_neg] using (z1g S.u _).mp u.property⟩
  obtain ⟨b,hb⟩:=hc (Submodule.Quotient.mk u')
  obtain ⟨x,rfl⟩:=z6g S.neg b
  rw [z7u] at hb
  obtain ⟨v,hv⟩:=(Submodule.Quotient.eq _).mp hb
  have h:=congrArg (fun z:plus (-S.neg.u) => S.i z.1) hv
  change S.i (-(-S.u v)+v) = S.i (z2y S.neg x-u.1) at h
  rw [neg_neg,map_add,map_sub,S.iu] at h
  have hd:=z3l S.neg x
  change S.i (z2y S.neg x) = x.1-(-S.a x.1) at hd
  rw [hd,sub_neg_eq_add] at h
  refine ⟨x.1-S.i v,?_⟩
  rw [map_sub]
  calc
    _ = (x.1+S.a x.1)-(S.a (S.i v)+S.i v):=by abel
    _ = S.i u.1:=by rw [h]; abel
end z17
namespace z13
open NumberField
open scoped Classical
variable (K:Type*) [Field K] [NumberField K]
abbrev z44:=Additive (𝓞 K)ˣ
lemma zi9:Module.finrank ℤ (z44 K) = NumberField.Units.rank K:=by
  letI:=AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
  let q:z44 K →ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    AddMonoidHom.toIntLinearMap (M:=z44 K)
      (M₂:=Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
      (MonoidHom.toAdditive (QuotientGroup.mk' (NumberField.Units.torsion K)))
  have hq:Function.Surjective q:=by
    intro x
    obtain ⟨u,hu⟩:=QuotientGroup.mk'_surjective (NumberField.Units.torsion K) x.toMul
    exact ⟨Additive.ofMul u,congrArg Additive.ofMul hu⟩
  have hk:Finite q.ker:=by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    exact inferInstanceAs (Finite (NumberField.Units.torsion K))
  have hr:=q.ker.finrank_quotient_add_finrank
  rw [(q.quotKerEquivOfSurjective hq).finrank_eq,NumberField.Units.rank_modTorsion] at hr
  have hz:Module.finrank ℤ q.ker = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  exact (by simpa only [hz,add_zero] using hr.symm)
variable (E:Type*) [Field E] [NumberField E] [Algebra K E]
noncomputable def extend:(𝓞 K)ˣ →* (𝓞 E)ˣ :=
  Units.map (algebraMap (𝓞 K) (𝓞 E))
lemma extend_injective:Function.Injective (extend K E):=by
  intro u v h
  exact NumberField.Units.coe_injective K ((algebraMap K E).injective
    (congrArg (fun u:(𝓞 E)ˣ => (u:E)) h))
lemma zk8 (u:(𝓞 E)ˣ) (hu:(u:E) ∈ Set.range (algebraMap K E)) :
    ∃ v:(𝓞 K)ˣ, extend K E v = u:=by
  obtain ⟨x,hx⟩:=hu
  have hxi:IsIntegral ℤ x:=(isIntegral_algebraMap_iff (R:=ℤ)
    (algebraMap K E).injective).mp (hx ▸ (u:𝓞 E).property)
  have hx0:x ≠ 0:=by
    intro h
    have h0:=NumberField.Units.coe_ne_zero u
    exact h0 (hx.symm.trans (by simp [h]))
  have huinv:((u⁻¹:(𝓞 E)ˣ):E) = (u:E)⁻¹:=by
    simpa using NumberField.Units.coe_zpow u (-1)
  have hxinv:algebraMap K E x⁻¹ = ((u⁻¹:(𝓞 E)ˣ):E):=by
    rw [map_inv₀,hx,huinv]
  have hxii:IsIntegral ℤ x⁻¹:=(isIntegral_algebraMap_iff (R:=ℤ)
    (algebraMap K E).injective).mp (hxinv ▸ ((u⁻¹:(𝓞 E)ˣ):𝓞 E).property)
  let v:(𝓞 K)ˣ:=Units.mkOfMulEqOne ⟨x,hxi⟩ ⟨x⁻¹,hxii⟩ (by
    apply RingOfIntegers.coe_injective
    exact mul_inv_cancel₀ hx0)
  refine ⟨v,NumberField.Units.coe_injective E ?_⟩
  exact hx
variable (σ:E ≃ₐ[K] E)
noncomputable def action:z44 E →ₗ[ℤ] z44 E :=
  (MonoidHom.toAdditive (Units.map (RingOfIntegers.mapRingHom σ.toRingHom))).toIntLinearMap
@[simp] lemma z9m (u:(𝓞 K)ˣ) :
    action K E σ (Additive.ofMul (extend K E u)) = Additive.ofMul (extend K E u):=by
  apply Additive.toMul.injective
  apply NumberField.Units.coe_injective E
  exact σ.commutes (u:K)
variable [FiniteDimensional K E] [IsGalois K E]
variable (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
include hdeg hne in
lemma z4h (τ:E ≃ₐ[K] E):τ = 1 ∨ τ = σ:=by
  obtain ⟨z,hz,huniq⟩:=(Nat.card_eq_two_iff' (1:E ≃ₐ[K] E)).mp
    ((IsGalois.card_aut_eq_finrank K E).trans hdeg)
  by_cases hτ:τ = 1
  · exact Or.inl hτ
  · exact Or.inr ((huniq τ hτ).trans (huniq σ hne).symm)
include hdeg in
lemma z40 :
    (action K E σ).comp (action K E σ) = LinearMap.id:=by
  have hp:σ^2 = 1:=by
    rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
    exact pow_card_eq_one'
  apply LinearMap.ext
  intro u
  change action K E σ (action K E σ u) = u
  apply Additive.toMul.injective
  apply NumberField.Units.coe_injective E
  change σ (σ (u.toMul:E)) = (u.toMul:E)
  exact congrArg (fun τ:E ≃ₐ[K] E => τ (u.toMul:E)) (by simpa [pow_two] using hp)
include hdeg hne in
noncomputable def zam:z44 K ≃ₗ[ℤ] z9.plus (action K E σ):=by
  let f:z44 K →ₗ[ℤ] z44 E:=(MonoidHom.toAdditive (extend K E)).toIntLinearMap
  let g:=f.codRestrict (z9.plus (action K E σ)) (fun u =>
    (z9.z1g _ _).mpr (z9m K E σ u.toMul))
  apply LinearEquiv.ofBijective g
  constructor
  · intro u v h
    exact extend_injective K E (congrArg (fun x:z9.plus (action K E σ) => x.1.toMul) h)
  · intro u
    have hfix:=(z9.z1g _ _).mp u.2
    have hu:(u.1.toMul:E) ∈ Set.range (algebraMap K E):=by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases z4h K E σ hdeg hne τ with rfl | rfl
      · rfl
      · exact congrArg (fun u:z44 E => (u.toMul:E)) hfix
    obtain ⟨v,hv⟩:=zk8 K E u.1.toMul hu
    exact ⟨Additive.ofMul v,Subtype.ext hv⟩
include hdeg hne in
lemma zij :
    Module.finrank ℤ (z9.plus (action K E σ)) = NumberField.Units.rank K:=by
  rw [← (zam K E σ hdeg hne).finrank_eq,zi9]
include hdeg hne in
lemma zks :
    Module.finrank ℤ (z9.minus (action K E σ)) + NumberField.Units.rank K =
      NumberField.Units.rank E:=by
  have h:=z9.zez (action K E σ) (z40 K E σ hdeg)
  rw [zij K E σ hdeg hne,zi9] at h
  rwa [add_comm] at h
end z13
namespace z13
open NumberField
open scoped Classical
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
abbrev H0:=z9.plus (action K E σ) ⧸
  (z9.norm (action K E σ) (z40 K E σ hdeg)).range
abbrev H1:=z9.plus (-action K E σ) ⧸
  (z9.norm (-action K E σ)
    (z9.z1t (action K E σ) (z40 K E σ hdeg))).range
include hdeg in
lemma zfq [IsTotallyReal K] [IsTotallyReal E] :
    NumberField.Units.rank E = 2*NumberField.Units.rank K+1:=by
  have hK:=IsTotallyReal.finrank K
  have hE:=IsTotallyReal.finrank E
  have hzK:=IsTotallyReal.nrComplexPlaces_eq_zero K
  have hzE:=IsTotallyReal.nrComplexPlaces_eq_zero E
  have hd:=Module.finrank_mul_finrank ℚ K E
  rw [hdeg] at hd
  have hpos:0 < Module.finrank ℚ K:=Module.finrank_pos
  rw [NumberField.Units.rank,NumberField.Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega
include hne in
lemma zla [IsTotallyReal K] [IsTotallyReal E] :
    Nat.card (H1 K E σ hdeg) = 2*Nat.card (H0 K E σ hdeg):=by
  have h:=z9.zdv (action K E σ) (z40 K E σ hdeg)
  have hm:=zks K E σ hdeg hne
  rw [zfq K E hdeg] at hm
  have hmr:Module.finrank ℤ (z9.minus (action K E σ)) =
      NumberField.Units.rank K+1:=by omega
  rw [zij K E σ hdeg hne,hmr,pow_succ] at h
  change Nat.card (H0 K E σ hdeg) * (2^NumberField.Units.rank K*2) =
    Nat.card (H1 K E σ hdeg) * 2^NumberField.Units.rank K at h
  apply (Nat.eq_of_mul_eq_mul_right (by positivity:0 < 2^NumberField.Units.rank K))
  nlinarith [h]
include hdeg hne in
lemma z5j (x:E):algebraMap K E (Algebra.norm K x) = σ x*x:=by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have he:(Finset.univ:Finset (E ≃ₐ[K] E)) = {σ,1}:=by
    ext τ
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact (z4h K E σ hdeg hne τ).symm
  rw [he,Finset.prod_pair hne]
  rfl
end z13
namespace z10
open NumberField
open scoped Classical nonZeroDivisors
variable (E:Type*) [Field E] [NumberField E]
abbrev Ideals:=(FractionalIdeal (𝓞 E)⁰ E)ˣ
variable (σ:E ≃+* E)
noncomputable def actionHom:FractionalIdeal (𝓞 E)⁰ E →+* FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.extendedHom' E
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (RingOfIntegers.mapRingEquiv σ).injective)
private lemma localization_map :
    IsLocalization.map (S:=E) E (RingOfIntegers.mapRingHom σ.toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (RingOfIntegers.mapRingEquiv σ).injective) = σ.toRingHom:=by
  apply IsFractionRing.ringHom_ext (A:=𝓞 E)
  intro a
  exact IsLocalization.map_eq _ a
lemma z29 (I:FractionalIdeal (𝓞 E)⁰ E) (x:E) :
    x ∈ actionHom E σ I ↔ σ.symm x ∈ I:=by
  change x ∈ (I.extended E _) ↔ _
  rw [FractionalIdeal.mem_extended_iff]
  change x ∈ Submodule.span (𝓞 E)
    ((IsLocalization.map (S:=E) E (RingOfIntegers.mapRingHom σ.toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (RingOfIntegers.mapRingEquiv σ).injective)) '' (I:Set E)) ↔ _
  rw [localization_map E σ]
  constructor
  · intro hx
    refine Submodule.span_induction (p:=fun x _ => σ.symm x ∈ I) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a,ha,rfl⟩
      change σ.symm (σ a) ∈ I
      rw [RingEquiv.symm_apply_apply]
      exact ha
    · simp only [map_zero]
      exact I.coeToSubmodule.zero_mem
    · intro a b ha hb h₁ h₂
      simp only [map_add]
      exact I.coeToSubmodule.add_mem h₁ h₂
    · intro a b hb h
      change σ.symm ((a:E)*b) ∈ I
      rw [map_mul]
      exact I.coeToSubmodule.smul_mem (RingOfIntegers.mapRingEquiv σ.symm a) h
  · intro hx
    exact Submodule.subset_span ⟨σ.symm x,hx,σ.apply_symm_apply x⟩
@[simp] lemma z67 (I:FractionalIdeal (𝓞 E)⁰ E) :
    actionHom E σ.symm (actionHom E σ I) = I:=by
  ext x
  rw [z29,z29]
  simp
noncomputable def zmh:FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E :=
  RingEquiv.ofRingHom (actionHom E σ) (actionHom E σ.symm)
    (RingHom.ext (fun I => by simpa using z67 E σ.symm I))
    (RingHom.ext (z67 E σ))
noncomputable def action:Ideals E ≃* Ideals E:=Units.mapEquiv (zmh E σ).toMulEquiv
lemma zjq (x:E) :
    actionHom E σ (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (σ x):=by
  ext y
  rw [z29,FractionalIdeal.mem_spanSingleton,FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨RingOfIntegers.mapRingEquiv σ a,?_⟩
    have h:=congrArg σ ha
    rw [Algebra.smul_def,map_mul,RingEquiv.apply_symm_apply] at h
    rw [Algebra.smul_def]
    exact h
  · rintro ⟨a,ha⟩
    refine ⟨RingOfIntegers.mapRingEquiv σ.symm a,?_⟩
    have h:=congrArg σ.symm ha
    rw [Algebra.smul_def,map_mul,RingEquiv.symm_apply_apply] at h
    rw [Algebra.smul_def]
    exact h
noncomputable def z15:Eˣ ≃* Eˣ:=Units.mapEquiv σ.toMulEquiv
@[simp] lemma z4f (x:Eˣ) :
    action E σ (toPrincipalIdeal (𝓞 E) E x) = toPrincipalIdeal (𝓞 E) E (z15 E σ x):=by
  apply Units.ext
  change actionHom E σ (toPrincipalIdeal (𝓞 E) E x:FractionalIdeal (𝓞 E)⁰ E) = _
  rw [coe_toPrincipalIdeal,coe_toPrincipalIdeal]
  exact zjq E σ x
noncomputable def z5w:(𝓞 E)ˣ →* Eˣ:=Units.map (algebraMap (𝓞 E) E)
lemma zc8:Function.Injective (z5w E) :=
  Units.map_injective RingOfIntegers.coe_injective
lemma z5c (x:Eˣ) :
    toPrincipalIdeal (𝓞 E) E x = 1 ↔ x ∈ (z5w E).range:=by
  rw [toPrincipalIdeal_eq_iff]
  simp only [Units.val_one]
  rw [← FractionalIdeal.spanSingleton_one (S:=(𝓞 E)⁰)]
  rw [eq_comm,FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨u,hu⟩
    change (u:E)*1 = (x:E) at hu
    rw [mul_one] at hu
    exact ⟨u,Units.ext hu⟩
  · rintro ⟨u,hu⟩
    refine ⟨u,?_⟩
    have h:=congrArg Units.val hu
    change (u:E)*1 = (x:E)
    rw [mul_one]
    exact h
end z10
namespace z10
open NumberField
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
noncomputable def extend:Ideals K →* Ideals E :=
  Units.map (FractionalIdeal.extendedHom E (𝓞 E)).toMonoidHom
noncomputable def zcm:Kˣ →* Eˣ:=Units.map (algebraMap K E).toMonoidHom
lemma extend_injective:Function.Injective (extend K E) :=
  Units.map_injective (FractionalIdeal.extendedHom_injective (L:=E) (B:=𝓞 E) (A:=𝓞 K) (K:=K))
lemma zma (x:K) :
    FractionalIdeal.extendedHom E (𝓞 E) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap K E x):=by
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHom E (𝓞 E) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) :
    Submodule (𝓞 E) E) =
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap K E x):Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHom_eq_span,FractionalIdeal.coe_spanSingleton]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨y,hy,rfl⟩
    obtain ⟨r,hr⟩:=(FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).mp hy
    rw [← hr]
    change algebraMap K E ((r:K)*x) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _ (algebraMap (𝓞 K) (𝓞 E) r)
      (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro _ ⟨rfl⟩
    exact Submodule.subset_span ⟨x,FractionalIdeal.mem_spanSingleton_self _ _,rfl⟩
@[simp] lemma z58 (x:Kˣ) :
    extend K E (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 E) E (zcm K E x):=by
  apply Units.ext
  change FractionalIdeal.extendedHom E (𝓞 E)
    (toPrincipalIdeal (𝓞 K) K x:FractionalIdeal (𝓞 K)⁰ K) = _
  rw [coe_toPrincipalIdeal,coe_toPrincipalIdeal]
  exact zma K E x
variable (σ:E ≃ₐ[K] E)
lemma zfv (I:Ideals K):action E σ.toRingEquiv (extend K E I) = extend K E I:=by
  apply Units.ext
  change actionHom E σ.toRingEquiv (FractionalIdeal.extendedHom E (𝓞 E) I.1) =
    FractionalIdeal.extendedHom E (𝓞 E) I.1
  have hstable (τ:E ≃ₐ[K] E) (x:E)
      (hx:x ∈ FractionalIdeal.extendedHom E (𝓞 E) I.1) :
      τ x ∈ FractionalIdeal.extendedHom E (𝓞 E) I.1:=by
    change x ∈ ((FractionalIdeal.extendedHom E (𝓞 E) I.1):Submodule (𝓞 E) E) at hx
    change τ x ∈ ((FractionalIdeal.extendedHom E (𝓞 E) I.1):Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_extendedHom_eq_span] at hx ⊢
    refine Submodule.span_induction (p:=fun x _ => τ x ∈
      Submodule.span (𝓞 E) (algebraMap K E '' (I.1:Set K))) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨y,hy,rfl⟩
      rw [τ.commutes]
      exact Submodule.subset_span ⟨y,hy,rfl⟩
    · simpa only [map_zero] using Submodule.zero_mem _
    · intro a b ha hb h₁ h₂
      simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    · intro a b hb h
      change τ ((a:E)*b) ∈ _
      rw [map_mul]
      exact Submodule.smul_mem _ (RingOfIntegers.mapAlgEquiv τ a) h
  ext x
  rw [z29]
  constructor
  · intro h
    change σ.symm x ∈ _ at h
    simpa only [AlgEquiv.apply_symm_apply] using hstable σ (σ.symm x) h
  · exact hstable σ.symm x
end z10
namespace zj
open NumberField z10
open scoped Classical nonZeroDivisors
variable (K:Type*) [Field K] [NumberField K]
abbrev Classes:=Ideals K ⧸ (toPrincipalIdeal (𝓞 K) K).range
noncomputable def equiv:Classes K ≃* ClassGroup (𝓞 K):=(ClassGroup.equiv K).symm
instance:Finite (Classes K):=Finite.of_equiv (ClassGroup (𝓞 K)) (equiv K).symm.toEquiv
noncomputable def mk:Ideals K →* Classes K:=QuotientGroup.mk' _
lemma mk_surjective:Function.Surjective (mk K):=QuotientGroup.mk'_surjective _
@[simp] lemma mk_eq_one (I:Ideals K):mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range :=
  QuotientGroup.eq_one_iff I
@[simp] lemma zf9 (x:Kˣ):mk K (toPrincipalIdeal (𝓞 K) K x) = 1 :=
  (mk_eq_one K _).mpr ⟨x,rfl⟩
variable (E:Type*) [Field E] [NumberField E] [Algebra K E]
variable (σ:E ≃ₐ[K] E)
noncomputable def action:Classes E →* Classes E :=
  QuotientGroup.map _ _ (z10.action E σ.toRingEquiv).toMonoidHom (by
    rintro _ ⟨x,rfl⟩
    exact ⟨z15 E σ.toRingEquiv x,(z4f E σ.toRingEquiv x).symm⟩)
end zj
namespace z7
open NumberField z9 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2)
abbrev U:=Additive (𝓞 E)ˣ
abbrev F:=Additive Eˣ
abbrev P:=Additive (toPrincipalIdeal (𝓞 E) E).range
abbrev D:=Additive (Ideals E)
abbrev C:=Additive (zj.Classes E)
noncomputable instance:Module ℤ (C E):=AddCommGroup.toIntModule (C E)
noncomputable def z3g:F E →ₗ[ℤ] F E :=
  (MonoidHom.toAdditive (z15 E σ.toRingEquiv).toMonoidHom).toIntLinearMap
noncomputable def z22:D E →ₗ[ℤ] D E :=
  (MonoidHom.toAdditive (z10.action E σ.toRingEquiv).toMonoidHom).toIntLinearMap
noncomputable def zn1 :
    (toPrincipalIdeal (𝓞 E) E).range →* (toPrincipalIdeal (𝓞 E) E).range :=
  (((z10.action E σ.toRingEquiv).toMonoidHom).comp
    (toPrincipalIdeal (𝓞 E) E).range.subtype).codRestrict _ (fun p => by
      obtain ⟨x,hx⟩:=p.property
      refine ⟨z15 E σ.toRingEquiv x,?_⟩
      change toPrincipalIdeal (𝓞 E) E (z15 E σ.toRingEquiv x) =
        z10.action E σ.toRingEquiv p.1
      rw [← z4f,hx])
noncomputable def zcv:P E →ₗ[ℤ] P E :=
  (MonoidHom.toAdditive (zn1 K E σ)).toIntLinearMap
noncomputable def z31:C E →ₗ[ℤ] C E :=
  AddMonoidHom.toIntLinearMap (M:=C E) (M₂:=C E)
    (MonoidHom.toAdditive (zj.action K E σ))
noncomputable def zd0:U E →ₗ[ℤ] F E :=
  (MonoidHom.toAdditive (z5w E)).toIntLinearMap
noncomputable def principal:F E →ₗ[ℤ] P E :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 E) E).rangeRestrict).toIntLinearMap
noncomputable def z8t:P E →ₗ[ℤ] D E :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 E) E).range.subtype).toIntLinearMap
noncomputable def z1i:D E →ₗ[ℤ] C E :=
  AddMonoidHom.toIntLinearMap (M:=D E) (M₂:=C E)
    (MonoidHom.toAdditive (zj.mk E))
include hdeg in
lemma z76 (x:E):σ (σ x) = x:=by
  have hp:σ^2 = 1:=by
    rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
    exact pow_card_eq_one'
  exact congrArg (fun τ:E ≃ₐ[K] E => τ x) (by simpa [pow_two] using hp)
include hdeg in
lemma zf8:(z3g K E σ).comp (z3g K E σ) = LinearMap.id:=by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  exact z76 K E σ hdeg x.toMul
include hdeg in
lemma z33:(z22 K E σ).comp (z22 K E σ) = LinearMap.id:=by
  have hs:σ.toRingEquiv.symm = σ.toRingEquiv:=by
    ext x
    have h:=z76 K E σ hdeg (σ.symm x)
    change σ.symm x = σ x
    simpa only [AlgEquiv.apply_symm_apply] using h.symm
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  change actionHom E σ.toRingEquiv (actionHom E σ.toRingEquiv x.toMul.1) = x.toMul.1
  simpa only [hs] using z67 E σ.toRingEquiv x.toMul.1
include hdeg in
lemma z8v:(zcv K E σ).comp (zcv K E σ) = LinearMap.id:=by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  have h:=LinearMap.congr_fun (z33 K E σ hdeg) (Additive.ofMul x.toMul.1)
  exact congrArg Additive.toMul h
include hdeg in
lemma zfa:(z31 K E σ).comp (z31 K E σ) = LinearMap.id:=by
  apply LinearMap.ext
  intro x
  obtain ⟨I,hI⟩:=zj.mk_surjective E x.toMul
  have hi:z1i E (Additive.ofMul I) = x:=congrArg Additive.ofMul hI
  rw [← hi]
  have h:=LinearMap.congr_fun (z33 K E σ hdeg) (Additive.ofMul I)
  exact congrArg (z1i E) h
noncomputable def z1w:z17.Sequence (U E) (F E) (P E) where
  i:=zd0 E
  p:=principal E
  hi:=zc8 E
  hp x:=by
    obtain ⟨a,ha⟩:=x.toMul.property
    exact ⟨Additive.ofMul a,congrArg Additive.ofMul (Subtype.ext ha)⟩
  exact:=by
    ext x
    change (∃ u:U E, zd0 E u = x) ↔ principal E x = 0
    change (∃ u:(𝓞 E)ˣ, z5w E u = x.toMul) ↔
      (toPrincipalIdeal (𝓞 E) E).rangeRestrict x.toMul = 1
    rw [Subtype.ext_iff]
    exact (z5c E x.toMul).symm
  u:=z13.action K E σ
  a:=z3g K E σ
  b:=zcv K E σ
  hu:=z13.z40 K E σ hdeg
  ha:=zf8 K E σ hdeg
  hb:=z8v K E σ hdeg
  iu x:=by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  pa x:=by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (z4f E σ.toRingEquiv x.toMul).symm
noncomputable def z1d:z17.Sequence (P E) (D E) (C E) where
  i:=z8t E
  p:=z1i E
  hi:=fun x y h => congrArg Additive.ofMul (Subtype.ext (congrArg Additive.toMul h))
  hp x:=by
    obtain ⟨I,hI⟩:=zj.mk_surjective E x.toMul
    exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩
  exact:=by
    ext x
    change (∃ p:P E, z8t E p = x) ↔ z1i E x = 0
    change (∃ p:(toPrincipalIdeal (𝓞 E) E).range, p.1 = x.toMul) ↔
      zj.mk E x.toMul = 1
    rw [zj.mk_eq_one]
    constructor
    · rintro ⟨p,hp⟩; exact hp ▸ p.property
    · intro hx; exact ⟨⟨x.toMul,hx⟩,rfl⟩
  u:=zcv K E σ
  a:=z22 K E σ
  b:=z31 K E σ
  hu:=z8v K E σ hdeg
  ha:=z33 K E σ hdeg
  hb:=zfa K E σ hdeg
  iu _:=rfl
  pa _:=rfl
include hdeg in
lemma z94 (hne:σ ≠ 1) (z:F E) (hz:-z3g K E σ z = z) :
    ∃ x:F E, x-z3g K E σ x = z:=by
  have hprod:σ (z.toMul:E)*(z.toMul:E) = 1:=by
    change ((z15 E σ.toRingEquiv z.toMul)⁻¹:Eˣ) = z.toMul at hz
    have h':=congrArg Units.val hz
    rw [Units.val_inv_eq_inv_val] at h'
    change (σ (z.toMul:E))⁻¹ = (z.toMul:E) at h'
    calc
      σ (z.toMul:E)*(z.toMul:E) = σ (z.toMul:E)*(σ (z.toMul:E))⁻¹:=by rw [h']
      _ = 1:=mul_inv_cancel₀ (by simpa only [map_zero] using σ.injective.ne (Units.ne_zero z.toMul))
  have hn:Algebra.norm K (z.toMul:E) = 1:=by
    apply (algebraMap K E).injective
    rw [z13.z5j K E σ hdeg hne,hprod,map_one]
  have hg:∀ τ:E ≃ₐ[K] E, τ ∈ Subgroup.zpowers σ:=by
    intro τ
    rcases z13.z4h K E σ hdeg hne τ with ht | ht
    · rw [ht]; exact Subgroup.one_mem _
    · rw [ht]; exact Subgroup.mem_zpowers σ
  letI:Algebra.IsQuadraticExtension K E:=⟨hdeg⟩
  obtain ⟨x,hx⟩:=groupCohomology.exists_div_of_norm_eq_one (K:=K) (L:=E) (g:=σ) hg hn
  refine ⟨Additive.ofMul x,?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((x / z15 E σ.toRingEquiv x:Eˣ):E) = (z.toMul:E)
  rw [Units.val_div_eq_div_val]
  exact hx
end z7
namespace z7
open NumberField z9 z17
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
include hne in
lemma z98 :
    Function.Surjective (connecting (z1w K E σ hdeg)) :=
  z35 _ (z94 K E σ hdeg hne)
lemma z4z:Finite (z17.H1 (z1w K E σ hdeg).neg):=by
  dsimp [z17.H1,Sequence.neg]
  exact z9.z7h _ _
noncomputable def z99 :
    z17.H1 (z1w K E σ hdeg).neg ≃ₗ[ℤ] z13.H0 K E σ hdeg:=by
  exact LinearEquiv.refl ℤ (z13.H0 K E σ hdeg)
include hne in
lemma z8b :
    Nat.card (z17.H1 (z1d K E σ hdeg)) ≤
      Nat.card (z13.H0 K E σ hdeg):=by
  letI:=z4z K E σ hdeg
  have h:=zga (z1w K E σ hdeg) (z94 K E σ hdeg hne)
  rw [Nat.card_congr (z99 K E σ hdeg).toEquiv] at h
  exact h
include hne in
lemma z9f:Finite (z17.H1 (z1d K E σ hdeg)):=by
  letI:=z4z K E σ hdeg
  exact Finite.of_injective (z6m (z1w K E σ hdeg) (z94 K E σ hdeg hne))
    (z2p _ _)
abbrev z4k:=plus (A:=C E) (z31 K E σ) ⧸
  (z2m (z1d K E σ hdeg)).range
noncomputable def z7o :
    z4k K E σ hdeg ≃ₗ[ℤ] (connecting (z1d K E σ hdeg)).range :=
  (Submodule.quotEquivOfEq _ _ (z8d (z1d K E σ hdeg)).symm).trans
    (connecting (z1d K E σ hdeg)).quotKerEquivRange
include hne in
lemma zbl :
    Nat.card (z4k K E σ hdeg) ≤ Nat.card (z13.H0 K E σ hdeg):=by
  letI:=z9f K E σ hdeg hne
  rw [Nat.card_congr (z7o K E σ hdeg).toEquiv]
  exact (Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective).trans
    (z8b K E σ hdeg hne)
end z7
namespace z7
open NumberField z9 z17
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
noncomputable def zef:Submodule ℤ (plus (z22 K E σ)) :=
  (z2m (z1w K E σ hdeg)).range.map (z8e (z1d K E σ hdeg))
abbrev z7p:=plus (z22 K E σ) ⧸ zef K E σ hdeg
set_option maxHeartbeats 2000000 in
include hne in
lemma za2 :
    Nat.card (z7p K E σ hdeg) = Nat.card (z13.H1 K E σ hdeg) *
      Nat.card (z2m (z1d K E σ hdeg)).range:=by
  change Nat.card (_ ⧸ (z2m (z1w K E σ hdeg)).range.map
    (z8e (z1d K E σ hdeg))) = _
  refine (zgp _ (zfw (z1d K E σ hdeg)) _).trans ?_
  have e₁:(plus (zcv K E σ) ⧸ (z2m (z1w K E σ hdeg)).range) ≃ₗ[ℤ]
      z13.H1 K E σ hdeg :=
    (Submodule.quotEquivOfEq _ _ (z8d (z1w K E σ hdeg)).symm).trans
      ((connecting (z1w K E σ hdeg)).quotKerEquivOfSurjective
        (z98 K E σ hdeg hne))
  have e₂:(plus (z22 K E σ) ⧸ (z8e (z1d K E σ hdeg)).range) ≃ₗ[ℤ]
      (z2m (z1d K E σ hdeg)).range :=
    (Submodule.quotEquivOfEq _ _ (zlo (z1d K E σ hdeg)).symm).trans
      (z2m (z1d K E σ hdeg)).quotKerEquivRange
  exact congrArg₂ (·*·) (Nat.card_congr e₁.toEquiv) (Nat.card_congr e₂.toEquiv)
set_option maxHeartbeats 2000000 in
include hne in
lemma z9o [IsTotallyReal K] [IsTotallyReal E] :
    2*Nat.card (plus (A:=C E) (z31 K E σ)) ≤ Nat.card (z7p K E σ hdeg):=by
  have hc:=(z2m (z1d K E σ hdeg)).range.card_eq_card_quotient_mul_card
  change Nat.card (plus (A:=C E) (z31 K E σ)) =
    Nat.card (z2m (z1d K E σ hdeg)).range * Nat.card (z4k K E σ hdeg) at hc
  rw [hc,za2 K E σ hdeg hne,z13.zla K E σ hdeg hne]
  have h:=zbl K E σ hdeg hne
  calc
    _ ≤ 2*(Nat.card (z2m (z1d K E σ hdeg)).range *
      Nat.card (z13.H0 K E σ hdeg)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h)
    _ = _:=by ring
end z7

namespace z5s
open NumberField
variable {R A S:Type*} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [IsNoetherianRing S] [IsDomain S]
lemma hom_ext [Algebra.FormallyUnramified R A] (I:Ideal S) (hI:I ≠ ⊤)
    {f g:A →ₐ[R] S} (h:∀ x, f x - g x ∈ I):f = g:=by
  apply Algebra.FormallyUnramified.ext_of_iInf I (I.iInf_pow_eq_bot_of_isDomain hI)
  intro x
  exact Ideal.Quotient.eq.mpr (h x)
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma formallyUnramified (h:differentIdeal (𝓞 K) (𝓞 L) = ⊤) :
    Algebra.FormallyUnramified (𝓞 K) (𝓞 L):=by
  apply Algebra.unramifiedLocus_eq_univ_iff.mp
  apply Set.eq_univ_of_forall
  intro P
  apply not_dvd_differentIdeal_iff.mp
  rw [h,Ideal.dvd_iff_le]
  intro hh
  exact P.isPrime.ne_top (top_unique hh)
variable {K L} {M:Type*} [Field M] [NumberField M] [Algebra K M]
lemma zfk (hL:differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (I:Ideal (𝓞 M)) (hI:I ≠ ⊤) {f g:L →ₐ[K] M}
    (h:∀ x:𝓞 L, RingOfIntegers.mapAlgHom f x - RingOfIntegers.mapAlgHom g x ∈ I) :
    f = g:=by
  letI:=formallyUnramified K L hL
  have he:=hom_ext I hI h
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A:=𝓞 L)
  intro x
  exact congrArg (fun x:𝓞 M => (x:M)) (AlgHom.congr_fun he x)
lemma zky (hL:differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (I:Ideal (𝓞 M)) (hI:I ≠ ⊤) (σ:Gal(M/K))
    (hσ:σ ∈ I.toAddSubgroup.inertia Gal(M/K)) (f:L →ₐ[K] M) (x:L) :
    σ (f x) = f x:=by
  have he:σ.toAlgHom.comp f = f:=by
    apply zfk hL I hI
    intro y
    exact hσ (RingOfIntegers.mapAlgHom f y)
  exact AlgHom.congr_fun he x
end z5s
namespace z23
open NumberField
open scoped Classical
section Algebra
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
  (τ:S ≃ₐ[R] S)
end Algebra
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
include hne in
lemma z80 (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Ideal.span (Set.range (fun a:𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)) = ⊤:=by
  by_contra h
  apply hne
  apply AlgEquiv.coe_algHom_injective
  apply z5s.zfk hunram _ h
  intro a
  exact Ideal.subset_span (Set.mem_range_self a)
end z23
namespace z23
open NumberField
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
noncomputable def z6f (J:FractionalIdeal (𝓞 E)⁰ E):Submodule (𝓞 K) K :=
  (J.coeToSubmodule.restrictScalars (𝓞 K)).comap
    (IsScalarTower.toAlgHom (𝓞 K) K E).toLinearMap
include hdeg hne in
lemma zcc (J:FractionalIdeal (𝓞 E)⁰ E) :
    IsFractional (𝓞 K)⁰ (z6f K E J):=by
  obtain ⟨d,hd,hJ⟩:=J.isFractional
  let r:𝓞 K:=RingOfIntegers.norm K d
  have hd0:(d:E) ≠ 0:=RingOfIntegers.coe_ne_zero_iff.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  have hr0:r ≠ 0:=by
    apply RingOfIntegers.coe_ne_zero_iff.mp
    change Algebra.norm K (d:E) ≠ 0
    exact Algebra.norm_ne_zero_iff.mpr hd0
  refine ⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr hr0,?_⟩
  intro x hx
  obtain ⟨b,hb⟩:=hJ (algebraMap K E x) hx
  have hr:algebraMap K E (r:K) = σ (d:E)*(d:E) :=
    z13.z5j K E σ hdeg hne (d:E)
  have he:algebraMap K E ((r:K)*x) =
      ((RingOfIntegers.mapAlgEquiv σ d*b:𝓞 E):E):=by
    change algebraMap K E ((r:K)*x) = σ (d:E)*(b:E)
    change (b:E) = (d:E)*algebraMap K E x at hb
    rw [map_mul,hr,hb,mul_assoc]
  have hi:IsIntegral ℤ ((r:K)*x) :=
    (isIntegral_algebraMap_iff (R:=ℤ) (algebraMap K E).injective).mp
      (he ▸ (RingOfIntegers.mapAlgEquiv σ d*b).property)
  exact ⟨⟨(r:K)*x,hi⟩,rfl⟩
noncomputable def contraction (J:FractionalIdeal (𝓞 E)⁰ E):FractionalIdeal (𝓞 K)⁰ K :=
  ⟨z6f K E J,zcc K E σ hdeg hne J⟩
include hdeg hne in
lemma z63
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (J:FractionalIdeal (𝓞 E)⁰ E) (hJ:∀ x ∈ J, σ x ∈ J) :
    FractionalIdeal.extendedHom E (𝓞 E) (contraction K E σ hdeg hne J) = J:=by
  let I:=contraction K E σ hdeg hne J
  let V:Submodule (𝓞 E) E:=Submodule.span (𝓞 E) (algebraMap K E '' (I:Set K))
  have hVJ:V ≤ J.coeToSubmodule:=by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  have hσ (x:E):σ (σ x) = x:=by
    have hp:σ^2 = 1:=by
      rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
      exact pow_card_eq_one'
    exact congrArg (fun τ:E ≃ₐ[K] E => τ x) (by simpa [pow_two] using hp)
  have htrace (x:E) (hx:x ∈ J):σ x+x ∈ V:=by
    have hf:σ x+x ∈ Set.range (algebraMap K E):=by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases z13.z4h K E σ hdeg hne τ with rfl | rfl
      · rfl
      · rw [map_add,hσ]; ac_rfl
    obtain ⟨r,hr⟩:=hf
    apply Submodule.subset_span
    refine ⟨r,?_,hr⟩
    change algebraMap K E r ∈ J
    rw [hr]
    exact J.coeToSubmodule.add_mem (hJ x hx) hx
  have hJV:J.coeToSubmodule ≤ V:=by
    intro x hx
    have hmem:(1:𝓞 E) ∈ Ideal.span
        (Set.range (fun a:𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)):=by
      rw [z80 K E σ hne hunram]
      trivial
    have hh:∀ a ∈ Ideal.span
        (Set.range (fun a:𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)), a • x ∈ V:=by
      intro a ha
      refine Submodule.span_induction (p:=fun a _ => a • x ∈ V) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨b,rfl⟩
        have h₁:=V.smul_mem (RingOfIntegers.mapAlgEquiv σ b) (htrace x hx)
        have h₂:=htrace (b • x) (J.coeToSubmodule.smul_mem b hx)
        convert V.sub_mem h₁ h₂ using 1
        change ((σ (b:E))-(b:E))*x = σ (b:E)*(σ x+x)-(σ ((b:E)*x)+(b:E)*x)
        rw [map_mul]
        ring
      · simpa only [zero_smul] using V.zero_mem
      · intro a b ha hb h₁ h₂
        simpa only [add_smul] using V.add_mem h₁ h₂
      · intro a b hb h
        simpa only [smul_eq_mul,mul_smul] using V.smul_mem a h
    simpa only [one_smul] using hh 1 hmem
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHom E (𝓞 E) I):Submodule (𝓞 E) E) = J.coeToSubmodule
  rw [FractionalIdeal.coe_extendedHom_eq_span]
  exact le_antisymm hVJ hJV
end z23
namespace z4
open NumberField z9 z17 z7 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
noncomputable def z42:F K ≃ₗ[ℤ] plus (z3g K E σ):=by
  let f:F K →ₗ[ℤ] F E:=(MonoidHom.toAdditive (zcm K E)).toIntLinearMap
  let g:F K →ₗ[ℤ] plus (z3g K E σ):=f.codRestrict _ (fun x => by
    rw [z1g]
    apply Additive.toMul.injective
    apply Units.ext
    exact σ.commutes x.toMul)
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    apply Additive.toMul.injective
    exact Units.map_injective (algebraMap K E).injective (congrArg (fun z:plus (z3g K E σ) => z.1.toMul) h)
  · intro y
    have hy:=(z1g (z3g K E σ) _).mp y.property
    have hr:(y.1.toMul:E) ∈ Set.range (algebraMap K E):=by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases z13.z4h K E σ hdeg hne τ with ht | ht
      · rw [ht]; rfl
      · rw [ht]; exact congrArg (fun z:F E => (z.toMul:E)) hy
    obtain ⟨x,hx⟩:=hr
    have hx0:x ≠ 0:=by
      intro h0
      apply Units.ne_zero y.1.toMul
      rw [← hx,h0,map_zero]
    refine ⟨Additive.ofMul (Units.mk0 x hx0),Subtype.ext ?_⟩
    apply Additive.toMul.injective
    exact Units.ext hx
variable (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
noncomputable def z2v:D K ≃ₗ[ℤ] plus (z22 K E σ):=by
  let f:D K →ₗ[ℤ] D E:=(MonoidHom.toAdditive (z10.extend K E)).toIntLinearMap
  let g:D K →ₗ[ℤ] plus (z22 K E σ):=f.codRestrict _ (fun x =>
    (z1g _ _).mpr (z10.zfv K E σ x.toMul))
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    exact z10.extend_injective K E (congrArg (fun z:plus (z22 K E σ) => z.1.toMul) h)
  · intro J
    have hfix:=(z1g (z22 K E σ) _).mp J.property
    have hfi:actionHom E σ.toRingEquiv J.1.toMul.1 = J.1.toMul.1 :=
      congrArg (fun z:D E => z.toMul.1) hfix
    have hs (x:E) (hx:x ∈ J.1.toMul.1):σ x ∈ J.1.toMul.1:=by
      rw [← hfi,z29]
      change σ.symm (σ x) ∈ _
      simpa only [AlgEquiv.symm_apply_apply] using hx
    let I:=z23.contraction K E σ hdeg hne J.1.toMul.1
    have he:FractionalIdeal.extendedHom E (𝓞 E) I = J.1.toMul.1 :=
      z23.z63 K E σ hdeg hne hunram J.1.toMul.1 hs
    have hi:I ≠ 0:=by
      intro hi
      have hz:=he.symm
      rw [hi,map_zero] at hz
      exact J.1.toMul.ne_zero hz
    refine ⟨Additive.ofMul (Units.mk0 I hi),Subtype.ext ?_⟩
    apply Additive.toMul.injective
    exact Units.ext he
noncomputable def z11 (K:Type) [Field K] [NumberField K]:F K →ₗ[ℤ] D K :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 K) K)).toIntLinearMap
lemma z8z (x:F K) :
    z8e (z1d K E σ hdeg)
      (z2m (z1w K E σ hdeg) (z42 K E σ hdeg hne x)) =
        z2v K E σ hdeg hne hunram (z11 K x):=by
  apply Subtype.ext
  exact (z58 K E x.toMul).symm
set_option maxHeartbeats 2000000 in
lemma zkr :
    (z11 K).range.map (z2v K E σ hdeg hne hunram).toLinearMap =
      zef K E σ hdeg:=by
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    refine ⟨z2m (z1w K E σ hdeg) (z42 K E σ hdeg hne x),⟨_,rfl⟩,?_⟩
    exact z8z K E σ hdeg hne hunram x
  · rintro ⟨z,⟨x,rfl⟩,hx⟩
    obtain ⟨a,rfl⟩:=(z42 K E σ hdeg hne).surjective x
    refine ⟨z11 K a,⟨a,rfl⟩,?_⟩
    exact (z8z K E σ hdeg hne hunram a).symm.trans hx
noncomputable def zcq :
    (D K ⧸ (z11 K).range) ≃ₗ[ℤ] z7p K E σ hdeg :=
  Submodule.Quotient.equiv _ _ (z2v K E σ hdeg hne hunram)
    (zkr K E σ hdeg hne hunram)
lemma z7k:(z1i K).ker = (z11 K).range:=by
  ext x
  change zj.mk K x.toMul = 1 ↔ _
  rw [zj.mk_eq_one]
  rfl
noncomputable def zco:(D K ⧸ (z11 K).range) ≃ₗ[ℤ] C K :=
  (Submodule.quotEquivOfEq _ _ (z7k K).symm).trans
    ((z1i K).quotKerEquivOfSurjective (by
      intro x
      obtain ⟨I,hI⟩:=zj.mk_surjective K x.toMul
      exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩))
noncomputable def zk0:z7p K E σ hdeg ≃ₗ[ℤ] C K :=
  (zcq K E σ hdeg hne hunram).symm.trans (zco K)
include hdeg hne hunram in
lemma z77 [IsTotallyReal K] [IsTotallyReal E] :
    2*Nat.card (plus (A:=C E) (z31 K E σ)) ≤ Nat.card (ClassGroup (𝓞 K)):=by
  have h:=z9o K E σ hdeg hne
  rw [Nat.card_congr (zk0 K E σ hdeg hne hunram).toEquiv] at h
  exact h.trans_eq (Nat.card_congr (Additive.toMul.trans (zj.equiv K).toEquiv))
end z4
namespace z14
open NumberField Ideal Module
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
abbrev Primes (F:Type*) [Field F] [NumberField F]:={p:Ideal (𝓞 F) // Prime p}
noncomputable def below (P:Primes E):Primes K:=by
  letI:P.1.IsPrime:=(Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
  exact ⟨P.1.under (𝓞 K), Ideal.prime_of_isPrime (Ideal.under_ne_bot (𝓞 K) P.property.ne_zero) inferInstance⟩
noncomputable def degree (P:Primes E):ℕ:=(below K E P).1.inertiaDeg' P.1
lemma degree_pos (P:Primes E):0 < degree K E P:=by
  let p:=below K E P
  letI:p.1.IsPrime:=(Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI:p.1.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  haveI:P.1.LiesOver p.1:=inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
  exact Ideal.inertiaDeg'_pos p.1 P.1
noncomputable def norm:(Ideal (𝓞 E))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I:=⟨Ideal.relNorm (𝓞 K) I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    change Ideal.relNorm (𝓞 K) I.1 ≠ ⊥
    exact Ideal.relNorm_eq_bot_iff.not.mpr (nonZeroDivisors.coe_ne_zero I))⟩
  map_one':=by apply Subtype.ext; exact map_one _
  map_mul' I J:=by apply Subtype.ext; exact map_mul _ _ _
lemma relNorm_prime (P:Primes E) :
    Ideal.relNorm (𝓞 K) P.1 = (below K E P).1 ^ degree K E P:=by
  let p:=below K E P
  letI:p.1.IsPrime:=(Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI:p.1.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  letI:P.1.IsPrime:=(Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
  letI:P.1.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  haveI:P.1.LiesOver p.1:=inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
  rw [show degree K E P = P.1.inertiaDeg (𝓞 K) from Ideal.inertiaDeg'_eq_inertiaDeg (p:=p.1) (q:=P.1)]
  exact Ideal.relNorm_eq_pow_of_isMaximal P.1 p.1
lemma zkp (P:Primes E) :
    Ideal.absNorm P.1 = Ideal.absNorm (below K E P).1 ^ degree K E P:=by
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 E) P.1, relNorm_prime, map_pow]
lemma zk6 (s:Finset (Primes E)) (p:Primes K) :
    (s.filter (fun P => below K E P = p)).card ≤ Module.finrank K E:=by
  letI:NoZeroSMulDivisors (𝓞 K) (𝓞 E):=⟨fun h => smul_eq_zero.mp h⟩
  let t:=s.filter (fun P => below K E P = p)
  letI:p.1.IsPrime:=(Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI:p.1.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  have hsubset:t.image Subtype.val ⊆ primesOverFinset p.1 (𝓞 E):=by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩:=Finset.mem_image.mp hQ
    have he:=congrArg Subtype.val (Finset.mem_filter.mp hP).2
    letI:P.1.IsPrime:=(Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
    haveI:P.1.LiesOver p.1:=by
      rw [← he]
      exact inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
    exact (mem_primesOverFinset_iff p.property.ne_zero (𝓞 E)).mpr ⟨inferInstance,inferInstance⟩
  calc
    _ = (t.image Subtype.val).card:=(Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (primesOverFinset p.1 (𝓞 E)).card:=Finset.card_le_card hsubset
    _ ≤ _:=Ideal.card_primesOverFinset_le_finrank (𝓞 E) K E p.property.ne_zero
end z14
namespace z1o
open NumberField
open scoped Classical nonZeroDivisors
noncomputable def descend {A B C:Type*} [Monoid A] [Monoid B] [Monoid C]
    (q:A →* B) (hq:Function.Surjective q) (f:A →* C)
    (hf:∀ a b, q a = q b → f a = f b):B →* C where
  toFun b:=f (Classical.choose (hq b))
  map_one':=(hf _ 1 (by rw [Classical.choose_spec (hq 1),map_one])).trans f.map_one
  map_mul' b c:=by
    rw [← map_mul]
    apply hf
    rw [Classical.choose_spec (hq (b*c)),map_mul,Classical.choose_spec (hq b),Classical.choose_spec (hq c)]
@[simp] lemma zkk {A B C:Type*} [Monoid A] [Monoid B] [Monoid C]
    (q:A →* B) (hq:Function.Surjective q) (f:A →* C)
    (hf:∀ a b, q a = q b → f a = f b) (a:A) :
    descend q hq f hf (q a) = f a :=
  hf _ _ (Classical.choose_spec (hq (q a)))
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
lemma zdf (I J:(Ideal (𝓞 E))⁰) (h:ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (z14.norm K E I) = ClassGroup.mk0 (z14.norm K E J):=by
  obtain ⟨a,b,ha,hb,hab⟩:=ClassGroup.mk0_eq_mk0_iff.mp h
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  letI:=FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 E))
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 E) a,Algebra.intNorm (𝓞 K) (𝓞 E) b,
    Algebra.intNorm_ne_zero.mpr ha,Algebra.intNorm_ne_zero.mpr hb,?_⟩
  have h:=congrArg (Ideal.relNorm (𝓞 K)) hab
  rw [map_mul,map_mul,Ideal.relNorm_singleton,Ideal.relNorm_singleton] at h
  exact h
noncomputable def norm:ClassGroup (𝓞 E) →* ClassGroup (𝓞 K) :=
  descend ClassGroup.mk0 ClassGroup.mk0_surjective (ClassGroup.mk0.comp (z14.norm K E))
    (zdf K E)
@[simp] lemma zhl (I:(Ideal (𝓞 E))⁰) :
    norm K E (ClassGroup.mk0 I) = ClassGroup.mk0 (z14.norm K E I) :=
  zkk _ _ _ _ I
end z1o
namespace zj
open NumberField z10
open scoped Classical nonZeroDivisors
variable (K:Type*) [Field K] [NumberField K]
noncomputable def z8j:(Ideal (𝓞 K))⁰ →* Classes K:=(mk K).comp (FractionalIdeal.mk0 K)
@[simp] lemma z9s (I:(Ideal (𝓞 K))⁰):equiv K (z8j K I) = ClassGroup.mk0 I:=by
  change (ClassGroup.equiv K).symm (mk K (FractionalIdeal.mk0 K I)) = _
  change (ClassGroup.equiv K).symm (QuotientGroup.mk' _ (FractionalIdeal.mk0 K I)) = _
  rw [← ClassGroup.equiv_mk0, MulEquiv.symm_apply_apply]
lemma z9b:Function.Surjective (z8j K):=by
  intro c
  obtain ⟨I,hI⟩:=ClassGroup.mk0_surjective (equiv K c)
  exact ⟨I,(equiv K).injective ((z9s K I).trans hI)⟩
variable (E:Type*) [Field E] [NumberField E] [Algebra K E]
noncomputable def norm:Classes E →* Classes K :=
  ((equiv K).symm.toMonoidHom.comp (z1o.norm K E)).comp (equiv E).toMonoidHom
@[simp] lemma zba (I:(Ideal (𝓞 E))⁰) :
    norm K E (z8j E I) = z8j K (z14.norm K E I):=by
  apply (equiv K).injective
  change equiv K ((equiv K).symm (z1o.norm K E (equiv E (z8j E I)))) = _
  rw [MulEquiv.apply_symm_apply,z9s,z1o.zhl,z9s]
variable (σ:E ≃ₐ[K] E)
noncomputable def zi6 (I:(Ideal (𝓞 E))⁰):(Ideal (𝓞 E))⁰ :=
  ⟨Ideal.map (RingOfIntegers.mapAlgEquiv σ) I.1,mem_nonZeroDivisors_iff_ne_zero.mpr
    ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapAlgEquiv σ).injective).not.mpr
      (nonZeroDivisors.coe_ne_zero I))⟩
lemma zjf (I:(Ideal (𝓞 E))⁰) :
    action K E σ (z8j E I) = z8j E (zi6 K E σ I):=by
  change mk E (z10.action E σ.toRingEquiv (FractionalIdeal.mk0 E I)) =
    mk E (FractionalIdeal.mk0 E (zi6 K E σ I))
  apply congrArg (mk E)
  apply Units.ext
  change z10.actionHom E σ.toRingEquiv (FractionalIdeal.mk0 E I).1 =
    (FractionalIdeal.mk0 E (zi6 K E σ I)).1
  rw [FractionalIdeal.coe_mk0,FractionalIdeal.coe_mk0]
  exact FractionalIdeal.extended_coeIdeal_eq_map E _ I.1
lemma zme (c:Classes E):norm K E (action K E σ c) = norm K E c:=by
  obtain ⟨I,rfl⟩:=z9b E c
  rw [zjf,zba,zba]
  congr 1
  apply Subtype.ext
  exact Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv σ) I.1
end zj
namespace z3q
open scoped Classical
variable {A B:Type*} [AddCommGroup A] [AddCommGroup B]
lemma zad [Finite A] (f:A →ₗ[ℤ] A) :
    Nat.card (A ⧸ f.range) = Nat.card f.ker:=by
  have h₁:=f.range.card_eq_card_quotient_mul_card
  have h₂:=f.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv,mul_comm] at h₂
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h₁.symm.trans h₂)
lemma z4g [Finite A] [Finite B] (σ:A →ₗ[ℤ] A) (f:A →ₗ[ℤ] B)
    (hf:∀ x, f (σ x) = f x):Nat.card f.range ≤ Nat.card (z9.plus σ):=by
  have hle:(σ-LinearMap.id).range ≤ f.ker:=by
    rintro _ ⟨x,rfl⟩
    change f (σ x-x) = 0
    rw [map_sub,hf,sub_self]
  let q:=(σ-LinearMap.id).range.liftQ f hle
  have he:q.range = f.range:=Submodule.range_liftQ _ _ _
  rw [← he]
  letI:Finite (A ⧸ (σ-LinearMap.id).range) :=
    Finite.of_surjective _ (σ-LinearMap.id).range.mkQ_surjective
  calc
    Nat.card q.range ≤ Nat.card (A ⧸ (σ-LinearMap.id).range) :=
      Nat.card_le_card_of_surjective q.rangeRestrict (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
    _ = Nat.card (z9.plus σ):=zad _
end z3q
namespace z1k
open NumberField z7 z9
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E)
noncomputable def z2o:C E →ₗ[ℤ] C K :=
  AddMonoidHom.toIntLinearMap (M:=C E) (M₂:=C K) (MonoidHom.toAdditive (zj.norm K E))
lemma za6 (c:C E):z2o K E (z31 K E σ c) = z2o K E c :=
  zj.zme K E σ c.toMul
set_option maxHeartbeats 2000000 in
lemma z4g :
    Nat.card (z2o K E).range ≤ Nat.card (plus (A:=C E) (z31 K E σ)):=by
  letI:Finite (C E):=Finite.of_equiv (zj.Classes E) Additive.ofMul
  letI:Finite (C K):=Finite.of_equiv (zj.Classes K) Additive.ofMul
  exact @z3q.z4g (C E) (C K) inferInstance inferInstance
    inferInstance inferInstance (z31 K E σ) (z2o K E) (za6 K E σ)
end z1k
namespace z4v
open MeasureTheory Set Metric
open scoped ENNReal Classical BigOperators
variable {ι:Type*} [Fintype ι]
def cast (z:ι → ℤ):ι → ℝ:=fun i => z i
def cell (z:ι → ℤ):Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Ico (z i:ℝ) (z i+1)
noncomputable def floor (x:ι → ℝ):ι → ℤ:=fun i => ⌊x i⌋
@[simp] lemma zft (z:ι → ℤ) (x:ι → ℝ) :
    x ∈ cell z ↔ floor x = z:=by
  simp only [cell,Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Ico,floor,funext_iff]
  exact forall_congr' fun i => Int.floor_eq_iff.symm
lemma zdh (x:ι → ℝ):x ∈ cell (floor x):=by simp
lemma zkg:Pairwise (fun z w:ι → ℤ => Disjoint (cell z) (cell w)):=by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hzw ((zft z x).mp hx |>.symm.trans ((zft w x).mp hy))
lemma zfy (z:ι → ℤ):MeasurableSet (cell z) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
@[simp] lemma zo4 (z:ι → ℤ):volume (cell z) = 1:=by
  simp [cell,volume_pi_pi,Real.volume_Ico]
lemma zbd {z:ι → ℤ} {x:ι → ℝ} (hx:x ∈ cell z) :
    dist x (cast z) < 1:=by
  apply (dist_pi_lt_iff zero_lt_one).mpr
  intro i
  have hi:=Set.mem_pi.mp hx i (Set.mem_univ i)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  dsimp [cast]
  constructor <;> linarith [hi.1,hi.2]
def tiles (s:Finset (ι → ℤ)):Set (ι → ℝ):=⋃ z ∈ s, cell z
@[simp] lemma zo3 (s:Finset (ι → ℤ)):volume (tiles s) = s.card:=by
  rw [tiles,measure_biUnion_finset]
  · simp
  · exact zkg.set_pairwise _
  · intro z _
    exact zfy z
lemma z6a {S:Set (ι → ℝ)} {x y:ι → ℝ}
    (hx:x ∈ S) (hy:y ∉ S):∃ z ∈ frontier S, dist x z ≤ dist x y:=by
  obtain ⟨z,hz,he⟩:=exists_mem_frontier_infDist_compl_eq_dist hx
    (show S ≠ Set.univ from fun h => hy (h ▸ Set.mem_univ y))
  exact ⟨z,hz,he ▸ infDist_le_dist_of_mem (show y ∈ Sᶜ from hy)⟩
def cover (t:Finset (ι → ℝ)) (r:ℝ):Set (ι → ℝ):=⋃ y ∈ t, closedBall y r
lemma zgb (t:Finset (ι → ℝ)) :
    volume (cover t 2) ≤ (t.card:ℝ≥0∞)*4^Fintype.card ι:=by
  calc
    volume (cover t 2) ≤ ∑ y ∈ t, volume (closedBall y 2):=measure_biUnion_finset_le _ _
    _ = _:=by norm_num [Real.volume_pi_closedBall _ (by norm_num:(0:ℝ) ≤ 2)]
lemma zax (S:Set (ι → ℝ)) (s:Finset (ι → ℤ))
    (hs:∀ z, z ∈ s ↔ cast z ∈ S) (t:Finset (ι → ℝ))
    (ht:∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    tiles s ⊆ S ∪ cover t 2:=by
  intro x hx
  by_cases hxS:x ∈ S
  · exact Or.inl hxS
  · right
    obtain ⟨z,hz,hxz⟩:=Set.mem_iUnion₂.mp hx
    have hzS:=(hs z).mp hz
    obtain ⟨w,hw,hd⟩:=z6a (S:=Sᶜ) hxS (by simpa using hzS)
    rw [frontier_compl] at hw
    obtain ⟨y,hy,hwy⟩:=ht w hw
    refine Set.mem_iUnion₂.mpr ⟨y,hy,?_⟩
    apply mem_closedBall.mpr
    have hdx:=zbd hxz
    have htri:=dist_triangle x w y
    linarith
lemma zb6 (S:Set (ι → ℝ)) (s:Finset (ι → ℤ))
    (hs:∀ z, z ∈ s ↔ cast z ∈ S) (t:Finset (ι → ℝ))
    (ht:∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    S ⊆ tiles s ∪ cover t 2:=by
  intro x hx
  by_cases hz:floor x ∈ s
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨floor x,hz,zdh x⟩)
  · right
    have hzS:cast (floor x) ∉ S:=fun h => hz ((hs _).mpr h)
    obtain ⟨w,hw,hd⟩:=z6a hx hzS
    obtain ⟨y,hy,hwy⟩:=ht w hw
    refine Set.mem_iUnion₂.mpr ⟨y,hy,?_⟩
    apply mem_closedBall.mpr
    have hdx:=zbd (zdh x)
    have htri:=dist_triangle x w y
    linarith
lemma zmj (S:Set (ι → ℝ)) (hS:volume S ≠ ⊤)
    (s:Finset (ι → ℤ)) (hs:∀ z, z ∈ s ↔ cast z ∈ S)
    (t:Finset (ι → ℝ)) (ht:∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    |(s.card:ℝ)-volume.real S| ≤ (t.card:ℝ)*4^Fintype.card ι:=by
  have hc:volume (cover t 2) ≠ ⊤:=ne_top_of_le_ne_top (by finiteness) (zgb t)
  have htiles:volume (tiles s) ≠ ⊤:=by simp
  have h₁:=(measureReal_mono (μ:=volume) (zax S s hs t ht)
    (measure_union_lt_top hS.lt_top hc.lt_top).ne).trans (measureReal_union_le S (cover t 2))
  have h₂:=(measureReal_mono (μ:=volume) (zb6 S s hs t ht)
    (measure_union_lt_top htiles.lt_top hc.lt_top).ne).trans (measureReal_union_le (tiles s) (cover t 2))
  have he:volume.real (tiles s) = s.card:=by simp [measureReal_def]
  have hb:volume.real (cover t 2) ≤ (t.card:ℝ)*4^Fintype.card ι:=by
    have hh:=ENNReal.toReal_mono (by finiteness) (zgb t)
    simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofNat] using hh
  rw [he] at h₁ h₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
end z4v
namespace z2u
open Set Metric
open scoped Classical NNReal
variable {ι:Type*} [Fintype ι]
def cube (ι:Type*):Set (ι → ℝ):=Set.univ.pi fun _ => Set.Icc 0 1
noncomputable def point (n:ℕ) (v:ι → Fin (n+1)):ι → ℝ:=fun i => (v i:ℝ)/(n:ℝ)
lemma znc {n:ℕ} (hn:0 < n) (v:ι → Fin (n+1)):point n v ∈ cube ι:=by
  intro i _
  constructor
  · dsimp [point]; positivity
  · dsimp [point]
    apply (div_le_one (by exact_mod_cast hn)).mpr
    exact_mod_cast Nat.le_of_lt_succ (v i).isLt
lemma exists_point {n:ℕ} (hn:0 < n) (x:ι → ℝ) (hx:x ∈ cube ι) :
    ∃ v:ι → Fin (n+1), dist x (point n v) ≤ (n:ℝ)⁻¹:=by
  have hnr:(0:ℝ) < n:=by exact_mod_cast hn
  have hxn (i:ι):(n:ℝ)*x i ≤ n:=by
    have hi:=hx i (Set.mem_univ i)
    nlinarith [hi.2]
  let v:ι → Fin (n+1):=fun i => ⟨⌊(n:ℝ)*x i⌋₊,Nat.lt_succ_of_le (Nat.floor_le_of_le (hxn i))⟩
  refine ⟨v,(dist_pi_le_iff (inv_nonneg.mpr hnr.le)).mpr fun i => ?_⟩
  rw [Real.dist_eq]
  change |x i-(⌊(n:ℝ)*x i⌋₊:ℝ)/(n:ℝ)| ≤ (n:ℝ)⁻¹
  have hi:=hx i (Set.mem_univ i)
  have hfloor:=Nat.floor_le (show 0 ≤ (n:ℝ)*x i from mul_nonneg hnr.le hi.1)
  have hlt:=Nat.lt_floor_add_one ((n:ℝ)*x i)
  have hnonneg:0 ≤ x i-(⌊(n:ℝ)*x i⌋₊:ℝ)/(n:ℝ):=by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hnr).mpr
    nlinarith
  rw [abs_of_nonneg hnonneg,← one_div,sub_le_iff_le_add,← add_div]
  apply (le_div_iff₀ hnr).mpr
  nlinarith
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma zl6 (f:(ι → ℝ) → E) (K:ℝ≥0) (hf:LipschitzOnWith K f (cube ι))
    (t:ℝ) (ht:0 ≤ t) :
    ∃ s:Finset E, s.card ≤ (⌈t*(K:ℝ)⌉₊+2)^Fintype.card ι ∧
      ∀ x ∈ cube ι, ∃ y ∈ s, dist (t • f x) y ≤ 1:=by
  let n:=⌈t*(K:ℝ)⌉₊+1
  have hn:0 < n:=Nat.succ_pos _
  let s:=Finset.univ.image (fun v:ι → Fin (n+1) => t • f (point n v))
  refine ⟨s,?_,?_⟩
  · have hc:=Finset.card_image_le (s:=(Finset.univ:Finset (ι → Fin (n+1))))
      (f:=fun v => t • f (point n v))
    simpa [s,n,Fintype.card_fun] using hc
  · intro x hx
    obtain ⟨v,hv⟩:=exists_point hn x hx
    refine ⟨t • f (point n v),Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,?_⟩
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg ht]
    have hdist:=hf.dist_le_mul x hx (point n v) (znc hn v)
    have hnr:(0:ℝ) < n:=by exact_mod_cast hn
    have hnK:t*(K:ℝ) ≤ n:=by
      have hh:=Nat.le_ceil (t*(K:ℝ))
      dsimp [n]
      push_cast
      linarith
    calc
      t*dist (f x) (f (point n v)) ≤ t*((K:ℝ)*dist x (point n v)):=mul_le_mul_of_nonneg_left hdist ht
      _ ≤ t*((K:ℝ)*(n:ℝ)⁻¹):=by gcongr
      _ = (t*(K:ℝ))/(n:ℝ):=by rw [div_eq_mul_inv]; ring
      _ ≤ 1:=(div_le_one hnr).mpr hnK
lemma zgj (f:(ι → ℝ) → E) (K:ℝ≥0) (hf:LipschitzOnWith K f (cube ι))
    (t:ℝ) (ht:0 ≤ t) :
    ∃ s:Finset E, (s.card:ℝ) ≤ ((K:ℝ)+3)^Fintype.card ι*(t+1)^Fintype.card ι ∧
      ∀ x ∈ cube ι, ∃ y ∈ s, dist (t • f x) y ≤ 1:=by
  obtain ⟨s,hs,hcover⟩:=zl6 f K hf t ht
  refine ⟨s,?_,hcover⟩
  have hc:(⌈t*(K:ℝ)⌉₊:ℝ) < t*(K:ℝ)+1:=Nat.ceil_lt_add_one (mul_nonneg ht K.2)
  have hbound:(⌈t*(K:ℝ)⌉₊+2:ℝ) ≤ ((K:ℝ)+3)*(t+1):=by
    calc
      _ ≤ t*(K:ℝ)+3:=by linarith
      _ ≤ t*(K:ℝ)+3+((K:ℝ)+3*t):=le_add_of_nonneg_right (by positivity)
      _ = _:=by ring
  have hs':(s.card:ℝ) ≤ (⌈t*(K:ℝ)⌉₊+2:ℝ)^Fintype.card ι:=by exact_mod_cast hs
  calc
    _ ≤ (⌈t*(K:ℝ)⌉₊+2:ℝ)^Fintype.card ι:=hs'
    _ ≤ (((K:ℝ)+3)*(t+1))^Fintype.card ι:=pow_le_pow_left₀ (by positivity) hbound _
    _ = _:=mul_pow _ _ _
end z2u
namespace z6q
open MeasureTheory Set Metric
open scoped Classical Pointwise NNReal BigOperators
variable {ι κ:Type*} [Fintype ι] [Fintype κ]
variable (S:Set (ι → ℝ)) (r:ℕ)
  (f:κ → (Fin r → ℝ) → (ι → ℝ)) (K:κ → ℝ≥0)
  (hf:∀ j, LipschitzOnWith (K j) (f j) (z2u.cube (Fin r)))
  (hfront:∀ x ∈ frontier S, ∃ j y, y ∈ z2u.cube (Fin r) ∧ f j y = x)
include hf hfront
lemma zex (t:ℝ) (ht:0 < t) :
    ∃ T:Finset (ι → ℝ), (T.card:ℝ) ≤
      (∑ j, ((K j:ℝ)+3)^r)*(t+1)^r ∧
      ∀ x ∈ frontier (t • S), ∃ y ∈ T, dist x y ≤ 1:=by
  have hex:∀ j, ∃ T:Finset (ι → ℝ), (T.card:ℝ) ≤
      ((K j:ℝ)+3)^r*(t+1)^r ∧
      ∀ x ∈ z2u.cube (Fin r), ∃ y ∈ T, dist (t • f j x) y ≤ 1:=by
    intro j
    simpa using z2u.zgj (f j) (K j) (hf j) t ht.le
  choose T hT hcov using hex
  refine ⟨Finset.univ.biUnion T,?_,?_⟩
  · have hc:((Finset.univ.biUnion T).card:ℝ) ≤ ∑ j, ((T j).card:ℝ):=by
      exact_mod_cast (Finset.card_biUnion_le (s:=Finset.univ) (t:=T))
    refine hc.trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hT j
  · intro x hx
    have he:frontier (t • S) = t • frontier S:=by
      have hh:=(Homeomorph.smul (α:=ι → ℝ) (Units.mk0 t ht.ne')).image_frontier S
      change (fun x:ι → ℝ => t • x) '' frontier S =
        frontier ((fun x:ι → ℝ => t • x) '' S) at hh
      simpa only [Set.image_smul] using hh.symm
    rw [he] at hx
    obtain ⟨z,hz,rfl⟩:=hx
    obtain ⟨j,y,hy,hyz⟩:=hfront z hz
    obtain ⟨w,hw,hd⟩:=hcov j y hy
    refine ⟨w,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hw⟩,?_⟩
    simpa only [hyz] using hd
lemma zf5 (hS:volume S ≠ ⊤) (t:ℝ) (ht:0 < t)
    (s:Finset (ι → ℤ)) (hs:∀ z, z ∈ s ↔ z4v.cast z ∈ t • S) :
    |(s.card:ℝ)-t^Fintype.card ι*volume.real S| ≤
      4^Fintype.card ι*(∑ j, ((K j:ℝ)+3)^r)*(t+1)^r:=by
  obtain ⟨T,hT,hcov⟩:=zex S r f K hf hfront t ht
  have hvol:volume (t • S) ≠ ⊤:=by
    rw [volume.addHaar_smul_of_nonneg ht.le]
    exact ENNReal.mul_ne_top (by finiteness) hS
  have he:volume.real (t • S) = t^Fintype.card ι*volume.real S:=by
    rw [measureReal_def,volume.addHaar_smul_of_nonneg ht.le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.le _),Module.finrank_pi]
    rfl
  have hcount:=z4v.zmj (t • S) hvol s hs T hcov
  rw [he] at hcount
  calc
    _ ≤ (T.card:ℝ)*4^Fintype.card ι:=hcount
    _ ≤ ((∑ j, ((K j:ℝ)+3)^r)*(t+1)^r)*4^Fintype.card ι:=by gcongr
    _ = _:=by ring
lemma z4y (hS:volume S ≠ ⊤) :
    ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t → ∀ s:Finset (ι → ℤ),
      (∀ z, z ∈ s ↔ z4v.cast z ∈ t • S) →
      |(s.card:ℝ)-t^Fintype.card ι*volume.real S| ≤ C*t^r:=by
  let C:=4^Fintype.card ι*(∑ j, ((K j:ℝ)+3)^r)*2^r+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht s hs
  have ht0:0 < t:=lt_of_lt_of_le zero_lt_one ht
  have hh:=zf5 S r f K hf hfront hS t ht0 s hs
  have hp:(t+1)^r ≤ 2^r*t^r:=by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    _ ≤ 4^Fintype.card ι*(∑ j, ((K j:ℝ)+3)^r)*(t+1)^r:=hh
    _ ≤ 4^Fintype.card ι*(∑ j, ((K j:ℝ)+3)^r)*(2^r*t^r):=by gcongr
    _ ≤ C*t^r:=by dsimp [C]; nlinarith [pow_nonneg ht0.le r]
end z6q
namespace zii
open Set
open scoped Classical
variable {ι:Type*} [Fintype ι]
lemma zkj (S:Set (ι → ℝ)) (hS:Bornology.IsBounded S) :
    {z:ι → ℤ | (fun i => (z i:ℝ)) ∈ S}.Finite:=by
  obtain ⟨C,hC⟩:=hS.exists_norm_le
  let m:ℤ:=⌈|C|⌉
  have hfin:(Set.univ.pi fun _:ι => Set.Icc (-m) m).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply hfin.subset
  intro z hz i _
  have hi:|(z i:ℝ)| ≤ C:=by
    have hh:=norm_le_pi_norm (fun i => (z i:ℝ)) i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (hC _ hz)
  have hm:C ≤ (m:ℝ):=(le_abs_self C).trans (Int.le_ceil _)
  have hle:|(z i:ℝ)| ≤ (m:ℝ):=hi.trans hm
  have hh:=abs_le.mp hle
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2
lemma exists_finset (S:Set (ι → ℝ)) (hS:Bornology.IsBounded S) :
    ∃ s:Finset (ι → ℤ), ∀ z, z ∈ s ↔ (fun i => (z i:ℝ)) ∈ S:=by
  exact ⟨(zkj S hS).toFinset,fun z => Set.Finite.mem_toFinset _⟩
end zii
namespace z7w
open MeasureTheory Set Metric
open scoped Classical Pointwise NNReal BigOperators
variable {ι κ E:Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma z4y (S:Set E) (hS:Bornology.IsBounded S)
    (r:ℕ) (g:κ → (Fin r → ℝ) → E) (K:κ → ℝ≥0)
    (hg:∀ j, LipschitzOnWith (K j) (g j) (z2u.cube (Fin r)))
    (hfront:∀ x ∈ frontier S, ∃ j y, y ∈ z2u.cube (Fin r) ∧ g j y = x)
    (b:(ι → ℝ) ≃L[ℝ] E) :
    ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t →
      |(Nat.card {z:ι → ℤ | b (fun i => (z i:ℝ)) ∈ t • S}:ℝ)-
        t^Fintype.card ι*volume.real (b ⁻¹' S)| ≤ C*t^r:=by
  let T:Set (ι → ℝ):=b ⁻¹' S
  let f:κ → (Fin r → ℝ) → (ι → ℝ):=fun j y => b.symm (g j y)
  let K':κ → ℝ≥0:=fun j => ‖b.symm.toContinuousLinearMap‖₊ * K j
  have hf:∀ j, LipschitzOnWith (K' j) (f j) (z2u.cube (Fin r)):=by
    intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb:=b.symm.toContinuousLinearMap.lipschitz.dist_le_mul (g j x) (g j y)
    have hh:=(hg j).dist_le_mul x hx y hy
    calc
      dist (f j x) (f j y) ≤ ‖b.symm.toContinuousLinearMap‖*dist (g j x) (g j y):=hb
      _ ≤ ‖b.symm.toContinuousLinearMap‖*((K j:ℝ)*dist x y):=by gcongr
      _ = (K' j:ℝ)*dist x y:=by simp only [K',NNReal.coe_mul,coe_nnnorm]; ring
  have hfr:∀ x ∈ frontier T, ∃ j y, y ∈ z2u.cube (Fin r) ∧ f j y = x:=by
    intro x hx
    have hx':b x ∈ frontier S:=by
      change x ∈ b ⁻¹' frontier S
      change x ∈ b.toHomeomorph ⁻¹' frontier S
      rw [b.toHomeomorph.preimage_frontier]
      exact hx
    obtain ⟨j,y,hy,he⟩:=hfront (b x) hx'
    exact ⟨j,y,hy,by dsimp [f]; rw [he,b.symm_apply_apply]⟩
  have hT:Bornology.IsBounded T:=b.antilipschitz.isBounded_preimage hS
  obtain ⟨C,hC,hcount⟩:=z6q.z4y T r f K' hf hfr hT.measure_lt_top.ne
  refine ⟨C,hC,?_⟩
  intro t ht
  have ht0:0 < t:=lt_of_lt_of_le zero_lt_one ht
  have hset:b ⁻¹' (t • S) = t • T:=by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      refine ⟨b.symm y,by simpa [T] using hy,?_⟩
      have hh:=congrArg b.symm he
      simpa only [map_smul,b.symm_apply_apply] using hh
    · rintro ⟨y,hy,rfl⟩
      exact ⟨b y,hy,(map_smul b t y).symm⟩
  have htT:Bornology.IsBounded (t • T):=by
    rw [← Set.image_smul]
    exact (lipschitzWith_smul t).isBounded_image hT
  obtain ⟨s,hs⟩:=zii.exists_finset (t • T) htT
  have hcard:Nat.card {z:ι → ℤ | b (fun i => (z i:ℝ)) ∈ t • S} = s.card:=by
    calc
      _ = Nat.card {z:ι → ℤ | z ∈ s}:=Nat.card_congr (Equiv.setCongr (by
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hs z]
        change (fun i => (z i:ℝ)) ∈ b ⁻¹' (t • S) ↔ _
        rw [hset]))
      _ = s.card:=Nat.card_eq_finsetCard s
  rw [hcard]
  exact hcount t ht s hs
end z7w
namespace z1y
open Set Metric
open scoped Classical NNReal
variable {n:ℕ}
abbrev cube (n:ℕ):Set (Fin n → ℝ):=Set.univ.pi fun _ => Set.Icc 0 1
@[simp] lemma zeo:interior (cube n) = Set.univ.pi (fun _ => Set.Ioo (0:ℝ) 1):=by
  change interior (Set.univ.pi fun _:Fin n => Set.Icc (0:ℝ) 1) = _
  rw [interior_pi_set Set.finite_univ]
  simp only [interior_Icc]
lemma zis (i:Fin (n+1)) (ε:Fin 2) {y:Fin n → ℝ} (hy:y ∈ cube n) :
    i.insertNth (α:=fun _ => ℝ) (ε:ℝ) y ∈ cube (n+1):=by
  intro j _
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same]
    constructor
    · positivity
    · exact_mod_cast Nat.le_of_lt_succ ε.isLt
  · simpa only [Fin.insertNth_apply_succAbove] using hy k (Set.mem_univ k)
lemma zmg (i:Fin (n+1)) (ε:Fin 2) (x y:Fin n → ℝ) :
    dist (i.insertNth (α:=fun _ => ℝ) (ε:ℝ) x) (i.insertNth (α:=fun _ => ℝ) (ε:ℝ) y) = dist x y:=by
  rw [Fin.dist_insertNth_insertNth,dist_self,max_eq_right dist_nonneg]
lemma zm7 (y:Fin (n+1) → ℝ) (hy:y ∈ cube (n+1))
    (hyi:y ∉ interior (cube (n+1))) :
    ∃ i:Fin (n+1), ∃ ε:Fin 2, ∃ x:Fin n → ℝ,
      x ∈ cube n ∧ i.insertNth (α:=fun _ => ℝ) (ε:ℝ) x = y:=by
  have hh:¬ ∀ i, 0 < y i ∧ y i < 1:=by
    intro h
    apply hyi
    rw [zeo]
    exact fun i _ => h i
  push_neg at hh
  obtain ⟨i,hi⟩:=hh
  have hib:=hy i (Set.mem_univ i)
  have he:y i = 0 ∨ y i = 1:=by
    by_cases h:0 < y i
    · exact Or.inr (le_antisymm hib.2 (hi h))
    · exact Or.inl (le_antisymm (le_of_not_gt h) hib.1)
  have hx:i.removeNth y ∈ cube n:=fun k _ => hy (i.succAbove k) (Set.mem_univ _)
  rcases he with he | he
  · refine ⟨i,0,i.removeNth y,hx,?_⟩
    simpa only [Fin.val_zero,Nat.cast_zero,he] using Fin.insertNth_self_removeNth i y
  · refine ⟨i,1,i.removeNth y,hx,?_⟩
    simpa only [Fin.val_one,Nat.cast_one,he] using Fin.insertNth_self_removeNth i y
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ:Type*} [Fintype κ]
lemma zku (S:Set E) (f:κ → (Fin (n+1) → ℝ) → E)
    (K:κ → ℝ≥0) (hf:∀ j, LipschitzOnWith (K j) (f j) (cube (n+1)))
    (hclosure:∀ z ∈ closure S, ∃ j y, y ∈ cube (n+1) ∧ f j y = z)
    (hinterior:∀ j y, y ∈ interior (cube (n+1)) → f j y ∈ interior S) :
    ∃ g:(κ × Fin (n+1) × Fin 2) → (Fin n → ℝ) → E,
      (∀ j, LipschitzOnWith (K j.1) (g j) (cube n)) ∧
      ∀ z ∈ frontier S, ∃ j y, y ∈ cube n ∧ g j y = z:=by
  let g:(κ × Fin (n+1) × Fin 2) → (Fin n → ℝ) → E :=
    fun j x => f j.1 (j.2.1.insertNth (α:=fun _ => ℝ) (j.2.2:ℝ) x)
  refine ⟨g,?_,?_⟩
  · intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hf j.1).dist_le_mul _ (zis _ _ hx) _ (zis _ _ hy) |>.trans_eq
      (congrArg ((K j.1:ℝ)*·) (zmg _ _ x y))
  · intro z hz
    obtain ⟨j,y,hy,he⟩:=hclosure z hz.1
    have hyi:y ∉ interior (cube (n+1)):=by
      intro h
      exact hz.2 (he ▸ hinterior j y h)
    obtain ⟨i,ε,x,hx,hxy⟩:=zm7 y hy hyi
    exact ⟨(j,i,ε),x,hx,by simpa only [g,hxy] using he⟩
lemma zho (f:(Fin n → ℝ) → E) (hf:ContDiffOn ℝ 1 f (cube n)) :
    ∃ K:ℝ≥0, LipschitzOnWith K f (cube n) :=
  hf.exists_lipschitzOnWith (by norm_num) (convex_pi fun _ _ => convex_Icc 0 1)
    (isCompact_univ_pi fun _ => isCompact_Icc)
end z1y
namespace z1l
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units.dirichletUnitTheorem
open Set MeasureTheory
open scoped Classical Pointwise
variable (K:Type*) [Field K] [NumberField K]
abbrev space:=InfinitePlace K → ℝ
def z6s (x:space K):space K:=fun w => |x w|
def region:Set (space K):=z6s K ⁻¹' (expMapBasis '' paramSet K)
abbrev cube:Set (space K):=Set.univ.pi fun _ => Set.Icc 0 1
noncomputable def z4j (x:space K):space K:=fun w => if w = w₀ then 0 else x w
noncomputable def chart (ε:InfinitePlace K → Fin 2) (x:space K):space K :=
  fun w => (-1:ℝ)^(ε w).val * x w₀ * expMapBasis (z4j K x) w
lemma ze0:ContDiff ℝ 1 (expMapBasis:space K → space K):=by
  apply contDiff_pi.mpr
  intro w
  simp only [expMapBasis_apply,expMap_apply]
  change ContDiff ℝ 1 (fun x:space K => Real.exp ((w.mult:ℝ)⁻¹ *
    (completeBasis K).equivFunL.symm x w))
  fun_prop
lemma zeu:ContDiff ℝ 1 (z4j K):=by
  apply contDiff_pi.mpr
  intro w
  dsimp only [z4j]
  split_ifs <;> fun_prop
lemma zjs (ε:InfinitePlace K → Fin 2):ContDiff ℝ 1 (chart K ε):=by
  apply contDiff_pi.mpr
  intro w
  dsimp only [chart]
  have hh:=(ze0 K).comp (zeu K)
  have hc:ContDiff ℝ 1 (fun x:space K => expMapBasis (z4j K x) w) :=
    (contDiff_pi.mp hh) w
  fun_prop
lemma znl (ε:InfinitePlace K → Fin 2) (x:space K) (hx:0 ≤ x w₀) :
    z6s K (chart K ε x) = x w₀ • expMapBasis (z4j K x):=by
  ext w
  simp only [z6s,chart,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg hx,abs_of_nonneg (expMapBasis_nonneg _ _),Pi.smul_apply,smul_eq_mul]
lemma zab:Continuous (z6s K):=by unfold z6s; fun_prop
lemma z7d:closure (region K) ⊆ z6s K ⁻¹' compactSet K:=by
  refine ((zab K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  apply (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K)
lemma zj4 (x:space K) (hx:x ∈ closure (region K)) :
    ∃ ε:InfinitePlace K → Fin 2, ∃ y:space K, y ∈ cube K ∧ chart K ε y = x:=by
  have hh:=z7d K hx
  obtain ⟨r,hr,_,⟨z,hz,rfl⟩,he⟩:=hh
  let y:space K:=fun w => if w = w₀ then r else z w
  have hy:y ∈ cube K:=by
    intro w _
    dsimp only [y]
    split_ifs with hw
    · exact hr
    · simpa only [if_neg hw] using hz w (Set.mem_univ _)
  have hyr:y w₀ = r:=by simp [y]
  have hyz:z4j K y = z:=by
    ext w
    dsimp only [z4j,y]
    split_ifs with hw
    · subst w
      exact (Set.mem_singleton_iff.mp (by simpa using hz w₀ (Set.mem_univ _))).symm
    · rfl
  let ε:InfinitePlace K → Fin 2:=fun w => if x w < 0 then 1 else 0
  refine ⟨ε,y,hy,?_⟩
  ext w
  have hew:=congrFun he w
  change r * expMapBasis z w = |x w| at hew
  simp only [chart,hyr,hyz]
  rw [mul_assoc,hew]
  dsimp only [ε]
  split_ifs with hw
  · simp [abs_of_neg hw]
  · simp [abs_of_nonneg (le_of_not_gt hw)]
lemma zb9 :
    z6s K ⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (region K):=by
  have hO:IsOpen (expMapBasis '' interior (paramSet K)) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  apply interior_maximal (Set.preimage_mono (Set.image_mono interior_subset))
  exact hO.preimage (zab K)
lemma zki (ε:InfinitePlace K → Fin 2) (y:space K)
    (hy:y ∈ interior (cube K)):chart K ε y ∈ interior (region K):=by
  have hy':∀ w, 0 < y w ∧ y w < 1:=by
    rw [show interior (cube K) = Set.univ.pi (fun _ => Set.Ioo (0:ℝ) 1) by
      change interior (Set.univ.pi fun _:InfinitePlace K => Set.Icc (0:ℝ) 1) = _
      rw [interior_pi_set Set.finite_univ]
      simp only [interior_Icc]] at hy
    exact fun w => hy w (Set.mem_univ w)
  let z:space K:=fun w => if w = w₀ then Real.log (y w₀) else y w
  apply zb9 K
  refine ⟨z,?_,?_⟩
  · rw [interior_paramSet]
    intro w _
    dsimp only [z]
    split_ifs with hw
    · exact Real.log_neg (hy' w₀).1 (hy' w₀).2
    · exact hy' w
  · rw [expMapBasis_apply'',show z w₀ = Real.log (y w₀) by simp [z],Real.exp_log (hy' w₀).1,
      znl K ε y (hy' w₀).1.le]
    congr 2
    ext w
    dsimp only [z,z4j]
    split_ifs <;> rfl
end z1l
namespace z1l
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units.dirichletUnitTheorem
open Set MeasureTheory
open scoped Classical Pointwise NNReal
variable (K:Type*) [Field K] [NumberField K]
lemma zmi (x:space K):‖z6s K x‖ = ‖x‖:=by
  simp [z6s,Pi.norm_def,Real.norm_eq_abs]
lemma zi8:Bornology.IsBounded (region K):=by
  obtain ⟨C,hC⟩:=(isCompact_compactSet K).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,fun x hx => ?_⟩
  rw [← zmi K x]
  exact hC _ (z7d K (subset_closure hx))
variable (n:ℕ) (e:Fin (n+1) ≃ InfinitePlace K)
def reindex (x:Fin (n+1) → ℝ):space K:=fun w => x (e.symm w)
lemma zds {x:Fin (n+1) → ℝ}
    (hx:x ∈ interior (z1y.cube (n+1))) :
    reindex K n e x ∈ interior (cube K):=by
  rw [z1y.zeo] at hx
  change reindex K n e x ∈ interior (Set.univ.pi fun _:InfinitePlace K => Set.Icc (0:ℝ) 1)
  rw [interior_pi_set Set.finite_univ]
  simp only [interior_Icc]
  exact fun w _ => hx (e.symm w) (Set.mem_univ _)
include e in
lemma zc5 :
    ∃ g:((InfinitePlace K → Fin 2) × Fin (n+1) × Fin 2) → (Fin n → ℝ) → space K,
    ∃ C:((InfinitePlace K → Fin 2) × Fin (n+1) × Fin 2) → ℝ≥0,
      (∀ j, LipschitzOnWith (C j) (g j) (z1y.cube n)) ∧
      ∀ z ∈ frontier (region K), ∃ j y, y ∈ z1y.cube n ∧ g j y = z:=by
  let f:(InfinitePlace K → Fin 2) → (Fin (n+1) → ℝ) → space K :=
    fun ε x => chart K ε (reindex K n e x)
  have hfd (ε:InfinitePlace K → Fin 2):ContDiff ℝ 1 (f ε):=by
    apply (zjs K ε).comp
    unfold reindex
    fun_prop
  have hf:∀ ε, ∃ C:ℝ≥0, LipschitzOnWith C (f ε) (z1y.cube (n+1)) :=
    fun ε => z1y.zho _ (hfd ε).contDiffOn
  choose C hC using hf
  have hclosure:∀ z ∈ closure (region K), ∃ ε y,
      y ∈ z1y.cube (n+1) ∧ f ε y = z:=by
    intro z hz
    obtain ⟨ε,y,hy,he⟩:=zj4 K z hz
    refine ⟨ε,fun i => y (e i),fun i _ => hy (e i) (Set.mem_univ _),?_⟩
    have hey:reindex K n e (fun i => y (e i)) = y:=by
      ext w
      exact congrArg y (e.apply_symm_apply w)
    change chart K ε (reindex K n e (fun i => y (e i))) = z
    rw [hey]
    exact he
  have hi:∀ ε y, y ∈ interior (z1y.cube (n+1)) →
      f ε y ∈ interior (region K):=by
    intro ε y hy
    exact zki K ε _ (zds K n e hy)
  obtain ⟨g,hg,hfront⟩:=z1y.zku (region K) f C hC hclosure hi
  exact ⟨g,fun j => C j.1,hg,hfront⟩
end z1l
namespace z1l
open NumberField MeasureTheory
open scoped Pointwise Classical
variable (K:Type*) [Field K] [NumberField K]
lemma zbq (n:ℕ) (e:Fin (n+1) ≃ InfinitePlace K)
    (b:(Fin (n+1) → ℝ) ≃L[ℝ] space K) :
    ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t →
      |(Nat.card {z:Fin (n+1) → ℤ | b (fun i => (z i:ℝ)) ∈ t • region K}:ℝ)-
        t^(n+1)*volume.real (b ⁻¹' region K)| ≤ C*t^n:=by
  obtain ⟨g,D,hg,hfront⟩:=zc5 K n e
  simpa using z7w.z4y (region K) (zi8 K)
    n g D hg hfront b
end z1l
namespace z2d
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped Classical
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
noncomputable def equiv:realSpace K ≃L[ℝ] mixedSpace K :=
  (LinearEquiv.ofBijective (mixedSpaceOfRealSpace (K:=K)).toLinearMap ⟨injective_mixedSpaceOfRealSpace K,by
    intro x
    refine ⟨fun w => x.1 ⟨w,IsTotallyReal.isReal w⟩,?_⟩
    apply Prod.ext
    · rfl
    · funext w
      exact (not_isReal_iff_isComplex.mpr w.property (IsTotallyReal.isReal w.1)).elim⟩).toContinuousLinearEquiv
@[simp] lemma zdg (x:realSpace K) :
    normAtAllPlaces (equiv K x) = z1l.z6s K x:=by
  ext w
  change normAtPlace w (mixedSpaceOfRealSpace x) = |x w|
  rw [normAtPlace_apply_of_isReal (IsTotallyReal.isReal w)]
  rfl
lemma z9e:(equiv K) ⁻¹' normLeOne K = z1l.region K:=by
  ext x
  rw [Set.mem_preimage,normLeOne_eq_preimage]
  change normAtAllPlaces (equiv K x) ∈ expMapBasis '' paramSet K ↔ _
  rw [zdg]
  rfl
end z2d
namespace z71
open Module
open scoped Classical
variable {ι E:Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
noncomputable def map (b:Basis ι ℝ E) (z:ι → ℤ):E :=
  b.equivFunL.symm (fun i => (z i:ℝ))
lemma map_injective (b:Basis ι ℝ E):Function.Injective (map b):=by
  intro z w h
  have h':=b.equivFunL.symm.injective h
  funext i
  exact_mod_cast congrFun h' i
lemma range_map (b:Basis ι ℝ E) :
    Set.range (map b) = (Submodule.span ℤ (Set.range b):Set E):=by
  ext x
  rw [SetLike.mem_coe, b.mem_span_iff_repr_mem ℤ]
  constructor
  · rintro ⟨z,rfl⟩ i
    refine ⟨z i,?_⟩
    change (z i:ℝ) = b.equivFun (b.equivFun.symm (fun j => (z j:ℝ))) i
    rw [LinearEquiv.apply_symm_apply]
  · intro h
    choose z hz using h
    refine ⟨z, b.equivFunL.injective ?_⟩
    ext i
    simpa [map, Basis.equivFunL, Basis.equivFun_apply] using hz i
noncomputable def equiv (b:Basis ι ℝ E) :
    (ι → ℤ) ≃ Submodule.span ℤ (Set.range b) :=
  (Equiv.ofInjective (map b) (map_injective b)).trans
    (Equiv.setCongr (range_map b))
lemma zni (b:Basis ι ℝ E) (S:Set E) :
    Nat.card {z:ι → ℤ | map b z ∈ S} =
      Nat.card {x:Submodule.span ℤ (Set.range b) | (x:E) ∈ S}:=by
  exact Nat.card_congr ((equiv b).subtypeEquiv (fun _ => Iff.rfl))
end z71
namespace z2d
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical Pointwise
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
lemma zfj {t:ℝ} (ht:0 < t) (x:mixedSpace K) :
    x ∈ t • normLeOne K ↔
      x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ Module.finrank ℚ K:=by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero ht.ne'), mixedEmbedding.norm_smul,
    abs_of_pos (inv_pos.mpr ht), inv_pow]
  congr 1
  rw [← div_eq_inv_mul, div_le_iff₀ (pow_pos ht _), one_mul]
lemma zd9 (n:ℕ) (e:Fin (n+1) ≃ InfinitePlace K)
    (b:(Fin (n+1) → ℝ) ≃L[ℝ] mixedSpace K) :
    ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t →
      |(Nat.card {z:Fin (n+1) → ℤ | b (fun i => (z i:ℝ)) ∈ t • normLeOne K}:ℝ)-
        t^(n+1)*volume.real (b ⁻¹' normLeOne K)| ≤ C*t^n:=by
  let b':=b.trans (equiv K).symm
  have hpre:b' ⁻¹' z1l.region K = b ⁻¹' normLeOne K:=by
    rw [← z9e]
    ext x
    change equiv K ((equiv K).symm (b x)) ∈ normLeOne K ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hmem (t:ℝ) (x:Fin (n+1) → ℝ) :
      b' x ∈ t • z1l.region K ↔ b x ∈ t • normLeOne K:=by
    rw [← z9e]
    constructor
    · rintro ⟨y,hy,h⟩
      refine ⟨equiv K y,hy,?_⟩
      have hh:=congrArg (equiv K) h
      simpa [b',map_smul] using hh
    · rintro ⟨y,hy,h⟩
      refine ⟨(equiv K).symm y,?_,?_⟩
      · change equiv K ((equiv K).symm y) ∈ normLeOne K
        rwa [ContinuousLinearEquiv.apply_symm_apply]
      · simpa [b',map_smul] using congrArg (equiv K).symm h
  obtain ⟨C,hC,h⟩:=z1l.zbq K n e b'
  refine ⟨C,hC,?_⟩
  intro t ht
  simpa only [hpre,hmem] using h t ht
lemma zdq (n:ℕ) (e:Fin (n+1) ≃ InfinitePlace K)
    (b:Module.Basis (Fin (n+1)) ℝ (mixedSpace K)) :
    ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t →
      |(Nat.card {x:Submodule.span ℤ (Set.range b) | (x:mixedSpace K) ∈ t • normLeOne K}:ℝ)-
        t^(n+1)*volume.real (b.equivFunL.symm ⁻¹' normLeOne K)| ≤ C*t^n:=by
  obtain ⟨C,hC,h⟩:=zd9 K n e b.equivFunL.symm
  refine ⟨C,hC,?_⟩
  intro t ht
  simpa only [← z71.zni, z71.map] using h t ht
end z2d
namespace z2d
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory Module
open scoped Classical Pointwise nonZeroDivisors
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
lemma zlv:Fintype.card (InfinitePlace K) = Module.finrank ℚ K:=by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  simpa only [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] using
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
lemma zcl (J:(Ideal (𝓞 K))⁰) {t:ℝ} (ht:0 < t) :
    Nat.card {x:idealLattice K (FractionalIdeal.mk0 K J) | (x:mixedSpace K) ∈ t • normLeOne K} =
      Nat.card {a:idealSet K J | mixedEmbedding.norm (a:mixedSpace K) ≤ t^Module.finrank ℚ K}:=by
  have hset:{x:mixedSpace K | x ∈ idealLattice K (FractionalIdeal.mk0 K J) ∧
      x ∈ t • normLeOne K} =
      {x:mixedSpace K | x ∈ idealSet K J ∧ mixedEmbedding.norm x ≤ t^Module.finrank ℚ K}:=by
    ext x
    simp only [Set.mem_setOf_eq, zfj K ht, mem_idealSet,
      mem_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨⟨y,⟨a,ha,rfl⟩,hy⟩,hx,hn⟩
      exact ⟨⟨hx,a,ha,hy⟩,hn⟩
    · rintro ⟨⟨hx,a,ha,hy⟩,hn⟩
      exact ⟨⟨(a:K),⟨a,ha,rfl⟩,hy⟩,hx,hn⟩
  exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    ((Equiv.setCongr hset).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm))
lemma zb0 (n:ℕ) (hd:Module.finrank ℚ K = n+1)
    (J:(Ideal (𝓞 K))⁰) :
    ∃ A:ℝ, ∃ C > (0:ℝ), ∀ t:ℝ, 1 ≤ t →
      |(Nat.card {a:idealSet K J | mixedEmbedding.norm (a:mixedSpace K) ≤ t^(n+1)}:ℝ)-
        t^(n+1)*A| ≤ C*t^n:=by
  let b₀:=fractionalIdealLatticeBasis K (FractionalIdeal.mk0 K J)
  let f:Free.ChooseBasisIndex ℤ ((FractionalIdeal.mk0 K J):FractionalIdeal (𝓞 K)⁰ K) ≃ Fin (n+1) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, ← finrank_eq_card_basis b₀,
      mixedEmbedding.finrank,hd])
  let b:=b₀.reindex f
  have hspan:Submodule.span ℤ (Set.range b) = idealLattice K (FractionalIdeal.mk0 K J):=by
    rw [show Set.range b = Set.range b₀ by
      simpa only [b, Basis.coe_reindex] using f.symm.surjective.range_comp (b₀:_ → mixedSpace K)]
    exact span_idealLatticeBasis K _
  let e:Fin (n+1) ≃ InfinitePlace K :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,zlv K,hd])
  obtain ⟨C,hC,h⟩:=zdq K n e b
  refine ⟨volume.real (b.equivFunL.symm ⁻¹' normLeOne K),C,hC,?_⟩
  intro t ht
  have hh:=h t ht
  rw [hspan,zcl K J (lt_of_lt_of_le zero_lt_one ht),hd] at hh
  exact hh
end z2d
namespace z51
open Filter Topology
lemma zjr (f:ℝ → ℝ) (n:ℕ) (a b C k:ℝ) (ha:0 < a)
    (hf:Tendsto (fun x => f x/x) atTop (𝓝 k))
    (hbound:∀ t:ℝ, 1 ≤ t → |f (a*t^(n+1))-b*t^(n+1)| ≤ C*t^n):b = a*k:=by
  have hp:Tendsto (fun t:ℝ => t^(n+1)) atTop atTop:=tendsto_pow_atTop (by omega)
  have harg:Tendsto (fun t:ℝ => a*t^(n+1)) atTop atTop:=hp.const_mul_atTop ha
  have hratio:Tendsto (fun t:ℝ => f (a*t^(n+1))/t^(n+1)) atTop (𝓝 (a*k)):=by
    apply ((hf.comp harg).const_mul a).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp
    field_simp
  have herror:Tendsto (fun t:ℝ => |f (a*t^(n+1))/t^(n+1)-b|) atTop (𝓝 0):=by
    have hlim:Tendsto (fun t:ℝ => C/t) atTop (𝓝 0):=by
      have hh:=(tendsto_inv_atTop_zero:Tendsto (fun t:ℝ => t⁻¹) atTop (𝓝 0)).const_mul C
      simpa only [div_eq_mul_inv,mul_zero] using hh
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g:=fun t:ℝ => C/t) ?_ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0:0 < t:=lt_of_lt_of_le zero_lt_one ht
    calc
      _ = |f (a*t^(n+1))-b*t^(n+1)| / t^(n+1):=by
        calc
          _ = |(f (a*t^(n+1))-b*t^(n+1))/t^(n+1)|:=by
            congr 1
            field_simp
          _ = _:=by rw [abs_div,abs_of_pos (pow_pos ht0 _)]
      _ ≤ C*t^n/t^(n+1):=div_le_div_of_nonneg_right (hbound t ht) (pow_nonneg ht0.le _)
      _ = C/t:=by rw [pow_succ]; field_simp
  have hb:Tendsto (fun t:ℝ => f (a*t^(n+1))/t^(n+1)) atTop (𝓝 b):=by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using herror)
  exact tendsto_nhds_unique hb hratio
lemma zgn (f:ℝ → ℝ) (n:ℕ) (a C k:ℝ) (ha:0 < a)
    (hbound:∀ t:ℝ, 1 ≤ t → |f (a*t^(n+1))-k*(a*t^(n+1))| ≤ C*t^n)
    (x:ℝ) (hx:a ≤ x) :
    |f x-k*x| ≤ (C/a^((n:ℝ)/(n+1)))*x^((n:ℝ)/(n+1)):=by
  have hx0:0 < x:=ha.trans_le hx
  let t:=(x/a)^((n+1:ℕ):ℝ)⁻¹
  have ht:1 ≤ t:=Real.one_le_rpow ((le_div_iff₀ ha).mpr (by simpa using hx)) (by positivity)
  have htd:t^(n+1) = x/a:=Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have he:a*t^(n+1) = x:=by rw [htd]; field_simp
  have htn:t^n = (x/a)^((n:ℝ)/(n+1)):=by
    rw [show t^n = t^(n:ℝ) from (Real.rpow_natCast t n).symm]
    dsimp [t]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hh:=hbound t ht
  rw [he,htn,Real.div_rpow hx0.le ha.le] at hh
  convert hh using 1 <;> ring
end z51
namespace z1c
open NumberField Ideal Module Filter Topology
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open scoped Classical nonZeroDivisors Real
variable (K:Type*) [Field K] [NumberField K]
noncomputable def count (c:ClassGroup (𝓞 K)) (s:ℝ):ℕ :=
  Nat.card {I:(Ideal (𝓞 K))⁰ // (absNorm (I:Ideal (𝓞 K)):ℝ) ≤ s ∧ ClassGroup.mk0 I = c}
noncomputable def z1p:ℝ :=
  (2 ^ InfinitePlace.nrRealPlaces K * (2 * π) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K) /
    (Units.torsionOrder K * Real.sqrt |NumberField.discr K|)
lemma zfu {c:ClassGroup (𝓞 K)} {J:(Ideal (𝓞 K))⁰}
    (hJ:ClassGroup.mk0 J = c⁻¹) (s:ℝ) :
    count K c s = Nat.card {I:(Ideal (𝓞 K))⁰ // (J:Ideal (𝓞 K)) ∣ I ∧
      Submodule.IsPrincipal (I:Ideal (𝓞 K)) ∧ (absNorm (I:Ideal (𝓞 K)):ℝ) ≤ s*absNorm (J:Ideal (𝓞 K))}:=by
  unfold count
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I:(Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm
lemma zfg [IsTotallyReal K] (n:ℕ) (hd:finrank ℚ K = n+1)
    (c:ClassGroup (𝓞 K)) :
    ∃ D > (0:ℝ), ∀ᶠ s:ℝ in atTop,
      |(count K c s:ℝ)-z1p K*s| ≤ D*s^((n:ℝ)/(n+1)):=by
  obtain ⟨J,hJ⟩:=ClassGroup.mk0_surjective c⁻¹
  let N:ℝ:=absNorm (J:Ideal (𝓞 K))
  let w:ℝ:=Units.torsionOrder K
  have hN:0 < N:=Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)
  have hw:0 < w:=Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Units.torsionOrder_ne_zero K))
  let a:=N⁻¹
  have ha:0 < a:=inv_pos.mpr hN
  have hcard (t:ℝ) :
      Nat.card {x:idealSet K J | mixedEmbedding.norm (x:mixedSpace K) ≤ t^(n+1)} =
        count K c (a*t^(n+1)) * Units.torsionOrder K:=by
    change Nat.card {x:idealSet K J // mixedEmbedding.norm (x:mixedSpace K) ≤ t^(n+1)} = _
    rw [← card_isPrincipal_dvd_norm_le K J, zfu K hJ]
    congr 1
    have he:a*t^(n+1)*(absNorm (J:Ideal (𝓞 K)):ℝ) = t^(n+1):=by
      change N⁻¹*t^(n+1)*N = _
      field_simp
    rw [he]
  obtain ⟨A,C,hC,h⟩:=z2d.zb0 K n hd J
  let f:ℝ → ℝ:=fun s => count K c s
  have hb:∀ t:ℝ, 1 ≤ t → |f (a*t^(n+1))-(A/w)*t^(n+1)| ≤ (C/w)*t^n:=by
    intro t ht
    have hh:=h t ht
    rw [hcard,Nat.cast_mul] at hh
    apply (mul_le_mul_iff_right₀ hw).mp
    calc
      w*|f (a*t^(n+1))-(A/w)*t^(n+1)| = |f (a*t^(n+1))*w-t^(n+1)*A|:=by
        calc
          _ = |w*(f (a*t^(n+1))-(A/w)*t^(n+1))|:=by rw [abs_mul,abs_of_pos hw]
          _ = _:=by congr 1; field_simp
      _ ≤ C*t^n:=hh
      _ = w*((C/w)*t^n):=by field_simp
  have hcoef:A/w = a*z1p K:=z51.zjr f n a (A/w) (C/w)
    (z1p K) ha (NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c) hb
  have hb':∀ t:ℝ, 1 ≤ t → |f (a*t^(n+1))-z1p K*(a*t^(n+1))| ≤ (C/w)*t^n:=by
    intro t ht
    have hh:=hb t ht
    rw [hcoef] at hh
    convert hh using 1 <;> ring
  refine ⟨(C/w)/a^((n:ℝ)/(n+1)),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop a] with s hs
  exact z51.zgn f n a (C/w) (z1p K) ha hb' s hs
lemma z97 [IsTotallyReal K] (n:ℕ) (hd:finrank ℚ K = n+1)
    (χ:ClassGroup (𝓞 K) → ℝ) (hχ:∑ c, χ c = 0) :
    ∃ D > (0:ℝ), ∀ᶠ s:ℝ in atTop,
      |∑ c, χ c*(count K c s:ℝ)| ≤ D*s^((n:ℝ)/(n+1)):=by
  have h:=fun c => zfg K n hd c
  choose D hD hbound using h
  let C:=∑ c, |χ c| *D c
  have hC:0 ≤ C:=Finset.sum_nonneg (fun c _ => mul_nonneg (abs_nonneg _) (hD c).le)
  refine ⟨C+1,by positivity,?_⟩
  have hevent:∀ᶠ s:ℝ in atTop, ∀ c, |(count K c s:ℝ)-z1p K*s| ≤ D c*s^((n:ℝ)/(n+1)) :=
    Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_ge_atTop (0:ℝ)] with s hs hs0
  have he:(∑ c, χ c*((count K c s:ℝ)-z1p K*s)) =
      ∑ c, χ c*(count K c s:ℝ):=by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hχ,zero_mul,sub_zero]
  rw [← he]
  calc
    _ ≤ ∑ c, |χ c*((count K c s:ℝ)-z1p K*s)|:=Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, |χ c| *(D c*s^((n:ℝ)/(n+1))):=by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs c) (abs_nonneg _)
    _ = C*s^((n:ℝ)/(n+1)):=by dsimp [C]; simp only [Finset.sum_mul,mul_assoc]
    _ ≤ (C+1)*s^((n:ℝ)/(n+1)):=by gcongr; linarith
end z1c

namespace z3p
open scoped Classical BigOperators
structure Data (α:Type*) where
  norm:α → ℕ
  pos:∀ x, 0 < norm x
  finite_le:∀ N, {x | norm x ≤ N}.Finite
namespace Data
variable {α:Type*} (D:Data α)
noncomputable def z4n (N:ℕ):Finset α:=(D.finite_le N).toFinset
@[simp] lemma zen (N:ℕ) (x:α):x ∈ D.z4n N ↔ D.norm x ≤ N :=
  Set.Finite.mem_toFinset _
noncomputable def fiber (N:ℕ):Finset α:=(D.z4n N).filter (fun x => D.norm x = N)
@[simp] lemma mem_fiber (N:ℕ) (x:α):x ∈ D.fiber N ↔ D.norm x = N:=by
  simp [fiber]
  exact fun h => h ▸ Nat.le_refl N
variable {M:Type*} [AddCommMonoid M]
noncomputable def coeff (W:α → M) (n:ℕ):M:=∑ x ∈ D.fiber n, W x
@[simp] lemma coeff_zero (W:α → M):D.coeff W 0 = 0:=by
  apply Finset.sum_eq_zero
  intro x hx
  exact ((D.pos x).ne' ((D.mem_fiber 0 x).mp hx)).elim
lemma z93 (W:α → M) (N:ℕ) :
    ∑ n ∈ Finset.Icc 1 N, D.coeff W n = ∑ x ∈ D.z4n N, W x:=by
  have hf (n:ℕ) (hn:n ∈ Finset.Icc 1 N) :
      D.fiber n = (D.z4n N).filter (fun x => D.norm x = n):=by
    ext x
    simp only [mem_fiber,Finset.mem_filter,zen]
    exact ⟨fun h => ⟨h ▸ (Finset.mem_Icc.mp hn).2,h⟩,And.right⟩
  simp_rw [coeff]
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun s:Finset α => ∑ x ∈ s, W x) (hf n hn))]
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_Icc.mpr
    ⟨D.pos x,(D.zen N x).mp hx⟩) W
lemma z6j {E:Type*} [SeminormedAddCommGroup E] (W:α → E) (N:ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖D.coeff W n‖ ≤ ∑ x ∈ D.z4n N, ‖W x‖:=by
  rw [← D.z93 (fun x => ‖W x‖) N]
  apply Finset.sum_le_sum
  intro n _
  exact norm_sum_le _ _
lemma zk3 {β:Type*} [Fintype β] (cl:α → β) (χ:β → ℝ) (N:ℕ) :
    ∑ x ∈ D.z4n N, χ (cl x) =
      ∑ c, χ c*(Nat.card {x:α // D.norm x ≤ N ∧ cl x = c}:ℝ):=by
  rw [← Finset.sum_fiberwise (D.z4n N) cl (fun x => χ (cl x))]
  apply Finset.sum_congr rfl
  intro c _
  have hc:Nat.card {x:α // D.norm x ≤ N ∧ cl x = c} =
      ((D.z4n N).filter (fun x => cl x = c)).card:=by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.setCongr (by ext x; simp; rfl))
  rw [hc]
  calc
    _ = ∑ x ∈ (D.z4n N).filter (fun x => cl x = c), χ c :=
      Finset.sum_congr rfl (fun x hx => congrArg χ (Finset.mem_filter.mp hx).2)
    _ = _:=by simp [mul_comm]
end Data
end z3p
namespace z6e
open Filter Topology MeasureTheory Asymptotics Finset
lemma zlk {E:Type*} [NormedAddCommGroup E] (S:ℕ → E) (q C:ℝ)
    (hq:0 ≤ q) (hC:0 < C)
    (h:∀ᶠ n:ℕ in atTop, ‖S n‖ ≤ C*(n:ℝ)^q) :
    ∃ D > (0:ℝ), ∀ n:ℕ, 1 ≤ n → ‖S n‖ ≤ D*(n:ℝ)^q:=by
  obtain ⟨N,hN⟩:=eventually_atTop.mp h
  let B:=∑ k ∈ Finset.range N, ‖S k‖
  have hB:0 ≤ B:=Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C+B+1,by positivity,?_⟩
  intro n hn
  have hpow:1 ≤ (n:ℝ)^q:=Real.one_le_rpow (by exact_mod_cast hn) hq
  by_cases hnN:N ≤ n
  · calc
      _ ≤ C*(n:ℝ)^q:=hN n hnN
      _ ≤ (C+B+1)*(n:ℝ)^q:=by gcongr; linarith
  · have hh:‖S n‖ ≤ B:=Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ B:=hh
      _ ≤ (C+B+1)*(n:ℝ)^q:=by nlinarith
lemma norm_le (f:ℕ → ℂ) (q C:ℝ) (hq0:0 ≤ q) (hq:q < 1) (hC:0 ≤ C)
    (hbound:∀ n:ℕ, 1 ≤ n → ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C*(n:ℝ)^q)
    (s:ℝ) (hs:1 < s) (hs2:s ≤ 2) (hconv:LSeriesSummable f (s:ℂ)) :
    ‖LSeries f (s:ℂ)‖ ≤ 2*C/(1-q):=by
  have hqpos:0 < 1-q:=sub_pos.mpr hq
  have hO:(fun n:ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] (fun n:ℕ => (n:ℝ)^q):=by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) q)] using hbound n hn
  rw [LSeries_eq_mul_integral f hq0 (by simpa using hq.trans hs) hconv hO,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hs)]
  have hmajor:IntegrableOn (fun t:ℝ => C*t^(q-2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith:q-2 < -1) zero_lt_one).const_mul C
  have hint:‖∫ t in Set.Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) *
      (t:ℂ)^(-((s:ℂ)+1))‖ ≤ ∫ t in Set.Ioi (1:ℝ), C*t^(q-2):=by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1:1 ≤ t:=ht.le
    have ht0:0 < t:=zero_lt_one.trans ht
    have hn:1 ≤ ⌊t⌋₊:=(Nat.le_floor_iff ht0.le).mpr (by simpa using ht1)
    have hp:‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ C*t^q :=
      (hbound _ hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le) hq0) hC)
    have hc:‖(t:ℂ)^(-((s:ℂ)+1))‖ = t^(-s-1):=by
      rw [show -((s:ℂ)+1) = ((-s-1:ℝ):ℂ) by push_cast; ring,Complex.norm_cpow_real]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
    rw [norm_mul,hc]
    calc
      _ ≤ (C*t^q)*t^(-s-1):=mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg ht0.le _)
      _ = C*t^(q+(-s-1)):=by rw [Real.rpow_add ht0]; ring
      _ ≤ C*t^(q-2):=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hC
  have he:(∫ t in Set.Ioi (1:ℝ), C*t^(q-2)) = C/(1-q):=by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith:q-2 < -1) zero_lt_one,Real.one_rpow]
    rw [show q-2+1 = -(1-q) by ring,div_neg,neg_div,neg_neg]
    ring
  rw [he] at hint
  calc
    _ ≤ s*(C/(1-q)):=mul_le_mul_of_nonneg_left hint (le_of_lt (lt_trans zero_lt_one hs))
    _ ≤ 2*(C/(1-q)):=mul_le_mul_of_nonneg_right hs2 (by positivity)
    _ = _:=by ring
end z6e
namespace z8
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K:Type*) [Field K] [NumberField K]
noncomputable def data:z3p.Data (Ideal (𝓞 K))⁰ where
  norm I:=absNorm (I:Ideal (𝓞 K))
  pos I:=absNorm_pos_of_nonZeroDivisors I
  finite_le:=finite_setOf_absNorm_le₀
noncomputable def coeff (χ:ClassGroup (𝓞 K) → ℝ) (n:ℕ):ℝ :=
  (data K).coeff (fun I => χ (ClassGroup.mk0 I)) n
lemma z93 (χ:ClassGroup (𝓞 K) → ℝ) (N:ℕ) :
    ∑ n ∈ Finset.Icc 1 N, coeff K χ n =
      ∑ c, χ c*(z1c.count K c N:ℝ):=by
  unfold coeff
  rw [z3p.Data.z93,z3p.Data.zk3]
  congr 1
  ext c
  congr 2
  simp only [z1c.count,data,Nat.cast_le]
lemma z6j (χ:ClassGroup (𝓞 K) → ℝ) (N:ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖(coeff K χ n:ℂ)‖ ≤
      ∑ c, |χ c| *(z1c.count K c N:ℝ):=by
  have h:=(data K).z6j (fun I => χ (ClassGroup.mk0 I)) N
  have he:=(data K).zk3 ClassGroup.mk0 (fun c => |χ c|) N
  simp only [Real.norm_eq_abs] at h
  rw [he] at h
  simpa only [coeff,Complex.norm_real,Real.norm_eq_abs,z1c.count,data,Nat.cast_le] using h
lemma summable (χ:ClassGroup (𝓞 K) → ℝ) {s:ℂ} (hs:1 < s.re) :
    LSeriesSummable (fun n => (coeff K χ n:ℂ)) s:=by
  let B:ℕ → ℝ:=fun n => ∑ c, |χ c| *(z1c.count K c n:ℝ)
  have hB0 (n:ℕ):0 ≤ B n:=Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hlim:Tendsto (fun n:ℕ => B n/(n:ℝ)) atTop
      (𝓝 (∑ c, |χ c| *z1c.z1p K)):=by
    have hh:=tendsto_finset_sum Finset.univ (fun c _ =>
      ((NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c).comp
        tendsto_natCast_atTop_atTop).const_mul |χ c|)
    simpa only [B,z1c.count,z1c.z1p,
      Finset.sum_div,mul_div_assoc,Function.comp_apply] using hh
  have hBO:B =O[atTop] (fun n:ℕ => (n:ℝ)^(1:ℝ)) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa only [Real.rpow_one,RCLike.ofReal_real_eq_id,id] using hlim)
  have hO:(fun n:ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(coeff K χ k:ℂ)‖) =O[atTop] B:=by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun n => by
      simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (hB0 n),
        abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] using z6j K χ n)
  exact LSeriesSummable_of_sum_norm_bigO (hO.trans hBO) (by norm_num) hs
lemma zhy [IsTotallyReal K] (n:ℕ) (hd:finrank ℚ K = n+1)
    (χ:ClassGroup (𝓞 K) → ℝ) (hχ:∑ c, χ c = 0) :
    ∃ B > (0:ℝ), ∀ s:ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun k => (coeff K χ k:ℂ)) (s:ℂ)‖ ≤ B:=by
  let q:ℝ:=(n:ℝ)/(n+1)
  have hq0:0 ≤ q:=by dsimp [q]; positivity
  have hq:q < 1:=by dsimp [q]; apply (div_lt_one (by positivity)).mpr; linarith
  obtain ⟨C,hC,h⟩:=z1c.z97 K n hd χ hχ
  have hn:∀ᶠ N:ℕ in atTop,
      ‖∑ k ∈ Finset.Icc 1 N, (coeff K χ k:ℂ)‖ ≤ C*(N:ℝ)^q:=by
    have hh:=(tendsto_natCast_atTop_atTop:Tendsto (fun N:ℕ => (N:ℝ)) atTop atTop).eventually h
    filter_upwards [hh] with N hN
    simpa only [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,z93] using hN
  obtain ⟨D,hD,hbound⟩:=z6e.zlk
    (fun N => ∑ k ∈ Finset.Icc 1 N, (coeff K χ k:ℂ)) q C hq0 hC hn
  have hp:0 < 1-q:=sub_pos.mpr hq
  refine ⟨2*D/(1-q),by positivity,?_⟩
  intro s hs hs2
  exact z6e.norm_le _ q D hq0 hq hD.le hbound s hs hs2
    (summable K χ (by simpa using hs))
end z8
namespace z3p.Data
open scoped Classical BigOperators
variable {α:Type*} (D:z3p.Data α)
lemma ziq (W:α → ℝ) (n:ℕ) :
    (∑' x:{x:α // D.norm x = n}, W x.1) = D.coeff W n:=by
  let e:{x:α // x ∈ D.fiber n} ≃ {x:α // D.norm x = n} :=
    Equiv.subtypeEquivRight (fun x => D.mem_fiber n x)
  rw [← e.tsum_eq (fun x => W x.1)]
  change (∑' x:{x:α // x ∈ D.fiber n}, W x.1) = _
  exact Finset.tsum_subtype (D.fiber n) W
lemma zg5 (W:α → ℝ) (hW:∀ x, 0 ≤ W x) :
    Summable W ↔ Summable (D.coeff W):=by
  have hpart:∀ x:α, ∃! n:ℕ, x ∈ {x:α | D.norm x = n} :=
    fun x => ⟨D.norm x,rfl,fun n hn => hn.symm⟩
  have hfinite (n:ℕ):Summable (fun x:{x:α // D.norm x = n} => W x.1):=by
    have hfin:{x:α | D.norm x = n}.Finite:=(D.finite_le n).subset (fun x hx => hx.le)
    exact hfin.summable W
  rw [summable_partition hW hpart]
  change ((∀ n, Summable (fun x:{x:α // D.norm x = n} => W x.1)) ∧
    Summable (fun n => ∑' x:{x:α // D.norm x = n}, W x.1)) ↔ _
  simp only [D.ziq]
  exact and_iff_right hfinite
lemma zml (W:α → ℝ) (hW:Summable W) :
    (∑' n, D.coeff W n) = ∑' x, W x:=by
  let e:=Equiv.sigmaFiberEquiv D.norm
  have hs:=e.summable_iff.mpr hW
  calc
    _ = ∑' n, ∑' x:{x:α // D.norm x = n}, W x.1 :=
      tsum_congr (fun n => (D.ziq W n).symm)
    _ = ∑' p:(n:ℕ) × {x:α // D.norm x = n}, W p.2.1:=hs.tsum_sigma.symm
    _ = _:=e.tsum_eq W
lemma zjz (W:α → ℝ) (g:ℕ → ℝ) (n:ℕ) :
    D.coeff (fun x => W x*g (D.norm x)) n = D.coeff W n*g n:=by
  unfold coeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  change W x*g (D.norm x) = _
  rw [(D.mem_fiber n x).mp hx]
end z3p.Data
namespace zcg
lemma term_eq (f:ℕ → ℝ) (hf:f 0 = 0) (s:ℝ) (n:ℕ) :
    LSeries.term (fun k => (f k:ℂ)) (s:ℂ) n =
      ((f n*(n:ℝ)^(-s):ℝ):ℂ):=by
  rw [LSeries.term_def₀ (by simp only [hf,Complex.ofReal_zero])]
  simp only [Complex.ofReal_mul,Complex.ofReal_cpow (Nat.cast_nonneg n),Complex.ofReal_neg,
    Complex.ofReal_natCast]
lemma summable (f:ℕ → ℝ) (hf:f 0 = 0) (s:ℝ)
    (hs:LSeriesSummable (fun k => (f k:ℂ)) (s:ℂ)) :
    Summable (fun n => f n*(n:ℝ)^(-s)):=by
  unfold LSeriesSummable at hs
  change Summable (fun n => LSeries.term (fun k => (f k:ℂ)) (s:ℂ) n) at hs
  simpa only [term_eq f hf s,Complex.summable_ofReal] using hs
lemma znv (f:ℕ → ℝ) (hf:f 0 = 0) (s:ℝ) :
    LSeries (fun k => (f k:ℂ)) (s:ℂ) = ((∑' n, f n*(n:ℝ)^(-s):ℝ):ℂ):=by
  simp only [LSeries,term_eq f hf s,Complex.ofReal_tsum]
end zcg
namespace z89
open scoped Classical BigOperators
def Property (ι:Type*) [Fintype ι]:Prop :=
  ∀ f:ι → ℕ → ℝ, (∀ i, Summable (fun n => ‖f i n‖)) →
    Summable (fun z:ι → ℕ => ‖∏ i, f i (z i)‖) ∧
      HasSum (fun z:ι → ℕ => ∏ i, f i (z i)) (∏ i, ∑' n, f i n)
set_option maxHeartbeats 2000000 in
lemma zig (ι:Type*) [Fintype ι]:Property ι:=by
  refine Fintype.induction_empty_option (P:=Property) ?_ ?_ ?_ ι
  · intro α β _ e ih f hf
    letI:=Fintype.ofEquiv β e.symm
    have h:=ih (fun a => f (e a)) (fun a => hf (e a))
    let E:(β → ℕ) ≃ (α → ℕ):=Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he (z:β → ℕ):(∏ a, f (e a) (E z a)) = ∏ b, f b (z b):=by
      change (∏ a, f (e a) (z (e a))) = _
      exact e.prod_comp (fun b => f b (z b))
    constructor
    · simpa only [Function.comp_def,he] using E.summable_iff.mpr h.1
    · have hh:=E.hasSum_iff.mpr h.2
      have hc:=e.prod_comp (fun b => ∑' n, f b n)
      simpa only [Function.comp_def,he,hc] using hh
  · intro f hf
    constructor
    · exact summable_of_finite_support (Set.toFinite _)
    · simpa using hasSum_unique (fun z:PEmpty → ℕ => ∏ i, f i (z i))
  · intro α _ ih f hf
    have h:=ih (fun a => f (some a)) (fun a => hf (some a))
    let E:(Option α → ℕ) ≃ ℕ × (α → ℕ):=Equiv.piOptionEquivProd
    have he (z:Option α → ℕ) :
        f none (E z).1 * (∏ a, f (some a) ((E z).2 a)) = ∏ a, f a (z a):=by
      change f none (z none)*(∏ a, f (some a) (z (some a))) = _
      exact (Fintype.prod_option (fun a:Option α => f a (z a))).symm
    constructor
    · have hh:=(hf none).mul_norm h.1
      simpa only [Function.comp_def,he] using E.summable_iff.mpr hh
    · have hh:=(hf none).of_norm.hasSum.mul h.2 (summable_mul_of_summable_norm (hf none) h.1)
      have hh':=E.hasSum_iff.mpr hh
      simpa only [Function.comp_def,he,Fintype.prod_option] using hh'
end z89
namespace z9r
open scoped Classical BigOperators
open Filter Topology
variable {ι:Type*}
lemma zk7 [Fintype ι] (w:ι → ℝ) (m:Multiset ι) :
    (m.map w).prod = ∏ i, w i ^ m.count i:=by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,ih,Multiset.count_cons,pow_add,Finset.prod_mul_distrib]
    simp [mul_comm]
noncomputable def ze3 [Fintype ι]:Multiset ι ≃ (ι → ℕ) :=
  Multiset.toFinsupp.toEquiv.trans Finsupp.equivFunOnFinite
lemma zhn [Fintype ι] (m:Multiset ι) (i:ι):ze3 m i = m.count i:=by
  simp [ze3]
lemma zkv [Fintype ι] (w:ι → ℝ) (hw:∀ i, ‖w i‖ < 1) :
    HasSum (fun m:Multiset ι => (m.map w).prod) (∏ i, (1-w i)⁻¹):=by
  obtain ⟨_,hh⟩:=z89.zig ι (fun i n => w i ^ n)
    (fun i => by
      have hi:Summable (fun n:ℕ => ‖w i‖^n) :=
        summable_geometric_of_norm_lt_one (by simpa only [norm_norm] using hw i)
      simpa only [norm_pow] using hi)
  have he:=(ze3 (ι:=ι)).hasSum_iff.mpr hh
  simpa only [Function.comp_def,zhn,← zk7,
    tsum_geometric_of_norm_lt_one (hw _)] using he
lemma zd6 (s:Finset ι) (m:Multiset ι)
    (hm:∀ x ∈ m, x ∈ s) :
    m ∈ Set.range (Multiset.map (Subtype.val:s → ι)):=by
  lift m to Multiset s using hm with a ha
  exact ⟨a,rfl⟩
noncomputable def restricted (w:ι → ℝ) (s:Finset ι) (m:Multiset ι):ℝ :=
  if m ∈ Set.range (Multiset.map (Subtype.val:s → ι)) then (m.map w).prod else 0
lemma zh1 (w:ι → ℝ) (hw:∀ i, ‖w i‖ < 1) (s:Finset ι) :
    HasSum (restricted w s) (∏ i ∈ s, (1-w i)⁻¹):=by
  apply (Multiset.map_injective (f:=(Subtype.val:s → ι)) Subtype.val_injective).hasSum_iff
    (fun m hm => by simp [restricted,hm]) |>.mp
  have hh:=zkv (fun i:s => w i) (fun i => hw i)
  simpa only [Function.comp_def,restricted,Set.mem_range_self,if_true,Multiset.map_map,
    Finset.prod_coe_sort s (fun i => (1-w i)⁻¹)] using hh
lemma hasProd (w:ι → ℝ) (hw:∀ i, ‖w i‖ < 1)
    (hsum:Summable (fun m:Multiset ι => ‖(m.map w).prod‖)) :
    HasProd (fun i => (1-w i)⁻¹) (∑' m:Multiset ι, (m.map w).prod):=by
  have hpoint (m:Multiset ι):Tendsto (fun s:Finset ι => restricted w s m) atTop
      (𝓝 ((m.map w).prod)):=by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m.toFinset] with s hs
    have hm:m ∈ Set.range (Multiset.map (Subtype.val:s → ι)) :=
      zd6 s m (fun x hx => hs (Multiset.mem_toFinset.mpr hx))
    simp [restricted,hm]
  have hbound:∀ᶠ s:Finset ι in atTop, ∀ m:Multiset ι,
      ‖restricted w s m‖ ≤ ‖(m.map w).prod‖:=by
    apply Filter.Eventually.of_forall
    intro s m
    unfold restricted
    split_ifs <;> simp
  have hlim:=tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  change Tendsto (fun s:Finset ι => ∏ i ∈ s, (1-w i)⁻¹) atTop _
  simpa only [(zh1 w hw _).tsum_eq] using hlim
end z9r
namespace z1e
open UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors
variable {α:Type*} [CommMonoidWithZero α] [Nontrivial α] [IsCancelMulZero α] [UniqueFactorizationMonoid α]
  [NormalizationMonoid α] [Subsingleton αˣ]
noncomputable def factors (a:α):Multiset {p:α // Prime p} :=
  (normalizedFactors a).pmap (fun p hp => ⟨p,hp⟩) (fun p hp => prime_of_normalized_factor p hp)
@[simp] lemma zhd (a:α):(factors a).map Subtype.val = normalizedFactors a:=by
  rw [factors,Multiset.map_pmap,Multiset.pmap_eq_map]
  exact Multiset.map_id _
def prime (p:{p:α // Prime p}):α⁰ :=
  ⟨p.1,mem_nonZeroDivisors_iff_ne_zero.mpr p.property.ne_zero⟩
noncomputable def prod (m:Multiset {p:α // Prime p}):α⁰:=(m.map prime).prod
@[simp] lemma coe_prod (m:Multiset {p:α // Prime p}) :
    (prod m:α) = (m.map Subtype.val).prod:=by
  induction m using Multiset.induction_on with
  | empty => rfl
  | @cons p m ih =>
    simpa only [prod,Multiset.map_cons,Multiset.prod_cons,Submonoid.coe_mul,prime] using
      congrArg (p.1 * ·) ih
@[simp] lemma prod_factors (a:α⁰):prod (factors (a:α)) = a:=by
  apply Subtype.ext
  rw [coe_prod,zhd]
  simpa only [associated_eq_eq] using prod_normalizedFactors (nonZeroDivisors.coe_ne_zero a)
@[simp] lemma factors_prod (m:Multiset {p:α // Prime p}) :
    factors (prod m:α) = m:=by
  apply Multiset.map_injective (f:=Subtype.val) Subtype.val_injective
  rw [zhd,coe_prod]
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨q,hq,rfl⟩:=Multiset.mem_map.mp hp
  exact q.property
noncomputable def equiv:α⁰ ≃ Multiset {p:α // Prime p} where
  toFun a:=factors (a:α)
  invFun:=prod
  left_inv:=prod_factors
  right_inv:=factors_prod
lemma equiv_symm_apply (m:Multiset {p:α // Prime p}):(equiv (α:=α)).symm m = prod m:=rfl
@[simp] lemma map_prod {R:Type*} [CommMonoid R] (f:α⁰ →* R)
    (m:Multiset {p:α // Prime p}):f (prod m) = (m.map (fun p => f (prime p))).prod:=by
  rw [prod,← Multiset.prod_hom,Multiset.map_map]
  rfl
end z1e
namespace z1e
open scoped Classical nonZeroDivisors
variable {α:Type*} [CommMonoidWithZero α] [Nontrivial α] [IsCancelMulZero α]
  [UniqueFactorizationMonoid α] [NormalizationMonoid α] [Subsingleton αˣ]
lemma hasProd (f:α⁰ →* ℝ) (hf:Summable (fun a => ‖f a‖))
    (hp:∀ p:{p:α // Prime p}, ‖f (prime p)‖ < 1) :
    HasProd (fun p:{p:α // Prime p} => (1-f (prime p))⁻¹) (∑' a, f a):=by
  have hs:Summable (fun m:Multiset {p:α // Prime p} =>
      ‖(m.map (fun p => f (prime p))).prod‖):=by
    have hh:=(equiv (α:=α)).symm.summable_iff.mpr hf
    simpa only [Function.comp_def,equiv_symm_apply,map_prod] using hh
  have hh:=z9r.hasProd (fun p => f (prime p)) hp hs
  have he:(∑' m:Multiset {p:α // Prime p}, (m.map (fun p => f (prime p))).prod) = ∑' a, f a:=by
    simpa only [equiv_symm_apply,map_prod] using (equiv (α:=α)).symm.tsum_eq f
  rwa [he] at hh
end z1e
namespace z8
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K:Type*) [Field K] [NumberField K]
noncomputable def weight (χ:ClassGroup (𝓞 K) → ℝ) (s:ℝ) (I:(Ideal (𝓞 K))⁰):ℝ :=
  χ (ClassGroup.mk0 I) * (absNorm (I:Ideal (𝓞 K)):ℝ)^(-s)
@[simp] lemma coeff_zero (χ:ClassGroup (𝓞 K) → ℝ):coeff K χ 0 = 0 :=
  z3p.Data.coeff_zero _ _
lemma zg9 (χ:ClassGroup (𝓞 K) → ℝ) (s:ℝ) (n:ℕ) :
    (data K).coeff (weight K χ s) n = coeff K χ n * (n:ℝ)^(-s) :=
  (data K).zjz (fun I => χ (ClassGroup.mk0 I)) (fun n => (n:ℝ)^(-s)) n
lemma zc7 (χ:ClassGroup (𝓞 K) → ℝ) (hχ:∀ c, 0 ≤ χ c)
    (s:ℝ) (hs:1 < s):Summable (weight K χ s):=by
  apply ((data K).zg5 (weight K χ s) (fun I =>
    mul_nonneg (hχ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))).mpr
  have hh:=zcg.summable (coeff K χ) (coeff_zero K χ) s (summable K χ (by simpa using hs))
  change Summable (fun n => (data K).coeff (weight K χ s) n)
  simpa only [zg9] using hh
lemma z37 (χ:ClassGroup (𝓞 K) → ℝ) (s:ℝ) (hs:1 < s) :
    Summable (fun I => ‖weight K χ s I‖):=by
  have hh:=zc7 K (fun c => |χ c|) (fun _ => abs_nonneg _) s hs
  refine hh.congr (fun I => ?_)
  simp only [weight,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
lemma zae (χ:ClassGroup (𝓞 K) → ℝ) (s:ℝ) (hs:1 < s) :
    LSeries (fun k => (coeff K χ k:ℂ)) (s:ℂ) = ((∑' I, weight K χ s I:ℝ):ℂ):=by
  rw [zcg.znv _ (coeff_zero K χ)]
  congr 1
  have hh:=(data K).zml (weight K χ s) (z37 K χ s hs).of_norm
  simpa only [zg9] using hh
noncomputable def weightHom (χ:ClassGroup (𝓞 K) →* ℝ) (s:ℝ):(Ideal (𝓞 K))⁰ →* ℝ where
  toFun:=weight K χ s
  map_one':=by simp [weight]
  map_mul' I J:=by
    simp only [weight,map_mul,Submonoid.coe_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
lemma weightHom_apply (χ:ClassGroup (𝓞 K) →* ℝ) (s:ℝ) (I:(Ideal (𝓞 K))⁰) :
    weightHom K χ s I = weight K χ s I:=rfl
lemma zjp (χ:ClassGroup (𝓞 K) →* ℝ) (c:ClassGroup (𝓞 K)):‖χ c‖ = 1 :=
  (χ.isOfFinOrder (isOfFinOrder_of_finite c)).norm_eq_one
lemma zac (p:{p:Ideal (𝓞 K) // Prime p}):1 < absNorm p.1:=by
  have hp:0 < absNorm p.1:=absNorm_pos_of_nonZeroDivisors (S:=𝓞 K) (z1e.prime p)
  have hn:absNorm p.1 ≠ 1:=by
    intro h
    apply p.property.2.1
    rw [absNorm_eq_one_iff.mp h]
    rw [← Ideal.one_eq_top]
    exact isUnit_one
  change 0 < absNorm p.1 at hp
  omega
lemma zb4 (χ:ClassGroup (𝓞 K) →* ℝ) (s:ℝ) (hs:0 < s)
    (p:{p:Ideal (𝓞 K) // Prime p}) :
    ‖weightHom K χ s (z1e.prime p)‖ < 1:=by
  change ‖χ (ClassGroup.mk0 (z1e.prime p)) * (absNorm p.1:ℝ)^(-s)‖ < 1
  rw [norm_mul,zjp,one_mul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast zac K p) (neg_neg_of_pos hs)
lemma zed (χ:ClassGroup (𝓞 K) →* ℝ) (s:ℝ) (hs:1 < s) :
    HasProd (fun p:{p:Ideal (𝓞 K) // Prime p} =>
      (1-weight K χ s (z1e.prime p))⁻¹) (∑' I, weight K χ s I):=by
  exact z1e.hasProd (weightHom K χ s) (z37 K χ s hs)
    (zb4 K χ s (zero_lt_one.trans hs))
end z8
namespace z8
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K:Type*) [Field K] [NumberField K]
lemma zge (χ:ClassGroup (𝓞 K) → ℝ) :
    Tendsto (fun N:ℕ => (∑ k ∈ Finset.Icc 1 N, coeff K χ k)/(N:ℝ)) atTop
      (𝓝 (∑ c, χ c*z1c.z1p K)):=by
  have hh:=tendsto_finset_sum Finset.univ (fun c _ =>
    ((NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c).comp
      tendsto_natCast_atTop_atTop).const_mul (χ c))
  simpa only [z93,z1c.count,z1c.z1p,
    Finset.sum_div,mul_div_assoc,Function.comp_apply] using hh
noncomputable def zeta (s:ℝ):ℝ:=∑' I, weight K (fun _ => 1) s I
noncomputable def residue:ℝ:=(Fintype.card (ClassGroup (𝓞 K)):ℝ)*z1c.z1p K
lemma zev:0 < z1c.z1p K:=by
  have hreg:=Units.regulator_pos K
  have htor:(0:ℝ) < Units.torsionOrder K:=Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hd:(NumberField.discr K:ℝ) ≠ 0:=Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  unfold z1c.z1p
  positivity
lemma zm0:0 < residue K:=by
  unfold residue
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (zev K)
lemma zfh:Tendsto (fun s:ℝ => (s-1)*zeta K s)
    (𝓝[Set.Ioi 1] 1) (𝓝 (residue K)):=by
  have hlim:=(zge K (fun _ => 1)).ofReal
  have hlim':Tendsto (fun N:ℕ => (∑ k ∈ Finset.Icc 1 N, (coeff K (fun _ => 1) k:ℂ))/(N:ℂ))
      atTop (𝓝 ((residue K:ℝ):ℂ)):=by
    simpa only [Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,one_mul,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,residue] using hlim
  have hh:=LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div hlim'
    (fun s hs => summable K (fun _ => 1) (by simpa using hs))
  have hr:=(Complex.continuous_re.tendsto _).comp hh
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp only [Function.comp_apply]
  rw [zae K _ s hs]
  change (((s:ℂ)-1)*((zeta K s:ℝ):ℂ)).re = _
  simp
end z8
namespace z1b
open scoped Classical BigOperators
variable (G:Type*) [CommGroup G] [Fintype G]
variable (hs:∀ g:G, g^2 = 1)
abbrev Index:=AddChar (Additive G) ℂ
include hs in
lemma ze6 (χ:Index G) (g:G) :
    χ (Additive.ofMul g) = 1 ∨ χ (Additive.ofMul g) = -1:=by
  apply mul_self_eq_one_iff.mp
  rw [← χ.map_add_eq_mul]
  have he:Additive.ofMul g + Additive.ofMul g = 0:=by
    change Additive.ofMul (g*g) = Additive.ofMul (1:G)
    exact congrArg Additive.ofMul (by simpa only [pow_two] using hs g)
  rw [he,χ.map_zero_eq_one]
include hs in
lemma ofReal_re (χ:Index G) (g:G) :
    ((χ (Additive.ofMul g)).re:ℂ) = χ (Additive.ofMul g):=by
  rcases ze6 G hs χ g with h | h <;> simp [h]
noncomputable def z2k (χ:Index G):G →* ℝ where
  toFun g:=(χ (Additive.ofMul g)).re
  map_one':=by change (χ 0).re = 1; simp
  map_mul' g h:=by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul,ofReal_re G hs,ofReal_re G hs,ofReal_re G hs]
    exact χ.map_add_eq_mul _ _
@[simp] lemma zel (χ:Index G) (g:G):z2k G hs χ g = (χ (Additive.ofMul g)).re:=rfl
@[simp] lemma zhg (g:G):z2k G hs 1 g = 1:=by simp
include hs in
lemma zgc (χ:Index G) (g:G):z2k G hs χ g = 1 ∨ z2k G hs χ g = -1:=by
  rcases ze6 G hs χ g with h | h <;> simp [h]
include hs in
lemma zm5 (χ ψ:Index G) (g:G) :
    z2k G hs (χ*ψ) g = z2k G hs χ g * z2k G hs ψ g:=by
  apply Complex.ofReal_injective
  simp only [zel,Complex.ofReal_mul]
  rw [ofReal_re G hs (χ*ψ) g,ofReal_re G hs χ g,ofReal_re G hs ψ g,AddChar.mul_apply]
include hs in
lemma exists_neg {g:G} (hg:g ≠ 1):∃ χ:Index G, z2k G hs χ g = -1:=by
  have hg':Additive.ofMul g ≠ 0:=hg
  obtain ⟨χ,hχ⟩:=AddChar.exists_apply_ne_zero.mpr hg'
  rcases ze6 G hs χ g with h | h
  · exact (hχ h).elim
  · exact ⟨χ,by simp [h]⟩
include hs in
lemma zh4:Function.Injective (z2k G hs):=by
  intro χ ψ h
  ext x
  have hh:=congrArg (fun f:G →* ℝ => ((f x.toMul:ℝ):ℂ)) h
  simp only [zel] at hh
  rw [ofReal_re G hs,ofReal_re G hs] at hh
  simpa only [ofMul_toMul] using hh
lemma zlm {H:Type*} [Group H] [Fintype H] (f:H →* ℝ) (hf:f ≠ 1) :
    ∑ h:H, f h = 0:=by
  obtain ⟨a,ha⟩:∃ a, f a ≠ 1:=by
    by_contra! h
    exact hf (DFunLike.ext _ _ h)
  have he:=Equiv.sum_comp (Equiv.mulLeft a) (fun h:H => f h)
  change (∑ h:H, f (a*h)) = ∑ h:H, f h at he
  simp only [map_mul,← Finset.mul_sum] at he
  have hz:(f a-1)*(∑ h:H, f h) = 0:=by nlinarith [he]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)
include hs in
lemma zh5 {H:Type*} [Group H] [Fintype H]
    (q:H →* G) (hq:Function.Surjective q) {χ:Index G} (hχ:χ ≠ 1) :
    ∑ h:H, z2k G hs χ (q h) = 0:=by
  apply zlm ((z2k G hs χ).comp q)
  intro hh
  apply hχ
  apply zh4 G hs
  ext g
  obtain ⟨h,rfl⟩:=hq g
  have he:=DFunLike.congr_fun hh h
  simpa only [MonoidHom.comp_apply,MonoidHom.one_apply,zhg] using he
@[simp] lemma zj6:Fintype.card (Index G) = Fintype.card G:=by
  rw [AddChar.card_eq]
  exact Fintype.card_congr Additive.toMul
end z1b
namespace z1b
open scoped Classical BigOperators
variable (G:Type*) [CommGroup G] [Fintype G]
variable (hs:∀ g:G, g^2 = 1)
noncomputable def z3c (g:G) (x:ℝ):ℝ :=
  ∏ χ:Index G, (1-z2k G hs χ g*x)⁻¹
lemma zgk (x:ℝ):z3c G hs 1 x = ((1-x)⁻¹)^Fintype.card G:=by
  simp only [z3c,map_one,one_mul,Finset.prod_const,Finset.card_univ,zj6]
lemma zh0 (g:G) {x:ℝ} (hx0:0 ≤ x) (hx:x < 1) :
    0 < z3c G hs g x:=by
  apply Finset.prod_pos
  intro χ _
  apply inv_pos.mpr
  rcases zgc G hs χ g with h | h
  · rw [h,one_mul]; linarith
  · rw [h,neg_one_mul]; linarith
lemma ze8 {g:G} (hg:g ≠ 1) {x:ℝ} (hx0:0 ≤ x) (hx:x < 1) :
    1 ≤ z3c G hs g x:=by
  obtain ⟨ψ,hψ⟩:=exists_neg G hs hg
  let P:=z3c G hs g x
  have hflip:(∏ χ:Index G, (1+z2k G hs χ g*x)⁻¹) = P:=by
    have hh:=Equiv.prod_comp (Equiv.mulRight ψ) (fun χ:Index G => (1-z2k G hs χ g*x)⁻¹)
    change (∏ χ:Index G, (1-z2k G hs (χ*ψ) g*x)⁻¹) = P at hh
    simpa only [zm5,hψ,mul_neg_one,neg_mul,sub_neg_eq_add] using hh
  have hp:P*P = ((1-x^2)⁻¹)^Fintype.card G:=by
    change z3c G hs g x*P = _
    rw [← hflip,z3c,← Finset.prod_mul_distrib]
    have he (χ:Index G):(1-z2k G hs χ g*x)⁻¹*(1+z2k G hs χ g*x)⁻¹ = (1-x^2)⁻¹:=by
      rw [← mul_inv]
      congr 1
      rcases zgc G hs χ g with h | h <;> rw [h] <;> ring
    simp only [he,Finset.prod_const,Finset.card_univ,zj6]
  have hb0:0 < 1-x^2:=by nlinarith
  have hb1:1 ≤ (1-x^2)⁻¹:=(one_le_inv₀ hb0).mpr (by nlinarith [sq_nonneg x])
  have hpow:1 ≤ ((1-x^2)⁻¹)^Fintype.card G:=one_le_pow₀ hb1
  have hP:0 < P:=zh0 G hs g hx0 hx
  rw [← hp] at hpow
  nlinarith
lemma zdl {P:Type*} (g:P → G) (x:P → ℝ)
    (s:Finset P) (hx0:∀ p ∈ s, 0 ≤ x p) (hx:∀ p ∈ s, x p < 1) :
    (∏ p ∈ s, if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G ≤
      ∏ χ:Index G, ∏ p ∈ s, (1-z2k G hs χ (g p)*x p)⁻¹:=by
  rw [← Finset.prod_pow,Finset.prod_comm]
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs
    · exact pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (hx p hp).le)) _
    · positivity
  · intro p hp
    change (if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G ≤ z3c G hs (g p) (x p)
    by_cases hg:g p = 1
    · rw [if_pos hg,hg,zgk]
    · rw [if_neg hg,one_pow]
      exact ze8 G hs hg (hx0 p hp) (hx p hp)
end z1b
namespace z2s
open Filter Topology
open scoped Classical BigOperators
variable {P:Type*}
lemma zjx (w x:P → ℝ) (h:∀ p, ‖w p‖ ≤ ‖x p‖) (m:Multiset P) :
    ‖(m.map w).prod‖ ≤ ‖(m.map x).prod‖:=by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons p m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
    exact mul_le_mul (h p) ih (norm_nonneg _) (norm_nonneg _)
variable (G:Type*) [CommGroup G] [Fintype G] (hs:∀ g:G, g^2 = 1)
noncomputable def value (g:P → G) (x:P → ℝ) (p:P):ℝ:=if g p = 1 then x p else (x p)^2
lemma z4d (g:P → G) (x:P → ℝ) (hx0:∀ p, 0 ≤ x p) (hx:∀ p, x p < 1) (p:P) :
    0 ≤ value G g x p ∧ value G g x p ≤ x p:=by
  unfold value
  split_ifs
  · exact ⟨hx0 p,le_rfl⟩
  · constructor
    · positivity
    · nlinarith [hx0 p,hx p]
lemma zji (g:P → G) (x:P → ℝ) (hx0:∀ p, 0 ≤ x p) (hx:∀ p, x p < 1)
    (hsum:Summable (fun m:Multiset P => ‖(m.map x).prod‖)) :
    ∃ a:ℝ, 1 ≤ a ∧ HasProd (fun p => (1-value G g x p)⁻¹) a:=by
  have hw0 (p:P):=(z4d G g x hx0 hx p).1
  have hw (p:P):value G g x p < 1:=(z4d G g x hx0 hx p).2.trans_lt (hx p)
  have hnorm (p:P):‖value G g x p‖ ≤ ‖x p‖:=by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hw0 p),abs_of_nonneg (hx0 p)] using
      (z4d G g x hx0 hx p).2
  have hsumw:Summable (fun m:Multiset P => ‖(m.map (value G g x)).prod‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (zjx _ _ hnorm) hsum
  have hp:=z9r.hasProd (value G g x)
    (fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hw0 p)] using hw p) hsumw
  refine ⟨_,?_,hp⟩
  apply ge_of_tendsto hp
  apply Filter.Eventually.of_forall
  intro s
  apply Finset.one_le_prod
  intro p _
  apply (one_le_inv₀ (sub_pos.mpr (hw p))).mpr
  linarith [hw0 p]
lemma zj1 (g:P → G) (x:P → ℝ) (hx0:∀ p, 0 ≤ x p) (hx:∀ p, x p < 1)
    (a z:ℝ) (L:z1b.Index G → ℝ)
    (ha:HasProd (fun p => (1-value G g x p)⁻¹) a)
    (hz:HasProd (fun p => (1-(x p)^2)⁻¹) z)
    (hL:∀ χ, HasProd (fun p => (1-z1b.z2k G hs χ (g p)*x p)⁻¹) (L χ)) :
    a^Fintype.card G ≤ z^Fintype.card G * ∏ χ, L χ:=by
  have hr:=Filter.Tendsto.mul (Filter.Tendsto.pow hz (Fintype.card G))
    (tendsto_finsetProd Finset.univ (fun χ _ => hL χ))
  apply le_of_tendsto_of_tendsto (Filter.Tendsto.pow ha (Fintype.card G)) hr
  apply Filter.Eventually.of_forall
  intro s
  have hsq0 (p:P):0 < 1-(x p)^2:=by nlinarith [hx0 p,hx p]
  have hsq1 (p:P):1 ≤ (1-(x p)^2)⁻¹:=(one_le_inv₀ (hsq0 p)).mpr (by nlinarith [sq_nonneg (x p)])
  have hsplit0 (p:P):0 ≤ (if g p = 1 then (1-x p)⁻¹ else 1):=by
    split_ifs
    · exact (inv_pos.mpr (sub_pos.mpr (hx p))).le
    · norm_num
  have hker (p:P):(1-value G g x p)⁻¹ ≤
      (1-(x p)^2)⁻¹*(if g p = 1 then (1-x p)⁻¹ else 1):=by
    unfold value
    split_ifs with h
    · exact le_mul_of_one_le_left (inv_nonneg.mpr (sub_nonneg.mpr (hx p).le)) (hsq1 p)
    · simp
  have hfinite:=z1b.zdl G hs g x s (fun p _ => hx0 p) (fun p _ => hx p)
  have hk0:0 ≤ ∏ p ∈ s, (1-value G g x p)⁻¹:=by
    apply Finset.prod_nonneg
    intro p _
    exact (inv_pos.mpr (sub_pos.mpr ((z4d G g x hx0 hx p).2.trans_lt (hx p)))).le
  calc
    _ ≤ (∏ p ∈ s, (1-(x p)^2)⁻¹*(if g p = 1 then (1-x p)⁻¹ else 1))^Fintype.card G:=by
      apply pow_le_pow_left₀ hk0
      exact Finset.prod_le_prod (fun p _ => (inv_pos.mpr
        (sub_pos.mpr ((z4d G g x hx0 hx p).2.trans_lt (hx p)))).le) (fun p _ => hker p)
    _ = (∏ p ∈ s, (1-(x p)^2)⁻¹)^Fintype.card G *
        (∏ p ∈ s, if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G:=by
      rw [Finset.prod_mul_distrib,mul_pow]
    _ ≤ _:=mul_le_mul_of_nonneg_left hfinite (pow_nonneg
      (Finset.prod_nonneg (fun p _ => (inv_pos.mpr (hsq0 p)).le)) _)
end z2s
namespace zfe
open Filter Topology
open scoped Classical BigOperators
variable {P Q:Type*}
lemma ze2 (A:P → ℝ) (hA:∀ p, 1 ≤ A p) (a:ℝ)
    (ha:HasProd A a) (s:Finset P):∏ p ∈ s, A p ≤ a:=by
  apply ge_of_tendsto ha
  filter_upwards [eventually_ge_atTop s] with t ht
  rw [← Finset.prod_sdiff ht]
  have hs:=Finset.one_le_prod (s:=s) (fun p _ => hA p)
  have hdiff:=Finset.one_le_prod (s:=t \ s) (fun p _ => hA p)
  nlinarith
lemma zmc (g:P → Q) (A:Q → ℝ) (B:P → ℝ) (d:ℕ)
    (hA:∀ q, 1 ≤ A q) (hB:∀ p, 0 ≤ B p) (hBA:∀ p, B p ≤ A (g p))
    (hfib:∀ s:Finset P, ∀ q:Q, (s.filter (fun p => g p = q)).card ≤ d)
    (a b:ℝ) (ha:HasProd A a) (hb:HasProd B b):b ≤ a^d:=by
  apply le_of_tendsto' hb
  intro s
  have hmid:(∏ p ∈ s, A (g p)) = ∏ q ∈ s.image g, A q ^ (s.filter (fun p => g p = q)).card:=by
    rw [← Finset.prod_fiberwise_of_maps_to (s:=s) (t:=s.image g) (g:=g) (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) (fun p => A (g p))]
    apply Finset.prod_congr rfl
    intro q hq
    calc
      _ = ∏ p ∈ s.filter (fun p => g p = q), A q :=
        Finset.prod_congr rfl (fun p hp => congrArg A (Finset.mem_filter.mp hp).2)
      _ = _:=Finset.prod_const _
  calc
    _ ≤ ∏ p ∈ s, A (g p):=Finset.prod_le_prod (fun p _ => hB p) (fun p _ => hBA p)
    _ = ∏ q ∈ s.image g, A q ^ (s.filter (fun p => g p = q)).card:=hmid
    _ ≤ ∏ q ∈ s.image g, A q^d:=Finset.prod_le_prod
      (fun q _ => pow_nonneg (zero_le_one.trans (hA q)) _)
      (fun q _ => pow_le_pow_right₀ (hA q) (hfib s q))
    _ = (∏ q ∈ s.image g, A q)^d:=Finset.prod_pow _ _ _
    _ ≤ a^d:=pow_le_pow_left₀ (Finset.prod_nonneg (fun q _ => zero_le_one.trans (hA q)))
      (ze2 A hA a ha _ ) _
end zfe
namespace z1r
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
noncomputable def z1j (F:Type*) [Field F] [NumberField F] (s:ℝ) (p:z14.Primes F):ℝ :=
  (absNorm p.1:ℝ)^(-s)
lemma z2l (F:Type*) [Field F] [NumberField F] (s:ℝ) (hs:0 < s)
    (p:z14.Primes F):0 ≤ z1j F s p ∧ z1j F s p < 1:=by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast z8.zac F p)
    (neg_neg_of_pos hs)
lemma zff (F:Type*) [Field F] [NumberField F] (s:ℝ) (hs:1 < s) :
    HasProd (fun p:z14.Primes F => (1-z1j F s p)⁻¹) (z8.zeta F s):=by
  simpa only [z8.weight,MonoidHom.one_apply,one_mul,z1j,z8.zeta,
    z1e.prime] using z8.zed F 1 s hs
lemma zgm (F:Type*) [Field F] [NumberField F] (s:ℝ) (hs:1 < s) :
    Summable (fun m:Multiset (z14.Primes F) => ‖(m.map (z1j F s)).prod‖):=by
  have hh:=(z1e.equiv (α:=Ideal (𝓞 F))).symm.summable_iff.mpr
    (z8.z37 F (fun _ => 1) s hs)
  have he (m:Multiset (z14.Primes F)) :
      z8.weight F (fun _ => 1) s (z1e.prod m) = (m.map (z1j F s)).prod:=by
    have h:=z1e.map_prod (z8.weightHom F 1 s) m
    simp only [z8.weightHom_apply,z8.weight,MonoidHom.one_apply,one_mul,
      z1e.prime] at h
    simp only [z8.weight,one_mul]
    rw [h]
    rfl
  simpa only [Function.comp_def,z1e.equiv_symm_apply,he] using hh
lemma zmv (P:z14.Primes E) :
    z14.norm K E (z1e.prime P) =
      (z1e.prime (z14.below K E P))^z14.degree K E P:=by
  apply Subtype.ext
  exact z14.relNorm_prime K E P
lemma zcs (s:ℝ) (P:z14.Primes E) :
    z1j E s P = (z1j K s (z14.below K E P))^z14.degree K E P:=by
  unfold z1j
  rw [z14.zkp K E P,Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _) _ _,
    mul_comm (z14.degree K E P:ℝ),Real.rpow_mul_natCast (Nat.cast_nonneg _) _ _]
variable {G:Type*} [CommGroup G] [Fintype G]
variable (q:ClassGroup (𝓞 K) →* G)
variable (hkill:∀ I:(Ideal (𝓞 E))⁰, q (ClassGroup.mk0 (z14.norm K E I)) = 1)
noncomputable def label (p:z14.Primes K):G:=q (ClassGroup.mk0 (z1e.prime p))
include hkill in
lemma zk5 (P:z14.Primes E) (hP:label K q (z14.below K E P) ≠ 1) :
    2 ≤ z14.degree K E P:=by
  have hpos:=z14.degree_pos K E P
  have hh:=hkill (z1e.prime P)
  rw [zmv,map_pow,map_pow] at hh
  by_contra h
  have hd:z14.degree K E P = 1:=by omega
  rw [hd,pow_one] at hh
  exact hP hh
include hkill in
lemma zi5 (s:ℝ) (hs:0 < s) (P:z14.Primes E) :
    z1j E s P ≤ z2s.value G (label K q) (z1j K s) (z14.below K E P):=by
  rw [zcs K E]
  have hb:=z2l K s hs (z14.below K E P)
  unfold z2s.value
  split_ifs with h
  · exact pow_le_of_le_one hb.1 hb.2.le (z14.degree_pos K E P).ne'
  · exact pow_le_pow_of_le_one hb.1 hb.2.le (zk5 K E q hkill P h)
include hkill in
lemma zep (s:ℝ) (hs:1 < s) :
    ∃ a:ℝ, 1 ≤ a ∧
      HasProd (fun p => (1-z2s.value G (label K q) (z1j K s) p)⁻¹) a ∧
      z8.zeta E s ≤ a^Module.finrank K E:=by
  have hs0:0 < s:=zero_lt_one.trans hs
  have hx0:=fun p => (z2l K s hs0 p).1
  have hx:=fun p => (z2l K s hs0 p).2
  obtain ⟨a,ha0,ha⟩:=z2s.zji G (label K q) (z1j K s) hx0 hx
    (zgm K s hs)
  refine ⟨a,ha0,ha,?_⟩
  have hk (p:z14.Primes K):z2s.value G (label K q) (z1j K s) p < 1 :=
    (z2s.z4d G (label K q) (z1j K s) hx0 hx p).2.trans_lt (hx p)
  apply zfe.zmc (z14.below K E)
    (fun p => (1-z2s.value G (label K q) (z1j K s) p)⁻¹)
    (fun P => (1-z1j E s P)⁻¹) (Module.finrank K E) ?_ ?_ ?_
    (fun t p => by
      convert z14.zk6 K E t p using 1
      congr 1
      ext P
      simp only [Finset.mem_filter]) a _ ha (zff E s hs)
  · intro p
    apply (one_le_inv₀ (sub_pos.mpr (hk p))).mpr
    linarith [(z2s.z4d G (label K q) (z1j K s) hx0 hx p).1]
  · intro P
    exact (inv_pos.mpr (sub_pos.mpr (z2l E s hs0 P).2)).le
  · intro P
    apply (inv_le_inv₀ (sub_pos.mpr (z2l E s hs0 P).2) (sub_pos.mpr (hk _))).mpr
    exact sub_le_sub_left (zi5 K E q hkill s hs0 P) 1
end z1r
namespace z4u
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K:Type*) [Field K] [NumberField K]
variable (G:Type*) [CommGroup G] [Fintype G] (hsq:∀ g:G, g^2 = 1)
variable (q:ClassGroup (𝓞 K) →* G)
noncomputable def pullback (χ:z1b.Index G):ClassGroup (𝓞 K) →* ℝ :=
  (z1b.z2k G hsq χ).comp q
noncomputable def series (χ:z1b.Index G) (s:ℝ):ℝ :=
  ∑' I, z8.weight K (pullback K G hsq q χ) s I
@[simp] lemma zn5 (s:ℝ):series K G hsq q 1 s = z8.zeta K s:=by
  simp only [series,z8.zeta,z8.weight,pullback,MonoidHom.comp_apply,
    z1b.zhg,one_mul]
lemma z6u (F:Type*) [Field F] [NumberField F] (s:ℝ):0 ≤ z8.zeta F s:=by
  apply tsum_nonneg
  intro I
  exact mul_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
lemma zkm (F:Type*) [Field F] [NumberField F] {s t:ℝ} (hs:1 < s) (hst:s ≤ t) :
    z8.zeta F t ≤ z8.zeta F s:=by
  apply Summable.tsum_le_tsum _ (z8.z37 F (fun _ => 1) t (hs.trans_le hst)).of_norm
    (z8.z37 F (fun _ => 1) s hs).of_norm
  intro I
  simp only [z8.weight,one_mul]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors I)
  · linarith
lemma zfb (s:ℝ) (p:z14.Primes K) :
    z1r.z1j K (2*s) p = (z1r.z1j K s p)^2:=by
  unfold z1r.z1j
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) _ 2]
  congr 1
  norm_num
  ring
lemma zc6 (s:ℝ) (hs:1 < s) (a:ℝ)
    (ha:HasProd (fun p =>
      (1-z2s.value G (z1r.label K q) (z1r.z1j K s) p)⁻¹) a) :
    a^Fintype.card G ≤ (z8.zeta K (2*s))^Fintype.card G *
      ∏ χ, series K G hsq q χ s:=by
  have hs0:0 < s:=zero_lt_one.trans hs
  apply z2s.zj1 G hsq (z1r.label K q) (z1r.z1j K s)
    (fun p => (z1r.z2l K s hs0 p).1)
    (fun p => (z1r.z2l K s hs0 p).2) a _ _ ha
  · simpa only [zfb] using z1r.zff K (2*s) (by linarith)
  · intro χ
    simpa only [z8.weight,pullback,MonoidHom.comp_apply,z1r.label,
      z1r.z1j,series,z1e.prime] using
      z8.zed K (pullback K G hsq q χ) s hs
variable (hq:Function.Surjective q)
include hq in
lemma zfd [IsTotallyReal K] (n:ℕ) (hd:finrank ℚ K = n+1)
    (χ:z1b.Index G) (hχ:χ ≠ 1) :
    ∃ B > (0:ℝ), ∀ s:ℝ, 1 < s → s ≤ 2 → |series K G hsq q χ s| ≤ B:=by
  have hz:∑ c, pullback K G hsq q χ c = 0 :=
    z1b.zh5 G hsq q hq hχ
  obtain ⟨B,hB,h⟩:=z8.zhy K n hd (pullback K G hsq q χ) hz
  refine ⟨B,hB,?_⟩
  intro s hs hs2
  have hh:=h s hs hs2
  rw [z8.zae K _ s hs,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh
include hq in
lemma zkt [IsTotallyReal K] (n:ℕ) (hd:finrank ℚ K = n+1) :
    ∃ C > (0:ℝ), ∀ s:ℝ, 1 < s → s ≤ 2 →
      (∏ χ:z1b.Index G, series K G hsq q χ s) ≤ C*z8.zeta K s:=by
  have h:∀ χ:z1b.Index G, ∃ B > (0:ℝ),
      χ ≠ 1 → ∀ s:ℝ, 1 < s → s ≤ 2 → |series K G hsq q χ s| ≤ B:=by
    intro χ
    by_cases hχ:χ = 1
    · exact ⟨1,zero_lt_one,fun h => (h hχ).elim⟩
    · obtain ⟨B,hB,h⟩:=zfd K G hsq q hq n hd χ hχ
      exact ⟨B,hB,fun _ => h⟩
  choose B hB hbound using h
  let S:Finset (z1b.Index G):=Finset.univ.erase 1
  let C:ℝ:=∏ χ ∈ S, B χ
  have hC:0 < C:=Finset.prod_pos (fun χ _ => hB χ)
  refine ⟨C,hC,?_⟩
  intro s hs hs2
  have hrest:(∏ χ ∈ S, series K G hsq q χ s) ≤ C:=by
    calc
      _ ≤ |∏ χ ∈ S, series K G hsq q χ s|:=le_abs_self _
      _ = ∏ χ ∈ S, |series K G hsq q χ s|:=Finset.abs_prod _ _
      _ ≤ C:=Finset.prod_le_prod (fun χ _ => abs_nonneg _) (fun χ hχ =>
        hbound χ (Finset.mem_erase.mp hχ).1 s hs hs2)
  have he:(∏ χ:z1b.Index G, series K G hsq q χ s) =
      z8.zeta K s * (∏ χ ∈ S, series K G hsq q χ s):=by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1:z1b.Index G)),zn5]
  rw [he]
  calc
    _ ≤ z8.zeta K s*C:=mul_le_mul_of_nonneg_left hrest (z6u K s)
    _ = _:=mul_comm _ _
end z4u
namespace z84
open Filter Topology
lemma degree_le {α:Type*} (l:Filter α) [l.NeBot]
    (u a b:α → ℝ) (A B C:ℝ) (hA:0 < A)
    (hu:Tendsto u l (𝓝 0)) (ha:Tendsto (fun x => u x*a x) l (𝓝 A))
    (hb:Tendsto (fun x => u x*b x) l (𝓝 B))
    (hu0:∀ᶠ x in l, 0 ≤ u x) (m d:ℕ)
    (h:∀ᶠ x in l, a x^m ≤ C*b x^d):m ≤ d:=by
  by_contra hmd
  have hdm:d < m:=by omega
  have hsub:0 < m-d:=Nat.sub_pos_of_lt hdm
  have hright:Tendsto (fun x => C*(u x*b x)^d*u x^(m-d)) l (𝓝 0):=by
    have hh:=((hb.pow d).const_mul C).mul (hu.pow (m-d))
    simpa only [zero_pow hsub.ne',mul_zero] using hh
  have hbound:∀ᶠ x in l, (u x*a x)^m ≤ C*(u x*b x)^d*u x^(m-d):=by
    filter_upwards [hu0,h] with x hx hh
    calc
      _ = u x^m*a x^m:=mul_pow _ _ _
      _ ≤ u x^m*(C*b x^d):=mul_le_mul_of_nonneg_left hh (pow_nonneg hx _)
      _ = C*(u x*b x)^d*u x^(m-d):=by
        rw [mul_pow]
        have he:u x^m = u x^d*u x^(m-d):=by rw [← pow_add,Nat.add_sub_of_le hdm.le]
        rw [he]
        ring
  have hle:=le_of_tendsto_of_tendsto (ha.pow m) hright hbound
  exact (not_le_of_gt (pow_pos hA m)) hle
end z84
namespace z4u
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [IsTotallyReal K]
variable (G:Type*) [CommGroup G] [Fintype G] (hsq:∀ g:G, g^2 = 1)
variable (q:ClassGroup (𝓞 K) →* G) (hq:Function.Surjective q)
variable (hkill:∀ I:(Ideal (𝓞 E))⁰, q (ClassGroup.mk0 (z14.norm K E I)) = 1)
include hsq hq hkill in
lemma zjl:Fintype.card G ≤ Module.finrank K E:=by
  have hdpos:0 < Module.finrank ℚ K:=Module.finrank_pos
  let n:=Module.finrank ℚ K-1
  have hd:Module.finrank ℚ K = n+1:=by dsimp [n]; omega
  obtain ⟨C,hC,hprod⟩:=zkt K G hsq q hq n hd
  let m:=Fintype.card G
  let d:=Module.finrank K E
  let T:=((z8.zeta K 2)^m*C)^d
  have hmain (s:ℝ) (hs:1 < s) (hs2:s ≤ 2) :
      (z8.zeta E s)^m ≤ T*(z8.zeta K s)^d:=by
    obtain ⟨a,ha0,ha,hE⟩:=z1r.zep K E q hkill s hs
    have hchar:=zc6 K G hsq q s hs a ha
    have hsqb:(z8.zeta K (2*s))^m ≤ (z8.zeta K 2)^m :=
      pow_le_pow_left₀ (z6u K (2*s)) (zkm K (by norm_num) (by linarith)) _
    have hA:a^m ≤ ((z8.zeta K 2)^m*C)*z8.zeta K s:=by
      calc
        _ ≤ (z8.zeta K (2*s))^m * ∏ χ, series K G hsq q χ s:=hchar
        _ ≤ (z8.zeta K (2*s))^m * (C*z8.zeta K s) :=
          mul_le_mul_of_nonneg_left (hprod s hs hs2) (pow_nonneg (z6u K _) _)
        _ ≤ (z8.zeta K 2)^m * (C*z8.zeta K s) :=
          mul_le_mul_of_nonneg_right hsqb (mul_nonneg hC.le (z6u K s))
        _ = _:=by ring
    calc
      _ ≤ (a^d)^m:=pow_le_pow_left₀ (z6u E s) hE _
      _ = (a^m)^d:=by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ (((z8.zeta K 2)^m*C)*z8.zeta K s)^d :=
        pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans ha0) _) hA _
      _ = _:=by rw [mul_pow]
  have hu:Tendsto (fun s:ℝ => s-1) (𝓝[Set.Ioi 1] 1) (𝓝 0):=by
    have hh:Tendsto (fun s:ℝ => s) (𝓝[Set.Ioi 1] 1) (𝓝 1) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using hh.sub_const 1
  apply z84.degree_le (𝓝[Set.Ioi 1] (1:ℝ)) (fun s => s-1)
    (z8.zeta E) (z8.zeta K) (z8.residue E)
    (z8.residue K) T (z8.zm0 E) hu
    (z8.zfh E) (z8.zfh K) ?_ m d ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_nonneg.mpr (Set.mem_Ioi.mp hs).le
  · have htwo:∀ᶠ s:ℝ in 𝓝[Set.Ioi 1] 1, s < 2 :=
      (eventually_lt_nhds (by norm_num:(1:ℝ) < 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,htwo] with s hs hs2
    exact hmain s hs hs2.le
end z4u
namespace z2g
open NumberField Ideal Module
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
noncomputable def subgroup:Subgroup (ClassGroup (𝓞 K)) :=
  Subgroup.closure (Set.range (ClassGroup.mk0.comp (z14.norm K E)))
abbrev quotient:=ClassGroup (𝓞 K) ⧸ subgroup K E
noncomputable def map:ClassGroup (𝓞 K) →* quotient K E:=QuotientGroup.mk' (subgroup K E)
lemma map_surjective:Function.Surjective (map K E):=QuotientGroup.mk'_surjective _
lemma zlg (I:(Ideal (𝓞 E))⁰):map K E (ClassGroup.mk0 (z14.norm K E I)) = 1:=by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_closure (Set.mem_range_self I)
noncomputable def extend (I:(Ideal (𝓞 K))⁰):(Ideal (𝓞 E))⁰ :=
  ⟨Ideal.map (algebraMap (𝓞 K) (𝓞 E)) I.1,
    mem_nonZeroDivisors_iff_ne_zero.mpr (Ideal.map_ne_bot_of_ne_bot (nonZeroDivisors.coe_ne_zero I))⟩
lemma zlx (I:(Ideal (𝓞 K))⁰) :
    z14.norm K E (extend K E I) = I ^ Module.finrank K E:=by
  letI:=FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 E))
  apply Subtype.ext
  change Ideal.relNorm (𝓞 K) (Ideal.map (algebraMap (𝓞 K) (𝓞 E)) I.1) = I.1 ^ Module.finrank K E
  rw [Ideal.relNorm_algebraMap]
  congr 1
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
lemma zmk (g:quotient K E):g ^ Module.finrank K E = 1:=by
  obtain ⟨c,rfl⟩:=map_surjective K E g
  obtain ⟨I,rfl⟩:=ClassGroup.mk0_surjective c
  have hh:=zlg K E (extend K E I)
  rwa [zlx,map_pow,map_pow] at hh
lemma card_le_two [IsTotallyReal K] (hd:Module.finrank K E = 2) :
    Fintype.card (quotient K E) ≤ 2:=by
  have hsq (g:quotient K E):g^2 = 1:=by simpa only [hd] using zmk K E g
  have hh:=z4u.zjl K E (quotient K E) hsq (map K E)
    (map_surjective K E) (zlg K E)
  rwa [hd] at hh
end z2g
namespace z20
open NumberField z7
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
lemma za4:z2g.subgroup K E = (z1o.norm K E).range:=by
  have he:Set.range (ClassGroup.mk0.comp (z14.norm K E)) =
      ((z1o.norm K E).range:Set (ClassGroup (𝓞 K))):=by
    ext c
    constructor
    · rintro ⟨I,rfl⟩
      exact ⟨ClassGroup.mk0 I,z1o.zhl K E I⟩
    · rintro ⟨c,rfl⟩
      obtain ⟨I,rfl⟩:=ClassGroup.mk0_surjective c
      exact ⟨I,(z1o.zhl K E I).symm⟩
  rw [z2g.subgroup,he,Subgroup.closure_eq]
end z20
namespace z20
open NumberField z7
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
noncomputable def zj3:(z1k.z2o K E).range ≃ (z1o.norm K E).range :=
  (Additive.toMul.trans (zj.equiv K).toEquiv).subtypeEquiv (fun y => by
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨zj.equiv E x.toMul,?_⟩
      change z1o.norm K E (zj.equiv E x.toMul) =
        zj.equiv K ((zj.equiv K).symm
          (z1o.norm K E (zj.equiv E x.toMul)))
      rw [MulEquiv.apply_symm_apply]
    · rintro ⟨c,hc⟩
      refine ⟨Additive.ofMul ((zj.equiv E).symm c),?_⟩
      apply Additive.toMul.injective
      apply (zj.equiv K).injective
      change zj.equiv K ((zj.equiv K).symm
        (z1o.norm K E (zj.equiv E ((zj.equiv E).symm c)))) = _
      rw [MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply]
      exact hc)
variable (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
include hdeg hne hunram in
lemma zmf [IsTotallyReal K] [IsTotallyReal E] :
    2 ≤ Nat.card (z2g.quotient K E):=by
  have h₁:=z1k.z4g K E σ
  have h₂:=z4.z77 K E σ hdeg hne hunram
  have h:2*Nat.card (z1o.norm K E).range ≤ Nat.card (ClassGroup (𝓞 K)):=by
    rw [← Nat.card_congr (zj3 K E)]
    exact (Nat.mul_le_mul_left 2 h₁).trans h₂
  have hm:Nat.card (z1o.norm K E).range * Nat.card (z2g.quotient K E) =
      Nat.card (ClassGroup (𝓞 K)):=by
    change Nat.card (z1o.norm K E).range * Nat.card
      (ClassGroup (𝓞 K) ⧸ z2g.subgroup K E) = _
    rw [za4]
    exact (z1o.norm K E).range.card_mul_index
  rw [← hm,mul_comm 2] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos
include hdeg hne hunram in
lemma card_eq_two [IsTotallyReal K] [IsTotallyReal E] :
    Nat.card (z2g.quotient K E) = 2:=by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact z2g.card_le_two K E hdeg
  · exact zmf K E σ hdeg hne hunram
end z20
namespace z3q
open scoped Classical
variable {A B:Type*} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
lemma zgh (σ:A →ₗ[ℤ] A) (f:A →ₗ[ℤ] B)
    (hf:∀ x, f (σ x) = f x)
    (hc:Nat.card f.range = Nat.card (z9.plus σ)) :
    f.ker = (σ-LinearMap.id).range:=by
  have hle:(σ-LinearMap.id).range ≤ f.ker:=by
    rintro _ ⟨x,rfl⟩
    change f (σ x-x) = 0
    rw [map_sub,hf,sub_self]
  have h₁:=f.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv,hc] at h₁
  have h₂:=(σ-LinearMap.id).range.card_eq_card_quotient_mul_card
  rw [zad] at h₂
  have he:Nat.card f.ker = Nat.card (σ-LinearMap.id).range :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h₁.symm.trans h₂)
  apply le_antisymm _ hle
  have hs:((σ-LinearMap.id).range:Set A) = (f.ker:Set A) :=
    Set.eq_of_subset_of_ncard_le hle (by exact he.le)
  exact le_of_eq (SetLike.coe_injective hs.symm)
end z3q
namespace z20
open NumberField z7 z9 z17
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) [IsTotallyReal K] [IsTotallyReal E]
include hdeg hne hunram in
lemma z79 :
    2*Nat.card (z1k.z2o K E).range = Nat.card (ClassGroup (𝓞 K)):=by
  rw [Nat.card_congr (zj3 K E),mul_comm]
  have h:=(z1o.norm K E).range.card_mul_index
  have hi:(z1o.norm K E).range.index = 2:=by
    change Nat.card (ClassGroup (𝓞 K) ⧸ (z1o.norm K E).range) = 2
    rw [← za4]
    exact card_eq_two K E σ hdeg hne hunram
  rwa [hi] at h
include hdeg hne hunram in
lemma z5x :
    Nat.card (z1k.z2o K E).range = Nat.card (plus (A:=C E) (z31 K E σ)):=by
  have h₁:=z1k.z4g K E σ
  have h₂:=z4.z77 K E σ hdeg hne hunram
  have h₃:=z79 K E σ hdeg hne hunram
  omega
set_option maxHeartbeats 2000000 in
include hdeg hne hunram in
lemma zal :
    (z1k.z2o K E).ker = (z31 K E σ-LinearMap.id).range:=by
  letI:Finite (C E):=Finite.of_equiv (zj.Classes E) Additive.ofMul
  letI:Finite (C K):=Finite.of_equiv (zj.Classes K) Additive.ofMul
  exact @z3q.zgh (C E) (C K) inferInstance inferInstance inferInstance inferInstance
    (z31 K E σ) (z1k.z2o K E) (z1k.za6 K E σ)
    (z5x K E σ hdeg hne hunram)
include hdeg hne hunram in
lemma zi4 :
    2*Nat.card (plus (A:=C E) (z31 K E σ)) = Nat.card (ClassGroup (𝓞 K)):=by
  rw [← z5x K E σ hdeg hne hunram]
  exact z79 K E σ hdeg hne hunram
include hne hunram in
lemma zdj :
    Nat.card (z4k K E σ hdeg) = Nat.card (z13.H0 K E σ hdeg):=by
  have h₁:=(z2m (z1d K E σ hdeg)).range.card_eq_card_quotient_mul_card
  change Nat.card (plus (A:=C E) (z31 K E σ)) =
    Nat.card (z2m (z1d K E σ hdeg)).range * Nat.card (z4k K E σ hdeg) at h₁
  have h₂:=za2 K E σ hdeg hne
  rw [Nat.card_congr (z4.zk0 K E σ hdeg hne hunram).toEquiv,
    z13.zla K E σ hdeg hne] at h₂
  have hc:Nat.card (C K) = Nat.card (ClassGroup (𝓞 K)) :=
    Nat.card_congr (Additive.toMul.trans (zj.equiv K).toEquiv)
  rw [hc,← zi4 K E σ hdeg hne hunram,h₁] at h₂
  have hp:0 < Nat.card (z2m (z1d K E σ hdeg)).range:=Nat.card_pos
  nlinarith
include hne hunram in
lemma zhz :
    Nat.card (z17.H1 (z1d K E σ hdeg)) =
      Nat.card (z13.H0 K E σ hdeg):=by
  apply le_antisymm (z8b K E σ hdeg hne)
  rw [← zdj K E σ hdeg hne hunram,
    Nat.card_congr (z7o K E σ hdeg).toEquiv]
  letI:=z9f K E σ hdeg hne
  exact Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
end z20

namespace z20
open NumberField z7 z9 z17
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) [IsTotallyReal K] [IsTotallyReal E]
include hne hunram in
lemma z7j :
    Function.Surjective (connecting (z1w K E σ hdeg).neg):=by
  let S:=z1w K E σ hdeg
  letI:Finite (z17.H1 S.neg):=z4z K E σ hdeg
  letI:Finite (z7l S):=Finite.of_injective _ (z2p S (z94 K E σ hdeg hne))
  letI:=Fintype.ofFinite (z7l S)
  letI:=Fintype.ofFinite (z17.H1 S.neg)
  have hh:=z94 K E σ hdeg hne
  have hcard:Fintype.card (z7l S) = Fintype.card (z17.H1 S.neg):=by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
    rw [Nat.card_congr (z99 K E σ hdeg).toEquiv]
    exact zhz K E σ hdeg hne hunram
  have hsurj:=((Fintype.bijective_iff_injective_and_card (z6m S hh)).mpr
    ⟨z2p S hh,hcard⟩).surjective
  intro t
  obtain ⟨q,hq⟩:=hsurj t
  obtain ⟨b,rfl⟩:=(norm (-S.b) (z1t S.b S.hb)).range.mkQ_surjective q
  exact ⟨b,hq⟩
include hdeg hne hunram in
lemma zg4 (u:(𝓞 K)ˣ) :
    ∃ x:Eˣ, Algebra.norm K (x:E) = (u:K):=by
  let uf:=z13.zam K E σ hdeg hne (Additive.ofMul u)
  obtain ⟨x,hx⟩:=z6i (z1w K E σ hdeg)
    (z7j K E σ hdeg hne hunram) uf
  refine ⟨x.toMul,?_⟩
  apply (algebraMap K E).injective
  rw [z13.z5j K E σ hdeg hne]
  have h:=congrArg (fun z:F E => (z.toMul:E)) hx
  change ((x.toMul * z10.z15 E σ.toRingEquiv x.toMul:Eˣ):E) =
    algebraMap K E (u:K) at h
  rw [Units.val_mul] at h
  change (x.toMul:E)*σ (x.toMul:E) = algebraMap K E (u:K) at h
  simpa only [mul_comm] using h
end z20
namespace z83
open scoped Classical
section Ring
variable {R:Type*} [CommRing R] (σ:R ≃+* R)
noncomputable def z3k (I:Ideal R):Ideal R :=
  Ideal.span ((fun x:R => σ x*x) '' (I:Set R))
private lemma zi3 (I:Ideal R) (x:R) (hx:x ∈ I):σ x*x ∈ z3k σ I :=
  Ideal.subset_span ⟨x,hx,rfl⟩
private lemma zk1 (I:Ideal R) (x y:R) (hx:x ∈ I) (hy:y ∈ I) :
    σ x*y+x*σ y ∈ z3k σ I:=by
  have h:=(z3k σ I).sub_mem
    ((z3k σ I).sub_mem (zi3 σ I (x+y) (I.add_mem hx hy)) (zi3 σ I x hx))
    (zi3 σ I y hy)
  convert h using 1
  rw [map_add]
  ring
lemma zie (hdiff:Ideal.span (Set.range (fun a:R => σ a-a)) = ⊤) (I:Ideal R) :
    z3k σ I = I*Ideal.map σ I:=by
  have hxy (x y:R) (hx:x ∈ I) (hy:y ∈ I):x*σ y ∈ z3k σ I:=by
    have hone:(1:R) ∈ Ideal.span (Set.range (fun a:R => σ a-a)):=by rw [hdiff]; trivial
    have hmul:∀ a ∈ Ideal.span (Set.range (fun a:R => σ a-a)), a*(x*σ y) ∈ z3k σ I:=by
      intro a ha
      refine Submodule.span_induction (p:=fun a _ => a*(x*σ y) ∈ z3k σ I) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨b,rfl⟩
        have h₁:=zk1 σ I x (b*y) hx (I.mul_mem_left b hy)
        have h₂:=(z3k σ I).mul_mem_left b (zk1 σ I x y hx hy)
        convert (z3k σ I).sub_mem h₁ h₂ using 1
        rw [map_mul]
        ring
      · simpa using (z3k σ I).zero_mem
      · intro a b ha hb h₁ h₂
        simpa only [add_mul] using (z3k σ I).add_mem h₁ h₂
      · intro a b hb h
        simpa only [smul_eq_mul,mul_assoc] using (z3k σ I).mul_mem_left a h
    simpa only [one_mul] using hmul 1 hone
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change σ x*x ∈ I*Ideal.map σ I
    rw [mul_comm (σ x)]
    exact Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem _ hx)
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩:=(Ideal.mem_map_iff_of_surjective _ σ.surjective).mp hy
    exact hxy x z hx hz
end Ring
open NumberField
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
include hdeg hne in
lemma zjm (x:𝓞 E) :
    algebraMap (𝓞 K) (𝓞 E) (Algebra.intNorm (𝓞 K) (𝓞 E) x) = RingOfIntegers.mapAlgEquiv σ x*x:=by
  apply RingOfIntegers.coe_injective
  change algebraMap K E (algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) x)) = σ (x:E)*(x:E)
  rw [Algebra.algebraMap_intNorm (K:=K) (L:=E)]
  exact z13.z5j K E σ hdeg hne (x:E)
include hdeg hne in
lemma map_relNorm (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) (I:Ideal (𝓞 E)) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 E)) (Ideal.relNorm (𝓞 K) I) =
      I*Ideal.map (RingOfIntegers.mapAlgEquiv σ) I:=by
  have h:=zie (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
    (z23.z80 K E σ hne hunram) I
  rw [Ideal.map_relNorm]
  have hf:((algebraMap (𝓞 K) (𝓞 E)) ∘ Algebra.intNorm (𝓞 K) (𝓞 E)) =
      (fun x:𝓞 E => RingOfIntegers.mapAlgEquiv σ x*x) :=
    funext (zjm K E σ hdeg hne)
  rw [hf]
  exact h
end z83
namespace z24
open NumberField z7 z9 z17 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
noncomputable def z2f:D E →ₗ[ℤ] D K :=
  (z4.z2v K E σ hdeg hne hunram).symm.toLinearMap.comp
    (z9.norm (z22 K E σ) (z33 K E σ hdeg))
noncomputable def z55:F E →ₗ[ℤ] F K :=
  (MonoidHom.toAdditive (Units.map (Algebra.norm K))).toIntLinearMap
@[simp] lemma z4l (I:D E) :
    z4.z2v K E σ hdeg hne hunram (z2f K E σ hdeg hne hunram I) =
      z9.norm (z22 K E σ) (z33 K E σ hdeg) I:=by
  exact (z4.z2v K E σ hdeg hne hunram).apply_symm_apply _
@[simp] lemma z8a (x:F E) :
    z2f K E σ hdeg hne hunram (z4.z11 E x) =
      z4.z11 K (z55 K E x):=by
  apply (z4.z2v K E σ hdeg hne hunram).injective
  rw [z4l]
  apply Subtype.ext
  change Additive.ofMul (z10.action E σ.toRingEquiv (toPrincipalIdeal (𝓞 E) E x.toMul) *
      toPrincipalIdeal (𝓞 E) E x.toMul) =
    Additive.ofMul (z10.extend K E (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K) x.toMul)))
  apply congrArg Additive.ofMul
  rw [z4f,← map_mul,z58]
  apply congrArg (toPrincipalIdeal (𝓞 E) E)
  apply Units.ext
  change σ (x.toMul:E)*(x.toMul:E) = algebraMap K E (Algebra.norm K (x.toMul:E))
  exact (z13.z5j K E σ hdeg hne (x.toMul:E)).symm
@[simp] lemma zhj (I:D E) :
    z2f K E σ hdeg hne hunram (z22 K E σ I) = z2f K E σ hdeg hne hunram I:=by
  apply (z4.z2v K E σ hdeg hne hunram).injective
  rw [z4l,z4l]
  apply Subtype.ext
  change z22 K E σ (z22 K E σ I)+z22 K E σ I = z22 K E σ I+I
  rw [involutive _ (z33 K E σ hdeg)]
  abel
@[simp] lemma zg3 (I:(Ideal (𝓞 E))⁰) :
    z2f K E σ hdeg hne hunram (Additive.ofMul (FractionalIdeal.mk0 E I)) =
      Additive.ofMul (FractionalIdeal.mk0 K (z14.norm K E I)):=by
  apply (z4.z2v K E σ hdeg hne hunram).injective
  rw [z4l]
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change actionHom E σ.toRingEquiv (FractionalIdeal.mk0 E I).1 * (FractionalIdeal.mk0 E I).1 =
    FractionalIdeal.extendedHom E (𝓞 E) (FractionalIdeal.mk0 K (z14.norm K E I)).1
  rw [FractionalIdeal.coe_mk0,FractionalIdeal.coe_mk0,
    FractionalIdeal.extendedHom_coeIdeal_eq_map]
  change ((I.1:FractionalIdeal (𝓞 E)⁰ E).extended E _) * (I.1:FractionalIdeal (𝓞 E)⁰ E) = _
  rw [FractionalIdeal.extended_coeIdeal_eq_map,← FractionalIdeal.coeIdeal_mul]
  congr 1
  exact (mul_comm _ _).trans (z83.map_relNorm K E σ hdeg hne hunram I.1).symm
private lemma zer (x:F K) :
    z1i K (z4.z11 K x) = 0 :=
  zj.zf9 K x.toMul
private lemma z88:Function.Surjective (z1i E):=by
  intro c
  obtain ⟨I,hI⟩:=zj.mk_surjective E c.toMul
  exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩
private lemma zbx:(z1i E).ker ≤
    ((z1i K).comp (z2f K E σ hdeg hne hunram)).ker:=by
  intro I hI
  rw [z4.z7k] at hI
  obtain ⟨x,rfl⟩:=hI
  change z1i K (z2f K E σ hdeg hne hunram (z4.z11 E x)) = 0
  rw [z8a,zer]
set_option maxHeartbeats 3000000 in
private noncomputable def zh8:C E →ₗ[ℤ] C K :=
  @factor (D E) (C E) (C K) inferInstance inferInstance inferInstance (z1i E) (z88 E)
    ((z1i K).comp (z2f K E σ hdeg hne hunram)) (zbx K E σ hdeg hne hunram)
set_option maxHeartbeats 3000000 in
private lemma za8 (I:D E) :
    zh8 K E σ hdeg hne hunram (z1i E I) = z1i K (z2f K E σ hdeg hne hunram I) :=
  @z7i (D E) (C E) (C K) inferInstance inferInstance inferInstance
    (z1i E) (z88 E)
    ((z1i K).comp (z2f K E σ hdeg hne hunram)) (zbx K E σ hdeg hne hunram) I
set_option maxHeartbeats 2000000 in
private lemma zjb:zh8 K E σ hdeg hne hunram = z1k.z2o K E:=by
  apply LinearMap.ext
  intro c
  obtain ⟨I,hI⟩:=zj.z9b E c.toMul
  have hc:z1i E (Additive.ofMul (FractionalIdeal.mk0 E I)) = c:=congrArg Additive.ofMul hI
  rw [← hc,za8,zg3]
  exact (zj.zba K E I).symm
set_option maxHeartbeats 2000000 in
lemma zn2 (I:D E) :
    z1k.z2o K E (z1i E I) = z1i K (z2f K E σ hdeg hne hunram I):=by
  rw [← zjb K E σ hdeg hne hunram]
  exact za8 K E σ hdeg hne hunram I
end z24
namespace z24
open NumberField z7 z9 z17 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  [IsTotallyReal K] [IsTotallyReal E]
  (σ:E ≃ₐ[K] E) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
set_option maxHeartbeats 3000000 in
lemma z7z (a:F K) (I:D E)
    (ha:z4.z11 K a = z2f K E σ hdeg hne hunram I) :
    ∃ x:F E, z55 K E x = a:=by
  have hI:z1i E I ∈ (z1k.z2o K E).ker:=by
    change z1k.z2o K E (z1i E I) = 0
    rw [zn2 K E σ hdeg hne hunram,← ha]
    exact zj.zf9 K a.toMul
  rw [z20.zal K E σ hdeg hne hunram] at hI
  obtain ⟨c,hc⟩:=hI
  obtain ⟨J,hJ⟩:=zj.mk_surjective E c.toMul
  let j:D E:=Additive.ofMul J
  have hj:z1i E j = c:=congrArg Additive.ofMul hJ
  let T:D E:=I-(z22 K E σ j-j)
  have hT:z1i E T = 0:=by
    change z1i E (I-(z22 K E σ j-j)) = 0
    rw [map_sub,map_sub]
    change z1i E I-(z31 K E σ (z1i E j)-z1i E j) = 0
    rw [hj]
    change z31 K E σ c-c = z1i E I at hc
    rw [hc,sub_self]
  have hT':T ∈ (z4.z11 E).range:=by
    rw [← z4.z7k]
    exact hT
  obtain ⟨x,hx⟩:=hT'
  have hn:z2f K E σ hdeg hne hunram T = z2f K E σ hdeg hne hunram I:=by
    change z2f K E σ hdeg hne hunram (I-(z22 K E σ j-j)) = _
    rw [map_sub,map_sub,zhj,sub_self,sub_zero]
  have hpx:z4.z11 K (z55 K E x) =
      z4.z11 K a:=by
    rw [← z8a K E σ hdeg hne hunram,hx,hn,ha]
  have hu:z4.z11 K (a-z55 K E x) = 0:=by
    rw [map_sub,hpx,sub_self]
  obtain ⟨u,hu⟩:=(z5c K (a-z55 K E x).toMul).mp hu
  obtain ⟨y,hy⟩:=z20.zg4 K E σ hdeg hne hunram u
  have hy':z55 K E (Additive.ofMul y) = a-z55 K E x:=by
    apply Additive.toMul.injective
    apply Units.ext
    change Algebra.norm K (y:E) = _
    rw [hy]
    exact congrArg (fun z:Kˣ => (z:K)) hu
  refine ⟨x+Additive.ofMul y,?_⟩
  rw [map_add,hy']
  abel
end z24
namespace z1n
open scoped Classical
variable {G A B:Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
  (ρ:G →* AddAut A)
@[simp] lemma addAut_one_apply (a:A):(1:AddAut A) a = a:=rfl
@[simp] lemma addAut_mul_apply (g h:AddAut A) (a:A):(g * h) a = g (h a):=rfl
def IsCocycle (f:G → G → A):Prop :=
  ∀ g h k, ρ g (f h k)+f g (h*k) = f g h+f (g*h) k
def boundary (b:G → A) (g h:G):A:=ρ g (b h)-b (g*h)+b g
def IsCoboundary (f:G → G → A):Prop:=∃ b, f = boundary ρ b
@[simp] lemma act_one (a:A):ρ 1 a = a:=by rw [map_one]; rfl
@[simp] lemma z8o (g h:G) (a:A):ρ (g*h) a = ρ g (ρ h a):=by rw [map_mul]; rfl
@[simp] lemma znp (b:G → A):boundary ρ b 1 1 = b 1:=by
  simp [boundary]
lemma z5a (b:G → A):IsCocycle ρ (boundary ρ b):=by
  intro g h k
  simp only [boundary,map_add,map_sub,z8o,mul_assoc]
  abel
lemma zay {f:G → G → A} (hf:IsCocycle ρ f) (g:G):f 1 g = f 1 1:=by
  have h:=hf 1 1 g
  simp only [act_one,one_mul] at h
  exact add_right_cancel h
lemma z6o {f:G → G → A} (hf:IsCocycle ρ f) (g:G):f g 1 = ρ g (f 1 1):=by
  have h:=hf g 1 1
  simp only [one_mul,mul_one] at h
  exact (add_right_cancel h).symm
lemma zil {f:G → G → A} (hf:IsCocycle ρ f)
    (s:G) (hs:s*s = 1) :
    ρ s (f s s-ρ s (f 1 1)) = f s s-ρ s (f 1 1):=by
  have h:=hf s s s
  rw [hs,zay ρ hf,z6o ρ hf] at h
  have he:ρ s (ρ s (f 1 1)) = f 1 1:=by rw [← z8o,hs,act_one]
  rw [map_sub,he]
  exact sub_eq_sub_iff_add_eq_add.mpr h
lemma ze7 {f:G → G → A} (hf:IsCocycle ρ f)
    (s:G) (hne:s ≠ 1) (hs:s*s = 1) (hg:∀ g:G, g = 1 ∨ g = s)
    (x:A) (hx:ρ s x+x = f s s-ρ s (f 1 1)):IsCoboundary ρ f:=by
  let b:G → A:=fun g => f 1 1 + if g = 1 then 0 else x
  refine ⟨b,?_⟩
  funext g h
  rcases hg g with rfl | rfl <;> rcases hg h with rfl | rfl
  · simp [b,boundary]
  · simp [b,boundary,zay ρ hf]
  · rw [z6o ρ hf]
    simp only [boundary,b,mul_one,if_pos,if_neg hne,add_zero]
    abel
  · simp only [boundary,b,hs,if_pos,if_neg hne,map_add,add_zero]
    have hh:=(eq_sub_iff_add_eq.mp hx).symm
    convert hh using 1 <;> abel
lemma zeq (τ:G →* AddAut B) (p:A →+ B)
    (hp:∀ g a, p (ρ g a) = τ g (p a))
    (s:G) (hne:s ≠ 1) (hs:s*s = 1) (hg:∀ g:G, g = 1 ∨ g = s)
    (hlift:∀ a:A, ρ s a = a → ∀ I:B,
      p a = τ s I+I → ∃ x:A, ρ s x+x = a)
    {f:G → G → A} (hf:IsCocycle ρ f)
    (hb:IsCoboundary τ (fun g h => p (f g h))):IsCoboundary ρ f:=by
  obtain ⟨b,hb⟩:=hb
  have hb' (g h:G):p (f g h) = boundary τ b g h:=congrFun (congrFun hb g) h
  have h1:p (f 1 1) = b 1:=by simpa using hb' 1 1
  have hnorm:p (f s s-ρ s (f 1 1)) = τ s (b s-b 1)+(b s-b 1):=by
    rw [map_sub,hp,h1,hb' s s]
    simp only [boundary,hs,map_sub]
    abel
  obtain ⟨x,hx⟩:=hlift _ (zil ρ hf s hs) _ hnorm
  exact ze7 ρ hf s hne hs hg x hx
end z1n
namespace zg
open NumberField z7 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
noncomputable def z15:Gal(E/K) →* AddAut (F E) where
  toFun σ:=(z10.z15 E σ.toRingEquiv).toAdditive
  map_one':=by
    apply AddEquiv.ext
    intro x
    rfl
  map_mul' σ τ:=by
    apply AddEquiv.ext
    intro x
    rfl
noncomputable def z1h:Gal(E/K) →* AddAut (D E) where
  toFun σ:=(z10.action E σ.toRingEquiv).toAdditive
  map_one':=by
    apply AddEquiv.ext
    intro I
    apply Additive.toMul.injective
    apply Units.ext
    ext x
    change x ∈ actionHom E (1:Gal(E/K)).toRingEquiv I.toMul.1 ↔ x ∈ I.toMul.1
    rw [z29]
    rfl
  map_mul' σ τ:=by
    apply AddEquiv.ext
    intro I
    apply Additive.toMul.injective
    apply Units.ext
    ext x
    change x ∈ actionHom E (σ*τ).toRingEquiv I.toMul.1 ↔
      x ∈ actionHom E σ.toRingEquiv (actionHom E τ.toRingEquiv I.toMul.1)
    rw [z29,z29,z29]
    rfl
lemma z4w (σ:Gal(E/K)) (x:F E) :
    z4.z11 E (z15 K E σ x) =
      z1h K E σ (z4.z11 E x):=by
  exact congrArg Additive.ofMul (z10.z4f E σ.toRingEquiv x.toMul).symm
end zg
namespace z24
open NumberField z7 z9 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  [IsTotallyReal K] [IsTotallyReal E]
  (σ:Gal(E/K)) (hdeg:Module.finrank K E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
lemma zj2 (x:F E) :
    (z4.z42 K E σ hdeg hne (z55 K E x)).1 =
      z3g K E σ x+x:=by
  apply Additive.toMul.injective
  apply Units.ext
  exact z13.z5j K E σ hdeg hne x.toMul
include hdeg hne hunram in
lemma zj0 (a:F E) (ha:z3g K E σ a = a) (I:D E)
    (hI:z4.z11 E a = z22 K E σ I+I) :
    ∃ x:F E, z3g K E σ x+x = a:=by
  let af:plus (z3g K E σ):=⟨a,(z1g _ _).mpr ha⟩
  let a₀:=(z4.z42 K E σ hdeg hne).symm af
  have ha₀:(z4.z42 K E σ hdeg hne a₀).1 = a:=by
    exact congrArg Subtype.val ((z4.z42 K E σ hdeg hne).apply_symm_apply af)
  have hnorm:z4.z11 K a₀ = z2f K E σ hdeg hne hunram I:=by
    apply (z4.z2v K E σ hdeg hne hunram).injective
    rw [z4l]
    apply Subtype.ext
    change Additive.ofMul (z10.extend K E (toPrincipalIdeal (𝓞 K) K a₀.toMul)) = _
    rw [z58]
    change z4.z11 E
      (z4.z42 K E σ hdeg hne a₀).1 = z22 K E σ I+I
    rw [ha₀,hI]
  obtain ⟨x,hx⟩:=z7z K E σ hdeg hne hunram a₀ I hnorm
  refine ⟨x,?_⟩
  rw [← zj2 K E σ hdeg hne,hx,ha₀]
include σ hdeg hne hunram in
lemma z90
    {f:Gal(E/K) → Gal(E/K) → F E}
    (hf:z1n.IsCocycle (zg.z15 K E) f)
    (hb:z1n.IsCoboundary (zg.z1h K E)
      (fun g h => z4.z11 E (f g h))) :
    z1n.IsCoboundary (zg.z15 K E) f:=by
  apply z1n.zeq (zg.z15 K E)
    (zg.z1h K E) (z4.z11 E).toAddMonoidHom
    (zg.z4w K E) σ hne _
    (z13.z4h K E σ hdeg hne) _ hf hb
  · ext x
    exact z76 K E σ hdeg x
  · intro a ha I hI
    exact zj0 K E σ hdeg hne hunram a ha I hI
end z24
namespace zg
open NumberField z7 z10
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
variable {G:Type*} [Group G] [Fintype G] (r:G →* Gal(E/K))
lemma zbs (b:G → D E)
    (hb:∀ g h, b (g*h) = zg.z1h K E (r g) (b h)+b g) :
    ∃ I:D E, ∀ g, zg.z1h K E (r g) I-I = b g:=by
  let J:FractionalIdeal (𝓞 E)⁰ E:=∑ g:G, (b g).toMul.1
  have hJ:J ≠ 0:=by
    intro h
    have hh:(b 1).toMul.1 ≤ J:=Finset.single_le_sum (f:=fun g:G => (b g).toMul.1) (fun g _ => zero_le) (Finset.mem_univ (1:G))
    rw [h] at hh
    exact (b 1).toMul.ne_zero (le_antisymm hh (zero_le))
  let j:Ideals E:=Units.mk0 J hJ
  have hj (g:G):(b g).toMul.1 * actionHom E (r g).toRingEquiv J = J:=by
    change (b g).toMul.1 * actionHom E (r g).toRingEquiv (∑ h:G, (b h).toMul.1) = _
    rw [map_sum,Finset.mul_sum]
    calc
      (∑ h:G, (b g).toMul.1 * actionHom E (r g).toRingEquiv (b h).toMul.1) =
          ∑ h:G, (b (g*h)).toMul.1:=by
        apply Finset.sum_congr rfl
        intro h _
        have hh:=congrArg (fun z:D E => z.toMul.1) (hb g h)
        change (b (g*h)).toMul.1 = actionHom E (r g).toRingEquiv (b h).toMul.1 * (b g).toMul.1 at hh
        rw [hh,mul_comm]
      _ = J:=by exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => (b h).toMul.1)
  refine ⟨-Additive.ofMul j,?_⟩
  intro g
  have hh:b g+zg.z1h K E (r g) (Additive.ofMul j) = Additive.ofMul j:=by
    apply Additive.toMul.injective
    exact Units.ext (hj g)
  rw [map_neg]
  have hh':=eq_sub_of_add_eq hh
  rw [hh']
  abel
end zg
namespace z10
open NumberField
open scoped Classical nonZeroDivisors
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  (σ:K ≃+* K) (τ:E ≃+* E)
  (hcomm:∀ x, τ (algebraMap K E x) = algebraMap K E (σ x))
include hcomm in
lemma z7x (I:FractionalIdeal (𝓞 K)⁰ K) (x:E)
    (hx:x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) I) :
    τ x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) (actionHom K σ I):=by
  change x ∈ ((FractionalIdeal.extendedHom E (𝓞 E) I):Submodule (𝓞 E) E) at hx
  change τ x ∈ ((FractionalIdeal.extendedHom E (𝓞 E) (actionHom K σ I)):Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHom_eq_span] at hx ⊢
  refine Submodule.span_induction (p:=fun x _ => τ x ∈
    Submodule.span (𝓞 E) (algebraMap K E '' (actionHom K σ I:Set K))) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y,hy,rfl⟩
    rw [hcomm]
    refine Submodule.subset_span ⟨σ y,?_,rfl⟩
    exact (z29 K σ I (σ y)).mpr (by rw [RingEquiv.symm_apply_apply]; exact hy)
  · simpa only [map_zero] using Submodule.zero_mem _
  · intro a b ha hb h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro a b hb h
    change τ ((a:E)*b) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _ (RingOfIntegers.mapRingEquiv τ a) h
include hcomm in
lemma z9m (I:Ideals K) :
    action E τ (extend K E I) = extend K E (action K σ I):=by
  have hi (x:K):τ.symm (algebraMap K E x) = algebraMap K E (σ.symm x):=by
    apply τ.injective
    rw [RingEquiv.apply_symm_apply,hcomm,RingEquiv.apply_symm_apply]
  apply Units.ext
  ext x
  change x ∈ actionHom E τ (FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) ↔
    x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) (actionHom K σ I.1)
  rw [z29]
  constructor
  · intro hx
    simpa only [RingEquiv.apply_symm_apply] using
      z7x K E σ τ hcomm I.1 (τ.symm x) hx
  · intro hx
    have h:=z7x K E σ.symm τ.symm hi (actionHom K σ I.1) x hx
    rwa [z67] at h
end z10
namespace zg
open NumberField z7 z10
open scoped Classical nonZeroDivisors
variable (K M E:Type) [Field K] [Field M] [Field E]
  [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M]
noncomputable def z26:F M →+ F E:=MonoidHom.toAdditive (zcm M E)
noncomputable def z1u:D M →+ D E:=MonoidHom.toAdditive (extend M E)
lemma zb8:Function.Injective (z26 M E):=by
  exact Units.map_injective (algebraMap M E).injective
lemma z4a:Function.Injective (z1u M E):=extend_injective M E
lemma z9p (σ:Gal(E/K)) (x:F M) :
    z26 M E (zg.z15 K M (AlgEquiv.restrictNormalHom M σ) x) =
      zg.z15 K E σ (z26 M E x):=by
  apply Additive.toMul.injective
  apply Units.ext
  exact σ.restrictNormal_commutes M x.toMul
lemma z5d (σ:Gal(E/K)) (I:D M) :
    z1u M E (zg.z1h K M (AlgEquiv.restrictNormalHom M σ) I) =
      zg.z1h K E σ (z1u M E I):=by
  exact congrArg Additive.ofMul (z9m M E (σ.restrictNormal M).toRingEquiv σ.toRingEquiv
    (fun x => (σ.restrictNormal_commutes M x).symm) I.toMul).symm
lemma z86 (x:F M) :
    z4.z11 E (z26 M E x) =
      z1u M E (z4.z11 M x):=by
  exact congrArg Additive.ofMul (z58 M E x.toMul).symm
end zg
namespace z1n
open scoped Classical
variable {G Q A:Type*} [Group G] [Group Q] [AddCommGroup A]
  (ρ:G →* AddAut A)
def z53 (b:G → A):Prop:=∀ g h, b (g*h) = ρ g (b h)+b g
def z1v:Prop:=∀ b:G → A, z53 ρ b → ∃ a, ∀ g, ρ g a-a = b g
lemma zck {f t:G → G → A} (hf:IsCocycle ρ f) (ht:IsCocycle ρ t) :
    IsCocycle ρ (fun g h => f g h+t g h):=by
  intro g h k
  simp only [map_add]
  calc
    _ = (ρ g (f h k)+f g (h*k))+(ρ g (t h k)+t g (h*k)):=by abel
    _ = (f g h+f (g*h) k)+(t g h+t (g*h) k):=by rw [hf,ht]
    _ = _:=by abel
lemma z5r (b c:G → A) (g h:G) :
    boundary ρ (fun g => b g+c g) g h = boundary ρ b g h+boundary ρ c g h:=by
  simp only [boundary,map_add]
  abel
lemma z8h (q:G →* Q) (hq:Function.Surjective q) :
    ∃ r:Q → G, r 1 = 1 ∧ ∀ x, q (r x) = x:=by
  let r:Q → G:=fun x => if x = 1 then 1 else (hq x).choose
  refine ⟨r,by simp [r],?_⟩
  intro x
  by_cases hx:x = 1
  · simp [r,hx]
  · simpa [r,hx] using (hq x).choose_spec
lemma zjc (q:G →* Q) (r:Q → G) (hr1:r 1 = 1) (hr:∀ x, q (r x) = x)
    {f:G → G → A} (hf:IsCocycle ρ f)
    (hzero:∀ h k, q h = 1 → q k = 1 → f h k = 0) :
    ∃ b:G → A, ∀ h g, q h = 1 → f h g+boundary ρ b h g = 0:=by
  let b:G → A:=fun g => f (g*(r (q g))⁻¹) (r (q g))
  refine ⟨b,?_⟩
  intro h g hh
  have h₁:f 1 1 = 0:=hzero 1 1 (map_one q) (map_one q)
  have bh:b h = 0:=by
    simp only [b,hh,hr1,inv_one,mul_one]
    rw [z6o ρ hf,h₁,map_zero]
  have hk:q (g*(r (q g))⁻¹) = 1:=by simp [hr]
  have hp:(g*(r (q g))⁻¹)*r (q g) = g:=by group
  have hb:b (h*g) = f (h*(g*(r (q g))⁻¹)) (r (q g)):=by
    simp only [b,map_mul,hh,one_mul,mul_assoc]
  have he:=hf h (g*(r (q g))⁻¹) (r (q g))
  rw [hp,hzero h _ hh hk,zero_add] at he
  change ρ h (b g)+f h g = _ at he
  rw [← hb] at he
  simp only [boundary,bh,add_zero]
  rw [← he]
  abel
lemma z8n (q:G →* Q) {f:G → G → A} (hf:IsCocycle ρ f)
    (hz:∀ h g, q h = 1 → f h g = 0) (h g k:G) (hh:q h = 1) :
    f (h*g) k = ρ h (f g k):=by
  have he:=hf h g k
  rw [hz h _ hh,hz h _ hh,add_zero,zero_add] at he
  exact he.symm
lemma zfr (q:G →* Q) {f:G → G → A} (hf:IsCocycle ρ f)
    (hz:∀ h g, q h = 1 → f h g = 0) (g:G) :
    z53 (ρ.comp q.ker.subtype) (fun h:q.ker => f g (g⁻¹*h*g)):=by
  intro h k
  have hq:q h = 1:=h.property
  have hh:q (g⁻¹*h*g) = 1:=by simp only [map_mul,map_inv,hq,mul_one,inv_mul_cancel]
  have hp:(g⁻¹*(h*k:q.ker)*g) = (g⁻¹*h*g)*(g⁻¹*k*g):=by
    change g⁻¹*((h:G)*(k:G))*g = _
    group
  have he:=hf g (g⁻¹*h*g) (g⁻¹*k*g)
  rw [hz _ _ hh,map_zero,zero_add,← hp] at he
  have hgh:g*(g⁻¹*h*g) = (h:G)*g:=by group
  rw [hgh,z8n ρ q hf hz h g _ h.property] at he
  change f g (g⁻¹*(h*k:q.ker)*g) = ρ h (f g (g⁻¹*k*g))+f g (g⁻¹*h*g)
  exact he.trans (add_comm _ _)
lemma zj7 (q:G →* Q) (r:Q → G) (hr1:r 1 = 1) (hr:∀ x, q (r x) = x)
    (hH1:z1v (ρ.comp q.ker.subtype))
    {f:G → G → A} (hf:IsCocycle ρ f)
    (hz:∀ h g, q h = 1 → f h g = 0) :
    ∃ b:G → A, (∀ h g, q h = 1 → f h g+boundary ρ b h g = 0) ∧
      (∀ g h, q h = 1 → f g h+boundary ρ b g h = 0):=by
  have hex (x:Q):∃ a:A, ∀ h:q.ker,
      ρ h a-a = f (r x) ((r x)⁻¹*h*r x) :=
    hH1 _ (zfr ρ q hf hz (r x))
  let a:Q → A:=fun x => if x = 1 then 0 else (hex x).choose
  have ha1:a 1 = 0:=by simp [a]
  have ha (x:Q) (h:G) (hh:q h = 1) :
      ρ h (a x)-a x = f (r x) ((r x)⁻¹*h*r x):=by
    by_cases hx:x = 1
    · subst x
      rw [ha1,map_zero,sub_self,hr1,hz 1 _ (map_one q)]
    · simpa only [a,if_neg hx] using (hex x).choose_spec ⟨h,hh⟩
  let k:G → G:=fun g => g*(r (q g))⁻¹
  have hk (g:G):q (k g) = 1:=by simp [k,hr]
  have hkr (g:G):k g*r (q g) = g:=by simp [k]
  let b:G → A:=fun g => ρ (k g) (a (q g))
  have bh (h:G) (hh:q h = 1):b h = 0:=by simp [b,hh,ha1]
  have bc (h g:G) (hh:q h = 1):b (h*g) = ρ h (b g):=by
    simp only [b,k,map_mul,hh,one_mul]
    rw [mul_assoc]; rfl
  have hd (g h:G) (hh:q h = 1) :
      f g (g⁻¹*h*g) = ρ h (b g)-b g:=by
    have hkh:q ((k g)⁻¹*h*k g) = 1:=by simp [hh,hk]
    have ht:(r (q g))⁻¹*((k g)⁻¹*h*k g)*r (q g) = g⁻¹*h*g:=by
      simp only [k]
      group
    have he:=ha (q g) ((k g)⁻¹*h*k g) hkh
    rw [ht] at he
    have hc:=z8n ρ q hf hz (k g) (r (q g)) (g⁻¹*h*g) (hk g)
    rw [hkr,← he,map_sub] at hc
    rw [hc]
    change ρ (k g) (ρ ((k g)⁻¹*h*k g) (a (q g)))-ρ (k g) (a (q g)) =
      ρ h (ρ (k g) (a (q g)))-ρ (k g) (a (q g))
    congr 1
    rw [← z8o,← z8o]
    congr 2
    group
  refine ⟨b,?_,?_⟩
  · intro h g hh
    rw [hz h g hh,boundary,bh h hh,bc h g hh]
    abel
  · intro g h hh
    have hgh:q (g*h*g⁻¹) = 1:=by simp [hh]
    have he:=hd g (g*h*g⁻¹) hgh
    have ht:g⁻¹*(g*h*g⁻¹)*g = h:=by group
    rw [ht] at he
    have hb:b (g*h) = ρ (g*h*g⁻¹) (b g):=by
      convert bc (g*h*g⁻¹) g hgh using 1
      group
    rw [boundary,bh h hh,map_zero,zero_sub,hb,he]
    abel
def Horizontal (q:G →* Q) (f:G → G → A):Prop :=
  (∀ h g, q h = 1 → f h g = 0) ∧ (∀ g h, q h = 1 → f g h = 0)
lemma zgu (q:G →* Q) (hq:Function.Surjective q)
    (hH1:z1v (ρ.comp q.ker.subtype))
    {f:G → G → A} (hf:IsCocycle ρ f)
    (hres:IsCoboundary (ρ.comp q.ker.subtype) (fun h k:q.ker => f h k)) :
    ∃ b:G → A, Horizontal q (fun g h => f g h+boundary ρ b g h):=by
  obtain ⟨r,hr1,hr⟩:=z8h q hq
  obtain ⟨t,ht⟩:=hres
  let d:G → A:=fun g => if hg:q g = 1 then -t ⟨g,hg⟩ else 0
  have hd (h:q.ker):d h = -t h:=by
    have hh:q h = 1:=h.property
    simp only [d,dif_pos hh]
  let f₀:G → G → A:=fun g h => f g h+boundary ρ d g h
  have hf₀:IsCocycle ρ f₀:=zck ρ hf (z5a ρ d)
  have hz₀ (g h:G) (hg:q g = 1) (hh:q h = 1):f₀ g h = 0:=by
    let g':q.ker:=⟨g,hg⟩
    let h':q.ker:=⟨h,hh⟩
    have he:f g h = boundary (ρ.comp q.ker.subtype) t g' h' :=
      congrFun (congrFun ht g') h'
    change f g h+(ρ g (d h)-d (g*h)+d g) = 0
    rw [show d g = -t g' from hd g',show d h = -t h' from hd h',
      show d (g*h) = -t (g'*h') from hd (g'*h'),he,map_neg]
    change (ρ g (t h')-t (g'*h')+t g')+(-ρ g (t h')- -t (g'*h')+-t g') = 0
    abel
  obtain ⟨b₁,hb₁⟩:=zjc ρ q r hr1 hr hf₀ hz₀
  let f₁:G → G → A:=fun g h => f₀ g h+boundary ρ b₁ g h
  have hf₁:IsCocycle ρ f₁:=zck ρ hf₀ (z5a ρ b₁)
  obtain ⟨b₂,hb₂,hb₂'⟩:=zj7 ρ q r hr1 hr hH1 hf₁ hb₁
  let b:G → A:=fun g => (d g+b₁ g)+b₂ g
  have he (g h:G):f g h+boundary ρ b g h = f₁ g h+boundary ρ b₂ g h:=by
    simp only [b,z5r,f₁,f₀]
    abel
  refine ⟨b,?_,?_⟩
  · intro h g hh
    exact (he h g).trans (hb₂ h g hh)
  · intro g h hh
    exact (he g h).trans (hb₂' g h hh)
end z1n
namespace z1n
open scoped Classical
variable {G Q A A₀:Type*} [Group G] [Group Q] [AddCommGroup A] [AddCommGroup A₀]
  (ρ:G →* AddAut A) (q:G →* Q)
lemma ze9 {f:G → G → A} (hf:IsCocycle ρ f) (hz:Horizontal q f)
    (g k h:G) (hh:q h = 1):f g (k*h) = f g k:=by
  have he:=hf g k h
  rw [hz.2 k h hh,hz.2 (g*k) h hh,map_zero,zero_add,add_zero] at he
  exact he
lemma z85 {f:G → G → A} (hf:IsCocycle ρ f) (hz:Horizontal q f)
    (g h k:G) (heq:q h = q k):f g h = f g k:=by
  have hk:q (k⁻¹*h) = 1:=by simp [heq]
  convert ze9 ρ q hf hz g k (k⁻¹*h) hk using 1
  group
lemma z92 {f:G → G → A} (hf:IsCocycle ρ f) (hz:Horizontal q f)
    (g h k:G) (heq:q g = q h):f g k = f h k:=by
  have hk:q (h⁻¹*g) = 1:=by simp [heq]
  have he:=hf h (h⁻¹*g) k
  rw [hz.1 _ _ hk,hz.2 _ _ hk,map_zero,zero_add,zero_add] at he
  have hp:h*(h⁻¹*g) = g:=by group
  rw [hp] at he
  rw [← he]
  apply z85 ρ q hf hz
  simp [hk]
lemma zhi {f:G → G → A} (hf:IsCocycle ρ f) (hz:Horizontal q f)
    (g k h:G) (hh:q h = 1):ρ h (f g k) = f g k:=by
  rw [← z8n ρ q hf hz.1 h g k hh]
  apply z92 ρ q hf hz
  simp [hh]
variable (ρ₀:Q →* AddAut A₀) (e:A₀ →+ A)
  (hei:Function.Injective e)
  (hee:∀ g x, e (ρ₀ (q g) x) = ρ g (e x))
  (hes:∀ a:A, (∀ h:G, q h = 1 → ρ h a = a) → ∃ x:A₀, e x = a)
include hei hee hes in
lemma ziy (hq:Function.Surjective q)
    {f:G → G → A} (hf:IsCocycle ρ f) (hz:Horizontal q f) :
    ∃ f₀:Q → Q → A₀, IsCocycle ρ₀ f₀ ∧ ∀ g h, e (f₀ (q g) (q h)) = f g h:=by
  obtain ⟨r,hr1,hr⟩:=z8h q hq
  have hex (x y:Q):∃ a:A₀, e a = f (r x) (r y) :=
    hes _ (zhi ρ q hf hz (r x) (r y))
  let f₀:Q → Q → A₀:=fun x y => (hex x y).choose
  have he (g h:G):e (f₀ (q g) (q h)) = f g h:=by
    change e (hex (q g) (q h)).choose = _
    rw [(hex (q g) (q h)).choose_spec]
    exact (z92 ρ q hf hz _ _ _ (hr (q g))).trans
      (z85 ρ q hf hz _ _ _ (hr (q h)))
  refine ⟨f₀,?_,he⟩
  intro x y z
  obtain ⟨g,rfl⟩:=hq x
  obtain ⟨h,rfl⟩:=hq y
  obtain ⟨k,rfl⟩:=hq z
  apply hei
  rw [map_add,map_add,hee,he,← map_mul,← map_mul,he,he,he]
  exact hf g h k
lemma zf1 (a:A) (g h:G) :
    boundary ρ (fun g => ρ g a-a) g h = 0:=by
  simp only [boundary,map_sub,z8o]
  abel
include hei hee hes in
lemma zfn (hq:Function.Surjective q)
    (hH1:z1v (ρ.comp q.ker.subtype))
    {f:G → G → A} (hz:Horizontal q f) (hb:IsCoboundary ρ f)
    {f₀:Q → Q → A₀} (he:∀ g h, e (f₀ (q g) (q h)) = f g h) :
    IsCoboundary ρ₀ f₀:=by
  obtain ⟨b,hb⟩:=hb
  have hb' (g h:G):f g h = boundary ρ b g h:=congrFun (congrFun hb g) h
  have hc:z53 (ρ.comp q.ker.subtype) (fun h:q.ker => b h):=by
    intro g h
    have he₁:=hb' g h
    rw [hz.1 g _ g.property] at he₁
    change 0 = ρ g (b h)-b (g*h)+b g at he₁
    exact (eq_of_sub_eq_zero (show b (g*h)-(ρ g (b h)+b g) = 0 by
      calc
        _ = -(ρ g (b h)-b (g*h)+b g):=by abel
        _ = 0:=by rw [← he₁,neg_zero]))
  obtain ⟨a,ha⟩:=hH1 _ hc
  let c:G → A:=fun g => b g-(ρ g a-a)
  have ch (h:G) (hh:q h = 1):c h = 0:=by
    have he:=ha ⟨h,hh⟩
    change ρ h a-a = b h at he
    simp [c,he]
  have cb (g h:G):boundary ρ c g h = f g h:=by
    rw [hb' g h]
    change (ρ g (b h-(ρ h a-a))-(b (g*h)-(ρ (g*h) a-a))+(b g-(ρ g a-a))) = _
    simp only [map_sub,z8o,boundary]
    abel
  have cr (g h:G) (hh:q h = 1):c (g*h) = c g:=by
    have he:=cb g h
    rw [hz.2 g h hh,boundary,ch h hh,map_zero,zero_sub] at he
    exact (sub_eq_zero.mp (show c g-c (g*h) = 0 by convert he using 1 <;> abel)).symm
  have ce (g h:G) (heq:q g = q h):c g = c h:=by
    have hk:q (h⁻¹*g) = 1:=by simp [heq]
    convert cr h (h⁻¹*g) hk using 1
    group
  have cf (g h:G) (hh:q h = 1):ρ h (c g) = c g:=by
    have he:=cb h g
    rw [hz.1 h g hh,boundary,ch h hh,add_zero,ce (h*g) g (by simp [hh])] at he
    exact sub_eq_zero.mp he
  obtain ⟨r,hr1,hr⟩:=z8h q hq
  have hex (x:Q):∃ a:A₀, e a = c (r x):=hes _ (cf (r x))
  let c₀:Q → A₀:=fun x => (hex x).choose
  have ec (g:G):e (c₀ (q g)) = c g:=by
    exact (hex (q g)).choose_spec.trans (ce _ _ (hr (q g)))
  refine ⟨c₀,?_⟩
  funext x y
  obtain ⟨g,rfl⟩:=hq x
  obtain ⟨h,rfl⟩:=hq y
  apply hei
  rw [he,boundary,map_add,map_sub,hee,ec,← map_mul,ec,ec]
  exact (cb g h).symm
end z1n
namespace z1n
open scoped Classical
variable {G Q A B A₀ B₀:Type*} [Group G] [Group Q]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup A₀] [AddCommGroup B₀]
  (ρ:G →* AddAut A) (τ:G →* AddAut B) (p:A →+ B)
  (hp:∀ g a, p (ρ g a) = τ g (p a))
include hp in
lemma zlq (b:G → A) (g h:G) :
    p (boundary ρ b g h) = boundary τ (fun g => p (b g)) g h:=by
  simp only [boundary,map_add,map_sub,hp]
include hp in
lemma zjg {f:G → G → A} (hf:IsCoboundary ρ f) :
    IsCoboundary τ (fun g h => p (f g h)):=by
  obtain ⟨b,rfl⟩:=hf
  exact ⟨fun g => p (b g),funext fun g => funext fun h => zlq ρ τ p hp b g h⟩
lemma zjd {f t:G → G → A}
    (hf:IsCoboundary ρ f) (ht:IsCoboundary ρ t) :
    IsCoboundary ρ (fun g h => f g h+t g h):=by
  obtain ⟨b,rfl⟩:=hf
  obtain ⟨c,rfl⟩:=ht
  exact ⟨fun g => b g+c g,funext fun g => funext fun h => (z5r ρ b c g h).symm⟩
lemma zbm {f:G → G → A} (hf:IsCoboundary ρ f) (c:G → A) :
    IsCoboundary ρ (fun g h => f g h-boundary ρ c g h):=by
  obtain ⟨b,rfl⟩:=hf
  refine ⟨fun g => b g-c g,?_⟩
  funext g h
  simp only [boundary,map_sub]
  abel
def z1q:Prop :=
  ∀ f:G → G → A, IsCocycle ρ f → IsCoboundary τ (fun g h => p (f g h)) → IsCoboundary ρ f
include hp in
lemma z8f (q:G →* Q) (hq:Function.Surjective q)
    (ρ₀:Q →* AddAut A₀) (τ₀:Q →* AddAut B₀) (p₀:A₀ →+ B₀)
    (eA:A₀ →+ A) (eB:B₀ →+ B)
    (heiA:Function.Injective eA) (heiB:Function.Injective eB)
    (heeA:∀ g x, eA (ρ₀ (q g) x) = ρ g (eA x))
    (heeB:∀ g x, eB (τ₀ (q g) x) = τ g (eB x))
    (hesA:∀ a:A, (∀ h:G, q h = 1 → ρ h a = a) → ∃ x:A₀, eA x = a)
    (hesB:∀ a:B, (∀ h:G, q h = 1 → τ h a = a) → ∃ x:B₀, eB x = a)
    (hcomm:∀ x, p (eA x) = eB (p₀ x))
    (hH1A:z1v (ρ.comp q.ker.subtype))
    (hH1B:z1v (τ.comp q.ker.subtype))
    (hH2ker:z1q (ρ.comp q.ker.subtype) (τ.comp q.ker.subtype) p)
    (hH2quot:z1q ρ₀ τ₀ p₀):z1q ρ τ p:=by
  intro f hf hb
  have hres:IsCoboundary (ρ.comp q.ker.subtype) (fun g h:q.ker => f g h):=by
    apply hH2ker
    · intro g h k
      exact hf g h k
    · obtain ⟨b,hb⟩:=hb
      refine ⟨fun g:q.ker => b g,?_⟩
      funext g h
      exact congrFun (congrFun hb g) h
  obtain ⟨d,hd⟩:=zgu ρ q hq hH1A hf hres
  let f':G → G → A:=fun g h => f g h+boundary ρ d g h
  have hf':IsCocycle ρ f':=zck ρ hf (z5a ρ d)
  have hb':IsCoboundary τ (fun g h => p (f' g h)):=by
    have hb₂:IsCoboundary τ (fun g h => p (boundary ρ d g h)) :=
      zjg ρ τ p hp ⟨d,rfl⟩
    simpa only [f',map_add] using zjd τ hb hb₂
  obtain ⟨f₀,hf₀,he₀⟩:=ziy ρ q ρ₀ eA heiA heeA hesA hq hf' hd
  have hzB:Horizontal q (fun g h => p (f' g h)):=by
    constructor
    · intro h g hh
      exact (congrArg p (hd.1 h g hh)).trans (map_zero p)
    · intro g h hh
      exact (congrArg p (hd.2 g h hh)).trans (map_zero p)
  have heB (g h:G):eB (p₀ (f₀ (q g) (q h))) = p (f' g h):=by
    rw [← hcomm,he₀]
  have hB₀:IsCoboundary τ₀ (fun g h => p₀ (f₀ g h)) :=
    zfn τ q τ₀ eB heiB heeB hesB hq hH1B hzB hb' heB
  obtain ⟨a,ha⟩:=hH2quot f₀ hf₀ hB₀
  have hc:IsCoboundary ρ f':=by
    refine ⟨fun g => eA (a (q g)),?_⟩
    funext g h
    rw [← he₀,ha,boundary,map_add,map_sub,heeA,← map_mul]
    rfl
  have hc':=zbm ρ hc d
  simpa only [f',add_sub_cancel_right] using hc'
end z1n
namespace z1n
open scoped Classical
variable {G H A B:Type*} [Group G] [Group H] [AddCommGroup A] [AddCommGroup B]
  (ρ:G →* AddAut A) (τ:G →* AddAut B) (p:A →+ B) (e:H ≃* G)
lemma z1v.comp_equiv (hρ:z1v ρ):z1v (ρ.comp e.toMonoidHom):=by
  intro b hb
  have hc:z53 ρ (fun g => b (e.symm g)):=by
    intro g h
    simpa only [map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
      using hb (e.symm g) (e.symm h)
  obtain ⟨a,ha⟩:=hρ _ hc
  refine ⟨a,?_⟩
  intro h
  simpa only [MulEquiv.symm_apply_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using ha (e h)
lemma z1q.comp_equiv (hρ:z1q ρ τ p) :
    z1q (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom) p:=by
  intro f hf hb
  let f':G → G → A:=fun g h => f (e.symm g) (e.symm h)
  have hf':IsCocycle ρ f':=by
    intro g h k
    simpa only [f',map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
      using hf (e.symm g) (e.symm h) (e.symm k)
  have hb':IsCoboundary τ (fun g h => p (f' g h)):=by
    obtain ⟨b,hb⟩:=hb
    refine ⟨fun g => b (e.symm g),?_⟩
    funext g h
    have he:=congrFun (congrFun hb (e.symm g)) (e.symm h)
    simpa only [f',boundary,map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using he
  obtain ⟨b,hb⟩:=hρ f' hf' hb'
  refine ⟨fun h => b (e h),?_⟩
  funext g h
  have he:=congrFun (congrFun hb (e g)) (e h)
  simpa only [f',boundary,map_mul,MulEquiv.symm_apply_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using he
end z1n
namespace zg
open NumberField z7 z10 z1n
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E]
lemma zc0:z1v (z15 K E):=by
  intro b hb
  have hm:groupCohomology.IsMulCocycle₁ (fun g:Gal(E/K) => (b g).toMul):=by
    intro g h
    exact congrArg Additive.toMul (hb g h)
  obtain ⟨a,ha⟩:=groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hm
  refine ⟨Additive.ofMul a,?_⟩
  intro g
  exact congrArg Additive.ofMul (ha g)
variable (M:IntermediateField K E) [Normal K M]
noncomputable def z2z:(AlgEquiv.restrictNormalHom (F:=K) (K₁:=E) M).ker ≃* Gal(E/M) :=
  (MulEquiv.subgroupCongr M.restrictNormalHom_ker).trans (IntermediateField.fixingSubgroupEquiv M)
variable [NumberField M]
lemma zcn :
    z1v ((z15 K E).comp (AlgEquiv.restrictNormalHom (F:=K) (K₁:=E) M).ker.subtype):=by
  change z1v ((z15 M E).comp (z2z K E M).toMonoidHom)
  exact z1v.comp_equiv (z15 M E) (z2z K E M) (zc0 M E)
lemma zca :
    z1v ((z1h K E).comp (AlgEquiv.restrictNormalHom (F:=K) (K₁:=E) M).ker.subtype):=by
  intro b hb
  exact zbs K E _ b hb
variable [IsGalois M E] [IsTotallyReal M] [IsTotallyReal E]
  (σ:Gal(E/M)) (hdeg:Module.finrank M E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 M) (𝓞 E) = ⊤)
include σ hdeg hne hunram in
lemma z9w :
    z1q
      ((z15 K E).comp (AlgEquiv.restrictNormalHom (F:=K) (K₁:=E) M).ker.subtype)
      ((z1h K E).comp (AlgEquiv.restrictNormalHom (F:=K) (K₁:=E) M).ker.subtype)
      (z4.z11 E).toAddMonoidHom:=by
  change z1q ((z15 M E).comp (z2z K E M).toMonoidHom)
    ((z1h M E).comp (z2z K E M).toMonoidHom) _
  apply z1q.comp_equiv
  intro f hf hb
  exact z24.z90 M E σ hdeg hne hunram hf hb
include hdeg hne in
lemma ze5 (a:F E)
    (ha:∀ g:Gal(E/K), AlgEquiv.restrictNormalHom M g = 1 → z15 K E g a = a) :
    ∃ x:F M, z26 M E x = a:=by
  have haσ:z3g M E σ a = a:=ha ((z2z K E M).symm σ).1 ((z2z K E M).symm σ).property
  let af:z9.plus (z3g M E σ):=⟨a,(z9.z1g _ _).mpr haσ⟩
  obtain ⟨x,hx⟩:=(z4.z42 M E σ hdeg hne).surjective af
  exact ⟨x,congrArg Subtype.val hx⟩
include hdeg hne hunram in
lemma zdm (a:D E)
    (ha:∀ g:Gal(E/K), AlgEquiv.restrictNormalHom M g = 1 → z1h K E g a = a) :
    ∃ x:D M, z1u M E x = a:=by
  have haσ:z22 M E σ a = a:=ha ((z2z K E M).symm σ).1 ((z2z K E M).symm σ).property
  let af:z9.plus (z22 M E σ):=⟨a,(z9.z1g _ _).mpr haσ⟩
  obtain ⟨x,hx⟩:=(z4.z2v M E σ hdeg hne hunram).surjective af
  exact ⟨x,congrArg Subtype.val hx⟩
end zg
namespace zg
open NumberField z7 z10 z1n
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal E]
  (M:IntermediateField K E) [Normal K M] [NumberField M] [IsTotallyReal M]
  (σ:Gal(E/M)) (hdeg:Module.finrank M E = 2) (hne:σ ≠ 1)
  (hunram:differentIdeal (𝓞 M) (𝓞 E) = ⊤)
include σ hdeg hne hunram in
lemma zdd
    (hM:z1q (z15 K M) (z1h K M)
      (z4.z11 M).toAddMonoidHom) :
    z1q (z15 K E) (z1h K E)
      (z4.z11 E).toAddMonoidHom:=by
  exact z8f (z15 K E) (z1h K E)
    (z4.z11 E).toAddMonoidHom (z4w K E)
    (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
    (z15 K M) (z1h K M) (z4.z11 M).toAddMonoidHom
    (z26 M E) (z1u M E)
    (zb8 M E) (z4a M E)
    (z9p K M E) (z5d K M E)
    (ze5 K E M σ hdeg hne) (zdm K E M σ hdeg hne hunram)
    (z86 M E)
    (zcn K E M) (zca K E M)
    (z9w K E M σ hdeg hne hunram) hM
end zg
namespace z75
open scoped Classical
variable (G:Type*) [Group G] [Finite G] [Nontrivial G]
lemma za3 (hG:IsPGroup 2 G) :
    ∃ H:Subgroup G, H.Normal ∧ Nat.card H = 2:=by
  letI:Fact (Nat.Prime 2):=⟨by norm_num⟩
  letI:=hG.center_nontrivial
  obtain ⟨n,hn,he⟩:=(hG.to_subgroup (Subgroup.center G)).nontrivial_iff_card.mp inferInstance
  have hd:2 ∣ Nat.card (Subgroup.center G):=by
    rw [he]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨s,hs⟩:=exists_prime_orderOf_dvd_card' (G:=Subgroup.center G) 2 hd
  let H:=Subgroup.zpowers (s:G)
  have hcent:H ≤ Subgroup.center G:=Subgroup.zpowers_le.mpr s.property
  refine ⟨H,?_,?_⟩
  · refine ⟨?_⟩
    intro n hn g
    have hc:=(Subgroup.mem_center_iff.mp (hcent hn)) g
    simpa only [hc,mul_assoc,mul_inv_cancel,mul_one] using hn
  · change Nat.card (Subgroup.zpowers (s:G)) = 2
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.center G).subtype Subtype.val_injective s).trans hs
end z75
namespace z4q
open NumberField
variable (K M E:Type*) [Field K] [Field M] [Field E] [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
lemma zeh (h:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    differentIdeal (𝓞 M) (𝓞 E) = ⊤ ∧ differentIdeal (𝓞 K) (𝓞 M) = ⊤:=by
  have ht:=differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 M) (𝓞 E)
  have h₁:differentIdeal (𝓞 M) (𝓞 E) = ⊤:=by
    apply top_unique
    rw [← h,ht]
    exact Ideal.mul_le_left
  have h₂:Ideal.map (algebraMap (𝓞 M) (𝓞 E)) (differentIdeal (𝓞 K) (𝓞 M)) = ⊤:=by
    apply top_unique
    rw [← h,ht]
    exact Ideal.mul_le_right
  refine ⟨h₁,?_⟩
  exact (Ideal.map_eq_top_iff (algebraMap (𝓞 M) (𝓞 E))
    (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp h₂
end z4q
namespace z1n
variable {G A:Type*} [Group G] [AddCommGroup A]
lemma zbf [Subsingleton G] (ρ:G →* AddAut A) (f:G → G → A) :
    IsCoboundary ρ f:=by
  refine ⟨fun _ => f 1 1,?_⟩
  funext g h
  have hg:g = 1:=Subsingleton.elim _ _
  have hh:h = 1:=Subsingleton.elim _ _
  subst g h
  simp [boundary]
end z1n
namespace zg
open NumberField z7 z10 z1n
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]
lemma z9n (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    z1q (z15 K E) (z1h K E)
      (z4.z11 E).toAddMonoidHom:=by
  generalize hn:Module.finrank K E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    rcases subsingleton_or_nontrivial Gal(E/K) with htriv | hnontriv
    · letI:=htriv
      intro f hf hb
      exact zbf _ _
    · letI:=hnontriv
      obtain ⟨H,hH,hcard⟩:=z75.za3 Gal(E/K) hG
      letI:=hH
      let M:=IntermediateField.fixedField H
      letI:NumberField M:=NumberField.of_module_finite ℚ M
      letI:IsTotallyReal M:=IsTotallyReal.of_algebra M E
      have hdeg:Module.finrank M E = 2:=by
        exact (IntermediateField.finrank_fixedField_eq_card H).trans hcard
      have hMlt:Module.finrank K M < n:=by
        have he:=Module.finrank_mul_finrank K M E
        rw [hdeg,hn] at he
        have hp:0 < Module.finrank K M:=Module.finrank_pos
        omega
      have hGM:IsPGroup 2 Gal(M/K) :=
        hG.of_surjective (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
      have hu:=z4q.zeh K M E hunram
      have hM:=ih (Module.finrank K M) hMlt M hGM hu.2 rfl
      have hc:Nat.card Gal(E/M) = 2:=(IsGalois.card_aut_eq_finrank M E).trans hdeg
      letI:Nontrivial Gal(E/M):=Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨σ,hσ⟩:=exists_ne (1:Gal(E/M))
      exact zdd K E M σ hdeg hσ hu.1 hM
end zg
namespace z10
open NumberField
open scoped Classical nonZeroDivisors
variable (E:Type*) [Field E] [NumberField E]
lemma zhs:Function.Injective (fun I:Ideals E => I*I):=by
  intro I J h
  apply Units.ext
  have hs:I.1*I.1 = J.1*J.1:=congrArg Units.val h
  have hsum:I.1+J.1 ≠ 0:=by
    intro hz
    have hle:I.1 ≤ I.1+J.1:=le_add_of_nonneg_right (zero_le)
    rw [hz] at hle
    exact I.ne_zero (le_antisymm hle (zero_le))
  apply mul_left_cancel₀ hsum
  calc
    (I.1+J.1)*I.1 = I.1*I.1+I.1*J.1:=by ring
    _ = J.1*J.1+I.1*J.1:=by rw [hs]
    _ = (I.1+J.1)*J.1:=by ring
lemma zi7:Function.Injective (fun I:Additive (Ideals E) => I+I):=by
  intro I J h
  apply Additive.toMul.injective
  exact zhs E (congrArg Additive.toMul h)
end z10
namespace z6
open scoped Classical
variable {A B:Type*} [AddCommGroup A] [AddCommGroup B]
abbrev V (A:Type*) [AddCommGroup A]:=ModN A 2
abbrev mk:A →+ V A:=ModN.mkQ 2
lemma mk_surjective:Function.Surjective (mk (A:=A)) :=
  (LinearMap.range (LinearMap.lsmul ℤ A (2:ℤ))).mkQ_surjective
lemma mk_eq_zero (a:A):mk a = 0 ↔ ∃ b:A, b+b = a:=by
  change Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change (∃ b:A, (2:ℤ) • b = a) ↔ _
  simp only [two_smul]
lemma z7b (a:A):mk (a+a) = 0:=(mk_eq_zero _).mpr ⟨a,rfl⟩
lemma zcd (a:V A):a+a = 0:=by
  obtain ⟨x,rfl⟩:=mk_surjective a
  rw [← map_add,z7b]
noncomputable def map (p:A →+ B):V A →ₗ[ZMod 2] V B :=
  (ModN.liftEquiv' (n:=2)).symm ⟨mk.comp p,fun a => by
    change 2 • mk (p a) = 0
    simpa only [two_nsmul] using zcd (mk (p a))⟩
@[simp] lemma map_mk (p:A →+ B) (a:A):map p (mk a) = mk (p a):=rfl
variable {G:Type*} [Group G] (ρ:G →* AddAut A)
def fixed:Submodule (ZMod 2) (V A) where
  carrier:={a | ∀ g, map (ρ g).toAddMonoidHom a = a}
  zero_mem' g:=map_zero _
  add_mem' ha hb g:=by rw [map_add,ha g,hb g]
  smul_mem' c a ha g:=by rw [map_smul,ha g]
def pairs:AddSubgroup (A × (G → A)) where
  carrier:={x | ∀ g, ρ g x.1-x.1 = x.2 g+x.2 g}
  zero_mem' g:=by simp
  add_mem':=by
    intro x y hx hy g
    change ρ g (x.1+y.1)-(x.1+y.1) = (x.2 g+y.2 g)+(x.2 g+y.2 g)
    rw [map_add]
    calc
      _ = (ρ g x.1-x.1)+(ρ g y.1-y.1):=by abel
      _ = _:=by rw [hx,hy]; abel
  neg_mem':=by
    intro x hx g
    change ρ g (-x.1)- -x.1 = -x.2 g+ -x.2 g
    rw [map_neg]
    calc
      _ = -(ρ g x.1-x.1):=by abel
      _ = _:=by rw [hx]; abel
noncomputable def projection:pairs ρ →+ fixed ρ where
  toFun x:=⟨mk x.1.1,fun g => by
    rw [map_mk]
    change mk (ρ g x.1.1) = mk x.1.1
    apply sub_eq_zero.mp
    rw [← map_sub,x.property g,z7b]⟩
  map_zero':=Subtype.ext (map_zero mk)
  map_add' x y:=Subtype.ext (map_add mk x.1.1 y.1.1)
lemma z4x:Function.Surjective (projection ρ):=by
  intro v
  obtain ⟨a,ha⟩:=mk_surjective v.1
  have hex (g:G):∃ b:A, b+b = ρ g a-a:=by
    apply (mk_eq_zero _).mp
    have hp:=v.property g
    rw [← ha,map_mk] at hp
    change mk (ρ g a) = mk a at hp
    rw [map_sub,hp,sub_self]
  choose b hb using hex
  exact ⟨⟨(a,b),fun g => (hb g).symm⟩,Subtype.ext ha⟩
end z6
namespace z3h
open scoped Classical
open z1n
variable {G A:Type} [Group G] [AddCommGroup A]
  (ρ:G →* AddAut A) (i:ZMod 2 →+ A)
  (hi:Function.Injective i) (hfix:∀ g t, ρ g (i t) = i t)
  (hker:∀ a:A, a+a = 0 → ∃ t:ZMod 2, i t = a)
noncomputable abbrev H2 (G:Type) [Group G]:=groupCohomology (Rep.trivial (ZMod 2) G (ZMod 2)) 2
noncomputable abbrev Z2 (G:Type) [Group G]:=groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) G (ZMod 2))
lemma z56 (x:z6.pairs ρ) (g h:G) :
    boundary ρ x.1.2 g h+boundary ρ x.1.2 g h = 0:=by
  rw [← z5r]
  have he:(fun g => x.1.2 g+x.1.2 g) = (fun g => ρ g x.1.1-x.1.1) :=
    funext fun g => (x.property g).symm
  rw [he,zf1]
noncomputable def value (x:z6.pairs ρ) (g h:G):ZMod 2 :=
  (hker _ (z56 ρ x g h)).choose
@[simp] lemma z49 (x:z6.pairs ρ) (g h:G) :
    i (value ρ i hker x g h) = boundary ρ x.1.2 g h :=
  (hker _ (z56 ρ x g h)).choose_spec
include hi hfix in
lemma zkw (x:z6.pairs ρ) :
    (fun gh:G × G => value ρ i hker x gh.1 gh.2) ∈ Z2 G:=by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  apply hi
  change i (value ρ i hker x (g*h) k+value ρ i hker x g h) =
    i (value ρ i hker x h k+value ρ i hker x g (h*k))
  rw [map_add,map_add,z49,z49,z49,z49]
  have hf:=z5a ρ x.1.2 g h k
  rw [← z49 ρ i hker x h k,hfix,z49] at hf
  exact (add_comm _ _).trans hf.symm
noncomputable def z6w:z6.pairs ρ →+ Z2 G where
  toFun x:=⟨fun gh => value ρ i hker x gh.1 gh.2,zkw ρ i hi hfix hker x⟩
  map_zero':=by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker 0 gh.1 gh.2) = i 0
    rw [z49,map_zero]
    simp [boundary]
  map_add' x y:=by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker (x+y) gh.1 gh.2) =
      i (value ρ i hker x gh.1 gh.2+value ρ i hker y gh.1 gh.2)
    rw [map_add,z49,z49,z49]
    exact z5r ρ x.1.2 y.1.2 gh.1 gh.2
noncomputable def z95:z6.pairs ρ →+ H2 G :=
  (groupCohomology.H2π (Rep.trivial (ZMod 2) G (ZMod 2))).hom.toAddMonoidHom.comp
    (z6w ρ i hi hfix hker)
include hi hfix in
lemma z6r (x:z6.pairs ρ)
    (hx:z6.projection ρ x = 0):z95 ρ i hi hfix hker x = 0:=by
  have hx₀:z6.mk x.1.1 = 0:=congrArg Subtype.val hx
  obtain ⟨z,hz⟩:=(z6.mk_eq_zero _).mp hx₀
  have ht (g:G):∃ t:ZMod 2, i t = x.1.2 g-(ρ g z-z):=by
    apply hker
    have hxg:=x.property g
    rw [← hz,map_add] at hxg
    calc
      _ = (x.1.2 g+x.1.2 g)-((ρ g z+ρ g z)-(z+z)):=by abel
      _ = 0:=by rw [← hxg,sub_self]
  choose t ht using ht
  apply (groupCohomology.H2π_eq_zero_iff _).mpr
  refine ⟨t,?_⟩
  funext gh
  apply hi
  change i (t gh.2-t (gh.1*gh.2)+t gh.1) = i (value ρ i hker x gh.1 gh.2)
  rw [map_add,map_sub,z49,ht,ht,ht]
  have hfg:ρ gh.1 (x.1.2 gh.2-(ρ gh.2 z-z)) = x.1.2 gh.2-(ρ gh.2 z-z):=by
    rw [← ht,hfix]
  rw [← hfg]
  simp only [map_sub,z8o,boundary]
  abel
private noncomputable def factor {X Y Z:Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (p:X →ₗ[ℤ] Y) (hp:Function.Surjective p) (f:X →ₗ[ℤ] Z) (h:p.ker ≤ f.ker):Y →ₗ[ℤ] Z :=
  (p.ker.liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
private lemma z7i {X Y Z:Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (p:X →ₗ[ℤ] Y) (hp:Function.Surjective p) (f:X →ₗ[ℤ] Z) (h:p.ker ≤ f.ker) (x:X) :
    factor p hp f h (p x) = f x:=by
  change p.ker.liftQ f h ((p.quotKerEquivOfSurjective hp).symm (p x)) = _
  rw [← p.quotKerEquivOfSurjective_apply_mk hp x,LinearEquiv.symm_apply_apply]
  rfl
private lemma z9z :
    (z6.projection ρ).toIntLinearMap.ker ≤ (z95 ρ i hi hfix hker).toIntLinearMap.ker:=by
  intro x hx
  exact z6r ρ i hi hfix hker x hx
noncomputable def connecting:z6.fixed ρ →ₗ[ZMod 2] H2 G :=
  (factor (z6.projection ρ).toIntLinearMap (z6.z4x ρ)
    (z95 ρ i hi hfix hker).toIntLinearMap (z9z ρ i hi hfix hker)).toAddMonoidHom.toZModLinearMap 2
@[simp] lemma z7a (x:z6.pairs ρ) :
    connecting ρ i hi hfix hker (z6.projection ρ x) = z95 ρ i hi hfix hker x :=
  z7i (z6.projection ρ).toIntLinearMap (z6.z4x ρ)
    (z95 ρ i hi hfix hker).toIntLinearMap (z9z ρ i hi hfix hker) x
include hi hfix in
lemma z35 (hH1:z1v ρ)
    (hH2:∀ f:Z2 G, IsCoboundary ρ (fun g h => i (f (g,h)))) :
    Function.Surjective (connecting ρ i hi hfix hker):=by
  intro y
  induction y using groupCohomology.H2_induction_on with | h f =>
  obtain ⟨b,hb⟩:=hH2 f
  have hb' (g h:G):i (f (g,h)) = boundary ρ b g h:=congrFun (congrFun hb g) h
  have hc:z53 ρ (fun g => b g+b g):=by
    intro g h
    have hδ:boundary ρ (fun g => b g+b g) g h = 0:=by
      rw [z5r,← hb',← map_add,CharTwo.add_self_eq_zero,map_zero]
    change ρ g (b h+b h)-(b (g*h)+b (g*h))+(b g+b g) = 0 at hδ
    have he:(ρ g (b h+b h)+(b g+b g))-(b (g*h)+b (g*h)) = 0:=by
      rw [← sub_add_eq_add_sub]
      exact hδ
    exact (sub_eq_zero.mp he).symm
  obtain ⟨a,ha⟩:=hH1 _ hc
  let x:z6.pairs ρ:=⟨(a,b),ha⟩
  have hx:z6w ρ i hi hfix hker x = f:=by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker x gh.1 gh.2) = i (f (gh.1,gh.2))
    rw [z49,hb']
  refine ⟨z6.projection ρ x,?_⟩
  rw [z7a]
  change groupCohomology.H2π _ (z6w ρ i hi hfix hker x) = _
  rw [hx]
include hi hfix in
lemma zdp (a:A) (ha:∀ g, ρ g a = a)
    (v:z6.fixed ρ) (hv:v.1 = z6.mk a) :
    connecting ρ i hi hfix hker v = 0:=by
  let x:z6.pairs ρ:=⟨(a,fun _ => 0),fun g => by simp [ha]⟩
  have hx:z6.projection ρ x = v:=Subtype.ext hv.symm
  rw [← hx,z7a]
  have hcx:z6w ρ i hi hfix hker x = 0:=by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker x gh.1 gh.2) = i 0
    rw [z49,map_zero]
    simp [x,boundary]
  change groupCohomology.H2π _ (z6w ρ i hi hfix hker x) = 0
  rw [hcx,map_zero]
end z3h

namespace z1m
open NumberField z7 z10 z1n
open scoped Classical nonZeroDivisors
variable (E:Type) [Field E] [NumberField E]
lemma zmod_two_cases (t:ZMod 2):t = 0 ∨ t = 1:=by
  revert t
  decide
noncomputable def sign:ZMod 2 →+ F E where
  toFun t:=if t = 0 then 0 else Additive.ofMul (-1:Eˣ)
  map_zero':=by simp
  map_add' a b:=by
    rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
    · simp
    · simp
    · simp
    rw [show (1+1:ZMod 2) = 0 by decide]
    change (if (0:ZMod 2) = 0 then (0:F E) else Additive.ofMul (-1:Eˣ)) =
      (if (1:ZMod 2) = 0 then (0:F E) else Additive.ofMul (-1:Eˣ)) +
        (if (1:ZMod 2) = 0 then (0:F E) else Additive.ofMul (-1:Eˣ))
    rw [if_pos rfl,if_neg (by decide)]
    change Additive.ofMul (1:Eˣ) = Additive.ofMul ((-1:Eˣ)*(-1))
    simp
@[simp] lemma sign_zero:sign E 0 = 0:=map_zero _
@[simp] lemma sign_one:sign E 1 = Additive.ofMul (-1:Eˣ):=by simp [sign]
lemma zcy:Function.Injective (sign E):=by
  intro a b h
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · have he:=congrArg (fun a:F E => (a.toMul:E)) h
    norm_num [sign] at he
  · have he:=congrArg (fun a:F E => (a.toMul:E)) h
    norm_num [sign] at he
  · rfl
lemma zif (a:F E) (ha:a+a = 0):∃ t:ZMod 2, sign E t = a:=by
  have hs:(a.toMul:E)^2 = (1:E)^2:=by
    have he:=congrArg (fun a:F E => (a.toMul:E)) ha
    simpa only [pow_two,mul_one,toMul_add,toMul_zero,Units.val_mul,Units.val_one] using he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · refine ⟨0,?_⟩
    rw [sign_zero]
    apply Additive.toMul.injective
    exact Units.ext h.symm
  · refine ⟨1,?_⟩
    rw [sign_one]
    apply Additive.toMul.injective
    exact Units.ext h.symm
lemma zju (t:ZMod 2):z4.z11 E (sign E t) = 0:=by
  rcases zmod_two_cases t with rfl | rfl
  · simp
  · change z4.z11 E (sign E (1:ZMod 2)) = 0
    rw [sign_one]
    change toPrincipalIdeal (𝓞 E) E (-1:Eˣ) = 1
    apply (z5c E _).mpr
    refine ⟨(-1:(𝓞 E)ˣ),?_⟩
    apply Units.ext
    simp [z5w]
variable (K:Type) [Field K] [NumberField K] [Algebra K E]
lemma zdt (g:Gal(E/K)) (t:ZMod 2) :
    zg.z15 K E g (sign E t) = sign E t:=by
  rcases zmod_two_cases t with rfl | rfl
  · simp
  · change zg.z15 K E g (sign E (1:ZMod 2)) = sign E 1
    rw [sign_one]
    apply Additive.toMul.injective
    apply Units.ext
    change g (-1:E) = -1
    simp
noncomputable def connecting:z6.fixed (zg.z15 K E) →ₗ[ZMod 2]
    z3h.H2 Gal(E/K) :=
  z3h.connecting (zg.z15 K E) (sign E)
    (zcy E) (zdt E K) (zif E)
variable [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]
lemma z35 (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤):Function.Surjective (connecting E K):=by
  apply z3h.z35 _ _ _ _ _ (zg.zc0 K E)
  intro f
  apply zg.z9n K E hG hunram
  · intro g h k
    change zg.z15 K E g (sign E (f (h,k)))+sign E (f (g,h*k)) =
      sign E (f (g,h))+sign E (f (g*h,k))
    rw [zdt,← map_add (sign E),← map_add (sign E)]
    apply congrArg (sign E)
    have he:=(groupCohomology.mem_cocycles₂_iff f).mp f.property g h k
    exact he.symm.trans (add_comm _ _)
  · refine ⟨fun _ => 0,?_⟩
    funext g h
    exact (zju E _).trans (by simp [boundary])
end z1m
namespace z10
open NumberField
open scoped Classical nonZeroDivisors
variable (K M E:Type*) [Field K] [Field M] [Field E] [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
lemma zlr (I:Ideals K):extend M E (extend K M I) = extend K E I:=by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHom E (𝓞 E) (FractionalIdeal.extendedHom M (𝓞 M) I.1)) :
    Submodule (𝓞 E) E) = (FractionalIdeal.extendedHom E (𝓞 E) I.1:Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHom_eq_span,FractionalIdeal.coe_extendedHom_eq_span]
  have hI:((FractionalIdeal.extendedHom M (𝓞 M) I.1):Set M) =
      (Submodule.span (𝓞 M) (algebraMap K M '' (I.1:Set K)):Set M) :=
    congrArg (fun p:Submodule (𝓞 M) M => (p:Set M)) (FractionalIdeal.coe_extendedHom_eq_span M (𝓞 M) I.1)
  rw [hI]
  let f:M →ₗ[𝓞 M] E:=(IsScalarTower.toAlgHom (𝓞 M) M E).toLinearMap
  change Submodule.span (𝓞 E) (f '' (Submodule.span (𝓞 M) (algebraMap K M '' (I.1:Set K)):Set M)) = _
  rw [← Submodule.map_coe,Submodule.map_span,Submodule.span_span_of_tower,Set.image_image]
  congr 1
  have he:(fun x => f (algebraMap K M x)) = algebraMap K E:=by
    funext x
    exact (IsScalarTower.algebraMap_apply K M E x).symm
  rw [he]
lemma z7f (ha:Function.Surjective (algebraMap K E)) :
    Function.Surjective (extend K E):=by
  intro I
  let V:=z23.z6f K E I.1
  have hV:IsFractional (𝓞 K)⁰ V:=by
    obtain ⟨d,hd,hI⟩:=I.1.isFractional
    obtain ⟨r,hr⟩:=ha (d:E)
    have hint:IsIntegral ℤ r :=
      (isIntegral_algebraMap_iff (R:=ℤ) (algebraMap K E).injective).mp (hr ▸ d.property)
    let r₀:𝓞 K:=⟨r,hint⟩
    have hr0:r₀ ≠ 0:=by
      intro hz
      apply mem_nonZeroDivisors_iff_ne_zero.mp hd
      apply RingOfIntegers.coe_injective
      have hrz:r = 0:=congrArg (fun z:𝓞 K => (z:K)) hz
      change (d:E) = 0
      rw [← hr,hrz,map_zero]
    refine ⟨r₀,mem_nonZeroDivisors_iff_ne_zero.mpr hr0,?_⟩
    intro x hx
    obtain ⟨b,hb⟩:=hI (algebraMap K E x) hx
    have he:algebraMap K E (r*x) = (b:E):=by
      change (b:E) = (d:E)*algebraMap K E x at hb
      rw [map_mul,hr,hb]
    have hint':IsIntegral ℤ (r*x) :=
      (isIntegral_algebraMap_iff (R:=ℤ) (algebraMap K E).injective).mp (he ▸ b.property)
    exact ⟨⟨r*x,hint'⟩,rfl⟩
  let J:FractionalIdeal (𝓞 K)⁰ K:=⟨V,hV⟩
  have he:FractionalIdeal.extendedHom E (𝓞 E) J = I.1:=by
    apply FractionalIdeal.coeToSubmodule_injective
    change (FractionalIdeal.extendedHom E (𝓞 E) J:Submodule (𝓞 E) E) = I.1.coeToSubmodule
    rw [FractionalIdeal.coe_extendedHom_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y,rfl⟩:=ha x
      exact Submodule.subset_span ⟨y,hx,rfl⟩
  have hJ:J ≠ 0:=by
    intro hz
    rw [hz,map_zero] at he
    exact I.ne_zero he.symm
  refine ⟨Units.mk0 J hJ,?_⟩
  exact Units.ext he
end z10
namespace zg
open NumberField z7 z10 z1n
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]
lemma zaw (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) (I:D E)
    (hI:∀ g:Gal(E/K), z1h K E g I = I) :
    ∃ J:D K, z1u K E J = I:=by
  generalize hn:Module.finrank K E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases hdeg:Module.finrank K E = 1
    · have hcard:Nat.card Gal(E/K) = 1:=(IsGalois.card_aut_eq_finrank K E).trans hdeg
      have hg (g:Gal(E/K)):g = 1:=by
        have hp:g ^ Nat.card Gal(E/K) = 1:=pow_card_eq_one'
        rwa [hcard,pow_one] at hp
      have ha:Function.Surjective (algebraMap K E):=by
        intro x
        change x ∈ Set.range (algebraMap K E)
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro g
        rw [hg g]
        rfl
      obtain ⟨J,hJ⟩:=z7f K E ha I.toMul
      exact ⟨Additive.ofMul J,congrArg Additive.ofMul hJ⟩
    · have hc:1 < Nat.card Gal(E/K):=by
        rw [IsGalois.card_aut_eq_finrank]
        have hp:0 < Module.finrank K E:=Module.finrank_pos
        omega
      letI:Nontrivial Gal(E/K):=Finite.one_lt_card_iff_nontrivial.mp hc
      obtain ⟨H,hH,hcard⟩:=z75.za3 Gal(E/K) hG
      letI:=hH
      let M:=IntermediateField.fixedField H
      letI:NumberField M:=NumberField.of_module_finite ℚ M
      have hdegM:Module.finrank M E = 2 :=
        (IntermediateField.finrank_fixedField_eq_card H).trans hcard
      have hMlt:Module.finrank K M < n:=by
        have he:=Module.finrank_mul_finrank K M E
        rw [hdegM,hn] at he
        have hp:0 < Module.finrank K M:=Module.finrank_pos
        omega
      have hGM:IsPGroup 2 Gal(M/K) :=
        hG.of_surjective (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
      have hu:=z4q.zeh K M E hunram
      have hcardM:Nat.card Gal(E/M) = 2:=(IsGalois.card_aut_eq_finrank M E).trans hdegM
      letI:Nontrivial Gal(E/M):=Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨σ,hσ⟩:=exists_ne (1:Gal(E/M))
      have hσI:z22 M E σ I = I:=hI (σ.restrictScalars K)
      obtain ⟨J,hJ⟩:=(z4.z2v M E σ hdegM hσ hu.1).surjective
        ⟨I,(z9.z1g _ _).mpr hσI⟩
      have hj:z1u M E J = I:=congrArg Subtype.val hJ
      have hfix (g:Gal(M/K)):z1h K M g J = J:=by
        obtain ⟨s,rfl⟩:=AlgEquiv.restrictNormalHom_surjective E g
        apply z4a M E
        rw [z5d,hj,hI]
      obtain ⟨L,hL⟩:=ih (Module.finrank K M) hMlt M hGM hu.2 J hfix rfl
      refine ⟨L,?_⟩
      have he:=congrArg (z1u M E) hL
      change Additive.ofMul (extend M E (extend K M L.toMul)) = z1u M E J at he
      rw [zlr] at he
      exact he.trans hj
end zg
namespace z6
open z1n
open scoped Classical
variable {G A:Type} [Group G] [AddCommGroup A] (ρ:G →* AddAut A)
lemma zn8 (hH1:z1v ρ) (h2:Function.Injective (fun a:A => a+a)) (v:fixed ρ) :
    ∃ a:A, mk a = v.1 ∧ ∀ g, ρ g a = a:=by
  obtain ⟨x,hx⟩:=z4x ρ v
  have hb:z53 ρ x.1.2:=by
    intro g h
    have hz:boundary ρ x.1.2 g h = 0:=h2 (by
      simpa only [zero_add] using z3h.z56 ρ x g h)
    change ρ g (x.1.2 h)-x.1.2 (g*h)+x.1.2 g = 0 at hz
    have hz':(ρ g (x.1.2 h)+x.1.2 g)-x.1.2 (g*h) = 0:=by
      rw [← sub_add_eq_add_sub]
      exact hz
    exact (sub_eq_zero.mp hz').symm
  obtain ⟨a,ha⟩:=hH1 _ hb
  refine ⟨x.1.1-(a+a),?_,?_⟩
  · rw [map_sub,z7b,sub_zero]
    exact congrArg Subtype.val hx
  · intro g
    have hp:=x.property g
    rw [← ha g] at hp
    apply sub_eq_zero.mp
    calc
      _ = (ρ g x.1.1-x.1.1)-((ρ g a-a)+(ρ g a-a)):=by rw [map_sub,map_add]; abel
      _ = 0:=by rw [hp,sub_self]
end z6
namespace z6
open z1n
open scoped Classical
variable {G A B A₀:Type} [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup A₀]
  (ρ:G →* AddAut A) (τ:G →* AddAut B) (p:A →+ B)
  (hp:∀ g a, p (ρ g a) = τ g (p a))
include hp in
lemma zix (g:G) (v:V A) :
    map (τ g).toAddMonoidHom (map p v) = map p (map (ρ g).toAddMonoidHom v):=by
  obtain ⟨a,rfl⟩:=mk_surjective v
  simp only [map_mk]
  exact congrArg mk (hp g a).symm
noncomputable def zns:fixed ρ →ₗ[ZMod 2] fixed τ :=
  ((map p).comp (fixed ρ).subtype).codRestrict _ (fun v g => by
    change map (τ g).toAddMonoidHom (map p v.1) = map p v.1
    rw [zix ρ τ p hp,v.property g])
variable (e:A₀ →+ A) (hei:Function.Injective e)
  (hef:∀ g a, ρ g (e a) = e a)
  (hes:∀ a:A, (∀ g, ρ g a = a) → ∃ a₀:A₀, e a₀ = a)
noncomputable def zjh:V A₀ →ₗ[ZMod 2] fixed ρ :=
  (map e).codRestrict _ (fun v g => by
    obtain ⟨a,rfl⟩:=mk_surjective v
    rw [map_mk,map_mk]
    exact congrArg mk (hef g a))
include hef hes in
lemma zg0 (hH1:z1v ρ) (h2:Function.Injective (fun a:A => a+a)) :
    Function.Surjective (zjh ρ e hef):=by
  intro v
  obtain ⟨a,ha,haf⟩:=zn8 ρ hH1 h2 v
  obtain ⟨b,hb⟩:=hes a haf
  refine ⟨mk b,Subtype.ext ?_⟩
  change map e (mk b) = v.1
  rw [map_mk,hb,ha]
include hei hef hes in
lemma zh3 (h2:Function.Injective (fun a:A => a+a)) :
    Function.Injective (zjh ρ e hef):=by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  obtain ⟨a,rfl⟩:=mk_surjective v
  have hz:mk (e a) = 0:=congrArg Subtype.val hv
  obtain ⟨b,hb⟩:=(mk_eq_zero _).mp hz
  have hbf (g:G):ρ g b = b:=h2 (by
    change ρ g b+ρ g b = b+b
    rw [← map_add,hb,hef])
  obtain ⟨c,hc⟩:=hes b hbf
  apply (mk_eq_zero _).mpr
  refine ⟨c,hei ?_⟩
  rw [map_add,hc,hb]
noncomputable def zam (hH1:z1v ρ) (h2:Function.Injective (fun a:A => a+a)) :
    V A₀ ≃ₗ[ZMod 2] fixed ρ :=
  LinearEquiv.ofBijective (zjh ρ e hef)
    ⟨zh3 ρ e hei hef hes h2,zg0 ρ e hef hes hH1 h2⟩
end z6
namespace z1a
open NumberField z7 z10 z1n zg
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]
private lemma zno:z1v (z1h K E):=by
  intro b hb
  exact zbs K E (MonoidHom.id _) b hb
private lemma zdn (g:Gal(E/K)) (I:D K) :
    z1h K E g (z1u K E I) = z1u K E I:=by
  exact congrArg Additive.ofMul (zfv K E g I.toMul)
noncomputable def z4b (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    z6.V (D K) ≃ₗ[ZMod 2] z6.fixed (z1h K E) :=
  z6.zam (z1h K E) (z1u K E) (z4a K E)
    (zdn K E) (zaw K E hG hunram) (zno K E)
    (z10.zi7 E)
noncomputable def z39:z6.fixed (z15 K E) →ₗ[ZMod 2] z6.fixed (z1h K E) :=
  z6.zns (z15 K E) (z1h K E)
    (z4.z11 E).toAddMonoidHom (z4w K E)
noncomputable def z25:Submodule (ZMod 2) (z6.fixed (z15 K E)):=(z39 K E).ker
noncomputable def obstruction (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    z6.fixed (z15 K E) →ₗ[ZMod 2] z6.V (C K) :=
  (z6.map (A:=D K) (B:=C K) (z1i K).toAddMonoidHom).comp
    ((z4b K E hG hunram).symm.toLinearMap.comp (z39 K E))
private lemma z7n (g:Gal(E/K)) (a:F K) :
    z15 K E g (z26 K E a) = z26 K E a:=by
  apply Additive.toMul.injective
  apply Units.ext
  exact g.commutes a.toMul
noncomputable def z3t:F K →+ z6.fixed (z15 K E) where
  toFun a:=⟨z6.mk (z26 K E a),fun g => by
    rw [z6.map_mk]
    exact congrArg z6.mk (z7n K E g a)⟩
  map_zero':=by apply Subtype.ext; simp
  map_add' a b:=by apply Subtype.ext; simp
lemma zlp (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) (a:F K) :
    z39 K E (z3t K E a) =
      z4b K E hG hunram (z6.mk (z4.z11 K a)):=by
  apply Subtype.ext
  change z6.map (z4.z11 E).toAddMonoidHom
    (z6.mk (z26 K E a)) = z6.mk (z1u K E (z4.z11 K a))
  rw [z6.map_mk]
  exact congrArg z6.mk (z86 K E a)
lemma ziu (a:F K):z1m.connecting E K (z3t K E a) = 0:=by
  exact z3h.zdp (z15 K E) (z1m.sign E)
    (z1m.zcy E) (z1m.zdt E K)
    (z1m.zif E) (z26 K E a) (z7n K E · a) _ rfl
set_option maxHeartbeats 2000000 in
lemma zg7 (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (v:z6.fixed (z15 K E)) (hv:obstruction K E hG hunram v = 0) :
    ∃ s:z25 K E, z1m.connecting E K s.1 = z1m.connecting E K v:=by
  obtain ⟨J,hJ⟩:=z6.mk_surjective ((z4b K E hG hunram).symm (z39 K E v))
  have hdiv:z39 K E v = z4b K E hG hunram (z6.mk J):=by
    rw [hJ,LinearEquiv.apply_symm_apply]
  have hclass:z6.mk (z1i K J) = 0:=by
    change z6.map (A:=D K) (B:=C K) (z1i K).toAddMonoidHom
      ((z4b K E hG hunram).symm (z39 K E v)) = 0 at hv
    rw [← hJ,z6.map_mk] at hv
    exact hv
  obtain ⟨c,hc⟩:=(z6.mk_eq_zero _).mp hclass
  obtain ⟨I,hI⟩:=zj.mk_surjective K c.toMul
  let I':D K:=Additive.ofMul I
  have hI':z1i K I' = c:=congrArg Additive.ofMul hI
  have hpr:J-(I'+I') ∈ (z4.z11 K).range:=by
    rw [← z4.z7k]
    change z1i K (J-(I'+I')) = 0
    rw [map_sub,map_add,hI',hc,sub_self]
  obtain ⟨a,ha⟩:=hpr
  have hparity:z6.mk (z4.z11 K a) = z6.mk J:=by
    rw [ha,map_sub,z6.z7b,sub_zero]
  have hd:z39 K E (z3t K E a) = z39 K E v:=by
    rw [zlp K E hG hunram,hparity,hdiv]
  refine ⟨⟨v-z3t K E a,?_⟩,?_⟩
  · change z39 K E (v-z3t K E a) = 0
    rw [map_sub,hd,sub_self]
  · change z1m.connecting E K (v-z3t K E a) = _
    rw [map_sub,ziu,sub_zero]
end z1a
namespace z6y
open scoped Classical
variable {k V H C:Type*} [Field k] [AddCommGroup V] [AddCommGroup H] [AddCommGroup C]
  [Module k V] [Module k H] [Module k C] [FiniteDimensional k C]
lemma finrank_le (f:V →ₗ[k] H) (hf:Function.Surjective f) (g:V →ₗ[k] C)
    (S:Submodule k V) [FiniteDimensional k S]
    (hS:∀ v:V, g v = 0 → ∃ s:S, f s.1 = f v) :
    Module.finrank k H ≤ Module.finrank k C+Module.finrank k S:=by
  obtain ⟨s,hs⟩:=LinearMap.exists_rightInverse_of_surjective g.rangeRestrict
    (LinearMap.range_eq_top.mpr g.surjective_rangeRestrict)
  have hs' (c:g.range):g (s c) = c.1 :=
    congrArg Subtype.val (LinearMap.congr_fun hs c)
  let F:g.range × S →ₗ[k] H:=(f.comp s).coprod (f.comp S.subtype)
  have hF:Function.Surjective F:=by
    intro y
    obtain ⟨v,rfl⟩:=hf y
    have hw:g (v-s (g.rangeRestrict v)) = 0:=by rw [map_sub,hs']; exact sub_self _
    obtain ⟨u,hu⟩:=hS _ hw
    refine ⟨(g.rangeRestrict v,u),?_⟩
    change f (s (g.rangeRestrict v))+f u.1 = f v
    rw [hu,map_sub]
    abel
  have hbound:=F.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hF,(Submodule.topEquiv:(⊤:Submodule k H) ≃ₗ[k] H).finrank_eq,Module.finrank_prod] at hbound
  exact hbound.trans (Nat.add_le_add_right (Submodule.finrank_le g.range) _)
end z6y
namespace z1a
open NumberField z7 zg
open scoped Classical nonZeroDivisors
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]
set_option maxHeartbeats 2000000 in
lemma z3m (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    [FiniteDimensional (ZMod 2) (z25 K E)] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Gal(E/K) (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2) (z6.V (C K))+Module.finrank (ZMod 2) (z25 K E):=by
  letI:Finite (C K):=Finite.of_equiv (zj.Classes K) Additive.ofMul
  letI:Finite (z6.V (C K)):=Finite.of_surjective z6.mk z6.mk_surjective
  letI:FiniteDimensional (ZMod 2) (z6.V (C K)):=Module.Finite.of_finite
  exact z6y.finrank_le (z1m.connecting E K)
    (z1m.z35 E K hG hunram) (obstruction K E hG hunram)
    (z25 K E) (zg7 K E hG hunram)
end z1a
namespace z41
open NumberField FractionalIdeal
open scoped Classical nonZeroDivisors
variable (E:Type*) [Field E] [NumberField E]
lemma z4r (P:Ideal (𝓞 E)) (hp0:P ≠ ⊥) (hp1:P ≠ ⊤)
    (a:E) (I:FractionalIdeal (𝓞 E)⁰ E) (hI:I ≠ 0)
    (ha:spanSingleton (𝓞 E)⁰ a = I*I) :
    ∃ x:E, x ≠ 0 ∧ ∃ b:𝓞 E, (b:E) = a*x^2 ∧ IsCoprime P (Ideal.span {b}):=by
  obtain ⟨x,hx⟩:=IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a:=(P:FractionalIdeal (𝓞 E)⁰ E)) (b:=I) (c:=1)
    coeIdeal_le_one (coeIdeal_ne_zero.mpr hp0) hI
  have hx0:x ≠ 0:=by
    intro h
    rw [h,spanSingleton_zero,zero_mul,add_zero] at hx
    apply hp1
    apply coeIdeal_injective (K:=E)
    simpa only [coeIdeal_top] using hx
  have hle:spanSingleton (𝓞 E)⁰ x*I ≤ 1:=by
    rw [← hx]
    exact le_add_of_nonneg_left (FractionalIdeal.zero_le _)
  obtain ⟨J,hJ⟩:=le_one_iff_exists_coeIdeal.mp hle
  have hcop:IsCoprime P J:=by
    rw [Ideal.isCoprime_iff_sup_eq]
    apply coeIdeal_injective (K:=E)
    change ((P ⊔ J:Ideal (𝓞 E)):FractionalIdeal (𝓞 E)⁰ E) = ((⊤:Ideal (𝓞 E)):FractionalIdeal (𝓞 E)⁰ E)
    rw [coeIdeal_sup,coeIdeal_top,hJ]
    exact hx
  have hprod:spanSingleton (𝓞 E)⁰ (a*x^2) = (J:FractionalIdeal (𝓞 E)⁰ E)*(J:FractionalIdeal (𝓞 E)⁰ E):=by
    rw [← spanSingleton_mul_spanSingleton,← spanSingleton_pow,ha,hJ]
    ring
  have hr:a*x^2 ∈ (1:FractionalIdeal (𝓞 E)⁰ E):=by
    have hle':(J:FractionalIdeal (𝓞 E)⁰ E)*(J:FractionalIdeal (𝓞 E)⁰ E) ≤ 1:=by
      have hj:(J:FractionalIdeal (𝓞 E)⁰ E) ≤ 1:=coeIdeal_le_one
      exact (mul_le_mul' hj hj).trans_eq (_root_.one_mul _)
    exact hle' (hprod ▸ mem_spanSingleton_self (𝓞 E)⁰ (a*x^2))
  obtain ⟨b,hb⟩:=(mem_one_iff (𝓞 E)⁰).mp hr
  change (b:E) = a*x^2 at hb
  refine ⟨x,hx0,b,hb,?_⟩
  have hbJ:Ideal.span {b} = J^2:=by
    apply coeIdeal_injective (K:=E)
    change ((Ideal.span {b}):FractionalIdeal (𝓞 E)⁰ E) = ((J^2:Ideal (𝓞 E)):FractionalIdeal (𝓞 E)⁰ E)
    rw [coeIdeal_span_singleton,coeIdeal_pow,pow_two]
    change spanSingleton (𝓞 E)⁰ (b:E) = _
    rw [hb,hprod]
  rw [hbJ]
  exact hcop.pow_right
end z41
namespace z5
open NumberField
open scoped Classical nonZeroDivisors
variable (E:Type*) [Field E] [NumberField E]
def modulus:Ideal (𝓞 E):=Ideal.span {(4:𝓞 E)}
abbrev R:=𝓞 E ⧸ modulus E
abbrev reduce:𝓞 E →+* R E:=Ideal.Quotient.mk (modulus E)
@[simp] lemma z8r:reduce E 4 = 0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
lemma z64:modulus E ≠ ⊤:=by
  intro h
  have hm:Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(4:ℤ)}) = ⊤:=by
    simpa only [Ideal.map_span,Set.image_singleton,map_ofNat,modulus] using h
  have he:=(Ideal.map_eq_top_iff (algebraMap ℤ (𝓞 E))
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp hm
  have hu:IsUnit (4:ℤ):=Ideal.span_singleton_eq_top.mp he
  norm_num [Int.isUnit_iff] at hu
lemma za0 (a:𝓞 E):IsUnit (reduce E a) ↔ IsCoprime a 4:=by
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨b,hb⟩:=Ideal.Quotient.mk_surjective ((u⁻¹:(R E)ˣ):R E)
    have he:reduce E (a*b) = reduce E 1:=by
      rw [map_mul,map_one,← hu,hb]
      exact u.val_inv
    have hm:a*b-1 ∈ Ideal.span {(4:𝓞 E)}:=Ideal.Quotient.eq.mp he
    obtain ⟨c,hc⟩:=Ideal.mem_span_singleton.mp hm
    refine ⟨b,-c,?_⟩
    linear_combination hc
  · intro h
    have he:=h.map (reduce E)
    rw [z8r,isCoprime_zero_right] at he
    exact he
noncomputable def unit (a:𝓞 E) (ha:IsUnit (reduce E a)):(R E)ˣ:=ha.unit
@[simp] lemma zdy (a:𝓞 E) (ha:IsUnit (reduce E a)):(unit E a ha:R E) = reduce E a:=ha.unit_spec
noncomputable def z1f (a:𝓞 E) (ha:IsUnit (reduce E a)):z6.V (Additive (R E)ˣ) :=
  z6.mk (Additive.ofMul (unit E a ha))
lemma zb2 (a b:𝓞 E) (ha:IsUnit (reduce E a)) (hb:IsUnit (reduce E b))
    (x:E) (hx:(a:E) = (b:E)*x^2):z1f E a ha = z1f E b hb:=by
  have hy:((b:E)*x)^2 = (a*b:𝓞 E):=by
    change ((b:E)*x)^2 = (a:E)*(b:E)
    rw [hx]
    ring
  have hyi:IsIntegral ℤ ((b:E)*x):=IsIntegral.of_pow (by norm_num:0 < 2) (hy ▸ (a*b).property)
  let y:𝓞 E:=⟨(b:E)*x,hyi⟩
  have hyy:y*y = a*b:=by
    apply RingOfIntegers.coe_injective
    change ((b:E)*x)*((b:E)*x) = ((a*b:𝓞 E):E)
    simpa only [pow_two] using hy
  have hyq:reduce E y*reduce E y = reduce E a*reduce E b:=by
    rw [← map_mul,hyy,map_mul]
  have huy:IsUnit (reduce E y):=isUnit_of_mul_isUnit_left (hyq ▸ ha.mul hb)
  have he:unit E a ha*unit E b hb = unit E y huy*unit E y huy:=by
    apply Units.ext
    simpa only [Units.val_mul,zdy] using hyq.symm
  have he':(Additive.ofMul (unit E a ha):Additive (R E)ˣ)+Additive.ofMul (unit E b hb) =
      Additive.ofMul (unit E y huy)+Additive.ofMul (unit E y huy):=congrArg Additive.ofMul he
  have hm:=congrArg (z6.mk (A:=Additive (R E)ˣ)) he'
  rw [map_add,map_add,z6.zcd] at hm
  change z1f E a ha+z1f E b hb = 0 at hm
  have hn:-z1f E b hb = z1f E b hb :=
    neg_eq_iff_add_eq_zero.mpr (z6.zcd _)
  exact (eq_neg_of_add_eq_zero_left hm).trans hn
instance:Nontrivial (R E):=Ideal.Quotient.nontrivial_iff.mpr (z64 E)
instance:Finite (R E):=(modulus E).finiteQuotientOfFreeOfNeBot (by simp [modulus])
@[simp] lemma zit:z1f E 1 (by simp) = 0:=by
  have hu:unit E 1 (by simp) = 1:=by apply Units.ext; simp
  unfold z1f
  rw [hu]
  exact map_zero z6.mk
lemma zia (a b:𝓞 E) (ha:IsUnit (reduce E a)) (hb:IsUnit (reduce E b)) :
    z1f E (a*b) (by simpa only [map_mul] using ha.mul hb) =
      z1f E a ha+z1f E b hb:=by
  have hu:unit E (a*b) (by simpa only [map_mul] using ha.mul hb) = unit E a ha*unit E b hb:=by
    apply Units.ext
    simp only [zdy,Units.val_mul,map_mul]
  change z6.mk (Additive.ofMul (unit E (a*b) _)) = _
  rw [hu]
  exact map_add z6.mk _ _
lemma zch (a:𝓞 E) (ha:IsUnit (reduce E a))
    (h:z1f E a ha = 0):∃ b c:𝓞 E, a = b^2+4*c:=by
  obtain ⟨v,hv⟩:=(z6.mk_eq_zero _).mp h
  obtain ⟨b,hb⟩:=Ideal.Quotient.mk_surjective (v.toMul:R E)
  have he:reduce E a = reduce E (b^2):=by
    have hv':=congrArg (fun z:Additive (R E)ˣ => (z.toMul:R E)) hv
    change (v.toMul:R E)*(v.toMul:R E) = (unit E a ha:R E) at hv'
    rw [zdy,← hb] at hv'
    simpa only [map_pow,pow_two,map_mul] using hv'.symm
  have hm:a-b^2 ∈ Ideal.span {(4:𝓞 E)}:=Ideal.Quotient.eq.mp he
  obtain ⟨c,hc⟩:=Ideal.mem_span_singleton.mp hm
  refine ⟨b,c,?_⟩
  linear_combination hc
end z5
namespace z1z
open NumberField z7 z10
open scoped Classical nonZeroDivisors
variable (E:Type) [Field E] [NumberField E]
noncomputable def divisor:z6.V (F E) →ₗ[ZMod 2] z6.V (D E) :=
  z6.map (z4.z11 E).toAddMonoidHom
noncomputable def Sel:=(divisor E).ker
noncomputable def z2a (a:𝓞 E) (ha:a ≠ 0):z6.V (F E) :=
  z6.mk (Additive.ofMul (Units.mk0 (a:E) (RingOfIntegers.coe_ne_zero_iff.mpr ha)))
structure Representative (v:z6.V (F E)) where
  a:𝓞 E
  ne_zero:a ≠ 0
  unit:IsUnit (z5.reduce E a)
  class_eq:z2a E a ne_zero = v
lemma z28 (v:Sel E):Nonempty (Representative E v.1):=by
  obtain ⟨a,ha⟩:=z6.mk_surjective v.1
  have hp:z6.mk (z4.z11 E a) = 0:=by
    have h:=v.property
    change divisor E v.1 = 0 at h
    rw [← ha] at h
    exact h
  obtain ⟨I,hI⟩:=(z6.mk_eq_zero _).mp hp
  have hvirt:FractionalIdeal.spanSingleton (𝓞 E)⁰ (a.toMul:E) = I.toMul.1*I.toMul.1:=by
    have he:=congrArg (fun I:D E => I.toMul.1) hI.symm
    change (toPrincipalIdeal (𝓞 E) E a.toMul:FractionalIdeal (𝓞 E)⁰ E) = _ at he
    simpa only [coe_toPrincipalIdeal,toMul_add,Units.val_mul] using he
  have hp0:z5.modulus E ≠ ⊥:=by simp [z5.modulus]
  obtain ⟨x,hx,r,hr,hcop⟩:=z41.z4r E
    (z5.modulus E) hp0 (z5.z64 E)
    (a.toMul:E) I.toMul.1 I.toMul.ne_zero hvirt
  have hr0:r ≠ 0:=by
    apply RingOfIntegers.coe_ne_zero_iff.mp
    change (r:E) ≠ 0
    rw [hr]
    exact mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ hx)
  have hru:IsUnit (z5.reduce E r) :=
    (z5.za0 E r).mpr
      ((Ideal.isCoprime_span_singleton_iff (4:𝓞 E) r).mp hcop).symm
  refine ⟨⟨r,hr0,hru,?_⟩⟩
  let xu:Eˣ:=Units.mk0 x hx
  have he:Units.mk0 (r:E) (RingOfIntegers.coe_ne_zero_iff.mpr hr0) = a.toMul*(xu*xu):=by
    apply Units.ext
    simpa only [xu,Units.val_mul,Units.val_mk0,pow_two] using hr
  change z6.mk (Additive.ofMul (Units.mk0 (r:E) _)) = v.1
  rw [he]
  change z6.mk (a+(Additive.ofMul xu+Additive.ofMul xu)) = v.1
  rw [map_add,z6.z7b,add_zero,ha]
lemma z9h {v:z6.V (F E)} (a b:Representative E v) :
    z5.z1f E a.a a.unit = z5.z1f E b.a b.unit:=by
  let au:F E:=Additive.ofMul (Units.mk0 (a.a:E) (RingOfIntegers.coe_ne_zero_iff.mpr a.ne_zero))
  let bu:F E:=Additive.ofMul (Units.mk0 (b.a:E) (RingOfIntegers.coe_ne_zero_iff.mpr b.ne_zero))
  have hm:z6.mk (au-bu) = 0:=by
    rw [map_sub]
    change z2a E a.a a.ne_zero-z2a E b.a b.ne_zero = 0
    rw [a.class_eq,b.class_eq,sub_self]
  obtain ⟨z,hz⟩:=(z6.mk_eq_zero _).mp hm
  have he:au = bu+(z+z):=by rw [hz]; abel
  have hv:=congrArg (fun a:F E => (a.toMul:E)) he
  change (a.a:E) = (b.a:E)*((z.toMul:E)*(z.toMul:E)) at hv
  exact z5.zb2 E a.a b.a a.unit b.unit z.toMul (by simpa only [pow_two] using hv)
noncomputable def residue (v:Sel E):z6.V (Additive (z5.R E)ˣ) :=
  z5.z1f E (z28 E v).some.a (z28 E v).some.unit
lemma z1x (v:Sel E) (r:Representative E v.1) :
    residue E v = z5.z1f E r.a r.unit :=
  z9h E (z28 E v).some r
@[simp] lemma zgi:z2a E 1 (by simp) = 0:=by
  have he:Units.mk0 (1:E) (by simp) = 1:=by apply Units.ext; rfl
  change z6.mk (Additive.ofMul (Units.mk0 (1:E) _)) = 0
  rw [he]
  exact map_zero z6.mk
lemma zh2 (a b:𝓞 E) (ha:a ≠ 0) (hb:b ≠ 0) :
    z2a E (a*b) (mul_ne_zero ha hb) = z2a E a ha+z2a E b hb:=by
  have he:Units.mk0 ((a*b:𝓞 E):E) (RingOfIntegers.coe_ne_zero_iff.mpr (mul_ne_zero ha hb)) =
      Units.mk0 (a:E) (RingOfIntegers.coe_ne_zero_iff.mpr ha)*
        Units.mk0 (b:E) (RingOfIntegers.coe_ne_zero_iff.mpr hb):=by apply Units.ext; rfl
  change z6.mk (Additive.ofMul (Units.mk0 ((a*b:𝓞 E):E) _)) = _
  rw [he]
  exact map_add z6.mk _ _
@[simp] lemma zli:residue E 0 = 0:=by
  let r:Representative E (0:z6.V (F E)):=⟨1,by simp,by simp,zgi E⟩
  rw [z1x E 0 r]
  exact z5.zit E
lemma zm6 (v w:Sel E):residue E (v+w) = residue E v+residue E w:=by
  let a:=(z28 E v).some
  let b:=(z28 E w).some
  let r:Representative E (v+w).1:={
    a:=a.a*b.a
    ne_zero:=mul_ne_zero a.ne_zero b.ne_zero
    unit:=by simpa only [map_mul] using a.unit.mul b.unit
    class_eq:=by rw [zh2 E a.a b.a a.ne_zero b.ne_zero,a.class_eq,b.class_eq]; rfl }
  rw [z1x E (v+w) r,z1x E v a,z1x E w b]
  exact z5.zia E a.a b.a a.unit b.unit
noncomputable def zeg:Sel E →ₗ[ZMod 2] z6.V (Additive (z5.R E)ˣ) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun:=residue E
    map_zero':=zli E
    map_add':=zm6 E }
end z1z
namespace z3j
open NumberField z7 zg
open scoped Classical
variable (E:Type) [Field E] [NumberField E] [IsTotallyReal E]
noncomputable def signHom (τ:E →+* ℝ):F E →+ ZMod 2 where
  toFun a:=if 0 < τ (a.toMul:E) then 0 else 1
  map_zero':=by change (if 0 < τ 1 then (0:ZMod 2) else 1) = 0; simp
  map_add' a b:=by
    change (if 0 < τ ((a.toMul:E)*(b.toMul:E)) then (0:ZMod 2) else 1) =
      (if 0 < τ (a.toMul:E) then 0 else 1)+(if 0 < τ (b.toMul:E) then 0 else 1)
    rw [map_mul]
    have ha:τ (a.toMul:E) ≠ 0:=by simpa only [map_zero] using τ.injective.ne (Units.ne_zero a.toMul)
    have hb:τ (b.toMul:E) ≠ 0:=by simpa only [map_zero] using τ.injective.ne (Units.ne_zero b.toMul)
    by_cases ha':0 < τ (a.toMul:E) <;> by_cases hb':0 < τ (b.toMul:E)
    · simp [ha',hb',mul_pos ha' hb']
    · have hb'':τ (b.toMul:E) < 0:=lt_of_le_of_ne (le_of_not_gt hb') hb
      simp [ha',hb',not_lt.mpr (mul_neg_of_pos_of_neg ha' hb'').le]
    · have ha'':τ (a.toMul:E) < 0:=lt_of_le_of_ne (le_of_not_gt ha') ha
      simp [ha',hb',not_lt.mpr (mul_neg_of_neg_of_pos ha'' hb').le]
    · have ha'':τ (a.toMul:E) < 0:=lt_of_le_of_ne (le_of_not_gt ha') ha
      have hb'':τ (b.toMul:E) < 0:=lt_of_le_of_ne (le_of_not_gt hb') hb
      simp only [if_neg ha',if_neg hb',if_pos (mul_pos_of_neg_of_neg ha'' hb'')]
      exact (CharTwo.add_self_eq_zero (1:ZMod 2)).symm
noncomputable def z5i (φ:E →+* ℂ):z6.V (F E) →ₗ[ZMod 2] ZMod 2 :=
  (ModN.liftEquiv' (n:=2)).symm
    ⟨signHom E (IsTotallyReal.complexEmbedding_isReal φ).embedding,fun a => by
      simpa only [two_nsmul] using CharTwo.add_self_eq_zero
        (signHom E (IsTotallyReal.complexEmbedding_isReal φ).embedding a)⟩
@[simp] lemma z8p (φ:E →+* ℂ) (a:F E) :
    z5i E φ (z6.mk a) = if 0 < (φ (a.toMul:E)).re then 0 else 1:=rfl
lemma zhx (φ:E →+* ℂ) (a:F E) (h:z5i E φ (z6.mk a) = 0) :
    0 < (φ (a.toMul:E)).re:=by
  simpa only [z8p,ite_eq_left_iff,one_ne_zero,imp_false,not_not] using h
variable (K:Type) [Field K] [NumberField K] [Algebra K E]
lemma equivariant (φ:E →+* ℂ) (g:Gal(E/K)) (v:z6.V (F E)) :
    z5i E φ (z6.map (z15 K E g).toAddMonoidHom v) =
      z5i E (φ.comp g.toRingHom) v:=by
  obtain ⟨a,rfl⟩:=z6.mk_surjective v
  rw [z6.map_mk,z8p,z8p]
  rfl
variable [FiniteDimensional K E] [IsGalois K E]
noncomputable def zak:z6.fixed (z15 K E) →ₗ[ZMod 2] ((K →+* ℂ) → ZMod 2) :=
  LinearMap.pi (fun φ => (z5i E (ComplexEmbedding.lift E φ)).comp (z6.fixed (z15 K E)).subtype)
lemma z8x (v:z6.fixed (z15 K E)) (hv:zak E K v = 0)
    (a:F E) (ha:z6.mk a = v.1):∀ φ:E →+* ℂ, 0 < (φ (a.toMul:E)).re:=by
  intro φ
  let τ:K →+* ℂ:=φ.comp (algebraMap K E)
  let ψ:E →+* ℂ:=ComplexEmbedding.lift E τ
  obtain ⟨g,hg⟩:=ComplexEmbedding.exists_comp_symm_eq_of_comp_eq ψ φ (by
    exact ComplexEmbedding.lift_comp_algebraMap E τ)
  have hψ:z5i E ψ v.1 = 0:=congrFun hv τ
  have he:=equivariant E K ψ g.symm v.1
  change ψ.comp g.symm.toRingHom = φ at hg
  rw [v.property g.symm,hg] at he
  apply zhx E φ a
  rw [ha,← he,hψ]
lemma zko:Module.finrank (ZMod 2) ((K →+* ℂ) → ZMod 2) = Module.finrank ℚ K:=by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,NumberField.Embeddings.card,Nat.cast_id]
end z3j
namespace z1z
open NumberField z7 z10 zg
open scoped Classical nonZeroDivisors
variable (E:Type) [Field E] [NumberField E]
def z3s:Prop:=∀ (a b c:𝓞 E), a ≠ 0 → IsCoprime a 2 → a = b^2+4*c →
  ∀ I:FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → FractionalIdeal.spanSingleton (𝓞 E)⁰ (a:E) = I*I →
  (∀ φ:E →+* ℂ, 0 ≤ (φ (a:E)).re) → IsSquare (a:E)
lemma z6v (a:𝓞 E) (ha:a ≠ 0) (hs:IsSquare (a:E)) :
    z2a E a ha = 0:=by
  obtain ⟨x,hx⟩:=hs
  have hx0:x ≠ 0:=by
    intro h
    apply RingOfIntegers.coe_ne_zero_iff.mpr ha
    change (a:E) = 0
    rw [hx,h,zero_mul]
  let u:Eˣ:=Units.mk0 x hx0
  have he:Units.mk0 (a:E) (RingOfIntegers.coe_ne_zero_iff.mpr ha) = u*u:=Units.ext hx
  change z6.mk (Additive.ofMul (Units.mk0 (a:E) _)) = 0
  rw [he]
  exact z6.z7b (Additive.ofMul u)
variable (K:Type) [Field K] [NumberField K] [Algebra K E]
noncomputable def z47:z1a.z25 K E →ₗ[ZMod 2] Sel E where
  toFun v:=⟨v.1.1,congrArg Subtype.val v.property⟩
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
variable [IsTotallyReal E] [FiniteDimensional K E] [IsGalois K E]
noncomputable def zmr:z1a.z25 K E →ₗ[ZMod 2]
    z6.V (Additive (z5.R E)ˣ) × ((K →+* ℂ) → ZMod 2) :=
  ((zeg E).comp (z47 E K)).prod
    ((z3j.zak E K).comp (z1a.z25 K E).subtype)
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in
lemma zec (hterm:z3s E):Function.Injective (zmr E K):=by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hr:residue E (z47 E K v) = 0:=congrArg Prod.fst hv
  have hs:z3j.zak E K v.1 = 0:=congrArg Prod.snd hv
  let r:=(z28 E (z47 E K v)).some
  have hres:z5.z1f E r.a r.unit = 0:=by
    rw [← z1x E (z47 E K v) r]
    exact hr
  obtain ⟨b,c,hbc⟩:=z5.zch E r.a r.unit hres
  have hcop:IsCoprime r.a (4:𝓞 E):=(z5.za0 E r.a).mp r.unit
  have hcop2:IsCoprime r.a (2:𝓞 E) :=
    (IsCoprime.pow_right_iff (by norm_num:0 < 2)).mp (by simpa only [show (2:𝓞 E)^2 = 4 by norm_num] using hcop)
  let a:F E:=Additive.ofMul (Units.mk0 (r.a:E) (RingOfIntegers.coe_ne_zero_iff.mpr r.ne_zero))
  have ha:z6.mk a = v.1.1:=r.class_eq
  have hpositive (φ:E →+* ℂ):0 ≤ (φ (r.a:E)).re :=
    (z3j.z8x E K v.1 hs a ha φ).le
  have hdiv:z6.mk (z4.z11 E a) = 0:=by
    have hh:=(z47 E K v).property
    change divisor E v.1.1 = 0 at hh
    rw [← ha] at hh
    exact hh
  obtain ⟨I,hI⟩:=(z6.mk_eq_zero _).mp hdiv
  have hvirt:FractionalIdeal.spanSingleton (𝓞 E)⁰ (r.a:E) = I.toMul.1*I.toMul.1:=by
    have he:=congrArg (fun I:D E => I.toMul.1) hI.symm
    change (toPrincipalIdeal (𝓞 E) E a.toMul:FractionalIdeal (𝓞 E)⁰ E) = _ at he
    simpa only [a,coe_toPrincipalIdeal,toMul_add,Units.val_mul,toMul_ofMul,Units.val_mk0] using he
  have hsq:=hterm r.a b c r.ne_zero hcop2 hbc I.toMul.1 I.toMul.ne_zero hvirt hpositive
  have hz:=z6v E r.a r.ne_zero hsq
  apply Subtype.ext
  apply Subtype.ext
  exact r.class_eq.symm.trans hz
end z1z
namespace z12
open NumberField
open scoped Classical
variable (E:Type*) [Field E] [NumberField E]
def modulus:Ideal (𝓞 E):=Ideal.span {(2:𝓞 E)}
abbrev R:=𝓞 E ⧸ modulus E
abbrev reduce:𝓞 E →+* R E:=Ideal.Quotient.mk (modulus E)
@[simp] lemma zj8:reduce E 2 = 0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
lemma z64:modulus E ≠ ⊤:=by
  intro h
  have hm:Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(2:ℤ)}) = ⊤:=by
    simpa only [Ideal.map_span,Set.image_singleton,map_ofNat,modulus] using h
  have he:=(Ideal.map_eq_top_iff (algebraMap ℤ (𝓞 E))
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp hm
  have hu:IsUnit (2:ℤ):=Ideal.span_singleton_eq_top.mp he
  norm_num [Int.isUnit_iff] at hu
instance:Nontrivial (R E):=Ideal.Quotient.nontrivial_iff.mpr (z64 E)
instance:Finite (R E):=(modulus E).finiteQuotientOfFreeOfNeBot (by simp [modulus])
instance:CharP (R E) 2:=(CharP.charP_iff_prime_eq_zero (by norm_num:Nat.Prime 2)).mpr (by
  simpa only [map_ofNat,Nat.cast_ofNat] using zj8 E)
noncomputable instance:Algebra (ZMod 2) (R E):=ZMod.algebra _ _
instance:FiniteDimensional (ZMod 2) (R E):=Module.Finite.of_finite
lemma finrank:Module.finrank (ZMod 2) (R E) = Module.finrank ℚ E:=by
  apply Nat.pow_right_injective (a:=2) (by norm_num)
  have hc:Nat.card (R E) = 2^Module.finrank ℚ E:=by
    change Ideal.absNorm (modulus E) = _
    rw [modulus,Ideal.absNorm_span_singleton]
    have hn:=Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis E) (2:ℤ)
    rw [← Module.finrank_eq_card_basis (RingOfIntegers.basis E),RingOfIntegers.rank] at hn
    simpa only [map_ofNat,Int.natAbs_pow,show (2:ℤ).natAbs = 2 from rfl] using congrArg Int.natAbs hn
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2), Nat.card_eq_fintype_card,ZMod.card] at hc
  exact hc
variable (K:Type*) [Field K] [NumberField K] [Algebra K E]
noncomputable def action (g:Gal(E/K)):R E ≃+* R E :=
  Ideal.quotientEquiv (modulus E) (modulus E) (RingOfIntegers.mapAlgEquiv g).toRingEquiv
    (by simp only [modulus,Ideal.map_span,Set.image_singleton,map_ofNat])
@[simp] lemma z3d (g:Gal(E/K)) (a:𝓞 E) :
    action E K g (reduce E a) = reduce E (RingOfIntegers.mapAlgEquiv g a):=rfl
noncomputable def zln (g:Gal(E/K)):R E →ₗ[ZMod 2] R E :=
  AddMonoidHom.toZModLinearMap 2 (action E K g).toAddMonoidHom
noncomputable def fixed:Submodule (ZMod 2) (R E) where
  carrier:={x | ∀ g, action E K g x = x}
  zero_mem' g:=map_zero _
  add_mem' hx hy g:=by rw [map_add,hx g,hy g]
  smul_mem' c x hx g:=by
    change zln E K g (c • x) = c • x
    rw [map_smul]
    exact congrArg (c • ·) (hx g)
noncomputable def extend:R K →+* R E :=
  Ideal.quotientMap (modulus E) (algebraMap (𝓞 K) (𝓞 E)) (by
    rw [modulus,Ideal.span_le]
    rintro x (rfl:x = 2)
    change algebraMap (𝓞 K) (𝓞 E) 2 ∈ modulus E
    simp only [map_ofNat]
    exact Ideal.mem_span_singleton_self _)
@[simp] lemma zem (a:𝓞 K) :
    extend E K (reduce K a) = reduce E (algebraMap (𝓞 K) (𝓞 E) a):=rfl
noncomputable def zh9:R K →ₗ[ZMod 2] fixed E K :=
  (AddMonoidHom.toZModLinearMap 2 (extend E K).toAddMonoidHom).codRestrict _ (by
    intro x g
    obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
    change action E K g (extend E K (reduce K a)) = extend E K (reduce K a)
    rw [zem,z3d]
    congr 1
    apply RingOfIntegers.coe_injective
    exact g.commutes (a:K))
end z12
namespace z36
open NumberField
open scoped Classical
variable (E:Type*) [Field E] [NumberField E]
abbrev U:=Additive (z5.R E)ˣ
abbrev W:=z6.V (U E)
noncomputable def toTwo:(z5.R E) →+* (z12.R E) :=
  Ideal.quotientMap (z12.modulus E) (RingHom.id _) (by
    rw [z5.modulus,Ideal.span_le]
    rintro x (rfl:x = 4)
    change (4:𝓞 E) ∈ Ideal.span {(2:𝓞 E)}
    exact Ideal.mem_span_singleton.mpr ⟨2,by norm_num⟩)
@[simp] lemma zap (a:𝓞 E):toTwo E ((z5.reduce E) a) = (z12.reduce E) a:=rfl
private lemma zg2 (a:𝓞 E):(z5.reduce E) (1+2*a)*(z5.reduce E) (1+2*a) = 1:=by
  rw [← map_mul]
  have he:(1+2*a)*(1+2*a) = 1+4*(a+a*a):=by ring
  rw [he,map_add,map_mul,z5.z8r,zero_mul,map_one,add_zero]
noncomputable def principal (a:𝓞 E):(z5.R E)ˣ :=
  Units.mkOfMulEqOne ((z5.reduce E) (1+2*a)) ((z5.reduce E) (1+2*a)) (zg2 E a)
noncomputable def zfi:𝓞 E →+ U E where
  toFun a:=Additive.ofMul (principal E a)
  map_zero':=by apply Additive.toMul.injective; apply Units.ext; simp [principal]
  map_add' a b:=by
    apply Additive.toMul.injective
    apply Units.ext
    change (z5.reduce E) (1+2*(a+b)) = (z5.reduce E) (1+2*a)*(z5.reduce E) (1+2*b)
    rw [← map_mul]
    have he:(1+2*a)*(1+2*b) = (1+2*(a+b))+4*(a*b):=by ring
    simp only [he,map_add,map_mul,z5.z8r,zero_mul,add_zero]
private lemma zkn:((z12.reduce E)).toAddMonoidHom.ker ≤ (zfi E).ker:=by
  intro a ha
  change (z12.reduce E) a = 0 at ha
  obtain ⟨b,hb⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  change Additive.ofMul (principal E a) = 0
  apply Additive.toMul.injective
  apply Units.ext
  change (z5.reduce E) (1+2*a) = 1
  rw [hb]
  have he:(1+2*(2*b)) = (1+4*b):=by ring
  rw [he,map_add,map_mul,z5.z8r,zero_mul,map_one,add_zero]
noncomputable def z2x:(z12.R E) →+ U E :=
  ((z12.reduce E)).toAddMonoidHom.liftOfSurjective Ideal.Quotient.mk_surjective ⟨zfi E,zkn E⟩
@[simp] lemma z32 (a:𝓞 E) :
    z2x E ((z12.reduce E) a) = Additive.ofMul (principal E a):=by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
noncomputable def z2w:(z12.R E) →ₗ[ZMod 2] W E :=
  AddMonoidHom.toZModLinearMap 2 (z6.mk.comp (z2x E))
@[simp] lemma z68 (a:𝓞 E) :
    z2w E ((z12.reduce E) a) = z6.mk (Additive.ofMul (principal E a)):=by
  change z6.mk (z2x E ((z12.reduce E) a)) = _
  rw [z32]
lemma zb7:Function.Injective (z2x E):=by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [z32] at hx
  have he:=congrArg (fun u:U E => (u.toMul:(z5.R E))) hx
  change (z5.reduce E) (1+2*a) = 1 at he
  rw [← map_one (z5.reduce E)] at he
  obtain ⟨b,hb⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hb':2*b = a:=by
    have htwo:(2:𝓞 E) ≠ 0:=by norm_num
    apply mul_left_cancel₀ htwo
    linear_combination -hb
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨b,hb'.symm⟩
variable [IsReduced (z12.R E)]
private lemma zej (u:(z5.R E)ˣ) (hu:toTwo E ((u:(z5.R E))^2) = 1) :
    toTwo E (u:(z5.R E)) = 1:=by
  apply frobenius_inj (z12.R E) 2
  change (toTwo E (u:(z5.R E)))^2 = (1:(z12.R E))^2
  simpa only [map_pow,one_pow] using hu
lemma zhw (u:U E) (hu:u+u = 0):∃ x:(z12.R E), z2x E x = u:=by
  have hu':(u.toMul:(z5.R E))^2 = 1:=by
    have h:=congrArg (fun u:U E => (u.toMul:(z5.R E))) hu
    simpa only [pow_two,toMul_add,toMul_zero,Units.val_mul,Units.val_one] using h
  have hred:toTwo E (u.toMul:(z5.R E)) = 1:=zej E u.toMul (by rw [hu',map_one])
  obtain ⟨a,ha⟩:=Ideal.Quotient.mk_surjective (u.toMul:(z5.R E))
  change (z5.reduce E) a = (u.toMul:(z5.R E)) at ha
  have ha':(z12.reduce E) a = (z12.reduce E) 1:=by rw [← zap,ha,hred,map_one]
  obtain ⟨b,hb⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp ha')
  have he:a = 1+2*b:=by linear_combination hb
  refine ⟨(z12.reduce E) b,?_⟩
  rw [z32]
  apply Additive.toMul.injective
  apply Units.ext
  change (z5.reduce E) (1+2*b) = (u.toMul:(z5.R E))
  rw [← he,ha]
lemma z9x:Function.Injective (z2w E):=by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change z6.mk (z2x E x) = 0 at hx
  obtain ⟨u,hu⟩:=(z6.mk_eq_zero _).mp hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [z32] at hu
  have he:=congrArg (fun u:U E => (u.toMul:(z5.R E))) hu
  change (u.toMul:(z5.R E))*(u.toMul:(z5.R E)) = (z5.reduce E) (1+2*a) at he
  have hred:toTwo E (u.toMul:(z5.R E)) = 1:=by
    apply zej E u.toMul
    rw [pow_two,he,zap,map_add,map_mul,map_one,z12.zj8,zero_mul,add_zero]
  obtain ⟨b,hb⟩:=Ideal.Quotient.mk_surjective (u.toMul:(z5.R E))
  change (z5.reduce E) b = (u.toMul:(z5.R E)) at hb
  have hb':(z12.reduce E) b = (z12.reduce E) 1:=by rw [← zap,hb,hred,map_one]
  obtain ⟨c,hc⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hb')
  have hbc:b = 1+2*c:=by linear_combination hc
  have hu0:u+u = 0:=by
    apply Additive.toMul.injective
    apply Units.ext
    change (u.toMul:(z5.R E))*(u.toMul:(z5.R E)) = 1
    rw [← hb,hbc]
    exact zg2 E c
  apply zb7 E
  rw [map_zero,z32,← hu,hu0]
lemma z9j:Function.Bijective (z2w E):=by
  letI:Finite (W E):=Finite.of_surjective z6.mk z6.mk_surjective
  apply (z9x E).bijective_of_nat_card_le
  rw [z3u.z82 (U E) 2]
  let f:(z12.R E) → (z3u.mulN (U E) 2).ker:=fun x =>
    ⟨z2x E x,by
      change (2:ℤ) • z2x E x = 0
      rw [two_zsmul]
      rw [← map_add,CharTwo.add_self_eq_zero,map_zero]⟩
  apply Nat.card_le_card_of_surjective f
  intro u
  have hu:=u.property
  change (2:ℤ) • u.1 = 0 at hu
  rw [two_zsmul] at hu
  obtain ⟨x,hx⟩:=zhw E u.1 hu
  exact ⟨x,Subtype.ext hx⟩
noncomputable def equiv:(z12.R E) ≃ₗ[ZMod 2] W E :=
  LinearEquiv.ofBijective (z2w E) (z9j E)
end z36
namespace z38
open NumberField
open scoped nonZeroDivisors Classical
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]
noncomputable def trace:𝓞 E →ₗ[𝓞 K] 𝓞 K where
  toFun x:=⟨Algebra.trace K E (x:E), Algebra.isIntegral_trace x.property⟩
  map_add' x y:=by apply RingOfIntegers.coe_injective; exact map_add (Algebra.trace K E) _ _
  map_smul' r x:=by
    apply RingOfIntegers.coe_injective
    change Algebra.trace K E ((algebraMap K E (r:K))*(x:E)) = (r:K)*Algebra.trace K E (x:E)
    simpa only [Algebra.smul_def,smul_eq_mul,Algebra.algebraMap_self,RingHom.id_apply] using map_smul (Algebra.trace K E) (r:K) (x:E)
lemma zkl (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    FractionalIdeal.dual (𝓞 K) K (1:FractionalIdeal (𝓞 E)⁰ E) = 1:=by
  have h:=coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)
  rw [hunram,FractionalIdeal.coeIdeal_top] at h
  have:=congrArg (fun I:FractionalIdeal (𝓞 E)⁰ E => I⁻¹) h
  simpa only [inv_one,inv_inv] using this.symm
lemma zd8 (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (hJ:(LinearMap.range (trace K E):Ideal (𝓞 K)) ≠ ⊥) :
    ((LinearMap.range (trace K E):Ideal (𝓞 K)):FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤ 1:=by
  intro x hx
  have hJ0:((LinearMap.range (trace K E):Ideal (𝓞 K)):FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_eq_zero.not.mpr hJ
  have hx':∀ y:𝓞 E, x*Algebra.trace K E (y:E) ∈ (1:FractionalIdeal (𝓞 K)⁰ K):=by
    intro y
    exact (FractionalIdeal.mem_inv_iff hJ0).mp hx _
      (FractionalIdeal.mem_coeIdeal_of_mem _ (show trace K E y ∈ LinearMap.range (trace K E) from ⟨y,rfl⟩))
  have hmem:algebraMap K E x ∈ FractionalIdeal.dual (𝓞 K) K (1:FractionalIdeal (𝓞 E)⁰ E):=by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro y hy
    obtain ⟨b,rfl⟩:=(FractionalIdeal.mem_one_iff _).mp hy
    change Algebra.trace K E (algebraMap K E x*(b:E)) ∈ (algebraMap (𝓞 K) K).range
    have ht:Algebra.trace K E (algebraMap K E x*(b:E)) = x*Algebra.trace K E (b:E):=by
      simpa only [Algebra.smul_def,smul_eq_mul,Algebra.algebraMap_self,RingHom.id_apply] using map_smul (Algebra.trace K E) x (b:E)
    rw [ht]
    exact (FractionalIdeal.mem_one_iff _).mp (hx' b)
  rw [zkl K E hunram] at hmem
  obtain ⟨a,ha⟩:=(FractionalIdeal.mem_one_iff _).mp hmem
  have hi:IsIntegral ℤ (algebraMap K E x):=ha ▸ a.property
  have hxint:IsIntegral ℤ x:=(isIntegral_algebraMap_iff (algebraMap K E).injective).mp hi
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x,hxint⟩,rfl⟩
lemma za5:(LinearMap.range (trace K E):Ideal (𝓞 K)) ≠ ⊥:=by
  intro h
  have hz:trace K E 1 = 0:=by
    have hm:trace K E 1 ∈ LinearMap.range (trace K E):=⟨1,rfl⟩
    rw [h] at hm
    exact hm
  have he:=congrArg (fun x:𝓞 K => (x:K)) hz
  change Algebra.trace K E 1 = 0 at he
  rw [← map_one (algebraMap K E),Algebra.trace_algebraMap] at he
  have hd:(Module.finrank K E:K) ≠ 0:=Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  exact hd (by simpa only [nsmul_eq_mul,mul_one] using he)
lemma trace_surjective (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Function.Surjective (trace K E):=by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  apply (FractionalIdeal.coeIdeal_le_coeIdeal K).mp
  rw [FractionalIdeal.coeIdeal_top]
  have h:=zd8 K E hunram (za5 K E)
  have h':=(FractionalIdeal.inv_le_comm (A:=𝓞 K) (K:=K) (J:=1)
    (FractionalIdeal.coeIdeal_eq_zero.not.mpr (za5 K E)) (by simp)).mp h
  simpa only [inv_one] using h'
lemma zhh (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    ∃ t:𝓞 E, Algebra.trace K E (t:E) = 1:=by
  obtain ⟨t,ht⟩:=trace_surjective K E hunram 1
  exact ⟨t,congrArg (fun x:𝓞 K => (x:K)) ht⟩
variable [IsGalois K E]
lemma zau (x:𝓞 E) :
    algebraMap (𝓞 K) (𝓞 E) (trace K E x) = ∑ g:Gal(E/K), RingOfIntegers.mapAlgEquiv g x:=by
  apply RingOfIntegers.coe_injective
  change algebraMap K E (Algebra.trace K E (x:E)) = _
  rw [trace_eq_sum_automorphisms]
  simp only [map_sum]
  rfl
end z38
namespace z12
open NumberField
open scoped Classical
variable (E K:Type*) [Field E] [Field K] [NumberField E] [NumberField K]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
lemma zce (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Function.Surjective (zh9 E K):=by
  intro v
  obtain ⟨t,ht⟩:=z38.zhh K E hunram
  obtain ⟨x,hx⟩:=Ideal.Quotient.mk_surjective v.1
  change reduce E x = v.1 at hx
  refine ⟨reduce K (z38.trace K E (t*x)),?_⟩
  apply Subtype.ext
  change extend E K (reduce K (z38.trace K E (t*x))) = v.1
  rw [zem,z38.zau,map_sum]
  have hgx (g:Gal(E/K)):reduce E (RingOfIntegers.mapAlgEquiv g x) = v.1:=by
    rw [← z3d,hx]
    exact v.property g
  simp_rw [map_mul,hgx,← Finset.sum_mul,← map_sum,← z38.zau]
  have ht':z38.trace K E t = 1:=RingOfIntegers.coe_injective ht
  rw [ht',map_one,map_one,one_mul]
lemma z74 (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (fixed E K) ≤ Module.finrank ℚ K:=by
  rw [← finrank K]
  have h:=LinearMap.finrank_range_le (zh9 E K)
  rw [LinearMap.range_eq_top.mpr (zce E K hunram),finrank_top] at h
  exact h
end z12
namespace z5
open NumberField
open scoped Classical
variable (E K:Type*) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]
noncomputable def action (g:Gal(E/K)):R E ≃+* R E :=
  Ideal.quotientEquiv (modulus E) (modulus E) (RingOfIntegers.mapAlgEquiv g).toRingEquiv
    (by simp only [modulus,Ideal.map_span,Set.image_singleton,map_ofNat])
@[simp] lemma z3d (g:Gal(E/K)) (a:𝓞 E) :
    action E K g (reduce E a) = reduce E (RingOfIntegers.mapAlgEquiv g a):=rfl
lemma zmz (x:R E):action E K 1 x = x:=by
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rfl
lemma zmt (g h:Gal(E/K)) (x:R E):action E K (g*h) x = action E K g (action E K h x):=by
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rfl
noncomputable def z2i:Gal(E/K) →* AddAut (Additive (R E)ˣ) where
  toFun g:=(Units.mapEquiv (action E K g).toMulEquiv).toAdditive
  map_one':=by
    apply AddEquiv.ext
    intro u
    apply Additive.toMul.injective
    apply Units.ext
    exact zmz E K (u.toMul:R E)
  map_mul' g h:=by
    apply AddEquiv.ext
    intro u
    apply Additive.toMul.injective
    apply Units.ext
    exact zmt E K g h (u.toMul:R E)
lemma zg8 (g:Gal(E/K)) (a:𝓞 E) (ha:IsUnit (reduce E a)) :
    z1f E (RingOfIntegers.mapAlgEquiv g a) (by
      rw [← z3d]; exact ha.map (action E K g).toMonoidHom) =
      z6.map (z2i E K g).toAddMonoidHom (z1f E a ha):=by
  simp only [z1f,z6.map_mk]
  apply congrArg z6.mk
  apply Additive.toMul.injective
  apply Units.ext
  change (unit E (RingOfIntegers.mapAlgEquiv g a) _:R E) = action E K g (unit E a ha:R E)
  simp only [zdy,z3d]
end z5
namespace z36
open NumberField
open scoped Classical
variable (E K:Type*) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]
lemma z8m (g:Gal(E/K)) (x:z12.R E) :
    z2w E (z12.action E K g x) =
      z6.map (z5.z2i E K g).toAddMonoidHom (z2w E x):=by
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [z12.z3d,z68,z68,z6.map_mk]
  apply congrArg z6.mk
  apply Additive.toMul.injective
  apply Units.ext
  change z5.reduce E (1+2*RingOfIntegers.mapAlgEquiv g a) =
    z5.action E K g (z5.reduce E (1+2*a))
  simp only [z5.z3d,map_add,map_mul,map_one,map_ofNat]
variable [IsReduced (z12.R E)]
noncomputable def zn6:z6.fixed (z5.z2i E K) →ₗ[ZMod 2]
    z12.fixed E K :=
  ((equiv E).symm.toLinearMap.comp (z6.fixed (z5.z2i E K)).subtype).codRestrict _ (by
    intro w g
    apply (equiv E).injective
    change z2w E (z12.action E K g ((equiv E).symm w.1)) = _
    rw [z8m]
    change z6.map (z5.z2i E K g).toAddMonoidHom
      ((equiv E) ((equiv E).symm w.1)) = (equiv E) ((equiv E).symm w.1)
    rw [LinearEquiv.apply_symm_apply]
    exact w.property g)
lemma zdi:Function.Injective (zn6 E K):=by
  intro x y h
  apply Subtype.ext
  apply (equiv E).symm.injective
  exact congrArg Subtype.val h
variable [FiniteDimensional K E] [IsGalois K E]
lemma z74 (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (z6.fixed (z5.z2i E K)) ≤ Module.finrank ℚ K:=by
  exact (LinearMap.finrank_le_finrank_of_injective (zdi E K)).trans
    (z12.z74 E K hunram)
end z36
namespace z1z
open NumberField z7 zg
open scoped Classical
variable (E K:Type) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]
lemma ze1 (g:Gal(E/K)) (a:𝓞 E) (ha:a ≠ 0) :
    z2a E (RingOfIntegers.mapAlgEquiv g a) (by
      simpa only [map_zero] using (RingOfIntegers.mapAlgEquiv g).injective.ne ha) =
      z6.map (z15 K E g).toAddMonoidHom (z2a E a ha):=by
  unfold z2a
  rw [z6.map_mk]
  apply congrArg z6.mk
  apply Additive.toMul.injective
  apply Units.ext
  rfl
lemma zka (v:z1a.z25 K E) :
    residue E (z47 E K v) ∈ z6.fixed (z5.z2i E K):=by
  intro g
  let r:=(z28 E (z47 E K v)).some
  let s:Representative E v.1.1:={
    a:=RingOfIntegers.mapAlgEquiv g r.a
    ne_zero:=by simpa only [map_zero] using (RingOfIntegers.mapAlgEquiv g).injective.ne r.ne_zero
    unit:=by
      rw [← z5.z3d E K]
      exact r.unit.map (z5.action E K g).toMonoidHom
    class_eq:=by
      rw [ze1 E K g r.a r.ne_zero,r.class_eq]
      exact v.1.property g }
  have hr:=z1x E (z47 E K v) r
  have hs:=z1x E (z47 E K v) s
  rw [hr]
  change z6.map (z5.z2i E K g).toAddMonoidHom
    (z5.z1f E r.a r.unit) = z5.z1f E r.a r.unit
  rw [← z5.zg8 E K g r.a r.unit]
  exact hs.symm.trans hr
noncomputable def zl9:z1a.z25 K E →ₗ[ZMod 2]
    z6.fixed (z5.z2i E K) :=
  ((zeg E).comp (z47 E K)).codRestrict _ (zka E K)
variable [IsTotallyReal E] [FiniteDimensional K E] [IsGalois K E]
noncomputable def zby:z1a.z25 K E →ₗ[ZMod 2]
    z6.fixed (z5.z2i E K) × ((K →+* ℂ) → ZMod 2) :=
  (zl9 E K).prod
    ((z3j.zak E K).comp (z1a.z25 K E).subtype)
lemma z5n (hterm:z3s E) :
    Function.Injective (zby E K):=by
  intro x y h
  apply zec E K hterm
  apply Prod.ext
  · exact congrArg (fun z:z6.fixed (z5.z2i E K) × ((K →+* ℂ) → ZMod 2) => z.1.1) h
  · exact congrArg (fun z:z6.fixed (z5.z2i E K) × ((K →+* ℂ) → ZMod 2) => z.2) h
lemma zbr (hterm:z3s E)
    [IsReduced (z12.R E)]
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (z1a.z25 K E) ≤ 2*Module.finrank ℚ K:=by
  letI:Finite (z6.V (Additive (z5.R E)ˣ)) :=
    Finite.of_surjective z6.mk z6.mk_surjective
  letI:FiniteDimensional (ZMod 2) (z6.fixed (z5.z2i E K)) :=
    Module.Finite.of_finite
  have h:=LinearMap.finrank_le_finrank_of_injective (z5n E K hterm)
  rw [Module.finrank_prod,z3j.zko] at h
  have hres:=z36.z74 E K hunram
  omega
lemma z7m (hterm:z3s E) :
    FiniteDimensional (ZMod 2) (z1a.z25 K E):=by
  letI:Finite (z6.V (Additive (z5.R E)ˣ)) :=
    Finite.of_surjective z6.mk z6.mk_surjective
  letI:FiniteDimensional (ZMod 2) (z6.fixed (z5.z2i E K)) :=
    Module.Finite.of_finite
  exact FiniteDimensional.of_injective (zby E K) (z5n E K hterm)
end z1z

namespace z1a
open NumberField z7
open scoped Classical
variable (K E:Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]
lemma zbi (hG:IsPGroup 2 Gal(E/K))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (hterm:z1z.z3s E)
    [IsReduced (z12.R E)] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Gal(E/K) (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2) (z6.V (C K))+2*Module.finrank ℚ K:=by
  letI:=z1z.z7m E K hterm
  exact (z3m K E hG hunram).trans
    (Nat.add_le_add_left (z1z.zbr E K hterm hunram) _)
end z1a
namespace z7v
open scoped Classical
variable (p:ℕ) [Fact p.Prime] {G V:Type*} [Group G]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
lemma zlb [Nontrivial V] (hG:IsPGroup p G) (ρ:Representation (ZMod p) G V) :
    ∃ v:V, v ≠ 0 ∧ ∀ g:G, ρ g v = v:=by
  letI:Finite V:=Finite.of_equiv (Fin (Module.finrank (ZMod p) V) → ZMod p)
    (Module.finBasis (ZMod p) V).equivFun.symm.toEquiv
  letI:MulAction G V:={
    smul:=fun g v => ρ g v
    one_smul:=fun v => by change ρ 1 v = v; rw [map_one]; rfl
    mul_smul:=fun g h v => by change ρ (g*h) v = ρ g (ρ h v); rw [map_mul]; rfl }
  have hpV:p ∣ Nat.card V:=by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod p),Nat.card_eq_fintype_card,ZMod.card]
    have hd:0 < Module.finrank (ZMod p) V:=Module.finrank_pos
    rw [← Nat.succ_pred_eq_of_pos hd,pow_succ]
    exact dvd_mul_left _ _
  have hz:(0:V) ∈ MulAction.fixedPoints G V:=by
    apply MulAction.mem_fixedPoints.mpr
    intro g
    exact (ρ g).map_zero
  obtain ⟨v,hv,hv0⟩:=hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV hz
  exact ⟨v,hv0.symm,MulAction.mem_fixedPoints.mp hv⟩
lemma z8w [Nontrivial V] (hG:IsPGroup p G) (ρ:Representation (ZMod p) G V) :
    ∃ f:Module.Dual (ZMod p) V, f ≠ 0 ∧ ∀ g:G, ∀ v:V, f (ρ g v) = f v:=by
  obtain ⟨f,hf,hfix⟩:=zlb p hG ρ.dual
  refine ⟨f,hf,?_⟩
  intro g v
  have hh:=congrArg (fun f:Module.Dual (ZMod p) V => f v) (hfix g⁻¹)
  simpa only [Representation.dual_apply,Module.Dual.transpose_apply,inv_inv,LinearMap.coe_comp,Function.comp_apply] using hh
end z7v
namespace zv
open scoped Classical
variable (k G:Type*) [Field k] [Group G]
noncomputable def augmentation:MonoidAlgebra k G →ₐ[k] k:=MonoidAlgebra.lift k k G (1:G →* k)
noncomputable def ideal:Ideal (MonoidAlgebra k G):=RingHom.ker (augmentation k G).toRingHom
instance:(ideal k G).IsTwoSided:=inferInstanceAs (RingHom.ker (augmentation k G).toRingHom).IsTwoSided
@[simp] lemma z5l (g:G) (r:k):augmentation k G (MonoidAlgebra.single g r) = r:=by
  simp [augmentation,MonoidAlgebra.lift_single]
@[simp] lemma augmentation_of (g:G):augmentation k G (MonoidAlgebra.of k G g) = 1:=by
  exact z5l k G g 1
lemma z5v (a:MonoidAlgebra k G):a ∈ ideal k G ↔ augmentation k G a = 0:=Iff.rfl
lemma zkz:ideal k G ≠ ⊤:=by
  intro h
  have hh:(1:MonoidAlgebra k G) ∈ ideal k G:=by rw [h]; trivial
  change augmentation k G 1 = 0 at hh
  simp at hh
variable {M:Type*} [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]
lemma map_smul (f:M →ₗ[k] k)
    (hf:∀ g:G, ∀ v:M, f (MonoidAlgebra.of k G g • v) = f v)
    (a:MonoidAlgebra k G) (v:M):f (a • v) = augmentation k G a * f v:=by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa only [augmentation_of,one_mul] using hf g v
  | add a b ha hb => rw [add_smul,map_add,ha,hb,map_add,add_mul]
  | smul r a ha =>
    have hau:augmentation k G (r • a) = r • augmentation k G a :=
      (augmentation k G).toLinearMap.map_smul r a
    rw [smul_assoc,f.map_smul,ha,hau]
    simp only [smul_eq_mul,mul_assoc]
lemma zm4 (p:ℕ) [Fact p.Prime] {M:Type*} [AddCommGroup M]
    [Module (ZMod p) M] [Module (MonoidAlgebra (ZMod p) G) M]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
    [FiniteDimensional (ZMod p) M] [Nontrivial M] (hG:IsPGroup p G) :
    ideal (ZMod p) G • (⊤:Submodule (MonoidAlgebra (ZMod p) G) M) ≠ ⊤:=by
  obtain ⟨f,hf,hfix⟩:=z7v.z8w p hG (Representation.ofModule' M)
  have hfi:∀ g:G, ∀ v:M, f (MonoidAlgebra.of (ZMod p) G g • v) = f v:=hfix
  intro he
  apply hf
  ext v
  have hv:v ∈ ideal (ZMod p) G • (⊤:Submodule (MonoidAlgebra (ZMod p) G) M):=by rw [he]; trivial
  change f v = 0
  exact Submodule.smul_induction_on hv (fun a ha v _ => by
    rw [map_smul (ZMod p) G f hfi, (z5v _ _ _).mp ha,zero_mul])
    (fun x y hx hy => by rw [_root_.map_add,hx,hy,add_zero])
end zv
namespace zv
open scoped Classical
variable (G:Type*) [Group G] (p:ℕ) [Fact p.Prime]
variable {M:Type*} [AddCommGroup M] [Module (ZMod p) M]
  [Module (MonoidAlgebra (ZMod p) G) M]
  [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
  [FiniteDimensional (ZMod p) M]
lemma zaj (hG:IsPGroup p G)
    (N:Submodule (MonoidAlgebra (ZMod p) G) M)
    (hN:N ⊔ ideal (ZMod p) G • (⊤:Submodule (MonoidAlgebra (ZMod p) G) M) = ⊤) :
    N = ⊤:=by
  by_contra hne
  letI:Nontrivial (M ⧸ N):=Submodule.Quotient.nontrivial_iff.mpr hne
  letI:FiniteDimensional (ZMod p) (M ⧸ N):=Module.Finite.of_surjective
    (N.mkQ.restrictScalars (ZMod p)) N.mkQ_surjective
  have hh:Submodule.map N.mkQ (ideal (ZMod p) G • (⊤:Submodule (MonoidAlgebra (ZMod p) G) M)) = ⊤ :=
    (Submodule.map_mkQ_eq_top N _).mpr hN
  rw [Submodule.map_smul'',Submodule.map_top,Submodule.range_mkQ] at hh
  exact zm4 G p hG hh
end zv
namespace z6t
variable {k M N P:Type*} [Field k] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
lemma zjw (f:M →ₗ[k] N) (g:P →ₗ[k] M)
    (hex:f.ker = g.range) (D:Submodule k M) (E:Submodule k N) (F:Submodule k P)
    (hf:D.map f = E) (hg:F ≤ D.comap g) :
    Function.Exact (F.mapQ D g hg) (D.mapQ E f (by rw [← hf]; exact Submodule.le_comap_map f D)):=by
  rw [LinearMap.exact_iff]
  ext v
  obtain ⟨x,rfl⟩:=D.mkQ_surjective v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have hfx:f x ∈ E:=(Submodule.Quotient.mk_eq_zero E).mp hx
    rw [← hf] at hfx
    obtain ⟨y,hy,hxy⟩:=hfx
    have hker:x-y ∈ f.ker:=by simp only [LinearMap.mem_ker,map_sub,hxy,sub_self]
    rw [hex] at hker
    obtain ⟨z,hz⟩:=hker
    refine ⟨F.mkQ z,?_⟩
    change D.mkQ (g z) = D.mkQ x
    rw [hz,map_sub]
    have hy0:D.mkQ y = 0:=(Submodule.Quotient.mk_eq_zero D).mpr hy
    rw [hy0,sub_zero]
  · rintro ⟨z,hz⟩
    obtain ⟨p,rfl⟩:=F.mkQ_surjective z
    have hgp:f (g p) = 0:=by
      apply LinearMap.mem_ker.mp
      rw [hex]
      exact LinearMap.mem_range_self _ _
    rw [← hz]
    change E.mkQ (f (g p)) = 0
    rw [hgp,map_zero]
lemma zey [FiniteDimensional k M] [FiniteDimensional k N] [FiniteDimensional k P]
    (f:M →ₗ[k] N) (g:P →ₗ[k] M)
    (hex:f.ker = g.range) (D:Submodule k M) (E:Submodule k N) (F:Submodule k P)
    (hf:D.map f = E) (hg:F ≤ D.comap g) :
    Module.finrank k (M ⧸ D) ≤ Module.finrank k (N ⧸ E)+Module.finrank k (P ⧸ F):=by
  let f':=D.mapQ E f (by rw [← hf]; exact Submodule.le_comap_map f D)
  let g':=F.mapQ D g hg
  have he:f'.ker = g'.range:=LinearMap.exact_iff.mp (zjw f g hex D E F hf hg)
  have hh:=f'.finrank_range_add_finrank_ker
  rw [he] at hh
  have h₁:Module.finrank k f'.range ≤ Module.finrank k (N ⧸ E):=Submodule.finrank_le _
  have h₂:=g'.finrank_range_le
  omega
end z6t
namespace zbb
open scoped Classical BigOperators
variable {A:Type*} [Ring A]
lemma zcz (I:Ideal A) [I.IsTwoSided] (ι:Type*) [Fintype ι] :
    I • (⊤:Submodule A (ι → A)) = Submodule.pi Set.univ (fun _:ι => I):=by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro r hr v _
    apply Submodule.mem_pi.mpr
    intro i _
    exact I.mul_mem_right (v i) hr
  · intro v hv
    rw [pi_eq_sum_univ v]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem_smul ((Submodule.mem_pi.mp hv) i trivial) Submodule.mem_top
variable (k:Type*) [Field k] [Algebra k A] [FiniteDimensional k A]
lemma zd2 (I:Ideal A) [I.IsTwoSided] (d:ℕ) :
    Module.finrank k ((Fin d → A) ⧸ (I • (⊤:Submodule A (Fin d → A))).restrictScalars k) =
      d*Module.finrank k (A ⧸ I.restrictScalars k):=by
  rw [zcz]
  change Module.finrank k ((Fin d → A) ⧸ Submodule.pi Set.univ (fun _:Fin d => I.restrictScalars k)) = _
  rw [(Submodule.quotientPi (fun _:Fin d => I.restrictScalars k)).finrank_eq]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
lemma zf2 (I:Ideal A) [I.IsTwoSided] (d r:ℕ)
    (f:(Fin d → A) →ₗ[A] A) (g:(Fin r → A) →ₗ[A] (Fin d → A))
    (hI:f.range = I) (hex:f.ker = g.range)
    (hmin:f.ker ≤ I • (⊤:Submodule A (Fin d → A))) (n:ℕ) :
    d*Module.finrank k (A ⧸ (I^(n+1)).restrictScalars k) ≤
      Module.finrank k (A ⧸ (I^(n+2)).restrictScalars k)+
        r*Module.finrank k (A ⧸ (I^n).restrictScalars k):=by
  let D:=(I^(n+1) • (⊤:Submodule A (Fin d → A))).restrictScalars k
  let E:=(I^(n+2)).restrictScalars k
  let F:=(I^n • (⊤:Submodule A (Fin r → A))).restrictScalars k
  have hf:D.map (f.restrictScalars k) = E:=by
    dsimp only [D,E]
    rw [← Submodule.restrictScalars_map,Submodule.map_smul'',Submodule.map_top,hI,Ideal.smul_eq_mul]
    congr 1
  have hg:F ≤ D.comap (g.restrictScalars k):=by
    apply Submodule.map_le_iff_le_comap.mp
    dsimp only [D,F]
    rw [← Submodule.restrictScalars_map,Submodule.map_smul'',Submodule.map_top,← hex]
    apply Submodule.restrictScalars_mono k
    calc
      I^n • f.ker ≤ I^n • (I • (⊤:Submodule A (Fin d → A))):=Submodule.smul_mono le_rfl hmin
      _ = I^(n+1) • (⊤:Submodule A (Fin d → A)):=by rw [← Submodule.mul_smul,← Submodule.pow_succ]
  have hhex:(f.restrictScalars k).ker = (g.restrictScalars k).range:=by
    rw [LinearMap.ker_restrictScalars,LinearMap.range_restrictScalars,hex]
  have hh:=z6t.zey (f.restrictScalars k) (g.restrictScalars k)
    hhex D E F hf hg
  simpa only [D,E,F,zd2] using hh
end zbb
namespace z2q
open scoped Classical BigOperators
variable (G:Type*) [Group G] (p:ℕ) [Fact p.Prime]
variable (M:Type*) [AddCommGroup M] [Module (ZMod p) M]
  [Module (MonoidAlgebra (ZMod p) G) M]
  [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
  [FiniteDimensional (ZMod p) M]
noncomputable def z16:Submodule (MonoidAlgebra (ZMod p) G) M :=
  zv.ideal (ZMod p) G • ⊤
noncomputable instance:Module.Finite (ZMod p) (M ⧸ z16 G p M) :=
  Module.Finite.of_surjective ((z16 G p M).mkQ.restrictScalars (ZMod p))
    (z16 G p M).mkQ_surjective
noncomputable def z3w:ℕ:=Module.finrank (ZMod p) (M ⧸ z16 G p M)
omit [FiniteDimensional (ZMod p) M] in
lemma z9q (a:MonoidAlgebra (ZMod p) G) (v:M) :
    (z16 G p M).mkQ (a • v) =
      zv.augmentation (ZMod p) G a • (z16 G p M).mkQ v:=by
  let ε:=zv.augmentation (ZMod p) G
  let N:=z16 G p M
  have ha:a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a) ∈ zv.ideal (ZMod p) G:=by
    rw [zv.z5v,map_sub,AlgHom.commutes]; simp only [Algebra.algebraMap_self,RingHom.id_apply,ε,sub_self]
  have hv:(a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a)) • v ∈ N :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  have hq:N.mkQ ((a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a)) • v) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr hv
  rw [sub_smul,map_sub,algebraMap_smul] at hq
  have hs:N.mkQ (ε a • v) = ε a • N.mkQ v:=(N.mkQ.restrictScalars (ZMod p)).map_smul _ _
  rw [hs,sub_eq_zero] at hq
  exact hq
lemma z43 (hG:IsPGroup p G) :
    ∃ f:(Fin (z3w G p M) → MonoidAlgebra (ZMod p) G) →ₗ[MonoidAlgebra (ZMod p) G] M,
      Function.Surjective f ∧
      f.ker ≤ zv.ideal (ZMod p) G •
        (⊤:Submodule (MonoidAlgebra (ZMod p) G) (Fin (z3w G p M) → MonoidAlgebra (ZMod p) G)):=by
  let A:=MonoidAlgebra (ZMod p) G
  let ε:=zv.augmentation (ZMod p) G
  let N:=z16 G p M
  let B:=Module.finBasis (ZMod p) (M ⧸ N)
  have hlift:∀ i:Fin (z3w G p M), ∃ x:M, N.mkQ x = B i :=
    fun i => N.mkQ_surjective (B i)
  choose lift hlift using hlift
  let f:(Fin (z3w G p M) → A) →ₗ[A] M:=Fintype.linearCombination A lift
  have hq (c:Fin (z3w G p M) → A) :
      N.mkQ (f c) = ∑ i, ε (c i) • B i:=by
    rw [Fintype.linearCombination_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [z9q,hlift]
  have hsurj:Function.Surjective (N.mkQ.comp f):=by
    intro v
    refine ⟨fun i => algebraMap (ZMod p) A (B.repr v i),?_⟩
    change N.mkQ (f _) = v
    rw [hq]
    simp only [A,ε,AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply]
    exact B.sum_repr v
  have ht:f.range = ⊤:=by
    apply zv.zaj G p hG
    rw [sup_comm]
    apply (Submodule.map_mkQ_eq_top N f.range).mp
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr hsurj
  refine ⟨f,LinearMap.range_eq_top.mp ht,?_⟩
  rw [zbb.zcz]
  intro c hc
  have hz:∑ i, ε (c i) • B i = 0:=by
    rw [← hq,LinearMap.mem_ker.mp hc,map_zero]
  have hzero:=Fintype.linearIndependent_iff.mp B.linearIndependent _ hz
  apply Submodule.mem_pi.mpr
  intro i _
  exact (zv.z5v _ _ _).mpr (hzero i)
end z2q
namespace z5g
lemma zea (d r:ℕ) (hr:4*r ≤ d^2)
    (a:ℕ → ℕ) (ha1:d*a 0 ≤ 2*a 1)
    (hrec:∀ n, d*a (n+1) ≤ a (n+2)+r*a n):∀ n, d*a n ≤ 2*a (n+1):=by
  intro n
  induction n with
  | zero => exact ha1
  | succ n ih =>
    have h₁:=Nat.mul_le_mul_left d ih
    have h₂:=Nat.mul_le_mul_right (a n) hr
    have h₃:=Nat.mul_le_mul_left (2*d) (hrec n)
    have hn:=hrec n
    have ht:2*r*a n ≤ d*a (n+1):=by nlinarith
    nlinarith
lemma zbj (d r:ℕ) (hd:3 ≤ d) (hr:4*r ≤ d^2)
    (a:ℕ → ℕ) (ha0:0 < a 0) (ha1:d*a 0 ≤ 2*a 1)
    (hrec:∀ n, d*a (n+1) ≤ a (n+2)+r*a n):∀ n, n < a n:=by
  have hg:=zea d r hr a ha1 hrec
  intro n
  induction n with
  | zero => exact ha0
  | succ n ih =>
    have hh:=hg n
    have hm:=Nat.mul_le_mul_right (a n) hd
    omega
end z5g
namespace zk2
open scoped Classical
lemma z3m {A:Type*} [Ring A] (k:Type*) [Field k] [Algebra k A]
    [FiniteDimensional k A] (I:Ideal A) [I.IsTwoSided] (hIproper:I ≠ ⊤)
    (d r:ℕ) (hd:3 ≤ d)
    (f:(Fin d → A) →ₗ[A] A) (g:(Fin r → A) →ₗ[A] (Fin d → A))
    (hI:f.range = I) (hex:f.ker = g.range)
    (hmin:f.ker ≤ I • (⊤:Submodule A (Fin d → A))):d^2 < 4*r:=by
  let a:=fun n:ℕ => Module.finrank k (A ⧸ (I^(n+1)).restrictScalars k)
  have hc (n:ℕ):=zbb.zf2 k I d r f g hI hex hmin n
  have ha0:0 < a 0:=by
    have hp:I.restrictScalars k ≠ ⊤:=by
      intro h
      apply hIproper
      apply top_unique
      intro x _
      change x ∈ I.restrictScalars k
      rw [h]
      trivial
    letI:Nontrivial (A ⧸ I.restrictScalars k):=Submodule.Quotient.nontrivial_iff.mpr hp
    change 0 < Module.finrank k (A ⧸ (I^1).restrictScalars k)
    rw [Submodule.pow_one]
    exact Module.finrank_pos
  have ha1:d*a 0 ≤ 2*a 1:=by
    have hh:=hc 0
    have hz:Module.finrank k (A ⧸ (I^0).restrictScalars k) = 0:=by
      have he:I^0 = ⊤:=by rw [Submodule.pow_zero]; exact Ideal.one_eq_top
      rw [he,Submodule.restrictScalars_top]
      exact Module.finrank_zero_of_subsingleton
    rw [hz,mul_zero,add_zero] at hh
    change d*a 0 ≤ a 1 at hh
    omega
  have hrec:∀ n, d*a (n+1) ≤ a (n+2)+r*a n:=by
    intro n
    exact hc (n+1)
  by_contra h
  have hg:=z5g.zbj d r hd (Nat.le_of_not_gt h) a ha0 ha1 hrec
  have hh:=hg (Module.finrank k A)
  have hb:=((I^(Module.finrank k A+1)).restrictScalars k).finrank_quotient_le
  exact (not_lt_of_ge hb) hh
end zk2
namespace zda
open scoped Classical
variable (G:Type*) [Group G] [Finite G] (p:ℕ) [Fact p.Prime]
lemma z3m (hG:IsPGroup p G) (d:ℕ) (hd:3 ≤ d)
    (f:(Fin d → MonoidAlgebra (ZMod p) G) →ₗ[MonoidAlgebra (ZMod p) G]
      zv.ideal (ZMod p) G)
    (hf:Function.Surjective f)
    (hmin:f.ker ≤ zv.ideal (ZMod p) G •
      (⊤:Submodule (MonoidAlgebra (ZMod p) G) (Fin d → MonoidAlgebra (ZMod p) G))) :
    d^2 < 4*z2q.z3w G p f.ker:=by
  let A:=MonoidAlgebra (ZMod p) G
  let I:=zv.ideal (ZMod p) G
  let f':(Fin d → A) →ₗ[A] A:=I.subtype.comp f
  have hker:f'.ker = f.ker:=by
    ext v
    change ((f v:I):A) = 0 ↔ f v = 0
    exact Submodule.coe_eq_zero
  have hf':f'.range = I:=by
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hf,Submodule.map_top,Submodule.range_subtype]
  letI:FiniteDimensional (ZMod p) f.ker:=inferInstanceAs
    (FiniteDimensional (ZMod p) (f.ker.restrictScalars (ZMod p)))
  obtain ⟨g,hg,_⟩:=z2q.z43 G p f.ker hG
  let g':=f.ker.subtype.comp g
  have hg':g'.range = f'.ker:=by
    rw [hker,LinearMap.range_comp,LinearMap.range_eq_top.mpr hg,Submodule.map_top,Submodule.range_subtype]
  exact zk2.z3m (ZMod p) I (zv.zkz _ _) d
    (z2q.z3w G p f.ker) hd f' g' hf' hg'.symm (hker ▸ hmin)
end zda
noncomputable section
namespace z1s
open CategoryTheory
universe u
variable (k G:Type u) [Field k] [Group G]
variable (M:Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]
abbrev of:Rep k G:=Rep.of (Representation.ofModule' M)
def asModuleEquiv:(of k G M).ρ.asModule ≃ₗ[MonoidAlgebra k G] M :=
  { (of k G M).ρ.asModuleEquiv.toAddEquiv with
    map_smul':=fun a x => by
      change (of k G M).ρ.asModuleEquiv (a • x) = a • (of k G M).ρ.asModuleEquiv x
      rw [Representation.asModuleEquiv_map_smul]
      change (Representation.ofModule' M).asAlgebraHom a _ = _
      simp [Representation.ofModule',Representation.asAlgebraHom] }
instance [Module.Free (MonoidAlgebra k G) M]:Projective (of k G M):=by
  apply Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective
  exact ModuleCat.projective_of_free
    ((Module.Free.chooseBasis (MonoidAlgebra k G) M).map (asModuleEquiv k G M).symm)
variable {M}
variable {N:Type u} [AddCommGroup N] [Module k N] [Module (MonoidAlgebra k G) N]
  [IsScalarTower k (MonoidAlgebra k G) N]
def map (f:M →ₗ[MonoidAlgebra k G] N):of k G M ⟶ of k G N :=
  Rep.ofHom ⟨f.restrictScalars k, fun g => by
    ext x
    exact f.map_smul (MonoidAlgebra.of k G g) x⟩
end z1s
namespace z1s
open CategoryTheory
universe u
variable (k G:Type u) [Field k] [Group G]
variable (M:Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]
noncomputable def z16:Submodule (MonoidAlgebra k G) M :=
  zv.ideal k G • ⊤
lemma zai (f:of k G M ⟶ Rep.trivial k G k)
    {v:M} (hv:v ∈ z16 k G M):f.hom v = 0:=by
  have hf:∀ g:G, ∀ v:M, f.hom (MonoidAlgebra.of k G g • v) = f.hom v :=
    fun g v => Rep.hom_comm_apply f g v
  exact Submodule.smul_induction_on hv (fun a ha v _ => by
    change f.hom.toLinearMap (a • v) = 0
    rw [zv.map_smul k G f.hom.toLinearMap hf,
      (zv.z5v _ _ _).mp ha,zero_mul])
    (fun x y hx hy => by rw [map_add,hx,hy,add_zero])
lemma z9q (a:MonoidAlgebra k G) (v:M) :
    (z16 k G M).mkQ (a • v) =
      zv.augmentation k G a • (z16 k G M).mkQ v:=by
  let ε:=zv.augmentation k G
  let N:=z16 k G M
  have ha:a-algebraMap k (MonoidAlgebra k G) (ε a) ∈ zv.ideal k G:=by
    rw [zv.z5v,map_sub,AlgHom.commutes]
    simp only [Algebra.algebraMap_self,RingHom.id_apply,ε,sub_self]
  have hv:(a-algebraMap k (MonoidAlgebra k G) (ε a)) • v ∈ N :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  have hq:N.mkQ ((a-algebraMap k (MonoidAlgebra k G) (ε a)) • v) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr hv
  rw [sub_smul,map_sub,algebraMap_smul] at hq
  have hs:N.mkQ (ε a • v) = ε a • N.mkQ v:=(N.mkQ.restrictScalars k).map_smul _ _
  rw [hs,sub_eq_zero] at hq
  exact hq
noncomputable def zgv (f:of k G M ⟶ Rep.trivial k G k) :
    Module.Dual k (M ⧸ z16 k G M) :=
  (z16 k G M).restrictScalars k |>.liftQ f.hom.toLinearMap
    (fun _ hv => zai k G M f hv)
noncomputable def zew (f:Module.Dual k (M ⧸ z16 k G M)) :
    of k G M ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨f.comp ((z16 k G M).mkQ.restrictScalars k), fun g => by
    ext v
    change f ((z16 k G M).mkQ (MonoidAlgebra.of k G g • v)) =
      f ((z16 k G M).mkQ v)
    rw [z9q,zv.augmentation_of,one_smul]⟩
noncomputable def zfm :
    (of k G M ⟶ Rep.trivial k G k) ≃ₗ[k] Module.Dual k (M ⧸ z16 k G M) where
  toFun:=zgv k G M
  invFun:=zew k G M
  left_inv f:=by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl
  right_inv f:=by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩:=(z16 k G M).mkQ_surjective v
    rfl
  map_add' f g:=by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩:=(z16 k G M).mkQ_surjective v
    rfl
  map_smul' r f:=by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩:=(z16 k G M).mkQ_surjective v
    rfl
lemma zjo :
    Module.finrank k (of k G M ⟶ Rep.trivial k G k) =
      Module.finrank k (M ⧸ z16 k G M):=by
  rw [(zfm k G M).finrank_eq,Subspace.dual_finrank_eq]
lemma zbc (d:ℕ) :
    Module.finrank k ((Fin d → MonoidAlgebra k G) ⧸ z16 k G (Fin d → MonoidAlgebra k G)) = d:=by
  classical
  let A:=MonoidAlgebra k G
  let I:=zv.ideal k G
  let ε:=(zv.augmentation k G).toLinearMap
  have hsurj:Function.Surjective ε:=by
    intro x
    exact ⟨MonoidAlgebra.single 1 x,zv.z5l k G 1 x⟩
  letI:FiniteDimensional k (A ⧸ I.restrictScalars k) :=
    (ε.quotKerEquivOfSurjective hsurj).symm.finiteDimensional
  have hq:Module.finrank k (A ⧸ I.restrictScalars k) = 1:=by
    change Module.finrank k (A ⧸ ε.ker) = 1
    rw [(ε.quotKerEquivOfSurjective hsurj).finrank_eq,Module.finrank_self]
  have he:z16 k G (Fin d → A) = Submodule.pi Set.univ (fun _:Fin d => I):=by
    apply le_antisymm
    · apply Submodule.smul_le.mpr
      intro r hr v _
      apply Submodule.mem_pi.mpr
      intro i _
      exact I.mul_mem_right (v i) hr
    · intro v hv
      rw [pi_eq_sum_univ v]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem_smul ((Submodule.mem_pi.mp hv) i trivial) Submodule.mem_top
  rw [he]
  change Module.finrank k ((Fin d → A) ⧸ Submodule.pi Set.univ (fun _:Fin d => I.restrictScalars k)) = d
  rw [(Submodule.quotientPi (fun _:Fin d => I.restrictScalars k)).finrank_eq]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change d*Module.finrank k (A ⧸ I.restrictScalars k) = d
  rw [hq,mul_one]
lemma zb1 (d:ℕ) :
    Module.finrank k (of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) = d:=by
  rw [zjo,zbc]
end z1s
noncomputable section
namespace z3o
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable {C:Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {X₀ X₁ X₂ Z:C} (d₀:X₁ ⟶ X₀) (d₁:X₂ ⟶ X₁) (h:CategoryStruct.comp d₁ d₀ = 0)
lemma d_comp_self {X Y:C} (f:X ⟶ Y):CategoryStruct.comp (Projective.d f) f = 0:=by
  unfold Projective.d Projective.syzygies
  simp
def complex:ChainComplex C ℕ :=
  ChainComplex.mk X₀ X₁ X₂ d₀ d₁ h (fun S => ⟨_, Projective.d S.f, d_comp_self S.f⟩)
@[simp] lemma z9i:(complex d₀ d₁ h).d 1 0 = d₀:=by
  simp [complex]
@[simp] lemma zk4:(complex d₀ d₁ h).d 3 2 = Projective.d d₁:=by
  change CategoryStruct.comp (𝟙 _) (Projective.d d₁) = _
  simp
@[simp] lemma zkc:(complex d₀ d₁ h).d 2 1 = d₁:=by
  simp [complex]
lemma id_comp_eq {X Y:C} {f g:X ⟶ Y} (e:f = g) :
    CategoryStruct.comp (𝟙 X) g = CategoryStruct.comp f (𝟙 Y):=by
  rw [e, Category.id_comp, Category.comp_id]
lemma zlu (hex:(ShortComplex.mk d₁ d₀ h).Exact) (n:ℕ) :
    (complex d₀ d₁ h).ExactAt (n+1):=by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  match n with
  | 0 =>
    refine (ShortComplex.exact_iff_of_iso ?_).2 hex
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (id_comp_eq (zkc d₀ d₁ h)) (id_comp_eq (z9i d₀ d₁ h))
  | n+1 =>
    refine (ShortComplex.exact_iff_of_iso ?_).2
      (CategoryTheory.exact_d_f ((complex d₀ d₁ h).d (n+2) (n+1)))
    refine ShortComplex.isoMk (ChainComplex.mkXIso X₀ X₁ X₂ d₀ d₁ h
      (fun S => ⟨_, Projective.d S.f, d_comp_self S.f⟩) n) (Iso.refl _) (Iso.refl _) ?_ ?_
    · refine Eq.trans ?_ (Category.comp_id _).symm
      exact (ChainComplex.mk_d _ _ _ _ _ _ _ n).symm
    · exact id_comp_eq rfl
instance [Projective X₀] [Projective X₁] [Projective X₂] (n:ℕ) :
    Projective ((complex d₀ d₁ h).X n):=by
  obtain (_|_|_|n):=n
  · exact ‹Projective X₀›
  · exact ‹Projective X₁›
  · exact ‹Projective X₂›
  · apply Projective.projective_over
variable [Projective X₀] [Projective X₁] [Projective X₂]
def resolution (π:X₀ ⟶ Z) (hπ:CategoryStruct.comp d₀ π = 0) [Epi π]
    (hex₀:(ShortComplex.mk d₀ π hπ).Exact)
    (hex₁:(ShortComplex.mk d₁ d₀ h).Exact):ProjectiveResolution Z where
  complex:=complex d₀ d₁ h
  π:=(ChainComplex.toSingle₀Equiv _ _).symm ⟨π,by simp only [z9i]; exact hπ⟩
  quasiIso:=⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hex₀,inferInstance⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · exact id_comp_eq (z9i d₀ d₁ h)
        · exact id_comp_eq (ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact zlu d₀ d₁ h hex₁ n
      · apply ChainComplex.exactAt_succ_single_obj⟩
end z3o
noncomputable section
open CategoryTheory
namespace z9t
variable {C:Type*} [Category C] [Abelian C]
def iso (K:CochainComplex C ℕ) (n:ℕ)
    (hleft:K.d n (n+1) = 0) (hright:K.d (n+1) (n+2) = 0) :
    K.homology (n+1) ≅ K.X (n+1) :=
  K.homologyIsoSc' n (n+1) (n+2) (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (K.sc' n (n+1) (n+2)) hleft hright).homologyIso
end z9t
namespace z5u
open CategoryTheory
variable (k G:Type) [Field k] [Group G]
noncomputable def augmentation:z1s.of k G (MonoidAlgebra k G) ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨(zv.augmentation k G).toLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    change zv.augmentation k G ((MonoidAlgebra.of k G g)*x) =
      zv.augmentation k G x
    rw [map_mul,zv.augmentation_of,one_mul]⟩
instance:Epi (augmentation k G):=by
  rw [Rep.epi_iff_surjective]
  intro x
  exact ⟨MonoidAlgebra.single 1 x,zv.z5l k G 1 x⟩
variable {k G} {d r:ℕ}
variable (f:(Fin d → (MonoidAlgebra k G)) →ₗ[(MonoidAlgebra k G)] (zv.ideal k G))
variable (g:(Fin r → (MonoidAlgebra k G)) →ₗ[(MonoidAlgebra k G)] f.ker)
noncomputable def d₀:z1s.of k G (Fin d → (MonoidAlgebra k G)) ⟶ z1s.of k G (MonoidAlgebra k G) :=
  z1s.map k G (((zv.ideal k G)).subtype.comp f)
noncomputable def d₁:z1s.of k G (Fin r → (MonoidAlgebra k G)) ⟶ z1s.of k G (Fin d → (MonoidAlgebra k G)) :=
  z1s.map k G (f.ker.subtype.comp g)
lemma z7s:CategoryStruct.comp (d₀ f) (augmentation k G) = 0:=by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (zv.z5v k G _).mp (f x).property
lemma zeb:CategoryStruct.comp (d₁ f g) (d₀ f) = 0:=by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (f (g x):(MonoidAlgebra k G)) = 0
  rw [LinearMap.mem_ker.mp (g x).property]
  rfl
lemma exact₀ (hf:Function.Surjective f) :
    (ShortComplex.mk (d₀ f) (augmentation k G) (z7s f)).Exact:=by
  apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change zv.augmentation k G x = 0 at hx
  obtain ⟨v,hv⟩:=hf ⟨x,(zv.z5v k G x).mpr hx⟩
  exact ⟨v,congrArg Subtype.val hv⟩
lemma exact₁ (hg:Function.Surjective g) :
    (ShortComplex.mk (d₁ f g) (d₀ f) (zeb f g)).Exact:=by
  apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hfx:f x = 0:=Subtype.ext hx
  obtain ⟨v,hv⟩:=hg ⟨x,LinearMap.mem_ker.mpr hfx⟩
  exact ⟨v,congrArg Subtype.val hv⟩
noncomputable def resolution (hf:Function.Surjective f) (hg:Function.Surjective g) :
    ProjectiveResolution (Rep.trivial k G k) :=
  z3o.resolution (d₀ f) (d₁ f g) (zeb f g)
    (augmentation k G) (z7s f) (exact₀ f hf) (exact₁ f g hg)
end z5u
namespace z5u
open CategoryTheory
variable {k G:Type} [Field k] [Group G] {d r:ℕ}
variable (f:(Fin d → MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] zv.ideal k G)
variable (g:(Fin r → MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] f.ker)
variable (hf:Function.Surjective f) (hg:Function.Surjective g)
variable (hminf:f.ker ≤ z1s.z16 k G (Fin d → MonoidAlgebra k G))
variable (hming:g.ker ≤ z1s.z16 k G (Fin r → MonoidAlgebra k G))
lemma zl0 (φ:z1s.of k G (MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    CategoryStruct.comp (d₀ f) φ = 0:=by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change φ.hom (f x:MonoidAlgebra k G) = 0
  apply z1s.zai
  have h:(f x:MonoidAlgebra k G) • (1:MonoidAlgebra k G) ∈
      z1s.z16 k G (MonoidAlgebra k G):=Submodule.smul_mem_smul (f x).property
    (Submodule.mem_top:(1:MonoidAlgebra k G) ∈ (⊤:Submodule (MonoidAlgebra k G) (MonoidAlgebra k G)))
  simpa only [smul_eq_mul,mul_one] using h
include hminf in
lemma zle (φ:z1s.of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    CategoryStruct.comp (d₁ f g) φ = 0:=by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change φ.hom (g x:Fin d → MonoidAlgebra k G) = 0
  exact z1s.zai k G _ φ (hminf (g x).property)
include hming in
lemma zl2 (φ:z1s.of k G (Fin r → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    CategoryStruct.comp (Projective.d (d₁ f g)) φ = 0:=by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change φ.hom ((Projective.d (d₁ f g)).hom x) = 0
  apply z1s.zai k G _ φ
  apply hming
  apply LinearMap.mem_ker.mpr
  have he:CategoryStruct.comp (Projective.d (d₁ f g)) (d₁ f g) = 0:=z3o.d_comp_self _
  have hx:=congrArg (fun h => h.hom x) he
  apply Subtype.ext
  exact hx
lemma zj5 :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 0 1 = 0:=by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change CategoryStruct.comp (d₀ f) φ = 0
  exact zl0 f φ
include hminf in
lemma zbz :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 1 2 = 0:=by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change CategoryStruct.comp (d₁ f g) φ = 0
  exact zle f g hminf φ
include hming in
lemma ziv :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 2 3 = 0:=by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change CategoryStruct.comp ((z3o.complex (d₀ f) (d₁ f g) (zeb f g)).d 3 2) φ = 0
  rw [z3o.zk4]
  exact zl2 f g hming φ
noncomputable def H1Iso :
    groupCohomology (Rep.trivial k G k) 1 ≅
      ModuleCat.of k (z1s.of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :=
  groupCohomologyIso _ 1 (resolution f g hf hg) ≪≫
    z9t.iso _ 0 (zj5 f g hf hg) (zbz f g hf hg hminf)
noncomputable def H2Iso :
    groupCohomology (Rep.trivial k G k) 2 ≅
      ModuleCat.of k (z1s.of k G (Fin r → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :=
  groupCohomologyIso _ 2 (resolution f g hf hg) ≪≫
    z9t.iso _ 1 (zbz f g hf hg hminf) (ziv f g hf hg hming)
include hf hg hminf in
lemma zn4:Module.finrank k (groupCohomology (Rep.trivial k G k) 1) = d:=by
  rw [(H1Iso f g hf hg hminf).toLinearEquiv.finrank_eq]
  exact z1s.zb1 k G d
include hf hg hminf hming in
lemma zmu:Module.finrank k (groupCohomology (Rep.trivial k G k) 2) = r:=by
  rw [(H2Iso f g hf hg hminf hming).toLinearEquiv.finrank_eq]
  exact z1s.zb1 k G r
end z5u
namespace zg6
open CategoryTheory
open scoped Classical
variable (G:Type) [Group G] [Finite G] (p:ℕ) [Fact p.Prime]
lemma z3m (hG:IsPGroup p G)
    (hd:3 ≤ Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1)) :
    (Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1))^2 <
      4*Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2):=by
  obtain ⟨f,hf,hminf⟩:=z2q.z43 G p
    (zv.ideal (ZMod p) G) hG
  letI:FiniteDimensional (ZMod p) f.ker:=inferInstanceAs
    (FiniteDimensional (ZMod p) (f.ker.restrictScalars (ZMod p)))
  obtain ⟨g,hg,hming⟩:=z2q.z43 G p f.ker hG
  have he₁:=z5u.zn4 f g hf hg hminf
  have he₂:=z5u.zmu f g hf hg hminf hming
  rw [he₁,he₂]
  rw [he₁] at hd
  exact zda.z3m G p hG _ hd f hf hminf
end zg6
namespace z21
open NumberField
open scoped Classical
structure Layer (B:Type) [Field B] [NumberField B] (d:ℕ) where
  carrier:Type
  field:Field carrier
  numberField:NumberField carrier
  real:IsTotallyReal carrier
  algebra:Algebra B carrier
  galois:IsGalois B carrier
  zcw:IsPGroup 2 Gal(carrier/B)
  unramified:differentIdeal (𝓞 B) (𝓞 carrier) = ⊤
  z30:d ≤ Module.finrank (ZMod 2)
    (groupCohomology (Rep.trivial (ZMod 2) Gal(carrier/B) (ZMod 2)) 1)
instance instOMAField1:type_of% @Layer.field:=@Layer.field
instance instOMAField2:type_of% @Layer.numberField:=@Layer.numberField
instance instOMAField3:type_of% @Layer.real:=@Layer.real
instance instOMAField4:type_of% @Layer.algebra:=@Layer.algebra
instance instOMAField5:type_of% @Layer.galois:=@Layer.galois
variable {B:Type} [Field B] [NumberField B] {d:ℕ}
def z4m (M:Layer B d):Prop :=
  ∀ N:Layer B d, Module.finrank B N.carrier ≤ Module.finrank B M.carrier
def z3v (B:Type) [Field B] [NumberField B] (d R:ℕ):Prop :=
  ∀ M:Layer B d, z4m M →
    Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(M.carrier/B) (ZMod 2)) 2) ≤ R
lemma zgl {R:ℕ} (hd:3 ≤ d) (hnum:4*R ≤ d^2)
    (hrel:z3v B d R) (M:Layer B d):¬ z4m M:=by
  intro hmax
  letI:Fact (Nat.Prime 2):=⟨by norm_num⟩
  have hgs:=zg6.z3m Gal(M.carrier/B) 2 M.zcw
    (hd.trans M.z30)
  have hr:=hrel M hmax
  have hM:=M.z30
  nlinarith
lemma zdo (h₀:Nonempty (Layer B d))
    (hbound:∃ n:ℕ, ∀ M:Layer B d, Module.finrank B M.carrier ≤ n) :
    ∃ M:Layer B d, z4m M:=by
  let s:Set ℕ:={n | ∃ M:Layer B d, Module.finrank B M.carrier = n}
  have hs:s.Nonempty:=by
    obtain ⟨M⟩:=h₀
    exact ⟨_, M, rfl⟩
  have hb:BddAbove s:=by
    obtain ⟨n,hn⟩:=hbound
    exact ⟨n, fun m ⟨M,hM⟩ => hM ▸ hn M⟩
  obtain ⟨M,hM⟩:=Nat.sSup_mem hs hb
  refine ⟨M, fun N => ?_⟩
  rw [hM]
  exact le_csSup hb (show Module.finrank B N.carrier ∈ s from ⟨N,rfl⟩)
lemma zc9 (h₀:Nonempty (Layer B d))
    {R:ℕ} (hd:3 ≤ d) (hnum:4*R ≤ d^2) (hrel:z3v B d R) (n:ℕ) :
    ∃ M:Layer B d, n ≤ Module.finrank B M.carrier:=by
  by_contra hn
  push_neg at hn
  obtain ⟨M,hM⟩:=zdo h₀ ⟨n, fun N => (hn N).le⟩
  exact zgl hd hnum hrel M hM
lemma zkb (h₀:Nonempty (Layer B d)) {R:ℕ} (hd:3 ≤ d) (hnum:4*R ≤ d^2) (hrel:z3v B d R) :
    ∃ M:ℕ → Layer B d, ∀ n, 2^n ≤ Module.finrank B (M n).carrier:=by
  exact Classical.skolem.mp (fun n => zc9 h₀ hd hnum hrel (2^n))
end z21
namespace z69
open NumberField IntermediateField
open scoped Classical
variable {K L M:Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M] [Algebra K L] [Algebra K M]
lemma zje (hL:differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hgen:normalClosure K L M = ⊤) (P:Ideal (𝓞 M)) (hP:P ≠ ⊤) :
    P.toAddSubgroup.inertia Gal(M/K) = ⊥:=by
  apply eq_bot_iff.mpr
  intro σ hσ
  change σ = 1
  let F:IntermediateField K M:={
    toSubalgebra:=AlgHom.equalizer σ.toAlgHom (AlgHom.id K M)
    inv_mem':=fun x hx => by
      change σ x⁻¹ = x⁻¹
      change σ x = x at hx
      rw [map_inv₀,hx] }
  have hF:normalClosure K L M ≤ F:=by
    apply normalClosure_le_iff.mpr
    intro f y hy
    obtain ⟨x,rfl⟩:=hy
    exact z5s.zky hL P hP σ hσ f x
  rw [hgen] at hF
  apply AlgEquiv.ext
  intro x
  exact hF (show x ∈ (⊤:IntermediateField K M) from trivial)
lemma z4e [IsGalois K M]
    (hL:differentIdeal (𝓞 K) (𝓞 L) = ⊤) (hgen:normalClosure K L M = ⊤) :
    differentIdeal (𝓞 K) (𝓞 M) = ⊤:=by
  by_contra hn
  obtain ⟨P,hP,hle⟩:=Ideal.exists_le_maximal (differentIdeal (𝓞 K) (𝓞 M)) hn
  letI:P.IsMaximal:=hP
  have hP0:P ≠ ⊥:=Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField M)
  let p:=P.under (𝓞 K)
  have hp0:p ≠ ⊥:=fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  letI:p.IsMaximal:=(inferInstance:p.IsPrime).isMaximal hp0
  letI:Field ((𝓞 K) ⧸ p):=Ideal.Quotient.field p
  letI:Field ((𝓞 M) ⧸ P):=Ideal.Quotient.field P
  letI:Finite ((𝓞 K) ⧸ p):=Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI:Finite ((𝓞 M) ⧸ P):=Ideal.finiteQuotientOfFreeOfNeBot P hP0
  have hc:=Ideal.card_inertia_eq_ramificationIdxIn (G:=Gal(M/K)) p P
  rw [Ideal.inertia, zje hL hgen P hP.ne_top] at hc
  have he:P.ramificationIdx (𝓞 K) = 1:=by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(M/K),← hc]
    simp
  have hu:Algebra.IsUnramifiedAt (𝓞 K) P :=
    Ideal.ramificationIdx_eq_one_iff.mp he
  exact (not_dvd_differentIdeal_iff.mpr hu) (Ideal.dvd_iff_le.mpr hle)
end z69
namespace zag
open NumberField IntermediateField
variable {K L M:Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M] [Algebra K L] [Algebra K M]
lemma zan [IsTotallyReal L] (hgen:normalClosure K L M = ⊤):IsTotallyReal M:=by
  letI:IsTotallyReal K:=IsTotallyReal.of_algebra K L
  let F:IntermediateField K M:={
    carrier:={x | ∀ σ:M →+* ℂ, star (σ x) = σ x}
    add_mem':=fun hx hy σ => by rw [map_add,star_add,hx,hy]
    mul_mem':=fun hx hy σ => by rw [map_mul,star_mul,hx,hy,mul_comm]
    zero_mem':=fun σ => by simp
    one_mem':=fun σ => by simp
    algebraMap_mem':=fun x σ =>
      RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (σ.comp (algebraMap K M))) x
    inv_mem':=fun x hx σ => by rw [map_inv₀,star_inv₀,hx] }
  have hF:normalClosure K L M ≤ F:=by
    apply normalClosure_le_iff.mpr
    intro f y hy
    obtain ⟨x,rfl⟩:=hy
    intro σ
    exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (σ.comp f.toRingHom)) x
  rw [hgen] at hF
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hF (show x ∈ (⊤:IntermediateField K M) from trivial) w.embedding
end zag
namespace zar
open IntermediateField
variable {K L M T:Type*} [Field K] [Field L] [Field M] [Field T]
  [Algebra K L] [Algebra K M] [Algebra K T]
lemma hom_ext (hgen:normalClosure K L M = ⊤) {f g:M →ₐ[K] T}
    (h:∀ φ:L →ₐ[K] M, f.comp φ = g.comp φ):f = g:=by
  let F:IntermediateField K M:={
    toSubalgebra:=AlgHom.equalizer f g
    inv_mem':=fun x hx => by
      change f x⁻¹ = g x⁻¹
      change f x = g x at hx
      rw [map_inv₀,map_inv₀,hx] }
  have hF:normalClosure K L M ≤ F:=by
    apply normalClosure_le_iff.mpr
    intro φ y hy
    obtain ⟨x,rfl⟩:=hy
    exact AlgHom.congr_fun (h φ) x
  rw [hgen] at hF
  apply AlgHom.ext
  intro x
  exact hF (show x ∈ (⊤:IntermediateField K M) from trivial)
end zar
namespace z78
open IntermediateField
variable {B K L M:Type*} [Field B] [Field K] [Field L] [Field M]
  [Algebra B K] [Algebra B L] [Algebra B M] [Algebra K L] [Algebra K M]
  [IsScalarTower B K L] [IsScalarTower B K M] [Normal B K]
lemma zn7 (σ:Gal(M/B)) (hσ:AlgEquiv.restrictNormalHom K σ = 1) (x:K) :
    σ (algebraMap K M x) = algebraMap K M x:=by
  rw [← σ.restrictNormal_commutes K x]
  change algebraMap K M ((AlgEquiv.restrictNormalHom K σ) x) = _
  rw [hσ]
  rfl
lemma zng (u:L) (a:K) (hu:u^2 = algebraMap K L a)
    (hgenL:Algebra.adjoin K {u} = ⊤) (hgenM:normalClosure B L M = ⊤)
    (σ:Gal(M/B)) (hσ:AlgEquiv.restrictNormalHom K σ = 1):σ^2 = 1:=by
  have hfix (f:L →ₐ[B] M) (x:K):σ (f (algebraMap K L x)) = f (algebraMap K L x):=by
    rw [← f.restrictNormal_commutes K x]
    exact zn7 σ hσ _
  apply AlgEquiv.coe_algHom_injective
  apply zar.hom_ext hgenM
  intro f
  let F:Subalgebra K L:={
    carrier:={x | σ (σ (f x)) = f x}
    add_mem':=fun hx hy => by simpa only [Set.mem_setOf_eq,map_add] using congrArg₂ (· + ·) hx hy
    mul_mem':=fun hx hy => by simpa only [Set.mem_setOf_eq,map_mul] using congrArg₂ (· * ·) hx hy
    zero_mem':=by simp
    one_mem':=by simp
    algebraMap_mem':=fun x => by
      change σ (σ (f (algebraMap K L x))) = f (algebraMap K L x)
      rw [hfix,hfix] }
  have hF:Algebra.adjoin K {u} ≤ F:=by
    apply Algebra.adjoin_le
    intro x hx
    have hx':=Set.mem_singleton_iff.mp hx
    subst x
    have hs:(σ (f u))^2 = (f u)^2:=by
      rw [← map_pow,← map_pow,hu,hfix]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · change σ (σ (f u)) = f u
      rw [h,h]
    · change σ (σ (f u)) = f u
      rw [h,map_neg,h,neg_neg]
  rw [hgenL] at hF
  apply AlgHom.ext
  intro x
  change σ (σ (f x)) = f x
  exact hF (show x ∈ (⊤:Subalgebra K L) from trivial)
lemma isPGroup (hK:IsPGroup 2 Gal(K/B))
    (u:L) (a:K) (hu:u^2 = algebraMap K L a)
    (hgenL:Algebra.adjoin K {u} = ⊤) (hgenM:normalClosure B L M = ⊤) :
    IsPGroup 2 Gal(M/B):=by
  intro σ
  obtain ⟨n,hn⟩:=hK (AlgEquiv.restrictNormalHom K σ)
  refine ⟨n+1,?_⟩
  rw [pow_succ,pow_mul]
  exact zng u a hu hgenL hgenM (σ^(2^n)) (by rw [map_pow,hn])
end z78
namespace zic
open CategoryTheory
variable {G H:Type} [Group G] [Group H] [Finite G] (p:ℕ) [Fact p.Prime]
lemma finrank_le (f:G →* H) (hf:Function.Surjective f) :
    Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) H (ZMod p)) 1) ≤
      Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1):=by
  rw [(groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) H (ZMod p))).toLinearEquiv.finrank_eq,
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) G (ZMod p))).toLinearEquiv.finrank_eq]
  let φ:(Additive H →+ ZMod p) →ₗ[ZMod p] (Additive G →+ ZMod p):={
    toFun:=fun χ => χ.comp (MonoidHom.toAdditive f)
    map_add':=fun χ ψ => rfl
    map_smul':=fun r χ => rfl }
  have hφ:Function.Injective φ:=by
    intro χ ψ h
    apply AddMonoidHom.ext
    intro x
    obtain ⟨y,hy⟩:=hf x.toMul
    have he:=congrArg (fun χ:Additive G →+ ZMod p => χ (Additive.ofMul y)) h
    change χ (Additive.ofMul (f y)) = ψ (Additive.ofMul (f y)) at he
    rw [hy] at he; exact he
  letI:Finite (Additive G →+ ZMod p):=Finite.of_injective
    (fun χ:Additive G →+ ZMod p => (χ:Additive G → ZMod p)) DFunLike.coe_injective
  letI:Module.Finite (ZMod p) (Additive G →+ ZMod p):=Module.Finite.of_finite
  exact LinearMap.finrank_le_finrank_of_injective hφ
end zic
namespace z21
open NumberField IntermediateField
open scoped Classical
variable {B:Type} [Field B] [NumberField B] {d:ℕ} (M:Layer B d)
variable (L:Type) [Field L] [NumberField L] [IsTotallyReal L]
  [Algebra M.carrier L] [Algebra B L] [IsScalarTower B M.carrier L]
lemma z9u
    (hunram:differentIdeal (𝓞 M.carrier) (𝓞 L) = ⊤)
    (u:L) (a:M.carrier) (hu:u^2 = algebraMap M.carrier L a)
    (hgen:Algebra.adjoin M.carrier {u} = ⊤)
    (hdegree:1 < Module.finrank M.carrier L) :
    ∃ N:Layer B d, Module.finrank B M.carrier < Module.finrank B N.carrier:=by
  let Ω:=AlgebraicClosure L
  let N:=normalClosure B L Ω
  letI:NumberField N:=NumberField.of_module_finite B N
  let f:M.carrier →ₐ[B] N:=(IsScalarTower.toAlgHom B L N).comp
    (IsScalarTower.toAlgHom B M.carrier L)
  letI:Algebra M.carrier N:=f.toRingHom.toAlgebra
  letI:IsScalarTower B M.carrier N:=IsScalarTower.of_algHom f
  letI:IsScalarTower M.carrier L N:=IsScalarTower.of_algebraMap_eq' rfl
  letI:IsGalois B N:={}
  have hN:normalClosure B L N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp (inferInstance:IsNormalClosure B L N)).2
  letI:IsTotallyReal N:=zag.zan hN
  have hBL:differentIdeal (𝓞 B) (𝓞 L) = ⊤:=by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 B) (𝓞 M.carrier) (𝓞 L),
      M.unramified,hunram,Ideal.map_top,Ideal.top_mul]
  have hBN:=z69.z4e hBL hN
  have hpN:IsPGroup 2 Gal(N/B):=z78.isPGroup M.zcw u a hu hgen hN
  have hdN:d ≤ Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(N/B) (ZMod 2)) 1):=by
    exact M.z30.trans (zic.finrank_le 2
      (AlgEquiv.restrictNormalHom M.carrier) (AlgEquiv.restrictNormalHom_surjective N))
  let N₀:Layer B d:={
    carrier:=N
    field:=inferInstance
    numberField:=inferInstance
    real:=inferInstance
    algebra:=inferInstance
    galois:=inferInstance
    zcw:=hpN
    unramified:=hBN
    z30:=hdN }
  refine ⟨N₀,?_⟩
  change Module.finrank B M.carrier < Module.finrank B N
  have hLN:Module.finrank M.carrier L ≤ Module.finrank M.carrier N :=
    LinearMap.finrank_le_finrank_of_injective
      (f:=(IsScalarTower.toAlgHom M.carrier L N).toLinearMap)
      (IsScalarTower.toAlgHom M.carrier L N).injective
  have hd:=Module.finrank_mul_finrank B M.carrier N
  have hp:0 < Module.finrank B M.carrier:=Module.finrank_pos
  nlinarith
lemma z7y (hM:z4m M)
    (hunram:differentIdeal (𝓞 M.carrier) (𝓞 L) = ⊤)
    (u:L) (a:M.carrier) (hu:u^2 = algebraMap M.carrier L a)
    (hgen:Algebra.adjoin M.carrier {u} = ⊤) :
    Module.finrank M.carrier L = 1:=by
  by_contra hn
  have hp:0 < Module.finrank M.carrier L:=Module.finrank_pos
  have hd:1 < Module.finrank M.carrier L:=by omega
  obtain ⟨N,hN⟩:=z9u M L hunram u a hu hgen hd
  exact hN.not_ge (hM N)
end z21
namespace z18
open scoped Classical
variable (K:Type*) [Field K] [CharZero K] (a b:K)
lemma zl4
    (h:IsSquare (algebraMap K (QuadraticAlgebra K a 0) b)) :
    IsSquare b ∨ ∃ y:K, b = a*y^2:=by
  obtain ⟨z,hz⟩:=h
  have hr:=congrArg QuadraticAlgebra.re hz
  have hi:=congrArg QuadraticAlgebra.im hz
  change b = z.re*z.re+a*z.im*z.im at hr
  change (0:K) = z.re*z.im+z.im*z.re+0*z.im*z.im at hi
  have hh:2*z.re*z.im = 0:=by linear_combination -hi
  have hz':z.re = 0 ∨ z.im = 0:=by
    simpa only [mul_eq_zero,show (2:K) ≠ 0 from by norm_num,false_or] using hh
  rcases hz' with hz' | hz'
  · right
    exact ⟨z.im,by simpa [hz',pow_two,mul_assoc] using hr⟩
  · left
    exact ⟨z.re,by simpa [hz'] using hr⟩
end z18
namespace z18
open scoped Classical
variable (K:Type*) [Field K] [CharZero K] (a b:K)
lemma zaa
    (h:IsSquare (algebraMap K (QuadraticAlgebra K a 0) b)) :
    IsSquare b ∨ IsSquare (b*a):=by
  rcases zl4 K a b h with hb | ⟨y,hy⟩
  · exact Or.inl hb
  · right
    refine ⟨a*y,?_⟩
    rw [hy]
    ring
def root:QuadraticAlgebra K a 0:=⟨0,1⟩
omit [CharZero K] in
lemma z66:(root K a)^2 = algebraMap K (QuadraticAlgebra K a 0) a:=by
  ext <;> simp [root,pow_two,← QuadraticAlgebra.C_eq_algebraMap]
omit [CharZero K] in
lemma z46:Algebra.adjoin K {root K a} = ⊤:=by
  apply top_unique
  intro z _
  have hr:root K a ∈ Algebra.adjoin K {root K a}:=Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem:=Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ z.re)
    (Subalgebra.smul_mem _ hr z.im)
  have he:algebraMap K (QuadraticAlgebra K a 0) z.re+z.im • root K a = z:=by
    ext <;> simp [root,← QuadraticAlgebra.C_eq_algebraMap]
  simpa only [he] using hmem
end z18
namespace z2h
open NumberField
open scoped Classical
lemma zei (z:ℂ) (r:ℝ) (hr:0 ≤ r) (hz:z^2 = r):star z = z:=by
  have hs:((Real.sqrt r:ℂ))^2 = (r:ℂ):=by
    exact_mod_cast Real.sq_sqrt hr
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hz.trans hs.symm) with h | h
  · simp [h]
  · simp [h]
variable (K L:Type*) [Field K] [Field L] [NumberField L]
  [Algebra K L] [IsTotallyReal K]
private def zcp:Subalgebra K L where
  carrier:={x | ∀ σ:L →+* ℂ, star (σ x) = σ x}
  add_mem' hx hy σ:=by rw [map_add,star_add,hx,hy]
  mul_mem' hx hy σ:=by rw [map_mul,star_mul,hx,hy,mul_comm]
  zero_mem' σ:=by simp
  one_mem' σ:=by simp
  algebraMap_mem' x σ:=by
    have h:=IsTotallyReal.complexEmbedding_isReal (σ.comp (algebraMap K L))
    exact RingHom.congr_fun h x
lemma znh (S:Set L) (hgen:Algebra.adjoin K S = ⊤)
    (hS:∀ u ∈ S, ∃ r:ℚ, 0 ≤ r ∧ u^2 = algebraMap ℚ L r):IsTotallyReal L:=by
  have hs:Algebra.adjoin K S ≤ zcp K L:=by
    apply Algebra.adjoin_le
    intro u hu σ
    obtain ⟨r,hr,he⟩:=hS u hu
    apply zei (σ u) (r:ℝ) (by exact_mod_cast hr)
    have hm:=congrArg σ he
    simpa using hm
  have hall:∀ x:L, ∀ σ:L →+* ℂ, star (σ x) = σ x:=by
    intro x
    apply hs
    rw [hgen]
    trivial
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hall x w.embedding
lemma z5m (u:L) (r:ℚ) (hr:0 ≤ r)
    (hu:u^2 = algebraMap ℚ L r) (hgen:Algebra.adjoin K {u} = ⊤):IsTotallyReal L:=by
  apply znh K L {u} hgen
  intro v hv
  exact Set.mem_singleton_iff.mp hv ▸ ⟨r,hr,hu⟩
end z2h
namespace z2h
open NumberField
variable (K L:Type*) [Field K] [Field L] [NumberField L] [Algebra K L] [IsTotallyReal K]
lemma zfs (S:Set L) (hgen:Algebra.adjoin K S = ⊤)
    (hS:∀ u ∈ S, ∃ a:K, u^2 = algebraMap K L a ∧
      ∀ σ:K →+* ℂ, 0 ≤ (σ a).re):IsTotallyReal L:=by
  have hs:Algebra.adjoin K S ≤ zcp K L:=by
    apply Algebra.adjoin_le
    intro u hu σ
    obtain ⟨a,ha,hpos⟩:=hS u hu
    let τ:=σ.comp (algebraMap K L)
    have hr:((τ a).re:ℂ) = τ a :=
      Complex.conj_eq_iff_re.mp (RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal τ) a)
    apply zei (σ u) (τ a).re (hpos τ)
    rw [← map_pow,ha,hr]
    rfl
  rw [hgen] at hs
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hs (show x ∈ (⊤:Subalgebra K L) from trivial) w.embedding
end z2h
namespace z6d
open NumberField Polynomial
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma z9g (a b c:𝓞 K) (hab:a = b^2+4*c)
    (u:L) (hu:u^2 = algebraMap K L (a:K)) :
    IsIntegral ℤ ((u+algebraMap K L (b:K))/2):=by
  apply isIntegral_trans (A:=𝓞 K)
  refine ⟨X^2-C b*X-C c,?_,?_⟩
  · apply Monic.sub_of_left (Monic.sub_of_left (monic_X.pow 2) (by compute_degree!))
    rw [degree_sub_eq_left_of_degree_lt (by compute_degree!)]
    compute_degree!
  · simp only [eval₂_sub,eval₂_pow,eval₂_mul,eval₂_X,eval₂_C]
    have hab':algebraMap K L (a:K) =
        (algebraMap K L (b:K))^2+4*algebraMap K L (c:K):=by
      exact congrArg (algebraMap (𝓞 K) L) hab |>.trans (by
        simp only [map_add,map_pow,map_mul,map_ofNat]
        rfl)
    change ((u+algebraMap K L (b:K))/2)^2 -
      algebraMap K L (b:K)*((u+algebraMap K L (b:K))/2)-algebraMap K L (c:K) = 0
    field_simp
    linear_combination hu.trans hab'
end z6d
namespace z5f
open NumberField Polynomial
open scoped Classical nonZeroDivisors
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma zaz (a:𝓞 K) (b c:𝓞 K) (hab:a = b^2+4*c)
    (u:L) (hu:u^2 = algebraMap K L ((a:𝓞 K):K))
    (hgen:Algebra.adjoin K {u} = ⊤):algebraMap (𝓞 K) (𝓞 L) a ∈ differentIdeal (𝓞 K) (𝓞 L):=by
  let v:𝓞 L:=⟨(u+algebraMap K L (b:K))/2,z6d.z9g K L a b c hab u hu⟩
  have hvgen:Algebra.adjoin K {(v:L)} = ⊤:=by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro x hx
    have hx':x = u:=Set.mem_singleton_iff.mp hx
    subst x
    have hv:(v:L) ∈ Algebra.adjoin K {(v:L)}:=Algebra.subset_adjoin (Set.mem_singleton _)
    have he:u = 2*(v:L)-algebraMap K L (b:K):=by
      change u = 2*((u+algebraMap K L (b:K))/2)-algebraMap K L (b:K); ring
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2) hv)
      (Subalgebra.algebraMap_mem _ _)
  have hvrel:v^2-algebraMap (𝓞 K) (𝓞 L) b*v-algebraMap (𝓞 K) (𝓞 L) c = 0:=by
    apply RingOfIntegers.coe_injective
    change ((u+algebraMap K L (b:K))/2)^2 -
      algebraMap K L (b:K)*((u+algebraMap K L (b:K))/2)-algebraMap K L (c:K) = 0
    have hab':algebraMap K L ((a:𝓞 K):K) =
        (algebraMap K L (b:K))^2+4*algebraMap K L (c:K):=by
      exact congrArg (algebraMap (𝓞 K) L) hab |>.trans (by
        simp only [map_add,map_pow,map_mul,map_ofNat]
        rfl)
    field_simp
    linear_combination hu.trans hab'
  have hd:=z2n.z50 K L v hvgen (X^2-C b*X-C c)
    (by simpa using hvrel)
  let z:𝓞 L:=2*v-algebraMap (𝓞 K) (𝓞 L) b
  have hz:z ∈ differentIdeal (𝓞 K) (𝓞 L):=by
    simpa [z,derivative_sub,derivative_pow,derivative_mul,derivative_X,derivative_C,map_ofNat] using hd
  have hzu:(z:L) = u:=by dsimp [z,v]; change 2*((u+algebraMap K L (b:K))/2)-algebraMap K L (b:K) = u; field_simp; ring
  have hzsq:z^2 = algebraMap (𝓞 K) (𝓞 L) a:=by
    apply RingOfIntegers.coe_injective
    change (z:L)^2 = algebraMap K L ((a:𝓞 K):K)
    rw [hzu,hu]
  rw [← hzsq,pow_two]
  exact Ideal.mul_mem_left _ _ hz
lemma z4e (a b c:𝓞 K) (ha0:a ≠ 0) (ha2:IsCoprime a 2)
    (hab:a = b^2+4*c) (I:FractionalIdeal (𝓞 K)⁰ K) (hI:I ≠ 0)
    (hvirtual:FractionalIdeal.spanSingleton (𝓞 K)⁰ (a:K) = I*I)
    (u:L) (hu:u^2 = algebraMap K L (a:K))
    (hgen:Algebra.adjoin K {u} = ⊤):differentIdeal (𝓞 K) (𝓞 L) = ⊤:=by
  have haD:=zaz K L a b c hab u hu hgen
  by_cases hau:IsUnit a
  · exact Ideal.eq_top_of_isUnit_mem _ haD (hau.map (algebraMap (𝓞 K) (𝓞 L)))
  have hp0:Ideal.span ({a}:Set (𝓞 K)) ≠ ⊥:=by simpa using ha0
  have hp1:Ideal.span ({a}:Set (𝓞 K)) ≠ ⊤:=by
    intro he
    exact hau (Ideal.span_singleton_eq_top.mp he)
  obtain ⟨x,hx,r,hr,hcop⟩:=z41.z4r K
    (Ideal.span {a}) hp0 hp1 (a:K) I hI hvirtual
  have hvsq:(algebraMap K L x*u)^2 = algebraMap K L (r:K):=by
    rw [mul_pow,hu,hr,map_mul,map_pow]
    ring
  have hvi:IsIntegral ℤ (algebraMap K L x*u) :=
    IsIntegral.of_pow (by norm_num:0 < 2)
      (hvsq ▸ (algebraMap (𝓞 K) (𝓞 L) r).property)
  let v:𝓞 L:=⟨algebraMap K L x*u,hvi⟩
  have hvgen:Algebra.adjoin K {(v:L)} = ⊤:=by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro y ⟨rfl⟩
    have hv:(v:L) ∈ Algebra.adjoin K {(v:L)}:=Algebra.subset_adjoin (Set.mem_singleton _)
    have he:u = algebraMap K L x⁻¹*(v:L):=by
      change u = algebraMap K L x⁻¹*(algebraMap K L x*u)
      rw [map_inv₀,← mul_assoc,inv_mul_cancel₀ (by simpa only [map_zero] using (algebraMap K L).injective.ne hx),one_mul]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hv
  have hvrel:v^2 = algebraMap (𝓞 K) (𝓞 L) r:=RingOfIntegers.coe_injective hvsq
  have hvD:=z2n.zha K L r v hvgen hvrel
  have h4r:algebraMap (𝓞 K) (𝓞 L) (4*r) ∈ differentIdeal (𝓞 K) (𝓞 L):=by
    have he:(2*v)^2 = algebraMap (𝓞 K) (𝓞 L) (4*r):=by
      rw [mul_pow,hvrel,map_mul,map_ofNat]
      norm_num
    rw [← he,pow_two]
    exact Ideal.mul_mem_left _ _ hvD
  have har:IsCoprime a r:=(Ideal.isCoprime_span_singleton_iff a r).mp hcop
  have ha4:IsCoprime a 4:=by
    have he:=ha2.pow_right (n:=2)
    norm_num at he ⊢
    exact he
  obtain ⟨s,t,hst⟩:=ha4.mul_right har
  have hh:=Ideal.add_mem (differentIdeal (𝓞 K) (𝓞 L))
    (Ideal.mul_mem_left _ (algebraMap (𝓞 K) (𝓞 L) s) haD)
    (Ideal.mul_mem_left _ (algebraMap (𝓞 K) (𝓞 L) t) h4r)
  have he:=congrArg (algebraMap (𝓞 K) (𝓞 L)) hst
  simp only [map_add,map_mul,map_one] at he
  apply (Ideal.eq_top_iff_one _).mpr
  rw [map_mul,he] at hh
  exact hh
end z5f
namespace z21
open NumberField
open scoped Classical
variable {B:Type} [Field B] [NumberField B] {d:ℕ} (M:Layer B d)
lemma z72 (hM:z4m M) :
    z1z.z3s M.carrier:=by
  intro a b c ha0 hcop hbc I hI hvirt hpos
  by_contra hn
  let aK:M.carrier:=(a:M.carrier)
  letI:Fact (∀ x:M.carrier, x^2 ≠ aK+0*x) :=
    ⟨fun x hx => hn ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let L:=QuadraticAlgebra M.carrier aK 0
  letI:NumberField L:=NumberField.of_module_finite M.carrier L
  letI:Algebra B L:=inferInstance
  letI:IsScalarTower B M.carrier L:=inferInstance
  let u:L:=z18.root M.carrier aK
  have hu:u^2 = algebraMap M.carrier L aK:=z18.z66 M.carrier aK
  have hgen:Algebra.adjoin M.carrier {u} = ⊤:=z18.z46 M.carrier aK
  letI:IsTotallyReal L:=z2h.zfs M.carrier L {u} hgen (by
    intro x hx
    have hx':x = u:=Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨aK,hu,hpos⟩)
  have hunram:=z5f.z4e M.carrier L a b c ha0 hcop hbc I hI hvirt u hu hgen
  have hd:=z7y M L hM hunram u aK hu hgen
  have he:Module.finrank M.carrier L = 2:=QuadraticAlgebra.finrank_eq_two aK 0
  omega
end z21
namespace z12
open NumberField
open scoped Classical
variable (E:Type*) [Field E] [NumberField E]
lemma z8i (hcop:IsCoprime (differentIdeal ℤ (𝓞 E)) (modulus E)) :
    IsReduced (R E):=by
  let p:Ideal ℤ:=Ideal.span {(2:ℤ)}
  have hp0:p ≠ ⊥:=by simp [p]
  letI:p.IsPrime:=(Ideal.span_singleton_prime (by norm_num:(2:ℤ) ≠ 0)).mpr
    (by norm_num [Int.prime_iff_natAbs_prime])
  letI:p.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance hp0
  have hs:Squarefree (modulus E):=by
    apply (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (by simp [modulus])).mpr
    intro P hP hsq
    have hd:=pow_sub_one_dvd_differentIdeal ℤ P 2 hp0 (by
      simpa only [p,Ideal.map_span,Set.image_singleton,map_ofNat,pow_two,modulus] using hsq)
    simp only [Nat.reduceSub,pow_one] at hd
    exact hP.not_isUnit (hcop.isUnit_of_dvd' hd (dvd_trans (dvd_mul_right P P) hsq))
  apply (Ideal.isRadical_iff_quotient_reduced (modulus E)).mp
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)).mpr
  intro x hx
  apply Ideal.dvd_span_singleton.mp
  apply (hs.dvd_pow_iff_dvd (by norm_num:(2:ℕ) ≠ 0)).mp
  rw [Ideal.span_singleton_pow]
  exact Ideal.dvd_span_singleton.mpr hx
end z12
namespace z12
open NumberField
variable (K E:Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
lemma zdc (hcop:IsCoprime (NumberField.discr E) (2:ℤ)) :
    IsCoprime (differentIdeal ℤ (𝓞 E)) (modulus E):=by
  obtain ⟨a,b,hab⟩:=hcop
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a*NumberField.discr E,Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)),
    b*2,Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),?_⟩
  exact_mod_cast hab
lemma z7t
    (hcop:IsCoprime (NumberField.discr K) (2:ℤ))
    (hunram:differentIdeal (𝓞 K) (𝓞 E) = ⊤):IsReduced (R E):=by
  apply z8i E
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E),hunram,Ideal.top_mul]
  have h:=(zdc K hcop).map (Ideal.mapHom (algebraMap (𝓞 K) (𝓞 E)))
  simpa only [Ideal.mapHom_apply,modulus,Ideal.map_span,Set.image_singleton,map_ofNat] using h
end z12
namespace z21
open NumberField z7
open scoped Classical
variable (B:Type) [Field B] [NumberField B] [IsTotallyReal B] (d:ℕ)
lemma zct (hodd:IsCoprime (NumberField.discr B) (2:ℤ)) :
    z3v B d
      (Module.finrank (ZMod 2) (z6.V (C B))+2*Module.finrank ℚ B):=by
  intro M hM
  letI:IsReduced (z12.R M.carrier) :=
    z12.z7t B M.carrier hodd M.unramified
  exact z1a.zbi B M.carrier M.zcw M.unramified
    (z72 M hM)
lemma zgz (hodd:IsCoprime (NumberField.discr B) (2:ℤ))
    (h₀:Nonempty (Layer B d)) (hd:3 ≤ d)
    (hnum:4*(Module.finrank (ZMod 2) (z6.V (C B))+2*Module.finrank ℚ B) ≤ d^2) :
    ∃ M:ℕ → Layer B d, ∀ n, 2^n ≤ Module.finrank B (M n).carrier :=
  zkb h₀ hd hnum (zct B d hodd)
end z21
namespace z4i
open NumberField
open scoped Classical nonZeroDivisors
variable (K:Type*) [Field K] [NumberField K] [IsTotallyReal K]
lemma card_le (hdeg:Module.finrank ℚ K = 4) :
    Nat.card (ClassGroup (𝓞 K)) ≤ 16*(NumberField.discr K).natAbs:=by
  have hex (C:ClassGroup (𝓞 K)):∃ I:(Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧ (Ideal.absNorm I.1:ℝ) ≤ Real.sqrt |(NumberField.discr K:ℝ)|:=by
    obtain ⟨I,hI,hbound⟩:=NumberField.exists_ideal_in_class_of_norm_le C
    refine ⟨I,hI,hbound.trans ?_⟩
    rw [IsTotallyReal.nrComplexPlaces_eq_zero,hdeg]
    norm_num
    nlinarith [Real.sqrt_nonneg |(NumberField.discr K:ℝ)|]
  choose f hf hb using hex
  let S:Finset (Ideal (𝓞 K)):=Finset.univ.image (fun C => (f C).1)
  let N:ℕ:=⌊Real.sqrt |(NumberField.discr K:ℝ)|⌋₊
  have hinj:Function.Injective (fun C => (f C).1):=by
    intro C D h
    have he:f C = f D:=Subtype.ext h
    rw [← hf C,← hf D,he]
  have hcard:S.card = Nat.card (ClassGroup (𝓞 K)):=by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Nat.card_eq_fintype_card]
  have hcount:S.card ≤ 2^(Module.finrank ℚ K)*N^2:=by
    apply z9l.card_le K S N
    · intro I hI
      obtain ⟨C,_,rfl⟩:=Finset.mem_image.mp hI
      exact mem_nonZeroDivisors_iff_ne_zero.mp (f C).2
    · intro I hI
      obtain ⟨C,_,rfl⟩:=Finset.mem_image.mp hI
      exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (hb C)
  rw [hcard,hdeg] at hcount
  have hN:(N:ℝ)^2 ≤ (NumberField.discr K).natAbs:=by
    have hle:(N:ℝ) ≤ Real.sqrt |(NumberField.discr K:ℝ)|:=Nat.floor_le (Real.sqrt_nonneg _)
    have hsq:=sq_le_sq₀ (by positivity:(0:ℝ) ≤ N) (Real.sqrt_nonneg |(NumberField.discr K:ℝ)|) |>.mpr hle
    rw [Real.sq_sqrt (abs_nonneg _)] at hsq
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hsq
  have hN':N^2 ≤ (NumberField.discr K).natAbs:=by exact_mod_cast hN
  exact hcount.trans (by norm_num; omega)
end z4i
namespace z4i
open NumberField z7
open scoped Classical
variable (K:Type) [Field K] [NumberField K] [IsTotallyReal K]
lemma zhm (hdeg:Module.finrank ℚ K = 4) :
    2^Module.finrank (ZMod 2) (z6.V (C K)) ≤ 16*(NumberField.discr K).natAbs:=by
  letI:Finite (C K):=Finite.of_equiv (zj.Classes K) Additive.ofMul
  letI:Finite (z6.V (C K)):=Finite.of_surjective z6.mk z6.mk_surjective
  letI:FiniteDimensional (ZMod 2) (z6.V (C K)):=Module.Finite.of_finite
  have h:=Nat.card_le_card_of_surjective (z6.mk (A:=C K)) z6.mk_surjective
  have hc:Nat.card (C K) = Nat.card (ClassGroup (𝓞 K)) :=
    (Nat.card_congr (Additive.ofMul:zj.Classes K ≃ C K)).symm.trans
      (Nat.card_congr (zj.equiv K).toEquiv)
  rw [hc,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_eq_fintype_card,ZMod.card] at h
  exact h.trans (card_le K hdeg)
lemma zls (hdeg:Module.finrank ℚ K = 4) (N:ℕ)
    (hdisc:16*(NumberField.discr K).natAbs ≤ 2^N) :
    Module.finrank (ZMod 2) (z6.V (C K)) ≤ N:=by
  apply (Nat.pow_le_pow_iff_right (by norm_num:1 < 2)).mp
  exact (zhm K hdeg).trans hdisc
end z4i
namespace z3r
open NumberField Polynomial
open scoped Classical
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma z9g (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1) :
    IsIntegral ℤ ((u+1)/2):=by
  refine ⟨X^2-X-C a,?_,?_⟩
  · apply Monic.sub_of_left (Monic.sub_of_left (monic_X.pow 2) (by simp))
    rw [degree_sub_eq_left_of_degree_lt (by simp)]
    exact lt_of_le_of_lt degree_C_le (by simp)
  · simp only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
    change ((u+1)/2)^2-(u+1)/2-(a:L) = 0
    have htwo:(2:L) ≠ 0:=by norm_num
    field_simp
    linear_combination hu
noncomputable def half (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1):𝓞 L :=
  ⟨(u+1)/2,z9g L a u hu⟩
lemma zkq (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1) :
    (half L a u hu)^2-half L a u hu-a = 0:=by
  apply RingOfIntegers.coe_injective
  change ((u+1)/2)^2-(u+1)/2-(a:L) = 0
  field_simp
  linear_combination hu
omit [NumberField K] in
lemma zm9 (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1)
    (hgen:Algebra.adjoin K {u} = ⊤) :
    Algebra.adjoin K {((half L a u hu:𝓞 L):L)} = ⊤:=by
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  intro x hx
  have hx':x = u:=Set.mem_singleton_iff.mp hx
  subst x
  have ht:((u+1)/2:L) ∈ Algebra.adjoin K {((half L a u hu:𝓞 L):L)} :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have he:u = 2*((u+1)/2)-1:=by field_simp; ring
  have hmem:=Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2) ht) (Subalgebra.one_mem _)
  simpa only [Nat.cast_ofNat,← he,SetLike.mem_coe] using hmem
noncomputable def z2e (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1):𝓞 L :=
  2*half L a u hu-1
@[simp] lemma zik (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1) :
    (z2e L a u hu:L) = u:=by
  change 2*((u+1)/2)-1 = u
  field_simp
  ring
lemma z5q (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1)
    (hgen:Algebra.adjoin K {u} = ⊤) :
    z2e L a u hu ∈ differentIdeal (𝓞 K) (𝓞 L):=by
  have hd:=z2n.z50 K L (half L a u hu) (zm9 K L a u hu hgen)
    (X^2-X-C (a:𝓞 K)) (by simpa using zkq L a u hu)
  simpa [z2e,derivative_sub,derivative_pow,derivative_X,derivative_C,map_ofNat] using hd
lemma cast_four_aux (M:Type*) [Field M] [NumberField M] (a:ℤ) :
    ((((4*a+1:ℤ):𝓞 M)):M) = 4*(a:M)+1:=by
  rw [show ((4*a+1:ℤ):𝓞 M) = 4*(a:𝓞 M)+1 by push_cast; ring]
  rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_one, map_intCast, map_ofNat]
lemma rootInteger_sq_aux (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1) :
    (z2e L a u hu)^2 = ((4*a+1:ℤ):𝓞 L):=by
  have h2:((z2e L a u hu:𝓞 L):L)^2 = u^2:=by rw [zik]
  apply RingOfIntegers.coe_injective
  rw [map_pow]
  exact (h2.trans hu).trans (cast_four_aux L a).symm
lemma z4e (a b:ℤ) (hcop:IsCoprime (4*a+1) (4*b+1))
    (u v:L) (hu:u^2 = 4*(a:L)+1) (hv:v^2 = 4*(b:L)+1)
    (hgenU:Algebra.adjoin K {u} = ⊤) (hgenV:Algebra.adjoin K {v} = ⊤) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤:=by
  let D:=differentIdeal (𝓞 K) (𝓞 L)
  have hU:z2e L a u hu ∈ D:=z5q K L a u hu hgenU
  have hV:z2e L b v hv ∈ D:=z5q K L b v hv hgenV
  have hUsq:(z2e L a u hu)^2 = (4*a+1:ℤ):=rootInteger_sq_aux L a u hu
  have hVsq:(z2e L b v hv)^2 = (4*b+1:ℤ):=rootInteger_sq_aux L b v hv
  obtain ⟨r,s,hrs⟩:=hcop
  have hA:((4*a+1:ℤ):𝓞 L) ∈ D:=hUsq ▸ (show (z2e L a u hu)^2 ∈ D by rw [pow_two]; exact D.mul_mem_left _ hU)
  have hB:((4*b+1:ℤ):𝓞 L) ∈ D:=hVsq ▸ (show (z2e L b v hv)^2 ∈ D by rw [pow_two]; exact D.mul_mem_left _ hV)
  apply (Ideal.eq_top_iff_one _).mpr
  have hm:=D.add_mem (D.mul_mem_left (r:𝓞 L) hA) (D.mul_mem_left (s:𝓞 L) hB)
  convert hm using 1
  exact_mod_cast hrs.symm
end z3r
namespace z2t
open NumberField
open scoped Classical
variable (K L:Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
lemma zaz (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1)
    (hgen:Algebra.adjoin K {u} = ⊤):((4*a+1:ℤ):𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L):=by
  have hr:=z3r.z5q K L a u hu hgen
  have hs:(z3r.z2e L a u hu)^2 = ((4*a+1:ℤ):𝓞 L) :=
    z3r.rootInteger_sq_aux L a u hu
  have h:=Ideal.mul_mem_left (differentIdeal (𝓞 K) (𝓞 L)) (z3r.z2e L a u hu) hr
  rwa [← pow_two,hs] at h
lemma zkh (a:ℤ):Ideal.absNorm (Ideal.span {(a:𝓞 L)}) = a.natAbs^Module.finrank ℚ L:=by
  rw [Ideal.absNorm_span_singleton]
  have hn:=Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis L) a
  rw [← Module.finrank_eq_card_basis (RingOfIntegers.basis L),RingOfIntegers.rank] at hn
  rw [eq_intCast] at hn
  simpa only [map_intCast,Int.cast_id,Int.natAbs_pow] using congrArg Int.natAbs hn
lemma zg1 (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1)
    (hgen:Algebra.adjoin K {u} = ⊤) :
    (NumberField.discr L).natAbs ∣ (4*a+1).natAbs^Module.finrank ℚ L *
      (NumberField.discr K).natAbs^Module.finrank K L:=by
  have hd:=Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem _).mpr (zaz K L a u hu hgen))
  rw [zkh] at hd
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  exact mul_dvd_mul_right hd _
lemma odd (hodd:IsCoprime (NumberField.discr K) (2:ℤ))
    (a:ℤ) (u:L) (hu:u^2 = 4*(a:L)+1) (hgen:Algebra.adjoin K {u} = ⊤) :
    IsCoprime (NumberField.discr L) (2:ℤ):=by
  have ha:IsCoprime (4*a+1) (2:ℤ):=⟨1,-2*a,by ring⟩
  rw [Int.isCoprime_iff_nat_coprime] at hodd ha ⊢
  have hc:=(ha.pow_left (Module.finrank ℚ L)).mul_left (hodd.pow_left (Module.finrank K L))
  exact hc.of_dvd_left (zg1 K L a u hu hgen)
end z2t
namespace z2j
open NumberField
lemma natCast_eq_aux {R:Type*} [CommRing R] (D:ℕ) (a:ℤ) (h:(D:ℤ) = 4*a+1) :
    (D:R) = 4*(a:R)+1:=by
  have h2:=congrArg (Int.cast:ℤ → R) h
  push_cast at h2
  exact h2
lemma prod_cast_aux {R:Type*} [CommRing R] {ι:Type*} (a:ι → ℤ) (s:Finset ι) (b:ℤ)
    (h:∏ i ∈ s, (4*a i+1) = 4*b+1):∏ i ∈ s, (4*(a i:R)+1) = 4*(b:R)+1:=by
  have h2:=congrArg (Int.cast:ℤ → R) h
  push_cast at h2
  exact h2
lemma prod_cast_nat_aux {R:Type*} [CommRing R] {ι:Type*} (a:ι → ℤ) (s:Finset ι) (D:ℕ)
    (h:∏ i ∈ s, (4*a i+1) = ((5*D:ℕ):ℤ)):∏ i ∈ s, (4*(a i:R)+1) = 5*(D:R):=by
  have h2:=congrArg (Int.cast:ℤ → R) h
  push_cast at h2
  exact h2
lemma algebraMap_four_aux {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] (z:ℤ) :
    algebraMap R S (4*(z:R)+1) = 4*(z:S)+1:=by
  rw [map_add, map_mul, map_intCast, map_one, map_ofNat]
open scoped Classical
structure Data (D:ℕ) where
  B:Type
  field:Field B
  numberField:NumberField B
  real:IsTotallyReal B
  z5y:B
  sqrtD:B
  zjk:z5y^2 = 5
  D_sq:sqrtD^2 = D
  degree:Module.finrank ℚ B = 4
  odd:IsCoprime (NumberField.discr B) (2:ℤ)
  z8q:(NumberField.discr B).natAbs ≤ 625*D^4
instance instOMAField6:type_of% @Data.field:=@Data.field
instance instOMAField7:type_of% @Data.numberField:=@Data.numberField
instance instOMAField8:type_of% @Data.real:=@Data.real
lemma z3n (D:ℕ) (hDpos:0 < D) (a:ℤ) (hDa:(D:ℤ) = 4*a+1)
    (h5:¬ IsSquare (5:ℚ)) (hD:¬ IsSquare (D:ℚ)) (h5D:¬ IsSquare (5*(D:ℚ))) :
    Nonempty (Data D):=by
  letI:Fact (∀ x:ℚ, x^2 ≠ (5:ℚ)+0*x) :=
    ⟨fun x hx => h5 ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let F:=QuadraticAlgebra ℚ (5:ℚ) 0
  letI:NumberField F:=NumberField.of_module_finite ℚ F
  let u:F:=z18.root ℚ 5
  have hu:u^2 = 5:=by simpa using z18.z66 ℚ (5:ℚ)
  have hgenF:Algebra.adjoin ℚ {u} = ⊤:=z18.z46 ℚ (5:ℚ)
  letI:IsTotallyReal F:=z2h.z5m ℚ F u 5 (by norm_num) (by simpa using hu) hgenF
  have hDF:¬ IsSquare (D:F):=by
    intro h
    have h':IsSquare (algebraMap ℚ F (D:ℚ)):=by simpa using h
    rcases z18.zaa ℚ (5:ℚ) (D:ℚ) h' with h' | h'
    · exact hD h'
    · exact h5D (by simpa only [mul_comm] using h')
  letI:Fact (∀ x:F, x^2 ≠ (D:F)+0*x) :=
    ⟨fun x hx => hDF ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let B:=QuadraticAlgebra F (D:F) 0
  letI:NumberField B:=NumberField.of_module_finite F B
  let v:B:=z18.root F (D:F)
  have hv:v^2 = D:=by simpa only [map_natCast] using z18.z66 F (D:F)
  have hgenB:Algebra.adjoin F {v} = ⊤:=z18.z46 F (D:F)
  letI:IsTotallyReal B:=z2h.z5m F B v (D:ℚ)
    (by positivity) (by simpa using hv) hgenB
  have hdF:Module.finrank ℚ F = 2:=QuadraticAlgebra.finrank_eq_two 5 0
  have hdFB:Module.finrank F B = 2:=QuadraticAlgebra.finrank_eq_two (D:F) 0
  have hdB:Module.finrank ℚ B = 4:=by
    rw [← Module.finrank_mul_finrank ℚ F B,hdF,hdFB]
  have hu':u^2 = 4*(1:F)+1:=by norm_num; exact hu
  have hv':v^2 = 4*(a:B)+1:=by rw [hv]; exact natCast_eq_aux D a hDa
  have hoddQ:IsCoprime (NumberField.discr ℚ) (2:ℤ):=by norm_num [Int.isCoprime_iff_nat_coprime]
  have hoddF:=z2t.odd ℚ F hoddQ 1 u hu' hgenF
  have hoddB:=z2t.odd F B hoddF a v hv' hgenB
  have hdiscF:(NumberField.discr F).natAbs ≤ 25:=by
    have hdiv:=z2t.zg1 ℚ F 1 u hu' hgenF
    norm_num [hdF] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hdiscB:(NumberField.discr B).natAbs ≤ 625*D^4:=by
    have hdiv:=z2t.zg1 F B a v hv' hgenB
    rw [← hDa,Int.natAbs_natCast,hdB,hdFB] at hdiv
    have hp:0 < D^4*(NumberField.discr F).natAbs^2:=by
      exact mul_pos (pow_pos hDpos _) (pow_pos (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)) _)
    apply (Nat.le_of_dvd hp hdiv).trans
    nlinarith [Nat.pow_le_pow_left hdiscF 2]
  refine ⟨{
    B:=B
    field:=inferInstance
    numberField:=inferInstance
    real:=inferInstance
    z5y:=algebraMap F B u
    sqrtD:=v
    zjk:=by rw [← map_pow,hu,map_ofNat]
    D_sq:=hv
    degree:=hdB
    odd:=hoddB
    z8q:=hdiscB }⟩
end z2j
namespace z45
open NumberField
open scoped Classical
variable (K:Type*) [Field K] [NumberField K] (a b:ℤ)
variable [Fact (∀ x:K, x^2 ≠ (4*(a:K)+1)+0*x)]
abbrev L:=QuadraticAlgebra K (4*(a:K)+1) 0
noncomputable instance:NumberField (L K a):=NumberField.of_module_finite K (L K a)
noncomputable def u:L K a:=z18.root K (4*(a:K)+1)
@[simp] lemma u_sq:(u K a)^2 = 4*(a:L K a)+1:=by
  have h:=z18.z66 K (4*(a:K)+1)
  rw [z2j.algebraMap_four_aux] at h
  exact h
noncomputable def v (w:K):L K a:=algebraMap K (L K a) w / u K a
lemma znf (ha:4*a+1 ≠ 0):u K a ≠ 0:=by
  intro h
  have hs:=u_sq K a
  rw [h,zero_pow (by norm_num),eq_comm] at hs
  apply ha
  exact_mod_cast hs
lemma v_sq (w:K) (hw:w^2 = (4*(a:K)+1)*(4*(b:K)+1))
    (ha:4*a+1 ≠ 0):(v K a w)^2 = 4*(b:L K a)+1:=by
  have hw':(algebraMap K (L K a) w)^2 =
      (4*(a:L K a)+1)*(4*(b:L K a)+1):=by
    simpa only [map_pow,map_mul,map_add,map_ofNat,map_intCast,map_one] using congrArg (algebraMap K (L K a)) hw
  rw [v,div_pow,u_sq]
  have ha':(4*(a:L K a)+1) ≠ 0:=by exact_mod_cast ha
  apply (div_eq_iff ha').mpr
  simpa [mul_comm] using hw'
omit [NumberField K] in
lemma ze4:Algebra.adjoin K {u K a} = ⊤:=z18.z46 K _
lemma znm (w:K) (hw:w^2 = (4*(a:K)+1)*(4*(b:K)+1))
    (ha:4*a+1 ≠ 0) (hb:4*b+1 ≠ 0):Algebra.adjoin K {v K a w} = ⊤:=by
  have hu0:=znf K a ha
  have hb':(4*(b:L K a)+1) ≠ 0:=by exact_mod_cast hb
  have hw':(algebraMap K (L K a) w)^2 =
      (4*(a:L K a)+1)*(4*(b:L K a)+1):=by
    simpa only [map_pow,map_mul,map_add,map_ofNat,map_intCast,map_one] using congrArg (algebraMap K (L K a)) hw
  have he:u K a = algebraMap K (L K a) (w/(4*(b:K)+1))*v K a w:=by
    rw [v,map_div₀,map_add,map_mul,map_ofNat,map_intCast,map_one]
    field_simp
    linear_combination (4*(b:L K a)+1)*(u_sq K a)-hw'
  apply top_unique
  rw [← ze4 K a]
  apply Algebra.adjoin_le
  intro x hx
  have hx':x = u K a:=Set.mem_singleton_iff.mp hx
  subst x
  rw [he]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin (Set.mem_singleton _))
lemma unramified (w:K) (hw:w^2 = (4*(a:K)+1)*(4*(b:K)+1))
    (ha:4*a+1 ≠ 0) (hb:4*b+1 ≠ 0) (hcop:IsCoprime (4*a+1) (4*b+1)) :
    differentIdeal (𝓞 K) (𝓞 (L K a)) = ⊤ :=
  z3r.z4e K (L K a) a b hcop (u K a) (v K a w)
    (u_sq K a) (v_sq K a b w hw ha) (ze4 K a) (znm K a b w hw ha hb)
lemma zan [IsTotallyReal K] (ha:0 ≤ 4*a+1):IsTotallyReal (L K a):=by
  apply z2h.z5m K (L K a) (u K a) (4*a+1:ℚ) (by exact_mod_cast ha) ?_ (ze4 K a)
  simp
end z45
namespace z9a
open NumberField
open scoped Classical
universe u
variable (K:Type u) [Field K] [NumberField K] (a b:ℤ)
structure Data where
  carrier:Type u
  instField:Field carrier
  instNumberField:NumberField carrier
  instAlgebra:Algebra K carrier
  z59:IsTotallyReal carrier
  root:carrier
  remainder:carrier
  z66:root^2 = 4*(a:carrier)+1
  zb3:remainder^2 = 4*(b:carrier)+1
  z46:Algebra.adjoin K {root} = ⊤
  unramified:differentIdeal (𝓞 K) (𝓞 carrier) = ⊤
instance instOMAField9:type_of% @Data.instField:=@Data.instField
instance instOMAField10:type_of% @Data.instNumberField:=@Data.instNumberField
instance instOMAField11:type_of% @Data.instAlgebra:=@Data.instAlgebra
instance instOMAField12:type_of% @Data.z59:=@Data.z59
variable [IsTotallyReal K]
lemma z3n (w:K) (hw:w^2 = (4*(a:K)+1)*(4*(b:K)+1))
    (ha:0 < 4*a+1) (hb:0 < 4*b+1) (hcop:IsCoprime (4*a+1) (4*b+1)) :
    Nonempty (Data K a b):=by
  classical
  by_cases hs:IsSquare (4*(a:K)+1)
  · obtain ⟨x,hx⟩:=hs
    have hx':x^2 = 4*(a:K)+1:=by simpa [pow_two] using hx.symm
    have ha':(4*(a:K)+1) ≠ 0:=by exact_mod_cast ha.ne'
    have hrem:(w/x)^2 = 4*(b:K)+1:=by
      rw [div_pow,hx',hw]
      exact mul_div_cancel_left₀ _ ha'
    refine ⟨{
      carrier:=K
      instField:=inferInstance
      instNumberField:=inferInstance
      instAlgebra:=inferInstance
      z59:=inferInstance
      root:=x
      remainder:=w/x
      z66:=hx'
      zb3:=hrem
      z46:=Subsingleton.elim _ _
      unramified:=?_ }⟩
    apply (Ideal.eq_top_iff_one _).mpr
    have hd:=z2n.z50 K K (0:𝓞 K) (Subsingleton.elim _ _) Polynomial.X (by simp)
    simpa using hd
  · letI:Fact (∀ x:K, x^2 ≠ (4*(a:K)+1)+0*x) :=
      ⟨fun x hx => hs ⟨x,by simpa [pow_two] using hx.symm⟩⟩
    letI:IsTotallyReal (z45.L K a):=z45.zan K a ha.le
    exact ⟨{
      carrier:=z45.L K a
      instField:=inferInstance
      instNumberField:=inferInstance
      instAlgebra:=inferInstance
      z59:=inferInstance
      root:=z45.u K a
      remainder:=z45.v K a w
      z66:=z45.u_sq K a
      zb3:=z45.v_sq K a b w hw ha.ne'
      z46:=z45.ze4 K a
      unramified:=z45.unramified K a b w hw ha.ne' hb.ne' hcop }⟩
end z9a
namespace z3y
open NumberField
open scoped Classical BigOperators
variable (K E L:Type*) [Field K] [Field E] [Field L]
  [NumberField K] [NumberField E] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
lemma zhk
    (hE:differentIdeal (𝓞 K) (𝓞 E) = ⊤) (hL:differentIdeal (𝓞 E) (𝓞 L) = ⊤) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤:=by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 E) (𝓞 L),hE,hL,Ideal.map_top]
  simp
omit [NumberField K] [NumberField E] [NumberField L] in
lemma zl3 (S:Set E) (T:Set L)
    (hS:Algebra.adjoin K S = ⊤) (hT:Algebra.adjoin E T = ⊤) :
    Algebra.adjoin K ((algebraMap E L '' S) ∪ T) = ⊤:=by
  rw [← Algebra.adjoin_eq_adjoin_union K S T hS,hT,Subalgebra.restrictScalars_top]
lemma za7 {ι:Type*} (a:ι → ℤ) (s:Finset ι) :
    ∃ b:ℤ, ∏ i ∈ s, (4*a i+1) = 4*b+1:=by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨b,hb⟩:=ih
    refine ⟨4*a i*b+a i+b,?_⟩
    rw [Finset.prod_insert hi,hb]
    ring
end z3y
namespace z34
open NumberField
open scoped BigOperators Classical
universe u v
variable (K:Type u) [Field K] [NumberField K] {ι:Type v} (a:ι → ℤ) (s:Finset ι)
structure Data where
  carrier:Type u
  instField:Field carrier
  instNumberField:NumberField carrier
  instAlgebra:Algebra K carrier
  z59:IsTotallyReal carrier
  roots:ι → carrier
  z3f:∀ i ∈ s, (roots i)^2 = 4*(a i:carrier)+1
  adjoin_roots:Algebra.adjoin K (roots '' (s:Set ι)) = ⊤
  unramified:differentIdeal (𝓞 K) (𝓞 carrier) = ⊤
instance instOMAField13:type_of% @Data.instField:=@Data.instField
instance instOMAField14:type_of% @Data.instNumberField:=@Data.instNumberField
instance instOMAField15:type_of% @Data.instAlgebra:=@Data.instAlgebra
instance instOMAField16:type_of% @Data.z59:=@Data.z59
lemma z3n [IsTotallyReal K]
    (hpos:∀ i ∈ s, 0 < 4*a i+1)
    (hcop:Set.Pairwise (s:Set ι) (fun i j => IsCoprime (4*a i+1) (4*a j+1)))
    (w:K) (hw:w^2 = ∏ i ∈ s, (4*(a i:K)+1)) :
    Nonempty (Data K a s):=by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    refine ⟨{
      carrier:=K
      instField:=inferInstance
      instNumberField:=inferInstance
      instAlgebra:=inferInstance
      z59:=inferInstance
      roots:=fun _ => 0
      z3f:=by simp
      adjoin_roots:=Subsingleton.elim _ _
      unramified:=?_ }⟩
    apply (Ideal.eq_top_iff_one _).mpr
    have hd:=z2n.z50 K K (0:𝓞 K) (Subsingleton.elim _ _) Polynomial.X (by simp)
    simpa using hd
  | @insert j s hjs ih =>
    obtain ⟨b,hb⟩:=z3y.za7 a s
    have hjpos:0 < 4*a j+1:=hpos j (Finset.mem_insert_self _ _)
    have hbpos:0 < 4*b+1:=by
      rw [← hb]
      exact Finset.prod_pos (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
    have hjcop:IsCoprime (4*a j+1) (4*b+1):=by
      rw [← hb]
      apply IsCoprime.prod_right
      intro i hi
      exact hcop (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi) (fun he => hjs (he ▸ hi))
    have hw':w^2 = (4*(a j:K)+1)*(4*(b:K)+1):=by
      rw [Finset.prod_insert hjs] at hw
      have hb':(∏ i ∈ s, (4*(a i:K)+1)) = 4*(b:K)+1:=z2j.prod_cast_aux a s b hb
      rwa [hb'] at hw
    obtain ⟨E⟩:=z9a.z3n K (a j) b w hw' hjpos hbpos hjcop
    let F:=E.carrier
    have hpos':∀ i ∈ s, 0 < 4*a i+1:=fun i hi => hpos i (Finset.mem_insert_of_mem hi)
    have hcop':Set.Pairwise (s:Set ι) (fun i j => IsCoprime (4*a i+1) (4*a j+1)) :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
    have hrem:E.remainder^2 = ∏ i ∈ s, (4*(a i:F)+1):=by
      have hb':(∏ i ∈ s, (4*(a i:F)+1)) = 4*(b:F)+1:=z2j.prod_cast_aux a s b hb
      rw [hb']
      exact E.zb3
    obtain ⟨D⟩:=ih F hpos' hcop' E.remainder hrem
    let L:=D.carrier
    letI:Algebra K L:=Algebra.compHom L (algebraMap K F)
    letI:IsScalarTower K F L:=IsScalarTower.of_algebraMap_eq' rfl
    let roots:ι → L:=fun i => if i=j then algebraMap F L E.root else D.roots i
    have hroots (i:ι) (hi:i ∈ insert j s):(roots i)^2 = 4*(a i:L)+1:=by
      by_cases hij:i=j
      · subst i
        simp only [roots,if_pos rfl,← map_pow,E.z66]
        exact z2j.algebraMap_four_aux (a j)
      · exact (show roots i = D.roots i from if_neg hij) ▸ D.z3f i ((Finset.mem_insert.mp hi).resolve_left hij)
    have hgen:Algebra.adjoin K (roots '' (↑(insert j s):Set ι)) = ⊤:=by
      have hg:=z3y.zl3 K F L {E.root} (D.roots '' (s:Set ι)) E.z46 D.adjoin_roots
      apply top_unique
      rw [← hg]
      apply Algebra.adjoin_mono
      rintro x (hx|hx)
      · obtain ⟨y,hy,rfl⟩:=hx
        have hy':=Set.mem_singleton_iff.mp hy
        subst y
        exact ⟨j,Finset.mem_insert_self _ _,by simp [roots]⟩
      · obtain ⟨i,hi,rfl⟩:=hx
        exact ⟨i,Finset.mem_insert_of_mem hi,by simp [roots,show i ≠ j from fun he => hjs (he ▸ hi)]⟩
    exact ⟨{
      carrier:=L
      instField:=inferInstance
      instNumberField:=inferInstance
      instAlgebra:=inferInstance
      z59:=inferInstance
      roots:=roots
      z3f:=hroots
      adjoin_roots:=hgen
      unramified:=z3y.zhk K F L E.unramified D.unramified }⟩
end z34
namespace z2c
open scoped Classical BigOperators
universe u v
variable (K:Type u) [Field K] {ι:Type v} (a:ι → K) (s:Finset ι)
structure Data where
  carrier:Type u
  instField:Field carrier
  instAlgebra:Algebra K carrier
  instFinite:Module.Finite K carrier
  roots:ι → carrier
  z3f:∀ i ∈ s, (roots i)^2 = algebraMap K carrier (a i)
  adjoin_roots:Algebra.adjoin K (roots '' (s:Set ι)) = ⊤
  degree:Module.finrank K carrier = 2^s.card
  z1f:∀ b:K, IsSquare (algebraMap K carrier b) →
    ∃ t:Finset ι, t ⊆ s ∧ IsSquare (b*∏ i ∈ t, a i)
instance instOMAField17:type_of% @Data.instField:=@Data.instField
instance instOMAField18:type_of% @Data.instAlgebra:=@Data.instAlgebra
instance instOMAField19:type_of% @Data.instFinite:=@Data.instFinite
variable [CharZero K]
lemma z3n
    (hind:∀ t:Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅) :
    Nonempty (Data K a s):=by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{
      carrier:=K
      instField:=inferInstance
      instAlgebra:=inferInstance
      instFinite:=inferInstance
      roots:=fun _ => 0
      z3f:=by simp
      adjoin_roots:=Subsingleton.elim _ _
      degree:=by simp
      z1f:=fun b hb => ⟨∅,by simp,by simpa using hb⟩ }⟩
  | @insert j s hjs ih =>
    have hsind:∀ t:Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅ :=
      fun t ht => hind t (ht.trans (Finset.subset_insert j s))
    obtain ⟨E⟩:=ih hsind
    let F:=E.carrier
    let c:F:=algebraMap K F (a j)
    have hc:¬ IsSquare c:=by
      intro h
      obtain ⟨t,ht,hsq⟩:=E.z1f (a j) h
      have hjt:j ∉ t:=fun hj => hjs (ht hj)
      have he:=hind (insert j t) (Finset.insert_subset_insert j ht)
        (by simpa [Finset.prod_insert hjt] using hsq)
      exact Finset.insert_ne_empty j t he
    letI:Fact (∀ x:F, x^2 ≠ c+0*x):=⟨fun x hx => hc ⟨x,by simpa [pow_two] using hx.symm⟩⟩
    let L:=QuadraticAlgebra F c 0
    letI:CharZero F:=charZero_of_injective_algebraMap (algebraMap K F).injective
    letI:FiniteDimensional K L:=Module.Finite.trans F L
    let root:ι → L:=fun i => if i=j then z18.root F c else algebraMap F L (E.roots i)
    have hroots (i:ι) (hi:i ∈ insert j s):(root i)^2 = algebraMap K L (a i):=by
      by_cases hij:i=j
      · subst i
        simp only [root,if_pos rfl]
        exact z18.z66 F c
      · have his:i ∈ s:=(Finset.mem_insert.mp hi).resolve_left hij
        simp only [root,if_neg hij,← map_pow,E.z3f i his]
        rfl
    have hgen:Algebra.adjoin K (root '' (↑(insert j s):Set ι)) = ⊤:=by
      let S:=Algebra.adjoin K (root '' (↑(insert j s):Set ι))
      let φ:F →ₐ[K] L:=IsScalarTower.toAlgHom K F L
      have hold:Algebra.adjoin K (E.roots '' (s:Set ι)) ≤ S.comap φ:=by
        apply Algebra.adjoin_le
        rintro x ⟨i,hi,rfl⟩
        change algebraMap F L (E.roots i) ∈ S
        have hij:i ≠ j:=fun he => hjs (he ▸ hi)
        have hx:=Algebra.subset_adjoin (R:=K) (Set.mem_image_of_mem root (show i ∈ (↑(insert j s):Set ι) from Finset.mem_insert_of_mem hi))
        simpa only [root,if_neg hij,SetLike.mem_coe] using hx
      have hF (x:F):algebraMap F L x ∈ S:=by
        apply hold
        rw [E.adjoin_roots]
        trivial
      have hr:z18.root F c ∈ S:=by
        have hx:=Algebra.subset_adjoin (R:=K) (Set.mem_image_of_mem root (show j ∈ (↑(insert j s):Set ι) from Finset.mem_insert_self _ _))
        simpa only [root,if_pos rfl,SetLike.mem_coe] using hx
      apply top_unique
      intro z _
      have hz:=S.add_mem (hF z.re) (S.mul_mem (hF z.im) hr)
      have he:algebraMap F L z.re+algebraMap F L z.im*z18.root F c = z:=by
        change QuadraticAlgebra.mk (z.re+(z.im*0+c*0*1)) (0+(z.im*1+0*0+0*0*1)) = z
        ext <;> simp
      simpa only [he] using hz
    refine ⟨{
      carrier:=L
      instField:=inferInstance
      instAlgebra:=inferInstance
      instFinite:=inferInstance
      roots:=root
      z3f:=hroots
      adjoin_roots:=hgen
      degree:=?_
      z1f:=?_ }⟩
    · have he:=Module.finrank_mul_finrank K F L
      rw [QuadraticAlgebra.finrank_eq_two,E.degree] at he
      simpa [Finset.card_insert_of_notMem hjs,pow_succ] using he.symm
    · intro b hb
      have hb':IsSquare (algebraMap F L (algebraMap K F b)):=hb
      rcases z18.zaa F c (algebraMap K F b) hb' with h | h
      · obtain ⟨t,ht,hsq⟩:=E.z1f b h
        exact ⟨t,ht.trans (Finset.subset_insert _ _),hsq⟩
      · have he:IsSquare (algebraMap K F (b*a j)):=by simpa [map_mul,c] using h
        obtain ⟨t,ht,hsq⟩:=E.z1f (b*a j) he
        have hjt:j ∉ t:=fun hj => hjs (ht hj)
        exact ⟨insert j t,Finset.insert_subset_insert j ht,by simpa [Finset.prod_insert hjt,mul_assoc] using hsq⟩
end z2c
namespace z2c
open Polynomial
open scoped Classical BigOperators
universe u v
variable (K:Type u) [Field K] {ι:Type v} (a:ι → K) (s:Finset ι) (E:Data K a s)
noncomputable def polynomial:K[X]:=∏ i ∈ s, (X^2-C (a i))
lemma zhv:(polynomial K a s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C (a i) (by norm_num))
instance splittingField:Polynomial.IsSplittingField K E.carrier (polynomial K a s) where
  splits':=by
    rw [polynomial,Polynomial.map_prod]
    apply Polynomial.Splits.prod
    intro i hi
    simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C]
    have he:(X^2-C (algebraMap K E.carrier (a i)):E.carrier[X]) =
        (X-C (E.roots i))*(X-C (-E.roots i)):=by
      rw [map_neg]
      calc
        X^2-C (algebraMap K E.carrier (a i)) = X^2-C ((E.roots i)^2):=by rw [E.z3f i hi]
        _ = _:=by rw [map_pow]; ring
    rw [he]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  adjoin_rootSet':=by
    apply top_unique
    rw [← E.adjoin_roots]
    apply Algebra.adjoin_mono
    rintro x ⟨i,hi,rfl⟩
    apply (zhv K a s).mem_rootSet.mpr
    rw [polynomial,map_prod]
    apply Finset.prod_eq_zero hi
    simp [E.z3f i hi]
instance [CharZero K]:IsGalois K E.carrier:=by
  letI:Normal K E.carrier:=Normal.of_isSplittingField (polynomial K a s)
  exact {}
end z2c
namespace z2c
open NumberField
open scoped Classical BigOperators
variable {ι:Type*} (a:ι → ℚ) (s:Finset ι) (E:Data ℚ a s)
noncomputable instance:NumberField E.carrier:=NumberField.of_module_finite ℚ E.carrier
end z2c
namespace z3z
open scoped BigOperators Classical
variable {ι:Type*} (p:ι → ℕ) (hp:∀ i, (p i).Prime) (hinj:Function.Injective p)
include hp hinj in
lemma independent (s:Finset ι) (hs:IsSquare (∏ i ∈ s, (p i:ℚ))):s = ∅:=by
  have hsq:IsSquare (∏ i ∈ s, p i):=by
    apply Rat.isSquare_natCast_iff.mp
    simpa using hs
  have hfree:Squarefree (∏ i ∈ s, p i):=by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Nat.coprime_iff_isRelPrime.mp ((hp i).coprime_iff_not_dvd.mpr (by
        intro h
        exact hij (hinj ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp h)))))
    · intro i hi
      exact (hp i).squarefree
  obtain ⟨x,hx⟩:=hsq
  have hunit:IsUnit x:=hfree x (by rw [hx])
  have hx1:x = 1:=Nat.isUnit_iff.mp hunit
  have hprod:∏ i ∈ s, p i = 1:=by simpa [hx1] using hx
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hd:=Finset.dvd_prod_of_mem p hi
  rw [hprod] at hd
  exact (hp i).not_dvd_one hd
end z3z
namespace z19
open scoped Classical BigOperators
set_option maxRecDepth 100000 in
def p:Fin 256 → ℕ:=![5,13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,197,229,233,241,257,269,277,281,293,313,317,337,349,353,373,389,397,401,409,421,433,449,457,461,509,521,541,557,569,577,593,601,613,617,641,653,661,673,677,701,709,733,757,761,769,773,797,809,821,829,853,857,877,881,929,937,941,953,977,997,1009,1013,1021,1033,1049,1061,1069,1093,1097,1109,1117,1129,1153,1181,1193,1201,1213,1217,1229,1237,1249,1277,1289,1297,1301,1321,1361,1373,1381,1409,1429,1433,1453,1481,1489,1493,1549,1553,1597,1601,1609,1613,1621,1637,1657,1669,1693,1697,1709,1721,1733,1741,1753,1777,1789,1801,1861,1873,1877,1889,1901,1913,1933,1949,1973,1993,1997,2017,2029,2053,2069,2081,2089,2113,2129,2137,2141,2153,2161,2213,2221,2237,2269,2273,2281,2293,2297,2309,2333,2341,2357,2377,2381,2389,2393,2417,2437,2441,2473,2477,2521,2549,2557,2593,2609,2617,2621,2633,2657,2677,2689,2693,2713,2729,2741,2749,2753,2777,2789,2797,2801,2833,2837,2857,2861,2897,2909,2917,2953,2957,2969,3001,3037,3041,3049,3061,3089,3109,3121,3137,3169,3181,3209,3217,3221,3229,3253,3257,3301,3313,3329,3361,3373,3389,3413,3433,3449,3457,3461,3469,3517,3529,3533,3541,3557,3581,3593,3613,3617,3637,3673,3677,3697,3701,3709,3733]
def a (i:Fin 256):ℤ:=(p i / 4:ℕ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma properties (i:Fin 256):(p i).Prime ∧ p i % 4 = 1 ∧ p i ≤ 2^14:=by
  fin_cases i <;> norm_num [p]
lemma prime (i:Fin 256):(p i).Prime:=(properties i).1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma injective:Function.Injective p:=by decide
lemma p_eq (i:Fin 256):(p i:ℤ) = 4*a i+1:=by
  have h:=Nat.mod_add_div (p i) 4
  rw [(properties i).2.1] at h
  dsimp only [a]
  exact_mod_cast (by omega:p i = 4*(p i/4)+1)
def rest:Finset (Fin 256):=Finset.univ.erase 0
noncomputable def D:ℕ:=∏ i ∈ rest, p i
lemma D_pos:0 < D:=Finset.prod_pos (fun i _ => (prime i).pos)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma prod_eq:∏ i:Fin 256, p i = 5*D:=by
  have he:=Finset.mul_prod_erase Finset.univ p (show (0:Fin 256) ∈ Finset.univ by simp)
  simpa only [D,rest,show p 0 = 5 from rfl] using he.symm
lemma pos (i:Fin 256):0 < 4*a i+1:=by rw [← p_eq]; exact_mod_cast (prime i).pos
lemma coprime:Set.Pairwise (Set.univ:Set (Fin 256)) (fun i j => IsCoprime (4*a i+1) (4*a j+1)):=by
  intro i _ j _ hij
  rw [← p_eq,← p_eq]
  apply Nat.isCoprime_iff_coprime.mpr
  apply (prime i).coprime_iff_not_dvd.mpr
  intro h
  exact hij (injective ((Nat.prime_dvd_prime_iff_eq (prime i) (prime j)).mp h))
lemma znt:D ≤ (2^14)^255:=by
  have h:=Finset.prod_le_prod (s:=rest) (f:=p) (g:=fun _ => 2^14)
    (fun i _ => Nat.zero_le _) (fun i _ => (properties i).2.2)
  simpa only [D,Finset.prod_const,rest,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin,Nat.reduceSub] using h
end z19
namespace z19
open scoped Classical BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma zjt:¬ IsSquare (5:ℚ):=by
  intro h
  have he:=z3z.independent p prime injective ({0}:Finset (Fin 256)) (by simpa [p] using h)
  simp at he
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma zm2:¬ IsSquare (D:ℚ):=by
  intro h
  have he:=z3z.independent p prime injective rest (by simpa [D] using h)
  have hm:(1:Fin 256) ∈ rest:=by simp [rest]
  rw [he] at hm
  exact Finset.notMem_empty _ hm
lemma zhr:¬ IsSquare (5*(D:ℚ)):=by
  intro h
  have hp:(∏ i:Fin 256, (p i:ℚ)) = 5*(D:ℚ):=by exact_mod_cast prod_eq
  have he:=z3z.independent p prime injective Finset.univ (hp ▸ h)
  have hm:(0:Fin 256) ∈ (Finset.univ:Finset (Fin 256)):=Finset.mem_univ _
  rw [he] at hm
  exact Finset.notMem_empty _ hm
end z19
namespace z19
open scoped Classical
lemma zo1:∃ a₀:ℤ, (D:ℤ) = 4*a₀+1:=by
  obtain ⟨b,hb⟩:=z3y.za7 a rest
  refine ⟨b,?_⟩
  dsimp only [D]
  push_cast
  simpa only [← p_eq] using hb
end z19
namespace z2r
open Polynomial
open scoped Classical BigOperators
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
  {ι:Type*} (a:ι → K) (s:Finset ι) (roots:ι → L)
noncomputable def polynomial:K[X]:=∏ i ∈ s, (X^2-C (a i))
omit [Field L] [Algebra K L] in
lemma monic:(polynomial K a s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C (a i) (by norm_num))
lemma splits (hroots:∀ i ∈ s, (roots i)^2 = algebraMap K L (a i)) :
    ((polynomial K a s).map (algebraMap K L)).Splits:=by
  rw [polynomial,Polynomial.map_prod]
  apply Polynomial.Splits.prod
  intro i hi
  simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C]
  have he:(X^2-C (algebraMap K L (a i)):L[X]) = (X-C (roots i))*(X-C (-roots i)):=by
    rw [map_neg]
    calc
      X^2-C (algebraMap K L (a i)) = X^2-C ((roots i)^2):=by rw [hroots i hi]
      _ = _:=by rw [map_pow]; ring
  rw [he]
  exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
lemma zao (hroots:∀ i ∈ s, (roots i)^2 = algebraMap K L (a i))
    (hgen:Algebra.adjoin K (roots '' (s:Set ι)) = ⊤) :
    Polynomial.IsSplittingField K L (polynomial K a s) where
  splits':=splits K L a s roots hroots
  adjoin_rootSet':=by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    rintro x ⟨i,hi,rfl⟩
    apply (monic K a s).mem_rootSet.mpr
    rw [polynomial,map_prod]
    apply Finset.prod_eq_zero hi
    simp [hroots i hi]
lemma isGalois [CharZero K] (hroots:∀ i ∈ s, (roots i)^2 = algebraMap K L (a i))
    (hgen:Algebra.adjoin K (roots '' (s:Set ι)) = ⊤):IsGalois K L:=by
  letI:Polynomial.IsSplittingField K L (polynomial K a s):=zao K L a s roots hroots hgen
  letI:Normal K L:=Normal.of_isSplittingField (polynomial K a s)
  exact {}
end z2r
namespace z96
open scoped Classical BigOperators
variable (K L:Type*) [Field K] [Field L] [CharZero K] [Algebra K L] [FiniteDimensional K L]
  {ι:Type*} (a:ι → K) (s:Finset ι)
lemma zn3 (hind:∀ t:Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅)
    (roots:ι → L) (hroots:∀ i ∈ s, (roots i)^2 = algebraMap K L (a i)) :
    2^s.card ≤ Module.finrank K L:=by
  obtain ⟨E⟩:=z2c.z3n K a s hind
  letI:Polynomial.IsSplittingField K E.carrier (z2r.polynomial K a s) :=
    z2r.zao K E.carrier a s E.roots E.z3f E.adjoin_roots
  let φ:E.carrier →ₐ[K] L:=Polynomial.IsSplittingField.lift E.carrier
    (z2r.polynomial K a s) (z2r.splits K L a s roots hroots)
  rw [← E.degree]
  exact LinearMap.finrank_le_finrank_of_injective (f:=φ.toLinearMap) φ.toRingHom.injective
end z96
namespace zbt
open scoped Classical
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
lemma zkd (S:Set L) (hgen:Algebra.adjoin K S = ⊤)
    (hS:∀ x ∈ S, ∃ a:K, x^2 = algebraMap K L a) (σ:Gal(L/K)):σ^2 = 1:=by
  apply AlgEquiv.coe_algHom_injective
  apply AlgHom.ext_of_adjoin_eq_top hgen
  intro x hx
  obtain ⟨a,ha⟩:=hS x hx
  have hs:(σ x)^2 = x^2:=by
    rw [← map_pow,ha,σ.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · change σ (σ x) = x
    rw [h,h]
  · change σ (σ x) = x
    rw [h,map_neg,h,neg_neg]
end zbt
namespace z7g
open CategoryTheory
open scoped Classical
variable (G:Type) [Group G] [Finite G]
omit [Finite G] in
lemma zn9 (hs:∀ g:G, g^2 = 1) (g h:G):g*h = h*g:=by
  have hinv (x:G):x⁻¹ = x:=inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs x)
  calc
    g*h = (g*h)⁻¹:=(hinv _).symm
    _ = h⁻¹*g⁻¹:=mul_inv_rev _ _
    _ = h*g:=by rw [hinv,hinv]
lemma zjy (hs:∀ g:G, g^2 = 1) :
    Nat.card G = 2^(Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) G (ZMod 2)) 1)):=by
  letI:CommGroup G:={ ‹Group G› with mul_comm:=zn9 G hs }
  letI:Module (ZMod 2) (Additive G):=AddCommGroup.zmodModule (n:=2)
    (fun x => show x.toMul^2 = 1 from hs x.toMul)
  let e:(Additive G →+ ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive G):={
    toFun:=fun f => f.toZModLinearMap 2
    invFun:=fun f => f.toAddMonoidHom
    left_inv:=fun f => rfl
    right_inv:=fun f => rfl
    map_add':=fun f g => rfl
    map_smul':=fun r f => rfl }
  have he:=(groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod 2) G (ZMod 2))).toLinearEquiv.finrank_eq
  rw [he,e.finrank_eq,Subspace.dual_finrank_eq]
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive G)
  rw [Nat.card_zmod] at hc
  exact hc
end z7g
namespace z34
open NumberField
open scoped Classical
variable (K:Type*) [Field K] [NumberField K] {ι:Type*} (a:ι → ℤ) (s:Finset ι) (E:Data K a s)
lemma zo2 (σ:Gal(E.carrier/K)):σ^2 = 1:=by
  apply zbt.zkd K E.carrier (E.roots '' (s:Set ι)) E.adjoin_roots ?_ σ
  rintro x ⟨i,hi,rfl⟩
  refine ⟨4*(a i:K)+1,?_⟩
  simpa only [map_add,map_mul,map_ofNat,map_intCast,map_one] using E.z3f i hi
end z34
namespace z27
open NumberField CategoryTheory
open scoped Classical BigOperators
structure Data where
  B:Type
  zll:Field B
  zav:NumberField B
  realB:IsTotallyReal B
  z5y:B
  zh7:z5y^2 = 5
  zjv:Module.finrank ℚ B = 4
  oddB:IsCoprime (NumberField.discr B) (2:ℤ)
  znj:16*(NumberField.discr B).natAbs ≤ 2^14294
  L:Type
  zl1:Field L
  zaq:NumberField L
  realL:IsTotallyReal L
  algebra:Algebra B L
  galois:IsGalois B L
  unramified:differentIdeal (𝓞 B) (𝓞 L) = ⊤
  elementary:∀ σ:Gal(L/B), σ^2 = 1
  z30:254 ≤ Module.finrank (ZMod 2)
    (groupCohomology (Rep.trivial (ZMod 2) Gal(L/B) (ZMod 2)) 1)
instance instOMAField20:type_of% @Data.zll:=@Data.zll
instance instOMAField21:type_of% @Data.zav:=@Data.zav
instance instOMAField22:type_of% @Data.realB:=@Data.realB
instance instOMAField23:type_of% @Data.zl1:=@Data.zl1
instance instOMAField24:type_of% @Data.zaq:=@Data.zaq
instance instOMAField25:type_of% @Data.realL:=@Data.realL
instance instOMAField26:type_of% @Data.algebra:=@Data.algebra
instance instOMAField27:type_of% @Data.galois:=@Data.galois
set_option maxHeartbeats 4000000 in
lemma z3n:Nonempty Data:=by
  obtain ⟨a₀,ha₀⟩:=z19.zo1
  obtain ⟨E⟩:=z2j.z3n z19.D z19.D_pos a₀ ha₀
    z19.zjt z19.zm2 z19.zhr
  let B:=E.B
  let w:B:=E.z5y*E.sqrtD
  have hw:w^2 = ∏ i:Fin 256, (4*(z19.a i:B)+1):=by
    have hp:(∏ i:Fin 256, (4*(z19.a i:B)+1)) = 5*(z19.D:B):=by
      have hz:(∏ i:Fin 256, (4*z19.a i+1)) = (5*z19.D:ℕ):=by
        simp_rw [← z19.p_eq]
        exact_mod_cast z19.prod_eq
      exact z2j.prod_cast_nat_aux _ _ _ hz
    rw [hp]
    dsimp only [w]
    rw [mul_pow,E.zjk,E.D_sq]
  obtain ⟨U⟩:=z34.z3n B z19.a Finset.univ
    (fun i _ => z19.pos i) (by simpa using z19.coprime) w hw
  let L:=U.carrier
  let aB:Fin 256 → B:=fun i => 4*(z19.a i:B)+1
  have hrootsB (i:Fin 256) (hi:i ∈ (Finset.univ:Finset (Fin 256))) :
      (U.roots i)^2 = algebraMap B L (aB i):=by
    rw [show aB i = 4*(z19.a i:B)+1 from rfl,z2j.algebraMap_four_aux]
    exact U.z3f i hi
  letI:IsGalois B L:=z2r.isGalois B L aB Finset.univ U.roots hrootsB U.adjoin_roots
  have hexp:∀ σ:Gal(L/B), σ^2 = 1:=z34.zo2 B z19.a Finset.univ U
  have hrootsQ (i:Fin 256) (hi:i ∈ (Finset.univ:Finset (Fin 256))) :
      (U.roots i)^2 = algebraMap ℚ L (z19.p i:ℚ):=by
    have hp:(z19.p i:L) = 4*(z19.a i:L)+1 :=
      z2j.natCast_eq_aux _ _ (z19.p_eq i)
    simpa only [map_natCast,Rat.cast_natCast,hp] using U.z3f i hi
  have hdegreeL:2^256 ≤ Module.finrank ℚ L:=by
    have hd:=z96.zn3 ℚ L (fun i => (z19.p i:ℚ)) Finset.univ
      (fun t _ ht => z3z.independent z19.p z19.prime z19.injective t ht)
      U.roots hrootsQ
    simpa using hd
  have hdegreeBL:2^254 ≤ Module.finrank B L:=by
    have hd:=Module.finrank_mul_finrank ℚ B L
    rw [E.degree] at hd
    norm_num1 at hdegreeL ⊢
    omega
  have hH1:254 ≤ Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(L/B) (ZMod 2)) 1):=by
    have hc:=z7g.zjy Gal(L/B) hexp
    rw [IsGalois.card_aut_eq_finrank] at hc
    apply (Nat.pow_le_pow_iff_right (by norm_num:1 < 2)).mp
    simpa only [← hc] using hdegreeBL
  have hdisc:16*(NumberField.discr B).natAbs ≤ 2^14294:=by
    calc
      _ ≤ 16*(625*z19.D^4):=Nat.mul_le_mul_left 16 E.z8q
      _ ≤ 2^14*((2^14)^255)^4:=by
        have hp:=Nat.pow_le_pow_left z19.znt 4
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul (by norm_num:16*625 ≤ 2^14) hp
      _ = _:=by
        rw [← pow_mul,← pow_mul,← pow_add]
  exact ⟨{
    B:=B
    zll:=inferInstance
    zav:=inferInstance
    realB:=inferInstance
    z5y:=E.z5y
    zh7:=E.zjk
    zjv:=E.degree
    oddB:=E.odd
    znj:=hdisc
    L:=L
    zl1:=inferInstance
    zaq:=inferInstance
    realL:=inferInstance
    algebra:=inferInstance
    galois:=inferInstance
    unramified:=U.unramified
    elementary:=hexp
    z30:=hH1 }⟩
end z27
namespace z27
noncomputable def Data.layer (E:Data):z21.Layer E.B 254 where
  carrier:=E.L
  field:=inferInstance
  numberField:=inferInstance
  real:=inferInstance
  algebra:=inferInstance
  galois:=inferInstance
  zcw:=fun σ => ⟨1,by simpa only [pow_one] using E.elementary σ⟩
  unramified:=E.unramified
  z30:=E.z30
end z27
namespace OMA1207
open NumberField z7
open Filter
open scoped Classical
lemma z6l (E:z27.Data) :
    ∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ)^(1-c):=by
  have hclass:=z4i.zls E.B E.zjv 14294 E.znj
  have hnum:4*(Module.finrank (ZMod 2) (z6.V (C E.B))+2*Module.finrank ℚ E.B) ≤ 254^2:=by
    rw [E.zjv]
    omega
  obtain ⟨M,hM⟩:=z21.zgz E.B 254 E.oddB ⟨E.layer⟩ (by norm_num) hnum
  exact z4s E.B E.z5y E.zh7
    (fun n => (M n).carrier) (fun n => (M n).zcw) hM (fun n => (M n).unramified)
end OMA1207
namespace OMA1207
lemma erdos_1207 :
    (∃ c > (0:ℝ), ∀ᶠ n:ℕ in atTop, (P 2 n:ℝ) < (n:ℝ) ^ (1 - c)):=by
  exact z6l (Classical.choice z27.z3n)
end OMA1207

theorem OMA.solution : type_of% @Erdos1207.erdos_1207 := OMA1207.erdos_1207
