import OMAReductions.R_Green3_green_3_R2_H1_R1
import Mathlib
/-! Franchi, Gowers and Yip, Product-free subsets of (0,1), Section 4.
We specialize the sumset estimate to the symmetric difference set of a
truncated prefix, and use disjoint translates in the final contradiction. -/
open Set MeasureTheory
open scoped Pointwise
namespace OMA.R_Green3_green_3_R2_H1_R1_H3_R1

lemma clip {S : Set ℝ} (hs : ∃ s : Finset (ℝ×ℝ), S=⋃p∈s,Icc p.1 p.2) (l r : ℝ) :
    ∃ t : Finset (ℝ×ℝ), S∩Icc l r=⋃p∈t,Icc p.1 p.2 := by
  classical
  obtain ⟨s,rfl⟩ := hs
  refine ⟨s.image (fun p => (max p.1 l,min p.2 r)),?_⟩
  rw [Finset.set_biUnion_finset_image]
  ext z
  simp only [mem_inter_iff,mem_iUnion,mem_Icc, max_le_iff,le_min_iff]
  grind

lemma reflect {S : Set ℝ} (hs : ∃ s : Finset (ℝ×ℝ), S=⋃p∈s,Icc p.1 p.2) :
    ∃ t : Finset (ℝ×ℝ), -S=⋃p∈t,Icc p.1 p.2 := by
  classical
  obtain ⟨s,rfl⟩ := hs
  refine ⟨s.image (fun p => (-p.2,-p.1)),?_⟩
  rw [Finset.set_biUnion_finset_image]
  ext z
  simp only [mem_neg,mem_iUnion,mem_Icc]
  grind

lemma compactOf {S : Set ℝ} (hs : ∃ s : Finset (ℝ×ℝ), S=⋃p∈s,Icc p.1 p.2) : IsCompact S := by
  obtain ⟨s,rfl⟩ := hs
  exact s.finite_toSet.isCompact_biUnion fun _ _ => isCompact_Icc

lemma intervalFinite (a b : ℝ) : volume (Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

lemma negMass (S : Set ℝ) : volume.real (-S)=volume.real S := by
  simp [measureReal_def,Measure.measure_neg]

lemma reflectDisc (S : Set ℝ) : let d (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
    d (-S)=d S := by
  let vals (S : Set ℝ) := {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  have sub (T : Set ℝ) : vals (-T) ⊆ vals T := by
    rintro z ⟨a,b,ab,rfl⟩
    have e : (-T)∩Icc a b = -(T∩Icc (-b) (-a)) := by
      ext x; simp only [mem_neg,mem_inter_iff,mem_Icc]; grind
    refine ⟨-b,-a,neg_le_neg ab,?_⟩
    rw [e,negMass]; ring
  apply congrArg sSup
  exact Set.Subset.antisymm (sub S) (by simpa [vals] using sub (-S))

lemma discMono {S T : Set ℝ} (sub : S⊆T) (ct : IsCompact T) :
    let d (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
    d S≤d T := by
  let vals (S : Set ℝ) := {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  have ne : (vals S).Nonempty := ⟨_,0,0,le_rfl,rfl⟩
  have bdd : BddAbove (vals T) := by
    refine ⟨2*volume.real T,?_⟩
    rintro z ⟨a,b,ab,rfl⟩
    have m := measureReal_mono (s₁:=T∩Icc a b) inter_subset_left ct.measure_lt_top.ne (μ:=volume)
    linarith
  apply csSup_le ne
  rintro z ⟨a,b,ab,rfl⟩
  have m := measureReal_mono (inter_subset_inter_left (Icc a b) sub)
    ((measure_mono (inter_subset_left (t:=Icc a b) (s:=T))).trans_lt ct.measure_lt_top).ne (μ:=volume)
  have upper := le_csSup bdd (show 2*volume.real (T∩Icc a b)-(b-a)∈vals T from ⟨a,b,ab,rfl⟩)
  change _ ≤ sSup (vals T)
  linarith

lemma firstMass (sumset : OMA.R_Green3_green_3_R2_H1_R1.H1)
    {A : Set ℝ} (fin : ∃ s : Finset (ℝ×ℝ), A=⋃p∈s,Icc p.1 p.2) (least : IsLeast A 1)
    (sf : ∀ a∈A,∀ b∈A,a+b∉A) (x : ℝ) (hx : 1≤x) :
    let F (u : ℝ):=volume.real (A∩Icc 0 u)
    let d (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
    F (x-1)+2*F x ≤ x-1+d (A∩Icc 0 (x+1)) := by
  classical
  let C:=A∩Icc 0 x
  let D:=C+(-C)
  let P:=D∩Ici 0
  let N:=D∩Iic 0
  let L:=A∩Icc 0 (x-1)
  let d (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  have fc := clip fin 0 x
  have cc : IsCompact C := compactOf fc
  have cd : IsCompact D := cc.add cc.neg
  have cp : IsCompact P := cd.inter_right isClosed_Ici
  have cn : IsCompact N := cd.inter_right isClosed_Iic
  have cl : IsCompact L := compactOf (clip fin 0 (x-1))
  have nc : C.Nonempty := ⟨1,least.1,by norm_num,hx⟩
  have nn : (-C).Nonempty := ⟨-1,by simpa [C] using (show (1:ℝ)∈C from ⟨least.1,by norm_num,hx⟩)⟩
  have flip := reflectDisc C
  have bm := sumset C (-C) fc (reflect fc) nc nn flip.symm
  change 2*volume.real C+2*volume.real (-C)-d C-d (-C)≤volume.real D at bm
  change d (-C)=d C at flip
  rw [negMass,flip] at bm
  have symm (z : ℝ) (h : z∈D) : -z∈D := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Set.mem_add.mp h
    exact Set.mem_add.mpr ⟨-b,hb,-a,by simpa using ha,by ring⟩
  have nv : N = -P := by
    ext z; change (z∈D ∧ z≤0) ↔ (-z∈D ∧ 0≤ -z)
    constructor
    · intro h; exact ⟨symm z h.1,by linarith [h.2]⟩
    · intro h; exact ⟨by simpa using symm _ h.1,by linarith [h.2]⟩
  have dp : volume.real D≤2*volume.real P := by
    have e : D=P∪N := by ext z; change z∈D ↔ (z∈D ∧ 0≤z) ∨ (z∈D ∧ z≤0); grind
    calc volume.real D = volume.real (P∪N) := congrArg volume.real e
      _ ≤ volume.real P+volume.real N := measureReal_union_le _ _
      _ = 2*volume.real P := by rw [nv,negMass]; ring
  have dis : Disjoint P L := by
    apply Set.disjoint_left.mpr
    intro z hz hl
    obtain ⟨a,ha,b,hb,eq⟩ := Set.mem_add.mp hz.1
    exact sf z hl.1 (-b) hb.1 (by convert ha.1 using 1 <;> linarith)
  have inI : P∪L ⊆ Icc 0 (x-1) := by
    rintro z (hz|hz)
    · obtain ⟨a,ha,b,hb,eq⟩ := Set.mem_add.mp hz.1
      exact ⟨hz.2,by linarith [least.2 hb.1,ha.2.2]⟩
    · exact hz.2
  have pack := measureReal_mono inI (intervalFinite _ _) (μ:=volume)
  rw [measureReal_union dis cl.measurableSet cp.measure_lt_top.ne cl.measure_lt_top.ne,
      Real.volume_real_Icc_of_le (by linarith)] at pack
  have mono := discMono (S:=C) (T:=A∩Icc 0 (x+1))
    (fun z h => ⟨h.1,h.2.1,by linarith [h.2.2]⟩) (compactOf (clip fin _ _))
  change d C≤d (A∩Icc 0 (x+1)) at mono
  change volume.real L+2*volume.real C≤x-1+d (A∩Icc 0 (x+1))
  linarith only [bm,dp,pack,mono]

lemma prefixDiff {A : Set ℝ} (ca : IsCompact A) (least : IsLeast A 1) {l r : ℝ} (lr : l≤r) :
    volume.real (A∩Icc 0 r)-volume.real (A∩Icc 0 l)=volume.real (A∩Icc l r) := by
  have e : A∩Icc 0 r=(A∩Icc 0 l)∪(A∩Ioc l r) := by
    ext z; simp only [mem_inter_iff,mem_union,mem_Icc,mem_Ioc]
    constructor
    · rintro ⟨h,lo,hi⟩; rcases le_or_gt z l with le|gt
      · exact Or.inl ⟨h,lo,le⟩
      · exact Or.inr ⟨h,gt,hi⟩
    · rintro (⟨h,lo,hi⟩|⟨h,lo,hi⟩)
      · exact ⟨h,lo,hi.trans lr⟩
      · exact ⟨h,by linarith [least.2 h],hi⟩
  have dis : Disjoint (A∩Icc 0 l) (A∩Ioc l r) :=
    Set.disjoint_left.mpr fun _ h k => k.2.1.not_ge h.2.2
  have f {T : Set ℝ} : volume (A∩T)≠⊤ := ((measure_mono inter_subset_left).trans_lt ca.measure_lt_top).ne
  rw [e,measureReal_union dis (ca.measurableSet.inter measurableSet_Ioc) f f]
  have same : volume.real (A∩Ioc l r)=volume.real (A∩Icc l r) :=
    measureReal_congr (ae_eq_set_inter .rfl Ioc_ae_eq_Icc)
  linarith

lemma prefixLe {A : Set ℝ} (ca : IsCompact A) (least : IsLeast A 1) {l r : ℝ} (lr : l≤r) :
    let F (u : ℝ):=volume.real (A∩Icc 0 u)
    0≤F r-F l ∧ F r-F l≤r-l := by
  dsimp only
  rw [prefixDiff ca least lr]
  refine ⟨measureReal_nonneg,?_⟩
  exact (measureReal_mono inter_subset_right (intervalFinite l r)).trans (Real.volume_real_Icc_of_le lr).le

lemma translatePack {A : Set ℝ} (ca : IsCompact A) (least : IsLeast A 1)
    (sf : ∀ a∈A,∀ b∈A,a+b∉A) {l r k u v : ℝ} (hk : k∈A)
    (lr : l≤r) (uv : u≤v) (lo : u≤l+k) (hi : r+k≤v) :
    let F (z : ℝ):=volume.real (A∩Icc 0 z)
    F r-F l+(F v-F u)≤v-u := by
  let T:=(fun z : ℝ => z+(-k)) ⁻¹' (A∩Icc l r)
  let U:=A∩Icc u v
  have vol : volume.real T=volume.real (A∩Icc l r) := by
    dsimp only [T,measureReal_def]; rw [measure_preimage_add_right]
  have td : Disjoint T U := by
    apply Set.disjoint_left.mpr
    intro z ht hu
    exact sf (z+(-k)) ht.1 k hk (by simpa using hu.1)
  have bound : T∪U⊆Icc u v := by
    rintro z (h|h)
    · exact ⟨by linarith [h.2.1],by linarith [h.2.2]⟩
    · exact h.2
  have h := measureReal_mono bound (intervalFinite _ _) (μ:=volume)
  have ft : volume T≠⊤ := ((measure_mono ((subset_union_left : T⊆T∪U).trans bound)).trans_lt
    (lt_top_iff_ne_top.mpr (intervalFinite u v))).ne
  have cu : IsCompact U := ca.inter_right isClosed_Icc
  rw [measureReal_union td cu.measurableSet ft cu.measure_lt_top.ne,vol,Real.volume_real_Icc_of_le uv] at h
  dsimp only; rw [prefixDiff ca least lr,prefixDiff ca least uv]; exact h

lemma prefixGap {A : Set ℝ} (ca : IsCompact A) (least : IsLeast A 1) {l r : ℝ} (lr : l≤r)
    (gap : Disjoint A (Ioo l r)) : volume.real (A∩Icc 0 r)=volume.real (A∩Icc 0 l) := by
  have zero : volume.real (A∩Icc l r)=0 := by
    have e := measureReal_congr (μ:=volume) (ae_eq_set_inter (s:=A) .rfl (Ioo_ae_eq_Icc (a:=l) (b:=r)))
    rw [gap.inter_eq] at e
    simpa using e.symm
  linarith only [prefixDiff ca least lr,zero]

/-- FGY Sections 4.4–4.8. Locate a short maximizing interval in the strip
3 < y < 3+s, obtain (3), and find the last occupied point of [a-2,a-1].
The gap for any maximizing interval is supplied by the proved first-gap estimate. -/
def H1 : Prop :=
  ∀ (A : Set ℝ), (∃ s : Finset (ℝ×ℝ), A=⋃p∈s,Icc p.1 p.2) → IsLeast A 1 →
    (∀ a∈A,∀ b∈A,a+b∉A) → ∀ x ε : ℝ, 1≤x → 0<ε →
    let F (z : ℝ):=volume.real (A∩Icc 0 z)
    let d (S : Set ℝ):=sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
    let t:=d (A∩Icc 0 (x+1))
    (∀ z∈Icc (x-ε) (x+ε),z<F (z-1)+F z+F (z+1)) →
    Icc (x-1-ε) (x-1+ε)⊆A → Icc (x+1-ε) (x+1+ε)⊆A →
    1-t<F (x+1)-F x →
    (∀ a b : ℝ, a≤b → 2*(F b-F a)-(b-a)=t → Disjoint A (Icc (x-a) (x+1-b))) →
    ∃ a b w : ℝ, a∈A ∧ b∈A ∧ 2<a ∧ a≤b ∧
      0<t ∧ t≤b-a ∧ b-a<1 ∧ 2*(F b-F a)-(b-a)=t ∧
      3<x+1-a ∧ x+1-a<3+(b-a) ∧
      2*(F (x-1)-F (x+1-a))+F (a-2)≤a-2+t ∧
      0≤w ∧ w≤1 ∧ a-2+w∈A ∧ Disjoint A (Ioo (a-2+w) (a-1))

/-- FGY Sections 4.9–4.11. The terminal gaps give either the packing estimate
on [1,2], or the shorter packing estimate ending at v-y+2. In the latter
case u and v are separated by a gap of length at least one. -/
def H2 : Prop :=
  ∀ (A : Set ℝ), (∃ s : Finset (ℝ×ℝ), A=⋃p∈s,Icc p.1 p.2) → IsLeast A 1 →
    (∀ a∈A,∀ b∈A,a+b∉A) → ∀ x ε : ℝ, 1≤x → 0<ε →
    let F (z : ℝ):=volume.real (A∩Icc 0 z)
    let d (S : Set ℝ):=sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
    let t:=d (A∩Icc 0 (x+1))
    (∀ z∈Icc (x-ε) (x+ε),z<F (z-1)+F z+F (z+1)) →
    Icc (x-1-ε) (x-1+ε)⊆A → Icc (x+1-ε) (x+1+ε)⊆A →
    1-t<F (x+1)-F x →
    ∀ a b w : ℝ, (a∈A ∧ b∈A ∧ 2<a ∧ a≤b ∧
      0<t ∧ t≤b-a ∧ b-a<1 ∧ 2*(F b-F a)-(b-a)=t ∧
      3<x+1-a ∧ x+1-a<3+(b-a) ∧
      2*(F (x-1)-F (x+1-a))+F (a-2)≤a-2+t ∧
      0≤w ∧ w≤1 ∧ a-2+w∈A ∧ Disjoint A (Ioo (a-2+w) (a-1))) →
    F a-F (a-2)≤1-F (2-w) →
    let y:=x+1-a
    (b+1≤x ∧ Disjoint A (Ioo (b+1) x)) ∧
      ((F y=F 2 ∧ F (x+1)-F (x-1)+F 2≤1) ∨
       (∃ u v : ℝ, u≤v-1 ∧ F u=F 2 ∧ F v=F 2 ∧
        F (x+1)-F (x-1)+F (v-y+2)+2*(F y-F v)≤1))
theorem main : H1 → H2 → OMA.R_Green3_green_3_R2_H1_R1.H3 := by
  intro locate terminal sumset A fin least sf x ε x1 ep crit left right
  let F (z : ℝ):=volume.real (A∩Icc 0 z)
  let d (S : Set ℝ):=sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  let t:=d (A∩Icc 0 (x+1))
  have ca := compactOf fin
  have bad := crit x (show x∈Icc (x-ε) (x+ε) from ⟨by linarith,by linarith⟩)
  change x<F (x-1)+F x+F (x+1) at bad
  have mass := firstMass sumset fin least sf x x1
  change F (x-1)+2*F x≤x-1+t at mass
  have gain : 1-t<F (x+1)-F x := by linarith
  have gap (a b : ℝ) (ab : a≤b) (hit : 2*(F b-F a)-(b-a)=t) :
      Disjoint A (Icc (x-a) (x+1-b)) := by
    apply Set.disjoint_left.mpr
    intro k hk h
    have p := translatePack ca least sf hk ab (show x≤x+1 by linarith)
      (by linarith [h.1]) (by linarith [h.2])
    change F b-F a+(F (x+1)-F x)≤x+1-x at p
    have upper := (prefixLe ca least ab).2
    change F b-F a≤b-a at upper
    linarith
  obtain ⟨a,b,w,hs⟩ := locate A fin least sf x ε x1 ep crit left right gain gap
  obtain ⟨ha,hb,a2,ab,tp,ts,sl,hit,y3,ys,three,w0,w1,hw,wgap⟩ := hs
  change t≤b-a at ts
  change 2*(F b-F a)-(b-a)=t at hit
  change 2*(F (x-1)-F (x+1-a))+F (a-2)≤a-2+t at three
  have lone : F 1=0 := by
    have sub : A∩Icc (0:ℝ) 1⊆Icc 1 1 := fun z h => ⟨least.2 h.1,h.2.2⟩
    apply le_antisymm _ measureReal_nonneg
    exact (measureReal_mono sub (intervalFinite 1 1)).trans (by rw [Real.volume_real_Icc_of_le le_rfl]; norm_num)
  have plusOne := translatePack ca least sf least.1 (show a-2≤a-2+w by linarith)
    (show a-1≤a-1+w by linarith) (by linarith) (by linarith)
  have plusW := translatePack ca least sf hw (show 1≤2-w by linarith)
    (show a-1+w≤a by linarith) (by linarith) (by linarith)
  change F (a-2+w)-F (a-2)+(F (a-1+w)-F (a-1))≤_ at plusOne
  change F (2-w)-F 1+(F a-F (a-1+w))≤_ at plusW
  have noMass : F (a-1)=F (a-2+w) := prefixGap ca least (by linarith) wgap
  have nine : F a-F (a-2)≤1-F (2-w) := by linarith only [plusOne,plusW,noMass,lone]
  obtain ⟨⟨bx,endgap⟩,cases⟩ := terminal A fin least sf x ε x1 ep crit left right gain a b w
    ⟨ha,hb,a2,ab,tp,ts,sl,hit,y3,ys,three,w0,w1,hw,wgap⟩ nine
  let y:=x+1-a
  have ten : F (x-1)+F (a-2)+F (x+1)≤x+t+F 2-3 := by
    rcases cases with ⟨same,p⟩ | ⟨u,v,uv,fu,fv,p⟩
    · change F (x+1-a)=F 2 at same
      change F (x+1)-F (x-1)+F 2≤1 at p
      linarith only [three,same,p,y3]
    · change F u=F 2 at fu
      change F v=F 2 at fv
      change F (x+1)-F (x-1)+F (v-y+2)+2*(F y-F v)≤1 at p
      change 3<y at y3
      have down := (prefixLe ca least (show v-y+2≤v-1 by linarith)).2
      have up := (prefixLe ca least uv).1
      change F (v-1)-F (v-y+2)≤v-1-(v-y+2) at down
      change 0≤F (v-1)-F u at up
      change 2*(F (x-1)-F y)+F (a-2)≤a-2+t at three
      have ey : a+y=x+1 := by dsimp only [y]; ring
      linarith only [p,three,fu,fv,down,up,ey]
  have lastW := translatePack ca least sf hw (show 2-w≤2 by linarith)
    (show a≤a+1 by linarith) (by linarith) (by linarith)
  change F 2-F (2-w)+(F (a+1)-F a)≤a+1-a at lastW
  have lastI := translatePack ca least sf least.1 ab (show a+1≤b+1 by linarith) le_rfl le_rfl
  change F b-F a+(F (b+1)-F (a+1))≤b+1-(a+1) at lastI
  have endvalue : F x=F (b+1) := prefixGap ca least bx endgap
  linarith only [ten,nine,lastW,lastI,hit,sl,ts,bad,endvalue]
end OMA.R_Green3_green_3_R2_H1_R1_H3_R1
