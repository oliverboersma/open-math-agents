import OMAReductions.R_Green3_green_3_R2_H1_R1
import Mathlib
/-! Franchi–Gowers–Yip, Theorem 3.12, by induction on the number of component
intervals. When a left endpoint block of A and a right endpoint block of B
attain their common discrepancy, the two estimates of Corollary 3.11 are
supported on half-lines whose overlap has length twice that discrepancy.
Otherwise the balanced-block decomposition removes a prefix or suffix and
exhibits a disjoint interval in the sumset paying for the removed mass. -/
open Set MeasureTheory
open scoped Pointwise
namespace OMA.R_Green3_green_3_R2_H1_R1_H1_R1

/-- Endpoint case of the balanced interval covering estimate (FGY Corollary
3.11). The two half-lines meet at the sum of the distinguished endpoints. -/
def H1 : Prop :=
  let disc (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  ∀ (A B : Set ℝ), (∃ s : Finset (ℝ×ℝ), A=⋃p∈s,Icc p.1 p.2) →
    (∃ t : Finset (ℝ×ℝ), B=⋃p∈t,Icc p.1 p.2) → disc A=disc B →
    ∀ a b c d : ℝ, IsLeast A a → IsGreatest B d → a≤b → c≤d →
    2*volume.real (A∩Icc a b)-(b-a)=disc A →
    2*volume.real (B∩Icc c d)-(d-c)=disc B →
    2*volume.real B ≤ volume.real ((A+B)∩Iic (a+d+disc A)) ∧
    2*volume.real A ≤ volume.real ((A+B)∩Ici (a+d-disc B))

/-- The peeling case in FGY's proof. A maximal left-balanced prefix (or its
reflection, on either side) can be removed without changing the discrepancy.
Its doubled mass fits in a separate interval of the original sumset. -/
def H2 : Prop :=
  let body (s : Finset (ℝ×ℝ)) := ⋃p∈s,Icc p.1 p.2
  let disc (S : Set ℝ) := sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (S∩Icc a b)-(b-a)}
  ∀ s t : Finset (ℝ×ℝ), let A:=body s; let B:=body t
    A.Nonempty → B.Nonempty → disc A=disc B →
    (¬ ∃ a b c d : ℝ, IsLeast A a ∧ IsGreatest B d ∧ a≤b ∧ c≤d ∧
      2*volume.real (A∩Icc a b)-(b-a)=disc A ∧ 2*volume.real (B∩Icc c d)-(d-c)=disc B) →
    ∃ u v : Finset (ℝ×ℝ), let U:=body u; let V:=body v
      u.card+v.card<s.card+t.card ∧ U.Nonempty ∧ V.Nonempty ∧ disc U=disc A ∧ disc V=disc B ∧
      U+V⊆A+B ∧ ∃ l r : ℝ, l≤r ∧ Icc l r⊆A+B ∧ Disjoint (Icc l r) (U+V) ∧
        2*(volume.real A+volume.real B-volume.real U-volume.real V)≤r-l

lemma compactBody (s : Finset (ℝ×ℝ)) : IsCompact (⋃p∈s,Icc p.1 p.2) :=
  s.finite_toSet.isCompact_biUnion fun _ _ => isCompact_Icc

lemma overlapBound (S : Set ℝ) (hs : IsCompact S) (x d : ℝ) (hd : 0≤d) :
    volume.real (S∩Iic (x+d)) + volume.real (S∩Ici (x-d)) ≤ volume.real S + 2*d := by
  let L := S∩Iic (x+d)
  let R := S∩Ici (x-d)
  have lf : volume L≠⊤ := (measure_mono inter_subset_left).trans_lt hs.measure_lt_top |>.ne
  have rf : volume R≠⊤ := (measure_mono inter_subset_left).trans_lt hs.measure_lt_top |>.ne
  have ie := measureReal_union_add_inter (hs.measurableSet.inter measurableSet_Ici : MeasurableSet R) lf rf
  have union : L∪R ⊆ S := union_subset inter_subset_left inter_subset_left
  have inter : L∩R ⊆ Icc (x-d) (x+d) := fun _ h => ⟨h.2.2,h.1.2⟩
  have u := measureReal_mono union hs.measure_lt_top.ne (μ:=volume)
  have i := measureReal_mono inter (μ:=volume) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  rw [Real.volume_real_Icc_of_le (by linarith)] at i
  change volume.real L+volume.real R≤_
  linarith only [ie,u,i]

lemma discrepancy_nonneg (A : Set ℝ) (ha : IsCompact A) :
    0 ≤ sSup {t | ∃ a b : ℝ, a≤b ∧ t=2*volume.real (A∩Icc a b)-(b-a)} := by
  apply le_csSup
  · refine ⟨2*volume.real A,?_⟩
    rintro t ⟨a,b,hab,rfl⟩
    have h := measureReal_mono (s₁:=A∩Icc a b) inter_subset_left ha.measure_lt_top.ne (μ:=volume)
    linarith
  · refine ⟨0,0,le_rfl,?_⟩
    have hz : volume.real (A∩Icc (0:ℝ) 0)=0 := by
      apply le_antisymm _ measureReal_nonneg
      exact (measureReal_mono inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).trans
        (by rw [Real.volume_real_Icc]; norm_num)
    rw [hz]; ring

lemma sumsetBound (terminal : H1) (peel : H2) (s t : Finset (ℝ×ℝ)) :
    let A:=⋃p∈s,Icc p.1 p.2
    let B:=⋃p∈t,Icc p.1 p.2
    let disc (S : Set ℝ) := sSup {z | ∃ a b : ℝ, a≤b ∧ z=2*volume.real (S∩Icc a b)-(b-a)}
    A.Nonempty → B.Nonempty → disc A=disc B →
      2*volume.real A+2*volume.real B-disc A-disc B ≤ volume.real (A+B) := by
  classical
  let body (f : Finset (ℝ×ℝ)) := ⋃p∈f,Icc p.1 p.2
  let disc (S : Set ℝ) := sSup {z | ∃ a b : ℝ, a≤b ∧ z=2*volume.real (S∩Icc a b)-(b-a)}
  induction n:s.card+t.card using Nat.strong_induction_on generalizing s t with
  | h n ih =>
    let A:=body s
    let B:=body t
    change A.Nonempty → B.Nonempty → disc A=disc B → 2*volume.real A+2*volume.real B-disc A-disc B≤volume.real (A+B)
    intro an bn eq
    have ca : IsCompact A := compactBody s
    have cb : IsCompact B := compactBody t
    have cs := ca.add cb
    by_cases ends : ∃ a b c d : ℝ, IsLeast A a ∧ IsGreatest B d ∧ a≤b ∧ c≤d ∧
      2*volume.real (A∩Icc a b)-(b-a)=disc A ∧ 2*volume.real (B∩Icc c d)-(d-c)=disc B
    · obtain ⟨a,b,c,d,al,bg,ab,cd,ea,eb⟩ := ends
      obtain ⟨hl,hr⟩ := terminal A B ⟨s,rfl⟩ ⟨t,rfl⟩ eq a b c d al bg ab cd ea eb
      change 2*volume.real B≤volume.real ((A+B)∩Iic (a+d+disc A)) at hl
      change 2*volume.real A≤volume.real ((A+B)∩Ici (a+d-disc B)) at hr
      rw [←eq] at hr ⊢
      have take := overlapBound _ cs (a+d) (disc A) (discrepancy_nonneg A ca)
      linarith only [hl,hr,take]
    · obtain ⟨u,v,lt,un,vn,du,dv,sub,l,r,lr,band,separate,len⟩ := peel s t an bn eq ends
      have smaller := ih (u.card+v.card) (by omega) u v rfl un vn (du.trans (eq.trans dv.symm))
      change 2*volume.real (body u)+2*volume.real (body v)-disc (body u)-disc (body v)≤volume.real (body u+body v) at smaller
      change disc (body u)=disc A at du
      change disc (body v)=disc B at dv
      rw [du,dv] at smaller
      have su := (compactBody u).add (compactBody v)
      have total := measureReal_mono (union_subset band sub) cs.measure_lt_top.ne (μ:=volume)
      rw [measureReal_union separate su.measurableSet
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) su.measure_lt_top.ne,
        Real.volume_real_Icc_of_le lr] at total
      change 2*(volume.real A+volume.real B-volume.real (body u)-volume.real (body v))≤r-l at len
      change r-l+volume.real (body u+body v)≤volume.real (A+B) at total
      linarith only [len,smaller,total]
theorem main : H1 → H2 → OMA.R_Green3_green_3_R2_H1_R1.H1 := by
  rintro terminal peel A B ⟨s,rfl⟩ ⟨t,rfl⟩
  exact sumsetBound terminal peel s t
end OMA.R_Green3_green_3_R2_H1_R1_H1_R1
