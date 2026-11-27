import OMAReductions.R_Erdos827_erdos_827_variants_n_five_le_R1
import Mathlib

/-! A second count corrects the overlap among five-sets containing bad four-sets.
If there are d bad four-sets, at most 25*d+46620 five-sets contain one.
The remaining bad five-sets and twice the bad four-sets use at most 128205
vertex-link collisions. The pair-link bound gives d ≤ 11322, leaving at least
666 rainbow five-sets among the 435897 five-sets. -/

namespace OMA.RainbowFive
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma exchange {β γ : Type*} (S : Finset β) (T : Finset γ) (R : β → γ → Prop) [∀ a b, Decidable (R a b)] :
    (∑ a ∈ S, (T.filter (R a)).card) = ∑ b ∈ T, (S.filter fun a => R a b).card := by
  simp only [card_filter]
  exact sum_comm

lemma restrict_below (X d : Finset α) (sub : d⊆X) (k : ℕ) :
    ((X.powersetCard k).filter (· ⊆ d)) = d.powersetCard k := by
  ext z
  simp only [mem_filter,mem_powersetCard]
  exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans sub,h.2⟩,h.1⟩⟩

lemma choose_sum {β γ : Type*} (S : Finset β) (D : Finset γ) (R : β → γ → Prop) [∀ a b, Decidable (R a b)] :
    (∑ a ∈ S, ((D.filter (R a)).card).choose 2) =
    ∑ Q ∈ D.powersetCard 2, (S.filter fun a => ∀ d ∈ Q, R a d).card := by
  have one (a : β) : (D.filter (R a)).powersetCard 2 =
      (D.powersetCard 2).filter (fun Q => ∀ d ∈ Q, R a d) := by
    ext Q
    simp only [mem_filter,mem_powersetCard]
    constructor
    · intro h
      exact ⟨⟨h.1.trans (filter_subset _ _),h.2⟩,fun d hd => (mem_filter.mp (h.1 hd)).2⟩
    · rintro ⟨⟨sub,sz⟩,rel⟩
      exact ⟨fun d hd => mem_filter.mpr ⟨sub hd,rel d hd⟩,sz⟩
  calc _ = ∑ a ∈ S, ((D.powersetCard 2).filter (fun Q => ∀ d ∈ Q, R a d)).card :=
         sum_congr rfl fun a _ => (card_powersetCard 2 (D.filter (R a))).symm.trans (congrArg Finset.card (one a))
       _ = _ := exchange _ _ _

lemma pair_shadow (X : Finset α) (D : Finset (Finset α)) (hd : D ⊆ X.powersetCard 4) :
    (∑ B ∈ X.powersetCard 3, ((D.filter (B ⊆ ·)).card).choose 2) ≤
    ∑ Y ∈ X.powersetCard 5, ((D.filter (· ⊆ Y)).card).choose 2 := by
  rw [choose_sum (X.powersetCard 3) D (fun B d => B⊆d),
      choose_sum (X.powersetCard 5) D (fun Y d => d⊆Y)]
  apply sum_le_sum
  intro Q hQ
  obtain ⟨sub,sz⟩ := mem_powersetCard.mp hQ
  obtain ⟨d,e,ne,rfl⟩ := card_eq_two.mp sz
  have ds := mem_powersetCard.mp (hd (sub (by simp : d ∈ ({d,e} : Finset _))))
  have es := mem_powersetCard.mp (hd (sub (by simp : e ∈ ({d,e} : Finset _))))
  have hlt : (d∩e).card < 4 := by
    by_contra! h
    have one := eq_of_subset_of_card_le (inter_subset_left (s₁ := d) (s₂ := e)) (ds.2 ▸ h)
    have two := eq_of_subset_of_card_le (inter_subset_right (s₁ := d) (s₂ := e)) (es.2 ▸ h)
    exact ne (one.symm.trans two)
  by_cases haveB : ∃ B ∈ X.powersetCard 3, B⊆d ∧ B⊆e
  · obtain ⟨B,hB,hBd,hBe⟩ := haveB
    have z := card_le_card (subset_inter hBd hBe)
    have sb := (mem_powersetCard.mp hB).2
    have hi : (d∩e).card=3 := by omega
    have un := card_union_add_card_inter d e
    have hu : d∪e ∈ X.powersetCard 5 :=
      mem_powersetCard.mpr ⟨union_subset ds.1 es.1,by omega⟩
    have small : ((X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      have ident (z) (hz : z ∈ (X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)) :
          z=d∩e := by
        obtain ⟨hz,holds⟩ := mem_filter.mp hz
        apply eq_of_subset_of_card_le (subset_inter (holds d (by simp)) (holds e (by simp)))
        rw [hi,(mem_powersetCard.mp hz).2]
      exact (ident a ha).trans (ident b hb).symm
    apply small.trans
    apply card_pos.mpr
    exact ⟨d∪e,mem_filter.mpr ⟨hu,by simp⟩⟩
  · have no : ((X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha,ok⟩ := mem_filter.mp ha
      exact haveB ⟨a,ha,ok d (by simp),ok e (by simp)⟩
    rw [no,card_empty]
    exact Nat.zero_le _

lemma shadow_budget (X : Finset α) (D : Finset (Finset α)) (hX : X.card=37)
    (hd : D ⊆ X.powersetCard 4) :
    ((X.powersetCard 5).filter fun Y => ∃ d ∈ D, d⊆Y).card ≤ 25*D.card + 46620 := by
  let A := X.powersetCard 3
  let Z := X.powersetCard 5
  let n (B : Finset α) := (D.filter (B ⊆ ·)).card
  let k (Y : Finset α) := (D.filter (· ⊆ Y)).card
  have na : (∑ B ∈ A, n B) = 4*D.card := by
    change (∑ B ∈ A, (D.filter (B⊆·)).card) = _
    rw [exchange A D (fun B d => B⊆d)]
    have one (d) (h : d∈D) : (A.filter (·⊆d)).card=4 := by
      obtain ⟨s,sz⟩ := mem_powersetCard.mp (hd h)
      dsimp only [A]
      rw [restrict_below _ _ s,card_powersetCard,sz]; decide
    simpa [mul_comm] using sum_congr rfl one
  have kz : (∑ Y ∈ Z, k Y) = 33*D.card := by
    change (∑ Y ∈ Z, (D.filter (·⊆Y)).card) = _
    rw [exchange Z D (fun Y d => d⊆Y)]
    have one (d) (h : d∈D) : (Z.filter (d⊆·)).card=33 := by
      obtain ⟨s,sz⟩ := mem_powersetCard.mp (hd h)
      dsimp only [Z]
      rw [card_filter_powersetCard_subset _ _ _ s (by omega),sz,hX]; decide
    simpa [mul_comm] using sum_congr rfl one
  have choose_low (a : ℕ) : 5*a ≤ a.choose 2 + 15 := by
    induction a with
    | zero => decide
    | succ a ih =>
      by_cases h : a<5
      · interval_cases a <;> decide
      · have iden : (a+1).choose 2 = a + a.choose 2 := by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ a 1
        omega
  have countA : A.card=7770 := by dsimp only [A]; rw [card_powersetCard,hX]; decide
  have lo := sum_le_sum (s := A) (fun B _ => choose_low (n B))
  simp only [←mul_sum,sum_add_distrib,sum_const,smul_eq_mul,countA,na] at lo
  have common := pair_shadow X D hd
  change (∑ B ∈ A, (n B).choose 2) ≤ ∑ Y ∈ Z, (k Y).choose 2 at common
  have upper (Y) (hY : Y∈Z) : 2*(k Y).choose 2 + 5*(if 0<k Y then 1 else 0) ≤ 5*k Y := by
    have h : D.filter (·⊆Y) ⊆ Y.powersetCard 4 := fun d h => mem_powersetCard.mpr
      ⟨(mem_filter.mp h).2,(mem_powersetCard.mp (hd (mem_filter.mp h).1)).2⟩
    have bound := card_le_card h
    rw [card_powersetCard,(mem_powersetCard.mp hY).2] at bound
    change k Y ≤ 5 at bound
    generalize e : k Y = a at *
    interval_cases a <;> decide
  have up := sum_le_sum upper
  simp only [sum_add_distrib,←mul_sum,kz] at up
  have c : ((X.powersetCard 5).filter fun Y => ∃ d ∈ D,d⊆Y).card =
      ∑ Y ∈ Z, if 0<k Y then 1 else 0 := by
    rw [card_filter]
    apply sum_congr rfl
    intro Y _
    have iff : (∃ d ∈ D,d⊆Y) ↔ 0<k Y := by simp only [k,card_pos,filter_nonempty_iff]
    simp only [iff]
  rw [c]
  omega

end OMA.RainbowFive


namespace OMA.RainbowFive
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma link_budget (S : Finset (Finset α)) (c : Finset α → ℝ) (F : Finset (Finset α))
    (p q : Finset α → Finset α) (k : ℕ)
    (pair : ∀ Y∈F, p Y∈S ∧ q Y∈S ∧ p Y ≠ q Y ∧ c (p Y)=c (q Y) ∧ p Y ∪ q Y=Y)
    (cap : ∀ r, (S.filter fun T => c T=r).card ≤ k+1) : 2*F.card ≤ S.card*k := by
  classical
  let R (Y T : Finset α) := T=p Y ∨ T=q Y
  have low (Y) (h : Y∈F) : 2 ≤ (S.filter (R Y)).card := by
    obtain ⟨hp,hq,ne,_,_⟩ := pair Y h
    have eq : S.filter (R Y)={p Y,q Y} := by ext T; simp [R]; aesop
    simp [eq,ne]
  have high (T) (hT : T ∈ S) : (F.filter (fun Y => R Y T)).card ≤ k := by
    let other (Y : Finset α) := if T=p Y then q Y else p Y
    have info {Y} (h : Y ∈ F.filter (fun Y => R Y T)) :
        other Y ∈ S ∧ other Y ≠ T ∧ c (other Y) = c T ∧ T ∪ other Y=Y := by
      obtain ⟨hY,rel⟩ := mem_filter.mp h
      obtain ⟨hp,hq,ne,col,un⟩ := pair Y hY
      rcases rel with e|e
      · simp only [other,e,ite_true]
        exact ⟨hq,ne.symm,col.symm,un⟩
      · simp only [other,e,if_neg ne.symm]
        exact ⟨hp,ne,col,(union_comm _ _).trans un⟩
    have cmp : (F.filter (fun Y => R Y T)).card ≤ ((S.filter fun U => c U=c T).erase T).card := by
      apply card_le_card_of_injOn other
      · intro Y h
        obtain ⟨hs,hn,hc,_⟩ := info h
        exact mem_erase.mpr ⟨hn,mem_filter.mpr ⟨hs,hc⟩⟩
      · intro Y hY Z hZ eq
        rw [←(info hY).2.2.2,←(info hZ).2.2.2,eq]
    have del := card_erase_add_one (mem_filter.mpr ⟨hT,rfl⟩ : T∈S.filter fun U => c U=c T)
    have lim := cap (c T)
    omega
  have e : F.card • (2:ℕ) ≤ S.card • k :=
    card_nsmul_le_card_nsmul (r := R) (s := F) (t := S) low high
  simpa only [smul_eq_mul,mul_comm F.card] using e

lemma vertex_fiber (X : Finset α) (c : Finset α → ℝ) (a : α) (r : ℝ)
    (cap : (((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card ≤ 12) :
    (((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)).card ≤ 12 := by
  apply le_trans _ cap
  apply card_le_card_of_injOn (fun T : Finset α => T.erase a)
  · intro T hT
    obtain ⟨hT,col⟩ := mem_filter.mp hT
    obtain ⟨hT,contains⟩ := mem_filter.mp hT
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp hT
    have ha := singleton_subset_iff.mp contains
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨erase_subset_erase _ sub,?_⟩,?_⟩
    · rw [card_erase_of_mem ha,sz]
    · simpa only [insert_erase ha] using col
  · intro T hT U hU eq
    have h (V) (hv : V ∈ ((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)) :
        a∈V := singleton_subset_iff.mp (mem_filter.mp (mem_filter.mp hv).1).2
    exact (insert_erase (h _ hT)).symm.trans ((congrArg (insert a) eq).trans (insert_erase (h _ hU)))

lemma edge_fiber (X B : Finset α) (c : Finset α → ℝ) (r : ℝ) (sb : B.card=2)
    (cap : ((X\B).filter fun z => c (insert z B)=r).card ≤ 2) :
    (((X.powersetCard 3).filter (B ⊆ ·)).filter (fun T => c T=r)).card ≤ 2 := by
  let S := ((X.powersetCard 3).filter (B ⊆ ·)).filter fun T => c T=r
  let Z := (X\B).filter fun z => c (insert z B)=r
  have sub : S ⊆ Z.image (fun z => insert z B) := by
    intro T h
    obtain ⟨hT,col⟩ := mem_filter.mp h
    obtain ⟨hT,contains⟩ := mem_filter.mp hT
    obtain ⟨tx,st⟩ := mem_powersetCard.mp hT
    have cs : (T\B).card=1 := by rw [card_sdiff_of_subset contains,st,sb]
    obtain ⟨z,hz⟩ := card_eq_one.mp cs
    have inD : z∈T\B := by rw [hz]; simp
    have eq : insert z B=T := by
      rw [←singleton_union,←hz,sdiff_union_of_subset contains]
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_sdiff.mpr
      ⟨tx (mem_sdiff.mp inD).1,(mem_sdiff.mp inD).2⟩,eq ▸ col⟩,eq⟩
  exact (card_le_card sub).trans (card_image_le.trans cap)

end OMA.RainbowFive


namespace OMA.RainbowFive
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

theorem rainbow_five (X : Finset α) (c : Finset α → ℝ) (hX : X.card=37)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2)
    (vertices : ∀ a∈X,∀ r,(((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card≤12) :
    ∃ Y⊆X, Y.card=5 ∧ Set.InjOn c (Y.powersetCard 3 : Set (Finset α)) := by
  classical
  by_contra! no
  let bad (Y : Finset α) := ¬ Set.InjOn c (Y.powersetCard 3 : Set (Finset α))
  let D := (X.powersetCard 4).filter bad
  let E := (X.powersetCard 5).filter fun Y => ¬ ∃ d∈D,d⊆Y
  let F := D∪E
  have fd : D ⊆ F := subset_union_left
  have fe : E ⊆ F := subset_union_right
  have dX : D ⊆ X.powersetCard 4 := filter_subset _ _
  have eX : E ⊆ X.powersetCard 5 := filter_subset _ _
  have points {Y : Finset α} (hY : Y ∈ F) : Y⊆X := by
    rcases mem_union.mp hY with h|h
    · exact (mem_powersetCard.mp (dX h)).1
    · exact (mem_powersetCard.mp (eX h)).1
  have de : Disjoint D E := disjoint_left.mpr fun Y hd he => by
    have four := (mem_powersetCard.mp (dX hd)).2
    have five := (mem_powersetCard.mp (eX he)).2
    omega
  have pick (Y : Finset α) (hY : Y∈F) :
      ∃ p q : Finset α, p ∈ X.powersetCard 3 ∧ q ∈ X.powersetCard 3 ∧
        p≠q ∧ c p=c q ∧ p∪q=Y := by
    have hb : bad Y := by
      rcases mem_union.mp hY with h|h
      · exact (mem_filter.mp h).2
      · exact no Y (points hY) (mem_powersetCard.mp (eX h)).2
    change ¬ Set.InjOn _ _ at hb
    simp only [Set.InjOn,not_forall] at hb
    push Not at hb
    obtain ⟨p,hp,q,hq,col,ne⟩ := hb
    obtain ⟨py,sp⟩ := mem_powersetCard.mp hp
    obtain ⟨qy,sq⟩ := mem_powersetCard.mp hq
    have un : p∪q ⊆ Y := union_subset py qy
    have more : 3 < (p∪q).card := by
      by_contra! le
      have ep := eq_of_subset_of_card_le (subset_union_left (s₂ := q)) (show (p∪q).card ≤ p.card by omega)
      have eq := eq_of_subset_of_card_le (subset_union_right (s₁ := p)) (show (p∪q).card ≤ q.card by omega)
      exact ne (ep.trans eq.symm)
    refine ⟨p,q,mem_powersetCard.mpr ⟨py.trans (points hY),sp⟩,
      mem_powersetCard.mpr ⟨qy.trans (points hY),sq⟩,ne,col,?_⟩
    apply eq_of_subset_of_card_le un
    rcases mem_union.mp hY with hd|he
    · rw [(mem_powersetCard.mp (dX hd)).2]; omega
    · have sz := (mem_powersetCard.mp (eX he)).2
      by_contra! lt
      have su : (p∪q).card=4 := by omega
      apply (mem_filter.mp he).2
      refine ⟨p∪q,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨un.trans (points hY),su⟩,?_⟩,un⟩
      intro injective
      exact ne (injective (mem_powersetCard.mpr ⟨subset_union_left,sp⟩)
        (mem_powersetCard.mpr ⟨subset_union_right,sq⟩) col)
  choose! p q pair using pick
  let I (Y : Finset α) := p Y ∩ q Y
  have iX (Y) (hy : Y∈F) : I Y ⊆ X :=
    inter_subset_left.trans (mem_powersetCard.mp (pair Y hy).1).1
  have ic (Y) (hy : Y∈F) : Y.card+(I Y).card=6 := by
    obtain ⟨hp,hq,_,_,un⟩ := pair Y hy
    simpa only [I,un,(mem_powersetCard.mp hp).2,(mem_powersetCard.mp hq).2] using card_union_add_card_inter (p Y) (q Y)
  let S (B : Finset α) := (X.powersetCard 3).filter (B⊆·)
  let L (B : Finset α) := F.filter fun Y => B⊆I Y
  have bound (B : Finset α) (k : ℕ) (lim : ∀ r, ((S B).filter fun T => c T=r).card ≤ k+1) :
      2*(L B).card ≤ (S B).card*k := by
    apply link_budget (S B) c (L B) p q k _ lim
    intro Y hy
    obtain ⟨yf,bi⟩ := mem_filter.mp hy
    obtain ⟨hp,hq,ne,col,un⟩ := pair Y yf
    exact ⟨mem_filter.mpr ⟨hp,bi.trans inter_subset_left⟩,mem_filter.mpr ⟨hq,bi.trans inter_subset_right⟩,ne,col,un⟩
  have degree (a : α) (ha : a∈X) : 2*((L {a}).card) ≤ 6930 := by
    have b := bound {a} 11 (fun r => vertex_fiber X c a r (vertices a ha r))
    have k : (S {a}).card=630 := by
      dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr ha) (by simp),hX,card_singleton]; decide
    omega
  have countV : (∑ a ∈ X, (L {a}).card)=2*D.card+E.card := by
    change (∑ a ∈ X, (F.filter (fun Y => {a}⊆I Y)).card)=_
    rw [exchange X F (fun a Y => {a}⊆I Y)]
    have each (Y) (hy : Y∈F) : (X.filter fun a => {a}⊆I Y).card = (I Y).card := by
      congr 1; ext a
      simp only [mem_filter,singleton_subset_iff]
      exact ⟨And.right,fun ha => ⟨iX Y hy ha,ha⟩⟩
    rw [sum_congr rfl each]
    change (∑ Y ∈ D∪E, (I Y).card)=_
    rw [sum_union de]
    have dcount (Y) (hy : Y∈D) : (I Y).card=2 := by
      have := ic Y (fd hy); have := (mem_powersetCard.mp (dX hy)).2; omega
    have ecount (Y) (hy : Y∈E) : (I Y).card=1 := by
      have := ic Y (fe hy); have := (mem_powersetCard.mp (eX hy)).2; omega
    rw [sum_congr rfl dcount,sum_congr rfl ecount]
    simp [mul_comm]
  have many := sum_le_sum degree
  simp only [←mul_sum,countV,sum_const,smul_eq_mul,hX] at many
  have per (B) (hB : B ∈ X.powersetCard 2) : (L B).card ≤ 17 := by
    obtain ⟨bx,sb⟩ := mem_powersetCard.mp hB
    have b := bound B 1 (fun r => edge_fiber X B c r sb (edges B bx sb r))
    have s : (S B).card=35 := by
      dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ bx (by omega),sb,hX]; decide
    omega
  have dBound : D.card ≤ 11322 := by
    have sub (Y) (h : Y∈D) : I Y ∈ X.powersetCard 2 := by
      refine mem_powersetCard.mpr ⟨iX Y (fd h),?_⟩
      have := ic Y (fd h); have := (mem_powersetCard.mp (dX h)).2; omega
    have inequality : D.card ≤ ∑ B ∈ X.powersetCard 2, (L B).card := by
      calc D.card = ∑ Y ∈ D, (1:ℕ) := by simp
           _ ≤ ∑ Y ∈ D, ((X.powersetCard 2).filter (·⊆I Y)).card := sum_le_sum (fun Y h =>
                  card_pos.mpr ⟨I Y,mem_filter.mpr ⟨sub Y h,Subset.rfl⟩⟩)
           _ ≤ _ := by
             rw [exchange D (X.powersetCard 2) (fun Y B => B ⊆ I Y)]
             exact sum_le_sum fun B _ => card_le_card (filter_subset_filter _ fd)
    have b := sum_le_sum per
    rw [sum_const,smul_eq_mul,card_powersetCard,hX] at b
    rw [show Nat.choose 37 2 = 666 by decide] at b
    omega
  have shadow := shadow_budget X D hX dX
  have parts := card_filter_add_card_filter_not (s := X.powersetCard 5) (fun Y => ∃ d∈D,d⊆Y)
  change _ + E.card = _ at parts
  rw [card_powersetCard,hX] at parts
  rw [show Nat.choose 37 5 = 435897 by decide] at parts
  omega
end OMA.RainbowFive


theorem OMA.solution : OMA.R_Erdos827_erdos_827_variants_n_five_le_R1.H2 := by
  exact OMA.RainbowFive.rainbow_five
