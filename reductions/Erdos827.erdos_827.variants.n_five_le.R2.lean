import FormalConjectures.ErdosProblems.«827»
import Mathlib

/-!
# Three overlapping families of equal circumradius in a putative 37-point counterexample

Martínez and Roldán-Pensado state the bound in Theorem 1.2 of arXiv:1402.6276.
Javi Soto's reduction (#4669) isolates a vertex incident to thirteen triangles of a single radius.
Here that same vertex must also admit three distinct radii with at least nine triangles each.
Two further points belong to the supports of all three families. The remaining cases distinguish
whether the triangle on these three marked points belongs to one of the families.

The fixed-chord geometry uses Ian Qvist (@Genbox, #1550) and @ivillar (#4882).
The four-set shadow estimate and the choice of colliding pairs use Marcus Buffett (#4926).
The additional incidence count uses the fact that the link of one radius has maximum degree two,
so it has at least as many endpoints as edges. If no pair of endpoints lies in three rich supports,
the rich classes account for at most twice `36.choose 2` equal-radius pairs at the vertex.
All other classes together account for at most `7 * 630 / 2` pairs.
-/
open Erdos827 EuclideanGeometry Finset

namespace OMA.CircumradiusOverlap.Geometry

private theorem two_distances {a b c d e : ℝ²} {r s : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : dist c a = r) (hb : dist d a = r) (he : dist e a = r)
    (ha' : dist c b = s) (hb' : dist d b = s) (he' : dist e b = s) :
    e = c ∨ e = d :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hab hcd ha hb he ha' hb' he'

private theorem radius_unique_at_insert {E : Finset ℝ²} (hE : E.card = 2)
    {x : ℝ²} (hx : x ∉ E) {r s : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert x E) s) :
    r = s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have hax : a ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hbx : b ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hxx : x ∈ (insert x {a, b} : Finset ℝ²) := by simp
  by_cases he : c = d
  · exact (hc x hxx).symm.trans (he ▸ hd x hxx)
  · exact False.elim (hx (by
      rcases two_distances he hab (hc a hax) (hc b hbx) (hc x hxx)
        (hd a hax) (hd b hbx) (hd x hxx) with h | h <;> simp [h]))

private theorem three_insert_impossible {X E : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hEX : E ⊆ X) (hE : E.card = 2)
    {x y z : ℝ²} (hxX : x ∈ X) (hyX : y ∈ X) (hzX : z ∈ X)
    (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert y E) r)
    (h₃ : OnCircleOfRadius (insert z E) r) : False := by
  classical
  have centers_ne {u v c : ℝ²} (huX : u ∈ X) (hvX : v ∈ X)
      (hu : u ∉ E) (hv : v ∉ E) (huv : u ≠ v)
      (huc : ∀ w ∈ insert u E, dist w c = r)
      (hvc : ∀ w ∈ insert v E, dist w c = r) : False := by
    apply hX (↑(insert u (insert v E)) : Set ℝ²)
    · intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huX
      · obtain rfl | hw := Finset.mem_insert.mp hw
        · exact hvX
        · exact hEX hw
    · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [huv, hu]),
        Finset.card_insert_of_notMem hv, hE]
    · refine ⟨c, r, ?_⟩
      intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huc _ (Finset.mem_insert_self ..)
      · exact hvc w hw
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨e, he⟩ := h₃
  have hcd : c ≠ d := fun hh => centers_ne hxX hyX hx hy hxy hc (hh ▸ hd)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  have ha (w : ℝ²) : a ∈ (insert w {a, b} : Finset ℝ²) := by simp
  have hb (w : ℝ²) : b ∈ (insert w {a, b} : Finset ℝ²) := by simp
  obtain h | h := two_distances hab hcd
    ((dist_comm _ _).trans (hc a (ha x))) ((dist_comm _ _).trans (hd a (ha y)))
    ((dist_comm _ _).trans (he a (ha z))) ((dist_comm _ _).trans (hc b (hb x)))
    ((dist_comm _ _).trans (hd b (hb y))) ((dist_comm _ _).trans (he b (hb z)))
  · exact centers_ne hxX hzX hx hz hxz hc (h ▸ he)
  · exact centers_ne hyX hzX hy hz hyz hd (h ▸ he)

private theorem radius_unique {T : Finset ℝ²} (hT : T.card = 3) {r s : ℝ}
    (hr : OnCircleOfRadius T r) (hs : OnCircleOfRadius T s) : r = s := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hE : (T.erase p).card = 2 := by
    have := Finset.card_erase_add_one hp
    omega
  exact radius_unique_at_insert hE (notMem_erase p T)
    (by simpa [insert_erase hp] using hr) (by simpa [insert_erase hp] using hs)

private theorem exists_radius {X : Finset ℝ²} (hX : NonTrilinear (X : Set ℝ²)) {T : Finset ℝ²}
    (hT : T ⊆ X) (h3 : T.card = 3) : ∃ r, OnCircleOfRadius T r := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  have hcol : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
    hX (hT (by simp)) (hT (by simp)) (hT (by simp)) hab hbc hac
  have hind : AffineIndependent ℝ ![a, b, c] := affineIndependent_iff_not_collinear_set.mpr hcol
  obtain ⟨cs, ⟨_, hcs⟩, _⟩ := hind.existsUnique_dist_eq
  refine ⟨cs.radius, cs.center, fun p hp => ?_⟩
  have hp' : p ∈ Set.range ![a, b, c] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  exact EuclideanGeometry.mem_sphere.mp (hcs hp')

end OMA.CircumradiusOverlap.Geometry

open Erdos827 EuclideanGeometry Finset OMA.CircumradiusOverlap.Geometry in
theorem OMA.CircumradiusOverlap.radius_coloring : ∀ X : Finset ℝ², InGeneralPosition (X:Set ℝ²) →
  ∃ c : Finset ℝ²→ℝ,
    (∀ T⊆X,T.card=3 → ∀ r, c T=r ↔ OnCircleOfRadius T r) ∧
    ∀ B⊆X,B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2 := by
  intro X hX
  obtain ⟨hNT, hNF⟩ := hX
  classical
  let c : Finset ℝ² → ℝ := fun T => if h : ∃ r, OnCircleOfRadius T r then h.choose else 0
  have hc : ∀ T ⊆ X, T.card = 3 → OnCircleOfRadius T (c T) := by
    intro T hT h3
    have h := exists_radius hNT hT h3
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨c, ?_, ?_⟩
  · intro T hT h3 r
    constructor
    · rintro rfl
      exact hc T hT h3
    · intro hr
      exact radius_unique h3 (hc T hT h3) hr
  · intro B hB h2 r
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hlt
    rw [Finset.mem_filter, Finset.mem_sdiff] at hx hy hz
    have hins (w : ℝ²) (hw : w ∈ X) (hwB : w ∉ B) :
        OnCircleOfRadius (insert w B) (c (insert w B)) :=
      hc _ (Finset.insert_subset hw hB) (by rw [Finset.card_insert_of_notMem hwB, h2])
    have ox := hins x hx.1.1 hx.1.2
    have oy := hins y hy.1.1 hy.1.2
    have oz := hins z hz.1.1 hz.1.2
    rw [hx.2] at ox
    rw [hy.2] at oy
    rw [hz.2] at oz
    exact three_insert_impossible hNF hB h2 hx.1.1 hy.1.1 hz.1.1 hx.1.2 hy.1.2 hz.1.2
      hxy hxz hyz ox oy oz

namespace OMA.CircumradiusOverlap
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

end OMA.CircumradiusOverlap


namespace OMA.CircumradiusOverlap
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
    : (((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)).card ≤
      (((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card := by
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

end OMA.CircumradiusOverlap


namespace OMA.CircumradiusOverlap
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma link_support (X : Finset α) (c : Finset α → ℝ)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter fun z => c (insert z B)=r).card≤2)
    {a : α} (ha : a ∈ X) (r : ℝ) :
    (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r).card ≤ ((((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r).biUnion id).card := by
  let V := X.erase a
  let L := (V.powersetCard 2).filter fun B => c (insert a B)=r
  let U := L.biUnion id
  have support : U ⊆ V := by
    intro x hx
    obtain ⟨B,hB,mem⟩ := mem_biUnion.mp hx
    exact (mem_powersetCard.mp (mem_filter.mp hB).1).1 mem
  have lo (B) (hB : B ∈ L) : 2 ≤ (U.filter (· ∈ B)).card := by
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp (mem_filter.mp hB).1
    have eq : U.filter (· ∈ B) = B := by ext x; simp only [mem_filter]; exact ⟨And.right, fun h => ⟨mem_biUnion.mpr ⟨B,hB,h⟩,h⟩⟩
    rw [eq,sz]
  have hi (b) (inU : b ∈ U) : (L.filter (b ∈ ·)).card ≤ 2 := by
    have hb := support inU
    have ba : b ≠ a := (mem_erase.mp hb).1
    let P : Finset α := {a,b}
    have sz : P.card = 2 := card_pair ba.symm
    have hP : P ⊆ X := insert_subset ha (singleton_subset_iff.mpr (mem_erase.mp hb).2)
    let T := (X\P).filter fun z => c (insert z P) = r
    have sub : L.filter (b ∈ ·) ⊆ T.image (fun z => ({b,z} : Finset α)) := by
      intro B h
      obtain ⟨hB,bB⟩ := mem_filter.mp h
      obtain ⟨hB,col⟩ := mem_filter.mp hB
      obtain ⟨inV,szB⟩ := mem_powersetCard.mp hB
      obtain ⟨z,ne,w,eq⟩ := Finset.card_eq_two.mp szB
      rcases (show b = z ∨ b = ne by simpa [eq] using bB) with e|e
      · subst z
        have hn := mem_erase.mp (inV (show ne∈B by simp [eq]))
        exact mem_image.mpr ⟨ne,mem_filter.mpr ⟨mem_sdiff.mpr ⟨hn.2,by simp [P,hn.1,w.symm]⟩,
          by convert col using 2; ext x; simp [P,eq]; tauto⟩,eq.symm⟩
      · subst ne
        have hn := mem_erase.mp (inV (show z∈B by simp [eq]))
        exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_sdiff.mpr ⟨hn.2,by simp [P,hn.1,w]⟩,
          by convert col using 2; ext x; simp [P,eq]; tauto⟩,by rw [eq,pair_comm]⟩
    exact (card_le_card sub).trans (card_image_le.trans (edges P hP sz r))
  have h := card_nsmul_le_card_nsmul (r := fun (B : Finset α) x => x∈B) (s:=L) (t:=U) lo hi
  change L.card * 2 ≤ U.card * 2 at h
  change L.card ≤ U.card
  omega
/-- A family of unions of two distinct monochromatic members injects into the
union of the two-element subsets of the individual color classes. -/
lemma count_unions (S F : Finset (Finset α)) (c : Finset α → ℝ)
    (p q : Finset α → Finset α)
    (pair : ∀ Y∈F, p Y∈S ∧ q Y∈S ∧ p Y≠q Y ∧ c (p Y)=c (q Y) ∧ p Y∪q Y=Y) :
    F.card ≤ ∑ r ∈ S.image c, ((S.filter fun T => c T=r).card).choose 2 := by
  classical
  let f (Y : Finset α) : Finset (Finset α) := {p Y,q Y}
  let A (r : ℝ) := (S.filter fun T => c T=r).powersetCard 2
  have b : F.card ≤ ((S.image c).biUnion A).card := by
    apply card_le_card_of_injOn f
    · intro Y hY
      obtain ⟨hp,hq,ne,col,_⟩ := pair Y hY
      refine mem_biUnion.mpr ⟨_,mem_image_of_mem c hp,mem_powersetCard.mpr ⟨?_,card_pair ne⟩⟩
      exact insert_subset (mem_filter.mpr ⟨hp,rfl⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨hq,col.symm⟩))
    · intro Y hY Z hZ eq
      have u (W) (hw : W∈F) : (f W).biUnion id=W := by simpa [f] using (pair W hw).2.2.2.2
      exact (u Y hY).symm.trans ((congrArg (fun s : Finset (Finset α) => s.biUnion id) eq).trans (u Z hZ))
  exact b.trans ((card_biUnion_le).trans_eq (by simp [A]))

/-- Three rich color classes must share two endpoints if the color classes
contribute more than 3465 pairs. Each color class has at most as many
members as its support has endpoints. -/
lemma support_budget {β : Type*} [DecidableEq β] (V : Finset α) (R : Finset β)
    (t : β → ℕ) (U : β → Finset α) (size : V.card=36)
    (total : (∑ r ∈ R, t r) ≤ 630) (support : ∀ r∈R, U r ⊆ V)
    (inc : ∀ r∈R, t r ≤ (U r).card)
    (thin : ∀ D ∈ V.powersetCard 2,
      ((R.filter fun r => 9 ≤ t r).filter fun r => D⊆U r).card ≤ 2) :
    (∑ r ∈ R, (t r).choose 2) ≤ 3465 := by
  classical
  let H := R.filter fun r => 9 ≤ t r
  have hi : (∑ r ∈ H, (t r).choose 2) ≤ 1260 := by
    calc _ ≤ ∑ r ∈ H, ((V.powersetCard 2).filter (· ⊆ U r)).card := by
           apply sum_le_sum
           intro r hr
           have hr' := (mem_filter.mp hr).1
           rw [restrict_below V (U r) (support r hr') 2, card_powersetCard]
           exact Nat.choose_le_choose 2 (inc r hr')
         _ = _ := exchange H (V.powersetCard 2) (fun r D => D ⊆ U r)
         _ ≤ ∑ _D ∈ V.powersetCard 2, 2 := sum_le_sum thin
         _ = 1260 := by rw [sum_const,smul_eq_mul,card_powersetCard,size]; decide
  let K := R.filter fun r => ¬ 9 ≤ t r
  have cheap (n : ℕ) (hn : n < 9) : 2 * n.choose 2 ≤ 7*n := by interval_cases n <;> decide
  have lo : 2*(∑ r ∈ K, (t r).choose 2) ≤ 7*630 := by
    calc _ = ∑ r ∈ K, 2 * (t r).choose 2 := mul_sum ..
         _ ≤ ∑ r ∈ K, 7 * t r := sum_le_sum fun r hr => cheap _ (Nat.lt_of_not_ge (mem_filter.mp hr).2)
         _ = 7 * ∑ r ∈ K, t r := (mul_sum ..).symm
         _ ≤ _ := Nat.mul_le_mul_left 7 ((sum_le_sum_of_subset (filter_subset _ _)).trans total)
  have split := sum_filter_add_sum_filter_not R (fun r => 9 ≤ t r) (fun r => (t r).choose 2)
  change (∑ r ∈ H, _) + (∑ r ∈ K, _) = _ at split
  omega
theorem rainbow_five (X : Finset α) (c : Finset α → ℝ) (hX : X.card=37)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2)
    (thin : ∀ a∈X, (∃ s : ℝ, 13 ≤ (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=s).card) →
       ∀ D∈(X.erase a).powersetCard 2, ∀ C : Finset ℝ, C.card=3 →
       ¬ ∀ r∈C, let E := ((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r
                9 ≤ E.card ∧ D ⊆ E.biUnion id) :
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
    by_cases rich : ∃ s : ℝ, 13 ≤ (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=s).card
    case neg =>
      have b := bound {a} 11 (by
        intro r
        have l := vertex_fiber X c a r
        have cap : ¬ 13 ≤ (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r).card := fun h => rich ⟨r,h⟩
        change (((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)).card ≤ 11+1
        omega)
      have sc : (S {a}).card=630 := by
        dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr ha) (by simp),hX,card_singleton]; decide
      omega
    let V := X.erase a
    let R := (S {a}).image c
    let t (r : ℝ) := ((S {a}).filter fun T => c T=r).card
    let E' (r : ℝ) := (V.powersetCard 2).filter fun B => c (insert a B)=r
    let U (r : ℝ) := (E' r).biUnion id
    have same (r : ℝ) : t r ≤ (E' r).card := vertex_fiber X c a r
    have vs : V.card=36 := by simp [V,card_erase_of_mem ha,hX]
    have sc : (S {a}).card=630 := by
      dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr ha) (by simp),hX,card_singleton]; decide
    have tot : (∑ r ∈ R,t r) ≤ 630 := by
      have eq := card_eq_sum_card_fiberwise (s:=S {a}) (t:=R) (f:=c) (fun T hT => mem_image_of_mem c hT)
      exact eq.ge.trans sc.le
    have sub (r : ℝ) (_ : r∈R) : U r ⊆ V := by
      intro x hx
      obtain ⟨B,hB,mem⟩ := mem_biUnion.mp hx
      exact (mem_powersetCard.mp (mem_filter.mp hB).1).1 mem
    have small (D') (hD : D'∈V.powersetCard 2) :
        ((R.filter fun r => 9 ≤ t r).filter fun r => D'⊆U r).card ≤ 2 := by
      by_contra! many
      obtain ⟨C,cs,sz⟩ := exists_subset_card_eq (show 3 ≤ _ from many)
      apply thin a ha rich D' hD C sz
      intro r hr
      have hr' := mem_filter.mp (cs hr)
      exact ⟨(mem_filter.mp hr'.1).2.trans (same r),hr'.2⟩
    have lim := support_budget V R t U vs tot sub (fun r _ => (same r).trans (link_support X c edges ha r)) small
    have pairs := count_unions (S {a}) (L {a}) c p q (by
      intro Y hy
      obtain ⟨yf,bi⟩ := mem_filter.mp hy
      obtain ⟨hp,hq,ne,col,un⟩ := pair Y yf
      exact ⟨mem_filter.mpr ⟨hp,bi.trans inter_subset_left⟩,mem_filter.mpr ⟨hq,bi.trans inter_subset_right⟩,ne,col,un⟩)
    have bound' : (L {a}).card ≤ 3465 := pairs.trans lim
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
end OMA.CircumradiusOverlap

namespace OMA.R_Erdos827_erdos_827_variants_n_five_le_R2
open Finset EuclideanGeometry Erdos827
open scoped Classical

/-- The base triangle uses one of the three rich radii. -/
def H1 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, let fan (r : ℝ) := ((X.erase a).powersetCard 2).filter fun B => OnCircleOfRadius (insert a B) r
           (∃ s : ℝ, 13 ≤ (fan s).card) →
           ∀ D ∈ (X.erase a).powersetCard 2, ∀ C : Finset ℝ, C.card = 3 →
           (∀ r ∈ C, 9 ≤ (fan r).card ∧ D ⊆ (fan r).biUnion id) →
           (∃ r ∈ C, OnCircleOfRadius (insert a D) r) → ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

/-- Each rich radius is witnessed at both base endpoints by triangles using a point outside the base. -/
def H2 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, let fan (r : ℝ) := ((X.erase a).powersetCard 2).filter fun B => OnCircleOfRadius (insert a B) r
           (∃ s : ℝ, 13 ≤ (fan s).card) →
           ∀ D ∈ (X.erase a).powersetCard 2, ∀ C : Finset ℝ, C.card = 3 →
           (∀ r ∈ C, 9 ≤ (fan r).card ∧ D ⊆ (fan r).biUnion id) →
           (∀ r ∈ C, ¬ OnCircleOfRadius (insert a D) r) → ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

theorem main : H1 → H2 → type_of% @Erdos827.erdos_827.variants.n_five_le := by
  classical
  intro onBase offBase
  apply n_le
  intro X hX gp
  obtain ⟨c,track,edges⟩ := OMA.CircumradiusOverlap.radius_coloring X gp
  by_contra no
  have thin (a) (ha : a ∈ X)
      (large : ∃ s : ℝ, 13 ≤ (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=s).card)
      (D) (hD : D ∈ (X.erase a).powersetCard 2) (C : Finset ℝ) (hC : C.card=3) :
      ¬ ∀ r∈C, let E := ((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r
               9 ≤ E.card ∧ D ⊆ E.biUnion id := by
    let fan (r : ℝ) := ((X.erase a).powersetCard 2).filter fun B => OnCircleOfRadius (insert a B) r
    have eq (r : ℝ) : ((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r) = fan r := by
      apply filter_congr
      intro B hb
      obtain ⟨sub,sz⟩ := mem_powersetCard.mp hb
      have ab : a∉B := fun h => notMem_erase a X (sub h)
      exact track _ (insert_subset ha (sub.trans (erase_subset ..))) (by rw [card_insert_of_notMem ab,sz]) r
    intro overlap
    obtain ⟨s,hs⟩ := large
    rw [eq] at hs
    have geo (r) (hr : r∈C) : 9 ≤ (fan r).card ∧ D ⊆ (fan r).biUnion id := by
      simpa only [eq] using overlap r hr
    by_cases base : ∃ r ∈ C, OnCircleOfRadius (insert a D) r
    · exact no (onBase X hX gp a ha ⟨s,hs⟩ D hD C hC geo base)
    · exact no (offBase X hX gp a ha ⟨s,hs⟩ D hD C hC geo (by simpa using base))
  obtain ⟨Y,yx,sy,inj⟩ := OMA.CircumradiusOverlap.rainbow_five X c hX edges thin
  apply no
  refine ⟨Y,yx,sy,?_⟩
  intro T ty U uy st su ne r hr hu
  exact ne (inj (mem_powersetCard.mpr ⟨ty,st⟩) (mem_powersetCard.mpr ⟨uy,su⟩)
    (((track T (ty.trans yx) st r).mpr hr).trans ((track U (uy.trans yx) su r).mpr hu).symm))

end OMA.R_Erdos827_erdos_827_variants_n_five_le_R2
