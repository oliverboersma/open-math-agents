import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Relabel the at most four configurations with at least three triple supports. -/


namespace WeightNineteenHighTripleCatalogue

open Finset
open scoped BigOperators

abbrev Support := Finset (Fin 6)
abbrev Family := Finset Support

def smallMask (s : Support) : Nat := ∑ a ∈ s, 2^a.val

def familyMask (s : Family) : Nat := ∑ a ∈ s, 2^(smallMask a)

def codeMap (code : Nat) (a : Fin 6) : Fin 6 :=
  ⟨((code >>> (3*a.val)) &&& 7) % 6, Nat.mod_lt _ (by decide)⟩

def move (code : Nat) (F : Family) : Family := F.image (Finset.image (codeMap code))

def canonicalTripleFamily (three : Bool) : Finset (Finset (Fin 6)) :=
  if three then {{0,1,2}, {0,3,4}, {1,3,5}} else {{0,1,2}, {0,3,4}, {1,3,5}, {2,4,5}}

lemma image_of_injective {X Y : Type} [DecidableEq Y] (f : X ↪ Y)
    [DecidableEq X] (A : Finset X) : A.image f = A.map f := by
  exact (Finset.map_eq_image _ _).symm

lemma moved_family (code : Nat) (injective : Function.Injective (codeMap code)) :
    ∃ e : Equiv.Perm (Fin 6), ∀ F : Family,
      move code F = F.image (Finset.map e.toEmbedding) := by
  let e := Equiv.ofBijective (codeMap code) ((Finite.injective_iff_bijective).mp injective)
  refine ⟨e,?_⟩
  intro F
  apply Finset.image_congr
  intro S _
  exact image_of_injective e.toEmbedding S

lemma map_support_overlap (e : Equiv.Perm (Fin 6)) (S U : Support) :
    (S.map e.toEmbedding ∩ U.map e.toEmbedding).card = (S ∩ U).card := by
  have both : S.map e.toEmbedding ∩ U.map e.toEmbedding = (S ∩ U).map e.toEmbedding := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_map_equiv]
  simp only [both,Finset.card_map]

lemma compose_moves (e f : Equiv.Perm (Fin 6)) (F : Family) :
    (F.image (Finset.map e.toEmbedding)).image (Finset.map f.toEmbedding) =
      F.image (Finset.map (e.trans f).toEmbedding) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S _
  rw [Function.comp_apply,Finset.map_map]
  rfl

lemma third_member (S : Support) (x y : Fin 6) (sx : x ∈ S) (sy : y ∈ S) (ne : x ≠ y)
    (three : S.card = 3) : ∃ p, p ≠ x ∧ p ≠ y ∧ p ∈ S ∧ S = {x,y,p} := by
  have on : {x,y} ⊆ S := Finset.insert_subset_iff.mpr ⟨sx,Finset.singleton_subset_iff.mpr sy⟩
  have one : (S \ {x,y}).card = 1 := by
    rw [Finset.card_sdiff_of_subset on,three,Finset.card_pair_eq_two_iff.mpr ne]
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp one
  have mem : p ∈ S \ {x,y} := hp ▸ Finset.mem_singleton_self _
  obtain ⟨onS,other⟩ := Finset.mem_sdiff.mp mem
  have different : p ≠ x ∧ p ≠ y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using other
  refine ⟨p,different.1,different.2,onS,?_⟩
  ext v
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro on_v
    by_cases vx : v = x
    · exact Or.inl vx
    by_cases vy : v = y
    · exact Or.inr (Or.inl vy)
    have single : v ∈ S \ {x,y} := Finset.mem_sdiff.mpr ⟨on_v,by simp [vx,vy]⟩
    rw [hp,Finset.mem_singleton] at single
    exact Or.inr (Or.inr single)
  · rintro (rfl | rfl | rfl)
    · exact sx
    · exact sy
    · exact onS

lemma intersection_three (A B C : Support) (a : A.card = 3) (b : B.card = 3) (c : C.card = 3)
    (ab : (A ∩ B).card ≤ 1) (ac : (A ∩ C).card ≤ 1) (bc : (B ∩ C).card ≤ 1) :
    (A ∩ B).card = 1 ∧ (A ∩ C).card = 1 ∧ (B ∩ C).card = 1 ∧
    (C ∩ (A ∪ B)).card = 2 := by
  have left := Finset.card_union_add_card_inter A B
  have right := Finset.card_union_add_card_inter C (A ∪ B)
  have maxUnion := (Finset.card_le_card (Finset.subset_univ (C ∪ (A ∪ B)))).trans_eq (Fintype.card_fin 6)
  have shape : C ∩ (A ∪ B) = (A ∩ C) ∪ (B ∩ C) := by
    ext z
    simp only [Finset.mem_union,Finset.mem_inter]
    tauto
  have cap : (C ∩ (A ∪ B)).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [shape]
    exact Finset.card_union_le _ _
  omega

lemma move_three (A B C : Support) (a : A.card = 3) (b : B.card = 3) (c : C.card = 3)
    (ab : (A ∩ B).card ≤ 1) (ac : (A ∩ C).card ≤ 1) (bc : (B ∩ C).card ≤ 1) :
    ∃ e : Equiv.Perm (Fin 6), A.map e.toEmbedding = {0,1,2} ∧
      B.map e.toEmbedding = {0,3,4} ∧ C.map e.toEmbedding = {1,3,5} := by
  obtain ⟨oneAB,oneAC,oneBC,cross⟩ := intersection_three A B C a b c ab ac bc
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp oneAB
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp oneAC
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp oneBC
  have pair_x : x ∈ A ∧ x ∈ B := Finset.mem_inter.mp (hx ▸ Finset.mem_singleton_self _)
  have pair_y : y ∈ A ∧ y ∈ C := Finset.mem_inter.mp (hy ▸ Finset.mem_singleton_self _)
  have pair_z : z ∈ B ∧ z ∈ C := Finset.mem_inter.mp (hz ▸ Finset.mem_singleton_self _)
  have identifyX (v : Fin 6) (vA : v ∈ A) (vB : v ∈ B) : v = x := by
    have both : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨vA,vB⟩
    rwa [hx,Finset.mem_singleton] at both
  have identifyY (v : Fin 6) (vA : v ∈ A) (vC : v ∈ C) : v = y := by
    have both : v ∈ A ∩ C := Finset.mem_inter.mpr ⟨vA,vC⟩
    rwa [hy,Finset.mem_singleton] at both
  have identifyZ (v : Fin 6) (vB : v ∈ B) (vC : v ∈ C) : v = z := by
    have both : v ∈ B ∩ C := Finset.mem_inter.mpr ⟨vB,vC⟩
    rwa [hz,Finset.mem_singleton] at both
  have yz : y ≠ z := by
    intro eq
    have shape : C ∩ (A ∪ B) = (A ∩ C) ∪ (B ∩ C) := by
      ext v
      simp only [Finset.mem_union,Finset.mem_inter]
      tauto
    rw [shape,hy,hz,eq,Finset.union_self,Finset.card_singleton] at cross
    omega
  have xy : x ≠ y := by
    intro eq
    exact yz (identifyZ y (eq ▸ pair_x.2) pair_y.2)
  have xz : x ≠ z := by
    intro eq
    exact yz ((identifyY z (eq ▸ pair_x.1) pair_z.2).symm)
  obtain ⟨u,ux,uy,uA,formA⟩ := third_member A x y pair_x.1 pair_y.1 xy a
  obtain ⟨v,vx,vz,vB,formB⟩ := third_member B x z pair_x.2 pair_z.1 xz b
  obtain ⟨w,wy,wz,wC,formC⟩ := third_member C y z pair_y.2 pair_z.2 yz c
  have uz : u ≠ z := fun eq => ux (identifyX u uA (eq.symm ▸ pair_z.1))
  have vy : v ≠ y := fun eq => vx (identifyX v (eq.symm ▸ pair_y.1) vB)
  have wx : w ≠ x := fun eq => wy (identifyY w (eq.symm ▸ pair_x.1) wC)
  have uv : u ≠ v := fun eq => ux (identifyX u uA (eq.symm ▸ vB))
  have uw : u ≠ w := fun eq => uy (identifyY u uA (eq.symm ▸ wC))
  have vw : v ≠ w := fun eq => vz (identifyZ v vB (eq.symm ▸ wC))
  let f (n : Fin 6) : Fin 6 := [x,y,u,z,v,w][n.val]!
  have inj : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,xy,xz,yz,ux,uy,uz,vx,vy,vz,wx,wy,wz,uv,uw,vw,
        Ne.symm xy,Ne.symm xz,Ne.symm yz,Ne.symm ux,Ne.symm uy,Ne.symm uz,
        Ne.symm vx,Ne.symm vy,Ne.symm vz,Ne.symm wx,Ne.symm wy,Ne.symm wz,
        Ne.symm uv,Ne.symm uw,Ne.symm vw]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
  have imageA : ({0,1,2} : Support).map e.toEmbedding = A := by
    rw [formA,Finset.map_insert,Finset.map_insert,Finset.map_singleton]
    rfl
  have imageB : ({0,3,4} : Support).map e.toEmbedding = B := by
    rw [formB,Finset.map_insert,Finset.map_insert,Finset.map_singleton]
    rfl
  have imageC : ({1,3,5} : Support).map e.toEmbedding = C := by
    rw [formC,Finset.map_insert,Finset.map_insert,Finset.map_singleton]
    rfl
  have inverse (S T : Support) (image : T.map e.toEmbedding = S) : S.map e.symm.toEmbedding = T := by
    ext i
    rw [Finset.mem_map_equiv,Equiv.symm_symm,← image,Finset.mem_map_equiv,e.symm_apply_apply]
  exact ⟨e.symm,inverse _ _ imageA,inverse _ _ imageB,inverse _ _ imageC⟩

lemma canonical_three : canonicalTripleFamily true = ({{0,1,2},{0,3,4},{1,3,5}} : Family) := rfl

lemma canonical_four : canonicalTripleFamily false =
    insert ({2,4,5} : Support) (canonicalTripleFamily true) := by decide +kernel

lemma checked_fourth : ∀ D ∈ (Finset.univ : Support).powersetCard 3,
    D ∉ canonicalTripleFamily true →
    (∀ U ∈ canonicalTripleFamily true, (D ∩ U).card ≤ 1) → D = {2,4,5} := by
  have h : ∀ D : ↥((Finset.univ : Support).powersetCard 3),
      D.val ∉ canonicalTripleFamily true →
      (∀ U : ↥(canonicalTripleFamily true), (D.val ∩ U.val).card ≤ 1) →
        D.val = {2,4,5} := by decide +kernel
  exact fun D hd new fits => h ⟨D,hd⟩ new (fun U => fits U.val U.property)

lemma fourth_choice (D : Support) (size : D.card = 3) (new : D ∉ canonicalTripleFamily true)
    (fits : ∀ U ∈ canonicalTripleFamily true, (D ∩ U).card ≤ 1) : D = {2,4,5} :=
  checked_fourth D (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,size⟩) new fits

lemma triple_normal (three : Bool) (T : Family)
    (cardT : T.card = if three then 3 else 4)
    (size : ∀ U ∈ T, U.card = 3)
    (overlap : ∀ U ∈ T, ∀ V ∈ T, U ≠ V → (U ∩ V).card ≤ 1) :
    ∃ e : Equiv.Perm (Fin 6), T.image (Finset.map e.toEmbedding) = canonicalTripleFamily three := by
  have enough : 3 ≤ T.card := by cases three <;> simp_all
  obtain ⟨first,subset,threeSize⟩ := Finset.exists_subset_card_eq enough
  obtain ⟨A,B,C,ab,ac,bc,form⟩ := Finset.card_eq_three.mp threeSize
  have hA : A ∈ T := subset (form.symm ▸ Finset.mem_insert_self _ _)
  have hB : B ∈ T := subset (form.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hC : C ∈ T := subset (form.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨e,imA,imB,imC⟩ := move_three A B C (size A hA) (size B hB) (size C hC)
    (overlap A hA B hB ab) (overlap A hA C hC ac) (overlap B hB C hC bc)
  let T' := T.image (Finset.map e.toEmbedding)
  have first_norm : first.image (Finset.map e.toEmbedding) = canonicalTripleFamily true := by
    rw [form,Finset.image_insert,Finset.image_insert,Finset.image_singleton,imA,imB,imC,canonical_three]
  have sub' : canonicalTripleFamily true ⊆ T' := by
    rw [← first_norm]
    exact Finset.image_subset_image subset
  have sizes : T'.card = T.card := Finset.card_image_of_injective _ (Finset.map_injective _)
  have threeCount : (canonicalTripleFamily true).card = 3 := by decide +kernel
  refine ⟨e,?_⟩
  change T' = _
  cases three with
  | true =>
    exact (Finset.eq_of_subset_of_card_le sub' (by rw [sizes,cardT,threeCount]; decide)).symm
  | false =>
    have one : (T' \ canonicalTripleFamily true).card = 1 := by
      rw [Finset.card_sdiff_of_subset sub',sizes,cardT,threeCount]
      decide
    obtain ⟨D,formD⟩ := Finset.card_eq_one.mp one
    have memD : D ∈ T' \ canonicalTripleFamily true := formD ▸ Finset.mem_singleton_self _
    obtain ⟨onD,new⟩ := Finset.mem_sdiff.mp memD
    obtain ⟨P,hP,moveP⟩ := Finset.mem_image.mp onD
    have sizeD : D.card = 3 := by rw [← moveP,Finset.card_map,size P hP]
    have compatible (U : Support) (onU : U ∈ canonicalTripleFamily true) : (D ∩ U).card ≤ 1 := by
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (sub' onU)
      have diff : P ≠ Q := fun same => new ((same ▸ moveP) ▸ onU)
      rw [← moveP,map_support_overlap]
      exact overlap P hP Q hQ diff
    have determined := fourth_choice D sizeD new compatible
    rw [canonical_four,← determined]
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨onD,sub'⟩) ?_
    rw [Finset.card_insert_of_notMem new,threeCount,sizes,cardT]
    decide

end WeightNineteenHighTripleCatalogue


namespace WeightNineteenHighTripleCatalogue

open Finset

def admissiblePairs (T : Family) : Family :=
  ((Finset.univ : Support).powersetCard 2).filter fun P => ∀ S ∈ T, ¬ P ⊆ S

def candidates (three : Bool) : Finset Family :=
  let E := admissiblePairs (canonicalTripleFamily three)
  if three then E.powersetCard 5 ∪ E.powersetCard 6 else E.powersetCard 3

def layoutPatterns (i : Fin 4) : Family :=
  let T := canonicalTripleFamily true
  let S := canonicalTripleFamily false
  let A := admissiblePairs T
  let B := admissiblePairs S
  ([T ∪ A,T ∪ A.erase {2,3},T ∪ A.erase {2,4},S ∪ B] : List Family)[i.val]!

def symmetries : List Nat := [0x2c688, 0x2a318, 0x25681, 0x22159, 0x15303, 0x1414b]

def pairCheck (three : Bool) (P : Family) : Prop :=
  ∃ word ∈ symmetries, (∀ a b : Fin 6, codeMap word a = codeMap word b → a = b) ∧
    ∃ i : Fin 4, move word (canonicalTripleFamily three ∪ P) = layoutPatterns i

instance (three : Bool) (P : Family) : Decidable (pairCheck three P) := by
  unfold pairCheck
  infer_instance

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 4096 in
lemma check_pair_moves : ∀ three : Bool, ∀ P ∈ candidates three, pairCheck three P := by
  have h : ∀ three : Bool, ∀ P : ↥(candidates three), pairCheck three P.val := by decide +kernel
  exact fun three P hP => h three ⟨P,hP⟩

lemma image_eq_card (e : Equiv.Perm (Fin 6)) (F : Family) :
    (F.image (Finset.map e.toEmbedding)).card = F.card :=
  Finset.card_image_of_injective _ (Finset.map_injective _)

theorem normalize_high_triples (F : Family) (three : Bool)
    (sizes : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ 3)
    (overlap : ∀ S ∈ F, ∀ U ∈ F, S ≠ U → (S ∩ U).card ≤ 1)
    (tSize : (F.filter fun S => S.card = 3).card = if three then 3 else 4)
    (pSize : let P := (F.filter fun S => S.card = 2).card
      if three then P = 5 ∨ P = 6 else P = 3) :
    ∃ (e : Equiv.Perm (Fin 6)) (i : Fin 4),
      F.image (Finset.map e.toEmbedding) = layoutPatterns i := by
  let T := F.filter fun S => S.card = 3
  let P := F.filter fun S => S.card = 2
  have union : F = T ∪ P := by
    ext S
    simp only [T,P,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro hS
      have interval := sizes S hS
      by_cases h : S.card = 3
      · exact Or.inl ⟨hS,h⟩
      · exact Or.inr ⟨hS,by omega⟩
    · rintro (⟨hS,_⟩ | ⟨hS,_⟩) <;> exact hS
  obtain ⟨e,tNormal⟩ := triple_normal three T tSize (fun t ht => (Finset.mem_filter.mp ht).2)
    (fun t ht s hs ne => overlap _ (Finset.mem_filter.mp ht).1 _ (Finset.mem_filter.mp hs).1 ne)
  let P' := P.image (Finset.map e.toEmbedding)
  have pairCount : P'.card = P.card := image_eq_card e P
  have pNormal : P' ⊆ admissiblePairs (canonicalTripleFamily three) := by
    intro s hs
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
    have two : u.card = 2 := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by simpa using two⟩,?_⟩
    intro S hS cover
    rw [← tNormal] at hS
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
    have three : v.card = 3 := (Finset.mem_filter.mp hv).2
    have diff : u ≠ v := fun eq => by rw [eq] at two; omega
    have small := overlap u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 diff
    have subset : u ⊆ v := by
      intro a ha
      have mapped := cover (Finset.mem_map_of_mem _ ha)
      rw [Finset.mem_map_equiv] at mapped
      simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using mapped
    rw [Finset.inter_eq_left.mpr subset] at small
    omega
  have listed : P' ∈ candidates three := by
    cases three
    · change P' ∈ (admissiblePairs (canonicalTripleFamily false)).powersetCard 3
      exact Finset.mem_powersetCard.mpr ⟨pNormal,pairCount.trans pSize⟩
    · change P' ∈ (admissiblePairs (canonicalTripleFamily true)).powersetCard 5 ∪
        (admissiblePairs (canonicalTripleFamily true)).powersetCard 6
      apply Finset.mem_union.mpr
      rcases pSize with h | h
      · exact Or.inl (Finset.mem_powersetCard.mpr ⟨pNormal,pairCount.trans h⟩)
      · exact Or.inr (Finset.mem_powersetCard.mpr ⟨pNormal,pairCount.trans h⟩)
  obtain ⟨word,_,injective,i,final⟩ := check_pair_moves three P' listed
  obtain ⟨f,computed⟩ := moved_family word injective
  have firstMove : F.image (Finset.map e.toEmbedding) = canonicalTripleFamily three ∪ P' := by
    rw [union,Finset.image_union,tNormal]
  refine ⟨e.trans f,i,?_⟩
  rw [computed,← firstMove,Finset.image_image] at final
  convert final using 1
  apply Finset.image_congr
  intro s _
  rw [Function.comp_apply,Finset.map_map]
  rfl

end WeightNineteenHighTripleCatalogue


namespace WeightNineteenSupportRelabel

open Finset
open scoped BigOperators

abbrev Columns := Fin 19 → Finset (Fin 6)

def shared (C : Columns) : Finset (Fin 19) :=
  Finset.univ.filter fun p => 2 ≤ (C p).card

def layout (C : Columns) : Finset (Finset (Fin 6)) :=
  (shared C).image C

def fiber (C : Columns) (s : Finset (Fin 6)) : Finset (Fin 19) :=
  Finset.univ.filter fun p => C p = s

lemma mem_fiber (C : Columns) (s : Finset (Fin 6)) (p : Fin 19) :
    p ∈ fiber C s ↔ C p = s := by simp [fiber]

lemma injective_shared (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    (shared C : Set (Fin 19)).InjOn C := by
  intro p hp q hq same
  by_contra different
  have small := overlap p q different
  rw [same,Finset.inter_self] at small
  have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  omega

lemma high_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (s : Finset (Fin 6)) (many : 2 ≤ s.card) :
    (fiber C s).card = if s ∈ layout C then 1 else 0 := by
  by_cases yes : s ∈ layout C
  · rw [if_pos yes]
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp yes
    apply Finset.card_eq_one.mpr
    refine ⟨p,?_⟩
    ext q
    rw [mem_fiber,Finset.mem_singleton]
    constructor
    · intro hs
      have hq : q ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
      exact injective_shared C overlap hq hp (hs.trans eq.symm)
    · rintro rfl
      exact eq
  · rw [if_neg yes]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hs := (mem_fiber C s p).mp hp
    have here : p ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
    exact yes (hs ▸ Finset.mem_image_of_mem C here)

lemma single_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (a : Fin 6) :
    (fiber C {a}).card + ((layout C).filter fun s => a ∈ s).card =
      (Finset.univ.filter fun p => a ∈ C p).card := by
  let high := (shared C).filter fun p => a ∈ C p
  have image_high : high.image C = (layout C).filter fun s => a ∈ s := by
    ext s
    constructor
    · rintro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨sharedp,one⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ sharedp,one⟩
    · rintro hs
      obtain ⟨in_layout,one⟩ := Finset.mem_filter.mp hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp in_layout
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,one⟩,rfl⟩
  have inj : (high : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    exact injective_shared C overlap (Finset.filter_subset _ _ hp) (Finset.filter_subset _ _ hq) same
  have high_count := Finset.card_image_of_injOn inj
  rw [image_high] at high_count
  have apart : Disjoint (fiber C {a}) high := by
    rw [Finset.disjoint_left]
    intro p hf hp
    have hs := (mem_fiber C {a} p).mp hf
    have many := (Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).2
    rw [hs,Finset.card_singleton] at many
    omega
  have cover : fiber C {a} ∪ high = Finset.univ.filter fun p => a ∈ C p := by
    ext p
    rw [Finset.mem_union, mem_fiber]
    have hit : p ∈ (Finset.univ.filter fun p => a ∈ C p) ↔ a ∈ C p := by simp
    rw [hit]
    constructor
    · rintro (one | above)
      · rw [one]
        simp
      · exact (Finset.mem_filter.mp above).2
    · intro on_a
      by_cases many : 2 ≤ (C p).card
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p,many⟩,on_a⟩)
      · apply Or.inl
        symm
        apply Finset.eq_of_subset_of_card_le ((Finset.singleton_subset_iff).mpr on_a)
        rw [Finset.card_singleton]
        omega
  rw [high_count,← Finset.card_union_of_disjoint apart,cover]

lemma sum_fibers (C : Columns) : (∑ s : Finset (Fin 6), (fiber C s).card) = 19 := by
  calc
    _ = ∑ s : Finset (Fin 6), ∑ p : Fin 19, if C p = s then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [fiber]
    _ = ∑ p : Fin 19, ∑ s : Finset (Fin 6), if C p = s then (1 : Nat) else 0 := Finset.sum_comm
    _ = 19 := by simp [eq_comm]

theorem relabel_columns (C D : Columns)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (same : layout C = layout D) :
    ∃ e : Equiv.Perm (Fin 19), ∀ p, D (e p) = C p := by
  classical
  have counts_ne (s : Finset (Fin 6)) (nonzero : s ≠ ∅) : (fiber C s).card = (fiber D s).card := by
    by_cases large : 2 ≤ s.card
    · rw [high_fiber C c_overlap s large,high_fiber D d_overlap s large,same]
    · have pos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonzero)
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      have left := single_fiber C c_overlap a
      have right := single_fiber D d_overlap a
      rw [same,c_row] at left
      rw [d_row] at right
      omega
  have all_counts (s : Finset (Fin 6)) : (fiber C s).card = (fiber D s).card := by
    by_cases zero : s = ∅
    · subst s
      let nonempty := (Finset.univ : Finset (Finset (Fin 6))).erase ∅
      have agree : (∑ s ∈ nonempty, (fiber C s).card) = ∑ s ∈ nonempty, (fiber D s).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact counts_ne s (Finset.ne_of_mem_erase hs)
      have hc := Finset.sum_erase_add Finset.univ (fun s => (fiber C s).card) (Finset.mem_univ ∅)
      have hd := Finset.sum_erase_add Finset.univ (fun s => (fiber D s).card) (Finset.mem_univ ∅)
      rw [sum_fibers] at hc hd
      change (∑ s ∈ nonempty, (fiber C s).card) + (fiber C ∅).card = 19 at hc
      change (∑ s ∈ nonempty, (fiber D s).card) + (fiber D ∅).card = 19 at hd
      omega
    · exact counts_ne s zero
  let match_card (s : Finset (Fin 6)) : Fintype.card ↥(fiber C s) = Fintype.card ↥(fiber D s) := by
    rw [Fintype.card_coe,Fintype.card_coe,all_counts]
  let fibers (s : Finset (Fin 6)) : ↥(fiber C s) ≃ ↥(fiber D s) :=
    (Fintype.equivOfCardEq (match_card s))
  let as_fiber (W : Columns) (s : Finset (Fin 6)) : {p // W p = s} ≃ ↥(fiber W s) :=
    Equiv.subtypeEquivProp (funext fun p => propext (mem_fiber W s p).symm)
  let mapped (s : Finset (Fin 6)) : {p // C p = s} ≃ {p // D p = s} :=
    ((as_fiber C s).trans (fibers s)).trans (as_fiber D s).symm
  let e : Equiv.Perm (Fin 19) :=
    (Equiv.sigmaFiberEquiv C).symm.trans
      ((Equiv.sigmaCongrRight mapped).trans (Equiv.sigmaFiberEquiv D))
  exact ⟨e,fun p => (mapped (C p) ⟨p,rfl⟩).property⟩

end WeightNineteenSupportRelabel

namespace WeightNineteenFourNormalize

open Finset WeightNineteenSupportRelabel

def transform (e : Equiv.Perm (Fin 6)) : Finset (Fin 6) ↪ Finset (Fin 6) :=
  (Finset.mapEmbedding e.toEmbedding).toEmbedding

def relabel (C : Columns) (e : Equiv.Perm (Fin 6)) : Columns :=
  fun p => (C p).map e.toEmbedding

lemma layout_relabel (C : Columns) (e : Equiv.Perm (Fin 6)) :
    layout (relabel C e) = (layout C).map (transform e) := by
  have same : shared (relabel C e) = shared C := by
    ext p
    simp only [shared,Finset.mem_filter,relabel,Finset.card_map]
  unfold layout
  rw [same,Finset.map_eq_image,Finset.image_image]
  rfl

theorem use_canonical_columns (C D : Columns) (e : Equiv.Perm (Fin 6))
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (rows : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (targetOverlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (targetRows : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (matched : (layout C).map (transform e) = layout D) :
    ∃ π : Equiv.Perm (Fin 19), ∀ p, relabel C e (π p) = D p := by
  have movedOverlap (p q : Fin 19) (different : p ≠ q) :
      (relabel C e p ∩ relabel C e q).card ≤ 1 := by
    have same : relabel C e p ∩ relabel C e q = (C p ∩ C q).map e.toEmbedding := by
      ext a
      simp only [relabel,Finset.mem_inter,Finset.mem_map_equiv]
    rw [same,Finset.card_map]
    exact overlap p q different
  have movedRows (a : Fin 6) : (Finset.univ.filter fun p => a ∈ relabel C e p).card = 5 := by
    have same : (Finset.univ.filter fun p => a ∈ relabel C e p) =
        Finset.univ.filter fun p => e.symm a ∈ C p := by
      ext p
      simp only [relabel,Finset.mem_filter,Finset.mem_map_equiv]
    rw [same,rows]
  obtain ⟨π,form⟩ := relabel_columns (relabel C e) D movedOverlap targetOverlap movedRows targetRows
    ((layout_relabel C e).trans matched)
  exact ⟨π.symm,fun p => by simpa only [Equiv.apply_symm_apply] using (form (π.symm p)).symm⟩

end WeightNineteenFourNormalize

namespace WeightNineteenHighTripleTables

open Finset WeightNineteenSupportRelabel WeightNineteenHighTripleCatalogue

def columns (i : Fin 4) (p : Fin 19) := ((([[[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 3], [2, 4], [2, 5], [4, 5], [0], [0], [1], [1], [2], [3], [3], [4], [5], []], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 4], [2, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], [3], [4], [5]], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [0, 5], [1, 4], [2, 3], [2, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], [4], [4], [5]], [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5], [0, 5], [1, 4], [2, 3], [0], [0], [1], [1], [2], [2], [3], [3], [4], [4], [5], [5]]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset

lemma shared_disjoint : ∀ i : Fin 4, ∀ p ∈ shared (columns i), ∀ q ∈ shared (columns i),
    p ≠ q → (columns i p ∩ columns i q).card ≤ 1 := by
  have checked : ∀ i : Fin 4, ∀ p q : ↥(shared (columns i)),
      p ≠ q → (columns i p.val ∩ columns i q.val).card ≤ 1 := by decide +kernel
  exact fun i p hp q hq different =>
    checked i ⟨p,hp⟩ ⟨q,hq⟩ (fun equal => different (congrArg Subtype.val equal))

lemma targetOverlap (i : Fin 4) (p q : Fin 19) (different : p ≠ q) :
    (columns i p ∩ columns i q).card ≤ 1 := by
  by_cases hp : p ∈ shared (columns i)
  · by_cases hq : q ∈ shared (columns i)
    · exact shared_disjoint i p hp q hq different
    · have small : ¬ 2 ≤ (columns i q).card := by simpa [shared] using hq
      exact (Finset.card_le_card Finset.inter_subset_right).trans (by omega)
  · have small : ¬ 2 ≤ (columns i p).card := by simpa [shared] using hp
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by omega)

lemma targetRows : ∀ i : Fin 4, ∀ a : Fin 6,
    (Finset.univ.filter fun p => a ∈ columns i p).card = 5 := by decide +kernel

lemma targetLayouts : ∀ i : Fin 4, layout (columns i) = layoutPatterns i := by decide +kernel

end WeightNineteenHighTripleTables



open Finset WeightNineteenHighTripleCatalogue WeightNineteenSupportRelabel WeightNineteenFourNormalize

set_option maxRecDepth 12000 in
set_option maxHeartbeats 25000000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1.H1 := by
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1.H1
  dsimp only
  intro C overlap rows maxSize counts
  let F := layout C
  have sizes (V : Finset (Fin 6)) (hv : V ∈ F) : 2 ≤ V.card ∧ V.card ≤ 3 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(Finset.mem_filter.mp hp).2,maxSize p⟩
  have separated (V : Finset (Fin 6)) (hv : V ∈ F) (W : Finset (Fin 6)) (hw : W ∈ F)
      (different : V ≠ W) : (V ∩ W).card ≤ 1 := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hw
    exact overlap p q (fun eq => different (congrArg C eq))
  have normalized : ∃ e : Equiv.Perm (Fin 6), ∃ i : Fin 4,
      F.image (Finset.map e.toEmbedding) = layoutPatterns i := by
    rcases counts with ⟨three,minPairs,maxPairs⟩ | ⟨four,threePairs⟩
    · have range : (F.filter fun s => s.card = 2).card = 5 ∨ (F.filter fun s => s.card = 2).card = 6 := by
        change 5 ≤ (F.filter fun s => s.card = 2).card at minPairs
        change (F.filter fun s => s.card = 2).card ≤ 6 at maxPairs
        omega
      exact normalize_high_triples F true sizes separated three range
    · exact normalize_high_triples F false sizes separated four threePairs
  obtain ⟨e,i,moved⟩ := normalized
  let D := WeightNineteenHighTripleTables.columns
  have matched : (layout C).map (transform e) = layout (D i) := by
    rw [Finset.map_eq_image,WeightNineteenHighTripleTables.targetLayouts]
    exact moved
  obtain ⟨π,relabeled⟩ := use_canonical_columns C (D i) e overlap rows (WeightNineteenHighTripleTables.targetOverlap i) (WeightNineteenHighTripleTables.targetRows i) matched
  exact ⟨i,e,π,relabeled⟩

