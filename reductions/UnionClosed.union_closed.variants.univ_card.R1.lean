import FormalConjectures.Wikipedia.UnionClosed
import Mathlib

/-! # Weighted certificates for the twelve-element case
A surjection duplicates active coordinates until there are exactly twelve,
preserving family size and every copied coordinate's frequency. A singleton
or doublet supplies an injection from sets missing both coordinates to sets
containing both. If all nonempty sets have size at least six, the full set
pays for the empty set in the uniform incidence count. The remaining finite
weight certificates are the three small-generator cases of Vučković and
Živković, The 12-Element Case of Frankl's Conjecture (2017), Lemma 4 and
Table I, especially rows 25, 32, and 33. -/

namespace OMA.R_UnionClosed_union_closed_variants_univ_card_R1
open Finset UnionClosed
open scoped Classical

-- The 3-element minimum case on the fixed twelve-coordinate universe.
def H1 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, S.card = 3) → (∀ S ∈ F, S.Nonempty → 3 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- The 4-element minimum case on the fixed twelve-coordinate universe.
def H2 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, S.card = 4) → (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- The 5-element minimum case on the fixed twelve-coordinate universe.
def H3 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧ S.card=5 ∧ T.card=5) → (∀ S ∈ F, S.Nonempty → 5 ≤ S.card) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)


lemma incidence (F : Finset (Finset (Fin 12))) (w : Fin 12 → ℕ) :
    (∑ S ∈ F, ∑ i ∈ S, w i) = ∑ i, w i*(F.filter (i ∈ ·)).card := by
  calc
    _ = ∑ S ∈ F, ∑ i : Fin 12, if i ∈ S then w i else 0 := by simp
    _ = ∑ i : Fin 12, ∑ S ∈ F, if i ∈ S then w i else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [←sum_filter]
      simp [Nat.mul_comm]

lemma witness (F : Finset (Finset (Fin 12))) (w : Fin 12 → ℕ) (wp : 0 < ∑ i, w i)
    (hw : F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)) :
    ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  by_contra! fail
  have h := sum_le_sum (s:=univ) (fun (i : Fin 12) _ =>
    Nat.mul_le_mul_left (w i) (show 2*(F.filter (i ∈ ·)).card + 1 ≤ F.card from fail i))
  simp only [mul_add,mul_one,sum_add_distrib,←sum_mul] at h
  rw [incidence] at hw
  have twice : (∑ i, w i*(2*(F.filter (i ∈ ·)).card)) =
      2*(∑ i, w i*(F.filter (i ∈ ·)).card) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
  rw [twice,mul_comm (∑ i, w i) F.card] at h
  omega

lemma small_member (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (a b : Fin 12) (pair : {a,b} ∈ F) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  let A := F.filter (a ∈ ·)
  let B := F.filter (b ∈ ·)
  let none := F \ (A∪B)
  have fromNone {X : Finset (Fin 12)} (hX : X ∈ none) : X ∈ F ∧ a ∉ X ∧ b ∉ X := by
    have h := mem_sdiff.mp hX
    simpa [A,B,h.1] using h
  have inj : none.card ≤ (A∩B).card := by
    apply card_le_card_of_injOn (fun X => X∪{a,b})
    · intro X hX
      obtain ⟨xf,_,_⟩ := fromNone hX
      have u := closed _ xf _ pair
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨u,by simp⟩,mem_filter.mpr ⟨u,by simp⟩⟩
    · intro X hX Y hY eq
      have x := fromNone hX
      have y := fromNone hY
      ext i
      by_cases ia : i=a
      · simp [ia,x.2.1,y.2.1]
      by_cases ib : i=b
      · simp [ib,x.2.2,y.2.2]
      simpa [ia,ib] using Finset.ext_iff.mp eq i
  have sub : A∪B ⊆ F := union_subset (filter_subset _ _) (filter_subset _ _)
  have partition := card_sdiff_add_card_eq_card sub
  have overlap := card_union_add_card_inter A B
  change none.card + (A∪B).card = F.card at partition
  by_cases h : F.card ≤ 2*A.card
  · exact ⟨a,h⟩
  · exact ⟨b,by change F.card ≤ 2*B.card; omega⟩

lemma large_members (F : Finset (Finset (Fin 12))) (empty : ∅ ∈ F) (full : univ ∈ F)
    (hl : ∀ S ∈ F, S.Nonempty → 6 ≤ S.card) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  let M := (F.erase ∅).erase univ
  have ef : (univ : Finset (Fin 12)) ≠ ∅ := univ_nonempty.ne_empty
  have nu : univ ∉ M := notMem_erase _ _
  have ne : ∅ ∉ M := fun h => (notMem_erase ∅ F) (mem_of_mem_erase h)
  have hsplit : F = insert ∅ (insert univ M) := by
    dsimp [M]; rw [insert_erase (mem_erase.mpr ⟨ef,full⟩), insert_erase empty]
  have sum : 6*M.card ≤ ∑ S ∈ M, S.card := by
    have h := sum_le_sum (s:=M) (f:=fun _ => 6) (g:=Finset.card) (fun S hS =>
      hl S (mem_of_mem_erase (mem_of_mem_erase hS)) (nonempty_iff_ne_empty.mpr (mem_erase.mp (mem_of_mem_erase hS)).1))
    simpa [Nat.mul_comm] using h
  apply witness F (fun _ => 1) (by simp)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one]
  have n0 : (∅ : Finset (Fin 12)) ∉ insert univ M := by simp [ef.symm,ne]
  rw [hsplit,card_insert_of_notMem n0,card_insert_of_notMem nu,sum_insert n0,sum_insert nu]
  simp only [card_empty,card_univ,Fintype.card_fin,zero_add]
  omega

-- With a unique five-set, one proper member of size at least seven
-- balances its one-unit deficit. Without such a member every nonempty
-- set contains the five-set: a six-set missing it would make a union
-- of size between seven and eleven.
lemma unique_five (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅∈F) (full : univ∈F) (low : ∀ X ∈ F, X.Nonempty → 5 ≤ X.card)
    (S : Finset (Fin 12)) (sf : S∈F) (sc : S.card=5)
    (only : ∀ X ∈ F, X.card=5 → X=S) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  have se : S ≠ ∅ := by intro h; simp [h] at sc
  have su : S ≠ univ := by intro h; simp [h] at sc
  have ue : (univ : Finset (Fin 12)) ≠ ∅ := univ_nonempty.ne_empty
  by_cases big : ∃ Y ∈ F, Y≠univ ∧ 7≤Y.card
  · obtain ⟨Y,yf,yu,yc⟩ := big
    have ye : Y≠∅ := by intro e; simp [e] at yc
    have ys : Y≠S := by intro e; rw [e,sc] at yc; omega
    let P := (((F.erase ∅).erase univ).erase S).erase Y
    have sm : S ∈ (F.erase ∅).erase univ := mem_erase.mpr ⟨su,mem_erase.mpr ⟨se,sf⟩⟩
    have ym : Y ∈ ((F.erase ∅).erase univ).erase S := mem_erase.mpr ⟨ys,mem_erase.mpr ⟨yu,mem_erase.mpr ⟨ye,yf⟩⟩⟩
    have allp : 6*P.card ≤ ∑ X ∈ P, X.card := by
      have bound (X) (h : X ∈ P) : 6 ≤ X.card := by
        simp only [P,mem_erase] at h
        have l := low X h.2.2.2.2 (nonempty_iff_ne_empty.mpr h.2.2.2.1)
        have ne := h.2.1
        by_contra! no
        exact ne (only X h.2.2.2.2 (by omega))
      have := sum_le_sum (s:=P) (f:=fun _ => 6) (g:=Finset.card) bound
      simpa [Nat.mul_comm] using this
    have pe : ∅∉P := by simp [P]
    have pu : univ∉P := by simp [P]
    have ps : S∉P := by simp [P]
    have py : Y∉P := notMem_erase _ _
    have split : F=insert ∅ (insert univ (insert S (insert Y P))) := by
      dsimp [P]; rw [insert_erase ym,insert_erase sm,insert_erase (mem_erase.mpr ⟨ue,full⟩),insert_erase empty]
    apply witness F (fun _ => 1) (by simp)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one]
    rw [split]
    simp [pe,pu,ps,py,se.symm,su.symm,ue.symm,ye.symm,yu.symm,ys.symm,sc]
    omega
  · have all (X) (hX : X∈F) (ne : X.Nonempty) : S⊆X := by
      by_cases whole : X=univ
      · simp [whole]
      by_cases five : X.card=5
      · rw [only X hX five]
      have c := low X hX ne
      have upper : X.card<7 := by by_contra! no; exact big ⟨X,hX,whole,no⟩
      have six : X.card=6 := by omega
      by_contra no
      have sub : X ⊂ X∪S := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,fun eq => by
        have h : S ⊆ X∪S := subset_union_right
        rw [←eq] at h
        exact no h⟩
      have high := card_lt_card sub
      have cap := card_union_le X S
      have proper : X∪S≠univ := by intro eq; rw [eq] at cap; simp [six,sc] at cap
      exact big ⟨X∪S,closed _ hX _ sf,proper,by omega⟩
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr se
    have subset : F.erase ∅ ⊆ F.filter (i∈·) := by
      intro X hX
      exact mem_filter.mpr ⟨mem_of_mem_erase hX,all X (mem_of_mem_erase hX) (nonempty_iff_ne_empty.mpr (mem_erase.mp hX).1) hi⟩
    have h := card_le_card subset
    have p : 0 < (F.erase ∅).card := card_pos.mpr ⟨S,mem_erase.mpr ⟨se,sf⟩⟩
    have eq := card_erase_add_one empty
    exact ⟨i,by omega⟩

lemma twelve (h₃ : H1) (h₄ : H2) (h₅ : H3) (F : Finset (Finset (Fin 12)))
    (closed : IsUnionClosed F) (empty : ∅∈F) (full : univ∈F) : ∃ i, F.card ≤ 2*(F.filter (i ∈ ·)).card := by
  by_cases small : ∃ S ∈ F, S.Nonempty ∧ S.card ≤ 2
  · obtain ⟨S,hS,ne,le⟩ := small
    by_cases one : S.card=1
    · obtain ⟨a,rfl⟩ := card_eq_one.mp one
      exact small_member F closed a a (by simpa using hS)
    · obtain ⟨a,b,_,rfl⟩ := card_eq_two.mp (show S.card=2 by have := card_pos.mpr ne; omega)
      exact small_member F closed a b hS
  have at3 (S) (hS : S∈F) (ne : S.Nonempty) : 3 ≤ S.card := by
    by_contra! no
    exact small ⟨S,hS,ne,by omega⟩
  have bump (k : ℕ) (bound : ∀ S ∈ F, S.Nonempty → k ≤ S.card)
      (no : ¬ ∃ S ∈ F, S.card=k) (S) (hS : S∈F) (hne : S.Nonempty) : k+1 ≤ S.card := by
    have := bound S hS hne
    have diff : S.card≠k := fun eq => no ⟨S,hS,eq⟩
    omega
  by_cases three : ∃ S ∈ F, S.card = 3
  · obtain ⟨w,p,b⟩ := h₃ F closed empty full three at3
    exact witness F w p b
  have at4 := bump 3 at3 three
  by_cases four : ∃ S ∈ F, S.card = 4
  · obtain ⟨w,p,b⟩ := h₄ F closed empty full four at4
    exact witness F w p b
  have at5 := bump 4 at4 four
  by_cases five : ∃ S ∈ F, S.card = 5
  · obtain ⟨S,sf,sc⟩ := five
    by_cases another : ∃ T ∈ F, T.card=5 ∧ T≠S
    · obtain ⟨T,tf,tc,ts⟩ := another
      obtain ⟨w,p,b⟩ := h₅ F closed empty full ⟨S,sf,T,tf,ts.symm,sc,tc⟩ at5
      exact witness F w p b
    · exact unique_five F closed empty full at5 S sf sc (fun X hX c => by
        by_contra h
        exact another ⟨X,hX,c,h⟩)
  exact large_members F empty full (bump 5 at5 five)

lemma support_mem {α : Type*} [DecidableEq α] {F : Finset (Finset α)} (h : IsUnionClosed F)
    (e : ∅∈F) (B : Finset (Finset α)) (sub : B ⊆ F) : B.biUnion id ∈ F := by
  induction B using Finset.induction_on with
  | empty => simpa using e
  | @insert X B _ ih =>
    rw [biUnion_insert]
    exact h _ (sub (mem_insert_self ..)) _ (ih (fun _ hB => sub (mem_insert_of_mem hB)))

lemma clones {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (n : T.Nonempty)
    (bound : Fintype.card α ≤ 12) : ∃ f : Fin 12 → α, (∀ i, f i ∈ T) ∧ ∀ t ∈ T, ∃ i, f i = t := by
  obtain ⟨z,hz⟩ := n
  let e := Fintype.equivFin ↥T
  have size : Fintype.card ↥T ≤ 12 := by simpa using (T.card_le_univ.trans bound)
  let f (i : Fin 12) : α := if hi : i.val < Fintype.card ↥T then (e.symm ⟨i.val,hi⟩).val else z
  refine ⟨f,?_,?_⟩
  · intro i; dsimp [f]; split_ifs; exact Subtype.property _; exact hz
  · intro t ht
    let j := e ⟨t,ht⟩
    refine ⟨⟨j.val,j.isLt.trans_le size⟩,?_⟩
    change (if hi : j.val < Fintype.card ↥T then (e.symm ⟨j.val,hi⟩).val else z) = t
    rw [dif_pos j.isLt]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨t,ht⟩)

theorem main : H1 → H2 → H3 → type_of% @UnionClosed.union_closed.variants.univ_card := by
  intro h₃ h₄ h₅ α de A fa neα nontrivial closed bound
  by_cases zero : A=∅
  · subst A; obtain ⟨a⟩ := neα; exact ⟨a,by simp⟩
  have someSet : ∃ S ∈ A, S.Nonempty := by
    by_contra! empty
    apply nontrivial
    apply (Finset.nonempty_iff_ne_empty.mpr zero).subset_singleton_iff.mp
    intro S hS
    exact mem_singleton.mpr (empty S hS)
  let F := insert ∅ A
  have fclosed : IsUnionClosed F := by
    intro X hx Y hy
    rcases mem_insert.mp hx with rfl | x <;> rcases mem_insert.mp hy with rfl | y
    · simp [F]
    · simpa [F] using (mem_insert_of_mem y : Y∈F)
    · simpa [F] using (mem_insert_of_mem x : X∈F)
    · exact mem_insert_of_mem (closed X x Y y)
  let T := F.biUnion id
  have en : ∅ ∈ F := mem_insert_self ..
  have top : T ∈ F := support_mem fclosed en F (by rfl)
  have sub (S : Finset α) (hS : S∈F) : S ⊆ T := fun i hi => mem_biUnion.mpr ⟨S,hS,hi⟩
  obtain ⟨S,sA,t,ht⟩ := someSet
  obtain ⟨f,inside,surj⟩ := clones T ⟨t,sub S (mem_insert_of_mem sA) ht⟩ bound
  let pull (S : Finset α) := univ.filter (fun i : Fin 12 => f i ∈ S)
  let B := F.image pull
  have pmem (S : Finset α) (i : Fin 12) : i∈pull S ↔ f i ∈ S := by simp [pull]
  have inj : Set.InjOn pull (F : Set (Finset α)) := by
    intro X hx Y hy eq
    ext i
    by_cases ti : i ∈ T
    · obtain ⟨u,rfl⟩ := surj i ti
      rw [←pmem X,←pmem Y,eq]
    · have nx : i∉X := fun h => ti (sub X hx h)
      have ny : i∉Y := fun h => ti (sub Y hy h)
      simp [nx,ny]
  have bclosed : IsUnionClosed B := by
    intro U hu V hv
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hu
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hv
    refine mem_image.mpr ⟨X∪Y,fclosed _ hX _ hY,?_⟩
    ext i; simp [pull]
  have be : ∅∈B := mem_image.mpr ⟨∅,en,by simp [pull]⟩
  have bt : univ∈B := mem_image.mpr ⟨T,top,by ext i; simp [pull,inside]⟩
  obtain ⟨i,hi⟩ := twelve h₃ h₄ h₅ B bclosed be bt
  have eqf : B.filter (i ∈ ·) = (F.filter (f i ∈ ·)).image pull := by
    ext U
    constructor
    · intro hU
      obtain ⟨hU,u⟩ := mem_filter.mp hU
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
      exact mem_image.mpr ⟨X,mem_filter.mpr ⟨hX,(pmem _ _).mp u⟩,rfl⟩
    · intro hU
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
      exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hX).1,(pmem _ _).mpr (mem_filter.mp hX).2⟩
  have eqA : F.filter (f i ∈ ·) = A.filter (f i ∈ ·) := by ext X; simp [F]; aesop
  have bc : B.card=F.card := card_image_of_injOn inj
  have fi : Set.InjOn pull (↑(F.filter (f i ∈ ·)) : Set (Finset α)) :=
    inj.mono (fun _ hs => (mem_filter.mp hs).1)
  have freq : (B.filter (i ∈ ·)).card = (A.filter (f i ∈ ·)).card := by
    rw [eqf,card_image_of_injOn fi,eqA]
  rw [bc,freq] at hi
  have hb : A.card ≤ 2*(A.filter (f i ∈ ·)).card := (card_le_card (subset_insert ∅ A)).trans hi
  refine ⟨f i,?_⟩
  have cast : (A.card:ℚ) ≤ 2*((A.filter (f i ∈ ·)).card:ℚ) := by exact_mod_cast hb
  linarith

end OMA.R_UnionClosed_union_closed_variants_univ_card_R1
