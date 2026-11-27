import FormalConjectures.Wikipedia.UnionClosed
import Mathlib

/-! # A separating minimal family for the fifty-set theorem
Roberts and Simpson, A note on the union-closed sets conjecture (2010),
Theorems 3 and 4. Coordinates with identical incidence columns are identified
before applying the structural argument. -/

namespace OMA.R_UnionClosed_union_closed_variants_family_card_R1
open Finset UnionClosed
open scoped Classical

/-- The twelve-element theorem, restricted to finite ordinal ground sets. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → m ≤ 12 → ∀ F : Finset (Finset (Fin m)),
  F ≠ {∅} → IsUnionClosed F → (∃ i, F.card ≤ 2 * (F.filter (i ∈ ·)).card)

/-- The structural incidence estimate from Roberts and Simpson. The exceptional
sets are the ground set and the maximal sets omitting each coordinate. -/
def H2 : Prop := ∀ m n : ℕ, 12 < m → ∀ F : Finset (Finset (Fin m)),
  (∀ i, ∃ X ∈ F, i ∈ X) → (Function.Injective (fun i : Fin m => F.filter (i ∈ ·))) → IsUnionClosed F → F.card = 2*n+1 →
  (∀ i, (F.filter (i ∈ ·)).card ≤ n) → (∃ i, (F.filter (i ∈ ·)).card = n) →
  (∀ B ⊆ F, B.card < F.card → B ≠ {∅} → IsUnionClosed B → (∃ i, B.card ≤ 2 * (B.filter (i ∈ ·)).card)) →
  ∃ x : Fin m, (F.filter (x ∈ ·)).card = n ∧ ∃ C ⊆ F, m ≤ n ∧
    ((F.filter (x ∉ ·)) ∩ C).card ≤ 1 ∧ ∀ y, ((F \ C).filter (y ∈ ·)).card ≤ n-m

lemma normalize {α : Type*} [DecidableEq α] [Nonempty α]
    (F : Finset (Finset α)) (hnt : F ≠ {∅}) (hc : IsUnionClosed F)
    (go : ∀ m : ℕ, 0 < m → ∀ B : Finset (Finset (Fin m)),
      B.card = F.card → B ≠ {∅} → IsUnionClosed B → (∀ i, ∃ X ∈ B, i ∈ X) → (Function.Injective (fun i : Fin m => B.filter (i ∈ ·))) → (∃ i, B.card ≤ 2 * (B.filter (i ∈ ·)).card)) :
    (∃ i, F.card ≤ 2 * (F.filter (i ∈ ·)).card) := by
  classical
  by_cases zero : F = ∅
  · subst F; exact ⟨Classical.arbitrary α,by simp⟩
  have someSet : ∃ S ∈ F, S.Nonempty := by
    by_contra! empty
    apply hnt
    apply (Finset.nonempty_iff_ne_empty.mpr zero).subset_singleton_iff.mp
    intro S hS
    exact mem_singleton.mpr (empty S hS)
  let T := F.biUnion id
  let col (i : α) := F.filter (i ∈ ·)
  let P := T.image col
  let m := P.card
  let e : Fin m ≃ ↥P := (Fintype.equivFinOfCardEq (by simp [m])).symm
  have rep (i : Fin m) : ∃ a ∈ T, col a = (e i).val := mem_image.mp (e i).property
  choose f fmem feq using rep
  have same (i : Fin m) (a : α) (h : col a = (e i).val)
      (X : Finset α) (hx : X ∈ F) : a ∈ X ↔ f i ∈ X := by
    have t : X ∈ col a ↔ X ∈ col (f i) := by rw [h,feq]
    simpa [col,hx] using t
  let pull (X : Finset α) := univ.filter (fun i : Fin m => f i ∈ X)
  let B := F.image pull
  have pmem (X : Finset α) (i : Fin m) : i ∈ pull X ↔ f i ∈ X := by simp [pull]
  have sub (X : Finset α) (hx : X ∈ F) : X ⊆ T :=
    fun _ ha => mem_biUnion.mpr ⟨X,hx,ha⟩
  have inj : Set.InjOn pull (F : Set (Finset α)) := by
    intro X hx Y hy eq
    ext a
    by_cases ha : a ∈ T
    · let p : ↥P := ⟨col a,mem_image_of_mem _ ha⟩
      let i := e.symm p
      have h : col a = (e i).val := by simp [i,p]
      rw [same i a h X hx,same i a h Y hy,← pmem X,← pmem Y,eq]
    · have nx : a ∉ X := fun h => ha (sub X hx h)
      have ny : a ∉ Y := fun h => ha (sub Y hy h)
      simp [nx,ny]
  have bc : B.card = F.card := card_image_of_injOn inj
  have bclosed : IsUnionClosed B := by
    intro U hu V hv
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hu
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hv
    refine mem_image.mpr ⟨X∪Y,hc _ hX _ hY,?_⟩
    ext; simp [pull]
  have ba : (∀ i, ∃ X ∈ B, i ∈ X) := by
    intro i
    obtain ⟨X,hX,hi⟩ := mem_biUnion.mp (fmem i)
    exact ⟨pull X,mem_image_of_mem _ hX,(pmem _ _).mpr hi⟩
  obtain ⟨X,hX,a,ha⟩ := someSet
  have hm : 0 < m := Finset.card_pos.mpr ⟨col a,mem_image_of_mem _ (sub X hX ha)⟩
  have bn : B ≠ {∅} := by
    intro h
    obtain ⟨U,hu,hi⟩ := ba ⟨0,hm⟩
    have := mem_singleton.mp (h ▸ hu)
    subst U; simp at hi
  have bs : (Function.Injective (fun i : Fin m => B.filter (i ∈ ·))) := by
    intro i j eq
    change B.filter (i ∈ ·) = B.filter (j ∈ ·) at eq
    apply e.injective
    apply Subtype.ext
    rw [← feq i,← feq j]
    ext X
    by_cases hx : X ∈ F
    · have hb : pull X ∈ B := mem_image_of_mem _ hx
      have t : pull X ∈ B.filter (i ∈ ·) ↔ pull X ∈ B.filter (j ∈ ·) := by rw [eq]
      simpa [col,hx,hb,pmem] using t
    · simp [col,hx]
  obtain ⟨i,hi⟩ := go m hm B bc bn bclosed ba bs
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
  have fi : Set.InjOn pull (↑(F.filter (f i ∈ ·)) : Set (Finset α)) :=
    inj.mono (fun _ hs => (mem_filter.mp hs).1)
  have ff : (B.filter (i ∈ ·)).card = (F.filter (f i ∈ ·)).card := by simp only [eqf,card_image_of_injOn fi]
  exact ⟨f i,by rwa [← bc,← ff]⟩

lemma minimalErase {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (hc : IsUnionClosed F) (hn : F.Nonempty) :
    ∃ S ∈ F, F.erase S ≠ {∅} ∧ IsUnionClosed (F.erase S) := by
  classical
  obtain ⟨S,hs,minimal⟩ := F.exists_min_image Finset.card hn
  refine ⟨S,hs,?_,?_⟩
  · intro h
    have he : ∅ ∈ F.erase S := by rw [h]; simp
    have hz := minimal ∅ (mem_erase.mp he).2
    have seq : S = ∅ := card_eq_zero.mp (by simpa using hz)
    exact (mem_erase.mp he).1 seq.symm
  · intro X hx Y hy
    refine mem_erase.mpr ⟨?_,hc X (mem_erase.mp hx).2 Y (mem_erase.mp hy).2⟩
    intro h
    have le : X ⊆ S := h ▸ subset_union_left
    have lt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨le,(mem_erase.mp hx).1⟩)
    exact (Nat.not_lt_of_ge (minimal X (mem_erase.mp hx).2)) lt

lemma finiteCase (small : H1) (structureBound : H2) (k : ℕ) :
    ∀ m : ℕ, 0 < m → ∀ F : Finset (Finset (Fin m)), F.card = k → k ≤ 50 →
      F ≠ {∅} → IsUnionClosed F → (∃ i, F.card ≤ 2 * (F.filter (i ∈ ·)).card) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro d hd F fcard limit nontrivial closed
    let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    apply normalize F nontrivial closed
    intro m hm A size nt hc ha hs
    have sk : A.card = k := size.trans fcard
    by_cases ground : m ≤ 12
    · exact small m hm ground A nt hc
    have recurse (B : Finset (Finset (Fin m))) (_ : B ⊆ A)
        (hlt : B.card < A.card) (hb : B ≠ {∅}) (hbc : IsUnionClosed B) : (∃ i, B.card ≤ 2 * (B.filter (i ∈ ·)).card) :=
      ih B.card (by omega) m hm B rfl (by omega) hb hbc
    by_contra counter
    have strict (i : Fin m) : 2 * (A.filter (i ∈ ·)).card < A.card :=
      lt_of_not_ge (fun h => counter ⟨i,h⟩)
    have ne : A.Nonempty := card_pos.mp (by have := strict ⟨0,hm⟩; omega)
    obtain ⟨S,hS,ent,ec⟩ := minimalErase hc ne
    have eraseCard := card_erase_of_mem hS
    obtain ⟨z,hz⟩ := recurse (A.erase S) (erase_subset _ _) (card_erase_lt_of_mem hS) ent ec
    have mono : ((A.erase S).filter (z ∈ ·)).card ≤ (A.filter (z ∈ ·)).card :=
      card_le_card (filter_subset_filter _ (erase_subset _ _))
    let n := (A.filter (z ∈ ·)).card
    have count : A.card = 2*n+1 := by have := strict z; dsimp [n]; omega
    have maxFreq (i : Fin m) : (A.filter (i ∈ ·)).card ≤ n := by have := strict i; omega
    obtain ⟨x,hx,C,_hC,hwidth,excep,residual⟩ :=
      structureBound m n (by omega) A ha hs hc count maxFreq ⟨z,rfl⟩ recurse
    let D := A.filter (x ∉ ·)
    have parts := card_filter_add_card_filter_not (s := A) (p := fun X => x ∈ X)
    have dcount : D.card = n+1 := by
      change (A.filter (x ∈ ·)).card + D.card = A.card at parts
      omega
    have dnt : D ≠ {∅} := by
      intro eq
      have h1 : D.card = 1 := by rw [eq,card_singleton]
      omega
    have dc : IsUnionClosed D := by
      intro X hX Y hY
      obtain ⟨hX,xX⟩ := mem_filter.mp hX
      obtain ⟨hY,xY⟩ := mem_filter.mp hY
      exact mem_filter.mpr ⟨hc X hX Y hY,by simpa using And.intro xX xY⟩
    obtain ⟨y,hy⟩ := recurse D (filter_subset ..) (by omega) dnt dc
    have cover : D.filter (y ∈ ·) ⊆ ((A \ C).filter (y ∈ ·)) ∪ (D ∩ C) := by
      intro X hX
      obtain ⟨hD,hyX⟩ := mem_filter.mp hX
      by_cases h : X ∈ C
      · exact mem_union_right _ (mem_inter.mpr ⟨hD,h⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_filter.mp hD).1,h⟩,hyX⟩)
    have upper : (D.filter (y ∈ ·)).card ≤ ((A \ C).filter (y ∈ ·)).card + (D ∩ C).card :=
      (card_le_card cover).trans (card_union_le ..)
    change (D ∩ C).card ≤ 1 at excep
    have := residual y
    omega

theorem main : H1 → H2 → type_of% @UnionClosed.union_closed.variants.family_card := by
  intro small structureBound α de A neα nontrivial closed bound
  have good := normalize A nontrivial closed (fun m hm B size nt hc _ _ =>
    finiteCase small structureBound A.card m hm B size bound nt hc)
  obtain ⟨i,hi⟩ := good
  refine ⟨i,?_⟩
  change A.card ≤ 2 * (A.filter (i ∈ ·)).card at hi
  have cast : (A.card : ℚ) ≤ 2*((A.filter (i ∈ ·)).card : ℚ) := by exact_mod_cast hi
  linarith

end OMA.R_UnionClosed_union_closed_variants_family_card_R1
