import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases

/-! Canonically relabel exterior supports and rows with a single code point. -/


namespace WeightNineteenSupportFibers

open Finset
open scoped BigOperators

abbrev Columns (n : Nat) := Fin n → Finset (Fin 6)

variable {n k : Nat}

def shared (C : Columns n) : Finset (Fin n) :=
  Finset.univ.filter fun p => 2 ≤ (C p).card

def layout (C : Columns n) : Finset (Finset (Fin 6)) :=
  (shared C).image C

def fiber (C : Columns n) (s : Finset (Fin 6)) : Finset (Fin n) :=
  Finset.univ.filter fun p => C p = s

lemma mem_fiber (C : Columns n) (s : Finset (Fin 6)) (p : Fin n) :
    p ∈ fiber C s ↔ C p = s := by simp [fiber]

lemma injective_shared (C : Columns n)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    (shared C : Set (Fin n)).InjOn C := by
  intro p hp q hq same
  by_contra different
  have small := overlap p q different
  rw [same,Finset.inter_self] at small
  have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  omega

lemma high_fiber (C : Columns n)
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

lemma single_fiber (C : Columns n)
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
  have inj : (high : Set (Fin n)).InjOn C := by
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

lemma sum_fibers (C : Columns n) : (∑ s : Finset (Fin 6), (fiber C s).card) = n := by
  calc
    _ = ∑ s : Finset (Fin 6), ∑ p : Fin n, if C p = s then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [fiber]
    _ = ∑ p : Fin n, ∑ s : Finset (Fin 6), if C p = s then (1 : Nat) else 0 := Finset.sum_comm
    _ = n := by simp [eq_comm]

theorem relabel_columns (C D : Columns n)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = k)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = k)
    (same : layout C = layout D) :
    ∃ e : Equiv.Perm (Fin n), ∀ p, D (e p) = C p := by
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
      change (∑ s ∈ nonempty, (fiber C s).card) + (fiber C ∅).card = n at hc
      change (∑ s ∈ nonempty, (fiber D s).card) + (fiber D ∅).card = n at hd
      omega
    · exact counts_ne s zero
  let match_card (s : Finset (Fin 6)) : Fintype.card ↥(fiber C s) = Fintype.card ↥(fiber D s) := by
    rw [Fintype.card_coe,Fintype.card_coe,all_counts]
  let fibers (s : Finset (Fin 6)) : ↥(fiber C s) ≃ ↥(fiber D s) :=
    (Fintype.equivOfCardEq (match_card s))
  let as_fiber (W : Columns n) (s : Finset (Fin 6)) : {p // W p = s} ≃ ↥(fiber W s) :=
    Equiv.subtypeEquivProp (funext fun p => propext (mem_fiber W s p).symm)
  let mapped (s : Finset (Fin 6)) : {p // C p = s} ≃ {p // D p = s} :=
    ((as_fiber C s).trans (fibers s)).trans (as_fiber D s).symm
  let e : Equiv.Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv C).symm.trans
      ((Equiv.sigmaCongrRight mapped).trans (Equiv.sigmaFiberEquiv D))
  exact ⟨e,fun p => (mapped (C p) ⟨p,rfl⟩).property⟩

end WeightNineteenSupportFibers


namespace WeightNineteenExteriorSupports

open Finset WeightNineteenSupportFibers

theorem exterior_layout (C : Columns 19) (D : Columns 92)
    (maxTwo : ∀ q, (D q).card ≤ 2)
    (rowMeet : ∀ a b : Fin 6, a ≠ b → ∃! x : Fin 19 ⊕ Fin 92,
      Sum.elim (fun p => a ∈ C p ∧ b ∈ C p) (fun q => a ∈ D q ∧ b ∈ D q) x) :
    layout D = ((Finset.univ : Finset (Fin 6)).powersetCard 2).filter
      (fun T => ∀ p : Fin 19, ¬ T ⊆ C p) := by
  ext T
  constructor
  · intro on
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp on
    have isPair : (D q).card = 2 := le_antisymm (maxTwo q) (Finset.mem_filter.mp hq).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,isPair⟩,?_⟩
    intro p cover
    obtain ⟨a,b,diff,form⟩ := Finset.card_eq_two.mp isPair
    have in_a : a ∈ D q := form ▸ Finset.mem_insert_self _ _
    have in_b : b ∈ D q := form ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨_,_,only⟩ := rowMeet a b diff
    have same := (only (.inl p) ⟨cover in_a,cover in_b⟩).trans (only (.inr q) ⟨in_a,in_b⟩).symm
    cases same
  · intro on
    obtain ⟨allowed,noAlready⟩ := Finset.mem_filter.mp on
    have pair := (Finset.mem_powersetCard.mp allowed).2
    obtain ⟨a,b,diff,rfl⟩ := Finset.card_eq_two.mp pair
    obtain ⟨point,seen,_⟩ := rowMeet a b diff
    cases point with
    | inl p =>
      exact False.elim (noAlready p (Finset.insert_subset_iff.mpr
        ⟨seen.1,Finset.singleton_subset_iff.mpr seen.2⟩))
    | inr q =>
      have inside : {a,b} ⊆ D q := Finset.insert_subset_iff.mpr
        ⟨seen.1,Finset.singleton_subset_iff.mpr seen.2⟩
      have exactPair : {a,b} = D q := Finset.eq_of_subset_of_card_le inside ((maxTwo q).trans_eq pair.symm)
      exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        rw [← exactPair,pair]⟩,exactPair.symm⟩

theorem exterior_relabel (C : Columns 19) (D E : Columns 92)
    (maxTwo : ∀ q, (D q).card ≤ 2)
    (rowMeet : ∀ a b : Fin 6, a ≠ b → ∃! x : Fin 19 ⊕ Fin 92,
      Sum.elim (fun p => a ∈ C p ∧ b ∈ C p) (fun q => a ∈ D q ∧ b ∈ D q) x)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (e_overlap : ∀ p q, p ≠ q → (E p ∩ E q).card ≤ 1)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 6)
    (e_row : ∀ a, (Finset.univ.filter fun p => a ∈ E p).card = 6)
    (chosen : layout E = ((Finset.univ : Finset (Fin 6)).powersetCard 2).filter
      (fun T => ∀ p : Fin 19, ¬ T ⊆ C p)) :
    ∃ e : Equiv.Perm (Fin 92), ∀ p, D (e p) = E p := by
  obtain ⟨e,aligned⟩ := relabel_columns D E d_overlap e_overlap d_row e_row
    ((exterior_layout C D maxTwo rowMeet).trans chosen.symm)
  exact ⟨e.symm,fun p => by simpa only [Equiv.apply_symm_apply] using (aligned (e.symm p)).symm⟩

end WeightNineteenExteriorSupports


namespace WeightNineteenOneHotRows

open Finset

theorem align_colors {n k : Nat} (f g : Fin n → Fin k)
    (counts : ∀ a, (Finset.univ.filter fun i => f i = a).card =
      (Finset.univ.filter fun i => g i = a).card) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, f (e i) = g i := by
  classical
  let fiber (h : Fin n → Fin k) (a : Fin k) : {i // h i = a} ≃ ↥(Finset.univ.filter fun i => h i = a) :=
    Equiv.subtypeEquivProp (funext fun i => propext (by simp))
  let matched (a : Fin k) : {i // g i = a} ≃ {i // f i = a} :=
    (fiber g a).trans ((Fintype.equivOfCardEq (by
      rw [Fintype.card_coe,Fintype.card_coe,counts])).trans (fiber f a).symm)
  let e := (Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight matched).trans (Equiv.sigmaFiberEquiv f))
  exact ⟨e,fun i => (matched (g i) ⟨i,rfl⟩).property⟩

theorem normalize_one_hits {n k : Nat} (M : Fin n → Fin k → Bool)
    (g : Fin n → Fin k)
    (one : ∀ i, (Finset.univ.filter fun a => M i a = true).card = 1)
    (counts : ∀ a, (Finset.univ.filter fun i => M i a = true).card =
      (Finset.univ.filter fun i => g i = a).card) :
    ∃ e : Equiv.Perm (Fin n), ∀ i a, M (e i) a = decide (g i = a) := by
  classical
  let f (i : Fin n) := (Finset.card_eq_one.mp (one i)).choose
  have chosen (i : Fin n) : (Finset.univ.filter fun a => M i a = true) = {f i} :=
    (Finset.card_eq_one.mp (one i)).choose_spec
  have hit (i : Fin n) (a : Fin k) : M i a = true ↔ f i = a := by
    have share : a ∈ Finset.univ.filter (fun a => M i a = true) ↔ M i a = true := by simp
    rw [← share, chosen,Finset.mem_singleton,eq_comm]
  have together (a : Fin k) : (Finset.univ.filter fun i => f i = a).card =
      (Finset.univ.filter fun i => g i = a).card := by
    have same : (Finset.univ.filter fun i => f i = a) =
        (Finset.univ.filter fun i => M i a = true) := by
      ext i
      simp only [Finset.mem_filter,hit]
    rw [same,counts]
  obtain ⟨e,h⟩ := align_colors f g together
  refine ⟨e,fun i a => Bool.eq_iff_iff.mpr ?_⟩
  simp only [hit,h,decide_eq_true_eq]

end WeightNineteenOneHotRows

namespace WeightNineteenOuterNormalization

open Finset WeightNineteenSupportFibers WeightNineteenExteriorSupports WeightNineteenOneHotRows

abbrev Rows := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
abbrev Cols := Fin 19 ⊕ Fin 92
abbrev Model := Rows → Cols → Bool

def heavyInside (M : Model) (p : Fin 19) : Finset (Fin 6) :=
  Finset.univ.filter fun a => M (.inl a) (.inl p) = true

def heavyOutside (M : Model) (q : Fin 92) : Finset (Fin 6) :=
  Finset.univ.filter fun a => M (.inl a) (.inr q) = true

def mediumDegree (M : Model) (p : Cols) : Nat :=
  (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card

lemma card_filter_sum {X Y : Type} [Fintype X] [Fintype Y]
    (P : X ⊕ Y → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (.inl x)).card +
      (Finset.univ.filter fun y => P (.inr y)).card := by
  have parts : Finset.univ.filter P = (Finset.univ.filter fun x => P (.inl x)).disjSum
      (Finset.univ.filter fun y => P (.inr y)) := by
    ext l
    cases l <;> simp [Finset.mem_filter]
  rw [parts,Finset.card_disjSum]

theorem reorder_outer_matrices (M : Model)
    (E : Columns 92) (g : Fin 68 → Fin 19)
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (cols : ∀ p, (Finset.univ.filter fun l => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (colPairs : ∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true)
    (five : ∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5)
    (one : ∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1)
    (inner : ∀ p : Fin 19, mediumDegree M (.inl p) + 2 * (heavyInside M p).card = 9)
    (outer : ∀ p : Fin 92, mediumDegree M (.inr p) + 2 * (heavyOutside M p).card = 4)
    (eOverlap : ∀ p q, p ≠ q → (E p ∩ E q).card ≤ 1)
    (eSizes : ∀ a, (Finset.univ.filter fun p => a ∈ E p).card = 6)
    (eForm : layout E = ((Finset.univ : Finset (Fin 6)).powersetCard 2).filter
      (fun T => ∀ p : Fin 19, ¬ T ⊆ heavyInside M p))
    (gSizes : ∀ p, (Finset.univ.filter fun c => g c = p).card = (heavyInside M p).card + 2) :
    ∃ (ε : Equiv.Perm (Fin 92)) (ρ : Equiv.Perm (Fin 68)),
      (∀ q, heavyOutside M (ε q) = E q) ∧
      (∀ c p, M (.inr (.inr (ρ c))) (.inl p) = decide (g c = p)) := by
  have maxTwo (q : Fin 92) : (heavyOutside M q).card ≤ 2 := by
    have h := outer q
    omega
  have heavyMeet (a b : Fin 6) (ne : a ≠ b) : ∃! x : Cols, Sum.elim
      (fun p => a ∈ heavyInside M p ∧ b ∈ heavyInside M p)
      (fun q => a ∈ heavyOutside M q ∧ b ∈ heavyOutside M q) x := by
    have form (x : Cols) : Sum.elim
        (fun p => a ∈ heavyInside M p ∧ b ∈ heavyInside M p)
        (fun q => a ∈ heavyOutside M q ∧ b ∈ heavyOutside M q) x ↔
        M (.inl a) x = true ∧ M (.inl b) x = true := by
      cases x <;> simp [heavyInside,heavyOutside]
    simp_rw [form]
    exact rowPairs (.inl a) (.inl b) (fun eq => ne (Sum.inl.inj eq))
  have extOverlap (p q : Fin 92) (ne : p ≠ q) : (heavyOutside M p ∩ heavyOutside M q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have both (c : Fin 6) (hc : c ∈ heavyOutside M p ∩ heavyOutside M q) :
        M (.inl c) (.inr p) = true ∧ M (.inl c) (.inr q) = true := by
      simpa [heavyOutside] using hc
    obtain ⟨_,_,unique⟩ := colPairs (.inr p) (.inr q) (fun eq => ne (Sum.inr.inj eq))
    exact Sum.inl.inj ((unique (.inl a) (both a ha)).trans (unique (.inl b) (both b hb)).symm)
  have outsideSix (a : Fin 6) : (Finset.univ.filter fun q => a ∈ heavyOutside M q).card = 6 := by
    have total := rows (.inl a)
    rw [card_filter_sum, five a] at total
    simpa [heavyOutside] using (show (Finset.univ.filter fun q : Fin 92 => M (.inl a) (.inr q) = true).card = 6 by omega)
  have shortLabels (p : Fin 19) :
      (Finset.univ.filter fun c : Fin 68 => M (.inr (.inr c)) (.inl p) = true).card =
        (Finset.univ.filter fun c => g c = p).card := by
    rw [gSizes]
    have total := cols (.inl p)
    rw [card_filter_sum] at total
    have split : (Finset.univ.filter fun d : Fin 37 ⊕ Fin 68 => M (.inr d) (.inl p) = true).card =
        mediumDegree M (.inl p) +
          (Finset.univ.filter fun c : Fin 68 => M (.inr (.inr c)) (.inl p) = true).card :=
      card_filter_sum (fun d => M (.inr d) (.inl p) = true)
    rw [split] at total
    change (heavyInside M p).card + _ = _ at total
    have balanced := inner p
    omega
  obtain ⟨ε,extForm⟩ := exterior_relabel (heavyInside M) (heavyOutside M) E
    maxTwo heavyMeet extOverlap eOverlap outsideSix eSizes eForm
  obtain ⟨ρ,oneForm⟩ := normalize_one_hits (fun c p => M (.inr (.inr c)) (.inl p)) g one shortLabels
  exact ⟨ε,ρ,extForm,oneForm⟩

end WeightNineteenOuterNormalization



namespace WeightNineteenCanonicalOuterTables

open Finset

def interiors : List (List (List (Fin 6))) :=
  [[[0,1,2,3],[0,4],[0,5],[1,4],[1,5],[2,4],[2,5],[3,4],[3,5],[4,5],[0],[0],[1],[1],[2],[2],[3],[3],[]],
   [[0,1,2,3],[0,4],[0,5],[1,4],[1,5],[2,4],[2,5],[3,4],[3,5],[0],[0],[1],[1],[2],[2],[3],[3],[4],[5]],
   [[0,1,2,3],[0,4,5],[1,4],[1,5],[2,4],[2,5],[3,4],[3,5],[0],[0],[0],[1],[1],[2],[2],[3],[3],[4],[5]]]

def interior (i : Fin 3) (p : Fin 19) : Finset (Fin 6) :=
  ((interiors[i.val]!)[p.val]!).toFinset

def exterior (i : Fin 3) (q : Fin 92) : Finset (Fin 6) :=
  let double := i = 1
  let start : List (List (Fin 6)) := if double then [[4,5]] else []
  let blocks := (List.finRange 6).flatMap fun a => List.replicate (if double ∧ 4 ≤ a.val then 5 else 6) [a]
  ((start ++ blocks)[q.val]!).toFinset

def shortLabel (i : Fin 3) (c : Fin 68) : Fin 19 :=
  ((List.finRange 19).flatMap fun p => List.replicate ((interior i p).card + 2) p)[c.val]!

def sharedExterior (i : Fin 3) : Finset (Finset (Fin 6)) :=
  (Finset.univ.filter fun q => 2 ≤ (exterior i q).card).image (exterior i)

set_option maxHeartbeats 1000000 in
theorem exterior_overlap : ∀ i : Fin 3, ∀ p q : Fin 92, p ≠ q →
    (exterior i p ∩ exterior i q).card ≤ 1 := by decide +kernel

theorem exterior_rows : ∀ i : Fin 3, ∀ a : Fin 6,
    (Finset.univ.filter fun p => a ∈ exterior i p).card = 6 := by decide +kernel

theorem exterior_layout : ∀ i : Fin 3,
    sharedExterior i = ((Finset.univ : Finset (Fin 6)).powersetCard 2).filter
      (fun T => ∀ p : Fin 19, ¬ T ⊆ interior i p) := by decide +kernel

theorem short_labels : ∀ i : Fin 3, ∀ p : Fin 19,
    (Finset.univ.filter fun c => shortLabel i c = p).card = (interior i p).card + 2 := by decide +kernel

end WeightNineteenCanonicalOuterTables



open Finset WeightNineteenOuterNormalization WeightNineteenCanonicalOuterTables

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H2_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H2_R1_H2_R1.H1
  dsimp only
  intro i M rows cols rowPairs colPairs five one inner outer supports
  have pos : i.val < 3 := by omega
  let tag : Fin 3 := ⟨i.val,pos⟩
  have insideForm (p : Fin 19) : heavyInside M p = interior tag p := by
    fin_cases i <;> exact supports p
  have eForm := exterior_layout tag
  change _ = (Finset.univ.powersetCard 2 : Finset (Finset (Fin 6))).filter
    (fun T => ∀ p : Fin 19, ¬ T ⊆ interior tag p) at eForm
  simp only [← insideForm] at eForm
  have gForm (p : Fin 19) :
      (Finset.univ.filter fun c => shortLabel tag c = p).card = (heavyInside M p).card + 2 := by
    rw [short_labels,insideForm]
  have result := reorder_outer_matrices M (exterior tag) (shortLabel tag) rows cols rowPairs colPairs five one
    inner outer (exterior_overlap tag) (exterior_rows tag) eForm gForm
  fin_cases i <;> exact result

