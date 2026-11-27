import FormalConjectures.ErdosProblems.«757»
import Mathlib

-- Problem: Erdős Problem 757, variant lowerBound
-- Credit: @Dugongue (reduction R1, agent Claude Code, model claude-opus-5-5)
-- Credit: leaf H1 and leaf H2: author not named in the piece files
-- Credit: @LordMike (assembly)


-- Reduction Erdos757.erdos_757.variants.lowerBound.R1 of Erdős Problem 757 — lowerBound
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Source: Gyárfás and Lehel, Linear sets with five distinct differences among any four elements,
-- J. Combin. Theory Ser. B (1995). No new result is claimed.
--
-- Split.
--   H1 (the combinatorial heart, Gyárfás–Lehel, for finite sets of integers, in 3-AP-free form):
--      there is c > 1/2 such that every finite set of integers in which every 4-subset determines
--      at least five distinct positive differences contains a 3-AP-free subset of size at least c|A|.
--   H2 (Freiman-type transfer to the integers): for every finite A ⊆ ℝ there is an additive map
--      f : ℝ →+ ℝ, injective on A - A, sending A into ℤ.
-- Proved here (main):
--   * the difference condition forbids a + b = c + d with a, b, c, d distinct (B - B would have
--     at most 9 elements), so inside such a set a 3-AP-free subset is automatically Sidon;
--   * the difference condition, Sidon sets and cardinalities transfer along f;
--   * the admissible constants are bounded above by 1 (take A a singleton), so sSup > 1/2.

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1

open scoped Pointwise

/-- Gyárfás–Lehel, integer sets, 3-AP-free form. -/
def H1 : Prop := ∃ c : ℝ, 1 / 2 < c ∧ ∀ A : Set ℝ, A.Finite → A ⊆ Set.range ((↑) : ℤ → ℝ) →
  (∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard) →
  ∃ S ⊆ A, (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z) ∧ c * A.ncard ≤ (S.ncard : ℝ)

/-- Transfer of a finite set of reals to the integers by an additive map injective on A - A. -/
def H2 : Prop := ∀ A : Set ℝ, A.Finite →
  ∃ f : ℝ →+ ℝ, Set.InjOn f (A - A) ∧ f '' A ⊆ Set.range ((↑) : ℤ → ℝ)

/-- A finite list of reals has at most its length many distinct entries. -/
theorem ncard_list_le (l : List ℝ) : ({x | x ∈ l} : Set ℝ).ncard ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : {x | x ∈ a :: l} = insert a {x | x ∈ l} := by
      ext x; simp
    rw [e]
    exact (Set.ncard_insert_le _ _).trans (by simp; omega)

/-- Inside a set where every 4-subset has at least five distinct positive differences,
a 3-AP-free subset is a Sidon set. -/
theorem sidon_of_apfree {A S : Set ℝ} (hSA : S ⊆ A)
    (hcond : ∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard)
    (hap : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z) :
    IsSidon S := by
  intro a ha c hc b hb d hd h
  by_cases hac : a = c
  · left
    exact ⟨hac, by subst hac; linarith⟩
  by_cases had : a = d
  · right
    exact ⟨had, by subst had; linarith⟩
  exfalso
  by_cases hab : a = b
  · subst hab
    have e := hap c hc a ha d hd (by linarith)
    subst e
    exact hac (by linarith)
  by_cases hcd : c = d
  · subst hcd
    exact hab (hap a ha c hc b hb (by linarith))
  have hbc : b ≠ c := fun e => had (by linarith)
  have hbd : b ≠ d := fun e => hac (by linarith)
  have hBA : ({a, b, c, d} : Set ℝ) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with e | e | e | e <;> rw [e]
    exacts [hSA ha, hSA hb, hSA hc, hSA hd]
  have hB4 : ({a, b, c, d} : Set ℝ).ncard = 4 := by
    have hl : ({a, b, c, d} : Set ℝ) = ↑([a, b, c, d].toFinset) := by
      ext x; simp
    rw [hl, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
    · rfl
    · simp [hab, hac, had, hbc, hbd, hcd]
  have hsub : ({a, b, c, d} : Set ℝ) - {a, b, c, d} ⊆
      {x | x ∈ [0, a - c, c - a, a - d, d - a, a - b, b - a, c - d, d - c]} := by
    rintro x ⟨u, hu, v, hv, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton]
    rcases hu with e1 | e1 | e1 | e1 <;> rcases hv with e2 | e2 | e2 | e2 <;> rw [e1, e2] <;>
      repeat (first | (left; linarith) | right)
    all_goals linarith
  have h9 : (({a, b, c, d} : Set ℝ) - {a, b, c, d}).ncard ≤ 9 :=
    (Set.ncard_le_ncard hsub (List.finite_toSet _)).trans (ncard_list_le _)
  have h11 := hcond _ hBA hB4
  omega

/-- Admissible constants are at most 1. -/
theorem bdd : BddAbove {c : ℝ | Erdos757.IsAdmissible c} := by
  refine ⟨1, fun c hc => ?_⟩
  have hc' : Erdos757.IsAdmissible c := hc
  obtain ⟨S, hS, -, hcS⟩ := hc' (A := ({0} : Set ℝ)) (Set.finite_singleton 0) (by
    intro B hB hB4
    exfalso
    have h := Set.ncard_le_ncard hB (Set.finite_singleton 0)
    rw [Set.ncard_singleton] at h
    omega)
  have h1 : S.ncard ≤ 1 := by
    have h := Set.ncard_le_ncard hS (Set.finite_singleton 0)
    rwa [Set.ncard_singleton] at h
  rw [Set.ncard_singleton] at hcS
  have h' : (S.ncard : ℝ) ≤ 1 := by exact_mod_cast h1
  push_cast at hcS
  linarith

/-- The image of A ∩ f⁻¹ T under f, when T ⊆ f '' A. -/
theorem image_inter_preimage_eq {f : ℝ → ℝ} {A T : Set ℝ} (hT : T ⊆ f '' A) :
    f '' (A ∩ f ⁻¹' T) = T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hT hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

theorem image_sub_eq (f : ℝ →+ ℝ) (B : Set ℝ) : f '' (B - B) = f '' B - f '' B := by
  ext y
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, f v, ⟨v, hv, rfl⟩, (map_sub f u v).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u - v, ⟨u, hu, v, hv, rfl⟩, map_sub f u v⟩

theorem admissible (h1 : H1) (h2 : H2) : ∃ c : ℝ, 1 / 2 < c ∧ Erdos757.IsAdmissible c := by
  obtain ⟨c, hc, hH⟩ := h1
  refine ⟨c, hc, ?_⟩
  intro A hA hcond
  obtain ⟨f, hinj, hint⟩ := h2 A hA
  have hinjA : Set.InjOn f A := by
    intro x hx y hy hxy
    have h0 : f (x - y) = f (x - x) := by
      rw [map_sub, map_sub, hxy]
    have e := hinj (Set.sub_mem_sub hx hy) (Set.sub_mem_sub hx hx) h0
    linarith
  have hcond' : ∀ B' ⊆ f '' A, B'.ncard = 4 → 11 ≤ (B' - B').ncard := by
    intro B' hB' hB'4
    have hBA : A ∩ f ⁻¹' B' ⊆ A := Set.inter_subset_left
    have hfB : f '' (A ∩ f ⁻¹' B') = B' := image_inter_preimage_eq hB'
    have hB4 : (A ∩ f ⁻¹' B').ncard = 4 := by
      rw [← Set.ncard_image_of_injOn (hinjA.mono hBA), hfB, hB'4]
    have h11 := hcond _ hBA hB4
    rw [← hfB, ← image_sub_eq,
      Set.ncard_image_of_injOn (hinj.mono (Set.sub_subset_sub hBA hBA))]
    exact h11
  obtain ⟨S', hS'A, hap, hcard⟩ := hH (f '' A) (hA.image f) hint hcond'
  have hSA : A ∩ f ⁻¹' S' ⊆ A := Set.inter_subset_left
  have hfS : f '' (A ∩ f ⁻¹' S') = S' := image_inter_preimage_eq hS'A
  have hsid : IsSidon S' := sidon_of_apfree hS'A hcond' hap
  refine ⟨A ∩ f ⁻¹' S', hSA, ?_, ?_⟩
  · intro a ha b hb c hc d hd h
    rcases hsid (f a) ha.2 (f b) hb.2 (f c) hc.2 (f d) hd.2
        (by rw [← map_add, ← map_add, h]) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      exact ⟨hinjA ha.1 hb.1 e1, hinjA hc.1 hd.1 e2⟩
    · right
      exact ⟨hinjA ha.1 hd.1 e1, hinjA hc.1 hb.1 e2⟩
  · have e1 : (f '' A).ncard = A.ncard := Set.ncard_image_of_injOn hinjA
    have e2 : S'.ncard = (A ∩ f ⁻¹' S').ncard := by
      rw [← Set.ncard_image_of_injOn (hinjA.mono hSA), hfS]
    rw [e1, e2] at hcard
    exact hcard

theorem main : H1 → H2 → type_of% @Erdos757.erdos_757.variants.lowerBound := by
  intro h1 h2 A
  obtain ⟨c, hc, hadm⟩ := admissible h1 h2
  exact lt_csSup_of_lt bdd hadm hc

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1


/-! The arithmetic-progression hypergraph of a (4,5)-set, following Gyárfás and Lehel.
The original proof bounds the transversal number of a sparse triple system.
Ma and Tang, arXiv:2602.23282, sharpen the resulting fraction to 9/17 using
Henning and Yeo. Either transversal estimate suffices in the second step. -/

namespace OMA.Sparse757
open Finset
open scoped Pointwise Classical

/-- All proper progressions are covered by a sparse, linear, F₇-free triple system. -/
def H1 : Prop := ∀ A : Finset ℝ,
    (∀ B ⊆ (A : Set ℝ), B.ncard = 4 → 11 ≤ (B - B).ncard) →
    ∃ E : Finset (Finset ℝ), E.card ≤ A.card ∧
      (∀ e ∈ E, e ⊆ A ∧ e.card = 3) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ u : Fin 7 → ℝ, Function.Injective u →
        ¬ ({u 0,u 1,u 2} ∈ E ∧ {u 0,u 3,u 4} ∈ E ∧ {u 0,u 5,u 6} ∈ E ∧
          {u 1,u 3,u 5} ∈ E ∧ {u 2,u 4,u 6} ∈ E)) ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2*y → x ≠ z → {x,y,z} ∈ E

/-- A transversal saving, uniform in the size of the sparse linear triple system. -/
def H2 : Prop := ∃ r : ℝ, r < 1/2 ∧ ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), E.card ≤ A.card →
    (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (∀ u : Fin 7 → ℝ, Function.Injective u →
      ¬ ({u 0,u 1,u 2} ∈ E ∧ {u 0,u 3,u 4} ∈ E ∧ {u 0,u 5,u 6} ∈ E ∧
        {u 1,u 3,u 5} ∈ E ∧ {u 2,u 4,u 6} ∈ E)) →
    ∃ T ⊆ A, (∀ e ∈ E, ∃ x ∈ e, x ∈ T) ∧ (T.card : ℝ) ≤ r*A.card

theorem main : H1 → H2 → OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H1 := by
  rintro geometry ⟨r,hr,cover⟩
  refine ⟨1-r, by linarith, ?_⟩
  intro A hA _hZ hfour
  let V := hA.toFinset
  have hV : (V : Set ℝ) = A := hA.coe_toFinset
  obtain ⟨E,small,triple,linear,free,progress⟩ := geometry V (by simpa [hV] using hfour)
  obtain ⟨T,sub,hit,cost⟩ := cover V E small triple linear free
  refine ⟨(↑(V \ T) : Set ℝ),?_,?_,?_⟩
  · exact hV ▸ (show ((V \ T : Finset ℝ) : Set ℝ) ⊆ (V : Set ℝ) from
      fun _ hx => (mem_sdiff.mp hx).1)
  · intro x hx y hy z hz hsum
    by_contra hne
    obtain ⟨w,hw,hwT⟩ := hit _ (progress x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1 z
      (mem_sdiff.mp hz).1 hsum hne)
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl|rfl
    · exact (mem_sdiff.mp hx).2 hwT
    · exact (mem_sdiff.mp hy).2 hwT
    · exact (mem_sdiff.mp hz).2 hwT
  · have total : ((V \ T).card : ℝ) + T.card = V.card := by
      exact_mod_cast card_sdiff_add_card_eq_card sub
    have cardA : A.ncard = V.card := by rw [← hV, Set.ncard_coe_finset]
    rw [cardA,Set.ncard_coe_finset]
    linarith

end OMA.Sparse757

/-!
# Arithmetic-progression triples in a (4,5)-set

The hypergraph framework and the forbidden configuration are due to
A. Gyárfás and J. Lehel, “Linear sets with five distinct differences among any
four elements” (1995), Proposition 2.6. See also J. Ma and Q. Tang,
“Largest Sidon subsets in weak Sidon sets,” arXiv:2602.23282, §5.2.
The real-linear certificates in this proof check the midpoint orientations
directly.
-/

section Four757

/- Arithmetic consequences of having at least five distances on every four
points. The certificates bound the full signed difference set by nine. -/
open Finset
open scoped Pointwise Classical
namespace OMA.Geo757

abbrev FourFive (A : Finset ℝ) := ∀ B ⊆ (A:Set ℝ), B.ncard=4 → 11≤(B-B).ncard
def AP (a b c : ℝ) := b+c=2*a ∨ a+c=2*b ∨ a+b=2*c

private theorem impossible {A : Finset ℝ} (hA : FourFive A) {a b c d : ℝ}
    (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd:d∈A)
    (ab:a≠b) (ac:a≠c) (ad:a≠d) (bc:b≠c) (bd:b≠d) (cd:c≠d)
    (p q r s : ℝ)
    (cover : ∀ x ∈ ({a,b,c,d}:Finset ℝ), ∀ y ∈ ({a,b,c,d}:Finset ℝ),
      x-y ∈ [0,p,-p,q,-q,r,-r,s,-s].toFinset) : False := by
  let B : Finset ℝ := {a,b,c,d}
  have large := hA (B:Set ℝ) (by
    intro x hx
    change x ∈ ({a,b,c,d}:Finset ℝ) at hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption)
    (by simp [B,ab,ac,ad,bc,bd,cd])
  rw [← coe_sub,Set.ncard_coe_finset] at large
  have small : B-B ⊆ [0,p,-p,q,-q,r,-r,s,-s].toFinset := by
    intro e he
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_sub.mp he
    exact cover x hx y hy
  have bound := (card_le_card small).trans (List.toFinset_card_le _)
  change (B-B).card≤9 at bound
  omega

theorem four_weak {A : Finset ℝ} (hA : FourFive A) {a b c d : ℝ}
    (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd:d∈A)
    (ab:a≠b) (ac:a≠c) (ad:a≠d) (bc:b≠c) (bd:b≠d) (cd:c≠d)
    (eq : a+b=c+d) : False := by
  apply impossible hA ha hb hc hd ab ac ad bc bd cd (a-b) (a-c) (a-d) (c-d)
  intro x hx y hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] <;>
    grind

theorem unique_triple {A : Finset ℝ} (hA : FourFive A) {a b c d : ℝ}
    (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd:d∈A)
    (ab:a≠b) (ac:a≠c) (ad:a≠d) (bc:b≠c) (bd:b≠d)
    (h : AP a b c) (h' : AP a b d) : c=d := by
  by_contra ne
  rcases h with h|h|h <;> rcases h' with g|g|g
  all_goals first | exact ne (by linarith only [h,g]) | skip
  case' inl.inr.inl => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-d) (c-d) 0
  case' inl.inr.inr => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-d) (b-c) (c-d)
  case' inr.inl.inl => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-c) (c-d) 0
  case' inr.inl.inr.inr => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-c) (a-d) (c-d)
  case' inr.inr.inl => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-c) (b-d) (c-d)
  case' inr.inr.inr.inl => apply impossible hA ha hb hc hd ab ac ad bc bd ne (a-b) (a-c) (a-d) (c-d)
  all_goals
    intro x hx y hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] <;> grind

end OMA.Geo757

end Four757

section Fseven757

/- The five-edge obstruction of Gyárfás and Lehel. After choosing the
midpoint of each progression, its equations force either two equal vertices
or equal sums on disjoint pairs. Each leaf below specifies witnesses and
checks the consequence in ordered-field arithmetic. -/

namespace OMA.Geo757

set_option maxHeartbeats 4000000 in
theorem excludeF7 (u : Fin 7 → ℝ)
    (same : ∀ i j, i ≠ j → u i ≠ u j)
    (weak : ∀ i j k l, (i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l) →
      u i+u j≠u k+u l)
    (t0 : AP (u 0) (u 1) (u 2))
    (t1 : AP (u 0) (u 3) (u 4))
    (t2 : AP (u 0) (u 5) (u 6))
    (t3 : AP (u 1) (u 3) (u 5))
    (t4 : AP (u 2) (u 4) (u 6)) : False := by
  rcases t0 with h0|h0|h0
  · rcases t1 with h1|h1|h1
    · exact weak 1 2 3 4 (by decide) (by linarith only [h0, h1])
    · rcases t2 with h2|h2|h2
      · exact weak 1 2 5 6 (by decide) (by linarith only [h0, h1, h2])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact weak 0 2 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 3 4 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
    · rcases t2 with h2|h2|h2
      · exact weak 1 2 5 6 (by decide) (by linarith only [h0, h1, h2])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact weak 0 1 2 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 4 3 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · exact weak 0 1 4 6 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 2 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 2 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
  · rcases t1 with h1|h1|h1
    · rcases t2 with h2|h2|h2
      · exact weak 3 4 5 6 (by decide) (by linarith only [h0, h1, h2])
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 2 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 2 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact weak 0 1 2 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
    · rcases t2 with h2|h2|h2
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 2 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 4 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact weak 0 3 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
    · rcases t2 with h2|h2|h2
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact weak 0 1 2 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 2 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
      · rcases t3 with h3|h3|h3
        · exact weak 0 2 3 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact weak 0 5 1 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 4 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · exact weak 0 1 4 6 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact weak 0 3 1 2 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact weak 0 5 1 2 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
  · rcases t1 with h1|h1|h1
    · rcases t2 with h2|h2|h2
      · exact weak 3 4 5 6 (by decide) (by linarith only [h0, h1, h2])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 2 1 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 2 1 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 3 2 6 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 4 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
    · rcases t2 with h2|h2|h2
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 2 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 2 1 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 4 1 2 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 6 1 2 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 3 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 4 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 4 1 5 (by decide) (by linarith only [h0, h1, h2, h3])
        · rcases t4 with h4|h4|h4
          · exact same 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 4 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
    · rcases t2 with h2|h2|h2
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 1 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 0 3 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 5 2 4 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · rcases t4 with h4|h4|h4
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 3 1 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · rcases t4 with h4|h4|h4
          · exact same 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact same 0 5 (by decide) (by linarith only [h0, h1, h2, h3, h4])
          · exact weak 0 1 3 6 (by decide) (by linarith only [h0, h1, h2, h3, h4])
        · exact weak 0 6 1 3 (by decide) (by linarith only [h0, h1, h2, h3])
      · rcases t3 with h3|h3|h3
        · exact weak 0 1 4 6 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 3 2 6 (by decide) (by linarith only [h0, h1, h2, h3])
        · exact weak 0 5 2 4 (by decide) (by linarith only [h0, h1, h2, h3])

end OMA.Geo757

end Fseven757

section Geo757

/- Assemble the finite arithmetic-progression hypergraph. Different edges
have different middle points and intersect in at most one vertex. -/
open Finset
open scoped Pointwise Classical
namespace OMA.Geo757

noncomputable def edges (A : Finset ℝ) : Finset (Finset ℝ) :=
  A.powerset.filter fun e ↦ ∃ a b c : ℝ, a<b ∧ b<c ∧ a+c=2*b ∧ e={a,b,c}

private theorem edge_spec {A : Finset ℝ} {e} (he:e∈edges A) :
    e ⊆ A ∧ ∃ a b c : ℝ, a<b ∧ b<c ∧ a+c=2*b ∧ e={a,b,c} := by
  simpa [edges] using he

private theorem size_three {A : Finset ℝ} {e} (he:e∈edges A) : e.card=3 := by
  obtain ⟨a,b,c,ab,bc,_,rfl⟩ := (edge_spec he).2
  simp [ab.ne,bc.ne,(ab.trans bc).ne]

private theorem edge_AP {A : Finset ℝ} {a b c} (h:({a,b,c}:Finset ℝ)∈edges A) : AP a b c := by
  obtain ⟨x,y,z,xy,yz,eq,he⟩ := (edge_spec h).2
  have hx : x∈({a,b,c}:Finset ℝ) := he ▸ (by simp)
  have hy : y∈({a,b,c}:Finset ℝ) := he ▸ (by simp)
  have hz : z∈({a,b,c}:Finset ℝ) := he ▸ (by simp)
  simp only [mem_insert,mem_singleton] at hx hy hz
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    rcases hz with rfl|rfl|rfl <;> unfold AP <;> grind

private theorem midpoint_inj {A : Finset ℝ} (hA:FourFive A) :
    (edges A).card≤A.card := by
  classical
  choose lo mid hi data using fun (e:↥(edges A)) ↦ (edge_spec e.2).2
  have inA (e:↥(edges A)) : lo e ∈ A ∧ mid e ∈ A ∧ hi e ∈ A := by
    have sub := (edge_spec e.2).1
    rw [(data e).2.2.2] at sub
    exact ⟨sub (by simp),sub (by simp),sub (by simp)⟩
  let m (e:↥(edges A)) : ↥A := ⟨mid e,(inA e).2.1⟩
  have inj : Function.Injective m := by
    intro e f eq
    have mm : mid e=mid f := congrArg Subtype.val eq
    obtain ⟨e1,e2,e3,e4⟩ := data e
    obtain ⟨f1,f2,f3,f4⟩ := data f
    have same : lo e=lo f := by
      by_contra ne
      have ne' : hi e≠hi f := by intro he; apply ne; linarith
      exact four_weak hA (inA e).1 (inA e).2.2 (inA f).1 (inA f).2.2
        (e1.trans e2).ne ne (by intro he; linarith) (by intro he; linarith) ne'
        (f1.trans f2).ne (by linarith)
    have last : hi e=hi f := by linarith
    apply Subtype.ext
    rw [e4,f4,same,mm,last]
  simpa using Fintype.card_le_of_injective m inj

private theorem extract {e : Finset ℝ} (he:e.card=3) {x y : ℝ}
    (hx:x∈e) (hy:y∈e) (ne:x≠y) : ∃ z∈e, x≠z ∧ y≠z ∧ e={x,y,z} := by
  obtain ⟨z,hz,hout⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x,y}:Finset ℝ).card<e.card by rw [card_pair ne,he]; decide)
  simp only [mem_insert,mem_singleton,not_or] at hout
  refine ⟨z,hz,Ne.symm hout.1,Ne.symm hout.2,?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl <;> assumption
  · simp [he,ne,Ne.symm hout.1,Ne.symm hout.2]

theorem geometry (A : Finset ℝ) (hA : FourFive A) :
    ∃ E : Finset (Finset ℝ), E.card ≤ A.card ∧
      (∀ e ∈ E, e ⊆ A ∧ e.card = 3) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ u : Fin 7 → ℝ, Function.Injective u →
        ¬ ({u 0,u 1,u 2} ∈ E ∧ {u 0,u 3,u 4} ∈ E ∧ {u 0,u 5,u 6} ∈ E ∧
          {u 1,u 3,u 5} ∈ E ∧ {u 2,u 4,u 6} ∈ E)) ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2*y → x ≠ z → {x,y,z} ∈ E := by
  refine ⟨edges A, midpoint_inj hA, fun _ he ↦ ⟨(edge_spec he).1,size_three he⟩,?_,?_,?_⟩
  · intro e he f hf ne
    by_contra! many
    obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp many
    obtain ⟨xe,xf⟩ := mem_inter.mp hx
    obtain ⟨ye,yf⟩ := mem_inter.mp hy
    obtain ⟨z,ze,xz,yz,eq⟩ := extract (size_three he) xe ye xy
    obtain ⟨w,wf,xw,yw,eq'⟩ := extract (size_three hf) xf yf xy
    have zw := unique_triple hA ((edge_spec he).1 xe) ((edge_spec he).1 ye)
      ((edge_spec he).1 ze) ((edge_spec hf).1 wf) xy xz xw yz yw
      (edge_AP (eq ▸ he)) (edge_AP (eq' ▸ hf))
    exact ne (by rw [eq,eq',zw])
  · intro u hu ⟨h0,h1,h2,h3,h4⟩
    have inc : ∀ i : Fin 7, u i∈A := by
      have a := (edge_spec h0).1
      have b := (edge_spec h1).1
      have c := (edge_spec h2).1
      intro i
      fin_cases i <;> first | apply a; solve | simp | done
                            | apply b; solve | simp | done
                            | apply c; simp
    apply excludeF7 u (fun _ _ h ↦ hu.ne h) _ (edge_AP h0) (edge_AP h1) (edge_AP h2)
      (edge_AP h3) (edge_AP h4)
    rintro i j k l ⟨ij,ik,il,jk,jl,kl⟩
    exact four_weak hA (inc i) (inc j) (inc k) (inc l)
      (hu.ne ij) (hu.ne ik) (hu.ne il) (hu.ne jk) (hu.ne jl) (hu.ne kl)
  · intro x hx y hy z hz eq ne
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_,?_⟩
    · intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption
    rcases lt_or_gt_of_ne ne with h|h
    · exact ⟨x,y,z,by linarith,by linarith,eq,rfl⟩
    · exact ⟨z,y,x,by linarith,by linarith,by linarith,by ext; simp; tauto⟩

end OMA.Geo757

end Geo757

theorem OMA.part1757 : OMA.Sparse757.H1 := OMA.Geo757.geometry

/-!
# A transversal of size strictly below half

This is a quantitative version of the argument of A. Gyárfás and J. Lehel,
“Linear sets with five distinct differences among any four elements” (1995),
Theorem 3.2(b), DOI 10.1006/jctb.1995.1028. We use the same five-edge,
seven-vertex forbidden configuration. The maximum matching and the random
choice among disjoint triples give the uniform transversal fraction 49999/100000.
-/


/- Local exchanges in a maximum matching of a simple subcubic graph.
The graph and its matchings are finite sets of unordered vertex pairs. -/
namespace OMA.Aug757
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

def PairwiseDisj (M : Finset (Finset α)) : Prop :=
  ∀ e∈M,∀ f∈M,e≠f → Disjoint e f
def free (M : Finset (Finset α)) (x : α) := x∉M.biUnion id
noncomputable def incident (E : Finset (Finset α)) (x : α) := E.filter (fun e ↦ x∈e)
noncomputable def outside (E M : Finset (Finset α)) (e : Finset α) :=
  E.filter fun f ↦ (e∩f).Nonempty ∧ ∃ x∈f,free M x
private noncomputable def leaves (E M : Finset (Finset α)) (a : α) :=
  (E.biUnion id).filter (fun z ↦ free M z ∧ ({a,z}:Finset α)∈E)

private theorem leaf_iff {E M : Finset (Finset α)} {a z:α} :
    z∈leaves E M a ↔ free M z ∧ ({a,z}:Finset α)∈E := by
  rw [leaves,mem_filter]
  exact ⟨And.right, fun h ↦ ⟨mem_biUnion.mpr ⟨_,h.2,by simp⟩,h⟩⟩

private theorem occupied {M : Finset (Finset α)} {e} (he:e∈M) {x} (hx:x∈e) : ¬free M x :=
  fun h ↦ h (mem_biUnion.mpr ⟨_,he,hx⟩)

private theorem pair_injective (a : α) : Function.Injective (fun z:α ↦ ({a,z}:Finset α)) := by
  intro z w eq
  change ({a,z}:Finset α)={a,w} at eq
  have h : z=a ∨ z=w := by
    have : z∈({a,w}:Finset α) := eq ▸ (by simp)
    simpa using this
  have h' : w=a ∨ w=z := by
    have : w∈({a,z}:Finset α) := eq.symm ▸ (by simp)
    simpa using this
  grind

private theorem exchange {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card)
    (A B : Finset (Finset α)) (am:A⊆M) (be:B⊆E) (bd:PairwiseDisj B)
    (meet : ∀ e∈B,∀x∈e,free M x ∨ ∃f∈A,x∈f)
    (new_nonempty : ∀ e∈B, e.Nonempty) : B.card≤A.card := by
  let R := M \ A
  have apart {b r} (hb:b∈B) (hr:r∈R) : Disjoint b r := by
    obtain ⟨hm,ha⟩ := mem_sdiff.mp hr
    apply disjoint_left.mpr
    intro x xb xr
    rcases meet b hb x xb with h|⟨f,fa,xf⟩
    · exact occupied hm xr h
    · exact disjoint_left.mp (md _ (am fa) _ hm (by rintro rfl;exact ha fa)) xf xr
  have d : Disjoint B R := by
    apply disjoint_left.mpr
    intro b hb hr
    obtain ⟨x,hx⟩ := new_nonempty b hb
    exact disjoint_left.mp (apart hb hr) hx hx
  have hmatch : PairwiseDisj (B∪R) := by
    intro b hb r hr ne
    rcases mem_union.mp hb with h|h <;> rcases mem_union.mp hr with k|k
    · exact bd _ h _ k ne
    · exact apart h k
    · exact (apart k h).symm
    · exact md _ (mem_sdiff.mp h).1 _ (mem_sdiff.mp k).1 ne
  have bound := maximal _ (union_subset be (Subset.trans sdiff_subset ms)) hmatch
  rw [card_union_of_disjoint d] at bound
  have rest : R.card+A.card=M.card := card_sdiff_add_card_eq_card am
  omega

private theorem exchange3 {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card)
    {a b u v : α} (ab:a≠b) (em:({a,b}:Finset α)∈M)
    (hu:u∈leaves E M a) (hv:v∈leaves E M b) : u=v := by
  by_contra uv
  obtain ⟨fu,au⟩ := leaf_iff.mp hu
  obtain ⟨fv,bv⟩ := leaf_iff.mp hv
  have na : ¬free M a := occupied em (by simp)
  have nb : ¬free M b := occupied em (by simp)
  have dis : Disjoint ({a,u}:Finset α) {b,v} := by
    simp only [disjoint_left,mem_insert,mem_singleton]
    grind
  have ne : ({a,u}:Finset α) ≠ {b,v} := by
    intro h; exact disjoint_left.mp dis (show a∈({a,u}:Finset α) by simp) (h ▸ (by simp))
  have bad := exchange ms md maximal ({ {a,b} }:Finset (Finset α)) { {a,u},{b,v} }
    (by simpa) (by simpa [insert_subset_iff] using And.intro au bv)
    (by intro e he f hf ef; simp only [mem_insert,mem_singleton] at he hf
        rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> first | exact dis | exact dis.symm | contradiction)
    (by intro e he x hx; simp only [mem_insert,mem_singleton] at he
        rcases he with rfl|rfl <;> simp only [mem_insert,mem_singleton] at hx <;>
          rcases hx with rfl|rfl <;> simp_all)
    (by intro e he; rcases mem_insert.mp he with rfl|h
        · simp
        · rw [mem_singleton.mp h];simp)
  simp [ne] at bad

private theorem exchange5 {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card)
    {a b c d u v : α} (ab:a≠b) (cd:c≠d)
    (em:({a,b}:Finset α)∈M) (fm:({c,d}:Finset α)∈M)
    (ef:({a,b}:Finset α)≠{c,d}) (cross:({a,c}:Finset α)∈E)
    (hu:u∈leaves E M b) (hv:v∈leaves E M d) : u=v := by
  by_contra uv
  obtain ⟨fu,bu⟩ := leaf_iff.mp hu
  obtain ⟨fv,dv⟩ := leaf_iff.mp hv
  have nfa := occupied em (show a∈({a,b}:Finset α) by simp)
  have nfb := occupied em (show b∈({a,b}:Finset α) by simp)
  have nfc := occupied fm (show c∈({c,d}:Finset α) by simp)
  have nfd := occupied fm (show d∈({c,d}:Finset α) by simp)
  have sep := md _ em _ fm ef
  simp only [disjoint_left,mem_insert,mem_singleton] at sep
  have bc : Disjoint ({b,u}:Finset α) {a,c} := by
    simp only [disjoint_left,mem_insert,mem_singleton];grind
  have bd : Disjoint ({b,u}:Finset α) {d,v} := by
    simp only [disjoint_left,mem_insert,mem_singleton];grind
  have ad : Disjoint ({a,c}:Finset α) {d,v} := by
    simp only [disjoint_left,mem_insert,mem_singleton];grind
  have diff {x y z w:α} (h:Disjoint ({x,y}:Finset α) {z,w}) : ({x,y}:Finset α)≠{z,w} := by
    intro e; exact disjoint_left.mp h (show x∈({x,y}:Finset α) by simp) (e ▸ (by simp))
  have bad := exchange ms md maximal ({ {a,b},{c,d} }:Finset (Finset α))
    { {b,u},{a,c},{d,v} }
    (by simp [insert_subset_iff,em,fm]) (by simp [insert_subset_iff,bu,cross,dv])
    (by intro e he f hf h
        simp only [mem_insert,mem_singleton] at he hf
        rcases he with rfl|rfl|rfl <;> rcases hf with rfl|rfl|rfl <;>
          first | assumption | exact bc.symm | exact bd.symm | exact ad.symm | contradiction)
    (by intro e he x hx
        simp only [mem_insert,mem_singleton] at he
        rcases he with rfl|rfl|rfl <;> simp only [mem_insert,mem_singleton] at hx <;>
          rcases hx with rfl|rfl <;> simp_all)
    (by intro e he; simp only [mem_insert,mem_singleton] at he
        rcases he with rfl|rfl|rfl <;> simp)
  simp [diff bc,diff bd,diff ad,ef] at bad

private theorem pair_of_two {e:Finset α} {x y:α} (two:e.card=2) (hx:x∈e) (hy:y∈e) (ne:x≠y) :
    ({x,y}:Finset α)=e := eq_of_subset_of_card_le (by simp [insert_subset_iff,hx,hy])
      (by rw [card_pair ne,two])

private noncomputable def attached (E M : Finset (Finset α)) (a : α) :=
  (leaves E M a).image fun z ↦ ({a,z}:Finset α)

private theorem attach_card (E M : Finset (Finset α)) (a:α) :
    (attached E M a).card=(leaves E M a).card := card_image_of_injective _ (pair_injective a)

private theorem split_outside {E M : Finset (Finset α)} (two : ∀e∈E,e.card=2)
    {a b:α} (ab:a≠b) (em:({a,b}:Finset α)∈M) :
    (outside E M {a,b}).card=(leaves E M a).card+(leaves E M b).card := by
  have oa := occupied em (show a∈({a,b}:Finset α) by simp)
  have ob := occupied em (show b∈({a,b}:Finset α) by simp)
  have one {x y:α} (xy:({x,y}:Finset α)={a,b}) {e:Finset α} (he:e∈attached E M x) :
      e∈outside E M {a,b} := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    obtain ⟨fr,ez⟩ := leaf_iff.mp hz
    exact mem_filter.mpr ⟨ez,⟨x,mem_inter.mpr ⟨xy ▸ (by simp),by simp⟩⟩,z,by simp,fr⟩
  have eq : outside E M {a,b}=attached E M a ∪ attached E M b := by
    ext e
    constructor
    · intro he
      obtain ⟨eE,⟨x,hx⟩,z,hz,fr⟩ := mem_filter.mp he
      obtain ⟨hx,xe⟩ := mem_inter.mp hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl
      · have p := pair_of_two (two _ eE) xe hz (by grind)
        rw [← p] at eE ⊢
        exact mem_union_left _ (mem_image_of_mem _ (leaf_iff.mpr ⟨fr,eE⟩))
      · have p := pair_of_two (two _ eE) xe hz (by grind)
        rw [← p] at eE ⊢
        exact mem_union_right _ (mem_image_of_mem _ (leaf_iff.mpr ⟨fr,eE⟩))
    · intro he
      rcases mem_union.mp he with h|h
      · exact one rfl h
      · exact one (Finset.pair_comm b a) h
  have dis : Disjoint (attached E M a) (attached E M b) := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    obtain ⟨w,hw,eq⟩ := mem_image.mp hf
    have h := leaf_iff.mp hz
    have k := leaf_iff.mp hw
    have a' : a∈({b,w}:Finset α) := eq.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at a'
    grind
  rw [eq,card_union_of_disjoint dis,attach_card,attach_card]

private theorem leaf_cap {E M : Finset (Finset α)} {a b:α} (eo:({a,b}:Finset α)∈E)
    (ob:¬free M b) (deg:(incident E a).card≤3) : (leaves E M a).card≤2 := by
  have no : ({a,b}:Finset α)∉attached E M a := by
    rintro h
    obtain ⟨z,hz,eq⟩ := mem_image.mp h
    have zb := pair_injective a eq
    exact ob (zb ▸ (leaf_iff.mp hz).1)
  have sub : insert {a,b} (attached E M a)⊆incident E a := by
    intro e he
    rcases mem_insert.mp he with rfl|h
    · exact mem_filter.mpr ⟨eo,by simp⟩
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨(leaf_iff.mp hz).2,by simp⟩
  have count := (card_le_card sub).trans deg
  rw [card_insert_of_notMem no,attach_card] at count
  omega

theorem outside_le_two {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card) (two : ∀e∈E,e.card=2)
    (degree : ∀x,(incident E x).card≤3) {e} (em:e∈M) : (outside E M e).card≤2 := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp (two e (ms em))
  rw [split_outside two ab em]
  have oa := occupied em (show a∈({a,b}:Finset α) by simp)
  have ob := occupied em (show b∈({a,b}:Finset α) by simp)
  by_cases ea:(leaves E M a).Nonempty
  · by_cases eb:(leaves E M b).Nonempty
    · obtain ⟨u,hu⟩ := ea
      obtain ⟨v,hv⟩ := eb
      have s1 : leaves E M a ⊆ {v} := fun _ h ↦ mem_singleton.mpr (exchange3 ms md maximal ab em h hv)
      have s2 : leaves E M b ⊆ {u} := fun _ h ↦ mem_singleton.mpr (exchange3 ms md maximal ab em hu h).symm
      simpa using Nat.add_le_add (card_le_card s1) (card_le_card s2)
    · rw [not_nonempty_iff_eq_empty.mp eb,card_empty,Nat.add_zero]
      exact leaf_cap (ms em) ob (degree _)
  · rw [not_nonempty_iff_eq_empty.mp ea,card_empty,Nat.zero_add]
    exact leaf_cap (by simpa [Finset.pair_comm b a] using ms em) oa (degree _)

private theorem neighbor_bound {E : Finset (Finset α)} {x:α} (L:Finset α)
    (adj:∀z∈L,({x,z}:Finset α)∈E) (cap:(incident E x).card≤3) : L.card≤3 := by
  apply le_trans _ cap
  rw [← card_image_of_injective L (pair_injective x)]
  apply card_le_card
  intro e he
  obtain ⟨z,hz,rfl⟩ := mem_image.mp he
  exact mem_filter.mpr ⟨adj z hz,by simp⟩

private theorem at_cross {E M : Finset (Finset α)} {a b c : α} (bc:b≠c)
    (e:({a,b}:Finset α)∈E) (f:({a,c}:Finset α)∈E)
    (ob:¬free M b) (oc:¬free M c) (cap:(incident E a).card≤3) : (leaves E M a).card≤1 := by
  let L := leaves E M a
  have nb : b∉L := fun h ↦ ob (leaf_iff.mp h).1
  have nc : c∉L := fun h ↦ oc (leaf_iff.mp h).1
  have sz := neighbor_bound (insert b (insert c L))
    (fun z hz ↦ (mem_insert.mp hz).elim (fun eq ↦ eq ▸ e) fun h ↦
      (mem_insert.mp h).elim (fun eq ↦ eq ▸ f) (fun zL ↦ (leaf_iff.mp zL).2)) cap
  simp only [mem_insert,bc,nb,nc,or_self,not_false_eq_true,
    card_insert_of_notMem] at sz
  change L.card≤1
  omega

private theorem orient_pair {e:Finset α} (two:e.card=2) {a:α} (ha:a∈e) :
    ∃ b, a≠b ∧ e={a,b} := by
  obtain ⟨x,y,xy,h⟩ := card_eq_two.mp two
  subst e
  rcases mem_insert.mp ha with rfl|h
  · exact ⟨y,xy,rfl⟩
  · rw [mem_singleton.mp h]
    exact ⟨x,xy.symm,Finset.pair_comm _ _⟩

/-- Maximum matching edges with two outside edges cannot be adjacent to
one another. No equality assumption on the endpoint degrees is needed. -/
theorem no_tight_cross {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card) (two : ∀e∈E,e.card=2)
    (degree : ∀x,(incident E x).card≤3) {e f} (em:e∈M) (fm:f∈M) (ef:e≠f)
    (oe:(outside E M e).card=2) (of':(outside E M f).card=2) :
    ¬ ∃ g∈E, (g∩e).Nonempty ∧ (g∩f).Nonempty := by
  rintro ⟨g,ge,⟨a,ha⟩,c,hc⟩
  obtain ⟨ag,ae⟩ := mem_inter.mp ha
  obtain ⟨cg,cf⟩ := mem_inter.mp hc
  have sep := md _ em _ fm ef
  have ac : a≠c := fun eq ↦ disjoint_left.mp sep ae (eq ▸ cf)
  obtain ⟨b,ab,rfl⟩ := orient_pair (two e (ms em)) ae
  obtain ⟨d,cd,rfl⟩ := orient_pair (two f (ms fm)) cf
  have cross : ({a,c}:Finset α)∈E := (pair_of_two (two g ge) ag cg ac) ▸ ge
  have na := occupied em (show a∈({a,b}:Finset α) by simp)
  have nc := occupied fm (show c∈({c,d}:Finset α) by simp)
  have nb := occupied em (show b∈({a,b}:Finset α) by simp)
  have nd := occupied fm (show d∈({c,d}:Finset α) by simp)
  have bc : b≠c := disjoint_iff_ne.mp sep _ (by simp) _ cf
  have ad : a≠d := disjoint_iff_ne.mp sep _ ae _ (by simp)
  have bd : b≠d := disjoint_iff_ne.mp sep _ (by simp) _ (by simp)
  have onea := at_cross bc (ms em) cross nb nc (degree a)
  have onec := at_cross ad.symm (ms fm) (Finset.pair_comm a c ▸ cross) nd na (degree c)
  rw [split_outside two ab em] at oe
  rw [split_outside two cd fm] at of'
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0<(leaves E M b).card)
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0<(leaves E M d).card)
  have eqUV := exchange5 ms md maximal ab cd em fm ef cross hu hv
  subst v
  have l1 : leaves E M b ⊆ {u} := fun _ hz ↦ mem_singleton.mpr
    (exchange5 ms md maximal ab cd em fm ef cross hz hv)
  have l2 : leaves E M d ⊆ {u} := fun _ hz ↦ mem_singleton.mpr
    (exchange5 ms md maximal ab cd em fm ef cross hu hz).symm
  have lb : (leaves E M b).card≤1 := by simpa using card_le_card l1
  have ld : (leaves E M d).card≤1 := by simpa using card_le_card l2
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<(leaves E M a).card)
  obtain ⟨y,hy⟩ := card_pos.mp (by omega : 0<(leaves E M c).card)
  have xeq := exchange3 ms md maximal ab em hx hu
  have yeq := exchange3 ms md maximal cd fm hy hv
  subst x; subst y
  have bad := neighbor_bound ({a,b,c,d}:Finset α) (x:=u)
    (by intro z hz; simp only [mem_insert,mem_singleton] at hz
        rcases hz with rfl|rfl|rfl|rfl
        · simpa [Finset.pair_comm u z] using (leaf_iff.mp hx).2
        · simpa [Finset.pair_comm u z] using (leaf_iff.mp hu).2
        · simpa [Finset.pair_comm u z] using (leaf_iff.mp hy).2
        · simpa [Finset.pair_comm u z] using (leaf_iff.mp hv).2) (degree u)
  simp [ab,ac,ad,bc,bd,cd] at bad

omit [DecidableEq α] in
theorem maximum (E : Finset (Finset α)) :
    ∃ M⊆E,PairwiseDisj M ∧ ∀ L⊆E,PairwiseDisj L → L.card≤M.card := by
  classical
  let C := E.powerset.filter PairwiseDisj
  have emp : ∅∈C := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [PairwiseDisj]⟩
  obtain ⟨M,hm,largest⟩ := exists_max_image C Finset.card ⟨_,emp⟩
  obtain ⟨me,md⟩ := mem_filter.mp hm
  exact ⟨M,mem_powerset.mp me,md,fun L le ld ↦ largest L (mem_filter.mpr ⟨mem_powerset.mpr le,ld⟩)⟩

theorem covered {E M : Finset (Finset α)} (ms:M⊆E) (md:PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card) {e} (he:e∈E) (ne:e.Nonempty) :
    ∃ x∈e, ¬free M x := by
  by_contra! allfree
  have bad := exchange ms md maximal ∅ {e} (empty_subset _) (singleton_subset_iff.mpr he)
    (by simp [PairwiseDisj]) (by simpa using allfree) (by simpa using ne)
  simp at bad

end OMA.Aug757

/- Count the matching edges reached by the endpoints of an unmatched edge. -/
namespace OMA.MatchFiber757
open Finset Aug757
open scoped Classical
variable {α : Type*} [DecidableEq α]

private theorem incident_card {M : Finset (Finset α)} (md : PairwiseDisj M) (x : α) :
    (incident M x).card = if free M x then 0 else 1 := by
  classical
  by_cases h : free M x
  · rw [if_pos h]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨em,xe⟩ := mem_filter.mp he
    exact h (mem_biUnion.mpr ⟨e,em,xe⟩)
  · rw [if_neg h]
    have hx : x∈M.biUnion id := not_not.mp h
    obtain ⟨e,em,xe⟩ := mem_biUnion.mp hx
    apply card_eq_one.mpr
    refine ⟨e, ?_⟩
    ext f
    simp only [incident,mem_filter,mem_singleton]
    constructor
    · rintro ⟨fm,xf⟩
      by_contra ne
      exact disjoint_left.mp (md f fm e em ne) xf xe
    · rintro rfl
      exact ⟨em,xe⟩

/-- Each occupied endpoint of an unmatched edge belongs to a different matching edge. -/
theorem fiber {E M : Finset (Finset α)} (ms : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E,PairwiseDisj L → L.card≤M.card) (two : ∀e∈E,e.card=2)
    (g : Finset α) (he : g∈E) (hm : g∉M) :
    (M.filter (fun e => (g∩e).Nonempty)).card = if ∃x∈g, free M x then 1 else 2 := by
  classical
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp (two g he)
  have eq : M.filter (fun e => (({a,b}:Finset α)∩e).Nonempty) =
      incident M a ∪ incident M b := by
    ext e
    simp only [incident,mem_filter,mem_union,Finset.Nonempty,mem_inter,mem_insert,mem_singleton]
    grind
  have sep : Disjoint (incident M a) (incident M b) := by
    apply disjoint_left.mpr
    intro e ha hb
    obtain ⟨em,ae⟩ := mem_filter.mp ha
    obtain ⟨_,be⟩ := mem_filter.mp hb
    have same : ({a,b}:Finset α)=e := eq_of_subset_of_card_le
      (by simp [insert_subset_iff,ae,be]) (by rw [card_pair ab,two e (ms em)])
    exact hm (same ▸ em)
  obtain ⟨x,hx,occ⟩ := covered ms md maximal he (by simp)
  rw [eq,card_union_of_disjoint sep,incident_card md,incident_card md]
  simp only [mem_insert,mem_singleton] at hx ⊢
  by_cases fa : free M a <;> by_cases fb : free M b <;> simp_all
  all_goals grind

end OMA.MatchFiber757

/- Incidence counts for a maximum matching in a simple subcubic graph. -/
namespace OMA.Count757
open Finset Aug757
open scoped Classical
variable {α : Type*} [DecidableEq α]

private noncomputable def touching (L : Finset (Finset α)) (e : Finset α) :=
  L.filter (fun g => (g∩e).Nonempty)

private theorem count_touch (K L : Finset (Finset α)) :
    ∑ e∈K, (touching L e).card = ∑ g∈L, (touching K g).card := by
  simp only [touching,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun g _ => sum_congr rfl (fun e _ => ?_))
  rw [inter_comm g e]

/-- After removing its own matching edge, each endpoint has at most two incident edges. -/
private theorem others_cap {E M : Finset (Finset α)} (sub : M⊆E)
    (two : ∀ e∈E, e.card=2) (degree : ∀ x,(incident E x).card≤3)
    {e} (he:e∈M) : (touching (E \ M) e).card≤4 := by
  obtain ⟨a,b,_,rfl⟩ := card_eq_two.mp (two e (sub he))
  let p : Finset α := {a,b}
  have subset : touching (E \ M) p ⊆ (incident E a).erase p ∪ (incident E b).erase p := by
    intro g hg
    obtain ⟨ng,x,hx⟩ := mem_filter.mp hg
    obtain ⟨ge,gm⟩ := mem_sdiff.mp ng
    have gp : g≠p := fun eq => gm (eq ▸ he)
    obtain ⟨xg,xp⟩ := mem_inter.mp hx
    rcases mem_insert.mp xp with rfl|xe
    · exact mem_union_left _ (mem_erase.mpr ⟨gp,mem_filter.mpr ⟨ge,xg⟩⟩)
    · rw [mem_singleton.mp xe] at xg
      exact mem_union_right _ (mem_erase.mpr ⟨gp,mem_filter.mpr ⟨ge,xg⟩⟩)
  have pa : p∈incident E a := mem_filter.mpr ⟨sub he,by simp [p]⟩
  have pb : p∈incident E b := mem_filter.mpr ⟨sub he,by simp [p]⟩
  have cap := (card_le_card subset).trans (card_union_le ..)
  rw [card_erase_of_mem pa,card_erase_of_mem pb] at cap
  have da := degree a
  have db := degree b
  change (touching (E \ M) p).card≤4
  omega

/-- Each unmatched edge either meets one matched cell and a free vertex, or
joins two matched cells. No edge of the latter type joins two cells that
both have two outside neighbors. -/
theorem count {E M : Finset (Finset α)} (sub : M⊆E) (md : PairwiseDisj M)
    (maximal : ∀ L⊆E, PairwiseDisj L → L.card≤M.card)
    (two : ∀ e∈E,e.card=2) (degree : ∀ x,(incident E x).card≤3)
    (fiber : ∀ g∈E, g∉M → (M.filter (fun e => (g∩e).Nonempty)).card =
      if ∃ x∈g, free M x then 1 else 2) : 6*E.card≤23*M.card := by
  let U := E \ M
  let O := U.filter (fun g => ∃ x∈g, free M x)
  let C := U \ O
  let T := M.filter (fun e => (outside E M e).card=2)
  let D := M \ T
  have ou : O⊆U := filter_subset ..
  have tm : T⊆M := filter_subset ..
  have dd : D⊆M := sdiff_subset
  have um : U.card+M.card=E.card := card_sdiff_add_card_eq_card sub
  have cu : C.card+O.card=U.card := card_sdiff_add_card_eq_card ou
  have dT : D.card+T.card=M.card := card_sdiff_add_card_eq_card tm
  have outEq (e : Finset α) : touching O e = outside E M e := by
    ext g
    simp only [touching,O,U,outside,mem_filter,mem_sdiff,inter_comm e g]
    constructor
    · rintro ⟨⟨⟨he,_⟩,leaf⟩,meet⟩; exact ⟨he,meet,leaf⟩
    · rintro ⟨he,meet,x,hx,freeX⟩
      exact ⟨⟨⟨he, fun gm => freeX (mem_biUnion.mpr ⟨g,gm,hx⟩)⟩,x,hx,freeX⟩,meet⟩
  have split (e : Finset α) : (touching C e).card+(touching O e).card=(touching U e).card := by
    have h : touching C e = touching U e \ touching O e := by
      ext g
      simp only [C,touching,mem_sdiff,mem_filter]
      tauto
    rw [h]
    exact card_sdiff_add_card_eq_card (filter_subset_filter _ ou)
  have cap (e) (he:e∈M) : (touching C e).card+(touching O e).card≤4 :=
    (split e).trans_le (others_cap sub two degree he)
  have sizes {g} (gU:g∈U) : (touching M g).card = if ∃ x∈g, free M x then 1 else 2 := by
    simpa only [touching,inter_comm g] using fiber g (mem_sdiff.mp gU).1 (mem_sdiff.mp gU).2
  have oCount : ∑ e∈M,(touching O e).card = O.card := by
    rw [count_touch]
    calc
      _ = ∑ _g∈O,(1:ℕ) := sum_congr rfl (fun g hg => (sizes (ou hg)).trans (if_pos (mem_filter.mp hg).2))
      _ = _ := by simp
  have twoC (g) (hg:g∈C) : (touching M g).card=2 := by
    obtain ⟨gu,go⟩ := mem_sdiff.mp hg
    exact (sizes gu).trans (if_neg (fun leaf => go (mem_filter.mpr ⟨gu,leaf⟩)))
  have cCount : ∑ e∈M,(touching C e).card = 2*C.card := by
    rw [count_touch]
    calc
      _ = ∑ _g∈C,(2:ℕ) := sum_congr rfl twoC
      _ = _ := by simp [Nat.mul_comm]
  let c (e : Finset α) := (touching C e).card
  let o (e : Finset α) := (touching O e).card
  have cSplit : (∑ e∈D,c e)+(∑ e∈T,c e)=2*C.card := (sum_sdiff tm).trans cCount
  have oSplit : (∑ e∈D,o e)+(∑ e∈T,o e)=O.card := (sum_sdiff tm).trans oCount
  have sat (e) (he:e∈T) : o e=2 := (congrArg Finset.card (outEq e)).trans (mem_filter.mp he).2
  have defic (e) (he:e∈D) : o e≤1 := by
    have bound := outside_le_two sub md maximal two degree (dd he)
    have ne : (outside E M e).card≠2 := fun h => (mem_sdiff.mp he).2 (mem_filter.mpr ⟨dd he,h⟩)
    change (touching O e).card≤1
    rw [outEq]
    omega
  have satO : ∑ e∈T,o e=2*T.card := (sum_const_nat sat).trans (Nat.mul_comm ..)
  have satC : ∑ e∈T,c e≤2*T.card := calc
    _ ≤ ∑ _e∈T,2 := sum_le_sum (fun e he => by have h := cap e (tm he); have t := sat e he;change c e+o e≤4 at h;omega)
    _ = _ := by simp [Nat.mul_comm]
  have defO : ∑ e∈D,o e≤D.card := (sum_le_sum defic).trans_eq (by simp)
  have defBoth : (∑ e∈D,c e)+(∑ e∈D,o e)≤4*D.card := by
    rw [←sum_add_distrib]
    calc
      _ ≤ ∑ _e∈D,4 := sum_le_sum (fun e he => cap e (dd he))
      _ = _ := by simp [Nat.mul_comm]
  have across : ∑ e∈T,c e≤∑ e∈D,c e := by
    change (∑ e∈T,(touching C e).card)≤∑ e∈D,(touching C e).card
    rw [count_touch T C,count_touch D C]
    apply sum_le_sum
    intro g hg
    have cone : (touching T g).card≤1 := by
      apply card_le_one.mpr
      intro e he f hf
      by_contra ef
      obtain ⟨et,eg⟩ := mem_filter.mp he
      obtain ⟨ft,fg⟩ := mem_filter.mp hf
      apply no_tight_cross sub md maximal two degree (tm et) (tm ft) ef
        (mem_filter.mp et).2 (mem_filter.mp ft).2
      exact ⟨g,(mem_sdiff.mp (mem_sdiff.mp hg).1).1,inter_comm e g ▸ eg,inter_comm f g ▸ fg⟩
    have part : touching D g = touching M g \ touching T g := by
      ext e
      simp only [D,touching,mem_filter,mem_sdiff]
      tauto
    have counts : (touching D g).card+(touching T g).card=(touching M g).card := by
      rw [part]
      exact card_sdiff_add_card_eq_card (filter_subset_filter _ tm)
    have h := twoC g hg
    omega
  omega

end OMA.Count757

/- Independent choices of one point per disjoint triple can simultaneously
cover all arms at a positive fraction of the centers. -/
namespace OMA.Improve757
open Finset
open scoped Classical

private theorem average {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (boxes : ι → Finset α) (three : ∀ i, (boxes i).card=3)
    (good : (ι→α) → α → Prop)
    (localChoice : ∀ x∈S, ∃ (X : Finset ι) (t : ι → α), X.card≤3 ∧
      (∀ i, t i∈boxes i) ∧ ∀ u, (∀ i∈X,u i=t i) → good u x) :
    ∃ u∈Fintype.piFinset boxes, S.card ≤ 27*(S.filter (good u)).card := by
  let Ω := Fintype.piFinset boxes
  have pos : 0<Ω.card := by simp [Ω,Fintype.card_piFinset,three]
  have freq (x : α) (hx : x∈S) : Ω.card ≤ 27*(Ω.filter (fun u => good u x)).card := by
    obtain ⟨X,t,hX,ht,hg⟩ := localChoice x hx
    let restricted (i : ι) := if i∈X then {t i} else boxes i
    have sub : Fintype.piFinset restricted ⊆ Ω.filter (fun u => good u x) := by
      intro u hu
      have mem := Fintype.mem_piFinset.mp hu
      apply mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        by_cases hi : i∈X
        · have : u i=t i := by simpa [restricted,hi] using mem i
          rw [this]; exact ht i
        · simpa [restricted,hi] using mem i
      · apply hg
        intro i hi
        simpa [restricted,hi] using mem i
    have hprod : (Fintype.piFinset restricted).card = 3^(Fintype.card ι-X.card) := by
      rw [Fintype.card_piFinset]
      have f (i : ι) : (restricted i).card = if i∈X then 1 else 3 := by
        by_cases h : i∈X <;> simp [restricted,h,three]
      simp_rw [f]
      rw [Finset.prod_ite]
      simp [← Finset.sdiff_eq_filter,Finset.card_sdiff_of_subset]
    have mult : Ω.card=3^X.card*(Fintype.piFinset restricted).card := by
      rw [hprod,←pow_add,Nat.add_sub_of_le (Finset.card_le_univ X)]
      simp [Ω,Fintype.card_piFinset,three]
    calc _ = _ := mult
         _ ≤ 27*(Ω.filter (fun u => good u x)).card :=
           Nat.mul_le_mul (show 3^X.card ≤ 3^3 from Nat.pow_le_pow_right (by decide) hX) (card_le_card sub)
  by_contra! no
  have double : ∑ x ∈ S, (Ω.filter fun u=>good u x).card =
      ∑ u ∈ Ω, (S.filter (good u)).card := by
    simp only [Finset.card_filter]
    exact sum_comm
  have lower : S.card*Ω.card ≤ 27*(∑ u ∈ Ω, (S.filter (good u)).card) := by
    rw [←double,mul_sum]
    simpa using sum_le_sum freq
  have upper : ∑ u ∈ Ω, 27*(S.filter (good u)).card < Ω.card*S.card := by
    simpa using (sum_lt_sum_of_nonempty (card_pos.mp pos) (fun u hu => no u hu))
  rw [←mul_sum] at upper
  rw [Nat.mul_comm Ω.card S.card] at upper
  omega

private theorem obstruction (E : Finset (Finset ℝ))
    (tri : ∀ e∈E, e.card=3)
    (lin : ∀ e∈E, ∀ f∈E, e≠f → (e∩f).card≤1)
    (free : ¬∃ v : Fin 7→ℝ, Function.Injective v ∧
      {v 0,v 1,v 2}∈E ∧ {v 0,v 3,v 4}∈E ∧ {v 0,v 5,v 6}∈E ∧
      {v 1,v 3,v 5}∈E ∧ {v 2,v 4,v 6}∈E)
    (x : ℝ) (l r : Finset ℝ) (hl : l∈E) (hr : r∈E) (dis : Disjoint l r)
    (xl : x∉l) (xr : x∉r) (P : Fin 3→Finset ℝ) (Pinj : Function.Injective P)
    (hm : ∀ i, P i∈E) (xm : ∀ i,x∈P i)
    (left : ∀ i, (P i∩l).Nonempty) (right : ∀ i, (P i∩r).Nonempty) : False := by
  choose u hu using left
  choose v hv using right
  have ul (i) := (mem_inter.mp (hu i)).2
  have vr (i) := (mem_inter.mp (hv i)).2
  have xu (i) : x≠u i := fun e => xl (e ▸ ul i)
  have xv (i) : x≠v i := fun e => xr (e ▸ vr i)
  have uv (i j) : u i≠v j := fun e => disjoint_left.mp dis (ul i) (e ▸ vr j)
  have column (w : Fin 3→ℝ) (wx : ∀ i, x≠w i) (wp : ∀ i, w i∈P i) : Function.Injective w := by
    intro i j eq
    by_contra ne
    have small := card_le_one.mp (lin _ (hm i) _ (hm j) (Pinj.ne ne))
    exact wx i (small x (mem_inter.mpr ⟨xm i,xm j⟩) (w i) (mem_inter.mpr ⟨wp i,eq ▸ wp j⟩))
  have ui := column u xu (fun i => (mem_inter.mp (hu i)).1)
  have vi := column v xv (fun i => (mem_inter.mp (hv i)).1)
  have P_eq (i) : {x,u i,v i} = P i := by
    apply eq_of_subset_of_card_le
    · simp [insert_subset_iff,xm,(mem_inter.mp (hu i)).1,(mem_inter.mp (hv i)).1]
    · simp [tri _ (hm i),xu,xv,uv]
  have col_eq (w : Fin 3 → ℝ) (a : Finset ℝ) (ma : a∈E) (wi : Function.Injective w)
      (wa : ∀ i, w i∈a) : {w 0,w 1,w 2} = a := by
    apply eq_of_subset_of_card_le
    · simp [insert_subset_iff,wa]
    · simp [tri a ma,wi.eq_iff]
  let idx : Fin 7→Option (Bool × Fin 3) := ![none,some (false,0),some (true,0),
    some (false,1),some (true,1),some (false,2),some (true,2)]
  let lab : Option (Bool × Fin 3) → ℝ
    | none => x
    | some (false,i) => u i
    | some (true,i) => v i
  have injLab : Function.Injective lab := by
    rintro (_|⟨b,i⟩) (_|⟨c,j⟩) eq
    · rfl
    · cases c
      · exact (xu j eq).elim
      · exact (xv j eq).elim
    · cases b
      · exact (xu i eq.symm).elim
      · exact (xv i eq.symm).elim
    · cases b <;> cases c
      · have e := ui (show u i=u j from eq); subst j; rfl
      · exact (uv _ _ eq).elim
      · exact (uv _ _ eq.symm).elim
      · have e := vi (show v i=v j from eq); subst j; rfl
  let z := lab ∘ idx
  apply free
  refine ⟨z,?_,P_eq 0 ▸ hm 0,P_eq 1 ▸ hm 1,P_eq 2 ▸ hm 2,?_,?_⟩
  · exact injLab.comp (by dsimp [idx]; decide)
  · change {u 0,u 1,u 2}∈E
    rw [col_eq u l hl ui ul];exact hl
  · change {v 0,v 1,v 2}∈E
    rw [col_eq v r hr vi vr];exact hr

/-- Choose different residual triples for all arms of a center. Hall can only
fail if three arms go through a pair of triples, forming the forbidden F₇. -/
private theorem match_arms (E F : Finset (Finset ℝ)) (x : ℝ) (J : Finset (Finset ℝ))
    (tri : ∀ e∈E, e.card=3) (lin : ∀ e∈E, ∀ f∈E, e≠f → (e∩f).card≤1)
    (free : ¬∃ v : Fin 7→ℝ, Function.Injective v ∧
      {v 0,v 1,v 2}∈E ∧ {v 0,v 3,v 4}∈E ∧ {v 0,v 5,v 6}∈E ∧
      {v 1,v 3,v 5}∈E ∧ {v 2,v 4,v 6}∈E)
    (sub : F⊆E) (pairs : ∀ l∈F, ∀ r∈F, l≠r → Disjoint l r)
    (xf : ∀ l∈F, x∉l) (jc : J.card≤3) (jE : J⊆E) (jx : ∀ e∈J, x∈e)
    (many : ∀ e∈J, 2 ≤ (F.filter fun b => (e∩b).Nonempty).card) :
    ∃ f : J→Finset ℝ, Function.Injective f ∧ ∀ i, f i∈F ∧ (i.val∩f i).Nonempty := by
  let neigh (i : J) := F.filter (fun b => (i.val ∩ b).Nonempty)
  suffices h : ∀ s : Finset J, s.card ≤ (s.biUnion neigh).card by
    obtain ⟨f,inj,mem⟩ := (all_card_le_biUnion_card_iff_existsInjective' neigh).mp h
    exact ⟨f,inj,fun i => mem_filter.mp (mem i)⟩
  intro s
  by_contra! bad
  have upper : s.card≤3 := (card_le_univ _).trans (by simpa using jc)
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<s.card)
  have lo : 2 ≤ (s.biUnion neigh).card :=
    (many i i.property).trans (card_le_card (subset_biUnion_of_mem neigh hi))
  have eq3 : s.card=3 := by omega
  have eq2 : (s.biUnion neigh).card=2 := by omega
  obtain ⟨l,r,lr,eq⟩ := card_eq_two.mp eq2
  have cover (j : J) (hj : j∈s) : neigh j = {l,r} := by
    rw [←eq]
    apply eq_of_subset_of_card_le (subset_biUnion_of_mem neigh hj)
    rw [eq2];exact many j j.property
  have ends (j : J) (hj : j∈s) : (l∈F ∧ (j.val∩l).Nonempty) ∧ (r∈F ∧ (j.val∩r).Nonempty) := by
    constructor <;> apply mem_filter.mp
    · change l∈neigh j;rw [cover j hj];simp
    · change r∈neigh j;rw [cover j hj];simp
  let π := (s.equivFinOfCardEq eq3).symm
  let P (j : Fin 3) := ((π j).val).val
  have Pinj : Function.Injective P := Subtype.val_injective.comp (Subtype.val_injective.comp π.injective)
  obtain ⟨⟨hl,_⟩,hr,_⟩ := ends i hi
  exact obstruction E tri lin free x l r (sub hl) (sub hr) (pairs l hl r hr lr) (xf l hl) (xf r hr) P Pinj
    (fun j => jE (π j).val.property) (fun j => jx _ (π j).val.property)
    (fun j => (ends _ (π j).property).1.2) (fun j => (ends _ (π j).property).2.2)

theorem core_cover (S : Finset ℝ) (F E : Finset (Finset ℝ))
    (tri : ∀ e∈E, e.card=3) (lin : ∀ e∈E, ∀ f∈E, e≠f → (e∩f).card≤1)
    (free : ¬∃ v : Fin 7→ℝ, Function.Injective v ∧
      {v 0,v 1,v 2}∈E ∧ {v 0,v 3,v 4}∈E ∧ {v 0,v 5,v 6}∈E ∧
      {v 1,v 3,v 5}∈E ∧ {v 2,v 4,v 6}∈E)
    (sub : F⊆E) (pairs : ∀ l∈F, ∀ r∈F, l≠r → Disjoint l r)
    (separate : ∀ l∈F, Disjoint S l)
    (inside : ∀ e∈E, e ⊆ S ∪ F.biUnion id)
    (center : ∀ e∈E, e∈F ∨ (e∩S).card=1)
    (degree : ∀ x∈S, (E.filter (fun e => x∈e)).card≤3) :
    ∃ T ⊆ S ∪ F.biUnion id, (∀ e∈E,(e∩T).Nonempty) ∧ 27*T.card ≤ 26*S.card+27*F.card := by
  let boxes (i : F) := i.val
  let good (u : F→ℝ) (x : ℝ) := ∀ e∈E, x∈e → ∃ b : F,u b∈e
  have localChoice (x : ℝ) (hx : x∈S) :
      ∃ (X : Finset F) (t : F→ℝ), X.card ≤ 3 ∧ (∀ i,t i∈boxes i) ∧
        ∀ u, (∀ i∈X,u i=t i) → good u x := by
    let J := E.filter (fun e => x∈e)
    have jE : J⊆E := filter_subset ..
    have jx (e) (he : e∈J) := (mem_filter.mp he).2
    have xf (l) (hl:l∈F) : x∉l := fun h => disjoint_left.mp (separate l hl) hx h
    have many (e) (he:e∈J) : 2 ≤ (F.filter (fun b => (e∩b).Nonempty)).card := by
      have xe := jx e he
      have ce := (center e (jE he)).resolve_left (fun h => xf e h xe)
      have two : (e.erase x).card = 2 := by rw [card_erase_of_mem xe, tri _ (jE he)]
      obtain ⟨a,b,ab,pair⟩ := card_eq_two.mp two
      have ea : a∈e.erase x := by rw [pair]; simp
      have eb : b∈e.erase x := by rw [pair]; simp
      have block (q : ℝ) (hq:q∈e.erase x) : ∃ B∈F,q∈B := by
        obtain ⟨nq,qe⟩ := mem_erase.mp hq
        have qs : q∉S := fun qs => nq (card_le_one.mp ce.le q (mem_inter.mpr ⟨qe,qs⟩) x (mem_inter.mpr ⟨xe,hx⟩))
        exact mem_biUnion.mp ((mem_union.mp (inside e (jE he) qe)).resolve_left qs)
      obtain ⟨l,hl,al⟩ := block a ea
      obtain ⟨r,hr,br⟩ := block b eb
      have ax := (mem_erase.mp ea).2
      have bx := (mem_erase.mp eb).2
      have lr : l≠r := by
        rintro rfl
        have ne : e ≠ l := fun eq => xf l hl (eq ▸ xe)
        exact ab (card_le_one.mp (lin e (jE he) l (sub hl) ne) a (mem_inter.mpr ⟨ax,al⟩)
          b (mem_inter.mpr ⟨bx,br⟩))
      exact one_lt_card.mpr ⟨l,mem_filter.mpr ⟨hl,⟨a,mem_inter.mpr ⟨ax,al⟩⟩⟩,
        r,mem_filter.mpr ⟨hr,⟨b,mem_inter.mpr ⟨bx,br⟩⟩⟩,lr⟩
    obtain ⟨f,fi,hf⟩ := match_arms E F x J tri lin free sub pairs xf (degree x hx) jE jx many
    let g (j : J) : F := ⟨f j,(hf j).1⟩
    have gi : Function.Injective g := fun i j eq => fi (congrArg Subtype.val eq)
    choose v hv using (fun j => (hf j).2)
    have box_mem (i : F) : (boxes i).Nonempty := card_pos.mp (by rw [show (boxes i).card=3 from tri _ (sub i.property)];decide)
    let t (i : F) := if h : ∃ j,g j=i then v h.choose else (box_mem i).choose
    have te (j : J) : t (g j)=v j := by
      have ex : ∃ i,g i=g j := ⟨j,rfl⟩
      simp only [t,dif_pos ex]
      exact congrArg v (gi ex.choose_spec)
    refine ⟨univ.image g,t,(card_image_le.trans (by simpa using degree x hx)),?_,?_⟩
    · intro i
      by_cases ex : ∃ j,g j=i
      · obtain ⟨j,rfl⟩ := ex
        rw [te]
        exact (mem_inter.mp (hv j)).2
      · rw [show t i=(box_mem i).choose by dsimp only [t];rw [dif_neg ex]]
        exact (box_mem i).choose_spec
    · intro u hit e he xe
      let j : J := ⟨e,mem_filter.mpr ⟨he,xe⟩⟩
      refine ⟨g j,?_⟩
      rw [hit (g j) (mem_image_of_mem _ (mem_univ _)),te]
      exact (mem_inter.mp (hv j)).1
  obtain ⟨u,hu,size⟩ := average S boxes (fun i => tri _ (sub i.property)) good localChoice
  let B := univ.image u
  let G := S.filter (good u)
  let T := B ∪ (S \ G)
  have restriction (i : F) : u i∈i.val := (Fintype.mem_piFinset.mp hu) i
  have uB (i : F) : u i∈B := mem_image_of_mem _ (mem_univ _)
  refine ⟨T,?_,?_,?_⟩
  · intro z hz
    rcases mem_union.mp hz with h|h
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact mem_union_right _ (mem_biUnion.mpr ⟨i.val,i.property,restriction i⟩)
    · exact mem_union_left _ (mem_sdiff.mp h).1
  · intro e he
    rcases center e he with hf|hc
    · let i : F := ⟨e,hf⟩
      exact ⟨u i,mem_inter.mpr ⟨restriction i,mem_union_left _ (uB i)⟩⟩
    · obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<(e∩S).card)
      obtain ⟨xe,xs⟩ := mem_inter.mp hx
      by_cases saved : good u x
      · obtain ⟨i,hi⟩ := saved e he xe
        exact ⟨u i,mem_inter.mpr ⟨hi,mem_union_left _ (uB i)⟩⟩
      · have no : x∉G := fun h => saved (mem_filter.mp h).2
        exact ⟨x,mem_inter.mpr ⟨xe,mem_union_right _ (mem_sdiff.mpr ⟨xs,no⟩)⟩⟩
  · have hT : T.card ≤ B.card+(S \ G).card := card_union_le ..
    have exactSize := card_sdiff_add_card_eq_card (show G⊆S from filter_subset ..)
    have hB : B.card ≤ F.card := card_image_le.trans (by simp)
    have saved : S.card≤27*G.card := by
      convert! size using 1
      congr 2
      ext z
      simp only [G,mem_filter]
    omega


end OMA.Improve757

/- Two greedy phases for the Gyárfás–Lehel transversal bound. A newly
selected center pays for itself by removing at least k edges. When the
original degree is at most k, none of those edges can have met an earlier
center. -/
namespace OMA.Peel757
open Finset
open scoped Classical

noncomputable def unhit (E : Finset (Finset ℝ)) (S : Finset ℝ) :=
  E.filter fun e ↦ Disjoint e S

private theorem degree_zero {E : Finset (Finset ℝ)} {S : Finset ℝ} {x : ℝ} (hx:x∈S) :
    ((unhit E S).filter fun e ↦ x∈e).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨h,xe⟩ := mem_filter.mp he
  exact disjoint_left.mp (mem_filter.mp h).2 xe hx

private theorem peel (V : Finset ℝ) (E : Finset (Finset ℝ)) (k : ℕ) (hk:0<k) :
    ∃ S ⊆ V, k*S.card+(unhit E S).card≤E.card ∧
      (∀ x∈V, ((unhit E S).filter (fun e ↦ x∈e)).card<k) ∧
      ((∀ x∈V, (E.filter (fun e ↦ x∈e)).card≤k) → ∀ e∈E,(e∩S).card≤1) := by
  classical
  let ok (S : Finset ℝ) := k*S.card+(unhit E S).card≤E.card ∧
    ((∀ x∈V, (E.filter (fun e ↦ x∈e)).card≤k) → ∀ e∈E,(e∩S).card≤1)
  let choices := V.powerset.filter ok
  have emp : ∅ ∈ choices := by
    apply mem_filter.mpr
    exact ⟨mem_powerset.mpr (empty_subset _), by simp [ok,unhit]⟩
  obtain ⟨S,hs,best⟩ := exists_max_image choices Finset.card ⟨_,emp⟩
  obtain ⟨sv,hs⟩ := mem_filter.mp hs
  have sub := mem_powerset.mp sv
  refine ⟨S,sub,hs.1,?_,hs.2⟩
  intro x hv
  by_cases hx:x∈S
  · simpa [degree_zero hx] using hk
  by_contra! many
  let P := unhit E S
  let J := P.filter fun e ↦ x∈e
  have remove : J.card+(unhit E (insert x S)).card=P.card := by
    convert card_filter_add_card_filter_not (s:=P) (fun e ↦ x∈e) using 2
    congr 1
    ext e
    simp [P,unhit,disjoint_insert_right,and_comm,and_left_comm,and_assoc]
  have augment : insert x S ∈ choices := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset hv sub),?_,?_⟩
    · rw [card_insert_of_notMem hx,Nat.mul_succ]
      change k≤J.card at many
      have prior : k*S.card+P.card≤E.card := hs.1
      omega
    · intro cap e he
      by_cases xe:x∈e
      · have full : J=E.filter (fun e ↦ x∈e) := eq_of_subset_of_card_le
          (filter_subset_filter _ (filter_subset ..)) ((cap x hv).trans many)
        have ej : e∈J := full ▸ mem_filter.mpr ⟨he,xe⟩
        have dis := (mem_filter.mp (mem_filter.mp ej).1).2
        have small : e∩insert x S ⊆ {x} := by
          intro z hz
          obtain ⟨ze,zs⟩ := mem_inter.mp hz
          exact mem_singleton.mpr ((mem_insert.mp zs).resolve_right (disjoint_left.mp dis ze))
        simpa using card_le_card small
      · have eq : e∩insert x S=e∩S := by
          ext y
          simp only [mem_inter,mem_insert]
          grind
        exact eq ▸ hs.2 cap e he
  have bad := best _ augment
  rw [card_insert_of_notMem hx] at bad
  omega

/-- The high-degree centers, then the three-edge centers, with their edge
budgets, residual degree bounds, and independence of the second group. -/
theorem decompose (V : Finset ℝ) (E : Finset (Finset ℝ)) :
    ∃ S₀ ⊆ V, ∃ S₁ ⊆ V \ S₀,
      let P := unhit E S₀
      let R := unhit P S₁
      4*S₀.card+3*S₁.card+R.card≤E.card ∧
      (∀ x∈V,(P.filter (fun e ↦ x∈e)).card≤3) ∧
      (∀ x∈V,(R.filter (fun e ↦ x∈e)).card≤2) ∧
      (∀ e∈P,(e∩S₁).card≤1) := by
  obtain ⟨S₀,hS₀,h0,d0,_⟩ := peel V E 4 (by decide)
  let P := unhit E S₀
  obtain ⟨S₁,hS₁,h1,d1,l1⟩ := peel (V \ S₀) P 3 (by decide)
  refine ⟨S₀,hS₀,S₁,hS₁,?_,fun x hx ↦ Nat.le_of_lt_succ (d0 x hx),?_,
    l1 (fun x hx ↦ Nat.le_of_lt_succ (d0 x (mem_sdiff.mp hx).1))⟩
  · change 4*S₀.card+3*S₁.card+(unhit P S₁).card≤E.card
    change 4*S₀.card+P.card≤E.card at h0
    omega
  · intro x hx
    by_cases h:x∈S₀
    · have z := degree_zero (E:=E) h
      have sub := card_le_card (filter_subset_filter (fun e ↦ x∈e)
        (show unhit P S₁ ⊆ P from filter_subset ..))
      exact sub.trans (by simpa only [P,z] using (by decide : 0≤2))
    · exact Nat.le_of_lt_succ (d1 x (mem_sdiff.mpr ⟨hx,h⟩))

/-- Restore all selected centers after covering the degree-two residual. -/
theorem extend (V : Finset ℝ) (E : Finset (Finset ℝ)) (S₀ S₁ U : Finset ℝ)
    (s0 : S₀⊆V) (s1 : S₁⊆V \ S₀) (uv : U⊆V)
    (hit : ∀e∈unhit (unhit E S₀) S₁, (e∩U).Nonempty) :
    ∃ T⊆V, (∀e∈E,(e∩T).Nonempty) ∧ T.card≤S₀.card+S₁.card+U.card := by
  refine ⟨(S₀∪S₁)∪U,union_subset (union_subset s0 (Subset.trans s1 sdiff_subset)) uv,?_,?_⟩
  · intro e he
    by_cases a:Disjoint e S₀
    · by_cases b:Disjoint e S₁
      · obtain ⟨x,hx⟩ := hit e (mem_filter.mpr ⟨mem_filter.mpr ⟨he,a⟩,b⟩)
        exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hx).1,mem_union_right _ (mem_inter.mp hx).2⟩⟩
      · obtain ⟨x,xe,xs⟩ := not_disjoint_iff.mp b
        exact ⟨x,mem_inter.mpr ⟨xe,mem_union_left _ (mem_union_right _ xs)⟩⟩
    · obtain ⟨x,xe,xs⟩ := not_disjoint_iff.mp a
      exact ⟨x,mem_inter.mpr ⟨xe,mem_union_left _ (mem_union_left _ xs)⟩⟩
  · exact (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)

end OMA.Peel757

/- The degree-two remainder of the transversal construction of Gyárfás--Lehel:
degree-two vertices are the edges of its simple dual graph. The isolated
triples form the disjoint boxes used for local improvements. -/
namespace OMA.Residual757
open Finset
open scoped Classical

noncomputable def layer (V : Finset ℝ) (R : Finset (Finset ℝ)) (i : ℕ) :=
  V.filter (fun x => (R.filter (fun e=>x∈e)).card=i)

noncomputable def boxes (V : Finset ℝ) (R : Finset (Finset ℝ)) :=
  R.filter (fun e => e⊆layer V R 1)

/-- The three residual degree layers partition the vertices. Counting incidences
by vertices and by triples also determines the size of the remaining edge set. -/
theorem layer_counts (V : Finset ℝ) (R : Finset (Finset ℝ))
    (inside : ∀ e∈R, e⊆V) (tri : ∀ e∈R, e.card=3)
    (degree : ∀ x∈V, (R.filter (fun e=>x∈e)).card≤2) :
    V.card = (layer V R 0).card + (layer V R 1).card + (layer V R 2).card ∧
    3*R.card = (layer V R 1).card + 2*(layer V R 2).card := by
  let d (x : ℝ) := (R.filter (fun e => x∈e)).card
  have coeff (i : ℕ) : (layer V R i).card = ∑ x∈V, (if d x=i then 1 else 0) := by
    change (V.filter (fun x => d x=i)).card = _
    rw [card_eq_sum_ones, sum_filter]
  have doubleCount : ∑ x∈V, d x = 3*R.card := by
    calc
      _ = ∑ e∈R, (V.filter (fun x => x∈e)).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x e => x∈e)
      _ = ∑ _e∈R, 3 := by
        refine sum_congr rfl (fun e he => ?_)
        have h : V.filter (·∈e) = e := by
          ext x
          exact mem_filter.trans ⟨And.right, fun hx => ⟨inside e he hx, hx⟩⟩
        rw [h, tri e he]
      _ = _ := by simp [Nat.mul_comm]
  constructor
  · rw [coeff, coeff, coeff, ←sum_add_distrib, ←sum_add_distrib, card_eq_sum_ones]
    refine sum_congr rfl (fun x hx => ?_)
    have hd : d x≤2 := degree x hx
    interval_cases h : d x <;> decide
  · rw [←doubleCount, coeff, coeff, mul_sum, ←sum_add_distrib]
    refine sum_congr rfl (fun x hx => ?_)
    have hd : d x≤2 := degree x hx
    interval_cases h : d x <;> decide

theorem boxes_spec (V : Finset ℝ) (R : Finset (Finset ℝ))
    (inside : ∀ e∈R, e⊆V) (tri : ∀ e∈R, e.card=3)
    (degree : ∀ x∈V, (R.filter (fun e=>x∈e)).card≤2) :
    boxes V R ⊆ R ∧
    (∀ e∈boxes V R, ∀ f∈boxes V R, e≠f → Disjoint e f) ∧
    (boxes V R).biUnion id ⊆ layer V R 1 ∧
    (layer V R 1 \ (boxes V R).biUnion id).card ≤ 4*(layer V R 2).card ∧
    ∀ e∈R, e⊆(boxes V R).biUnion id → e∈boxes V R := by
  let F := boxes V R
  have sub : F⊆R := filter_subset ..
  have deg1 (e) (he:e∈F) : e⊆layer V R 1 := (mem_filter.mp he).2
  have uni : F.biUnion id ⊆ layer V R 1 := by
    intro x hx
    obtain ⟨e,he,hx⟩ := mem_biUnion.mp hx
    exact deg1 e he hx
  refine ⟨sub,?_,uni,?_,fun e he h => mem_filter.mpr ⟨he,h.trans uni⟩⟩
  · intro e he f hf ne
    apply disjoint_left.mpr
    intro x xe xf
    have dx := (mem_filter.mp (deg1 e he xe)).2
    exact ne (card_le_one.mp dx.le e (mem_filter.mpr ⟨sub he,xe⟩) f (mem_filter.mpr ⟨sub hf,xf⟩))
  · let near (x : ℝ) := (R.filter (fun e=>x∈e)).biUnion (fun e => e.erase x)
    have cap (x : ℝ) (hx : x∈layer V R 2) : (near x).card ≤ 4 := by
      calc
        _ ≤ ∑ e ∈ R.filter (fun e=>x∈e), (e.erase x).card := card_biUnion_le
        _ = ∑ _e ∈ R.filter (fun e=>x∈e), 2 := by
          apply sum_congr rfl
          intro e he
          obtain ⟨he,xe⟩ := mem_filter.mp he
          rw [card_erase_of_mem xe,tri e he]
        _ = 4 := by simp [(mem_filter.mp hx).2]
    have bound : layer V R 1 \ F.biUnion id ⊆ (layer V R 2).biUnion near := by
      intro y hy
      obtain ⟨hd1,notIn⟩ := mem_sdiff.mp hy
      obtain ⟨yv,h1⟩ := mem_filter.mp hd1
      obtain ⟨e,he⟩ := card_pos.mp (by omega : 0<(R.filter (fun e=>y∈e)).card)
      obtain ⟨er,ye⟩ := mem_filter.mp he
      have notBox : ¬e⊆layer V R 1 := fun h => notIn (mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨er,h⟩,ye⟩)
      obtain ⟨x,xe,out⟩ := Finset.not_subset.mp notBox
      have xv := inside e er xe
      have one : (R.filter (fun e=>x∈e)).card ≠ 1 := fun h => out (mem_filter.mpr ⟨xv,h⟩)
      have pos : 0<(R.filter (fun e=>x∈e)).card := card_pos.mpr ⟨e,mem_filter.mpr ⟨er,xe⟩⟩
      have ub := degree x xv
      have xy : y≠x := fun h => out (h ▸ hd1)
      exact mem_biUnion.mpr ⟨x,mem_filter.mpr ⟨xv,by omega⟩,
        mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨er,xe⟩,mem_erase.mpr ⟨xy,ye⟩⟩⟩
    calc
      _ ≤ _ := card_le_card bound
      _ ≤ ∑ x ∈ layer V R 2, (near x).card := card_biUnion_le
      _ ≤ ∑ _x ∈ layer V R 2, 4 := sum_le_sum cap
      _ = _ := by simp [Nat.mul_comm]

/-- Count the vertices in the disjoint boxes, or within one step of a
degree-two vertex. -/
theorem boxes_budget (V : Finset ℝ) (R : Finset (Finset ℝ))
    (inside : ∀ e∈R, e⊆V) (tri : ∀ e∈R, e.card=3)
    (degree : ∀ x∈V, (R.filter (fun e=>x∈e)).card≤2) :
    (layer V R 1).card ≤ 3*(boxes V R).card + 4*(layer V R 2).card := by
  obtain ⟨sub, _, covered, leftover, _⟩ := boxes_spec V R inside tri degree
  have size : ((boxes V R).biUnion id).card ≤ 3*(boxes V R).card := calc
    _ ≤ ∑ e∈boxes V R, e.card := card_biUnion_le
    _ = ∑ _e∈boxes V R, 3 := sum_congr rfl (fun e he => tri e (sub he))
    _ = _ := by simp [Nat.mul_comm]
  have partition := card_sdiff_add_card_eq_card covered
  omega

private theorem lifts (V : Finset ℝ) (R : Finset (Finset ℝ))
    (inside : ∀ e∈R, e⊆V) (tri : ∀ e∈R, e.card=3)
    (N : ℝ→Finset (Finset ℝ)) (Adj : ∀ x, N x=R.filter (fun e=>x∈e))
    (M : Finset (Finset (Finset ℝ))) (sub : M⊆(layer V R 2).image N)
    (dis : ∀ a∈M, ∀ b∈M, a≠b → Disjoint a b) :
    ∃ T⊆V, (∀ e∈R,(e∩T).Nonempty) ∧ T.card+M.card ≤ R.card := by
  let U := M.biUnion id
  have chooseX (p : M) : ∃ x∈layer V R 2, N x=p.val := mem_image.mp (sub p.property)
  choose x hx xe using chooseX
  have two (p : M) : p.val.card=2 := by rw [←xe p, Adj];exact (mem_filter.mp (hx p)).2
  have cover (p : M) {e} (he : e∈p.val) : e∈R ∧ x p∈e := by
    rw [←xe p,Adj] at he
    exact mem_filter.mp he
  have ur : U⊆R := by
    intro e he
    obtain ⟨p,hp,ep⟩ := mem_biUnion.mp he
    exact (cover ⟨p,hp⟩ ep).1
  have count : U.card=2*M.card := by
    rw [show U=M.biUnion id from rfl,card_biUnion (by exact fun p hp q hq pq => dis p hp q hq pq)]
    trans ∑ _p∈M, 2
    · exact sum_congr rfl (fun p hp => two ⟨p,hp⟩)
    · simp [Nat.mul_comm]
  let rest := R \ U
  have chooseY (e : rest) : e.val.Nonempty := card_pos.mp (by rw [tri _ (mem_sdiff.mp e.property).1];decide)
  choose y hy using chooseY
  let C := univ.image x
  let D := univ.image y
  refine ⟨C∪D,?_,?_,?_⟩
  · intro z m
    rcases mem_union.mp m with m|m
    · obtain ⟨p,_,rfl⟩ := mem_image.mp m
      exact (mem_filter.mp (hx p)).1
    · obtain ⟨e,_,rfl⟩ := mem_image.mp m
      exact inside _ (mem_sdiff.mp e.property).1 (hy e)
  · intro e he
    by_cases m : e∈U
    · obtain ⟨p,hp,ep⟩ := mem_biUnion.mp m
      let i : M := ⟨p,hp⟩
      exact ⟨x i,mem_inter.mpr ⟨(cover i ep).2,mem_union_left _ (mem_image_of_mem _ (mem_univ i))⟩⟩
    · let i : rest := ⟨e,mem_sdiff.mpr ⟨he,m⟩⟩
      exact ⟨y i,mem_inter.mpr ⟨hy i,mem_union_right _ (mem_image_of_mem _ (mem_univ i))⟩⟩
  · have c : C.card≤M.card := card_image_le.trans (by simp)
    have d : D.card≤rest.card := card_image_le.trans (by simp)
    have total : rest.card+U.card=R.card := card_sdiff_add_card_eq_card ur
    have un := card_union_le C D
    omega

theorem residual_cover
    (matching : ∀ (Vg : Finset (Finset ℝ)) (Eg : Finset (Finset (Finset ℝ))),
      (∀ e∈Eg,e.card=2) → (∀e∈Eg,e⊆Vg) → (∀v∈Vg,(Eg.filter (fun e=>v∈e)).card≤3) →
      ∃ M⊆Eg, (∀ a∈M,∀ b∈M,a≠b → Disjoint a b) ∧ 6*Eg.card≤23*M.card)
    (V : Finset ℝ) (R : Finset (Finset ℝ))
    (inside : ∀ e∈R,e⊆V) (tri : ∀ e∈R,e.card=3)
    (lin : ∀ e∈R,∀ f∈R,e≠f → (e∩f).card≤1) :
    ∃ T⊆V, (∀ e∈R,(e∩T).Nonempty) ∧ 23*T.card+6*(layer V R 2).card≤23*R.card := by
  let N (x : ℝ) := R.filter (fun e=>x∈e)
  let E := (layer V R 2).image N
  have size (p) (hp : p∈E) : p.card=2 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact (mem_filter.mp hx).2
  have sub (p) (hp : p∈E) : p⊆R := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp hp
    exact filter_subset ..
  have inj : Set.InjOn N (layer V R 2:Set ℝ) := by
    intro x hx y hy eq
    obtain ⟨e,he,f,hf,ef⟩ := one_lt_card.mp (by rw [show (N x).card=2 from (mem_filter.mp hx).2];decide)
    have le := card_le_one.mp (lin e (mem_filter.mp he).1 f (mem_filter.mp hf).1 ef)
    have ey : e∈N y := eq ▸ he
    have fy : f∈N y := eq ▸ hf
    exact le x (mem_inter.mpr ⟨(mem_filter.mp he).2,(mem_filter.mp hf).2⟩) y
      (mem_inter.mpr ⟨(mem_filter.mp ey).2,(mem_filter.mp fy).2⟩)
  have de (e) (he : e∈R) : (E.filter (fun p => e∈p)).card≤3 := by
    have s : E.filter (fun p => e∈p) ⊆ e.image N := by
      intro p hp
      obtain ⟨ep,ve⟩ := mem_filter.mp hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ep
      exact mem_image_of_mem _ (mem_filter.mp ve).2
    exact (card_le_card s).trans (card_image_le.trans_eq (tri e he))
  obtain ⟨M,mE,dis,large⟩ := matching R E size sub de
  obtain ⟨T,tV,hT,sz⟩ := lifts V R inside tri N (fun _ => rfl) M mE dis
  have count : E.card=(layer V R 2).card := card_image_of_injOn inj
  exact ⟨T,tV,hT,by omega⟩

/-- Compare the two constructed covers: either the matching saves vertices
in the degree-two remainder, or the random choices save enough centers. -/
theorem size_choice {n s₀ s₁ p₀ p₁ p₂ r f t₁ t₂ : ℕ}
    (partition : n=s₀+s₁+p₀+p₁+p₂) (incidence : 3*r=p₁+2*p₂)
    (budget : 4*s₀+3*s₁+r≤n) (boxes_large : p₁≤3*f+4*p₂)
    (first : 23*t₁+6*p₂≤23*(s₀+s₁+r)) (second : 27*t₂+s₁+54*f≤27*n) :
    100000*t₁≤49999*n ∨ 100000*t₂≤49999*n := by
  by_contra! bad
  obtain ⟨a,b⟩ := bad
  linarith only [partition, incidence, budget, boxes_large, first, second,
    a, b, Nat.zero_le s₀, Nat.zero_le p₀, Nat.zero_le p₂, Nat.zero_le n]

end OMA.Residual757

/- Restrict to the surviving centers and the disjoint triples. A transversal
on this restriction extends to all edges by including the discarded vertices. -/
namespace OMA.Peel757
open Finset
open scoped Classical

theorem improved (V : Finset ℝ) (E : Finset (Finset ℝ)) (S₀ S₁ : Finset ℝ)
    (F : Finset (Finset ℝ))
    (tri : ∀ e∈E,e⊆V ∧ e.card=3)
    (lin : ∀ e∈E,∀ f∈E,e≠f → (e∩f).card≤1)
    (free : ∀ u : Fin 7 → ℝ, Function.Injective u →
      ¬ ({u 0,u 1,u 2}∈E ∧ {u 0,u 3,u 4}∈E ∧ {u 0,u 5,u 6}∈E ∧
        {u 1,u 3,u 5}∈E ∧ {u 2,u 4,u 6}∈E))
    (sv : S₁⊆V \ S₀)
    (cap : ∀ x∈V,((unhit E S₀).filter (fun e ↦ x∈e)).card≤3)
    (single : ∀ e∈unhit E S₀,(e∩S₁).card≤1)
    (sub : F⊆unhit (unhit E S₀) S₁)
    (pairs : ∀ e∈F, ∀ f∈F, e≠f → Disjoint e f)
    (closed : ∀ e∈unhit (unhit E S₀) S₁, e⊆F.biUnion id → e∈F) :
    ∃ T⊆V, (∀e∈E,(e∩T).Nonempty) ∧ 27*T.card+S₁.card+54*F.card≤27*V.card := by
  let P := unhit E S₀
  let W := S₁ ∪ F.biUnion id
  let H := E.filter fun e ↦ e⊆W
  have inP {e} (he:e∈F) : e∈P := (mem_filter.mp (sub he)).1
  have inE {e} (he:e∈F) : e∈E := (mem_filter.mp (inP he)).1
  have sep {e} (he:e∈F) : Disjoint S₁ e := (mem_filter.mp (sub he)).2.symm
  have Wv : W⊆V := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact (mem_sdiff.mp (sv h)).1
    obtain ⟨e,he,xe⟩ := mem_biUnion.mp h
    exact (tri _ (inE he)).1 xe
  have sep0 : Disjoint W S₀ := by
    apply disjoint_left.mpr
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact (mem_sdiff.mp (sv h)).2
    obtain ⟨e,he,xe⟩ := mem_biUnion.mp h
    exact disjoint_left.mp (mem_filter.mp (inP he)).2 xe
  have hP : H⊆P := by
    intro e he
    obtain ⟨eE,eW⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨eE,sep0.mono_left eW⟩
  have hE : H⊆E := filter_subset ..
  have fH : F⊆H := by
    intro e he
    exact mem_filter.mpr ⟨inE he,fun _ hx ↦ mem_union_right _ (mem_biUnion.mpr ⟨_,he,hx⟩)⟩
  have center {e} (he:e∈H) : e∈F ∨ (e∩S₁).card=1 := by
    by_cases h:Disjoint e S₁
    · left
      apply closed _ (mem_filter.mpr ⟨hP he,h⟩)
      intro x hx
      exact (mem_union.mp ((mem_filter.mp he).2 hx)).resolve_left (disjoint_left.mp h hx)
    · right
      have n : (e∩S₁).Nonempty := nonempty_iff_ne_empty.mpr (fun eq ↦ h (disjoint_iff_inter_eq_empty.mpr eq))
      exact le_antisymm (single e (hP he)) (card_pos.mpr n)
  obtain ⟨T,tW,hit,cost⟩ := OMA.Improve757.core_cover S₁ F H
    (fun e he ↦ (tri _ (hE he)).2) (fun e he f hf ↦ lin _ (hE he) _ (hE hf))
    (by rintro ⟨u,ui,h0,h1,h2,h3,h4⟩; exact free u ui ⟨hE h0,hE h1,hE h2,hE h3,hE h4⟩)
    fH pairs (fun _ he ↦ sep he) (fun _ he ↦ (mem_filter.mp he).2) (fun _ he ↦ center he)
    (fun x hx ↦ (card_le_card (filter_subset_filter (fun e ↦ x∈e) hP)).trans
      (cap x (mem_sdiff.mp (sv hx)).1))
  let T' := T ∪ (V \ W)
  refine ⟨T',union_subset (Subset.trans tW Wv) sdiff_subset,?_,?_⟩
  · intro e he
    by_cases inside:e⊆W
    · obtain ⟨x,hx⟩ := hit e (mem_filter.mpr ⟨he,inside⟩)
      exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hx).1,mem_union_left _ (mem_inter.mp hx).2⟩⟩
    · obtain ⟨x,xe,xw⟩ := not_subset.mp inside
      exact ⟨x,mem_inter.mpr ⟨xe,mem_union_right _ (mem_sdiff.mpr ⟨(tri _ he).1 xe,xw⟩)⟩⟩
  · have dis : Disjoint S₁ (F.biUnion id) := by
      apply disjoint_left.mpr
      intro x xs xb
      obtain ⟨e,he,xe⟩ := mem_biUnion.mp xb
      exact disjoint_left.mp (sep he) xs xe
    have boxsize : (F.biUnion id).card=3*F.card := by
      rw [card_biUnion (t:=id) (fun i hi j hj ne ↦ pairs _ hi _ hj ne)]
      calc
        _ = ∑ _e ∈ F, 3 := sum_congr rfl (fun e he ↦ (tri _ (inE he)).2)
        _ = _ := by simp [Nat.mul_comm]
    have wsize : W.card=S₁.card+3*F.card := (card_union_of_disjoint dis).trans (by rw [boxsize])
    have rest := card_sdiff_add_card_eq_card Wv
    have upper : T'.card ≤ T.card+(V \ W).card := card_union_le ..
    omega

end OMA.Peel757

/- The uniform transversal saving for the sparse progression hypergraph. -/
namespace OMA.Finish757
open Finset Residual757 Peel757
open scoped Classical

/-- Combine the two transversals of the sparse triple system. The first comes
from a matching on the degree-two remainder; the second changes the choices
on isolated triples to save a positive fraction of the degree-three centers. -/
theorem of_matching
    (matching : ∀ (Vg : Finset (Finset ℝ)) (Eg : Finset (Finset (Finset ℝ))),
      (∀ e∈Eg,e.card=2) → (∀e∈Eg,e⊆Vg) → (∀v∈Vg,(Eg.filter (fun e=>v∈e)).card≤3) →
      ∃ M⊆Eg, (∀ a∈M,∀ b∈M,a≠b → Disjoint a b) ∧ 6*Eg.card≤23*M.card) :
    OMA.Sparse757.H2 := by
  refine ⟨49999/100000, by norm_num, ?_⟩
  intro A E thin tri lin free
  obtain ⟨S₀,s₀,S₁,s₁,edgeBudget,cap3,cap2,single⟩ := decompose A E
  let P := unhit E S₀
  let R := unhit P S₁
  let V := (A \ S₀) \ S₁
  have VA : V ⊆ A := Subset.trans sdiff_subset sdiff_subset
  have subE : R ⊆ E := Subset.trans (filter_subset ..) (filter_subset ..)
  have inside (e) (he:e∈R) : e⊆V := by
    intro x hx
    obtain ⟨hp,hs₁⟩ := mem_filter.mp he
    obtain ⟨he,hs₀⟩ := mem_filter.mp hp
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(tri e he).1 hx,disjoint_left.mp hs₀ hx⟩,
      disjoint_left.mp hs₁ hx⟩
  have three (e) (he:e∈R) := (tri e (subE he)).2
  have degree (x) (hx:x∈V) := cap2 x (VA hx)
  obtain ⟨U,uV,uhit,uCost⟩ := residual_cover matching V R inside three
    (fun e he f hf => lin e (subE he) f (subE hf))
  obtain ⟨T₁,t₁,hit₁,addCost⟩ := extend A E S₀ S₁ U s₀ s₁ (Subset.trans uV VA) uhit
  let F := boxes V R
  obtain ⟨fr,pair,_,_,closed⟩ := boxes_spec V R inside three degree
  obtain ⟨T₂,t₂,hit₂,two⟩ := improved A E S₀ S₁ F tri lin free s₁ cap3 single fr pair closed
  obtain ⟨vCount,incidence⟩ := layer_counts V R inside three degree
  have part : A.card=S₀.card+S₁.card+(layer V R 0).card+(layer V R 1).card+(layer V R 2).card := by
    have a := card_sdiff_add_card_eq_card s₀
    have b : V.card+S₁.card=(A \ S₀).card := card_sdiff_add_card_eq_card s₁
    omega
  have small : 4*S₀.card+3*S₁.card+R.card≤A.card := edgeBudget.trans thin
  have one : 23*T₁.card+6*(layer V R 2).card≤23*(S₀.card+S₁.card+R.card) := by omega
  have boxBound := boxes_budget V R inside three degree
  have convertCost (T : Finset ℝ) (smallT : 100000*T.card≤49999*A.card)
      (sub : T⊆A) (hit : ∀ e∈E, (e∩T).Nonempty) :
      ∃ T ⊆ A, (∀ e∈E, ∃ x∈e, x∈T) ∧ (T.card:ℝ)≤49999/100000*A.card := by
    refine ⟨T,sub,?_,?_⟩
    · intro e he
      obtain ⟨x,hx⟩ := hit e he
      exact ⟨x,mem_inter.mp hx⟩
    · have castCost : (100000:ℝ)*T.card≤49999*A.card := by exact_mod_cast smallT
      linarith
  rcases size_choice part incidence small boxBound one two with h|h
  · exact convertCost T₁ h t₁ hit₁
  · exact convertCost T₂ h t₂ hit₂

end OMA.Finish757

/- The complete transversal saving for the Gyárfás--Lehel obstruction. -/
namespace OMA.Count757
open Finset Aug757
open scoped Classical

/-- A simple graph of maximum degree three has a matching containing at least
`6/23` of its edges. The chosen matching has maximum cardinality. -/
theorem matching {α : Type*} [DecidableEq α]
    (V : Finset α) (E : Finset (Finset α)) (two : ∀ e∈E,e.card=2)
    (within : ∀ e∈E,e⊆V) (degree : ∀ x∈V,(E.filter (fun e => x∈e)).card≤3) :
    ∃ M⊆E, (∀ a∈M,∀ b∈M,a≠b → Disjoint a b) ∧ 6*E.card≤23*M.card := by
  obtain ⟨M,ms,md,maximal⟩ := maximum E
  have cap (x) : (incident E x).card≤3 := by
    by_cases hv : x∈V
    · exact degree x hv
    · have empty : incident E x=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        obtain ⟨ee,xe⟩ := mem_filter.mp he
        exact hv (within e ee xe))
      simp [empty]
  exact ⟨M,ms,md,count ms md maximal two cap (OMA.MatchFiber757.fiber ms md maximal two)⟩

end OMA.Count757

theorem OMA.part2757 : OMA.Sparse757.H2 :=
  OMA.Finish757.of_matching OMA.Count757.matching

theorem OMA.Leaf1.solve : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H1 :=
  OMA.Sparse757.main OMA.part1757 OMA.part2757


/-!
Freiman transfer: a finite set of reals is the image of an additive map into the integers,
injective on differences. The map is a rational linear form on a Hamel basis, scaled to clear
denominators. The argument is the standard one; the write-up here is independent.
-/

open scoped Pointwise
open Module

namespace Erdos757Transfer

lemma exists_dual_eq_one {V : Type*} [AddCommGroup V] [Module ℚ V] {v : V} (hv : v ≠ 0) :
    ∃ f : Dual ℚ V, f v = 1 := by
  classical
  have hli : LinearIndepOn ℚ (fun _ : Unit => v) Set.univ := by
    rw [linearIndepOn_univ_iff]
    exact (linearIndependent_unique_iff (R := ℚ) (v := fun _ : Unit => v)).2 hv
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hli
  exact ⟨f, hf () ⟨⟩⟩

/-- A rational linear form that avoids zero on a finite set of nonzero vectors. -/
lemma exists_dual_ne_zero_on {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Finset V)
    (hs : ∀ x ∈ s, x ≠ 0) : ∃ f : Dual ℚ V, ∀ x ∈ s, f x ≠ 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    obtain ⟨g, hg⟩ := exists_dual_eq_one (V := V) ha0
    let bad : Finset ℚ :=
      insert (-(f a)) ((s.filter fun x => g x ≠ 0).image fun x => -(f x) / g x)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert (0 : ℚ) bad)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    have hcbad : c ∉ bad := fun h => hc (by simp [h])
    refine ⟨f + c • g, ?_⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxa | hx
    · subst hxa
      rw [LinearMap.add_apply, LinearMap.smul_apply, hg, smul_eq_mul, mul_one]
      intro hzero
      apply hcbad
      have hcneg : c = -(f x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hzero
      rw [hcneg]
      exact Finset.mem_insert_self _ _
    · rw [LinearMap.add_apply, LinearMap.smul_apply]
      by_cases hgx : g x = 0
      · simpa [hgx] using hf x hx
      · intro hsum
        apply hcbad
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hgx⟩, ?_⟩)
        have hsum' : c * g x = -(f x) := by
          rw [← sub_eq_zero]
          linear_combination hsum
        exact (eq_div_of_mul_eq hgx hsum').symm

/-- Clear denominators of a finite set of rationals. -/
lemma exists_clear_denoms (s : Finset ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ s, ∃ z : ℤ, (N : ℚ) * q = z := by
  classical
  refine ⟨∏ q ∈ s, q.den, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun q _ => q.den_ne_zero
  · intro q hq
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq
    refine ⟨q.num * k, ?_⟩
    calc
      ((∏ r ∈ s, r.den : ℕ) : ℚ) * q = ((q.den * k : ℕ) : ℚ) * q := by rw [hk]
      _ = (q.den : ℚ) * (k : ℚ) * q := by push_cast; ring
      _ = (k : ℚ) * (q.den * q) := by ring
      _ = (k : ℚ) * q.num := by rw [Rat.den_mul_eq_num]
      _ = (q.num * k : ℤ) := by push_cast; ring

end Erdos757Transfer

theorem OMA.Leaf2.solve : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H2 := by
  intro A hA
  classical
  have hdiff : ((A - A) - (A - A)).Finite := (hA.sub hA).sub (hA.sub hA)
  let D : Finset ℝ := hdiff.toFinset.erase 0
  have hD : ∀ x ∈ D, x ≠ 0 := fun x hx => (Finset.mem_erase.mp hx).1
  obtain ⟨φ, hφ⟩ := Erdos757Transfer.exists_dual_ne_zero_on D hD
  obtain ⟨N, hN, hclear⟩ :=
    Erdos757Transfer.exists_clear_denoms (hA.toFinset.image fun a => φ a)
  let scale : ℝ → ℚ := fun x => (N : ℚ) * φ x
  let f : ℝ →+ ℝ :=
    { toFun := fun x => (scale x : ℝ)
      map_zero' := by simp [scale]
      map_add' := fun x y => by
        simp only [scale, map_add, mul_add, Rat.cast_add] }
  refine ⟨f, ?_, ?_⟩
  · intro x hx y hy hfeq
    have hqe : scale x = scale y := Rat.cast_injective hfeq
    have hφeq : φ x = φ y := by
      simpa [scale] using mul_left_cancel₀ (by exact_mod_cast hN.ne') hqe
    by_contra hne
    have hd : x - y ∈ D := by
      rw [Finset.mem_erase, Set.Finite.mem_toFinset]
      refine ⟨sub_ne_zero.mpr hne, ?_⟩
      exact ⟨x, hx, y, hy, rfl⟩
    have hnz : φ (x - y) ≠ 0 := hφ _ hd
    rw [map_sub, hφeq, sub_self] at hnz
    exact hnz rfl
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨z, hz⟩ := hclear (φ a)
      (Finset.mem_image.mpr ⟨a, hA.mem_toFinset.mpr ha, rfl⟩)
    refine ⟨z, ?_⟩
    have hscale : scale a = (z : ℚ) := by simpa [scale] using hz
    rw [show f a = (scale a : ℝ) from rfl, hscale]
    exact (Rat.cast_intCast z).symm

theorem OMA.solution : type_of% @Erdos757.erdos_757.variants.lowerBound := by
  intro A
  exact OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.main OMA.Leaf1.solve OMA.Leaf2.solve (A := A)
