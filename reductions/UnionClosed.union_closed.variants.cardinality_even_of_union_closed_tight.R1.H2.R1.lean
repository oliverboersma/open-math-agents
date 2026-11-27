import OMAReductions.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1
import Mathlib

/-!
If the sets containing a half-frequency element have a least member S, every
element of S has exactly the same support as that element. Union with S then
pairs the two halves of the family. Peel off such factors, preserving both the
tightness and a proposed violation of the quarter bound on the remaining
coordinates. A family missing the empty set instead yields an odd union-closed
family with maximum frequency exactly one short of the Frankl bound.
-/

namespace OMA.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1_H2_R1

/-- Frankl's bound for odd families with an element occurring in exactly
the floor of half the members. -/
def H1 : Prop := ∀ B : Finset (Finset ℕ), ∅ ∈ B → 1 < B.card →
    (∀ X ∈ B, ∀ Y ∈ B, X ∪ Y ∈ B) →
    (∃ k : ℕ, 2 * (B.filter (fun X => k ∈ X)).card + 1 = B.card) →
    ∃ j : ℕ, B.card ≤ 2 * (B.filter (fun X => j ∈ X)).card

/-- The quarter bound only on families containing the empty set after
all factors from least members of half-frequency columns have been removed. -/
def H2 : Prop := ∀ (A : Finset (Finset ℕ)) (i : ℕ), ∅ ∈ A →
    (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) →
    (∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card) →
    2 * (A.filter (fun X => i ∈ X)).card = A.card →
    (∀ (k : ℕ), 2 * (A.filter (fun X => k ∈ X)).card = A.card →
      ∀ S ∈ A, k ∈ S → ∃ T ∈ A, k ∈ T ∧ ¬ S ⊆ T) →
    ∀ j : ℕ, 2 * ((A.filter (fun X => i ∉ X)).filter (fun X => j ∈ X)).card ≤
      (A.filter (fun X => i ∉ X)).card

/-- A least upper row yields the explicit pairing X ↦ X ∪ S. -/
theorem pair_rows (A : Finset (Finset ℕ)) (k : ℕ) (S : Finset ℕ) (hS : S ∈ A) (hk : k ∈ S)
    (hu : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A)
    (hle : ∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card)
    (heq : 2 * (A.filter (fun X => k ∈ X)).card = A.card)
    (hmin : ∀ T ∈ A, k ∈ T → S ⊆ T) :
    let B := A.filter (fun X => k ∉ X)
    (∀ X ∈ B, ∀ j ∈ S, j ∉ X) ∧
    ∀ (P : Finset ℕ → Prop) [DecidablePred P],
      (A.filter P).card = (B.filter P).card + (B.filter (fun X => P (X ∪ S))).card := by
  classical
  let B := A.filter (fun X => k ∉ X)
  let C := A.filter (fun X => k ∈ X)
  have hsizes := Finset.card_filter_add_card_filter_not (s := A) (fun X => k ∈ X)
  have hBC : B.card = C.card := by change (A.filter _).card = (A.filter _).card; omega
  have hsep (X) (hX : X ∈ B) (j) (hj : j ∈ S) : j ∉ X := by
    have hsub : C ⊆ A.filter (fun T => j ∈ T) := by
      intro T hT
      obtain ⟨hT',hkT⟩ := Finset.mem_filter.mp hT
      exact Finset.mem_filter.mpr ⟨hT',hmin T hT' hkT hj⟩
    have hcard := hle j
    have hsame := Finset.eq_of_subset_of_card_le hsub (by dsimp [C]; omega)
    intro hjX
    have hXC : X ∈ C := hsame ▸ Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hX).1,hjX⟩
    exact (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hXC).2
  have hinj : Set.InjOn (fun X : Finset ℕ => X ∪ S) (B : Set (Finset ℕ)) := by
    intro X hX Y hY h
    change X ∪ S = Y ∪ S at h
    ext j
    by_cases hj : j ∈ S
    · simp [hsep X hX j hj,hsep Y hY j hj]
    · simpa [hj] using (show j ∈ X ∪ S ↔ j ∈ Y ∪ S by rw [h])
  have hC : B.image (fun X => X ∪ S) = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro T hT
      obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_filter.mpr ⟨hu X (Finset.mem_filter.mp hX).1 S hS,Finset.mem_union_right _ hk⟩
    · rw [Finset.card_image_of_injOn hinj,hBC]
  refine ⟨hsep,?_⟩
  intro P _
  have hd : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro X hX hY
    exact (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2
  have hA : A = B ∪ C := by ext X; simp [B,C]; tauto
  calc
    (A.filter P).card = ((B.filter P) ∪ (C.filter P)).card := by conv_lhs => rw [hA,Finset.filter_union]
    _ = (B.filter P).card + (C.filter P).card :=
      Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    _ = _ := by
      rw [← hC,Finset.filter_image,Finset.card_image_of_injOn (hinj.mono (by intro X hX; exact (Finset.mem_filter.mp hX).1))]

theorem descend (h1 : H1) (h2 : H2) : ∀ N (A : Finset (Finset ℕ)), A.card = N →
    0 < N → (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) →
    (∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card) →
    ∀ i : ℕ, 2 * (A.filter (fun X => i ∈ X)).card = A.card →
    ∀ j : ℕ, 2 * ((A.filter (fun X => i ∉ X)).filter (fun X => j ∈ X)).card ≤
      (A.filter (fun X => i ∉ X)).card := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A hN hpos hu hle i hi j
    have hzero : ∅ ∈ A := by
      by_contra he
      let D := insert ∅ A
      have hd : D.card = A.card + 1 := Finset.card_insert_of_notMem he
      have hf (k : ℕ) : D.filter (fun X => k ∈ X) = A.filter (fun X => k ∈ X) := by
        ext X
        simp [D]
        aesop
      have huD : ∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D := by
        intro X hX Y hY
        rcases Finset.mem_insert.mp hX with rfl | hX'
        · simpa using hY
        rcases Finset.mem_insert.mp hY with rfl | hY'
        · simpa using hX
        exact Finset.mem_insert_of_mem (hu X hX' Y hY')
      obtain ⟨k,hk⟩ := h1 D (Finset.mem_insert_self _ _) (by omega) huD
        ⟨i,by rw [hf,hd,hi]⟩
      rw [hf,hd] at hk
      have := hle k
      omega
    by_cases hp : ∃ (k : ℕ) (S : Finset ℕ), 2 * (A.filter (fun X => k ∈ X)).card = A.card ∧
        S ∈ A ∧ k ∈ S ∧ ∀ T ∈ A, k ∈ T → S ⊆ T
    · obtain ⟨k,S,hk,hS,hkS,hmin⟩ := hp
      let B := A.filter (fun X => k ∉ X)
      obtain ⟨hsep,hcount⟩ := pair_rows A k S hS hkS hu hle hk hmin
      have hcard : A.card = 2 * B.card := by
        have := Finset.card_filter_add_card_filter_not (s := A) (fun X => k ∈ X)
        dsimp [B]
        omega
      have hc (P Q R : Finset ℕ → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
          (hq : ∀ X ∈ B, P X ↔ Q X) (hr : ∀ X ∈ B, P (X ∪ S) ↔ R X) :
          (A.filter P).card = (B.filter Q).card + (B.filter R).card := by
        have e1 := Finset.filter_congr hq
        have e2 := Finset.filter_congr hr
        exact (hcount P).trans (by rw [e1,e2])
      have hleB (a : ℕ) : 2 * (B.filter (fun X => a ∈ X)).card ≤ B.card := by
        by_cases ha : a ∈ S
        · have he : B.filter (fun X => a ∈ X) = ∅ :=
            Finset.filter_eq_empty_iff.mpr (fun X hX => hsep X hX a ha)
          simp [he]
        · have e := hc (fun X => a ∈ X) (fun X => a ∈ X) (fun X => a ∈ X)
            (fun _ _ => Iff.rfl) (fun X _ => by simp [ha])
          have := hle a
          omega
      have huB : ∀ X ∈ B, ∀ Y ∈ B, X ∪ Y ∈ B := by
        intro X hX Y hY
        obtain ⟨hXA,hkX⟩ := Finset.mem_filter.mp hX
        obtain ⟨hYA,hkY⟩ := Finset.mem_filter.mp hY
        exact Finset.mem_filter.mpr ⟨hu X hXA Y hYA,by simp [hkX,hkY]⟩
      rw [Finset.filter_filter]
      by_cases hiS : i ∈ S
      · have e1 := hc (fun X => i ∉ X) (fun _ => True) (fun _ => False)
          (fun X hX => by simp [hsep X hX i hiS]) (fun X _ => by simp [hiS])
        have e2 := hc (fun X => i ∉ X ∧ j ∈ X) (fun X => j ∈ X) (fun _ => False)
          (fun X hX => by simp [hsep X hX i hiS]) (fun X _ => by simp [hiS])
        simp only [Finset.filter_true,Finset.filter_false,Finset.card_empty,Nat.add_zero] at e1 e2
        have := hleB j
        omega
      · have ei := hc (fun X => i ∈ X) (fun X => i ∈ X) (fun X => i ∈ X)
          (fun _ _ => Iff.rfl) (fun X _ => by simp [hiS])
        have e1 := hc (fun X => i ∉ X) (fun X => i ∉ X) (fun X => i ∉ X)
          (fun _ _ => Iff.rfl) (fun X _ => by simp [hiS])
        by_cases hjS : j ∈ S
        · have e2 := hc (fun X => i ∉ X ∧ j ∈ X) (fun _ => False) (fun X => i ∉ X)
            (fun X hX => by simp [hsep X hX j hjS]) (fun X _ => by simp [hiS,hjS])
          simp only [Finset.filter_false,Finset.card_empty,Nat.zero_add] at e2
          omega
        · have e2 := hc (fun X => i ∉ X ∧ j ∈ X) (fun X => i ∉ X ∧ j ∈ X)
              (fun X => i ∉ X ∧ j ∈ X) (fun _ _ => Iff.rfl) (fun X _ => by simp [hiS,hjS])
          have small := ih B.card (by omega) B rfl (by omega) huB hleB i (by omega) j
          rw [Finset.filter_filter] at small
          omega
    · apply h2 A i hzero hu hle hi _ j
      intro k hk S hS hkS
      by_contra! hall
      exact hp ⟨k,S,hk,hS,hkS,hall⟩

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1.H2 := by
  intro h1 h2 A i _ hn hu hle hi
  exact descend h1 h2 A.card A rfl (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)) hu hle i hi

end OMA.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1_H2_R1
