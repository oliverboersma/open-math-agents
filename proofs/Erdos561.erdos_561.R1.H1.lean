import OMAReductions.R_Erdos561_erdos_561_R1
import Mathlib

/-! Hall deficiencies in two lists cannot coexist under the prefix sum condition. -/
open Finset

namespace TwoDemandLists

private theorem deficiency {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (n : α → ℕ) (r : β → ℕ) (h : ¬ ∃ f : α ↪ β, ∀ i, n i ≤ r (f i)) :
    ∃ a : ℕ, (univ.filter (fun i => a ≤ n i)).Nonempty ∧
      (univ.filter (fun k => a ≤ r k)).card < (univ.filter (fun i => a ≤ n i)).card := by
  classical
  let T (i : α) := univ.filter (fun k => n i ≤ r k)
  have hf : ¬ ∀ S : Finset α, S.card ≤ (S.biUnion T).card := by
    intro hHall
    obtain ⟨f, hf, hmem⟩ := (all_card_le_biUnion_card_iff_exists_injective T).mp hHall
    exact h ⟨⟨f, hf⟩, fun i => (mem_filter.mp (hmem i)).2⟩
  push Not at hf
  obtain ⟨S, hdef⟩ := hf
  have hne : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image n hne
  have hL : S ⊆ univ.filter (fun j => n i ≤ n j) := fun j hj =>
    mem_filter.mpr ⟨mem_univ _, hmin j hj⟩
  have hR : T i ⊆ S.biUnion T := fun k hk => mem_biUnion.mpr ⟨i, hi, hk⟩
  exact ⟨n i, ⟨i, mem_filter.mpr ⟨mem_univ _, le_rfl⟩⟩,
    (card_le_card hR).trans_lt (hdef.trans_le (card_le_card hL))⟩

private theorem high_index {s : ℕ} (n : Fin s → ℕ) (a : ℕ)
    (h : (univ.filter (fun i => a ≤ n i)).Nonempty) :
    ∃ i : Fin s, a ≤ n i ∧ (univ.filter (fun j => a ≤ n j)).card ≤ i.val + 1 := by
  let S := univ.filter (fun i => a ≤ n i)
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image Fin.val h
  have hsub : S ⊆ Iic i := fun j hj => mem_Iic.mpr (hmax j hj)
  exact ⟨i, (mem_filter.mp hi).2, by simpa only [Fin.card_Iic] using card_le_card hsub⟩

theorem one_matching (s t : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (r b : Fin (s + t - 1) → ℕ)
    (h : ∀ i j (k : Fin (s + t - 1)), k.val ≤ i.val + j.val →
      n i + m j - 1 ≤ r k + b k) :
    (∃ f : Fin s ↪ Fin (s + t - 1), ∀ i, n i ≤ r (f i)) ∨
      (∃ f : Fin t ↪ Fin (s + t - 1), ∀ j, m j ≤ b (f j)) := by
  classical
  by_contra hn
  obtain ⟨hR, hB⟩ := not_or.mp hn
  obtain ⟨a, ha, har⟩ := deficiency n r hR
  obtain ⟨c, hc, hcb⟩ := deficiency m b hB
  obtain ⟨i, hi, hiCount⟩ := high_index n a ha
  obtain ⟨j, hj, hjCount⟩ := high_index m c hc
  let K : Fin (s + t - 1) := ⟨i.val + j.val, by
    have := i.isLt
    have := j.isLt
    omega⟩
  let R := univ.filter (fun k => a ≤ r k)
  let B := univ.filter (fun k => c ≤ b k)
  have hcover : Iic K ⊆ R ∪ B := by
    intro k hk
    have hsmall : k.val ≤ i.val + j.val := show k ≤ K from mem_Iic.mp hk
    have hsum := h i j k hsmall
    simp only [mem_union, R, B, mem_filter, mem_univ, true_and]
    omega
  have hCount : K.val + 1 ≤ R.card + B.card := by
    rw [← Fin.card_Iic]
    exact (card_le_card hcover).trans (card_union_le _ _)
  change R.card < (univ.filter (fun i => a ≤ n i)).card at har
  change B.card < (univ.filter (fun j => c ≤ m j)).card at hcb
  change i.val + j.val + 1 ≤ R.card + B.card at hCount
  omega

end TwoDemandLists

theorem OMA.solution : OMA.R_Erdos561_erdos_561_R1.H1 := TwoDemandLists.one_matching