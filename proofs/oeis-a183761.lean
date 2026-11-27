import OMAStatements.S_oeis_a183761

-- Problem: A183761, rows-increasing nonsingular matrices are as many as positive-determinant ones.
-- Credit: @bnb9001

namespace OMA_A183761_Proof

open OMA.S_oeis_a183761

lemma det_swap (M : (ℕ × ℕ) × (ℕ × ℕ)) : det M.swap = - det M := by
  unfold det; simp; ring

lemma swap_mem {n : ℕ} {M : (ℕ × ℕ) × (ℕ × ℕ)} (h : M ∈ mats n) : M.swap ∈ mats n := by
  unfold mats at *
  simp only [Finset.mem_product] at *
  exact ⟨h.2, h.1⟩

lemma card_swap_eq (n : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ) → Prop) [DecidablePred p] :
    ((mats n).filter p).card = ((mats n).filter (fun M => p M.swap)).card := by
  refine Finset.card_bij (fun M _ => M.swap) ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_filter] at hM ⊢
    exact ⟨swap_mem hM.1, by simpa using hM.2⟩
  · intro M _ M' _ h
    exact Prod.swap_injective h
  · intro M hM
    simp only [Finset.mem_filter] at hM
    exact ⟨M.swap, by simp only [Finset.mem_filter]; exact ⟨swap_mem hM.1, hM.2⟩, by simp⟩

end OMA_A183761_Proof

open OMA_A183761_Proof OMA.S_oeis_a183761 in
theorem OMA.solution : type_of% @OMA.S_oeis_a183761.main := by
  intro n _
  set N := (mats n).filter (fun M => det M ≠ 0) with hN
  -- split by row order
  have h1 : ((mats n).filter (fun M => RowLt M.1 M.2 ∧ det M ≠ 0)).card +
      ((mats n).filter (fun M => RowLt M.2 M.1 ∧ det M ≠ 0)).card = N.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext M
      simp only [hN, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩) <;> tauto
      · rintro ⟨hm, hd⟩
        have hne : M.1 ≠ M.2 := by
          intro he
          apply hd
          unfold det
          rw [he]
          ring
        obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := M
        simp only [RowLt, ne_eq, Prod.mk.injEq] at hne ⊢
        by_cases hac : a = c
        · subst hac
          have : b ≠ d := fun h => hne ⟨rfl, h⟩
          rcases Nat.lt_or_gt_of_ne this with h | h
          · left; exact ⟨hm, Or.inr ⟨rfl, h⟩, hd⟩
          · right; exact ⟨hm, Or.inr ⟨rfl, h⟩, hd⟩
        · rcases Nat.lt_or_gt_of_ne hac with h | h
          · left; exact ⟨hm, Or.inl h, hd⟩
          · right; exact ⟨hm, Or.inl h, hd⟩
    · rw [Finset.disjoint_filter]
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _ ⟨h, _⟩ ⟨h', _⟩
      simp only [RowLt] at h h'
      omega
  have h2 : ((mats n).filter (fun M => RowLt M.1 M.2 ∧ det M ≠ 0)).card =
      ((mats n).filter (fun M => RowLt M.2 M.1 ∧ det M ≠ 0)).card := by
    rw [card_swap_eq n]
    congr 1
    ext M
    simp [det_swap]
  -- split by sign of the determinant
  have h3 : ((mats n).filter (fun M => 0 < det M)).card +
      ((mats n).filter (fun M => det M < 0)).card = N.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext M
      simp only [hN, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hm, h⟩ | ⟨hm, h⟩) <;> exact ⟨hm, by omega⟩
      · rintro ⟨hm, hd⟩
        rcases lt_or_gt_of_ne hd with h | h
        · right; exact ⟨hm, h⟩
        · left; exact ⟨hm, h⟩
    · rw [Finset.disjoint_filter]
      intro M _ h h'
      omega
  have h4 : ((mats n).filter (fun M => 0 < det M)).card =
      ((mats n).filter (fun M => det M < 0)).card := by
    rw [card_swap_eq n]
    congr 1
    ext M
    simp [det_swap]
  omega
