import OMAReductions.R_Erdos372_erdos_372_R1
import Mathlib

-- Step Erdos372.erdos_372.R1.H2: hypothesis H2 of reduction Erdos372.erdos_372.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos372StepH2

/-- For every `k` there is a set of `k` positive integers in which every difference divides the
smaller element. Induction: from `A`, take `M = ∏ a ∈ A, a` and pass to `{M} ∪ (A + M)`. -/
theorem exists_set (k : ℕ) : ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ a ∈ A, ∀ b ∈ A, a < b → b - a ∣ a := by
  induction k with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨A, hc, hpos, hdiv⟩ := ih
    obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ∏ a ∈ A, a := ⟨_, rfl⟩
    have hMpos : 0 < M := by
      rw [hMdef]
      exact Finset.prod_pos hpos
    have hdvdM : ∀ a ∈ A, a ∣ M := by
      intro a ha
      rw [hMdef]
      exact Finset.dvd_prod_of_mem _ ha
    refine ⟨insert M (A.image (· + M)), ?_, ?_, ?_⟩
    · have hnot : M ∉ A.image (· + M) := by
        intro h
        obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
        have := hpos x hx
        omega
      rw [Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (add_left_injective M), hc]
    · intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · omega
      · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
        omega
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxM | hx'
      · rcases Finset.mem_insert.mp hy with hyM | hy'
        · omega
        · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hy'
          have e : y - x = b := by omega
          rw [e, hxM]
          exact hdvdM b hb
      · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hx'
        have hapos := hpos a ha
        rcases Finset.mem_insert.mp hy with hyM | hy'
        · omega
        · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hy'
          have hab : a < b := by omega
          have e : y - x = b - a := by omega
          have h1 := hdiv a ha b hb hab
          rw [e, ← hae]
          exact dvd_add h1 (h1.trans (hdvdM a ha))

end Erdos372StepH2

theorem OMA.solution : OMA.R_Erdos372_erdos_372_R1.H2 := Erdos372StepH2.exists_set
