import FormalConjectures.ErdosProblems.«359»

namespace OMA359

def B (i : ℕ) : ℕ := [1, 2, 4, 5, 8, 10, 14, 15].getD i 0

lemma Ble : ∀ j < 8, B j ≤ 15 := by decide

lemma P1 : ∀ j < 7, B j < B (j + 1) := by decide

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma P2 : ∀ j < 7, ∀ a < 7, ∀ b < 7, a ≤ b → b ≤ j →
    B (j + 1) ≠ ∑ i ∈ Finset.Icc a b, B i := by decide

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma P3 : ∀ j < 7, ∀ m < 15, B j < m → m < B (j + 1) →
    ∃ a < 7, ∃ b < 7, a ≤ b ∧ b ≤ j ∧ m = ∑ i ∈ Finset.Icc a b, B i := by decide

lemma step (A : ℕ → ℕ)
    (hA : ∀ j, IsLeast
      {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (A <| j + 1))
    (j : ℕ) (hj : j < 7) (h : ∀ i ≤ j, A i = B i) : A (j + 1) = B (j + 1) := by
  have key : ∀ a b, a ≤ b → b ≤ j → ∑ i ∈ Finset.Icc a b, A i = ∑ i ∈ Finset.Icc a b, B i := by
    intro a b _ hb
    apply Finset.sum_congr rfl
    intro i hi
    exact h i (le_trans (Finset.mem_Icc.mp hi).2 hb)
  have hL : IsLeast
      {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (B (j + 1)) := by
    constructor
    · refine ⟨?_, ?_⟩
      · rw [h j le_rfl]; exact P1 j hj
      · intro a b hab
        by_cases hba : a ≤ b
        · have hbj : b ≤ j := by
            have := hab (Finset.mem_Icc.mpr ⟨hba, le_rfl⟩)
            simpa using this
          rw [key a b hba hbj]
          exact P2 j hj a (by omega) b (by omega) hba hbj
        · have : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hba
          rw [this]
          simp only [Finset.sum_empty]
          have : 0 < B (j + 1) := by
            have := P1 j hj
            omega
          omega
    · intro m ⟨hm1, hm2⟩
      by_contra hlt
      have hlt : m < B (j + 1) := lt_of_not_ge hlt
      have hB : B j < m := by rw [← h j le_rfl]; exact hm1
      obtain ⟨a, ha, b, hb, hab, hbj, hmeq⟩ :=
        P3 j hj m (by have := Ble (j + 1) (by omega); omega) hB hlt
      apply hm2 a b
      · intro x hx
        have := Finset.mem_Icc.mp hx
        simp only [Finset.mem_Iic]; omega
      · rw [key a b hab hbj]; exact hmeq
  exact (hA j).unique hL |>.symm ▸ rfl

end OMA359

theorem OMA.solution : type_of% @Erdos359.erdos_359.variants.isGoodFor_1_low_values := by
  intro A hA
  obtain ⟨h0, _, hL⟩ := hA
  have all : ∀ j ≤ 7, A j = OMA359.B j := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj
      cases j with
      | zero => exact h0
      | succ j =>
        exact OMA359.step A hL j (by omega)
          (fun i hi => ih i (by omega) (by omega))
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i ≤ 7 := hi
    rw [all i hi']
    interval_cases i <;> simp [OMA359.B]
  · intro hx
    have hx' : x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 5 ∨ x = 8 ∨ x = 10 ∨ x = 14 ∨ x = 15 := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, by rw [all 0 (by omega)]; rfl⟩
    · exact ⟨1, by simp, by rw [all 1 (by omega)]; rfl⟩
    · exact ⟨2, by simp, by rw [all 2 (by omega)]; rfl⟩
    · exact ⟨3, by simp, by rw [all 3 (by omega)]; rfl⟩
    · exact ⟨4, by simp, by rw [all 4 (by omega)]; rfl⟩
    · exact ⟨5, by simp, by rw [all 5 (by omega)]; rfl⟩
    · exact ⟨6, by simp, by rw [all 6 (by omega)]; rfl⟩
    · exact ⟨7, by simp, by rw [all 7 (by omega)]; rfl⟩
