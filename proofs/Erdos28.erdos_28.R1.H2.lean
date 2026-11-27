import OMAReductions.R_Erdos28_erdos_28_R1

-- Step Erdos28.erdos_28.R1.H2: hypothesis H2 of reduction Erdos28.erdos_28.R1
-- Credit: @anmolspace
-- Proof: a pair (p1, p2) with p1 + p2 = n and both coordinates in insert a A either has both
-- coordinates in A, or is (a, n - a), or is (n - a, a); so the count grows by at most 2.

namespace OMA.SE28
open Finset

lemma key (A : Set ℕ) (a n : ℕ)
    {i1 : DecidablePred (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)}
    {i2 : DecidablePred (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)} :
    ((antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)).card
      ≤ ((antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)).card + 2 := by
  classical
  have hsub : (antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)
      ⊆ (antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)
        ∪ {(a, n - a), (n - a, a)} := by
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_insert_iff,
      Set.mem_insert_iff] at hp
    obtain ⟨hsum, h1, h2⟩ := hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases ha1 : p.1 = a
    · right; left
      exact Prod.ext ha1 (by simp only; omega)
    · by_cases ha2 : p.2 = a
      · right; right
        exact Prod.ext (by simp only; omega) ha2
      · left
        exact ⟨hsum, h1.resolve_left ha1, h2.resolve_left ha2⟩
  have h2 : ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left h2 _

end OMA.SE28

theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1.H2 := by
  intro A a n
  rw [AdditiveCombinatorics.sumRep_def, AdditiveCombinatorics.sumRep_def]
  exact OMA.SE28.key A a n
