import OMAStatements.S_oeis_a143310

-- Problem: A143310: Triangle read by rows, A000012 * A127446, 1 <= k <= n.
-- Upstream: formal-conjectures statements/oeis-a143310.lean:0 (declaration OMA.S_oeis_a143310.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a143310

open OMA.S_oeis_a143310

lemma solve : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    T n k = ∑ i ∈ Finset.Icc 1 n, if i * k ≤ n then i * k else 0 := by
  intro n k hk hkn
  unfold T
  have h1 : ∑ j ∈ Finset.Icc 1 n, A000012 n j * A127446 j k =
      ∑ j ∈ (Finset.Icc 1 n).filter (fun j => k ∣ j), j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    unfold A000012 A127446
    rw [if_pos hj.2, one_mul]
    by_cases hd : k ∣ j
    · rw [if_pos ⟨hk, Nat.le_of_dvd (by omega) hd, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2.2), if_neg hd]
  have h2 : ∑ i ∈ Finset.Icc 1 n, (if i * k ≤ n then i * k else 0) =
      ∑ i ∈ (Finset.Icc 1 n).filter (fun i => i * k ≤ n), i * k := by
    rw [Finset.sum_filter]
  have h3 : (Finset.Icc 1 n).filter (fun j => k ∣ j) =
      ((Finset.Icc 1 n).filter (fun i => i * k ≤ n)).image (fun i => i * k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj1, hjn⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, by ring⟩
      · rcases Nat.eq_zero_or_pos m with h | h
        · subst h
          simp at hj1
        · exact h
      · nlinarith
      · rw [mul_comm]
        exact hjn
    · rintro ⟨i, ⟨⟨hi1, hin⟩, hik⟩, rfl⟩
      refine ⟨⟨?_, hik⟩, Dvd.intro_left i rfl⟩
      nlinarith
  rw [h1, h2, h3, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_right hk hxy

end OMA.P_oeis_a143310

theorem OMA.solution : type_of% @OMA.S_oeis_a143310.main := OMA.P_oeis_a143310.solve
