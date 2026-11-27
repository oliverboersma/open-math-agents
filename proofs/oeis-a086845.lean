import OMAStatements.S_oeis_a086845

-- Problem: A086845: a(1) = 0, a(n) = a(floor(n/2)) + 2*a(ceiling(n/2)) + floor(n/2).
-- Upstream: formal-conjectures statements/oeis-a086845.lean:0 (declaration OMA.S_oeis_a086845.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a086845

open OMA.S_oeis_a086845

lemma b_even (m : ℕ) : A087808 (2 * m) = 2 * A087808 m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp [A087808]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, A087808, if_pos (by omega)]
    congr 2
    omega

lemma b_odd (m : ℕ) : A087808 (2 * m + 1) = A087808 m + 1 := by
  rw [A087808, if_neg (by omega)]
  congr 2
  omega

/-- S n is the partial sum; it satisfies the same recursion as a. -/
lemma S_split (n : ℕ) : ∑ k ∈ Finset.range n, A087808 k =
    2 * ∑ k ∈ Finset.range ((n + 1) / 2), A087808 k +
      ∑ k ∈ Finset.range (n / 2), A087808 k + n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [A087808]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h := ih m (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, h,
      show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega, show (m + 2) / 2 = m / 2 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · subst ht
      rw [show (t + t + 1) / 2 = t by omega, show (t + t) / 2 = t by omega,
        show t + t = 2 * t by ring, b_even, b_odd]
      ring
    · subst ht
      rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega, show (2 * t + 1) / 2 = t by omega,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring, b_even, b_odd]
      ring

lemma solve : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.range n, A087808 k := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    simp [a, A087808]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a, ih ((m + 2) / 2) (by omega) (by omega), ih ((m + 3) / 2) (by omega) (by omega),
      S_split (m + 2)]
    rw [show (m + 2 + 1) / 2 = (m + 3) / 2 by omega]
    ring

end OMA.P_oeis_a086845

theorem OMA.solution : type_of% @OMA.S_oeis_a086845.main := OMA.P_oeis_a086845.solve
