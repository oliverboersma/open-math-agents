import FormalConjectures.ErdosProblems.«423»

open Filter Asymptotics

namespace OMA.R_Erdos423_erdos_423_variants_upper_bound_R1

-- Count the distinct sums of blocks of length at least two in the first m terms.
-- With m terms, removing the singleton sums discards at most m values.
-- The underlying convex difference-set bound is Cushman, Theorem 1.5.
def H1 : Prop :=
  ∀ a : ℕ → ℕ, StrictMono (fun k : ℕ => a (k + 1)) →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ ((1101 : ℝ) / 688 - η) ≤
        C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ)

-- Tang's transfer step relates the count of distinct sums to growth of the greedy sequence.
def H2 : Prop :=
  ∀ a : ℕ → ℕ, Erdos423.IsHofstadterSeq a → ∀ c : ℝ, 1 < c →
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ (c - η) ≤
        C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ)) →
    ∀ ε : ℝ, 0 < ε → (fun n : ℕ => (a n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (c - 1) + ε))

theorem main : H1 → H2 → type_of% @Erdos423.erdos_423.variants.upper_bound := by
  intro hcount htransfer a ha ε hε
  have hexponent : (1 : ℝ) / ((1101 : ℝ) / 688 - 1) = 688 / 413 := by norm_num
  simpa only [hexponent] using
    htransfer a ha ((1101 : ℝ) / 688) (by norm_num)
      (hcount a (Erdos423.IsHofstadterSeq.strictMono ha)) ε hε

end OMA.R_Erdos423_erdos_423_variants_upper_bound_R1
