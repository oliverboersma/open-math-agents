import Mathlib

/-!
# OEIS A002293: Three copies of each letter, avoiding 231 and 221

Source: https://oeis.org/A002293
Credit: @gblacher2

This enumeration is the three-copy case of Defant and Kravitz, Stack-sorting
for Words, Theorem 3.6 (https://arxiv.org/abs/1809.09158).
-/

namespace OMA.S_oeis_a002293

/-- Each letter appears three times, and no three increasing positions form
231 or 221. For either pattern the last letter is smaller than the first,
and the middle letter is at least the first. -/
def IsUniformAvoidingWord {n : ℕ} (word : Fin (3 * n) → Fin n) : Prop :=
  (∀ letter : Fin n, (Finset.univ.filter fun i => word i = letter).card = 3) ∧
    ∀ i j k, i < j → j < k → ¬ (word k < word i ∧ word i ≤ word j)

theorem main : ∀ n : ℕ,
    Nat.card {word : Fin (3 * n) → Fin n // IsUniformAvoidingWord word} =
      Nat.choose (4 * n) n / (3 * n + 1) := by
  sorry

end OMA.S_oeis_a002293
