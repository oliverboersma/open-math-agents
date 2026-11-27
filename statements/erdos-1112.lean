import Mathlib

/-!
# Erdős problem 1112

The problem asks whether every choice of the gap bounds and number of summands
admits an integer growth threshold for the sequence to be avoided. This states
the affirmative answer to the question as formulated on the Erdős Problems site.
Index zero below is the first term of each infinite sequence.

Source: https://www.erdosproblems.com/1112
-/

namespace OMA.S_erdos_1112

/-- A sequence whose successive terms grow by at least one fixed real factor greater than one. -/
def Lacunary (b : ℕ → ℕ) : Prop :=
  ∃ q : ℝ, 1 < q ∧ ∀ i, q * (b i : ℝ) ≤ (b (i + 1) : ℝ)

/-- The set of sums of exactly `k` terms. The same sequence index may occur more than once. -/
def sumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  {s | ∃ j : Fin k → ℕ, ∑ t, a (j t) = s}

theorem main :
    ∀ d₁ d₂ k : ℕ, 1 ≤ d₁ → d₁ < d₂ → 3 ≤ k →
      ∃ r : ℤ, ∀ b : ℕ → ℕ, (∀ i, 0 < b i) → StrictMono b → Lacunary b →
        (∀ i, r * (b i : ℤ) ≤ (b (i + 1) : ℤ)) →
        ∃ a : ℕ → ℕ, (∀ i, 0 < a i) ∧ StrictMono a ∧
          (∀ i, d₁ ≤ a (i + 1) - a i ∧ a (i + 1) - a i ≤ d₂) ∧
          Disjoint (sumset k a) (Set.range b) := by
  sorry

end OMA.S_erdos_1112
