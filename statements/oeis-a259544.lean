import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Distinct subset means in OEIS A259544

Source: https://oeis.org/A259544 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

For nonempty subsets, cross-multiplication gives the equality condition for
their arithmetic means. The minimum possible upper bound on an eligible
positive set equals the minimum possible largest element. The two clauses
give the exceptional index and the growth conjecture stated in the source.
-/

namespace OMA.S_oeis_a259544

open scoped BigOperators

def hasDistinctMeans (s : Finset ℕ) : Prop :=
  ∀ u v : Finset ℕ, u ⊆ s → v ⊆ s → u.Nonempty → v.Nonempty →
    (∑ x ∈ u, x) * v.card = (∑ x ∈ v, x) * u.card → u = v

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ s : Finset ℕ, s.card = n ∧ (∀ x ∈ s, 0 < x ∧ x ≤ m) ∧ hasDistinctMeans s}

theorem main :
    (a 4 = 7 ∧ ∀ n : ℕ, 0 < n → (a n < 2 ^ (n - 1) ↔ n = 4)) ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ n) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a259544
