import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Multiset.Replicate
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Logic.Relation

/-!
# Unreachable stone-pile positions

The source counts all positive integer partitions inaccessible under equal-pile transfers.
It asks for the zero and one level sets and the values at four and eight times an odd prime.
Charlie Neder gave several earlier evaluations in 2019.

Source: https://oeis.org/A292727
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a292727

/-- A legal forward transfer chooses two equal piles of positive size x and
moves y stones from one to the other. An emptied pile is removed. -/
def move (s t : Multiset ℕ) : Prop :=
  ∃ (x y : ℕ) (rest : Multiset ℕ), 0 < y ∧ y ≤ x ∧ s = x ::ₘ x ::ₘ rest ∧
    t = if y = x then (x + y) ::ₘ rest else (x - y) ::ₘ (x + y) ::ₘ rest

/-- The given total starts as n singleton piles. -/
def reachable (n : ℕ) (s : Multiset ℕ) : Prop :=
  Relation.ReflTransGen move (Multiset.replicate n 1) s

/-- Piles are unordered and empty piles are discarded. -/
def position (n : ℕ) (s : Multiset ℕ) : Prop :=
  s.sum = n ∧ ∀ x ∈ s, 0 < x

/-- A292727, the number of unreachable partitions of n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | position n s ∧ ¬ reachable n s}

/-- The four conjectured assertions in the entry, including the two odd-prime formulas. -/
theorem main :
    (∀ n : ℕ, 0 < n →
      (a n = 0 ↔ ∃ k : ℕ, n = 2 ^ k) ∧
      (a n = 1 ↔ Nat.Prime n ∧ Odd n)) ∧
    (∀ p : ℕ, Nat.Prime p → Odd p → a (4 * p) = p + 4 ∧ a (8 * p) = 2 * p + 20) := by
  sorry

end OMA.S_oeis_a292727
