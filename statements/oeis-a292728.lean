import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Multiset.Replicate
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Logic.Relation

/-!
# Reachable terminal states in the equal-pile transfer game

A terminal partition has distinct parts: precisely two equal piles enable a move.
A000009 counts all partitions into distinct parts.

Source: https://oeis.org/A292728
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a292728

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

/-- A000009, the number of partitions of n into distinct parts. -/
noncomputable def distinctPartitions (n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | position n s ∧ s.Nodup}

/-- A292728, the reachable terminal partitions of n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | position n s ∧ s.Nodup ∧ reachable n s}

/-- The two terminal-position conjectures, on the original positive-index domain. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n = distinctPartitions n ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (distinctPartitions n - a n = 1 ↔ Nat.Prime n ∧ Odd n) := by
  sorry

end OMA.S_oeis_a292728
