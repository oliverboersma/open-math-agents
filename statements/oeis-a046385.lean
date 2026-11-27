import Mathlib.Data.Finset.Insert
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Bounds.Defs

/-!
# Palindromic prime factors in OEIS A046385

Source: https://oeis.org/A046385 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The sequence records the least positive decimal palindrome for each number
of prime factors counted with multiplicity, with all of its prime factors
palindromic. Hugo Pfoertner conjectures that the sequence has exactly the
terms recorded in the entry, including the later terms indexed by 15, 16,
and 20.
-/

namespace OMA.S_oeis_a046385

def palindromesWithFactorCount (n : ℕ) : Set ℕ :=
  {k | 0 < k ∧ (Nat.digits 10 k).Palindrome ∧ k.primeFactorsList.length = n ∧
    ∀ p ∈ k.primeFactorsList, (Nat.digits 10 p).Palindrome}

def knownTerms : Finset (ℕ × ℕ) :=
  {(0, 1), (1, 2), (2, 4), (3, 8), (4, 88), (5, 252), (6, 2772), (7, 82728),
    (8, 2112), (9, 4224), (10, 8448), (11, 236989632), (12, 48384), (13, 2977792),
    (15, 405504), (16, 40955904), (20, 677707776)}

theorem main : ∀ n k : ℕ,
    IsLeast (palindromesWithFactorCount n) k ↔ (n, k) ∈ knownTerms := by
  sorry

end OMA.S_oeis_a046385
