import Mathlib

/-!
# A000041: a(n) is the number of partitions of n (the partition numbers).

Source: https://oeis.org/A000041
Credit: @ZenimXD

The entry's comments record three conjectures. `main` states all three, as a conjunction, in the
order the source gives them.

Conjecture 1 (Gary W. Adamson, Apr 04 2013). Starting with offset 1, the sequence represents the
numbers of ordered compositions of n using the signed (++--++...) terms of A001318, starting
(1, 2, -5, -7, 12, 15, ...). The source adds that this is true by the pentagonal number theorem
(Joerg Arndt, Apr 08 2013); it is stated here because the source lists it.

Conjecture 2 (Zhi-Wei Sun, Dec 02 2013). No a(n) has the form x^m with m > 1 and x > 1.

Conjecture 3 (Zhi-Wei Sun, May 16 2023). Each integer n > 2 different from 6 can be written as a
sum of finitely many numbers of the form a(k) + 2 (k > 0) with no summand dividing another.
Verified for n <= 7140.

Reading of the source:
* `a n` is the number of partitions of n, with the entry's offset 0 (a(0) = 1).
* Conjecture 1: the signed terms are the nonzero generalized pentagonal numbers
  g = k(3k - 1)/2 (k a nonzero integer: 1, 2, 5, 7, 12, 15, ...) with sign (-1)^(|k| + 1),
  giving + + - - + + ... . A composition of n into such parts is counted with the product of the
  signs of its parts (parts that are not generalized pentagonal count 0), so the represented
  number is the signed count. Starting with offset 1 is read as the claim for every n >= 1.
* Conjecture 2: n ranges over all indices n >= 0, and x, m over the natural numbers.
* Conjecture 3: the summands are indexed by `Fin j`; no summand dividing another is required for
  every pair of distinct positions, so no value repeats. n ranges over the naturals.
-/

namespace OMA.S_oeis_a000041

/-- A000041(n): the number of partitions of `n`. -/
def a (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The signed term of A001318 at `g`: the generalized pentagonal numbers are `k(3k - 1)/2` for
nonzero integers `k`, that is `j(3j - 1)/2` (k = j) and `j(3j + 1)/2` (k = -j) for `j ≥ 1`, and
the term with index `k` carries the sign `(-1)^(|k| + 1)`. The value is that sign if `g` is
generalized pentagonal and `0` otherwise. Such a `j` satisfies `j ≤ g`, and `g` arises from at most
one `k` (`3k^2 - k` is injective on the integers), so at most one summand below is nonzero. -/
def signedPentagonal (g : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (g + 1),
    ((if j ≠ 0 ∧ 2 * g = j * (3 * j - 1) then (-1) ^ (j + 1) else 0) +
      (if j ≠ 0 ∧ 2 * g = j * (3 * j + 1) then (-1) ^ (j + 1) else 0))

theorem main :
    -- Conjecture 1: for n ≥ 1, a(n) is the signed count of compositions of n into
    -- generalized pentagonal parts.
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = ∑ c : Composition n, (c.blocks.map signedPentagonal).prod) ∧
    -- Conjecture 2: no a(n) is a perfect power x^m with m > 1 and x > 1.
    (∀ n x m : ℕ, 1 < m → 1 < x → a n ≠ x ^ m) ∧
    -- Conjecture 3: every n > 2 with n ≠ 6 is a sum of numbers a(k) + 2 (k > 0), no one of
    -- which divides another.
    (∀ n : ℕ, 2 < n → n ≠ 6 →
      ∃ (j : ℕ) (b : Fin j → ℕ),
        (∀ i, ∃ k : ℕ, 0 < k ∧ b i = a k + 2) ∧
        (∀ i i', i ≠ i' → ¬ b i ∣ b i') ∧
        ∑ i, b i = n) := by
  sorry

end OMA.S_oeis_a000041
