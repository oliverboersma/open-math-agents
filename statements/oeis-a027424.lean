import Mathlib

/-!
# OEIS A027424: Granvik's sign-sum formula for the number of distinct products i*j

Source: https://oeis.org/A027424 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027424 (N. J. A. Sloane), offset 1: Number of distinct products i*j with 1 <= i, j <= n
(number of distinct terms in n X n multiplication table). Formula section, from Mats Granvik,
Nov 26 2019:
n^2 = Sum_{m=1..n^2} Sum_{k=1..n^2} [k|m]*[m <= n*k]*[k <= n]
a(n) = Sum_{m=1..n^2} sign( Sum_{k=1..n^2} [k|m]*[m <= n*k]*[k <= n] ), conjecture.

Formalization notes:
* The word conjecture is attached to the second formula only, and that formula is the statement
  below; the first line is a counting identity that the entry does not mark as conjectural.
* [P] is 1 if P holds and 0 otherwise; the inner sum is taken in the integers and sign is
  `Int.sign`. The statement is for every n >= 1 (offset 1).
* Controls from the entry: the definition gives 1, 3, 6, 9, 14, 18, 25, 30, 36, 42, 53, 59 for
  n = 1..12.
-/

namespace OMA.S_oeis_a027424

open Finset

/-- The values of the n X n multiplication table. -/
def prods (n : ℕ) : Finset ℕ := (Icc 1 n ×ˢ Icc 1 n).image fun p => p.1 * p.2

/-- A027424(n): the number of distinct products i*j with 1 <= i, j <= n. -/
def a (n : ℕ) : ℕ := (prods n).card

/-- Granvik's inner sum Sum_{k=1..n^2} [k|m]*[m <= n*k]*[k <= n]. -/
def inner (n m : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 (n ^ 2),
    (if k ∣ m then 1 else 0) * (if m ≤ n * k then 1 else 0) * (if k ≤ n then 1 else 0)

/-- Granvik's conjecture: a(n) = Sum_{m=1..n^2} sign(inner sum) for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ∑ m ∈ Icc 1 (n ^ 2), Int.sign (inner n m) := by
  sorry

end OMA.S_oeis_a027424
