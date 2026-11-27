import Mathlib

/-!
# A222945: distinct sums i+j+k with |i|, |j|, |k|, |i*j*k| <= n, versus A004766

Source: https://oeis.org/A222945
Credit: @ivillar

A222945 (offset 0): a(n) is the number of distinct sums i+j+k over integers i, j, k with
|i|, |j|, |k|, |i*j*k| <= n; data 1, 7, 9, 13, 17, 21, ...
A004766 (offset 1) lists the numbers whose binary expansion ends 01: 5, 9, 13, 17, ...
Conjecture (R. J. Mathar, May 26 2024): a(n) = A004766(n) for n >= 2.
Sela Fried (Mar 13 2026) notes that Mathar's conjecture is true.

Formalization notes.
* `sums n` is the finite set of all sums i+j+k with i, j, k in [-n, n] and |i*j*k| ≤ n, and
  a(n) is its cardinality.
* The binary expansion of m ends 01 when its two lowest binary digits are 1 (units) and
  0 (twos): `Nat.digits 2 m` lists the digits from the least significant one, so this is
  `(Nat.digits 2 m).take 2 = [1, 0]` (in particular m has at least two binary digits).
* A004766 has offset 1, so A004766(n) = `Nat.nth endsIn01 (n - 1)` (Nat.nth counts from 0).
-/

namespace OMA.S_oeis_a222945

/-- All sums i+j+k with |i|, |j|, |k| ≤ n and |i*j*k| ≤ n. -/
noncomputable def sums (n : ℕ) : Finset ℤ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      (fun t : ℤ × ℤ × ℤ => |t.1 * t.2.1 * t.2.2| ≤ (n : ℤ))).image
    (fun t => t.1 + t.2.1 + t.2.2)

/-- A222945: the number of distinct sums. -/
noncomputable def a (n : ℕ) : ℕ := (sums n).card

/-- The binary expansion of m ends 01. -/
def endsIn01 (m : ℕ) : Prop := (Nat.digits 2 m).take 2 = [1, 0]

/-- A004766 (offset 1): the n-th number whose binary expansion ends 01. -/
noncomputable def A004766 (n : ℕ) : ℕ := Nat.nth endsIn01 (n - 1)

/-- Mathar's conjecture: a(n) = A004766(n) for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = A004766 n := by
  sorry

end OMA.S_oeis_a222945
