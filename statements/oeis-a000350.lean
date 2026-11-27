import Mathlib

/-!
# Binary terminal coincidences between Fibonacci numbers and their indices

Source: https://oeis.org/A000350
Credit: @Heart-galaxy

OEIS A000350 comments that, apart from 1 and 5, no positive m has the property
that Fibonacci(m), written in binary, ends with m written in binary. `Nat.digits`
uses the canonical base-2 expansion; reversing its least-significant-first list
makes the usual most-significant-first binary notation. The positive range avoids
the separate zero convention (Nat.digits 2 0 = []).
-/

namespace OMA.S_oeis_a000350

/-- The canonical binary representation of `m` is a suffix of that of `n`. -/
def BinaryEndsWith (n m : ℕ) : Prop :=
  ∃ front : List ℕ, (Nat.digits 2 n).reverse = front ++ (Nat.digits 2 m).reverse

theorem main : ∀ m : ℕ, 0 < m →
    (BinaryEndsWith (Nat.fib m) m ↔ m = 1 ∨ m = 5) := by
  sorry

end OMA.S_oeis_a000350
