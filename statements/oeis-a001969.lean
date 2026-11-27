import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# OEIS A001969

Source: https://oeis.org/A001969 (OEIS Foundation, CC BY-SA 4.0).
Alex Ratushnyak's conjecture characterizes the nonnegative integers with
an even number of ones in binary. They are exactly the numbers obtained
by exclusive-or of the two one-position binary rotations of one integer.
Both rotations use the width of the input's binary expansion. Zero uses
one zero bit.
-/

namespace OMA.S_oeis_a001969

def width (n : ℕ) := n.log2 + 1

def ones (n : ℕ) : ℕ := ∑ i ∈ Finset.range (width n), (n.testBit i).toNat

def rotatedXor (n : ℕ) : ℕ :=
  let word := BitVec.ofNat (width n) n
  (word.rotateRight 1 ^^^ word.rotateLeft 1).toNat

theorem main : ∀ n : ℕ, Even (ones n) ↔ ∃ x : ℕ, rotatedXor x = n := by
  sorry

end OMA.S_oeis_a001969
