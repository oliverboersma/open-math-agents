import Mathlib

/-!
# Rotational symmetries of binary expansions (OEIS A138904)

Source: https://oeis.org/A138904 (OEIS Foundation, CC BY-SA 4.0).

A138904(m) is the number of rotational symmetries of the binary expansion of m: the number of
cyclic shifts r, with 0 <= r < L where L is the length of the expansion, that map the expansion
to itself (r = 0 always counts).

First conjecture (in the entry): for binary expansions of length n, the values that occur as
numbers of symmetries are exactly the divisors of n. The entry's second conjecture, describing
the numbers with a given number of symmetries when the proper divisors of n are pairwise
coprime, is not stated here.
-/

namespace OMA.S_oeis_a138904

/-- A138904(m): the number of cyclic shifts fixing the binary expansion of `m`. -/
def a (m : ℕ) : ℕ :=
  ((Finset.range (Nat.digits 2 m).length).filter
    (fun r => (Nat.digits 2 m).rotate r = Nat.digits 2 m)).card

/-- The first conjecture on A138904: over the numbers whose binary expansion has length `n`,
the attained numbers of symmetries are exactly the divisors of `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    {s : ℕ | ∃ m : ℕ, (Nat.digits 2 m).length = n ∧ a m = s} = {d : ℕ | d ∣ n} := by
  sorry

end OMA.S_oeis_a138904
