import Mathlib

/-!
# Layman's set-cardinality conjecture for OEIS A000126

Source: https://oeis.org/A000126
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A000/A000126.seq

The OEIS entry has offset 1 and gives a(n) = Fibonacci(n + 3) - (n + 1).
John W. Layman's 2007 conjecture identifies a(n) with the cardinality of S(n),
where S(1) = {1} and S(n) is the smallest set containing x + 1 and 2*x + 1
for every x in S(n - 1). The union of the two images below is exactly that
smallest set. The value at index 0 is an unused convention.

Status: OEIS reports the conjecture proved by Sela Fried on February 18, 2026;
see https://oeis.org/A000126/a000126.pdf . This file formalizes the statement
and does not supply a Lean proof of the published result.

Formalization credit: @Heart-galaxy.
-/

namespace OMA.S_oeis_a000126

/-- Layman's sets, with an unused empty set at index zero. -/
def laymanSet : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {1}
  | n + 2 =>
      (laymanSet (n + 1)).image (fun x => x + 1) ∪
        (laymanSet (n + 1)).image (fun x => 2 * x + 1)

/-- OEIS A000126 at its stated indices n ≥ 1. -/
def a (n : ℕ) : ℕ := Nat.fib (n + 3) - (n + 1)

/-- Layman's conjecture, reported proved in the OEIS source in 2026. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (laymanSet n).card = a n := by
  sorry

end OMA.S_oeis_a000126
