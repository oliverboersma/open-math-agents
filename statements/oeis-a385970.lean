import Mathlib

/-!
# OEIS A385970

In A385969 an integer is represented as a nonempty sum of powers whose
bases are distinct integers greater than one and whose exponents are a
permutation of those bases. Ordering the pairs by their bases recovers
the increasing order used in the source. A385970 lists the minimum
lengths of such representations. Alberto Zanoni conjectured that its
values are unbounded.

Sources: https://oeis.org/A385970 and https://oeis.org/A385969
-/

namespace OMA.S_oeis_a385970

def powerSum (xs : List (ℕ × ℕ)) : ℕ := (xs.map (fun p => p.1 ^ p.2)).sum

structure Represents (n : ℕ) (xs : List (ℕ × ℕ)) : Prop where
  nonempty : xs ≠ []
  distinct : (xs.map Prod.fst).Nodup
  bases : ∀ p ∈ xs, 1 < p.1
  exponents : (xs.map Prod.fst).Perm (xs.map Prod.snd)
  total : powerSum xs = n

theorem main : ∀ k : ℕ, ∃ n : ℕ, (∃ xs, Represents n xs) ∧
    ∀ xs, Represents n xs → k < xs.length := by
  sorry

end OMA.S_oeis_a385970
