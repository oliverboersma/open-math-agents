import Mathlib

/-!
# A009388: If a, b in sequence, so is a*b-1

Source: https://oeis.org/A009388
Credit: @xor2k

Formalizes the OEIS A009388 conjecture (David W. Wilson; the comment of Franklin T.
Adams-Watters, Aug 31 2016, reads): All terms are congruent to 0 or 2 mod 3. It follows that
no three consecutive integers are in the sequence.

Conventions: the sequence lists, in increasing order, the smallest set of natural numbers that
contains the seed `2` (the first term in the OEIS data `2, 3, 5, 8, 9, 14, ...`) and is closed
under `(a, b) ↦ a*b - 1` (with `a = b` allowed, e.g. `3 = 2*2 - 1`). It is given as the
inductive predicate `InSeq`. All members are at least `2`, so the natural subtraction
`a*b - 1` is exact. Both claims of the comment are stated: every member is `≡ 0` or `≡ 2`
(mod 3), and no three consecutive integers `n, n+1, n+2` are all members.
-/

namespace OMA.S_oeis_a009388

/-- Membership in A009388: generated from `2` by `(a, b) ↦ a*b - 1`. -/
inductive InSeq : ℕ → Prop
  | base : InSeq 2
  | step {a b : ℕ} : InSeq a → InSeq b → InSeq (a * b - 1)

/-- Every term is congruent to `0` or `2` mod `3`, and no three consecutive integers
are all terms. -/
theorem main :
    (∀ x : ℕ, InSeq x → x % 3 = 0 ∨ x % 3 = 2) ∧
      (∀ n : ℕ, ¬ (InSeq n ∧ InSeq (n + 1) ∧ InSeq (n + 2))) := by
  sorry

end OMA.S_oeis_a009388
