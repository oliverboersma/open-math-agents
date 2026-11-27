import Mathlib

/-!
# A048200: minimal pair-exchange / set-rotate sequences reversing n elements

Source: https://oeis.org/A048200
Credit: @sntntHb

`a(n)` is the minimal length of a sequence of operations reversing `n` distinct ordered elements,
where the two allowed operations are a left-rotate (the leftmost element moves to the right end)
and a pair-exchange of the two leftmost elements. The entry records the conjecture
(Sai Satwik Kuppili and Bhadrachalam Chitturi, Jun 09 2020):
`a(n) = 3n^2/4 - 2n` if `n` is even and `a(n) = (3n^2 - 10n + 15)/4` if `n` is odd.

The data `0, 1, 2, 4, 10, 15, 23, 32, 42, 55, 67, 84, 98, 119` starts at `n = 1`. The formula
agrees with every listed term from `n = 4` on (for `n = 3` it gives 3 while `a(3) = 2`), so the
conjecture is stated for `n ≥ 4`. Divisions are cleared: for even `n`, `4 a(n) + 8 n = 3 n^2`; for
odd `n`, `4 a(n) + 10 n = 3 n^2 + 15`.

The `n` elements are `0, 1, ..., n - 1` in a list, operation `true` is the left-rotate
`List.rotate 1` and operation `false` exchanges the first two entries. A word of operations is
applied from left to right, and `a n` is the least length of a word sending `List.range n` to its
reverse (rotations and adjacent exchanges generate all permutations, so such words exist).
-/

namespace OMA.S_oeis_a048200

/-- Exchange the two leftmost elements. -/
def exch : List ℕ → List ℕ
  | x :: y :: t => y :: x :: t
  | l => l

/-- One operation: `true` is a left-rotate, `false` is a pair-exchange. -/
def step (l : List ℕ) (b : Bool) : List ℕ := if b then l.rotate 1 else exch l

/-- Apply a word of operations from left to right. -/
def run (w : List Bool) (l : List ℕ) : List ℕ := w.foldl step l

/-- OEIS A048200: the minimal length of a word reversing `n` ordered elements. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ w : List Bool, w.length = k ∧ run w (List.range n) = (List.range n).reverse}

/-- The Kuppili-Chitturi conjecture for A048200, for `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (Even n → 4 * a n + 8 * n = 3 * n ^ 2) ∧ (Odd n → 4 * a n + 10 * n = 3 * n ^ 2 + 15) := by
  sorry

end OMA.S_oeis_a048200
