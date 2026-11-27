import Mathlib

/-!
# A050446. Adjacent letter sums and magic labelings of a path

This is John Tyler Rascoe's conjecture of June 6, 2025. The entry's zero-based
table is defined here by its magic-labeling interpretation. The graph has
`n + 1` vertices, `n` path edges, and one loop at each vertex. Each loop
contributes once to the sum at its vertex. In the word count, `[m]` denotes
the letters `1, ..., m`, encoded with one added to each zero-based label.

Source: https://oeis.org/A050446
Credit: @dwilfand-sys
-/

namespace OMA.S_oeis_a050446

/-- Enumerate the length-`n` lists with entries from `0` to `size - 1`. -/
def labelings : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, size => (List.range size).flatMap fun x =>
      (labelings n size).map fun xs => x :: xs

def tableValue (n m : ℕ) : ℕ :=
  ((labelings n (m + 1)).flatMap fun edges =>
    (labelings (n + 1) (m + 1)).filter fun loops =>
      (List.range (n + 1)).all fun v =>
        let left := if v = 0 then 0 else edges[v - 1]?.getD 0
        decide (loops[v]?.getD 0 + left + edges[v]?.getD 0 = m)).length

def wordCount (n m : ℕ) : ℕ :=
  ((labelings n m).filter fun w =>
    (w.zip (w.drop 1)).all fun pair => decide (pair.1 + pair.2 + 2 ≤ m + 1)).length

theorem main : ∀ n m : ℕ, tableValue n m = wordCount n m := by
  sorry

end OMA.S_oeis_a050446
