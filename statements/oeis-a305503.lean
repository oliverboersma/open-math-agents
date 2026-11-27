import Mathlib

/-!
# A305503: Largest cardinality of subsets A of {0,1,...,n-1} with |A + A| > |A - A|.

Source: https://oeis.org/A305503
Credit: @mbilenko03

Conjecture (from the entry): `a(n) = n - 7` for all `n > 15`.

The entry also lists conjectures of Colin Barker (Jun 01 2020): the g.f.
`x^14*(9 - 9*x + x^2) / (1 - x)^2` and `a(n) = 2*a(n-1) - a(n-2)` for `n > 17`. Given the known
values `a(1) = … = a(14) = 0` and `a(15) = 9`, both follow from (and the g.f. is equivalent to)
`a(n) = n - 7` for `n ≥ 16`, so `main` states only that.

Literature: H. V. Chu, Integers 20 (2020) #A87, proved `n - 7 ≤ a(n) ≤ n - 4` for `n ≥ 16` and
conjectured `a(n) = n - 7`; a 2026 preprint (Zenodo, doi:10.5281/zenodo.23204247) claims a proof.

Conventions:
- Subsets of `{0, 1, …, n-1}` are finite sets `A` of integers with `A ⊆ [0, n)`, and `A + A`,
  `A - A` are the pointwise sum and difference sets (computed in `ℤ`, so `A - A` contains the
  negative differences too, as in the entry's example for `n = 15`).
- `a(n)` is the supremum of the attained sizes; the sizes are bounded by `n`, so it is a maximum,
  and it is 0 when there is no such set (as for `n ≤ 14`).
-/

namespace OMA.S_oeis_a305503

open Pointwise

/-- The largest size of a subset `A` of `{0, …, n-1}` with `|A + A| > |A - A|` (OEIS A305503). -/
noncomputable def maxMSTD (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Ico 0 (n : ℤ) ∧ A.card = k ∧
    (A - A).card < (A + A).card}

theorem main : ∀ n : ℕ, 15 < n → maxMSTD n = n - 7 := by
  sorry

end OMA.S_oeis_a305503
