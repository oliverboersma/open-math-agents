import Mathlib

/-!
# A102239: a(n) = (Sum_{i=0..n} 5^i) + 1 - (Sum_{i=0..n} 5^i) mod 2

Source: https://oeis.org/A102239
Credit: @xor2k

Formalizes the OEIS A102239 conjecture (offset 0): a(n) = 4*a(n-1) + 5*a(n-2) - 2.

Conventions: the sequence is indexed by `n : ℕ` starting at `0` (offset 0), so the
recurrence is meaningful for every `n ≥ 2`; it is stated as `a(n+2) = 4*a(n+1) + 5*a(n) - 2`
for all `n : ℕ`. The sequence itself is computed in `ℕ`: the inner sum is
`∑ i ∈ Finset.range (n + 1), 5 ^ i`, and since `s % 2 ≤ 1` the natural subtraction
`s + 1 - s % 2` is exact. The recurrence is stated after casting to `ℤ`, so the `- 2`
is ordinary integer subtraction.
-/

namespace OMA.S_oeis_a102239

/-- `s(n) = Sum_{i=0..n} 5^i`. -/
def s (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), 5 ^ i

/-- `a(n) = s(n) + 1 - (s(n) mod 2)`. -/
def a (n : ℕ) : ℕ :=
  s n + 1 - s n % 2

/-- For every `n ≥ 2`, `a(n) = 4*a(n-1) + 5*a(n-2) - 2` (written with `n + 2` in place of `n`). -/
theorem main :
    ∀ n : ℕ, (a (n + 2) : ℤ) = 4 * (a (n + 1) : ℤ) + 5 * (a n : ℤ) - 2 := by
  sorry

end OMA.S_oeis_a102239
