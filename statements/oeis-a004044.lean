import Mathlib

/-!
# A004044: The classic football pool problem: size of minimal covering code in {0,1,2}^n with
covering radius 1.

Source: https://oeis.org/A004044
Credit: @mbilenko03

Conjecture (Thomas Ordowski, Jul 10 2021): `a((3^m+1)/2) = 3^((3^m+1)/2 - m)` for `m > 0`.
(The entry adds the equivalent form `a((3^m-1)/2 + 1) = 3 * a((3^m-1)/2)`, using the known values
`a((3^m-1)/2) = 3^((3^m-1)/2 - m)` given by the ternary Hamming codes; the first form is stated.)

Conventions:
- Words of length `n` over `{0, 1, 2}` are functions `Fin n → Fin 3`, with the Hamming distance
  `hammingDist` (the number of coordinates where two words differ).
- A covering code with radius 1 is a set `C` of words such that every word is at Hamming distance
  at most 1 from some word of `C`. `a(n)` is the least size of such a code, written as an
  infimum over the attained sizes (the set is nonempty: all `3^n` words form a code).
- `(3^m + 1)/2` is exact natural-number division (`3^m` is odd).
-/

namespace OMA.S_oeis_a004044

/-- `C` is a ternary covering code of length `n` with covering radius 1. -/
def IsCoveringCode (n : ℕ) (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x : Fin n → Fin 3, ∃ c ∈ C, hammingDist x c ≤ 1

/-- The minimal size of a ternary covering code of length `n` with radius 1 (OEIS A004044). -/
noncomputable def footballPool (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Fin n → Fin 3), C.card = k ∧ IsCoveringCode n C}

theorem main : ∀ m : ℕ, 0 < m → footballPool ((3 ^ m + 1) / 2) = 3 ^ ((3 ^ m + 1) / 2 - m) := by
  sorry

end OMA.S_oeis_a004044
