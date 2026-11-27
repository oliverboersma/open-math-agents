import Mathlib

/-!
# A239293: Smallest composite c > n such that n^c == n (mod c)

Source: https://oeis.org/A239293
Credit: @xor2k

Formalizes the OEIS A239293 conjecture (offset 1): a(n) = n+1 if and only if n+1 is an odd
composite number.

Conventions: `n` ranges over `n ≥ 1` (the OEIS offset). A number `c` is composite when
`1 < c` and `c` is not prime. `a n` is the infimum (`sInf`) of the set of composite `c > n`
with `n ^ c ≡ n [MOD c]`; when this set is nonempty this is its least element, as in OEIS.
(If the set were empty, `sInf` would give `0`; this never equals `n + 1`, and in that case
`n + 1` is not in the set, so the equivalence is unaffected by this convention.)
-/

namespace OMA.S_oeis_a239293

/-- A natural number is composite if it is greater than `1` and not prime. -/
def IsComposite (c : ℕ) : Prop :=
  1 < c ∧ ¬ c.Prime

/-- `a(n)` = smallest composite `c > n` such that `n^c ≡ n (mod c)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {c : ℕ | n < c ∧ IsComposite c ∧ n ^ c ≡ n [MOD c]}

/-- For `n ≥ 1`: `a(n) = n + 1` if and only if `n + 1` is an odd composite number. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n = n + 1 ↔ (Odd (n + 1) ∧ IsComposite (n + 1))) := by
  sorry

end OMA.S_oeis_a239293
