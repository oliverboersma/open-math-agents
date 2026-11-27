import Mathlib

/-!
# OEIS A094639: irreducibility of the Catalan-square polynomials

Source: https://oeis.org/A094639
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A094639 lists the partial sums of the squares of the Catalan numbers. Its comment records
a conjecture of Zhi-Wei Sun (Mar 23 2013): for any positive integer `n`, the polynomial
`P_n(x) = Sum_{k=0..n} (C_k)^2 x^k`, with `C_k = binomial(2k,k)/(k+1)`, is irreducible over
the field of rational numbers.

Conventions: `C_k` is Mathlib's `catalan k`, which equals `binomial(2k,k)/(k+1)` for every
`k` (Mathlib lemma `succ_mul_catalan_eq_centralBinom`). Irreducibility is `Irreducible`
in `Polynomial ℚ`. The range `n ≥ 1` is the source's; `n = 0` gives the constant `1`, a unit.
-/

namespace OMA.S_oeis_a094639

open Polynomial

/-- Sun's polynomial `P_n(x) = Sum_{k=0..n} (C_k)^2 x^k` over `ℚ`. -/
noncomputable def catalanSqPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((catalan k : ℚ) ^ 2) * X ^ k

/-- For every positive integer `n`, `P_n(x)` is irreducible over `ℚ`. -/
theorem main : ∀ n : ℕ, 0 < n → Irreducible (catalanSqPoly n) := by
  sorry

end OMA.S_oeis_a094639
