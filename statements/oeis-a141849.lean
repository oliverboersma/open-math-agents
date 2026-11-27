import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic

/-!
# A141849 and the distinct linear factors of a polynomial over a prime field

Federico Provvedi proposed this characterization in his comment of 17 April 2018
on OEIS A141849, the primes congruent to 1 modulo 11.

Source: https://oeis.org/A141849
Formalization: @anmolspace, with OpenAI Codex.

The geometric sum below is the polynomial quotient of (X + 1)^11 - 1 by X.
It is monic of degree 10 in every characteristic. Each distinct root a in the
prime field corresponds to the monic irreducible linear factor X - a. Counting
field elements counts distinct factors even when the polynomial has a repeated
root. This includes the exceptional characteristic 11.
-/

namespace OMA.S_oeis_a141849

/-- The exact polynomial quotient, including its value at zero. -/
noncomputable def shiftedQuotient (p : ℕ) : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range 11, (Polynomial.X + 1) ^ j

/-- A prime is 1 modulo 11 exactly when the quotient has ten distinct linear factors. -/
theorem main : ∀ (p : ℕ) [Fact p.Prime],
    p % 11 = 1 ↔
      (Finset.univ.filter (fun a : ZMod p => (shiftedQuotient p).eval a = 0)).card = 10 := by
  sorry

end OMA.S_oeis_a141849
