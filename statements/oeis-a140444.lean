import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Defs

/-!
# A140444 and the factorization of a translated seventh cyclotomic polynomial

Federico Provvedi's comment of 24 May 2018 gives examples of six distinct
linear factors over the prime fields of orders 29, 43, 71 and 113.
The irreducibility assertion is over the rationals. The examples and
the modular equivalence concern the reduction over the prime field.

The geometric sum is precisely ((X+1)^7-1)/X in both coefficient fields.
It is monic of degree six. Its distinct roots over a field correspond
bijectively to its distinct monic irreducible linear factors.

Source: https://oeis.org/A140444
Formalization: @anmolspace, with OpenAI Codex.
-/
namespace OMA.S_oeis_a140444

noncomputable def shiftedQuotient (R : Type*) [CommRing R] : Polynomial R :=
  ∑ j ∈ Finset.range 7, (Polynomial.X + 1) ^ j

theorem main : Irreducible (shiftedQuotient ℚ) ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 14 = 1 ↔
      (Finset.univ.filter (fun a : ZMod p => (shiftedQuotient (ZMod p)).eval a = 0)).card = 6 := by
  sorry

end OMA.S_oeis_a140444
