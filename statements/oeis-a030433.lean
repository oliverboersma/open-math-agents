import Mathlib

/-!
The conjecture of Federico Provvedi recorded in OEIS A030433 characterizes
the primes of the form 10k+9 by a polynomial factorization. The geometric
sum below is the exact polynomial quotient of (X+1)^5-1 by X.
Source: https://oeis.org/A030433
Formalization: @anmolspace with OpenAI Codex.
-/

namespace OMA.S_oeis_a030433
open Polynomial

noncomputable def shiftedQuotient (p : ℕ) : (ZMod p)[X] :=
  ∑ j ∈ Finset.range 5, (X + 1)^j

/-- Normalized factors are monic over the field. Taking the underlying
finset counts each distinct irreducible quadratic once. -/
noncomputable def quadraticFactors (p : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors (shiftedQuotient p)).toFinset.filter
    (fun f => f.natDegree = 2)

theorem main : ∀ (p : ℕ) [Fact p.Prime], p % 10 = 9 ↔ (quadraticFactors p).card = 2 := by
  sorry

end OMA.S_oeis_a030433
