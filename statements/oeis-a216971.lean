import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Set.Card

/-!
# Row divisibility in OEIS A216971

The entry in column k counts endofunctions with exactly k non-periodic
points whose immediate image is periodic. Fin n labels the n elements.
Source: https://oeis.org/A216971
Credit: @Hennyrick
-/

namespace OMA.S_oeis_a216971

theorem main : ∀ n k : ℕ, 0 < n → k < n →
    n ∣ {f : Fin n → Fin n |
      {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard = k}.ncard := by
  sorry

end OMA.S_oeis_a216971
