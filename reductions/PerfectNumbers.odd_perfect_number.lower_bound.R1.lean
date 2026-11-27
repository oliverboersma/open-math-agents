import FormalConjectures.Wikipedia.PerfectNumbers

/-!
# Reduction of Nielsen's lower bounds for an odd perfect number

The target is a conjunction of two independent published bounds on an odd perfect number `n`:
Nielsen's `n > 10^1500` and his count `≥ 101` of prime factors. They come from different papers and
different arguments, so each is its own step.
-/

-- Reduction PerfectNumbers.odd_perfect_number.lower_bound.R1
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1

open Nat

/-- The size bound: an odd perfect number exceeds `10 ^ 1500`. -/
def H1 : Prop := ∀ (n : ℕ), Odd n → Perfect n → n > 10 ^ 1500

/-- The counting bound: an odd perfect number has at least `101` prime factors, counted with
multiplicity, in its prime factorisation. -/
def H2 : Prop := ∀ (n : ℕ), Odd n → Perfect n → (n.primeFactorsList).length ≥ 101

theorem main : H1 → H2 →
    type_of% @PerfectNumbers.odd_perfect_number.lower_bound := by
  intro h1 h2 n hn hp
  exact ⟨h1 n hn hp, h2 n hn hp⟩

end OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1
