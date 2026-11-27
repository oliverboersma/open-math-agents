import FormalConjectures.Wikipedia.Andrica
import Mathlib

/-! Andrica's inequality for large n from Oppermann's conjecture for large x. Both are
consequences of Ferreira, Real exponential sums over primes and prime gaps (arXiv 2307.08725),
and the second is the catalogue's Oppermann.oppermann_conjecture.ferreira_large_x. The
passage from Oppermann to Andrica is elementary: consecutive squares and pronic numbers
x^2, x (x + 1), (x + 1)^2 cut the integers into intervals each containing a prime, so a prime
p with x^2 ≤ p < (x + 1)^2 is followed by a prime below (x + 1)^2 or below (x + 1) (x + 2),
and in both cases the square roots differ by less than 1. -/

namespace OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1

/-- Oppermann's conjecture for all sufficiently large x (Ferreira). -/
def H1 : Prop := ∀ᶠ x : ℕ in Filter.atTop,
  (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
  (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)

/-- Oppermann's conjecture from X on implies Andrica's inequality for every prime that is
at least X^2. -/
def H2 : Prop := ∀ X : ℕ,
  (∀ x ≥ X, (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)) →
  ∀ n : ℕ, X ^ 2 ≤ n.nth Nat.Prime →
    Real.sqrt ((n + 1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1

theorem main : H1 → H2 → type_of% @Andrica.andrica_conjecture.ferreira_large_n := by
  intro h1 h2
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h1
  refine Filter.eventually_atTop.2 ⟨X ^ 2, fun n hn => ?_⟩
  exact h2 X hX n (le_trans hn
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_apply)

end OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1
