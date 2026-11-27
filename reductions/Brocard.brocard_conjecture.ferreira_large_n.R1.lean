import FormalConjectures.Wikipedia.BrocardConjecture
import Mathlib

/-! Brocard's conjecture for large n from Oppermann's conjecture for large x. Both are
consequences of Ferreira, Real exponential sums over primes and prime gaps (arXiv 2307.08725),
and the second is the catalogue's Oppermann.oppermann_conjecture.ferreira_large_x. The
passage from Oppermann to Brocard is elementary: for consecutive odd primes p < q one has
q ≥ p + 2, and Oppermann at p, p + 1 and p + 2 puts four distinct primes into the intervals
(p^2, p (p + 1)), (p (p + 1), (p + 1)^2), ((p + 1)^2, (p + 1) (p + 2)) and
((p + 1) (p + 2), (p + 2)^2), all inside (p^2, q^2). -/

namespace OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R1

/-- Oppermann's conjecture for all sufficiently large x (Ferreira). -/
def H1 : Prop := ∀ᶠ x : ℕ in Filter.atTop,
  (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
  (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)

/-- Oppermann's conjecture from X on implies Brocard's conjecture for every odd prime that is
at least X. -/
def H2 : Prop := ∀ X : ℕ,
  (∀ x ≥ X, (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)) →
  ∀ n : ℕ, 1 ≤ n → X ≤ n.nth Nat.Prime →
    4 ≤ ((Finset.Ioo ((n.nth Nat.Prime) ^ 2) (((n + 1).nth Nat.Prime) ^ 2)).filter
      Nat.Prime).card

theorem main : H1 → H2 → type_of% @Brocard.brocard_conjecture.ferreira_large_n := by
  intro h1 h2
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h1
  refine Filter.eventually_atTop.2 ⟨max X 1, fun n hn => ?_⟩
  exact h2 X hX n (le_trans (le_max_right _ _) hn) (le_trans (le_trans (le_max_left _ _) hn)
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_apply)

end OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R1
