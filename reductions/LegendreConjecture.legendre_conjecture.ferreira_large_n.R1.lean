import FormalConjectures.Wikipedia.LegendreConjecture
import Mathlib

/-! Legendre's conjecture for large n from Andrica's inequality for large n. Both are
consequences of Ferreira, Real exponential sums over primes and prime gaps (arXiv 2307.08725),
and the second is the catalogue's Andrica.andrica_conjecture.ferreira_large_n. The passage
from Andrica to Legendre is elementary: if p is the largest prime up to m^2 and q the next
prime, then sqrt q < 1 + sqrt p ≤ 1 + m, so q lies strictly between m^2 and (m + 1)^2. -/

namespace OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1

/-- Andrica's inequality for all sufficiently large n (Ferreira). -/
def H1 : Prop := ∀ᶠ n : ℕ in Filter.atTop,
  Real.sqrt ((n + 1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1

/-- Andrica's inequality from the N-th prime on implies a prime between m^2 and (m + 1)^2
whenever m^2 exceeds the N-th prime. -/
def H2 : Prop := ∀ N : ℕ,
  (∀ n ≥ N, Real.sqrt ((n + 1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1) →
  ∀ m : ℕ, N.nth Nat.Prime < m ^ 2 → ∃ p ∈ Set.Ioo (m ^ 2) ((m + 1) ^ 2), Nat.Prime p

theorem main : H1 → H2 →
    type_of% @LegendreConjecture.legendre_conjecture.ferreira_large_n := by
  intro h1 h2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
  refine Filter.eventually_atTop.2 ⟨N.nth Nat.Prime + 1, fun m hm => ?_⟩
  exact h2 N hN m (lt_of_lt_of_le hm (Nat.le_self_pow two_ne_zero m))

end OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1
