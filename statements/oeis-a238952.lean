import Mathlib.NumberTheory.Divisors

/-!
# Arcs in the transitive closure of the divisor lattice

OEIS A238952 counts the strict divisibility pairs (a,b) among the positive
divisors of n. Grouping edges by their upper endpoint b gives one arc for
each proper divisor of b. Wesley Ivan Hurt conjectured the floor-sum formula
on 21 December 2017. Antti Karttunen recorded the related sum of divisor
counts over proper divisors in 2018, following Geoffrey Critzer.

Source: https://oeis.org/A238952
Formalization: @anmolspace, with OpenAI Codex.
-/
namespace OMA.S_oeis_a238952

/-- An arc with upper endpoint b starts at any proper divisor of b. -/
def arcs (n : ℕ) : ℕ := ∑ b ∈ n.divisors, b.properDivisors.card

theorem main : ∀ n : ℕ, 1 ≤ n → arcs n =
    ∑ i ∈ Finset.Icc 1 (n/2), i.divisors.card * (n/i - (n-1)/i) := by
  sorry

end OMA.S_oeis_a238952
