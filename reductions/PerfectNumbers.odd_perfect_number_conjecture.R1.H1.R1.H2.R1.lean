import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H2.R1
-- of step PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers with least prime factor 3: exactly three prime factors, and the open rest

The parent step says that an odd perfect number with at least three distinct prime factors does
not have least prime factor `3`.

* `H1` (classical; Peirce 1832, Sylvester 1888): the statement for exactly three distinct prime
  factors, because no odd perfect number has exactly three distinct prime factors at all. The
  bound `2 * ∏ (p - 1) ≤ ∏ p` leaves only the prime supports `{3, 5, 7}`, `{3, 5, 11}` and
  `{3, 5, 13}`; each is excluded by the size of `σ(n) / n` for the admissible exponents together
  with a few divisibility facts.
* `H2`: the case of four or more distinct prime factors, which stays open.
-/

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1_H2_R1

/-- Exactly three distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card = 3 → Nat.minFac n ≠ 3

/-- The open part: four or more distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → 4 ≤ n.primeFactors.card → Nat.minFac n ≠ 3

theorem main : H1 → H2 →
    OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1.H2 := by
  intro h1 h2 n hperf hodd hc
  by_cases h3 : n.primeFactors.card = 3
  · exact h1 n hperf hodd h3
  · exact h2 n hperf hodd (by omega)

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1_H2_R1
