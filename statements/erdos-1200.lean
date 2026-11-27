import Mathlib

/-!
# Erdős Problem 1200

Source: https://www.erdosproblems.com/1200
Credit: @timlantin

There exists a constant $C$ such that for all large $x$ there is a collection of primes
$p_1<\ldots<p_k<x$ with $\sum\frac{1}{p_i}<C$ together with a system of congruences
$a_i\pmod{p_i}$ such that every integer $n<x$ satisfies at least one of these congruences.

A conjecture of Erdős and Ruzsa.

Formalization notes:
* `x` ranges over natural numbers, which is equivalent to real `x` via $\lceil x \rceil$.
* The covered integers are $1 \leq n < x$.
* Written with Claude Code (AI-assisted).
-/

namespace OMA.S_erdos_1200

open Filter

/-- The Erdős–Ruzsa covering conjecture. -/
theorem main :
    ∃ C : ℝ, ∀ᶠ x : ℕ in atTop, ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p < x) ∧
      ∑ p ∈ P, (1 : ℝ) / p < C ∧
      ∃ a : ℕ → ℕ, ∀ n, 1 ≤ n → n < x → ∃ p ∈ P, n ≡ a p [MOD p] := by
  sorry

end OMA.S_erdos_1200
