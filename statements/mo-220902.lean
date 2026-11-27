import Mathlib

/-!
# Primes of the form $(2m+1)^2-2^{2s+1}$

Source: https://mathoverflow.net/questions/220902
Credit: @LordMike

Source question (MathOverflow 220902, posed by the user few_reps in 2015): 'Does there exist infinitely
many primes of the form $(2m+1)^2-2^{2s+1}$ with $m,s\geq 1$ ?'. The asker notes that the Bunyakowsky
conjecture would give an affirmative answer for each fixed s, but that conjecture is not known for any
polynomial of degree at least 2; the question remains unanswered (no answers, comments judge a proof
to be a major achievement).

Modelling choices:
* The question is yes/no with no stated answer. The natural (heuristically expected) direction is
  affirmative, so `main` asserts that the set of such primes is infinite; the answer could in principle be
  negative.
* Primes are positive, so the expression is evaluated in the integers and the set collects natural
  primes `p` with `(p : ℤ) = (2m+1)^2 - 2^(2s+1)` for some naturals m, s with m ≥ 1 and s ≥ 1. Negative
  values of the expression (which occur when 2^(2s+1) exceeds (2m+1)^2) are not counted, since they are
  not prime numbers (a commenter asked about this and the asker replied that negative values are not counted).
* We count distinct prime values (the literal reading of the question), not pairs (m, s). (The two
  readings coincide: for fixed p the equation x^2 - p = 2^n has only finitely many solutions, at most
  four by Beukers' theorem on the generalized Ramanujan-Nagell equation; this is not needed for the
  statement.)
* Example (non-vacuity): m = 3, s = 1 gives 49 - 8 = 41, a prime.
-/

namespace OMA.S_mo_220902

theorem main :
    {p : ℕ | p.Prime ∧ ∃ m s : ℕ, 1 ≤ m ∧ 1 ≤ s ∧
      (p : ℤ) = (2 * (m : ℤ) + 1) ^ 2 - 2 ^ (2 * s + 1)}.Infinite := by
  sorry

end OMA.S_mo_220902
