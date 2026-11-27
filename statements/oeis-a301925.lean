import Mathlib

/-!
# A301925: a(n) is the smallest prime p such that the gap between p and the next prime is 4*n.

Source: https://oeis.org/A301925
Credit: @LAPRAI

Formalizes the OEIS comment: It is a plausible conjecture that a(n) always exists (N. J. A. Sloane, Jul 21 2018).

Conventions: offset 1; the gap between `p` and the next prime is `4n` means `p` and `p + 4n` are prime and no number strictly between them is prime.
-/

namespace OMA.S_oeis_a301925

/-- For every `n ≥ 1` some prime `p` is followed by the next prime `p + 4n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (p + 4 * n).Prime ∧
    ∀ m : ℕ, p < m → m < p + 4 * n → ¬ m.Prime := by
  sorry

end OMA.S_oeis_a301925
