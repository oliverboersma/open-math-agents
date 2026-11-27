import Mathlib

/-!
# OEIS A318291: for every odd prime p, infinitely many j with j*2^k - p composite for all k > 0

Source: https://oeis.org/A318291 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry, offset 1: a(n) is the minimum k > 0 such that n*2^k - 3 is prime, or 0 if no such k exists.
Comment (Martin Michael Musatov, Sep 04 2018): Conjecture: For every odd prime p, there exist
infinitely many numbers j that are non-multiples of p and have the property that j*2^k - p is
composite for every k > 0. (An earlier comment by Robert Israel, Aug 24 2018, shows by a covering
set that such j exist for p = 3.)

Formalization notes:
* j ranges over the natural numbers; a number is composite when it is greater than 1 and not
  prime. The subtraction is the truncated one of the natural numbers, and the condition
  1 < j*2^k - p makes it the true difference.
* `main` is the conjecture for every prime p other than 2.
-/

namespace OMA.S_oeis_a318291

/-- Musatov's conjecture: for every odd prime p there are infinitely many j, not multiples of p,
such that j*2^k - p is composite for every k > 0. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 →
    Set.Infinite {j : ℕ | ¬ p ∣ j ∧ ∀ k, 0 < k → 1 < j * 2 ^ k - p ∧ ¬ (j * 2 ^ k - p).Prime} := by
  sorry

end OMA.S_oeis_a318291
