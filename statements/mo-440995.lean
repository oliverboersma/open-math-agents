import Mathlib

/-!
# A sum over the descents of the squares modulo a prime

Source: https://mathoverflow.net/questions/440995

For a prime `p` with `p % 4 = 1`, let `A_p` be the set of integers `a` with
`0 ≤ a ≤ p` such that the remainder of `(a + 1)^2` modulo `p` is smaller than
the remainder of `a^2` modulo `p`. The question conjectures that the elements
of `A_p` add up to `7 (p^2 - 1) / 24`. This states that the conjecture holds.
-/

namespace OMA.S_mo_440995

/-- The set `A_p`, as a finite set of natural numbers in `[0, p]`. -/
def descentSet (p : ℕ) : Finset ℕ :=
  (Finset.range (p + 1)).filter (fun a => (a + 1) ^ 2 % p < a ^ 2 % p)

theorem main : ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ((∑ n ∈ descentSet p, n : ℕ) : ℚ) = 7 * ((p : ℚ) ^ 2 - 1) / 24 := by
  sorry

end OMA.S_mo_440995
