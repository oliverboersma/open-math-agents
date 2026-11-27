import Mathlib

/-!
# A213382: Numbers n such that n^n mod (n + 2) = n

Source: https://oeis.org/A213382
Credit: @AkiRA-COM-FP

Formalizes the OEIS A213382 conjecture: every term of A176003, namely `n = 3*k - 2`
where `k = 1` or `k` is prime, satisfies `n^n % (n + 2) = n`.
-/

namespace OMA.S_oeis_a213382

/-- For every noncomposite positive integer `k` (`k = 1` or `k` prime),
`n = 3*k - 2` satisfies `n^n % (n + 2) = n`. -/
theorem main :
    ∀ k : ℕ, (k = 1 ∨ k.Prime) →
      (3 * k - 2) ^ (3 * k - 2) % (3 * k) = 3 * k - 2 := by
  sorry

end OMA.S_oeis_a213382
