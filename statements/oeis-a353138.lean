import Mathlib

/-!
# OEIS A353138

For a positive integer `n` with `b` decimal digits, William Halpin's
function adds `b ^ d` over every digit `d` of `n`, counting repeated
digits with multiplicity. The conjectured fixed points are 1 and 4624.

Source: https://oeis.org/A353138
-/

namespace OMA.S_oeis_a353138

def term (n : ℕ) : ℕ :=
  let digits := Nat.digits 10 n
  (digits.map (fun d => digits.length ^ d)).sum

theorem main : ∀ n : ℕ, 0 < n → (term n = n ↔ n = 1 ∨ n = 4624) := by
  sorry

end OMA.S_oeis_a353138
