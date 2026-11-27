import Mathlib

/-!
# OEIS A252491 and prime decimal concatenations

Source: https://oeis.org/A252491 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

M. F. Hasler observed the relation below in 2015. The definition of the
companion sequence follows OEIS A086766 and the corresponding Formal Conjectures module.
-/

namespace OMA.S_oeis_a252491

/-- The decimal geometric sum in A252491, whose first index is one. -/
def a (n : ℕ) : ℕ := (10 ^ (n ^ 2) - 1) / (10 ^ n - 1)

/-- A086766 is the least positive number of repetitions of the decimal expansion of
`n` which yield a prime after appending a final 1, or zero if no such count exists. -/
noncomputable def repetitionCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    sInf {r : ℕ | 0 < r ∧
      (n * (∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10 n).length) ^ i) * 10 + 1).Prime}

theorem main : ∀ p : ℕ, p.Prime → ¬ (a p).Prime → repetitionCount (10 ^ (p - 1)) = 0 := by
  sorry

end OMA.S_oeis_a252491
