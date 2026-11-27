import Mathlib

/-!
# Powers of ten in the digit-sum sequence A007618

Charles R Greathouse IV conjectured in the OEIS entry for A007618 that
infinitely many powers of ten occur in the sequence.

Source: https://oeis.org/A007618
Formalization: Codex (AI)
-/

namespace OMA.S_oeis_a007618

/-- After `k` iterations from 5, this is the OEIS term with index `k + 1`. -/
def orbit (k : ℕ) : ℕ :=
  Nat.iterate (fun n : ℕ => n + (Nat.digits 10 n).sum) k 5

theorem main : {e : ℕ | ∃ k : ℕ, orbit k = 10 ^ e}.Infinite := by
  sorry

end OMA.S_oeis_a007618
