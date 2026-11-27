import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Basic

/-!
# Neighboring squarefree numbers at multiples of m

Source: https://oeis.org/A357315 (Juri-Stepan Gerasimov, OEIS Foundation,
CC BY-SA 4.0).

The test in the entry ranges over the positive integers k strictly less
than the positive candidate m. The conjecture is finiteness of the full
set of such m.
-/

namespace OMA.S_oeis_a357315

def terms : Set ℕ :=
  {m | 0 < m ∧ ∀ k : ℕ, 0 < k → k < m → Squarefree (m*k - 1) ∨ Squarefree (m*k + 1)}

theorem main : terms.Finite := by
  sorry

end OMA.S_oeis_a357315
