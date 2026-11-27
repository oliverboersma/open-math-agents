import Mathlib

/-!
# OEIS A102730

For `0 ≤ m ≤ n` count `m` when the binary expansion of `m!` is a contiguous
substring of the binary expansion of `n!`. The indices zero and one are both
counted. Reversing both words preserves contiguous containment, so we may
use Lean's least-significant-digit-first expansions throughout.

Zumkeller proposed boundedness. Greathouse conjectured the opposite,
namely that for every `k` some term exceeds `k`.

Source: https://oeis.org/A102730
-/

namespace OMA.S_oeis_a102730

def occurs (m n : ℕ) : Prop :=
  (Nat.digits 2 m.factorial).IsInfix (Nat.digits 2 n.factorial)

noncomputable def term (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n+1)).filter (fun m => occurs m n)).card

theorem main : ∀ k : ℕ, ∃ n : ℕ, k < term n := by
  sorry

end OMA.S_oeis_a102730
