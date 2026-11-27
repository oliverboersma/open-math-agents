import Mathlib

/-!
# OEIS A394431

Among all bases b with 1 < b < n, choose the least base giving the maximum
digit sum of n. For n > 8, Sean A. Irvine conjectured that the chosen
base is ceil((n+1)/2), equivalently floor(n/2)+1.

Source: https://oeis.org/A394431
-/

namespace OMA.S_oeis_a394431

def ds (b n : ℕ) := (Nat.digits b n).sum

def maximizer (n b : ℕ) : Prop :=
  1 < b ∧ b < n ∧ ∀ c, 1 < c → c < n → ds c n ≤ ds b n

theorem main : ∀ n : ℕ, 8 < n → IsLeast {b | maximizer n b} (n/2+1) := by
  sorry

end OMA.S_oeis_a394431
