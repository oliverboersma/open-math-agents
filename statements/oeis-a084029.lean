import Mathlib

/-!
# OEIS A084029

Row `n`, starting at `n = 1`, lists the first `n` positive `n`-digit
multiples of `n` with decimal digit sum `n`, padding with zeros if needed.
The conjecture says there is just one zero in the entire triangle. The
second row is `[20, 0]`. Thus the conjecture says that every other row has
at least `n` distinct eligible entries.

Source: https://oeis.org/A084029
-/

namespace OMA.S_oeis_a084029

def qualifies (n m : ℕ) : Prop :=
  (Nat.digits 10 m).length = n ∧ n ∣ m ∧ (Nat.digits 10 m).sum = n

theorem main : (∀ m : ℕ, qualifies 2 m ↔ m = 20) ∧
    ∀ n : ℕ, 0 < n → n ≠ 2 → ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ m ∈ s, qualifies n m := by
  sorry

end OMA.S_oeis_a084029
