import Mathlib

/-!
# OEIS A083807

Amarnath Murthy and Meenakshi Srikanth consider perfect powers whose decimal
digits belong to `{0, 4, 6, 8, 9}`. They call a term trivial when it is
obtained from another term by multiplying by a positive power of ten and
conjecture that the set of nontrivial terms is infinite.

Source: https://oeis.org/A083807
-/

namespace OMA.S_oeis_a083807

def isTerm (n : ℕ) : Prop :=
  (∃ a e : ℕ, 2 ≤ a ∧ 2 ≤ e ∧ n = a ^ e) ∧
    ∀ d ∈ Nat.digits 10 n, d ∈ ({0, 4, 6, 8, 9} : Finset ℕ)

def nontrivialTerms : Set ℕ :=
  {n | isTerm n ∧ ¬ ∃ k m : ℕ, 0 < k ∧ isTerm m ∧ n = 10 ^ k * m}

theorem main : nontrivialTerms.Infinite := by
  sorry

end OMA.S_oeis_a083807
