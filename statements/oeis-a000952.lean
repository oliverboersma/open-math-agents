import Mathlib

/-!
# A000952: Numbers k == 2 (mod 4) that are the orders of conference matrices.

Source: https://oeis.org/A000952
Credit: @mbilenko03

The entry says: if `k ≡ 2 (mod 4)` then a necessary condition (for a conference matrix of order
`k` to exist) is that `k - 1` is a sum of 2 squares (A286636), and it is conjectured that this
condition is also sufficient. The conjecture: for every `k ≡ 2 (mod 4)` such that `k - 1` is a
sum of two squares, there is a conference matrix of order `k`.

Conventions:
- As in the entry, a conference matrix of order `k` is a `k × k` matrix `A` with entries in
  `{-1, 0, +1}` such that `A Aᵀ = (k - 1) I`. (Each row then has exactly one zero, and permuting
  columns gives the usual form with zero diagonal, so this agrees with the standard definition.)
- 'Sum of 2 squares' allows a zero square (e.g. `9 = 3^2 + 0^2`, and 10 is a term).
-/

namespace OMA.S_oeis_a000952

/-- `A` is a conference matrix of order `k`: entries in `{-1, 0, 1}` and `A Aᵀ = (k - 1) I`. -/
def IsConferenceMatrix (k : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) ∧
    A * A.transpose = ((k : ℤ) - 1) • (1 : Matrix (Fin k) (Fin k) ℤ)

theorem main :
    ∀ k : ℕ, k % 4 = 2 → (∃ a b : ℕ, k - 1 = a ^ 2 + b ^ 2) →
      ∃ A : Matrix (Fin k) (Fin k) ℤ, IsConferenceMatrix k A := by
  sorry

end OMA.S_oeis_a000952
