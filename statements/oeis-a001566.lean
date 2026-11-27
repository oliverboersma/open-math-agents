import Mathlib.Data.Nat.Basic

/-!
Gerald McGarvey's conjecture in OEIS A001566, 8 August 2004.
Source: https://oeis.org/A001566/internal

This uses the printed expression 8a+7. The numerical examples instead
correspond to 40a+7. The proposed proof addresses both normalizations.
The quotient sequence starts at index 1 of A001566. Its indices 1, 3, …
are the alternating terms whose displayed examples include 0 and 55.
The membership clause starts with the positive quotients, since A046194
starts at 1 and the comment's listed positions start at its first term.
-/

namespace OMA.S_oeis_a001566

def term : ℕ → ℕ
  | 0 => 3
  | n + 1 => term n ^ 2 - 2

def a (n : ℕ) : ℕ := (term n - 7) / 8

def IsHeptagonalTriangular (a : ℕ) : Prop :=
  (∃ h : ℕ, 0 < h ∧ 2 * a = h * (5 * h - 3)) ∧
    (∃ t : ℕ, 0 < t ∧ 2 * a = t * (t + 1))

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, 1 < d → ¬ (d ^ 2 ∣ a n)) ∧
    (∀ k : ℕ, 55 ∣ a (2 * k + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → IsHeptagonalTriangular (a n)) := by
  sorry

end OMA.S_oeis_a001566
