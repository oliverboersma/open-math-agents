import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Prime divisors and gaps for the constant coordinate of (2 + √2 + √3)^n

The ordered basis is 1, √2, √3, √6. Multiplication in this basis gives the
four-coordinate recurrence and the initial power is 1. The indices start
at zero. The gap sequence uses consecutive hits in the full increasing
enumeration. The seven displayed blocks and their claimed lengths are
transcribed as printed. The phase allows the starting position of a cyclic word.

Source: https://oeis.org/A377109
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a377109

def coords : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 0, 0, 0)
  | n+1 =>
    let (a, b, c, d) := coords n
    (2*a + 2*b + 3*c, a + 2*b + 3*d, a + 2*c + 2*d, b + c + 2*d)

def a (n : ℕ) : ℕ := (coords n).1

def displayed : List (ℕ × List ℕ) := [
  (2, [4]),
  (3, [8, 1, 4, 3, 8]),
  (5, [10, 20, 9, 8, 32, 21, 20]),
  (7, [2, 30, 9, 19, 6, 28, 12, 5, 16, 26, 22, 13, 2, 1, 24, 16, 57]),
  (11, [61, 29, 70]),
  (13, [9, 15, 24, 3, 21, 21, 3, 24, 15, 9, 24]),
  (17, [30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 1, 29, 29, 1, 30, 30, 30, 30, 2, 28, 30, 30, 28, 2, 17, 13, 30, 30, 30, 13, 17])]

def gap (k : ℕ → ℕ) (j : ℕ) : ℕ := k (j+1) - k j

def purePeriod (k : ℕ → ℕ) (d : ℕ) : Prop :=
  0 < d ∧ ∀ j : ℕ, gap k (j+d) = gap k j

/-- The infinitude, eventual-period and seven explicit pure-period claims. -/
theorem main : ∀ p : ℕ, Nat.Prime p → ∃ k : ℕ → ℕ,
    StrictMono k ∧ (∀ n : ℕ, p ∣ a n ↔ ∃ j : ℕ, k j = n) ∧
    (∃ N d : ℕ, 0 < d ∧ ∀ j : ℕ, N ≤ j → gap k (j+d) = gap k j) ∧
    ∀ w : List ℕ, (p, w) ∈ displayed →
      (∃ phase : ℕ, ∀ j : ℕ, gap k j = w.getD ((j+phase) % w.length) 0) ∧
      purePeriod k w.length ∧ (∀ d : ℕ, purePeriod k d → w.length ≤ d) := by
  sorry

end OMA.S_oeis_a377109
