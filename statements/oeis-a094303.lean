import Mathlib

/-!
# Mathar's recurrence identity for A094303

Source: https://oeis.org/A094303
Conjecture: R. J. Mathar, April 24, 2007.
Proof in the OEIS entry: Petros Hadjicostas, May 11, 2020.

The sequence starts with a(1) = 1 and a(2) = 2. For n ≥ 2,
a(n+1) equals a(n) times the sum of a(1) through a(n-1).
The pair below stores the current term and that preceding sum.
In the companion recurrence both sequences start at 1. The next
values are their sum and their product respectively. Its first
coordinate is A003686, denoted u.
-/

namespace OMA.S_oeis_a094303

def state : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 =>
      let (current, previousSum) := state k
      (current * previousSum, previousSum + current)

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => (state k).1

def companion : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
      let (currentSum, currentProduct) := companion k
      (currentSum + currentProduct, currentSum * currentProduct)

def u (n : ℕ) : ℕ := (companion (n - 1)).1

theorem main : ∀ n : ℕ, 3 ≤ n → a n = u (n + 1) - u n := by
  sorry

end OMA.S_oeis_a094303
