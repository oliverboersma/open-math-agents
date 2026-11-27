import Mathlib

/-!
# A001045: Jacobsthal sequence (or Jacobsthal numbers): a(n) = a(n-1) + 2*a(n-2), with a(0) = 0, a(1) = 1; also a(n) = nearest integer to 2^n/3.

Source: https://oeis.org/A001045
Credit: @ShoQo

Two conjectures from the entry, both marked true there (Sela Fried, 2025):
* Fossaceca (Jan 31 2009): "It appears that a(n) is also the number of integers between 2^n
  and 2^(n+1) that are divisible by 3 with no remainder."
* Copeland (Nov 06 2012): "3!*a(n-1) is apparently the trace of the n-th power of the adjacency
  matrix of the complete 3-graph, a 3 X 3 matrix with diagonal elements all zero and
  off-diagonal all ones. The off-diagonal elements for the n-th power are all equal to a(n)
  while each diagonal element seems to be a(n) + 1 for an even power and a(n) - 1 for an odd."

Formalization notes:
* Offset 0. "Between 2^n and 2^(n+1)" is the open interval (the endpoints are powers of 2, so
  this does not matter).
* Copeland's claims are stated for powers `n ≥ 1` (the trace formula uses a(n-1)).
-/

namespace OMA.S_oeis_a001045

/-- The Jacobsthal numbers: a(0) = 0, a(1) = 1, a(n) = a(n-1) + 2 a(n-2). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a (n + 1) + 2 * a n

/-- The adjacency matrix of the complete graph on 3 vertices. -/
def A : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => if i = j then 0 else 1

theorem main :
    (∀ n : ℕ, ((((Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card : ℕ) : ℤ) = a n) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A ^ n).trace = 6 * a (n - 1) ∧
      (∀ i j, i ≠ j → (A ^ n) i j = a n) ∧
      (∀ i, (A ^ n) i i = if Even n then a n + 1 else a n - 1)) := by
  sorry

end OMA.S_oeis_a001045
