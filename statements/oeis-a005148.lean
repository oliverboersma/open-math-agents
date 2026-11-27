import Mathlib

/-!
# The 2-adic valuation of the Newman–Shanks sequence

Sources: https://oeis.org/A005148 and https://oeis.org/A076657
Conjecture: Benoit Cloitre, June 22, 2002.
Known proof: Miquel Cerda, https://doi.org/10.5281/zenodo.23928179.

Let C(n) be the central binomial coefficient. The Shanks–Beukers
convolution in A005148 and A076657 determines a(n) for n ≥ 1:
the convolution of C(n)^3 with a(n) is C(n)(16^n - C(n)^2)/24.
The definition below computes 24 times the sequence before dividing.
The binary digit sum counts the ones in the binary expansion.
An odd quotient expresses that the indicated power of 2 divides a(n)
exactly, with no extra factor of 2.
-/

namespace OMA.S_oeis_a005148

def central (n : ℕ) : ℤ := ((2 * n).choose n : ℕ)

def scaled : (n : ℕ) → ℤ
  | 0 => 0
  | n + 1 =>
      central (n + 1) * (16 ^ (n + 1) - central (n + 1) ^ 2) -
        ∑ i : Fin n, central (n - (i : ℕ)) ^ 3 * scaled ((i : ℕ) + 1)
termination_by n => n
decreasing_by exact Nat.succ_lt_succ i.isLt

def a (n : ℕ) : ℤ := scaled n / 24

def weight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem main : ∀ n : ℕ, 0 < n →
    ∃ u : ℤ, Odd u ∧ a n = 2 ^ (3 * (weight n - 1)) * u := by
  sorry

end OMA.S_oeis_a005148
