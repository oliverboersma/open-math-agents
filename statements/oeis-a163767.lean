import Mathlib

/-!
# A163767: a(n) = tau_{n}(n) = number of ordered n-factorizations of n

Source: https://oeis.org/A163767
Credit: @xor2k

Formalizes the OEIS A163767 conjecture (offset 1): a(n) = n^k when n is the product of k
distinct primes.

Conventions: `a n` is the number of ordered `n`-tuples `(d_1, ..., d_n)` of natural numbers
with `d_1 * ... * d_n = n` (tuples are functions `Fin n → ℕ`; for `n ≥ 1` every entry is a
positive divisor of `n`, so the set is finite and `Nat.card` is its size). This is
`tau_n(n)`, the `n`-th term of the `n`-fold Dirichlet self-convolution of the all-ones
sequence. A number that is the product of `k` distinct primes is written as `∏ p ∈ s, p` for a
finite set `s` of primes with `s.card = k`; the case `s = ∅` gives `n = 1`, `k = 0`.
-/

namespace OMA.S_oeis_a163767

/-- `a n = tau_n(n)`: the number of ordered `n`-tuples of natural numbers whose product is `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {f : Fin n → ℕ // ∏ i, f i = n}

/-- If `n` is the product of the `k = s.card` distinct primes in `s`, then `a n = n ^ k`. -/
theorem main :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → a (∏ p ∈ s, p) = (∏ p ∈ s, p) ^ s.card := by
  sorry

end OMA.S_oeis_a163767
