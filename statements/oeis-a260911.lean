import Mathlib

/-!
# A260911: Least k < prime(n) with i^2 + j^2 = k^2 for some 0 < i < j < k, all quadratic residues mod prime(n)

Source: https://oeis.org/A260911
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A260911): (i) a(n) > 0 for all n > 25. In other words,
for any prime p > 100, we have a^2 + b^2 = c^2 for some a,b,c in the set
R(p) = {0<r<p: r is a quadratic residue mod p}. I have verified the conjecture for primes
p < 1.5*10^7.

(Only part (i) of the conjecture is formalized here.)

Conventions:
* The conjecture is stated in its second form, for every prime p > 100 (prime(26) = 101), with
  0 < a < b < c < p as in the definition of the sequence (0 < i < j < k < prime(n)).
* a^2 + b^2 = c^2 is an equation of integers.
* For 0 < r < p, r is a quadratic residue modulo p when its class in `ZMod p` is a square:
  `IsSquare (r : ZMod p)`.
-/

namespace OMA.S_oeis_a260911

/-- Sun's conjecture (i) on A260911: for every prime `p > 100` there are quadratic residues
`0 < a < b < c < p` modulo `p` with `a^2 + b^2 = c^2`. -/
theorem main : ∀ p : ℕ, p.Prime → 100 < p → ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < p ∧
    a ^ 2 + b ^ 2 = c ^ 2 ∧
    IsSquare (a : ZMod p) ∧ IsSquare (b : ZMod p) ∧ IsSquare (c : ZMod p) := by
  sorry

end OMA.S_oeis_a260911
