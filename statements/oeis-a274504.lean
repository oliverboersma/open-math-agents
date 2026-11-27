import Mathlib

/-!
# A274504: Primes with Kronecker symbol (p|14) != 1

Source: https://oeis.org/A274504
Credit: @xor2k

Formalizes the conjecture in the comments of OEIS A274504, which reads:
Conjecture: primes not congruent to (1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45) mod 56.
That is, a prime `p` belongs to the sequence (its Kronecker symbol `(p|14)` is not `1`) if and
only if `p mod 56` is not one of the twelve listed residues.

Conventions:
* Mathlib has no Kronecker symbol, so it is defined below for a positive lower argument `n`:
  writing `n = 2^e * m` with `m` odd (`e = n.factorization 2`), `(a|n) = (a|2)^e * (a|m)`, where
  `(a|m)` is the Jacobi symbol (Mathlib's `jacobiSym`) and `(a|2)` is the Kronecker symbol at `2`:
  `0` for even `a`, `1` for `a ≡ 1, 7 (mod 8)`, `-1` for `a ≡ 3, 5 (mod 8)`, which is exactly
  Mathlib's character `ZMod.χ₈`. This agrees with the standard Kronecker symbol for `n > 0`
  (as used by Magma's KroneckerSymbol in the OEIS program); for `n = 14` it is `χ₈(a) * (a|7)`.
* `p` ranges over all primes (`Nat.Prime p`), cast to `ℤ` for the symbol; `mod 56` is `%`.
-/

namespace OMA.S_oeis_a274504

/-- Kronecker symbol `(a|n)` for `n > 0`: `χ₈(a)^e * J(a | n / 2^e)` with `e` the exponent of `2`
in `n` and `J` the Jacobi symbol. -/
def kronecker (a : ℤ) (n : ℕ) : ℤ :=
  ZMod.χ₈ (a : ZMod 8) ^ (n.factorization 2) * jacobiSym a (n / 2 ^ (n.factorization 2))

/-- A prime `p` has Kronecker symbol `(p|14) ≠ 1` if and only if `p mod 56` is not among
`1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45`. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p →
      (kronecker p 14 ≠ 1 ↔
        p % 56 ∉ ({1, 3, 5, 9, 13, 15, 19, 23, 25, 27, 39, 45} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a274504
