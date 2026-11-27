import Mathlib

/-!
# A006318: irreducibility of Schröder polynomials modulo small primes

Source: https://oeis.org/A006318
Credit: @caa1982

`a(n)` is the `n`-th large Schröder number ($1, 2, 6, 22, 90, 394, \ldots$, offset 0). It equals
$\sum_{k=0}^{n} \binom{n+k}{2k} C_k$ with $C_k$ the Catalan numbers (a standard formula, used below
as the definition; it reproduces the listed terms).

Conjecture (Zhi-Wei Sun, Apr 07 2013): for each $n > 2$, the polynomial
$\sum_{k=0}^{n} a(k) x^{n-k}$ is irreducible modulo some prime $p < n(n+1)$, i.e. its reduction in
$\mathbb{F}_p[x]$ is irreducible for some such prime. (The polynomial is monic, since $a(0) = 1$, so
its reduction keeps degree $n$.)

The entry also records a conjecture of Colin Defant (Sep 17 2018) on permutations whose image under
West's stack-sorting map avoids 231 and 321. Read literally with the entry's offset it fails at
$n = 1$ (one permutation of length 1, but $a(1) = 2$), so its intended indexing is ambiguous; it is
not part of this statement.
-/

namespace OMA.S_oeis_a006318

/-- The large Schröder number $a(n) = \sum_{k=0}^{n} \binom{n+k}{2k} C_k$. -/
def schroder (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n + k).choose (2 * k) * catalan k

/-- The reduction modulo `p` of $\sum_{k=0}^{n} a(k) x^{n-k}$. -/
noncomputable def schroderPoly (p n : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (schroder k : ZMod p) * Polynomial.X ^ (n - k)

/-- Conjecture (Sun): for every `n > 2` some prime `p < n (n + 1)` makes the polynomial irreducible
modulo `p`. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p < n * (n + 1) ∧
    Irreducible (schroderPoly p n) := by
  sorry

end OMA.S_oeis_a006318
