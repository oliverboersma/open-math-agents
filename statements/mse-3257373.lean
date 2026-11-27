import Mathlib

/-!
# Is $\lfloor \zeta(-n) \rfloor$ only prime for $n=23$?

Source: https://math.stackexchange.com/questions/3257373/is-lfloor-zeta-n-rfloor-only-prime-for-n-23
Credit: @mgv27

I searched for primes of the form $\lfloor \zeta(-n) \rfloor$, where $n \in \mathbb{N}$, for
$n \le 10^4$ and found $\lfloor \zeta(-n) \rfloor$ is only prime for $n = 23$.
Note $\zeta(-(2n-1)) = -\frac{B_{2n}}{2n}$.

(1) Is $\lfloor \zeta(-n) \rfloor$, where $n \in \mathbb{N}$, only prime for $n = 23$?
(2) Are there finitely many primes of the form $\lfloor \zeta(-n) \rfloor$?

Formalization notes:
* `main` states question (1), the asker's conjecture: for `n ≥ 1`, `⌊ζ(-n)⌋` is a (positive)
  prime iff `n = 23` (`ζ(-23) = 236364091/65520 ≈ 3607.51`, and `3607` is prime).
* `ζ` is Mathlib's `riemannZeta`; `ζ(-n)` is real (Mathlib's `riemannZeta_neg_nat_eq_bernoulli`
  gives `(-1)^n B_{n+1}/(n+1)`), and we take the floor of its real part.
* "Prime" means a positive prime, as with PARI's `ispseudoprime` used by the asker; the floor
  is negative for `n ≡ 1 (mod 4)`, `n ≥ 1`.
* Comments report no other prime for `n ≤ 2·10⁴`; heuristically infinitely many are expected.
-/

namespace OMA.S_mse_3257373

/-- `⌊ζ(-n)⌋` as an integer. -/
noncomputable def floorZetaNeg (n : ℕ) : ℤ :=
  ⌊(riemannZeta (-(n : ℂ))).re⌋

/-- Question (1): for `n ≥ 1`, `⌊ζ(-n)⌋` is prime only for `n = 23`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ p : ℕ, p.Prime ∧ floorZetaNeg n = (p : ℤ)) ↔ n = 23) := by
  sorry

end OMA.S_mse_3257373
