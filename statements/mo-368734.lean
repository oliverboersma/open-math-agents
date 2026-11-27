import Mathlib

/-!
# Integer polynomial inducing a permutation of order $p$ on $\mathbb{Z}/p\mathbb{Z}$ for infinitely many $p$

Source: https://mathoverflow.net/questions/368734
Credit: @nokiexow

The same integer polynomial must work for infinitely many prime moduli.
The order refers to the permutation under composition.
-/

namespace OMA.S_mo_368734

theorem main : ∃ Q : Polynomial ℤ, 2 ≤ Q.natDegree ∧
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ σ : Equiv.Perm (ZMod p),
      orderOf σ = p ∧ ∀ x : ZMod p, σ x = Q.eval₂ (Int.castRingHom (ZMod p)) x} := by
  sorry

end OMA.S_mo_368734

