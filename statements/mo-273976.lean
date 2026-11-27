import Mathlib

/-!
# $G$ a group, with $p$ a prime number, and $|G|=2^p-1$, is it abelian?

Source: https://mathoverflow.net/questions/273976
Credit: @nokiexow

Primality is assumed for the exponent, not for the order of the group.
-/

namespace OMA.S_mo_273976

universe u

theorem main : ∀ p : ℕ, p.Prime → ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = 2 ^ p - 1 → ∀ g h : G, g * h = h * g := by
  sorry

end OMA.S_mo_273976

