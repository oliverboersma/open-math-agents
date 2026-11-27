import FormalConjectures.Paper.KaplanskyUInvariant
import Mathlib

/-! Reduction of Karpenko's theorem on values of the u-invariant to Merkurjev's theorem for
positive even integers (H1) and the odd case n >= 9 with n + 1 and n + 3 not powers of 2 (H2),
ruling out n in {0, 1, 3, 5, 7} directly in `main`. -/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_karpenko_R1

open KaplanskyUInvariant

/-- Merkurjev (1991): every positive even integer is a u-invariant. -/
def H1 : Prop :=
  ∀ n : ℕ, Even n → n ≠ 0 → IsUInvariant n

/-- Odd case of Karpenko's theorem: every odd integer n >= 9 such that neither n + 1 nor n + 3
is a power of 2 is a u-invariant. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 9 ≤ n → (∀ r, 2 ^ r ≠ n + 1) → (∀ r, 2 ^ r ≠ n + 3) → IsUInvariant n

theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.karpenko := by
  intro h1 h2 n hn1 hn3
  have hn0 : n ≠ 0 := by
    intro h0
    exact hn1 0 (by omega)
  rcases Nat.even_or_odd n with heven | hodd
  · exact h1 n heven hn0
  · have hge9 : 9 ≤ n := by
      by_contra hlt
      push_neg at hlt
      rcases hodd with ⟨k, rfl⟩
      have hk : k < 4 := by omega
      interval_cases k
      · exact hn1 1 (by norm_num)
      · exact hn1 2 (by norm_num)
      · exact hn3 3 (by norm_num)
      · exact hn1 3 (by norm_num)
    exact h2 n hodd hge9 hn1 hn3

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_karpenko_R1
