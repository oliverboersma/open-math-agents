import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

/-!
# Frobenius' subgroup conjecture

The n solutions of x raised to n equals one form a subgroup when n is
positive and divides the order of the finite group. Nobuo Iiyori and
Hiroyoshi Yamaki announced the completed proof in 1991.
Source: https://www.openproblemgarden.org/op/subgroup_formed_by_elements_of_order_dividing_n
Formalization: @sturdy4days.
-/

namespace OMA.S_opg_subgroup_formed_by_elements_of_order_dividing_n

theorem main : ∀ (G : Type) [Group G] [Fintype G] (n : ℕ),
    0 < n → n ∣ Fintype.card G → {x : G | x ^ n = 1}.ncard = n →
    ∃ H : Subgroup G, ∀ x : G, x ∈ H ↔ x ^ n = 1 := by
  sorry

end OMA.S_opg_subgroup_formed_by_elements_of_order_dividing_n
