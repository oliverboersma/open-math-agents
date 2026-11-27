import FormalConjectures.Paper.PartitionParity
import Mathlib

/-! Zheng's lower bound of order sqrt X for the number of n ≤ X with p(n) odd, from its
explicit form. Ono and Swaminathan, Appendix A, Corollary 2 (Zheng), gives
liminf N_odd(X) / sqrt X ≥ 243 / (64 sqrt 6 pi^5); this is the catalogue's
PartitionParity.zheng.liminf. A positive lower bound for the liminf of f(X) / sqrt X in the
extended reals gives sqrt X = O(f), which is a statement about real functions only. -/

namespace OMA.R_PartitionParity_zheng_odd_R1
open Filter Asymptotics

/-- Zheng's explicit bound for the liminf of N_odd(X) / sqrt X. -/
def H1 : Prop :=
  ((243 / (64 * Real.sqrt 6 * Real.pi ^ 5) : ℝ) : EReal) ≤
    liminf (fun X : ℝ ↦
      ((({n : ℕ | (n : ℝ) ≤ X ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ) / Real.sqrt X : ℝ) :
        EReal)) atTop

/-- A positive lower bound for liminf f(X) / sqrt X gives sqrt X = O(f). -/
def H2 : Prop := ∀ (f : ℝ → ℝ) (c : ℝ), 0 < c →
  ((c : ℝ) : EReal) ≤ liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) atTop →
    (fun X : ℝ ↦ Real.sqrt X) =O[atTop] f

theorem main : H1 → H2 → type_of% @PartitionParity.zheng.odd := by
  intro h1 h2
  exact h2 _ _ (by positivity) h1

end OMA.R_PartitionParity_zheng_odd_R1
