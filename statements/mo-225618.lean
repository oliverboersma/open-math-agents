import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic

/-!
# Approximate stationarity for a mixture of permutation matrices

Source: https://mathoverflow.net/questions/225618
Credit: @zarnab222-dev

The question asks whether the expected total variation distance moved by a permutation
can be made uniformly small whenever the distance moved by the mixture is small.
The tolerance is independent of the state space, distribution and decomposition.
The weights below index all permutations, so their convex combination is precisely the
specified Birkhoff decomposition. The affirmative assertion is stated in epsilon-delta form.
-/

namespace OMA.S_mo_225618

variable {X : Type} [Fintype X]

def IsProb (v : X → ℝ) : Prop := (∀ x, 0 ≤ v x) ∧ ∑ x, v x = 1

noncomputable def tv (v w : X → ℝ) : ℝ := (∑ x, |v x - w x|) / 2

def push (p : Equiv.Perm X) (v : X → ℝ) (x : X) : ℝ := v (p.symm x)

noncomputable def mix [DecidableEq X] (weights : Equiv.Perm X → ℝ) (v : X → ℝ) (x : X) : ℝ :=
  ∑ p, weights p * push p v x

theorem main :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (weights : Equiv.Perm X → ℝ) (v : X → ℝ),
        IsProb weights → IsProb v → tv v (mix weights v) ≤ δ →
          ∑ p, weights p * tv v (push p v) ≤ η := by
  sorry

end OMA.S_mo_225618

