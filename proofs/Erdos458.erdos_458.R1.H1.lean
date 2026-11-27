import OMAReductions.R_Erdos458_erdos_458_R1
import Mathlib

-- Step Erdos458.erdos_458.R1.H1: hypothesis H1 of reduction Erdos458.erdos_458.R1
-- Credit: @ivillar

/-!
`log lcm(1..n)` is Chebyshev's `ψ n` (Mathlib's `Chebyshev.psi_eq_log_lcmUpto`), and `ψ` is the
summatory von Mangoldt function, so the difference is the sum over `(a, b]`.
-/
open Finset ArithmeticFunction

namespace F2E458

theorem log_lcm (n : ℕ) : Real.log (Erdos458.lcm_upto n : ℝ) = Chebyshev.psi n :=
  (Chebyshev.psi_eq_log_lcmUpto n).symm

theorem log_lcm_diff : ∀ a b : ℕ, a ≤ b →
    Real.log (Erdos458.lcm_upto b : ℝ) - Real.log (Erdos458.lcm_upto a : ℝ) =
      ∑ n ∈ Ioc a b, vonMangoldt n := by
  intro a b hab
  rw [log_lcm, log_lcm, Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

end F2E458

theorem OMA.solution : OMA.R_Erdos458_erdos_458_R1.H1 :=
  F2E458.log_lcm_diff
