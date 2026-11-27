import Mathlib.Analysis.Real.Sqrt

/-!
# The slope of the nested recurrence with denominator 4

The bounded recursion constructs the source sequence at every natural
index. The function cf computes successive two-level truncations of
the periodic continued fraction in the conjecture, starting at zero.

Source: https://oeis.org/A366870
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a366870

def bounded : (n : ℕ) → Fin (n+1)
  | 0 => 0
  | n+1 =>
    let previous := bounded n
    let j := previous.val / 4
    let earlier := bounded j
    ⟨n+1 - earlier.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
termination_by n => n
decreasing_by
  all_goals first
    | exact Nat.lt_succ_self _
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) (Fin.isLt _)

def value (n : ℕ) : ℕ := (bounded n).val

noncomputable def cf : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 / (1 + 1 / (4 + cf n))

noncomputable def slope : ℝ := 2 * (Real.sqrt 2 - 1)

open Filter Topology

theorem main : Tendsto cf atTop (𝓝 slope) ∧
    Tendsto (fun n : ℕ => (value n : ℝ) / (n : ℝ)) atTop (𝓝 slope) := by
  sorry

end OMA.S_oeis_a366870
