import Mathlib

/-!
Source: https://oeis.org/A369275
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A369/A369275.seq
Credit: @Heart-galaxy

The sequence is the set of nonnegative integers starting a strictly increasing
five-point block of sine values at unit spacing. Mathar conjectured that two
consecutive integers never both belong, equivalently that no six-point block
is strictly increasing. Greathouse records the conjecture as true on December
10, 2024. Only that imported conjecture is stated; the separate empirical
modular patterns in the entry were explicitly refuted there.
-/

namespace OMA.S_oeis_a369275

def qualifies (k : ℕ) : Prop :=
  Real.sin (k:ℝ)<Real.sin ((k:ℝ)+1) ∧
  Real.sin ((k:ℝ)+1)<Real.sin ((k:ℝ)+2) ∧
  Real.sin ((k:ℝ)+2)<Real.sin ((k:ℝ)+3) ∧
  Real.sin ((k:ℝ)+3)<Real.sin ((k:ℝ)+4)

theorem main : ∀ k : ℕ, qualifies k → ¬qualifies (k+1) := by
  sorry

end OMA.S_oeis_a369275
