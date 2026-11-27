import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Data.ZMod.Basic

/-!
# OEIS A395839

The sequence is defined by the coefficients of 10 C(X)² - C(X),
where C is the ordinary generating series of the Catalan numbers.
The OEIS entry conjectures the parity of every coefficient and all
three residue classes of coefficients modulo three.

Source: https://oeis.org/A395839
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a395839

noncomputable def catalanZ : PowerSeries ℤ :=
  PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries

noncomputable def series : PowerSeries ℤ := 10 * catalanZ ^ 2 - catalanZ

theorem main :
    (∀ n : ℕ, ((series.coeff n : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k) ∧
    (∀ n : ℕ,
      ((series.coeff (3 * n + 1) : ℤ) : ZMod 3) = (catalan n : ZMod 3) ∧
      ((series.coeff (3 * n) : ℤ) : ZMod 3) = 0 ∧
      ((series.coeff (3 * n + 2) : ℤ) : ZMod 3) = 0) := by
  sorry

end OMA.S_oeis_a395839
