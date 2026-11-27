import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Ring.Parity

/-!
# MacEachen conjecture

Prime indices select the distinct primorials 2, 6, 30, and so on.
A singleton selects one primorial. The empty product gives the first term
of OEIS A129912, which is 1.

Source: https://www.openproblemgarden.org/op/maceachen_conjecture
Author's formulation: https://oeis.org/A129912
Credit: @Hennyrick
-/

namespace OMA.S_opg_maceachen_conjecture

theorem main : ∀ p : ℕ, p.Prime → Odd p →
    ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧
      (let d := Nat.dist p (S.prod primorial)
       d = 1 ∨ (d.Prime ∧ d < p)) := by
  sorry

end OMA.S_opg_maceachen_conjecture
