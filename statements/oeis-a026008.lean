import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

/-!
# The five-term recurrence for the Catalan sequence A026008

Ralf Stephan's two binomial formulas on the OEIS entry give the tabulated
sequence 1, 1, 2, 3, 5, 9, 14, … . We write the binomials as factorial
quotients in the rationals. The table, both formulas and the Mathematica
program agree. The short name refers to T(n,⌊n/2⌋) of A008315, which gives
1 at n=2 where the A026008 table gives 2. Here a means the tabulated A026008.

Mathar's recurrence starts at n=4, the first index having four predecessors.
Writing n=t+4 keeps all terms within the published offset zero.

Source: https://oeis.org/A026008
Triangle: https://oeis.org/A008315
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a026008

def evenTerm (k : ℕ) : ℚ :=
  ((2*k+2).factorial : ℚ) / ((k+1).factorial * ((k+2).factorial : ℚ))

def oddTerm (k : ℕ) : ℚ :=
  3 * ((2*k+2).factorial : ℚ) / (k.factorial * ((k+3).factorial : ℚ))

def a (n : ℕ) : ℚ :=
  if n % 2 = 0 then evenTerm (n/2) else oddTerm (n/2)

theorem main : ∀ t : ℕ,
    ((t:ℚ)+9)*a (t+4) + ((t:ℚ)+7)*a (t+3) -
      (5*(t:ℚ)+29)*a (t+2) - 4*((t:ℚ)+4)*a (t+1) +
      4*((t:ℚ)+2)*a t = 0 := by
  sorry

end OMA.S_oeis_a026008
