import Mathlib.Data.Nat.Choose.Basic

/-!
# The recurrence for the diagonal of A059836

The OEIS offset is one, and the entry gives a(j+1) as j! times the central
binomial coefficient in row j. This is recorded below as diagonal j.
Setting n=t+3 in the printed recurrence includes the first admissible index,
where a(n-2)=a(1). The zero-offset interpretation can be checked separately.

Source: https://oeis.org/A059837 (R. J. Mathar's conjecture)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a059837

def diagonal (j : ℕ) : ℤ := (j.factorial : ℤ)*(j.choose (j/2) : ℤ)

theorem main : ∀ t : ℕ, let n : ℤ := (t : ℤ)+3;
    (n+1)*diagonal (t+2) - 2*n*diagonal (t+1) - 4*n*(n-1)^2*diagonal t = 0 := by
  sorry

end OMA.S_oeis_a059837
