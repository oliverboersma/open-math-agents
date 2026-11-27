import Mathlib

/-!
# Consecutive integers with opposite binary and balanced ternary digit sums

Thomas König defined OEIS A334765 in 2020 and conjectured that no four consecutive
integers occur in it. The first run of three begins with its 116th term, 32770.
Source: https://oeis.org/A334765 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.
-/

namespace OMA.S_oeis_a334765

/-- The balanced ternary last digit is n−3q ∈ {−1,0,1}, with q=⌊(n+1)/3⌋. -/
def balancedSum (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    let q := (n+1)/3
    (n : ℤ) - 3*(q : ℤ) + balancedSum q
termination_by n
decreasing_by omega

def digitMatch (n : ℕ) : Bool := decide (((Nat.digits 2 n).sum : ℤ) = -balancedSum n)

theorem main :
    (∀ n : ℕ, ¬ (∀ i : Fin 4, digitMatch (n+i.val) = true)) ∧
    (∀ i : Fin 3, digitMatch (32770+i.val) = true) ∧
    (∀ n : Fin 32770, ¬ (∀ i : Fin 3, digitMatch (n.val+i.val) = true)) ∧
    (List.range 32770).countP digitMatch = 115 := by
  sorry

end OMA.S_oeis_a334765
