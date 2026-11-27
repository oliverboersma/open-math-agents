import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
# A composite number whose square is in A231558

Sources: https://oeis.org/A231978 and https://oeis.org/A231558
(Vladimir Shevelev and Peter J. C. Moses, OEIS Foundation, CC BY-SA 4.0).

A number is odious when its binary digits contain an odd number of ones.
A231558 consists of the odd composite numbers n for which n itself and
n+d, n*d, n/d are odious for every positive divisor d. The terms of
A231978 are the numbers whose squares meet that condition.
-/

namespace OMA.S_oeis_a231978

def odious (n : ℕ) : Prop := ((Nat.digits 2 n).sum % 2) = 1

def composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

def inA231558 (n : ℕ) : Prop :=
  n % 2 = 1 ∧ composite n ∧ odious n ∧
    ∀ d : ℕ, 0 < d → d ∣ n → odious (n+d) ∧ odious (n*d) ∧ odious (n/d)

theorem main : ∃ m : ℕ, composite m ∧ inA231558 (m^2) := by
  sorry

end OMA.S_oeis_a231978
