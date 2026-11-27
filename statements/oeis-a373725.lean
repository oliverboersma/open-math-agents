import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Multiplicity

/-!
# Equal factorial multiplicities at neighboring integers

Sources: https://oeis.org/A373725 and https://oeis.org/A011776
(Amiram Eldar, OEIS Foundation, CC BY-SA 4.0).

For n > 1, A011776(n) is the largest e for which n^e divides n!.
A373725 lists the k where A011776(k) and A011776(k+1) agree.
-/

namespace OMA.S_oeis_a373725

noncomputable def a (n : ℕ) : ℕ := multiplicity n n.factorial

theorem main : ∀ p : ℕ, p.Prime → p ≠ 3 → (2*p-1).Prime →
    a (4*p^2-1) = a (4*p^2) := by
  sorry

end OMA.S_oeis_a373725
