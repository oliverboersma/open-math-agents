import Mathlib

/-!
# OEIS A057923

Let a(0)=0 and a(1)=2. Each next term is the least nonnegative integer
that makes the bitwise OR of the new adjacent pair exceed that of the
previous adjacent pair. In 2017 Robert Israel conjectured strict
increase at distance two for every index.

Source: https://oeis.org/A057923
-/

namespace OMA.S_oeis_a057923

def candidate (y t : ℕ) : ∃ z : ℕ, t < (y ||| z) :=
  ⟨t+1, Nat.lt_of_lt_of_le (Nat.lt_succ_self t) Nat.right_le_or⟩

noncomputable def pick (y t : ℕ) := Nat.find (candidate y t)

noncomputable def pair : ℕ → ℕ × ℕ
  | 0 => (0,2)
  | n+1 => let p := pair n; (p.2, pick p.2 (p.1 ||| p.2))

noncomputable def term (n : ℕ) : ℕ := (pair n).1

theorem main : ∀ n : ℕ, term n < term (n+2) := by
  sorry

end OMA.S_oeis_a057923
