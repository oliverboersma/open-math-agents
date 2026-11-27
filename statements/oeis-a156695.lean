import Mathlib

/-!
# A156695: Odd numbers that are not of the form p + 2^a + 2^b, a, b > 0, p prime.

Source: https://oeis.org/A156695
Credit: @mbilenko03

Conjecture (from the entry, Bill McEachen): all members of this sequence greater than 5 are
divisible by `255 = 3 * 5 * 17`.

Conventions:
- A member is an odd natural number `n` with no representation `n = p + 2^a + 2^b` where `p` is
  prime and `a, b > 0` are integers (`a = b` is allowed, as in the entry's definition, which puts
  no other condition on `a` and `b`). The first terms are 1, 3, 5, 6495105, ….
-/

namespace OMA.S_oeis_a156695

theorem main :
    ∀ n : ℕ, Odd n → 5 < n →
      (¬ ∃ p a b : ℕ, p.Prime ∧ 0 < a ∧ 0 < b ∧ n = p + 2 ^ a + 2 ^ b) → 255 ∣ n := by
  sorry

end OMA.S_oeis_a156695
