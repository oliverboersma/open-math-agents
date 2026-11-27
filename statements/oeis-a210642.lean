import Mathlib

/-!
# A210642: a(n) = least integer m > 1 such that k! == n! (mod m) for no 0 < k < n

Source: https://oeis.org/A210642
Credit: @niclorusso

Conjecture (in the comments of A210642): a(n) is a prime not exceeding 2n with the only exceptions
a(4)=4 and a(6)=9.

Conventions:
* The sequence has offset 1: a(n) is the least m > 1 such that k! and n! are incongruent modulo m
  for every 0 < k < n. Such m exist (any m > n!), so the infimum `sInf` is attained.
* The conjecture is stated as: for every n >= 1 other than 4 and 6, a(n) is prime and a(n) <= 2n;
  and a(4) = 4, a(6) = 9.
-/

namespace OMA.S_oeis_a210642

/-- A210642: the least `m > 1` such that `k! ≢ n! (mod m)` for all `0 < k < n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD m])}

/-- The conjecture on A210642. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ≠ 4 → n ≠ 6 → (a n).Prime ∧ a n ≤ 2 * n) ∧ a 4 = 4 ∧ a 6 = 9 := by
  sorry

end OMA.S_oeis_a210642
