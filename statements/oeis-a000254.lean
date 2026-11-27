import Mathlib

/-!
# A000254: Unsigned Stirling numbers of first kind, s(n+1,2): a(n+1) = (n+1)*a(n) + n!.

Source: https://oeis.org/A000254
Credit: @ShoQo

Gary Detlefs' conjectures (Sep 11 2010), all reported true by Sela Fried (2025):
1. "It appears that, with the exception of n=4, a(n) mod n = 0 if n is composite and
   a(n) mod n = n-1 if n is prime."
2. "It appears that, for n >= 3, (a(n+1)^2 - a(n)^2) mod n^2 = 0 if n is composite and 4*n if
   n is prime."
3. "It appears that, for n >= 3, (a(n+1)^3 - a(n)^2) mod n = 0 if n is composite and n - 2 if
   n is prime."
4. "It appears that, for n >= 3, (a(n)^2 + a(n+1)^2) mod n = 0 if n is composite and = 2 if n
   is prime."

Formalization notes:
* Offset 0: a(0) = 0, a(n+1) = (n+1) a(n) + n! (data 0, 1, 3, 11, 50, 274, ...).
* In (1), n ranges over n >= 2 (1 is neither prime nor composite), n ≠ 4.
* In (2), for prime n the value is read as a congruence, a(n+1)^2 - a(n)^2 ≡ 4n (mod n^2):
  at n = 3 the literal residue is 3 = 12 - 9, since 4n = 12 exceeds n^2 = 9. For every prime
  n >= 5 this is the same as the residue being exactly 4n.
* All differences are of naturals with a(n)^2 ≤ a(n+1)^2 ≤ a(n+1)^3, so they are exact.
-/

namespace OMA.S_oeis_a000254

/-- a(0) = 0, a(n+1) = (n+1) a(n) + n!: the unsigned Stirling numbers s(n+1, 2). -/
def a : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (n + 1) * a n + n.factorial

theorem main :
    (∀ n : ℕ, 2 ≤ n → n ≠ 4 →
      (n.Prime → a n % n = n - 1) ∧ (¬ n.Prime → a n % n = 0)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (n.Prime → a (n + 1) ^ 2 - a n ^ 2 ≡ 4 * n [MOD n ^ 2]) ∧
      (¬ n.Prime → (a (n + 1) ^ 2 - a n ^ 2) % n ^ 2 = 0)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (n.Prime → (a (n + 1) ^ 3 - a n ^ 2) % n = n - 2) ∧
      (¬ n.Prime → (a (n + 1) ^ 3 - a n ^ 2) % n = 0)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (n.Prime → (a n ^ 2 + a (n + 1) ^ 2) % n = 2) ∧
      (¬ n.Prime → (a n ^ 2 + a (n + 1) ^ 2) % n = 0)) := by
  sorry

end OMA.S_oeis_a000254
