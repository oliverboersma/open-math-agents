import Mathlib

/-!
# Primitive roots modulo primes related to Fibonacci numbers or Lucas numbers

Source: https://mathoverflow.net/questions/350730 (Zhi-Wei Sun, 2020). See also https://oeis.org/A331506.
Credit: @prasledi

The statement is the Conjecture of the post, parts (i) and (ii), as a conjunction.
(i) For every prime p there are Fibonacci numbers F k and F m with F k * F m < p whose product is a
primitive root modulo p. (ii) The same with Lucas numbers.
The indices start at 0 (F 0 = 0, L 0 = 2) and k = m is allowed, since the source does not ask for
distinct numbers. A primitive root modulo p is a residue that is a primitive (p - 1)-th root of
unity in ZMod p. The strong version of part (i) mentioned later in the post is not included.
-/

namespace OMA.S_mo_350730

/-- Lucas numbers: L 0 = 2, L 1 = 1, L (n + 2) = L (n + 1) + L n. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem main :
    (∀ p : ℕ, p.Prime → ∃ k m : ℕ, Nat.fib k * Nat.fib m < p ∧
      IsPrimitiveRoot ((Nat.fib k * Nat.fib m : ℕ) : ZMod p) (p - 1)) ∧
    (∀ p : ℕ, p.Prime → ∃ k m : ℕ, lucas k * lucas m < p ∧
      IsPrimitiveRoot ((lucas k * lucas m : ℕ) : ZMod p) (p - 1)) := by
  sorry

end OMA.S_mo_350730
