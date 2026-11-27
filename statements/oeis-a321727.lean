import Mathlib

/-!
# A321727: Number of permutations f of {1,...,n} such that prime(k) + prime(f(k)) + 1 is prime for every k = 1,...,n.

Source: https://oeis.org/A321727
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): a(n) > 0 for all n > 0.

Translation notes.
* {1, ..., n} is modelled by Fin n with k standing for k + 1, and prime(k + 1), the
  (k + 1)-th prime with prime(1) = 2, is Nat.nth Nat.Prime k (0-indexed).
* a(n) > 0 means some permutation f of {1, ..., n} has prime(k) + prime(f(k)) + 1 prime for
  every k.
* This reading reproduces the listed data a(1..8) = 1, 1, 1, 2, 6, 10, 31, 76 (checked by
  computer).
-/

namespace OMA.S_oeis_a321727

theorem main : ∀ n : ℕ, 0 < n → ∃ f : Equiv.Perm (Fin n),
    ∀ k : Fin n, (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (f k) + 1).Prime := by
  sorry

end OMA.S_oeis_a321727
