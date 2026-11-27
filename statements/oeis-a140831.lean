import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Consecutive numbers whose prime-power factors are out of order

Source: https://oeis.org/A140831 (Mike Jones's June 2022 conjecture,
OEIS Foundation, CC BY-SA 4.0). For a prime p dividing n, p^(n.factorization p)
is its maximal power dividing n. An inversion means that a smaller prime has a
larger prime-power component than a larger prime dividing the same n. Different
primes with positive exponents cannot give equal prime powers.
-/

namespace OMA.S_oeis_a140831

def inversion (n : ℕ) : Prop := 0 < n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p ∣ n ∧ q ∣ n ∧
    q^(n.factorization q) < p^(n.factorization p)

theorem main : {k : ℕ | inversion k ∧ inversion (k+1)}.Infinite := by
  sorry

end OMA.S_oeis_a140831
