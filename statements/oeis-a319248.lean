import Mathlib

/-!
# A319248: Lesser of the pairs of twin primes in A001122.

Source: https://oeis.org/A319248
Credit: @darealpandaboi

Conjecture: there are infinitely many pairs of twin primes and infinitely many primes with
primitive root 2 are two famous unsolved problems, so a stronger conjecture implying both of
them is that this sequence is infinite.

Translation notes.
* A001122 is the set of primes q such that 2 is a primitive root modulo q, i.e. the residue
  of 2 has multiplicative order q - 1: IsPrimitiveRoot (2 : ZMod q) (q - 1).
* p is a term when p and p + 2 are both primes in A001122.
* This reading reproduces the listed data: 3, 11, 59, 179, 347, 419, 659, 827, 1451, 1619,
  1667, 2027, ... (checked by computer).
-/

namespace OMA.S_oeis_a319248

/-- q is in A001122: q is prime and 2 is a primitive root modulo q. -/
def InA001122 (q : ℕ) : Prop := q.Prime ∧ IsPrimitiveRoot (2 : ZMod q) (q - 1)

theorem main : {p : ℕ | InA001122 p ∧ InA001122 (p + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a319248
