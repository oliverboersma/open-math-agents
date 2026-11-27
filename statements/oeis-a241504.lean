import Mathlib

/-!
# A241504: Primitive roots modulo prime(n) below prime(n) that are partition numbers

Source: https://oeis.org/A241504
Credit: @niclorusso

a(n) = |{0 < g < prime(n): g is not only a primitive root modulo prime(n) but also a partition
number given by A000041}|.

Conjecture (Zhi-Wei Sun, in the comments of A241504): (i) a(n) > 0 for all n > 0. In other words,
any prime p has a primitive root g < p which is also a partition number.

(Only part (i) of the conjecture is formalized here.)

Conventions:
* The partition numbers are p(m) = the number of partitions of m (A000041), here
  `Fintype.card (Nat.Partition m)`.
* g is a primitive root modulo the prime p when the class of g in `ZMod p` has multiplicative order
  p - 1: `IsPrimitiveRoot (g : ZMod p) (p - 1)`.
-/

namespace OMA.S_oeis_a241504

/-- `x` is a partition number: `x = p(m)` for some `m`. -/
def IsPartitionNumber (x : ℕ) : Prop :=
  ∃ m : ℕ, Fintype.card (Nat.Partition m) = x

/-- Sun's conjecture (i) on A241504: every prime `p` has a primitive root `0 < g < p` that is a
partition number. -/
theorem main : ∀ p : ℕ, p.Prime →
    ∃ g : ℕ, 0 < g ∧ g < p ∧ IsPrimitiveRoot (g : ZMod p) (p - 1) ∧ IsPartitionNumber g := by
  sorry

end OMA.S_oeis_a241504
