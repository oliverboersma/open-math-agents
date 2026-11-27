import Mathlib

/-!
# A261387: Number of ways to write n = k + m with 0 < k < m < n such that prime(k) is a primitive root modulo prime(m) and also prime(m) is a primitive root modulo prime(k).

Source: https://oeis.org/A261387
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261387):
(i) `a(n) > 0` except for `n = 1, 2, 8`.
(ii) Any positive rational number `r` not equal to 1 can be written as `m/n`, where `m` and `n` are
positive integers such that `prime(m)` is a primitive root modulo `prime(n)` and also `prime(n)` is
a primitive root modulo `prime(m)`.

Formalization notes:
* `prime i` is the `i`-th prime with `prime 1 = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`.
* "`g` is a primitive root modulo the prime `q`" is `IsPrimitiveRoot (g : ZMod q) (q - 1)`.
* Part (i) is stated as an equivalence for every `n`.
* With these definitions the number of representations for `n = 1, ..., 20` is 0, 0, 1, 1, 1, 1,
  2, 0, 2, 1, 3, 3, 1, 1, 2, 1, 2, 7, 4, 2 (data of A261387).
-/

namespace OMA.S_oeis_a261387

/-- The `i`-th prime, `prime 1 = 2`. -/
noncomputable def prime (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- `prime a` and `prime b` are primitive roots modulo each other. -/
def MutualPrimitiveRoots (a b : ℕ) : Prop :=
  IsPrimitiveRoot ((prime a : ℕ) : ZMod (prime b)) (prime b - 1) ∧
    IsPrimitiveRoot ((prime b : ℕ) : ZMod (prime a)) (prime a - 1)

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, (∃ k m : ℕ, 0 < k ∧ k < m ∧ k + m = n ∧ MutualPrimitiveRoots k m) ↔
        n ∉ ({1, 2, 8} : Finset ℕ)) ∧
      ∀ r : ℚ, 0 < r → r ≠ 1 →
        ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ r = (m : ℚ) / n ∧ MutualPrimitiveRoots m n := by
  sorry

end OMA.S_oeis_a261387
