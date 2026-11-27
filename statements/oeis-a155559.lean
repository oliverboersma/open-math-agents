import Mathlib

/-!
# A155559: a(n) = 2*A131577(n)

Source: https://oeis.org/A155559
Credit: @xor2k

Formalizes the OEIS A155559 conjecture: a(n) = A090129(n+3)-A090129(n+2).

Conventions:
* A155559 has offset 0, so the statement is for all `n : ℕ`;
* A131577 (offset 0) is zero followed by powers of 2: `A131577(0) = 0`, `A131577(n) = 2^(n-1)`
  for `n ≥ 1` (equivalently `(2^n - 0^n)/2`);
* A090129(n) (offset 1) is the smallest exponent `k` such that `2^n` divides `3^k - 1`, i.e.
  the multiplicative order of `3` modulo `2^n`; it is `orderOf (3 : ZMod (2 ^ n))`, which is
  the least `k > 0` with `3^k = 1` in `ZMod (2^n)` (this exists as `3` is a unit mod `2^n`);
  only the arguments `n + 2, n + 3 ≥ 2` occur;
* the subtraction is natural subtraction; it does not truncate since A090129 is
  nondecreasing.
-/

namespace OMA.S_oeis_a155559

/-- A131577: `0, 1, 2, 4, 8, ...`. -/
def A131577 (n : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - 1)

/-- A155559: `a(n) = 2*A131577(n)`. -/
def a (n : ℕ) : ℕ :=
  2 * A131577 n

/-- A090129: the multiplicative order of `3` modulo `2^n`. -/
noncomputable def A090129 (n : ℕ) : ℕ :=
  orderOf (3 : ZMod (2 ^ n))

/-- For every `n ≥ 0`, `a(n) = A090129(n+3) - A090129(n+2)`. -/
theorem main :
    ∀ n : ℕ, a n = A090129 (n + 3) - A090129 (n + 2) := by
  sorry

end OMA.S_oeis_a155559
