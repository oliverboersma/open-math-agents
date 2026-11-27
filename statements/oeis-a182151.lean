import Mathlib

/-!
# A182151: Carmichael numbers divisible by 31

Source: https://oeis.org/A182151
Credit: @xor2k

Formalizes the OEIS A182151 conjecture: Any Carmichael number C divisible by 31 can be written
in one of the following three forms: C = 2790n+31; C = 2790n+31^2 or C = 2790n+31*61, where n
is natural.

Conventions: Carmichael numbers are taken with the defining property of OEIS A002997:
composite numbers `m` (that is, `1 < m` and `m` not prime) such that `b^(m-1) ≡ 1 (mod m)`
for every `b` coprime to `m`. The bases `b` range over `ℕ` (every residue class has a
natural representative), and `m - 1` is ordinary subtraction since `m > 1`. Korselt's
criterion is not built into the definition. The `n` in the three forms is a natural number
`n ≥ 0` (the same existential `n` for the disjunction of the three forms).
-/

namespace OMA.S_oeis_a182151

/-- Carmichael numbers: composite `m` with `b^(m-1) ≡ 1 (mod m)` for all `b` coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, b.Coprime m → b ^ (m - 1) ≡ 1 [MOD m]

/-- Every Carmichael number divisible by `31` is of the form `2790n + 31`, `2790n + 31^2` or
`2790n + 31*61` for some natural number `n`. -/
theorem main :
    ∀ C : ℕ, IsCarmichael C → 31 ∣ C →
      ∃ n : ℕ, C = 2790 * n + 31 ∨ C = 2790 * n + 31 ^ 2 ∨ C = 2790 * n + 31 * 61 := by
  sorry

end OMA.S_oeis_a182151
