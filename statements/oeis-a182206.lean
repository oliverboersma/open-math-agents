import Mathlib

/-!
# A182206: Carmichael numbers of the form C = 37*73*(18n+91)

Source: https://oeis.org/A182206
Credit: @xor2k

Formalizes the OEIS A182206 conjecture: Any Carmichael number C divisible by 37 and 73 can be
written as C = 37*73*(18n+91), where n is natural.

Conventions: Carmichael numbers are taken with the defining property of OEIS A002997:
composite numbers `m` (that is, `1 < m` and `m` not prime) such that `b^(m-1) ≡ 1 (mod m)`
for every `b` coprime to `m`. The bases `b` range over `ℕ` (every residue class has a
natural representative), and `m - 1` is ordinary subtraction since `m > 1`. Korselt's
criterion is not built into the definition. The integer `n` in `18n+91` is a natural
number `n ≥ 0`, which is the strongest reading.
-/

namespace OMA.S_oeis_a182206

/-- Carmichael numbers: composite `m` with `b^(m-1) ≡ 1 (mod m)` for all `b` coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, b.Coprime m → b ^ (m - 1) ≡ 1 [MOD m]

/-- Every Carmichael number divisible by `37` and `73` equals `37 * 73 * (18 * n + 91)` for
some natural number `n`. -/
theorem main :
    ∀ C : ℕ, IsCarmichael C → 37 ∣ C → 73 ∣ C → ∃ n : ℕ, C = 37 * 73 * (18 * n + 91) := by
  sorry

end OMA.S_oeis_a182206
