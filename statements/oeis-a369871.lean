import Mathlib

/-!
# A369871: a(n) = least prime factor of A024411(n).

Source: https://oeis.org/A369871
Credit: @bnb9001

A024411 lists, in increasing order, the numbers that are the short leg of more than one primitive
Pythagorean triangle (20, 28, 33, 36, ...). A primitive Pythagorean triangle with short leg `m`
is a triple `(m, b, c)` with `0 < m < b`, `m^2 + b^2 = c^2` and `gcd(m, b) = 1`; two triangles
with the same short leg are different when their other legs differ. Both sequences have offset 1,
and the least prime factor is `Nat.minFac`.

Conjecture: every prime occurs infinitely many times. Aditya P Bhattad notes that the conjecture
is true.
-/

namespace OMA.S_oeis_a369871

/-- `(m, b, c)` is a primitive Pythagorean triangle with short leg `m`. -/
def IsPPT (m b c : ℕ) : Prop := 0 < m ∧ m < b ∧ m ^ 2 + b ^ 2 = c ^ 2 ∧ Nat.Coprime m b

/-- `m` is the short leg of more than one primitive Pythagorean triangle (A024411). -/
def MultiShortLeg (m : ℕ) : Prop :=
  ∃ b₁ c₁ b₂ c₂ : ℕ, IsPPT m b₁ c₁ ∧ IsPPT m b₂ c₂ ∧ b₁ ≠ b₂

/-- A369871: the least prime factor of the `n`-th term (1-indexed) of A024411. -/
noncomputable def a (n : ℕ) : ℕ := Nat.minFac (Nat.nth MultiShortLeg (n - 1))

/-- Every prime `p` equals `a n` for infinitely many `n ≥ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → {n : ℕ | 1 ≤ n ∧ a n = p}.Infinite := by
  sorry

end OMA.S_oeis_a369871
