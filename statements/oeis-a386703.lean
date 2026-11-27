import Mathlib

/-!
# OEIS A386703

Source: https://oeis.org/A386703 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A386703(n), for `n ≥ 1`, is the residue of `p(n)` modulo `q(n)` in the interval
`(-q(n)/2, q(n)/2]`, where `p(n) = A000041(n)` is the number of partitions of `n` and
`q(n) = A000009(n)` is the number of partitions of `n` into distinct parts.
Data (from n = 1): 0, 0, 1, 1, 1, -1, 0, -2, -2, 2, -4, 2, -7, 3, -13, 7, ...

Conjecture (from the sequence entry): |a(n)| > 1 for all n > 7.

The residue is the unique integer `r` with `r ≡ p(n) (mod q(n))` and `-q(n) < 2 r ≤ q(n)`;
we state the conjecture for every such `r`. Partitions are Mathlib's `Nat.Partition n`, and a
partition has distinct parts when its multiset of parts has no duplicates.
-/

namespace OMA.S_oeis_a386703

/-- `p n`: the number of partitions of `n` (A000041). -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `q n`: the number of partitions of `n` into distinct parts (A000009). -/
def q (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun π => π.parts.Nodup).card

/-- `r` is the residue of `p n` modulo `q n` in `(-q n / 2, q n / 2]`. -/
def IsCenteredResidue (n : ℕ) (r : ℤ) : Prop :=
  r ≡ (p n : ℤ) [ZMOD (q n : ℤ)] ∧ -(q n : ℤ) < 2 * r ∧ 2 * r ≤ (q n : ℤ)

theorem main : ∀ n : ℕ, 7 < n → ∀ r : ℤ, IsCenteredResidue n r → 1 < |r| := by
  sorry

end OMA.S_oeis_a386703
