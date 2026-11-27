import Mathlib

/-!
# A variation of Fermat's little theorem in the form a^(n-d) ≡ a (mod n)
Source: https://math.stackexchange.com/questions/948616

For a fixed d, the asker calls n valid when n ≥ d + 1 and a^(n-d) ≡ a (mod n)
for every integer a. For d = 0 these are 1, the primes and the Carmichael
numbers; for d = 1 this is OEIS A216090.

Translation choices:
* The question allows any integer d, but the sequences discussed are for d ≥ 0,
  so we take d : ℕ. The exponent n - d is then a natural number since n ≥ d + 1.
* The conjecture says that if d + 1 is squarefree then many prime multiples of
  d + 1 are valid, while if d + 1 is not squarefree then no multiple of d + 1
  other than possibly d + 1 itself is valid. We read many as infinitely many,
  and a prime multiple of d + 1 as a number p * (d + 1) with p prime.
* The final sentence of the conjecture, that valid n not divisible by d + 1 are
  much less abundant, is a heuristic with no precise mathematical content, so it
  is not formalized.
-/

namespace OMA.S_mse_948616

/-- n is valid for d when n ≥ d + 1 and a^(n-d) ≡ a (mod n) for every integer a. -/
def Valid (d n : ℕ) : Prop := d + 1 ≤ n ∧ ∀ a : ℤ, a ^ (n - d) ≡ a [ZMOD n]

theorem main : ∀ d : ℕ,
    (Squarefree (d + 1) → {p : ℕ | p.Prime ∧ Valid d (p * (d + 1))}.Infinite) ∧
    (¬ Squarefree (d + 1) → ∀ n, d + 1 ∣ n → n ≠ d + 1 → ¬ Valid d n) := by
  sorry

end OMA.S_mse_948616
