import Mathlib

/-!
# Are there infinitely many Giuga numbers?

Source: https://en.wikipedia.org/wiki/Giuga_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source says: "a **Giuga number** is a composite number `n` such that for each of its distinct
prime factors `p` we have `p ∣ (n / p - 1)`", and then asks "Are there infinitely many Giuga
numbers?"  (It is not known whether there are.)  So the proposition formalized below is
`{n : ℕ | IsGiuga n}.Infinite`, with the definition transcribed verbatim: `n` composite, and every
prime `p` dividing `n` satisfies `p ∣ n / p - 1`.

Note: "composite" is taken in its standard sense, `1 < n` and `n` not prime.  The source's
equivalent condition `p ^ 2 ∣ n - p` is not used, to avoid truncated subtraction; the definition
above is the one the source states first.  Sanity check: `30 = 2 * 3 * 5` is a Giuga number,
since `30 / 2 - 1 = 14 = 2 * 7`, `30 / 3 - 1 = 9 = 3 ^ 2` and `30 / 5 - 1 = 5`.
-/

namespace OMA.S_wp_are_there_infinitely_many_giuga_numbers

-- definitions the statement needs (no sorry, no axiom)

/-- A natural number is **composite** when it is greater than one and not prime. -/
def Composite (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime

/-- `n` is a **Giuga number**: a composite number such that each of its distinct prime factors `p`
satisfies `p ∣ n / p - 1`. -/
def IsGiuga (n : ℕ) : Prop :=
  Composite n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ n / p - 1

/-- Are there infinitely many Giuga numbers? -/
theorem main : {n : ℕ | IsGiuga n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_giuga_numbers
