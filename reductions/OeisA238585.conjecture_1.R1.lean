import FormalConjectures.OEIS.«238585»

/-!
# A238585, conjecture 1: the vanishing indices and the positive direction

`a n` counts the primes `p < n` for which `prime(p)^2 + (prime(n) - 1)^2` is prime, where
`prime(i)` is the `i`-th prime.  Conjecture 1 says

`0 < a n ↔ ¬ (n ∣ 6)`,

i.e. `a n` vanishes exactly on the divisors of `6`.

`H1` is the finite direction: on the divisors of `6` the count is zero.  This is a direct
computation of `a` on the (finitely many) divisors of `6`.

`H2` is the open direction: every positive `n` not dividing `6` has `a n > 0`. The
positivity hypothesis is essential, since `a 0 = 0`.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA238585_conjecture_1_R1

/-- The finite direction: the divisors of six have zero count. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∣ 6 → OeisA238585.a n = 0

/-- The open direction: a nonzero count happens only away from the divisors of six. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ¬ n ∣ 6 → 0 < OeisA238585.a n

theorem main : H1 → H2 → type_of% @OeisA238585.conjecture_1 := by
  intro h1 h2 n hn
  exact ⟨fun hpos hd => by rw [h1 n hd] at hpos; exact lt_irrefl 0 hpos, h2 n hn⟩

end OMA.R_OeisA238585_conjecture_1_R1
