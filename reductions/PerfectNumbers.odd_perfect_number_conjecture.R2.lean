import FormalConjectures.Wikipedia.PerfectNumbers

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R2 of the odd perfect number conjecture
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers: Sylvester's theorem on 105, and the open rest

The conjecture says that every perfect number is even.

* `H1` (Sylvester, Sur l'impossibilité de l'existence d'un nombre parfait impair qui ne contient
  pas au moins 5 diviseurs premiers distincts, C. R. Acad. Sci. Paris 106 (1888)): no odd perfect
  number is divisible by `105 = 3 * 5 * 7`. In an odd perfect `n` the exponents of `3` and `7`
  are even, because `4 ∣ σ(p^a)` for odd `a` and `p ≡ 3 (mod 4)`; so `3^2 * 5 * 7^2` divides `n`
  with these exact minimal exponents, and `σ(n) / n ≥ (13/9)(6/5)(57/49) > 2`.
* `H2`: every perfect number not divisible by `105` is even. This is the open problem and stays
  open.
-/

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2

/-- Sylvester: an odd perfect number is not divisible by `105`. -/
def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → ¬ 105 ∣ n

/-- The open part: perfect numbers not divisible by `105` are even. -/
def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → ¬ 105 ∣ n → Even n

theorem main : H1 → H2 → type_of% @PerfectNumbers.odd_perfect_number_conjecture := by
  intro h1 h2 n hn
  by_contra hne
  have hodd : Odd n := Nat.not_even_iff_odd.mp hne
  exact hne (h2 n hn (h1 n hn hodd))

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2
