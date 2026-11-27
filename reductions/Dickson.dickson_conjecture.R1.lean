import FormalConjectures.Wikipedia.Dickson

-- Reduction Dickson.dickson_conjecture.R1 of Dickson's conjecture
-- Credit: @marcusbuffett

/-!
# Dickson's conjecture: one linear form is Dirichlet's theorem, and the open rest

Dickson's conjecture says that finitely many linear forms `a_i n + b_i` with positive leading
coefficients, with no fixed prime divisor of their product, are simultaneously prime for
infinitely many `n`.

* `H1` (Dirichlet 1837): the conjecture for at most one form. For a single form `a n + b` the
  condition says `gcd(a, b) = 1`, and Dirichlet's theorem on primes in arithmetic progressions
  gives infinitely many primes `p ≡ b (mod a)`; each large one is a value of the form.
* `H2`: the conjecture for two or more forms. This is open (it contains the twin prime
  conjecture).
-/

namespace OMA.R_Dickson_dickson_conjecture_R1

open Polynomial

/-- At most one form: Dirichlet's theorem. -/
def H1 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) → SchinzelCondition fs →
    fs.card ≤ 1 → Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

/-- The open part: two or more forms. -/
def H2 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) → SchinzelCondition fs →
    2 ≤ fs.card → Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

theorem main : H1 → H2 → type_of% @Dickson.dickson_conjecture := by
  intro h1 h2 fs hfs hfs'
  by_cases hc : fs.card ≤ 1
  · exact h1 fs hfs hfs' hc
  · exact h2 fs hfs hfs' (by omega)

end OMA.R_Dickson_dickson_conjecture_R1
