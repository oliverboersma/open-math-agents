import FormalConjectures.OEIS.«262813»

/-!
Multiplying by eight and adding one turns a square plus a triangular number
into the quadratic form u² + 2v². Modulo eight, a value congruent to one
forces u to be odd and v to be even. A nonsquare residual excludes u = 1,
which would give a zero triangular term.
-/

namespace OMA.R_OeisA262813_conjecture_1_R1

/-- A norm representation with a positive triangular term proves positivity. -/
def H1 : Prop :=
  ∀ n x u v : ℕ, (3 ≤ u ∨ ¬ IsSquare (n - x ^ 3)) →
    8 * n + 1 = 8 * x ^ 3 + u ^ 2 + 2 * v ^ 2 → 0 < OeisA262813.a n

/-- The initial range can be checked using explicit norm witnesses. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → n < 90 →
    ∃ x u v : ℕ, 3 ≤ u ∧ 8 * n + 1 = 8 * x ^ 3 + u ^ 2 + 2 * v ^ 2

/-- The open norm existence statement, with a nonsquare residual. -/
def H3 : Prop :=
  ∀ n : ℕ, 90 ≤ n →
    ∃ x u v : ℕ, ¬ IsSquare (n - x ^ 3) ∧
      8 * n + 1 = 8 * x ^ 3 + u ^ 2 + 2 * v ^ 2

section Proof

theorem main : H1 → H2 → H3 → type_of% @OeisA262813.conjecture_1 := by
  intro norm small large n hn
  by_cases h : n < 90
  · obtain ⟨x, u, v, hu, heq⟩ := small n hn h
    exact norm n x u v (Or.inl hu) heq
  · obtain ⟨x, u, v, hu, heq⟩ := large n (by omega)
    exact norm n x u v (Or.inr hu) heq

end Proof

end OMA.R_OeisA262813_conjecture_1_R1
