import FormalConjectures.OEIS.«280831»

-- Reduction OeisA280831.conjecture.R1 of Zhi-Wei Sun's 1680-Conjecture (A280831)
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
Two observations split the 1680-conjecture into a classical theorem and its genuinely open core.
* If n = a^2 + b^2 + c^2, take x = a and y = 0: then x^4 + 1680 y^3 z = (a^2)^2 is a square.
* Doubling every coordinate multiplies x^4 + 1680 y^3 z by 16, so A n implies A (4 n).
By the Gauss-Legendre three-square theorem every n with 4 not dividing n and n mod 8 not 7 is a
sum of three squares (H1, a known theorem not yet in Mathlib). Hence the conjecture holds as soon
as it holds for every n congruent to 7 mod 8 (H2), which is exactly where Sun's condition bites.
-/

namespace OMA.R_OeisA280831_conjecture_R1

open OeisA280831

/-- The part of the Gauss-Legendre three-square theorem used here. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 4 ≠ 0 → n % 8 ≠ 7 → ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2

/-- The open core: the 1680-conjecture for every n congruent to 7 modulo 8. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 8 = 7 → A n

lemma zero_rep : A 0 :=
  ⟨0, 0, 0, 0, by norm_num, 0, by norm_num⟩

lemma of_three_squares {n a b c : ℕ} (h : n = a ^ 2 + b ^ 2 + c ^ 2) : A n :=
  ⟨a, 0, b, c, by rw [h]; ring, a ^ 2, by ring⟩

lemma four_mul {n : ℕ} (h : A n) : A (4 * n) := by
  obtain ⟨x, y, z, w, heq, r, hr⟩ := h
  refine ⟨2 * x, 2 * y, 2 * z, 2 * w, ?_, 4 * r, ?_⟩
  · rw [heq]
    ring
  · calc
      (2 * x) ^ 4 + 1680 * (2 * y) ^ 3 * (2 * z) = 16 * (x ^ 4 + 1680 * y ^ 3 * z) := by ring
      _ = 4 * r * (4 * r) := by rw [hr]; ring

theorem main : H1 → H2 → type_of% @OeisA280831.conjecture := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      exact zero_rep
    by_cases h4 : n % 4 = 0
    · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h4
      exact four_mul (ih m (by omega))
    by_cases h7 : n % 8 = 7
    · exact h2 n h7
    · obtain ⟨a, b, c, h⟩ := h1 n h4 h7
      exact of_three_squares h

end OMA.R_OeisA280831_conjecture_R1
