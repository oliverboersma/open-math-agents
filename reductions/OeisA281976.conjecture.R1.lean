import FormalConjectures.OEIS.«281976»

-- Reduction OeisA281976.conjecture.R1 of Zhi-Wei Sun's Conjecture (A281976)
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
Scaling: if n = a^2 + b^2 + c^2 + d^2 with a and a + 24 b squares and c ≤ d, then multiplying
every coordinate by k^2 represents k^4 n with the same properties. Hence the conjecture only
has to be proved for fourth-power-free n, which we split by parity: H1 covers the odd
fourth-power-free n, H2 the even ones (those with 2-adic valuation 1, 2 or 3).
-/

namespace OMA.R_OeisA281976_conjecture_R1

open OeisA281976

/-- Sun's representation exists for every odd fourth-power-free `n`. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 2 = 1 → (∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ n) → A n

/-- Sun's representation exists for every even fourth-power-free `n`. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 2 = 0 → (∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ n) → A n

lemma zero_rep : A 0 :=
  ⟨0, 0, 0, 0, by norm_num, le_rfl, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

lemma mul_fourth_of {n : ℕ} (h : A n) (k : ℕ) : A (k ^ 4 * n) := by
  obtain ⟨a, b, c, d, heq, hcd, ⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  refine ⟨k ^ 2 * a, k ^ 2 * b, k ^ 2 * c, k ^ 2 * d, ?_, Nat.mul_le_mul_left _ hcd,
    ⟨k * x, ?_⟩, ⟨k * y, ?_⟩⟩
  · rw [heq]
    ring
  · rw [hx]
    ring
  · calc
      k ^ 2 * a + 24 * (k ^ 2 * b) = k ^ 2 * (a + 24 * b) := by ring
      _ = _ := by rw [hy]; ring

lemma of_fourth_power_free
    (h : ∀ n : ℕ, (∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ n) → A n) (n : ℕ) : A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      exact zero_rep
    by_cases hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ n
    · exact h n hfree
    push_neg at hfree
    obtain ⟨p, hp, m, rfl⟩ := hfree
    have hpow : 1 < p ^ 4 := Nat.one_lt_pow (by decide) hp.one_lt
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst m
        simp at hzero
      · exact h0
    have hlt : m < p ^ 4 * m := by simpa using Nat.mul_lt_mul_of_pos_right hpow hm
    exact mul_fourth_of (ih m hlt) p

theorem main : H1 → H2 → type_of% @OeisA281976.conjecture := by
  intro h1 h2 n
  apply of_fourth_power_free
  intro m hm
  rcases Nat.mod_two_eq_zero_or_one m with he | ho
  · exact h2 m he hm
  · exact h1 m ho hm

end OMA.R_OeisA281976_conjecture_R1
