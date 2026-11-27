import FormalConjectures.OEIS.«261876»

-- Reduction OeisA261876.conjecture_1.R1 of Sun's conjecture (i) in A261876
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
Two observations split conjecture (i) into a classical theorem and its genuinely open core.
* If n = a^2 + b^2 + c^2 with n > 0, put one nonzero coordinate in the z slot and take y = 0:
  then (5 x^2 + 7 y^2 + 9 z^2) y z = 0 is a square and z > 0, so a n > 0.
* Doubling every coordinate multiplies (5 x^2 + 7 y^2 + 9 z^2) y z by 16 and keeps z > 0, so
  a m > 0 implies a (4 m) > 0.
By the Gauss-Legendre three-square theorem every n with 4 not dividing n and n mod 8 not 7 is a
sum of three squares (H1, a known theorem not yet in Mathlib). Hence conjecture (i) holds as soon
as it holds for every n congruent to 7 mod 8 (H2).
-/

namespace OMA.R_OeisA261876_conjecture_1_R1

open OeisA261876

/-- The part of the Gauss-Legendre three-square theorem used here. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 4 ≠ 0 → n % 8 ≠ 7 → ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2

/-- The open core: conjecture (i) for every n congruent to 7 modulo 8. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 8 = 7 → 0 < a n

lemma isSquare_true_iff (k : ℕ) : isSquare k = true ↔ IsSquare k := by
  unfold isSquare
  rw [beq_iff_eq, sq]
  constructor
  · intro h
    exact ⟨Nat.sqrt k, h.symm⟩
  · rintro ⟨r, rfl⟩
    rw [Nat.sqrt_eq]

lemma le_of_sq_le {x n : ℕ} (h : x ^ 2 ≤ n) : x ≤ n := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · omega
  · nlinarith

lemma pos_of_rep {n x y z w : ℕ} (heq : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (hz : 0 < z)
    (hsq : IsSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z)) : 0 < a n := by
  have hx : x ≤ n := le_of_sq_le (by omega)
  have hy : y ≤ n := le_of_sq_le (by omega)
  have hz' : z ≤ n := le_of_sq_le (by omega)
  have hw : w ≤ n := le_of_sq_le (by omega)
  unfold a
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨x, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨y, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨z, Finset.mem_Ico.mpr ⟨hz, by omega⟩, ?_⟩
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨w, Finset.mem_range.mpr (by omega), ?_⟩
  have hc : (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n &&
      isSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z)) = true := by
    rw [Bool.and_eq_true, beq_iff_eq, isSquare_true_iff]
    exact ⟨heq, hsq⟩
  rw [if_pos hc]
  exact Nat.one_pos

lemma rep_of_pos {n : ℕ} (h : 0 < a n) : ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    0 < z ∧ IsSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z) := by
  unfold a at h
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp h)
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  obtain ⟨z, hzm, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hc : (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n &&
      isSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z)) = true := by
    by_contra hne
    exact hw (if_neg hne)
  rw [Bool.and_eq_true, beq_iff_eq, isSquare_true_iff] at hc
  exact ⟨x, y, z, w, hc.1, (Finset.mem_Ico.mp hzm).1, hc.2⟩

theorem main : H1 → H2 → type_of% @OeisA261876.conjecture_1 := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h4 : n % 4 = 0
    · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h4
      obtain ⟨x, y, z, w, heq, hz, r, hr⟩ := rep_of_pos (ih m (by omega) (by omega))
      apply pos_of_rep (x := 2 * x) (y := 2 * y) (z := 2 * z) (w := 2 * w)
      · rw [← heq]
        ring
      · omega
      · refine ⟨4 * r, ?_⟩
        calc
          (5 * (2 * x) ^ 2 + 7 * (2 * y) ^ 2 + 9 * (2 * z) ^ 2) * (2 * y) * (2 * z)
              = 16 * ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z) := by ring
          _ = 4 * r * (4 * r) := by rw [hr]; ring
    by_cases h7 : n % 8 = 7
    · exact h2 n h7
    · obtain ⟨p, q, s, h⟩ := h1 n h4 h7
      by_cases hp : p = 0
      · subst p
        by_cases hq : q = 0
        · subst q
          have hs : 0 < s := by
            rcases Nat.eq_zero_or_pos s with hs | hs
            · subst s
              simp at h
              omega
            · exact hs
          exact pos_of_rep (x := 0) (y := 0) (z := s) (w := 0) (by rw [h]; ring) hs
            ⟨0, by ring⟩
        · exact pos_of_rep (x := 0) (y := 0) (z := q) (w := s) (by rw [h]; ring)
            (Nat.pos_of_ne_zero hq) ⟨0, by ring⟩
      · exact pos_of_rep (x := q) (y := 0) (z := p) (w := s) (by rw [h]; ring)
          (Nat.pos_of_ne_zero hp) ⟨0, by ring⟩

end OMA.R_OeisA261876_conjecture_1_R1
