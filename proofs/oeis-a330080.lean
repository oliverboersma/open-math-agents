import OMAStatements.S_oeis_a330080
import Mathlib

-- Problem: A330080, the floors of the rational recurrence b(n+3) = (b(n+2) + b(n+1)) / b(n).
-- Upstream: formal-conjectures statements/oeis-a330080.lean (declaration OMA.S_oeis_a330080.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: all terms are positive and (1+x)(1+y)(1+z)(x+y+z) = 24xyz is invariant along consecutive
-- triples; a polynomial inequality shows this forces every term below 6.

namespace OMA.P_oeis_a330080

open OMA.S_oeis_a330080

theorem ineq0 (y z : ℚ) (hy : 0 < y) (hz : 0 < z) :
    144 * y * z < 7 * (1 + y) * (1 + z) * (6 + y + z) := by
  nlinarith [mul_pos hy hz, sq_nonneg (y - z), sq_nonneg (y + z - 11 / 2), mul_pos (mul_pos hy hz) hy,
    mul_pos (mul_pos hy hz) hz, sq_nonneg (y - 3), sq_nonneg (z - 3)]

theorem ineq (x y z : ℚ) (hx : 6 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    24 * x * y * z < (1 + x) * (1 + y) * (1 + z) * (x + y + z) := by
  have h0 := ineq0 y z hy hz
  have hd : 0 ≤ (1 + y) * (1 + z) * (13 + y + z) - 24 * y * z := by
    nlinarith [mul_pos hy hz, sq_nonneg (y - z), mul_pos (mul_pos hy hz) hy,
      mul_pos (mul_pos hy hz) hz]
  obtain ⟨u, hu0, rfl⟩ : ∃ u, 0 ≤ u ∧ x = 6 + u := ⟨x - 6, by linarith, by ring⟩
  nlinarith [mul_nonneg hu0 hd, mul_nonneg (mul_nonneg hu0 hu0)
    (mul_pos (by linarith : (0:ℚ) < 1 + y) (by linarith : (0:ℚ) < 1 + z)).le]

/-- The invariant of the recurrence. -/
def E (x y z : ℚ) : Prop := (1 + x) * (1 + y) * (1 + z) * (x + y + z) = 24 * x * y * z

theorem E_step (x y z : ℚ) (hx : 0 < x) (hE : E x y z) : E y z ((z + y) / x) := by
  unfold E at *
  have key : x ^ 2 * ((1 + y) * (1 + z) * (1 + (z + y) / x) * (y + z + (z + y) / x) -
      24 * y * z * ((z + y) / x)) =
      (y + z) * ((1 + x) * (1 + y) * (1 + z) * (x + y + z) - 24 * x * y * z) := by
    field_simp
    ring
  rw [hE, sub_self, mul_zero] at key
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hx2
  linarith

theorem pos_inv : ∀ n : ℕ, 0 < term n ∧ 0 < term (n + 1) ∧ 0 < term (n + 2) ∧
    E (term n) (term (n + 1)) (term (n + 2))
  | 0 => by
    refine ⟨by norm_num [term], by norm_num [term], by norm_num [term], ?_⟩
    unfold E
    norm_num [term]
  | n + 1 => by
    obtain ⟨hx, hy, hz, hE⟩ := pos_inv n
    have hw : term (n + 3) = (term (n + 2) + term (n + 1)) / term n := rfl
    refine ⟨hy, hz, ?_, ?_⟩
    · rw [hw]
      positivity
    · rw [hw]
      exact E_step _ _ _ hx hE

theorem main' : ∀ n : ℕ, 0 ≤ ⌊term n⌋ ∧ ⌊term n⌋ ≤ 5 := by
  intro n
  obtain ⟨hx, hy, hz, hE⟩ := pos_inv n
  refine ⟨Int.floor_nonneg.mpr hx.le, ?_⟩
  rw [Int.floor_le_iff]
  by_contra h
  have h6 : (6 : ℚ) ≤ term n := by push_cast at h; linarith
  have := ineq _ _ _ h6 hy hz
  unfold E at hE
  linarith

end OMA.P_oeis_a330080

theorem OMA.solution : type_of% @OMA.S_oeis_a330080.main := OMA.P_oeis_a330080.main'
