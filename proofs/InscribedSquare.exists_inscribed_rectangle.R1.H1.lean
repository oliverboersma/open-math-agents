import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1
import Mathlib

/-!
Step H1 of the InscribedSquare reduction: the explicit maps
u(s,t) = exp(i pi (s+t)) and v(s,t) = exp(i pi (s-t)) on the unit square.
-/

namespace OMA.P1InscribedSquareH1

theorem key (x y : ℝ) :
    Circle.exp (Real.pi * x) = Circle.exp (Real.pi * y) ↔ ∃ m : ℤ, x = y + 2 * m := by
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h : Real.pi * (x - (y + 2 * m)) = 0 := by linear_combination hm
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h Real.pi_ne_zero
    · linarith
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; ring⟩

end OMA.P1InscribedSquareH1

open OMA.P1InscribedSquareH1 in
theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H1 := by
  unfold OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H1
  intro seam
  refine ⟨fun p => Circle.exp (Real.pi * ((p.1 : ℝ) + (p.2 : ℝ))),
    fun p => Circle.exp (Real.pi * ((p.1 : ℝ) - (p.2 : ℝ))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Circle.exp.continuous.comp (by fun_prop)
  · exact Circle.exp.continuous.comp (by fun_prop)
  · intro t
    constructor
    · rw [key]
      exact ⟨0, by simp [unitInterval.coe_symm_eq]⟩
    · rw [key]
      exact ⟨-1, by simp [unitInterval.coe_symm_eq]; ring⟩
  · intro p
    rw [key]
    have t0 := p.2.2.1
    have t1 := p.2.2.2
    constructor
    · rintro ⟨m, hm⟩
      have a0 : (0 : ℝ) ≤ m := by linarith
      have a1 : (m : ℝ) ≤ 1 := by linarith
      have b0 : (0 : ℤ) ≤ m := by exact_mod_cast a0
      have b1 : m ≤ (1 : ℤ) := by exact_mod_cast a1
      have hc : m = 0 ∨ m = 1 := by omega
      rcases hc with rfl | rfl
      · left
        exact Subtype.ext (show (p.2 : ℝ) = 0 by push_cast at hm; linarith)
      · right
        exact Subtype.ext (show (p.2 : ℝ) = 1 by push_cast at hm; linarith)
    · rintro (h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]; ring⟩
  · intro p q hpq
    simp only [seam]
    have s0 := p.1.2.1
    have s1 := p.1.2.2
    have t0 := p.2.2.1
    have t1 := p.2.2.2
    have s0' := q.1.2.1
    have s1' := q.1.2.2
    have t0' := q.2.2.1
    have t1' := q.2.2.2
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [key] at h1 h2
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      have a1 : ((m + n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a2 : (-1 : ℝ) ≤ ((m + n : ℤ) : ℝ) := by push_cast; linarith
      have a3 : ((m - n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a4 : (-1 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by push_cast; linarith
      have b1 : m + n ≤ 1 := by exact_mod_cast a1
      have b2 : -1 ≤ m + n := by exact_mod_cast a2
      have b3 : m - n ≤ 1 := by exact_mod_cast a3
      have b4 : -1 ≤ m - n := by exact_mod_cast a4
      have hc : (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
          (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by omega
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        push_cast at hm hn <;>
        first
        | exact Or.inl (Prod.ext (Subtype.ext (by linarith)) (Subtype.ext (by linarith)))
        | exact Or.inr (Or.inl ⟨Subtype.ext (show (p.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.2 : ℝ) = 1 - (p.2 : ℝ) by linarith)⟩)
        | exact Or.inr (Or.inr ⟨Subtype.ext (show (p.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (p.2 : ℝ) = 1 - (q.2 : ℝ) by linarith)⟩)
    · rw [key] at h1 h2
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      have a1 : ((m + n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a2 : (-1 : ℝ) ≤ ((m + n : ℤ) : ℝ) := by push_cast; linarith
      have a3 : ((m - n : ℤ) : ℝ) ≤ 2 := by push_cast; linarith
      have a4 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by push_cast; linarith
      have b1 : m + n ≤ 1 := by exact_mod_cast a1
      have b2 : -1 ≤ m + n := by exact_mod_cast a2
      have b3 : m - n ≤ 2 := by exact_mod_cast a3
      have b4 : 0 ≤ m - n := by exact_mod_cast a4
      have hc : (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = -1) ∨ (m = 1 ∧ n = 0) ∨
          (m = 0 ∧ n = -1) := by omega
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        push_cast at hm hn <;>
        first
        | exact Or.inl (Prod.ext (Subtype.ext (by linarith)) (Subtype.ext (by linarith)))
        | exact Or.inr (Or.inl ⟨Subtype.ext (show (p.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.2 : ℝ) = 1 - (p.2 : ℝ) by linarith)⟩)
        | exact Or.inr (Or.inr ⟨Subtype.ext (show (p.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (p.2 : ℝ) = 1 - (q.2 : ℝ) by linarith)⟩)
