import OMAStatements.S_oeis_a290650
import Mathlib.Tactic

open OMA.S_oeis_a290650

-- Follow the halving steps until the next multiplication.
private theorem exceed (i : ℕ) (hp : 0 < term i) : ∃ j, i < term j := by
  by_cases he : term i % 2 = 0
  · have h : term (i + 1) = term i / 2 := by rw [term, if_pos he]
    obtain ⟨j, hj⟩ := exceed (i + 1) (by omega)
    exact ⟨j, by omega⟩
  · exact ⟨i + 1, by rw [term, if_neg he]; nlinarith⟩
termination_by term i
decreasing_by omega

theorem OMA.solution : type_of% @OMA.S_oeis_a290650.main := by
  intro B
  apply exceed
  induction B with
  | zero => decide
  | succ i ih =>
    rw [term]
    split
    · omega
    · positivity
