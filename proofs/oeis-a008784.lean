import OMAStatements.S_oeis_a008784
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a008784.main := by
  intro k hk
  constructor
  · rintro ⟨x, hx⟩
    haveI : NeZero k := ⟨by omega⟩
    refine ⟨x.val + k, ?_, ?_⟩
    · rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val, hx]
      ring
    · have : 1 ≤ x.val + k := by omega
      nlinarith
  · rintro ⟨m, hm, -⟩
    refine ⟨(m : ZMod k), ?_⟩
    have := (ZMod.natCast_eq_zero_iff (m ^ 2 + 1) k).2 hm
    push_cast at this
    linear_combination this
