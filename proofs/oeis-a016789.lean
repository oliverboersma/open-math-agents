import OMAStatements.S_oeis_a016789
import Mathlib

-- Problem: oeis-a016789
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P016789
open OMA.S_oeis_a016789

theorem sol : type_of% @OMA.S_oeis_a016789.main := by
  intro y
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨9 * (n : ℤ) ^ 3 + 18 * n ^ 2 + 12 * n + 2, ?_⟩
    unfold a; push_cast; ring
  · rintro ⟨k, hk⟩
    refine ⟨y / 3, ?_⟩
    unfold a
    have h : (y : ℤ) % 3 = 2 := by
      have : ((y : ℤ) ^ 3) % 3 = 2 := by rw [hk]; omega
      rcases (show (y : ℤ) % 3 = 0 ∨ (y : ℤ) % 3 = 1 ∨ (y : ℤ) % 3 = 2 by omega) with h | h | h
      · exfalso; rw [pow_succ, pow_succ, pow_one, Int.mul_emod, Int.mul_emod ((y:ℤ)), h] at this; norm_num at this
      · exfalso; rw [pow_succ, pow_succ, pow_one, Int.mul_emod, Int.mul_emod ((y:ℤ)), h] at this; norm_num at this
      · exact h
    omega

end OMA.P016789

theorem OMA.solution : type_of% @OMA.S_oeis_a016789.main := OMA.P016789.sol
