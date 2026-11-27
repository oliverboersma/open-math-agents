import OMAStatements.S_oeis_a002735
import Mathlib

-- Problem: oeis-a002735
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P002735
open OMA.S_oeis_a002735

theorem sol : type_of% @OMA.S_oeis_a002735.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold a
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, B, if_neg (by omega),
    show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
  norm_num

end OMA.P002735

theorem OMA.solution : type_of% @OMA.S_oeis_a002735.main := OMA.P002735.sol
