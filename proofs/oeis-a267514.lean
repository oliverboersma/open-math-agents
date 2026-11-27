import OMAStatements.S_oeis_a267514

-- Problem: OEIS A267514, Colin Barker's conjectured recurrence and generating function
-- for the Rule 137 center column.
-- Disproof: the recurrence a(n) = 10 a(n-1) + a(n-7) - 10 a(n-8) says that the center
-- column is periodic with period 7 from n = 1 on; it fails at n = 62, where the center
-- cell differs from the cell at n = 55 (R. J. Mathar, OEIS, Apr 12 2019).

namespace OMA.A267514Proof

open OMA.S_oeis_a267514

set_option maxRecDepth 100000 in
lemma fails : a 62 ≠ 10 * a (62 - 1) + a (62 - 7) - 10 * a (62 - 8) := by
  decide

end OMA.A267514Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267514.main) := by
  intro h
  exact OMA.A267514Proof.fails (h.1 62 (by norm_num))
