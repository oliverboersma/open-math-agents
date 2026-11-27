import OMAStatements.S_oeis_a071622
import Mathlib.Tactic.Ring

namespace OMA.A071622

open OMA.S_oeis_a071622

-- Sum a block of 2^depth contributions in a balanced tree.
def block (start : ℕ) : ℕ → ℤ
  | 0 => contribution (start + 1)
  | depth + 1 => block start depth + block (start + 2 ^ depth) depth

lemma add_block (start depth : ℕ) : a (start + 2 ^ depth) = a start + block start depth := by
  induction depth generalizing start with
  | zero => simp [block, a]
  | succ depth ih =>
    rw [show start + 2 ^ (depth + 1) = start + 2 ^ depth + 2 ^ depth by ring,
      ih (start + 2 ^ depth), ih start, block, add_assoc]

lemma advance (start depth : ℕ) (v delta result : ℤ) (hs : a start = v)
    (hb : block start depth = delta) (sum : v + delta = result) :
    a (start + 2 ^ depth) = result := by
  rw [add_block, hs, hb, sum]

set_option maxHeartbeats 4000000 in
lemma witness : a 18966 = 0 := by
  have h1 : a 16384 = 156 := advance 0 14 0 156 156 rfl (by decide +kernel) (by decide)
  have h2 : a 18432 = 48 := advance 16384 11 156 (-108) 48 h1 (by decide +kernel) (by decide)
  have h3 : a 18944 = 6 := advance 18432 9 48 (-42) 6 h2 (by decide +kernel) (by decide)
  have h4 : a 18960 = 4 := advance 18944 4 6 (-2) 4 h3 (by decide +kernel) (by decide)
  have h5 : a 18964 = 2 := advance 18960 2 4 (-2) 2 h4 (by decide +kernel) (by decide)
  exact advance 18964 1 2 (-2) 0 h5 (by decide +kernel) (by decide)

end OMA.A071622

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071622.main) := by
  intro h
  have hbad := h 18966 (by decide)
  rw [OMA.A071622.witness, Int.cast_zero] at hbad
  exact (not_lt_of_ge (sq_nonneg _)) hbad
