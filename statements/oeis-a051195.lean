import Mathlib

/-!
# OEIS A051195

The terms count aperiodic binary words of length `2*n+2` with exactly `n`
ones. A word is represented by its set of one-positions, counted from
zero. A repeated word consists of at least two identical consecutive
blocks. The equations in `repeated` record its total length and weight.
R. J. Mathar conjectured the fourth-order recurrence below, where the
first applicable last index is 4.

Sources: https://oeis.org/A051195 and https://oeis.org/A050186
-/

namespace OMA.S_oeis_a051195

def copies (r l : ℕ) (block : Finset ℕ) : Finset ℕ :=
  (Finset.range r).biUnion (fun j => block.image (fun i => j*l+i))

def repeated (n : ℕ) (word : Finset ℕ) : Prop :=
  ∃ r l : ℕ, ∃ block : Finset ℕ, 2 ≤ r ∧ 0 < l ∧ block ⊆ Finset.range l ∧
    2*n+2 = r*l ∧ n = r*block.card ∧ word = copies r l block

def words (n : ℕ) : Finset (Finset ℕ) := (Finset.range (2*n+2)).powersetCard n

noncomputable def term (n : ℕ) : ℕ := by
  classical
  exact ((words n).filter (fun w => ¬ repeated n w)).card

def recurrence (k : ℕ) (z₀ z₁ z₂ z₃ z₄ : ℚ) : ℚ :=
  let n : ℚ := k+4
  (-(n+2)*(n-1)*z₄ + 2*(n+1)*(3*n-4)*z₃ + 4*(-n^2+5*n-1)*z₂
    - 8*n*(3*n-4)*z₁ + 16*(n-1)*(2*n-5)*z₀)

theorem main : ∀ k : ℕ, recurrence k (term k) (term (k+1)) (term (k+2))
    (term (k+3)) (term (k+4)) = 0 := by
  sorry

end OMA.S_oeis_a051195
