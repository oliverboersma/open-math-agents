import Mathlib

/-! The point counts in A346784 are compared to the positive walk-length
records of A346126. Radii below are squared. A record size k occurs when
some global radius threshold admits size k but cannot admit k+1, allowing
all placements. Because both attainable sizes are downward closed, these
are exactly the successively attained record maxima.
Sources: https://oeis.org/A346784 and https://oeis.org/A346126.
Credit: @shunyaekam. -/

namespace OMA.S_oeis_a346784

abbrev Site := ℤ × ℤ
abbrev Center := ℝ × ℝ

def unitStep (p q : Site) : Prop :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x^2 + x*y + y^2 = 1

def valid (m : ℕ) (p : ℕ → Site) : Prop :=
  (∀ i < m, unitStep (p i) (p (i+1))) ∧
  (∀ i j : ℕ, i < j → j ≤ m → p i = p j → i = 0 ∧ j = m) ∧
  (p 0 = p m → 3 ≤ m)

def fits (m : ℕ) (p : ℕ → Site) (o : Center) (s : ℝ) : Prop :=
  ∀ i ≤ m,
    let x := (p i).1 - o.1
    let y := (p i).2 - o.2
    x^2 + x*y + y^2 ≤ s

def attainable (m : ℕ) (s : ℝ) : Prop :=
  ∃ (p : ℕ → Site) (o : Center), valid m p ∧ fits m p o s

def pointsFit (k : ℕ) (s : ℝ) : Prop :=
  ∃ (p : Fin k → Site) (o : Center), Function.Injective p ∧
    ∀ i, let x := (p i).1 - o.1
         let y := (p i).2 - o.2
         x^2 + x*y + y^2 ≤ s

def recordSize (canFit : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  0 < k ∧ ∃ s : ℝ, 0 ≤ s ∧ canFit k s ∧ ¬ canFit (k+1) s

noncomputable def recordRank (canFit : ℕ → ℝ → Prop) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (k+1)).filter (recordSize canFit)).card

theorem main : ∀ n k m : ℕ, 2 < n →
    recordSize pointsFit k → recordRank pointsFit k = n →
    recordSize attainable m → recordRank attainable m = n-1 → k = m := by
  sorry

end OMA.S_oeis_a346784
