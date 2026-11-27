import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime divisibility in OEIS A377118

Clark Kimberling, October 2024. Source: https://oeis.org/A377118
Formalization: @thomasfredrickson with Codex.

The OEIS offset is zero. The six blocks below use the prime labels printed in
the entry. A block may start at any phase. Its length is claimed to be the
least positive period of the full gap sequence.
-/

namespace OMA.S_oeis_a377118

/-- The coefficients of 1, t, t² in (t + t²)^n, using t³ = 2. -/
def coefficients : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | n + 1 =>
    let (u, v, w) := coefficients n
    (2 * v + 2 * w, u + 2 * w, u + v)

def a (n : ℕ) : ℕ := (coefficients n).2.1

/-- Distance from the j-th to the next index at which p divides the term. -/
noncomputable def gap (p j : ℕ) : ℕ :=
  Nat.nth (fun n => p ∣ a n) (j + 1) - Nat.nth (fun n => p ∣ a n) j

def displayed : List (ℕ × List ℕ) := [
  (2, [1]),
  (3, [9, 4, 1, 2, 8]),
  (5, [7, 6, 5, 22]),
  (7, [60, 23, 5, 9, 16, 8, 42, 7, 19, 1, 2, 10, 31, 4, 11, 6, 34]),
  (11, [30]),
  (13, [119, 13, 9, 25, 15, 51, 45, 1, 2, 17, 41, 28, 54])]

def generalClaim (p : ℕ) : Prop :=
    {n : ℕ | p ∣ a n}.Infinite ∧
      ∃ d > 0, ∃ N : ℕ, ∀ j ≥ N, gap p (j + d) = gap p j

def purePeriod (p d : ℕ) : Prop := 0 < d ∧ ∀ j, gap p (j + d) = gap p j

theorem main : ∀ p : ℕ, p.Prime → generalClaim p ∧
    ∀ w : List ℕ, (p, w) ∈ displayed →
      (∃ phase : ℕ, ∀ j, gap p j = w.getD ((j + phase) % w.length) 0) ∧
      purePeriod p w.length ∧ (∀ d, purePeriod p d → w.length ≤ d) := by
  sorry

end OMA.S_oeis_a377118
