import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic

/-!
# Transitivity of balanced mass transport on the integers
Source: https://mathoverflow.net/q/202165 (James Propp, April 2015).
The linked formulation https://mathoverflow.net/q/201745 specifies sigma-finite measures.
On the integers these are nonnegative weights finite at each site, with arbitrary total mass.
Credit: @LDJAI with OpenAI Codex.
-/

namespace OMA.S_mo_202165

abbrev Profile := ℤ → ℝ

def moment (q : Bool) (x : ℤ) : ℝ := if q then (x : ℝ) else 1

def tally (l u : ℤ) (q : Bool) (p : Profile) : ℝ :=
  ∑ x ∈ Finset.Icc l u, moment q x * p x

/-- One row per left endpoint. Countably many packets assigned the same window can be
summed, since each site has finite mass. Zero rows are omitted in the original decomposition. -/
structure Rows (r : ℤ) (p : Profile) where
  val : ℤ → Profile
  pos : ∀ i x, 0 ≤ val i x
  loc : ∀ i x, val i x ≠ 0 → i ≤ x ∧ x ≤ i + r
  col : ∀ x, ∑ i ∈ Finset.Icc (x-r) x, val i x = p x

/-- Equal row masses and first moments express equal masses and centers of mass. -/
def Balanced (p q : Profile) : Prop :=
  ∃ r : ℤ, 0 ≤ r ∧ ∃ (a : Rows r p) (b : Rows r q), ∀ i j,
    tally i (i+r) j (a.val i) = tally i (i+r) j (b.val i)

theorem main : ∀ p q s : Profile, Balanced p q → Balanced q s → Balanced p s := by
  sorry

end OMA.S_mo_202165
