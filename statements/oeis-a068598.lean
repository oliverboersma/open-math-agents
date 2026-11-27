import Mathlib

/-!
# OEIS A068598

Each positive part is represented by its value minus one in Fin n.
A block is one strict partition of n. In a family, two blocks sharing
a part must coincide. We count families maximal under inclusion, with
a(0)=1 as in the source.

Beregovsky conjectured growth asymptotic to A exp(B n^C), proposing
C approximately 1.54 and later 1.36. Both fits require positive A,B
and C>1. The existence claim below includes both proposals and every
other choice of coefficients in the same range.

Source: https://oeis.org/A068598
-/

namespace OMA.S_oeis_a068598

abbrev Block (n : ℕ) := Finset (Fin n)
abbrev Family (n : ℕ) := Finset (Block n)

def admissible {n : ℕ} (s : Family n) : Prop :=
  (∀ b ∈ s, b.Nonempty ∧ (∑ i ∈ b, (i.val+1))=n) ∧
    ∀ b ∈ s, ∀ d ∈ s, ∀ i ∈ b, i ∈ d → b=d

noncomputable def term (n : ℕ) : ℕ := by
  classical
  exact if n=0 then 1 else
    (Finset.univ.filter (fun s : Family n => admissible s ∧
      ∀ t : Family n, s ⊆ t → admissible t → t=s)).card

open Filter Topology in
theorem main : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 1 < c ∧
    Tendsto (fun n : ℕ => (term n : ℝ)/(a*Real.exp (b*(n:ℝ)^c))) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a068598
