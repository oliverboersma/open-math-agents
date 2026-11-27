import FormalConjectures.ErdosProblems.«207»

-- Reduction Erdos207.erdos_207.R1 of Erdős Problem 207
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- For `n` large with `n % 6 = 1` or `3` the target asks for a Steiner triple system on `n`
-- vertices whose small edge sets already span enough vertices. The two halves are independent:
-- existence of the design, and the vertex-spreading property of every such design.

namespace OMA.R_Erdos207_erdos_207_R1

/-- Existence: for every `g >= 2` and every large `n` with `n % 6` in `{1, 3}` there is a
3-uniform block design on `Fin n` with `2`-subsets as blocks. -/
def H1 : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in Filter.atTop, n % 6 = 1 ∨ n % 6 = 3 →
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 3

/-- Spreading: for every `g >= 2` and every large `n` with `n % 6` in `{1, 3}`, any block design
on `Fin n` has the property that `j <= g` edges span at least `j + 3` vertices. -/
def H2 : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in Filter.atTop, n % 6 = 1 ∨ n % 6 = 3 →
    ∀ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 3 → ∀ E ⊆ H,
      2 ≤ E.card → E.card ≤ g → E.card + 3 ≤ (E.biUnion id).card

theorem main : H1 → H2 → type_of% @Erdos207.erdos_207 := by
  intro h1 h2 g hg
  filter_upwards [h1 g hg, h2 g hg] with n hn1 hn2 hmod
  obtain ⟨H, hH⟩ := hn1 hmod
  exact ⟨H, hH, hn2 hmod H hH⟩

end OMA.R_Erdos207_erdos_207_R1
