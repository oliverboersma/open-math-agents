import Mathlib

/-!
# Gold partition conjecture

Source: https://en.wikipedia.org/wiki/1/3–2/3_conjecture#Generalizations_and_related_results
Credit: @LordMike

The Wikipedia article on the 1/3-2/3 conjecture says: 'Marcin Peczarski has formulated a gold
partition conjecture stating that in each partial order that is not a total order one can find two
consecutive comparisons such that, if t_i denotes the number of linear extensions remaining after i
of the comparisons have been made, then (in each of the four possible outcomes of the comparisons)
t_0 >= t_1 + t_2. If this conjecture is true, it would imply the 1/3-2/3 conjecture [...].'
(Peczarski, The gold partition conjecture, Order 23 (2006), 89-95; the two comparisons are chosen
in advance, before their outcomes are known.)

Modelling choices:
* A finite partial order is a type `α` with `[Fintype α] [PartialOrder α]`; it is not a total order
  iff it has two incomparable elements (the hypothesis of `main`). Any finite poset is isomorphic to one on
  such a type (in `Type`), so nothing is lost.
* `numExt α extra` is the number of linear extensions of the order, among those satisfying the
  extra constraints `extra : List (α × α)`, where `(a, b)` in `extra` means that `a` comes before
  `b`. A linear extension is a bijection `σ : α ≃ Fin (card α)` (a listing of the elements) with
  `a < b → σ a < σ b`. Adding the constraints and counting linear extensions is the same as adding
  the relations and taking the transitive closure; an outcome contradicting the order has count 0.
* A comparison of `x` and `y` has the two outcomes `x` before `y` and `y` before `x`. The statement
  asks for two pairs `(x, y)` and `(u, v)` (chosen in advance, not depending on the first outcome)
  such that for each of the four outcomes `(p, q)`: `t_0 = numExt []`, `t_1 = numExt [p]`,
  `t_2 = numExt [p, q]`, and `t_0 >= t_1 + t_2`.
* The compared elements are only required to be distinct (`x ≠ y`, `u ≠ v`); this excludes the
  degenerate pair with `x = y` (which would make a count 0 and the inequality trivial). Comparing
  already comparable elements cannot help (the surviving outcome keeps `t_1 = t_0`, forcing
  `t_2 = 0`, impossible), so requiring incomparability of `x, y` would give the same statement.
  The second comparison may involve elements already ordered by the first outcome.
* When the first outcome leaves a chain (`t_1 = 1`), `t_2` is 0 or 1 here, and `t_0 >= 2` makes the
  inequality hold, consistent with the convention `t_2 = 1` used in the literature.
* The source states a conjecture (not a yes/no question); the statement is the conjecture itself.
  It is open in general; it is known for posets of width 2, semiorders, and up to 14 elements
  (computer verified).
-/

namespace OMA.S_wp_gold_partition_conjecture

/-- Number of linear extensions of the partial order on `α` (bijections `σ : α ≃ Fin (card α)`
with `a < b → σ a < σ b`) that also satisfy `σ a < σ b` for every `(a, b)` in `extra`. -/
noncomputable def numExt (α : Type*) [Fintype α] [PartialOrder α] (extra : List (α × α)) : ℕ :=
  Nat.card {σ : α ≃ Fin (Fintype.card α) //
    (∀ a b : α, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}

/-- Gold partition conjecture (Peczarski): every finite partial order that is not a total order
has two comparisons `x ? y` and `u ? v`, fixed in advance, such that in each of the four outcomes
`t_0 ≥ t_1 + t_2`, where `t_i` is the number of linear extensions after `i` comparisons. -/
theorem main : ∀ (α : Type) [Fintype α] [PartialOrder α],
    (∃ a b : α, ¬ a ≤ b ∧ ¬ b ≤ a) →
    ∃ x y u v : α, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        numExt α [] ≥ numExt α [p] + numExt α [p, q] := by
  sorry

end OMA.S_wp_gold_partition_conjecture
