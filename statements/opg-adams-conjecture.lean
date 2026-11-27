import Mathlib

/-!
# Ádám's Conjecture

Source: https://www.openproblemgarden.org/op/adams_conjecture
Credit: @LordMike

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The Open Problem Garden page (posted by fhavet) states: 'Conjecture: Every digraph with at least
one directed cycle has an arc whose reversal reduces the number of directed cycles.' It notes that
the conjecture fails for multigraphs (counterexamples of Grinberg, Jirásek and Thomassen) and that
it 'remains open for tournaments': 'Conjecture: Every tournament that is not transitive has an arc
whose reversal reduces the number of directed cycles.' The problem was posed by András Ádám
(Problem 2 in Theory of Graphs and its Applications, Prague 1964).

This file formalizes the tournament version, the form that the source describes as open. The
general digraph version is not stated: the literature records a 2023 family of strongly 2-connected
oriented graphs that are counterexamples to it, so only the tournament case stays open.

Modelling choices:
* A tournament is a relation `adj` on `Fin n` that is irreflexive, such that for distinct `i j`
  exactly one of `adj i j`, `adj j i` holds.
* A directed cycle is a directed cycle subgraph, i.e. its set of arcs. Concretely a cycle is
  given by a duplicate-free list `l` of at least 3 vertices with `l[i] -> l[i+1]` and
  `l[last] -> l[0]` all arcs (the arcs are the pairs of `l.zip (l.rotate 1)`). Two lists
  differing by a rotation give the same arc set, so they count as one cycle. Cycles of length 2 do
  not occur in tournaments (also after reversal), so requiring length at least 3 is harmless.
* The number of cycles is the `Set.ncard` of the set of such arc sets; this set is finite (it
  lives in the power set of `Fin n x Fin n`), so `ncard` is the true count.
* Reversing the arc `a -> b` gives the relation `reverse adj a b`, again a tournament.
* 'Not transitive' is taken literally: the relation `adj` is not transitive.
-/

namespace OMA.S_opg_adams_conjecture

/-- The arc sets of the directed cycles (of length at least 3) of the digraph `adj` on `Fin n`. -/
def cycles {n : ℕ} (adj : Fin n → Fin n → Prop) : Set (Finset (Fin n × Fin n)) :=
  {C | ∃ l : List (Fin n), l.Nodup ∧ 3 ≤ l.length ∧
    (∀ p ∈ l.zip (l.rotate 1), adj p.1 p.2) ∧ C = (l.zip (l.rotate 1)).toFinset}

/-- Reversal of the arc `a -> b`. -/
def reverse {n : ℕ} (adj : Fin n → Fin n → Prop) (a b : Fin n) : Fin n → Fin n → Prop :=
  fun x y => (adj x y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a)

/-- Ádám's conjecture for tournaments: every non-transitive tournament has an arc whose reversal
decreases the number of directed cycles. -/
theorem main : ∀ (n : ℕ) (adj : Fin n → Fin n → Prop),
    (∀ i, ¬ adj i i) → (∀ i j, i ≠ j → (adj i j ↔ ¬ adj j i)) → ¬ (∀ x y z, adj x y → adj y z → adj x z) →
    ∃ a b, adj a b ∧ (cycles (reverse adj a b)).ncard < (cycles adj).ncard := by
  sorry

end OMA.S_opg_adams_conjecture
