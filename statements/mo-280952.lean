import Mathlib

/-!
# Relationship between the core of the quotient game of a convex game G and the projection of the core of G onto the a priori coalitions?

Source: https://mathoverflow.net/questions/280952 (question by Joachim Henkel)
Credit: @tatashbar

The source asks a yes/no question: for a convex game `G = (N, v)` and a partition of `N` into
a priori unions `b_1, ..., b_m`, is the core `C'` of the quotient game `G'` equal to `f(C)`,
where `C` is the core of `G` and `f` sends an allocation to the vector of union totals?
The asker's hunch is that it is, so `main` states the affirmative, `C' = f(C)`.

Status: this is a known result, not an open problem. The source page has an answer by
Ron Peretz (September 2017): yes, because the extreme points of the core of a convex game are
its marginal vectors (L. S. Shapley, Cores of convex games, Int. J. Game Theory 1 (1971),
11-26, doi 10.1007/BF01753431), and a marginal vector of `G'` is the image under `f` of a
marginal vector of `G` for an order of the players that keeps each union consecutive.

Reading of the source (standard conventions of cooperative game theory):
* A game is a characteristic function `v` on coalitions (finite sets of players) with
  `v ∅ = 0`; it is convex when `v` is supermodular (Shapley 1971).
* The partition into `m` unions is a surjective map `b` from the players to an index type
  `M` (player `i` belongs to union `b i`); surjectivity says that every union is nonempty.
* The quotient game gives a set `T` of unions the value of the players in those unions.
* The core is the set of allocations `x` with `x(N) = v(N)` and `x(S) ≥ v(S)` for all `S`.
-/

namespace OMA.S_mo_280952

open Finset

/-- A game `v` on the player set `N` (a real value for every coalition) is *convex* if its
characteristic function is supermodular: `v S + v T ≤ v (S ∪ T) + v (S ∩ T)`. -/
def IsConvexGame {N : Type*} [DecidableEq N] (v : Finset N → ℝ) : Prop :=
  ∀ S T : Finset N, v S + v T ≤ v (S ∪ T) + v (S ∩ T)

/-- The core of the game `v`: the allocations that distribute exactly the value of the grand
coalition and give every coalition at least its own value. -/
def core {N : Type*} [Fintype N] (v : Finset N → ℝ) : Set (N → ℝ) :=
  {x | ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i}

/-- The quotient game between the a priori unions. The partition is given by the map `b`
sending a player to the index of its union; a set `T` of unions is worth what the players of
those unions are worth together in the original game. -/
def quotientGame {N M : Type*} [Fintype N] [DecidableEq M] (v : Finset N → ℝ) (b : N → M) :
    Finset M → ℝ :=
  fun T => v (univ.filter fun i => b i ∈ T)

/-- The map `f` of the source: an allocation to the players is sent to the vector of union
totals, `y k = ∑ x i` over the members `i` of union `k`. -/
def unionTotals {N M : Type*} [Fintype N] [DecidableEq M] (b : N → M) (x : N → ℝ) : M → ℝ :=
  fun k => ∑ i with b i = k, x i

/-- For a convex game, the core of the quotient game is the image of the core under the
union-totals map: `C' = f(C)`. -/
theorem main : ∀ {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    (v : Finset N → ℝ), v ∅ = 0 → IsConvexGame v →
    ∀ b : N → M, Function.Surjective b →
      core (quotientGame v b) = unionTotals b '' core v := by
  sorry

end OMA.S_mo_280952
