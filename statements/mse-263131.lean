import Mathlib

/-!
# Is there a Steiner system $S(6,9,45)$?

Source: https://math.stackexchange.com/questions/263131/is-there-a-steiner-system-s6-9-45
Credit: @mgv27

A Steiner system $S(t,k,n)$ is a family of $k$-element subsets ("blocks") of an $n$-element set
such that every $t$-element subset is contained in exactly one block. The divisibility
conditions do not rule out $S(6,9,45)$ (it would have $96965$ blocks, and the derived systems
$S(5,8,44)$, $S(4,7,43)$, $S(3,6,42)$, $S(2,5,41)$ all have integral block counts).
Does the Steiner system $S(6,9,45)$ actually exist?

Formalization notes:
* `main` states the "yes" reading: a Steiner system `S(6,9,45)` exists on `Fin 45`.
* No nontrivial Steiner system with `t ≥ 6` is known explicitly; Keevash's existence theorem
  only covers sufficiently large `n` satisfying the divisibility conditions.
-/

namespace OMA.S_mse_263131

/-- `blocks` is a Steiner system `S(t, k, n)` on `Fin n`: all blocks have `k` elements and every
`t`-element subset lies in exactly one block. -/
def IsSteinerSystem (t k n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, B.card = k) ∧
    ∀ T : Finset (Fin n), T.card = t → ∃! B, B ∈ blocks ∧ T ⊆ B

/-- Does the Steiner system `S(6, 9, 45)` exist? -/
theorem main : ∃ blocks : Finset (Finset (Fin 45)), IsSteinerSystem 6 9 45 blocks := by
  sorry

end OMA.S_mse_263131
