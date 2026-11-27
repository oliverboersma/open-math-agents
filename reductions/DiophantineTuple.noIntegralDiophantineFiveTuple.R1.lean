import FormalConjectures.Wikipedia.DiophantineTuple
import Mathlib

/-! Reduction of the Diophantine 5-tuple theorem (He-Togbe-Ziegler 2019) to two independent
non-extendability results for ordered integral Diophantine quadruples `0 < a < b < c < d`:
- `H1` (Fujita 2008): no regular Diophantine quadruple `{a, b, c, regularExtension a b c}`
  extends to a Diophantine 5-tuple with a larger fifth element `e > d`.
- `H2` (He-Togbe-Ziegler 2019): no irregular Diophantine quadruple `{a, b, c, d}` (with
  `d != regularExtension a b c`) extends to a Diophantine 5-tuple with `e > d`.
In `main`, we order any hypothetical 5-tuple `t` via `t.orderEmbOfFin` into
`0 < a < b < c < d < e`, pass the Diophantine property to `{a, b, c, d, e}`, and split on
whether `d = regularExtension a b c`. -/

namespace OMA.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1

open DiophantineTuple

/-- Fujita (2008): no regular integral Diophantine quadruple `{a, b, c, d}` with
`0 < a < b < c < d = regularExtension a b c` extends to a 5-tuple `{a, b, c, d, e}` with
`d < e`. -/
def H1 : Prop :=
  ∀ a b c d e : ℕ, 0 < a → a < b → b < c → c < d → d < e →
    d = regularExtension a b c → ¬ IsIntegralDiophantineTuple {a, b, c, d, e}

/-- He-Togbe-Ziegler (2019): no irregular integral Diophantine quadruple `{a, b, c, d}` with
`0 < a < b < c < d` and `d != regularExtension a b c` extends to a 5-tuple `{a, b, c, d, e}`
with `d < e`. -/
def H2 : Prop :=
  ∀ a b c d e : ℕ, 0 < a → a < b → b < c → c < d → d < e →
    d ≠ regularExtension a b c → ¬ IsIntegralDiophantineTuple {a, b, c, d, e}

theorem main : H1 → H2 → type_of% @DiophantineTuple.noIntegralDiophantineFiveTuple := by
  rintro h1 h2 ⟨t, ht, hcard⟩
  set g := t.orderEmbOfFin hcard
  have hm : StrictMono g := (t.orderEmbOfFin hcard).strictMono
  have hmem : ∀ i, g i ∈ t := fun i => t.orderEmbOfFin_mem hcard i
  have ha0 : 0 < g 0 := Nat.pos_of_ne_zero (ht.1 (g 0) (hmem 0))
  have h01 : g 0 < g 1 := hm (by decide)
  have h12 : g 1 < g 2 := hm (by decide)
  have h23 : g 2 < g 3 := hm (by decide)
  have h34 : g 3 < g 4 := hm (by decide)
  have hsub : ({g 0, g 1, g 2, g 3, g 4} : Finset ℕ) ⊆ t := by
    simp [Finset.insert_subset_iff, hmem]
  have ht5 : IsIntegralDiophantineTuple {g 0, g 1, g 2, g 3, g 4} :=
    isDiophantineTuple_of_subset (R := ℕ) _ _ ht hsub
  by_cases hreg : g 3 = regularExtension (g 0) (g 1) (g 2)
  · exact h1 (g 0) (g 1) (g 2) (g 3) (g 4) ha0 h01 h12 h23 h34 hreg ht5
  · exact h2 (g 0) (g 1) (g 2) (g 3) (g 4) ha0 h01 h12 h23 h34 hreg ht5

end OMA.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1
