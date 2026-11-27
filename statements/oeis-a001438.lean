import Mathlib

/-!
# A001438: Maximal number of mutually orthogonal Latin squares (or MOLS) of order n.

Source: https://oeis.org/A001438
Credit: @mbilenko03

Conjecture (Parker and others): `a(10) = 2`, that is, the largest number of mutually orthogonal
Latin squares of order 10 is 2.

Conventions:
- A Latin square of order `n` is a function `L : Fin n → Fin n → Fin n` (row, column ↦ symbol)
  in which every row and every column is a bijection.
- Two Latin squares `L`, `M` of order `n` are orthogonal when the superimposed pairs
  `(L i j, M i j)` are all distinct, i.e. the map `(i, j) ↦ (L i j, M i j)` is injective.
- `HasMOLS n k`: there are `k` Latin squares of order `n` that are pairwise orthogonal.
  `maxMOLS n` is the supremum of such `k`, which is `a(n)` for `n ≥ 2` (for `n ≥ 2` the set is
  bounded by `n - 1`, so the supremum is a maximum; the convention `a(0) = a(1) = ∞` does not
  matter here). The conjecture is `maxMOLS 10 = 2`.
-/

namespace OMA.S_oeis_a001438

/-- `L` is a Latin square of order `n`: every row and every column is a bijection. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i => L i j)

/-- `L` and `M` are orthogonal: all superimposed pairs `(L i j, M i j)` are distinct. -/
def Orthogonal {n : ℕ} (L M : Fin n → Fin n → Fin n) : Prop :=
  Function.Injective (fun p : Fin n × Fin n => (L p.1 p.2, M p.1 p.2))

/-- There are `k` pairwise orthogonal Latin squares of order `n`. -/
def HasMOLS (n k : ℕ) : Prop :=
  ∃ L : Fin k → Fin n → Fin n → Fin n,
    (∀ a, IsLatin (L a)) ∧ ∀ a b, a ≠ b → Orthogonal (L a) (L b)

/-- The maximal number of mutually orthogonal Latin squares of order `n` (OEIS A001438). -/
noncomputable def maxMOLS (n : ℕ) : ℕ := sSup {k : ℕ | HasMOLS n k}

theorem main : maxMOLS 10 = 2 := by
  sorry

end OMA.S_oeis_a001438
