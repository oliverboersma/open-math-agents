import OMAStatements.S_oeis_a005479

-- Reduction oeis-a005479.R1 of A005479: Prime Lucas numbers (cf. A000032).
-- Credit: @sobrien032
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
OEIS A005479 records two conjectures: the prime Lucas numbers congruent to 7 modulo 10 are
exactly 7, 47 and 2207, and these are also exactly the prime Lucas numbers `L k` whose index
`k ≥ 1` is not prime. Both are equalities of sets, so each splits into its two inclusions.

`H1` is the finite check that 7 = L 4, 47 = L 8 and 2207 = L 16 lie in both sets: they are
prime, they end in the digit 7, and the indices 4, 8 and 16 are not prime.

`H2` is the open part: no other prime Lucas number ends in 7, and no other prime Lucas number
has an index `k ≥ 1` that is not prime. A prime `L k` with `k ≥ 1` not prime has `k` a power of
2. Modulo 10 the Lucas numbers repeat with period 12, ending in 7 exactly at the indices 4 and 8
modulo 12, which are not prime, and every `2 ^ m` with `m ≥ 2` lies in one of these classes. So
both parts of `H2` say that `L (2 ^ m)` is composite for every `m ≥ 5`.
-/

namespace OMA.R_oeis_a005479_R1

open OMA.S_oeis_a005479

/-- 7, 47 and 2207 are prime Lucas numbers congruent to 7 modulo 10, and each is `L k` for some
`k ≥ 1` that is not prime. -/
def H1 : Prop :=
  ({7, 47, 2207} : Set ℕ) ⊆ {p : ℕ | (∃ k : ℕ, lucas k = p) ∧ p.Prime ∧ p % 10 = 7} ∧
    ({7, 47, 2207} : Set ℕ) ⊆ {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ ¬ k.Prime ∧ lucas k = p ∧ p.Prime}

/-- The open part: every prime Lucas number congruent to 7 modulo 10, and every prime Lucas number
`L k` with `k ≥ 1` not prime, is 7, 47 or 2207. -/
def H2 : Prop :=
  {p : ℕ | (∃ k : ℕ, lucas k = p) ∧ p.Prime ∧ p % 10 = 7} ⊆ ({7, 47, 2207} : Set ℕ) ∧
    {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ ¬ k.Prime ∧ lucas k = p ∧ p.Prime} ⊆ ({7, 47, 2207} : Set ℕ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a005479.main :=
  fun h1 h2 => ⟨Set.Subset.antisymm h2.1 h1.1, Set.Subset.antisymm h2.2 h1.2⟩

end OMA.R_oeis_a005479_R1
