import FormalConjectures.Wikipedia.EswarathasanLevineConjecture

-- Reduction EswarathasanLevineConjecture.eswarathasan_levine_harmonic_conjecture.R1
-- Credit: @marcusbuffett

/-!
# The Eswarathasan-Levine conjecture: the primes 2, 3 and 5, and the open rest

For a prime `p` let `J_p` be the set of `n ≥ 1` such that `p` divides the numerator of the
harmonic number `H_n`. The conjecture says that `J_p` is finite for every prime `p`.

* `H1` (Eswarathasan and Levine 1991): `J_p` is finite for `p < 7`; in fact `J_2` is empty,
  `J_3 = {2, 7, 22}` and `J_5 = {4, 20, 24}`. The proof is the descent `n ∈ J_p → ⌊n / p⌋ ∈ J_p`
  for `n ≥ p`, which makes `J_p` a tree, together with the evaluation of the harmonic numbers
  at the finitely many candidates.
* `H2`: `J_p` is finite for every prime `p ≥ 7`. This is open in general (it has been checked
  for many individual primes by the same descent; `J_7` has 13 elements, the largest 102728).
-/

namespace OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1

/-- The primes below seven. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p < 7 → (EswarathasanLevineConjecture.harmonicNumDivisibleSet p).Finite

/-- The open part: the primes from seven on. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p → (EswarathasanLevineConjecture.harmonicNumDivisibleSet p).Finite

theorem main : H1 → H2 →
    type_of% @EswarathasanLevineConjecture.eswarathasan_levine_harmonic_conjecture := by
  intro h1 h2 p hp
  by_cases h : p < 7
  · exact h1 p hp h
  · exact h2 p hp (by omega)

end OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1
