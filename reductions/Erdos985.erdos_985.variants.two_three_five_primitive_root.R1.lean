import FormalConjectures.ErdosProblems.«985»

-- Reduction Erdos985.erdos_985.variants.two_three_five_primitive_root.R1 of Erdős Problem 985 — two three five primitive root
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Heath-Brown's theorem says that at least one of `2`, `3`, `5` is a primitive root modulo
-- infinitely many primes. The target is the disjunction over the three bases, so each base is
-- its own step; any one of them already finishes the problem.

namespace OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R1

/-- Base `2` is a primitive root modulo infinitely many primes. -/
def H1 : Prop := Set.Infinite {p : ℕ | p.Prime ∧ orderOf (2 : ZMod p) = p - 1}

/-- Base `3` is a primitive root modulo infinitely many primes. -/
def H2 : Prop := Set.Infinite {p : ℕ | p.Prime ∧ orderOf (3 : ZMod p) = p - 1}

/-- Base `5` is a primitive root modulo infinitely many primes. -/
def H3 : Prop := Set.Infinite {p : ℕ | p.Prime ∧ orderOf (5 : ZMod p) = p - 1}

theorem main : H1 → H2 → H3 →
    type_of% @Erdos985.erdos_985.variants.two_three_five_primitive_root := by
  intro h1 h2 h3
  exact h1.mono fun p hp => ⟨hp.1, Or.inl hp.2⟩

end OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R1
