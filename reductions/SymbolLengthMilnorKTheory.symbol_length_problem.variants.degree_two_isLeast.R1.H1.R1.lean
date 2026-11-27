import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1
-- Credit: @hyprspacecoyote
--
-- Step H1 says that every class of K_2(C(x, y))/p is a single symbol for p = 2 and p = 3 (a theorem
-- of Artin). The two primes need different mathematics, so they are split:
--   H1  p = 2: elementary once C(x, y) has u-invariant 4 (Tsen-Lang): the Albert form of two
--       quaternion symbols is isotropic, so they share a slot. A complete Lean proof of H1 is
--       ready as the step proof (Lang's degree count over C[x, y] with Krull's height theorem,
--       then the common-slot identities in K_2/2).
--   H2  p = 3: needs period = index in degree 3 (Artin, de Jong) and Wedderburn's theorem that
--       degree-3 division algebras are cyclic; no elementary route is known.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1

def H1 : Prop := 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) 2 2

def H2 : Prop := 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) 3 2

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1.H1 := by
  intro h2 h3 p hp hp3
  have h : p = 2 ∨ p = 3 := by
    have := hp.two_le
    omega
  rcases h with rfl | rfl
  · exact h2
  · exact h3

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1
