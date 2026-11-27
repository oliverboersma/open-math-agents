import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H2.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H2
-- Credit: @hyprspacecoyote
--
-- Step H2 asks for K_{m+1}(C(x_1, ..., x_m))/p = 0 for m >= 3 and every prime p. The prime 2 and
-- the odd primes need different mathematics, so they are split:
--   H1  p = 2: elementary from quadratic forms. C(x_1, ..., x_m) has u-invariant 2^m (Lang's
--       degree count), so the form <<a_1, ..., a_m>> + <c> in 2^m + 1 variables is isotropic;
--       a nonzero pure value e of the Pfister form is a slot of {a_1, ..., a_m} and a norm
--       from F(sqrt(-c)), hence {a_1, ..., a_m, c} = 0. A complete Lean proof is ready as the
--       step proof (all m, not only m >= 3).
--   H2  p odd: needs Bass-Tate (Milnor's exact sequence with norms) or cd = m plus Bloch-Kato.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H2_R1

def H1 : Prop := ∀ m : ℕ, 3 ≤ m →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 (m + 1)

def H2 : Prop := ∀ m p : ℕ, 3 ≤ m → p.Prime → p ≠ 2 →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p (m + 1)

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1.H2 := by
  intro h1 h2 m p hm hp
  by_cases hp2 : p = 2
  · subst hp2
    exact h1 m hm
  · exact h2 m p hm hp hp2

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H2_R1
