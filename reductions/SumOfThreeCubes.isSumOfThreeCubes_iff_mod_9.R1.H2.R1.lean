import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

/-!
The finite-congruence counterpart of Colliot-Thélène and Wittenberg's
p-adic solubility theorem (Lemma 4.5, arXiv:0911.3539) is separated from
the integral local-global implication. Their theorem identifies the only
exception as the 3-adic obstruction at 4 or 5 modulo 9.
The preceding split into necessity and sufficiency is due to @ihateSAS.
-/
namespace OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1

/-- Solubility at every positive modulus is equivalent to avoiding the two
forbidden classes modulo nine. -/
def H1 : Prop := ∀ n : ℤ,
    (∀ m : ℕ, 0 < m → ∃ x y z : ZMod m, (n : ZMod m)=x^3+y^3+z^3) ↔
    ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])

/-- The remaining integral local-global implication for the diagonal cubic. -/
def H2 : Prop := ∀ n : ℤ,
    (∀ m : ℕ, 0 < m → ∃ x y z : ZMod m, (n : ZMod m)=x^3+y^3+z^3) →
    SumOfThreeCubes.IsSumOfThreeCubes n

theorem main : H1 → H2 → OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H2 := by
  intro localCriterion globalCriterion n hn
  exact globalCriterion n ((localCriterion n).2 hn)

end OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1
