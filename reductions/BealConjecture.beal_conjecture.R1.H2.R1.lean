import OMAReductions.R_BealConjecture_beal_conjecture_R1
import Mathlib.NumberTheory.FLT.Four

/-!
# Fourth-power signatures in Beal's conjecture

Reduction of BealConjecture.beal_conjecture.R1.H2 into four independent signatures.
The all-fourth-powers case follows from Fermat's Last Theorem for exponent four.
Credit: @rgoldman73-dev.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R1_H2_R1

/-- Two fourth powers on the left and an odd prime exponent on the right. -/
def H1 : Prop :=
  ∀ {A B C p : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < p → p.Prime →
    A ^ 4 + B ^ 4 = C ^ p → ∃ r : ℕ, r.Prime ∧ r ∣ A ∧ r ∣ B ∧ r ∣ C

/-- A fourth power on each side and an odd prime exponent on the remaining term. -/
def H2 : Prop :=
  ∀ {A B C p : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < p → p.Prime →
    A ^ 4 + B ^ p = C ^ 4 → ∃ r : ℕ, r.Prime ∧ r ∣ A ∧ r ∣ B ∧ r ∣ C

/-- One fourth power on the left and odd prime exponents on the other terms. -/
def H3 : Prop :=
  ∀ {A B C p q : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 →
    2 < p → p.Prime → 2 < q → q.Prime →
    A ^ 4 + B ^ p = C ^ q → ∃ r : ℕ, r.Prime ∧ r ∣ A ∧ r ∣ B ∧ r ∣ C

/-- A fourth power on the right and odd prime exponents on the left. -/
def H4 : Prop :=
  ∀ {A B C p q : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 →
    2 < p → p.Prime → 2 < q → q.Prime →
    A ^ p + B ^ q = C ^ 4 → ∃ r : ℕ, r.Prime ∧ r ∣ A ∧ r ∣ B ∧ r ∣ C

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R1.H2 := by
  intro h1 h2 h3 h4 A B C x y z hA hB hC hx hy hz hfour heq
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rcases hz with rfl | hz
      · exact (fermatLastTheoremFour A B C hA hB hC heq).elim
      · exact h1 hA hB hC hz.1 hz.2 heq
    · rcases hz with rfl | hz
      · exact h2 hA hB hC hy.1 hy.2 heq
      · exact h3 hA hB hC hy.1 hy.2 hz.1 hz.2 heq
  · rcases hy with rfl | hy
    · rcases hz with rfl | hz
      · obtain ⟨r, hr, hrB, hrA, hrC⟩ :=
          h2 hB hA hC hx.1 hx.2 (by simpa only [Nat.add_comm] using heq)
        exact ⟨r, hr, hrA, hrB, hrC⟩
      · obtain ⟨r, hr, hrB, hrA, hrC⟩ :=
          h3 hB hA hC hx.1 hx.2 hz.1 hz.2 (by simpa only [Nat.add_comm] using heq)
        exact ⟨r, hr, hrA, hrB, hrC⟩
    · rcases hz with rfl | hz
      · exact h4 hA hB hC hx.1 hx.2 hy.1 hy.2 heq
      · rcases hfour with hx4 | hy4 | hz4
        · subst x
          norm_num at hx
        · subst y
          norm_num at hy
        · subst z
          norm_num at hz

end OMA.R_BealConjecture_beal_conjecture_R1_H2_R1
