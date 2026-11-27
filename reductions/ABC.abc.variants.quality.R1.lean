import FormalConjectures.Wikipedia.ABC
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree

/-!
If the sum or the product of the summands is squarefree, the radical is
at least the sum. The logarithmic inequality therefore reduces to a
power inequality on triples with repeated prime factors on both sides.
-/

namespace OMA.R_ABC_abc_variants_quality_R1

def H1 : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →
    a + b = c →
    1 < ABC.radical (a * b * c) ∧
      ((Squarefree c ∨ Squarefree (a * b)) → c ≤ ABC.radical (a * b * c))

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ |
      0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ ¬ Squarefree c ∧ ¬ Squarefree (a * b) ∧
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)}.Finite

section Proof

private theorem quality_gt_iff (a b c : ℕ) (hc : 0 < c)
    (hrad : 1 < ABC.radical (a * b * c)) (ε : ℝ) :
    1 + ε < ABC.quality a b c ↔
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ) := by
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hr' : (1 : ℝ) < (ABC.radical (a * b * c) : ℝ) := by exact_mod_cast hrad
  have hrs : (0 : ℝ) < (ABC.radical (a * b * c) : ℝ) := by linarith
  rw [ABC.quality, lt_div_iff₀ (Real.log_pos hr'),
    ← Real.log_rpow hrs, Real.log_lt_log_iff (Real.rpow_pos_of_pos hrs _) hc']

theorem main : H1 → H2 → type_of% @ABC.abc.variants.quality := by
  intro radicalBound finiteCritical ε hε
  apply (finiteCritical ε hε).subset
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hcop, hsum, hquality⟩
  have ⟨hrad, hsquarefree⟩ := radicalBound a b c ha hb hcop hsum
  have hpower := (quality_gt_iff a b c hc hrad ε).mp hquality
  have hbad : ¬ (Squarefree c ∨ Squarefree (a * b)) := by
    intro hs
    have hcle : (c : ℝ) ≤ (ABC.radical (a * b * c) : ℝ) := by
      exact_mod_cast hsquarefree hs
    have hone : (1 : ℝ) ≤ (ABC.radical (a * b * c) : ℝ) := by exact_mod_cast hrad.le
    have hle := Real.self_le_rpow_of_one_le hone (by linarith : (1 : ℝ) ≤ 1 + ε)
    exact (not_lt_of_ge (hcle.trans hle)) hpower
  exact ⟨ha, hb, hc, hcop, hsum, fun h => hbad (Or.inl h),
    fun h => hbad (Or.inr h), hpower⟩

end Proof

end OMA.R_ABC_abc_variants_quality_R1
