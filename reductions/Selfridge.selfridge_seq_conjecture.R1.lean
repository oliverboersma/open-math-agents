import FormalConjectures.Wikipedia.Selfridge

-- Credit: @Optymyzt
namespace OMA.R_Selfridge_selfridge_seq_conjecture_R1

-- Six pairwise coprime divisors of F12 and a coprime cofactor that is
-- composite and not a perfect power give this lower bound.
def H1 : Prop := 8 ≤ Selfridge.fermatFactors 12

-- Any later Fermat number with at most seven distinct prime factors suffices.
def H2 : Prop := ∃ n : ℕ, 12 < n ∧ Selfridge.fermatFactors n ≤ 7

theorem main : H1 → H2 → type_of% @Selfridge.selfridge_seq_conjecture := by
  intro h₁ h₂ hmono
  obtain ⟨n, hn, hcount⟩ := h₂
  have hlow : 8 ≤ Selfridge.fermatFactors 12 := h₁
  have hle : Selfridge.fermatFactors 12 ≤ Selfridge.fermatFactors n := hmono hn.le
  omega

end OMA.R_Selfridge_selfridge_seq_conjecture_R1
