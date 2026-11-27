import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1

/-!
# Coprime crystal pairs share a cross multiplier

If the smaller components a and c are coprime and their products agree,
the factorizations are (a, c*m) and (c, a*m). The multiplier is odd, the
case m = 1 is identical after sorting, and sorting bounds each smaller
component by m times the other. Separate the first remaining multiplier
m = 3 from the variable-multiplier problem. The former has only two free
component variables with a ratio between one third and three.
-/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1

open Arxiv.«1601.03081»

def H1 : Prop :=
  ∀ a c : ℕ, a.Coprime c → a ≤ c * 3 → c ≤ a * 3 →
    IsCrystalWithComponents (a * (c * 3)) a (c * 3) →
    IsCrystalWithComponents (a * (c * 3)) c (a * 3) →
    (a + c * 3)^2 / ((a + 1) * (c * 3 + 1)) =
      (c + a * 3)^2 / ((c + 1) * (a * 3 + 1))

def H2 : Prop :=
  ∀ a c m : ℕ, 5 ≤ m → Odd m → a.Coprime c → a ≤ c * m → c ≤ a * m →
    IsCrystalWithComponents (a * (c * m)) a (c * m) →
    IsCrystalWithComponents (a * (c * m)) c (a * m) →
    (a + c * m)^2 / ((a + 1) * (c * m + 1)) =
      (c + a * m)^2 / ((c + 1) * (a * m + 1))

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1.H1 := by
  intro hthree hlarge n a b c d hab hcd hs ht hcop
  have hn₁ := hab.2.2.2.1
  have hn₂ := hcd.2.2.2.1
  have ha : 0 < a := by have := hab.2.1; omega
  have hdvd : a ∣ d := hcop.dvd_of_dvd_mul_left
    ⟨b, hn₂.symm.trans hn₁⟩
  obtain ⟨m, rfl⟩ := hdvd
  have he : a * b = a * (c * m) := by
    calc
      a * b = n := hn₁.symm
      _ = c * (a * m) := hn₂
      _ = a * (c * m) := by ac_rfl
  have hb : b = c * m := Nat.eq_of_mul_eq_mul_left ha he
  subst b
  have hm : Odd m := Nat.Odd.of_mul_right (Nat.Odd.of_mul_right (hn₁ ▸ hab.1))
  rw [hn₁] at hab hcd
  obtain h | h | h : m = 1 ∨ m = 3 ∨ 5 ≤ m := by
    obtain ⟨z, hz⟩ := hm
    omega
  · subst m
    simp only [mul_one] at hs ht ⊢
    have : a = c := le_antisymm hs ht
    subst c
    rfl
  · subst m
    exact hthree a c hcop hs ht hab hcd
  · exact hlarge a c m h hm hcop hs ht hab hcd

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1
