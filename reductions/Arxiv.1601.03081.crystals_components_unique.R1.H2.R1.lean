import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1

/-! # Shared-divisor normalization for crystal parameters -/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1

def H1 : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < c → a * b = c * d → ¬ Nat.Coprime a c →
    ∃ g x y z : ℕ, 1 < g ∧ a = g * x ∧ c = g * y ∧ b = y * z ∧ d = x * z ∧
      Nat.Coprime x y

def H2 : Prop :=
  ∀ g x y z : ℕ, 1 < g → 0 < x → 0 < y → 0 < z → x ≠ y →
    g * x ≤ y * z → g * y ≤ x * z → Nat.Coprime x y →
    (g * x + 1) * (y * z + 1) ∣ (g * x + y * z) ^ 2 →
    (g * y + 1) * (x * z + 1) ∣ (g * y + x * z) ^ 2 →
      g = z

theorem normalized_shared_divisor {a b c d : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hab : a * b = c * d)
    (hcop : ¬ Nat.Coprime a c) :
    ∃ g x y z : ℕ, 1 < g ∧ a = g * x ∧ c = g * y ∧ b = y * z ∧ d = x * z ∧
      Nat.Coprime x y := by
  let g := Nat.gcd a c
  let x := a / g
  let y := c / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left c ha
  have hgdvd_a : g ∣ a := by dsimp [g]; exact Nat.gcd_dvd_left a c
  have hgdvd_c : g ∣ c := by dsimp [g]; exact Nat.gcd_dvd_right a c
  have hga : a = g * x := by
    dsimp [x]
    exact (Nat.mul_div_cancel' hgdvd_a).symm
  have hgc : c = g * y := by
    dsimp [y]
    exact (Nat.mul_div_cancel' hgdvd_c).symm
  have hcopxy : Nat.Coprime x y := by
    dsimp [x, y, g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hg_gt : 1 < g := by
    by_contra h
    have hg_eq : g = 1 := by omega
    apply hcop
    change Nat.gcd a c = 1
    simpa [g] using hg_eq
  have hcancel : x * b = y * d := by
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc
      g * (x * b) = (g * x) * b := by ring
      _ = a * b := by rw [hga]
      _ = c * d := hab
      _ = (g * y) * d := by rw [hgc]
      _ = g * (y * d) := by ring
  have hy_dvd_b : y ∣ b := by
    apply (hcopxy.symm.dvd_mul_left).mp
    have hdiv : y ∣ x * b := by
      rw [hcancel]
      exact dvd_mul_right y d
    exact hdiv
  have hx_dvd_d : x ∣ d := by
    apply (hcopxy.dvd_mul_left).mp
    have hdiv : x ∣ y * d := by
      rw [← hcancel]
      exact dvd_mul_right x b
    exact hdiv
  let z := b / y
  have hyb : b = y * z := by
    dsimp [z]
    exact (Nat.mul_div_cancel' hy_dvd_b).symm
  have hdy : y * d = y * (x * z) := by
    calc
      y * d = x * b := hcancel.symm
      _ = x * (y * z) := by rw [hyb]
      _ = y * (x * z) := by ring
  have hypos : 0 < y := by
    have hyne : y ≠ 0 := by
      intro hy
      simp [hy] at hgc
      omega
    exact Nat.pos_iff_ne_zero.mpr hyne
  have hd : d = x * z := Nat.eq_of_mul_eq_mul_left hypos hdy
  exact ⟨g, x, y, z, hg_gt, hga, hgc, hyb, hd, hcopxy⟩

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1.H2 := by
  intro hnorm hcore n a b c d hab hcd hab' hcd' hnotcop
  obtain ⟨_, ha, hb, hprod₁, hdiv₁⟩ :=
    (Arxiv.«1601.03081».isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hab
  obtain ⟨_, hc, hd, hprod₂, hdiv₂⟩ :=
    (Arxiv.«1601.03081».isCrystalWithComponents_iff_sum_sq_dvd n c d).mp hcd
  have hprod : a * b = c * d := hprod₁.symm.trans hprod₂
  obtain ⟨g, x, y, z, hg, hax, hcy, hby, hdx, hxy⟩ :=
    hnorm a b c d (by omega) (by omega) hprod hnotcop
  have hxpos : 0 < x := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hx
    simp [hx] at hax
    omega
  have hypos : 0 < y := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hy
    simp [hy] at hcy
    omega
  have hzpos : 0 < z := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    simp [hz] at hby
    omega
  have hsort₁ : g * x ≤ y * z := by rw [← hax, ← hby]; exact hab'
  have hsort₂ : g * y ≤ x * z := by rw [← hcy, ← hdx]; exact hcd'
  have hdiv₁' : (g * x + 1) * (y * z + 1) ∣ (g * x + y * z) ^ 2 := by
    simpa [hax, hby] using hdiv₁
  have hdiv₂' : (g * y + 1) * (x * z + 1) ∣ (g * y + x * z) ^ 2 := by
    simpa [hcy, hdx] using hdiv₂
  by_cases hxy_eq : x = y
  · subst y
    have hac : a = c := by rw [hax, hcy]
    have hprod' : a * b = a * d := by simpa [hac] using hprod
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left (by omega) hprod'
    simp [hac, hbd]
  · have hgz := hcore g x y z hg hxpos hypos hzpos hxy_eq hsort₁ hsort₂ hxy hdiv₁' hdiv₂'
    subst z
    have hn : (g * x + y * g) ^ 2 = (g * y + x * g) ^ 2 := by ring
    have hd : (g * x + 1) * (y * g + 1) = (g * y + 1) * (x * g + 1) := by ring
    rw [hax, hby, hcy, hdx, hn, hd]

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1
