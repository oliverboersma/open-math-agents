import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1
import Mathlib

/-! Explicit Egyptian fractions for the nonexceptional residue classes. -/

namespace OMA.Erdos242Residues

private theorem expansion {p a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hd : 0 < d) (hp : 0 < p) (hbp : b < c * p) (he : c * p + a + b = 4 * a * b * c * d) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hb : 0 < b := ha.trans hab
  refine ⟨a * b * d, a * c * d * p, b * c * d * p, Nat.one_le_of_lt (by positivity), ?_, ?_, ?_⟩
  · calc
      a * b * d = b * (a * d) := by ac_rfl
      _ < (c * p) * (a * d) := Nat.mul_lt_mul_of_pos_right hbp (Nat.mul_pos ha hd)
      _ = a * c * d * p := by ac_rfl
  · exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hab hc) hd) hp
  have he' : (c : ℚ) * p + a + b = 4 * a * b * c * d := by exact_mod_cast he
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp [ha', hb', hc', hd', hp']
  linear_combination -he'

private theorem residue_cover {r : ℕ} (hr : r < 840) (h24 : r % 24 = 1) (h5 : r % 5 ≠ 0)
    (h7 : r % 7 ≠ 0) (h : ¬ (r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529)) :
    r % 84 = 73 ∨ r % 40 = 33 ∨ r % 20 = 17 ∨ r % 56 = 41 ∨ r % 168 = 145 := by
  let t := r / 24
  have ht : t < 35 := by dsimp [t]; omega
  have he : r = 24 * t + 1 := by dsimp [t]; omega
  clear_value t
  subst r
  interval_cases t <;> norm_num at *

theorem solve (p : ℕ) (hp : p.Prime) (h24 : p % 24 = 1)
    (h : ¬ (p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨ p % 840 = 289 ∨
      p % 840 = 361 ∨ p % 840 = 529)) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hp21 : 21 < p := by have := hp.two_le; omega
  have h5 : p % 5 ≠ 0 := by
    intro h0
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h0) with he | he <;> omega
  have h7 : p % 7 ≠ 0 := by
    intro h0
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h0) with he | he <;> omega
  rcases residue_cover (Nat.mod_lt p (by decide))
    (by simpa only [Nat.mod_mod_of_dvd p (by decide : 24 ∣ 840)] using h24)
    (by simpa only [Nat.mod_mod_of_dvd p (by decide : 5 ∣ 840)] using h5)
    (by simpa only [Nat.mod_mod_of_dvd p (by decide : 7 ∣ 840)] using h7) h
      with h₁ | h₂ | h₃ | h₄ | h₅
  · rw [Nat.mod_mod_of_dvd p (by decide : 84 ∣ 840)] at h₁
    apply expansion (a := 1) (b := 21) (c := 2) (d := (p + 11) / 84) (p := p) <;>
      norm_num <;> omega
  · rw [Nat.mod_mod_of_dvd p (by decide : 40 ∣ 840)] at h₂
    apply expansion (a := 2) (b := 5) (c := 1) (d := (p + 7) / 40) (p := p) <;>
      norm_num <;> omega
  · rw [Nat.mod_mod_of_dvd p (by decide : 20 ∣ 840)] at h₃
    apply expansion (a := 1) (b := 5) (c := 2) (d := (p + 3) / 20) (p := p) <;>
      norm_num <;> omega
  · rw [Nat.mod_mod_of_dvd p (by decide : 56 ∣ 840)] at h₄
    apply expansion (a := 1) (b := 14) (c := 1) (d := (p + 15) / 56) (p := p) <;>
      norm_num <;> omega
  · rw [Nat.mod_mod_of_dvd p (by decide : 168 ∣ 840)] at h₅
    apply expansion (a := 2) (b := 21) (c := 1) (d := (p + 23) / 168) (p := p) <;>
      norm_num <;> omega

end OMA.Erdos242Residues

theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1_H1_R1.H2 :=
  OMA.Erdos242Residues.solve