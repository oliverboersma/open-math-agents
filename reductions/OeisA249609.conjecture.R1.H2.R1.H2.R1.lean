import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1

def H1 : Prop :=
  ∀ a : ℕ, 1 ≤ a → Odd a → a ≠ 1 → a ≠ 3 →
    ∃ k ∈ List.range' 1 (2 ^ a), OeisA249609.isEvil ((2 ^ a).choose k) = true

def H2 : Prop :=
  ∀ n : ℕ, 0 < n → Even n → OeisA249609.isEvil n = false →
    n ∉ ({0, 1, 2, 7, 8} : Finset ℕ) → (∀ a : ℕ, n ≠ 2 ^ a) →
    ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true

lemma digits_two_pow_sub_one (a : ℕ) :
    Nat.digits 2 (2 ^ a - 1) = List.replicate a 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hp : 0 < 2 ^ a := by positivity
    have he : 2 ^ (a + 1) - 1 = 1 + 2 * (2 ^ a - 1) := by
      rw [pow_succ]
      omega
    rw [he, Nat.digits_add 2 (by decide) 1 _ (by decide) (Or.inl (by decide)), ih]
    exact List.replicate_succ.symm

lemma choose_power_two_two (a : ℕ) (ha : 1 ≤ a) :
    Nat.choose (2 ^ a) 2 = 2 ^ (a - 1) * (2 ^ a - 1) := by
  rw [Nat.choose_two_right]
  have hp : 2 ^ a = 2 ^ (a - 1) * 2 := by
    nth_rw 1 [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
  have he : 2 ^ a * (2 ^ a - 1) =
      (2 ^ (a - 1) * (2 ^ a - 1)) * 2 := by
    rw [hp]
    ring
  rw [he]
  simp

lemma power_two_second_coefficient_evil (a : ℕ) (ha : 1 ≤ a) (he : Even a) :
    OeisA249609.isEvil (Nat.choose (2 ^ a) 2) = true := by
  have hp : 0 < 2 ^ a := by positivity
  have hgt : 1 < 2 ^ a := by
    have ht := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    norm_num at ht
    omega
  have hpos : 0 < 2 ^ a - 1 := by omega
  have hmod : a % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp he.two_dvd
  unfold OeisA249609.isEvil
  rw [choose_power_two_two a ha, Nat.digits_base_pow_mul (by decide) hpos,
    digits_two_pow_sub_one]
  simp [List.count_replicate, hmod]

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1.H2 := by
  intro hpow hother n hn he hodd hnot
  by_cases hp : ∃ a : ℕ, n = 2 ^ a
  · obtain ⟨a, rfl⟩ := hp
    have ha : 1 ≤ a := by
      by_contra h
      have : a = 0 := by omega
      subst a
      norm_num at hnot
    rcases Nat.even_or_odd a with haeven | haodd
    · have hbig : 2 ≤ 2 ^ a := by
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) ha)
      refine ⟨2, ?_, power_two_second_coefficient_evil a ha haeven⟩
      apply List.mem_range'.2
      exact ⟨1, by omega, by simp⟩
    · have ha1 : a ≠ 1 := by
        intro h; subst a; norm_num at hnot
      have ha3 : a ≠ 3 := by
        intro h; subst a; norm_num at hnot
      exact hpow a ha haodd ha1 ha3
  · exact hother n hn he hodd hnot (by simpa only [not_exists] using hp)

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1
