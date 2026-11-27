import OMAReductions.R_Erdos137_erdos_137_R1_H2_R1

-- Step Erdos137.erdos_137.R1.H2.R1.H2
-- Credit: @caa1982

open Finset

private lemma prod_Ico_four (a : ℕ) :
    ∏ x ∈ Ico a (a + 4), x = a * (a + 1) * (a + 2) * (a + 3) := by
  have h : Ico a (a + 4) = {a, a + 1, a + 2, a + 3} := by
    ext x
    simp only [mem_Ico, mem_insert, mem_singleton]
    omega
  rw [h, prod_insert (by simp), prod_insert (by simp), prod_insert (by simp), prod_singleton]
  ring

private lemma four_dvd_prod_four (a : ℕ) : 4 ∣ a * (a + 1) * (a + 2) * (a + 3) := by
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨k * (2 * k + 1) * (k + 1) * (2 * k + 3), ?_⟩; ring
  · refine ⟨(2 * k + 1) * (k + 1) * (2 * k + 3) * (k + 2), ?_⟩; ring

private lemma nine_dvd_prod_four_iff (a : ℕ) :
    9 ∣ a * (a + 1) * (a + 2) * (a + 3) ↔ a % 3 = 0 ∨ 9 ∣ a + 3 - a % 3 := by
  have hmod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · rw [show (a % 3 = 0 ∨ 9 ∣ a + 3 - a % 3) ↔ True by simp [h0], iff_true]
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk]
    refine ⟨k * (3 * k + 1) * (3 * k + 2) * (k + 1), ?_⟩
    ring
  · have hsub : a + 3 - a % 3 = a + 2 := by omega
    rw [hsub]
    simp only [h1, one_ne_zero, false_or]
    have hcop : Nat.Coprime 9 (a * (a + 1) * (a + 3)) := by
      rw [show (9 : ℕ) = 3 ^ 2 by decide]
      apply Nat.Coprime.pow_left
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_ <;>
      · rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
        omega
    rw [show a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 1) * (a + 3)) * (a + 2) by ring]
    exact hcop.dvd_mul_left
  · have hsub : a + 3 - a % 3 = a + 1 := by omega
    rw [hsub]
    simp only [h2, OfNat.ofNat_ne_zero, false_or]
    have hcop : Nat.Coprime 9 (a * (a + 2) * (a + 3)) := by
      rw [show (9 : ℕ) = 3 ^ 2 by decide]
      apply Nat.Coprime.pow_left
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_ <;>
      · rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
        omega
    rw [show a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 2) * (a + 3)) * (a + 1) by ring]
    exact hcop.dvd_mul_left

private lemma three_dvd_prod_four (a : ℕ) : 3 ∣ a * (a + 1) * (a + 2) * (a + 3) := by
  have hmod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h0) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _) _

theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H2_R1.H2 := by
  intro a ha
  set P := ∏ x ∈ Ico a (a + 4), x
  have hPeq : P = a * (a + 1) * (a + 2) * (a + 3) := prod_Ico_four a
  have hPpos : 0 < P := by rw [hPeq]; positivity
  constructor
  · intro hpow
    refine ⟨?_, ?_⟩
    · intro x hx p hp hp3 hpx
      have hpP : p ∣ P := dvd_trans hpx (Finset.dvd_prod_of_mem _ hx)
      have hp2P : p ^ 2 ∣ P := hpow p (Nat.mem_primeFactors.mpr ⟨hp, hpP, hPpos.ne'⟩)
      have hPsplit : P = x * ∏ y ∈ (Ico a (a + 4)).erase x, y :=
        (Finset.mul_prod_erase (Ico a (a + 4)) id hx).symm
      have hcop : Nat.Coprime (p ^ 2) (∏ y ∈ (Ico a (a + 4)).erase x, y) := by
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.prod_right
        intro y hy
        rw [hp.coprime_iff_not_dvd]
        intro hpy
        have hne : y ≠ x := (Finset.mem_erase.mp hy).1
        have hxI := Finset.mem_Ico.mp hx
        have hyI := Finset.mem_Ico.mp (Finset.mem_erase.mp hy).2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hdvd : p ∣ x - y := Nat.dvd_sub hpx hpy
          have hle := Nat.le_of_dvd (by omega) hdvd
          omega
        · have hdvd : p ∣ y - x := Nat.dvd_sub hpy hpx
          have hle := Nat.le_of_dvd (by omega) hdvd
          omega
      rw [hPsplit, mul_comm] at hp2P
      exact hcop.dvd_of_dvd_mul_left hp2P
    · rw [← nine_dvd_prod_four_iff, ← hPeq]
      have h3P : 3 ∣ P := hPeq ▸ three_dvd_prod_four a
      exact hpow 3 (Nat.mem_primeFactors.mpr ⟨by decide, h3P, hPpos.ne'⟩)
  · rintro ⟨hgt3, h3⟩
    intro p hpP
    obtain ⟨hp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hpP
    by_cases hp2 : p = 2
    · subst hp2
      rw [hPeq]
      exact four_dvd_prod_four a
    · by_cases hp3 : p = 3
      · subst hp3
        rw [hPeq]
        exact (nine_dvd_prod_four_iff a).mpr h3
      · have hp_gt3 : 3 < p := by have := hp.two_le; omega
        obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpdvd
        exact dvd_trans (hgt3 x hx p hp hp_gt3 hpx) (Finset.dvd_prod_of_mem _ hx)
