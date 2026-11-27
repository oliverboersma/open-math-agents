import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @anmolspace
-- Proof: 509203 is a Riesel number. 2^24 = 1 mod 5592405 = 3*5*7*13*17*241, so 509203 * 2^m mod
-- 5592405 depends only on m mod 24, and for each residue one of 3, 5, 7, 13, 17, 241 divides
-- 509203 * 2^m - 1 (checked by decide); that number exceeds 241, so it is never prime.

namespace OMA.SA108129

lemma period (m : ℕ) : (509203 * 2 ^ (m + 24)) % 5592405 = (509203 * 2 ^ m) % 5592405 := by
  rw [pow_add, ← mul_assoc, Nat.mul_mod, show 2 ^ 24 % 5592405 = 1 by norm_num, mul_one,
    Nat.mod_mod]

lemma reduce (m : ℕ) : (509203 * 2 ^ m) % 5592405 = (509203 * 2 ^ (m % 24)) % 5592405 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 24
    · rw [Nat.mod_eq_of_lt hm]
    · have e : m = (m - 24) + 24 := by omega
      rw [e, period, ih (m - 24) (by omega)]
      congr 3
      omega

set_option maxRecDepth 100000 in
lemma cover : ∀ r < 24, ∃ p < 242, 3 ≤ p ∧ p ∣ 5592405 ∧ (509203 * 2 ^ r) % 5592405 % p = 1 := by
  decide

lemma key (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hpr
  obtain ⟨p, hp242, hp3, hpP, hmod⟩ := cover (m % 24) (Nat.mod_lt _ (by norm_num))
  rw [← reduce, Nat.mod_mod_of_dvd _ hpP] at hmod
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    have := Nat.dvd_sub_mod (n := p) (509203 * 2 ^ m)
    rwa [hmod] at this
  have hbig : 509203 * 2 ≤ 509203 * 2 ^ m := by
    apply Nat.mul_le_mul_left
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h | h <;> omega

end OMA.SA108129

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  have hno : ¬ ∃ m, m ≠ 0 ∧ ((2 * 254602 - 1) * 2 ^ m - 1).Prime := by
    rintro ⟨m, hm, hp⟩
    have e : 2 * 254602 - 1 = 509203 := by norm_num
    rw [e] at hp
    exact OMA.SA108129.key m hm hp
  show OeisA108129.a 254602 = -1
  unfold OeisA108129.a
  rw [if_neg (by norm_num), dif_neg hno]
