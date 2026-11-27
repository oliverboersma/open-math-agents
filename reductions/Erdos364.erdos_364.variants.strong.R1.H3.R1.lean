import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1

/-! Reduce the Erdős–Mollin–Walsh conjecture by locating a square in the least
hypothetical triple, or factoring all three nonsquare terms. -/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1

private theorem prime_sq_dvd {n p : ℕ} (hn : n.Powerful) (hp : p.Prime)
    (hd : p ∣ n) : p ^ 2 ∣ n := by
  by_cases hz : n = 0
  · simp [hz]
  · exact hn p (Nat.mem_primeFactors.mpr ⟨hp, hd, hz⟩)

private theorem powerful_of_coprime_factor {a b : ℕ} (hab : a.Coprime b)
    (h : (a * b).Powerful) : a.Powerful := by
  intro p hp
  obtain ⟨hpPrime, hpa, _⟩ := Nat.mem_primeFactors.mp hp
  have hpb : (p ^ 2).Coprime b :=
    (Nat.coprime_pow_left_iff (by decide : 0 < (2 : ℕ)) p b).mpr
      (hab.coprime_dvd_left hpa)
  exact hpb.dvd_of_dvd_mul_right (prime_sq_dvd h hpPrime (hpa.mul_right b))

private theorem four_dvd_of_even {n : ℕ} (h : n.Powerful) (he : n % 2 = 0) :
    n % 4 = 0 :=
  Nat.dvd_iff_mod_eq_zero.mp (prime_sq_dvd h Nat.prime_two (Nat.dvd_of_mod_eq_zero he))

private theorem nine_dvd_of_three_dvd {n : ℕ} (h : n.Powerful) (he : n % 3 = 0) :
    n % 9 = 0 :=
  Nat.dvd_iff_mod_eq_zero.mp (prime_sq_dvd h Nat.prime_three (Nat.dvd_of_mod_eq_zero he))

private theorem start_mod_four {a : ℕ} (ha : a.Powerful) (hb : (a + 1).Powerful)
    (hc : (a + 2).Powerful) : a % 4 = 3 := by
  have h₀ := four_dvd_of_even ha
  have h₁ := four_dvd_of_even hb
  have h₂ := four_dvd_of_even hc
  omega

/-- The congruence classes from Beckon, On Consecutive Triples Of Powerful Numbers. -/
private theorem start_mod_thirty_six {a : ℕ} (ha : a.Powerful) (hb : (a + 1).Powerful)
    (hc : (a + 2).Powerful) : a % 36 = 7 ∨ a % 36 = 27 ∨ a % 36 = 35 := by
  have h₀ := nine_dvd_of_three_dvd ha
  have h₁ := nine_dvd_of_three_dvd hb
  have h₂ := nine_dvd_of_three_dvd hc
  have hmod3 (i : ℕ) : (a + i) % 3 = (a % 9 + i) % 3 := by
    rw [Nat.add_mod (a % 9) i 3, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)]
    exact Nat.add_mod a i 3
  have hmod9 (i : ℕ) : (a + i) % 9 = (a % 9 + i) % 9 := by
    rw [Nat.add_mod (a % 9) i 9, Nat.mod_mod]
    exact Nat.add_mod a i 9
  rw [← Nat.mod_mod_of_dvd a (by decide : 3 ∣ 9)] at h₀
  rw [hmod3 1, hmod9 1] at h₁
  rw [hmod3 2, hmod9 2] at h₂
  have h₉ : a % 9 = 0 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
    have hlt : a % 9 < 9 := Nat.mod_lt _ (by decide)
    interval_cases hr : a % 9 <;>
      norm_num at h₀ <;> norm_num at h₁ <;> norm_num at h₂ <;> decide
  have h₄ := start_mod_four ha hb hc
  omega

private theorem square_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [pow_two, Nat.mul_mod]
  have h : x % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases hx : x % 2 <;> decide

private theorem square_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [pow_two, Nat.mul_mod]
  have h : x % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hx : x % 4 <;> decide

/-- Adapted from the factorization argument in Mian and Siddique, arXiv:2609.25011.
Lean source at https://github.com/ibrahimmian36/Optio/blob/main/Erdos364/Representation.lean
Copyright (c) 2026 Millennium Research, Apache-2.0. -/
private theorem nonsquare_representation {n : ℕ} (hn : n.Powerful)
    (h : ¬ ∃ x : ℕ, n = x ^ 2) :
    ∃ x u : ℕ, 1 < u ∧ Squarefree u ∧ n = x ^ 2 * u ^ 3 := by
  have hn0 : n ≠ 0 := fun hz => h ⟨0, by simp [hz]⟩
  obtain ⟨u, s, hu, hs, hprod, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn0)
  have hu0 := hu.ne'
  have hs0 := hs.ne'
  have hfact : n.factorization = 2 • s.factorization + u.factorization := by
    rw [← hprod, Nat.factorization_mul (pow_ne_zero 2 hs0) hu0, Nat.factorization_pow]
  have hdiv : u ∣ s := by
    rw [← Nat.factorization_le_iff_dvd hu0 hs0, Finsupp.le_iff]
    intro p hp
    have hpu : p ∈ u.primeFactors := Nat.support_factorization u ▸ hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpu
    have hpn : p ∣ n := hprod ▸ (hpd.mul_left (s ^ 2))
    have h₂ := (Nat.Prime.pow_dvd_iff_le_factorization hpp hn0).mp (prime_sq_dvd hn hpp hpn)
    have h₁ := (Nat.squarefree_iff_factorization_le_one hu0).mp hsf p
    have he : n.factorization p = 2 * s.factorization p + u.factorization p := by
      simp [hfact, Finsupp.add_apply, two_smul, two_mul]
    omega
  obtain ⟨x, hx⟩ := hdiv
  have he : n = x ^ 2 * u ^ 3 := by
    rw [← hprod, hx]
    ring
  refine ⟨x, u, ?_, hsf, he⟩
  by_contra! hle
  have hu1 : u = 1 := by omega
  exact h ⟨x, by simpa [hu1] using he⟩

private theorem cube_factor_dvd (x u : ℕ) : u ∣ x ^ 2 * u ^ 3 :=
  (dvd_pow_self u (by decide : (3 : ℕ) ≠ 0)).mul_left (x ^ 2)

/-- The middle term of a least counterexample is a square. Its predecessor factors
into the odd, coprime neighbors of the square root. A powerful square root
would itself be the center of a smaller counterexample. -/
def H1 : Prop :=
  ¬ ∃ x : ℕ, 2 ≤ x ∧ x % 2 = 0 ∧ ¬ x.Powerful ∧
    (x - 1).Powerful ∧ (x + 1).Powerful ∧ (x ^ 2 + 1).Powerful

/-- The final term is an odd square, written as `(2 * k + 1)^2`. -/
def H2 : Prop :=
  ¬ ∃ k : ℕ, 1 ≤ k ∧
    (4 * k * (k + 1) - 1).Powerful ∧ (4 * k * (k + 1)).Powerful

/-- All three terms are nonsquares. The squarefree cube factors are
pairwise coprime, and the first term satisfies the local conditions at 2 and 3. -/
def H3 : Prop :=
  ¬ ∃ x y z u v w : ℕ,
    1 < u ∧ 1 < v ∧ 1 < w ∧
    Squarefree u ∧ Squarefree v ∧ Squarefree w ∧
    u.Coprime v ∧ u.Coprime w ∧ v.Coprime w ∧
    ((x ^ 2 * u ^ 3) % 36 = 7 ∨ (x ^ 2 * u ^ 3) % 36 = 27 ∨
      (x ^ 2 * u ^ 3) % 36 = 35) ∧
    x ^ 2 * u ^ 3 + 1 = y ^ 2 * v ^ 3 ∧
    y ^ 2 * v ^ 3 + 1 = z ^ 2 * w ^ 3

theorem main : H1 → H2 → H3 → OMA.R_Erdos364_erdos_364_variants_strong_R1.H3 := by
  classical
  intro hmiddle hlast hgeneral hCounterexample
  let a := Nat.find hCounterexample
  have htriple : a.Powerful ∧ (a + 1).Powerful ∧ (a + 2).Powerful :=
    Nat.find_spec hCounterexample
  obtain ⟨ha, hb, hc⟩ := htriple
  have h₄ := start_mod_four ha hb hc
  have hfirst : ¬ ∃ x : ℕ, a = x ^ 2 := by
    rintro ⟨x, hx⟩
    have hs := square_mod_four x
    omega
  by_cases hs : ∃ x : ℕ, a + 1 = x ^ 2
  · obtain ⟨x, hx⟩ := hs
    have hxe : x % 2 = 0 := by
      have hb₂ : x ^ 2 % 2 = 0 := by omega
      rwa [square_mod_two] at hb₂
    have hxpos : 2 ≤ x := by
      by_contra! hn
      interval_cases x <;> norm_num at *
    have hfac : (x - 1) * (x + 1) = a := by
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = k + 1 := ⟨x - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at *
      nlinarith
    have hcop : (x - 1).Coprime (x + 1) := by
      have hodd : Odd (x - 1) := Nat.odd_iff.mpr (by omega)
      have he : x + 1 = (x - 1) + 2 := by omega
      rw [he, Nat.coprime_self_add_right, Nat.coprime_two_right]
      exact hodd
    have hprod : ((x - 1) * (x + 1)).Powerful := hfac.symm ▸ ha
    have hprev := powerful_of_coprime_factor hcop hprod
    have hnext := powerful_of_coprime_factor hcop.symm (Nat.mul_comm _ _ ▸ hprod)
    have hroot : ¬ x.Powerful := by
      intro hxpow
      have he₁ : x - 1 + 1 = x := by omega
      have he₂ : x - 1 + 2 = x + 1 := by omega
      have hmin : a ≤ x - 1 :=
        Nat.find_min' hCounterexample ⟨hprev, he₁.symm ▸ hxpow, he₂.symm ▸ hnext⟩
      have hbound : 2 * x ≤ x ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_right x hxpos
      omega
    have hsucc : x ^ 2 + 1 = a + 2 := by omega
    exact hmiddle ⟨x, hxpos, hxe, hroot, hprev, hnext, hsucc.symm ▸ hc⟩
  by_cases hs' : ∃ x : ℕ, a + 2 = x ^ 2
  · obtain ⟨x, hx⟩ := hs'
    have hxo : x % 2 = 1 := by
      have hc₂ : x ^ 2 % 2 = 1 := by omega
      rwa [square_mod_two] at hc₂
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    have hmid : a + 1 = 4 * k * (k + 1) := by nlinarith
    have hk : 1 ≤ k := by
      by_contra! hn
      have : k = 0 := by omega
      simp [this] at hmid
    have hstart : 4 * k * (k + 1) - 1 = a := by omega
    exact hlast ⟨k, hk, hstart.symm ▸ ha, hmid ▸ hb⟩
  obtain ⟨x, u, hu, hus, hxa⟩ := nonsquare_representation ha hfirst
  obtain ⟨y, v, hv, hvs, hyb⟩ := nonsquare_representation hb hs
  obtain ⟨z, w, hw, hws, hzc⟩ := nonsquare_representation hc hs'
  have hud : u ∣ a := hxa.symm ▸ cube_factor_dvd x u
  have hvd : v ∣ a + 1 := hyb.symm ▸ cube_factor_dvd y v
  have hwd : w ∣ a + 2 := hzc.symm ▸ cube_factor_dvd z w
  have hab : a.Coprime (a + 1) := by simp [Nat.coprime_self_add_right]
  have hac : a.Coprime (a + 2) := by
    rw [Nat.coprime_self_add_right, Nat.coprime_two_right, Nat.odd_iff]
    omega
  have hbc : (a + 1).Coprime (a + 2) := by
    simpa [Nat.coprime_self_add_right, Nat.add_assoc] using
      (show (a + 1).Coprime ((a + 1) + 1) by simp [Nat.coprime_self_add_right])
  exact hgeneral ⟨x, y, z, u, v, w, hu, hv, hw, hus, hvs, hws,
    (hab.coprime_dvd_left hud).coprime_dvd_right hvd,
    (hac.coprime_dvd_left hud).coprime_dvd_right hwd,
    (hbc.coprime_dvd_left hvd).coprime_dvd_right hwd,
    hxa ▸ start_mod_thirty_six ha hb hc, by omega, by omega⟩

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1
