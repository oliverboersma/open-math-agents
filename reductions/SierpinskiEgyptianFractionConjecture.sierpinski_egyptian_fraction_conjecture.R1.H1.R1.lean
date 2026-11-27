import OMAReductions.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1

open SierpinskiEgyptianFractionConjecture

-- Reduction SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture.R1.H1.R1 of step SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture.R1.H1
-- Credit: @senamakel

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1

lemma decomp_of_p_plus_five_divisor (p d : ℕ) (h180 : p % 180 = 1)
    (hd : d ∣ p + 5) (hd5 : d % 5 = 4) : HasSierpinskiDecomposition p := by
  let a := (p + 4) / 5
  let t := (d - 4) / 5
  have hp5 : p % 5 = 1 := by omega
  have ha : 5 * a = p + 4 := by
    dsimp [a]
    omega
  have hdt : d = 5 * t + 4 := by
    dsimp [t]
    omega
  let x := a + t
  have hpx : 5 * x = p + d := by
    dsimp [x]
    omega
  have hmul : 5 * (x + 1) = p + 5 + d := by
    dsimp [x]
    omega
  have hcop : Nat.Coprime d 5 := by
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro h5d
    have hz : d % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5d
    omega
  have hxdiv : d ∣ x + 1 := by
    obtain ⟨k, hk⟩ := hd
    have hdx : d ∣ 5 * (x + 1) := by
      refine ⟨k + 1, ?_⟩
      rw [hmul, hk]
      ring
    exact hcop.dvd_mul_left.mp hdx
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_remainder
    (p := p) (a := x) (t := d) (q := x) (by omega) (by omega) hpx ?_ hxdiv
  exact ⟨p, by ring⟩

lemma decomp_of_p_sq_plus_five_divisor (p d : ℕ) (hp : p.Prime)
    (h180 : p % 180 = 1) (hd : d ∣ p ^ 2 + 5) (hd5 : d % 5 = 4) :
    HasSierpinskiDecomposition p := by
  let x := (p + d) / 5
  have hp5 : p % 5 = 1 := by omega
  have hx : 5 * x = p + d := by
    dsimp [x]
    omega
  have hcop : Nat.Coprime d 5 := by
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro h5d
    have hz : d % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5d
    omega
  have hdN : d ∣ p * x + 1 := by
    obtain ⟨k, hk⟩ := hd
    have hmul : 5 * (p * x + 1) = p ^ 2 + p * d + 5 := by
      calc
        5 * (p * x + 1) = p * (5 * x) + 5 := by ring
        _ = p * (p + d) + 5 := by rw [hx]
        _ = p ^ 2 + p * d + 5 := by ring
    have hd5mul : d ∣ 5 * (p * x + 1) := by
      refine ⟨k + p, ?_⟩
      calc
        5 * (p * x + 1) = p ^ 2 + p * d + 5 := hmul
        _ = d * k + p * d := by rw [← hk]; ring
        _ = d * (k + p) := by ring
    exact hcop.dvd_mul_left.mp hd5mul
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_remainder
    (p := p) (a := x) (t := d) (q := p * x) hp.pos (by omega) hx (dvd_refl _) hdN

lemma decomp_of_p_plus_one_divisor (p d : ℕ) (hp : p.Prime)
    (h180 : p % 180 = 1) (hd : d ∣ p + 1) (hd5 : d % 5 = 4) :
    HasSierpinskiDecomposition p := by
  let x := (p + d) / 5
  let b := (p + 1) / d
  have hp5 : p % 5 = 1 := by omega
  have hx : 5 * x = p + d := by
    dsimp [x]
    omega
  have hdb : d * b = p + 1 := by
    dsimp [b]
    exact Nat.mul_div_cancel' hd
  have hb : 0 < b := by
    have hb0 : b ≠ 0 := by
      intro h0
      have htmp := hdb
      rw [h0, Nat.mul_zero] at htmp
      omega
    exact Nat.pos_of_ne_zero hb0
  have hxpos : 0 < x := by omega
  have hypos : 0 < x * b := Nat.mul_pos hxpos hb
  have hzpos : 0 < p * x * b := Nat.mul_pos (Nat.mul_pos hp.pos hxpos) hb
  apply OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.decomposition_of_identity
    (n := p) (x := x) (y := x * b) (z := p * x * b) hp.pos hxpos hypos hzpos ?_
  calc
    5 * x * (x * b) * (p * x * b) = p * x ^ 2 * b ^ 2 * (5 * x) := by ring
    _ = p * x ^ 2 * b ^ 2 * (p + d) := by rw [hx]
    _ = p * x ^ 2 * b * (p * b + (p + 1)) := by rw [← hdb]; ring
    _ = p * ((x * b) * (p * x * b) + x * (p * x * b) + x * (x * b)) := by ring

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) →
    ((p + 5) / 6).Prime →
    HasSierpinskiDecomposition p

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) →
    ¬ ((p + 5) / 6).Prime →
    HasSierpinskiDecomposition p

theorem main : H1 → H2 → OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1.H1 := by
  intro hPrime hComposite p hp h180 hlarge hq
  by_cases h5 : ∃ d : ℕ, d ∣ p + 5 ∧ d % 5 = 4
  · obtain ⟨d, hd, hd5⟩ := h5
    exact decomp_of_p_plus_five_divisor p d h180 hd hd5
  by_cases hsq5 : ∃ d : ℕ, d ∣ p ^ 2 + 5 ∧ d % 5 = 4
  · obtain ⟨d, hd, hd5⟩ := hsq5
    exact decomp_of_p_sq_plus_five_divisor p d hp h180 hd hd5
  by_cases h1 : ∃ d : ℕ, d ∣ p + 1 ∧ d % 5 = 4
  · obtain ⟨d, hd, hd5⟩ := h1
    exact decomp_of_p_plus_one_divisor p d hp h180 hd hd5
  have hno5 : ∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4 := by
    intro d hd hd5
    exact h5 ⟨d, hd, hd5⟩
  have hnosq5 : ∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4 := by
    intro d hd hd5
    exact hsq5 ⟨d, hd, hd5⟩
  have hno1 : ∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4 := by
    intro d hd hd5
    exact h1 ⟨d, hd, hd5⟩
  by_cases hN : ((p + 5) / 6).Prime
  · exact hPrime p hp h180 hlarge hq hno5 hnosq5 hno1 hN
  · exact hComposite p hp h180 hlarge hq hno5 hnosq5 hno1 hN

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1
