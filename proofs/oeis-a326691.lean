import OMAStatements.S_oeis_a326691
import Mathlib.Tactic

namespace ReciprocalDerivativeProof

open Finset OMA.S_oeis_a326691

private def cofactorSum (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n / p

/-- After multiplying by n, the reciprocal sum has the integer numerator S−1. -/
private lemma denominator_formula {n : ℕ} (hn : 0 < n) :
    sequence n = n.gcd ((cofactorSum n : ℤ) - 1).natAbs := by
  have nonzero : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have clear_den : (∑ p ∈ n.primeFactors, (1 : ℚ) / p) * n = (cofactorSum n : ℚ) := by
    rw [sum_mul]
    simp only [cofactorSum, Nat.cast_sum]
    refine sum_congr rfl fun p hp => ?_
    have hd := Nat.dvd_of_mem_primeFactors hp
    have nz : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have prod : ((n / p : ℕ) : ℚ) * p = n := by exact_mod_cast Nat.div_mul_cancel hd
    field_simp
    linear_combination -prod
  have fraction : (∑ p ∈ n.primeFactors, (1 : ℚ) / p) - 1 / (n : ℚ) =
      mkRat ((cofactorSum n : ℤ)-1) n := by
    rw [Rat.mkRat_eq_div, eq_div_iff nonzero, sub_mul, clear_den, div_mul_cancel₀ _ nonzero]
    push_cast
    rfl
  unfold OMA.S_oeis_a326691.sequence
  rw [fraction, Rat.den_mkRat, if_neg hn.ne', Nat.div_div_self (Nat.gcd_dvd_left _ _) hn.ne']

/-- A squared prime factor divides every cofactor of n, even its own. -/
private lemma repeated_dvd_cofactor {n p q : ℕ} (hp : p.Prime) (hpow : p^2 ∣ n)
    (hq : q ∈ n.primeFactors) : p ∣ n / q := by
  have qdvd := Nat.dvd_of_mem_primeFactors hq
  by_cases h : p = q
  · subst q
    exact (Nat.dvd_div_iff_mul_dvd qdvd).mpr (by simpa [pow_two] using hpow)
  have pdvd : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hpow
  have no : ¬ p ∣ q := fun hdiv => h ((Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hdiv)
  exact (hp.dvd_mul.mp (show p ∣ (n / q) * q by rwa [Nat.div_mul_cancel qdvd])).resolve_right no

private lemma repeated_sums {n p : ℕ} (hp : p.Prime) (hpow : p^2 ∣ n) :
    p ∣ cofactorSum n ∧ p ∣ arithmeticDerivative n :=
  ⟨Finset.dvd_sum fun _ hq => repeated_dvd_cofactor hp hpow hq,
    Finset.dvd_sum fun _ hq => dvd_mul_of_dvd_right (repeated_dvd_cofactor hp hpow hq) _⟩

/-- Modulo a divisor of n that avoids all repeated primes, the weights are immaterial. -/
private lemma sums_congruent {n d : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (avoids : ∀ p : ℕ, p.Prime → p^2 ∣ n → ¬ p ∣ d) :
    (cofactorSum n : ZMod d) = (arithmeticDerivative n : ZMod d) := by
  simp only [cofactorSum, arithmeticDerivative, Nat.cast_sum, Nat.cast_mul]
  refine sum_congr rfl fun p hmem => ?_
  have hp := Nat.prime_of_mem_primeFactors hmem
  have pn := Nat.dvd_of_mem_primeFactors hmem
  by_cases once : n.factorization p = 1
  · simp [once]
  have pos := hp.factorization_pos_of_dvd hn.ne' pn
  have squared := (hp.pow_dvd_iff_le_factorization hn.ne').mpr (show 2 ≤ n.factorization p by omega)
  have cop := (hp.coprime_iff_not_dvd.mpr (avoids p hp squared)).symm
  have dz := cop.dvd_of_dvd_mul_right (show d ∣ (n / p)*p by rwa [Nat.div_mul_cancel pn])
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr dz, mul_zero]

private lemma avoids_repeated {n d b : ℕ} (hd : d ∣ 1 + (n-1)*b)
    (hb : ∀ p : ℕ, p.Prime → p^2 ∣ n → p ∣ b) :
    ∀ p : ℕ, p.Prime → p^2 ∣ n → ¬ p ∣ d := by
  intro p hp hpow pd
  have one := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right (hb p hp hpow) (n-1))).mpr (pd.trans hd)
  exact hp.not_dvd_one one

private lemma gcd_transform {n s : ℕ} (hn : 0 < n) :
    n.gcd ((s : ℤ)-1).natAbs = n.gcd (1 + (n-1)*s) := by
  have equivalent (d : ℕ) (hd : d ∣ n) :
      d ∣ ((s : ℤ) - 1).natAbs ↔ d ∣ 1+(n-1)*s := by
    have hcast : (n : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
    rw [hcast]
    constructor <;> intro h <;> linear_combination -h
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((equivalent _ (Nat.gcd_dvd_left _ _)).mp (Nat.gcd_dvd_right _ _))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((equivalent _ (Nat.gcd_dvd_left _ _)).mpr (Nat.gcd_dvd_right _ _))

private lemma transfer {n d a b : ℕ} (cong : (a : ZMod d) = (b : ZMod d))
    (ha : d ∣ 1 + (n-1)*a) : d ∣ 1 + (n-1)*b := by
  rw [← ZMod.natCast_eq_zero_iff] at ha ⊢
  push_cast at ha ⊢
  rwa [← cong]

end ReciprocalDerivativeProof

open ReciprocalDerivativeProof OMA.S_oeis_a326691 in
theorem OMA.solution : type_of% @OMA.S_oeis_a326691.main := by
  intro n hn
  rw [denominator_formula hn, gcd_transform hn]
  apply Nat.dvd_antisymm
  · have hd := Nat.gcd_dvd_right n (1 + (n-1)*cofactorSum n)
    have avoids := avoids_repeated hd (fun p hp hpow => (repeated_sums hp hpow).1)
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (transfer (sums_congruent hn (Nat.gcd_dvd_left _ _) avoids) hd)
  · have hd := Nat.gcd_dvd_right n (1 + (n-1)*arithmeticDerivative n)
    have avoids := avoids_repeated hd (fun p hp hpow => (repeated_sums hp hpow).2)
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (transfer (sums_congruent hn (Nat.gcd_dvd_left _ _) avoids).symm hd)
