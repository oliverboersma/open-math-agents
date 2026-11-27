import FormalConjectures.ErdosProblems.«820»
import Mathlib.FieldTheory.Finite.Basic

/-! Reduction by @Burntgogi. The lower input follows from Fan--Pollack,
"Extremal behavior of the shifted prime divisor function", Theorem 1.1.
The forced-prime argument is due to Erdos and was applied here by van Doorn.
The upper input follows from Liam Price's bound for K (Erdos Problem 820,
July 2026). The supremum argument reconciles the two exponents. -/

open Filter

namespace OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1

theorem eventually_strictMono : ∀ᶠ n : ℕ in atTop, StrictMono (fun a => (Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ)))))) := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log (n : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ) < n)).mpr
    linarith [Real.exp_one_lt_three]
  intro a b hab
  exact Real.exp_lt_exp.mpr (Real.rpow_lt_rpow_of_exponent_lt (by linarith)
    (div_lt_div_of_pos_right hab (Real.log_pos hlog)))

/-- The separating exponent need not coincide with either known endpoint. -/
theorem critical_of_separate_bounds (v : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
    (hlower : ∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ))))) < v n)
    (hupper : ∀ᶠ n : ℕ in atTop, v n < (Real.exp ((n : ℝ) ^ (b / Real.log (Real.log (n : ℝ)))))) :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ),
      (∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ ((c-ε) / Real.log (Real.log (n : ℝ))))) < v n) ∧
      ∀ᶠ n : ℕ in atTop, v n < (Real.exp ((n : ℝ) ^ ((c+ε) / Real.log (Real.log (n : ℝ))))) := by
  let S : Set ℝ := {s | ∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ (s / Real.log (Real.log (n : ℝ))))) < v n}
  have has : a ∈ S := hlower
  have hne : S.Nonempty := ⟨a, has⟩
  have hbounded : BddAbove S := by
    refine ⟨b, fun s hs => ?_⟩
    by_contra! h
    have hcut : ∀ᶠ n : ℕ in atTop, ¬(Real.exp ((n : ℝ) ^ (s / Real.log (Real.log (n : ℝ))))) < v n := by
      filter_upwards [hupper, eventually_strictMono] with n hupper hmono
      exact not_lt.mpr (hupper.trans (hmono h)).le
    exact hs hcut
  refine ⟨sSup S, ha.trans_le (le_csSup hbounded has), fun ε hε => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hcs⟩ := exists_lt_of_lt_csSup hne (show sSup S - ε < sSup S by linarith)
    exact (show ∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ (s / Real.log (Real.log (n : ℝ))))) < v n from hs).and_eventually
      eventually_strictMono |>.mono fun _ h => (h.2 hcs).trans h.1
  · have hs : sSup S + ε/2 ∉ S := fun h => (not_lt.mpr (le_csSup hbounded h)) (by linarith)
    have he : ∀ᶠ n : ℕ in atTop, ¬(Real.exp ((n : ℝ) ^ ((sSup S + ε/2) / Real.log (Real.log (n : ℝ))))) < v n := by
      change ¬(∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ ((sSup S + ε/2) / Real.log (Real.log (n : ℝ))))) < v n) at hs
      simpa only [not_frequently] using hs
    filter_upwards [he, eventually_strictMono] with n hn hm
    exact (le_of_not_gt hn).trans_lt (hm (show sSup S + ε/2 < sSup S + ε by linarith))

theorem H_le_K {n : ℕ} (hn : 2 ≤ n) : Erdos820.H n ≤ Erdos820.K n := by
  have hsize : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) hn
  let l := 2^n - 1
  have hl : 2 < l := by dsimp [l]; omega
  have hne : {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) l}.Nonempty := by
    refine ⟨l, hl.le, ?_⟩
    have h1 : 1 ≤ l^n := Nat.one_le_pow _ _ (by omega)
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega : n ≠ 0))
      (((Nat.coprime_self_sub_right h1).2 (Nat.coprime_one_right _)).symm)
  have hk := Nat.sInf_mem hne
  change 2 ≤ Erdos820.K n ∧ Nat.Coprime ((Erdos820.K n)^n-1) l at hk
  have h2 : 2 < Erdos820.K n := by
    by_contra! hh
    have he := Nat.le_antisymm hh hk.1
    have h := hk.2
    rw [he] at h
    change Nat.Coprime l l at h
    have hone : l = 1 := by simpa using h
    omega
  exact Nat.sInf_le ⟨2, by decide, h2, hk.2.symm⟩

theorem official_of_lower_and_upper {a b : ℝ} (ha : 0 < a)
    (hl : ∃ᶠ n : ℕ in atTop, (Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ))))) < Erdos820.H n)
    (hu : ∀ᶠ n : ℕ in atTop, (Erdos820.K n : ℝ) < (Real.exp ((n : ℝ) ^ (b / Real.log (Real.log (n : ℝ)))))) :
    type_of% @Erdos820.erdos_820.variants.log_log_exponent := by
  apply critical_of_separate_bounds _ ha hl
  filter_upwards [hu, eventually_ge_atTop 2] with n hk hn
  exact (show (Erdos820.H n : ℝ) ≤ Erdos820.K n by exact_mod_cast H_le_K hn).trans_lt hk


private theorem forced_prime {p m n : ℕ} (hp : p.Prime) (hd : p-1 ∣ n)
    (hm : 1 ≤ m) (h : ¬p ∣ m) : p ∣ m^n-1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun he => h ((ZMod.natCast_eq_zero_iff _ _).mp he)
  obtain ⟨j,hj⟩ := hd
  have hpow : (m : ZMod p)^n = 1 := by
    rw [hj, pow_mul, ZMod.pow_card_sub_one_eq_one hm0, one_pow]
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hm), Nat.cast_pow, Nat.cast_one, hpow, sub_self]

/-- The forced primes for a minimal coprime pair give the lower bound of van Doorn. -/
theorem shifted_count_le_H_sq {n : ℕ} (hn : 1 ≤ n) :
    2^((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card ≤ Erdos820.H n ^ 2 := by
  obtain ⟨k,hk,hkH,hcop⟩ := Erdos820.H_spec hn
  let l := Erdos820.H n
  have hl : 2 < l := hk.trans_lt hkH
  have hsub : (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n) ⊆ (k*l).primeFactors := by
    intro p hp
    obtain ⟨hpr, hdiv⟩ := (Finset.mem_filter.mp hp).2
    refine Nat.mem_primeFactors.mpr ⟨hpr, ?_, Nat.mul_ne_zero (by omega) (by omega)⟩
    by_contra hf
    have hk' : ¬p ∣ k := fun h => hf (dvd_mul_of_dvd_left h _)
    have hl' : ¬p ∣ l := fun h => hf (dvd_mul_of_dvd_right h _)
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpr,
      forced_prime hpr hdiv (by omega : 1 ≤ k) hk',
      forced_prime hpr hdiv (by omega : 1 ≤ l) hl'⟩) hcop
  calc
    _ ≤ 2^(k*l).primeFactors.card := Nat.pow_le_pow_right (by decide) (Finset.card_le_card hsub)
    _ = ∏ _p ∈ (k*l).primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ (k*l).primeFactors, p := by
      exact Finset.prod_le_prod' (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
    _ ≤ k*l := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.prod_primeFactors_dvd _)
    _ ≤ _ := by change k*l ≤ l^2; rw [pow_two]; exact Nat.mul_le_mul_right _ hkH.le

theorem official_of_shifted_primes {a b : ℝ} (ha : 0 < a)
    (hl : ∃ᶠ n : ℕ in atTop, 4 * ((n : ℝ) ^ (a / Real.log (Real.log n))) <
      ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card)
    (hu : ∀ᶠ n : ℕ in atTop, (Erdos820.K n : ℝ) < (Real.exp ((n : ℝ) ^ (b / Real.log (Real.log (n : ℝ)))))) :
    type_of% @Erdos820.erdos_820.variants.log_log_exponent := by
  apply official_of_lower_and_upper ha _ hu
  apply (hl.and_eventually (eventually_ge_atTop 2)).mono
  rintro n ⟨hcount, hn⟩
  have hpow : (2 : ℝ) ^ ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card ≤ (Erdos820.H n : ℝ)^2 := by
    exact_mod_cast shifted_count_le_H_sq (by omega : 1 ≤ n)
  have hlog : (1/2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hpos : 0 < (n:ℝ) ^ (a / Real.log (Real.log n)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlt : ((Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ))))))^2 < (2:ℝ)^((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card := by
    rw [ ← Real.exp_nat_mul, ← Real.exp_log (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    push_cast
    nlinarith [mul_pos (sub_pos.mpr hlog)
      (show 0 < (((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card : ℝ) by linarith)]
  have hsq := hlt.trans_le hpow
  have hv : (0:ℝ) ≤ Erdos820.H n := Nat.cast_nonneg _
  have hw : 0 < (Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ))))) := Real.exp_pos _
  nlinarith


/-- A positive maximal-order exponent for the shifted prime divisor count. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ᶠ n : ℕ in atTop,
    4 * (n : ℝ) ^ (a / Real.log (Real.log n)) <
      (((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card : ℝ)

/-- An eventual finite upper exponent for the fixed-base function K. -/
def H2 : Prop :=
  ∃ b : ℝ, ∀ᶠ n : ℕ in atTop,
    (Erdos820.K n : ℝ) < Real.exp ((n : ℝ) ^ (b / Real.log (Real.log n)))

theorem main : H1 → H2 → type_of% @Erdos820.erdos_820.variants.log_log_exponent := by
  rintro ⟨a, ha, hl⟩ ⟨b, hu⟩
  exact official_of_shifted_primes ha hl hu

end OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1
