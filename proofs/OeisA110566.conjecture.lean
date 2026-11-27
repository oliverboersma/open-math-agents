import FormalConjectures.OEIS.«110566»
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Data.Nat.Factorization.Basic

-- Credit: @marcusbuffett
/-!
The odd number 81 never occurs. Grouping denominators divisible by 3 gives
H(n) = H(n/3)/3 + a 3-integral remainder, as in Peter Shiu, The denominators
of harmonic numbers, arXiv:1607.02863. For 27 ≤ n < 81 the valuation of
H(n) is at most zero. From that point on appending a base-three digit lowers
it by exactly one, while the exponent of 3 in the lcm increases by one.
-/

namespace HarmonicThree
open Finset

private lemma integral_remainder (n : ℕ) :
    0 ≤ padicValRat 3 (harmonic n - harmonic (n/3)/3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hd : 3 ∣ n+1
    · have h : (n+1)/3 = n/3+1 := by omega
      have hn : (n+1:ℚ) = 3*((n/3:ℕ)+1:ℚ) := by
        exact_mod_cast (show n+1=3*(n/3+1) by omega)
      rw [h,harmonic_succ n,harmonic_succ (n/3)]
      convert ih using 1
      congr 1
      push_cast
      rw [hn, mul_inv_rev]
      ring
    · have h : (n+1)/3 = n/3 := by omega
      rw [h,harmonic_succ]
      have hv : padicValRat 3 (((n+1:ℕ):ℚ)⁻¹)=0 := by
        rw [padicValRat.inv,padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hd]
        simp
      rw [show harmonic n + (((n+1:ℕ):ℚ)⁻¹) - harmonic (n/3)/3 =
        (harmonic n-harmonic (n/3)/3) + (((n+1:ℕ):ℚ)⁻¹) by ring]
      by_cases hz : (harmonic n-harmonic (n/3)/3) + (((n+1:ℕ):ℚ)⁻¹)=0
      · rw [hz]; simp
      · exact le_trans (le_min ih hv.ge) (padicValRat.min_le_padicValRat_add hz)

private lemma bound (n : ℕ) (hn : 27 ≤ n) :
    padicValRat 3 (harmonic n) + (Nat.log 3 n : ℤ) ≤ 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 81
    · interval_cases n <;> decide +kernel
    have hq : 27 ≤ n/3 := by omega
    have prev := ih (n/3) (by omega) hq
    have lg : 3 ≤ Nat.log 3 (n/3) := Nat.le_log_of_pow_le (by decide) (by simpa using hq)
    have hval : padicValRat 3 (harmonic (n/3)) ≤ 0 := by omega
    have qpos := (harmonic_pos (show n/3 ≠ 0 by omega)).ne'
    have hv : padicValRat 3 (harmonic (n/3)/3) = padicValRat 3 (harmonic (n/3))-1 := by
      rw [padicValRat.div qpos (by norm_num)]
      rw [show padicValRat 3 3 = 1 by decide +kernel]
    let R := harmonic n - harmonic (n/3)/3
    have he : harmonic n = harmonic (n/3)/3 + R := by dsimp [R]; ring
    have vr : 0 ≤ padicValRat 3 R := integral_remainder n
    have step : padicValRat 3 (harmonic n) = padicValRat 3 (harmonic (n/3))-1 := by
      rw [he]
      by_cases zero : R=0
      · simpa [zero] using hv
      rw [padicValRat.add_eq_of_lt (he ▸ (harmonic_pos (by omega : n ≠ 0)).ne')
        (div_ne_zero qpos (by norm_num)) zero (by omega),hv]
    have hlog := Nat.log_div_base 3 n
    omega

private lemma lcm_data (n : ℕ) :
    let L := (Icc 1 n).lcm id
    (harmonic n).den ∣ L ∧ L ≠ 0 ∧ padicValNat 3 L = Nat.log 3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨hd,hz,hv⟩
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (show 1 ≤ n+1 by omega), Finset.lcm_insert]
    change (harmonic (n+1)).den ∣ (n+1).lcm ((Icc 1 n).lcm id) ∧ _
    refine ⟨?_, Nat.lcm_ne_zero (Nat.succ_ne_zero n) hz, ?_⟩
    · rw [harmonic_succ]
      apply (Rat.add_den_dvd_lcm _ _).trans
      apply Nat.lcm_dvd
      · exact hd.trans (Nat.dvd_lcm_right _ _)
      · rw [Rat.den_inv_of_ne_zero (show ((n+1:ℕ):ℚ) ≠ 0 by positivity)]
        exact
          (Nat.dvd_lcm_left (n+1) ((Icc 1 n).lcm id))
    · let L := (Icc 1 n).lcm id
      change padicValNat 3 (Nat.lcm (n+1) L)=_
      have hp : Nat.Prime 3 := by decide
      rw [← Nat.factorization_def _ hp, Nat.factorization_lcm (by omega) hz,
        Finsupp.sup_apply, Nat.factorization_def _ hp,Nat.factorization_def _ hp]
      change max (padicValNat 3 (n+1)) (padicValNat 3 L) = _
      rw [show padicValNat 3 L = Nat.log 3 n from hv, max_comm]
      exact Nat.max_log_padicValNat_succ_eq_log_succ n

theorem missing (n : ℕ) : OeisA110566.a n ≠ 81 := by
  intro eq
  obtain ⟨dvd,_,vL⟩ := lcm_data n
  have val := congrArg (padicValNat 3) eq
  rw [OeisA110566.a,padicValNat.div_of_dvd dvd,vL] at val
  have four : padicValNat 3 81 = 4 := by decide +kernel
  rw [four] at val
  by_cases sm : n < 27
  · have h := Nat.log_mono_right (b:=3) (show n ≤ 26 by omega)
    have three : Nat.log 3 26 = 2 := by decide
    omega
  · have h := bound n (by omega)
    rw [padicValRat_def] at h
    omega

end HarmonicThree

theorem OMA.disproof : ¬ (type_of% @OeisA110566.conjecture) := by
  intro all
  obtain ⟨n, _, h⟩ := all 81 (by decide)
  exact HarmonicThree.missing n h

