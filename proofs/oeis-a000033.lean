import OMAStatements.S_oeis_a000033
import Mathlib

/-!
# Van Hoeij's prime congruence for the ménage hit coefficients

The conjecture is in the OEIS entry A000033, dated June 10, 2019.
The factorial cuts off the rook-coefficient sum at the prime. Below that
cutoff the Frobenius identity makes the second p-step difference of each
binomial coefficient zero. The case of the prime two uses Pascal's identity.
-/

namespace RookBinom

open Polynomial

/-- Shifting the top index by p has zero second difference below degree 2p. -/
theorem choose_second_difference {p : ℕ} (hp : p.Prime) (m r : ℕ) (hr : r < p) :
    ((m + 2 * p).choose (2 * r) : ZMod p) + (m.choose (2 * r) : ZMod p) =
      2 * ((m + p).choose (2 * r) : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let Q : (ZMod p)[X] := 1 + X
  have hF : Q ^ p = 1 + X ^ p := by
    simp only [Q, add_pow_char, one_pow]
  have hpoly : Q ^ (m + 2 * p) + Q ^ m - (Q ^ (m+p) + Q ^ (m+p)) =
      Q ^ m * X ^ (2 * p) := by
    rw [pow_add, pow_add _ m p, Nat.mul_comm 2 p, pow_mul, pow_mul, hF]
    ring
  have hk : ¬ 2 * p ≤ 2 * r := by omega
  have heq := congrArg (fun f : (ZMod p)[X] => f.coeff (2*r)) hpoly
  simp only [Q, coeff_sub, coeff_add, coeff_one_add_X_pow, coeff_mul_X_pow', if_neg hk] at heq
  simpa only [two_mul (((m + p).choose (2 * r) : ℕ) : ZMod p)] using sub_eq_zero.mp heq

end RookBinom

namespace RookOdd
open Finset OMA.S_oeis_a000033

private lemma choose_two_cast {p : ℕ} (k : ℕ) :
    2 * (k.choose 2 : ZMod p) = (k : ZMod p) * ((k : ZMod p) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

private def factor (p n r : ℕ) : ZMod p :=
  (-1)^r * r.factorial * ((n : ZMod p) - r) * ((n : ZMod p) - r - 1)

private lemma doubled (p n r : ℕ) :
    2 * (signedTerm n r : ZMod p) = factor p n r * (rookCount n r : ZMod p) := by
  by_cases hr : r ≤ n
  · have h := choose_two_cast (p := p) (n-r)
    rw [Nat.cast_sub hr] at h
    simp only [signedTerm, factor, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    linear_combination (-1 : ZMod p)^r * r.factorial * (rookCount n r : ZMod p) * h
  · have h : rookCount n r = 0 := by
      simp [rookCount, Nat.choose_eq_zero_of_lt (show n+r < 2*r by omega),
        Nat.choose_eq_zero_of_lt (show n+r-1 < 2*r by omega)]
    simp [h, signedTerm]

private lemma rook_step {p : ℕ} (hp : p.Prime) (n r : ℕ) (hn : 0<n) (hr : r<p) :
    (rookCount (n+2*p) r : ZMod p) + (rookCount n r : ZMod p) =
      2 * (rookCount (n+p) r : ZMod p) := by
  have h := RookBinom.choose_second_difference hp (n+r) r hr
  have j := RookBinom.choose_second_difference hp (n+r-1) r hr
  simp only [rookCount, Nat.cast_add]
  rw [show n+2*p+r=n+r+2*p by omega, show n+p+r=n+r+p by omega,
    show n+r+2*p-1=n+r-1+2*p by omega, show n+r+p-1=n+r-1+p by omega]
  linear_combination h+j

private lemma term_step {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (n r : ℕ) (hn : 0<n) :
    (signedTerm (n+2*p) r : ZMod p) + (signedTerm n r : ZMod p) =
      2 * (signedTerm (n+p) r : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hr : r < p
  · have h2 : (2 : ZMod p) ≠ 0 := by
      have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
      change ((2 : ℕ) : ZMod p) ≠ 0
      exact fun hz => (Nat.not_dvd_of_pos_of_lt (by decide) hlt) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    apply mul_left_cancel₀ h2
    rw [mul_add, doubled, doubled, mul_left_comm, doubled]
    have hf : factor p (n+2*p) r = factor p n r := by simp [factor]
    have hf' : factor p (n+p) r = factor p n r := by simp [factor]
    rw [hf,hf']
    linear_combination factor p n r * rook_step hp n r hn hr
  · have hfact : (r.factorial : ZMod p) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos (by omega))
    simp [signedTerm, hfact]

private lemma extend_sum (p n M : ℕ) (h : n ≤ M) :
    (signedValue n : ZMod p) = ∑ r ∈ range (M+1), (signedTerm n r : ZMod p) := by
  simp only [signedValue, Int.cast_sum]
  apply sum_subset (range_mono (by omega : n+1 ≤ M+1))
  intro r _ hr
  have hnr : n < r := by simpa [Nat.lt_succ_iff] using hr
  simp [signedTerm, Nat.sub_eq_zero_of_le hnr.le]

theorem odd_congruence (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hodd : p ≠ 2) :
    (p : ℤ) ∣ a n + 2 * a (n+p) + a (n+2*p) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have he : (signedValue (n+2*p) : ZMod p) + (signedValue n : ZMod p) =
      2 * (signedValue (n+p) : ZMod p) := by
    rw [extend_sum p (n+2*p) (n+2*p) le_rfl, extend_sum p n (n+2*p) (by omega),
      extend_sum p (n+p) (n+2*p) (by omega), ← sum_add_distrib, mul_sum]
    exact sum_congr rfl (fun r _ => term_step hp hodd n r hn)
  have hsign : (-1 : ZMod p)^p = -1 := hp.odd_of_ne_two hodd |>.neg_one_pow
  have hdouble : (-1 : ZMod p)^(2*p) = 1 := by rw [two_mul, pow_add, hsign]; ring
  simp only [a, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_neg,
    Int.cast_one, pow_add, hdouble, hsign]
  linear_combination (-1 : ZMod p)^n * he

end RookOdd

namespace RookParity
open Finset OMA.S_oeis_a000033

private lemma choose_period (n : ℕ) :
    (((n+4).choose 2 : ℕ) : ZMod 2) = (n.choose 2 : ZMod 2) := by
  have step (k : ℕ) : (((k+1).choose 2 : ℕ) : ZMod 2) =
      k + (k.choose 2 : ZMod 2) := by
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.cast_add]
  change (((n+1+1+1+1).choose 2 : ℕ) : ZMod 2) = _
  rw [step, step, step, step]
  push_cast
  ring_nf
  simp [show (6 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide]

private lemma truncated {n : ℕ} (hn : 0 < n) :
    (a n : ZMod 2) = ((n-1).choose 2 : ZMod 2) *
      (((n+1).choose 2 : ZMod 2) + (n.choose 2 : ZMod 2)) := by
  have minus : (-1 : ZMod 2) = 1 := by decide
  have small : ∑ r ∈ range 2, (signedTerm n r : ZMod 2) =
      ∑ r ∈ range (n+1), (signedTerm n r : ZMod 2) := by
    apply sum_subset (range_mono (by omega))
    intro r hr hs
    have hr2 : 2 ≤ r := by simpa only [mem_range, not_lt] using hs
    obtain ⟨b,hb⟩ := Nat.dvd_factorial (by decide : 0 < 2) hr2
    simp [signedTerm, hb, show (2 : ZMod 2) = 0 by decide]
  rw [a, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, minus, one_pow, one_mul,
    signedValue, Int.cast_sum, ← small]
  simp [sum_range_succ, signedTerm, rookCount, minus, show (1+1 : ZMod 2) = 0 by decide]

/-- For the prime two, only r=0,1 survive. The remaining factor is four-periodic
because Pascal's recursion gives C(n+4,2) = C(n,2) modulo two. -/
lemma two (n : ℕ) (hn : 0 < n) : (2 : ℤ) ∣ a n + 2 * a (n+2) + a (n+2*2) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  push_cast
  have h : (2 : ZMod 2) = 0 := by decide
  change (a n : ZMod 2) + 2 * (a (n+2) : ZMod 2) + (a (n+4) : ZMod 2) = 0
  rw [h, zero_mul, add_zero, truncated hn, truncated (show 0 < n+4 by omega),
    show n+4-1 = (n-1)+4 by omega, show n+4+1 = (n+1)+4 by omega,
    choose_period, choose_period, choose_period]
  rw [← two_mul, h, zero_mul]

end RookParity

theorem OMA.solution : type_of% @OMA.S_oeis_a000033.main := by
  intro n p hn hp
  by_cases h : p = 2
  · subst p
    exact RookParity.two n hn
  · exact RookOdd.odd_congruence n p hn hp h
