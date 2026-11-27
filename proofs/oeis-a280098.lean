import OMAStatements.S_oeis_a280098
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-!
# Classification of the moduli in A280098

Necessity follows by applying the conjectured divisibility to the product
of two distinct primes in the classes u and -u⁻¹. It forces every unit
modulo k to have square one. Passing to prime-power divisors then forces
k to divide 24. For sufficiency, pair each divisor with its complementary
divisor. The small residue rings determine the sum of each pair.
-/

namespace DivisorSumModuli

open ArithmeticFunction

private theorem prime_sigma {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors]
  simp [hp.ne_one.symm, add_comm]

private theorem all_units_square {k : ℕ} [NeZero k]
    (h : ∀ n : ℕ, 0 < n → k ∣ sigma 1 (k * n - 1)) (u : (ZMod k)ˣ) :
    u ^ 2 = 1 := by
  obtain ⟨p, _, hp, hpclass⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
  obtain ⟨q, hpq, hq, hqclass⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (u⁻¹.isUnit.neg) p
  have huv : (u : ZMod k) * (↑(u⁻¹) : ZMod k) = 1 := u.val_inv
  have hd : k ∣ p * q + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [hpclass, hqclass, mul_neg, huv]
    ring
  obtain ⟨n, hn⟩ := hd
  have hpos : 0 < n := by
    by_contra! hz
    obtain rfl : n = 0 := by omega
    simp at hn
  have hsig := h n hpos
  rw [← hn, Nat.add_sub_cancel, isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_primes hp hq).mpr hpq.ne), prime_sigma hp, prime_sigma hq] at hsig
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hsig
  push_cast at hz
  rw [hpclass, hqclass] at hz
  have hu : (u : ZMod k) = (↑(u⁻¹) : ZMod k) := by linear_combination hz + huv
  apply Units.ext
  change (u : ZMod k) ^ 2 = 1
  rw [pow_two]
  simpa only [← hu] using huv

private theorem divides_twenty_four {k : ℕ} [NeZero k]
    (hsq : ∀ u : (ZMod k)ˣ, u ^ 2 = 1) : k ∣ 24 := by
  have descend {d : ℕ} (hd : d ∣ k) (u : (ZMod d)ˣ) : u ^ 2 = 1 := by
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hd u
    rw [← map_pow, hsq, map_one]
  have square {d a : ℕ} (hd : d ∣ k) (ha : Nat.Coprime a d) :
      (a : ZMod d) ^ 2 = 1 := by
    have hu := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d))
      (descend hd (ZMod.unitOfCoprime a ha))
    simpa using hu
  have h16 : ¬16 ∣ k := by
    intro hd
    exact (by decide : (3 : ZMod 16) ^ 2 ≠ 1) (square hd (by decide : Nat.Coprime 3 16))
  have h9 : ¬9 ∣ k := by
    intro hd
    exact (by decide : (2 : ZMod 9) ^ 2 ≠ 1) (square hd (by decide : Nat.Coprime 2 9))
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 24 k).mpr
  intro p e hp he
  cases e with
  | zero => simp
  | succ e =>
    have hpk : p ∣ k := (dvd_pow_self p (Nat.succ_ne_zero e)).trans he
    by_cases hp2 : p = 2
    · subst p
      have hbound : e + 1 ≤ 3 := by
        by_contra! hg
        exact h16 ((pow_dvd_pow 2 (by omega : 4 ≤ e + 1)).trans he)
      exact (pow_dvd_pow 2 hbound).trans (by decide : 2 ^ 3 ∣ 24)
    · have hsq2 := square hpk ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      have hz : (3 : ZMod p) = 0 := by linear_combination hsq2
      have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
      have hbound : e + 1 ≤ 1 := by
        by_contra! hg
        exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ e + 1)).trans he)
      exact (pow_dvd_pow 3 hbound).trans (by decide : 3 ^ 1 ∣ 24)

private theorem paired_divisors {k m : ℕ} (hm : (m : ZMod k) = -1)
    (hpairs : ∀ u v : ZMod k, u * v = -1 → u + v = 0 ∧ v ≠ u) :
    k ∣ sigma 1 m := by
  have hpair (d : ℕ) (hd : d ∈ m.divisors) :
      (d : ZMod k) + ((m / d : ℕ) : ZMod k) = 0 ∧ m / d ≠ d := by
    have hprod : (d : ZMod k) * ((m / d : ℕ) : ZMod k) = -1 := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), hm]
    obtain ⟨hadd, hne⟩ := hpairs _ _ hprod
    exact ⟨hadd, fun he => hne (congrArg (fun x : ℕ => (x : ZMod k)) he)⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [sigma_one_apply, Nat.cast_sum]
  apply Finset.sum_involution (fun d _ => m / d)
  · exact fun d hd => (hpair d hd).1
  · exact fun d hd _ => (hpair d hd).2
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd),
      Nat.ne_zero_of_mem_divisors hd⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (Nat.ne_zero_of_mem_divisors hd)

theorem classify (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 0 < n → k ∣ sigma 1 (k * n - 1)) ↔
    k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 12 ∨ k = 24 := by
  constructor
  · intro h
    have : NeZero k := ⟨hk.ne'⟩
    have hd := divides_twenty_four (all_units_square h)
    have hne : k ≠ 2 := by
      rintro rfl
      have ht := h 1 (by decide)
      norm_num at ht
    have hle := Nat.le_of_dvd (by decide : 0 < 24) hd
    have list_check : ∀ t : Fin 25, t.val ∣ 24 → t.val ≠ 2 →
        t.val = 1 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 6 ∨ t.val = 8 ∨ t.val = 12 ∨ t.val = 24 := by
      decide
    exact list_check ⟨k, by omega⟩ hd hne
  · intro hs n hn
    rcases hs with rfl | hs
    · exact one_dvd _
    have hpairs : ∀ u v : ZMod k, u * v = -1 → u + v = 0 ∧ v ≠ u := by
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    apply paired_divisors _ hpairs
    rw [Nat.cast_sub (show 1 ≤ k * n from Nat.mul_pos hk hn),
      Nat.cast_one, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_sub]

end DivisorSumModuli

theorem OMA.solution : type_of% @OMA.S_oeis_a280098.main := DivisorSumModuli.classify
