import OMAReductions.R_Green46_green_46_variants_upper_R1
import Mathlib

/-! Chinese remaindering over the primes p <= x: choose A with A = 1 - a_p (mod p) for each
of them. If i + 1 = a_p (mod p) for a covering prime p, then p divides A + i and the
primorial, so A + i is not coprime to the primorial. -/

open Green46 Filter Finset Real Asymptotics

namespace OMA.P2bG46

theorem sol : OMA.R_Green46_green_46_variants_upper_R1.H2 := by
  unfold OMA.R_Green46_green_46_variants_upper_R1.H2
  intro x y ⟨a, ha⟩
  classical
  let t := (Finset.range (x + 1)).filter Nat.Prime
  have hs : ∀ p ∈ t, (id p : ℕ) ≠ 0 := fun p hp => (Finset.mem_filter.1 hp).2.ne_zero
  have pp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2).2 hpq
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset (fun p => p + 1 - a p % p) id t hs pp
  refine ⟨(A : ℤ), fun i hi => ?_⟩
  obtain ⟨p, hpx, hp, hmod⟩ := ha (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hpt : p ∈ t := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩
  have hAp : A ≡ p + 1 - a p % p [MOD p] := hA p hpt
  have hsum := hAp.add hmod
  have hq := Nat.div_add_mod (a p) p
  have hr := Nat.mod_lt (a p) hp.pos
  have heq : p + 1 - a p % p + a p = 1 + p * (1 + a p / p) := by
    rw [mul_add, mul_one]; omega
  rw [heq] at hsum
  have h1 : 1 + p * (1 + a p / p) ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [Nat.add_mul_mod_self_left]
  have h2 : A + (i + 1) ≡ 1 [MOD p] := hsum.trans h1
  have h3 : A + i ≡ 0 [MOD p] := by
    have : A + i + 1 ≡ 0 + 1 [MOD p] := by rw [add_assoc, zero_add]; exact h2
    exact Nat.ModEq.add_right_cancel' 1 this
  have hdvd : p ∣ A + i := (Nat.modEq_zero_iff_dvd).1 h3
  have habs : ((A : ℤ) + (i : ℤ)).natAbs = A + i := by
    rw [show (A : ℤ) + (i : ℤ) = ((A + i : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  rw [habs]
  intro hcop
  have hpp : p ∣ primorial x := (Nat.Prime.dvd_primorial_iff hp).2 hpx
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hpp
  exact hp.one_lt.ne' this

end OMA.P2bG46

theorem OMA.solution : OMA.R_Green46_green_46_variants_upper_R1.H2 := OMA.P2bG46.sol
