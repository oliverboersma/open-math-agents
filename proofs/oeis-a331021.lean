import OMAStatements.S_oeis_a331021
import Mathlib

namespace LargeGcdWieferich

private theorem extract (k a : ℕ) (hk : 0 < k) (hg : k < Nat.gcd (k^2) a) :
    ∃ p : ℕ, p.Prime ∧ p ∣ k ∧ p^2 ∣ a := by
  let d := Nat.gcd (k^2) a
  have hd : 0 < d := hk.trans hg
  have hex : ∃ p, k.factorization p < d.factorization p := by
    by_contra! hh
    have hle : d.factorization ≤ k.factorization := fun p => hh p
    have hdiv := (Nat.factorization_le_iff_dvd hd.ne' hk.ne').mp hle
    exact (not_le_of_gt hg) (Nat.le_of_dvd hk hdiv)
  obtain ⟨p, hp⟩ := hex
  have hp0 : 0 < d.factorization p := by omega
  have hs : p ∈ d.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hp0.ne'
  have hpP := Nat.prime_of_mem_primeFactors hs
  have hdk : d ∣ k^2 := Nat.gcd_dvd_left _ _
  have hpk : p ∣ k := hpP.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hs).trans hdk)
  have hkP := hpP.factorization_pos_of_dvd hk.ne' hpk
  have hp2 : 2 ≤ d.factorization p := by omega
  exact ⟨p, hpP, hpk,
    ((hpP.pow_dvd_iff_le_factorization hd.ne').mpr hp2).trans (Nat.gcd_dvd_right _ _)⟩

private theorem descend {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : p.Coprime m)
    (hd : p^2 ∣ 2^m-1) : p^2 ∣ 2^(p-1)-1 := by
  have hb : (2:ℕ).Coprime (p^2) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hcast : (2 : ZMod (p^2))^m = 1 := by
    have hpos : 1 ≤ (2:ℕ)^m := Nat.succ_le_of_lt (by positivity)
    have hmod : 1 ≡ 2^m [MOD p^2] := (Nat.modEq_iff_dvd' hpos).mpr hd
    have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod.symm
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hz
  have heuler : (2 : ZMod (p^2))^(p*(p-1)) = 1 := by
    have h : (2:ℕ)^((p^2).totient) ≡ 1 [MOD p^2] := Nat.ModEq.pow_totient hb
    rw [show (p^2).totient = p*(p-1) by simpa using Nat.totient_prime_pow_succ hp 1] at h
    have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hh
  let r := orderOf (2 : ZMod (p^2))
  have hrm : r ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hcast
  have hrp : r ∣ p*(p-1) := orderOf_dvd_iff_pow_eq_one.mpr heuler
  have hrc : r.Coprime p := hc.symm.of_dvd_left hrm
  have hr : r ∣ p-1 := hrc.dvd_of_dvd_mul_left hrp
  have hfin : (2 : ZMod (p^2))^(p-1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hr
  have hpos : 1 ≤ (2:ℕ)^(p-1) := Nat.succ_le_of_lt (by positivity)
  apply (Nat.modEq_iff_dvd' hpos).mp
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hfin.symm

theorem main : ∀ k : ℕ, 0 < k → k < Nat.gcd (k^2) (2^(k-1)-1) →
    ∃ p : ℕ, p.Prime ∧ p ∣ k ∧ p^2 ∣ 2^(p-1)-1 := by
  intro k hk hg
  obtain ⟨p,hp,hpk,hd⟩ := extract k (2^(k-1)-1) hk hg
  have hkn : 1 < k := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hk hpk)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h0 : 2 ∣ (2:ℕ)^(k-1) := dvd_pow_self _ (by omega)
    have h1 : 2 ∣ (2:ℕ)^(k-1)-1 := (dvd_pow_self 2 (by decide : (2:ℕ) ≠ 0)).trans hd
    have h := Nat.dvd_sub h0 h1
    have hpos : 1 ≤ (2:ℕ)^(k-1) := Nat.succ_le_of_lt (by positivity)
    have he : (2:ℕ)^(k-1) - (2^(k-1)-1) = 1 := by omega
    rw [he] at h
    norm_num at h
  have hc : p.Coprime (k-1) := hp.coprime_iff_not_dvd.mpr (by
    intro h
    have h' := Nat.dvd_sub hpk h
    rw [show k-(k-1)=1 by omega] at h'
    exact hp.ne_one (Nat.dvd_one.mp h'))
  exact ⟨p,hp,hpk,descend hp hp2 hc hd⟩

end LargeGcdWieferich

theorem OMA.solution : type_of% @OMA.S_oeis_a331021.main := LargeGcdWieferich.main