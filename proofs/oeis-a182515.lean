import OMAStatements.S_oeis_a182515
import Mathlib

namespace OMA.A182515Proof

open ArithmeticFunction

theorem carm_dvd (C : ℕ) (h : OMA.S_oeis_a182515.IsCarmichael C) : carmichael C ∣ C - 1 := by
  obtain ⟨h1, -, hb⟩ := h
  have : NeZero C := ⟨by omega⟩
  rw [carmichael_eq_exponent']
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro v
  have hc := ZMod.val_coe_unit_coprime v
  have hm := hb _ hc
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  ext
  push_cast
  exact hz

theorem prime_sub_dvd (C p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpC : p ∣ C)
    (h : OMA.S_oeis_a182515.IsCarmichael C) : p - 1 ∣ C - 1 := by
  have h1 := carm_dvd C h
  have h2 := carmichael_dvd hpC
  have h3 := carmichael_pow_of_prime_ne_two 1 hp hp2
  rw [pow_one, Nat.totient_prime hp] at h3
  rw [← h3]
  exact h2.trans h1

end OMA.A182515Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182515.main := by
  intro C hC h23 h67
  have b := OMA.A182515Proof.prime_sub_dvd C 67 (by norm_num) (by norm_num) h67 hC
  have c := hC.1
  have hd : 23 * 67 ∣ C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h23 h67
  obtain ⟨k, rfl⟩ := hd
  have b' : 66 ∣ 23 * 67 * k - 1 := b
  refine ⟨k / 66, ?_⟩
  omega
