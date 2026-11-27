import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

namespace OMA.Erdos649

theorem purePower_iff (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : q < p) :
    (∃ e : ℕ, 0 < e ∧ (q ^ e - 1).maxPrimeFac = p) ↔
      (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac = p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hq_ne : (q : ZMod p) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hpq) (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff q p).mp hz))
  let d := orderOf (q : ZMod p)
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h => hq_ne (orderOf_eq_zero_iff_eq_zero.mp h))
  have hqpow (e : ℕ) (he : 0 < e) : 1 < q ^ e :=
    Nat.one_lt_pow he.ne' hq.one_lt
  have hp_dvd_iff (e : ℕ) (he : 0 < e) :
      p ∣ q ^ e - 1 ↔ (q : ZMod p) ^ e = 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (hqpow e he).le,
      Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have hp_dvd_d : p ∣ q ^ d - 1 :=
    (hp_dvd_iff d hd).mpr (pow_orderOf_eq_one (q : ZMod p))
  have hnd : 0 < q ^ d - 1 := by have := hqpow d hd; omega
  constructor
  · rintro ⟨e, he, hpmax⟩
    have hp_dvd_e : p ∣ q ^ e - 1 := hpmax ▸ Nat.maxPrimeFac_dvd
    have hde : d ∣ e := orderOf_dvd_iff_pow_eq_one.mpr ((hp_dvd_iff e he).mp hp_dvd_e)
    have hfac := Nat.pow_sub_one_dvd_pow_sub_one q hde
    have hnd' : 1 < q ^ d - 1 := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hnd hp_dvd_d)
    have hne : q ^ e - 1 ≠ 0 := by have := hqpow e he; omega
    apply Nat.maxPrimeFac_eq_of_dvd_of_le _ _ hnd hp hp_dvd_d
    rw [← hpmax]
    exact Nat.le_maxPrimeFac hne (Nat.prime_maxPrimeFac_of_one_lt _ hnd')
      (Nat.maxPrimeFac_dvd.trans hfac)
  · intro h
    exact ⟨d, hd, h⟩

end OMA.Erdos649

theorem OMA.solution : OMA.R_Erdos649_erdos_649_variants_tong_question_R1.H1 :=
  OMA.Erdos649.purePower_iff
