import OMAStatements.S_oeis_a182085
import Mathlib

namespace OMASol_oeis_a182085

theorem korselt_one (l d t a : ℕ) (hl : l.Prime) (hd : l = d + 1) :
    a ^ (d * t + 1) ≡ a [MOD l] := by
  haveI := Fact.mk hl
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  by_cases h : (a : ZMod l) = 0
  · simp [h]
  · have hd' : d = l - 1 := by omega
    rw [pow_succ, pow_mul, hd', ZMod.pow_card_sub_one_eq_one h, one_pow, one_mul]

theorem combine (p q r a N : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : a ^ N ≡ a [MOD p]) (h2 : a ^ N ≡ a [MOD q]) (h3 : a ^ N ≡ a [MOD r]) :
    a ^ N ≡ a [MOD p * q * r] := by
  have cpq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have cpr : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  have cqr : q.Coprime r := (Nat.coprime_primes hq hr).mpr hqr
  have h12 : a ^ N ≡ a [MOD p * q] := (Nat.modEq_and_modEq_iff_modEq_mul cpq).mp ⟨h1, h2⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.mul cpr cqr)).mp ⟨h12, h3⟩

end OMASol_oeis_a182085

theorem OMA.solution : type_of% @OMA.S_oeis_a182085.main := by
  intro k hp hq hr
  refine ⟨?_, ?_, ?_⟩
  · have : 1 < (30 * k + 7) * (60 * k + 13) := by nlinarith
    nlinarith
  · exact Nat.not_prime_mul (by nlinarith) (by omega)
  · intro a
    apply OMASol_oeis_a182085.combine _ _ _ a _ hp hq hr (by omega) (by omega) (by omega)
    · have e : (30 * k + 7) * (60 * k + 13) * (150 * k + 31)
          = (30 * k + 6) * (9000 * k ^ 2 + 4110 * k + 470) + 1 := by ring
      rw [e]; exact OMASol_oeis_a182085.korselt_one _ _ _ a hp (by omega)
    · have e : (30 * k + 7) * (60 * k + 13) * (150 * k + 31)
          = (60 * k + 12) * (4500 * k ^ 2 + 2055 * k + 235) + 1 := by ring
      rw [e]; exact OMASol_oeis_a182085.korselt_one _ _ _ a hq (by omega)
    · have e : (30 * k + 7) * (60 * k + 13) * (150 * k + 31)
          = (150 * k + 30) * (1800 * k ^ 2 + 822 * k + 94) + 1 := by ring
      rw [e]; exact OMASol_oeis_a182085.korselt_one _ _ _ a hr (by omega)
