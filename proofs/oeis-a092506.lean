import OMAStatements.S_oeis_a092506
import Mathlib

namespace TotientFermatForm

private theorem even_totient (m : ℕ) (hm : 0 < m) (he : Even m) :
    2*m.totient ≤ m ∧ (2*m.totient = m → ∃ j : ℕ, m = 2^j) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    obtain ⟨r, rfl⟩ := even_iff_two_dvd.mp he
    have hr : 0 < r := by omega
    by_cases hre : Even r
    · obtain ⟨hb, heq⟩ := ih r (by omega) hr hre
      rw [Nat.totient_two_mul_of_even hre]
      refine ⟨by omega, fun h => ?_⟩
      obtain ⟨j, hj⟩ := heq (by omega)
      refine ⟨j+1, ?_⟩
      rw [hj, pow_succ, mul_comm]
    · have hro : Odd r := Nat.not_even_iff_odd.mp hre
      rw [Nat.totient_two_mul_of_odd hro]
      refine ⟨by have := Nat.totient_le r; omega, fun heq => ?_⟩
      have hr1 : r = 1 := by
        by_contra hn
        have := Nat.totient_lt r (by omega)
        omega
      exact ⟨1, by simp [hr1]⟩

theorem main :
    {x : ℕ | 1 ≤ x ∧ Nat.totient x + Nat.totient (x - 1) = (3 * x - 2) / 2} =
      {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 2 ^ n + 1} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hphi⟩
    by_cases hsmall : x ≤ 2
    · interval_cases x
      · norm_num at hphi
      · exact ⟨Nat.prime_two, 0, rfl⟩
    have hx3 : 3 ≤ x := by omega
    have hodd : ¬ Even x := by
      intro he
      have h₁ := (even_totient x (by omega) he).1
      have h₂ := Nat.totient_lt (x-1) (by omega)
      rw [Nat.even_iff] at he
      omega
    have hxmod : x%2 = 1 := by
      rw [Nat.even_iff] at hodd
      omega
    have hep : Even (x-1) := by
      rw [Nat.even_iff]
      omega
    have h₂ := even_totient (x-1) (by omega) hep
    have h₁ := Nat.totient_lt x (by omega)
    have hprime : x.Prime := (Nat.totient_eq_iff_prime (by omega)).mp (by omega)
    obtain ⟨j,hj⟩ := h₂.2 (by omega)
    exact ⟨hprime, j, by omega⟩
  · rintro ⟨hp, j, rfl⟩
    cases j with
    | zero => decide
    | succ j =>
      refine ⟨Nat.succ_pos _, ?_⟩
      rw [Nat.totient_prime hp, Nat.add_sub_cancel]
      have hphi := Nat.totient_prime_pow_succ Nat.prime_two j
      have hpw : (2:ℕ)^(j+1) = 2^j*2 := pow_succ 2 j
      rw [hphi, hpw]
      omega

end TotientFermatForm

theorem OMA.solution : type_of% @OMA.S_oeis_a092506.main := TotientFermatForm.main