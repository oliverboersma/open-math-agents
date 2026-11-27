import OMAStatements.S_oeis_a268466
import Mathlib

namespace OMA.A268466Aux

theorem geom_mod_two (m : ℕ) (hm : m % 2 = 1) :
    ∀ n, (∑ i ∈ Finset.range n, m ^ i) % 2 = n % 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hm, one_pow]
    omega

theorem not_modEq (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm1 : 1 < m) (hm2 : m ≤ 2 ^ k) :
    ¬ m ^ m ≡ 1 [MOD 2 ^ k] := by
  intro h
  rcases Nat.even_or_odd m with he | ho
  · have h2 : m ^ m ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) h
    have hm0 : m % 2 = 0 := Nat.even_iff.1 he
    unfold Nat.ModEq at h2
    rw [Nat.pow_mod, hm0, zero_pow (by omega)] at h2
    simp at h2
  · have hmo : m % 2 = 1 := Nat.odd_iff.1 ho
    have hpos : 1 ≤ m ^ m := Nat.one_le_pow _ _ (by omega)
    have hd : 2 ^ k ∣ m ^ m - 1 := (Nat.modEq_iff_dvd' hpos).1 h.symm
    have heq : m ^ m - 1 = (m - 1) * ∑ i ∈ Finset.range m, m ^ i := by
      rw [mul_comm, geom_sum_mul_of_one_le (by omega)]
    rw [heq] at hd
    have hS : Odd (∑ i ∈ Finset.range m, m ^ i) := by
      rw [Nat.odd_iff, geom_mod_two m hmo m, hmo]
    have hc : Nat.Coprime (2 ^ k) (∑ i ∈ Finset.range m, m ^ i) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hS)
    have hd2 : 2 ^ k ∣ m - 1 := hc.dvd_of_dvd_mul_right hd
    have := Nat.le_of_dvd (by omega) hd2
    omega

theorem a_pow (k : ℕ) (hk : 1 ≤ k) : OMA.S_oeis_a268466.a (2 ^ k) = 2 ^ k + 1 := by
  unfold OMA.S_oeis_a268466.a
  have hmem : 2 ^ k + 1 ∈ {m : ℕ | 1 < m ∧ m ^ m ≡ 1 [MOD 2 ^ k]} := by
    refine ⟨by have := Nat.one_le_two_pow (n := k); omega, ?_⟩
    have h1 : 2 ^ k + 1 ≡ 1 [MOD 2 ^ k] := by
      unfold Nat.ModEq
      simp [Nat.add_mod]
    simpa using h1.pow (2 ^ k + 1)
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro m hm
  by_contra hlt
  exact not_modEq k hk m hm.1 (by omega) hm.2

end OMA.A268466Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a268466.main := by
  have hinj : Function.Injective (fun k : ℕ => 2 ^ (k + 1)) := by
    intro x y hxy
    have := Nat.pow_right_injective (le_refl 2) hxy
    omega
  apply Set.infinite_of_injective_forall_mem hinj
  intro k
  refine ⟨?_, ?_⟩
  · have := Nat.one_le_two_pow (n := k)
    simp only [pow_succ]
    omega
  · rw [OMA.A268466Aux.a_pow (k + 1) (by omega)]
    have he : Even (2 ^ (k + 1)) := (Nat.even_pow).2 ⟨even_two, by omega⟩
    rw [he.neg_one_pow]
    push_cast
    ring
