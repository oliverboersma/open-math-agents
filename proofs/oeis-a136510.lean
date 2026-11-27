import OMAStatements.S_oeis_a136510
import Mathlib

-- Problem: oeis-a136510, for every n > 0 some power n^k with k > 1 contains the binary
-- expansion of n as a block of consecutive digits.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Write n = 2^a m with m odd and let L be the number of binary digits of m. With
-- e = phi(2^L), Euler gives m^(e+1) = m + 2^L q, so the binary digits of m^(e+1) start (from
-- the low end) with those of m. Then n^(e+1) = 2^(a(e+1)) m^(e+1) has the digits: a(e+1)
-- zeros, the digits of m, the digits of q, which contains a zeros followed by the digits of m.

theorem OMA.solution : type_of% @OMA.S_oeis_a136510.main := by
  intro n hn
  have hne : ∃ k, k ∈ OMA.S_oeis_a136510.exponents n := by
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
    have hm0 : 0 < m := hm.pos
    obtain ⟨L, hL⟩ : ∃ L, L = (Nat.digits 2 m).length := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = Nat.totient (2 ^ L) := ⟨_, rfl⟩
    have hcop : Nat.Coprime m (2 ^ L) := Nat.Coprime.pow_right L (Nat.coprime_two_right.mpr hm)
    have hpow : m ^ e ≡ 1 [MOD 2 ^ L] := by rw [he]; exact Nat.ModEq.pow_totient hcop
    have h1 : m ^ (e + 1) ≡ m [MOD 2 ^ L] := by
      have h2 := hpow.mul_right m
      rw [one_mul, ← pow_succ] at h2
      exact h2
    have hle : m ≤ m ^ (e + 1) := Nat.le_self_pow (by omega) m
    have hdvd : 2 ^ L ∣ m ^ (e + 1) - m := (Nat.modEq_iff_dvd' hle).mp h1.symm
    obtain ⟨q, hq⟩ := hdvd
    have hmk : m ^ (e + 1) = m + 2 ^ L * q := by omega
    have hd1 : Nat.digits 2 (2 ^ a * m) = List.replicate a 0 ++ Nat.digits 2 m :=
      Nat.digits_base_pow_mul (by norm_num) hm0
    have hd2 : Nat.digits 2 (m ^ (e + 1)) = Nat.digits 2 m ++ Nat.digits 2 q := by
      rw [hmk, hL]
      exact (Nat.digits_append_digits (by norm_num)).symm
    have hd3 : Nat.digits 2 ((2 ^ a * m) ^ (e + 1)) =
        List.replicate (a * (e + 1)) 0 ++ Nat.digits 2 (m ^ (e + 1)) := by
      rw [mul_pow, ← pow_mul]
      exact Nat.digits_base_pow_mul (by norm_num) (pow_pos hm0 _)
    refine ⟨e + 1, ?_⟩
    show 1 < e + 1 ∧ (Nat.digits 2 (2 ^ a * m)).IsInfix (Nat.digits 2 ((2 ^ a * m) ^ (e + 1)))
    have he0 : 0 < e := by rw [he]; exact Nat.totient_pos.mpr (by positivity)
    refine ⟨by omega, ?_⟩
    rw [hd1, hd3, hd2]
    refine ⟨List.replicate (a * e) 0, Nat.digits 2 q, ?_⟩
    have hrep : List.replicate (a * (e + 1)) (0 : ℕ) =
        List.replicate (a * e) 0 ++ List.replicate a 0 := by
      rw [← List.replicate_add, Nat.mul_succ]
    rw [hrep]
    simp only [List.append_assoc]
  classical
  exact ⟨Nat.find hne, Nat.find_spec hne, fun k hk => Nat.find_min' hne hk⟩
