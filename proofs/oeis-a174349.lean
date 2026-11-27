import OMAStatements.S_oeis_a174349
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a174349.main := by
  intro i hi
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  constructor
  · rintro ⟨n, hn, h⟩ rfl
    have h' : OMA.S_oeis_a174349.prime (1 + 1) = OMA.S_oeis_a174349.prime 1 + 2 * n := h.2
    unfold OMA.S_oeis_a174349.prime at h'
    norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three] at h'
    omega
  · intro hne
    have hp := Nat.prime_nth_prime (i - 1)
    have hq := Nat.prime_nth_prime i
    have hlt : Nat.nth Nat.Prime (i - 1) < Nat.nth Nat.Prime i := hmono (by omega)
    have h3 : 3 ≤ Nat.nth Nat.Prime (i - 1) := by
      have h := hmono.monotone (show 1 ≤ i - 1 by omega)
      rw [Nat.nth_prime_one_eq_three] at h
      exact h
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two (by omega)
    refine ⟨b - a, by omega, hi, ?_⟩
    show OMA.S_oeis_a174349.prime (i + 1) = OMA.S_oeis_a174349.prime i + 2 * (b - a)
    unfold OMA.S_oeis_a174349.prime
    rw [Nat.add_sub_cancel]
    omega
