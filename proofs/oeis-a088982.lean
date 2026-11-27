import OMAStatements.S_oeis_a088982
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a088982.main := by
  intro x hx
  have hsm : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  set a := Nat.nth Nat.Prime (x - 1) with ha
  set b := Nat.nth Nat.Prime x with hb
  have hpa : a.Prime := Nat.prime_nth_prime _
  have hpb : b.Prime := Nat.prime_nth_prime _
  have hab : a < b := hsm (by omega)
  have ha2 : 2 < a := by
    have : Nat.nth Nat.Prime 0 < a := hsm (by omega)
    rwa [Nat.nth_prime_zero_eq_two] at this
  have hb2 : b ≠ 2 := by omega
  have hoa : Odd a := hpa.odd_of_ne_two (by omega)
  have hob : Odd b := hpb.odd_of_ne_two hb2
  have hab2 : a + 2 ≤ b := by
    obtain ⟨i, hi⟩ := hoa
    obtain ⟨j, hj⟩ := hob
    omega
  refine ⟨Nat.nth Nat.Prime a, Nat.prime_nth_prime _, ?_, ?_⟩
  · show Nat.nth Nat.Prime (a - 1) < Nat.nth Nat.Prime a
    exact hsm (by omega)
  · show Nat.nth Nat.Prime a < Nat.nth Nat.Prime (b - 1)
    exact hsm (by omega)
