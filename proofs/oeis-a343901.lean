import OMAStatements.S_oeis_a343901
import Mathlib

/-!
# Proof of OEIS A343901 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a343901.main := by
  intro n hn
  let S : Set ℕ := {p | p.Prime ∧ (p - 1) ∣ Nat.totient n}
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  have hfinite : S.Finite := by
    refine (Set.finite_Iic (Nat.totient n + 1)).subset ?_
    intro p hp
    have hdiv : (p - 1) ∣ Nat.totient n := hp.2
    have hbound := Nat.le_of_dvd hpos hdiv
    change p ≤ Nat.totient n + 1
    omega
  have hmem : 2 ∈ S := ⟨Nat.prime_two, one_dvd _⟩
  exact (Set.ncard_pos hfinite).mpr ⟨2, hmem⟩
