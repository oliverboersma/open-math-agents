import OMAStatements.S_oeis_a003500
import Mathlib

-- Problem: oeis-a003500
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P003500
open OMA.S_oeis_a003500

lemma key : ∀ n : ℕ, 2 ∣ a n ∧ 2 ∣ a (n + 1) ∧ 2 ≤ a n ∧ a n < a (n + 1)
  | 0 => by decide
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := key n
    refine ⟨h2, ?_, by omega, ?_⟩
    · rw [show n + 1 + 1 = n + 2 by ring, a]; omega
    · rw [show n + 1 + 1 = n + 2 by ring, a]; omega

theorem sol : type_of% @OMA.S_oeis_a003500.main := by
  intro p hp
  obtain ⟨h1, -, h3, -⟩ := key p
  have hp2 : 2 ≤ p := hp.two_le
  have hgt : 2 < a p := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have := (key q).2.2
    omega
  refine ⟨by omega, ?_⟩
  intro hpr
  rw [Int.prime_iff_natAbs_prime] at hpr
  have h2 : 2 ∣ (a p).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa using this
  have := (Nat.Prime.eq_one_or_self_of_dvd hpr 2 h2)
  omega

end OMA.P003500

theorem OMA.solution : type_of% @OMA.S_oeis_a003500.main := OMA.P003500.sol
