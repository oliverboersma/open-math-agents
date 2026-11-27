import OMAStatements.S_oeis_a308090
import Mathlib

/-!
# Proof of OEIS A308090 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a308090.main := by
  intro n hn ha
  by_contra hnp
  obtain ⟨d, hd, hd₂, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  have hfac : d ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hcommon : d ∣ Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial) := by
    rw [← ha] at hd
    exact hd.trans (Nat.gcd_dvd_left _ _)
  have htwo : d ∣ 2 ^ n :=
    (Nat.dvd_add_iff_left hfac).mpr (hcommon.trans (Nat.gcd_dvd_left _ _))
  have hthree : d ∣ 3 ^ n :=
    (Nat.dvd_add_iff_left hfac).mpr (hcommon.trans (Nat.gcd_dvd_right _ _))
  have hcop : Nat.Coprime 2 3 := by decide
  have hg : Nat.gcd (2 ^ n) (3 ^ n) = 1 := hcop.pow n n
  have hone : d ∣ 1 := hg ▸ Nat.dvd_gcd htwo hthree
  have hd₁ := Nat.dvd_one.mp hone
  omega
