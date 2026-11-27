import OMAStatements.S_oeis_a244626
import Mathlib

/-!
# Proof of OEIS A244626 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a244626.main := by
  intro p hp hmod
  let : Fact p.Prime := ⟨hp⟩
  have hp₂ : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by omega
  have hsymbol : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two hp₂, ZMod.χ₈_nat_eq_if_mod_eight, hodd]
    rcases hmod with h | h <;> simp [h]
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hpow : ((2 ^ ((p - 1) / 2) : ℕ) : ZMod p) = -1 := by
    simpa [hsymbol, hhalf] using (legendreSym.eq_pow p 2).symm
  have hval := congrArg ZMod.val (hpow.trans hcast.symm)
  rw [ZMod.val_natCast, ZMod.val_natCast_of_lt (Nat.sub_lt hp.pos Nat.one_pos)] at hval
  exact hval
