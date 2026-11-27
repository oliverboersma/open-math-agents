import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

/-! A zero among the low ternary digits certifies that the whole numeral
cannot consist entirely of ones and twos. Stop at a zero quotient so that
leading zeros never count. -/

namespace OMA.Ternary

def zeroIn : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n => n != 0 && (n % 3 == 0 || zeroIn fuel (n / 3))

lemma sound {fuel n : ℕ} (h : zeroIn fuel n = true) : 0 ∈ Nat.digits 3 n := by
  induction fuel generalizing n with
  | zero => simp [zeroIn] at h
  | succ fuel ih =>
    simp only [zeroIn, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq] at h
    rw [Nat.digits_eq_cons_digits_div (by decide) h.1]
    rcases h.2 with hz | ht
    · simp [hz]
    · exact List.mem_cons_of_mem _ (ih ht)

set_option maxRecDepth 8192 in
lemma table : (List.range 985).all (fun i => zeroIn 26 (2 ^ (i + 16))) = true := by
  decide +kernel

end OMA.Ternary

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  intro k hk hl sub
  have h := List.all_eq_true.mp OMA.Ternary.table (k - 16) (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel (by omega)] at h
  have := sub (OMA.Ternary.sound h)
  simp at this
