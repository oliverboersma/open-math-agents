import OMAStatements.S_oeis_a328002
import Mathlib.Tactic

namespace OMA.Ratio328002
open OMA.S_oeis_a328002

def prod (k : ℕ) : ℚ := ∏ i ∈ Finset.range k, factor (i+1)
def total (k : ℕ) : ℚ := ∑ i ∈ Finset.range (k+1), prod i

lemma prod_step (k : ℕ) : prod (k+1) = prod k * factor (k+1) :=
  Finset.prod_range_succ _ _
lemma total_step (k : ℕ) : total (k+1) = total k + prod (k+1) :=
  Finset.sum_range_succ _ _

lemma prod_pos (k : ℕ) : 0 < prod k := by
  apply Finset.prod_pos
  intro i hi
  unfold factor
  split <;> positivity

lemma prod_odd (m : ℕ) : prod (2*m+1) = prod (2*m) * ((2*(m:ℚ)+1)/2) := by
  rw [prod_step, factor, if_neg (by omega)]
  push_cast
  ring

lemma prod_even (m : ℕ) :
    prod (2*m+1+1) = prod (2*m+1) * (1/((m:ℚ)+1)) := by
  rw [prod_step, factor, if_pos (by omega)]
  push_cast
  field_simp
  ring

lemma total_even (m : ℕ) :
    total (2*m) = (2*(m:ℚ)+1)*(m+3)*prod (2*m)/3 := by
  induction m with
  | zero => norm_num [total, prod]
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega, total_step, total_step, ih,
      prod_even, prod_odd]
    push_cast
    field_simp
    ring

lemma total_odd (m : ℕ) :
    total (2*m+1) = (2*(m:ℚ)+1)*(2*m+9)*prod (2*m)/6 := by
  rw [total_step, total_even, prod_odd]
  ring

lemma q_even (m : ℕ) : q (2*m) - 2 = 3/((m:ℚ)+3) := by
  change (2:ℚ)^(2*m+1) * total (2*m+1) / (2^(2*m)*total (2*m)) - 2 = _
  rw [pow_succ, total_odd, total_even]
  have hp := prod_pos (2*m)
  field_simp
  ring

lemma q_odd (m : ℕ) : q (2*m+1) - 2 = 6/(((m:ℚ)+1)*(2*m+9)) := by
  change (2:ℚ)^(2*m+1+1) * total (2*m+1+1) / (2^(2*m+1)*total (2*m+1)) - 2 = _
  rw [pow_succ, show 2*m+1+1 = 2*(m+1) by omega, total_even, total_odd,
    show 2*(m+1) = 2*m+1+1 by omega, prod_even, prod_odd]
  push_cast
  have hp := prod_pos (2*m)
  field_simp
  ring

lemma excess_num (r : ℚ) : (r-2).num = r.num-2*(r.den:ℤ) := by
  have hd : (r-2).den = r.den := Rat.sub_intCast_den r (2:ℤ)
  have h := Rat.num_div_den (r-2)
  rw [hd] at h
  have h' := Rat.num_div_den r
  have hpos : (r.den:ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  field_simp at h h'
  exact_mod_cast (show ((r-2).num:ℚ) = (r.num:ℚ)-2*(r.den:ℚ) by linarith)

lemma frac_num (a b : ℕ) (hb : 0 < b) :
    ((a:ℚ)/b).num = (a:ℤ)/(Nat.gcd b a : ℕ) := by
  have hpos : 0 < (b:ℤ) := by exact_mod_cast hb
  rw [show (a:ℚ)/(b:ℚ) = Rat.divInt (a:ℤ) (b:ℤ) by simp [Rat.divInt_eq_div],
    Rat.num_divInt, Int.sign_eq_one_of_pos hpos, one_mul]
  rfl

end OMA.Ratio328002

open OMA.S_oeis_a328002 OMA.Ratio328002

theorem OMA.solution : type_of% @OMA.S_oeis_a328002.main := by
  intro n
  obtain ⟨m, hm | hm⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2, by omega⟩
  · subst n
    unfold d
    rw [← excess_num, q_even]
    rw [show (3:ℚ)/((m:ℚ)+3) = ((3:ℕ):ℚ)/((m+3:ℕ):ℚ) by push_cast; rfl,
      frac_num _ _ (by omega), Nat.gcd_comm, Nat.gcd_rec]
    have h := Nat.mod_lt m (by decide : 0 < 6)
    interval_cases v : m % 6 <;>
      rw [show (2*m)%12 = 2*(m%6) by omega, v,
        show (m+3)%3 = (m%6)%3 by omega, v] <;> decide
  · subst n
    unfold d
    rw [← excess_num, q_odd]
    rw [show (6:ℚ)/(((m:ℚ)+1)*(2*m+9)) =
      ((6:ℕ):ℚ)/(((m+1)*(2*m+9):ℕ):ℚ) by push_cast; rfl,
      frac_num _ _ (by positivity), Nat.gcd_comm, Nat.gcd_rec]
    have h := Nat.mod_lt m (by decide : 0 < 6)
    interval_cases v : m % 6 <;>
      rw [show (2*m+1)%12 = 2*(m%6)+1 by omega, v,
        Nat.mul_mod, show (m+1)%6 = ((m%6)+1)%6 by omega,
        show (2*m+9)%6 = (2*(m%6)+9)%6 by omega, v] <;> decide
