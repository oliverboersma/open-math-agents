import OMAStatements.S_oeis_a394431

namespace OMA.S_oeis_a394431

private theorem split {b n : ℕ} (hb : 1 < b) (hn : 0 < n) :
    ds b n = n%b + ds b (n/b) := by
  unfold ds
  rw [Nat.digits_def' hb hn, List.sum_cons]

-- For bases exceeding half of n, the two digits are 1 and n-b.
private theorem upper_base {b n : ℕ} (hb : 1 < b) (hle : b ≤ n) (hn : n < 2*b) :
    ds b n = 1+(n-b) := by
  have hq : n/b = 1 := Nat.div_eq_of_lt_le (by simpa using hle) (by simpa using hn)
  have h1 : ds b 1 = 1 := by simp [ds, Nat.digits_of_lt b 1 one_ne_zero hb]
  have hr := Nat.mod_add_div n b
  rw [hq, mul_one] at hr
  rw [split hb (by omega), hq,h1]
  omega

-- For bases at most half of n, the digit sum is strictly less than n/2.
private theorem lower_base {b n : ℕ} (hb : 1 < b) (hn : 8 < n) (hl : 2*b ≤ n) :
    2*ds b n < n := by
  let q := n/b
  let r := n%b
  have hparts : r+b*q=n := Nat.mod_add_div _ _
  have hr : r < b := Nat.mod_lt _ (by omega)
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr hl
  have hds : ds b n = r+ds b q := split hb (by omega)
  rw [hds]
  have hsmall : ds b q ≤ q := Nat.digit_sum_le _ _
  by_cases hb2 : b = 2
  · subst b
    have hstrict : ds 2 q < q := by
      rw [split (by decide : 1 < 2) (by omega)]
      have hs : ds 2 (q/2) ≤ q/2 := Nat.digit_sum_le _ _
      omega
    omega
  by_cases hb3 : b = 3
  · subst b
    have hq3 : 3 ≤ q := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    omega
  have hprod : 2*q+b ≤ b*q := by
    calc
      2*q+b ≤ 2*q+(b-2)*2 := by omega
      _ ≤ 2*q+(b-2)*q := Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _
      _ = b*q := by rw [← Nat.add_mul, show 2+(b-2)=b by omega]
  omega

end OMA.S_oeis_a394431

open OMA.S_oeis_a394431 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394431.main := by
  intro n hn
  let b := n/2+1
  have h1 : 1 < b := by dsimp only [b]; omega
  have h2 : b < n := by dsimp only [b]; omega
  have hb : ds b n = 1+(n-b) := upper_base h1 h2.le (by dsimp only [b]; omega)
  have less {c : ℕ} (hc1 : 1 < c) (hcn : c < n) (hc : c ≠ b) : ds c n < ds b n := by
    rw [hb]
    rcases lt_or_gt_of_ne hc with h | h
    · have hsmall := lower_base hc1 hn (show 2*c ≤ n by dsimp only [b] at h; omega)
      dsimp only [b]
      omega
    · rw [upper_base hc1 hcn.le (by dsimp only [b] at h; omega)]
      omega
  constructor
  · refine ⟨h1,h2,?_⟩
    intro c hc hc'
    by_cases h : c = b
    · subst c; exact le_rfl
    · exact (less hc hc' h).le
  · intro c hc
    by_contra! h
    have hlt := less hc.1 hc.2.1 (by omega : c ≠ b)
    exact (not_le_of_gt hlt) (hc.2.2 b h1 h2)
