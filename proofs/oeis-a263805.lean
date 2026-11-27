import OMAStatements.S_oeis_a263805

namespace R157
open OMA.S_oeis_a263805

def g (t : ℕ) (i : ℤ) : Bool := decide (0 ≤ i ∨ i < -(t : ℤ) ∨ (i % 2 = 0 ∧ -(t : ℤ) < i))

theorem g_iff (t : ℕ) (i : ℤ) :
    g t i = true ↔ (0 ≤ i ∨ i < -(t : ℤ) ∨ (i % 2 = 0 ∧ -(t : ℤ) < i)) := by
  simp [g]

theorem step (t : ℕ) (ht : 1 ≤ t) (i : ℤ) :
    ruleOut 157 (g t (i - 1)) (g t i) (g t (i + 1)) = g (t + 1) i := by
  cases h1 : g t (i - 1) <;> cases h2 : g t i <;> cases h3 : g t (i + 1) <;>
    cases h4 : g (t + 1) i <;>
    simp only [g, decide_eq_true_eq, decide_eq_false_iff_not, Nat.cast_add, Nat.cast_one] at h1 h2 h3 h4 <;>
    first | decide | (exfalso; omega)

theorem cell_succ (t : ℕ) (i : ℤ) : cell 157 (t + 1) i = g (t + 1) i := by
  induction t generalizing i with
  | zero =>
    show ruleOut 157 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
    cases h1 : decide (i - 1 = 0) <;> cases h2 : decide (i = 0) <;> cases h3 : decide (i + 1 = 0) <;>
      cases h4 : g (0 + 1) i <;>
      simp only [g, decide_eq_true_eq, decide_eq_false_iff_not, Nat.cast_add, Nat.cast_one,
        Nat.cast_zero] at h1 h2 h3 h4 <;>
      first | decide | (exfalso; omega)
  | succ t ih =>
    show ruleOut 157 (cell 157 (t + 1) (i - 1)) (cell 157 (t + 1) i) (cell 157 (t + 1) (i + 1)) = _
    rw [ih, ih, ih]
    exact step (t + 1) (by omega) i

def S (b : ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 157 n ((j : ℤ) - n) then b ^ (2 * n - j) else 0

def Q (b : ℤ) (m : ℕ) : ℤ := ∑ x ∈ Finset.range m, if x % 2 = 1 then b ^ x else 0

theorem Q_succ (b : ℤ) (m : ℕ) : Q b (m + 1) = Q b m + if m % 2 = 1 then b ^ m else 0 :=
  Finset.sum_range_succ _ _

theorem Q_odd (b : ℤ) (k : ℕ) : Q b (2 * k + 1) = Q b (2 * k) := by
  rw [Q_succ, if_neg (by omega), add_zero]

theorem Q_even (b : ℤ) (k : ℕ) : (b ^ 2 - 1) * Q b (2 * k) = b ^ (2 * k + 1) - b := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Q_succ, Q_odd, if_pos (by omega), mul_add, ih]
    ring

theorem S_succ (b : ℤ) (m : ℕ) :
    S b (m + 1) = (∑ e ∈ Finset.range (m + 2), b ^ e) + b ^ (m + 2) * Q b m := by
  unfold S
  rw [← Finset.sum_range_reflect]
  rw [Finset.sum_congr rfl
    (g := fun e => if (e < m + 2 ∨ ((e + m) % 2 = 1 ∧ e < 2 * m + 2)) then b ^ e else 0) ?_]
  · rw [show 2 * (m + 1) + 1 = (m + 2) + (m + 1) by ring, Finset.sum_range_add,
      Finset.sum_range_succ _ m]
    rw [if_neg (by omega), add_zero]
    congr 1
    · exact Finset.sum_congr rfl (fun e he => if_pos (Or.inl (Finset.mem_range.mp he)))
    · unfold Q
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' := Finset.mem_range.mp hx
      by_cases h2 : x % 2 = 1
      · rw [if_pos (by omega), if_pos h2, pow_add]
      · rw [if_neg (by omega), if_neg h2, mul_zero]
  · intro e he
    have he' := Finset.mem_range.mp he
    rw [cell_succ]
    have hexp : 2 * (m + 1) - (2 * (m + 1) + 1 - 1 - e) = e := by omega
    have hi : (((2 * (m + 1) + 1 - 1 - e : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 - e := by
      omega
    rw [hexp, hi]
    clear hexp hi he
    by_cases hc : e < m + 2 ∨ (e + m) % 2 = 1 ∧ e < 2 * m + 2
    · rw [if_pos hc, if_pos ((g_iff _ _).mpr (by omega))]
    · rw [if_neg hc, if_neg (fun h => hc (by have := (g_iff _ _).mp h; omega))]

theorem key_odd (b : ℤ) (k : ℕ) :
    (b - 1) * (b ^ 2 - 1) * S b (2 * k + 1) =
      (b ^ 2 - 1) * (b ^ (2 * k + 2) - 1) + (b - 1) * b ^ (2 * k + 2) * (b ^ (2 * k + 1) - b) := by
  rw [S_succ]
  have h1 := geom_sum_mul b (2 * k + 2)
  have h2 := Q_even b k
  linear_combination (b ^ 2 - 1) * h1 + (b - 1) * b ^ (2 * k + 2) * h2

theorem key_even (b : ℤ) (k : ℕ) :
    (b - 1) * (b ^ 2 - 1) * S b (2 * k + 2) =
      (b ^ 2 - 1) * (b ^ (2 * k + 3) - 1) + (b - 1) * b ^ (2 * k + 3) * (b ^ (2 * k + 1) - b) := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, S_succ, Q_odd]
  have h1 := geom_sum_mul b (2 * k + 1 + 2)
  have h2 := Q_even b k
  linear_combination (b ^ 2 - 1) * h1 + (b - 1) * b ^ (2 * k + 1 + 2) * h2

theorem ha_odd (k : ℕ) :
    891 * a (2 * k + 1) =
      99 * (10 ^ (2 * k + 2) - 1) + 9 * 10 ^ (2 * k + 2) * (10 ^ (2 * k + 1) - 10) := by
  show 891 * S 10 (2 * k + 1) = _
  linear_combination key_odd 10 k

theorem ha_even (k : ℕ) :
    891 * a (2 * k + 2) =
      99 * (10 ^ (2 * k + 3) - 1) + 9 * 10 ^ (2 * k + 3) * (10 ^ (2 * k + 1) - 10) := by
  show 891 * S 10 (2 * k + 2) = _
  linear_combination key_even 10 k

theorem ha_zero : a 0 = 1 := by
  show S 10 0 = 1
  simp [S, cell]

theorem recur (m : ℕ) :
    a (m + 5) = 11 * a (m + 4) + 9990 * a (m + 3) - 110000 * a (m + 2) + 100000 * a (m + 1) := by
  have h : (891 : ℤ) * (a (m + 5) -
      (11 * a (m + 4) + 9990 * a (m + 3) - 110000 * a (m + 2) + 100000 * a (m + 1))) = 0 := by
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have e5 := ha_odd (k + 2)
      have e4 := ha_even (k + 1)
      have e3 := ha_odd (k + 1)
      have e2 := ha_even k
      have e1 := ha_odd k
      rw [show 2 * (k + 2) + 1 = 2 * k + 5 by ring] at e5
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring] at e4
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at e3
      linear_combination e5 - 11 * e4 - 9990 * e3 + 110000 * e2 - 100000 * e1
    · have e5 := ha_even (k + 2)
      have e4 := ha_odd (k + 2)
      have e3 := ha_even (k + 1)
      have e2 := ha_odd (k + 1)
      have e1 := ha_even k
      rw [show 2 * (k + 2) + 2 = 2 * k + 1 + 5 by ring] at e5
      rw [show 2 * (k + 2) + 1 = 2 * k + 1 + 4 by ring] at e4
      rw [show 2 * (k + 1) + 2 = 2 * k + 1 + 3 by ring] at e3
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring] at e2
      rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring] at e1
      linear_combination e5 - 11 * e4 - 9990 * e3 + 110000 * e2 - 100000 * e1
  have := (mul_eq_zero.mp h).resolve_left (by norm_num)
  linarith

end R157

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a263805.main := by
  open OMA.S_oeis_a263805 R157 in
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    exact recur m
  · have h1 : a 1 = 11 := by have := ha_odd 0; norm_num at this; linarith
    have h2 : a 2 = 111 := by have := ha_even 0; norm_num at this; linarith
    have h3 : a 3 = 101111 := by have := ha_odd 1; norm_num at this; linarith
    have h4 : a 4 = 1011111 := by have := ha_even 1; norm_num at this; linarith
    rw [show ((1 - X) * (1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ)
        = 1 - C 11 * X ^ 1 - C 9990 * X ^ 2 + C 110000 * X ^ 3 - C 100000 * X ^ 4 by
          simp only [map_ofNat]; ring,
      show (1 - 10000 * X ^ 2 + 100000 * X ^ 3 - 100000 * X ^ 4 : PowerSeries ℚ)
        = 1 - C 10000 * X ^ 2 + C 100000 * X ^ 3 - C 100000 * X ^ 4 by simp only [map_ofNat]]
    rw [show ∀ p : PowerSeries ℚ,
        p * (1 - C 11 * X ^ 1 - C 9990 * X ^ 2 + C 110000 * X ^ 3 - C 100000 * X ^ 4)
        = p - C 11 * (p * X ^ 1) - C 9990 * (p * X ^ 2) + C 110000 * (p * X ^ 3)
          - C 100000 * (p * X ^ 4)
        from fun p => by ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
    rcases n with _ | _ | _ | _ | _ | n
    · simp [ha_zero]
    · simp [ha_zero, h1]
    · simp [ha_zero, h1, h2]; norm_num
    · simp [ha_zero, h1, h2, h3]; norm_num
    · simp [ha_zero, h1, h2, h3, h4]; norm_num
    · have := recur n
      simp only [show n + 1 + 1 + 1 + 1 + 1 = n + 5 by ring]
      simp
      rw [this]
      push_cast
      ring
  · rintro n ⟨k, rfl⟩
    have hq : (891 : ℚ) * (a (2 * k + 1) : ℚ) =
        99 * ((10 : ℚ) ^ (2 * k + 2) - 1) + 9 * (10 : ℚ) ^ (2 * k + 2) * ((10 : ℚ) ^ (2 * k + 1) - 10) := by
      exact_mod_cast ha_odd k
    rw [zpow_natCast]
    linear_combination (1 / 891 : ℚ) * hq
  · rintro n hn ⟨r, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [show k + 1 + (k + 1) = 2 * k + 2 by ring]
    have hq : (891 : ℚ) * (a (2 * k + 2) : ℚ) =
        99 * ((10 : ℚ) ^ (2 * k + 3) - 1) + 9 * (10 : ℚ) ^ (2 * k + 3) * ((10 : ℚ) ^ (2 * k + 1) - 10) := by
      exact_mod_cast ha_even k
    rw [zpow_natCast]
    linear_combination (1 / 891 : ℚ) * hq
