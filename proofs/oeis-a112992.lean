import OMAStatements.S_oeis_a112992

open OMA.S_oeis_a112992 in
lemma OMA.a112992_J_closed (m : ℕ) : 3 * (J m : ℤ) + (-1) ^ m = 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [J]
    | 1 => norm_num [J]
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      simp only [J]
      push_cast
      linear_combination h1 + 2 * h0

open OMA.S_oeis_a112992 in
lemma OMA.a112992_J_odd (m : ℕ) (hm : 1 ≤ m) : Odd (J m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => simp [J]
    | n + 2 =>
      simp only [J]
      have h1 := ih (n + 1) (by omega) (by omega)
      exact h1.add_even (even_two_mul _)

open OMA.S_oeis_a112992 in
lemma OMA.a112992_ceil (m : ℕ) :
    ⌈((2 : ℚ) ^ m) / 3⌉ = (J m : ℤ) + (if Even m then 1 else 0) := by
  have h := OMA.a112992_J_closed m
  rw [Int.ceil_eq_iff]
  have hq : (2 : ℚ) ^ m = 3 * (J m : ℚ) + (-1) ^ m := by
    exact_mod_cast h.symm
  rcases Nat.even_or_odd m with he | ho
  · rw [if_pos he]
    rw [he.neg_one_pow] at hq
    push_cast
    constructor <;> linarith
  · rw [if_neg (Nat.not_even_iff_odd.2 ho)]
    rw [ho.neg_one_pow] at hq
    push_cast
    constructor <;> linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a112992.main := by
  intro k _
  have hc : OMA.S_oeis_a112992.c k = (OMA.S_oeis_a112992.J (2 ^ k % k) : ℤ) +
      (if Even (2 ^ k % k) then 1 else 0) := OMA.a112992_ceil _
  rw [hc]
  rcases Nat.even_or_odd (2 ^ k % k) with he | ho
  · rw [if_pos he]
    rcases Nat.eq_zero_or_pos (2 ^ k % k) with h0 | hpos
    · rw [h0]
      refine ⟨fun _ => ⟨1, by simp [OMA.S_oeis_a112992.J]⟩, fun hev => ?_⟩
      exfalso
      simp [OMA.S_oeis_a112992.J] at hev
    · have hJ := OMA.a112992_J_odd (2 ^ k % k) hpos
      refine ⟨fun hodd => ?_, fun _ => ⟨_, rfl⟩⟩
      exfalso
      have : Even ((OMA.S_oeis_a112992.J (2 ^ k % k) : ℤ) + 1) :=
        (Int.odd_coe_nat _ |>.2 hJ).add_one
      exact (Int.not_even_iff_odd.2 hodd) this
  · rw [if_neg (Nat.not_even_iff_odd.2 ho), add_zero]
    have hJ := OMA.a112992_J_odd (2 ^ k % k) ho.pos
    refine ⟨fun _ => ⟨_, rfl⟩, fun hev => ?_⟩
    exfalso
    exact (Int.not_even_iff_odd.2 ((Int.odd_coe_nat _).2 hJ)) hev
