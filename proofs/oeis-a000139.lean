import OMAStatements.S_oeis_a000139

-- Problem: A000139
-- Statement: statements/oeis-a000139.lean
-- Credit: @Heart-galaxy

/-!
The factorial quotient has the same parity as `Nat.choose (3 * n) (n + 1)`.
Lucas's theorem reduces oddness to the absence of a binary carry.
The parity characterization is recorded at https://oeis.org/A324964.
-/

namespace OMA.S_oeis_a000139

/-- An integer identity for the factorial quotient. -/
private lemma quotient_identity (n : ℕ) :
    a n + 8 * (3 * n + 1).choose n =
      9 * (3 * n).choose n + (3 * n + 1).choose (n + 1) := by
  let D := (2 * n + 1).factorial * (n + 1).factorial
  let F := (3 * n).factorial
  have hd : 0 < D := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hc := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  rw [show 3 * n - n = 2 * n by omega] at hc
  have hb := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n + 1 by omega)
  rw [show 3 * n + 1 - n = 2 * n + 1 by omega] at hb
  have he := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 3 * n + 1 by omega)
  rw [show 3 * n + 1 - (n + 1) = 2 * n by omega] at he
  have hc' : D * (3 * n).choose n = (2 * n + 1) * (n + 1) * F := by
    dsimp [D, F]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    calc
      _ = (2 * n + 1) * (n + 1) * ((3 * n).choose n * n.factorial * (2 * n).factorial) :=
        by ring
      _ = _ := by rw [hc]
  have hb' : D * (3 * n + 1).choose n = (3 * n + 1) * (n + 1) * F := by
    dsimp [D, F]
    rw [show (n + 1).factorial = (n + 1) * n.factorial by rw [Nat.factorial_succ]]
    calc
      _ = (n + 1) * ((3 * n + 1).choose n * n.factorial * (2 * n + 1).factorial) := by ring
      _ = _ := by rw [hb, Nat.factorial_succ]; ring
  have he' : D * (3 * n + 1).choose (n + 1) = (3 * n + 1) * (2 * n + 1) * F := by
    dsimp [D, F]
    rw [show (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial by rw [Nat.factorial_succ]]
    calc
      _ = (2 * n + 1) * ((3 * n + 1).choose (n + 1) * (n + 1).factorial * (2 * n).factorial) :=
        by ring
      _ = _ := by rw [he, Nat.factorial_succ]; ring
  let T := 9 * (3 * n).choose n + (3 * n + 1).choose (n + 1)
  let U := 8 * (3 * n + 1).choose n
  have hscale : D * T = 2 * F + D * U := by
    dsimp [T, U]
    rw [mul_add, show D * (9 * (3 * n).choose n) = 9 * (D * (3 * n).choose n) by ring,
      show D * (8 * (3 * n + 1).choose n) = 8 * (D * (3 * n + 1).choose n) by ring,
      hc', hb', he']
    ring
  have hut : U ≤ T := by nlinarith
  have hquot : 2 * F / D = T - U := by
    have hprod : 2 * F = D * (T - U) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [hprod, Nat.mul_div_right _ hd]
  change 2 * F / D + U = T
  rw [hquot, Nat.sub_add_cancel hut]

private lemma factorial_parity (n : ℕ) : Odd (a n) ↔ Odd ((3 * n).choose (n + 1)) := by
  have h := quotient_identity n
  rw [Nat.choose_succ_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

private lemma choose_low_bits (x y : ℕ) : ((x + y) % 2).choose (x % 2) =
    if x % 2 = 1 ∧ y % 2 = 1 then 0 else 1 := by
  rw [Nat.add_mod]
  have hx := Nat.mod_lt x (by decide : 0 < 2)
  have hy := Nat.mod_lt y (by decide : 0 < 2)
  generalize x % 2 = u at hx ⊢
  generalize y % 2 = v at hy ⊢
  interval_cases u <;> interval_cases v <;> decide

/-- A binary form of Lucas's theorem in terms of disjoint bit positions. -/
private theorem odd_choose_add_iff (x y : ℕ) :
    Odd ((x + y).choose x) ↔ ∀ i : ℕ, ¬ (x.testBit i ∧ y.testBit i) := by
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    by_cases hx : x = 0
    · subst x
      simp
    have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)
    have hlucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (x + y) x 2 ⟨Nat.prime_two⟩
    simp only [Nat.ModEq] at hlucas
    rw [Nat.odd_iff, hlucas, choose_low_bits]
    by_cases hcollision : x % 2 = 1 ∧ y % 2 = 1
    · have hbits : ¬ ∀ i : ℕ, ¬ (x.testBit i ∧ y.testBit i) := by
        intro h
        exact h 0 ⟨Nat.mod_two_eq_one_iff_testBit_zero.mp hcollision.1,
          Nat.mod_two_eq_one_iff_testBit_zero.mp hcollision.2⟩
      rw [if_pos hcollision, zero_mul]
      exact iff_of_false (by decide) hbits
    · have hadd : (x + y) / 2 = x / 2 + y / 2 := by omega
      rw [if_neg hcollision, one_mul, hadd, ← Nat.odd_iff, ih (x / 2) hlt (y / 2)]
      constructor
      · intro h i
        cases i with
        | zero => simpa only [← Nat.mod_two_eq_one_iff_testBit_zero] using hcollision
        | succ i => simpa only [Nat.testBit_succ] using h i
      · intro h i
        simpa only [Nat.testBit_div_two] using h (i + 1)

private theorem add_one_overlap_double_add_one (q : ℕ) :
    ∃ i : ℕ, (q + 1).testBit i ∧ (2 * q + 1).testBit i := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq : q % 2 = 0
    · exact ⟨0, Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega),
        Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)⟩
    · obtain ⟨i, left_bit, right_bit⟩ := ih (q / 2) (by omega)
      refine ⟨i + 1, ?_, ?_⟩
      · rwa [← Nat.testBit_div_two, show (q + 1) / 2 = q / 2 + 1 by omega]
      · rwa [← Nat.testBit_div_two, show (2 * q + 1) / 2 = 2 * (q / 2) + 1 by omega]

private lemma testBit_bit_tail (b : Bool) (q i : ℕ) :
    (Nat.bit b q).testBit (i + 1) = q.testBit i := by
  rw [← Nat.testBit_div_two, Nat.bit_div_two]

private lemma noOverlap_bit0_shift (q : ℕ) :
    (∀ i : ℕ, ¬ ((Nat.bit true q).testBit i ∧ (Nat.bit false (Nat.bit false q)).testBit i)) ↔
      ∀ i : ℕ, ¬ (q.testBit i ∧ q.testBit (i + 1)) := by
  have right_zero : (Nat.bit false (Nat.bit false q)).testBit 0 = false :=
    Nat.testBit_bit_zero false _
  have right_one : (Nat.bit false (Nat.bit false q)).testBit 1 = false :=
    (testBit_bit_tail false (Nat.bit false q) 0).trans (Nat.testBit_bit_zero false q)
  have left_high (i : ℕ) : (Nat.bit true q).testBit (i + 2) = q.testBit (i + 1) :=
    testBit_bit_tail true q (i + 1)
  have right_high (i : ℕ) : (Nat.bit false (Nat.bit false q)).testBit (i + 2) = q.testBit i :=
    (testBit_bit_tail false (Nat.bit false q) (i + 1)).trans (testBit_bit_tail false q i)
  constructor
  · intro h i hi
    exact h (i + 2) ⟨(left_high i).trans hi.2, (right_high i).trans hi.1⟩
  · intro h i hi
    rcases i with _ | _ | i
    · exact (by decide : false ≠ true) (right_zero.symm.trans hi.2)
    · exact (by decide : false ≠ true) (right_one.symm.trans hi.2)
    · exact h i ⟨(right_high i).symm.trans hi.2, (left_high i).symm.trans hi.1⟩

private lemma noAdjacent_four_mul_add_one (q : ℕ) :
    (∀ i : ℕ, ¬ ((4 * q + 1).testBit i ∧ (4 * q + 1).testBit (i + 1))) ↔
      ∀ i : ℕ, ¬ (q.testBit i ∧ q.testBit (i + 1)) := by
  have hrepr : 4 * q + 1 = Nat.bit true (Nat.bit false q) := by
    simp only [Nat.bit_true_apply, Nat.bit_false_apply]
    omega
  have bit_one : (4 * q + 1).testBit 1 = false := by
    rw [hrepr]
    exact (testBit_bit_tail true (Nat.bit false q) 0).trans (Nat.testBit_bit_zero false q)
  have high (i : ℕ) : (4 * q + 1).testBit (i + 2) = q.testBit i := by
    rw [hrepr]
    exact (testBit_bit_tail true (Nat.bit false q) (i + 1)).trans (testBit_bit_tail false q i)
  constructor
  · intro h i hi
    exact h (i + 2) ⟨(high i).trans hi.1, (high (i + 1)).trans hi.2⟩
  · intro h i hi
    rcases i with _ | _ | i
    · exact (by decide : false ≠ true) (bit_one.symm.trans hi.2)
    · exact (by decide : false ≠ true) (bit_one.symm.trans hi.1)
    · exact h i ⟨(high i).symm.trans hi.1, (high (i + 1)).symm.trans hi.2⟩

private theorem no_carry_iff (n : ℕ) (hn : 0 < n) :
    (∀ i : ℕ, ¬ ((n + 1).testBit i ∧ (2 * n - 1).testBit i)) ↔ IsA022341 n := by
  by_cases heven : n % 2 = 0
  · refine iff_of_false (fun h => h 0 ⟨?_, ?_⟩) (fun h => by have := h.1; omega)
    · exact Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
    · exact Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
  have hodd : n % 2 = 1 := by omega
  let q := n / 4
  by_cases hfour : n % 4 = 1
  · have hnform : n = 4 * q + 1 := by dsimp [q]; omega
    have hleft : (n + 1) / 2 = Nat.bit true q := by
      rw [Nat.bit_true_apply]
      dsimp [q]
      omega
    have hright : (2 * n - 1) / 2 = Nat.bit false (Nat.bit false q) := by
      simp only [Nat.bit_false_apply]
      dsimp [q]
      omega
    have hshift : (∀ i : ℕ, ¬ ((n + 1).testBit i ∧ (2 * n - 1).testBit i)) ↔
        (∀ i : ℕ, ¬ (((n + 1) / 2).testBit i ∧ ((2 * n - 1) / 2).testBit i)) := by
      constructor
      · intro h i
        simpa only [Nat.testBit_div_two] using h (i + 1)
      · intro h i
        cases i with
        | zero =>
          have hzero := Nat.mod_two_eq_zero_iff_testBit_zero.mp (show (n + 1) % 2 = 0 by omega)
          simp [hzero]
        | succ i => simpa only [Nat.testBit_succ] using h i
    refine hshift.trans ?_
    rw [hleft, hright]
    refine (noOverlap_bit0_shift q).trans ?_
    constructor
    · intro h
      refine ⟨hodd, ?_⟩
      rw [hnform]
      exact (noAdjacent_four_mul_add_one q).mpr h
    · intro h
      have hadj := h.2
      rw [hnform] at hadj
      exact (noAdjacent_four_mul_add_one q).mp hadj
  · have hthree : n % 4 = 3 := by omega
    apply iff_of_false
    · intro h
      obtain ⟨i, left_bit, right_bit⟩ := add_one_overlap_double_add_one q
      refine h (i + 2) ⟨?_, ?_⟩
      · rwa [← Nat.testBit_div_two (n + 1) (i + 1),
          ← Nat.testBit_div_two ((n + 1) / 2) i,
          show ((n + 1) / 2) / 2 = q + 1 by dsimp [q]; omega]
      · rwa [← Nat.testBit_div_two (2 * n - 1) (i + 1),
          ← Nat.testBit_div_two ((2 * n - 1) / 2) i,
          show ((2 * n - 1) / 2) / 2 = 2 * q + 1 by dsimp [q]; omega]
    · intro h
      refine h.2 0 ⟨Nat.mod_two_eq_one_iff_testBit_zero.mp hodd, ?_⟩
      rw [← Nat.testBit_div_two n 0]
      exact Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)

/-- A000139 is odd precisely at indices belonging to A022341. -/
theorem solution_lemma : ∀ n : ℕ, Odd (a n) ↔ IsA022341 n := by
  intro n
  rw [factorial_parity]
  by_cases hn : n = 0
  · subst n
    simp [IsA022341]
  · have hsum : n + 1 + (2 * n - 1) = 3 * n := by omega
    have h := odd_choose_add_iff (n + 1) (2 * n - 1)
    rw [hsum] at h
    exact h.trans (no_carry_iff n (Nat.pos_of_ne_zero hn))

end OMA.S_oeis_a000139

theorem OMA.solution : type_of% @OMA.S_oeis_a000139.main := by
  exact OMA.S_oeis_a000139.solution_lemma
