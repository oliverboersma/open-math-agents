import OMAStatements.S_oeis_a309417

namespace OEISA309417Proof

open OMA.S_oeis_a309417

private def dsum (x : ℕ) : ℕ := (Nat.digits 10 x).sum

private def step (x : ℕ) : ℕ := x - dsum x

private lemma dsum_zero : dsum 0 = 0 := by
  simp [dsum]

private lemma dsum_mul_add (q r : ℕ) (hr : r < 10) : dsum (10 * q + r) = dsum q + r := by
  by_cases h0 : 10 * q + r = 0
  · have hq : q = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hq; subst hr0
    simp [dsum]
  · have hpos : 0 < 10 * q + r := Nat.pos_of_ne_zero h0
    have hdig : Nat.digits 10 (10 * q + r) = (10 * q + r) % 10 :: Nat.digits 10 ((10 * q + r) / 10) :=
      Nat.digits_def' (by norm_num) hpos
    have hmod : (10 * q + r) % 10 = r := by omega
    have hdiv : (10 * q + r) / 10 = q := by omega
    simp only [dsum, hdig, hmod, hdiv, List.sum_cons]
    omega

private lemma dsum_pos {x : ℕ} (hx : 0 < x) : 0 < dsum x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hsplit : x = 10 * (x / 10) + x % 10 := by omega
    have hd : dsum x = dsum (x / 10) + x % 10 := by
      conv_lhs => rw [hsplit]
      exact dsum_mul_add (x / 10) (x % 10) (by omega)
    by_cases hm : x % 10 = 0
    · have hqpos : 0 < x / 10 := by omega
      have hqlt : x / 10 < x := by omega
      have := ih (x / 10) hqlt hqpos
      omega
    · omega

private lemma dsum_le (x : ℕ) : dsum x ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x = 0
    · subst hx; simp [dsum_zero]
    · have hsplit : x = 10 * (x / 10) + x % 10 := by omega
      have hd : dsum x = dsum (x / 10) + x % 10 := by
        conv_lhs => rw [hsplit]
        exact dsum_mul_add (x / 10) (x % 10) (by omega)
      have hqlt : x / 10 < x := by omega
      have := ih (x / 10) hqlt
      omega

private lemma dsum_le_nine_mul {n x : ℕ} (hx : x < 10 ^ n) : dsum x ≤ 9 * n := by
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0; simp [dsum_zero]
  | succ n ih =>
    have hsplit : x = 10 * (x / 10) + x % 10 := by omega
    have hd : dsum x = dsum (x / 10) + x % 10 := by
      conv_lhs => rw [hsplit]
      exact dsum_mul_add (x / 10) (x % 10) (by omega)
    have hq : x / 10 < 10 ^ n := by
      rw [pow_succ] at hx
      omega
    have := ih hq
    omega

private lemma dsum_pow_ten (n : ℕ) : dsum (10 ^ n) = 1 := by
  induction n with
  | zero =>
    have h1 : dsum (10 * 0 + 1) = dsum 0 + 1 := dsum_mul_add 0 1 (by norm_num)
    simpa [dsum_zero] using h1
  | succ n ih =>
    have h1 : dsum (10 * 10 ^ n + 0) = dsum (10 ^ n) + 0 := dsum_mul_add (10 ^ n) 0 (by norm_num)
    have hpow : 10 ^ (n + 1) = 10 * 10 ^ n + 0 := by ring
    rw [hpow, h1, ih]

private lemma step_lt {x : ℕ} (hx : 0 < x) : step x < x := by
  have h1 := dsum_pos hx
  have h2 := dsum_le x
  unfold step
  omega

private lemma step_add_dsum (x : ℕ) : step x + dsum x = x := by
  have h := dsum_le x
  unfold step
  omega

private lemma countSteps_succ_succ (fuel x : ℕ) :
    countSteps (fuel + 1) (x + 1) = 1 + countSteps fuel (step (x + 1)) := rfl

private lemma orbit_countSteps_and_pos :
    ∀ fuel x : ℕ, x ≤ fuel →
      step^[countSteps fuel x] x = 0 ∧
      ∀ i < countSteps fuel x, 0 < step^[i] x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [countSteps]
  | succ fuel ih =>
    intro x hx
    cases x with
    | zero =>
      simp [countSteps]
    | succ y =>
      have hstep_le : step (y + 1) ≤ fuel := by
        have := step_lt (show 0 < y + 1 by omega)
        omega
      obtain ⟨hzero, hpos⟩ := ih (step (y + 1)) hstep_le
      rw [countSteps_succ_succ]
      constructor
      · rw [add_comm, Function.iterate_succ_apply, hzero]
      · intro i hi
        cases i with
        | zero =>
          simp
        | succ j =>
          rw [Function.iterate_succ_apply]
          exact hpos j (by omega)

private lemma orbit_strictAnti {fuel x : ℕ} (hxf : x ≤ fuel) :
    ∀ {i j : ℕ}, i < j → j ≤ countSteps fuel x → step^[j] x < step^[i] x := by
  intro i j hij hj
  have hpos := (orbit_countSteps_and_pos fuel x hxf).2
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep : step^[j + 1] x < step^[j] x := by
      rw [Function.iterate_succ_apply']
      exact step_lt (hpos j (by omega))
    by_cases hEq : i = j
    · subst hEq; exact hstep
    · exact lt_trans hstep (ih (by omega) (by omega))

private lemma orbit_sum_dsum (x k : ℕ) :
    step^[k] x + ∑ i ∈ Finset.range k, dsum (step^[i] x) = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have h := step_add_dsum (step^[k] x)
    omega

private lemma term_pos (n : ℕ) : 0 < term n := by
  have h0 : step^[term n] (10 ^ n) = 0 :=
    (orbit_countSteps_and_pos (10 ^ n) (10 ^ n) le_rfl).1
  by_contra h
  have hzero : term n = 0 := by omega
  rw [hzero] at h0
  simp at h0

private noncomputable def orbitSet (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (term n)).image (fun i => step^[i] (10 ^ n))

private lemma orbitSet_subset (n : ℕ) : orbitSet n ⊆ Finset.range (10 ^ n) := by
  intro y hy
  simp only [orbitSet, Finset.mem_image, Finset.mem_Ico] at hy
  obtain ⟨i, ⟨hi1, him⟩, rfl⟩ := hy
  rw [Finset.mem_range]
  have hlt := orbit_strictAnti (fuel := 10 ^ n) (x := 10 ^ n) le_rfl (i := 0) (j := i) (by omega) (le_of_lt him)
  simpa using hlt

private lemma orbit_injOn (n : ℕ) :
    Set.InjOn (fun i => step^[i] (10 ^ n)) (Finset.Ico 1 (term n) : Set ℕ) := by
  intro i hi j hj hEq
  dsimp only at hEq
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hlt := orbit_strictAnti (fuel := 10 ^ n) (x := 10 ^ n) le_rfl hij (le_of_lt hj.2)
    omega
  · rfl
  · have hlt := orbit_strictAnti (fuel := 10 ^ n) (x := 10 ^ n) le_rfl hji (le_of_lt hi.2)
    omega

private lemma orbitSet_card (n : ℕ) : (orbitSet n).card + 1 = term n := by
  have hcard : (orbitSet n).card = (Finset.Ico 1 (term n)).card :=
    Finset.card_image_of_injOn (orbit_injOn n)
  rw [hcard, Nat.card_Ico]
  have hp := term_pos n
  omega

private lemma orbitSet_sum_dsum (n : ℕ) :
    (∑ y ∈ orbitSet n, dsum y) + 1 = 10 ^ n := by
  have hsum_img : ∑ y ∈ orbitSet n, dsum y = ∑ i ∈ Finset.Ico 1 (term n), dsum (step^[i] (10 ^ n)) :=
    Finset.sum_image (by
      intro a ha b hb hEq
      exact orbit_injOn n ha hb hEq)
  have htele := orbit_sum_dsum (10 ^ n) (term n)
  have h0 : step^[term n] (10 ^ n) = 0 :=
    (orbit_countSteps_and_pos (10 ^ n) (10 ^ n) le_rfl).1
  rw [h0, zero_add] at htele
  have hrange : Finset.range (term n) = insert 0 (Finset.Ico 1 (term n)) := by
    ext i
    have hp := term_pos n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Ico 1 (term n) := by simp
  rw [hrange, Finset.sum_insert hnotmem] at htele
  simp only [Function.iterate_zero, id_eq, dsum_pow_ten] at htele
  rw [hsum_img]
  omega

private lemma sum_range_mul_ten {α : Type*} [AddCommMonoid α] (k : ℕ) (f : ℕ → α) :
    ∑ x ∈ Finset.range (k * 10), f x =
      ∑ q ∈ Finset.range k, ∑ r ∈ Finset.range 10, f (10 * q + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_comm]

private lemma sum_range_pow_succ {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ∑ x ∈ Finset.range (10 ^ (n + 1)), f x =
      ∑ q ∈ Finset.range (10 ^ n), ∑ r ∈ Finset.range 10, f (10 * q + r) := by
  rw [pow_succ]
  exact sum_range_mul_ten (10 ^ n) f

private noncomputable def M2 (n : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (10 ^ n), ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 2

private noncomputable def M4 (n : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (10 ^ n), ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 4

private lemma sum_ten_sq (A : ℝ) :
    ∑ r ∈ Finset.range 10, (A + ((r : ℝ) - 9 / 2)) ^ 2 = 10 * A ^ 2 + 165 / 2 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  push_cast
  ring

private lemma sum_ten_pow4 (A : ℝ) :
    ∑ r ∈ Finset.range 10, (A + ((r : ℝ) - 9 / 2)) ^ 4 =
      10 * A ^ 4 + 495 * A ^ 2 + 9669 / 8 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  push_cast
  ring

private lemma M2_eq (n : ℕ) : M2 n = (33 / 4 : ℝ) * (n : ℝ) * (10 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp [M2, dsum_zero]
  | succ n ih =>
    unfold M2
    rw [sum_range_pow_succ]
    have hinner : ∀ q ∈ Finset.range (10 ^ n),
        ∑ r ∈ Finset.range 10, ((dsum (10 * q + r) : ℝ) - (9 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 =
          10 * ((dsum q : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 2 + 165 / 2 := by
      intro q _
      have hcongr : ∑ r ∈ Finset.range 10,
            ((dsum (10 * q + r) : ℝ) - (9 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 =
          ∑ r ∈ Finset.range 10,
            (((dsum q : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) + ((r : ℝ) - 9 / 2)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        rw [dsum_mul_add q r hr]
        push_cast
        ring
      rw [hcongr, sum_ten_sq]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum]
    change 10 * M2 n + ∑ _q ∈ Finset.range (10 ^ n), (165 / 2 : ℝ) = _
    rw [ih, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

private lemma M4_le (n : ℕ) : M4 n ≤ 300 * (n : ℝ) ^ 2 * (10 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp [M4, dsum_zero]
  | succ n ih =>
    unfold M4
    rw [sum_range_pow_succ]
    have hinner : ∀ q ∈ Finset.range (10 ^ n),
        ∑ r ∈ Finset.range 10, ((dsum (10 * q + r) : ℝ) - (9 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 4 =
          10 * ((dsum q : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 4 +
          495 * ((dsum q : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 2 + 9669 / 8 := by
      intro q _
      have hcongr : ∑ r ∈ Finset.range 10,
            ((dsum (10 * q + r) : ℝ) - (9 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 4 =
          ∑ r ∈ Finset.range 10,
            (((dsum q : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) + ((r : ℝ) - 9 / 2)) ^ 4 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        rw [dsum_mul_add q r hr]
        push_cast
        ring
      rw [hcongr, sum_ten_pow4]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    change 10 * M4 n + 495 * M2 n + ∑ _q ∈ Finset.range (10 ^ n), (9669 / 8 : ℝ) ≤ _
    rw [M2_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h10 : (0 : ℝ) ≤ (10 : ℝ) ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hstep : 10 * M4 n ≤ 10 * (300 * (n : ℝ) ^ 2 * (10 : ℝ) ^ n) := by linarith
    have hpow : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
    have hpoly : 300 * ((n : ℝ) + 1) ^ 2 * ((10 : ℝ) ^ n * 10) =
        10 * (300 * (n : ℝ) ^ 2 * (10 : ℝ) ^ n) + 6000 * ((n : ℝ) * (10 : ℝ) ^ n) +
        3000 * (10 : ℝ) ^ n := by ring
    have hprod : 0 ≤ (n : ℝ) * (10 : ℝ) ^ n := mul_nonneg hn h10
    have hmid : 495 * ((33 / 4 : ℝ) * (n : ℝ) * (10 : ℝ) ^ n) =
        (16335 / 4 : ℝ) * ((n : ℝ) * (10 : ℝ) ^ n) := by ring
    push_cast
    rw [hpow, hpoly, hmid]
    linarith

private lemma sq_le_ten_pow (n : ℕ) : n ^ 2 ≤ 10 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    cases n with
    | zero => norm_num
    | succ m =>
      have h1 : (m + 2) ^ 2 ≤ 10 * (m + 1) ^ 2 := by
        calc
          (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
          _ ≤ 10 * m ^ 2 + 20 * m + 10 := by omega
          _ = 10 * (m + 1) ^ 2 := by ring
      calc
        (m + 2) ^ 2 ≤ 10 * (m + 1) ^ 2 := h1
        _ ≤ 10 * 10 ^ (m + 1) := by exact Nat.mul_le_mul_left 10 ih
        _ = 10 ^ (m + 2) := by ring

private lemma bad_card_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    let B := (Finset.range (10 ^ n)).filter
      (fun x => ε * (n : ℝ) < |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)|)
    (B.card : ℝ) ≤ (300 / ε ^ 4) * ((10 : ℝ) ^ n / (n : ℝ) ^ 2) := by
  classical
  intro B
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hmarkov : (B.card : ℝ) * (ε * (n : ℝ)) ^ 4 ≤ M4 n := by
    calc
      (B.card : ℝ) * (ε * (n : ℝ)) ^ 4
          = ∑ _x ∈ B, (ε * (n : ℝ)) ^ 4 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ B, ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 4 := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : ε * (n : ℝ) < |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| :=
            (Finset.mem_filter.mp hx).2
          have hpow : (ε * (n : ℝ)) ^ 4 ≤ |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ^ 4 :=
            pow_le_pow_left₀ (by positivity) (le_of_lt hx') 4
          have habs : |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ^ 4 =
              ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 4 := by
            have hsq : |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ^ 2 =
                ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 2 := sq_abs _
            calc
              |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ^ 4
                  = (|(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ^ 2) ^ 2 := by ring
              _ = (((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 2) ^ 2 := by rw [hsq]
              _ = ((dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)) ^ 4 := by ring
          linarith
      _ ≤ M4 n := by
          unfold M4
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro x _ _
          positivity
  have hM4 := M4_le n
  have hbound : (B.card : ℝ) * (ε ^ 4 * (n : ℝ) ^ 4) ≤ 300 * (n : ℝ) ^ 2 * (10 : ℝ) ^ n := by
    have : (ε * (n : ℝ)) ^ 4 = ε ^ 4 * (n : ℝ) ^ 4 := by ring
    linarith
  have hden : 0 < ε ^ 4 * (n : ℝ) ^ 4 := by positivity
  rw [show (300 / ε ^ 4) * ((10 : ℝ) ^ n / (n : ℝ) ^ 2) =
      (300 * (n : ℝ) ^ 2 * (10 : ℝ) ^ n) / (ε ^ 4 * (n : ℝ) ^ 4) by field_simp]
  exact (le_div_iff₀ hden).mpr hbound

private lemma ratio_bounds {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 9 / 2) {n : ℕ} (hn : 1 ≤ n) :
    let K := 300 / ε ^ 4
    (1 - (1 + 9 * K) / (n : ℝ)) / (9 / 2 + ε) ≤
      ((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n ∧
    ((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n ≤
      1 / (9 / 2 - ε) + (1 + K) / (n : ℝ) := by
  classical
  intro K
  set V := orbitSet n
  set B := (Finset.range (10 ^ n)).filter
    (fun x => ε * (n : ℝ) < |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)|)
  have hB : (B.card : ℝ) ≤ K * ((10 : ℝ) ^ n / (n : ℝ) ^ 2) := bad_card_le hε hn
  have hVsub : V ⊆ Finset.range (10 ^ n) := orbitSet_subset n
  have hVcard : (V.card : ℝ) + 1 = (term n : ℝ) := by exact_mod_cast orbitSet_card n
  have hVsum : (∑ x ∈ V, (dsum x : ℝ)) + 1 = (10 : ℝ) ^ n := by
    have := orbitSet_sum_dsum n
    exact_mod_cast this
  have hdisj : Disjoint (V \ B) (V ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mp hx2).2
  have hunion : (V \ B) ∪ (V ∩ B) = V := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit_sum :
      (∑ x ∈ V \ B, (dsum x : ℝ)) + (∑ x ∈ V ∩ B, (dsum x : ℝ)) = ∑ x ∈ V, (dsum x : ℝ) := by
    rw [← Finset.sum_union hdisj, hunion]
  have hsplit_card : ((V \ B).card : ℝ) + ((V ∩ B).card : ℝ) = (V.card : ℝ) := by
    have := Finset.card_sdiff_add_card_inter V B
    exact_mod_cast this
  have hVB_le_B : ((V ∩ B).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hVsB_le_m : ((V \ B).card : ℝ) ≤ (term n : ℝ) := by
    have h1 : (V \ B).card ≤ V.card := Finset.card_le_card Finset.sdiff_subset
    have h1' : ((V \ B).card : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast h1
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have h10_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hsq : (n : ℝ) ^ 2 ≤ (10 : ℝ) ^ n := by exact_mod_cast sq_le_ten_pow n
  have hn_le_10 : (n : ℝ) ≤ (10 : ℝ) ^ n := by
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
    linarith
  have hnB_div : (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n ≤ K / (n : ℝ) := by
    rw [div_le_iff₀ h10_pos]
    have hmul := mul_le_mul_of_nonneg_left hB (le_of_lt hn_pos)
    have hEq : (n : ℝ) * (K * ((10 : ℝ) ^ n / (n : ℝ) ^ 2)) = K / (n : ℝ) * (10 : ℝ) ^ n := by
      field_simp
    linarith
  have hn_div : (n : ℝ) / (10 : ℝ) ^ n ≤ 1 / (n : ℝ) := by
    rw [div_le_div_iff₀ h10_pos hn_pos]
    nlinarith
  have h1_div : 1 / (10 : ℝ) ^ n ≤ 1 / (n : ℝ) := by
    rw [div_le_div_iff₀ h10_pos hn_pos]
    linarith
  have hgood_lo : ∀ x ∈ V \ B, (9 / 2 - ε) * (n : ℝ) ≤ (dsum x : ℝ) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxR : x ∈ Finset.range (10 ^ n) := hVsub hx.1
    have hnotB : ¬ (ε * (n : ℝ) < |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)|) := by
      intro hc
      exact hx.2 (Finset.mem_filter.mpr ⟨hxR, hc⟩)
    have habs : |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ≤ ε * (n : ℝ) := not_lt.mp hnotB
    have := (abs_le.mp habs).1
    linarith
  have hgood_hi : ∀ x ∈ V \ B, (dsum x : ℝ) ≤ (9 / 2 + ε) * (n : ℝ) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxR : x ∈ Finset.range (10 ^ n) := hVsub hx.1
    have hnotB : ¬ (ε * (n : ℝ) < |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)|) := by
      intro hc
      exact hx.2 (Finset.mem_filter.mpr ⟨hxR, hc⟩)
    have habs : |(dsum x : ℝ) - (9 / 2 : ℝ) * (n : ℝ)| ≤ ε * (n : ℝ) := not_lt.mp hnotB
    have := (abs_le.mp habs).2
    linarith
  have hbad_hi : ∀ x ∈ V ∩ B, (dsum x : ℝ) ≤ 9 * (n : ℝ) := by
    intro x hx
    have hxR : x < 10 ^ n := Finset.mem_range.mp (hVsub (Finset.mem_inter.mp hx).1)
    exact_mod_cast dsum_le_nine_mul hxR
  constructor
  · -- Lower bound
    have hsum_good : ∑ x ∈ V \ B, (dsum x : ℝ) ≤ ((V \ B).card : ℝ) * ((9 / 2 + ε) * (n : ℝ)) := by
      calc
        ∑ x ∈ V \ B, (dsum x : ℝ) ≤ ∑ _x ∈ V \ B, ((9 / 2 + ε) * (n : ℝ)) :=
          Finset.sum_le_sum hgood_hi
        _ = ((V \ B).card : ℝ) * ((9 / 2 + ε) * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hsum_bad : ∑ x ∈ V ∩ B, (dsum x : ℝ) ≤ ((V ∩ B).card : ℝ) * (9 * (n : ℝ)) := by
      calc
        ∑ x ∈ V ∩ B, (dsum x : ℝ) ≤ ∑ _x ∈ V ∩ B, (9 * (n : ℝ)) :=
          Finset.sum_le_sum hbad_hi
        _ = ((V ∩ B).card : ℝ) * (9 * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have h1 : (10 : ℝ) ^ n - 1 ≤
        (term n : ℝ) * ((9 / 2 + ε) * (n : ℝ)) + (B.card : ℝ) * (9 * (n : ℝ)) := by
      have hpa : 0 ≤ (9 / 2 + ε) * (n : ℝ) := by positivity
      have h9n : 0 ≤ 9 * (n : ℝ) := by positivity
      have ha : ((V \ B).card : ℝ) * ((9 / 2 + ε) * (n : ℝ)) ≤ (term n : ℝ) * ((9 / 2 + ε) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hVsB_le_m hpa
      have hb : ((V ∩ B).card : ℝ) * (9 * (n : ℝ)) ≤ (B.card : ℝ) * (9 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hVB_le_B h9n
      linarith
    have h2 : 1 - 1 / (10 : ℝ) ^ n ≤
        (((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n) * (9 / 2 + ε) +
        9 * ((n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by
      have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt h10_pos)
      have hL : ((10 : ℝ) ^ n - 1) / (10 : ℝ) ^ n = 1 - 1 / (10 : ℝ) ^ n := by field_simp
      have hR : ((term n : ℝ) * ((9 / 2 + ε) * (n : ℝ)) + (B.card : ℝ) * (9 * (n : ℝ))) / (10 : ℝ) ^ n =
          (((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n) * (9 / 2 + ε) +
          9 * ((n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by ring
      linarith
    have h3 : 1 - (1 + 9 * K) / (n : ℝ) ≤
        (((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n) * (9 / 2 + ε) := by
      have hEq : (1 + 9 * K) / (n : ℝ) = 1 / (n : ℝ) + 9 * (K / (n : ℝ)) := by ring
      linarith
    exact (div_le_iff₀ (by linarith : (0 : ℝ) < 9 / 2 + ε)).mpr h3
  · -- Upper bound
    have hsum_good : ((V \ B).card : ℝ) * ((9 / 2 - ε) * (n : ℝ)) ≤ ∑ x ∈ V \ B, (dsum x : ℝ) := by
      calc
        ((V \ B).card : ℝ) * ((9 / 2 - ε) * (n : ℝ)) = ∑ _x ∈ V \ B, ((9 / 2 - ε) * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ V \ B, (dsum x : ℝ) := Finset.sum_le_sum hgood_lo
    have hbad_nonneg : 0 ≤ ∑ x ∈ V ∩ B, (dsum x : ℝ) :=
      Finset.sum_nonneg (fun x _ => Nat.cast_nonneg _)
    have hcard_lo : (term n : ℝ) - 1 - (B.card : ℝ) ≤ ((V \ B).card : ℝ) := by linarith
    have hc_pos : 0 < (9 / 2 - ε) * (n : ℝ) := by nlinarith
    have h1 : ((term n : ℝ) - 1 - (B.card : ℝ)) * ((9 / 2 - ε) * (n : ℝ)) ≤ (10 : ℝ) ^ n := by
      have hm := mul_le_mul_of_nonneg_right hcard_lo (le_of_lt hc_pos)
      linarith
    have h2 : (((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n) * (9 / 2 - ε) ≤
        1 + (9 / 2 - ε) * ((n : ℝ) / (10 : ℝ) ^ n + (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by
      have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt h10_pos)
      have hL : ((term n : ℝ) - 1 - (B.card : ℝ)) * ((9 / 2 - ε) * (n : ℝ)) / (10 : ℝ) ^ n =
          (((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n) * (9 / 2 - ε) -
          (9 / 2 - ε) * ((n : ℝ) / (10 : ℝ) ^ n + (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by ring
      have hR : (10 : ℝ) ^ n / (10 : ℝ) ^ n = 1 := div_self (ne_of_gt h10_pos)
      linarith
    have h3 : ((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n ≤
        1 / (9 / 2 - ε) + ((n : ℝ) / (10 : ℝ) ^ n + (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by
      have hpos : (0 : ℝ) < 9 / 2 - ε := by linarith
      rw [← mul_le_mul_iff_left₀ hpos]
      have hEq : (9 / 2 - ε) *
          (1 / (9 / 2 - ε) + ((n : ℝ) / (10 : ℝ) ^ n + (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n)) =
          1 + (9 / 2 - ε) * ((n : ℝ) / (10 : ℝ) ^ n + (n : ℝ) * (B.card : ℝ) / (10 : ℝ) ^ n) := by
        rw [mul_add, mul_one_div_cancel (ne_of_gt hpos)]
      linarith
    have hEq2 : (1 + K) / (n : ℝ) = 1 / (n : ℝ) + K / (n : ℝ) := by ring
    linarith

private lemma tendsto_scaled_term :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n)
      Filter.atTop (nhds (2 / 9 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := min 1 (δ / 4)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε_le1 : ε ≤ 1 := min_le_left _ _
  have hε_leδ : ε ≤ δ / 4 := min_le_right _ _
  have hε2 : ε < 9 / 2 := by linarith
  set K : ℝ := 300 / ε ^ 4
  have hK_pos : 0 < K := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * (1 + 9 * K) / δ)
  refine ⟨max 1 N0, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : N0 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn_gt : 4 * (1 + 9 * K) / δ < (n : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hn0)
  have hsmall : (1 + 9 * K) / (n : ℝ) < δ / 4 := by
    rw [div_lt_iff₀ hn_pos]
    have hmul : 4 * (1 + 9 * K) < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn_gt
    have hEq : δ / 4 * (n : ℝ) = ((n : ℝ) * δ) / 4 := by ring
    linarith
  have hsmall2 : (1 + K) / (n : ℝ) < δ / 4 := by
    have hle : (1 + K) / (n : ℝ) ≤ (1 + 9 * K) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
      linarith
    linarith
  obtain ⟨hlo, hhi⟩ := ratio_bounds hε_pos hε2 hn1
  have hhi_eps : 1 / (9 / 2 - ε) ≤ 2 / 9 + ε := by
    have hpos : (0 : ℝ) < 9 / 2 - ε := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith
  have hlo_eps : 2 / 9 - ε ≤ 1 / (9 / 2 + ε) := by
    have hpos : (0 : ℝ) < 9 / 2 + ε := by linarith
    rw [le_div_iff₀ hpos]
    nlinarith
  have hlo_err : (1 + 9 * K) / (n : ℝ) / (9 / 2 + ε) ≤ (1 + 9 * K) / (n : ℝ) := by
    have hnum : 0 ≤ (1 + 9 * K) / (n : ℝ) := by positivity
    exact div_le_self hnum (by linarith)
  have hlo_split : (1 - (1 + 9 * K) / (n : ℝ)) / (9 / 2 + ε) =
      1 / (9 / 2 + ε) - (1 + 9 * K) / (n : ℝ) / (9 / 2 + ε) := by ring
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private lemma tendsto_ratio_aux :
    Filter.Tendsto (fun n : ℕ => 10 * (n : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 10) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden : Filter.Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hq : Filter.Tendsto (fun n : ℕ => (10 : ℝ) / (1 + (1 : ℝ) / (n : ℝ))) Filter.atTop (nhds 10) := by
    have h := (tendsto_const_nhds (x := (10 : ℝ))).div hden (by norm_num)
    rw [div_one] at h
    exact h.congr (fun n => Pi.div_apply _ _ n)
  refine hq.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem main_proof :
    Filter.Tendsto (fun n : ℕ => (term (n + 1) : ℝ) / (term n : ℝ))
      Filter.atTop (nhds 10) := by
  let a : ℕ → ℝ := fun n => ((n : ℝ) * (term n : ℝ)) / (10 : ℝ) ^ n
  have ha : Filter.Tendsto a Filter.atTop (nhds (2 / 9 : ℝ)) := tendsto_scaled_term
  have ha_succ : Filter.Tendsto (fun n => a (n + 1)) Filter.atTop (nhds (2 / 9 : ℝ)) :=
    ha.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiv : Filter.Tendsto (fun n => a (n + 1) / a n) Filter.atTop (nhds 1) := by
    have h := ha_succ.div ha (by norm_num)
    rw [div_self (by norm_num : (2 / 9 : ℝ) ≠ 0)] at h
    exact h.congr (fun n => Pi.div_apply _ _ n)
  have hprod : Filter.Tendsto
      (fun n => (a (n + 1) / a n) * (10 * (n : ℝ) / ((n : ℝ) + 1))) Filter.atTop (nhds 10) := by
    simpa using hdiv.mul tendsto_ratio_aux
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have ht0 : (term n : ℝ) ≠ 0 := by
    have := term_pos n
    positivity
  have h10 : (10 : ℝ) ^ n ≠ 0 := by positivity
  simp only [a]
  push_cast [pow_succ]
  field_simp

end OEISA309417Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a309417.main :=
  OEISA309417Proof.main_proof
