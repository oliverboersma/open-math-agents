import OMAReductions.R_Erdos294_erdos_294_R1_H1_R1_H2_R1

/-! Reciprocal mass bounds on smooth integers in dyadic intervals. -/

open Finset Filter

namespace Erdos294StepH1

private lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ s.biUnion t, f b) ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have hunion :
        (∑ b ∈ t a ∪ s.biUnion t, f b) ≤ (∑ b ∈ t a, f b) + ∑ b ∈ s.biUnion t, f b := by
      have h := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := sum_nonneg fun b _ => hf b
      linarith
    linarith

private lemma sum_image_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ s.image g, f b) ≤ ∑ a ∈ s, f (g a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [image_insert, sum_insert ha]
    by_cases hmem : g a ∈ s.image g
    · rw [insert_eq_of_mem hmem]
      linarith [hf (g a)]
    · rw [sum_insert hmem]
      linarith

private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

private lemma eighteen_lt_exp_three : (18 : ℝ) < Real.exp 3 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
  nlinarith

private lemma four_lt_exp_two : (4 : ℝ) < Real.exp 2 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos (1 / 2)
  have hexp : Real.exp (1 / 2) < 2 := by nlinarith
  have hlog := Real.log_lt_log hpos hexp
  rwa [Real.log_exp] at hlog

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) four_lt_exp_two.le
  rwa [Real.log_exp] at h

private lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 4 * x := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hexp : Real.log x / 2 + 1 ≤ Real.exp (Real.log x / 2) :=
    Real.add_one_le_exp (Real.log x / 2)
  have hsq : Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2) = x := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by linarith)]
  have hpos : 0 < Real.exp (Real.log x / 2) := Real.exp_pos (Real.log x / 2)
  nlinarith

private lemma interval_eq_Ico {N : ℕ} (hN : 256 ≤ N) :
    ((Icc 1 N).filter fun n => N ≤ 16 * n) = Ico ((N + 15) / 16) (N + 1) := by
  ext n
  simp only [mem_filter, mem_Icc, mem_Ico]
  omega

private lemma sum_Ico_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Ico a b, (f (k + 1) - f k)) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ico_succ_top hmn, ih]
    ring

private lemma harmonic_bounds {N : ℕ} (hN : 256 ≤ N) :
    (2 : ℝ) ≤ (∑ n ∈ (Icc 1 N).filter (fun n => N ≤ 16 * n), 1 / (n : ℝ)) ∧
      (∑ n ∈ (Icc 1 N).filter (fun n => N ≤ 16 * n), 1 / (n : ℝ)) ≤ 3 := by
  rw [interval_eq_Ico hN]
  set m := (N + 15) / 16
  have hm4 : 16 ≤ m := by omega
  have hmN : m ≤ N + 1 := by omega
  constructor
  · have hstep : ∀ k ∈ Ico m (N + 1),
        Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have := (mem_Ico.mp hk).1
        omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hdivpos : 0 < ((k : ℝ) + 1) / (k : ℝ) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hdivpos
      rw [Real.log_div (by positivity) hkpos.ne'] at hlog
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hrhs : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
        field_simp [hkpos.ne']
        ring
      rw [hcast]
      linarith
    have htel := sum_Ico_telescope (fun k : ℕ => Real.log (k : ℝ)) hmN
    have hsum := sum_le_sum hstep
    rw [htel] at hsum
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hratio : (8 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      have hnat : 8 * m ≤ N + 1 := by omega
      exact_mod_cast hnat
    have hlog8 : Real.log 8 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      rw [← Real.log_div (by positivity) hmpos.ne']
      exact Real.log_le_log (by norm_num) hratio
    have h2log8 : (2 : ℝ) ≤ Real.log 8 := by
      have h := Real.log_le_log (Real.exp_pos 2) exp_two_lt_eight.le
      rwa [Real.log_exp] at h
    linarith
  · let g : ℕ → ℝ := fun j => Real.log ((j - 1 : ℕ) : ℝ)
    have hstep : ∀ k ∈ Ico m (N + 1), 1 / (k : ℝ) ≤ g (k + 1) - g k := by
      intro k hk
      have hk2 : 2 ≤ k := by
        have := (mem_Ico.mp hk).1
        omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < k - 1 by omega)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk1pos hkpos)
      rw [Real.log_div hk1pos.ne' hkpos.ne'] at hlog
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (k - 1) + 1 = k := by omega
        have h' : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by exact_mod_cast this
        linarith
      have hrhs : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
        rw [hcast]
        field_simp [hkpos.ne']
        ring
      have hg : g (k + 1) - g k = Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
        dsimp [g]
      rw [hg]
      linarith
    have htel := sum_Ico_telescope g hmN
    have hsum := sum_le_sum hstep
    rw [htel] at hsum
    have hgm : g (N + 1) - g m = Real.log (N : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
      dsimp [g]
    rw [hgm] at hsum
    have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    have hratio : (N : ℝ) / ((m - 1 : ℕ) : ℝ) ≤ 18 := by
      rw [div_le_iff₀ hm1pos]
      have hnat : N ≤ 18 * (m - 1) := by omega
      exact_mod_cast hnat
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog18 : Real.log (N : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) ≤ Real.log 18 := by
      rw [← Real.log_div hNpos.ne' hm1pos.ne']
      exact Real.log_le_log (div_pos hNpos hm1pos) hratio
    have hlog18_le : Real.log 18 ≤ 3 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 18) eighteen_lt_exp_three.le
      rwa [Real.log_exp] at h
    linarith

private lemma divisor_mass_le {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    (∑ n ∈ ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => d ∣ n), 1 / (n : ℝ)) ≤
      16 / (d : ℝ) := by
  set M := ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => d ∣ n)
  have hcard : M.card ≤ N / d := by
    have hinj : M.card ≤ (Icc 1 (N / d)).card := by
      refine card_le_card_of_injOn (fun n => n / d) ?_ ?_
      · intro n hn
        obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
        obtain ⟨hnIcc, _⟩ := mem_filter.mp hnI
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnIcc
        have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
        exact mem_Icc.mpr ⟨hq1, Nat.div_le_div_right hnN⟩
      · intro a ha b hb hab
        obtain ⟨_, hda⟩ := mem_filter.mp ha
        obtain ⟨_, hdb⟩ := mem_filter.mp hb
        have ha' : d * (a / d) = a := Nat.mul_div_cancel' hda
        have hb' : d * (b / d) = b := Nat.mul_div_cancel' hdb
        dsimp only at hab
        rw [← ha', hab, hb']
    simpa using hinj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hterm : ∀ n ∈ M, 1 / (n : ℝ) ≤ 16 / (N : ℝ) := by
    intro n hn
    obtain ⟨hnI, _⟩ := mem_filter.mp hn
    obtain ⟨hnIcc, hn16⟩ := mem_filter.mp hnI
    obtain ⟨hn1, _⟩ := mem_Icc.mp hnIcc
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn16' : (N : ℝ) ≤ 16 * (n : ℝ) := by exact_mod_cast hn16
    rw [div_le_div_iff₀ hnpos hNpos]
    linarith
  have hsum : (∑ n ∈ M, 1 / (n : ℝ)) ≤ (M.card : ℝ) * (16 / (N : ℝ)) := by
    calc
      (∑ n ∈ M, 1 / (n : ℝ)) ≤ ∑ _n ∈ M, 16 / (N : ℝ) := sum_le_sum hterm
      _ = (M.card : ℝ) * (16 / (N : ℝ)) := by simp
  have hdiv_le : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N d
  have hcard_le : (M.card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    have h1 : (M.card : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := (le_div_iff₀ hdpos).mpr hdiv_le
    exact h1.trans h2
  calc
    (∑ n ∈ M, 1 / (n : ℝ)) ≤ (M.card : ℝ) * (16 / (N : ℝ)) := hsum
    _ ≤ ((N : ℝ) / (d : ℝ)) * (16 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard_le (by positivity)
    _ = 16 / (d : ℝ) := by
      field_simp [hNpos.ne', hdpos.ne']

private lemma large_squares_sum_le {y : ℕ} (hy : 16384 ≤ y) :
    (∑ m ∈ Icc (Nat.sqrt y + 1) y, 16 / ((m ^ 2 : ℕ) : ℝ)) ≤ 1 / 8 := by
  set z := Nat.sqrt y
  have hz128 : 128 ≤ z := Nat.le_sqrt.mpr (by omega)
  have hz_sq : z * z ≤ y := Nat.sqrt_le y
  have hzy : z + 1 ≤ y + 1 := by nlinarith
  have hIco : Icc (z + 1) y = Ico (z + 1) (y + 1) := by
    ext m
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hIco]
  let h : ℕ → ℝ := fun k => -(1 / ((k - 1 : ℕ) : ℝ))
  have hstep : ∀ m ∈ Ico (z + 1) (y + 1), 16 / ((m ^ 2 : ℕ) : ℝ) ≤ 16 * (h (m + 1) - h m) := by
    intro m hm
    have hm2 : 2 ≤ m := by
      have := (mem_Ico.mp hm).1
      omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (m - 1) + 1 = m := by omega
      have h' : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by exact_mod_cast this
      linarith
    have hdiff : h (m + 1) - h m = 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
      dsimp [h]
      ring
    rw [hdiff, Nat.cast_pow]
    have hfrac : 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
      rw [hmcast]
      field_simp [hmpos.ne', (show (m : ℝ) - 1 ≠ 0 by linarith)]
      ring
    rw [hfrac]
    have hle : ((m - 1 : ℕ) : ℝ) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rw [hmcast]
      nlinarith
    have hdiv : 1 / ((m : ℝ) ^ 2) ≤ 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hm1pos hmpos) hle
    have h16eq : 16 / ((m : ℝ) ^ 2) = 16 * (1 / ((m : ℝ) ^ 2)) := by ring
    linarith
  have hsum := sum_le_sum hstep
  have hsub_eq : (∑ i ∈ Ico (z + 1) (y + 1), (h (i + 1) - h i)) = h (y + 1) - h (z + 1) :=
    sum_Ico_telescope h hzy
  rw [← mul_sum, hsub_eq] at hsum
  have htel : h (y + 1) - h (z + 1) = 1 / (z : ℝ) - 1 / (y : ℝ) := by
    dsimp [h]
    ring
  rw [htel] at hsum
  have hy_nonneg : 0 ≤ 1 / (y : ℝ) := by positivity
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hz128' : (128 : ℝ) ≤ z := by exact_mod_cast hz128
  have h16z : 16 / (z : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ hzpos]
    linarith
  have h16dist : 16 * (1 / (z : ℝ) - 1 / (y : ℝ)) = 16 / (z : ℝ) - 16 * (1 / (y : ℝ)) := by ring
  linarith

private lemma small_powers_sum_le {y : ℕ} (hy : 16384 ≤ y) :
    (∑ m ∈ Icc 2 (Nat.sqrt y), 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤ 1 / 8 := by
  set z := Nat.sqrt y
  have hz128 : 128 ≤ z := Nat.le_sqrt.mpr (by omega)
  have hz_sq : (z : ℝ) ^ 2 ≤ (y : ℝ) := by
    have : z * z ≤ y := Nat.sqrt_le y
    have hcast : (z : ℝ) * (z : ℝ) ≤ (y : ℝ) := by exact_mod_cast this
    nlinarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hterm : ∀ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ) ≤ 16 / ((z : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 < m := by
      have := (mem_Icc.mp hm).1
      omega
    have hyd : y < m ^ (m.log y + 1) := Nat.lt_pow_succ_log_self hm1 y
    have hyd' : (y : ℝ) < ((m ^ (m.log y + 1) : ℕ) : ℝ) := by exact_mod_cast hyd
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 2) (hz_sq.trans hyd'.le)
  have hsum :
      (∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤
        ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := by
    calc
      _ ≤ ∑ _m ∈ Icc 2 z, 16 / ((z : ℝ) ^ 2) := sum_le_sum hterm
      _ = ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := by simp
  have hcard : (Icc 2 z).card ≤ z := by
    rw [Nat.card_Icc]
    omega
  have hcard' : ((Icc 2 z).card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hcard
  have hz128' : (128 : ℝ) ≤ z := by exact_mod_cast hz128
  calc
    (∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤
        ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := hsum
    _ ≤ (z : ℝ) * (16 / ((z : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = 16 / (z : ℝ) := by
      field_simp [hzpos.ne']
    _ ≤ 1 / 8 := by
      rw [div_le_iff₀ hzpos]
      linarith

private lemma dyadic_block_primes_le {y : ℕ} (hy : 2 ≤ y) (k : ℕ) :
    (∑ p ∈ (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime, 16 / (p : ℝ)) ≤
      64 / Real.log (y : ℝ) := by
  set P := (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime
  set A : ℕ := 2 ^ k * y
  set B : ℕ := 2 ^ (k + 1) * y
  have hApos_nat : 0 < A := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast hApos_nat
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hterm : ∀ p ∈ P, 16 / (p : ℝ) ≤ 16 * Real.log (p : ℝ) / ((A : ℝ) * Real.log (y : ℝ)) := by
    intro p hp
    simp only [P, mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hAp, _⟩, _⟩ := hp
    have hAp' : (A : ℝ) < (p : ℝ) := by exact_mod_cast hAp
    have hyp : (y : ℝ) ≤ (p : ℝ) := by
      have : y ≤ A := Nat.le_mul_of_pos_left y (Nat.pow_pos (by decide))
      have h' : (y : ℝ) ≤ (A : ℝ) := by exact_mod_cast this
      linarith
    have hppos : (0 : ℝ) < p := lt_trans hApos hAp'
    have hlogp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log (by positivity) hyp
    rw [div_le_div_iff₀ hppos (mul_pos hApos hlogy)]
    nlinarith [mul_le_mul_of_nonneg_left hlogp (by positivity : (0 : ℝ) ≤ 16 * (p : ℝ)),
      mul_le_mul_of_nonneg_right hAp'.le (by positivity : (0 : ℝ) ≤ 16 * Real.log (y : ℝ))]
  have hsum1 :
      (∑ p ∈ P, 16 / (p : ℝ)) ≤
        (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := by
    calc
      (∑ p ∈ P, 16 / (p : ℝ)) ≤
          ∑ p ∈ P, 16 * Real.log (p : ℝ) / ((A : ℝ) * Real.log (y : ℝ)) := sum_le_sum hterm
      _ = ∑ p ∈ P, (16 / ((A : ℝ) * Real.log (y : ℝ))) * Real.log (p : ℝ) := by
        refine sum_congr rfl fun p _ => ?_
        ring
      _ = (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := by
        rw [← mul_sum]
  have hsub : P ⊆ (Ioc 0 ⌊(B : ℝ)⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [P, mem_filter, mem_Ioc, Nat.floor_natCast] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have htheta_sub : (∑ p ∈ P, Real.log (p : ℝ)) ≤ Chebyshev.theta (B : ℝ) := by
    unfold Chebyshev.theta
    exact sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  have htheta_ub : Chebyshev.theta (B : ℝ) ≤ Real.log 4 * (B : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  have hBA : (B : ℝ) = 2 * (A : ℝ) := by
    dsimp [A, B]
    rw [pow_succ']
    push_cast
    ring
  have hlogsum : (∑ p ∈ P, Real.log (p : ℝ)) ≤ 4 * (A : ℝ) := by
    have h4 : Real.log 4 * (B : ℝ) ≤ 2 * (B : ℝ) :=
      mul_le_mul_of_nonneg_right log_four_le_two (by positivity)
    linarith
  calc
    (∑ p ∈ P, 16 / (p : ℝ)) ≤
        (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := hsum1
    _ ≤ (16 / ((A : ℝ) * Real.log (y : ℝ))) * (4 * (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogsum (by positivity)
    _ = 64 / Real.log (y : ℝ) := by
      field_simp [hApos.ne', hlogy.ne']
      ring

private lemma large_primes_sum_le {N y : ℕ} (hy : 2 ≤ y) :
    (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
      64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) := by
  set K := Nat.log 2 (N / y) + 1
  let block : ℕ → Finset ℕ := fun k => (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime
  have hcover : (Ioc y N).filter Nat.Prime ⊆ (range K).biUnion block := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hyp, hpN⟩, hprime⟩ := hp
    let q := (p - 1) / y
    have hq1 : 1 ≤ q := Nat.div_pos (by omega) (by omega)
    have hqN : q ≤ N / y := Nat.div_le_div_right (by omega)
    let k := Nat.log 2 q
    have hkK : k < K := by
      have : k ≤ Nat.log 2 (N / y) := Nat.log_mono_right hqN
      omega
    have hpow_le : 2 ^ k ≤ q := Nat.pow_log_le_self 2 (by omega)
    have hlow : 2 ^ k * y < p := by
      have h1 : 2 ^ k * y ≤ q * y := Nat.mul_le_mul_right y hpow_le
      have h2 : q * y ≤ p - 1 := Nat.div_mul_le_self (p - 1) y
      omega
    have hpow_gt : q < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) q
    have hhigh : p ≤ 2 ^ (k + 1) * y := by
      have h1 : q + 1 ≤ 2 ^ (k + 1) := by omega
      have h2 : (q + 1) * y ≤ 2 ^ (k + 1) * y := Nat.mul_le_mul_right y h1
      have hdiv := Nat.div_add_mod (p - 1) y
      have hmod : (p - 1) % y < y := Nat.mod_lt (p - 1) (by omega)
      have hmul : (q + 1) * y = y * ((p - 1) / y) + y := by
        dsimp [q]
        ring
      have h3 : p ≤ (q + 1) * y := by omega
      exact h3.trans h2
    exact mem_biUnion.mpr ⟨k, mem_range.mpr hkK, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlow, hhigh⟩, hprime⟩⟩
  have h1 :
      (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
        ∑ p ∈ (range K).biUnion block, 16 / (p : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hcover fun p _ _ => by positivity
  have h2 :
      (∑ p ∈ (range K).biUnion block, 16 / (p : ℝ)) ≤
        ∑ k ∈ range K, ∑ p ∈ block k, 16 / (p : ℝ) :=
    sum_biUnion_le_sum (range K) block (fun p => 16 / (p : ℝ)) (fun p => by positivity)
  have h3 :
      (∑ k ∈ range K, ∑ p ∈ block k, 16 / (p : ℝ)) ≤
        ∑ _k ∈ range K, 64 / Real.log (y : ℝ) :=
    sum_le_sum fun k _ => dyadic_block_primes_le hy k
  calc
    (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
        ∑ _k ∈ range K, 64 / Real.log (y : ℝ) := (h1.trans h2).trans h3
    _ = ((K : ℕ) : ℝ) * (64 / Real.log (y : ℝ)) := by simp
    _ = 64 * ((K : ℕ) : ℝ) / Real.log (y : ℝ) := by ring

private lemma bad_reciprocal_sum_le {N y : ℕ} (hN : 256 ≤ N) (hy : 16384 ≤ y)
    (hKlog : 64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) ≤ 1 / 4) :
    (∑ n ∈ ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => ¬ n ∣ Nat.lcmUpto y),
      1 / (n : ℝ)) ≤ 1 / 2 := by
  set I_N := (Icc 1 N).filter fun n => N ≤ 16 * n
  set Q := Nat.lcmUpto y
  set z := Nat.sqrt y
  let D1 := (Ioc y N).filter Nat.Prime
  let D2 := (Icc (z + 1) y).image fun m => m ^ 2
  let D3 := (Icc 2 z).image fun m => m ^ (m.log y + 1)
  let D := D1 ∪ D2 ∪ D3
  let mult : ℕ → Finset ℕ := fun d => I_N.filter fun n => d ∣ n
  have hcover : I_N.filter (fun n => ¬ n ∣ Q) ⊆ D.biUnion mult := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨hnI, hnotdvd⟩ := hn
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hnI).1).1
    have hnN : n ≤ N := (mem_Icc.mp (mem_filter.mp hnI).1).2
    have hQ0 : Q ≠ 0 := Nat.lcmUpto_ne_zero y
    have hex : ∃ p : ℕ, p.Prime ∧ Q.factorization p < n.factorization p := by
      by_contra! hall
      exact hnotdvd ((Nat.factorization_prime_le_iff_dvd (by omega) hQ0).mp hall)
    obtain ⟨p, hp, hfac⟩ := hex
    rw [Nat.factorization_lcmUpto y hp] at hfac
    have hexp : p.log y + 1 ≤ n.factorization p := by omega
    have hdvd_pow : p ^ (p.log y + 1) ∣ n :=
      (Nat.pow_dvd_pow p hexp).trans (Nat.ordProj_dvd n p)
    by_cases hpy : y < p
    · have hpdvd : p ∣ n := (dvd_pow_self p (Nat.succ_ne_zero _)).trans hdvd_pow
      have hpN : p ≤ N := (Nat.le_of_dvd (by omega) hpdvd).trans hnN
      have hpD : p ∈ D :=
        mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpy, hpN⟩, hp⟩))
      exact mem_biUnion.mpr ⟨p, hpD, mem_filter.mpr ⟨hnI, hpdvd⟩⟩
    · have hpy' : p ≤ y := le_of_not_gt hpy
      by_cases hpz : z < p
      · have hlog1 : 1 ≤ p.log y := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpy')
        have hp2dvd : p ^ 2 ∣ n :=
          (Nat.pow_dvd_pow p (show 2 ≤ p.log y + 1 by omega)).trans hdvd_pow
        have hp2D2 : p ^ 2 ∈ D2 := mem_image.mpr ⟨p, mem_Icc.mpr ⟨by omega, hpy'⟩, rfl⟩
        have hp2D : p ^ 2 ∈ D := mem_union_left _ (mem_union_right _ hp2D2)
        exact mem_biUnion.mpr ⟨p ^ 2, hp2D, mem_filter.mpr ⟨hnI, hp2dvd⟩⟩
      · have hpz' : p ≤ z := le_of_not_gt hpz
        have hp2 : 2 ≤ p := hp.two_le
        have hpD3 : p ^ (p.log y + 1) ∈ D3 :=
          mem_image.mpr ⟨p, mem_Icc.mpr ⟨hp2, hpz'⟩, rfl⟩
        have hpD : p ^ (p.log y + 1) ∈ D := mem_union_right _ hpD3
        exact mem_biUnion.mpr ⟨p ^ (p.log y + 1), hpD, mem_filter.mpr ⟨hnI, hdvd_pow⟩⟩
  let mass : ℕ → ℝ := fun d => ∑ n ∈ mult d, 1 / (n : ℝ)
  have hmass0 : ∀ d, 0 ≤ mass d := fun d => sum_nonneg fun _ _ => by positivity
  have hsub :
      (∑ n ∈ I_N.filter (fun n => ¬ n ∣ Q), 1 / (n : ℝ)) ≤ ∑ d ∈ D, mass d := by
    calc
      _ ≤ ∑ n ∈ D.biUnion mult, 1 / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ ≤ ∑ d ∈ D, mass d := sum_biUnion_le_sum D mult _ fun _ => by positivity
  have hunion123 : (∑ d ∈ D, mass d) ≤ (∑ d ∈ D1, mass d) + (∑ d ∈ D2, mass d) + ∑ d ∈ D3, mass d := by
    have h1 : (∑ d ∈ D1 ∪ D2 ∪ D3, mass d) ≤ (∑ d ∈ D1 ∪ D2, mass d) + ∑ d ∈ D3, mass d := by
      have h := sum_union_inter (s₁ := D1 ∪ D2) (s₂ := D3) (f := mass)
      have hi : 0 ≤ ∑ d ∈ (D1 ∪ D2) ∩ D3, mass d := sum_nonneg fun d _ => hmass0 d
      linarith
    have h2 : (∑ d ∈ D1 ∪ D2, mass d) ≤ (∑ d ∈ D1, mass d) + ∑ d ∈ D2, mass d := by
      have h := sum_union_inter (s₁ := D1) (s₂ := D2) (f := mass)
      have hi : 0 ≤ ∑ d ∈ D1 ∩ D2, mass d := sum_nonneg fun d _ => hmass0 d
      linarith
    dsimp [D]
    linarith
  have hN1 : 1 ≤ N := by omega
  have hD1_le : (∑ d ∈ D1, mass d) ≤ 1 / 4 := by
    have hstep : ∀ p ∈ D1, mass p ≤ 16 / (p : ℝ) := by
      intro p hp
      exact divisor_mass_le hN1 (mem_filter.mp hp).2.one_le
    exact (sum_le_sum hstep).trans ((large_primes_sum_le (by omega) ).trans hKlog)
  have hD2_le : (∑ d ∈ D2, mass d) ≤ 1 / 8 := by
    calc
      (∑ d ∈ D2, mass d) ≤ ∑ m ∈ Icc (z + 1) y, mass (m ^ 2) :=
        sum_image_le_sum _ _ mass hmass0
      _ ≤ ∑ m ∈ Icc (z + 1) y, 16 / ((m ^ 2 : ℕ) : ℝ) := by
        refine sum_le_sum fun m hm => divisor_mass_le hN1 ?_
        have : 1 ≤ m := by
          have := (mem_Icc.mp hm).1
          omega
        exact Nat.one_le_pow 2 m this
      _ ≤ 1 / 8 := large_squares_sum_le hy
  have hD3_le : (∑ d ∈ D3, mass d) ≤ 1 / 8 := by
    calc
      (∑ d ∈ D3, mass d) ≤ ∑ m ∈ Icc 2 z, mass (m ^ (m.log y + 1)) :=
        sum_image_le_sum _ _ mass hmass0
      _ ≤ ∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ) := by
        refine sum_le_sum fun m hm => divisor_mass_le hN1 ?_
        have : 1 ≤ m := by
          have := (mem_Icc.mp hm).1
          omega
        exact Nat.one_le_pow _ m this
      _ ≤ 1 / 8 := small_powers_sum_le hy
  linarith

private lemma asymptotic_params (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      256 ≤ N ∧
        let y := ⌊c * (N : ℝ) / ((Real.log N) ^ 3 * (Real.log (Real.log N)) ^ 4)⌋₊
        16384 ≤ y ∧
          64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) ≤ 1 / 4 := by
  let B : ℝ := max (4 * 20000 ^ 2) ((4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) + 20000 * |Real.log (2 / c)|)
  let N0 : ℕ := ⌈Real.exp B⌉₊ + 256
  filter_upwards [eventually_ge_atTop N0] with N hN
  have hN256 : 256 ≤ N := by omega
  refine ⟨hN256, ?_⟩
  dsimp only
  set L := Real.log (N : ℝ)
  set D := L ^ 3 * (Real.log L) ^ 4
  set X := c * (N : ℝ) / D
  set y := ⌊X⌋₊
  have hB_ge1 : (1600000000 : ℝ) ≤ B := by
    have : (4 * 20000 ^ 2 : ℝ) ≤ B := le_max_left _ _
    linarith
  have hB_ge2 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) + 20000 * |Real.log (2 / c)| ≤ B :=
    le_max_right _ _
  have hexpB_le : Real.exp B ≤ (N : ℝ) := by
    have h1 : Real.exp B ≤ (⌈Real.exp B⌉₊ : ℝ) := Nat.le_ceil (Real.exp B)
    have h2 : (⌈Real.exp B⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show ⌈Real.exp B⌉₊ ≤ N by omega)
    exact h1.trans h2
  have hBL : B ≤ L := by
    have h := Real.log_le_log (Real.exp_pos B) hexpB_le
    rwa [Real.log_exp] at h
  have hL_big : (1600000000 : ℝ) ≤ L := hB_ge1.trans hBL
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogL_sq : (Real.log L) ^ 2 ≤ 4 * L := log_sq_le_four_mul (by linarith)
  have hlogL_small : 20000 * Real.log L ≤ L := by
    have hsq : (20000 * Real.log L) ^ 2 ≤ L ^ 2 := by nlinarith
    nlinarith
  have hlogL_le : Real.log L ≤ L := by linarith
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_le_L7 : D ≤ L ^ 7 := by
    have hp4 : (Real.log L) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hlogL_pos.le hlogL_le 4
    have hL3 : 0 ≤ L ^ 3 := by positivity
    calc
      D = L ^ 3 * (Real.log L) ^ 4 := rfl
      _ ≤ L ^ 3 * L ^ 4 := mul_le_mul_of_nonneg_left hp4 hL3
      _ = L ^ 7 := by ring
  have hL8 : L ^ 8 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * Real.exp (L / 2) := by
    have hpow := Real.pow_div_factorial_le_exp (L / 4) (by linarith) 4
    have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac] at hpow
    have hsq : ((L / 4) ^ 4 / 24) ^ 2 ≤ (Real.exp (L / 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpow 2
    have hexp2 : (Real.exp (L / 4)) ^ 2 = Real.exp (L / 2) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hexp2] at hsq
    nlinarith
  have hconst_L : (4 ^ 8 * 24 ^ 2 : ℝ) ≤ (c / 2) * L := by
    have h1 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) ≤ L := by
      have ha : 0 ≤ |Real.log (2 / c)| := abs_nonneg _
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ c / 2 by positivity)
    have h3 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) * (c / 2) = (4 ^ 8 * 24 ^ 2 : ℝ) := by
      field_simp [hc.ne']
    linarith
  have hL7_exp : L ^ 7 ≤ (c / 2) * Real.exp (L / 2) := by
    have h1 : L ^ 8 ≤ (c / 2) * L * Real.exp (L / 2) := by
      calc
        L ^ 8 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * Real.exp (L / 2) := hL8
        _ ≤ ((c / 2) * L) * Real.exp (L / 2) :=
          mul_le_mul_of_nonneg_right hconst_L (Real.exp_pos _).le
    have hposexp : 0 < Real.exp (L / 2) := Real.exp_pos (L / 2)
    nlinarith
  have hN_exp : (N : ℝ) = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by exact_mod_cast (show 0 < N by omega))]
  have hX_ge_exp : 2 * Real.exp (L / 2) ≤ X := by
    dsimp [X]
    rw [le_div_iff₀ hD_pos, hN_exp]
    have hDL : D ≤ (c / 2) * Real.exp (L / 2) := hD_le_L7.trans hL7_exp
    have hmul := mul_le_mul_of_nonneg_right hDL (show 0 ≤ 2 * Real.exp (L / 2) by positivity)
    linarith
  have hexp_large : 50000 ≤ Real.exp (L / 2) := by
    have h := Real.add_one_le_exp (L / 2)
    linarith
  have hy_ge_exp : Real.exp (L / 2) ≤ (y : ℝ) := by
    have hfl : X - 1 < (y : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  have hy16384 : 16384 ≤ y := by
    have : (16384 : ℝ) ≤ (y : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨hy16384, ?_⟩
  have hlogy_ge : L / 2 ≤ Real.log (y : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (L / 2)) hy_ge_exp
    rwa [Real.log_exp] at h
  have hX_half_le_y : X / 2 ≤ (y : ℝ) := by
    have hfl : X - 1 < (y : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  have hy_ge_frac : (c / 2) * (N : ℝ) / L ^ 7 ≤ (y : ℝ) := by
    have hXL7 : c * (N : ℝ) / L ^ 7 ≤ X := by
      dsimp [X]
      exact div_le_div_of_nonneg_left (by positivity) hD_pos hD_le_L7
    have heq : (c / 2) * (N : ℝ) / L ^ 7 = (c * (N : ℝ) / L ^ 7) / 2 := by ring
    linarith
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hNy_le : ((N / y : ℕ) : ℝ) ≤ (2 / c) * L ^ 7 := by
    have h1 : ((N / y : ℕ) : ℝ) * (y : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N y
    have h2 : ((N / y : ℕ) : ℝ) ≤ (N : ℝ) / (y : ℝ) := (le_div_iff₀ hypos).mpr h1
    have h3 : (N : ℝ) / (y : ℝ) ≤ (2 / c) * L ^ 7 := by
      rw [div_le_iff₀ hypos]
      have h4 : (c / 2) * (N : ℝ) ≤ (y : ℝ) * L ^ 7 :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < L ^ 7)).mp hy_ge_frac
      have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 / c by positivity)
      have h6 : (2 / c) * ((c / 2) * (N : ℝ)) = (N : ℝ) := by
        field_simp [hc.ne']
      have h7 : (2 / c) * ((y : ℝ) * L ^ 7) = (2 / c) * L ^ 7 * (y : ℝ) := by ring
      linarith
    exact h2.trans h3
  have habs_logc : 20000 * |Real.log (2 / c)| ≤ L := by
    have hpos_t : 0 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) := by positivity
    linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
  have hK_le : ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) ≤ L / 512 := by
    by_cases hq0 : N / y = 0
    · simp [hq0]
      linarith
    · set k := Nat.log 2 (N / y)
      have hpow_nat : 2 ^ k ≤ N / y := Nat.pow_log_le_self 2 hq0
      have hpow_real : (2 : ℝ) ^ k ≤ (2 / c) * L ^ 7 := by
        have h1 : (2 : ℝ) ^ k ≤ ((N / y : ℕ) : ℝ) := by exact_mod_cast hpow_nat
        exact h1.trans hNy_le
      have hlog_pow : (k : ℝ) * Real.log 2 ≤ Real.log (2 / c) + 7 * Real.log L := by
        have h := Real.log_le_log (by positivity) hpow_real
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
        linarith
      have hk_half : (k : ℝ) * (1 / 2) ≤ |Real.log (2 / c)| + 7 * Real.log L := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        have hle1 : (k : ℝ) * (1 / 2) ≤ (k : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2.le hk0
        have hle2 : Real.log (2 / c) ≤ |Real.log (2 / c)| := le_abs_self _
        linarith
      have hcast_k : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast_k]
      linarith
  have hlogy_pos : 0 < Real.log (y : ℝ) := by linarith
  rw [div_le_iff₀ hlogy_pos]
  linarith

end Erdos294StepH1

theorem OMA.solution : OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1.H1 := by
  intro c hc
  filter_upwards [Erdos294StepH1.asymptotic_params c hc] with N hN
  obtain ⟨hN256, hy16384, hKlog⟩ := hN
  dsimp only
  set y := ⌊c * (N : ℝ) / ((Real.log N) ^ 3 * (Real.log (Real.log N)) ^ 4)⌋₊
  set Q := Nat.lcmUpto y
  set I_N := (Icc 1 N).filter fun n => N ≤ 16 * n
  set A' := I_N.filter fun n => n ∣ Q
  have hA_eq :
      ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q) = A' := by
    ext n
    simp only [A', I_N, mem_filter]
    tauto
  rw [hA_eq]
  have hharm := Erdos294StepH1.harmonic_bounds hN256
  have hbad := Erdos294StepH1.bad_reciprocal_sum_le hN256 hy16384 hKlog
  have hsplit :=
    sum_filter_add_sum_filter_not I_N (fun n => n ∣ Q) (fun n : ℕ => 1 / (n : ℝ))
  have hbad_nonneg :
      0 ≤ ∑ n ∈ I_N.filter (fun n => ¬ n ∣ Q), 1 / (n : ℝ) :=
    sum_nonneg fun _ _ => by positivity
  have hgood_lo : (3 / 2 : ℝ) ≤ ∑ n ∈ A', 1 / (n : ℝ) := by linarith
  have hgood_hi : (∑ n ∈ A', 1 / (n : ℝ)) ≤ 3 := by linarith
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast Nat.lcmUpto_pos y
  have hsum_eq : ((∑ n ∈ A', Q / n : ℕ) : ℝ) = (Q : ℝ) * ∑ n ∈ A', 1 / (n : ℝ) := by
    rw [Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hdvd : n ∣ Q := (mem_filter.mp hn).2
    have hmul : ((Q / n : ℕ) : ℝ) * (n : ℝ) = (Q : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    field_simp [hnpos.ne']
    linarith
  constructor
  · have hreal : ((3 * Q : ℕ) : ℝ) ≤ ((2 * ∑ n ∈ A', Q / n : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsum_eq]
      nlinarith
    exact_mod_cast hreal
  · have hreal : ((∑ n ∈ A', Q / n : ℕ) : ℝ) ≤ ((3 * Q : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsum_eq]
      nlinarith
    exact_mod_cast hreal
