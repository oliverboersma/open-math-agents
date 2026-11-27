import OMAReductions.R_oeis_a387471_R1
import Mathlib

/-! Bounds and exact identities for the three-degree trigonometric grid. -/

namespace CevaGrid

open Real

private noncomputable def angle (j : ℤ) : ℝ := Real.pi * j / 60

private noncomputable def sine (j : ℤ) : ℝ := Real.sin (angle j)

private theorem sum_sine (m n : ℤ) :
    sine m + sine n =
      2 * Real.sin (angle (m+n) / 2) * Real.cos (angle (m-n) / 2) := by
  have h₁ : angle (m+n) / 2 = (angle m + angle n) / 2 := by simp [angle]; ring
  have h₂ : angle (m-n) / 2 = (angle m - angle n) / 2 := by simp [angle]; ring
  rw [h₁, h₂]
  exact Real.sin_add_sin (angle m) (angle n)

private theorem product_to_sum (x y z : ℝ) :
    4 * (sin x * sin y * sin z) =
      sin (x+y-z) + sin (x-y+z) + sin (-x+y+z) - sin (x+y+z) := by
  simp only [sin_add, sin_sub, cos_add, cos_sub, sin_neg, cos_neg]
  ring

private theorem sine_neg (j : ℤ) : sine (-j) = -sine j := by
  unfold sine
  rw [show angle (-j) = -angle j by simp [angle]; ring, sin_neg]

private theorem exact_grid : sine 2 * sine 14 * sine 16 = sine 18 * sine 6 * sine 4 := by
  have habc := product_to_sum (angle 2) (angle 14) (angle 16)
  have hdef := product_to_sum (angle 18) (angle 6) (angle 4)
  rw [show angle 2 + angle 14 - angle 16 = angle 0 by norm_num [angle]; ring,
    show angle 2 - angle 14 + angle 16 = angle 4 by norm_num [angle]; ring,
    show -angle 2 + angle 14 + angle 16 = angle 28 by norm_num [angle]; ring,
    show angle 2 + angle 14 + angle 16 = angle 32 by norm_num [angle]; ring] at habc
  rw [show angle 18 + angle 6 - angle 4 = angle 20 by norm_num [angle]; ring,
    show angle 18 - angle 6 + angle 4 = angle 16 by norm_num [angle]; ring,
    show -angle 18 + angle 6 + angle 4 = angle (-8) by norm_num [angle]; ring,
    show angle 18 + angle 6 + angle 4 = angle 28 by norm_num [angle]; ring] at hdef
  change 4 * (sine 2 * sine 14 * sine 16) =
    sine 0 + sine 4 + sine 28 - sine 32 at habc
  change 4 * (sine 18 * sine 6 * sine 4) =
    sine 20 + sine 16 + sine (-8) - sine 28 at hdef
  have h0 : sine 0 = 0 := by simp [sine, angle]
  have hneg := sine_neg 8
  have hsup : sine 32 = sine 28 := by
    unfold sine
    rw [show angle 32 = Real.pi - angle 28 by norm_num [angle]; ring, sin_pi_sub]
  have hplus : sine 28 + sine 8 = 2 * sine 18 * cos (Real.pi / 6) := by
    rw [sum_sine]
    rw [show angle (28+8) / 2 = angle 18 by norm_num [angle]; ring,
      show angle (28-8) / 2 = Real.pi / 6 by norm_num [angle]; ring]
    rfl
  have hminus : sine 16 - sine 4 = 2 * sine 6 * cos (Real.pi / 6) := by
    rw [sub_eq_add_neg, ← sine_neg 4, sum_sine,
      show angle (16 + (-4)) / 2 = angle 6 by norm_num [angle]; ring,
      show angle (16 - (-4)) / 2 = Real.pi / 6 by norm_num [angle]; ring]
    rfl
  have h20 : sine 20 = cos (Real.pi / 6) := by
    simp only [sine]
    rw [← sin_pi_div_two_sub]
    congr 1
    norm_num [angle]; ring
  have h18 : sine 18 = cos (Real.pi / 5) := by
    simp only [sine]
    rw [← sin_pi_div_two_sub]
    congr 1
    norm_num [angle]; ring
  have h6 : sine 6 = cos (2 * (Real.pi / 5)) := by
    simp only [sine]
    rw [← sin_pi_div_two_sub]
    congr 1
    norm_num [angle]; ring
  have hgold : sine 18 = 1/2 + sine 6 := by
    rw [h18, h6, cos_two_mul]
    linarith [quadratic_root_cos_pi_div_five]
  rw [h0, hsup] at habc
  rw [hneg, h20] at hdef
  nlinarith [congrArg (fun z : ℝ => 2 * z * cos (Real.pi / 6)) hgold]

private noncomputable def approx (x : ℝ) : ℝ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880

private theorem sine_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x - approx x| ≤ 1/1000000 := by
  let z : ℂ := (x : ℂ) * Complex.I
  have hz : ‖z‖ = x := by simp [z, abs_of_nonneg hx0]
  have h := Complex.exp_bound (n := 10) (show ‖z‖ ≤ 1 by rwa [hz]) (by decide)
  have him := Complex.abs_im_le_norm (Complex.exp z -
    ∑ m ∈ Finset.range 10, z^m / (m.factorial : ℂ))
  have he : (Complex.exp z -
    ∑ m ∈ Finset.range 10, z^m / (m.factorial : ℂ)).im = Real.sin x - approx x := by
    simp only [Complex.sub_im, Complex.exp_im, z, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_sub, neg_zero, add_zero, mul_one, Real.exp_zero, one_mul]
    congr 1
    rw [Complex.im_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [approx, mul_pow, Complex.mul_im, Complex.mul_re, Complex.div_im,
      Complex.normSq_apply, Nat.factorial_succ, Complex.I_pow_eq_pow_mod, pow_succ]; ring
  rw [he] at him
  refine him.trans (h.trans ?_)
  rw [hz]
  have hp := pow_le_one₀ hx0 hx1 (n := 10)
  norm_num at *
  linarith

private noncomputable def wave (i : Fin 19) := sine ((i.val : ℤ)+1)

private def sample (i : Fin 19) : ℤ :=
  ![5234, 10453, 15643, 20791, 25882, 30902, 35837, 40674, 45399, 50000, 54464, 58779, 62932, 66913, 70711, 74314, 77715, 80902, 83867] i

private noncomputable def center (i : Fin 19) : ℝ := (sample i : ℝ) / 100000

private theorem center_norm (i : Fin 19) : |center i| ≤ 1 := by
  fin_cases i <;> norm_num [center, sample, Matrix.cons_val_zero, Matrix.cons_val_succ]

private theorem wave_norm (i : Fin 19) : |wave i| ≤ 1 := Real.abs_sin_le_one _

private theorem sample_close (i : Fin 19) : |wave i - center i| ≤ 1/100000 := by
  let u : ℝ := (i.val : ℝ) + 1
  let r : ℝ := (3141593/1000000 : ℝ) * u / 60
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 19 := by
    have hi : i.val + 1 ≤ 19 := by omega
    dsimp [u]
    exact_mod_cast hi
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hangle : |angle ((i.val : ℤ)+1) - r| ≤ 1/1000000 := by
    have hlo : 0 ≤ (Real.pi - (3141592/1000000 : ℝ)) * u :=
      mul_nonneg (sub_nonneg.mpr (by linarith [Real.pi_gt_d6])) hu0
    have hhi : 0 ≤ ((3141593/1000000 : ℝ) - Real.pi) * u :=
      mul_nonneg (sub_nonneg.mpr (by linarith [Real.pi_lt_d6])) hu0
    apply abs_le.mpr
    unfold angle r u at *
    push_cast
    constructor <;> nlinarith
  have h₁ : |wave i - sin r| ≤ 1/1000000 :=
    (Real.abs_sin_sub_sin_le _ _).trans hangle
  have h₂ := sine_error r hr0 hr1
  have h₃ : |approx r - center i| ≤ 1/125000 := by
    fin_cases i <;> norm_num [r, u, approx, center, sample, Matrix.cons_val_zero, Matrix.cons_val_succ]
  calc
    _ ≤ |wave i - sin r| + |sin r - approx r| + |approx r - center i| := by
      rw [show wave i - center i =
        (wave i - sin r + (sin r - approx r)) + (approx r - center i) by ring]
      exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

private theorem product_close (a b c : Fin 19) :
    |wave a * wave b * wave c - center a * center b * center c| ≤ 3/100000 := by
  rw [show wave a * wave b * wave c - center a * center b * center c =
    (wave a - center a) * wave b * wave c + center a * (wave b - center b) * wave c +
      center a * center b * (wave c - center c) by ring]
  refine (abs_add_le _ _).trans ((add_le_add_left (abs_add_le _ _) _).trans ?_)
  simp only [abs_mul]
  calc
    _ ≤ ((1/100000 : ℝ) * 1 * 1) + (1 * (1/100000) * 1) + (1 * 1 * (1/100000)) := by
      gcongr <;> first | apply sample_close | apply wave_norm | apply center_norm
    _ = _ := by norm_num

private abbrev Triple := Fin 19 × Fin 19 × Fin 19

private def good : Finset Triple := {(1,13,15), (1,15,13), (13,1,15), (13,15,1), (15,1,13), (15,13,1), (3,5,17), (3,17,5), (5,3,17), (5,17,3), (17,3,5), (17,5,3)}

private def difference (a b c : Fin 19) : ℤ :=
  sample a * sample b * sample c - sample a.rev * sample b.rev * sample c.rev

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem check (a b c : Fin 19) : a ≠ 9 → b ≠ 9 → c ≠ 9 →
    (difference a b c).natAbs ≤ 60000000000 → (a,b,c) ∈ good := by
  revert b c
  fin_cases a <;> decide +kernel

private theorem finite_classification (a b c : Fin 19) (ha : a ≠ 9) (hb : b ≠ 9) (hc : c ≠ 9) :
    wave a * wave b * wave c = wave a.rev * wave b.rev * wave c.rev ↔ (a,b,c) ∈ good := by
  constructor
  · intro he
    apply check a b c ha hb hc
    have h₁ := product_close a b c
    have h₂ := product_close a.rev b.rev c.rev
    have ht := (abs_add_le
      (center a * center b * center c - wave a * wave b * wave c)
      (wave a.rev * wave b.rev * wave c.rev - center a.rev * center b.rev * center c.rev))
    rw [← he, show (center a * center b * center c - wave a * wave b * wave c) +
      (wave a * wave b * wave c - center a.rev * center b.rev * center c.rev) =
      center a * center b * center c - center a.rev * center b.rev * center c.rev by ring] at ht
    have hg : |center a * center b * center c -
        center a.rev * center b.rev * center c.rev| ≤ 6/100000 := by
      rw [abs_sub_comm (center a * center b * center c) (wave a * wave b * wave c)] at ht
      rw [← he] at h₂
      linarith
    have hg' : |(↑(difference a b c) : ℝ)| ≤ 60000000000 := by
      unfold difference
      push_cast
      dsimp [center] at hg
      rw [show (sample a : ℝ) * (sample b : ℝ) * (sample c : ℝ) -
          (sample a.rev : ℝ) * (sample b.rev : ℝ) * (sample c.rev : ℝ) =
          1000000000000000 * ((sample a : ℝ) / 100000 * ((sample b : ℝ) / 100000) *
            ((sample c : ℝ) / 100000) - ((sample a.rev : ℝ) / 100000) *
            ((sample b.rev : ℝ) / 100000) * ((sample c.rev : ℝ) / 100000)) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000000000000000)]
      linarith
    rw [← Int.cast_abs, Int.abs_eq_natAbs] at hg'
    exact_mod_cast hg'
  · intro h
    simp only [good, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl,rfl⟩ := h <;>
      norm_num [wave, Fin.rev] <;>
      first | simpa only [mul_comm, mul_left_comm, mul_assoc] using exact_grid
            | simpa only [mul_comm, mul_left_comm, mul_assoc] using exact_grid.symm

open OMA.S_oeis_a387471 (ratio)

private abbrev Rays (n : ℕ) := Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)

private def eligible (n : ℕ) : Set (Rays n) :=
  {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧
    ¬ (t.1.val+1=n ∨ t.2.1.val+1=n ∨ t.2.2.val+1=n) ∧
    (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))}

private theorem ratio_grid {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1)) (a : Fin 19)
    (he : 10*(i.val+1) = n*(a.val+1)) :
    ratio (2*n-1) i.val = wave a / wave a.rev := by
  have hm : (2*n-1)+1 = 2*n := by omega
  have hmR : ((↑(2*n-1 : ℕ) : ℝ)+1) = 2*(n : ℝ) := by exact_mod_cast hm
  have heR : (10 : ℝ)*((i.val : ℝ)+1) = (n : ℝ)*((a.val : ℝ)+1) := by exact_mod_cast he
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hx : ((i.val : ℝ)+1)*Real.pi/(3*((↑(2*n-1 : ℕ) : ℝ)+1)) =
      angle ((a.val : ℤ)+1) := by
    rw [hmR, angle]
    push_cast
    calc
      _ = (10*((i.val : ℝ)+1))*Real.pi/(60*(n : ℝ)) := by ring
      _ = _ := by rw [heR]; field_simp
  have hrefl : a.rev.val+1+a.val+1 = 20 := by
    rw [Fin.val_rev]
    omega
  have hreflR : (a.rev.val : ℝ)+1+(a.val : ℝ)+1 = 20 := by exact_mod_cast hrefl
  have hy : Real.pi / 3 - angle ((a.val : ℤ)+1) = angle ((a.rev.val : ℤ)+1) := by
    unfold angle
    push_cast
    linear_combination -(Real.pi / 60) * hreflR
  unfold ratio wave sine
  dsimp only
  rw [hx, hy]

private theorem wave_pos (a : Fin 19) : 0 < wave a := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold angle
    exact div_pos (mul_pos Real.pi_pos (by positivity)) (by norm_num)
  · have hu : (a.val : ℝ)+1 ≤ 19 := by exact_mod_cast (by omega : a.val+1 ≤ 19)
    unfold angle
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) Real.pi_pos.le, Real.pi_pos]

private theorem median_iff {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1)) (a : Fin 19)
    (he : 10*(i.val+1) = n*(a.val+1)) : i.val+1=n ↔ a=9 := by
  constructor
  · intro hi
    rw [hi, Nat.mul_comm 10 n] at he
    have ha := (Nat.mul_left_cancel_iff (by omega : 0 < n)).mp he
    apply Fin.ext
    omega
  · rintro rfl
    change 10*(i.val+1)=n*10 at he
    omega

private def positions : Finset (Fin 19) := {1,3,5,13,15,17}

private theorem good_indices (a b c : Fin 19) : (a,b,c) ∈ good →
    a ∈ positions ∧ b ∈ positions ∧ c ∈ positions := by
  intro h
  simp only [good, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl,rfl⟩ := h <;> decide

private theorem pos_data : ∀ a : Fin 19, a ∈ positions →
    (a.val+1)%2=0 ∧ Nat.Coprime 5 (a.val+1) := by decide

private theorem pos_not_median {a : Fin 19} (ha : a ∈ positions) : a ≠ 9 := by
  rintro rfl
  exact (by decide : (9 : Fin 19) ∉ positions) ha

private theorem eligible_grid {n : ℕ} (hn : 1 ≤ n) (t : Rays n) (s : Triple)
    (ha : 10*(t.1.val+1)=n*(s.1.val+1))
    (hb : 10*(t.2.1.val+1)=n*(s.2.1.val+1))
    (hc : 10*(t.2.2.val+1)=n*(s.2.2.val+1)) : t ∈ eligible n ↔ s ∈ good := by
  rcases t with ⟨i,j,k⟩
  rcases s with ⟨a,b,c⟩
  have hprod :
      ratio (2*n-1) i.val * ratio (2*n-1) j.val * ratio (2*n-1) k.val = 1 ↔
      wave a * wave b * wave c = wave a.rev * wave b.rev * wave c.rev := by
    rw [ratio_grid hn i a ha, ratio_grid hn j b hb, ratio_grid hn k c hc,
      div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq
        (mul_ne_zero (mul_ne_zero (wave_pos _).ne' (wave_pos _).ne') (wave_pos _).ne')]
  have ham := median_iff hn i a ha
  have hbm := median_iff hn j b hb
  have hcm := median_iff hn k c hc
  constructor
  · rintro ⟨he,hm,_⟩
    exact (finite_classification a b c (fun h => hm (Or.inl (ham.mpr h)))
      (fun h => hm (Or.inr (Or.inl (hbm.mpr h)))) (fun h => hm (Or.inr (Or.inr (hcm.mpr h))))).mp
      (hprod.mp he)
  · intro hg
    obtain ⟨ha',hb',hc'⟩ := good_indices a b c hg
    have hna := pos_not_median ha'
    have hnb := pos_not_median hb'
    have hnc := pos_not_median hc'
    refine ⟨hprod.mpr ((finite_classification a b c hna hnb hnc).mpr hg), ?_,
      ⟨⟨a.val+1,ha⟩,⟨b.val+1,hb⟩,⟨c.val+1,hc⟩⟩⟩
    rintro (h | h | h)
    · exact hna (ham.mp h)
    · exact hnb (hbm.mp h)
    · exact hnc (hcm.mp h)

private theorem exists_code {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1))
    (hd : n ∣ 10*(i.val+1)) : ∃ a : Fin 19, 10*(i.val+1)=n*(a.val+1) := by
  obtain ⟨q,hq⟩ := hd
  have hq0 : 0 < q := by by_contra! hh; simp [show q=0 by omega] at hq
  have hq20 : q < 20 := by
    apply (Nat.mul_lt_mul_left (by omega : 0 < n)).mp
    rw [← hq]
    have hi := i.isLt
    omega
  exact ⟨⟨q-1, by omega⟩, by
    change 10*(i.val+1)=n*(q-1+1)
    rw [show q-1+1=q by omega]
    exact hq⟩

private noncomputable def code {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1))
    (hd : n ∣ 10*(i.val+1)) : Fin 19 := (exists_code hn i hd).choose

private theorem code_spec {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1))
    (hd : n ∣ 10*(i.val+1)) : 10*(i.val+1)=n*((code hn i hd).val+1) :=
  (exists_code hn i hd).choose_spec

private theorem code_unique {n : ℕ} (hn : 1 ≤ n) {i : Fin (2*n-1)} {a b : Fin 19}
    (ha : 10*(i.val+1)=n*(a.val+1)) (hb : 10*(i.val+1)=n*(b.val+1)) : a=b := by
  have h := (Nat.mul_left_cancel_iff (by omega : 0 < n)).mp (ha.symm.trans hb)
  apply Fin.ext
  omega

private theorem five_dvd {n : ℕ} {i : Fin (2*n-1)} {a : Fin 19}
    (ha : a ∈ positions) (he : 10*(i.val+1)=n*(a.val+1)) : 5 ∣ n := by
  apply (pos_data a ha).2.dvd_of_dvd_mul_right
  rw [← he]
  exact dvd_mul_of_dvd_left (by decide : 5 ∣ 10) _

private def liftCode (d : ℕ) (hd : 0 < d) (a : Fin 19) : Fin (2*(5*d)-1) :=
  ⟨d*((a.val+1)/2)-1, by
    have hh : (a.val+1)/2 < 10 := by omega
    have hh' := Nat.mul_lt_mul_of_pos_left hh hd
    omega⟩

private theorem lift_spec (d : ℕ) (hd : 0 < d) (a : Fin 19) (ha : a ∈ positions) :
    10*((liftCode d hd a).val+1)=(5*d)*(a.val+1) := by
  have hea := (pos_data a ha).1
  have hpa : 0 < (a.val+1)/2 := by omega
  have hpos := Nat.mul_pos hd hpa
  change 10*(d*((a.val+1)/2)-1+1)=(5*d)*(a.val+1)
  rw [show d*((a.val+1)/2)-1+1=d*((a.val+1)/2) by omega]
  conv_rhs => rw [show a.val+1=2*((a.val+1)/2) by omega]
  ring

private noncomputable def encode {n : ℕ} (hn : 1 ≤ n) (t : Rays n)
    (h : t ∈ eligible n) : Triple :=
  (code hn t.1 h.2.2.1, code hn t.2.1 h.2.2.2.1, code hn t.2.2 h.2.2.2.2)

theorem main : ∀ n : ℕ, 1 ≤ n → (eligible n).ncard = if 5 ∣ n then 12 else 0 := by
  intro n hn
  have hg : ∀ t h, encode hn t h ∈ good := by
    intro t h
    exact (eligible_grid hn t (encode hn t h) (code_spec hn _ h.2.2.1)
      (code_spec hn _ h.2.2.2.1) (code_spec hn _ h.2.2.2.2)).mp h
  by_cases h5 : 5 ∣ n
  · rw [if_pos h5]
    calc
      _ = (good : Set Triple).ncard := by
        apply Set.ncard_congr (encode hn) hg
        · intro x y hx hy he
          have h₁ := code_spec hn x.1 hx.2.2.1
          have h₂ := code_spec hn x.2.1 hx.2.2.2.1
          have h₃ := code_spec hn x.2.2 hx.2.2.2.2
          have h₄ := code_spec hn y.1 hy.2.2.1
          have h₅ := code_spec hn y.2.1 hy.2.2.2.1
          have h₆ := code_spec hn y.2.2 hy.2.2.2.2
          dsimp [encode] at he
          simp only [Prod.mk.injEq] at he
          rcases he with ⟨e₁,e₂,e₃⟩
          rw [e₁] at h₁
          rw [e₂] at h₂
          rw [e₃] at h₃
          exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
        · obtain ⟨d,rfl⟩ := h5
          have hd : 0 < d := by omega
          rintro ⟨a,b,c⟩ h
          obtain ⟨ha,hb,hc⟩ := good_indices a b c h
          let t := (liftCode d hd a,liftCode d hd b,liftCode d hd c)
          have ea := lift_spec d hd a ha
          have eb := lift_spec d hd b hb
          have ec := lift_spec d hd c hc
          have ht := (eligible_grid hn t (a,b,c) ea eb ec).mpr h
          refine ⟨t, ht, ?_⟩
          exact Prod.ext (code_unique hn (code_spec hn _ ht.2.2.1) ea)
            (Prod.ext (code_unique hn (code_spec hn _ ht.2.2.2.1) eb)
              (code_unique hn (code_spec hn _ ht.2.2.2.2) ec))
      _ = 12 := by rw [Set.ncard_coe_finset]; decide
  · rw [if_neg h5]
    have he : eligible n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t h
      have hpos := (good_indices _ _ _ (hg t h)).1
      exact h5 (five_dvd hpos (code_spec hn t.1 h.2.2.1))
    simp [he]

end CevaGrid

theorem OMA.solution : OMA.R_oeis_a387471_R1.H2 :=
  CevaGrid.main