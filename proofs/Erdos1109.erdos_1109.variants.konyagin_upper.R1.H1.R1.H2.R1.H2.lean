import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1
import Mathlib

/-!
Large sieve bound for reduced prime and small prime square denominators via the discrete Fejer kernel.
-/

namespace OMA.LargeSieve1109

open Finset Real
open scoped ComplexConjugate

private noncomputable def e (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * θ)

private lemma e_zero : e 0 = 1 := by
  simp [e]

private lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma e_neg (x : ℝ) : e (-x) = conj (e x) := by
  have h1 : e (-x) * e x = 1 := by
    rw [← e_add, neg_add_cancel, e_zero]
  have h2 : conj (e x) * e x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]
    norm_num
  have hne : e x ≠ 0 := by
    intro hz
    have hn := norm_e x
    simp [hz] at hn
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

private lemma e_sub (x y : ℝ) : e (x - y) = e x * conj (e y) := by
  rw [sub_eq_add_neg, e_add, e_neg]

private lemma e_nat_mul (θ : ℝ) (n : ℕ) : e (θ * n) = (e θ) ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma e_int_add_one (θ : ℝ) : e (θ + 1) = e θ := by
  rw [e_add]
  have h1 : e 1 = 1 := by
    unfold e
    simpa [mul_assoc] using Complex.exp_two_pi_mul_I
  rw [h1, mul_one]

private lemma e_int_sub_one (θ : ℝ) : e (θ - 1) = e θ := by
  have h := e_int_add_one (θ - 1)
  simpa using h.symm

private lemma two_abs_le_norm_e_sub_one {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    2 * |θ| ≤ ‖e θ - 1‖ := by
  rcases eq_or_lt_of_le (abs_nonneg θ) with h0 | hpos
  · have hz : θ = 0 := abs_eq_zero.mp h0.symm
    simp [hz]
  by_cases hq : |θ| ≤ 1 / 4
  · have hy_pos : 0 < 2 * Real.pi * |θ| := by positivity
    have hy_lt2 : 2 * Real.pi * |θ| < 2 := by nlinarith [Real.pi_lt_four]
    have hsin_pos : 2 * |θ| ≤ Real.sin (2 * Real.pi * |θ|) := by
      have hcube := Real.sin_gt_sub_cube hy_pos
      have hsq : (2 * Real.pi * |θ|) ^ 2 ≤ 4 := by nlinarith
      have hpi3 : 3 < Real.pi := Real.pi_gt_three
      nlinarith
    have him : |(e θ - 1).im| = Real.sin (2 * Real.pi * |θ|) := by
      unfold e
      have h : 2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
      rcases le_or_gt 0 θ with hnn | hneg
      · have habs : |θ| = θ := abs_of_nonneg hnn
        rw [habs] at hsin_pos ⊢
        rw [abs_of_nonneg (by linarith [hsin_pos])]
      · have hneg' : |θ| = -θ := abs_of_neg hneg
        have harg : 2 * Real.pi * θ = -(2 * Real.pi * |θ|) := by rw [hneg']; ring
        rw [harg, Real.sin_neg, abs_neg, abs_of_nonneg (by linarith [hsin_pos, abs_nonneg θ])]
    calc 2 * |θ| ≤ Real.sin (2 * Real.pi * |θ|) := hsin_pos
      _ = |(e θ - 1).im| := him.symm
      _ ≤ ‖e θ - 1‖ := Complex.abs_im_le_norm _
  · push Not at hq
    have hlo : Real.pi / 2 ≤ 2 * Real.pi * |θ| := by nlinarith [Real.pi_pos]
    have hhi : 2 * Real.pi * |θ| ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hcos_abs : Real.cos (2 * Real.pi * |θ|) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hlo (by linarith [Real.pi_pos])
    have hcos_eq : Real.cos (2 * Real.pi * θ) = Real.cos (2 * Real.pi * |θ|) := by
      rcases le_or_gt 0 θ with hnn | hneg
      · rw [abs_of_nonneg hnn]
      · rw [abs_of_neg hneg, mul_neg, Real.cos_neg]
    have hre : (e θ - 1).re = Real.cos (2 * Real.pi * θ) - 1 := by
      unfold e
      have h : 2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h, Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
    have habs_re : 1 ≤ |(e θ - 1).re| := by
      rw [hre, hcos_eq, abs_of_nonpos (by linarith)]
      linarith
    calc 2 * |θ| ≤ 1 := by linarith
      _ ≤ |(e θ - 1).re| := habs_re
      _ ≤ ‖e θ - 1‖ := Complex.abs_re_le_norm _

private lemma fejer_bound (H : ℕ) {θ : ℝ} (hpos : 0 < |θ|) (hhi : |θ| ≤ 1 / 2) :
    ‖∑ h ∈ range H, (e θ) ^ h‖ ^ 2 ≤ 1 / θ ^ 2 := by
  have hmul : (∑ h ∈ range H, (e θ) ^ h) * (e θ - 1) = (e θ) ^ H - 1 := geom_sum_mul (e θ) H
  have htop : ‖(e θ) ^ H - 1‖ ≤ 2 := by
    calc ‖(e θ) ^ H - 1‖ ≤ ‖(e θ) ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖e θ‖ ^ H + 1 := by rw [norm_pow, norm_one]
      _ = 2 := by rw [norm_e, one_pow]; norm_num
  have hbot : 2 * |θ| ≤ ‖e θ - 1‖ := two_abs_le_norm_e_sub_one hhi
  have hprod : ‖∑ h ∈ range H, (e θ) ^ h‖ * (2 * |θ|) ≤ 2 := by
    calc ‖∑ h ∈ range H, (e θ) ^ h‖ * (2 * |θ|)
        ≤ ‖∑ h ∈ range H, (e θ) ^ h‖ * ‖e θ - 1‖ :=
          mul_le_mul_of_nonneg_left hbot (norm_nonneg _)
      _ = ‖(∑ h ∈ range H, (e θ) ^ h) * (e θ - 1)‖ := (norm_mul _ _).symm
      _ = ‖(e θ) ^ H - 1‖ := by rw [hmul]
      _ ≤ 2 := htop
  have hle : ‖∑ h ∈ range H, (e θ) ^ h‖ ≤ 1 / |θ| := by
    rw [le_div_iff₀ hpos]
    linarith
  have hsq : ‖∑ h ∈ range H, (e θ) ^ h‖ ^ 2 ≤ (1 / |θ|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  simpa [div_pow, sq_abs] using hsq

private lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ m ∈ Icc 1 N, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have aux : ∀ k : ℕ, ∑ m ∈ Icc 1 (k + 1), (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 2 - 1 / ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hsplit : Icc 1 (k + 2) = insert (k + 2) (Icc 1 (k + 1)) := by
        ext x
        simp only [mem_Icc, mem_insert]
        omega
      rw [hsplit, sum_insert (by simp)]
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hstep : (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 2) ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
        push_cast
        rw [div_sub_div _ _ hk1.ne' hk2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hk := aux k
  have hpos : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  linarith

private lemma ray_sum_le {ι : Type*} [DecidableEq ι] (U : Finset ι) (N : ℕ) (y : ι → ℝ)
    (hlo : ∀ x ∈ U, 1 ≤ y x) (hhi : ∀ x ∈ U, y x ≤ N)
    (hsep : ∀ x ∈ U, ∀ z ∈ U, x ≠ z → 1 ≤ |y x - y z|) :
    ∑ x ∈ U, (1 : ℝ) / (y x) ^ 2 ≤ 2 := by
  let m : ι → ℕ := fun x => ⌊y x⌋₊
  have hm_mem : ∀ x ∈ U, m x ∈ Icc 1 N := by
    intro x hx
    rw [mem_Icc]
    refine ⟨(Nat.le_floor_iff (by linarith [hlo x hx])).mpr (by simpa using hlo x hx), ?_⟩
    exact Nat.floor_le_of_le (hhi x hx)
  have hm_inj : Set.InjOn m (U : Set ι) := by
    intro x hx z hz heq
    by_contra hne
    have hxU : x ∈ U := mem_coe.mp hx
    have hzU : z ∈ U := mem_coe.mp hz
    have hx_lo : (m x : ℝ) ≤ y x := Nat.floor_le (by linarith [hlo x hxU])
    have hx_hi : y x < (m x : ℝ) + 1 := Nat.lt_floor_add_one (y x)
    have hz_lo : (m z : ℝ) ≤ y z := Nat.floor_le (by linarith [hlo z hzU])
    have hz_hi : y z < (m z : ℝ) + 1 := Nat.lt_floor_add_one (y z)
    have hlt : |y x - y z| < 1 := by
      rw [abs_lt]
      change m x = m z at heq
      have heq' : (m x : ℝ) = (m z : ℝ) := by exact_mod_cast heq
      constructor <;> linarith
    linarith [hsep x hxU z hzU hne]
  have hterm : ∀ x ∈ U, (1 : ℝ) / (y x) ^ 2 ≤ (1 : ℝ) / ((m x : ℝ) ^ 2) := by
    intro x hx
    have hm1 : 1 ≤ m x := (mem_Icc.mp (hm_mem x hx)).1
    have hm_pos : (0 : ℝ) < (m x : ℝ) := by exact_mod_cast hm1
    have hm_le : (m x : ℝ) ≤ y x := Nat.floor_le (by linarith [hlo x hx])
    exact one_div_le_one_div_of_le (sq_pos_of_pos hm_pos) (pow_le_pow_left₀ hm_pos.le hm_le 2)
  calc ∑ x ∈ U, (1 : ℝ) / (y x) ^ 2
      ≤ ∑ x ∈ U, (1 : ℝ) / ((m x : ℝ) ^ 2) := sum_le_sum hterm
    _ = ∑ n ∈ U.image m, (1 : ℝ) / ((n : ℝ) ^ 2) :=
          (sum_image (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) hm_inj).symm
    _ ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ 2) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro n hn
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
        exact hm_mem x hx
    _ ≤ 2 := sum_inv_sq_le_two N

private lemma row_kernel_sum {ι : Type*} [DecidableEq ι] (J : Finset ι) (N : ℕ) (hN : 0 < N)
    (α : ι → ℝ)
    (h01 : ∀ x ∈ J, 0 < α x ∧ α x < 1)
    (hsep : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → 1 / (N : ℝ) ≤ |α x - α y| ∧ 1 / (N : ℝ) ≤ 1 - |α x - α y|)
    {j : ι} (hj : j ∈ J) :
    ∑ k ∈ J, ‖∑ h ∈ range (2 * N), (e (α k - α j)) ^ h‖ ^ 2 ≤ 8 * (N : ℝ) ^ 2 := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  let β : ι → ℝ := fun k =>
    if α k - α j > 1 / 2 then α k - 1
    else if α j - α k > 1 / 2 then α k + 1
    else α k
  have hβj : β j = α j := by
    dsimp only [β]
    split_ifs <;> linarith
  have hβ_eq_e : ∀ k, e (β k - α j) = e (α k - α j) := by
    intro k
    dsimp only [β]
    split_ifs with h1 h2
    · rw [show α k - 1 - α j = (α k - α j) - 1 by ring, e_int_sub_one]
    · rw [show α k + 1 - α j = (α k - α j) + 1 by ring, e_int_add_one]
    · rfl
  have hβ_half : ∀ k ∈ J, |β k - α j| ≤ 1 / 2 := by
    intro k hk
    have hk01 := h01 k hk
    have hj01 := h01 j hj
    dsimp only [β]
    split_ifs with h1 h2 <;> rw [abs_le] <;> constructor <;> linarith
  have hβ_cases : ∀ w, (β w = α w - 1 ∧ 1 / 2 < α w - α j) ∨
      (β w = α w + 1 ∧ 1 / 2 < α j - α w) ∨
      (β w = α w ∧ α w - α j ≤ 1 / 2 ∧ α j - α w ≤ 1 / 2) := by
    intro w
    dsimp only [β]
    split_ifs with h1 h2
    · exact Or.inl ⟨rfl, h1⟩
    · exact Or.inr (Or.inl ⟨rfl, h2⟩)
    · exact Or.inr (Or.inr ⟨rfl, le_of_not_gt h1, le_of_not_gt h2⟩)
  have hβ_sep : ∀ x ∈ J, ∀ z ∈ J, x ≠ z → 1 / (N : ℝ) ≤ |β x - β z| := by
    intro x hx z hz hne
    obtain ⟨hd1, hd2⟩ := hsep x hx z hz hne
    have hx01 := h01 x hx
    have hz01 := h01 z hz
    have hj01 := h01 j hj
    rcases le_total (α x) (α z) with hxz | hzx
    · have habs_xz : |α x - α z| = α z - α x := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs_xz] at hd1 hd2
      rcases hβ_cases x with ⟨hbx, hx1⟩ | ⟨hbx, hx2⟩ | ⟨hbx, hx3a, hx3b⟩ <;>
        rcases hβ_cases z with ⟨hbz, hz1⟩ | ⟨hbz, hz2⟩ | ⟨hbz, hz3a, hz3b⟩ <;>
        rw [hbx, hbz]
      · rw [show α x - 1 - (α z - 1) = -(α z - α x) by ring, abs_neg, abs_of_nonneg (by linarith)]
        exact hd1
      · exfalso; linarith
      · exfalso; linarith
      · rw [show α x + 1 - (α z - 1) = 2 - (α z - α x) by ring, abs_of_nonneg (by linarith)]
        linarith
      · rw [show α x + 1 - (α z + 1) = -(α z - α x) by ring, abs_neg, abs_of_nonneg (by linarith)]
        exact hd1
      · rw [show α x + 1 - α z = 1 - (α z - α x) by ring, abs_of_nonneg (by linarith)]
        exact hd2
      · rw [show α x - (α z - 1) = 1 - (α z - α x) by ring, abs_of_nonneg (by linarith)]
        exact hd2
      · exfalso; linarith
      · rw [show α x - α z = -(α z - α x) by ring, abs_neg, abs_of_nonneg (by linarith)]
        exact hd1
    · have habs_xz : |α x - α z| = α x - α z := abs_of_nonneg (by linarith)
      rw [habs_xz] at hd1 hd2
      rcases hβ_cases x with ⟨hbx, hx1⟩ | ⟨hbx, hx2⟩ | ⟨hbx, hx3a, hx3b⟩ <;>
        rcases hβ_cases z with ⟨hbz, hz1⟩ | ⟨hbz, hz2⟩ | ⟨hbz, hz3a, hz3b⟩ <;>
        rw [hbx, hbz]
      · rw [show α x - 1 - (α z - 1) = α x - α z by ring, abs_of_nonneg (by linarith)]
        exact hd1
      · rw [show α x - 1 - (α z + 1) = -((2 : ℝ) - (α x - α z)) by ring, abs_neg,
          abs_of_nonneg (by linarith)]
        linarith
      · rw [show α x - 1 - α z = -(1 - (α x - α z)) by ring, abs_neg, abs_of_nonneg (by linarith)]
        exact hd2
      · exfalso; linarith
      · rw [show α x + 1 - (α z + 1) = α x - α z by ring, abs_of_nonneg (by linarith)]
        exact hd1
      · exfalso; linarith
      · exfalso; linarith
      · rw [show α x - (α z + 1) = -(1 - (α x - α z)) by ring, abs_neg, abs_of_nonneg (by linarith)]
        exact hd2
      · rw [abs_of_nonneg (by linarith)]
        exact hd1
  let K : ι → ℝ := fun k => ‖∑ h ∈ range (2 * N), (e (α k - α j)) ^ h‖ ^ 2
  rw [← add_sum_erase J K hj]
  have hdiag : K j = 4 * (N : ℝ) ^ 2 := by
    have hsum : ∑ _h ∈ range (2 * N), (e (α j - α j)) ^ _h = ((2 * N : ℕ) : ℂ) := by
      simp [e_zero]
    dsimp only [K]
    rw [hsum, Complex.norm_natCast]
    push_cast
    ring
  let U := (J.erase j).filter (fun k => α j < β k)
  let L := (J.erase j).filter (fun k => β k ≤ α j)
  have hpart : ∑ k ∈ J.erase j, K k = (∑ k ∈ U, K k) + (∑ k ∈ L, K k) := by
    have h := sum_filter_add_sum_filter_not (J.erase j) (fun k => α j < β k) K
    simpa [U, L, not_lt] using h.symm
  have hK_le : ∀ k ∈ J.erase j, K k ≤ (N : ℝ) ^ 2 * ((1 : ℝ) / ((N : ℝ) * |β k - α j|) ^ 2) := by
    intro k hk
    obtain ⟨hk_ne, hkJ⟩ := mem_erase.mp hk
    have hsep_kj : 1 / (N : ℝ) ≤ |β k - α j| := by
      rw [← hβj]
      exact hβ_sep k hkJ j hj hk_ne
    have hpos : 0 < |β k - α j| := lt_of_lt_of_le (by positivity) hsep_kj
    have hfb := fejer_bound (2 * N) hpos (hβ_half k hkJ)
    dsimp only [K]
    simp_rw [← hβ_eq_e k]
    refine hfb.trans_eq ?_
    rw [mul_pow, sq_abs]
    field_simp
  have hU_sum : ∑ k ∈ U, K k ≤ 2 * (N : ℝ) ^ 2 := by
    have h1 : ∑ k ∈ U, K k ≤ (N : ℝ) ^ 2 * ∑ k ∈ U, (1 : ℝ) / ((N : ℝ) * (β k - α j)) ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hkE, hk_gt⟩ := mem_filter.mp hk
      have habs : |β k - α j| = β k - α j := abs_of_pos (sub_pos.mpr hk_gt)
      simpa [habs] using hK_le k hkE
    have hray : ∑ k ∈ U, (1 : ℝ) / ((N : ℝ) * (β k - α j)) ^ 2 ≤ 2 := by
      refine ray_sum_le U N (fun k => (N : ℝ) * (β k - α j)) ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkE, hk_gt⟩ := mem_filter.mp hk
        obtain ⟨hk_ne, hkJ⟩ := mem_erase.mp hkE
        have h := hβ_sep k hkJ j hj hk_ne
        rw [hβj, abs_of_pos (sub_pos.mpr hk_gt)] at h
        linarith [(div_le_iff₀ hN_pos).mp h]
      · intro k hk
        obtain ⟨hkE, _⟩ := mem_filter.mp hk
        have hh := (abs_le.mp (hβ_half k (mem_erase.mp hkE).2)).2
        nlinarith
      · intro x hx z hz hne
        have hxJ := (mem_erase.mp (mem_filter.mp hx).1).2
        have hzJ := (mem_erase.mp (mem_filter.mp hz).1).2
        have h := hβ_sep x hxJ z hzJ hne
        have hmul : (N : ℝ) * (β x - α j) - (N : ℝ) * (β z - α j) = (N : ℝ) * (β x - β z) := by ring
        rw [hmul, abs_mul, abs_of_pos hN_pos]
        linarith [(div_le_iff₀ hN_pos).mp h]
    nlinarith
  have hL_sum : ∑ k ∈ L, K k ≤ 2 * (N : ℝ) ^ 2 := by
    have h1 : ∑ k ∈ L, K k ≤ (N : ℝ) ^ 2 * ∑ k ∈ L, (1 : ℝ) / ((N : ℝ) * (α j - β k)) ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hkE, hk_le⟩ := mem_filter.mp hk
      have habs : |β k - α j| = α j - β k := by
        rw [abs_of_nonpos (sub_nonpos.mpr hk_le)]
        ring
      simpa [habs] using hK_le k hkE
    have hray : ∑ k ∈ L, (1 : ℝ) / ((N : ℝ) * (α j - β k)) ^ 2 ≤ 2 := by
      refine ray_sum_le L N (fun k => (N : ℝ) * (α j - β k)) ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkE, hk_le⟩ := mem_filter.mp hk
        obtain ⟨hk_ne, hkJ⟩ := mem_erase.mp hkE
        have h := hβ_sep k hkJ j hj hk_ne
        rw [hβj] at h
        have habs : |β k - α j| = α j - β k := by
          rw [abs_of_nonpos (sub_nonpos.mpr hk_le)]
          ring
        rw [habs] at h
        linarith [(div_le_iff₀ hN_pos).mp h]
      · intro k hk
        obtain ⟨hkE, _⟩ := mem_filter.mp hk
        have hh := (abs_le.mp (hβ_half k (mem_erase.mp hkE).2)).1
        nlinarith
      · intro x hx z hz hne
        have hxJ := (mem_erase.mp (mem_filter.mp hx).1).2
        have hzJ := (mem_erase.mp (mem_filter.mp hz).1).2
        have h := hβ_sep x hxJ z hzJ hne
        have hmul : (N : ℝ) * (α j - β x) - (N : ℝ) * (α j - β z) = -((N : ℝ) * (β x - β z)) := by ring
        rw [hmul, abs_neg, abs_mul, abs_of_pos hN_pos]
        linarith [(div_le_iff₀ hN_pos).mp h]
    nlinarith
  rw [hdiag, hpart]
  linarith

private lemma general_large_sieve {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (N : ℕ) (hN : 0 < N) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (α : ι → ℝ)
    (h01 : ∀ x ∈ J, 0 < α x ∧ α x < 1)
    (hsep : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → 1 / (N : ℝ) ≤ |α x - α y| ∧ 1 / (N : ℝ) ≤ 1 - |α x - α y|) :
    ∑ j ∈ J, ‖∑ a ∈ A, e (α j * a)‖ ^ 2 ≤ 8 * (N : ℝ) * A.card := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  let v : ι → ℂ := fun j => ∑ a ∈ A, e (α j * a)
  let S : ℝ := ∑ j ∈ J, ‖v j‖ ^ 2
  change S ≤ 8 * (N : ℝ) * A.card
  by_cases hS0 : S ≤ 0
  · refine hS0.trans (by positivity)
  push Not at hS0
  let g : ℕ → ℂ := fun a => ∑ j ∈ J, conj (v j) * e (α j * a)
  have hS_complex : ((S : ℝ) : ℂ) = ∑ a ∈ A, g a := by
    dsimp only [S, g]
    push_cast
    have hv : ∀ j ∈ J, (‖v j‖ : ℂ) ^ 2 = conj (v j) * v j := by
      intro j _
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [sum_congr rfl hv]
    simp only [v, mul_sum]
    exact sum_comm
  have hS_le_sum : S ≤ ∑ a ∈ A, ‖g a‖ := by
    have h1 : S = ‖((S : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hS0.le]
    rw [h1, hS_complex]
    exact norm_sum_le A g
  have hcs : (∑ a ∈ A, ‖g a‖) ^ 2 ≤ (A.card : ℝ) * ∑ a ∈ A, ‖g a‖ ^ 2 := by
    have h0 : 0 ≤ ∑ a ∈ A, ∑ b ∈ A, (‖g a‖ - ‖g b‖) ^ 2 :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ∑ a ∈ A, ∑ b ∈ A, (‖g a‖ - ‖g b‖) ^ 2 =
        2 * (A.card : ℝ) * (∑ a ∈ A, ‖g a‖ ^ 2) - 2 * (∑ a ∈ A, ‖g a‖) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
        ← mul_sum, ← sum_mul]
      ring
    linarith
  have hA_le_Icc : ∑ a ∈ A, ‖g a‖ ^ 2 ≤ ∑ a ∈ Icc 1 N, ‖g a‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hA fun _ _ _ => sq_nonneg _
  let G : ℕ × ℕ → ℝ := fun p =>
    ‖∑ j ∈ J, conj (v j) * e (α j * p.1) * conj (e (α j * p.2))‖ ^ 2
  have hfiber : (N : ℝ) * ∑ a ∈ Icc 1 N, ‖g a‖ ^ 2 ≤
      ∑ p ∈ range (2 * N) ×ˢ range (2 * N), G p := by
    let Q : Finset (ℕ × ℕ) := Icc 1 N ×ˢ range N
    let φ : ℕ × ℕ → ℕ × ℕ := fun q => (q.2 + q.1, q.2)
    have hφ_inj : Set.InjOn φ (Q : Set (ℕ × ℕ)) := by
      rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [φ, Prod.mk.injEq] at h
      ext <;> omega
    have hφ_sub : Q.image φ ⊆ range (2 * N) ×ˢ range (2 * N) := by
      intro p hp
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hp
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
      have hbN := mem_range.mp hb
      dsimp only [φ]
      exact mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
    have hG_φ : ∀ q ∈ Q, G (φ q) = ‖g q.1‖ ^ 2 := by
      rintro ⟨a, b⟩ _
      dsimp only [G, φ, g]
      congr 2
      refine sum_congr rfl fun j _ => ?_
      have hadd : e (α j * ((b + a : ℕ) : ℝ)) * conj (e (α j * b)) = e (α j * a) := by
        have h1 : α j * ((b + a : ℕ) : ℝ) = α j * a + α j * b := by push_cast; ring
        rw [h1, ← e_sub, add_sub_cancel_right]
      rw [mul_assoc]
      congr 1
    calc (N : ℝ) * ∑ a ∈ Icc 1 N, ‖g a‖ ^ 2
        = ∑ a ∈ Icc 1 N, ∑ _b ∈ range N, ‖g a‖ ^ 2 := by
            simp [sum_const, nsmul_eq_mul, mul_sum]
      _ = ∑ q ∈ Q, ‖g q.1‖ ^ 2 := by
            dsimp only [Q]
            rw [sum_product]
      _ = ∑ q ∈ Q, G (φ q) := sum_congr rfl fun q hq => (hG_φ q hq).symm
      _ = ∑ p ∈ Q.image φ, G p := (sum_image hφ_inj).symm
      _ ≤ ∑ p ∈ range (2 * N) ×ˢ range (2 * N), G p :=
          sum_le_sum_of_subset_of_nonneg hφ_sub fun _ _ _ => sq_nonneg _
  let K : ι → ι → ℝ := fun j k => ‖∑ h ∈ range (2 * N), (e (α k - α j)) ^ h‖ ^ 2
  have hK_symm : ∀ j k, K j k = K k j := by
    intro j k
    dsimp only [K]
    have hconj : ∑ h ∈ range (2 * N), (e (α j - α k)) ^ h =
        conj (∑ h ∈ range (2 * N), (e (α k - α j)) ^ h) := by
      rw [map_sum]
      refine sum_congr rfl fun h _ => ?_
      rw [map_pow, ← e_neg, neg_sub]
    rw [hconj, RCLike.norm_conj]
  have hdouble_expand : ∑ p ∈ range (2 * N) ×ˢ range (2 * N), G p ≤
      ∑ j ∈ J, ∑ k ∈ J, ‖v j‖ * ‖v k‖ * K j k := by
    have hG_re : ∀ p : ℕ × ℕ, G p =
        (∑ j ∈ J, ∑ k ∈ J, v j * conj (v k) *
          (e (α k - α j)) ^ p.1 * conj ((e (α k - α j)) ^ p.2)).re := by
      intro p
      dsimp only [G]
      have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (conj z * z).re := by
        intro z
        rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [hnorm]
      congr 1
      rw [map_sum, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      have h1 : ∀ m : ℕ, conj (e (α j * m)) * e (α k * m) = (e (α k - α j)) ^ m := by
        intro m
        rw [← e_nat_mul, mul_comm (conj _), ← e_sub]
        congr 1
        ring
      have h2 : e (α j * p.2) * conj (e (α k * p.2)) = conj ((e (α k - α j)) ^ p.2) := by
        rw [← h1 p.2]
        simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      calc v j * conj (e (α j * p.1)) * e (α j * p.2) *
            (conj (v k) * e (α k * p.1) * conj (e (α k * p.2)))
          = v j * conj (v k) * (conj (e (α j * p.1)) * e (α k * p.1)) *
              (e (α j * p.2) * conj (e (α k * p.2))) := by ring
        _ = v j * conj (v k) * (e (α k - α j)) ^ p.1 * conj ((e (α k - α j)) ^ p.2) := by
              rw [h1 p.1, h2]
    simp_rw [hG_re]
    rw [sum_product]
    simp_rw [← Complex.re_sum]
    have hswap : (∑ h₁ ∈ range (2 * N), ∑ h₂ ∈ range (2 * N),
        ∑ j ∈ J, ∑ k ∈ J, v j * conj (v k) *
          (e (α k - α j)) ^ h₁ * conj ((e (α k - α j)) ^ h₂)) =
        ∑ j ∈ J, ∑ k ∈ J, v j * conj (v k) * ((K j k : ℝ) : ℂ) := by
      rw [sum_comm]
      conv_lhs =>
        arg 2
        ext h₂
        rw [sum_comm]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      conv_lhs =>
        arg 2
        ext h₂
        rw [sum_comm]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm]
      have hprod : ∀ (c z : ℂ),
          (∑ h₁ ∈ range (2 * N), ∑ h₂ ∈ range (2 * N), c * z ^ h₁ * conj (z ^ h₂)) =
          c * ((∑ h₁ ∈ range (2 * N), z ^ h₁) * conj (∑ h₂ ∈ range (2 * N), z ^ h₂)) := by
        intro c z
        rw [map_sum, sum_mul, mul_sum]
        refine sum_congr rfl fun h₁ _ => ?_
        rw [mul_sum, mul_sum]
        exact sum_congr rfl fun h₂ _ => by ring
      rw [hprod (v j * conj (v k)) (e (α k - α j))]
      congr 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hswap, Complex.re_sum]
    refine sum_le_sum fun j _ => ?_
    rw [Complex.re_sum]
    refine sum_le_sum fun k _ => ?_
    calc (v j * conj (v k) * (K j k : ℂ)).re
        ≤ ‖v j * conj (v k) * (K j k : ℂ)‖ := Complex.re_le_norm _
      _ = ‖v j‖ * ‖v k‖ * K j k := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
            Real.norm_of_nonneg (sq_nonneg _)]
  have hschur : ∑ j ∈ J, ∑ k ∈ J, ‖v j‖ * ‖v k‖ * K j k ≤ 8 * (N : ℝ) ^ 2 * S := by
    have h2 : 2 * ∑ j ∈ J, ∑ k ∈ J, ‖v j‖ * ‖v k‖ * K j k ≤
        ∑ j ∈ J, ∑ k ∈ J, (‖v j‖ ^ 2 + ‖v k‖ ^ 2) * K j k := by
      rw [mul_sum]
      refine sum_le_sum fun j _ => ?_
      rw [mul_sum]
      refine sum_le_sum fun k _ => ?_
      have hnn : 0 ≤ K j k := sq_nonneg _
      have hab : 2 * (‖v j‖ * ‖v k‖) ≤ ‖v j‖ ^ 2 + ‖v k‖ ^ 2 := by
        nlinarith [sq_nonneg (‖v j‖ - ‖v k‖)]
      nlinarith
    have hsymm_sum : ∑ j ∈ J, ∑ k ∈ J, ‖v k‖ ^ 2 * K j k =
        ∑ j ∈ J, ∑ k ∈ J, ‖v j‖ ^ 2 * K j k := by
      rw [sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
      rw [hK_symm]
    have hsplit_sum : ∑ j ∈ J, ∑ k ∈ J, (‖v j‖ ^ 2 + ‖v k‖ ^ 2) * K j k =
        2 * ∑ j ∈ J, ‖v j‖ ^ 2 * (∑ k ∈ J, K j k) := by
      simp only [add_mul, sum_add_distrib]
      rw [hsymm_sum]
      simp only [← mul_sum]
      ring
    have hrow : ∑ j ∈ J, ‖v j‖ ^ 2 * (∑ k ∈ J, K j k) ≤ 8 * (N : ℝ) ^ 2 * S := by
      dsimp only [S]
      rw [mul_sum]
      refine sum_le_sum fun j hj => ?_
      have hr := row_kernel_sum J N hN α h01 hsep hj
      nlinarith [sq_nonneg ‖v j‖]
    linarith
  have hchain1 : (N : ℝ) * ∑ a ∈ Icc 1 N, ‖g a‖ ^ 2 ≤ 8 * (N : ℝ) ^ 2 * S :=
    hfiber.trans (hdouble_expand.trans hschur)
  have hchain2 : ∑ a ∈ Icc 1 N, ‖g a‖ ^ 2 ≤ 8 * (N : ℝ) * S := by
    nlinarith
  have hS_sq : S ^ 2 ≤ 8 * (N : ℝ) * (A.card : ℝ) * S := by
    have h1 : S ^ 2 ≤ (∑ a ∈ A, ‖g a‖) ^ 2 := pow_le_pow_left₀ hS0.le hS_le_sum 2
    have h2 : (∑ a ∈ A, ‖g a‖) ^ 2 ≤ (A.card : ℝ) * (8 * (N : ℝ) * S) := by
      refine hcs.trans ?_
      exact mul_le_mul_of_nonneg_left (hA_le_Icc.trans hchain2) (Nat.cast_nonneg _)
    linarith
  nlinarith

private lemma reduced_pair {N X p r : ℕ} (hpX : p ≤ X) (hp : p.Prime) (hXN : X * X ≤ N)
    (hr_lt : r < p * p) (hr_ne : r ≠ 0) (hcond : p ^ 4 ≤ N ∨ p ∣ r) :
    ∃ u q : ℕ, 0 < u ∧ u < q ∧ q * q ≤ N ∧ (q = p ∨ q = p * p ∧ ¬ p ∣ u) ∧
      ((r : ℝ) / ((p * p : ℕ) : ℝ)) = (u : ℝ) / (q : ℝ) := by
  by_cases hdvd : p ∣ r
  · obtain ⟨u, rfl⟩ := hdvd
    have hu_pos : 0 < u := by
      rcases Nat.eq_zero_or_pos u with rfl | h
      · simp at hr_ne
      · exact h
    have hu_lt : u < p := by nlinarith
    refine ⟨u, p, hu_pos, hu_lt, (Nat.mul_le_mul hpX hpX).trans hXN, Or.inl rfl, ?_⟩
    have hp_r : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    field_simp
  · have hp4 : p ^ 4 ≤ N := hcond.resolve_right hdvd
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_ne
    refine ⟨r, p * p, hr_pos, hr_lt, by nlinarith [show (p * p) * (p * p) = p ^ 4 by ring],
      Or.inr ⟨rfl, hdvd⟩, ?_⟩
    push_cast
    rfl

end OMA.LargeSieve1109

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1.H2 := by
  intro N X hN hXN A hA
  classical
  let P := (Finset.range (X + 1)).filter Nat.Prime
  let R : ℕ → Finset ℕ := fun p =>
    (Finset.range (p * p)).filter (fun r => r ≠ 0 ∧ (p ^ 4 ≤ N ∨ p ∣ r))
  let J : Finset (Σ _ : ℕ, ℕ) := P.sigma R
  let α : (Σ _ : ℕ, ℕ) → ℝ := fun x => (x.2 : ℝ) / ((x.1 * x.1 : ℕ) : ℝ)
  have hmemJ : ∀ x ∈ J, x.1 ≤ X ∧ x.1.Prime ∧ x.2 < x.1 * x.1 ∧ x.2 ≠ 0 ∧
      (x.1 ^ 4 ≤ N ∨ x.1 ∣ x.2) := by
    intro x hx
    obtain ⟨hpP, hrR⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hp_lt, hp_prime⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hr_lt, hr_ne, hcond⟩ := Finset.mem_filter.mp hrR
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_lt), hp_prime,
      Finset.mem_range.mp hr_lt, hr_ne, hcond⟩
  have h01 : ∀ x ∈ J, 0 < α x ∧ α x < 1 := by
    intro x hx
    obtain ⟨_, hp, hr_lt, hr_ne, _⟩ := hmemJ x hx
    have hpp : 0 < x.1 * x.1 := Nat.mul_pos hp.pos hp.pos
    have hr_pos : 0 < x.2 := Nat.pos_of_ne_zero hr_ne
    dsimp only [α]
    exact ⟨by positivity, (div_lt_one (by exact_mod_cast hpp)).mpr (by exact_mod_cast hr_lt)⟩
  have hsep : ∀ x ∈ J, ∀ y ∈ J, x ≠ y →
      1 / (N : ℝ) ≤ |α x - α y| ∧ 1 / (N : ℝ) ≤ 1 - |α x - α y| := by
    intro x hx y hy hne
    obtain ⟨hxX, hxp, hxr_lt, hxr_ne, hxcond⟩ := hmemJ x hx
    obtain ⟨hyX, hyp, hyr_lt, hyr_ne, hycond⟩ := hmemJ y hy
    obtain ⟨u₁, q₁, hu₁_pos, hu₁_lt, hq₁N, hq₁_form, hαx⟩ :=
      OMA.LargeSieve1109.reduced_pair hxX hxp hXN hxr_lt hxr_ne hxcond
    obtain ⟨u₂, q₂, hu₂_pos, hu₂_lt, hq₂N, hq₂_form, hαy⟩ :=
      OMA.LargeSieve1109.reduced_pair hyX hyp hXN hyr_lt hyr_ne hycond
    have hq₁_pos : 0 < q₁ := lt_trans hu₁_pos hu₁_lt
    have hq₂_pos : 0 < q₂ := lt_trans hu₂_pos hu₂_lt
    have hprod_le_N : q₁ * q₂ ≤ N := by nlinarith
    have hne_cross : u₁ * q₂ ≠ u₂ * q₁ := by
      intro heq
      by_cases hp_eq : x.1 = y.1
      · rcases x with ⟨px, rx⟩
        rcases y with ⟨py, ry⟩
        dsimp only at hp_eq hαx hαy hne
        subst hp_eq
        have hα_eq : α ⟨px, rx⟩ = α ⟨px, ry⟩ := by
          dsimp only [α]
          rw [hαx, hαy, div_eq_div_iff (by positivity) (by positivity)]
          exact_mod_cast heq
        dsimp only [α] at hα_eq
        have hpp_ne : ((px * px : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.mul_pos hxp.pos hxp.pos).ne'
        have hr_eq : (rx : ℝ) = (ry : ℝ) := (div_left_inj' hpp_ne).mp hα_eq
        have hr_nat : rx = ry := Nat.cast_injective hr_eq
        exact hne (by subst hr_nat; rfl)
      · have hnot_dvd_q₂ : ¬ x.1 ∣ q₂ := by
          have hcop : ¬ x.1 ∣ y.1 := fun hd => hp_eq ((Nat.prime_dvd_prime_iff_eq hxp hyp).mp hd)
          rcases hq₂_form with rfl | ⟨rfl, _⟩
          · exact hcop
          · exact fun hd => hcop ((hxp.dvd_mul.mp hd).elim id id)
        have hnot_dvd_u₁ : ¬ x.1 ∣ u₁ := by
          rcases hq₁_form with rfl | ⟨_, hnd⟩
          · exact Nat.not_dvd_of_pos_of_lt hu₁_pos hu₁_lt
          · exact hnd
        have hdvd_rhs : x.1 ∣ u₂ * q₁ := by
          rcases hq₁_form with rfl | ⟨rfl, _⟩
          · exact dvd_mul_left x.1 u₂
          · exact dvd_mul_of_dvd_right (dvd_mul_left x.1 x.1) u₂
        rw [← heq] at hdvd_rhs
        rcases hxp.dvd_mul.mp hdvd_rhs with h1 | h2
        · exact hnot_dvd_u₁ h1
        · exact hnot_dvd_q₂ h2
    have hdiff_ge1 : (1 : ℝ) ≤ |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)| := by
      rcases lt_or_gt_of_ne hne_cross with hlt | hgt
      · have h1 : ((u₁ * q₂ : ℕ) : ℝ) + 1 ≤ ((u₂ * q₁ : ℕ) : ℝ) := by exact_mod_cast hlt
        push_cast at h1
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have h1 : ((u₂ * q₁ : ℕ) : ℝ) + 1 ≤ ((u₁ * q₂ : ℕ) : ℝ) := by exact_mod_cast hgt
        push_cast at h1
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hq12_pos : (0 : ℝ) < (q₁ : ℝ) * (q₂ : ℝ) := by positivity
    have hq12_le_N : (q₁ : ℝ) * (q₂ : ℝ) ≤ N := by exact_mod_cast hprod_le_N
    have hα_diff : |α x - α y| = |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := by
      dsimp only [α]
      rw [hαx, hαy, div_sub_div _ _ (by positivity) (by positivity), abs_div, abs_of_pos hq12_pos, mul_comm (q₁ : ℝ) (u₂ : ℝ)]
    constructor
    · rw [hα_diff]
      calc 1 / (N : ℝ) ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) :=
            one_div_le_one_div_of_le hq12_pos hq12_le_N
        _ ≤ |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) :=
            div_le_div_of_nonneg_right hdiff_ge1 hq12_pos.le
    · have hu₁_hi : (u₁ : ℝ) + 1 ≤ q₁ := by exact_mod_cast hu₁_lt
      have hu₂_hi : (u₂ : ℝ) + 1 ≤ q₂ := by exact_mod_cast hu₂_lt
      have hu₁_lo : (1 : ℝ) ≤ u₁ := by exact_mod_cast hu₁_pos
      have hu₂_lo : (1 : ℝ) ≤ u₂ := by exact_mod_cast hu₂_pos
      have h1 : (u₁ : ℝ) * q₂ - (u₂ : ℝ) * q₁ ≤ (q₁ : ℝ) * q₂ - 1 := by nlinarith
      have h2 : (u₂ : ℝ) * q₁ - (u₁ : ℝ) * q₂ ≤ (q₁ : ℝ) * q₂ - 1 := by nlinarith
      have habs_hi : |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)| ≤ (q₁ : ℝ) * q₂ - 1 := by
        rw [abs_le]
        constructor <;> linarith
      rw [hα_diff]
      have h3 : 1 - |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) =
          ((q₁ : ℝ) * q₂ - |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)|) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
        field_simp
      rw [h3]
      calc 1 / (N : ℝ) ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) :=
            one_div_le_one_div_of_le hq12_pos hq12_le_N
        _ ≤ ((q₁ : ℝ) * q₂ - |(u₁ * q₂ : ℝ) - (u₂ * q₁ : ℝ)|) / ((q₁ : ℝ) * (q₂ : ℝ)) :=
            div_le_div_of_nonneg_right (by linarith) hq12_pos.le
  have hrewrite : (∑ p ∈ P, ∑ r ∈ R p,
      ‖∑ a ∈ A, (Complex.exp (2 * Real.pi * Complex.I / (p * p : ℕ))) ^ (a * r)‖ ^ 2) =
      ∑ x ∈ J, ‖∑ a ∈ A, OMA.LargeSieve1109.e (α x * a)‖ ^ 2 := by
    dsimp only [J]
    rw [Finset.sum_sigma']
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold OMA.LargeSieve1109.e
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp only [α]
    push_cast
    ring
  change (∑ p ∈ P, ∑ r ∈ R p,
      ‖∑ a ∈ A, (Complex.exp (2 * Real.pi * Complex.I / (p * p : ℕ))) ^ (a * r)‖ ^ 2) ≤
      100 * (N : ℝ) * A.card
  rw [hrewrite]
  have hmain := OMA.LargeSieve1109.general_large_sieve J N hN A hA α h01 hsep
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) * A.card := by positivity
  linarith
