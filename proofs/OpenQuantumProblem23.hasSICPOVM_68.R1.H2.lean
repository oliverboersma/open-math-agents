import OMAReductions.R_OpenQuantumProblem23_hasSICPOVM_68_R1
import Mathlib

-- Port of Yaoling Yang, SIC-POVMs exist in every dimension, Apache-2.0.
-- https://github.com/Hertaspace/sic-povm-lean/tree/e74571352233162adee70895903d82f8465fd054
-- Source modules are identified below. The mathematical argument is due to
-- Radchenko and Wheeler and to Appleby, Flammia and Kopp.
-- Credit: @marcusbuffett
-- SICLean.Defs
section
noncomputable section

open Matrix

namespace SICLean

def omega (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

def xi (d : ℕ) : ℂ := -Complex.exp (Real.pi * Complex.I / d)

def D (d : ℕ) (p : ℤ × ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
      xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((j : ℕ) : ℤ))
    else 0

def ov (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) : ℂ :=
  (A * (D d p)ᴴ).trace

def IsZeroLabel (d : ℕ) (p : ℤ × ℤ) : Prop :=
  (d : ℤ) ∣ p.1 ∧ (d : ℤ) ∣ p.2

instance (d : ℕ) : DecidablePred (IsZeroLabel d) :=
  fun p => inferInstanceAs (Decidable ((d : ℤ) ∣ p.1 ∧ (d : ℤ) ∣ p.2))

def rsicConst (d r : ℕ) : ℝ :=
  ((r : ℝ) * ((d : ℝ) - r)) / ((d : ℝ) ^ 2 - 1)

def IsRSIC (d r : ℕ) (P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  Function.Injective P ∧
  (∀ j, (P j).IsHermitian ∧ P j * P j = P j ∧ (P j).rank = r) ∧
  ∃ α : ℂ, Pairwise fun j k => (P j * P k).trace = α

def HasRSIC (d r : ℕ) : Prop :=
  ∃ P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsRSIC d r P

end SICLean
end
end

-- SICLean.Inputs
section
noncomputable section

open Matrix

namespace SICLean

structure IsGhost (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) : Prop where
  idem : G * G = G
  trace_eq : G.trace = r
  ov_mul_ov_neg : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
    ov d G p * ov d G (-p) = (rsicConst d r : ℂ)

def UnimodularFlip (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) (σ : ℂ →+* ℂ) : Prop :=
  ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p → Complex.normSq (σ (ov d G p)) = rsicConst d r

def GhostGaloisInput (d r : ℕ) : Prop :=
  ∃ G : Matrix (Fin d) (Fin d) ℂ, IsGhost d r G ∧ ∃ σ : ℂ →+* ℂ, UnimodularFlip d r G σ

end SICLean
end
end

-- SICLean.WHBasic
section
noncomputable section

open Matrix

namespace SICLean

variable {d : ℕ}

theorem omega_eq_xi_sq (d : ℕ) : omega d = xi d ^ 2 := by
  simp only [omega, xi, pow_two, neg_mul_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem xi_ne_zero (d : ℕ) : xi d ≠ 0 :=
  neg_ne_zero.mpr (Complex.exp_ne_zero _)

theorem fin_ext_of_label [NeZero d] {i j : Fin d}
    (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)) : i = j := by
  have hv : (ZMod.val ((i : ℕ) : ZMod d)) = (ZMod.val ((j : ℕ) : ZMod d)) := by
    rw [h]
  rw [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at hv
  exact Fin.val_injective hv

theorem exists_sub_of_label {d : ℕ} {i j : ℕ} {a : ℤ}
    (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (a : ZMod d)) :
    ∃ t : ℤ, (i : ℤ) = (j : ℤ) + a + (d : ℤ) * t := by
  have h' : (((i : ℤ) - (j : ℤ) - a : ℤ) : ZMod d) = 0 := by
    push_cast
    rw [h]
    ring
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  exact ⟨t, by linear_combination ht⟩

theorem omega_pow_d_of_ne_zero (d : ℕ) (hd : d ≠ 0) : omega d ^ (d : ℕ) = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [omega]
  rw [← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hd']
  exact Complex.exp_two_pi_mul_I

theorem xi_zpow_two_mul_d (d : ℕ) : xi d ^ ((2 * d : ℕ) : ℤ) = 1 := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [zpow_natCast, pow_mul, ← omega_eq_xi_sq]
    exact omega_pow_d_of_ne_zero d hd

theorem omega_zpow (d : ℕ) (z : ℤ) : omega d ^ z = xi d ^ (2 * z) := by
  rw [omega_eq_xi_sq]
  exact (zpow_mul (xi d) 2 z).symm

theorem xi_zpow_eq_of_dvd {d : ℕ} {e e' : ℤ} (h : ((2 * d : ℕ) : ℤ) ∣ (e - e')) :
    xi d ^ e = xi d ^ e' := by
  obtain ⟨n, hn⟩ := h
  have he : e = e' + ((2 * d : ℕ) : ℤ) * n := by linear_combination hn
  rw [he, zpow_add₀ (xi_ne_zero d), _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow,
    mul_one]

theorem star_xi (d : ℕ) : star (xi d) = (xi d)⁻¹ := by
  have hc : (starRingEnd ℂ) (Real.pi * Complex.I / (d : ℂ)) =
      -(Real.pi * Complex.I / (d : ℂ)) := by
    have hd : (starRingEnd ℂ) ((d : ℕ) : ℂ) = ((d : ℕ) : ℂ) := by simp
    rw [div_eq_mul_inv, (starRingEnd ℂ).map_mul, Complex.conj_inv, hd,
      (starRingEnd ℂ).map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hL : star (xi d) = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
    simp only [Complex.star_def, xi, map_neg, ← Complex.exp_conj, hc]
  have hR : (xi d)⁻¹ = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
    simp only [xi, ← neg_inv, ← Complex.exp_neg]
  rw [hL, hR]

theorem star_omega (d : ℕ) : star (omega d) = (omega d)⁻¹ := by
  rw [omega_eq_xi_sq, star_pow, star_xi, ← inv_pow]

def finIdx (d : ℕ) [NeZero d] (r : ZMod d) : Fin d :=
  ⟨ZMod.val r, ZMod.val_lt r⟩

theorem label_finIdx (d : ℕ) [NeZero d] (r : ZMod d) : ((finIdx d r : ℕ) : ZMod d) = r := by
  have h1 : (finIdx d r : ℕ) < d := ZMod.val_lt r
  refine ZMod.val_injective d ?_
  rw [ZMod.val_cast_of_lt h1]
  rfl

theorem sum_label_single (d : ℕ) [NeZero d] (F : Fin d → ℂ) (r : ZMod d) :
    ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0) = F (finIdx d r) := by
  have h : ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0)
      = (if ((finIdx d r : ℕ) : ZMod d) = r then F (finIdx d r) else 0) :=
    Fintype.sum_eq_single
      (f := fun k : Fin d => if ((k : ℕ) : ZMod d) = r then F k else 0)
      (finIdx d r) (by
        intro k hk
        rw [if_neg]
        intro hcon
        exact hk (fin_ext_of_label (hcon.trans (label_finIdx d r).symm)))
  rwa [if_pos (label_finIdx d r)] at h

theorem D_zero : D d (0, 0) = 1 := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  have hD : (D d (0, 0)) i j = if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) then 1 else 0 := by
    simp only [D]
    push_cast
    simp
  rw [hD, Matrix.one_apply]
  by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)
  · simp [fin_ext_of_label h]
  · rw [if_neg h, if_neg]
    intro hij
    exact h (by rw [hij])

theorem star_zpow (x : ℂ) (z : ℤ) : star (x ^ z) = (star x) ^ z := by
  cases z with
  | ofNat n =>
      show star (x ^ ((n : ℕ) : ℤ)) = (star x) ^ ((n : ℕ) : ℤ)
      rw [zpow_natCast, star_pow, zpow_natCast]
  | negSucc n =>
      rw [zpow_negSucc, Complex.star_def, Complex.conj_inv, ← Complex.star_def, star_pow,
        ← zpow_negSucc]

theorem conjTranspose_D (p : ℤ × ℤ) : (D d p)ᴴ = D d (-p) := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  simp only [Matrix.conjTranspose_apply, D]
  push_cast
  rw [show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl]
  have hnc : ∀ a : ℤ, ((-a : ℤ) : ZMod d) = (-(a : ZMod d)) := fun a => by push_cast; rfl
  rw [hnc]
  by_cases h : ((j : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos h, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (-(p.1) : ZMod d) by
      linear_combination -h)]
    obtain ⟨t, ht⟩ := exists_sub_of_label h
    rw [star_mul, star_zpow, star_zpow, star_omega, star_xi, _root_.inv_zpow, _root_.inv_zpow,
      ← _root_.zpow_neg, ← _root_.zpow_neg, omega_zpow, omega_zpow,
      ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
    push_cast
    linear_combination 2 * p.2 * ht
  · rw [if_neg h, star_zero, if_neg]
    intro hcon
    exact h (by linear_combination -hcon)

theorem D_mul_D (p q : ℤ × ℤ) :
    D d p * D d q = xi d ^ (p.2 * q.1 - p.1 * q.2) • D d (p + q) := by
  ext i j
  by_cases hd : d = 0
  · exact absurd i.isLt (by omega)
  haveI : NeZero d := ⟨hd⟩
  simp only [Matrix.mul_apply, D, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rw [show (p + q).1 = p.1 + q.1 from rfl, show (p + q).2 = p.2 + q.2 from rfl]
  have h2 : ((p.1 + q.1 : ℤ) : ZMod d) = ((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d) := by
    rw [Int.cast_add]
  rw [h2]
  by_cases h : ((i : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) + (((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d))
  · rw [if_pos h]
    have key : ∀ k : Fin d,
        (if ((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d) then
              xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) else 0) *
          (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
              xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ)) else 0)
          = (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
              xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
                (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))) else 0) := by
      intro k
      by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
      · rw [if_pos hk, if_pos hk, if_pos (show ((i : ℕ) : ZMod d) =
            ((k : ℕ) : ZMod d) + (p.1 : ZMod d) by
            linear_combination h - hk), mul_assoc]
      · rw [if_neg hk, if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl (fun k _ => key k),
      sum_label_single d (fun k => xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
        (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))))
        (((j : ℕ) : ZMod d) + (q.1 : ZMod d))]
    obtain ⟨t, ht⟩ := exists_sub_of_label (label_finIdx d (((j : ℕ) : ZMod d) + (q.1 : ZMod d)))
    rw [omega_zpow, omega_zpow, omega_zpow]
    simp only [mul_assoc]
    rw [← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
      ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
    push_cast
    linear_combination 2 * p.2 * ht
  · rw [if_neg h, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
    · rw [if_pos hk, if_neg (show ¬(((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d)) by
        intro hc
        exact h (by linear_combination hc + hk)), zero_mul]
    · rw [if_neg hk, mul_zero]

theorem D_mul_conjTranspose_D (p : ℤ × ℤ) : D d p * (D d p)ᴴ = 1 := by
  rw [conjTranspose_D, D_mul_D, show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl,
    show p.2 * (-(p.1)) - p.1 * (-(p.2)) = 0 from by ring,
    show p + -p = ((0 : ℤ), (0 : ℤ)) from (add_neg_cancel p).trans rfl,
    zpow_zero, one_smul, D_zero]

theorem D_add_smul (p v : ℤ × ℤ) :
    D d (p + (d : ℤ) • v) =
      xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * p.2) + (d : ℤ) ^ 2 * (v.1 * v.2)) • D d p := by
  by_cases hd : d = 0
  · subst hd
    ext i j
    exact absurd i.isLt (by omega)
  ext i j
  haveI : NeZero d := ⟨hd⟩
  simp only [D, Matrix.smul_apply, smul_eq_mul]
  rw [show (p + (d : ℤ) • v).1 = p.1 + (d : ℤ) * v.1 from rfl,
    show (p + (d : ℤ) • v).2 = p.2 + (d : ℤ) * v.2 from rfl]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero]
  by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos h, if_pos h]
    rw [omega_zpow, omega_zpow, ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
      ← zpow_add₀ (xi_ne_zero d)]
    refine xi_zpow_eq_of_dvd ⟨v.2 * ((j : ℕ) : ℤ), ?_⟩
    push_cast
    linear_combination (d : ℤ) * v.2 * ((j : ℕ) : ℤ)
  · rw [if_neg h, if_neg h, mul_zero]

theorem omega_zpow_dvd (d : ℕ) {z : ℤ} (h : (d : ℤ) ∣ z) : omega d ^ z = 1 := by
  by_cases hd : d = 0
  · subst hd
    have h1 : omega 0 = 1 := by
      rw [omega]
      simp
    rw [h1, _root_.one_zpow]
  · obtain ⟨c, hc⟩ := h
    rw [hc, _root_.zpow_mul, zpow_natCast, omega_pow_d_of_ne_zero d hd, _root_.one_zpow]

theorem omega_exp (d : ℕ) (z : ℤ) :
    omega d ^ z = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (d : ℂ)) := by
  cases z with
  | ofNat n =>
      show omega d ^ ((n : ℕ) : ℤ) = Complex.exp (2 * ↑Real.pi * Complex.I * ((n : ℕ) : ℂ) / ↑d)
      rw [zpow_natCast]
      simp only [omega]
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
  | negSucc n =>
      rw [zpow_negSucc]
      simp only [omega]
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring

theorem omega_ne_one_of_not_dvd [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) : omega d ^ a ≠ 1 := by
  intro h
  apply ha
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (d : ℂ)) = 1 := by
    rw [← omega_exp d a, h]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have h2c : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2c hπ) Complex.I_ne_zero
  have h2 : (2 * Real.pi * Complex.I : ℂ) * (a : ℂ)
      = (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) * (d : ℂ)) := by
    have h3 := (div_eq_iff hd0).mp hk
    linear_combination h3
  have h4 : (a : ℂ) = ((k * (d : ℕ) : ℤ) : ℂ) := by
    have := mul_left_cancel₀ hpi h2
    push_cast
    push_cast at this
    linear_combination this
  exact ⟨k, (Int.cast_injective h4).trans (mul_comm _ _)⟩

theorem sum_omega_pow_eq_zero [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) :
    ∑ i : Fin d, omega d ^ (a * ((i : ℕ) : ℤ)) = 0 := by
  have h1 : omega d ^ a ≠ 1 := omega_ne_one_of_not_dvd ha
  rw [Fin.sum_univ_eq_sum_range (fun k => omega d ^ (a * ((k : ℕ) : ℤ))) d]
  have hterm : ∀ i ∈ Finset.range d, omega d ^ (a * ((i : ℕ) : ℤ)) = (omega d ^ a) ^ i := by
    intro i _
    rw [_root_.zpow_mul, zpow_natCast]
  have h5 : (omega d ^ a) ^ (d : ℕ) = omega d ^ (a * ((d : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
  rw [Finset.sum_congr rfl (fun i hi => hterm i hi), geom_sum_eq h1, h5, mul_comm,
    omega_zpow_dvd d ⟨a, rfl⟩]
  ring

theorem trace_D [NeZero d] (p : ℤ × ℤ) :
    (D d p).trace = if IsZeroLabel d p then (d : ℂ) * xi d ^ (p.1 * p.2) else 0 := by
  have htr : (D d p).trace = ∑ i, (D d p) i i := by
    show ∑ i, Matrix.diag (D d p) i = ∑ i, (D d p) i i
    rw [Finset.sum_congr rfl (fun i _ => Matrix.diag_apply (D d p) i)]
  rw [htr]
  by_cases h1 : (d : ℤ) ∣ p.1
  · have hp1 : ((p.1 : ℤ) : ZMod d) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mpr h1
    have entry : ∀ i : Fin d, (D d p) i i = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) := by
      intro i
      show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
          xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0)
        = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
      rw [hp1, add_zero, if_pos rfl]
    rw [Finset.sum_congr rfl (fun i _ => entry i)]
    by_cases h2 : (d : ℤ) ∣ p.2
    · rw [if_pos ⟨h1, h2⟩]
      obtain ⟨c, hc⟩ := h2
      have homega : ∀ i : Fin d, omega d ^ (p.2 * ((i : ℕ) : ℤ)) = 1 := by
        intro i
        exact omega_zpow_dvd d ⟨c * (i : ℕ), by
          push_cast
          linear_combination ((i : ℕ) : ℤ) * hc⟩
      simp_rw [homega, mul_one]
      simp
    · have hmc : ∀ i : Fin d, xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
          = omega d ^ (p.2 * ((i : ℕ) : ℤ)) * xi d ^ (p.1 * p.2) := fun _ => mul_comm _ _
      rw [if_neg (fun hc => h2 hc.2), Finset.sum_congr rfl (fun i _ => hmc i),
        ← Finset.sum_mul, sum_omega_pow_eq_zero h2, zero_mul]
  · have hp1 : ¬ (((p.1 : ℤ) : ZMod d) = 0) := fun hc => h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mp hc)
    have entry : ∀ i : Fin d, (D d p) i i = 0 := by
      intro i
      show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
          xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0) = 0
      rw [if_neg]
      intro h
      exact hp1 (show ((p.1 : ℤ) : ZMod d) = (0 : ZMod d) from by linear_combination -h)
    rw [Finset.sum_congr rfl (fun i _ => entry i), Finset.sum_const_zero, if_neg (fun hc => h1 hc.1)]

theorem omega_ne_zero (d : ℕ) : omega d ≠ 0 := by
  show Complex.exp _ ≠ 0
  exact Complex.exp_ne_zero _

theorem sum_omega_symplectic [NeZero d] (u : ℤ × ℤ) (hu : ¬ IsZeroLabel d u) :
    ∑ s : Fin d × Fin d, omega d ^ (u.2 * ((s.1 : ℕ) : ℤ) - u.1 * ((s.2 : ℕ) : ℤ)) = 0 := by
  have hsplit : ∀ a b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
      = omega d ^ (u.2 * ((a : ℕ) : ℤ)) * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) := by
    intro a b
    rw [zpow_sub₀ (omega_ne_zero d), div_eq_mul_inv, ← _root_.zpow_neg, ← neg_mul]
  by_cases h2 : (d : ℤ) ∣ u.2
  · have h1 : ¬ ((d : ℤ) ∣ u.1) := fun hc => hu ⟨hc, h2⟩
    have h1n : ¬ ((d : ℤ) ∣ (-u.1)) := fun hc => h1 (dvd_neg.mp hc)
    rw [Fintype.sum_prod_type' (fun a b : Fin d => omega d ^ (u.2 * ((a : ℕ) : ℤ)
      - u.1 * ((b : ℕ) : ℤ)))]
    refine Finset.sum_eq_zero ?_
    intro a _
    have hbeta : ∑ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
        = ∑ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ))
          * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun b _ => hsplit a b)
    have hmc : ∀ b : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ)) * omega d ^ ((-u.1) * ((b : ℕ) : ℤ))
        = omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) * omega d ^ (u.2 * ((a : ℕ) : ℤ)) :=
      fun _ => mul_comm _ _
    rw [hbeta, Finset.sum_congr rfl (fun b _ => hmc b), ← Finset.sum_mul,
      sum_omega_pow_eq_zero h1n, zero_mul]
  · rw [Fintype.sum_prod_type' (fun a b : Fin d => omega d ^ (u.2 * ((a : ℕ) : ℤ)
      - u.1 * ((b : ℕ) : ℤ))), Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro b _
    have hbeta : ∑ a : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ) - u.1 * ((b : ℕ) : ℤ))
        = ∑ a : Fin d, omega d ^ (u.2 * ((a : ℕ) : ℤ))
          * omega d ^ ((-u.1) * ((b : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun a _ => hsplit a b)
    rw [hbeta, ← Finset.sum_mul, sum_omega_pow_eq_zero h2, zero_mul]

theorem eq_sum_ov_smul_D [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) :
    A = (d : ℂ)⁻¹ • ∑ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) • D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) := by
  ext i j

  have hDxy : ∀ x y : Fin d, (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j
      = (if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d) then
          xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ)) * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))
        else 0) := by
    intro x y
    show (if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (((x : ℕ) : ℤ) : ZMod d) then
        xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ))
          * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)) else 0) = _
    push_cast
    rfl

  have hov : ∀ a b : Fin d, ov d A (((a : ℕ) : ℤ), ((b : ℕ) : ℤ))
      = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
        * ∑ s : Fin d, omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))) := by
    intro a b
    have hDt : (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ
        = D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) := by
      rw [conjTranspose_D, show (-(((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))
        = (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) from rfl]
    show (A * (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ).trace = _
    rw [hDt]
    have h1 : ∀ s : Fin d, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s
        = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
          * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)))) := by
      intro s
      rw [Matrix.diag_apply, Matrix.mul_apply]
      have hD : ∀ k : Fin d, (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
          = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
            * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                (1 : ℂ) else 0)) := by
        intro k
        simp only [D]
        push_cast
        rw [neg_mul_neg]
        by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ZMod d))
        · rw [if_pos hc, if_pos hc, mul_one]
        · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
      have hpull : ∀ k : Fin d, A s k * (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
          = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
            * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                A s k else 0)) := by
        intro k
        rw [hD k]
        by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)
        · rw [if_pos hc, if_pos hc, mul_one]
          ring
        · rw [if_neg hc, if_neg hc]
          ring
      rw [Finset.sum_congr rfl (fun k _ => hpull k), ← Finset.mul_sum,
        Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_zero]),
        sum_label_single d (fun k => omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ)) * A s k)
          (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))]
    show (∑ s, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s) = _
    rw [Finset.sum_congr rfl (fun s _ => h1 s), ← Finset.mul_sum]

  set r : Fin d := finIdx d (((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d)) with hrdef
  have hr : ((r : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d) := label_finIdx d _
  have hsum : ∑ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))
        * (D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) i j = (d : ℂ) * A i j := by
    rw [Fintype.sum_prod_type' (fun x y : Fin d =>
      ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ)) * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j)]
    have hzero : ∀ x : Fin d, x ≠ r → ∑ y : Fin d,
        (ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))
          * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j) = 0 := by
      intro x hx
      refine Finset.sum_eq_zero ?_
      intro y _
      rw [hDxy x y, if_neg (show ¬(((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d)) by
        intro hcon
        exact hx (fin_ext_of_label (show ((x : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) by
          rw [hr]
          linear_combination -hcon))), mul_zero]
    rw [Fintype.sum_eq_single r hzero,
      Finset.sum_congr rfl (fun y _ => by
        rw [hDxy r y, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((r : ℕ) : ZMod d) by
          linear_combination -hr), hov r y])]

    have hph : ∀ y s : Fin d, xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
          * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
            * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))))
        = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)) := by
      intro y s
      rw [omega_zpow, omega_zpow, omega_zpow,
        ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
      refine xi_zpow_eq_of_dvd (⟨0, ?_⟩ : ((2 * d : ℕ) : ℤ) ∣ _)
      push_cast
      ring
    have htaux : ∀ y s : Fin d,
        (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))))
          * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
        = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
      intro y s
      rw [mul_assoc,
        mul_right_comm (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ)))
          (A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
          (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))),
        ← mul_assoc, hph y s]
    have hterm : ∀ y : Fin d,
        (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * ∑ s' : Fin d, omega d ^ (-((y : ℕ) : ℤ) * ((s' : ℕ) : ℤ))
              * A s' (finIdx d (((s' : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
          * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
        = ∑ s : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
      intro y
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun s _ => htaux y s)]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_comm]
    have hpull2 : ∀ s : Fin d,
        ∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))
        = (∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)))
          * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) :=
      fun s => (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl (fun s _ => hpull2 s)]

    have hinner : ∀ s : Fin d, ∑ y : Fin d,
        omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
        = if s = i then (d : ℂ) else 0 := by
      intro s
      by_cases hs : s = i
      · rw [hs]
        have hdvd : (d : ℤ) ∣ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) + ((r : ℕ) : ℤ)) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [hr]
          ring
        rw [Finset.sum_congr rfl (fun y _ => omega_zpow_dvd d
          (dvd_mul_of_dvd_left hdvd _))]
        simp
      · have hnd : ¬((d : ℤ) ∣ (((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ))) := by
          intro hc
          have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
          push_cast at h0
          rw [hr] at h0
          exact hs (fin_ext_of_label (show ((s : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) by
            linear_combination -h0))
        rw [sum_omega_pow_eq_zero hnd, if_neg hs]
    rw [Finset.sum_congr rfl (fun s _ => by rw [hinner s, ite_mul, zero_mul])]
    rw [Fintype.sum_eq_single i (fun s hs => by rw [if_neg hs]),
      if_pos rfl]
    have hkj : finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) = j :=
      fin_ext_of_label (show ((j : ℕ) : ZMod d)
          = ((finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) : ℕ) : ZMod d) from by
        rw [label_finIdx]
        push_cast
        linear_combination hr).symm
    rw [hkj]

  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hsum, inv_mul_cancel_left₀ (by exact_mod_cast (NeZero.ne d) : (d : ℂ) ≠ 0)]

theorem exists_map_D [NeZero d] (σ : ℂ →+* ℂ) :
    ∃ k : ℤ, IsCoprime k (d : ℤ) ∧ ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2) := by
  have h2d : (2 * d : ℕ) ≠ 0 := fun h => NeZero.ne d (by simpa using h)
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) (2 * d) :=
    Complex.isPrimitiveRoot_exp (2 * d) h2d
  have he : Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))
      = Complex.exp (Real.pi * Complex.I / d) := by
    congr 1
    have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    field_simp [hd]
    push_cast
    ring
  have hinj : Function.Injective σ := RingHom.injective σ
  have hσprim : IsPrimitiveRoot (σ (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)))) (2 * d) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := σ.toMonoidHom) hinj).mpr hprim
  obtain ⟨m, _, hm⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim hσprim.pow_eq_one
  have hcop : Nat.Coprime m (2 * d) := by
    refine (hprim.pow_iff_coprime (Nat.pos_of_ne_zero h2d) m).mp ?_
    rw [hm]
    exact hσprim
  have h2m : ¬ 2 ∣ m := by
    intro h2m
    have hg : 2 ∣ Nat.gcd m (2 * d) := Nat.dvd_gcd h2m ⟨d, by ring⟩
    rw [show Nat.gcd m (2 * d) = 1 from hcop] at hg
    norm_num at hg
  have hneg1 : (-1 : ℂ) ^ m = -1 := by
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact absurd (by rw [ht]; exact ⟨t, by ring⟩) h2m
    · exact Odd.neg_one_pow ⟨t, ht⟩
  refine ⟨(m : ℤ), (Nat.Coprime.coprime_mul_left_right hcop).cast, ?_⟩
  intro p
  ext i j
  simp only [Matrix.map_apply, D]
  by_cases hc : (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d)
  · rw [if_pos hc, if_pos hc]
    have hw : Complex.exp (2 * Real.pi * Complex.I / d)
        = Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ (2 : ℕ) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
      field_simp [hd]
      push_cast
      ring
    have hx : σ (xi d) = xi d ^ ((m : ℕ) : ℤ) := by
      show σ (-Complex.exp (Real.pi * Complex.I / d))
        = (-Complex.exp (Real.pi * Complex.I / d)) ^ ((m : ℕ) : ℤ)
      rw [map_neg, ← he, ← hm]
      rw [show (-Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) ^ ((m : ℕ) : ℤ)
          = (-1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ m from by
        rw [neg_eq_neg_one_mul, mul_zpow, zpow_natCast, zpow_natCast, hneg1]]
      rw [neg_one_mul]
    have hw' : σ (omega d) = omega d ^ ((m : ℕ) : ℤ) := by
      show σ (Complex.exp (2 * Real.pi * Complex.I / d))
        = Complex.exp (2 * Real.pi * Complex.I / d) ^ ((m : ℕ) : ℤ)
      rw [hw, map_pow, ← hm, ← _root_.pow_mul, _root_.zpow_natCast, ← _root_.pow_mul,
        Nat.mul_comm m 2]
    rw [map_mul, map_zpow₀ σ (xi d) (p.1 * p.2), map_zpow₀ σ (omega d) (p.2 * ((j : ℕ) : ℤ)),
      hx, hw', ← _root_.zpow_mul, ← _root_.zpow_mul]
    congr 1
    · congr 1
      ring
    · congr 1
      ring
  · rw [if_neg hc, if_neg hc]
    exact map_zero σ

theorem rank_eq_trace_of_idem (A : Matrix (Fin d) (Fin d) ℂ) (hA : A * A = A) :
    ((A.rank : ℕ) : ℂ) = A.trace := by
  have he : IsIdempotentElem A.mulVecLin := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hA]
  have htrL : A.trace = LinearMap.trace ℂ (Fin d → ℂ) A.mulVecLin := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
    congr 1
    ext i j
    simp [Matrix.mulVecLin, LinearMap.toMatrix]
  have hr : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
    rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))]
    rfl
  have hp : LinearMap.IsProj (LinearMap.range A.mulVecLin) A.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range A.mulVecLin he
  rw [htrL, LinearMap.IsProj.trace hp, ← hr]

theorem exists_unit_of_rank_one (A : Matrix (Fin d) (Fin d) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (h1 : A.rank = 1) :
    ∃ ψ : Fin d → ℂ, ∑ i, Complex.normSq (ψ i) = 1 ∧ ∀ i j, A i j = ψ i * star (ψ j) := by
  have hcj : ∀ k l, A l k = star (A k l) := fun k l => by
    have h1' : Matrix.conjTranspose A l k = A l k := by rw [show Matrix.conjTranspose A = A from hH]
    rw [Matrix.conjTranspose_apply] at h1'
    exact h1'.symm
  have htr : (1 : ℂ) = A.trace := by
    have h2 := rank_eq_trace_of_idem A hA
    rw [h1] at h2
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k, A k k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : A.trace = (0:ℂ) := by
      show ∑ i, Matrix.diag A i = 0
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.diag_apply]
      exact hcon i
    rw [hz] at htr
    exact absurd htr (by norm_num)
  set u : Fin d → ℂ := fun i => A i k with hu
  have hAu : A *ᵥ u = u := by
    funext i
    have h2 : (A * A) i k = A i k := congrFun (congrFun hA i) k
    rw [Matrix.mul_apply] at h2
    show ∑ l, A i l * u l = u i
    simpa [hu] using h2
  have hrk : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 1 := by
    have h5 : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
      rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))]
      rfl
    rw [← h5]
    exact h1
  have huMem : u ∈ LinearMap.range A.mulVecLin := by
    refine ⟨u, ?_⟩
    show A *ᵥ u = u
    exact hAu
  have hspan : LinearMap.range A.mulVecLin = Submodule.span ℂ {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrk huMem (fun h => hk (congrFun h k))
  have hcol : ∀ j, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j (1:ℂ), ?_⟩
    funext i
    show (A *ᵥ Pi.single j (1:ℂ)) i = A i j
    simp [Matrix.mulVec, Matrix.mulVec_single]
  have hdec : ∀ j, ∃ c : ℂ, ∀ i, A i j = c * u i := by
    intro j
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcol j)
    exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩
  have hform : ∀ i j, A i j = A i k * A k j / A k k := by
    intro i j
    obtain ⟨c, hc⟩ := hdec j
    have hik : A i j = c * A i k := hc i
    have hkj : A k j = c * A k k := hc k
    rw [hik, hkj]
    field_simp [hk]

  have hkksum : A k k = ∑ l, ((Complex.normSq (A k l) : ℝ) : ℂ) := by
    have h2 : (A * A) k k = A k k := congrFun (congrFun hA k) k
    rw [Matrix.mul_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hcj k l]
    simp only [Complex.star_def, Complex.mul_conj]
  have hsumnn : 0 ≤ ∑ l, Complex.normSq (A k l) :=
    Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg _)
  have hrne : (∑ l, Complex.normSq (A k l)) ≠ 0 := by
    intro hz
    apply hk
    rw [hkksum, ← Complex.ofReal_sum, hz]
    simp
  obtain ⟨r, hr0, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ((r : ℂ) = A k k) := by
    refine ⟨∑ l, Complex.normSq (A k l), lt_of_le_of_ne hsumnn (Ne.symm hrne), ?_⟩
    rw [hkksum]
    exact Complex.ofReal_sum _ _

  have hcolsum : ∑ i, Complex.normSq (A i k) = r := by
    have h7 : ((∑ i, Complex.normSq (A i k) : ℝ) : ℂ) = A k k := by
      rw [Complex.ofReal_sum, hkksum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcj k i]
      simp only [Complex.star_def, Complex.normSq_conj]
    exact Complex.ofReal_inj.mp (h7.trans hrc.symm)
  refine ⟨fun i => A i k / ((Real.sqrt r : ℂ)), ?_, ?_⟩
  · have hdiv : ∀ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ)))
        = Complex.normSq (A i k) / r := by
      intro i
      rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hr0.le]
    show ∑ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ))) = 1
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), ← Finset.sum_div, hcolsum, div_self hr0.ne']
  · intro i j
    rw [hform i j, hcj j k, ← hrc]
    show A i k * star (A j k) / ((r : ℝ) : ℂ)
      = A i k / ((Real.sqrt r : ℂ)) * star (A j k / ((Real.sqrt r : ℂ)))
    have hsd : star (A j k / ((Real.sqrt r : ℂ)))
        = star (A j k) / star ((Real.sqrt r : ℂ)) := star_div₀ _ _
    have hs : star ((Real.sqrt r : ℂ)) = ((Real.sqrt r : ℂ)) := by simp
    rw [hsd, hs, div_mul_div_comm]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le]

end SICLean
end
end

-- SICLean.CoreGalois
section
noncomputable section

open Matrix

namespace SICLean

private theorem galois_xi_normSq (d : ℕ) (n : ℤ) :
    Complex.normSq (xi d ^ n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_zpow]
  have h : ‖xi d‖ = 1 := by
    simp [xi, Complex.norm_exp]
  rw [h]
  simp

theorem map_rsicConst (d r : ℕ) (σ : ℂ →+* ℂ) :
    σ (rsicConst d r : ℂ) = (rsicConst d r : ℂ) := by
  simp [rsicConst, map_div₀]

theorem rsicConst_pos {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r < d) :
    0 < rsicConst d r := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrd' : (r : ℝ) < d := by exact_mod_cast hrd
  unfold rsicConst
  exact div_pos (mul_pos hr' (sub_pos.mpr hrd')) (by nlinarith)

private theorem galois_ov_adj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (p : ℤ × ℤ) : ov d Aᴴ p = star (ov d A (-p)) := by
  simp only [ov, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [conjTranspose_D, trace_mul_comm]

theorem map_ov_of_map_D {d : ℕ} (σ : ℂ →+* ℂ) (k : ℤ)
    (hD : ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2))
    (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :
    σ (ov d A p) = ov d (A.map σ) (p.1, k * p.2) := by
  simp only [ov, conjTranspose_D, AddMonoidHom.map_trace, Matrix.map_mul]
  rw [hD]
  congr 2
  simp

private theorem galois_ov_phase {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    {p q : ℤ × ℤ} {z : ℂ} (h : D d q = z • D d p) :
    ov d A q = star z * ov d A p := by
  simp only [ov, h, conjTranspose_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

private theorem galois_lift {d : ℕ} {k : ℤ} (hk : IsCoprime k (d : ℤ))
    (q : ℤ × ℤ) : ∃ p v : ℤ × ℤ,
      q = (p.1, k * p.2) + (d : ℤ) • v ∧
      (IsZeroLabel d p → IsZeroLabel d q) := by
  obtain ⟨a, b, hab⟩ := hk
  refine ⟨(q.1, a * q.2), (0, b * q.2), ?_, ?_⟩
  · apply Prod.ext
    · change q.1 = q.1 + (d : ℤ) * 0
      simp
    · change q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2)
      calc
        q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
        _ = k * (a * q.2) + (d : ℤ) * (b * q.2) := by ring
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    have heq : q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2) := by
      calc
        q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
        _ = _ := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right h₂ k) (dvd_mul_right _ _)

private theorem galois_eq_of_ov [NeZero d]
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ p : Fin d × Fin d,
      ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) =
      ov d B (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) : A = B := by
  rw [eq_sum_ov_smul_D A, eq_sum_ov_smul_D B]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [h p]

theorem map_fiducial_of_ghost_flip {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hrd : r < d) {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d r G)
    {σ : ℂ →+* ℂ} (hσ : UnimodularFlip d r G σ) :
    (G.map σ).IsHermitian ∧
    G.map σ * G.map σ = G.map σ ∧
    (G.map σ).trace = r ∧
    ∀ q : ℤ × ℤ, ¬ IsZeroLabel d q →
      Complex.normSq (ov d (G.map σ) q) = rsicConst d r := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨k, hk, hD⟩ := exists_map_D (d := d) σ
  let P := G.map σ
  have ht : P.trace = r := by
    change (G.map σ).trace = r
    rw [← AddMonoidHom.map_trace, hG.trace_eq, map_natCast]
  have hm (p : ℤ × ℤ) :
      σ (ov d G p) = ov d P (p.1, k * p.2) := map_ov_of_map_D σ k hD G p
  have hcpos := rsicConst_pos hd hr hrd
  have hconj (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
      ov d P (-(p.1, k * p.2)) = star (ov d P (p.1, k * p.2)) := by
    have hnonzero : σ (ov d G p) ≠ 0 := by
      intro hz
      have hh := hσ p hp
      rw [hz, Complex.normSq_zero] at hh
      linarith
    have hprod : σ (ov d G p) * σ (ov d G (-p)) = (rsicConst d r : ℂ) := by
      rw [← map_mul, hG.ov_mul_ov_neg p hp, map_rsicConst]
    have hnorm : σ (ov d G p) * star (σ (ov d G p)) = (rsicConst d r : ℂ) := by
      change σ (ov d G p) * starRingEnd ℂ (σ (ov d G p)) = _
      rw [Complex.mul_conj, hσ p hp]
    have hh := mul_left_cancel₀ hnonzero (hprod.trans hnorm.symm)
    rw [hm p, hm (-p)] at hh
    simpa using hh
  have hmod (q : ℤ × ℤ) (hq : ¬ IsZeroLabel d q) :
      Complex.normSq (ov d P q) = rsicConst d r := by
    obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
    have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
    have hphase : D d q =
        xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
          (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
      rw [hqeq, D_add_smul]
    rw [galois_ov_phase P hphase, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      galois_xi_normSq, one_mul, ← hm p]
    exact hσ p hp
  have hH : P.IsHermitian := by
    apply galois_eq_of_ov
    intro s
    let q : ℤ × ℤ := (((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ))
    change ov d Pᴴ q = ov d P q
    by_cases hq : IsZeroLabel d q
    · have hqzero : q = (0, 0) := by
        have h₁ : (s.1 : ℤ) = 0 := by
          have hlt : (s.1 : ℤ) < d := by exact_mod_cast s.1.isLt
          have hnn : (0 : ℤ) ≤ s.1 := by positivity
          exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.1
        have h₂ : (s.2 : ℤ) = 0 := by
          have hlt : (s.2 : ℤ) < d := by exact_mod_cast s.2.isLt
          have hnn : (0 : ℤ) ≤ s.2 := by positivity
          exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.2
        exact Prod.ext h₁ h₂
      simp [hqzero, ov, D_zero, trace_conjTranspose, ht]
    · obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
      have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
      have hphase : D d q =
          xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
            (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
        rw [hqeq, D_add_smul]
      rw [galois_ov_phase Pᴴ hphase, galois_ov_phase P hphase,
        galois_ov_adj, hconj p hp, star_star]
  refine ⟨hH, ?_, ht, hmod⟩
  rw [← Matrix.map_mul, hG.idem]

end SICLean
end
end

-- SICLean.CoreRankOne
section
noncomputable section

open Matrix

namespace SICLean

private theorem rankOne_norm_xi (d : ℕ) : ‖xi d‖ = 1 := by
  simp [xi, Complex.norm_exp]

private theorem rankOne_normSq_xi_zpow (d : ℕ) (n : ℤ) :
    Complex.normSq (xi d ^ n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_zpow, rankOne_norm_xi]
  simp

private theorem rankOne_dot_eq_sum_normSq {d : ℕ} (ψ : Fin d → ℂ) :
    star ψ ⬝ᵥ ψ = ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

private theorem rankOne_normalized {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    OpenQuantumProblem23.IsNormalized (OpenQuantumProblem23.mkStateVector ψ) := by
  have hn : ‖OpenQuantumProblem23.mkStateVector ψ‖ ^ 2 = 1 := by
    simpa only [PiLp.norm_sq_eq_of_L2, Complex.sq_norm] using hψ
  unfold OpenQuantumProblem23.IsNormalized
  nlinarith [norm_nonneg (OpenQuantumProblem23.mkStateVector ψ)]

private theorem rankOne_dot_mulVec {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) = star ψ ⬝ᵥ ((Aᴴ * B) *ᵥ ψ) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

private theorem rankOne_trace_mul {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    {ψ : Fin d → ℂ} (hψ : ∀ i j, P i j = ψ i * star (ψ j))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (P * A).trace = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  simp only [trace, diag, Matrix.mul_apply, hψ, mulVec, dotProduct, Pi.star_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rankOne_orbit_normalized {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) (p : ℤ × ℤ) :
    OpenQuantumProblem23.IsNormalized
      (OpenQuantumProblem23.mkStateVector (D d p *ᵥ ψ)) := by
  apply rankOne_normalized
  apply Complex.ofReal_injective
  rw [← rankOne_dot_eq_sum_normSq, rankOne_dot_mulVec]
  have hD : (D d p)ᴴ * D d p = 1 := by
    simpa only [conjTranspose_D, neg_neg] using
      (D_mul_conjTranspose_D (d := d) (-p))
  rw [hD, one_mulVec, rankOne_dot_eq_sum_normSq, hψ]

private theorem rankOne_orbit_overlap {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    {ψ : Fin d → ℂ} (hψ : ∀ i j, P i j = ψ i * star (ψ j))
    (p q : ℤ × ℤ) :
    OpenQuantumProblem23.overlapSq
      (OpenQuantumProblem23.mkStateVector (D d p *ᵥ ψ))
      (OpenQuantumProblem23.mkStateVector (D d q *ᵥ ψ)) =
      Complex.normSq (ov d P (p - q)) := by
  change Complex.normSq (star (D d p *ᵥ ψ) ⬝ᵥ (D d q *ᵥ ψ)) = _
  rw [rankOne_dot_mulVec, conjTranspose_D, D_mul_D, smul_mulVec, dotProduct_smul]
  change Complex.normSq ((xi d ^ ((-p).2 * q.1 - (-p).1 * q.2)) *
    (star ψ ⬝ᵥ (D d (-p + q) *ᵥ ψ))) = _
  rw [Complex.normSq_mul, rankOne_normSq_xi_zpow, one_mul]
  unfold ov
  rw [conjTranspose_D, rankOne_trace_mul hψ]
  congr 3
  abel_nf

private def rankOne_label {d : ℕ} (p : Fin d × Fin d) : ℤ × ℤ :=
  (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))

private theorem rankOne_fin_eq_of_dvd_sub {d : ℕ} {i j : Fin d}
    (h : (d : ℤ) ∣ (i : ℤ) - (j : ℤ)) : i = j := by
  have hm : (j : ℤ) ≡ (i : ℤ) [ZMOD (d : ℤ)] := Int.modEq_iff_dvd.mpr h
  have hi : (i : ℤ) % d = (i : ℤ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hj : (j : ℤ) % d = (j : ℤ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  rw [Int.ModEq, hi, hj] at hm
  apply Fin.ext
  exact_mod_cast hm.symm

private theorem rankOne_label_sub_nonzero {d : ℕ} {p q : Fin d × Fin d} (hpq : p ≠ q) :
    ¬ IsZeroLabel d (rankOne_label p - rankOne_label q) := by
  rintro ⟨h₁, h₂⟩
  apply hpq
  apply Prod.ext
  · exact rankOne_fin_eq_of_dvd_sub h₁
  · exact rankOne_fin_eq_of_dvd_sub h₂

private theorem rankOne_rsicConst {d : ℕ} (hd : 2 ≤ d) :
    rsicConst d 1 = OpenQuantumProblem23.sicOverlapSq d := by
  unfold rsicConst OpenQuantumProblem23.sicOverlapSq
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hsucc : (d : ℝ) + 1 ≠ 0 := by linarith
  norm_num only [Nat.cast_one, one_mul]
  field_simp [hden, hsucc]
  ring

theorem hasSICPOVM_of_fiducial {d : ℕ} (hd : 2 ≤ d)
    {P : Matrix (Fin d) (Fin d) ℂ} (hH : P.IsHermitian) (hP : P * P = P)
    (ht : P.trace = 1)
    (hov : ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      Complex.normSq (ov d P p) = rsicConst d 1) :
    OpenQuantumProblem23.HasSICPOVM d := by
  have hrank : P.rank = 1 := by
    have hc : (P.rank : ℂ) = 1 := (rank_eq_trace_of_idem P hP).trans ht
    exact_mod_cast hc
  obtain ⟨ψ, hψ, hPψ⟩ := exists_unit_of_rank_one P hH hP hrank
  let e : Fin (d ^ 2) ≃ Fin d × Fin d := Fintype.equivOfCardEq (by simp [pow_two])
  refine ⟨fun j => OpenQuantumProblem23.mkStateVector
    (D d (rankOne_label (e j)) *ᵥ ψ), ?_, ?_⟩
  · intro j
    exact rankOne_orbit_normalized ψ hψ _
  · intro j k hjk
    rw [rankOne_orbit_overlap hPψ]
    rw [hov _ (rankOne_label_sub_nonzero (e.injective.ne hjk))]
    exact rankOne_rsicConst hd

end SICLean
end
end

-- SICLean.Main
section
noncomputable section
open Matrix OpenQuantumProblem23
namespace SICLean

theorem hasSICPOVM_of_ghost_flip {d : ℕ} (hd : 2 ≤ d)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d 1 G) {σ : ℂ →+* ℂ}
    (hσ : UnimodularFlip d 1 G σ) : HasSICPOVM d := by
  obtain ⟨hH, hP, ht, hov⟩ :=
    map_fiducial_of_ghost_flip hd (by omega) (by omega) hG hσ
  exact hasSICPOVM_of_fiducial hd hH hP (by simpa using ht) hov

end SICLean
end
end

-- SICLean.L2a.Defs
section
noncomputable section

open Matrix

namespace SICLean.L2a

abbrev Index (M : ℕ) := ZMod M × ZMod M

abbrev Values (M : ℕ) := Index M → ℂ

def valueAt {M : ℕ} (F : Values M) (i j : ℤ) : ℂ := F (i, j)

def epsilon (M : ℕ) : ℝ :=
  ((M : ℝ) - 1 + Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) / 2

def sqrtEpsilon (M : ℕ) : ℂ := (Real.sqrt (epsilon M) : ℂ)

def denominator (M : ℕ) : ℂ := sqrtEpsilon M + (sqrtEpsilon M)⁻¹

def convolutionScalar (M : ℕ) : ℂ := (Real.sqrt ((M : ℝ) - 3) : ℂ)

def e (M : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ))

def quadraticForm (i j : ℤ) : ℤ := i ^ 2 - i * j + j ^ 2

def gaussianLift (M : ℕ) (i j : ℤ) : ℂ := e M (quadraticForm i j)

def gaussian (M : ℕ) (h : Index M) : ℂ :=
  gaussianLift M h.1.val h.2.val

def pairing (M : ℕ) (h k : Index M) : ℂ :=
  gaussian M (h + k) / (gaussian M h * gaussian M k)

def theta (M : ℕ) (i j : ℤ) : ℂ :=
  (-1 : ℂ) ^ (i + j + i * j) *
    Complex.exp (Real.pi * Complex.I * (quadraticForm i j : ℂ) / (M : ℂ))

def heisenbergPhase (M : ℕ) (i j : ℤ) : ℂ :=
  (-1 : ℂ) ^ (i + j) *
    Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ))

def toWH (i j : ℤ) : ℤ × ℤ := (-j, i)

def fromWH (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)

def qPower (M : ℕ) (i : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  fun a b => if a = b then omega M ^ (i * (b : ℤ)) else 0

def pPower (M : ℕ) (j : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  fun a b => if (b : ZMod M) = (a : ZMod M) + (j : ZMod M) then 1 else 0

def convolution (M : ℕ) (F : Values M) (r s : ℤ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ j : Fin M,
    valueAt F i j * valueAt F (r - i) (s - j) * gaussianLift M i j *
      e M (-(i : ℤ) * r + (j : ℤ) * (r - s))

def P (M : ℕ) (F : Values M) : Matrix (Fin M) (Fin M) ℂ :=
  (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
    (theta M i j * valueAt F i j) • D M (toWH i j)

def ghostProjector (M : ℕ) (F : Values M) : Matrix (Fin M) (Fin M) ℂ :=
  (denominator M)⁻¹ • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F)

def coefficient (M : ℕ) (F : Values M) (i j : ℤ) : ℂ :=
  -(theta M i j * valueAt F i j) / denominator M

end SICLean.L2a
end
end

-- SICLean.L2a.Inputs
section
noncomputable section

namespace SICLean.L2a

structure RWConvolutionInput (M : ℕ) (F : Values M) : Prop where
  origin : F 0 = sqrtEpsilon M ^ 3
  reflection : ∀ h : Index M, h ≠ 0 → F h * F (-h) = (gaussian M h)⁻¹
  convolution_eq : ∀ h : Index M,
    convolution M F h.1.val h.2.val =
      convolutionScalar M * F h + if h = 0 then (M : ℂ) else 0

structure RWUnitCircleInput (M : ℕ) (F : Values M) (τ : ℂ →+* ℂ) : Prop where
  norm_F : ∀ h : Index M, h ≠ 0 → ‖τ (F h)‖ = 1

end SICLean.L2a
end
end

-- SICLean.L2a.Algebra
section
noncomputable section

open Matrix

namespace SICLean.L2a

theorem epsilon_gt_one {M : ℕ} (hM : 4 ≤ M) : 1 < epsilon M := by
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hs := Real.sqrt_nonneg (((M : ℝ) - 1) ^ 2 - 4)
  unfold epsilon
  rw [one_lt_div (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem epsilon_quadratic {M : ℕ} (hM : 4 ≤ M) :
    epsilon M ^ 2 - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hnng : (0 : ℝ) ≤ ((M : ℝ) - 1) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hnng
  unfold epsilon
  field_simp
  nlinarith

theorem sqrtEpsilon_ne_zero {M : ℕ} (hM : 4 ≤ M) : sqrtEpsilon M ≠ 0 := by
  have h1 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
  intro h
  apply absurd (Real.sqrt_eq_zero'.mp (Complex.ofReal_eq_zero.mp h))
  exact (not_le.mpr h1)

theorem sqrtEpsilon_sub_inv {M : ℕ} (hM : 4 ≤ M) :
    sqrtEpsilon M - (sqrtEpsilon M)⁻¹ = convolutionScalar M := by
  have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
  have hε0 : (0 : ℝ) < epsilon M := by linarith
  have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
  have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
    rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
  have hwq : Real.sqrt (epsilon M) ^ 4 - ((M : ℝ) - 1) * Real.sqrt (epsilon M) ^ 2 + 1 = 0 := by
    rw [h4, hw2]
    exact epsilon_quadratic hM
  have key : (Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) - 3) := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    field_simp
    nlinarith
  have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    by_contra hc
    push_neg at hc
    have h8 := mul_lt_mul_of_pos_right hc hwpos
    simp only [zero_mul] at h8
    rw [mul_comm, mul_sub, mul_inv_cancel₀ (ne_of_gt hwpos)] at h8
    nlinarith
  have hfin : Real.sqrt (((M : ℝ) - 3)) = Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ :=
    (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
  have h2 : (Real.sqrt ((M : ℝ) - 3) : ℂ)
      = (Real.sqrt (epsilon M) : ℂ) - ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
    rw [hfin, Complex.ofReal_sub, Complex.ofReal_inv]
  simp only [sqrtEpsilon, convolutionScalar]
  exact h2.symm

theorem sqrtEpsilon_cube {M : ℕ} (hM : 4 ≤ M) :
    sqrtEpsilon M ^ 3 = ((M : ℂ) - 1) * sqrtEpsilon M - (sqrtEpsilon M)⁻¹ := by
  have hν : sqrtEpsilon M ≠ 0 := sqrtEpsilon_ne_zero hM
  have hε0 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
  have h2 : sqrtEpsilon M * sqrtEpsilon M = (epsilon M : ℂ) := by
    simp only [sqrtEpsilon]
    exact_mod_cast Real.mul_self_sqrt (le_of_lt hε0)
  have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
    have h := epsilon_quadratic hM
    linear_combination h
  have hq2 : (epsilon M : ℂ) * (epsilon M : ℂ) - ((M : ℂ) - 1) * (epsilon M : ℂ) + 1 = 0 := by
    exact_mod_cast hq
  apply mul_right_cancel₀ hν
  have hν3 : sqrtEpsilon M ^ 3 * sqrtEpsilon M = sqrtEpsilon M ^ 4 := by
    rw [pow_succ, show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two]
    ring
  have hq3 : sqrtEpsilon M ^ 4 - ((M : ℂ) - 1) * sqrtEpsilon M ^ 2 + 1 = 0 := by
    rw [show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two, h2]
    exact hq2
  rw [hν3, sub_mul, mul_assoc, inv_mul_cancel₀ hν]
  linear_combination hq3

theorem denominator_eq_sqrt {M : ℕ} (hM : 4 ≤ M) :
    denominator M = (Real.sqrt ((M : ℝ) + 1) : ℂ) := by
  have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
  have hε0 : (0 : ℝ) < epsilon M := by linarith
  have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
  have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
    rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
  have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
    have h := epsilon_quadratic hM
    linear_combination h
  have key : (Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) + 1) := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    field_simp
    nlinarith [hw2]
  have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ := by
    have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
    have := inv_nonneg.mpr (le_of_lt hwpos)
    linarith
  have hfin : Real.sqrt (((M : ℝ) + 1)) = Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ :=
    (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
  have h2 : (Real.sqrt ((M : ℝ) + 1) : ℂ)
      = (Real.sqrt (epsilon M) : ℂ) + ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
    rw [hfin, Complex.ofReal_add, Complex.ofReal_inv]
  simp only [denominator, sqrtEpsilon]
  exact h2.symm

theorem denominator_ne_zero {M : ℕ} (hM : 4 ≤ M) : denominator M ≠ 0 := by
  rw [denominator_eq_sqrt hM]
  intro h
  have h1 : Real.sqrt ((M : ℝ) + 1) = 0 := Complex.ofReal_eq_zero.mp h
  have h2 : ((M : ℝ) + 1) ≤ 0 := Real.sqrt_eq_zero'.mp h1
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

theorem map_denominator_eq_or_neg {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) :
    τ (denominator M) = (Real.sqrt ((M : ℝ) + 1) : ℂ) ∨
      τ (denominator M) = -(Real.sqrt ((M : ℝ) + 1) : ℂ) := by
  refine sq_eq_sq_iff_eq_or_eq_neg.mp ?_
  have hn : (0 : ℝ) ≤ ((M : ℝ) + 1) := by
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hsq : denominator M ^ 2 = ((M : ℂ) + 1) := by
    rw [denominator_eq_sqrt hM]
    exact_mod_cast Real.sq_sqrt hn
  rw [← map_pow τ _ 2, hsq, map_add, map_natCast, map_one]
  exact_mod_cast (Real.sq_sqrt hn).symm

theorem e_eq_omega_zpow (M : ℕ) (n : ℤ) : e M n = omega M ^ n := by
  rw [e, omega_exp]

theorem e_eq_of_dvd {M : ℕ} {n n' : ℤ} (h : ((M : ℕ) : ℤ) ∣ n - n') : e M n = e M n' := by
  by_cases hM : M = 0
  · subst hM
    have hn : n = n' := sub_eq_zero.mp (Int.zero_dvd.mp h)
    rw [hn]
  · rw [e_eq_omega_zpow, e_eq_omega_zpow]
    obtain ⟨q, hq⟩ := h
    have hn : n = n' + ((M : ℕ) : ℤ) * q := by linear_combination hq
    rw [hn, zpow_add₀ (omega_ne_zero M), _root_.zpow_mul, zpow_natCast,
      omega_pow_d_of_ne_zero M hM, _root_.one_zpow, mul_one]

theorem gaussian_eq_lift {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    gaussian M ((i : ZMod M), (j : ZMod M)) = gaussianLift M i j := by
  have hne : M ≠ 0 := by omega
  haveI : NeZero M := ⟨hne⟩
  have hA : ((M : ℕ) : ℤ) ∣ (((i : ZMod M).val : ℕ) : ℤ) - i := by
    have hv : (((i : ZMod M).val : ℕ) : ℤ) = i % ((M : ℕ) : ℤ) := ZMod.val_intCast i
    refine ⟨-(i / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv i ((M : ℕ) : ℤ)]
  have hB : ((M : ℕ) : ℤ) ∣ (((j : ZMod M).val : ℕ) : ℤ) - j := by
    have hv : (((j : ZMod M).val : ℕ) : ℤ) = j % ((M : ℕ) : ℤ) := ZMod.val_intCast j
    refine ⟨-(j / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv j ((M : ℕ) : ℤ)]
  have hdvd : ((M : ℕ) : ℤ) ∣ quadraticForm (((i : ZMod M).val : ℕ) : ℤ)
      (((j : ZMod M).val : ℕ) : ℤ) - quadraticForm i j := by
    have h1 : quadraticForm (((i : ZMod M).val : ℕ) : ℤ) (((j : ZMod M).val : ℕ) : ℤ)
        - quadraticForm i j
        = ((((i : ZMod M).val : ℕ) : ℤ) - i) * ((((i : ZMod M).val : ℕ) : ℤ) + i)
          - ((((i : ZMod M).val : ℕ) : ℤ) - i) * j
          - (((i : ZMod M).val : ℕ) : ℤ) * ((((j : ZMod M).val : ℕ) : ℤ) - j)
          + ((((j : ZMod M).val : ℕ) : ℤ) - j) * ((((j : ZMod M).val : ℕ) : ℤ) + j) := by
      unfold quadraticForm; ring
    rw [h1]
    exact dvd_add (dvd_sub
      (dvd_sub (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left hA _))
      (dvd_mul_of_dvd_right hB _))
      (dvd_mul_of_dvd_left hB _)
  unfold gaussian gaussianLift
  exact e_eq_of_dvd hdvd

theorem e_mul (M : ℕ) (n n' : ℤ) : e M n * e M n' = e M (n + n') := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, e_eq_omega_zpow, ← zpow_add₀ (omega_ne_zero M)]

theorem e_inv (M : ℕ) (n : ℤ) : (e M n)⁻¹ = e M (-n) := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, ← _root_.zpow_neg]

theorem pairing_eq_exp {M : ℕ} (hM : 4 ≤ M) (i j k l : ℤ) :
    pairing M ((i : ZMod M), (j : ZMod M)) ((k : ZMod M), (l : ZMod M)) =
      e M (2 * i * k - i * l - j * k + 2 * j * l) := by
  have h1 : ((i : ZMod M), (j : ZMod M)) + ((k : ZMod M), (l : ZMod M))
      = (((i + k : ℤ) : ZMod M), ((j + l : ℤ) : ZMod M)) := by
    push_cast
    rfl
  have hg1 : gaussian M (((i : ZMod M), (j : ZMod M)) + ((k : ZMod M), (l : ZMod M)))
      = gaussianLift M (i + k) (j + l) := by
    rw [h1]
    exact gaussian_eq_lift hM (i + k) (j + l)
  rw [pairing, hg1, gaussian_eq_lift hM i j, gaussian_eq_lift hM k l]
  rw [gaussianLift, gaussianLift, gaussianLift, div_eq_inv_mul, mul_inv]
  rw [e_inv, e_inv, e_mul, e_mul]
  congr 1
  unfold quadraticForm
  ring

theorem negOne_zpow_eq_of_two_dvd {e e' : ℤ} (h : (2 : ℤ) ∣ e - e') :
    (-1 : ℂ) ^ e = (-1 : ℂ) ^ e' := by
  obtain ⟨n, hn⟩ := h
  have he : e = e' + 2 * n := by linear_combination hn
  have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul, h2, _root_.one_zpow, mul_one]

theorem xi_zpow_exp (M : ℕ) (z : ℤ) :
    xi M ^ z = (-1 : ℂ) ^ z *
      Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ)) := by
  have hx : xi M = (-1 : ℂ) * Complex.exp (Real.pi * Complex.I / (M : ℂ)) := by
    rw [xi]
    ring
  have key : Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ))
      = Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ z := by
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [hx, mul_zpow, key]

theorem theta_eq_xi_zpow (M : ℕ) (i j : ℤ) :
    theta M i j = xi M ^ quadraticForm i j := by
  have h1 : (2 : ℤ) ∣ i - i * i := by
    obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one i
    exact ⟨-q + i, by linear_combination -hq⟩
  have h2 : (2 : ℤ) ∣ j - j * j := by
    obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one j
    exact ⟨-q + j, by linear_combination -hq⟩
  have hexp : (i + j + i * j) - quadraticForm i j
      = (i - i * i) + (j - j * j) + 2 * (i * j) := by
    unfold quadraticForm; ring
  have hpar : (2 : ℤ) ∣ (i + j + i * j) - quadraticForm i j := by
    rw [hexp]
    exact dvd_add (dvd_add h1 h2) (dvd_mul_right (2 : ℤ) (i * j))
  rw [theta, xi_zpow_exp, negOne_zpow_eq_of_two_dvd hpar]

theorem theta_neg (M : ℕ) (i j : ℤ) : theta M (-i) (-j) = theta M i j := by
  rw [theta_eq_xi_zpow, theta_eq_xi_zpow]
  congr 1
  unfold quadraticForm
  ring

theorem theta_sq (M : ℕ) (i j : ℤ) : theta M i j ^ 2 = gaussianLift M i j := by
  rw [theta_eq_xi_zpow, pow_two, ← zpow_add₀ (xi_ne_zero M)]
  rw [show quadraticForm i j + quadraticForm i j = 2 * quadraticForm i j from by ring]
  rw [← omega_zpow, ← e_eq_omega_zpow, gaussianLift]

theorem theta_pow_two_mul {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    theta M i j ^ (2 * M) = 1 := by
  rw [theta_eq_xi_zpow, ← zpow_natCast (xi M ^ quadraticForm i j) (2 * M),
    ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow]

theorem map_theta_norm {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) (i j : ℤ) :
    ‖τ (theta M i j)‖ = 1 := by
  have hx : τ (theta M i j) ^ (2 * M) = 1 := by
    rw [← map_pow τ, theta_pow_two_mul hM, map_one]
  have hn : ‖τ (theta M i j)‖ ^ (2 * M) = 1 := by
    rw [← Complex.norm_pow, hx]
    simp
  have hn0 : (2 * M : ℕ) ≠ 0 := by omega
  have key : ∀ a : ℝ, 0 ≤ a → a ^ (2 * M) = 1 → a = 1 := by
    intro a ha h
    rcases lt_trichotomy a 1 with h1 | h1 | h1
    · exfalso
      rcases lt_or_ge (0 : ℝ) a with h0 | h0
      · have hin : 1 < a⁻¹ := (one_lt_inv_iff₀).mpr ⟨h0, h1⟩
        have h2 := one_lt_pow₀ hin hn0
        rw [inv_pow, h] at h2
        norm_num at h2
      · have h0e : a = 0 := le_antisymm h0 ha
        rw [h0e, zero_pow hn0] at h
        norm_num at h
    · exact h1
    · have h2 := one_lt_pow₀ h1 hn0
      rw [h] at h2
      linarith
  exact key ‖τ (theta M i j)‖ (norm_nonneg _) hn

theorem xi_pow_M {M : ℕ} (hM : 4 ≤ M) :
    xi M ^ ((M : ℕ) : ℤ) = (-1 : ℂ) ^ (((M : ℕ) + 1 : ℕ) : ℤ) := by
  have hMn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hkey : (M : ℂ) * (Real.pi * Complex.I / (M : ℂ)) = Real.pi * Complex.I := by
    field_simp
  have hexp : Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ (M : ℕ) = -1 := by
    rw [← Complex.exp_nat_mul, hkey, Complex.exp_pi_mul_I]
  have hR : (-1 : ℂ) ^ (((M + 1 : ℕ) : ℤ)) = (-1 : ℂ) ^ ((M : ℕ) : ℤ) * (-1 : ℂ) := by
    have hc : ((M + 1 : ℕ) : ℤ) = ((M : ℕ) : ℤ) + 1 := by omega
    rw [hc, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_natCast, xi, neg_pow, hexp, hR, zpow_natCast]

theorem xi_zpow_mul_M {M : ℕ} (hM : 4 ≤ M) (k : ℤ) :
    xi M ^ ((M : ℤ) * k) = (-1 : ℂ) ^ (((M : ℤ) + 1) * k) := by
  have hc : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
  rw [_root_.zpow_mul, xi_pow_M hM, hc, ← _root_.zpow_mul]

theorem theta_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
    theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) =
      (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j := by
  have hQ : quadraticForm (i + (M : ℤ) * a) (j + (M : ℤ) * b)
      = quadraticForm i j + (M : ℤ) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
        + (M : ℤ) * quadraticForm a b) := by
    unfold quadraticForm; ring
  have hE : (-1 : ℂ) ^ (((M : ℤ) + 1) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
        + (M : ℤ) * quadraticForm a b))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
    refine negOne_zpow_eq_of_two_dvd ?_
    obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
    push_cast at hts
    refine ⟨((M : ℤ) + 1) * (i * a + j * b - i * b - j * a) + t * quadraticForm a b, ?_⟩
    unfold quadraticForm
    linear_combination (a * a - a * b + b * b) * hts
  rw [theta_eq_xi_zpow, theta_eq_xi_zpow, hQ, zpow_add₀ (xi_ne_zero M),
    xi_zpow_mul_M hM, hE,
    mul_comm ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)))]

theorem phased_displacement_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
    theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) •
        D M (toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)) =
      theta M i j • D M (toWH i j) := by
  have hto : toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)
      = toWH i j + (M : ℤ) • ((-b, a) : ℤ × ℤ) := by
    show (-(j + (M : ℤ) * b), i + (M : ℤ) * a)
        = ((-j + (M : ℤ) * (-b), i + (M : ℤ) * a) : ℤ × ℤ)
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have hE : xi M ^ ((M : ℤ) * ((toWH i j).1 * ((-b, a) : ℤ × ℤ).2
        + ((-b, a) : ℤ × ℤ).1 * (toWH i j).2)
        + (M : ℤ) ^ 2 * (((-b, a) : ℤ × ℤ).1 * ((-b, a) : ℤ × ℤ).2))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
    show xi M ^ ((M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a))
      = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
    have hexp2 : (M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a)
        = (M : ℤ) * (-j * a + -b * i + (M : ℤ) * (-b * a)) := by
      ring
    rw [hexp2, xi_zpow_mul_M hM]
    refine negOne_zpow_eq_of_two_dvd ?_
    obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
    push_cast at hts
    refine ⟨-((M : ℤ) + 1) * (j * a + i * b) - t * (b * a), ?_⟩
    linear_combination (-(b * a)) * hts
  have hone : (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
      * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = 1 := by
    have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
    rw [← _root_.zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show ((M : ℤ) + 1) * (i * b + j * a) + ((M : ℤ) + 1) * (i * b + j * a)
        = 2 * (((M : ℤ) + 1) * (i * b + j * a)) from by ring,
      _root_.zpow_mul, h2, _root_.one_zpow]
  have hs : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
      * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = theta M i j := by
    have hrw : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
        * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
        = ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
          * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))) * theta M i j := by
      ring
    rw [hrw, hone, one_mul]
  rw [hto, D_add_smul, smul_smul, theta_add_period hM, hE, hs]

theorem qPower_mul_pPower {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    qPower M i * pPower M j = xi M ^ (-(i * j)) • D M (toWH i j) := by
  haveI : NeZero M := ⟨by omega⟩
  ext a b
  simp only [Matrix.mul_apply, qPower, pPower, D, toWH, Matrix.smul_apply, smul_eq_mul]
  push_cast
  by_cases hL : ((b : ℕ) : ZMod M) = ((a : ℕ) : ZMod M) + (j : ZMod M)
  · have hR : ((a : ℕ) : ZMod M) = ((b : ℕ) : ZMod M) + (-(j : ZMod M)) := by
      linear_combination -hL
    obtain ⟨t, ht⟩ := exists_sub_of_label hL
    have hsum : (∑ k : Fin M, (if a = k then omega M ^ (i * ((k : ℕ) : ℤ)) else 0)
        * (if ((b : ℕ) : ZMod M) = ((k : ℕ) : ZMod M) + (j : ZMod M) then 1 else 0))
        = omega M ^ (i * ((a : ℕ) : ℤ)) := by
      refine (Finset.sum_eq_single (s := Finset.univ) a ?_ ?_).trans ?_
      · intro k _ hk
        rw [if_neg (Ne.symm hk), zero_mul]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
      · show (if a = a then omega M ^ (i * ((a : ℕ) : ℤ)) else 0)
            * (if ((b : ℕ) : ZMod M) = ((a : ℕ) : ZMod M) + (j : ZMod M) then 1 else 0)
            = omega M ^ (i * ((a : ℕ) : ℤ))
        rw [if_pos rfl, if_pos hL, mul_one]
    rw [hsum, if_pos hR, omega_zpow, omega_zpow,
      ← _root_.zpow_add₀ (xi_ne_zero M), ← _root_.zpow_add₀ (xi_ne_zero M)]
    refine xi_zpow_eq_of_dvd ⟨-(i * t), ?_⟩
    push_cast
    linear_combination -(2 * i) * ht
  · have hR : ¬(((a : ℕ) : ZMod M) = ((b : ℕ) : ZMod M) + (-(j : ZMod M))) := by
      intro hc
      exact hL (by linear_combination -hc)
    rw [if_neg hR, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hk : a = k
    · subst hk
      rw [if_pos rfl, if_neg hL, mul_zero]
    · rw [if_neg hk, zero_mul]

theorem heisenbergPhase_mul_xi (M : ℕ) (i j : ℤ) :
    heisenbergPhase M i j * xi M ^ (-(i * j)) = theta M i j := by
  rw [heisenbergPhase, theta, xi_zpow_exp]
  have hre : ((-1 : ℂ) ^ (i + j)
        * Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ)))
      * ((-1 : ℂ) ^ (-(i * j))
        * Complex.exp (Real.pi * Complex.I * ((-(i * j) : ℤ) : ℂ) / (M : ℂ)))
      = ((-1 : ℂ) ^ (i + j)) * ((-1 : ℂ) ^ (-(i * j)))
        * (Complex.exp (Real.pi * Complex.I * ((i ^ 2 + j ^ 2 : ℤ) : ℂ) / (M : ℂ))
          * Complex.exp (Real.pi * Complex.I * ((-(i * j) : ℤ) : ℂ) / (M : ℂ))) := by
    ring
  have hd : (2 : ℤ) ∣ (i + j + -(i * j)) - (i + j + i * j) := ⟨-(i * j), by ring⟩
  rw [hre, ← Complex.exp_add, ← _root_.zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    negOne_zpow_eq_of_two_dvd hd]
  congr 1
  congr 1
  unfold quadraticForm
  push_cast
  ring

theorem P_eq_heisenberg {M : ℕ} (hM : 4 ≤ M) (F : Values M) :
    P M F = (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
      (heisenbergPhase M i j * valueAt F i j) • (qPower M i * pPower M j) := by
  have key : ∀ i j : Fin M,
      (heisenbergPhase M (i : ℤ) (j : ℤ) * valueAt F i j)
        • (qPower M (i : ℤ) * pPower M (j : ℤ))
        = (theta M (i : ℤ) (j : ℤ) * valueAt F i j) • D M (toWH (i : ℤ) (j : ℤ)) := by
    intro i j
    have hrw : (heisenbergPhase M (i : ℤ) (j : ℤ) * valueAt F i j)
          * xi M ^ (-((i : ℤ) * (j : ℤ)))
        = theta M (i : ℤ) (j : ℤ) * valueAt F i j := by
      rw [← heisenbergPhase_mul_xi]
      ring
    rw [qPower_mul_pPower hM, smul_smul, hrw]
  rw [P]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  exact (key i j).symm

theorem convolution_eq_of_input {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (r s : ℤ) :
    convolution M F r s = convolutionScalar M * valueAt F r s +
      if IsZeroLabel M (r, s) then (M : ℂ) else 0 := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨t₁, ht₁⟩ : (M : ℤ) ∣ r - ((r : ZMod M).val : ℤ) := by
    refine ⟨r / (M : ℤ), ?_⟩
    rw [ZMod.val_intCast]
    linear_combination -(Int.emod_add_mul_ediv r (M : ℤ))
  obtain ⟨t₂, ht₂⟩ : (M : ℤ) ∣ s - ((s : ZMod M).val : ℤ) := by
    refine ⟨s / (M : ℤ), ?_⟩
    rw [ZMod.val_intCast]
    linear_combination -(Int.emod_add_mul_ediv s (M : ℤ))
  have key : ∀ i j : Fin M,
      valueAt F (i : ℤ) (j : ℤ) * valueAt F (r - (i : ℤ)) (s - (j : ℤ))
          * gaussianLift M (i : ℤ) (j : ℤ)
          * e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
        = valueAt F (i : ℤ) (j : ℤ)
            * valueAt F (((r : ZMod M).val : ℤ) - (i : ℤ))
              (((s : ZMod M).val : ℤ) - (j : ℤ))
            * gaussianLift M (i : ℤ) (j : ℤ)
            * e M (-(i : ℤ) * ((r : ZMod M).val : ℤ)
              + (j : ℤ) * (((r : ZMod M).val : ℤ) - ((s : ZMod M).val : ℤ))) := by
    intro i j
    have h1 : ((r - (i : ℤ) : ℤ) : ZMod M)
        = ((((r : ZMod M).val : ℤ) - (i : ℤ) : ℤ) : ZMod M) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-t₁, by linear_combination -ht₁⟩
    have h2 : ((s - (j : ℤ) : ℤ) : ZMod M)
        = ((((s : ZMod M).val : ℤ) - (j : ℤ) : ℤ) : ZMod M) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-t₂, by linear_combination -ht₂⟩
    have hv : valueAt F (r - (i : ℤ)) (s - (j : ℤ))
        = valueAt F (((r : ZMod M).val : ℤ) - (i : ℤ))
            (((s : ZMod M).val : ℤ) - (j : ℤ)) := by
      unfold valueAt
      rw [h1, h2]
    have he : e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
        = e M (-(i : ℤ) * ((r : ZMod M).val : ℤ)
          + (j : ℤ) * (((r : ZMod M).val : ℤ) - ((s : ZMod M).val : ℤ))) := by
      refine e_eq_of_dvd ⟨-(i : ℤ) * t₁ + (j : ℤ) * (t₁ - t₂), ?_⟩
      linear_combination ((j : ℤ) - (i : ℤ)) * ht₁ - (j : ℤ) * ht₂
    rw [hv, he]
  have hconv : convolution M F r s
      = convolution M F ((r : ZMod M).val) ((s : ZMod M).val) := by
    unfold convolution
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact key i j
  have h0 : convolution M F ((r : ZMod M).val) ((s : ZMod M).val)
      = convolutionScalar M * F ((r : ZMod M), (s : ZMod M))
        + if ((r : ZMod M), (s : ZMod M)) = 0 then (M : ℂ) else 0 :=
    hA.convolution_eq ((r : ZMod M), (s : ZMod M))
  have hzero : ((r : ZMod M), (s : ZMod M)) = (0 : Index M) ↔ IsZeroLabel M (r, s) := by
    constructor
    · intro h
      have hp := Prod.ext_iff.mp h
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r M).mp hp.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd s M).mp hp.2⟩
    · intro h
      rw [Prod.ext_iff]
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r M).mpr h.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd s M).mpr h.2⟩
  have hite : (if ((r : ZMod M), (s : ZMod M)) = 0 then (M : ℂ) else 0)
      = if IsZeroLabel M (r, s) then (M : ℂ) else 0 := by
    by_cases h : ((r : ZMod M), (s : ZMod M)) = (0 : Index M)
    · rw [if_pos h, if_pos (hzero.mp h)]
    · rw [if_neg h, if_neg (mt hzero.mpr h)]
  rw [hconv, h0, hite]
  rfl

end SICLean.L2a
end
end

-- SICLean.L2a.Weyl
section
noncomputable section

open Matrix

namespace SICLean.L2a

def phasedD (M : ℕ) (i j : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  theta M i j • D M (toWH i j)

def residueD (M : ℕ) (h : Index M) : Matrix (Fin M) (Fin M) ℂ :=
  phasedD M h.1.val h.2.val

def indexEquiv (M : ℕ) [NeZero M] : (Fin M × Fin M) ≃ Index M where
  toFun p := ((p.1 : ℕ), (p.2 : ℕ))
  invFun h := (finIdx M h.1, finIdx M h.2)
  left_inv p := by
    apply Prod.ext <;> apply fin_ext_of_label <;> apply label_finIdx
  right_inv h := by
    exact Prod.ext (label_finIdx M h.1) (label_finIdx M h.2)

theorem sum_fin_index {M : ℕ} [NeZero M] {A : Type*} [AddCommMonoid A]
    (f : Index M → A) :
    (∑ i : Fin M, ∑ j : Fin M, f ((i : ℕ), (j : ℕ))) = ∑ h : Index M, f h := by
  rw [← Fintype.sum_prod_type']
  exact (indexEquiv M).sum_comp f

theorem phasedD_eq_of_cast_eq {M : ℕ} (hM : 4 ≤ M) (i j k l : ℤ)
    (hi : (i : ZMod M) = (k : ZMod M)) (hj : (j : ZMod M) = (l : ZMod M)) :
    phasedD M i j = phasedD M k l := by
  obtain ⟨a, ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k i M).mp hi.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub l j M).mp hj.symm
  have hi' : i = k + (M : ℤ) * a := by linear_combination ha
  have hj' : j = l + (M : ℤ) * b := by linear_combination hb
  rw [hi', hj']
  exact phased_displacement_add_period hM k l a b

theorem residueD_eq_phasedD {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
    residueD M ((i : ZMod M), (j : ZMod M)) = phasedD M i j := by
  haveI : NeZero M := ⟨by omega⟩
  apply phasedD_eq_of_cast_eq hM <;> simp

theorem phasedD_zero (M : ℕ) : phasedD M 0 0 = 1 := by
  simp [phasedD, theta_eq_xi_zpow, quadraticForm, toWH, D_zero]

theorem residueD_zero (M : ℕ) : residueD M 0 = 1 := by
  simpa [residueD] using phasedD_zero M

theorem phasedD_mul (M : ℕ) (i j r s : ℤ) :
    phasedD M i j * phasedD M (r - i) (s - j) =
      (gaussianLift M i j * e M (-i * r + j * (r - s))) • phasedD M r s := by
  simp only [phasedD, Matrix.smul_mul, Matrix.mul_smul, D_mul_D, smul_smul]
  have ht : toWH i j + toWH (r - i) (s - j) = toWH r s := by
    ext <;> simp [toWH] <;> ring
  rw [ht]
  congr 1
  simp only [theta_eq_xi_zpow, gaussianLift, e_eq_omega_zpow, omega_zpow,
    ← zpow_add₀ (xi_ne_zero M)]
  congr 1
  dsimp [quadraticForm, toWH]
  ring

theorem P_eq_sum_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (F : Values M) :
    P M F = (M : ℂ)⁻¹ • ∑ h : Index M, F h • residueD M h := by
  rw [P, ← sum_fin_index]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [residueD, ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt,
    phasedD, valueAt, smul_smul, Int.cast_natCast, mul_comm]

theorem isZeroLabel_iff_cast {M : ℕ} (i j : ℤ) :
    IsZeroLabel M (i, j) ↔ ((i : ZMod M), (j : ZMod M)) = 0 := by
  change (_ ∧ _) ↔ ((i : ZMod M), (j : ZMod M)) = (0, 0)
  simp only [IsZeroLabel, Prod.mk.injEq, Prod.fst_zero, Prod.snd_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem isZeroLabel_toWH {M : ℕ} (i j : ℤ) :
    IsZeroLabel M (toWH i j) ↔ IsZeroLabel M (i, j) := by
  simp only [IsZeroLabel, toWH, dvd_neg, and_comm]

def convolutionKernel (M : ℕ) (u r : Index M) : ℂ :=
  gaussianLift M u.1.val u.2.val *
    e M (-(u.1.val : ℤ) * r.1.val + (u.2.val : ℤ) * (r.1.val - r.2.val))

theorem residueD_mul_sub {M : ℕ} [NeZero M] (hM : 4 ≤ M) (u r : Index M) :
    residueD M u * residueD M (r - u) =
      convolutionKernel M u r • residueD M r := by
  have hr : r - u =
      ((((r.1.val : ℤ) - u.1.val : ℤ) : ZMod M),
        (((r.2.val : ℤ) - u.2.val : ℤ) : ZMod M)) := by
    ext <;> simp
  rw [hr, residueD_eq_phasedD hM]
  exact phasedD_mul M u.1.val u.2.val r.1.val r.2.val

theorem convolution_eq_sum_index {M : ℕ} [NeZero M] (F : Values M) (r : Index M) :
    convolution M F r.1.val r.2.val =
      (M : ℂ)⁻¹ * ∑ u : Index M, F u * F (r - u) * convolutionKernel M u r := by
  rcases r with ⟨r, s⟩
  rw [convolution, ← sum_fin_index]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [valueAt, convolutionKernel, ZMod.val_cast_of_lt i.isLt,
    ZMod.val_cast_of_lt j.isLt, mul_assoc]

theorem trace_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (h : Index M) :
    (residueD M h).trace = if h = 0 then (M : ℂ) else 0 := by
  classical
  by_cases hh : h = 0
  · simp [hh, residueD_zero, Matrix.trace_one]
  · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val) := by
      rw [isZeroLabel_toWH, isZeroLabel_iff_cast]
      simpa using hh
    rw [residueD, phasedD, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
    simp

theorem ov_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M)
    (h : Index M) (i j : ℤ) :
    ov M (residueD M h) (toWH i j) =
      if h = ((i : ZMod M), (j : ZMod M)) then theta M i j * (M : ℂ) else 0 := by
  classical
  by_cases hh : h = ((i : ZMod M), (j : ZMod M))
  · rw [hh, residueD_eq_phasedD hM]
    simp [ov, phasedD, Matrix.smul_mul, D_mul_conjTranspose_D, Matrix.trace_smul,
      Matrix.trace_one]
  · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val + -(toWH i j)) := by
      intro hz
      apply hh
      have hz' := (isZeroLabel_iff_cast _ _).mp hz
      have h₁ := congrArg Prod.fst hz'
      have h₂ := congrArg Prod.snd hz'
      simp [toWH] at h₁ h₂
      apply Prod.ext <;> dsimp
      · linear_combination h₂
      · linear_combination -h₁
    rw [residueD, phasedD, ov, Matrix.smul_mul, conjTranspose_D, D_mul_D,
      Matrix.trace_smul, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
    simp

theorem ov_P_toWH {M : ℕ} (hM : 4 ≤ M) (F : Values M) (i j : ℤ) :
    ov M (P M F) (toWH i j) = theta M i j * valueAt F i j := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [P_eq_sum_residueD hM]
  simp only [ov, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
    smul_eq_mul]
  change (M : ℂ)⁻¹ * ∑ h : Index M, F h * ov M (residueD M h) (toWH i j) = _
  simp_rw [ov_residueD hM]
  simp [mul_ite, Finset.sum_ite_eq', valueAt, hn, mul_comm, mul_left_comm, mul_assoc]

end SICLean.L2a
end
end

-- SICLean.L2a.Quadratic
section
noncomputable section

open Matrix

namespace SICLean.L2a

theorem P_mul_P {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    P M F * P M F = convolutionScalar M • P M F + 1 := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hprod : P M F * P M F =
      (M : ℂ)⁻¹ • ∑ r : Index M, (convolution M F r.1.val r.2.val) • residueD M r := by
    calc
      _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : Index M, ∑ v : Index M,
          (F u * F v) • (residueD M u * residueD M v)) := by
        simp only [P_eq_sum_residueD hM, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum, smul_smul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : Index M, ∑ r : Index M,
          (F u * F (r - u) * convolutionKernel M u r) • residueD M r) := by
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        apply Fintype.sum_equiv (Equiv.addLeft u)
        intro v
        change (F u * F v) • (residueD M u * residueD M v) =
          (F u * F (u + v - u) * convolutionKernel M u (u + v)) • residueD M (u + v)
        have hm := residueD_mul_sub hM u (u + v)
        simp only [add_sub_cancel_left] at hm ⊢
        rw [hm, smul_smul]
      _ = (M : ℂ)⁻¹ • ∑ r : Index M,
          ((M : ℂ)⁻¹ * ∑ u : Index M, F u * F (r - u) * convolutionKernel M u r) •
            residueD M r := by
        rw [Finset.sum_comm]
        simp only [mul_smul, Finset.smul_sum, Finset.sum_smul]
      _ = _ := by simp_rw [convolution_eq_sum_index]
  rw [hprod]
  simp_rw [hA.convolution_eq]
  rw [P_eq_sum_residueD hM]
  simp [add_smul, ite_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    residueD_zero, hn, mul_comm, mul_left_comm, mul_assoc]

theorem P_quadratic {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
      (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) = 0 := by
  have hν := sqrtEpsilon_ne_zero hM
  have hc := sqrtEpsilon_sub_inv hM
  have hprod := P_mul_P hM hA
  calc
    _ = (P M F * P M F - convolutionScalar M • P M F) - 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [← hc]
      simp only [sub_smul, mul_inv_cancel₀ hν, one_smul]
      match_scalars <;> simp [hν] <;> ring
    _ = 0 := by rw [hprod]; abel

theorem trace_P {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : (P M F).trace = sqrtEpsilon M ^ 3 := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [P_eq_sum_residueD hM]
  simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp_rw [trace_residueD hM]
  simp [mul_ite, hA.origin, hn, mul_assoc, mul_comm, mul_left_comm]

end SICLean.L2a
end
end

-- SICLean.L2a.Ghost
section
noncomputable section

open Matrix

namespace SICLean.L2a

theorem denominator_sq {M : ℕ} (hM : 4 ≤ M) :
    denominator M ^ 2 = (M : ℂ) + 1 := by
  rw [denominator_eq_sqrt hM]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
  exact_mod_cast hs

theorem rsicConst_one {M : ℕ} (hM : 4 ≤ M) :
    rsicConst M 1 = ((M : ℝ) + 1)⁻¹ := by
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hn : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  simp only [rsicConst, Nat.cast_one, one_mul]
  field_simp
  <;> ring

theorem ghostProjector_idempotent {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    ghostProjector M F * ghostProjector M F = ghostProjector M F := by
  have hs := denominator_ne_zero hM
  have hq :
      (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
          (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) =
        denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
    have he :
        (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
            (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) =
          (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
              (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) -
            denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, denominator]
      module
    rw [P_quadratic hM hA] at he
    exact sub_eq_zero.mp he.symm
  simp only [ghostProjector, Matrix.smul_mul, Matrix.mul_smul, hq, smul_smul]
  simp [mul_assoc, hs]

theorem trace_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : (ghostProjector M F).trace = 1 := by
  have hs := denominator_ne_zero hM
  have ht : sqrtEpsilon M * (M : ℂ) - sqrtEpsilon M ^ 3 = denominator M := by
    rw [sqrtEpsilon_cube hM, denominator]
    ring
  simp only [ghostProjector, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, trace_P hM hA]
  rw [ht, inv_mul_cancel₀ hs]

theorem ghostProjector_residue_expansion {M : ℕ} [NeZero M] (hM : 4 ≤ M)
    {F : Values M} (hA : RWConvolutionInput M F) :
    ghostProjector M F = (M : ℂ)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ) +
      (M : ℂ)⁻¹ • ∑ h : Index M,
        if h = 0 then 0 else (-F h / denominator M) • residueD M h := by
  classical
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hs := denominator_ne_zero hM
  have ht : (M : ℂ) * sqrtEpsilon M - sqrtEpsilon M ^ 3 = denominator M := by
    rw [sqrtEpsilon_cube hM, denominator]
    ring
  have hall : (∑ h : Index M, (-F h / denominator M) • residueD M h) =
      (-(denominator M)⁻¹) • ∑ h : Index M, F h • residueD M h := by
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    ring
  have hterm (h : Index M) :
      (if h = 0 then 0 else (-F h / denominator M) • residueD M h) =
        (-F h / denominator M) • residueD M h -
          if h = 0 then (-F 0 / denominator M) • residueD M 0 else 0 := by
    by_cases hh : h = 0 <;> simp [hh]
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, residueD_zero, hA.origin, hall]
  rw [ghostProjector, P_eq_sum_residueD hM]
  match_scalars <;> field_simp [hn, hs] <;> linear_combination ht

theorem ghostProjector_expansion {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) :
    ghostProjector M F = (M : ℂ)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ) +
      (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
        if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 0
        else coefficient M F i j • D M (toWH i j) := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  rw [ghostProjector_residue_expansion hM hA, ← sum_fin_index]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hz : (((i : ℕ) : ZMod M), ((j : ℕ) : ZMod M)) = (0 : Index M) ↔
      (i : ℕ) = 0 ∧ (j : ℕ) = 0 := by
    change ((_, _) = (0, 0)) ↔ _
    simp only [Prod.mk.injEq, ZMod.natCast_eq_zero_iff]
    constructor
    · rintro ⟨hi, hj⟩
      exact ⟨Nat.eq_zero_of_dvd_of_lt hi i.isLt, Nat.eq_zero_of_dvd_of_lt hj j.isLt⟩
    · rintro ⟨hi, hj⟩
      simp [hi, hj]
  rw [if_congr hz rfl rfl]
  split_ifs
  · rfl
  · simp only [residueD, ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt,
      phasedD, coefficient, valueAt, Int.cast_natCast, smul_smul]
    congr 1
    ring

theorem coefficient_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
    coefficient M F i j * coefficient M F (-i) (-j) = ((M : ℂ) + 1)⁻¹ := by
  have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
    mt (isZeroLabel_iff_cast i j).mpr hij
  have hr := hA.reflection ((i : ZMod M), (j : ZMod M)) hh
  have hr' : valueAt F i j * valueAt F (-i) (-j) = (gaussianLift M i j)⁻¹ := by
    simpa only [valueAt, Prod.neg_mk, Int.cast_neg, gaussian_eq_lift hM] using hr
  have hg : gaussianLift M i j ≠ 0 := Complex.exp_ne_zero _
  rw [coefficient, coefficient, theta_neg]
  calc
    _ = (theta M i j ^ 2 * (valueAt F i j * valueAt F (-i) (-j))) /
        denominator M ^ 2 := by ring
    _ = _ := by rw [theta_sq, hr', denominator_sq hM, mul_inv_cancel₀ hg, one_div]

theorem coefficient_add_period {M : ℕ} (hM : 4 ≤ M) (F : Values M) (i j a b : ℤ) :
    coefficient M F (i + (M : ℤ) * a) (j + (M : ℤ) * b) =
      (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * coefficient M F i j := by
  unfold coefficient
  rw [theta_add_period hM]
  have hv : valueAt F (i + (M : ℤ) * a) (j + (M : ℤ) * b) = valueAt F i j := by
    simp [valueAt]
  rw [hv]
  ring

theorem ov_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
    ov M (ghostProjector M F) p = coefficient M F (fromWH p).1 (fromWH p).2 := by
  haveI : NeZero M := ⟨by omega⟩
  have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
  have hov := ov_P_toWH hM F (fromWH p).1 (fromWH p).2
  have hback : toWH (fromWH p).1 (fromWH p).2 = p := by simp [toWH, fromWH]
  rw [hback] at hov
  simp only [ghostProjector, ov, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  rw [conjTranspose_D, trace_D, if_neg hpneg]
  rw [← conjTranspose_D p]
  change (denominator M)⁻¹ * (sqrtEpsilon M * 0 - ov M (P M F) p) = _
  rw [hov]
  simp [coefficient, div_eq_mul_inv, mul_comm]

theorem ov_ghostProjector_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
    ov M (ghostProjector M F) p * ov M (ghostProjector M F) (-p) =
      (rsicConst M 1 : ℂ) := by
  have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
  have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
    simpa [fromWH, IsZeroLabel, and_comm] using hp
  rw [ov_ghostProjector hM hA p hp, ov_ghostProjector hM hA (-p) hpneg]
  change coefficient M F (fromWH p).1 (fromWH p).2 *
      coefficient M F (-(fromWH p).1) (-(fromWH p).2) = _
  rw [coefficient_mul_neg hM hA _ _ hf, rsicConst_one hM]
  push_cast
  rfl

theorem isGhost_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) : IsGhost M 1 (ghostProjector M F) := by
  exact ⟨ghostProjector_idempotent hM hA, by simpa using trace_ghostProjector hM hA,
    ov_ghostProjector_mul_neg hM hA⟩

end SICLean.L2a
end
end

-- SICLean.L2a.Main
section
noncomputable section

open OpenQuantumProblem23

namespace SICLean.L2a

theorem map_coefficient_normSq {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ)
    (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
    Complex.normSq (τ (coefficient M F i j)) = rsicConst M 1 := by
  have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
    mt (isZeroLabel_iff_cast i j).mpr hij
  have hF : ‖τ (valueAt F i j)‖ = 1 := hB.norm_F _ hh
  have hd : Complex.normSq (τ (denominator M)) = (M : ℝ) + 1 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
    rcases map_denominator_eq_or_neg hM τ with h | h
    · rw [h, Complex.normSq_ofReal]
      nlinarith
    · rw [h, Complex.normSq_neg, Complex.normSq_ofReal]
      nlinarith
  rw [coefficient, map_div₀, map_neg, map_mul, Complex.normSq_div,
    Complex.normSq_neg, Complex.normSq_mul, hd]
  simp only [Complex.normSq_eq_norm_sq, map_theta_norm hM τ, hF, one_pow, one_mul,
    rsicConst_one hM, one_div]

theorem unimodularFlip_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
    UnimodularFlip M 1 (ghostProjector M F) τ := by
  intro p hp
  have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
    simpa [fromWH, IsZeroLabel, and_comm] using hp
  rw [ov_ghostProjector hM hA p hp]
  exact map_coefficient_normSq hM hB _ _ hf

end SICLean.L2a

namespace SICLean

open L2a

theorem ghostGaloisInput_of_RW {M : ℕ} (hM : 4 ≤ M) {F : Values M}
    (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
    GhostGaloisInput M 1 := by
  exact ⟨ghostProjector M F, isGhost_of_RW hM hA, τ, unimodularFlip_of_RW hM hA hB⟩

end SICLean
end
end

open SICLean
open OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1

private theorem e_eq_char (i : ℤ) :
    L2a.e 68 i = ZMod.stdAddChar (i : ZMod 68) := by
  rw [ZMod.stdAddChar_coe]
  rfl

private theorem gauss_eq_char (i j : ℤ) :
    L2a.gaussianLift 68 i j =
    ZMod.stdAddChar ((i : ZMod 68)^2 - (i : ZMod 68)*(j : ZMod 68) + (j : ZMod 68)^2) := by
  rw [L2a.gaussianLift, e_eq_char]
  simp [L2a.quadraticForm]

private def residueIndex : ZMod 68 ≃ Fin 68 := (ZMod.finEquiv 68).toEquiv.symm

private theorem residueIndex_val (i : ZMod 68) : (residueIndex i).val = i.val := rfl

private theorem liftVal (t : ZMod 68) : ((t.val : ℤ) : ZMod 68) = t := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem trace_residues (A : Matrix (Fin 68) (Fin 68) ℂ) :
    (A.submatrix residueIndex residueIndex).trace = A.trace :=
  residueIndex.sum_comp (fun i => A i i)

private theorem fourier_diagonal (A : Matrix (Fin 68) (Fin 68) ℂ) (a b : ZMod 68) :
    Complex.normSq (∑ t, (A.submatrix residueIndex residueIndex) (t+a) t * ZMod.stdAddChar (b*t)) =
    Complex.normSq (ov 68 A ((a.val : ℤ),-(b.val : ℤ))) := by
  let z := star (xi 68 ^ ((a.val : ℤ) * -(b.val : ℤ)))
  have hz : Complex.normSq z = 1 := by
    unfold z
    rw [Complex.star_def, Complex.normSq_conj, Complex.normSq_eq_norm_sq, norm_zpow]
    have hu : ‖xi 68‖ = 1 := by simp [xi, Complex.norm_exp]
    simp [hu]
  have chars (t : ZMod 68) :
      star (omega 68 ^ (-(b.val : ℤ) * (t.val : ℤ))) = ZMod.stdAddChar (b*t) := by
    rw [omega_exp]
    change star (L2a.e 68 (-(b.val : ℤ) * (t.val : ℤ))) = _
    rw [e_eq_char]
    simp only [Int.cast_mul, Int.cast_neg, liftVal]
    rw [neg_mul, AddChar.map_neg_eq_inv]
    change star ((ZMod.toCircle (b*t) : ℂ)⁻¹) = _
    rw [star_inv₀]
    change (starRingEnd ℂ (ZMod.toCircle (b*t) : ℂ))⁻¹ = _
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]
    rfl
  have hsum : ov 68 A ((a.val : ℤ),-(b.val : ℤ)) =
      z * ∑ t, (A.submatrix residueIndex residueIndex) (t+a) t * ZMod.stdAddChar (b*t) := by
    unfold ov
    rw [← trace_residues, ← Matrix.submatrix_mul_equiv _ _ residueIndex residueIndex residueIndex]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change (∑ i : ZMod 68, A (residueIndex i) (residueIndex t) * star (D 68 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex i) (residueIndex t))) = _
    rw [Finset.sum_eq_single (t+a)]
    · have hD : D 68 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex (t+a)) (residueIndex t) =
            xi 68 ^ ((a.val : ℤ) * -(b.val : ℤ)) *
              omega 68 ^ (-(b.val : ℤ) * (t.val : ℤ)) := by
        simp only [D, residueIndex_val, liftVal, if_true]
      rw [hD, star_mul, chars]
      dsimp [z]
      ring
    · intro i _ hi
      have hD : D 68 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex i) (residueIndex t) = 0 := by
        simp only [D, residueIndex_val, liftVal, if_neg hi]
      rw [hD, star_zero, mul_zero]
    · simp
  rw [hsum, Complex.normSq_mul, hz, one_mul]

private theorem convolution_residues (F : ZMod 68 → ZMod 68 → ℂ) (r s : ZMod 68) :
    L2a.convolution 68 (fun h => F h.1 h.2) r.val s.val =
      (68 : ℂ)⁻¹ * ∑ i : ZMod 68, ∑ j : ZMod 68, F i j * F (r-i) (s-j) *
        ZMod.stdAddChar (i^2-i*j+j^2) * ZMod.stdAddChar (-i*r+j*(r-s)) := by
  unfold L2a.convolution
  congr 1
  rw [← residueIndex.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← residueIndex.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [L2a.valueAt, Function.comp_apply, gauss_eq_char, e_eq_char, Int.cast_neg,
    Int.cast_mul, Int.cast_sub, Int.cast_add, residueIndex_val, liftVal]

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1.H2 := by
  classical
  intro F τ hzero hreflect hconv hcircle
  let f : L2a.Values 68 := fun h => F h.1 h.2
  have hA : L2a.RWConvolutionInput 68 f := by
    constructor
    · convert hzero using 1 <;> norm_num [f, L2a.sqrtEpsilon, L2a.epsilon]
    · rintro ⟨i,j⟩ hij
      simpa [f, L2a.gaussian, gauss_eq_char] using hreflect i j hij
    · rintro ⟨r,s⟩
      change L2a.convolution 68 f r.val s.val = _
      rw [show L2a.convolution 68 f r.val s.val = _ from convolution_residues F r s]
      by_cases h : (r,s) = ((0,0) : ZMod 68 × ZMod 68)
      · have hz : (r,s) = (0 : L2a.Index 68) := h
        simpa only [L2a.convolutionScalar, Nat.cast_ofNat, show (68:ℝ)-3=65 by norm_num, f,
          if_pos h, if_pos hz] using hconv r s
      · have hz : (r,s) ≠ (0 : L2a.Index 68) := h
        simpa only [L2a.convolutionScalar, Nat.cast_ofNat, show (68:ℝ)-3=65 by norm_num, f,
          if_neg h, if_neg hz] using hconv r s
  have hB : L2a.RWUnitCircleInput 68 f τ := ⟨fun h hh => hcircle h.1 h.2 hh⟩
  obtain ⟨G, hG, θ, hθ⟩ := ghostGaloisInput_of_RW (by decide : 4 ≤ 68) hA hB
  obtain ⟨hH, hP, ht, hflat⟩ := map_fiducial_of_ghost_flip (by decide : 2 ≤ 68)
    (by decide : 1 ≤ 1) (by decide : 1 < 68) hG hθ
  refine ⟨(G.map θ).submatrix residueIndex residueIndex, hH.submatrix _, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hP]
  · rw [trace_residues, ht, Nat.cast_one]
  intro a b hab
  rw [fourier_diagonal (G.map θ) a b]
  have hn : ¬IsZeroLabel 68 ((a.val : ℤ), -(b.val : ℤ)) := by
    rintro ⟨ha,hb⟩
    apply hab
    have ha0 : a.val = 0 := by have := a.val_lt; omega
    have hb0 : b.val = 0 := by have := b.val_lt; omega
    exact Prod.ext (ZMod.val_injective 68 (by simpa using ha0))
      (ZMod.val_injective 68 (by simpa using hb0))
  convert hflat _ hn using 1 <;> norm_num [rsicConst]
