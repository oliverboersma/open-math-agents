import FormalConjectures.Wikipedia.SixStandardDeviations
import Mathlib

namespace SpencerBP

noncomputable section

open Real

/-! Definitions communes (variante a barriere simplifiee, voir blueprint.md section 1). -/

variable {ι : Type} [Fintype ι] {n : ℕ}

/-- produit scalaire concret sur `Fin n → ℝ` -/
def dotv (a z : Fin n → ℝ) : ℝ := ∑ j, a j * z j

/-- R(z) = n - |z|^2 -/
def Rr (z : Fin n → ℝ) : ℝ := (n : ℝ) - ∑ j, z j ^ 2

/-- s(z) = R(z) - 4 -/
def ss (z : Fin n → ℝ) : ℝ := Rr z - 4

/-- Delta = 4.1 sqrt n -/
def Dl (n : ℕ) : ℝ := 41 / 10 * √(n : ℝ)

/-- jeu de la ligne i : Delta - <a_i, z> -/
def gap (a : ι → Fin n → ℝ) (z : Fin n → ℝ) (i : ι) : ℝ := Dl n - dotv (a i) z

/-- barriere en t : phi(t) = 64 e^{-t^2/8} / t^2 -/
def phi (t : ℝ) : ℝ := 64 * exp (-(t ^ 2) / 8) / t ^ 2

/-- phi' (derivee en t) -/
def phi1 (t : ℝ) : ℝ := 64 * exp (-(t ^ 2) / 8) * (-2 / (8 * t) - 2 / t ^ 3)

/-- phi'' (derivee seconde en t) -/
def phi2 (t : ℝ) : ℝ := 64 * exp (-(t ^ 2) / 8) * (4 / 64 + 6 / (8 * t ^ 2) + 6 / t ^ 4)

/-- psi(t) = -t phi'(t) - 2 phi(t) = 16 e^{-t^2/8} -/
def psi (t : ℝ) : ℝ := 16 * exp (-(t ^ 2) / 8)

/-- t_i = gap_i / sqrt s -/
def tt (a : ι → Fin n → ℝ) (z : Fin n → ℝ) (i : ι) : ℝ := gap a z i / √(ss z)

/-- potentiel Phi(z) = (1/s) sum_i phi(t_i) (significatif pour s > 0 et jeux > 0) -/
def Phi (a : ι → Fin n → ℝ) (z : Fin n → ℝ) : ℝ := (∑ i, phi (tt a z i)) / ss z

/-- region ouverte (s > 0, jeux > 0) dans le cube -/
def Kopen (a : ι → Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | (∀ j, |z j| ≤ 1) ∧ 0 < ss z ∧ ∀ i, 0 < gap a z i}

/-- region fermee (s >= 0, jeux >= 0) dans le cube -/
def Kcl (a : ι → Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | (∀ j, |z j| ≤ 1) ∧ 0 ≤ ss z ∧ ∀ i, 0 ≤ gap a z i}

section
variable {n : ℕ}

theorem A_exp2 (y : ℝ) (hy : 0 ≤ y) : exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have key : MonotoneOn (fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      have h : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y)) (-1 + x + exp (-x)) x := by
        have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          simpa using (hasDerivAt_pow 2 x).div_const 2
        have h3 : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
          simpa using (hasDerivAt_neg x).exp
        exact ((h1.add h2).sub h3).congr_deriv (by ring)
      rw [h.deriv]
      have := Real.add_one_le_exp (-x)
      linarith
  have := key (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp at this
  linarith

end

section
variable {n : ℕ}

theorem A_exp3 (y : ℝ) (hy : 0 ≤ y) : 1 - y + y ^ 2 / 2 - y ^ 3 / 6 ≤ exp (-y) := by
  have key : MonotoneOn (fun y : ℝ => exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro x hx
      have hx' : 0 ≤ x := le_of_lt (by simpa using hx)
      have h : HasDerivAt (fun y : ℝ => exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6))
          (-exp (-x) + 1 - x + x ^ 2 / 2) x := by
        have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          simpa using (hasDerivAt_pow 2 x).div_const 2
        have h2' : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (3 * x ^ 2 / 6) x := by
          simpa using (hasDerivAt_pow 3 x).div_const 6
        have h3 : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
          simpa using (hasDerivAt_neg x).exp
        exact (h3.sub ((h1.add h2).sub h2')).congr_deriv (by ring)
      rw [h.deriv]
      have := A_exp2 x hx'
      linarith
  have := key (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp at this
  linarith

-- polynome : x in (0,11), E >= cubique

end

section
variable {n : ℕ}

theorem A_poly (x : ℝ) (h0 : 0 < x) (h1 : x < 11) :
    0 ≤ x ^ 3 - 6 * x ^ 2 - 48 * x + (8 * x ^ 2 + 96 * x + 768) *
      (1 - x / 8 + (x / 8) ^ 2 / 2 - (x / 8) ^ 3 / 6) := by
  nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 8), mul_pos h0 h0, mul_pos h0 (sub_pos.2 h1),
    mul_pos (mul_pos h0 h0) (sub_pos.2 h1), sq_nonneg (x ^ 2 - 20 * x)]

end

section
variable {n : ℕ}

theorem phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t := by
  unfold phi; positivity

end

section
variable {n : ℕ}

theorem hasDerivAt_phi {t : ℝ} (ht : 0 < t) : HasDerivAt phi (phi1 t) t := by
  have h1 : HasDerivAt (fun s : ℝ => exp (-(s ^ 2) / 8)) (exp (-(t ^ 2) / 8) * (-(2 * t) / 8)) t := by
    have := ((hasDerivAt_pow 2 t).neg.div_const 8).exp
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h3 := (h1.const_mul 64).div h2 (by positivity)
  have h4 : phi = fun s : ℝ => 64 * exp (-(s ^ 2) / 8) / s ^ 2 := rfl
  rw [h4]
  refine h3.congr_deriv ?_
  unfold phi1
  field_simp

end

section
variable {n : ℕ}

theorem hasDerivAt_phi1 {t : ℝ} (ht : 0 < t) : HasDerivAt phi1 (phi2 t) t := by
  have h1 : HasDerivAt (fun s : ℝ => exp (-(s ^ 2) / 8)) (exp (-(t ^ 2) / 8) * (-(2 * t) / 8)) t := by
    have := ((hasDerivAt_pow 2 t).neg.div_const 8).exp
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => -2 / (8 * s) - 2 / s ^ 3)
      (2 / (8 * t ^ 2) + 6 / t ^ 4) t := by
    have a1 : HasDerivAt (fun s : ℝ => 8 * s) 8 t := by simpa using (hasDerivAt_id t).const_mul 8
    have a2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
    have b1 := (hasDerivAt_const t (-2 : ℝ)).div a1 (by positivity)
    have b2 := (hasDerivAt_const t (2 : ℝ)).div a2 (by positivity)
    refine (b1.sub b2).congr_deriv ?_
    field_simp
    ring
  have h3 := (h1.const_mul 64).mul h2
  have h4 : phi1 = fun s : ℝ => 64 * exp (-(s ^ 2) / 8) * (-2 / (8 * s) - 2 / s ^ 3) := rfl
  rw [h4]
  refine h3.congr_deriv ?_
  unfold phi2
  field_simp
  ring

end

section
variable {n : ℕ}

theorem phi2_pos {t : ℝ} (ht : 0 < t) : 0 < phi2 t := by
  unfold phi2; positivity

end

section
variable {n : ℕ}

theorem psi_eq {t : ℝ} (ht : 0 < t) : -t * phi1 t - 2 * phi t = psi t := by
  unfold phi1 phi psi
  field_simp
  ring

end

section
variable {n : ℕ}

theorem psi_pos (t : ℝ) : 0 < psi t := by
  unfold psi; positivity

end

section
variable {n : ℕ}

theorem A_key {t : ℝ} (ht : 0 < t) :
    (1 - phi t / 4) * phi2 t ≤ 3 / 4 * psi t := by
  set x := t ^ 2 with hx
  have hx0 : 0 < x := by positivity
  set E := exp (-(t ^ 2) / 8) with hE
  have hE0 : 0 < E := exp_pos _
  have H : 0 ≤ x ^ 3 - 6 * x ^ 2 - 48 * x + E * (8 * x ^ 2 + 96 * x + 768) := by
    rcases lt_or_ge x 11 with h | h
    · have e3 := A_exp3 (x / 8) (by positivity)
      have e3' : 1 - x / 8 + (x / 8) ^ 2 / 2 - (x / 8) ^ 3 / 6 ≤ E := by
        have : -(t ^ 2) / 8 = -(x / 8) := by rw [hx]; ring
        rw [hE, this]; exact e3
      have hp := A_poly x hx0 h
      have hq : 0 < 8 * x ^ 2 + 96 * x + 768 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left e3' hq.le]
    · have : 0 ≤ x ^ 3 - 6 * x ^ 2 - 48 * x := by nlinarith [mul_pos hx0 hx0]
      have : 0 ≤ E * (8 * x ^ 2 + 96 * x + 768) := by positivity
      linarith
  have eq : 3 / 4 * psi t - (1 - phi t / 4) * phi2 t
      = 8 * E * (x ^ 3 - 6 * x ^ 2 - 48 * x + E * (8 * x ^ 2 + 96 * x + 768)) / (x ^ 3) := by
    unfold psi phi phi2
    rw [← hE]
    have h4 : t ^ 4 = x ^ 2 := by rw [hx]; ring
    have h8 : 8 * t ^ 2 = 8 * x := by rw [hx]
    rw [h4, h8, ← hx]
    field_simp
    ring
  have : 0 ≤ 8 * E * (x ^ 3 - 6 * x ^ 2 - 48 * x + E * (8 * x ^ 2 + 96 * x + 768)) / (x ^ 3) := by
    positivity
  linarith

end

section
variable {n : ℕ}

theorem phi_capped {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    min (phi2 t) θ ≤ 3 / 4 * psi t + 1 / 4 * θ * phi t := by
  have hp := phi_pos ht
  have hps := psi_pos t
  rcases le_or_gt 4 (phi t) with h | h
  · have : min (phi2 t) θ ≤ θ := min_le_right _ _
    nlinarith
  · have hk := A_key ht
    have hl : 0 ≤ 1 - phi t / 4 := by linarith
    have : min (phi2 t) θ ≤ (1 - phi t / 4) * phi2 t + phi t / 4 * θ := by
      have a := mul_le_mul_of_nonneg_left (min_le_left (phi2 t) θ) hl
      have b := mul_le_mul_of_nonneg_left (min_le_right (phi2 t) θ) (by linarith : 0 ≤ phi t / 4)
      nlinarith
    nlinarith

end

section
variable {n : ℕ}

theorem barrier_zero {n : ℕ} (hn : 5 ≤ n) :
    2 * (n : ℝ) * (64 * exp (-(Dl n) ^ 2 / (8 * ((n : ℝ) - 4))) / (Dl n) ^ 2) < 1 := by
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD : (Dl n) ^ 2 = 1681 / 100 * n := by
    unfold Dl
    rw [mul_pow, Real.sq_sqrt hn0.le]; norm_num
  have h4 : (0 : ℝ) < (n : ℝ) - 4 := by linarith
  have hexp : exp (-(Dl n) ^ 2 / (8 * ((n : ℝ) - 4))) ≤ exp (-(21 / 10)) := by
    apply Real.exp_le_exp.mpr
    rw [hD, div_le_iff₀ (by positivity)]
    nlinarith
  have hE : 8 < exp (21 / 10 : ℝ) := by
    have e1 := Real.exp_one_gt_d9
    have e2 : exp (21 / 10 : ℝ) = exp 1 * exp 1 * exp (1 / 10) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have e3 := Real.add_one_le_exp (1 / 10 : ℝ)
    rw [e2]
    nlinarith [Real.exp_pos 1]
  have hinv : exp (-(21 / 10 : ℝ)) < 1 / 8 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hE
  rw [hD]
  have : 2 * (n : ℝ) * (64 * exp (-(1681 / 100 * (n : ℝ)) / (8 * ((n : ℝ) - 4))) / (1681 / 100 * n))
      = 12800 / 1681 * exp (-(1681 / 100 * (n : ℝ)) / (8 * ((n : ℝ) - 4))) := by
    field_simp
    norm_num
  rw [this]
  have hexp' : exp (-(1681 / 100 * (n : ℝ)) / (8 * ((n : ℝ) - 4))) ≤ exp (-(21 / 10)) := by
    rw [← hD]; exact hexp
  nlinarith

end

open Filter Topology in
theorem C_second_test {F F1 : ℝ → ℝ} {F2 : ℝ}
    (hF : ∀ᶠ l in 𝓝 (0 : ℝ), HasDerivAt F (F1 l) l) (hF1 : HasDerivAt F1 F2 0)
    (hmin : IsLocalMin F 0) : 0 ≤ F2 := by
  by_contra hneg
  push_neg at hneg
  have hF0 : HasDerivAt F (F1 0) 0 := hF.self_of_nhds
  have hz : F1 0 = 0 := hmin.hasDerivAt_eq_zero hF0
  have hslope := hF1.tendsto_slope_zero_right
  have h1 : ∀ᶠ l in 𝓝[>] (0 : ℝ), l⁻¹ • (F1 (0 + l) - F1 0) < 0 :=
    hslope.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ l in 𝓝[>] (0 : ℝ), HasDerivAt F (F1 l) l ∧ F 0 ≤ F l ∧ F1 l < 0 := by
    filter_upwards [nhdsWithin_le_nhds hF, nhdsWithin_le_nhds hmin, h1, self_mem_nhdsWithin]
      with l hl1 hl2 hl3 hl4
    refine ⟨hl1, hl2, ?_⟩
    have hl : (0 : ℝ) < l := hl4
    simp only [zero_add, hz, sub_zero, smul_eq_mul] at hl3
    by_contra hcon
    push_neg at hcon
    have : 0 ≤ l⁻¹ * F1 l := mul_nonneg (inv_nonneg.mpr hl.le) hcon
    linarith
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp h2
  set η := u / 2 with hη
  have hηpos : 0 < η := by simp only [hη]; linarith [hu.out]
  have hηu : η < u := by simp only [hη]; linarith [hu.out]
  have hcont : ContinuousOn F (Set.Icc 0 η) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hF0.continuousAt.continuousWithinAt
    · exact (hsub ⟨h, lt_of_le_of_lt hx.2 hηu⟩).1.continuousAt.continuousWithinAt
  have hanti : StrictAntiOn F (Set.Icc 0 η) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 η) hcont fun x hx => ?_
    rw [interior_Icc] at hx
    have := hsub ⟨hx.1, lt_trans hx.2 hηu⟩
    rw [this.1.deriv]
    exact this.2.2
  have hlt := hanti ⟨le_refl 0, hηpos.le⟩ ⟨hηpos.le, le_refl η⟩ hηpos
  have := (hsub ⟨hηpos, hηu⟩).2.1
  linarith

open Filter Topology in
theorem C_single (G B s V : ℝ) (hG : 0 < G) (hs : 0 < s) :
    ∃ f1 : ℝ → ℝ,
      (∀ᶠ l in 𝓝 (0 : ℝ),
        HasDerivAt (fun l => phi ((G - l * B) / √(s - l ^ 2 * V)) / (s - l ^ 2 * V)) (f1 l) l) ∧
      HasDerivAt f1 ((phi2 (G / √s) * B ^ 2 - V * psi (G / √s)) / s ^ 2) 0 := by
  have hS : ∀ l : ℝ, HasDerivAt (fun l : ℝ => s - l ^ 2 * V) (-(2 * l * V)) l := by
    intro l
    have := ((hasDerivAt_pow 2 l).mul_const V).const_sub s
    refine this.congr_deriv ?_
    norm_num
  have hr : ∀ l : ℝ, 0 < s - l ^ 2 * V →
      HasDerivAt (fun l : ℝ => √(s - l ^ 2 * V)) (-(l * V) / √(s - l ^ 2 * V)) l := by
    intro l hl
    have := (hS l).sqrt hl.ne'
    refine this.congr_deriv ?_
    have : 0 < √(s - l ^ 2 * V) := Real.sqrt_pos.mpr hl
    field_simp
  have hN : ∀ l : ℝ, HasDerivAt (fun l : ℝ => G - l * B) (-B) l := by
    intro l
    have := ((hasDerivAt_id l).mul_const B).const_sub G
    simpa using this
  set T : ℝ → ℝ := fun l => (G - l * B) / √(s - l ^ 2 * V) with hTdef
  set T1 : ℝ → ℝ := fun l => -B / √(s - l ^ 2 * V)
      + (G - l * B) * (l * V) / (√(s - l ^ 2 * V)) ^ 3 with hT1def
  have hT : ∀ l : ℝ, 0 < s - l ^ 2 * V → HasDerivAt T (T1 l) l := by
    intro l hl
    have hq : 0 < √(s - l ^ 2 * V) := Real.sqrt_pos.mpr hl
    have := (hN l).div (hr l hl) hq.ne'
    refine this.congr_deriv ?_
    simp only [hT1def]
    field_simp
    ring
  have hT10 : HasDerivAt T1 (G * V / (√s) ^ 3) 0 := by
    have hq : 0 < √(s - 0 ^ 2 * V) := Real.sqrt_pos.mpr (by simpa using hs)
    have hr0 := hr 0 (by simpa using hs)
    have hpow := hr0.pow 3
    have e1 : HasDerivAt (fun l : ℝ => -B / √(s - l ^ 2 * V))
        ((0 * √(s - 0 ^ 2 * V) - (-B) * (-(0 * V) / √(s - 0 ^ 2 * V))) / (√(s - 0 ^ 2 * V)) ^ 2) 0 :=
      (hasDerivAt_const (0 : ℝ) (-B)).div hr0 hq.ne'
    have e2n : HasDerivAt (fun l : ℝ => (G - l * B) * (l * V))
        ((-B) * (0 * V) + (G - 0 * B) * (1 * V)) 0 :=
      (hN 0).mul (((hasDerivAt_id (0:ℝ)).mul_const V))
    have e2 := e2n.div hpow (pow_ne_zero 3 hq.ne')
    have := e1.add e2
    refine this.congr_deriv ?_
    have hs' : 0 < √s := Real.sqrt_pos.mpr hs
    simp
    field_simp
  have hs' : 0 < √s := Real.sqrt_pos.mpr hs
  have hT0 : T 0 = G / √s := by simp [hTdef]
  have hT10v : T1 0 = -B / √s := by simp [hT1def]
  have hpos0 : 0 < T 0 := by rw [hT0]; positivity
  have hS0 : 0 < s - 0 ^ 2 * V := by simpa using hs
  have hev1 : ∀ᶠ l in 𝓝 (0 : ℝ), 0 < s - l ^ 2 * V := by
    have hc : Continuous (fun l : ℝ => s - l ^ 2 * V) := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds hS0)
  have hev2 : ∀ᶠ l in 𝓝 (0 : ℝ), 0 < G - l * B := by
    have hc : Continuous (fun l : ℝ => G - l * B) := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hG))
  refine ⟨fun l => (phi1 (T l) * T1 l * (s - l ^ 2 * V) - phi (T l) * (-(2 * l * V)))
      / (s - l ^ 2 * V) ^ 2, ?_, ?_⟩
  · filter_upwards [hev1, hev2] with l hl1 hl2
    have hTp : 0 < T l := div_pos hl2 (Real.sqrt_pos.mpr hl1)
    exact ((hasDerivAt_phi hTp).comp l (hT l hl1)).div (hS l) hl1.ne'
  · have hp := (hasDerivAt_phi hpos0).comp 0 (hT 0 hS0)
    have hN1 := ((hasDerivAt_phi1 hpos0).comp 0 (hT 0 hS0)).mul hT10
    have hQ : HasDerivAt (fun l : ℝ => -(2 * l * V)) (-(2 * V)) 0 :=
      ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const V).neg).congr_deriv (by simp)
    have hnum := (hN1.mul (hS 0)).sub (hp.mul hQ)
    have hden := (hS 0).pow 2
    have hdiv := hnum.div hden (pow_ne_zero 2 hS0.ne')
    refine hdiv.congr_deriv ?_
    have ht0 : 0 < G / √s := by positivity
    rw [← psi_eq ht0]
    simp [hT0, hT10v]
    field_simp
    have hsq : √s ^ 2 = s := Real.sq_sqrt hs.le
    have h3 : √s ^ 3 = √s * s := by
      calc √s ^ 3 = √s * √s ^ 2 := by ring
        _ = √s * s := by rw [hsq]
    rw [h3, hsq]
    ring

open Filter Topology in
theorem second_order (a : ι → Fin n → ℝ) {z : Fin n → ℝ} (hz : z ∈ Kopen a)
    (hmin : ∀ w ∈ Kopen a, Phi a z ≤ Phi a w)
    (v : Fin n → ℝ) (hperp : ∑ j, z j * v j = 0) (hsupp : ∀ j, |z j| = 1 → v j = 0) :
    (∑ i, psi (tt a z i)) * ∑ j, v j ^ 2 ≤ ∑ i, phi2 (tt a z i) * (dotv (a i) v) ^ 2 := by
  classical
  set s := ss z with hsdef
  set V := ∑ j, v j ^ 2 with hVdef
  have hs : 0 < s := hz.2.1
  have hG : ∀ i, 0 < gap a z i := hz.2.2
  set zl : ℝ → Fin n → ℝ := fun l j => z j + l * v j with hzl
  have hss : ∀ l, ss (zl l) = s - l ^ 2 * V := by
    intro l
    have h1 : ∑ j, (z j + l * v j) ^ 2 = ∑ j, z j ^ 2 + 2 * l * ∑ j, z j * v j + l ^ 2 * V := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hsdef, ss, Rr, hzl]
    rw [h1, hperp]
    ring
  have hgp : ∀ l i, gap a (zl l) i = gap a z i - l * dotv (a i) v := by
    intro l i
    unfold gap dotv
    have : ∑ j, a i j * (z j + l * v j) = ∑ j, a i j * z j + l * ∑ j, a i j * v j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hzl]
    rw [this]; ring
  have hPhi : ∀ l, Phi a (zl l) = ∑ i, phi ((gap a z i - l * dotv (a i) v) / √(s - l ^ 2 * V))
        / (s - l ^ 2 * V) := by
    intro l
    unfold Phi tt
    rw [hss, Finset.sum_div]
    simp only [hgp]
  -- zl l dans Kopen pour l petit
  have hev_box : ∀ᶠ l in 𝓝 (0 : ℝ), ∀ j, |zl l j| ≤ 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : |z j| = 1
    · have := hsupp j hj
      exact Filter.Eventually.of_forall fun l => by simp [hzl, this, hj]
    · have hlt : |z j| < 1 := lt_of_le_of_ne (hz.1 j) hj
      have hc : Continuous (fun l : ℝ => |z j + l * v j|) := by fun_prop
      have := (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [this] with l hl using hl.le
  have hev_s : ∀ᶠ l in 𝓝 (0 : ℝ), 0 < s - l ^ 2 * V := by
    have hc : Continuous (fun l : ℝ => s - l ^ 2 * V) := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hs))
  have hev_g : ∀ᶠ l in 𝓝 (0 : ℝ), ∀ i, 0 < gap a z i - l * dotv (a i) v := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous (fun l : ℝ => gap a z i - l * dotv (a i) v) := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hG i))
  have hev_K : ∀ᶠ l in 𝓝 (0 : ℝ), zl l ∈ Kopen a := by
    filter_upwards [hev_box, hev_s, hev_g] with l h1 h2 h3
    refine ⟨h1, ?_, fun i => ?_⟩
    · rw [hss]; exact h2
    · rw [hgp]; exact h3 i
  have hz0 : zl 0 = z := by funext j; simp [hzl]
  have hlocal : IsLocalMin (fun l : ℝ => ∑ i, phi ((gap a z i - l * dotv (a i) v)
      / √(s - l ^ 2 * V)) / (s - l ^ 2 * V)) 0 := by
    filter_upwards [hev_K] with l hl
    have h := hmin _ hl
    rw [hPhi] at h
    have h0 := hPhi 0
    rw [hz0] at h0
    simp only [h0] at h
    simpa using h
  choose f1 hf1 hf1' using fun i =>
    C_single (gap a z i) (dotv (a i) v) s V (hG i) hs
  have hFd : ∀ᶠ l in 𝓝 (0 : ℝ), HasDerivAt (fun l : ℝ => ∑ i, phi ((gap a z i - l * dotv (a i) v)
      / √(s - l ^ 2 * V)) / (s - l ^ 2 * V)) (∑ i, f1 i l) l := by
    filter_upwards [Filter.eventually_all.2 hf1] with l hl
    exact HasDerivAt.fun_sum fun i _ => hl i
  have hFd' : HasDerivAt (fun l : ℝ => ∑ i, f1 i l)
      (∑ i, (phi2 (gap a z i / √s) * (dotv (a i) v) ^ 2 - V * psi (gap a z i / √s)) / s ^ 2) 0 :=
    HasDerivAt.fun_sum fun i _ => hf1' i
  have h2 := C_second_test hFd hFd' hlocal
  rw [← Finset.sum_div] at h2
  have hX := mul_nonneg h2 (sq_nonneg s)
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hs.ne'), Finset.sum_sub_distrib, ← Finset.mul_sum] at hX
  have htt : ∀ i, tt a z i = gap a z i / √s := fun i => rfl
  simp only [htt]
  linarith

theorem B_step1 [DecidableEq ι] (a : ι → Fin n → ℝ) (ha : ∀ i j, |a i j| ≤ 1) (J : Finset (Fin n))
    (H : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (L : ℝ)
    (W : Submodule ℝ (Fin n → ℝ)) (hWJ : ∀ v ∈ W, ∀ j, j ∉ J → v j = 0)
    (hWH : ∀ v ∈ W, ∀ i ∈ H, dotv (a i) v = 0)
    (hW : ∀ v ∈ W, L * ∑ j, v j ^ 2 ≤ ∑ i, w i * (dotv (a i) v) ^ 2) :
    L * (Module.finrank ℝ W : ℝ) ≤ (J.card : ℝ) * ∑ i, (if i ∈ H then 0 else w i) := by
  classical
  let T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
  have hTinj : Function.Injective T := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.injective
  let W' : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := W.map T
  have hdim : Module.finrank ℝ W' = Module.finrank ℝ W :=
    (Submodule.equivMapOfInjective T hTinj W).finrank_eq.symm
  let bs := stdOrthonormalBasis ℝ W'
  let e : Fin (Module.finrank ℝ W') → EuclideanSpace ℝ (Fin n) := fun k => (bs k : W')
  have horth : Orthonormal ℝ e := bs.orthonormal.comp_linearIsometry W'.subtypeₗᵢ
  let u : Fin (Module.finrank ℝ W') → (Fin n → ℝ) := fun k => (e k).ofLp
  have huW : ∀ k, u k ∈ W := by
    intro k
    obtain ⟨v, hv, hvT⟩ := (bs k).2
    have : u k = v := by
      have := congrArg WithLp.ofLp hvT
      simpa [u, e, T] using this.symm
    rw [this]; exact hv
  have hnorm : ∀ k, ∑ j, u k j ^ 2 = 1 := by
    intro k
    have h1 := horth.1 k
    rw [EuclideanSpace.norm_eq] at h1
    rw [Real.sqrt_eq_one] at h1
    simpa [u, Real.norm_eq_abs, sq_abs] using h1
  have hbess : ∀ i, ∑ k, (dotv (a i) (u k)) ^ 2 ≤ (J.card : ℝ) := by
    intro i
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => if j ∈ J then a i j else 0)
    have hB := horth.sum_inner_products_le x (s := Finset.univ)
    have hin : ∀ k, inner ℝ (e k) x = dotv (a i) (u k) := by
      intro k
      simp only [PiLp.inner_apply, dotv, x, u]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ J
      · simp [hj, mul_comm]
      · have := hWJ _ (huW k) j hj
        simp only [u] at this
        simp [hj, this]
    have hx : ‖x‖ ^ 2 ≤ (J.card : ℝ) := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      calc ∑ j, ‖x j‖ ^ 2 = ∑ j, (if j ∈ J then a i j ^ 2 else 0) := by
            apply Finset.sum_congr rfl; intro j _
            by_cases hj : j ∈ J <;> simp [x, hj, sq_abs]
        _ ≤ ∑ j, (if j ∈ J then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum; intro j _
            by_cases hj : j ∈ J
            · simp only [hj, if_true]
              have := ha i j
              nlinarith [abs_nonneg (a i j), sq_abs (a i j)]
            · simp [hj]
        _ = J.card := by simp [Finset.sum_ite_mem]
    calc ∑ k, (dotv (a i) (u k)) ^ 2 = ∑ k, ‖inner ℝ (e k) x‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro k _
          rw [hin k, Real.norm_eq_abs, sq_abs]
      _ ≤ ‖x‖ ^ 2 := hB
      _ ≤ J.card := hx
  -- somme
  have hk : ∀ k, L ≤ ∑ i, w i * (dotv (a i) (u k)) ^ 2 := by
    intro k
    have := hW _ (huW k)
    rwa [hnorm k, mul_one] at this
  have h1 : L * (Module.finrank ℝ W' : ℝ) ≤ ∑ k, ∑ i, w i * (dotv (a i) (u k)) ^ 2 := by
    have := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ W')))) => hk k)
    simpa [mul_comm] using this
  have h2 : ∑ k, ∑ i, w i * (dotv (a i) (u k)) ^ 2
      ≤ (J.card : ℝ) * ∑ i, (if i ∈ H then 0 else w i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.mul_sum]
    by_cases hi : i ∈ H
    · have : ∑ k, (dotv (a i) (u k)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro k _
        rw [hWH _ (huW k) i hi]; simp
      simp [hi, this]
    · simp only [hi, if_false]
      calc w i * ∑ k, (dotv (a i) (u k)) ^ 2 ≤ w i * J.card :=
            mul_le_mul_of_nonneg_left (hbess i) (hw i)
        _ = J.card * w i := by ring
  calc L * (Module.finrank ℝ W : ℝ) = L * (Module.finrank ℝ W' : ℝ) := by rw [hdim]
    _ ≤ _ := h1.trans h2

def B_dotLin (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := dotv a v
  map_add' x y := by
    simp only [dotv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dotv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring

theorem trace_capped (a : ι → Fin n → ℝ) (ha : ∀ i j, |a i j| ≤ 1)
    (J : Finset (Fin n)) (hJ : 0 < J.card) (V : Submodule ℝ (Fin n → ℝ))
    (hVJ : ∀ v ∈ V, ∀ j, j ∉ J → v j = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (L : ℝ) (hL : 0 < L)
    (hV : ∀ v ∈ V, L * ∑ j, v j ^ 2 ≤ ∑ i, w i * (dotv (a i) v) ^ 2) :
    (Module.finrank ℝ V : ℝ) ≤ ((J.card : ℝ) / L) * ∑ i, min (w i) (L / (J.card : ℝ)) := by
  classical
  have hc : (0 : ℝ) < J.card := by exact_mod_cast hJ
  let H : Finset ι := Finset.univ.filter (fun i => L / (J.card : ℝ) ≤ w i)
  let Fh : V →ₗ[ℝ] (H → ℝ) :=
    LinearMap.pi (fun i : H => (B_dotLin (a i)).comp V.subtype)
  have hrn := LinearMap.finrank_range_add_finrank_ker Fh
  have hrange : Module.finrank ℝ Fh.range ≤ H.card := by
    calc Module.finrank ℝ Fh.range ≤ Module.finrank ℝ (H → ℝ) := Submodule.finrank_le _
      _ = H.card := by simp
  let W : Submodule ℝ (Fin n → ℝ) := (LinearMap.ker Fh).map V.subtype
  have hWdim : Module.finrank ℝ W = Module.finrank ℝ (LinearMap.ker Fh) :=
    Submodule.finrank_map_subtype_eq V (LinearMap.ker Fh)
  have hWmem : ∀ v ∈ W, ∃ x : V, x ∈ LinearMap.ker Fh ∧ (x : Fin n → ℝ) = v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨x, hx, rfl⟩
  have key := B_step1 a ha J H w hw L W
    (by
      intro v hv j hj
      obtain ⟨x, _, rfl⟩ := hWmem v hv
      exact hVJ _ x.2 j hj)
    (by
      intro v hv i hi
      obtain ⟨x, hx, rfl⟩ := hWmem v hv
      have := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      exact this)
    (by
      intro v hv
      obtain ⟨x, _, rfl⟩ := hWmem v hv
      exact hV _ x.2)
  have hsplit : ∑ i, min (w i) (L / (J.card : ℝ))
      = (H.card : ℝ) * (L / J.card) + ∑ i, (if i ∈ H then 0 else w i) := by
    have : ∀ i, min (w i) (L / (J.card : ℝ))
        = (if i ∈ H then L / (J.card : ℝ) else 0) + (if i ∈ H then 0 else w i) := by
      intro i
      by_cases hi : i ∈ H
      · have : L / (J.card : ℝ) ≤ w i := by simpa [H] using hi
        simp [hi, min_eq_right this]
      · have : w i < L / (J.card : ℝ) := by simpa [H] using hi
        simp [hi, min_eq_left this.le]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [H]
  rw [hsplit]
  have hfW : (Module.finrank ℝ W : ℝ) ≤ ((J.card : ℝ) / L) * ∑ i, (if i ∈ H then 0 else w i) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    linarith
  have hV' : (Module.finrank ℝ V : ℝ) ≤ H.card + Module.finrank ℝ W := by
    rw [hWdim]
    have : Module.finrank ℝ V ≤ H.card + Module.finrank ℝ (LinearMap.ker Fh) := by omega
    exact_mod_cast this
  have : ((J.card : ℝ) / L) * ((H.card : ℝ) * (L / J.card)) = H.card := by
    field_simp
  calc (Module.finrank ℝ V : ℝ) ≤ H.card + Module.finrank ℝ W := hV'
    _ ≤ H.card + ((J.card : ℝ) / L) * ∑ i, (if i ∈ H then 0 else w i) := by linarith
    _ = _ := by rw [mul_add, this]

def B_ext (J : Finset (Fin n)) : (J → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun u j := if h : j ∈ J then u ⟨j, h⟩ else 0
  map_add' x y := by
    funext j; by_cases h : j ∈ J <;> simp [h]
  map_smul' c x := by
    funext j; by_cases h : j ∈ J <;> simp [h]

theorem B_ext_inj (J : Finset (Fin n)) : Function.Injective (B_ext J) := by
  intro x y hxy
  funext j
  have := congrFun hxy j.1
  simpa [B_ext, j.2] using this

theorem no_interior_minimizer [Nonempty ι] (a : ι → Fin n → ℝ) (ha : ∀ i j, |a i j| ≤ 1)
    (hn : 5 ≤ n) {z : Fin n → ℝ} (hz : z ∈ Kopen a)
    (hmin : ∀ w ∈ Kopen a, Phi a z ≤ Phi a w) (hΦ : Phi a z < 1) : False := by
  classical
  have hz' := hz
  obtain ⟨hz1, hs, hg⟩ := hz'
  let J : Finset (Fin n) := Finset.univ.filter (fun j => |z j| < 1)
  have hJmem : ∀ j, j ∈ J ↔ |z j| < 1 := by intro j; simp [J]
  have hR : Rr z ≤ J.card := by
    unfold Rr
    have h1 : (n : ℝ) = ∑ j : Fin n, (1 : ℝ) := by simp
    rw [h1, ← Finset.sum_sub_distrib]
    calc ∑ j : Fin n, (1 - z j ^ 2) ≤ ∑ j : Fin n, (if j ∈ J then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro j _
          by_cases hj : j ∈ J
          · simp only [hj, if_true]; nlinarith [sq_nonneg (z j)]
          · simp only [hj, if_false]
            have h2 : |z j| = 1 := le_antisymm (hz1 j) (not_lt.mp (fun h => hj ((hJmem j).2 h)))
            have : z j ^ 2 = 1 := by rw [← sq_abs, h2]; norm_num
            linarith
      _ = J.card := by simp [Finset.sum_ite_mem]
  have hRs : Rr z = ss z + 4 := by unfold ss; ring
  have hcR : (4 : ℝ) < J.card := by linarith
  have hJ : 0 < J.card := by
    have : (0 : ℝ) < J.card := by linarith
    exact_mod_cast this
  have hc : (0 : ℝ) < J.card := by exact_mod_cast hJ
  -- sous-espace V
  let Λ : (J → ℝ) →ₗ[ℝ] ℝ := (B_dotLin z).comp (B_ext J)
  let V : Submodule ℝ (Fin n → ℝ) := (LinearMap.ker Λ).map (B_ext J)
  have hVdim : Module.finrank ℝ V = Module.finrank ℝ (LinearMap.ker Λ) :=
    (Submodule.equivMapOfInjective (B_ext J) (B_ext_inj J) (LinearMap.ker Λ)).finrank_eq.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Λ
  have hr1 : Module.finrank ℝ Λ.range ≤ 1 := by
    calc Module.finrank ℝ Λ.range ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  have hdomain : Module.finrank ℝ (J → ℝ) = J.card := by simp
  have hlow : J.card ≤ 1 + Module.finrank ℝ V := by
    rw [hVdim]; omega
  have hVmem : ∀ v ∈ V, ∃ u ∈ LinearMap.ker Λ, B_ext J u = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨u, hu, rfl⟩
  have hVJ : ∀ v ∈ V, ∀ j, j ∉ J → v j = 0 := by
    intro v hv j hj
    obtain ⟨u, _, rfl⟩ := hVmem v hv
    simp [B_ext, hj]
  have hVperp : ∀ v ∈ V, ∑ j, z j * v j = 0 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hVmem v hv
    exact LinearMap.mem_ker.mp hu
  -- poids
  have ht : ∀ i, 0 < tt a z i := fun i => div_pos (hg i) (Real.sqrt_pos.2 hs)
  set L : ℝ := ∑ i, psi (tt a z i) with hLdef
  have hL : 0 < L := Finset.sum_pos (fun i _ => psi_pos _) Finset.univ_nonempty
  have hV : ∀ v ∈ V, L * ∑ j, v j ^ 2 ≤ ∑ i, phi2 (tt a z i) * (dotv (a i) v) ^ 2 := by
    intro v hv
    refine second_order a hz hmin v (hVperp v hv) ?_
    intro j hj
    apply hVJ v hv j
    intro hjJ
    have := (hJmem j).1 hjJ
    linarith
  have hT := trace_capped a ha J hJ V hVJ (fun i => phi2 (tt a z i))
    (fun i => (phi2_pos (ht i)).le) L hL hV
  have hθ : 0 < L / (J.card : ℝ) := div_pos hL hc
  have hS : ∑ i, min (phi2 (tt a z i)) (L / (J.card : ℝ))
      ≤ 3 / 4 * L + 1 / 4 * (L / J.card) * ∑ i, phi (tt a z i) := by
    calc ∑ i, min (phi2 (tt a z i)) (L / (J.card : ℝ))
        ≤ ∑ i, (3 / 4 * psi (tt a z i) + 1 / 4 * (L / J.card) * phi (tt a z i)) :=
          Finset.sum_le_sum (fun i _ => phi_capped (ht i) hθ)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hP : ∑ i, phi (tt a z i) < ss z := by
    have h1 : Phi a z * ss z = ∑ i, phi (tt a z i) := by
      unfold Phi; field_simp
    rw [← h1]
    nlinarith
  have hfin : (Module.finrank ℝ V : ℝ) < 3 / 4 * J.card + ss z / 4 := by
    have hcL : 0 ≤ (J.card : ℝ) / L := by positivity
    have h3 := mul_le_mul_of_nonneg_left hS hcL
    have h4 : ((J.card : ℝ) / L) * (3 / 4 * L + 1 / 4 * (L / J.card) * ∑ i, phi (tt a z i))
        = 3 / 4 * J.card + (∑ i, phi (tt a z i)) / 4 := by
      field_simp
    linarith
  have hlow' : (J.card : ℝ) ≤ 1 + Module.finrank ℝ V := by exact_mod_cast hlow
  have : ss z ≤ J.card - 4 := by unfold ss; linarith
  linarith

theorem C_continuous_ss : Continuous (ss : (Fin n → ℝ) → ℝ) := by
  unfold ss Rr; fun_prop

theorem C_continuous_gap (a : ι → Fin n → ℝ) (i : ι) : Continuous (fun z => gap a z i) := by
  unfold gap dotv; fun_prop

theorem C_phi_ge {t : ℝ} (ht : 0 < t) (h1 : t ≤ 1) : 32 / t ^ 2 ≤ phi t := by
  unfold phi
  have h := Real.add_one_le_exp (-(t ^ 2) / 8)
  have h2 : t ^ 2 ≤ 1 := by nlinarith
  have h3 : 1 / 2 ≤ exp (-(t ^ 2) / 8) := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right ht2]
  linarith

theorem C_closed_Kcl (a : ι → Fin n → ℝ) : IsClosed (Kcl a) := by
  have : Kcl a = (⋂ j, {z : Fin n → ℝ | |z j| ≤ 1}) ∩ {z | 0 ≤ ss z} ∩ ⋂ i, {z | 0 ≤ gap a z i} := by
    ext z; simp [Kcl, Set.mem_iInter, and_assoc]
  rw [this]
  refine ((isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le continuous_const C_continuous_ss)).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (C_continuous_gap a i))

theorem C_compact_Kcl (a : ι → Fin n → ℝ) : IsCompact (Kcl a) := by
  refine Metric.isCompact_of_isClosed_isBounded (C_closed_Kcl a) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  simpa using hz.1 j

theorem C_Phi_contAt (a : ι → Fin n → ℝ) {z : Fin n → ℝ} (hz : z ∈ Kopen a) :
    ContinuousAt (Phi a) z := by
  have hs : 0 < ss z := hz.2.1
  have hsq : 0 < √(ss z) := Real.sqrt_pos.mpr hs
  have hcs : ContinuousAt (ss : (Fin n → ℝ) → ℝ) z := C_continuous_ss.continuousAt
  have ht : ∀ i, ContinuousAt (fun w => tt a w i) z := fun i =>
    (C_continuous_gap a i).continuousAt.div hcs.sqrt hsq.ne'
  unfold Phi
  refine ContinuousAt.div (tendsto_finset_sum _ fun i _ => ?_) hcs hs.ne'
  have hpos : 0 < tt a z i := div_pos (hz.2.2 i) hsq
  exact (hasDerivAt_phi hpos).continuousAt.comp (f := fun w => tt a w i) (ht i)

theorem C_zero_mem (a : ι → Fin n → ℝ) (hn : 5 ≤ n) : (0 : Fin n → ℝ) ∈ Kopen a := by
  have hDl : 0 < Dl n := by
    unfold Dl
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  refine ⟨fun j => by simp, ?_, fun i => ?_⟩
  · have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [ss, Rr, Pi.zero_apply]
    simp
    linarith
  · simpa [gap, dotv] using hDl

theorem exists_min (a : ι → Fin n → ℝ) (hn : 5 ≤ n) :
    ∃ z ∈ Kcl a, ss z = 0 ∨ (z ∈ Kopen a ∧ ∀ w ∈ Kopen a, Phi a z ≤ Phi a w) := by
  classical
  by_cases h0 : ∃ z ∈ Kcl a, ss z = 0
  · obtain ⟨z, hz, h⟩ := h0
    exact ⟨z, hz, Or.inl h⟩
  push_neg at h0
  have hKc := C_compact_Kcl a
  have hz0 := C_zero_mem a hn
  have hz0c : (0 : Fin n → ℝ) ∈ Kcl a := ⟨hz0.1, hz0.2.1.le, fun i => (hz0.2.2 i).le⟩
  obtain ⟨z0, hz0K, hz0min⟩ := hKc.exists_isMinOn ⟨0, hz0c⟩ C_continuous_ss.continuousOn
  set m := ss z0 with hm
  have hmpos : 0 < m := lt_of_le_of_ne hz0K.2.1 (h0 z0 hz0K).symm
  have hmle : ∀ w ∈ Kcl a, m ≤ ss w := fun w hw => hz0min hw
  set c := Phi a 0 with hc
  set M : ℝ := |c| * n + 1 with hM
  have hMpos : 0 < M := by positivity
  set δ : ℝ := min 1 (32 / M) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hDl : 0 < Dl n := by
    unfold Dl
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  set ε : ℝ := min (δ * √m) (Dl n) with hε
  have hεpos : 0 < ε := lt_min (by have := Real.sqrt_pos.mpr hmpos; positivity) hDl
  -- borne uniforme sur les jeux
  have key : ∀ w ∈ Kopen a, Phi a w ≤ c → ∀ i, ε ≤ gap a w i := by
    intro w hw hwc i
    have hs : 0 < ss w := hw.2.1
    have hsq : 0 < √(ss w) := Real.sqrt_pos.mpr hs
    have hwK : w ∈ Kcl a := ⟨hw.1, hs.le, fun i => (hw.2.2 i).le⟩
    have hss_le : ss w ≤ n := by
      unfold ss Rr
      have : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hsum : ∑ i, phi (tt a w i) ≤ c * ss w := by
      have := hwc
      unfold Phi at this
      rwa [div_le_iff₀ hs] at this
    have hti : 0 < tt a w i := div_pos (hw.2.2 i) hsq
    have hsingle : phi (tt a w i) ≤ ∑ i, phi (tt a w i) :=
      Finset.single_le_sum (f := fun i => phi (tt a w i))
        (fun k _ => (phi_pos (div_pos (hw.2.2 k) hsq)).le) (Finset.mem_univ i)
    have hcs : c * ss w ≤ |c| * n := by
      calc c * ss w ≤ |c| * ss w := mul_le_mul_of_nonneg_right (le_abs_self c) hs.le
        _ ≤ |c| * n := mul_le_mul_of_nonneg_left hss_le (abs_nonneg c)
    have hphiM : phi (tt a w i) ≤ M := by linarith
    have htδ : δ ≤ tt a w i := by
      by_cases h1 : tt a w i ≤ 1
      · have h32 := C_phi_ge hti h1
        have hsq2 : 32 / M ≤ tt a w i ^ 2 := by
          have h2 : 32 / tt a w i ^ 2 ≤ M := h32.trans hphiM
          rw [div_le_iff₀ (by positivity)] at h2
          rw [div_le_iff₀ hMpos]
          nlinarith
        have : tt a w i ^ 2 ≤ tt a w i := by nlinarith
        exact (min_le_right _ _).trans (hsq2.trans this)
      · exact (min_le_left _ _).trans (by linarith)
    have hgap : gap a w i = tt a w i * √(ss w) := by
      unfold tt; field_simp
    have hsm : √m ≤ √(ss w) := Real.sqrt_le_sqrt (hmle w hwK)
    have hsqm : 0 < √m := Real.sqrt_pos.mpr hmpos
    rw [hgap]
    calc ε ≤ δ * √m := min_le_left _ _
      _ ≤ tt a w i * √(ss w) := mul_le_mul htδ hsm hsqm.le hti.le
  -- ensemble compact T
  set T : Set (Fin n → ℝ) := Kcl a ∩ ⋂ i, {z | ε ≤ gap a z i} with hT
  have hTclosed : IsClosed T :=
    (C_closed_Kcl a).inter (isClosed_iInter fun i => isClosed_le continuous_const (C_continuous_gap a i))
  have hTc : IsCompact T := hKc.of_isClosed_subset hTclosed Set.inter_subset_left
  have hTK : ∀ z ∈ T, z ∈ Kopen a := by
    intro z hz
    have hzK : z ∈ Kcl a := hz.1
    have hg : ∀ i, ε ≤ gap a z i := fun i => Set.mem_iInter.mp hz.2 i
    exact ⟨hzK.1, lt_of_lt_of_le hmpos (hmle z hzK), fun i => lt_of_lt_of_le hεpos (hg i)⟩
  have h0T : (0 : Fin n → ℝ) ∈ T := by
    refine ⟨hz0c, Set.mem_iInter.mpr fun i => ?_⟩
    have : gap a 0 i = Dl n := by simp [gap, dotv]
    show ε ≤ gap a 0 i
    rw [this]; exact min_le_right _ _
  have hcont : ContinuousOn (Phi a) T := fun z hz => (C_Phi_contAt a (hTK z hz)).continuousWithinAt
  obtain ⟨z, hzT, hzmin⟩ := hTc.exists_isMinOn ⟨0, h0T⟩ hcont
  refine ⟨z, hzT.1, Or.inr ⟨hTK z hzT, fun w hw => ?_⟩⟩
  by_cases hwc : Phi a w ≤ c
  · have hwT : w ∈ T := by
      refine ⟨⟨hw.1, hw.2.1.le, fun i => (hw.2.2 i).le⟩, Set.mem_iInter.mpr fun i => ?_⟩
      exact key w hw hwc i
    exact hzmin hwT
  · push_neg at hwc
    exact (hzmin h0T).trans hwc.le

theorem rounding (a : ι → Fin n → ℝ) (ha : ∀ i j, |a i j| ≤ 1) (z : Fin n → ℝ)
    (hz : ∀ j, |z j| ≤ 1) :
    ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧ ∀ i, |dotv (a i) x| ≤ |dotv (a i) z| + Rr z := by
  classical
  refine ⟨fun j => if 0 ≤ z j then 1 else -1, fun j => ?_, fun i => ?_⟩
  · by_cases h : 0 ≤ z j <;> simp [h]
  · set x : Fin n → ℝ := fun j => if 0 ≤ z j then 1 else -1 with hx
    have hRr : Rr z = ∑ j, (1 - z j ^ 2) := by
      simp [Rr, Finset.sum_sub_distrib]
    have hj : ∀ j, |a i j * (x j - z j)| ≤ 1 - z j ^ 2 := by
      intro j
      have h1 := hz j
      have h2 := ha i j
      have hzz : |z j| ≤ 1 := h1
      have hsq : z j ^ 2 = |z j| ^ 2 := (sq_abs _).symm
      have hxz : |x j - z j| = 1 - |z j| := by
        by_cases h : 0 ≤ z j
        · have : x j = 1 := by simp [hx, h]
          rw [this, abs_of_nonneg h] at *
          rw [abs_of_nonneg (by linarith [abs_of_nonneg h])]
        · have h' : z j < 0 := not_le.mp h
          have : x j = -1 := by simp [hx, h]
          rw [this, abs_of_neg h']
          rw [show -1 - z j = -(1 + z j) by ring, abs_neg]
          have : -1 ≤ z j := by have := (abs_le.mp hzz).1; linarith
          rw [abs_of_nonneg (by linarith)]
          rw [abs_of_neg h'] at *; ring
      rw [abs_mul, hxz]
      have h0 : 0 ≤ 1 - |z j| := by linarith
      have : |a i j| * (1 - |z j|) ≤ 1 * (1 - |z j|) := mul_le_mul_of_nonneg_right h2 h0
      nlinarith [abs_nonneg (z j)]
    have hdiff : dotv (a i) x - dotv (a i) z = ∑ j, a i j * (x j - z j) := by
      simp [dotv, mul_sub, Finset.sum_sub_distrib]
    have hb : |dotv (a i) x - dotv (a i) z| ≤ Rr z := by
      rw [hdiff, hRr]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hj j)
    have := abs_sub_abs_le_abs_sub (dotv (a i) x) (dotv (a i) z)
    linarith

theorem Phi_zero_lt_one [Nonempty ι] (a : ι → Fin n → ℝ) (hn : 5 ≤ n)
    (hcard : Fintype.card ι ≤ 2 * n) : Phi a 0 < 1 := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : ss (0 : Fin n → ℝ) = (n : ℝ) - 4 := by simp [ss, Rr]
  have hs0 : 0 < (n : ℝ) - 4 := by linarith
  have hDl : 0 < Dl n := by unfold Dl; positivity
  have hDl2 : (Dl n) ^ 2 > 0 := by positivity
  have ht : ∀ i, tt a (0 : Fin n → ℝ) i = Dl n / √((n : ℝ) - 4) := by
    intro i; simp [tt, gap, dotv, hs]
  have ht2 : (Dl n / √((n : ℝ) - 4)) ^ 2 = (Dl n) ^ 2 / ((n : ℝ) - 4) := by
    rw [div_pow, Real.sq_sqrt hs0.le]
  set X := 64 * exp (-(Dl n) ^ 2 / (8 * ((n : ℝ) - 4))) / (Dl n) ^ 2 with hX
  have hXpos : 0 < X := by positivity
  have hphi : phi (Dl n / √((n : ℝ) - 4)) = X * ((n : ℝ) - 4) := by
    unfold phi
    rw [ht2, hX]
    have : -((Dl n) ^ 2 / ((n : ℝ) - 4)) / 8 = -(Dl n) ^ 2 / (8 * ((n : ℝ) - 4)) := by
      field_simp
    rw [this]
    field_simp
  have hΦ : Phi a 0 = (Fintype.card ι : ℝ) * X := by
    unfold Phi
    simp only [ht, hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hphi]
    field_simp
  rw [hΦ]
  have hc : (Fintype.card ι : ℝ) ≤ 2 * n := by exact_mod_cast hcard
  have := barrier_zero hn
  calc (Fintype.card ι : ℝ) * X ≤ (2 * n) * X := mul_le_mul_of_nonneg_right hc hXpos.le
    _ < 1 := by rw [hX]; exact this

theorem small_case (n : ℕ) (hn : n ≤ 4) (S : Fin n → Finset (Fin n)) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
  have hn1 : 1 ≤ n := by
    have := i.pos; exact this
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hsq : (n : ℝ) ≤ 4 * Real.sqrt n := by
    have h4 : (n : ℝ) ≤ 4 := by exact_mod_cast hn
    have := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hc : ((S i).card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ (S i)).trans (by simp)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  linarith

theorem const_le (n : ℕ) (hn : 5 ≤ n) : Dl n + 4 ≤ 6 * Real.sqrt n := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (11 / 5 : ℝ) ≤ Real.sqrt n := by
    rw [show (11 / 5 : ℝ) = Real.sqrt (121 / 25) by
      rw [show (121 / 25 : ℝ) = (11 / 5) ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold Dl
  linarith

theorem core_colouring [Nonempty ι] (a : ι → Fin n → ℝ) (ha : ∀ i j, |a i j| ≤ 1)
    (hn : 5 ≤ n) (hcard : Fintype.card ι ≤ 2 * n) :
    ∃ z : Fin n → ℝ, (∀ j, |z j| ≤ 1) ∧ Rr z ≤ 4 ∧ ∀ i, dotv (a i) z ≤ Dl n := by
  obtain ⟨z, hzK, h⟩ := exists_min a hn
  rcases h with h0 | ⟨hzo, hmin⟩
  · refine ⟨z, hzK.1, ?_, fun i => ?_⟩
    · have h1 : Rr z = ss z + 4 := by unfold ss; ring
      rw [h1, h0]; norm_num
    · have := hzK.2.2 i
      unfold gap at this; linarith
  · exfalso
    have hDl : 0 < Dl n := by
      unfold Dl
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have h0 : (0 : Fin n → ℝ) ∈ Kopen a := by
      refine ⟨fun j => by simp, ?_, fun i => ?_⟩
      · have : (5 : ℝ) ≤ n := by exact_mod_cast hn
        simp only [ss, Rr, Pi.zero_apply]
        simp
        linarith
      · simpa [gap, dotv] using hDl
    exact no_interior_minimizer a ha hn hzo hmin
      (lt_of_le_of_lt (hmin 0 h0) (Phi_zero_lt_one a hn hcard))

end

end SpencerBP

open SpencerBP in
theorem spencer_final : type_of% @SixStandardDeviations.six_standard_deviations := by
  intro n S
  by_cases hn : n ≤ 4
  · exact small_case n hn S
  · have hn5 : 5 ≤ n := by omega
    let a : Bool × Fin n → Fin n → ℝ :=
      fun p j => (if p.1 then (1 : ℝ) else -1) * (if j ∈ S p.2 then (1 : ℝ) else 0)
    have ha : ∀ i j, |a i j| ≤ 1 := by
      intro i j
      obtain ⟨b, k⟩ := i
      simp only [a]
      by_cases hb : b <;> by_cases hj : j ∈ S k <;> simp [hb, hj]
    haveI : Nonempty (Bool × Fin n) := ⟨(true, ⟨0, by omega⟩)⟩
    have hcard : Fintype.card (Bool × Fin n) ≤ 2 * n := by simp [Fintype.card_prod]
    obtain ⟨z, hz1, hR, hzd⟩ := core_colouring a ha hn5 hcard
    obtain ⟨x, hx, hxd⟩ := rounding a ha z hz1
    refine ⟨x, hx, fun i => ?_⟩
    have hsum : ∀ b : Bool, ∀ y : Fin n → ℝ, dotv (a (b, i)) y
        = (if b then 1 else -1) * ∑ j ∈ S i, y j := by
      intro b y
      have key : ∑ j : Fin n, (if j ∈ S i then (1 : ℝ) else 0) * y j = ∑ j ∈ S i, y j := by
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      cases b <;> simp only [dotv, a, mul_assoc, ← Finset.mul_sum, key] <;> simp
    have h1 := hxd (true, i)
    have hpos := hzd (true, i)
    have hneg := hzd (false, i)
    rw [hsum true z] at hpos
    rw [hsum false z] at hneg
    rw [hsum true x, hsum true z] at h1
    simp only [if_true, one_mul] at hpos h1
    simp only [Bool.false_eq_true, if_false] at hneg
    have habs : |∑ j ∈ S i, z j| ≤ Dl n := abs_le.mpr ⟨by linarith, hpos⟩
    have hc := const_le n hn5
    calc |∑ j ∈ S i, x j| ≤ |∑ j ∈ S i, z j| + Rr z := h1
      _ ≤ Dl n + 4 := by linarith
      _ ≤ 6 * Real.sqrt n := hc

theorem OMA.solution : type_of% @SixStandardDeviations.six_standard_deviations :=
  spencer_final
