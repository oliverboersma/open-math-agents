import OMAStatements.S_opg_coloring_the_odd_distance_graph
import Mathlib

/- Davies's lattice construction with finite character orthogonality. -/

namespace OddDistProof

open Finset Filter
open scoped Topology BigOperators
noncomputable section

private def vx (K t : ℕ) : ℤ := 2 ^ (K + t) - 2 ^ (K - t)
private def vy (K t : ℕ) : ℤ := -2 ^ t - 2 * 2 ^ K
private def phase (K t : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 * vx K t + p.2 * vy K t

private theorem vx_factor {K t : ℕ} (ht : t ≤ K) :
    vx K t = 2 ^ (K - t) * (2 ^ (t + t) - 1) := by
  unfold vx
  rw [show K + t = (K - t) + (t + t) by omega, pow_add]
  ring

private theorem vy_factor {K t : ℕ} (ht : t ≤ K) :
    vy K t = 2 ^ t * (-1 - 2 ^ (K + 1 - t)) := by
  unfold vy
  have he : (2 : ℤ) ^ t * 2 ^ (K + 1 - t) = 2 * 2 ^ K := by
    rw [← pow_add, show t + (K + 1 - t) = K + 1 by omega, pow_succ']
  linear_combination he

private def point (K : ℕ) (x y : ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(x : ℝ) + (y : ℝ) / (2 * (2 : ℝ) ^ K),
    (y : ℝ) * Real.sqrt (1 - (1 / (2 * (2 : ℝ) ^ K)) ^ 2)]

private theorem edge {K t : ℕ} (ht : t < K) {s x y x' y' : ℤ}
    (hs : Odd s) (hx : x - x' = s * vx K t) (hy : y - y' = s * vy K t) :
    OMA.S_opg_coloring_the_odd_distance_graph.oddDistanceGraph.Adj
      (point K x y) (point K x' y') := by
  let L : ℕ := 2 ^ (K + t) + 2 ^ (K - t) + 1
  have hsq : dist (point K x y) (point K x' y') ^ 2 = ((s : ℝ) * (L : ℝ)) ^ 2 := by
    rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two]
    simp only [point, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.dist_eq, sq_abs]
    rw [show (x : ℝ) + y / (2 * (2 : ℝ) ^ K) -
        (↑x' + y' / (2 * (2 : ℝ) ^ K)) =
        (x - x' : ℤ) + (y - y' : ℤ) / (2 * (2 : ℝ) ^ K) by push_cast; ring]
    rw [show (y : ℝ) * Real.sqrt (1 - (1 / (2 * (2 : ℝ) ^ K)) ^ 2) -
        (y' : ℝ) * Real.sqrt (1 - (1 / (2 * (2 : ℝ) ^ K)) ^ 2) =
        (y - y' : ℤ) * Real.sqrt (1 - (1 / (2 * (2 : ℝ) ^ K)) ^ 2) by push_cast; ring]
    rw [Real.sq_sqrt (by positivity), hx, hy, mul_pow,
      Real.sq_sqrt (by
        have hp : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
        have hh : 0 ≤ (1 : ℝ) / (2 * 2 ^ K) := by positivity
        have hh' : (1 : ℝ) / (2 * 2 ^ K) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
        nlinarith)]
    unfold L vx vy
    push_cast
    have he : (2 : ℝ) ^ K = 2 ^ (K - t) * 2 ^ t := by
      rw [← pow_add, Nat.sub_add_cancel ht.le]
    have he' : (2 : ℝ) ^ (K + t) = 2 ^ (K - t) * 2 ^ t * 2 ^ t := by
      rw [pow_add, he]
    rw [he', he]
    field_simp
    ring
  have hab : (s.natAbs : ℝ) = |(s : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hdist : dist (point K x y) (point K x' y') = (s.natAbs * L : ℕ) := by
    push_cast
    rw [hab]
    apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
    rw [hsq, mul_pow, mul_pow, sq_abs]
  have hs' : Odd s.natAbs := Int.natAbs_odd.mpr hs
  have hL : Odd L := by
    have hp (a : ℕ) (ha : 0 < a) : Even ((2 : ℕ) ^ a) := by
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
      rw [pow_succ']
      exact ⟨2 ^ b, by ring⟩
    exact (Even.add (hp _ (by omega)) (hp _ (by omega))).add_odd (by decide)
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  refine ⟨?_, Or.inl ⟨_, hs'.mul hL, hdist⟩⟩
  intro heq
  rw [heq, dist_self] at hdist
  have hpos : 0 < ((s.natAbs * L : ℕ) : ℝ) := by
    exact_mod_cast (hs'.mul hL).pos
  exact hpos.ne' hdist.symm

private def direction (K : ℕ) (i : ℕ × Bool) : ℤ × ℤ :=
  if i.2 then (vx K i.1, vy K i.1) else -(vx K i.1, vy K i.1)

private theorem directions (K : ℕ) :
    ∃ D : Finset (ℤ × ℤ), D = (range K ×ˢ (univ : Finset Bool)).image (direction K) ∧
      #D = 2 * K ∧ 0 ∉ D ∧ ∀ u, -u ∈ D ↔ u ∈ D := by
  have hn (t : ℕ) : vy K t < 0 := by
    unfold vy
    linarith [show (0 : ℤ) < 2 ^ t by positivity, show (0 : ℤ) ≤ 2 * 2 ^ K by positivity]
  have hm : StrictAnti (vy K) := by
    intro i j hij
    have h : (2 : ℤ) ^ i < 2 ^ j := pow_lt_pow_right₀ (by norm_num) hij
    unfold vy
    linarith
  have hinj : Function.Injective (direction K) := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have h' := congrArg Prod.snd h
    cases s <;> cases t <;> simp [direction] at h' ⊢
    · exact hm.injective h'
    · linarith [hn i, hn j]
    · linarith [hn i, hn j]
    · exact hm.injective h'
  let A := range K ×ˢ (univ : Finset Bool)
  refine ⟨A.image (direction K), rfl, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]
    simp [A, Nat.mul_comm]
  · intro h
    obtain ⟨⟨t, s⟩, _, h⟩ := mem_image.mp h
    have h' := congrArg Prod.snd h
    cases s <;> simp [direction] at h' <;> linarith [hn t]
  · have hneg (u : ℤ × ℤ) (hu : u ∈ A.image (direction K)) : -u ∈ A.image (direction K) := by
      obtain ⟨⟨t, s⟩, ht, rfl⟩ := mem_image.mp hu
      refine mem_image.mpr ⟨(t, !s), by simpa [A] using ht, ?_⟩
      cases s <;> simp [direction]
    exact fun u => ⟨fun h => by simpa using hneg (-u) h, hneg u⟩

private def badPhase (x : ℝ) : Prop := ∃ z : ℤ, Odd z ∧ 2 * x = z

private theorem no_three {K a b c : ℕ} {p : ℝ × ℝ}
    (hab : a < b) (hbc : b < c) (hc : c < K)
    (ha : badPhase (phase K a p)) (hb : badPhase (phase K b p))
    (hd : badPhase (phase K c p)) : False := by
  let X (t : ℕ) : ℤ := 2 ^ (c - t) * (2 ^ (t + t) - 1)
  let Y (t : ℕ) : ℤ := 2 ^ (t - a) * (-1 - 2 ^ (K + 1 - t))
  have hX (t : ℕ) (ht : t ≤ c) : vx K t = 2 ^ (K - c) * X t := by
    rw [vx_factor (by omega)]
    dsimp only [X]
    rw [← mul_assoc, ← pow_add, show K - c + (c - t) = K - t by omega]
  have hY (t : ℕ) (ht : a ≤ t) (ht' : t ≤ K) : vy K t = 2 ^ a * Y t := by
    rw [vy_factor ht']
    dsimp only [Y]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
  let D (i j : ℕ) : ℤ := X i * Y j - X j * Y i
  obtain ⟨A, hA, eA⟩ := ha
  obtain ⟨B, hB, eB⟩ := hb
  obtain ⟨C, hC, eC⟩ := hd
  have hr : D b c * A + D c a * B + D a b * C = 0 := by
    suffices (↑(D b c * A + D c a * B + D a b * C) : ℝ) = 0 by exact_mod_cast this
    push_cast
    rw [← eA, ← eB, ← eC]
    unfold phase
    rw [hX a (by omega), hX b (by omega), hX c le_rfl,
      hY a le_rfl (by omega), hY b (by omega) (by omega), hY c (by omega) hc.le]
    dsimp only [D]
    push_cast
    ring
  have two : (2 : ZMod 2) = 0 := by decide
  have mn : (-1 : ZMod 2) = 1 := by decide
  have xa : (X a : ZMod 2) = 0 := by simp [X, two, zero_pow (by omega : c - a ≠ 0)]
  have xb : (X b : ZMod 2) = 0 := by simp [X, two, zero_pow (by omega : c - b ≠ 0)]
  have xc : (X c : ZMod 2) = 1 := by
    simp [X, two, zero_pow (by omega : c + c ≠ 0), mn]
  have ya : (Y a : ZMod 2) = 1 := by
    simp [Y, two, zero_pow (by omega : K + 1 - a ≠ 0), mn]
  have yb : (Y b : ZMod 2) = 0 := by simp [Y, two, zero_pow (by omega : b - a ≠ 0)]
  have yc : (Y c : ZMod 2) = 0 := by simp [Y, two, zero_pow (by omega : c - a ≠ 0)]
  have bb : (B : ZMod 2) = 1 := by
    obtain ⟨q, rfl⟩ := hB
    simp [two]
  have hm := congrArg (fun z : ℤ => (z : ZMod 2)) hr
  simp [D, xa, xb, xc, ya, yb, yc, bb] at hm

open scoped Classical in
private theorem bad_card (K : ℕ) (p : ℝ × ℝ) :
    #((range K).filter (fun t => badPhase (phase K t p))) ≤ 2 := by
  classical
  by_contra! h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp h
  rw [mem_filter, mem_range] at ha hb hc
  by_cases hab' : a < b
  · by_cases hbc' : b < c
    · exact no_three hab' hbc' hc.1 ha.2 hb.2 hc.2
    · by_cases hac' : a < c
      · exact no_three hac' (by omega) hb.1 ha.2 hc.2 hb.2
      · exact no_three (by omega) hab' hb.1 hc.2 ha.2 hb.2
  · by_cases hac' : a < c
    · exact no_three (by omega) hac' hc.1 hb.2 ha.2 hc.2
    · by_cases hbc' : b < c
      · exact no_three hbc' (by omega) ha.1 hb.2 hc.2 ha.2
      · exact no_three (by omega) (by omega) ha.1 hc.2 hb.2 ha.2

private def wave (x : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)

private theorem wave_add (x y : ℝ) : wave (x + y) = wave x * wave y := by
  rw [wave, wave, wave, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem wave_nat (x : ℝ) (j : ℕ) : wave ((j : ℝ) * x) = wave x ^ j := by
  rw [wave, wave, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem wave_norm (x : ℝ) : ‖wave x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem wave_eq_one (x : ℝ) : wave x = 1 ↔ ∃ j : ℤ, x = j := by
  rw [wave, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have he := congrArg Complex.im hj
    simp [Complex.mul_im] at he
    nlinarith [Real.pi_pos]
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    push_cast
    ring

private theorem wave_star (x : ℝ) : star (wave x) = wave (-x) := by
  apply mul_left_cancel₀ (show wave x ≠ 0 from Complex.exp_ne_zero _)
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, wave_norm]
  rw [← wave_add, add_neg_cancel, (wave_eq_one 0).2 ⟨0, by simp⟩]
  norm_num

private def squareKernel (n : ℕ) (x : ℝ) : ℝ :=
  (wave x).re * ‖∑ j ∈ range n, wave (2 * x) ^ j‖ ^ 2 / (n : ℝ) ^ 2

private theorem norm_geom_le (n : ℕ) (x : ℝ) :
    ‖∑ j ∈ range n, wave (2 * x) ^ j‖ ≤ n := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_pow, wave_norm]

private theorem squareKernel_eventually {n : ℕ → ℕ} {x : ℕ → ℝ} {a ε : ℝ}
    (hn : Tendsto n atTop atTop) (hx : Tendsto x atTop (𝓝 a))
    (ha : ¬badPhase a) (hε : 0 < ε) :
    ∀ᶠ i in atTop, -ε ≤ squareKernel (n i) (x i) := by
  have hcont : Continuous wave := by unfold wave; fun_prop
  by_cases h : wave (2 * a) = 1
  · obtain ⟨j, hj⟩ := (wave_eq_one _).mp h
    have he : Even j := by
      rw [← Int.not_odd_iff_even]
      exact fun ho => ha ⟨j, ho, hj⟩
    obtain ⟨l, hl⟩ := he
    have hw : wave a = 1 := (wave_eq_one _).mpr ⟨l, by
      rw [hl, Int.cast_add] at hj
      linarith⟩
    have ht : Tendsto (fun i => (wave (x i)).re) atTop (𝓝 1) := by
      simpa [Function.comp_def, hw] using (Complex.continuous_re.comp hcont).continuousAt.tendsto.comp hx
    filter_upwards [ht.eventually_const_lt zero_lt_one] with i hi
    exact (neg_nonpos.mpr hε.le).trans (div_nonneg
      (mul_nonneg hi.le (sq_nonneg _)) (sq_nonneg _))
  · let δ : ℝ := ‖wave (2 * a) - 1‖ / 2
    have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h))
    have ht : Tendsto (fun i => ‖wave (2 * x i) - 1‖) atTop (𝓝 ‖wave (2 * a) - 1‖) :=
      ((hcont.comp (continuous_const.mul continuous_id)).sub continuous_const).norm.continuousAt.tendsto.comp hx
    obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((2 / δ) ^ 2 / ε))
    have hδ' : δ < ‖wave (2 * a) - 1‖ :=
      half_lt_self (norm_pos_iff.mpr (sub_ne_zero.mpr h))
    filter_upwards [ht.eventually_const_lt hδ',
      hn.eventually (eventually_ge_atTop N)] with i hi hNi
    let z := wave (2 * x i)
    let S := ∑ j ∈ range (n i), z ^ j
    have hg : ‖S‖ * ‖z - 1‖ ≤ 2 := by
      rw [← norm_mul, show S * (z - 1) = z ^ n i - 1 from geom_sum_mul z (n i)]
      exact (norm_sub_le _ _).trans (by simp [z, norm_pow, wave_norm]; norm_num)
    have hS : ‖S‖ ≤ 2 / δ :=
      (le_div_iff₀ hδ).mpr ((mul_le_mul_of_nonneg_left hi.le (norm_nonneg _)).trans hg)
    have hn' : max 1 ((2 / δ) ^ 2 / ε) < (n i : ℝ) :=
      hN.trans_le (by exact_mod_cast hNi)
    have hn1 : 1 < (n i : ℝ) := (le_max_left _ _).trans_lt hn'
    have hnε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn')
    have hSq : ‖S‖ ^ 2 ≤ (2 / δ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hS
    have hbound : ‖S‖ ^ 2 ≤ ε * (n i : ℝ) ^ 2 := by
      calc
        ‖S‖ ^ 2 ≤ (2 / δ) ^ 2 := hSq
        _ ≤ ε * (n i : ℝ) := by linarith
        _ ≤ ε * (n i : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          nlinarith
    have hre := (abs_le.mp (Complex.abs_re_le_norm (wave (x i)))).1
    rw [wave_norm] at hre
    apply (le_div_iff₀ (show 0 < (n i : ℝ) ^ 2 by positivity)).mpr
    change -ε * (n i : ℝ) ^ 2 ≤ (wave (x i)).re * ‖S‖ ^ 2
    have hr := mul_le_mul_of_nonneg_right hre (sq_nonneg ‖S‖)
    rw [neg_mul]
    exact (neg_le_neg hbound).trans (by simpa only [neg_one_mul] using hr)

private def geom (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range n, wave (2 * x) ^ j

-- The multiplier 1 + 2 * (j - l) occurs n - r times for each sign of 2 * r + 1.
private def kernel (n : ℕ) (x : ℝ) : ℝ :=
  (wave x * (geom n x * star (geom (n + 1) x))).re / ((n : ℝ) * (n + 1 : ℝ))

private theorem re_ge_neg_norm (w : ℂ) : -‖w‖ ≤ w.re :=
  (abs_le.mp (Complex.abs_re_le_norm w)).1

private theorem kernel_ge_neg_one {n : ℕ} (hn : 0 < n) (x : ℝ) :
    -1 ≤ kernel n x := by
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) * (n + 1 : ℝ))).mpr
  rw [neg_one_mul]
  have h := re_ge_neg_norm (wave x * (geom n x * star (geom (n + 1) x)))
  rw [norm_mul, norm_mul, wave_norm, one_mul, norm_star] at h
  refine (neg_le_neg ?_).trans h
  exact mul_le_mul (norm_geom_le n x) (by
    simpa only [geom, Nat.cast_add, Nat.cast_one] using norm_geom_le (n + 1) x)
    (norm_nonneg _) (by positivity)

private theorem kernel_eventually {n : ℕ → ℕ} {x : ℕ → ℝ} {a ε : ℝ}
    (hn : Tendsto n atTop atTop) (hx : Tendsto x atTop (𝓝 a))
    (ha : ¬badPhase a) (hε : 0 < ε) :
    ∀ᶠ i in atTop, -ε ≤ kernel (n i) (x i) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 / ε))
  filter_upwards [squareKernel_eventually hn hx ha (half_pos hε),
    hn.eventually (eventually_ge_atTop N)] with i hi hNi
  let u := x i
  let k := n i
  have hNk : max 1 (2 / ε) < (k : ℝ) := hN.trans_le (by exact_mod_cast hNi)
  have hk : (1 : ℝ) < k := (le_max_left _ _).trans_lt hNk
  have hp : (0 : ℝ) < k := zero_lt_one.trans hk
  have hs : geom (k + 1) u = geom k u + wave (2 * u) ^ k :=
    sum_range_succ _ _
  have herr := re_ge_neg_norm (wave u * (geom k u * star (wave (2 * u) ^ k)))
  rw [norm_mul, norm_mul, wave_norm, norm_star, norm_pow, wave_norm, one_pow,
    mul_one, one_mul] at herr
  have herr' : -(k : ℝ) ≤ (wave u * (geom k u * star (wave (2 * u) ^ k))).re :=
    (neg_le_neg (norm_geom_le k u)).trans herr
  have he : 1 ≤ ε / 2 * ((k : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hNk)
    nlinarith only [hh, hε]
  have hmain := (le_div_iff₀ (show 0 < (k : ℝ) ^ 2 by positivity)).mp hi
  have hscale := mul_le_mul_of_nonneg_left he hp.le
  have hsq := mul_nonneg (half_pos hε).le hp.le
  apply (le_div_iff₀ (show 0 < (k : ℝ) * (k + 1 : ℝ) by positivity)).mpr
  change -ε * ((k : ℝ) * (k + 1 : ℝ)) ≤ (wave u * (geom k u * star (geom (k + 1) u))).re
  rw [hs, star_add, mul_add (geom k u), mul_add (wave u), Complex.add_re]
  have hreal : (wave u * (geom k u * star (geom k u))).re = (wave u).re * ‖geom k u‖ ^ 2 := by
    simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hreal]
  change -(ε / 2) * (k : ℝ) ^ 2 ≤ (wave u).re * ‖geom k u‖ ^ 2 at hmain
  nlinarith only [hmain, hscale, hsq, herr']

-- Integer coordinates give period one in each variable.
private theorem uniform (K : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      -(5 / 2 : ℝ) ≤ ∑ t ∈ range K, kernel n (phase K t p) := by
  classical
  by_contra! h
  choose p hp hlow using fun j : ℕ => h (j + 1) (by omega)
  obtain ⟨q, _, φ, hφ, hq⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hp
  let ε : ℝ := 1 / (4 * (K + 1 : ℝ))
  have hε : 0 < ε := by positivity
  have hf : Tendsto (fun i => φ i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ (φ i)) hφ.tendsto_atTop
  have hev : ∀ᶠ i in atTop, ∀ t ∈ range K,
      -ε - (if badPhase (phase K t q) then 1 else 0) ≤
        kernel (φ i + 1) (phase K t (p (φ i))) := by
    apply (eventually_all_finset _).mpr
    intro t _
    by_cases ht : badPhase (phase K t q)
    · filter_upwards with i
      simp only [ht, if_true]
      have hg := kernel_ge_neg_one (Nat.succ_pos (φ i)) (phase K t (p (φ i)))
      linarith
    · have hcont : Continuous (phase K t) := by unfold phase; fun_prop
      simpa [ht] using kernel_eventually hf (hcont.continuousAt.tendsto.comp hq) ht hε
  obtain ⟨i, hi⟩ := hev.exists
  have hsum := sum_le_sum hi
  have hcard : (∑ t ∈ range K, if badPhase (phase K t q) then (1 : ℝ) else 0) ≤ 2 := by
    rw [← sum_filter]
    simpa using (show (#((range K).filter (fun t => badPhase (phase K t q))) : ℝ) ≤ 2
      by exact_mod_cast bad_card K q)
  have hh : (K : ℝ) * ε ≤ 1 / 4 := by
    dsimp [ε]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  linarith [hlow (φ i)]

private abbrev Torus (m : ℕ) := ZMod m × ZMod m

section Fourier
variable {m : ℕ} [NeZero m]

private def character (z u : Torus m) : ℂ :=
  ZMod.stdAddChar (z.1 * u.1) * ZMod.stdAddChar (z.2 * u.2)

private theorem character_add (z u v : Torus m) :
    character z (u + v) = character z u * character z v := by
  simp only [character, Prod.fst_add, Prod.snd_add, mul_add, AddChar.map_add_eq_mul]
  ring

private theorem character_zero (z : Torus m) : character z 0 = 1 := by
  simp [character]

private theorem zero_character (u : Torus m) : character 0 u = 1 := by
  simp [character]

private theorem character_star (z u : Torus m) :
    star (character z u) = character z (-u) := by
  have hn : ‖character z u‖ = 1 := by
    simp only [character, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  apply mul_left_cancel₀ (show character z u ≠ 0 by intro h; simp [h] at hn)
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, ← character_add,
    add_neg_cancel, character_zero]
  norm_num

private theorem orthogonality (u : Torus m) :
    ∑ z : Torus m, character z u = if u = 0 then (m : ℂ) ^ 2 else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [character, ← mul_sum, ← sum_mul]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),
    AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  rcases u with ⟨a, b⟩
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [Prod.ext_iff, ha, hb, pow_two]

private def indicatorFourier (I : Finset (Torus m)) (z : Torus m) : ℂ :=
  ∑ u ∈ I, character z (-u)

private def mass (I : Finset (Torus m)) (z : Torus m) : ℝ :=
  ‖indicatorFourier I z‖ ^ 2

private theorem moment (I : Finset (Torus m)) (d : Torus m) :
    ∑ z : Torus m, (character z d).re * mass I z =
      ∑ u ∈ I, ∑ v ∈ I, if d = u - v then (m : ℝ) ^ 2 else 0 := by
  classical
  have he (z : Torus m) :
      character z d * (indicatorFourier I z * star (indicatorFourier I z)) =
        ∑ u ∈ I, ∑ v ∈ I, character z (d - u + v) := by
    simp only [indicatorFourier, star_sum, character_star, neg_neg, sum_mul, mul_sum,
      sub_eq_add_neg, character_add, mul_assoc]
    rw [sum_comm]
  have hz : ∑ z : Torus m, ∑ u ∈ I, ∑ v ∈ I, character z (d - u + v) =
      ∑ u ∈ I, ∑ v ∈ I, if d = u - v then (m : ℂ) ^ 2 else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [orthogonality]
    have hv : d - u + v = 0 ↔ d = u - v := by
      constructor
      · intro h
        calc
          d = (d - u + v) + (u - v) := by abel
          _ = u - v := by rw [h, zero_add]
      · intro h
        rw [h]
        abel
    simp only [hv]
  simp_rw [← he] at hz
  have hr := congrArg Complex.re hz
  simpa only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mass, apply_ite, Complex.zero_re] using hr

private theorem parseval (I : Finset (Torus m)) :
    ∑ z : Torus m, mass I z = (m : ℝ) ^ 2 * I.card := by
  classical
  have hr := moment I 0
  simp only [character_zero, Complex.one_re, one_mul] at hr
  rw [hr]
  trans ∑ _u ∈ I, (m : ℝ) ^ 2
  · apply sum_congr rfl
    intro u hu
    rw [sum_eq_single u]
    · simp
    · intro v _ hv
      rw [if_neg (fun h => hv ((sub_eq_zero.mp h.symm).symm))]
    · exact fun h => (h hu).elim
  · simp [mul_comm]

private def symbol {ι : Type} (S : Finset ι) (d : ι → Torus m) (D : ℝ)
    (z : Torus m) : ℝ :=
  (∑ i ∈ S, (character z (d i)).re) / D

private theorem ratio {ι : Type} (S : Finset ι) (d : ι → Torus m) {D : ℝ}
    (I : Finset (Torus m))
    (hind : ∀ i ∈ S, ∀ u ∈ I, ∀ v ∈ I, d i ≠ u - v)
    (hmin : ∀ z, -(5 / 2 : ℝ) ≤ symbol S d D z) :
    ((S.card : ℝ) / D + 5 / 2) * I.card ≤ (5 / 2 : ℝ) * (m : ℝ) ^ 2 := by
  classical
  have hzero : ∑ z : Torus m, symbol S d D z * mass I z = 0 := by
    simp only [symbol, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
    suffices (∑ i ∈ S, ∑ z : Torus m, (character z (d i)).re * mass I z) = 0 by
      rw [this, zero_div]
    apply sum_eq_zero
    intro i hi
    rw [moment]
    apply sum_eq_zero
    intro u hu
    exact sum_eq_zero fun v hv => if_neg (hind i hi u hu v hv)
  let W := (S.card : ℝ) / D
  have hW : symbol S d D (0 : Torus m) = W := by simp [symbol, zero_character, W]
  have h (z : Torus m) :
      -(5 / 2 : ℝ) * mass I z + (if z = 0 then (W + 5 / 2) * mass I z else 0) ≤
        symbol S d D z * mass I z := by
    have hm : 0 ≤ mass I z := sq_nonneg _
    by_cases hz : z = 0
    · subst z
      rw [if_pos rfl, hW]
      ring_nf
      rfl
    · simpa [hz] using mul_le_mul_of_nonneg_right (hmin z) hm
  have hh := sum_le_sum (fun z (_ : z ∈ (univ : Finset (Torus m))) => h z)
  simp only [sum_add_distrib, ← mul_sum, sum_ite_eq', mem_univ, if_true, hzero, parseval] at hh
  have hm0 : mass I (0 : Torus m) = (I.card : ℝ) ^ 2 := by
    simp [mass, indicatorFourier, zero_character]
  rw [hm0] at hh
  by_cases hn : I.card = 0
  · simp [hn]
  · have hp : (0 : ℝ) < I.card := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply le_of_mul_le_mul_right _ hp
    calc
      (W + 5 / 2) * (I.card : ℝ) * I.card = (W + 5 / 2) * (I.card : ℝ) ^ 2 := by ring
      _ ≤ ((5 / 2 : ℝ) * (m : ℝ) ^ 2) * I.card := by linarith

end Fourier

private def oddStep (j l : ℕ) : ℤ := 1 + 2 * ((j : ℤ) - l)

private def stepX (K : ℕ) (i : ℕ × ℕ × ℕ) : ℤ := oddStep i.2.1 i.2.2 * vx K i.1
private def stepY (K : ℕ) (i : ℕ × ℕ × ℕ) : ℤ := oddStep i.2.1 i.2.2 * vy K i.1

private def step (m K : ℕ) (i : ℕ × ℕ × ℕ) : Torus m :=
  ((stepX K i : ZMod m), (stepY K i : ZMod m))

private def steps (K n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range K ×ˢ (range n ×ˢ range (n + 1))

private def frequency {m : ℕ} (z : Torus m) : ℝ × ℝ :=
  ((z.1.val : ℝ) / m, (z.2.val : ℝ) / m)

private theorem character_cast {m : ℕ} [NeZero m] (z : Torus m) (x y : ℤ) :
    character z ((x : ZMod m), (y : ZMod m)) =
      wave ((frequency z).1 * x + (frequency z).2 * y) := by
  have h (a : ZMod m) (b : ℤ) : a * (b : ZMod m) = (((a.val : ℤ) * b : ℤ) : ZMod m) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [character, h, ZMod.stdAddChar_coe]
  rw [wave, ← Complex.exp_add]
  congr 1
  dsimp [frequency]
  push_cast
  ring

private theorem wave_step (j l : ℕ) (x : ℝ) :
    wave ((oddStep j l : ℝ) * x) =
      wave x * (wave (2 * x) ^ j * star (wave (2 * x) ^ l)) := by
  rw [show (oddStep j l : ℝ) * x = x + ((j : ℝ) * (2 * x) + -((l : ℝ) * (2 * x))) by
        unfold oddStep
        push_cast
        ring,
      wave_add, wave_add, ← wave_star, wave_nat, wave_nat]

private theorem symbol_eq {m : ℕ} [NeZero m] (K n : ℕ) (z : Torus m) :
    symbol (steps K n) (step m K) ((n : ℝ) * (n + 1 : ℝ)) z =
      ∑ t ∈ range K, kernel n (phase K t (frequency z)) := by
  simp only [symbol, steps, sum_product, kernel, ← sum_div]
  congr 1
  apply sum_congr rfl
  intro t _
  let x := phase K t (frequency z)
  have hchar (j l : ℕ) : character z (step m K (t, j, l)) = wave ((oddStep j l : ℝ) * x) := by
    rw [step, character_cast]
    congr 1
    dsimp [stepX, stepY, x, phase]
    push_cast
    ring
  simp only [hchar]
  simp_rw [← Complex.re_sum]
  change (∑ j ∈ range n, ∑ l ∈ range (n + 1), wave ((oddStep j l : ℝ) * x)).re =
    (wave x * (geom n x * star (geom (n + 1) x))).re
  congr 1
  simp only [geom, wave_step, star_sum, sum_mul, mul_sum]
  rw [sum_comm]

private theorem frequency_mem {m : ℕ} [NeZero m] (z : Torus m) :
    frequency z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  have h (a : ZMod m) : (a.val : ℝ) / m ∈ Set.Icc 0 1 :=
    ⟨by positivity, (div_le_one (by exact_mod_cast NeZero.pos m)).mpr
      (by exact_mod_cast (ZMod.val_lt a).le)⟩
  exact ⟨h z.1, h z.2⟩

private theorem unwrap {m R B x y : ℕ} [NeZero m] (hm : R + B ≤ m)
    (hx : x < R) (hy : y < R) {b : ℤ} (hb : |b| < (B : ℤ))
    (he : (b : ZMod m) = (x : ZMod m) - y) : (x : ℤ) - y = b := by
  let e : ℤ := (x : ℤ) - y - b
  have hz : (e : ZMod m) = 0 := by
    dsimp [e]
    push_cast
    rw [he, sub_self]
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd e m).mp hz
  have hs : |e| < (m : ℤ) := by
    dsimp [e]
    rw [abs_lt] at hb ⊢
    omega
  by_cases hq0 : q = 0
  · simpa [e, hq0, sub_eq_zero] using hq
  · have hq1 : (1 : ℤ) ≤ |q| := by have := abs_pos.mpr hq0; omega
    rw [hq, abs_mul, abs_of_nonneg (Int.natCast_nonneg m)] at hs
    have hh := mul_le_mul_of_nonneg_left hq1 (Int.natCast_nonneg m)
    omega

private theorem no_coloring (c : ℕ) :
    ¬OMA.S_opg_coloring_the_odd_distance_graph.oddDistanceGraph.Colorable c := by
  classical
  rintro ⟨col⟩
  let K := 4 * c + 4
  obtain ⟨n, hn, hmin⟩ := uniform K
  let S := steps K n
  let B := ∑ i ∈ S, ((stepX K i).natAbs + (stepY K i).natAbs + 1)
  let R := 100 * (B + 1)
  let m := R + B
  have hR : 0 < R := by dsimp [R]; omega
  have hRm : R ≤ m := Nat.le_add_right _ _
  have : NeZero m := ⟨(hR.trans_le hRm).ne'⟩
  let emb : (Fin R × Fin R) ↪ Torus m :=
    ⟨fun u => (u.1.val, u.2.val), by
      intro u v he
      apply Prod.ext
      · apply Fin.ext
        have he' := congrArg (fun z : Torus m => z.1.val) he
        simpa only [ZMod.val_natCast_of_lt (u.1.isLt.trans_le hRm),
          ZMod.val_natCast_of_lt (v.1.isLt.trans_le hRm)] using he'
      · apply Fin.ext
        have he' := congrArg (fun z : Torus m => z.2.val) he
        simpa only [ZMod.val_natCast_of_lt (u.2.isLt.trans_le hRm),
          ZMod.val_natCast_of_lt (v.2.isLt.trans_le hRm)] using he'⟩
  let box := univ.map emb
  have bounds {u : Torus m} (hu : u ∈ box) : u.1.val < R ∧ u.2.val < R := by
    obtain ⟨v, _, rfl⟩ := mem_map.mp hu
    change ((v.1.val : ZMod m)).val < R ∧ ((v.2.val : ZMod m)).val < R
    rw [ZMod.val_natCast_of_lt (v.1.isLt.trans_le hRm),
      ZMod.val_natCast_of_lt (v.2.isLt.trans_le hRm)]
    exact ⟨v.1.isLt, v.2.isLt⟩
  let color (u : Torus m) := col (point K u.1.val u.2.val)
  let I (r : Fin c) := box.filter (fun u => color u = r)
  have hind (r : Fin c) : ∀ i ∈ S, ∀ u ∈ I r, ∀ v ∈ I r, step m K i ≠ u - v := by
    intro i hi u hu v hv he
    obtain ⟨hub, hur⟩ := mem_filter.mp hu
    obtain ⟨hvb, hvr⟩ := mem_filter.mp hv
    have hb : (stepX K i).natAbs + (stepY K i).natAbs + 1 ≤ B :=
      single_le_sum (f := fun a => (stepX K a).natAbs + (stepY K a).natAbs + 1)
        (fun a _ => Nat.zero_le _) hi
    have bx : |stepX K i| < (B : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show (stepX K i).natAbs < B by omega)
    have by' : |stepY K i| < (B : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show (stepY K i).natAbs < B by omega)
    have ex : (stepX K i : ZMod m) = (u.1.val : ZMod m) - v.1.val := by
      simpa [step, ZMod.natCast_zmod_val] using congrArg Prod.fst he
    have ey : (stepY K i : ZMod m) = (u.2.val : ZMod m) - v.2.val := by
      simpa [step, ZMod.natCast_zmod_val] using congrArg Prod.snd he
    have ht : i.1 < K := mem_range.mp (mem_product.mp hi).1
    have ho : Odd (oddStep i.2.1 i.2.2) :=
      ⟨(i.2.1 : ℤ) - i.2.2, by unfold oddStep; ring⟩
    exact col.valid (edge ht ho
      (unwrap (le_refl m) (bounds hub).1 (bounds hvb).1 bx ex)
      (unwrap (le_refl m) (bounds hub).2 (bounds hvb).2 by' ey)) (hur.trans hvr.symm)
  have hratio (r : Fin c) :
      ((K : ℝ) + 5 / 2) * (I r).card ≤ (5 / 2 : ℝ) * (m : ℝ) ^ 2 := by
    have h := ratio S (step m K) (D := (n : ℝ) * (n + 1 : ℝ)) (I r) (hind r)
      (fun z => by rw [show S = steps K n from rfl, symbol_eq]; exact hmin _ (frequency_mem z))
    have hS : (S.card : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) = K := by
      simp only [S, steps, card_product, card_range, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    rwa [hS] at h
  have hcards : ∑ r : Fin c, ((I r).card : ℝ) = (R : ℝ) ^ 2 := by
    simpa [I, box, pow_two] using (sum_fiberwise box color (fun _ => (1 : ℝ)))
  have hsum := sum_le_sum (fun r (_ : r ∈ (univ : Finset (Fin c))) => hratio r)
  simp only [← mul_sum, hcards, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm : (m : ℝ) ≤ (11 / 10 : ℝ) * R := by
    dsimp [m, R]
    push_cast
    linarith [show (0 : ℝ) ≤ B by positivity]
  have hsq := (sq_le_sq₀ (show 0 ≤ (m : ℝ) by positivity)
    (show 0 ≤ (11 / 10 : ℝ) * R by positivity)).mpr hm
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (c : ℝ) * (5 / 2) by positivity)
  have hk : (c : ℝ) * (5 / 2) * (11 / 10) ^ 2 < (K : ℝ) + 5 / 2 := by
    dsimp [K]
    push_cast
    linarith [show (0 : ℝ) ≤ c by positivity]
  have hlt := mul_lt_mul_of_pos_right hk (show 0 < (R : ℝ) ^ 2 by positivity)
  nlinarith only [hsum, hmul, hlt]

end
end OddDistProof

theorem OMA.solution : type_of% @OMA.S_opg_coloring_the_odd_distance_graph.main := by
  by_contra h
  obtain ⟨c, hc⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp h
  exact OddDistProof.no_coloring c hc