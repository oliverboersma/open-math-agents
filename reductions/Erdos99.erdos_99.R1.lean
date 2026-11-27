import FormalConjectures.ErdosProblems.«99»

-- Reduction Erdos99.erdos_99.R1 of Erdős Problem 99
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: an explicit packing bound (n points, min distance 1, diameter at most 2 sqrt n).
-- H2: the remaining core, for configurations already satisfying the first-order
--     (contact/diametral) balance condition and the diameter bound, which are proved
--     necessary for minimizers below.

open Set Metric EuclideanGeometry Filter
open scoped InnerProductSpace Topology

namespace OMA.R_Erdos99_erdos_99_R1

private lemma exists_dist_eq_diam (A : Finset ℝ²) (hA : A.Nonempty) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) := by
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (A ×ˢ A)
    (fun z : ℝ² × ℝ² => dist z.1 z.2) (hA.product hA)
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hz
  refine ⟨z.1, hp, z.2, hq, le_antisymm
    (dist_le_diam_of_mem A.finite_toSet.isBounded hp hq) ?_⟩
  exact diam_le_of_forall_dist_le (dist_nonneg (x := z.1) (y := z.2))
    (fun p hp q hq => hmax (p, q) (Finset.mem_product.mpr ⟨hp, hq⟩))

/-- A competitor with distances at least one can be rescaled to attain distance one. -/
private lemma no_separated_improvement {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (f : ℝ² → ℝ²)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist (f p) (f q)) :
    ¬ (∀ p ∈ A, ∀ q ∈ A, dist (f p) (f q) < diam (A : Set ℝ²)) := by
  classical
  intro hsmall
  let pairs := (A ×ˢ A).filter (fun z => z.1 ≠ z.2)
  obtain ⟨p, hp, q, hq, hpq⟩ := hA.2
  have hpq_ne : p ≠ q := by
    intro h
    subst q
    simp at hpq
  have hpair : pairs.Nonempty :=
    ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq_ne⟩⟩
  obtain ⟨z, hz, hzmin⟩ :=
    Finset.exists_min_image pairs (fun w => dist (f w.1) (f w.2)) hpair
  obtain ⟨hzA, hz_ne⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hzA
  let d := dist (f z.1) (f z.2)
  have hd : 1 ≤ d := hsep z.1 hz₁ z.2 hz₂ hz_ne
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  let g := fun p => d⁻¹ • f p
  have hscale (p q : ℝ²) : dist (g p) (g q) = d⁻¹ * dist (f p) (f q) := by
    simp [g, dist_smul₀, Real.norm_eq_abs, abs_of_pos hdpos]
  have hgsep (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) (hne : p ≠ q) :
      1 ≤ dist (g p) (g q) := by
    rw [hscale, ← div_eq_inv_mul, le_div_iff₀ hdpos, one_mul]
    exact hzmin (p, q) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hne⟩)
  have hginj : Set.InjOn g (A : Set ℝ²) := by
    intro p hp q hq heq
    by_contra hne
    have hh := hgsep p hp q hq hne
    rw [heq, dist_self] at hh
    norm_num at hh
  let B := A.image g
  have hB : Erdos99.HasMinDist1 B := by
    constructor
    · intro x hx y hy hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact hgsep p hp q hq (fun heq => hxy (congrArg g heq))
    · refine ⟨g z.1, Finset.mem_image_of_mem g hz₁, g z.2, Finset.mem_image_of_mem g hz₂, ?_⟩
      rw [hscale]
      exact inv_mul_cancel₀ hdpos.ne'
  have hBmem : B ∈ {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} :=
    ⟨Finset.card_image_of_injOn hginj, hB⟩
  have hcompare : diam (A : Set ℝ²) ≤ diam (B : Set ℝ²) := hmin hBmem
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_dist_eq_diam B
    ⟨g p, Finset.mem_image_of_mem g hp⟩
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
  have hinv : d⁻¹ ≤ 1 := (inv_le_one₀ hdpos).mpr hd
  have hlt : dist (g p') (g q') < diam (A : Set ℝ²) := by
    rw [hscale]
    exact (mul_le_of_le_one_left dist_nonneg hinv).trans_lt (hsmall p' hp' q' hq')
  exact (not_lt_of_ge hcompare) (hxy ▸ hlt)

/-- At a minimum, no velocity can preserve the contacts to first order while
strictly shortening every diametral pair to first order. -/
private lemma no_contracting_velocity {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (v : ℝ² → ℝ²)
    (hunit : ∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
  by_contra! hdiam
  let move (t : ℝ) (x : ℝ²) := x + t • v x
  have hsquare (t : ℝ) (p q : ℝ²) :
      dist (move t p) (move t q) ^ 2 =
        dist p q ^ 2 + 2 * ⟪p - q, v p - v q⟫_ℝ * t + t ^ 2 * ‖v p - v q‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : move t p - move t q = (p - q) + t • (v p - v q) := by
      dsimp [move]
      rw [smul_sub]
      abel
    rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hpairs (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) := by
    have hc : Continuous (fun t : ℝ => dist (move t p) (move t q)) := by
      unfold move
      fun_prop
    have hzero : dist (move 0 p) (move 0 q) = dist p q := by simp [move]
    refine Eventually.and ?_ ?_
    · by_cases hu : dist p q = 1
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        have htpos : 0 ≤ t := (show 0 < t from ht).le
        rw [← sq_le_sq₀ zero_le_one dist_nonneg, hsquare, hu]
        have hlinear := mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
          (hunit p hp q hq hu)) htpos
        have hquadratic := mul_nonneg (sq_nonneg t) (sq_nonneg ‖v p - v q‖)
        linarith
      · by_cases hpq : p = q
        · exact Eventually.of_forall (fun _ hne => (hne hpq).elim)
        · have hstrict : 1 < dist (move 0 p) (move 0 q) :=
            hzero ▸ lt_of_le_of_ne (hA.1 p hp q hq hpq) (Ne.symm hu)
          exact (eventually_nhdsWithin_of_eventually_nhds
            (continuousAt_const.eventually_lt hc.continuousAt hstrict)).mono
              (fun _ ht _ => ht.le)
    · by_cases hd : dist p q = diam (A : Set ℝ²)
      · let coeff (t : ℝ) := 2 * ⟪p - q, v p - v q⟫_ℝ + t * ‖v p - v q‖ ^ 2
        have hcoeff : Continuous coeff := by unfold coeff; fun_prop
        have hneg : coeff 0 < 0 := by
          simpa [coeff] using mul_neg_of_pos_of_neg
            (by norm_num : (0 : ℝ) < 2) (hdiam p hp q hq hd)
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), coeff t < 0 :=
          eventually_nhdsWithin_of_eventually_nhds
            (hcoeff.continuousAt.eventually_lt continuousAt_const hneg)
        filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
        rw [← hd, ← sq_lt_sq₀ dist_nonneg dist_nonneg, hsquare]
        have hprod := mul_neg_of_pos_of_neg (show 0 < t from htpos) ht
        dsimp [coeff] at hprod
        nlinarith only [hprod]
      · have hstrict : dist (move 0 p) (move 0 q) < diam (A : Set ℝ²) := by
          rw [hzero]
          exact lt_of_le_of_ne (dist_le_diam_of_mem A.finite_toSet.isBounded hp hq) hd
        exact eventually_nhdsWithin_of_eventually_nhds
          (hc.continuousAt.eventually_lt continuousAt_const hstrict)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ A, ∀ q ∈ A,
      (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) :=
    (Finset.eventually_all A).mpr fun p hp =>
      (Finset.eventually_all A).mpr fun q hq => hpairs p hp q hq
  obtain ⟨t, ht⟩ := hall.exists
  exact no_separated_improvement hA hmin (move t)
    (fun p hp q hq => (ht p hp q hq).1) (fun p hp q hq => (ht p hp q hq).2)


def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n ∧
    (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧ (∃ p ∈ B, ∃ q ∈ B, dist p q = 1) ∧
    Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))) ≤ 2 * Real.sqrt n

def H2 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n →
    (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) → (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) →
    Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≤ 2 * Real.sqrt n →
    (∀ v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
      ∃ p ∈ A, ∃ q ∈ A, dist p q = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ∧
        0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
    (¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1) →
    ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n ∧
      (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
      Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))) <
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))

theorem main : H1 → H2 → type_of% @Erdos99.erdos_99 := by
  intro h1 h2
  filter_upwards [(eventually_ge_atTop 2).and h2] with n ⟨hn2, hn⟩
  intro A hcard hA hmin
  by_contra htri
  have hmin' : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A := by
    simpa only [hcard] using hmin
  obtain ⟨B, hBc, hBsep, hB1, hBd⟩ := h1 n hn2
  have hBmem : B ∈ {B : Finset ℝ² | B.card = n ∧ Erdos99.HasMinDist1 B} :=
    ⟨hBc, fun p hp q hq hpq => hBsep p hp q hq hpq, hB1⟩
  have hdA : diam (A : Set ℝ²) ≤ 2 * Real.sqrt n := (hmin hBmem).trans hBd
  have htri' : ¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
      dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1 := by
    rintro ⟨p, hp, q, hq, r, hr, h⟩
    exact htri ⟨p, hp, q, hq, r, hr, h⟩
  obtain ⟨C, hCc, hCsep, hCd⟩ := hn A hcard (fun p hp q hq hpq => hA.1 p hp q hq hpq) hA.2 hdA
    (fun v hv => no_contracting_velocity hA hmin' v hv) htri'
  classical
  let e : A ≃ C := Finset.equivOfCardEq (hcard.trans hCc.symm)
  let f (p : ℝ²) : ℝ² := if hp : p ∈ A then (e ⟨p, hp⟩ : ℝ²) else p
  have hf (p : ℝ²) (hp : p ∈ A) : f p = (e ⟨p, hp⟩ : ℝ²) := by simp [f, hp]
  have hmem (p : ℝ²) (hp : p ∈ A) : f p ∈ C := by
    rw [hf p hp]
    exact (e ⟨p, hp⟩).property
  refine no_separated_improvement hA hmin' f ?_ (fun p hp q hq =>
    (dist_le_diam_of_mem C.finite_toSet.isBounded (hmem p hp) (hmem q hq)).trans_lt hCd)
  intro p hp q hq hpq
  apply hCsep _ (hmem p hp) _ (hmem q hq)
  rw [hf p hp, hf q hq]
  intro heq
  exact hpq (congrArg Subtype.val (e.injective (Subtype.ext heq)))

end OMA.R_Erdos99_erdos_99_R1
