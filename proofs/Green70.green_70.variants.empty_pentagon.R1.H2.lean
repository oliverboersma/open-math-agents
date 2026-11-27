import OMAReductions.R_Green70_green_70_variants_empty_pentagon_R1
import Mathlib.Tactic

/-!
Proof of `Green70.green_70.variants.empty_pentagon.R1.H2`:
the convex-layer bound of Abel et al. (arXiv:0904.0262, Theorem 3).

For `k ≥ 3`, if a finite planar set `P` contains neither `k` collinear points nor an empty
pentagon, then any subset `S ⊆ P` in convex position (`S ⊆ frontier (convexHull ℝ S)`) has
`|S| < m(k)`.

The proof constructs a minimal large convex-position subset `A₁` (minimizing `|P ∩ conv(A₁)|`),
peels `k` nested convex layers `A₁, ..., A_k`, proves the layer-size recurrence
`|A_i| < 11 * k * (|A_{i+1}| + 2)` via purely algebraic cyclic ordering around an interior point,
and then tracks an empty arc `x₁ → y₁` of `A₁` through its followers `x_i → y_i` in `A_i` to
force either `k` collinear points or an empty pentagon.
-/

namespace Green70H2Proof

open Set Finset Green70 Classical
open scoped Topology

private abbrev Pt := ℝ × ℝ

/- ### Part 1: 2D orientation, Cramer's rule, convexity, and collinearity -/

private def det2 (u v : Pt) : ℝ := u.1 * v.2 - u.2 * v.1

private def orient (a b c : Pt) : ℝ := det2 (b - a) (c - a)

@[simp] private lemma det2_self (u : Pt) : det2 u u = 0 := by simp [det2]; ring

private lemma det2_plucker_snd (a b c : Pt) :
    a.2 * det2 b c - b.2 * det2 a c + c.2 * det2 a b = 0 := by
  simp [det2]; ring

private def orientLin (a b : Pt) : Pt →ₗ[ℝ] ℝ where
  toFun p := (b.1 - a.1) * p.2 - (b.2 - a.2) * p.1
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r p := by simp only [RingHom.id_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]; ring

private lemma orient_eq_lin (a b p : Pt) :
    orient a b p = orientLin a b p - orientLin a b a := by
  simp only [orient, det2, orientLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_sub, Prod.snd_sub]
  ring

private lemma orient_self_left (a b : Pt) : orient a a b = 0 := by
  simp [orient, det2]

private lemma orient_self_right (a b : Pt) : orient a b b = 0 := by
  simp [orient, det2]; ring

private lemma orient_self_mid (a b : Pt) : orient a b a = 0 := by
  simp [orient, det2]

private lemma orient_swap (a b c : Pt) : orient a c b = -orient a b c := by
  simp [orient, det2]; ring

private lemma orient_swap_fst (a b c : Pt) : orient b a c = -orient a b c := by
  simp [orient, det2]; ring

private lemma orient_cycle (a b c : Pt) : orient b c a = orient a b c := by
  simp [orient, det2]; ring

private lemma orient_collinear_of_three_on_line {a b p q r : Pt} (hab : a ≠ b)
    (hp : orient a b p = 0) (hq : orient a b q = 0) (hr : orient a b r = 0) :
    orient p q r = 0 := by
  have h1 : (b.1 - a.1) * orient p q r =
      (q.1 - p.1) * (orient a b r - orient a b p) - (r.1 - p.1) * (orient a b q - orient a b p) := by
    simp [orient, det2]; ring
  have h2 : (b.2 - a.2) * orient p q r =
      (q.2 - p.2) * (orient a b r - orient a b p) - (r.2 - p.2) * (orient a b q - orient a b p) := by
    simp [orient, det2]; ring
  rw [hp, hq, hr] at h1 h2
  by_cases hx : b.1 - a.1 = 0
  · have hy : b.2 - a.2 ≠ 0 := fun hy => hab (Prod.ext (by linarith) (by linarith))
    exact (mul_eq_zero.mp (by linarith : (b.2 - a.2) * orient p q r = 0)).resolve_left hy
  · exact (mul_eq_zero.mp (by linarith : (b.1 - a.1) * orient p q r = 0)).resolve_left hx

private lemma ray_hit_line_comb (a b z w p : Pt)
    (hp : orient a b p = 0) (hray : det2 (w - z) (p - z) = 0) :
    (orient a b z - orient a b w) • p = (-orient a b w) • z + orient a b z • w := by
  ext
  · have h1 : (orient a b z - orient a b w) * p.1 - ((-orient a b w) * z.1 + orient a b z * w.1) =
        (b.1 - a.1) * det2 (w - z) (p - z) - (w.1 - z.1) * orient a b p := by
      simp [orient, det2]; ring
    rw [hray, hp] at h1; simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]; linarith
  · have h2 : (orient a b z - orient a b w) * p.2 - ((-orient a b w) * z.2 + orient a b z * w.2) =
        (b.2 - a.2) * det2 (w - z) (p - z) - (w.2 - z.2) * orient a b p := by
      simp [orient, det2]; ring
    rw [hray, hp] at h2; simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]; linarith

private lemma orient_sum (a b c p : Pt) :
    orient b c p + orient c a p + orient a b p = orient a b c := by
  simp [orient, det2]; ring

private lemma cramer_triangle (a b c p : Pt) :
    orient b c p • a + orient c a p • b + orient a b p • c = orient a b c • p := by
  ext <;> simp [orient, det2] <;> ring

private lemma det2_cramer (u v w : Pt) :
    det2 w v • u + det2 u w • v = det2 u v • w := by
  ext <;> simp [det2] <;> ring

private lemma orient_sub (z a b c : Pt) : orient (a - z) (b - z) (c - z) = orient a b c := by
  simp [orient, det2]

private lemma orient_zero_right (a b : Pt) : orient a b 0 = det2 a b := by
  simp [orient, det2]; ring

private lemma orient_aff_comb (a b p q : Pt) (t : ℝ) :
    orient a b ((1 - t) • p + t • q) = (1 - t) * orient a b p + t * orient a b q := by
  simp [orient, det2]; ring

private lemma convexHull_orient_ge {S : Set Pt} {a b : Pt} {c : ℝ}
    (h : ∀ p ∈ S, c ≤ orient a b p) : ∀ p ∈ convexHull ℝ S, c ≤ orient a b p := by
  have hconv : Convex ℝ {p : Pt | c + orientLin a b a ≤ orientLin a b p} :=
    convex_halfSpace_ge (orientLin a b).isLinear _
  have hsub : convexHull ℝ S ⊆ {p : Pt | c + orientLin a b a ≤ orientLin a b p} :=
    convexHull_min (fun p hp => by
      change c + orientLin a b a ≤ orientLin a b p
      have := h p hp; rw [orient_eq_lin] at this; linarith) hconv
  intro p hp
  have hp' : c + orientLin a b a ≤ orientLin a b p := hsub hp
  rw [orient_eq_lin]; linarith

private lemma convexHull_orient_gt {S : Set Pt} {a b : Pt} {c : ℝ}
    (h : ∀ p ∈ S, c < orient a b p) : ∀ p ∈ convexHull ℝ S, c < orient a b p := by
  have hconv : Convex ℝ {p : Pt | c + orientLin a b a < orientLin a b p} :=
    convex_halfSpace_gt (orientLin a b).isLinear _
  have hsub : convexHull ℝ S ⊆ {p : Pt | c + orientLin a b a < orientLin a b p} :=
    convexHull_min (fun p hp => by
      change c + orientLin a b a < orientLin a b p
      have := h p hp; rw [orient_eq_lin] at this; linarith) hconv
  intro p hp
  have hp' : c + orientLin a b a < orientLin a b p := hsub hp
  rw [orient_eq_lin]; linarith

private lemma convexHull_orient_le {S : Set Pt} {a b : Pt} {c : ℝ}
    (h : ∀ p ∈ S, orient a b p ≤ c) : ∀ p ∈ convexHull ℝ S, orient a b p ≤ c := by
  have h' : ∀ p ∈ S, -c ≤ orient b a p := fun p hp => by
    rw [orient_swap_fst]; linarith [h p hp]
  intro p hp
  have := convexHull_orient_ge h' p hp
  rw [orient_swap_fst] at this; linarith

private lemma convexHull_orient_lt {S : Set Pt} {a b : Pt} {c : ℝ}
    (h : ∀ p ∈ S, orient a b p < c) : ∀ p ∈ convexHull ℝ S, orient a b p < c := by
  have h' : ∀ p ∈ S, -c < orient b a p := fun p hp => by
    rw [orient_swap_fst]; linarith [h p hp]
  intro p hp
  have := convexHull_orient_gt h' p hp
  rw [orient_swap_fst] at this; linarith

private lemma convexHull_lin_gt {S : Set Pt} {L : Pt →ₗ[ℝ] ℝ} {c : ℝ}
    (h : ∀ p ∈ S, c < L p) : ∀ p ∈ convexHull ℝ S, c < L p :=
  convexHull_min h (convex_halfSpace_gt L.isLinear c)

private lemma mem_convexHull_triangle_of_orient {a b c p : Pt}
    (hD : 0 < orient a b c)
    (h1 : 0 ≤ orient b c p) (h2 : 0 ≤ orient c a p) (h3 : 0 ≤ orient a b p) :
    p ∈ convexHull ℝ ({a, b, c} : Set Pt) := by
  set D := orient a b c
  set w1 := orient b c p / D
  set w2 := orient c a p / D
  set w3 := orient a b p / D
  have hw1 : 0 ≤ w1 := div_nonneg h1 hD.le
  have hw2 : 0 ≤ w2 := div_nonneg h2 hD.le
  have hw3 : 0 ≤ w3 := div_nonneg h3 hD.le
  have hsum : w1 + w2 + w3 = 1 := by
    simp only [w1, w2, w3]
    rw [← add_div, ← add_div, orient_sum, div_self hD.ne']
  have hp_eq : w1 • a + w2 • b + w3 • c = p := by
    have hcr := cramer_triangle a b c p
    ext
    · have hx := congrArg Prod.fst hcr
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul] at hx ⊢
      simp only [w1, w2, w3]; field_simp [hD.ne']; linarith
    · have hy := congrArg Prod.snd hcr
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hy ⊢
      simp only [w1, w2, w3]; field_simp [hD.ne']; linarith
  have ha : a ∈ convexHull ℝ ({a, b, c} : Set Pt) := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ convexHull ℝ ({a, b, c} : Set Pt) := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ convexHull ℝ ({a, b, c} : Set Pt) := subset_convexHull ℝ _ (by simp)
  by_cases h12 : w1 + w2 = 0
  · have h10 : w1 = 0 := by linarith
    have h20 : w2 = 0 := by linarith
    have h31 : w3 = 1 := by linarith
    rw [← hp_eq, h10, h20, h31]; simpa using hc
  · have hpos : 0 < w1 + w2 := lt_of_le_of_ne (by linarith) (Ne.symm h12)
    let q : Pt := (w1 / (w1 + w2)) • a + (w2 / (w1 + w2)) • b
    have hq : q ∈ convexHull ℝ ({a, b, c} : Set Pt) :=
      (convex_convexHull ℝ _) ha hb (div_nonneg hw1 hpos.le) (div_nonneg hw2 hpos.le)
        (by rw [← add_div, div_self hpos.ne'])
    have hcomb : (w1 + w2) • q + w3 • c = p := by
      rw [← hp_eq]
      ext <;> simp only [q, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
        field_simp [hpos.ne'] <;> ring
    rw [← hcomb]
    exact (convex_convexHull ℝ _) hq hc hpos.le hw3 hsum

private lemma mem_interior_triangle_of_orient {a b c p : Pt}
    (hD : 0 < orient a b c)
    (h1 : 0 < orient b c p) (h2 : 0 < orient c a p) (h3 : 0 < orient a b p) :
    p ∈ interior (convexHull ℝ ({a, b, c} : Set Pt)) := by
  let U : Set Pt := {x | 0 < orient b c x ∧ 0 < orient c a x ∧ 0 < orient a b x}
  have hcont : ∀ u v : Pt, Continuous (fun x : Pt => orient u v x) := fun u v => by
    simp only [orient, det2, Prod.fst_sub, Prod.snd_sub]
    fun_prop
  have hUopen : IsOpen U :=
    ((isOpen_lt continuous_const (hcont b c)).inter
      ((isOpen_lt continuous_const (hcont c a)).inter
        (isOpen_lt continuous_const (hcont a b))))
  have hUsub : U ⊆ convexHull ℝ ({a, b, c} : Set Pt) := fun x hx =>
    mem_convexHull_triangle_of_orient hD hx.1.le hx.2.1.le hx.2.2.le
  exact mem_interior.mpr ⟨U, hUsub, hUopen, h1, h2, h3⟩

private lemma convex_comb_mem_interior {K : Set Pt} (hK : Convex ℝ K)
    {z y : Pt} (hz : z ∈ interior K) (hy : y ∈ K) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) • z + t • y ∈ interior K := by
  obtain ⟨U, hUK, hUopen, hzU⟩ := mem_interior.mp hz
  let f : Pt → Pt := fun x => (1 - t)⁻¹ • (x - t • y)
  have hf_cont : Continuous f := by fun_prop
  have hVopen : IsOpen (f ⁻¹' U) := hUopen.preimage hf_cont
  have h1t : (1 - t : ℝ) ≠ 0 := by linarith
  have hVmem : (1 - t) • z + t • y ∈ f ⁻¹' U := by
    change (1 - t)⁻¹ • ((1 - t) • z + t • y - t • y) ∈ U
    rw [add_sub_cancel_right, inv_smul_smul₀ h1t]
    exact hzU
  have hVsub : f ⁻¹' U ⊆ K := by
    intro x hx
    have hfx : f x ∈ K := hUK hx
    have hx_eq : (1 - t) • f x + t • y = x := by
      simp only [f, smul_inv_smul₀ h1t, sub_add_cancel]
    rw [← hx_eq]
    exact hK hfx hy (by linarith) ht0.le (by ring)
  exact mem_interior.mpr ⟨f ⁻¹' U, hVsub, hVopen, hVmem⟩

private lemma frontier_convexHull_finset (S : Finset Pt) :
    frontier (convexHull ℝ (S : Set Pt)) =
      convexHull ℝ (S : Set Pt) \ interior (convexHull ℝ (S : Set Pt)) := by
  have hclosed : IsClosed (convexHull ℝ (S : Set Pt)) :=
    (S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  rw [frontier, hclosed.closure_eq]

private lemma orient_pos_of_mem_interior {S : Finset Pt} {a b w : Pt}
    (hge : ∀ p ∈ S, 0 ≤ orient a b p) (hab : a ≠ b)
    (hw : w ∈ interior (convexHull ℝ (S : Set Pt))) : 0 < orient a b w := by
  have hwge : 0 ≤ orient a b w := convexHull_orient_ge hge w (interior_subset hw)
  by_contra hnot
  have hw0 : orient a b w = 0 := le_antisymm (not_lt.mp hnot) hwge
  let d : Pt := (-(b.2 - a.2), b.1 - a.1)
  have hd_pos : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_contra h0
    have h1 : b.1 - a.1 = 0 := by nlinarith
    have h2 : b.2 - a.2 = 0 := by nlinarith
    exact hab (Prod.ext (by linarith) (by linarith))
  have hc : Continuous (fun t : ℝ => w + t • (-d)) := by fun_prop
  have ht : Filter.Tendsto (fun t : ℝ => w + t • (-d)) (𝓝[>] 0) (𝓝 w) := by
    simpa [ContinuousWithinAt] using hc.continuousAt.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, w + t • (-d) ∈ convexHull ℝ (S : Set Pt) :=
    ht (mem_interior_iff_mem_nhds.mp hw)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, (0 : ℝ) < t := self_mem_nhdsWithin
  obtain ⟨t, ht_pos, ht_mem⟩ := (hpos.and he).exists
  have hle := convexHull_orient_ge hge _ ht_mem
  have hcalc : orient a b (w + t • (-d)) = orient a b w - t * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    simp [orient, det2, d]; ring
  rw [hcalc, hw0] at hle
  nlinarith

private lemma mem_frontier_of_min_orient {S : Finset Pt} {a b p : Pt}
    (hp : p ∈ S) (hab : a ≠ b) (hmin : ∀ q ∈ S, orient a b p ≤ orient a b q) :
    p ∈ frontier (convexHull ℝ (S : Set Pt)) := by
  rw [frontier_convexHull_finset]
  refine ⟨subset_convexHull ℝ (S : Set Pt) hp, fun hi => ?_⟩
  let d : Pt := (-(b.2 - a.2), b.1 - a.1)
  have hd_pos : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_contra h0
    have h1 : b.1 - a.1 = 0 := by nlinarith
    have h2 : b.2 - a.2 = 0 := by nlinarith
    exact hab (Prod.ext (by linarith) (by linarith))
  have hc : Continuous (fun t : ℝ => p + t • (-d)) := by fun_prop
  have ht : Filter.Tendsto (fun t : ℝ => p + t • (-d)) (𝓝[>] 0) (𝓝 p) := by
    simpa [ContinuousWithinAt] using hc.continuousAt.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • (-d) ∈ convexHull ℝ (S : Set Pt) :=
    ht (mem_interior_iff_mem_nhds.mp hi)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, (0 : ℝ) < t := self_mem_nhdsWithin
  obtain ⟨t, ht_pos, ht_mem⟩ := (hpos.and he).exists
  have hle := convexHull_orient_ge hmin _ ht_mem
  have hcalc : orient a b (p + t • (-d)) = orient a b p - t * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    simp [orient, det2, d]; ring
  rw [hcalc] at hle
  nlinarith

private lemma collinear_of_orient_zero {T : Set Pt} {a b : Pt} (hab : a ≠ b)
    (h : ∀ p ∈ T, orient a b p = 0) : Collinear ℝ T := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, fun p hp => ?_⟩
  have ho : (b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1) = 0 := h p hp
  have hne : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
    by_contra h0; push Not at h0
    exact hab (Prod.ext (by linarith) (by linarith))
  rcases hne with hx | hy
  · refine ⟨(p.1 - a.1) / (b.1 - a.1), ?_⟩
    ext
    · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp [hx]; ring
    · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp [hx]; linarith
  · refine ⟨(p.2 - a.2) / (b.2 - a.2), ?_⟩
    ext
    · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp [hy]; linarith
    · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp [hy]; ring

private lemma collinear_of_interior_empty {S : Finset Pt}
    (hemp : interior (convexHull ℝ (S : Set Pt)) = ∅) : Collinear ℝ (S : Set Pt) := by
  by_cases h2 : S.card ≤ 1
  · obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp h2
    exact (collinear_singleton ℝ a).subset (by simpa using Finset.coe_subset.mpr ha)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    apply collinear_of_orient_zero hab
    intro c hc
    by_contra hne
    have hne_int : (interior (convexHull ℝ (S : Set Pt))).Nonempty := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hD : 0 < orient a c b := by rw [orient_swap]; linarith
        let m : Pt := (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • c + (1 / 3 : ℝ) • b
        have hm : m ∈ interior (convexHull ℝ ({a, c, b} : Set Pt)) := by
          apply mem_interior_triangle_of_orient hD
          · have : orient c b m = orient a c b / 3 := by simp [m, orient, det2]; ring
            linarith
          · have : orient b a m = orient a c b / 3 := by simp [m, orient, det2]; ring
            linarith
          · have : orient a c m = orient a c b / 3 := by simp [m, orient, det2]; ring
            linarith
        have hsub : ({a, c, b} : Set Pt) ⊆ (S : Set Pt) := by
          rintro x (rfl | rfl | rfl) <;> assumption
        exact ⟨m, interior_mono (convexHull_mono hsub) hm⟩
      · let m : Pt := (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b + (1 / 3 : ℝ) • c
        have hm : m ∈ interior (convexHull ℝ ({a, b, c} : Set Pt)) := by
          apply mem_interior_triangle_of_orient hgt
          · have : orient b c m = orient a b c / 3 := by simp [m, orient, det2]; ring
            linarith
          · have : orient c a m = orient a b c / 3 := by simp [m, orient, det2]; ring
            linarith
          · have : orient a b m = orient a b c / 3 := by simp [m, orient, det2]; ring
            linarith
        have hsub : ({a, b, c} : Set Pt) ⊆ (S : Set Pt) := by
          rintro x (rfl | rfl | rfl) <;> assumption
        exact ⟨m, interior_mono (convexHull_mono hsub) hm⟩
    rw [hemp] at hne_int
    exact Set.not_nonempty_empty hne_int

/- ### Part 2: Strict convex pentagon & splitting lemma -/

private lemma hasEmptyPentagon_of_cyclic5 {P : Finset Pt} (f : Fin 5 → Pt)
    (hmem : ∀ i : Fin 5, f i ∈ P)
    (hedges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j))
    (hempty : ∀ w ∈ P, w ∈ convexHull ℝ (Set.range f) → w ∈ Set.range f) :
    HasEmptyPentagon P := by
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    by_cases h1 : b = a + 1
    · subst h1
      have hpos := hedges a (a + 2) (by fin_cases a <;> decide) (by fin_cases a <;> decide)
      rw [hab, orient_self_left] at hpos; linarith
    · have hpos := hedges a b (Ne.symm hne) h1
      rw [← hab, orient_self_mid] at hpos; linarith
  let S : Finset Pt := Finset.univ.image f
  have hScoe : (S : Set Pt) = Set.range f := by ext x; simp [S]
  have hSP : S ⊆ P := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩; exact hmem i
  have hScard : S.card = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hconv : ConvexIndependent ℝ ((↑) : ↥(S : Set Pt) → Pt) := by
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro p hp
    rw [hScoe] at hp ⊢
    rcases hp with ⟨i, rfl⟩
    let L : Pt →ₗ[ℝ] ℝ := orientLin (f (i - 1)) (f i) + orientLin (f i) (f (i + 1))
    let c : ℝ := orientLin (f (i - 1)) (f i) (f (i - 1)) + orientLin (f i) (f (i + 1)) (f i)
    have hval : ∀ x : Pt, L x - c = orient (f (i - 1)) (f i) x + orient (f i) (f (i + 1)) x := by
      intro x
      simp only [L, c, LinearMap.add_apply, orient_eq_lin]
      ring
    have hgt : ∀ x ∈ Set.range f \ {f i}, c < L x := by
      rintro x ⟨⟨j, rfl⟩, hjne⟩
      have hji : j ≠ i := fun h => hjne (by simp [h])
      have hpos : 0 < orient (f (i - 1)) (f i) (f j) + orient (f i) (f (i + 1)) (f j) := by
        have hstep : (i - 1) + 1 = i := sub_add_cancel i 1
        by_cases hj1 : j = i - 1
        · subst hj1
          have h0 : orient (f (i - 1)) (f i) (f (i - 1)) = 0 := orient_self_mid _ _
          have h2 := hedges i (i - 1) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
          linarith
        · by_cases hj2 : j = i + 1
          · subst hj2
            have h0 : orient (f i) (f (i + 1)) (f (i + 1)) = 0 := orient_self_right _ _
            have h1 := hedges (i - 1) (i + 1) (by fin_cases i <;> decide) (by rw [hstep]; fin_cases i <;> decide)
            rw [hstep] at h1
            linarith
          · have h1 := hedges (i - 1) j hj1 (by rw [hstep]; exact hji)
            rw [hstep] at h1
            have h2 := hedges i j hji hj2
            linarith
      linarith [hval (f j)]
    intro hmem_hull
    have hlt := convexHull_lin_gt hgt (f i) hmem_hull
    have hzero : L (f i) - c = 0 := by
      rw [hval, orient_self_right, orient_self_mid, add_zero]
    linarith
  exact ⟨S, hSP, hScard, hconv, fun p hp hphull => by
    rw [hScoe] at hphull; rw [← Finset.mem_coe, hScoe]; exact hempty p hp hphull⟩

private lemma pentagon_split {f : Fin 5 → Pt}
    (hedges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j))
    {w : Pt} (hw : w ∈ convexHull ℝ (Set.range f)) :
    (0 ≤ orient (f 0) (f 2) w ∧ w ∈ convexHull ℝ ({f 0, f 2, f 3, f 4} : Set Pt)) ∨
    (orient (f 0) (f 2) w ≤ 0 ∧ w ∈ convexHull ℝ ({f 0, f 1, f 2} : Set Pt)) := by
  have hge : ∀ i : Fin 5, 0 ≤ orient (f i) (f (i + 1)) w := by
    intro i
    apply convexHull_orient_ge _ w hw
    rintro _ ⟨j, rfl⟩
    by_cases h1 : j = i
    · subst h1; rw [orient_self_mid]
    · by_cases h2 : j = i + 1
      · subst h2; rw [orient_self_right]
      · exact (hedges i j h1 h2).le
  by_cases h02 : 0 ≤ orient (f 0) (f 2) w
  · left
    refine ⟨h02, ?_⟩
    by_cases h03 : 0 ≤ orient (f 0) (f 3) w
    · have hD : 0 < orient (f 0) (f 3) (f 4) := by
        have := hedges 3 0 (by decide) (by decide)
        rwa [show (3 : Fin 5) + 1 = 4 by decide, orient_cycle] at this
      have hmem := mem_convexHull_triangle_of_orient hD (hge 3) (by simpa using hge 4) h03
      exact convexHull_mono (by rintro x (rfl | rfl | rfl) <;> simp) hmem
    · have h30 : 0 ≤ orient (f 3) (f 0) w := by
        rw [orient_swap_fst]; linarith
      have hD : 0 < orient (f 0) (f 2) (f 3) := by
        have := hedges 2 0 (by decide) (by decide)
        rwa [show (2 : Fin 5) + 1 = 3 by decide, orient_cycle] at this
      have hmem := mem_convexHull_triangle_of_orient hD (hge 2) h30 h02
      exact convexHull_mono (by rintro x (rfl | rfl | rfl) <;> simp) hmem
  · right
    refine ⟨(not_le.mp h02).le, ?_⟩
    have h20 : 0 ≤ orient (f 2) (f 0) w := by
      rw [orient_swap_fst]; linarith
    have hD : 0 < orient (f 0) (f 1) (f 2) := hedges 0 2 (by decide) (by decide)
    exact mem_convexHull_triangle_of_orient hD (hge 1) h20 (hge 0)

private def tuple5 (a b c d e : Pt) : Fin 5 → Pt
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e

private lemma cyclic5_edges_of_10 {a b c d e : Pt}
    (h012 : 0 < orient a b c) (h013 : 0 < orient a b d) (h014 : 0 < orient a b e)
    (h023 : 0 < orient a c d) (h024 : 0 < orient a c e) (h034 : 0 < orient a d e)
    (h123 : 0 < orient b c d) (h124 : 0 < orient b c e) (h134 : 0 < orient b d e)
    (h234 : 0 < orient c d e) :
    ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 →
      0 < orient (tuple5 a b c d e i) (tuple5 a b c d e (i + 1)) (tuple5 a b c d e j) := by
  have h120 : 0 < orient b c a := by rw [orient_cycle]; exact h012
  have h231 : 0 < orient c d b := by rw [orient_cycle]; exact h123
  have h230 : 0 < orient c d a := by rw [orient_cycle]; exact h023
  have h340 : 0 < orient d e a := by rw [orient_cycle]; exact h034
  have h341 : 0 < orient d e b := by rw [orient_cycle]; exact h134
  have h342 : 0 < orient d e c := by rw [orient_cycle]; exact h234
  have h401 : 0 < orient e a b := by rw [← orient_cycle]; exact h014
  have h402 : 0 < orient e a c := by rw [← orient_cycle]; exact h024
  have h403 : 0 < orient e a d := by rw [← orient_cycle]; exact h034
  intro i j hji hji1
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hji
    | exact absurd rfl hji1
    | assumption

/- ### Part 3: Purely algebraic polar cyclic order around an interior point `z` -/

private noncomputable def upperHalf (v : Pt) : Bool :=
  decide (0 < v.2 ∨ (v.2 = 0 ∧ 0 < v.1))

private lemma upperHalf_true_iff (v : Pt) :
    upperHalf v = true ↔ 0 < v.2 ∨ (v.2 = 0 ∧ 0 < v.1) := by
  simp [upperHalf]

private lemma upperHalf_false_iff {v : Pt} (hv : v ≠ 0) :
    upperHalf v = false ↔ v.2 < 0 ∨ (v.2 = 0 ∧ v.1 < 0) := by
  simp only [upperHalf, decide_eq_false_iff_not, not_or, not_lt, not_and]
  constructor
  · rintro ⟨hy, hx⟩
    rcases lt_or_eq_of_le hy with hlt | heq
    · exact Or.inl hlt
    · right
      refine ⟨heq, lt_of_le_of_ne (hx heq) ?_⟩
      intro hx0
      exact hv (Prod.ext hx0 heq)
  · rintro (hlt | ⟨heq, hx⟩)
    · exact ⟨hlt.le, fun h => by linarith⟩
    · exact ⟨heq.le, fun _ => hx.le⟩

private def angleLt (u v : Pt) : Prop :=
  (upperHalf u = true ∧ upperHalf v = false) ∨ (upperHalf u = upperHalf v ∧ 0 < det2 u v)

private lemma det2_trans_same_half {u v w : Pt} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : upperHalf u = upperHalf v) (hvw : upperHalf v = upperHalf w)
    (h1 : 0 < det2 u v) (h2 : 0 < det2 v w) : 0 < det2 u w := by
  have hpl := det2_plucker_snd u v w
  cases h : upperHalf u with
  | true =>
    have hu' := (upperHalf_true_iff u).mp h
    have hv' := (upperHalf_true_iff v).mp (huv.symm.trans h)
    have hw' := (upperHalf_true_iff w).mp (hvw.symm.trans (huv.symm.trans h))
    have hu2 : 0 ≤ u.2 := hu'.elim le_of_lt (fun h => h.1.ge)
    have hv2 : 0 < v.2 := hv'.resolve_right fun ⟨hv0, hv1⟩ => by
      have : det2 u v = -u.2 * v.1 := by simp [det2, hv0]
      nlinarith
    have hw2 : 0 < w.2 := hw'.resolve_right fun ⟨hw0, hw1⟩ => by
      have : det2 v w = -v.2 * w.1 := by simp [det2, hw0]
      nlinarith
    nlinarith
  | false =>
    have hu' := (upperHalf_false_iff hu).mp h
    have hv' := (upperHalf_false_iff hv).mp (huv.symm.trans h)
    have hw' := (upperHalf_false_iff hw).mp (hvw.symm.trans (huv.symm.trans h))
    have hu2 : u.2 ≤ 0 := hu'.elim le_of_lt (fun h => h.1.le)
    have hv2 : v.2 < 0 := hv'.resolve_right fun ⟨hv0, hv1⟩ => by
      have : det2 u v = -u.2 * v.1 := by simp [det2, hv0]
      nlinarith
    have hw2 : w.2 < 0 := hw'.resolve_right fun ⟨hw0, hw1⟩ => by
      have : det2 v w = -v.2 * w.1 := by simp [det2, hw0]
      nlinarith
    nlinarith

private lemma angleLt_irrefl (u : Pt) : ¬ angleLt u u := by
  rintro (⟨h1, h2⟩ | ⟨-, h⟩)
  · rw [h1] at h2; cases h2
  · rw [det2_self] at h; linarith

private lemma angleLt_trans {u v w : Pt} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h1 : angleLt u v) (h2 : angleLt v w) : angleLt u w := by
  rcases h1 with ⟨hu1, hv1⟩ | ⟨huv, hd1⟩ <;> rcases h2 with ⟨hv2, hw2⟩ | ⟨hvw, hd2⟩
  · rw [hv1] at hv2; cases hv2
  · left; exact ⟨hu1, hvw.symm.trans hv1⟩
  · left; exact ⟨huv.trans hv2, hw2⟩
  · right; exact ⟨huv.trans hvw, det2_trans_same_half hu hv hw huv hvw hd1 hd2⟩

private lemma same_ray_of_same_half_det_zero {u v : Pt} (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : upperHalf u = upperHalf v) (hd : det2 u v = 0) : ∃ t : ℝ, 0 < t ∧ v = t • u := by
  have hd' : u.1 * v.2 - u.2 * v.1 = 0 := hd
  cases h : upperHalf u with
  | true =>
    have hu' := (upperHalf_true_iff u).mp h
    have hv' := (upperHalf_true_iff v).mp (heq.symm.trans h)
    rcases hu' with huy | ⟨huy, hux⟩ <;> rcases hv' with hvy | ⟨hvy, hvx⟩
    · refine ⟨v.2 / u.2, div_pos hvy huy, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        field_simp [huy.ne'] <;> linarith
    · exfalso; rw [hvy] at hd'; nlinarith
    · exfalso; rw [huy] at hd'; nlinarith
    · refine ⟨v.1 / u.1, div_pos hvx hux, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      · field_simp [hux.ne']
      · rw [huy, hvy]; ring
  | false =>
    have hu' := (upperHalf_false_iff hu).mp h
    have hv' := (upperHalf_false_iff hv).mp (heq.symm.trans h)
    rcases hu' with huy | ⟨huy, hux⟩ <;> rcases hv' with hvy | ⟨hvy, hvx⟩
    · refine ⟨v.2 / u.2, div_pos_of_neg_of_neg hvy huy, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        field_simp [huy.ne] <;> linarith
    · exfalso; rw [hvy] at hd'; nlinarith
    · exfalso; rw [huy] at hd'; nlinarith
    · refine ⟨v.1 / u.1, div_pos_of_neg_of_neg hvx hux, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      · field_simp [hux.ne]
      · rw [huy, hvy]; ring

private lemma angleLt_trichotomy {u v : Pt} (hu : u ≠ 0) (hv : v ≠ 0) :
    angleLt u v ∨ angleLt v u ∨ ∃ t : ℝ, 0 < t ∧ v = t • u := by
  by_cases h : upperHalf u = upperHalf v
  · rcases lt_trichotomy (det2 u v) 0 with hlt | heq | hgt
    · right; left; right; exact ⟨h.symm, by simp only [det2] at hlt ⊢; linarith⟩
    · right; right; exact same_ray_of_same_half_det_zero hu hv h heq
    · left; right; exact ⟨h, hgt⟩
  · cases hu1 : upperHalf u <;> cases hv1 : upperHalf v
    · exact absurd (hu1.trans hv1.symm) h
    · right; left; left; exact ⟨hv1, hu1⟩
    · left; left; exact ⟨hu1, hv1⟩
    · exact absurd (hu1.trans hv1.symm) h

private lemma angleLt_of_det_pos_same_half {u v : Pt} (h : upperHalf u = upperHalf v)
    (hd : 0 < det2 u v) : angleLt u v := Or.inr ⟨h, hd⟩

private lemma det2_pos_of_pos_comb_left {a b w : Pt}
    (hab : 0 < det2 a b) (ha : 0 < det2 a w) (hb : 0 < det2 w b) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ w = α • a + β • b := by
  refine ⟨det2 w b / det2 a b, det2 a w / det2 a b, div_pos hb hab, div_pos ha hab, ?_⟩
  have hcr := det2_cramer a b w
  ext
  · have hx := congrArg Prod.fst hcr
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx ⊢
    field_simp [hab.ne']; linarith
  · have hy := congrArg Prod.snd hcr
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy ⊢
    field_simp [hab.ne']; linarith

-- Positive linear combination preserves upperHalf:
private lemma upperHalf_pos_comb' {a b w : Pt} (ha0 : a ≠ 0) (hb0 : b ≠ 0) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hw : w = α • a + β • b)
    (hsame : upperHalf a = upperHalf b) : upperHalf w = upperHalf a := by
  have hw1 : w.1 = α * a.1 + β * b.1 := by rw [hw]; simp
  have hw2 : w.2 = α * a.2 + β * b.2 := by rw [hw]; simp
  cases h : upperHalf a with
  | true =>
    rw [upperHalf_true_iff]
    have ha' := (upperHalf_true_iff a).mp h
    have hb' := (upperHalf_true_iff b).mp (hsame.symm.trans h)
    rcases ha' with ha2 | ⟨ha2, ha1⟩ <;> rcases hb' with hb2 | ⟨hb2, hb1⟩
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · right; exact ⟨by nlinarith, by nlinarith⟩
  | false =>
    have ha' := (upperHalf_false_iff ha0).mp h
    have hb' := (upperHalf_false_iff hb0).mp (hsame.symm.trans h)
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hw1 hw2
      simp only [Prod.fst_zero, Prod.snd_zero] at hw1 hw2
      rcases ha' with ha2 | ⟨ha2, ha1⟩ <;> rcases hb' with hb2 | ⟨hb2, hb1⟩ <;> nlinarith
    rw [upperHalf_false_iff hw0]
    rcases ha' with ha2 | ⟨ha2, ha1⟩ <;> rcases hb' with hb2 | ⟨hb2, hb1⟩
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · right; exact ⟨by nlinarith, by nlinarith⟩

private lemma det2_pos_of_angleLt_between {a b w : Pt}
    (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hab : 0 < det2 a b) :
    (0 < det2 a w ∧ 0 < det2 w b) ↔
      if upperHalf a = upperHalf b then angleLt a w ∧ angleLt w b
      else (upperHalf a = false ∧ upperHalf b = true ∧ (angleLt a w ∨ angleLt w b)) ∨
           (upperHalf a = true ∧ upperHalf b = false ∧ angleLt a w ∧ angleLt w b) := by
  split_ifs with hsame
  · constructor
    · rintro ⟨haw, hwb⟩
      obtain ⟨α, β, hα, hβ, hcomb⟩ := det2_pos_of_pos_comb_left hab haw hwb
      have hhw : upperHalf w = upperHalf a := upperHalf_pos_comb' ha hb hα hβ hcomb hsame
      exact ⟨Or.inr ⟨hhw.symm, haw⟩, Or.inr ⟨hhw.trans hsame, hwb⟩⟩
    · rintro ⟨h1, h2⟩
      have hhw : upperHalf w = upperHalf a := by
        rcases h1 with ⟨ha1, hw1⟩ | ⟨hh, -⟩
        · rcases h2 with ⟨hw2, -⟩ | ⟨hh, -⟩
          · rw [hw1] at hw2; cases hw2
          · rw [hsame, ← hh, hw1] at ha1; cases ha1
        · exact hh.symm
      have hd1 : 0 < det2 a w := by
        rcases h1 with ⟨ha1, hw1⟩ | ⟨-, hd⟩
        · rw [hhw, ha1] at hw1; cases hw1
        · exact hd
      have hd2 : 0 < det2 w b := by
        rcases h2 with ⟨hw2, hb2⟩ | ⟨-, hd⟩
        · rw [hhw, hsame, hb2] at hw2; cases hw2
        · exact hd
      exact ⟨hd1, hd2⟩
  · cases ha1 : upperHalf a <;> cases hb1 : upperHalf b
    · exact absurd (ha1.trans hb1.symm) hsame
    · -- a in lowerHalf (false), b in upperHalf (true): wraparound!
      simp only [ha1, hb1, true_and, false_and, or_false, Bool.false_eq_true, Bool.true_eq_false]
      constructor
      · rintro ⟨haw, hwb⟩
        cases hw1 : upperHalf w with
        | false => exact Or.inl (Or.inr ⟨ha1.trans hw1.symm, haw⟩)
        | true => exact Or.inr (Or.inr ⟨hw1.trans hb1.symm, hwb⟩)
      · rintro (h1 | h2)
        · have hw1 : upperHalf w = false := by
            rcases h1 with ⟨h', -⟩ | ⟨hh, -⟩
            · rw [ha1] at h'; cases h'
            · exact hh.symm.trans ha1
          have haw : 0 < det2 a w := by
            rcases h1 with ⟨h', -⟩ | ⟨-, hd⟩
            · rw [ha1] at h'; cases h'
            · exact hd
          refine ⟨haw, ?_⟩
          have ha' := (upperHalf_false_iff ha).mp ha1
          have hw' := (upperHalf_false_iff hw).mp hw1
          have hb' := (upperHalf_true_iff b).mp hb1
          have hpl := det2_plucker_snd a w b
          have hb2 : 0 ≤ b.2 := hb'.elim le_of_lt (fun h => h.1.ge)
          have ha2 : a.2 < 0 := ha'.resolve_right fun ⟨ha0, ha1'⟩ => by
            have : det2 a b = a.1 * b.2 := by simp [det2, ha0]
            nlinarith
          have hw2 : w.2 < 0 := hw'.resolve_right fun ⟨hw0, hw1'⟩ => by
            have : det2 a w = -a.2 * w.1 := by simp [det2, hw0]
            nlinarith
          nlinarith
        · have hw1 : upperHalf w = true := by
            rcases h2 with ⟨-, h'⟩ | ⟨hh, -⟩
            · rw [hb1] at h'; cases h'
            · exact hh.trans hb1
          have hwb : 0 < det2 w b := by
            rcases h2 with ⟨-, h'⟩ | ⟨-, hd⟩
            · rw [hb1] at h'; cases h'
            · exact hd
          refine ⟨?_, hwb⟩
          have ha' := (upperHalf_false_iff ha).mp ha1
          have hw' := (upperHalf_true_iff w).mp hw1
          have hb' := (upperHalf_true_iff b).mp hb1
          have hpl := det2_plucker_snd a w b
          have hw2 : 0 ≤ w.2 := hw'.elim le_of_lt (fun h => h.1.ge)
          have hb2 : 0 < b.2 := hb'.resolve_right fun ⟨hb0, hb1'⟩ => by
            have : det2 w b = -w.2 * b.1 := by simp [det2, hb0]
            nlinarith
          have ha2 : a.2 < 0 := ha'.resolve_right fun ⟨ha0, ha1'⟩ => by
            have : det2 a b = a.1 * b.2 := by simp [det2, ha0]
            nlinarith
          nlinarith
    · -- a in upperHalf (true), b in lowerHalf (false): non-wraparound crossing π!
      simp only [ha1, hb1, false_and, true_and, false_or, Bool.false_eq_true, Bool.true_eq_false]
      constructor
      · rintro ⟨haw, hwb⟩
        cases hw1 : upperHalf w with
        | true => exact ⟨Or.inr ⟨ha1.trans hw1.symm, haw⟩, Or.inl ⟨hw1, hb1⟩⟩
        | false => exact ⟨Or.inl ⟨ha1, hw1⟩, Or.inr ⟨hw1.trans hb1.symm, hwb⟩⟩
      · rintro ⟨h1, h2⟩
        cases hw1 : upperHalf w with
        | true =>
          have haw : 0 < det2 a w := by
            rcases h1 with ⟨-, h'⟩ | ⟨-, hd⟩
            · rw [hw1] at h'; cases h'
            · exact hd
          refine ⟨haw, ?_⟩
          have ha' := (upperHalf_true_iff a).mp ha1
          have hw' := (upperHalf_true_iff w).mp hw1
          have hb' := (upperHalf_false_iff hb).mp hb1
          have hpl := det2_plucker_snd a w b
          have hb2 : b.2 ≤ 0 := hb'.elim le_of_lt (fun h => h.1.le)
          have ha2 : 0 < a.2 := ha'.resolve_right fun ⟨ha0, ha1'⟩ => by
            have : det2 a b = a.1 * b.2 := by simp [det2, ha0]
            nlinarith
          have hw2 : 0 < w.2 := hw'.resolve_right fun ⟨hw0, hw1'⟩ => by
            have : det2 a w = -a.2 * w.1 := by simp [det2, hw0]
            nlinarith
          nlinarith
        | false =>
          have hwb : 0 < det2 w b := by
            rcases h2 with ⟨h', -⟩ | ⟨-, hd⟩
            · rw [hw1] at h'; cases h'
            · exact hd
          refine ⟨?_, hwb⟩
          have ha' := (upperHalf_true_iff a).mp ha1
          have hw' := (upperHalf_false_iff hw).mp hw1
          have hb' := (upperHalf_false_iff hb).mp hb1
          have hpl := det2_plucker_snd a w b
          have hw2 : w.2 ≤ 0 := hw'.elim le_of_lt (fun h => h.1.le)
          have hb2 : b.2 < 0 := hb'.resolve_right fun ⟨hb0, hb1'⟩ => by
            have : det2 w b = -w.2 * b.1 := by simp [det2, hb0]
            nlinarith
          have ha2 : 0 < a.2 := ha'.resolve_right fun ⟨ha0, ha1'⟩ => by
            have : det2 a b = a.1 * b.2 := by simp [det2, ha0]
            nlinarith
          nlinarith
    · exact absurd (ha1.trans hb1.symm) hsame

/- ### Part 4: Cyclic enumeration of a boundary layer `A` around an interior point `z` -/

private structure CyclicLayer (A : Finset Pt) (z : Pt) where
  n : ℕ
  hn : 3 ≤ n
  hcard : A.card = n
  u : Fin n → Pt
  hmem : ∀ i : Fin n, u i ∈ A
  hsurj : ∀ x ∈ A, ∃ i : Fin n, u i = x
  hinj : Function.Injective u
  hne : ∀ i : Fin n, u i ≠ z
  hmono : ∀ i j : Fin n, i < j → angleLt (u i - z) (u j - z)
  hfirst : upperHalf (u ⟨0, by omega⟩ - z) = true
  hlast : upperHalf (u ⟨n - 1, by omega⟩ - z) = false

private lemma CyclicLayer.hn0 {A : Finset Pt} {z : Pt} (C : CyclicLayer A z) : 0 < C.n := by
  have := C.hn; omega

private def cycNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ hn⟩

private lemma cycNext_val_of_lt {n : ℕ} (hn : 0 < n) {i : Fin n} (h : i.1 + 1 < n) :
    (cycNext hn i).1 = i.1 + 1 := Nat.mod_eq_of_lt h

private lemma cycNext_eq_zero_of_not_lt {n : ℕ} (hn : 0 < n) {i : Fin n} (h : ¬ i.1 + 1 < n) :
    cycNext hn i = ⟨0, hn⟩ :=
  Fin.ext (by simp only [cycNext]; rw [show i.1 + 1 = n by have := i.isLt; omega, Nat.mod_self])

private def cycPrev {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + n - 1) % n, Nat.mod_lt _ hn⟩

private lemma cycNext_prev {n : ℕ} (hn : 0 < n) (i : Fin n) :
    cycNext hn (cycPrev hn i) = i := by
  apply Fin.ext; simp only [cycNext, cycPrev]
  have hi := i.isLt
  by_cases h0 : i.1 = 0
  · rw [h0]; simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  · rw [show i.1 + n - 1 = n + (i.1 - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : i.1 - 1 < n), show i.1 - 1 + 1 = i.1 by omega,
      Nat.mod_eq_of_lt hi]

private lemma cycPrev_next {n : ℕ} (hn : 0 < n) (i : Fin n) :
    cycPrev hn (cycNext hn i) = i := by
  apply Fin.ext; simp only [cycNext, cycPrev]
  have hi := i.isLt
  by_cases hlast : i.1 + 1 = n
  · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]; omega
  · rw [Nat.mod_eq_of_lt (by omega : i.1 + 1 < n), show i.1 + 1 + n - 1 = n + i.1 by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hi]

private lemma build_cyclicLayer {A : Finset Pt} {z : Pt}
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) :
    Nonempty (CyclicLayer A z) := by
  have hne : ∀ x ∈ A, x ≠ z := fun x hx hxz => by
    have := hfront hx
    rw [frontier_convexHull_finset, hxz] at this
    exact this.2 hz
  have hno_ray : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ t : ℝ, 0 < t → y - z ≠ t • (x - z) := by
    intro x hx y hy hxy t ht heq
    have hfrontx := (frontier_convexHull_finset A ▸ hfront hx)
    have hfronty := (frontier_convexHull_finset A ▸ hfront hy)
    rcases lt_trichotomy t 1 with hlt | rfl | hgt
    · have hy_eq : y = (1 - t) • z + t • x := by
        ext
        · have := congrArg Prod.fst heq; simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at this
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith
        · have := congrArg Prod.snd heq; simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at this
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linarith
      rw [hy_eq] at hfronty
      exact hfronty.2 (convex_comb_mem_interior (convex_convexHull ℝ _) hz hfrontx.1 ht hlt)
    · apply hxy
      ext
      · have := congrArg Prod.fst heq; simp at this; linarith
      · have := congrArg Prod.snd heq; simp at this; linarith
    · have htinv0 : 0 < t⁻¹ := inv_pos.mpr ht
      have htinv1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
      have hx_eq : x = (1 - t⁻¹) • z + t⁻¹ • y := by
        ext
        · have := congrArg Prod.fst heq; simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at this
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          field_simp [ht.ne']; linarith
        · have := congrArg Prod.snd heq; simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at this
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          field_simp [ht.ne']; linarith
      rw [hx_eq] at hfrontx
      exact hfrontx.2 (convex_comb_mem_interior (convex_convexHull ℝ _) hz hfronty.1 htinv0 htinv1)
  -- Local linear order on {x // x ∈ A} via angleLt (x - z) (y - z)
  letI : LT {x : Pt // x ∈ A} := ⟨fun x y => angleLt (x.1 - z) (y.1 - z)⟩
  letI : LE {x : Pt // x ∈ A} := ⟨fun x y => x = y ∨ angleLt (x.1 - z) (y.1 - z)⟩
  letI : DecidableEq {x : Pt // x ∈ A} := inferInstance
  letI : LinearOrder {x : Pt // x ∈ A} :=
    { le := (· ≤ ·)
      lt := (· < ·)
      le_refl := fun _ => Or.inl rfl
      le_trans := fun a b c h1 h2 => by
        rcases h1 with rfl | h1
        · exact h2
        · rcases h2 with rfl | h2
          · exact Or.inr h1
          · exact Or.inr (angleLt_trans (sub_ne_zero.mpr (hne a.1 a.2))
              (sub_ne_zero.mpr (hne b.1 b.2)) (sub_ne_zero.mpr (hne c.1 c.2)) h1 h2)
      lt_iff_le_not_ge := fun a b => by
        constructor
        · intro h
          refine ⟨Or.inr h, ?_⟩
          rintro (rfl | hba)
          · exact angleLt_irrefl _ h
          · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (hne a.1 a.2))
              (sub_ne_zero.mpr (hne b.1 b.2)) (sub_ne_zero.mpr (hne a.1 a.2)) h hba)
        · rintro ⟨rfl | h, hnot⟩
          · exact absurd (Or.inl rfl) hnot
          · exact h
      le_antisymm := fun a b h1 h2 => by
        rcases h1 with rfl | h1
        · rfl
        · rcases h2 with rfl | h2
          · rfl
          · exact absurd (angleLt_trans (sub_ne_zero.mpr (hne a.1 a.2))
              (sub_ne_zero.mpr (hne b.1 b.2)) (sub_ne_zero.mpr (hne a.1 a.2)) h1 h2)
              (angleLt_irrefl _)
      le_total := fun a b => by
        by_cases hab : a = b
        · exact Or.inl (Or.inl hab)
        · rcases angleLt_trichotomy (sub_ne_zero.mpr (hne a.1 a.2))
            (sub_ne_zero.mpr (hne b.1 b.2)) with h1 | h2 | ⟨t, ht, heq⟩
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr h2)
          · exact absurd heq (hno_ray a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h)) t ht)
      toDecidableLE := Classical.decRel _ }
  have hn3 : 3 ≤ A.card := by
    by_contra hlt
    have hcol : Collinear ℝ (A : Set Pt) := by
      rcases (show A.card = 0 ∨ A.card = 1 ∨ A.card = 2 by omega) with h0 | h1 | h2
      · rw [Finset.card_eq_zero.mp h0]; simpa using collinear_empty ℝ Pt
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1; simpa using collinear_singleton ℝ a
      · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2; simpa using collinear_pair ℝ a b
    -- Any collinear finite set has empty interior of convexHull!
    have hlin : ∃ a b : Pt, a ≠ b ∧ ∀ p ∈ A, orient a b p = 0 := by
      rcases (show A.card = 0 ∨ A.card = 1 ∨ A.card = 2 by omega) with h0 | h1 | h2
      · refine ⟨(0, 0), (1, 0), by simp, fun p hp => by simp [Finset.card_eq_zero.mp h0] at hp⟩
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        refine ⟨a, a + (1, 0), by simp, fun p hp => ?_⟩
        rw [Finset.mem_singleton.mp hp, orient_self_mid]
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
        refine ⟨a, b, hab, fun p hp => ?_⟩
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact orient_self_mid p b
        · rw [Finset.mem_singleton.mp hp']; exact orient_self_right a b
    obtain ⟨a, b, hab, hor⟩ := hlin
    have hpos := orient_pos_of_mem_interior (fun p hp => (hor p hp).ge) hab hz
    have hle := convexHull_orient_le (fun p hp => (hor p hp).le) z (interior_subset hz)
    linarith
  let e : Fin A.card ≃o {x : Pt // x ∈ A} :=
    Fintype.orderIsoFinOfCardEq {x : Pt // x ∈ A} (Fintype.card_coe A)
  let u : Fin A.card → Pt := fun i => (e i).1
  have hmono : ∀ i j : Fin A.card, i < j → angleLt (u i - z) (u j - z) := fun i j hij => by
    have hle : e i = e j ∨ angleLt (u i - z) (u j - z) := e.map_rel_iff.mpr hij.le
    exact hle.resolve_left (fun h => hij.ne (e.injective h))
  have hsurj : ∀ x ∈ A, ∃ i : Fin A.card, u i = x := fun x hx =>
    ⟨e.symm ⟨x, hx⟩, by simp [u]⟩
  -- Since z ∈ interior (convexHull ℝ A), A has a point with y > z.2 (upperHalf = true)
  -- and a point with y < z.2 (upperHalf = false)!
  have hex_pos : ∃ i : Fin A.card, upperHalf (u i - z) = true := by
    by_contra hall
    push Not at hall
    have hle : ∀ p ∈ A, p.2 ≤ z.2 := fun p hp => by
      obtain ⟨i, rfl⟩ := hsurj p hp
      have hfalse : upperHalf (u i - z) = false := Bool.eq_false_iff.mpr (hall i)
      have := (upperHalf_false_iff (sub_ne_zero.mpr (hne (u i) (e i).2))).mp hfalse
      rcases this with h1 | ⟨h1, -⟩ <;> simp only [Prod.snd_sub] at h1 <;> linarith
    have hge_or : ∀ p ∈ A, 0 ≤ orient (z + (1, 0)) z p := fun p hp => by
      have := hle p hp; simp [orient, det2]; linarith
    have hpos := orient_pos_of_mem_interior hge_or (by simp) hz
    rw [orient_self_right] at hpos; linarith
  have hex_neg : ∃ i : Fin A.card, upperHalf (u i - z) = false := by
    by_contra hall
    push Not at hall
    have hge : ∀ p ∈ A, z.2 ≤ p.2 := fun p hp => by
      obtain ⟨i, rfl⟩ := hsurj p hp
      have htrue : upperHalf (u i - z) = true := by
        cases h : upperHalf (u i - z)
        · exact absurd h (hall i)
        · rfl
      have := (upperHalf_true_iff (u i - z)).mp htrue
      rcases this with h1 | ⟨h1, -⟩ <;> simp only [Prod.snd_sub] at h1 <;> linarith
    have hge_or : ∀ p ∈ A, 0 ≤ orient z (z + (1, 0)) p := fun p hp => by
      have := hge p hp; simp [orient, det2]; linarith
    have hpos := orient_pos_of_mem_interior hge_or (by simp) hz
    rw [orient_self_mid] at hpos; linarith
  have hfirst : upperHalf (u ⟨0, by omega⟩ - z) = true := by
    obtain ⟨i, hi⟩ := hex_pos
    by_cases h0 : i = ⟨0, by omega⟩
    · rwa [← h0]
    · have hlt : (⟨0, by omega⟩ : Fin A.card) < i := Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h))
      rcases hmono _ _ hlt with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact h1.trans hi
  have hlast : upperHalf (u ⟨A.card - 1, by omega⟩ - z) = false := by
    obtain ⟨i, hi⟩ := hex_neg
    by_cases h1 : i = ⟨A.card - 1, by omega⟩
    · rwa [← h1]
    · have hlt : i < ⟨A.card - 1, by omega⟩ := by
        show i.1 < A.card - 1; have := i.isLt
        by_contra hge; exact h1 (Fin.ext (by dsimp only; omega))
      rcases hmono _ _ hlt with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact h2
      · exact h2.symm.trans hi
  exact ⟨⟨A.card, hn3, rfl, u, fun i => (e i).2, hsurj,
    fun i j hij => e.injective (Subtype.ext hij), fun i => hne (u i) (e i).2,
    hmono, hfirst, hlast⟩⟩

/- Core properties of CyclicLayer -/

private lemma CyclicLayer.det_arc_pos {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n) :
    0 < det2 (C.u i - z) (C.u (cycNext C.hn0 i) - z) := by
  have hn0 : 0 < C.n := C.hn0
  let j := cycNext C.hn0 i
  by_contra hle
  push Not at hle
  -- Show every point p ∈ A satisfies 0 ≤ orient (C.u i) z p (i.e. det2 (C.u i - z) (p - z) ≤ 0)!
  have hall : ∀ p ∈ A, 0 ≤ orient (C.u i) z p := by
    intro p hp
    obtain ⟨k, rfl⟩ := C.hsurj p hp
    have hcalc : orient (C.u i) z (C.u k) = -det2 (C.u i - z) (C.u k - z) := by
      simp [orient, det2]; ring
    rw [hcalc]; apply neg_nonneg.mpr
    by_contra hpos
    push Not at hpos
    -- If 0 < det2 (u i - z) (u k - z), then u k lies strictly between u i and u j in cyclic order!
    have hki : k ≠ i := fun h => by rw [h, det2_self] at hpos; linarith
    have hkj : k ≠ j := fun h => by rw [h] at hpos; linarith
    by_cases hilast : i.1 + 1 < C.n
    · have hj_val : j.1 = i.1 + 1 := Nat.mod_eq_of_lt hilast
      have h_no_between : ¬ (angleLt (C.u i - z) (C.u k - z) ∧ angleLt (C.u k - z) (C.u j - z)) := by
        rintro ⟨h1, h2⟩
        have hik : i < k := by
          by_contra hge
          have hki' : k < i := lt_of_le_of_ne (not_lt.mp hge) hki
          exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne i))
            (sub_ne_zero.mpr (C.hne k)) (sub_ne_zero.mpr (C.hne i)) h1 (C.hmono k i hki'))
        have hkj' : k < j := by
          by_contra hge
          have hjk : j < k := lt_of_le_of_ne (not_lt.mp hge) hkj.symm
          exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne k))
            (sub_ne_zero.mpr (C.hne j)) (sub_ne_zero.mpr (C.hne k)) h2 (C.hmono j k hjk))
        have : i.1 < k.1 := hik
        have : k.1 < j.1 := hkj'
        omega
      -- Use upperHalf to show angleLt (u i - z) (u k - z) ∧ angleLt (u k - z) (u j - z)!
      have hij_lt : angleLt (C.u i - z) (C.u j - z) := C.hmono i j (show i.1 < j.1 by omega)
      cases hui : upperHalf (C.u i - z) with
      | true =>
        cases huk : upperHalf (C.u k - z) with
        | true =>
          have h1 : angleLt (C.u i - z) (C.u k - z) := Or.inr ⟨hui.trans huk.symm, hpos⟩
          cases huj : upperHalf (C.u j - z) with
          | false => exact h_no_between ⟨h1, Or.inl ⟨huk, huj⟩⟩
          | true =>
            exfalso
            rcases hij_lt with ⟨-, hbad⟩ | ⟨-, hd⟩
            · rw [huj] at hbad; cases hbad
            · linarith
        | false =>
          have h1 : angleLt (C.u i - z) (C.u k - z) := Or.inl ⟨hui, huk⟩
          cases huj : upperHalf (C.u j - z) with
          | true =>
            rcases hij_lt with ⟨-, hbad⟩ | ⟨-, hd⟩
            · rw [huj] at hbad; cases hbad
            · linarith
          | false =>
            have hdet_kj : 0 < det2 (C.u k - z) (C.u j - z) := by
              have hui' := (upperHalf_true_iff _).mp hui
              have huk' := (upperHalf_false_iff (sub_ne_zero.mpr (C.hne k))).mp huk
              have huj' := (upperHalf_false_iff (sub_ne_zero.mpr (C.hne j))).mp huj
              have hpl := det2_plucker_snd (C.u i - z) (C.u k - z) (C.u j - z)
              have hk2 : (C.u k - z).2 ≤ 0 := huk'.elim le_of_lt (fun h => h.1.le)
              have hi2 : 0 < (C.u i - z).2 := hui'.resolve_right fun ⟨hi0, hi1⟩ => by
                have : det2 (C.u i - z) (C.u k - z) = (C.u i - z).1 * (C.u k - z).2 := by simp [det2, hi0]
                nlinarith
              have hj2 : (C.u j - z).2 < 0 := huj'.resolve_right fun ⟨hj0, hj1⟩ => by
                have : det2 (C.u i - z) (C.u j - z) = -(C.u i - z).2 * (C.u j - z).1 := by
                  simp [det2, hj0]; ring
                nlinarith
              have hle' : det2 (C.u i - z) (C.u j - z) ≤ 0 := hle
              nlinarith
            exact h_no_between ⟨h1, Or.inr ⟨huk.trans huj.symm, hdet_kj⟩⟩
      | false =>
        cases huj : upperHalf (C.u j - z) with
        | true =>
          rcases hij_lt with ⟨hbad, -⟩ | ⟨hbad, -⟩
          · rw [hui] at hbad; cases hbad
          · rw [hui, huj] at hbad; cases hbad
        | false =>
          rcases hij_lt with ⟨hbad, -⟩ | ⟨-, hd⟩
          · rw [hui] at hbad; cases hbad
          · linarith
    · -- i = n - 1, j = 0: u i in false, u j in true!
      have hi_eq : i = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
      have hj_eq : j = ⟨0, by omega⟩ := Fin.ext (by
        simp only [j, cycNext]; rw [show i.1 + 1 = C.n by have := i.isLt; omega, Nat.mod_self])
      have hui : upperHalf (C.u i - z) = false := by rw [hi_eq]; exact C.hlast
      have huj : upperHalf (C.u j - z) = true := by rw [hj_eq]; exact C.hfirst
      cases huk : upperHalf (C.u k - z) with
      | false =>
        have hik : angleLt (C.u i - z) (C.u k - z) := Or.inr ⟨hui.trans huk.symm, hpos⟩
        have hki' : k < i := by
          show k.1 < i.1; have := k.isLt; rw [hi_eq] at hki ⊢
          by_contra hge; exact hki (Fin.ext (by omega))
        exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne i))
          (sub_ne_zero.mpr (C.hne k)) (sub_ne_zero.mpr (C.hne i)) hik (C.hmono k i hki'))
      | true =>
        have hkj' : j < k := by
          show j.1 < k.1; rw [hj_eq] at hkj ⊢
          exact Nat.pos_of_ne_zero (fun h => hkj (Fin.ext h))
        have hjk_lt := C.hmono j k hkj'
        have hd_jk : 0 < det2 (C.u j - z) (C.u k - z) := by
          rcases hjk_lt with ⟨-, hbad⟩ | ⟨-, hd⟩
          · rw [huk] at hbad; cases hbad
          · exact hd
        -- Now u i in false, u j, u k in true, det2 u_i u_j ≤ 0, det2 u_j u_k > 0, det2 u_i u_k > 0 -> impossible!
        have hui' := (upperHalf_false_iff (sub_ne_zero.mpr (C.hne i))).mp hui
        have huj' := (upperHalf_true_iff _).mp huj
        have huk' := (upperHalf_true_iff _).mp huk
        have hpl := det2_plucker_snd (C.u i - z) (C.u j - z) (C.u k - z)
        have hj2 : 0 ≤ (C.u j - z).2 := huj'.elim le_of_lt (fun h => h.1.ge)
        have hk2 : 0 < (C.u k - z).2 := huk'.resolve_right fun ⟨hk0, hk1⟩ => by
          have : det2 (C.u j - z) (C.u k - z) = -(C.u j - z).2 * (C.u k - z).1 := by
            simp [det2, hk0]; ring
          nlinarith
        have hi2 : (C.u i - z).2 < 0 := hui'.resolve_right fun ⟨hi0, hi1⟩ => by
          have : det2 (C.u i - z) (C.u k - z) = (C.u i - z).1 * (C.u k - z).2 := by simp [det2, hi0]
          nlinarith
        have hle' : det2 (C.u i - z) (C.u j - z) ≤ 0 := hle
        nlinarith
  have hpos := orient_pos_of_mem_interior hall (C.hne i) hz
  rw [orient_self_right] at hpos; linarith

private lemma CyclicLayer.arc_wedge_iff {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n) {w : Pt} (hw : w ≠ z) :
    (0 < det2 (C.u i - z) (w - z) ∧ 0 < det2 (w - z) (C.u (cycNext C.hn0 i) - z)) ↔
      (if i.1 + 1 < C.n then angleLt (C.u i - z) (w - z) ∧ angleLt (w - z) (C.u (cycNext C.hn0 i) - z)
       else angleLt (C.u i - z) (w - z) ∨ angleLt (w - z) (C.u ⟨0, C.hn0⟩ - z)) := by
  have hn0 : 0 < C.n := C.hn0
  have hd := C.det_arc_pos hz i
  have hiff := det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne i))
    (sub_ne_zero.mpr (C.hne (cycNext C.hn0 i))) (sub_ne_zero.mpr hw) hd
  rw [hiff]
  split_ifs with hsame hlt hlt
  · rfl
  · exfalso
    have hi_eq : i = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
    have hj_eq : cycNext C.hn0 i = ⟨0, C.hn0⟩ := cycNext_eq_zero_of_not_lt C.hn0 hlt
    rw [hj_eq, hi_eq, C.hlast, C.hfirst] at hsame
    cases hsame
  · have hij : angleLt (C.u i - z) (C.u (cycNext C.hn0 i) - z) :=
      C.hmono i (cycNext C.hn0 i) (show i.1 < (cycNext C.hn0 i).1 by rw [cycNext_val_of_lt C.hn0 hlt]; omega)
    rcases hij with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp [h1, h2]
    · exact absurd h1 hsame
  · have hi_eq : i = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
    have hj_eq : cycNext C.hn0 i = ⟨0, C.hn0⟩ := cycNext_eq_zero_of_not_lt C.hn0 hlt
    rw [hj_eq]
    have h1 : upperHalf (C.u i - z) = false := by rw [hi_eq]; exact C.hlast
    have h2 : upperHalf (C.u ⟨0, C.hn0⟩ - z) = true := C.hfirst
    simp [h1, h2]

private lemma CyclicLayer.arc_wedge_empty_of_mem {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n) (k : Fin C.n) :
    ¬ (0 < det2 (C.u i - z) (C.u k - z) ∧ 0 < det2 (C.u k - z) (C.u (cycNext C.hn0 i) - z)) := by
  intro h
  have hn0 : 0 < C.n := C.hn0
  rw [C.arc_wedge_iff hz i (C.hne k)] at h
  split_ifs at h with hlt
  · have hj_val : (cycNext C.hn0 i).1 = i.1 + 1 := Nat.mod_eq_of_lt hlt
    have hik : i < k := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hki
      · exact angleLt_irrefl _ h.1
      · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne i))
          (sub_ne_zero.mpr (C.hne k)) (sub_ne_zero.mpr (C.hne i)) h.1 (C.hmono k i hki))
    have hkj : k < cycNext hn0 i := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hjk
      · exact angleLt_irrefl _ h.2
      · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne k))
          (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne k)) h.2 (C.hmono _ k hjk))
    have : i.1 < k.1 := hik
    have : k.1 < (cycNext hn0 i).1 := hkj
    omega
  · have hi_eq : i = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
    rcases h with h1 | h2
    · by_cases hki : k = i
      · subst hki; exact angleLt_irrefl _ h1
      · have hlt' : k < i := by
          show k.1 < i.1; have := k.isLt; rw [hi_eq] at hki ⊢
          by_contra hge; exact hki (Fin.ext (by omega))
        exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne i))
          (sub_ne_zero.mpr (C.hne k)) (sub_ne_zero.mpr (C.hne i)) h1 (C.hmono k i hlt'))
    · by_cases hk0 : k = ⟨0, hn0⟩
      · subst hk0; exact angleLt_irrefl _ h2
      · have hlt' : (⟨0, hn0⟩ : Fin C.n) < k := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
        exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne k))
          (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne k)) h2 (C.hmono _ k hlt'))

private lemma CyclicLayer.arc_wedge_disjoint {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) {i j : Fin C.n} (hij : i ≠ j) {w : Pt} :
    ¬ ((0 < det2 (C.u i - z) (w - z) ∧ 0 < det2 (w - z) (C.u (cycNext C.hn0 i) - z)) ∧
       (0 < det2 (C.u j - z) (w - z) ∧ 0 < det2 (w - z) (C.u (cycNext C.hn0 j) - z))) := by
  rintro ⟨hi, hj⟩
  have hn0 : 0 < C.n := C.hn0
  have hw : w ≠ z := fun h => by rw [h, sub_self] at hi; simp [det2] at hi
  rw [C.arc_wedge_iff hz i hw] at hi
  rw [C.arc_wedge_iff hz j hw] at hj
  have htr : ∀ a b c : Pt, a ≠ z → b ≠ z → c ≠ z → angleLt (a - z) (b - z) →
      angleLt (b - z) (c - z) → angleLt (a - z) (c - z) := fun a b c ha hb hc =>
    angleLt_trans (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) (sub_ne_zero.mpr hc)
  have hmono_le : ∀ a b : Fin C.n, a ≤ b → ∀ x : Pt, x ≠ z →
      angleLt (C.u b - z) (x - z) → angleLt (C.u a - z) (x - z) := fun a b hab x hx hbx => by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact hbx
    · exact htr _ _ _ (C.hne a) (C.hne b) hx (C.hmono a b hlt) hbx
  split_ifs at hi with hilt <;> split_ifs at hj with hjlt
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : cycNext C.hn0 i ≤ j := by
        show (cycNext C.hn0 i).1 ≤ j.1
        rw [cycNext_val_of_lt C.hn0 hilt]; exact hlt
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne (cycNext C.hn0 i)) hw hi.2
        (hmono_le _ _ hle w hw hj.1))
    · have hle : cycNext C.hn0 j ≤ i := by
        show (cycNext C.hn0 j).1 ≤ i.1
        rw [cycNext_val_of_lt C.hn0 hjlt]; exact hgt
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne (cycNext C.hn0 j)) hw hj.2
        (hmono_le _ _ hle w hw hi.1))
  · have hj_eq : j = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
    rcases hj with hj1 | hj2
    · have hle : cycNext C.hn0 i ≤ j := by
        show (cycNext C.hn0 i).1 ≤ j.1; rw [cycNext_val_of_lt C.hn0 hilt, hj_eq]; dsimp only; omega
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne (cycNext C.hn0 i)) hw hi.2
        (hmono_le _ _ hle w hw hj1))
    · have hle : (⟨0, C.hn0⟩ : Fin C.n) ≤ i := Nat.zero_le _
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne ⟨0, C.hn0⟩) hw hj2 (hmono_le _ _ hle w hw hi.1))
  · have hi_eq : i = ⟨C.n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
    rcases hi with hi1 | hi2
    · have hle : cycNext C.hn0 j ≤ i := by
        show (cycNext C.hn0 j).1 ≤ i.1; rw [cycNext_val_of_lt C.hn0 hjlt, hi_eq]; dsimp only; omega
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne (cycNext C.hn0 j)) hw hj.2
        (hmono_le _ _ hle w hw hi1))
    · have hle : (⟨0, C.hn0⟩ : Fin C.n) ≤ j := Nat.zero_le _
      exact angleLt_irrefl _ (htr _ _ _ hw (C.hne ⟨0, C.hn0⟩) hw hi2 (hmono_le _ _ hle w hw hj.1))
  · exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))

private lemma CyclicLayer.exists_arc_cover {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) {w : Pt} (hw : w ≠ z) :
    (∃ i : Fin C.n, ∃ t : ℝ, 0 < t ∧ w - z = t • (C.u i - z)) ∨
    (∃ i : Fin C.n, 0 < det2 (C.u i - z) (w - z) ∧ 0 < det2 (w - z) (C.u (cycNext C.hn0 i) - z)) := by
  have hn0 : 0 < C.n := C.hn0
  by_cases hray : ∃ i : Fin C.n, ∃ t : ℝ, 0 < t ∧ w - z = t • (C.u i - z)
  · exact Or.inl hray
  · right
    have hcomp : ∀ i : Fin C.n, angleLt (C.u i - z) (w - z) ∨ angleLt (w - z) (C.u i - z) := by
      intro i
      rcases angleLt_trichotomy (sub_ne_zero.mpr (C.hne i)) (sub_ne_zero.mpr hw) with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd ⟨i, h3⟩ hray
    let S : Finset (Fin C.n) := Finset.univ.filter fun i => angleLt (w - z) (C.u i - z)
    by_cases hS : S.Nonempty
    · let j := S.min' hS
      have hj_lt : angleLt (w - z) (C.u j - z) := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
      by_cases hj0 : j.1 = 0
      · refine ⟨⟨C.n - 1, by omega⟩, ?_⟩
        rw [C.arc_wedge_iff hz ⟨C.n - 1, by omega⟩ hw]
        rw [if_neg (by dsimp only; omega)]
        right
        rwa [show (⟨0, hn0⟩ : Fin C.n) = j from Fin.ext hj0.symm]
      · let i : Fin C.n := ⟨j.1 - 1, by have := j.isLt; omega⟩
        have hilt : i.1 + 1 < C.n := by dsimp only [i]; have := j.isLt; omega
        have hnext : cycNext hn0 i = j := Fin.ext (by
          simp only [cycNext, i]; rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]; omega)
        have hi_not : ¬ angleLt (w - z) (C.u i - z) := fun hi_mem => by
          have hle := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_mem⟩)
          have : j.1 ≤ i.1 := hle
          dsimp only [i] at this; omega
        have hi_lt : angleLt (C.u i - z) (w - z) := (hcomp i).resolve_right hi_not
        refine ⟨i, ?_⟩
        rw [C.arc_wedge_iff hz i hw, if_pos hilt, hnext]
        exact ⟨hi_lt, hj_lt⟩
    · refine ⟨⟨C.n - 1, by omega⟩, ?_⟩
      rw [C.arc_wedge_iff hz ⟨C.n - 1, by omega⟩ hw, if_neg (by dsimp only; omega)]
      left
      refine (hcomp ⟨C.n - 1, by omega⟩).resolve_right fun h => hS ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

private lemma CyclicLayer.chord_outside_nonneg {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt)))
    {a b : Pt} (ha : a ∈ A) (hb : b ∈ A) (hab : 0 < det2 (a - z) (b - z))
    {w : Pt} (hw : w ∈ A)
    (hnotW : ¬ (0 < det2 (a - z) (w - z) ∧ 0 < det2 (w - z) (b - z))) :
    0 ≤ orient a b w := by
  by_contra hlt
  push Not at hlt
  have ha_ne : a ≠ z := fun h => by rw [h, sub_self] at hab; simp [det2] at hab
  have hb_ne : b ≠ z := fun h => by rw [h, sub_self] at hab; simp [det2] at hab
  have hDab : 0 < orient z a b := by
    have : orient z a b = det2 (a - z) (b - z) := by simp [orient, det2]
    linarith
  have hsum : orient a b w + orient b z w + orient z a w = orient z a b :=
    orient_sum z a b w
  have hbw : orient b z w = det2 (w - z) (b - z) := by simp [orient, det2]; ring
  have haw : orient z a w = det2 (a - z) (w - z) := by simp [orient, det2]
  have hnot_both_le : ¬ (det2 (a - z) (w - z) ≤ 0 ∧ det2 (w - z) (b - z) ≤ 0) := fun ⟨h1, h2⟩ => by
    linarith
  -- Either det2 (a - z) (w - z) ≤ 0 and det2 (w - z) (b - z) > 0, or vice versa!
  by_cases h1 : 0 < det2 (a - z) (w - z)
  · have h2 : det2 (w - z) (b - z) ≤ 0 := not_lt.mp fun h2' => hnotW ⟨h1, h2'⟩
    -- Then b ∈ interior (convexHull ℝ {z, a, w})!
    have hb_in : b ∈ interior (convexHull ℝ ({z, a, w} : Set Pt)) := by
      have hD : 0 < orient z a w := by linarith
      have ho1 : 0 < orient a w b := by rw [orient_swap]; linarith
      have ho2 : 0 < orient w z b := by
        have : orient w z b = -det2 (w - z) (b - z) := by simp [orient, det2]; ring
        rcases lt_or_eq_of_le h2 with h2lt | h2eq
        · linarith
        · exfalso
          have hwz : orient a b z = det2 (a - z) (b - z) := by simp [orient, det2]; ring
          have hb_comb : (orient a b z - orient a b w) • b = (-orient a b w) • z + orient a b z • w :=
            ray_hit_line_comb a b z w b (orient_self_right a b) h2eq
          set t := orient a b z / (orient a b z - orient a b w)
          have ht0 : 0 < t := div_pos (by linarith) (by linarith)
          have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          have hb_eq : b = (1 - t) • z + t • w := by
            have hden : orient a b z - orient a b w ≠ 0 := by linarith
            ext
            · have hx := congrArg Prod.fst hb_comb
              simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul] at hx ⊢
              simp only [t]; field_simp [hden]; linarith
            · have hy := congrArg Prod.snd hb_comb
              simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hy ⊢
              simp only [t]; field_simp [hden]; linarith
          have hb_int := convex_comb_mem_interior (convex_convexHull ℝ (A : Set Pt)) hz
            (subset_convexHull ℝ (A : Set Pt) hw) ht0 ht1
          rw [← hb_eq] at hb_int
          exact ((frontier_convexHull_finset A ▸ hfront hb).2) hb_int
      have ho3 : 0 < orient z a b := hDab
      exact mem_interior_triangle_of_orient hD ho1 ho2 ho3
    have hsub : ({z, a, w} : Set Pt) ⊆ convexHull ℝ (A : Set Pt) := by
      rintro x (rfl | rfl | rfl)
      · exact interior_subset hz
      · exact subset_convexHull ℝ _ ha
      · exact subset_convexHull ℝ _ hw
    have hb_int : b ∈ interior (convexHull ℝ (A : Set Pt)) := by
      have hm := interior_mono (convexHull_min hsub (convex_convexHull ℝ _)) hb_in
      exact hm
    exact ((frontier_convexHull_finset A ▸ hfront hb).2) hb_int
  · have h2 : 0 < det2 (w - z) (b - z) := by
      by_contra h2le; exact hnot_both_le ⟨not_lt.mp h1, not_lt.mp h2le⟩
    have h1le : det2 (a - z) (w - z) ≤ 0 := not_lt.mp h1
    -- Symmetrically, a ∈ interior (convexHull ℝ {z, w, b})!
    have ha_in : a ∈ interior (convexHull ℝ ({z, w, b} : Set Pt)) := by
      have hD : 0 < orient z w b := by
        have : orient z w b = det2 (w - z) (b - z) := by simp [orient, det2]
        linarith
      have ho1 : 0 < orient w b a := by rw [orient_cycle, orient_swap]; linarith
      have ho2 : 0 < orient b z a := by
        have : orient b z a = det2 (a - z) (b - z) := by simp [orient, det2]; ring
        linarith
      have ho3 : 0 < orient z w a := by
        have : orient z w a = -det2 (a - z) (w - z) := by simp [orient, det2]; ring
        rcases lt_or_eq_of_le h1le with h1lt | h1eq
        · linarith
        · exfalso
          have hwz : orient a b z = det2 (a - z) (b - z) := by simp [orient, det2]; ring
          have h1eq' : det2 (w - z) (a - z) = 0 := by simp [det2] at h1eq ⊢; linarith
          have ha_comb : (orient a b z - orient a b w) • a = (-orient a b w) • z + orient a b z • w :=
            ray_hit_line_comb a b z w a (orient_self_mid a b) h1eq'
          set t := orient a b z / (orient a b z - orient a b w)
          have ht0 : 0 < t := div_pos (by linarith) (by linarith)
          have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          have ha_eq : a = (1 - t) • z + t • w := by
            have hden : orient a b z - orient a b w ≠ 0 := by linarith
            ext
            · have hx := congrArg Prod.fst ha_comb
              simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul] at hx ⊢
              simp only [t]; field_simp [hden]; linarith
            · have hy := congrArg Prod.snd ha_comb
              simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hy ⊢
              simp only [t]; field_simp [hden]; linarith
          have ha_int := convex_comb_mem_interior (convex_convexHull ℝ (A : Set Pt)) hz
            (subset_convexHull ℝ (A : Set Pt) hw) ht0 ht1
          rw [← ha_eq] at ha_int
          exact ((frontier_convexHull_finset A ▸ hfront ha).2) ha_int
      exact mem_interior_triangle_of_orient hD ho1 ho2 ho3
    have hsub : ({z, w, b} : Set Pt) ⊆ convexHull ℝ (A : Set Pt) := by
      rintro x (rfl | rfl | rfl)
      · exact interior_subset hz
      · exact subset_convexHull ℝ _ hw
      · exact subset_convexHull ℝ _ hb
    have ha_int : a ∈ interior (convexHull ℝ (A : Set Pt)) :=
      interior_mono (convexHull_min hsub (convex_convexHull ℝ _)) ha_in
    exact ((frontier_convexHull_finset A ▸ hfront ha).2) ha_int

private lemma CyclicLayer.arc_supporting {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n) :
    ∀ w ∈ convexHull ℝ (A : Set Pt), 0 ≤ orient (C.u i) (C.u (cycNext C.hn0 i)) w := by
  apply convexHull_orient_ge
  intro p hp
  obtain ⟨k, rfl⟩ := C.hsurj p hp
  exact C.chord_outside_nonneg hfront hz (C.hmem i) (C.hmem _) (C.det_arc_pos hz i)
    (C.hmem k) (C.arc_wedge_empty_of_mem hz i k)

private lemma CyclicLayer.arc_supporting_interior {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n)
    {w : Pt} (hw : w ∈ interior (convexHull ℝ (A : Set Pt))) :
    0 < orient (C.u i) (C.u (cycNext C.hn0 i)) w := by
  have hne : C.u i ≠ C.u (cycNext C.hn0 i) := fun h => by
    have hd := C.det_arc_pos hz i; rw [h, det2_self] at hd; linarith
  exact orient_pos_of_mem_interior
    (fun p hp => C.arc_supporting hfront hz i p (subset_convexHull ℝ _ hp)) hne hw

private lemma CyclicLayer.arc_segment_empty {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt))) (i : Fin C.n)
    {w : Pt} (hw : w ∈ A) (hseg : w ∈ convexHull ℝ ({C.u i, C.u (cycNext C.hn0 i)} : Set Pt)) :
    w = C.u i ∨ w = C.u (cycNext C.hn0 i) := by
  have hn0 : 0 < C.n := C.hn0
  rw [convexHull_pair] at hseg
  rcases hseg with ⟨α, β, hα, hβ, hsum, rfl⟩
  by_cases hα0 : α = 0
  · right; rw [hα0, show β = 1 by linarith]; simp
  · by_cases hβ0 : β = 0
    · left; rw [hβ0, show α = 1 by linarith]; simp
    · exfalso
      obtain ⟨k, hk⟩ := C.hsurj _ hw
      have hd := C.det_arc_pos hz i
      have h1 : 0 < det2 (C.u i - z) (C.u k - z) := by
        rw [hk]
        have : α • C.u i + β • C.u (cycNext hn0 i) - z =
            α • (C.u i - z) + β • (C.u (cycNext hn0 i) - z) := by
          ext
          · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination z.1 * hsum
          · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination z.2 * hsum
        rw [this]
        have : det2 (C.u i - z) (α • (C.u i - z) + β • (C.u (cycNext hn0 i) - z)) =
            β * det2 (C.u i - z) (C.u (cycNext hn0 i) - z) := by simp [det2]; ring
        rw [this]; exact mul_pos (lt_of_le_of_ne hβ (Ne.symm hβ0)) hd
      have h2 : 0 < det2 (C.u k - z) (C.u (cycNext hn0 i) - z) := by
        rw [hk]
        have : α • C.u i + β • C.u (cycNext hn0 i) - z =
            α • (C.u i - z) + β • (C.u (cycNext hn0 i) - z) := by
          ext
          · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination z.1 * hsum
          · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination z.2 * hsum
        rw [this]
        have : det2 (α • (C.u i - z) + β • (C.u (cycNext hn0 i) - z)) (C.u (cycNext hn0 i) - z) =
            α * det2 (C.u i - z) (C.u (cycNext hn0 i) - z) := by simp [det2]; ring
        rw [this]; exact mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) hd
      exact C.arc_wedge_empty_of_mem hz i k ⟨h1, h2⟩

/- ### Part 5: Layer-size recurrence `|A| < 11 * k * (|A'| + 2)` -/

private lemma CyclicLayer.same_half_wedge_orient_le {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt)))
    {i j r : Fin C.n} (hij : i < j) (hjr : j < r)
    (hsame : upperHalf (C.u i - z) = upperHalf (C.u r - z)) :
    0 ≤ orient (C.u i) (C.u j) (C.u r) := by
  have hir_det : 0 < det2 (C.u i - z) (C.u r - z) := by
    rcases C.hmono i r (hij.trans hjr) with ⟨h1, h2⟩ | ⟨-, hd⟩
    · rw [hsame, h2] at h1; cases h1
    · exact hd
  have hj_wedge : 0 < det2 (C.u i - z) (C.u j - z) ∧ 0 < det2 (C.u j - z) (C.u r - z) := by
    rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne i)) (sub_ne_zero.mpr (C.hne r))
      (sub_ne_zero.mpr (C.hne j)) hir_det, if_pos hsame]
    exact ⟨C.hmono i j hij, C.hmono j r hjr⟩
  by_contra hlt
  push Not at hlt
  -- orient (u i) (u r) (u j) = -orient (u i) (u j) (u r) > 0, so u j ∈ interior (conv {z, u i, u r})!
  have hj_in : C.u j ∈ interior (convexHull ℝ ({z, C.u i, C.u r} : Set Pt)) := by
    apply mem_interior_triangle_of_orient
    · have : orient z (C.u i) (C.u r) = det2 (C.u i - z) (C.u r - z) := by simp [orient, det2]
      linarith
    · rw [orient_swap]; linarith
    · have : orient (C.u r) z (C.u j) = det2 (C.u j - z) (C.u r - z) := by simp [orient, det2]; ring
      linarith
    · have : orient z (C.u i) (C.u j) = det2 (C.u i - z) (C.u j - z) := by simp [orient, det2]
      linarith
  have hsub : ({z, C.u i, C.u r} : Set Pt) ⊆ convexHull ℝ (A : Set Pt) := by
    rintro x (rfl | rfl | rfl)
    · exact interior_subset hz
    · exact subset_convexHull ℝ _ (C.hmem i)
    · exact subset_convexHull ℝ _ (C.hmem r)
  have hj_int := interior_mono (convexHull_min hsub (convex_convexHull ℝ _)) hj_in
  exact (frontier_convexHull_finset A ▸ hfront (C.hmem j)).2 hj_int

private lemma CyclicLayer.same_half_orient_pos_of_corner {A : Finset Pt} {z : Pt} (C : CyclicLayer A z)
    (hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)))
    (hz : z ∈ interior (convexHull ℝ (A : Set Pt)))
    {i j r c : Fin C.n} (hij : i < j) (hjr : j < r)
    (hsame : upperHalf (C.u i - z) = upperHalf (C.u r - z))
    (hc1 : i < c) (hc2 : c < r)
    (hcorner : 0 < orient (C.u ⟨c.1 - 1, by have := c.isLt; omega⟩) (C.u c)
      (C.u ⟨c.1 + 1, by have := r.isLt; omega⟩)) :
    0 < orient (C.u i) (C.u j) (C.u r) := by
  have hge := C.same_half_wedge_orient_le hfront hz hij hjr hsame
  by_contra hnot
  have h0 : orient (C.u i) (C.u j) (C.u r) = 0 := le_antisymm (not_lt.mp hnot) hge
  have hir_det : 0 < det2 (C.u i - z) (C.u r - z) := by
    rcases C.hmono i r (hij.trans hjr) with ⟨h1, h2⟩ | ⟨-, hd⟩
    · rw [hsame, h2] at h1; cases h1
    · exact hd
  have hj_wedge : 0 < det2 (C.u i - z) (C.u j - z) ∧ 0 < det2 (C.u j - z) (C.u r - z) := by
    rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne i)) (sub_ne_zero.mpr (C.hne r))
      (sub_ne_zero.mpr (C.hne j)) hir_det, if_pos hsame]
    exact ⟨C.hmono i j hij, C.hmono j r hjr⟩
  -- Every s with i ≤ s ≤ r MUST satisfy orient (u i) (u r) (u s) = 0!
  have hall_col : ∀ s : Fin C.n, i ≤ s → s ≤ r → orient (C.u i) (C.u r) (C.u s) = 0 := by
    intro s his hsr
    rcases eq_or_lt_of_le his with rfl | h1
    · exact orient_self_mid _ _
    · rcases eq_or_lt_of_le hsr with rfl | h2
      · exact orient_self_right _ _
      · have hle : orient (C.u i) (C.u r) (C.u s) ≤ 0 := by
          rw [orient_swap]; linarith [C.same_half_wedge_orient_le hfront hz h1 h2 hsame]
        by_contra hne
        have hlt : orient (C.u i) (C.u r) (C.u s) < 0 := lt_of_le_of_ne hle hne
        -- Then u j lies in openSegment (u i) (u r), hence in interior (conv {z, u i, u r, u s})!
        have hs_det : 0 < det2 (C.u i - z) (C.u s - z) ∧ 0 < det2 (C.u s - z) (C.u r - z) := by
          rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne i)) (sub_ne_zero.mpr (C.hne r))
            (sub_ne_zero.mpr (C.hne s)) hir_det, if_pos hsame]
          exact ⟨C.hmono i s h1, C.hmono s r h2⟩
        -- u j = α u i + β u r with α, β > 0, α + β = 1!
        have hsum_d_raw : det2 (C.u j - z) (C.u r - z) + det2 (C.u i - z) (C.u j - z) =
            det2 (C.u i - z) (C.u r - z) := by
          simp only [orient, det2, Prod.fst_sub, Prod.snd_sub] at h0 ⊢; linarith
        set αj := det2 (C.u j - z) (C.u r - z) / det2 (C.u i - z) (C.u r - z)
        set βj := det2 (C.u i - z) (C.u j - z) / det2 (C.u i - z) (C.u r - z)
        have hαβ_sum : αj + βj = 1 := by
          simp only [αj, βj]; rw [← add_div, hsum_d_raw, div_self hir_det.ne']
        have hj_eq : C.u j = αj • C.u i + βj • C.u r := by
          have hcr := det2_cramer (C.u i - z) (C.u r - z) (C.u j - z)
          ext
          · have hx := congrArg Prod.fst hcr
            simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at hx ⊢
            have hmul : det2 (C.u i - z) (C.u r - z) * (C.u j).1 =
                det2 (C.u j - z) (C.u r - z) * (C.u i).1 + det2 (C.u i - z) (C.u j - z) * (C.u r).1 := by
              linear_combination -hx - z.1 * hsum_d_raw
            simp only [αj, βj]; field_simp [hir_det.ne']; linarith
          · have hy := congrArg Prod.snd hcr
            simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at hy ⊢
            have hmul : det2 (C.u i - z) (C.u r - z) * (C.u j).2 =
                det2 (C.u j - z) (C.u r - z) * (C.u i).2 + det2 (C.u i - z) (C.u j - z) * (C.u r).2 := by
              linear_combination -hy - z.2 * hsum_d_raw
            simp only [αj, βj]; field_simp [hir_det.ne']; linarith
        -- Choose m = convex comb of z and u s on the chord u i u r -> Wait: even simpler!
        -- Pick ε > 0 small so (z, u i, u s) or (z, u s, u r) — actually u j ∈ interior of quad {z, u i, u s, u r}!
        -- Since orient (u i) (u r) z > 0 and orient (u i) (u r) (u s) < 0, the triangle containing u j is
        -- either {z, u i, u s} (if det2(u s - z, u j - z) < 0), {z, u s, u r} (if > 0), or segment (z, u s)!
        have hj_int : C.u j ∈ interior (convexHull ℝ (A : Set Pt)) := by
          rcases lt_trichotomy (det2 (C.u s - z) (C.u j - z)) 0 with hjs | hjs | hjs
          · -- u j ∈ interior (conv {z, u i, u s})!
            have hD : 0 < orient z (C.u i) (C.u s) := by
              have : orient z (C.u i) (C.u s) = det2 (C.u i - z) (C.u s - z) := by simp [orient, det2]
              linarith [hs_det.1]
            have ho1 : 0 < orient (C.u i) (C.u s) (C.u j) := by
              have hβ : 0 < βj := div_pos hj_wedge.1 hir_det
              have hlin : orient (C.u i) (C.u s) (C.u j) = βj * orient (C.u i) (C.u s) (C.u r) := by
                rw [hj_eq, show αj = 1 - βj by linarith, orient_aff_comb, orient_self_mid]; ring
              rw [hlin]
              exact mul_pos hβ (by rw [orient_swap]; linarith)
            have ho2 : 0 < orient (C.u s) z (C.u j) := by
              have : orient (C.u s) z (C.u j) = -det2 (C.u s - z) (C.u j - z) := by simp [orient, det2]; ring
              linarith
            have ho3 : 0 < orient z (C.u i) (C.u j) := by
              have : orient z (C.u i) (C.u j) = det2 (C.u i - z) (C.u j - z) := by simp [orient, det2]
              linarith [hj_wedge.1]
            have hsub : ({z, C.u i, C.u s} : Set Pt) ⊆ convexHull ℝ (A : Set Pt) := by
              rintro x (rfl | rfl | rfl)
              · exact interior_subset hz
              · exact subset_convexHull ℝ _ (C.hmem i)
              · exact subset_convexHull ℝ _ (C.hmem s)
            exact interior_mono (convexHull_min hsub (convex_convexHull ℝ _))
              (mem_interior_triangle_of_orient hD ho1 ho2 ho3)
          · -- det2 (u s - z) (u j - z) = 0, so u j lies on openSegment z (u s)!
            have hz_or : orient (C.u i) (C.u r) z = det2 (C.u i - z) (C.u r - z) := by
              simp [orient, det2]; ring
            have h0' : orient (C.u i) (C.u r) (C.u j) = 0 := by rw [orient_swap]; linarith
            have hcomb : (orient (C.u i) (C.u r) z - orient (C.u i) (C.u r) (C.u s)) • C.u j =
                (-orient (C.u i) (C.u r) (C.u s)) • z + orient (C.u i) (C.u r) z • C.u s :=
              ray_hit_line_comb (C.u i) (C.u r) z (C.u s) (C.u j) h0' hjs
            set t := orient (C.u i) (C.u r) z / (orient (C.u i) (C.u r) z - orient (C.u i) (C.u r) (C.u s))
            have hden : orient (C.u i) (C.u r) z - orient (C.u i) (C.u r) (C.u s) ≠ 0 := by linarith
            have ht0 : 0 < t := div_pos (by linarith) (by linarith)
            have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
            have hj_eq' : C.u j = (1 - t) • z + t • C.u s := by
              ext
              · have hx := congrArg Prod.fst hcomb
                simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul] at hx ⊢
                simp only [t]; field_simp [hden]; linarith
              · have hy := congrArg Prod.snd hcomb
                simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hy ⊢
                simp only [t]; field_simp [hden]; linarith
            rw [hj_eq']
            exact convex_comb_mem_interior (convex_convexHull ℝ _) hz (subset_convexHull ℝ _ (C.hmem s)) ht0 ht1
          · -- u j ∈ interior (conv {z, u s, u r})!
            have hD : 0 < orient z (C.u s) (C.u r) := by
              have : orient z (C.u s) (C.u r) = det2 (C.u s - z) (C.u r - z) := by simp [orient, det2]
              linarith [hs_det.2]
            have ho1 : 0 < orient (C.u s) (C.u r) (C.u j) := by
              have hα : 0 < αj := div_pos hj_wedge.2 hir_det
              have hlin : orient (C.u s) (C.u r) (C.u j) = αj * orient (C.u s) (C.u r) (C.u i) := by
                rw [hj_eq, show αj = 1 - βj by linarith, orient_aff_comb, orient_self_right]; ring
              rw [hlin]
              exact mul_pos hα (by rw [orient_cycle, orient_swap]; linarith)
            have ho2 : 0 < orient (C.u r) z (C.u j) := by
              have : orient (C.u r) z (C.u j) = det2 (C.u j - z) (C.u r - z) := by simp [orient, det2]; ring
              linarith [hj_wedge.2]
            have ho3 : 0 < orient z (C.u s) (C.u j) := by
              have : orient z (C.u s) (C.u j) = det2 (C.u s - z) (C.u j - z) := by simp [orient, det2]
              linarith
            have hsub : ({z, C.u s, C.u r} : Set Pt) ⊆ convexHull ℝ (A : Set Pt) := by
              rintro x (rfl | rfl | rfl)
              · exact interior_subset hz
              · exact subset_convexHull ℝ _ (C.hmem s)
              · exact subset_convexHull ℝ _ (C.hmem r)
            exact interior_mono (convexHull_min hsub (convex_convexHull ℝ _))
              (mem_interior_triangle_of_orient hD ho1 ho2 ho3)
        exact (frontier_convexHull_finset A ▸ hfront (C.hmem j)).2 hj_int
  -- Now u (c-1), u c, u (c+1) ALL lie on line (u i, u r), so orient (u (c-1)) (u c) (u (c+1)) = 0!
  have hcm1 := hall_col ⟨c.1 - 1, by have := c.isLt; omega⟩ (by show i.1 ≤ c.1 - 1; have : i.1 < c.1 := hc1; omega)
    (by show c.1 - 1 ≤ r.1; have : c.1 < r.1 := hc2; omega)
  have hc0 := hall_col c hc1.le hc2.le
  have hcp1 := hall_col ⟨c.1 + 1, by have := r.isLt; omega⟩
    (by show i.1 ≤ c.1 + 1; have : i.1 < c.1 := hc1; omega)
    (by show c.1 + 1 ≤ r.1; have : c.1 < r.1 := hc2; omega)
  have hir_ne : C.u i ≠ C.u r := fun h => by rw [h, det2_self] at hir_det; linarith
  have hcol3 : orient (C.u ⟨c.1 - 1, by have := c.isLt; omega⟩) (C.u c)
      (C.u ⟨c.1 + 1, by have := r.isLt; omega⟩) = 0 :=
    orient_collinear_of_three_on_line hir_ne hcm1 hc0 hcp1
  linarith

private lemma layer_card_bound {P A : Finset Pt} {k : ℕ} (hk : 3 ≤ k)
    (hAP : A ⊆ P)
    (hA_full : A = P.filter fun p => p ∈ frontier (convexHull ℝ (A : Set Pt)))
    (hnocol : ¬ HasCollinear k P) (hnopent : ¬ HasEmptyPentagon P) :
    let I := P.filter fun p => p ∈ interior (convexHull ℝ (A : Set Pt))
    let A' := P.filter fun p => p ∈ frontier (convexHull ℝ (I : Set Pt))
    A.card < 11 * k * (A'.card + 2) := by
  intro I A'
  have hfront : (A : Set Pt) ⊆ frontier (convexHull ℝ (A : Set Pt)) := fun p hp => by
    have : p ∈ A := hp; rw [hA_full] at this; exact (Finset.mem_filter.mp this).2
  by_cases hemp : interior (convexHull ℝ (A : Set Pt)) = ∅
  · have hcol := collinear_of_interior_empty hemp
    have hlt : A.card < k := by
      by_contra hge
      obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq (not_lt.mp hge)
      exact hnocol ⟨T, hTA.trans hAP, hTcard, hcol.subset (Finset.coe_subset.mpr hTA)⟩
    nlinarith
  · obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨C⟩ := build_cyclicLayer hfront hz
    by_contra hbig
    push Not at hbig
    have hbig' : 11 * k * (A'.card + 2) ≤ C.n := C.hcard ▸ hbig
    -- Block t (for t < A'.card + 2) spans indices [t * (11 * k), (t + 1) * (11 * k) - 1]
    let B := 11 * k
    have hB_pos : 0 < B := by omega
    have hblock_hi : ∀ t : Fin (A'.card + 2), t.1 * B + B ≤ C.n := fun t => by
      have h1 : (t.1 + 1) * B ≤ (A'.card + 2) * B := Nat.mul_le_mul_right B (by omega)
      have h2 : (t.1 + 1) * B = t.1 * B + B := by ring
      have h3 : (A'.card + 2) * B = 11 * k * (A'.card + 2) := by dsimp only [B]; ring
      omega
    let aIdx : Fin (A'.card + 2) → Fin C.n := fun t =>
      ⟨t.1 * B, by have := hblock_hi t; omega⟩
    let bIdx : Fin (A'.card + 2) → Fin C.n := fun t =>
      ⟨t.1 * B + B - 1, by have := hblock_hi t; omega⟩
    -- At most ONE block has upperHalf (u (aIdx t) - z) ≠ upperHalf (u (bIdx t) - z)!
    have hgood_count : ∃ T : Finset (Fin (A'.card + 2)), A'.card + 1 ≤ T.card ∧
        ∀ t ∈ T, upperHalf (C.u (aIdx t) - z) = upperHalf (C.u (bIdx t) - z) := by
      let bad := Finset.univ.filter fun t : Fin (A'.card + 2) =>
        upperHalf (C.u (aIdx t) - z) ≠ upperHalf (C.u (bIdx t) - z)
      have hbad_le1 : bad.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro t1 ht1 t2 ht2
        have h1 := (Finset.mem_filter.mp ht1).2
        have h2 := (Finset.mem_filter.mp ht2).2
        have h1tf : upperHalf (C.u (aIdx t1) - z) = true ∧ upperHalf (C.u (bIdx t1) - z) = false := by
          have hab1 : aIdx t1 < bIdx t1 := by show t1.1 * B < t1.1 * B + B - 1; omega
          rcases C.hmono (aIdx t1) (bIdx t1) hab1 with ⟨ht, hf⟩ | ⟨heq, -⟩
          · exact ⟨ht, hf⟩
          · exact absurd heq h1
        have h2tf : upperHalf (C.u (aIdx t2) - z) = true ∧ upperHalf (C.u (bIdx t2) - z) = false := by
          have hab2 : aIdx t2 < bIdx t2 := by show t2.1 * B < t2.1 * B + B - 1; omega
          rcases C.hmono (aIdx t2) (bIdx t2) hab2 with ⟨ht, hf⟩ | ⟨heq, -⟩
          · exact ⟨ht, hf⟩
          · exact absurd heq h2
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hba : bIdx t1 < aIdx t2 := by
            show t1.1 * B + B - 1 < t2.1 * B
            have h1 : (t1.1 + 1) * B ≤ t2.1 * B := Nat.mul_le_mul_right B hlt
            have h2 : (t1.1 + 1) * B = t1.1 * B + B := by ring
            omega
          rcases C.hmono (bIdx t1) (aIdx t2) hba with ⟨hbad, -⟩ | ⟨hbad, -⟩
          · rw [h1tf.2] at hbad; cases hbad
          · rw [h1tf.2, h2tf.1] at hbad; cases hbad
        · have hba : bIdx t2 < aIdx t1 := by
            show t2.1 * B + B - 1 < t1.1 * B
            have h1 : (t2.1 + 1) * B ≤ t1.1 * B := Nat.mul_le_mul_right B hgt
            have h2 : (t2.1 + 1) * B = t2.1 * B + B := by ring
            omega
          rcases C.hmono (bIdx t2) (aIdx t1) hba with ⟨hbad, -⟩ | ⟨hbad, -⟩
          · rw [h2tf.2] at hbad; cases hbad
          · rw [h2tf.2, h1tf.1] at hbad; cases hbad
      let good := Finset.univ.filter fun t : Fin (A'.card + 2) =>
        upperHalf (C.u (aIdx t) - z) = upperHalf (C.u (bIdx t) - z)
      have hsum : good.card + bad.card = A'.card + 2 := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (A'.card + 2))))
          (fun t => upperHalf (C.u (aIdx t) - z) = upperHalf (C.u (bIdx t) - z))
        simpa [good, bad] using this
      exact ⟨good, by omega, fun t ht => (Finset.mem_filter.mp ht).2⟩
    obtain ⟨T, hTcard, hTgood⟩ := hgood_count
    -- For each t ∈ T, extract a point p_t ∈ A' strictly inside open wedge W z (u (aIdx t)) (u (bIdx t))!
    have hex_pt : ∀ t ∈ T, ∃ p ∈ A',
        0 < det2 (C.u (aIdx t) - z) (p - z) ∧ 0 < det2 (p - z) (C.u (bIdx t) - z) := by
      intro t ht
      have hsame := hTgood t ht
      have hab_lt : aIdx t < bIdx t := by show t.1 * B < t.1 * B + B - 1; omega
      have hab_det : 0 < det2 (C.u (aIdx t) - z) (C.u (bIdx t) - z) := by
        rcases C.hmono (aIdx t) (bIdx t) hab_lt with ⟨h1, h2⟩ | ⟨-, hd⟩
        · rw [hsame, h2] at h1; cases h1
        · exact hd
      -- In each of 11 sub-windows of length k - 1 inside (aIdx t, bIdx t), find a corner!
      have hex_corner : ∀ s : Fin 11, ∃ c : Fin C.n,
          (aIdx t).1 + 1 + s.1 * (k - 1) ≤ c.1 ∧ c.1 < (aIdx t).1 + 1 + (s.1 + 1) * (k - 1) ∧
          ∃ hc1 : c.1 + 1 < C.n,
            0 < orient (C.u ⟨c.1 - 1, by have := c.isLt; omega⟩) (C.u c) (C.u ⟨c.1 + 1, hc1⟩) := by
        intro s
        by_contra hnone
        push Not at hnone
        -- Then k consecutive points starting at base := (aIdx t).1 + s.1 * (k - 1) are collinear!
        let base := (aIdx t).1 + s.1 * (k - 1)
        have hbase_hi : base + k - 1 < C.n := by
          have hs10 : s.1 ≤ 10 := by omega
          have hm : s.1 * (k - 1) ≤ 10 * (k - 1) := Nat.mul_le_mul_right (k - 1) hs10
          have hbh := hblock_hi t
          dsimp only [base, aIdx, B] at hbh ⊢
          omega
        have hzero : ∀ r : ℕ, (hr : r < k - 2) →
            orient (C.u ⟨base + r, by omega⟩) (C.u ⟨base + r + 1, by omega⟩)
              (C.u ⟨base + r + 2, by omega⟩) = 0 := by
          intro r hr
          let c : Fin C.n := ⟨base + r + 1, by omega⟩
          have hc_val : c.1 = base + r + 1 := rfl
          have hc1 : c.1 + 1 < C.n := by omega
          have hc_lo : (aIdx t).1 + 1 + s.1 * (k - 1) ≤ c.1 := by dsimp only [base] at hc_val ⊢; omega
          have hc_hi : c.1 < (aIdx t).1 + 1 + (s.1 + 1) * (k - 1) := by
            have hmul : (s.1 + 1) * (k - 1) = s.1 * (k - 1) + (k - 1) := by rw [Nat.add_mul, one_mul]
            dsimp only [base] at hc_val ⊢; omega
          have hle := hnone c hc_lo hc_hi hc1
          have hge : 0 ≤ orient (C.u ⟨c.1 - 1, by omega⟩) (C.u c) (C.u ⟨c.1 + 1, hc1⟩) := by
            have hnext : cycNext C.hn0 ⟨c.1 - 1, by omega⟩ = c := Fin.ext (by
              rw [cycNext_val_of_lt C.hn0 (by dsimp only; omega)]; dsimp only; omega)
            have hsup := C.arc_supporting hfront hz ⟨c.1 - 1, by omega⟩
              (C.u ⟨c.1 + 1, hc1⟩) (subset_convexHull ℝ _ (C.hmem _))
            rwa [hnext] at hsup
          have heq1 : (⟨c.1 - 1, by omega⟩ : Fin C.n) = ⟨base + r, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          have heq2 : (⟨c.1 + 1, hc1⟩ : Fin C.n) = ⟨base + r + 2, by omega⟩ :=
            Fin.ext rfl
          rw [heq1, heq2] at hle hge
          exact le_antisymm hle hge
        -- By strong induction on r < k, every u (base + r) lies on line (u base, u (base + 1))!
        have hall_line_strong : ∀ r : ℕ, (hr : r < k) →
            orient (C.u ⟨base, by omega⟩) (C.u ⟨base + 1, by omega⟩) (C.u ⟨base + r, by omega⟩) = 0 := by
          intro r
          induction r using Nat.strongRecOn with
          | ind r ih =>
            intro hr
            by_cases hr0 : r = 0
            · subst hr0; exact orient_self_mid _ _
            · by_cases hr1 : r = 1
              · subst hr1; exact orient_self_right _ _
              · have h1 := ih (r - 1) (by omega) (by omega)
                have h2 := ih (r - 2) (by omega) (by omega)
                have hstep := hzero (r - 2) (by omega)
                have e1 : (⟨base + (r - 2), by omega⟩ : Fin C.n) = ⟨base + (r - 2), by omega⟩ := rfl
                have e2 : (⟨base + (r - 2) + 1, by omega⟩ : Fin C.n) = ⟨base + (r - 1), by omega⟩ :=
                  Fin.ext (by dsimp only; omega)
                have e3 : (⟨base + (r - 2) + 2, by omega⟩ : Fin C.n) = ⟨base + r, by omega⟩ :=
                  Fin.ext (by dsimp only; omega)
                rw [e2, e3] at hstep
                have hne_pair : C.u ⟨base + (r - 2), by omega⟩ ≠ C.u ⟨base + (r - 1), by omega⟩ := fun h => by
                  have := congrArg Fin.val (C.hinj h); dsimp only at this; omega
                have hne_01 : C.u ⟨base, by omega⟩ ≠ C.u ⟨base + 1, by omega⟩ := fun h => by
                  have := congrArg Fin.val (C.hinj h); dsimp only at this; omega
                have ha_on : orient (C.u ⟨base + (r - 2), by omega⟩) (C.u ⟨base + (r - 1), by omega⟩) (C.u ⟨base, by omega⟩) = 0 :=
                  orient_collinear_of_three_on_line hne_01 h2 h1 (orient_self_mid _ _)
                have hb_on : orient (C.u ⟨base + (r - 2), by omega⟩) (C.u ⟨base + (r - 1), by omega⟩) (C.u ⟨base + 1, by omega⟩) = 0 :=
                  orient_collinear_of_three_on_line hne_01 h2 h1 (orient_self_right _ _)
                exact orient_collinear_of_three_on_line hne_pair ha_on hb_on hstep
        let Kset : Finset Pt := Finset.univ.image fun r : Fin k => C.u ⟨base + r.1, by omega⟩
        have hKsub : Kset ⊆ P := by
          intro x hx; rcases Finset.mem_image.mp hx with ⟨r, -, rfl⟩; exact hAP (C.hmem _)
        have hKcard : Kset.card = k := by
          rw [Finset.card_image_of_injective _ (fun r1 r2 h => Fin.ext (by
            have := congrArg Fin.val (C.hinj h); dsimp only at this; omega)),
            Finset.card_univ, Fintype.card_fin]
        have hKcol : Collinear ℝ (Kset : Set Pt) := by
          apply collinear_of_orient_zero (a := C.u ⟨base, by omega⟩) (b := C.u ⟨base + 1, by omega⟩)
          · intro h; have := congrArg Fin.val (C.hinj h); dsimp only at this; omega
          · intro p hp
            rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨r, -, rfl⟩
            exact hall_line_strong r.1 r.isLt
        exact hnocol ⟨Kset, hKsub, hKcard, hKcol⟩
      -- Pick 11 corners c 0 < c 1 < ... < c 10!
      let c : Fin 11 → Fin C.n := fun s => (hex_corner s).choose
      have hc_spec : ∀ s : Fin 11, (aIdx t).1 + 1 + s.1 * (k - 1) ≤ (c s).1 ∧
          (c s).1 < (aIdx t).1 + 1 + (s.1 + 1) * (k - 1) ∧
          ∃ hc1 : (c s).1 + 1 < C.n,
            0 < orient (C.u ⟨(c s).1 - 1, by have := (c s).isLt; omega⟩) (C.u (c s)) (C.u ⟨(c s).1 + 1, hc1⟩) :=
        fun s => (hex_corner s).choose_spec
      have hc_lt : ∀ s1 s2 : Fin 11, s1 < s2 → c s1 < c s2 := fun s1 s2 h12 => by
        show (c s1).1 < (c s2).1
        have h1 := (hc_spec s1).2.1
        have h2 := (hc_spec s2).1
        have : s1.1 + 1 ≤ s2.1 := h12
        nlinarith
      have hc_bounds : ∀ s : Fin 11, aIdx t < c s ∧ c s < bIdx t := fun s => by
        have h1 := (hc_spec s).1
        have h2 := (hc_spec s).2.1
        have hm : (s.1 + 1) * (k - 1) ≤ 11 * (k - 1) := Nat.mul_le_mul_right (k - 1) (by omega)
        constructor
        · show (aIdx t).1 < (c s).1; omega
        · show (c s).1 < (bIdx t).1; dsimp only [aIdx, bIdx, B] at h1 h2 ⊢; omega
      have hsame_sub : ∀ r1 r2 : Fin C.n, aIdx t ≤ r1 → r1 < r2 → r2 ≤ bIdx t →
          upperHalf (C.u r1 - z) = upperHalf (C.u r2 - z) := by
        intro r1 r2 h1 h12 h2
        have hr1_eq : upperHalf (C.u r1 - z) = upperHalf (C.u (aIdx t) - z) := by
          rcases eq_or_lt_of_le h1 with rfl | hlt
          · rfl
          · have hm1 := C.hmono (aIdx t) r1 hlt
            have hm2 := C.hmono r1 (bIdx t) (lt_of_lt_of_le h12 h2)
            rcases hm1 with ⟨ha1, hr1⟩ | ⟨heq, -⟩
            · rcases hm2 with ⟨hr2, -⟩ | ⟨heq, -⟩
              · rw [hr1] at hr2; cases hr2
              · rw [← heq, hr1] at hsame; rw [ha1] at hsame; cases hsame
            · exact heq.symm
        have hr2_eq : upperHalf (C.u r2 - z) = upperHalf (C.u (aIdx t) - z) := by
          rcases eq_or_lt_of_le h2 with rfl | hlt
          · exact hsame.symm
          · have hm1 := C.hmono (aIdx t) r2 (lt_of_le_of_lt h1 h12)
            have hm2 := C.hmono r2 (bIdx t) hlt
            rcases hm1 with ⟨ha1, hr2⟩ | ⟨heq, -⟩
            · rcases hm2 with ⟨hr2', -⟩ | ⟨heq, -⟩
              · rw [hr2] at hr2'; cases hr2'
              · rw [← heq, hr2] at hsame; rw [ha1] at hsame; cases hsame
            · exact heq.symm
        exact hr1_eq.trans hr2_eq.symm
      -- Build the 5-gon f : Fin 5 → Pt using corners c 1, c 3, c 5, c 7, c 9!
      let qIdx : Fin 5 → Fin C.n := fun m => c ⟨2 * m.1 + 1, by have := m.isLt; omega⟩
      let f : Fin 5 → Pt := fun m => C.u (qIdx m)
      have hq_mono : ∀ m1 m2 : Fin 5, m1 < m2 → qIdx m1 < qIdx m2 := fun m1 m2 h12 =>
        hc_lt _ _ (show 2 * m1.1 + 1 < 2 * m2.1 + 1 by have : m1.1 < m2.1 := h12; omega)
      have hq_between_corner : ∀ m1 m2 : Fin 5, m1 < m2 →
          ∃ s : Fin 11, qIdx m1 < c s ∧ c s < qIdx m2 := fun m1 m2 h12 =>
        ⟨⟨2 * m1.1 + 2, by have := m1.isLt; have := m2.isLt; have : m1.1 < m2.1 := h12; omega⟩,
          hc_lt _ _ (show 2 * m1.1 + 1 < 2 * m1.1 + 2 by omega),
          hc_lt _ _ (show 2 * m1.1 + 2 < 2 * m2.1 + 1 by have : m1.1 < m2.1 := h12; omega)⟩
      have htri_pos : ∀ m1 m2 m3 : Fin 5, m1 < m2 → m2 < m3 → 0 < orient (f m1) (f m2) (f m3) := by
        intro m1 m2 m3 h12 h23
        obtain ⟨s, hs1, hs2⟩ := hq_between_corner m1 m2 h12
        have h13 : qIdx m1 < qIdx m3 := (hq_mono m1 m2 h12).trans (hq_mono m2 m3 h23)
        have hsam := hsame_sub (qIdx m1) (qIdx m3) (hc_bounds _).1.le h13 (hc_bounds _).2.le
        exact C.same_half_orient_pos_of_corner hfront hz (hq_mono m1 m2 h12) (hq_mono m2 m3 h23) hsam
          hs1 (hs2.trans (hq_mono m2 m3 h23)) (hc_spec s).2.2.choose_spec
      have hf_edges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j) := by
        intro i j hji hji1
        fin_cases i <;> fin_cases j
        all_goals try exact absurd rfl hji
        all_goals try exact absurd rfl hji1
        all_goals first
          | exact htri_pos _ _ _ (by decide) (by decide)
          | (rw [orient_cycle]; exact htri_pos _ _ _ (by decide) (by decide))
          | (rw [← orient_cycle]; exact htri_pos _ _ _ (by decide) (by decide))
      -- Every vertex of f has orient (u (aIdx t)) (u (bIdx t)) (f m) < 0!
      have hf_outer : ∀ m : Fin 5, orient (C.u (aIdx t)) (C.u (bIdx t)) (f m) < 0 := by
        intro m
        rw [orient_swap]
        have hpos := C.same_half_orient_pos_of_corner hfront hz
          (hc_bounds ⟨2 * m.1 + 1, by have := m.isLt; omega⟩).1
          (hc_bounds ⟨2 * m.1 + 1, by have := m.isLt; omega⟩).2 hsame
          (hc_bounds 0).1 (hc_bounds 0).2 (hc_spec 0).2.2.choose_spec
        linarith
      -- Show convexHull ℝ (Set.range f) ∩ A = Set.range f!
      have hf_A_empty : ∀ x ∈ A, x ∈ convexHull ℝ (Set.range f) → x ∈ Set.range f := by
        intro x hx hxhull
        obtain ⟨r, rfl⟩ := C.hsurj x hx
        by_contra hnot
        have hr_ne : ∀ m : Fin 5, r ≠ qIdx m := fun m h => hnot ⟨m, by rw [h]⟩
        -- Since every q ∈ range f has orient (u (aIdx t)) (u (bIdx t)) q < 0, so does u r!
        have hr_out : orient (C.u (aIdx t)) (C.u (bIdx t)) (C.u r) < 0 :=
          convexHull_orient_lt (by rintro _ ⟨m, rfl⟩; exact hf_outer m) _ hxhull
        -- Therefore r lies strictly in (aIdx t, bIdx t)!
        have hr_wedge : 0 < det2 (C.u (aIdx t) - z) (C.u r - z) ∧ 0 < det2 (C.u r - z) (C.u (bIdx t) - z) := by
          by_contra hnotW
          have hge := C.chord_outside_nonneg hfront hz (C.hmem _) (C.hmem _) hab_det (C.hmem r) hnotW
          linarith
        have hr_in_ab : aIdx t < r ∧ r < bIdx t := by
          rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
            (sub_ne_zero.mpr (C.hne r)) hab_det, if_pos hsame] at hr_wedge
          constructor
          · by_contra hle
            rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
            · exact angleLt_irrefl _ hr_wedge.1
            · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hr_wedge.1 (C.hmono _ _ hlt))
          · by_contra hle
            rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
            · exact angleLt_irrefl _ hr_wedge.2
            · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hr_wedge.2 (C.hmono _ _ hlt))
        -- Either r < qIdx 0, or r > qIdx 4, or qIdx m < r < qIdx (m + 1) for some m < 4!
        have hbad_edge : ∃ i : Fin 5, orient (f i) (f (i + 1)) (C.u r) < 0 := by
          by_cases h0 : r < qIdx 0
          · refine ⟨4, ?_⟩
            change orient (C.u (qIdx 4)) (C.u (qIdx 0)) (C.u r) < 0
            rw [orient_cycle, orient_swap]
            have hsam := hsame_sub r (qIdx 4) hr_in_ab.1.le (h0.trans (hq_mono 0 4 (by decide))) (hc_bounds _).2.le
            have hpos := C.same_half_orient_pos_of_corner hfront hz h0 (hq_mono 0 4 (by decide)) hsam
              (h0.trans (hc_lt 1 2 (by decide))) (hc_lt 2 9 (by decide)) (hc_spec 2).2.2.choose_spec
            linarith
          · by_cases h4 : qIdx 4 < r
            · refine ⟨4, ?_⟩
              change orient (C.u (qIdx 4)) (C.u (qIdx 0)) (C.u r) < 0
              rw [← orient_cycle, orient_swap]
              have hsam := hsame_sub (qIdx 0) r (hc_bounds _).1.le ((hq_mono 0 4 (by decide)).trans h4) hr_in_ab.2.le
              have hpos := C.same_half_orient_pos_of_corner hfront hz (hq_mono 0 4 (by decide)) h4 hsam
                (hc_lt 1 2 (by decide)) ((hc_lt 2 9 (by decide)).trans h4) (hc_spec 2).2.2.choose_spec
              linarith
            · -- qIdx 0 < r < qIdx 4: pick maximal m with qIdx m < r!
              have h0' : qIdx 0 < r := lt_of_le_of_ne (not_lt.mp h0) (hr_ne 0).symm
              have h4' : r < qIdx 4 := lt_of_le_of_ne (not_lt.mp h4) (hr_ne 4)
              have hex_m : ∃ m : Fin 5, m.1 < 4 ∧ qIdx m < r ∧ r < qIdx (m + 1) := by
                by_cases h1 : r < qIdx 1
                · exact ⟨0, by decide, h0', h1⟩
                · by_cases h2 : r < qIdx 2
                  · exact ⟨1, by decide, lt_of_le_of_ne (not_lt.mp h1) (hr_ne 1).symm, h2⟩
                  · by_cases h3 : r < qIdx 3
                    · exact ⟨2, by decide, lt_of_le_of_ne (not_lt.mp h2) (hr_ne 2).symm, h3⟩
                    · exact ⟨3, by decide, lt_of_le_of_ne (not_lt.mp h3) (hr_ne 3).symm, h4'⟩
              obtain ⟨m, hm4, hmr1, hmr2⟩ := hex_m
              refine ⟨m, ?_⟩
              have h12 : m < m + 1 := by
                show m.1 < (m + 1).1
                have : (m + 1).1 = m.1 + 1 := by
                  fin_cases m <;> first | rfl | exact absurd hm4 (by decide)
                omega
              obtain ⟨s, hs1, hs2⟩ := hq_between_corner m (m + 1) h12
              have hsam := hsame_sub (qIdx m) (qIdx (m + 1)) (hc_bounds _).1.le
                (hmr1.trans hmr2) (hc_bounds _).2.le
              have hpos := C.same_half_orient_pos_of_corner hfront hz hmr1 hmr2 hsam hs1 hs2 (hc_spec s).2.2.choose_spec
              change orient (C.u (qIdx m)) (C.u (qIdx (m + 1))) (C.u r) < 0
              rw [orient_swap]; linarith
        obtain ⟨i, hi_neg⟩ := hbad_edge
        have hge : 0 ≤ orient (f i) (f (i + 1)) (C.u r) := by
          apply convexHull_orient_ge _ _ hxhull
          rintro _ ⟨j, rfl⟩
          by_cases h1 : j = i
          · subst h1; rw [orient_self_mid]
          · by_cases h2 : j = i + 1
            · subst h2; rw [orient_self_right]
            · exact (hf_edges i j h1 h2).le
        linarith
      -- Since ¬ HasEmptyPentagon P, ∃ w ∈ P \ range f inside convexHull ℝ (range f)!
      have hex_w : ∃ w ∈ I, orient (C.u (aIdx t)) (C.u (bIdx t)) w < 0 := by
        by_contra hnone
        push Not at hnone
        apply hnopent
        apply hasEmptyPentagon_of_cyclic5 f (fun m => hAP (C.hmem _)) hf_edges
        intro w hw hwhull
        have hw_A : w ∈ convexHull ℝ (A : Set Pt) :=
          convexHull_mono (by rintro _ ⟨m, rfl⟩; exact C.hmem _) hwhull
        by_cases hwf : w ∈ frontier (convexHull ℝ (A : Set Pt))
        · exact hf_A_empty w (by rw [hA_full]; exact Finset.mem_filter.mpr ⟨hw, hwf⟩) hwhull
        · have hwi : w ∈ I := Finset.mem_filter.mpr ⟨hw, by
            rw [frontier_convexHull_finset, Set.mem_sdiff, not_and_or, not_not] at hwf
            exact hwf.resolve_left (not_not.mpr hw_A)⟩
          have hge := hnone w hwi
          have hlt := convexHull_orient_lt (by rintro _ ⟨m, rfl⟩; exact hf_outer m) w hwhull
          linarith
      obtain ⟨w0, hw0_I, hw0_lt⟩ := hex_w
      have hI_ne : I.Nonempty := ⟨w0, hw0_I⟩
      obtain ⟨p, hp_I, hp_min⟩ := Finset.exists_min_image I (fun q => orient (C.u (aIdx t)) (C.u (bIdx t)) q) hI_ne
      have hp_lt : orient (C.u (aIdx t)) (C.u (bIdx t)) p < 0 := lt_of_le_of_lt (hp_min w0 hw0_I) hw0_lt
      have hab_ne : C.u (aIdx t) ≠ C.u (bIdx t) := fun h => by
        rw [h, det2_self] at hab_det; linarith
      have hp_A' : p ∈ A' := Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp_I).1, mem_frontier_of_min_orient hp_I hab_ne hp_min⟩
      -- Show p lies strictly in open wedge W z (u (aIdx t)) (u (bIdx t))!
      have hp_wedge : 0 < det2 (C.u (aIdx t) - z) (p - z) ∧ 0 < det2 (p - z) (C.u (bIdx t) - z) := by
        -- Every q ∈ A \ W has orient (u (aIdx t)) (u (bIdx t)) q ≥ 0!
        -- Wait: we only need p ∈ convexHull ℝ A and orient (u (aIdx t)) (u (bIdx t)) p < 0!
        -- Express p in terms of u (aIdx t), u (bIdx t): show EVERY q ∈ A with orient < 0 lies in W!
        -- Actually, ANY w ∈ convexHull ℝ A with orient (u a) (u b) w < 0 lies in W!
        -- Because ALL vertices of A outside W have orient (u a) (u b) ≥ 0, wait: what about
        -- det2 (u a - z) (w - z) > 0? Let's check:
        -- Define the convex set K := {w | orient (u a) (u b) w ≥ 0 ∨ (det2(u a - z, w - z) > 0 ∧ det2(w - z, u b - z) > 0)}!
        -- Wait: is the intersection of {orient (u a) (u b) < 0} with conv(A) inside W?!
        -- CHECK: For EVERY v ∈ A:
        --   - If v ∈ W: then det2 (u a - z) (v - z) > 0 AND det2 (v - z) (u b - z) > 0!
        --   - Wait: could v ∉ W have det2 (u a - z) (v - z) < 0? YES, e.g. on the OTHER side of z!
        --   - So instead, look at the supporting line of conv(A) at u (aIdx t) — NO, EVEN SIMPLER!!
        --   Every point in conv(A) is a convex combination of A; even simpler, use C.exists_arc_cover on p!
        --   Wait: if p ∉ W, then the ray z → p hits ∂conv(A) at a point q on some arc u_r → u_{r+1}
        --   with r outside [aIdx t, bIdx t - 1]!
        --   At u_r and u_{r+1}, BOTH have orient (u a) (u b) ≥ 0 (by chord_outside_nonneg)!
        --   And z has orient (u a) (u b) z > 0!
        --   So EVERYTHING in triangle[z, u_r, u_{r+1}] has orient (u a) (u b) ≥ 0!!
        --   Since p ∈ conv(A) and p is on ray z → q, p ∈ triangle[z, u_r, u_{r+1}], so orient ≥ 0! CONTRADICTION!!
        have hp_ne_z : p ≠ z := fun h => by
          rw [h] at hp_lt
          have : orient (C.u (aIdx t)) (C.u (bIdx t)) z = det2 (C.u (aIdx t) - z) (C.u (bIdx t) - z) := by
            simp [orient, det2]; ring
          linarith
        have hp_convA : p ∈ convexHull ℝ (A : Set Pt) := interior_subset (Finset.mem_filter.mp hp_I).2
        by_contra hnotW
        rcases C.exists_arc_cover hz hp_ne_z with ⟨r, s, hs, hray⟩ | ⟨r, hr1, hr2⟩
        · -- p - z = s • (u r - z) with s > 0! Since p ∈ int(conv A), s < 1!
          have hs_lt1 : s < 1 := by
            by_contra hge
            have hs1 : 1 ≤ s := not_lt.mp hge
            have hp_inA := (Finset.mem_filter.mp hp_I).2
            rcases eq_or_lt_of_le hs1 with rfl | hgt
            · have hpeq : p = C.u r := by ext <;> (have := congrArg Prod.fst hray; have := congrArg Prod.snd hray; simp at *; linarith)
              rw [hpeq] at hp_inA
              exact (frontier_convexHull_finset A ▸ hfront (C.hmem r)).2 hp_inA
            · have hur_eq : C.u r = (1 - s⁻¹) • z + s⁻¹ • p := by
                ext
                · have hx := congrArg Prod.fst hray; simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at hx
                  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp [hs.ne']; linarith
                · have hy := congrArg Prod.snd hray; simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at hy
                  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp [hs.ne']; linarith
              have hur_int := convex_comb_mem_interior (convex_convexHull ℝ _) hz (interior_subset hp_inA)
                (inv_pos.mpr hs) (inv_lt_one_of_one_lt₀ hgt)
              rw [← hur_eq] at hur_int
              exact (frontier_convexHull_finset A ▸ hfront (C.hmem r)).2 hur_int
          have hr_notW : ¬ (0 < det2 (C.u (aIdx t) - z) (C.u r - z) ∧ 0 < det2 (C.u r - z) (C.u (bIdx t) - z)) := by
            rintro ⟨h1, h2⟩
            apply hnotW
            rw [hray]
            have e1 : det2 (C.u (aIdx t) - z) (s • (C.u r - z)) = s * det2 (C.u (aIdx t) - z) (C.u r - z) := by
              simp [det2]; ring
            have e2 : det2 (s • (C.u r - z)) (C.u (bIdx t) - z) = s * det2 (C.u r - z) (C.u (bIdx t) - z) := by
              simp [det2]; ring
            exact ⟨by rw [e1]; exact mul_pos hs h1, by rw [e2]; exact mul_pos hs h2⟩
          have hr_ge := C.chord_outside_nonneg hfront hz (C.hmem _) (C.hmem _) hab_det (C.hmem r) hr_notW
          have hz_ge : 0 ≤ orient (C.u (aIdx t)) (C.u (bIdx t)) z := by
            have : orient (C.u (aIdx t)) (C.u (bIdx t)) z = det2 (C.u (aIdx t) - z) (C.u (bIdx t) - z) := by
              simp [orient, det2]; ring
            linarith
          have hp_eq : p = (1 - s) • z + s • C.u r := by
            ext
            · have := congrArg Prod.fst hray; simp at this ⊢; linarith
            · have := congrArg Prod.snd hray; simp at this ⊢; linarith
          rw [hp_eq, orient_aff_comb] at hp_lt
          nlinarith
        · -- p lies in open wedge of arc r → next r!
          have hp_tri : p ∈ convexHull ℝ ({z, C.u r, C.u (cycNext C.hn0 r)} : Set Pt) := by
            apply mem_convexHull_triangle_of_orient
            · have : orient z (C.u r) (C.u (cycNext C.hn0 r)) =
                  det2 (C.u r - z) (C.u (cycNext C.hn0 r) - z) := by simp [orient, det2]
              linarith [C.det_arc_pos hz r]
            · exact C.arc_supporting hfront hz r p hp_convA
            · have : orient (C.u (cycNext C.hn0 r)) z p = det2 (p - z) (C.u (cycNext C.hn0 r) - z) := by
                simp [orient, det2]; ring
              linarith
            · have : orient z (C.u r) p = det2 (C.u r - z) (p - z) := by simp [orient, det2]
              linarith
          -- Show BOTH u r and u (next r) lie outside W z (u (aIdx t)) (u (bIdx t))!
          have hr_out1 : ¬ (0 < det2 (C.u (aIdx t) - z) (C.u r - z) ∧ 0 < det2 (C.u r - z) (C.u (bIdx t) - z)) := by
            intro hrW
            rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
              (sub_ne_zero.mpr (C.hne r)) hab_det, if_pos hsame] at hrW
            have hra : aIdx t < r := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
              · exact angleLt_irrefl _ hrW.1
              · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                  (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hrW.1 (C.hmono _ _ hlt))
            have hrb : r < bIdx t := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
              · exact angleLt_irrefl _ hrW.2
              · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                  (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hrW.2 (C.hmono _ _ hlt))
            have hrlt : r.1 + 1 < C.n := by have := (bIdx t).isLt; have : r.1 < (bIdx t).1 := hrb; omega
            have hnext_le : cycNext C.hn0 r ≤ bIdx t := by
              show (cycNext C.hn0 r).1 ≤ (bIdx t).1; rw [cycNext_val_of_lt C.hn0 hrlt]; exact hrb
            have hp_w := (C.arc_wedge_iff hz r hp_ne_z).mp ⟨hr1, hr2⟩
            rw [if_pos hrlt] at hp_w
            apply hnotW
            rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
              (sub_ne_zero.mpr hp_ne_z) hab_det, if_pos hsame]
            refine ⟨angleLt_trans (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne r))
              (sub_ne_zero.mpr hp_ne_z) hrW.1 hp_w.1, ?_⟩
            rcases eq_or_lt_of_le hnext_le with hEq | hlt'
            · rw [← hEq]; exact hp_w.2
            · exact angleLt_trans (sub_ne_zero.mpr hp_ne_z) (sub_ne_zero.mpr (C.hne _))
                (sub_ne_zero.mpr (C.hne _)) hp_w.2 (C.hmono _ _ hlt')
          have hr_out2 : ¬ (0 < det2 (C.u (aIdx t) - z) (C.u (cycNext C.hn0 r) - z) ∧
              0 < det2 (C.u (cycNext C.hn0 r) - z) (C.u (bIdx t) - z)) := by
            intro hrW
            rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
              (sub_ne_zero.mpr (C.hne _)) hab_det, if_pos hsame] at hrW
            have hra : aIdx t < cycNext C.hn0 r := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with hEq | hlt
              · rw [hEq] at hrW; exact angleLt_irrefl _ hrW.1
              · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                  (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hrW.1 (C.hmono _ _ hlt))
            have hrb : cycNext C.hn0 r < bIdx t := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with hEq | hlt
              · rw [hEq] at hrW; exact angleLt_irrefl _ hrW.2
              · exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr (C.hne _))
                  (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _)) hrW.2 (C.hmono _ _ hlt))
            have hrlt : r.1 + 1 < C.n := by
              by_contra hge
              have h0 : cycNext C.hn0 r = ⟨0, C.hn0⟩ := cycNext_eq_zero_of_not_lt C.hn0 hge
              have : (aIdx t).1 < (cycNext C.hn0 r).1 := hra
              rw [h0] at this; dsimp only at this; omega
            have ha_le : aIdx t ≤ r := by
              show (aIdx t).1 ≤ r.1
              have : (aIdx t).1 < (cycNext C.hn0 r).1 := hra
              rw [cycNext_val_of_lt C.hn0 hrlt] at this; omega
            have hp_w := (C.arc_wedge_iff hz r hp_ne_z).mp ⟨hr1, hr2⟩
            rw [if_pos hrlt] at hp_w
            apply hnotW
            rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
              (sub_ne_zero.mpr hp_ne_z) hab_det, if_pos hsame]
            refine ⟨?_, angleLt_trans (sub_ne_zero.mpr hp_ne_z) (sub_ne_zero.mpr (C.hne _))
              (sub_ne_zero.mpr (C.hne _)) hp_w.2 hrW.2⟩
            rcases eq_or_lt_of_le ha_le with rfl | hlt'
            · exact hp_w.1
            · exact angleLt_trans (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne r))
                (sub_ne_zero.mpr hp_ne_z) (C.hmono _ _ hlt') hp_w.1
          have hge_all : 0 ≤ orient (C.u (aIdx t)) (C.u (bIdx t)) p := by
            apply convexHull_orient_ge _ p hp_tri
            rintro q (hq | hq | hq)
            · rw [hq]
              have : orient (C.u (aIdx t)) (C.u (bIdx t)) z = det2 (C.u (aIdx t) - z) (C.u (bIdx t) - z) := by
                simp [orient, det2]; ring
              linarith
            · rw [hq]; exact C.chord_outside_nonneg hfront hz (C.hmem _) (C.hmem _) hab_det (C.hmem r) hr_out1
            · rw [hq]; exact C.chord_outside_nonneg hfront hz (C.hmem _) (C.hmem _) hab_det (C.hmem _) hr_out2
          linarith
      exact ⟨p, hp_A', hp_wedge⟩
    -- Map t ∈ T to its chosen point in A'; wedges are pairwise disjoint, so map is injective!
    let φ : Fin (A'.card + 2) → Pt := fun t => if ht : t ∈ T then (hex_pt t ht).choose else 0
    have hφ_mem : ∀ t ∈ T, φ t ∈ A' := fun t ht => by
      simp only [φ, dif_pos ht]; exact (hex_pt t ht).choose_spec.1
    have hφ_inj : Set.InjOn φ (T : Set (Fin (A'.card + 2))) := by
      intro t1 ht1 t2 ht2 heq
      by_contra hne
      have ht1' : t1 ∈ T := ht1
      have ht2' : t2 ∈ T := ht2
      have h1 := (hex_pt t1 ht1').choose_spec.2
      have h2 := (hex_pt t2 ht2').choose_spec.2
      have hpeq : (hex_pt t1 ht1').choose = (hex_pt t2 ht2').choose := by
        simpa [φ, dif_pos ht1', dif_pos ht2'] using heq
      rw [hpeq] at h1
      set p := (hex_pt t2 ht2').choose
      have hpz : p ≠ z := fun h => by rw [h, sub_self] at h2; simp [det2] at h2
      have hsam1 := hTgood t1 ht1'
      have hsam2 := hTgood t2 ht2'
      have hd1 : 0 < det2 (C.u (aIdx t1) - z) (C.u (bIdx t1) - z) := by
        rcases C.hmono (aIdx t1) (bIdx t1) (by show t1.1 * B < t1.1 * B + B - 1; omega) with ⟨x1, x2⟩ | ⟨-, d⟩
        · rw [hsam1, x2] at x1; cases x1
        · exact d
      have hd2 : 0 < det2 (C.u (aIdx t2) - z) (C.u (bIdx t2) - z) := by
        rcases C.hmono (aIdx t2) (bIdx t2) (by show t2.1 * B < t2.1 * B + B - 1; omega) with ⟨x1, x2⟩ | ⟨-, d⟩
        · rw [hsam2, x2] at x1; cases x1
        · exact d
      rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
        (sub_ne_zero.mpr hpz) hd1, if_pos hsam1] at h1
      rw [det2_pos_of_angleLt_between (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr (C.hne _))
        (sub_ne_zero.mpr hpz) hd2, if_pos hsam2] at h2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hba : bIdx t1 < aIdx t2 := by
          show t1.1 * B + B - 1 < t2.1 * B
          have h1' : (t1.1 + 1) * B ≤ t2.1 * B := Nat.mul_le_mul_right B hlt
          have h2' : (t1.1 + 1) * B = t1.1 * B + B := by ring
          omega
        exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr hpz) (sub_ne_zero.mpr (C.hne _))
          (sub_ne_zero.mpr hpz) h1.2 (angleLt_trans (sub_ne_zero.mpr (C.hne _))
            (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr hpz) (C.hmono _ _ hba) h2.1))
      · have hba : bIdx t2 < aIdx t1 := by
          show t2.1 * B + B - 1 < t1.1 * B
          have h1' : (t2.1 + 1) * B ≤ t1.1 * B := Nat.mul_le_mul_right B hgt
          have h2' : (t2.1 + 1) * B = t2.1 * B + B := by ring
          omega
        exact angleLt_irrefl _ (angleLt_trans (sub_ne_zero.mpr hpz) (sub_ne_zero.mpr (C.hne _))
          (sub_ne_zero.mpr hpz) h2.2 (angleLt_trans (sub_ne_zero.mpr (C.hne _))
            (sub_ne_zero.mpr (C.hne _)) (sub_ne_zero.mpr hpz) (C.hmono _ _ hba) h1.1))
    have hcard_le : T.card ≤ A'.card := by
      rw [← Finset.card_image_of_injOn hφ_inj]
      exact Finset.card_le_card (Finset.image_subset_iff.mpr hφ_mem)
    omega

/- ### Part 6: Followers, Claim B (4-hole + empty follower), Claim C (alignment), and final 5-hole -/

private structure FollowerData (P : Finset Pt) (z : Pt) (A₁ A₂ : Finset Pt)
    (x y p q : Pt) : Prop where
  hx : x ∈ A₁
  hy : y ∈ A₁
  hp : p ∈ A₂
  hq : q ∈ A₂
  hA₁P : A₁ ⊆ P
  hA₂P : A₂ ⊆ P
  hA₁_front : (A₁ : Set Pt) ⊆ frontier (convexHull ℝ (A₁ : Set Pt))
  hA₂_full : A₂ = P.filter fun w => w ∈ frontier (convexHull ℝ (A₂ : Set Pt))
  hA₂_in_int : (A₂ : Set Pt) ⊆ interior (convexHull ℝ (A₁ : Set Pt))
  hP_split : ∀ w ∈ P, w ∈ convexHull ℝ (A₁ : Set Pt) → w ∈ A₁ ∨ w ∈ convexHull ℝ (A₂ : Set Pt)
  hxy_det : 0 < det2 (x - z) (y - z)
  hpq_det : 0 < det2 (p - z) (q - z)
  hxy_sup : ∀ w ∈ convexHull ℝ (A₁ : Set Pt), 0 ≤ orient x y w
  hpq_sup : ∀ w ∈ convexHull ℝ (A₂ : Set Pt), 0 ≤ orient p q w
  hxy_seg : ∀ w ∈ A₁, w ∈ convexHull ℝ ({x, y} : Set Pt) → w = x ∨ w = y
  hpq_seg : ∀ w ∈ A₂, w ∈ convexHull ℝ ({p, q} : Set Pt) → w = p ∨ w = q
  hxp_nonneg : 0 ≤ det2 (p - z) (x - z)
  hxq_nonneg : 0 ≤ det2 (x - z) (q - z)
  hyp_nonneg : 0 ≤ det2 (p - z) (y - z)
  hyq_nonneg : 0 ≤ det2 (y - z) (q - z)
  hpq_x_neg : orient p q x < 0
  hpq_y_neg : orient p q y < 0
  hxy_p_pos : 0 < orient x y p
  hxy_q_pos : 0 < orient x y q

private lemma convexHull_quad_subset_seg_union_int {K : Set Pt} (hK : Convex ℝ K)
    {x y p q : Pt} (hx : x ∈ K) (hy : y ∈ K) (hp : p ∈ interior K) (hq : q ∈ interior K) :
    convexHull ℝ ({x, y, q, p} : Set Pt) ⊆ convexHull ℝ ({x, y} : Set Pt) ∪ interior K := by
  have hconv : Convex ℝ (convexHull ℝ ({x, y} : Set Pt) ∪ interior K) := by
    intro a ha b hb α β hα hβ hsum
    by_cases hα0 : α = 0
    · rw [hα0, show β = 1 by linarith]; simpa using hb
    · by_cases hβ0 : β = 0
      · rw [hβ0, show α = 1 by linarith]; simpa using ha
      · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
        have hsegK : convexHull ℝ ({x, y} : Set Pt) ⊆ K :=
          convexHull_min (by rintro u (rfl | rfl) <;> assumption) hK
        rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
        · exact Or.inl ((convex_convexHull ℝ _) ha1 hb1 hα hβ hsum)
        · right
          have hcomb : α • a + β • b = (1 - α) • b + α • a := by
            rw [show 1 - α = β by linarith, add_comm]
          rw [hcomb]
          exact convex_comb_mem_interior hK hb2 (hsegK ha1) hαp (by linarith)
        · right
          have hcomb : α • a + β • b = (1 - β) • a + β • b := by
            rw [show 1 - β = α by linarith]
          rw [hcomb]
          exact convex_comb_mem_interior hK ha2 (hsegK hb1) hβp (by linarith)
        · right
          have hcomb : α • a + β • b = (1 - β) • a + β • b := by
            rw [show 1 - β = α by linarith]
          rw [hcomb]
          exact convex_comb_mem_interior hK ha2 (interior_subset hb2) hβp (by linarith)
  refine convexHull_min ?_ hconv
  rintro u (rfl | rfl | rfl | rfl)
  · exact Or.inl (subset_convexHull ℝ _ (by simp))
  · exact Or.inl (subset_convexHull ℝ _ (by simp))
  · exact Or.inr hq
  · exact Or.inr hp

private lemma convexHull_quad_subset_seg_union_neg {x y p q : Pt}
    (hx : orient p q x < 0) (hy : orient p q y < 0) :
    convexHull ℝ ({x, y, q, p} : Set Pt) ⊆
      convexHull ℝ ({p, q} : Set Pt) ∪ {w : Pt | orient p q w < 0} := by
  have hseg0 : ∀ w ∈ convexHull ℝ ({p, q} : Set Pt), orient p q w ≤ 0 :=
    convexHull_orient_le (by
      rintro u (rfl | rfl)
      · exact (orient_self_mid _ _).le
      · exact (orient_self_right _ _).le)
  have hconv : Convex ℝ (convexHull ℝ ({p, q} : Set Pt) ∪ {w : Pt | orient p q w < 0}) := by
    intro a ha b hb α β hα hβ hsum
    by_cases hα0 : α = 0
    · rw [hα0, show β = 1 by linarith]; simpa using hb
    · by_cases hβ0 : β = 0
      · rw [hβ0, show α = 1 by linarith]; simpa using ha
      · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
        have hor : orient p q (α • a + β • b) = α * orient p q a + β * orient p q b := by
          rw [show α = 1 - β by linarith, orient_aff_comb]
        rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
        · exact Or.inl ((convex_convexHull ℝ _) ha1 hb1 hα hβ hsum)
        · right; change orient p q (α • a + β • b) < 0; rw [hor]
          have := hseg0 a ha1; change orient p q b < 0 at hb2; nlinarith
        · right; change orient p q (α • a + β • b) < 0; rw [hor]
          have := hseg0 b hb1; change orient p q a < 0 at ha2; nlinarith
        · right; change orient p q (α • a + β • b) < 0; rw [hor]
          change orient p q a < 0 at ha2; change orient p q b < 0 at hb2; nlinarith
  refine convexHull_min ?_ hconv
  rintro u (rfl | rfl | rfl | rfl)
  · exact Or.inr hx
  · exact Or.inr hy
  · exact Or.inl (subset_convexHull ℝ _ (by simp))
  · exact Or.inl (subset_convexHull ℝ _ (by simp))

private lemma follower_four_hole_empty {P : Finset Pt} {z : Pt} {A₁ A₂ : Finset Pt} {x y p q : Pt}
    (F : FollowerData P z A₁ A₂ x y p q) :
    ∀ w ∈ P, w ∈ convexHull ℝ ({x, y, q, p} : Set Pt) → w ∈ ({x, y, q, p} : Set Pt) := by
  intro w hw hwhull
  have hwA₁ : w ∈ convexHull ℝ (A₁ : Set Pt) := by
    refine convexHull_min ?_ (convex_convexHull ℝ (A₁ : Set Pt)) hwhull
    rintro u (rfl | rfl | rfl | rfl)
    · exact subset_convexHull ℝ _ F.hx
    · exact subset_convexHull ℝ _ F.hy
    · exact interior_subset (F.hA₂_in_int F.hq)
    · exact interior_subset (F.hA₂_in_int F.hp)
  rcases F.hP_split w hw hwA₁ with hw1 | hw2
  · have hsub := convexHull_quad_subset_seg_union_int (convex_convexHull ℝ (A₁ : Set Pt))
      (subset_convexHull ℝ _ F.hx) (subset_convexHull ℝ _ F.hy)
      (F.hA₂_in_int F.hp) (F.hA₂_in_int F.hq) hwhull
    rcases hsub with hseg | hint
    · rcases F.hxy_seg w hw1 hseg with rfl | rfl <;> simp
    · exact absurd hint (frontier_convexHull_finset A₁ ▸ F.hA₁_front hw1).2
  · have hsub := convexHull_quad_subset_seg_union_neg F.hpq_x_neg F.hpq_y_neg hwhull
    have hw_ge : 0 ≤ orient p q w := F.hpq_sup w hw2
    rcases hsub with hseg | hneg
    · have hpq_ne : p ≠ q := fun h => by have := F.hpq_det; rw [h, det2_self] at this; linarith
      have hw_not_int : w ∉ interior (convexHull ℝ (A₂ : Set Pt)) := fun hint => by
        have hpos := orient_pos_of_mem_interior (fun u hu => F.hpq_sup u (subset_convexHull ℝ _ hu)) hpq_ne hint
        have hle : orient p q w ≤ 0 := convexHull_orient_le (by
          rintro u (rfl | rfl)
          · exact (orient_self_mid _ _).le
          · exact (orient_self_right _ _).le) w hseg
        linarith
      have hwA₂ : w ∈ A₂ := by
        rw [F.hA₂_full]
        exact Finset.mem_filter.mpr ⟨hw, by rw [frontier_convexHull_finset]; exact ⟨hw2, hw_not_int⟩⟩
      rcases F.hpq_seg w hwA₂ hseg with rfl | rfl <;> simp
    · change orient p q w < 0 at hneg; linarith

private lemma orient_in_basis (z p q a b c : Pt) (hD : det2 (p - z) (q - z) ≠ 0) :
    let D := det2 (p - z) (q - z)
    let α := fun w : Pt => det2 (w - z) (q - z) / D
    let β := fun w : Pt => det2 (p - z) (w - z) / D
    orient a b c = D * ((α b - α a) * (β c - β a) - (β b - β a) * (α c - α a)) := by
  intro D α β
  have hrep : ∀ w : Pt, w - z = α w • (p - z) + β w • (q - z) := fun w => by
    have hcr := det2_cramer (p - z) (q - z) (w - z)
    ext
    · have hx := congrArg Prod.fst hcr; simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx ⊢
      simp only [α, β, D]; field_simp [hD]; linarith
    · have hy := congrArg Prod.snd hcr; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy ⊢
      simp only [α, β, D]; field_simp [hD]; linarith
  have hba : b - a = (α b - α a) • (p - z) + (β b - β a) • (q - z) := by
    have hb := hrep b; have ha := hrep a
    ext
    · have h1 := congrArg Prod.fst hb; have h2 := congrArg Prod.fst ha
      simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2 ⊢; linarith
    · have h1 := congrArg Prod.snd hb; have h2 := congrArg Prod.snd ha
      simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢; linarith
  have hca : c - a = (α c - α a) • (p - z) + (β c - β a) • (q - z) := by
    have hc := hrep c; have ha := hrep a
    ext
    · have h1 := congrArg Prod.fst hc; have h2 := congrArg Prod.fst ha
      simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2 ⊢; linarith
    · have h1 := congrArg Prod.snd hc; have h2 := congrArg Prod.snd ha
      simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢; linarith
  change det2 (b - a) (c - a) = _
  rw [hba, hca]
  simp only [det2, D, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private lemma five_hole_of_follower_point {P : Finset Pt} {z : Pt} {A₁ A₂ : Finset Pt} {x y p q r : Pt}
    (F : FollowerData P z A₁ A₂ x y p q) (hrP : r ∈ P)
    (hr_pq : 0 < orient p q r)
    (hr_p : 0 ≤ det2 (p - z) (r - z)) (hr_q : 0 ≤ det2 (r - z) (q - z))
    (hstrict_left : 0 < det2 (p - z) (x - z) ∨ 0 < det2 (p - z) (r - z))
    (hstrict_right : 0 < det2 (y - z) (q - z) ∨ 0 < det2 (r - z) (q - z))
    (hr_min : ∀ w ∈ P, w ∈ convexHull ℝ ({p, q, r} : Set Pt) → 0 < orient p q w → orient p q r ≤ orient p q w) :
    HasEmptyPentagon P := by
  set D := det2 (p - z) (q - z)
  have hD : 0 < D := F.hpq_det
  let α : Pt → ℝ := fun w => det2 (w - z) (q - z) / D
  let β : Pt → ℝ := fun w => det2 (p - z) (w - z) / D
  have hαp : α p = 1 := by simp only [α, D]; exact div_self hD.ne'
  have hβp : β p = 0 := by simp [β, det2_self]
  have hαq : α q = 0 := by simp [α, det2_self]
  have hβq : β q = 1 := by simp only [β, D]; exact div_self hD.ne'
  have hor : ∀ a b c : Pt, orient a b c = D * ((α b - α a) * (β c - β a) - (β b - β a) * (α c - α a)) :=
    fun a b c => orient_in_basis z p q a b c hD.ne'
  have hαx_nn : 0 ≤ α x := div_nonneg F.hxq_nonneg hD.le
  have hβx_nn : 0 ≤ β x := div_nonneg F.hxp_nonneg hD.le
  have hαy_nn : 0 ≤ α y := div_nonneg F.hyq_nonneg hD.le
  have hβy_nn : 0 ≤ β y := div_nonneg F.hyp_nonneg hD.le
  have hαr_nn : 0 ≤ α r := div_nonneg hr_q hD.le
  have hβr_nn : 0 ≤ β r := div_nonneg hr_p hD.le
  have hxy_det_ab : 0 < α x * β y - β x * α y := by
    have h1 := hor z x y
    have hαz : α z = 0 := by simp [α, det2]
    have hβz : β z = 0 := by simp [β, det2]
    have hzxy : orient z x y = det2 (x - z) (y - z) := by simp [orient, det2]
    rw [hzxy, hαz, hβz] at h1
    nlinarith [F.hxy_det]
  have hαx_pos : 0 < α x := by nlinarith
  have hβy_pos : 0 < β y := by nlinarith
  have hx_sum : 1 < α x + β x := by
    have h1 := hor p q x; rw [hαp, hβp, hαq, hβq] at h1; nlinarith [F.hpq_x_neg]
  have hy_sum : 1 < α y + β y := by
    have h1 := hor p q y; rw [hαp, hβp, hαq, hβq] at h1; nlinarith [F.hpq_y_neg]
  have hr_sum : α r + β r < 1 := by
    have h1 := hor p q r; rw [hαp, hβp, hαq, hβq] at h1; nlinarith [hr_pq]
  have hxyp : 0 < (α x * β y - β x * α y) + β x - β y := by
    have h1 := hor x y p; rw [hαp, hβp] at h1; nlinarith [F.hxy_p_pos]
  have hxyq : 0 < (α x * β y - β x * α y) + α y - α x := by
    have h1 := hor x y q; rw [hαq, hβq] at h1; nlinarith [F.hxy_q_pos]
  have hleft : 0 < β x ∨ 0 < β r := hstrict_left.imp (fun h => div_pos h hD) (fun h => div_pos h hD)
  have hright : 0 < α y ∨ 0 < α r := hstrict_right.imp (fun h => div_pos h hD) (fun h => div_pos h hD)
  -- Order the 5 vertices counterclockwise: f = ![p, q, r, ...] wait:
  -- Check counterclockwise order of pentagon_split (f 0 → f 2 is the chord p → q!):
  -- Set f = ![q, r, p, x, y]!!
  -- Then f 0 = q, f 1 = r, f 2 = p, f 3 = x, f 4 = y!
  -- Check edges: q → r → p → x → y → q!
  -- Wait: chord f 0 → f 2 is q → p (orient q p = -orient p q), so:
  --   orient q p w ≥ 0  ↔  w ∈ {q, p, x, y} (the 4-hole!)
  --   orient q p w ≤ 0  ↔  w ∈ {q, r, p} (the triangle!)
  -- YES!! f = ![q, r, p, x, y] matches `pentagon_split` directly!
  let f : Fin 5 → Pt := tuple5 q r p x y
  have hf_mem : ∀ i : Fin 5, f i ∈ P := by
    intro i; fin_cases i
    · exact F.hA₂P F.hq
    · exact hrP
    · exact F.hA₂P F.hp
    · exact F.hA₁P F.hx
    · exact F.hA₁P F.hy
  have hf_edges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j) := by
    apply cyclic5_edges_of_10
    · rw [hor, hαq, hβq, hαp, hβp]; apply mul_pos hD; linarith
    · rw [hor, hαq, hβq]; apply mul_pos hD
      nlinarith [mul_pos (sub_pos.mpr hr_sum) hαx_pos, mul_nonneg hαr_nn (sub_pos.mpr hx_sum).le]
    · rw [hor, hαq, hβq]; apply mul_pos hD
      rcases hright with h | h <;>
        nlinarith [mul_nonneg (sub_pos.mpr hr_sum).le hαy_nn, mul_nonneg hαr_nn (sub_pos.mpr hy_sum).le]
    · rw [hor, hαq, hβq, hαp, hβp]; apply mul_pos hD; linarith
    · rw [hor, hαq, hβq, hαp, hβp]; apply mul_pos hD; linarith
    · rw [hor, hαq, hβq]; apply mul_pos hD; linarith
    · rw [hor, hαp, hβp]; apply mul_pos hD
      rcases hleft with h | h <;>
        nlinarith [mul_nonneg (sub_pos.mpr hr_sum).le hβx_nn, mul_nonneg hβr_nn (sub_pos.mpr hx_sum).le]
    · rw [hor, hαp, hβp]; apply mul_pos hD
      nlinarith [mul_pos (sub_pos.mpr hr_sum) hβy_pos, mul_nonneg hβr_nn (sub_pos.mpr hy_sum).le]
    · rw [hor]; apply mul_pos hD
      nlinarith [mul_pos (sub_pos.mpr hr_sum) hxy_det_ab, mul_nonneg hαr_nn hxyp.le, mul_nonneg hβr_nn hxyq.le]
    · rw [hor, hαp, hβp]; apply mul_pos hD; linarith
  apply hasEmptyPentagon_of_cyclic5 f hf_mem hf_edges
  intro w hw hwhull
  rcases pentagon_split hf_edges hwhull with ⟨hqp_ge, hquad⟩ | ⟨hqp_le, htri⟩
  · -- w ∈ convexHull {q, p, x, y} = convexHull {x, y, q, p}!
    have hquad' : w ∈ convexHull ℝ ({x, y, q, p} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) hquad
    rcases follower_four_hole_empty F w hw hquad' with rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
  · -- w ∈ convexHull {q, r, p}!
    have htri' : w ∈ convexHull ℝ ({p, q, r} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) htri
    have hge : 0 ≤ orient p q w := by
      have : orient p q w = -orient q p w := by rw [orient_swap_fst]
      change orient q p w ≤ 0 at hqp_le; linarith
    rcases eq_or_lt_of_le hge with h0 | hpos
    · -- orient p q w = 0: w lies in convexHull {p, q}!
      have hw_quad : w ∈ convexHull ℝ ({x, y, q, p} : Set Pt) := by
        have hD_tri : 0 < orient p q r := hr_pq
        have hqr : 0 ≤ orient q r w := convexHull_orient_ge (by
          rintro u (hu | hu | hu)
          · rw [hu, orient_cycle]; exact hD_tri.le
          · rw [hu]; exact (orient_self_mid q r).ge
          · rw [Set.mem_singleton_iff.mp hu]; exact (orient_self_right q r).ge) w htri'
        have hrp : 0 ≤ orient r p w := convexHull_orient_ge (by
          rintro u (hu | hu | hu)
          · rw [hu]; exact (orient_self_right r p).ge
          · rw [hu, ← orient_cycle]; exact hD_tri.le
          · rw [Set.mem_singleton_iff.mp hu]; exact (orient_self_mid r p).ge) w htri'
        have hcr := cramer_triangle p q r w
        rw [← h0, zero_smul, add_zero] at hcr
        have hsum_w : orient q r w + orient r p w = orient p q r := by
          have := orient_sum p q r w; linarith
        have hw_seg : w ∈ convexHull ℝ ({p, q} : Set Pt) := by
          rw [convexHull_pair]
          refine ⟨orient q r w / orient p q r, orient r p w / orient p q r,
            div_nonneg hqr hD_tri.le, div_nonneg hrp hD_tri.le,
            by rw [← add_div, hsum_w, div_self hD_tri.ne'], ?_⟩
          ext
          · have hx := congrArg Prod.fst hcr; simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx ⊢
            field_simp [hD_tri.ne']; linarith
          · have hy := congrArg Prod.snd hcr; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy ⊢
            field_simp [hD_tri.ne']; linarith
        exact convexHull_mono (by rintro u (rfl | rfl) <;> simp) hw_seg
      rcases follower_four_hole_empty F w hw hw_quad with rfl | rfl | rfl | rfl
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    · -- 0 < orient p q w: by minimality of r, orient p q r ≤ orient p q w;
      -- since w ∈ conv{p, q, r} has orient p q w ≤ orient p q r, equality holds, forcing w = r!
      have hle_min := hr_min w hw htri' hpos
      have hqr : 0 ≤ orient q r w := convexHull_orient_ge (by
        rintro u (hu | hu | hu)
        · rw [hu, orient_cycle]; exact hr_pq.le
        · rw [hu]; exact (orient_self_mid q r).ge
        · rw [Set.mem_singleton_iff.mp hu]; exact (orient_self_right q r).ge) w htri'
      have hrp : 0 ≤ orient r p w := convexHull_orient_ge (by
        rintro u (hu | hu | hu)
        · rw [hu]; exact (orient_self_right r p).ge
        · rw [hu, ← orient_cycle]; exact hr_pq.le
        · rw [Set.mem_singleton_iff.mp hu]; exact (orient_self_mid r p).ge) w htri'
      have hsum_w := orient_sum p q r w
      have hqr0 : orient q r w = 0 := by linarith
      have hrp0 : orient r p w = 0 := by linarith
      have hcr := cramer_triangle p q r w
      rw [hqr0, hrp0, zero_smul, zero_smul, zero_add, zero_add] at hcr
      have hweq : w = r := by
        have h1 : orient p q w = orient p q r := by linarith
        rw [h1] at hcr
        exact (smul_right_injective Pt hr_pq.ne' hcr).symm
      exact ⟨1, hweq.symm⟩

private lemma five_hole_of_left_transition {P : Finset Pt} {z : Pt}
    {A₀ A₁ A₂ : Finset Pt} {x₀ y₀ x₁ y₁ x₂ y₂ : Pt}
    (F₁ : FollowerData P z A₀ A₁ x₀ y₀ x₁ y₁)
    (F₂ : FollowerData P z A₁ A₂ x₁ y₁ x₂ y₂)
    (hx₁_ray : det2 (x₁ - z) (x₀ - z) = 0)
    (hy₁_not_ray : 0 < det2 (y₀ - z) (y₁ - z))
    (hy₂_ray : det2 (y₁ - z) (y₂ - z) = 0) :
    HasEmptyPentagon P := by
  set D := det2 (x₁ - z) (y₁ - z)
  have hD : 0 < D := F₁.hpq_det
  let α : Pt → ℝ := fun w => det2 (w - z) (y₁ - z) / D
  let β : Pt → ℝ := fun w => det2 (x₁ - z) (w - z) / D
  have hαx1 : α x₁ = 1 := div_self hD.ne'
  have hβx1 : β x₁ = 0 := by simp [β, det2_self]
  have hαy1 : α y₁ = 0 := by simp [α, det2_self]
  have hβy1 : β y₁ = 1 := div_self hD.ne'
  have hor : ∀ a b c : Pt, orient a b c = D * ((α b - α a) * (β c - β a) - (β b - β a) * (α c - α a)) :=
    fun a b c => orient_in_basis z x₁ y₁ a b c hD.ne'
  have hβx0 : β x₀ = 0 := by simp [β, hx₁_ray]
  have hαx0 : 1 < α x₀ := by
    have h1 := hor x₁ y₁ x₀; rw [hαx1, hβx1, hαy1, hβy1, hβx0] at h1; nlinarith [F₁.hpq_x_neg]
  have hαy0 : 0 < α y₀ := div_pos hy₁_not_ray hD
  have hβy0 : 0 < β y₀ := by
    have h1 := hor z x₀ y₀
    have hαz : α z = 0 := by simp [α, det2]
    have hβz : β z = 0 := by simp [β, det2]
    have hdet : orient z x₀ y₀ = det2 (x₀ - z) (y₀ - z) := by simp [orient, det2]
    rw [hdet, hαz, hβz, hβx0] at h1
    nlinarith [F₁.hxy_det, mul_pos hD (by linarith : 0 < α x₀)]
  have hy0_sum : 1 < α y₀ + β y₀ := by
    have h1 := hor x₁ y₁ y₀; rw [hαx1, hβx1, hαy1, hβy1] at h1; nlinarith [F₁.hpq_y_neg]
  have hxy0_y1 : 0 < α y₀ + α x₀ * β y₀ - α x₀ := by
    have h1 := hor x₀ y₀ y₁; rw [hβx0, hαy1, hβy1] at h1; nlinarith [F₁.hxy_q_pos]
  have hαy2 : α y₂ = 0 := by
    have : det2 (y₂ - z) (y₁ - z) = -det2 (y₁ - z) (y₂ - z) := by simp [det2]; ring
    simp [α, this, hy₂_ray]
  have hβy2_pos : 0 < β y₂ := by
    have h1 := hor z x₁ y₂
    have hαz : α z = 0 := by simp [α, det2]
    have hβz : β z = 0 := by simp [β, det2]
    have hdet : orient z x₁ y₂ = det2 (x₁ - z) (y₂ - z) := by simp [orient, det2]
    rw [hdet, hαz, hβz, hαx1, hβx1, hαy2] at h1
    -- det2 (x₁ - z) (y₂ - z) > 0 since x₁, y₁, y₂ has y₂ on open ray (z, y₁)!
    have hy2_ne_z : y₂ ≠ z := fun h => by
      have := F₂.hpq_det; rw [h, sub_self] at this; simp [det2] at this
    -- orient x₁ y₁ y₂ > 0 and orient y₂ x₁ ... actually F₂.hxy_q_pos : 0 < orient x₁ y₁ y₂!
    -- Wait: hor x₁ y₁ y₂ gives 1 - β y₂ > 0; what gives β y₂ > 0?
    -- Since y₂ ∈ A₂ ⊆ interior (conv A₁) and y₁ ∈ A₁, y₂ = t • (y₁ - z) + z with t > 0?
    -- Check F₂.hyp_nonneg / F₂.hpq_det! F₂ has 0 ≤ det2 (x₂ - z) (y₁ - z) and 0 < det2 (x₂ - z) (y₂ - z)!
    -- Wait: F₂.hxy_q_pos is 0 < orient x₁ y₁ y₂, AND F₂.hpq_y_neg is orient x₂ y₂ y₁ < 0!
    -- Express orient x₂ y₂ y₁ in (α, β) using α y₂ = 0!
    -- Actually simpler: det2 (x₁ - z) (y₂ - z) = D * β y₂!
    -- Check F₂.hxq_nonneg : 0 ≤ det2 (x₁ - z) (y₂ - z) (that gives β y₂ ≥ 0!), and if β y₂ = 0 then y₂ = z (since α y₂ = 0), impossible since y₂ ≠ z!
    have hβ_nn : 0 ≤ β y₂ := div_nonneg F₂.hxq_nonneg hD.le
    rcases eq_or_lt_of_le hβ_nn with h0 | hpos
    · exfalso
      have hcr := det2_cramer (x₁ - z) (y₁ - z) (y₂ - z)
      have h1' : det2 (y₂ - z) (y₁ - z) = 0 := by simp [det2] at hy₂_ray ⊢; linarith
      have h2' : det2 (x₁ - z) (y₂ - z) = 0 := by
        have := div_eq_zero_iff.mp h0.symm; exact this.resolve_right hD.ne'
      rw [h1', h2', zero_smul, zero_smul, add_zero] at hcr
      exact hy2_ne_z (sub_eq_zero.mp (smul_right_injective Pt hD.ne' (hcr.symm.trans (smul_zero _).symm)))
    · exact hpos
  have hβy2_lt1 : β y₂ < 1 := by
    have h1 := hor x₁ y₁ y₂; rw [hαx1, hβx1, hαy1, hβy1, hαy2] at h1; nlinarith [F₂.hxy_q_pos]
  -- Counterclockwise pentagon: f = tuple5 y₁ y₂ x₁ x₀ y₀ (chord f 0 → f 2 is y₁ → x₁!)
  let f : Fin 5 → Pt := tuple5 y₁ y₂ x₁ x₀ y₀
  have hf_mem : ∀ i : Fin 5, f i ∈ P := by
    intro i; fin_cases i
    · exact F₁.hA₂P F₁.hq
    · exact F₂.hA₂P F₂.hq
    · exact F₁.hA₂P F₁.hp
    · exact F₁.hA₁P F₁.hx
    · exact F₁.hA₁P F₁.hy
  have hf_edges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j) := by
    apply cyclic5_edges_of_10
    · rw [hor, hαy1, hβy1, hαy2, hαx1, hβx1]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hαy2, hβx0]; apply mul_pos hD; nlinarith
    · rw [hor, hαy1, hβy1, hαy2]; apply mul_pos hD; nlinarith
    · rw [hor, hαy1, hβy1, hαx1, hβx1, hβx0]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hαx1, hβx1]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hβx0]; apply mul_pos hD; linarith
    · rw [hor, hαy2, hαx1, hβx1, hβx0]; apply mul_pos hD; nlinarith
    · rw [hor, hαy2, hαx1, hβx1]; apply mul_pos hD
      nlinarith [mul_pos hβy2_pos (sub_pos.mpr hy0_sum), mul_pos (sub_pos.mpr hβy2_lt1) hβy0]
    · rw [hor, hαy2, hβx0]; apply mul_pos hD
      nlinarith [mul_pos hβy2_pos hxy0_y1, mul_pos (sub_pos.mpr hβy2_lt1) (mul_pos (by linarith : 0 < α x₀) hβy0)]
    · rw [hor, hαx1, hβx1, hβx0]; apply mul_pos hD; nlinarith
  apply hasEmptyPentagon_of_cyclic5 f hf_mem hf_edges
  intro w hw hwhull
  rcases pentagon_split hf_edges hwhull with ⟨hge, hquad⟩ | ⟨hle, htri⟩
  · have hquad' : w ∈ convexHull ℝ ({x₀, y₀, y₁, x₁} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) hquad
    rcases follower_four_hole_empty F₁ w hw hquad' with rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
  · -- w ∈ convexHull {y₁, y₂, x₁} ⊆ convexHull {x₁, y₁, y₂, x₂}!
    have htri' : w ∈ convexHull ℝ ({x₁, y₁, y₂, x₂} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) htri
    rcases follower_four_hole_empty F₂ w hw htri' with rfl | rfl | rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · -- Impossible: x₂ ∉ convexHull {y₁, y₂, x₁} because orient y₂ x₁ x₂ < 0!
      exfalso
      have hx2_ge : 0 ≤ orient y₂ x₁ w := convexHull_orient_ge (by
        rintro u (hu | hu | hu)
        · rw [hu]; exact (hf_edges 1 0 (by decide) (by decide)).le
        · rw [hu]; exact (orient_self_mid y₂ x₁).ge
        · rw [Set.mem_singleton_iff.mp hu]; exact (orient_self_right y₂ x₁).ge) w htri
      have heq_or : orient y₂ x₁ w = orient w y₂ x₁ := by
        rw [hor y₂ x₁ w, hor w y₂ x₁, hαx1, hβx1, hαy2]; ring
      linarith [F₂.hpq_x_neg]

private lemma five_hole_of_right_transition {P : Finset Pt} {z : Pt}
    {A₀ A₁ A₂ : Finset Pt} {x₀ y₀ x₁ y₁ x₂ y₂ : Pt}
    (F₁ : FollowerData P z A₀ A₁ x₀ y₀ x₁ y₁)
    (F₂ : FollowerData P z A₁ A₂ x₁ y₁ x₂ y₂)
    (hy₁_ray : det2 (y₁ - z) (y₀ - z) = 0)
    (hx₁_not_ray : 0 < det2 (x₁ - z) (x₀ - z))
    (hx₂_ray : det2 (x₁ - z) (x₂ - z) = 0) :
    HasEmptyPentagon P := by
  set D := det2 (x₁ - z) (y₁ - z)
  have hD : 0 < D := F₁.hpq_det
  let α : Pt → ℝ := fun w => det2 (w - z) (y₁ - z) / D
  let β : Pt → ℝ := fun w => det2 (x₁ - z) (w - z) / D
  have hαx1 : α x₁ = 1 := div_self hD.ne'
  have hβx1 : β x₁ = 0 := by simp [β, det2_self]
  have hαy1 : α y₁ = 0 := by simp [α, det2_self]
  have hβy1 : β y₁ = 1 := div_self hD.ne'
  have hor : ∀ a b c : Pt, orient a b c = D * ((α b - α a) * (β c - β a) - (β b - β a) * (α c - α a)) :=
    fun a b c => orient_in_basis z x₁ y₁ a b c hD.ne'
  have hαy0 : α y₀ = 0 := by
    have : det2 (y₀ - z) (y₁ - z) = -det2 (y₁ - z) (y₀ - z) := by simp [det2]; ring
    simp [α, this, hy₁_ray]
  have hβy0 : 1 < β y₀ := by
    have h1 := hor x₁ y₁ y₀; rw [hαx1, hβx1, hαy1, hβy1, hαy0] at h1; nlinarith [F₁.hpq_y_neg]
  have hβx0 : 0 < β x₀ := div_pos hx₁_not_ray hD
  have hαx0 : 0 < α x₀ := by
    have h1 := hor z x₀ y₀
    have hαz : α z = 0 := by simp [α, det2]
    have hβz : β z = 0 := by simp [β, det2]
    have hdet : orient z x₀ y₀ = det2 (x₀ - z) (y₀ - z) := by simp [orient, det2]
    rw [hdet, hαz, hβz, hαy0] at h1
    nlinarith [F₁.hxy_det, mul_pos hD (by linarith : 0 < β y₀)]
  have hx0_sum : 1 < α x₀ + β x₀ := by
    have h1 := hor x₁ y₁ x₀; rw [hαx1, hβx1, hαy1, hβy1] at h1; nlinarith [F₁.hpq_x_neg]
  have hxy0_x1 : 0 < β x₀ + β y₀ * α x₀ - β y₀ := by
    have h1 := hor x₀ y₀ x₁; rw [hαy0, hαx1, hβx1] at h1; nlinarith [F₁.hxy_p_pos]
  have hβx2 : β x₂ = 0 := by simp [β, hx₂_ray]
  have hαx2_pos : 0 < α x₂ := by
    have hx2_ne_z : x₂ ≠ z := fun h => by
      have := F₂.hpq_det; rw [h, sub_self] at this; simp [det2] at this
    have hα_nn : 0 ≤ α x₂ := div_nonneg F₂.hyp_nonneg hD.le
    rcases eq_or_lt_of_le hα_nn with h0 | hpos
    · exfalso
      have hcr := det2_cramer (x₁ - z) (y₁ - z) (x₂ - z)
      have h1' : det2 (x₂ - z) (y₁ - z) = 0 := (div_eq_zero_iff.mp h0.symm).resolve_right hD.ne'
      rw [h1', hx₂_ray, zero_smul, zero_smul, add_zero] at hcr
      exact hx2_ne_z (sub_eq_zero.mp (smul_right_injective Pt hD.ne' (hcr.symm.trans (smul_zero _).symm)))
    · exact hpos
  have hαx2_lt1 : α x₂ < 1 := by
    have h1 := hor x₁ y₁ x₂; rw [hαx1, hβx1, hαy1, hβy1, hβx2] at h1; nlinarith [F₂.hxy_p_pos]
  -- Counterclockwise pentagon: f = tuple5 y₁ x₂ x₁ x₀ y₀ (chord f 0 → f 2 is y₁ → x₁!)
  let f : Fin 5 → Pt := tuple5 y₁ x₂ x₁ x₀ y₀
  have hf_mem : ∀ i : Fin 5, f i ∈ P := by
    intro i; fin_cases i
    · exact F₁.hA₂P F₁.hq
    · exact F₂.hA₂P F₂.hp
    · exact F₁.hA₂P F₁.hp
    · exact F₁.hA₁P F₁.hx
    · exact F₁.hA₁P F₁.hy
  have hf_edges : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (f i) (f (i + 1)) (f j) := by
    apply cyclic5_edges_of_10
    · rw [hor, hαy1, hβy1, hβx2, hαx1, hβx1]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hβx2]; apply mul_pos hD
      nlinarith [mul_pos hαx2_pos (sub_pos.mpr hx0_sum), mul_pos (sub_pos.mpr hαx2_lt1) hαx0]
    · rw [hor, hαy1, hβy1, hβx2, hαy0]; apply mul_pos hD; nlinarith
    · rw [hor, hαy1, hβy1, hαx1, hβx1]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hαx1, hβx1, hαy0]; apply mul_pos hD; linarith
    · rw [hor, hαy1, hβy1, hαy0]; apply mul_pos hD; nlinarith
    · rw [hor, hβx2, hαx1, hβx1]; apply mul_pos hD; nlinarith
    · rw [hor, hβx2, hαx1, hβx1, hαy0]; apply mul_pos hD; nlinarith
    · rw [hor, hβx2, hαy0]; apply mul_pos hD
      nlinarith [mul_pos hαx2_pos hxy0_x1, mul_pos (sub_pos.mpr hαx2_lt1) (mul_pos hαx0 (by linarith : 0 < β y₀))]
    · rw [hor, hαx1, hβx1, hαy0]; apply mul_pos hD; linarith
  apply hasEmptyPentagon_of_cyclic5 f hf_mem hf_edges
  intro w hw hwhull
  rcases pentagon_split hf_edges hwhull with ⟨hge, hquad⟩ | ⟨hle, htri⟩
  · have hquad' : w ∈ convexHull ℝ ({x₀, y₀, y₁, x₁} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) hquad
    rcases follower_four_hole_empty F₁ w hw hquad' with rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
  · have htri' : w ∈ convexHull ℝ ({x₁, y₁, y₂, x₂} : Set Pt) :=
      convexHull_mono (by rintro u (hu | hu | hu) <;> rw [hu] <;> simp [f, tuple5]) htri
    rcases follower_four_hole_empty F₂ w hw htri' with rfl | rfl | rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · -- Impossible: y₂ ∉ convexHull {y₁, x₂, x₁} because orient y₁ x₂ y₂ = orient x₂ y₂ y₁ < 0!
      exfalso
      have hy2_ge : 0 ≤ orient y₁ x₂ w := convexHull_orient_ge (by
        rintro u (hu | hu | hu)
        · rw [hu]; exact (orient_self_mid y₁ x₂).ge
        · rw [hu]; exact (orient_self_right y₁ x₂).ge
        · rw [Set.mem_singleton_iff.mp hu]; exact (hf_edges 0 2 (by decide) (by decide)).le) w htri
      have heq_or : orient y₁ x₂ w = orient x₂ w y₁ := by
        rw [hor y₁ x₂ w, hor x₂ w y₁, hαy1, hβy1, hβx2]; ring
      linarith [F₂.hpq_y_neg]
    · exact ⟨1, rfl⟩

/- Extracting a FollowerData from an empty arc of layer A₁ enclosing layer A₂ -/

private lemma exists_follower_of_empty_arc {P A₁ A₂ : Finset Pt} {z : Pt}
    (hA₁P : A₁ ⊆ P) (hA₂P : A₂ ⊆ P)
    (hA₁_full : A₁ = P.filter fun w => w ∈ frontier (convexHull ℝ (A₁ : Set Pt)))
    (hA₂_full : A₂ = P.filter fun w => w ∈ frontier (convexHull ℝ (A₂ : Set Pt)))
    (hA₂_in_int : (A₂ : Set Pt) ⊆ interior (convexHull ℝ (A₁ : Set Pt)))
    (hP_split : ∀ w ∈ P, w ∈ convexHull ℝ (A₁ : Set Pt) → w ∈ A₁ ∨ w ∈ convexHull ℝ (A₂ : Set Pt))
    (hz₁ : z ∈ interior (convexHull ℝ (A₁ : Set Pt)))
    (hz₂ : z ∈ interior (convexHull ℝ (A₂ : Set Pt)))
    (C₁ : CyclicLayer A₁ z) (C₂ : CyclicLayer A₂ z)
    (i : Fin C₁.n)
    (hempty : ∀ b ∈ A₂, ¬ (0 < det2 (C₁.u i - z) (b - z) ∧
        0 < det2 (b - z) (C₁.u (cycNext C₁.hn0 i) - z))) :
    ∃ j : Fin C₂.n, FollowerData P z A₁ A₂ (C₁.u i) (C₁.u (cycNext C₁.hn0 i))
      (C₂.u j) (C₂.u (cycNext C₂.hn0 j)) := by
  have hn1 : 0 < C₁.n := C₁.hn0
  have hn2 : 0 < C₂.n := C₂.hn0
  have hA₁_front : (A₁ : Set Pt) ⊆ frontier (convexHull ℝ (A₁ : Set Pt)) := fun w hw => by
    have : w ∈ A₁ := hw; rw [hA₁_full] at this; exact (Finset.mem_filter.mp this).2
  have hA₂_front : (A₂ : Set Pt) ⊆ frontier (convexHull ℝ (A₂ : Set Pt)) := fun w hw => by
    have : w ∈ A₂ := hw; rw [hA₂_full] at this; exact (Finset.mem_filter.mp this).2
  let x := C₁.u i
  let y := C₁.u (cycNext hn1 i)
  have hxy_det : 0 < det2 (x - z) (y - z) := C₁.det_arc_pos hz₁ i
  -- Midpoint m = (1/2) • x + (1/2) • y lies strictly inside open wedge W z x y!
  let m : Pt := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hm_det1 : 0 < det2 (x - z) (m - z) := by
    have : det2 (x - z) (m - z) = det2 (x - z) (y - z) / 2 := by simp [m, det2]; ring
    linarith
  have hm_det2 : 0 < det2 (m - z) (y - z) := by
    have : det2 (m - z) (y - z) = det2 (x - z) (y - z) / 2 := by simp [m, det2]; ring
    linarith
  have hm_ne_z : m ≠ z := fun h => by rw [h, sub_self] at hm_det1; simp [det2] at hm_det1
  -- m cannot lie on any ray of C₂ (else that point of A₂ would lie in W z x y)!
  have hm_not_ray : ∀ j : Fin C₂.n, ∀ t : ℝ, 0 < t → m - z ≠ t • (C₂.u j - z) := by
    intro j t ht heq
    apply hempty (C₂.u j) (C₂.hmem j)
    have h1 : det2 (x - z) (m - z) = t * det2 (x - z) (C₂.u j - z) := by
      rw [heq]; simp [det2]; ring
    have h2 : det2 (m - z) (y - z) = t * det2 (C₂.u j - z) (y - z) := by
      rw [heq]; simp [det2]; ring
    exact ⟨by nlinarith, by nlinarith⟩
  obtain ⟨j, hj1, hj2⟩ := (C₂.exists_arc_cover hz₂ hm_ne_z).resolve_left (by
    rintro ⟨j, t, ht, heq⟩; exact hm_not_ray j t ht heq)
  let p := C₂.u j
  let q := C₂.u (cycNext hn2 j)
  have hpq_det : 0 < det2 (p - z) (q - z) := C₂.det_arc_pos hz₂ j
  -- Helper: show x, y ∈ Wbar z p q using cyclic order!
  have hxy_in_Wbar : 0 ≤ det2 (p - z) (x - z) ∧ 0 ≤ det2 (x - z) (q - z) ∧
      0 ≤ det2 (p - z) (y - z) ∧ 0 ≤ det2 (y - z) (q - z) := by
    -- Express both wedges as cyclic intervals in angleLt!
    -- Even simpler: neither p nor q lies in W z x y; m lies in W z x y ∩ W z p q!
    -- For ANY w ∈ {x, y}, if w ∉ Wbar z p q, then either p ∈ W z x y or q ∈ W z x y!
    have htr : ∀ a b c : Pt, a ≠ z → b ≠ z → c ≠ z → angleLt (a - z) (b - z) →
        angleLt (b - z) (c - z) → angleLt (a - z) (c - z) := fun a b c ha hb hc =>
      angleLt_trans (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) (sub_ne_zero.mpr hc)
    -- Use `C₂.exists_arc_cover`? No, check the 4 inequalities directly via `angleLt`!
    have hm_arc1 := (C₁.arc_wedge_iff hz₁ i hm_ne_z).mp ⟨hm_det1, hm_det2⟩
    have hm_arc2 := (C₂.arc_wedge_iff hz₂ j hm_ne_z).mp ⟨hj1, hj2⟩
    have hp_not := hempty p (C₂.hmem j)
    have hq_not := hempty q (C₂.hmem (cycNext hn2 j))
    rw [C₁.arc_wedge_iff hz₁ i (C₂.hne j)] at hp_not
    rw [C₁.arc_wedge_iff hz₁ i (C₂.hne (cycNext hn2 j))] at hq_not
    -- Show angleLt relations between x, y, p, q:
    -- Let inW1 w := if i.1 + 1 < C₁.n then angleLt x w ∧ angleLt w y else angleLt x w ∨ angleLt w y
    -- Let inW2 w := if j.1 + 1 < C₂.n then angleLt p w ∧ angleLt w q else angleLt p w ∨ angleLt w q
    -- Note: for w ∈ {x, y}, we want 0 ≤ det2 (p - z) (w - z) ∧ 0 ≤ det2 (w - z) (q - z),
    -- which holds iff (w is on ray p) ∨ (w is on ray q) ∨ (w ∈ W z p q)!
    have hWbar_of_ray_or_W : ∀ w : Pt, w ≠ z →
        ((∃ t : ℝ, 0 < t ∧ w - z = t • (p - z)) ∨ (∃ t : ℝ, 0 < t ∧ w - z = t • (q - z)) ∨
          (0 < det2 (p - z) (w - z) ∧ 0 < det2 (w - z) (q - z))) →
        0 ≤ det2 (p - z) (w - z) ∧ 0 ≤ det2 (w - z) (q - z) := by
      rintro w _ (⟨t, ht, heq⟩ | ⟨t, ht, heq⟩ | ⟨h1, h2⟩)
      · rw [heq]
        refine ⟨?_, ?_⟩
        · have : det2 (p - z) (t • (p - z)) = 0 := by simp [det2]; ring
          linarith
        · have : det2 (t • (p - z)) (q - z) = t * det2 (p - z) (q - z) := by simp [det2]; ring
          rw [this]; exact (mul_pos ht hpq_det).le
      · rw [heq]
        refine ⟨?_, ?_⟩
        · have : det2 (p - z) (t • (q - z)) = t * det2 (p - z) (q - z) := by simp [det2]; ring
          rw [this]; exact (mul_pos ht hpq_det).le
        · have : det2 (t • (q - z)) (q - z) = 0 := by simp [det2]; ring
          linarith
      · exact ⟨h1.le, h2.le⟩
    have hx_ok : 0 ≤ det2 (p - z) (x - z) ∧ 0 ≤ det2 (x - z) (q - z) := by
      apply hWbar_of_ray_or_W x (C₁.hne i)
      rcases angleLt_trichotomy (sub_ne_zero.mpr (C₂.hne j)) (sub_ne_zero.mpr (C₁.hne i)) with hpx | hxp | ⟨t, ht, heq⟩
      · rcases angleLt_trichotomy (sub_ne_zero.mpr (C₁.hne i)) (sub_ne_zero.mpr (C₂.hne (cycNext hn2 j))) with hxq | hqx | ⟨t, ht, heq⟩
        · -- angleLt p x ∧ angleLt x q!
          right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne i)]
          split_ifs with hjlt
          · exact ⟨hpx, hxq⟩
          · -- Wait: if j = n2 - 1 (wraparound), could angleLt p x ∧ angleLt x q happen?!
            -- NO! Because p = u (n2 - 1) has upperHalf = false, q = u 0 has upperHalf = true,
            -- so angleLt p x implies upperHalf x = false, and angleLt x q implies upperHalf x = true -> impossible!
            left; exact hpx
        · -- angleLt p x ∧ angleLt q x!
          -- Check: if j.1 + 1 < C₂.n, angleLt p q and angleLt q x; since m ∈ W z p q, angleLt m q < x -> contradicts x < m!
          right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne i)]
          split_ifs with hjlt
          · exfalso
            -- m has angleLt p m ∧ angleLt m q, while angleLt q x!
            -- So angleLt m x!
            rw [if_pos hjlt] at hm_arc2
            have hmx : angleLt (m - z) (x - z) := htr _ _ _ hm_ne_z (C₂.hne _) (C₁.hne i) hm_arc2.2 hqx
            split_ifs at hm_arc1 with hilt
            · exact angleLt_irrefl _ (htr _ _ _ (C₁.hne i) hm_ne_z (C₁.hne i) hm_arc1.1 hmx)
            · -- i = n1 - 1 (wraparound): x has upperHalf = false, y = u 0 has upperHalf = true!
              -- Since angleLt p x and angleLt q x, Wait: if q ∈ W z x y (meaning angleLt x q ∨ angleLt q y), contradiction!
              -- Here we know angleLt m x and (angleLt x m ∨ angleLt m y)!
              rcases hm_arc1 with hxm | hmy
              · exact angleLt_irrefl _ (htr _ _ _ (C₁.hne i) hm_ne_z (C₁.hne i) hxm hmx)
              · -- angleLt m y and angleLt m q and angleLt q x -> check angleLt q y vs angleLt y q!
                -- Since upperHalf x = false and angleLt p x, upperHalf p = false; since angleLt p q (hjlt!), upperHalf q = false!
                -- Wait: upperHalf y = true, so angleLt y q! Then angleLt m y < q < x, and upperHalf m = true (since m < y and y = true)!
                -- Wait: if upperHalf m = true and upperHalf p = false, then angleLt m p, contradicting hm_arc2.1 : angleLt p m!!
                rw [if_neg hilt] at hp_not; push Not at hp_not
                -- hp_not.2 : ¬ angleLt p y!
                -- Meanwhile hm_arc2.1 : angleLt p m and hmy : angleLt m y -> by transitivity angleLt p y!!
                exact hp_not.2 (htr _ _ _ (C₂.hne j) hm_ne_z (C₁.hne _) hm_arc2.1 hmy)
          · left; exact hpx
        · right; left; refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
          rw [heq, inv_smul_smul₀ ht.ne']
      · -- angleLt x p!
        rcases angleLt_trichotomy (sub_ne_zero.mpr (C₁.hne i)) (sub_ne_zero.mpr (C₂.hne (cycNext hn2 j))) with hxq | hqx | ⟨t, ht, heq⟩
        · -- angleLt x p ∧ angleLt x q!
          right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne i)]
          split_ifs with hjlt
          · exfalso
            rw [if_pos hjlt] at hm_arc2
            split_ifs at hm_arc1 with hilt
            · rw [if_pos hilt] at hp_not
              -- angleLt x p, angleLt p m, angleLt m y -> angleLt p y -> p ∈ W z x y, contradiction!
              exact hp_not ⟨hxp, htr _ _ _ (C₂.hne j) hm_ne_z (C₁.hne _) hm_arc2.1 hm_arc1.2⟩
            · rw [if_neg hilt] at hp_not
              exact hp_not (Or.inl hxp)
          · right
            have hj_eq : cycNext C₂.hn0 j = ⟨0, C₂.hn0⟩ := cycNext_eq_zero_of_not_lt C₂.hn0 hjlt
            rwa [← hj_eq]
        · -- angleLt x p ∧ angleLt q x!
          -- Then q < x < p! So j MUST be wraparound (n2 - 1), and then x ∈ W z p q is FALSE!
          -- Wait: if q < x < p, then p and q are on opposite sides of x!
          -- Check if j is wraparound: if j is NOT wraparound, p < q < x < p -> cycle, impossible!
          -- If j IS wraparound: m ∈ W z p q means (p < m ∨ m < q)!
          --   - If p < m: since x < p < m, and if i not wraparound then p < m < y so p ∈ W z x y, contradiction!
          --     If i IS wraparound: x < p already gives p ∈ W z x y, contradiction!
          --   - If m < q: since m < q < x, if i not wraparound x < m < q < x cycle!
          --     If i IS wraparound: q < x and m < q, either x < m (cycle m < q < x < m) or m < y!
          --     If m < y: wait, m < q < x and m < y; since ¬ (q < y) (hq_not!), y ≤ q < x;
          --     and ¬ (x < p) (hp_not!) -> CONTRADICTS x < p!!
          exfalso
          split_ifs at hm_arc2 with hjlt
          · have hpq_lt : angleLt (p - z) (q - z) :=
              C₂.hmono j (cycNext C₂.hn0 j) (show j.1 < (cycNext C₂.hn0 j).1 by rw [cycNext_val_of_lt C₂.hn0 hjlt]; omega)
            exact angleLt_irrefl _ (htr _ _ _ (C₁.hne i) (C₂.hne j) (C₁.hne i) hxp
              (htr _ _ _ (C₂.hne j) (C₂.hne _) (C₁.hne i) hpq_lt hqx))
          · split_ifs at hm_arc1 with hilt
            · rw [if_pos hilt] at hp_not hq_not
              rcases hm_arc2 with hpm | hmq
              · exact hp_not ⟨hxp, htr _ _ _ (C₂.hne j) hm_ne_z (C₁.hne _) hpm hm_arc1.2⟩
              · have hmq' : angleLt (m - z) (q - z) := by
                  have hj_eq : cycNext C₂.hn0 j = ⟨0, C₂.hn0⟩ := cycNext_eq_zero_of_not_lt C₂.hn0 hjlt
                  dsimp only [q]; rwa [hj_eq]
                exact angleLt_irrefl _ (htr _ _ _ (C₁.hne i) hm_ne_z (C₁.hne i) hm_arc1.1
                  (htr _ _ _ hm_ne_z (C₂.hne _) (C₁.hne i) hmq' hqx))
            · rw [if_neg hilt] at hp_not
              exact hp_not (Or.inl hxp)
        · right; left; refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
          rw [heq, inv_smul_smul₀ ht.ne']
      · left; exact ⟨t, ht, heq⟩
    have hy_ok : 0 ≤ det2 (p - z) (y - z) ∧ 0 ≤ det2 (y - z) (q - z) := by
      apply hWbar_of_ray_or_W y (C₁.hne (cycNext hn1 i))
      rcases angleLt_trichotomy (sub_ne_zero.mpr (C₂.hne j)) (sub_ne_zero.mpr (C₁.hne (cycNext hn1 i))) with hpy | hyp | ⟨t, ht, heq⟩
      · rcases angleLt_trichotomy (sub_ne_zero.mpr (C₁.hne (cycNext hn1 i))) (sub_ne_zero.mpr (C₂.hne (cycNext hn2 j))) with hyq | hqy | ⟨t, ht, heq⟩
        · right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne _)]
          split_ifs with hjlt
          · exact ⟨hpy, hyq⟩
          · left; exact hpy
        · right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne _)]
          split_ifs with hjlt
          · exfalso
            rw [if_pos hjlt] at hm_arc2
            split_ifs at hm_arc1 with hilt
            · rw [if_pos hilt] at hq_not
              exact hq_not ⟨htr _ _ _ (C₁.hne i) hm_ne_z (C₂.hne _) hm_arc1.1 hm_arc2.2, hqy⟩
            · rw [if_neg hilt] at hq_not
              have hi_eq : cycNext C₁.hn0 i = ⟨0, C₁.hn0⟩ := cycNext_eq_zero_of_not_lt C₁.hn0 hilt
              rw [hi_eq] at hqy
              exact hq_not (Or.inr hqy)
          · left; exact hpy
        · right; left; refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩; rw [heq, inv_smul_smul₀ ht.ne']
      · rcases angleLt_trichotomy (sub_ne_zero.mpr (C₁.hne (cycNext hn1 i))) (sub_ne_zero.mpr (C₂.hne (cycNext hn2 j))) with hyq | hqy | ⟨t, ht, heq⟩
        · right; right; rw [C₂.arc_wedge_iff hz₂ j (C₁.hne _)]
          split_ifs with hjlt
          · exfalso
            rw [if_pos hjlt] at hm_arc2
            split_ifs at hm_arc1 with hilt
            · exact angleLt_irrefl _ (htr _ _ _ hm_ne_z (C₁.hne _) hm_ne_z hm_arc1.2
                (htr _ _ _ (C₁.hne _) (C₂.hne j) hm_ne_z hyp hm_arc2.1))
            · rw [if_neg hilt] at hq_not
              rcases hm_arc1 with hxm | hmy
              · exact hq_not (Or.inl (htr _ _ _ (C₁.hne i) hm_ne_z (C₂.hne _) hxm hm_arc2.2))
              · have hi_eq : cycNext C₁.hn0 i = ⟨0, C₁.hn0⟩ := cycNext_eq_zero_of_not_lt C₁.hn0 hilt
                rw [hi_eq] at hyp
                exact angleLt_irrefl _ (htr _ _ _ hm_ne_z (C₁.hne _) hm_ne_z hmy
                  (htr _ _ _ (C₁.hne _) (C₂.hne j) hm_ne_z hyp hm_arc2.1))
          · right
            have hj_eq : cycNext C₂.hn0 j = ⟨0, C₂.hn0⟩ := cycNext_eq_zero_of_not_lt C₂.hn0 hjlt
            rwa [← hj_eq]
        · exfalso
          split_ifs at hm_arc2 with hjlt
          · have hpq_lt : angleLt (p - z) (q - z) :=
              C₂.hmono j (cycNext C₂.hn0 j) (show j.1 < (cycNext C₂.hn0 j).1 by rw [cycNext_val_of_lt C₂.hn0 hjlt]; omega)
            exact angleLt_irrefl _ (htr _ _ _ (C₁.hne _) (C₂.hne j) (C₁.hne _) hyp
              (htr _ _ _ (C₂.hne j) (C₂.hne _) (C₁.hne _) hpq_lt hqy))
          · split_ifs at hm_arc1 with hilt
            · rw [if_pos hilt] at hq_not
              rcases hm_arc2 with hpm | hmq
              · exact angleLt_irrefl _ (htr _ _ _ hm_ne_z (C₁.hne _) hm_ne_z hm_arc1.2
                  (htr _ _ _ (C₁.hne _) (C₂.hne j) hm_ne_z hyp hpm))
              · exact hq_not ⟨htr _ _ _ (C₁.hne i) hm_ne_z (C₂.hne _) hm_arc1.1
                  (by have hj_eq : cycNext C₂.hn0 j = ⟨0, C₂.hn0⟩ := cycNext_eq_zero_of_not_lt C₂.hn0 hjlt
                      rwa [hj_eq]), hqy⟩
            · rw [if_neg hilt] at hq_not
              have hi_eq : cycNext C₁.hn0 i = ⟨0, C₁.hn0⟩ := cycNext_eq_zero_of_not_lt C₁.hn0 hilt
              rw [hi_eq] at hqy
              exact hq_not (Or.inr hqy)
        · right; left; refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩; rw [heq, inv_smul_smul₀ ht.ne']
      · left; exact ⟨t, ht, heq⟩
    exact ⟨hx_ok.1, hx_ok.2, hy_ok.1, hy_ok.2⟩
  -- Deduce orient p q x < 0 and orient p q y < 0 (since x, y ∈ A₁ ⊆ ∂conv A₁, while Wbar z p q ∩ [p,q] ⊆ int(conv A₁))!
  have hpq_neg_of_Wbar : ∀ w ∈ A₁, 0 ≤ det2 (p - z) (w - z) → 0 ≤ det2 (w - z) (q - z) →
      orient p q w < 0 := by
    intro w hw h1 h2
    by_contra hge
    push Not at hge
    have hw_tri : w ∈ convexHull ℝ ({z, p, q} : Set Pt) := by
      apply mem_convexHull_triangle_of_orient
      · have : orient z p q = det2 (p - z) (q - z) := by simp [orient, det2]
        linarith
      · exact hge
      · have : orient q z w = det2 (w - z) (q - z) := by simp [orient, det2]; ring
        linarith
      · have : orient z p w = det2 (p - z) (w - z) := by simp [orient, det2]
        linarith
    have hsub : ({z, p, q} : Set Pt) ⊆ interior (convexHull ℝ (A₁ : Set Pt)) := by
      rintro u (rfl | rfl | rfl)
      · exact hz₁
      · exact hA₂_in_int (C₂.hmem j)
      · exact hA₂_in_int (C₂.hmem (cycNext hn2 j))
    have hw_int : w ∈ interior (convexHull ℝ (A₁ : Set Pt)) :=
      convexHull_min hsub (convex_convexHull ℝ (A₁ : Set Pt)).interior hw_tri
    exact (frontier_convexHull_finset A₁ ▸ hA₁_front hw).2 hw_int
  refine ⟨j, ⟨C₁.hmem i, C₁.hmem _, C₂.hmem j, C₂.hmem _, hA₁P, hA₂P, hA₁_front, hA₂_full,
    hA₂_in_int, hP_split, hxy_det, hpq_det, C₁.arc_supporting hA₁_front hz₁ i,
    C₂.arc_supporting hA₂_front hz₂ j, fun w => C₁.arc_segment_empty hz₁ i, fun w => C₂.arc_segment_empty hz₂ j,
    hxy_in_Wbar.1, hxy_in_Wbar.2.1, hxy_in_Wbar.2.2.1, hxy_in_Wbar.2.2.2,
    hpq_neg_of_Wbar x (C₁.hmem i) hxy_in_Wbar.1 hxy_in_Wbar.2.1,
    hpq_neg_of_Wbar y (C₁.hmem _) hxy_in_Wbar.2.2.1 hxy_in_Wbar.2.2.2,
    C₁.arc_supporting_interior hA₁_front hz₁ i (hA₂_in_int (C₂.hmem j)),
    C₁.arc_supporting_interior hA₁_front hz₁ i (hA₂_in_int (C₂.hmem _))⟩⟩

/- Claim B: If `p → q` is the follower of an empty arc `x → y` and `¬ HasEmptyPentagon P`,
   then `p → q` is also empty (no point of `A₃` in open wedge `W z p q`)! -/

private lemma claimB_follower_empty {P A₁ A₂ A₃ : Finset Pt} {z x y p q : Pt}
    (F : FollowerData P z A₁ A₂ x y p q)
    (hA₃P : A₃ ⊆ P) (hA₃_in_int : (A₃ : Set Pt) ⊆ interior (convexHull ℝ (A₂ : Set Pt)))
    (hnopent : ¬ HasEmptyPentagon P) :
    ∀ b ∈ A₃, ¬ (0 < det2 (p - z) (b - z) ∧ 0 < det2 (b - z) (q - z)) := by
  intro b hb ⟨hb1, hb2⟩
  -- Define D := {w ∈ P | 0 < orient p q w ∧ 0 < det2 (p - z) (w - z) ∧ 0 < det2 (w - z) (q - z)}
  let D : Finset Pt := P.filter fun w =>
    0 < orient p q w ∧ 0 < det2 (p - z) (w - z) ∧ 0 < det2 (w - z) (q - z)
  have hb_pq : 0 < orient p q b := by
    have hpq_ne : p ≠ q := fun h => by have := F.hpq_det; rw [h, det2_self] at this; linarith
    exact orient_pos_of_mem_interior (fun u hu => F.hpq_sup u (subset_convexHull ℝ _ hu)) hpq_ne (hA₃_in_int hb)
  have hD_ne : D.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hA₃P hb, hb_pq, hb1, hb2⟩⟩
  obtain ⟨r, hrD, hr_min⟩ := Finset.exists_min_image D (fun w => orient p q w) hD_ne
  obtain ⟨hrP, hr_pq, hr_p, hr_q⟩ := Finset.mem_filter.mp hrD
  apply hnopent
  refine five_hole_of_follower_point F hrP hr_pq hr_p.le hr_q.le (Or.inr hr_p) (Or.inr hr_q) ?_
  intro w hw htri hw_pq
  -- Show w ∈ D! Since w ∈ conv {p, q, r} and 0 < orient p q w, w lies in open wedge W z p q!
  have hw_p : 0 < det2 (p - z) (w - z) := by
    have hge : 0 ≤ det2 (p - z) (w - z) := by
      have : det2 (p - z) (w - z) = orient z p w := by simp [orient, det2]
      rw [this]
      apply convexHull_orient_ge _ w htri
      rintro u (hu | hu | hu)
      · rw [hu]; exact (orient_self_right z p).ge
      · rw [hu]; have : orient z p q = det2 (p - z) (q - z) := by simp [orient, det2]
        linarith [F.hpq_det]
      · rw [Set.mem_singleton_iff.mp hu]; have : orient z p r = det2 (p - z) (r - z) := by simp [orient, det2]
        linarith
    rcases eq_or_lt_of_le hge with h0 | hpos
    · exfalso
      -- If det2 (p - z) (w - z) = 0, orient z p w = 0 while orient z p q > 0 and orient z p r > 0!
      -- Since w ∈ conv {p, q, r}, convex combination weight on q and r must BOTH be 0, so w = p -> orient p q w = 0!
      have hsub : convexHull ℝ ({p, q, r} : Set Pt) ⊆ {p} ∪ {u | 0 < orient z p u} := by
        have hconv : Convex ℝ ({p} ∪ {u | 0 < orient z p u}) := by
          intro a ha b hb α β hα hβ hsum
          by_cases hα0 : α = 0
          · rw [hα0, show β = 1 by linarith]; simpa using hb
          · by_cases hβ0 : β = 0
            · rw [hβ0, show α = 1 by linarith]; simpa using ha
            · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
              have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
              have hor : orient z p (α • a + β • b) = α * orient z p a + β * orient z p b := by
                rw [show α = 1 - β by linarith, orient_aff_comb]
              rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
              · left
                rw [Set.mem_singleton_iff.mp ha1, Set.mem_singleton_iff.mp hb1, ← add_smul, hsum, one_smul]
                rfl
              · right
                change 0 < orient z p (α • a + β • b); rw [hor, Set.mem_singleton_iff.mp ha1, orient_self_right]
                change 0 < orient z p b at hb2; nlinarith
              · right
                change 0 < orient z p (α • a + β • b); rw [hor, Set.mem_singleton_iff.mp hb1, orient_self_right]
                change 0 < orient z p a at ha2; nlinarith
              · right; change 0 < orient z p (α • a + β • b); rw [hor]
                change 0 < orient z p a at ha2; change 0 < orient z p b at hb2; nlinarith
        refine convexHull_min ?_ hconv
        rintro u (hu | hu | hu)
        · rw [hu]; exact Or.inl rfl
        · rw [hu]; right; change 0 < orient z p q
          have : orient z p q = det2 (p - z) (q - z) := by simp [orient, det2]
          linarith [F.hpq_det]
        · rw [Set.mem_singleton_iff.mp hu]; right; change 0 < orient z p r
          have : orient z p r = det2 (p - z) (r - z) := by simp [orient, det2]
          linarith
      rcases hsub htri with rfl | hgt
      · rw [orient_self_mid] at hw_pq; linarith
      · have : orient z p w = det2 (p - z) (w - z) := by simp [orient, det2]
        change 0 < orient z p w at hgt; linarith
    · exact hpos
  have hw_q : 0 < det2 (w - z) (q - z) := by
    have hsub : convexHull ℝ ({p, q, r} : Set Pt) ⊆ {q} ∪ {u | 0 < orient q z u} := by
      have hconv : Convex ℝ ({q} ∪ {u | 0 < orient q z u}) := by
        intro a ha b hb α β hα hβ hsum
        by_cases hα0 : α = 0
        · rw [hα0, show β = 1 by linarith]; simpa using hb
        · by_cases hβ0 : β = 0
          · rw [hβ0, show α = 1 by linarith]; simpa using ha
          · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
            have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
            have hor : orient q z (α • a + β • b) = α * orient q z a + β * orient q z b := by
              rw [show α = 1 - β by linarith, orient_aff_comb]
            rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
            · left
              rw [Set.mem_singleton_iff.mp ha1, Set.mem_singleton_iff.mp hb1, ← add_smul, hsum, one_smul]
              rfl
            · right
              change 0 < orient q z (α • a + β • b); rw [hor, Set.mem_singleton_iff.mp ha1, orient_self_mid]
              change 0 < orient q z b at hb2; nlinarith
            · right
              change 0 < orient q z (α • a + β • b); rw [hor, Set.mem_singleton_iff.mp hb1, orient_self_mid]
              change 0 < orient q z a at ha2; nlinarith
            · right; change 0 < orient q z (α • a + β • b); rw [hor]
              change 0 < orient q z a at ha2; change 0 < orient q z b at hb2; nlinarith
      refine convexHull_min ?_ hconv
      rintro u (hu | hu | hu)
      · rw [hu]; right; change 0 < orient q z p
        have : orient q z p = det2 (p - z) (q - z) := by simp [orient, det2]; ring
        linarith [F.hpq_det]
      · rw [hu]; exact Or.inl rfl
      · rw [Set.mem_singleton_iff.mp hu]; right; change 0 < orient q z r
        have : orient q z r = det2 (r - z) (q - z) := by simp [orient, det2]; ring
        linarith
    rcases hsub htri with rfl | hgt
    · rw [orient_self_right] at hw_pq; linarith
    · have : orient q z w = det2 (w - z) (q - z) := by simp [orient, det2]; ring
      change 0 < orient q z w at hgt; linarith
  exact hr_min w (Finset.mem_filter.mpr ⟨hw, hw_pq, hw_p, hw_q⟩)

/- Claim C: For any follower `p → q` of `x → y`, either `p` is on ray `z → x` or `q` is on ray `z → y`! -/

private lemma claimC_aligned {P A₁ A₂ : Finset Pt} {z x y p q : Pt}
    (F : FollowerData P z A₁ A₂ x y p q) (hzP : z ∈ P)
    (hnopent : ¬ HasEmptyPentagon P) :
    det2 (p - z) (x - z) = 0 ∨ det2 (y - z) (q - z) = 0 := by
  by_contra hnot
  push Not at hnot
  have h1 : 0 < det2 (p - z) (x - z) := lt_of_le_of_ne F.hxp_nonneg (Ne.symm hnot.1)
  have h2 : 0 < det2 (y - z) (q - z) := lt_of_le_of_ne F.hyq_nonneg (Ne.symm hnot.2)
  let D : Finset Pt := P.filter fun w =>
    0 < orient p q w ∧ 0 ≤ det2 (p - z) (w - z) ∧ 0 ≤ det2 (w - z) (q - z)
  have hz_pq : 0 < orient p q z := by
    have : orient p q z = det2 (p - z) (q - z) := by simp [orient, det2]; ring
    linarith [F.hpq_det]
  have hD_ne : D.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hzP, hz_pq, by simp [det2], by simp [det2]⟩⟩
  obtain ⟨r, hrD, hr_min⟩ := Finset.exists_min_image D (fun w => orient p q w) hD_ne
  obtain ⟨hrP, hr_pq, hr_p, hr_q⟩ := Finset.mem_filter.mp hrD
  apply hnopent
  refine five_hole_of_follower_point F hrP hr_pq hr_p hr_q (Or.inl h1) (Or.inl h2) ?_
  intro w hw htri hw_pq
  have hw_p : 0 ≤ det2 (p - z) (w - z) := by
    have : det2 (p - z) (w - z) = orient z p w := by simp [orient, det2]
    rw [this]
    apply convexHull_orient_ge _ w htri
    rintro u (hu | hu | hu)
    · rw [hu]; exact (orient_self_right z p).ge
    · rw [hu]; have : orient z p q = det2 (p - z) (q - z) := by simp [orient, det2]
      linarith [F.hpq_det]
    · rw [Set.mem_singleton_iff.mp hu]; have : orient z p r = det2 (p - z) (r - z) := by simp [orient, det2]
      linarith
  have hw_q : 0 ≤ det2 (w - z) (q - z) := by
    have : det2 (w - z) (q - z) = orient q z w := by simp [orient, det2]; ring
    rw [this]
    apply convexHull_orient_ge _ w htri
    rintro u (hu | hu | hu)
    · rw [hu]; have : orient q z p = det2 (p - z) (q - z) := by simp [orient, det2]; ring
      linarith [F.hpq_det]
    · rw [hu]; exact (orient_self_mid q z).ge
    · rw [Set.mem_singleton_iff.mp hu]; have : orient q z r = det2 (r - z) (q - z) := by simp [orient, det2]; ring
      linarith
  exact hr_min w (Finset.mem_filter.mpr ⟨hw, hw_pq, hw_p, hw_q⟩)

/- ### Part 7: Layer peeling, induction, and main theorem -/

private noncomputable def peelLayer (P : Finset Pt) (A : Finset Pt) : Finset Pt :=
  let I := P.filter fun p => p ∈ interior (convexHull ℝ (A : Set Pt))
  P.filter fun p => p ∈ frontier (convexHull ℝ (I : Set Pt))

private lemma peelLayer_subset (P A : Finset Pt) : peelLayer P A ⊆ P :=
  Finset.filter_subset _ _

private lemma peelLayer_in_int {P A : Finset Pt} :
    (peelLayer P A : Set Pt) ⊆ interior (convexHull ℝ (A : Set Pt)) := by
  intro p hp
  have hp_mem : p ∈ peelLayer P A := hp
  simp only [peelLayer, Finset.mem_filter] at hp_mem
  have hconv : convexHull ℝ ((P.filter fun q => q ∈ interior (convexHull ℝ (A : Set Pt))) : Set Pt) ⊆
      interior (convexHull ℝ (A : Set Pt)) :=
    convexHull_min (fun q hq => (Finset.mem_filter.mp hq).2) (convex_convexHull ℝ _).interior
  exact hconv (frontier_convexHull_finset _ ▸ hp_mem.2).1

private lemma peelLayer_conv_eq {P A : Finset Pt} :
    let I := P.filter fun p => p ∈ interior (convexHull ℝ (A : Set Pt))
    convexHull ℝ (peelLayer P A : Set Pt) = convexHull ℝ (I : Set Pt) := by
  intro I
  apply le_antisymm
  · refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _)
    have hp_mem : p ∈ peelLayer P A := hp
    simp only [peelLayer, Finset.mem_filter] at hp_mem
    exact (frontier_convexHull_finset I ▸ hp_mem.2).1
  · -- Every point of I lies in convexHull (I ∩ frontier(conv I))!
    -- Prove by induction on Finset size: removing interior points of a finite set preserves convexHull!
    have hrem : ∀ (S : Finset Pt), convexHull ℝ (S : Set Pt) ⊆
        convexHull ℝ ((S.filter fun p => p ∈ frontier (convexHull ℝ (S : Set Pt))) : Set Pt) := by
      intro S
      -- Use extremePoints: every extreme point of conv S lies in S and in frontier (conv S)!
      -- Wait: even simpler, prove directly via `Finset.strongInduction` or Krein-Milman (`closure_convexHull_extremePoints`)!
      have hK := S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
      have hkm := closure_convexHull_extremePoints hK (convex_convexHull ℝ (S : Set Pt))
      have hext_sub : (convexHull ℝ (S : Set Pt)).extremePoints ℝ ⊆
          ((S.filter fun p => p ∈ frontier (convexHull ℝ (S : Set Pt))) : Set Pt) := by
        intro p hp
        have hpS : p ∈ S := extremePoints_convexHull_subset hp
        have hp_front : p ∈ frontier (convexHull ℝ (S : Set Pt)) := by
          rw [frontier_convexHull_finset]
          refine ⟨hp.1, fun hint => ?_⟩
          obtain ⟨U, hUK, hUopen, hpU⟩ := mem_interior.mp hint
          -- Pick ε > 0 so p + (ε, 0) and p - (ε, 0) are both in U ⊆ conv S!
          have hc1 : Continuous (fun t : ℝ => p + t • ((1, 0) : Pt)) := by fun_prop
          have hc2 : Continuous (fun t : ℝ => p - t • ((1, 0) : Pt)) := by fun_prop
          have ht1 : Filter.Tendsto (fun t : ℝ => p + t • ((1, 0) : Pt)) (𝓝[>] 0) (𝓝 p) := by
            simpa [ContinuousWithinAt] using hc1.continuousAt.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
          have ht2 : Filter.Tendsto (fun t : ℝ => p - t • ((1, 0) : Pt)) (𝓝[>] 0) (𝓝 p) := by
            simpa [ContinuousWithinAt] using hc2.continuousAt.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
          have he1 : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • ((1, 0) : Pt) ∈ U := ht1 (hUopen.mem_nhds hpU)
          have he2 : ∀ᶠ t : ℝ in 𝓝[>] 0, p - t • ((1, 0) : Pt) ∈ U := ht2 (hUopen.mem_nhds hpU)
          have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, (0 : ℝ) < t := self_mem_nhdsWithin
          obtain ⟨t, ht_pos, h1, h2⟩ := (hpos.and (he1.and he2)).exists
          have hopen : p ∈ openSegment ℝ (p + t • ((1, 0) : Pt)) (p - t • ((1, 0) : Pt)) := by
            refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
            ext <;> simp <;> ring
          have heq : p + t • ((1, 0) : Pt) = p := hp.2 (hUK h1) (hUK h2) hopen
          have hfst := congrArg Prod.fst heq
          simp at hfst; linarith
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hpS, hp_front⟩)
      have hclosed : IsClosed (convexHull ℝ ((S.filter fun p => p ∈ frontier (convexHull ℝ (S : Set Pt))) : Set Pt)) :=
        ((S.filter _).finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
      calc convexHull ℝ (S : Set Pt)
          = closure (convexHull ℝ ((convexHull ℝ (S : Set Pt)).extremePoints ℝ)) := hkm.symm
        _ ⊆ closure (convexHull ℝ ((S.filter fun p => p ∈ frontier (convexHull ℝ (S : Set Pt))) : Set Pt)) :=
            closure_mono (convexHull_mono hext_sub)
        _ = convexHull ℝ ((S.filter fun p => p ∈ frontier (convexHull ℝ (S : Set Pt))) : Set Pt) :=
            hclosed.closure_eq
    have hsub : (I.filter fun p => p ∈ frontier (convexHull ℝ (I : Set Pt))) ⊆ peelLayer P A := by
      intro p hp
      obtain ⟨hpI, hpf⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpI).1, hpf⟩
    exact (hrem I).trans (convexHull_mono (Finset.coe_subset.mpr hsub))

private lemma peelLayer_full {P A : Finset Pt} :
    peelLayer P A = P.filter fun p => p ∈ frontier (convexHull ℝ (peelLayer P A : Set Pt)) := by
  rw [peelLayer_conv_eq]; rfl

private lemma peelLayer_split {P A : Finset Pt}
    (hA_full : A = P.filter fun p => p ∈ frontier (convexHull ℝ (A : Set Pt))) :
    ∀ w ∈ P, w ∈ convexHull ℝ (A : Set Pt) → w ∈ A ∨ w ∈ convexHull ℝ (peelLayer P A : Set Pt) := by
  intro w hw hwhull
  by_cases hwf : w ∈ frontier (convexHull ℝ (A : Set Pt))
  · left; rw [hA_full]; exact Finset.mem_filter.mpr ⟨hw, hwf⟩
  · right
    rw [peelLayer_conv_eq]
    refine subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hw, ?_⟩))
    rw [frontier_convexHull_finset, Set.mem_sdiff, not_and_or, not_not] at hwf
    exact hwf.resolve_left (not_not.mpr hwhull)

private lemma peelLayer_card_bound {P A : Finset Pt} {k : ℕ} (hk : 3 ≤ k)
    (hAP : A ⊆ P) (hA_full : A = P.filter fun p => p ∈ frontier (convexHull ℝ (A : Set Pt)))
    (hnocol : ¬ HasCollinear k P) (hnopent : ¬ HasEmptyPentagon P) :
    A.card < 11 * k * ((peelLayer P A).card + 2) :=
  layer_card_bound hk hAP hA_full hnocol hnopent

private noncomputable def iterPeel (P A : Finset Pt) : ℕ → Finset Pt
  | 0 => A
  | n + 1 => peelLayer P (iterPeel P A n)

private lemma iterPeel_subset (P A : Finset Pt) (hAP : A ⊆ P) :
    ∀ n : ℕ, iterPeel P A n ⊆ P
  | 0 => hAP
  | _ + 1 => peelLayer_subset P _

private lemma iterPeel_full (P A : Finset Pt)
    (hA_full : A = P.filter fun p => p ∈ frontier (convexHull ℝ (A : Set Pt))) :
    ∀ n : ℕ, iterPeel P A n = P.filter fun p => p ∈ frontier (convexHull ℝ (iterPeel P A n : Set Pt))
  | 0 => hA_full
  | _ + 1 => peelLayer_full

private lemma iterPeel_in_int (P A : Finset Pt) (n : ℕ) :
    (iterPeel P A (n + 1) : Set Pt) ⊆ interior (convexHull ℝ (iterPeel P A n : Set Pt)) :=
  peelLayer_in_int

private lemma iterPeel_strict_subset_hull {P A : Finset Pt} {i j : ℕ} (hij : i < j) :
    (iterPeel P A j : Set Pt) ⊆ interior (convexHull ℝ (iterPeel P A i : Set Pt)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hEq : i = j
    · subst hEq; exact iterPeel_in_int P A i
    · have h1 := iterPeel_in_int P A j
      have h2 := ih (by omega)
      have h3 : convexHull ℝ (iterPeel P A j : Set Pt) ⊆ interior (convexHull ℝ (iterPeel P A i : Set Pt)) :=
        convexHull_min h2 (convex_convexHull ℝ _).interior
      exact h1.trans (interior_subset.trans h3)

private lemma iterPeel_disjoint {P A : Finset Pt}
    (hA_full : A = P.filter fun p => p ∈ frontier (convexHull ℝ (A : Set Pt)))
    {i j : ℕ} (hij : i < j) {x : Pt} (hi : x ∈ iterPeel P A i) (hj : x ∈ iterPeel P A j) : False := by
  have hint := iterPeel_strict_subset_hull hij hj
  have hfi : x ∈ frontier (convexHull ℝ (iterPeel P A i : Set Pt)) := by
    have := iterPeel_full P A hA_full i
    rw [this] at hi; exact (Finset.mem_filter.mp hi).2
  exact (frontier_convexHull_finset _ ▸ hfi).2 hint

theorem main : OMA.R_Green70_green_70_variants_empty_pentagon_R1.H2 := by
  intro k hk
  -- Choose M = (33 * k) ^ k so any layer A_i (i < k) has interior nonempty!
  let M : ℕ := (33 * k) ^ k
  refine ⟨M, fun P S hSP hSfront hnocol hnopent => ?_⟩
  by_contra hge
  push Not at hge
  -- Consider all subsets X ⊆ P with M ≤ X.card and X ⊆ frontier (convexHull ℝ X)
  let Cands : Finset (Finset Pt) := P.powerset.filter fun X =>
    M ≤ X.card ∧ (X : Set Pt) ⊆ frontier (convexHull ℝ (X : Set Pt))
  have hS_cand : S ∈ Cands := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSP, hge, hSfront⟩
  obtain ⟨A0, hA0_cand, hA0_min⟩ := Finset.exists_min_image Cands
    (fun X => (P.filter fun p => p ∈ convexHull ℝ (X : Set Pt)).card) ⟨S, hS_cand⟩
  obtain ⟨hA0P', hA0_card, hA0_front⟩ := Finset.mem_filter.mp hA0_cand
  have hA0P : A0 ⊆ P := Finset.mem_powerset.mp hA0P'
  -- Expand A0 to the full boundary layer A1 := P ∩ frontier (conv A0)!
  let A1 : Finset Pt := P.filter fun p => p ∈ frontier (convexHull ℝ (A0 : Set Pt))
  have hA0_sub_A1 : A0 ⊆ A1 := fun p hp => Finset.mem_filter.mpr ⟨hA0P hp, hA0_front hp⟩
  have hA1_conv : convexHull ℝ (A1 : Set Pt) = convexHull ℝ (A0 : Set Pt) := by
    apply le_antisymm
    · refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _)
      have : p ∈ A1 := hp
      exact (frontier_convexHull_finset A0 ▸ (Finset.mem_filter.mp this).2).1
    · exact convexHull_mono (Finset.coe_subset.mpr hA0_sub_A1)
  have hA1P : A1 ⊆ P := Finset.filter_subset _ _
  have hA1_full : A1 = P.filter fun p => p ∈ frontier (convexHull ℝ (A1 : Set Pt)) := by
    rw [hA1_conv]
  have hA1_card : M ≤ A1.card := hA0_card.trans (Finset.card_le_card hA0_sub_A1)
  have hA1_min : ∀ X ⊆ P, (X : Set Pt) ⊆ frontier (convexHull ℝ (X : Set Pt)) →
      (P.filter fun p => p ∈ convexHull ℝ (X : Set Pt)).card <
      (P.filter fun p => p ∈ convexHull ℝ (A1 : Set Pt)).card → X.card < M := by
    intro X hXP hXfront hlt
    by_contra hXbig
    push Not at hXbig
    have hX_cand : X ∈ Cands := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hXP, hXbig, hXfront⟩
    have hle := hA0_min X hX_cand
    rw [hA1_conv] at hlt
    omega
  -- Define layers L i := iterPeel P A1 i for i = 0, 1, ..., k - 1!
  let L : ℕ → Finset Pt := iterPeel P A1
  -- Show (L i).card ≥ (33 * k) ^ (k - i) for all i ≤ k!
  have hL_card_ge : ∀ i : ℕ, i ≤ k → (33 * k) ^ (k - i) ≤ (L i).card := by
    intro i
    induction i with
    | zero => intro _; simpa [L, iterPeel, M] using hA1_card
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hrec := peelLayer_card_bound hk (iterPeel_subset P A1 hA1P i)
        (iterPeel_full P A1 hA1_full i) hnocol hnopent
      change (L i).card < 11 * k * ((L (i + 1)).card + 2) at hrec
      have hpow : (33 * k) ^ (k - i) = 33 * k * (33 * k) ^ (k - (i + 1)) := by
        rw [show k - i = (k - (i + 1)) + 1 by omega, pow_succ']
      have hpos : 1 ≤ (33 * k) ^ (k - (i + 1)) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  -- In particular, for i = k - 1, (L (k - 1)).card ≥ 33 * k ≥ 3, AND L (k - 1) has nonempty interior
  -- because L k has card ≥ 1, so picking z ∈ L k gives z ∈ interior (conv (L i)) for ALL i < k!
  have hLk_ne : (L k).Nonempty := Finset.card_pos.mp (by
    have := hL_card_ge k le_rfl
    simp only [Nat.sub_self, pow_zero] at this
    omega)
  obtain ⟨z, hz_Lk⟩ := hLk_ne
  have hzP : z ∈ P := iterPeel_subset P A1 hA1P k hz_Lk
  have hz_int : ∀ i : ℕ, i < k → z ∈ interior (convexHull ℝ (L i : Set Pt)) := fun i hi =>
    iterPeel_strict_subset_hull hi hz_Lk
  have hL_front : ∀ i : ℕ, (L i : Set Pt) ⊆ frontier (convexHull ℝ (L i : Set Pt)) := fun i p hp => by
    have : p ∈ iterPeel P A1 i := hp
    rw [iterPeel_full P A1 hA1_full i] at this
    exact (Finset.mem_filter.mp this).2
  -- Build CyclicLayer C i for every i < k around z!
  have hC_ex : ∀ i : ℕ, i < k → Nonempty (CyclicLayer (L i) z) := fun i hi =>
    build_cyclicLayer (hL_front i) (hz_int i hi)
  let C : ∀ i : ℕ, i < k → CyclicLayer (L i) z := fun i hi => (hC_ex i hi).some
  -- Step 1: L 0 (= A1) MUST have an empty arc (otherwise |L 1| ≥ |L 0| ≥ M, contradicting minimality of A1)!
  have hL1_lt : (L 1).card < (L 0).card := by
    have hL1_lt_M : (L 1).card < M := by
      apply hA1_min (L 1) (iterPeel_subset P A1 hA1P 1) (hL_front 1)
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro p hp
        obtain ⟨hpP, hphull⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨hpP, ?_⟩
        exact convexHull_min (fun q hq => interior_subset (iterPeel_in_int P A1 0 hq))
          (convex_convexHull ℝ _) hphull
      · intro hEq
        have hM_pos : 0 < M := Nat.pos_of_ne_zero (by positivity)
        obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (lt_of_lt_of_le hM_pos hA1_card)
        have hmemA1 : a0 ∈ P.filter fun p => p ∈ convexHull ℝ (A1 : Set Pt) :=
          Finset.mem_filter.mpr ⟨hA1P ha0, subset_convexHull ℝ _ ha0⟩
        rw [← hEq] at hmemA1
        have hmemL1 : a0 ∈ convexHull ℝ (L 1 : Set Pt) := (Finset.mem_filter.mp hmemA1).2
        have hint : a0 ∈ interior (convexHull ℝ (A1 : Set Pt)) :=
          convexHull_min (iterPeel_in_int P A1 0) (convex_convexHull ℝ _).interior hmemL1
        exact (frontier_convexHull_finset A1 ▸ hL_front 0 ha0).2 hint
    have hL0_ge : M ≤ (L 0).card := hA1_card
    omega
  have hex_empty0 : ∃ i₀ : Fin (C 0 (by omega)).n,
      ∀ b ∈ L 1, ¬ (0 < det2 ((C 0 (by omega)).u i₀ - z) (b - z) ∧
        0 < det2 (b - z) ((C 0 (by omega)).u (cycNext (C 0 (by omega)).hn0 i₀) - z)) := by
    by_contra hnone
    push Not at hnone
    let C0 := C 0 (by omega)
    let g : Fin C0.n → Pt := fun i => (hnone i).choose
    have hg_mem : ∀ i : Fin C0.n, g i ∈ L 1 := fun i => (hnone i).choose_spec.1
    have hg_inj : Function.Injective g := by
      intro i1 i2 heq
      by_contra hne
      have h1 := (hnone i1).choose_spec.2
      have h2 := (hnone i2).choose_spec.2
      change 0 < det2 (C0.u i1 - z) (g i1 - z) ∧ 0 < det2 (g i1 - z) (C0.u (cycNext C0.hn0 i1) - z) at h1
      change 0 < det2 (C0.u i2 - z) (g i2 - z) ∧ 0 < det2 (g i2 - z) (C0.u (cycNext C0.hn0 i2) - z) at h2
      rw [heq] at h1
      exact C0.arc_wedge_disjoint (hz_int 0 (by omega)) hne ⟨h1, h2⟩
    have hle : C0.n ≤ (L 1).card := by
      calc C0.n = (Finset.univ.image g).card := by
              rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]
        _ ≤ (L 1).card := Finset.card_le_card (Finset.image_subset_iff.mpr fun i _ => hg_mem i)
    have hcard0 := C0.hcard
    omega
  obtain ⟨i₀, hi₀_empty⟩ := hex_empty0
  -- Step 2: Build the chain of empty arcs idx : (t : ℕ) → (ht : t < k) → Fin (C t ht).n
  -- with FollowerData at every step t → t + 1 (for t + 1 < k)!
  have hbuild_chain : ∃ (idx : ∀ t : ℕ, (ht : t < k) → Fin (C t ht).n),
      ∀ (t : ℕ) (ht1 : t + 1 < k),
        FollowerData P z (L t) (L (t + 1))
          ((C t (by omega)).u (idx t (by omega)))
          ((C t (by omega)).u (cycNext (C t (by omega)).hn0 (idx t (by omega))))
          ((C (t + 1) ht1).u (idx (t + 1) ht1))
          ((C (t + 1) ht1).u (cycNext (C (t + 1) ht1).hn0 (idx (t + 1) ht1))) := by
    -- Build recursively a dependent function up to any m < k
    have hrec : ∀ m : ℕ, (hm : m < k) →
        ∃ (idx : ∀ t : ℕ, (ht : t ≤ m) → Fin (C t (by omega)).n),
          (∀ (t : ℕ) (ht1 : t + 1 ≤ m),
            FollowerData P z (L t) (L (t + 1))
              ((C t (by omega)).u (idx t (by omega)))
              ((C t (by omega)).u (cycNext (C t (by omega)).hn0 (idx t (by omega))))
              ((C (t + 1) (by omega)).u (idx (t + 1) ht1))
              ((C (t + 1) (by omega)).u (cycNext (C (t + 1) (by omega)).hn0 (idx (t + 1) ht1)))) ∧
          (m + 1 < k → ∀ b ∈ L (m + 1),
            ¬ (0 < det2 ((C m hm).u (idx m le_rfl) - z) (b - z) ∧
               0 < det2 (b - z) ((C m hm).u (cycNext (C m hm).hn0 (idx m le_rfl)) - z))) := by
      intro m
      induction m with
      | zero =>
        intro hm
        refine ⟨fun t ht => (Nat.eq_zero_of_le_zero ht).symm ▸ i₀, fun t ht1 => by omega, fun _ => hi₀_empty⟩
      | succ m ih =>
        intro hm1
        obtain ⟨idx, hF, hempty_m⟩ := ih (by omega)
        have hm_empty := hempty_m hm1
        obtain ⟨j_next, hF_next⟩ := exists_follower_of_empty_arc
          (iterPeel_subset P A1 hA1P m) (iterPeel_subset P A1 hA1P (m + 1))
          (iterPeel_full P A1 hA1_full m) (iterPeel_full P A1 hA1_full (m + 1))
          (iterPeel_in_int P A1 m) (peelLayer_split (iterPeel_full P A1 hA1_full m))
          (hz_int m (by omega)) (hz_int (m + 1) hm1)
          (C m (by omega)) (C (m + 1) hm1) (idx m le_rfl) hm_empty
        let idx' : ∀ t : ℕ, (ht : t ≤ m + 1) → Fin (C t (by omega)).n := fun t ht =>
          if htm : t ≤ m then idx t htm else (show m + 1 = t by omega) ▸ j_next
        refine ⟨idx', ?_, ?_⟩
        · intro t ht1
          by_cases htm : t + 1 ≤ m
          · have h1 : idx' t (by omega) = idx t (by omega) := dif_pos (by omega)
            have h2 : idx' (t + 1) ht1 = idx (t + 1) htm := dif_pos htm
            rw [h1, h2]; exact hF t htm
          · have hteq : t = m := by omega
            subst hteq
            have h1 : idx' t (by omega) = idx t le_rfl := dif_pos le_rfl
            have h2 : idx' (t + 1) ht1 = j_next := dif_neg (by omega)
            rw [h1, h2]; exact hF_next
        · intro hm2 b hb
          have hlast : idx' (m + 1) le_rfl = j_next := dif_neg (by omega)
          rw [hlast]
          exact claimB_follower_empty hF_next (iterPeel_subset P A1 hA1P (m + 2))
            (iterPeel_in_int P A1 (m + 1)) hnopent b hb
    obtain ⟨idx, hF, -⟩ := hrec (k - 1) (by omega)
    exact ⟨fun t ht => idx t (by omega), fun t ht1 => hF t (by omega)⟩
  obtain ⟨idx, hF⟩ := hbuild_chain
  let xPt : ∀ t : ℕ, t < k → Pt := fun t ht => (C t ht).u (idx t ht)
  let yPt : ∀ t : ℕ, t < k → Pt := fun t ht =>
    (C t ht).u (cycNext (C t ht).hn0 (idx t ht))
  -- For each step t ∈ {0, ..., k - 2}, classify transition t → t + 1 via Claim C!
  have hAlign : ∀ (t : ℕ) (ht1 : t + 1 < k),
      det2 (xPt (t + 1) ht1 - z) (xPt t (by omega) - z) = 0 ∨
      det2 (yPt t (by omega) - z) (yPt (t + 1) ht1 - z) = 0 := fun t ht1 =>
    claimC_aligned (hF t ht1) hzP hnopent
  -- Cannot have ALL steps t < k - 1 left-or-double aligned (otherwise {xPt 0, ..., xPt (k-2), z} are k collinear points)!
  have hnot_all_left : ∃ (t : ℕ) (ht1 : t + 1 < k),
      det2 (xPt (t + 1) ht1 - z) (xPt t (by omega) - z) ≠ 0 := by
    by_contra hall
    push Not at hall
    -- Show every xPt t lies on line (z, xPt 0)!
    have hon : ∀ t : ℕ, (ht : t < k) → orient z (xPt 0 (by omega)) (xPt t ht) = 0 := by
      intro t
      induction t with
      | zero => intro _; exact orient_self_right _ _
      | succ t ih =>
        intro ht1
        have hprev := ih (by omega)
        have hstep := hall t ht1
        have hne0 : xPt 0 (by omega) ≠ z := (C 0 (by omega)).hne _
        have hnet : xPt t (by omega) ≠ z := (C t (by omega)).hne _
        -- det2 (xPt 0 - z) (xPt t - z) = 0 and det2 (xPt (t+1) - z) (xPt t - z) = 0 with xPt t ≠ z
        -- implies det2 (xPt 0 - z) (xPt (t+1) - z) = 0!
        have hstep' : orient z (xPt t (by omega)) (xPt (t + 1) ht1) = 0 := by
          simp [orient, det2] at hstep ⊢; linarith
        have h0_on : orient z (xPt t (by omega)) (xPt 0 (by omega)) = 0 := by
          rw [orient_swap]; linarith
        exact orient_collinear_of_three_on_line hnet.symm (orient_self_mid _ _) h0_on hstep'
    let g : Fin k → Pt := fun t => if ht : t.1 < k - 1 then xPt t.1 (by omega) else z
    have hg_mem : ∀ t : Fin k, g t ∈ P := fun t => by
      by_cases ht : t.1 < k - 1
      · simp only [g, dif_pos ht]; exact iterPeel_subset P A1 hA1P t.1 ((C t.1 (by omega)).hmem _)
      · simp only [g, dif_neg ht]; exact hzP
    have hg_inj : Function.Injective g := by
      intro t1 t2 heq
      by_contra hne
      have hord : ∀ a b : Fin k, a < b → g a ≠ g b := by
        intro a b hab hEq
        have ha_lt : a.1 < k - 1 := by have := b.isLt; have : a.1 < b.1 := hab; omega
        by_cases hb_lt : b.1 < k - 1
        · simp only [g, dif_pos ha_lt, dif_pos hb_lt] at hEq
          have ha_L : xPt a.1 (by omega) ∈ L a.1 := (C a.1 (by omega)).hmem _
          have hb_L : xPt b.1 (by omega) ∈ L b.1 := (C b.1 (by omega)).hmem _
          rw [hEq] at ha_L
          exact iterPeel_disjoint hA1_full hab ha_L hb_L
        · simp only [g, dif_pos ha_lt, dif_neg hb_lt] at hEq
          exact (C a.1 (by omega)).hne _ hEq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hord t1 t2 hlt heq
      · exact hord t2 t1 hgt heq.symm
    let Kset : Finset Pt := Finset.univ.image g
    have hKcol : Collinear ℝ (Kset : Set Pt) := by
      apply collinear_of_orient_zero (a := z) (b := xPt 0 (by omega)) ((C 0 (by omega)).hne _).symm
      intro p hp
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨t, -, rfl⟩
      by_cases ht : t.1 < k - 1
      · simp only [g, dif_pos ht]; exact hon t.1 (by omega)
      · simp only [g, dif_neg ht]; exact orient_self_mid _ _
    exact hnocol ⟨Kset, Finset.image_subset_iff.mpr fun t _ => hg_mem t,
      by rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin], hKcol⟩
  -- Symmetrically, cannot have ALL steps t < k - 1 right-or-double aligned!
  have hnot_all_right : ∃ (t : ℕ) (ht1 : t + 1 < k),
      det2 (yPt t (by omega) - z) (yPt (t + 1) ht1 - z) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hon : ∀ t : ℕ, (ht : t < k) → orient z (yPt 0 (by omega)) (yPt t ht) = 0 := by
      intro t
      induction t with
      | zero => intro _; exact orient_self_right _ _
      | succ t ih =>
        intro ht1
        have hprev := ih (by omega)
        have hstep := hall t ht1
        have hnet : yPt t (by omega) ≠ z := (C t (by omega)).hne _
        have hstep' : orient z (yPt t (by omega)) (yPt (t + 1) ht1) = 0 := by
          simp [orient, det2] at hstep ⊢; linarith
        have h0_on : orient z (yPt t (by omega)) (yPt 0 (by omega)) = 0 := by
          rw [orient_swap]; linarith
        exact orient_collinear_of_three_on_line hnet.symm (orient_self_mid _ _) h0_on hstep'
    let g : Fin k → Pt := fun t => if ht : t.1 < k - 1 then yPt t.1 (by omega) else z
    have hg_mem : ∀ t : Fin k, g t ∈ P := fun t => by
      by_cases ht : t.1 < k - 1
      · simp only [g, dif_pos ht]; exact iterPeel_subset P A1 hA1P t.1 ((C t.1 (by omega)).hmem _)
      · simp only [g, dif_neg ht]; exact hzP
    have hg_inj : Function.Injective g := by
      intro t1 t2 heq
      by_contra hne
      have hord : ∀ a b : Fin k, a < b → g a ≠ g b := by
        intro a b hab hEq
        have ha_lt : a.1 < k - 1 := by have := b.isLt; have : a.1 < b.1 := hab; omega
        by_cases hb_lt : b.1 < k - 1
        · simp only [g, dif_pos ha_lt, dif_pos hb_lt] at hEq
          have ha_L : yPt a.1 (by omega) ∈ L a.1 := (C a.1 (by omega)).hmem _
          have hb_L : yPt b.1 (by omega) ∈ L b.1 := (C b.1 (by omega)).hmem _
          rw [hEq] at ha_L
          exact iterPeel_disjoint hA1_full hab ha_L hb_L
        · simp only [g, dif_pos ha_lt, dif_neg hb_lt] at hEq
          exact (C a.1 (by omega)).hne _ hEq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hord t1 t2 hlt heq
      · exact hord t2 t1 hgt heq.symm
    let Kset : Finset Pt := Finset.univ.image g
    have hKcol : Collinear ℝ (Kset : Set Pt) := by
      apply collinear_of_orient_zero (a := z) (b := yPt 0 (by omega)) ((C 0 (by omega)).hne _).symm
      intro p hp
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨t, -, rfl⟩
      by_cases ht : t.1 < k - 1
      · simp only [g, dif_pos ht]; exact hon t.1 (by omega)
      · simp only [g, dif_neg ht]; exact orient_self_mid _ _
    exact hnocol ⟨Kset, Finset.image_subset_iff.mpr fun t _ => hg_mem t,
      by rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin], hKcol⟩
  -- Wait: hnot_all_left gives a RIGHT-aligned step t_R (y aligned, x NOT aligned) in {0, ..., k - 2},
  -- and hnot_all_right gives a LEFT-aligned step t_L (x aligned, y NOT aligned) in {0, ..., k - 2}!
  -- Wait: in {0, ..., k - 2}, check indices!
  -- Actually in hnot_all_left, g used t.1 < k - 1, which ONLY checks steps 0, ..., k - 3 (k - 1 points xPt 0..xPt(k-2) + z = k points)!
  -- WAIT: for t = k - 2, xPt (k - 1) wasn't even needed in g! Wait: our induction in hon proved it for all t < k,
  -- using hall for t + 1 < k (which includes t = k - 2)! That's completely valid!
  -- Now obtain t_R (not left) and t_L (not right) with t_R + 1 < k and t_L + 1 < k!
  obtain ⟨tR, htR1, hR_ne⟩ := hnot_all_left
  obtain ⟨tL, htL1, hL_ne⟩ := hnot_all_right
  -- Note tR ≠ tL because at tR we have y aligned (by hAlign), whereas at tL we have y NOT aligned!
  have htRL_ne : tR ≠ tL := fun h => by
    subst h
    rcases hAlign tR htR1 with hx0 | hy0
    · exact hR_ne hx0
    · exact hL_ne hy0
  rcases lt_or_gt_of_ne htRL_ne with hRL | hLR
  · -- tR < tL: find smallest j ∈ (tR, tL] where step j is NOT strictly right-aligned (i.e., x IS aligned at j)!
    let S : Finset ℕ := (Finset.Ioc tR tL).filter fun j =>
      ∃ hj1 : j + 1 < k, det2 (xPt (j + 1) hj1 - z) (xPt j (by omega) - z) = 0
    have htL_in : tL ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hRL, le_rfl⟩,
      ⟨htL1, (hAlign tL htL1).resolve_right hL_ne⟩⟩
    obtain ⟨j, hj_in, hj_min⟩ := Finset.exists_min_image S id ⟨tL, htL_in⟩
    have hj_mem := Finset.mem_filter.mp hj_in
    have hj_gt : tR < j := (Finset.mem_Ioc.mp hj_mem.1).1
    have hj_le : j ≤ tL := (Finset.mem_Ioc.mp hj_mem.1).2
    obtain ⟨hj1, hj_x0⟩ := hj_mem.2
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + 1 := ⟨j - 1, by omega⟩
    have hm2 : m + 2 < k := by omega
    have hm1 : m + 1 < k := by omega
    have hm_x0 : det2 (xPt (m + 2) hm2 - z) (xPt (m + 1) hm1 - z) = 0 := hj_x0
    have hm_not_x : det2 (xPt (m + 1) hm1 - z) (xPt m (by omega) - z) ≠ 0 := by
      by_cases hEq : m = tR
      · subst hEq; exact hR_ne
      · intro hx0
        have hmem' : m ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ⟨hm1, hx0⟩⟩
        have hle : m + 1 ≤ m := hj_min m hmem'
        omega
    have hm_y0 : det2 (yPt m (by omega) - z) (yPt (m + 1) hm1 - z) = 0 :=
      (hAlign m hm1).resolve_left hm_not_x
    have hF1 := hF m hm1
    have hF2 := hF (m + 1) hm2
    have hx_pos : 0 < det2 (xPt (m + 1) hm1 - z) (xPt m (by omega) - z) :=
      lt_of_le_of_ne hF1.hxp_nonneg (Ne.symm hm_not_x)
    have hy_ray : det2 (yPt (m + 1) hm1 - z) (yPt m (by omega) - z) = 0 := by
      simp [det2] at hm_y0 ⊢; linarith
    have hx2_ray : det2 (xPt (m + 1) hm1 - z) (xPt (m + 2) hm2 - z) = 0 := by
      simp [det2] at hm_x0 ⊢; linarith
    exact hnopent (five_hole_of_right_transition hF1 hF2 hy_ray hx_pos hx2_ray)
  · -- tL < tR: find smallest j ∈ (tL, tR] where step j is NOT strictly left-aligned (i.e., y IS aligned at j)!
    let S : Finset ℕ := (Finset.Ioc tL tR).filter fun j =>
      ∃ hj1 : j + 1 < k, det2 (yPt j (by omega) - z) (yPt (j + 1) hj1 - z) = 0
    have htR_in : tR ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hLR, le_rfl⟩,
      ⟨htR1, (hAlign tR htR1).resolve_left hR_ne⟩⟩
    obtain ⟨j, hj_in, hj_min⟩ := Finset.exists_min_image S id ⟨tR, htR_in⟩
    have hj_mem := Finset.mem_filter.mp hj_in
    have hj_gt : tL < j := (Finset.mem_Ioc.mp hj_mem.1).1
    have hj_le : j ≤ tR := (Finset.mem_Ioc.mp hj_mem.1).2
    obtain ⟨hj1, hj_y0⟩ := hj_mem.2
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + 1 := ⟨j - 1, by omega⟩
    have hm2 : m + 2 < k := by omega
    have hm1 : m + 1 < k := by omega
    have hm_y0_next : det2 (yPt (m + 1) hm1 - z) (yPt (m + 2) hm2 - z) = 0 := hj_y0
    have hm_not_y : det2 (yPt m (by omega) - z) (yPt (m + 1) hm1 - z) ≠ 0 := by
      by_cases hEq : m = tL
      · subst hEq; exact hL_ne
      · intro hy0
        have hmem' : m ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ⟨hm1, hy0⟩⟩
        have hle : m + 1 ≤ m := hj_min m hmem'
        omega
    have hm_x0 : det2 (xPt (m + 1) hm1 - z) (xPt m (by omega) - z) = 0 :=
      (hAlign m hm1).resolve_right hm_not_y
    have hF1 := hF m hm1
    have hF2 := hF (m + 1) hm2
    have hy_pos : 0 < det2 (yPt m (by omega) - z) (yPt (m + 1) hm1 - z) :=
      lt_of_le_of_ne hF1.hyq_nonneg (Ne.symm hm_not_y)
    exact hnopent (five_hole_of_left_transition hF1 hF2 hm_x0 hy_pos hm_y0_next)

end Green70H2Proof

theorem OMA.solution : OMA.R_Green70_green_70_variants_empty_pentagon_R1.H2 :=
  Green70H2Proof.main
