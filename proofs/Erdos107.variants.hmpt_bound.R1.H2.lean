import OMAReductions.R_Erdos107_variants_hmpt_bound_R1

/-!
A projective chart at one transversal point puts a subfamily into ordered
convex position. The HMPT chain count in alternating gaps gives the required
finite bound, which is converted to the asymptotic threshold.
-/

-- Step Erdos107.variants.hmpt_bound.R1.H2: hypothesis H2 of reduction Erdos107.variants.hmpt_bound.R1
-- Credit: @<handle>
-- H2 := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, 1 ≤ k ∧     (k : ℝ) ≤ C * Real.sqrt (n * Real.log n) ∧     ∀ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),       (∀ i j l, ∀ x ∈ T i, ∀ y ∈ T j, ∀ z ∈ T l, x ≠ y → y ≠ z → x ≠ z →         ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →       (∀ g : Fin k → EuclideanSpace ℝ (Fin 2), (∀ i, g i ∈ T i) →         Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a})) →       (∀ i, (2 : ℝ) ^ ((n : ℝ) + C * Real.sqrt (n * Real.log n)) < (T i).card) →       ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n ∧ (∀ p ∈ S, ∃ i, p ∈ T i) ∧         ∀ a ∈ (S : Set (EuclideanSpace ℝ (Fin 2))),           a ∉ convexHull ℝ ((S : Set (EuclideanSpace ℝ (Fin 2))) \ {a})

open Filter
open scoped BigOperators

namespace HMPTStep

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def ConvexPosition (S : Set Plane) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (S \ {p})

private def General {ι : Type*} (T : ι → Finset Plane) : Prop :=
  ∀ i j l, ∀ x ∈ T i, ∀ y ∈ T j, ∀ z ∈ T l, x ≠ y → y ≠ z → x ≠ z →
    ¬ Collinear ℝ ({x, y, z} : Set Plane)

private def Transversals {ι : Type*} (T : ι → Finset Plane) : Prop :=
  ∀ g : ι → Plane, (∀ i, g i ∈ T i) →
    Function.Injective g ∧ ConvexPosition (Set.range g)

private def HasPolygon {ι : Type*} (n : ℕ) (T : ι → Finset Plane) : Prop :=
  ∃ S : Finset Plane, S.card = n ∧ (∀ p ∈ S, ∃ i, p ∈ T i) ∧ ConvexPosition S

private theorem convexPosition_mono {S U : Set Plane}
    (h : ConvexPosition U) (hSU : S ⊆ U) : ConvexPosition S :=
  fun p hp hpHull =>
    h p (hSU hp) (convexHull_mono (Set.sdiff_subset_sdiff_left hSU) hpHull)

private theorem hasPolygon_of_large {ι : Type*} {n : ℕ} {T : ι → Finset Plane}
    {S : Finset Plane} (hn : n ≤ S.card) (hS : ConvexPosition S)
    (hST : ∀ p ∈ S, ∃ i, p ∈ T i) : HasPolygon n T := by
  obtain ⟨U, hUS, hU⟩ := Finset.exists_subset_card_eq hn
  exact ⟨U, hU, fun p hp => hST p (hUS hp), convexPosition_mono hS hUS⟩

private theorem transversal_subfamily {ι κ : Type*} {T : ι → Finset Plane}
    (hT : Transversals T) (hne : ∀ i, (T i).Nonempty)
    (e : κ ↪ ι) (g : κ → Plane) (hg : ∀ i, g i ∈ T (e i)) :
    Function.Injective g ∧ ConvexPosition (Set.range g) := by
  classical
  choose z hz using hne
  let f : ι → Plane := fun i =>
    if h : ∃ j : κ, e j = i then g h.choose else z i
  have hf : ∀ i, f i ∈ T i := by
    intro i
    dsimp only [f]
    split
    · rename_i h
      simpa only [h.choose_spec] using hg h.choose
    · exact hz i
  have he : ∀ j, f (e j) = g j := by
    intro j
    simp only [f, dif_pos (show ∃ l, e l = e j from ⟨j, rfl⟩)]
    congr 1
    apply e.injective
    exact Exists.choose_spec (show ∃ l, e l = e j from ⟨j, rfl⟩)
  obtain ⟨hfinj, hfconv⟩ := hT f hf
  refine ⟨fun i j hij => e.injective (hfinj (by rwa [he, he])), ?_⟩
  apply convexPosition_mono hfconv
  rintro p ⟨j, rfl⟩
  exact ⟨e j, he j⟩

private theorem transversal_pairwise_disjoint {ι : Type*} {T : ι → Finset Plane}
    (hT : Transversals T) (hne : ∀ i, (T i).Nonempty) {i j : ι} (hij : i ≠ j) :
    Disjoint (T i) (T j) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hq
  choose g hg using hne
  let f (l : ι) := if l = i ∨ l = j then p else g l
  have hf : ∀ l, f l ∈ T l := by
    intro l
    by_cases h : l = i ∨ l = j
    · rcases h with rfl | rfl
      · simpa [f] using hp
      · simpa [f] using hq
    · simpa [f, h] using hg l
  exact hij ((hT f hf).1 (by simp [f]))

private abbrev Point := ℝ × ℝ

private def det (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

private theorem det_cycle (a b c : Point) : det b c a = det a b c := by
  unfold det
  ring

private theorem det_swap (a b c : Point) : det b a c = -det a b c := by
  unfold det
  ring

private theorem det_rev (a b c : Point) : det c b a = -det a b c := by
  unfold det
  ring

private theorem det_swap_last (a b c : Point) : det a c b = -det a b c := by
  unfold det
  ring

private theorem det_self₁₂ (a b : Point) : det a a b = 0 := by simp [det]

private theorem det_self₁₃ (a b : Point) : det a b a = 0 := by simp [det]

private theorem det_self₂₃ (a b : Point) : det a b b = 0 := by simp [det, mul_comm]

private theorem det_bary (a b c p q z : Point) :
    det a b c * det p q z =
      det b c z * det p q a + det c a z * det p q b + det a b z * det p q c := by
  unfold det
  ring

private theorem det_add (a b c p : Point) :
    det a b c = det p a b + det p b c + det p c a := by
  unfold det
  ring

private theorem exists_coordinates (S : Finset Plane) :
    ∃ x y : Plane →ₗ[ℝ] ℝ, Set.InjOn x S ∧ Function.Injective (x.prod y) := by
  classical
  let slopes := (S ×ˢ S).image fun (p, q) => (q 0 - p 0) / (p 1 - q 1)
  obtain ⟨t, ht⟩ := slopes.exists_notMem
  let x : Plane →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : Plane →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint : Function.Injective (x.prod y) := by
    intro p q h
    have h₁ : p 0 + t * p 1 = q 0 + t * q 1 := congrArg Prod.fst h
    have h₂ : p 1 = q 1 := congrArg Prod.snd h
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [h₂] at h₁
      exact add_right_cancel h₁
    · exact h₂
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq h
  by_cases h₁ : p 1 = q 1
  · exact hjoint (Prod.ext h h₁)
  · have he : t = (q 0 - p 0) / (p 1 - q 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr h₁)).mpr
      change p 0 + t * p 1 = q 0 + t * q 1 at h
      linarith only [h]
    exact False.elim (ht (Finset.mem_image.mpr ⟨(p, q),
      Finset.mem_product.mpr ⟨hp, hq⟩, he.symm⟩))

private theorem det_ne_zero {x y : Plane →ₗ[ℝ] ℝ} (hxy : Function.Injective (x.prod y))
    {a b c : Plane} (hab : x a ≠ x b) (hac : x a ≠ x c)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    det ((x.prod y) a) ((x.prod y) b) ((x.prod y) c) ≠ 0 := by
  intro h
  let t := (x b - x a) / (x c - x a)
  have hden := sub_ne_zero.mpr hac.symm
  have h₁ : x b - x a = t * (x c - x a) := by dsimp [t]; rw [div_mul_cancel₀ _ hden]
  have h₂ : y b - y a = t * (y c - y a) := by
    change (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a) = 0 at h
    dsimp [t]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hden).2 (by linarith only [h])
  have ht : b - a = t • (c - a) := by
    apply hxy
    apply Prod.ext
    · change x (b - a) = x (t • (c - a))
      simpa only [map_sub, map_smul, smul_eq_mul] using h₁
    · change y (b - a) = y (t • (c - a))
      simpa only [map_sub, map_smul, smul_eq_mul] using h₂
  apply hnc
  refine (collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set Plane))).mpr ⟨c - a, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨t, sub_eq_iff_eq_add.mp ht⟩
  · exact ⟨1, by simp⟩

private noncomputable def perspective (p : Point) : Point := (p.2 / p.1, 1 / p.1)

private theorem perspective_det (a b c : Point)
    (ha : a.1 ≠ 0) (hb : b.1 ≠ 0) (hc : c.1 ≠ 0) :
    det (perspective a) (perspective b) (perspective c) * (a.1 * b.1 * c.1) =
      det a b c := by
  simp only [perspective, det]
  field_simp
  ring

private theorem det_perspective_origin (a b : Point) (ha : 0 < a.1) (hb : 0 < b.1) :
    ((perspective b).1 - (perspective a).1) * (a.1 * b.1) = det (0, 0) a b := by
  simp only [perspective, det, sub_zero]
  field_simp

private def centered (x y : Plane →ₗ[ℝ] ℝ) (a : Plane) (e : ℝ) (p : Plane) : Point :=
  (e * (x p - x a), y p - y a)

private theorem centered_det (x y : Plane →ₗ[ℝ] ℝ) (a : Plane) (e : ℝ) (p q r : Plane) :
    det (centered x y a e p) (centered x y a e q) (centered x y a e r) =
      e * det ((x.prod y) p) ((x.prod y) q) ((x.prod y) r) := by
  change det (centered x y a e p) (centered x y a e q) (centered x y a e r) =
    e * det (x p, y p) (x q, y q) (x r, y r)
  simp only [det, centered]
  ring

private noncomputable def chart (x y : Plane →ₗ[ℝ] ℝ) (a : Plane) (e : ℝ) (p : Plane) : Point :=
  perspective (centered x y a e p)

private theorem chart_det_ne {x y : Plane →ₗ[ℝ] ℝ} {a : Plane} {e : ℝ} (he : e ≠ 0)
    {p q r : Plane} (hp : 0 < (centered x y a e p).1) (hq : 0 < (centered x y a e q).1)
    (hr : 0 < (centered x y a e r).1)
    (hd : det ((x.prod y) p) ((x.prod y) q) ((x.prod y) r) ≠ 0) :
    det (chart x y a e p) (chart x y a e q) (chart x y a e r) ≠ 0 := by
  intro hz
  have h := perspective_det _ _ _ hp.ne' hq.ne' hr.ne'
  change det (chart x y a e p) (chart x y a e q) (chart x y a e r) * _ = _ at h
  rw [hz, zero_mul, centered_det] at h
  exact (mul_ne_zero he hd) h.symm

private theorem strict_halfspace_exposes {S : Set Plane} {p : Plane} (x : Plane →ₗ[ℝ] ℝ)
    (h : ∀ q ∈ S, q ≠ p → x p < x q) :
    p ∉ convexHull ℝ (S \ {p}) := by
  intro hp
  have hsub : S \ {p} ⊆ {q | x p < x q} := fun q hq => h q hq.1 hq.2
  exact lt_irrefl (x p) (convexHull_min hsub (convex_halfSpace_gt x.isLinear (x p)) hp)

private theorem chart_exposes {S : Set Plane} {p a : Plane} {e : ℝ}
    {x y : Plane →ₗ[ℝ] ℝ} (hpos : ∀ q ∈ S, 0 < (centered x y a e q).1)
    (u v : ℝ) (hs :
      ∀ q ∈ S, q ≠ p → u * (chart x y a e p).1 + v * (chart x y a e p).2 <
        u * (chart x y a e q).1 + v * (chart x y a e q).2)
    (hp : p ∈ S) : p ∉ convexHull ℝ (S \ {p}) := by
  let c := u * (chart x y a e p).1 + v * (chart x y a e p).2
  let L : Plane →ₗ[ℝ] ℝ := u • y - (c * e) • x
  apply strict_halfspace_exposes L
  intro q hq hn
  have hcross (r : Plane) (hr : 0 < (centered x y a e r).1) :
      (u * (chart x y a e r).1 + v * (chart x y a e r).2) * (centered x y a e r).1 =
        u * (y r - y a) + v := by
    change (u * ((y r - y a) / (e * (x r - x a))) + v * (1 / (e * (x r - x a)))) *
      (e * (x r - x a)) = _
    have hnen : e * (x r - x a) ≠ 0 := hr.ne'
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hnen, mul_assoc, div_mul_cancel₀ _ hnen]
    ring
  have hp' := hcross p (hpos p hp)
  change c * (e * (x p - x a)) = _ at hp'
  have hq' := mul_lt_mul_of_pos_right (hs q hq hn) (hpos q hq)
  rw [hcross q (hpos q hq)] at hq'
  change c * (e * (x q - x a)) < _ at hq'
  change u * y p - (c * e) * x p < u * y q - (c * e) * x q
  linarith only [hp', hq']

private theorem mem_hull_triangle {x y : Plane →ₗ[ℝ] ℝ}
    (hxy : Function.Injective (x.prod y)) {a b c p : Plane}
    (h : 0 < det ((x.prod y) a) ((x.prod y) b) ((x.prod y) c))
    (ha : 0 ≤ det ((x.prod y) b) ((x.prod y) c) ((x.prod y) p))
    (hb : 0 ≤ det ((x.prod y) c) ((x.prod y) a) ((x.prod y) p))
    (hc : 0 ≤ det ((x.prod y) a) ((x.prod y) b) ((x.prod y) p)) :
    p ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  let f := x.prod y
  let d := det (f a) (f b) (f c)
  let u := det (f b) (f c) (f p) / d
  let v := det (f c) (f a) (f p) / d
  let w := det (f a) (f b) (f p) / d
  have hd : 0 < d := h
  have hu : 0 ≤ u := div_nonneg ha hd.le
  have hv : 0 ≤ v := div_nonneg hb hd.le
  have hw : 0 ≤ w := div_nonneg hc hd.le
  have hs : u + v + w = 1 := by
    dsimp only [u, v, w]
    rw [← add_div, ← add_div, div_eq_iff hd.ne', one_mul]
    simp only [d, det]
    ring
  have heq : p = u • a + v • b + w • c := by
    apply hxy
    apply Prod.ext
    · change x p = x (u • a + v • b + w • c)
      simp only [map_add, map_smul, smul_eq_mul, u, v, w]
      field_simp [hd.ne']
      change x p * det (x a, y a) (x b, y b) (x c, y c) = _
      simp only [f, LinearMap.prod_apply, Function.prod, det]
      ring
    · change y p = y (u • a + v • b + w • c)
      simp only [map_add, map_smul, smul_eq_mul, u, v, w]
      field_simp [hd.ne']
      change y p * det (x a, y a) (x b, y b) (x c, y c) = _
      simp only [f, LinearMap.prod_apply, Function.prod, det]
      ring
  rw [heq]
  let z : Fin 3 → Plane := ![a, b, c]
  let weights : Fin 3 → ℝ := ![u, v, w]
  have hcm := (convex_convexHull ℝ ({a, b, c} : Set Plane)).sum_mem
    (t := Finset.univ) (w := weights) (z := z)
    (by intro i _; fin_cases i <;> assumption)
    (by simpa [weights, Fin.sum_univ_succ, add_assoc] using hs)
    (by intro i _; apply subset_convexHull ℝ; fin_cases i <;> simp [z])
  simpa [weights, z, Fin.sum_univ_succ, add_assoc] using hcm

private theorem signed_det_centered (x y : Plane →ₗ[ℝ] ℝ) (a : Plane) (e : ℝ)
    (p q r : Plane) :
    det (((e • x).prod y) p) (((e • x).prod y) q) (((e • x).prod y) r) =
      det (centered x y a e p) (centered x y a e q) (centered x y a e r) := by
  change det (e * x p, y p) (e * x q, y q) (e * x r, y r) = _
  simp only [det, centered]
  ring

private theorem chart_mixed_positive {x y : Plane →ₗ[ℝ] ℝ}
    (hxy : Function.Injective (x.prod y)) {a p q r : Plane} {e : ℝ}
    (hp : 0 < (centered x y a e p).1) (hq : 0 < (centered x y a e q).1)
    (hr : 0 < (centered x y a e r).1)
    (hpq : (chart x y a e p).1 < (chart x y a e q).1)
    (hqr : (chart x y a e q).1 < (chart x y a e r).1)
    (hout : q ∉ convexHull ℝ ({a, p, r} : Set Plane)) :
    0 < det (chart x y a e p) (chart x y a e q) (chart x y a e r) := by
  have he : e ≠ 0 := by
    intro h
    simp [centered, h] at hp
  have hinj : Function.Injective ((e • x).prod y) := by
    intro b c h
    have h₁ : e * x b = e * x c := congrArg Prod.fst h
    have h₂ : y b = y c := congrArg Prod.snd h
    exact hxy (Prod.ext (mul_left_cancel₀ he h₁) h₂)
  have ha : centered x y a e a = (0, 0) := by simp [centered]
  have hRay {b c : Plane} (hb : 0 < (centered x y a e b).1)
      (hc : 0 < (centered x y a e c).1)
      (hbc : (chart x y a e b).1 < (chart x y a e c).1) :
      0 < det (((e • x).prod y) a) (((e • x).prod y) b) (((e • x).prod y) c) := by
    rw [signed_det_centered (a := a), ha, ← det_perspective_origin _ _ hb hc]
    exact mul_pos (sub_pos.mpr hbc) (mul_pos hb hc)
  by_contra! hbad
  apply hout
  refine mem_hull_triangle hinj (hRay hp hr (hpq.trans hqr)) ?_ ?_ (hRay hp hq hpq).le
  · rw [det_swap_last, signed_det_centered (a := a), ← perspective_det _ _ _ hp.ne' hq.ne' hr.ne']
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hbad (by positivity))
  · rw [← det_cycle (((e • x).prod y) r) (((e • x).prod y) a) (((e • x).prod y) q)]
    exact (hRay hq hr hqr).le

private theorem exists_quantile {α : Type*} [LinearOrder α] (S : Finset α) {s : ℕ}
    (hs : 0 < s) (hS : s ≤ S.card) :
    ∃ b ∈ S, (S.filter (· ≤ b)).card = s := by
  classical
  let E := S.orderEmbOfFin rfl
  let j : Fin S.card := ⟨s - 1, by omega⟩
  refine ⟨E j, S.orderEmbOfFin_mem rfl j, ?_⟩
  have h : S.filter (· ≤ E j) = (Finset.Iic j).image E := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpS, hpj⟩ := Finset.mem_filter.mp hp
      let i := (S.orderIsoOfFin rfl).symm ⟨p, hpS⟩
      have hi : E i = p := by simp [E, i, ← Finset.coe_orderIsoOfFin_apply]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Iic.mpr (E.le_iff_le.mp (hi ▸ hpj)), hi⟩
    · rintro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl i,
        E.monotone (Finset.mem_Iic.mp hi)⟩
  rw [h, Finset.card_image_of_injective _ E.injective, Fin.card_Iic]
  dsimp [j]
  omega

private theorem separated_subfamilies {ι α : Type*} [LinearOrder α] {s : ℕ} (hs : 0 < s)
    (r : ℕ) (I : Finset ι) (T : ι → Finset α)
    (hI : r ≤ I.card) (hT : ∀ i ∈ I, r * s ≤ (T i).card) :
    ∃ e : Fin r ↪ ι, ∃ W : Fin r → Finset α,
      (∀ j, e j ∈ I ∧ W j ⊆ T (e j) ∧ (W j).card = s) ∧
      ∀ i j, i < j → ∀ p ∈ W i, ∀ q ∈ W j, p < q := by
  classical
  induction r generalizing I T with
  | zero =>
    exact ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, Fin.elim0, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  | succ r ih =>
    have hR : ∀ i : I, s ≤ (T i).card := by
      intro i
      have hh := hT i i.property
      rw [Nat.succ_mul] at hh
      omega
    have hQ : ∀ i : I, ∃ b ∈ T i, ((T i).filter (· ≤ b)).card = s :=
      fun i => exists_quantile (T i) hs (hR i)
    choose b hb hbc using hQ
    let cuts := Finset.univ.image b
    have hcuts : cuts.Nonempty := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
      exact ⟨b ⟨i, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (cuts.min'_mem hcuts)
    let z := b i
    let V (j : ι) := (T j).filter (z < ·)
    have hV : ∀ j ∈ I.erase i.val, r * s ≤ (V j).card := by
      intro j hj
      let jj : I := ⟨j, Finset.mem_of_mem_erase hj⟩
      have hzj : z ≤ b jj := by
        change b i ≤ b jj
        rw [hi]
        exact cuts.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      have hsub : (T j).filter (· ≤ z) ⊆ (T j).filter (· ≤ b jj) := by
        intro p hp
        obtain ⟨hpT, hpz⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hpT, hpz.trans hzj⟩
      have hcard : ((T j).filter (· ≤ z)).card ≤ s :=
        (Finset.card_le_card hsub).trans (hbc jj).le
      have hsplit := Finset.card_filter_add_card_filter_not (s := T j) (p := (z < ·))
      simp only [not_lt] at hsplit
      have hfull := hT j jj.property
      rw [Nat.succ_mul] at hfull
      change (V j).card + _ = _ at hsplit
      omega
    have hI' : r ≤ (I.erase i.val).card := by
      rw [Finset.card_erase_of_mem i.property]
      omega
    obtain ⟨e, W, hW, hord⟩ := ih _ V hI' hV
    let E : Fin (r + 1) → ι := Fin.cases i e
    let U : Fin (r + 1) → Finset α := Fin.cases ((T i).filter (· ≤ z)) W
    refine ⟨⟨E, ?_⟩, U, ?_, ?_⟩
    · intro a c he
      rcases a.eq_zero_or_eq_succ with rfl | ⟨a, rfl⟩ <;>
        rcases c.eq_zero_or_eq_succ with rfl | ⟨c, rfl⟩
      · rfl
      · exact ((Finset.ne_of_mem_erase (hW c).1) he.symm).elim
      · exact ((Finset.ne_of_mem_erase (hW a).1) he).elim
      · exact congrArg Fin.succ (e.injective he)
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · exact ⟨i.property, Finset.filter_subset _ _, hbc i⟩
      · exact ⟨Finset.mem_of_mem_erase (hW l).1,
          (hW l).2.1.trans (Finset.filter_subset _ _), (hW l).2.2⟩
    · intro a c hac p hp q hq
      obtain ⟨c, rfl⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hac))
      rcases a.eq_zero_or_eq_succ with rfl | ⟨a, rfl⟩
      · exact ((Finset.mem_filter.mp hp).2).trans_lt (Finset.mem_filter.mp ((hW c).2.1 hq)).2
      · exact hord a c (by simpa using hac) p hp q hq

private def familyUnion {ι α : Type*} [Fintype ι] [DecidableEq α]
    (T : ι → Finset α) : Finset α := Finset.univ.biUnion T

private theorem mem_familyUnion {ι α : Type*} [Fintype ι] [DecidableEq α]
    {T : ι → Finset α} {p : α} : p ∈ familyUnion T ↔ ∃ i, p ∈ T i := by
  simp [familyUnion]

private theorem transversal_hull3 {ι : Type*} {T : ι → Finset Plane}
    (htrans : Transversals T) (hne : ∀ i, (T i).Nonempty)
    {i₀ i₁ i₂ i₃ : ι} (h₀₁ : i₀ ≠ i₁) (h₀₂ : i₀ ≠ i₂) (h₀₃ : i₀ ≠ i₃)
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {a p q r : Plane} (ha : a ∈ T i₀) (hp : p ∈ T i₁)
    (hq : q ∈ T i₂) (hr : r ∈ T i₃) :
    q ∉ convexHull ℝ ({a, p, r} : Set Plane) := by
  classical
  choose g hg using hne
  let f := Function.update (Function.update (Function.update (Function.update g i₀ a) i₁ p) i₂ q) i₃ r
  have upd {j : ι} {z : Plane} (hz : z ∈ T j) {f₀ : ι → Plane} (hf₀ : ∀ i, f₀ i ∈ T i) :
      ∀ i, Function.update f₀ j z i ∈ T i := by
    intro i
    by_cases h : i = j
    · subst i; simpa using hz
    · simpa [Function.update_of_ne h] using hf₀ i
  obtain ⟨hinj, hcv⟩ := htrans f (upd hr (upd hq (upd hp (upd ha hg))))
  have hfa : f i₀ = a := by simp [f, h₀₁, h₀₂, h₀₃]
  have hfp : f i₁ = p := by simp [f, h₁₂, h₁₃]
  have hfq : f i₂ = q := by simp [f, h₂₃]
  have hfr : f i₃ = r := by simp [f]
  intro h
  apply hcv q ⟨i₂, hfq⟩
  apply convexHull_mono _ h
  have mem (j : ι) (hj : j ≠ i₂) : f j ∈ Set.range f \ {q} :=
    ⟨⟨j, rfl⟩, fun he => hj (hinj (he.trans hfq.symm))⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hfa ▸ mem i₀ h₀₂
  · exact hfp ▸ mem i₁ h₁₂
  · exact hfr ▸ mem i₃ h₂₃.symm

private theorem chart_key_ne {x y : Plane →ₗ[ℝ] ℝ} {a p q : Plane} {e : ℝ}
    (he : e ≠ 0) (hp : 0 < (centered x y a e p).1) (hq : 0 < (centered x y a e q).1)
    (hdet : det ((x.prod y) a) ((x.prod y) p) ((x.prod y) q) ≠ 0) :
    (chart x y a e p).1 ≠ (chart x y a e q).1 := by
  intro h
  have hz := det_perspective_origin _ _ hp hq
  change ((chart x y a e q).1 - (chart x y a e p).1) * _ = _ at hz
  have ha : centered x y a e a = (0, 0) := by simp [centered]
  rw [h, sub_self, zero_mul, ← ha, centered_det] at hz
  exact (mul_ne_zero he hdet) hz.symm

private theorem finset_pullback {α β : Type*} [DecidableEq β] (f : α → β)
    (S : Finset α) (U : Finset β) (hU : U ⊆ S.image f) :
    ∃ V ⊆ S, V.image f = U := by
  refine ⟨S.filter (fun p => f p ∈ U), Finset.filter_subset _ _, ?_⟩
  ext q
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hp).2
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hU h)
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, rfl⟩

private theorem majority_side {ι : Type*} [Fintype ι] {T : ι → Finset Plane}
    (i₀ : ι) (a : Plane) (x : Plane →ₗ[ℝ] ℝ) {N r : ℕ}
    (hI : 2 * r ≤ Fintype.card ι - 1)
    (hN : ∀ i, N ≤ (T i).card) (hx : ∀ i ≠ i₀, ∀ p ∈ T i, x p ≠ x a) :
    ∃ e : ℝ, e ≠ 0 ∧ ∃ I : Finset ι, r ≤ I.card ∧ i₀ ∉ I ∧
      ∀ i ∈ I, N ≤ 2 * ((T i).filter (fun p => 0 < e * (x p - x a))).card := by
  classical
  let J := Finset.univ.erase i₀
  let P (i : ι) := (T i).filter (fun p => 0 < x p - x a)
  let I := J.filter (fun i => N ≤ 2 * (P i).card)
  by_cases h : r ≤ I.card
  · refine ⟨1, one_ne_zero, I, h, ?_, ?_⟩
    · exact fun hmem => Finset.notMem_erase i₀ _ (Finset.mem_filter.mp hmem).1
    · intro j hj
      simpa [P] using (Finset.mem_filter.mp hj).2
  · let K := J.filter (fun i => ¬ N ≤ 2 * (P i).card)
    have hsplit : I.card + K.card = J.card := Finset.card_filter_add_card_filter_not (s := J) _
    have hJ : J.card = Fintype.card ι - 1 := by simp [J]
    refine ⟨-1, by norm_num, K, by omega, ?_, ?_⟩
    · exact fun hmem => Finset.notMem_erase i₀ _ (Finset.mem_filter.mp hmem).1
    · intro j hj
      obtain ⟨hjJ, hjbad⟩ := Finset.mem_filter.mp hj
      have hjne : j ≠ i₀ := Finset.ne_of_mem_erase hjJ
      have heq : (T j).filter (fun p => 0 < (-1 : ℝ) * (x p - x a)) =
          (T j).filter (fun p => ¬ 0 < x p - x a) := by
        ext p
        by_cases hp : p ∈ T j
        · have hh := sub_ne_zero.mpr (hx j hjne p hp)
          simp only [Finset.mem_filter, hp, true_and, neg_mul, one_mul, neg_pos, not_lt]
          constructor <;> intro w <;> linarith [(lt_or_gt_of_ne hh).resolve_right fun h => by linarith]
        · simp [hp]
      rw [heq]
      have hsum := Finset.card_filter_add_card_filter_not (s := T j) (fun p => 0 < x p - x a)
      change (P j).card + _ = _ at hsum
      have hcard := hN j
      omega

private def Exposed (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∃ u v : ℝ, ∀ q ∈ S, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

private def Ordered {r : ℕ} (W : Fin r → Finset Point) : Prop :=
  (∀ i j, i < j → ∀ p ∈ W i, ∀ q ∈ W j, p.1 < q.1) ∧
  (∀ i j l, i < j → j < l → ∀ p ∈ W i, ∀ q ∈ W j, ∀ z ∈ W l, 0 < det p q z) ∧
  (∀ p ∈ familyUnion W, ∀ q ∈ familyUnion W, ∀ z ∈ familyUnion W,
    p ≠ q → q ≠ z → p ≠ z → det p q z ≠ 0)

private theorem ordered_of_transversals {k r s : ℕ} (hr : 2 * r + 1 ≤ k) (hs : 0 < s)
    {T : Fin k → Finset Plane} (hgen : General T) (htrans : Transversals T)
    (hne : ∀ i, (T i).Nonempty) (hlarge : ∀ i, k * s ≤ (T i).card) :
    ∃ P : Fin r → Finset Point, Ordered P ∧ (∀ i, (P i).card = s) ∧
      ∀ Z : Finset Point, Z ⊆ familyUnion P → Exposed Z → HasPolygon Z.card T := by
  classical
  let i₀ : Fin k := ⟨0, by omega⟩
  obtain ⟨a, ha⟩ := hne i₀
  let U := familyUnion T
  obtain ⟨x, y, hx, hxy⟩ := exists_coordinates U
  have haU : a ∈ U := mem_familyUnion.mpr ⟨i₀, ha⟩
  have hxA : ∀ i ≠ i₀, ∀ p ∈ T i, x p ≠ x a := by
    intro i hi p hp he
    have hpU : p ∈ U := mem_familyUnion.mpr ⟨i, hp⟩
    have hpa := hx hpU haU he
    exact Finset.disjoint_left.mp (transversal_pairwise_disjoint htrans hne hi) hp (hpa ▸ ha)
  obtain ⟨d, hd, I, hI, hia, hiN⟩ :=
    majority_side i₀ a x (by simpa using (show 2 * r ≤ k - 1 by omega)) hlarge hxA
  let V (i : Fin k) := (T i).filter fun p => 0 < d * (x p - x a)
  let G := chart x y a d
  let key (p : Plane) := (G p).1
  let UV := familyUnion V
  have hVU : UV ⊆ U := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_familyUnion.mp hp
    exact mem_familyUnion.mpr ⟨i, (Finset.mem_filter.mp hi).1⟩
  have hvpos : ∀ p ∈ UV, 0 < (centered x y a d p).1 := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_familyUnion.mp hp
    exact (Finset.mem_filter.mp hi).2
  have hdet {p q z : Plane} (hp : p ∈ U) (hq : q ∈ U) (hz : z ∈ U)
      (hpq : p ≠ q) (hqz : q ≠ z) (hpz : p ≠ z) :
      det ((x.prod y) p) ((x.prod y) q) ((x.prod y) z) ≠ 0 := by
    obtain ⟨i, hi⟩ := mem_familyUnion.mp hp
    obtain ⟨j, hj⟩ := mem_familyUnion.mp hq
    obtain ⟨l, hl⟩ := mem_familyUnion.mp hz
    exact det_ne_zero hxy (fun h => hpq (hx hp hq h)) (fun h => hpz (hx hp hz h))
      (hgen i j l p hi q hj z hl hpq hqz hpz)
  have hane : ∀ p ∈ UV, a ≠ p := by
    rintro p hp rfl
    simpa [centered] using hvpos a hp
  have hkey : Set.InjOn key (UV : Set Plane) := by
    intro p hp q hq eq
    by_contra hne'
    exact chart_key_ne hd (hvpos p hp) (hvpos q hq)
      (hdet haU (hVU hp) (hVU hq) (hane p hp) hne' (hane q hq)) eq
  have hv_mem {i : Fin k} {p : Plane} (hp : p ∈ V i) : p ∈ UV := mem_familyUnion.mpr ⟨i, hp⟩
  have hK : ∀ i ∈ I, r * s ≤ ((V i).image key).card := by
    intro i hi
    rw [Finset.card_image_of_injOn (hkey.mono (fun _ => hv_mem))]
    have h₁ := hiN i hi
    have h₂ := Nat.mul_le_mul_right s (show 2 * r ≤ k by omega)
    rw [Nat.mul_assoc] at h₂
    change k * s ≤ 2 * (V i).card at h₁
    omega
  obtain ⟨j, W, hW, horder⟩ :=
    separated_subfamilies hs r I (fun i => (V i).image key) hI hK
  have hpull : ∀ i, ∃ A ⊆ V (j i), A.image key = W i :=
    fun i => finset_pullback key _ _ (hW i).2.1
  choose A hA hAW using hpull
  let P (i : Fin r) := (A i).image G
  have hAUV {i : Fin r} {p : Plane} (hp : p ∈ A i) : p ∈ UV := hv_mem (hA i hp)
  have hinjG : Set.InjOn G (UV : Set Plane) := fun _ hp _ hq he =>
    hkey hp hq (congrArg Prod.fst he)
  have hsubP : familyUnion P ⊆ UV.image G := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_familyUnion.mp hp
    obtain ⟨p, hp_, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image_of_mem _ (hAUV hp_)
  have hsort {i j : Fin r} (hij : i < j) {p q : Plane} (hp : p ∈ A i) (hq : q ∈ A j) :
      (G p).1 < (G q).1 := by
    apply horder i j hij
    · rw [← hAW i]; exact Finset.mem_image_of_mem _ hp
    · rw [← hAW j]; exact Finset.mem_image_of_mem _ hq
  refine ⟨P, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hij p hp q hq
    obtain ⟨p, hp_, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq_, rfl⟩ := Finset.mem_image.mp hq
    exact hsort hij hp_ hq_
  · intro i l b hil hlb p hp q hq z hz
    obtain ⟨p, hp_, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq_, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz_, rfl⟩ := Finset.mem_image.mp hz
    have hidx (i : Fin r) : i₀ ≠ j i := fun h => hia (h.symm ▸ (hW i).1)
    exact chart_mixed_positive hxy (hvpos p (hAUV hp_)) (hvpos q (hAUV hq_)) (hvpos z (hAUV hz_))
      (hsort hil hp_ hq_) (hsort hlb hq_ hz_)
      (transversal_hull3 htrans hne (hidx i) (hidx l) (hidx b) (j.injective.ne hil.ne)
        (j.injective.ne (hil.trans hlb).ne) (j.injective.ne hlb.ne) ha
        (Finset.mem_filter.mp (hA i hp_)).1 (Finset.mem_filter.mp (hA l hq_)).1
        (Finset.mem_filter.mp (hA b hz_)).1)
  · intro p hp q hq z hz hpq hqz hpz
    obtain ⟨p, hp_, rfl⟩ := Finset.mem_image.mp (hsubP hp)
    obtain ⟨q, hq_, rfl⟩ := Finset.mem_image.mp (hsubP hq)
    obtain ⟨z, hz_, rfl⟩ := Finset.mem_image.mp (hsubP hz)
    exact chart_det_ne hd (hvpos p hp_) (hvpos q hq_) (hvpos z hz_)
      (hdet (hVU hp_) (hVU hq_) (hVU hz_) (fun h => hpq (congrArg G h))
        (fun h => hqz (congrArg G h)) (fun h => hpz (congrArg G h)))
  · intro i
    have hAn := Finset.card_image_of_injOn (hkey.mono (fun _ hp => hAUV (i := i) hp))
    rw [hAW i, (hW i).2.2] at hAn
    change ((A i).image G).card = _
    rw [Finset.card_image_of_injOn (hinjG.mono (fun _ hp => hAUV hp)), ← hAn]
  · intro Z hZ hcv
    obtain ⟨Y, hYV, hYZ⟩ := finset_pullback G UV Z (hZ.trans hsubP)
    have hYcard : Y.card = Z.card := by
      rw [← hYZ, Finset.card_image_of_injOn (hinjG.mono hYV)]
    refine ⟨Y, hYcard, fun p hp => mem_familyUnion.mp (hVU (hYV hp)), ?_⟩
    intro p hp
    have hmem (q : Plane) (hq : q ∈ Y) : G q ∈ Z := hYZ ▸ Finset.mem_image_of_mem _ hq
    obtain ⟨u, v, huv⟩ := hcv (G p) (hmem p hp)
    exact chart_exposes (fun q hq => hvpos q (hYV hq)) u v
      (fun q hq hqp => huv (G q) (hmem q hq) (fun he => hqp (hinjG (hYV hq) (hYV hp) he))) hp

private theorem positive_det_of_product {t d : ℝ} (ht : 0 < t)
    (h : 0 < t * d) : 0 < d := pos_of_mul_pos_right h ht.le

private theorem negative_det_of_product {t d : ℝ} (ht : 0 < t)
    (h : t * d < 0) : d < 0 := neg_of_mul_neg_right h ht.le

private theorem vertical_endpoints {a b c d p q : Point}
    (hbase : 0 < det a b q)
    (hc₁ : det b q c < 0) (hc₂ : 0 < det q a c)
    (hd₁ : 0 < det b q d) (hd₂ : det q a d < 0)
    (ha : 0 < det p q a) (hb : det p q b < 0) :
    det p q c < 0 ∧ 0 < det p q d := by
  constructor
  · apply negative_det_of_product hbase
    rw [det_bary a b q p q c, det_self₂₃, mul_zero, add_zero]
    exact add_neg (mul_neg_of_neg_of_pos hc₁ ha) (mul_neg_of_pos_of_neg hc₂ hb)
  · apply positive_det_of_product hbase
    rw [det_bary a b q p q d, det_self₂₃, mul_zero, add_zero]
    exact add_pos (mul_pos hd₁ ha) (mul_pos_of_neg_of_neg hd₂ hb)

private theorem vertical_next_side {a c d p q z : Point}
    (hframe : 0 < det c d a)
    (h₁ : det d a z < 0) (h₂ : 0 < det a c z) (h₃ : 0 < det c d z)
    (hc : det p q c < 0) (hd : 0 < det p q d) (ha : 0 < det p q a) :
    0 < det p q z := by
  apply positive_det_of_product hframe
  rw [det_bary c d a p q z]
  exact add_pos (add_pos (mul_pos_of_neg_of_neg h₁ hc) (mul_pos h₂ hd)) (mul_pos h₃ ha)

private theorem vertical_prev_side {b c d p q z : Point}
    (hframe : 0 < det b c d)
    (h₁ : 0 < det c d z) (h₂ : 0 < det d b z) (h₃ : det b c z < 0)
    (hb : det p q b < 0) (hc : det p q c < 0) (hd : 0 < det p q d) :
    det p q z < 0 := by
  apply negative_det_of_product hframe
  rw [det_bary b c d p q z]
  exact add_neg (add_neg (mul_neg_of_pos_of_neg h₁ hb) (mul_neg_of_pos_of_neg h₂ hc))
    (mul_neg_of_neg_of_pos h₃ hd)

private theorem horizontal_far_side {a b p q z : Point}
    (hframe : 0 < det a b p) (h₁ : 0 < det b p z) (h₂ : 0 < det p a z)
    (ha : det p q a < 0) (hb : det p q b < 0) : det p q z < 0 := by
  apply negative_det_of_product hframe
  rw [det_bary a b p p q z, det_self₁₃, mul_zero, add_zero]
  exact add_neg (mul_neg_of_pos_of_neg h₁ ha) (mul_neg_of_pos_of_neg h₂ hb)

private theorem ordered_cyclic {r : ℕ} {P : Fin r → Finset Point} (hP : Ordered P)
    {i j l : Fin r} {p q z : Point} (hp : p ∈ P i) (hq : q ∈ P j) (hz : z ∈ P l)
    (h : (i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) : 0 < det p q z := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hP.2.1 i j l h₁ h₂ p hp q hq z hz
  · rw [← det_cycle]; exact hP.2.1 j l i h₁ h₂ q hq z hz p hp
  · rw [det_cycle]; exact hP.2.1 l i j h₁ h₂ z hz p hp q hq

private theorem ordered_anticyclic {r : ℕ} {P : Fin r → Finset Point} (hP : Ordered P)
    {i j l : Fin r} {p q z : Point} (hp : p ∈ P i) (hq : q ∈ P j) (hz : z ∈ P l)
    (h : (j < i ∧ i < l) ∨ (i < l ∧ l < j) ∨ (l < j ∧ j < i)) : det p q z < 0 := by
  have hp := ordered_cyclic hP hq hp hz h
  rw [det_swap] at hp
  exact neg_pos.mp hp

private def TripleChain {α : Type*} (f : α → ℝ) (R : α → α → α → Prop) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, f a < f b → f b < f c → R a b c

private abbrev Turning (f : Point → ℝ) (σ : ℝ) (S : Finset Point) : Prop :=
  TripleChain f (fun a b c => 0 < σ * det a b c) S

private theorem positive_lower_bound {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 < f x) : ∃ δ > 0, ∀ x ∈ S, δ ≤ f x := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst S
    exact ⟨1, zero_lt_one, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := S.exists_min_image f h
    exact ⟨f x, hf x hx, hmin⟩

private theorem expose_from_edge {S : Finset Point} {p q : Point} (hpq : p ≠ q)
    (σ : ℝ) (h : ∀ z ∈ S, z ≠ p → z ≠ q → 0 < σ * det p q z) :
    ∃ u v : ℝ, ∀ z ∈ S, z ≠ p → u * p.1 + v * p.2 < u * z.1 + v * z.2 := by
  classical
  let a := q.1 - p.1
  let b := q.2 - p.2
  let D (z : Point) := a * (z.1 - p.1) + b * (z.2 - p.2)
  let U := (S.erase p).erase q
  obtain ⟨ε, hε, hδ⟩ := positive_lower_bound U (fun z => σ * det p q z / (1 + |D z|)) (by
    intro z hz
    have hz' := Finset.mem_of_mem_erase hz
    have hzp : z ≠ p := Finset.ne_of_mem_erase hz'
    have hzq : z ≠ q := Finset.ne_of_mem_erase hz
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz'
    exact div_pos (h z hzS hzp hzq) (by positivity))
  refine ⟨-σ * b + ε * a, σ * a + ε * b, ?_⟩
  intro z hz hzp
  have hbound : 0 < σ * det p q z + ε * D z := by
    by_cases hzq : z = q
    · subst z
      rw [det_self₂₃, mul_zero, zero_add]
      apply mul_pos hε
      have hn : a ≠ 0 ∨ b ≠ 0 := by
        by_contra! he
        exact hpq (Prod.ext (sub_eq_zero.mp he.1).symm (sub_eq_zero.mp he.2).symm)
      change 0 < a * a + b * b
      rcases hn with hn | hn
      · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr hn) (mul_self_nonneg b)
      · exact add_pos_of_nonneg_of_pos (mul_self_nonneg a) (mul_self_pos.mpr hn)
    · have hmem : z ∈ U := Finset.mem_erase.mpr ⟨hzq, Finset.mem_erase.mpr ⟨hzp, hz⟩⟩
      have H := (le_div_iff₀ (show 0 < 1 + |D z| by positivity)).mp (hδ z hmem)
      have L := mul_le_mul_of_nonneg_left (neg_abs_le (D z)) hε.le
      linarith only [H, L, hε]
  have heq :
      (-σ * b + ε * a) * z.1 + (σ * a + ε * b) * z.2 -
        ((-σ * b + ε * a) * p.1 + (σ * a + ε * b) * p.2) = σ * det p q z + ε * D z := by
    simp only [a, b, D, det]
    ring
  exact sub_pos.mp (heq.symm ▸ hbound)

private theorem top_pair {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : Set.InjOn f S) (hS : 2 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, f a < f b ∧ ∀ z ∈ S, z ≠ b → f z ≤ f a := by
  classical
  obtain ⟨b, hb, hbmax⟩ := S.exists_max_image f (Finset.card_pos.mp (by omega))
  have hne : (S.erase b).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hb]; omega)
  obtain ⟨a, ha, hamax⟩ := (S.erase b).exists_max_image f hne
  have haS := Finset.mem_of_mem_erase ha
  have hab := lt_of_le_of_ne (hbmax a haS) (fun h => Finset.ne_of_mem_erase ha (hf haS hb h))
  exact ⟨a, haS, b, hb, hab, fun z hz hzb => hamax z (Finset.mem_erase.mpr ⟨hzb, hz⟩)⟩

private theorem adjacent_pair {α : Type*} {S : Finset α} {f : α → ℝ}
    (hf : Set.InjOn f S) (hS : 2 ≤ S.card) {p : α} (hp : p ∈ S) :
    ∃ a ∈ S, ∃ b ∈ S, (p = a ∨ p = b) ∧ f a < f b ∧
      ∀ z ∈ S, z ≠ a → z ≠ b → f z < f a ∨ f b < f z := by
  classical
  let H := S.filter (fun z => f p < f z)
  by_cases h : H.Nonempty
  · obtain ⟨q, hq, hmin⟩ := H.exists_min_image f h
    obtain ⟨hqS, hpq⟩ := Finset.mem_filter.mp hq
    refine ⟨p, hp, q, hqS, Or.inl rfl, hpq, ?_⟩
    intro z hz hzp hzq
    rcases lt_or_gt_of_ne (fun he => hzp (hf hz hp he)) with hzp' | hpz'
    · exact Or.inl hzp'
    · exact Or.inr (lt_of_le_of_ne (hmin z (Finset.mem_filter.mpr ⟨hz, hpz'⟩))
        (fun he => hzq (hf hz hqS he.symm)))
  · obtain ⟨a, ha, b, hb, hab, hmax⟩ := top_pair S f hf hS
    have hpb : p = b := by
      by_contra hpne
      exact h ⟨b, Finset.mem_filter.mpr ⟨hb, (hmax p hp hpne).trans_lt hab⟩⟩
    exact ⟨a, ha, b, hb, Or.inr hpb, hab, fun z hz hza hzb =>
      Or.inl (lt_of_le_of_ne (hmax z hz hzb) (fun he => hza (hf hz ha he)))⟩

private theorem expose_chain {A S : Finset Point} (_hAS : A ⊆ S)
    {f : Point → ℝ} (hf : Set.InjOn f A) (hA : 2 ≤ A.card) (σ : ℝ)
    (hturn : Turning f σ A)
    (hout : ∀ p ∈ A, ∀ q ∈ A, f p < f q →
      ∀ z ∈ S, z ∉ A → 0 < σ * det p q z)
    {p : Point} (hp : p ∈ A) :
    ∃ u v : ℝ, ∀ q ∈ S, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2 := by
  obtain ⟨a, ha, b, hb, hpab, hab, hbetween⟩ := adjacent_pair hf hA hp
  have habne : a ≠ b := fun h => hab.ne (congrArg f h)
  have h : ∀ z ∈ S, z ≠ a → z ≠ b → 0 < σ * det a b z := by
    intro z hz hza hzb
    by_cases hzA : z ∈ A
    · rcases hbetween z hzA hza hzb with hza' | hzb'
      · rw [det_cycle z a b]; exact hturn z hzA a ha b hb hza' hab
      · exact hturn a ha b hb z hzA hab hzb'
    · exact hout a ha b hb hab z hz hzA
  rcases hpab with rfl | rfl
  · exact expose_from_edge habne σ h
  · apply expose_from_edge habne.symm (-σ)
    intro z hz hzb hza
    rw [det_swap, neg_mul_neg]
    exact h z hz hza hzb

private theorem exposed_mono {A S : Finset Point} (h : Exposed S) (hAS : A ⊆ S) : Exposed A := by
  intro p hp
  obtain ⟨u, v, hv⟩ := h p (hAS hp)
  exact ⟨u, v, fun q hq hqp => hv q (hAS hq) hqp⟩

private def TripleTransitive {α : Type*} (f : α → ℝ) (R : α → α → α → Prop) : Prop :=
  ∀ ⦃a b c d⦄, f a < f b → f b < f c → f c < f d →
    R a b c → R b c d → R a b d ∧ R a c d

private theorem tripleChain_mono {α : Type*} {f : α → ℝ} {R : α → α → α → Prop}
    {S U : Finset α} (h : TripleChain f R U) (hSU : S ⊆ U) : TripleChain f R S :=
  fun a ha b hb c hc => h a (hSU ha) b (hSU hb) c (hSU hc)

private theorem tripleChain_append {α : Type*} [DecidableEq α] {f : α → ℝ}
    {R : α → α → α → Prop} (ht : TripleTransitive f R) {S : Finset α}
    (hinj : Set.InjOn f S) (hS : TripleChain f R S)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hab : f a < f b) (hbc : f b < f c)
    (hmax : ∀ z ∈ S, z ≠ b → f z ≤ f a) (hR : R a b c) :
    TripleChain f R (insert c S) := by
  have lemax : ∀ z ∈ S, f z ≤ f b := by
    intro z hz
    by_cases hzb : z = b
    · simp [hzb]
    · exact (hmax z hz hzb).trans hab.le
  have leins : ∀ z ∈ insert c S, f z ≤ f c := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact (lemax z hz).trans hbc.le
  have hlast : ∀ z ∈ S, f z < f b → R z b c := by
    intro z hz hzb
    have hza := hmax z hz (fun e => hzb.ne (congrArg f e))
    rcases hza.eq_or_lt with h | h
    · rwa [hinj hz ha h]
    · exact (ht h hab hbc (hS z hz a ha b hb h hab) hR).2
  intro x hx y hy z hz hxy hyz
  have hxS := (Finset.mem_insert.mp hx).resolve_left (fun h =>
    ((leins y hy).not_gt) (by simpa [h] using hxy))
  have hyS := (Finset.mem_insert.mp hy).resolve_left (fun h =>
    ((leins z hz).not_gt) (by simpa [h] using hyz))
  rcases Finset.mem_insert.mp hz with rfl | hzS
  · rcases (lemax y hyS).eq_or_lt with hy' | hy'
    · rw [hinj hyS hb hy'] at hxy ⊢
      exact hlast x hxS hxy
    · exact (ht hxy hy' hbc (hS x hxS y hyS b hb hxy hy') (hlast y hyS hy')).1
  · exact hS x hxS y hyS z hzS hxy hyz

private theorem tripleChain_flip {α : Type*} {f : α → ℝ} {R : α → α → α → Prop}
    {S : Finset α} :
    TripleChain (fun p => -f p) (fun a b c => R c b a) S ↔ TripleChain f R S := by
  constructor <;> intro h a ha b hb c hc hab hbc
  · exact h c hc b hb a ha (by simp; exact hbc) (by simp; exact hab)
  · exact h c hc b hb a ha (by simpa using hbc) (by simpa using hab)

private theorem tripleChain_prepend {α : Type*} [DecidableEq α] {f : α → ℝ}
    {R : α → α → α → Prop} (ht : TripleTransitive f R) {S : Finset α}
    (hinj : Set.InjOn f S) (hS : TripleChain f R S)
    {a b c : α} (hb : b ∈ S) (hc : c ∈ S) (hab : f a < f b) (hbc : f b < f c)
    (hmin : ∀ z ∈ S, z ≠ b → f c ≤ f z) (hR : R a b c) :
    TripleChain f R (insert a S) := by
  apply (tripleChain_flip (f := f) (R := R) (S := insert a S)).mp
  apply tripleChain_append (a := c) (b := b) (c := a) _ (fun _ hp _ hq h => hinj hp hq (neg_injective h))
    (tripleChain_flip.mpr hS) hc hb (by simpa) (by simpa) (fun z hz hzb => by simpa using hmin z hz hzb) hR
  intro i j k l hij hjk hkl h₁ h₂
  have h := ht (a := l) (b := k) (c := j) (d := i)
    (by simpa using hkl) (by simpa using hjk) (by simpa using hij) h₂ h₁
  exact ⟨h.2, h.1⟩

private theorem card_le_one_of_chain_bound {α : Type*} {f : α → ℝ}
    {R : α → α → α → Prop} {S : Finset α}
    (h : ∀ A ⊆ S, TripleChain f R A → A.card ≤ 1) : S.card ≤ 1 := by
  classical
  by_contra! h'
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h'
  have hsub : ({a, b} : Finset α) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact ha
    · exact (Finset.mem_singleton.mp h).symm ▸ hb
  have hc : TripleChain f R ({a, b} : Finset α) := by
    intro x hx y hy z hz hxy hyz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      exact (lt_irrefl _ (by first | exact hxy | exact hyz | exact hxy.trans hyz)).elim
  have hcard := h _ hsub hc
  rw [Finset.card_pair hab] at hcard
  omega

private theorem cups_bound {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : Set.InjOn f S) (R Q : α → α → α → Prop)
    (hR : TripleTransitive f R) (hQ : TripleTransitive f Q)
    (hcover : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, f a < f b → f b < f c → R a b c ∨ Q a b c)
    (u v : ℕ) (hu : ∀ A ⊆ S, TripleChain f R A → A.card ≤ u + 1)
    (hv : ∀ A ⊆ S, TripleChain f Q A → A.card ≤ v + 1) :
    S.card ≤ (u + v).choose u := by
  classical
  have main : ∀ d u v : ℕ, u + v = d → ∀ U ⊆ S,
      (∀ A ⊆ U, TripleChain f R A → A.card ≤ u + 1) →
      (∀ A ⊆ U, TripleChain f Q A → A.card ≤ v + 1) → U.card ≤ (u + v).choose u := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u v huv U hUS hur hvr
      by_cases hu0 : u = 0
      · subst u
        simpa using card_le_one_of_chain_bound hur
      by_cases hv0 : v = 0
      · subst v
        simpa using card_le_one_of_chain_bound hvr
      let isEnd (b : α) := ∃ A ⊆ U, u + 1 ≤ A.card ∧ TripleChain f R A ∧
        b ∈ A ∧ ∀ a ∈ A, f a ≤ f b
      let T := U.filter isEnd
      let V := U.filter (fun b => ¬ isEnd b)
      have hTU : T ⊆ U := Finset.filter_subset _ _
      have hVU : V ⊆ U := Finset.filter_subset _ _
      have hvr' : ∀ B ⊆ T, TripleChain f Q B → B.card ≤ (v - 1) + 1 := by
        intro B hBT hB
        by_contra! hBbig
        have hBU := hBT.trans hTU
        have hinjB := hf.mono (Finset.coe_subset.mpr (hBU.trans hUS))
        obtain ⟨c, hc, b, hb, hcb, hmin⟩ :=
          top_pair B (fun p => -f p) (fun _ hp _ hq h => hinjB hp hq (neg_injective h)) (by omega)
        have hbc : f b < f c := neg_lt_neg_iff.mp hcb
        obtain ⟨A, hAU, hAbig, hA, hbA, hbmax⟩ := (Finset.mem_filter.mp (hBT hb)).2
        have hinjA := hf.mono (Finset.coe_subset.mpr (hAU.trans hUS))
        obtain ⟨a, ha, b', hb', hab', hmax⟩ := top_pair A f hinjA (by omega)
        have hb_eq : b' = b := by
          apply hinjA hb' hbA
          apply le_antisymm (hbmax b' hb')
          by_cases he : b = b'
          · simp [he]
          · exact ((hmax b hbA he).trans hab'.le)
        subst b'
        rcases hcover a (hUS (hAU ha)) b (hUS (hAU hbA)) c (hUS (hBU hc)) hab' hbc with h | h
        · have hn : c ∉ A := fun hcA => (hbmax c hcA).not_gt hbc
          have hh := hur _ (Finset.insert_subset (hBU hc) hAU)
            (tripleChain_append hR hinjA hA ha hbA hab' hbc hmax h)
          rw [Finset.card_insert_of_notMem hn] at hh
          omega
        · have hn : a ∉ B := by
            intro haB
            have hne : a ≠ b := fun he => hab'.ne (congrArg f he)
            have hh : f c ≤ f a := neg_le_neg_iff.mp (hmin a haB hne)
            linarith only [hab', hbc, hh]
          have hh := hvr _ (Finset.insert_subset (hAU ha) hBU)
            (tripleChain_prepend hQ hinjB hB hb hc hab' hbc
              (fun z hz hzb => neg_le_neg_iff.mp (hmin z hz hzb)) h)
          rw [Finset.card_insert_of_notMem hn] at hh
          omega
      have hur' : ∀ A ⊆ V, TripleChain f R A → A.card ≤ (u - 1) + 1 := by
        intro A hAV hA
        by_contra! hAbig
        obtain ⟨b, hb, hbmax⟩ := A.exists_max_image f (Finset.card_pos.mp (by omega))
        exact (Finset.mem_filter.mp (hAV hb)).2 ⟨A, hAV.trans hVU, by omega, hA, hb, hbmax⟩
      have hT := ih (u + (v - 1)) (by omega) u (v - 1) rfl T (hTU.trans hUS)
        (fun A hA h => hur A (hA.trans hTU) h) hvr'
      have hV := ih (u - 1 + v) (by omega) (u - 1) v rfl V (hVU.trans hUS)
        hur' (fun A hA h => hvr A (hA.trans hVU) h)
      have hsplit : T.card + V.card = U.card := Finset.card_filter_add_card_filter_not isEnd
      have hchoose : (u + v).choose u =
          (u + (v - 1)).choose u + (u - 1 + v).choose (u - 1) := by
        obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu0
        obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
        rw [show a.succ + b.succ = (a + b + 1).succ by omega, Nat.choose_succ_succ']
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        rw [show a + 1 + b = a + b + 1 by omega, show a + (b + 1) = a + b + 1 by omega]
        exact add_comm _ _
      rw [hchoose, ← hsplit]
      exact Nat.add_le_add hT hV
  exact main (u + v) u v rfl S (fun _ h => h) hu hv

private abbrev gapFamilySize (m : ℕ) := 2 * m + 3

private def gapIndex {m : ℕ} (i : Fin m) : Fin (gapFamilySize m) := ⟨2 * i.val + 2, by dsimp [gapFamilySize]; omega⟩
private def beforeIndex {m : ℕ} (i : Fin m) : Fin (gapFamilySize m) :=
  ⟨if i.val = 0 then 0 else 2 * i.val - 1, by dsimp [gapFamilySize]; split <;> omega⟩
private def leftIndex {m : ℕ} (i : Fin m) : Fin (gapFamilySize m) := ⟨2 * i.val + 1, by dsimp [gapFamilySize]; omega⟩
private def rightIndex {m : ℕ} (i : Fin m) : Fin (gapFamilySize m) := ⟨2 * i.val + 3, by dsimp [gapFamilySize]; omega⟩
private def afterIndex {m : ℕ} (i : Fin m) : Fin (gapFamilySize m) :=
  ⟨min (2 * i.val + 5) (2 * m + 2), by dsimp [gapFamilySize]; have := min_le_right (2 * i.val + 5) (2 * m + 2); omega⟩

private theorem index_order {m : ℕ} (i : Fin m) :
    beforeIndex i < leftIndex i ∧ leftIndex i < gapIndex i ∧
      gapIndex i < rightIndex i ∧ rightIndex i < afterIndex i := by
  simp only [beforeIndex, leftIndex, gapIndex, rightIndex, afterIndex, Fin.mk_lt_mk]
  split <;> omega

private theorem indices_adjacent {m : ℕ} (i j : Fin m) (h : i.val + 1 = j.val) :
    rightIndex i < gapIndex j ∧ gapIndex j < afterIndex i ∧
      beforeIndex j < gapIndex i ∧ gapIndex i < leftIndex j := by
  simp only [beforeIndex, leftIndex, gapIndex, rightIndex, afterIndex, Fin.mk_lt_mk]
  split <;> omega

private theorem gap_lt_of_lt {m : ℕ} {i j : Fin m} (h : i < j) :
    gapIndex i < gapIndex j := by
  have h' : i.val < j.val := h
  change 2 * i.val + 2 < 2 * j.val + 2
  omega

private theorem indices_far {m : ℕ} (i j : Fin m) (h : i ≠ j)
    (hpar : i.val % 2 = j.val % 2) : gapIndex j < beforeIndex i ∨ afterIndex i < gapIndex j := by
  have hne : i.val ≠ j.val := fun h' => h (Fin.ext h')
  simp only [beforeIndex, gapIndex, afterIndex, Fin.mk_lt_mk]
  split <;> omega

private theorem family_disjoint {r : ℕ} {P : Fin r → Finset Point}
    (hP : Ordered P) {i j : Fin r} (hij : i ≠ j) : Disjoint (P i) (P j) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hP.1 _ _ h p hp p hq).false
  · exact (hP.1 _ _ h p hq p hp).false

private structure GapFrame {m : ℕ} (P : Fin (gapFamilySize m) → Finset Point) (i : Fin m) where
  a : Point
  b : Point
  c : Point
  d : Point
  ha : a ∈ P (afterIndex i)
  hb : b ∈ P (beforeIndex i)
  hc : c ∈ P (leftIndex i)
  hd : d ∈ P (rightIndex i)

private theorem frame_ab {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) : F.b.1 < F.a.1 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := index_order i
  exact hP.1 _ _ (h₁.trans (h₂.trans (h₃.trans h₄))) _ F.hb _ F.ha

private theorem frame_det {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) {p : Point}
    (hp : p ∈ P (gapIndex i)) : 0 < det F.a F.b p := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := index_order i
  exact ordered_cyclic hP F.ha F.hb hp (Or.inr (Or.inl ⟨h₁.trans h₂, h₃.trans h₄⟩))

private theorem frame_endpoints {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) {p q : Point}
    (hq : q ∈ P (gapIndex i)) (ha : 0 < det p q F.a) (hb : det p q F.b < 0) :
    det p q F.c < 0 ∧ 0 < det p q F.d := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := index_order i
  apply vertical_endpoints (frame_det hP F hq) _ _ _ _ ha hb
  · exact ordered_anticyclic hP F.hb hq F.hc (Or.inr (Or.inl ⟨h₁, h₂⟩))
  · exact ordered_cyclic hP hq F.ha F.hc (Or.inr (Or.inr ⟨h₂, h₃.trans h₄⟩))
  · exact ordered_cyclic hP F.hb hq F.hd (Or.inl ⟨h₁.trans h₂, h₃⟩)
  · exact ordered_anticyclic hP hq F.ha F.hd (Or.inr (Or.inl ⟨h₃, h₄⟩))

private theorem frame_next_side {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i j : Fin m} (F : GapFrame P i) (hij : i.val + 1 = j.val)
    {p q z : Point} (hq : q ∈ P (gapIndex i)) (hz : z ∈ P (gapIndex j))
    (ha : 0 < det p q F.a) (hb : det p q F.b < 0) : 0 < det p q z := by
  obtain ⟨_, h₂, h₃, h₄⟩ := index_order i
  obtain ⟨hj₁, hj₂, _, _⟩ := indices_adjacent i j hij
  obtain ⟨hc, hd⟩ := frame_endpoints hP F hq ha hb
  apply vertical_next_side _ _ _ _ hc hd ha
  · exact ordered_cyclic hP F.hc F.hd F.ha (Or.inl ⟨h₂.trans h₃, h₄⟩)
  · exact ordered_anticyclic hP F.hd F.ha hz (Or.inr (Or.inl ⟨hj₁, hj₂⟩))
  · exact ordered_cyclic hP F.ha F.hc hz (Or.inr (Or.inl ⟨h₂.trans (h₃.trans hj₁), hj₂⟩))
  · exact ordered_cyclic hP F.hc F.hd hz (Or.inl ⟨h₂.trans h₃, hj₁⟩)

private theorem frame_prev_side {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i j : Fin m} (F : GapFrame P i) (hji : j.val + 1 = i.val)
    {p q z : Point} (hq : q ∈ P (gapIndex i)) (hz : z ∈ P (gapIndex j))
    (ha : 0 < det p q F.a) (hb : det p q F.b < 0) : det p q z < 0 := by
  obtain ⟨h₁, h₂, h₃, _⟩ := index_order i
  obtain ⟨_, _, hj₁, hj₂⟩ := indices_adjacent j i hji
  obtain ⟨hc, hd⟩ := frame_endpoints hP F hq ha hb
  apply vertical_prev_side _ _ _ _ hb hc hd
  · exact ordered_cyclic hP F.hb F.hc F.hd (Or.inl ⟨h₁, h₂.trans h₃⟩)
  · exact ordered_cyclic hP F.hc F.hd hz (Or.inr (Or.inr ⟨hj₂, h₂.trans h₃⟩))
  · exact ordered_cyclic hP F.hd F.hb hz (Or.inr (Or.inl ⟨hj₁, hj₂.trans (h₂.trans h₃)⟩))
  · exact ordered_anticyclic hP F.hb F.hc hz (Or.inr (Or.inl ⟨hj₁, hj₂⟩))

private theorem frame_far_side {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i j : Fin m} (F : GapFrame P i)
    (hfar : gapIndex j < beforeIndex i ∨ afterIndex i < gapIndex j)
    {p q z : Point} (hp : p ∈ P (gapIndex i)) (hz : z ∈ P (gapIndex j))
    (ha : det p q F.a < 0) (hb : det p q F.b < 0) : det p q z < 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := index_order i
  apply horizontal_far_side (frame_det hP F hp) _ _ ha hb
  · rcases hfar with h | h
    · exact ordered_cyclic hP F.hb hp hz (Or.inr (Or.inr ⟨h, h₁.trans h₂⟩))
    · exact ordered_cyclic hP F.hb hp hz (Or.inl ⟨h₁.trans h₂, h₃.trans (h₄.trans h)⟩)
  · rcases hfar with h | h
    · exact ordered_cyclic hP hp F.ha hz (Or.inr (Or.inr ⟨h.trans (h₁.trans h₂), h₃.trans h₄⟩))
    · exact ordered_cyclic hP hp F.ha hz (Or.inl ⟨h₃.trans h₄, h⟩)

private theorem frame_far_base {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i j : Fin m} (F : GapFrame P i)
    (hfar : gapIndex j < beforeIndex i ∨ afterIndex i < gapIndex j)
    {z : Point} (hz : z ∈ P (gapIndex j)) : 0 < det F.b F.a z := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := index_order i
  have hba := h₁.trans (h₂.trans (h₃.trans h₄))
  rcases hfar with h | h
  · exact ordered_cyclic hP F.hb F.ha hz (Or.inr (Or.inr ⟨h, hba⟩))
  · exact ordered_cyclic hP F.hb F.ha hz (Or.inl ⟨hba, h⟩)

private def gapCoordinates (a b o p : Point) : Point := (det a b p, o.1 - p.1)

private noncomputable def gapChart (a b p : Point) : Point :=
  perspective (gapCoordinates a b b p)

private noncomputable def gapKeyA (a b p : Point) : ℝ :=
  (perspective (gapCoordinates a b a p)).1

private theorem gapKey_order {a b o p q : Point} (hab : b.1 < a.1)
    (ho : o = a ∨ o = b) (hp : 0 < det a b p) (hq : 0 < det a b q) :
    (perspective (gapCoordinates a b o p)).1 < (perspective (gapCoordinates a b o q)).1 ↔
      det p q o < 0 := by
  change (o.1 - p.1) / det a b p < (o.1 - q.1) / det a b q ↔ _
  have h :
      (o.1 - q.1) * det a b p - (o.1 - p.1) * det a b q =
        (a.1 - b.1) * (-det p q o) := by
    rcases ho with rfl | rfl <;> simp only [det] <;> ring
  rw [div_lt_div_iff₀ hp hq, ← sub_pos, h, mul_pos_iff_of_pos_left (sub_pos.mpr hab), neg_pos]

private theorem gapCoordinates_det (a b p q r : Point) :
    det (gapCoordinates a b b p) (gapCoordinates a b b q) (gapCoordinates a b b r) =
      -(a.1 - b.1) * det p q r := by
  simp only [gapCoordinates, det]
  ring

private theorem gapChart_turn {a b p q r : Point} (hab : b.1 < a.1)
    (hp : 0 < det a b p) (hq : 0 < det a b q) (hr : 0 < det a b r) (σ : ℝ) :
    0 < (-σ) * det (gapChart a b p) (gapChart a b q) (gapChart a b r) ↔
      0 < σ * det p q r := by
  have hD := perspective_det (gapCoordinates a b b p) (gapCoordinates a b b q)
    (gapCoordinates a b b r) hp.ne' hq.ne' hr.ne'
  change det (gapChart a b p) (gapChart a b q) (gapChart a b r) *
    (det a b p * det a b q * det a b r) = _ at hD
  rw [gapCoordinates_det] at hD
  have heq :
      ((-σ) * det (gapChart a b p) (gapChart a b q) (gapChart a b r)) *
        (det a b p * det a b q * det a b r) = (a.1 - b.1) * (σ * det p q r) := by
    rw [mul_assoc, hD]
    ring
  rw [← mul_pos_iff_of_pos_right (mul_pos (mul_pos hp hq) hr), heq,
    mul_pos_iff_of_pos_left (sub_pos.mpr hab)]

private theorem det_sign_transitive (g : Point → Point) (σ : ℝ) :
    TripleTransitive (fun p => (g p).1) (fun p q r => 0 < σ * det (g p) (g q) (g r)) := by
  intro a b c d hab hbc hcd h₁ h₂
  let u := g a
  let v := g b
  let w := g c
  let z := g d
  change 0 < σ * det u v z ∧ 0 < σ * det u w z
  have eq₁ : (w.1 - v.1) * (σ * det u v z) =
      (z.1 - v.1) * (σ * det u v w) + (v.1 - u.1) * (σ * det v w z) := by
    unfold det; ring
  have eq₂ : (w.1 - v.1) * (σ * det u w z) =
      (w.1 - u.1) * (σ * det v w z) + (z.1 - w.1) * (σ * det u v w) := by
    unfold det; ring
  constructor
  · apply positive_det_of_product (sub_pos.mpr hbc)
    rw [eq₁]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply positive_det_of_product (sub_pos.mpr hbc)
    rw [eq₂]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem largest_subset {α : Type*} (S : Finset α) (Q : Finset α → Prop)
    (hq : Q ∅) : ∃ A ⊆ S, Q A ∧ ∀ B ⊆ S, Q B → B.card ≤ A.card := by
  classical
  let A := S.powerset.filter Q
  obtain ⟨U, hu, hmax⟩ := A.exists_max_image Finset.card ⟨∅, by simp [A, hq]⟩
  exact ⟨U, Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2,
    fun B hBS hB => hmax B (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBS, hB⟩)⟩

private def PairChain {α : Type*} (f g : α → ℝ) (S : Finset α) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, f p < f q → g p < g q

private theorem split_key_orders {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hg : Set.InjOn g S) :
    ∃ V ⊆ S, ∃ H ⊆ S, PairChain f (fun p => -g p) V ∧ PairChain f g H ∧
      S.card ≤ V.card * H.card := by
  classical
  let vert : Finset α → Prop := PairChain f (fun p => -g p)
  obtain ⟨V, hVS, hV, hvmax⟩ := largest_subset S vert (by simp [vert, PairChain])
  obtain ⟨H, hHS, hH, hhmax⟩ := largest_subset S (PairChain f g) (by simp [PairChain])
  refine ⟨V, hVS, H, hHS, hV, hH, ?_⟩
  let below (p : α) := S.powerset.filter fun A =>
    vert A ∧ ∀ z ∈ A, f z < f p ∧ g p < g z
  let r (p : α) := (below p).sup Finset.card
  have hext {p : α} (hp : p ∈ S) {A : Finset α} (hA : A ∈ below p) :
      insert p A ⊆ S ∧ vert (insert p A) ∧ (insert p A).card = A.card + 1 := by
    obtain ⟨hs, hvert, hlo⟩ := Finset.mem_filter.mp hA
    have hn : p ∉ A := fun h => (hlo p h).1.false
    refine ⟨Finset.insert_subset hp (Finset.mem_powerset.mp hs), ?_,
      Finset.card_insert_of_notMem hn⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx' <;>
      rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact hxy.false.elim
    · exact ((hlo y hy').1.asymm hxy).elim
    · exact neg_lt_neg ((hlo x hx').2)
    · exact hvert x hx' y hy' hxy
  have hrlt : ∀ p ∈ S, r p < V.card := by
    intro p hp
    have hvpos : 0 < V.card := by
      have hh : vert {p} := by simp [vert, PairChain]
      have hh' := hvmax {p} (Finset.singleton_subset_iff.mpr hp) hh
      simpa using hh'
    apply (Finset.sup_lt_iff hvpos).mpr
    intro A hA
    obtain ⟨hsub, hturn, hcard⟩ := hext hp hA
    have hh := hvmax _ hsub hturn
    omega
  have hrise {p q : α} (hp : p ∈ S) (hpq : f p < f q) (hqp : g q < g p) : r p < r q := by
    have hne : (below p).Nonempty := ⟨∅, by simp [below, vert, PairChain]⟩
    obtain ⟨A, hA, he⟩ := Finset.exists_mem_eq_sup (below p) hne Finset.card
    obtain ⟨hsub, hturn, hcard⟩ := hext hp hA
    have hm : insert p A ∈ below q := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hturn, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hpq, hqp⟩
      · have hz := (Finset.mem_filter.mp hA).2.2 x hx
        exact ⟨hz.1.trans hpq, hqp.trans hz.2⟩
    have hh : (insert p A).card ≤ r q := Finset.le_sup hm
    change r p = A.card at he
    omega
  calc
    S.card = ∑ j ∈ Finset.range V.card, (S.filter (fun p => r p = j)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_range.mpr (hrlt p hp))
    _ ≤ ∑ _j ∈ Finset.range V.card, H.card := by
      apply Finset.sum_le_sum
      intro j _
      apply hhmax _ (Finset.filter_subset _ _)
      intro p hp q hq hpq
      obtain ⟨hpS, hpj⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqS, hqj⟩ := Finset.mem_filter.mp hq
      have hn : g p ≠ g q := fun he => hpq.ne (congrArg f (hg hpS hqS he))
      rcases lt_or_gt_of_ne hn with h | h
      · exact h
      · exact ((hrise hpS hpq h).ne (hpj.trans hqj.symm)).elim
    _ = V.card * H.card := by simp

private noncomputable def frameKey {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point} {i : Fin m}
    (F : GapFrame P i) (p : Point) : ℝ := (gapChart F.a F.b p).1

private theorem frame_order_key {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) {o p q : Point}
    (ho : o = F.a ∨ o = F.b) (hp : p ∈ P (gapIndex i)) (hq : q ∈ P (gapIndex i)) :
    (perspective (gapCoordinates F.a F.b o p)).1 <
      (perspective (gapCoordinates F.a F.b o q)).1 ↔ det p q o < 0 :=
  gapKey_order (frame_ab hP F) ho (frame_det hP F hp) (frame_det hP F hq)

private theorem frame_key_inj {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) {o : Point} (ho : o = F.a ∨ o = F.b) :
    Set.InjOn (fun p => (perspective (gapCoordinates F.a F.b o p)).1) (P (gapIndex i)) := by
  intro p hp q hq he
  by_contra hn
  have no_eq (r : Point) (hr : r ∈ P (gapIndex i)) : r ≠ o := by
    have hdet := frame_det hP F hr
    intro heq
    rcases ho with h | h
    · rw [heq, h, det_self₁₃] at hdet
      exact hdet.false
    · rw [heq, h, det_self₂₃] at hdet
      exact hdet.false
  have hoo : o ∈ familyUnion P := by
    rcases ho with rfl | rfl
    · exact mem_familyUnion.mpr ⟨_, F.ha⟩
    · exact mem_familyUnion.mpr ⟨_, F.hb⟩
  have hdet := hP.2.2 p (mem_familyUnion.mpr ⟨_, hp⟩) q (mem_familyUnion.mpr ⟨_, hq⟩)
    o hoo hn (no_eq q hq) (no_eq p hp)
  rcases lt_or_gt_of_ne hdet with h | h
  · exact ((frame_order_key hP F ho hp hq).mpr h).ne he
  · have h' : det q p o < 0 := by rw [det_swap]; exact neg_neg_of_pos h
    exact ((frame_order_key hP F ho hq hp).mpr h').ne he.symm

private theorem split_gap_turns {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) {S : Finset Point} (hS : S ⊆ P (gapIndex i)) :
    ∃ U ⊆ S, ∃ V ⊆ S, Turning (frameKey F) (-1) U ∧ Turning (frameKey F) 1 V ∧
      S.card ≤ (U.card + V.card).choose U.card := by
  classical
  let f := frameKey F
  let G := gapChart F.a F.b
  let R (p q r : Point) := 0 < (1 : ℝ) * det (G p) (G q) (G r)
  let Q (p q r : Point) := 0 < (-1 : ℝ) * det (G p) (G q) (G r)
  have hbase (p : Point) (hp : p ∈ S) := frame_det hP F (hS hp)
  have rIff {a b c : Point} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
      R a b c ↔ 0 < (-1 : ℝ) * det a b c := by
    simpa only [R, neg_neg] using gapChart_turn (frame_ab hP F) (hbase a ha) (hbase b hb) (hbase c hc) (-1)
  have qIff {a b c : Point} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
      Q a b c ↔ 0 < (1 : ℝ) * det a b c :=
    gapChart_turn (frame_ab hP F) (hbase a ha) (hbase b hb) (hbase c hc) 1
  obtain ⟨U, hUS, hU, huMax⟩ := largest_subset S (TripleChain f R) (by simp [TripleChain])
  obtain ⟨V, hVS, hV, hvMax⟩ := largest_subset S (TripleChain f Q) (by simp [TripleChain])
  refine ⟨U, hUS, V, hVS, ?_, ?_, ?_⟩
  · intro a ha b hb c hc hab hbc
    exact (rIff (hUS ha) (hUS hb) (hUS hc)).mp (hU a ha b hb c hc hab hbc)
  · intro a ha b hb c hc hab hbc
    exact (qIff (hVS ha) (hVS hb) (hVS hc)).mp (hV a ha b hb c hc hab hbc)
  · apply cups_bound S f ((frame_key_inj hP F (Or.inr rfl)).mono hS) R Q
      (det_sign_transitive G 1) (det_sign_transitive G (-1)) _ U.card V.card
      (fun A ha h => (huMax A ha h).trans (Nat.le_succ _))
      (fun A ha h => (hvMax A ha h).trans (Nat.le_succ _))
    intro a ha b hb c hc hab hbc
    have hIn (p : Point) (hp : p ∈ S) : p ∈ familyUnion P := mem_familyUnion.mpr ⟨_, hS hp⟩
    have hn := hP.2.2 a (hIn a ha) b (hIn b hb) c (hIn c hc)
      (fun he => hab.ne (congrArg f he)) (fun he => hbc.ne (congrArg f he))
      (fun he => (hab.trans hbc).ne (congrArg f he))
    rcases lt_or_gt_of_ne hn with h | h
    · left; exact (rIff ha hb hc).mpr (by simpa using h)
    · right; exact (qIff ha hb hc).mpr (by simpa using h)

private structure GapChains {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point} {i : Fin m}
    (F : GapFrame P i) where
  left : Finset Point
  right : Finset Point
  inner : Finset Point
  outer : Finset Point
  left_sub : left ⊆ P (gapIndex i)
  right_sub : right ⊆ P (gapIndex i)
  inner_sub : inner ⊆ P (gapIndex i)
  outer_sub : outer ⊆ P (gapIndex i)
  left_turn : Turning (frameKey F) (-1) left
  right_turn : Turning (frameKey F) 1 right
  inner_turn : Turning (frameKey F) (-1) inner
  outer_turn : Turning (frameKey F) 1 outer
  leftSide : ∀ p ∈ left, ∀ q ∈ left, frameKey F p < frameKey F q →
    0 < det p q F.a ∧ det p q F.b < 0
  rightSide : ∀ p ∈ right, ∀ q ∈ right, frameKey F p < frameKey F q →
    0 < det p q F.a ∧ det p q F.b < 0
  innerSide : ∀ p ∈ inner, ∀ q ∈ inner, frameKey F p < frameKey F q →
    det p q F.a < 0 ∧ det p q F.b < 0
  card_le : (P (gapIndex i)).card ≤
    (left.card + right.card).choose left.card * (inner.card + outer.card).choose inner.card

private theorem gap_chains {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i : Fin m} (F : GapFrame P i) : Nonempty (GapChains F) := by
  let S := P (gapIndex i)
  let f := frameKey F
  let g := gapKeyA F.a F.b
  obtain ⟨V, hVS, H, hHS, hv, hh, hc⟩ := split_key_orders S f g (frame_key_inj hP F (Or.inl rfl))
  obtain ⟨L, hLV, R, hRV, hl, hr, hvC⟩ := split_gap_turns hP F hVS
  obtain ⟨I, hIH, O, hOH, hi, ho, hhC⟩ := split_gap_turns hP F hHS
  have vert {p q : Point} (hp : p ∈ V) (hq : q ∈ V) (hpq : f p < f q) :
      0 < det p q F.a ∧ det p q F.b < 0 := by
    have hdeg := neg_lt_neg_iff.mp (hv p hp q hq hpq)
    have ha := (frame_order_key hP F (Or.inl rfl) (hVS hq) (hVS hp)).mp hdeg
    rw [det_swap] at ha
    exact ⟨neg_neg_iff_pos.mp ha, (frame_order_key hP F (Or.inr rfl) (hVS hp) (hVS hq)).mp hpq⟩
  exact ⟨⟨L, R, I, O, hLV.trans hVS, hRV.trans hVS, hIH.trans hHS, hOH.trans hHS,
    hl, hr, hi, ho, (fun _ hp _ hq => vert (hLV hp) (hLV hq)),
    (fun _ hp _ hq => vert (hRV hp) (hRV hq)), (fun p hp q hq hpq =>
      ⟨(frame_order_key hP F (Or.inl rfl) (hHS (hIH hp)) (hHS (hIH hq))).mp (hh p (hIH hp) q (hIH hq) hpq),
        (frame_order_key hP F (Or.inr rfl) (hHS (hIH hp)) (hHS (hIH hq))).mp hpq⟩),
    hc.trans (Nat.mul_le_mul hvC hhC)⟩⟩

private theorem expose_piece {A S : Finset Point} (hAS : A ⊆ S)
    {f : Point → ℝ} (hf : Set.InjOn f A) (σ : ℝ) (hturn : Turning f σ A)
    (hout : ∀ p ∈ A, ∀ q ∈ A, f p < f q → ∀ z ∈ S, z ∉ A → 0 < σ * det p q z)
    {p : Point} (hp : p ∈ A)
    (hsingle : ∃ u v : ℝ, ∀ q ∈ S, q ∉ A → u * p.1 + v * p.2 < u * q.1 + v * q.2) :
    ∃ u v : ℝ, ∀ q ∈ S, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2 := by
  by_cases h : 2 ≤ A.card
  · exact expose_chain hAS hf h σ hturn hout hp
  · obtain ⟨u, v, hsep⟩ := hsingle
    refine ⟨u, v, fun q hq hqp => hsep q hq ?_⟩
    intro hqA
    exact hqp (Finset.card_le_one.mp (by omega) q hqA p hp)

private theorem chain_exposed {A : Finset Point} {f : Point → ℝ}
    (hf : Set.InjOn f A) {σ : ℝ} (h : Turning f σ A) : Exposed A := by
  intro p hp
  exact expose_piece (fun _ h => h) hf σ h
    (fun _ _ _ _ _ _ hz hn => (hn hz).elim) hp
    ⟨0, 0, fun _ hq hqn => (hqn hq).elim⟩

private theorem expose_vertical_join {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {i j : Fin m} (hij : i.val + 1 = j.val)
    {F : GapFrame P i} {G : GapFrame P j} (C : GapChains F) (D : GapChains G) :
    Exposed (C.right ∪ D.left) := by
  have hlt : gapIndex i < gapIndex j := gap_lt_of_lt (show i < j from by
    change i.val < j.val
    omega)
  have hR := (frame_key_inj hP F (Or.inr rfl)).mono C.right_sub
  have hL := (frame_key_inj hP G (Or.inr rfl)).mono D.left_sub
  intro p hp
  rcases Finset.mem_union.mp hp with hp' | hp'
  · refine expose_piece Finset.subset_union_left hR 1 C.right_turn ?_ hp' ⟨1, 0, ?_⟩
    · intro a ha b hb hab q hq hn
      have hqL := (Finset.mem_union.mp hq).resolve_left hn
      obtain ⟨ha, hb'⟩ := C.rightSide a ha b hb hab
      simpa only [one_mul] using frame_next_side hP F hij (C.right_sub hb) (D.left_sub hqL) ha hb'
    · intro q hq hn
      have hqL := (Finset.mem_union.mp hq).resolve_left hn
      simpa using hP.1 _ _ hlt p (C.right_sub hp') q (D.left_sub hqL)
  · refine expose_piece Finset.subset_union_right hL (-1) D.left_turn ?_ hp' ⟨-1, 0, ?_⟩
    · intro a ha b hb hab q hq hn
      have hqR := (Finset.mem_union.mp hq).resolve_right hn
      obtain ⟨ha, hb'⟩ := D.leftSide a ha b hb hab
      simpa using frame_prev_side hP G hij (D.left_sub hb) (C.right_sub hqR) ha hb'
    · intro q hq hn
      have hqR := (Finset.mem_union.mp hq).resolve_right hn
      simpa using hP.1 _ _ hlt q (C.right_sub hqR) p (D.left_sub hp')

private theorem expose_horizontal_join {m : ℕ} {P : Fin (gapFamilySize m) → Finset Point}
    (hP : Ordered P) {F : ∀ i, GapFrame P i} (G : ∀ i, GapChains (F i))
    (I : Finset (Fin m)) {b : ℕ} (hpar : ∀ i ∈ I, i.val % 2 = b) :
    Exposed (I.biUnion fun i => (G i).inner) := by
  intro p hp
  obtain ⟨i, hi, hpI⟩ := Finset.mem_biUnion.mp hp
  have hIS : (G i).inner ⊆ I.biUnion (fun j => (G j).inner) :=
    fun q hq => Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
  have hfar {q : Point} (hq : q ∈ I.biUnion (fun j => (G j).inner)) (hn : q ∉ (G i).inner) :
      ∃ j : Fin m, (gapIndex j < beforeIndex i ∨ afterIndex i < gapIndex j) ∧ q ∈ P (gapIndex j) := by
    obtain ⟨j, hj, hqJ⟩ := Finset.mem_biUnion.mp hq
    have hjne : i ≠ j := fun he => hn (he.symm ▸ hqJ)
    exact ⟨j, indices_far i j hjne ((hpar i hi).trans (hpar j hj).symm), (G j).inner_sub hqJ⟩
  have hinj := (frame_key_inj hP (F i) (Or.inr rfl)).mono (G i).inner_sub
  refine expose_piece hIS hinj (-1) (G i).inner_turn ?_ hpI ?_
  · intro u hu v hv huv q hq hn
    obtain ⟨j, hj, hqJ⟩ := hfar hq hn
    obtain ⟨ha, hb⟩ := (G i).innerSide u hu v hv huv
    simpa using frame_far_side hP (F i) hj ((G i).inner_sub hu) hqJ ha hb
  · let a := (F i).a
    let b' := (F i).b
    refine ⟨b'.2 - a.2, a.1 - b'.1, ?_⟩
    intro q hq hn
    obtain ⟨j, hj, hqJ⟩ := hfar hq hn
    have hqpos : 0 < det b' a q := frame_far_base hP (F i) hj hqJ
    have hppos : 0 < det a b' p := frame_det hP (F i) ((G i).inner_sub hpI)
    rw [det_swap] at hppos
    have heq (z : Point) :
        (b'.2 - a.2) * z.1 + (a.1 - b'.1) * z.2 -
          ((b'.2 - a.2) * b'.1 + (a.1 - b'.1) * b'.2) = det b' a z := by
      unfold det
      ring
    linarith only [heq q, heq p, hqpos, hppos]

private theorem sum_path_bound {m n : ℕ} (L R : Fin m → ℕ)
    (hl : ∀ i, L i ≤ n) (hr : ∀ i, R i ≤ n)
    (hp : ∀ i j : Fin m, i.val + 1 = j.val → R i + L j ≤ n) :
    ∑ i, (L i + R i) ≤ m * n + n := by
  cases m with
  | zero => simp
  | succ d =>
    have hsum : (∑ i : Fin d, (R i.castSucc + L i.succ)) ≤ d * n := by
      calc
        _ ≤ ∑ _i : Fin d, n := Finset.sum_le_sum fun i _ => hp i.castSucc i.succ rfl
        _ = d * n := by simp
    calc
      ∑ i : Fin (d + 1), (L i + R i) =
          L 0 + R (Fin.last d) + ∑ i : Fin d, (R i.castSucc + L i.succ) := by
        rw [Finset.sum_add_distrib, Fin.sum_univ_succ L, Fin.sum_univ_castSucc R,
          Finset.sum_add_distrib]
        omega
      _ ≤ n + n + d * n := Nat.add_le_add (Nat.add_le_add (hl 0) (hr (Fin.last d))) hsum
      _ = (d + 1) * n + n := by ring

private theorem ordered_log_bound {m n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s)
    {P : Fin (gapFamilySize m) → Finset Point} (hP : Ordered P)
    (hc : ∀ i, (P i).card = s)
    (hno : ∀ Z ⊆ familyUnion P, Exposed Z → Z.card ≤ n) :
    (m : ℝ) * Real.log s ≤ ((m : ℝ) * n + n) * Real.log 2 +
      2 * n * Real.log (2 * (n : ℝ)) := by
  classical
  have hne : ∀ i, (P i).Nonempty := fun i => Finset.card_pos.mp (hc i ▸ hs)
  let F : (i : Fin m) → GapFrame P i := fun i =>
    ⟨(hne _).choose, (hne _).choose, (hne _).choose, (hne _).choose,
      (hne _).choose_spec, (hne _).choose_spec, (hne _).choose_spec, (hne _).choose_spec⟩
  let G : (i : Fin m) → GapChains (F i) := fun i => Classical.choice (gap_chains hP (F i))
  let L (i : Fin m) := (G i).left.card
  let R (i : Fin m) := (G i).right.card
  let A (i : Fin m) := (G i).inner.card
  let B (i : Fin m) := (G i).outer.card
  have hsub {i : Fin (gapFamilySize m)} : P i ⊆ familyUnion P :=
    fun p hp => mem_familyUnion.mpr ⟨i, hp⟩
  have hsingle (i : Fin m) {S : Finset Point} (hS : S ⊆ P (gapIndex i)) {σ : ℝ}
      (h : Turning (frameKey (F i)) σ S) : S.card ≤ n :=
    hno S (hS.trans hsub) (chain_exposed ((frame_key_inj hP (F i) (Or.inr rfl)).mono hS) h)
  have hl : ∀ i, L i ≤ n := fun i => hsingle i (G i).left_sub (G i).left_turn
  have hr : ∀ i, R i ≤ n := fun i => hsingle i (G i).right_sub (G i).right_turn
  have ha : ∀ i, A i ≤ n := fun i => hsingle i (G i).inner_sub (G i).inner_turn
  have hb : ∀ i, B i ≤ n := fun i => hsingle i (G i).outer_sub (G i).outer_turn
  have hv : ∑ i, (L i + R i) ≤ m * n + n := by
    apply sum_path_bound L R hl hr
    intro i j h
    have hlt : i < j := by change i.val < j.val; omega
    have hD := family_disjoint hP (gap_lt_of_lt hlt).ne
    have hdisj : Disjoint (G i).right (G j).left :=
      hD.mono (G i).right_sub (G j).left_sub
    have hC := hno ((G i).right ∪ (G j).left)
      (Finset.union_subset ((G i).right_sub.trans hsub) ((G j).left_sub.trans hsub))
      (expose_vertical_join hP h (G i) (G j))
    rwa [Finset.card_union_of_disjoint hdisj] at hC
  let E := Finset.univ.filter fun i : Fin m => i.val % 2 = 0
  let O := Finset.univ.filter fun i : Fin m => ¬ i.val % 2 = 0
  have hpar (I : Finset (Fin m)) (p : ℕ) (hp : ∀ i ∈ I, i.val % 2 = p) : ∑ i ∈ I, A i ≤ n := by
    let Y := I.biUnion fun i => (G i).inner
    have hY : Y ⊆ familyUnion P := by
      intro q hq
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hq
      exact hsub ((G i).inner_sub hi)
    have hd : Set.PairwiseDisjoint (I : Set (Fin m)) (fun i => (G i).inner) := by
      intro i _ j _ hne
      have hn : gapIndex i ≠ gapIndex j := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact (gap_lt_of_lt h).ne
        · exact (gap_lt_of_lt h).ne'
      exact (family_disjoint hP hn).mono (G i).inner_sub (G j).inner_sub
    have hC := hno Y hY (expose_horizontal_join hP G I hp)
    rw [Finset.card_biUnion hd] at hC
    exact hC
  have hEa : ∑ i ∈ E, A i ≤ n := hpar E 0 fun i hi => (Finset.mem_filter.mp hi).2
  have hOa : ∑ i ∈ O, A i ≤ n := hpar O 1 fun i hi => by
    have h := (Finset.mem_filter.mp hi).2
    omega
  have hh : ∑ i, A i ≤ 2 * n := by
    have he : (∑ i ∈ E, A i) + (∑ i ∈ O, A i) = ∑ i, A i :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    omega
  have hc' (i : Fin m) : s ≤ 2 ^ (L i + R i) * (2 * n) ^ (A i) := by
    have H := (G i).card_le
    rw [hc] at H
    refine H.trans (Nat.mul_le_mul (Nat.choose_le_two_pow _ _) ?_)
    calc
      (A i + B i).choose (A i) ≤ (A i + B i) ^ (A i) := Nat.choose_le_pow _ _
      _ ≤ (2 * n) ^ (A i) := Nat.pow_le_pow_left (by have := ha i; have := hb i; omega) _
  have hsPow : s ^ m ≤ 2 ^ (m * n + n) * (2 * n) ^ (2 * n) := by
    calc
      s ^ m = ∏ i : Fin m, s := by simp
      _ ≤ ∏ i : Fin m, 2 ^ (L i + R i) * (2 * n) ^ (A i) := Finset.prod_le_prod' fun i _ => hc' i
      _ = 2 ^ (∑ i, (L i + R i)) * (2 * n) ^ (∑ i, A i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hv) (Nat.pow_le_pow_right (by omega) hh)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (s : ℝ) ^ m ≤ (2 : ℝ) ^ (m * n + n) * (2 * (n : ℝ)) ^ (2 * n) := by
    exact_mod_cast hsPow
  have hlog := Real.log_le_log (pow_pos hsR m) hpow
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  exact hlog

private abbrev familySize (m : ℕ) : ℕ := 4 * m + 7

private def FiniteBound : Prop :=
  ∀ (n m : ℕ), 4 ≤ n → 0 < m → ∀ T : Fin (familySize m) → Finset Plane,
    General T → Transversals T → (∀ i, (T i).Nonempty) → ¬ HasPolygon n T →
    ∃ i, (m : ℝ) * Real.log (T i).card ≤
      ((m : ℝ) * n + n) * Real.log 2 +
        m * Real.log (2 * (familySize m : ℝ)) + 2 * n * Real.log (2 * (n : ℝ))

theorem finite_bound : FiniteBound := by
  classical
  intro n m hn hm T hgen htrans hne hno
  let k := familySize m
  have hk : 0 < k := by dsimp [k, familySize]; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨j, -, hmin⟩ := (Finset.univ : Finset (Fin k)).exists_min_image (fun i => (T i).card)
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  let N := (T j).card
  let s := N / k
  have hNr : (0 : ℝ) < N := by exact_mod_cast Finset.card_pos.mpr (hne j)
  refine ⟨j, ?_⟩
  change (m : ℝ) * Real.log (N : ℝ) ≤
    ((m : ℝ) * n + n) * Real.log 2 + m * Real.log (2 * (k : ℝ)) + 2 * n * Real.log (2 * (n : ℝ))
  have hdiv : N % k + k * s = N := Nat.mod_add_div N k
  have hrem : N % k < k := Nat.mod_lt N hk
  by_cases hs0 : s = 0
  · have hsmall : N ≤ 2 * k := by rw [hs0, mul_zero, add_zero] at hdiv; omega
    have hlog := Real.log_le_log hNr (show (N : ℝ) ≤ 2 * (k : ℝ) by exact_mod_cast hsmall)
    have hlog' := mul_le_mul_of_nonneg_left hlog hmr.le
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpos₁ : 0 ≤ ((m : ℝ) * n + n) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    have hpos₂ : 0 ≤ 2 * (n : ℝ) * Real.log (2 * (n : ℝ)) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    linarith only [hlog', hpos₁, hpos₂]
  · have hs : 0 < s := Nat.pos_of_ne_zero hs0
    have hlarge : ∀ i, k * s ≤ (T i).card :=
      fun i => (by omega : k * s ≤ N).trans (hmin i (Finset.mem_univ _))
    obtain ⟨P, hP, hcard, hlift⟩ :=
      ordered_of_transversals (r := gapFamilySize m) (show 2 * gapFamilySize m + 1 ≤ k by
        dsimp [k, familySize, gapFamilySize]; omega) hs hgen htrans hne hlarge
    have hPno : ∀ Z ⊆ familyUnion P, Exposed Z → Z.card ≤ n := by
      intro Z hZ hC
      by_contra! hZbig
      obtain ⟨Y, hYZ, hYc⟩ := Finset.exists_subset_card_eq (show n ≤ Z.card by omega)
      apply hno
      rw [← hYc]
      exact hlift Y (hYZ.trans hZ) (exposed_mono hC hYZ)
    have hPlog := ordered_log_bound hn hs hP hcard hPno
    have hsmall : N ≤ 2 * k * s := by
      have hks : k ≤ k * s := by
        simpa using Nat.mul_le_mul_left k (show 1 ≤ s by omega)
      rw [Nat.mul_assoc]
      omega
    have hsr : (0 : ℝ) < s := by exact_mod_cast hs
    have hlog := Real.log_le_log hNr
      (show (N : ℝ) ≤ 2 * (k : ℝ) * (s : ℝ) by exact_mod_cast hsmall)
    rw [Real.log_mul (by positivity) hsr.ne'] at hlog
    have hlog' := mul_le_mul_of_nonneg_left hlog hmr.le
    linarith only [hlog', hPlog]

theorem h2_of_finiteBound (hfinite : FiniteBound) :
    OMA.R_Erdos107_variants_hmpt_bound_R1.H2 := by
  classical
  refine ⟨100, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  let s : ℝ := Real.sqrt ((n : ℝ) * Real.log n)
  let m : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := OMA.R_Erdos107_variants_hmpt_bound_R1.one_le_scale (by omega)
  have hsm : s ≤ (m : ℝ) := Nat.le_ceil s
  have hmUpper : (m : ℝ) < s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  have hk : (familySize m : ℝ) ≤ 15 * s := by
    simp only [familySize, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  refine ⟨familySize m, by dsimp [familySize]; omega, by linarith, ?_⟩
  intro T hgen htrans hcard
  have hpos : ∀ i, (0 : ℝ) < (T i).card := fun i =>
    (Real.rpow_pos_of_pos (by norm_num) _).trans (hcard i)
  have hne : ∀ i, (T i).Nonempty := fun i =>
    Finset.card_pos.mp (by exact_mod_cast hpos i)
  by_contra hno
  obtain ⟨i, hbound⟩ := hfinite n m hn hm T hgen htrans hne hno
  have hlam : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 1 ≤ Real.log (n : ℝ) := by
    calc
      1 ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
  have hlog2n : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by linarith)
    linarith
  have hs2 : s * s = (n : ℝ) * Real.log n := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have hnms : (n : ℝ) ≤ (m : ℝ) * s := by
    calc
      (n : ℝ) ≤ (n : ℝ) * Real.log n := le_mul_of_one_le_right hn0.le hlogn
      _ = s * s := hs2.symm
      _ ≤ m * s := mul_le_mul_of_nonneg_right hsm (by positivity)
  have htail : 2 * (n : ℝ) * Real.log (2 * (n : ℝ)) ≤ 4 * ((m : ℝ) * s) := by
    calc
      _ ≤ 2 * (n : ℝ) * (2 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2n (by positivity)
      _ = 4 * (s * s) := by rw [hs2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsm (by positivity)) (by norm_num)
  have hlogk : Real.log (2 * (familySize m : ℝ)) ≤ 30 * s := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (familySize m : ℝ))
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hbudget : (4 + 30 : ℝ) ≤ 99 * Real.log 2 := by linarith
  have hbound' : (m : ℝ) * Real.log (T i).card ≤
      (m : ℝ) * ((n : ℝ) + 100 * s) * Real.log 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hnms (show 0 ≤ Real.log 2 by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hlogk hm0.le
    have h₃ := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ (m : ℝ) * s by positivity)
    nlinarith only [hbound, h₁, h₂, h₃, htail]
  have hl := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) (hcard i)
  rw [Real.log_rpow (by norm_num)] at hl
  change ((n : ℝ) + 100 * s) * Real.log 2 < Real.log (T i).card at hl
  have hc := mul_lt_mul_of_pos_left hl hm0
  nlinarith only [hbound', hc]

end HMPTStep

theorem OMA.solution : OMA.R_Erdos107_variants_hmpt_bound_R1.H2 := by
  exact HMPTStep.h2_of_finiteBound HMPTStep.finite_bound

