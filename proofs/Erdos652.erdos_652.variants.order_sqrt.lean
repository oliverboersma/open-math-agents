import FormalConjectures.ErdosProblems.«652»

section

/-! # The order of the kth pinned distance count

Two finite geometric inputs suffice: an incidence bound at arbitrarily large sizes for
each fixed number of centers, and a rectangular circle-grid construction. The incidence
bound counts the zero distance; the definition of the admissible constants excludes it.
Credit: @JaviSoto. -/

namespace OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1

open Filter Finset Erdos652
open scoped EuclideanGeometry Classical

/-- A restricted version of Mathialagan's pinned incidence bound: the centers are in the
point set, and only arbitrarily large sizes are required for each fixed k. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∃ᶠ n : ℕ in atTop,
    ∀ P Q : Finset ℝ², P ⊆ Q → P.card = k → Q.card = n →
      ∃ p ∈ P, c * Real.sqrt ((k : ℝ) * n) ≤ ((Q.image fun q => dist q p).card : ℝ)

/-- A rectangular circle grid of height k*m supplies enough points while keeping the
number of radii at each of its k centers linear in k*m. -/
def H2 : Prop :=
  ∀ k n m : ℕ, k ≤ n → n ≤ m * (k * m) →
    ∃ pts : Finset ℝ², pts.card = n ∧ k ≤
      (pts.filter fun p => distinctDistancesFrom pts p ≤ k + 3*k*m).card

open Filter

private lemma all_distances_le_twice (Q : Finset ℝ²) (hQ : 2 ≤ Q.card) {p : ℝ²} (hp : p ∈ Q) :
    (Q.image fun q => dist q p).card ≤ 2 * distinctDistancesFrom Q p := by
  classical
  let D := (Q.erase p).image fun q => dist q p
  have hd : distinctDistancesFrom Q p = D.card := by
    unfold distinctDistancesFrom
    apply congrArg Finset.card
    ext d
    simp only [D, Finset.mem_image, Finset.mem_erase]
  have hpos : 0 < D.card := Finset.card_pos.mpr
    ((Finset.erase_nonempty hp).mpr (Finset.one_lt_card_iff_nontrivial.mp hQ) |>.image _)
  have he : Q.image (fun q => dist q p) = insert 0 D := by
    calc
      _ = (insert p (Q.erase p)).image (fun q => dist q p) := by rw [insert_erase hp]
      _ = _ := by rw [image_insert, dist_self]
  rw [hd, he]
  have := Finset.card_insert_le 0 D
  omega

private lemma admissible_lower {c : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : ∃ᶠ n : ℕ in atTop, ∀ P Q : Finset ℝ², P ⊆ Q → P.card = k → Q.card = n →
      ∃ p ∈ P, c * Real.sqrt ((k : ℝ) * n) ≤ ((Q.image fun q => dist q p).card : ℝ))
    {a : ℝ} (ha : AdmissibleConstant k a) : c / 2 * Real.sqrt k ≤ a := by
  classical
  obtain ⟨n, hinc, ⟨Q, hcard, hgood⟩, hn⟩ := ((h.and_eventually
    (ha.2.and (eventually_ge_atTop 2))).exists)
  obtain ⟨P, hsub, hP⟩ := Finset.exists_subset_card_eq hgood
  have hPQ : P ⊆ Q := hsub.trans (Finset.filter_subset _ _)
  obtain ⟨p, hp, hlow⟩ := hinc P Q hPQ hP hcard
  have hpQ := hPQ hp
  have hu := (Finset.mem_filter.mp (hsub hp)).2
  have hd : ((Q.image fun q => dist q p).card : ℝ) ≤
      2 * (distinctDistancesFrom Q p : ℝ) := by
    exact_mod_cast all_distances_le_twice Q (by omega) hpQ
  rw [Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ))] at hlow
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  by_contra! hbad
  have hcontra := mul_lt_mul_of_pos_right hbad hs
  linarith only [hlow.trans hd, hu, hcontra]

/-- Choose the grid width one above the integer square root of n/k. -/
private lemma admissible_of_rectangle (rect : H2)
    (k : ℕ) (hk : 2 ≤ k) : Erdos652.AdmissibleConstant k (8 * Real.sqrt k) := by
  classical
  have hkpos : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hkpos
  refine ⟨by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop k] with n hkn
  let d := (n / k).sqrt
  let m := d + 1
  have hdlt : (n / k).sqrt < m := Nat.lt_succ_self _
  have hlarge : n < m * m * k := (Nat.div_lt_iff_lt_mul hkpos).mp (Nat.sqrt_lt.mp hdlt)
  have hsize : n ≤ m * (k * m) := by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlarge.le
  obtain ⟨pts, hpts, hgood⟩ := rect k n m hkn hsize
  refine ⟨pts, hpts, hgood.trans (card_le_card ?_)⟩
  intro p hp
  obtain ⟨hpp, hcount⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hpp, ?_⟩
  have hdsq : d*d*k ≤ n := (Nat.mul_le_mul_right k (Nat.sqrt_le (n/k))).trans (Nat.div_mul_le_self n k)
  have hdsqr : (d : ℝ)*(d : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hdsq
  have hdroot : (d : ℝ) * Real.sqrt k ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hkr.le, sq]
    exact hdsqr
  have hdprod : (k : ℝ)*d ≤ Real.sqrt k * Real.sqrt n := by
    calc (k : ℝ)*d = (Real.sqrt k * Real.sqrt k) * d :=
           congrArg (fun x : ℝ => x * d) (Real.mul_self_sqrt hkr.le).symm
         _ = Real.sqrt k * ((d : ℝ) * Real.sqrt k) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hdroot (Real.sqrt_nonneg _)
  have hknr : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hkprod : (k : ℝ) ≤ Real.sqrt k * Real.sqrt n := by
    calc (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hkr.le).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hknr) (Real.sqrt_nonneg _)
  have hreal : (distinctDistancesFrom pts p : ℝ) ≤ k + 3*(k:ℝ)*((d:ℝ)+1) := by
    exact_mod_cast hcount
  linarith

theorem main : H1 → H2 → type_of% @Erdos652.erdos_652.variants.order_sqrt := by
  rintro ⟨c, hc, hinc⟩ rect
  refine ⟨c / 2, 8, by positivity, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hu := admissible_of_rectangle rect k hk
  change c / 2 * Real.sqrt k ≤ sInf {a : ℝ | AdmissibleConstant k a} ∧
    sInf {a : ℝ | AdmissibleConstant k a} ≤ 8 * Real.sqrt k
  constructor
  · exact le_csInf ⟨_, hu⟩ fun a ha => admissible_lower hk (hinc k hk) ha
  · exact csInf_le ⟨0, fun a ha => ha.1.le⟩ hu

end OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1
end

section

/-! Specialize Mathialagan's bound, proved in #2684, to the nested-center step of #1867.
Credit: @JaviSoto. -/

section
/- # Mathialagan's bipartite distinct-distance theorem

Formalizes the planar crossing argument of Surya Mathialagan (2021), Theorem 14.
The planar edge inequality, the drawing by cut circle arcs, and the counting
argument are proved below. -/

/- # Euler's edge bound for simple graphs drawn by arcs in the plane

Split each arc into two vertex branches and a middle connector. Rounding the compact pieces
together to a fine square grid preserves their intersections and connectedness. This realizes
the graph as a minor of a finite grid subgraph. Discrete integration identifies grid circulations
with the differences of face potentials, a property preserved by contracting connected branch
sets. Rank-nullity and counting the nonzero entries of face boundaries give `E ≤ 3V`.
Credit: @JaviSoto. -/

section

/- Discretization of compact connected drawings by connected subgraphs of the square lattice. -/

open Set Filter Topology

namespace OMA.Grid652

/-- Integer lattice with the four axis-aligned unit steps. -/
def squareGrid : SimpleGraph (ℤ × ℤ) where
  Adj v w := (v.1 = w.1 ∧ |v.2 - w.2| = 1) ∨ (v.2 = w.2 ∧ |v.1 - w.1| = 1)
  symm := ⟨by
    intro v w h
    rcases h with ⟨h,k⟩ | ⟨h,k⟩
    · exact Or.inl ⟨h.symm, (abs_sub_comm _ _).trans k⟩
    · exact Or.inr ⟨h.symm, (abs_sub_comm _ _).trans k⟩⟩
  loopless := ⟨by intro v; simp⟩

noncomputable def snap (p : ℝ × ℝ) : ℤ × ℤ := (⌊p.1⌋, ⌊p.2⌋)

/-- The nine grid vertices centered on the lower-left corner of the unit square containing p. -/
def pixel (p : ℝ × ℝ) : Set (ℤ × ℤ) :=
  {v | |v.1 - (snap p).1| ≤ 1 ∧ |v.2 - (snap p).2| ≤ 1}

def raster (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) := {v | ∃ p ∈ K, v ∈ pixel p}

lemma snap_mem (p : ℝ × ℝ) : snap p ∈ pixel p := by simp [pixel]

lemma floor_close {a b : ℝ} (hab : |a - b| < 1) : |⌊a⌋ - ⌊b⌋| ≤ 1 := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hab
  have h₃ := Int.floor_le a
  have h₄ := Int.floor_le b
  have h₅ := Int.lt_floor_add_one a
  have h₆ := Int.lt_floor_add_one b
  have h₇ : (⌊a⌋ : ℝ) < (⌊b⌋ : ℝ) + 2 := by linarith
  have h₈ : (⌊b⌋ : ℝ) < (⌊a⌋ : ℝ) + 2 := by linarith
  have h₉ : ⌊a⌋ < ⌊b⌋ + 2 := by exact_mod_cast h₇
  have h₁₀ : ⌊b⌋ < ⌊a⌋ + 2 := by exact_mod_cast h₈
  rw [abs_le]
  omega

lemma snap_mem_of_close {p q : ℝ × ℝ} (h : dist q p < 1) : snap q ∈ pixel p := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at h
  exact ⟨floor_close h.1, floor_close h.2⟩

lemma pixel_reachable {S : Set (ℤ × ℤ)} {p : ℝ × ℝ} (hS : pixel p ⊆ S)
    {v : ℤ × ℤ} (hv : v ∈ pixel p) :
    (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨v, hS hv⟩ := by
  obtain ⟨hx,hy⟩ := hv
  let m : ℤ × ℤ := (v.1, (snap p).2)
  have hm : m ∈ pixel p := ⟨hx, by simp [m]⟩
  have h₁ : (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨m, hS hm⟩ := by
    by_cases h : v.1 = (snap p).1
    · have he : (⟨snap p, hS (snap_mem p)⟩ : S) = ⟨m, hS hm⟩ :=
        Subtype.ext (Prod.ext h.symm rfl)
      rw [he]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.induce_adj]
      apply Or.inr
      have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
      exact ⟨rfl, by rw [abs_sub_comm]; change |v.1 - (snap p).1| = 1; omega⟩
  apply h₁.trans
  by_cases h : v.2 = (snap p).2
  · have he : (⟨m, hS hm⟩ : S) = ⟨v, hS ⟨hx,hy⟩⟩ := Subtype.ext (Prod.ext rfl h.symm)
    rw [he]
  · apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.induce_adj]
    apply Or.inl
    have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
    exact ⟨rfl, by rw [abs_sub_comm]; change |v.2 - (snap p).2| = 1; omega⟩

lemma raster_preconnected {K : Set (ℝ × ℝ)} (hK : IsPreconnected K) :
    (squareGrid.induce (raster K)).Preconnected := by
  let toVertex (p : K) : raster K := ⟨snap p.val, p.val, p.property, snap_mem _⟩
  have sameComponent (p q : K) (h : dist q.val p.val < 1) :
      (squareGrid.induce (raster K)).Reachable (toVertex p) (toVertex q) :=
    pixel_reachable (S := raster K) (p := p.val) (fun _ hv => ⟨p.val, p.property,hv⟩)
      (snap_mem_of_close h)
  intro a b
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  let P (z : K) := (squareGrid.induce (raster K)).Reachable (toVertex ⟨x,hx⟩) (toVertex z)
  have hl : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro z
    filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < 1 by norm_num)] with w hw
    have h := sameComponent z w hw
    exact propext ⟨(·.trans h.symm), (·.trans h)⟩
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hxy : P ⟨y,hy⟩ := (hl.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨x,hx⟩).symm ▸
    SimpleGraph.Reachable.refl _
  exact (pixel_reachable (S := raster K) (p := x) (fun _ hv => ⟨x,hx,hv⟩) hax).symm.trans
    (hxy.trans (pixel_reachable (S := raster K) (p := y) (fun _ hv => ⟨y,hy,hv⟩) hby))

lemma raster_finite {K : Set (ℝ × ℝ)} (hK : IsCompact K) : (raster K).Finite := by
  obtain ⟨lx,hlx⟩ := (hK.image continuous_fst).bddBelow
  obtain ⟨ly,hly⟩ := (hK.image continuous_snd).bddBelow
  obtain ⟨ux,hux⟩ := (hK.image continuous_fst).bddAbove
  obtain ⟨uy,huy⟩ := (hK.image continuous_snd).bddAbove
  apply (Set.finite_Icc (⌊lx⌋ - 1, ⌊ly⌋ - 1) (⌊ux⌋ + 1, ⌊uy⌋ + 1)).subset
  rintro v ⟨p,hp,hx,hy⟩
  have ax' : ⌊lx⌋ ≤ ⌊p.1⌋ := Int.floor_mono (hlx ⟨p,hp,rfl⟩)
  have ay' : ⌊ly⌋ ≤ ⌊p.2⌋ := Int.floor_mono (hly ⟨p,hp,rfl⟩)
  have bx' : ⌊p.1⌋ ≤ ⌊ux⌋ := Int.floor_mono (hux ⟨p,hp,rfl⟩)
  have by'' : ⌊p.2⌋ ≤ ⌊uy⌋ := Int.floor_mono (huy ⟨p,hp,rfl⟩)
  change |v.1 - ⌊p.1⌋| ≤ 1 at hx
  change |v.2 - ⌊p.2⌋| ≤ 1 at hy
  rw [abs_le] at hx hy
  exact ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩⟩

noncomputable def scale (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1/h, p.2/h)

lemma scale_continuous (h : ℝ) : Continuous (scale h) :=
  (continuous_fst.div_const h).prodMk (continuous_snd.div_const h)

def rasterAt (h : ℝ) (K : Set (ℝ × ℝ)) := raster (scale h '' K)

private lemma pixel_error {z : ℤ} {p h : ℝ} (hh : 0 < h) (hz : |z - ⌊p/h⌋| ≤ 1) :
    |h * z - p| < 2*h := by
  have h₁ := Int.floor_le (p/h)
  have h₂ := Int.lt_floor_add_one (p/h)
  obtain ⟨hx,hy⟩ := abs_le.mp hz
  have hx' : (-1 : ℝ) ≤ z - (⌊p/h⌋ : ℤ) := by exact_mod_cast hx
  have hy' : (z : ℝ) - (⌊p/h⌋ : ℤ) ≤ 1 := by exact_mod_cast hy
  have h₃ := (le_div_iff₀ hh).mp h₁
  have h₄ := (div_lt_iff₀ hh).mp h₂
  rw [abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hx' hh.le,
    mul_le_mul_of_nonneg_right hy' hh.le]

lemma rasterAt_thickening {z : ℤ × ℤ} {h : ℝ} {K : Set (ℝ × ℝ)}
    (hh : 0 < h) (hz : z ∈ rasterAt h K) :
    (h * z.1, h * z.2) ∈ Metric.thickening (2*h) K := by
  obtain ⟨_,⟨p,hp,rfl⟩,hx,hy⟩ := hz
  apply Metric.mem_thickening_iff.mpr
  refine ⟨p,hp,?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨pixel_error hh hx, pixel_error hh hy⟩

lemma eventually_rasterAt_disjoint_iff {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), Disjoint (rasterAt h K) (rasterAt h L) ↔ Disjoint K L := by
  by_cases hd : Disjoint K L
  · obtain ⟨r,hr,hsep⟩ := hd.exists_thickenings hK hL.isClosed
    have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < r/2 :=
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhr
    refine ⟨fun _ => hd,fun _ => Set.disjoint_left.mpr ?_⟩
    intro z hz hw
    have hlt : 2*h ≤ r := by linarith
    exact Set.disjoint_left.mp hsep
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hz))
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hw))
  · filter_upwards with h
    refine ⟨fun hgrid => ?_, fun hdis => (hd hdis).elim⟩
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp hgrid
      (show snap (scale h p) ∈ rasterAt h K from ⟨_,⟨p,hp,rfl⟩,snap_mem _⟩)
      (show snap (scale h p) ∈ rasterAt h L from ⟨_,⟨p,hq,rfl⟩,snap_mem _⟩)

/-- A finite family of compact connected plane sets admits finite connected lattice models
    with exactly the same intersection relation, and the mesh may be chosen arbitrarily fine. -/
theorem finite_grid_realization {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∀ i, (rasterAt h (K i)).Finite ∧ (squareGrid.induce (rasterAt h (K i))).Preconnected) ∧
      (∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j)) := by
  have pairs : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j) := by
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_rasterAt_disjoint_iff (hc i) (hc j)
  filter_upwards [pairs] with h hh
  exact ⟨fun i => ⟨raster_finite ((hc i).image (scale_continuous h)),
    raster_preconnected ((hp i).image _ (scale_continuous h).continuousOn)⟩, hh⟩

open scoped EuclideanGeometry

def coords (p : ℝ²) : ℝ × ℝ := (p 0, p 1)

lemma coords_injective : Function.Injective coords := by
  intro p q h
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma coords_continuous : Continuous coords :=
  (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 1)

/-- Joint rasterization for the formal conjecture's Euclidean-space model, including empty sets. -/
theorem plane_grid_realization {ι : Type*} [Finite ι] (K : ι → Set ℝ²)
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∃ A : ι → Set (ℤ × ℤ),
      (∀ i, (A i).Finite ∧ (squareGrid.induce (A i)).Preconnected) ∧
      (∀ i j, Disjoint (A i) (A j) ↔ Disjoint (K i) (K j)) := by
  obtain ⟨h, h₁, h₂⟩ := (finite_grid_realization (fun i => coords '' K i)
    (fun i => (hc i).image coords_continuous)
    (fun i => (hp i).image _ coords_continuous.continuousOn)).exists
  exact ⟨_,h₁,fun i j => (h₂ i j).trans (Set.disjoint_image_iff coords_injective)⟩


end OMA.Grid652

/- Face potentials under deletion and contraction of finite directed networks. -/

open scoped BigOperators

namespace OMA.Grid652

variable {W V E J F : Type*}

noncomputable def atom (w : W) (u : W) : ℚ := by classical exact if w = u then 1 else 0

/-- Push a function of finite support forward, summing its coefficients over each fiber. -/
noncomputable def push [Fintype W] (f : W → V) : (W → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun z := ∑ w, z w • atom (f w)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.smul_sum, mul_smul]

lemma push_atom [Fintype W] (f : W → V) (w : W) : push f (atom w) = atom (f w) := by
  classical
  change (∑ u, (if w = u then (1 : ℚ) else 0) • atom (f u)) = _
  simp [ite_smul]

lemma push_comp [Fintype W] [Fintype V] {U : Type*} (f : W → V) (g : V → U)
    (z : W → ℚ) : push g (push f z) = push (g ∘ f) z := by
  change push g (∑ w, z w • atom (f w)) = _
  simp only [map_sum, map_smul, push_atom]
  rfl

lemma push_id [Fintype W] (z : W → ℚ) : push id z = z := by
  classical
  ext w
  simp [push, atom]

noncomputable def net [Fintype E] (s t : E → V) : (E → ℚ) →ₗ[ℚ] (V → ℚ) :=
  push t - push s

lemma net_atom [Fintype E] (s t : E → V) (e : E) : net s t (atom e) = atom (t e) - atom (s e) := by
  simp [net, push_atom]

lemma net_push [Fintype W] [Fintype E] (s t : E → W) (π : W → V) (z : E → ℚ) :
    push π (net s t z) = net (π ∘ s) (π ∘ t) z := by simp [net, map_sub, push_comp]

lemma net_sum [Fintype E] [Fintype J] (s t : E ⊕ J → W) (z : E → ℚ) (w : J → ℚ) :
    net s t (Sum.elim z w) =
      net (s ∘ Sum.inl) (t ∘ Sum.inl) z + net (s ∘ Sum.inr) (t ∘ Sum.inr) w := by
  simp [net, push, Fintype.sum_sum_type]
  abel

/-- An exact dual means the divergence-free flows are exactly the edge differences of
    face potentials. The face on either side need not be different. -/
def ExactDual [Fintype E] (s t : E → V) (l r : E → F) : Prop :=
  ∀ z : E → ℚ, net s t z = 0 ↔ ∃ c : F → ℚ, ∀ e, z e = c (l e) - c (r e)

/-- Connectedness of a fiber is needed only to route the difference of two unit sources
    along its internal edges. The equivalence closure of edge endpoint pairs suffices. -/
lemma atom_sub_mem_range_of_joined [Fintype J] (s t : J → W) {a b : W}
    (h : Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) a b) :
    atom b - atom a ∈ LinearMap.range (net s t) := by
  induction h with
  | rel a b h =>
    obtain ⟨j,rfl,rfl⟩ := h
    exact ⟨atom j,net_atom s t j⟩
  | refl a => simp
  | symm a b _ ih => simpa using (LinearMap.range (net s t)).neg_mem ih
  | trans a b c _ _ ih₁ ih₂ =>
    convert (LinearMap.range (net s t)).add_mem ih₂ ih₁ using 1
    abel

lemma mem_internal_range [Fintype J] [Fintype W] [Fintype V] (s t : J → W)
    (π : W → V) (anchor : V → W)
    (joined : ∀ w, Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) (anchor (π w)) w)
    {b : W → ℚ} (hb : push π b = 0) :
    b ∈ LinearMap.range (net s t) := by
  have h₁ : (∑ w, b w • (atom w - atom (anchor (π w)))) ∈ LinearMap.range (net s t) :=
    Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (atom_sub_mem_range_of_joined s t (joined w))
  have h₂ : push (anchor ∘ π) b = 0 := by rw [← push_comp, hb, map_zero]
  simp only [smul_sub, Finset.sum_sub_distrib] at h₁
  change push id b - push (anchor ∘ π) b ∈ _ at h₁
  simpa [push_id, h₂] using h₁

/-- Contract connected internal branch sets by forgetting their edges in the dual. -/
theorem exactDual_contract [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (l r : E ⊕ J → F) (hD : ExactDual s t l r)
    (π : W → V) (anchor : V → W) (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w) :
    ExactDual (π ∘ s ∘ Sum.inl) (π ∘ t ∘ Sum.inl) (l ∘ Sum.inl) (r ∘ Sum.inl) := by
  have collapsed (w : J → ℚ) : push π (net (s ∘ Sum.inr) (t ∘ Sum.inr) w) = 0 := by
    rw [net_push]
    have heq : π ∘ s ∘ Sum.inr = π ∘ t ∘ Sum.inr := funext internal
    simp [heq, net]
  intro z
  constructor
  · intro hz
    obtain ⟨w,hw⟩ := mem_internal_range (s ∘ Sum.inr) (t ∘ Sum.inr) π anchor joined
      (b := -net (s ∘ Sum.inl) (t ∘ Sum.inl) z) (by rw [map_neg, net_push, hz, neg_zero])
    have hfull : net s t (Sum.elim z w) = 0 := by rw [net_sum, hw, add_neg_cancel]
    obtain ⟨c,hc⟩ := (hD _).mp hfull
    exact ⟨c,fun e => hc (.inl e)⟩
  · rintro ⟨c,hc⟩
    let w (j : J) := c (l (.inr j)) - c (r (.inr j))
    have hfull : net s t (Sum.elim z w) = 0 :=
      (hD _).mpr ⟨c,fun e => by cases e with | inl e => exact hc e | inr j => rfl⟩
    have hh := congrArg (push π) hfull
    simpa only [net_sum, map_add, collapsed, add_zero, net_push, map_zero] using hh

abbrev GridPoint := ℤ × ℤ
abbrev GridEdge := GridPoint ⊕ GridPoint

/-- Each oriented edge is indexed by its head, with horizontal edges in the left summand. -/
def gridHead : GridEdge → GridPoint := Sum.elim id id
def gridTail : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1-1,p.2)) (fun p => (p.1,p.2-1))
def faceLeft : GridEdge → GridPoint :=
  Sum.elim id (fun p => (p.1+1,p.2))
def faceRight : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1,p.2+1)) id

/-- A discrete integral on all integer coordinates, based at zero. -/
def primitive (f : ℤ → ℚ) (x : ℤ) : ℚ :=
  x.inductionOn' 0 0 (fun i _ a => a + f i) (fun i _ a => a - f (i-1))

lemma primitive_zero (f : ℤ → ℚ) : primitive f 0 = 0 := Int.inductionOn'_self

lemma primitive_succ (f : ℤ → ℚ) (x : ℤ) : primitive f (x+1) = primitive f x + f x := by
  by_cases hx : 0 ≤ x
  · exact Int.inductionOn'_add_one hx
  · have he : primitive f (x+1-1) = primitive f (x+1) - f (x+1-1) :=
      Int.inductionOn'_sub_one (by omega : x+1 ≤ (0:ℤ))
    simp only [add_sub_cancel_right] at he
    linarith

lemma grid_integral (H V : ℤ → ℤ → ℚ)
    (hdiv : ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j) :
    ∃ c : GridPoint → ℚ, (∀ i j, H i j = c (i,j) - c (i,j+1)) ∧
      (∀ i j, V i j = c (i+1,j) - c (i,j)) := by
  let c (p : GridPoint) := primitive (fun i => V i p.2) p.1 - primitive (H 0) p.2
  have hv (i j : ℤ) : c (i+1,j) = c (i,j) + V i j := by simp [c, primitive_succ]; ring
  refine ⟨c,?_,fun i j => by rw [hv]; ring⟩
  intro i j
  have step (i : ℤ) :
      (H i j = c (i,j) - c (i,j+1)) ↔ (H (i+1) j = c (i+1,j) - c (i+1,j+1)) := by
    rw [hv, hv]
    constructor <;> intro hh <;> linarith [hdiv i j]
  refine Int.inductionOn' i 0 ?_ (fun n _ => (step n).mp) ?_
  · simp [c,primitive_zero,primitive_succ]
  · intro n _ ih
    apply (step (n-1)).mpr
    simpa using ih

lemma push_inj_apply [Fintype E] (f : E → W) (hf : Function.Injective f) (z : E → ℚ) (e : E) :
    push f z (f e) = z e := by
  classical
  simp [push, atom, hf.eq_iff, mul_ite]

lemma push_outside [Fintype E] (f : E → W) (z : E → ℚ) (w : W) (hw : w ∉ Set.range f) :
    push f z w = 0 := by
  classical
  have hn : ∀ e, f e ≠ w := fun e he => hw ⟨e,he⟩
  simp [push,atom,hn]

private lemma head_atom (e : GridEdge) (i j : ℤ) :
    atom (gridHead e) (i,j) = atom e (.inl (i,j)) + atom e (.inr (i,j)) := by
  classical
  cases e with
  | inl p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]
  | inr p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]

private lemma tail_atom (e : GridEdge) (i j : ℤ) :
    atom (gridTail e) (i,j) = atom e (.inl (i+1,j)) + atom e (.inr (i,j+1)) := by
  classical
  rcases e with ⟨x,y⟩ | ⟨x,y⟩ <;> simp [gridTail,atom,Prod.mk.injEq,sub_eq_iff_eq_add]

lemma grid_net_apply [Fintype E] (key : E → GridEdge) (z : E → ℚ) (i j : ℤ) :
    net (gridTail ∘ key) (gridHead ∘ key) z (i,j) =
      (push key z (.inl (i,j)) + push key z (.inr (i,j))) -
      (push key z (.inl (i+1,j)) + push key z (.inr (i,j+1))) := by
  classical
  simp [net, push, head_atom, tail_atom, mul_add, Finset.sum_add_distrib]

def missing (key : E → GridEdge) (a b : GridPoint) : Prop :=
  ∃ d ∉ Set.range key, faceLeft d = a ∧ faceRight d = b

/-- Every finite subgraph of the infinite square lattice has an exact dual. Faces are
    obtained by identifying neighboring unit squares across all omitted grid edges. -/
theorem grid_exactDual [Fintype E] (key : E → GridEdge) (inj : Function.Injective key) :
    ExactDual (gridTail ∘ key) (gridHead ∘ key)
      (Quot.mk (missing key) ∘ faceLeft ∘ key) (Quot.mk (missing key) ∘ faceRight ∘ key) := by
  classical
  intro z
  let H (i j : ℤ) := push key z (.inl (i,j))
  let V (i j : ℤ) := push key z (.inr (i,j))
  have diviff : net (gridTail ∘ key) (gridHead ∘ key) z = 0 ↔
      ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j := by
    constructor
    · intro hz i j
      have he := congrFun hz (i,j)
      rw [grid_net_apply] at he
      exact (sub_eq_zero.mp he).symm
    · intro he
      funext ⟨i,j⟩
      exact (grid_net_apply key z i j).trans (sub_eq_zero.mpr (he i j).symm)
  rw [diviff]
  constructor
  · intro hdiv
    obtain ⟨c,hH,hV⟩ := grid_integral H V hdiv
    have hgrad (e : GridEdge) : push key z e = c (faceLeft e) - c (faceRight e) := by
      rcases e with ⟨i,j⟩ | ⟨i,j⟩
      · exact hH i j
      · exact hV i j
    have compat : ∀ a b, missing key a b → c a = c b := by
      rintro _ _ ⟨e,he,rfl,rfl⟩
      exact sub_eq_zero.mp ((hgrad e).symm.trans (push_outside key z e he))
    exact ⟨Quot.lift c compat,fun e => (push_inj_apply key inj z e).symm.trans (hgrad (key e))⟩
  · rintro ⟨c,hc⟩
    let q := Quot.mk (missing key)
    have he (d : GridEdge) : push key z d = c (q (faceLeft d)) - c (q (faceRight d)) := by
      by_cases hd : d ∈ Set.range key
      · obtain ⟨e,rfl⟩ := hd
        exact (push_inj_apply key inj z e).trans (hc e)
      · have hq : q (faceLeft d) = q (faceRight d) := Quot.sound ⟨d,hd,rfl,rfl⟩
        simp [hq, push_outside key z d hd]
    intro i j
    dsimp only [H,V]
    rw [he,he,he,he]
    simp [faceLeft,faceRight]

end OMA.Grid652

/- A linear-algebraic Euler bound from the two faces on either side of an edge.
    Neither facial walks nor a choice of spanning trees are required. -/

open Set Matrix Module
open scoped BigOperators

namespace OMA.Grid652

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable {k : Type*} [Field k]

omit [Fintype V] in
/-- A nonzero circulation on a finite simple graph uses at least three edges. Both the
    ordinary oriented incidence matrix and the unsigned matrix over ZMod 2 satisfy this. -/
lemma circulation_support_card [DecidableEq k] (edge : E → Finset V)
    (two : ∀ e, (edge e).card = 2) (simple : Function.Injective edge)
    (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    {z : E → k} (hne : z ≠ 0) (hcycle : M.mulVec z = 0) :
    3 ≤ (Finset.univ.filter fun e => z e ≠ 0).card := by
  classical
  let S := Finset.univ.filter fun e => z e ≠ 0
  have hs {e : E} : e ∈ S ↔ z e ≠ 0 := by simp [S]
  have another {e : E} (he : e ∈ S) {v : V} (hv : v ∈ edge e) :
      ∃ f ∈ S.erase e, v ∈ edge f := by
    by_contra! no
    have eq : (M.mulVec z) v = M v e * z e := by
      apply Finset.sum_eq_single e
      · intro f _ hfe
        by_cases hf : f ∈ S
        · have hvf := no f (Finset.mem_erase.mpr ⟨hfe,hf⟩)
          have hM : M v f = 0 := not_ne_iff.mp (fun hp => hvf ((suppM v f).mp hp))
          simp [hM]
        · have hz : z f = 0 := by simpa [S] using hf
          simp [hz]
      · simp
    have hzero : (M.mulVec z) v = 0 := congrFun hcycle v
    exact (mul_ne_zero ((suppM v e).mpr hv) (hs.mp he)) (eq.symm.trans hzero)
  by_contra! hcard
  have hz : ∃ e, z e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e,he⟩ := hz
  have hem := hs.mpr he
  have hone : (S.erase e).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hem]
    change S.card < 3 at hcard
    omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [two]; decide : 0 < (edge e).card)
  obtain ⟨f,hf,_⟩ := another hem hv
  have sub : edge e ⊆ edge f := by
    intro w hw
    obtain ⟨g,hg,hwg⟩ := another hem hw
    exact (Finset.card_le_one.mp hone g hg f hf) ▸ hwg
  have heq : e = f := simple (Finset.eq_of_subset_of_card_le sub (by rw [two,two]))
  exact (Finset.mem_erase.mp hf).1 heq.symm

/-- Boundary of one dual face. Its value on a primal edge is determined by the two
    adjacent faces, which may coincide. -/
noncomputable def faceBoundary (l r : E → F) (f : F) (e : E) : k := by
  classical exact (if l e = f then 1 else 0) - (if r e = f then 1 else 0)

/-- Euler's weak edge bound for graphs whose cycle space is generated by edge differences
    of face potentials and whose individual face boundaries have zero divergence. -/
theorem euler_of_face_potentials (edge : E → Finset V) (two : ∀ e, (edge e).card = 2)
    (simple : Function.Injective edge) (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    (l r : E → F) (hface : ∀ f, M.mulVec (faceBoundary l r f) = 0)
    (hfill : ∀ z : E → k, M.mulVec z = 0 → ∃ c : F → k, ∀ e, z e = c (l e) - c (r e)) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let B := faceBoundary (k := k) l r
  let A : Finset F := Finset.univ.filter fun f => B f ≠ 0
  have doubleCount : A.card • (3 : ℕ) ≤ (Finset.univ : Finset E).card • 2 := by
    apply Finset.card_nsmul_le_card_nsmul (fun f e => B f e ≠ 0)
    · intro f hf
      exact circulation_support_card edge two simple M suppM
        (Finset.mem_filter.mp hf).2 (hface f)
    · intro e _
      apply le_trans (Finset.card_le_card (t := {l e,r e}) ?_) Finset.card_le_two
      intro f hf
      by_contra! hn
      have hz := (Finset.mem_filter.mp hf).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      exact hz (by simp [B, faceBoundary, Ne.symm hn.1, Ne.symm hn.2])
  let column (f : A) := B f.val
  have hspan : LinearMap.ker M.mulVecLin ≤ Submodule.span k (Set.range column) := by
    intro z hz
    obtain ⟨c,hc⟩ := hfill z (by exact hz)
    have hcomb : z = ∑ f : F, c f • B f := by
      ext e
      rw [hc]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B, faceBoundary,
        mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
      simp
    rw [hcomb]
    apply Submodule.sum_mem
    intro f _
    by_cases hf : f ∈ A
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f,hf⟩,rfl⟩)
    · have hzero : B f = 0 := by simpa [A] using hf
      simp [hzero]
  have hker := (Submodule.finrank_mono hspan).trans (finrank_range_le_card (R := k) column)
  have hrange := (LinearMap.range M.mulVecLin).finrank_le
  have htotal := M.mulVecLin.finrank_range_add_finrank_ker
  simp only [finrank_pi, Fintype.card_coe] at hker hrange htotal
  have hcount : A.card * 3 ≤ Fintype.card E * 2 := by simpa using doubleCount
  omega

end OMA.Grid652

/- Every simple graph represented by disjoint connected branch sets in a finite square-grid
    subgraph has at most three times as many edges as vertices. -/

open Set Matrix Module

namespace OMA.Grid652

variable {W V E J F : Type*}

lemma exactDual_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (different : ∀ e, s e ≠ t e)
    (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (l r : E → F) (hD : ExactDual s t l r) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let D := Finset.univ.image l ∪ Finset.univ.image r
  let L (e : E) : D := ⟨l e,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let R (e : E) : D := ⟨r e,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let M (v : V) (e : E) := atom (t e) v - atom (s e) v
  have eq (z : E → ℚ) : Matrix.mulVec M z = net s t z := by
    ext v
    simp [Matrix.mulVec,dotProduct,M,net,push,mul_comm,mul_sub,Finset.sum_sub_distrib]
  apply euler_of_face_potentials (fun e => ({s e,t e} : Finset V)) (fun e => by simp [different e])
    simple M _ L R
  · intro f
    rw [eq]
    apply (hD _).mpr
    refine ⟨fun p => atom p f.val,fun e => ?_⟩
    simp only [faceBoundary,atom]
    have h₁ : (L e = f) ↔ l e = f.val := Subtype.ext_iff
    have h₂ : (R e = f) ↔ r e = f.val := Subtype.ext_iff
    simp [h₁,h₂]
  · intro z hz
    obtain ⟨c,hc⟩ := (hD _).mp ((eq z).symm.trans hz)
    exact ⟨fun p => c p.val,hc⟩
  · intro v e
    by_cases h : s e = v
    · subst v
      simp [M,atom,(different e).symm]
    · by_cases h' : t e = v
      · subst v
        simp [M,atom,h]
      · simp [M,atom,h,h',Ne.symm h,Ne.symm h']

/-- Extending a finite network along an injective vertex map leaves its cycle space unchanged. -/
lemma injective_net [Fintype E] [Fintype W] (s t : E → W) (p : W → V)
    (hp : Function.Injective p) (z : E → ℚ) :
    net (p ∘ s) (p ∘ t) z = 0 ↔ net s t z = 0 := by
  rw [← net_push]
  refine ⟨fun h => funext fun w => ?_,fun h => by simp [h]⟩
  exact (push_inj_apply p hp _ w).symm.trans (congrFun h (p w))

/-- Exact planar edge bound for any simple grid minor: the finite network has one
    extra edge per desired graph edge and arbitrary connected internal branch edges. -/
theorem euler_grid_minor [DecidableEq V] [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (p : W → GridPoint) (hp : Function.Injective p)
    (key : E ⊕ J → GridEdge) (inj : Function.Injective key)
    (tail : gridTail ∘ key = p ∘ s) (head : gridHead ∘ key = p ∘ t)
    (π : W → V) (anchor : V → W)
    (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w)
    (different : ∀ e : E, π (s (.inl e)) ≠ π (t (.inl e)))
    (simple : Function.Injective (fun e : E => ({π (s (.inl e)),π (t (.inl e))} : Finset V))) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let l := Quot.mk (missing key) ∘ faceLeft ∘ key
  let r := Quot.mk (missing key) ∘ faceRight ∘ key
  have hD : ExactDual s t l r := by
    intro z
    have hD := grid_exactDual key inj z
    rw [tail,head,injective_net s t p hp] at hD
    exact hD
  exact exactDual_bound _ _ different simple _ _ (exactDual_contract s t l r hD π anchor internal joined)

end OMA.Grid652

/- Turn a family of disjoint vertex patches and disjoint edge connectors into a grid minor. -/

open Set

namespace OMA.Grid652

variable {X V E : Type*}

/-- Follow a walk until it first touches the target, retaining its connected prefix. -/
lemma before_target (G : SimpleGraph X) {C T : Set X} {a b : C}
    (p : (G.induce C).Walk a b) (ha : a.val ∉ T) (hb : b.val ∈ T) :
    ∃ D : Set X, D ⊆ C ∧ a.val ∈ D ∧ Disjoint D T ∧ (G.induce D).Preconnected ∧
      ∃ x ∈ D, ∃ y ∈ T, G.Adj x y := by
  classical
  induction p with
  | nil => exact (ha hb).elim
  | @cons a u b au p ih =>
    by_cases hu : u.val ∈ T
    · refine ⟨{a.val},Set.singleton_subset_iff.mpr a.property,rfl,?_,?_,a.val,rfl,u.val,hu,au⟩
      · simpa using ha
      · intro x y
        have he : x = y := Subtype.ext (x.property.trans y.property.symm)
        rw [he]
    · obtain ⟨D,hDC,huD,hd,hc,tail⟩ := ih hu hb
      let S : Set X := {a.val,u.val}
      have aS : a.val ∈ S := by simp [S]
      have uS : u.val ∈ S := by simp [S]
      refine ⟨S ∪ D,Set.union_subset ?_ hDC, Or.inl aS,disjoint_union_left.mpr ⟨?_,hd⟩,?_,?_⟩
      · intro x hx
        rcases hx with rfl | h
        · exact a.property
        · exact h ▸ u.property
      · intro I hS hT x hx
        rcases hS hx with he | he
        · exact ha (he ▸ hT hx)
        · exact hu (he ▸ hT hx)
      · exact (G.induce_union_connected (G.induce_pair_connected_of_adj au).preconnected hc
          ⟨u.val,uS,huD⟩).preconnected
      · obtain ⟨x,hx,y,hy,hxy⟩ := tail
        exact ⟨x,Or.inr hx,y,hy,hxy⟩

lemma patches_reach {G : SimpleGraph X} {A B : Set X} (h : A ⊆ B)
    {x y : A} (p : (G.induce A).Reachable x y) :
    (G.induce B).Reachable ⟨x.val,h x.property⟩ ⟨y.val,h y.property⟩ := by
  exact p.map (⟨Set.inclusion h,fun {a b} ha => ha⟩ : G.induce A →g G.induce B)

/-- A bipartite incidence model whose connector patches meet only their two prescribed
    end patches can be refined to disjoint connected branch sets with a single adjacency
    for each edge. -/
theorem shrink_connectors [Finite E] (G : SimpleGraph X) (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (B : V → Set X) (C : E → Set X)
    (Bfin : ∀ v, (B v).Finite) (Cfin : ∀ e, (C e).Finite)
    (Bne : ∀ v, (B v).Nonempty) (Bconn : ∀ v, (G.induce (B v)).Preconnected)
    (Cconn : ∀ e, (G.induce (C e)).Preconnected)
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    ∃ R : V → Set X, (∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (G.induce (R v)).Preconnected) ∧
      (∀ v w, v ≠ w → Disjoint (R v) (R w)) ∧
      ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), G.Adj x y := by
  classical
  have expandBranch (e : E) : ∃ D : Set X, D ⊆ C e ∧ (D ∩ B (s e)).Nonempty ∧
      Disjoint D (B (t e)) ∧ (G.induce D).Preconnected ∧ ∃ x ∈ D, ∃ y ∈ B (t e), G.Adj x y := by
    obtain ⟨x,hx,hxs⟩ := Set.not_disjoint_iff.mp ((touch e (s e)).mpr (Or.inl rfl))
    obtain ⟨y,hy,hyt⟩ := Set.not_disjoint_iff.mp ((touch e (t e)).mpr (Or.inr rfl))
    have hxt := Set.disjoint_left.mp (BB _ _ (hne e)) hxs
    obtain ⟨p⟩ := Cconn e ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨D,hDC,hxD,hdt,hD,htouch⟩ := before_target G p hxt hyt
    exact ⟨D,hDC,⟨x,hxD,hxs⟩,hdt,hD,htouch⟩
  choose D sub inter avoid conn bridge using expandBranch
  let R (v : V) := B v ∪ ⋃ e : {e // s e = v}, D e.val
  have Bsub (v : V) : B v ⊆ R v := Set.subset_union_left
  have Dsub (e : E) : D e ⊆ R (s e) := fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨⟨e,rfl⟩,hx⟩)
  have avoid' (e : E) (v : V) (h : s e ≠ v) : Disjoint (D e) (B v) := by
    by_cases ht : t e = v
    · exact ht ▸ avoid e
    · apply Disjoint.mono_left (sub e)
      by_contra! hh
      exact ((touch e v).mp hh).elim h ht
  refine ⟨R,?_,?_,?_⟩
  · intro v
    refine ⟨(Bfin v).union (Set.finite_iUnion fun e => (Cfin e.val).subset (sub e.val)),
      (Bne v).mono (Bsub v),?_⟩
    obtain ⟨a,ha⟩ := Bne v
    have reaches (p : R v) : (G.induce (R v)).Reachable ⟨a,Bsub v ha⟩ p := by
      rcases p with ⟨p,hp | hp⟩
      · exact patches_reach (Bsub v) (Bconn v ⟨a,ha⟩ ⟨p,hp⟩)
      · obtain ⟨⟨e,rfl⟩,he⟩ := Set.mem_iUnion.mp hp
        obtain ⟨d,hd,hb⟩ := inter e
        exact (patches_reach (Bsub _) (Bconn _ ⟨a,ha⟩ ⟨d,hb⟩)).trans
          (patches_reach (Dsub e) (conn e ⟨d,hd⟩ ⟨p,he⟩))
    exact fun p q => (reaches p).symm.trans (reaches q)
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp (BB _ _ hvw) hx hy
    · obtain ⟨⟨e,he⟩,hy'⟩ := Set.mem_iUnion.mp hy
      exact Set.disjoint_left.mp (avoid' e v (he ▸ hvw.symm)) hy' hx
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (avoid' e w (he ▸ hvw)) hx' hy
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨f,hf⟩,hy'⟩ := Set.mem_iUnion.mp hy
      have hef : e ≠ f := fun h => hvw (he.symm.trans ((congrArg s h).trans hf))
      exact Set.disjoint_left.mp (CC _ _ hef) (sub _ hx') (sub _ hy')
  · intro e
    obtain ⟨x,hx,y,hy,h⟩ := bridge e
    exact ⟨x,Dsub e hx,y,Bsub _ hy,h⟩

/-- An undirected grid adjacency has a canonical horizontal or vertical orientation. -/
lemma grid_arrow {x y : GridPoint} (h : squareGrid.Adj x y) :
    (∃ d, gridTail d = x ∧ gridHead d = y) ∨ (∃ d, gridTail d = y ∧ gridHead d = x) := by
  obtain ⟨i,j⟩ := x
  obtain ⟨k,m⟩ := y
  rcases h with ⟨h,hd⟩ | ⟨h,hd⟩
  · change i = k at h
    subst k
    change |j - m| = 1 at hd
    rcases abs_choice (j-m) with hab | hab
    · exact Or.inr ⟨.inr (i,j),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
    · exact Or.inl ⟨.inr (i,m),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
  · change j = m at h
    subst m
    change |i - k| = 1 at hd
    rcases abs_choice (i-k) with hab | hab
    · exact Or.inr ⟨.inl (i,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩
    · exact Or.inl ⟨.inl (k,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩

/-- Construct the finite grid minor from the branch-set formulation. The orientation of
    each selected bridge follows the canonical orientation of its lattice edge. -/
theorem grid_branch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (R : V → Set GridPoint)
    (Rprop : ∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (squareGrid.induce (R v)).Preconnected)
    (Rdis : ∀ v w, v ≠ w → Disjoint (R v) (R w))
    (bridge : ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), squareGrid.Adj x y) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let (v : V) : Fintype (R v) := (Rprop v).1.fintype
  let W := (v : V) × R v
  let pos (w : W) : GridPoint := w.2.val
  have posinj : Function.Injective pos := by
    rintro ⟨v,x⟩ ⟨w,y⟩ he
    have hvw : v = w := by
      by_contra h
      exact Set.disjoint_left.mp (Rdis _ _ h) x.property ((show x.val = y.val from he) ▸ y.property)
    subst w
    exact congrArg (Sigma.mk v) (Subtype.ext he)
  have chooseBridge (e : E) : ∃ (a b : W) (d : GridEdge),
      (a.1 = s e ∧ b.1 = t e ∨ a.1 = t e ∧ b.1 = s e) ∧
      gridTail d = pos a ∧ gridHead d = pos b := by
    obtain ⟨x,hx,y,hy,hxy⟩ := bridge e
    rcases grid_arrow hxy with ⟨d,hd1,hd2⟩ | ⟨d,hd1,hd2⟩
    · exact ⟨⟨_,x,hx⟩,⟨_,y,hy⟩,d,Or.inl ⟨rfl,rfl⟩,hd1,hd2⟩
    · exact ⟨⟨_,y,hy⟩,⟨_,x,hx⟩,d,Or.inr ⟨rfl,rfl⟩,hd1,hd2⟩
  choose a b d owners tail head using chooseBridge
  have pairEq (e : E) : ({(a e).1,(b e).1} : Finset V) = {s e,t e} := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp [ha,hb]
    · rw [ha,hb,Finset.pair_comm]
  have distinct (e : E) : (a e).1 ≠ (b e).1 := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa [ha,hb] using hne e
    · simpa [ha,hb] using (hne e).symm
  let J := {p : W × W // p.1.1 = p.2.1 ∧ ∃ k, gridTail k = pos p.1 ∧ gridHead k = pos p.2}
  have hJ (j : J) := j.property.2
  choose d' jt jh using hJ
  let src : E ⊕ J → W := Sum.elim a (fun j => j.val.1)
  let dst : E ⊕ J → W := Sum.elim b (fun j => j.val.2)
  let key : E ⊕ J → GridEdge := Sum.elim d d'
  have T (k : E ⊕ J) : gridTail (key k) = pos (src k) := by
    rcases k with e | j
    · exact tail e
    · exact jt j
  have H (k : E ⊕ J) : gridHead (key k) = pos (dst k) := by
    rcases k with e | j
    · exact head e
    · exact jh j
  have inj : Function.Injective key := by
    intro k k' he
    have hs := posinj ((T k).symm.trans ((congrArg gridTail he).trans (T k')))
    have ht := posinj ((H k).symm.trans ((congrArg gridHead he).trans (H k')))
    rcases k with e | j <;> rcases k' with f | i
    · apply congrArg Sum.inl
      apply simple
      exact (pairEq e).symm.trans ((congrArg₂ (fun x y : W => ({x.1,y.1} : Finset V)) hs ht).trans
        (pairEq f))
    · exfalso
      exact distinct e ((congrArg Sigma.fst hs).trans (i.property.1.trans (congrArg Sigma.fst ht).symm))
    · exfalso
      exact distinct f ((congrArg Sigma.fst hs).symm.trans (j.property.1.trans (congrArg Sigma.fst ht)))
    · exact congrArg Sum.inr (Subtype.ext (Prod.ext hs ht))
  let anchor (v : V) : W := ⟨v, Classical.choose (Rprop v).2.1, Classical.choose_spec (Rprop v).2.1⟩
  let rel (x y : W) := ∃ j : J, src (.inr j) = x ∧ dst (.inr j) = y
  have step {v : V} {x y : R v} (adj : (squareGrid.induce (R v)).Adj x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    rcases grid_arrow adj with h | h
    · exact .rel _ _ ⟨⟨(⟨v,x⟩,⟨v,y⟩),rfl,h⟩,rfl,rfl⟩
    · exact .symm _ _ (.rel _ _ ⟨⟨(⟨v,y⟩,⟨v,x⟩),rfl,h⟩,rfl,rfl⟩)
  have joins {v : V} {x y : R v} (p : (squareGrid.induce (R v)).Walk x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    induction p with
    | nil => exact .refl _
    | cons adj _ ih => exact .trans _ _ _ (step adj) ih
  apply euler_grid_minor src dst pos posinj key inj (funext T) (funext H) Sigma.fst anchor
    (fun j => j.property.1) _ distinct
  · intro e f he
    exact simple ((pairEq e).symm.trans (he.trans (pairEq f)))
  · rintro ⟨v,w⟩
    obtain ⟨p⟩ := (Rprop v).2.2 (anchor v).2 w
    exact joins p

open scoped EuclideanGeometry

/-- The Euler edge bound directly in terms of disjoint compact connected Euclidean patches
    and disjoint compact connected edge corridors with the prescribed incidence relation. -/
theorem grid_patch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (B : V → Set ℝ²) (C : E → Set ℝ²)
    (Bprop : ∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v))
    (Cprop : ∀ e, IsCompact (C e) ∧ IsPreconnected (C e))
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let K : V ⊕ E → Set ℝ² := Sum.elim B C
  obtain ⟨A,info,dis⟩ := plane_grid_realization K
    (fun i => by cases i with | inl v => exact (Bprop v).2.1 | inr e => exact (Cprop e).1)
    (fun i => by cases i with | inl v => exact (Bprop v).2.2 | inr e => exact (Cprop e).2)
  have nonempty (v : V) : (A (.inl v)).Nonempty := by
    by_contra! hn
    have hD := (dis (.inl v) (.inl v)).mp (by simp [hn])
    exact (Bprop v).1.ne_empty (disjoint_self.mp hD)
  obtain ⟨R,hR,hdis,hbridge⟩ := shrink_connectors squareGrid s t hne (A ∘ Sum.inl) (A ∘ Sum.inr)
    (fun v => (info (.inl v)).1) (fun e => (info (.inr e)).1) nonempty
    (fun v => (info (.inl v)).2) (fun e => (info (.inr e)).2)
    (fun v w h => (dis _ _).mpr (BB v w h)) (fun e f h => (dis _ _).mpr (CC e f h))
    (fun e v => (not_congr (dis (.inr e) (.inl v))).trans (touch e v))
  exact grid_branch_bound s t hne simple R hR hdis hbridge

end OMA.Grid652

/- Splitting a finite plane drawing into disjoint vertex stars and the
middle thirds of its arcs, with exactly the original incidence relation. -/
namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

private noncomputable def loCut : unitInterval := ⟨1/3, by constructor <;> norm_num⟩
private noncomputable def hiCut : unitInterval := ⟨2/3, by constructor <;> norm_num⟩

private lemma cuts : (0 : unitInterval) < loCut ∧ loCut < hiCut ∧ hiCut < 1 := by
  change (0:ℝ) < 1/3 ∧ (1:ℝ)/3 < 2/3 ∧ (2:ℝ)/3 < 1
  norm_num

private structure DrawArc (Q : Finset ℝ²) where
  src : Q
  dst : Q
  path : Path (src : ℝ²) (dst : ℝ²)
  inj : Function.Injective path
  vertex : ∀ (v : Q), (v : ℝ²) ∈ range path → v = src ∨ v = dst

private def DrawArc.tip {Q} (d : DrawArc Q) : Bool → Q
  | false => d.src
  | true => d.dst

private def outerTimes : Bool → Set unitInterval
  | false => Icc 0 loCut
  | true => Icc hiCut 1

private def DrawArc.outer {Q} (d : DrawArc Q) (b : Bool) : Set ℝ² :=
  d.path '' outerTimes b

private def DrawArc.middle {Q} (d : DrawArc Q) : Set ℝ² :=
  d.path '' Icc loCut hiCut

private lemma DrawArc.outer_props {Q} (d : DrawArc Q) (b : Bool) :
    (d.tip b : ℝ²) ∈ d.outer b ∧ IsCompact (d.outer b) ∧ IsPreconnected (d.outer b) := by
  cases b
  · exact ⟨⟨0, ⟨le_rfl, cuts.1.le⟩, d.path.source⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩
  · exact ⟨⟨1, ⟨cuts.2.2.le, le_rfl⟩, d.path.target⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩

private lemma DrawArc.outer_vertex {Q} (d : DrawArc Q) (b : Bool) (v : Q)
    (h : (v : ℝ²) ∈ d.outer b) : v = d.tip b := by
  obtain ⟨t, ht, hv⟩ := h
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · cases b
    · exact hx
    · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
      have hle : hiCut ≤ 0 := he ▸ ht.1
      exact ((cuts.1.trans cuts.2.1).not_ge hle).elim
  · cases b
    · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
      have hle : 1 ≤ loCut := he ▸ ht.2
      exact ((cuts.2.1.trans cuts.2.2).not_ge hle).elim
    · exact hy

private lemma DrawArc.middle_avoids {Q} (d : DrawArc Q) (v : Q) :
    (v : ℝ²) ∉ d.middle := by
  rintro ⟨t, ht, hv⟩
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
    exact cuts.1.not_ge (he ▸ ht.1)
  · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
    exact cuts.2.2.not_ge (he ▸ ht.2)

private lemma DrawArc.side_unique {Q} (d : DrawArc Q) {b c : Bool} {z : ℝ²}
    (hb : z ∈ d.outer b) (hc : z ∈ d.outer c) : b = c := by
  obtain ⟨t, ht, rfl⟩ := hb
  obtain ⟨u, hu, he⟩ := hc
  have := d.inj he
  subst u
  cases b <;> cases c
  · rfl
  · exact (cuts.2.1.not_ge (le_trans hu.1 ht.2)).elim
  · exact (cuts.2.1.not_ge (le_trans ht.1 hu.2)).elim
  · rfl

private lemma DrawArc.middle_meets {Q} (d : DrawArc Q) (b : Bool) :
    (d.middle ∩ d.outer b).Nonempty := by
  cases b
  · exact ⟨d.path loCut, ⟨loCut, ⟨le_rfl, cuts.2.1.le⟩, rfl⟩,
      ⟨loCut, ⟨cuts.1.le, le_rfl⟩, rfl⟩⟩
  · exact ⟨d.path hiCut, ⟨hiCut, ⟨cuts.2.1.le, le_rfl⟩, rfl⟩,
      ⟨hiCut, ⟨le_rfl, cuts.2.2.le⟩, rfl⟩⟩

/-- Each branch set consists of its vertex and the adjacent outer thirds. Each
connector is a middle third. The compact pieces can then be rasterized jointly. -/
theorem split_drawing (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (hcross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) :
    ∃ (B : S → Set ℝ²) (C : E → Set ℝ²),
      (∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v)) ∧
      (∀ e, IsCompact (C e) ∧ IsPreconnected (C e)) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ e f, e ≠ f → Disjoint (C e) (C f)) ∧
      (∀ e v, ¬ Disjoint (C e) (B v) ↔ v.val ∈ edge e.val) := by
  classical
  have arcs (e : E) : ∃ d : DrawArc Q, edge e.val = {d.src,d.dst} ∧
      curve e.val = range d.path := by
    obtain ⟨x,y,_,hed,γ,hi,hγ,hv⟩ := hd e e.2
    refine ⟨⟨x,y,γ,hi,fun v h => ?_⟩, hed, hγ⟩
    simpa only [hed, Finset.mem_insert, Finset.mem_singleton] using hv v (hγ ▸ h)
  choose d ends full using arcs
  have crossing {e f : E} (hef : e ≠ f) {z : ℝ²} (he : z ∈ range (d e).path)
      (hf : z ∈ range (d f).path) : ∃ v : Q, (v : ℝ²) = z := by
    have h := hcross e e.2 f f.2 (fun h => hef (Subtype.ext h))
      ⟨(full e).symm ▸ he, (full f).symm ▸ hf⟩
    exact ⟨h.choose,h.choose_spec.2⟩
  let tips (v : S) := {p : E × Bool // (d p.1).tip p.2 = v.val}
  let part (v : S) : Option (tips v) → Set ℝ²
    | none => {(v.val : ℝ²)}
    | some p => (d p.val.1).outer p.val.2
  let B (v : S) := ⋃ k, part v k
  have piece (v : S) (k : Option (tips v)) :
      (v.val : ℝ²) ∈ part v k ∧ IsCompact (part v k) ∧ IsPreconnected (part v k) := by
    cases k with
    | none => exact ⟨mem_singleton _, isCompact_singleton, isPreconnected_singleton⟩
    | some p => simpa only [part, ← p.property] using (d p.val.1).outer_props p.val.2
  have memB {v : S} {z : ℝ²} (h : z ∈ B v) :
      z = (v.val : ℝ²) ∨ ∃ e b, (d e).tip b = v.val ∧ z ∈ (d e).outer b := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    cases k with
    | none => exact Or.inl hk
    | some p => exact Or.inr ⟨_,_,p.property,hk⟩
  have vertexB {v : S} (x : Q) (h : (x : ℝ²) ∈ B v) : x = v.val := by
    rcases memB h with hx | ⟨e,b,ht,hx⟩
    · exact Subtype.ext hx
    · exact ((d e).outer_vertex b x hx).trans ht
  have wholeOuter {e : E} {b z} (h : z ∈ (d e).outer b) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  have wholeMiddle {e : E} {z} (h : z ∈ (d e).middle) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  refine ⟨B,fun e => (d e).middle, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨⟨_,mem_iUnion.mpr ⟨none,(piece v none).1⟩⟩,
      isCompact_iUnion (fun k => (piece v k).2.1),
      isPreconnected_iUnion ⟨_,mem_iInter.mpr (fun k => (piece v k).1)⟩
        (fun k => (piece v k).2.2)⟩
  · exact fun e => ⟨isCompact_Icc.image (d e).path.continuous,
      isPreconnected_Icc.image _ (d e).path.continuous.continuousOn⟩
  · intro v w hne
    apply disjoint_left.mpr
    intro z hv hw
    apply hne
    apply Subtype.ext
    rcases memB hv with rfl | ⟨e,b,ht,he⟩
    · exact vertexB _ hw
    rcases memB hw with rfl | ⟨f,c,hu,hf⟩
    · exact (vertexB _ hv).symm
    by_cases h : e = f
    · subst f
      rw [← ht, ← hu, (d e).side_unique he hf]
    · obtain ⟨x,rfl⟩ := crossing h (wholeOuter he) (wholeOuter hf)
      exact (vertexB x hv).symm.trans (vertexB x hw)
  · intro e f hne
    apply disjoint_left.mpr
    intro z he hf
    obtain ⟨x,rfl⟩ := crossing hne (wholeMiddle he) (wholeMiddle hf)
    exact (d e).middle_avoids x he
  · intro e v
    constructor
    · intro hn
      obtain ⟨z, he, hv⟩ := not_disjoint_iff.mp hn
      rcases memB hv with rfl | ⟨f,b,ht,hf⟩
      · exact ((d e).middle_avoids _ he).elim
      by_cases h : e = f
      · subst f
        rw [ends, ← ht]
        cases b <;> simp [DrawArc.tip]
      · obtain ⟨x,rfl⟩ := crossing h (wholeMiddle he) (wholeOuter hf)
        exact ((d e).middle_avoids x he).elim
    · intro hv
      have side : ∃ b, (d e).tip b = v.val := by
        rw [ends, Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv.elim (fun h => ⟨false,h.symm⟩) (fun h => ⟨true,h.symm⟩)
      obtain ⟨b,hb⟩ := side
      obtain ⟨z,hz,hleg⟩ := (d e).middle_meets b
      exact not_disjoint_iff.mpr ⟨z,hz,mem_iUnion.mpr ⟨some (⟨(e,b),hb⟩ : tips v),hleg⟩⟩

end OMA.Grid652

namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

theorem plane_drawing_bound (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inside : ∀ i ∈ E, edge i ⊆ S) (inj : Set.InjOn edge (E : Set ℕ))
    (cross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) : E.card ≤ 3 * S.card := by
  classical
  have ep (e : E) : ∃ s t : S, s ≠ t ∧ edge e.val = {s.val,t.val} := by
    obtain ⟨x,y,hne,hed,_⟩ := hd e e.2
    have hx := inside e e.2 (show x ∈ edge e.val by simp [hed])
    have hy := inside e e.2 (show y ∈ edge e.val by simp [hed])
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,fun h => hne (congrArg Subtype.val h),hed⟩
  choose s t hne hed using ep
  have simple : Function.Injective (fun e => ({s e,t e} : Finset S)) := by
    intro e f h
    apply Subtype.ext
    apply inj e.2 f.2
    rw [hed e, hed f]
    simpa using congrArg (Finset.image (Subtype.val : S → Q)) h
  obtain ⟨B,C,hB,hC,hBB,hCC,ht⟩ := split_drawing Q S E edge curve hd cross
  have touch (e : E) (v : S) : ¬ Disjoint (C e) (B v) ↔ s e = v ∨ t e = v := by
    rw [ht, hed e, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.imp (fun h => Subtype.ext h.symm) (fun h => Subtype.ext h.symm)
    · exact fun h => h.imp (fun h => congrArg Subtype.val h.symm) (fun h => congrArg Subtype.val h.symm)
  simpa using grid_patch_bound s t hne simple B C hB hC hBB hCC touch

end OMA.Grid652

end

/- # Mathialagan's bound for distances from a small set of centers

The planar simple-graph edge inequality and an explicit geometric drawing give the
bound for arbitrary, not necessarily nested, sets P and Q. The two-center bound,
crossing deletion, vertex sampling and constants are proved here.
Credit: @JaviSoto. -/

/- The random sampling part of the graph crossing lemma, by exact finite counting. -/

namespace OMA.Crossing

open Finset

private theorem samples_containing {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (A : Finset V) :
    (univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0)))).card =
      (r+1)^(Fintype.card V-A.card) := by
  classical
  let t (v : V) : Finset (Fin (r+1)) := if v ∈ A then {0} else univ
  have he : univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0))) = Fintype.piFinset t := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ A
      · have hv' := h hv
        simpa [t,hv] using hv'
      · simp [t,hv]
    · intro h v hv
      have hv' := h v
      simpa [t,hv] using hv'
  rw [he, Fintype.card_piFinset]
  have hc (v : V) : (t v).card = if v ∈ A then 1 else r+1 := by
    by_cases hv : v ∈ A <;> simp [t,hv]
  simp_rw [hc]
  rw [prod_ite]
  simp [show (univ.filter fun v => v ∉ A) = Aᶜ by ext; simp, card_compl]

private theorem sum_surviving {V α : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (E : Finset α) (verts : α → Finset V) (hj : ∀ e ∈ E, (verts e).card = j) :
    ∑ f : V → Fin (r+1), (E.filter (fun e => verts e ⊆ (univ.filter (fun v => f v = 0)))).card =
      E.card * (r+1)^(Fintype.card V-j) := by
  classical
  calc
    _ = ∑ e ∈ E, (univ.filter (fun f : V → Fin (r+1) => verts e ⊆ (univ.filter (fun v => f v = 0)))).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (univ : Finset (V → Fin (r+1)))) (t := E)
        (fun (f : V → Fin (r+1)) (e : α) => verts e ⊆ univ.filter (fun v => f v = 0))
    _ = _ := by
      simp only [samples_containing]
      rw [sum_congr rfl (fun e he => by rw [hj e he])]
      simp

/-- Suppose every induced subdrawing satisfies the linear planarization inequality:
the number of surviving edges is at most three times the vertices plus the surviving
crossings. For edges supported on pairs and crossings supported on four distinct vertices,
sampling a 1/r fraction of the vertices amplifies this to a cubic crossing bound. -/
theorem sample_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card)
    (r : ℕ) (hr : 1 ≤ r) :
    E.card * r^2 ≤ 3 * Fintype.card V * r^3 + C.card := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  let n := Fintype.card V
  have h := sum_le_sum (s := (univ : Finset (V → Fin (r+1)))) (fun f _ => planar ((univ.filter (fun v => f v = 0))))
  have hvertex (f : V → Fin (r+1)) :
      (univ.filter (fun e : V => ({e} : Finset V) ⊆ (univ.filter (fun v => f v = 0)))).card = ((univ.filter (fun v => f v = 0))).card := by simp
  have hvertices := sum_surviving (V := V) r 1 univ (fun e : V => {e}) (by simp)
  simp_rw [hvertex,card_univ] at hvertices
  rw [sum_add_distrib, ← mul_sum, hvertices, sum_surviving _ _ _ _ he, sum_surviving _ _ _ _ hc] at h
  have hpow (j : ℕ) (hj : j ≤ 4) :
      (r+1)^(Fintype.card V-j) = (r+1)^(4-j) * (r+1)^(Fintype.card V-4) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow 2 (by decide), hpow 1 (by decide)] at h
  norm_num at h
  apply Nat.le_of_mul_le_mul_right _ (pow_pos (by omega : 0 < r+1) (n-4))
  simpa only [n, Nat.succ_eq_add_one, add_mul, mul_assoc] using h

/-- A drawing with at least 12 edges per vertex and the planarization inequality
has at least e³/(288 v²) crossings. -/
theorem cubic_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V) (hdense : 12 * Fintype.card V ≤ E.card)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card) :
    E.card^3 ≤ 288 * (Fintype.card V)^2 * C.card := by
  let n := Fintype.card V
  let r := E.card / (6*n)
  have hn : 0 < n := by dsimp [n]; omega
  have hr : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by dsimp [n] at *; omega)
  have hsplit := sample_crossing_bound E C edge cross he hc hV planar r hr
  have hu : r * (6*n) ≤ E.card := Nat.div_mul_le_self _ _
  have hq : E.card ≤ 12*n*r := by
    have hlt : E.card < (r+1)*(6*n) := (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self r)
    have hrr : r+1 ≤ 2*r := by omega
    exact hlt.le.trans ((Nat.mul_le_mul_right _ hrr).trans_eq (by ring))
  have hcross : E.card*r^2 ≤ 2*C.card := by
    change E.card * r^2 ≤ 3*n*r^3 + C.card at hsplit
    nlinarith only [hsplit, Nat.mul_le_mul_right (r^2) hu]
  calc
    E.card^3 = E.card^2 * E.card := by ring
    _ ≤ (12*n*r)^2 * E.card := by gcongr
    _ = (144*n^2) * (E.card*r^2) := by ring
    _ ≤ (144*n^2) * (2*C.card) := Nat.mul_le_mul_left _ hcross
    _ = _ := by change _ = 288*n^2*C.card; ring

end OMA.Crossing

/- Two centers give an injective encoding by two radii and a side of their common line. -/

namespace OMA.CircleArcs

open scoped EuclideanGeometry

/-- Two circles with distinct centers meet at most once in either open halfplane of the
line through their centers. Thus arcs cut at every center line cannot have parallel edges
or a second crossing with another incident arc. -/
theorem eq_of_dist_eq_in_same_halfplane {a b x y : ℝ²} (hab : a ≠ b)
    (ha : dist x a = dist y a) (hb : dist x b = dist y b)
    (hs : 0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0)) * ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0))) : x = y := by
  have hdist (u v : ℝ²) : dist u v ^ 2 = (u 0-v 0)^2 + (u 1-v 1)^2 := by
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hE := congrArg (fun z : ℝ => z^2) ha
  have hF := congrArg (fun z : ℝ => z^2) hb
  simp only [hdist] at hE hF
  let u := b 0-a 0
  let v := b 1-a 1
  let dot (z : ℝ²) := u*(z 0-a 0) + v*(z 1-a 1)
  have hd : dot x = dot y := by
    dsimp [dot,u,v]; linear_combination (hE - hF)/2
  have hid (z : ℝ²) : dot z ^ 2 + ((b 0-a 0)*(z 1-a 1) - (b 1-a 1)*(z 0-a 0)) ^ 2 =
      (u^2+v^2)*((z 0-a 0)^2+(z 1-a 1)^2) := by dsimp [dot,u,v]; ring
  have hh := hid x
  rw [hd,hE,← hid y] at hh
  have hside : ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0)) = ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (add_left_cancel hh) with he | he
    · exact he
    · rw [he] at hs
      have hz : ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) = 0 := by nlinarith only [hs, sq_nonneg (((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)))]
      simp [hz, he]
  have huv : u^2+v^2 ≠ 0 := by
    intro hz
    obtain ⟨hu2,hv2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg u) (sq_nonneg v)).mp hz
    have hu : u = 0 := by simpa using hu2
    have hv : v = 0 := by simpa using hv2
    apply hab
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp hu).symm
    · exact (sub_eq_zero.mp hv).symm
  change u*(x 1-a 1) - v*(x 0-a 0) = u*(y 1-a 1) - v*(y 0-a 0) at hside
  dsimp only [dot] at hd
  ext i
  fin_cases i
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 0 = (u^2+v^2)*y 0
    linear_combination u*hd-v*hside
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 1 = (u^2+v^2)*y 1
    linear_combination v*hd+u*hside

open Finset
open scoped Classical

theorem two_centers (Q : Finset ℝ²) {a b : ℝ²} (hab : a ≠ b) :
    Q.card ≤ 2 * (Q.image fun x => dist a x).card * (Q.image fun x => dist b x).card := by
  let F (x : ℝ²) := (decide (0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))), dist a x, dist b x)
  let T := (univ : Finset Bool) ×ˢ ((Q.image (dist a)) ×ˢ (Q.image (dist b)))
  have hmap : Set.MapsTo F (Q : Set ℝ²) (T : Set (Bool × ℝ × ℝ)) := by
    intro x hx
    exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩⟩
  have hinj : Set.InjOn F (Q : Set ℝ²) := by
    intro x _ y _ he
    have hs : decide (0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))) = decide (0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0))) := congrArg Prod.fst he
    have hA : dist a x = dist a y := congrArg (fun t : Bool × ℝ × ℝ => t.2.1) he
    have hB : dist b x = dist b y := congrArg (fun t : Bool × ℝ × ℝ => t.2.2) he
    apply eq_of_dist_eq_in_same_halfplane hab (by simpa only [dist_comm x, dist_comm y] using hA)
      (by simpa only [dist_comm x, dist_comm y] using hB)
    by_cases hx : 0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))
    · have hy : 0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by simpa [hx] using hs.symm
      exact mul_nonneg hx hy
    · have hy : ¬ 0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by simpa [hx] using hs.symm
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx) (le_of_not_ge hy)
  simpa [T,Nat.mul_assoc] using card_le_card_of_injOn F hmap hinj

end OMA.CircleArcs

/- Quantitative estimates for a bipartite distinct-distance drawing. -/

namespace OMA.Math652

/-- The edge count, pair-of-circles intersection count, and cubic crossing bound
give the square-root distinct distance estimate throughout the range `k³ ≤ n`. -/
theorem distance_bound (k n D e X : ℕ) (hk : 2 ≤ k) (hn : k^3 ≤ n)
    (htwo : n ≤ 2*D^2) (hedge : k*n ≤ e + 4*k^2*(D+1))
    (hX : X ≤ 2*(k*D)^2) (hcross : 12*n ≤ e → e^3 ≤ 288*n^2*X) :
    (1/68 : ℝ)*Real.sqrt ((k:ℝ)*n) ≤ D := by
  have hk0 : 0 < k := by omega
  have hn0 : 0 < n := (pow_pos hk0 3).trans_le hn
  have hD : 1 ≤ D := by
    by_contra! h
    have : D = 0 := by omega
    subst D
    simp_all
  have bound : k*n ≤ 4624*D^2 := by
    by_cases hk' : k ≤ 24
    · calc k*n ≤ 24*(2*D^2) := Nat.mul_le_mul hk' htwo
           _ ≤ 4624*D^2 := by omega
    by_cases he : k*n ≤ 2*e
    · have dense : 12*n ≤ e := by
        have := Nat.mul_le_mul_right n (show 24 ≤ k by omega)
        omega
      have cube : (k*n)^3 ≤ (2*e)^3 := by gcongr
      have upper : e^3 ≤ 288*n^2*(2*(k*D)^2) :=
        (hcross dense).trans (Nat.mul_le_mul_left _ hX)
      have h : k*n ≤ 4608*D^2 := by
        apply Nat.le_of_mul_le_mul_left (c := k^2*n^2) _ (by positivity)
        nlinarith only [cube,upper]
      omega
    · have loss : n ≤ 16*k*D := by
        apply Nat.le_of_mul_le_mul_left (c := k) _ hk0
        have := Nat.mul_le_mul_left (4*k^2) (show D+1 ≤ 2*D by omega)
        nlinarith only [hedge,he,this]
      have h : k*n ≤ 256*D^2 := by
        apply Nat.le_of_mul_le_mul_left (c := k^2) _ (by positivity)
        have hsq : n^2 ≤ (16*k*D)^2 := by gcongr
        nlinarith only [hsq,Nat.mul_le_mul_right n hn]
      omega
  have hreal : (k:ℝ)*n ≤ (68*(D:ℝ))^2 := by
    have cast : (k:ℝ)*n ≤ 4624*(D:ℝ)^2 := by exact_mod_cast bound
    nlinarith only [cast]
  have hroot : Real.sqrt ((k:ℝ)*n) ≤ 68*(D:ℝ) :=
    (Real.sqrt_le_iff.mpr ⟨by positivity,hreal⟩)
  linarith

end OMA.Math652

/- Plane drawings, the linear planar edge inequality and the circle-arc input. -/

namespace OMA.R_Erdos652_erdos_652_variants_mathialagan_R1

open Finset
open scoped EuclideanGeometry Classical

/-- Euler's linear edge bound for a simple drawing with disjoint edge interiors. -/
def H1 : Prop :=
  ∀ (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) →
  (∀ i ∈ E, edge i ⊆ S) → Set.InjOn edge (E : Set ℕ) →
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) →
  E.card ≤ 3 * S.card

/-- Use arcs between consecutive data points on the concentric circles about each center.
Cut at all center lines so crossings involve four distinct endpoints. C records the
ordered exceptional pairs; unlisted pairs meet only at common endpoints. -/
def H2 : Prop :=
  ∀ (P Q : Finset ℝ²) (D : ℕ), 2 ≤ P.card → P.card ^ 3 ≤ Q.card →
  (∀ p ∈ P, (Q.image (dist p)).card ≤ D) →
  ∃ (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ)),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) ∧
  Set.InjOn edge (E : Set ℕ) ∧
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) ∧
  (∀ ij ∈ C, (edge ij.1 ∪ edge ij.2).card = 4) ∧
  P.card * Q.card ≤ E.card + 4 * P.card^2 * (D+1) ∧ C.card ≤ 2 * (P.card*D)^2

/-- Removing the first edge of each crossing suffices for every induced subdrawing. -/
theorem induced_edges {Q : Finset ℝ²} (planar : H1) (E : Finset ℕ) (edge : ℕ → Finset Q)
    (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ))
    (drawn : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inj : Set.InjOn edge (E : Set ℕ))
    (meet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q))
    (S : Finset Q) : (E.filter (fun i => edge i ⊆ S)).card ≤ 3 * S.card +
      (C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)).card := by
  let F := E.filter (fun i => edge i ⊆ S)
  let K := C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)
  let G := F \ K.image Prod.fst
  have hsub {i} (hi : i ∈ G) : i ∈ F := (mem_sdiff.mp hi).1
  have hE {i} (hi : i ∈ G) : i ∈ E := (mem_filter.mp (hsub hi)).1
  have hgood : G.card ≤ 3 * S.card := by
    apply planar Q S G edge curve (fun i hi => drawn i (hE hi))
      (fun _ hi => (mem_filter.mp (hsub hi)).2) (fun _ hi _ hj eq => inj (hE hi) (hE hj) eq)
    intro i hi j hj hij
    apply meet i (hE hi) j (hE hj) hij
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨(i,j), mem_filter.mpr
      ⟨hc, union_subset (mem_filter.mp (hsub hi)).2 (mem_filter.mp (hsub hj)).2⟩, rfl⟩)
  calc F.card ≤ G.card + (K.image Prod.fst).card := card_le_card_sdiff_add_card
       _ ≤ 3 * S.card + K.card := Nat.add_le_add hgood card_image_le

theorem main : H1 → H2 → type_of% @Erdos652.erdos_652.variants.mathialagan := by
  intro hplanar hdraw
  refine ⟨1/68, by norm_num, ?_⟩
  intro P Q hk hn
  let d (p : ℝ²) := (Q.image (dist p)).card
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image d (card_pos.mp (by omega))
  obtain ⟨u, v, hu, hv, huv⟩ := one_lt_card_iff.mp hk
  have htwo : Q.card ≤ 2 * (d p)^2 := calc
    Q.card ≤ 2 * d u * d v := OMA.CircleArcs.two_centers Q huv
    _ ≤ 2 * d p * d p := by gcongr <;> apply hmax <;> assumption
    _ = _ := by ring
  obtain ⟨E, edge, curve, C, drawn, hinj, meet, four, hedge, hX⟩ := hdraw P Q (d p) hk hn hmax
  refine ⟨p, hp, OMA.Math652.distance_bound P.card Q.card (d p) E.card C.card
    hk hn htwo hedge hX ?_⟩
  intro hdense
  have hV : 4 ≤ Q.card := by
    have h := Nat.pow_le_pow_left hk 3
    omega
  have two (i) (hi : i ∈ E) : (edge i).card = 2 := by
    obtain ⟨x,y,hne,he,_⟩ := drawn i hi
    simp [he,hne]
  have h := OMA.Crossing.cubic_crossing_bound E C edge (fun ij => edge ij.1 ∪ edge ij.2)
    two four (by simpa only [Fintype.card_coe] using hV)
    (by simpa only [Fintype.card_coe] using hdense) (induced_edges hplanar E edge curve C drawn hinj meet)
  simpa only [Fintype.card_coe] using h

end OMA.R_Erdos652_erdos_652_variants_mathialagan_R1

/- Angular coordinates and consecutive edges of a finite, cut circle. -/

namespace OMA.Math652ArcOrder

open Finset
open scoped EuclideanGeometry Classical

noncomputable abbrev plane := Complex.orthonormalBasisOneI.repr

noncomputable def angle (p q : ℝ²) : ℝ := (plane.symm (q-p)).arg

noncomputable def point (p : ℝ²) (r t : ℝ) : ℝ² :=
  p + plane ((r : ℂ) * Complex.exp (t*Complex.I))

theorem continuous_point (p : ℝ²) (r : ℝ) : Continuous (point p r) := by
  unfold point
  fun_prop

theorem angle_mem (p q : ℝ²) : angle p q ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

theorem angle_point (p : ℝ²) {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) : angle p (point p r t) = t := by
  simp [angle,point,Complex.exp_mul_I,Complex.arg_mul_cos_add_sin_mul_I hr ht]

theorem point_angle (p q : ℝ²) : point p (dist p q) (angle p q) = q := by
  have hn : dist p q = ‖plane.symm (q-p)‖ := by rw [LinearIsometryEquiv.norm_map, dist_comm, dist_eq_norm]
  rw [point,angle,hn,Complex.norm_mul_exp_arg_mul_I,LinearIsometryEquiv.apply_symm_apply]
  abel

theorem dist_point (p : ℝ²) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : dist p (point p r t) = r := by
  rw [dist_comm, dist_eq_norm]
  simp [point, Complex.norm_exp, hr]

noncomputable def arcPath (p : ℝ²) (r s t : ℝ) : Path (point p r s) (point p r t) :=
  (Path.segment s t).map (continuous_point p r)

theorem range_arcPath (p : ℝ²) (r : ℝ) {s t : ℝ} (hst : s ≤ t) :
    Set.range (arcPath p r s t) = point p r '' Set.Icc s t := by
  change Set.range (point p r ∘ (Path.segment s t)) = _
  rw [Set.range_comp,Path.range_segment,segment_eq_Icc hst]

theorem injective_arcPath (p : ℝ²) {r s t : ℝ} (hr : 0 < r) (hst : s < t)
    (hs : -Real.pi < s) (ht : t ≤ Real.pi) : Function.Injective (arcPath p r s t) := by
  have hseg (u : unitInterval) : Path.segment s t u ∈ Set.Icc s t := by
    rw [← segment_eq_Icc hst.le, ← Path.range_segment]
    exact Set.mem_range_self _
  intro u v h
  have eq := congrArg (angle p) h
  change angle p (point p r (Path.segment s t u)) = angle p (point p r (Path.segment s t v)) at eq
  have hangle (u : unitInterval) : Path.segment s t u ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hs.trans_le (hseg u).1,(hseg u).2.trans ht⟩
  rw [angle_point _ hr (hangle u),angle_point _ hr (hangle v)] at eq
  exact Path.segment_injective_of_ne hst.ne eq

def interval {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (i : Fin m) : Set ℝ :=
  Set.Icc (θ i.castSucc) (θ i.succ)

noncomputable def hits {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (z : ℝ) : Finset (Fin m) :=
  univ.filter fun i => z ∈ interval θ i

noncomputable def surviving {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) : Finset (Fin m) :=
  univ \ C.biUnion (hits θ)

/-- At most two consecutive closed intervals contain a fixed cut; their common
vertex is the only way both can contain it. -/
theorem card_hits {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (z : ℝ) : (hits θ z).card ≤ 2 := by
  let side (i : Fin m) := decide (θ i.castSucc = z)
  have diff {i j : Fin m} (h : i < j) (hi : z ∈ interval θ i) (hj : z ∈ interval θ j) :
      side i ≠ side j := by
    have ord : θ i.succ ≤ θ j.castSucc := θ.monotone (by simpa using h)
    have heq : θ j.castSucc = z := le_antisymm hj.1 (hi.2.trans ord)
    have hne : θ i.castSucc ≠ z := (θ.strictMono Fin.castSucc_lt_succ).trans_le (ord.trans hj.1) |>.ne
    simp [side,heq,hne]
  have hc : (hits θ z).card ≤ (univ : Finset Bool).card := by
    apply card_le_card_of_injOn side (fun _ _ => mem_univ _)
    intro i hi j hj eq
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    rcases lt_trichotomy i j with h|h|h
    · exact (diff h hi' hj' eq).elim
    · exact h
    · exact (diff h hj' hi' eq.symm).elim
  simpa using hc

theorem card_surviving {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) :
    m+1 ≤ (surviving θ C).card + 2*C.card+1 := by
  have hu : (C.biUnion (hits θ)).card ≤ C.card*2 :=
    card_biUnion_le.trans ((sum_le_sum fun t _ => card_hits θ t).trans_eq (by simp))
  have h : (univ : Finset (Fin m)).card ≤ (surviving θ C).card + (C.biUnion (hits θ)).card :=
    card_le_card_sdiff_add_card
  simp only [card_univ,Fintype.card_fin] at h
  omega

theorem avoids_cuts {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) {i : Fin m}
    (hi : i ∈ surviving θ C) {z : ℝ} (hz : z ∈ C) : z ∉ interval θ i := by
  intro h
  exact (mem_sdiff.mp hi).2 (mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨mem_univ _,h⟩⟩)

theorem consecutive {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (i : Fin m) (j : Fin (m+1))
    (h : θ j ∈ interval θ i) : j = i.castSucc ∨ j = i.succ := by
  have h1 := θ.le_iff_le.mp h.1
  have h2 := θ.le_iff_le.mp h.2
  change i.val ≤ j.val at h1
  change j.val ≤ i.val + 1 at h2
  by_cases eq : j.val = i.val
  · exact Or.inl (Fin.ext eq)
  · exact Or.inr (Fin.ext (by change j.val = i.val+1; omega))

/-- The points at radius `r` in the direction of a second center and its opposite. -/
noncomputable def cutPoints (p b : ℝ²) (r : ℝ) : Finset ℝ² :=
  {p + (r / dist p b) • (b-p), p + (-(r / dist p b)) • (b-p)}

noncomputable def lineSide (p b z : ℝ²) : ℝ :=
  (b 0 - p 0)*(z 1 - p 1) - (b 1 - p 1)*(z 0 - p 0)

private theorem point_on_line {p b z : ℝ²} (hb : p ≠ b) (hz : lineSide p b z = 0) :
    ∃ t : ℝ, z = p + t • (b-p) := by
  unfold lineSide at hz
  by_cases h : b 0 - p 0 = 0
  · have h' : b 1 - p 1 ≠ 0 := by
      intro hy
      exact hb (by ext i; fin_cases i <;> simp <;> linarith)
    refine ⟨(z 1 - p 1)/(b 1 - p 1),?_⟩
    ext i
    fin_cases i <;> simp [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,h]
    · rcases mul_eq_zero.mp (show (b 1-p 1)*(z 0-p 0) = 0 by rw [h] at hz; linarith) with h₁|h₂
      · exact (h' h₁).elim
      · linarith
    · field_simp
      ring
  · refine ⟨(z 0-p 0)/(b 0-p 0),?_⟩
    ext i
    fin_cases i <;> simp [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply] <;> field_simp
    · ring
    · linarith

theorem mem_cutPoints {p b z : ℝ²} {r : ℝ} (hb : p ≠ b) (hr : dist p z = r)
    (hz : lineSide p b z = 0) : z ∈ cutPoints p b r := by
  obtain ⟨t,rfl⟩ := point_on_line hb hz
  have hp : 0 < dist p b := dist_pos.mpr hb
  have hnorm : |t| * dist p b = r := by
    rw [dist_comm p _,dist_eq_norm] at hr
    simpa [norm_smul,Real.norm_eq_abs,← dist_eq_norm,dist_comm b p] using hr
  have h := (eq_div_iff hp.ne').mpr hnorm
  rcases le_or_gt 0 t with ht|ht
  · rw [abs_of_nonneg ht] at h
    simp [cutPoints,h]
  · rw [abs_of_neg ht] at h
    have he : t = -(r / dist p b) := by linarith
    simp [cutPoints,he]

noncomputable def cuts (P : Finset ℝ²) (p : ℝ²) (r : ℝ) : Finset ℝ :=
  (P.erase p).biUnion fun b => (cutPoints p b r).image (angle p)

theorem card_cuts (P : Finset ℝ²) {p : ℝ²} (hp : p ∈ P) (r : ℝ) :
    (cuts P p r).card ≤ (P.card-1)*2 := by
  calc
    _ ≤ ∑ b ∈ P.erase p, ((cutPoints p b r).image (angle p)).card := card_biUnion_le
    _ ≤ ∑ _b ∈ P.erase p, 2 := sum_le_sum fun b _ => card_image_le.trans card_le_two
    _ = _ := by simp [card_erase_of_mem hp]

/-- On every surviving interval, no point of the circle lies on any of the cut lines. -/
theorem not_on_cut_line (P : Finset ℝ²) {p b : ℝ²} (hb : b ∈ P) (hne : p ≠ b)
    {r : ℝ} (hr : 0 < r) {m : ℕ} (θ : Fin (m+1) ↪o ℝ)
    (hθ : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi)
    {i : Fin m} (hi : i ∈ surviving θ (cuts P p r))
    {t : ℝ} (ht : t ∈ interval θ i) : lineSide p b (point p r t) ≠ 0 := by
  intro hz
  have hcut := mem_cutPoints hne (dist_point p hr.le t) hz
  have harg := angle_point p hr (show t ∈ Set.Ioc (-Real.pi) Real.pi from
    ⟨(hθ _).1.trans_le ht.1,ht.2.trans (hθ _).2⟩)
  exact avoids_cuts θ _ hi (mem_biUnion.mpr
    ⟨b,mem_erase.mpr ⟨hne.symm,hb⟩,mem_image.mpr ⟨_,hcut,harg⟩⟩) ht

/-- Any two points on a retained interval lie in the same open halfplane of every
cut line. The determinant defining the halfplane is continuous and never vanishes. -/
theorem same_side (P : Finset ℝ²) {p b : ℝ²} (hb : b ∈ P) (hne : p ≠ b)
    {r : ℝ} (hr : 0 < r) {m : ℕ} (θ : Fin (m+1) ↪o ℝ)
    (hθ : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi)
    {i : Fin m} (hi : i ∈ surviving θ (cuts P p r)) {t u : ℝ}
    (ht : t ∈ interval θ i) (hu : u ∈ interval θ i) :
    0 < lineSide p b (point p r t) * lineSide p b (point p r u) := by
  let f (s : ℝ) := lineSide p b (point p r s)
  have hcont : Continuous f := by
    unfold f lineSide
    have hc := continuous_point p r
    fun_prop
  have hn (s : ℝ) (hs : s ∈ interval θ i) : f s ≠ 0 := not_on_cut_line P hb hne hr θ hθ hi hs
  have same {a b : ℝ} (ha : a ∈ interval θ i) (hb : b ∈ interval θ i) (h : f a < 0) : f b < 0 := by
    by_contra! h'
    obtain ⟨s,hs,he⟩ := isPreconnected_Icc.intermediate_value ha hb hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f a) (f b) from ⟨h.le,h'⟩)
    exact hn s hs he
  change 0 < f t * f u
  rcases lt_or_gt_of_ne (hn t ht) with ht'|ht'
  · exact mul_pos_of_neg_of_neg ht' (same ht hu ht')
  · rcases lt_or_gt_of_ne (hn u hu) with hu'|hu'
    · exact (lt_asymm ht' (same hu ht hu')).elim
    · exact mul_pos ht' hu'

noncomputable def layer (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) : Finset ℝ² :=
  Q.filter fun q => dist p q = r

/-- Polar-angle enumeration of one radius class of a finite set. -/
structure LayerOrder (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) (n : ℕ) where
  θ : Fin n ↪o ℝ
  range_angle : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi
  members : ∀ q, q ∈ layer Q p r ↔ ∃ j, point p r (θ j) = q

noncomputable def orderLayer (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) {n : ℕ}
    (hN : (layer Q p r).card = n) : LayerOrder Q p r n := by
  let A := layer Q p r
  let T := A.image (angle p)
  have hr {q : ℝ²} (hq : q ∈ A) : dist p q = r := (mem_filter.mp hq).2
  have hpt {q : ℝ²} (hq : q ∈ A) : point p r (angle p q) = q := hr hq ▸ point_angle p q
  have hinj : Set.InjOn (angle p) (A : Set ℝ²) := by
    intro x hx y hy eq
    rw [← hpt hx,eq,hpt hy]
  have hcard : T.card = n := (card_image_of_injOn hinj).trans hN
  let θ := T.orderEmbOfFin hcard
  have hθ (j : Fin n) : θ j ∈ T := T.orderEmbOfFin_mem hcard j
  refine ⟨θ,?_,?_⟩
  · intro j
    obtain ⟨q,_,he⟩ := mem_image.mp (hθ j)
    rw [← he]
    exact angle_mem _ _
  · intro q
    constructor
    · intro hq
      have hmem : angle p q ∈ (T : Set ℝ) := mem_image_of_mem _ hq
      rw [← T.range_orderEmbOfFin hcard] at hmem
      obtain ⟨j,hj⟩ := hmem
      exact ⟨j,(congrArg (point p r) hj).trans (hpt hq)⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨q,hq,he⟩ := mem_image.mp (hθ j)
      rw [← he,hpt hq]
      exact hq

theorem LayerOrder.avoids {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} (hr : 0 < r) {m : ℕ}
    (L : LayerOrder Q p r (m+1)) (i : Fin m) {q : ℝ²} (hq : q ∈ Q)
    (h : q ∈ Set.range (arcPath p r (L.θ i.castSucc) (L.θ i.succ))) :
    q = point p r (L.θ i.castSucc) ∨ q = point p r (L.θ i.succ) := by
  rw [range_arcPath p r (L.θ.strictMono Fin.castSucc_lt_succ).le] at h
  obtain ⟨t,ht,rfl⟩ := h
  have hq' : point p r t ∈ layer Q p r := mem_filter.mpr ⟨hq,dist_point p hr.le t⟩
  obtain ⟨j,hj⟩ := (L.members _).mp hq'
  have h' := congrArg (angle p) hj
  have ht' : t ∈ Set.Ioc (-Real.pi) Real.pi := ⟨(L.range_angle _).1.trans_le ht.1,ht.2.trans (L.range_angle _).2⟩
  rw [angle_point _ hr (L.range_angle j),angle_point _ hr ht'] at h'
  rcases consecutive L.θ i j (h' ▸ ht) with he|he
  · exact Or.inl (he ▸ hj.symm)
  · exact Or.inr (he ▸ hj.symm)

/-- All local data contributed by a single circle, indexed by its surviving edges. -/
structure CircleChain (P Q : Finset ℝ²) (p : ℝ²) (r : ℝ) where
  n : ℕ
  edge : Fin n → Finset Q
  curve : Fin n → Set ℝ²
  drawn : ∀ i, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i
  simple : Function.Injective edge
  onCircle : ∀ i z, z ∈ curve i → dist p z = r
  uniqueOutside : ∀ i j z, z ∉ Q → z ∈ curve i → z ∈ curve j → i = j
  halfplanes : ∀ i b, b ∈ P → p ≠ b → ∀ x y, x ∈ curve i → y ∈ curve i →
    0 < lineSide p b x * lineSide p b y
  count : (layer Q p r).card ≤ n + 4*(P.card-1)+1

private noncomputable def emptyChain (P Q : Finset ℝ²) (p : ℝ²) (r : ℝ)
    (h : (layer Q p r).card ≤ 1) : CircleChain P Q p r where
  n := 0
  edge := Fin.elim0
  curve := Fin.elim0
  drawn := fun i => i.elim0
  simple := fun i => Fin.elim0 i
  onCircle := fun i => i.elim0
  uniqueOutside := fun i => i.elim0
  halfplanes := fun i => i.elim0
  count := by omega

private noncomputable def vertex {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {n : ℕ}
    (L : LayerOrder Q p r n) (j : Fin n) : Q :=
  ⟨point p r (L.θ j),(mem_filter.mp ((L.members _).mpr ⟨j,rfl⟩)).1⟩

private theorem vertex_injective {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} (hr : 0 < r) {n : ℕ}
    (L : LayerOrder Q p r n) : Function.Injective (vertex L) := by
  intro i j eq
  have h := congrArg (fun q : Q => angle p q) eq
  change angle p (point p r (L.θ i)) = angle p (point p r (L.θ j)) at h
  rwa [angle_point p hr (L.range_angle _),angle_point p hr (L.range_angle _),L.θ.injective.eq_iff] at h

private theorem interval_inside {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {m : ℕ}
    (L : LayerOrder Q p r (m+1)) {i : Fin m} {s : ℝ} (hs : s ∈ interval L.θ i) :
    s ∈ Set.Ioc (-Real.pi) Real.pi := ⟨(L.range_angle _).1.trans_le hs.1,hs.2.trans (L.range_angle _).2⟩

private theorem unique_interval {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {m : ℕ}
    (L : LayerOrder Q p r (m+1)) {i j : Fin m} {s : ℝ} (hs : point p r s ∉ Q)
    (hi : s ∈ interval L.θ i) (hj : s ∈ interval L.θ j) : i = j := by
  have forbidden {i j : Fin m} (hlt : i < j) (hi : s ∈ interval L.θ i)
      (hj : s ∈ interval L.θ j) : False := by
    have ord : L.θ i.succ ≤ L.θ j.castSucc := L.θ.monotone (by simpa using hlt)
    exact hs (le_antisymm hj.1 (hi.2.trans ord) ▸ (vertex L j.castSucc).property)
  rcases lt_trichotomy i j with h|h|h
  · exact (forbidden h hi hj).elim
  · exact h
  · exact (forbidden h hj hi).elim

/-- Construct the data on every radius, including empty and radius-zero layers. -/
noncomputable def circleChain (P Q : Finset ℝ²) (p : ℝ²) (hp : p ∈ P) (r : ℝ) :
    CircleChain P Q p r := by
  by_cases hr : 0 < r
  · cases hm : (layer Q p r).card with
    | zero => exact emptyChain P Q p r (by omega)
    | succ m =>
      let L := orderLayer Q p r hm
      let E := surviving L.θ (cuts P p r)
      let idx (i : Fin E.card) : Fin m := E.equivFin.symm i
      have hi (i : Fin E.card) : idx i ∈ E := (E.equivFin.symm i).property
      have hidx : Function.Injective idx := Subtype.val_injective.comp E.equivFin.symm.injective
      let x (i : Fin E.card) := vertex L (idx i).castSucc
      let y (i : Fin E.card) := vertex L (idx i).succ
      let γ (i : Fin E.card) := arcPath p r (L.θ (idx i).castSucc) (L.θ (idx i).succ)
      have hγ (i : Fin E.card) : Set.range (γ i) = point p r '' interval L.θ (idx i) :=
        range_arcPath p r (L.θ.strictMono Fin.castSucc_lt_succ).le
      refine {
        n := E.card, edge := fun i => {x i,y i}, curve := fun i => Set.range (γ i)
        drawn := ?_, simple := ?_, onCircle := ?_, uniqueOutside := ?_, halfplanes := ?_, count := ?_ }
      · intro i
        refine ⟨x i,y i,(vertex_injective hr L).ne Fin.castSucc_lt_succ.ne,rfl,γ i,?_,rfl,?_⟩
        · exact injective_arcPath p hr (L.θ.strictMono Fin.castSucc_lt_succ) (L.range_angle _).1 (L.range_angle _).2
        · intro v hv
          rcases L.avoids hr (idx i) v.property hv with h | h
          · rw [show v = x i from Subtype.ext h]
            simp
          · rw [show v = y i from Subtype.ext h]
            simp
      · intro i j eq
        have he := congrArg (fun s : Finset Q => (s : Set Q)) eq
        change (({x i,y i} : Finset Q) : Set Q) = (({x j,y j} : Finset Q) : Set Q) at he
        simp only [coe_pair,Set.pair_eq_pair_iff] at he
        rcases he with ⟨h,_⟩|⟨h,h'⟩
        · exact hidx (Fin.ext (congrArg (fun v : Fin (m+1) => v.val) (vertex_injective hr L h)))
        · have h₁ := congrArg Fin.val (vertex_injective hr L h)
          have h₂ := congrArg Fin.val (vertex_injective hr L h')
          change (idx i).val = (idx j).val+1 at h₁
          change (idx i).val+1 = (idx j).val at h₂
          omega
      · intro i z hz
        obtain ⟨t,_,rfl⟩ := hγ i ▸ hz
        exact dist_point p hr.le t
      · intro i j z hz hi hj
        obtain ⟨t,ht,rfl⟩ := hγ i ▸ hi
        obtain ⟨u,hu,htu⟩ := hγ j ▸ hj
        have he := congrArg (angle p) htu
        rw [angle_point p hr (interval_inside L hu),angle_point p hr (interval_inside L ht)] at he
        exact hidx (unique_interval L hz ht (he ▸ hu))
      · intro i b hb hne z w hz hw
        obtain ⟨t,ht,rfl⟩ := hγ i ▸ hz
        obtain ⟨u,hu,rfl⟩ := hγ i ▸ hw
        exact same_side P hb hne hr L.θ L.range_angle (hi i) ht hu
      · have h := card_surviving L.θ (cuts P p r)
        have h' := card_cuts P hp r
        change (layer Q p r).card ≤ (surviving L.θ (cuts P p r)).card + 4*(P.card-1)+1
        omega
  · apply emptyChain P Q p r
    apply card_le_one.mpr
    intro x hx y hy
    have he {z} (hz : z ∈ layer Q p r) : p = z :=
      dist_eq_zero.mp (le_antisymm ((mem_filter.mp hz).2.trans_le (le_of_not_gt hr)) dist_nonneg)
    exact (he hx).symm.trans (he hy)

theorem eq_of_dist_eq_in_same_halfplane {a b x y : ℝ²} (hab : a ≠ b)
    (ha : dist x a = dist y a) (hb : dist x b = dist y b)
    (hs : 0 < lineSide a b x * lineSide a b y) : x = y := by
  have hdist (u v : ℝ²) : dist u v ^ 2 = (u 0-v 0)^2 + (u 1-v 1)^2 := by
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hE := congrArg (fun z : ℝ => z^2) ha
  have hF := congrArg (fun z : ℝ => z^2) hb
  simp only [hdist] at hE hF
  let u := b 0-a 0
  let v := b 1-a 1
  let dot (z : ℝ²) := u*(z 0-a 0) + v*(z 1-a 1)
  have hd : dot x = dot y := by
    dsimp [dot,u,v]; linear_combination (hE - hF)/2
  have hid (z : ℝ²) : dot z ^ 2 + lineSide a b z ^ 2 =
      (u^2+v^2)*((z 0-a 0)^2+(z 1-a 1)^2) := by dsimp [lineSide,dot,u,v]; ring
  have hh := hid x
  rw [hd,hE,← hid y] at hh
  have hside : lineSide a b x = lineSide a b y := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (add_left_cancel hh) with he | he
    · exact he
    · rw [he] at hs
      nlinarith only [hs,sq_nonneg (lineSide a b y)]
  have huv : u^2+v^2 ≠ 0 := by
    intro hz
    obtain ⟨hu2,hv2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg u) (sq_nonneg v)).mp hz
    have hu : u = 0 := by simpa using hu2
    have hv : v = 0 := by simpa using hv2
    apply hab
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp hu).symm
    · exact (sub_eq_zero.mp hv).symm
  change u*(x 1-a 1) - v*(x 0-a 0) = u*(y 1-a 1) - v*(y 0-a 0) at hside
  dsimp only [dot] at hd
  ext i
  fin_cases i
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 0 = (u^2+v^2)*y 0
    linear_combination u*hd-v*hside
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 1 = (u^2+v^2)*y 1
    linear_combination v*hd+u*hside

namespace CircleChain

variable {P Q : Finset ℝ²} {p b : ℝ²} {r s : ℝ}

theorem edge_card (L : CircleChain P Q p r) (i : Fin L.n) : (L.edge i).card = 2 := by
  obtain ⟨x,y,hxy,he,-⟩ := L.drawn i
  rw [he,card_pair hxy]

theorem mem_curve_iff (L : CircleChain P Q p r) (i : Fin L.n) (v : Q) :
    (v : ℝ²) ∈ L.curve i ↔ v ∈ L.edge i := by
  obtain ⟨x,y,hxy,he,γ,_,hg,ha⟩ := L.drawn i
  refine ⟨ha v,?_⟩
  intro h
  rw [hg]
  rw [he,mem_insert,mem_singleton] at h
  rcases h with rfl|rfl
  · exact γ.source_mem_range
  · exact γ.target_mem_range

private theorem equidistant (L : CircleChain P Q p r) {i j : Fin L.n} {x y : ℝ²}
    (hx : x ∈ L.curve i) (hy : y ∈ L.curve j) : dist x p = dist y p := by
  rw [dist_comm x p,dist_comm y p,L.onCircle i _ hx,L.onCircle j _ hy]

/-- One arc, together with a circle at a different center, has at most one
common point: every point of the arc is on the same side of the line of centers. -/
theorem meet_unique (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i : Fin L.n} {j j' : Fin M.n} {x y : ℝ²}
    (hx : x ∈ L.curve i) (hy : y ∈ L.curve i) (hx' : x ∈ M.curve j) (hy' : y ∈ M.curve j') :
    x = y :=
  eq_of_dist_eq_in_same_halfplane hne (L.equidistant hx hy) (M.equidistant hx' hy')
    (L.halfplanes i b hb hne x y hx hy)

theorem edge_ne (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) (i : Fin L.n) (j : Fin M.n) : L.edge i ≠ M.edge j := by
  intro eq
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < (L.edge i).card by rw [L.edge_card]; decide)
  exact hxy (Subtype.ext (L.meet_unique M hb hne ((L.mem_curve_iff _ _).mpr hx)
    ((L.mem_curve_iff _ _).mpr hy) ((M.mem_curve_iff _ _).mpr (eq ▸ hx))
    ((M.mem_curve_iff _ _).mpr (eq ▸ hy))))

/-- A shared point outside the data set forces four distinct endpoints. -/
theorem four_ends (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i : Fin L.n} {j : Fin M.n} {z : ℝ²}
    (hz : z ∉ Q) (hz₁ : z ∈ L.curve i) (hz₂ : z ∈ M.curve j) :
    (L.edge i ∪ M.edge j).card = 4 := by
  have hd : Disjoint (L.edge i) (M.edge j) := disjoint_left.mpr fun v hv hv' =>
    hz ((L.meet_unique M hb hne ((L.mem_curve_iff _ _).mpr hv) hz₁
      ((M.mem_curve_iff _ _).mpr hv') hz₂) ▸ v.property)
  rw [card_union_of_disjoint hd,L.edge_card,M.edge_card]

/-- Given two fixed circles, the side of the line of centers determines both
participating edges at a crossing away from the data points. -/
theorem crossing_pair_eq (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i i' : Fin L.n} {j j' : Fin M.n} {x y : ℝ²}
    (hx : x ∉ Q) (hy : y ∉ Q) (hxi : x ∈ L.curve i) (hxj : x ∈ M.curve j)
    (hyi : y ∈ L.curve i') (hyj : y ∈ M.curve j')
    (hsgn : decide (0 < lineSide p b x) = decide (0 < lineSide p b y)) : i = i' ∧ j = j' := by
  have hx' := L.halfplanes i b hb hne x x hxi hxi
  have hy' := L.halfplanes i' b hb hne y y hyi hyi
  have hs : 0 < lineSide p b x * lineSide p b y := by
    by_cases h : 0 < lineSide p b x
    · exact mul_pos h (by simpa [h] using hsgn)
    · have h' : ¬ 0 < lineSide p b y := by simpa [h] using hsgn
      apply mul_pos_of_neg_of_neg
      · exact lt_of_le_of_ne (le_of_not_gt h) (fun e => by simp [e] at hx')
      · exact lt_of_le_of_ne (le_of_not_gt h') (fun e => by simp [e] at hy')
  obtain rfl := eq_of_dist_eq_in_same_halfplane hne (L.equidistant hxi hyi) (M.equidistant hxj hyj) hs
  exact ⟨L.uniqueOutside _ _ _ hx hxi hyi,M.uniqueOutside _ _ _ hy hxj hyj⟩

end CircleChain

end OMA.Math652ArcOrder

/- Combine the disjoint radius classes into the finite drawing; the side of
the center line identifies an exceptional intersection of two circles. -/

namespace OMA.Math652ArcOrder

open Finset
open scoped EuclideanGeometry Classical

private abbrev RingTag (P Q : Finset ℝ²) := (p : P) × (Q.image (dist (p : ℝ²)))

private noncomputable abbrev chain {P Q : Finset ℝ²} (a : RingTag P Q) :=
  circleChain P Q a.1 a.1.property a.2

private abbrev EdgeTag (P Q : Finset ℝ²) := (a : RingTag P Q) × Fin (chain a).n

private noncomputable abbrev drawEdge {P Q : Finset ℝ²} (e : EdgeTag P Q) := (chain e.1).edge e.2
private noncomputable abbrev drawCurve {P Q : Finset ℝ²} (e : EdgeTag P Q) := (chain e.1).curve e.2

private theorem tagged_simple {P Q : Finset ℝ²} : Function.Injective (@drawEdge P Q) := by
  rintro ⟨⟨⟨p,hp⟩,⟨r,hr⟩⟩,i⟩ ⟨⟨⟨b,hb⟩,⟨s,hs⟩⟩,j⟩ eq
  let L := circleChain P Q p hp r
  let M := circleChain P Q b hb s
  change L.edge i = M.edge j at eq
  have same : p = b := by by_contra h; exact L.edge_ne M hb h i j eq
  subst b
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (L.edge i).card by rw [L.edge_card]; decide)
  have h1 := L.onCircle i x ((L.mem_curve_iff i x).mpr hx)
  have h2 := M.onCircle j x ((M.mem_curve_iff j x).mpr (eq ▸ hx))
  have hrs := h1.symm.trans h2
  cases hrs
  have hij := L.simple eq
  subst j
  rfl

private noncomputable def badPairs (P Q : Finset ℝ²) : Finset (EdgeTag P Q × EdgeTag P Q) :=
  univ.filter fun e => e.1 ≠ e.2 ∧ ∃ z : ℝ², z ∉ Q ∧ z ∈ drawCurve e.1 ∧ z ∈ drawCurve e.2

private theorem centers_ne {P Q : Finset ℝ²} {a b : EdgeTag P Q} (h : (a,b) ∈ badPairs P Q) :
    (a.1.1 : ℝ²) ≠ b.1.1 := by
  rcases a with ⟨⟨⟨p,hp⟩,⟨r,hr⟩⟩,i⟩
  rcases b with ⟨⟨⟨p',hp'⟩,⟨s,hs⟩⟩,j⟩
  obtain ⟨hne,z,hz,hi,hj⟩ := (mem_filter.mp h).2
  change p ≠ p'
  rintro rfl
  let L := circleChain P Q p hp r
  let M := circleChain P Q p hp' s
  have hrs := (L.onCircle i z hi).symm.trans (M.onCircle j z hj)
  subst s
  obtain rfl := L.uniqueOutside i j z hz hi hj
  exact hne rfl

private theorem card_badPairs {P Q : Finset ℝ²} :
    (badPairs P Q).card ≤ (Fintype.card (RingTag P Q))^2*2 := by
  let B := badPairs P Q
  have hv (u : B) : ∃ z : ℝ², z ∉ Q ∧ z ∈ drawCurve u.val.1 ∧ z ∈ drawCurve u.val.2 :=
    (mem_filter.mp u.property).2.2
  let w (u : B) : ℝ² := (hv u).choose
  have hw (u : B) : w u ∉ Q ∧ w u ∈ drawCurve u.val.1 ∧ w u ∈ drawCurve u.val.2 := (hv u).choose_spec
  let sgn (u : B) := decide (0 < lineSide u.val.1.1.1 u.val.2.1.1 (w u))
  let code (u : B) : (RingTag P Q × RingTag P Q) × Bool := ((u.val.1.1,u.val.2.1),sgn u)
  have inj : Function.Injective code := by
    rintro u v he
    have hc₁ : u.val.1.1 = v.val.1.1 := congrArg (fun t => t.1.1) he
    have hc₂ : u.val.2.1 = v.val.2.1 := congrArg (fun t => t.1.2) he
    have hsg : sgn u = sgn v := congrArg Prod.snd he
    obtain ⟨hu,hui,huj⟩ := hw u
    obtain ⟨hv',hvi,hvj⟩ := hw v
    have hne := centers_ne u.property
    rcases u with ⟨⟨⟨a,i⟩,⟨b,j⟩⟩,hu'⟩
    rcases v with ⟨⟨⟨a',i'⟩,⟨b',j'⟩⟩,hv''⟩
    change a = a' at hc₁
    change b = b' at hc₂
    subst a'; subst b'
    obtain ⟨rfl,rfl⟩ := (chain a).crossing_pair_eq (chain b) b.1.property hne hu hv' hui huj hvi hvj hsg
    rfl
  simpa [B,pow_two] using Fintype.card_le_of_injective code inj

private theorem tag_counts (P Q : Finset ℝ²) (D : ℕ) (hk : 2 ≤ P.card)
    (hD : ∀ p ∈ P, (Q.image (dist p)).card ≤ D) :
    Fintype.card (RingTag P Q) ≤ P.card*D ∧
    P.card*Q.card ≤ Fintype.card (EdgeTag P Q) + 4*P.card^2*(D+1) := by
  have hrings : Fintype.card (RingTag P Q) ≤ P.card*D := by
    rw [Fintype.card_sigma]
    calc _ ≤ ∑ _p : P, D := sum_le_sum fun p _ => by simpa using hD (p : ℝ²) p.property
         _ = _ := by simp
  have htotal : (∑ c : RingTag P Q, (layer Q c.1 c.2).card) = P.card*Q.card := by
    rw [Fintype.sum_sigma]
    have hf (p : P) : (∑ r : Q.image (dist (p : ℝ²)), (layer Q p r).card) = Q.card := by
      exact (sum_coe_sort (Q.image (dist (p : ℝ²))) (fun r : ℝ => (layer Q p r).card)).trans
        (card_eq_sum_card_image (dist (p : ℝ²)) Q).symm
    calc _ = ∑ _p : P, Q.card := sum_congr rfl fun p _ => hf p
         _ = _ := by simp
  have htag : (∑ c : RingTag P Q, (chain c).n) = Fintype.card (EdgeTag P Q) := by
    rw [Fintype.card_sigma]; simp
  have hsum := sum_le_sum (s := (univ : Finset (RingTag P Q))) fun c _ => (chain c).count
  simp only [sum_add_distrib,htotal,htag,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at hsum
  refine ⟨hrings,hsum.trans ?_⟩
  calc _ = Fintype.card (EdgeTag P Q) + Fintype.card (RingTag P Q) * (4*(P.card-1)+1) := by ring
       _ ≤ Fintype.card (EdgeTag P Q) + (P.card*D) * (4*P.card) :=
         Nat.add_le_add_left (Nat.mul_le_mul hrings (by omega)) _
       _ ≤ _ := by nlinarith

/-- The cut-circle drawing gives the geometric input to the Mathialagan reduction. -/
theorem global_circle_drawing : OMA.R_Erdos652_erdos_652_variants_mathialagan_R1.H2 := by
  intro P Q D hk _ hD
  let encode (a : EdgeTag P Q) : ℕ := (Fintype.equivFin (EdgeTag P Q) a).val
  have inj : Function.Injective encode := Fin.val_injective.comp (Fintype.equivFin _).injective
  let both := Prod.map encode encode
  let E := univ.image encode
  let C := (badPairs P Q).image both
  let edge := Function.extend encode drawEdge (fun _ => ∅)
  let curve := Function.extend encode drawCurve (fun _ => ∅)
  have e_eq (a : EdgeTag P Q) : edge (encode a) = drawEdge a := inj.extend_apply _ _ a
  have c_eq (a : EdgeTag P Q) : curve (encode a) = drawCurve a := inj.extend_apply _ _ a
  have hE : E.card = Fintype.card (EdgeTag P Q) :=
    (card_image_of_injective univ inj).trans card_univ
  obtain ⟨hrings,hcount⟩ := tag_counts P Q D hk hD
  refine ⟨E,edge,curve,C,?_,?_,?_,?_,hE ▸ hcount,?_⟩
  · intro i hi
    obtain ⟨a,_,rfl⟩ := mem_image.mp hi
    rw [e_eq,c_eq]
    exact (chain a.1).drawn a.2
  · intro i hi j hj he
    obtain ⟨a,_,rfl⟩ := mem_image.mp hi
    obtain ⟨b,_,rfl⟩ := mem_image.mp hj
    rw [e_eq,e_eq] at he
    exact congrArg encode (tagged_simple he)
  · intro i hi j hj hne he z hz
    obtain ⟨a,_,rfl⟩ := mem_image.mp hi
    obtain ⟨b,_,rfl⟩ := mem_image.mp hj
    obtain ⟨ha,hb⟩ := hz
    rw [c_eq] at ha hb
    have hzQ : z ∈ Q := by
      by_contra h
      exact he (mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨mem_univ _,fun h => hne (congrArg encode h),z,h,ha,hb⟩,rfl⟩)
    refine ⟨⟨z,hzQ⟩,?_,rfl⟩
    rw [e_eq,e_eq]
    exact mem_inter.mpr ⟨((chain a.1).mem_curve_iff _ _).mp ha,((chain b.1).mem_curve_iff _ _).mp hb⟩
  · intro ij hij
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hij
    obtain ⟨z,hz,ha,hb⟩ := (mem_filter.mp hab).2.2
    change (edge (encode a) ∪ edge (encode b)).card = 4
    rw [e_eq,e_eq]
    exact (chain a.1).four_ends (chain b.1) b.1.1.property (centers_ne hab) hz ha hb
  · calc C.card ≤ (badPairs P Q).card := card_image_le
         _ ≤ (Fintype.card (RingTag P Q))^2*2 := card_badPairs
         _ ≤ (P.card*D)^2*2 := by gcongr
         _ = 2*(P.card*D)^2 := Nat.mul_comm _ _

end OMA.Math652ArcOrder

theorem OMA.E652Corollaries.mathialagan : type_of% @Erdos652.erdos_652.variants.mathialagan :=
  OMA.R_Erdos652_erdos_652_variants_mathialagan_R1.main OMA.Grid652.plane_drawing_bound
    OMA.Math652ArcOrder.global_circle_drawing
end

namespace OMA.E652Corollaries

open Filter Finset Erdos652
open scoped EuclideanGeometry Classical

/-- The existing order-sqrt reduction requires only nested sets at arbitrarily large sizes. -/
theorem orderLowerOfMathialagan (inc : type_of% @erdos_652.variants.mathialagan) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∃ᶠ n : ℕ in atTop,
      ∀ P Q : Finset ℝ², P ⊆ Q → P.card = k → Q.card = n →
        ∃ p ∈ P, c * Real.sqrt ((k : ℝ) * n) ≤ ((Q.image fun q => dist q p).card : ℝ) := by
  obtain ⟨c,hc,h⟩ := inc
  refine ⟨c,hc,fun k hk => ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop (k^3)] with n hn P Q _ hP hQ
  obtain ⟨p,hp,hd⟩ := h P Q (hP ▸ hk) (by simpa only [hP,hQ] using hn)
  exact ⟨p,hp,by simpa only [hP,hQ,dist_comm p] using hd⟩

end OMA.E652Corollaries

end

section

/-! A rectangular version of Elekes's construction. The grid has `m` columns and
`k*m` radial levels. Adapted from the square-grid proof by @Deldor14. -/
open scoped EuclideanGeometry
open Finset Filter
namespace OMA.E652Rectangle
noncomputable section

private def anchor (h : ℕ) : ℝ² := WithLp.toLp 2 ![(h : ℝ), 0]
private def grid (m r : ℕ) (p : Fin m × Fin r) : ℝ² :=
  WithLp.toLp 2 ![-(p.1.val : ℝ), Real.sqrt ((m : ℝ)^2 + p.2.val - (p.1.val : ℝ)^2)]

private theorem height_nonneg (m r : ℕ) (p : Fin m × Fin r) :
    0 ≤ (m : ℝ)^2 + p.2.val - (p.1.val : ℝ)^2 := by
  have hx : (p.1.val : ℝ) ≤ m := by exact_mod_cast p.1.isLt.le
  have hs := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) p.1.val) hx
  nlinarith [Nat.cast_nonneg (α := ℝ) p.2.val]

private theorem grid_inj (m r : ℕ) : Function.Injective (grid m r) := by
  intro p q hpq
  have h₁ := congrArg (fun z : ℝ² => z 0) hpq
  change -(p.1.val : ℝ) = -(q.1.val : ℝ) at h₁
  have hx : p.1 = q.1 := Fin.ext (by exact_mod_cast neg_inj.mp h₁)
  have h₂ := congrArg (fun z : ℝ² => (z 1)^2) hpq
  change (Real.sqrt _)^2 = (Real.sqrt _)^2 at h₂
  rw [Real.sq_sqrt (height_nonneg m r p), Real.sq_sqrt (height_nonneg m r q), hx] at h₂
  exact Prod.ext hx (Fin.ext (by exact_mod_cast (show (p.2.val : ℝ) = q.2.val by linarith)))

private theorem grid_dist (m r h : ℕ) (p : Fin m × Fin r) :
    dist (grid m r p) (anchor h) =
      Real.sqrt ((m : ℝ)^2 + (h : ℝ)^2 + (p.2.val + 2*h*p.1.val : ℕ)) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  simp only [Real.dist_eq, sq_abs]
  change (-(p.1.val : ℝ) - h)^2 + (Real.sqrt _ - 0)^2 = _
  rw [sub_zero, Real.sq_sqrt (height_nonneg m r p)]
  push_cast
  ring

theorem construction (k n m : ℕ) (hk : k ≤ n) (hn : n ≤ m * (k * m)) :
    ∃ pts : Finset ℝ², pts.card = n ∧
      k ≤ (pts.filter fun v => distinctDistancesFrom pts v ≤ k + 3*k*m).card := by
  classical
  let A := (range k).image anchor
  let B := univ.image (grid m (k*m))
  have hai : Function.Injective anchor := by
    intro a b hab
    have he := congrArg (fun z : ℝ² => z 0) hab
    change (a : ℝ) = (b : ℝ) at he
    exact_mod_cast he
  have ha : A.card = k := by simp [A, card_image_of_injective _ hai]
  have hb : B.card = m * (k*m) := by simp [B, card_image_of_injective _ (grid_inj m (k*m))]
  obtain ⟨pts, hA, hpts, hcard⟩ := exists_subsuperset_card_eq
    (subset_union_left : A ⊆ A ∪ B) (ha ▸ hk)
    (hn.trans (hb ▸ card_le_card (subset_union_right : B ⊆ A ∪ B)))
  refine ⟨pts, hcard, ha.ge.trans (card_le_card (s := A) ?_)⟩
  intro x hx
  obtain ⟨h, hh, rfl⟩ := mem_image.mp hx
  have hhk := mem_range.mp hh
  refine mem_filter.mpr ⟨hA (mem_image.mpr ⟨h,hh,rfl⟩), ?_⟩
  let D := (range (3*k*m)).image (fun j : ℕ => Real.sqrt ((m:ℝ)^2 + (h:ℝ)^2 + j))
  have sub : ((pts.erase (anchor h)).image fun y => dist y (anchor h)) ⊆
      (A.image fun y => dist y (anchor h)) ∪ D := by
    rintro _ hy
    obtain ⟨y, hypts, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp (hpts (mem_of_mem_erase hypts)) with ha' | hb'
    · exact mem_union_left _ (mem_image_of_mem _ ha')
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hb'
      apply mem_union_right
      refine mem_image.mpr ⟨p.2.val+2*h*p.1.val, mem_range.mpr ?_, (grid_dist m (k*m) h p).symm⟩
      have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hhk.le) p.1.isLt.le
      nlinarith [p.2.isLt]
  have deq : distinctDistancesFrom pts (anchor h) =
      ((pts.erase (anchor h)).image fun y => dist y (anchor h)).card := by
    unfold distinctDistancesFrom
    apply congrArg Finset.card
    ext d
    simp only [mem_image, mem_erase]
  rw [deq]
  exact (card_le_card sub).trans ((card_union_le ..).trans <| Nat.add_le_add
    (card_image_le.trans ha.le) (card_image_le.trans (card_range _).le))
end
end OMA.E652Rectangle

end

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.order_sqrt :=
  OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1.main
    (OMA.E652Corollaries.orderLowerOfMathialagan OMA.E652Corollaries.mathialagan)
    OMA.E652Rectangle.construction
