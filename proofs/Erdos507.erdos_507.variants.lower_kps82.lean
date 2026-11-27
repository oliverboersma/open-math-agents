import FormalConjectures.ErdosProblems.«507»
import Mathlib

/-!
# Komlós–Pintz–Szemerédi lower bound for Heilbronn's triangle problem (Erdős Problem 507)

Proves `Erdos507.erdos_507.variants.lower_kps82`:
- `R1`: reduces the lower bound on `α(n)` to a sparse grid/disk point sample (`H1`) and
  Duke–Lefmann–Rödl's linear 3-uniform hypergraph independence bound (`H2`).
- `H1`: grid sampling with bounded triangle and 4-vertex conflict counts.
- `H2`: weighted independent set (Verstraete–Wilson) bound for linear triple systems.
-/

/- The probabilistic construction of Komlós, Pintz and Szemerédi, followed by the
independence bound for linear hypergraphs of Duke, Lefmann and Rödl. The geometric
lemmas use the coordinate method in the project's Erdős lower-bound proof. The deletion of
vertices in conflicting triangles and the passage to the minimum triangle area are proved below. -/

namespace OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1

open Finset Asymptotics Filter Erdos507
open scoped EuclideanGeometry

open scoped Classical in
/-- A sample with few small triangles and few pairs of triangles sharing an edge.
The parameter d is an upper bound on average degree after removing at most half
the points, and its dependence on the area cutoff is recorded explicitly. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ (S : Finset ℝ²) (E : Finset (Finset ℝ²)) (d : ℝ),
      (S : Set ℝ²) ⊆ Metric.closedBall 0 1 ∧
      (∀ e ∈ E, e ⊆ S ∧ e.card = 3) ∧
      (∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
        |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ ε * lowerBest n →
        univ.image p ∈ E) ∧
      2 * (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ S.card ∧
      2 ≤ d ∧ 6 * (E.card : ℝ) ≤ d * S.card ∧
      d / Real.log d ≤ C * ε * ((S.card : ℝ) / n) ^ 2

open scoped Classical in
/-- The independence number bound of Duke, Lefmann and Rödl for a linear
three-uniform hypergraph of average degree at most d. -/
def H2 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Finset V)) (d : ℝ),
    2 ≤ d → (∀ e ∈ E, e ⊆ S ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    3 * (E.card : ℝ) ≤ d * S.card →
    ∃ I ⊆ S, (∀ e ∈ E, ¬ e ⊆ I) ∧
      a * S.card * Real.sqrt (Real.log d / d) ≤ (I.card : ℝ)

open scoped Classical in
private theorem delete_conflicts {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 3)
    (hX : 2 * (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ S.card) :
    ∃ W ⊆ S, S.card ≤ 2 * W.card ∧
      ∀ e ∈ E, e ⊆ W → ∀ f ∈ E, f ⊆ W → e ≠ f → (e ∩ f).card ≤ 1 := by
  let X := (E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card
  have choose_one (q : X) : ∃ x, x ∈ q.1.1 ∧ x ∈ q.1.2 := by
    have hq := (mem_filter.mp q.2).2.2
    exact (Finset.card_pos.mp (by omega : 0 < (q.1.1 ∩ q.1.2).card)).imp
      (fun _ hx => mem_inter.mp hx)
  choose remove hremove using choose_one
  let R : Finset V := univ.image remove
  have hR : R ⊆ S := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := mem_image.mp hx
    have hq : q.1 ∈ E ×ˢ E := (mem_filter.mp q.2).1
    exact (hE q.1.1 (mem_product.mp hq).1).1 (hremove q).1
  have hRcard : R.card ≤ X.card := by
    simpa [R] using card_image_le (f := remove) (s := (univ : Finset X))
  refine ⟨S \ R, sdiff_subset, ?_, ?_⟩
  · have hcard := card_sdiff_of_subset hR
    change 2 * X.card ≤ S.card at hX
    omega
  · intro e he hWe f hf hWf hne
    by_contra! hbad
    let q : X := ⟨(e,f), mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩, hne, by
      change 2 ≤ (e ∩ f).card
      omega⟩⟩
    have hr : remove q ∈ R := mem_image.mpr ⟨q, mem_univ _, rfl⟩
    have hw : remove q ∈ S \ R := hWe (hremove q).1
    exact (mem_sdiff.mp hw).2 hr

private theorem signed_area_formula (a b c : ℝ²) :
    EuclideanGeometry.triangle_area a b c =
      ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp
  ring

private theorem collinear_area {T : Set ℝ²} (hT : Collinear ℝ T)
    {a b c : ℝ²} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    EuclideanGeometry.triangle_area a b c = 0 := by
  obtain ⟨base, v, onLine⟩ := (collinear_iff_exists_forall_eq_smul_vadd T).mp hT
  obtain ⟨x, rfl⟩ := onLine a ha
  obtain ⟨y, rfl⟩ := onLine b hb
  obtain ⟨z, rfl⟩ := onLine c hc
  rw [signed_area_formula]
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem disk_area_bound {a b c : ℝ²}
    (ha : a ∈ Metric.closedBall (0 : ℝ²) 1)
    (hb : b ∈ Metric.closedBall (0 : ℝ²) 1)
    (hc : c ∈ Metric.closedBall (0 : ℝ²) 1) :
    |EuclideanGeometry.triangle_area a b c| ≤ 4 := by
  have hcoord (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i| ≤ 1 := by
    have hnorm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans hnorm
  have hdiff (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i - c i| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hcoord x hx i, hcoord c hc i])
  rw [signed_area_formula, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num)]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h₁ := mul_le_mul (hdiff a ha 0) (hdiff b hb 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := mul_le_mul (hdiff b hb 0) (hdiff a ha 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

private theorem le_alpha_of_triangles {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℝ²) (hcard : S.card = n) (hS : (S : Set ℝ²) ⊆ Metric.closedBall 0 1)
    {r : ℝ} (hr : 0 < r) (htri : ∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
      r ≤ |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)|) : r ≤ α n := by
  have find_triple (T : Finset ℝ²) (hT : T.card = n) :
      ∃ p : Fin 3 → ℝ², Function.Injective p ∧ ∀ i, p i ∈ T := by
    obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin 3) (s := T) (by simpa [hT] using hn)
    exact ⟨g,g.injective,fun i => hg (Set.mem_range_self i)⟩
  obtain ⟨p, hp, hmem⟩ := find_triple S hcard
  have hcol : ¬ Collinear ℝ (S : Set ℝ²) := by
    intro hc
    have he := collinear_area hc (hmem 0) (hmem 1) (hmem 2)
    have h := htri p hp hmem
    rw [he, abs_zero] at h
    exact hr.not_ge h
  have hmin : r ≤ minTriangleArea S := by
    apply le_csInf
    · exact ⟨_, p, hp, hmem, rfl⟩
    · rintro _ ⟨q, hq, hm, rfl⟩
      exact htri q hq hm
  apply hmin.trans
  unfold α
  apply le_csSup
  · refine ⟨4, ?_⟩
    rintro _ ⟨T, ⟨hT, hDisk, _⟩, rfl⟩
    obtain ⟨q, hq, hm⟩ := find_triple T hT
    have hmin' : minTriangleArea T ≤ |EuclideanGeometry.triangle_area (q 0) (q 1) (q 2)| := by
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro _ ⟨u, hu, hmu, rfl⟩
        exact abs_nonneg _
      · exact ⟨q, hq, hm, rfl⟩
    exact hmin'.trans (disk_area_bound (hDisk (hm 0)) (hDisk (hm 1)) (hDisk (hm 2)))
  · exact ⟨S, ⟨hcard,hS,hcol⟩, rfl⟩

theorem main : H1 → H2 → type_of% @Erdos507.erdos_507.variants.lower_kps82 := by
  classical
  rintro ⟨C,hC,hSample⟩ ⟨a,ha,hInd⟩
  let ε := a^2 / (4*C)
  have hε : 0 < ε := by positivity
  refine Asymptotics.IsBigO.of_bound ε⁻¹ ?_
  filter_upwards [hSample ε hε, eventually_ge_atTop (3 : ℕ)] with n hs hn
  obtain ⟨S,E,d,hDisk,hEdges,hCover,hConf,hd,hDegree,hRatio⟩ := hs
  obtain ⟨W,hWS,hSW,hLinear⟩ := delete_conflicts S E hEdges hConf
  let F := E.filter (fun e => e ⊆ W)
  have hF (e) (he : e ∈ F) : e ⊆ W ∧ e.card = 3 := by
    obtain ⟨heE, heW⟩ := mem_filter.mp he
    exact ⟨heW, (hEdges e heE).2⟩
  have hFLinear (e) (he : e ∈ F) (f) (hf : f ∈ F) (hne : e ≠ f) : (e ∩ f).card ≤ 1 :=
    hLinear e (mem_filter.mp he).1 (hF e he).1 f (mem_filter.mp hf).1 (hF f hf).1 hne
  have hFcard : (F.card : ℝ) ≤ E.card := by exact_mod_cast card_filter_le _ _
  have hSW' : (S.card : ℝ) ≤ 2 * W.card := by exact_mod_cast hSW
  have hd0 : 0 < d := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log d := Real.log_pos (by linarith)
  have hFdeg : 3 * (F.card : ℝ) ≤ d * W.card := by
    have h := mul_le_mul_of_nonneg_left hSW' hd0.le
    linarith
  obtain ⟨I,hIW,hFree,hI⟩ := hInd W F d hd hF hFLinear hFdeg
  have hcancel : C*ε = a^2/4 := by dsimp [ε]; field_simp
  have hDensity : d / Real.log d ≤ a^2 * ((W.card : ℝ)/n)^2 := by
    have hdivide : (S.card : ℝ) / n ≤ (2*W.card) / n :=
      div_le_div_of_nonneg_right hSW' hn0.le
    rw [hcancel] at hRatio
    refine hRatio.trans ?_
    calc a^2 / 4 * ((S.card : ℝ) / n)^2 ≤ a^2 / 4 * ((2*W.card : ℝ) / n)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdivide 2) (by positivity)
        _ = _ := by ring
  rw [div_pow, ← mul_div_assoc] at hDensity
  have hSquared : (n : ℝ)^2 ≤ (a*W.card*Real.sqrt (Real.log d/d))^2 := by
    calc (n : ℝ)^2 = (d / Real.log d * (n : ℝ)^2) * (Real.log d / d) := by
          field_simp
        _ ≤ a^2 * (W.card : ℝ)^2 * (Real.log d / d) :=
          mul_le_mul_of_nonneg_right ((le_div_iff₀ (sq_pos_of_pos hn0)).mp hDensity) (by positivity)
        _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hEnough : n ≤ I.card := by
    have hRange : 0 ≤ a*W.card*Real.sqrt (Real.log d/d) := by positivity
    exact_mod_cast ((sq_le_sq₀ hn0.le hRange).mp hSquared).trans hI
  obtain ⟨T,hTI,hTcard⟩ := exists_subset_card_eq hEnough
  have hTW : T ⊆ W := hTI.trans hIW
  have hTS : T ⊆ S := hTW.trans hWS
  have hLowerPos : 0 < lowerBest n := by
    unfold lowerBest
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) (by positivity)
  have αlower : ε * lowerBest n ≤ α n := by
    apply le_alpha_of_triangles hn T hTcard (fun _ hm => hDisk (hTS hm)) (mul_pos hε hLowerPos)
    intro p hp hM
    by_contra! hSmall
    have hMem : univ.image p ∈ E := hCover p hp (fun i => hTS (hM i)) hSmall.le
    have hInside : univ.image p ⊆ I := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hTI (hM j)
    exact hFree _ (mem_filter.mpr ⟨hMem, hInside.trans hIW⟩) hInside
  have hα0 : 0 ≤ α n := (mul_pos hε hLowerPos).le.trans αlower
  rw [Real.norm_of_nonneg hLowerPos.le, Real.norm_of_nonneg hα0]
  calc lowerBest n = ε⁻¹ * (ε * lowerBest n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left αlower (inv_nonneg.mpr hε.le)

end OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1

section H1Part

/- Slice counting for small triangles on an integer grid. The estimate is
valid before normalization to the unit disk. -/

namespace OMA.HeilbronnGrid

open Finset
open scoped BigOperators

private theorem fiber_bound {m : ℕ} (a b t : ℝ) (ha : a ≠ 0) (ht : 0 ≤ t) :
    (((univ : Finset (Fin m)).filter fun x => |a*(x.val : ℝ)+b| ≤ t).card : ℝ)
      ≤ 1 + 2*t/|a| := by
  let S := (univ : Finset (Fin m)).filter fun x => |a*(x.val : ℝ)+b| ≤ t
  change (S.card : ℝ) ≤ _
  by_cases hS : S.Nonempty
  · let P := S.image Fin.val
    have hP : P.Nonempty := hS.image Fin.val
    let lo := P.min' hP
    let hi := P.max' hP
    have hLo : lo ∈ P := P.min'_mem hP
    have hHi : hi ∈ P := P.max'_mem hP
    have hOrder : lo ≤ hi := P.min'_le hi hHi
    have hsub : P ⊆ Icc lo hi :=
      fun j hj => mem_Icc.mpr ⟨P.min'_le j hj, P.le_max' j hj⟩
    have hcard : S.card ≤ hi + 1 - lo := by
      have hinj : Function.Injective (Fin.val : Fin m → ℕ) := Fin.val_injective
      rw [← card_image_of_injective S hinj]
      change P.card ≤ _
      simpa [Nat.card_Icc] using card_le_card hsub
    have hlo : |a*(lo : ℝ)+b| ≤ t := by
      obtain ⟨x, hx, hval⟩ := mem_image.mp hLo
      rw [← hval]
      exact (mem_filter.mp hx).2
    have hhi : |a*(hi : ℝ)+b| ≤ t := by
      obtain ⟨x, hx, hval⟩ := mem_image.mp hHi
      rw [← hval]
      exact (mem_filter.mp hx).2
    have hOrderR : (lo : ℝ) ≤ hi := by exact_mod_cast hOrder
    have hw : |a| * ((hi : ℝ)-lo) ≤ 2*t := by
      rw [← abs_of_nonneg (sub_nonneg.mpr hOrderR), ← abs_mul]
      rw [show a*((hi : ℝ)-lo) = (a*hi+b)-(a*lo+b) by ring]
      exact (abs_sub _ _).trans (by linarith)
    have hAbs : 0 < |a| := abs_pos.mpr ha
    have hw' : (hi : ℝ)-lo ≤ 2*t/|a| := (le_div_iff₀ hAbs).mpr (by simpa only [mul_comm] using hw)
    have hc : (S.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_sub (by omega : lo ≤ hi+1), Nat.cast_add, Nat.cast_one] at hc
    linarith
  · have hzero : S.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hS)
    rw [hzero, Nat.cast_zero]
    positivity

theorem strip_bound {m : ℕ} (a b c t : ℝ) (hb : b ≠ 0) (ht : 0 ≤ t) :
    (((univ : Finset (Fin m × Fin m)).filter
      fun p => |a*(p.1.val : ℝ)+b*(p.2.val : ℝ)+c| ≤ t).card : ℝ)
      ≤ (m : ℝ) * (1 + 2*t/|b|) := by
  let strip := ((univ : Finset (Fin m × Fin m)).filter
      fun p => |a*(p.1.val : ℝ)+b*(p.2.val : ℝ)+c| ≤ t)
  let ys (x : Fin m) := (univ : Finset (Fin m)).filter
      fun y => |a*(x.val : ℝ)+b*(y.val : ℝ)+c| ≤ t
  have hcount : strip.card = ∑ x : Fin m, (ys x).card := by
    rw [card_filter, Fintype.sum_prod_type]
    simp only [ys, card_filter]
  have hslice (x : Fin m) : ((ys x).card : ℝ) ≤ 1 + 2*t/|b| := by
    simpa only [ys, add_comm (a*(x.val : ℝ)), add_assoc] using fiber_bound b (a*x.val+c) t hb ht
  change (strip.card : ℝ) ≤ _
  rw [hcount, Nat.cast_sum]
  calc
    _ ≤ ∑ _x : Fin m, (1 + 2*t/|b|) := sum_le_sum (fun x _ => hslice x)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]


abbrev Grid (m : ℕ) := Fin m × Fin m

/-- Distance in the original integer coordinates, before scaling. -/
def gridDistance {m : ℕ} (a b : Grid m) : ℕ :=
  max (Nat.dist a.1.val b.1.val) (Nat.dist a.2.val b.2.val)

private theorem coordinate_band {m : ℕ} (a : Fin m) (j : ℕ) :
    ((univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val ≤ j).card ≤ 2*j+1 := by
  let B := (univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val ≤ j
  change B.card ≤ _
  rw [← card_image_of_injective B Fin.val_injective]
  have hsub : B.image Fin.val ⊆ Icc (a.val-j) (a.val+j) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have hd := (mem_filter.mp hb).2
    unfold Nat.dist at hd
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

private theorem coordinate_shell {m : ℕ} (a : Fin m) (j : ℕ) :
    ((univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val = j).card ≤ 2 := by
  let B := (univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val = j
  change B.card ≤ _
  rw [← card_image_of_injective B Fin.val_injective]
  have hsub : B.image Fin.val ⊆ {a.val-j,a.val+j} := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have hd := (mem_filter.mp hb).2
    simp only [mem_insert, mem_singleton]
    unfold Nat.dist at hd
    omega
  exact (card_le_card hsub).trans (by
    exact (card_insert_le _ _).trans (by simp))

/-- At most twelve times the radius many grid points have a given positive distance. -/
theorem shell_bound {m : ℕ} (a : Grid m) (j : ℕ) (hj : 0 < j) :
    ((univ : Finset (Grid m)).filter fun b => gridDistance a b = j).card ≤ 12*j := by
  let U₁ := (univ : Finset (Fin m)).filter fun x => Nat.dist a.1.val x.val ≤ j
  let U₂ := (univ : Finset (Fin m)).filter fun y => Nat.dist a.2.val y.val ≤ j
  let D₁ := (univ : Finset (Fin m)).filter fun x => Nat.dist a.1.val x.val = j
  let D₂ := (univ : Finset (Fin m)).filter fun y => Nat.dist a.2.val y.val = j
  have hsub : ((univ : Finset (Grid m)).filter fun b => gridDistance a b = j) ⊆
      D₁ ×ˢ U₂ ∪ U₁ ×ˢ D₂ := by
    rintro ⟨x,y⟩ h
    have hd := (mem_filter.mp h).2
    change max (Nat.dist a.1.val x.val) (Nat.dist a.2.val y.val) = j at hd
    have hx : Nat.dist a.1.val x.val ≤ j := hd ▸ le_max_left _ _
    have hy : Nat.dist a.2.val y.val ≤ j := hd ▸ le_max_right _ _
    rcases le_total (Nat.dist a.1.val x.val) (Nat.dist a.2.val y.val) with hxy | hyx
    · rw [max_eq_right hxy] at hd
      exact mem_union_right _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,
        mem_filter.mpr ⟨mem_univ _,hd⟩⟩)
    · rw [max_eq_left hyx] at hd
      exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hd⟩,
        mem_filter.mpr ⟨mem_univ _,hy⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_product, card_product]
  have h1 := Nat.mul_le_mul (coordinate_shell a.1 j) (coordinate_band a.2 j)
  have h2 := Nat.mul_le_mul (coordinate_band a.1 j) (coordinate_shell a.2 j)
  change D₁.card*U₂.card ≤ _ at h1
  change U₁.card*D₂.card ≤ _ at h2
  omega

theorem gridDistance_pos {m : ℕ} {a b : Grid m} (h : a ≠ b) : 0 < gridDistance a b := by
  by_contra! h'
  have hx : Nat.dist a.1.val b.1.val = 0 := by
    change max (Nat.dist a.1.val b.1.val) (Nat.dist a.2.val b.2.val) ≤ 0 at h'
    exact Nat.le_zero.mp ((le_max_left _ _).trans h')
  have hy : Nat.dist a.2.val b.2.val = 0 := by
    exact Nat.le_zero.mp ((le_max_right _ _).trans h')
  apply h
  apply Prod.ext
  · apply Fin.ext
    unfold Nat.dist at hx
    omega
  · apply Fin.ext
    unfold Nat.dist at hy
    omega

theorem gridDistance_lt {m : ℕ} (a b : Grid m) : gridDistance a b < m := by
  unfold gridDistance Nat.dist
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  have h3 := b.1.isLt
  have h4 := b.2.isLt
  omega


/-- Twice the signed area in the unscaled grid, up to orientation. -/
def determinant {m : ℕ} (a b c : Grid m) : ℝ :=
  ((b.1.val : ℝ) - a.1.val)*((c.2.val : ℝ) - a.2.val) -
    ((b.2.val : ℝ) - a.2.val)*((c.1.val : ℝ) - a.1.val)

private theorem abs_coordinate_dist (x y : ℕ) :
    |(x : ℝ) - y| = (Nat.dist x y : ℝ) := by
  rcases le_total x y with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

theorem triangle_slice_bound {m : ℕ} {a b : Grid m} (hab : a ≠ b) (t : ℝ) (ht : 0 ≤ t) :
    (((univ : Finset (Grid m)).filter fun c => |determinant a b c| ≤ t).card : ℝ)
      ≤ (m : ℝ) * (1 + 2*t/(gridDistance a b : ℝ)) := by
  let x := (b.1.val : ℝ) - a.1.val
  let y := (b.2.val : ℝ) - a.2.val
  let z := y*a.1.val - x*a.2.val
  have hf (c : Grid m) : determinant a b c = (-y)*c.1.val + x*c.2.val + z := by
    unfold determinant
    dsimp [x,y,z]
    ring
  have hd : (gridDistance a b : ℝ) = max |x| |y| := by
    simp [gridDistance, x,y, Nat.cast_max, abs_coordinate_dist, Nat.dist_comm]
  have hpos : 0 < (gridDistance a b : ℝ) := by exact_mod_cast gridDistance_pos hab
  simp_rw [hf]
  rcases le_total |y| |x| with h | h
  · rw [hd, max_eq_left h]
    have hxb : x ≠ 0 := by
      rw [hd, max_eq_left h] at hpos
      exact (abs_pos.mp hpos)
    exact strip_bound (-y) x z t hxb ht
  · rw [hd, max_eq_right h]
    have hyb : -y ≠ 0 := by
      rw [hd, max_eq_right h] at hpos
      exact neg_ne_zero.mpr (abs_pos.mp hpos)
    let U := (univ : Finset (Grid m)).filter fun c => |(-y)*c.1.val+x*c.2.val+z| ≤ t
    let V := (univ : Finset (Grid m)).filter fun c => |x*c.1.val+(-y)*c.2.val+z| ≤ t
    have hUV : U.card = V.card := by
      apply card_equiv (Equiv.prodComm (Fin m) (Fin m))
      intro c
      simp [U,V,add_comm (x*(c.2.val : ℝ))]
    change (U.card : ℝ) ≤ _
    rw [hUV]
    simpa [V, abs_neg] using strip_bound (m := m) x (-y) z t hyb ht

private theorem group_radii {m : ℕ} (a : Grid m) (f : ℕ → ℝ) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), f (gridDistance a b)) =
      ∑ r ∈ Icc 1 m, ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ)*f r := by
  let S := (univ : Finset (Grid m)).filter fun b => b ≠ a
  have hm : ∀ b ∈ S, gridDistance a b ∈ Icc 1 m := by
    intro b hb
    have hne : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
    exact mem_Icc.mpr ⟨gridDistance_pos hne, (gridDistance_lt a b).le⟩
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_congr rfl
  intro r hr
  have hrPos : 0 < r := (mem_Icc.mp hr).1
  have hFiber : (S.filter fun b => gridDistance a b = r) =
      (univ.filter fun b : Grid m => gridDistance a b = r) := by
    ext b
    by_cases hb : b = a
    · subst b
      have hz : gridDistance a a = 0 := by simp [gridDistance]
      simp [S,hz,show (0 : ℕ) ≠ r by omega]
    · simp [S,hb]
  rw [hFiber]
  rw [show (∑ b ∈ (univ.filter fun b : Grid m => gridDistance a b = r),
        f (gridDistance a b)) = ∑ _ ∈ (univ.filter fun b : Grid m => gridDistance a b = r), f r by
    apply sum_congr rfl
    intro b hb
    rw [(mem_filter.mp hb).2]]
  simp

theorem first_inverse_moment {m : ℕ} (a : Grid m) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), (1 : ℝ) / gridDistance a b) ≤ 12*(m : ℝ) := by
  rw [group_radii a (fun j => (1 : ℝ)/j)]
  calc
    _ ≤ ∑ r ∈ Icc 1 m, (12 : ℝ) := by
      apply sum_le_sum
      intro r hr
      have hrNat : 0 < r := (mem_Icc.mp hr).1
      have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrNat
      have hcard : ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ) ≤ 12*r := by
        exact_mod_cast shell_bound a r hrNat
      calc _ ≤ (12*(r : ℝ))*(1/r) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp [Nat.card_Icc, mul_comm]

theorem second_inverse_moment {m : ℕ} (a : Grid m) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), ((1 : ℝ) / gridDistance a b)^2)
      ≤ 12*(1 + Real.log m) := by
  rw [group_radii a (fun j => ((1 : ℝ)/j)^2)]
  calc
    _ ≤ ∑ r ∈ Icc 1 m, (12 : ℝ) * (r : ℝ)⁻¹ := by
      apply sum_le_sum
      intro r hr
      have hrNat : 0 < r := (mem_Icc.mp hr).1
      have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrNat
      have hcard : ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ) ≤ 12*r := by
        exact_mod_cast shell_bound a r hrNat
      calc _ ≤ (12*(r : ℝ))*(1/r)^2 := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp
    _ = 12*(harmonic m : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast <;> rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m) (by norm_num)


abbrev Triple (m : ℕ) := Grid m × Grid m × Grid m
abbrev Quadruple (m : ℕ) := Grid m × Grid m × Grid m × Grid m

noncomputable def triangleLabels {m : ℕ} (t : ℝ) : Finset (Triple m) :=
  univ.filter fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 ∧
    |determinant q.1 q.2.1 q.2.2| ≤ t

noncomputable def conflictLabels {m : ℕ} (t : ℝ) : Finset (Quadruple m) :=
  univ.filter fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
    q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2 ∧
      |determinant q.1 q.2.1 q.2.2.1| ≤ t ∧ |determinant q.1 q.2.1 q.2.2.2| ≤ t

private noncomputable def slice {m : ℕ} (a b : Grid m) (t : ℝ) : Finset (Grid m) :=
  univ.filter fun c => |determinant a b c| ≤ t

private theorem count_by_fibers {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ a : A, (@Finset.filter B (fun b => P (a,b))
      (fun b => inferInstance) univ).card := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

private theorem weaken_triangles {m : ℕ} (t : ℝ) :
    (triangleLabels (m:=m) t).card ≤
      ∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card := by
  let L : Finset (Triple m) := univ.filter fun q => q.2.1 ≠ q.1 ∧
    |determinant q.1 q.2.1 q.2.2| ≤ t
  have hsub : triangleLabels t ⊆ L := by
    intro q hq
    have h := (mem_filter.mp hq).2
    exact mem_filter.mpr ⟨mem_univ _, h.1.symm, h.2.2.2⟩
  refine (card_le_card hsub).trans_eq ?_
  dsimp only [L]
  rw [count_by_fibers]
  apply sum_congr rfl
  intro a ha
  rw [count_by_fibers, sum_filter]
  apply sum_congr rfl
  intro b hb
  by_cases h : b ≠ a <;> simp [h, slice]

private theorem weaken_conflicts {m : ℕ} (t : ℝ) :
    (conflictLabels (m:=m) t).card ≤
      ∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card^2 := by
  let L : Finset (Quadruple m) := univ.filter fun q => q.2.1 ≠ q.1 ∧
    |determinant q.1 q.2.1 q.2.2.1| ≤ t ∧ |determinant q.1 q.2.1 q.2.2.2| ≤ t
  have hsub : conflictLabels t ⊆ L := by
    intro q hq
    have h := (mem_filter.mp hq).2
    exact mem_filter.mpr ⟨mem_univ _, h.1.symm, h.2.2.2.2.2.2⟩
  refine (card_le_card hsub).trans_eq ?_
  dsimp only [L]
  rw [count_by_fibers]
  apply sum_congr rfl
  intro a ha
  rw [count_by_fibers, sum_filter]
  apply sum_congr rfl
  intro b hb
  by_cases h : b ≠ a
  · rw [if_pos h, pow_two, ← card_product]
    congr 1
    ext q
    simp [h, slice]
  · simp [h]

theorem triangles_total {m : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    ((triangleLabels (m:=m) t).card : ℝ) ≤ (m : ℝ)^5 + 24*t*(m : ℝ)^4 := by
  have hcast := (show ((triangleLabels (m:=m) t).card : ℝ) ≤
      ((∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card : ℕ) : ℝ) by
    exact_mod_cast weaken_triangles t)
  simp only [Nat.cast_sum] at hcast
  refine hcast.trans ?_
  have fibers (a : Grid m) : (∑ b ∈ univ.filter (· ≠ a), ((slice a b t).card : ℝ)) ≤
      (m : ℝ)^3 + 24*t*(m : ℝ)^2 := by
    calc
      _ ≤ ∑ b ∈ univ.filter (· ≠ a), (m : ℝ)*(1+2*t/(gridDistance a b : ℝ)) := by
        apply sum_le_sum
        intro b hb
        have hn : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
        exact triangle_slice_bound hn t ht
      _ = (m : ℝ)*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) +
          (2*t*(m : ℝ))*(∑ b ∈ univ.filter (· ≠ a), (1 : ℝ)/gridDistance a b) := by
        have hs : (∑ _b ∈ univ.filter (· ≠ a), (m : ℝ)) =
            (m : ℝ)*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
        rw [Finset.mul_sum, ← hs, ← sum_add_distrib]
        apply sum_congr rfl
        intro b hb
        ring
      _ ≤ _ := by
        have hcardNat := card_filter_le (s := (univ : Finset (Grid m))) (· ≠ a)
        have hcard : ((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) ≤ (m : ℝ)^2 := by
          simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at hcardNat
          exact_mod_cast (by simpa [pow_two] using hcardNat : _ ≤ m^2)
        have h1 := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m)
        have h2 := mul_le_mul_of_nonneg_left (first_inverse_moment a)
          (show 0 ≤ 2*t*(m : ℝ) by positivity)
        nlinarith only [h1,h2]
  calc
    _ ≤ ∑ _a : Grid m, ((m : ℝ)^3 + 24*t*(m : ℝ)^2) := sum_le_sum (fun a _ => fibers a)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod,Fintype.card_fin]; push_cast; ring

theorem conflicts_total {m : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    ((conflictLabels (m:=m) t).card : ℝ) ≤
      2*(m : ℝ)^6 + 96*t^2*(m : ℝ)^4*(1+Real.log m) := by
  have hcast := (show ((conflictLabels (m:=m) t).card : ℝ) ≤
      ((∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card^2 : ℕ) : ℝ) by
    exact_mod_cast weaken_conflicts t)
  simp only [Nat.cast_sum,Nat.cast_pow] at hcast
  refine hcast.trans ?_
  have fibers (a : Grid m) : (∑ b ∈ univ.filter (· ≠ a), ((slice a b t).card : ℝ)^2) ≤
      2*(m : ℝ)^4 + 96*t^2*(m : ℝ)^2*(1+Real.log m) := by
    calc
      _ ≤ ∑ b ∈ univ.filter (· ≠ a), (2*(m : ℝ)^2 + 8*t^2*(m : ℝ)^2*((1 : ℝ)/gridDistance a b)^2) := by
        apply sum_le_sum
        intro b hb
        have hn : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
        have hu := triangle_slice_bound hn t ht
        have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ((slice a b t).card : ℝ)) hu 2
        apply hs.trans
        have he : 2*(m : ℝ)^2 + 8*t^2*(m : ℝ)^2*((1 : ℝ)/gridDistance a b)^2 -
            ((m : ℝ)*(1+2*t/(gridDistance a b : ℝ)))^2 =
            (m : ℝ)^2*(1-2*t/(gridDistance a b : ℝ))^2 := by ring
        rw [← sub_nonneg, he]
        positivity
      _ = 2*(m : ℝ)^2*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) +
          (8*t^2*(m : ℝ)^2)*(∑ b ∈ univ.filter (· ≠ a), ((1 : ℝ)/gridDistance a b)^2) := by
        rw [Finset.mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm ((univ.filter (· ≠ a)).card : ℝ)]
      _ ≤ _ := by
        have hcardNat := card_filter_le (s := (univ : Finset (Grid m))) (· ≠ a)
        have hcard : ((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) ≤ (m : ℝ)^2 := by
          simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at hcardNat
          exact_mod_cast (by simpa [pow_two] using hcardNat : _ ≤ m^2)
        have h1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2*(m : ℝ)^2 by positivity)
        have h2 := mul_le_mul_of_nonneg_left (second_inverse_moment a)
          (show 0 ≤ 8*t^2*(m : ℝ)^2 by positivity)
        nlinarith only [h1,h2]
  calc
    _ ≤ ∑ _a : Grid m, (2*(m : ℝ)^4 + 96*t^2*(m : ℝ)^2*(1+Real.log m)) :=
      sum_le_sum (fun a _ => fibers a)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod,Fintype.card_fin]; push_cast; ring


open scoped EuclideanGeometry
open Finset

def tripleVerts {m : ℕ} (q : Triple m) : Finset (Grid m) :=
  {q.1,q.2.1,q.2.2}

def conflictVerts {m : ℕ} (q : Quadruple m) : Finset (Grid m) :=
  {q.1,q.2.1,q.2.2.1,q.2.2.2}

theorem triple_card {m : ℕ} {q : Triple m} {t : ℝ} (h : q ∈ triangleLabels t) :
    (tripleVerts q).card = 3 := by
  have hq := (mem_filter.mp h).2
  simp [tripleVerts, hq.1, hq.2.1, hq.2.2.1, card_insert_of_notMem]

theorem conflict_card {m : ℕ} {q : Quadruple m} {t : ℝ} (h : q ∈ conflictLabels t) :
    (conflictVerts q).card = 4 := by
  have hq := (mem_filter.mp h).2
  simp [conflictVerts, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1,
    hq.2.2.2.2.2.1, card_insert_of_notMem]

private theorem determinant_same_vertices {m : ℕ} (a b c x y z : Grid m)
    (he : ({a,b,c} : Finset (Grid m)) = {x,y,z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    |determinant a b c| = |determinant x y z| := by
  have hx : x = a ∨ x = b ∨ x = c := by
    have : x ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  have hy : y = a ∨ y = b ∨ y = c := by
    have : y ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  have hz : z = a ∨ z = b ∨ z = c := by
    have : z ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
    rcases hz with hz | hz | hz <;> subst x <;> subst y <;> subst z <;> try contradiction
  · rfl
  · rw [show determinant a c b = -determinant a b c by unfold determinant; ring, abs_neg]
  · rw [show determinant b a c = -determinant a b c by unfold determinant; ring, abs_neg]
  · exact congrArg abs (by unfold determinant; ring)
  · exact congrArg abs (by unfold determinant; ring)
  · rw [show determinant c b a = -determinant a b c by unfold determinant; ring, abs_neg]

private theorem set_eq_triangle {m : ℕ} {e : Finset (Grid m)} (he : e.card = 3)
    {a b c : Grid m} (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : e = {a,b,c} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp [he, hab, hac, hbc, card_insert_of_notMem]

private noncomputable def point {m : ℕ} (q : Grid m) : ℝ² :=
  WithLp.toLp 2 ![(q.1.val : ℝ)/(2*m), (q.2.val : ℝ)/(2*m)]

private theorem point_injective {m : ℕ} (hm : 0 < m) : Function.Injective (point (m:=m)) := by
  intro a b h
  have hm' : (0 : ℝ) < 2*m := by exact_mod_cast (show 0 < 2*m by omega)
  apply Prod.ext <;> apply Fin.ext
  · have h₀ := congrArg (fun x : ℝ² => x 0) h
    change (a.1.val : ℝ)/(2*m) = (b.1.val : ℝ)/(2*m) at h₀
    exact_mod_cast (div_left_inj' hm'.ne').mp h₀
  · have h₁ := congrArg (fun x : ℝ² => x 1) h
    change (a.2.val : ℝ)/(2*m) = (b.2.val : ℝ)/(2*m) at h₁
    exact_mod_cast (div_left_inj' hm'.ne').mp h₁

private theorem point_in_disk {m : ℕ} (hm : 0 < m) (q : Grid m) :
    point q ∈ Metric.closedBall (0 : ℝ²) 1 := by
  have hm' : (0 : ℝ) < 2*m := by exact_mod_cast (show 0 < 2*m by omega)
  have hx : (q.1.val : ℝ)/(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ hm').mpr
    have := (show (q.1.val : ℝ) ≤ m by exact_mod_cast q.1.isLt.le)
    linarith
  have hy : (q.2.val : ℝ)/(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ hm').mpr
    have := (show (q.2.val : ℝ) ≤ m by exact_mod_cast q.2.isLt.le)
    linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change ((q.1.val : ℝ)/(2*m))^2 + ((q.2.val : ℝ)/(2*m))^2 ≤ 1^2
  have hx2 := pow_le_pow_left₀ (by positivity) hx 2
  have hy2 := pow_le_pow_left₀ (by positivity) hy 2
  norm_num at hx2 hy2 ⊢
  linarith

private theorem point_area {m : ℕ} (hm : 0 < m) (a b c : Grid m) :
    |EuclideanGeometry.triangle_area (point a) (point b) (point c)| =
      |determinant a b c| / (8 * (m : ℝ)^2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : EuclideanGeometry.triangle_area (point a) (point b) (point c) =
      determinant a b c / (8 * (m : ℝ)^2) := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
    simp [point, determinant]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * m^2)]

theorem grid_to_disk {m : ℕ} (hm : 0 < m) (r : ℝ) (U : Finset (Grid m)) :
    let t := 8 * (m : ℝ)^2 * r
    let T := (triangleLabels t).filter (fun q => tripleVerts q ⊆ U)
    let X := (conflictLabels t).filter (fun q => conflictVerts q ⊆ U)
    ∃ (S : Finset ℝ²) (E : Finset (Finset ℝ²)),
      S.card = U.card ∧ E.card ≤ T.card ∧
      (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ X.card ∧
      (S : Set ℝ²) ⊆ Metric.closedBall 0 1 ∧
      (∀ e ∈ E, e ⊆ S ∧ e.card = 3) ∧
      (∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
        |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ r →
        univ.image p ∈ E) := by
  classical
  dsimp only
  let t := 8 * (m : ℝ)^2 * r
  let T := (triangleLabels t).filter (fun q => tripleVerts q ⊆ U)
  let X := (conflictLabels t).filter (fun q => conflictVerts q ⊆ U)
  let p : Grid m ↪ ℝ² := ⟨point, point_injective hm⟩
  let F := T.image tripleVerts
  let f : Finset (Grid m) ↪ Finset ℝ² := ⟨Finset.map p, Finset.map_injective p⟩
  let S := U.map p
  let E := F.map f
  have hF (e : Finset (Grid m)) (he : e ∈ F) : e ⊆ U ∧ e.card = 3 := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp he
    exact ⟨(mem_filter.mp hq).2,triple_card (mem_filter.mp hq).1⟩
  have hTri (e : Finset (Grid m)) (he : e ∈ F) {a b c : Grid m}
      (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      |determinant a b c| ≤ t := by
    have hEq := set_eq_triangle (hF e he).2 ha hb hc hab hac hbc
    obtain ⟨q,hq,hEq'⟩ := mem_image.mp he
    rw [← determinant_same_vertices q.1 q.2.1 q.2.2 a b c (hEq'.trans hEq) hab hac hbc]
    exact (mem_filter.mp (mem_filter.mp hq).1).2.2.2.2
  refine ⟨S,E,card_map _,(card_map _).le.trans card_image_le,?_,?_,?_,?_⟩
  · let Y := (E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card
    change Y.card ≤ X.card
    let form (q : Quadruple m) : Finset ℝ² × Finset ℝ² :=
      (f (tripleVerts (q.1,q.2.1,q.2.2.1)), f (tripleVerts (q.1,q.2.1,q.2.2.2)))
    apply card_le_card_of_surjOn form
    rintro ⟨e₀,g₀⟩ hY
    have hpair := mem_filter.mp hY
    obtain ⟨he₀,hg₀⟩ := mem_product.mp hpair.1
    obtain ⟨e,he,rfl⟩ := mem_map.mp he₀
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hg₀
    have hne : e ≠ g := fun h => hpair.2.1 (congrArg f h)
    have hcard : 2 ≤ (e ∩ g).card := by
      have h := hpair.2.2
      change 2 ≤ (e.map p ∩ g.map p).card at h
      rw [← map_inter e g, card_map] at h
      exact h
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < (e ∩ g).card)
    have hae := (mem_inter.mp ha).1
    have hag := (mem_inter.mp ha).2
    have hbe := (mem_inter.mp hb).1
    have hbg := (mem_inter.mp hb).2
    have heCard := (hF e he).2
    have hgCard := (hF g hg).2
    have hesub : ¬ e ⊆ g := fun h => hne (eq_of_subset_of_card_le h (by omega))
    have hgsub : ¬ g ⊆ e := fun h => hne (eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨c,hce,hcg⟩ := not_subset.mp hesub
    obtain ⟨d,hdg,hde⟩ := not_subset.mp hgsub
    have hac : a ≠ c := fun h => hcg (h ▸ hag)
    have had : a ≠ d := fun h => hde (h ▸ hae)
    have hbc : b ≠ c := fun h => hcg (h ▸ hbg)
    have hbd : b ≠ d := fun h => hde (h ▸ hbe)
    have hcd : c ≠ d := fun h => hcg (h.symm ▸ hdg)
    have hq1 := hTri e he hae hbe hce hab hac hbc
    have hq2 := hTri g hg hag hbg hdg hab had hbd
    let q : Quadruple m := (a,b,c,d)
    have hX : q ∈ X := by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hab,hac,had,hbc,hbd,hcd,hq1,hq2⟩,?_⟩
      intro x hx
      simp only [conflictVerts, q, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hF e he).1 hae
      · exact (hF e he).1 hbe
      · exact (hF e he).1 hce
      · exact (hF g hg).1 hdg
    refine ⟨q,hX,?_⟩
    change (f ({a,b,c} : Finset (Grid m)), f ({a,b,d} : Finset (Grid m))) = (f e, f g)
    rw [← set_eq_triangle heCard hae hbe hce hab hac hbc, ← set_eq_triangle hgCard hag hbg hdg hab had hbd]
  · intro x hx
    obtain ⟨q,_,rfl⟩ := mem_map.mp hx
    exact point_in_disk hm q
  · intro e he
    obtain ⟨g,hg,rfl⟩ := mem_map.mp he
    exact ⟨map_subset_map.mpr (hF g hg).1, (card_map _).trans (hF g hg).2⟩
  · intro w hw hmem hArea
    have hpre (i : Fin 3) : ∃ q ∈ U, p q = w i := mem_map.mp (hmem i)
    choose q hqU hqEq using hpre
    have hqInj : Function.Injective q := fun i j h => hw (by rw [← hqEq i, ← hqEq j,h])
    have h01 : q 0 ≠ q 1 := hqInj.ne (by decide)
    have h02 : q 0 ≠ q 2 := hqInj.ne (by decide)
    have h12 : q 1 ≠ q 2 := hqInj.ne (by decide)
    let z : Triple m := (q 0,q 1,q 2)
    have hmt : 0 < (8 : ℝ) * m^2 := by
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    rw [← hqEq 0, ← hqEq 1, ← hqEq 2] at hArea
    change |EuclideanGeometry.triangle_area (point (q 0)) (point (q 1)) (point (q 2))| ≤ r at hArea
    rw [point_area hm] at hArea
    have hzt : |determinant (q 0) (q 1) (q 2)| ≤ t := by
      simpa only [t, mul_comm r] using (div_le_iff₀ hmt).mp hArea
    have hZ : z ∈ T := by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h01,h02,h12,hzt⟩,?_⟩
      intro x hx
      simp only [tripleVerts, z, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> apply hqU
    refine mem_map.mpr ⟨tripleVerts z,mem_image.mpr ⟨z,hZ,rfl⟩,?_⟩
    change (tripleVerts z).map p = univ.image w
    ext x
    simp [tripleVerts, z, hqEq, Fin.exists_fin_succ, eq_comm]


end OMA.HeilbronnGrid


/- Bernoulli sampling of vertex sets with bounded induced configurations. -/

open Finset
open scoped BigOperators

namespace OMA.SampleFinset4

private theorem weight_supersets {V : Type*} [DecidableEq V] {Q T : Finset V}
    (hT : T ⊆ Q) (p : ℝ) :
    (∑ S ∈ Q.powerset, if T ⊆ S then p ^ S.card * (1 - p) ^ (Q \ S).card else 0)
      = p ^ T.card := by
  let g := fun v => if v ∈ T then (0 : ℝ) else 1 - p
  have hprod := Finset.prod_add (fun _ : V => p) g Q
  have hleft : (∏ v ∈ Q, (p + g v)) = p ^ T.card := by
    rw [← prod_sdiff hT]
    have hs : (∏ v ∈ Q \ T, (p + g v)) = 1 := by
      apply prod_eq_one
      intro v hv
      simp [g, (mem_sdiff.1 hv).2]
    have ht : (∏ v ∈ T, (p + g v)) = p ^ T.card := by
      rw [← prod_const]
      exact prod_congr rfl fun v hv => by simp [g, hv]
    rw [hs, ht, one_mul]
  rw [hleft] at hprod
  rw [hprod]
  apply sum_congr rfl
  intro S hS
  by_cases hsub : T ⊆ S
  · rw [if_pos hsub, prod_const]
    congr 1
    rw [← prod_const]
    apply prod_congr rfl
    intro v hv
    have hnv : v ∉ T := fun hm => (mem_sdiff.1 hv).2 (hsub hm)
    simp [g, hnv]
  · rw [if_neg hsub]
    obtain ⟨v, hvT, hvS⟩ := not_subset.1 hsub
    have hv : v ∈ Q \ S := mem_sdiff.2 ⟨hT hvT, hvS⟩
    have hz : g v = 0 := if_pos hvT
    rw [Finset.prod_eq_zero hv hz, mul_zero]

private theorem expectation {V I : Type*} [DecidableEq V] (Q : Finset V) (A : Finset I)
    (t : I → Finset V) (d : ℕ)
    (h : ∀ i ∈ A, t i ⊆ Q ∧ (t i).card = d) (p : ℝ) :
    (∑ S ∈ Q.powerset, (p ^ S.card * (1 - p) ^ (Q \ S).card) *
      ((A.filter fun i => t i ⊆ S).card : ℝ)) = (A.card : ℝ) * p ^ d := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ _i ∈ A, p ^ d := by
      apply sum_congr rfl
      intro i hi
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [weight_supersets (h i hi).1, (h i hi).2]
    _ = _ := by rw [sum_const, nsmul_eq_mul]


/-- Choose a Bernoulli subset that is large and has few induced triples and
four-vertex conflicts. The labels of the triples and conflicts may repeat a vertex set. -/
theorem exists_sparse_sample {V E X : Type*} [DecidableEq V]
    (Q : Finset V) (edges : Finset E) (conflicts : Finset X)
    (edgeVerts : E → Finset V) (conflictVerts : X → Finset V)
    (hE : ∀ e ∈ edges, edgeVerts e ⊆ Q ∧ (edgeVerts e).card = 3)
    (hX : ∀ x ∈ conflicts, conflictVerts x ⊆ Q ∧ (conflictVerts x).card = 4)
    (p d : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hd : 0 < d)
    (avgE : 24 * (edges.card : ℝ) * p^3 ≤ d * ((Q.card : ℝ) * p))
    (avgX : 8 * (conflicts.card : ℝ) * p^4 ≤ (Q.card : ℝ) * p) :
    ∃ S ⊆ Q, (Q.card : ℝ) * p / 2 ≤ (S.card : ℝ) ∧
      6 * ((edges.filter fun e => edgeVerts e ⊆ S).card : ℝ) ≤ d * S.card ∧
      2 * (conflicts.filter fun x => conflictVerts x ⊆ S).card ≤ S.card := by
  let w (S : Finset V) : ℝ := p ^ S.card * (1-p) ^ (Q \ S).card
  let e (S : Finset V) : ℝ := (edges.filter fun v => edgeVerts v ⊆ S).card
  let x (S : Finset V) : ℝ := (conflicts.filter fun v => conflictVerts v ⊆ S).card
  let score (S : Finset V) : ℝ := S.card - (6/d)*e S - 2*x S
  have hw (S : Finset V) : 0 ≤ w S :=
    mul_nonneg (pow_nonneg hp₀ _) (pow_nonneg (sub_nonneg.mpr hp₁) _)
  have hMass : ∑ S ∈ Q.powerset, w S = 1 := by
    simpa only [empty_subset, if_true, card_empty, pow_zero] using
      weight_supersets (Q := Q) (T := ∅) (empty_subset Q) p
  have hEdge : (∑ S ∈ Q.powerset, w S * e S) = (edges.card : ℝ)*p^3 :=
    expectation Q edges edgeVerts 3 hE p
  have hConflict : (∑ S ∈ Q.powerset, w S * x S) = (conflicts.card : ℝ)*p^4 :=
    expectation Q conflicts conflictVerts 4 hX p
  have hVertices : (∑ S ∈ Q.powerset, w S * (S.card : ℝ)) = (Q.card : ℝ)*p := by
    have h := expectation Q Q (fun a : V => {a}) 1 (fun a ha => by simpa using ha) p
    rw [pow_one] at h
    rw [← h]
    apply sum_congr rfl
    intro S hS
    have hf : (Q.filter fun a => ({a} : Finset V) ⊆ S) = S := by
      ext a
      simp only [mem_filter, singleton_subset_iff]
      exact ⟨And.right, fun ha => ⟨mem_powerset.mp hS ha, ha⟩⟩
    rw [hf]
  have hScore : (∑ S ∈ Q.powerset, w S * score S) =
      (Q.card : ℝ) * p - (6/d)*((edges.card : ℝ)*p^3) - 2*((conflicts.card : ℝ)*p^4) := by
    rw [← hVertices, ← hEdge, ← hConflict, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    dsimp only [score]
    ring
  have hpE : (6/d)*((edges.card : ℝ)*p^3) ≤ (Q.card : ℝ)*p/4 := by
    calc
      _ = (24*(edges.card : ℝ)*p^3) / (4*d) := by field_simp; ring
      _ ≤ (d*((Q.card : ℝ)*p))/(4*d) := div_le_div_of_nonneg_right avgE (by positivity)
      _ = _ := by field_simp
  have hExpected : (Q.card : ℝ)*p/2 ≤ ∑ S ∈ Q.powerset, w S * score S := by
    rw [hScore]
    linarith
  obtain ⟨S,hS,hBest⟩ := exists_max_image Q.powerset score
    ⟨∅, mem_powerset.mpr (empty_subset Q)⟩
  have hMax : (∑ T ∈ Q.powerset, w T * score T) ≤ score S := by
    calc
      _ ≤ ∑ T ∈ Q.powerset, w T * score S :=
        sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hBest T hT) (hw T))
      _ = _ := by rw [← sum_mul, hMass, one_mul]
  have hChoice := hExpected.trans hMax
  have hNonneg : 0 ≤ (Q.card : ℝ)*p/2 := by positivity
  have hEdge₀ : 0 ≤ (6/d)*e S := by dsimp [e]; positivity
  have hConflict₀ : 0 ≤ 2*x S := by dsimp [x]; positivity
  change (Q.card : ℝ)*p/2 ≤ S.card - (6/d)*e S - 2*x S at hChoice
  refine ⟨S,mem_powerset.mp hS,by linarith,?_ ,?_⟩
  · change 6*e S ≤ d*S.card
    rw [mul_comm d]
    apply (div_le_iff₀ hd).mp
    rw [mul_div_right_comm]
    linarith
  · have hc : 2*x S ≤ S.card := by linarith
    dsimp only [x] at hc
    exact_mod_cast hc

end OMA.SampleFinset4


namespace OMA.HeilbronnParameters

open Filter Asymptotics

/-- Parameters for the Bernoulli sample. Its expected size is x^(9/8),
and the area threshold is r per triangle. -/
theorem eventual_parameters (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      let N := x ^ (9/8 : ℝ)
      let r := ε * (Real.log x / x^2)
      let d := 5000*r*N^2
      1 < x ∧ 1 ≤ Real.log x ∧ 1/x^4 ≤ r ∧
        0 < N ∧ N ≤ x^8 ∧
        2 ≤ d ∧ Real.log x / 4 ≤ Real.log d ∧ 320000*r^2*Real.log x*N^3 ≤ 1 := by
  let K := (320000 : ℝ) * ε^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (s:=5/8) (3:ℝ)
    (by norm_num)).bound (inv_pos.mpr hK)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 ε⁻¹), hlog] with x hx hlogB hlogRate
  dsimp only
  let N := x ^ (9/8 : ℝ)
  let r := ε * (Real.log x / x^2)
  let d := 5000*r*N^2
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl1 : 1 ≤ Real.log x := (le_max_left _ _).trans hlogB
  have hl0 : 0 < Real.log x := by linarith
  have hεlog : 1 ≤ ε * Real.log x := by
    have h := mul_le_mul_of_nonneg_left ((le_max_right 1 ε⁻¹).trans hlogB) hε.le
    rwa [mul_inv_cancel₀ hε.ne'] at h
  have hN0 : 0 < N := Real.rpow_pos_of_pos hx0 _
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hN2 : N^2 = x ^ (9/4 : ℝ) := by
    dsimp only [N]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hN3 : N^3 = x ^ (27/8 : ℝ) := by
    dsimp only [N]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hApow : (x ^ (5/8 : ℝ)) * x ^ (27/8 : ℝ) = x^4 := by
    rw [← Real.rpow_add hx0]
    norm_num [Real.rpow_natCast]
  have hDpower : x ^ (9/4 : ℝ) = x^2 * x ^ (1/4 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hx0]
    norm_num
  have hD : d = 5000*ε*Real.log x * x ^ (1/4 : ℝ) := by
    dsimp only [d,r]
    rw [hN2,hDpower]
    field_simp
  have hp1 : 1 ≤ x ^ (1/4 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
  have hDlower : 2 ≤ d := by
    rw [hD]
    have h := mul_le_mul hεlog hp1 (by positivity) (by positivity : 0 ≤ ε * Real.log x)
    nlinarith only [h]
  have hloglower : Real.log x / 4 ≤ Real.log d := by
    have hbase : x ^ (1/4 : ℝ) ≤ d := by
      rw [hD]
      have h := mul_le_mul_of_nonneg_right hεlog
        (Real.rpow_nonneg hx0.le (1/4 : ℝ))
      nlinarith only [h,hp1]
    have hmono := Real.log_le_log (Real.rpow_pos_of_pos hx0 (1/4:ℝ)) hbase
    rw [Real.log_rpow hx0] at hmono
    linarith
  have hround : 1 / x^4 ≤ r := by
    have h : 1 / x^2 ≤ r := by
      dsimp only [r]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hεlog (by positivity)
    apply (one_div_le_one_div_of_le (by positivity) _).trans h
    have hs := one_le_pow₀ (a:=x) hx.le (n:=2)
    nlinarith [sq_nonneg (x^2-1)]
  have hNle : N ≤ x^8 := by
    dsimp only [N]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hlogBound : (Real.log x)^3 ≤ K⁻¹ * x ^ (5/8 : ℝ) := by
    have hh := hlogRate
    change ‖(Real.log x)^(3:ℝ)‖ ≤ K⁻¹ * ‖x ^ (5/8:ℝ)‖ at hh
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hh
    exact (Real.rpow_natCast (Real.log x) 3 ▸ hh)
  have hlogPower : (Real.log x)^3 * x^(27/8 : ℝ) ≤ K⁻¹ * x^4 := by
    calc
      _ ≤ (K⁻¹ * x ^ (5/8 : ℝ)) * x^(27/8 : ℝ) :=
        mul_le_mul_of_nonneg_right hlogBound (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc,hApow]
  have hlogPower' : K * ((Real.log x)^3 * x^(27/8 : ℝ)) ≤ x^4 := by
    calc _ ≤ K * (K⁻¹ * x^4) := mul_le_mul_of_nonneg_left hlogPower hK.le
      _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
  have hConf : 320000*r^2*Real.log x*N^3 ≤ 1 := by
    rw [hN3]
    calc
      _ = (K * ((Real.log x)^3 * x^(27/8 : ℝ))) / x^4 := by
        dsimp only [r,K]
        field_simp
      _ ≤ _ := (div_le_one (by positivity)).mpr hlogPower'
  exact ⟨hx,hl1,hround,hN0,hNle,hDlower,hloglower,hConf⟩

end OMA.HeilbronnParameters


namespace OMA.HeilbronnSampleApplication

open OMA.HeilbronnGrid OMA.HeilbronnParameters
open Finset Filter Erdos507
open scoped BigOperators EuclideanGeometry

private theorem normalized_triangle_bound {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r)
    (hRound : 1/(m : ℝ) ≤ r) :
    ((triangleLabels (m:=m) (8*(m : ℝ)^2*r)).card : ℝ) ≤ (m : ℝ)^6*(193*r) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ ≤ (m : ℝ)^5 + 24*(8*(m : ℝ)^2*r)*(m : ℝ)^4 :=
      triangles_total _ (by positivity)
    _ = (m : ℝ)^6*(1/(m : ℝ)+192*r) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem normalized_conflict_bound {m : ℕ} (hm : 0 < m) (r L : ℝ) (hr : 0 ≤ r)
    (hRound : 1/(m : ℝ) ≤ r) (hL : 1 ≤ L) (hLog : Real.log (m : ℝ) = 4*L) :
    ((conflictLabels (m:=m) (8*(m : ℝ)^2*r)).card : ℝ) ≤ (m : ℝ)^8*(40000*r^2*L) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1/(m : ℝ)) hRound 2
  calc
    _ ≤ 2*(m : ℝ)^6 + 96*(8*(m : ℝ)^2*r)^2*(m : ℝ)^4*(1+Real.log m) :=
      conflicts_total _ (by positivity)
    _ = (m : ℝ)^8*(2*(1/(m : ℝ))^2 + 6144*r^2*(1+4*L)) := by
      rw [hLog]
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 2 by norm_num)
      have h2 := mul_le_mul_of_nonneg_right (show 2 + 6144 * (1+4*L) ≤ 40000*L by linarith)
        (sq_nonneg r)
      nlinarith only [h1,h2]

theorem successful_sampling : OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1.H1 := by
  classical
  refine ⟨80000, by norm_num, ?_⟩
  intro ε hε
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventual_parameters ε hε)] with n hParams
  let m := n^4
  let N := (n : ℝ) ^ (9/8 : ℝ)
  let r := ε * lowerBest n
  let d := 5000*r*N^2
  have hP : (1 : ℝ) < n ∧ 1 ≤ Real.log n ∧ 1/(n : ℝ)^4 ≤ r ∧
      0 < N ∧ N ≤ (n : ℝ)^8 ∧
      2 ≤ d ∧ Real.log n/4 ≤ Real.log d ∧ 320000*r^2*Real.log n*N^3 ≤ 1 := hParams
  rcases hP with ⟨hn,hL,hRound,hN,hNle,hd,hLogD,hTiny⟩
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn
  have hm : 0 < m := by
    have hn' : 0 < n := by exact_mod_cast hn0
    exact pow_pos hn' _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : 0 < r := by dsimp [r,lowerBest]; positivity
  have hd0 : 0 < d := by linarith
  have hL0 : 0 < Real.log (n : ℝ) := by linarith
  have hRound' : 1/(m : ℝ) ≤ r := by simpa only [m,Nat.cast_pow] using hRound
  have hLogM : Real.log (m : ℝ) = 4 * Real.log n := by
    rw [show (m : ℝ) = (n : ℝ)^4 by simp [m], Real.log_pow]
    norm_num
  let p := N/(m : ℝ)^2
  have hp0 : 0 < p := div_pos hN (by positivity)
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    simpa only [m,Nat.cast_pow,← pow_mul, show 4*2=8 by decide] using hNle
  let Q : Finset (Grid m) := univ
  let t := 8*(m : ℝ)^2*r
  let T := triangleLabels (m:=m) t
  let X := conflictLabels (m:=m) t
  have hT : (T.card : ℝ) ≤ (m : ℝ)^6*(193*r) :=
    normalized_triangle_bound hm r hr.le hRound'
  have hX : (X.card : ℝ) ≤ (m : ℝ)^8*(40000*r^2*Real.log n) :=
    normalized_conflict_bound hm r _ hr.le hRound' hL hLogM
  have hMp : (m : ℝ)^2*p = N := by dsimp [p]; field_simp
  have hQ : (Q.card : ℝ)*p = N := by
    rw [show (Q.card : ℝ) = (m : ℝ)^2 by simp [Q,Grid,pow_two]]
    exact hMp
  have hCube : (m : ℝ)^6 * p^3 = N^3 := by
    rw [← hMp]
    ring
  have hFourth : (m : ℝ)^8 * p^4 = N^4 := by
    rw [← hMp]
    ring
  have hMeanT : 24*(T.card : ℝ)*p^3 ≤ d*((Q.card : ℝ)*p) := by
    calc
      _ ≤ 24*((m : ℝ)^6*(193*r))*p^3 := by gcongr
      _ = (24*193)*r*N^3 := by
        rw [show (24:ℝ)*((m : ℝ)^6*(193*r))*p^3 = (24*193)*r*((m : ℝ)^6*p^3) by ring, hCube]
      _ ≤ d*((Q.card : ℝ)*p) := by
        rw [hQ]
        dsimp only [d]
        nlinarith only [mul_nonneg hr.le (pow_nonneg hN.le 3)]
  have hMeanX : 8*(X.card : ℝ)*p^4 ≤ (Q.card : ℝ)*p := by
    calc
      _ ≤ 8*((m : ℝ)^8*(40000*r^2*Real.log n))*p^4 := by gcongr
      _ = (320000*r^2*Real.log n*N^3)*N := by
        rw [show (8:ℝ)*((m : ℝ)^8*(40000*r^2*Real.log n))*p^4 =
              (320000*r^2*Real.log n)*((m : ℝ)^8*p^4) by ring, hFourth]
        ring
      _ ≤ _ := by simpa only [hQ,one_mul] using mul_le_mul_of_nonneg_right hTiny hN.le
  have hTL (q : Triple m) (hq : q ∈ T) : tripleVerts q ⊆ Q ∧ (tripleVerts q).card = 3 :=
    ⟨subset_univ _,triple_card hq⟩
  have hXL (q : Quadruple m) (hq : q ∈ X) : conflictVerts q ⊆ Q ∧ (conflictVerts q).card = 4 :=
    ⟨subset_univ _,conflict_card hq⟩
  obtain ⟨U,-,hUSize,hUCount,hUConf⟩ :=
    OMA.SampleFinset4.exists_sparse_sample Q T X tripleVerts conflictVerts hTL hXL
      p d hp0.le hp1 hd0 hMeanT hMeanX
  rw [hQ] at hUSize
  obtain ⟨S,E,hSCard,hEBound,hXBound,hDisk,hEdges,hCover⟩ := grid_to_disk hm r U
  refine ⟨S,E,d,hDisk,hEdges,hCover,?_,hd,?_,?_⟩
  · change (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤
      (X.filter fun q => conflictVerts q ⊆ U).card at hXBound
    omega
  · have hEcast : (E.card : ℝ) ≤ ((T.filter fun q => tripleVerts q ⊆ U).card : ℝ) := by
      exact Nat.cast_le.mpr hEBound
    rw [← hSCard] at hUCount
    linarith
  · have hSSize : N ≤ 2*(S.card : ℝ) := by rw [hSCard]; linarith
    have hdiv := div_le_div_of_nonneg_right hSSize hn0.le
    calc
      d / Real.log d ≤ d / (Real.log n / 4) :=
        div_le_div_of_nonneg_left hd0.le (by positivity) hLogD
      _ = 20000*ε*(N/(n : ℝ))^2 := by
        dsimp only [d,r,lowerBest]
        field_simp
        ring
      _ ≤ 20000*ε*((2*(S.card : ℝ))/(n : ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdiv 2) (by positivity)
      _ = _ := by ring

end OMA.HeilbronnSampleApplication

end H1Part

section H2Part

/- A finite version of the weighted argument of Verstraete and Wilson
(Independent sets in hypergraphs, arXiv:2409.19908), specialized to triples.
The first sampling step deletes short Berge cycles. The second part uses the
probability measure on independent sets with weight exponential in the number
of pairs they span in the two-shadow. -/


/- Finite estimates for the weighted-independent-set proof of the
logarithmic independence bound for linear triple systems. -/

namespace OMA.HypergraphWeights

open Finset
open scoped BigOperators

/-- A finite Gibbs distribution with a zero-energy element has mean energy
at most the logarithm of the number of available states. -/
theorem energy_bound {I : Type*} (F : Finset I) (z : I → ℝ)
    (hz : ∃ i ∈ F, z i = 0) :
    (∑ i ∈ F, Real.exp (-z i) * z i) ≤
      (∑ i ∈ F, Real.exp (-z i)) * Real.log F.card := by
  let w i := Real.exp (-z i)
  let Z := ∑ i ∈ F, w i
  obtain ⟨j,hj,hj0⟩ := hz
  have hcount : (0 : ℝ) < F.card := by
    exact_mod_cast card_pos.mpr (show F.Nonempty from ⟨j,hj⟩)
  have hw (i : I) : 0 < w i := Real.exp_pos _
  have hZ : 1 ≤ Z := by
    have h1 : w j ≤ Z := single_le_sum (fun i _ => (hw i).le) hj
    simpa [w,hj0] using h1
  have hZ0 : 0 < Z := by linarith
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hpoint (i : I) :
      w i * (Real.log Z + z i - Real.log F.card) ≤ Z / F.card - w i := by
    have hpos : 0 < Z / (w i * (F.card : ℝ)) :=
      div_pos hZ0 (mul_pos (hw i) hcount)
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) (hw i).le
    have he : Real.log (Z / (w i * (F.card : ℝ))) =
        Real.log Z + z i - Real.log F.card := by
      rw [Real.log_div hZ0.ne' (mul_ne_zero (hw i).ne' hcount.ne'),
        Real.log_mul (hw i).ne' hcount.ne']
      dsimp only [w]
      rw [Real.log_exp]
      ring
    have hmul : w i * (Z / (w i * (F.card : ℝ)) - 1) = Z / F.card - w i := by
      field_simp [(hw i).ne',hcount.ne']
    rwa [he,hmul] at h
  have hsum := sum_le_sum (fun i (_ : i ∈ F) => hpoint i)
  have hright : (∑ i ∈ F, (Z / (F.card : ℝ) - w i)) = 0 := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    change (F.card : ℝ)*(Z/F.card)-Z=0
    field_simp [hcount.ne'] <;> ring
  have hleft : (∑ i ∈ F, w i * (Real.log Z + z i - Real.log F.card)) =
      Z * Real.log Z + (∑ i ∈ F,w i*z i) - Z*Real.log F.card := by
    rw [show Z * Real.log Z + (∑ i ∈ F,w i*z i) - Z*Real.log F.card =
      (∑ i ∈ F,w i)*Real.log Z + (∑ i ∈ F,w i*z i) - (∑ i ∈ F,w i)*Real.log F.card by rfl]
    rw [sum_mul,sum_mul,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hleft,hright] at hsum
  change (∑ i ∈ F,w i*z i) ≤ Z*Real.log F.card
  linarith only [hsum, mul_nonneg hZ0.le hlogZ]

private theorem sum_power_powerset {V : Type*} [DecidableEq V] (S : Finset V) (a : ℝ) :
    ∑ I ∈ S.powerset, a ^ I.card = (1+a)^S.card := by
  have h := Finset.prod_add (fun _ : V => a) (fun _ => 1) S
  simpa only [prod_const, one_pow, mul_one, add_comm a 1] using h.symm

/-- The logarithm of the number of subsets of size at most m is bounded
by m times one plus the logarithm of the size ratio. -/
theorem log_count_subsets {V : Type*} [DecidableEq V] (S : Finset V) (F : Finset (Finset V))
    (hm : 0 < m) (hN : m ≤ S.card) (hF : F.Nonempty)
    (hsub : F ⊆ S.powerset) (hcard : ∀ I ∈ F, I.card ≤ m) :
    Real.log F.card ≤ m * (1 + Real.log ((S.card : ℝ)/m)) := by
  let a := (m : ℝ)/(S.card : ℝ)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < S.card := by
    exact_mod_cast (hm.trans_le hN)
  have ha0 : 0 < a := div_pos hm0 hN0
  have ha1 : a ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hN)
  have hF0 : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hF
  have hsum : (F.card : ℝ)*a^m ≤ (1+a)^S.card := by
    calc _ = ∑ _I ∈ F, a^m := by rw [sum_const,nsmul_eq_mul]
      _ ≤ ∑ I ∈ F, a^I.card :=
        sum_le_sum (fun I hI => pow_le_pow_of_le_one ha0.le ha1 (hcard I hI))
      _ ≤ ∑ I ∈ S.powerset, a^I.card :=
        sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => pow_nonneg ha0.le _)
      _ = _ := sum_power_powerset S a
  have hz := Real.log_le_log (mul_pos hF0 (pow_pos ha0 _)) hsum
  rw [Real.log_mul hF0.ne' (pow_ne_zero _ ha0.ne'), Real.log_pow, Real.log_pow] at hz
  have ht : Real.log (1+a) ≤ a := by
    have ht' := Real.log_le_sub_one_of_pos (show 0 < 1+a by linarith)
    linarith
  have hmul : (S.card : ℝ)*a = m := by dsimp [a]; field_simp
  have hlogA : Real.log a = - Real.log ((S.card : ℝ)/m) := by
    dsimp [a]
    rw [Real.log_div hm0.ne' hN0.ne',Real.log_div hN0.ne' hm0.ne']
    ring
  have hlogUpper := mul_le_mul_of_nonneg_left ht hN0.le
  rw [hmul] at hlogUpper
  rw [hlogA] at hz
  linarith

/-- Adding the central vertex to a matching link removes the two-point
state and discounts each singleton by the factor beta. -/
theorem log_link_bound (δ u v : ℝ) (hδ : 0 ≤ δ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    let β := Real.exp (-δ)
    let W := 1 + u + v + β*u*v
    let Wplus := 1 + β*(u+v)
    Real.log (W/Wplus) ≤ 4 * ((δ*(u+v) + β*u*v)/W) := by
  dsimp only
  let β := Real.exp (-δ)
  let W := 1 + u + v + β*u*v
  let P := 1 + β*(u+v)
  have hβ : 0 < β := Real.exp_pos _
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hβδ : 1-β ≤ δ := by
    have h := Real.add_one_le_exp (-δ)
    change -δ+1 ≤ β at h
    linarith
  have hP : 1 ≤ P := by dsimp [P]; linarith [mul_nonneg hβ.le (add_nonneg hu hv)]
  have hP0 : 0 < P := by linarith
  have hW0 : 0 < W := by dsimp [W]; positivity
  have hbetauv : β*u*v ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul hβ1 hu1 hu (by norm_num)) hv).trans
      (by simpa using hv1)
  have hW : W ≤ 4 := by dsimp [W]; linarith
  have hWP : W ≤ 4*P := by linarith
  have hdif : W-P ≤ δ*(u+v)+β*u*v := by
    dsimp [W,P]
    nlinarith only [mul_le_mul_of_nonneg_right hβδ (add_nonneg hu hv)]
  have hnum : 0 ≤ δ*(u+v)+β*u*v := by positivity
  change Real.log (W/P) ≤ 4*((δ*(u+v)+β*u*v)/W)
  calc
    _ ≤ W/P-1 := Real.log_le_sub_one_of_pos (div_pos hW0 hP0)
    _ = (W-P)/P := by field_simp
    _ ≤ (δ*(u+v)+β*u*v)/P := div_le_div_of_nonneg_right hdif hP0.le
    _ ≤ 4*((δ*(u+v)+β*u*v)/W) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hP0 hW0).mpr
      calc (δ*(u+v)+β*u*v)*W ≤ (δ*(u+v)+β*u*v)*(4*P) :=
          mul_le_mul_of_nonneg_left hWP hnum
        _ = _ := by ring

/-- Either the center itself is frequently selected, or the odds against
it are large enough to contribute logarithmically. -/
theorem occupancy_bound (d p : ℝ) (hd : Real.exp 8 ≤ d)
    (hp : 0 < p) (hp1 : p ≤ 1/2) :
    Real.log d/64 ≤ p*Real.sqrt d + (1-p)/4 * Real.log ((1-p)/p) := by
  have hd0 := (Real.exp_pos (8:ℝ)).trans_le hd
  have hlog : 8 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos (8:ℝ)) hd
    rwa [Real.log_exp] at h
  have hq : 1/2 ≤ 1-p := by linarith
  have hq0 : 0 < 1-p := by linarith
  have hR : 1 ≤ (1-p)/p := (le_div_iff₀ hp).mpr (by linarith)
  have hSecond : 0 ≤ (1-p)/4 * Real.log ((1-p)/p) :=
    mul_nonneg (by positivity) (Real.log_nonneg hR)
  let a := d^(1/4:ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hd0 _
  have haLog : Real.log a = Real.log d / 4 := by
    dsimp [a]
    rw [Real.log_rpow hd0]
    ring
  by_cases hpa : a⁻¹ ≤ p
  · have hasq : a*a = Real.sqrt d := by
      dsimp [a]
      rw [← Real.rpow_add hd0]
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num
    have hMul := mul_le_mul_of_nonneg_right hpa (Real.sqrt_nonneg d)
    rw [← hasq, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at hMul
    have hLower : Real.log d/4 ≤ a := by
      have h := Real.log_le_sub_one_of_pos ha
      rw [haLog] at h
      linarith
    rw [hasq] at hMul
    linarith only [hMul,hLower,hlog,hSecond]
  · have hratio : a/2 ≤ (1-p)/p := by
      have hl := lt_of_not_ge hpa
      rw [← one_div] at hl
      have hl' := (lt_div_iff₀ ha).mp hl
      apply (le_div_iff₀ hp).mpr
      nlinarith only [hq,hl']
    have hlogratio := Real.log_le_log (by positivity : 0 < a/2) hratio
    rw [Real.log_div ha.ne' (by norm_num),haLog] at hlogratio
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
      linarith
    have hhalfLog : Real.log d/8 ≤ Real.log ((1-p)/p) := by linarith
    have hmul := mul_le_mul
      (show (1:ℝ)/8 ≤ (1-p)/4 by linarith) hhalfLog (by linarith) (by positivity)
    have hpTerm := mul_nonneg hp.le (Real.sqrt_nonneg d)
    linarith only [hmul,hpTerm]


theorem product_occupancy {L : Type*} [Fintype L]
    (d δ : ℝ) (hd : Real.exp 8 ≤ d) (hδ : 0 ≤ δ)
    (u v : L → ℝ) (hu : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    let β := Real.exp (-δ)
    let W i := 1 + u i + v i + β*u i*v i
    let P i := 1 + β*(u i+v i)
    Real.log d/64*((∏ i,W i)+(∏ i,P i)) ≤
      Real.sqrt d*(∏ i,P i) +
        (∏ i,W i)*(∑ i, (δ*(u i+v i)+β*u i*v i)/W i) := by
  dsimp only
  let β := Real.exp (-δ)
  let W i := 1 + u i + v i + β*u i*v i
  let P i := 1 + β*(u i+v i)
  let w := ∏ i, W i
  let c := ∏ i, P i
  let A := ∑ i, (δ*(u i+v i)+β*u i*v i)/W i
  have hb : 0 < β := Real.exp_pos _
  have hb1 : β ≤ 1 := by
    dsimp [β]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hW (i : L) : 0 < W i := by
    dsimp [W]
    positivity [hu i, hv i]
  have hP (i : L) : 0 < P i := by
    dsimp [P]
    positivity [hu i, hv i]
  have hP_le (i : L) : P i ≤ W i := by
    have h := mul_nonneg (sub_nonneg.mpr hb1) (add_nonneg (hu i) (hv i))
    have h' := mul_nonneg (mul_nonneg hb.le (hu i)) (hv i)
    dsimp [P,W]
    nlinarith only [h,h']
  have hw : 0 < w := prod_pos (fun i _ => hW i)
  have hc : 0 < c := prod_pos (fun i _ => hP i)
  have hc_le : c ≤ w := prod_le_prod (fun i _ => (hP i).le) (fun i _ => hP_le i)
  let p := c/(w+c)
  have hTot : 0 < w+c := add_pos hw hc
  have hp : 0 < p := div_pos hc hTot
  have hp1 : p ≤ 1/2 := (div_le_iff₀ hTot).mpr (by linarith)
  have hp' : 1-p = w/(w+c) := by dsimp [p]; field_simp; ring
  have hRatio : (1-p)/p = w/c := by rw [hp']; dsimp [p]; field_simp
  have hlog : Real.log (w/c) ≤ 4*A := by
    dsimp only [w,c,A]
    rw [Real.log_div (prod_ne_zero_iff.mpr (fun i _ => (hW i).ne'))
      (prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
      Real.log_prod (fun i _ => (hW i).ne'), Real.log_prod (fun i _ => (hP i).ne'),
      ← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro i hi
    rw [← Real.log_div (hW i).ne' (hP i).ne']
    exact log_link_bound δ (u i) (v i) hδ (hu i) (hu1 i) (hv i) (hv1 i)
  have hOcc := occupancy_bound d p hd hp hp1
  rw [hRatio] at hOcc
  have h := hOcc.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hlog (show 0 ≤ (1-p)/4 by linarith)))
  have h' := mul_le_mul_of_nonneg_right h hTot.le
  change Real.log d/64*(w+c) ≤ Real.sqrt d*c+w*A
  calc _ ≤ (p*Real.sqrt d + (1-p)/4*(4*A))*(w+c) := h'
    _ = _ := by rw [hp']; dsimp [p]; field_simp <;> ring

/-- The sum of an additive score under a product of finite weights. -/
theorem additive_product_sum {L A : Type*} [Fintype L] [Fintype A] [DecidableEq L]
    (w s : L → A → ℝ) (hw : ∀ i, (∑ a,w i a) ≠ 0) :
    (∑ x : L → A, (∏ i, w i (x i)) * ∑ i, s i (x i)) =
      (∏ i, ∑ a,w i a) * ∑ i, (∑ a,w i a*s i a)/(∑ a,w i a) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  let r (j : L) (a : A) := (if j = i then w j a*s j a else w j a)
  have hprod (x : L → A) :
      (∏ j,w j (x j)) * s i (x i) = ∏ j,r j (x j) := by
    have hs : (∏ j : L, if j = i then s j (x j) else (1:ℝ)) = s i (x i) := by
      simp
    rw [← hs, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j hj
    by_cases hji : j = i <;> simp [r,hji]
  simp_rw [hprod]
  rw [← Fintype.prod_sum]
  rw [← prod_mul_prod_compl ({i} : Finset L), ← prod_mul_prod_compl ({i} : Finset L)]
  simp only [prod_singleton,r,if_pos]
  have hrest : (∏ j ∈ ({i} : Finset L)ᶜ, ∑ a,r j a) =
      ∏ j ∈ ({i} : Finset L)ᶜ, ∑ a,w j a := by
    apply prod_congr rfl
    intro j hj
    have hj' : j ≠ i := by simpa using hj
    simp [r,hj']
  rw [hrest]
  field_simp [hw i]


end OMA.HypergraphWeights


/- Bernoulli sampling of vertex sets with bounded induced configurations. -/

open Finset
open scoped BigOperators

namespace OMA.SampleFinset

private theorem weight_supersets {V : Type*} [DecidableEq V] {Q T : Finset V}
    (hT : T ⊆ Q) (p : ℝ) :
    (∑ S ∈ Q.powerset, if T ⊆ S then p ^ S.card * (1 - p) ^ (Q \ S).card else 0)
      = p ^ T.card := by
  let g := fun v => if v ∈ T then (0 : ℝ) else 1 - p
  have hprod := Finset.prod_add (fun _ : V => p) g Q
  have hleft : (∏ v ∈ Q, (p + g v)) = p ^ T.card := by
    rw [← prod_sdiff hT]
    have hs : (∏ v ∈ Q \ T, (p + g v)) = 1 := by
      apply prod_eq_one
      intro v hv
      simp [g, (mem_sdiff.1 hv).2]
    have ht : (∏ v ∈ T, (p + g v)) = p ^ T.card := by
      rw [← prod_const]
      exact prod_congr rfl fun v hv => by simp [g, hv]
    rw [hs, ht, one_mul]
  rw [hleft] at hprod
  rw [hprod]
  apply sum_congr rfl
  intro S hS
  by_cases hsub : T ⊆ S
  · rw [if_pos hsub, prod_const]
    congr 1
    rw [← prod_const]
    apply prod_congr rfl
    intro v hv
    have hnv : v ∉ T := fun hm => (mem_sdiff.1 hv).2 (hsub hm)
    simp [g, hnv]
  · rw [if_neg hsub]
    obtain ⟨v, hvT, hvS⟩ := not_subset.1 hsub
    have hv : v ∈ Q \ S := mem_sdiff.2 ⟨hT hvT, hvS⟩
    have hz : g v = 0 := if_pos hvT
    rw [Finset.prod_eq_zero hv hz, mul_zero]

private theorem expectation {V I : Type*} [DecidableEq V] (Q : Finset V) (A : Finset I)
    (t : I → Finset V) (d : ℕ)
    (h : ∀ i ∈ A, t i ⊆ Q ∧ (t i).card = d) (p : ℝ) :
    (∑ S ∈ Q.powerset, (p ^ S.card * (1 - p) ^ (Q \ S).card) *
      ((A.filter fun i => t i ⊆ S).card : ℝ)) = (A.card : ℝ) * p ^ d := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ _i ∈ A, p ^ d := by
      apply sum_congr rfl
      intro i hi
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [weight_supersets (h i hi).1, (h i hi).2]
    _ = _ := by rw [sum_const, nsmul_eq_mul]


/-- Choose a Bernoulli subset that is large and has few induced triples and
conflicts of the specified size. The labels of the triples and conflicts may repeat a vertex set. -/
theorem exists_sparse_sample {V E X : Type*} [DecidableEq V]
    (Q : Finset V) (edges : Finset E) (conflicts : Finset X)
    (edgeVerts : E → Finset V) (conflictVerts : X → Finset V) (conflictSize : ℕ)
    (hE : ∀ e ∈ edges, edgeVerts e ⊆ Q ∧ (edgeVerts e).card = 3)
    (hX : ∀ x ∈ conflicts, conflictVerts x ⊆ Q ∧ (conflictVerts x).card = conflictSize)
    (p d : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hd : 0 < d)
    (avgE : 24 * (edges.card : ℝ) * p^3 ≤ d * ((Q.card : ℝ) * p))
    (avgX : 8 * (conflicts.card : ℝ) * p^conflictSize ≤ (Q.card : ℝ) * p) :
    ∃ S ⊆ Q, (Q.card : ℝ) * p / 2 ≤ (S.card : ℝ) ∧
      6 * ((edges.filter fun e => edgeVerts e ⊆ S).card : ℝ) ≤ d * S.card ∧
      2 * (conflicts.filter fun x => conflictVerts x ⊆ S).card ≤ S.card := by
  let w (S : Finset V) : ℝ := p ^ S.card * (1-p) ^ (Q \ S).card
  let e (S : Finset V) : ℝ := (edges.filter fun v => edgeVerts v ⊆ S).card
  let x (S : Finset V) : ℝ := (conflicts.filter fun v => conflictVerts v ⊆ S).card
  let score (S : Finset V) : ℝ := S.card - (6/d)*e S - 2*x S
  have hw (S : Finset V) : 0 ≤ w S :=
    mul_nonneg (pow_nonneg hp₀ _) (pow_nonneg (sub_nonneg.mpr hp₁) _)
  have hMass : ∑ S ∈ Q.powerset, w S = 1 := by
    simpa only [empty_subset, if_true, card_empty, pow_zero] using
      weight_supersets (Q := Q) (T := ∅) (empty_subset Q) p
  have hEdge : (∑ S ∈ Q.powerset, w S * e S) = (edges.card : ℝ)*p^3 :=
    expectation Q edges edgeVerts 3 hE p
  have hConflict : (∑ S ∈ Q.powerset, w S * x S) = (conflicts.card : ℝ)*p^conflictSize :=
    expectation Q conflicts conflictVerts conflictSize hX p
  have hVertices : (∑ S ∈ Q.powerset, w S * (S.card : ℝ)) = (Q.card : ℝ)*p := by
    have h := expectation Q Q (fun a : V => {a}) 1 (fun a ha => by simpa using ha) p
    rw [pow_one] at h
    rw [← h]
    apply sum_congr rfl
    intro S hS
    have hf : (Q.filter fun a => ({a} : Finset V) ⊆ S) = S := by
      ext a
      simp only [mem_filter, singleton_subset_iff]
      exact ⟨And.right, fun ha => ⟨mem_powerset.mp hS ha, ha⟩⟩
    rw [hf]
  have hScore : (∑ S ∈ Q.powerset, w S * score S) =
      (Q.card : ℝ) * p - (6/d)*((edges.card : ℝ)*p^3) - 2*((conflicts.card : ℝ)*p^conflictSize) := by
    rw [← hVertices, ← hEdge, ← hConflict, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    dsimp only [score]
    ring
  have hpE : (6/d)*((edges.card : ℝ)*p^3) ≤ (Q.card : ℝ)*p/4 := by
    calc
      _ = (24*(edges.card : ℝ)*p^3) / (4*d) := by field_simp; ring
      _ ≤ (d*((Q.card : ℝ)*p))/(4*d) := div_le_div_of_nonneg_right avgE (by positivity)
      _ = _ := by field_simp
  have hExpected : (Q.card : ℝ)*p/2 ≤ ∑ S ∈ Q.powerset, w S * score S := by
    rw [hScore]
    linarith
  obtain ⟨S,hS,hBest⟩ := exists_max_image Q.powerset score
    ⟨∅, mem_powerset.mpr (empty_subset Q)⟩
  have hMax : (∑ T ∈ Q.powerset, w T * score T) ≤ score S := by
    calc
      _ ≤ ∑ T ∈ Q.powerset, w T * score S :=
        sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hBest T hT) (hw T))
      _ = _ := by rw [← sum_mul, hMass, one_mul]
  have hChoice := hExpected.trans hMax
  have hNonneg : 0 ≤ (Q.card : ℝ)*p/2 := by positivity
  have hEdge₀ : 0 ≤ (6/d)*e S := by dsimp [e]; positivity
  have hConflict₀ : 0 ≤ 2*x S := by dsimp [x]; positivity
  change (Q.card : ℝ)*p/2 ≤ S.card - (6/d)*e S - 2*x S at hChoice
  refine ⟨S,mem_powerset.mp hS,by linarith,?_ ,?_⟩
  · change 6*e S ≤ d*S.card
    rw [mul_comm d]
    apply (div_le_iff₀ hd).mp
    rw [mul_div_right_comm]
    linarith
  · have hc : 2*x S ≤ S.card := by linarith
    dsimp only [x] at hc
    exact_mod_cast hc

end OMA.SampleFinset


/- Link structure in a Berge-triangle-free linear triple system. -/

namespace OMA.TripleSystem

open Finset
open scoped BigOperators

section Vertices

variable {V : Type*} [DecidableEq V]

def incidence (E : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  E.filter (v ∈ ·)

def neighbors (E : Finset (Finset V)) (v : V) : Finset V :=
  (incidence E v).biUnion (fun e => e.erase v)

def shadow (E : Finset (Finset V)) : Finset (Finset V) :=
  E.biUnion (fun e => e.powersetCard 2)

def independent (E : Finset (Finset V)) (U : Finset V) : Prop :=
  ∀ e ∈ E, ¬ e ⊆ U

instance (E : Finset (Finset V)) (U : Finset V) : Decidable (independent E U) :=
  inferInstanceAs (Decidable (∀ e ∈ E, ¬ e ⊆ U))

def independentSets (Q : Finset V) (E : Finset (Finset V)) : Finset (Finset V) :=
  Q.powerset.filter (independent E)

def uniformThree (Q : Finset V) (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e ⊆ Q ∧ e.card = 3

def linear (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e∩f).card ≤ 1

def triangleFree (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, ∀ g ∈ E, e ≠ f → f ≠ g → g ≠ e →
    ∀ x ∈ e ∩ f, ∀ y ∈ f ∩ g, ∀ z ∈ g ∩ e, x ≠ y → y ≠ z → z ≠ x → False

@[simp] theorem mem_incidence {E : Finset (Finset V)} {v : V} {e : Finset V} :
    e ∈ incidence E v ↔ e ∈ E ∧ v ∈ e := by simp [incidence]

@[simp] theorem mem_neighbors {E : Finset (Finset V)} {v x : V} :
    x ∈ neighbors E v ↔ x ≠ v ∧ ∃ e ∈ E, v ∈ e ∧ x ∈ e := by
  simp only [neighbors,mem_biUnion,mem_incidence,mem_erase]
  tauto

@[simp] theorem center_not_neighbor (E : Finset (Finset V)) (v : V) : v ∉ neighbors E v := by
  simp

theorem neighbor_symmetric {E : Finset (Finset V)} {v x : V} :
    x ∈ neighbors E v ↔ v ∈ neighbors E x := by
  simp only [mem_neighbors]
  constructor <;>
    rintro ⟨h,e,he,ha,hb⟩ <;> exact ⟨h.symm,e,he,hb,ha⟩

theorem neighbors_subset {Q : Finset V} {E : Finset (Finset V)} (hU : uniformThree Q E) (v : V) :
    neighbors E v ⊆ Q := by
  intro x hx
  obtain ⟨_,e,he,_,hxe⟩ := mem_neighbors.mp hx
  exact (hU e he).1 hxe

theorem link_card {Q : Finset V} {E : Finset (Finset V)} (hU : uniformThree Q E)
    {v : V} {e : Finset V} (he : e ∈ incidence E v) : (e.erase v).card = 2 := by
  obtain ⟨he',hv⟩ := mem_incidence.mp he
  rw [card_erase_of_mem hv,(hU e he').2]

theorem link_disjoint {E : Finset (Finset V)} (hL : linear E)
    {v : V} {e f : Finset V} (he : e ∈ incidence E v) (hf : f ∈ incidence E v)
    (hef : e ≠ f) : Disjoint (e.erase v) (f.erase v) := by
  obtain ⟨he',hve⟩ := mem_incidence.mp he
  obtain ⟨hf',hvf⟩ := mem_incidence.mp hf
  rw [Finset.disjoint_left]
  intro x hxe hxf
  have hord : 1 < (e ∩ f).card := one_lt_card.mpr
    ⟨x,mem_inter.mpr ⟨(mem_erase.mp hxe).2,(mem_erase.mp hxf).2⟩,
      v,mem_inter.mpr ⟨hve,hvf⟩,(mem_erase.mp hxe).1⟩
  exact hord.not_ge (hL e he' f hf' hef)

theorem edge_away_meets_neighbors_at_most_once {E : Finset (Finset V)}
    (hL : linear E) (hT : triangleFree E) {v : V} {e : Finset V} (he : e ∈ E) (hv : v ∉ e) :
    (e∩neighbors E v).card ≤ 1 := by
  by_contra! h
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp h
  have hxe := (mem_inter.mp hx).1
  have hye := (mem_inter.mp hy).1
  obtain ⟨hxv,f,hf,hvf,hxf⟩ := mem_neighbors.mp (mem_inter.mp hx).2
  obtain ⟨hyv,g,hg,hvg,hyg⟩ := mem_neighbors.mp (mem_inter.mp hy).2
  have hef : e ≠ f := fun h => hv (h ▸ hvf)
  have hge : g ≠ e := fun h => hv (h ▸ hvg)
  by_cases hfg : f = g
  · subst g
    have hxfy : 1 < (e ∩ f).card :=
      one_lt_card.mpr ⟨x,mem_inter.mpr ⟨hxe,hxf⟩,y,mem_inter.mpr ⟨hye,hyg⟩,hxy⟩
    exact hxfy.not_ge (hL e he f hf hef)
  · exact hT e he f hf g hg hef hfg hge
      x (mem_inter.mpr ⟨hxe,hxf⟩) v (mem_inter.mpr ⟨hvf,hvg⟩)
      y (mem_inter.mpr ⟨hyg,hye⟩) hxv hyv.symm hxy.symm

theorem degree_sum {Q : Finset V} {E : Finset (Finset V)} (hU : uniformThree Q E) :
    ∑ v ∈ Q,(incidence E v).card = 3*E.card := by
  simp only [incidence,card_filter]
  rw [sum_comm]
  calc
    _ = ∑ _e ∈ E,(3:ℕ) := by
      apply sum_congr rfl
      intro e he
      have heq : Q.filter (· ∈ e) = e := by
        ext v
        simp only [mem_filter]
        exact ⟨And.right,fun h => ⟨(hU e he).1 h,h⟩⟩
      rw [← card_filter,heq,(hU e he).2]
    _ = _ := by simp [sum_const, nsmul_eq_mul, Nat.mul_comm]

theorem neighbor_card {Q : Finset V} {E : Finset (Finset V)} (hU : uniformThree Q E)
    (hL : linear E) (v : V) : (neighbors E v).card = 2 * (incidence E v).card := by
  unfold neighbors
  rw [card_biUnion (fun e he f hf hne => link_disjoint hL he hf hne)]
  calc
    _ = ∑ _e ∈ incidence E v, (2:ℕ) := sum_congr rfl (fun e he => link_card hU he)
    _ = _ := by simp [sum_const, nsmul_eq_mul, Nat.mul_comm]

theorem shadow_pair {E : Finset (Finset V)} {x y : V} (hxy : x ≠ y) :
    ({x,y} : Finset V) ∈ shadow E ↔ y ∈ neighbors E x := by
  simp only [shadow,mem_biUnion,mem_powersetCard,mem_neighbors]
  have hcard : ({x,y} : Finset V).card = 2 := by simp [hxy]
  simp [hcard,hxy.symm,insert_subset_iff, singleton_subset_iff]

theorem unique_shadow_edge {E : Finset (Finset V)} (hL : linear E)
    {s : Finset V} (hs : s ∈ shadow E) :
    ∃! e, e ∈ E ∧ s ⊆ e := by
  obtain ⟨e,he,h⟩ := mem_biUnion.mp hs
  obtain ⟨hsE,hcard⟩ := mem_powersetCard.mp h
  refine ⟨e,⟨he,hsE⟩,?_⟩
  intro f hf
  by_contra! hne
  have h := card_le_card (subset_inter hf.2 hsE)
  rw [hcard] at h
  have := hL f hf.1 e he hne
  omega


theorem independent_remove_edges {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) :
    ∃ I ⊆ Q, independent E I ∧ Q.card ≤ I.card + E.card := by
  have hchoose (e : E) : ∃ x, x ∈ e.val := by
    have hc := (hU e.val e.property).2
    exact card_pos.mp (by omega)
  choose drop hdrop using hchoose
  let R : Finset V := univ.image drop
  have hR : R ⊆ Q := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    exact (hU e.val e.property).1 (hdrop e)
  have hRC : R.card ≤ E.card := by
    simpa [R] using card_image_le (f := drop) (s := (univ : Finset E))
  refine ⟨Q \ R,sdiff_subset,?_,?_⟩
  · intro e he hI
    let q : E := ⟨e,he⟩
    have hq : drop q ∈ R := mem_image.mpr ⟨q,mem_univ _,rfl⟩
    exact (mem_sdiff.mp (hI (hdrop q))).2 hq
  · have hcard := card_sdiff_of_subset hR
    omega

theorem remove_high_degree {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (d : ℝ) (hd : 0 < d)
    (hAverage : 3*(E.card : ℝ) ≤ d*Q.card) :
    ∃ S ⊆ Q, Q.card ≤ 2 * S.card ∧
      ∀ v ∈ S, ((incidence (E.filter (· ⊆ S)) v).card : ℝ) ≤ 2*d := by
  classical
  let B := Q.filter fun v => 2*d < ((incidence E v).card : ℝ)
  have hB : B ⊆ Q := filter_subset _ _
  have hsum : (∑ v ∈ Q, ((incidence E v).card : ℝ)) = 3*(E.card : ℝ) := by
    exact_mod_cast degree_sum hU
  have hBad : 2*d*(B.card : ℝ) ≤ d*Q.card := by
    calc
      _ = ∑ _v ∈ B, (2*d) := by rw [sum_const,nsmul_eq_mul]; ring
      _ ≤ ∑ v ∈ B, ((incidence E v).card : ℝ) := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2.le
      _ ≤ ∑ v ∈ Q, ((incidence E v).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := hsum.le.trans hAverage
  have hBCard : 2*B.card ≤ Q.card := by
    have h := (mul_le_mul_iff_right₀ hd).mp (show d*(2*(B.card : ℝ)) ≤ d*Q.card from by
      nlinarith only [hBad])
    exact_mod_cast h
  refine ⟨Q \ B,sdiff_subset,?_,?_⟩
  · have h := card_sdiff_of_subset hB
    omega
  · intro v hv
    have hvQ := (mem_sdiff.mp hv).1
    have hnot := (mem_sdiff.mp hv).2
    have hOld : ((incidence E v).card : ℝ) ≤ 2*d := by
      by_contra! h
      exact hnot (mem_filter.mpr ⟨hvQ,h⟩)
    have hinc : incidence (E.filter (· ⊆ Q \ B)) v ⊆ incidence E v := by
      intro e he
      rw [mem_incidence] at he ⊢
      exact ⟨(mem_filter.mp he.1).1,he.2⟩
    exact (Nat.cast_le.mpr (card_le_card hinc)).trans hOld



def outside (Q : Finset V) (E : Finset (Finset V)) (v : V) : Finset V :=
  Q \ insert v (neighbors E v)

def withCenter (v : V) (b : Bool) (I : Finset V) : Finset V :=
  if b then insert v I else I

def extension (v : V) (b : Bool) (T J : Finset V) : Finset V :=
  withCenter v b (T ∪ J)

theorem center_not_outside (Q : Finset V) (E : Finset (Finset V)) (v : V) :
    v ∉ outside Q E v := by simp [outside]

theorem outside_disjoint_neighbors (Q : Finset V) (E : Finset (Finset V)) (v : V) :
    Disjoint (outside Q E v) (neighbors E v) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (mem_sdiff.mp hx).2 (mem_insert_of_mem hy)

theorem extension_subset {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) {v : V} (hv : v ∈ Q) {T J : Finset V}
    (hT : T ⊆ outside Q E v) (hJ : J ⊆ neighbors E v) (b : Bool) :
    extension v b T J ⊆ Q := by
  have hT' : T ⊆ Q := hT.trans sdiff_subset
  have hJ' : J ⊆ Q := hJ.trans (neighbors_subset hU _)
  have hTJ := union_subset hT' hJ'
  cases b
  · exact hTJ
  · exact insert_subset_iff.mpr ⟨hv,hTJ⟩

theorem reconstruct_extension {Q : Finset V} {E : Finset (Finset V)} {v : V} {I : Finset V}
    (hI : I ⊆ Q) :
    extension v (decide (v ∈ I)) (I ∩ outside Q E v) (I ∩ neighbors E v) = I := by
  ext x
  by_cases hx : x = v
  · subst x
    by_cases hvI : v ∈ I <;> simp [extension,withCenter,outside,hvI]
  · by_cases hxN : x ∈ neighbors E v
    · by_cases hvI : v ∈ I <;> simp [extension,withCenter,outside,hx,hxN,hvI]
    · by_cases hvI : v ∈ I <;> simp [extension,withCenter,outside,hx,hxN,hvI,mem_sdiff]
      all_goals exact fun h => hI h

theorem extension_independent_iff {Q : Finset V} {E : Finset (Finset V)}
    (hL : linear E) (hTriangle : triangleFree E) {v : V}
    {T J : Finset V} (hT : T ⊆ outside Q E v) (hJ : J ⊆ neighbors E v)
    (hIT : independent E T) (b : Bool) :
    independent E (extension v b T J) ↔
      (∀ x ∈ J, independent E (insert x T)) ∧
      (b = true → ∀ e ∈ incidence E v, ¬ e.erase v ⊆ J) := by
  have hvT : v ∉ T := fun h => center_not_outside Q E v (hT h)
  have hvJ : v ∉ J := fun h => center_not_neighbor E v (hJ h)
  have hTJ : T ∪ J ⊆ extension v b T J := by
    cases b
    · exact Subset.rfl
    · exact subset_insert _ _
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro x hx e he heT
      apply h e he
      apply heT.trans
      apply subset_trans _ hTJ
      apply insert_subset_iff.mpr
      exact ⟨mem_union_right _ hx,subset_union_left⟩
    · intro hb e he hErase
      subst b
      obtain ⟨heE,hve⟩ := mem_incidence.mp he
      apply h e heE
      intro x hx
      by_cases hEq : x = v
      · subst x
        simp [extension,withCenter]
      · have hxJ := hErase (mem_erase.mpr ⟨hEq,hx⟩)
        simp [extension,withCenter,hxJ]
  · rintro ⟨hAvail,hPairs⟩ e he heIn
    by_cases hve : v ∈ e
    · have hb : b = true := by
        cases b
        · have h := heIn hve
          simp [extension,withCenter,hvT,hvJ] at h
        · rfl
      apply hPairs hb e (mem_incidence.mpr ⟨he,hve⟩)
      intro x hx
      have hxv := (mem_erase.mp hx).1
      have hxe := (mem_erase.mp hx).2
      have hxN : x ∈ neighbors E v := mem_neighbors.mpr ⟨hxv,e,he,hve,hxe⟩
      have hxin := heIn hxe
      simp only [extension,withCenter,hb,if_true,mem_insert,mem_union,hxv,false_or] at hxin
      rcases hxin with hxT | hxJ
      · exact ((Finset.disjoint_left.mp (outside_disjoint_neighbors Q E v)) (hT hxT) hxN).elim
      · exact hxJ
    · have hrest : e ⊆ T ∪ J := by
        intro x hx
        have hin := heIn hx
        have hxv : x ≠ v := fun h => hve (h ▸ hx)
        cases b <;> simpa [extension,withCenter,hxv] using hin
      have hbound := edge_away_meets_neighbors_at_most_once hL hTriangle he hve
      by_cases hInt : (e ∩ J).Nonempty
      · obtain ⟨x,hx⟩ := hInt
        have hxE := (mem_inter.mp hx).1
        have hxJ := (mem_inter.mp hx).2
        apply hAvail x hxJ e he
        intro y hy
        rcases mem_union.mp (hrest hy) with hyT | hyJ
        · exact mem_insert_of_mem hyT
        · have hyx : y = x := by
            by_contra! hne
            have h2 := one_lt_card.mpr ⟨y,mem_inter.mpr ⟨hy,hJ hyJ⟩,
              x,mem_inter.mpr ⟨hxE,hJ hxJ⟩,hne⟩
            exact h2.not_ge hbound
          simpa [hyx]
      · apply hIT e he
        intro x hx
        rcases mem_union.mp (hrest hx) with hxT | hxJ
        · exact hxT
        · exact (hInt ⟨x,mem_inter.mpr ⟨hx,hxJ⟩⟩).elim


def shadowCount (E : Finset (Finset V)) (J : Finset V) : ℕ :=
  ((shadow E).filter (· ⊆ J)).card

private theorem official_pair_card {E : Finset (Finset V)} {s : Finset V} (hs : s ∈ shadow E) :
    s.card = 2 := by
  obtain ⟨e,_,he⟩ := mem_biUnion.mp hs
  exact (mem_powersetCard.mp he).2

private theorem shadow_count_insert {E : Finset (Finset V)} {J : Finset V} {x : V}
    (hx : x ∉ J) : shadowCount E (insert x J) = shadowCount E J + (neighbors E x ∩ J).card := by
  let A := (shadow E).filter (· ⊆ J)
  let B := (neighbors E x ∩ J).image (fun y => ({x,y} : Finset V))
  have hBCard : B.card = (neighbors E x ∩ J).card := by
    apply card_image_of_injOn
    intro y hy z hz hEq
    have hyN : y ∈ neighbors E x := (mem_inter.mp hy).1
    have hyne : y ≠ x := (mem_neighbors.mp hyN).1
    change ({x,y} : Finset V) = {x,z} at hEq
    have hyMem : y ∈ ({x,z} : Finset V) := by rw [← hEq]; simp
    simpa [hyne] using hyMem
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro s hsA hsB
    obtain ⟨y,_,rfl⟩ := mem_image.mp hsB
    exact hx ((mem_filter.mp hsA).2 (by simp))
  have hEq : (shadow E).filter (· ⊆ insert x J) = A ∪ B := by
    ext s
    constructor
    · intro hs
      obtain ⟨hsE,hsIns⟩ := mem_filter.mp hs
      by_cases hsJ : s ⊆ J
      · exact mem_union_left _ (mem_filter.mpr ⟨hsE,hsJ⟩)
      · obtain ⟨y,hy,hyJ⟩ := not_subset.mp hsJ
        have hyx : y = x := by simpa [hyJ] using hsIns hy
        subst y
        obtain ⟨a,b,hab,he⟩ := card_eq_two.mp (official_pair_card hsE)
        have hxin : x ∈ ({a,b} : Finset V) := he ▸ hy
        simp only [mem_insert, mem_singleton] at hxin
        rcases hxin with rfl | rfl
        · subst s
          have hJ : b ∈ J := by simpa [hab.symm] using hsIns (by simp : b ∈ ({x,b} : Finset V))
          have hN : b ∈ neighbors E x := (shadow_pair hab).mp hsE
          exact mem_union_right _ (mem_image.mpr ⟨b,mem_inter.mpr ⟨hN,hJ⟩,rfl⟩)
        · subst s
          have hJ : a ∈ J := by simpa [hab] using hsIns (by simp : a ∈ ({a,x} : Finset V))
          have hN : a ∈ neighbors E x := by
            apply (shadow_pair hab.symm).mp
            simpa [Finset.pair_comm] using hsE
          exact mem_union_right _ (mem_image.mpr ⟨a,mem_inter.mpr ⟨hN,hJ⟩,Finset.pair_comm _ _⟩)
    · intro hs
      rcases mem_union.mp hs with h | h
      · obtain ⟨hsE,hsJ⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨hsE,hsJ.trans (subset_insert _ _)⟩
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
        obtain ⟨hyN,hyJ⟩ := mem_inter.mp hy
        have hxy : x ≠ y := (mem_neighbors.mp hyN).1.symm
        exact mem_filter.mpr ⟨(shadow_pair hxy).mpr hyN,
          insert_subset_iff.mpr ⟨mem_insert_self _ _,singleton_subset_iff.mpr (mem_insert_of_mem hyJ)⟩⟩
  unfold shadowCount
  rw [hEq,card_union_of_disjoint hdis,hBCard]

theorem shadow_count_union {E : Finset (Finset V)} {T J : Finset V} (hdis : Disjoint T J) :
    shadowCount E (T∪J) = shadowCount E T + shadowCount E J +
      ∑ x ∈ J,(neighbors E x ∩ T).card := by
  induction J using Finset.induction_on with
  | empty =>
    have h₀ : shadowCount E ∅ = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heE,he0⟩ := mem_filter.mp he
      have hfalse := card_le_card he0
      rw [official_pair_card heE,card_empty] at hfalse
      omega
    simp [h₀]
  | insert x J hx ih =>
    have hxT : x ∉ T := by
      intro h
      exact (Finset.disjoint_left.mp hdis) h (mem_insert_self _ _)
    have hxTJ : x ∉ T ∪ J := by simp [hxT,hx]
    have hd : Disjoint T J := hdis.mono_right (subset_insert _ _)
    have hd' : Disjoint (neighbors E x ∩ T) (neighbors E x ∩ J) :=
      hd.mono inter_subset_right inter_subset_right
    rw [union_insert,shadow_count_insert hxTJ,shadow_count_insert hx,ih hd,
      sum_insert hx, inter_union_distrib_left,card_union_of_disjoint hd']
    omega

theorem local_shadow_count {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hFree : triangleFree E)
    {v : V} {J : Finset V} (hJ : J ⊆ neighbors E v) :
    shadowCount E J = ((incidence E v).filter (fun e => e.erase v ⊆ J)).card := by
  let B := (incidence E v).filter (fun e => e.erase v ⊆ J)
  let G := B.image (·.erase v)
  have hinj : (B : Set (Finset V)).InjOn (·.erase v) := by
    intro e he f hf hEq
    have hv₁ : v ∈ e := (mem_incidence.mp (mem_filter.mp he).1).2
    have hv₂ : v ∈ f := (mem_incidence.mp (mem_filter.mp hf).1).2
    have h := congrArg (insert v) hEq
    rwa [insert_erase hv₁,insert_erase hv₂] at h
  have hg : G.card = B.card := card_image_of_injOn hinj
  have hEq : (shadow E).filter (· ⊆ J) = G := by
    ext s
    constructor
    · intro hs
      obtain ⟨hsE,hsJ⟩ := mem_filter.mp hs
      obtain ⟨e,he,hsE'⟩ := mem_biUnion.mp hsE
      have hsSub := (mem_powersetCard.mp hsE').1
      have hsCard := (mem_powersetCard.mp hsE').2
      have hve : v ∈ e := by
        by_contra! hn
        have h := card_le_card (subset_inter hsSub (hsJ.trans hJ))
        rw [hsCard] at h
        exact (show ¬(2:ℕ) ≤ 1 by decide)
          (h.trans (edge_away_meets_neighbors_at_most_once hL hFree he hn))
      have hInc : e ∈ incidence E v := mem_incidence.mpr ⟨he,hve⟩
      have hSub : s ⊆ e.erase v := by
        intro x hx
        exact mem_erase.mpr ⟨(mem_neighbors.mp (hJ (hsJ hx))).1,hsSub hx⟩
      have hS : s = e.erase v := eq_of_subset_of_card_le hSub (by rw [hsCard,link_card hU hInc])
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨hInc,hS ▸ hsJ⟩,hS.symm⟩
    · intro hs
      obtain ⟨e,he,rfl⟩ := mem_image.mp hs
      obtain ⟨heInc,heSub⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨e,(mem_incidence.mp heInc).1,
        mem_powersetCard.mpr ⟨erase_subset _ _,link_card hU heInc⟩⟩,heSub⟩
  rw [shadowCount,hEq,hg]

theorem shadow_count_extension {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hFree : triangleFree E)
    {v : V} {T J : Finset V} (hT : T ⊆ outside Q E v) (hJ : J ⊆ neighbors E v) (b : Bool) :
    shadowCount E (extension v b T J) =
      shadowCount E T + (∑ x ∈ J,(neighbors E x ∩ T).card) +
      ((incidence E v).filter (fun e => e.erase v ⊆ J)).card + (if b then J.card else 0) := by
  have hdis : Disjoint T J := (outside_disjoint_neighbors Q E v).mono hT hJ
  have hvT : v ∉ T := fun h => center_not_outside Q E v (hT h)
  have hvJ : v ∉ J := fun h => center_not_neighbor E v (hJ h)
  have hvTJ : v ∉ T ∪ J := by simp [hvT,hvJ]
  have hInter : neighbors E v ∩ (T∪J) = J := by
    ext x
    simp only [mem_inter,mem_union]
    exact ⟨fun ⟨hxN,hx⟩ => hx.elim (fun hxT =>
      ((Finset.disjoint_left.mp (outside_disjoint_neighbors Q E v)) (hT hxT) hxN).elim) id,
      fun hx => ⟨hJ hx,Or.inr hx⟩⟩
  cases b
  · simp [extension,withCenter,shadow_count_union hdis,local_shadow_count hU hL hFree hJ]
    omega
  · simp [extension,withCenter,shadow_count_insert hvTJ,hInter,shadow_count_union hdis,
      local_shadow_count hU hL hFree hJ]
    omega


/-- Choose an ordering for the two neighbors contributed by each incident edge. -/
structure LinkEndpoints {E : Finset (Finset V)} (v : V) where
  left : (incidence E v) → V
  right : (incidence E v) → V
  distinct : ∀ i, left i ≠ right i
  pair_eq : ∀ i, i.val.erase v = {left i,right i}

noncomputable def orderLinks {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (v : V) : LinkEndpoints (E:=E) v := by
  have h (i : incidence E v) : ∃ a b : V, a ≠ b ∧ i.val.erase v = {a,b} :=
    card_eq_two.mp (link_card hU i.property)
  choose a b hne hp using h
  exact ⟨a,b,hne,hp⟩

variable {E : Finset (Finset V)} {v : V}

abbrev LinkIndex := ↥(incidence E v)

def linkPick (a b : V) (k : Fin 4) : Finset V :=
  if k=0 then ∅ else if k=1 then {a} else if k=2 then {b} else {a,b}

def linkCode (a b : V) (J : Finset V) : Fin 4 :=
  if a ∈ J then (if b ∈ J then 3 else 1) else (if b ∈ J then 2 else 0)

theorem linkPick_subset (a b : V) (k : Fin 4) : linkPick a b k ⊆ {a,b} := by
  fin_cases k <;> simp [linkPick]

theorem pick_code (a b : V) (J : Finset V) :
    linkPick a b (linkCode a b J) = J ∩ {a,b} := by
  ext x
  by_cases h₁ : a ∈ J <;> by_cases h₂ : b ∈ J
  all_goals
    by_cases hx1 : x = a <;> by_cases hx2 : x = b
    all_goals
      simp_all [linkPick,linkCode]

theorem code_pick {a b : V} (hne : a ≠ b) (k : Fin 4) :
    linkCode a b (linkPick a b k) = k := by
  fin_cases k <;> simp [linkPick,linkCode,hne,hne.symm]

private def picked (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4) : Finset V :=
  univ.biUnion fun i => linkPick (L.left i) (L.right i) (σ i)

theorem picked_subset (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4) :
    picked L σ ⊆ neighbors E v := by
  intro x hx
  obtain ⟨i,_,hix⟩ := mem_biUnion.mp hx
  have h := linkPick_subset _ _ (σ i) hix
  rw [← L.pair_eq i] at h
  exact mem_biUnion.mpr ⟨i.val,i.property,h⟩

private theorem link_pick_disjoint (hL : linear E) (L : LinkEndpoints (E:=E) v)
    (σ : (incidence E v) → Fin 4) {i j : incidence E v} (hne : i ≠ j) :
    Disjoint (linkPick (L.left i) (L.right i) (σ i))
      (linkPick (L.left j) (L.right j) (σ j)) := by
  have he : i.val ≠ j.val := fun h => hne (Subtype.ext h)
  have h := link_disjoint hL i.property j.property he
  rw [L.pair_eq i,L.pair_eq j] at h
  exact h.mono (linkPick_subset _ _ _) (linkPick_subset _ _ _)

private theorem picked_inter_pair (hL : linear E) (L : LinkEndpoints (E:=E) v)
    (σ : (incidence E v) → Fin 4) (i : incidence E v) :
    picked L σ ∩ {L.left i,L.right i} = linkPick (L.left i) (L.right i) (σ i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hsel,hpair⟩ := mem_inter.mp hx
    obtain ⟨j,_,hxj⟩ := mem_biUnion.mp hsel
    by_cases hji : j = i
    · exact hji ▸ hxj
    · have h := link_disjoint hL j.property i.property (fun he => hji (Subtype.ext he))
      rw [L.pair_eq j,L.pair_eq i] at h
      exact ((Finset.disjoint_left.mp h) (linkPick_subset _ _ _ hxj) hpair).elim
  · intro hx
    exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,hx⟩,linkPick_subset _ _ _ hx⟩

noncomputable def choiceEquiv (hL : linear E) (L : LinkEndpoints (E:=E) v) :
    ((incidence E v) → Fin 4) ≃ ↥((neighbors E v).powerset) where
  toFun σ := ⟨picked L σ,mem_powerset.mpr (picked_subset L σ)⟩
  invFun J i := linkCode (L.left i) (L.right i) J.val
  left_inv σ := by
    funext i
    apply_fun linkPick (L.left i) (L.right i)
    · rw [pick_code,picked_inter_pair hL]
    · intro a b hab
      have h := congrArg (linkCode (L.left i) (L.right i)) hab
      simpa only [code_pick (L.distinct i)] using h
  right_inv J := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,h⟩ := mem_biUnion.mp hx
      rw [pick_code] at h
      exact (mem_inter.mp h).1
    · intro hx
      have hn := mem_powerset.mp J.property hx
      obtain ⟨e,he,hxe⟩ := mem_biUnion.mp hn
      let i : incidence E v := ⟨e,he⟩
      have hpair : x ∈ ({L.left i,L.right i} : Finset V) := by
        rw [← L.pair_eq i]
        exact hxe
      apply mem_biUnion.mpr
      refine ⟨i,mem_univ _,?_⟩
      rw [pick_code]
      exact mem_inter.mpr ⟨hx,hpair⟩

theorem pick_sum {R : Type*} [AddCommMonoid R] (hL : linear E)
    (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4) (f : V → R) :
    ∑ x ∈ picked L σ, f x =
      ∑ i ∈ (univ : Finset (incidence E v)), ∑ x ∈ linkPick (L.left i) (L.right i) (σ i), f x := by
  classical
  rw [picked,sum_biUnion]
  intro i hi j hj hne
  exact link_pick_disjoint hL L σ hne

theorem picked_full_link (hL : linear E) (L : LinkEndpoints (E:=E) v)
    (σ : (incidence E v) → Fin 4) (i : incidence E v) :
    i.val.erase v ⊆ picked L σ ↔ σ i = 3 := by
  constructor
  · intro h
    rw [L.pair_eq i] at h
    have he : linkPick (L.left i) (L.right i) (σ i) = {L.left i,L.right i} := by
      rw [← picked_inter_pair hL L]
      exact inter_eq_right.mpr h
    have hc := congrArg (linkCode (L.left i) (L.right i)) he
    change linkCode (L.left i) (L.right i) (linkPick (L.left i) (L.right i) (σ i)) =
      linkCode (L.left i) (L.right i) {L.left i,L.right i} at hc
    rw [code_pick (L.distinct i)] at hc
    simpa [linkCode] using hc
  · intro h
    rw [L.pair_eq i]
    intro x hx
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,?_⟩
    simp [h,linkPick,hx]


def fullLinks (E : Finset (Finset V)) (v : V) (I : Finset V) : Finset (Finset V) :=
  (incidence E v).filter (fun e => e.erase v ⊆ I)

noncomputable def vertexScore (E : Finset (Finset V)) (d δ : ℝ) (v : V) (I : Finset V) : ℝ :=
  if v ∈ I then Real.sqrt d else δ*(neighbors E v ∩ I).card+(fullLinks E v I).card

theorem full_link_sum_le_shadow {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (I : Finset V) :
    (∑ v ∈ Q,(fullLinks E v I).card) ≤ shadowCount E I := by
  let S := Q.biUnion (fun v => (fullLinks E v I).image (fun e => (v,e)))
  have hsCard : S.card = ∑ v ∈ Q,(fullLinks E v I).card := by
    unfold S
    rw [card_biUnion]
    · apply sum_congr rfl
      intro v hv
      exact card_image_of_injective _ fun a b h => congrArg Prod.snd h
    · intro v hv w hw hvw
      change Disjoint ((fullLinks E v I).image (fun e => (v,e)))
        ((fullLinks E w I).image (fun e => (w,e)))
      rw [Finset.disjoint_left]
      intro q hqv hqw
      obtain ⟨e,_,he⟩ := mem_image.mp hqv
      obtain ⟨f,_,hf⟩ := mem_image.mp hqw
      exact hvw (congrArg Prod.fst (he.trans hf.symm))
  rw [← hsCard]
  let eraseCenter : V × Finset V → Finset V := fun q => q.2.erase q.1
  have hS (q : V × Finset V) (hq : q ∈ S) : q.2 ∈ incidence E q.1 ∧ q.2.erase q.1 ⊆ I := by
    rcases q with ⟨v,e⟩
    obtain ⟨w,hw,hq⟩ := mem_biUnion.mp hq
    obtain ⟨f,hf,hEq⟩ := mem_image.mp hq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hEq
    exact mem_filter.mp hf
  have hSMap : Set.MapsTo eraseCenter S ((shadow E).filter (· ⊆ I) : Finset (Finset V)) := by
    intro q hq
    obtain ⟨hinc,hsub⟩ := hS q hq
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨q.2,(mem_incidence.mp hinc).1,
      mem_powersetCard.mpr ⟨erase_subset _ _,link_card hU hinc⟩⟩,hsub⟩
  have hInj : Set.InjOn eraseCenter S := by
    rintro ⟨v,e⟩ hq ⟨w,f⟩ hr he
    have hIe := (hS (v,e) hq).1
    have hIf := (hS (w,f) hr).1
    have hShadow : e.erase v ∈ shadow E := (mem_filter.mp (hSMap hq)).1
    obtain ⟨g,hg,hunique⟩ := unique_shadow_edge hL hShadow
    have hEqE : e = g := hunique _ ⟨(mem_incidence.mp hIe).1,erase_subset _ _⟩
    have hEqF : f = g := hunique _ ⟨(mem_incidence.mp hIf).1,by
      change e.erase v = f.erase w at he
      rw [he]
      exact erase_subset _ _⟩
    subst g
    subst f
    apply Prod.ext
    · change v = w
      by_contra! hne
      have hmem : v ∈ e.erase w := mem_erase.mpr ⟨hne,(mem_incidence.mp hIe).2⟩
      change e.erase v = e.erase w at he
      rw [← he] at hmem
      exact (mem_erase.mp hmem).1 rfl
    · rfl
  exact card_le_card_of_injOn eraseCenter hSMap hInj

theorem sum_neighbors_inter {Q : Finset V} {E : Finset (Finset V)} {I : Finset V} :
    ∑ v ∈ Q,(neighbors E v ∩ I).card = ∑ x ∈ I,(neighbors E x ∩ Q).card := by
  have hEq (A : Finset V) (v : V) : neighbors E v ∩ A = A.filter (· ∈ neighbors E v) := by
    ext x
    simp [and_comm]
  simp_rw [hEq,card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro v hv
  have he : x ∈ neighbors E v ↔ v ∈ neighbors E x := neighbor_symmetric
  by_cases hx : x ∈ neighbors E v
  · simp [hx,he.mp hx]
  · simp [hx,show v ∉ neighbors E x from fun h => hx (he.mpr h)]

theorem upper_score_sum {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E)
    (d δ : ℝ) (hδ : 0 ≤ δ) (hMax : ∀ v ∈ Q, ((incidence E v).card : ℝ) ≤ d)
    {I : Finset V} (hI : I ⊆ Q) :
    ∑ v ∈ Q,vertexScore E d δ v I ≤
      (Real.sqrt d + 2*δ*d)*I.card + shadowCount E I := by
  have h₁ : (∑ v ∈ Q, if v ∈ I then Real.sqrt d else (0:ℝ)) = Real.sqrt d * I.card := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    have hh : Q.filter (· ∈ I) = I := by ext u; exact mem_filter.trans ⟨And.right, fun h => ⟨hI h,h⟩⟩
    rw [hh,mul_comm]
  have h₂ : (∑ v ∈ Q, ((neighbors E v∩I).card : ℝ)) ≤ 2*d*I.card := by
    rw [← Nat.cast_sum,sum_neighbors_inter,Nat.cast_sum]
    calc
      _ ≤ ∑ _v ∈ I,(2*d) := by
        apply sum_le_sum
        intro v hv
        have hcard : ((neighbors E v∩Q).card : ℝ) ≤ (neighbors E v).card :=
          Nat.cast_le.mpr (card_le_card inter_subset_left)
        rw [neighbor_card hU hL,Nat.cast_mul,Nat.cast_ofNat] at hcard
        exact hcard.trans (mul_le_mul_of_nonneg_left (hMax v (hI hv)) (by norm_num))
      _ = _ := by rw [sum_const,nsmul_eq_mul]; ring
  have h₃ : (∑ v ∈ Q,((fullLinks E v I).card : ℝ)) ≤ shadowCount E I := by
    exact_mod_cast full_link_sum_le_shadow hU hL I
  calc
    _ ≤ ∑ v ∈ Q, ((if v ∈ I then Real.sqrt d else (0:ℝ)) +
        δ*(neighbors E v ∩ I).card+(fullLinks E v I).card) := by
      apply sum_le_sum
      intro v hv
      by_cases hvI : v ∈ I
      · simp only [vertexScore,if_pos hvI]
        have hA : 0 ≤ δ*((neighbors E v∩I).card:ℝ) := by positivity
        have hB : 0 ≤ ((fullLinks E v I).card:ℝ) := by positivity
        linarith
      · simp [vertexScore,hvI]
    _ = Real.sqrt d * I.card +
        δ*(∑ v ∈ Q, ((neighbors E v ∩ I).card : ℝ)) +
        (∑ v ∈ Q, ((fullLinks E v I).card : ℝ)) := by
      rw [sum_add_distrib,sum_add_distrib,← mul_sum,h₁]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left h₂ hδ
      nlinarith only [h,h₃]


private noncomputable def vertexMass (E : Finset (Finset V)) (T : Finset V)
    (δ : ℝ) (x : V) : ℝ :=
  if independent E (insert x T) then Real.exp (-δ*(neighbors E x∩T).card) else 0

private theorem vertex_mass_range (E : Finset (Finset V)) (T : Finset V)
    (δ : ℝ) (hδ : 0 ≤ δ) (x : V) :
    0 ≤ vertexMass E T δ x ∧ vertexMass E T δ x ≤ 1 := by
  unfold vertexMass
  split
  · refine ⟨(Real.exp_pos _).le,?_⟩
    rw [← Real.exp_zero,Real.exp_le_exp]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (Nat.cast_nonneg _)
  · norm_num

private noncomputable def linkMass (β u w : ℝ) (b : Bool) (k : Fin 4) : ℝ :=
  if k = 0 then 1 else if k = 1 then (if b then β*u else u)
    else if k = 2 then (if b then β*w else w) else (if b then 0 else β*u*w)

private noncomputable def localScore (δ : ℝ) (k : Fin 4) : ℝ :=
  if k = 0 then 0 else if k = 3 then 2*δ+1 else δ

private theorem link_mass_sums (β u w δ : ℝ) :
    (∑ k : Fin 4,linkMass β u w false k) = 1+u+w+β*u*w ∧
    (∑ k : Fin 4,linkMass β u w true k) = 1+β*(u+w) ∧
    (∑ k : Fin 4,linkMass β u w false k*localScore δ k) =
      δ*(u+w)+(2*δ+1)*β*u*w := by
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  refine ⟨?_,?_,?_⟩ <;>
    norm_num [Fin.sum_univ_four,linkMass,localScore,h20,h21,h30,h31,h32,h31.symm,h32.symm] <;> ring

private def linkLegal (E : Finset (Finset V)) (T : Finset V) (a c : V)
    (b : Bool) (k : Fin 4) : Prop :=
  (∀ x ∈ linkPick a c k, independent E (insert x T)) ∧ (b = true → k ≠ 3)

private instance (E : Finset (Finset V)) (T : Finset V) (a c : V) (b : Bool) (k : Fin 4) :
    Decidable (linkLegal E T a c b k) :=
  inferInstanceAs (Decidable ((∀ x ∈ linkPick a c k,independent E (insert x T)) ∧ (b = true → k ≠ 3)))

private def linkEnergy (E : Finset (Finset V)) (T : Finset V) (a c : V)
    (b : Bool) (k : Fin 4) : ℕ :=
  (∑ x ∈ linkPick a c k,(neighbors E x∩T).card) +
    (if k = 3 then 1 else 0) + (if b then (linkPick a c k).card else 0)

private theorem link_mass_formula {E : Finset (Finset V)} (T : Finset V)
    (δ : ℝ) {a c : V} (hne : a ≠ c) (b : Bool) (k : Fin 4) :
    linkMass (Real.exp (-δ)) (vertexMass E T δ a) (vertexMass E T δ c) b k =
      if linkLegal E T a c b k then Real.exp (-δ*((linkEnergy E T a c b k : ℕ) : ℝ)) else 0 := by
  have ex_add_one (z : ℝ) : Real.exp (-(δ*(z+1))) = Real.exp (-δ)*Real.exp (-(δ*z)) := by
    rw [show -(δ*(z+1)) = -δ+(-(δ*z)) by ring,Real.exp_add]
  have ex_add_pair (y z : ℝ) : Real.exp (-(δ*(y+z))) = Real.exp (-(δ*y))*Real.exp (-(δ*z)) := by
    rw [show -(δ*(y+z)) = -(δ*y)+(-(δ*z)) by ring, Real.exp_add]
  by_cases ha : independent E (insert a T) <;> by_cases hc : independent E (insert c T) <;>
    fin_cases k <;> cases b <;>
    simp [linkMass,vertexMass,linkLegal,linkEnergy,linkPick,ha,hc,hne,ex_add_one,ex_add_pair] <;> ring

private theorem extension_legal {Q : Finset V} {E : Finset (Finset V)}
    (hL : linear E) (hTriangle : triangleFree E) {v : V}
    {T : Finset V} (hT : T ⊆ outside Q E v) (hIT : independent E T)
    (L : LinkEndpoints (E:=E) v) (b : Bool) (σ : (incidence E v) → Fin 4) :
    independent E (extension v b T (picked L σ)) ↔
      ∀ i : incidence E v, linkLegal E T (L.left i) (L.right i) b (σ i) := by
  rw [extension_independent_iff hL hTriangle hT (picked_subset L σ) hIT]
  constructor
  · rintro ⟨h₁,h₂⟩ i
    refine ⟨fun x hx => h₁ x (mem_biUnion.mpr ⟨i,mem_univ _,hx⟩),?_⟩
    intro hb hFull
    exact h₂ hb i.val i.property ((picked_full_link hL L σ i).mpr hFull)
  · intro h
    refine ⟨?_,?_⟩
    · intro x hx
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
      exact (h i).1 x hi
    · intro hb e he hfull
      let i : incidence E v := ⟨e,he⟩
      exact (h i).2 hb ((picked_full_link hL L σ i).mp hfull)

private theorem full_link_count_sum {E : Finset (Finset V)} {v : V}
    (hL : linear E) (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4) :
    (fullLinks E v (picked L σ)).card = ∑ i : incidence E v, if σ i = 3 then 1 else 0 := by
  unfold fullLinks
  rw [card_filter, ← sum_coe_sort]
  apply sum_congr rfl
  intro i hi
  by_cases h : σ i = 3
  · simp [h,(picked_full_link hL L σ i).mpr h]
  · simp [h,show ¬i.val.erase v ⊆ picked L σ from fun he => h ((picked_full_link hL L σ i).mp he)]

private theorem pick_card_sum {E : Finset (Finset V)} {v : V}
    (hL : linear E) (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4) :
    (picked L σ).card =
      ∑ i : incidence E v,(linkPick (L.left i) (L.right i) (σ i)).card := by
  simpa [sum_const,nsmul_eq_mul] using pick_sum hL L σ (fun _ => (1:ℕ))

private theorem count_extension_eq_energy {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hTriangle : triangleFree E) {v : V}
    {T : Finset V} (hT : T ⊆ outside Q E v)
    (L : LinkEndpoints (E:=E) v) (b : Bool) (σ : (incidence E v) → Fin 4) :
    shadowCount E (extension v b T (picked L σ)) =
      shadowCount E T + ∑ i : incidence E v, linkEnergy E T (L.left i) (L.right i) b (σ i) := by
  rw [shadow_count_extension hU hL hTriangle hT (picked_subset L σ), ← fullLinks,
    full_link_count_sum hL, pick_card_sum hL, pick_sum hL]
  cases b <;> simp [linkEnergy, sum_add_distrib, add_assoc]

private theorem scored_extension {Q : Finset V} {E : Finset (Finset V)} {v : V}
    (hL : linear E) {T : Finset V} (hT : T ⊆ outside Q E v)
    (L : LinkEndpoints (E:=E) v) (σ : (incidence E v) → Fin 4)
    (d δ : ℝ) (b : Bool) :
    vertexScore E d δ v (extension v b T (picked L σ)) =
      if b then Real.sqrt d else ∑ i : incidence E v,localScore δ (σ i) := by
  have hvT : v ∉ T := fun h => center_not_outside Q E v (hT h)
  have hvI : v ∉ picked L σ := fun h => center_not_neighbor E v (picked_subset L σ h)
  cases b
  · change vertexScore E d δ v (T ∪ picked L σ) = ∑ i : incidence E v,localScore δ (σ i)
    rw [vertexScore,if_neg (by simp [hvT,hvI])]
    have hset : neighbors E v ∩ (T ∪ picked L σ) = picked L σ := by
      ext x
      simp only [mem_inter,mem_union]
      exact ⟨fun ⟨hxN,hx⟩ => hx.elim (fun hxT =>
        ((Finset.disjoint_left.mp (outside_disjoint_neighbors Q E v)) (hT hxT) hxN).elim) id,
        fun hx => ⟨picked_subset L σ hx,Or.inr hx⟩⟩
    have hfull : fullLinks E v (T ∪ picked L σ) = fullLinks E v (picked L σ) := by
      ext e
      simp only [fullLinks,mem_filter]
      constructor
      · rintro ⟨he,hsub⟩
        refine ⟨he,?_⟩
        intro x hx
        have hN : x ∈ neighbors E v := mem_biUnion.mpr ⟨e,he,hx⟩
        rw [← hset]
        exact mem_inter.mpr ⟨hN,hsub hx⟩
      · rintro ⟨he,hs⟩
        exact ⟨he,hs.trans subset_union_right⟩
    rw [hset,hfull,full_link_count_sum hL,pick_card_sum hL]
    push_cast
    simp only [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hne := L.distinct i
    generalize σ i = k
    fin_cases k <;> simp [linkPick,localScore,hne] <;> ring
  · change vertexScore E d δ v (insert v (T ∪ picked L σ)) = Real.sqrt d
    simp [vertexScore]

private theorem weighted_extension {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hTriangle : triangleFree E) {v : V}
    {T : Finset V} (hT : T ⊆ outside Q E v) (hIT : independent E T)
    (L : LinkEndpoints (E:=E) v) (δ : ℝ) (b : Bool) (σ : (incidence E v) → Fin 4) :
    (if independent E (extension v b T (picked L σ)) then
      Real.exp (-δ*((shadowCount E (extension v b T (picked L σ)) : ℕ) : ℝ)) else 0) =
        Real.exp (-δ*((shadowCount E T : ℕ) : ℝ)) *
          ∏ i : incidence E v,
            linkMass (Real.exp (-δ)) (vertexMass E T δ (L.left i)) (vertexMass E T δ (L.right i)) b (σ i) := by
  classical
  simp_rw [link_mass_formula T δ (L.distinct _)]
  have hLegal := extension_legal hL hTriangle hT hIT L b σ
  by_cases h : independent E (extension v b T (picked L σ))
  · rw [if_pos h,count_extension_eq_energy hU hL hTriangle hT]
    push_cast
    rw [mul_add,Real.exp_add,mul_sum,Real.exp_sum]
    congr 1
    exact prod_congr rfl (fun i _ => (if_pos (hLegal.mp h i)).symm)
  · rw [if_neg h]
    have hNo : ¬ ∀ i : incidence E v, linkLegal E T (L.left i) (L.right i) b (σ i) :=
      fun hAll => h (hLegal.mpr hAll)
    obtain ⟨i,hi⟩ := not_forall.mp hNo
    rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi),mul_zero]


noncomputable def allowedWeight (E : Finset (Finset V)) (δ : ℝ) (I : Finset V) : ℝ :=
  if independent E I then Real.exp (-δ*(shadowCount E I : ℝ)) else 0

private theorem conditional_lower {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hTriangle : triangleFree E) {v : V}
    {T : Finset V} (hT : T ⊆ outside Q E v) (hIT : independent E T)
    (L : LinkEndpoints (E:=E) v) (d δ : ℝ) (hd : Real.exp 8 ≤ d) (hδ : 0 ≤ δ) :
    Real.log d/64 * (∑ x : Bool × ((incidence E v) → Fin 4),
      allowedWeight E δ (extension v x.1 T (picked L x.2))) ≤
      ∑ x : Bool × ((incidence E v) → Fin 4),
        allowedWeight E δ (extension v x.1 T (picked L x.2)) *
          vertexScore E d δ v (extension v x.1 T (picked L x.2)) := by
  classical
  let I := ↥(incidence E v)
  let β := Real.exp (-δ)
  let u (i : I) := vertexMass E T δ (L.left i)
  let w (i : I) := vertexMass E T δ (L.right i)
  let e0 (i : I) := 1+u i+w i+β*u i*w i
  let e1 (i : I) := 1+β*(u i+w i)
  let g (b : Bool) (i : I) (k : Fin 4) := linkMass β (u i) (w i) b k
  let z := Real.exp (-δ*(shadowCount E T : ℝ))
  let make (b : Bool) (σ : I → Fin 4) := extension v b T (picked L σ)
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hu (i : I) : 0 ≤ u i ∧ u i ≤ 1 := vertex_mass_range E T δ hδ (L.left i)
  have hw (i : I) : 0 ≤ w i ∧ w i ≤ 1 := vertex_mass_range E T δ hδ (L.right i)
  have hb : 0 < β := Real.exp_pos _
  have he0 (i : I) : 0 < e0 i := by dsimp [e0]; positivity [((hu i).1), ((hw i).1)]
  have hMass (b : Bool) (σ : I → Fin 4) :
      allowedWeight E δ (make b σ) = z * (∏ i, g b i (σ i)) :=
    weighted_extension hU hL hTriangle hT hIT L δ b σ
  have h0 (i : I) : (∑ k,g false i k) = e0 i := (link_mass_sums β _ _ δ).1
  have h1 (i : I) : (∑ k,g true i k) = e1 i := (link_mass_sums β _ _ δ).2.1
  have hsum0 : (∑ σ : I → Fin 4,allowedWeight E δ (make false σ)) = z*(∏ i,e0 i) := by
    simp_rw [hMass false]
    rw [← mul_sum, ← Fintype.prod_sum]
    simp_rw [h0]
  have hsum1 : (∑ σ : I → Fin 4,allowedWeight E δ (make true σ)) = z*(∏ i,e1 i) := by
    simp_rw [hMass true]
    rw [← mul_sum, ← Fintype.prod_sum]
    simp_rw [h1]
  have hscore1 (σ : I → Fin 4) : vertexScore E d δ v (make true σ) = Real.sqrt d := by
    simpa only [if_true] using scored_extension hL hT L σ d δ true
  have only_score (σ : I → Fin 4) :
      vertexScore E d δ v (make false σ) = ∑ i,localScore δ (σ i) := by
    exact scored_extension hL hT L σ d δ false
  have hscore0 : z*(∏ i,e0 i)*(∑ i,(δ*(u i+w i)+β*u i*w i)/e0 i) ≤
      ∑ σ : I → Fin 4,
        allowedWeight E δ (make false σ) * vertexScore E d δ v (make false σ) := by
    simp_rw [hMass false, only_score, mul_assoc z]
    rw [← mul_sum, OMA.HypergraphWeights.additive_product_sum (g false) (fun _ => localScore δ)
      (fun i => (h0 i).symm ▸ (he0 i).ne')]
    simp_rw [h0]
    have hterm (i : I) : (∑ k,g false i k * localScore δ k) =
          δ*(u i+w i)+(2*δ+1)*β*u i*w i := (link_mass_sums β _ _ δ).2.2
    simp_rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hz
    apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun i _ => (he0 i).le))
    apply sum_le_sum
    intro i hi
    apply div_le_div_of_nonneg_right _ (he0 i).le
    have h := mul_nonneg (mul_nonneg (mul_nonneg hδ hb.le) (hu i).1) (hw i).1
    nlinarith only [h]
  have hbase := OMA.HypergraphWeights.product_occupancy d δ hd hδ
    u w (fun i => (hu i).1) (fun i => (hu i).2) (fun i => (hw i).1) (fun i => (hw i).2)
  change Real.log d/64*((∏ i,e0 i)+(∏ i,e1 i)) ≤
    Real.sqrt d*(∏ i,e1 i)+(∏ i,e0 i)*(∑ i,(δ*(u i+w i)+β*u i*w i)/e0 i) at hbase
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  change Real.log d/64*((∑ σ : I → Fin 4,allowedWeight E δ (make true σ))+
      (∑ σ : I → Fin 4,allowedWeight E δ (make false σ))) ≤
    (∑ σ : I → Fin 4,allowedWeight E δ (make true σ)*vertexScore E d δ v (make true σ))+
      (∑ σ : I → Fin 4,allowedWeight E δ (make false σ)*vertexScore E d δ v (make false σ))
  have hPresent : (∑ σ : I → Fin 4,
      allowedWeight E δ (make true σ)*vertexScore E d δ v (make true σ)) =
      (z*(∏ i,e1 i))*Real.sqrt d := by
    simp_rw [hscore1]
    rw [← sum_mul,hsum1]
  rw [hsum0,hsum1,hPresent]
  have h := mul_le_mul_of_nonneg_left hbase hz
  calc
    _ = z * (Real.log d/64*((∏ i,e0 i)+(∏ i,e1 i))) := by ring
    _ ≤ _ := h
    _ ≤ _ := by linarith only [hscore0]

private noncomputable def extensionEquiv {Q : Finset V} {E : Finset (Finset V)} {v : V}
    (hU : uniformThree Q E) (hL : linear E) (hv : v ∈ Q) (L : LinkEndpoints (E:=E) v) :
    (↥((outside Q E v).powerset) × (Bool × ((incidence E v) → Fin 4))) ≃ ↥Q.powerset where
  toFun f := ⟨extension v f.2.1 f.1.val (picked L f.2.2),
    mem_powerset.mpr (extension_subset hU hv (mem_powerset.mp f.1.property)
      (picked_subset L f.2.2) f.2.1)⟩
  invFun I :=
    (⟨I.val ∩ outside Q E v,mem_powerset.mpr inter_subset_right⟩,decide (v ∈ I.val),
      (choiceEquiv hL L).symm ⟨I.val ∩ neighbors E v,mem_powerset.mpr inter_subset_right⟩)
  left_inv f := by
    rcases f with ⟨T,b,σ⟩
    have hT := mem_powerset.mp T.property
    have hJ := picked_subset L σ
    have hCenter : v ∈ extension v b T.val (picked L σ) ↔ b = true := by
      have hvT : v ∉ T.val := fun hv => center_not_outside Q E v (hT hv)
      have hvJ : v ∉ picked L σ := fun hv => center_not_neighbor E v (hJ hv)
      cases b <;> simp [extension,withCenter,hvT,hvJ]
    have hOut : extension v b T.val (picked L σ) ∩ outside Q E v = T.val := by
      ext x
      have hx0 : x ∈ outside Q E v → x ≠ v := fun hx h => center_not_outside Q E v (h ▸ hx)
      have hDis : Disjoint (outside Q E v) (picked L σ) :=
        (outside_disjoint_neighbors Q E v).mono_right hJ
      by_cases hx : x ∈ outside Q E v
      · have hxNot : x ∉ picked L σ := fun h => (Finset.disjoint_left.mp hDis) hx h
        cases b <;> simp [extension,withCenter,hx,hxNot,hx0 hx]
      · have hnot : x ∉ T.val := fun h => hx (hT h)
        simp [hx,hnot]
    have hIn : extension v b T.val (picked L σ) ∩ neighbors E v = picked L σ := by
      ext x
      by_cases hx : x ∈ neighbors E v
      · have hxnot : x ∉ T.val := fun h =>
          (Finset.disjoint_left.mp (outside_disjoint_neighbors Q E v)) (hT h) hx
        have hxv := (mem_neighbors.mp hx).1
        cases b <;> simp [extension,withCenter,hx,hxnot,hxv]
      · have hp : x ∉ picked L σ := fun h => hx (hJ h)
        simp [hx,hp]
    apply Prod.ext
    · exact Subtype.ext hOut
    · apply Prod.ext
      · cases b <;> simp_all
      · apply (choiceEquiv hL L).injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext hIn
  right_inv I := by
    apply Subtype.ext
    let J : ↥((neighbors E v).powerset) :=
      ⟨I.val ∩ neighbors E v,mem_powerset.mpr inter_subset_right⟩
    have hJ := congrArg Subtype.val ((choiceEquiv hL L).apply_symm_apply J)
    change picked L ((choiceEquiv hL L).symm J) = I.val ∩ neighbors E v at hJ
    change extension v (decide (v ∈ I.val)) (I.val ∩ outside Q E v)
      (picked L ((choiceEquiv hL L).symm J)) = I.val
    rw [hJ]
    exact reconstruct_extension (mem_powerset.mp I.property)


theorem independent_mono {E : Finset (Finset V)} {I J : Finset V} (h : J ⊆ I)
    (hi : independent E I) : independent E J := fun e he hsub => hi e he (hsub.trans h)

theorem weighted_score_lower {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hTriangle : triangleFree E)
    (d δ : ℝ) (hd : Real.exp 8 ≤ d) (hδ : 0 ≤ δ) {v : V} (hv : v ∈ Q) :
    Real.log d/64*(∑ I ∈ independentSets Q E,Real.exp (-δ*(shadowCount E I : ℝ))) ≤
      ∑ I ∈ independentSets Q E,Real.exp (-δ*(shadowCount E I : ℝ))*vertexScore E d δ v I := by
  classical
  let L := orderLinks hU v
  let e := extensionEquiv hU hL hv L
  have hW (I : Finset V) :
      (if independent E I then
        Real.exp (-δ*(shadowCount E I : ℝ))*vertexScore E d δ v I else 0) =
      allowedWeight E δ I * vertexScore E d δ v I := by
    by_cases h : independent E I <;> simp [allowedWeight,h]
  have reindex (f : Finset V → ℝ) :
      (∑ I ∈ Q.powerset,f I) =
      ∑ x : ↥((outside Q E v).powerset) × (Bool × ((incidence E v) → Fin 4)),
        f (extension v x.2.1 x.1.val (picked L x.2.2)) := by
    rw [← sum_coe_sort]
    exact (e.sum_comp (fun I => f I.val)).symm
  simp only [independentSets,sum_filter,hW]
  change Real.log d/64*(∑ I ∈ Q.powerset,allowedWeight E δ I) ≤ _
  rw [reindex (allowedWeight E δ),reindex (fun I => allowedWeight E δ I*vertexScore E d δ v I)]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type,mul_sum]
  apply sum_le_sum
  intro T hT
  have hTout : T.val ⊆ outside Q E v := mem_powerset.mp T.property
  by_cases hIT : independent E T.val
  · exact conditional_lower hU hL hTriangle hTout hIT L d δ hd hδ
  · have hzero (x : Bool × ((incidence E v) → Fin 4)) :
        allowedWeight E δ (extension v x.1 T.val (picked L x.2)) = 0 := by
      have hsub : T.val ⊆ extension v x.1 T.val (picked L x.2) := by
        rcases x with ⟨b,σ⟩
        cases b
        · exact subset_union_left
        · exact subset_union_left.trans (subset_insert _ _)
      exact if_neg (fun hs => hIT (independent_mono hsub hs))
    simp_rw [hzero,zero_mul]
    simp

theorem independent_logarithmic_locally {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (hTriangle : triangleFree E)
    (d : ℝ) (hd : Real.exp 8 ≤ d)
    (hMax : ∀ v ∈ Q, ((incidence E v).card : ℝ) ≤ d)
    (hCoarse : ∃ I ⊆ Q, independent E I ∧ (Q.card : ℝ)/(8*Real.sqrt d) ≤ I.card) :
    ∃ I ⊆ Q, independent E I ∧ (Q.card : ℝ)*Real.sqrt (Real.log d/d)/320 ≤ I.card := by
  classical
  by_cases hQ : Q.Nonempty
  swap
  · have hEmpty : Q = ∅ := not_nonempty_iff_eq_empty.mp hQ
    refine ⟨∅,empty_subset _, ?_, by simp [hEmpty]⟩
    intro e he h
    have hCard := card_le_card h
    rw [(hU e he).2,card_empty] at hCard
    omega
  have hQ0 : (0 : ℝ) < Q.card := by exact_mod_cast card_pos.mpr hQ
  have hd0 : 0 < d := (Real.exp_pos (8:ℝ)).trans_le hd
  have hLog : 8 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos (8:ℝ)) hd
    rwa [Real.log_exp] at h
  have hLog0 : 0 < Real.log d := by linarith
  let δ := Real.sqrt (Real.log d/d)
  have hδ : 0 < δ := Real.sqrt_pos_of_pos (div_pos hLog0 hd0)
  have hδsq : δ^2*d = Real.log d := by
    dsimp [δ]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hd0.ne']
  let F := independentSets Q E
  have hEmpty : ∅ ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (empty_subset Q),?_⟩
    intro e he h
    have hc := card_le_card h
    rw [(hU e he).2,card_empty] at hc
    omega
  obtain ⟨A,hAF,hMost⟩ := exists_max_image F Finset.card ⟨∅,hEmpty⟩
  let m := A.card
  have hA := mem_filter.mp hAF
  have hmMax (I : Finset V) (hI : I ∈ F) : I.card ≤ m := hMost I hI
  have hmQ : m ≤ Q.card := card_le_card (mem_powerset.mp hA.1)
  obtain ⟨I,hIQ,hIind,hIcount⟩ := hCoarse
  have hIm : I.card ≤ m := hmMax I (mem_filter.mpr ⟨mem_powerset.mpr hIQ,hIind⟩)
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos_of_pos hd0
  have hmCoarse : (Q.card : ℝ)/(8*Real.sqrt d) ≤ m :=
    hIcount.trans (Nat.cast_le.mpr hIm)
  have hm0 : (0 : ℝ) < m := (div_pos hQ0 (by positivity)).trans_le hmCoarse
  have hmNat : 0 < m := by exact_mod_cast hm0
  let w (I : Finset V) := Real.exp (-(δ*(shadowCount E I : ℝ)))
  let Z := ∑ I ∈ F,w I
  have hw (I : Finset V) : 0 < w I := Real.exp_pos _
  have hZ : 0 < Z := sum_pos (fun I hI => hw I) ⟨∅,hEmpty⟩
  have hEnerg : δ * (∑ I ∈ F,w I*(shadowCount E I : ℝ)) ≤ Z*Real.log F.card := by
    have hZero : shadowCount E (∅ : Finset V) = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heE,he0⟩ := mem_filter.mp he
      have hc := card_le_card he0
      rw [official_pair_card heE,card_empty] at hc
      omega
    have h := OMA.HypergraphWeights.energy_bound F (fun J => δ*(shadowCount E J : ℝ))
      ⟨∅,hEmpty,by simp [hZero]⟩
    change (∑ I ∈ F,w I*(δ*(shadowCount E I : ℝ))) ≤ Z*Real.log F.card at h
    rw [mul_sum]
    convert h using 1
    apply sum_congr rfl
    intro J hJ
    ring
  have hlogCount : Real.log F.card ≤ (m : ℝ)*(2*Real.log d) := by
    have h := OMA.HypergraphWeights.log_count_subsets Q F hmNat hmQ ⟨∅,hEmpty⟩
      (filter_subset _ _) hmMax
    have hRatio : (Q.card : ℝ)/m ≤ 8*Real.sqrt d := by
      apply (div_le_iff₀ hm0).mpr
      have hh := (div_le_iff₀ (show 0 < 8*Real.sqrt d by positivity)).mp hmCoarse
      nlinarith only [hh]
    have hAux := Real.log_le_log (div_pos hQ0 hm0) hRatio
    rw [Real.log_mul (by norm_num) hsqrt.ne',Real.sqrt_eq_rpow,Real.log_rpow hd0] at hAux
    have h3 : Real.log 8 ≤ 7 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hm0.le)
  have hEnerg' : (∑ I ∈ F,w I*(shadowCount E I : ℝ)) ≤ Z*(m : ℝ)*(2*δ*d) := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    calc
      _ ≤ Z*Real.log F.card := hEnerg
      _ ≤ Z*((m : ℝ)*(2*Real.log d)) := mul_le_mul_of_nonneg_left hlogCount hZ.le
      _ = _ := by rw [← hδsq]; ring
  have hSqrtLe : Real.sqrt d ≤ δ*d := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg d) (by positivity)).mp
    rw [Real.sq_sqrt hd0.le,mul_pow]
    have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)≤Real.log d by linarith) hd0.le
    nlinarith only [hh,hδsq, congrArg (fun x : ℝ => x*d) hδsq]
  have hLow : (Q.card : ℝ)*(Real.log d/64)*Z ≤
      ∑ I ∈ F,w I*(∑ v ∈ Q,vertexScore E d δ v I) := by
    rw [← (show (∑ _v ∈ Q,Real.log d/64*Z) = (Q.card : ℝ)*(Real.log d/64)*Z by
      rw [sum_const,nsmul_eq_mul]; ring)]
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_le_sum (fun v hv => by
      simpa only [neg_mul] using weighted_score_lower hU hL hTriangle d δ hd hδ.le hv)
  have hUp : (∑ I ∈ F,w I*(∑ v ∈ Q,vertexScore E d δ v I)) ≤
      Z*((Real.sqrt d+2*δ*d)*(m : ℝ)) + Z*(m : ℝ)*(2*δ*d) := by
    calc
      _ ≤ ∑ I ∈ F,w I*((Real.sqrt d+2*δ*d)*(m : ℝ) + shadowCount E I) := by
        apply sum_le_sum
        intro J hJ
        apply mul_le_mul_of_nonneg_left _ (hw J).le
        have hJQ := mem_powerset.mp (mem_filter.mp hJ).1
        apply (upper_score_sum hU hL d δ hδ.le hMax hJQ).trans
        exact add_le_add (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (hmMax J hJ)) (by positivity)) le_rfl
      _ = Z*((Real.sqrt d+2*δ*d)*(m : ℝ)) + ∑ I ∈ F,w I*(shadowCount E I : ℝ) := by
        simp_rw [mul_add]
        rw [sum_add_distrib,← sum_mul]
      _ ≤ _ := add_le_add le_rfl hEnerg'
  have hUpper : (Q.card : ℝ)*(Real.log d/64) ≤ 5*δ*d*(m : ℝ) := by
    apply (mul_le_mul_iff_left₀ hZ).mp
    have h := hLow.trans hUp
    have hs := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hSqrtLe hm0.le) hZ.le
    nlinarith only [h,hs]
  have hFinal : (Q.card : ℝ)*δ/320 ≤ m := by
    apply (mul_le_mul_iff_left₀ (mul_pos hδ hd0)).mp
    rw [← hδsq] at hUpper
    nlinarith only [hUpper]
  exact ⟨A,mem_powerset.mp hA.1,hA.2,hFinal⟩


end Vertices

end OMA.TripleSystem


namespace OMA.TripleSystem

open Finset
open scoped BigOperators

section Vertices

variable {V : Type*} [DecidableEq V]

theorem coarse_independent {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (d : ℝ) (hd : 1 ≤ d)
    (hAverage : 3*(E.card : ℝ) ≤ d*Q.card) :
    ∃ I ⊆ Q, independent E I ∧ (Q.card : ℝ)/(8*Real.sqrt d) ≤ I.card := by
  classical
  let s := Real.sqrt d
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s := Real.sqrt_pos_of_pos hd0
  have hs : s^2 = d := Real.sq_sqrt hd0.le
  have hs1 : 1 ≤ s := (sq_le_sq₀ (by norm_num : (0:ℝ)≤1) hs0.le).mp (by rw [hs]; simpa)
  let p := 1/(2*s)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hpD : d*p^2 = 1/4 := by
    rw [← hs]
    dsimp only [p]
    field_simp <;> norm_num
  have hAvgEdge : 24*(E.card : ℝ)*p^3 ≤ (3:ℝ)*((Q.card : ℝ)*p) := by
    calc
      _ = (3*(E.card : ℝ))*(8*p^3) := by ring
      _ ≤ (d*Q.card)*(8*p^3) := mul_le_mul_of_nonneg_right hAverage (by positivity)
      _ = 2*((Q.card : ℝ)*p) := by
        rw [show d*(Q.card : ℝ)*(8*p^3) = 8*(d*p^2)*((Q.card : ℝ)*p) by ring,hpD]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨U,hUQ,hUCount,hUEdge,-⟩ := OMA.SampleFinset.exists_sparse_sample Q E
    (∅ : Finset Unit) id (fun _ => ∅) 0 hU (by simp)
      p 3 hp.le hp1 (by norm_num) hAvgEdge (by simp [mul_nonneg (Nat.cast_nonneg _) hp.le])
  let F := E.filter (· ⊆ U)
  have hU' : uniformThree U F := by
    intro e he
    obtain ⟨heE,heU⟩ := mem_filter.mp he
    exact ⟨heU,(hU e heE).2⟩
  obtain ⟨I,hIU,hIF,hICount⟩ := independent_remove_edges hU'
  have hIE : independent E I := by
    intro e he hs
    exact hIF e (mem_filter.mpr ⟨he,hs.trans hIU⟩) hs
  have hc : (U.card : ℝ) ≤ I.card + F.card := by exact_mod_cast hICount
  change 6*(F.card : ℝ) ≤ 3*U.card at hUEdge
  refine ⟨I,hIU.trans hUQ,hIE,?_⟩
  have heq : (Q.card : ℝ)/(8*Real.sqrt d) = (Q.card : ℝ)*p/4 := by
    dsimp [p,s]
    ring
  rw [heq]
  linarith

theorem average_le_max {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (d : ℝ)
    (hMax : ∀ v ∈ Q, ((incidence E v).card : ℝ) ≤ d) :
    3*(E.card : ℝ) ≤ d*Q.card := by
  have hs : (∑ v ∈ Q, ((incidence E v).card : ℝ)) = 3*(E.card : ℝ) := by
    exact_mod_cast degree_sum hU
  rw [← hs]
  calc
    _ ≤ ∑ _v ∈ Q, d := sum_le_sum (fun v hv => hMax v hv)
    _ = _ := by rw [sum_const,nsmul_eq_mul,mul_comm]

end Vertices

end OMA.TripleSystem


namespace OMA.TripleSystem

open Finset
open scoped BigOperators

section Vertices

variable {V : Type*} [DecidableEq V]

noncomputable def edgeFor (E : Finset (Finset V)) (x y : V) : Finset V := by
  classical
  exact if h : ∃ e ∈ E, x ∈ e ∧ y ∈ e then h.choose else ∅

theorem edge_for_spec {E : Finset (Finset V)} {x y : V} (h : y ∈ neighbors E x) :
    edgeFor E x y ∈ E ∧ x ∈ edgeFor E x y ∧ y ∈ edgeFor E x y := by
  classical
  have ht := (mem_neighbors.mp h).2
  unfold edgeFor
  rw [dif_pos ht]
  exact ht.choose_spec

theorem edge_for_eq {E : Finset (Finset V)} (hL : linear E) {x y : V}
    (hne : x ≠ y) {e : Finset V} (he : e ∈ E) (hx : x ∈ e) (hy : y ∈ e) :
    edgeFor E x y = e := by
  have hF := edge_for_spec (mem_neighbors.mpr ⟨hne.symm,e,he,hx,hy⟩)
  by_contra! h
  have heF : 1 < (edgeFor E x y ∩ e).card := one_lt_card.mpr
    ⟨x,mem_inter.mpr ⟨hF.2.1,hx⟩,y,mem_inter.mpr ⟨hF.2.2,hy⟩,hne⟩
  exact heF.not_ge (hL _ hF.1 e he h)

def candidateCycles (Q : Finset V) (E : Finset (Finset V)) : Finset (V × V × V) :=
  Q.biUnion fun x => (neighbors E x ×ˢ neighbors E x).image (fun p => (x,p.1,p.2))

noncomputable def cycleLabels (Q : Finset V) (E : Finset (Finset V)) : Finset (V × V × V) :=
  (candidateCycles Q E).filter fun t => t.2.2 ∈ neighbors E t.2.1 ∧
    edgeFor E t.1 t.2.1 ≠ edgeFor E t.2.1 t.2.2 ∧
    edgeFor E t.2.1 t.2.2 ≠ edgeFor E t.2.2 t.1 ∧
    edgeFor E t.2.2 t.1 ≠ edgeFor E t.1 t.2.1

noncomputable def cycleVerts (E : Finset (Finset V)) (t : V × V × V) : Finset V :=
  edgeFor E t.1 t.2.1 ∪ edgeFor E t.2.1 t.2.2 ∪ edgeFor E t.2.2 t.1

private theorem mem_candidate {Q : Finset V} {E : Finset (Finset V)} {x y z : V} :
    (x,y,z) ∈ candidateCycles Q E ↔ x ∈ Q ∧ y ∈ neighbors E x ∧ z ∈ neighbors E x := by
  simp [candidateCycles]

theorem number_of_cycles {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (D : ℝ) (hD : 0 ≤ D)
    (hMax : ∀ x ∈ Q, ((incidence E x).card : ℝ) ≤ D) :
    ((cycleLabels Q E).card : ℝ) ≤ 4*D^2*Q.card := by
  classical
  have hNat : (cycleLabels Q E).card ≤ ∑ x ∈ Q,(neighbors E x).card^2 := by
    apply (card_filter_le _ _).trans
    unfold candidateCycles
    refine card_biUnion_le.trans ?_
    apply sum_le_sum
    intro x hx
    refine card_image_le.trans_eq ?_
    rw [card_product,pow_two]
  have hCast := (Nat.cast_le (α:=ℝ)).mpr hNat
  simp only [Nat.cast_sum,Nat.cast_pow] at hCast
  apply hCast.trans
  calc
    _ ≤ ∑ _x ∈ Q,(2*D)^2 := by
      apply sum_le_sum
      intro x hx
      apply pow_le_pow_left₀ (by positivity)
      rw [neighbor_card hU hL,Nat.cast_mul,Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left (hMax x hx) (by norm_num)
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

private theorem intersection_singleton {E : Finset (Finset V)} (hL : linear E)
    {e f : Finset V} (he : e ∈ E) (hf : f ∈ E) (hne : e ≠ f)
    {x : V} (hx : x ∈ e) (hx' : x ∈ f) : e ∩ f = {x} := by
  symm
  apply eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨hx,hx'⟩))
  simpa using hL e he f hf hne

theorem cycle_vertices {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) {t : V × V × V} (ht : t ∈ cycleLabels Q E) :
    cycleVerts E t ⊆ Q ∧ (cycleVerts E t).card = 6 := by
  classical
  rcases t with ⟨x,y,z⟩
  obtain ⟨hbase,hyz,hef,hfg,hge⟩ := mem_filter.mp ht
  obtain ⟨hx,hy,hz⟩ := mem_candidate.mp hbase
  let e := edgeFor E x y
  let f := edgeFor E y z
  let g := edgeFor E z x
  have he : e ∈ E ∧ x ∈ e ∧ y ∈ e := edge_for_spec hy
  have hf : f ∈ E ∧ y ∈ f ∧ z ∈ f := edge_for_spec hyz
  have hg : g ∈ E ∧ z ∈ g ∧ x ∈ g := edge_for_spec (neighbor_symmetric.mp hz)
  have hef' : e∩f = {y} := intersection_singleton hL he.1 hf.1 hef he.2.2 hf.2.1
  have hfg' : f∩g = {z} := intersection_singleton hL hf.1 hg.1 hfg hf.2.2 hg.2.1
  have heg' : e∩g = {x} := intersection_singleton hL he.1 hg.1 hge.symm he.2.1 hg.2.2
  have hxz : x ≠ z := (mem_neighbors.mp hz).1.symm
  change (e∪f∪g) ⊆ Q ∧ (e∪f∪g).card = 6
  refine ⟨union_subset (union_subset (hU e he.1).1 (hU f hf.1).1) (hU g hg.1).1,?_⟩
  have hC := card_union_add_card_inter e f
  rw [hef',card_singleton,(hU e he.1).2,(hU f hf.1).2] at hC
  have hCg := card_union_add_card_inter (e∪f) g
  rw [union_inter_distrib_right,heg',hfg',(hU g hg.1).2] at hCg
  have h2 : (({x} : Finset V) ∪ {z}).card = 2 := by simp [hxz]
  rw [h2] at hCg
  omega

private theorem cover_cycle {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) {e f g : Finset V}
    (he : e ∈ E) (hf : f ∈ E) (hg : g ∈ E)
    (hef : e ≠ f) (hfg : f ≠ g) (hge : g ≠ e)
    {x y z : V} (hx : x ∈ e∩f) (hy : y ∈ f∩g) (hz : z ∈ g∩e)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    (x,y,z) ∈ cycleLabels Q E ∧ cycleVerts E (x,y,z) = f∪g∪e := by
  have hxQ := (hU e he).1 (mem_inter.mp hx).1
  have hey : edgeFor E x y = f := edge_for_eq hL hxy hf (mem_inter.mp hx).2 (mem_inter.mp hy).1
  have hgz : edgeFor E y z = g := edge_for_eq hL hyz hg (mem_inter.mp hy).2 (mem_inter.mp hz).1
  have hezx : edgeFor E z x = e := edge_for_eq hL hzx he (mem_inter.mp hz).2 (mem_inter.mp hx).1
  constructor
  · apply mem_filter.mpr
    refine ⟨mem_candidate.mpr ⟨hxQ,?_,?_⟩,?_,?_,?_,?_⟩
    · exact mem_neighbors.mpr ⟨hxy.symm,f,hf,(mem_inter.mp hx).2,(mem_inter.mp hy).1⟩
    · exact mem_neighbors.mpr ⟨hzx,e,he,(mem_inter.mp hx).1,(mem_inter.mp hz).2⟩
    · exact mem_neighbors.mpr ⟨hyz.symm,g,hg,(mem_inter.mp hy).2,(mem_inter.mp hz).1⟩
    · simpa only [hey,hgz] using hfg
    · simpa only [hgz,hezx] using hge
    · simpa only [hezx,hey] using hef
  · simp only [cycleVerts,hey,hgz,hezx]

theorem delete_cycles {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E)
    (U : Finset V) (hUQ : U ⊆ Q)
    (hFew : 2*((cycleLabels Q E).filter (fun t => cycleVerts E t ⊆ U)).card ≤ U.card) :
    ∃ W ⊆ U, U.card ≤ 2*W.card ∧ triangleFree (E.filter (· ⊆ W)) := by
  classical
  let X := (cycleLabels Q E).filter (fun t => cycleVerts E t ⊆ U)
  have hx (t : X) : ∃ x, x ∈ cycleVerts E t.val :=
    card_pos.mp (by rw [(cycle_vertices hU hL (mem_filter.mp t.property).1).2]; decide)
  choose drop hdrop using hx
  let R : Finset V := univ.image drop
  have hRU : R ⊆ U := by
    intro x hxR
    obtain ⟨t,_,rfl⟩ := mem_image.mp hxR
    exact (mem_filter.mp t.property).2 (hdrop t)
  have hR : R.card ≤ X.card := by simpa [R] using card_image_le (f:=drop) (s:=(univ : Finset X))
  refine ⟨U\R,sdiff_subset,?_,?_⟩
  · have h := card_sdiff_of_subset hRU
    change 2*X.card ≤ U.card at hFew
    omega
  · intro e he f hf g hg hef hfg hge x hx y hy z hz hxy hyz hzx
    have he' := mem_filter.mp he
    have hf' := mem_filter.mp hf
    have hg' := mem_filter.mp hg
    obtain ⟨hmem,heq⟩ := cover_cycle hU hL he'.1 hf'.1 hg'.1 hef hfg hge hx hy hz hxy hyz hzx
    have hsub : cycleVerts E (x,y,z) ⊆ U\R := by
      rw [heq]
      exact union_subset (union_subset hf'.2 hg'.2) he'.2
    let t : X := ⟨(x,y,z),mem_filter.mpr ⟨hmem,hsub.trans sdiff_subset⟩⟩
    have hr : drop t ∈ R := mem_image.mpr ⟨t,mem_univ _,rfl⟩
    exact (mem_sdiff.mp (hsub (hdrop t))).2 hr

end Vertices

end OMA.TripleSystem


namespace OMA.TripleSystem

open Finset

section Vertices

variable {V : Type*} [DecidableEq V]

private theorem induced_uniform {Q W : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) : uniformThree W (E.filter (· ⊆ W)) := by
  intro e he
  exact ⟨(mem_filter.mp he).2,(hU e (mem_filter.mp he).1).2⟩

private theorem induced_linear {W : Finset V} {E : Finset (Finset V)}
    (hL : linear E) : linear (E.filter (· ⊆ W)) := by
  intro e he f hf hne
  exact hL e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hne

private theorem induced_triangleFree {W : Finset V} {E : Finset (Finset V)}
    (hT : triangleFree E) : triangleFree (E.filter (· ⊆ W)) := by
  intro e he f hf g hg
  exact hT e (mem_filter.mp he).1 f (mem_filter.mp hf).1 g (mem_filter.mp hg).1

private theorem independent_from_induced {I W : Finset V} {E : Finset (Finset V)}
    (hIW : I ⊆ W) (hI : independent (E.filter (· ⊆ W)) I) : independent E I := by
  intro e he hIe
  exact hI e (mem_filter.mpr ⟨he,hIe.trans hIW⟩) hIe

private theorem induced_average {W : Finset V} {E : Finset (Finset V)}
    (d : ℝ) (hd : 0 ≤ d) {U : Finset V} (hWU : W ⊆ U)
    (hSize : U.card ≤ 2*W.card)
    (hAvg : 6*((E.filter (· ⊆ U)).card : ℝ) ≤ d*U.card) :
    3*((E.filter (· ⊆ W)).card : ℝ) ≤ d*W.card := by
  have hSub : E.filter (· ⊆ W) ⊆ E.filter (· ⊆ U) := by
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.trans hWU⟩
  have hC : ((E.filter (· ⊆ W)).card : ℝ) ≤ (E.filter (· ⊆ U)).card :=
    Nat.cast_le.mpr (card_le_card hSub)
  have hS : (U.card : ℝ) ≤ 2*W.card := by exact_mod_cast hSize
  linarith [mul_le_mul_of_nonneg_left hS hd]

/-- A linear three-uniform hypergraph has an independent set of logarithmic size
relative to the inverse square root of its average degree. -/
theorem linear_logarithmic_bound {Q : Finset V} {E : Finset (Finset V)}
    (hU : uniformThree Q E) (hL : linear E) (d : ℝ) (hd : 2 ≤ d)
    (hAvg : 3*(E.card : ℝ) ≤ d*Q.card) :
    ∃ I ⊆ Q, independent E I ∧
      (1/200000 : ℝ)*Q.card*Real.sqrt (Real.log d/d) ≤ I.card := by
  classical
  have hd0 : 0 < d := by linarith
  have hd1 : 1 ≤ d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  let D := 2*d
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hDd : d ≤ D := by dsimp [D]; linarith
  have hgrow := Real.log_le_log hd0 hDd
  by_cases hLarge : Real.exp 100 ≤ D
  swap
  · have hlog : Real.log d ≤ 100 := by
      have h := Real.log_lt_log hD0 (lt_of_not_ge hLarge)
      rw [Real.log_exp] at h
      linarith
    obtain ⟨I,hIQ,hI,hCount⟩ := coarse_independent hU d hd1 hAvg
    refine ⟨I,hIQ,hI,?_⟩
    apply le_trans ?_ hCount
    rw [Real.sqrt_div hlogd]
    have hSqrt := Real.sqrt_le_sqrt hlog
    norm_num at hSqrt
    have hs : 0 < Real.sqrt d := Real.sqrt_pos_of_pos hd0
    have hmul : (Q.card : ℝ)*Real.sqrt (Real.log d) ≤ 10*Q.card := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hSqrt (Nat.cast_nonneg Q.card)
    apply (le_div_iff₀ (show 0 < 8*Real.sqrt d by positivity)).mpr
    field_simp
    nlinarith
  have hLogD : 100 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 100) hLarge
    rwa [Real.log_exp] at h
  let p := D ^ (-(5/12) : ℝ)
  have hp : 0 < p := Real.rpow_pos_of_pos hD0 _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hd1.trans hDd) (by norm_num)
  let B := 8*D*p^2
  have hB : 0 < B := by dsimp [B]; positivity
  have hpPow (k : ℕ) : p^k = D ^ (-(5/12) * (k : ℝ)) := by
    rw [Real.rpow_mul hD0.le,Real.rpow_natCast]
  have hFive : D^2*p^5 = D ^ (-(1/12) : ℝ) := by
    rw [hpPow,← Real.rpow_natCast D 2,← Real.rpow_add hD0]
    congr 1
    norm_num
  have hSmall : 32*D^2*p^5 ≤ 1 := by
    have h32 : Real.log 32 ≤ 5 := by
      rw [show (32 : ℝ) = 2^5 by norm_num,Real.log_pow]
      have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
      norm_num at h ⊢
      linarith
    rw [show 32*D^2*p^5 = 32*(D^2*p^5) by ring,hFive,
      Real.rpow_def_of_pos hD0,← Real.exp_log (show 0 < (32 : ℝ) by norm_num),← Real.exp_add]
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  obtain ⟨Q₀,hQ₀Q,hQ₀,hMax₀⟩ := remove_high_degree hU d hd0 hAvg
  let E₀ := E.filter (· ⊆ Q₀)
  have hU₀ : uniformThree Q₀ E₀ := induced_uniform hU
  have hL₀ : linear E₀ := induced_linear hL
  have hAvg₀ := average_le_max hU₀ D hMax₀
  have hEdges : 24*(E₀.card : ℝ)*p^3 ≤ B*((Q₀.card : ℝ)*p) := by
    calc
      _ = (3*(E₀.card : ℝ))*(8*p^3) := by ring
      _ ≤ (D*Q₀.card)*(8*p^3) := mul_le_mul_of_nonneg_right hAvg₀ (by positivity)
      _ = _ := by dsimp [B]; ring
  have hCycles : 8*((cycleLabels Q₀ E₀).card : ℝ)*p^6 ≤ (Q₀.card : ℝ)*p := by
    have hc := number_of_cycles hU₀ hL₀ D hD0.le hMax₀
    calc
      _ = ((cycleLabels Q₀ E₀).card : ℝ)*(8*p^6) := by ring
      _ ≤ (4*D^2*Q₀.card)*(8*p^6) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (32*D^2*p^5)*((Q₀.card : ℝ)*p) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hSmall (show 0 ≤ (Q₀.card : ℝ)*p by positivity)
  obtain ⟨U,hUQ₀,hSizeU,hUE,hUX⟩ := OMA.SampleFinset.exists_sparse_sample Q₀ E₀
    (cycleLabels Q₀ E₀) id (cycleVerts E₀) 6 hU₀
    (fun _ h => cycle_vertices hU₀ hL₀ h) p B hp.le hp1 hB hEdges hCycles
  obtain ⟨W,hWU,hSizeW,hWT⟩ := delete_cycles hU₀ hL₀ U hUQ₀ hUX
  let E₁ := E₀.filter (· ⊆ W)
  have hU₁ : uniformThree W E₁ := induced_uniform hU₀
  have hL₁ : linear E₁ := induced_linear hL₀
  have hAvg₁ : 3*(E₁.card : ℝ) ≤ B*W.card := induced_average B hB.le hWU hSizeW hUE
  obtain ⟨K,hKW,hSizeK,hMax₂⟩ := remove_high_degree hU₁ B hB hAvg₁
  let E₂ := E₁.filter (· ⊆ K)
  let D' := 2*B
  have hD' : 0 < D' := by dsimp [D']; positivity
  have hU₂ : uniformThree K E₂ := induced_uniform hU₁
  have hL₂ : linear E₂ := induced_linear hL₁
  have hT₂ : triangleFree E₂ := induced_triangleFree hWT
  have hD'Formula : D' = 16*(D ^ (1/6 : ℝ)) := by
    have hBase : D*p^2 = D ^ (1/6 : ℝ) := by
      rw [hpPow]
      nth_rw 1 [← Real.rpow_one D]
      rw [← Real.rpow_add hD0]
      congr 1
      norm_num
    calc
      D' = 16*(D*p^2) := by dsimp [D',B]; ring
      _ = _ := by rw [hBase]
  have hLogD' : Real.log D/6 ≤ Real.log D' := by
    rw [hD'Formula,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hD0 _).ne',
      Real.log_rpow hD0]
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 16 by norm_num)
    linarith
  have hLarge' : Real.exp 8 ≤ D' := by
    apply (Real.log_le_log_iff (Real.exp_pos 8) hD').mp
    rw [Real.log_exp]
    linarith
  have hAvg₂ := average_le_max hU₂ D' hMax₂
  have hD'1 : 1 ≤ D' := by
    apply (Real.log_le_log_iff (by norm_num : (0:ℝ)<1) hD').mp
    rw [Real.log_one]
    linarith
  obtain ⟨I,hIK,hI,hSizeI⟩ := independent_logarithmic_locally
    hU₂ hL₂ hT₂ D' hLarge' hMax₂ (coarse_independent hU₂ D' hD'1 hAvg₂)
  have hIW := hIK.trans hKW
  have hIQ₀ := hIW.trans (hWU.trans hUQ₀)
  refine ⟨I,hIQ₀.trans hQ₀Q,
    independent_from_induced hIQ₀ (independent_from_induced hIW (independent_from_induced hIK hI)),?_⟩
  have hK : (Q.card : ℝ)*p/16 ≤ K.card := by
    have h₀ : (Q.card : ℝ) ≤ 2*Q₀.card := by exact_mod_cast hQ₀
    have hW : (U.card : ℝ) ≤ 2*W.card := by exact_mod_cast hSizeW
    have hK' : (W.card : ℝ) ≤ 2*K.card := by exact_mod_cast hSizeK
    linarith [mul_le_mul_of_nonneg_right h₀ hp.le]
  have hLogD'0 : 0 ≤ Real.log D' := by linarith
  have hSquare : (p*Real.sqrt (Real.log D'/D'))^2 = Real.log D'/(32*d) := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    have hf : D'=32*d*p^2 := by dsimp [D',B,D]; ring
    rw [hf]
    field_simp
  have hCompare : Real.sqrt (Real.log d/d)/24 ≤ p*Real.sqrt (Real.log D'/D') := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow,Real.sq_sqrt (by positivity),hSquare]
    field_simp
    linarith
  refine le_trans ?_ hSizeI
  have hk := mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg (Real.log D'/D'))
  have hc := mul_le_mul_of_nonneg_left hCompare (Nat.cast_nonneg (α:=ℝ) Q.card)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) Q.card) (Real.sqrt_nonneg (Real.log d/d))]

end Vertices

end OMA.TripleSystem

private theorem erdos507_h2_proof : OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1.H2 := by
  refine ⟨1/200000, by norm_num, ?_⟩
  intro V inst S E d hd hU hL hAvg
  exact OMA.TripleSystem.linear_logarithmic_bound hU hL d hd hAvg

end H2Part

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.lower_kps82 :=
  OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1.main
    OMA.HeilbronnSampleApplication.successful_sampling
    erdos507_h2_proof
