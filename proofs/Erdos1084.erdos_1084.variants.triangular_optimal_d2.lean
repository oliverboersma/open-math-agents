import FormalConjectures.ErdosProblems.«1084»
import Mathlib

/-!
# Erdős Problem 1084 — Triangular Lattice Optimality in `ℝ²` (Harborth's Theorem)

For every `n : ℕ`, the maximum number of unit distances in a 1-separated subset of `ℝ²`
of size `3n² + 3n + 1` is `9n² + 3n`, achieved by the regular hexagonal patch of the
triangular lattice.

Credits:
- Reduction `R1` (`OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1`): `@marcusbuffett`.
- Hexagonal patch cardinality (`H1`): `@ivillar`.
- Hexagonal patch contact count (`H2`, `OMA.HexagonalPatchContacts`): merged proof in repository.
- Unit-circle chord gap lemma (`chord_gap`): adapted from `PackingDeficit` in
  `Erdos1084.erdos_1084.variants.upper_d2`.
- Harborth's inequality (`H3`, `Erdos1084Harborth.harborth`): elementary self-contained proof via
  generic rotation, parallelogram-law non-crossing of unit edges, vertical slab trapezoidation
  paired with the geometric rotation system (spanning-tree-to-`G` squeeze induction for Euler's
  formula and face-component bijection), turning-number telescoping on the outer face, and
  strong induction on `|S|`.
-/

namespace OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

open scoped EuclideanGeometry
open Finset

-- Count integer coordinates in the three strips defining the regular hexagon.
def H1 : Prop :=
  ∀ n : ℕ, let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
    patch.card = 3*n^2 + 3*n + 1

-- Count the nearest-neighbour contacts in the same patch.
def H2 : Prop :=
  ∀ n : ℕ, let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
    let point (p : ℤ × ℤ) : ℝ² :=
      !₂[(p.1 : ℝ) + (p.2 : ℝ)/2, Real.sqrt 3 * (p.2 : ℝ)/2]
    9*n^2 + 3*n ≤ unitDistNum (patch.image point)

-- Harborth's squared deficit inequality for planar contact graphs.
def H3 : Prop :=
  ∀ S : Finset ℝ², Metric.IsSeparated' 1 (S : Set ℝ²) →
    12*S.card ≤ (3*S.card - unitDistNum S)^2 + 3

-- The lattice norm estimate follows the hexagonal lattice argument in
-- the repository's proof of the hexagonal lower bound for Erdős 232.
lemma int_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : (4 : ℤ) ≤ (2 * x + y) ^ 2 + 3 * y ^ 2 := by
  have hsq : ∀ n : ℤ, n ≠ 0 → (1 : ℤ) ≤ n ^ 2 := by
    intro n hn
    by_cases h1 : (1 : ℤ) ≤ n
    · nlinarith
    · have h2 : n ≤ -1 := by omega
      nlinarith
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simp only [add_zero]
    rcases h with hx | hx
    · have := hsq x hx
      nlinarith
    · exact absurd rfl hx
  · have hy1 := hsq y hy
    rcases eq_or_ne (2 * x + y) 0 with hm | hm
    · have hx0 : x ≠ 0 := by rintro rfl; omega
      have hx1 := hsq x hx0
      have hyy : y = -2 * x := by omega
      rw [hyy]
      nlinarith
    · have hm1 := hsq (2 * x + y) hm
      nlinarith

lemma real_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (4 : ℝ) ≤ (2 * (x : ℝ) + (y : ℝ)) ^ 2 + 3 * (y : ℝ) ^ 2 := by
  have h' := int_key x y h
  have h'' : ((4 : ℤ) : ℝ) ≤ (((2 * x + y) ^ 2 + 3 * y ^ 2 : ℤ) : ℝ) := by exact_mod_cast h'
  push_cast at h''
  linarith


lemma lattice_sep (p q : ℤ × ℤ) (hne : p ≠ q) :
    let point (r : ℤ × ℤ) : ℝ² :=
      !₂[(r.1 : ℝ) + (r.2 : ℝ)/2, Real.sqrt 3 * (r.2 : ℝ)/2]
    1 ≤ dist (point p) (point q) := by
  intro point
  have hd : p.1-q.1 ≠ 0 ∨ p.2-q.2 ≠ 0 := by
    by_contra! h
    exact hne (Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2))
  have h := real_key _ _ hd
  push_cast at h
  have hid : 4 * ‖point p - point q‖^2 =
      (2*((p.1 : ℝ)-q.1) + ((p.2 : ℝ)-q.2))^2 + 3*((p.2 : ℝ)-q.2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change 4 * (((p.1 : ℝ) + p.2/2 - (q.1 + q.2/2))^2 +
      (Real.sqrt 3*p.2/2 - Real.sqrt 3*q.2/2)^2) = _
    ring_nf
    norm_num [Real.sq_sqrt] <;> ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (point p - point q)]

theorem main : H1 → H2 → H3 → type_of% @Erdos1084.erdos_1084.variants.triangular_optimal_d2 := by
  classical
  intro count contacts bound n
  let N := 3*n^2 + 3*n + 1
  let target := 9*n^2 + 3*n
  have upper (S : Finset ℝ²) (hs : S.card = N)
      (hsep : Metric.IsSeparated' 1 (S : Set ℝ²)) : unitDistNum S ≤ target := by
    have h := bound S hsep
    rw [hs] at h
    have hdef : 6*n + 3 ≤ 3*N - unitDistNum S := by
      by_contra! hsmall
      have hle : 3*N - unitDistNum S ≤ 6*n+2 := by omega
      have hh := Nat.pow_le_pow_left hle 2
      dsimp [N] at h
      nlinarith
    dsimp [N,target] at *
    omega
  apply le_antisymm
  · exact ciSup_le' fun S => ciSup_le' fun hs => ciSup_le' fun hsep => upper S hs hsep
  let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
  let point (p : ℤ × ℤ) : ℝ² :=
    !₂[(p.1 : ℝ) + (p.2 : ℝ)/2, Real.sqrt 3 * (p.2 : ℝ)/2]
  let S := patch.image point
  have inj : Function.Injective point := by
    intro p q he
    by_contra h
    have hh := lattice_sep p q h
    change 1 ≤ dist (point p) (point q) at hh
    rw [he, dist_self] at hh
    norm_num at hh
  have hs : S.card = N := (Finset.card_image_of_injective _ inj).trans (count n)
  have hsep : Metric.IsSeparated' 1 (S : Set ℝ²) := by
    intro x hx y hy hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    have hd : 1 ≤ dist (point p) (point q) := lattice_sep p q (fun he => hne (congrArg point he))
    simpa only [ENNReal.ofReal_one, ← edist_dist] using ENNReal.ofReal_le_ofReal hd
  change target ≤ ⨆ (T : Finset ℝ²) (_ : T.card = N) (_ : Metric.IsSeparated' 1 (T : Set ℝ²)), unitDistNum T
  refine le_ciSup_of_le ?_ S ?_
  · refine ⟨target, ?_⟩
    rintro _ ⟨T,rfl⟩
    exact ciSup_le' fun h => ciSup_le' fun h' => upper T h h'
  apply le_ciSup_of_le (Set.finite_range _).bddAbove hs
  apply le_ciSup_of_le (Set.finite_range _).bddAbove hsep
  exact contacts n

end OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

namespace OMA.HexagonalPatchCount

open Finset

private lemma fiber_card (n : ℕ) (y : ℤ) (hy : y ∈ Icc (-(n:ℤ)) n) :
    (((Icc (-(n:ℤ)) n).filter (fun x => x + y ∈ Icc (-(n:ℤ)) n)).card : ℤ) = 2*n+1 - |y| := by
  have e : (Icc (-(n:ℤ)) n).filter (fun x => x + y ∈ Icc (-(n:ℤ)) n) =
      Icc (max (-(n:ℤ)) (-n - y)) (min (n:ℤ) (n - y)) := by
    ext x; simp only [mem_filter, mem_Icc, max_le_iff, le_min_iff]; omega
  rw [e, Int.card_Icc]
  simp only [mem_Icc] at hy
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_nonpos h]; omega

private lemma abs_sum (n : ℕ) : ∑ y ∈ Icc (-(n:ℤ)) n, |y| = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e : Icc (-((k+1 : ℕ):ℤ)) ((k+1 : ℕ):ℤ) =
        insert (-((k:ℤ)+1)) (insert ((k:ℤ)+1) (Icc (-(k:ℤ)) k)) := by
      ext x; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [e, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih]
    rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
    push_cast; ring

theorem patch_card : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H1 := by
  intro n interval patch
  have hc : (patch.card : ℤ) = ∑ y ∈ interval, (((interval.filter (fun x => x + y ∈ interval)).card : ℕ) : ℤ) := by
    have : patch.card = ∑ y ∈ interval, (interval.filter (fun x => x + y ∈ interval)).card := by
      simp only [patch, card_filter]
      rw [sum_product_right]
    rw [this]; push_cast; rfl
  have hs : ∑ y ∈ interval, (((interval.filter (fun x => x + y ∈ interval)).card : ℕ) : ℤ) =
      ∑ y ∈ interval, ((2*n+1 : ℤ) - |y|) := by
    apply sum_congr rfl
    intro y hy
    exact fiber_card n y hy
  rw [hs, sum_sub_distrib, abs_sum, sum_const] at hc
  simp only [interval, Int.card_Icc, nsmul_eq_mul] at hc
  have h2 : ((n:ℤ) + 1 - -(n:ℤ)).toNat = 2*n+1 := by omega
  rw [h2] at hc
  push_cast at hc
  have : (patch.card : ℤ) = ((3*n^2+3*n+1 : ℕ) : ℤ) := by rw [hc]; push_cast; ring
  exact_mod_cast this

end OMA.HexagonalPatchCount

namespace OMA.HexagonalPatchContacts

open Finset

private def upperCornerEquiv (n : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (n - p.2, p.1)
  invFun p := (p.2, n - p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def oppositeEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (-p.1, -p.2)
  invFun p := (-p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private theorem card_patch (n : ℕ) :
    let I := Icc (-(n : ℤ)) (n : ℤ)
    ((I ×ˢ I).filter (fun p => p.1 + p.2 ∈ I)).card = 3 * n^2 + 3 * n + 1 := by
  classical
  let I := Icc (-(n : ℤ)) (n : ℤ)
  let J := Icc (0 : ℤ) (n : ℤ)
  let box := I ×ˢ I
  let upper := box.filter fun p => (n : ℤ) < p.1 + p.2
  let lower := box.filter fun p => p.1 + p.2 < -(n : ℤ)
  let patch := box.filter fun p => p.1 + p.2 ∈ I
  change patch.card = _
  have hI : I.card = 2 * n + 1 := by
    simp only [I, Int.card_Icc]
    omega
  have hJ : J.card = n + 1 := by
    simp only [J, Int.card_Icc]
    omega
  have hu : upper.card = (n + 1).choose 2 := by
    calc
      upper.card = ((J ×ˢ J).filter fun p => p.1 < p.2).card := by
        apply card_equiv (upperCornerEquiv (n : ℤ))
        rintro ⟨x, y⟩
        simp only [upper, box, I, J, mem_filter, mem_product, mem_Icc,
          upperCornerEquiv, Equiv.coe_fn_mk]
        omega
      _ = (n + 1).choose 2 := by rw [card_product_filter_lt, hJ]
  have hl : lower.card = upper.card := by
    apply card_equiv oppositeEquiv
    rintro ⟨x, y⟩
    simp only [lower, upper, box, I, mem_filter, mem_product, mem_Icc,
      oppositeEquiv, Equiv.coe_fn_mk]
    omega
  have hmiss : (box.filter fun p => p.1 + p.2 ∉ I) = upper ∪ lower := by
    ext p
    by_cases hp : p ∈ box
    · simp only [upper, lower, mem_union, mem_filter, hp, true_and, I, mem_Icc]
      omega
    · simp [upper, lower, hp]
  have hdisj : Disjoint upper lower := by
    refine disjoint_left.mpr ?_
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    omega
  have hpart := card_filter_add_card_filter_not (s := box) (fun p => p.1 + p.2 ∈ I)
  change patch.card + _ = _ at hpart
  rw [hmiss, card_union_of_disjoint hdisj, hl, hu] at hpart
  have hbox : box.card = (2 * n + 1)^2 := by
    dsimp [box]
    rw [card_product, hI, pow_two]
  rw [hbox] at hpart
  have hchoose : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (n + 1))]
    simp
  nlinarith only [hpart, hchoose]


open scoped EuclideanGeometry
open OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1 (lattice_sep)

private def interval (n : ℕ) : Finset ℤ := Icc (-(n : ℤ)) (n : ℤ)

private def patch (n : ℕ) : Finset (ℤ × ℤ) :=
  (interval n ×ˢ interval n).filter fun p => p.1 + p.2 ∈ interval n

private theorem mem_patch (n : ℕ) (p : ℤ × ℤ) :
    p ∈ patch n ↔ -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n ∧
      -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n ∧ -(n : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ n := by
  simp [patch, interval, and_assoc]

private def step (d : Fin 3) : ℤ × ℤ := ![(1, 0), (0, 1), (1, -1)] d

private def good (n : ℕ) (d : Fin 3) : Finset (ℤ × ℤ) :=
  (patch n).filter fun p => p + step d ∈ patch n

private def rightBorder (n : ℕ) : Finset (ℤ × ℤ) :=
  (patch n).filter fun p => p + step 0 ∉ patch n

private theorem mem_rightBorder (n : ℕ) (p : ℤ × ℤ) :
    p ∈ rightBorder n ↔ p.2 ∈ interval n ∧ p.1 = min (n : ℤ) (n - p.2) := by
  simp only [rightBorder, step, mem_filter, mem_patch, interval, mem_Icc, Prod.fst_add,
    Prod.snd_add, Matrix.cons_val_zero, add_zero]
  rcases le_total (0 : ℤ) p.2 with h | h
  · rw [min_eq_right (by omega)]
    omega
  · rw [min_eq_left (by omega)]
    omega

private theorem card_rightBorder (n : ℕ) : (rightBorder n).card = 2 * n + 1 := by
  let endpoint : ℤ ↪ (ℤ × ℤ) :=
    ⟨fun y => (min (n : ℤ) (n - y), y), fun _ _ h => congrArg Prod.snd h⟩
  have hborder : rightBorder n = (interval n).map endpoint := by
    ext p
    rw [mem_rightBorder, mem_map]
    constructor
    · rintro ⟨h, hx⟩
      exact ⟨p.2, h, Prod.ext hx.symm rfl⟩
    · rintro ⟨y, h, rfl⟩
      exact ⟨h, rfl⟩
  rw [hborder, card_map, interval, Int.card_Icc]
  omega

private def swapCoords : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.prodComm ℤ ℤ

private def diagonalCoords : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1, -p.1 - p.2)
  invFun p := (p.1, -p.1 - p.2)
  left_inv p := Prod.ext rfl (by change -p.1 - (-p.1 - p.2) = p.2; omega)
  right_inv p := Prod.ext rfl (by change -p.1 - (-p.1 - p.2) = p.2; omega)

private theorem card_good (n : ℕ) (d : Fin 3) : (good n d).card = 3 * n^2 + n := by
  have hcount := card_patch n
  change (patch n).card = _ at hcount
  have hsplit := card_filter_add_card_filter_not (s := patch n) (fun p => p + step 0 ∈ patch n)
  change (good n 0).card + (rightBorder n).card = (patch n).card at hsplit
  rw [card_rightBorder, hcount] at hsplit
  have hhorizontal : (good n 0).card = 3 * n^2 + n := by omega
  have hvert : (good n 0).card = (good n 1).card := by
    apply card_equiv swapCoords
    intro p
    simp [good, swapCoords, mem_patch, step]
    omega
  have hdiag : (good n 0).card = (good n 2).card := by
    apply card_equiv diagonalCoords
    intro p
    simp [good, diagonalCoords, mem_patch, step]
    omega
  fin_cases d
  · exact hhorizontal
  · exact hvert.symm.trans hhorizontal
  · exact hdiag.symm.trans hhorizontal

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, Real.sqrt 3 * (p.2 : ℝ) / 2]

private theorem point_injective : Function.Injective point := by
  intro p q h
  by_contra hne
  have hsep := lattice_sep p q hne
  change 1 ≤ dist (point p) (point q) at hsep
  rw [h, dist_self] at hsep
  norm_num at hsep

private theorem dist_step (p : ℤ × ℤ) (d : Fin 3) : dist (point p) (point (p + step d)) = 1 := by
  rw [dist_eq_norm]
  have hsq : ‖point p - point (p + step d)‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change ((p.1 : ℝ) + (p.2 : ℝ) / 2 - (((p + step d).1 : ℝ) + ((p + step d).2 : ℝ) / 2))^2 +
      (Real.sqrt 3 * (p.2 : ℝ) / 2 - Real.sqrt 3 * ((p + step d).2 : ℝ) / 2)^2 = 1
    fin_cases d <;> simp [step] <;> ring_nf <;> norm_num [Real.sq_sqrt]
  nlinarith [norm_nonneg (point p - point (p + step d))]

private theorem step_injective : Function.Injective step := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [step]

private theorem steps_not_opposite (i j : Fin 3) : step i + step j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [step, Prod.ext_iff]

private noncomputable def edge (e : Σ _ : Fin 3, ℤ × ℤ) : Sym2 ℝ² :=
  s(point e.2, point (e.2 + step e.1))

private theorem edge_injective : Function.Injective edge := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain rfl := point_injective h₁
    obtain rfl := step_injective (add_left_cancel (point_injective h₂))
    rfl
  · have h₁' := point_injective h₁
    have h₂' := point_injective h₂
    have hsum : q + (step j + step i) = q + 0 := by
      rw [← add_assoc, ← h₁', h₂', add_zero]
    exact (steps_not_opposite j i (add_left_cancel hsum)).elim

private theorem out_dist (a b : ℝ²) : dist (s(a,b)).out.1 (s(a,b)).out.2 = dist a b := by
  have h : s((s(a,b)).out.1, (s(a,b)).out.2) = s(a,b) := (s(a,b)).out_eq
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, dist_comm]

theorem contacts (n : ℕ) : 9 * n^2 + 3 * n ≤ unitDistNum ((patch n).image point) := by
  classical
  let oriented := (univ : Finset (Fin 3)).sigma (good n)
  have hcard : oriented.card = 9 * n^2 + 3 * n := by
    simp [oriented, card_sigma, card_good]
    ring
  rw [← hcard, ← card_image_of_injective oriented edge_injective, unitDistNum]
  apply card_le_card
  intro e he
  rcases mem_image.mp he with ⟨⟨d,p⟩, hp, rfl⟩
  have hgood : p ∈ good n d := (mem_sigma.mp hp).2
  obtain ⟨hp₁,hp₂⟩ := mem_filter.mp hgood
  refine mem_filter.mpr ⟨?_, ?_⟩
  · change s(point p, point (p + step d)) ∈ ((patch n).image point).sym2
    exact mk_mem_sym2_iff.mpr ⟨mem_image_of_mem _ hp₁, mem_image_of_mem _ hp₂⟩
  · change dist (s(point p, point (p + step d))).out.1
      (s(point p, point (p + step d))).out.2 = 1
    rw [out_dist, dist_step]

end OMA.HexagonalPatchContacts

namespace Erdos1084Harborth

open scoped BigOperators EuclideanGeometry
open Finset

/- ## Section 1: Pure Graph & Permutation Combinatorics -/

section GraphComb

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma deleteEdges_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) [DecidableRel (G.deleteEdges {e}).Adj] :
    (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
  ext x
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
    Set.mem_singleton_iff, Finset.mem_erase]
  tauto

private lemma deleteEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) [DecidableRel (G.deleteEdges {e}).Adj] :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  rw [deleteEdges_edgeFinset G e]
  exact Finset.card_erase_add_one he

private lemma reachable_deleteEdges_or {G : SimpleGraph V} {u v : V}
    {x y : V} (h : G.Reachable x y) :
    (G.deleteEdges {s(u, v)}).Reachable x y ∨
      ((G.deleteEdges {s(u, v)}).Reachable x u ∨ (G.deleteEdges {s(u, v)}).Reachable x v) ∧
      ((G.deleteEdges {s(u, v)}).Reachable y u ∨ (G.deleteEdges {s(u, v)}).Reachable y v) := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => left; exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    by_cases he : s(a, b) = s(u, v)
    · have hab' : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := Sym2.eq_iff.mp he
      have ha : (G.deleteEdges {s(u, v)}).Reachable a u ∨ (G.deleteEdges {s(u, v)}).Reachable a v := by
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (SimpleGraph.Reachable.refl _)
        · exact Or.inr (SimpleGraph.Reachable.refl _)
      have hb : (G.deleteEdges {s(u, v)}).Reachable b u ∨ (G.deleteEdges {s(u, v)}).Reachable b v := by
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (SimpleGraph.Reachable.refl _)
        · exact Or.inl (SimpleGraph.Reachable.refl _)
      rcases ih with hbc | ⟨_, hc⟩
      · right
        refine ⟨ha, ?_⟩
        rcases hb with hbu | hbv
        · exact Or.inl (hbc.symm.trans hbu)
        · exact Or.inr (hbc.symm.trans hbv)
      · exact Or.inr ⟨ha, hc⟩
    · have hab' : (G.deleteEdges {s(u, v)}).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simp [he]⟩
      have hstep : (G.deleteEdges {s(u, v)}).Reachable a b := hab'.reachable
      rcases ih with hbc | ⟨hb, hc⟩
      · exact Or.inl (hstep.trans hbc)
      · right
        refine ⟨?_, hc⟩
        rcases hb with hbu | hbv
        · exact Or.inl (hstep.trans hbu)
        · exact Or.inr (hstep.trans hbv)

private lemma components_deleteEdges_le (G : SimpleGraph V) (u v : V) :
    Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent ≤
      Nat.card G.ConnectedComponent + 1 := by
  classical
  let G' := G.deleteEdges {s(u, v)}
  let q : G'.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))
  let cv : G'.ConnectedComponent := G'.connectedComponentMk v
  haveI : Fintype G'.ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcard : Fintype.card G'.ConnectedComponent =
      Fintype.card {c : G'.ConnectedComponent // c ≠ cv} + 1 := by
    have h1 : Fintype.card {c : G'.ConnectedComponent // c ≠ cv} =
        Fintype.card G'.ConnectedComponent - Fintype.card {c : G'.ConnectedComponent // c = cv} :=
      Fintype.card_subtype_compl (fun c : G'.ConnectedComponent => c = cv)
    have hle := Fintype.card_subtype_le (fun c : G'.ConnectedComponent => c = cv)
    have h2 : Fintype.card {c : G'.ConnectedComponent // c = cv} = 1 := Fintype.card_unique
    omega
  rw [hcard]
  refine Nat.add_le_add_right ?_ 1
  refine Fintype.card_le_of_injective (fun c : {c : G'.ConnectedComponent // c ≠ cv} => q c.1) ?_
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hq
  apply Subtype.ext
  induction c₁ using SimpleGraph.ConnectedComponent.ind with | _ x =>
  induction c₂ using SimpleGraph.ConnectedComponent.ind with | _ y =>
  have hreach : G.Reachable x y := SimpleGraph.ConnectedComponent.exact hq
  rcases reachable_deleteEdges_or (u := u) (v := v) hreach with hxy | ⟨hx, hy⟩
  · exact SimpleGraph.ConnectedComponent.sound hxy
  · have hxu : G'.Reachable x u := hx.resolve_right (fun h => hc₁ (SimpleGraph.ConnectedComponent.sound h))
    have hyu : G'.Reachable y u := hy.resolve_right (fun h => hc₂ (SimpleGraph.ConnectedComponent.sound h))
    exact SimpleGraph.ConnectedComponent.sound (hxu.trans hyu.symm)

private lemma components_deleteEdges_eq_of_reachable (G : SimpleGraph V) {u v : V}
    (hr : (G.deleteEdges {s(u, v)}).Reachable u v) :
    Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent =
      Nat.card G.ConnectedComponent := by
  classical
  let G' := G.deleteEdges {s(u, v)}
  let q : G'.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))
  haveI : Fintype G'.ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_of_bijective (f := q) ⟨?_, ?_⟩
  · intro c₁ c₂ hq
    induction c₁ using SimpleGraph.ConnectedComponent.ind with | _ x =>
    induction c₂ using SimpleGraph.ConnectedComponent.ind with | _ y =>
    have hreach : G.Reachable x y := SimpleGraph.ConnectedComponent.exact hq
    rcases reachable_deleteEdges_or (u := u) (v := v) hreach with hxy | ⟨hx, hy⟩
    · exact SimpleGraph.ConnectedComponent.sound hxy
    · have hxu : G'.Reachable x u := hx.elim id (fun h => h.trans hr.symm)
      have hyu : G'.Reachable y u := hy.elim id (fun h => h.trans hr.symm)
      exact SimpleGraph.ConnectedComponent.sound (hxu.trans hyu.symm)
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
    exact ⟨G'.connectedComponentMk x, rfl⟩

private lemma card_le_edges_add_components (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤ G.edgeFinset.card + Nat.card G.ConnectedComponent := by
  classical
  suffices h : ∀ m : ℕ, ∀ H : SimpleGraph V, ∀ [DecidableRel H.Adj],
      H.edgeFinset.card = m → Fintype.card V ≤ m + Nat.card H.ConnectedComponent by
    exact h G.edgeFinset.card G rfl
  intro m
  induction m with
  | zero =>
    intro H _ hm
    have hempty : H.edgeFinset = ∅ := Finset.card_eq_zero.mp hm
    have hbot : ∀ x y : V, ¬ H.Adj x y := by
      intro x y hxy
      have : s(x, y) ∈ H.edgeFinset := H.mem_edgeFinset.mpr hxy
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    have hinj : Function.Injective H.connectedComponentMk := by
      intro x y hxy
      obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hxy
      cases p with
      | nil => rfl
      | cons hab _ => exact (hbot _ _ hab).elim
    haveI : Fintype H.ConnectedComponent := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, zero_add]
    exact Fintype.card_le_of_injective _ hinj
  | succ m ih =>
    intro H _ hm
    have hne : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with | _ u v =>
    have hcard' : (H.deleteEdges {s(u, v)}).edgeFinset.card = m := by
      have := deleteEdges_card H s(u, v) he
      omega
    have hih := ih (H.deleteEdges {s(u, v)}) hcard'
    have hcomp := components_deleteEdges_le H u v
    omega

private lemma connected_natCard_components {W : Type*} [Fintype W] {G : SimpleGraph W}
    (hconn : G.Connected) : Nat.card G.ConnectedComponent = 1 := by
  classical
  haveI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  obtain ⟨v₀⟩ := hconn.nonempty
  refine ⟨G.connectedComponentMk v₀, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
  exact SimpleGraph.ConnectedComponent.sound (hconn x v₀)

private lemma card_le_edges_add_one_of_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h1 := card_le_edges_add_components G
  rw [connected_natCard_components hconn] at h1
  exact h1

private lemma card_le_edges_add_components_of_cycle_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (he : G.Adj u v) (hr : (G.deleteEdges {s(u, v)}).Reachable u v) :
    Fintype.card V + 1 ≤ G.edgeFinset.card + Nat.card G.ConnectedComponent := by
  classical
  have h1 := card_le_edges_add_components (G.deleteEdges {s(u, v)})
  have h2 := deleteEdges_card G s(u, v) (G.mem_edgeFinset.mpr he)
  have h3 := components_deleteEdges_eq_of_reachable G hr
  omega

private lemma minimal_connected_edge_card :
    ∀ k : ℕ, ∀ (W : Type*) [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
      T.Connected →
      (∀ u v : W, T.Adj u v → ¬ (T.deleteEdges {s(u, v)}).Connected) →
      T.edgeFinset.card = k → k + 1 = Fintype.card W := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    intro W _ _ T _ hTc hTmin hk
    classical
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hle := card_le_edges_add_one_of_connected T hTc
      have : Nonempty W := hTc.nonempty
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      omega
    · obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < T.edgeFinset.card)
      induction e using Sym2.ind with | _ u v =>
      have huv : T.Adj u v := T.mem_edgeFinset.mp he
      let T' := T.deleteEdges {s(u, v)}
      have hnotr : ¬ T'.Reachable u v := by
        intro hr
        apply hTmin u v huv
        refine @SimpleGraph.Connected.mk _ _ (fun x y => ?_) hTc.nonempty
        rcases reachable_deleteEdges_or (u := u) (v := v) (hTc x y) with hxy | ⟨hx, hy⟩
        · exact hxy
        · exact (hx.elim id (fun h => h.trans hr.symm)).trans
            (hy.elim id (fun h => h.trans hr.symm)).symm
      let Wu := {x : W // T'.Reachable x u}
      let Wv := {x : W // ¬ T'.Reachable x u}
      have hpart : Fintype.card Wu + Fintype.card Wv = Fintype.card W := by
        dsimp only [Wu, Wv]
        have h1 := Fintype.card_subtype_compl (fun x : W => T'.Reachable x u)
        have hle := Fintype.card_subtype_le (fun x : W => T'.Reachable x u)
        omega
      let Tu : SimpleGraph Wu := T'.induce (fun x => T'.Reachable x u)
      let Tv : SimpleGraph Wv := T'.induce (fun x => ¬ T'.Reachable x u)
      have hTu_conn : Tu.Connected := by
        refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨u, SimpleGraph.Reachable.refl u⟩⟩
        have hwalk : ∀ (x y : W) (p : T'.Walk x y) (hy : T'.Reachable y u),
            Tu.Reachable ⟨x, p.reachable.trans hy⟩ ⟨y, hy⟩ := by
          intro x y p
          induction p with
          | nil => intro hy; exact SimpleGraph.Reachable.refl _
          | @cons a₁ b₁ c hab p ihp =>
            intro hy
            have hb : T'.Reachable b₁ u := p.reachable.trans hy
            have hadj : Tu.Adj ⟨a₁, hab.reachable.trans hb⟩ ⟨b₁, hb⟩ := hab
            exact hadj.reachable.trans (ihp hy)
        have ha : Tu.Reachable a ⟨u, SimpleGraph.Reachable.refl u⟩ := by
          obtain ⟨p⟩ := a.2; exact hwalk a.1 u p (SimpleGraph.Reachable.refl u)
        have hb : Tu.Reachable b ⟨u, SimpleGraph.Reachable.refl u⟩ := by
          obtain ⟨p⟩ := b.2; exact hwalk b.1 u p (SimpleGraph.Reachable.refl u)
        exact ha.trans hb.symm
      have hTv_conn : Tv.Connected := by
        refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨v, fun h => hnotr h.symm⟩⟩
        have hrv : ∀ x : W, ¬ T'.Reachable x u → T'.Reachable x v := by
          intro x hx
          rcases reachable_deleteEdges_or (u := u) (v := v) (hTc x v) with hxv | ⟨hx', _⟩
          · exact hxv
          · exact hx'.resolve_left hx
        have hwalk : ∀ (x y : W) (p : T'.Walk x y) (hx : ¬ T'.Reachable x u),
            Tv.Reachable ⟨x, hx⟩ ⟨y, fun h => hx (p.reachable.trans h)⟩ := by
          intro x y p
          induction p with
          | nil => intro hx; exact SimpleGraph.Reachable.refl _
          | @cons a₁ b₁ c hab p ihp =>
            intro hx
            have hb : ¬ T'.Reachable b₁ u := fun h => hx (hab.reachable.trans h)
            have hadj : Tv.Adj ⟨a₁, hx⟩ ⟨b₁, hb⟩ := hab
            exact hadj.reachable.trans (ihp hb)
        have ha : Tv.Reachable a ⟨v, fun h => hnotr h.symm⟩ := by
          obtain ⟨p⟩ := hrv a.1 a.2; exact hwalk a.1 v p a.2
        have hb : Tv.Reachable b ⟨v, fun h => hnotr h.symm⟩ := by
          obtain ⟨p⟩ := hrv b.1 b.2; exact hwalk b.1 v p b.2
        exact ha.trans hb.symm
      have hedges : Tu.edgeFinset.card + Tv.edgeFinset.card = T'.edgeFinset.card := by
        let eU : Sym2 Wu ↪ Sym2 W := (Function.Embedding.subtype _).sym2Map
        let eV : Sym2 Wv ↪ Sym2 W := (Function.Embedding.subtype _).sym2Map
        rw [← Finset.card_map eU, ← Finset.card_map eV, ← Finset.card_union_of_disjoint]
        · congr 1
          ext x
          induction x using Sym2.ind with | _ a b =>
          simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_edgeFinset]
          constructor
          · rintro (⟨y, hy, hyEq⟩ | ⟨y, hy, hyEq⟩)
            · induction y using Sym2.ind with | _ a' b' =>
              have h1 : s(a'.1, b'.1) = s(a, b) := hyEq
              rw [← h1]; exact hy
            · induction y using Sym2.ind with | _ a' b' =>
              have h1 : s(a'.1, b'.1) = s(a, b) := hyEq
              rw [← h1]; exact hy
          · intro hab
            by_cases ha : T'.Reachable a u
            · left
              have hb : T'.Reachable b u := hab.symm.reachable.trans ha
              exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hab, rfl⟩
            · right
              have hb : ¬ T'.Reachable b u := fun h => ha (hab.reachable.trans h)
              exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hab, rfl⟩
        · rw [Finset.disjoint_left]
          intro x hxU hxV
          obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hxU
          obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hxV
          induction y using Sym2.ind with | _ a b =>
          induction z using Sym2.ind with | _ c d =>
          have hz' : s(c.1, d.1) = s(a.1, b.1) := hz
          rcases Sym2.eq_iff.mp hz' with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact c.2 (h1.symm ▸ a.2)
          · exact c.2 (h1.symm ▸ b.2)
      have hT'card : T'.edgeFinset.card + 1 = k := by
        have hdel : T'.edgeFinset.card + 1 = T.edgeFinset.card := deleteEdges_card T s(u, v) he
        omega
      have hTu_min : ∀ a b : Wu, Tu.Adj a b → ¬ (Tu.deleteEdges {s(a, b)}).Connected := by
        intro a b hab hcon
        apply hTmin a.1 b.1 (SimpleGraph.deleteEdges_adj.mp hab).1
        have huv_in : (T.deleteEdges {s(a.1, b.1)}).Adj u v := by
          refine SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩
          intro hmem
          have heq : s(u, v) = s(a.1, b.1) := by simpa using hmem
          exact (SimpleGraph.deleteEdges_adj.mp hab).2 (by simp [heq])
        have hWu_reach : ∀ x y : Wu, (T.deleteEdges {s(a.1, b.1)}).Reachable x.1 y.1 := by
          intro x y
          obtain ⟨p⟩ := hcon x y
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x₁ y₁ z hxy _ ihp =>
            obtain ⟨hxyT', hxyNot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
            have hadj : (T.deleteEdges {s(a.1, b.1)}).Adj x₁.1 y₁.1 := by
              refine SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.deleteEdges_adj.mp hxyT').1, ?_⟩
              intro hmem
              have heq : s(x₁.1, y₁.1) = s(a.1, b.1) := by simpa using hmem
              apply hxyNot
              rw [Set.mem_singleton_iff]
              rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
              · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
            exact hadj.reachable.trans ihp
        have hWv_reach : ∀ x y : Wv, (T.deleteEdges {s(a.1, b.1)}).Reachable x.1 y.1 := by
          intro x y
          obtain ⟨p⟩ := hTv_conn x y
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x₁ y₁ z hxy _ ihp =>
            have hadj : (T.deleteEdges {s(a.1, b.1)}).Adj x₁.1 y₁.1 := by
              refine SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.deleteEdges_adj.mp hxy).1, ?_⟩
              intro hmem
              have heq : s(x₁.1, y₁.1) = s(a.1, b.1) := by simpa using hmem
              rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact x₁.2 (h1.symm ▸ a.2)
              · exact x₁.2 (h1.symm ▸ b.2)
            exact hadj.reachable.trans ihp
        refine @SimpleGraph.Connected.mk _ _ (fun x y => ?_) hTc.nonempty
        have hxu : (T.deleteEdges {s(a.1, b.1)}).Reachable x u := by
          by_cases hx : T'.Reachable x u
          · exact hWu_reach ⟨x, hx⟩ ⟨u, SimpleGraph.Reachable.refl u⟩
          · exact (hWv_reach ⟨x, hx⟩ ⟨v, fun h => hnotr h.symm⟩).trans huv_in.symm.reachable
        have hyu : (T.deleteEdges {s(a.1, b.1)}).Reachable y u := by
          by_cases hy : T'.Reachable y u
          · exact hWu_reach ⟨y, hy⟩ ⟨u, SimpleGraph.Reachable.refl u⟩
          · exact (hWv_reach ⟨y, hy⟩ ⟨v, fun h => hnotr h.symm⟩).trans huv_in.symm.reachable
        exact hxu.trans hyu.symm
      have hTv_min : ∀ a b : Wv, Tv.Adj a b → ¬ (Tv.deleteEdges {s(a, b)}).Connected := by
        intro a b hab hcon
        apply hTmin a.1 b.1 (SimpleGraph.deleteEdges_adj.mp hab).1
        have huv_in : (T.deleteEdges {s(a.1, b.1)}).Adj u v := by
          refine SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩
          intro hmem
          have heq : s(u, v) = s(a.1, b.1) := by simpa using hmem
          exact (SimpleGraph.deleteEdges_adj.mp hab).2 (by simp [heq])
        have hWu_reach : ∀ x y : Wu, (T.deleteEdges {s(a.1, b.1)}).Reachable x.1 y.1 := by
          intro x y
          obtain ⟨p⟩ := hTu_conn x y
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x₁ y₁ z hxy _ ihp =>
            have hadj : (T.deleteEdges {s(a.1, b.1)}).Adj x₁.1 y₁.1 := by
              refine SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.deleteEdges_adj.mp hxy).1, ?_⟩
              intro hmem
              have heq : s(x₁.1, y₁.1) = s(a.1, b.1) := by simpa using hmem
              rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact a.2 (h1 ▸ x₁.2)
              · exact b.2 (h1 ▸ x₁.2)
            exact hadj.reachable.trans ihp
        have hWv_reach : ∀ x y : Wv, (T.deleteEdges {s(a.1, b.1)}).Reachable x.1 y.1 := by
          intro x y
          obtain ⟨p⟩ := hcon x y
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x₁ y₁ z hxy _ ihp =>
            obtain ⟨hxyT', hxyNot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
            have hadj : (T.deleteEdges {s(a.1, b.1)}).Adj x₁.1 y₁.1 := by
              refine SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.deleteEdges_adj.mp hxyT').1, ?_⟩
              intro hmem
              have heq : s(x₁.1, y₁.1) = s(a.1, b.1) := by simpa using hmem
              apply hxyNot
              rw [Set.mem_singleton_iff]
              rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
              · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
            exact hadj.reachable.trans ihp
        refine @SimpleGraph.Connected.mk _ _ (fun x y => ?_) hTc.nonempty
        have hxu : (T.deleteEdges {s(a.1, b.1)}).Reachable x u := by
          by_cases hx : T'.Reachable x u
          · exact hWu_reach ⟨x, hx⟩ ⟨u, SimpleGraph.Reachable.refl u⟩
          · exact (hWv_reach ⟨x, hx⟩ ⟨v, fun h => hnotr h.symm⟩).trans huv_in.symm.reachable
        have hyu : (T.deleteEdges {s(a.1, b.1)}).Reachable y u := by
          by_cases hy : T'.Reachable y u
          · exact hWu_reach ⟨y, hy⟩ ⟨u, SimpleGraph.Reachable.refl u⟩
          · exact (hWv_reach ⟨y, hy⟩ ⟨v, fun h => hnotr h.symm⟩).trans huv_in.symm.reachable
        exact hxu.trans hyu.symm
      have ihu := ihk Tu.edgeFinset.card (by omega) Wu Tu hTu_conn hTu_min rfl
      have ihv := ihk Tv.edgeFinset.card (by omega) Wv Tv hTv_conn hTv_min rfl
      omega

private lemma exists_spanning_tree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.Connected ∧
      ∀ [DecidableRel T.Adj], T.edgeFinset.card + 1 = Fintype.card V := by
  classical
  suffices h : ∀ m : ℕ, ∀ H : SimpleGraph V, ∀ [DecidableRel H.Adj], H ≤ G → H.Connected →
      H.edgeFinset.card = m →
      ∃ T : SimpleGraph V, T ≤ G ∧ T.Connected ∧
        ∀ [DecidableRel T.Adj], T.edgeFinset.card + 1 = Fintype.card V by
    exact h G.edgeFinset.card G le_rfl hconn rfl
  intro m
  induction m with
  | zero =>
    intro H _ hHG hHconn hm
    refine ⟨H, hHG, hHconn, ?_⟩
    intro _
    have hle := card_le_edges_add_one_of_connected H hHconn
    have : Nonempty V := hHconn.nonempty
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hEq : H.edgeFinset.card = 0 := by convert hm
    omega
  | succ m ih =>
    intro H _ hHG hHconn hm
    by_cases hred : ∃ u v : V, H.Adj u v ∧ (H.deleteEdges {s(u, v)}).Connected
    · obtain ⟨u, v, huv, hconn'⟩ := hred
      have hcard' : (H.deleteEdges {s(u, v)}).edgeFinset.card = m := by
        have := deleteEdges_card H s(u, v) (H.mem_edgeFinset.mpr huv)
        omega
      exact ih (H.deleteEdges {s(u, v)}) ((SimpleGraph.deleteEdges_le _).trans hHG) hconn' hcard'
    · push Not at hred
      refine ⟨H, hHG, hHconn, ?_⟩
      intro _
      exact minimal_connected_edge_card H.edgeFinset.card V H hHconn hred rfl

/- ### Permutation Orbits, Tree Single-Orbit Lemma, and Edge-Splicing Lemma -/

private def sameOrbit {α : Type*} (φ : Equiv.Perm α) (x y : α) : Prop :=
  ∃ k : ℕ, (φ ^ k) x = y

private lemma sameOrbit_refl {α : Type*} (φ : Equiv.Perm α) (x : α) : sameOrbit φ x x :=
  ⟨0, rfl⟩

private lemma sameOrbit_trans {α : Type*} (φ : Equiv.Perm α) {x y z : α}
    (h1 : sameOrbit φ x y) (h2 : sameOrbit φ y z) : sameOrbit φ x z := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  exact ⟨m + k, by rw [pow_add, Equiv.Perm.mul_apply]⟩

private lemma sameOrbit_symm {α : Type*} [Fintype α] (φ : Equiv.Perm α) {x y : α}
    (h : sameOrbit φ x y) : sameOrbit φ y x := by
  classical
  obtain ⟨k, rfl⟩ := h
  have hord : 0 < orderOf φ := orderOf_pos φ
  let m := orderOf φ - (k % orderOf φ)
  refine ⟨m, ?_⟩
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  have hdvd : orderOf φ ∣ m + k := by
    have h1 : k = orderOf φ * (k / orderOf φ) + k % orderOf φ := (Nat.div_add_mod k (orderOf φ)).symm
    have h2 : k % orderOf φ < orderOf φ := Nat.mod_lt k hord
    refine ⟨k / orderOf φ + 1, ?_⟩
    dsimp [m]
    rw [mul_add, mul_one]
    omega
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, pow_mul, pow_orderOf_eq_one, one_pow]
  rfl

private def orbitSetoid {α : Type*} [Fintype α] (φ : Equiv.Perm α) : Setoid α where
  r := sameOrbit φ
  iseqv := ⟨sameOrbit_refl φ, fun h => sameOrbit_symm φ h, fun h1 h2 => sameOrbit_trans φ h1 h2⟩

private noncomputable def numOrbits {α : Type*} [Fintype α] (φ : Equiv.Perm α) : ℕ :=
  Nat.card (Quotient (orbitSetoid φ))

private lemma sameOrbit_step {α : Type*} (φ : Equiv.Perm α) (x : α) :
    sameOrbit φ x (φ x) := ⟨1, by simp⟩

/-- A permutation `φ` is transitive iff `numOrbits φ = 1` (for nonempty `α`). -/
private lemma numOrbits_eq_one_iff {α : Type*} [Fintype α] [Nonempty α] (φ : Equiv.Perm α) :
    numOrbits φ = 1 ↔ ∀ x y : α, sameOrbit φ x y := by
  classical
  unfold numOrbits
  haveI : Fintype (Quotient (orbitSetoid φ)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩ x y
    have hx : Quotient.mk (orbitSetoid φ) x = q := hq _
    have hy : Quotient.mk (orbitSetoid φ) y = q := hq _
    exact Quotient.exact (hx.trans hy.symm)
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty α›
    refine ⟨Quotient.mk (orbitSetoid φ) x₀, fun q => ?_⟩
    induction q using Quotient.ind with | _ y =>
    exact Quotient.sound (h y x₀)

/-- Darts of a simple graph `H`. -/
private abbrev DartOf {W : Type*} (H : SimpleGraph W) := {d : W × W // H.Adj d.1 d.2}

/-- Build the dart permutation `φ(u, v) = (v, σ_v(u))` from local neighbor permutations `σ_v`. -/
private def dartPerm {W : Type*} (H : SimpleGraph W)
    (σ : ∀ v : W, Equiv.Perm {u : W // H.Adj v u}) : Equiv.Perm (DartOf H) where
  toFun d := ⟨(d.1.2, (σ d.1.2 ⟨d.1.1, d.2.symm⟩).1), (σ d.1.2 ⟨d.1.1, d.2.symm⟩).2⟩
  invFun d := ⟨(((σ d.1.1).symm ⟨d.1.2, d.2⟩).1, d.1.1), (((σ d.1.1).symm ⟨d.1.2, d.2⟩).2).symm⟩
  left_inv d := by
    rcases d with ⟨⟨u, v⟩, huv⟩
    simp
  right_inv d := by
    rcases d with ⟨⟨u, v⟩, huv⟩
    simp

/-- A cyclic permutation on a finite type `A` is one with a single orbit (or `A` is empty). -/
private def IsCyclicPerm {A : Type*} [Fintype A] (σ : Equiv.Perm A) : Prop :=
  ∀ x y : A, sameOrbit σ x y

/-- Deleting one element `a` from a cyclic permutation on `A` gives a cyclic permutation on `{x // x ≠ a}`. -/
private def deleteElemPerm {A : Type*} [DecidableEq A] (σ : Equiv.Perm A) (a : A) :
    Equiv.Perm {x : A // x ≠ a} where
  toFun x :=
    if h : σ x.1 = a then ⟨σ a, fun h' => x.2 (σ.injective (h.trans h'.symm))⟩
    else ⟨σ x.1, h⟩
  invFun y :=
    if h : σ.symm y.1 = a then ⟨σ.symm a, fun h' => y.2 (σ.symm.injective (h.trans h'.symm))⟩
    else ⟨σ.symm y.1, h⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    split_ifs with h1 h2 h3
    · exact σ.symm_apply_eq.mpr h1.symm
    · exact (h2 (σ.symm_apply_apply a)).elim
    · rw [σ.symm_apply_apply] at h3; exact (x.2 h3).elim
    · exact σ.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    dsimp only
    split_ifs with h1 h2 h3
    · exact σ.eq_symm_apply.mp h1.symm
    · exact (h2 (σ.apply_symm_apply a)).elim
    · rw [σ.apply_symm_apply] at h3; exact (y.2 h3).elim
    · exact σ.apply_symm_apply y.1

private lemma deleteElemPerm_isCyclic {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (a : A) (hcyc : IsCyclicPerm σ) :
    IsCyclicPerm (deleteElemPerm σ a) := by
  intro x y
  obtain ⟨k, hk⟩ := hcyc x.1 y.1
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    rcases k with _ | k
    · exact ⟨0, Subtype.ext hk⟩
    · by_cases hxa : σ x.1 = a
      · rcases k with _ | k
        · exfalso
          rw [zero_add, pow_one] at hk
          exact y.2 (hk.symm.trans hxa)
        · have hx' : ((deleteElemPerm σ a) x).1 = σ a := by
            simp only [deleteElemPerm, Equiv.coe_fn_mk]
            split_ifs <;> first | rfl | contradiction
          have hk' : (σ ^ k) ((deleteElemPerm σ a) x).1 = y.1 := by
            rw [hx']
            have : (σ ^ (k + 2)) x.1 = (σ ^ k) (σ (σ x.1)) := by
              rw [pow_add, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
            rw [← hk, this, hxa]
          obtain ⟨m, hm⟩ := ih k (by omega) ((deleteElemPerm σ a) x) hk'
          exact ⟨m + 1, by rw [pow_add, pow_one, Equiv.Perm.mul_apply]; exact hm⟩
      · have hx' : ((deleteElemPerm σ a) x).1 = σ x.1 := by
          simp only [deleteElemPerm, Equiv.coe_fn_mk]
          split_ifs <;> first | rfl | contradiction
        have hk' : (σ ^ k) ((deleteElemPerm σ a) x).1 = y.1 := by
          rw [hx']
          have : (σ ^ (k + 1)) x.1 = (σ ^ k) (σ x.1) := by
            rw [pow_add, pow_one, Equiv.Perm.mul_apply]
          rw [← hk, this]
        obtain ⟨m, hm⟩ := ih k (by omega) ((deleteElemPerm σ a) x) hk'
        exact ⟨m + 1, by rw [pow_add, pow_one, Equiv.Perm.mul_apply]; exact hm⟩

/-- Any rotation system (cyclic local permutations) on a finite tree has a SINGLE dart orbit. -/
private lemma tree_one_orbit :
    ∀ n : ℕ, 2 ≤ n →
    ∀ (W : Type*) [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj]
      (σ : ∀ v : W, Equiv.Perm {u : W // T.Adj v u}),
      Fintype.card W = n → T.Connected → T.edgeFinset.card + 1 = n →
      (∀ v, IsCyclicPerm (σ v)) →
      ∀ d₁ d₂ : DartOf T, sameOrbit (dartPerm T σ) d₁ d₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn W _ _ T _ σ hW hconn hedge hcyc
    classical
    by_cases hn2 : n = 2
    · subst hn2
      intro d₁ d₂
      have hcard_d : Fintype.card (DartOf T) = 2 := by
        have h1 : Fintype.card (DartOf T) = ∑ v : W, T.degree v := by
          have e : DartOf T ≃ Σ v : W, {u : W // T.Adj v u} :=
            { toFun := fun d => ⟨d.1.2, ⟨d.1.1, d.2.symm⟩⟩
              invFun := fun p => ⟨(p.2.1, p.1), p.2.2.symm⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
              right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
          rw [Fintype.card_congr e, Fintype.card_sigma]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Fintype.card_coe]
          exact Fintype.card_congr ⟨fun u => ⟨u.1, (T.mem_neighborFinset _ _).mpr u.2⟩,
            fun u => ⟨u.1, (T.mem_neighborFinset _ _).mp u.2⟩, fun _ => rfl, fun _ => rfl⟩
        rw [h1, T.sum_degrees_eq_twice_card_edges]
        omega
      by_cases h : d₁ = d₂
      · exact h ▸ sameOrbit_refl _ _
      · have hne : dartPerm T σ d₁ ≠ d₁ := by
          intro heq
          have : d₁.1.2 = d₁.1.1 := congrArg (fun d => d.1.1) heq
          exact T.loopless.irrefl d₁.1.1 (this ▸ d₁.2)
        -- In a 2-element type, d₂ must be dartPerm T σ d₁
        have hmem : ∀ x : DartOf T, x = d₁ ∨ x = dartPerm T σ d₁ := by
          intro x
          by_contra hx
          push Not at hx
          let s : Finset (DartOf T) := {d₁, dartPerm T σ d₁, x}
          have hs : s.card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hx.2.symm]
            · simp [hne.symm, hx.1.symm]
          have hle : s.card ≤ Fintype.card (DartOf T) := Finset.card_le_univ s
          omega
        rcases hmem d₂ with h1 | h2
        · exact (h h1.symm).elim
        · exact ⟨1, by simp [h2]⟩
    · -- n ≥ 3: find a leaf ℓ (degree 1)
      have hn3 : 3 ≤ n := by omega
      have hpos_deg : ∀ v : W, 1 ≤ T.degree v := by
        intro v
        have hne : ∃ w : W, w ≠ v := by
          by_contra h
          push Not at h
          have : Fintype.card W ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (h a).trans (h b).symm)
          omega
        obtain ⟨w, hw⟩ := hne
        obtain ⟨p⟩ := hconn v w
        cases p with
        | nil => exact (hw rfl).elim
        | cons hvu _ =>
          have : _ ∈ T.neighborFinset v := (T.mem_neighborFinset _ _).mpr hvu
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨_, this⟩
      have hleaf : ∃ ℓ : W, T.degree ℓ = 1 := by
        by_contra h
        push Not at h
        have hge2 : ∀ v : W, 2 ≤ T.degree v := fun v => by
          have := hpos_deg v; have := h v; omega
        have hsum : 2 * Fintype.card W ≤ ∑ v : W, T.degree v := by
          calc 2 * Fintype.card W = ∑ _ : W, (2 : ℕ) := by simp [mul_comm]
            _ ≤ ∑ v : W, T.degree v := Finset.sum_le_sum (fun v _ => hge2 v)
        rw [T.sum_degrees_eq_twice_card_edges] at hsum
        omega
      obtain ⟨ℓ, hℓdeg⟩ := hleaf
      have hℓcard : (T.neighborFinset ℓ).card = 1 := by
        rwa [SimpleGraph.card_neighborFinset_eq_degree]
      obtain ⟨w, hwmem⟩ := Finset.card_eq_one.mp hℓcard
      have hℓw : T.Adj ℓ w := (T.mem_neighborFinset _ _).mp (hwmem ▸ Finset.mem_singleton_self w)
      have hℓ_only : ∀ u : W, T.Adj ℓ u → u = w := fun u hu =>
        Finset.mem_singleton.mp (hwmem ▸ (T.mem_neighborFinset _ _).mpr hu)
      -- Delete ℓ to get W' = {x // x ≠ ℓ} and T' = T.induce (· ≠ ℓ)
      let W' := {x : W // x ≠ ℓ}
      let T' : SimpleGraph W' := T.induce (fun x => x ≠ ℓ)
      have hW' : Fintype.card W' = n - 1 := by
        dsimp only [W']
        have hsum : Fintype.card {x : W // x ≠ ℓ} = Fintype.card W - Fintype.card {x : W // x = ℓ} :=
          Fintype.card_subtype_compl (fun x : W => x = ℓ)
        have h1 : Fintype.card {x : W // x = ℓ} = 1 := Fintype.card_unique
        omega
      have hT'_conn : T'.Connected := by
        refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨w, hℓw.ne.symm⟩⟩
        obtain ⟨p⟩ := hconn a.1 b.1
        have hp' : ∀ (x y : W) (q : T.Walk x y) (hx : x ≠ ℓ) (hy : y ≠ ℓ), q.IsPath →
            T'.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
          intro x y q
          induction q with
          | nil => intro hx hy _; exact SimpleGraph.Reachable.refl _
          | @cons a₁ b₁ c hab q' ihq =>
            intro hx hy hpath
            have hb : b₁ ≠ ℓ := by
              intro hbl
              subst hbl
              cases q' with
              | nil => exact hy rfl
              | @cons _ c₁ _ hlc q'' =>
                have h1 : a₁ = w := hℓ_only a₁ hab.symm
                have h2 : c₁ = w := hℓ_only c₁ hlc
                have hnd := hpath.support_nodup
                simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons] at hnd
                exact hnd.1 (Or.inr (h1 ▸ h2 ▸ q''.start_mem_support))
            have hstep : T'.Adj ⟨a₁, hx⟩ ⟨b₁, hb⟩ := hab
            exact hstep.reachable.trans (ihq hb hy hpath.of_cons)
        exact hp' a.1 b.1 p.toPath a.2 b.2 p.toPath.property
      have hT'_edge : T'.edgeFinset.card + 1 = n - 1 := by
        let emb : Sym2 W' ↪ Sym2 W := (Function.Embedding.subtype _).sym2Map
        have hEq : T.edgeFinset = insert s(ℓ, w) (T'.edgeFinset.map emb) := by
          ext e
          induction e using Sym2.ind with | _ a b =>
          simp only [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_edgeFinset]
          constructor
          · intro hab
            by_cases ha : a = ℓ
            · subst ha; left; rw [hℓ_only b hab]
            · by_cases hb : b = ℓ
              · subst hb; left; rw [hℓ_only a hab.symm, Sym2.eq_swap]
              · right; exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hab, rfl⟩
          · rintro (heq | ⟨y, hy, hyEq⟩)
            · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hℓw
              · exact hℓw.symm
            · induction y using Sym2.ind with | _ a' b' =>
              have h1 : s(a'.1, b'.1) = s(a, b) := hyEq
              rw [← h1]; exact hy
        have hnot : s(ℓ, w) ∉ T'.edgeFinset.map emb := by
          intro hm
          obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hm
          induction y using Sym2.ind with | _ a' b' =>
          have hy' : s(a'.1, b'.1) = s(ℓ, w) := hy
          rcases Sym2.eq_iff.mp hy' with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact a'.2 h1
          · exact b'.2 h2
        have hc := congrArg Finset.card hEq
        rw [Finset.card_insert_of_notMem hnot, Finset.card_map] at hc
        omega
      -- Build induced cyclic rotation system σ' on T'
      let equivN (v : W') (hv : v.1 ≠ w) : {u : W' // T'.Adj v u} ≃ {u : W // T.Adj v.1 u} :=
        { toFun := fun u => ⟨u.1.1, u.2⟩
          invFun := fun u => ⟨⟨u.1, fun h => hv (hℓ_only v.1 (h ▸ u.2).symm)⟩, u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let equivNw : {u : W' // T'.Adj ⟨w, hℓw.ne.symm⟩ u} ≃
          {u : {x : W // T.Adj w x} // u ≠ ⟨ℓ, hℓw.symm⟩} :=
        { toFun := fun u => ⟨⟨u.1.1, u.2⟩, fun h => u.1.2 (congrArg Subtype.val h)⟩
          invFun := fun u => ⟨⟨u.1.1, fun h => u.2 (Subtype.ext h)⟩, u.1.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let σ' : ∀ v : W', Equiv.Perm {u : W' // T'.Adj v u} := fun v =>
        if hv : v.1 = w then
          let e1 : {u : W' // T'.Adj v u} ≃ {u : W' // T'.Adj ⟨w, hℓw.ne.symm⟩ u} :=
            Equiv.subtypeEquiv (Equiv.refl _) (fun u => by subst hv; rfl)
          (e1.trans equivNw).trans ((deleteElemPerm (σ w) ⟨ℓ, hℓw.symm⟩).trans (e1.trans equivNw).symm)
        else
          (equivN v hv).trans ((σ v.1).trans (equivN v hv).symm)
      have hcyc' : ∀ v : W', IsCyclicPerm (σ' v) := by
        intro v
        dsimp only [σ']
        split_ifs with hv
        · intro x y
          let e := (Equiv.subtypeEquiv (Equiv.refl W') (fun u => by subst hv; rfl) :
            {u : W' // T'.Adj v u} ≃ {u : W' // T'.Adj ⟨w, hℓw.ne.symm⟩ u}).trans equivNw
          have hc := deleteElemPerm_isCyclic (σ w) ⟨ℓ, hℓw.symm⟩ (hcyc w) (e x) (e y)
          obtain ⟨k, hk⟩ := hc
          refine ⟨k, ?_⟩
          have hpow : ∀ m : ℕ, ∀ z, ((e.trans ((deleteElemPerm (σ w) ⟨ℓ, hℓw.symm⟩).trans e.symm)) ^ m) z =
              e.symm (((deleteElemPerm (σ w) ⟨ℓ, hℓw.symm⟩) ^ m) (e z)) := by
            intro m
            induction m with
            | zero => intro z; simp
            | succ m ihm =>
              intro z
              rw [pow_succ', Equiv.Perm.mul_apply, ihm, pow_succ', Equiv.Perm.mul_apply]
              simp
          rw [hpow, hk, e.symm_apply_apply]
        · intro x y
          let e := equivN v hv
          obtain ⟨k, hk⟩ := hcyc v.1 (e x) (e y)
          refine ⟨k, ?_⟩
          have hpow : ∀ m : ℕ, ∀ z, ((e.trans ((σ v.1).trans e.symm)) ^ m) z =
              e.symm (((σ v.1) ^ m) (e z)) := by
            intro m
            induction m with
            | zero => intro z; simp
            | succ m ihm =>
              intro z
              rw [pow_succ', Equiv.Perm.mul_apply, ihm, pow_succ', Equiv.Perm.mul_apply]
              simp
          rw [hpow, hk, e.symm_apply_apply]
      have hIH := ih (n - 1) (by omega) (by omega) W' T' σ' hW' hT'_conn hT'_edge hcyc'
      -- Embed DartOf T' into DartOf T
      let embD : DartOf T' → DartOf T := fun d => ⟨(d.1.1.1, d.1.2.1), d.2⟩
      -- Show every single φ'-step is realized by 1 or 3 φ-steps
      have hstep_sim : ∀ d : DartOf T', sameOrbit (dartPerm T σ) (embD d) (embD (dartPerm T' σ' d)) := by
        intro d
        by_cases hw : d.1.2.1 = w
        · have hdw : T.Adj w d.1.1.1 := hw ▸ d.2.symm
          by_cases hhit : (σ w ⟨d.1.1.1, hdw⟩).1 = ℓ
          · refine ⟨3, ?_⟩
            have h1 : dartPerm T σ (embD d) = ⟨(w, ℓ), hℓw.symm⟩ := by
              apply Subtype.ext; apply Prod.ext
              · exact hw
              · dsimp [dartPerm, embD]; subst hw; exact hhit
            have h2 : dartPerm T σ ⟨(w, ℓ), hℓw.symm⟩ = ⟨(ℓ, w), hℓw⟩ := by
              apply Subtype.ext; apply Prod.ext
              · rfl
              · exact hℓ_only _ (σ ℓ ⟨w, hℓw⟩).2
            have h3 : dartPerm T σ ⟨(ℓ, w), hℓw⟩ = embD (dartPerm T' σ' d) := by
              apply Subtype.ext; apply Prod.ext
              · exact hw.symm
              · dsimp [dartPerm, embD, σ']
                rw [dif_pos hw]
                have hhit' : σ w ⟨d.1.1.1, hw ▸ d.2.symm⟩ = ⟨ℓ, hℓw.symm⟩ := Subtype.ext hhit
                simp only [equivNw, deleteElemPerm, hhit', Equiv.trans_apply, Equiv.coe_fn_mk,
                  Equiv.subtypeEquiv_apply, Equiv.refl_apply, Equiv.coe_fn_symm_mk, ↓reduceDIte]
                rfl
            change dartPerm T σ (dartPerm T σ (dartPerm T σ (embD d))) = _
            rw [h1, h2, h3]
          · refine ⟨1, ?_⟩
            apply Subtype.ext; apply Prod.ext
            · rfl
            · dsimp [dartPerm, embD, σ']
              rw [dif_pos hw]
              have hhit' : σ w ⟨d.1.1.1, hw ▸ d.2.symm⟩ ≠ ⟨ℓ, hℓw.symm⟩ :=
                fun h => hhit (congrArg Subtype.val h)
              simp only [equivNw, deleteElemPerm, Equiv.trans_apply, Equiv.coe_fn_mk,
                Equiv.subtypeEquiv_apply, Equiv.refl_apply, Equiv.coe_fn_symm_mk]
              rw [dif_neg hhit']
              subst hw; rfl
        · refine ⟨1, ?_⟩
          apply Subtype.ext; apply Prod.ext
          · rfl
          · dsimp [dartPerm, embD, σ']
            rw [dif_neg hw]
            simp [equivN]
      have hsim : ∀ a b : DartOf T', sameOrbit (dartPerm T σ) (embD a) (embD b) := by
        intro a b
        obtain ⟨k, hk⟩ := hIH a b
        induction k generalizing a with
        | zero => exact hk ▸ sameOrbit_refl _ _
        | succ k ihk =>
          have h1 := hstep_sim a
          have h2 := ihk (dartPerm T' σ' a) (by rw [← hk, pow_succ, Equiv.Perm.mul_apply])
          exact sameOrbit_trans _ h1 h2
      -- Every dart of T is in the same orbit as some embD d₀
      have hto_emb : ∀ d : DartOf T, ∃ d' : DartOf T', sameOrbit (dartPerm T σ) d (embD d') := by
        intro d
        by_cases h1 : d.1.1 ≠ ℓ ∧ d.1.2 ≠ ℓ
        · exact ⟨⟨(⟨d.1.1, h1.1⟩, ⟨d.1.2, h1.2⟩), d.2⟩, sameOrbit_refl _ _⟩
        · have hσw_ne : (σ w ⟨ℓ, hℓw.symm⟩).1 ≠ ℓ := by
            intro heq
            have hdeg2 : ∃ u : W, T.Adj w u ∧ u ≠ ℓ := by
              have hne : ∃ x : W', x ≠ ⟨w, hℓw.ne.symm⟩ := by
                by_contra h; push Not at h
                have : Fintype.card W' ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (h a).trans (h b).symm)
                omega
              obtain ⟨x, hx⟩ := hne
              obtain ⟨p⟩ := hT'_conn ⟨w, hℓw.ne.symm⟩ x
              cases p with
              | nil => exact (hx rfl).elim
              | @cons _ u' _ hwu _ => exact ⟨u'.1, hwu, u'.2⟩
            obtain ⟨u, hwu, huℓ⟩ := hdeg2
            obtain ⟨k, hk⟩ := hcyc w ⟨ℓ, hℓw.symm⟩ ⟨u, hwu⟩
            have hfix : ∀ m, ((σ w) ^ m) ⟨ℓ, hℓw.symm⟩ = ⟨ℓ, hℓw.symm⟩ := by
              intro m; induction m with
              | zero => rfl
              | succ m ihm => rw [pow_succ', Equiv.Perm.mul_apply, ihm]; exact Subtype.ext heq
            rw [hfix k] at hk
            exact huℓ (congrArg Subtype.val hk).symm
          let d_out : DartOf T' :=
            ⟨(⟨w, hℓw.ne.symm⟩, ⟨(σ w ⟨ℓ, hℓw.symm⟩).1, hσw_ne⟩), (σ w ⟨ℓ, hℓw.symm⟩).2⟩
          refine ⟨d_out, ?_⟩
          by_cases ha : d.1.1 = ℓ
          · have hb : d.1.2 = w := hℓ_only d.1.2 (ha ▸ d.2)
            have hd : d = ⟨(ℓ, w), hℓw⟩ := Subtype.ext (Prod.ext ha hb)
            rw [hd]
            exact ⟨1, rfl⟩
          · have hb : d.1.2 = ℓ := by tauto
            have ha' : d.1.1 = w := hℓ_only d.1.1 (hb ▸ d.2.symm)
            have hd : d = ⟨(w, ℓ), hℓw.symm⟩ := Subtype.ext (Prod.ext ha' hb)
            rw [hd]
            refine ⟨2, ?_⟩
            have hstep1 : dartPerm T σ ⟨(w, ℓ), hℓw.symm⟩ = ⟨(ℓ, w), hℓw⟩ := by
              apply Subtype.ext; apply Prod.ext; · rfl
              · exact hℓ_only _ (σ ℓ ⟨w, hℓw⟩).2
            change dartPerm T σ (dartPerm T σ _) = _
            rw [hstep1]; rfl
      intro d₁ d₂
      obtain ⟨d₁', h₁⟩ := hto_emb d₁
      obtain ⟨d₂', h₂⟩ := hto_emb d₂
      exact sameOrbit_trans _ h₁ (sameOrbit_trans _ (hsim d₁' d₂') (sameOrbit_symm _ h₂))

/-- Pure permutation splicing lemma: inserting two new elements `e₁, e₂` between `d_a ↦ φ(d_b)`
    and `d_b ↦ φ(d_a)` where `d_a ≠ d_b` lie in the SAME `φ`-orbit increases `numOrbits` by 1. -/
private lemma splice_adds_one_orbit {D : Type*} [Fintype D] [DecidableEq D]
    (φ : Equiv.Perm D) {d_a d_b : D} (hne : d_a ≠ d_b) (hsame : sameOrbit φ d_a d_b)
    (φ' : Equiv.Perm (D ⊕ Bool))
    (h_other : ∀ d : D, d ≠ d_a → d ≠ d_b → φ' (Sum.inl d) = Sum.inl (φ d))
    (h_da : φ' (Sum.inl d_a) = Sum.inr false)
    (h_e1 : φ' (Sum.inr false) = Sum.inl (φ d_b))
    (h_db : φ' (Sum.inl d_b) = Sum.inr true)
    (h_e2 : φ' (Sum.inr true) = Sum.inl (φ d_a)) :
    numOrbits φ' = numOrbits φ + 1 := by
  classical
  -- Step 1: find minimal positive k with (φ^k) d_a = d_b, and minimal positive m with (φ^m) d_a = d_a
  have hk_ex : ∃ k : ℕ, 0 < k ∧ (φ ^ k) d_a = d_b := by
    obtain ⟨k, hk⟩ := hsame
    rcases k with _ | k
    · exact (hne hk).elim
    · exact ⟨k + 1, Nat.succ_pos _, hk⟩
  let k := Nat.find hk_ex
  have hk_pos : 0 < k := (Nat.find_spec hk_ex).1
  have hk_eq : (φ ^ k) d_a = d_b := (Nat.find_spec hk_ex).2
  have hk_min : ∀ j, 0 < j → j < k → (φ ^ j) d_a ≠ d_b := fun j hj hlt h =>
    Nat.find_min hk_ex hlt ⟨hj, h⟩
  have hm_ex : ∃ m : ℕ, 0 < m ∧ (φ ^ m) d_a = d_a :=
    ⟨orderOf φ, orderOf_pos φ, by rw [pow_orderOf_eq_one]; rfl⟩
  let m := Nat.find hm_ex
  have hm_pos : 0 < m := (Nat.find_spec hm_ex).1
  have hm_eq : (φ ^ m) d_a = d_a := (Nat.find_spec hm_ex).2
  have hm_min : ∀ j, 0 < j → j < m → (φ ^ j) d_a ≠ d_a := fun j hj hlt h =>
    Nat.find_min hm_ex hlt ⟨hj, h⟩
  have hkm : k < m := by
    by_contra hle
    push_neg at hle
    have hrem : (φ ^ (k % m)) d_a = d_b := by
      have hdiv : ∀ q r, (φ ^ (m * q + r)) d_a = (φ ^ r) d_a := by
        intro q r
        induction q with
        | zero => simp
        | succ q ihq =>
          have : m * (q + 1) + r = m + (m * q + r) := by ring
          rw [this, pow_add, Equiv.Perm.mul_apply, ihq, ← Equiv.Perm.mul_apply, ← pow_add,
            add_comm, pow_add, Equiv.Perm.mul_apply, hm_eq]
      rw [← hdiv (k / m) (k % m), Nat.div_add_mod]
      exact hk_eq
    rcases Nat.eq_zero_or_pos (k % m) with h0 | hpos
    · rw [h0] at hrem; exact hne hrem
    · exact hk_min (k % m) hpos (lt_of_lt_of_le (Nat.mod_lt k hm_pos) hle) hrem
  -- Partition the orbit C₀ = {(φ^j) d_a | j < m} into:
  -- S1 = {Sum.inr false} ∪ {Sum.inl ((φ^j) d_a) | j = 0 ∨ k < j < m}
  -- S2 = {Sum.inr true}  ∪ {Sum.inl ((φ^j) d_a) | 0 < j ≤ k}
  have hinj_m : ∀ i j, i < m → j < m → (φ ^ i) d_a = (φ ^ j) d_a → i = j := by
    intro i j hi hj heq
    wlog hle : i ≤ j generalizing i j
    · exact (this j i hj hi heq.symm (by omega)).symm
    rcases eq_or_lt_of_le hle with rfl | hlt
    · rfl
    · exfalso
      have : (φ ^ (j - i)) d_a = d_a := by
        apply (φ ^ i).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
        exact heq.symm
      exact hm_min (j - i) (by omega) (by omega) this
  -- Show φ' stays inside S1 and S2 respectively, and acts transitively on each!
  let orb1 : Finset (D ⊕ Bool) :=
    insert (Sum.inr false) (insert (Sum.inl d_a)
      ((Finset.Ioo k m).image (fun j => Sum.inl ((φ ^ j) d_a))))
  let orb2 : Finset (D ⊕ Bool) :=
    insert (Sum.inr true) ((Finset.Ioc 0 k).image (fun j => Sum.inl ((φ ^ j) d_a)))
  have h1_reach : ∀ x ∈ orb1, sameOrbit φ' (Sum.inl d_a) x := by
    intro x hx
    simp only [orb1, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioo] at hx
    rcases hx with rfl | rfl | ⟨j, ⟨hkj, hjm⟩, rfl⟩
    · exact ⟨1, by simp [h_da]⟩
    · exact sameOrbit_refl _ _
    · -- Walk from Sum.inl d_a -> Sum.inr false -> Sum.inl (φ d_b) = Sum.inl ((φ^(k+1)) d_a) -> ... -> Sum.inl ((φ^j) d_a)
      have hstart : sameOrbit φ' (Sum.inl d_a) (Sum.inl ((φ ^ (k + 1)) d_a)) := by
        refine ⟨2, ?_⟩
        change φ' (φ' (Sum.inl d_a)) = _
        rw [h_da, h_e1, pow_succ', Equiv.Perm.mul_apply, hk_eq]
      have hwalk : ∀ t : ℕ, k + 1 + t < m →
          sameOrbit φ' (Sum.inl ((φ ^ (k + 1)) d_a)) (Sum.inl ((φ ^ (k + 1 + t)) d_a)) := by
        intro t
        induction t with
        | zero => intro _; exact sameOrbit_refl _ _
        | succ t iht =>
          intro hlt
          have hprev := iht (by omega)
          have hna : (φ ^ (k + 1 + t)) d_a ≠ d_a := hm_min _ (by omega) (by omega)
          have hnb : (φ ^ (k + 1 + t)) d_a ≠ d_b := fun h => by
            have := hinj_m (k + 1 + t) k (by omega) hkm (h.trans hk_eq.symm)
            omega
          have hstep : φ' (Sum.inl ((φ ^ (k + 1 + t)) d_a)) = Sum.inl ((φ ^ (k + 1 + (t + 1))) d_a) := by
            rw [h_other _ hna hnb, ← Equiv.Perm.mul_apply, ← pow_succ']
            rfl
          exact sameOrbit_trans _ hprev ⟨1, by simp [hstep]⟩
      have hj_eq : j = k + 1 + (j - (k + 1)) := by omega
      rw [hj_eq]
      exact sameOrbit_trans _ hstart (hwalk (j - (k + 1)) (by omega))
  have h2_reach : ∀ x ∈ orb2, sameOrbit φ' (Sum.inl d_b) x := by
    intro x hx
    simp only [orb2, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioc] at hx
    rcases hx with rfl | ⟨j, ⟨hj0, hjk⟩, rfl⟩
    · exact ⟨1, by simp [h_db]⟩
    · have hstart : sameOrbit φ' (Sum.inl d_b) (Sum.inl ((φ ^ 1) d_a)) := by
        refine ⟨2, ?_⟩
        change φ' (φ' (Sum.inl d_b)) = _
        rw [h_db, h_e2, pow_one]
      have hwalk : ∀ t : ℕ, 1 + t ≤ k →
          sameOrbit φ' (Sum.inl ((φ ^ 1) d_a)) (Sum.inl ((φ ^ (1 + t)) d_a)) := by
        intro t
        induction t with
        | zero => intro _; exact sameOrbit_refl _ _
        | succ t iht =>
          intro hle
          have hprev := iht (by omega)
          have hna : (φ ^ (1 + t)) d_a ≠ d_a := hm_min _ (by omega) (by omega)
          have hnb : (φ ^ (1 + t)) d_a ≠ d_b := hk_min _ (by omega) (by omega)
          have hstep : φ' (Sum.inl ((φ ^ (1 + t)) d_a)) = Sum.inl ((φ ^ (1 + (t + 1))) d_a) := by
            rw [h_other _ hna hnb, ← Equiv.Perm.mul_apply, ← pow_succ']
            rfl
          exact sameOrbit_trans _ hprev ⟨1, by simp [hstep]⟩
      have hj_eq : j = 1 + (j - 1) := by omega
      rw [hj_eq]
      exact sameOrbit_trans _ hstart (hwalk (j - 1) (by omega))
  have h1_closed : ∀ x ∈ orb1, φ' x ∈ orb1 := by
    intro x hx
    simp only [orb1, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioo] at hx ⊢
    rcases hx with rfl | rfl | ⟨j, ⟨hkj, hjm⟩, rfl⟩
    · -- φ' (Sum.inr false) = Sum.inl (φ d_b) = Sum.inl ((φ^(k+1)) d_a)
      rw [h_e1]
      by_cases hkm1 : k + 1 = m
      · right; left; congr 1
        rw [← hk_eq, ← Equiv.Perm.mul_apply, ← pow_succ', hkm1, hm_eq]
      · right; right
        refine ⟨k + 1, ⟨by omega, by omega⟩, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, hk_eq]
    · left; exact h_da
    · have hna : (φ ^ j) d_a ≠ d_a := hm_min _ (by omega) hjm
      have hnb : (φ ^ j) d_a ≠ d_b := fun h => by
        have := hinj_m j k hjm hkm (h.trans hk_eq.symm); omega
      rw [h_other _ hna hnb]
      by_cases hj1 : j + 1 = m
      · right; left; congr 1
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hj1, hm_eq]
      · right; right
        exact ⟨j + 1, ⟨by omega, by omega⟩, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
  have h12_disj : ¬ sameOrbit φ' (Sum.inl d_a) (Sum.inl d_b) := by
    rintro ⟨r, hr⟩
    have hmem : ∀ t : ℕ, (φ' ^ t) (Sum.inl d_a) ∈ orb1 := by
      intro t; induction t with
      | zero => simp [orb1]
      | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply]; exact h1_closed _ iht
    have hdb_in := hr ▸ hmem r
    simp only [orb1, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioo, Sum.inl.injEq,
      reduceCtorEq, false_or] at hdb_in
    rcases hdb_in with h1 | ⟨j, ⟨hkj, hjm⟩, h2⟩
    · exact hne h1.symm
    · have := hinj_m j k hjm hkm (h2.trans hk_eq.symm); omega
  -- Helper: any d with ¬ sameOrbit φ d d_a has its φ-orbit preserved by φ'
  have hout_eq : ∀ d : D, ¬ sameOrbit φ d d_a → ∀ t : ℕ, (φ' ^ t) (Sum.inl d) = Sum.inl ((φ ^ t) d) := by
    intro d hd t
    induction t with
    | zero => rfl
    | succ t iht =>
      rw [pow_succ', Equiv.Perm.mul_apply, iht, pow_succ', Equiv.Perm.mul_apply]
      have hna : (φ ^ t) d ≠ d_a := fun h => hd ⟨t, h⟩
      have hnb : (φ ^ t) d ≠ d_b := fun h =>
        hd (sameOrbit_trans φ ⟨t, h⟩ (sameOrbit_symm φ hsame))
      exact h_other _ hna hnb
  -- Now construct a bijection: Quotient (orbitSetoid φ') ≃ Option (Quotient (orbitSetoid φ))
  -- Wait: even simpler! Quotient (orbitSetoid φ') ≃ Quotient (orbitSetoid φ) ⊕ Unit,
  -- mapping [Sum.inl d_b] ↦ Sum.inr () and every other orbit to its φ-orbit!
  let q_da : Quotient (orbitSetoid φ) := Quotient.mk _ d_a
  let q'_da : Quotient (orbitSetoid φ') := Quotient.mk _ (Sum.inl d_a)
  let q'_db : Quotient (orbitSetoid φ') := Quotient.mk _ (Sum.inl d_b)
  have hq'_ne : q'_da ≠ q'_db := fun h => h12_disj (Quotient.exact h)
  -- Show every x : D ⊕ Bool in the φ-orbit of d_a is in q'_da or q'_db
  have hC0_cover : ∀ d : D, sameOrbit φ d_a d →
      Quotient.mk (orbitSetoid φ') (Sum.inl d) = q'_da ∨
      Quotient.mk (orbitSetoid φ') (Sum.inl d) = q'_db := by
    intro d hd
    obtain ⟨t, rfl⟩ := hd
    have hrem : (φ ^ (t % m)) d_a = (φ ^ t) d_a := by
      have hdiv : ∀ q r, (φ ^ (m * q + r)) d_a = (φ ^ r) d_a := by
        intro q r; induction q with
        | zero => simp
        | succ q ihq =>
          have : m * (q + 1) + r = m + (m * q + r) := by ring
          rw [this, pow_add, Equiv.Perm.mul_apply, ihq, ← Equiv.Perm.mul_apply, ← pow_add,
            add_comm, pow_add, Equiv.Perm.mul_apply, hm_eq]
      rw [← hdiv (t / m) (t % m), Nat.div_add_mod]
    rw [← hrem]
    set r := t % m
    have hr : r < m := Nat.mod_lt t hm_pos
    by_cases hr0 : r = 0
    · left; rw [hr0]; rfl
    · by_cases hrk : r ≤ k
      · right
        have hmem : Sum.inl ((φ ^ r) d_a) ∈ orb2 := by
          simp only [orb2, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioc]
          right; exact ⟨r, ⟨by omega, hrk⟩, rfl⟩
        exact Quotient.sound (sameOrbit_symm φ' (h2_reach _ hmem))
      · left
        have hmem : Sum.inl ((φ ^ r) d_a) ∈ orb1 := by
          simp only [orb1, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioo]
          right; right; exact ⟨r, ⟨by omega, hr⟩, rfl⟩
        exact Quotient.sound (sameOrbit_symm φ' (h1_reach _ hmem))
  -- Map f : Quotient (orbitSetoid φ') → Quotient (orbitSetoid φ)
  let f : Quotient (orbitSetoid φ') → Quotient (orbitSetoid φ) :=
    Quotient.lift
      (fun x : D ⊕ Bool => match x with
        | Sum.inl d => Quotient.mk _ d
        | Sum.inr _ => q_da)
      (by
        intro x y hxy
        -- Enough to check one step y = φ' x, by induction on k
        obtain ⟨t, rfl⟩ := hxy
        induction t generalizing x with
        | zero => rfl
        | succ t iht =>
          have h1 : (match x with | Sum.inl d => Quotient.mk (orbitSetoid φ) d | Sum.inr _ => q_da) =
              (match φ' x with | Sum.inl d => Quotient.mk (orbitSetoid φ) d | Sum.inr _ => q_da) := by
            rcases x with d | b
            · by_cases h1 : d = d_a
              · subst h1; rw [h_da]
              · by_cases h2 : d = d_b
                · subst h2; rw [h_db]; exact Quotient.sound (sameOrbit_symm φ hsame)
                · rw [h_other d h1 h2]; exact Quotient.sound (sameOrbit_step φ d)
            · cases b
              · rw [h_e1]; exact Quotient.sound (sameOrbit_trans φ hsame (sameOrbit_step φ d_b))
              · rw [h_e2]; exact Quotient.sound (sameOrbit_step φ d_a)
          rw [h1]
          have : (φ' ^ (t + 1)) x = (φ' ^ t) (φ' x) := by rw [pow_add, pow_one, Equiv.Perm.mul_apply]
          rw [this]
          exact iht (φ' x))
  -- Show f restricts to a bijection {q' // q' ≠ q'_db} ≃ Quotient (orbitSetoid φ)
  have hbij : Function.Bijective (fun q : {q : Quotient (orbitSetoid φ') // q ≠ q'_db} => f q.1) := by
    constructor
    · intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ hf
      apply Subtype.ext
      induction q₁ using Quotient.ind with | _ x₁ =>
      induction q₂ using Quotient.ind with | _ x₂ =>
      -- Classify x₁, x₂ as in orb(d_a) or outside
      have hclass : ∀ x : D ⊕ Bool, Quotient.mk (orbitSetoid φ') x ≠ q'_db →
          (f (Quotient.mk _ x) = q_da → Quotient.mk (orbitSetoid φ') x = q'_da) ∧
          (∀ d : D, x = Sum.inl d → ¬ sameOrbit φ d d_a → f (Quotient.mk _ x) = Quotient.mk _ d) := by
        intro x hx
        refine ⟨fun hfx => ?_, fun d hd _ => by subst hd; rfl⟩
        rcases x with d | b
        · have hsd : sameOrbit φ d_a d := sameOrbit_symm φ (Quotient.exact hfx)
          exact (hC0_cover d hsd).resolve_right hx
        · cases b
          · exact Quotient.sound (sameOrbit_symm φ' ⟨1, by simp [h_da]⟩)
          · exfalso; exact hx (Quotient.sound (sameOrbit_symm φ' ⟨1, by simp [h_db]⟩))
      by_cases h1 : f (Quotient.mk _ x₁) = q_da
      · have h2 : f (Quotient.mk _ x₂) = q_da := hf.symm.trans h1
        exact ((hclass x₁ hq₁).1 h1).trans ((hclass x₂ hq₂).1 h2).symm
      · rcases x₁ with d₁ | b₁
        · rcases x₂ with d₂ | b₂
          · have hnd₁ : ¬ sameOrbit φ d₁ d_a := fun h => h1 (Quotient.sound h)
            have h12 : sameOrbit φ d₁ d₂ := Quotient.exact hf
            obtain ⟨t, rfl⟩ := h12
            exact Quotient.sound ⟨t, hout_eq d₁ hnd₁ t⟩
          · exact (h1 hf).elim
        · exact (h1 rfl).elim
    · intro q
      induction q using Quotient.ind with | _ d =>
      by_cases hd : sameOrbit φ d_a d
      · exact ⟨⟨q'_da, hq'_ne⟩, Quotient.sound hd⟩
      · have hne_db : Quotient.mk (orbitSetoid φ') (Sum.inl d) ≠ q'_db := by
          intro h
          have : f (Quotient.mk _ (Sum.inl d)) = f q'_db := congrArg f h
          have : sameOrbit φ d d_b := Quotient.exact this
          exact hd (sameOrbit_symm φ (sameOrbit_trans φ this (sameOrbit_symm φ hsame)))
        exact ⟨⟨Quotient.mk _ (Sum.inl d), hne_db⟩, rfl⟩
  unfold numOrbits
  haveI : Fintype (Quotient (orbitSetoid φ')) := Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitSetoid φ)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hsplit : Fintype.card (Quotient (orbitSetoid φ')) =
      Fintype.card {q : Quotient (orbitSetoid φ') // q ≠ q'_db} + 1 := by
    have h1 : Fintype.card {q : Quotient (orbitSetoid φ') // q ≠ q'_db} =
        Fintype.card (Quotient (orbitSetoid φ')) - Fintype.card {q : Quotient (orbitSetoid φ') // q = q'_db} :=
      Fintype.card_subtype_compl (fun q : Quotient (orbitSetoid φ') => q = q'_db)
    have hle := Fintype.card_subtype_le (fun q : Quotient (orbitSetoid φ') => q = q'_db)
    have h2 : Fintype.card {q : Quotient (orbitSetoid φ') // q = q'_db} = 1 := Fintype.card_unique
    omega
  rw [hsplit]
  congr 1
  exact Fintype.card_of_bijective hbij

end GraphComb

/- ## Section 2: 2D Unit-Distance Geometry, Generic Rotation, and Non-Crossing -/

section Geom2D

/-- Chord gap lemma (adapted from PackingDeficit): two unit complex numbers at distance ≥ 1
    have arguments differing by at least `π / 3` and at most `5π / 3`. -/
private lemma chord_gap {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hd : 1 ≤ ‖x - y‖) (harg : x.arg ≤ y.arg) :
    Real.pi / 3 ≤ y.arg - x.arg ∧ y.arg - x.arg ≤ 5 * Real.pi / 3 := by
  have hxr : x.re = Real.cos x.arg := by rw [← Complex.norm_mul_cos_arg, hx, one_mul]
  have hxi : x.im = Real.sin x.arg := by rw [← Complex.norm_mul_sin_arg, hx, one_mul]
  have hyr : y.re = Real.cos y.arg := by rw [← Complex.norm_mul_cos_arg, hy, one_mul]
  have hyi : y.im = Real.sin y.arg := by rw [← Complex.norm_mul_sin_arg, hy, one_mul]
  have hcos : Real.cos (y.arg - x.arg) ≤ 1 / 2 := by
    have hsq : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hxr, hxi, hyr, hyi] at hsq
    rw [Real.cos_sub]
    nlinarith only [hsq, Real.sin_sq_add_cos_sq x.arg, Real.sin_sq_add_cos_sq y.arg]
  have hπ := Real.pi_pos
  have hid : Real.cos (2 * Real.pi - (y.arg - x.arg)) = Real.cos (y.arg - x.arg) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
  constructor
  · by_contra! H
    have hlt := Real.strictAntiOn_cos
      (show y.arg - x.arg ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩) H
    rw [Real.cos_pi_div_three] at hlt; linarith
  · by_contra! H
    have hlt := Real.strictAntiOn_cos
      (show 2 * Real.pi - (y.arg - x.arg) ∈ Set.Icc 0 Real.pi from
        ⟨by linarith [Complex.arg_le_pi y, Complex.neg_pi_lt_arg x], by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show 2 * Real.pi - (y.arg - x.arg) < Real.pi / 3 by linarith)
    rw [Real.cos_pi_div_three, hid] at hlt; linarith

private lemma unit_neighbors_le_six {A : Type*} (S : Finset A) (u : A → ℂ)
    (hnorm : ∀ a ∈ S, ‖u a‖ = 1)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ ‖u a - u b‖) :
    S.card ≤ 6 := by
  classical
  let s := S.image fun a => (u a).arg
  have hinj : Set.InjOn (fun a => (u a).arg) ↑S := by
    intro a ha b hb hab
    change (u a).arg = (u b).arg at hab
    by_contra H
    apply not_le_of_gt (by norm_num : (0 : ℝ) < 1)
    have heq : u a = u b :=
      Complex.ext
        (by rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_cos_arg, hnorm _ ha, hnorm _ hb, hab])
        (by rw [← Complex.norm_mul_sin_arg, ← Complex.norm_mul_sin_arg, hnorm _ ha, hnorm _ hb, hab])
    simpa [heq] using hsep a ha b hb H
  have hcard : s.card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  by_contra! H
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq (show 7 ≤ s.card by omega)
  let g := t.orderEmbOfFin htcard
  have gap {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
      Real.pi / 3 ≤ y - x ∧ y - x ≤ 5 * Real.pi / 3 := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact chord_gap (hnorm _ ha) (hnorm _ hb)
      (hsep a ha b hb (fun h => hxy.ne (congrArg (fun z => (u z).arg) h))) hxy.le
  have gg (i j : Fin 7) (h : i < j) :=
    gap (ht (t.orderEmbOfFin_mem htcard i)) (ht (t.orderEmbOfFin_mem htcard j)) (g.strictMono h)
  linarith only [(gg 0 1 (by decide)).1, (gg 1 2 (by decide)).1, (gg 2 3 (by decide)).1,
    (gg 3 4 (by decide)).1, (gg 4 5 (by decide)).1, (gg 5 6 (by decide)).1,
    (gg 0 6 (by decide)).2, Real.pi_pos]

/-- Generic unit rotation: for any finite `S : Finset ℂ`, there exists `ω : ℂ` with `‖ω‖ = 1`
    such that all rotated points `ω * z` (`z ∈ S`) have pairwise distinct real parts. -/
private lemma exists_generic_unit_rot (S : Finset ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (ω * x).re ≠ (ω * y).re := by
  classical
  let u (t : ℝ) : ℂ := ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩
  have hu_norm (t : ℝ) : ‖u t‖ = 1 := by
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    have h1 : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
      field_simp; ring
    simp only [u, h1, Real.sqrt_one]
  let poly (z : ℂ) : Polynomial ℝ :=
    Polynomial.C (-z.re) * Polynomial.X ^ 2 + Polynomial.C (-2 * z.im) * Polynomial.X +
      Polynomial.C z.re
  have hpoly_ne (z : ℂ) (hz : z ≠ 0) : poly z ≠ 0 := by
    intro h0
    have hc0 : (poly z).coeff 0 = 0 := by rw [h0]; simp
    have hc1 : (poly z).coeff 1 = 0 := by rw [h0]; simp
    simp only [poly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at hc0 hc1
    norm_num at hc0 hc1
    exact hz (Complex.ext hc0 hc1)
  let bad : Finset ℝ := S.offDiag.biUnion (fun p => (poly (p.1 - p.2)).roots.toFinset)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨u t, hu_norm t, fun x hx y hy hxy hre => ?_⟩
  have hmem : (x, y) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hre' : (u t * (x - y)).re = 0 := by
    rw [mul_sub, Complex.sub_re]; linarith
  have heval : (poly (x - y)).eval t = 0 := by
    simp only [poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    simp only [Complex.mul_re, u] at hre'
    have hmul : (1 + t ^ 2) * ((1 - t ^ 2) / (1 + t ^ 2) * (x - y).re -
        2 * t / (1 + t ^ 2) * (x - y).im) = 0 := by rw [hre', mul_zero]
    have hden : (1 + t ^ 2) ≠ 0 := ne_of_gt hpos
    have hsim : (1 - t ^ 2) * (x - y).re - 2 * t * (x - y).im = 0 := by
      field_simp [hden] at hmul; linarith
    linarith
  have hroot : t ∈ (poly (x - y)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hpoly_ne _ (sub_ne_zero.mpr hxy))]
    exact heval
  exact ht (Finset.mem_biUnion.mpr ⟨(x, y), hmem, hroot⟩)

/-- No third point of a 1-separated set lies on a closed unit segment. -/
private lemma not_on_closed_unit_seg {a b c : ℂ}
    (hab : ‖a - b‖ = 1) (hac : 1 ≤ ‖a - c‖) (hbc : 1 ≤ ‖b - c‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : c = (1 - t) • a + t • b) : False := by
  have h1 : c - a = t • (b - a) := by
    rw [heq, Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
  have h2 : b - c = (1 - t) • (b - a) := by
    rw [heq, Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
  have hn1 : ‖a - c‖ = t := by
    rw [norm_sub_rev, h1, norm_smul, Real.norm_of_nonneg ht0, norm_sub_rev, hab, mul_one]
  have hn2 : ‖b - c‖ = 1 - t := by
    rw [h2, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hab, mul_one]
  linarith

/-- Two vertex-disjoint unit segments in a 1-separated set cannot intersect (parallelogram law). -/
private lemma no_unit_seg_crossing {a b c d : ℂ}
    (hab : ‖a - b‖ = 1) (hcd : ‖c - d‖ = 1)
    (hac : 1 ≤ ‖a - c‖) (hcb : 1 ≤ ‖c - b‖) (hbd : 1 ≤ ‖b - d‖) (hda : 1 ≤ ‖d - a‖)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : (1 - s) • a + s • b = (1 - t) • c + t • d) : False := by
  set q : ℂ := (1 - s) • a + s • b
  have haq : ‖a - q‖ = s := by
    have : a - q = s • (a - b) := by
      simp only [q, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg hs0, hab, mul_one]
  have hbq : ‖b - q‖ = 1 - s := by
    have : b - q = (1 - s) • (b - a) := by
      simp only [q, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hab, mul_one]
  have hcq : ‖c - q‖ = t := by
    have : c - q = t • (c - d) := by
      simp only [q, heq, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg ht0, hcd, mul_one]
  have hdq : ‖d - q‖ = 1 - t := by
    have : d - q = (1 - t) • (d - c) := by
      simp only [q, heq, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hcd, mul_one]
  have t1 : 1 ≤ s + t := by
    calc (1 : ℝ) ≤ ‖a - c‖ := hac
      _ = ‖(a - q) + (q - c)‖ := by ring_nf
      _ ≤ ‖a - q‖ + ‖q - c‖ := norm_add_le _ _
      _ = s + t := by rw [haq, norm_sub_rev, hcq]
  have t2 : 1 ≤ t + (1 - s) := by
    calc (1 : ℝ) ≤ ‖c - b‖ := hcb
      _ = ‖(c - q) + (q - b)‖ := by ring_nf
      _ ≤ ‖c - q‖ + ‖q - b‖ := norm_add_le _ _
      _ = t + (1 - s) := by rw [hcq, norm_sub_rev, hbq]
  have t3 : 1 ≤ (1 - s) + (1 - t) := by
    calc (1 : ℝ) ≤ ‖b - d‖ := hbd
      _ = ‖(b - q) + (q - d)‖ := by ring_nf
      _ ≤ ‖b - q‖ + ‖q - d‖ := norm_add_le _ _
      _ = (1 - s) + (1 - t) := by rw [hbq, norm_sub_rev, hdq]
  have t4 : 1 ≤ (1 - t) + s := by
    calc (1 : ℝ) ≤ ‖d - a‖ := hda
      _ = ‖(d - q) + (q - a)‖ := by ring_nf
      _ ≤ ‖d - q‖ + ‖q - a‖ := norm_add_le _ _
      _ = (1 - t) + s := by rw [hdq, norm_sub_rev, haq]
  have hs_half : s = 1 / 2 := by linarith
  have ht_half : t = 1 / 2 := by linarith
  -- Now u = a - q, v = c - q satisfy ‖u‖ = ‖v‖ = 1/2, a - c = u - v, a - d = u + v
  let u := a - q
  let v := c - q
  have hu : ‖u‖ = 1 / 2 := by rw [haq, hs_half]
  have hv : ‖v‖ = 1 / 2 := by rw [hcq, ht_half]
  have huv_sub : 1 ≤ ‖u - v‖ := by
    have : u - v = a - c := by simp only [u, v]; ring
    rw [this]; exact hac
  have huv_add : 1 ≤ ‖u + v‖ := by
    have hd_eq : d - q = -v := by
      have : (d - q) + (c - q) = 0 := by
        simp only [q, heq, ht_half, Complex.real_smul]; push_cast; ring
      exact eq_neg_of_add_eq_zero_left this
    have : u + v = a - d := by
      calc u + v = (a - q) - (d - q) := by rw [hd_eq]; ring
        _ = a - d := by ring
    rw [this, norm_sub_rev]; exact hda
  have hpara : ‖u - v‖ ^ 2 + ‖u + v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    ring
  have hsub2 : 1 ≤ ‖u - v‖ ^ 2 := by nlinarith
  have hadd2 : 1 ≤ ‖u + v‖ ^ 2 := by nlinarith
  rw [hu, hv] at hpara
  linarith

/-- Linear y-value along the line through `p a` and `p b` at x-coordinate `x`. -/
private noncomputable def edgeY {V : Type*} (p : V → ℂ) (a b : V) (x : ℝ) : ℝ :=
  (p a).im + ((p b).im - (p a).im) * ((x - (p a).re) / ((p b).re - (p a).re))

private lemma edgeY_point_eq {V : Type*} (p : V → ℂ) {a b : V} (hab : (p a).re < (p b).re) (x : ℝ) :
    let t := (x - (p a).re) / ((p b).re - (p a).re)
    (⟨x, edgeY p a b x⟩ : ℂ) = (1 - t) • p a + t • p b := by
  intro t
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, t]
    field_simp [hne]; ring
  · simp only [edgeY, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, t]
    ring

private lemma edgeY_at_left {V : Type*} (p : V → ℂ) (a b : V) :
    edgeY p a b (p a).re = (p a).im := by
  simp [edgeY]

private lemma edgeY_at_right {V : Type*} (p : V → ℂ) {a b : V} (hab : (p a).re < (p b).re) :
    edgeY p a b (p b).re = (p b).im := by
  unfold edgeY
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  rw [div_self hne, mul_one]; ring

/-- Slope of an edge `(a, b)` with `(p a).re < (p b).re`. -/
private noncomputable def edgeSlope {V : Type*} (p : V → ℂ) (a b : V) : ℝ :=
  ((p b).im - (p a).im) / ((p b).re - (p a).re)

private lemma edgeY_eq_left_add_slope {V : Type*} (p : V → ℂ) (a b : V) (x : ℝ) :
    edgeY p a b x = (p a).im + edgeSlope p a b * (x - (p a).re) := by
  unfold edgeY edgeSlope; ring

private lemma edgeY_eq_right_sub_slope {V : Type*} (p : V → ℂ) {a b : V}
    (hab : (p a).re < (p b).re) (x : ℝ) :
    edgeY p a b x = (p b).im - edgeSlope p a b * ((p b).re - x) := by
  unfold edgeY edgeSlope
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne]; ring

end Geom2D

/- ## Section 3: Heading Angle `ψ`, Geometric Rotation System, and Telescoping -/

section HeadingAndRot

/-- Heading angle `ψ(z) ∈ (-π/2, 3π/2)` for `z : ℂ` with `z.re ≠ 0`:
    `(-π/2, π/2)` when `z.re > 0`, and `(π/2, 3π/2)` when `z.re < 0`. -/
private noncomputable def heading (z : ℂ) : ℝ :=
  if 0 < z.re then z.arg
  else if 0 ≤ z.arg then z.arg else z.arg + 2 * Real.pi

private lemma cos_heading {z : ℂ} (hz : z ≠ 0) : Real.cos (heading z) = z.re / ‖z‖ := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.cos z.arg = z.re / ‖z‖ := by
    rw [eq_div_iff (ne_of_gt hpos), mul_comm, Complex.norm_mul_cos_arg]
  unfold heading
  split_ifs
  · exact h1
  · exact h1
  · rw [Real.cos_add_two_pi]; exact h1

private lemma sin_heading {z : ℂ} (hz : z ≠ 0) : Real.sin (heading z) = z.im / ‖z‖ := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.sin z.arg = z.im / ‖z‖ := by
    rw [eq_div_iff (ne_of_gt hpos), mul_comm, Complex.norm_mul_sin_arg]
  unfold heading
  split_ifs
  · exact h1
  · exact h1
  · rw [Real.sin_add_two_pi]; exact h1

private lemma heading_bounds_pos {z : ℂ} (hz : 0 < z.re) :
    -(Real.pi / 2) < heading z ∧ heading z < Real.pi / 2 := by
  unfold heading
  rw [if_pos hz]
  have hcos : 0 < Real.cos z.arg := by
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by simp [h] at hz)
    have : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
    nlinarith
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  constructor
  · by_contra! hle
    have : Real.cos z.arg ≤ 0 := by
      have : -z.arg ∈ Set.Icc (Real.pi / 2) Real.pi := ⟨by linarith, by linarith⟩
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le this.1 (by linarith)
    linarith
  · by_contra! hle
    have : Real.cos z.arg ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith)
    linarith

private lemma heading_bounds_neg {z : ℂ} (hz : z.re < 0) :
    Real.pi / 2 < heading z ∧ heading z < 3 * Real.pi / 2 := by
  have hne : z ≠ 0 := fun h => by simp [h] at hz
  have hcos : Real.cos z.arg < 0 := by
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hne
    have : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
    nlinarith
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  unfold heading
  rw [if_neg (not_lt.mpr hz.le)]
  split_ifs with h0
  · constructor
    · by_contra! hle
      have : 0 ≤ Real.cos z.arg := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩
      linarith
    · linarith [Real.pi_pos]
  · push_neg at h0
    constructor
    · linarith [Real.pi_pos]
    · by_contra! hge
      have : 0 ≤ Real.cos z.arg := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith

private lemma heading_neg_of_pos {z : ℂ} (hz : 0 < z.re) :
    heading (-z) = heading z + Real.pi := by
  have hnz : (-z).re < 0 := by simp [hz]
  have h1 := heading_bounds_pos hz
  have h2 := heading_bounds_neg hnz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hcos : Real.cos (heading (-z)) = Real.cos (heading z + Real.pi) := by
    rw [Real.cos_add_pi, cos_heading (neg_ne_zero.mpr hz0), cos_heading hz0,
      Complex.neg_re, norm_neg, neg_div]
  have hsin : Real.sin (heading (-z)) = Real.sin (heading z + Real.pi) := by
    rw [Real.sin_add_pi, sin_heading (neg_ne_zero.mpr hz0), sin_heading hz0,
      Complex.neg_im, norm_neg, neg_div]
  -- Both heading (-z) and heading z + π lie in (π/2, 3π/2), where sin is strictly decreasing!
  have hlt1 : heading (-z) - Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hlt2 : heading z ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hsin' : Real.sin (heading (-z) - Real.pi) = Real.sin (heading z) := by
    rw [Real.sin_sub_pi, hsin, Real.sin_add_pi, neg_neg]
  have heq := Real.strictMonoOn_sin.injOn hlt1 hlt2 hsin'
  linarith

private lemma heading_neg_of_neg {z : ℂ} (hz : z.re < 0) :
    heading (-z) = heading z - Real.pi := by
  have hp : 0 < (-z).re := by simp [hz]
  have h := heading_neg_of_pos hp
  rw [neg_neg] at h
  linarith

private lemma heading_lt_iff_slope_pos {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) :
    heading z₁ < heading z₂ ↔ z₁.im / z₁.re < z₂.im / z₂.re := by
  have hb1 := heading_bounds_pos h1
  have hb2 := heading_bounds_pos h2
  have hz1 : z₁ ≠ 0 := fun h => by simp [h] at h1
  have hz2 : z₂ ≠ 0 := fun h => by simp [h] at h2
  have htan (z : ℂ) (hz : 0 < z.re) : Real.tan (heading z) = z.im / z.re := by
    have hne : z ≠ 0 := fun h => by simp [h] at hz
    rw [Real.tan_eq_sin_div_cos, sin_heading hne, cos_heading hne,
      div_div_div_cancel_right₀ (ne_of_gt (norm_pos_iff.mpr hne))]
  rw [← htan z₁ h1, ← htan z₂ h2]
  exact ⟨fun h => Real.strictMonoOn_tan hb1 hb2 h, fun h => by
    by_contra! hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · rw [heq] at h; exact lt_irrefl _ h
    · exact not_lt.mpr (Real.strictMonoOn_tan hb2 hb1 hgt).le h⟩

private lemma heading_lt_iff_slope_neg {z₁ z₂ : ℂ} (h1 : z₁.re < 0) (h2 : z₂.re < 0) :
    heading z₁ < heading z₂ ↔ z₁.im / z₁.re < z₂.im / z₂.re := by
  have h1' : 0 < (-z₁).re := by simp [h1]
  have h2' : 0 < (-z₂).re := by simp [h2]
  have heq : heading z₁ < heading z₂ ↔ heading (-z₁) < heading (-z₂) := by
    rw [heading_neg_of_neg h1, heading_neg_of_neg h2]; constructor <;> intro h <;> linarith
  rw [heq, heading_lt_iff_slope_pos h1' h2']
  simp [neg_div_neg_eq]

private lemma heading_gap_ge_pi_div_three {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hd : 1 ≤ ‖x - y‖)
    (hxre : x.re ≠ 0) (hyre : y.re ≠ 0) (hlt : heading x < heading y) :
    Real.pi / 3 ≤ heading y - heading x ∧ heading y - heading x ≤ 5 * Real.pi / 3 := by
  -- Use cos(heading y - heading x) ≤ 1/2, identical to chord_gap!
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hxr : x.re = Real.cos (heading x) := by rw [cos_heading hx0, hx, div_one]
  have hxi : x.im = Real.sin (heading x) := by rw [sin_heading hx0, hx, div_one]
  have hyr : y.re = Real.cos (heading y) := by rw [cos_heading hy0, hy, div_one]
  have hyi : y.im = Real.sin (heading y) := by rw [sin_heading hy0, hy, div_one]
  have hcos : Real.cos (heading y - heading x) ≤ 1 / 2 := by
    have hsq : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hxr, hxi, hyr, hyi] at hsq
    rw [Real.cos_sub]
    nlinarith only [hsq, Real.sin_sq_add_cos_sq (heading x), Real.sin_sq_add_cos_sq (heading y)]
  have hb (z : ℂ) (hz : z.re ≠ 0) : -(Real.pi / 2) < heading z ∧ heading z < 3 * Real.pi / 2 := by
    rcases lt_or_gt_of_ne hz with h | h
    · have := heading_bounds_neg h; exact ⟨by linarith [Real.pi_pos], this.2⟩
    · have := heading_bounds_pos h; exact ⟨this.1, by linarith [Real.pi_pos]⟩
  have hbx := hb x hxre
  have hby := hb y hyre
  have hπ := Real.pi_pos
  have hid : Real.cos (2 * Real.pi - (heading y - heading x)) = Real.cos (heading y - heading x) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
  constructor
  · by_contra! H
    have hlt' := Real.strictAntiOn_cos
      (show heading y - heading x ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩) H
    rw [Real.cos_pi_div_three] at hlt'; linarith
  · by_contra! H
    have hlt' := Real.strictAntiOn_cos
      (show 2 * Real.pi - (heading y - heading x) ∈ Set.Icc 0 Real.pi from
        ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show 2 * Real.pi - (heading y - heading x) < Real.pi / 3 by linarith)
    rw [Real.cos_pi_div_three, hid] at hlt'; linarith

/-- Simple cyclic predecessor permutation on `Fin n` (0 ↦ n-1, i+1 ↦ i). -/
private def finPredPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  if h : 0 < n then
    { toFun := fun i => if hi : i.val = 0 then ⟨n - 1, by omega⟩ else ⟨i.val - 1, by omega⟩
      invFun := fun i => if hi : i.val + 1 = n then ⟨0, h⟩ else ⟨i.val + 1, by omega⟩
      left_inv := fun i => by
        apply Fin.ext; dsimp only
        rcases Nat.eq_zero_or_pos i.val with hi | hi
        · simp only [hi, ↓reduceDIte, Fin.val_mk, Nat.sub_add_cancel h]
        · have hne : i.val ≠ 0 := by omega
          simp only [hne, ↓reduceDIte, Fin.val_mk]
          have hne2 : i.val - 1 + 1 ≠ n := by omega
          simp only [hne2, ↓reduceDIte, Fin.val_mk]
          omega
      right_inv := fun i => by
        apply Fin.ext; dsimp only
        by_cases hi : i.val + 1 = n
        · simp only [hi, ↓reduceDIte, Fin.val_mk]
          omega
        · simp only [hi, ↓reduceDIte, Fin.val_mk]
          have hne2 : i.val + 1 ≠ 0 := by omega
          simp only [hne2, ↓reduceDIte, Fin.val_mk]
          omega }
  else Equiv.refl _

private lemma finPredPerm_apply_zero {n : ℕ} (h : 0 < n) (i : Fin n) (hi : i.val = 0) :
    (finPredPerm n i).val = n - 1 := by
  unfold finPredPerm; rw [dif_pos h]; simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]

private lemma finPredPerm_apply_pos {n : ℕ} (h : 0 < n) (i : Fin n) (hi : 0 < i.val) :
    (finPredPerm n i).val = i.val - 1 := by
  unfold finPredPerm; rw [dif_pos h]
  have hne : i.val ≠ 0 := by omega
  simp only [Equiv.coe_fn_mk, hne, ↓reduceDIte]

private lemma finPredPerm_isCyclic (n : ℕ) : IsCyclicPerm (finPredPerm n) := by
  intro x y
  have hpos : 0 < n := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 x)
  -- First show any i reaches ⟨0, hpos⟩ in i.val steps, and ⟨0, hpos⟩ reaches any j in (n - j.val) steps!
  have hto0 : ∀ k : ℕ, ∀ i : Fin n, i.val = k → sameOrbit (finPredPerm n) i ⟨0, hpos⟩ := by
    intro k; induction k with
    | zero => intro i hi; exact ⟨0, Fin.ext hi⟩
    | succ k ihk =>
      intro i hi
      have h1 : (finPredPerm n i).val = k := by rw [finPredPerm_apply_pos hpos i (by omega)]; omega
      exact sameOrbit_trans _ (sameOrbit_step _ i) (ihk (finPredPerm n i) h1)
  have hfrom0 : ∀ d : ℕ, ∀ j : Fin n, n - 1 - j.val = d → sameOrbit (finPredPerm n) ⟨n - 1, by omega⟩ j := by
    intro d; induction d with
    | zero =>
      intro j hj; exact ⟨0, Fin.ext (by simp; omega)⟩
    | succ d ihd =>
      intro j hj
      have hjlt : j.val + 1 < n := by omega
      let j1 : Fin n := ⟨j.val + 1, hjlt⟩
      have hprev : finPredPerm n j1 = j := by
        apply Fin.ext; rw [finPredPerm_apply_pos hpos j1 (by simp [j1])]; simp [j1]
      have h1 := ihd j1 (by simp [j1]; omega)
      exact sameOrbit_trans _ h1 ⟨1, by simp [hprev]⟩
  have hx0 := hto0 x.val x rfl
  have h0last : sameOrbit (finPredPerm n) ⟨0, hpos⟩ ⟨n - 1, by omega⟩ :=
    ⟨1, Fin.ext (by simpa using finPredPerm_apply_zero hpos ⟨0, hpos⟩ rfl)⟩
  have hlasty := hfrom0 (n - 1 - y.val) y rfl
  exact sameOrbit_trans _ hx0 (sameOrbit_trans _ h0last hlasty)

/-- Clockwise predecessor permutation on a finite nonempty type `A` sorted by an injective `f : A → ℝ`.
    Maps the `j`-th smallest element (for `j > 0`) to the `(j-1)`-th, and the 0-th to the largest. -/
private noncomputable def cwPredEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) : A ≃ Fin (Fintype.card A) := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hcard : s.card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let emb : Fin (Fintype.card A) ↪o ℝ := s.orderEmbOfFin hcard
  have hmem : ∀ a : A, f a ∈ Set.range emb := by
    intro a; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem f (Finset.mem_univ a)
  let toFin : A → Fin (Fintype.card A) := fun a => Classical.choose (hmem a)
  have htoFin : ∀ a : A, emb (toFin a) = f a := fun a => Classical.choose_spec (hmem a)
  have hbij : Function.Bijective toFin :=
    (Fintype.bijective_iff_injective_and_card toFin).mpr
      ⟨fun a b h => hinj ((htoFin a).symm.trans ((congrArg emb h).trans (htoFin b))), by simp⟩
  exact Equiv.ofBijective toFin hbij

private lemma cwPredEquiv_strictMono {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a b : A) :
    f a < f b ↔ cwPredEquiv f hinj a < cwPredEquiv f hinj b := by
  classical
  unfold cwPredEquiv
  dsimp only
  set s := Finset.univ.image f
  have hcard : s.card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let emb := s.orderEmbOfFin hcard
  have hmem : ∀ x : A, f x ∈ Set.range emb := by
    intro x; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem f (Finset.mem_univ x)
  have hspec (x : A) : emb (Classical.choose (hmem x)) = f x := Classical.choose_spec (hmem x)
  change f a < f b ↔ Classical.choose (hmem a) < Classical.choose (hmem b)
  rw [← emb.lt_iff_lt, hspec a, hspec b]

private lemma cwPredEquiv_mono {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a b : A) :
    f a ≤ f b ↔ cwPredEquiv f hinj a ≤ cwPredEquiv f hinj b := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, cwPredEquiv_strictMono f hinj, hinj.eq_iff,
    (cwPredEquiv f hinj).injective.eq_iff]

private noncomputable def cwPredPerm {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) : Equiv.Perm A :=
  let e := cwPredEquiv f hinj
  e.trans ((finPredPerm (Fintype.card A)).trans e.symm)

private lemma cwPredPerm_isCyclic {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) :
    IsCyclicPerm (cwPredPerm f hinj) := by
  intro x y
  let e := cwPredEquiv f hinj
  obtain ⟨k, hk⟩ := finPredPerm_isCyclic (Fintype.card A) (e x) (e y)
  refine ⟨k, ?_⟩
  have hconj : ∀ m : ℕ, ∀ z : A,
      ((cwPredPerm f hinj) ^ m) z = e.symm (((finPredPerm (Fintype.card A)) ^ m) (e z)) := by
    intro m; induction m with
    | zero => intro z; simp
    | succ m ihm =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply, ihm, pow_succ', Equiv.Perm.mul_apply]
      simp [cwPredPerm, e]
  rw [hconj, hk, e.symm_apply_apply]

/-- Key characterization of `cwPredPerm f`:
    - If `a` is NOT the minimizer of `f`, then `f (cwPredPerm f a) < f a` and there is NO `b`
      strictly between `f (cwPredPerm f a)` and `f a`.
    - If `a` IS the minimizer of `f`, then `cwPredPerm f a` is the MAXIMIZER of `f`. -/
private lemma cwPredPerm_spec {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a : A) :
    ((∀ b : A, f a ≤ f b) ∧ (∀ b : A, f b ≤ f (cwPredPerm f hinj a))) ∨
    (f (cwPredPerm f hinj a) < f a ∧ ∀ b : A, f (cwPredPerm f hinj a) < f b → f a ≤ f b) := by
  have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  let e := cwPredEquiv f hinj
  have he_prev : e (cwPredPerm f hinj a) = finPredPerm (Fintype.card A) (e a) := by
    simp [cwPredPerm, e]
  rcases Nat.eq_zero_or_pos (e a).val with hi0 | hipos
  · left
    have hval := finPredPerm_apply_zero hpos (e a) hi0
    constructor
    · intro b
      rw [cwPredEquiv_mono f hinj]
      change (e a).val ≤ (e b).val; omega
    · intro b
      rw [cwPredEquiv_mono f hinj]
      change (e b).val ≤ (e (cwPredPerm f hinj a)).val
      rw [he_prev, hval]; have := (e b).isLt; omega
  · right
    have hval := finPredPerm_apply_pos hpos (e a) hipos
    constructor
    · rw [cwPredEquiv_strictMono f hinj]
      change (e (cwPredPerm f hinj a)).val < (e a).val
      rw [he_prev, hval]; omega
    · intro b hb
      rw [cwPredEquiv_strictMono f hinj] at hb
      change (e (cwPredPerm f hinj a)).val < (e b).val at hb
      rw [he_prev, hval] at hb
      rw [cwPredEquiv_mono f hinj]
      change (e a).val ≤ (e b).val; omega

private lemma cwPredPerm_isMin_iff {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a : A) :
    (∀ b : A, f a ≤ f b) ↔ f a ≤ f (cwPredPerm f hinj a) := by
  rcases cwPredPerm_spec f hinj a with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
  · exact ⟨fun _ => hmin _, fun _ => hmin⟩
  · exact ⟨fun h => absurd (h _) (not_le_of_gt hlt), fun h => absurd h (not_le_of_gt hlt)⟩

private lemma cwPredPerm_ne_self {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (hcard : 2 ≤ Fintype.card A) (a : A) :
    cwPredPerm f hinj a ≠ a := by
  rcases cwPredPerm_spec f hinj a with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
  · intro heq
    rw [heq] at hmax
    have huniq : ∀ b : A, b = a := fun b => hinj (le_antisymm (hmax b) (hmin b))
    have : Fintype.card A ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => (huniq x).trans (huniq y).symm)
    omega
  · intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt

end HeadingAndRot

/- ## Section 4: Vertical Slab Trapezoid Graph `T(H)`, Squeeze, and Outer Face -/

section SlabAndSqueeze

/-- Geometric setup for a connected 1-separated unit-distance graph on `Fin n` (`n ≥ 4`),
    sorted strictly by x-coordinate. -/
private structure GeoSetup (n : ℕ) where
  hn : 4 ≤ n
  p : Fin n → ℂ
  hx_mono : StrictMono (fun i => (p i).re)
  hsep : ∀ i j : Fin n, i ≠ j → 1 ≤ ‖p i - p j‖

namespace GeoSetup

variable {n : ℕ} (S : GeoSetup n)
include S

private def G : SimpleGraph (Fin n) where
  Adj i j := ‖S.p i - S.p j‖ = 1
  symm := ⟨fun i j h => by rwa [norm_sub_rev]⟩
  loopless := ⟨fun i h => by simp at h⟩

private lemma G_adj_iff (i j : Fin n) : S.G.Adj i j ↔ ‖S.p i - S.p j‖ = 1 := Iff.rfl

private lemma re_ne {i j : Fin n} (h : i ≠ j) : (S.p i).re ≠ (S.p j).re :=
  S.hx_mono.injective.ne h

private lemma p_sub_re_ne {i j : Fin n} (h : i ≠ j) : (S.p i - S.p j).re ≠ 0 := by
  rw [Complex.sub_re]; exact sub_ne_zero.mpr (S.re_ne h)

private lemma p_sub_re_pos_iff {i j : Fin n} : 0 < (S.p i - S.p j).re ↔ j < i := by
  rw [Complex.sub_re, sub_pos]; exact S.hx_mono.lt_iff_lt

private lemma p_sub_re_neg_iff {i j : Fin n} : (S.p i - S.p j).re < 0 ↔ i < j := by
  rw [Complex.sub_re, sub_neg]; exact S.hx_mono.lt_iff_lt

private lemma heading_inj_at (v : Fin n) :
    Function.Injective (fun u : {u : Fin n // S.G.Adj v u} => heading (S.p u.1 - S.p v)) := by
  intro u₁ u₂ heq
  apply Subtype.ext
  by_contra hne
  have hsep := S.hsep u₁.1 u₂.1 hne
  have h1 : ‖S.p u₁.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact u₁.2
  have h2 : ‖S.p u₂.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact u₂.2
  have hz1 : S.p u₁.1 - S.p v ≠ 0 := fun h => by simp [h] at h1
  have hz2 : S.p u₂.1 - S.p v ≠ 0 := fun h => by simp [h] at h2
  have hvec : S.p u₁.1 - S.p v = S.p u₂.1 - S.p v := by
    apply Complex.ext
    · have c1 := cos_heading hz1; have c2 := cos_heading hz2
      rw [h1, div_one] at c1; rw [h2, div_one] at c2; linarith [congrArg Real.cos heq]
    · have s1 := sin_heading hz1; have s2 := sin_heading hz2
      rw [h1, div_one] at s1; rw [h2, div_one] at s2; linarith [congrArg Real.sin heq]
  have hp : S.p u₁.1 = S.p u₂.1 := sub_left_inj.mp hvec
  rw [hp, sub_self, norm_zero] at hsep
  norm_num at hsep

/-- Non-crossing of distinct unit edges at any shared strictly-interior x-coordinate. -/
private lemma edgeY_ne_of_ne_edges {a₁ b₁ a₂ b₂ : Fin n}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hadj₁ : S.G.Adj a₁ b₁) (hadj₂ : S.G.Adj a₂ b₂)
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    {x : ℝ} (hx₁ : (S.p a₁).re < x) (hx₂ : x < (S.p b₁).re)
    (hx₃ : (S.p a₂).re < x) (hx₄ : x < (S.p b₂).re) :
    edgeY S.p a₁ b₁ x ≠ edgeY S.p a₂ b₂ x := by
  intro hy
  have hr₁ : (S.p a₁).re < (S.p b₁).re := S.hx_mono h₁
  have hr₂ : (S.p a₂).re < (S.p b₂).re := S.hx_mono h₂
  set s := (x - (S.p a₁).re) / ((S.p b₁).re - (S.p a₁).re)
  set t := (x - (S.p a₂).re) / ((S.p b₂).re - (S.p a₂).re)
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hpt : (1 - s) • S.p a₁ + s • S.p b₁ = (1 - t) • S.p a₂ + t • S.p b₂ := by
    rw [← edgeY_point_eq S.p hr₁ x, ← edgeY_point_eq S.p hr₂ x, hy]
  -- Case split on whether endpoints overlap
  by_cases ha12 : a₁ = a₂
  · subst ha12
    have hdir : s • (S.p b₁ - S.p a₁) = t • (S.p b₂ - S.p a₁) := by
      simp only [Complex.real_smul] at hpt ⊢; push_cast at hpt ⊢; linear_combination hpt
    have hnorm := congrArg norm hdir
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs0.le, Real.norm_of_nonneg ht0.le,
      norm_sub_rev, hadj₁, norm_sub_rev, hadj₂, mul_one, mul_one] at hnorm
    rw [← hnorm] at hdir
    have hpb : S.p b₁ = S.p b₂ := by
      have : S.p b₁ - S.p a₁ = S.p b₂ - S.p a₁ := smul_right_injective ℂ (ne_of_gt hs0) hdir
      exact sub_left_inj.mp this
    have hb12 : b₁ = b₂ := S.hx_mono.injective (congrArg Complex.re hpb)
    exact hne (Prod.ext rfl hb12)
  · by_cases hb12 : b₁ = b₂
    · subst hb12
      have hdir : (1 - s) • (S.p a₁ - S.p b₁) = (1 - t) • (S.p a₂ - S.p b₁) := by
        simp only [Complex.real_smul] at hpt ⊢; push_cast at hpt ⊢; linear_combination hpt
      have hnorm := congrArg norm hdir
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith),
        hadj₁, hadj₂, mul_one, mul_one] at hnorm
      have hst : 1 - s = 1 - t := hnorm
      have hpa : S.p a₁ = S.p a₂ := by
        rw [hst] at hdir
        have : S.p a₁ - S.p b₁ = S.p a₂ - S.p b₁ := smul_right_injective ℂ (by linarith) hdir
        exact sub_left_inj.mp this
      have ha : a₁ = a₂ := S.hx_mono.injective (congrArg Complex.re hpa)
      exact ha12 ha
    · have ha1b2 : a₁ ≠ b₂ := fun h => by subst h; linarith
      have hb1a2 : b₁ ≠ a₂ := fun h => by subst h; linarith
      exact no_unit_seg_crossing hadj₁ hadj₂
        (S.hsep _ _ ha12) (S.hsep _ _ (Ne.symm hb1a2)) (S.hsep _ _ hb12) (S.hsep _ _ (Ne.symm ha1b2))
        hs0.le hs1.le ht0.le ht1.le hpt

/-- Linear interpolation preserves strict vertical order between distinct edges across their shared open interval. -/
private lemma edgeY_order_preserved {a₁ b₁ a₂ b₂ : Fin n}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hadj₁ : S.G.Adj a₁ b₁) (hadj₂ : S.G.Adj a₂ b₂)
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    {x x' : ℝ}
    (hx₁ : (S.p a₁).re < x) (hx₂ : x < (S.p b₁).re)
    (hx₃ : (S.p a₂).re < x) (hx₄ : x < (S.p b₂).re)
    (hx₁' : (S.p a₁).re < x') (hx₂' : x' < (S.p b₁).re)
    (hx₃' : (S.p a₂).re < x') (hx₄' : x' < (S.p b₂).re)
    (hlt : edgeY S.p a₁ b₁ x < edgeY S.p a₂ b₂ x) :
    edgeY S.p a₁ b₁ x' < edgeY S.p a₂ b₂ x' := by
  by_contra! hge
  have hne' := S.edgeY_ne_of_ne_edges h₁ h₂ hadj₁ hadj₂ hne hx₁' hx₂' hx₃' hx₄'
  have hgt : edgeY S.p a₂ b₂ x' < edgeY S.p a₁ b₁ x' := lt_of_le_of_ne hge (Ne.symm hne')
  -- Affine difference f(t) = edgeY₁(t) - edgeY₂(t) has f(x) < 0 < f(x'), so explicit root x* between x and x'!
  let f (z : ℝ) : ℝ := edgeY S.p a₁ b₁ z - edgeY S.p a₂ b₂ z
  have hfx : f x < 0 := sub_neg.mpr hlt
  have hfx' : 0 < f x' := sub_pos.mpr hgt
  let lam : ℝ := -f x / (f x' - f x)
  have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
  have hlam1 : lam < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let xstar : ℝ := (1 - lam) * x + lam * x'
  have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a₁ b₁ - edgeSlope S.p a₂ b₂) * z := by
    intro z; simp only [f, edgeY_eq_left_add_slope]; ring
  have hfstar : f xstar = 0 := by
    have hlin : f xstar = (1 - lam) * f x + lam * f x' := by
      rw [haff xstar, haff x, haff x']; simp only [xstar]; ring
    rw [hlin]
    have hden : f x' - f x ≠ 0 := by linarith
    dsimp [lam]; field_simp [hden]; ring
  have hbet : min x x' < xstar ∧ xstar < max x x' := by
    rcases le_total x x' with hxx | hxx
    · have hlt_xx : x < x' := lt_of_le_of_ne hxx (fun h => by rw [h] at hlt; linarith)
      rw [min_eq_left hxx, max_eq_right hxx]
      exact ⟨by dsimp [xstar]; nlinarith, by dsimp [xstar]; nlinarith⟩
    · have hlt_xx : x' < x := lt_of_le_of_ne hxx (fun h => by rw [← h] at hlt; linarith)
      rw [min_eq_right hxx, max_eq_left hxx]
      exact ⟨by dsimp [xstar]; nlinarith, by dsimp [xstar]; nlinarith⟩
  have h1 : (S.p a₁).re < xstar := lt_of_lt_of_le (lt_min hx₁ hx₁') hbet.1.le
  have h2 : xstar < (S.p b₁).re := lt_of_le_of_lt hbet.2.le (max_lt hx₂ hx₂')
  have h3 : (S.p a₂).re < xstar := lt_of_lt_of_le (lt_min hx₃ hx₃') hbet.1.le
  have h4 : xstar < (S.p b₂).re := lt_of_le_of_lt hbet.2.le (max_lt hx₄ hx₄')
  exact S.edgeY_ne_of_ne_edges h₁ h₂ hadj₁ hadj₂ hne h1 h2 h3 h4 (sub_eq_zero.mp hfstar)

/-- No vertex `v` lies on an edge `(a, b)` with `a < v < b`. -/
private lemma edgeY_ne_vertex {a b v : Fin n} (hav : a < v) (hvb : v < b)
    (hadj : S.G.Adj a b) : edgeY S.p a b (S.p v).re ≠ (S.p v).im := by
  intro hy
  have hab : (S.p a).re < (S.p b).re := S.hx_mono (hav.trans hvb)
  set t := ((S.p v).re - (S.p a).re) / ((S.p b).re - (S.p a).re)
  have ht0 : 0 ≤ t := (div_pos (sub_pos.mpr (S.hx_mono hav)) (by linarith)).le
  have ht1 : t ≤ 1 := ((div_lt_one (by linarith)).mpr (sub_lt_sub_right (S.hx_mono hvb) _)).le
  have heq : S.p v = (1 - t) • S.p a + t • S.p b := by
    rw [← edgeY_point_eq S.p hab (S.p v).re, hy]
  exact not_on_closed_unit_seg hadj (S.hsep a v hav.ne) (S.hsep b v hvb.ne.symm) ht0 ht1 heq

/-- Comparing a passing edge `(a, b)` (`a < v < b`) with a right-going edge `(v, w)` (`v < w`)
    at any `x ∈ ((p v).re, min((p b).re, (p w).re))`: order matches `edgeY a b (p v).re` vs `(p v).im`. -/
private lemma edgeY_lt_incident_right {a b v w : Fin n}
    (hav : a < v) (hvb : v < b) (hvw : v < w) (hadj₁ : S.G.Adj a b) (hadj₂ : S.G.Adj v w)
    {x : ℝ} (hx₁ : (S.p v).re < x) (hx₂ : x < (S.p b).re) (hx₃ : x < (S.p w).re) :
    edgeY S.p a b x < edgeY S.p v w x ↔ edgeY S.p a b (S.p v).re < (S.p v).im := by
  have hab : a < b := hav.trans hvb
  have hne : (a, b) ≠ (v, w) := fun h => hav.ne (congrArg Prod.fst h)
  have hxa : (S.p a).re < x := (S.hx_mono hav).trans hx₁
  -- By continuity/linearity of f(z) = edgeY a b z - edgeY v w z on [(p v).re, x]:
  -- f((p v).re) = edgeY a b (p v).re - (p v).im ≠ 0, and f(z) ≠ 0 on ((p v).re, x]
  let f (z : ℝ) : ℝ := edgeY S.p a b z - edgeY S.p v w z
  have hfv : f (S.p v).re = edgeY S.p a b (S.p v).re - (S.p v).im := by
    simp only [f, edgeY_at_left]
  have hfv_ne : f (S.p v).re ≠ 0 := by
    rw [hfv]; exact sub_ne_zero.mpr (S.edgeY_ne_vertex hav hvb hadj₁)
  have hfx_ne : f x ≠ 0 := sub_ne_zero.mpr (S.edgeY_ne_of_ne_edges hab hvw hadj₁ hadj₂ hne hxa hx₂ hx₁ hx₃)
  have hno_opp : ¬ (f (S.p v).re * f x < 0) := by
    intro hneg
    have hdiff : f x - f (S.p v).re ≠ 0 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        linarith
      · have h2 : f x < 0 := by nlinarith
        linarith
    let lam := -f (S.p v).re / (f x - f (S.p v).re)
    have hlam0 : 0 < lam := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact div_pos (by linarith) (by linarith)
      · have h2 : f x < 0 := by nlinarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hlam1 : lam < 1 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact (div_lt_one (by linarith)).mpr (by linarith)
      · have h2 : f x < 0 := by nlinarith
        rw [div_lt_iff_of_neg (by linarith)]; linarith
    let xstar := (1 - lam) * (S.p v).re + lam * x
    have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a b - edgeSlope S.p v w) * z := by
      intro z; simp only [f, edgeY_eq_left_add_slope]; ring
    have hfstar : f xstar = 0 := by
      have hlin : f xstar = (1 - lam) * f (S.p v).re + lam * f x := by
        rw [haff xstar, haff (S.p v).re, haff x]; simp only [xstar]; ring
      rw [hlin]; dsimp [lam]; field_simp [hdiff]; ring
    have h1 : (S.p v).re < xstar := by dsimp [xstar]; nlinarith
    have h2 : xstar < x := by dsimp [xstar]; nlinarith
    exact S.edgeY_ne_of_ne_edges hab hvw hadj₁ hadj₂ hne ((S.hx_mono hav).trans h1)
      (h2.trans hx₂) h1 (h2.trans hx₃) (sub_eq_zero.mp hfstar)
  constructor
  · intro hlt
    have hfx : f x < 0 := sub_neg.mpr hlt
    by_contra! hge
    have hfv_pos : 0 < f (S.p v).re := by
      rw [hfv]; exact sub_pos.mpr (lt_of_le_of_ne hge (S.edgeY_ne_vertex hav hvb hadj₁).symm)
    exact hno_opp (mul_neg_of_pos_of_neg hfv_pos hfx)
  · intro hlt
    have hfv_neg : f (S.p v).re < 0 := by rw [hfv]; exact sub_neg.mpr hlt
    by_contra! hge
    have hfx_pos : 0 < f x := lt_of_le_of_ne (sub_nonneg.mpr hge) hfx_ne.symm
    exact hno_opp (mul_neg_of_neg_of_pos hfv_neg hfx_pos)

/-- Comparing a passing edge `(a, b)` (`a < v < b`) with a left-going edge `(u, v)` (`u < v`)
    at any `x ∈ (max((p a).re, (p u).re), (p v).re)`: order matches `edgeY a b (p v).re` vs `(p v).im`. -/
private lemma edgeY_lt_incident_left {a b u v : Fin n}
    (hav : a < v) (hvb : v < b) (huv : u < v) (hadj₁ : S.G.Adj a b) (hadj₂ : S.G.Adj u v)
    {x : ℝ} (hx₁ : (S.p a).re < x) (hx₂ : (S.p u).re < x) (hx₃ : x < (S.p v).re) :
    edgeY S.p a b x < edgeY S.p u v x ↔ edgeY S.p a b (S.p v).re < (S.p v).im := by
  have hab : a < b := hav.trans hvb
  have hne : (a, b) ≠ (u, v) := fun h => hvb.ne (congrArg Prod.snd h).symm
  have hxb : x < (S.p b).re := hx₃.trans (S.hx_mono hvb)
  let f (z : ℝ) : ℝ := edgeY S.p a b z - edgeY S.p u v z
  have hfv : f (S.p v).re = edgeY S.p a b (S.p v).re - (S.p v).im := by
    simp only [f, edgeY_at_right S.p (S.hx_mono huv)]
  have hfv_ne : f (S.p v).re ≠ 0 := by
    rw [hfv]; exact sub_ne_zero.mpr (S.edgeY_ne_vertex hav hvb hadj₁)
  have hfx_ne : f x ≠ 0 := sub_ne_zero.mpr (S.edgeY_ne_of_ne_edges hab huv hadj₁ hadj₂ hne hx₁ hxb hx₂ hx₃)
  have hno_opp : ¬ (f (S.p v).re * f x < 0) := by
    intro hneg
    have hdiff : f x - f (S.p v).re ≠ 0 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        linarith
      · have h2 : f x < 0 := by nlinarith
        linarith
    let lam := -f (S.p v).re / (f x - f (S.p v).re)
    have hlam0 : 0 < lam := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact div_pos (by linarith) (by linarith)
      · have h2 : f x < 0 := by nlinarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hlam1 : lam < 1 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact (div_lt_one (by linarith)).mpr (by linarith)
      · have h2 : f x < 0 := by nlinarith
        rw [div_lt_iff_of_neg (by linarith)]; linarith
    let xstar := (1 - lam) * (S.p v).re + lam * x
    have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a b - edgeSlope S.p u v) * z := by
      intro z; simp only [f, edgeY_eq_left_add_slope]; ring
    have hfstar : f xstar = 0 := by
      have hlin : f xstar = (1 - lam) * f (S.p v).re + lam * f x := by
        rw [haff xstar, haff (S.p v).re, haff x]; simp only [xstar]; ring
      rw [hlin]; dsimp [lam]; field_simp [hdiff]; ring
    have h1 : x < xstar := by dsimp [xstar]; nlinarith
    have h2 : xstar < (S.p v).re := by dsimp [xstar]; nlinarith
    exact S.edgeY_ne_of_ne_edges hab huv hadj₁ hadj₂ hne (hx₁.trans h1)
      (h2.trans (S.hx_mono hvb)) (hx₂.trans h1) h2 (sub_eq_zero.mp hfstar)
  constructor
  · intro hlt
    have hfx : f x < 0 := sub_neg.mpr hlt
    by_contra! hge
    have hfv_pos : 0 < f (S.p v).re := by
      rw [hfv]; exact sub_pos.mpr (lt_of_le_of_ne hge (S.edgeY_ne_vertex hav hvb hadj₁).symm)
    exact hno_opp (mul_neg_of_pos_of_neg hfv_pos hfx)
  · intro hlt
    have hfv_neg : f (S.p v).re < 0 := by rw [hfv]; exact sub_neg.mpr hlt
    by_contra! hge
    have hfx_pos : 0 < f x := lt_of_le_of_ne (sub_nonneg.mpr hge) hfx_ne.symm
    exact hno_opp (mul_neg_of_neg_of_pos hfv_neg hfx_pos)

/- ### Geometric Rotation System `φ_H` for any Spanning Subgraph `H ≤ S.G` -/

section Subgraph

open Classical

variable (H : SimpleGraph (Fin n))

private lemma heading_inj_H (hHG : H ≤ S.G) (v : Fin n) :
    Function.Injective (fun u : {u : Fin n // H.Adj v u} => heading (S.p u.1 - S.p v)) := by
  intro u₁ u₂ heq
  have h1 : (⟨u₁.1, hHG u₁.2⟩ : {u : Fin n // S.G.Adj v u}) = ⟨u₂.1, hHG u₂.2⟩ :=
    S.heading_inj_at v heq
  exact Subtype.ext (congrArg (Subtype.val : {u : Fin n // S.G.Adj v u} → Fin n) h1)

/-- Clockwise-next neighbor permutation at `v` in `H`. -/
private noncomputable def geoSigma (hHG : H ≤ S.G) (v : Fin n) : Equiv.Perm {u : Fin n // H.Adj v u} :=
  cwPredPerm (fun u : {u : Fin n // H.Adj v u} => heading (S.p u.1 - S.p v)) (S.heading_inj_H H hHG v)

private lemma geoSigma_isCyclic (hHG : H ≤ S.G) (v : Fin n) :
    IsCyclicPerm (S.geoSigma H hHG v) :=
  cwPredPerm_isCyclic _ (S.heading_inj_H H hHG v)

private lemma geoSigma_spec (hHG : H ≤ S.G) (v : Fin n) (a : {u : Fin n // H.Adj v u}) :
    ((∀ b : {u : Fin n // H.Adj v u}, heading (S.p a.1 - S.p v) ≤ heading (S.p b.1 - S.p v)) ∧
     (∀ b : {u : Fin n // H.Adj v u}, heading (S.p b.1 - S.p v) ≤ heading (S.p (S.geoSigma H hHG v a).1 - S.p v))) ∨
    (heading (S.p (S.geoSigma H hHG v a).1 - S.p v) < heading (S.p a.1 - S.p v) ∧
     ∀ b : {u : Fin n // H.Adj v u}, heading (S.p (S.geoSigma H hHG v a).1 - S.p v) < heading (S.p b.1 - S.p v) →
       heading (S.p a.1 - S.p v) ≤ heading (S.p b.1 - S.p v)) :=
  cwPredPerm_spec _ (S.heading_inj_H H hHG v) a

private lemma geoSigma_ne_self (hHG : H ≤ S.G) (v : Fin n)
    (hdeg2 : ∃ u₁ u₂ : Fin n, H.Adj v u₁ ∧ H.Adj v u₂ ∧ u₁ ≠ u₂) (a : {u : Fin n // H.Adj v u}) :
    S.geoSigma H hHG v a ≠ a := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := hdeg2
  have hcard2 : 2 ≤ Fintype.card {u : Fin n // H.Adj v u} := by
    have hne' : (⟨u₁, hu₁⟩ : {u : Fin n // H.Adj v u}) ≠ ⟨u₂, hu₂⟩ := fun h => hne (congrArg Subtype.val h)
    have hle := Finset.card_le_univ ({⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩} : Finset {u : Fin n // H.Adj v u})
    rw [Finset.card_pair hne'] at hle
    exact hle
  exact cwPredPerm_ne_self _ (S.heading_inj_H H hHG v) hcard2 a

/-- Geometric dart permutation `φ_H` on `DartOf H`. -/
private noncomputable def geoPhi (hHG : H ≤ S.G) : Equiv.Perm (DartOf H) :=
  dartPerm H (S.geoSigma H hHG)

/-- Whether incoming dart `(u, v)` is at the minimum-heading neighbor of `v` in `H` (the `+2π` wrap). -/
private def isMinNeighbor (d : DartOf H) : Prop :=
  ∀ w : Fin n, H.Adj d.1.2 w → heading (S.p d.1.1 - S.p d.1.2) ≤ heading (S.p w - S.p d.1.2)

/-- Clockwise angle gap `θ_H(u, v) ∈ (0, 2π]` swept from ray `v → u` to ray `v → σ_v(u)`. -/
private noncomputable def gapAngle (hHG : H ≤ S.G) (d : DartOf H) : ℝ :=
  let v := d.1.2
  let u := d.1.1
  let w := (S.geoSigma H hHG v ⟨u, d.2.symm⟩).1
  let α_in := heading (S.p u - S.p v)
  let α_out := heading (S.p w - S.p v)
  α_in - α_out + if S.isMinNeighbor H d then 2 * Real.pi else 0

private lemma gapAngle_sum_at_vertex (hHG : H ≤ S.G) (v : Fin n) (hdeg : ∃ u, H.Adj v u) :
    ∑ u : {u : Fin n // H.Adj v u}, S.gapAngle H hHG ⟨(u.1, v), u.2.symm⟩ = 2 * Real.pi := by
  let f : {u : Fin n // H.Adj v u} → ℝ := fun u => heading (S.p u.1 - S.p v)
  have h1 : ∑ u : {u : Fin n // H.Adj v u}, (f u - f (S.geoSigma H hHG v u)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hcomp : ∑ u : {u : Fin n // H.Adj v u}, f (S.geoSigma H hHG v u) =
        ∑ u : {u : Fin n // H.Adj v u}, f u :=
      Fintype.sum_equiv (S.geoSigma H hHG v) (fun u => f (S.geoSigma H hHG v u)) f (fun _ => rfl)
    rw [hcomp, sub_self]
  obtain ⟨u₁, hu₁⟩ := hdeg
  have hne : (Finset.univ : Finset {u : Fin n // H.Adj v u}).Nonempty := ⟨⟨u₁, hu₁⟩, Finset.mem_univ _⟩
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_min_image Finset.univ f hne
  have hmin_iff : ∀ u : {u : Fin n // H.Adj v u},
      S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ ↔ u = u₀ := by
    intro u
    constructor
    · intro h
      exact S.heading_inj_H H hHG v (le_antisymm (h u₀.1 u₀.2) (hu₀ u (Finset.mem_univ u)))
    · rintro rfl w hw
      exact hu₀ ⟨w, hw⟩ (Finset.mem_univ _)
  have h2 : ∑ u : {u : Fin n // H.Adj v u},
      (if S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ then (2 * Real.pi : ℝ) else 0) = 2 * Real.pi := by
    rw [Finset.sum_eq_single u₀]
    · exact if_pos ((hmin_iff u₀).mpr rfl)
    · intro u _ hne
      exact if_neg (fun h => hne ((hmin_iff u).mp h))
    · intro h; exact (h (Finset.mem_univ u₀)).elim
  have hunf : ∀ u : {u : Fin n // H.Adj v u},
      S.gapAngle H hHG ⟨(u.1, v), u.2.symm⟩ =
      (f u - f (S.geoSigma H hHG v u)) +
      if S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ then (2 * Real.pi : ℝ) else 0 := by
    intro ⟨u, hu⟩
    simp only [gapAngle, f]
  rw [Finset.sum_congr rfl (fun u _ => hunf u), Finset.sum_add_distrib, h1, h2, zero_add]

private lemma gapAngle_ge_pi_div_three (hHG : H ≤ S.G) (d : DartOf H) :
    Real.pi / 3 ≤ S.gapAngle H hHG d := by
  classical
  let v := d.1.2
  let u : {x : Fin n // H.Adj v x} := ⟨d.1.1, d.2.symm⟩
  let w := S.geoSigma H hHG v u
  have hnorm_u : ‖S.p u.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact hHG u.2
  have hnorm_w : ‖S.p w.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact hHG w.2
  have hre_u : (S.p u.1 - S.p v).re ≠ 0 := S.p_sub_re_ne (H.ne_of_adj u.2).symm
  have hre_w : (S.p w.1 - S.p v).re ≠ 0 := S.p_sub_re_ne (H.ne_of_adj w.2).symm
  by_cases huw : u = w
  · -- Only 1 neighbor at v: gapAngle = 2π ≥ π/3
    have hmin : S.isMinNeighbor H d := by
      have hspec := (cwPredPerm_isMin_iff _ (S.heading_inj_H H hHG v) u).mpr (by rw [show cwPredPerm _ _ u = w from rfl, ← huw])
      intro x hx; exact hspec ⟨x, hx⟩
    unfold gapAngle
    dsimp only
    change heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
      (if S.isMinNeighbor H d then 2 * Real.pi else 0) ≥ Real.pi / 3
    rw [huw, sub_self, zero_add, if_pos hmin]
    linarith [Real.pi_pos]
  · have hsep_uw : 1 ≤ ‖(S.p u.1 - S.p v) - (S.p w.1 - S.p v)‖ := by
      rw [sub_sub_sub_cancel_right]
      exact S.hsep u.1 w.1 (fun h => huw (Subtype.ext h))
    rcases cwPredPerm_spec (fun x : {x : Fin n // H.Adj v x} => heading (S.p x.1 - S.p v))
        (S.heading_inj_H H hHG v) u with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
    · have hmin' : S.isMinNeighbor H d := fun x hx => hmin ⟨x, hx⟩
      have hlt : heading (S.p u.1 - S.p v) < heading (S.p w.1 - S.p v) :=
        lt_of_le_of_ne (hmin w) (fun h => huw (S.heading_inj_H H hHG v h))
      have hgap := heading_gap_ge_pi_div_three hnorm_u hnorm_w hsep_uw hre_u hre_w hlt
      unfold gapAngle; dsimp only
      change Real.pi / 3 ≤ heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
        (if S.isMinNeighbor H d then 2 * Real.pi else 0)
      rw [if_pos hmin']
      linarith [hgap.2]
    · have hnotmin : ¬ S.isMinNeighbor H d := fun h => not_lt_of_ge (h w.1 w.2) hlt
      have hsep_wu : 1 ≤ ‖(S.p w.1 - S.p v) - (S.p u.1 - S.p v)‖ := by
        rw [norm_sub_rev]; exact hsep_uw
      have hgap := heading_gap_ge_pi_div_three hnorm_w hnorm_u hsep_wu hre_w hre_u hlt
      unfold gapAngle; dsimp only
      change Real.pi / 3 ≤ heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
        (if S.isMinNeighbor H d then 2 * Real.pi else 0)
      rw [if_neg hnotmin, add_zero]
      exact hgap.1

/-- `leftTip_H d`: incoming dart `d = (u, v)` comes from the right (`v < u`) and is NOT the
    minimum-heading neighbor of `v`. -/
private def isLeftTip (d : DartOf H) : Prop :=
  d.1.2 < d.1.1 ∧ ¬ S.isMinNeighbor H d

/-- `rightCap_H d`: incoming dart `d = (u, v)` comes from the left (`u < v`) and IS the
    minimum-heading neighbor of `v` (which happens iff `v` has NO right neighbors in `H`
    and `u` is its topmost left neighbor). -/
private def isRightCap (d : DartOf H) : Prop :=
  d.1.1 < d.1.2 ∧ S.isMinNeighbor H d

/-- Exact dart-level turning-number identity! -/
private lemma gapAngle_telescoping (hHG : H ≤ S.G) (d : DartOf H) :
    S.gapAngle H hHG d =
      Real.pi + heading (S.p d.1.2 - S.p d.1.1) -
      heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) +
      (if S.isRightCap H d then 2 * Real.pi else 0) -
      (if S.isLeftTip H d then 2 * Real.pi else 0) := by
  rcases d with ⟨⟨u, v⟩, huv_adj⟩
  have huv_ne : u ≠ v := H.ne_of_adj huv_adj
  have hneg : S.p v - S.p u = -(S.p u - S.p v) := by ring
  unfold gapAngle isRightCap isLeftTip
  dsimp only [geoPhi, dartPerm, Equiv.coe_fn_mk]
  rcases lt_or_gt_of_ne huv_ne with huv | hvu
  · have hre : (S.p u - S.p v).re < 0 := S.p_sub_re_neg_iff.mpr huv
    have hhead : heading (S.p v - S.p u) = heading (S.p u - S.p v) - Real.pi := by
      rw [hneg]; exact heading_neg_of_neg hre
    have hnot : ¬ (v < u) := not_lt.mpr huv.le
    rw [hhead]
    by_cases hmin : S.isMinNeighbor H ⟨(u, v), huv_adj⟩
    · simp only [if_pos hmin, if_pos (And.intro huv hmin), hnot, false_and, if_false]; ring
    · simp only [hmin, and_false, hnot, false_and, if_false]; ring
  · have hre : 0 < (S.p u - S.p v).re := S.p_sub_re_pos_iff.mpr hvu
    have hhead : heading (S.p v - S.p u) = heading (S.p u - S.p v) + Real.pi := by
      rw [hneg]; exact heading_neg_of_pos hre
    have hnot : ¬ (u < v) := not_lt.mpr hvu.le
    rw [hhead]
    by_cases hmin : S.isMinNeighbor H ⟨(u, v), huv_adj⟩
    · simp only [hmin, not_true_eq_false, and_false, hnot, false_and, if_true, if_false]; ring
    · simp only [if_neg hmin, hnot, false_and, if_pos (And.intro hvu hmin), if_false]; ring

/-- Orbit-level turning-number formula: for ANY `φ_H`-invariant set `C : Finset (DartOf H)`,
    `∑_{d ∈ C} θ_H(d) = |C| * π - 2π * (#leftTips(C) - #rightCaps(C))`. -/
private lemma invariant_set_angle_sum (hHG : H ≤ S.G) (C : Finset (DartOf H))
    (hinv : ∀ d ∈ C, S.geoPhi H hHG d ∈ C) :
    haveI := Classical.decPred (S.isLeftTip H)
    haveI := Classical.decPred (S.isRightCap H)
    ∑ d ∈ C, S.gapAngle H hHG d =
      (C.card : ℝ) * Real.pi -
      2 * Real.pi * (((C.filter (S.isLeftTip H)).card : ℝ) -
                     ((C.filter (S.isRightCap H)).card : ℝ)) := by
  classical
  -- Bijection φ_H on C gives ∑_{d ∈ C} heading(φ_H d) = ∑_{d ∈ C} heading(d)
  have hbij : Finset.image (S.geoPhi H hHG) C = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact hinv d hd
    · rw [Finset.card_image_of_injective C (S.geoPhi H hHG).injective]
  have htele : ∑ d ∈ C, heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) =
      ∑ d ∈ C, heading (S.p d.1.2 - S.p d.1.1) := by
    conv_rhs => rw [← hbij]
    rw [Finset.sum_image (fun a _ b _ h => (S.geoPhi H hHG).injective h)]
  have hsum : ∑ d ∈ C, S.gapAngle H hHG d =
      ∑ d ∈ C, (Real.pi + heading (S.p d.1.2 - S.p d.1.1) -
        heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) +
        (if S.isRightCap H d then (2 * Real.pi : ℝ) else 0) -
        (if S.isLeftTip H d then (2 * Real.pi : ℝ) else 0)) :=
    Finset.sum_congr rfl (fun d _ => S.gapAngle_telescoping H hHG d)
  rw [hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [htele]
  ring

/- ### Vertical Slab Trapezoid Graph `T(H)` -/

/-- Oriented edges of `H`: pairs `(a, b)` with `a < b` and `H.Adj a b`. -/
private noncomputable def orientEdges : Finset (Fin n × Fin n) := by
  classical
  let _ := S
  exact Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ H.Adj e.1 e.2)

private lemma orientEdges_card :
    haveI := Classical.decRel H.Adj
    (S.orientEdges H).card = H.edgeFinset.card := by
  classical
  let f : Fin n × Fin n → Sym2 (Fin n) := fun e => s(e.1, e.2)
  have hinj : Set.InjOn f ↑(S.orientEdges H) := by
    intro e₁ he₁ e₂ he₂ hf
    simp only [Finset.mem_coe, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    rcases Sym2.eq_iff.mp hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; rw [h1, h2] at he₁; exact lt_asymm he₁.1 he₂.1
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext x
  induction x using Sym2.ind with | _ a b =>
  simp only [Finset.mem_image, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_edgeFinset, f]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨_, hadj⟩, hEq⟩
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · intro hab
    rcases lt_or_gt_of_ne (H.ne_of_adj hab) with h | h
    · exact ⟨(a, b), ⟨h, hab⟩, rfl⟩
    · exact ⟨(b, a), ⟨h, hab.symm⟩, Sym2.eq_swap⟩

/-- Active edges of `H` in slab `i : Fin (n + 1)`: edges `(a, b)` with `a.val < i.val ≤ b.val`. -/
private noncomputable def activeEdges (i : Fin (n + 1)) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1.val < i.val ∧ i.val ≤ e.2.val)

private lemma activeEdges_zero : S.activeEdges H 0 = ∅ := by
  classical
  ext e; simp [activeEdges]

private lemma activeEdges_last : S.activeEdges H (Fin.last n) = ∅ := by
  classical
  ext e
  simp only [activeEdges, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and,
    Fin.val_last]
  intro _ _ hle
  omega

/-- Sample x-coordinate strictly inside slab `i` (used for `1 ≤ i ≤ n - 1`). -/
private noncomputable def slabMid (i : Fin (n + 1)) : ℝ :=
  if h1 : 0 < i.val then
    if h2 : i.val < n then
      ((S.p ⟨i.val - 1, by omega⟩).re + (S.p ⟨i.val, h2⟩).re) / 2
    else (S.p ⟨n - 1, by have := S.hn; omega⟩).re + 1
  else (S.p ⟨0, by have := S.hn; omega⟩).re - 1

private lemma slabMid_between {i : Fin (n + 1)} {e : Fin n × Fin n}
    (he : e ∈ S.activeEdges H i) :
    (S.p e.1).re < S.slabMid i ∧ S.slabMid i < (S.p e.2).re := by
  classical
  simp only [activeEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  have h1 : 0 < i.val := by omega
  have h2 : i.val < n := by omega
  unfold slabMid
  rw [dif_pos h1, dif_pos h2]
  have ha : (S.p e.1).re ≤ (S.p ⟨i.val - 1, by omega⟩).re :=
    S.hx_mono.monotone (show e.1 ≤ ⟨i.val - 1, by omega⟩ from by change e.1.val ≤ i.val - 1; omega)
  have hb : (S.p ⟨i.val, h2⟩).re ≤ (S.p e.2).re :=
    S.hx_mono.monotone (show ⟨i.val, h2⟩ ≤ e.2 from by change i.val ≤ e.2.val; omega)
  have hlt : (S.p ⟨i.val - 1, by omega⟩).re < (S.p ⟨i.val, h2⟩).re :=
    S.hx_mono (show (⟨i.val - 1, by omega⟩ : Fin n) < ⟨i.val, h2⟩ from by change i.val - 1 < i.val; omega)
  exact ⟨by linarith, by linarith⟩

private lemma slabMid_castSucc_lt {v : Fin n} (h1 : 0 < v.val) :
    S.slabMid v.castSucc < (S.p v).re := by
  unfold slabMid
  rw [dif_pos (by simp [h1]), dif_pos (by simp [v.isLt])]
  have hlt := S.hx_mono (show (⟨v.val - 1, by omega⟩ : Fin n) < v from by change v.val - 1 < v.val; omega)
  have h1' : (⟨v.castSucc.val - 1, by simp; omega⟩ : Fin n) = ⟨v.val - 1, by omega⟩ := Fin.ext (by simp)
  have h2' : (⟨v.castSucc.val, by simp [v.isLt]⟩ : Fin n) = v := Fin.ext rfl
  rw [h1', h2']; linarith

private lemma lt_slabMid_succ {v : Fin n} (h2 : v.val + 1 < n) :
    (S.p v).re < S.slabMid v.succ := by
  unfold slabMid
  rw [dif_pos (by simp), dif_pos (by simp [h2])]
  have hlt := S.hx_mono (show v < ⟨v.val + 1, h2⟩ from by change v.val < v.val + 1; omega)
  have h1' : (⟨v.succ.val - 1, by simp⟩ : Fin n) = v := Fin.ext (by simp)
  have h2' : (⟨v.succ.val, by simp [h2]⟩ : Fin n) = ⟨v.val + 1, h2⟩ := Fin.ext (by simp)
  rw [h1', h2']; linarith

/-- Edges passing strictly over/under vertex `v : Fin n`, split into below and above `v`. -/
private noncomputable def passEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1 < v ∧ v < e.2)

private noncomputable def passBelow (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.passEdges H v).filter (fun e => edgeY S.p e.1 e.2 (S.p v).re < (S.p v).im)

private noncomputable def passAbove (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.passEdges H v).filter (fun e => (S.p v).im < edgeY S.p e.1 e.2 (S.p v).re)

private noncomputable def leftEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.2 = v)

private noncomputable def rightEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1 = v)

private lemma passEdges_partition (hHG : H ≤ S.G) (v : Fin n) :
    S.passEdges H v = S.passBelow H v ∪ S.passAbove H v ∧
    Disjoint (S.passBelow H v) (S.passAbove H v) := by
  classical
  constructor
  · ext e
    simp only [passBelow, passAbove, passEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hadj⟩, h1, h2⟩
      rcases lt_or_gt_of_ne (S.edgeY_ne_vertex h1 h2 (hHG hadj)) with h | h
      · exact Or.inl ⟨⟨⟨h1.trans h2, hadj⟩, h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨⟨h1.trans h2, hadj⟩, h1, h2⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passBelow, passAbove, Finset.mem_filter] at h1 h2
    linarith

private lemma activeEdges_castSucc_eq (v : Fin n) :
    S.activeEdges H v.castSucc = S.passEdges H v ∪ S.leftEdges H v ∧
    Disjoint (S.passEdges H v) (S.leftEdges H v) := by
  classical
  constructor
  · ext e
    simp only [activeEdges, passEdges, leftEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_castSucc, Fin.lt_def]
    constructor
    · rintro ⟨⟨hlt, hadj⟩, h1, h2⟩
      by_cases hev : e.2 = v
      · exact Or.inr ⟨⟨hlt, hadj⟩, hev⟩
      · left; refine ⟨⟨hlt, hadj⟩, h1, lt_of_le_of_ne h2 (fun h => hev (Fin.ext h.symm))⟩
    · rintro (⟨⟨hlt, hadj⟩, h1, h2⟩ | ⟨⟨hlt, hadj⟩, rfl⟩)
      · exact ⟨⟨hlt, hadj⟩, h1, h2.le⟩
      · exact ⟨⟨hlt, hadj⟩, hlt, le_rfl⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passEdges, leftEdges, Finset.mem_filter] at h1 h2
    exact h1.2.2.ne h2.2.symm

private lemma activeEdges_succ_eq (v : Fin n) :
    S.activeEdges H v.succ = S.passEdges H v ∪ S.rightEdges H v ∧
    Disjoint (S.passEdges H v) (S.rightEdges H v) := by
  classical
  constructor
  · ext e
    simp only [activeEdges, passEdges, rightEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_succ, Fin.lt_def]
    constructor
    · rintro ⟨⟨hlt, hadj⟩, h1, h2⟩
      by_cases hev : e.1 = v
      · exact Or.inr ⟨⟨hlt, hadj⟩, hev⟩
      · left; refine ⟨⟨hlt, hadj⟩, by omega, by omega⟩
    · rintro (⟨⟨hlt, hadj⟩, h1, h2⟩ | ⟨⟨hlt, hadj⟩, rfl⟩)
      · exact ⟨⟨hlt, hadj⟩, by omega, by omega⟩
      · exact ⟨⟨hlt, hadj⟩, by omega, by omega⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passEdges, rightEdges, Finset.mem_filter] at h1 h2
    exact h1.2.1.ne h2.2

private lemma activeEdges_card_step (v : Fin n) :
    (S.activeEdges H v.castSucc).card + (S.rightEdges H v).card =
    (S.activeEdges H v.succ).card + (S.leftEdges H v).card := by
  have h1 := S.activeEdges_castSucc_eq H v
  have h2 := S.activeEdges_succ_eq H v
  have c1 : (S.activeEdges H v.castSucc).card = (S.passEdges H v).card + (S.leftEdges H v).card := by
    rw [h1.1, Finset.card_union_of_disjoint h1.2]
  have c2 : (S.activeEdges H v.succ).card = (S.passEdges H v).card + (S.rightEdges H v).card := by
    rw [h2.1, Finset.card_union_of_disjoint h2.2]
  omega

private lemma passBelow_add_left_le (hHG : H ≤ S.G) (v : Fin n) :
    (S.passBelow H v).card + (S.leftEdges H v).card ≤ (S.activeEdges H v.castSucc).card := by
  have h1 := S.activeEdges_castSucc_eq H v
  have hp := S.passEdges_partition H hHG v
  rw [h1.1, Finset.card_union_of_disjoint h1.2, hp.1, Finset.card_union_of_disjoint hp.2]
  omega

private lemma passBelow_add_right_le (hHG : H ≤ S.G) (v : Fin n) :
    (S.passBelow H v).card + (S.rightEdges H v).card ≤ (S.activeEdges H v.succ).card := by
  have h2 := S.activeEdges_succ_eq H v
  have hp := S.passEdges_partition H hHG v
  rw [h2.1, Finset.card_union_of_disjoint h2.2, hp.1, Finset.card_union_of_disjoint hp.2]
  omega

private lemma leftEdges_add_rightEdges_eq_degree (v : Fin n) :
    haveI := Classical.decRel H.Adj
    (S.leftEdges H v).card + (S.rightEdges H v).card = H.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hL : (S.leftEdges H v).card = ((H.neighborFinset v).filter (· < v)).card := by
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      simp only [leftEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨he.2 ▸ he.1.2.symm, he.2 ▸ he.1.1⟩
    · intro e₁ he₁ e₂ he₂ h
      simp only [leftEdges, Finset.mem_filter] at he₁ he₂
      exact Prod.ext h (he₁.2.trans he₂.2.symm)
    · intro u hu
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
      exact ⟨(u, v), by simp [leftEdges, orientEdges, hu.2, hu.1.symm], rfl⟩
  have hR : (S.rightEdges H v).card = ((H.neighborFinset v).filter (fun u => ¬ u < v)).card := by
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      simp only [rightEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨he.2 ▸ he.1.2, not_lt.mpr (he.2 ▸ he.1.1).le⟩
    · intro e₁ he₁ e₂ he₂ h
      simp only [rightEdges, Finset.mem_filter] at he₁ he₂
      exact Prod.ext (he₁.2.trans he₂.2.symm) h
    · intro u hu
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
      have hvu : v < u := lt_of_le_of_ne (not_lt.mp hu.2) (H.ne_of_adj hu.1)
      exact ⟨(v, u), by simp [rightEdges, orientEdges, hvu, hu.1], rfl⟩
  rw [hL, hR, Finset.card_filter_add_card_filter_not]

private lemma sum_leftEdges_eq_edges :
    ∑ v : Fin n, (S.leftEdges H v).card = (S.orientEdges H).card := by
  classical
  have hpart : S.orientEdges H = Finset.univ.biUnion (fun v : Fin n => S.leftEdges H v) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, leftEdges, Finset.mem_filter]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [hpart, Finset.card_biUnion]
  intro v₁ _ v₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro e h1 h2
  simp only [leftEdges, Finset.mem_filter] at h1 h2
  exact hne (h1.2.symm.trans h2.2)

/-- Vertices of the vertical slab trapezoid graph `T(H)`: pairs `(i, r)` with `i : Fin (n + 1)`
    and `r : Fin ((activeEdges H i).card + 1)`. -/
private abbrev SlabVert : Type :=
  Σ i : Fin (n + 1), Fin ((S.activeEdges H i).card + 1)

private lemma slabVert_ext {i₁ i₂ : Fin (n + 1)} {r₁ : Fin ((S.activeEdges H i₁).card + 1)}
    {r₂ : Fin ((S.activeEdges H i₂).card + 1)} (hi : i₁ = i₂) (hr : r₁.val = r₂.val) :
    (⟨i₁, r₁⟩ : S.SlabVert H) = ⟨i₂, r₂⟩ := by
  subst hi; exact Sigma.ext rfl (heq_of_eq (Fin.ext hr))

/-- Directed gluing relation from slab `v.castSucc` to slab `v.succ` across vertex `v`. -/
private def slabGlueAcross (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1)) : Prop :=
  let p := (S.passBelow H v).card
  let dL := (S.leftEdges H v).card
  let dR := (S.rightEdges H v).card
  (r₁.val ≤ p ∧ r₂.val = r₁.val) ∨
  (p + dL ≤ r₁.val ∧ r₂.val + dL = r₁.val + dR)

/-- The vertical slab trapezoid graph `T(H)` on `SlabVert H`. -/
private def slabGraph : SimpleGraph (S.SlabVert H) where
  Adj x y :=
    (∃ (v : Fin n) (h₁ : x.1 = v.castSucc) (h₂ : y.1 = v.succ),
      S.slabGlueAcross H v (h₁ ▸ x.2) (h₂ ▸ y.2)) ∨
    (∃ (v : Fin n) (h₁ : y.1 = v.castSucc) (h₂ : x.1 = v.succ),
      S.slabGlueAcross H v (h₁ ▸ y.2) (h₂ ▸ x.2))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨v, h1, h2, _⟩ | ⟨v, h1, h2, _⟩
    · have : v.castSucc = v.succ := h1.symm.trans h2
      have := congrArg Fin.val this; simp at this
    · have : v.castSucc = v.succ := h1.symm.trans h2
      have := congrArg Fin.val this; simp at this⟩

private lemma slabGraph_adj_step (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1))
    (h : S.slabGlueAcross H v r₁ r₂) :
    (S.slabGraph H).Adj ⟨v.castSucc, r₁⟩ ⟨v.succ, r₂⟩ :=
  Or.inl ⟨v, rfl, rfl, h⟩

private lemma slabGraph_adj_step_iff (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1)) :
    (S.slabGraph H).Adj ⟨v.castSucc, r₁⟩ ⟨v.succ, r₂⟩ ↔ S.slabGlueAcross H v r₁ r₂ := by
  constructor
  · rintro (⟨w, h1, h2, hg⟩ | ⟨w, h1, h2, _⟩)
    · have hvw : v = w := Fin.ext (by simpa using congrArg Fin.val h1)
      subst hvw; exact hg
    · have : v.val + 1 = w.val := by simpa using congrArg Fin.val h1
      have : v.val = w.val + 1 := by simpa using congrArg Fin.val h2
      omega
  · exact S.slabGraph_adj_step H v r₁ r₂

/-- Left-going degree (number of gluing edges coming from slab `i - 1`) of a trapezoid `t`. -/
private noncomputable def slabInEdges (t : S.SlabVert H) : Finset (S.SlabVert H) := by
  classical
  exact Finset.univ.filter (fun s : S.SlabVert H => s.1.val + 1 = t.1.val ∧ (S.slabGraph H).Adj s t)

/-- Exact count of `slabInEdges` for every vertex of `T(H)` (assuming `∀ v, 1 ≤ H.degree v`):
    - At `i = 0`: `0`.
    - At `v.succ`, `r`:
      - `p < r < p + dR`: `0` (leftTip!)
      - `r = p` and `dR = 0`: `2` (rightCap!)
      - everywhere else: `1`! -/
private lemma slabInEdges_zero (r : Fin ((S.activeEdges H 0).card + 1)) :
    (S.slabInEdges H ⟨0, r⟩).card = 0 := by
  classical
  unfold slabInEdges
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ ⟨h, _⟩
  simp at h

private lemma slabInEdges_succ_card (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card)
    (v : Fin n) (r : Fin ((S.activeEdges H v.succ).card + 1)) :
    let p := (S.passBelow H v).card
    let dR := (S.rightEdges H v).card
    (S.slabInEdges H ⟨v.succ, r⟩).card =
      if p < r.val ∧ r.val < p + dR then 0
      else if r.val = p ∧ dR = 0 then 2
      else 1 := by
  classical
  intro p dR
  let dL := (S.leftEdges H v).card
  have hstep := S.activeEdges_card_step H v
  have hpL := S.passBelow_add_left_le H hHG v
  have hpR := S.passBelow_add_right_le H hHG v
  have hdv := hdeg v
  -- Any s ∈ slabInEdges H ⟨v.succ, r⟩ must have s.1 = v.castSucc and slabGlueAcross H v s.2 r
  have hmem : ∀ s : S.SlabVert H, s ∈ S.slabInEdges H ⟨v.succ, r⟩ ↔
      ∃ (hs : s.1 = v.castSucc), S.slabGlueAcross H v (hs ▸ s.2) r := by
    intro s
    simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]
    constructor
    · rintro ⟨hval, hadj⟩
      have hs : s.1 = v.castSucc := Fin.ext (by simp; omega)
      refine ⟨hs, ?_⟩
      rcases s with ⟨i, r₁⟩
      dsimp at hs; subst hs
      exact (S.slabGraph_adj_step_iff H v r₁ r).mp hadj
    · rintro ⟨hs, hg⟩
      rcases s with ⟨i, r₁⟩
      dsimp at hs; subst hs
      exact ⟨rfl, S.slabGraph_adj_step H v r₁ r hg⟩
  split_ifs with htip hcap
  · -- p < r < p + dR: NO preimage!
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs_in
    obtain ⟨hs, hg⟩ := (hmem s).mp hs_in
    rcases s with ⟨i, r₁⟩; dsimp only at hs; subst hs; dsimp only at hg
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · -- r = p ∧ dR = 0 (so dL ≥ 1): TWO distinct preimages: r₁ = p and r₁ = p + dL!
    have hdL : 1 ≤ dL := by omega
    let s₁ : S.SlabVert H := ⟨v.castSucc, ⟨p, by omega⟩⟩
    let s₂ : S.SlabVert H := ⟨v.castSucc, ⟨p + dL, by omega⟩⟩
    have hne : s₁ ≠ s₂ := fun h => by
      have : p = p + dL := by
        have := congrArg (fun x : S.SlabVert H => x.2.val) h
        simpa [s₁, s₂] using this
      omega
    have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₁, s₂} := by
      ext s
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hs, hg⟩
        rcases s with ⟨i, r₁⟩
        dsimp only at hs; subst hs; dsimp only at hg
        rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact S.slabVert_ext H rfl (by dsimp [s₁]; omega)
        · right; exact S.slabVert_ext H rfl (by dsimp [s₂]; omega)
      · rintro (rfl | rfl)
        · exact ⟨rfl, Or.inl ⟨le_rfl, hcap.1⟩⟩
        · exact ⟨rfl, Or.inr ⟨le_rfl, by dsimp [s₂]; omega⟩⟩
    rw [heq, Finset.card_pair hne]
  · -- Otherwise: UNIQUE preimage!
    by_cases hle : r.val ≤ p
    · -- r ≤ p and NOT (r = p ∧ dR = 0): unique preimage is s₁ = (v.castSucc, r)
      let s₁ : S.SlabVert H := ⟨v.castSucc, ⟨r.val, by omega⟩⟩
      have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₁} := by
        ext s
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, hg⟩
          rcases s with ⟨i, r₁⟩
          dsimp only at hs; subst hs; dsimp only at hg
          rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact S.slabVert_ext H rfl (by dsimp [s₁]; omega)
          · exfalso; omega
        · rintro rfl
          exact ⟨rfl, Or.inl ⟨hle, rfl⟩⟩
      rw [heq, Finset.card_singleton]
    · -- p + dR ≤ r: unique preimage is s₂ = (v.castSucc, r - dR + dL)
      have hge : p + dR ≤ r.val := by omega
      let s₂ : S.SlabVert H := ⟨v.castSucc, ⟨r.val - dR + dL, by omega⟩⟩
      have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₂} := by
        ext s
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, hg⟩
          rcases s with ⟨i, r₁⟩
          dsimp only at hs; subst hs; dsimp only at hg
          rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exfalso; omega
          · exact S.slabVert_ext H rfl (by dsimp [s₂]; omega)
        · rintro rfl
          exact ⟨rfl, Or.inr ⟨by dsimp [s₂]; omega, by dsimp [s₂]; omega⟩⟩
      rw [heq, Finset.card_singleton]

/-- Every edge of `T(H)` goes from slab `i` to slab `i + 1`, so `∑_{t ∈ C} |slabInEdges t|`
    equals the number of edges of `T(H)` with both endpoints in a connected component `C`!
    In particular, over all of `T(H)`, `∑ t, |slabInEdges t| = |(slabGraph H).edgeFinset|`. -/
private lemma sum_slabInEdges_eq_edges :
    haveI := Classical.decRel (S.slabGraph H).Adj
    ∑ t : S.SlabVert H, (S.slabInEdges H t).card = (S.slabGraph H).edgeFinset.card := by
  classical
  -- Bijection between Σ t, slabInEdges t and (slabGraph H).edgeFinset via (t, s) ↦ s(s, t)
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => s(p.2, p.1)) ?_ ?_ ?_
  · intro ⟨t, s⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter] at hp
    exact (S.slabGraph H).mem_edgeFinset.mpr hp.2
  · intro ⟨t₁, s₁⟩ h1 ⟨t₂, s₂⟩ h2 heq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter] at h1 h2
    rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · dsimp only at hs ht; exact Sigma.ext ht (heq_of_eq hs)
    · exfalso
      dsimp only at hs ht
      have hval1 := h1.1
      have hval2 := h2.1
      rw [hs, ht] at hval1
      omega
  · intro e he
    induction e using Sym2.ind with | _ x y =>
    have hadj : (S.slabGraph H).Adj x y := (S.slabGraph H).mem_edgeFinset.mp he
    rcases hadj with ⟨v, h1, h2, hg⟩ | ⟨v, h1, h2, hg⟩
    · refine ⟨⟨y, x⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter]
      exact ⟨by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
    · refine ⟨⟨x, y⟩, ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter]
      exact ⟨by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩

/-- Total vertex minus edge count of `T(H)`: `V(T(H)) - E(T(H)) = |E(H)| - n + 1`! -/
private lemma slab_vert_sub_edge (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    (Fintype.card (S.SlabVert H) : ℤ) - ((S.slabGraph H).edgeFinset.card : ℤ) =
      ((S.orientEdges H).card : ℤ) - (n : ℤ) + 1 := by
  classical
  -- Count edges across each vertex v directly from slabInEdges_succ_card!
  rw [← S.sum_slabInEdges_eq_edges H, Fintype.card_sigma]
  rw [Fin.sum_univ_succ (f := fun i : Fin (n + 1) => Fintype.card (Fin ((S.activeEdges H i).card + 1)))]
  rw [Fintype.sum_sigma, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => ∑ r : Fin ((S.activeEdges H i).card + 1), (S.slabInEdges H ⟨i, r⟩).card)]
  have h0_v : Fintype.card (Fin ((S.activeEdges H 0).card + 1)) = 1 := by
    rw [Fintype.card_fin, S.activeEdges_zero, Finset.card_empty]
  have h0_e : ∑ r : Fin ((S.activeEdges H 0).card + 1), (S.slabInEdges H ⟨0, r⟩).card = 0 := by
    simp [S.slabInEdges_zero]
  rw [h0_v, h0_e]
  -- For each v : Fin n, sum (1 - inDeg) over slab v.succ equals (dR - 1) if dR ≥ 1 else -1 = dR - 1!
  have hstep_sum : ∀ v : Fin n,
      ((Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ) -
        ((∑ r : Fin ((S.activeEdges H v.succ).card + 1), (S.slabInEdges H ⟨v.succ, r⟩).card : ℕ) : ℤ)) =
      ((S.rightEdges H v).card : ℤ) - 1 := by
    intro v
    have hcard : Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) =
        (S.activeEdges H v.succ).card + 1 := Fintype.card_fin _
    rw [hcard]
    push_cast
    rw [show ((S.activeEdges H v.succ).card : ℤ) + 1 =
        ∑ _ : Fin ((S.activeEdges H v.succ).card + 1), (1 : ℤ) by simp]
    rw [← Finset.sum_sub_distrib]
    set p := (S.passBelow H v).card
    set dR := (S.rightEdges H v).card
    have hpR := S.passBelow_add_right_le H hHG v
    have hterm : ∀ r : Fin ((S.activeEdges H v.succ).card + 1),
        (1 : ℤ) - ((S.slabInEdges H ⟨v.succ, r⟩).card : ℤ) =
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) -
          (if r.val = p ∧ dR = 0 then (1 : ℤ) else 0) := by
      intro r
      rw [S.slabInEdges_succ_card H hHG hdeg v r]
      split_ifs with h1 h2 <;> omega
    simp_rw [hterm, Finset.sum_sub_distrib]
    by_cases hdR : dR = 0
    · have h1 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; rw [if_neg (by omega)]
      have h2 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if r.val = p ∧ dR = 0 then (1 : ℤ) else 0) = 1 := by
        have hp_lt : p < (S.activeEdges H v.succ).card + 1 := by omega
        have heq : ∀ r : Fin ((S.activeEdges H v.succ).card + 1),
            (r.val = p ∧ dR = 0) ↔ r = ⟨p, hp_lt⟩ := by
          intro r; simp [hdR, Fin.ext_iff]
        simp_rw [heq]; simp
      rw [h1, h2, hdR]; ring
    · have h2 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if r.val = p ∧ dR = 0 then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; rw [if_neg (by tauto)]
      have h1 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) = (dR : ℤ) - 1 := by
        rw [Finset.sum_boole]
        have hcnt : (Finset.univ.filter (fun r : Fin ((S.activeEdges H v.succ).card + 1) =>
            p < r.val ∧ r.val < p + dR)).card = dR - 1 := by
          have : (Finset.univ.filter (fun r : Fin ((S.activeEdges H v.succ).card + 1) =>
              p < r.val ∧ r.val < p + dR)).card = (Finset.Ioo p (p + dR)).card := by
            refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
            · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
              exact Finset.mem_Ioo.mpr hr
            · intro r₁ _ r₂ _ h; exact Fin.ext h
            · intro k hk
              rw [Finset.mem_Ioo] at hk
              exact ⟨⟨k, by omega⟩, by simp [hk.1, hk.2], rfl⟩
          rw [this, Nat.card_Ioo]; omega
        rw [hcnt]
        have : 1 ≤ dR := Nat.one_le_iff_ne_zero.mpr hdR
        push_cast [Nat.cast_sub this]; rfl
      rw [h1, h2]; ring
  have hsumR : ∑ v : Fin n, (S.rightEdges H v).card = (S.orientEdges H).card := by
    have hpart : S.orientEdges H = Finset.univ.biUnion (fun v : Fin n => S.rightEdges H v) := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, rightEdges, Finset.mem_filter]
      exact ⟨fun h => ⟨e.1, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    rw [hpart, Finset.card_biUnion]
    intro v₁ _ v₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [rightEdges, Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  push_cast
  have hdiff :
      (1 + ∑ v : Fin n, (Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ)) -
      (0 + ∑ v : Fin n, ∑ r : Fin ((S.activeEdges H v.succ).card + 1), ((S.slabInEdges H ⟨v.succ, r⟩).card : ℤ)) =
      1 + ∑ v : Fin n, ((Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ) -
        ((∑ r : Fin ((S.activeEdges H v.succ).card + 1), (S.slabInEdges H ⟨v.succ, r⟩).card : ℕ) : ℤ)) := by
    push_cast; rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  simp_rw [hstep_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hRcast : (∑ v : Fin n, ((S.rightEdges H v).card : ℤ)) = ((S.orientEdges H).card : ℤ) := by
    exact_mod_cast hsumR
  rw [hRcast]; ring

/-- Outer trapezoid `(0, 0)` of `T(H)`. -/
private def outerVert : S.SlabVert H := ⟨0, ⟨0, Nat.succ_pos _⟩⟩

/-- The outer cycle in `T(H)`: the top edge `e₀ = {(0,0), (1, |A₁|)}` can be deleted while keeping
    `(0,0)` and `(1, |A₁|)` connected via the bottom+top boundary path! -/
private lemma slab_outer_cycle (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    let v0 : Fin n := ⟨0, by have := S.hn; omega⟩
    let u0 : S.SlabVert H := S.outerVert H
    let u1 : S.SlabVert H := ⟨v0.succ, Fin.last _⟩
    (S.slabGraph H).Adj u0 u1 ∧
    ((S.slabGraph H).deleteEdges {s(u0, u1)}).Reachable u0 u1 := by
  classical
  intro v0 u0 u1
  have hL0 : (S.leftEdges H v0).card = 0 := by
    unfold leftEdges
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he h2
    simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hlt0 : e.1 < v0 := h2 ▸ he.1
    have : e.1.val < 0 := hlt0
    omega
  have hR0 : 1 ≤ (S.rightEdges H v0).card := by have := hdeg v0; omega
  have hA0 : (S.activeEdges H v0.castSucc).card = 0 := by
    have : v0.castSucc = (0 : Fin (n + 1)) := Fin.ext rfl
    rw [this, S.activeEdges_zero, Finset.card_empty]
  have hA1 : 1 ≤ (S.activeEdges H v0.succ).card := by
    have := S.activeEdges_card_step H v0; omega
  have hp0 : (S.passBelow H v0).card = 0 := by
    have := S.passBelow_add_left_le H hHG v0; omega
  have hadj01 : (S.slabGraph H).Adj u0 u1 := by
    have h0eq : u0 = ⟨v0.castSucc, ⟨0, Nat.succ_pos _⟩⟩ := rfl
    rw [h0eq]
    apply S.slabGraph_adj_step H v0
    right
    refine ⟨by omega, ?_⟩
    have := S.activeEdges_card_step H v0
    simp [Fin.val_last]; omega
  refine ⟨hadj01, ?_⟩
  let G' := (S.slabGraph H).deleteEdges {s(u0, u1)}
  -- Bottom path: (0, 0) ~ (1, 0) ~ ... ~ (n, 0)
  have hbot : ∀ k : ℕ, (hk : k ≤ n) → G'.Reachable u0 ⟨⟨k, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ihk =>
      intro hk
      let vk : Fin n := ⟨k, by omega⟩
      have hprev := ihk (by omega)
      have hstep_adj : (S.slabGraph H).Adj ⟨vk.castSucc, ⟨0, Nat.succ_pos _⟩⟩ ⟨vk.succ, ⟨0, Nat.succ_pos _⟩⟩ := by
        apply S.slabGraph_adj_step H vk; left; exact ⟨Nat.zero_le _, rfl⟩
      have hne_e : s((⟨vk.castSucc, ⟨0, Nat.succ_pos _⟩⟩ : S.SlabVert H), ⟨vk.succ, ⟨0, Nat.succ_pos _⟩⟩) ≠ s(u0, u1) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · have : (0 : ℕ) = (S.activeEdges H v0.succ).card := by
            have hval := congrArg (fun x : S.SlabVert H => x.2.val) h2
            simpa [u1, Fin.val_last] using hval
          omega
        · have : k = 1 := by
            have hval := congrArg (fun x : S.SlabVert H => x.1.val) h1
            simpa [u1, v0, vk] using hval
          have : (0 : ℕ) = (S.activeEdges H v0.succ).card := by
            have hval := congrArg (fun x : S.SlabVert H => x.2.val) h1
            simpa [u1, Fin.val_last] using hval
          omega
      have hstep : G'.Adj ⟨vk.castSucc, ⟨0, Nat.succ_pos _⟩⟩ ⟨vk.succ, ⟨0, Nat.succ_pos _⟩⟩ :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hstep_adj, fun h => hne_e (Set.mem_singleton_iff.mp h)⟩
      exact hprev.trans hstep.reachable
  -- Top path from slab k (1 ≤ k ≤ n) up to slab n: (k, last) ~ (k+1, last) ~ ... ~ (n, last)
  have htop : ∀ d : ℕ, (hd : d ≤ n - 1) →
      G'.Reachable ⟨⟨n - d, by omega⟩, Fin.last _⟩ ⟨Fin.last n, Fin.last _⟩ := by
    intro d
    induction d with
    | zero =>
      intro _
      have hi : (⟨n - 0, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
      have heq : (⟨⟨n - 0, by omega⟩, Fin.last _⟩ : S.SlabVert H) = ⟨Fin.last n, Fin.last _⟩ :=
        S.slabVert_ext H hi (by simp only [Fin.val_last]; exact congrArg (fun j => (S.activeEdges H j).card) hi)
      exact heq ▸ SimpleGraph.Reachable.refl _
    | succ d ihd =>
      intro hd
      let vk : Fin n := ⟨n - (d + 1), by omega⟩
      have hstep_adj : (S.slabGraph H).Adj ⟨vk.castSucc, Fin.last _⟩ ⟨vk.succ, Fin.last _⟩ := by
        apply S.slabGraph_adj_step H vk; right
        have hstep := S.activeEdges_card_step H vk
        have hpL := S.passBelow_add_left_le H hHG vk
        simp only [Fin.val_last]
        omega
      have hne_e : s((⟨vk.castSucc, Fin.last _⟩ : S.SlabVert H), ⟨vk.succ, Fin.last _⟩) ≠ s(u0, u1) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · have : n - (d + 1) = 0 := by
            have := congrArg (fun x : S.SlabVert H => x.1.val) h1
            simpa [u0, outerVert, vk] using this
          omega
        · have : n - (d + 1) + 1 = 0 := by
            have := congrArg (fun x : S.SlabVert H => x.1.val) h2
            simpa [u0, outerVert, vk] using this
          omega
      have hstep : G'.Adj ⟨vk.castSucc, Fin.last _⟩ ⟨vk.succ, Fin.last _⟩ :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hstep_adj, fun h => hne_e (Set.mem_singleton_iff.mp h)⟩
      have hnext := ihd (by omega)
      have hi : vk.succ = ⟨n - d, by omega⟩ := Fin.ext (by simp [vk]; omega)
      have heq_next : (⟨vk.succ, Fin.last _⟩ : S.SlabVert H) = ⟨⟨n - d, by omega⟩, Fin.last _⟩ :=
        S.slabVert_ext H hi (by simp [Fin.val_last, hi])
      rw [heq_next] at hstep
      have heq_cur : (⟨⟨n - (d + 1), by omega⟩, Fin.last _⟩ : S.SlabVert H) = ⟨vk.castSucc, Fin.last _⟩ := rfl
      rw [heq_cur]
      exact hstep.reachable.trans hnext
  -- Connect u0 -> (n, 0) = (n, last) <- (1, last) = u1
  have h1 := hbot n le_rfl
  have h2 := htop (n - 1) le_rfl
  have hlast_eq : (⟨⟨n, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ : S.SlabVert H) = ⟨Fin.last n, Fin.last _⟩ :=
    S.slabVert_ext H (Fin.ext rfl) (by simp [Fin.val_last, S.activeEdges_last])
  have hi1 : (⟨n - (n - 1), by omega⟩ : Fin (n + 1)) = v0.succ := Fin.ext (by simp [v0]; have := S.hn; omega)
  have hu1_eq : (⟨⟨n - (n - 1), by omega⟩, Fin.last _⟩ : S.SlabVert H) = u1 :=
    S.slabVert_ext H hi1 (by simp [Fin.val_last, hi1])
  rw [hlast_eq] at h1
  rw [hu1_eq] at h2
  exact h1.trans h2.symm

/-- Euler lower bound on the number of connected components of `T(H)`:
    `c(T(H)) ≥ |E(H)| - n + 2`! -/
private lemma slab_components_ge (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    (S.orientEdges H).card + 2 ≤ Nat.card (S.slabGraph H).ConnectedComponent + n := by
  classical
  have hve := S.slab_vert_sub_edge H hHG hdeg
  have hcyc := S.slab_outer_cycle H hHG hdeg
  have hbound := card_le_edges_add_components_of_cycle_edge (S.slabGraph H) hcyc.1 hcyc.2
  omega

/-- Also for the outer component `F_out` alone: `|V(F_out)| ≤ |E(F_out)|`! -/
private lemma slab_outer_component_V_le_E (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    let F_out : Finset (S.SlabVert H) := by
      classical
      exact Finset.univ.filter (fun t => (S.slabGraph H).Reachable (S.outerVert H) t)
    F_out.card ≤ ∑ t ∈ F_out, (S.slabInEdges H t).card := by
  classical
  intro F_out
  let W := {t : S.SlabVert H // (S.slabGraph H).Reachable (S.outerVert H) t}
  let Gout : SimpleGraph W := (S.slabGraph H).induce (fun t => (S.slabGraph H).Reachable (S.outerVert H) t)
  have hcyc := S.slab_outer_cycle H hHG hdeg
  let v0 : Fin n := ⟨0, by have := S.hn; omega⟩
  let u0 : W := ⟨S.outerVert H, SimpleGraph.Reachable.refl _⟩
  let u1 : W := ⟨⟨v0.succ, Fin.last _⟩, hcyc.1.reachable⟩
  have hadj : Gout.Adj u0 u1 := hcyc.1
  -- Gout.deleteEdges {s(u0, u1)} is connected because hcyc.2 gives a walk in T(H)\{e₀}
  -- whose vertices are ALL reachable from outerVert!
  have hreach_del : (Gout.deleteEdges {s(u0, u1)}).Reachable u0 u1 := by
    obtain ⟨p⟩ := hcyc.2
    have hlift : ∀ (x y : S.SlabVert H) (hx : (S.slabGraph H).Reachable (S.outerVert H) x)
        (q : ((S.slabGraph H).deleteEdges {s(u0.1, u1.1)}).Walk x y),
        (Gout.deleteEdges {s(u0, u1)}).Reachable ⟨x, hx⟩ ⟨y, hx.trans (q.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))).reachable⟩ := by
      intro x y hx q
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a₁ b₁ c hab q' ihq =>
        obtain ⟨hab1, hab2⟩ := SimpleGraph.deleteEdges_adj.mp hab
        have hb : (S.slabGraph H).Reachable (S.outerVert H) b₁ := hx.trans hab1.reachable
        have hstep : (Gout.deleteEdges {s(u0, u1)}).Adj ⟨a₁, hx⟩ ⟨b₁, hb⟩ := by
          refine SimpleGraph.deleteEdges_adj.mpr ⟨hab1, ?_⟩
          intro hmem
          have heq : s((⟨a₁, hx⟩ : W), ⟨b₁, hb⟩) = s(u0, u1) := by simpa using hmem
          apply hab2
          rw [Set.mem_singleton_iff]
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)
          · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)
        exact hstep.reachable.trans (ihq hb)
    exact hlift u0.1 u1.1 u0.2 p
  have hGout_conn : Gout.Connected := by
    refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨u0⟩
    have hlift : ∀ (x y : S.SlabVert H) (hx : (S.slabGraph H).Reachable (S.outerVert H) x)
        (q : (S.slabGraph H).Walk x y),
        Gout.Reachable ⟨x, hx⟩ ⟨y, hx.trans q.reachable⟩ := by
      intro x y hx q
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a₁ b₁ c hab q' ihq =>
        have hb : (S.slabGraph H).Reachable (S.outerVert H) b₁ := hx.trans hab.reachable
        exact (show Gout.Adj ⟨a₁, hx⟩ ⟨b₁, hb⟩ from hab).reachable.trans (ihq hb)
    have ha : Gout.Reachable u0 a := by obtain ⟨p⟩ := a.2; exact hlift _ _ u0.2 p
    have hb : Gout.Reachable u0 b := by obtain ⟨p⟩ := b.2; exact hlift _ _ u0.2 p
    exact ha.symm.trans hb
  have hbound := card_le_edges_add_components_of_cycle_edge Gout hadj hreach_del
  rw [connected_natCard_components hGout_conn] at hbound
  have hcardW : Fintype.card W = F_out.card := by
    rw [Fintype.card_subtype]
  -- And Gout.edgeFinset.card = ∑ t ∈ F_out, (slabInEdges H t).card!
  have hedgesW : Gout.edgeFinset.card = ∑ t ∈ F_out, (S.slabInEdges H t).card := by
    rw [← Finset.card_sigma]
    symm
    refine Finset.card_bij
      (fun p hp => s(⟨p.2, by
        have h1 := (Finset.mem_sigma.mp hp).1
        have h2 := (Finset.mem_sigma.mp hp).2
        simp only [F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h1.trans h2.2.symm.reachable⟩,
        ⟨p.1, by
          have h1 := (Finset.mem_sigma.mp hp).1
          simp only [F_out, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          exact h1⟩)) ?_ ?_ ?_
    · intro ⟨t, s⟩ hp
      have h2 := (Finset.mem_sigma.mp hp).2
      simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h2
      exact Gout.mem_edgeFinset.mpr h2.2
    · intro ⟨t₁, s₁⟩ h1 ⟨t₂, s₂⟩ h2 heq
      have h1' := (Finset.mem_sigma.mp h1).2
      have h2' := (Finset.mem_sigma.mp h2).2
      simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h1' h2'
      rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Sigma.ext (congrArg Subtype.val ht) (heq_of_eq (congrArg Subtype.val hs))
      · exfalso
        have hv1 := h1'.1; have hv2 := h2'.1
        have hs' : s₁ = t₂ := congrArg Subtype.val hs
        have ht' : t₁ = s₂ := congrArg Subtype.val ht
        rw [hs', ht'] at hv1; omega
    · intro e he
      induction e using Sym2.ind with | _ x y =>
      have hadj' : (S.slabGraph H).Adj x.1 y.1 := Gout.mem_edgeFinset.mp he
      rcases hadj' with ⟨v, h1, h2, hg⟩ | ⟨v, h1, h2, hg⟩
      · refine ⟨⟨y.1, x.1⟩, ?_, by simp⟩
        simp only [Finset.mem_sigma, F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y.2, by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
      · refine ⟨⟨x.1, y.1⟩, ?_, by simp [Sym2.eq_swap]⟩
        simp only [Finset.mem_sigma, F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x.2, by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
  omega

/- ### Edge Rank in a Slab and the Left-Side Dart Map `τ_H : DartOf H → SlabVert H` -/

/-- Rank of an active edge `e ∈ activeEdges H i`: number of edges in `activeEdges H i` strictly
    below `e` at `slabMid i`. -/
private noncomputable def edgeRank (i : Fin (n + 1)) (e : Fin n × Fin n) : ℕ := by
  classical
  exact ((S.activeEdges H i).filter (fun e' =>
    edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i))).card

private lemma edgeRank_lt {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges H i) :
    S.edgeRank H i e < (S.activeEdges H i).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have : e ∈ (S.activeEdges H i).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i)) := by rw [h]; exact he
  simp only [Finset.mem_filter] at this
  exact lt_irrefl _ this.2

/-- Exact rank of a passing edge `(a, b)` in slab `v.castSucc` vs `v.succ`:
    - If `e ∈ passBelow H v`: `rank(v.castSucc, e) < p_v` AND `rank(v.succ, e) = rank(v.castSucc, e)`.
    - If `e ∈ passAbove H v`: `rank(v.castSucc, e) ≥ p_v + d_v^-` AND `rank(v.succ, e) + d_v^- = rank(v.castSucc, e) + d_v^+`. -/
private lemma edgeRank_passBelow (hHG : H ≤ S.G) {v : Fin n} {e : Fin n × Fin n} (he : e ∈ S.passBelow H v) :
    S.edgeRank H v.castSucc e < (S.passBelow H v).card ∧
    S.edgeRank H v.succ e = S.edgeRank H v.castSucc e := by
  classical
  have hpe : e ∈ S.passEdges H v := (Finset.mem_filter.mp he).1
  have he_lt : edgeY S.p e.1 e.2 (S.p v).re < (S.p v).im := (Finset.mem_filter.mp he).2
  have hpe' := Finset.mem_filter.mp hpe
  have he_or := Finset.mem_filter.mp hpe'.1
  have he_ac1 : e ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hpe
  have he_ac2 : e ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hpe
  have hmid1 := S.slabMid_between H he_ac1
  have hmid2 := S.slabMid_between H he_ac2
  have hmid1_lt_v : S.slabMid v.castSucc < (S.p v).re :=
    S.slabMid_castSucc_lt (by have := hpe'.2.1; omega)
  have hv_lt_mid2 : (S.p v).re < S.slabMid v.succ :=
    S.lt_slabMid_succ (by have := hpe'.2.2; omega)
  -- Every edge strictly below e at mid(v.castSucc) must be in passBelow H v, and strictly below e at (p v).re!
  have hfilt1 : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) =
      (S.passBelow H v).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid1' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact ⟨he'b, hlt⟩
        · exfalso
          have ha_gt := (Finset.mem_filter.mp he'a).2
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at ha_gt; linarith
          have := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid1'.1 hmid1'.2 hmid1.1 hmid1.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt
          linarith
      · exfalso
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have huv : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj e'.1 v := hL'.2 ▸ hHG ho'.2.2
        have hlt_inc := (S.edgeY_lt_incident_left hpe'.2.1 hpe'.2.2 huv (hHG he_or.2.2) hadj'
          hmid1.1 hmid1'.1 hmid1_lt_v).mpr he_lt
        rw [hL'.2] at hlt
        linarith
    · rintro ⟨he'b, hlt⟩
      refine ⟨?_, hlt⟩
      rw [(S.activeEdges_castSucc_eq H v).1]
      exact Finset.mem_union_left _ (Finset.mem_filter.mp he'b).1
  have hfilt2 : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p e.1 e.2 (S.slabMid v.succ)) =
      (S.passBelow H v).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid2' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hlt_v := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt
        have hlt_1 := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hlt
        exact ⟨Finset.mem_filter.mpr ⟨he'p, hlt_v.trans he_lt⟩, hlt_1⟩
      · exfalso
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hvw : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj v e'.2 := hR'.2 ▸ hHG ho'.2.2
        have hlt_inc := (S.edgeY_lt_incident_right hpe'.2.1 hpe'.2.2 hvw (hHG he_or.2.2) hadj'
          hv_lt_mid2 hmid2.2 hmid2'.2).mpr he_lt
        rw [hR'.2] at hlt
        linarith
    · rintro ⟨he'b, hlt⟩
      have he'p := (Finset.mem_filter.mp he'b).1
      have hp' := Finset.mem_filter.mp he'p
      have ho' := Finset.mem_filter.mp hp'.1
      have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
        rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
      have he'ac2 : e' ∈ S.activeEdges H v.succ := by
        rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
      have hmid1' := S.slabMid_between H he'ac1
      have hmid2' := S.slabMid_between H he'ac2
      have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
        hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hlt⟩
  constructor
  · unfold edgeRank
    rw [hfilt1]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have : e ∈ (S.passBelow H v).filter (fun e' =>
        edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
      rw [h]; exact he
    exact lt_irrefl _ (Finset.mem_filter.mp this).2
  · unfold edgeRank; rw [hfilt1, hfilt2]

private lemma edgeRank_passAbove (hHG : H ≤ S.G) {v : Fin n} {e : Fin n × Fin n} (he : e ∈ S.passAbove H v) :
    (S.passBelow H v).card + (S.leftEdges H v).card ≤ S.edgeRank H v.castSucc e ∧
    S.edgeRank H v.succ e + (S.leftEdges H v).card =
      S.edgeRank H v.castSucc e + (S.rightEdges H v).card := by
  classical
  have hpe : e ∈ S.passEdges H v := (Finset.mem_filter.mp he).1
  have he_gt : (S.p v).im < edgeY S.p e.1 e.2 (S.p v).re := (Finset.mem_filter.mp he).2
  have hpe' := Finset.mem_filter.mp hpe
  have he_or := Finset.mem_filter.mp hpe'.1
  have he_ac1 : e ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hpe
  have he_ac2 : e ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hpe
  have hmid1 := S.slabMid_between H he_ac1
  have hmid2 := S.slabMid_between H he_ac2
  have hmid1_lt_v : S.slabMid v.castSucc < (S.p v).re :=
    S.slabMid_castSucc_lt (by have := hpe'.2.1; omega)
  have hv_lt_mid2 : (S.p v).re < S.slabMid v.succ :=
    S.lt_slabMid_succ (by have := hpe'.2.2; omega)
  let Q := (S.passAbove H v).filter (fun e' =>
    edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re)
  have hfilt1 : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) =
      (S.passBelow H v ∪ S.leftEdges H v) ∪ Q := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union, Q]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid1' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact Or.inl (Or.inl he'b)
        · right
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          exact ⟨he'a, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid1'.1 hmid1'.2 hmid1.1 hmid1.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt⟩
      · exact Or.inl (Or.inr he'L)
    · rintro ((he'b | he'L) | ⟨he'a, hltv⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hltv : edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re :=
          (Finset.mem_filter.mp he'b).2.trans he_gt
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac1, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hltv⟩
      · have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_right _ he'L
        have hmid1' := S.slabMid_between H he'ac1
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have huv : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj e'.1 v := hL'.2 ▸ hHG ho'.2.2
        have hnot := (S.edgeY_lt_incident_left hpe'.2.1 hpe'.2.2 huv (hHG he_or.2.2) hadj'
          hmid1.1 hmid1'.1 hmid1_lt_v).not.mpr (not_lt.mpr he_gt.le)
        have hne_y := S.edgeY_ne_of_ne_edges he_or.2.1 huv (hHG he_or.2.2) hadj'
          (fun h => hpe'.2.2.ne (congrArg Prod.snd h).symm)
          hmid1.1 hmid1.2 hmid1'.1 hmid1_lt_v
        rw [hL'.2]
        exact ⟨he'ac1, lt_of_le_of_ne (not_lt.mp hnot) hne_y.symm⟩
      · have he'p := (Finset.mem_filter.mp he'a).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac1, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hltv⟩
  have hfilt2 : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p e.1 e.2 (S.slabMid v.succ)) =
      (S.passBelow H v ∪ S.rightEdges H v) ∪ Q := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union, Q]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid2' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact Or.inl (Or.inl he'b)
        · right
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          exact ⟨he'a, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt⟩
      · exact Or.inl (Or.inr he'R)
    · rintro ((he'b | he'R) | ⟨he'a, hltv⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid2' := S.slabMid_between H he'ac2
        have hltv : edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re :=
          (Finset.mem_filter.mp he'b).2.trans he_gt
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hltv⟩
      · have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_right _ he'R
        have hmid2' := S.slabMid_between H he'ac2
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hvw : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj v e'.2 := hR'.2 ▸ hHG ho'.2.2
        have hnot := (S.edgeY_lt_incident_right hpe'.2.1 hpe'.2.2 hvw (hHG he_or.2.2) hadj'
          hv_lt_mid2 hmid2.2 hmid2'.2).not.mpr (not_lt.mpr he_gt.le)
        have hne_y := S.edgeY_ne_of_ne_edges he_or.2.1 hvw (hHG he_or.2.2) hadj'
          (fun h => hpe'.2.1.ne (congrArg Prod.fst h))
          hmid2.1 hmid2.2 hv_lt_mid2 hmid2'.2
        rw [hR'.2]
        exact ⟨he'ac2, lt_of_le_of_ne (not_lt.mp hnot) hne_y.symm⟩
      · have he'p := (Finset.mem_filter.mp he'a).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid2' := S.slabMid_between H he'ac2
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hltv⟩
  have hdisj1 : Disjoint (S.passBelow H v) (S.leftEdges H v) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_castSucc_eq H v).2
  have hdisj2 : Disjoint (S.passBelow H v) (S.rightEdges H v) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_succ_eq H v).2
  have hdisjQ1 : Disjoint (S.passBelow H v ∪ S.leftEdges H v) Q := by
    rw [Finset.disjoint_union_left]
    exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
      Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        (S.activeEdges_castSucc_eq H v).2.symm⟩
  have hdisjQ2 : Disjoint (S.passBelow H v ∪ S.rightEdges H v) Q := by
    rw [Finset.disjoint_union_left]
    exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
      Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        (S.activeEdges_succ_eq H v).2.symm⟩
  have hc1 : S.edgeRank H v.castSucc e = (S.passBelow H v).card + (S.leftEdges H v).card + Q.card := by
    unfold edgeRank
    rw [hfilt1, Finset.card_union_of_disjoint hdisjQ1, Finset.card_union_of_disjoint hdisj1]
  have hc2 : S.edgeRank H v.succ e = (S.passBelow H v).card + (S.rightEdges H v).card + Q.card := by
    unfold edgeRank
    rw [hfilt2, Finset.card_union_of_disjoint hdisjQ2, Finset.card_union_of_disjoint hdisj2]
  omega

/-- Exact rank of a right-going edge `(v, w)` (`v < w`) in slab `v.succ`:
    `p_v + #{w' ∈ R_v | heading(p w' - p v) < heading(p w - p v)}`. -/
private lemma edgeRank_rightEdge (hHG : H ≤ S.G) {v w : Fin n} (hvw : v < w) (hadj : H.Adj v w) :
    S.edgeRank H v.succ (v, w) =
      (S.passBelow H v).card +
      ((S.rightEdges H v).filter (fun e' =>
        heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))).card := by
  classical
  have hmem : (v, w) ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw, hadj⟩, rfl⟩)
  have hmid := S.slabMid_between H hmem
  have hv_lt_mid : (S.p v).re < S.slabMid v.succ := hmid.1
  have hfilt : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p v w (S.slabMid v.succ)) =
      S.passBelow H v ∪ (S.rightEdges H v).filter (fun e' =>
        heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · left
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        refine Finset.mem_filter.mpr ⟨he'p, ?_⟩
        exact (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hvw (hHG ho'.2.2) (hHG hadj)
          hv_lt_mid hmid'.2 hmid.2).mp hlt
      · right
        refine ⟨he'R, ?_⟩
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
        rw [hR'.2] at hlt
        rw [edgeY_eq_left_add_slope, edgeY_eq_left_add_slope] at hlt
        have hsl : edgeSlope S.p v e'.2 < edgeSlope S.p v w := by
          have : 0 < S.slabMid v.succ - (S.p v).re := by linarith
          nlinarith
        exact (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hve')
          (S.p_sub_re_pos_iff.mpr hvw)).mpr (by simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using hsl)
    · rintro (he'b | ⟨he'R, hlt⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid' := S.slabMid_between H he'ac
        exact ⟨he'ac, (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hvw (hHG ho'.2.2) (hHG hadj)
          hv_lt_mid hmid'.2 hmid.2).mpr (Finset.mem_filter.mp he'b).2⟩
      · have he'ac : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_right _ he'R
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hsl : edgeSlope S.p v e'.2 < edgeSlope S.p v w := by
          have := (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hve')
            (S.p_sub_re_pos_iff.mpr hvw)).mp hlt
          simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using this
        refine ⟨he'ac, ?_⟩
        rw [hR'.2, edgeY_eq_left_add_slope, edgeY_eq_left_add_slope]
        have : 0 < S.slabMid v.succ - (S.p v).re := by linarith
        nlinarith
  have hdisj : Disjoint (S.passBelow H v)
      ((S.rightEdges H v).filter (fun e' => heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (S.activeEdges_succ_eq H v).2
  unfold edgeRank
  rw [hfilt, Finset.card_union_of_disjoint hdisj]

/-- Exact rank of a left-going edge `(u, v)` (`u < v`) in slab `v.castSucc`:
    `p_v + #{u' ∈ L_v | heading(p u - p v) < heading(p u' - p v)}`!
    (Remember: larger heading for left neighbors means LOWER y-value at `x < x_v`!) -/
private lemma edgeRank_leftEdge (hHG : H ≤ S.G) {u v : Fin n} (huv : u < v) (hadj : H.Adj u v) :
    S.edgeRank H v.castSucc (u, v) =
      (S.passBelow H v).card +
      ((S.leftEdges H v).filter (fun e' =>
        heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))).card := by
  classical
  have hmem : (u, v) ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, rfl⟩)
  have hmid := S.slabMid_between H hmem
  have hmid_lt_v : S.slabMid v.castSucc < (S.p v).re := hmid.2
  have hfilt : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p u v (S.slabMid v.castSucc)) =
      S.passBelow H v ∪ (S.leftEdges H v).filter (fun e' =>
        heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · left
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        refine Finset.mem_filter.mpr ⟨he'p, ?_⟩
        exact (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 huv (hHG ho'.2.2) (hHG hadj)
          hmid'.1 hmid.1 hmid_lt_v).mp hlt
      · right
        refine ⟨he'L, ?_⟩
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
        rw [hL'.2] at hlt
        rw [edgeY_eq_right_sub_slope S.p (S.hx_mono he'v), edgeY_eq_right_sub_slope S.p (S.hx_mono huv)] at hlt
        have hsl : edgeSlope S.p u v < edgeSlope S.p e'.1 v := by
          have : 0 < (S.p v).re - S.slabMid v.castSucc := by linarith
          nlinarith
        have hsl' : (S.p u - S.p v).im / (S.p u - S.p v).re < (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re := by
          have h1 : (S.p u - S.p v).im / (S.p u - S.p v).re = edgeSlope S.p u v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]
            rw [← neg_div_neg_eq]; ring_nf
          have h2 : (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re = edgeSlope S.p e'.1 v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]
            rw [← neg_div_neg_eq]; ring_nf
          linarith
        exact (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr huv)
          (S.p_sub_re_neg_iff.mpr he'v)).mpr hsl'
    · rintro (he'b | ⟨he'L, hlt⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid' := S.slabMid_between H he'ac
        exact ⟨he'ac, (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 huv (hHG ho'.2.2) (hHG hadj)
          hmid'.1 hmid.1 hmid_lt_v).mpr (Finset.mem_filter.mp he'b).2⟩
      · have he'ac : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_right _ he'L
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hsl' := (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr huv)
          (S.p_sub_re_neg_iff.mpr he'v)).mp hlt
        have hsl : edgeSlope S.p u v < edgeSlope S.p e'.1 v := by
          have h1 : (S.p u - S.p v).im / (S.p u - S.p v).re = edgeSlope S.p u v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
          have h2 : (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re = edgeSlope S.p e'.1 v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
          linarith
        refine ⟨he'ac, ?_⟩
        rw [hL'.2, edgeY_eq_right_sub_slope S.p (S.hx_mono he'v), edgeY_eq_right_sub_slope S.p (S.hx_mono huv)]
        have : 0 < (S.p v).re - S.slabMid v.castSucc := by linarith
        nlinarith
  have hdisj : Disjoint (S.passBelow H v)
      ((S.leftEdges H v).filter (fun e' => heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (S.activeEdges_castSucc_eq H v).2
  unfold edgeRank
  rw [hfilt, Finset.card_union_of_disjoint hdisj]

/-- Along any edge `e = (a, b)` (`a < b`), the trapezoid immediately ABOVE `e` stays in the same
    connected component of `T(H)` across all slabs `a + 1 ≤ i ≤ b`, and likewise for the trapezoid
    immediately BELOW `e`. -/
private lemma edge_top_connected (hHG : H ≤ S.G) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    (i j : Fin (n + 1)) (hi1 : a.val < i.val) (hi2 : i.val ≤ b.val)
    (hj1 : a.val < j.val) (hj2 : j.val ≤ b.val) :
    have hi : (a, b) ∈ S.activeEdges H i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hi1, hi2⟩
    have hj : (a, b) ∈ S.activeEdges H j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hj1, hj2⟩
    (S.slabGraph H).Reachable
      ⟨i, ⟨S.edgeRank H i (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hi)⟩⟩
      ⟨j, ⟨S.edgeRank H j (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hj)⟩⟩ := by
  classical
  -- Step lemma: from v.castSucc to v.succ when a < v < b
  have hstep : ∀ (v : Fin n) (hav : a < v) (hvb : v < b),
      have h1 : (a, b) ∈ S.activeEdges H v.castSucc :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simpa, by simpa using hvb.le⟩
      have h2 : (a, b) ∈ S.activeEdges H v.succ :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp; omega, by simp; omega⟩
      (S.slabGraph H).Adj
        ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h1)⟩⟩
        ⟨v.succ, ⟨S.edgeRank H v.succ (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h2)⟩⟩ := by
    intro v hav hvb
    have hp : (a, b) ∈ S.passEdges H v :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hav, hvb⟩
    rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hp
    apply S.slabGraph_adj_step H v
    rcases hp with hpb | hpa
    · have hr := S.edgeRank_passBelow H hHG hpb
      left; dsimp only; exact ⟨by omega, by omega⟩
    · have hr := S.edgeRank_passAbove H hHG hpa
      right; dsimp only; exact ⟨by omega, by omega⟩
  suffices hmono : ∀ (d : ℕ) (k : Fin (n + 1)) (hk1 : a.val < k.val) (hk2 : k.val + d ≤ b.val),
      ∀ (h1 : (a, b) ∈ S.activeEdges H k)
        (h2 : (a, b) ∈ S.activeEdges H ⟨k.val + d, by have := b.isLt; omega⟩),
      (S.slabGraph H).Reachable
        ⟨k, ⟨S.edgeRank H k (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h1)⟩⟩
        ⟨⟨k.val + d, by have := b.isLt; omega⟩, ⟨S.edgeRank H ⟨k.val + d, by have := b.isLt; omega⟩ (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h2)⟩⟩ by
    intro hi hj
    rcases le_total i.val j.val with hij | hji
    · have hi' : (⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      have hres := hmono (j.val - i.val) i hi1 (by omega) hi (hi' ▸ hj)
      have heq_j : (⟨⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ (a, b) + 1,
            Nat.succ_lt_succ (S.edgeRank_lt H (hi' ▸ hj))⟩⟩ : S.SlabVert H) =
          ⟨j, ⟨S.edgeRank H j (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hj)⟩⟩ :=
        S.slabVert_ext H hi' (by dsimp; rw [hi'])
      rw [heq_j] at hres; exact hres
    · have hj' : (⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
      have hres := hmono (i.val - j.val) j hj1 (by omega) hj (hj' ▸ hi)
      have heq_i : (⟨⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ (a, b) + 1,
            Nat.succ_lt_succ (S.edgeRank_lt H (hj' ▸ hi))⟩⟩ : S.SlabVert H) =
          ⟨i, ⟨S.edgeRank H i (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hi)⟩⟩ :=
        S.slabVert_ext H hj' (by dsimp; rw [hj'])
      rw [heq_i] at hres; exact hres.symm
  intro d
  induction d with
  | zero => intro k _ _ h1 h2; exact SimpleGraph.Reachable.refl _
  | succ d ihd =>
    intro k hk1 hk2 h1 h2
    let v : Fin n := ⟨k.val + d, by have := b.isLt; omega⟩
    have hm : (a, b) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp [v]; omega, by simp [v]; omega⟩
    have hprev := ihd k hk1 (by omega) h1 hm
    have hst := hstep v (by show a.val < v.val; simp [v]; omega) (by show v.val < b.val; simp [v]; omega)
    exact hprev.trans hst.reachable

private lemma edge_bot_connected (hHG : H ≤ S.G) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    (i j : Fin (n + 1)) (hi1 : a.val < i.val) (hi2 : i.val ≤ b.val)
    (hj1 : a.val < j.val) (hj2 : j.val ≤ b.val) :
    have hi : (a, b) ∈ S.activeEdges H i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hi1, hi2⟩
    have hj : (a, b) ∈ S.activeEdges H j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hj1, hj2⟩
    (S.slabGraph H).Reachable
      ⟨i, ⟨S.edgeRank H i (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hi)⟩⟩
      ⟨j, ⟨S.edgeRank H j (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hj)⟩⟩ := by
  classical
  have hstep : ∀ (v : Fin n) (hav : a < v) (hvb : v < b),
      have h1 : (a, b) ∈ S.activeEdges H v.castSucc :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simpa, by simpa using hvb.le⟩
      have h2 : (a, b) ∈ S.activeEdges H v.succ :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp; omega, by simp; omega⟩
      (S.slabGraph H).Adj
        ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h1)⟩⟩
        ⟨v.succ, ⟨S.edgeRank H v.succ (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h2)⟩⟩ := by
    intro v hav hvb
    have hp : (a, b) ∈ S.passEdges H v :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hav, hvb⟩
    rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hp
    apply S.slabGraph_adj_step H v
    rcases hp with hpb | hpa
    · have hr := S.edgeRank_passBelow H hHG hpb
      left; dsimp only; exact ⟨by omega, by omega⟩
    · have hr := S.edgeRank_passAbove H hHG hpa
      right; dsimp only; exact ⟨by omega, by omega⟩
  suffices hmono : ∀ (d : ℕ) (k : Fin (n + 1)) (hk1 : a.val < k.val) (hk2 : k.val + d ≤ b.val),
      ∀ (h1 : (a, b) ∈ S.activeEdges H k)
        (h2 : (a, b) ∈ S.activeEdges H ⟨k.val + d, by have := b.isLt; omega⟩),
      (S.slabGraph H).Reachable
        ⟨k, ⟨S.edgeRank H k (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h1)⟩⟩
        ⟨⟨k.val + d, by have := b.isLt; omega⟩, ⟨S.edgeRank H ⟨k.val + d, by have := b.isLt; omega⟩ (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h2)⟩⟩ by
    intro hi hj
    rcases le_total i.val j.val with hij | hji
    · have hi' : (⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      have hres := hmono (j.val - i.val) i hi1 (by omega) hi (hi' ▸ hj)
      have heq_j : (⟨⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ (a, b),
            Nat.lt_succ_of_lt (S.edgeRank_lt H (hi' ▸ hj))⟩⟩ : S.SlabVert H) =
          ⟨j, ⟨S.edgeRank H j (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hj)⟩⟩ :=
        S.slabVert_ext H hi' (by dsimp; rw [hi'])
      rw [heq_j] at hres; exact hres
    · have hj' : (⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
      have hres := hmono (i.val - j.val) j hj1 (by omega) hj (hj' ▸ hi)
      have heq_i : (⟨⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ (a, b),
            Nat.lt_succ_of_lt (S.edgeRank_lt H (hj' ▸ hi))⟩⟩ : S.SlabVert H) =
          ⟨i, ⟨S.edgeRank H i (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hi)⟩⟩ :=
        S.slabVert_ext H hj' (by dsimp; rw [hj'])
      rw [heq_i] at hres; exact hres.symm
  intro d
  induction d with
  | zero => intro k _ _ h1 h2; exact SimpleGraph.Reachable.refl _
  | succ d ihd =>
    intro k hk1 hk2 h1 h2
    let v : Fin n := ⟨k.val + d, by have := b.isLt; omega⟩
    have hm : (a, b) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp [v]; omega, by simp [v]; omega⟩
    have hprev := ihd k hk1 (by omega) h1 hm
    have hst := hstep v (by show a.val < v.val; simp [v]; omega) (by show v.val < b.val; simp [v]; omega)
    exact hprev.trans hst.reachable

/-- The left-side dart map `τ_H : DartOf H → SlabVert H`:
    - Right-going dart `(u, v)` (`u < v`): trapezoid immediately ABOVE `(u, v)` in slab `u.succ`.
    - Left-going dart `(u, v)` (`v < u`): trapezoid immediately BELOW `(v, u)` in slab `u.castSucc`. -/
private noncomputable def dartMap (d : DartOf H) : S.SlabVert H := by
  classical
  exact if h : d.1.1 < d.1.2 then
    have hmem : (d.1.1, d.1.2) ∈ S.activeEdges H d.1.1.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, d.2⟩, by simp, by simp; omega⟩
    ⟨d.1.1.succ, ⟨S.edgeRank H d.1.1.succ (d.1.1, d.1.2) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩
  else
    have hvu : d.1.2 < d.1.1 := lt_of_le_of_ne (not_lt.mp h) (H.ne_of_adj d.2).symm
    have hmem : (d.1.2, d.1.1) ∈ S.activeEdges H d.1.1.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, d.2.symm⟩, by simpa, by simp⟩
    ⟨d.1.1.castSucc, ⟨S.edgeRank H d.1.1.castSucc (d.1.2, d.1.1), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩

/-- Convenient endpoint connection of `dartMap` at the TARGET vertex `v = d.1.2`:
    - If `u < v`: `dartMap (u, v)` reaches `(v.castSucc, rank(v.castSucc, (u,v)) + 1)`.
    - If `v < u`: `dartMap (u, v)` reaches `(v.succ, rank(v.succ, (v,u)))`. -/
private lemma dartMap_to_target_left (hHG : H ≤ S.G) {u v : Fin n} (huv : u < v) (hadj : H.Adj u v) :
    have hmem : (u, v) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, by simpa, by simp⟩
    (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), hadj⟩)
      ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_pos huv]
  exact S.edge_top_connected H hHG huv hadj u.succ v.castSucc (by simp) (by simp; omega) (by simpa) (by simp)

private lemma dartMap_to_target_right (hHG : H ≤ S.G) {u v : Fin n} (hvu : v < u) (hadj : H.Adj u v) :
    have hmem : (v, u) ∈ S.activeEdges H v.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, hadj.symm⟩, by simp, by simp; omega⟩
    (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), hadj⟩)
      ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_neg (not_lt.mpr hvu.le)]
  exact S.edge_bot_connected H hHG hvu hadj.symm u.castSucc v.succ (by simpa) (by simp) (by simp) (by simp; omega)

/-- Convenient endpoint connection of `dartMap` at the SOURCE vertex `v = d.1.1`:
    - If `v < w`: `dartMap (v, w) = (v.succ, rank(v.succ, (v,w)) + 1)`.
    - If `w < v`: `dartMap (v, w) = (v.castSucc, rank(v.castSucc, (w,v)))`. -/
private lemma dartMap_at_source_right {v w : Fin n} (hvw : v < w) (hadj : H.Adj v w) :
    have hmem : (v, w) ∈ S.activeEdges H v.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw, hadj⟩, by simp, by simp; omega⟩
    S.dartMap H ⟨(v, w), hadj⟩ =
      ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_pos hvw]

private lemma dartMap_at_source_left {v w : Fin n} (hwv : w < v) (hadj : H.Adj v w) :
    have hmem : (w, v) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv, hadj.symm⟩, by simpa, by simp⟩
    S.dartMap H ⟨(v, w), hadj⟩ =
      ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_neg (not_lt.mpr hwv.le)]

/-- Helper: at vertex `v`, heading of any right neighbor `< π/2 <` heading of any left neighbor! -/
private lemma heading_right_lt_left {v u w : Fin n} (hvw : v < w) (huv : u < v) :
    heading (S.p w - S.p v) < heading (S.p u - S.p v) := by
  have h1 := heading_bounds_pos (S.p_sub_re_pos_iff.mpr hvw)
  have h2 := heading_bounds_neg (S.p_sub_re_neg_iff.mpr huv)
  linarith

/-- Key invariant: `dartMap H d` and `dartMap H (geoPhi H hHG d)` are ALWAYS in the SAME
    connected component of `T(H)`! -/
private lemma dartMap_phi_reachable (hHG : H ≤ S.G) (d : DartOf H) :
    (S.slabGraph H).Reachable (S.dartMap H d) (S.dartMap H (S.geoPhi H hHG d)) := by
  classical
  rcases d with ⟨⟨u, v⟩, huv⟩
  let w_sub := S.geoSigma H hHG v ⟨u, huv.symm⟩
  let w := w_sub.1
  have hvw : H.Adj v w := w_sub.2
  change (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), huv⟩) (S.dartMap H ⟨(v, w), hvw⟩)
  set p := (S.passBelow H v).card
  set dL := (S.leftEdges H v).card
  set dR := (S.rightEdges H v).card
  have hpL := S.passBelow_add_left_le H hHG v
  have hpR := S.passBelow_add_right_le H hHG v
  have hstep_c := S.activeEdges_card_step H v
  rcases S.geoSigma_spec H hHG v ⟨u, huv.symm⟩ with ⟨hmin, hmax⟩ | ⟨hlt, hgap⟩
  · -- Wrap case: u is MINIMUM heading at v, w is MAXIMUM heading at v!
    rcases lt_or_gt_of_ne (H.ne_of_adj huv) with hlt_uv | hgt_uv
    · -- Case 6 (rightCap!): u < v is min heading => NO right neighbors (dR = 0), w < v too!
      have hdR0 : dR = 0 := by
        dsimp only [dR]; unfold rightEdges
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h1
        simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have hve : v < e.2 := h1 ▸ he.1
        have hadj : H.Adj v e.2 := h1 ▸ he.2
        have h1' := hmin ⟨e.2, hadj⟩
        have h2' := S.heading_right_lt_left hve hlt_uv
        linarith
      have hlt_wv : w < v := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
        · exact h
        · exfalso; have := hmin ⟨w, hvw⟩; have := S.heading_right_lt_left h hlt_uv; linarith
      -- rank(v.castSucc, (u, v)) = p + dL - 1, rank(v.castSucc, (w, v)) = p!
      have hru : S.edgeRank H v.castSucc (u, v) = p + dL - 1 := by
        rw [S.edgeRank_leftEdge H hHG hlt_uv huv]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (u, v) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hL'.1
            have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
            refine ⟨he', lt_of_le_of_ne (hmin ⟨e'.1, hadj'⟩) (fun h => hne' ?_)⟩
            have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v h
            have hu' : u = e'.1 := congrArg Subtype.val hsub
            exact Prod.ext hu'.symm hL'.2
        have hu_mem : (u, v) ∈ S.leftEdges H v :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩
        rw [hfilt, Finset.card_erase_of_mem hu_mem]
        have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v), hu_mem⟩
        dsimp only [p, dL]; omega
      have hrw : S.edgeRank H v.castSucc (w, v) = p := by
        rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e' he' hlt'
          have hL' := Finset.mem_filter.mp he'
          have ho' := Finset.mem_filter.mp hL'.1
          have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
          exact not_lt.mpr (hmax ⟨e'.1, hadj'⟩) hlt'
        rw [hfilt, Finset.card_empty, add_zero]
      have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v),
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩⟩
      have h1 := S.dartMap_to_target_left H hHG hlt_uv huv
      have h2 := S.dartMap_at_source_left H hlt_wv hvw
      -- Connect (v.castSucc, p + dL) ~ (v.succ, p) ~ (v.castSucc, p)!
      have hmid : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by omega⟩⟩
          ⟨v.succ, ⟨p, by omega⟩⟩ := by
        apply S.slabGraph_adj_step H v; right; dsimp; omega
      have hmid2 : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by omega⟩⟩
          ⟨v.succ, ⟨p, by omega⟩⟩ := by
        apply S.slabGraph_adj_step H v; left; dsimp; omega
      rw [h2]
      exact h1.trans (hmid.reachable.trans hmid2.symm.reachable)
    · -- v < u is min heading: u is bottommost right neighbor (rank(v.succ, (v, u)) = p)
      have hru : S.edgeRank H v.succ (v, u) = p := by
        rw [S.edgeRank_rightEdge H hHG hgt_uv huv.symm]
        have hfilt : (S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p u - S.p v)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e' he' hlt'
          have hR' := Finset.mem_filter.mp he'
          have ho' := Finset.mem_filter.mp hR'.1
          have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
          exact not_lt.mpr (hmin ⟨e'.2, hadj'⟩) hlt'
        rw [hfilt, Finset.card_empty, add_zero]
      have h1 := S.dartMap_to_target_right H hHG hgt_uv huv
      rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with hlt_wv | hgt_wv
      · -- Case 4: w < v is max heading => bottommost left neighbor (rank(v.castSucc, (w,v)) = p)
        have hrw : S.edgeRank H v.castSucc (w, v) = p := by
          rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro e' he' hlt'
            have hL' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hL'.1
            have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
            exact not_lt.mpr (hmax ⟨e'.1, hadj'⟩) hlt'
          rw [hfilt, Finset.card_empty, add_zero]
        have h2 := S.dartMap_at_source_left H hlt_wv hvw
        have hglue : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; left; dsimp; omega
        rw [h2]
        exact h1.trans hglue.symm.reachable
      · -- Case 5: v < w is max heading => NO left neighbors (dL = 0), w is topmost right neighbor (rank = p + dR - 1)!
        have hdL0 : dL = 0 := by
          dsimp only [dL]; unfold leftEdges
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro e he h2
          simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
          have hev : e.1 < v := h2 ▸ he.1
          have hadj : H.Adj v e.1 := h2 ▸ he.2.symm
          have h1' := hmax ⟨e.1, hadj⟩
          have h2' := S.heading_right_lt_left hgt_wv hev
          linarith
        have hrw : S.edgeRank H v.succ (v, w) = p + dR - 1 := by
          rw [S.edgeRank_rightEdge H hHG hgt_wv hvw]
          have hfilt : (S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) = (S.rightEdges H v).erase (v, w) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hR' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hR'.1
              have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
              refine ⟨he', lt_of_le_of_ne (hmax ⟨e'.2, hadj'⟩) (fun h => hne' ?_)⟩
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v h
              have hw' : e'.2 = w := congrArg Subtype.val hsub
              exact Prod.ext hR'.2 hw'
          have hw_mem : (v, w) ∈ S.rightEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hw_mem]
          have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w), hw_mem⟩
          dsimp only [p, dR]; omega
        have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩⟩
        have h2 := S.dartMap_at_source_right H hgt_wv hvw
        have hglue1 : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨p, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; left; dsimp; omega
        have hglue2 : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨p, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; right; dsimp; omega
        rw [h2]
        exact h1.trans (hglue1.symm.reachable.trans hglue2.reachable)
  · -- Non-wrap case: heading(w) < heading(u) with NO neighbor strictly between them!
    rcases lt_or_gt_of_ne (H.ne_of_adj huv) with hlt_uv | hgt_uv
    · -- u < v (left neighbor)
      have h1 := S.dartMap_to_target_left H hHG hlt_uv huv
      rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with hlt_wv | hgt_wv
      · -- Case 2: both u < v and w < v, consecutive in L_v => rank(w,v) = rank(u,v) + 1!
        have hr_eq : S.edgeRank H v.castSucc (w, v) = S.edgeRank H v.castSucc (u, v) + 1 := by
          rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm, S.edgeRank_leftEdge H hHG hlt_uv huv]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) =
              insert (u, v) ((S.leftEdges H v).filter (fun e' =>
                heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨he', hlt'⟩
              have hL' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hL'.1
              have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
              have hge := hgap ⟨e'.1, hadj'⟩ hlt'
              rcases eq_or_lt_of_le hge with heq | hgt
              · left
                have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v heq
                have hu' : u = e'.1 := congrArg Subtype.val hsub
                exact Prod.ext hu'.symm hL'.2
              · right; exact ⟨he', hgt⟩
            · rintro (rfl | ⟨he', hgt⟩)
              · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩, hlt⟩
              · exact ⟨he', hlt.trans hgt⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [lt_irrefl])]
          dsimp only [p]; omega
        have h2 := S.dartMap_at_source_left H hlt_wv hvw
        rw [h2]
        have heq_vert : (⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by
              have hm : (u, v) ∈ S.activeEdges H v.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, by simpa, by simp⟩
              exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) =
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by
              have hm : (w, v) ∈ S.activeEdges H v.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_wv, hvw.symm⟩, by simpa, by simp⟩
              exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ := by
          refine Sigma.ext rfl (heq_of_eq (Fin.ext hr_eq.symm))
        rw [← heq_vert]; exact h1
      · -- Case 3: u < v is FIRST of L_v (topmost left, rank = p + dL - 1) and v < w is LAST of R_v (topmost right, rank = p + dR - 1)!
        have hru : S.edgeRank H v.castSucc (u, v) = p + dL - 1 := by
          rw [S.edgeRank_leftEdge H hHG hlt_uv huv]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (u, v) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hL' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hL'.1
              have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
              have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
              have hge := hgap ⟨e'.1, hadj'⟩ (S.heading_right_lt_left hgt_wv he'v)
              refine ⟨he', lt_of_le_of_ne hge (fun h => hne' ?_)⟩
              have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v h
              exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
          have hu_mem : (u, v) ∈ S.leftEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hu_mem]
          have : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v), hu_mem⟩; dsimp only [p, dL]; omega
        have hrw : S.edgeRank H v.succ (v, w) = p + dR - 1 := by
          rw [S.edgeRank_rightEdge H hHG hgt_wv hvw]
          have hfilt : (S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) = (S.rightEdges H v).erase (v, w) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hR' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hR'.1
              have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
              have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
              have hle : heading (S.p e'.2 - S.p v) ≤ heading (S.p w - S.p v) := by
                by_contra! hgt'
                have hge := hgap ⟨e'.2, hadj'⟩ hgt'
                have := S.heading_right_lt_left hve' hlt_uv
                linarith
              refine ⟨he', lt_of_le_of_ne hle (fun h => hne' ?_)⟩
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v h
              exact Prod.ext hR'.2 (congrArg Subtype.val hsub)
          have hw_mem : (v, w) ∈ S.rightEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hw_mem]
          have : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w), hw_mem⟩; dsimp only [p, dR]; omega
        have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩⟩
        have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩⟩
        have h2 := S.dartMap_at_source_right H hgt_wv hvw
        have hglue : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; right; dsimp; omega
        rw [h2]
        exact h1.trans hglue.reachable
    · -- Case 1 (leftTip!): v < u and heading(w) < heading(u) => v < w too, rank(v, u) = rank(v, w) + 1!
      have hgt_wv : v < w := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
        · exfalso; have := S.heading_right_lt_left hgt_uv h; linarith
        · exact h
      have hr_eq : S.edgeRank H v.succ (v, u) = S.edgeRank H v.succ (v, w) + 1 := by
        rw [S.edgeRank_rightEdge H hHG hgt_uv huv.symm, S.edgeRank_rightEdge H hHG hgt_wv hvw]
        have hfilt : (S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p u - S.p v)) =
            insert (v, w) ((S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨he', hlt'⟩
            have hR' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hR'.1
            have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
            have hle : heading (S.p e'.2 - S.p v) ≤ heading (S.p w - S.p v) := by
              by_contra! hgt'
              have := hgap ⟨e'.2, hadj'⟩ hgt'
              linarith
            rcases eq_or_lt_of_le hle with heq | hlt2
            · left
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v heq
              exact Prod.ext hR'.2 (congrArg Subtype.val hsub)
            · right; exact ⟨he', hlt2⟩
          · rintro (rfl | ⟨he', hlt2⟩)
            · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩, hlt⟩
            · exact ⟨he', hlt2.trans hlt⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp [lt_irrefl])]
        dsimp only [p]; omega
      have h1 := S.dartMap_to_target_right H hHG hgt_uv huv
      have h2 := S.dartMap_at_source_right H hgt_wv hvw
      rw [h2]
      have heq_vert : (⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by
            have hm : (v, u) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_uv, huv.symm⟩, by simp, by simp; omega⟩
            exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) =
          ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by
            have hm : (v, w) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, by simp, by simp; omega⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩ := by
        refine Sigma.ext rfl (heq_of_eq (Fin.ext hr_eq))
      rw [← heq_vert]; exact h1

/-- Induced map from `φ_H`-orbits to connected components of `T(H)`. -/
private noncomputable def orbitToComp (hHG : H ≤ S.G) :
    Quotient (orbitSetoid (S.geoPhi H hHG)) → (S.slabGraph H).ConnectedComponent :=
  Quotient.lift (fun d => (S.slabGraph H).connectedComponentMk (S.dartMap H d)) (by
    intro d₁ d₂ h
    obtain ⟨k, rfl⟩ := h
    induction k generalizing d₁ with
    | zero => rfl
    | succ k ihk =>
      have h1 : (S.slabGraph H).connectedComponentMk (S.dartMap H d₁) =
          (S.slabGraph H).connectedComponentMk (S.dartMap H (S.geoPhi H hHG d₁)) :=
        SimpleGraph.ConnectedComponent.sound (S.dartMap_phi_reachable H hHG d₁)
      rw [h1, show (S.geoPhi H hHG ^ (k + 1)) d₁ = (S.geoPhi H hHG ^ k) (S.geoPhi H hHG d₁) by
        rw [pow_add, pow_one, Equiv.Perm.mul_apply]]
      exact ihk _)

/-- `orbitToComp` is SURJECTIVE: every connected component of `T(H)` is hit by some dart! -/
private lemma orbitToComp_surjective (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    Function.Surjective (S.orbitToComp H hHG) := by
  classical
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
  rcases x with ⟨i, r⟩
  rcases Nat.eq_zero_or_pos r.val with hr0 | hrpos
  · -- r = 0: walk along bottom path to (1, 0), which is below the 0-th edge of activeEdges H 1!
    have hbot : ∀ k : ℕ, (hk : k ≤ n) →
        (S.slabGraph H).Reachable (S.outerVert H) ⟨⟨k, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ := by
      intro k; induction k with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ k ihk =>
        intro hk
        let vk : Fin n := ⟨k, by omega⟩
        exact (ihk (by omega)).trans
          (S.slabGraph_adj_step H vk ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ (Or.inl ⟨Nat.zero_le _, rfl⟩)).reachable
    let v0 : Fin n := ⟨0, by have := S.hn; omega⟩
    have hL0 : (S.leftEdges H v0).card = 0 := by
      unfold leftEdges
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he h2; simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hlt0 : e.1 < v0 := h2 ▸ he.1
      have : e.1.val < 0 := hlt0; omega
    have hR0 : 1 ≤ (S.rightEdges H v0).card := by have := hdeg v0; omega
    have hA1 : (S.activeEdges H v0.succ).Nonempty := by
      have := S.activeEdges_card_step H v0
      have hA0 : (S.activeEdges H v0.castSucc).card = 0 := by
        have : v0.castSucc = 0 := Fin.ext rfl; rw [this, S.activeEdges_zero, Finset.card_empty]
      exact Finset.card_pos.mp (by omega)
    -- Pick edge e_min ∈ activeEdges H v0.succ minimizing edgeY at slabMid v0.succ (rank = 0!)
    obtain ⟨emin, hemin_mem, hemin_min⟩ :=
      Finset.exists_min_image (S.activeEdges H v0.succ) (fun e => edgeY S.p e.1 e.2 (S.slabMid v0.succ)) hA1
    have hrank0 : S.edgeRank H v0.succ emin = 0 := by
      rw [edgeRank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e' he' hlt
      exact not_lt.mpr (hemin_min e' he') hlt
    have hemin_or := Finset.mem_filter.mp (Finset.mem_filter.mp hemin_mem).1
    have hlt_e : emin.1 < emin.2 := hemin_or.2.1
    have hadj_e : H.Adj emin.2 emin.1 := hemin_or.2.2.symm
    have he1_0 : emin.1 = v0 := by
      have h1 := (Finset.mem_filter.mp hemin_mem).2.1
      apply Fin.ext; simp [v0] at h1 ⊢; omega
    let d : DartOf H := ⟨(emin.2, emin.1), hadj_e⟩
    refine ⟨Quotient.mk _ d, ?_⟩
    apply SimpleGraph.ConnectedComponent.sound
    have h1 := S.dartMap_to_target_right H hHG hlt_e hadj_e
    dsimp only at h1
    have h1' : (S.slabGraph H).Reachable (S.dartMap H d) ⟨v0.succ, ⟨0, Nat.succ_pos _⟩⟩ := by
      have heq_dst : (⟨emin.1.succ, ⟨S.edgeRank H emin.1.succ (emin.1, emin.2), Nat.lt_succ_of_lt (S.edgeRank_lt H (by
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_e, hadj_e.symm⟩, by simp, by simp; omega⟩))⟩⟩ : S.SlabVert H) =
          ⟨v0.succ, ⟨0, Nat.succ_pos _⟩⟩ :=
        S.slabVert_ext H (congrArg Fin.succ he1_0) (by dsimp; rw [Prod.mk.eta, he1_0]; exact hrank0)
      rw [heq_dst] at h1; exact h1
    have h2 := hbot 1 (by have := S.hn; omega)
    have h3 := hbot i.val (by omega)
    have hr_eq : (⟨i, r⟩ : S.SlabVert H) = ⟨⟨i.val, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ :=
      Sigma.ext rfl (heq_of_eq (Fin.ext hr0))
    rw [hr_eq]
    exact h1'.trans (h2.symm.trans h3)
  · -- r > 0: find the unique edge e ∈ activeEdges H i of rank r - 1!
    have hcard_i : r.val - 1 < (S.activeEdges H i).card := by omega
    have hinj : Set.InjOn (fun e : Fin n × Fin n => edgeY S.p e.1 e.2 (S.slabMid i)) ↑(S.activeEdges H i) := by
      intro e₁ h1 e₂ h2 heq
      by_contra hne
      have hm1 := S.slabMid_between H h1
      have hm2 := S.slabMid_between H h2
      have ho1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have ho2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      exact S.edgeY_ne_of_ne_edges ho1.1 ho2.1 (hHG ho1.2) (hHG ho2.2) hne hm1.1 hm1.2 hm2.1 hm2.2 heq
    let ys := (S.activeEdges H i).image (fun e => edgeY S.p e.1 e.2 (S.slabMid i))
    have hys_card : ys.card = (S.activeEdges H i).card := Finset.card_image_of_injOn hinj
    let emb := ys.orderEmbOfFin hys_card
    have hy_mem : emb ⟨r.val - 1, hcard_i⟩ ∈ ys := ys.orderEmbOfFin_mem hys_card ⟨r.val - 1, hcard_i⟩
    obtain ⟨e, he_mem, he_y⟩ := Finset.mem_image.mp hy_mem
    have hrank : S.edgeRank H i e = r.val - 1 := by
      unfold edgeRank
      have hmem_emb : ∀ e' ∈ S.activeEdges H i, ∃ j, emb j = edgeY S.p e'.1 e'.2 (S.slabMid i) :=
        fun e' he' => Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ he')
      have hcard_lt : ((S.activeEdges H i).filter (fun e' =>
          edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i))).card =
          (Finset.univ.filter (fun j : Fin (S.activeEdges H i).card => j.val < r.val - 1)).card := by
        refine Finset.card_bij
          (fun e' he' => Classical.choose (hmem_emb e' (Finset.mem_filter.mp he').1))
          ?_ ?_ ?_
        · intro e' he'
          have hspec := Classical.choose_spec (hmem_emb e' (Finset.mem_filter.mp he').1)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hlt : emb (Classical.choose (hmem_emb e' (Finset.mem_filter.mp he').1)) < emb ⟨r.val - 1, hcard_i⟩ := by
            rw [hspec, ← he_y]; exact (Finset.mem_filter.mp he').2
          exact emb.lt_iff_lt.mp hlt
        · intro e₁ h1 e₂ h2 heq
          have hs1 := Classical.choose_spec (hmem_emb e₁ (Finset.mem_filter.mp h1).1)
          have hs2 := Classical.choose_spec (hmem_emb e₂ (Finset.mem_filter.mp h2).1)
          exact hinj (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
            (hs1.symm.trans ((congrArg emb heq).trans hs2))
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          obtain ⟨e', he'_mem, he'_y⟩ := Finset.mem_image.mp (ys.orderEmbOfFin_mem hys_card j)
          refine ⟨e', Finset.mem_filter.mpr ⟨he'_mem, ?_⟩, ?_⟩
          · rw [he'_y, he_y]; exact emb.strictMono hj
          · apply emb.injective
            rw [Classical.choose_spec (hmem_emb e' he'_mem), he'_y]
      rw [hcard_lt]
      have : (Finset.univ.filter (fun j : Fin (S.activeEdges H i).card => j.val < r.val - 1)).card =
          (Finset.range (r.val - 1)).card := by
        refine Finset.card_bij (fun j _ => j.val)
          (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
          (fun j₁ _ j₂ _ h => Fin.ext h)
          (fun k hk => ⟨⟨k, by rw [Finset.mem_range] at hk; omega⟩, by simp [Finset.mem_range.mp hk], rfl⟩)
      rw [this, Finset.card_range]
    have he_or := (Finset.mem_filter.mp (Finset.mem_filter.mp he_mem).1).2
    have he_sl := (Finset.mem_filter.mp he_mem).2
    let d : DartOf H := ⟨(e.1, e.2), he_or.2⟩
    refine ⟨Quotient.mk _ d, ?_⟩
    apply SimpleGraph.ConnectedComponent.sound
    have htop := S.edge_top_connected H hHG he_or.1 he_or.2 e.1.succ i (by simp) (by simp; omega) he_sl.1 he_sl.2
    dsimp only at htop
    rw [S.dartMap_at_source_right H he_or.1 he_or.2]
    have heq_i : (⟨i, ⟨S.edgeRank H i (e.1, e.2) + 1, Nat.succ_lt_succ (S.edgeRank_lt H (by
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_or.1, he_or.2⟩, he_sl.1, he_sl.2⟩))⟩⟩ : S.SlabVert H) =
        ⟨i, r⟩ :=
      S.slabVert_ext H rfl (by dsimp; rw [Prod.mk.eta, hrank]; omega)
    rw [heq_i] at htop; exact htop

private lemma slab_components_le_orbits (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    Nat.card (S.slabGraph H).ConnectedComponent ≤ numOrbits (S.geoPhi H hHG) := by
  classical
  unfold numOrbits
  haveI : Fintype (S.slabGraph H).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitSetoid (S.geoPhi H hHG))) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective (S.orbitToComp H hHG) (S.orbitToComp_surjective H hHG hdeg)

/-- Exact component turning-number identity: for any connected component `C` of `T(H)`
    (as a `Finset (SlabVert H)`), the darts mapping into `C` satisfy:
    `#leftTips(C) - #rightCaps(C) = |C| - ∑_{t ∈ C} |slabInEdges t| - 1_{outerVert ∈ C}`! -/
private lemma component_turning_identity (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card)
    (c : (S.slabGraph H).ConnectedComponent) :
    let F : Finset (S.SlabVert H) :=
      Finset.univ.filter (fun t => (S.slabGraph H).connectedComponentMk t = c)
    let D_F : Finset (DartOf H) :=
      Finset.univ.filter (fun d => (S.slabGraph H).connectedComponentMk (S.dartMap H d) = c)
    ((D_F.filter (S.isLeftTip H)).card : ℤ) - ((D_F.filter (S.isRightCap H)).card : ℤ) =
      (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) -
        (if S.outerVert H ∈ F then (1 : ℤ) else 0) := by
  classical
  intro F D_F
  -- Partition F into:
  -- 1. outerVert (contributes 1 to 1 - inDeg)
  -- 2. tipVerts = {(v.succ, r) ∈ F | p_v < r < p_v + dR_v} (contributes +1 each, bijects with D_F.filter isLeftTip!)
  -- 3. capVerts = {(v.succ, p_v) ∈ F | dR_v = 0} (contributes -1 each, bijects with D_F.filter isRightCap!)
  -- 4. all other vertices (contribute 0!)
  let isTipV (t : S.SlabVert H) : Prop :=
    ∃ (v : Fin n) (ht : t.1 = v.succ),
      (S.passBelow H v).card < t.2.val ∧ t.2.val < (S.passBelow H v).card + (S.rightEdges H v).card
  let isCapV (t : S.SlabVert H) : Prop :=
    ∃ (v : Fin n) (ht : t.1 = v.succ),
      t.2.val = (S.passBelow H v).card ∧ (S.rightEdges H v).card = 0
  have hterm : ∀ t : S.SlabVert H,
      (1 : ℤ) - ((S.slabInEdges H t).card : ℤ) =
        (if t = S.outerVert H then (1 : ℤ) else 0) +
        (if isTipV t then (1 : ℤ) else 0) -
        (if isCapV t then (1 : ℤ) else 0) := by
    rintro ⟨i, r⟩
    cases i using Fin.cases with
    | zero =>
      have hr0 : r = ⟨0, Nat.succ_pos _⟩ := by
        apply Fin.ext
        have hrlt : r.val < (S.activeEdges H 0).card + 1 := r.isLt
        have h0 : (S.activeEdges H 0).card = 0 := by rw [S.activeEdges_zero, Finset.card_empty]
        omega
      have h1 : (⟨0, r⟩ : S.SlabVert H) = S.outerVert H := Sigma.ext rfl (heq_of_eq hr0)
      have h2 : ¬ isTipV ⟨0, r⟩ := by rintro ⟨v, ht, _⟩; exact Fin.succ_ne_zero v ht.symm
      have h3 : ¬ isCapV ⟨0, r⟩ := by rintro ⟨v, ht, _⟩; exact Fin.succ_ne_zero v ht.symm
      rw [S.slabInEdges_zero, if_pos h1, if_neg h2, if_neg h3]; norm_num
    | succ v =>
      have hnot0 : (⟨v.succ, r⟩ : S.SlabVert H) ≠ S.outerVert H := fun h =>
        Fin.succ_ne_zero v (congrArg Sigma.fst h)
      have htip_iff : isTipV ⟨v.succ, r⟩ ↔
          (S.passBelow H v).card < r.val ∧ r.val < (S.passBelow H v).card + (S.rightEdges H v).card := by
        constructor
        · rintro ⟨w, ht, h1, h2⟩; have := Fin.succ_injective _ ht; subst this; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨v, rfl, h1, h2⟩
      have hcap_iff : isCapV ⟨v.succ, r⟩ ↔
          r.val = (S.passBelow H v).card ∧ (S.rightEdges H v).card = 0 := by
        constructor
        · rintro ⟨w, ht, h1, h2⟩; have := Fin.succ_injective _ ht; subst this; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨v, rfl, h1, h2⟩
      rw [if_neg hnot0, S.slabInEdges_succ_card H hHG hdeg v r]
      simp only [htip_iff, hcap_iff]
      split_ifs with h1 h2 <;> omega
  have hsum : (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) =
      (if S.outerVert H ∈ F then (1 : ℤ) else 0) +
      ((F.filter isTipV).card : ℤ) - ((F.filter isCapV).card : ℤ) := by
    have h1 : (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) =
        ∑ t ∈ F, ((1 : ℤ) - ((S.slabInEdges H t).card : ℤ)) := by
      push_cast; rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have htip : ∑ x ∈ F, (if isTipV x then (1 : ℤ) else 0) = ((F.filter isTipV).card : ℤ) := by
      rw [Finset.sum_boole]
    have hcap : ∑ x ∈ F, (if isCapV x then (1 : ℤ) else 0) = ((F.filter isCapV).card : ℤ) := by
      rw [Finset.sum_boole]
    rw [h1]
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', htip, hcap]
  -- Bijection 1: D_F.filter isLeftTip ≃ F.filter isTipV via d = (u, v) ↦ (v.succ, rank(v.succ, (v, u)))
  have hbij_tip : (D_F.filter (S.isLeftTip H)).card = (F.filter isTipV).card := by
    refine Finset.card_bij
      (fun d hd =>
        have hlt : d.1.2 < d.1.1 := (Finset.mem_filter.mp hd).2.1
        have hmem : (d.1.2, d.1.1) ∈ S.activeEdges H d.1.2.succ :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, d.2.symm⟩, by simp, by simp; omega⟩
        ⟨d.1.2.succ, ⟨S.edgeRank H d.1.2.succ (d.1.2, d.1.1), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩)
      ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, D_F, F, Finset.mem_univ, true_and] at hd ⊢
      rcases hd with ⟨hcomp, hvu, hnotmin⟩
      have hreach := S.dartMap_to_target_right H hHG hvu d.2
      refine ⟨(SimpleGraph.ConnectedComponent.sound hreach).symm.trans hcomp, d.1.2, rfl, ?_, ?_⟩
      · dsimp only
        rw [S.edgeRank_rightEdge H hHG hvu d.2.symm]
        have hex : ∃ w, H.Adj d.1.2 w ∧ heading (S.p w - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2) := by
          unfold isMinNeighbor at hnotmin; push Not at hnotmin; exact hnotmin
        obtain ⟨w, hvw, hlt_w⟩ := hex
        have hvw_lt : d.1.2 < w := by
          rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
          · exfalso; have := S.heading_right_lt_left hvu h; linarith
          · exact h
        have hpos : 0 < ((S.rightEdges H d.1.2).filter (fun e' =>
            heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2))).card :=
          Finset.card_pos.mpr ⟨(d.1.2, w), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw_lt, hvw⟩, rfl⟩, hlt_w⟩⟩
        omega
      · dsimp only
        rw [S.edgeRank_rightEdge H hHG hvu d.2.symm]
        have hlt_card : ((S.rightEdges H d.1.2).filter (fun e' =>
            heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2))).card <
            (S.rightEdges H d.1.2).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
          have : (d.1.2, d.1.1) ∈ (S.rightEdges H d.1.2).filter (fun e' =>
              heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2)) := by
            rw [h]; exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, d.2.symm⟩, rfl⟩
          exact lt_irrefl _ (Finset.mem_filter.mp this).2
        omega
    · intro d₁ h1 d₂ h2 heq
      have hv : d₁.1.2 = d₂.1.2 := Fin.succ_injective _ (congrArg Sigma.fst heq)
      have hvu1 : d₁.1.2 < d₁.1.1 := (Finset.mem_filter.mp h1).2.1
      have hvu2 : d₂.1.2 < d₂.1.1 := (Finset.mem_filter.mp h2).2.1
      have hr : S.edgeRank H d₁.1.2.succ (d₁.1.2, d₁.1.1) = S.edgeRank H d₂.1.2.succ (d₂.1.2, d₂.1.1) := by
        simpa using congrArg (fun x : S.SlabVert H => x.2.val) heq
      rcases d₁ with ⟨⟨u₁, v₁⟩, hadj1⟩
      rcases d₂ with ⟨⟨u₂, v₂⟩, hadj2⟩
      dsimp at hv hr hvu1 hvu2; subst hv
      rw [S.edgeRank_rightEdge H hHG hvu1 hadj1.symm, S.edgeRank_rightEdge H hHG hvu2 hadj2.symm] at hr
      have hcard_eq : ((S.rightEdges H v₁).filter (fun e' =>
          heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁))).card =
          ((S.rightEdges H v₁).filter (fun e' =>
          heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁))).card := by omega
      have hhead : heading (S.p u₁ - S.p v₁) = heading (S.p u₂ - S.p v₁) := by
        rcases lt_trichotomy (heading (S.p u₁ - S.p v₁)) (heading (S.p u₂ - S.p v₁)) with hlt | heq' | hgt
        · exfalso
          have hss : (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) ⊂
              (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.trans hlt⟩, fun h => ?_⟩
            have hm : (v₁, u₁) ∈ (S.rightEdges H v₁).filter (fun e' =>
                heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu1, hadj1.symm⟩, rfl⟩, hlt⟩
            rw [← h] at hm; exact lt_irrefl _ (Finset.mem_filter.mp hm).2
          have := Finset.card_lt_card hss; omega
        · exact heq'
        · exfalso
          have hss : (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) ⊂
              (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.trans hgt⟩, fun h => ?_⟩
            have hm : (v₁, u₂) ∈ (S.rightEdges H v₁).filter (fun e' =>
                heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu2, hadj2.symm⟩, rfl⟩, hgt⟩
            rw [← h] at hm; exact lt_irrefl _ (Finset.mem_filter.mp hm).2
          have := Finset.card_lt_card hss; omega
      have hsub : (⟨u₁, hadj1.symm⟩ : {x : Fin n // H.Adj v₁ x}) = ⟨u₂, hadj2.symm⟩ :=
        S.heading_inj_H H hHG v₁ hhead
      have hu : u₁ = u₂ := congrArg Subtype.val hsub
      exact Subtype.ext (Prod.ext hu rfl)
    · intro t ht
      simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨hcomp, v, hv, hr1, hr2⟩
      rcases t with ⟨i, r⟩; dsimp at hv hr1 hr2; subst hv
      let k := r.val - (S.passBelow H v).card
      have hk1 : 1 ≤ k := by omega
      have hk2 : k < (S.rightEdges H v).card := by omega
      let hs := (S.rightEdges H v).image (fun e => heading (S.p e.2 - S.p v))
      have hinjR : Set.InjOn (fun e : Fin n × Fin n => heading (S.p e.2 - S.p v)) ↑(S.rightEdges H v) := by
        intro e₁ h1 e₂ h2 heq
        have hR1 := Finset.mem_filter.mp h1; have hR2 := Finset.mem_filter.mp h2
        have ho1 := Finset.mem_filter.mp hR1.1; have ho2 := Finset.mem_filter.mp hR2.1
        have hsub : (⟨e₁.2, hR1.2 ▸ ho1.2.2⟩ : {x : Fin n // H.Adj v x}) = ⟨e₂.2, hR2.2 ▸ ho2.2.2⟩ :=
          S.heading_inj_H H hHG v heq
        exact Prod.ext (hR1.2.trans hR2.2.symm) (congrArg Subtype.val hsub)
      have hcardR : hs.card = (S.rightEdges H v).card := Finset.card_image_of_injOn hinjR
      let embR := hs.orderEmbOfFin hcardR
      obtain ⟨e, he_mem, he_h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨k, hk2⟩)
      obtain ⟨e0, he0_mem, he0_h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨0, by omega⟩)
      have hRe := Finset.mem_filter.mp he_mem
      have hoe := Finset.mem_filter.mp hRe.1
      have hve : v < e.2 := hRe.2 ▸ hoe.2.1
      have hadj_e : H.Adj e.2 v := (hRe.2 ▸ hoe.2.2).symm
      have hRe0 := Finset.mem_filter.mp he0_mem
      have hoe0 := Finset.mem_filter.mp hRe0.1
      have hadj_e0 : H.Adj v e0.2 := hRe0.2 ▸ hoe0.2.2
      have hlt0 : heading (S.p e0.2 - S.p v) < heading (S.p e.2 - S.p v) := by
        rw [he0_h, he_h]; exact embR.strictMono (show (⟨0, by omega⟩ : Fin _) < ⟨k, hk2⟩ from by change 0 < k; omega)
      have hmem_embR : ∀ e' ∈ S.rightEdges H v, ∃ j, embR j = heading (S.p e'.2 - S.p v) :=
        fun e' he' => Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ he')
      have hrank_e : S.edgeRank H v.succ (v, e.2) = r.val := by
        rw [S.edgeRank_rightEdge H hHG hve hadj_e.symm]
        have hcnt : ((S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p e.2 - S.p v))).card = k := by
          have h1 : ((S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p e.2 - S.p v))).card =
              (Finset.range k).card := by
            refine Finset.card_bij
              (fun e' he' => (Classical.choose (hmem_embR e' (Finset.mem_filter.mp he').1)).val)
              ?_ ?_ ?_
            · intro e' he'
              have hsp := Classical.choose_spec (hmem_embR e' (Finset.mem_filter.mp he').1)
              rw [Finset.mem_range]
              have hlt : embR (Classical.choose (hmem_embR e' (Finset.mem_filter.mp he').1)) < embR ⟨k, hk2⟩ := by
                rw [hsp, ← he_h]; exact (Finset.mem_filter.mp he').2
              exact embR.lt_iff_lt.mp hlt
            · intro e₁ h1 e₂ h2 hval
              have hsp1 := Classical.choose_spec (hmem_embR e₁ (Finset.mem_filter.mp h1).1)
              have hsp2 := Classical.choose_spec (hmem_embR e₂ (Finset.mem_filter.mp h2).1)
              exact hinjR (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
                (hsp1.symm.trans ((congrArg embR (Fin.ext hval)).trans hsp2))
            · intro j hj
              rw [Finset.mem_range] at hj
              obtain ⟨e', he'm, he'h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨j, by omega⟩)
              refine ⟨e', Finset.mem_filter.mpr ⟨he'm, by rw [he'h, he_h]; exact embR.strictMono (by change j < k; exact hj)⟩, ?_⟩
              have hsp := Classical.choose_spec (hmem_embR e' he'm)
              exact congrArg Fin.val (embR.injective (hsp.trans he'h))
          rw [h1, Finset.card_range]
        omega
      let d : DartOf H := ⟨(e.2, v), hadj_e⟩
      have hreach := S.dartMap_to_target_right H hHG hve hadj_e
      have heq_t : (⟨v.succ, ⟨S.edgeRank H v.succ (v, e.2), by
            have hm : (v, e.2) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hve, hadj_e.symm⟩, by simp, by simp; omega⟩
            exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) = ⟨v.succ, r⟩ :=
        Sigma.ext rfl (heq_of_eq (Fin.ext hrank_e))
      refine ⟨d, ?_, heq_t⟩
      simp only [Finset.mem_filter, D_F, Finset.mem_univ, true_and]
      refine ⟨(SimpleGraph.ConnectedComponent.sound hreach).trans (by rw [heq_t]; exact hcomp),
        hve, fun hmin => not_lt.mpr (hmin e0.2 hadj_e0) hlt0⟩
  -- Bijection 2: D_F.filter isRightCap ≃ F.filter isCapV via d = (u, v) ↦ (v.succ, p_v)
  have hbij_cap : (D_F.filter (S.isRightCap H)).card = (F.filter isCapV).card := by
    refine Finset.card_bij
      (fun d hd =>
        have hpR := S.passBelow_add_right_le H hHG d.1.2
        ⟨d.1.2.succ, ⟨(S.passBelow H d.1.2).card, by omega⟩⟩)
      ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, D_F, F, Finset.mem_univ, true_and] at hd ⊢
      rcases hd with ⟨hcomp, huv, hmin⟩
      have hdR0 : (S.rightEdges H d.1.2).card = 0 := by
        unfold rightEdges
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h1; simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have h1' := hmin e.2 (h1 ▸ he.2)
        have h2' := S.heading_right_lt_left (h1 ▸ he.1) huv; linarith
      have hu_mem : (d.1.1, d.1.2) ∈ S.leftEdges H d.1.2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, d.2⟩, rfl⟩
      have hdL1 : 1 ≤ (S.leftEdges H d.1.2).card := Finset.card_pos.mpr ⟨(d.1.1, d.1.2), hu_mem⟩
      have hru : S.edgeRank H d.1.2.castSucc (d.1.1, d.1.2) =
          (S.passBelow H d.1.2).card + (S.leftEdges H d.1.2).card - 1 := by
        rw [S.edgeRank_leftEdge H hHG huv d.2]
        have hfilt : (S.leftEdges H d.1.2).filter (fun e' =>
            heading (S.p d.1.1 - S.p d.1.2) < heading (S.p e'.1 - S.p d.1.2)) =
            (S.leftEdges H d.1.2).erase (d.1.1, d.1.2) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'; have ho' := Finset.mem_filter.mp hL'.1
            refine ⟨he', lt_of_le_of_ne (hmin e'.1 (hL'.2 ▸ ho'.2.2.symm)) (fun h => hne' ?_)⟩
            have hsub : (⟨d.1.1, d.2.symm⟩ : {x : Fin n // H.Adj d.1.2 x}) = ⟨e'.1, hL'.2 ▸ ho'.2.2.symm⟩ :=
              S.heading_inj_H H hHG d.1.2 h
            exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
        rw [hfilt, Finset.card_erase_of_mem hu_mem]
        omega
      have hreach := S.dartMap_to_target_left H hHG huv d.2
      have hglue : (S.slabGraph H).Adj
          ⟨d.1.2.castSucc, ⟨S.edgeRank H d.1.2.castSucc (d.1.1, d.1.2) + 1, by
            have hm : (d.1.1, d.1.2) ∈ S.activeEdges H d.1.2.castSucc :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, d.2⟩, by simpa, by simp⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
          ⟨d.1.2.succ, ⟨(S.passBelow H d.1.2).card, by have := S.passBelow_add_right_le H hHG d.1.2; omega⟩⟩ := by
        apply S.slabGraph_adj_step H d.1.2; right; dsimp; omega
      exact ⟨(SimpleGraph.ConnectedComponent.sound (hreach.trans hglue.reachable)).symm.trans hcomp,
        d.1.2, rfl, rfl, hdR0⟩
    · intro d₁ h1 d₂ h2 heq
      have hv : d₁.1.2 = d₂.1.2 := Fin.succ_injective _ (congrArg Sigma.fst heq)
      rcases d₁ with ⟨⟨u₁, v₁⟩, hadj1⟩; rcases d₂ with ⟨⟨u₂, v₂⟩, hadj2⟩
      dsimp at hv; subst hv
      have hm1 := (Finset.mem_filter.mp h1).2.2
      have hm2 := (Finset.mem_filter.mp h2).2.2
      have hhead : heading (S.p u₁ - S.p v₁) = heading (S.p u₂ - S.p v₁) :=
        le_antisymm (hm1 u₂ hadj2.symm) (hm2 u₁ hadj1.symm)
      have hsub : (⟨u₁, hadj1.symm⟩ : {x : Fin n // H.Adj v₁ x}) = ⟨u₂, hadj2.symm⟩ :=
        S.heading_inj_H H hHG v₁ hhead
      have hu : u₁ = u₂ := congrArg Subtype.val hsub
      exact Subtype.ext (Prod.ext hu rfl)
    · intro t ht
      simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨hcomp, v, hv, hrp, hdR0⟩
      rcases t with ⟨i, r⟩; dsimp at hv hrp hdR0; subst hv
      have hdL1 : 1 ≤ (S.leftEdges H v).card := by have := hdeg v; omega
      have hneL : (S.leftEdges H v).Nonempty := Finset.card_pos.mp hdL1
      obtain ⟨e, he_mem, he_min⟩ :=
        Finset.exists_min_image (S.leftEdges H v) (fun e => heading (S.p e.1 - S.p v)) hneL
      have hLe := Finset.mem_filter.mp he_mem
      have hoe := Finset.mem_filter.mp hLe.1
      have huv : e.1 < v := hLe.2 ▸ hoe.2.1
      have hadj : H.Adj e.1 v := hLe.2 ▸ hoe.2.2
      have hmin : S.isMinNeighbor H ⟨(e.1, v), hadj⟩ := by
        intro w hw
        have hwv : w < v := by
          rcases lt_or_gt_of_ne (H.ne_of_adj hw).symm with h | h
          · exact h
          · exfalso
            have : (v, w) ∈ S.rightEdges H v :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hw⟩, rfl⟩
            have := Finset.card_pos.mpr ⟨(v, w), this⟩; omega
        exact he_min (w, v) (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv, hw.symm⟩, rfl⟩)
      have hev_mem : (e.1, v) ∈ S.leftEdges H v :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, rfl⟩
      have hru : S.edgeRank H v.castSucc (e.1, v) =
          (S.passBelow H v).card + (S.leftEdges H v).card - 1 := by
        rw [S.edgeRank_leftEdge H hHG huv hadj]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p e.1 - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (e.1, v) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'; have ho' := Finset.mem_filter.mp hL'.1
            refine ⟨he', lt_of_le_of_ne (hmin e'.1 (hL'.2 ▸ ho'.2.2.symm)) (fun h => hne' ?_)⟩
            have hsub : (⟨e.1, hadj.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hL'.2 ▸ ho'.2.2.symm⟩ :=
              S.heading_inj_H H hHG v h
            exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
        rw [hfilt, Finset.card_erase_of_mem hev_mem]
        omega
      have hreach := S.dartMap_to_target_left H hHG huv hadj
      have hglue : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (e.1, v) + 1, by
            have hm : (e.1, v) ∈ S.activeEdges H v.castSucc :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, by simpa, by simp⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
          ⟨v.succ, r⟩ := by
        apply S.slabGraph_adj_step H v; right; dsimp; omega
      refine ⟨⟨(e.1, v), hadj⟩, ?_, Sigma.ext rfl (heq_of_eq (Fin.ext hrp.symm))⟩
      simp only [Finset.mem_filter, D_F, Finset.mem_univ, true_and]
      exact ⟨(SimpleGraph.ConnectedComponent.sound (hreach.trans hglue.reachable)).trans hcomp, huv, hmin⟩
  rw [hbij_tip, hbij_cap]
  linarith

end Subgraph

/- ### Edge Insertion in `T(H)` and the Spanning-Tree-to-`G` Squeeze! -/

open Classical in
/-- Adding a single edge `(a, b)` of `S.G` (`a < b`, `¬ H.Adj a b`) to a connected spanning
    subgraph `H ≤ S.G` where `orbitToComp H` is bijective:
    the two insertion darts `d_a, d_b ∈ DartOf H` lie in the SAME component of `T(H)`
    (via the chain of trapezoids traversed by the open segment `(a, b)`!), hence in the SAME
    `φ_H`-orbit, so `numOrbits φ_{H'} = numOrbits φ_H + 1`! -/
private lemma add_edge_adds_one_orbit (H : SimpleGraph (Fin n)) (hHG : H ≤ S.G)
    (hHconn : H.Connected)
    (hbij : Function.Bijective (S.orbitToComp H hHG))
    {a b : Fin n} (hab : a < b) (hadjG : S.G.Adj a b) (hnadjH : ¬ H.Adj a b) :
    let H' : SimpleGraph (Fin n) := H ⊔ SimpleGraph.fromEdgeSet {s(a, b)}
    have hH'G : H' ≤ S.G := by
      intro x y hxy
      rcases hxy with h | ⟨he, _⟩
      · exact hHG h
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadjG
        · exact hadjG.symm
    numOrbits (S.geoPhi H' hH'G) = numOrbits (S.geoPhi H hHG) + 1 := by
  classical
  intro H' hH'G
  have hdegH : ∀ v : Fin n, ∃ u, H.Adj v u := by
    intro v
    have hne : ∃ w : Fin n, w ≠ v := by
      by_cases h0 : v.val = 0
      · exact ⟨⟨1, by have := S.hn; omega⟩, fun h => by have hv1 : (1 : ℕ) = v.val := congrArg Fin.val h; omega⟩
      · exact ⟨⟨0, by have := S.hn; omega⟩, fun h => by have hv0 : (0 : ℕ) = v.val := congrArg Fin.val h; omega⟩
    obtain ⟨w, hw⟩ := hne
    obtain ⟨p⟩ := hHconn v w
    cases p with
    | nil => exact (hw rfl).elim
    | cons hvu _ => exact ⟨_, hvu⟩
  -- For each slab j with a < j ≤ b, define the trapezoid rank r_j of the open segment (a, b) in T(H)!
  let segRank (j : Fin (n + 1)) : ℕ :=
    ((S.activeEdges H j).filter (fun e =>
      edgeY S.p e.1 e.2 (S.slabMid j) < edgeY S.p a b (S.slabMid j))).card
  have hsegRank_le (j : Fin (n + 1)) : segRank j ≤ (S.activeEdges H j).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hmid_ab : ∀ j : Fin (n + 1), a.val < j.val → j.val ≤ b.val →
      (S.p a).re < S.slabMid j ∧ S.slabMid j < (S.p b).re := by
    intro j hj1 hj2
    have h1 : 0 < j.val := by omega
    have h2 : j.val < n := by omega
    unfold slabMid; rw [dif_pos h1, dif_pos h2]
    have ha : (S.p a).re ≤ (S.p ⟨j.val - 1, by omega⟩).re :=
      S.hx_mono.monotone (show a ≤ ⟨j.val - 1, by omega⟩ from by change a.val ≤ j.val - 1; omega)
    have hb : (S.p ⟨j.val, h2⟩).re ≤ (S.p b).re :=
      S.hx_mono.monotone (show ⟨j.val, h2⟩ ≤ b from by change j.val ≤ b.val; omega)
    have hlt := S.hx_mono (show (⟨j.val - 1, by omega⟩ : Fin n) < ⟨j.val, h2⟩ from by change j.val - 1 < j.val; omega)
    exact ⟨by linarith, by linarith⟩
  -- Step 1: (a.succ, segRank a.succ) is connected to (b.castSucc, segRank b.castSucc) in T(H)!
  have hchain_step : ∀ v : Fin n, a < v → v < b →
      (S.slabGraph H).Adj
        ⟨v.castSucc, ⟨segRank v.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩
        ⟨v.succ, ⟨segRank v.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
    intro v hav hvb
    -- Reuse the EXACT same passBelow/passAbove argument by viewing (a, b) in S.G!
    -- Compare edgeY a b (p v).re with (p v).im (unequal by edgeY_ne_vertex!)
    have hmid1 := hmid_ab v.castSucc (by simpa) (by simpa using hvb.le)
    have hmid2 := hmid_ab v.succ (by simp; omega) (by simp; omega)
    have hmid1_lt_v : S.slabMid v.castSucc < (S.p v).re :=
      S.slabMid_castSucc_lt (by omega)
    have hv_lt_mid2 : (S.p v).re < S.slabMid v.succ :=
      S.lt_slabMid_succ (by omega)
    apply S.slabGraph_adj_step H v
    rcases lt_or_gt_of_ne (S.edgeY_ne_vertex hav hvb hadjG) with hlt_v | hgt_v
    · -- (a, b) passes BELOW v: both filters equal (passBelow H v).filter (edgeY e (p v).re < edgeY a b (p v).re)!
      let Q := (S.passBelow H v).filter (fun e => edgeY S.p e.1 e.2 (S.p v).re < edgeY S.p a b (S.p v).re)
      have hf1 : (S.activeEdges H v.castSucc).filter (fun e =>
          edgeY S.p e.1 e.2 (S.slabMid v.castSucc) < edgeY S.p a b (S.slabMid v.castSucc)) = Q := by
        ext e; simp only [Finset.mem_filter, Q]
        constructor
        · rintro ⟨heac, hlt⟩
          have hm' := S.slabMid_between H heac
          rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at heac
          rcases heac with hep | heL
          · have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            have hltv := S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              hm'.1 hm'.2 hmid1.1 hmid1.2
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb) hlt
            exact ⟨Finset.mem_filter.mpr ⟨hep, hltv.trans hlt_v⟩, hltv⟩
          · exfalso
            have hL' := Finset.mem_filter.mp heL; have ho' := Finset.mem_filter.mp hL'.1
            have hinc := (S.edgeY_lt_incident_left hav hvb (hL'.2 ▸ ho'.2.1) hadjG (hL'.2 ▸ hHG ho'.2.2)
              hmid1.1 hm'.1 hmid1_lt_v).mpr hlt_v
            rw [hL'.2] at hlt; linarith
        · rintro ⟨heb, hltv⟩
          have hep := (Finset.mem_filter.mp heb).1
          have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          have heac : e ∈ S.activeEdges H v.castSucc := by
            rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hep
          have hm' := S.slabMid_between H heac
          have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
          exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
            hm'.1 hm'.2 hmid1.1 hmid1.2 hltv⟩
      have hf2 : (S.activeEdges H v.succ).filter (fun e =>
          edgeY S.p e.1 e.2 (S.slabMid v.succ) < edgeY S.p a b (S.slabMid v.succ)) = Q := by
        ext e; simp only [Finset.mem_filter, Q]
        constructor
        · rintro ⟨heac, hlt⟩
          have hm' := S.slabMid_between H heac
          rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at heac
          rcases heac with hep | heR
          · have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            have hltv := S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              hm'.1 hm'.2 hmid2.1 hmid2.2
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb) hlt
            exact ⟨Finset.mem_filter.mpr ⟨hep, hltv.trans hlt_v⟩, hltv⟩
          · exfalso
            have hR' := Finset.mem_filter.mp heR; have ho' := Finset.mem_filter.mp hR'.1
            have hinc := (S.edgeY_lt_incident_right hav hvb (hR'.2 ▸ ho'.2.1) hadjG (hR'.2 ▸ hHG ho'.2.2)
              hv_lt_mid2 hmid2.2 hm'.2).mpr hlt_v
            rw [hR'.2] at hlt; linarith
        · rintro ⟨heb, hltv⟩
          have hep := (Finset.mem_filter.mp heb).1
          have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          have heac : e ∈ S.activeEdges H v.succ := by
            rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hep
          have hm' := S.slabMid_between H heac
          have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
          exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
            hm'.1 hm'.2 hmid2.1 hmid2.2 hltv⟩
      left
      have h1 : segRank v.castSucc = Q.card := by dsimp [segRank]; rw [hf1]
      have h2 : segRank v.succ = Q.card := by dsimp [segRank]; rw [hf2]
      have hle : Q.card ≤ (S.passBelow H v).card := Finset.card_le_card (Finset.filter_subset _ _)
      dsimp; omega
    · -- (a, b) passes ABOVE v
      let Q := (S.passAbove H v).filter (fun e => edgeY S.p e.1 e.2 (S.p v).re < edgeY S.p a b (S.p v).re)
      have hf1 : (S.activeEdges H v.castSucc).filter (fun e =>
          edgeY S.p e.1 e.2 (S.slabMid v.castSucc) < edgeY S.p a b (S.slabMid v.castSucc)) =
          (S.passBelow H v ∪ S.leftEdges H v) ∪ Q := by
        ext e; simp only [Finset.mem_filter, Finset.mem_union, Q]
        constructor
        · rintro ⟨heac, hlt⟩
          have hm' := S.slabMid_between H heac
          rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at heac
          rcases heac with hep | heL
          · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hep
            rcases hep with heb | hea
            · exact Or.inl (Or.inl heb)
            · right
              have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hea).1
              have ho' := Finset.mem_filter.mp hp'.1
              have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
              exact ⟨hea, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
                hm'.1 hm'.2 hmid1.1 hmid1.2
                (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb) hlt⟩
          · exact Or.inl (Or.inr heL)
        · rintro ((heb | heL) | ⟨hea, hltv⟩)
          · have hep := (Finset.mem_filter.mp heb).1
            have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have heac : e ∈ S.activeEdges H v.castSucc := by
              rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hep
            have hm' := S.slabMid_between H heac
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
              hm'.1 hm'.2 hmid1.1 hmid1.2 ((Finset.mem_filter.mp heb).2.trans hgt_v)⟩
          · have heac : e ∈ S.activeEdges H v.castSucc := by
              rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_right _ heL
            have hm' := S.slabMid_between H heac
            have hL' := Finset.mem_filter.mp heL; have ho' := Finset.mem_filter.mp hL'.1
            have huv : e.1 < v := hL'.2 ▸ ho'.2.1
            have hnot := (S.edgeY_lt_incident_left hav hvb huv hadjG (hL'.2 ▸ hHG ho'.2.2)
              hmid1.1 hm'.1 hmid1_lt_v).not.mpr (not_lt.mpr hgt_v.le)
            have hney := S.edgeY_ne_of_ne_edges hab huv hadjG (hL'.2 ▸ hHG ho'.2.2)
              (fun h => hvb.ne (congrArg Prod.snd h).symm) hmid1.1 hmid1.2 hm'.1 hmid1_lt_v
            rw [hL'.2]
            exact ⟨heac, lt_of_le_of_ne (not_lt.mp hnot) hney.symm⟩
          · have hep := (Finset.mem_filter.mp hea).1
            have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have heac : e ∈ S.activeEdges H v.castSucc := by
              rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hep
            have hm' := S.slabMid_between H heac
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
              hm'.1 hm'.2 hmid1.1 hmid1.2 hltv⟩
      have hf2 : (S.activeEdges H v.succ).filter (fun e =>
          edgeY S.p e.1 e.2 (S.slabMid v.succ) < edgeY S.p a b (S.slabMid v.succ)) =
          (S.passBelow H v ∪ S.rightEdges H v) ∪ Q := by
        ext e; simp only [Finset.mem_filter, Finset.mem_union, Q]
        constructor
        · rintro ⟨heac, hlt⟩
          have hm' := S.slabMid_between H heac
          rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at heac
          rcases heac with hep | heR
          · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hep
            rcases hep with heb | hea
            · exact Or.inl (Or.inl heb)
            · right
              have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hea).1
              have ho' := Finset.mem_filter.mp hp'.1
              have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
              exact ⟨hea, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
                hm'.1 hm'.2 hmid2.1 hmid2.2
                (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb) hlt⟩
          · exact Or.inl (Or.inr heR)
        · rintro ((heb | heR) | ⟨hea, hltv⟩)
          · have hep := (Finset.mem_filter.mp heb).1
            have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have heac : e ∈ S.activeEdges H v.succ := by
              rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hep
            have hm' := S.slabMid_between H heac
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
              hm'.1 hm'.2 hmid2.1 hmid2.2 ((Finset.mem_filter.mp heb).2.trans hgt_v)⟩
          · have heac : e ∈ S.activeEdges H v.succ := by
              rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_right _ heR
            have hm' := S.slabMid_between H heac
            have hR' := Finset.mem_filter.mp heR; have ho' := Finset.mem_filter.mp hR'.1
            have hvw : v < e.2 := hR'.2 ▸ ho'.2.1
            have hnot := (S.edgeY_lt_incident_right hav hvb hvw hadjG (hR'.2 ▸ hHG ho'.2.2)
              hv_lt_mid2 hmid2.2 hm'.2).not.mpr (not_lt.mpr hgt_v.le)
            have hney := S.edgeY_ne_of_ne_edges hab hvw hadjG (hR'.2 ▸ hHG ho'.2.2)
              (fun h => hav.ne (congrArg Prod.fst h)) hmid2.1 hmid2.2 hv_lt_mid2 hm'.2
            rw [hR'.2]
            exact ⟨heac, lt_of_le_of_ne (not_lt.mp hnot) hney.symm⟩
          · have hep := (Finset.mem_filter.mp hea).1
            have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
            have heac : e ∈ S.activeEdges H v.succ := by
              rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hep
            have hm' := S.slabMid_between H heac
            have hne : e ≠ (a, b) := fun h => hnadjH (by rw [h] at ho'; exact ho'.2.2)
            exact ⟨heac, S.edgeY_order_preserved ho'.2.1 hab (hHG ho'.2.2) hadjG hne
              (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hav) (S.hx_mono hvb)
              hm'.1 hm'.2 hmid2.1 hmid2.2 hltv⟩
      have hd1 : Disjoint (S.passBelow H v) (S.leftEdges H v) :=
        Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_castSucc_eq H v).2
      have hd2 : Disjoint (S.passBelow H v) (S.rightEdges H v) :=
        Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_succ_eq H v).2
      have hq1 : Disjoint (S.passBelow H v ∪ S.leftEdges H v) Q := by
        rw [Finset.disjoint_union_left]
        exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
          Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
            (S.activeEdges_castSucc_eq H v).2.symm⟩
      have hq2 : Disjoint (S.passBelow H v ∪ S.rightEdges H v) Q := by
        rw [Finset.disjoint_union_left]
        exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
          Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
            (S.activeEdges_succ_eq H v).2.symm⟩
      have h1 : segRank v.castSucc = (S.passBelow H v).card + (S.leftEdges H v).card + Q.card := by
        dsimp [segRank]; rw [hf1, Finset.card_union_of_disjoint hq1, Finset.card_union_of_disjoint hd1]
      have h2 : segRank v.succ = (S.passBelow H v).card + (S.rightEdges H v).card + Q.card := by
        dsimp [segRank]; rw [hf2, Finset.card_union_of_disjoint hq2, Finset.card_union_of_disjoint hd2]
      right; dsimp; omega
  have hchain : (S.slabGraph H).Reachable
      ⟨a.succ, ⟨segRank a.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩
      ⟨b.castSucc, ⟨segRank b.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
    suffices hm : ∀ d : ℕ, (hd : a.val + 1 + d ≤ b.val) →
        (S.slabGraph H).Reachable
          ⟨a.succ, ⟨segRank a.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩
          ⟨⟨a.val + 1 + d, by have := b.isLt; omega⟩, ⟨segRank ⟨a.val + 1 + d, by have := b.isLt; omega⟩, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ by
      have := hm (b.val - (a.val + 1)) (by omega)
      have heq_dst : (⟨⟨a.val + 1 + (b.val - (a.val + 1)), by have := b.isLt; omega⟩,
          ⟨segRank ⟨a.val + 1 + (b.val - (a.val + 1)), by have := b.isLt; omega⟩, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ : S.SlabVert H) =
          ⟨b.castSucc, ⟨segRank b.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
        have hi : (⟨a.val + 1 + (b.val - (a.val + 1)), by have := b.isLt; omega⟩ : Fin (n + 1)) = b.castSucc :=
          Fin.ext (by simp; omega)
        exact S.slabVert_ext H hi (by dsimp; rw [hi])
      rw [heq_dst] at this; exact this
    intro d; induction d with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ d ihd =>
      intro hd
      let v : Fin n := ⟨a.val + 1 + d, by have := b.isLt; omega⟩
      exact (ihd (by omega)).trans (hchain_step v (by show a.val < v.val; simp [v]; omega)
        (by show v.val < b.val; simp [v]; omega)).reachable
  -- Step 2: Identify the insertion neighbors u_a (at a) and u_b (at b) in H, i.e. the CCW-next
  -- neighbors of b at a and of a at b in H'!
  have hab_H' : H'.Adj a b := Or.inr ⟨rfl, hadjG.ne⟩
  let u_a_H' := (S.geoSigma H' hH'G a).symm ⟨b, hab_H'⟩
  let u_b_H' := (S.geoSigma H' hH'G b).symm ⟨a, hab_H'.symm⟩
  -- Since deg_H(a) ≥ 1, deg_H'(a) ≥ 2, so u_a ≠ b, hence H.Adj a u_a!
  have hua_ne_b : u_a_H'.1 ≠ b := by
    intro heq
    have hfix : S.geoSigma H' hH'G a ⟨b, hab_H'⟩ = ⟨b, hab_H'⟩ := by
      have h1 : u_a_H' = ⟨b, hab_H'⟩ := Subtype.ext heq
      calc S.geoSigma H' hH'G a ⟨b, hab_H'⟩ = S.geoSigma H' hH'G a u_a_H' := by rw [← h1]
        _ = ⟨b, hab_H'⟩ := (S.geoSigma H' hH'G a).apply_symm_apply _
    obtain ⟨u0, hu0⟩ := hdegH a
    have hne0 : u0 ≠ b := fun h => hnadjH (h ▸ hu0)
    exact S.geoSigma_ne_self H' hH'G a ⟨u0, b, Or.inl hu0, hab_H', hne0⟩ ⟨b, hab_H'⟩ hfix
  have hub_ne_a : u_b_H'.1 ≠ a := by
    intro heq
    have hfix : S.geoSigma H' hH'G b ⟨a, hab_H'.symm⟩ = ⟨a, hab_H'.symm⟩ := by
      have h1 : u_b_H' = ⟨a, hab_H'.symm⟩ := Subtype.ext heq
      calc S.geoSigma H' hH'G b ⟨a, hab_H'.symm⟩ = S.geoSigma H' hH'G b u_b_H' := by rw [← h1]
        _ = ⟨a, hab_H'.symm⟩ := (S.geoSigma H' hH'G b).apply_symm_apply _
    obtain ⟨u0, hu0⟩ := hdegH b
    have hne0 : u0 ≠ a := fun h => hnadjH (h ▸ hu0).symm
    exact S.geoSigma_ne_self H' hH'G b ⟨u0, a, Or.inl hu0, hab_H'.symm, hne0⟩ ⟨a, hab_H'.symm⟩ hfix
  have hua_adj : H.Adj a u_a_H'.1 := by
    rcases u_a_H'.2 with h | ⟨he, _⟩
    · exact h
    · rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact (hua_ne_b h2).elim
      · exact (hab.ne h1).elim
  have hub_adj : H.Adj b u_b_H'.1 := by
    rcases u_b_H'.2 with h | ⟨he, _⟩
    · exact h
    · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (hab.ne h1.symm).elim
      · exact (hub_ne_a h2).elim
  let d_a : DartOf H := ⟨(u_a_H'.1, a), hua_adj.symm⟩
  let d_b : DartOf H := ⟨(u_b_H'.1, b), hub_adj.symm⟩
  -- Step 3: Show dartMap H d_a reaches (a.succ, segRank a.succ) and dartMap H d_b reaches (b.castSucc, segRank b.castSucc)!
  have hseg_a : segRank a.succ = (S.passBelow H a).card +
      ((S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p b - S.p a))).card := by
    have hmid := hmid_ab a.succ (by simp) (by simp; omega)
    have hfilt : (S.activeEdges H a.succ).filter (fun e =>
        edgeY S.p e.1 e.2 (S.slabMid a.succ) < edgeY S.p a b (S.slabMid a.succ)) =
        S.passBelow H a ∪ (S.rightEdges H a).filter (fun e =>
          heading (S.p e.2 - S.p a) < heading (S.p b - S.p a)) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨heac, hlt⟩
        have hm' := S.slabMid_between H heac
        rw [(S.activeEdges_succ_eq H a).1, Finset.mem_union] at heac
        rcases heac with hep | heR
        · left; have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          exact Finset.mem_filter.mpr ⟨hep, (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hab
            (hHG ho'.2.2) hadjG hmid.1 hm'.2 hmid.2).mp hlt⟩
        · right; refine ⟨heR, ?_⟩
          have hR' := Finset.mem_filter.mp heR; have ho' := Finset.mem_filter.mp hR'.1
          have hae : a < e.2 := hR'.2 ▸ ho'.2.1
          rw [hR'.2, edgeY_eq_left_add_slope, edgeY_eq_left_add_slope] at hlt
          have hsl : edgeSlope S.p a e.2 < edgeSlope S.p a b := by
            have : 0 < S.slabMid a.succ - (S.p a).re := by linarith
            nlinarith
          exact (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hae)
            (S.p_sub_re_pos_iff.mpr hab)).mpr (by simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using hsl)
      · rintro (heb | ⟨heR, hlt⟩)
        · have hep := (Finset.mem_filter.mp heb).1
          have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          have heac : e ∈ S.activeEdges H a.succ := by
            rw [(S.activeEdges_succ_eq H a).1]; exact Finset.mem_union_left _ hep
          have hm' := S.slabMid_between H heac
          exact ⟨heac, (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hab (hHG ho'.2.2) hadjG
            hmid.1 hm'.2 hmid.2).mpr (Finset.mem_filter.mp heb).2⟩
        · have heac : e ∈ S.activeEdges H a.succ := by
            rw [(S.activeEdges_succ_eq H a).1]; exact Finset.mem_union_right _ heR
          have hR' := Finset.mem_filter.mp heR; have ho' := Finset.mem_filter.mp hR'.1
          have hae : a < e.2 := hR'.2 ▸ ho'.2.1
          have hsl : edgeSlope S.p a e.2 < edgeSlope S.p a b := by
            have := (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hae)
              (S.p_sub_re_pos_iff.mpr hab)).mp hlt
            simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using this
          refine ⟨heac, ?_⟩
          rw [hR'.2, edgeY_eq_left_add_slope, edgeY_eq_left_add_slope]
          have : 0 < S.slabMid a.succ - (S.p a).re := by linarith
          nlinarith
    have hdisj : Disjoint (S.passBelow H a)
        ((S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p b - S.p a))) :=
      Finset.disjoint_left.mpr fun e h1 h2 =>
        Finset.disjoint_left.mp (S.activeEdges_succ_eq H a).2
          (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
    dsimp [segRank]; rw [hfilt, Finset.card_union_of_disjoint hdisj]
  have hseg_b : segRank b.castSucc = (S.passBelow H b).card +
      ((S.leftEdges H b).filter (fun e => heading (S.p a - S.p b) < heading (S.p e.1 - S.p b))).card := by
    have hmid := hmid_ab b.castSucc (by simpa) (by simp)
    have hfilt : (S.activeEdges H b.castSucc).filter (fun e =>
        edgeY S.p e.1 e.2 (S.slabMid b.castSucc) < edgeY S.p a b (S.slabMid b.castSucc)) =
        S.passBelow H b ∪ (S.leftEdges H b).filter (fun e =>
          heading (S.p a - S.p b) < heading (S.p e.1 - S.p b)) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨heac, hlt⟩
        have hm' := S.slabMid_between H heac
        rw [(S.activeEdges_castSucc_eq H b).1, Finset.mem_union] at heac
        rcases heac with hep | heL
        · left; have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          exact Finset.mem_filter.mpr ⟨hep, (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 hab
            (hHG ho'.2.2) hadjG hm'.1 hmid.1 hmid.2).mp hlt⟩
        · right; refine ⟨heL, ?_⟩
          have hL' := Finset.mem_filter.mp heL; have ho' := Finset.mem_filter.mp hL'.1
          have heb : e.1 < b := hL'.2 ▸ ho'.2.1
          rw [hL'.2, edgeY_eq_right_sub_slope S.p (S.hx_mono heb),
            edgeY_eq_right_sub_slope S.p (S.hx_mono hab)] at hlt
          have hsl : edgeSlope S.p a b < edgeSlope S.p e.1 b := by
            have : 0 < (S.p b).re - S.slabMid b.castSucc := by linarith
            nlinarith
          have hsl' : (S.p a - S.p b).im / (S.p a - S.p b).re < (S.p e.1 - S.p b).im / (S.p e.1 - S.p b).re := by
            have h1 : (S.p a - S.p b).im / (S.p a - S.p b).re = edgeSlope S.p a b := by
              simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
            have h2 : (S.p e.1 - S.p b).im / (S.p e.1 - S.p b).re = edgeSlope S.p e.1 b := by
              simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
            linarith
          exact (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr hab)
            (S.p_sub_re_neg_iff.mpr heb)).mpr hsl'
      · rintro (heb | ⟨heL, hlt⟩)
        · have hep := (Finset.mem_filter.mp heb).1
          have hp' := Finset.mem_filter.mp hep; have ho' := Finset.mem_filter.mp hp'.1
          have heac : e ∈ S.activeEdges H b.castSucc := by
            rw [(S.activeEdges_castSucc_eq H b).1]; exact Finset.mem_union_left _ hep
          have hm' := S.slabMid_between H heac
          exact ⟨heac, (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 hab (hHG ho'.2.2) hadjG
            hm'.1 hmid.1 hmid.2).mpr (Finset.mem_filter.mp heb).2⟩
        · have heac : e ∈ S.activeEdges H b.castSucc := by
            rw [(S.activeEdges_castSucc_eq H b).1]; exact Finset.mem_union_right _ heL
          have hL' := Finset.mem_filter.mp heL; have ho' := Finset.mem_filter.mp hL'.1
          have heb : e.1 < b := hL'.2 ▸ ho'.2.1
          have hsl' := (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr hab)
            (S.p_sub_re_neg_iff.mpr heb)).mp hlt
          have hsl : edgeSlope S.p a b < edgeSlope S.p e.1 b := by
            have h1 : (S.p a - S.p b).im / (S.p a - S.p b).re = edgeSlope S.p a b := by
              simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
            have h2 : (S.p e.1 - S.p b).im / (S.p e.1 - S.p b).re = edgeSlope S.p e.1 b := by
              simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
            linarith
          refine ⟨heac, ?_⟩
          rw [hL'.2, edgeY_eq_right_sub_slope S.p (S.hx_mono heb),
            edgeY_eq_right_sub_slope S.p (S.hx_mono hab)]
          have : 0 < (S.p b).re - S.slabMid b.castSucc := by linarith
          nlinarith
    have hdisj : Disjoint (S.passBelow H b)
        ((S.leftEdges H b).filter (fun e => heading (S.p a - S.p b) < heading (S.p e.1 - S.p b))) :=
      Finset.disjoint_left.mpr fun e h1 h2 =>
        Finset.disjoint_left.mp (S.activeEdges_castSucc_eq H b).2
          (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
    dsimp [segRank]; rw [hfilt, Finset.card_union_of_disjoint hdisj]
  -- Connect dartMap H d_a to (a.succ, segRank a.succ)
  have hda_reach : (S.slabGraph H).Reachable (S.dartMap H d_a)
      ⟨a.succ, ⟨segRank a.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
    have hspec := S.geoSigma_spec H' hH'G a u_a_H'
    have happly : S.geoSigma H' hH'G a u_a_H' = ⟨b, hab_H'⟩ :=
      (S.geoSigma H' hH'G a).apply_symm_apply _
    rw [happly] at hspec
    rcases hspec with ⟨hmin, hmax⟩ | ⟨hlt_ba, hgap_ba⟩
    · -- u_a is MIN heading at a in H', b is MAX heading at a in H' => NO left neighbors of a in H (dL_a = 0) and ALL right neighbors of a in H have heading < heading(b)!
      have hdL0 : (S.leftEdges H a).card = 0 := by
        unfold leftEdges
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h2; simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have h1' := hmax ⟨e.1, Or.inl (h2 ▸ he.2.symm)⟩
        have h2' := S.heading_right_lt_left hab (h2 ▸ he.1); linarith
      have haua : a < u_a_H'.1 := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hua_adj) with h | h
        · exact h
        · exfalso; have := hmax ⟨u_a_H'.1, Or.inl hua_adj⟩; have := S.heading_right_lt_left hab h; linarith
      have hru : S.edgeRank H a.succ (a, u_a_H'.1) = (S.passBelow H a).card := by
        rw [S.edgeRank_rightEdge H hHG haua hua_adj]
        have hf : (S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p u_a_H'.1 - S.p a)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro e he hlt
          have hR := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hR.1
          exact not_lt.mpr (hmin ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩) hlt
        rw [hf, Finset.card_empty, add_zero]
      have hseg_all : segRank a.succ = (S.passBelow H a).card + (S.rightEdges H a).card := by
        rw [hseg_a]; congr 1
        have hf : (S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p b - S.p a)) = S.rightEdges H a := by
          rw [Finset.filter_eq_self]; intro e he
          have hR := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hR.1
          refine lt_of_le_of_ne (hmax ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩) (fun h => ?_)
          have hsub : (⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩ : {x : Fin n // H'.Adj a x}) = ⟨b, hab_H'⟩ :=
            S.heading_inj_H H' hH'G a h
          have he2 : e.2 = b := congrArg Subtype.val hsub
          exact hnadjH (he2 ▸ hR.2 ▸ ho.2.2)
        rw [hf]
      have h1 := S.dartMap_to_target_right H hHG haua hua_adj.symm
      have hpL := S.passBelow_add_left_le H hHG a
      have hpR := S.passBelow_add_right_le H hHG a
      have hg1 : (S.slabGraph H).Adj ⟨a.castSucc, ⟨(S.passBelow H a).card, by omega⟩⟩
          ⟨a.succ, ⟨S.edgeRank H a.succ (a, u_a_H'.1), by
            have hm : (a, u_a_H'.1) ∈ S.activeEdges H a.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, haua, hua_adj⟩, by simp, by simp; omega⟩
            exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ := by
        apply S.slabGraph_adj_step H a; left; dsimp; omega
      have hg2 : (S.slabGraph H).Adj ⟨a.castSucc, ⟨(S.passBelow H a).card, by omega⟩⟩
          ⟨a.succ, ⟨segRank a.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
        apply S.slabGraph_adj_step H a; right; dsimp; omega
      exact h1.trans (hg1.symm.reachable.trans hg2.reachable)
    · -- Non-wrap: heading(b) < heading(u_a) with NO neighbor of a strictly between b and u_a!
      rcases lt_or_gt_of_ne (H.ne_of_adj hua_adj) with haua | huam
      · -- u_a is a RIGHT neighbor of a: rank(a.succ, (a, u_a)) = segRank a.succ!
        have hreq : S.edgeRank H a.succ (a, u_a_H'.1) = segRank a.succ := by
          rw [S.edgeRank_rightEdge H hHG haua hua_adj, hseg_a]; congr 1
          have hf : (S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p u_a_H'.1 - S.p a)) =
              (S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p b - S.p a)) := by
            ext e; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨heR, hlt⟩
              refine ⟨heR, ?_⟩
              have hR := Finset.mem_filter.mp heR; have ho := Finset.mem_filter.mp hR.1
              by_contra! hge
              have hne : e.2 ≠ b := fun h => hnadjH (h ▸ hR.2 ▸ ho.2.2)
              have hgt : heading (S.p b - S.p a) < heading (S.p e.2 - S.p a) :=
                lt_of_le_of_ne hge (fun h => hne (congrArg Subtype.val
                  (show (⟨b, hab_H'⟩ : {x : Fin n // H'.Adj a x}) = ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩ from
                    S.heading_inj_H H' hH'G a h)).symm)
              have := hgap_ba ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩ hgt; linarith
            · rintro ⟨heR, hlt⟩; exact ⟨heR, hlt.trans hlt_ba⟩
          rw [hf]
        have h1 := S.dartMap_to_target_right H hHG haua hua_adj.symm
        convert h1 using 1
        exact Sigma.ext rfl (heq_of_eq (Fin.ext hreq.symm))
      · -- u_a is a LEFT neighbor of a: topmost left edge (rank = p + dL - 1), and segRank a.succ = p + dR!
        have hru : S.edgeRank H a.castSucc (u_a_H'.1, a) = (S.passBelow H a).card + (S.leftEdges H a).card - 1 := by
          rw [S.edgeRank_leftEdge H hHG huam hua_adj.symm]
          have hf : (S.leftEdges H a).filter (fun e => heading (S.p u_a_H'.1 - S.p a) < heading (S.p e.1 - S.p a)) =
              (S.leftEdges H a).erase (u_a_H'.1, a) := by
            ext e; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he, hlt⟩; exact ⟨fun h => by rw [h] at hlt; exact lt_irrefl _ hlt, he⟩
            · rintro ⟨hne, he⟩
              have hL := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hL.1
              have hge := hgap_ba ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩ (S.heading_right_lt_left hab (hL.2 ▸ ho.2.1))
              refine ⟨he, lt_of_le_of_ne hge (fun h => hne ?_)⟩
              exact Prod.ext (congrArg Subtype.val
                (show u_a_H' = ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩ from S.heading_inj_H H' hH'G a h)).symm hL.2
          have hu_mem : (u_a_H'.1, a) ∈ S.leftEdges H a :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huam, hua_adj.symm⟩, rfl⟩
          rw [hf, Finset.card_erase_of_mem hu_mem]
          have := Finset.card_pos.mpr ⟨_, hu_mem⟩; omega
        have hseg_all : segRank a.succ = (S.passBelow H a).card + (S.rightEdges H a).card := by
          rw [hseg_a]; congr 1
          have hf : (S.rightEdges H a).filter (fun e => heading (S.p e.2 - S.p a) < heading (S.p b - S.p a)) = S.rightEdges H a := by
            rw [Finset.filter_eq_self]; intro e he
            have hR := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hR.1
            by_contra! hge
            have hne : e.2 ≠ b := fun h => hnadjH (h ▸ hR.2 ▸ ho.2.2)
            have hgt : heading (S.p b - S.p a) < heading (S.p e.2 - S.p a) :=
              lt_of_le_of_ne hge (fun h => hne (congrArg Subtype.val
                (show (⟨b, hab_H'⟩ : {x : Fin n // H'.Adj a x}) = ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩ from
                  S.heading_inj_H H' hH'G a h)).symm)
            have := hgap_ba ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩ hgt
            have := S.heading_right_lt_left (hR.2 ▸ ho.2.1) huam; linarith
          rw [hf]
        have hdL1 : 1 ≤ (S.leftEdges H a).card := Finset.card_pos.mpr ⟨(u_a_H'.1, a),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huam, hua_adj.symm⟩, rfl⟩⟩
        have h1 := S.dartMap_to_target_left H hHG huam hua_adj.symm
        have hglue : (S.slabGraph H).Adj
            ⟨a.castSucc, ⟨S.edgeRank H a.castSucc (u_a_H'.1, a) + 1, by
              have hm : (u_a_H'.1, a) ∈ S.activeEdges H a.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huam, hua_adj.symm⟩, by simpa, by simp⟩
              exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
            ⟨a.succ, ⟨segRank a.succ, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
          apply S.slabGraph_adj_step H a; right; dsimp; omega
        exact h1.trans hglue.reachable
  -- Connect dartMap H d_b to (b.castSucc, segRank b.castSucc)
  have hdb_reach : (S.slabGraph H).Reachable (S.dartMap H d_b)
      ⟨b.castSucc, ⟨segRank b.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩ := by
    have hspec := S.geoSigma_spec H' hH'G b u_b_H'
    have happly : S.geoSigma H' hH'G b u_b_H' = ⟨a, hab_H'.symm⟩ :=
      (S.geoSigma H' hH'G b).apply_symm_apply _
    rw [happly] at hspec
    rcases hspec with ⟨hmin, hmax⟩ | ⟨hlt_ab, hgap_ab⟩
    · -- Wrap: u_b is MIN heading at b in H', a is MAX heading at b in H' => NO left neighbor of b has heading > heading(a), so segRank b.castSucc = p_b!
      have hseg_p : segRank b.castSucc = (S.passBelow H b).card := by
        rw [hseg_b]
        have hf : (S.leftEdges H b).filter (fun e => heading (S.p a - S.p b) < heading (S.p e.1 - S.p b)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro e he hlt
          have hL := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hL.1
          exact not_lt.mpr (hmax ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩) hlt
        rw [hf, Finset.card_empty, add_zero]
      rcases lt_or_gt_of_ne (H.ne_of_adj hub_adj).symm with hubb | hbub
      · -- u_b < b is min heading => NO right neighbors of b (dR_b = 0), u_b is topmost left neighbor (rank = p + dL - 1)!
        have hdR0 : (S.rightEdges H b).card = 0 := by
          unfold rightEdges
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro e he h1; simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
          have h1' := hmin ⟨e.2, Or.inl (h1 ▸ he.2)⟩
          have h2' := S.heading_right_lt_left (h1 ▸ he.1) hubb; linarith
        have hru : S.edgeRank H b.castSucc (u_b_H'.1, b) = (S.passBelow H b).card + (S.leftEdges H b).card - 1 := by
          rw [S.edgeRank_leftEdge H hHG hubb hub_adj.symm]
          have hf : (S.leftEdges H b).filter (fun e => heading (S.p u_b_H'.1 - S.p b) < heading (S.p e.1 - S.p b)) =
              (S.leftEdges H b).erase (u_b_H'.1, b) := by
            ext e; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he, hlt⟩; exact ⟨fun h => by rw [h] at hlt; exact lt_irrefl _ hlt, he⟩
            · rintro ⟨hne, he⟩
              have hL := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hL.1
              refine ⟨he, lt_of_le_of_ne (hmin ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩) (fun h => hne ?_)⟩
              exact Prod.ext (congrArg Subtype.val
                (show u_b_H' = ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩ from S.heading_inj_H H' hH'G b h)).symm hL.2
          have hu_mem : (u_b_H'.1, b) ∈ S.leftEdges H b :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hubb, hub_adj.symm⟩, rfl⟩
          rw [hf, Finset.card_erase_of_mem hu_mem]
          have := Finset.card_pos.mpr ⟨_, hu_mem⟩; omega
        have hdL1 : 1 ≤ (S.leftEdges H b).card := Finset.card_pos.mpr ⟨(u_b_H'.1, b),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hubb, hub_adj.symm⟩, rfl⟩⟩
        have hpR := S.passBelow_add_right_le H hHG b
        have h1 := S.dartMap_to_target_left H hHG hubb hub_adj.symm
        have hg1 : (S.slabGraph H).Adj
            ⟨b.castSucc, ⟨S.edgeRank H b.castSucc (u_b_H'.1, b) + 1, by
              have hm : (u_b_H'.1, b) ∈ S.activeEdges H b.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hubb, hub_adj.symm⟩, by simpa, by simp⟩
              exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
            ⟨b.succ, ⟨(S.passBelow H b).card, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H b; right; dsimp; omega
        have hg2 : (S.slabGraph H).Adj
            ⟨b.castSucc, ⟨segRank b.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩
            ⟨b.succ, ⟨(S.passBelow H b).card, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H b; left; dsimp; omega
        exact h1.trans (hg1.reachable.trans hg2.symm.reachable)
      · -- b < u_b is min heading => bottommost right edge (rank(b.succ, (b, u_b)) = p_b)!
        have hru : S.edgeRank H b.succ (b, u_b_H'.1) = (S.passBelow H b).card := by
          rw [S.edgeRank_rightEdge H hHG hbub hub_adj]
          have hf : (S.rightEdges H b).filter (fun e => heading (S.p e.2 - S.p b) < heading (S.p u_b_H'.1 - S.p b)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro e he hlt
            have hR := Finset.mem_filter.mp he; have ho := Finset.mem_filter.mp hR.1
            exact not_lt.mpr (hmin ⟨e.2, Or.inl (hR.2 ▸ ho.2.2)⟩) hlt
          rw [hf, Finset.card_empty, add_zero]
        have h1 := S.dartMap_to_target_right H hHG hbub hub_adj.symm
        have hglue : (S.slabGraph H).Adj
            ⟨b.castSucc, ⟨segRank b.castSucc, Nat.lt_succ_of_le (hsegRank_le _)⟩⟩
            ⟨b.succ, ⟨S.edgeRank H b.succ (b, u_b_H'.1), by
              have hm : (b, u_b_H'.1) ∈ S.activeEdges H b.succ :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbub, hub_adj⟩, by simp, by simp; omega⟩
              exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ := by
          apply S.slabGraph_adj_step H b; left; dsimp; omega
        exact h1.trans hglue.symm.reachable
    · -- Non-wrap: heading(a) < heading(u_b) => since a < b, heading(a) > π/2, so u_b < b TOO!
      have hubb : u_b_H'.1 < b := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hub_adj).symm with h | h
        · exact h
        · exfalso; have := S.heading_right_lt_left h hab; linarith
      -- rank(b.castSucc, (u_b, b)) + 1 = segRank b.castSucc!
      have hreq : S.edgeRank H b.castSucc (u_b_H'.1, b) + 1 = segRank b.castSucc := by
        rw [S.edgeRank_leftEdge H hHG hubb hub_adj.symm, hseg_b]
        have hf : (S.leftEdges H b).filter (fun e => heading (S.p a - S.p b) < heading (S.p e.1 - S.p b)) =
            insert (u_b_H'.1, b) ((S.leftEdges H b).filter (fun e =>
              heading (S.p u_b_H'.1 - S.p b) < heading (S.p e.1 - S.p b))) := by
          ext e; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨heL, hlt⟩
            have hL := Finset.mem_filter.mp heL; have ho := Finset.mem_filter.mp hL.1
            have hge := hgap_ab ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩ hlt
            rcases eq_or_lt_of_le hge with heq | hgt
            · left; exact Prod.ext (congrArg Subtype.val
                (show u_b_H' = ⟨e.1, Or.inl (hL.2 ▸ ho.2.2.symm)⟩ from S.heading_inj_H H' hH'G b heq)).symm hL.2
            · right; exact ⟨heL, hgt⟩
          · rintro (rfl | ⟨heL, hgt⟩)
            · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hubb, hub_adj.symm⟩, rfl⟩, hlt_ab⟩
            · exact ⟨heL, hlt_ab.trans hgt⟩
        rw [hf, Finset.card_insert_of_notMem (by simp [lt_irrefl])]; omega
      have h1 := S.dartMap_to_target_left H hHG hubb hub_adj.symm
      convert h1 using 1
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hreq.symm))
  -- Step 4: Therefore dartMap H d_a and dartMap H d_b are in the SAME component of T(H),
  -- so by bijectivity of orbitToComp H, d_a and d_b are in the SAME φ_H-orbit!
  have hcomp_eq : S.orbitToComp H hHG (Quotient.mk _ d_a) = S.orbitToComp H hHG (Quotient.mk _ d_b) :=
    SimpleGraph.ConnectedComponent.sound (hda_reach.trans (hchain.trans hdb_reach.symm))
  have hsame : sameOrbit (S.geoPhi H hHG) d_a d_b :=
    Quotient.exact (hbij.1 hcomp_eq)
  have hne_dab : d_a ≠ d_b := fun h => hab.ne (congrArg (fun d : DartOf H => d.1.2) h)
  -- Step 5: Identify DartOf H' ≃ DartOf H ⊕ Bool and apply splice_adds_one_orbit!
  let emb : DartOf H ⊕ Bool ≃ DartOf H' :=
    { toFun := fun x => match x with
        | Sum.inl d => ⟨d.1, Or.inl d.2⟩
        | Sum.inr false => ⟨(a, b), hab_H'⟩
        | Sum.inr true => ⟨(b, a), hab_H'.symm⟩
      invFun := fun d =>
        if h1 : d.1 = (a, b) then Sum.inr false
        else if h2 : d.1 = (b, a) then Sum.inr true
        else Sum.inl ⟨d.1, by
          rcases d.2 with h | ⟨he, _⟩
          · exact h
          · rcases Sym2.eq_iff.mp he with ⟨ha1, hb1⟩ | ⟨hb1, ha1⟩
            · exact (h1 (Prod.ext ha1 hb1)).elim
            · exact (h2 (Prod.ext hb1 ha1)).elim⟩
      left_inv := fun x => by
        rcases x with d | b'
        · have h1 : d.1 ≠ (a, b) := fun h => hnadjH (by rcases d with ⟨⟨u, v⟩, hadj⟩; dsimp at h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact hadj)
          have h2 : d.1 ≠ (b, a) := fun h => hnadjH (by rcases d with ⟨⟨u, v⟩, hadj⟩; dsimp at h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact hadj.symm)
          simp [h1, h2]
        · cases b'
          · simp
          · have hne : (b, a) ≠ (a, b) := fun h => hab.ne (Prod.mk.inj h).1.symm
            simp [hne]
      right_inv := fun d => by
        dsimp
        split_ifs with h1 h2
        · exact Subtype.ext h1.symm
        · exact Subtype.ext h2.symm
        · rfl }
  let φ' : Equiv.Perm (DartOf H ⊕ Bool) := emb.trans ((S.geoPhi H' hH'G).trans emb.symm)
  -- Show how geoSigma H' relates to geoSigma H at every vertex v!
  have hσ_eq_other : ∀ (v u : Fin n) (hvu : H.Adj v u),
      (v ≠ a ∧ v ≠ b) ∨ (v = a ∧ u ≠ u_a_H'.1) ∨ (v = b ∧ u ≠ u_b_H'.1) →
      (S.geoSigma H' hH'G v ⟨u, Or.inl hvu⟩).1 = (S.geoSigma H hHG v ⟨u, hvu⟩).1 := by
    intro v u hvu hcase
    -- General fact: cwPredPerm on A' = A ∪ {new} agrees with cwPredPerm on A at every u whose cwPred in A' is ≠ new!
    have hnot_new : ∀ w : {x : Fin n // H'.Adj v x}, w = S.geoSigma H' hH'G v ⟨u, Or.inl hvu⟩ → H.Adj v w.1 := by
      intro w hw
      rcases w.2 with h | ⟨he, _⟩
      · exact h
      · exfalso
        rcases Sym2.eq_iff.mp he with ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
        · subst hva
          have hw_eq : w = ⟨b, hab_H'⟩ := Subtype.ext hwb
          rw [hw_eq] at hw
          have hthis : u_a_H' = ⟨u, Or.inl hvu⟩ := by
            have := congrArg (S.geoSigma H' hH'G v).symm hw
            rw [Equiv.symm_apply_apply] at this
            exact this
          rcases hcase with ⟨hva', _⟩ | ⟨_, hne⟩ | ⟨hvb', _⟩
          · exact hva' rfl
          · exact hne (congrArg Subtype.val hthis).symm
          · exact hab.ne hvb'
        · subst hvb
          have hw_eq : w = ⟨a, hab_H'.symm⟩ := Subtype.ext hwa
          rw [hw_eq] at hw
          have hthis : u_b_H' = ⟨u, Or.inl hvu⟩ := by
            have := congrArg (S.geoSigma H' hH'G v).symm hw
            rw [Equiv.symm_apply_apply] at this
            exact this
          rcases hcase with ⟨_, hvb'⟩ | ⟨hva', _⟩ | ⟨_, hne⟩
          · exact hvb' rfl
          · exact hab.ne hva'.symm
          · exact hne (congrArg Subtype.val hthis).symm
    let w' := S.geoSigma H' hH'G v ⟨u, Or.inl hvu⟩
    have hw'_H : H.Adj v w'.1 := hnot_new w' rfl
    let w := S.geoSigma H hHG v ⟨u, hvu⟩
    rcases S.geoSigma_spec H' hH'G v ⟨u, Or.inl hvu⟩ with ⟨hmin', hmax'⟩ | ⟨hlt', hgap'⟩
    · rcases S.geoSigma_spec H hHG v ⟨u, hvu⟩ with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
      · have heq : heading (S.p w'.1 - S.p v) = heading (S.p w.1 - S.p v) :=
          le_antisymm (hmax ⟨w'.1, hw'_H⟩) (hmax' ⟨w.1, Or.inl w.2⟩)
        have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj v x}) = w := S.heading_inj_H H hHG v heq
        exact congrArg Subtype.val hsub
      · exfalso; have := hmin' ⟨w.1, Or.inl w.2⟩; linarith
    · rcases S.geoSigma_spec H hHG v ⟨u, hvu⟩ with ⟨hmin, _⟩ | ⟨hlt, hgap⟩
      · exfalso; have := hmin ⟨w'.1, hw'_H⟩; linarith
      · have h1 : heading (S.p w'.1 - S.p v) ≤ heading (S.p w.1 - S.p v) := by
          by_contra! hgt; have := hgap ⟨w'.1, hw'_H⟩ hgt; linarith
        have h2 : heading (S.p w.1 - S.p v) ≤ heading (S.p w'.1 - S.p v) := by
          by_contra! hgt; have := hgap' ⟨w.1, Or.inl w.2⟩ hgt; linarith
        have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj v x}) = w := S.heading_inj_H H hHG v (le_antisymm h1 h2)
        exact congrArg Subtype.val hsub
  have hσ_ab : (S.geoSigma H' hH'G a ⟨b, hab_H'⟩).1 = (S.geoSigma H hHG a ⟨u_a_H'.1, hua_adj⟩).1 := by
    let w' := S.geoSigma H' hH'G a ⟨b, hab_H'⟩
    have hw'_ne_b : w'.1 ≠ b := by
      intro h
      have hfix : S.geoSigma H' hH'G a ⟨b, hab_H'⟩ = ⟨b, hab_H'⟩ := Subtype.ext h
      have : u_a_H' = ⟨b, hab_H'⟩ := by
        have h1 := congrArg (S.geoSigma H' hH'G a).symm hfix
        rw [Equiv.symm_apply_apply] at h1
        exact h1.symm
      exact hua_ne_b (congrArg Subtype.val this)
    have hw'_H : H.Adj a w'.1 := by
      rcases w'.2 with h | ⟨he, _⟩
      · exact h
      · rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact (hw'_ne_b h2).elim
        · exact (hab.ne h1).elim
    let w := S.geoSigma H hHG a ⟨u_a_H'.1, hua_adj⟩
    have hsp1 := S.geoSigma_spec H' hH'G a u_a_H'
    have happ1 : S.geoSigma H' hH'G a u_a_H' = ⟨b, hab_H'⟩ := (S.geoSigma H' hH'G a).apply_symm_apply _
    rw [happ1] at hsp1
    have hsp2 := S.geoSigma_spec H' hH'G a ⟨b, hab_H'⟩
    have hspH := S.geoSigma_spec H hHG a ⟨u_a_H'.1, hua_adj⟩
    rcases hsp1 with ⟨hmin1, hmax1⟩ | ⟨hlt1, hgap1⟩
    · have hw'_max : ∀ x : {x : Fin n // H.Adj a x}, heading (S.p x.1 - S.p a) ≤ heading (S.p w'.1 - S.p a) := by
        intro x
        rcases hsp2 with ⟨hmin2, _⟩ | ⟨hlt2, hgap2⟩
        · exfalso; have := hmin2 u_a_H'; have := hmax1 u_a_H'
          have hsub : u_a_H' = ⟨b, hab_H'⟩ := S.heading_inj_H H' hH'G a (le_antisymm this ‹_›)
          exact hua_ne_b (congrArg Subtype.val hsub)
        · by_contra! hgt
          have hge := hgap2 ⟨x.1, Or.inl x.2⟩ hgt
          have hle := hmax1 ⟨x.1, Or.inl x.2⟩
          have hsub : (⟨x.1, Or.inl x.2⟩ : {u : Fin n // H'.Adj a u}) = ⟨b, hab_H'⟩ :=
            S.heading_inj_H H' hH'G a (le_antisymm hle hge)
          have hx : x.1 = b := congrArg Subtype.val hsub
          exact hnadjH (hx ▸ x.2)
      rcases hspH with ⟨_, hmaxH⟩ | ⟨hltH, _⟩
      · have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj a x}) = w :=
          S.heading_inj_H H hHG a (le_antisymm (hmaxH ⟨w'.1, hw'_H⟩) (hw'_max w))
        exact congrArg Subtype.val hsub
      · exfalso; have := hmin1 ⟨w.1, Or.inl w.2⟩; linarith
    · rcases hsp2 with ⟨hmin2, hmax2⟩ | ⟨hlt2, hgap2⟩
      · have hua_minH : ∀ x : {x : Fin n // H.Adj a x}, heading (S.p u_a_H'.1 - S.p a) ≤ heading (S.p x.1 - S.p a) := by
          intro x
          have hge := hmin2 ⟨x.1, Or.inl x.2⟩
          have hne : x.1 ≠ b := fun h => hnadjH (h ▸ x.2)
          exact hgap1 ⟨x.1, Or.inl x.2⟩ (lt_of_le_of_ne hge (fun h => hne (by
            have hsub : (⟨b, hab_H'⟩ : {u : Fin n // H'.Adj a u}) = ⟨x.1, Or.inl x.2⟩ := S.heading_inj_H H' hH'G a h
            exact (congrArg Subtype.val hsub).symm)))
        rcases hspH with ⟨_, hmaxH⟩ | ⟨hltH, _⟩
        · have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj a x}) = w :=
            S.heading_inj_H H hHG a (le_antisymm (hmaxH ⟨w'.1, hw'_H⟩) (hmax2 ⟨w.1, Or.inl w.2⟩))
          exact congrArg Subtype.val hsub
        · exfalso; have := hua_minH w; linarith
      · rcases hspH with ⟨hminH, _⟩ | ⟨hltH, hgapH⟩
        · exfalso; have := hminH ⟨w'.1, hw'_H⟩; linarith
        · have h1 : heading (S.p w'.1 - S.p a) ≤ heading (S.p w.1 - S.p a) := by
            by_contra! hgt; have := hgapH ⟨w'.1, hw'_H⟩ hgt; linarith
          have h2 : heading (S.p w.1 - S.p a) ≤ heading (S.p w'.1 - S.p a) := by
            by_contra! hgt
            have hge := hgap2 ⟨w.1, Or.inl w.2⟩ hgt
            have hne : w.1 ≠ b := fun h => hnadjH (h ▸ w.2)
            have hgt2 : heading (S.p b - S.p a) < heading (S.p w.1 - S.p a) :=
              lt_of_le_of_ne hge (fun h => hne (by
                have hsub : (⟨b, hab_H'⟩ : {u : Fin n // H'.Adj a u}) = ⟨w.1, Or.inl w.2⟩ := S.heading_inj_H H' hH'G a h
                exact (congrArg Subtype.val hsub).symm))
            have := hgap1 ⟨w.1, Or.inl w.2⟩ hgt2; linarith
          have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj a x}) = w :=
            S.heading_inj_H H hHG a (le_antisymm h1 h2)
          exact congrArg Subtype.val hsub
  have hσ_ba : (S.geoSigma H' hH'G b ⟨a, hab_H'.symm⟩).1 = (S.geoSigma H hHG b ⟨u_b_H'.1, hub_adj⟩).1 := by
    let w' := S.geoSigma H' hH'G b ⟨a, hab_H'.symm⟩
    have hw'_ne_a : w'.1 ≠ a := by
      intro h
      have hfix : S.geoSigma H' hH'G b ⟨a, hab_H'.symm⟩ = ⟨a, hab_H'.symm⟩ := Subtype.ext h
      have : u_b_H' = ⟨a, hab_H'.symm⟩ := by
        have h1 := congrArg (S.geoSigma H' hH'G b).symm hfix
        rw [Equiv.symm_apply_apply] at h1
        exact h1.symm
      exact hub_ne_a (congrArg Subtype.val this)
    have hw'_H : H.Adj b w'.1 := by
      rcases w'.2 with h | ⟨he, _⟩
      · exact h
      · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact (hab.ne h1.symm).elim
        · exact (hw'_ne_a h2).elim
    let w := S.geoSigma H hHG b ⟨u_b_H'.1, hub_adj⟩
    have hsp1 := S.geoSigma_spec H' hH'G b u_b_H'
    have happ1 : S.geoSigma H' hH'G b u_b_H' = ⟨a, hab_H'.symm⟩ := (S.geoSigma H' hH'G b).apply_symm_apply _
    rw [happ1] at hsp1
    have hsp2 := S.geoSigma_spec H' hH'G b ⟨a, hab_H'.symm⟩
    have hspH := S.geoSigma_spec H hHG b ⟨u_b_H'.1, hub_adj⟩
    rcases hsp1 with ⟨hmin1, hmax1⟩ | ⟨hlt1, hgap1⟩
    · have hw'_max : ∀ x : {x : Fin n // H.Adj b x}, heading (S.p x.1 - S.p b) ≤ heading (S.p w'.1 - S.p b) := by
        intro x
        rcases hsp2 with ⟨hmin2, _⟩ | ⟨hlt2, hgap2⟩
        · exfalso; have := hmin2 u_b_H'; have := hmax1 u_b_H'
          have hsub : u_b_H' = ⟨a, hab_H'.symm⟩ := S.heading_inj_H H' hH'G b (le_antisymm this ‹_›)
          exact hub_ne_a (congrArg Subtype.val hsub)
        · by_contra! hgt
          have hge := hgap2 ⟨x.1, Or.inl x.2⟩ hgt
          have hle := hmax1 ⟨x.1, Or.inl x.2⟩
          have hsub : (⟨x.1, Or.inl x.2⟩ : {u : Fin n // H'.Adj b u}) = ⟨a, hab_H'.symm⟩ :=
            S.heading_inj_H H' hH'G b (le_antisymm hle hge)
          have hx : x.1 = a := congrArg Subtype.val hsub
          exact hnadjH (hx ▸ x.2).symm
      rcases hspH with ⟨_, hmaxH⟩ | ⟨hltH, _⟩
      · have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj b x}) = w :=
          S.heading_inj_H H hHG b (le_antisymm (hmaxH ⟨w'.1, hw'_H⟩) (hw'_max w))
        exact congrArg Subtype.val hsub
      · exfalso; have := hmin1 ⟨w.1, Or.inl w.2⟩; linarith
    · rcases hsp2 with ⟨hmin2, hmax2⟩ | ⟨hlt2, hgap2⟩
      · have hub_minH : ∀ x : {x : Fin n // H.Adj b x}, heading (S.p u_b_H'.1 - S.p b) ≤ heading (S.p x.1 - S.p b) := by
          intro x
          have hge := hmin2 ⟨x.1, Or.inl x.2⟩
          have hne : x.1 ≠ a := fun h => hnadjH (h ▸ x.2).symm
          exact hgap1 ⟨x.1, Or.inl x.2⟩ (lt_of_le_of_ne hge (fun h => hne (by
            have hsub : (⟨a, hab_H'.symm⟩ : {u : Fin n // H'.Adj b u}) = ⟨x.1, Or.inl x.2⟩ := S.heading_inj_H H' hH'G b h
            exact (congrArg Subtype.val hsub).symm)))
        rcases hspH with ⟨_, hmaxH⟩ | ⟨hltH, _⟩
        · have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj b x}) = w :=
            S.heading_inj_H H hHG b (le_antisymm (hmaxH ⟨w'.1, hw'_H⟩) (hmax2 ⟨w.1, Or.inl w.2⟩))
          exact congrArg Subtype.val hsub
        · exfalso; have := hub_minH w; linarith
      · rcases hspH with ⟨hminH, _⟩ | ⟨hltH, hgapH⟩
        · exfalso; have := hminH ⟨w'.1, hw'_H⟩; linarith
        · have h1 : heading (S.p w'.1 - S.p b) ≤ heading (S.p w.1 - S.p b) := by
            by_contra! hgt; have := hgapH ⟨w'.1, hw'_H⟩ hgt; linarith
          have h2 : heading (S.p w.1 - S.p b) ≤ heading (S.p w'.1 - S.p b) := by
            by_contra! hgt
            have hge := hgap2 ⟨w.1, Or.inl w.2⟩ hgt
            have hne : w.1 ≠ a := fun h => hnadjH (h ▸ w.2).symm
            have hgt2 : heading (S.p a - S.p b) < heading (S.p w.1 - S.p b) :=
              lt_of_le_of_ne hge (fun h => hne (by
                have hsub : (⟨a, hab_H'.symm⟩ : {u : Fin n // H'.Adj b u}) = ⟨w.1, Or.inl w.2⟩ := S.heading_inj_H H' hH'G b h
                exact (congrArg Subtype.val hsub).symm))
            have := hgap1 ⟨w.1, Or.inl w.2⟩ hgt2; linarith
          have hsub : (⟨w'.1, hw'_H⟩ : {x : Fin n // H.Adj b x}) = w :=
            S.heading_inj_H H hHG b (le_antisymm h1 h2)
          exact congrArg Subtype.val hsub
  -- Verify the 5 hypotheses of splice_adds_one_orbit for φ'
  have hnum_eq : numOrbits (S.geoPhi H' hH'G) = numOrbits φ' := by
    unfold numOrbits
    haveI : Fintype (Quotient (orbitSetoid (S.geoPhi H' hH'G))) := Fintype.ofFinite _
    haveI : Fintype (Quotient (orbitSetoid φ')) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hpow : ∀ k : ℕ, ∀ x, (φ' ^ k) x = emb.symm (((S.geoPhi H' hH'G) ^ k) (emb x)) := by
      intro k; induction k with
      | zero => intro x; simp
      | succ k ihk => intro x; rw [pow_succ', Equiv.Perm.mul_apply, ihk, pow_succ', Equiv.Perm.mul_apply]; simp [φ']
    refine (Fintype.card_of_bijective (f := Quotient.lift (fun x => Quotient.mk (orbitSetoid (S.geoPhi H' hH'G)) (emb x)) (by
      intro x y ⟨k, hk⟩; apply Quotient.sound; refine ⟨k, ?_⟩
      rw [← hk, hpow, emb.apply_symm_apply])) ⟨?_, ?_⟩).symm
    · intro q₁ q₂ h
      induction q₁ using Quotient.ind with | _ x₁ =>
      induction q₂ using Quotient.ind with | _ x₂ =>
      obtain ⟨k, hk⟩ := Quotient.exact h
      apply Quotient.sound; refine ⟨k, ?_⟩
      rw [hpow, hk, emb.symm_apply_apply]
    · intro q
      induction q using Quotient.ind with | _ y =>
      exact ⟨Quotient.mk _ (emb.symm y), by simp⟩
  rw [hnum_eq]
  refine splice_adds_one_orbit (S.geoPhi H hHG) hne_dab hsame φ' ?_ ?_ ?_ ?_ ?_
  · intro d hna hnb
    apply emb.injective
    rw [show emb (φ' (Sum.inl d)) = S.geoPhi H' hH'G (emb (Sum.inl d)) by simp [φ']]
    apply Subtype.ext; apply Prod.ext; · rfl
    · have hcase : (d.1.2 ≠ a ∧ d.1.2 ≠ b) ∨ (d.1.2 = a ∧ d.1.1 ≠ u_a_H'.1) ∨ (d.1.2 = b ∧ d.1.1 ≠ u_b_H'.1) := by
        by_cases ha : d.1.2 = a
        · right; left; refine ⟨ha, fun h => hna (Subtype.ext (Prod.ext h ha))⟩
        · by_cases hb : d.1.2 = b
          · right; right; refine ⟨hb, fun h => hnb (Subtype.ext (Prod.ext h hb))⟩
          · left; exact ⟨ha, hb⟩
      exact hσ_eq_other d.1.2 d.1.1 d.2.symm hcase
  · apply emb.injective
    rw [show emb (φ' (Sum.inl d_a)) = S.geoPhi H' hH'G (emb (Sum.inl d_a)) by simp [φ']]
    apply Subtype.ext; apply Prod.ext; · rfl
    · exact congrArg Subtype.val ((S.geoSigma H' hH'G a).apply_symm_apply ⟨b, hab_H'⟩)
  · apply emb.injective
    rw [show emb (φ' (Sum.inr false)) = S.geoPhi H' hH'G (emb (Sum.inr false)) by simp [φ']]
    apply Subtype.ext; apply Prod.ext; · rfl
    · exact hσ_ba
  · apply emb.injective
    rw [show emb (φ' (Sum.inl d_b)) = S.geoPhi H' hH'G (emb (Sum.inl d_b)) by simp [φ']]
    apply Subtype.ext; apply Prod.ext; · rfl
    · exact congrArg Subtype.val ((S.geoSigma H' hH'G b).apply_symm_apply ⟨a, hab_H'.symm⟩)
  · apply emb.injective
    rw [show emb (φ' (Sum.inr true)) = S.geoPhi H' hH'G (emb (Sum.inr true)) by simp [φ']]
    apply Subtype.ext; apply Prod.ext; · rfl
    · exact hσ_ab

open Classical in
private lemma numOrbits_geoPhi_congr {H₁ H₂ : SimpleGraph (Fin n)}
    (h₁ : H₁ ≤ S.G) (h₂ : H₂ ≤ S.G) (heq : H₁ = H₂) :
    numOrbits (S.geoPhi H₁ h₁) = numOrbits (S.geoPhi H₂ h₂) := by
  subst heq; rfl

/-- THE MAIN SQUEEZE THEOREM FOR `S.G` (assuming `S.G` is connected):
    1. `numOrbits (geoPhi S.G) = |E(S.G)| - n + 2` (exact Euler formula!).
    2. `orbitToComp S.G` is a BIJECTION between `φ_G`-orbits and connected components of `T(G)`! -/
private lemma squeeze_bijection (hconn : S.G.Connected) :
    haveI := Classical.decRel S.G.Adj
    numOrbits (S.geoPhi S.G le_rfl) + n = S.G.edgeFinset.card + 2 ∧
    Function.Bijective (S.orbitToComp S.G le_rfl) := by
  classical
  obtain ⟨T, hTG, hTconn, hTedge⟩ := exists_spanning_tree S.G hconn
  have hTcard : (S.orientEdges T).card = T.edgeFinset.card := S.orientEdges_card T
  -- Induct on k = |(S.orientEdges H)| - |(S.orientEdges T)| for connected spanning subgraphs T ≤ H ≤ S.G
  suffices hind : ∀ k : ℕ, ∀ H : SimpleGraph (Fin n), ∀ (hHG : H ≤ S.G),
      T ≤ H → (S.orientEdges H).card = (S.orientEdges T).card + k →
      numOrbits (S.geoPhi H hHG) + n = (S.orientEdges H).card + 2 ∧
      Function.Bijective (S.orbitToComp H hHG) by
    have hle : T.edgeFinset.card ≤ S.G.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hTG)
    have hGe := S.orientEdges_card S.G
    have hres := hind ((S.orientEdges S.G).card - (S.orientEdges T).card) S.G le_rfl hTG (by omega)
    rw [hGe] at hres
    exact hres
  intro k
  induction k with
  | zero =>
    intro H hHG hTH hcard
    have hHT : H = T := by
      have hsub : T.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hTH
      have hHe := S.orientEdges_card H
      have heq : T.edgeFinset = H.edgeFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
      ext x y
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset, ← heq,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    subst hHT
    have hdegT : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card := by
      intro v
      rw [S.leftEdges_add_rightEdges_eq_degree H v]
      have hne : ∃ w : Fin n, w ≠ v := by
        by_cases h0 : v.val = 0
        · exact ⟨⟨1, by have := S.hn; omega⟩, fun h => by have hv1 : (1 : ℕ) = v.val := congrArg Fin.val h; omega⟩
        · exact ⟨⟨0, by have := S.hn; omega⟩, fun h => by have hv0 : (0 : ℕ) = v.val := congrArg Fin.val h; omega⟩
      obtain ⟨w, hw⟩ := hne
      obtain ⟨p⟩ := hTconn v w
      cases p with
      | nil => exact (hw rfl).elim
      | cons hvu _ =>
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨_, (H.mem_neighborFinset _ _).mpr hvu⟩
    have hneD : Nonempty (DartOf H) := by
      have h0 : 1 ≤ (S.leftEdges H ⟨0, by have := S.hn; omega⟩).card +
          (S.rightEdges H ⟨0, by have := S.hn; omega⟩).card := hdegT _
      rw [S.leftEdges_add_rightEdges_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree] at h0
      obtain ⟨u, hu⟩ := Finset.card_pos.mp h0
      exact ⟨⟨(⟨0, by have := S.hn; omega⟩, u), (H.mem_neighborFinset _ _).mp hu⟩⟩
    have hTn : H.edgeFinset.card + 1 = n := by
      have h := @hTedge _
      rwa [Fintype.card_fin] at h
    have horb1 : numOrbits (S.geoPhi H hHG) = 1 :=
      (numOrbits_eq_one_iff (S.geoPhi H hHG)).mpr
        (tree_one_orbit n (by have := S.hn; omega) (Fin n) H (S.geoSigma H hHG)
          (Fintype.card_fin n) hTconn hTn
          (fun v => S.geoSigma_isCyclic H hHG v))
    have hge := S.slab_components_ge H hHG hdegT
    have hle := S.slab_components_le_orbits H hHG hdegT
    have hE : (S.orientEdges H).card = H.edgeFinset.card := S.orientEdges_card H
    have hcomp_eq : Nat.card (S.slabGraph H).ConnectedComponent = numOrbits (S.geoPhi H hHG) := by
      omega
    refine ⟨by omega, ?_⟩
    unfold numOrbits at hcomp_eq
    haveI : Fintype (S.slabGraph H).ConnectedComponent := Fintype.ofFinite _
    haveI : Fintype (Quotient (orbitSetoid (S.geoPhi H hHG))) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcomp_eq
    exact (Fintype.bijective_iff_surjective_and_card (S.orbitToComp H hHG)).mpr
      ⟨S.orbitToComp_surjective H hHG hdegT, hcomp_eq.symm⟩
  | succ k ihk =>
    intro H hHG hTH hcard
    have hHe := S.orientEdges_card H
    have hdiff : (H.edgeFinset \ T.edgeFinset).Nonempty := by
      have hsub : T.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hTH
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      have : H.edgeFinset = T.edgeFinset := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hem) hsub
      have hcardEq : H.edgeFinset.card = T.edgeFinset.card := congrArg Finset.card this
      omega
    obtain ⟨e, he⟩ := hdiff
    obtain ⟨heH, heT⟩ := Finset.mem_sdiff.mp he
    induction e using Sym2.ind with | _ x y =>
    have hxy : H.Adj x y := H.mem_edgeFinset.mp heH
    have hne : x ≠ y := H.ne_of_adj hxy
    obtain ⟨a, b, hab, hab_eq⟩ : ∃ a b : Fin n, a < b ∧ s(a, b) = s(x, y) := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨x, y, h, rfl⟩
      · exact ⟨y, x, h, Sym2.eq_swap⟩
    let H0 := H.deleteEdges {s(a, b)}
    have hH0G : H0 ≤ S.G := (SimpleGraph.deleteEdges_le _).trans hHG
    have hTH0 : T ≤ H0 := by
      intro u v huv
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hTH huv, ?_⟩
      intro hmem
      have h : s(u, v) = s(a, b) := by simpa using hmem
      apply heT
      rw [← hab_eq, ← h]; exact T.mem_edgeFinset.mpr huv
    have hH0conn : H0.Connected := hTconn.mono hTH0
    have hH0e := S.orientEdges_card H0
    have hdel : (S.orientEdges H0).card + 1 = (S.orientEdges H).card := by
      rw [S.orientEdges_card H0, S.orientEdges_card H]
      convert deleteEdges_card H s(a, b) (hab_eq ▸ heH)
    have hH0card : (S.orientEdges H0).card = (S.orientEdges T).card + k := by omega
    have hIH := ihk H0 hH0G hTH0 hH0card
    have hab_G : S.G.Adj a b := hHG (H.mem_edgeFinset.mp (hab_eq ▸ heH))
    have hab_notH0 : ¬ H0.Adj a b := fun h => (SimpleGraph.deleteEdges_adj.mp h).2 (by simp)
    have hH_eq : H = H0 ⊔ SimpleGraph.fromEdgeSet {s(a, b)} := by
      ext u v
      simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
        SimpleGraph.fromEdgeSet_adj, H0]
      constructor
      · intro huv
        by_cases hs : s(u, v) = s(a, b)
        · exact Or.inr ⟨hs, H.ne_of_adj huv⟩
        · exact Or.inl ⟨huv, hs⟩
      · rintro (⟨huv, _⟩ | ⟨hs, _⟩)
        · exact huv
        · exact H.mem_edgeFinset.mp (hs ▸ hab_eq ▸ heH)
    have horb_step := S.add_edge_adds_one_orbit H0 hH0G hH0conn hIH.2 hab hab_G hab_notH0
    have hdegH : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card := by
      intro v
      rw [S.leftEdges_add_rightEdges_eq_degree H v]
      have hne' : ∃ w : Fin n, w ≠ v := by
        by_cases h0 : v.val = 0
        · exact ⟨⟨1, by have := S.hn; omega⟩, fun h => by have hv1 : (1 : ℕ) = v.val := congrArg Fin.val h; omega⟩
        · exact ⟨⟨0, by have := S.hn; omega⟩, fun h => by have hv0 : (0 : ℕ) = v.val := congrArg Fin.val h; omega⟩
      obtain ⟨w, hw⟩ := hne'
      obtain ⟨p⟩ := (hTconn.mono hTH) v w
      cases p with
      | nil => exact (hw rfl).elim
      | cons hvu _ =>
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨_, (H.mem_neighborFinset _ _).mpr hvu⟩
    have horb_H : numOrbits (S.geoPhi H hHG) = numOrbits (S.geoPhi H0 hH0G) + 1 := by
      convert (S.numOrbits_geoPhi_congr hHG _ hH_eq).trans horb_step
    have hIH1 : numOrbits (S.geoPhi H0 hH0G) + n = (S.orientEdges H0).card + 2 := by
      convert hIH.1
    have horb_eq : numOrbits (S.geoPhi H hHG) + n = (S.orientEdges H).card + 2 := by
      rw [horb_H, ← hdel, add_right_comm, hIH1, add_right_comm]
    have hge := S.slab_components_ge H hHG hdegH
    have hle := S.slab_components_le_orbits H hHG hdegH
    have hcomp_eq : Nat.card (S.slabGraph H).ConnectedComponent = numOrbits (S.geoPhi H hHG) :=
      le_antisymm hle (Nat.le_of_add_le_add_right (horb_eq.symm ▸ hge))
    refine ⟨horb_eq, ?_⟩
    unfold numOrbits at hcomp_eq
    haveI : Fintype (S.slabGraph H).ConnectedComponent := Fintype.ofFinite _
    haveI : Fintype (Quotient (orbitSetoid (S.geoPhi H hHG))) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcomp_eq
    exact (Fintype.bijective_iff_surjective_and_card (S.orbitToComp H hHG)).mpr
      ⟨S.orbitToComp_surjective H hHG hdegH, hcomp_eq.symm⟩

end GeoSetup

end SlabAndSqueeze

/- ## Section 5: Harborth Inequalities (A) & (B) and Strong Induction -/

section HarborthCore

/-- Unit-distance graph on a finite subset `S : Finset ℂ`. -/
private def unitGraph (S : Finset ℂ) : SimpleGraph {z : ℂ // z ∈ S} where
  Adj x y := ‖x.1 - y.1‖ = 1
  symm := ⟨fun x y h => by rwa [norm_sub_rev]⟩
  loopless := ⟨fun x h => by simp at h⟩

private noncomputable def edgeCount (S : Finset ℂ) : ℕ := by
  classical
  exact (unitGraph S).edgeFinset.card

private lemma unitGraph_deg_le_six (S : Finset ℂ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (v : {z : ℂ // z ∈ S}) :
    haveI := Classical.decRel (unitGraph S).Adj
    (unitGraph S).degree v ≤ 6 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact unit_neighbors_le_six ((unitGraph S).neighborFinset v) (fun u => u.1 - v.1)
    (fun u hu => by rw [norm_sub_rev]; exact ((unitGraph S).mem_neighborFinset _ _).mp hu)
    (fun u _ w _ huw => by
      rw [sub_sub_sub_cancel_right]
      exact hsep u.1 u.2 w.1 w.2 (fun h => huw (Subtype.ext h)))

private lemma edgeCount_le_three_mul (S : Finset ℂ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    edgeCount S ≤ 3 * S.card := by
  classical
  have hsum : ∑ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v ≤ 6 * S.card := by
    calc ∑ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v
        ≤ ∑ _ : {z : ℂ // z ∈ S}, (6 : ℕ) :=
          Finset.sum_le_sum (fun v _ => unitGraph_deg_le_six S hsep v)
      _ = 6 * Fintype.card {z : ℂ // z ∈ S} := by simp [mul_comm]
      _ = 6 * S.card := by rw [Fintype.card_coe]
  rw [(unitGraph S).sum_degrees_eq_twice_card_edges] at hsum
  unfold edgeCount
  omega

open Classical in
private lemma sum_degree_eq_touching_add_internal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) :
    (G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ B)).card +
      (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B)).card =
      ∑ v ∈ B, G.degree v := by
  have hlhs : ∑ e ∈ G.edgeFinset, (B.filter (fun v => v ∈ e)).card =
      (G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ B)).card +
      (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B)).card := by
    have hterm : ∀ e ∈ G.edgeFinset,
        (B.filter (fun v => v ∈ e)).card =
          (if ∃ v ∈ e, v ∈ B then 1 else 0) + (if ∀ v ∈ e, v ∈ B then 1 else 0) := by
      intro e he
      induction e using Sym2.ind with | _ x y =>
      have hne : x ≠ y := G.ne_of_adj (G.mem_edgeFinset.mp he)
      by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
      · have hf : B.filter (fun v => v ∈ s(x, y)) = {x, y} := by
          ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨by rcases h with rfl | rfl <;> assumption, h⟩⟩
        rw [hf, Finset.card_pair hne, if_pos ⟨x, Sym2.mem_mk_left x y, hx⟩,
          if_pos (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)]
      · have hf : B.filter (fun v => v ∈ s(x, y)) = {x} := by
          ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
          exact ⟨fun ⟨hv, h⟩ => h.resolve_right (fun hvy => hy (hvy ▸ hv)),
            fun h => ⟨h ▸ hx, Or.inl h⟩⟩
        rw [hf, Finset.card_singleton, if_pos ⟨x, Sym2.mem_mk_left x y, hx⟩,
          if_neg (fun h => hy (h y (Sym2.mem_mk_right x y)))]
      · have hf : B.filter (fun v => v ∈ s(x, y)) = {y} := by
          ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
          exact ⟨fun ⟨hv, h⟩ => h.resolve_left (fun hvx => hx (hvx ▸ hv)),
            fun h => ⟨h ▸ hy, Or.inr h⟩⟩
        rw [hf, Finset.card_singleton, if_pos ⟨y, Sym2.mem_mk_right x y, hy⟩,
          if_neg (fun h => hx (h x (Sym2.mem_mk_left x y)))]
      · have hf : B.filter (fun v => v ∈ s(x, y)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro v hv hmem
          rcases Sym2.mem_iff.mp hmem with rfl | rfl <;> contradiction
        rw [hf, Finset.card_empty,
          if_neg (by rintro ⟨v, hv, hvB⟩; rcases Sym2.mem_iff.mp hv with rfl | rfl <;> contradiction),
          if_neg (fun h => hx (h x (Sym2.mem_mk_left x y)))]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    simp only [Finset.sum_boole, Nat.cast_id]
  have hrhs : ∑ e ∈ G.edgeFinset, (B.filter (fun v => v ∈ e)).card =
      ∑ v ∈ B, G.degree v := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.card_filter, ← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij
      (fun (e : Sym2 V) he => Classical.choose (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp he).2)) ?_ ?_ ?_
    · intro e he
      have hspec := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp he).2)
      have hadj : G.Adj v _ := G.mem_edgeFinset.mp (hspec ▸ (Finset.mem_filter.mp he).1)
      exact (G.mem_neighborFinset _ _).mpr hadj
    · intro e₁ h1 e₂ h2 hw
      have hs1 := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp h1).2)
      have hs2 := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp h2).2)
      rw [hs1, hs2, hw]
    · intro u hu
      have hadj : G.Adj v u := (G.mem_neighborFinset _ _).mp hu
      refine ⟨s(v, u), Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr hadj, Sym2.mem_mk_left v u⟩, ?_⟩
      have hspec := Classical.choose_spec (Sym2.mem_iff_exists.mp (Sym2.mem_mk_left v u))
      rcases Sym2.eq_iff.mp hspec.symm with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact (G.loopless.irrefl v (h ▸ hadj)).elim
  exact hlhs.symm.trans hrhs

/-- Key geometric step: for any connected 1-separated `S : Finset ℂ` with `|S| ≥ 4` and
    minimum degree `≥ 3`, there exists a subset `B ⊆ S` with `3 ≤ B.card` satisfying:
    - (A) `B.card + 3 ≤ 3 * S.card - edgeCount S`
    - (B) `edgeCount S ≤ edgeCount (S \ B) + 3 * B.card - 6`! -/
private lemma exists_boundary_subset (S : Finset ℂ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖)
    (hn4 : 4 ≤ S.card)
    (hconn : (unitGraph S).Connected)
    (hmin3 : ∀ v : {z : ℂ // z ∈ S}, haveI := Classical.decRel (unitGraph S).Adj; 3 ≤ (unitGraph S).degree v) :
    ∃ B : Finset ℂ, B ⊆ S ∧ 3 ≤ B.card ∧
      B.card + 3 ≤ 3 * S.card - edgeCount S ∧
      edgeCount S ≤ edgeCount (S \ B) + 3 * B.card - 6 := by
  classical
  -- Step 1: Rotate S by a generic unit complex number ω so all real parts are distinct!
  obtain ⟨ω, hω_norm, hω_re⟩ := exists_generic_unit_rot S
  have hω_ne : ω ≠ 0 := fun h => by simp [h] at hω_norm
  let rot (z : ℂ) : ℂ := ω * z
  have hrot_dist : ∀ x y : ℂ, ‖rot x - rot y‖ = ‖x - y‖ := by
    intro x y; dsimp [rot]; rw [← mul_sub, norm_mul, hω_norm, one_mul]
  let n := S.card
  let xs := S.image (fun z => (rot z).re)
  have hxs_inj : Set.InjOn (fun z => (rot z).re) ↑S := by
    intro x hx y hy hxy
    by_contra hne
    exact hω_re x hx y hy hne hxy
  have hxs_card : xs.card = n := Finset.card_image_of_injOn hxs_inj
  let embX := xs.orderEmbOfFin hxs_card
  have hex_pt : ∀ i : Fin n, ∃ z ∈ S, (rot z).re = embX i :=
    fun i => Finset.mem_image.mp (xs.orderEmbOfFin_mem hxs_card i)
  let pt : Fin n → ℂ := fun i => Classical.choose (hex_pt i)
  have hpt_mem : ∀ i : Fin n, pt i ∈ S := fun i => (Classical.choose_spec (hex_pt i)).1
  have hpt_re : ∀ i : Fin n, (rot (pt i)).re = embX i := fun i => (Classical.choose_spec (hex_pt i)).2
  have hpt_inj : Function.Injective pt := fun i j h =>
    embX.injective ((hpt_re i).symm.trans ((congrArg (fun z => (rot z).re) h).trans (hpt_re j)))
  have hpt_bij : Function.Bijective (fun i : Fin n => (⟨pt i, hpt_mem i⟩ : {z : ℂ // z ∈ S})) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j h => hpt_inj (congrArg Subtype.val h), by simp [n]⟩
  let eqV : Fin n ≃ {z : ℂ // z ∈ S} := Equiv.ofBijective _ hpt_bij
  -- Build GeoSetup n using p i := rot (pt i)
  let Gsetup : GeoSetup n :=
    { hn := hn4
      p := fun i => rot (pt i)
      hx_mono := fun i j hij => by dsimp only; rw [hpt_re i, hpt_re j]; exact embX.strictMono hij
      hsep := fun i j hij => by
        rw [hrot_dist]; exact hsep (pt i) (hpt_mem i) (pt j) (hpt_mem j) (hpt_inj.ne hij) }
  -- Graph isomorphism Gsetup.G ≃g unitGraph S via eqV
  let iso : Gsetup.G ≃g unitGraph S :=
    { toEquiv := eqV
      map_rel_iff' := by
        intro i j
        change ‖pt i - pt j‖ = 1 ↔ ‖rot (pt i) - rot (pt j)‖ = 1
        rw [hrot_dist] }
  have hGconn : Gsetup.G.Connected := iso.symm.connected_iff.mp hconn
  have hGmin3 : ∀ v : Fin n, 3 ≤ Gsetup.G.degree v := fun v => by
    rw [← iso.degree_eq v]; exact hmin3 (eqV v)
  have hGedge : Gsetup.G.edgeFinset.card = edgeCount S := by
    unfold edgeCount
    refine Finset.card_bij (fun e _ => Sym2.map eqV e) ?_ ?_ ?_
    · intro e he; induction e using Sym2.ind with | _ i j =>
      exact (unitGraph S).mem_edgeFinset.mpr (iso.map_adj_iff.mpr (Gsetup.G.mem_edgeFinset.mp he))
    · intro e₁ _ e₂ _ h; exact Sym2.map.injective eqV.injective h
    · intro e he; induction e using Sym2.ind with | _ x y =>
      refine ⟨s(eqV.symm x, eqV.symm y), Gsetup.G.mem_edgeFinset.mpr ?_, by simp⟩
      exact iso.symm.map_adj_iff.mpr ((unitGraph S).mem_edgeFinset.mp he)
  -- Step 2: Apply the Squeeze Theorem to Gsetup!
  obtain ⟨hEuler, hbij⟩ := Gsetup.squeeze_bijection hGconn
  -- Let c_out be the outer connected component of T(G), and C_out be the UNIQUE φ_G-orbit mapping to c_out!
  let c_out : (Gsetup.slabGraph Gsetup.G).ConnectedComponent :=
    (Gsetup.slabGraph Gsetup.G).connectedComponentMk (Gsetup.outerVert Gsetup.G)
  let C_out : Finset (DartOf Gsetup.G) :=
    Finset.univ.filter (fun d => (Gsetup.slabGraph Gsetup.G).connectedComponentMk (Gsetup.dartMap Gsetup.G d) = c_out)
  -- C_out is a SINGLE φ_G-orbit (because orbitToComp is bijective!)
  have hCout_same : ∀ d₁ ∈ C_out, ∀ d₂ ∈ C_out, sameOrbit (Gsetup.geoPhi Gsetup.G le_rfl) d₁ d₂ := by
    intro d₁ h1 d₂ h2
    have h1' : Gsetup.orbitToComp Gsetup.G le_rfl (Quotient.mk _ d₁) = c_out := (Finset.mem_filter.mp h1).2
    have h2' : Gsetup.orbitToComp Gsetup.G le_rfl (Quotient.mk _ d₂) = c_out := (Finset.mem_filter.mp h2).2
    exact Quotient.exact (hbij.1 (h1'.trans h2'.symm))
  have hCout_inv : ∀ d ∈ C_out, Gsetup.geoPhi Gsetup.G le_rfl d ∈ C_out := by
    intro d hd
    simp only [C_out, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact (SimpleGraph.ConnectedComponent.sound (Gsetup.dartMap_phi_reachable Gsetup.G le_rfl d)).symm.trans hd
  have hCout_ne : C_out.Nonempty := by
    obtain ⟨q, hq⟩ := hbij.2 c_out
    induction q using Quotient.ind with | _ d =>
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
  have hdegG : ∀ v : Fin n, 1 ≤ (Gsetup.leftEdges Gsetup.G v).card + (Gsetup.rightEdges Gsetup.G v).card := by
    intro v; rw [Gsetup.leftEdges_add_rightEdges_eq_degree]; have := hGmin3 v; omega
  -- Step 3: Angle sum on C_out ≥ (L + 2) * π!
  let L := C_out.card
  have hangle_out : ((L : ℝ) + 2) * Real.pi ≤ ∑ d ∈ C_out, Gsetup.gapAngle Gsetup.G le_rfl d := by
    rw [Gsetup.invariant_set_angle_sum Gsetup.G le_rfl C_out hCout_inv]
    have hturn := Gsetup.component_turning_identity Gsetup.G le_rfl hdegG c_out
    have hFout_eq : Finset.univ.filter (fun t => (Gsetup.slabGraph Gsetup.G).connectedComponentMk t = c_out) =
        Finset.univ.filter (fun t => (Gsetup.slabGraph Gsetup.G).Reachable (Gsetup.outerVert Gsetup.G) t) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, c_out,
        SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
    have hVleE := Gsetup.slab_outer_component_V_le_E Gsetup.G le_rfl hdegG
    have houter_in : Gsetup.outerVert Gsetup.G ∈
        Finset.univ.filter (fun t => (Gsetup.slabGraph Gsetup.G).connectedComponentMk t = c_out) := by
      simp [c_out]
    dsimp only at hturn hVleE
    rw [if_pos houter_in, hFout_eq] at hturn
    change ((C_out.filter (Gsetup.isLeftTip Gsetup.G)).card : ℤ) -
      ((C_out.filter (Gsetup.isRightCap Gsetup.G)).card : ℤ) = _ at hturn
    have hw_le : ((C_out.filter (Gsetup.isLeftTip Gsetup.G)).card : ℤ) -
        ((C_out.filter (Gsetup.isRightCap Gsetup.G)).card : ℤ) ≤ -1 := by omega
    have hw_real : ((C_out.filter (Gsetup.isLeftTip Gsetup.G)).card : ℝ) -
        ((C_out.filter (Gsetup.isRightCap Gsetup.G)).card : ℝ) ≤ -1 := by
      exact_mod_cast hw_le
    nlinarith [Real.pi_pos]
  -- Helper: every vertex of Gsetup.G has at least 2 distinct neighbors
  have hGdeg2 : ∀ v : Fin n, ∃ u₁ u₂ : Fin n, Gsetup.G.Adj v u₁ ∧ Gsetup.G.Adj v u₂ ∧ u₁ ≠ u₂ := by
    intro v
    have hdeg := hGmin3 v
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) hdeg)
    exact ⟨u₁, u₂, (Gsetup.G.mem_neighborFinset _ _).mp hu₁, (Gsetup.G.mem_neighborFinset _ _).mp hu₂, hne⟩
  -- Step 4: Every φ_G-orbit has size ≥ 3 (since deg ≥ 3 => σ_v(u) ≠ u)!
  have horb_ge3 : ∀ q : Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)),
      3 ≤ (Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)).card := by
    intro q
    induction q using Quotient.ind with | _ d =>
    let d1 := Gsetup.geoPhi Gsetup.G le_rfl d
    let d2 := Gsetup.geoPhi Gsetup.G le_rfl d1
    have hne01 : d ≠ d1 := fun h => Gsetup.G.loopless.irrefl d.1.1 ((congrArg (fun x : DartOf Gsetup.G => x.1.1) h).symm ▸ d.2)
    have hne12 : d1 ≠ d2 := fun h => Gsetup.G.loopless.irrefl d1.1.1 ((congrArg (fun x : DartOf Gsetup.G => x.1.1) h).symm ▸ d1.2)
    have hne02 : d ≠ d2 := by
      intro h
      have h1 : d.1.1 = d2.1.1 := congrArg (fun x : DartOf Gsetup.G => x.1.1) h
      have hfix : Gsetup.geoSigma Gsetup.G le_rfl d.1.2 ⟨d.1.1, d.2.symm⟩ = ⟨d.1.1, d.2.symm⟩ :=
        Subtype.ext h1.symm
      exact Gsetup.geoSigma_ne_self Gsetup.G le_rfl d.1.2 (hGdeg2 d.1.2) ⟨d.1.1, d.2.symm⟩ hfix
    have hsub : ({d, d1, d2} : Finset (DartOf Gsetup.G)) ⊆
        Finset.univ.filter (fun x : DartOf Gsetup.G => Quotient.mk (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)) x = Quotient.mk _ d) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl
      · rfl
      · exact Quotient.sound (sameOrbit_symm _ (sameOrbit_step _ d))
      · exact Quotient.sound (sameOrbit_symm _ (sameOrbit_trans _ (sameOrbit_step _ d) (sameOrbit_step _ d1)))
    have h3 : ({d, d1, d2} : Finset (DartOf Gsetup.G)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne12]
      · simp [hne01, hne02]
    exact h3 ▸ Finset.card_le_card hsub
  -- Inequality (A'): L + 3 ≤ 3 * n - e!
  have hineqA_L : L + 3 ≤ 3 * n - Gsetup.G.edgeFinset.card := by
    letI := Fintype.ofFinite (Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)))
    let q_out : Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)) :=
      Quotient.mk _ hCout_ne.choose
    have hq_out_eq : Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q_out) = C_out := by
      ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, q_out]
      constructor
      · intro h
        have hcomp : Gsetup.orbitToComp Gsetup.G le_rfl (Quotient.mk _ d) =
            Gsetup.orbitToComp Gsetup.G le_rfl (Quotient.mk _ hCout_ne.choose) := congrArg _ h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp.trans (Finset.mem_filter.mp hCout_ne.choose_spec).2⟩
      · intro hd; exact Quotient.sound (hCout_same d hd hCout_ne.choose hCout_ne.choose_spec)
    have htot : ∑ q : Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)),
        (Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)).card =
        2 * Gsetup.G.edgeFinset.card := by
      rw [← Finset.card_biUnion]
      · have hall : Finset.univ.biUnion (fun q : Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)) =>
            Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)) = Finset.univ := by
          ext d; simp
        rw [hall, Finset.card_univ]
        have hcard_d : Fintype.card (DartOf Gsetup.G) = ∑ v : Fin n, Gsetup.G.degree v := by
          have e : DartOf Gsetup.G ≃ Σ v : Fin n, {u : Fin n // Gsetup.G.Adj v u} :=
            ⟨fun d => ⟨d.1.2, ⟨d.1.1, d.2.symm⟩⟩, fun p => ⟨(p.2.1, p.1), p.2.2.symm⟩,
              fun d => by rcases d with ⟨⟨_, _⟩, _⟩; rfl,
              fun p => by rcases p with ⟨_, ⟨_, _⟩⟩; rfl⟩
          rw [Fintype.card_congr e, Fintype.card_sigma]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Fintype.card_coe]
          exact Fintype.card_congr ⟨fun u => ⟨u.1, (Gsetup.G.mem_neighborFinset _ _).mpr u.2⟩,
            fun u => ⟨u.1, (Gsetup.G.mem_neighborFinset _ _).mp u.2⟩, fun _ => rfl, fun _ => rfl⟩
        rw [hcard_d, Gsetup.G.sum_degrees_eq_twice_card_edges]
      · intro q₁ _ q₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro d h1 h2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact hne (h1.symm.trans h2)
    have hsplit : ∑ q : Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl)),
        (Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)).card =
        L + ∑ q ∈ Finset.univ.erase q_out,
          (Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)).card := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q_out), hq_out_eq]
    have hrest : 3 * (numOrbits (Gsetup.geoPhi Gsetup.G le_rfl) - 1) ≤
        ∑ q ∈ Finset.univ.erase q_out,
          (Finset.univ.filter (fun d : DartOf Gsetup.G => Quotient.mk _ d = q)).card := by
      calc 3 * (numOrbits (Gsetup.geoPhi Gsetup.G le_rfl) - 1)
          = ∑ _ ∈ Finset.univ.erase q_out, (3 : ℕ) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              nsmul_eq_mul, Nat.cast_id, mul_comm, numOrbits, Nat.card_eq_fintype_card]
        _ ≤ _ := Finset.sum_le_sum (fun q _ => horb_ge3 q)
    have h1orb : 1 ≤ numOrbits (Gsetup.geoPhi Gsetup.G le_rfl) := by
      have : 0 < Fintype.card (Quotient (orbitSetoid (Gsetup.geoPhi Gsetup.G le_rfl))) :=
        Fintype.card_pos_iff.mpr ⟨q_out⟩
      rw [numOrbits, Nat.card_eq_fintype_card]
      exact this
    omega
  -- Step 5: Define B_idx = C_out.image (·.1.2) ⊆ Fin n, and B = B_idx.image pt ⊆ S!
  let B_idx : Finset (Fin n) := C_out.image (fun d => d.1.2)
  let b := B_idx.card
  have hb_le_L : b ≤ L := Finset.card_image_le
  -- b ≥ 3: pick d ∈ C_out, d1 = φ d, d2 = φ d1; their targets (u, v, w) are 3 distinct vertices in B_idx!
  have hb_ge3 : 3 ≤ b := by
    obtain ⟨d, hd⟩ := hCout_ne
    let d1 := Gsetup.geoPhi Gsetup.G le_rfl d
    let d2 := Gsetup.geoPhi Gsetup.G le_rfl d1
    have hd1 : d1 ∈ C_out := hCout_inv d hd
    have hd2 : d2 ∈ C_out := hCout_inv d1 hd1
    have hv1 : d.1.1 ∈ B_idx := by
      -- Since C_out is finite and φ-bijective, d = φ(d_prev) for some d_prev ∈ C_out whose target is d.1.1!
      have hsurj : Finset.image (Gsetup.geoPhi Gsetup.G le_rfl) C_out = C_out :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => by obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hCout_inv y hy)
          (by rw [Finset.card_image_of_injective _ (Gsetup.geoPhi Gsetup.G le_rfl).injective])
      have hmem : d ∈ Finset.image (Gsetup.geoPhi Gsetup.G le_rfl) C_out := hsurj.symm ▸ hd
      obtain ⟨dp, hdp, hdp_eq⟩ := Finset.mem_image.mp hmem
      have : dp.1.2 = d.1.1 := congrArg (fun x : DartOf Gsetup.G => x.1.1) hdp_eq
      exact this ▸ Finset.mem_image_of_mem _ hdp
    have hv2 : d.1.2 ∈ B_idx := Finset.mem_image_of_mem _ hd
    have hv3 : d1.1.2 ∈ B_idx := Finset.mem_image_of_mem _ hd1
    have hne12 : d.1.1 ≠ d.1.2 := Gsetup.G.ne_of_adj d.2
    have hne23 : d.1.2 ≠ d1.1.2 := Gsetup.G.ne_of_adj d1.2
    have hne13 : d.1.1 ≠ d1.1.2 := by
      intro heq
      have hfix : Gsetup.geoSigma Gsetup.G le_rfl d.1.2 ⟨d.1.1, d.2.symm⟩ = ⟨d.1.1, d.2.symm⟩ :=
        Subtype.ext heq.symm
      exact Gsetup.geoSigma_ne_self Gsetup.G le_rfl d.1.2 (hGdeg2 d.1.2) ⟨d.1.1, d.2.symm⟩ hfix
    have hsub : ({d.1.1, d.1.2, d1.1.2} : Finset (Fin n)) ⊆ B_idx := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3 : ({d.1.1, d.1.2, d1.1.2} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne23]
      · simp [hne12, hne13]
    exact h3 ▸ Finset.card_le_card hsub
  -- Step 6: Degree sum over B_idx: ∑_{v ∈ B_idx} deg_G(v) ≤ 6 * b - 2 * L - 6!
  have hdeg_sum_B : ∑ v ∈ B_idx, Gsetup.G.degree v + 2 * L + 6 ≤ 6 * b := by
    have hper_v : ∀ v ∈ B_idx,
        let C_v := C_out.filter (fun d => d.1.2 = v)
        ((Gsetup.G.degree v : ℝ) - (C_v.card : ℝ)) * (Real.pi / 3) +
          ∑ d ∈ C_v, Gsetup.gapAngle Gsetup.G le_rfl d ≤ 2 * Real.pi := by
      intro v _
      dsimp only
      let Nv := (Finset.univ : Finset {u : Fin n // Gsetup.G.Adj v u})
      let Cv_sub : Finset {u : Fin n // Gsetup.G.Adj v u} :=
        Nv.filter (fun u => (⟨(u.1, v), u.2.symm⟩ : DartOf Gsetup.G) ∈ C_out)
      have hcard_Nv : Nv.card = Gsetup.G.degree v := by
        rw [Finset.card_univ, ← SimpleGraph.card_neighborFinset_eq_degree, ← Fintype.card_coe]
        exact Fintype.card_congr ⟨fun u => ⟨u.1, (Gsetup.G.mem_neighborFinset _ _).mpr u.2⟩,
          fun u => ⟨u.1, (Gsetup.G.mem_neighborFinset _ _).mp u.2⟩, fun _ => rfl, fun _ => rfl⟩
      have hcard_Cv : Cv_sub.card = (C_out.filter (fun d => d.1.2 = v)).card := by
        refine Finset.card_bij (fun u _ => ⟨(u.1, v), u.2.symm⟩) ?_ ?_ ?_
        · intro u hu; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, rfl⟩
        · intro u₁ _ u₂ _ h; exact Subtype.ext (congrArg (fun d : DartOf Gsetup.G => d.1.1) h)
        · intro d hd; obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
          refine ⟨⟨d.1.1, hd2 ▸ d.2.symm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rcases d with ⟨⟨u, w⟩, hadj⟩; dsimp at hd2; subst hd2; exact hd1
          · rcases d with ⟨⟨u, w⟩, hadj⟩; dsimp at hd2; subst hd2; rfl
      have hsum_Cv : ∑ u ∈ Cv_sub, Gsetup.gapAngle Gsetup.G le_rfl ⟨(u.1, v), u.2.symm⟩ =
          ∑ d ∈ C_out.filter (fun d => d.1.2 = v), Gsetup.gapAngle Gsetup.G le_rfl d := by
        refine Finset.sum_bij (fun u _ => ⟨(u.1, v), u.2.symm⟩) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro u hu; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, rfl⟩
        · intro u₁ _ u₂ _ h; exact Subtype.ext (congrArg (fun d : DartOf Gsetup.G => d.1.1) h)
        · intro d hd; obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
          refine ⟨⟨d.1.1, hd2 ▸ d.2.symm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rcases d with ⟨⟨u, w⟩, hadj⟩; dsimp at hd2; subst hd2; exact hd1
          · rcases d with ⟨⟨u, w⟩, hadj⟩; dsimp at hd2; subst hd2; rfl
      have hsum_all := Gsetup.gapAngle_sum_at_vertex Gsetup.G le_rfl v (by
        obtain ⟨u₁, _, hu₁, _, _⟩ := hGdeg2 v; exact ⟨u₁, hu₁⟩)
      have hsplit : ∑ u ∈ Nv \ Cv_sub, Gsetup.gapAngle Gsetup.G le_rfl ⟨(u.1, v), u.2.symm⟩ +
          ∑ u ∈ Cv_sub, Gsetup.gapAngle Gsetup.G le_rfl ⟨(u.1, v), u.2.symm⟩ = 2 * Real.pi := by
        rw [Finset.sum_sdiff (Finset.filter_subset _ _)]; exact hsum_all
      have hrest_ge : ((Nv \ Cv_sub).card : ℝ) * (Real.pi / 3) ≤
          ∑ u ∈ Nv \ Cv_sub, Gsetup.gapAngle Gsetup.G le_rfl ⟨(u.1, v), u.2.symm⟩ := by
        calc ((Nv \ Cv_sub).card : ℝ) * (Real.pi / 3)
            = ∑ _ ∈ Nv \ Cv_sub, (Real.pi / 3) := by simp
          _ ≤ _ := Finset.sum_le_sum (fun u _ => Gsetup.gapAngle_ge_pi_div_three Gsetup.G le_rfl _)
      have hcard_sdiff : (Nv \ Cv_sub).card = Gsetup.G.degree v - (C_out.filter (fun d => d.1.2 = v)).card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hcard_Nv, hcard_Cv]
      have hle_deg : (C_out.filter (fun d => d.1.2 = v)).card ≤ Gsetup.G.degree v := by
        rw [← hcard_Cv, ← hcard_Nv]; exact Finset.card_le_card (Finset.filter_subset _ _)
      rw [hsum_Cv] at hsplit
      rw [hcard_sdiff, Nat.cast_sub hle_deg] at hrest_ge
      linarith
    have hsum_B := Finset.sum_le_sum hper_v
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_B
    have hsum_k : ∑ v ∈ B_idx, (C_out.filter (fun d => d.1.2 = v)).card = L := by
      rw [← Finset.card_biUnion]
      · congr 1; ext d; simp only [Finset.mem_biUnion, Finset.mem_filter, B_idx, Finset.mem_image]
        exact ⟨fun ⟨_, _, hd, _⟩ => hd, fun hd => ⟨d.1.2, ⟨d, hd, rfl⟩, hd, rfl⟩⟩
      · intro v₁ _ v₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro d h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hsum_ang : ∑ v ∈ B_idx, ∑ d ∈ C_out.filter (fun d => d.1.2 = v), Gsetup.gapAngle Gsetup.G le_rfl d =
        ∑ d ∈ C_out, Gsetup.gapAngle Gsetup.G le_rfl d := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext d; simp only [Finset.mem_biUnion, Finset.mem_filter, B_idx, Finset.mem_image]
        exact ⟨fun ⟨_, _, hd, _⟩ => hd, fun hd => ⟨d.1.2, ⟨d, hd, rfl⟩, hd, rfl⟩⟩
      · intro v₁ _ v₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro d h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hsum_ang, ← Finset.sum_mul, Finset.sum_sub_distrib] at hsum_B
    have hsum_kR : (∑ v ∈ B_idx, ((C_out.filter (fun d => d.1.2 = v)).card : ℝ)) = (L : ℝ) := by
      exact_mod_cast hsum_k
    rw [hsum_kR] at hsum_B
    have hreal : ((∑ v ∈ B_idx, Gsetup.G.degree v : ℕ) : ℝ) + 2 * (L : ℝ) + 6 ≤ 6 * (b : ℝ) := by
      have hcast : (∑ v ∈ B_idx, (Gsetup.G.degree v : ℝ)) = ((∑ v ∈ B_idx, Gsetup.G.degree v : ℕ) : ℝ) := by
        push_cast; rfl
      rw [hcast] at hsum_B
      nlinarith [Real.pi_pos, hangle_out]
    exact_mod_cast hreal
  -- Step 7: Distinct undirected edges E_out of C_out!
  let E_out : Finset (Sym2 (Fin n)) := C_out.image (fun d => s(d.1.1, d.1.2))
  -- Every e ∈ E_out is in Gsetup.G.edgeFinset with both endpoints in B_idx!
  have hEout_sub : E_out ⊆ Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B_idx) := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨Gsetup.G.mem_edgeFinset.mpr d.2, fun v hv => ?_⟩
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · have hsurj : Finset.image (Gsetup.geoPhi Gsetup.G le_rfl) C_out = C_out :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => by obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hCout_inv y hy)
          (by rw [Finset.card_image_of_injective _ (Gsetup.geoPhi Gsetup.G le_rfl).injective])
      obtain ⟨dp, hdp, hdp_eq⟩ := Finset.mem_image.mp (hsurj.symm ▸ hd)
      have : dp.1.2 = d.1.1 := congrArg (fun x : DartOf Gsetup.G => x.1.1) hdp_eq
      exact this ▸ Finset.mem_image_of_mem _ hdp
    · exact Finset.mem_image_of_mem _ hd
  -- Lower bound on E_out.card: ≥ b - 1 always (connected graph on B_idx), and = b if L = b!
  have hEout_ge : b - 1 ≤ E_out.card := by
    -- Build SimpleGraph H_out on {v // v ∈ B_idx} with edges from E_out
    let H_out : SimpleGraph {v : Fin n // v ∈ B_idx} :=
      { Adj := fun x y => s(x.1, y.1) ∈ E_out
        symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩
        loopless := ⟨fun x h => by
          obtain ⟨d, _, hd⟩ := Finset.mem_image.mp h
          rcases Sym2.eq_iff.mp hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Gsetup.G.loopless.irrefl d.1.2 ((h1.trans h2.symm) ▸ d.2)
          · exact Gsetup.G.loopless.irrefl d.1.2 ((h1.trans h2.symm) ▸ d.2)⟩ }
    have hHout_conn : H_out.Connected := by
      obtain ⟨d₀, hd₀⟩ := hCout_ne
      refine @SimpleGraph.Connected.mk _ _ (fun x y => ?_) ⟨⟨d₀.1.2, Finset.mem_image_of_mem _ hd₀⟩⟩
      obtain ⟨dx, hdx, hxv⟩ := Finset.mem_image.mp x.2
      obtain ⟨dy, hdy, hyv⟩ := Finset.mem_image.mp y.2
      obtain ⟨k, hk⟩ := hCout_same dx hdx dy hdy
      have hwalk : ∀ (m : ℕ) (d : DartOf Gsetup.G) (hd : d ∈ C_out),
          H_out.Reachable ⟨d.1.2, Finset.mem_image_of_mem _ hd⟩
            ⟨((Gsetup.geoPhi Gsetup.G le_rfl ^ m) d).1.2, Finset.mem_image_of_mem _ (by
              clear hk
              induction m with
              | zero => exact hd
              | succ m ihm => rw [pow_succ', Equiv.Perm.mul_apply]; exact hCout_inv _ ihm)⟩ := by
        intro m; induction m with
        | zero => intro d hd; exact SimpleGraph.Reachable.refl _
        | succ m ihm =>
          intro d hd
          have hd' : Gsetup.geoPhi Gsetup.G le_rfl d ∈ C_out := hCout_inv d hd
          have hstep : H_out.Adj ⟨d.1.2, Finset.mem_image_of_mem _ hd⟩
              ⟨(Gsetup.geoPhi Gsetup.G le_rfl d).1.2, Finset.mem_image_of_mem _ hd'⟩ :=
            Finset.mem_image.mpr ⟨Gsetup.geoPhi Gsetup.G le_rfl d, hd', rfl⟩
          have hrest := ihm (Gsetup.geoPhi Gsetup.G le_rfl d) hd'
          convert hstep.reachable.trans hrest using 2
          rw [pow_add, pow_one, Equiv.Perm.mul_apply]
      have hw := hwalk k dx hdx
      convert hw using 1
      · exact Subtype.ext hxv.symm
      · exact Subtype.ext (by dsimp only; rw [hk, hyv])
    have hle := card_le_edges_add_one_of_connected H_out hHout_conn
    rw [Fintype.card_coe] at hle
    have hEcard : H_out.edgeFinset.card ≤ E_out.card := by
      let emb : Sym2 {v : Fin n // v ∈ B_idx} ↪ Sym2 (Fin n) := (Function.Embedding.subtype _).sym2Map
      rw [← Finset.card_map emb]
      refine Finset.card_le_card (fun e he => ?_)
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
      induction e' using Sym2.ind with | _ x y =>
      exact H_out.mem_edgeFinset.mp he'
    omega
  have hEout_eq_if : L = b → E_out.card = b := by
    intro hLb
    -- When L = b, every v ∈ B_idx has exactly 1 incoming dart in C_out, hence 1 outgoing dart too,
    -- so d ↦ s(d.1.1, d.1.2) is injective on C_out!
    have hinj_snd : Set.InjOn (fun d : DartOf Gsetup.G => d.1.2) ↑C_out := by
      exact Finset.injOn_of_card_image_eq hLb.symm
    have hinj_fst : Set.InjOn (fun d : DartOf Gsetup.G => d.1.1) ↑C_out := by
      intro d₁ h1 d₂ h2 hf
      -- d₁ = φ(p₁), d₂ = φ(p₂) with p₁, p₂ ∈ C_out and p₁.2 = d₁.1 = d₂.1 = p₂.2 => p₁ = p₂ => d₁ = d₂!
      have hsurj : Finset.image (Gsetup.geoPhi Gsetup.G le_rfl) C_out = C_out :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => by obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hCout_inv y hy)
          (by rw [Finset.card_image_of_injective _ (Gsetup.geoPhi Gsetup.G le_rfl).injective])
      obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp (hsurj.symm ▸ h1)
      obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp (hsurj.symm ▸ h2)
      have hp_eq : p₁ = p₂ := hinj_snd hp₁ hp₂ hf
      rw [hp_eq]
    have hinj_edge : Set.InjOn (fun d : DartOf Gsetup.G => s(d.1.1, d.1.2)) ↑C_out := by
      intro d₁ h1 d₂ h2 heq
      rcases Sym2.eq_iff.mp heq with ⟨h11, h22⟩ | ⟨h12, h21⟩
      · exact Subtype.ext (Prod.ext h11 h22)
      · -- d₂ = (d₁.2, d₁.1) has first coord d₁.2, same as φ(d₁)! So d₂ = φ(d₁), contradicting σ(d₁.1) ≠ d₁.1!
        exfalso
        have hphi_eq : d₂ = Gsetup.geoPhi Gsetup.G le_rfl d₁ :=
          hinj_fst h2 (hCout_inv d₁ h1) h21.symm
        have hfix : Gsetup.geoSigma Gsetup.G le_rfl d₁.1.2 ⟨d₁.1.1, d₁.2.symm⟩ = ⟨d₁.1.1, d₁.2.symm⟩ := by
          apply Subtype.ext
          have : (Gsetup.geoPhi Gsetup.G le_rfl d₁).1.2 = d₂.1.2 := congrArg (fun x : DartOf Gsetup.G => x.1.2) hphi_eq.symm
          exact this.trans h12.symm
        exact Gsetup.geoSigma_ne_self Gsetup.G le_rfl d₁.1.2 (hGdeg2 d₁.1.2) ⟨d₁.1.1, d₁.2.symm⟩ hfix
    rw [Finset.card_image_of_injOn hinj_edge]; exact hLb
  -- Step 8: Connect deleted edges e - e(S \ B) to ∑_{v ∈ B_idx} deg(v) - E_out.card!
  let B : Finset ℂ := B_idx.image pt
  have hB_sub : B ⊆ S := fun z hz => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hpt_mem i
  have hB_card : B.card = b := Finset.card_image_of_injective _ hpt_inj
  -- Number of edges in Gsetup.G touching B_idx equals edgeCount S - edgeCount (S \ B)
  have hE_sdiff : edgeCount (S \ B) = (Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ B_idx)).card := by
    unfold edgeCount
    refine Finset.card_bij
      (fun e he =>
        s(eqV.symm ⟨e.out.1.1, Finset.sdiff_subset e.out.1.2⟩,
          eqV.symm ⟨e.out.2.1, Finset.sdiff_subset e.out.2.2⟩)) ?_ ?_ ?_
    · intro e he
      have hadj := (unitGraph (S \ B)).mem_edgeFinset.mp he
      have hout : s(e.out.1, e.out.2) = e := e.out_eq
      have hadj' : (unitGraph (S \ B)).Adj e.out.1 e.out.2 := by rwa [← hout] at hadj
      have hGadj : Gsetup.G.Adj (eqV.symm ⟨e.out.1.1, Finset.sdiff_subset e.out.1.2⟩)
          (eqV.symm ⟨e.out.2.1, Finset.sdiff_subset e.out.2.2⟩) :=
        iso.symm.map_adj_iff.mpr hadj'
      refine Finset.mem_filter.mpr ⟨Gsetup.G.mem_edgeFinset.mpr hGadj, fun v hv hvB => ?_⟩
      simp only [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · have hpt_eq : pt (eqV.symm ⟨e.out.1.1, Finset.sdiff_subset e.out.1.2⟩) = e.out.1.1 :=
          congrArg Subtype.val (eqV.apply_symm_apply _)
        exact (Finset.mem_sdiff.mp e.out.1.2).2 (hpt_eq ▸ Finset.mem_image_of_mem pt hvB)
      · have hpt_eq : pt (eqV.symm ⟨e.out.2.1, Finset.sdiff_subset e.out.2.2⟩) = e.out.2.1 :=
          congrArg Subtype.val (eqV.apply_symm_apply _)
        exact (Finset.mem_sdiff.mp e.out.2.2).2 (hpt_eq ▸ Finset.mem_image_of_mem pt hvB)
    · intro e₁ h1 e₂ h2 heq
      rw [← e₁.out_eq, ← e₂.out_eq]
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have ha' := congrArg (fun x => (eqV x).1) ha
        have hb' := congrArg (fun x => (eqV x).1) hb
        simp only [Equiv.apply_symm_apply] at ha' hb'
        exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext ha', Subtype.ext hb'⟩)
      · have ha' := congrArg (fun x => (eqV x).1) ha
        have hb' := congrArg (fun x => (eqV x).1) hb
        simp only [Equiv.apply_symm_apply] at ha' hb'
        exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext ha', Subtype.ext hb'⟩)
    · intro e he
      induction e using Sym2.ind with | _ i j =>
      obtain ⟨hadj, hnotB⟩ := Finset.mem_filter.mp he
      have hadj' : Gsetup.G.Adj i j := Gsetup.G.mem_edgeFinset.mp hadj
      have hi : pt i ∈ S \ B := Finset.mem_sdiff.mpr ⟨hpt_mem i, fun h => by
        obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp h
        exact hnotB i (Sym2.mem_mk_left i j) (hpt_inj hki ▸ hk)⟩
      have hj : pt j ∈ S \ B := Finset.mem_sdiff.mpr ⟨hpt_mem j, fun h => by
        obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp h
        exact hnotB j (Sym2.mem_mk_right i j) (hpt_inj hkj ▸ hk)⟩
      let e0 : Sym2 {z : ℂ // z ∈ S \ B} := s(⟨pt i, hi⟩, ⟨pt j, hj⟩)
      refine ⟨e0, (unitGraph (S \ B)).mem_edgeFinset.mpr (iso.map_adj_iff.mpr hadj'), ?_⟩
      have heqV : ∀ k : Fin n, (eqV k).1 = pt k := fun _ => rfl
      have hout := e0.out_eq
      rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hi1 : eqV.symm ⟨e0.out.1.1, Finset.sdiff_subset e0.out.1.2⟩ = i :=
          eqV.injective (by rw [eqV.apply_symm_apply]; exact Subtype.ext ((congrArg Subtype.val h1).trans (heqV i).symm))
        have hj1 : eqV.symm ⟨e0.out.2.1, Finset.sdiff_subset e0.out.2.2⟩ = j :=
          eqV.injective (by rw [eqV.apply_symm_apply]; exact Subtype.ext ((congrArg Subtype.val h2).trans (heqV j).symm))
        rw [hi1, hj1]
      · have hi1 : eqV.symm ⟨e0.out.1.1, Finset.sdiff_subset e0.out.1.2⟩ = j :=
          eqV.injective (by rw [eqV.apply_symm_apply]; exact Subtype.ext ((congrArg Subtype.val h1).trans (heqV j).symm))
        have hj1 : eqV.symm ⟨e0.out.2.1, Finset.sdiff_subset e0.out.2.2⟩ = i :=
          eqV.injective (by rw [eqV.apply_symm_apply]; exact Subtype.ext ((congrArg Subtype.val h2).trans (heqV i).symm))
        rw [hi1, hj1, Sym2.eq_swap]
  -- Double counting ∑_{v ∈ B_idx} deg(v) = #(edges touching B_idx) + #(edges with both endpoints in B_idx)
  have hdouble : (Gsetup.G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ B_idx)).card +
      (Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B_idx)).card =
      ∑ v ∈ B_idx, Gsetup.G.degree v := by
    convert sum_degree_eq_touching_add_internal Gsetup.G B_idx
  have hpart_E : (Gsetup.G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ B_idx)).card +
      (Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ B_idx)).card = Gsetup.G.edgeFinset.card := by
    have hnot : Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ B_idx) =
        Gsetup.G.edgeFinset.filter (fun e => ¬ ∃ v ∈ e, v ∈ B_idx) := by
      congr 1; ext e; simp
    rw [hnot, Finset.card_filter_add_card_filter_not]
  have hEout_le : E_out.card ≤ (Gsetup.G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B_idx)).card :=
    Finset.card_le_card hEout_sub
  -- Combine into (A) and (B)!
  refine ⟨B, hB_sub, by omega, by omega, ?_⟩
  rcases eq_or_lt_of_le hb_le_L with hLb | hLb
  · have hEo := hEout_eq_if hLb.symm
    omega
  · omega

/-- Harborth's inequality on finite 1-separated subsets of `ℂ` (by strong induction on `S.card`). -/
private theorem harborth_complex :
    ∀ n : ℕ, ∀ S : Finset ℂ, S.card = n →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) →
      12 * n ≤ (3 * n - edgeCount S) ^ 2 + 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hsep
    classical
    -- Case 1: n ≤ 3
    by_cases hn3 : n ≤ 3
    · have h2e : 2 * edgeCount S ≤ n * (n - 1) := by
        have hdeg : ∀ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v ≤ n - 1 := by
          intro v
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          have hsub : (unitGraph S).neighborFinset v ⊆ Finset.univ.erase v := by
            intro u hu; exact Finset.mem_erase.mpr ⟨((unitGraph S).ne_of_adj (((unitGraph S).mem_neighborFinset _ _).mp hu)).symm, Finset.mem_univ _⟩
          have hle := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe, hcard] at hle
          exact hle
        have hsum : ∑ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v ≤ n * (n - 1) := by
          calc ∑ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v
              ≤ ∑ _ : {z : ℂ // z ∈ S}, (n - 1) := Finset.sum_le_sum (fun v _ => hdeg v)
            _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hcard, nsmul_eq_mul, Nat.cast_id]
        rw [(unitGraph S).sum_degrees_eq_twice_card_edges] at hsum
        exact hsum
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl | rfl
      · simp
      · have : edgeCount S = 0 := by omega
        rw [this]; norm_num
      · have : edgeCount S ≤ 1 := by omega
        have : 5 ≤ 3 * 2 - edgeCount S := by omega
        nlinarith
      · have : edgeCount S ≤ 3 := by omega
        have : 6 ≤ 3 * 3 - edgeCount S := by omega
        nlinarith
    have hn4 : 4 ≤ n := by omega
    -- Case 2: unitGraph S is disconnected
    by_cases hconn : (unitGraph S).Connected
    · -- Case 3: Some vertex has degree ≤ 2
      by_cases hdeg2 : ∃ v : {z : ℂ // z ∈ S}, (unitGraph S).degree v ≤ 2
      · obtain ⟨v, hv⟩ := hdeg2
        let S' := S.erase v.1
        have hS'_card : S'.card = n - 1 := by
          rw [Finset.card_erase_of_mem v.2, hcard]
        have hS'_sep : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → 1 ≤ ‖x - y‖ :=
          fun x hx y hy hxy => hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have hIH := ih (n - 1) (by omega) S' hS'_card hS'_sep
        -- Compare edgeCount S and edgeCount S': edgeCount S ≤ edgeCount S' + degree v
        have hedge_del : edgeCount S ≤ edgeCount S' + (unitGraph S).degree v := by
          unfold edgeCount
          have hpart : (unitGraph S).edgeFinset.card =
              ((unitGraph S).edgeFinset.filter (fun e => v ∈ e)).card +
              ((unitGraph S).edgeFinset.filter (fun e => v ∉ e)).card :=
            (Finset.card_filter_add_card_filter_not _).symm
          have hinc : ((unitGraph S).edgeFinset.filter (fun e => v ∈ e)).card = (unitGraph S).degree v := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            refine Finset.card_bij
              (fun e he => Classical.choose (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp he).2)) ?_ ?_ ?_
            · intro e he
              have hsp := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp he).2)
              exact ((unitGraph S).mem_neighborFinset _ _).mpr ((unitGraph S).mem_edgeFinset.mp (hsp ▸ (Finset.mem_filter.mp he).1))
            · intro e₁ h1 e₂ h2 hw
              have h1' := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp h1).2)
              have h2' := Classical.choose_spec (Sym2.mem_iff_exists.mp (Finset.mem_filter.mp h2).2)
              rw [h1', h2', hw]
            · intro u hu
              have hadj := ((unitGraph S).mem_neighborFinset _ _).mp hu
              refine ⟨s(v, u), Finset.mem_filter.mpr ⟨(unitGraph S).mem_edgeFinset.mpr hadj, Sym2.mem_mk_left v u⟩, ?_⟩
              have hsp := Classical.choose_spec (Sym2.mem_iff_exists.mp (Sym2.mem_mk_left v u))
              rcases Sym2.eq_iff.mp hsp.symm with ⟨_, h⟩ | ⟨h, _⟩
              · exact h
              · exact ((unitGraph S).loopless.irrefl v (h ▸ hadj)).elim
          have hrem : ((unitGraph S).edgeFinset.filter (fun e => v ∉ e)).card = (unitGraph S').edgeFinset.card := by
            refine Finset.card_bij
              (fun (e : Sym2 {z : ℂ // z ∈ S}) (he : e ∈ (unitGraph S).edgeFinset.filter (fun e => v ∉ e)) =>
                have h1 : e.out.1.1 ∈ S' := Finset.mem_erase.mpr
                  ⟨fun h => (Finset.mem_filter.mp he).2 (Subtype.ext h ▸ Sym2.out_fst_mem e), e.out.1.2⟩
                have h2 : e.out.2.1 ∈ S' := Finset.mem_erase.mpr
                  ⟨fun h => (Finset.mem_filter.mp he).2 (Subtype.ext h ▸ Sym2.out_snd_mem e), e.out.2.2⟩
                (s(⟨e.out.1.1, h1⟩, ⟨e.out.2.1, h2⟩) : Sym2 {z : ℂ // z ∈ S'})) ?_ ?_ ?_
            · intro e he
              have hadj := (unitGraph S).mem_edgeFinset.mp (Finset.mem_filter.mp he).1
              have hout := e.out_eq
              rw [← hout] at hadj
              exact (unitGraph S').mem_edgeFinset.mpr hadj
            · intro e₁ _ e₂ _ heq
              rw [← e₁.out_eq, ← e₂.out_eq]
              rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
              · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S'} → ℂ) ha),
                  Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S'} → ℂ) hb)⟩)
              · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S'} → ℂ) ha),
                  Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S'} → ℂ) hb)⟩)
            · intro e' he'
              induction e' using Sym2.ind with | _ x y =>
              have hadj := (unitGraph S').mem_edgeFinset.mp he'
              let e : Sym2 {z : ℂ // z ∈ S} := s(⟨x.1, Finset.mem_of_mem_erase x.2⟩, ⟨y.1, Finset.mem_of_mem_erase y.2⟩)
              have hvnot : v ∉ e := by
                intro hmem; rcases Sym2.mem_iff.mp hmem with h | h
                · exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h).symm
                · exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h).symm
              refine ⟨e, Finset.mem_filter.mpr ⟨(unitGraph S).mem_edgeFinset.mpr hadj, hvnot⟩, ?_⟩
              rcases Sym2.eq_iff.mp e.out_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h1),
                  Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h2)⟩)
              · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h1),
                  Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h2)⟩)
          omega
        have he'le : edgeCount S' ≤ 3 * (n - 1) := hS'_card ▸ edgeCount_le_three_mul S' hS'_sep
        set D' := 3 * (n - 1) - edgeCount S'
        set D := 3 * n - edgeCount S
        have h36 : 36 ≤ D' ^ 2 + 3 := by omega
        have hD'6 : 6 ≤ D' := by
          by_contra h
          have : D' ≤ 5 := by omega
          nlinarith
        have hD_ge : D' + 1 ≤ D := by omega
        have hsq : (D' + 1) ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hD_ge 2
        have h12n : 12 * n = 12 * (n - 1) + 12 := by omega
        nlinarith
      · -- Case 4: Connected AND ∀ v, 3 ≤ deg v! Apply exists_boundary_subset!
        push Not at hdeg2
        obtain ⟨B, hB_sub, hB3, hA, hB⟩ :=
          exists_boundary_subset S hsep (hcard ▸ hn4) hconn hdeg2
        rw [hcard] at hA
        set b := B.card
        set D := 3 * n - edgeCount S
        by_cases hbn : b = n
        · -- B = S: D ≥ n + 3 => D² + 3 ≥ (n + 3)² + 3 = 12n + (n - 3)² + 3 ≥ 12n!
          have hDge : n + 3 ≤ D := by omega
          have hsq : (n + 3) ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hDge 2
          nlinarith
        · -- b < n: apply IH to S' = S \ B!
          have hble : b ≤ n := hcard ▸ Finset.card_le_card hB_sub
          have hblt : b < n := lt_of_le_of_ne hble hbn
          let S' := S \ B
          have hS'_card : S'.card = n - b := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB_sub, hcard]
          have hS'_sep : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → 1 ≤ ‖x - y‖ :=
            fun x hx y hy hxy => hsep x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy) hxy
          have hIH := ih (n - b) (by omega) S' hS'_card hS'_sep
          have he'le : edgeCount S' ≤ 3 * (n - b) := hS'_card ▸ edgeCount_le_three_mul S' hS'_sep
          set D' := 3 * (n - b) - edgeCount S'
          have hB' : edgeCount S ≤ edgeCount S' + 3 * b - 6 := hB
          have hD6 : 6 ≤ D := by omega
          have hD'_le : D' ≤ D - 6 := by omega
          have hsq : D' ^ 2 ≤ (D - 6) ^ 2 := Nat.pow_le_pow_left hD'_le 2
          -- 12 * n = 12 * (n - b) + 12 * b ≤ (D - 6)² + 3 + 12 * (D - 3) = D² + 3!
          have h12b : 12 * b ≤ 12 * (D - 3) := by omega
          have halg : (D - 6) ^ 2 + 3 + 12 * (D - 3) = D ^ 2 + 3 := by
            zify [hD6, (show 3 ≤ D by omega)]
            ring
          omega
    · -- Case 2: unitGraph S is NOT connected! Split into component of v₀ and its complement!
      have hneS : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨z₀, hz₀⟩ := hneS
      let v₀ : {z : ℂ // z ∈ S} := ⟨z₀, hz₀⟩
      let S₁ : Finset ℂ := S.filter (fun z => ∃ hz : z ∈ S, (unitGraph S).Reachable v₀ ⟨z, hz⟩)
      let S₂ : Finset ℂ := S \ S₁
      have hS₁_sub : S₁ ⊆ S := Finset.filter_subset _ _
      have hS₁_pos : 1 ≤ S₁.card := Finset.card_pos.mpr
        ⟨z₀, Finset.mem_filter.mpr ⟨hz₀, hz₀, SimpleGraph.Reachable.refl _⟩⟩
      have hS₂_pos : 1 ≤ S₂.card := by
        have hnotall : ∃ v : {z : ℂ // z ∈ S}, ¬ (unitGraph S).Reachable v₀ v := by
          by_contra h; push_neg at h
          apply hconn; exact @SimpleGraph.Connected.mk _ _ (fun x y => (h x).symm.trans (h y)) ⟨v₀⟩
        obtain ⟨v₁, hv₁⟩ := hnotall
        refine Finset.card_pos.mpr ⟨v₁.1, Finset.mem_sdiff.mpr ⟨v₁.2, fun h => ?_⟩⟩
        obtain ⟨_, hz, hr⟩ := Finset.mem_filter.mp h
        exact hv₁ hr
      have hcard_sum : S₁.card + S₂.card = n := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS₁_sub]
        have := Finset.card_le_card hS₁_sub; omega
      have hS₁_sep : ∀ x ∈ S₁, ∀ y ∈ S₁, x ≠ y → 1 ≤ ‖x - y‖ :=
        fun x hx y hy hxy => hsep x (hS₁_sub hx) y (hS₁_sub hy) hxy
      have hS₂_sep : ∀ x ∈ S₂, ∀ y ∈ S₂, x ≠ y → 1 ≤ ‖x - y‖ :=
        fun x hx y hy hxy => hsep x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy) hxy
      have hIH₁ := ih S₁.card (by omega) S₁ rfl hS₁_sep
      have hIH₂ := ih S₂.card (by omega) S₂ rfl hS₂_sep
      -- No edge of unitGraph S crosses between S₁ and S₂, so edgeCount S = edgeCount S₁ + edgeCount S₂!
      have hedge_sum : edgeCount S = edgeCount S₁ + edgeCount S₂ := by
        unfold edgeCount
        let f₁ : Sym2 {z : ℂ // z ∈ S₁} ↪ Sym2 {z : ℂ // z ∈ S} :=
          (⟨fun x => ⟨x.1, hS₁_sub x.2⟩, fun _ _ h => Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h)⟩ :
            {z : ℂ // z ∈ S₁} ↪ {z : ℂ // z ∈ S}).sym2Map
        let f₂ : Sym2 {z : ℂ // z ∈ S₂} ↪ Sym2 {z : ℂ // z ∈ S} :=
          (⟨fun x => ⟨x.1, Finset.sdiff_subset x.2⟩, fun _ _ h => Subtype.ext (congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h)⟩ :
            {z : ℂ // z ∈ S₂} ↪ {z : ℂ // z ∈ S}).sym2Map
        rw [← Finset.card_map f₁, ← Finset.card_map f₂, ← Finset.card_union_of_disjoint]
        · congr 1
          ext e
          induction e using Sym2.ind with | _ x y =>
          simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_edgeFinset]
          constructor
          · intro hxy
            by_cases hx : x.1 ∈ S₁
            · left
              have hy : y.1 ∈ S₁ := by
                obtain ⟨_, _, hrx⟩ := Finset.mem_filter.mp hx
                exact Finset.mem_filter.mpr ⟨y.2, y.2, hrx.trans hxy.reachable⟩
              exact ⟨s(⟨x.1, hx⟩, ⟨y.1, hy⟩), hxy, rfl⟩
            · right
              have hy : y.1 ∉ S₁ := by
                intro hy
                obtain ⟨_, _, hry⟩ := Finset.mem_filter.mp hy
                exact hx (Finset.mem_filter.mpr ⟨x.2, x.2, hry.trans hxy.symm.reachable⟩)
              exact ⟨s(⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩, ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩), hxy, rfl⟩
          · rintro (⟨e', he', heq⟩ | ⟨e', he', heq⟩)
            · induction e' using Sym2.ind with | _ a b =>
              change s(⟨a.1, hS₁_sub a.2⟩, ⟨b.1, hS₁_sub b.2⟩) = s(x, y) at heq
              have hadj' : (unitGraph S₁).Adj a b := he'
              rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [← h1, ← h2]; exact hadj'
              · rw [← h1, ← h2]; exact hadj'.symm
            · induction e' using Sym2.ind with | _ a b =>
              change s(⟨a.1, Finset.sdiff_subset a.2⟩, ⟨b.1, Finset.sdiff_subset b.2⟩) = s(x, y) at heq
              have hadj' : (unitGraph S₂).Adj a b := he'
              rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [← h1, ← h2]; exact hadj'
              · rw [← h1, ← h2]; exact hadj'.symm
        · rw [Finset.disjoint_left]
          intro e h1 h2
          obtain ⟨e₁, _, rfl⟩ := Finset.mem_map.mp h1
          obtain ⟨e₂, _, heq⟩ := Finset.mem_map.mp h2
          induction e₁ using Sym2.ind with | _ a b =>
          induction e₂ using Sym2.ind with | _ c d =>
          rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
          · exact (Finset.mem_sdiff.mp c.2).2 ((congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h) ▸ a.2)
          · exact (Finset.mem_sdiff.mp c.2).2 ((congrArg (Subtype.val : {z : ℂ // z ∈ S} → ℂ) h) ▸ b.2)
      have he1_le := edgeCount_le_three_mul S₁ hS₁_sep
      have he2_le := edgeCount_le_three_mul S₂ hS₂_sep
      set D₁ := 3 * S₁.card - edgeCount S₁
      set D₂ := 3 * S₂.card - edgeCount S₂
      set D := 3 * n - edgeCount S
      have hD_eq : D = D₁ + D₂ := by omega
      have hD1_ge3 : 3 ≤ D₁ := by nlinarith
      have hD2_ge3 : 3 ≤ D₂ := by nlinarith
      rw [hD_eq]
      nlinarith

/-- **Harborth's Inequality (`H3` of `Erdos1084.erdos_1084.variants.triangular_optimal_d2.R1`)**:
    For every finite 1-separated `S : Finset ℝ²`,
    `12 * S.card ≤ (3 * S.card - unitDistNum S) ^ 2 + 3`. -/
theorem harborth (S : Finset ℝ²) (hsep : Metric.IsSeparated' 1 (S : Set ℝ²)) :
    12 * S.card ≤ (3 * S.card - unitDistNum S) ^ 2 + 3 := by
  classical
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ :=
    (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm
  let S_C : Finset ℂ := S.image e
  have hcard : S_C.card = S.card := Finset.card_image_of_injective S e.injective
  have hsep_C : ∀ x ∈ S_C, ∀ y ∈ S_C, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg e h)
    have hd := hsep ha hb hab
    rw [← dist_eq_norm, e.dist_map]
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp
      (by simpa only [ENNReal.ofReal_one, ← edist_dist] using hd)
  have hedge : unitDistNum S ≤ edgeCount S_C := by
    unfold edgeCount
    let embV : {z : ℂ // z ∈ S_C} ↪ ℝ² :=
      ⟨fun z => e.symm z.1, fun x y h => Subtype.ext (e.symm.injective h)⟩
    let embE := embV.sym2Map
    apply (Finset.card_le_card (t := (unitGraph S_C).edgeFinset.map embE) ?_).trans (Finset.card_map embE).le
    intro k hk
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hk
    let a := k.out.1
    let b := k.out.2
    have ha : a ∈ S := (Finset.mem_sym2_iff.mp hm) a (Sym2.out_fst_mem k)
    have hb : b ∈ S := (Finset.mem_sym2_iff.mp hm) b (Sym2.out_snd_mem k)
    have ha' : e a ∈ S_C := Finset.mem_image_of_mem e ha
    have hb' : e b ∈ S_C := Finset.mem_image_of_mem e hb
    refine Finset.mem_map.mpr ⟨s(⟨e a, ha'⟩, ⟨e b, hb'⟩), (unitGraph S_C).mem_edgeFinset.mpr ?_, ?_⟩
    · change ‖e a - e b‖ = 1
      rw [← dist_eq_norm, e.dist_map]
      exact hd
    · change s(e.symm (e a), e.symm (e b)) = k
      simp only [LinearIsometryEquiv.symm_apply_apply]
      exact Quot.out_eq k
  have hmain := harborth_complex S.card S_C hcard hsep_C
  have hsub : 3 * S.card - edgeCount S_C ≤ 3 * S.card - unitDistNum S :=
    Nat.sub_le_sub_left hedge _
  have hsq : (3 * S.card - edgeCount S_C) ^ 2 ≤ (3 * S.card - unitDistNum S) ^ 2 :=
    Nat.pow_le_pow_left hsub 2
  omega

end HarborthCore

end Erdos1084Harborth

theorem OMA.solution : type_of% @Erdos1084.erdos_1084.variants.triangular_optimal_d2 :=
  OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.main
    OMA.HexagonalPatchCount.patch_card
    OMA.HexagonalPatchContacts.contacts
    Erdos1084Harborth.harborth
