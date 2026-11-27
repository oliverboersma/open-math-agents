import OMAStatements.S_oeis_a387471
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Squarefree

-- Credit: @begcdn. Independent proof of the equal-angle triple-intersection count.
-- The roots-of-unity section proves the six-term rational-relation bound directly.

namespace A387471

def gridModulus : Nat := 4562284561

def gridMonomial (u : Int) : Int := (2 : Int) ^ (u % 120).toNat

def gridSine (u : Int) : Int := gridMonomial u - gridMonomial (-u)

def gridTest (a b c : Nat) : Bool :=
  let x : Int := (a : Int) - 10
  let y : Int := (b : Int) - 10
  let z : Int := (c : Int) - 10
  (gridSine (x+y-z) + gridSine (y+z-x) + gridSine (z+x-y)) % gridModulus == 0

def gridCandidates : List (Nat × Nat × Nat) :=
  (List.range 20).flatMap fun a =>
    (List.range 20).flatMap fun b =>
      ((List.range 20).filter fun c =>
        0 < a && a ≤ b && b ≤ c && a != 10 && b != 10 && c != 10 &&
          gridTest a b c).map fun c => (a,b,c)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem grid_candidates_eq : gridCandidates = [(2,14,16),(4,6,18)] := by decide +kernel

end A387471

namespace A387471
open Polynomial

theorem eval_cyclotomic_120 : (cyclotomic 120 ℤ).eval 2 = 4562284561 := by
  have product (n : ℕ) (hn : 0 < n) :
      (∏ d ∈ n.divisors, (cyclotomic d ℤ).eval 2) = 2^n-1 := by
    simpa only [eval_prod,eval_sub,eval_pow,eval_X,eval_one] using
      congrArg (Polynomial.eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
  have v1 : (cyclotomic 1 ℤ).eval 2 = 1 := by
    have e := product 1 (by decide)
    rw [show (1 : ℕ).divisors = {1} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton] at e ⊢
  have v2 : (cyclotomic 2 ℤ).eval 2 = 3 := by
    have e := product 2 (by decide)
    rw [show (2 : ℕ).divisors = {1,2} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1] at e ⊢
  have v3 : (cyclotomic 3 ℤ).eval 2 = 7 := by
    have e := product 3 (by decide)
    rw [show (3 : ℕ).divisors = {1,3} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1] at e ⊢
  have v4 : (cyclotomic 4 ℤ).eval 2 = 5 := by
    have e := product 4 (by decide)
    rw [show (4 : ℕ).divisors = {1,2,4} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2] at e ⊢
    all_goals linarith only [e]
  have v5 : (cyclotomic 5 ℤ).eval 2 = 31 := by
    have e := product 5 (by decide)
    rw [show (5 : ℕ).divisors = {1,5} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1] at e ⊢
    all_goals linarith only [e]
  have v6 : (cyclotomic 6 ℤ).eval 2 = 3 := by
    have e := product 6 (by decide)
    rw [show (6 : ℕ).divisors = {1,2,3,6} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3] at e ⊢
    all_goals linarith only [e]
  have v8 : (cyclotomic 8 ℤ).eval 2 = 17 := by
    have e := product 8 (by decide)
    rw [show (8 : ℕ).divisors = {1,2,4,8} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v4] at e ⊢
    all_goals linarith only [e]
  have v10 : (cyclotomic 10 ℤ).eval 2 = 11 := by
    have e := product 10 (by decide)
    rw [show (10 : ℕ).divisors = {1,2,5,10} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v5] at e ⊢
    all_goals linarith only [e]
  have v12 : (cyclotomic 12 ℤ).eval 2 = 13 := by
    have e := product 12 (by decide)
    rw [show (12 : ℕ).divisors = {1,2,3,4,6,12} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3,v4,v6] at e ⊢
    all_goals linarith only [e]
  have v15 : (cyclotomic 15 ℤ).eval 2 = 151 := by
    have e := product 15 (by decide)
    rw [show (15 : ℕ).divisors = {1,3,5,15} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v3,v5] at e ⊢
    all_goals linarith only [e]
  have v20 : (cyclotomic 20 ℤ).eval 2 = 205 := by
    have e := product 20 (by decide)
    rw [show (20 : ℕ).divisors = {1,2,4,5,10,20} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v4,v5,v10] at e ⊢
    all_goals linarith only [e]
  have v24 : (cyclotomic 24 ℤ).eval 2 = 241 := by
    have e := product 24 (by decide)
    rw [show (24 : ℕ).divisors = {1,2,3,4,6,8,12,24} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3,v4,v6,v8,v12] at e ⊢
    all_goals linarith only [e]
  have v30 : (cyclotomic 30 ℤ).eval 2 = 331 := by
    have e := product 30 (by decide)
    rw [show (30 : ℕ).divisors = {1,2,3,5,6,10,15,30} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3,v5,v6,v10,v15] at e ⊢
    all_goals linarith only [e]
  have v40 : (cyclotomic 40 ℤ).eval 2 = 61681 := by
    have e := product 40 (by decide)
    rw [show (40 : ℕ).divisors = {1,2,4,5,8,10,20,40} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v4,v5,v8,v10,v20] at e ⊢
    all_goals linarith only [e]
  have v60 : (cyclotomic 60 ℤ).eval 2 = 80581 := by
    have e := product 60 (by decide)
    rw [show (60 : ℕ).divisors = {1,2,3,4,5,6,10,12,15,20,30,60} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3,v4,v5,v6,v10,v12,v15,v20,v30] at e ⊢
    all_goals linarith only [e]
  have v120 : (cyclotomic 120 ℤ).eval 2 = 4562284561 := by
    have e := product 120 (by decide)
    rw [show (120 : ℕ).divisors = {1,2,3,4,5,6,8,10,12,15,20,24,30,40,60,120} by decide] at e
    norm_num [Finset.prod_insert,Finset.prod_singleton,v1,v2,v3,v4,v5,v6,v8,v10,v12,v15,v20,v24,v30,v40,v60] at e ⊢
    all_goals linarith only [e]
  exact v120

theorem grid_divisibility {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 120) (P : ℤ[X])
    (h : aeval ζ P = 0) : (4562284561 : ℤ) ∣ P.eval 2 := by
  have hp : cyclotomic 120 ℤ ∣ P := by
    rw [cyclotomic_eq_minpoly hζ (by decide)]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral (by decide)) h
  obtain ⟨Q,hQ⟩ := hp
  exact ⟨Q.eval 2, by rw [hQ, eval_mul, eval_cyclotomic_120]⟩

noncomputable def sinePoly (u : ℤ) : ℤ[X] := X^(u % 120).toNat - X^((-u) % 120).toNat

private theorem eval_grid_power (u : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I / 120) ^ (u % 120).toNat =
    Complex.exp (((u : ℝ)*Real.pi/60 : ℝ) * (Complex.I : ℂ)) := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u/120), ?_⟩
  have hn : (((u%120).toNat : ℕ) : ℂ) = ((u%120 : ℤ) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg u (by decide : (120 : ℤ) ≠ 0))
  have h : ((u%120 : ℤ) : ℂ) + 120 * ((u/120 : ℤ) : ℂ) = u := by
    exact_mod_cast Int.emod_add_mul_ediv u 120
  push_cast
  rw [hn]
  linear_combination (Real.pi : ℂ) * Complex.I / 60 * h

private theorem eval_sine_poly (u : ℤ) :
    aeval (Complex.exp (2 * Real.pi * Complex.I / 120)) (sinePoly u) =
    (2 * ((Real.sin ((u : ℝ)*Real.pi/60) : ℝ) : ℂ) * Complex.I) := by
  simp only [sinePoly, map_sub, map_pow, aeval_X, eval_grid_power, Complex.exp_ofReal_mul_I]
  simp only [Int.cast_neg,neg_mul,neg_div,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

theorem grid_sine_dvd (u v w : ℤ)
    (h : Real.sin ((u : ℝ)*Real.pi/60) + Real.sin ((v : ℝ)*Real.pi/60) +
         Real.sin ((w : ℝ)*Real.pi/60) = 0) :
    (4562284561 : ℤ) ∣ ((sinePoly u + sinePoly v + sinePoly w).eval 2) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 120)) 120 := by
    simpa using Complex.isPrimitiveRoot_exp 120 (by decide)
  apply grid_divisibility hz
  simp only [map_add, eval_sine_poly]
  have h' := congrArg ((↑) : ℝ → ℂ) h
  simp only [Complex.ofReal_add, Complex.ofReal_zero] at h'
  linear_combination 2 * Complex.I * h'

theorem classify_grid (a b c : ℕ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c < 20) (hma : a ≠ 10) (hmb : b ≠ 10) (hmc : c ≠ 10)
    (hs : let x : ℤ := (a : ℤ)-10
          let y : ℤ := (b : ℤ)-10
          let z : ℤ := (c : ℤ)-10
          Real.sin (((x+y-z : ℤ) : ℝ)*Real.pi/60) +
          Real.sin (((y+z-x : ℤ) : ℝ)*Real.pi/60) +
          Real.sin (((z+x-y : ℤ) : ℝ)*Real.pi/60) = 0) :
    (a,b,c) = (2,14,16) ∨ (a,b,c) = (4,6,18) := by
  let x : ℤ := (a : ℤ)-10
  let y : ℤ := (b : ℤ)-10
  let z : ℤ := (c : ℤ)-10
  have div := grid_sine_dvd (x+y-z) (y+z-x) (z+x-y) hs
  have ht : gridTest a b c := by
    apply beq_iff_eq.mpr
    apply Int.emod_eq_zero_of_dvd
    simpa only [sinePoly, eval_add, eval_sub, eval_pow, eval_X, gridSine, gridMonomial,
      gridModulus, Nat.cast_ofNat] using div
  have mem : (a,b,c) ∈ gridCandidates := by
    apply List.mem_flatMap.mpr
    refine ⟨a,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ?_⟩
    refine ⟨b,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨c,?_,rfl⟩⟩
    simp [List.mem_filter, hc, ha, hab, hbc, hma, hmb, hmc, ht]
  rw [grid_candidates_eq] at mem
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using mem

end A387471

namespace A387471

theorem centered_ceva (x y z : ℝ) :
    Real.sin (Real.pi/6+x) * Real.sin (Real.pi/6+y) * Real.sin (Real.pi/6+z) =
    Real.sin (Real.pi/6-x) * Real.sin (Real.pi/6-y) * Real.sin (Real.pi/6-z) ↔
    Real.sin (x+y-z) + Real.sin (y+z-x) + Real.sin (z+x-y) = 0 := by
  rw [← sub_eq_zero]
  have factor :
      Real.sin (Real.pi/6+x) * Real.sin (Real.pi/6+y) * Real.sin (Real.pi/6+z) -
      Real.sin (Real.pi/6-x) * Real.sin (Real.pi/6-y) * Real.sin (Real.pi/6-z) =
      (Real.cos (Real.pi/6) / 2) *
      (Real.sin (x+y-z) + Real.sin (y+z-x) + Real.sin (z+x-y)) := by
    simp only [Real.sin_add, Real.sin_sub, Real.cos_add, Real.sin_pi_div_six]
    linear_combination 2 * Real.cos (Real.pi/6) * Real.sin x * Real.sin y *
      Real.sin z * Real.sq_cos_pi_div_six
  rw [factor, mul_eq_zero]
  simp

end A387471

namespace A387471

open OMA.S_oeis_a387471

private noncomputable def ray (m i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * Real.pi / (3 * ((m : ℝ) + 1))

private theorem ray_bounds {m : ℕ} (i : Fin m) :
    0 < ray m i ∧ ray m i < Real.pi/3 := by
  unfold ray
  have hi : (i.val : ℝ) < m := by exact_mod_cast i.isLt
  have hm : (0 : ℝ) < 3*((m : ℝ)+1) := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hm).mpr
    nlinarith [mul_pos (sub_pos.mpr hi) Real.pi_pos]

private theorem ratio_injective {m : ℕ} (i j : Fin m)
    (h : ratio m i = ratio m j) : i = j := by
  have hi := ray_bounds i
  have hj := ray_bounds j
  let a := ray m i
  let b := ray m j
  change 0 < a ∧ a < Real.pi/3 at hi
  change 0 < b ∧ b < Real.pi/3 at hj
  have hpos (t : ℝ) (ht : 0 < t ∧ t < Real.pi/3) :
      0 < Real.sin (Real.pi/3-t) := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2])
        (by linarith [ht.1, Real.pi_pos])
  change Real.sin a / Real.sin (Real.pi/3-a) = Real.sin b / Real.sin (Real.pi/3-b) at h
  have he := (div_eq_div_iff (hpos a hi).ne' (hpos b hj).ne').mp h
  have hs : Real.sin (Real.pi/3) * Real.sin (a-b) = 0 := by
    simp only [Real.sin_sub] at he ⊢
    linear_combination he
  have hzero := (mul_eq_zero.mp hs).resolve_left (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] :
    0 < Real.pi/3) (by linarith [Real.pi_pos])).ne'
  have hab : a-b = 0 := Real.strictMonoOn_sin.injOn
    ⟨by linarith [hi.1,hj.2,Real.pi_pos], by linarith [hi.2,hj.1,Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by simpa using hzero)
  have ht : a=b := sub_eq_zero.mp hab
  change ((i.val : ℝ)+1)*Real.pi / _ = ((j.val : ℝ)+1)*Real.pi / _ at ht
  have hd : (3*((m : ℝ)+1)) ≠ 0 := by positivity
  have hnum := (div_left_inj' hd).mp ht
  apply Fin.ext
  have hval : (i.val : ℝ) = j.val := by linarith [(mul_left_inj' Real.pi_ne_zero).mp hnum]
  exact_mod_cast hval

private theorem reflect_ray {m : ℕ} (i : Fin m) :
    ray m i.rev = Real.pi/3 - ray m i := by
  unfold ray
  have hsum : i.rev.val + i.val + 1 = m := by rw [Fin.val_rev]; omega
  have hs : (i.rev.val : ℝ) + i.val + 1 = m := by exact_mod_cast hsum
  rw [eq_sub_iff_add_eq, ← add_div]
  apply (div_eq_iff (by positivity : (3*((m : ℝ)+1)) ≠ 0)).mpr
  linear_combination Real.pi * hs

private theorem ratio_pos {m : ℕ} (i : Fin m) : 0 < ratio m i := by
  have h := ray_bounds i
  change 0 < Real.sin (ray m i) / Real.sin (Real.pi/3-ray m i)
  apply div_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [h.1,h.2,Real.pi_pos]

private theorem reflect_ratio {m : ℕ} (i : Fin m) :
    ratio m i.rev = (ratio m i)⁻¹ := by
  change Real.sin (ray m i.rev) / Real.sin (Real.pi/3-ray m i.rev) = _
  rw [reflect_ray, sub_sub_cancel]
  exact (inv_div _ _).symm

private theorem pair_iff {m : ℕ} (i j : Fin m) :
    ratio m i * ratio m j = 1 ↔ j = i.rev := by
  constructor
  · intro h
    apply ratio_injective
    rw [reflect_ratio]
    exact eq_inv_of_mul_eq_one_right h
  · rintro rfl
    rw [reflect_ratio, mul_inv_cancel₀ (ratio_pos i).ne']

theorem median_count (n : ℕ) (hn : 1 ≤ n) :
    Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
      ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧
      (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)} = 6*n-5 := by
  let m := 2*n-1
  let c : Fin m := ⟨n-1, by dsimp [m]; omega⟩
  have hidx (i : Fin m) : i.val + 1 = n ↔ i = c := by
    change _ ↔ i = ⟨n-1, _⟩
    rw [Fin.ext_iff]
    dsimp
    omega
  have hrev : c.rev = c := by
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp [c,m]
    omega
  have hcenter : ratio m c = 1 := by
    have hp := (pair_iff c c).mpr hrev.symm
    nlinarith [ratio_pos c]
  let S : Set (Fin m) := Set.univ \ {c}
  let f (i : Fin m) := (c, i, i.rev)
  let g (i : Fin m) := (i, c, i.rev)
  let h (i : Fin m) := (i, i.rev, c)
  have hnot (i : Fin m) : i ∈ S ↔ i ≠ c := by simp [S]
  have hr (i : Fin m) : i.rev = c ↔ i = c := by
    constructor
    · intro hi
      simpa [hrev] using congrArg Fin.rev hi
    · rintro rfl
      exact hrev
  have heq : {t : Fin m × Fin m × Fin m |
      ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1 ∧
      (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)} =
      (f '' Set.univ ∪ g '' S) ∪ h '' S := by
    ext ⟨i,j,k⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_univ,
      true_and, hidx, hnot, f, g, h, Prod.mk.injEq]
    constructor
    · rintro ⟨ht, hm⟩
      by_cases hi : i=c
      · subst i
        left; left
        exact ⟨j,rfl,rfl,((pair_iff j k).mp (by simpa [hcenter] using ht)).symm⟩
      by_cases hj : j=c
      · subst j
        left; right
        exact ⟨i,hi,rfl,rfl,((pair_iff i k).mp (by simpa [hcenter] using ht)).symm⟩
      have hk : k=c := by tauto
      subst k
      exact Or.inr ⟨i,hi,rfl,((pair_iff i j).mp (by simpa [hcenter] using ht)).symm,rfl⟩
    · rintro ((⟨u,rfl,rfl,rfl⟩ | ⟨u,_,rfl,rfl,rfl⟩) | ⟨u,_,rfl,rfl,rfl⟩)
      all_goals constructor
      all_goals first | simpa only [hcenter, one_mul, mul_one] using (pair_iff u u.rev).mpr rfl | tauto
  have dfg : Disjoint (f '' Set.univ) (g '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj (congrArg Prod.fst e)
  have dfh : Disjoint (f '' Set.univ) (h '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj (congrArg Prod.fst e)
  have dgh : Disjoint (g '' S) (h '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj ((hr j).mp (congrArg (fun t => t.2.1) e))
  have hf : Function.Injective f := fun _ _ e => congrArg (fun t => t.2.1) e
  have hg : Function.Injective g := fun _ _ e => congrArg Prod.fst e
  have hh : Function.Injective h := fun _ _ e => congrArg Prod.fst e
  have du : Disjoint (f '' Set.univ ∪ g '' S) (h '' S) := disjoint_sup_left.mpr ⟨dfh,dgh⟩
  rw [heq, Set.ncard_union_eq du, Set.ncard_union_eq dfg,
      Set.ncard_image_of_injective _ hf, Set.ncard_image_of_injective _ hg,
      Set.ncard_image_of_injective _ hh]
  simp [S,m]
  omega

end A387471

namespace A387471

open OMA.S_oeis_a387471

def pattern (a b c : ℕ) : Prop :=
  [a,b,c].Perm [2,14,16] ∨ [a,b,c].Perm [4,6,18]

private theorem small_sine :
    Real.sin (3*Real.pi/10) = Real.sin (Real.pi/6) + Real.sin (Real.pi/10) := by
  rw [show 3*Real.pi/10=Real.pi/2-Real.pi/5 by ring, Real.sin_pi_div_two_sub,
    show Real.pi/10=Real.pi/2-2*(Real.pi/5) by ring, Real.sin_pi_div_two_sub,
    Real.cos_two_mul, Real.sin_pi_div_six]
  linarith [Real.quadratic_root_cos_pi_div_five]

noncomputable def gridRatio (a : ℕ) : ℝ :=
  Real.sin (a*Real.pi/60) / Real.sin (Real.pi/3-a*Real.pi/60)

private theorem grid_ratio_eq (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : a < 20) (hb' : b < 20) (hc' : c < 20) :
    gridRatio a * gridRatio b * gridRatio c = 1 ↔
      let x : ℤ := (a : ℤ)-10
      let y : ℤ := (b : ℤ)-10
      let z : ℤ := (c : ℤ)-10
      Real.sin (((x+y-z : ℤ) : ℝ)*Real.pi/60) +
      Real.sin (((y+z-x : ℤ) : ℝ)*Real.pi/60) +
      Real.sin (((z+x-y : ℤ) : ℝ)*Real.pi/60) = 0 := by
  have hd (j : ℕ) (hj : 0 < j) (hj' : j < 20) :
      Real.sin (Real.pi/3-j*Real.pi/60) ≠ 0 := by
    have hjr : (j : ℝ) < 20 := by exact_mod_cast hj'
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;>
      nlinarith [Real.pi_pos, mul_pos (sub_pos.mpr hjr) Real.pi_pos,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) j) Real.pi_pos.le]
  simp only [gridRatio,div_mul_div_comm,div_eq_one_iff_eq (mul_ne_zero
    (mul_ne_zero (hd a ha ha') (hd b hb hb')) (hd c hc hc'))]
  convert centered_ceva (((a:ℝ)-10)*Real.pi/60) (((b:ℝ)-10)*Real.pi/60)
    (((c:ℝ)-10)*Real.pi/60) using 1 <;> push_cast <;> ring_nf

private theorem first_grid_hit : gridRatio 2 * gridRatio 14 * gridRatio 16 = 1 := by
  apply (grid_ratio_eq 2 14 16 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mpr
  norm_num
  have h := small_sine
  ring_nf at h ⊢
  simp only [show Real.pi * (-1/6) = -(Real.pi * (1/6)) by ring,show Real.pi * (-1/10) = -(Real.pi * (1/10)) by ring,Real.sin_neg]
  linarith

private theorem second_grid_hit : gridRatio 4 * gridRatio 6 * gridRatio 18 = 1 := by
  apply (grid_ratio_eq 4 6 18 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mpr
  norm_num
  have h := small_sine
  ring_nf at h ⊢
  simp only [show Real.pi * (-3/10) = -(Real.pi * (3/10)) by ring,Real.sin_neg]
  linarith

theorem pattern_iff (a b c : ℕ) (ha : 0 < a ∧ a < 20 ∧ a ≠ 10)
    (hb : 0 < b ∧ b < 20 ∧ b ≠ 10) (hc : 0 < c ∧ c < 20 ∧ c ≠ 10) :
    gridRatio a * gridRatio b * gridRatio c = 1 ↔ pattern a b c := by
  constructor
  · intro hit
    have sorted (i j k : ℕ) (hi : 0 < i ∧ i < 20 ∧ i ≠ 10)
        (hj : 0 < j ∧ j < 20 ∧ j ≠ 10) (hk : 0 < k ∧ k < 20 ∧ k ≠ 10)
        (hij : i ≤ j) (hjk : j ≤ k) (ht : gridRatio i * gridRatio j * gridRatio k = 1) :=
      classify_grid i j k hi.1 hij hjk hk.2.1 hi.2.2 hj.2.2 hk.2.2
        ((grid_ratio_eq i j k hi.1 hj.1 hk.1 hi.2.1 hj.2.1 hk.2.1).mp ht)
    have order : (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨
      (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by omega
    rcases order with h | h | h | h | h | h
    · have e := sorted a b c ha hb hc h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
    · have e := sorted a c b ha hc hb h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
    · have e := sorted b a c hb ha hc h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
    · have e := sorted b c a hb hc ha h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
    · have e := sorted c a b hc ha hb h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
    · have e := sorted c b a hc hb ha h.1 h.2 (by simpa [mul_comm,mul_left_comm,mul_assoc] using hit)
      rcases e with e | e <;> simp only [Prod.mk.injEq] at e <;> rcases e with ⟨rfl,rfl,rfl⟩ <;> unfold pattern <;> decide
  · rintro (h | h)
    · have eq := (h.map gridRatio).prod_eq
      simpa [mul_assoc] using eq.trans (by simpa [mul_assoc] using first_grid_hit)
    · have eq := (h.map gridRatio).prod_eq
      simpa [mul_assoc] using eq.trans (by simpa [mul_assoc] using second_grid_hit)

end A387471

namespace A387471
open OMA.S_oeis_a387471

abbrev GridTriple := Fin 20 × Fin 20 × Fin 20

def allowed (r : ℕ) (t : GridTriple) : Prop :=
  let a := t.1.val
  let b := t.2.1.val
  let c := t.2.2.val
  (0 < a ∧ a ≠ 10) ∧ (0 < b ∧ b ≠ 10) ∧ (0 < c ∧ c ≠ 10) ∧
    pattern a b c ∧ (10 ∣ r*a ∧ 10 ∣ r*b ∧ 10 ∣ r*c)

instance (r : ℕ) (t : GridTriple) : Decidable (allowed r t) := by
  unfold allowed pattern
  infer_instance

private def table : Finset GridTriple :=
  Finset.univ.filter fun t => allowed 0 t

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 40000 in
private theorem table_list : table = {
    (2,14,16),(2,16,14),(14,2,16),(14,16,2),(16,2,14),(16,14,2),
    (4,6,18),(4,18,6),(6,4,18),(6,18,4),(18,4,6),(18,6,4)} := by decide +kernel

private theorem allowed_mod (n : ℕ) (t : GridTriple) :
    allowed n t ↔ allowed (n%10) t := by
  have mod_dvd (k : ℕ) : 10 ∣ n*k ↔ 10 ∣ (n%10)*k := by
    simp only [Nat.dvd_iff_mod_eq_zero,Nat.mod_mul_mod]
  unfold allowed
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr (mod_dvd _) (and_congr (mod_dvd _) (mod_dvd _))

private theorem table_count (n : ℕ) :
    Set.ncard {t : GridTriple | allowed n t} = if 5 ∣ n then 12 else 0 := by
  let r : Fin 10 := ⟨n%10, Nat.mod_lt _ (by decide)⟩
  let permitted (t : GridTriple) :=
    decide (10 ∣ r.val*t.1.val ∧ 10 ∣ r.val*t.2.1.val ∧ 10 ∣ r.val*t.2.2.val)
  have hset : {t : GridTriple | allowed n t} = ↑(table.filter (fun t => permitted t)) := by
    apply Set.ext
    intro t
    change allowed n t ↔ t ∈ table.filter (fun j => permitted j)
    rw [allowed_mod n]
    have ht : t ∈ table ↔ allowed 0 t :=
      ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    rw [Finset.mem_filter,ht]
    simp only [allowed,permitted,decide_eq_true_eq,r,zero_mul,dvd_zero,and_true]
    constructor
    · rintro ⟨a,b,c,p,d⟩
      exact ⟨⟨a,b,c,p⟩, d⟩
    · rintro ⟨⟨a,b,c,p⟩,d⟩
      exact ⟨a,b,c,p,d⟩
  rw [hset, Set.ncard_coe_finset, table_list]
  have hd : 5 ∣ n ↔ 5 ∣ r.val := by dsimp [r]; omega
  simp only [hd]
  change (Finset.filter (fun t : GridTriple => decide
    (10 ∣ r.val*t.1.val ∧ 10 ∣ r.val*t.2.1.val ∧ 10 ∣ r.val*t.2.2.val)) _).card = _
  generalize r = k
  fin_cases k <;> decide

private def ix {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1)) : Fin 20 :=
  ⟨10*(i.val+1)/n, by
    apply (Nat.div_lt_iff_lt_mul hn).mpr
    omega⟩

private theorem transfer {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n-1))
    (h : n ∣ 10*(i.val+1)) :
    ratio (2*n-1) i = gridRatio (ix hn i).val := by
  have he : (ix hn i).val*n = 10*(i.val+1) := Nat.div_mul_cancel h
  have hr : ((ix hn i).val : ℝ)*n = 10*(i.val+1 : ℝ) := by exact_mod_cast he
  have hm : ((2*n-1 : ℕ) : ℝ)+1 = 2*n := by
    exact_mod_cast (show 2*n-1+1=2*n by omega)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have angle : ((i.val : ℝ)+1)*Real.pi / (3*(((2*n-1 : ℕ):ℝ)+1)) =
      (ix hn i).val * Real.pi/60 := by
    rw [hm]
    field_simp
    linear_combination -6 * hr
  simp only [ratio,gridRatio,angle]

theorem exceptional_count (n : ℕ) (hn : 1 ≤ n) :
    Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
      ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧
      ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧
      (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))} =
    if 5 ∣ n then 12 else 0 := by
  let f (t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) : GridTriple :=
    (ix hn t.1, ix hn t.2.1, ix hn t.2.2)
  have np : n ≠ 0 := by omega
  have idx (i : Fin (2*n-1)) (h : n ∣ 10*(i.val+1)) :
      (ix hn i).val*n = 10*(i.val+1) := Nat.div_mul_cancel h
  have valid (i : Fin (2*n-1)) (h : n ∣ 10*(i.val+1)) (hm : i.val+1 ≠ n) :
      0 < (ix hn i).val ∧ (ix hn i).val < 20 ∧ (ix hn i).val ≠ 10 := by
    have he := idx i h
    refine ⟨Nat.pos_of_ne_zero ?_, (ix hn i).isLt, ?_⟩
    · intro e; rw [e,zero_mul] at he; omega
    · intro e; rw [e] at he; omega
  have divides (i : Fin (2*n-1)) (h : n ∣ 10*(i.val+1)) :
      10 ∣ n*(ix hn i).val := ⟨i.val+1, by rw [Nat.mul_comm,idx i h]⟩
  have inj (i j : Fin (2*n-1)) (hi : n ∣ 10*(i.val+1)) (hj : n ∣ 10*(j.val+1))
      (he : ix hn i = ix hn j) : i=j := by
    have := idx i hi
    rw [he,idx j hj] at this
    exact Fin.ext (by omega)
  have pre (k : Fin 20) (hk : 0 < k.val ∧ k.val ≠ 10) (hd : 10 ∣ n*k.val) :
      ∃ i : Fin (2*n-1), ix hn i = k ∧ n ∣ 10*(i.val+1) ∧ i.val+1 ≠ n := by
    obtain ⟨q,hq⟩ := hd
    have hpos := Nat.mul_pos hn hk.1
    have hlt := Nat.mul_lt_mul_of_pos_left k.isLt hn
    have hqpos : 0 < q := by omega
    let i : Fin (2*n-1) := ⟨q-1, by rw [Nat.mul_comm n 20] at hlt; omega⟩
    have hi : i.val+1=q := by dsimp [i]; omega
    have hd' : n ∣ 10*(i.val+1) := ⟨k.val, by rw [hi,hq]⟩
    refine ⟨i,?_,hd',?_⟩
    · apply Fin.ext
      apply Nat.eq_of_mul_eq_mul_right hn
      rw [idx i hd',hi,←hq,Nat.mul_comm]
    · intro he
      apply hk.2
      apply Nat.eq_of_mul_eq_mul_left hn
      rw [hq,←hi,he,Nat.mul_comm]
  rw [← table_count n]
  apply Set.BijOn.ncard_eq (f := f)
  constructor
  · rintro ⟨i,j,k⟩ ⟨hit,hm,di,dj,dk⟩
    have vi := valid i di (fun h => hm (Or.inl h))
    have vj := valid j dj (fun h => hm (Or.inr (Or.inl h)))
    have vk := valid k dk (fun h => hm (Or.inr (Or.inr h)))
    rw [transfer hn i di,transfer hn j dj,transfer hn k dk] at hit
    exact ⟨⟨vi.1,vi.2.2⟩,⟨vj.1,vj.2.2⟩,⟨vk.1,vk.2.2⟩,
      (pattern_iff _ _ _ vi vj vk).mp hit,divides i di,divides j dj,divides k dk⟩
  constructor
  · rintro ⟨i,j,k⟩ ⟨_,_,di,dj,dk⟩ ⟨u,v,w⟩ ⟨_,_,du,dv,dw⟩ e
    exact Prod.ext (inj i u di du (congrArg Prod.fst e))
      (Prod.ext (inj j v dj dv (congrArg (fun t => t.2.1) e))
        (inj k w dk dw (congrArg (fun t => t.2.2) e)))
  · rintro ⟨a,b,c⟩ ⟨ha,hb,hc,hp,da,db,dc⟩
    obtain ⟨i,hi,di,mi⟩ := pre a ha da
    obtain ⟨j,hj,dj,mj⟩ := pre b hb db
    obtain ⟨k,hk,dk,mk⟩ := pre c hc dc
    refine ⟨(i,j,k),⟨?_,by tauto,di,dj,dk⟩,Prod.ext hi (Prod.ext hj hk)⟩
    change ratio (2*n-1) i * ratio (2*n-1) j * ratio (2*n-1) k = 1
    rw [transfer hn i di,transfer hn j dj,transfer hn k dk,hi,hj,hk]
    exact (pattern_iff _ _ _ ⟨ha.1,a.isLt,ha.2⟩ ⟨hb.1,b.isLt,hb.2⟩
      ⟨hc.1,c.isLt,hc.2⟩).mpr hp

end A387471

namespace A387471

open Polynomial

theorem conjugate_sum {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {α : Type*} (s : Finset α) (e : α → ℕ) (k : ℕ) (hk : k.Coprime N)
    (h : ∑ i ∈ s, ζ^(e i) = 0) : ∑ i ∈ s, (ζ^k)^(e i) = 0 := by
  let P : ℤ[X] := ∑ i ∈ s, X^(e i)
  have hp : aeval ζ P = 0 := by simpa [P] using h
  have hd := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hN) hp
  rw [← cyclotomic_eq_minpoly hζ hN, cyclotomic_eq_minpoly (hζ.pow_of_coprime k hk) hN] at hd
  have hp' := (minpoly.isIntegrallyClosed_dvd_iff ((hζ.pow_of_coprime k hk).isIntegral hN) P).mpr hd
  simpa [P] using hp'

private theorem sum_powers {p : ℕ} {q : ℂ} (hq : q^p = 1) :
    ∑ j ∈ Finset.range p, q^j = if q=1 then (p : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr h)
    rw [geom_sum_mul,hq,sub_self]

theorem frequency_projection {α : Type*} (s : Finset α) (v r : α → ℂ)
    (p : ℕ) (a : ℂ) (ha : a^p=1) (hp : 0<p) (hr : ∀ i ∈ s, (r i)^p=1) :
    ∑ j ∈ Finset.range p, (∑ i ∈ s, v i * (r i)^j) / a^j =
    (∑ i ∈ s with r i=a, v i) * p := by
  classical
  have ha' : a ≠ 0 := by intro h; simp [h,zero_pow hp.ne'] at ha
  simp_rw [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hq : (r i/a)^p=1 := by rw [div_pow,hr i hi,ha,div_one]
  have hterm (j : ℕ) : v i * (r i)^j * (a^j)⁻¹ = v i * (r i/a)^j := by
    rw [div_pow,div_eq_mul_inv,mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum,sum_powers hq]
  simp only [div_eq_one_iff_eq ha']
  split_ifs <;> simp

theorem prime_split {α : Type*} (s : Finset α) (e : α → ℕ) (p d : ℕ)
    (hp : p.Prime) (hd : 0<d) {ζ : ℂ} (hz : IsPrimitiveRoot ζ (p*d))
    (h : ∑ i ∈ s, ζ^(e i) = 0) (hsmall : p ∣ d ∨ s.card < p) (a : ℕ) :
    ∑ i ∈ s with e i % p = a % p, ζ^(e i) = 0 := by
  classical
  let ρ := ζ^d
  have hr : IsPrimitiveRoot ρ p := by
    simpa [ρ,hd.ne'] using hz.pow_of_dvd hd.ne' (dvd_mul_left d p)
  have modpow (v : ℕ) : ρ^(v%p) = ρ^v := hr.eq_orderOf ▸ pow_mod_orderOf _ _
  have same (u v : ℕ) : ρ^u = ρ^v ↔ u%p = v%p := by
    rw [←modpow u,←modpow v]
    exact ⟨hr.pow_inj (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos),congrArg _⟩
  let F (j : ℕ) := ∑ i ∈ s, ζ^(e i) * (ρ^(e i))^j
  have proj (t : ℕ) : (∑ j ∈ Finset.range p, F j / (ρ^t)^j) =
      (∑ i ∈ s with e i % p = t % p, ζ^(e i)) * p := by
    have hpow (k : ℕ) : (ρ^k)^p=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,hr.pow_eq_one,one_pow]
    simpa only [F,same] using frequency_projection s (fun i => ζ^(e i))
      (fun i => ρ^(e i)) p (ρ^t) (hpow t) hp.pos (fun i _ => hpow _)
  have good (j : ℕ) (hj : ¬p ∣ 1+j*d) : F j=0 := by
    have cop : (1+j*d).Coprime (p*d) :=
      Nat.coprime_mul_iff_right.mpr ⟨(hp.coprime_iff_not_dvd.mpr hj).symm,
        (Nat.coprime_add_mul_right_left 1 d j).mpr (Nat.coprime_one_left _)⟩
    convert conjugate_sum (Nat.mul_pos hp.pos hd) hz s e (1+j*d) cop h using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ρ]
    rw [←pow_mul,←pow_mul,←pow_add,←pow_mul]
    congr 1
    ring
  have allzero (j : ℕ) (hj : j ∈ Finset.range p) : F j=0 := by
    by_cases hbad : p ∣ 1+j*d
    · have hnd : ¬p ∣ d := by
        intro hpd
        have h1 : p ∣ 1 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hpd j)).mpr hbad
        exact hp.not_dvd_one h1
      have hcard := hsmall.resolve_left hnd
      have hc : (s.image (fun i => e i % p)).card < (Finset.range p).card :=
        (Finset.card_image_le.trans_lt hcard).trans_eq (Finset.card_range p).symm
      obtain ⟨t,ht,htmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
      have ht' : t % p = t := Nat.mod_eq_of_lt (Finset.mem_range.mp ht)
      have hempty : (s.filter fun i => e i % p = t % p) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
        exact htmiss (Finset.mem_image.mpr ⟨i,hi,he.trans ht'⟩)
      have uniq (l : ℕ) (hl : l ∈ Finset.range p) (hne : l ≠ j) : F l = 0 := by
        apply good
        intro hbl
        have he := (Nat.modEq_zero_iff_dvd.mpr hbl).trans (Nat.modEq_zero_iff_dvd.mpr hbad).symm
        have he' := Nat.ModEq.cancel_right_of_coprime (hp.coprime_iff_not_dvd.mpr hnd)
          (Nat.ModEq.add_left_cancel' 1 he)
        apply hne
        simpa only [Nat.ModEq,Nat.mod_eq_of_lt (Finset.mem_range.mp hl),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] using he'
      have ht0 := proj t
      rw [hempty,Finset.sum_empty,zero_mul,Finset.sum_eq_single_of_mem j hj
        (fun l hl hne => by rw [uniq l hl hne,zero_div])] at ht0
      exact (div_eq_zero_iff.mp ht0).resolve_right (pow_ne_zero _ (pow_ne_zero _ (hr.isUnit hp.ne_zero).ne_zero))
    · exact good j hbad
  have hfin := proj a
  rw [Finset.sum_eq_zero (fun j hj => by rw [allzero j hj,zero_div])] at hfin
  exact (mul_eq_zero.mp hfin.symm).resolve_right (by exact_mod_cast hp.ne_zero)

private theorem bad_factor (N : ℕ) (hn : N ≠ 0) (bad : ¬N ∣ 30) :
    ∃ p d : ℕ, p.Prime ∧ N = p*d ∧ (p ∣ d ∨ 6 < p) := by
  by_contra! none
  have sf : Squarefree N := Nat.squarefree_iff_prime_squarefree.mpr (by
    intro p hp hpp
    obtain ⟨q,hq⟩ := hpp
    have eq : N = p*(p*q) := by rw [hq,Nat.mul_assoc]
    exact (none p (p*q) hp eq).1 (dvd_mul_right p q))
  apply bad
  rw [← Nat.prod_primeFactors_of_squarefree sf]
  apply (Nat.prod_primeFactors_dvd_iff (by decide : 30 ≠ 0)).mpr
  intro p h
  obtain ⟨hp,hpN,_⟩ := Nat.mem_primeFactors.mp h
  obtain ⟨d,hd⟩ := hpN
  have hle := (none p d hp hd).2
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp,?_,by decide⟩
  have small : ∀ q : Fin 7, q.val.Prime → q.val ∣ 30 := by decide
  exact small ⟨p,by omega⟩ hp

theorem mann_six {α : Type*} (s : Finset α) (hs : s.card ≤ 6) (N : ℕ)
    (hn : 0 < N) {ζ : ℂ} (hz : IsPrimitiveRoot ζ N) (e : α → ℕ)
    (h : ∑ i ∈ s, ζ^(e i) = 0)
    (irr : ∀ t : Finset α, t ⊆ s → t.Nonempty → (∑ i ∈ t, ζ^(e i)) = 0 → t=s)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) : (ζ^(e i))^30 = (ζ^(e j))^30 := by
  classical
  induction N using Nat.strong_induction_on generalizing ζ e with
  | h N ih =>
    by_cases divides : N ∣ 30
    · have hz30 := (hz.pow_eq_one_iff_dvd 30).mpr divides
      calc
        (ζ^(e i))^30 = (ζ^30)^(e i) := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ = (ζ^30)^(e j) := by rw [hz30,one_pow,one_pow]
        _ = (ζ^(e j))^30 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    obtain ⟨p,d,hp,heq,hbad⟩ := bad_factor N hn.ne' divides
    subst N
    have hd : 0 < d := Nat.pos_of_mul_pos_left hn
    have hdlt : d < p*d := by nlinarith [Nat.mul_le_mul_right d hp.two_le]
    have hsplit := prime_split s e p d hp hd hz h
      (hbad.imp_right (fun hlt => hs.trans_lt hlt)) (e i)
    let t := s.filter fun k => e k % p = e i % p
    have ht : t=s := irr t (Finset.filter_subset _ _) ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩ hsplit
    have hres : ∀ k ∈ s, e k % p = e i % p := Finset.filter_eq_self.mp ht
    let z := ζ^p
    have hz' : IsPrimitiveRoot z d := by
      simpa [z,hp.ne_zero] using hz.pow_of_dvd hp.ne_zero (dvd_mul_right p d)
    have factor (k : α) (hk : k ∈ s) :
        ζ^(e k) = ζ^(e i%p) * z^(e k/p) := by
      rw [←pow_mul,←pow_add,←hres k hk,Nat.mod_add_div]
    have hsumeq (u : Finset α) (hu : u ⊆ s) :
        ∑ k ∈ u, ζ^(e k) = ζ^(e i%p) * ∑ k ∈ u, z^(e k/p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k hk => factor k (hu hk))
    have hnz : ζ^(e i%p) ≠ 0 := pow_ne_zero _ (hz.isUnit hn.ne').ne_zero
    have hnew := (mul_eq_zero.mp ((hsumeq s (by rfl)).symm.trans h)).resolve_left hnz
    have hirr (u : Finset α) (hu : u ⊆ s) (hne : u.Nonempty)
        (hzero : ∑ k ∈ u, z^(e k/p)=0) : u=s := by
      exact irr u hu hne (by rw [hsumeq u hu,hzero,mul_zero])
    have hrec := ih d hdlt hd hz' (fun k => e k/p) hnew hirr
    rw [factor i hi,factor j hj,mul_pow,mul_pow,hrec]

end A387471

namespace A387471

noncomputable def unitAngle (a : ℝ) : ℂ := Complex.exp ((a : ℂ)*Complex.I)

private theorem unit_norm (a : ℝ) : ‖unitAngle a‖ = 1 := Complex.norm_exp_ofReal_mul_I a

private theorem wide_pair (a b : ℝ) (h : |a-b| < 2*Real.pi/3) :
    1 < ‖unitAngle a + unitAngle b‖ := by
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (a-b))
    (by linarith [Real.pi_pos] : 2*Real.pi/3 ≤ Real.pi) h
  have hcos : Real.cos (2*Real.pi/3) = -(1/2 : ℝ) := by
    rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
  rw [hcos,Real.cos_abs,Real.cos_sub] at hlt
  have hn := Complex.sq_norm (unitAngle a + unitAngle b)
  rw [Complex.normSq_apply] at hn
  simp only [Complex.add_re,Complex.add_im,unitAngle,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im] at hn
  change ‖Complex.exp ((a : ℂ)*Complex.I) + Complex.exp ((b : ℂ)*Complex.I)‖ > 1
  by_contra! hle
  nlinarith [Real.sin_sq_add_cos_sq a,Real.sin_sq_add_cos_sq b,
    mul_self_le_mul_self (norm_nonneg _) hle]

abbrev Six := Bool × Fin 3

noncomputable def sixRoot (a : Fin 3 → ℝ) (i : Six) : ℂ :=
  if i.1 then -starRingEnd ℂ (unitAngle (a i.2)) else unitAngle (a i.2)

theorem irreducible_six (a : Fin 3 → ℝ)
    (hb : ∀ i, -(Real.pi/2) < a i ∧ a i < Real.pi/2)
    (hd : ∀ i j, |a i - a j| < 2*Real.pi/3)
    (ho : ∀ i j, a i + a j ≠ 0)
    (hs : ∑ i : Six, sixRoot a i = 0) (t : Finset Six)
    (ht : t.Nonempty) (hz : ∑ i ∈ t, sixRoot a i = 0) : t=Finset.univ := by
  classical
  let z := sixRoot a
  have norm1 (i : Six) : ‖z i‖=1 := by
    obtain ⟨g,i⟩ := i
    cases g <;> simp [z,sixRoot,unit_norm]
  have positive (i : Fin 3) : 0 < (unitAngle (a i)).re := by
    rw [unitAngle,Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo (hb i)
  have sameSide (i j : Six) (hg : i.1=j.1) : 1 < ‖z i + z j‖ := by
    obtain ⟨g,i⟩ := i
    obtain ⟨g',j⟩ := j
    change g=g' at hg
    subst g'
    cases g
    · exact wide_pair _ _ (hd i j)
    · simpa [z,sixRoot,←neg_add,←map_add] using wide_pair _ _ (hd i j)
  have different (i j : Fin 3) : unitAngle (a i) - starRingEnd ℂ (unitAngle (a j)) ≠ 0 := by
    intro h
    have e := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [unitAngle,Complex.conj_im,Complex.exp_ofReal_mul_I_im] at e
    have en : a i = -(a j) := Real.strictMonoOn_sin.injOn
      ⟨(hb i).1.le,(hb i).2.le⟩ ⟨by linarith [(hb j).2], by linarith [(hb j).1]⟩
      (by simpa using e)
    exact ho i j (by linarith)
  have pair (i j : Six) : z i + z j ≠ 0 := by
    obtain ⟨g,i⟩ := i
    obtain ⟨g',j⟩ := j
    cases g <;> cases g'
    · intro e
      have hh := sameSide (false,i) (false,j) rfl
      rw [e,norm_zero] at hh; linarith
    · simpa [z,sixRoot,sub_eq_add_neg] using different i j
    · simpa [z,sixRoot,sub_eq_add_neg,add_comm] using different j i
    · intro e
      have hh := sameSide (true,i) (true,j) rfl
      rw [e,norm_zero] at hh; linarith
  have three (i j k : Six) (e : z i + z j + z k=0) : False := by
    have notsame (u v w : Six) (hg : u.1=v.1) (eq : z u + z v = -z w) : False := by
      have h := sameSide u v hg
      rw [eq,norm_neg,norm1] at h
      exact (lt_irrefl _ h)
    have eqs : i.1=j.1 ∨ i.1=k.1 ∨ j.1=k.1 := by
      cases i.1 <;> cases j.1 <;> cases k.1 <;> simp
    rcases eqs with h | h | h
    · exact notsame i j k h (by linear_combination e)
    · exact notsame i k j h (by linear_combination e)
    · exact notsame j k i h (by linear_combination e)
  have small (u : Finset Six) (hu : u.Nonempty) (hc : u.card ≤ 3)
      (eq : ∑ i ∈ u, z i = 0) : False := by
    have hpos := hu.card_pos
    interval_cases hcard : u.card
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hcard
      simp only [Finset.sum_singleton] at eq
      simpa [eq] using norm1 i
    · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hcard
      exact pair i j (by simpa [hij] using eq)
    · obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp hcard
      exact three i j k (by simpa [hij,hik,hjk,add_assoc] using eq)
  by_contra hne
  have hc : Fintype.card Six = 6 := by decide
  by_cases ht3 : t.card ≤ 3
  · exact small t ht ht3 hz
  · have hsum := Finset.sum_add_sum_compl t z
    change ∑ i : Six, z i = 0 at hs
    change ∑ i ∈ t, z i = 0 at hz
    rw [hz,hs,zero_add] at hsum
    exact small tᶜ (by simpa [Finset.nonempty_iff_ne_empty] using hne)
      (by rw [Finset.card_compl,hc]; omega) hsum

end A387471

namespace A387471

private theorem rear_angle (t : ℝ) :
    -starRingEnd ℂ (unitAngle t) = unitAngle (Real.pi-t) := by
  apply Complex.ext <;>
    simp only [unitAngle,Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,Real.cos_pi_sub,Real.sin_pi_sub,neg_neg]

private theorem int_angle_root (n : ℕ) (hn : 0<n) (u : ℤ) :
    unitAngle ((u : ℝ)*Real.pi/(6*n)) ^ (12*n) = 1 := by
  rw [unitAngle,←Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I u using 2
  push_cast
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

private theorem root_divides (n : ℕ) (hn : 0<n) (u : ℤ)
    (h : unitAngle ((u : ℝ)*Real.pi/(6*n)) ^ 30 =
      unitAngle (Real.pi-(u : ℝ)*Real.pi/(6*n)) ^ 30) :
    (n : ℤ) ∣ 5*u := by
  simp only [unitAngle,←Complex.exp_nat_mul] at h
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have he := congrArg Complex.im hk
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im, Complex.add_im] at he
  norm_num at he
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp at he
  refine ⟨15+k,?_⟩
  have ans : ((5 * u : ℤ) : ℝ) = (((n : ℤ)*(15+k) : ℤ) : ℝ) := by
    push_cast
    linear_combination he / 12
  exact_mod_cast ans

theorem orders_of_angles (n : ℕ) (hn : 0 < n) (u : Fin 3 → ℤ)
    (a : Fin 3 → ℝ) (hangle : ∀ i, a i = (u i : ℝ)*Real.pi/(6*n))
    (hb : ∀ i, -(Real.pi/2) < a i ∧ a i < Real.pi/2)
    (hd : ∀ i j, |a i-a j| < 2*Real.pi/3)
    (ho : ∀ i j, a i+a j ≠ 0)
    (hs : ∑ i : Six, sixRoot a i=0) (i : Fin 3) : (n : ℤ) ∣ 5*u i := by
  classical
  have hN : 0 < 12*n := by omega
  let ζ := Complex.exp (2*Real.pi*Complex.I/(12*n : ℕ))
  have hz : IsPrimitiveRoot ζ (12*n) := Complex.isPrimitiveRoot_exp _ hN.ne'
  letI : NeZero (12*n) := ⟨hN.ne'⟩
  have hpow (j : Six) : sixRoot a j ^ (12*n)=1 := by
    obtain ⟨g,j⟩ := j
    cases g
    · simpa [sixRoot,hangle] using int_angle_root n hn (u j)
    · simp only [sixRoot,if_true,rear_angle,hangle]
      convert int_angle_root n hn ((6:ℤ)*n-u j) using 3
      push_cast
      field_simp <;> ring
  choose e _ he using fun j => hz.eq_pow_of_pow_eq_one (hpow j)
  have hm := mann_six (Finset.univ : Finset Six) (by decide) (12*n) hN hz e
    (by simpa only [he] using hs)
    (fun t _ ht ht0 => irreducible_six a hb hd ho hs t ht (by simpa only [←he] using ht0))
    (false,i) (true,i) (Finset.mem_univ _) (Finset.mem_univ _)
  simp only [he,sixRoot,if_false,if_true,Bool.false_eq_true,rear_angle,hangle] at hm
  exact root_divides n hn (u i) hm

end A387471

namespace A387471
open OMA.S_oeis_a387471

private theorem no_opposite (A B C : ℝ)
    (ba : -(Real.pi/2)<A ∧ A<Real.pi/2) (bb : -(Real.pi/2)<B ∧ B<Real.pi/2)
    (bc : -(Real.pi/2)<C ∧ C<Real.pi/2)
    (ab : A+B ≠ 0) (ac : A+C ≠ 0) (bc' : B+C ≠ 0)
    (hs : Real.sin A + Real.sin B + Real.sin C=0) :
    ∀ i j : Fin 3, ![A,B,C] i + ![A,B,C] j ≠ 0 := by
  have opp (u v : ℝ) (bu : -(Real.pi/2)<u ∧ u<Real.pi/2)
      (bv : -(Real.pi/2)<v ∧ v<Real.pi/2) (h : Real.sin u + Real.sin v=0) : u+v=0 := by
    have e : u= -v := Real.strictMonoOn_sin.injOn ⟨bu.1.le,bu.2.le⟩
      ⟨by linarith [bv.2],by linarith [bv.1]⟩ (by rw [Real.sin_neg];linarith)
    linarith
  have ha : A ≠ 0 := by intro h; rw [h,Real.sin_zero,zero_add] at hs; exact bc' (opp B C bb bc hs)
  have hb : B ≠ 0 := by intro h; rw [h,Real.sin_zero,add_zero] at hs; exact ac (opp A C ba bc hs)
  have hc : C ≠ 0 := by intro h; rw [h,Real.sin_zero,add_zero] at hs; exact ab (opp A B ba bb hs)
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> intro eq <;> first
    | exact ha (by linarith only [eq])
    | exact hb (by linarith only [eq])
    | exact hc (by linarith only [eq])
    | exact ab (by linarith only [eq])
    | exact ac (by linarith only [eq])
    | exact bc' (by linarith only [eq])

private theorem sum_roots (A B C : ℝ) (hs : Real.sin A + Real.sin B + Real.sin C=0) :
    ∑ i : Six, sixRoot (![A,B,C]) i=0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.sum_univ_three, sixRoot, Bool.false_eq_true,
    if_false, if_true, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.neg_re,Complex.conj_re,Complex.zero_re]
    ring
  · simp only [Complex.add_im,Complex.neg_im,Complex.conj_im,Complex.zero_im,neg_neg,
      unitAngle,Complex.exp_ofReal_mul_I_im]
    change Real.sin A + Real.sin B + Real.sin C + (Real.sin A + Real.sin B + Real.sin C) = 0
    linarith

private theorem grid_centers (n : ℕ) (hn : 0<n) (X Y Z : ℤ) (x y z : ℝ)
    (hx : x = X*Real.pi/(6*n)) (hy : y = Y*Real.pi/(6*n)) (hz : z = Z*Real.pi/(6*n))
    (bx : -(Real.pi/6)<x ∧ x<Real.pi/6) (by' : -(Real.pi/6)<y ∧ y<Real.pi/6)
    (bz : -(Real.pi/6)<z ∧ z<Real.pi/6) (nx : x ≠ 0) (ny : y ≠ 0) (nz : z ≠ 0)
    (hs : Real.sin (x+y-z) + Real.sin (y+z-x) + Real.sin (z+x-y) = 0) :
    (n : ℤ) ∣ 10*X ∧ (n : ℤ) ∣ 10*Y ∧ (n : ℤ) ∣ 10*Z := by
  let u : Fin 3 → ℤ := ![X+Y-Z,Y+Z-X,Z+X-Y]
  let a : Fin 3 → ℝ := ![x+y-z,y+z-x,z+x-y]
  have he (i) : a i = (u i : ℝ)*Real.pi/(6*n) := by
    fin_cases i <;> simp [a,u,hx,hy,hz] <;> ring
  have hb (i) : -(Real.pi/2)<a i ∧ a i<Real.pi/2 := by
    fin_cases i <;> simp [a] <;> constructor <;>
      linarith [bx.1,bx.2,by'.1,by'.2,bz.1,bz.2]
  have hd (i j) : |a i-a j|<2*Real.pi/3 := by
    rw [abs_lt]
    fin_cases i <;> fin_cases j <;> constructor <;> simp [a] <;>
      linarith [bx.1,bx.2,by'.1,by'.2,bz.1,bz.2]
  have ho := no_opposite (x+y-z) (y+z-x) (z+x-y) (hb 0) (hb 1) (hb 2)
    (fun h => ny (by linarith only [h])) (fun h => nx (by linarith only [h]))
    (fun h => nz (by linarith only [h])) hs
  have h := orders_of_angles n hn u a he hb hd ho (sum_roots _ _ _ hs)
  have A := h 0
  have B := h 1
  have C := h 2
  change (n : ℤ) ∣ 5*(X+Y-Z) at A
  change (n : ℤ) ∣ 5*(Y+Z-X) at B
  change (n : ℤ) ∣ 5*(Z+X-Y) at C
  exact ⟨by rw [show 10*X=5*(X+Y-Z)+5*(Z+X-Y) by ring]; exact dvd_add A C,
    by rw [show 10*Y=5*(X+Y-Z)+5*(Y+Z-X) by ring]; exact dvd_add A B,
    by rw [show 10*Z=5*(Y+Z-X)+5*(Z+X-Y) by ring]; exact dvd_add B C⟩

theorem grid_restriction (n : ℕ) (hn : 1 ≤ n) (t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1))
    (hit : ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1)
    (hmed : ¬(t.1.val+1=n ∨ t.2.1.val+1=n ∨ t.2.2.val+1=n)) :
    n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1) := by
  obtain ⟨i,j,k⟩ := t
  let X (i : Fin (2*n-1)) : ℤ := (i.val : ℤ)+1-n
  let x (i : Fin (2*n-1)) : ℝ := (X i : ℝ)*Real.pi/(6*n)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have bound (i : Fin (2*n-1)) : -(Real.pi/6)<x i ∧ x i<Real.pi/6 := by
    have h1 : -(n : ℤ) < X i := by dsimp [X]; omega
    have h2 : X i < (n : ℤ) := by dsimp [X]; have := i.isLt; omega
    have h1' : -(n : ℝ) < (X i : ℝ) := by exact_mod_cast h1
    have h2' : (X i : ℝ) < n := by exact_mod_cast h2
    dsimp only [x]
    constructor
    · apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [mul_pos (sub_pos.mpr h1') Real.pi_pos]
    · apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_pos (sub_pos.mpr h2') Real.pi_pos]
  have nx (i : Fin (2*n-1)) (hi : i.val+1 ≠ n) : x i ≠ 0 := by
    have hx : X i ≠ 0 := by dsimp [X]; omega
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast hx) Real.pi_ne_zero) (by positivity)
  have frac (i : Fin (2*n-1)) : ratio (2*n-1) i =
      Real.sin (Real.pi/6+x i) / Real.sin (Real.pi/6-x i) := by
    have hm : ((2*n-1 : ℕ) : ℝ)+1 = 2*n := by exact_mod_cast (show 2*n-1+1=2*n by omega)
    unfold ratio
    rw [hm]
    have hangle : ((i.val : ℝ)+1)*Real.pi/(3*(2*n)) = Real.pi/6+x i := by
      dsimp [x,X]
      push_cast
      field_simp
      ring
    simp only [hangle,show Real.pi/3-(Real.pi/6+x i)=Real.pi/6-x i by ring]
  have hd (i : Fin (2*n-1)) : Real.sin (Real.pi/6-x i) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [(bound i).1,(bound i).2, Real.pi_pos]
  change ratio _ i * ratio _ j * ratio _ k = 1 at hit
  rw [frac,frac,frac,div_mul_div_comm,div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero (hd i) (hd j)) (hd k))] at hit
  have hs := (centered_ceva (x i) (x j) (x k)).mp hit
  obtain ⟨di,dj,dk⟩ := grid_centers n hn (X i) (X j) (X k) (x i) (x j) (x k)
    rfl rfl rfl (bound i) (bound j) (bound k) (nx i fun h => hmed (Or.inl h))
    (nx j fun h => hmed (Or.inr (Or.inl h))) (nx k fun h => hmed (Or.inr (Or.inr h))) hs
  have back (i : Fin (2*n-1)) (h : (n : ℤ) ∣ 10*X i) : n ∣ 10*(i.val+1) := by
    have d := dvd_add h (dvd_mul_left (n : ℤ) 10)
    have he : 10*X i + 10*(n : ℤ) = 10*((i.val : ℤ)+1) := by dsimp [X]; ring
    rw [he] at d
    exact_mod_cast d
  exact ⟨back i di,back j dj,back k dk⟩

end A387471

open OMA.S_oeis_a387471
open A387471

theorem OMA.solution : type_of% @OMA.S_oeis_a387471.main := by
  intro n hn
  let A : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)}
  let B : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧ (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))}
  have hab : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro t ht hs
    exact hs.2.1 ht.2
  have heq : {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1} = A ∪ B := by
    ext t
    constructor
    · intro ht
      by_cases hm : (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)
      · exact Or.inl ⟨ht, hm⟩
      · exact Or.inr ⟨ht, hm, grid_restriction n hn t ht hm⟩
    · rintro (ht | ht)
      · exact ht.1
      · exact ht.1
  unfold d
  rw [heq, Set.ncard_union_eq hab]
  have ha : A.ncard = 6*n-5 := median_count n hn
  have hb : B.ncard = if 5 ∣ n then 12 else 0 := exceptional_count n hn
  rw [ha, hb]
  split <;> omega

