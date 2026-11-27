import FormalConjectures.ErdosProblems.«856»
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The three-term harmonic LCM upper bound of Tang–Zhang (arXiv:2512.20055), using the Naslund–Sawin sunflower bound and a squarefree harmonic convolution. -/

open Finset

namespace TangZhangEuler

noncomputable def inversePower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' a b := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)

noncomputable def weight (z s : ℝ) (n : ℕ) : ℝ :=
  z ^ n.primeFactors.card * inversePower s n

theorem weight_one (z s : ℝ) : weight z s 1 = 1 := by
  simp [weight]

theorem weight_nonneg {z s : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ weight z s n := by
  exact mul_nonneg (pow_nonneg hz _) (Real.rpow_nonneg (by positivity) _)

theorem weight_mul {z s : ℝ} (hs : 0 < s) {a b : ℕ} (hc : Nat.Coprime a b) :
    weight z s (a * b) = weight z s a * weight z s b := by
  by_cases ha : a = 0
  · subst a
    simp [weight, inversePower, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  by_cases hb : b = 0
  · subst b
    simp [weight, inversePower, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  rw [weight, weight, weight, Nat.primeFactors_mul ha hb,
    card_union_of_disjoint hc.disjoint_primeFactors, pow_add, map_mul]
  ring

theorem weight_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (z s : ℝ) (j : ℕ) :
    weight z s (p ^ (j + 1)) = z * (inversePower s p) ^ (j + 1) := by
  rw [weight, Nat.primeFactors_pow_succ, hp.primeFactors, Finset.card_singleton, pow_one, map_pow]

theorem prime_inversePower_pos (s : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    0 < inversePower s p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

theorem prime_inversePower_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : Nat.Prime p) :
    inversePower s p < 1 := by
  change (p : ℝ) ^ (-s) < 1
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem summable_prime_power {z s : ℝ} (hz : 0 ≤ z) (hs : 0 < s) {p : ℕ}
    (hp : Nat.Prime p) : Summable (fun n : ℕ => ‖weight z s (p ^ n)‖) := by
  rw [← summable_nat_add_iff 1]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hz _), weight_prime_pow_succ hp, pow_succ]
  have hgeo := summable_geometric_of_lt_one (prime_inversePower_pos s hp).le
    (prime_inversePower_lt_one hs hp)
  simpa only [mul_assoc] using (hgeo.mul_right (inversePower s p)).mul_left z

theorem prime_weight_sum {z s : ℝ} (hz : 0 ≤ z) (hs : 0 < s) {p : ℕ}
    (hp : Nat.Prime p) :
    (∑' n : ℕ, weight z s (p ^ n)) =
      1 + z * (inversePower s p / (1 - inversePower s p)) := by
  rw [(summable_prime_power hz hs hp).of_norm.tsum_eq_zero_add]
  rw [pow_zero, weight_one]
  simp_rw [weight_prime_pow_succ hp, pow_succ]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one
    (prime_inversePower_pos s hp).le (prime_inversePower_lt_one hs hp)]
  congr 1
  rw [div_eq_mul_inv, mul_comm _ (inversePower s p)]

theorem prime_weight_le_geometric {z s : ℝ} (hz : 1 ≤ z) (hs : 0 < s) {p : ℕ}
    (hp : Nat.Prime p) :
    (∑' n : ℕ, weight z s (p ^ n)) ≤ (((1 - inversePower s p)⁻¹ : ℝ) ^ z) := by
  rw [prime_weight_sum (by linarith) hs hp]
  have ht := prime_inversePower_pos s hp
  have ht' := prime_inversePower_lt_one hs hp
  have he : 1 + inversePower s p / (1 - inversePower s p) = (1 - inversePower s p)⁻¹ := by
    have hs' : 1 - inversePower s p ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht')
    field_simp [hs']
    ring
  rw [← he]
  apply one_add_mul_self_le_rpow_one_add _ hz
  exact (by linarith : (-1 : ℝ) ≤ 0).trans (div_nonneg ht.le (by linarith))

theorem inversePower_summable {s : ℝ} (hs : 1 < s) :
    Summable (inversePower s) :=
  Real.summable_nat_rpow.mpr (by linarith : -s < -1)

theorem inversePower_tsum_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, inversePower s n) ≤ 1 + (s - 1)⁻¹ := by
  let f : ℝ → ℝ := fun x => x ^ (-s)
  have hanti : AntitoneOn f (Set.Ici 1) := by
    intro x hx y _ hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have hInt : MeasureTheory.IntegrableOn f (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnon (t : ℝ) (ht : t ∈ Set.Ioi 1) : 0 ≤ f t :=
    Real.rpow_nonneg (zero_le_one.trans ht.le) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := f) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hInt)
    (by simpa only [Nat.cast_one] using hnon)
  have hind : (∫ t in Set.Ioi (1 : ℝ), f t) = (s - 1)⁻¹ := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have he : -s + 1 = -(s - 1) := by ring
    rw [he, div_neg, neg_div, neg_neg, one_div]
  rw [Nat.cast_one, hind] at htail
  have hsum := inversePower_summable hs
  have hshift : Summable (fun n : ℕ => inversePower s (n + 1)) :=
    hsum.comp_injective Nat.succ_injective
  rw [hsum.tsum_eq_zero_add, hshift.tsum_eq_zero_add]
  have hzero : inversePower s 0 = 0 := by
    have hz : -s ≠ 0 := by linarith
    simp [inversePower, Real.zero_rpow hz]
  change (∑' n : ℕ, inversePower s (n + 1 + 1)) ≤ (s - 1)⁻¹ at htail
  rw [hzero, zero_add, zero_add, map_one]
  linarith

theorem weighted_series_bound {z s : ℝ} (hz : 1 ≤ z) (hs : 1 < s) (X : ℕ) :
    (∑ n ∈ Icc 1 X, weight z s n) ≤ (1 + (s - 1)⁻¹) ^ z := by
  classical
  have hz0 : 0 ≤ z := by linarith
  have hs0 : 0 < s := by linarith
  let P := range (X + 1)
  let S := P.filter Nat.Prime
  have hlocal : ∀ {p}, Nat.Prime p → Summable (fun n : ℕ => ‖weight z s (p ^ n)‖) :=
    summable_prime_power hz0 hs0
  obtain ⟨hsum, hfac⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (weight_one z s) (weight_mul hs0) hlocal P
  have hfactored (n : ℕ) (hn : n ∈ Icc 1 X) : n ∈ Nat.factoredNumbers P := by
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    refine Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) ?_
    intro p hp
    have hpn := Nat.le_of_dvd (by omega : 0 < n) (Nat.dvd_of_mem_primeFactors hp)
    exact mem_range.mpr (by omega)
  let emb : {n // n ∈ Icc 1 X} ↪ Nat.factoredNumbers P :=
    ⟨fun n => ⟨n, hfactored n n.property⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun x : Nat.factoredNumbers P => (x : ℕ)) h)⟩
  have hfin :
      (∑ n ∈ Icc 1 X, weight z s n) ≤ ∑' n : Nat.factoredNumbers P, weight z s n := by
    calc
      _ = ∑ n ∈ ((Icc 1 X).attach.map emb), weight z s n := by
        rw [sum_map, ← sum_attach (Icc 1 X) (weight z s)]
        rfl
      _ ≤ _ := by
        exact Summable.sum_le_tsum _ (fun (n : Nat.factoredNumbers P) _ => weight_nonneg hz0 (n : ℕ))
          hsum.of_norm
  have hprod_nonneg (p : ℕ) (hp : p ∈ S) : 0 ≤ (1 - inversePower s p)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr (prime_inversePower_lt_one hs0 (mem_filter.mp hp).2).le)
  have hZ : (∏ p ∈ S, (1 - inversePower s p)⁻¹) ≤ 1 + (s - 1)⁻¹ := by
    change (∏ p ∈ P with p.Prime, (1 - inversePower s p)⁻¹) ≤ _
    rw [EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
      (inversePower_summable hs) P]
    exact ((inversePower_summable hs).tsum_subtype_le (inversePower s) (Nat.factoredNumbers P)
      (fun n => Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _)).trans (inversePower_tsum_le hs)
  calc
    _ ≤ ∑' n : Nat.factoredNumbers P, weight z s n := hfin
    _ = ∏ p ∈ S, ∑' j : ℕ, weight z s (p ^ j) := hfac.tsum_eq
    _ ≤ ∏ p ∈ S, (((1 - inversePower s p)⁻¹ : ℝ) ^ z) := by
      refine prod_le_prod (fun p _ => tsum_nonneg (fun j => weight_nonneg hz0 _)) ?_
      intro p hp
      exact prime_weight_le_geometric hz hs0 (mem_filter.mp hp).2
    _ = (∏ p ∈ S, (1 - inversePower s p)⁻¹) ^ z :=
      Real.finsetProd_rpow _ _ hprod_nonneg _
    _ ≤ _ := Real.rpow_le_rpow (prod_nonneg hprod_nonneg) hZ hz0

theorem weighted_harmonic_le {z : ℝ} (hz : 1 ≤ z) {X : ℕ} (hX : 2 ≤ X) :
    (∑ m ∈ Icc 1 X, z ^ m.primeFactors.card / (m : ℝ)) ≤
      Real.exp 1 * (1 + Real.log X) ^ z := by
  have hz0 : 0 ≤ z := by linarith
  have hX1 : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hX0 : 0 < (X : ℝ) := by linarith
  have hlog := Real.log_pos hX1
  let s := (1 : ℝ) + (Real.log X)⁻¹
  have hs : 1 < s := lt_add_of_pos_right _ (inv_pos.mpr hlog)
  have htop : (X : ℝ) ^ ((Real.log X)⁻¹) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hX0, mul_inv_cancel₀ hlog.ne']
  have hterms (m : ℕ) (hm : m ∈ Icc 1 X) :
      z ^ m.primeFactors.card / (m : ℝ) ≤ Real.exp 1 * weight z s m := by
    obtain ⟨hm1, hmX⟩ := mem_Icc.mp hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have ha : (m : ℝ) ^ ((Real.log X)⁻¹) ≤ Real.exp 1 := by
      rw [← htop]
      exact Real.rpow_le_rpow hm0.le (by exact_mod_cast hmX) (inv_nonneg.mpr hlog.le)
    have hre : -s + (Real.log X)⁻¹ = -1 := by dsimp [s]; ring
    calc
      _ = (z ^ m.primeFactors.card * (m : ℝ) ^ (-s)) * (m : ℝ) ^ ((Real.log X)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add hm0, hre, Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := by
        rw [weight, mul_comm (Real.exp 1)]
        exact mul_le_mul_of_nonneg_left ha (mul_nonneg (pow_nonneg hz0 _) (Real.rpow_nonneg hm0.le _))
  have hs' : (s - 1)⁻¹ = Real.log X := by
    dsimp [s]
    rw [add_comm, add_sub_cancel_right, inv_inv]
  calc
    _ ≤ ∑ m ∈ Icc 1 X, Real.exp 1 * weight z s m := sum_le_sum hterms
    _ = Real.exp 1 * ∑ m ∈ Icc 1 X, weight z s m := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs' ▸ weighted_series_bound hz hs X) (Real.exp_nonneg _)

theorem weighted_harmonic_square_le {z : ℝ} (hz : 1 ≤ z) {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    (∑ m ∈ Icc 1 (N * N), z ^ m.primeFactors.card / (m : ℝ)) ≤
      (Real.exp 1 * 3 ^ z) * (Real.log N) ^ z := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  refine (weighted_harmonic_le hz (hX := by nlinarith)).trans ?_
  rw [Nat.cast_mul, Real.log_mul hN0.ne' hN0.ne', mul_assoc, ← Real.mul_rpow (by norm_num)
    (by linarith : 0 ≤ Real.log (N : ℝ))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)) (Real.exp_nonneg _)

end TangZhangEuler

/- Squarefree multiplier fibers for the harmonic LCM bound of Tang and Zhang. -/

open Finset
open scoped BigOperators

namespace SunflowerFiber

def ThreeFree (F : Finset (Finset ℕ)) : Prop :=
  ¬ ∃ U V W : Finset ℕ, U ∈ F ∧ V ∈ F ∧ W ∈ F ∧
    U ≠ V ∧ U ≠ W ∧ V ≠ W ∧ U ∩ V = U ∩ W ∧ U ∩ V = V ∩ W

def squarefreeUpTo (N : ℕ) : Finset ℕ := (Icc 1 N).filter Squarefree

def fiber (A B : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun p => p.1 * p.2 = m

def supports (A B : Finset ℕ) (m : ℕ) : Finset (Finset ℕ) :=
  (fiber A B m).image fun p => p.2.primeFactors

private theorem fiber_mem {A B : Finset ℕ} {m : ℕ} {p : ℕ × ℕ} :
    p ∈ fiber A B m ↔ p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 = m := by
  simp only [fiber, mem_filter, mem_product, and_assoc]

private theorem fst_nonzero {p : ℕ × ℕ} {m : ℕ} (hm : m ≠ 0) (hp : p.1 * p.2 = m) :
    p.1 ≠ 0 := fun h => hm (by simpa [h] using hp.symm)

private theorem snd_nonzero {p : ℕ × ℕ} {m : ℕ} (hm : m ≠ 0) (hp : p.1 * p.2 = m) :
    p.2 ≠ 0 := fun h => hm (by simpa [h] using hp.symm)

private theorem equal_fst_forces_equal {p q : ℕ × ℕ} {m : ℕ}
    (hm : m ≠ 0) (hp : p.1 * p.2 = m) (hq : q.1 * q.2 = m) (h : p.1 = q.1) :
    p = q :=
  Prod.ext h (mul_left_cancel₀ (fst_nonzero hm hp) (by rw [hp, h, hq]))

private theorem equal_support_forces_equal {p q : ℕ × ℕ} {m : ℕ}
    (hp : p.1 * p.2 = m) (hq : q.1 * q.2 = m)
    (hb : Squarefree p.2) (hc : Squarefree q.2) (h : p.2.primeFactors = q.2.primeFactors) :
    p = q := by
  have hbq : p.2 = q.2 := by
    rw [← Nat.prod_primeFactors_of_squarefree hb, ← Nat.prod_primeFactors_of_squarefree hc, h]
  exact Prod.ext (mul_right_cancel₀ hb.ne_zero (by rw [hp, hbq, hq])) hbq

private theorem mul_gcd_lcm {a b c d m : ℕ} (hc : c ≠ 0) (hp : a*b = m) (hq : c*d = m) :
    b.gcd d * a.lcm c = m := by
  have he : (a.gcd c) * b = c * (b.gcd d) := by
    calc
      _ = (a*b).gcd (c*b) := (Nat.gcd_mul_right _ _ _).symm
      _ = (c*d).gcd (c*b) := by rw [hp, hq]
      _ = _ := by rw [Nat.gcd_mul_left, Nat.gcd_comm d b]
  apply mul_left_cancel₀ hc
  calc
    c * (b.gcd d * a.lcm c) = ((a.gcd c)*b) * a.lcm c := by rw [← mul_assoc, ← he]
    _ = (a.gcd c * a.lcm c) * b := by ac_rfl
    _ = c * m := by rw [Nat.gcd_mul_lcm, ← hp]; ac_rfl

private theorem gcd_of_support_inter {b d : ℕ} (hb : Squarefree b) (hd : Squarefree d) :
    b.gcd d = ∏ e ∈ b.primeFactors ∩ d.primeFactors, e := by
  rw [← Nat.primeFactors_gcd hb.ne_zero hd.ne_zero]
  exact (Nat.prod_primeFactors_of_squarefree (hb.squarefree_of_dvd (Nat.gcd_dvd_left b d))).symm

private theorem lcm_of_support_inter {p q : ℕ × ℕ} {m : ℕ}
    (hm : m ≠ 0) (hp : p.1*p.2 = m) (hq : q.1*q.2 = m)
    (hb : Squarefree p.2) (hc : Squarefree q.2) :
    p.1.lcm q.1 = m / (∏ e ∈ p.2.primeFactors ∩ q.2.primeFactors, e) := by
  rw [← gcd_of_support_inter hb hc, ← mul_gcd_lcm (fst_nonzero hm hq) hp hq]
  exact (Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hb.ne_zero))).symm

theorem supports_card {A B : Finset ℕ} {m : ℕ} (hB : ∀ b ∈ B, Squarefree b) :
    (supports A B m).card = (fiber A B m).card := by
  apply card_image_of_injOn
  intro p hp q hq he
  obtain ⟨_, hpb, hpm⟩ := fiber_mem.1 hp
  obtain ⟨_, hqb, hqm⟩ := fiber_mem.1 hq
  exact equal_support_forces_equal hpm hqm (hB _ hpb) (hB _ hqb) he

theorem supports_subset {A B : Finset ℕ} {m : ℕ} (hm : m ≠ 0)
    (U : Finset ℕ) (hU : U ∈ supports A B m) : U ⊆ m.primeFactors := by
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hU
  have hm' := (fiber_mem.1 hp).2.2
  intro e he
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.1 he
  exact hprime.mem_primeFactors (hdiv.trans ⟨p.1, by rw [mul_comm, hm']⟩) hm

theorem supports_threeFree {A B : Finset ℕ} {m : ℕ} (hm : m ≠ 0)
    (hB : ∀ b ∈ B, Squarefree b) (hfree : ¬ Erdos856.HasEqualLcmTuple 3 A) :
    ThreeFree (supports A B m) := by
  rintro ⟨U,V,W,hU,hV,hW,hUV,hUW,hVW,hI,hJ⟩
  obtain ⟨p,hp,rfl⟩ := mem_image.1 hU
  obtain ⟨q,hq,rfl⟩ := mem_image.1 hV
  obtain ⟨r,hr,rfl⟩ := mem_image.1 hW
  obtain ⟨hpa,hpb,hpm⟩ := fiber_mem.1 hp
  obtain ⟨hqa,hqb,hqm⟩ := fiber_mem.1 hq
  obtain ⟨hra,hrb,hrm⟩ := fiber_mem.1 hr
  have hpq : p.1 ≠ q.1 := fun h => hUV (congrArg (fun t : ℕ × ℕ => t.2.primeFactors)
    (equal_fst_forces_equal hm hpm hqm h))
  have hpr : p.1 ≠ r.1 := fun h => hUW (congrArg (fun t : ℕ × ℕ => t.2.primeFactors)
    (equal_fst_forces_equal hm hpm hrm h))
  have hqr : q.1 ≠ r.1 := fun h => hVW (congrArg (fun t : ℕ × ℕ => t.2.primeFactors)
    (equal_fst_forces_equal hm hqm hrm h))
  have hpqc := lcm_of_support_inter hm hpm hqm (hB _ hpb) (hB _ hqb)
  have hprc := lcm_of_support_inter hm hpm hrm (hB _ hpb) (hB _ hrb)
  have hqrc := lcm_of_support_inter hm hqm hrm (hB _ hqb) (hB _ hrb)
  rw [← hI] at hprc
  rw [← hJ] at hqrc
  apply hfree
  let L := m / (∏ e ∈ p.2.primeFactors ∩ q.2.primeFactors, e)
  refine ⟨{p.1,q.1,r.1}, ?_, ?_, L, ?_⟩
  · exact insert_subset hpa (insert_subset hqa (singleton_subset_iff.2 hra))
  · simp [hpq, hpr, hqr]
  · intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hpqc
    · exact hprc
    · rw [Nat.lcm_comm]; exact hpqc
    · exact (hab rfl).elim
    · exact hqrc
    · rw [Nat.lcm_comm]; exact hprc
    · rw [Nat.lcm_comm]; exact hqrc
    · exact (hab rfl).elim

theorem harmonic_product_le_of_sunflower_bound {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hfree : ¬ Erdos856.HasEqualLcmTuple 3 A)
    {C z : ℝ}
    (hbound : ∀ (P : Finset ℕ) (F : Finset (Finset ℕ)),
      (∀ U ∈ F, U ⊆ P) → ThreeFree F → (F.card : ℝ) ≤ C * z ^ P.card) :
    (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ b ∈ squarefreeUpTo N, (b : ℝ)⁻¹) ≤
      C * ∑ m ∈ Icc 1 (N*N), z ^ m.primeFactors.card / (m : ℝ) := by
  let B := squarefreeUpTo N
  have hBsub : B ⊆ Icc 1 N := filter_subset _ _
  have hB : ∀ b ∈ B, Squarefree b := fun _ hb => (mem_filter.1 hb).2
  have hmap : ∀ p ∈ A ×ˢ B, p.1 * p.2 ∈ Icc 1 (N*N) := by
    intro p hp
    obtain ⟨ha, hb⟩ := mem_product.1 hp
    obtain ⟨ha0, haN⟩ := mem_Icc.1 (hA ha)
    obtain ⟨hb0, hbN⟩ := mem_Icc.1 (hBsub hb)
    exact mem_Icc.2 ⟨by simpa using Nat.mul_le_mul ha0 hb0, Nat.mul_le_mul haN hbN⟩
  have hfiber (m : ℕ) (hm : m ∈ Icc 1 (N*N)) :
      ((fiber A B m).card : ℝ) ≤ C * z ^ m.primeFactors.card := by
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    rw [← supports_card hB]
    exact hbound _ _ (supports_subset hm0) (supports_threeFree hm0 hB hfree)
  change (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ b ∈ B, (b : ℝ)⁻¹) ≤ _
  calc
    _ = ∑ p ∈ A ×ˢ B, ((p.1 * p.2 : ℕ) : ℝ)⁻¹ := by
      rw [sum_mul, sum_product]
      simp_rw [mul_sum, Nat.cast_mul, mul_inv_rev, mul_comm]
    _ = ∑ m ∈ Icc 1 (N*N), ∑ p ∈ fiber A B m, ((p.1*p.2 : ℕ) : ℝ)⁻¹ :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ m ∈ Icc 1 (N*N), ((fiber A B m).card : ℝ) / (m : ℝ) := by
      apply sum_congr rfl
      intro m _
      calc
        _ = ∑ _p ∈ fiber A B m, (m : ℝ)⁻¹ := by
          apply sum_congr rfl
          intro p hp
          rw [(fiber_mem.1 hp).2.2]
        _ = _ := by simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hfiber m hm) (by positivity)

theorem threeFree_of_subset {F G : Finset (Finset ℕ)} (hFG : F ⊆ G) (hG : ThreeFree G) :
    ThreeFree F := by
  rintro ⟨U,V,W,hU,hV,hW,rest⟩
  exact hG ⟨U,V,W,hFG hU,hFG hV,hFG hW,rest⟩

private theorem absorb_card_levels {z η : ℝ} (hz : 0 < z) (hη : 0 < η) (n : ℕ) :
    (n : ℝ) + 1 ≤ (1 + z / η) * (1 + η / z)^n := by
  have hq : 0 ≤ η/z := by positivity
  have hber : 1 + (n : ℝ)*(η/z) ≤ (1+η/z)^n :=
    one_add_mul_le_pow (by linarith) n
  have hn : (n : ℝ) ≤ (z/η)*(1+η/z)^n := by
    calc
      (n : ℝ) = (z/η) * ((n : ℝ) * (η/z)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hp : 1 ≤ (1+η/z)^n := (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hq)).trans hber
  rw [add_mul,one_mul]
  linarith only [hn,hp]

/-- Applying a uniform-family bound at each cardinality enlarges the exponential base only by η. -/
theorem nonuniform_bound_of_uniform {C z η : ℝ} (hC : 0 ≤ C) (hz : 0 < z) (hη : 0 < η)
    (huniform : ∀ (P : Finset ℕ) (F : Finset (Finset ℕ)) (k : ℕ),
      (∀ U ∈ F, U ⊆ P) → ThreeFree F → (∀ U ∈ F, U.card = k) →
        (F.card : ℝ) ≤ C * z ^ P.card)
    (P : Finset ℕ) (F : Finset (Finset ℕ)) (hsub : ∀ U ∈ F, U ⊆ P) (hfree : ThreeFree F) :
    (F.card : ℝ) ≤ (C * (1 + z / η)) * (z+η) ^ P.card := by
  have hmaps : (F : Set (Finset ℕ)).MapsTo Finset.card (range (P.card+1)) := by
    intro U hU
    exact mem_range.2 (Nat.lt_succ_of_le (card_le_card (hsub U hU)))
  have hfiber (k : ℕ) :
      ((F.filter fun U => U.card = k).card : ℝ) ≤ C * z ^ P.card :=
    huniform P _ k (fun U hU => hsub U (mem_filter.1 hU).1)
      (threeFree_of_subset (filter_subset _ _) hfree) (fun _ hU => (mem_filter.1 hU).2)
  calc
    (F.card : ℝ) = ∑ k ∈ range (P.card+1), ((F.filter fun U => U.card = k).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _k ∈ range (P.card+1), C * z ^ P.card := sum_le_sum fun k _ => hfiber k
    _ = (C * ((P.card : ℝ)+1)) * z ^ P.card := by
      simp [nsmul_eq_mul]
      ring
    _ ≤ (C * ((1 + z/η) * (1+η/z)^P.card)) * z ^ P.card := by
      gcongr
      exact absorb_card_levels hz hη _
    _ = _ := by
      have he : (1 + η/z)*z = z+η := by field_simp
      rw [← he, mul_pow]
      ring

end SunflowerFiber

/- A lower bound for the squarefree harmonic mass and absorption of a constant. -/

open Finset Filter
open scoped Topology

namespace Squarefree856

noncomputable def harmonic (N : ℕ) : ℝ :=
  ∑ b ∈ (Icc 1 N).filter Squarefree, (b : ℝ)⁻¹

private noncomputable def allHarmonic (N : ℕ) : ℝ := ∑ b ∈ Icc 1 N, (b : ℝ)⁻¹

private noncomputable def badHarmonic (N : ℕ) : ℝ :=
  ∑ b ∈ (Icc 1 N).filter (fun b => ¬Squarefree b), (b : ℝ)⁻¹

private theorem bad_divisor {b N : ℕ} (hb : b ∈ Icc 1 N) (hs : ¬Squarefree b) :
    ∃ d ∈ Icc 2 N, d^2 ∣ b := by
  have hB := mem_Icc.mp hb
  unfold Squarefree at hs
  push Not at hs
  obtain ⟨d,hd,hdU⟩ := hs
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
    omega
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdU isUnit_one
  have hdb : d*d ≤ b := Nat.le_of_dvd (by omega) hd
  have hdd : d ≤ d*d := Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero hd0)
  exact ⟨d,mem_Icc.mpr ⟨by omega,hdd.trans (hdb.trans hB.2)⟩,by rwa [pow_two]⟩

private theorem square_divisor_sum {N d : ℕ} (hd : 0 < d) :
    (∑ b ∈ (Icc 1 N).filter (fun b => d^2∣b), (b : ℝ)⁻¹) ≤
      ((d : ℝ)^2)⁻¹ * allHarmonic N := by
  let e : ℕ ↪ ℕ := ⟨fun k => d^2*k,fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hd _) h⟩
  have hSub : (Icc 1 N).filter (fun b => d^2∣b) ⊆ (Icc 1 N).map e := by
    intro b hb
    obtain ⟨hB,hD⟩ := mem_filter.mp hb
    obtain ⟨k,rfl⟩ := hD
    have hk : 1 ≤ k := by
      have h := (mem_Icc.mp hB).1
      by_contra! h'
      have h0 : k = 0 := by omega
      simp [h0] at h
    have hKN : k≤N :=
      (Nat.le_mul_of_pos_left _ (pow_pos hd _)).trans (mem_Icc.mp hB).2
    exact mem_map.mpr ⟨k,mem_Icc.mpr ⟨hk,hKN⟩,rfl⟩
  calc
    _ ≤ ∑ b ∈ (Icc 1 N).map e, (b : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hSub (fun b _ _ => by positivity)
    _ = _ := by
      rw [sum_map,allHarmonic,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change (((d^2*k : ℕ) : ℝ))⁻¹ = _
      rw [Nat.cast_mul,Nat.cast_pow,mul_inv]

private theorem bad_mass (N : ℕ) :
    badHarmonic N ≤ (∑ d ∈ Icc 2 N, ((d : ℝ)^2)⁻¹)*allHarmonic N := by
  classical
  let F (b d : ℕ) : ℝ := if d^2∣b then (b : ℝ)⁻¹ else 0
  have hF (b d : ℕ) : 0 ≤ F b d := by unfold F; positivity
  calc
    _ ≤ ∑ b ∈ (Icc 1 N).filter (fun b => ¬Squarefree b), ∑ d ∈ Icc 2 N, F b d := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨d,hd,hD⟩ := bad_divisor (mem_filter.mp hb).1 (mem_filter.mp hb).2
      have h := Finset.single_le_sum (f := F b) (fun d _ => hF b d) hd
      simpa [F,hD] using h
    _ ≤ ∑ b ∈ Icc 1 N, ∑ d ∈ Icc 2 N, F b d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun b _ _ =>
        Finset.sum_nonneg (fun d _ => hF b d))
    _ = ∑ d ∈ Icc 2 N, ∑ b ∈ Icc 1 N, F b d := Finset.sum_comm
    _ = ∑ d ∈ Icc 2 N, ∑ b ∈ (Icc 1 N).filter (fun b => d^2∣b), (b : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [sum_filter]
    _ ≤ _ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun d hd => square_divisor_sum (zero_lt_two.trans_le (mem_Icc.mp hd).1))

private theorem inv_sq_telescopes (n : ℕ) :
    (∑ d ∈ Icc 2 (n+2), ((d : ℝ)^2)⁻¹) ≤ (3/4 : ℝ)-((n+2 : ℕ) : ℝ)⁻¹ := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n.succ+2=(n+2)+1 by omega,Finset.sum_Icc_succ_top (by omega)]
    let x : ℝ := (n : ℝ)+2
    have hx : 0 < x := by dsimp [x]; positivity
    have hx1 : 0 < x+1 := by positivity
    have hD : x*(x+1) ≤ (x+1)^2 := by nlinarith
    have hS : ((x+1)^2)⁻¹ ≤ x⁻¹-(x+1)⁻¹ := by
      calc
        _ ≤ (x*(x+1))⁻¹ := inv_anti₀ (mul_pos hx hx1) hD
        _ = _ := by field_simp [hx.ne',hx1.ne']; ring
    push_cast at ih ⊢
    change (∑ d ∈ Icc 2 (n+2), ((d : ℝ)^2)⁻¹)+((x+1)^2)⁻¹ ≤ 3/4-(x+1)⁻¹
    change (∑ d ∈ Icc 2 (n+2), ((d : ℝ)^2)⁻¹) ≤ 3/4-x⁻¹ at ih
    linarith

private theorem inv_sq_sum (N : ℕ) :
    (∑ d ∈ Icc 2 N, ((d : ℝ)^2)⁻¹) ≤ (3/4 : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Icc 2 (N+2), ((d : ℝ)^2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (by
        intro d hd
        exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (by omega)⟩)
        (fun d _ _ => by positivity)
    _ ≤ 3/4-((N+2 : ℕ) : ℝ)⁻¹ := inv_sq_telescopes N
    _ ≤ _ := sub_le_self _ (by positivity)

theorem harmonic_lower (N : ℕ) : (1/4 : ℝ)*allHarmonic N ≤ harmonic N := by
  have hAll : 0≤allHarmonic N := Finset.sum_nonneg (fun _ _ => by positivity)
  have hBad := (bad_mass N).trans (mul_le_mul_of_nonneg_right (inv_sq_sum N) hAll)
  have hPart : harmonic N+badHarmonic N=allHarmonic N :=
    Finset.sum_filter_add_sum_filter_not (Icc 1 N) Squarefree _
  linarith

/-- The harmonic mass of the squarefree integers is at least a quarter of the logarithm. -/
theorem log_lower (N : ℕ) : (1/4 : ℝ)*Real.log (N : ℝ) ≤ harmonic N := by
  have h : Real.log (N : ℝ) ≤ allHarmonic N := by
    simpa only [Nat.floor_natCast, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, allHarmonic] using log_le_harmonic_floor (N : ℝ) (by positivity)
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ)≤1/4)).trans (harmonic_lower N)

/-- Divide by the squarefree harmonic mass and absorb a constant into a log power. -/
theorem absorb {F : ℕ → ℝ} {C z ε : ℝ} (_hC : 0<C) (hε : 0<ε)
    (hF : ∀ᶠ N : ℕ in atTop, F N*harmonic N ≤ C*(Real.log (N : ℝ))^z) :
    ∀ᶠ N : ℕ in atTop, F N ≤ (Real.log (N : ℝ))^(z-1+ε) := by
  have hLog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPow : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hLog
  filter_upwards [hF,hLog.eventually_gt_atTop (0 : ℝ),hPow.eventually_ge_atTop (4*C)]
    with N hN hlog hconst
  let l := Real.log (N : ℝ)
  have hl : 0 < l := hlog
  by_cases hF0 : F N ≤ 0
  · exact hF0.trans (Real.rpow_nonneg hl.le _)
  have hMass := mul_le_mul_of_nonneg_left (log_lower N) (le_of_not_ge hF0)
  have hDiv : F N ≤ ((4*C)*l^z)/l := by
    apply (le_div_iff₀ hl).mpr
    dsimp [l]
    linarith
  calc
    _ ≤ ((4*C)*l^z)/l := hDiv
    _ = (4*C)*l^(z-1) := by rw [Real.rpow_sub hl,Real.rpow_one,mul_div_assoc]
    _ ≤ l^ε*l^(z-1) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hl.le _)
    _ = l^(z-1+ε) := by rw [mul_comm,←Real.rpow_add hl]

end Squarefree856

/-
The uniform three-sunflower bound of Naslund and Sawin,
*Upper bounds for sunflower-free sets* (https://arxiv.org/abs/1606.09575).
-/

open scoped BigOperators

namespace NaslundSawin856

/-- A finite-dimensional subspace has a vector nonzero at every coordinate
where the subspace is nonzero. -/
private theorem max_support {I : Type*} [Fintype I] (E : Submodule ℝ (I → ℝ)) :
    ∃ w : E, Module.finrank ℝ E ≤
      ((Finset.univ : Finset I).filter fun i => (w : I → ℝ) i ≠ 0).card := by
  classical
  let support (w : E) : Finset I := Finset.univ.filter fun i => (w : I → ℝ) i ≠ 0
  let S := (Finset.univ : Finset I).powerset.filter (fun s => ∃ w : E, support w = s)
  have hS : S.Nonempty := ⟨support 0, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ⟨0, rfl⟩⟩⟩
  obtain ⟨s, hs, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hs).2
  have hsubset (v : E) : support v ⊆ s := by
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      ((Finset.univ : Finset I).image (fun i => -((w : I → ℝ) i) / (v : I → ℝ) i))
    let u := w + t • v
    have hu : s ∪ support v ⊆ support u := by
      intro i hi
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      change (w : I → ℝ) i + t * (v : I → ℝ) i ≠ 0
      intro hz
      by_cases hv : (v : I → ℝ) i = 0
      · have hi' : i ∈ s := by
          rcases Finset.mem_union.mp hi with hi' | hi'
          · exact hi'
          · simp [support, hv] at hi'
        have hw' : (w : I → ℝ) i ≠ 0 := by simpa [← hw, support] using hi'
        exact hw' (by simpa [hv] using hz)
      · apply ht
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ _, ((eq_div_iff hv).mpr (by linarith)).symm⟩
    have hSu : support u ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ⟨u, rfl⟩⟩
    have hcard : (s ∪ support v).card ≤ s.card :=
      (Finset.card_le_card hu).trans (hmax _ hSu)
    have heq : s = s ∪ support v :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left hcard
    exact fun i hi => heq ▸ Finset.mem_union_right s hi
  let restrict : E →ₗ[ℝ] (s → ℝ) :=
    { toFun := fun v i => (v : I → ℝ) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · exact congrFun hxy ⟨i, hi⟩
    · have hz : ((x - y : E) : I → ℝ) i = 0 := by
        by_contra hn
        exact hi (hsubset (x - y) (by simpa [support] using hn))
      exact sub_eq_zero.mp hz
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
  refine ⟨w, ?_⟩
  change Module.finrank ℝ E ≤ (support w).card
  rwa [hw]

/-- A diagonal tensor with nonzero diagonal has at least one slice per coordinate. -/
theorem diagonal_slice_bound {I R₁ R₂ R₃ : Type*} [Fintype I]
    [Fintype R₁] [Fintype R₂] [Fintype R₃] (T : I → I → I → ℝ)
    (hd : ∀ i, T i i i ≠ 0)
    (hoff : ∀ x y z, ¬ (x = y ∧ x = z) → T x y z = 0)
    (f₁ : R₁ → I → ℝ) (f₂ : R₂ → I → ℝ) (f₃ : R₃ → I → ℝ)
    (g₁ : R₁ → I → I → ℝ) (g₂ : R₂ → I → I → ℝ) (g₃ : R₃ → I → I → ℝ)
    (hs : ∀ x y z, T x y z = (∑ a, f₁ a x * g₁ a y z)
      + (∑ b, f₂ b y * g₂ b x z) + (∑ c, f₃ c z * g₃ c x y)) :
    Fintype.card I ≤ Fintype.card R₁ + Fintype.card R₂ + Fintype.card R₃ := by
  classical
  let L : (I → ℝ) →ₗ[ℝ] (R₃ → ℝ) :=
    { toFun := fun w c => ∑ z, w z * f₃ c z
      map_add' := by intro x y; funext c; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro t x; funext c; simp [mul_assoc, Finset.mul_sum] }
  obtain ⟨w, hw⟩ := max_support L.ker
  let s := (Finset.univ : Finset I).filter fun i => (w : I → ℝ) i ≠ 0
  have hR := Submodule.finrank_le L.range
  have hN := L.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hR hN
  have hkill (c : R₃) : ∑ z, (w : I → ℝ) z * f₃ c z = 0 :=
    congrFun (LinearMap.mem_ker.mp w.property) c
  let U : Matrix (↥s) (R₁ ⊕ R₂) ℝ := fun x a =>
    match a with
    | .inl a => f₁ a x
    | .inr b => ∑ z, (w : I → ℝ) z * g₂ b x z
  let V : Matrix (R₁ ⊕ R₂) (↥s) ℝ := fun a y =>
    match a with
    | .inl a => ∑ z, (w : I → ℝ) z * g₁ a y z
    | .inr b => f₂ b y
  have hcontract (x y : I) : (∑ z, (w : I → ℝ) z * T x y z) =
      (∑ a, f₁ a x * (∑ z, (w : I → ℝ) z * g₁ a y z)) +
      (∑ b, (∑ z, (w : I → ℝ) z * g₂ b x z) * f₂ b y) := by
    simp only [hs x y]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset I)) (t := (Finset.univ : Finset R₁)),
      Finset.sum_comm (s := (Finset.univ : Finset I))
      (t := (Finset.univ : Finset R₂)), Finset.sum_comm (s := (Finset.univ : Finset I))
      (t := (Finset.univ : Finset R₃))]
    have hz : (∑ c : R₃, ∑ z : I, (w : I → ℝ) z * (f₃ c z * g₃ c x y)) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      simp only [← mul_assoc, ← Finset.sum_mul, hkill, zero_mul]
    rw [hz, add_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro z _
      ring
    · apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
  let d : s → ℝ := fun x => (w : I → ℝ) x * T x x x
  have heq : U * V = Matrix.diagonal d := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    change (∑ a, f₁ a x * (∑ z, (w : I → ℝ) z * g₁ a y z)) +
      (∑ b, (∑ z, (w : I → ℝ) z * g₂ b x z) * f₂ b y) = Matrix.diagonal d x y
    rw [← hcontract, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst y
      rw [if_pos rfl, Finset.sum_eq_single x.val]
      · intro z _ hz
        rw [hoff x x z (fun h => hz h.2.symm), mul_zero]
      · simp
    · rw [if_neg hxy]
      apply Finset.sum_eq_zero
      intro z _
      rw [hoff x y z (fun h => hxy (Subtype.ext h.1)), mul_zero]
  have hdn (x : s) : d x ≠ 0 :=
    mul_ne_zero ((Finset.mem_filter.mp x.property).2) (hd x)
  have hrank : (Matrix.diagonal d).rank = s.card := by
    rw [Matrix.rank_diagonal]
    exact (Fintype.card_congr (Equiv.subtypeUnivEquiv hdn)).trans (Fintype.card_coe s)
  have hh := (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  rw [heq, hrank, Fintype.card_sum] at hh
  change Module.finrank ℝ L.ker ≤ s.card at hw
  omega


private def lowSubsets (J : Type*) [Fintype J] : Finset (Finset J) :=
  (Finset.univ : Finset J).powerset.filter fun s => s.card ≤ Fintype.card J / 3

private def familyTriple {I : Type*} (x y z : I) : Fin 3 → I := ![x, y, z]

private theorem exists_slices {I J : Type*} [Fintype J] (u : I → J → ℝ) :
    ∃ (f : lowSubsets J → I → ℝ) (g₁ g₂ g₃ : lowSubsets J → I → I → ℝ),
      ∀ x y z, (∏ a, (2 - u x a - u y a - u z a)) =
        (∑ s, f s x * g₁ s y z) + (∑ s, f s y * g₂ s x z) +
          (∑ s, f s z * g₃ s x y) := by
  classical
  let Choice := J → Option (Fin 3)
  let S (c : Choice) (i : Fin 3) : Finset J :=
    Finset.univ.filter fun a => c a = some i
  have hsmall (c : Choice) : ∃ i, (S c i).card ≤ Fintype.card J / 3 := by
    have hcount : (∑ i, (S c i).card) ≤ Fintype.card J := by
      calc
        (∑ i, (S c i).card) = ∑ i : Fin 3, ∑ a : J, if c a = some i then 1 else 0 := by
          simp [S, Finset.sum_boole]
        _ = ∑ a : J, ∑ i : Fin 3, if c a = some i then 1 else 0 :=
          Finset.sum_comm
        _ ≤ ∑ _a : J, 1 := by
          apply Finset.sum_le_sum
          intro a _
          cases hc : c a with
          | none => simp
          | some i =>
            simp only [Option.some.injEq]
            exact le_of_eq (by simp)
        _ = Fintype.card J := by simp
    by_contra! hn
    rw [Fin.sum_univ_three] at hcount
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    omega
  let leg (c : Choice) : Fin 3 := (hsmall c).choose
  let small (c : Choice) : lowSubsets J :=
    ⟨S c (leg c), Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), (hsmall c).choose_spec⟩⟩
  let key (c : Choice) : Fin 3 × lowSubsets J := (leg c, small c)
  let W (X : Fin 3 → I) (a : J) (o : Option (Fin 3)) : ℝ :=
    match o with
    | none => 2
    | some i => -u (X i) a
  let basis (s : lowSubsets J) (x : I) : ℝ := ∏ a ∈ s.val, -u x a
  let rest (c : Choice) (i : Fin 3) (Y : Fin 3 → I) : ℝ :=
    ∏ a ∈ Finset.univ.filter (fun a => c a ≠ some i), W Y a (c a)
  let grouped (i : Fin 3) (s : lowSubsets J) (Y : Fin 3 → I) : ℝ :=
    ∑ c ∈ Finset.univ.filter (fun c => key c = (i,s)), rest c i Y
  let g₁ (s : lowSubsets J) (y z : I) := grouped 0 s (familyTriple y y z)
  let g₂ (s : lowSubsets J) (x z : I) := grouped 1 s (familyTriple x x z)
  let g₃ (s : lowSubsets J) (x y : I) := grouped 2 s (familyTriple x y y)
  have hsplit (X Y : Fin 3 → I) (i : Fin 3) (s : lowSubsets J)
      (hXY : ∀ j, j ≠ i → X j = Y j) :
      (∑ c ∈ Finset.univ.filter (fun c => key c = (i,s)), ∏ a, W X a (c a)) =
        basis s (X i) * grouped i s Y := by
    simp only [grouped, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hp := (Finset.mem_filter.mp hc).2
    have hi : leg c = i := congrArg Prod.fst hp
    have hs : (small c).val = s.val := congrArg (fun p => p.2.val) hp
    have hS : S c i = s.val := by simpa [small, hi] using hs
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun a => c a = some i)]
    change (∏ a ∈ S c i, W X a (c a)) * rest c i X = basis s (X i) * rest c i Y
    congr 1
    · change (∏ a ∈ S c i, W X a (c a)) = ∏ a ∈ s.val, -u (X i) a
      rw [← hS]
      apply Finset.prod_congr rfl
      intro a ha
      have hc := (Finset.mem_filter.mp ha).2
      rw [hc]
    · apply Finset.prod_congr rfl
      intro a ha
      have hc := (Finset.mem_filter.mp ha).2
      cases hca : c a with
      | none => rfl
      | some j =>
        have hji : j ≠ i := by
          intro h
          subst j
          exact hc hca
        simp only [W, hXY j hji]
  refine ⟨basis, g₁, g₂, g₃, ?_⟩
  intro x y z
  let X := familyTriple x y z
  have hexpand : (∏ a, (2 - u x a - u y a - u z a)) =
      ∑ c : Choice, ∏ a, W X a (c a) := by
    rw [← Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro a _
    rw [Fintype.sum_option, Fin.sum_univ_three]
    change 2 - u x a - u y a - u z a = 2 + (-u x a + -u y a + -u z a)
    ring
  rw [hexpand, ← Finset.sum_fiberwise Finset.univ key, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  have hz₁ : ∀ j : Fin 3, j ≠ 0 → X j = familyTriple y y z j := by
    intro j hj
    fin_cases j <;> simp_all [X, familyTriple]
  have hz₂ : ∀ j : Fin 3, j ≠ 1 → X j = familyTriple x x z j := by
    intro j hj
    fin_cases j <;> simp_all [X, familyTriple]
  have hz₃ : ∀ j : Fin 3, j ≠ 2 → X j = familyTriple x y y j := by
    intro j hj
    fin_cases j <;> simp_all [X, familyTriple]
  simp only [hsplit X _ 0 _ hz₁, hsplit X _ 1 _ hz₂, hsplit X _ 2 _ hz₃]
  rfl


private def indicator {α : Type*} [DecidableEq α] (A : Finset α) (a : α) : ℝ :=
  if a ∈ A then 1 else 0

/-- The tensor determined by a uniform three-sunflower-free family is diagonal. -/
private theorem off_diagonal {α : Type*} [DecidableEq α] (P : Finset α) (F : Finset (Finset α))
    (k : ℕ) (hsub : ∀ A ∈ F, A ⊆ P) (hcard : ∀ A ∈ F, A.card = k)
    (hfree : ¬∃ A B C : Finset α, A ∈ F ∧ B ∈ F ∧ C ∈ F ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)
    (x y z : F) (hoff : ¬(x = y ∧ x = z)) :
    (∏ a : P, (2 - indicator x.val a.val - indicator y.val a.val - indicator z.val a.val)) =
      0 := by
  classical
  by_contra h
  have hpoint (a : α) (ha : a ∈ P) :
      2 - indicator x.val a - indicator y.val a - indicator z.val a ≠ 0 :=
    Finset.prod_ne_zero_iff.mp h ⟨a, ha⟩ (Finset.mem_univ _)
  have hab (a : α) (hx : a ∈ x.val) (hy : a ∈ y.val) : a ∈ z.val := by
    by_contra hz
    exact hpoint a (hsub x.val x.property hx) (by norm_num [indicator, hx, hy, hz])
  have hac (a : α) (hx : a ∈ x.val) (hz : a ∈ z.val) : a ∈ y.val := by
    by_contra hy
    exact hpoint a (hsub x.val x.property hx) (by norm_num [indicator, hx, hy, hz])
  have hbc (a : α) (hy : a ∈ y.val) (hz : a ∈ z.val) : a ∈ x.val := by
    by_contra hx
    exact hpoint a (hsub y.val y.property hy) (by norm_num [indicator, hx, hy, hz])
  have hxy : x.val ≠ y.val := by
    intro heq
    have hxz : x.val = z.val := Finset.eq_of_subset_of_card_le
      (fun a ha => hab a ha (heq ▸ ha))
      (le_of_eq ((hcard z.val z.property).trans (hcard x.val x.property).symm))
    exact hoff ⟨Subtype.ext heq, Subtype.ext hxz⟩
  have hxz : x.val ≠ z.val := by
    intro heq
    have hxy' : x.val = y.val := Finset.eq_of_subset_of_card_le
      (fun a ha => hac a ha (heq ▸ ha))
      (le_of_eq ((hcard y.val y.property).trans (hcard x.val x.property).symm))
    exact hxy hxy'
  have hyz : y.val ≠ z.val := by
    intro heq
    have hyx : y.val = x.val := Finset.eq_of_subset_of_card_le
      (fun a ha => hbc a ha (heq ▸ ha))
      (le_of_eq ((hcard x.val x.property).trans (hcard y.val y.property).symm))
    exact hxy hyx.symm
  apply hfree
  refine ⟨x.val, y.val, z.val, x.property, y.property, z.property, hxy, hxz, hyz, ?_, ?_⟩
  · ext a
    simp only [Finset.mem_inter]
    exact ⟨fun ha => ⟨ha.1, hab a ha.1 ha.2⟩, fun ha => ⟨ha.1, hac a ha.1 ha.2⟩⟩
  · ext a
    simp only [Finset.mem_inter]
    exact ⟨fun ha => ⟨ha.2, hab a ha.1 ha.2⟩, fun ha => ⟨hbc a ha.1 ha.2, ha.1⟩⟩

private theorem uniform_combinatorial {α : Type*} [DecidableEq α] (P : Finset α)
    (F : Finset (Finset α)) (k : ℕ) (hsub : ∀ A ∈ F, A ⊆ P) (hcard : ∀ A ∈ F, A.card = k)
    (hfree : ¬∃ A B C : Finset α, A ∈ F ∧ B ∈ F ∧ C ∈ F ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) :
    F.card ≤ 3 * (lowSubsets (↥P)).card := by
  classical
  let u (x : F) (a : P) : ℝ := indicator x.val a.val
  let T (x y z : F) : ℝ := ∏ a : P, (2 - u x a - u y a - u z a)
  obtain ⟨f, g₁, g₂, g₃, hs⟩ := exists_slices u
  have hd (x : F) : T x x x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    change 2 - indicator x.val a.val - indicator x.val a.val - indicator x.val a.val ≠ 0
    by_cases h : a.val ∈ x.val <;> norm_num [indicator, h]
  have hf := diagonal_slice_bound T hd (off_diagonal P F k hsub hcard hfree) f f f g₁ g₂ g₃ hs
  simp only [Fintype.card_coe] at hf
  omega

open Finset in
theorem small_subset_count {J : Type*} [DecidableEq J] (s : Finset J) :
    ((s.powerset.filter fun t => t.card ≤ s.card / 3).card : ℝ) ≤
      (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ s.card := by
  let N := s.card
  let K : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  have hmul (t : Finset J) (ht : t.card ≤ N / 3) : 1 ≤ K ^ N * (1/2 : ℝ) ^ t.card := by
    have hNat : t.card * 3 ≤ N := (Nat.le_div_iff_mul_le (by decide)).1 ht
    have hrNat : (t.card : ℝ)*3 ≤ N := by exact_mod_cast hNat
    have hr : (t.card : ℝ) ≤ (N : ℝ)/3 := by linarith only [hrNat]
    have he : (2 : ℝ) ^ ((N : ℝ)/3) = K ^ N := by
      rw [show (N : ℝ)/3 = (1/3 : ℝ)*(N : ℝ) by ring, Real.rpow_mul_natCast (by norm_num)]
    have hpow : (2 : ℝ) ^ t.card ≤ K ^ N := by
      rw [← Real.rpow_natCast, ← he]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hr
    have hh : 1 ≤ K ^ N / (2 : ℝ) ^ t.card :=
      (le_div_iff₀ (by positivity)).2 (by simpa only [one_mul] using hpow)
    simpa only [div_eq_mul_inv, one_mul, inv_pow] using hh
  have hroot : K * ((1/2 : ℝ) + 1) = 3 / (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _).ne').2
    have hr : K * (2 : ℝ) ^ ((2 : ℝ) / 3) = 2 := by
      change (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((2 : ℝ) / 3) = 2
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    calc
      _ = (K * (2 : ℝ) ^ ((2 : ℝ) / 3)) * ((1/2 : ℝ) + 1) := by ring
      _ = _ := by rw [hr]; norm_num
  calc
    _ = ∑ t ∈ s.powerset.filter (fun t => t.card ≤ N/3), (1 : ℝ) := by simp [N]
    _ ≤ ∑ t ∈ s.powerset.filter (fun t => t.card ≤ N/3), K ^ N * (1/2 : ℝ) ^ t.card :=
      sum_le_sum fun t ht => hmul t (mem_filter.1 ht).2
    _ ≤ ∑ t ∈ s.powerset, K ^ N * (1/2 : ℝ) ^ t.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = K ^ N * ((1/2 : ℝ) + 1) ^ N := by
      rw [← mul_sum]
      have hp := sum_pow_mul_eq_add_pow (1/2 : ℝ) 1 s
      simpa only [one_pow, mul_one, N] using congrArg (fun x : ℝ => K ^ N * x) hp
    _ = _ := by rw [← mul_pow, hroot]

/-- The Naslund–Sawin estimate for a uniform family with no three-petal sunflower. -/
theorem uniform_bound {α : Type*} [DecidableEq α] (P : Finset α)
    (F : Finset (Finset α)) (k : ℕ) (hsub : ∀ A ∈ F, A ⊆ P) (hcard : ∀ A ∈ F, A.card = k)
    (hfree : ¬∃ A B C : Finset α, A ∈ F ∧ B ∈ F ∧ C ∈ F ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) :
    (F.card : ℝ) ≤ 3 * (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ P.card := by
  classical
  have h := uniform_combinatorial P F k hsub hcard hfree
  have h₁ : (F.card : ℝ) ≤ 3 * ((lowSubsets (↥P)).card : ℝ) := by
    exact_mod_cast h
  have h₂ := small_subset_count (Finset.univ : Finset ↥P)
  have h₃ : ((lowSubsets (↥P)).card : ℝ) ≤ (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ P.card := by
    simpa only [lowSubsets, Finset.card_univ, Fintype.card_coe] using h₂
  exact h₁.trans (mul_le_mul_of_nonneg_left h₃ (by norm_num))

end NaslundSawin856

namespace TangZhangThree

open Filter Finset

noncomputable def base : ℝ := 3 / (2 : ℝ) ^ ((2 : ℝ) / 3)

private theorem base_ge_one : 1 ≤ base := by
  have hh : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  unfold base
  rw [le_div_iff₀ (by positivity), one_mul]
  linarith

theorem exact_of_uniform
    (huniform : ∀ (P : Finset ℕ) (F : Finset (Finset ℕ)) (k : ℕ),
      (∀ U ∈ F, U ⊆ P) → SunflowerFiber.ThreeFree F → (∀ U ∈ F, U.card = k) →
        (F.card : ℝ) ≤ 3 * base ^ P.card) :
    type_of% @Erdos856.erdos_856.variants.tang_zhang_three_upper := by
  intro ε hε
  let η := ε / 2
  let z := base + η
  let C := (3 : ℝ) * (1 + base / η)
  have hη : 0 < η := by dsimp [η]; positivity
  have hbase : 0 < base := zero_lt_one.trans_le base_ge_one
  have hz : 1 ≤ z := base_ge_one.trans (le_add_of_nonneg_right hη.le)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound := SunflowerFiber.nonuniform_bound_of_uniform
    (C := 3) (z := base) (η := η) (by norm_num) hbase hη huniform
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod : ∀ᶠ N : ℕ in atTop,
      Erdos856.f 3 N * Squarefree856.harmonic N ≤
        (C * (Real.exp 1 * 3 ^ z)) * (Real.log (N : ℝ)) ^ z := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop (1 : ℝ)]
      with N hN hlogN
    have hmass : 0 < Squarefree856.harmonic N :=
      (mul_pos (by norm_num) (zero_lt_one.trans_le hlogN)).trans_le (Squarefree856.log_lower N)
    apply (le_div_iff₀ hmass).mp
    unfold Erdos856.f
    apply csSup_le
    · refine ⟨0, (∅ : Finset ℕ), empty_subset _, ?_, by simp⟩
      rintro ⟨S, hsub, hS, -⟩
      have he : S = ∅ := Finset.subset_empty.mp hsub
      simp [he] at hS
    · intro y hy
      obtain ⟨A, hA, hfree, rfl⟩ := hy
      apply (le_div_iff₀ hmass).mpr
      calc
        _ ≤ C * ∑ m ∈ Icc 1 (N * N), z ^ m.primeFactors.card / (m : ℝ) :=
          SunflowerFiber.harmonic_product_le_of_sunflower_bound hA hfree hbound
        _ ≤ C * ((Real.exp 1 * 3 ^ z) * (Real.log (N : ℝ)) ^ z) :=
          mul_le_mul_of_nonneg_left (TangZhangEuler.weighted_harmonic_square_le hz hN hlogN) hC.le
        _ = _ := by dsimp [C]; ring
  have hh := Squarefree856.absorb (ε := η) (by positivity) hη hprod
  filter_upwards [hh] with N hN
  have he : z - 1 + η = base - 1 + ε := by dsimp [z, η]; ring
  rwa [he] at hN

end TangZhangThree

theorem OMA.solution : type_of% @Erdos856.erdos_856.variants.tang_zhang_three_upper :=
  TangZhangThree.exact_of_uniform fun P F k hsub hfree hcard =>
    NaslundSawin856.uniform_bound P F k hsub hcard hfree