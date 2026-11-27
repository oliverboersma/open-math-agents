import FormalConjectures.ErdosProblems.«802»
import Mathlib

/-!
Port of OpenAI's public proof of the logarithmic independence bound, from
https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026
The passage to all clique sizes and all average degrees is from @AItoBit at
https://github.com/AItoBit/formal-conjectures/tree/8cf6eb5d0204f9590118597b40185cc8d19db587/proofs/erdos802
Both sources are used under Apache-2.0. Adapted to the pinned target by @marcusbuffett.
-/

universe u v z

-- ===== source module OAI.Combinatorics.CliqueFree.Model =====

section

namespace OAI

namespace CliqueFreeLog

noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

end CliqueFreeLog

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Numerical =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence


namespace Numerical

lemma log_bounds {x : ℝ} (hx : 32 ≤ x) : 1 ≤ Real.log x ∧ 7 * Real.log x ≤ x := by
  have hx0 : 0 < x := by linarith
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ x by linarith)
  rw [h4] at hlower
  have hupper := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 32))
  rw [Real.log_div hx0.ne' (by norm_num), h32] at hupper
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  constructor <;> linarith

lemma pow_six_le_exp {x : ℝ} (hx : 32 ≤ x) : x ^ 6 ≤ Real.exp x := by
  have hx0 : 0 < x := by linarith
  have hlog := log_bounds hx
  calc
    _ = Real.exp (6 * Real.log x) := by
      have hp : Real.log (x ^ 6) = 6 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [← hp, Real.exp_log (pow_pos hx0 6)]
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

lemma exp_neg_le_inv_pow_seven {x : ℝ} (hx : 32 ≤ x) :
    Real.exp (-x) ≤ 1 / x ^ 7 := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ Real.exp (-(7 * Real.log x)) := Real.exp_le_exp.2 (by linarith [(log_bounds hx).2])
    _ = _ := by
      have hp : Real.log (x ^ 7) = 7 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [Real.exp_neg, ← hp, Real.exp_log (pow_pos hx0 7)]
      simp only [one_div]

noncomputable def threshold (x : ℝ) : ℝ := 1 / (Real.exp x * x ^ 6)

lemma threshold_pos {x : ℝ} (hx : 0 < x) : 0 < threshold x :=
  one_div_pos.2 (mul_pos (Real.exp_pos x) (pow_pos hx 6))

lemma growth_factor_le {x : ℝ} (hx : 32 ≤ x) :
    1 + Real.exp x / threshold x ≤ Real.exp (4 * x) := by
  have hx0 : 0 ≤ x := by linarith
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp_iff.2 hx0
  have he2 : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hp3 : 1 ≤ Real.exp x ^ 3 := one_le_pow₀ he1
  have hid : Real.exp x / threshold x = Real.exp x * Real.exp x * x ^ 6 := by
    unfold threshold
    simp only [div_div_eq_mul_div, div_one]
    ring
  rw [hid, show 4 * x = (4 : ℕ) * x by norm_num, Real.exp_nat_mul]
  calc
    _ ≤ 1 + Real.exp x * Real.exp x * Real.exp x :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_six_le_exp hx) (by positivity))
    _ = 1 + Real.exp x ^ 3 := by ring
    _ ≤ 2 * Real.exp x ^ 3 := by linarith
    _ ≤ Real.exp x * Real.exp x ^ 3 := mul_le_mul_of_nonneg_right he2 (by positivity)
    _ = _ := by ring

lemma leakage_factor {x : ℝ} (hx : 0 < x) :
    x ^ 2 * threshold x * Real.exp x = 1 / x ^ 4 := by
  unfold threshold
  field_simp [hx.ne', (Real.exp_pos x).ne']

lemma ceil_bounds {x : ℝ} (hx : 32 ≤ x) :
    0 < ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hl := Nat.le_ceil x
  have hu := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  refine ⟨?_, hl, by linarith⟩
  have : (0 : ℝ) < (⌈x⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

def lossRatio (x : ℝ) : ℝ := Real.log x / Real.sqrt x

def scale (X : ℝ) : ℕ → ℝ
  | 0 => X
  | n+1 => (scale X n)^2

lemma scale_ge {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : X ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 1 ≤ scale X n := hX.trans ih
    dsimp [scale]
    nlinarith

lemma scale_ge_add {X : ℝ} (hX : 2 ≤ X) (n : ℕ) : X + n ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    simp only [scale, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma lossRatio_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lossRatio x :=
  div_nonneg (Real.log_nonneg hx) (Real.sqrt_nonneg _)

lemma lossRatio_square {x : ℝ} (hx : 16 ≤ x) : lossRatio (x^2) ≤ (1/2) * lossRatio x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hs : 4 ≤ Real.sqrt x := by nlinarith
  unfold lossRatio
  rw [Real.log_pow, Real.sqrt_sq hx0.le]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ hx0).2
  rw [mul_assoc, div_mul_eq_mul_div]
  have hid : (Real.log x * x) / Real.sqrt x = Real.log x * Real.sqrt x := by
    apply (div_eq_iff (by linarith : Real.sqrt x ≠ 0)).2
    nlinarith
  have hid' : Real.log x / Real.sqrt x * x = Real.log x * Real.sqrt x := by
    calc
      _ = Real.log x * x / Real.sqrt x := by ring
      _ = _ := hid
  rw [hid']
  nlinarith [mul_le_mul_of_nonneg_left hs hl]

lemma lossRatio_scale {X : ℝ} (hX : 16 ≤ X) (n : ℕ) :
    lossRatio (scale X n) ≤ (1/2 : ℝ)^n * lossRatio X := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 16 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    calc
      _ ≤ (1/2) * lossRatio (scale X n) := lossRatio_square ht
      _ ≤ (1/2) * ((1/2 : ℝ)^n * lossRatio X) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma inv_scale {X : ℝ} (hX : 2 ≤ X) (n : ℕ) :
    1 / scale X n ≤ (1/2 : ℝ)^n * (1/X) := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    have ht0 : 0 < scale X n := by linarith
    have he : 1 / (scale X n)^2 ≤ (1/2) * (1 / scale X n) := by
      apply (div_le_iff₀ (pow_pos ht0 2)).2
      field_simp
      nlinarith
    calc
      _ ≤ (1/2) * (1 / scale X n) := he
      _ ≤ (1/2) * ((1/2 : ℝ)^n * (1/X)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma exists_iteration_threshold (a : ℝ) :
    ∃ X : ℝ, 32 ≤ X ∧ a * lossRatio X ≤ 1/4 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ ↦ a * lossRatio x) atTop (nhds 0) := by
    simpa only [lossRatio, Real.sqrt_eq_rpow, mul_zero] using h.const_mul a
  have he : ∀ᶠ x : ℝ in atTop, a * lossRatio x < 1/4 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨X,hX⟩ := eventually_atTop.1 he
  exact ⟨max 32 X, le_max_left _ _, (hX (max 32 X) (le_max_right _ _)).le⟩

lemma recurrence_bound {B q ε t m s : ℝ}
    (hB : 1 ≤ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ q/4) (_ht : 0 ≤ t) (hm : 0 ≤ m)
    (hs : s ≤ q/2)
    (hstep : (1-ε)*t - s*m ≤ B*(2-2*q)*m) :
    t ≤ B*(2-q)*m := by
  have hB0 : 0 ≤ B := by linarith
  have hb : 0 ≤ B*(2-q) := mul_nonneg hB0 (by linarith)
  have hb2 : B*(2-q) ≤ 2*B := by nlinarith
  have hnum : B*(2-2*q)+s ≤ (1-ε)*(B*(2-q)) := by
    have he : ε * (B*(2-q)) ≤ (q/4)*(2*B) :=
      mul_le_mul hε hb2 hb (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hq0]
  have hpos : 0 < 1-ε := by linarith
  apply (mul_le_mul_iff_right₀ hpos).1
  have hh := mul_le_mul_of_nonneg_right hnum hm
  nlinarith only [hh,hstep]

end CliqueFreeIndependence.Numerical

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.WeightedGraph =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

def mass (w : V → ℝ) (A : Finset V) : ℝ := ∑ v ∈ A, w v

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (G.Adj v)

@[simp] lemma mem_neighbors (G : SimpleGraph V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

noncomputable def crossMass (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) : ℝ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ B, if G.Adj u v then w u * w v else 0

/-- Unordered edge mass, written as half the directed edge mass. -/
noncomputable def edgeMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  crossMass G w univ univ / 2

noncomputable def neighborMass (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  mass w (neighbors G u)

noncomputable def commonMass (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ := by
  classical
  exact mass w (neighbors G u ∩ neighbors G v)

/-- Twice the triangle mass in the weighted neighborhood of u. -/
noncomputable def triangleAt (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ neighbors G u, w v * commonMass G w u v

/-- Unordered triangle mass, written as one sixth of the ordered triangle mass. -/
noncomputable def triangleMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  (∑ u, w u * triangleAt G w u) / 6

/-- The growth function `g_x`, including its zero convention. Only nonnegative `s` are used. -/
noncomputable def growth (x s : ℝ) : ℝ := s * (x + max 0 (Real.log (1 / s)))

/-- The full cross-mass property; sets may overlap. -/
def CrossBound (G : SimpleGraph V) (w : V → ℝ) (C : ℝ) : Prop :=
  ∀ (x : ℝ), 1 ≤ x → ∀ (A B : Finset V),
    mass w A ≤ Real.exp x → mass w B ≤ Real.exp x →
      crossMass G w A B ≤ C * growth x (mass w A)

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

omit [Fintype V] in
lemma crossMass_symm (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = crossMass G w B A := by
  classical
  unfold crossMass
  rw [sum_comm]
  simp_rw [G.adj_comm, mul_comm]

omit [Fintype V] in
lemma crossMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : 0 ≤ crossMass G w A B := by
  classical
  exact sum_nonneg fun u _ ↦ sum_nonneg fun v _ ↦ by
    split_ifs
    · exact mul_nonneg (hw u) (hw v)
    · exact le_rfl

omit [Fintype V] in
lemma crossMass_le_product (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : crossMass G w A B ≤ mass w A * mass w B := by
  classical
  unfold crossMass mass
  rw [sum_mul_sum]
  exact sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw u) (hw v)

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma commonMass_comm (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = commonMass G w v u := by
  classical
  simp [commonMass, inter_comm]

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma neighborMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ neighborMass G w u := mass_nonneg hw _

lemma commonMass_le_neighborMass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (u v : V) : commonMass G w u v ≤ neighborMass G w u := by
  classical
  exact mass_mono hw inter_subset_left

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma triangleMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ triangleMass G w := div_nonneg
      (sum_nonneg fun u _ ↦ mul_nonneg (hw u) (triangleAt_nonneg G hw u)) (by norm_num)

lemma edgeMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    2 * edgeMass G w = ∑ u, w u * neighborMass G w u := by
  classical
  rw [edgeMass, crossMass_factor]
  simp only [univ_inter, neighborMass]
  ring

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma triangleAt_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (u : V) :
    triangleAt G w u ≤ L * neighborMass G w u := by
  calc
    _ ≤ ∑ v ∈ neighbors G u, w v * L := sum_le_sum fun v _ ↦
      mul_le_mul_of_nonneg_left ((commonMass_le_neighborMass G hw u v).trans (hL u)) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _

lemma triangleMass_le_of_neighborMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) :
    triangleMass G w ≤ L / 3 * edgeMass G w := by
  have h : 6 * triangleMass G w ≤ L * (2 * edgeMass G w) := by
    rw [triangleMass_eq_sum, edgeMass_eq_sum, mul_sum]
    exact sum_le_sum fun u _ ↦ by
      have := mul_le_mul_of_nonneg_left (triangleAt_le G hw hL u) (hw u)
      nlinarith
  linarith

lemma neighborMass_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    {u : V} (hu : (neighbors G u).Nonempty) : τ ≤ neighborMass G w u := by
  rcases hu with ⟨v, hv⟩
  exact (hc u v (mem_neighbors G u v |>.1 hv)).trans (commonMass_le_neighborMass G hw u v)

lemma triangleAt_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    (u : V) : τ * neighborMass G w u ≤ triangleAt G w u := by
  calc
    _ = ∑ v ∈ neighbors G u, w v * τ := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ _ := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left
      (hc u v (mem_neighbors G u v |>.1 hv)) (hw v)

lemma commonMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = ∑ z ∈ neighbors G u, if G.Adj v z then w z else 0 := by
  classical
  unfold commonMass mass
  rw [← filter_mem_eq_inter, sum_filter]
  simp only [mem_neighbors]

lemma crossMass_all_right (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A univ = ∑ u ∈ A, w u * neighborMass G w u := by
  classical
  rw [crossMass_factor]
  simp [neighborMass]

lemma crossMass_all_left (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w univ A = ∑ u ∈ A, w u * neighborMass G w u := by
  rw [crossMass_symm, crossMass_all_right]

lemma crossMass_neighbors (G : SimpleGraph V) (w : V → ℝ)
    (A : Finset V) (v : V) :
    crossMass G w A (neighbors G v) = ∑ u ∈ A, w u * commonMass G w u v := by
  rw [crossMass_factor]
  simp only [commonMass, inter_comm]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Optimizer =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
variable {V : Type u} [Fintype V]

/-- The directed bilinear edge form (twice the quadratic mass on the diagonal). -/
noncomputable def edgeForm (G : SimpleGraph V) (a b : V → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then a u * b v else 0

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

lemma edgeForm_symm (G : SimpleGraph V) (a b : V → ℝ) : edgeForm G a b = edgeForm G b a := by
  unfold edgeForm
  rw [sum_comm]
  simp_rw [G.adj_comm,mul_comm]

lemma edgeForm_add_left (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G (a+b) c = edgeForm G a c + edgeForm G b c := by
  unfold edgeForm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp [Pi.add_apply,add_mul]

lemma edgeForm_add_right (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G a (b+c) = edgeForm G a b + edgeForm G a c := by
  rw [edgeForm_symm,edgeForm_add_left,edgeForm_symm _ b,edgeForm_symm _ c]

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

lemma edgeMass_add (G : SimpleGraph V) (a b : V → ℝ) :
    edgeMass G (a+b) = edgeMass G a + edgeMass G b + edgeForm G a b := by
  have h := edgeForm_self G (a+b)
  rw [edgeForm_add_left,edgeForm_add_right,edgeForm_add_right,edgeForm_self,edgeForm_self,
    edgeForm_symm G b a] at h
  linarith

lemma edgeForm_mono (G : SimpleGraph V) {a b c d : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) (hac : ∀ v, a v ≤ c v) (hbd : ∀ v, b v ≤ d v) :
    edgeForm G a b ≤ edgeForm G c d := by
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro v _
  split_ifs
  · exact mul_le_mul (hac u) (hbd v) (hb v) ((ha u).trans (hac u))
  · rfl

lemma edgeMass_mono_weight (G : SimpleGraph V) {w q : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hwq : ∀ v, w v ≤ q v) : edgeMass G w ≤ edgeMass G q := by
  have h := edgeForm_mono G hw hw hwq hwq
  rw [edgeForm_self,edgeForm_self] at h
  linarith

noncomputable def spike [DecidableEq V] (v : V) (t : ℝ) : V → ℝ := fun u ↦ if u = v then t else 0

lemma edgeForm_spike [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeForm G (spike v t) w = t * neighborMass G w v := by
  rw [edgeForm_neighbor]
  simp [spike,ite_mul]

lemma edgeMass_spike [DecidableEq V] (G : SimpleGraph V) (v : V) (t : ℝ) :
    edgeMass G (spike v t) = 0 := by
  have h := edgeForm_self G (spike v t)
  rw [edgeForm_spike] at h
  have hn : neighborMass G (spike v t) v = 0 := by
    simp [neighborMass,mass,neighbors,spike]
  rw [hn] at h
  linarith

omit [Fintype V] in
lemma update_eq_add_spike [DecidableEq V] (w : V → ℝ) (v : V) (t : ℝ) :
    Function.update w v t = w + spike v (t-w v) := by
  funext u
  by_cases h : u = v <;> simp [Function.update,spike,h]

lemma edgeMass_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeMass G (Function.update w v t) = edgeMass G w + (t-w v)*neighborMass G w v := by
  rw [update_eq_add_spike,edgeMass_add,edgeMass_spike,edgeForm_symm,edgeForm_spike]
  ring

/-- The vertex summand, with Mathlib's log(0)=0 convention. -/
def vertexPotential (t : ℝ) : ℝ := t * (1-Real.log t)

noncomputable def potential (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  ∑ v, vertexPotential (w v) - edgeMass G w

def IsOptimizer (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ q : V → ℝ, (∀ v, 0 ≤ q v) → potential G q ≤ potential G w

lemma continuous_vertexPotential : Continuous vertexPotential := by
  have h := continuous_id.sub Real.continuous_mul_log
  convert h using 1
  ext x
  simp [vertexPotential]
  ring

lemma continuous_edgeMass (G : SimpleGraph V) : Continuous (edgeMass G) := by
  classical
  unfold edgeMass crossMass
  apply Continuous.div_const
  apply continuous_finsetSum
  intro u _
  apply continuous_finsetSum
  intro v _
  split_ifs <;> fun_prop

lemma continuous_potential (G : SimpleGraph V) : Continuous (potential G) := by
  unfold potential
  apply Continuous.sub _ (continuous_edgeMass G)
  exact continuous_finsetSum _ fun v _ ↦ continuous_vertexPotential.comp (continuous_apply v)

lemma vertexPotential_le_one {t : ℝ} (ht : 0 ≤ t) : vertexPotential t ≤ 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [vertexPotential]
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ht.le
  rw [mul_sub,mul_inv_cancel₀ ht.ne'] at h
  unfold vertexPotential
  nlinarith

lemma potential_clamp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    potential G w ≤ potential G (fun v ↦ min (w v) 1) := by
  have hv (v : V) : vertexPotential (w v) ≤ vertexPotential (min (w v) 1) := by
    by_cases h : w v ≤ 1
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      simpa [vertexPotential] using vertexPotential_le_one (hw v)
  have hs := sum_le_sum (s := univ) (fun v _ ↦ hv v)
  have he := edgeMass_mono_weight G (fun v ↦ le_min (hw v) zero_le_one) (fun v ↦ min_le_left (w v) 1)
  unfold potential
  linarith

lemma exists_optimizer (G : SimpleGraph V) : ∃ w : V → ℝ, IsOptimizer G w := by
  let S : Set (V → ℝ) := Set.Icc 0 1
  have hS : IsCompact S := isCompact_Icc
  have hne : S.Nonempty := ⟨0,by simp [S]⟩
  obtain ⟨w,hw,hmax⟩ := hS.exists_isMaxOn hne (continuous_potential G).continuousOn
  refine ⟨w,hw.1,?_⟩
  intro q hq
  apply (potential_clamp G hq).trans
  apply hmax
  exact ⟨fun v ↦ le_min (hq v) zero_le_one,fun v ↦ min_le_right (q v) 1⟩

lemma potential_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    potential G (Function.update w v t) - potential G w =
      vertexPotential t - vertexPotential (w v) - (t-w v)*neighborMass G w v := by
  have hs : (∑ u, vertexPotential (Function.update w v t u)) =
      ∑ u, vertexPotential (w u) + (vertexPotential t - vertexPotential (w v)) := by
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v)]
    simp only [Function.update_self]
    have h : (∑ u ∈ univ.erase v, vertexPotential (Function.update w v t u)) =
        ∑ u ∈ univ.erase v, vertexPotential (w u) := by
      apply sum_congr rfl
      intro u hu
      rw [Function.update_of_ne (by simpa using (mem_erase.1 hu).1)]
    rw [h]
    ring
  unfold potential
  rw [hs,edgeMass_update]
  ring

lemma optimizer_stationary {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w) (v : V) :
    0 < w v ∧ Real.log (1/w v) = neighborMass G w v ∧ w v ≤ 1 := by
  classical
  let N := neighborMass G w v
  let a := Real.exp (-N)
  have ha : 0 < a := Real.exp_pos _
  have hN : 0 ≤ N := neighborMass_nonneg G hw.1 v
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hloga : Real.log a = -N := Real.log_exp _
  have hmax := hw.2 (Function.update w v a) (fun u ↦ by
    by_cases h : u = v
    · subst u; simpa using ha.le
    · simpa [h] using hw.1 u)
  have heq := potential_update G w v a
  have hbound : a ≤ w v * (1-Real.log (w v)-N) := by
    rw [vertexPotential,vertexPotential,hloga] at heq
    dsimp [N] at *
    nlinarith only [hmax,heq]
  have hwv : 0 < w v := by
    have h0 := hw.1 v
    by_contra hn
    have hz : w v = 0 := le_antisymm (le_of_not_gt hn) h0
    simp only [hz,zero_mul] at hbound
    linarith
  have hwa : w v = a := by
    by_contra hn
    have hdiv : a / w v ≠ 1 := by
      intro he
      exact hn ((div_eq_one_iff_eq hwv.ne').1 he).symm
    have hl := Real.log_lt_sub_one_of_pos (div_pos ha hwv) hdiv
    rw [Real.log_div ha.ne' hwv.ne',hloga] at hl
    have hh := mul_lt_mul_of_pos_left hl hwv
    have hid : w v * (a / w v - 1) = a-w v := by field_simp
    rw [hid] at hh
    nlinarith
  refine ⟨hwv,?_,hwa ▸ ha1⟩
  rw [one_div,Real.log_inv,hwa,hloga]
  simp [N]

/-- Expansion around a stationary positive maximizer. -/
lemma optimizer_divergence {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    0 ≤ potential G w - potential G q ∧
      potential G w - potential G q =
        (∑ v, (q v * Real.log (q v / w v) - q v + w v)) + edgeMass G (q-w) := by
  refine ⟨sub_nonneg.2 (hw.2 q hq),?_⟩
  have hsum (v : V) : vertexPotential (w v) - vertexPotential (q v) +
      (q v-w v)*neighborMass G w v = q v*Real.log (q v/w v) - q v + w v := by
    obtain ⟨hwv,hstat,_⟩ := optimizer_stationary hw v
    rw [one_div,Real.log_inv] at hstat
    rcases (hq v).eq_or_lt with hz | hqv
    · simp [← hz,vertexPotential,hstat.symm]
      ring
    · rw [Real.log_div hqv.ne' hwv.ne']
      unfold vertexPotential
      rw [← hstat]
      ring
  have he := edgeMass_add G (q-w) w
  have hqw : q-w+w = q := sub_add_cancel _ _
  rw [hqw,edgeForm_neighbor] at he
  simp only [Pi.sub_apply] at he
  have hs := congrArg (fun f : V → ℝ ↦ ∑ v, f v) (funext hsum)
  simp only [sum_add_distrib,sum_sub_distrib] at hs
  unfold potential
  simp only [sum_add_distrib,sum_sub_distrib]
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.OptimizerBounds =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

lemma sum_log_le_log_sum {p x : V → ℝ} (hp : ∀ v, 0 ≤ p v)
    (hs : ∑ v, p v = 1) (hx : ∀ v, 0 < x v) :
    (∑ v, p v * Real.log (x v)) ≤ Real.log (∑ v, p v * x v) := by
  simpa only [smul_eq_mul] using strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := univ) (w := p) (p := x) (fun v _ ↦ hp v) hs (fun v _ ↦ hx v)

lemma card_neighbors (G : SimpleGraph V) (v : V) : (neighbors G v).card = G.degree v := by
  classical
  have he : neighbors G v = G.neighborFinset v := by ext u; simp
  rw [he, G.card_neighborFinset_eq_degree]

lemma sum_neighborMass (G : SimpleGraph V) (w : V → ℝ) :
    (∑ v, neighborMass G w v) = ∑ v, (G.degree v : ℝ) * w v := by
  classical
  simp only [neighborMass, mass, neighbors, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  simp_rw [G.adj_comm]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  rw [← card_neighbors G v]
  rfl

lemma optimizer_total_weight {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ : ℝ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ) / Δ ≤ ∑ v, w v := by
  have hn : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hW : 0 < ∑ v, w v := sum_pos (fun v _ ↦ hwpos v) univ_nonempty
  have hp : (∑ _v : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
    simp [hn.ne']
  have hj := sum_log_le_log_sum (fun _v ↦ (inv_pos.2 hn).le) hp hwpos
  simp only [← mul_sum] at hj
  have he : (∑ v, Real.log (w v)) = -∑ v, neighborMass G w v := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    have hv := (optimizer_stationary hw v).2.1
    rw [one_div, Real.log_inv] at hv
    linarith
  rw [he, sum_neighborMass] at hj
  have hd := sum_le_sum (s := univ) fun v _ ↦ mul_le_mul_of_nonneg_right (hdeg v) (hw.1 v)
  rw [← mul_sum] at hd
  have hJ : Real.log ((Fintype.card V : ℝ) / (∑ v, w v)) ≤
      Δ * (∑ v, w v) / (Fintype.card V : ℝ) := by
    rw [Real.log_div hn.ne' hW.ne']
    rw [Real.log_mul (inv_ne_zero hn.ne') hW.ne', Real.log_inv] at hj
    have hm := mul_le_mul_of_nonneg_left hd (inv_pos.2 hn).le
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hΔpos : 0 < Δ := by linarith
  have hl : 1 < Real.log Δ := (Real.lt_log_iff_exp_lt hΔpos).2
    (Real.exp_one_lt_three.trans_le hΔ)
  by_contra h
  have hlt : (∑ v, w v) < (Fintype.card V : ℝ) / Δ := lt_of_not_ge h
  have hmul : Δ * (∑ v, w v) < Fintype.card V := by
    nlinarith [(lt_div_iff₀ hΔpos).1 hlt]
  have hlog := Real.log_lt_log hΔpos ((lt_div_iff₀ hW).2 hmul)
  have hfrac : Δ * (∑ v, w v) / (Fintype.card V : ℝ) < 1 :=
    (div_lt_one hn).2 hmul
  linarith

lemma optimizer_edge_bound {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ : ℝ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    2 * edgeMass G w ≤ Real.log Δ * (∑ v, w v) := by
  have hn : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hW : 0 < ∑ v, w v := sum_pos (fun v _ ↦ hwpos v) univ_nonempty
  have hp : (∑ v, w v / (∑ u, w u)) = 1 := by rw [← sum_div, div_self hW.ne']
  have hj := sum_log_le_log_sum (fun v ↦ (div_pos (hwpos v) hW).le) hp
    (fun v ↦ one_div_pos.2 (hwpos v))
  have hright : (∑ v, w v / (∑ u, w u) * (1 / w v)) =
      (Fintype.card V : ℝ) / (∑ v, w v) := by
    calc
      _ = ∑ _v : V, 1 / (∑ u, w u) := by
        apply sum_congr rfl
        intro v _
        field_simp [(hwpos v).ne']
      _ = _ := by simp [div_eq_mul_inv]
  have hleft : (∑ v, w v / (∑ u, w u) * Real.log (1 / w v)) =
      2 * edgeMass G w / (∑ v, w v) := by
    rw [← edgeForm_self, edgeForm_neighbor, sum_div]
    apply sum_congr rfl
    intro v _
    rw [(optimizer_stationary hw v).2.1]
    ring
  rw [hleft, hright] at hj
  have htotal := optimizer_total_weight hw hΔ hdeg
  have hΔpos : 0 < Δ := by linarith
  have hm : (Fintype.card V : ℝ) / (∑ v, w v) ≤ Δ := by
    apply (div_le_iff₀ hW).2
    nlinarith [(div_le_iff₀ hΔpos).1 htotal]
  have hh := hj.trans (Real.log_le_log (div_pos hn hW) hm)
  exact (div_le_iff₀ hW).1 hh

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Lottery =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence
namespace Lottery
variable {α β : Type u}

/-- A finite real lottery; list entries need not have distinct outcomes. -/
abbrev Law (α : Type u) := List (ℝ × α)

def expect (L : Law α) (f : α → ℝ) : ℝ := (L.map fun z ↦ z.1 * f z.2).sum

def Positive (L : Law α) : Prop := ∀ z ∈ L, 0 ≤ z.1

def total (L : Law α) : ℝ := expect L (fun _ ↦ 1)

def IsProb (L : Law α) : Prop := Positive L ∧ total L = 1

@[simp] lemma expect_nil (f : α → ℝ) : expect [] f = 0 := rfl
@[simp] lemma expect_cons (p : ℝ) (a : α) (L : Law α) (f : α → ℝ) :
    expect ((p,a)::L) f = p*f a + expect L f := rfl
@[simp] lemma expect_singleton (p : ℝ) (a : α) (f : α → ℝ) : expect [(p,a)] f = p*f a := by
  simp [expect]

lemma expect_append (L K : Law α) (f : α → ℝ) : expect (L++K) f = expect L f + expect K f := by
  simp [expect]

lemma expect_add (L : Law α) (f g : α → ℝ) :
    expect L (fun a ↦ f a + g a) = expect L f + expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_mul (L : Law α) (a : ℝ) (f : α → ℝ) :
    expect L (fun z ↦ a*f z) = a * expect L f := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_const (L : Law α) (a : ℝ) : expect L (fun _ ↦ a) = a * total L := by
  simpa only [mul_one,total] using expect_mul L a (fun _ ↦ 1)

lemma expect_mono {L : Law α} (hL : Positive L) {f g : α → ℝ}
    (h : ∀ z ∈ L, f z.2 ≤ g z.2) : expect L f ≤ expect L g := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (h z (by simp)) (hL z (by simp)))
      (ih (fun t ht ↦ hL t (by simp [ht])) (fun t ht ↦ h t (by simp [ht])))

lemma expect_sum {I : Type*} (L : Law α) (s : Finset I) (f : I → α → ℝ) :
    expect L (fun a ↦ ∑ i ∈ s, f i a) = ∑ i ∈ s, expect L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect_const]
  | @insert i s hi ih => simp only [sum_insert hi,expect_add,ih]

def transform (p : ℝ) (f : α → β) (L : Law α) : Law β := L.map (fun z ↦ (p*z.1,f z.2))

lemma expect_transform (p : ℝ) (f : α → β) (L : Law α) (g : β → ℝ) :
    expect (transform p f L) g = p * expect L (g ∘ f) := by
  induction L with
  | nil => simp [transform]
  | cons z L ih =>
    rcases z with ⟨q,a⟩
    simp only [transform,List.map_cons,expect_cons,Function.comp_apply] at *
    rw [ih]
    ring

lemma total_transform (p : ℝ) (f : α → β) (L : Law α) :
    total (transform p f L) = p * total L := expect_transform _ _ _ _

lemma positive_transform {p : ℝ} (hp : 0 ≤ p) (f : α → β) {L : Law α} (hL : Positive L) :
    Positive (transform p f L) := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  exact mul_nonneg hp (hL y hy)

lemma positive_append {L K : Law α} (hL : Positive L) (hK : Positive K) : Positive (L++K) := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact hL z hz
  · exact hK z hz

end Lottery

end CliqueFreeIndependence

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.MultiplierLaw =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence
namespace WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

/-- A weight vector restricted to a vertex set. -/
noncomputable def restrict (A : Finset V) (w : V → ℝ) : V → ℝ := fun v ↦ if v ∈ A then w v else 0

lemma edgeMass_smul (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) :
    edgeMass G (fun v ↦ a*w v) = a^2 * edgeMass G w := by
  have h : edgeForm G (fun v ↦ a*w v) (fun v ↦ a*w v) = a^2*edgeForm G w w := by
    unfold edgeForm
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    split_ifs <;> ring
  rw [edgeForm_self,edgeForm_self] at h
  linarith

lemma edgeMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    edgeMass G (restrict A w) = crossMass G w A A / 2 := by
  classical
  unfold edgeMass crossMass restrict
  congr 1
  calc
    _ = ∑ u, ∑ v, if u ∈ A ∧ v ∈ A then (if G.Adj u v then w u*w v else 0) else 0 := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu,hv]
    _ = _ := by
      simp only [ite_and]
      simp_rw [sum_ite_irrel]
      simp only [sum_const_zero]
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
      apply sum_congr rfl
      intro u hu
      rw [← sum_filter]
      simp

lemma crossMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A A = ∑ v ∈ A, w v * mass w (A ∩ neighbors G v) := crossMass_factor G w A A

lemma edgeMass_restrict_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A : Finset V) {t : ℝ} (hA : ∀ v ∈ A, mass w (A ∩ neighbors G v) ≤ t) :
    edgeMass G (restrict A w) ≤ t * mass w A / 2 := by
  rw [edgeMass_restrict,crossMass_restrict]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ v ∈ A, w v*t := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (hA v hv) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _

/-- Bounded multipliers supported on A, regardless of the lottery weight of the entry. -/
def BoundedOn (L : Law (V → ℝ)) (A : Finset V) (b : ℝ) : Prop :=
  ∀ z ∈ L, (∀ v, 0 ≤ z.2 v ∧ z.2 v ≤ b) ∧ (∀ v, v ∉ A → z.2 v = 0)

noncomputable def expectedEdges (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) : ℝ :=
  expect L (fun m ↦ edgeMass G (fun v ↦ w v*m v))

lemma expectedEdges_transform (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) (p k : ℝ) :
    expectedEdges G w (transform p (fun m v ↦ k*m v) L) = p*k^2*expectedEdges G w L := by
  unfold expectedEdges
  rw [expect_transform]
  have he (m : V → ℝ) : edgeMass G (fun v ↦ w v*(k*m v)) = k^2*edgeMass G (fun v ↦ w v*m v) := by
    convert edgeMass_smul G (fun v ↦ w v*m v) k using 2
    ext v
    ring
  change p * expect L (fun m ↦ edgeMass G (fun v ↦ w v*(k*m v))) = _
  simp_rw [he]
  rw [expect_mul]
  ring

omit [Fintype V] in
lemma mean_transform (L : Law (V → ℝ)) (p k : ℝ) (v : V) :
    expect (transform p (fun m v ↦ k*m v) L) (fun m ↦ m v) = p*k*expect L (fun m ↦ m v) := by
  rw [expect_transform]
  change p * expect L (fun m ↦ k*m v) = _
  rw [expect_mul]
  ring

omit [Fintype V] in
lemma bounded_transform {L : Law (V → ℝ)} {A : Finset V} {b B k : ℝ}
    (hL : BoundedOn L A b) (hk : 0 ≤ k) (hkb : k*b ≤ B) (p : ℝ) :
    BoundedOn (transform p (fun m v ↦ k*m v) L) A B := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  obtain ⟨hby,hsy⟩ := hL y hy
  exact ⟨fun v ↦ ⟨mul_nonneg hk (hby v).1,(mul_le_mul_of_nonneg_left (hby v).2 hk).trans hkb⟩,
    fun v hv ↦ by simp [hsy v hv]⟩

omit [Fintype V] in
lemma bounded_append {L K : Law (V → ℝ)} {A B S : Finset V} {b : ℝ}
    (hL : BoundedOn L A b) (hK : BoundedOn K B b) (hA : A ⊆ S) (hB : B ⊆ S) :
    BoundedOn (L++K) S b := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact ⟨(hL z hz).1,fun v hv ↦ (hL z hz).2 v (fun h ↦ hv (hA h))⟩
  · exact ⟨(hK z hz).1,fun v hv ↦ (hK z hz).2 v (fun h ↦ hv (hB h))⟩

lemma normalize_subprob (G : SimpleGraph V) (w : V → ℝ) {L : Law (V → ℝ)}
    (hL : Positive L) (hsum : total L ≤ 1) {A : Finset V} {b : ℝ} (hb : 0 ≤ b)
    (hbL : BoundedOn L A b) :
    ∃ K : Law (V → ℝ), IsProb K ∧ BoundedOn K A b ∧
      (∀ v, expect K (fun m ↦ m v) = expect L (fun m ↦ m v)) ∧
      expectedEdges G w K = expectedEdges G w L := by
  let K : Law (V → ℝ) := (1-total L,0)::L
  refine ⟨K,⟨?_,?_⟩,?_,?_,?_⟩
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact sub_nonneg.2 hsum
    · exact hL z hz
  · simp [K,total,expect_cons]
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨fun _ ↦ ⟨le_rfl,hb⟩,fun _ _ ↦ rfl⟩
    · exact hbL z hz
  · intro v
    simp [K]
  · simp [K,expectedEdges,edgeMass,crossMass]

end WeightedGraph
end CliqueFreeIndependence

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Deletion =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

noncomputable def closedNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact insert v (neighbors G v)

@[simp] lemma mem_closedNeighbors (G : SimpleGraph V) (u v : V) :
    u ∈ closedNeighbors G v ↔ u = v ∨ G.Adj v u := by
  classical
  simp [closedNeighbors]

lemma mass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    mass w (closedNeighbors G v) = w v + neighborMass G w v := by
  classical
  exact sum_insert (by simp) -- the two expressions are definitionally the sums

lemma edgeMass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    edgeMass G (restrict (closedNeighbors G v) w) =
      w v * neighborMass G w v + triangleAt G w v / 2 := by
  classical
  have hv : v ∉ neighbors G v := by simp
  have hs : (∑ u ∈ neighbors G v, if G.Adj v u then w v * w u else 0) =
      w v * neighborMass G w v := by
    rw [neighborMass, mass, mul_sum]
    apply sum_congr rfl
    intro u hu
    simp [(mem_neighbors G v u).1 hu]
  have hs' : (∑ u ∈ neighbors G v, if G.Adj u v then w u * w v else 0) =
      w v * neighborMass G w v := by
    simp_rw [G.adj_comm, mul_comm]
    exact hs
  have ht : crossMass G w (neighbors G v) (neighbors G v) = triangleAt G w v := by
    simpa [triangleAt, commonMass, inter_comm] using crossMass_neighbors G w (neighbors G v) v
  rw [edgeMass_restrict]
  have he : crossMass G w (closedNeighbors G v) (closedNeighbors G v) =
      2 * (w v * neighborMass G w v) + triangleAt G w v := by
    simp only [closedNeighbors, crossMass, sum_insert hv, G.irrefl, ite_false, zero_add,
      sum_add_distrib]
    rw [hs,hs']
    change _ + (_ + crossMass G w (neighbors G v) (neighbors G v)) = _
    rw [ht]
    ring
  rw [he]
  ring

lemma optimizer_deletion_cost {G : SimpleGraph V} {w : V → ℝ}
    (hw : IsOptimizer G w) (A : Finset V) :
    potential G w - potential G (restrict Aᶜ w) =
      mass w A + edgeMass G (restrict A w) := by
  classical
  have hq : ∀ v, 0 ≤ restrict Aᶜ w v := by
    intro v
    simp only [restrict]
    split_ifs
    · exact hw.1 v
    · rfl
  rw [(optimizer_divergence hw _ hq).2]
  have hsum : (∑ v, (restrict Aᶜ w v * Real.log (restrict Aᶜ w v / w v) -
      restrict Aᶜ w v + w v)) = mass w A := by
    calc
      _ = ∑ v, if v ∈ A then w v else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases hv : v ∈ A
        · simp [restrict,hv]
        · simp [restrict,hv, (optimizer_stationary hw v).1.ne']
      _ = mass w A := by simp [mass]
  have hdiff : restrict Aᶜ w - w = (-1 : ℝ) • restrict A w := by
    ext v
    by_cases hv : v ∈ A <;> simp [restrict,hv]
  rw [hsum, hdiff]
  have he := edgeMass_smul G (restrict A w) (-1)
  simpa only [Pi.smul_def,smul_eq_mul,neg_one_sq,one_mul] using congrArg (mass w A + ·) he

lemma potential_induce (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    potential (G.induce (A : Set V)) (fun v ↦ w v) = potential G (restrict A w) := by
  classical
  have he : edgeMass (G.induce (A : Set V)) (fun v ↦ w v) = edgeMass G (restrict A w) := by
    rw [edgeMass_restrict,edgeMass,crossMass]
    congr 1
    simp only [SimpleGraph.induce_adj]
    rw [← Finset.sum_subtype A (by simp)
      (fun u ↦ ∑ v : (A : Set V), if G.Adj u v then w u * w v else 0)]
    unfold crossMass
    apply sum_congr rfl
    intro u hu
    exact (Finset.sum_subtype A (by simp)
      (fun v ↦ if G.Adj u v then w u * w v else 0)).symm
  rw [potential, potential, he]
  congr 1
  rw [← Finset.sum_subtype A (by simp) (fun v ↦ vertexPotential (w v))]
  have hvertex (v : V) : vertexPotential (restrict A w v) =
      if v ∈ A then vertexPotential (w v) else 0 := by
    by_cases hv : v ∈ A <;> simp [restrict,hv,vertexPotential]
  simp_rw [hvertex]
  simp

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.FiniteEntropy =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence


namespace FiniteEntropy

variable {I : Type u} [Fintype I]

/-- A finite real-valued probability vector. -/
def IsProb (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Weighted row entropy, with the `0 log 0 = 0` convention. -/
def entropy (w p : I → ℝ) : ℝ := ∑ i, p i * Real.log (w i / p i)

/-- Relative entropy, used only when `q` is positive on the positive support of `p`. -/
def divergence (p q : I → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Total variation distance of two finite probability vectors. -/
def tv (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

lemma relTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) : 0 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, hq]
  have hq' := hs hp
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp)
  have hl : Real.log (q / p) = -Real.log (p / q) := by
    rw [Real.log_div hq'.ne' hp.ne', Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have hc : p * (q / p - 1) = q - p := by field_simp
  rw [hc] at hm
  linarith

lemma sqrt_sub_sq_le_relTerm {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, Real.sq_sqrt hq]
  have hq' := hs hp
  have hsp := Real.sqrt_pos.2 hp
  have hsq := Real.sqrt_pos.2 hq'
  have h := Real.log_le_sub_one_of_pos (div_pos hsq hsp)
  have hl : Real.log (Real.sqrt q / Real.sqrt p) = -(Real.log (p / q)) / 2 := by
    rw [Real.log_div hsq.ne' hsp.ne', Real.log_sqrt hq, Real.log_sqrt hp.le,
      Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * p by positivity)
  have hc : p * (Real.sqrt q / Real.sqrt p) = Real.sqrt p * Real.sqrt q := by
    calc
      _ = (Real.sqrt p) ^ 2 * (Real.sqrt q / Real.sqrt p) := by rw [Real.sq_sqrt hp.le]
      _ = Real.sqrt p * Real.sqrt q := by field_simp
  have hp2 := Real.sq_sqrt hp.le
  have hq2 := Real.sq_sqrt hq
  nlinarith

lemma divergence_nonneg {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) : 0 ≤ divergence p q := by
  have h := sum_nonneg (s := univ) fun i _ ↦ relTerm_nonneg (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

lemma hellinger_le_divergence {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) ≤ divergence p q := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    sqrt_sub_sq_le_relTerm (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

lemma tv_nonneg (p q : I → ℝ) : 0 ≤ tv p q := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

lemma tv_sq_le_hellinger {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q) :
    tv p q ^ 2 ≤ ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
  let f := fun i ↦ |Real.sqrt (p i) - Real.sqrt (q i)|
  let g := fun i ↦ Real.sqrt (p i) + Real.sqrt (q i)
  have hfactor (i : I) : |p i - q i| = f i * g i := by
    have he : p i - q i =
        (Real.sqrt (p i) - Real.sqrt (q i)) *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
      nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i))]
  have hsum : (∑ i, f i ^ 2) + (∑ i, g i ^ 2) = 4 := by
    rw [← sum_add_distrib]
    calc
      _ = (∑ i, (2 * p i + 2 * q i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [f, g]
        rw [sq_abs]
        nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
      _ = 4 := by norm_num [sum_add_distrib, ← mul_sum, hp.2, hq.2]
  have hf0 : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hg4 : ∑ i, g i ^ 2 ≤ 4 := by linarith
  have hc := sum_mul_sq_le_sq_mul_sq univ f g
  have hle := mul_le_mul_of_nonneg_left hg4 hf0
  have he : (∑ i, f i ^ 2) = ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
    simp [f]
  rw [tv, show (∑ i, |p i - q i|) = ∑ i, f i * g i from sum_congr rfl (fun i _ ↦ hfactor i)]
  rw [← he]
  nlinarith

lemma entropy_eq_sum {w p : I → ℝ} (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 ≤ p i) :
    entropy w p = ∑ i, (p i * Real.log (w i) - p i * Real.log (p i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div (hw i).ne' hi.ne', mul_sub]

lemma divergence_eq_sum {p q : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    divergence p q = ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div hi.ne' (hs i hi).ne', mul_sub]

lemma entropy_ge_neg_log_of_density {w p : I → ℝ} (_hw : ∀ i, 0 < w i)
    (hp : IsProb p) {b : ℝ} (hb : 0 < b) (hden : ∀ i, p i ≤ b * w i) :
    -Real.log b ≤ entropy w p := by
  have hi (i : I) : p i * (-Real.log b) ≤ p i * Real.log (w i / p i) := by
    rcases (hp.1 i).eq_or_lt with hi | hi
    · simp [← hi]
    apply mul_le_mul_of_nonneg_left _ hi.le
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.2 hb)
    apply (le_div_iff₀ hi).2
    calc
      b⁻¹ * p i = p i / b := by ring
      _ ≤ w i := (div_le_iff₀ hb).2 (by simpa [mul_comm] using hden i)
  have h := sum_le_sum (s := univ) fun i _ ↦ hi i
  simpa [← sum_mul, hp.2, entropy] using h

lemma tv_comm (p q : I → ℝ) : tv p q = tv q p := by
  simp only [tv, abs_sub_comm]

lemma tv_triangle (p q r : I → ℝ) : tv p r ≤ tv p q + tv q r := by
  have h := sum_le_sum (s := univ) fun i _ ↦ abs_sub_le (p i) (q i) (r i)
  simpa only [sum_add_distrib, tv, ← add_div] using div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

lemma weighted_sq_le {a f : I → ℝ} (ha : IsProb a) :
    (∑ i, a i * f i) ^ 2 ≤ ∑ i, a i * (f i) ^ 2 := by
  let m := ∑ i, a i * f i
  have h := sum_nonneg (s := univ) fun i _ ↦
    mul_nonneg (ha.1 i) (sq_nonneg (f i - m))
  have he : (∑ i, a i * (f i - m) ^ 2) = (∑ i, a i * (f i) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ i, (a i * (f i) ^ 2 - 2 * (a i * f i) * m + a i * m ^ 2) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ha.2]
        dsimp [m]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

omit [Fintype I] in
lemma mix_support {a : J → ℝ} {p : J → I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ j i, 0 ≤ p j i) {j : J} (hj : 0 < a j) {i : I} (hi : 0 < p j i) :
    0 < ∑ k, a k * p k i := by
  classical
  exact (mul_pos hj hi).trans_le (single_le_sum
    (fun k _ ↦ mul_nonneg (ha k) (hp k i)) (mem_univ j))

/-- The finite entropy-mixture identity for the averaged increment. -/
lemma entropy_mix_gap {w : I → ℝ} (hw : ∀ i, 0 < w i)
    {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a) (hp : ∀ j, IsProb (p j)) :
    entropy w (fun i ↦ ∑ j, a j * p j i) - ∑ j, a j * entropy w (p j) =
      ∑ j, a j * divergence (p j) (fun i ↦ ∑ k, a k * p k i) := by
  let b := fun i ↦ ∑ j, a j * p j i
  have hb := mix_isProb ha hp
  have hd (j : J) : a j * divergence (p j) b =
      a j * (∑ i, (p j i * Real.log (p j i) - p j i * Real.log (b i))) := by
    rcases (ha.1 j).eq_or_lt with hj | hj
    · simp [← hj]
    · rw [divergence_eq_sum (hp j).1
        (fun i hi ↦ mix_support ha.1 (fun k ↦ (hp k).1) hj hi)]
  change entropy w b - ∑ j, a j * entropy w (p j) = ∑ j, a j * divergence (p j) b
  rw [entropy_eq_sum hw hb.1]
  simp_rw [entropy_eq_sum hw (hp _).1, hd, mul_sum, mul_sub, sum_sub_distrib]
  have he (f : I → ℝ) : (∑ i, b i * f i) = ∑ j, ∑ i, a j * (p j i * f i) := by
    dsimp [b]
    simp_rw [sum_mul, mul_assoc]
    rw [sum_comm]
  rw [he, he]
  ring

lemma average_tv_sq_le_average_divergence {a : J → ℝ} (ha : IsProb a)
    {p q : J → I → ℝ} (hp : ∀ j, IsProb (p j)) (hq : ∀ j, IsProb (q j))
    (hs : ∀ j, 0 < a j → ∀ i, 0 < p j i → 0 < q j i) :
    (∑ j, a j * tv (p j) (q j)) ^ 2 ≤ ∑ j, a j * divergence (p j) (q j) := by
  apply (weighted_sq_le ha).trans
  apply sum_le_sum
  intro j _
  rcases (ha.1 j).eq_or_lt with hj | hj
  · simp [← hj]
  apply mul_le_mul_of_nonneg_left _ hj.le
  exact (tv_sq_le_hellinger (hp j) (hq j)).trans
    (hellinger_le_divergence (hp j) (hq j) (hs j hj))

omit [Fintype I] in
lemma mul_log_div {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    p * Real.log (w / p) = p * Real.log w - p * Real.log p := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  · rw [Real.log_div hw.ne' hp.ne', mul_sub]

omit [Fintype I] in
lemma partial_entropy_le (s : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hp : ∀ i ∈ s, 0 ≤ p i)
    {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ s, w i ≤ m) :
    (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
      (∑ i ∈ s, p i) * Real.log (m / (∑ i ∈ s, p i)) := by
  let t := ∑ i ∈ s, p i
  have ht : 0 ≤ t := sum_nonneg hp
  rcases ht.eq_or_lt with ht | ht
  · have hz : ∀ i ∈ s, p i = 0 := (sum_eq_zero_iff_of_nonneg hp).1 ht.symm
    simp only [show (∑ i ∈ s, p i) = 0 from ht.symm, zero_mul]
    apply le_of_eq
    exact sum_eq_zero (fun i hi ↦ by rw [hz i hi, zero_mul])
  have hi (i : I) (his : i ∈ s) :
      p i * Real.log (w i / p i) ≤ p i * Real.log (m / t) - p i + t * w i / m := by
    rcases (hp i his).eq_or_lt with hpi | hpi
    · simp only [← hpi, zero_mul, sub_self, zero_add]
      exact (div_pos (mul_pos ht (hw i his)) hm).le
    have hq : 0 < t * w i / m := div_pos (mul_pos ht (hw i his)) hm
    have hr := relTerm_nonneg hpi.le hq.le (fun _ ↦ hq)
    have hl : Real.log (p i / (t * w i / m)) =
        Real.log (m / t) - Real.log (w i / p i) := by
      rw [Real.log_div hpi.ne' hq.ne',
        Real.log_div (mul_pos ht (hw i his)).ne' hm.ne',
        Real.log_mul ht.ne' (hw i his).ne',
        Real.log_div hm.ne' ht.ne', Real.log_div (hw i his).ne' hpi.ne']
      ring
    rw [hl] at hr
    nlinarith
  have h := sum_le_sum hi
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_div, ← mul_sum] at h
  have hq : t * (∑ i ∈ s, w i) / m ≤ t := by
    apply (div_le_iff₀ hm).2
    exact mul_le_mul_of_nonneg_left hwm ht.le
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤ t * Real.log (m / t)
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
    t * Real.log (m / t) - t + t * (∑ i ∈ s, w i) / m at h
  linarith

lemma prob_sum_on {p : I → ℝ} (hp : IsProb p) (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : ∑ i ∈ D, p i = 1 := by
  rw [← hp.2]
  exact sum_subset (subset_univ _) (fun i _ hi ↦ hs i hi)

lemma entropy_sum_on {w p : I → ℝ} (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : entropy w p = ∑ i ∈ D, p i * Real.log (w i / p i) := by
  symm
  apply sum_subset (subset_univ _)
  intro i _ hi
  rw [hs i hi, zero_mul]

lemma entropy_supported_le_log (D : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p)
    (hs : ∀ i, i ∉ D → p i = 0) {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ D, w i ≤ m) :
    entropy w p ≤ Real.log m := by
  have h := partial_entropy_le D hw (fun i _ ↦ hp.1 i) hm hwm
  simpa only [prob_sum_on hp D hs, div_one, one_mul, ← entropy_sum_on D hs] using h

lemma entropy_supported_concentration (D s : Finset I) (hsD : s ⊆ D) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p) (hs : ∀ i, i ∉ D → p i = 0)
    {m M : ℝ} (hm : 1 ≤ m) (hM : 0 < M)
    (hwsmall : ∑ i ∈ s, w i ≤ m) (hwall : ∑ i ∈ D, w i ≤ M) :
    entropy w p ≤ Real.log 2 + Real.log m + (1 - ∑ i ∈ s, p i) * Real.log M := by
  classical
  let t := ∑ i ∈ s, p i
  let d := ∑ i ∈ D \ s, p i
  have ht : 0 ≤ t := sum_nonneg fun i _ ↦ hp.1 i
  have hd : 0 ≤ d := sum_nonneg fun i _ ↦ hp.1 i
  have htd : d + t = 1 := by
    dsimp [t, d]
    rw [sum_sdiff hsD, prob_sum_on hp D hs]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hwc : (∑ i ∈ D \ s, w i) ≤ M := by
    apply le_trans _ hwall
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i hi _ ↦ (hw i hi).le)
  have ha := partial_entropy_le s (fun i hi ↦ hw i (hsD hi)) (fun i _ ↦ hp.1 i) hm0 hwsmall
  have hc := partial_entropy_le (D \ s) (fun i hi ↦ hw i (mem_sdiff.1 hi).1)
    (fun i _ ↦ hp.1 i) hM hwc
  have he : entropy w p ≤ d * Real.log (M / d) + t * Real.log (m / t) := by
    rw [entropy_sum_on D hs, ← sum_sdiff hsD]
    exact add_le_add hc ha
  rw [mul_log_div hd hM, mul_log_div ht hm0] at he
  have hbin : -t * Real.log t - d * Real.log d ≤ Real.log 2 := by
    have hb := Real.binEntropy_le_log_two (p := t)
    have hd' : d = 1 - t := by linarith
    rw [hd']
    simpa [Real.binEntropy, Real.log_inv] using hb
  have hl := Real.log_nonneg hm
  have ht1 : t ≤ 1 := by linarith
  have hmterm : t * Real.log m ≤ Real.log m := by nlinarith
  change entropy w p ≤ Real.log 2 + Real.log m + (1 - t) * Real.log M
  have hd' : 1 - t = d := by linarith
  rw [hd']
  linarith

lemma entropy_tail_term {p w x a : ℝ} (hp : 0 ≤ p) (hw : 0 < w)
    (hx : 0 < x) (hd : p ≤ x * w) :
    (a + Real.log x) * (if p < w * Real.exp (-a) then p else 0) ≤
      p * (Real.log (w / p) + Real.log x) := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  have hlog := Real.log_le_log hp hd
  rw [Real.log_mul hx.ne' hw.ne'] at hlog
  have hlower : 0 ≤ Real.log (w / p) + Real.log x := by
    rw [Real.log_div hw.ne' hp.ne']
    linarith
  split_ifs with hsmall
  · have h := Real.log_lt_log hp hsmall
    rw [Real.log_mul hw.ne' (Real.exp_ne_zero _), Real.log_exp] at h
    have ha : a ≤ Real.log (w / p) := by
      rw [Real.log_div hw.ne' hp.ne']
      linarith
    nlinarith
  · simpa using mul_nonneg hp.le hlower

lemma entropy_tail {p w : I → ℝ} (hp : IsProb p) (hw : ∀ i, 0 < w i)
    {x a : ℝ} (hx : 0 < x) (hd : ∀ i, p i ≤ x * w i) :
    (a + Real.log x) * (∑ i, if p i < w i * Real.exp (-a) then p i else 0) ≤
      entropy w p + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    entropy_tail_term (a := a) (hp.1 i) (hw i) hx (hd i)
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hp.2, one_mul,
    entropy] using h

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.EdgeState =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

/-- Oriented edges, the disjoint union of the neighborhood state spaces. -/
abbrev EdgeState (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}

noncomputable instance edgeStateFintype (G : SimpleGraph V) : Fintype (EdgeState G) :=
  Subtype.fintype _

local instance (priority := 10000) edgeStateDecEq (G : SimpleGraph V) : DecidableEq (EdgeState G) :=
  Classical.decEq _

namespace EdgeState
variable {G : SimpleGraph V}
def src (e : EdgeState G) : V := e.val.1
def dst (e : EdgeState G) : V := e.val.2
omit [Fintype V] in
@[simp] lemma adj (e : EdgeState G) : G.Adj e.src e.dst := e.property

def rev (e : EdgeState G) : EdgeState G := ⟨(e.dst, e.src), e.adj.symm⟩
omit [Fintype V] in
@[simp] lemma src_rev (e : EdgeState G) : e.rev.src = e.dst := rfl
omit [Fintype V] in
@[simp] lemma dst_rev (e : EdgeState G) : e.rev.dst = e.src := rfl
omit [Fintype V] in
@[simp] lemma rev_rev (e : EdgeState G) : e.rev.rev = e := by cases e; rfl

def revEquiv : EdgeState G ≃ EdgeState G where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

lemma sum_fiber (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if e.src = u then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  rw [sum_eq (fun a b ↦ if a = u then f b else 0)]
  simp

lemma sum_fiber' (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if u = e.src then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  simpa only [eq_comm] using sum_fiber u f

end EdgeState

lemma growth_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : 0 ≤ growth x s :=
  mul_nonneg hs (add_nonneg hx (le_max_left _ _))

@[simp] lemma growth_zero (x : ℝ) : growth x 0 = 0 := by simp [growth]

lemma growth_small {x s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    growth x s = s * (x - Real.log s) := by
  have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  simp [growth, Real.log_inv, max_eq_right (neg_nonneg.2 hl), sub_eq_add_neg]

lemma growth_large {x s : ℝ} (hs : 1 ≤ s) : growth x s = s * x := by
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs
  simp [growth, Real.log_inv, max_eq_left (neg_nonpos.2 hl)]

lemma growth_mono {x : ℝ} (hx : 1 ≤ x) : MonotoneOn (growth x) (Set.Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha, growth_zero]
    exact growth_nonneg (by linarith) hb
  have hb0 : 0 < b := ha.trans_le hab
  by_cases hb1 : b ≤ 1
  · rw [growth_small ha (hab.trans hb1), growth_small hb0 hb1]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le hb0.le (fun _ ↦ hb0)
    rw [Real.log_div ha.ne' hb0.ne'] at hrel
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1
    have hmul := mul_nonneg (sub_nonneg.2 hab) (show 0 ≤ x - 1 - Real.log b by linarith)
    nlinarith
  by_cases ha1 : 1 ≤ a
  · rw [growth_large ha1, growth_large (le_of_not_ge hb1)]
    exact mul_le_mul_of_nonneg_right hab (by linarith)
  · rw [growth_small ha (le_of_not_ge ha1), growth_large (le_of_not_ge hb1)]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le (by norm_num : (0:ℝ) ≤ 1)
      (fun _ ↦ by norm_num)
    simp only [div_one] at hrel
    have hamul := mul_nonneg (sub_nonneg.2 (le_of_not_ge ha1)) (show 0 ≤ x - 1 by linarith)
    have hbmul := mul_nonneg (sub_nonneg.2 (le_of_not_ge hb1)) (show 0 ≤ x by linarith)
    nlinarith

lemma growth_le_twice {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    growth x s ≤ 2 * x * (s + Real.exp (-x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hexp := Real.exp_pos (-x)
  have hi (b : ℝ) (hb : Real.exp (-x) ≤ b) : growth x b ≤ 2 * x * b := by
    have hb0 := hexp.trans_le hb
    have hl : -Real.log b ≤ x := by
      have := Real.log_le_log hexp hb
      rw [Real.log_exp] at this
      linarith
    have hmax : max 0 (-Real.log b) ≤ x := max_le hx0 hl
    simp only [growth, one_div, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left hmax hb0.le]
  by_cases h : Real.exp (-x) ≤ s
  · have h' := hi s h
    nlinarith [mul_nonneg hx0 hexp.le]
  · have h' := (growth_mono hx hs hexp.le (le_of_not_ge h)).trans (hi _ le_rfl)
    nlinarith [mul_nonneg hx0 hs]

omit [Fintype V] in
lemma mass_union_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    mass w (A ∪ B) ≤ mass w A + mass w B := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := w)
  have hn := mass_nonneg hw (A ∩ B)
  change 0 ≤ ∑ u ∈ A ∩ B, w u at hn
  change (∑ u ∈ A ∪ B, w u) ≤ (∑ u ∈ A, w u) + ∑ u ∈ B, w u
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Packing =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

/-- Greedy disjoint-neighborhood packing, with a subprobability lottery. The additional
zero outcome is inserted only at the end. -/
lemma neighborhood_packing (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (A : Finset V) {s η b B : ℝ} (hs : 0 < s) (hη : 0 < η) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hbig : 2/η*b ≤ B) (_hAs : mass w A ≤ s)
    (hlocal : ∀ (R : Finset V), R ⊆ A → ∀ v ∈ R,
      η*s < mass w (R ∩ neighbors G v) →
      ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L (R ∩ neighbors G v) b ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R ∩ neighbors G v then 1 else 0) ∧
        expectedEdges G w L ≤ η * (mass w (R ∩ neighbors G v))^2) :
    ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w A/(2*s) ∧
      BoundedOn L A B ∧
      (∀ u, expect L (fun m ↦ m u) = if u ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ 2*η*s*mass w A := by
  classical
  have hw0 := fun v ↦ (hw v).le
  suffices hpack : ∀ R : Finset V, R ⊆ A →
      ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w R/(2*s) ∧
        BoundedOn L R B ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R then 1 else 0) ∧
        expectedEdges G w L ≤ 2*η*s*mass w R by exact hpack A Subset.rfl
  intro R
  refine Finset.strongInductionOn R ?_
  intro R ih hRA
  by_cases hsmall : ∀ v ∈ R, mass w (R ∩ neighbors G v) ≤ η*s
  · let m : V → ℝ := restrict R (fun _ ↦ 2)
    let L : Law (V → ℝ) := [(1/2,m)]
    refine ⟨L,?_,?_,?_,?_,?_⟩
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']; norm_num
    · have hr := div_nonneg (mass_nonneg hw0 R) (by positivity : 0 ≤ 2*s)
      simp only [L,total,expect_singleton,mul_one]
      linarith
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']
      refine ⟨?_,?_⟩
      · intro v
        dsimp [m,restrict]
        split_ifs <;> constructor <;> linarith
      · intro v hv
        simp [m,restrict,hv]
    · intro v
      simp [L,m,restrict]
    · have he := edgeMass_restrict_le G hw0 R hsmall
      have heq : (fun v ↦ w v*m v) = fun v ↦ 2*restrict R w v := by
        funext v
        by_cases hv : v ∈ R <;> simp [m,restrict,hv,mul_comm]
      simp only [L,expectedEdges,expect_singleton,heq,edgeMass_smul]
      have hn := mul_nonneg (mul_nonneg hη.le hs.le) (mass_nonneg hw0 R)
      nlinarith
  · push Not at hsmall
    obtain ⟨v,hv,hvlarge⟩ := hsmall
    let D := R ∩ neighbors G v
    have hDR : D ⊆ R := inter_subset_left
    have hDpos : 0 < mass w D := (mul_pos hη hs).trans hvlarge
    have hDne : D.Nonempty := by
      by_contra hn
      have he : D = ∅ := not_nonempty_iff_eq_empty.1 hn
      simp [he,mass] at hDpos
    obtain ⟨L,hLp,hLb,hLm,hLe⟩ := hlocal R hRA v hv hvlarge
    obtain ⟨K,hKp,hKt,hKb,hKm,hKe⟩ := ih (R \ D) (sdiff_ssubset hDR hDne) (sdiff_subset.trans hRA)
    let p := mass w D / (2*s)
    have hp : 0 < p := div_pos hDpos (by positivity)
    have hpη : η/2 < p := by
      apply (lt_div_iff₀ (by positivity : 0 < 2*s)).2
      nlinarith only [hvlarge]
    have hik : (1/p)*b ≤ B := by
      have hi : 1/p ≤ 2/η := by
        apply (div_le_div_iff₀ hp hη).2
        linarith
      exact (mul_le_mul_of_nonneg_right hi hb).trans hbig
    let J := transform p (fun m u ↦ (1/p)*m u) L
    have hJp : Positive J := positive_transform hp.le _ hLp.1
    have hJb : BoundedOn J D B := bounded_transform hLb (one_div_nonneg.2 hp.le) hik p
    have hpart : mass w (R \ D) + mass w D = mass w R := by
      exact sum_sdiff hDR
    have hJt : total J = p := by
      rw [total_transform,hLp.2,mul_one]
    have hJm (u : V) : expect J (fun m ↦ m u) = if u ∈ D then 1 else 0 := by
      rw [mean_transform,hLm,mul_one_div_cancel hp.ne',one_mul]
    have hJe : expectedEdges G w J ≤ 2*η*s*mass w D := by
      rw [expectedEdges_transform]
      have he := mul_le_mul_of_nonneg_left hLe (by positivity : 0 ≤ p*(1/p)^2)
      have hid : p*(1/p)^2*(η*(mass w D)^2) = 2*η*s*mass w D := by
        dsimp [p]
        field_simp
      exact he.trans_eq hid
    refine ⟨J++K,positive_append hJp hKp,?_,bounded_append hJb hKb hDR sdiff_subset,?_,?_⟩
    · change expect (J++K) (fun _ ↦ 1) ≤ _
      rw [expect_append]
      change total J + total K ≤ _
      rw [hJt]
      dsimp [p]
      have hparts : mass w D/(2*s) + mass w (R \ D)/(2*s) = mass w R/(2*s) := by
        rw [← add_div]
        congr 1
        linarith only [hpart]
      linarith only [hKt,hparts]
    · intro u
      rw [expect_append,hJm,hKm]
      by_cases hu : u ∈ D
      · have huR := hDR hu
        simp [hu,huR]
      · by_cases huR : u ∈ R <;> simp [hu,huR]
    · change expect (J++K) _ ≤ _
      rw [expect_append]
      change expectedEdges G w J + expectedEdges G w K ≤ _
      calc
        _ ≤ 2*η*s*mass w D + 2*η*s*mass w (R \ D) := add_le_add hJe hKe
        _ = _ := by rw [← mul_add,add_comm (mass w D),hpart]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.SparseMultipliers =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

/-- The bound `b_(k+2)(ε)`, indexed by the excess clique size. -/
noncomputable def multiplierBound (k : ℕ) (ε : ℝ) : ℝ := 2^((k+2)*k) / ε^k

lemma multiplierBound_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < multiplierBound k ε := by
  unfold multiplierBound
  positivity

lemma multiplierBound_ge_one (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ multiplierBound k ε := by
  unfold multiplierBound
  apply (le_div_iff₀ (pow_pos hε k)).2
  simpa using (pow_le_one₀ hε.le hε1 : ε^k ≤ 1).trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

lemma multiplierBound_step (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    multiplierBound (k+1) ε = (8/ε)*multiplierBound k (ε/4) := by
  have hn : (k+1+2)*(k+1) = 3+2*k+(k+2)*k := by ring
  have hp : (2:ℝ)^((k+1+2)*(k+1)) = 8*4^k*2^((k+2)*k) := by
    rw [hn,pow_add,pow_add,pow_mul]
    norm_num
  unfold multiplierBound
  rw [hp,pow_succ,div_pow]
  field_simp

lemma sparse_multipliers_on (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 < w v) (A : Finset V) (hfree : G.CliqueFreeOn (↑A) (k+2))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L A (multiplierBound k ε) ∧
      (∀ v, expect L (fun m ↦ m v) = if v ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ ε * (mass w A)^2 := by
  classical
  induction k generalizing A ε with
  | zero =>
    let m : V → ℝ := restrict A (fun _ ↦ 1)
    let L : Law (V → ℝ) := [(1,m)]
    have he : edgeMass G (restrict A w) = 0 := by
      rw [edgeMass_restrict]
      have hc : crossMass G w A A = 0 := by
        unfold crossMass
        apply sum_eq_zero
        intro u hu
        apply sum_eq_zero
        intro v hv
        have hnot : ¬ G.Adj u v := by
          intro hadj
          exact ((SimpleGraph.cliqueFreeOn_two G).1 hfree) hu hv hadj.ne hadj
        simp [hnot]
      rw [hc,zero_div]
    refine ⟨L,⟨?_,?_⟩,?_,?_,?_⟩
    · intro z hz
      have hz' : z = (1,m) := by simpa [L] using hz
      rw [hz']; norm_num
    · simp [L,total]
    · intro z hz
      have hz' : z = (1,m) := by simpa [L] using hz
      rw [hz']
      constructor
      · intro v
        simp only [m,restrict,multiplierBound,Nat.mul_zero,pow_zero,div_one]
        split_ifs <;> norm_num
      · intro v hv
        simp [m,restrict,hv]
    · intro v
      simp [L,m,restrict]
    · have heq : (fun v ↦ w v*m v) = restrict A w := by
        funext v
        by_cases hv : v ∈ A <;> simp [m,restrict,hv]
      simp only [L,expectedEdges,Lottery.expect_singleton,heq,he,mul_zero]
      positivity
  | succ k ih =>
    by_cases hA : A = ∅
    · subst A
      refine ⟨[(1,0)],⟨?_,by simp [total]⟩,?_,?_,?_⟩
      · intro z hz
        have hz' : z = (1,0) := by simpa using hz
        rw [hz']; norm_num
      · intro z hz
        have hz' : z = (1,0) := by simpa using hz
        rw [hz']
        exact ⟨fun _ ↦ ⟨le_rfl,(multiplierBound_pos (k+1) hε).le⟩,fun _ _ ↦ rfl⟩
      · intro v; simp
      · simp [expectedEdges,edgeMass,crossMass,mass]
    have hmass : 0 < mass w A := by
      exact sum_pos (fun v _ ↦ hw v) (nonempty_iff_ne_empty.2 hA)
    let η := ε/4
    let b := multiplierBound k η
    have hη : 0 < η := by dsimp [η]; positivity
    have hηhalf : η ≤ 1/2 := by dsimp [η]; linarith
    have hb := (multiplierBound_pos k hη).le
    have hbig : 2/η*b = multiplierBound (k+1) ε := by
      rw [multiplierBound_step k hε]
      dsimp [η,b]
      congr 1
      ring
    have hB : 2 ≤ multiplierBound (k+1) ε := by
      rw [← hbig]
      have hb1 : 1 ≤ b := multiplierBound_ge_one k hη (by linarith)
      have hi : 2 ≤ 2/η := (le_div_iff₀ hη).2 (by linarith)
      nlinarith
    obtain ⟨L,hLp,hLt,hLb,hLm,hLe⟩ := neighborhood_packing G hw A hmass hη hb hB hbig.le le_rfl
      (by
        intro R hRA v hv hlarge
        apply ih (R ∩ neighbors G v)
        · apply SimpleGraph.CliqueFreeOn.subset G _ (SimpleGraph.CliqueFreeOn.of_succ G hfree (hRA hv))
          intro u hu
          exact ⟨hRA (mem_inter.1 hu).1,(mem_neighbors G v u).1 (mem_inter.1 hu).2⟩
        · exact hη
        · exact hηhalf)
    have ht : total L ≤ 1 := by
      have he : 1/2+mass w A/(2*mass w A) = 1 := by
        field_simp [hmass.ne']
        norm_num
      exact hLt.trans_eq he
    obtain ⟨K,hKp,hKb,hKm,hKe⟩ := normalize_subprob G w hLp ht (multiplierBound_pos (k+1) hε).le hLb
    refine ⟨K,hKp,hKb,fun v ↦ (hKm v).trans (hLm v),?_⟩
    rw [hKe]
    have hε0 := mul_nonneg hε.le (sq_nonneg (mass w A))
    dsimp [η] at hLe
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.VariationalCross =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

lemma edgeForm_smul_left (G : SimpleGraph V) (a b : V → ℝ) (t : ℝ) :
    edgeForm G (fun v ↦ t*a v) b = t*edgeForm G a b := by
  unfold edgeForm
  simp only [mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  split_ifs <;> ring

lemma edgeForm_smul_right (G : SimpleGraph V) (a b : V → ℝ) (t : ℝ) :
    edgeForm G a (fun v ↦ t*b v) = t*edgeForm G a b := by
  rw [edgeForm_symm,edgeForm_smul_left,edgeForm_symm G b a]

lemma edgeMass_lin_sub (G : SimpleGraph V) (a b : V → ℝ) (k : ℝ) :
    edgeMass G (fun v ↦ k*a v-b v) =
      k^2*edgeMass G a + edgeMass G b - k*edgeForm G a b := by
  have he : (fun v ↦ k*a v-b v) = (fun v ↦ k*a v)+(fun v ↦ (-1)*b v) := by
    ext v; simp; ring
  rw [he,edgeMass_add,edgeMass_smul,edgeMass_smul,edgeForm_smul_left,edgeForm_smul_right]
  ring

lemma edgeForm_restrict (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) :
    edgeForm G (restrict S w) (restrict D w) = crossMass G w S D := by
  classical
  unfold edgeForm crossMass restrict
  calc
    _ = ∑ u, if u ∈ S then ∑ v, if v ∈ D then (if G.Adj u v then w u*w v else 0) else 0 else 0 := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u ∈ S
      · simp only [hu,ite_true]
        apply sum_congr rfl
        intro v _
        by_cases hv : v ∈ D <;> simp [hv]
      · simp [hu]
    _ = _ := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
      apply sum_congr rfl
      intro u hu
      rw [← sum_filter]
      simp

lemma expected_weight (w : V → ℝ) (L : Law (V → ℝ)) (S : Finset V)
    (hmean : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0) :
    expect L (fun m ↦ ∑ v, w v*m v) = mass w S := by
  classical
  rw [expect_sum]
  simp_rw [Lottery.expect_mul,hmean,mul_ite,mul_one,mul_zero]
  rw [← sum_filter]
  simp [mass]

lemma expected_edgeForm (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) (S D : Finset V)
    (hmean : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0) :
    expect L (fun m ↦ edgeForm G (fun v ↦ w v*m v) (restrict D w)) = crossMass G w S D := by
  classical
  rw [← edgeForm_restrict]
  simp only [edgeForm_neighbor]
  rw [expect_sum]
  apply sum_congr rfl
  intro u _
  have hf : (fun m : V → ℝ ↦ w u*m u*neighborMass G (restrict D w) u) =
      (fun m ↦ (w u*neighborMass G (restrict D w) u)*m u) := by ext m; ring
  rw [hf,Lottery.expect_mul,hmean]
  by_cases hu : u ∈ S <;> simp [restrict,hu]

lemma vertex_divergence_upper {w y L : ℝ} (hw : 0 < w) (hy : 0 ≤ y) (hL : y ≤ L) :
    (w*(1+y))*Real.log ((w*(1+y))/w) - w*(1+y) + w ≤ w*y*Real.log (1+L) := by
  have hy1 : 0 < 1+y := by linarith
  have hL1 : 0 < 1+L := hy1.trans_le (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hy1
  have hmono := Real.log_le_log hy1 (by linarith : 1+y ≤ 1+L)
  have hlo : w*y*Real.log (1+y) ≤ w*y*Real.log (1+L) :=
    mul_le_mul_of_nonneg_left hmono (mul_nonneg hw.le hy)
  have hcancel : w*(1+y)/w = 1+y := by field_simp
  rw [hcancel]
  nlinarith [mul_le_mul_of_nonneg_left hlog hw.le]

lemma variational_cross_lottery (G : SimpleGraph V) {w : V → ℝ} (hw : IsOptimizer G w)
    (S D : Finset V) (hSD : Disjoint S D) (L : Law (V → ℝ)) (hp : IsProb L)
    {b k ε : ℝ} (hk : 0 ≤ k) (hb : BoundedOn L S b)
    (hm : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0)
    (he : expectedEdges G w L ≤ ε*(mass w S)^2) :
    k*crossMass G w S D ≤ k^2*ε*(mass w S)^2 + (mass w D)^2/2 + mass w D +
      k*Real.log (1+k*b)*mass w S := by
  classical
  have hwpos := fun v ↦ (optimizer_stationary hw v).1
  have hw0 := fun v ↦ (hwpos v).le
  let cost (m : V → ℝ) : ℝ :=
    k*Real.log (1+k*b)*(∑ v, w v*m v) + mass w D +
      (k^2*edgeMass G (fun v ↦ w v*m v) + edgeMass G (restrict D w) -
        k*edgeForm G (fun v ↦ w v*m v) (restrict D w))
  have hcost (z : ℝ × (V → ℝ)) (hz : z ∈ L) : 0 ≤ cost z.2 := by
    let m := z.2
    have hm0 := fun v ↦ (hb z hz).1 v |>.1
    have hmb := fun v ↦ (hb z hz).1 v |>.2
    have hmD (v : V) (hv : v ∈ D) : m v = 0 :=
      (hb z hz).2 v (disjoint_left.1 hSD · hv)
    let q : V → ℝ := fun v ↦ if v ∈ D then 0 else w v*(1+k*m v)
    have hq (v : V) : 0 ≤ q v := by
      dsimp [q]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw0 v) (by nlinarith [mul_nonneg hk (hm0 v)])
    obtain ⟨hdiv,heq⟩ := optimizer_divergence hw q hq
    rw [heq] at hdiv
    have hve (v : V) : q v*Real.log (q v/w v)-q v+w v ≤
        k*Real.log (1+k*b)*(w v*m v) + if v ∈ D then w v else 0 := by
      by_cases hv : v ∈ D
      · simp [q,hv,hmD v hv]
      · have hh := vertex_divergence_upper (hwpos v) (mul_nonneg hk (hm0 v))
          (mul_le_mul_of_nonneg_left (hmb v) hk)
        dsimp [q]
        rw [if_neg hv,if_neg hv]
        nlinarith only [hh]
    have hD : (∑ v, if v ∈ D then w v else 0) = mass w D := by
      rw [← sum_filter]; simp [mass]
    have hvs : (∑ v, (q v*Real.log (q v/w v)-q v+w v)) ≤
        k*Real.log (1+k*b)*(∑ v, w v*m v) + mass w D := by
      calc
        _ ≤ ∑ v, (k*Real.log (1+k*b)*(w v*m v) + if v ∈ D then w v else 0) :=
          sum_le_sum fun v _ ↦ hve v
        _ = _ := by rw [sum_add_distrib,← mul_sum,hD]
    have hqsub : q-w = fun v ↦ k*(w v*m v)-restrict D w v := by
      ext v
      by_cases hv : v ∈ D <;> simp [q,restrict,hv,hmD v,Pi.sub_apply]
      ring
    rw [hqsub,edgeMass_lin_sub] at hdiv
    dsimp [cost,m]
    linarith only [hdiv,hvs]
  have havg : 0 ≤ expect L cost := by
    have hh := expect_mono hp.1 (f := fun _ ↦ 0) (g := cost) (fun z hz ↦ hcost z hz)
    simpa [Lottery.expect_const] using hh
  have hec : expect L cost =
      k*Real.log (1+k*b)*mass w S + mass w D +
        (k^2*expectedEdges G w L + edgeMass G (restrict D w) - k*crossMass G w S D) := by
    have hsub (a b : (V → ℝ) → ℝ) : expect L (fun m ↦ a m-b m) = expect L a-expect L b := by
      have hf : (fun m ↦ a m-b m) = (fun m ↦ a m+(-1)*b m) := by ext m; ring
      rw [hf,expect_add,Lottery.expect_mul]; ring
    dsimp [cost]
    rw [expect_add,expect_add,hsub,expect_add,Lottery.expect_mul,expected_weight w L S hm,
      Lottery.expect_const,hp.2,mul_one,Lottery.expect_mul,Lottery.expect_const,hp.2,mul_one,Lottery.expect_mul,
      expected_edgeForm G w L S D hm]
    rfl
  rw [hec] at havg
  have hDedge : edgeMass G (restrict D w) ≤ (mass w D)^2/2 := by
    rw [edgeMass_restrict]
    exact div_le_div_of_nonneg_right (by simpa [sq] using crossMass_le_product G hw0 D D) (by norm_num)
  have hmult := mul_le_mul_of_nonneg_left he (sq_nonneg k)
  nlinarith only [havg,hDedge,hmult]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.DisjointCross =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

/-- A logarithm estimate with `log 2 ≤ 1` already applied. -/
lemma log_multiplier_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) ≤
      (5 + 10*(k:ℝ) + (k:ℝ)^2)*x := by
  have hx0 : 0 ≤ x := by linarith
  have hε : Real.exp (-8*x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hb := multiplierBound_ge_one k (Real.exp_pos _) hε
  have he : 1 ≤ Real.exp (4*x) := Real.one_le_exp_iff.2 (by linarith)
  have hprod : 1 ≤ Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) :=
    one_le_mul_of_one_le_of_one_le he hb
  have hm := Real.log_le_log (by positivity : 0 < 1 + Real.exp (4*x) *
      multiplierBound k (Real.exp (-8*x)))
    (show 1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) ≤
      2 * (Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) by linarith)
  have hbpos := multiplierBound_pos k (Real.exp_pos (-8*x))
  have hlogb : Real.log (multiplierBound k (Real.exp (-8*x))) =
      (((k:ℝ)+2)*k)*Real.log 2 + 8*(k:ℝ)*x := by
    unfold multiplierBound
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  rw [Real.log_mul (by norm_num) (mul_pos (Real.exp_pos _) hbpos).ne',
    Real.log_mul (Real.exp_ne_zero _) hbpos.ne', Real.log_exp,hlogb] at hm
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (1 + ((k:ℝ)+2)*k) := by positivity
  have haux := mul_le_mul_of_nonneg_left hlog2 hc
  have hxaux := mul_le_mul_of_nonneg_left hx hc
  nlinarith

lemma cross_error_le {s t x : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hslo : Real.exp (-x) ≤ s) (hsup : s ≤ Real.exp x) (htup : t ≤ Real.exp x) :
    s^2 + t^2/2 + t ≤ 3 * Real.exp (4*x) * x * s := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : s ≤ Real.exp (4*x) := hsup.trans (Real.exp_le_exp.2 (by linarith))
  have hss : s^2 ≤ Real.exp (4*x)*s := by nlinarith [mul_le_mul_of_nonneg_right h1 hs]
  have hks : Real.exp (3*x) ≤ Real.exp (4*x)*s := by
    calc
      _ = Real.exp (4*x)*Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hslo (Real.exp_pos _).le
  have ht1 : t ≤ Real.exp (4*x)*s :=
    htup.trans ((Real.exp_le_exp.2 (by linarith : x ≤ 3*x)).trans hks)
  have ht2 : t^2 ≤ Real.exp (4*x)*s := by
    calc
      _ ≤ (Real.exp x)^2 := sq_le_sq₀ ht (Real.exp_pos x).le |>.2 htup
      _ = Real.exp (2*x) := by rw [sq,← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (3*x) := Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := hks
  have hscale := mul_le_mul_of_nonneg_left hx (mul_nonneg (Real.exp_pos (4*x)).le hs)
  nlinarith

lemma optimizer_cross_disjoint_moderate (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hslo : Real.exp (-x) ≤ mass w S) (hsup : mass w S ≤ Real.exp x)
    (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (8 + 10*(k:ℝ) + (k:ℝ)^2)*x*mass w S := by
  have hwpos := fun v ↦ (optimizer_stationary hw v).1
  have hεhalf : Real.exp (-8*x) ≤ 1/2 := by
    have hl : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  obtain ⟨L,hp,hb,hm,he⟩ := sparse_multipliers_on k G hwpos S hfree (Real.exp_pos (-8*x)) hεhalf
  have h := variational_cross_lottery G hw S D hSD L hp (Real.exp_pos (4*x)).le hb hm he
  have hcancel : (Real.exp (4*x))^2 * Real.exp (-8*x) = 1 := by
    rw [sq,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  rw [hcancel,one_mul] at h
  have hlog := log_multiplier_le k hx
  have hw0 := fun v ↦ (hwpos v).le
  have hs := mass_nonneg hw0 S
  have ht := mass_nonneg hw0 D
  have hlogs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (Real.exp_pos (4*x)).le) hs
  have herr := cross_error_le hx hs ht hslo hsup htup
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (4*x))).1
  nlinarith only [h,hlogs,herr]

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
variable {V : Type u} [Fintype V]

lemma optimizer_cross_disjoint (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hsup : mass w S ≤ Real.exp x) (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (4*((k:ℝ)+2)^2)*growth x (mass w S) := by
  have hw0 := fun v ↦ (optimizer_stationary hw v).1.le
  have hs := mass_nonneg hw0 S
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hcoeff : 8+10*(k:ℝ)+(k:ℝ)^2 ≤ 4*((k:ℝ)+2)^2 := by nlinarith
  have hcoeff0 : 0 ≤ 8+10*(k:ℝ)+(k:ℝ)^2 := by positivity
  rcases hs.eq_or_lt with hs | hs
  · have hc := crossMass_le_product G hw0 S D
    simpa [← hs] using hc
  by_cases hlo : Real.exp (-x) ≤ mass w S
  · have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hx hlo hsup htup
    have hg : x*mass w S ≤ growth x (mass w S) := by
      unfold growth
      nlinarith [mul_nonneg hs.le (le_max_left 0 (Real.log (1/mass w S)))]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(x*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)
  · let y := Real.log (1/mass w S)
    have hxy : x ≤ y := by
      have hlog := Real.log_le_log hs (le_of_not_ge hlo)
      rw [Real.log_exp] at hlog
      dsimp [y]
      rw [one_div,Real.log_inv]
      linarith
    have hy : 1 ≤ y := hx.trans hxy
    have hsy : Real.exp (-y) = mass w S := by
      dsimp [y]
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log hs]
    have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hy hsy.le
      (hsup.trans (Real.exp_le_exp.2 hxy)) (htup.trans (Real.exp_le_exp.2 hxy))
    have hg : y*mass w S ≤ growth x (mass w S) := by
      unfold growth
      have hmax := le_max_right 0 y
      change y*mass w S ≤ mass w S*(x+max 0 y)
      nlinarith [mul_le_mul_of_nonneg_right hmax hs.le]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(y*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.CrossBound =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
local instance classicalDecEq802 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V : Type u} [Fintype V]

section ColoringCount
variable [DecidableEq V]

lemma bool_point_count (u : V) (b : Bool) :
    (∑ f : V → Bool, if f u = b then (1:ℝ) else 0) =
      (Fintype.card (V → Bool) : ℝ)/2 := by
  let e := Equiv.funSplitAt u Bool
  have hc : (Fintype.card (V → Bool) : ℝ) =
      2*(Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ ↦ (n:ℝ)) h
  calc
    _ = (Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
      rw [← e.symm.sum_comp (fun f : V → Bool ↦ if f u = b then (1:ℝ) else 0)]
      rw [Fintype.sum_prod_type,Fintype.sum_bool]
      cases b <;> simp [e,Equiv.funSplitAt_symm_apply]
    _ = _ := by linarith

lemma bool_pair_count (u v : V) (huv : u ≠ v) :
    (∑ f : V → Bool, if f u = false ∧ f v = true then (1:ℝ) else 0) =
      (Fintype.card (V → Bool) : ℝ)/4 := by
  let e := Equiv.funSplitAt u Bool
  have hc : (Fintype.card (V → Bool) : ℝ) =
      2*(Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ ↦ (n:ℝ)) h
  have hsum := e.symm.sum_comp (fun f : V → Bool ↦
    if f u = false ∧ f v = true then (1:ℝ) else 0)
  rw [Fintype.sum_prod_type,Fintype.sum_bool] at hsum
  simp only [e,Equiv.funSplitAt_symm_apply,eq_self,dite_true,dif_neg huv.symm,
    Bool.true_eq_false,false_and,ite_false,true_and,sum_const_zero,zero_add] at hsum
  rw [← hsum, bool_point_count (⟨v,huv.symm⟩ : {j : V // j ≠ u}) true]
  linarith only [hc]

end ColoringCount

omit [Fintype V] in
lemma crossMass_colored (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) (f : V → Bool) :
    crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) =
      ∑ u ∈ S, ∑ v ∈ D, (if f u = false ∧ f v = true then (1:ℝ) else 0) *
        (if G.Adj u v then w u*w v else 0) := by
  classical
  unfold crossMass
  rw [sum_filter]
  apply sum_congr rfl
  intro u _
  rw [sum_filter]
  by_cases hu : f u = false
  · simp only [hu,true_and,ite_true]
    apply sum_congr rfl
    intro v _
    split_ifs <;> simp
  · simp [hu]

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
variable {V : Type u} [Fintype V]

lemma sum_colored_cross [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) :
    (∑ f : V → Bool, crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true)) =
      (Fintype.card (V → Bool) : ℝ)/4 * crossMass G w S D := by
  simp_rw [crossMass_colored]
  rw [sum_comm]
  unfold crossMass
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro v _
  classical
  by_cases huv : G.Adj u v
  · simp only [if_pos huv]
    rw [← sum_mul,bool_pair_count u v huv.ne]
  · simp [huv]

/-- Full optimizer cross mass, including overlapping sets, with an explicit constant. -/
theorem optimizer_cross_bound (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (hfree : G.CliqueFree (k+2)) :
    CrossBound G w (16*((k:ℝ)+2)^2) := by
  classical
  intro x hx S D hs ht
  have hw0 := fun v ↦ (optimizer_stationary hw v).1.le
  have hpoint (f : V → Bool) :
      crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) ≤
        (4*((k:ℝ)+2)^2)*growth x (mass w S) := by
    have hSD : Disjoint (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) := by
      apply disjoint_left.2
      intro v hv hv'
      have h1 := (mem_filter.1 hv).2
      have h2 := (mem_filter.1 hv').2
      rw [h1] at h2
      contradiction
    have hS := mass_mono hw0 (filter_subset (fun u ↦ f u = false) S)
    have hD := mass_mono hw0 (filter_subset (fun v ↦ f v = true) D)
    have h := optimizer_cross_disjoint k G hw _ _ hSD hfree.cliqueFreeOn hx
      (hS.trans hs) (hD.trans ht)
    exact h.trans (mul_le_mul_of_nonneg_left
      (growth_mono hx (mass_nonneg hw0 _) (mass_nonneg hw0 _) hS) (by positivity))
  have hsum := sum_le_sum (s := (univ : Finset (V → Bool))) fun f _ ↦ hpoint f
  rw [sum_colored_cross] at hsum
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  have hn : 0 < (Fintype.card (V → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hn).1
  nlinarith only [hsum]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.TriangleState =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere1 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

abbrev TriangleState (G : SimpleGraph V) :=
  {t : V × V × V // G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2}

noncomputable instance triangleStateFintype (G : SimpleGraph V) : Fintype (TriangleState G) :=
  Subtype.fintype _

namespace TriangleState
variable {G : SimpleGraph V}
def first (t : TriangleState G) : V := t.val.1
def second (t : TriangleState G) : V := t.val.2.1
def third (t : TriangleState G) : V := t.val.2.2

omit [Fintype V] in
@[simp] lemma adj12 (t : TriangleState G) : G.Adj t.first t.second := t.property.1
omit [Fintype V] in
@[simp] lemma adj13 (t : TriangleState G) : G.Adj t.first t.third := t.property.2.1
omit [Fintype V] in
@[simp] lemma adj23 (t : TriangleState G) : G.Adj t.second t.third := t.property.2.2

def edge12 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.second), t.adj12⟩
def edge13 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.third), t.adj13⟩
def edge23 (t : TriangleState G) : EdgeState G := ⟨(t.second, t.third), t.adj23⟩

def swap (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.first, t.third), t.adj12.symm, t.adj23, t.adj13⟩
def rotate (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.third, t.first), t.adj23, t.adj12.symm, t.adj13.symm⟩

def swapEquiv : TriangleState G ≃ TriangleState G where
  toFun := swap
  invFun := swap
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def rotateEquiv : TriangleState G ≃ TriangleState G where
  toFun := rotate
  invFun := rotate ∘ rotate
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

noncomputable def weight (w : V → ℝ) (t : TriangleState G) : ℝ :=
  w t.first * w t.second * w t.third

omit [Fintype V] in
lemma weight_pos {w : V → ℝ} (hw : ∀ u, 0 < w u) (t : TriangleState G) :
    0 < weight w t := mul_pos (mul_pos (hw _) (hw _)) (hw _)

omit [Fintype V] in
@[simp] lemma weight_swap (w : V → ℝ) (t : TriangleState G) :
    weight w (swap t) = weight w t := by unfold weight swap first second third; ring
omit [Fintype V] in
@[simp] lemma weight_rotate (w : V → ℝ) (t : TriangleState G) :
    weight w (rotate t) = weight w t := by unfold weight rotate first second third; ring

lemma sum_rotate (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (rotate t)) = ∑ t, weight w t * f t := by
  simpa only [rotateEquiv, Equiv.coe_fn_mk, weight_rotate] using rotateEquiv.sum_comp (fun t ↦ weight w t * f t)

lemma sum_swap (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (swap t)) = ∑ t, weight w t * f t := by
  simpa only [swapEquiv, Equiv.coe_fn_mk, weight_swap] using swapEquiv.sum_comp (fun t ↦ weight w t * f t)

lemma sum_eq (f : V → V → V → ℝ) :
    (∑ t : TriangleState G, f t.first t.second t.third) =
      ∑ u, ∑ v ∈ neighbors G u, ∑ z ∈ neighbors G u,
        if G.Adj v z then f u v z else 0 := by
  classical
  change (∑ t : {t : V × V × V // _}, f t.val.1 t.val.2.1 t.val.2.2) = _
  rw [← Finset.sum_subtype (univ.filter fun t : V × V × V ↦
    G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)
    (by simp) (fun t : V × V × V ↦ f t.1 t.2.1 t.2.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : G.Adj u v
  · simp only [huv, true_and, ↓reduceIte]
    apply sum_congr rfl
    intro z _
    by_cases huz : G.Adj u z <;> simp [huz]
  · simp [huv]

lemma sum_weight (w : V → ℝ) : (∑ t : TriangleState G, weight w t) = 6 * triangleMass G w := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z), triangleMass_eq_sum]
  simp only [triangleAt, commonMass_eq_sum, mul_sum, mul_ite, mul_zero, mul_assoc]

lemma marginal (w : V → ℝ) (f : V → V → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.first t.second) =
      ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * f e.src e.dst := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z * f u v), EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v * f u v)]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  rw [commonMass_eq_sum]
  simp only [mul_sum, sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

def flip (t : TriangleState G) : TriangleState G :=
  ⟨(t.first, t.third, t.second), t.adj13, t.adj12, t.adj23.symm⟩

def flipEquiv : TriangleState G ≃ TriangleState G where
  toFun := flip
  invFun := flip
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

omit [Fintype V] in
@[simp] lemma weight_flip (w : V → ℝ) (t : TriangleState G) :
    weight w (flip t) = weight w t := by unfold weight flip first second third; ring

lemma sum_flip (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (flip t)) = ∑ t, weight w t * f t := by
  simpa only [flipEquiv, Equiv.coe_fn_mk, weight_flip] using
    flipEquiv.sum_comp (fun t ↦ weight w t * f t)

abbrev CornerPairs (G : SimpleGraph V) :=
  {p : EdgeState G × EdgeState G // p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst}

def cornerEquiv : TriangleState G ≃ CornerPairs G where
  toFun t := ⟨(t.edge12, t.edge13), rfl, t.adj23⟩
  invFun p := ⟨(p.val.1.src, p.val.1.dst, p.val.2.dst), p.val.1.adj,
    by rw [p.property.1]; exact p.val.2.adj, p.property.2⟩
  left_inv t := by cases t; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext p.property.1 rfl

lemma corner_sum (w : V → ℝ) (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.edge12 t.edge13) =
      ∑ e : EdgeState G, ∑ z : EdgeState G,
        if e.src = z.src ∧ G.Adj e.dst z.dst
          then w e.src * w e.dst * w z.dst * f e z else 0 := by
  classical
  calc
    _ = ∑ p : CornerPairs G, w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2 :=
      (cornerEquiv.sum_comp (fun p ↦ w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2))
    _ = ∑ p : EdgeState G × EdgeState G,
        if p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst
          then w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2 else 0 := by
      rw [← Finset.sum_subtype (univ.filter fun p : EdgeState G × EdgeState G ↦
          p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst) (by simp)
        (fun p ↦ w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2), sum_filter]
    _ = _ := Fintype.sum_prod_type _

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
lemma sum_edge_permutations (w : V → ℝ) (g : EdgeState G → ℝ) :
    (∑ t, weight w t * g t.edge12.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23.rev) = (∑ t, weight w t * g t.edge12) := by
  refine ⟨sum_swap w (fun t ↦ g t.edge12), sum_flip w (fun t ↦ g t.edge12), ?_,
    sum_rotate w (fun t ↦ g t.edge12), ?_⟩
  · exact (sum_rotate w (fun t ↦ g (rotate t).edge12)).trans (sum_rotate w (fun t ↦ g t.edge12))
  · exact (sum_rotate w (fun t ↦ g (swap t).edge12)).trans (sum_swap w (fun t ↦ g t.edge12))
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Projection =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere2 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

/-- A weight-preserving, directed-edge-injective projection. -/
structure EdgeProjection (H : SimpleGraph U) (G : SimpleGraph V) (π : U → V) : Prop where
  map_adj : ∀ a b, H.Adj a b → G.Adj (π a) (π b)
  inj : ∀ a b c d, H.Adj a b → H.Adj c d → π a = π c → π b = π d → a = c ∧ b = d

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

def edgeMap (h : EdgeProjection H G π) (e : EdgeState H) : EdgeState G :=
  ⟨(π e.src, π e.dst), h.map_adj _ _ e.adj⟩

omit [Fintype V] [Fintype U] in
lemma edgeMap_injective (h : EdgeProjection H G π) : Function.Injective h.edgeMap := by
  intro e f hef
  have heq := congrArg Subtype.val hef
  have hpair := h.inj e.src e.dst f.src f.dst e.adj f.adj
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  exact Subtype.ext (Prod.ext hpair.1 hpair.2)

omit [Fintype V] [Fintype U] in
lemma mass_image_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset U) :
    mass w (A.image π) ≤ mass (w ∘ π) A := by
  classical
  exact sum_image_le_of_nonneg (fun _ _ ↦ hw _)

lemma crossMass_edge_sum (H : SimpleGraph U) (w : U → ℝ) (A B : Finset U) :
    crossMass H w A B =
      ∑ e : EdgeState H, if e.src ∈ A ∧ e.dst ∈ B then w e.src * w e.dst else 0 := by
  classical
  rw [EdgeState.sum_eq (fun a b ↦ if a ∈ A ∧ b ∈ B then w a * w b else 0)]
  have heq : (∑ a, ∑ b ∈ neighbors H a, if a ∈ A ∧ b ∈ B then w a * w b else 0) =
      ∑ a, if a ∈ A then (∑ b, if b ∈ B then if H.Adj a b then w a * w b else 0 else 0) else 0 := by
    apply sum_congr rfl
    intro a _
    by_cases ha : a ∈ A
    · simp only [ha, true_and, ↓reduceIte, neighbors, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases hb : b ∈ B <;> simp [hb]
    · simp [ha]
  rw [heq]
  simp [crossMass]

lemma crossMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset U) :
    crossMass H (w ∘ π) A B ≤ crossMass G w (A.image π) (B.image π) := by
  classical
  rw [crossMass_edge_sum, crossMass_edge_sum]
  calc
    _ ≤ ∑ e : EdgeState H,
        if (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π
          then w (h.edgeMap e).src * w (h.edgeMap e).dst else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : e.src ∈ A ∧ e.dst ∈ B
      · have hi : (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π :=
          ⟨mem_image.2 ⟨e.src, he.1, rfl⟩, mem_image.2 ⟨e.dst, he.2, rfl⟩⟩
        simp only [he, hi]
        exact le_rfl
      · simp only [he, ↓reduceIte]
        split_ifs
        · exact mul_nonneg (hw _) (hw _)
        · exact le_rfl
    _ ≤ _ := sum_injective_le h.edgeMap h.edgeMap_injective
      (fun e ↦ if e.src ∈ A.image π ∧ e.dst ∈ B.image π then w e.src * w e.dst else 0)
      (fun e ↦ by split_ifs; exact mul_nonneg (hw _) (hw _); exact le_rfl)

lemma crossBound (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {C : ℝ} (hC : 0 ≤ C) (hc : CrossBound G w C) : CrossBound H (w ∘ π) C := by
  classical
  intro x hx A B hA hB
  have hAi := mass_image_le (π := π) hw A
  have hBi := mass_image_le (π := π) hw B
  exact (h.crossMass_le hw A B).trans ((hc x hx _ _ (hAi.trans hA) (hBi.trans hB)).trans
    (mul_le_mul_of_nonneg_left (growth_mono hx (mass_nonneg hw _) (mass_nonneg (fun u ↦ hw (π u)) _) hAi) hC))

lemma edgeMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    edgeMass H (w ∘ π) ≤ edgeMass G w := by
  classical
  have hsum : (∑ e : EdgeState H, w (π e.src) * w (π e.dst)) ≤
      ∑ e : EdgeState G, w e.src * w e.dst :=
    sum_injective_le h.edgeMap h.edgeMap_injective (fun e ↦ w e.src * w e.dst)
      (fun e ↦ mul_nonneg (hw _) (hw _))
  unfold edgeMass
  rw [crossMass_edge_sum, crossMass_edge_sum]
  simpa only [mem_univ, true_and, ↓reduceIte, Function.comp_apply] using
    div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

omit [Fintype V] in
lemma neighbor_injective (h : EdgeProjection H G π) (a : U) :
    Set.InjOn π (neighbors H a) := by
  intro b hb c hc heq
  exact (h.inj a b a c ((mem_neighbors _ _ _).1 hb) ((mem_neighbors _ _ _).1 hc) rfl heq).2

lemma neighborhood_image (h : EdgeProjection H G π) (a : U) :
    (neighbors H a).image π ⊆ neighbors G (π a) := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hb
  exact (mem_neighbors _ _ _).2 (h.map_adj _ _ ((mem_neighbors _ _ _).1 hc))

lemma neighborMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (a : U) :
    neighborMass H (w ∘ π) a ≤ neighborMass G w (π a) := by
  classical
  calc
    _ = mass w ((neighbors H a).image π) := (sum_image (h.neighbor_injective a)).symm
    _ ≤ _ := mass_mono hw (h.neighborhood_image a)

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Splitting =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere3 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

namespace Splitting
variable {G : SimpleGraph V}

noncomputable def graph (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) : SimpleGraph (EdgeState G) where
  Adj a b := ∃ e, good e ∧ good e.rev ∧ F e = a ∧ F e.rev = b
  symm := ⟨by
    rintro a b ⟨e, he, hr, ha, hb⟩
    exact ⟨e.rev, hr, by simpa using he, hb, by simpa using ha⟩⟩
  loopless := ⟨by
    rintro a ⟨e, he, hr, ha, hb⟩
    have heq : e.src = e.dst := by
      calc
        e.src = (F e).src := (hF e).symm
        _ = (F e.rev).src := congrArg EdgeState.src (ha.trans hb.symm)
        _ = e.dst := hF e.rev
    exact e.adj.ne heq⟩

omit [Fintype V] in
lemma projection (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) :
    EdgeProjection (graph F hF good) G EdgeState.src := by
  have endpoints {a b : EdgeState G} {e : EdgeState G} (ha : F e = a) (hb : F e.rev = b) :
      a.src = e.src ∧ b.src = e.dst :=
    ⟨by rw [← ha, hF], by rw [← hb, hF]; rfl⟩
  constructor
  · rintro a b ⟨e, _, _, ha, hb⟩
    obtain ⟨hs, ht⟩ := endpoints ha hb
    rw [hs, ht]
    exact e.adj
  · rintro a b c d ⟨e, _, _, ha, hb⟩ ⟨f, _, _, hc, hd⟩ hac hbd
    obtain ⟨he1, he2⟩ := endpoints ha hb
    obtain ⟨hf1, hf2⟩ := endpoints hc hd
    have hef : e = f := Subtype.ext (Prod.ext (he1.symm.trans (hac.trans hf1))
      (he2.symm.trans (hbd.trans hf2)))
    subst f
    exact ⟨ha.symm.trans hc, hb.symm.trans hd⟩

lemma neighborMass_le (w : V → ℝ) (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop)
    (K : EdgeState G → EdgeState G → ℝ) (hK0 : ∀ a e, 0 ≤ K a e)
    (hK1 : ∀ a, ∑ e, K a e = 1) {L : ℝ} (hL : 0 ≤ L)
    (hadm : ∀ e, good e → w e.dst ≤ L * K (F e) e) (a : EdgeState G) :
    neighborMass (graph F hF good) (w ∘ EdgeState.src) a ≤ L := by
  classical
  let H := graph F hF good
  let N := ↑(neighbors H a)
  have hproj := projection F hF good
  let f : N → EdgeState G := fun b ↦
    ⟨(a.src, b.val.src), hproj.map_adj _ _ ((mem_neighbors _ _ _).1 b.property)⟩
  have hf : Function.Injective f := by
    intro b c heq
    apply Subtype.ext
    apply hproj.neighbor_injective a b.property c.property
    exact congrArg (fun e : EdgeState G ↦ e.dst) heq
  have hle (b : N) : w b.val.src ≤ L * K a (f b) := by
    obtain ⟨e, he, _, ha, hb⟩ := (mem_neighbors H a b.val).1 b.property
    have hef : f b = e := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg EdgeState.src ha).symm.trans (hF e)
      · exact (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    rw [hef, ← ha]
    have hd : b.val.src = e.dst := (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    simpa only [hd] using hadm e he
  calc
    _ = ∑ b : N, w b.val.src := (sum_coe_sort (neighbors H a) (fun b ↦ w b.src)).symm
    _ ≤ ∑ b : N, L * K a (f b) := sum_le_sum (fun b _ ↦ hle b)
    _ = L * ∑ b : N, K a (f b) := (mul_sum _ _ _).symm
    _ ≤ L * ∑ e, K a e := mul_le_mul_of_nonneg_left (sum_injective_le f hf (K a) (hK0 a)) hL
    _ = L := by rw [hK1, mul_one]

/-- All three corner agreements and all six admissible incidences. -/
def Survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) : Prop :=
  F t.edge12 = F t.edge13 ∧
  F t.edge12.rev = F t.edge23 ∧
  F t.edge13.rev = F t.edge23.rev ∧
  good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
  good t.edge23 ∧ good t.edge23.rev

lemma triangleMass_surviving_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (hF : ∀ e, (F e).src = e.src)
    (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) ≤
      6 * triangleMass (graph F hF good) (w ∘ EdgeState.src) := by
  classical
  let H := graph F hF good
  let S := {t : TriangleState G // Survives F good t}
  let f : S → TriangleState H := fun t ↦
    ⟨(F t.val.edge12, F t.val.edge12.rev, F t.val.edge13.rev),
      ⟨t.val.edge12, t.property.2.2.2.1, t.property.2.2.2.2.1, rfl, rfl⟩,
      ⟨t.val.edge13, t.property.2.2.2.2.2.1, t.property.2.2.2.2.2.2.1, t.property.1.symm, rfl⟩,
      ⟨t.val.edge23, t.property.2.2.2.2.2.2.2.1, t.property.2.2.2.2.2.2.2.2,
        t.property.2.1.symm, t.property.2.2.1.symm⟩⟩
  have coords (t : S) :
      (f t).first.src = t.val.first ∧ (f t).second.src = t.val.second ∧
        (f t).third.src = t.val.third := by
    change (F t.val.edge12).src = _ ∧ (F t.val.edge12.rev).src = _ ∧ (F t.val.edge13.rev).src = _
    simp only [hF]
    exact ⟨rfl, rfl, rfl⟩
  have hf : Function.Injective f := by
    intro t s hts
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (coords t).1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.first.src) hts).trans (coords s).1)
    · apply Prod.ext
      · exact (coords t).2.1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.second.src) hts).trans (coords s).2.1)
      · exact (coords t).2.2.symm.trans ((congrArg (fun a : TriangleState H ↦ a.third.src) hts).trans (coords s).2.2)
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight (w ∘ EdgeState.src) (f t) := by
      apply sum_congr rfl
      intro t _
      simp only [TriangleState.weight, Function.comp_apply, (coords t).1, (coords t).2.1, (coords t).2.2]
    _ ≤ ∑ t : TriangleState H, TriangleState.weight (w ∘ EdgeState.src) t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Reach =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere4 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

/-- Whole-graph sets that contain most of the walk. -/
noncomputable def enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) : Finset V :=
  A ∪ univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))

noncomputable def reach (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (v : V) : ℕ → Finset V
  | 0 => neighbors G v
  | n+1 => enlarge G w t (reach G w t v n)

lemma subset_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) :
    A ⊆ enlarge G w t A := subset_union_left

lemma not_mem_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V)
    {y : V} (hy : y ∉ enlarge G w t A) :
    y ∉ A ∧ mass w (A ∩ neighbors G y) < t := by
  simpa [enlarge, not_or, not_le] using hy

lemma enlarge_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t) (A : Finset V) :
    mass w (enlarge G w t A) ≤ (1 + L / t) * mass w A := by
  let B := univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))
  have hm : t * mass w B ≤ L * mass w A := by
    calc
      _ = ∑ y ∈ B, w y * t := by rw [← sum_mul]; exact mul_comm _ _
      _ ≤ ∑ y ∈ B, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (mem_filter.1 hy).2 (hw y)
      _ ≤ ∑ y, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_univ_sum_of_nonneg (fun y ↦ mul_nonneg (hw y) (mass_nonneg hw _))
      _ = crossMass G w univ A := (crossMass_factor G w univ A).symm
      _ = ∑ y ∈ A, w y * neighborMass G w y := crossMass_all_left G w A
      _ ≤ ∑ y ∈ A, w y * L := sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hL y) (hw y)
      _ = L * mass w A := by rw [← sum_mul]; exact mul_comm _ _
  have hB : mass w B ≤ L / t * mass w A := by
    calc
      _ ≤ L * mass w A / t := (le_div_iff₀ ht).2 (by nlinarith)
      _ = _ := by ring
  have hu := mass_union_le hw A B
  change mass w (A ∪ B) ≤ _
  nlinarith

lemma reach_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL0 : 0 ≤ L) (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t)
    (v : V) (n : ℕ) : mass w (reach G w t v n) ≤ (1 + L / t) ^ n * neighborMass G w v := by
  have hfac : 0 ≤ 1 + L / t := by positivity
  induction n with
  | zero => simp [reach, neighborMass]
  | succ n ih =>
    exact (enlarge_mass G hw hL ht _).trans (by
      have h := mul_le_mul_of_nonneg_left ih hfac
      simpa only [pow_succ', mul_assoc] using h)

lemma reach_mass_exp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x : ℝ} (hx : 32 ≤ x) (hL : ∀ v, neighborMass G w v ≤ Real.exp x)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    mass w (reach G w (Numerical.threshold x) v n) ≤ Real.exp (20 * x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ht := Numerical.threshold_pos hx0
  have hfac : 0 ≤ 1 + Real.exp x / Numerical.threshold x := by positivity
  have hfacn := pow_le_pow_left₀ hfac (Numerical.growth_factor_le hx) n
  calc
    _ ≤ (1 + Real.exp x / Numerical.threshold x) ^ n * neighborMass G w v :=
      reach_mass G hw (Real.exp_pos x).le hL ht v n
    _ ≤ Real.exp (4 * x) ^ n * Real.exp x :=
      mul_le_mul hfacn (hL v) (neighborMass_nonneg G hw v) (by positivity)
    _ = Real.exp ((n : ℝ) * (4 * x) + x) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

lemma growth_le_of_lower {x Y s : ℝ} (hx : 1 ≤ x) (hs : 1 / x ≤ s) :
    growth Y s ≤ s * (Y + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := (one_div_pos.2 hx0).trans_le hs
  have hrec : 1 / s ≤ x := by
    apply (div_le_iff₀ hs0).2
    have h := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hl := Real.log_le_log (one_div_pos.2 hs0) hrec
  have hm : max 0 (Real.log (1 / s)) ≤ Real.log x := max_le (Real.log_nonneg hx) hl
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) hs0.le

noncomputable def badSet (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : Finset V :=
  (neighbors G v).filter (fun u ↦ b < mass w (S v ∩ neighbors G u))

lemma badSet_subset (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : badSet G w S b v ⊆ neighbors G v := filter_subset _ _

lemma badSet_mass_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C Y : ℝ} (hCross : CrossBound G w C) (hY : 1 ≤ Y)
    (S : V → Finset V) (b : ℝ) (v : V)
    (hv : neighborMass G w v ≤ Real.exp Y) (hS : mass w (S v) ≤ Real.exp Y) :
    b * mass w (badSet G w S b v) ≤ C * growth Y (neighborMass G w v) := by
  calc
    _ = ∑ u ∈ badSet G w S b v, w u * b := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ ∑ u ∈ badSet G w S b v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum fun u hu ↦ mul_le_mul_of_nonneg_left ((mem_filter.1 hu).2.le) (hw u)
    _ ≤ ∑ u ∈ neighbors G v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum_of_subset_of_nonneg (badSet_subset G w S b v)
        (fun u _ _ ↦ mul_nonneg (hw u) (mass_nonneg hw _))
    _ = crossMass G w (neighbors G v) (S v) := (crossMass_factor _ _ _ _).symm
    _ ≤ _ := hCross Y hY _ _ hv hS

lemma conditional_bad_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x k : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hk : 0 ≤ k)
    (hCross : CrossBound G w C) (v : V) (B : Finset V) (hB : B ⊆ neighbors G v)
    (hs : 1 / x ≤ neighborMass G w v) (hL : neighborMass G w v ≤ Real.exp x)
    (hh : neighborMass G w v / x ≤ triangleAt G w v)
    (hb : mass w B ≤ k * neighborMass G w v) :
    crossMass G w B (neighbors G v) ≤
      (2 * C * x ^ 2 * (k + x * Real.exp (-x))) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  have hxsv : 1 ≤ x * neighborMass G w v := by
    have := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hhh : neighborMass G w v ≤ x * triangleAt G w v := by
    have := (div_le_iff₀ hx0).1 hh
    nlinarith
  have he : Real.exp (-x) ≤ x * Real.exp (-x) * neighborMass G w v := by
    nlinarith [mul_le_mul_of_nonneg_left hxsv (Real.exp_pos (-x)).le]
  have hf : 0 ≤ 2 * C * x := by positivity
  have hf' : 0 ≤ 2 * C * x * (k + x * Real.exp (-x)) := by positivity
  calc
    _ ≤ C * growth x (mass w B) := hCross x hx _ _ ((mass_mono hw hB).trans hL) hL
    _ ≤ C * (2 * x * (mass w B + Real.exp (-x))) :=
      mul_le_mul_of_nonneg_left (growth_le_twice hx (mass_nonneg hw B)) hC
    _ = (2 * C * x) * (mass w B + Real.exp (-x)) := by ring
    _ ≤ (2 * C * x) * (k * neighborMass G w v +
        x * Real.exp (-x) * neighborMass G w v) :=
      mul_le_mul_of_nonneg_left (add_le_add hb he) hf
    _ = (2 * C * x * (k + x * Real.exp (-x))) * neighborMass G w v := by ring
    _ ≤ (2 * C * x * (k + x * Real.exp (-x))) * (x * triangleAt G w v) :=
      mul_le_mul_of_nonneg_left hhh hf'
    _ = _ := by ring

lemma reach_bad_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) {v : V} (hv : (neighbors G v).Nonempty) :
    mass w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v) ≤
      (21 * C / x ^ 6) * neighborMass G w v := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hY : 1 ≤ 20 * x ^ 2 := by nlinarith
  have hxY : x ≤ 20 * x ^ 2 := by nlinarith
  have hs := neighborMass_ge_of_commonMass G hw hc hv
  have hS := reach_mass_exp G hw hx hL hn v
  have hm := badSet_mass_bound G hw hCross hY
    (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v
    ((hL v).trans (Real.exp_le_exp.2 hxY)) hS
  have hg := growth_le_of_lower (Y := 20 * x ^ 2) hx1 hs
  have hlog : Real.log x ≤ x ^ 2 := by
    have := Real.log_le_self hx0.le
    nlinarith
  have hgs : growth (20 * x ^ 2) (neighborMass G w v) ≤
      neighborMass G w v * (21 * x ^ 2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_left _ (neighborMass_nonneg G hw v)
    linarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hgs hC)
  calc
    _ ≤ C * (neighborMass G w v * (21 * x ^ 2)) / x ^ 8 := by
      apply (le_div_iff₀ (pow_pos hx0 8)).2
      nlinarith [hm']
    _ = _ := by field_simp [hx0.ne']

noncomputable def exceptionalConstant (C : ℝ) : ℝ := 42 * C ^ 2 + 2 * C
noncomputable def entropyConstant (C : ℝ) : ℝ := 10 + exceptionalConstant C
noncomputable def smoothingConstant (C : ℝ) : ℝ := 2 * Real.sqrt (entropyConstant C + 1)

lemma exceptionalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ exceptionalConstant C := by
  unfold exceptionalConstant
  positivity

lemma reach_bad_cross (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    crossMass G w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v)
      (neighbors G v) ≤ (exceptionalConstant C / x ^ 4) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  by_cases hv : (neighbors G v).Nonempty
  · have hbad := reach_bad_mass G hw hC hCross hx hL hc hn hv
    have hcond := conditional_bad_bound G hw hC (show 1 ≤ x by linarith)
      (show 0 ≤ 21 * C / x ^ 6 by positivity) hCross v _
      (badSet_subset G w _ _ v) (neighborMass_ge_of_commonMass G hw hc hv) (hL v)
      (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using triangleAt_ge_of_commonMass G hw hc v)
      hbad
    have hnum : 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * Real.exp (-x)) ≤
        exceptionalConstant C / x ^ 4 := by
      calc
        _ ≤ 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * (1 / x ^ 7)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Numerical.exp_neg_le_inv_pow_seven hx) hx0.le)
        _ = _ := by unfold exceptionalConstant; field_simp [hx0.ne']; ring
    exact hcond.trans (mul_le_mul_of_nonneg_right hnum (triangleAt_nonneg G hw v))
  · have he := not_nonempty_iff_eq_empty.1 hv
    simp [badSet, he, crossMass, triangleAt]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.FiniteKernel =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence


namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

abbrev Kernel (I : Type u) := Matrix I I ℝ

local instance : DecidableEq I := Classical.decEq I

def Stochastic (P : Kernel I) : Prop := ∀ i, IsProb (P i)
def Stationary (π : I → ℝ) (P : Kernel I) : Prop := ∀ j, ∑ i, π i * P i j = π j
def Reversible (π : I → ℝ) (P : Kernel I) : Prop := ∀ i j, π i * P i j = π j * P j i

noncomputable def lazy (P : Kernel I) : Kernel I := fun i j ↦
  ((if i = j then 1 else 0) + P i j) / 2

noncomputable def smoothed (P : Kernel I) (j : ℕ) : Kernel I := by
  classical
  exact P * lazy P ^ j

def avgEntropy (π w : I → ℝ) (K : Kernel I) : ℝ := ∑ i, π i * entropy w (K i)

lemma stochastic_one : Stochastic (1 : Kernel I) := by
  classical
  intro i
  constructor
  · intro j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma stochastic_mul {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q) :
    Stochastic (P * Q) := by
  intro i
  exact mix_isProb (hP i) hQ

lemma stochastic_pow {P : Kernel I} (hP : Stochastic P) (n : ℕ) : Stochastic (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (stochastic_one (I := I))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hP

lemma stochastic_lazy {P : Kernel I} (hP : Stochastic P) : Stochastic (lazy P) := by
  classical
  intro i
  constructor
  · intro j
    dsimp [lazy]
    have := (hP i).1 j
    split_ifs <;> positivity
  · change (∑ j, ((if i = j then (1 : ℝ) else 0) + P i j) / 2) = 1
    rw [← sum_div, sum_add_distrib]
    simp [(hP i).2]

lemma stochastic_smoothed {P : Kernel I} (hP : Stochastic P) (j : ℕ) :
    Stochastic (smoothed P j) := stochastic_mul hP (stochastic_pow (stochastic_lazy hP) j)

lemma stationary_of_reversible {π : I → ℝ} {P : Kernel I}
    (hP : Stochastic P) (hr : Reversible π P) : Stationary π P := by
  intro j
  calc
    _ = ∑ i, π j * P j i := sum_congr rfl fun i _ ↦ hr i j
    _ = π j := by rw [← mul_sum, (hP j).2, mul_one]

lemma stationary_lazy {π : I → ℝ} {P : Kernel I} (hP : Stationary π P) :
    Stationary π (lazy P) := by
  classical
  intro j
  change (∑ i, π i * (((if i = j then 1 else 0) + P i j) / 2)) = π j
  simp only [← mul_div_assoc, mul_add, ← sum_div, sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [hP j]
  ring

omit [Fintype I] in
lemma reversible_one (π : I → ℝ) : Reversible π (1 : Kernel I) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [h, Ne.symm h]

lemma reversible_mul {π : I → ℝ} {P Q : Kernel I}
    (hP : Reversible π P) (hQ : Reversible π Q) (hc : Commute P Q) :
    Reversible π (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, mul_sum]
  calc
    _ = ∑ k, π j * (Q j k * P k i) := by
      apply sum_congr rfl
      intro k _
      calc
        _ = (π i * P i k) * Q k j := by ring
        _ = (π k * P k i) * Q k j := by rw [hP]
        _ = (π k * Q k j) * P k i := by ring
        _ = (π j * Q j k) * P k i := by rw [hQ]
        _ = _ := by ring
    _ = π j * (Q * P) j i := by rw [Matrix.mul_apply, mul_sum]
    _ = _ := by rw [hc.eq]

lemma reversible_pow {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (n : ℕ) :
    Reversible π (P ^ n) := by
  classical
  induction n with
  | zero => simpa using reversible_one π
  | succ n ih =>
    rw [pow_succ]
    exact reversible_mul ih hP ((Commute.refl P).pow_left n)

omit [Fintype I] in
lemma reversible_lazy {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) :
    Reversible π (lazy P) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [lazy, h, Ne.symm h, ite_false, zero_add]
    rw [← mul_div_assoc, ← mul_div_assoc, hP i j]

omit [Fintype I] in
lemma lazy_eq (P : Kernel I) : lazy P = (1 / 2 : ℝ) • (1 + P) := by
  classical
  ext i j
  simp [lazy, Matrix.one_apply, div_eq_mul_inv, mul_comm]

lemma commute_lazy (P : Kernel I) : Commute P (lazy P) := by
  classical
  rw [lazy_eq]
  show P * ((1 / 2 : ℝ) • (1 + P)) = ((1 / 2 : ℝ) • (1 + P)) * P
  simp [mul_add, add_mul]

lemma reversible_smoothed {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (j : ℕ) :
    Reversible π (smoothed P j) := by
  classical
  exact reversible_mul hP (reversible_pow (reversible_lazy hP) j)
    ((commute_lazy P).pow_right j)

lemma smoothed_zero (P : Kernel I) : smoothed P 0 = P := by
  classical
  simp [smoothed]

lemma smoothed_succ (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = lazy P * smoothed P j := by
  classical
  unfold smoothed
  rw [pow_succ', ← mul_assoc, (commute_lazy P).eq, mul_assoc]

lemma smoothed_succ_right (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = smoothed P j * lazy P := by
  classical
  simp [smoothed, pow_succ, mul_assoc]

lemma smoothed_density {P : Kernel I} (hP : Stochastic P) {b : I → ℝ}
    (hb : ∀ i j, P i j ≤ b j) (n : ℕ) : ∀ i j, smoothed P n i j ≤ b j := by
  classical
  intro i j
  unfold smoothed
  rw [((commute_lazy P).pow_right n).eq, Matrix.mul_apply]
  have hQ := stochastic_pow (stochastic_lazy hP) n
  calc
    _ ≤ ∑ k, (lazy P ^ n) i k * b j :=
      sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hb k j) ((hQ i).1 k)
    _ = b j := by rw [← sum_mul, (hQ i).2, one_mul]

lemma pair_isProb {π : I → ℝ} (hπ : IsProb π) {Q : Kernel I} (hQ : Stochastic Q) :
    IsProb (fun a : I × I ↦ π a.1 * Q a.1 a.2) := by
  constructor
  · intro a
    exact mul_nonneg (hπ.1 a.1) ((hQ a.1).1 a.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, fun i ↦ (hQ i).2, mul_one]
    exact hπ.2

lemma stationary_average {π : I → ℝ} {Q : Kernel I} (hQ : Stationary π Q) (f : I → ℝ) :
    (∑ i, π i * ∑ j, Q i j * f j) = ∑ j, π j * f j := by
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul]
  exact sum_congr rfl fun j _ ↦ by rw [hQ j]

lemma entropy_increment {π w : I → ℝ} (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    avgEntropy π w (Q * K) - avgEntropy π w K =
      ∑ i, π i * ∑ j, Q i j * divergence (K j) ((Q * K) i) := by
  have he (i : I) := entropy_mix_gap hw (hQ i) hK
  have he' : ∀ i, entropy w ((Q * K) i) - ∑ j, Q i j * entropy w (K j) =
      ∑ j, Q i j * divergence (K j) ((Q * K) i) := he
  simp_rw [← he', mul_sub, sum_sub_distrib]
  rw [stationary_average hs]
  rfl

lemma entropy_increment_nonneg {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    0 ≤ avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  apply sum_nonneg
  intro i _
  apply mul_nonneg (hπ.1 i)
  apply sum_nonneg
  intro j _
  rcases ((hQ i).1 j).eq_or_lt with hj | hj
  · simp [← hj]
  exact mul_nonneg hj.le (divergence_nonneg (hK j) (stochastic_mul hQ hK i)
    (fun k hk ↦ mix_support (hQ i).1 (fun z ↦ (hK z).1) hj hk))

lemma entropy_increment_tv {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    (∑ i, π i * ∑ j, Q i j * tv (K j) ((Q * K) i)) ^ 2 ≤
      avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  have h := average_tv_sq_le_average_divergence (pair_isProb hπ hQ)
    (fun a : I × I ↦ hK a.2) (fun a : I × I ↦ stochastic_mul hQ hK a.1)
    (fun a ha i hi ↦ mix_support (hQ a.1).1 (fun j ↦ (hK j).1)
      (pos_of_mul_pos_right ha (hπ.1 a.1)) hi)
  simpa only [Fintype.sum_prod_type, mul_assoc, ← mul_sum] using h

lemma lazy_triangle_tv {π : I → ℝ} (hπ : IsProb π) {P K : Kernel I}
    (hP : Stochastic P) :
    (∑ i, π i * ∑ j, P i j * tv (K i) (K j)) ≤
      2 * (∑ i, π i * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) := by
  classical
  have hi (i : I) : (∑ j, P i j * tv (K i) (K j)) ≤
      2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i) := by
    calc
      _ ≤ ∑ j, P i j * (tv (K i) ((lazy P * K) i) + tv (K j) ((lazy P * K) i)) := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ ((hP i).1 j)
        have := tv_triangle (K i) ((lazy P * K) i) (K j)
        simpa only [tv_comm ((lazy P * K) i)] using this
      _ = _ := by
        have he (f : I → ℝ) : (∑ j, lazy P i j * f j) =
            (f i + ∑ j, P i j * f j) / 2 := by
          simp only [lazy, div_mul_eq_mul_div, add_mul, ← sum_div, sum_add_distrib,
            ite_mul, one_mul, zero_mul]
          simp
        rw [he]
        simp only [mul_add, sum_add_distrib, ← sum_mul, (hP i).2, one_mul]
        ring
  calc
    _ ≤ ∑ i, π i * (2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hi i) (hπ.1 i)
    _ = _ := by simp_rw [← mul_assoc, mul_comm (π _ ) 2, mul_assoc, ← mul_sum]

lemma smoothed_entropy_mono {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) :
    Monotone (fun j ↦ avgEntropy π w (smoothed P j)) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [smoothed_succ]
  exact sub_nonneg.1 (entropy_increment_nonneg hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs))

lemma smoothed_row_distance_sq {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) (j : ℕ) :
    (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) := by
  have h := entropy_increment_tv hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs)
  have hc := lazy_triangle_tv (K := smoothed P j) hπ hP
  have ha : 0 ≤ ∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((hP i).1 z) (tv_nonneg _ _))
  have hb : 0 ≤ ∑ i, π i * ∑ z, lazy P i z * tv (smoothed P j z)
      ((lazy P * smoothed P j) i) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((stochastic_lazy hP i).1 z) (tv_nonneg _ _))
  rw [smoothed_succ]
  have hp := mul_nonneg (sub_nonneg.2 hc) (add_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hb) ha)
  nlinarith

/-- Entropy telescoping gives the averaged triangle-row estimate. -/
lemma exists_smoothed_row_distance {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P)
    {R : ℕ} (hR : 0 < R) {D : ℝ}
    (hD : avgEntropy π w (smoothed P R) - avgEntropy π w (smoothed P 0) ≤ D) :
    ∃ j < R, (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * D / R := by
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  have hsum : (∑ j ∈ range R, (avgEntropy π w (smoothed P (j + 1)) -
      avgEntropy π w (smoothed P j))) ≤ ∑ _j ∈ range R, D / (R : ℝ) := by
    rw [sum_range_sub (fun j ↦ avgEntropy π w (smoothed P j)) R]
    have he : (∑ _j ∈ range R, D / (R : ℝ)) = D := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [he]
    exact hD
  obtain ⟨j, hj, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.2 (Nat.ne_of_gt hR)) hsum
  refine ⟨j, mem_range.1 hj, ?_⟩
  calc
    _ ≤ 4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) :=
      smoothed_row_distance_sq hπ hw hP hs j
    _ ≤ 4 * (D / (R : ℝ)) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by ring

variable {J : Type v}

def Preserves (label : I → J) (P : Kernel I) : Prop :=
  ∀ i j, label i ≠ label j → P i j = 0

omit [Fintype I] in
lemma preserves_one (label : I → J) : Preserves label (1 : Kernel I) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [h]

lemma preserves_mul {label : I → J} {P Q : Kernel I}
    (hP : Preserves label P) (hQ : Preserves label Q) : Preserves label (P * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : label i = label k
  · have hkj : label k ≠ label j := fun h ↦ hij (hik.trans h)
    rw [hQ k j hkj, mul_zero]
  · rw [hP i k hik, zero_mul]

lemma preserves_pow {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (P ^ n) := by
  induction n with
  | zero => simpa using preserves_one label
  | succ n ih => simpa only [pow_succ] using preserves_mul ih hP

omit [Fintype I] in
lemma preserves_lazy {label : I → J} {P : Kernel I} (hP : Preserves label P) :
    Preserves label (lazy P) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [lazy, h, hP i j hij]

lemma preserves_smoothed {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (smoothed P n) :=
  preserves_mul hP (preserves_pow (preserves_lazy hP) n)

def rowMass (K : Kernel I) (i : I) (A : Finset I) : ℝ := ∑ j ∈ A, K i j

lemma rowMass_le_one {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i A ≤ 1 := by
  rw [← (hK i).2]
  exact sum_le_univ_sum_of_nonneg (hK i).1

lemma rowMass_mul (P Q : Kernel I) (i : I) (A : Finset I) :
    rowMass (P * Q) i A = ∑ j, P i j * rowMass Q j A := by
  unfold rowMass
  simp only [Matrix.mul_apply, mul_sum]
  rw [sum_comm]

lemma rowMass_compl {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i Aᶜ = 1 - rowMass K i A := by
  have h : rowMass K i A + rowMass K i Aᶜ = 1 := by
    rw [rowMass, rowMass, sum_add_sum_compl, (hK i).2]
  linarith

lemma leakage_mul_le {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q)
    (i : I) (A B : Finset I) :
    rowMass (P * Q) i Bᶜ ≤ rowMass P i Aᶜ + ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
  rw [rowMass_mul]
  have hsplit : (∑ j, P i j * rowMass Q j Bᶜ) =
      (∑ j ∈ A, P i j * rowMass Q j Bᶜ) + ∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ :=
    (sum_add_sum_compl A _).symm
  rw [hsplit]
  have hle : (∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ) ≤ rowMass P i Aᶜ := by
    exact sum_le_sum fun j _ ↦ by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (rowMass_le_one hQ j Bᶜ) ((hP i).1 j)
  have he : (∑ j ∈ A, P i j * rowMass Q j Bᶜ) = ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
    simp only [rowMass, mul_sum]
    rw [sum_comm]
  rw [he]
  linarith

lemma reversed_entropy_tail {μ w : I → ℝ} {K : Matrix I I ℝ}
    (hμ : IsProb μ) (hw : ∀ i, 0 < w i) (hK : Stochastic K)
    (hr : Reversible μ K) {x a : ℝ} (hx : 0 < x)
    (hd : ∀ i j, K i j ≤ x * w j) :
    (a + Real.log x) *
        (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) ≤
      avgEntropy μ w K + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    mul_le_mul_of_nonneg_left (entropy_tail (a := a) (hK i) hw hx (hd i)) (hμ.1 i)
  have heq : (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) =
      ∑ i, μ i * ∑ j, if K i j < w j * Real.exp (-a) then K i j else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases hb : K i j < w j * Real.exp (-a)
    · simp only [hb, ↓reduceIte]
      exact hr j i
    · simp only [hb, ↓reduceIte, mul_zero]
  rw [heq]
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hμ.2, one_mul,
    avgEntropy, mul_left_comm] using h

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.LocalWalk =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere5 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

/-- The disjoint union of the neighborhood transition kernels. -/
noncomputable def transition : Kernel (EdgeState G) := fun e f ↦
  if e.src = f.src then
    if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0
  else 0

noncomputable def normalizer : ℝ :=
  ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst

noncomputable def law : EdgeState G → ℝ := fun e ↦
  (w e.src * w e.dst * commonMass G w e.src e.dst) / normalizer G w

noncomputable def vertexWeight : EdgeState G → ℝ := fun e ↦ w e.dst

noncomputable def fiber (u : V) : Finset (EdgeState G) := by
  classical
  exact univ.filter (fun e ↦ e.src = u)

@[simp] lemma mem_fiber (e : EdgeState G) (u : V) : e ∈ fiber G u ↔ e.src = u := by
  classical
  simp [fiber]

lemma fiber_mass (u : V) : (∑ e ∈ fiber G u, vertexWeight G w e) = neighborMass G w u := by
  classical
  simp only [fiber, sum_filter, vertexWeight, EdgeState.sum_fiber, neighborMass, mass]

lemma normalizer_eq : normalizer G w = 6 * triangleMass G w := by
  rw [normalizer, EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v),
    triangleMass_eq_sum]
  simp only [triangleAt, mul_sum, mul_assoc]

variable {G w}
lemma transition_stochastic (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : Stochastic (transition G w) := by
  classical
  intro e
  constructor
  · intro f
    dsimp [transition]
    split_ifs
    · exact (div_pos (hw _) (hc _ _ e.adj)).le
    all_goals exact le_rfl
  · change (∑ f : EdgeState G, if e.src = f.src then
        (if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0) else 0) = 1
    rw [EdgeState.sum_fiber' e.src (fun z ↦
      if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0)]
    have hid (z : V) : (if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0) =
        (if G.Adj e.dst z then w z else 0) / commonMass G w e.src e.dst := by
      split_ifs <;> simp
    simp_rw [hid]
    rw [← sum_div, ← commonMass_eq_sum, div_self (hc _ _ e.adj).ne']

lemma normalizer_pos [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : 0 < normalizer G w := by
  exact sum_pos (fun e _ ↦ mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) univ_nonempty

lemma law_isProb [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : IsProb (law G w) := by
  have hZ := normalizer_pos hw hc
  constructor
  · intro e
    exact (div_pos (mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) hZ).le
  · unfold law
    rw [← sum_div]
    exact div_self hZ.ne'

lemma transition_reversible [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) :
    Reversible (law G w) (transition G w) := by
  classical
  intro e f
  by_cases hsrc : e.src = f.src
  · by_cases hadj : G.Adj e.dst f.dst
    · simp only [transition, hsrc, ite_true, hadj, hadj.symm, law]
      have he := (hc _ _ e.adj).ne'
      have hf := (hc _ _ f.adj).ne'
      rw [hsrc] at he
      field_simp [he, hf, (normalizer_pos hw hc).ne']
    · simp [transition, hsrc, hadj, G.adj_comm f.dst]
  · simp [transition, hsrc, Ne.symm hsrc]

lemma transition_fixed_src (e f : EdgeState G) (h : e.src ≠ f.src) :
    transition G w e f = 0 := by simp [transition, h]

lemma transition_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) :
    ∀ e f, transition G w e f ≤ x * vertexWeight G w f := by
  classical
  intro e f
  have hc0 : 0 < commonMass G w e.src e.dst := (one_div_pos.2 hx).trans_le (hc _ _ e.adj)
  dsimp [transition, vertexWeight]
  split_ifs
  · apply (div_le_iff₀ hc0).2
    have h := (div_le_iff₀ hx).1 (hc _ _ e.adj)
    nlinarith [mul_le_mul_of_nonneg_left h (hw f.dst).le]
  all_goals exact (mul_pos hx (hw _)).le

lemma smoothed_fixed_src (n : ℕ) (e f : EdgeState G) (h : e.src ≠ f.src) :
    smoothed (transition G w) n e f = 0 :=
  preserves_smoothed (label := EdgeState.src) transition_fixed_src n e f h

lemma smoothed_supported (n : ℕ) (e f : EdgeState G) (h : f ∉ fiber G e.src) :
    smoothed (transition G w) n e f = 0 := by
  apply smoothed_fixed_src
  intro he
  apply h
  exact (mem_fiber G f e.src).2 he.symm

lemma smoothed_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) (n : ℕ) :
    ∀ e f, smoothed (transition G w) n e f ≤ x * vertexWeight G w f := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  exact FiniteKernel.smoothed_density (transition_stochastic hw hc0) (transition_density hw hx hc) n

lemma entropy_bounds [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) (e : EdgeState G) :
    -Real.log x ≤ entropy (vertexWeight G w) (smoothed (transition G w) n e) ∧
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤ x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hp := stochastic_smoothed (transition_stochastic hw hc0) n e
  constructor
  · exact entropy_ge_neg_log_of_density (w := vertexWeight G w) (fun f ↦ hw f.dst) hp hx
      (smoothed_density hw hx hc n e)
  · have h := entropy_supported_le_log (w := vertexWeight G w) (fiber G e.src) (fun f _ ↦ hw f.dst) hp
      (smoothed_supported n e) (Real.exp_pos x) (by rw [fiber_mass]; exact hL e.src)
    simpa only [Real.log_exp] using h

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.WalkEntropy =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere6 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}

noncomputable def liftSet (u : V) (A : Finset V) : Finset (EdgeState G) :=
  univ.filter (fun e ↦ e.src = u ∧ e.dst ∈ A)

@[simp] lemma mem_liftSet (u : V) (A : Finset V) (e : EdgeState G) :
    e ∈ liftSet (G := G) u A ↔ e.src = u ∧ e.dst ∈ A := by simp [liftSet]

lemma liftSet_subset_fiber (u : V) (A : Finset V) : liftSet (G := G) u A ⊆ fiber G u := by
  intro e he
  exact (mem_fiber G e u).2 ((mem_liftSet u A e).1 he).1

lemma sum_liftSet (u : V) (A : Finset V) (f : V → ℝ) :
    (∑ e ∈ liftSet (G := G) u A, f e.dst) = ∑ v ∈ A ∩ neighbors G u, f v := by
  rw [liftSet, sum_filter]
  have he : (∑ e : EdgeState G, if e.src = u ∧ e.dst ∈ A then f e.dst else 0) =
      ∑ e : EdgeState G, if e.src = u then (if e.dst ∈ A then f e.dst else 0) else 0 := by
    apply sum_congr rfl
    intro e _
    by_cases hs : e.src = u <;> by_cases hd : e.dst ∈ A <;> simp [hs, hd]
  rw [he, EdgeState.sum_fiber u (fun v ↦ if v ∈ A then f v else 0), ← sum_filter]
  congr 1
  ext v
  simp [and_comm]

lemma lazy_neighbor_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (e f : EdgeState G) (h : e.dst ≠ f.dst) :
    lazy (transition G w) e f ≤ if G.Adj e.dst f.dst then x * w f.dst else 0 := by
  have hef : e ≠ f := fun he ↦ h (congrArg EdgeState.dst he)
  simp only [lazy, hef, ite_false, zero_add]
  have hp := transition_density hw hx hc e f
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hn := (transition_stochastic hw hc0 e).1 f
  by_cases hadj : G.Adj e.dst f.dst
  · rw [if_pos hadj]
    change transition G w e f ≤ x * w f.dst at hp
    linarith
  · simp [transition, hadj]

lemma liftSet_adj_mass_le (hw : ∀ u, 0 ≤ w u) (u y : V) (A : Finset V) :
    (∑ z ∈ liftSet (G := G) u A, if G.Adj z.dst y then w z.dst else 0) ≤
      mass w (A ∩ neighbors G y) := by
  rw [sum_liftSet u A (fun z ↦ if G.Adj z y then w z else 0), ← sum_filter]
  have he : (A ∩ neighbors G u).filter (fun z ↦ G.Adj z y) =
      (A ∩ neighbors G y) ∩ neighbors G u := by
    ext z
    simp [G.adj_comm z y, and_assoc, and_comm]
  rw [he]
  exact mass_mono hw inter_subset_left

lemma incoming_good_le (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) (A : Finset V) :
    (∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
      ∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
      x ^ 2 * t * neighborMass G w e.src := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hQ := stochastic_lazy hP
  have hpt := preserves_lazy (label := EdgeState.src) (transition_fixed_src (G := G) (w := w))
  have hrow (y : EdgeState G) (hy : y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ) :
      (∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
    by_cases hsrc : y.src = e.src
    · rw [if_pos hsrc]
      have hyout : y.dst ∉ enlarge G w t A := by
        intro h
        exact (mem_compl.1 hy) ((mem_liftSet _ _ _).2 ⟨hsrc, h⟩)
      have hymass := (not_mem_enlarge G w t A hyout).2.le
      calc
        _ ≤ ∑ z ∈ liftSet (G := G) e.src A,
            (if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) := by
          apply sum_le_sum
          intro z hz
          have hzA := ((mem_liftSet _ _ _).1 hz).2
          have hzy : z.dst ≠ y.dst := by
            intro h
            apply hyout
            exact subset_enlarge G w t A (h ▸ hzA)
          have h1 := smoothed_density hw hx hc n e z
          have h2 := lazy_neighbor_density hw hx hc z y hzy
          change smoothed (transition G w) n e z ≤ x * w z.dst at h1
          have hm := mul_le_mul h1 h2 ((hQ z).1 y) (mul_pos hx (hw z.dst)).le
          by_cases hadj : G.Adj z.dst y.dst
          · simpa only [if_pos hadj] using hm.trans_eq (by rw [if_pos hadj]; ring)
          · simpa only [if_neg hadj, mul_zero, zero_mul] using hm
        _ = (∑ z ∈ liftSet (G := G) e.src A,
            if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) :=
          (sum_mul _ _ _).symm
        _ ≤ mass w (A ∩ neighbors G y.dst) * (x ^ 2 * w y.dst) :=
          mul_le_mul_of_nonneg_right (liftSet_adj_mass_le (fun u ↦ (hw u).le) _ _ _)
            (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ ≤ t * (x ^ 2 * w y.dst) := mul_le_mul_of_nonneg_right hymass
          (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ = _ := by ring
    · rw [if_neg hsrc]
      apply le_of_eq
      apply sum_eq_zero
      intro z hz
      have hzs := ((mem_liftSet _ _ _).1 hz).1
      rw [hpt z y (fun h ↦ hsrc (h.symm.trans hzs)), mul_zero]
  calc
    _ ≤ ∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := sum_le_sum hrow
    _ ≤ ∑ y : EdgeState G, if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
      apply sum_le_univ_sum_of_nonneg
      intro y
      split_ifs
      · exact mul_nonneg (mul_nonneg (sq_nonneg x) ht) (hw _).le
      · exact le_rfl
    _ = _ := by
      rw [EdgeState.sum_fiber e.src (fun y ↦ x ^ 2 * t * w y), ← mul_sum]
      rfl

lemma reach_leakage (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 ≤ t)
    (n : ℕ) (e : EdgeState G) :
    rowMass (smoothed (transition G w) n) e
      (liftSet (G := G) e.src (reach G w t e.dst n))ᶜ ≤ n * (x ^ 2 * t * L) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  induction n with
  | zero =>
    simp only [smoothed_zero, Nat.cast_zero, zero_mul, reach]
    apply le_of_eq
    apply sum_eq_zero
    intro f hf
    have hf' := mem_compl.1 hf
    by_cases hs : e.src = f.src
    · have ha : ¬G.Adj e.dst f.dst := by
        intro h
        exact hf' ((mem_liftSet _ _ _).2 ⟨hs.symm, (mem_neighbors G _ _).2 h⟩)
      simp [transition, hs, ha]
    · exact transition_fixed_src e f hs
  | succ n ih =>
    rw [smoothed_succ_right]
    have h := leakage_mul_le (stochastic_smoothed hP n) (stochastic_lazy hP) e
      (liftSet (G := G) e.src (reach G w t e.dst n))
      (liftSet (G := G) e.src (reach G w t e.dst (n+1)))
    have hinc := incoming_good_le hw hx hc ht n e (reach G w t e.dst n)
    have hmass := mul_le_mul_of_nonneg_left (hL e.src) (mul_nonneg (sq_nonneg x) ht)
    simp only [reach] at h
    simp only [Nat.cast_add, Nat.cast_one]
    change rowMass (smoothed (transition G w) n * lazy (transition G w)) e
      (liftSet (G := G) e.src (enlarge G w t (reach G w t e.dst n)))ᶜ ≤ _
    calc
      _ ≤ _ := h
      _ ≤ n * (x ^ 2 * t * L) + x ^ 2 * t * L :=
        add_le_add ih (hinc.trans hmass)
      _ = _ := by ring

lemma law_rev (e : EdgeState G) : law G w e.rev = law G w e := by
  simp only [law, EdgeState.src_rev, EdgeState.dst_rev, commonMass_comm G w e.dst e.src]
  ring

lemma law_bad_sum (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) =
      (∑ v, w v * crossMass G w (B v) (neighbors G v)) / normalizer G w := by
  have hr := EdgeState.revEquiv (G := G) |>.sum_comp
    (fun e : EdgeState G ↦ if e.src ∈ B e.dst then law G w e else 0)
  simp only [EdgeState.revEquiv, Equiv.coe_fn_mk, EdgeState.src_rev, EdgeState.dst_rev,
    law_rev] at hr
  rw [← hr]
  unfold law
  rw [EdgeState.sum_eq (fun u v ↦ if v ∈ B u then
    w u * w v * commonMass G w u v / normalizer G w else 0)]
  simp_rw [crossMass_neighbors, mul_sum, sum_div]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter]
  have he : (neighbors G v).filter (fun u ↦ u ∈ B v) = B v :=
    filter_mem_eq_inter.trans (inter_eq_right.2 (hB v))
  rw [he]
  apply sum_congr rfl
  intro u _
  rw [commonMass_comm G w v u]
  ring

lemma law_bad_le [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) {q : ℝ}
    (hb : ∀ v, crossMass G w (B v) (neighbors G v) ≤ q * triangleAt G w v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) ≤ q := by
  rw [law_bad_sum B hB, div_le_iff₀ (normalizer_pos hw hc)]
  calc
    _ ≤ ∑ v, w v * (q * triangleAt G w v) :=
      sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hb v) (hw v).le
    _ = q * normalizer G w := by
      rw [normalizer_eq, triangleMass_eq_sum, mul_sum]
      apply sum_congr rfl
      intro v _
      ring

lemma entropy_good_row (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) {b : ℝ} (hb : 1 ≤ b)
    (he : e.src ∉ badSet G w (fun v ↦ reach G w t v n) b e.dst) :
    entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hsmall : mass w (reach G w t e.dst n ∩ neighbors G e.src) ≤ b := by
    by_contra! h
    exact he (mem_filter.2 ⟨(mem_neighbors G _ _).2 e.adj.symm, h⟩)
  have h := entropy_supported_concentration (w := vertexWeight G w)
    (fiber G e.src) (liftSet (G := G) e.src (reach G w t e.dst n))
    (liftSet_subset_fiber _ _) (fun f _ ↦ hw f.dst) (stochastic_smoothed hP n e)
    (smoothed_supported n e) hb (Real.exp_pos x)
    (by change (∑ f ∈ liftSet (G := G) e.src (reach G w t e.dst n), w f.dst) ≤ b
        rw [sum_liftSet]; exact hsmall)
    (by rw [fiber_mass]; exact hL _)
  rw [Real.log_exp] at h
  have hl := reach_leakage hw hx hc hL ht n e
  rw [rowMass_compl (stochastic_smoothed hP n)] at hl
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hl hx.le))

lemma averaged_entropy_bound [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {b q : ℝ} (hb : 1 ≤ b)
    (hbad : (∑ e : EdgeState G,
      if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) ≤ q) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x + q * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  let A := Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x
  have hA : 0 ≤ A := by
    dsimp [A]
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
    positivity
  have hrow (e : EdgeState G) :
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
        A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0 := by
    split_ifs with he
    · exact (entropy_bounds hw hx hc hL n e).2.trans (by linarith)
    · simpa only [add_zero] using entropy_good_row hw hx hc hL ht n e hb he
  calc
    _ ≤ ∑ e, law G w e *
        (A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0) :=
      sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left (hrow e) (hmu.1 e)
    _ = A + (∑ e : EdgeState G,
        if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) * x := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hmu.2, one_mul, mul_ite, mul_zero]
      rw [sum_mul]
      simp only [ite_mul, zero_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hbad hx.le)

lemma avg_entropy_lower [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) :
    -Real.log x ≤ avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  calc
    _ = (∑ e, law G w e) * (-Real.log x) := by rw [hmu.2, one_mul]
    _ = ∑ e, law G w e * (-Real.log x) := sum_mul _ _ _
    _ ≤ _ := sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left
      (entropy_bounds hw hx hc hL n e).1 (hmu.1 e)

lemma avg_entropy_upper [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (n : ℕ) (hn : (n : ℝ) ≤ 2 * x) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      entropyConstant C * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hbad := law_bad_le hw hc0
    (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8))
    (badSet_subset G w _ _) (reach_bad_cross G (fun u ↦ (hw u).le) hC hCross hx hL hc hn)
  have hb : (1 : ℝ) ≤ x ^ 8 := one_le_pow₀ hx1
  have h := averaged_entropy_bound hw hx0 hc hL (Numerical.threshold_pos hx0).le n hb hbad
  rw [Real.log_pow] at h
  have hleak : ((n : ℝ) * (x ^ 2 * Numerical.threshold x * Real.exp x)) * x ≤ 1 := by
    rw [Numerical.leakage_factor hx0]
    calc
      _ = (n : ℝ) / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ (2 * x) / x ^ 3 := div_le_div_of_nonneg_right hn (pow_pos hx0 3).le
      _ = 2 / x ^ 2 := by field_simp [hx0.ne']
      _ ≤ 1 := (div_le_iff₀ (pow_pos hx0 2)).2 (by nlinarith)
  have hE := exceptionalConstant_nonneg hC
  have hq : (exceptionalConstant C / x ^ 4) * x ≤ exceptionalConstant C * Real.log x := by
    calc
      _ = exceptionalConstant C / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ exceptionalConstant C := (div_le_iff₀ (pow_pos hx0 3)).2 (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hx1 (n := 3)) hE)
      _ ≤ _ := by nlinarith [(Numerical.log_bounds hx).1]
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hl1 := (Numerical.log_bounds hx).1
  unfold entropyConstant
  norm_num only [Nat.cast_ofNat] at h
  linarith

noncomputable def rowDistance (n : ℕ) : ℝ :=
  ∑ e : EdgeState G, law G w e * ∑ f, transition G w e f *
    tv (smoothed (transition G w) n e) (smoothed (transition G w) n f)

/-- The `C`-dependent entropy smoothing bound. -/
lemma exists_smooth_index [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ j < ⌈x⌉₊,
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) j) ≤
        entropyConstant C * Real.log x ∧
      rowDistance (G := G) (w := w) j ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  have hP := transition_stochastic hw hc0
  have hs := stationary_of_reversible hP (transition_reversible hw hc0)
  have hceil := Numerical.ceil_bounds hx
  have hlow := avg_entropy_lower hw hx0 hc hL 0
  have hupp := avg_entropy_upper hw hC0 hCross hx hc hL ⌈x⌉₊ hceil.2.2
  have hD : avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) ⌈x⌉₊) -
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) 0) ≤
      (entropyConstant C + 1) * Real.log x := by linarith
  obtain ⟨j, hj, hdist⟩ := exists_smoothed_row_distance hmu (fun e ↦ hw e.dst) hP hs hceil.1 hD
  refine ⟨j, hj, ?_, ?_⟩
  · exact (smoothed_entropy_mono hmu (fun e ↦ hw e.dst) hP hs (Nat.le_of_lt hj)).trans hupp
  · have hA : 0 ≤ entropyConstant C + 1 := by
      have := exceptionalConstant_nonneg hC0
      unfold entropyConstant
      linarith
    have hlog : 0 ≤ Real.log x := ((Numerical.log_bounds hx).1.trans' (by norm_num))
    have href : rowDistance (G := G) (w := w) j ^ 2 ≤
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      exact hdist.trans (div_le_div_of_nonneg_left (by positivity) hx0 hceil.2.1)
    have hf : 0 ≤ Real.log x / x := div_nonneg hlog hx0.le
    have hsq : (smoothingConstant C * Real.sqrt (Real.log x / x)) ^ 2 =
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      rw [mul_pow, smoothingConstant, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hf]
      ring
    have hn : 0 ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
      unfold smoothingConstant
      positivity
    nlinarith

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.WalkCoupling =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere7 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}
lemma triangle_pair_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12 t.edge13) =
      normalizer G w * ∑ e, law G w e * ∑ z, transition G w e z * f e z := by
  rw [TriangleState.corner_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  have he := (hc _ _ e.adj).ne'
  have hZ := (normalizer_pos hw hc).ne'
  by_cases hs : e.src = z.src
  · by_cases ha : G.Adj e.dst z.dst
    · simp only [hs, ha, true_and, ↓reduceIte, transition, law]
      rw [hs] at he
      field_simp
    · simp [hs, ha, transition]
  · simp [hs, transition]

lemma triangle_edge_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) (f : EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12) =
      normalizer G w * ∑ e, law G w e * f e := by
  rw [triangle_pair_sum hw hc (fun e _ ↦ f e)]
  simp only [← sum_mul, (transition_stochastic hw hc _).2, one_mul]
end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.FiniteCoupling =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence


namespace FiniteCoupling
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq E := Classical.decEq E

abbrev Law (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
noncomputable def dist (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

def push (p : I → ℝ) (f : I → J) (y : J) : ℝ := ∑ i, if f i = y then p i else 0

def mix (p : I → ℝ) (q : I → J → ℝ) (y : J) : ℝ := ∑ i, p i * q i y

lemma sum_push (p : I → ℝ) (f : I → J) (g : J → ℝ) :
    ∑ y, push p f y * g y = ∑ i, p i * g (f i) := by
  simp only [push, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

lemma law_push {p : I → ℝ} (hp : Law p) (f : I → J) : Law (push p f) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ by split_ifs <;> simp_all, ?_⟩
  have h := sum_push p f (fun _ ↦ 1)
  simpa [hp.2] using h

lemma sum_mix (p : I → ℝ) (q : I → J → ℝ) (g : J → ℝ) :
    ∑ y, mix p q y * g y = ∑ i, p i * ∑ y, q i y * g y := by
  simp only [mix, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

lemma law_mix {p : I → ℝ} {q : I → J → ℝ} (hp : Law p) (hq : ∀ i, Law (q i)) :
    Law (mix p q) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ mul_nonneg (hp.1 i) ((hq i).1 y), ?_⟩
  have h := sum_mix p q (fun _ ↦ 1)
  simpa only [mul_one, (hq _).2, hp.2] using h

lemma law_dirac (j : J) : Law (fun y ↦ if y = j then (1 : ℝ) else 0) := by
  constructor
  · intro y; dsimp; split_ifs <;> norm_num
  · simp

lemma prob_event_le_one {p : I → ℝ} (hp : Law p) (b : I → Prop) [DecidablePred b] :
    (∑ i, if b i then p i else 0) ≤ 1 := by
  rw [← hp.2]
  apply sum_le_sum
  intro i _
  split_ifs <;> simp_all

lemma expected_indicator_push {p : I → ℝ} (f : I → J) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then push p f y else 0) = ∑ i, if b (f i) then p i else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_push p f (fun y ↦ if b y then 1 else 0)

lemma expected_indicator_mix (p : I → ℝ) (q : I → J → ℝ) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then mix p q y else 0) =
      ∑ i, p i * ∑ y, if b y then q i y else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_mix p q (fun y ↦ if b y then 1 else 0)

open MeasureTheory in
lemma exists_threshold_law (a : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    ∃ q : Finset I → ℝ, Law q ∧
      (∀ i, (∑ A, if i ∈ A then q A else 0) = a i) ∧
      (∀ i j, (∑ A, if i ∈ A ∧ j ∈ A then q A else 0) = min (a i) (a j)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 1)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Real.volume_Icc]
  let f : ℝ → Finset I := fun t ↦ univ.filter (fun i ↦ t ≤ a i)
  have hf : ∀ A, MeasurableSet (f ⁻¹' {A}) := by
    intro A
    have heq : f ⁻¹' {A} = ⋂ i, {t : ℝ | (t ≤ a i ↔ i ∈ A)} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.ext_iff,
        f, mem_filter, mem_univ, true_and, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ A
    · simpa only [hi, iff_true, Set.Iic] using (measurableSet_Iic : MeasurableSet (Set.Iic (a i)))
    · simpa only [hi, iff_false, not_le, Set.Ioi] using (measurableSet_Ioi : MeasurableSet (Set.Ioi (a i)))
  let q : Finset I → ℝ := fun A ↦ μ.real (f ⁻¹' {A})
  have hevent (b : Finset I → Prop) [DecidablePred b] :
      (∑ A, if b A then q A else 0) = μ.real {t | b (f t)} := by
    rw [← sum_filter]
    have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter b) (fun A _ ↦ hf A)
    convert h using 1; simp
  have hmass (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      μ.real {t | t ≤ c} = c := by
    change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic c) = c
    rw [measureReal_restrict_apply measurableSet_Iic]
    have heq : Set.Iic c ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 c := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨ht, h0, _⟩; exact ⟨h0, ht⟩
      · rintro ⟨h0, htc⟩; exact ⟨htc, h0, htc.trans hc1⟩
    change volume.real (Set.Iic c ∩ Set.Icc (0 : ℝ) 1) = _
    rw [heq, measureReal_def, Real.volume_Icc]
    simpa using ENNReal.toReal_ofReal hc0
  refine ⟨q, ⟨fun A ↦ measureReal_nonneg, ?_⟩, ?_, ?_⟩
  · have h := hevent (fun _ ↦ True)
    simpa [μ, measureReal_def, Real.volume_Icc] using h
  · intro i
    trans μ.real {t | i ∈ f t}
    · exact hevent (fun A ↦ i ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and] using hmass (a i) (ha0 i) (ha1 i)
  · intro i j
    trans μ.real {t | i ∈ f t ∧ j ∈ f t}
    · exact hevent (fun A ↦ i ∈ A ∧ j ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and, le_min_iff] using
      hmass (min (a i) (a j)) (le_min (ha0 i) (ha0 j)) ((min_le_left _ _).trans (ha1 i))

/-- A finite version of the first-accepted-trial construction, with states the
set of unfinished rows. The recursion strictly decreases that finite set. -/
lemma joint_of_trials [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i))
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (A : E → Finset I) (label : E → J)
    (hmarg : ∀ i y, (∑ e, if i ∈ A e ∧ label e = y then t e else 0) = p i y)
    (D : I → I → ℝ)
    (hpair : ∀ i j,
      (∑ e, if Xor (i ∈ A e) (j ∈ A e) then t e else 0) ≤
        D i j * (∑ e, if i ∈ A e ∨ j ∈ A e then t e else 0)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
  have hacc (i : I) : (∑ e, if i ∈ A e then t e else 0) = 1 := by
    have h := congrArg (fun g : J → ℝ ↦ ∑ y, g y) (funext (hmarg i))
    change (∑ y, ∑ e, if i ∈ A e ∧ label e = y then t e else 0) = ∑ y, p i y at h
    rw [sum_comm, (hp i).2] at h
    convert h using 1
    apply sum_congr rfl
    intro e _
    by_cases hi : i ∈ A e <;> simp [hi]
  let base : I → J := fun _ ↦ Classical.choice (inferInstance : Nonempty J)
  have hpartial (S : Finset I) :
      ∃ q : (I → J) → ℝ, Law q ∧
        (∀ i ∈ S, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
        (∀ i ∈ S, ∀ j ∈ S, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · let active : E → Prop := fun e ↦ (S ∩ A e).Nonempty
      let r : E → ℝ := fun e ↦ if active e then t e else 0
      let Q : ℝ := ∑ e, r e
      have hr (e : E) : 0 ≤ r e := by dsimp [r]; split_ifs <;> simp_all
      have hactive (i : I) (hi : i ∈ S) (e : E) (ha : i ∈ A e) : active e :=
        ⟨i, mem_inter.2 ⟨hi, ha⟩⟩
      have hQ : 0 < Q := by
        obtain ⟨i, hi⟩ := hS
        have hle : (∑ e, if i ∈ A e then t e else 0) ≤ Q := by
          apply sum_le_sum
          intro e _
          by_cases ha : i ∈ A e
          · simp only [ha, ↓reduceIte, r, hactive i hi e ha, le_refl]
          · simpa only [ha, ↓reduceIte] using hr e
        rw [hacc] at hle
        linarith
      have hrec (e : E) : ∃ q : (I → J) → ℝ, Law q ∧
          (active e →
            (∀ i ∈ S \ A e, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
            (∀ i ∈ S \ A e, ∀ j ∈ S \ A e,
              (∑ f, if f i ≠ f j then q f else 0) ≤ D i j)) := by
        by_cases he : active e
        · have hlt : S \ A e ⊂ S := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, ?_⟩
            intro heq
            obtain ⟨i, hi⟩ := he
            obtain ⟨hiS, hiA⟩ := mem_inter.1 hi
            rw [← heq] at hiS
            exact (mem_sdiff.1 hiS).2 hiA
          obtain ⟨q, hq, hqm, hqd⟩ := ih (S \ A e) hlt
          exact ⟨q, hq, fun _ ↦ ⟨hqm, hqd⟩⟩
        · exact ⟨_, law_dirac base, fun h ↦ (he h).elim⟩
      choose q hq hqrec using hrec
      let update : E → (I → J) → (I → J) :=
        fun e f i ↦ if i ∈ A e then label e else f i
      let coeff : E → ℝ := fun e ↦ r e / Q
      have hcoeff : Law coeff := by
        refine ⟨fun e ↦ div_nonneg (hr e) hQ.le, ?_⟩
        dsimp [coeff]
        rw [← sum_div]
        exact div_self hQ.ne'
      let out : (I → J) → ℝ := mix coeff (fun e ↦ push (q e) (update e))
      refine ⟨out, law_mix hcoeff (fun e ↦ law_push (hq e) (update e)), ?_, ?_⟩
      · intro i hi y
        change (∑ f, if f i = y then mix coeff (fun e ↦ push (q e) (update e)) f else 0) = _
        rw [expected_indicator_mix]
        simp_rw [expected_indicator_push]
        have heq (e : E) :
            r e * (∑ f, if update e f i = y then q e f else 0) =
              (if i ∈ A e ∧ label e = y then t e else 0) +
                p i y * (r e - if i ∈ A e then t e else 0) := by
          by_cases ha : i ∈ A e
          · have hb := hactive i hi e ha
            simp only [update, ha, ↓reduceIte, r, hb, true_and, sub_self, mul_zero, add_zero,
              sum_ite_irrel, (hq e).2]
            split_ifs <;> simp
          · have hni : i ∈ S \ A e := mem_sdiff.2 ⟨hi, ha⟩
            by_cases hb : active e
            · have hm := (hqrec e hb).1 i hni y
              simp only [update, ha, ↓reduceIte, false_and, r, hb, sub_zero, zero_add] at *
              rw [hm]
              ring
            · simp [r, hb, ha]
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        simp_rw [heq]
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, hmarg, hacc]
        change (p i y + p i y * (Q - 1)) / Q = p i y
        field_simp
        ring
      · intro i hi j hj
        change (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) ≤ _
        have hem : (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) =
            ∑ e, coeff e * ∑ f, if f i ≠ f j then push (q e) (update e) f else 0 :=
          expected_indicator_mix coeff (fun e ↦ push (q e) (update e)) (fun f ↦ f i ≠ f j)
        rw [hem]
        simp_rw [expected_indicator_push]
        have he (e : E) :
            r e * (∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
              D i j * r e + (if Xor (i ∈ A e) (j ∈ A e) then t e else 0) -
                D i j * (if i ∈ A e ∨ j ∈ A e then t e else 0) := by
          by_cases hai : i ∈ A e <;> by_cases haj : j ∈ A e
          · have hb := hactive i hi e hai
            simp [update, hai, haj, r, hb, Xor]
          · have hb := hactive i hi e hai
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ label e ≠ f j)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · have hb := hactive j hj e haj
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ f i ≠ label e)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · by_cases hb : active e
            · have hle := mul_le_mul_of_nonneg_left
                ((hqrec e hb).2 i (mem_sdiff.2 ⟨hi, hai⟩) j (mem_sdiff.2 ⟨hj, haj⟩)) (ht e)
              simpa [update, hai, haj, r, hb, Xor, mul_comm] using hle
            · simp [r, hb, hai, haj, Xor]
        have hsum := sum_le_sum (s := univ) (fun e _ ↦ he e)
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
        have hbound : (∑ e, r e * ∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
            D i j * Q := by
          have hpij := hpair i j
          dsimp [Q]
          linarith
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        exact (div_le_iff₀ hQ).2 (by nlinarith [hbound])
    · refine ⟨_, law_dirac base, ?_, ?_⟩ <;> simp_all
  obtain ⟨q, hq, hm, hd⟩ := hpartial univ
  exact ⟨q, hq, fun i ↦ hm i (mem_univ i), fun i j ↦ hd i (mem_univ i) j (mem_univ j)⟩

lemma sum_abs_eq (a b : ℝ) : a + b - 2 * min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/-- The joint finite law in the shared rejection lemma, with its sharp bound. -/
lemma shared_rejection [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤
        2 * dist (p i) (p j) / (1 + dist (p i) (p j))) := by
  have hbound (i : I) (y : J) : p i y ≤ 1 := by
    rw [← (hp i).2]
    exact single_le_sum (fun z _ ↦ (hp i).1 z) (mem_univ y)
  have hex (y : J) := exists_threshold_law (fun i ↦ p i y) (fun i ↦ (hp i).1 y) (fun i ↦ hbound i y)
  choose q hq hsingle hboth using hex
  let t : J × Finset I → ℝ := fun e ↦ q e.1 e.2
  have hmarg (i : I) (y : J) :
      (∑ e : J × Finset I, if i ∈ e.2 ∧ e.1 = y then t e else 0) = p i y := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ z, if z = y then (∑ A, if i ∈ A then q z A else 0) else 0 := by
        apply sum_congr rfl
        intro z _
        by_cases hz : z = y <;> simp [hz, t]
      _ = _ := by simp [hsingle]
  have hxor (i j : I) (y : J) :
      (∑ A, if Xor (i ∈ A) (j ∈ A) then q y A else 0) = |p i y - p j y| := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          2 * (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj, Xor]
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hsingle, hsingle, hboth]
        exact sum_abs_eq _ _
  have hor (i j : I) (y : J) :
      (∑ A, if i ∈ A ∨ j ∈ A then q y A else 0) =
        (p i y + p j y + |p i y - p j y|) / 2 := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, hsingle, hsingle, hboth]
        linarith [sum_abs_eq (p i y) (p j y)]
  have hdist0 (i j : I) : 0 ≤ dist (p i) (p j) :=
    div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply joint_of_trials p hp t (fun e ↦ (hq e.1).1 e.2) Prod.snd Prod.fst hmarg
    (fun i j ↦ 2 * dist (p i) (p j) / (1 + dist (p i) (p j)))
  intro i j
  have hden : 1 + dist (p i) (p j) ≠ 0 := by linarith [hdist0 i j]
  have hX : (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) =
      2 * dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hxor, dist]
    ring
  have hU : (∑ e : J × Finset I, if i ∈ e.2 ∨ j ∈ e.2 then t e else 0) =
      1 + dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hor, ← sum_div, sum_add_distrib, (hp i).2, (hp j).2, dist]
    ring
  change (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) ≤ _
  rw [hX, hU, div_mul_cancel₀ _ hden]

lemma sharp_bound_le (p q : I → ℝ) : 2 * dist p q / (1 + dist p q) ≤ 2 * dist p q := by
  have hd : 0 ≤ dist p q := div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply div_le_self (by positivity) (by linarith)

lemma positive_output {p : I → J → ℝ} {q : (I → J) → ℝ} (hq : Law q)
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y)
    {f : I → J} (hf : 0 < q f) (i : I) : 0 < p i (f i) := by
  rw [← hm]
  exact hf.trans_le (by
    have h := single_le_sum (s := univ) (a := f)
      (f := fun g ↦ if g i = f i then q g else 0)
      (fun g _ ↦ by split_ifs <;> simp_all [hq.1 g]) (mem_univ f)
    simpa using h)

lemma marginal_expectation {p : I → J → ℝ} {q : (I → J) → ℝ}
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y) (i : I) (g : J → ℝ) :
    (∑ f, q f * g (f i)) = ∑ y, p i y * g y := by
  have h := sum_push q (fun f ↦ f i) g
  simpa only [push, hm] using h.symm

lemma exists_positive_ge {q : I → ℝ} (hq : Law q) (f : I → ℝ) {L : ℝ}
    (hL : L ≤ ∑ i, q i * f i) : ∃ i, 0 < q i ∧ L ≤ f i := by
  by_contra h
  have hf : ∀ i, 0 < q i → f i < L := by
    intro i hi
    by_contra hn
    exact h ⟨i, hi, le_of_not_gt hn⟩
  obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg (fun j (_ : j ∈ univ) ↦ hq.1 j)).1
    (show 0 < ∑ j, q j by rw [hq.2]; norm_num)
  have hlt : (∑ j, q j * f j) < ∑ j, q j * L := by
    apply sum_lt_sum
    · intro j _
      rcases (hq.1 j).eq_or_lt with hj | hj
      · simp [← hj]
      · exact (mul_lt_mul_of_pos_left (hf j hj) hj).le
    · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hf i hi) hi⟩
  rw [← sum_mul, hq.2, one_mul] at hlt
  linarith

noncomputable def bad (p : Prop) : ℝ := if p then 0 else 1

lemma bad_and (p q : Prop) : bad (p ∧ q) ≤ bad p + bad q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bad, hp, hq]

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.SplittingLoss =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere8 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

namespace Splitting
open FiniteCoupling
variable {G : SimpleGraph V}

omit [Fintype V] in
lemma bad_survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) :
    bad (Survives F good t) ≤ bad (F t.edge12 = F t.edge13) +
      bad (F t.edge12.rev = F t.edge23) + bad (F t.edge13.rev = F t.edge23.rev) +
      bad (good t.edge12) + bad (good t.edge12.rev) + bad (good t.edge13) +
      bad (good t.edge13.rev) + bad (good t.edge23) + bad (good t.edge23.rev) := by
  unfold Survives
  have h1 := bad_and (F t.edge12 = F t.edge13)
    (F t.edge12.rev = F t.edge23 ∧ F t.edge13.rev = F t.edge23.rev ∧
      good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h2 := bad_and (F t.edge12.rev = F t.edge23)
    (F t.edge13.rev = F t.edge23.rev ∧ good t.edge12 ∧ good t.edge12.rev ∧
      good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h3 := bad_and (F t.edge13.rev = F t.edge23.rev)
    (good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h4 := bad_and (good t.edge12)
    (good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h5 := bad_and (good t.edge12.rev)
    (good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h6 := bad_and (good t.edge13) (good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h7 := bad_and (good t.edge13.rev) (good t.edge23 ∧ good t.edge23.rev)
  have h8 := bad_and (good t.edge23) (good t.edge23.rev)
  linarith

lemma bad_mass_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t)) ≤
      3 * (∑ t, TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) +
      6 * (∑ t, TriangleState.weight w t * bad (good t.edge12)) := by
  have h := sum_le_sum (s := univ) fun t _ ↦
    mul_le_mul_of_nonneg_left (bad_survives F good t)
      (show 0 ≤ TriangleState.weight w t from
        mul_nonneg (mul_nonneg (hw t.first) (hw t.second)) (hw t.third))
  simp only [mul_add, sum_add_distrib] at h
  obtain ⟨h1,h2,h3,h4,h5⟩ := TriangleState.sum_edge_permutations w (fun e ↦ bad (good e))
  have hc2 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12.rev = F t.edge23)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) := by
    have h := TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13))
    convert h using 1
    apply sum_congr rfl
    intro t _
    change _ * bad (F t.edge12.rev = F t.edge23) = _ * bad (F t.edge23 = F t.edge12.rev)
    rw [eq_comm (a := F t.edge23)]
  have hc3 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge13.rev = F t.edge23.rev)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) :=
    (TriangleState.sum_rotate w (fun t ↦ bad (F (TriangleState.rotate t).edge12 = F (TriangleState.rotate t).edge13))).trans
      (TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13)))
  rw [h1,h2,h3,h4,h5,hc2,hc3] at h
  linarith

lemma surviving_mass_eq {w : V → ℝ}
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) =
      6 * triangleMass G w - ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t) := by
  rw [← TriangleState.sum_weight, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : Survives F good t <;> simp [bad, ht]

open FiniteEntropy FiniteKernel LocalWalk

/-- The finite-law aggregate of all corner and incidence losses. -/
lemma expected_loss_le [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) {q : (EdgeState G → EdgeState G) → ℝ}
    (hq : Law q) (hm : ∀ i y, (∑ F, if F i = y then q F else 0) = K i y)
    (hp : ∀ i j, (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j))
    (good : (EdgeState G → EdgeState G) → EdgeState G → Prop)
    (b : EdgeState G → EdgeState G → Prop)
    (hb : ∀ F e, good F e ↔ b e (F e)) :
    (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w *
        (6 * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) +
         6 * (∑ e, law G w e * ∑ y, K e y * bad (b e y))) := by
  have hcoup (i j : EdgeState G) : (∑ F, q F * bad (F i = F j)) ≤ 2 * tv (K i) (K j) := by
    convert hp i j using 1
    apply sum_congr rfl
    intro F _
    by_cases h : F i = F j <;> simp [bad, h]
  have hadm (e : EdgeState G) : (∑ F, q F * bad (good F e)) = ∑ y, K e y * bad (b e y) := by
    simp_rw [hb]
    exact marginal_expectation hm e (fun y ↦ bad (b e y))
  have hcorner : (∑ F, q F * ∑ t : TriangleState G,
      TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) ≤
      2 * normalizer G w * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (F t.edge12 = F t.edge13) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ ≤ ∑ t : TriangleState G, TriangleState.weight w t * (2 * tv (K t.edge12) (K t.edge13)) :=
        sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hcoup _ _) (TriangleState.weight_pos hw t).le
      _ = 2 * ∑ t : TriangleState G, TriangleState.weight w t * tv (K t.edge12) (K t.edge13) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ = _ := by
        rw [triangle_pair_sum hw hc (fun e z ↦ tv (K e) (K z))]
        ring
  have hincidence : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (good F t.edge12)) =
      normalizer G w * ∑ e, law G w e * ∑ y, K e y * bad (b e y) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (good F t.edge12) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ = _ := by simp_rw [hadm]; exact triangle_edge_sum hw hc (fun e ↦ ∑ y, K e y * bad (b e y))
  have h := sum_le_sum (s := univ) fun F _ ↦
    mul_le_mul_of_nonneg_left (bad_mass_le (fun u ↦ (hw u).le) F (good F)) (hq.1 F)
  simp only [mul_add, sum_add_distrib, ← mul_assoc] at h
  have hid (a : ℝ) (f : (EdgeState G → EdgeState G) → ℝ) :
      (∑ F, q F * a * f F) = a * ∑ F, q F * f F := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro F _
    ring
  rw [hid, hid, hincidence] at h
  nlinarith

/-- Splitting from a joint kernel preserving first coordinates, with two averaged losses. -/
lemma exists_graph [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) (hK : Stochastic K)
    (hblock : ∀ e z, e.src ≠ z.src → K e z = 0)
    {a D δ : ℝ}
    (hD : (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) ≤ D)
    (hδ : (∑ e, law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-a) then K e y else 0) ≤ δ) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp a) ∧
      (1 - 6 * D - 6 * δ) * triangleMass G w ≤ triangleMass H (w ∘ EdgeState.src) := by
  obtain ⟨q,hq,hm,hp⟩ := shared_rejection K hK
  have hp' (i j : EdgeState G) : (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j) :=
    (hp i j).trans (sharp_bound_le (K i) (K j))
  let b : EdgeState G → EdgeState G → Prop := fun e y ↦ w e.dst * Real.exp (-a) ≤ K y e
  let good : (EdgeState G → EdgeState G) → EdgeState G → Prop := fun F e ↦ b e (F e)
  have hb (e y : EdgeState G) : K e y * bad (b e y) =
      if K y e < w e.dst * Real.exp (-a) then K e y else 0 := by
    by_cases h : K y e < w e.dst * Real.exp (-a)
    · simp [b,bad,h,not_le.2 h]
    · simp [b,bad,h,le_of_not_gt h]
  have hloss := expected_loss_le hw hc K hq hm hp' good b (fun _ _ ↦ Iff.rfl)
  simp_rw [hb] at hloss
  have hZ := (normalizer_pos hw hc).le
  have hZeq := normalizer_eq G w
  have hbound : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w * (6 * D + 6 * δ) :=
    hloss.trans (mul_le_mul_of_nonneg_left (by linarith [hD,hδ]) hZ)
  let S : (EdgeState G → EdgeState G) → ℝ := fun F ↦
    ∑ t : TriangleState G, if Survives F (good F) t then TriangleState.weight w t else 0
  have havg : normalizer G w * (1 - 6 * D - 6 * δ) ≤ ∑ F, q F * S F := by
    dsimp [S]
    simp_rw [surviving_mass_eq]
    rw [show (∑ F, q F * (6 * triangleMass G w -
        ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t))) =
        6 * triangleMass G w - ∑ F, q F * ∑ t : TriangleState G,
          TriangleState.weight w t * bad (Survives F (good F) t) by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hq.2, one_mul]]
    nlinarith
  obtain ⟨F,hFq,hFS⟩ := exists_positive_ge hq S havg
  have hF (e : EdgeState G) : (F e).src = e.src := by
    have hpos := positive_output hq hm hFq e
    by_contra hn
    have hzero := hblock e (F e) (Ne.symm hn)
    linarith
  let H := graph F hF (good F)
  refine ⟨H,projection F hF (good F),?_,?_⟩
  · intro z
    apply neighborMass_le w F hF (good F) K (fun a e ↦ (hK a).1 e)
      (fun a ↦ (hK a).2) (Real.exp_pos a).le ?_ z
    intro e he
    have hh : w e.dst * Real.exp (-a) ≤ K (F e) e := he
    have ht := mul_le_mul_of_nonneg_left hh (Real.exp_pos a).le
    have hid : Real.exp a * (w e.dst * Real.exp (-a)) = w e.dst := by
      calc
        _ = w e.dst * (Real.exp a * Real.exp (-a)) := by ring
        _ = _ := by rw [← Real.exp_add]; simp
    rwa [hid] at ht
  · have ht := triangleMass_surviving_le (fun v ↦ (hw v).le) F hF (good F)
    change S F ≤ 6 * triangleMass H (w ∘ EdgeState.src) at ht
    rw [hZeq] at hFS
    nlinarith only [ht, hFS]

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.VertexSplitting =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere9 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

noncomputable def splittingConstant (C : ℝ) : ℝ :=
  6 * (smoothingConstant C + entropyConstant C + 1)

lemma splitting_error_le {C x : ℝ} (hC : 1 ≤ C) (hx : 32 ≤ x) :
    6 * (smoothingConstant C * Real.sqrt (Real.log x / x)) +
    6 * ((entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x)) ≤
    splittingConstant C * (Real.log x / Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hl := (Numerical.log_bounds hx).1
  have hl0 : 0 ≤ Real.log x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hA : 0 ≤ entropyConstant C + 1 := by
    unfold entropyConstant exceptionalConstant
    positivity
  have hB : 0 ≤ smoothingConstant C := by unfold smoothingConstant; positivity
  have hslog : Real.sqrt (Real.log x) ≤ Real.log x := by
    have hh := Real.sq_sqrt hl0
    have hn := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have h1 : Real.sqrt (Real.log x / x) ≤ Real.log x / Real.sqrt x := by
    rw [Real.sqrt_div hl0]
    exact div_le_div_of_nonneg_right hslog hs.le
  have h2 : (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) ≤
      (entropyConstant C + 1) * (Real.log x / Real.sqrt x) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg hA hl0) hs (by linarith)
  unfold splittingConstant
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]

/-- Weighted vertex splitting with explicit constants. -/
lemma weighted_splitting {G : SimpleGraph V} [Nonempty (EdgeState G)] {w : V → ℝ}
    (hw : ∀ u, 0 < w u) {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C)
    (hx : 32 ≤ x) (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp (Real.sqrt x)) ∧
      (1 - splittingConstant C * (Real.log x / Real.sqrt x)) * triangleMass G w ≤
        triangleMass H (w ∘ EdgeState.src) := by
  open FiniteEntropy FiniteKernel LocalWalk in
  have hx0 : 0 < x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  obtain ⟨j,_,hH,hD⟩ := LocalWalk.exists_smooth_index hw hC hCross hx hc hL
  let K := FiniteKernel.smoothed (LocalWalk.transition G w) j
  have hP := LocalWalk.transition_stochastic hw hc0
  have hK := FiniteKernel.stochastic_smoothed hP j
  have hrev := FiniteKernel.reversible_smoothed (LocalWalk.transition_reversible hw hc0) j
  have htail := FiniteKernel.reversed_entropy_tail (LocalWalk.law_isProb hw hc0)
    (fun e : EdgeState G ↦ hw e.dst) hK hrev hx0 (LocalWalk.smoothed_density hw hx0 hc j)
    (a := Real.sqrt x)
  have hden : 0 < Real.sqrt x + Real.log x := by
    have hs := Real.sqrt_pos.2 hx0
    linarith [(Numerical.log_bounds hx).1]
  have hδ : (∑ e, LocalWalk.law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-Real.sqrt x) then K e y else 0) ≤
        (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) := by
    apply (le_div_iff₀ hden).2
    dsimp [K]
    change FiniteKernel.avgEntropy (LocalWalk.law G w) (fun e ↦ w e.dst)
      (FiniteKernel.smoothed (LocalWalk.transition G w) j) ≤ entropyConstant C * Real.log x at hH
    nlinarith only [htail,hH]
  obtain ⟨H,hproj,hneigh,htri⟩ := Splitting.exists_graph hw hc0 K hK
    (LocalWalk.smoothed_fixed_src j) hD hδ
  refine ⟨H,hproj,hneigh,?_⟩
  have hn := triangleMass_nonneg G (fun u ↦ (hw u).le)
  have he := splitting_error_le hC hx
  nlinarith [mul_le_mul_of_nonneg_right he hn]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Peeling =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

local instance (priority := 10000) edgeStateDecEqHere10 (G : SimpleGraph V) : DecidableEq (EdgeState G) := edgeStateDecEq G

open FiniteCoupling
lemma triangle_subgraph_surviving_le {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    (∑ t : TriangleState G, if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
      then TriangleState.weight w t else 0) ≤ 6 * triangleMass H w := by
  classical
  let S := {t : TriangleState G // H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third}
  let f : S → TriangleState H := fun t ↦ ⟨t.val.val, t.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : TriangleState H ↦ t.val) hab
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight w (f t) := rfl
    _ ≤ ∑ t : TriangleState H, TriangleState.weight w t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

lemma triangle_deletion_bound {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    6 * triangleMass G w ≤ 6 * triangleMass H w +
      3 * ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * bad (H.Adj e.src e.dst) := by
  have ht (t : TriangleState G) : TriangleState.weight w t ≤
      (if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
        then TriangleState.weight w t else 0) +
      TriangleState.weight w t * (bad (H.Adj t.first t.second) +
        bad (H.Adj t.first t.third) + bad (H.Adj t.second t.third)) := by
    have hn : 0 ≤ TriangleState.weight w t := mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)
    by_cases h1 : H.Adj t.first t.second <;> by_cases h2 : H.Adj t.first t.third <;>
      by_cases h3 : H.Adj t.second t.third <;> simp [bad,h1,h2,h3] <;> linarith
  have hs := sum_le_sum (s := univ) (fun t _ ↦ ht t)
  simp only [sum_add_distrib, mul_add] at hs
  rw [TriangleState.sum_weight] at hs
  have h13 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_flip w (fun t ↦ bad (H.Adj t.first t.second))
  have h23 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.second t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_rotate w (fun t ↦ bad (H.Adj t.first t.second))
  rw [h13,h23,TriangleState.marginal w (fun u v ↦ bad (H.Adj u v))] at hs
  have hsurv := triangle_subgraph_surviving_le (G := G) (H := H) hw
  linarith

/-- Delete exactly one unordered edge. -/
def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = u ∧ b = v ∨ a = v ∧ b = u)
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    intro hab
    apply h.2
    rcases hab with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr ⟨h2,h1⟩
    · exact Or.inl ⟨h2,h1⟩⟩
  loopless := ⟨fun a h ↦ G.irrefl h.1⟩

omit [Fintype V] in
lemma eraseEdge_le (G : SimpleGraph V) (u v : V) : eraseEdge G u v ≤ G := fun _ _ h ↦ h.1

lemma edgeMass_eraseEdge {G : SimpleGraph V} (w : V → ℝ) {u v : V} (huv : G.Adj u v) :
    edgeMass (eraseEdge G u v) w = edgeMass G w - w u * w v := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then w a * w b else 0) =
      (if (eraseEdge G u v).Adj a b then w a * w b else 0) +
      (if a = u ∧ b = v then w u * w v else 0) +
      (if a = v ∧ b = u then w v * w u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn]
    simp only [eraseEdge, h1, h2, or_self, not_false_eq_true, and_true, ite_false, add_zero]
  have he : crossMass G w univ univ = crossMass (eraseEdge G u v) w univ univ + 2 * w u * w v := by
    unfold crossMass
    simp_rw [heq,sum_add_distrib]
    simp [ite_and]

    ring
  unfold edgeMass
  linarith

lemma sum_removed_directed {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst * bad ((eraseEdge G u v).Adj e.src e.dst)) =
      f u v + f v u := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then f a b * bad ((eraseEdge G u v).Adj a b) else 0) =
      (if a = u ∧ b = v then f u v else 0) + (if a = v ∧ b = u then f v u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn,bad]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn,bad]
    by_cases ha : G.Adj a b <;> simp [eraseEdge,h1,h2,bad,ha]
  rw [EdgeState.sum_eq (fun a b ↦ f a b * bad ((eraseEdge G u v).Adj a b))]
  simp only [neighbors,sum_filter]
  simp_rw [heq,sum_add_distrib,ite_and]
  simp

lemma triangleMass_eraseEdge {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {u v : V} (huv : G.Adj u v) :
    triangleMass G w - w u * w v * commonMass G w u v ≤ triangleMass (eraseEdge G u v) w := by
  have h := triangle_deletion_bound (G := G) (H := eraseEdge G u v) hw
  rw [sum_removed_directed huv (fun a b ↦ w a * w b * commonMass G w a b), commonMass_comm G w v u] at h
  nlinarith only [h]

lemma peeling (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u v, H.Adj u v → τ ≤ commonMass H w u v) ∧
      triangleMass G w - τ * edgeMass G w ≤ triangleMass H w := by
  classical
  let S : Finset (SimpleGraph V) := univ.filter (fun H ↦ H ≤ G)
  obtain ⟨H,hHS,hmax⟩ := S.exists_max_image (fun H ↦ triangleMass H w - τ * edgeMass H w)
    ⟨G,by simp [S]⟩
  have hHG : H ≤ G := (mem_filter.1 hHS).2
  have hw0 := fun v ↦ (hw v).le
  refine ⟨H,hHG,?_,?_⟩
  · intro u v huv
    by_contra hn
    have hc : commonMass H w u v < τ := lt_of_not_ge hn
    have hle := hmax (eraseEdge H u v) (by simp [S]; exact (eraseEdge_le H u v).trans hHG)
    rw [edgeMass_eraseEdge w huv] at hle
    have ht := triangleMass_eraseEdge hw0 huv
    have hprod : 0 < w u * w v := mul_pos (hw u) (hw v)
    nlinarith [mul_lt_mul_of_pos_left hc hprod]
  · have hle := hmax G (by simp [S])
    have he := edgeMass_nonneg H hw0
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.TriangleBound =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph
variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma EdgeProjection.of_le {G H : SimpleGraph V} (hHG : H ≤ G) : EdgeProjection H G id where
  map_adj := fun _ _ h ↦ hHG h
  inj := fun _ _ _ _ _ _ h1 h2 ↦ ⟨h1,h2⟩

lemma neighborMass_bot (w : V → ℝ) (u : V) : neighborMass (⊥ : SimpleGraph V) w u = 0 := by
  simp [neighborMass, neighbors, mass]

lemma triangleMass_bot (w : V → ℝ) : triangleMass (⊥ : SimpleGraph V) w = 0 := by
  simp [triangleMass,triangleAt,neighbors]

lemma splittingConstant_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ splittingConstant C := by
  unfold splittingConstant smoothingConstant entropyConstant exceptionalConstant
  positivity

/-- One reduction step, allowing an arbitrary finite vertex type of copies. -/
lemma neighborhood_reduction (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hε : splittingConstant C * Numerical.lossRatio x ≤ 1)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ (U : Type u) (_ : Fintype U) (J : SimpleGraph U) (π : U → V),
      EdgeProjection J G π ∧ (∀ a, neighborMass J (w ∘ π) a ≤ Real.exp (Real.sqrt x)) ∧
      (1-splittingConstant C * Numerical.lossRatio x) * triangleMass G w - edgeMass G w / x ≤
        triangleMass J (w ∘ π) := by
  have hx0 : 0 < x := by linarith
  have hw0 := fun v ↦ (hw v).le
  have hε0 : 0 ≤ splittingConstant C * Numerical.lossRatio x :=
    mul_nonneg (splittingConstant_nonneg hC) (Numerical.lossRatio_nonneg (by linarith))
  obtain ⟨H,hHG,hc,hpeel⟩ := peeling G hw (one_div_pos.2 hx0)
  have hprojH := EdgeProjection.of_le hHG
  have hcH : CrossBound H w C := by
    simpa only [Function.comp_id] using hprojH.crossBound hw0 (by linarith) hCross
  have hLH : ∀ u, neighborMass H w u ≤ Real.exp x := by
    intro u
    exact (hprojH.neighborMass_le hw0 u).trans (hL u)
  by_cases hne : Nonempty (EdgeState H)
  · let := hne
    obtain ⟨J,hproj,hJ,hT⟩ := weighted_splitting hw hC hcH hx hc hLH
    refine ⟨EdgeState H,inferInstance,J,EdgeState.src,?_,hJ,?_⟩
    · exact ⟨fun a b h ↦ hHG (hproj.map_adj a b h),hproj.inj⟩
    · change (1-splittingConstant C * Numerical.lossRatio x) * triangleMass H w ≤
        triangleMass J (w ∘ EdgeState.src) at hT
      have hh := mul_le_mul_of_nonneg_left hpeel (sub_nonneg.2 hε)
      have hm := div_nonneg (edgeMass_nonneg G hw0) hx0.le
      rw [one_div_mul_eq_div] at hh
      nlinarith only [hT, hh, mul_nonneg hε0 hm]
  · have hbot : H = ⊥ := by
      apply SimpleGraph.ext
      funext a b
      apply propext
      simpa only [SimpleGraph.bot_adj, iff_false] using
        (fun hab : H.Adj a b ↦ hne ⟨⟨(a,b),hab⟩⟩)
    rw [hbot,triangleMass_bot] at hpeel
    refine ⟨V,inferInstance,⊥,id,EdgeProjection.of_le bot_le,?_,?_⟩
    · intro a
      simp only [Function.comp_id,neighborMass_bot]
      exact (Real.exp_pos _).le
    · simp only [Function.comp_id,triangleMass_bot]
      rw [one_div_mul_eq_div] at hpeel
      nlinarith [mul_nonneg hε0 (triangleMass_nonneg G hw0)]

/-- Uniform triangle bound at the reverse-squaring scale. -/
lemma triangle_bound_scale {C X : ℝ} (hC : 1 ≤ C) (hX : 32 ≤ X)
    (hsmall : splittingConstant C * Numerical.lossRatio X ≤ 1/4) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ u, 0 < w u) → CrossBound G w C →
      (∀ u, neighborMass G w u ≤ Real.exp (Numerical.scale X n)) →
      triangleMass G w ≤ (1+Real.exp X/3) * (2-(1/2:ℝ)^n) * edgeMass G w := by
  induction n with
  | zero =>
    intro V _ G w hw hCross hL
    have ht := triangleMass_le_of_neighborMass G (fun v ↦ (hw v).le) hL
    simp only [Numerical.scale, pow_zero] at ht ⊢
    have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
    nlinarith
  | succ n ih =>
    intro V _ G w hw hCross hL
    let x := Numerical.scale X (n+1)
    let q : ℝ := (1/2:ℝ)^(n+1)
    let ε := splittingConstant C * Numerical.lossRatio x
    have hx : 32 ≤ x := hX.trans (Numerical.scale_ge (by linarith) _)
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hε0 : 0 ≤ ε := mul_nonneg (splittingConstant_nonneg hC)
      (Numerical.lossRatio_nonneg (by linarith))
    have hε : ε ≤ q/4 := by
      have hh := mul_le_mul_of_nonneg_left (Numerical.lossRatio_scale (by linarith : 16 ≤ X) (n+1))
        (splittingConstant_nonneg hC)
      have hh2 := mul_le_mul_of_nonneg_left hsmall hq0
      dsimp [ε,x,q]
      nlinarith only [hh,hh2]
    obtain ⟨U,inst,J,π,hproj,hJ,hstep⟩ := neighborhood_reduction G hw hC hCross hx
      (by linarith : ε ≤ 1) hL
    let := inst
    have hsqrt : Real.sqrt x = Numerical.scale X n := by
      dsimp [x,Numerical.scale]
      exact Real.sqrt_sq (by linarith [Numerical.scale_ge (by linarith : 1 ≤ X) n])
    rw [hsqrt] at hJ
    have hJcross := hproj.crossBound (fun v ↦ (hw v).le) (by linarith) hCross
    have hupper := ih J (w ∘ π) (fun a ↦ hw (π a)) hJcross hJ
    have hmass := hproj.edgeMass_le (fun v ↦ (hw v).le)
    have hcoeff : 0 ≤ (1+Real.exp X/3)*(2-(1/2:ℝ)^n) := by
      apply mul_nonneg (by positivity)
      have hp : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hupperG := hupper.trans (mul_le_mul_of_nonneg_left hmass hcoeff)
    have hqeq : (1/2:ℝ)^n = 2*q := by dsimp [q]; rw [pow_succ]; ring
    rw [hqeq] at hupperG
    have hinv : 1/x ≤ q/2 := by
      have hi := Numerical.inv_scale (by linarith : 2 ≤ X) (n+1)
      have hXi : 1/X ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) (by linarith))
      have hi2 := mul_le_mul_of_nonneg_left hXi hq0
      dsimp [x,q] at *
      linarith
    apply Numerical.recurrence_bound (by linarith [Real.exp_pos X] : 1 ≤ 1+Real.exp X/3)
      hq0 hq1 hε0 hε (triangleMass_nonneg G (fun v ↦ (hw v).le))
      (edgeMass_nonneg G (fun v ↦ (hw v).le)) hinv
    calc
      (1-ε)*triangleMass G w - (1/x)*edgeMass G w =
          (1-ε)*triangleMass G w - edgeMass G w/x := by ring
      _ ≤ triangleMass J (w ∘ π) := hstep
      _ ≤ _ := hupperG

/-- The weighted triangle theorem with a size-independent constant. -/
theorem weighted_triangles {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ v, 0 < w v) → CrossBound G w C → triangleMass G w ≤ B * edgeMass G w := by
  obtain ⟨X,hX,hsmall⟩ := Numerical.exists_iteration_threshold (splittingConstant C)
  refine ⟨2*(1+Real.exp X/3),by positivity,?_⟩
  intro V _ G w hw hCross
  obtain ⟨n,hn⟩ := exists_nat_ge (mass w (univ : Finset V))
  have hL : ∀ v, neighborMass G w v ≤ Real.exp (Numerical.scale X n) := by
    intro v
    calc
      _ ≤ mass w univ := mass_mono (fun v ↦ (hw v).le) (subset_univ _)
      _ ≤ n := hn
      _ ≤ Numerical.scale X n := by
        have hh := Numerical.scale_ge_add (by linarith : 2 ≤ X) n
        linarith
      _ ≤ Real.exp (Numerical.scale X n) := by linarith [Real.add_one_le_exp (Numerical.scale X n)]
  have ht := triangle_bound_scale hC hX hsmall n G w hw hCross hL
  have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
  have hB : 0 ≤ 1+Real.exp X/3 := by positivity
  have hq : 0 ≤ (1/2:ℝ)^n := by positivity
  nlinarith [mul_nonneg hB hq, mul_nonneg (mul_nonneg hB hq) he]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.IndependentSet =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

lemma exists_optimizer_triangle_bound (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      IsOptimizer G w → G.CliqueFree (k+2) → triangleMass G w ≤ B * edgeMass G w := by
  have hC : 1 ≤ 16*((k : ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨B,hB,hbound⟩ := weighted_triangles.{u} hC
  exact ⟨B,hB,fun G w hw hf ↦ hbound G w (fun v ↦ (optimizer_stationary hw v).1)
    (optimizer_cross_bound k G hw hf)⟩

lemma exists_cheap_vertex {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ B : ℝ} (hΔ : 3 ≤ Δ) (hB : 0 ≤ B)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (htri : triangleMass G w ≤ B * edgeMass G w) :
    ∃ v, mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w) ≤
      (3+3*B/2) * Real.log Δ := by
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hp (v : V) :
      w v * (mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w)) ≤
      w v + 2 * (w v * neighborMass G w v) + w v * triangleAt G w v / 2 := by
    rw [mass_closedNeighbors,edgeMass_closedNeighbors]
    have hv := (optimizer_stationary hw v).2.2
    have hN := neighborMass_nonneg G hw.1 v
    have hsq : w v * w v ≤ w v := by nlinarith [hw.1 v]
    have hmul := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  have hsum := sum_le_sum (s := univ) fun v _ ↦ hp v
  simp only [sum_add_distrib, ← mul_sum, ← sum_div] at hsum
  have he := edgeForm_self G w
  rw [edgeForm_neighbor] at he
  have ht : (∑ v, w v * triangleAt G w v) / 2 = 3*triangleMass G w := by
    unfold triangleMass
    ring
  rw [he,ht] at hsum
  have hedge := optimizer_edge_bound hw hΔ hdeg
  have hlog : 1 ≤ Real.log Δ := le_of_lt <| (Real.lt_log_iff_exp_lt (by linarith)).2
    (Real.exp_one_lt_three.trans_le hΔ)
  have hW : 0 ≤ ∑ v, w v := sum_nonneg (fun v _ ↦ hw.1 v)
  have htot : (∑ v, w v * (mass w (closedNeighbors G v) +
      edgeMass G (restrict (closedNeighbors G v) w))) ≤
        ((3+3*B/2)*Real.log Δ) * (∑ v, w v) := by
    have h1 := mul_le_mul_of_nonneg_right hlog hW
    have h2 := mul_le_mul_of_nonneg_left hedge (show 0 ≤ 2+3*B/2 by positivity)
    nlinarith
  by_contra h
  push Not at h
  have hlt (v : V) := mul_lt_mul_of_pos_left (h v) (hwpos v)
  have hh := sum_lt_sum (s := univ) (fun v _ ↦ (hlt v).le)
    ⟨Classical.arbitrary V, mem_univ _, hlt _⟩
  rw [← sum_mul] at hh
  linarith

lemma degree_induce_le (G : SimpleGraph V) (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (fun u : (G.induce (A : Set V)).neighborSet v ↦
      (⟨u.val.val, u.property⟩ : G.neighborSet v))
    (fun u z h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : G.neighborSet v ↦ (x : V)) h)

omit [Fintype V] in
lemma indepSet_image_induce (G : SimpleGraph V) (A : Finset V) (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set (A : Set V))) :
    G.IsIndepSet (I.map ⟨Subtype.val, Subtype.val_injective⟩ : Set V) := by
  classical
  intro a ha b hb hab
  obtain ⟨a',ha',rfl⟩ := mem_map.1 ha
  obtain ⟨b',hb',rfl⟩ := mem_map.1 hb
  exact hI ha' hb' (fun h ↦ hab (congrArg Subtype.val h))

omit [Fintype V] in
lemma indepSet_insert_induce (G : SimpleGraph V) (A : Finset V) (v : V)
    (hA : ∀ b ∈ A, b ≠ v ∧ ¬G.Adj v b)
    (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set _)) :
    G.IsIndepSet (↑(insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩) : Finset V) : Set V) ∧
      (insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩)).card = I.card + 1 := by
  classical
  have hnot (b : V) (hb : b ∈ I.map ⟨Subtype.val, Subtype.val_injective⟩) :
      b ≠ v ∧ ¬G.Adj v b := by
    obtain ⟨b',_,rfl⟩ := mem_map.1 hb
    exact hA b' b'.property
  have hi := indepSet_image_induce G A I hI
  constructor
  · intro a ha b hb hab
    change a ∈ insert v (I.map _) at ha
    change b ∈ insert v (I.map _) at hb
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact fun _ ↦ hab rfl
      · exact (hnot b hb).2
    · rcases hb with rfl | hb
      · exact fun h ↦ (hnot a ha).2 h.symm
      · exact hi ha hb hab
  · rw [card_insert_of_notMem (fun h ↦ (hnot v h).1 rfl), card_map]

/-- The maximum-degree induction controls the original variational functional,
not a surrogate objective or a conditional independence bound. -/
lemma maximum_degree_potential_bound (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
        potential G q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
  classical
  have aux : ∀ n : ℕ, ∀ (U : Type u) [Fintype U], Fintype.card U = n →
      ∀ H : SimpleGraph U, H.CliqueFree (k+2) → (∀ v, (H.degree v : ℝ) ≤ Δ) →
        ∃ I : Finset U, H.IsIndepSet (I : Set U) ∧
          ∀ q : U → ℝ, (∀ v, 0 ≤ q v) →
            potential H q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ hn H hfree hdegree
      rcases isEmpty_or_nonempty U with hU | hU
      · let _ := hU
        refine ⟨∅,by simp,?_⟩
        intro q _
        simp [potential,edgeMass,crossMass]
      · let _ := hU
        obtain ⟨w,hw⟩ := exists_optimizer H
        obtain ⟨v,hv⟩ := exists_cheap_vertex hw hΔ hB hdegree (htri H w hw hfree)
        let A : Finset U := (closedNeighbors H v)ᶜ
        have hA : ∀ b ∈ A, b ≠ v ∧ ¬H.Adj v b := by
          intro b hb
          simpa [A] using hb
        have hcard : Fintype.card (A : Set U) < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [A])
        have hfreeA : (H.induce (A : Set U)).CliqueFree (k+2) :=
          (H.cliqueFree_induce_iff _ _).2 hfree.cliqueFreeOn
        have hdegA (a : (A : Set U)) : ((H.induce (A : Set U)).degree a : ℝ) ≤ Δ :=
          (Nat.cast_le.2 (degree_induce_le H A a)).trans (hdegree a)
        obtain ⟨I,hI,hIp⟩ := ih _ hcard (A : Set U) rfl (H.induce (A : Set U)) hfreeA hdegA
        obtain ⟨hJ,hJcard⟩ := indepSet_insert_induce H A v hA I hI
        refine ⟨insert v (I.map ⟨Subtype.val,Subtype.val_injective⟩),hJ,?_⟩
        intro q hq
        have hres := hIp (fun a ↦ w a) (fun a ↦ hw.1 a)
        rw [potential_induce] at hres
        have hcost := optimizer_deletion_cost hw (closedNeighbors H v)
        change potential H w - potential H (restrict A w) = _ at hcost
        rw [hJcard,Nat.cast_add,Nat.cast_one]
        have hmax := hw.2 q hq
        nlinarith
  exact aux _ V rfl G hf hdeg

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.MaxDegree =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeIndependence.WeightedGraph


variable {V : Type u} [Fintype V]

lemma log_le_one_add_quarter {t : ℝ} (ht : 0 < t) : Real.log t ≤ 1+t/4 := by
  have h4 : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos ht (by norm_num : (0 : ℝ) < 4))
  rw [Real.log_div ht.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hh
  linarith

lemma neighborMass_const (G : SimpleGraph V) (p : ℝ) (v : V) :
    neighborMass G (fun _ ↦ p) v = (G.degree v : ℝ)*p := by
  simp only [neighborMass,mass,sum_const,nsmul_eq_mul,card_neighbors]

lemma edgeMass_const_le (G : SimpleGraph V) {Δ : ℝ}
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (p : ℝ) :
    edgeMass G (fun _ ↦ p) ≤ (Fintype.card V : ℝ)*Δ*p^2/2 := by
  have hs := sum_le_sum (s := univ) fun v _ ↦ mul_le_mul_of_nonneg_right (hdeg v) (sq_nonneg p)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have he := edgeForm_self G (fun _ ↦ p)
  rw [edgeForm_neighbor] at he
  simp only [neighborMass_const] at he
  have he' : (∑ u, p*((G.degree u : ℝ)*p)) = ∑ u, (G.degree u : ℝ)*p^2 := by
    apply sum_congr rfl
    intro u _
    ring
  rw [he'] at he
  nlinarith

lemma potential_const_lower (G : SimpleGraph V) {Δ : ℝ} (hΔ : 1 < Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ)*(Real.log Δ)^2/(4*Δ) ≤
      potential G (fun _ ↦ Real.log Δ / Δ) := by
  have hΔpos : 0 < Δ := lt_trans zero_lt_one hΔ
  have ht : 0 < Real.log Δ := Real.log_pos hΔ
  have hp : 0 < Real.log Δ / Δ := div_pos ht hΔpos
  have hlog := log_le_one_add_quarter ht
  have hhe : Δ*(Real.log Δ/Δ) = Real.log Δ := by field_simp
  have hterm : Real.log Δ/4 ≤ 1-Real.log (Real.log Δ/Δ)-Δ*(Real.log Δ/Δ)/2 := by
    rw [Real.log_div ht.ne' hΔpos.ne', hhe]
    linarith
  have hc : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hterm (mul_nonneg hc hp.le)
  have he := edgeMass_const_le G hdeg (Real.log Δ/Δ)
  simp only [potential,vertexPotential,sum_const,card_univ,nsmul_eq_mul]
  have heq : (Fintype.card V : ℝ)*(Real.log Δ)^2/(4*Δ) =
      (Fintype.card V : ℝ)*(Real.log Δ/Δ)*(Real.log Δ/4) := by ring
  rw [heq]
  nlinarith

/-- The quantitative maximum-degree independence bound. -/
lemma maximum_degree_independence (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ)*Real.log Δ/(4*(3+3*B/2)*Δ) ≤ (G.indepNum : ℝ) := by
  have hΔpos : 0 < Δ := by linarith
  have ht : 0 < Real.log Δ := Real.log_pos (by linarith)
  have hD : 0 < 3+3*B/2 := by positivity
  obtain ⟨I,hI,hIp⟩ := maximum_degree_potential_bound k hB hΔ htri G hf hdeg
  have hupper := hIp (fun _ ↦ Real.log Δ/Δ) (fun _ ↦ (div_pos ht hΔpos).le)
  have hlower := potential_const_lower G (by linarith : 1 < Δ) hdeg
  have hc : (I.card : ℝ) ≤ G.indepNum := Nat.cast_le.2 hI.card_le_indepNum
  have hfinal := hupper.trans (mul_le_mul_of_nonneg_left hc (mul_pos hD ht).le)
  have hbound := hlower.trans hfinal
  apply (mul_le_mul_iff_left₀ (mul_pos hD ht)).1
  convert hbound using 1 <;> field_simp

lemma indepNum_induce_le (G : SimpleGraph V) (A : Finset V) :
    (G.induce (A : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨I,hI⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  have h := (indepSet_image_induce G A I hI.isIndepSet).card_le_indepNum
  simpa only [card_map,hI.card_eq] using h

lemma degree_cutoff_card (G : SimpleGraph V) {d : ℝ} (hd : 0 < d)
    (hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ)*d) :
    (Fintype.card V : ℝ)/2 ≤ ((univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d).card : ℝ) := by
  classical
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d
  have hv (v : V) (h : v ∈ Aᶜ) : 2*d ≤ (G.degree v : ℝ) := by
    have hh : ¬(G.degree v : ℝ) ≤ 2*d := by simpa [A] using h
    exact le_of_lt (lt_of_not_ge hh)
  have hlow := sum_le_sum (s := Aᶜ) fun v h ↦ hv v h
  simp only [sum_const,nsmul_eq_mul] at hlow
  have hu : (∑ v ∈ Aᶜ, (G.degree v : ℝ)) ≤ ∑ v, (G.degree v : ℝ) := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hcard : (A.card : ℝ)+(Aᶜ.card : ℝ) = Fintype.card V := by
    exact_mod_cast card_add_card_compl A
  change (Fintype.card V : ℝ)/2 ≤ (A.card : ℝ)
  rw [hsum] at hu
  nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

end

-- ===== source module OAI.Combinatorics.CliqueFree.Main =====

section

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

open scoped Classical

namespace CliqueFreeLog
open CliqueFreeIndependence.WeightedGraph

lemma sum_degrees_real {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ v, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- The logarithmic independence bound for ordinary clique exclusion and the graph's own
average degree, with a constant uniform in graph size and average degree. -/
theorem logarithmic_independence_bound (r : ℕ) (hr : 4 ≤ r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        G.CliqueFree r → 2 ≤ averageDegree G →
        c * (Fintype.card V : ℝ) * Real.log (averageDegree G) / averageDegree G ≤
          (G.indepNum : ℝ) := by
  classical
  obtain ⟨B,hB,htri⟩ := exists_optimizer_triangle_bound.{0} (r-2)
  let D : ℝ := 3+3*B/2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1/(16*D),by positivity,?_⟩
  intro V _ G hf hd
  let d : ℝ := averageDegree G
  have hd2 : 2 ≤ d := hd
  have hdpos : 0 < d := by linarith
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    intro hn
    have hz : averageDegree G = 0 := by simp [averageDegree,hn]
    rw [hz] at hd
    norm_num at hd
  have hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ)*d := by
    rw [sum_degrees_real]
    dsimp [d, averageDegree]
    field_simp
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d
  have hAcard : (Fintype.card V : ℝ)/2 ≤ (Fintype.card (A : Set V) : ℝ) := by
    have he : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    rw [he]
    exact degree_cutoff_card G hdpos hsum
  have hk : r-2+2 = r := Nat.sub_add_cancel (by omega)
  have hfree : (G.induce (A : Set V)).CliqueFree (r-2+2) := by
    rw [hk]
    exact (G.cliqueFree_induce_iff _ _).2 hf.cliqueFreeOn
  have hdeg (v : (A : Set V)) : ((G.induce (A : Set V)).degree v : ℝ) ≤ 2*d := by
    have hv : (G.degree v : ℝ) ≤ 2*d := (mem_filter.1 v.property).2
    exact (Nat.cast_le.2 (degree_induce_le G A v)).trans hv
  have hmax := maximum_degree_independence (r-2) hB.le (by linarith : 3 ≤ 2*d)
    htri (G.induce (A : Set V)) hfree hdeg
  have hi : ((G.induce (A : Set V)).indepNum : ℝ) ≤ G.indepNum :=
    Nat.cast_le.2 (indepNum_induce_le G A)
  have hlog : Real.log d ≤ Real.log (2*d) :=
    Real.log_le_log hdpos (by linarith)
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hnum : (Fintype.card V : ℝ)*Real.log d/2 ≤
      (Fintype.card (A : Set V) : ℝ)*Real.log (2*d) := by
    have h1 := mul_le_mul_of_nonneg_right hAcard hlog0
    have h2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (Fintype.card (A : Set V)))
    nlinarith
  have hden : 0 < 8*D*d := by positivity
  have hcompare := div_le_div_of_nonneg_right hnum hden.le
  change (Fintype.card (A : Set V) : ℝ)*Real.log (2*d)/(4*D*(2*d)) ≤ _ at hmax
  have heq : (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d =
      ((Fintype.card V : ℝ)*Real.log d/2)/(8*D*d) := by
    field_simp
    ring
  change (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d ≤ _
  rw [heq]
  apply hcompare.trans
  have hdeneq : 8*D*d = 4*D*(2*d) := by ring
  rw [hdeneq]
  exact hmax.trans hi

end CliqueFreeLog

end

end OAI

end

-- ===== source module Bridge802 =====

section

/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

open scoped BigOperators
open Finset
open OAI.CliqueFreeIndependence.WeightedGraph

namespace Erdos802Bridge

open scoped Classical in
/-- The repository's rational average degree equals the release's real average degree. -/
theorem averageDegree_cast {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (G.averageDegree : ℝ) = OAI.CliqueFreeLog.averageDegree G := by
  classical
  simp only [SimpleGraph.averageDegree, OAI.CliqueFreeLog.averageDegree,
    Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  have hsum := OAI.CliqueFreeLog.sum_degrees_real G
  exact congrArg (fun x : ℝ => x / (Fintype.card V : ℝ)) hsum

/-- Extend the released theorem to every clique size and every average degree. -/
theorem all_degrees_bound (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.CliqueFree r →
      c * (Fintype.card V : ℝ) * Real.log (OAI.CliqueFreeLog.averageDegree G) /
        OAI.CliqueFreeLog.averageDegree G ≤ (G.indepNum : ℝ) := by
  classical
  let s := max r 4
  have hs : 4 ≤ s := Nat.le_max_right r 4
  have hsk : s - 2 + 2 = s := Nat.sub_add_cancel (by omega)
  obtain ⟨c₁, hc₁, hmain⟩ := OAI.CliqueFreeLog.logarithmic_independence_bound s hs
  obtain ⟨B, hB, htri⟩ := exists_optimizer_triangle_bound.{0} (s - 2)
  let D : ℝ := 3 + 3 * B / 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let c₂ : ℝ := Real.log 4 / (32 * D)
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  let c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨c, hc, ?_⟩
  intro V _ G hf
  have hfs : G.CliqueFree s := SimpleGraph.CliqueFree.mono (Nat.le_max_left r 4) hf
  let d := OAI.CliqueFreeLog.averageDegree G
  have hd0 : 0 ≤ d := by dsimp [d, OAI.CliqueFreeLog.averageDegree]; positivity
  change c * (Fintype.card V : ℝ) * Real.log d / d ≤ (G.indepNum : ℝ)
  by_cases hz : d = 0
  · simp [hz]
  have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hz)
  by_cases hd : 2 ≤ d
  · have hb := hmain G hfs hd
    have hfactor : 0 ≤ (Fintype.card V : ℝ) * Real.log d / d := by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) hd0
    calc
      c * (Fintype.card V : ℝ) * Real.log d / d =
          c * ((Fintype.card V : ℝ) * Real.log d / d) := by ring
      _ ≤ c₁ * ((Fintype.card V : ℝ) * Real.log d / d) :=
        mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hfactor
      _ = c₁ * (Fintype.card V : ℝ) * Real.log d / d := by ring
      _ ≤ (G.indepNum : ℝ) := hb
  have hdlt : d < 2 := lt_of_not_ge hd
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    intro he
    have : d = 0 := by simp [d, OAI.CliqueFreeLog.averageDegree, he]
    exact hz this
  have hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ) * d := by
    rw [OAI.CliqueFreeLog.sum_degrees_real]
    dsimp [d, OAI.CliqueFreeLog.averageDegree]
    field_simp
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2 * d
  have hAcard : (Fintype.card V : ℝ) / 2 ≤ (Fintype.card (A : Set V) : ℝ) := by
    have he : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    rw [he]
    exact degree_cutoff_card G hdpos hsum
  have hfree : (G.induce (A : Set V)).CliqueFree (s - 2 + 2) := by
    rw [hsk]
    exact (G.cliqueFree_induce_iff _ _).2 hfs.cliqueFreeOn
  have hdeg (v : (A : Set V)) : ((G.induce (A : Set V)).degree v : ℝ) ≤ 4 := by
    have hv : (G.degree v : ℝ) ≤ 2 * d := (mem_filter.mp v.property).2
    have hi := Nat.cast_le (α := ℝ).mpr (degree_induce_le G A v)
    linarith
  have hmax := maximum_degree_independence (s - 2) hB.le (by norm_num : (3 : ℝ) ≤ 4)
    htri (G.induce (A : Set V)) hfree hdeg
  have hi : ((G.induce (A : Set V)).indepNum : ℝ) ≤ (G.indepNum : ℝ) :=
    Nat.cast_le.mpr (indepNum_induce_le G A)
  have hden : 4 * (3 + 3 * B / 2) * 4 = 16 * D := by dsimp [D]; ring
  rw [hden] at hmax
  have hnum : (Fintype.card V : ℝ) * Real.log 4 / 2 ≤
      (Fintype.card (A : Set V) : ℝ) * Real.log 4 := by
    have hh := mul_le_mul_of_nonneg_right hAcard hlog4.le
    nlinarith
  have hquot := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ 16 * D)
  have hstrong : c₂ * (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) := by
    calc
      c₂ * (Fintype.card V : ℝ) =
          ((Fintype.card V : ℝ) * Real.log 4 / 2) / (16 * D) := by
        dsimp [c₂]
        field_simp
        ring
      _ ≤ (Fintype.card (A : Set V) : ℝ) * Real.log 4 / (16 * D) := hquot
      _ ≤ (G.indepNum : ℝ) := hmax.trans hi
  have hratio : Real.log d / d ≤ 1 := by
    apply (div_le_one hdpos).mpr
    have hh := Real.log_le_sub_one_of_pos hdpos
    linarith
  calc
    c * (Fintype.card V : ℝ) * Real.log d / d =
        (c * (Fintype.card V : ℝ)) * (Real.log d / d) := by ring
    _ ≤ c * (Fintype.card V : ℝ) :=
      mul_le_of_le_one_right (mul_nonneg hc.le (Nat.cast_nonneg _)) hratio
    _ ≤ c₂ * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (Nat.cast_nonneg _)
    _ ≤ (G.indepNum : ℝ) := hstrong

open scoped Classical in
/-- The exact original repository statement, without restrictions on clique size or degree. -/
theorem erdos_802 : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (Real.log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  classical
  intro r
  obtain ⟨c, hc, hb⟩ := all_degrees_bound r
  refine ⟨c, hc, ?_⟩
  intro n G hf
  have hh := hb G hf
  rw [← averageDegree_cast] at hh
  simpa only [Fintype.card_fin, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh

end Erdos802Bridge

end

theorem OMA.solution : type_of% @Erdos802.erdos_802 :=
  Erdos802Bridge.erdos_802
