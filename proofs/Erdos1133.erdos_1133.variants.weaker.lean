import FormalConjectures.ErdosProblems.«1133»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! # Discretizing and norming polynomial obstructions in Erdős 1133 -/

namespace OMA.R_Erdos1133_erdos_1133_variants_weaker_R1

open Filter Set Polynomial

-- Uniform sampling estimate on the cubic mesh, independent of the chosen nodes.
def H1 : Prop :=
  ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ x ∈ Icc (-1 : ℝ) 1, ∃ k ≤ n^3, ∀ P : Polynomial ℝ,
      P.natDegree ≤ n → (∀ j ≤ n^3, |P.eval (g j)| ≤ K) →
      |P.eval x - P.eval (g k)| ≤ 1

-- All sample and peak indices now belong to one finite rational grid.
def H2 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    let m := ⌊(1 + ε) * (n : ℝ)⌋₊
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ a : Fin m → ℕ, (∀ i, a i ≤ n^3) →
      ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧
        (∀ i, |P.eval (g (a i))| ≤ 1) ∧
        (∀ j ≤ n^3, |P.eval (g j)| ≤ 4 * (A + 1)) ∧
        ∃ j ≤ n^3, 2 * A < |P.eval (g j)|

lemma exact_degree_of_peaking {n m : ℕ} {C : ℝ} (hC : 0 < C)
    (x : Fin m → Icc (-1 : ℝ) 1) (P : Polynomial ℝ) (hd : P.natDegree ≤ n)
    (hnodes : ∀ i, |P.eval (x i : ℝ)| ≤ 1) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hpeak : C < |P.eval z|) :
    ∃ Q : Polynomial ℝ, Q.natDegree = n ∧ (∀ i, |Q.eval (x i : ℝ)| ≤ 1) ∧
      C < |Q.eval z| := by
  rcases hd.eq_or_lt with heq | hlt
  · exact ⟨P, heq, hnodes, hpeak⟩
  let A := |P.eval z|
  have hA : 0 < A := hC.trans hpeak
  have hdpos : 0 < 2 * (A + 1) := by positivity
  let t := (A - C) / (2 * (A + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hpeak) hdpos
  have ht1 : t < 1 := by
    apply (div_lt_iff₀ hdpos).mpr
    linarith
  have hgap : t * (2 * (A + 1)) = A - C := div_mul_cancel₀ _ hdpos.ne'
  let Q := Polynomial.C (1-t) * P + Polynomial.C t * (X : Polynomial ℝ)^n
  have hmon : (Polynomial.C t * (X : Polynomial ℝ)^n).natDegree = n :=
    natDegree_C_mul_X_pow n t ht.ne'
  have hQ : Q.natDegree = n := by
    apply (natDegree_add_eq_right_of_natDegree_lt _).trans hmon
    rw [hmon]
    exact (natDegree_C_mul_le _ _).trans_lt hlt
  have heval (v : ℝ) : Q.eval v = (1-t) * P.eval v + t * v^n := by simp [Q]
  have hpow {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |v^n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hv)
  have hbound {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |t * v^n| ≤ t := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_of_le_one_right ht.le (hpow hv)
  refine ⟨Q,hQ,?_,?_⟩
  · intro i
    rw [heval]
    calc
      _ ≤ |(1-t) * P.eval (x i : ℝ)| + |t * (x i : ℝ)^n| := abs_add_le _ _
      _ ≤ (1-t) + t := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)]
        exact add_le_add (mul_le_of_le_one_right (sub_nonneg.mpr ht1.le) (hnodes i)) (hbound (x i).property)
      _ = 1 := by ring
  · have he : |(1-t) * P.eval z| ≤ |Q.eval z| + |t * z^n| := by
      simpa only [heval, add_sub_cancel_right] using
        (abs_sub ((1-t) * P.eval z + t * z^n) (t * z^n))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)] at he
    change (1-t) * A ≤ |Q.eval z| + |t * z^n| at he
    nlinarith [hbound hz]


theorem main : H1 → H2 → type_of% @Erdos1133.erdos_1133.variants.weaker := by
  intro h1 h2 A hA
  obtain ⟨ε, hε, hfinite⟩ := h2 A hA
  refine ⟨ε, hε, ?_⟩
  have hmesh := h1 (4 * (A + 1)) (by positivity)
  filter_upwards [hfinite, hmesh, Filter.eventually_ge_atTop 1] with n hn hnear hnpos
  let m := ⌊(1 + ε) * (n : ℝ)⌋₊
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  dsimp only at ⊢
  intro x
  have hchoice (i : Fin m) := hnear (x i : ℝ) (x i).property
  choose a ha happrox using hchoice
  obtain ⟨P, hdeg, hsample, hgrid, j, hj, hpeak⟩ := hn a ha
  let Q := Polynomial.C (1 / 2 : ℝ) * P
  have hevalQ (v : ℝ) : Q.eval v = (1 / 2 : ℝ) * P.eval v := by simp [Q]
  have hnodes (i : Fin m) : |Q.eval (x i : ℝ)| ≤ 1 := by
    have he := happrox i P hdeg hgrid
    have he2 : |P.eval (x i : ℝ)| ≤ |P.eval (x i : ℝ) - P.eval (g (a i))| + |P.eval (g (a i))| := by
      simpa only [sub_add_cancel] using abs_add_le (P.eval (x i : ℝ) - P.eval (g (a i))) (P.eval (g (a i)))
    rw [hevalQ, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith [hsample i]
  have hjreal : (j : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast hj
  have hden : (0 : ℝ) < (n : ℝ)^3 := by positivity
  have hz : g j ∈ Icc (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · dsimp [g]; linarith [div_nonneg (by positivity : 0 ≤ 2 * (j : ℝ)) hden.le]
    · dsimp [g]
      have : 2 * (j : ℝ) / (n : ℝ)^3 ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
      linarith
  have hlarge : A < |Q.eval (g j)| := by
    rw [hevalQ, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith
  obtain ⟨R, hd, hR, hRpeak⟩ := exact_degree_of_peaking hA x Q ((natDegree_C_mul_le _ _).trans hdeg) hnodes hz hlarge
  exact ⟨R, hd, hR, g j, hz, hRpeak⟩

end OMA.R_Erdos1133_erdos_1133_variants_weaker_R1

section
namespace OMA.Mesh1133

open Polynomial

lemma interval_derivative_bound (P : Polynomial ℝ) (n : ℕ) (hP : P.natDegree ≤ n)
    (M : ℝ) (hM : 0 < M) (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |P.eval u| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |P.derivative.eval x| ≤ 2 * (n : ℝ)^2 * M := by
  let a : ℝ := if 0 ≤ x then 1/2 else -(1/2)
  have ha : |a| = 1/2 := by dsimp [a]; split <;> norm_num
  let L : Polynomial ℝ := C a * X + C (x - a)
  have hL1 : L.eval 1 = x := by simp [L]
  have hL (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : L.eval u ∈ Set.Icc (-1 : ℝ) 1 := by
    have hxlo := hx.1
    have hxhi := hx.2
    have hulo := hu.1
    have huhi := hu.2
    simp only [L, eval_add, eval_mul, eval_C, eval_X, Set.mem_Icc]
    dsimp [a]
    split <;> constructor <;> linarith
  let Q : Polynomial ℝ := C M⁻¹ * P.comp L
  have hbQ (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : |Q.eval u| ≤ 1 := by
    simp only [Q, eval_mul, eval_C, eval_comp, abs_mul, abs_inv, abs_of_pos hM]
    calc
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hb _ (hL u hu)) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hLd : L.natDegree ≤ 1 := by
    rw [show L = C a * X + C (x-a) from rfl, natDegree_add_C]
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hQd : Q.degree ≤ n := by
    apply degree_le_of_natDegree_le
    exact (natDegree_C_mul_le _ _).trans
      (natDegree_comp_le.trans ((Nat.mul_le_mul hP hLd).trans_eq (Nat.mul_one n)))
  have upper (F : Polynomial ℝ) (hd : F.degree ≤ n)
      (hF : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |F.eval u| ≤ 1) :
      F.derivative.eval 1 ≤ (n : ℝ)^2 := by
    simpa [Polynomial.Chebyshev.derivative_T_eval_one] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1) le_rfl hd hF)
  have hplus := upper Q hQd hbQ
  have hminus := upper (-Q) (by simpa using hQd) (fun u hu => by simpa using hbQ u hu)
  have habs : |Q.derivative.eval 1| ≤ (n : ℝ)^2 := by
    apply abs_le.mpr
    exact ⟨by simpa using (neg_le_neg hminus), hplus⟩
  have he : Q.derivative.eval 1 = M⁻¹ * (a * P.derivative.eval x) := by
    simp [Q, derivative_C_mul, derivative_comp, eval_comp, hL1,
      show L.derivative = C a by simp [L, derivative_C_mul_X]]
  rw [he, abs_mul, abs_mul, abs_inv, abs_of_pos hM, ha, ← div_eq_inv_mul] at habs
  have h := (div_le_iff₀ hM).mp habs
  linarith

open Set Polynomial Filter

lemma mesh_round {n : ℕ} (hn : 0 < n) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∃ k ≤ n^3, g k ∈ Icc (-1 : ℝ) 1 ∧ |u - g k| ≤ 2 / (n : ℝ)^3 := by
  dsimp only
  let d := (n : ℝ)^3
  have hd : 0 < d := by dsimp [d]; positivity
  let w := (u + 1) * d / 2
  have hw : 0 ≤ w := by dsimp [w]; exact div_nonneg (mul_nonneg (by linarith [hu.1]) hd.le) (by norm_num)
  let k := ⌊w⌋₊
  have hlo : (k : ℝ) ≤ w := Nat.floor_le hw
  have hhi : w < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hw' : w ≤ d := by dsimp [w]; nlinarith [mul_le_mul_of_nonneg_right hu.2 hd.le]
  have hk' : (k : ℝ) ≤ d := hlo.trans hw'
  have hk : k ≤ n^3 := by dsimp [d] at hk'; exact_mod_cast hk'
  refine ⟨k,hk,?_,?_⟩
  · constructor
    · change -1 ≤ 2 * (k : ℝ) / d - 1
      linarith [div_nonneg (by positivity : (0 : ℝ) ≤ 2 * k) hd.le]
    · change 2 * (k : ℝ) / d - 1 ≤ 1
      linarith [(div_le_iff₀ hd).mpr (show 2 * (k : ℝ) ≤ 2 * d by linarith)]
  · change |u - (2 * (k : ℝ) / d - 1)| ≤ 2 / d
    have hpos : 2 * (k : ℝ) / d ≤ u+1 := (div_le_iff₀ hd).mpr (by dsimp [w] at hlo; linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ u - (2 * (k : ℝ) / d - 1))]
    apply (le_div_iff₀ hd).mpr
    have hc := div_mul_cancel₀ (2 * (k : ℝ)) hd.ne'
    dsimp [w] at hhi
    nlinarith

lemma mesh_estimate
    (hMarkov : ∀ (P : Polynomial ℝ) (n : ℕ), P.natDegree ≤ n →
      ∀ M > (0 : ℝ), (∀ u ∈ Icc (-1 : ℝ) 1, |P.eval u| ≤ M) →
        ∀ u ∈ Icc (-1 : ℝ) 1, |P.derivative.eval u| ≤ 2 * (n : ℝ)^2 * M) :
  ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ x ∈ Icc (-1 : ℝ) 1, ∃ k ≤ n^3, ∀ P : Polynomial ℝ,
      P.natDegree ≤ n → (∀ j ≤ n^3, |P.eval (g j)| ≤ K) →
      |P.eval x - P.eval (g k)| ≤ 1 := by
  intro K hK
  filter_upwards [Filter.eventually_ge_atTop ⌈8*(K+1)⌉₊] with n hn
  have hn' : 8*(K+1) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn8 : (8 : ℝ) ≤ n := by linarith
  have hnr : (0 : ℝ) < n := by linarith
  have hnpos : 0 < n := by exact_mod_cast hnr
  dsimp only
  intro x hx
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  obtain ⟨k,hk,hg,hxnear⟩ := mesh_round hnpos x hx
  refine ⟨k, hk, ?_⟩
  intro P hP hgrid
  obtain ⟨s,hs,hmax⟩ : ∃ s : ℝ, s ∈ Icc (-1 : ℝ) 1 ∧
      IsMaxOn (fun t => |P.eval t|) (Icc (-1 : ℝ) 1) s :=
    isCompact_Icc.exists_isMaxOn ⟨0, by constructor <;> norm_num⟩
      (continuous_abs.comp P.continuous).continuousOn
  let M := |P.eval s| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : |P.eval u| ≤ M := by
    dsimp [M]; linarith [show |P.eval u| ≤ |P.eval s| from hmax hu]
  have hlocal (u v : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
      (hd : |u-v| ≤ 2/(n:ℝ)^3) : |P.eval u - P.eval v| ≤ 4*M/(n:ℝ) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z (_ : z ∈ Icc (-1 : ℝ) 1) => P.differentiableAt)
      (fun z hz => by rw [P.deriv, Real.norm_eq_abs]; exact hMarkov P n hP M hM hbound z hz)
      (convex_Icc _ _) hv hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    apply h.trans
    calc
      _ ≤ (2*(n:ℝ)^2*M) * (2/(n:ℝ)^3) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp; ring
  obtain ⟨j,hj,hgj,hclose⟩ := mesh_round hnpos s hs
  have h1 := hlocal s (g j) hs hgj hclose
  have h2 : |P.eval s| ≤ |P.eval s - P.eval (g j)| + |P.eval (g j)| := by
    simpa only [sub_add_cancel] using abs_add_le (P.eval s - P.eval (g j)) (P.eval (g j))
  have h3 : 4*M/(n:ℝ) ≤ M/2 := (div_le_iff₀ hnr).mpr (by nlinarith [mul_le_mul_of_nonneg_left hn8 hM.le])
  have h4 : M ≤ 2*(K+1) := by
    have hnob := hgrid j hj
    change |P.eval (g j)| ≤ K at hnob
    change |P.eval s| + 1 ≤ 2*(K+1)
    change 4*M/(n:ℝ) ≤ (|P.eval s| + 1)/2 at h3
    linarith
  apply (hlocal x (g k) hx hg hxnear).trans
  exact (div_le_iff₀ hnr).mpr (by linarith)

end OMA.Mesh1133

private theorem h1_proof : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H1 :=
  OMA.Mesh1133.mesh_estimate OMA.Mesh1133.interval_derivative_bound
end

section
open Filter Set Polynomial
namespace OMA.MeshPeak1133

lemma grid_obstruction_of_continuous
    (hmesh : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H1)
    (hw : type_of% @Erdos1133.erdos_1133.variants.weaker) :
    OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H2 := by
  intro A hA
  let K := 3 * (A + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨ε, hε, hweak⟩ := hw K hK
  refine ⟨ε,hε,?_⟩
  filter_upwards [hweak, hmesh K hK, Filter.eventually_ge_atTop 1] with n hweak hnear hpos
  let m := ⌊(1 + ε) * (n : ℝ)⌋₊
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  have hgridmem (j : ℕ) (hj : j ≤ n^3) : g j ∈ Icc (-1 : ℝ) 1 := by
    have hjreal : (j : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast hj
    have hden : (0 : ℝ) < (n : ℝ)^3 := by positivity
    constructor
    · dsimp [g]; linarith [div_nonneg (by positivity : 0 ≤ 2 * (j : ℝ)) hden.le]
    · dsimp [g]
      have : 2 * (j : ℝ) / (n : ℝ)^3 ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
      linarith
  dsimp only
  intro a ha
  let x : Fin m → Icc (-1 : ℝ) 1 := fun i => ⟨g (a i), hgridmem _ (ha i)⟩
  obtain ⟨P,hd,hnodes,z,hz,hpz⟩ := hweak x
  obtain ⟨s,hs,hmax⟩ : ∃ s : ℝ, s ∈ Icc (-1 : ℝ) 1 ∧
      IsMaxOn (fun t => |P.eval t|) (Icc (-1 : ℝ) 1) s :=
    isCompact_Icc.exists_isMaxOn ⟨0, by constructor <;> norm_num⟩
      (continuous_abs.comp P.continuous).continuousOn
  let M := |P.eval s|
  have hKM : K < M := hpz.trans_le (hmax hz)
  have hM : 0 < M := hK.trans hKM
  let t := K/M
  have ht : 0 < t := div_pos hK hM
  have ht1 : t ≤ 1 := (div_le_one hM).mpr hKM.le
  let R := Polynomial.C t * P
  have hRdeg : R.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hd.le
  have he (u : ℝ) : |R.eval u| = t * |P.eval u| := by simp [R, abs_mul, abs_of_nonneg ht.le]
  have hRgrid (j : ℕ) (hj : j ≤ n^3) : |R.eval (g j)| ≤ K := by
    rw [he]
    calc
      _ ≤ t * M := mul_le_mul_of_nonneg_left (hmax (hgridmem j hj)) ht.le
      _ = K := div_mul_cancel₀ _ hM.ne'
  have hRs : |R.eval s| = K := by rw [he]; exact div_mul_cancel₀ _ hM.ne'
  refine ⟨R,hRdeg,?_,?_,?_⟩
  · intro i
    rw [he]
    exact (mul_le_of_le_one_right ht.le (hnodes i)).trans ht1
  · intro j hj
    exact (hRgrid j hj).trans (by dsimp [K]; linarith)
  · obtain ⟨j,hj,hg⟩ := hnear s hs
    refine ⟨j,hj,?_⟩
    have hdif := hg R hRdeg hRgrid
    have hab : |R.eval s| ≤ |R.eval s - R.eval (g j)| + |R.eval (g j)| := by
      simpa only [sub_add_cancel] using abs_add_le (R.eval s - R.eval (g j)) (R.eval (g j))
    change |R.eval s - R.eval (g j)| ≤ 1 at hdif
    change 2*A < |R.eval (g j)|
    dsimp [K] at hRs
    linarith
end OMA.MeshPeak1133

namespace OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1

open Filter Polynomial Real Set
open Polynomial.Chebyshev

def H1 : Prop :=
  ∀ K > (0 : ℝ), ∃ η > (0 : ℝ), ∃ D : ℕ, ∀ d ≥ D,
    ∀ Y : Finset ℝ, (Y.card : ℝ) ≤ (1+η)*d →
      ∃ A B : Polynomial ℝ, A.natDegree ≤ d ∧ B.natDegree < d ∧
        let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
        (∀ s ∈ Y, |q s| ≤ 1 ∧ |q (-s)| ≤ 1) ∧
          ∃ t ∈ Icc (0 : ℝ) π, K < |q t| ∧ ∀ s, |q s| ≤ |q t|

def H2 : Prop :=
  ∀ (d : ℕ) (A B : Polynomial ℝ), A.natDegree ≤ d → B.natDegree < d →
    let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
    ∀ M : ℝ, (∀ s, |q s| ≤ M) →
      ∀ s u : ℝ, |q s - q u| ≤ d*M*|s-u|

lemma interior_multiplier {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ π - a) :
    ∃ r : ℕ, 0 < r ∧ r ≤ 1 + ⌈(π/6) / a⌉₊ ∧
      1/2 ≤ |sin ((r : ℝ) * t)| := by
  let u := min t (π-t)
  have hmin : a ≤ u := le_min hat (by linarith)
  have hu : 0 < u := ha.trans_le hmin
  have hu' : u ≤ π/2 := by dsimp [u]; rcases le_total t (π-t) with h | h <;> simp [h] <;> linarith
  have he (j : ℕ) : |sin ((j : ℝ) * u)| = |sin ((j : ℝ) * t)| := by
    dsimp [u]
    rcases le_total t (π-t) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, mul_sub, sin_nat_mul_pi_sub, abs_neg, abs_mul, abs_pow]
      simp
  by_cases h : π/6 ≤ u
  · refine ⟨1, by decide, by omega, ?_⟩
    rw [← he]
    calc (1 / 2 : ℝ) = sin (π/6) := sin_pi_div_six.symm
      _ ≤ sin u := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hu' h
      _ ≤ _ := by simpa using (le_abs_self (sin u))
  · let r := ⌈(π/6)/u⌉₊
    have hd : 0 < (π/6)/u := by positivity
    have hr : 0 < r := Nat.ceil_pos.mpr hd
    have hlow : π/6 ≤ (r:ℝ)*u := (div_le_iff₀ hu).mp (Nat.le_ceil _)
    have hh : (r:ℝ) < (π/6)/u + 1 := Nat.ceil_lt_add_one hd.le
    have hupp : (r:ℝ)*u ≤ π/2 := by
      have hh' := mul_lt_mul_of_pos_right hh hu
      rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at hh'
      linarith [pi_pos]
    have hr' : r ≤ ⌈(π/6) / a⌉₊ := Nat.ceil_le_ceil (div_le_div_of_nonneg_left
      (by positivity) ha hmin)
    refine ⟨r, hr, by omega, ?_⟩
    rw [← he]
    calc (1 / 2 : ℝ) = sin (π/6) := sin_pi_div_six.symm
      _ ≤ sin ((r:ℝ)*u) := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hupp hlow
      _ ≤ _ := le_abs_self _

lemma transfer_peak {m d n : ℕ} {x : Fin m → Icc (-1 : ℝ) 1} {C a t : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ π-a)
    (hdeg : d + (1 + ⌈(π/6)/a⌉₊) ≤ n)
    (A B : Polynomial ℝ) (hA : A.natDegree ≤ d) (hB : B.natDegree < d)
    (hplus : ∀ i, |A.eval (x i : ℝ) + sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1)
    (hminus : ∀ i, |A.eval (x i : ℝ) - sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1)
    (hpeak : 4*C < |A.eval (cos t) + sin t * B.eval (cos t)|) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧ (∀ i, |P.eval (x i : ℝ)| ≤ 1) ∧
      ∃ z ∈ Icc (-1 : ℝ) 1, C < |P.eval z| := by
  have hsample (i : Fin m) : |A.eval (x i : ℝ)| ≤ 1 ∧ |sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1 := by
    have hp := abs_le.mp (hplus i)
    have hm := abs_le.mp (hminus i)
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  by_cases hv : C < |A.eval (cos t)|
  · exact ⟨A, by omega, fun i => (hsample i).1, cos t, ⟨neg_one_le_cos _,cos_le_one _⟩, hv⟩
  have hb : 2*C < |sin t * B.eval (cos t)| := by
    linarith [abs_add_le (A.eval (cos t)) (sin t * B.eval (cos t))]
  obtain ⟨r, hr, hr', hs⟩ := interior_multiplier ha hat hta
  cases r with
  | zero => omega
  | succ k =>
    let P : Polynomial ℝ := (1 - X^2) * U ℝ (k:ℤ) * B
    have ev (s : ℝ) : P.eval (cos s) =
        sin (((k:ℝ)+1)*s) * (sin s * B.eval (cos s)) := by
      simp only [P, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
      have hh := U_real_cos s (k : ℤ)
      push_cast at hh
      rw [← hh]
      nlinarith only [congrArg (fun v : ℝ => v * (U ℝ (k:ℤ)).eval (cos s) * B.eval (cos s)) (sin_sq_add_cos_sq s)]
    have d₀ : (1 - (X:Polynomial ℝ)^2).natDegree ≤ 2 := by
      apply (natDegree_sub_le ..).trans
      simp
    have d₁ := natDegree_mul_le (p := 1 - (X:Polynomial ℝ)^2) (q := U ℝ (k:ℤ))
    rw [natDegree_U_natCast] at d₁
    have d₂ := natDegree_mul_le (p := (1 - (X:Polynomial ℝ)^2) * U ℝ (k:ℤ)) (q := B)
    refine ⟨P, by dsimp [P]; omega, ?_, cos t, ⟨neg_one_le_cos _,cos_le_one _⟩, ?_⟩
    · intro i
      have e := ev (arccos (x i))
      rw [cos_arccos (x i).2.1 (x i).2.2] at e
      rw [e, abs_mul]
      exact mul_le_one₀ (abs_sin_le_one _) (abs_nonneg _) (hsample i).2
    · rw [ev, abs_mul]
      push_cast at hs
      have les := mul_le_mul_of_nonneg_right hs (abs_nonneg (sin t * B.eval (cos t)))
      linarith

lemma guard_mesh {a s L : ℝ} (hL : 0 < L) (hs : 0 ≤ s) (hsa : s ≤ a) :
    ∃ j : ℕ, j ≤ ⌈L*a⌉₊ ∧ |s - (j:ℝ)/L| ≤ 1/L := by
  let j := ⌊L*s⌋₊
  have hj : (j : ℝ) ≤ L*s := Nat.floor_le (mul_nonneg hL.le hs)
  have hj' : L*s < (j:ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · exact_mod_cast (hj.trans ((mul_le_mul_of_nonneg_left hsa hL.le).trans (Nat.le_ceil _)))
  · rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hL).mpr (by linarith)))]
    apply (le_div_iff₀ hL).mpr
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
    linarith

lemma guard_peak {n : ℕ} {a t M : ℝ} (hn : 0 < n)
    (ht : t ∈ Icc 0 π) (hM : 2 < M) (q : ℝ → ℝ)
    (hq : |q t| = M)
    (hLip : ∀ x y : ℝ, |q x - q y| ≤ (n:ℝ)*M*|x-y|)
    (hG : ∀ j : ℕ, j ≤ ⌈8*(n:ℝ)*a⌉₊ →
        |q ((j:ℝ)/(8*n))| ≤ 1 ∧ |q (π-(j:ℝ)/(8*n))| ≤ 1) :
    a ≤ t ∧ t ≤ π-a := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hL : (0:ℝ) < 8*n := by positivity
  have far (y : ℝ) (hy : |q y| ≤ 1) : 1/(8*(n:ℝ)) < |t-y| := by
    by_contra! h
    have hb : (n:ℝ)*M*|t-y| ≤ (n:ℝ)*M*(1/(8*(n:ℝ))) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg hn'.le (by linarith))
    have he : (n:ℝ)*M*(1/(8*(n:ℝ))) = M/8 := by field_simp
    rw [he] at hb
    have ht' : |q t| ≤ |q t-q y|+|q y| := by simpa using abs_add_le (q t-q y) (q y)
    have hxy := hLip t y
    linarith
  constructor
  · by_contra! ht'
    obtain ⟨j,hj,h⟩ := guard_mesh hL ht.1 ht'.le
    exact (far _ (hG j hj).1).not_ge h
  · by_contra! ht'
    have hsa : π-t ≤ a := by linarith
    obtain ⟨j,hj,h⟩ := guard_mesh hL (sub_nonneg.mpr ht.2) hsa
    have f := far _ (hG j hj).2
    rw [show t-(π-(j:ℝ)/(8*n)) = -(π-t-(j:ℝ)/(8*n)) by ring, abs_neg] at f
    exact f.not_ge h

lemma exact_degree_of_peaking {n m : ℕ} {C : ℝ} (hC : 0 < C)
    (x : Fin m → Icc (-1 : ℝ) 1) (P : Polynomial ℝ) (hd : P.natDegree ≤ n)
    (hnodes : ∀ i, |P.eval (x i : ℝ)| ≤ 1) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hpeak : C < |P.eval z|) :
    ∃ Q : Polynomial ℝ, Q.natDegree = n ∧ (∀ i, |Q.eval (x i : ℝ)| ≤ 1) ∧
      C < |Q.eval z| := by
  rcases hd.eq_or_lt with heq | hlt
  · exact ⟨P, heq, hnodes, hpeak⟩
  let A := |P.eval z|
  have hA : 0 < A := hC.trans hpeak
  have hdpos : 0 < 2 * (A + 1) := by positivity
  let t := (A - C) / (2 * (A + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hpeak) hdpos
  have ht1 : t < 1 := by
    apply (div_lt_iff₀ hdpos).mpr
    linarith
  have hgap : t * (2 * (A + 1)) = A - C := div_mul_cancel₀ _ hdpos.ne'
  let Q := Polynomial.C (1-t) * P + Polynomial.C t * (X : Polynomial ℝ)^n
  have hmon : (Polynomial.C t * (X : Polynomial ℝ)^n).natDegree = n :=
    natDegree_C_mul_X_pow n t ht.ne'
  have hQ : Q.natDegree = n := by
    apply (natDegree_add_eq_right_of_natDegree_lt _).trans hmon
    rw [hmon]
    exact (natDegree_C_mul_le _ _).trans_lt hlt
  have heval (v : ℝ) : Q.eval v = (1-t) * P.eval v + t * v^n := by simp [Q]
  have hpow {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |v^n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hv)
  have hbound {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |t * v^n| ≤ t := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_of_le_one_right ht.le (hpow hv)
  refine ⟨Q,hQ,?_,?_⟩
  · intro i
    rw [heval]
    calc
      _ ≤ |(1-t) * P.eval (x i : ℝ)| + |t * (x i : ℝ)^n| := abs_add_le _ _
      _ ≤ (1-t) + t := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)]
        exact add_le_add (mul_le_of_le_one_right (sub_nonneg.mpr ht1.le) (hnodes i)) (hbound (x i).property)
      _ = 1 := by ring
  · have he : |(1-t) * P.eval z| ≤ |Q.eval z| + |t * z^n| := by
      simpa only [heval, add_sub_cancel_right] using
        (abs_sub ((1-t) * P.eval z + t * z^n) (t * z^n))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)] at he
    change (1-t) * A ≤ |Q.eval z| + |t * z^n| at he
    nlinarith [hbound hz]


lemma continuous_peak : H1 → H2 → type_of% @Erdos1133.erdos_1133.variants.weaker := by
  classical
  intro sample bern C hC
  obtain ⟨η, hη, D, hsamp⟩ := sample (4*C+2) (by positivity)
  let a := η/128
  have ha : 0 < a := by dsimp [a]; positivity
  let R := 1+⌈(π/6)/a⌉₊
  let N := ⌈(4+(1+η)*(R:ℝ))/(η/2)⌉₊
  refine ⟨η/4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (D+R+N+1)] with n hn
  let m := ⌊(1+η/4)*(n:ℝ)⌋₊
  change ∀ x : Fin m → Icc (-1 : ℝ) 1, _
  intro x
  let d := n-R
  have hdN : D ≤ d := by dsimp [d]; omega
  have hdR : d+R = n := by dsimp [d]; omega
  have hdR' : (d:ℝ)+(R:ℝ)=(n:ℝ) := by exact_mod_cast hdR
  have hn' : 0 < n := by omega
  let J := ⌈8*(n:ℝ)*a⌉₊
  let I := Finset.range (J+1)
  let L := fun j : ℕ => (j:ℝ)/(8*(n:ℝ))
  let Y := ((Finset.univ : Finset (Fin m)).image fun i => arccos (x i)) ∪
      (I.image L ∪ I.image (fun j => π-L j))
  have cardY : Y.card ≤ m + 2*(J+1) := by
    have h₀ := Finset.card_image_le (f := fun i : Fin m => arccos (x i)) (s := Finset.univ)
    have h₁ := Finset.card_image_le (f := L) (s := I)
    have h₂ := Finset.card_image_le (f := fun j => π-L j) (s := I)
    have h₃ := Finset.card_union_le (I.image L) (I.image (fun j => π-L j))
    have h₄ := Finset.card_union_le ((Finset.univ : Finset (Fin m)).image fun i => arccos (x i))
      (I.image L ∪ I.image (fun j => π-L j))
    have hI : I.card = J+1 := Finset.card_range _
    simp only [Finset.card_univ, Fintype.card_fin] at h₀
    dsimp only [Y]
    omega
  have hY : (Y.card : ℝ) ≤ (1+η)*d := by
    have hJ : (J:ℝ) < 8*(n:ℝ)*a+1 := Nat.ceil_lt_add_one (by positivity)
    have hm : (m:ℝ) ≤ (1+η/4)*(n:ℝ) := Nat.floor_le (by positivity)
    have hN : (4+(1+η)*(R:ℝ))/(η/2) ≤ (n:ℝ) := by
      apply (Nat.le_ceil _).trans
      exact_mod_cast (show N ≤ n by omega)
    have hnR := (div_le_iff₀ (show 0 < η/2 by positivity)).mp hN
    have hc : (Y.card:ℝ) ≤ (m:ℝ)+2*((J:ℝ)+1) := by exact_mod_cast cardY
    dsimp only [a] at hJ
    rw [← hdR'] at hnR hJ hm
    nlinarith [mul_nonneg hη.le (Nat.cast_nonneg d),
      mul_nonneg hη.le (Nat.cast_nonneg R)]
  obtain ⟨A,B,hA,hB,hS,t,ht,hM,hglobal⟩ := hsamp d hdN Y hY
  let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
  have hLip := bern d A B hA hB |q t| hglobal
  have hM' : 2 < |q t| := by change 4*C+2 < |q t| at hM; linarith
  have hinterior := guard_peak (a := a) hn' ht hM' q rfl (fun s u => (hLip s u).trans (by
    have hd : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show d ≤ n by omega)
    gcongr)) (fun j hj => by
      have hI : j ∈ I := Finset.mem_range.mpr (by omega)
      exact ⟨(hS _ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem L hI)))).1,
        (hS _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hI)))).1⟩)
  have hinput (i : Fin m) : arccos (x i) ∈ Y := Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hsplus (i : Fin m) := (hS _ (hinput i)).1
  have hsminus (i : Fin m) := (hS _ (hinput i)).2
  obtain ⟨P,hP,hPx,z,hz,hPz⟩ := transfer_peak (x := x) hC ha hinterior.1 hinterior.2
    (le_of_eq hdR) A B hA hB (fun i => by
      simpa [Real.cos_arccos (x i).2.1 (x i).2.2] using hsplus i) (fun i => by
      simpa [Real.cos_neg,Real.sin_neg,Real.cos_arccos (x i).2.1 (x i).2.2,sub_eq_add_neg] using hsminus i)
    (by change 4*C+2 < |q t| at hM; change 4*C < |q t|; linarith)
  obtain ⟨Q,hQ,hQx,hQz⟩ := exact_degree_of_peaking hC x P hP hPx hz hPz
  exact ⟨Q,hQ,hQx,z,hz,hQz⟩


theorem main : H1 → H2 → OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H2 := by
  intro hc hb
  exact OMA.MeshPeak1133.grid_obstruction_of_continuous
    (OMA.Mesh1133.mesh_estimate OMA.Mesh1133.interval_derivative_bound) (continuous_peak hc hb)

end OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1
end

section

namespace Erdos1133.Norming

open Polynomial Set

noncomputable def value {n : ℕ} (a : Fin (n+1) → ℝ) (x : ℝ) : ℝ :=
  ∑ k, a k * Real.cos ((k.val : ℝ) * x)

/-- A finite cosine polynomial attains its global absolute maximum. -/
theorem exists_peak {n : ℕ} (a : Fin (n+1) → ℝ) :
    ∃ θ : ℝ, ∀ x : ℝ, |value a x| ≤ |value a θ| := by
  let P : Polynomial ℝ :=
    ∑ k : Fin (n+1), C (a k) * Chebyshev.T ℝ (k.val : ℤ)
  have heval (t : ℝ) : P.eval (Real.cos t) = value a t := by
    simp [P, value, Polynomial.eval_finsetSum, Chebyshev.T_real_cos]
  have hcont : Continuous (fun t : ℝ => |value a t|) := by
    unfold value
    fun_prop
  obtain ⟨y, _, hmax⟩ : ∃ y ∈ Icc (0:ℝ) Real.pi,
      IsMaxOn (fun t => |value a t|) (Icc (0:ℝ) Real.pi) y :=
    isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, Real.pi_pos.le⟩ hcont.continuousOn
  refine ⟨y, fun x => ?_⟩
  let z := Real.arccos (Real.cos x)
  have hcos : Real.cos z = Real.cos x :=
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
  have hx : value a x = value a z := by rw [← heval, ← heval, hcos]
  rw [hx]
  exact hmax ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- Negating the pointwise obstruction gives one dominating sampled node
for each cosine polynomial, uniformly over all real evaluation angles. -/
theorem norming_of_no_witness {n m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 ≤ C)
    (φ : Fin m → ℝ) (h : ¬ ∃ (a : Fin (n+1) → ℝ) (θ : ℝ),
      0 < |value a θ| ∧ ∀ i, C*|value a (φ i)| < |value a θ|) :
    ∀ a : Fin (n+1) → ℝ, ∃ i : Fin m, ∀ x, |value a x| ≤ C*|value a (φ i)| := by
  classical
  intro a
  obtain ⟨θ, hpeak⟩ := exists_peak a
  by_cases hθ : 0 < |value a θ|
  · have hi : ¬ ∀ i, C*|value a (φ i)| < |value a θ| := fun hh => h ⟨a,θ,hθ,hh⟩
    push Not at hi
    obtain ⟨i,hi⟩ := hi
    exact ⟨i, fun x => (hpeak x).trans hi⟩
  · refine ⟨⟨0,hm⟩, fun x => (hpeak x).trans ?_⟩
    exact (le_of_not_gt hθ).trans (mul_nonneg hC (abs_nonneg _))

/-- All simultaneous right hand sides for sparsifying a family can be chosen
to be its actual maximum absolute values. -/
theorem bounded_family {n m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 ≤ C)
    (φ : Fin m → ℝ) (h : ¬ ∃ (a : Fin (n+1) → ℝ) (θ : ℝ),
      0 < |value a θ| ∧ ∀ i, C*|value a (φ i)| < |value a θ|) :
    ∃ M : (Fin (n+1) → ℝ) → ℝ,
      (∀ a, 0 ≤ M a) ∧ (∀ a x, |value a x| ≤ M a) ∧
      ∀ a, ∃ i : Fin m, M a ≤ C*|value a (φ i)| := by
  classical
  let θ := fun (a : Fin (n+1) → ℝ) => (exists_peak a).choose
  refine ⟨fun a => |value a (θ a)|, fun a => abs_nonneg _, fun a x =>
    (exists_peak a).choose_spec x, ?_⟩
  intro a
  obtain ⟨i,hi⟩ := norming_of_no_witness hm hC φ h a
  exact ⟨i, hi (θ a)⟩

end Erdos1133.Norming

end

section

open Finset

namespace Erdos1133.CosineTrace

/-- Applies to the normalized row sum of the modulated harmonic kernel.
The uniform kernel and high-frequency estimates enter as independent bounds. -/
theorem harmonic_trace_bound {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {S : Finset ℕ} {dlo dhi b : ℕ → R} {W E : R}
    (hb : ∀ j ∈ S, 0 ≤ b j)
    (hlo : ∀ j ∈ S, dlo j = 1/2)
    (hkernel : |∑ j ∈ S, b j * (dlo j - dhi j)| ≤ W)
    (hhigh : ∑ j ∈ S, b j * |dhi j| ≤ E) :
    (1/2 : R) * ∑ j ∈ S, b j ≤ W + E := by
  have hid : (1/2 : R) * ∑ j ∈ S, b j =
      (∑ j ∈ S, b j * (dlo j - dhi j)) + ∑ j ∈ S, b j * dhi j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => by rw [hlo j hj]; ring)
  have h2 : (∑ j ∈ S, b j * dhi j) ≤ E :=
    (Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (le_abs_self _) (hb j hj))).trans hhigh
  rw [hid]
  exact add_le_add ((le_abs_self _).trans hkernel) h2

/-- Expanding the diagonal pairing into its coordinate sum recovers the discrete
coefficient at each sampled node. -/
theorem coordinate_diagonal {R : Type*} [Field R] (N p : ℕ)
    (z : ℕ → R) (w : ℕ → ℕ → R) (v : ℕ → R) :
    (∑ t ∈ range N, z t * ∑ i ∈ range p, w t i * v i) / N =
      ∑ i ∈ range p, ((∑ t ∈ range N, z t * w t i)/(N : R)) * v i := by
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Reproduction of a low column transfers a discrete orthogonality identity to
the reconstructed high coefficient. -/
theorem reconstructed_orthogonality {R : Type*} [CommSemiring R] (N p : ℕ)
    (z y : ℕ → R) (w : ℕ → ℕ → R) (v : ℕ → R)
    (hrep : ∀ t < N, ∑ i ∈ range p, w t i * v i = y t)
    (horth : ∑ t ∈ range N, z t * y t = 0) :
    ∑ i ∈ range p, (∑ t ∈ range N, z t * w t i) * v i = 0 := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ = ∑ t ∈ range N, z t * y t :=
      Finset.sum_congr rfl (fun t ht => by rw [hrep t (mem_range.mp ht)])
    _ = 0 := horth

/-- The average of bounded kernel entries paired with rows of bounded ℓ¹ norm. -/
theorem averaged_row_bound {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {N p : ℕ} (w f : ℕ → ℕ → R) {C D : R} (hN : 0 < N) (hD : 0 ≤ D)
    (hw : ∀ t < N, ∑ i ∈ range p, |w t i| ≤ C)
    (hf : ∀ t < N, ∀ i < p, |f t i| ≤ D) :
    |(∑ t ∈ range N, ∑ i ∈ range p, w t i * f t i) / N| ≤ C*D := by
  rw [abs_div, abs_of_nonneg (show 0 ≤ (N : R) from Nat.cast_nonneg N)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  calc
    _ ≤ ∑ t ∈ range N, |∑ i ∈ range p, w t i * f t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ range N, (C*D) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ ∑ i ∈ range p, |w t i * f t i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ range p, |w t i| * D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hf t (mem_range.mp ht) i (mem_range.mp hi)) (abs_nonneg _)
        _ ≤ C*D := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hw t (mem_range.mp ht)) hD
    _ = _ := by simp [mul_comm]
/-- A finite weighted trace, represented as a linear functional on kernel entries. -/
noncomputable def rowTrace {R : Type*} [Field R] (N p : ℕ) (w : ℕ → ℕ → R) :
    (ℕ → ℕ → R) →ₗ[R] R where
  toFun f := (∑ t ∈ range N, ∑ i ∈ range p, w t i * f t i) / N
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (w _ _) c, ← Finset.mul_sum]
    ring

theorem trace_elementary_tensor {R : Type*} [Field R] (N p : ℕ)
    (w : ℕ → ℕ → R) (z v : ℕ → R) :
    rowTrace N p w (fun t i => z t * v i) =
      (∑ t ∈ range N, z t * ∑ i ∈ range p, w t i * v i)/(N:R) := by
  change (∑ t ∈ range N, ∑ i ∈ range p, w t i * (z t * v i)) / N = _
  simp_rw [mul_left_comm (w _ _) (z _), ← Finset.mul_sum]

/-- Finite matrix trace comparison. The two tensor families may be indexed
arbitrarily; the cosine specialization uses k=n-j and k=n+j. -/
theorem finite_trace_contradiction {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (S : Finset ℕ) (N p : ℕ) (w : ℕ → ℕ → R) (b : ℕ → R)
    (lo hi : ℕ → ℕ → ℕ → R) {C D E : R} (hN : 0 < N) (hD : 0 ≤ D)
    (hb : ∀ j ∈ S, 0 ≤ b j)
    (hw : ∀ t < N, ∑ i ∈ range p, |w t i| ≤ C)
    (hlo : ∀ j ∈ S, rowTrace N p w (lo j) = 1/2)
    (hk : let K := ∑ j ∈ S, b j • (lo j - hi j)
          ∀ t < N, ∀ i < p, |K t i| ≤ D)
    (hhi : ∑ j ∈ S, b j * |rowTrace N p w (hi j)| ≤ E)
    (hlarge : C*D + E < (1/2:R) * ∑ j ∈ S, b j) : False := by
  let K := ∑ j ∈ S, b j • (lo j - hi j)
  have heq : rowTrace N p w K = ∑ j ∈ S,
      b j * (rowTrace N p w (lo j) - rowTrace N p w (hi j)) := by
    simp [K]
  have hbound : |rowTrace N p w K| ≤ C*D := averaged_row_bound w K hN hD hw hk
  rw [heq] at hbound
  exact (not_lt_of_ge (harmonic_trace_bound hb hlo hbound hhi)) hlarge


end Erdos1133.CosineTrace

end

section

open Finset
namespace Erdos1133.CosineTrace

/-- Exact finite cosine sum on a half-step mesh. -/
theorem midpoint_cosine_sum (N : ℕ) (a : ℝ) :
    2*Real.sin (a/2) * (∑ t ∈ range N, Real.cos (((t:ℝ)+1/2)*a))
      = Real.sin ((N:ℝ)*a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.cast_succ]
    have h := @Real.sin_sub_sin (((N:ℝ)+1)*a) ((N:ℝ)*a)
    rw [show (((N:ℝ)+1)*a-(N:ℝ)*a)/2 = a/2 by ring,
      show (((N:ℝ)+1)*a+(N:ℝ)*a)/2 = ((N:ℝ)+1/2)*a by ring] at h
    linarith

end Erdos1133.CosineTrace

end

section

namespace Erdos1133.Band

/-- A finite harmonic band can be placed inside the first half of each
sufficiently large degree while controlling the cost of the rank estimate. -/
theorem choose_band (k n : Nat) (hn : 2*2^k ≤ n) :
    ∃ J : Nat, 0 < J ∧ 2*(2^k*J) ≤ n ∧ n ≤ 4*(2^k*J) := by
  let Q : Nat := 2*2^k
  let J := n/Q
  have hpow : 0 < 2^k := Nat.pow_pos (by decide)
  have hQ : 0 < Q := Nat.mul_pos (by decide) hpow
  have hJ : 0 < J := Nat.div_pos hn hQ
  have hlo : J*Q ≤ n := Nat.div_mul_le_self n Q
  have hrem := Nat.mod_lt n hQ
  have hdecomp := Nat.mod_add_div n Q
  change n%Q + Q*J = n at hdecomp
  have hQJ : Q ≤ Q*J := by
    have hm := Nat.mul_le_mul_left Q hJ
    simpa only [Nat.mul_one] using hm
  have heq : Q*J = 2*(2^k*J) := Nat.mul_assoc 2 (2^k) J
  refine ⟨J, hJ, ?_, ?_⟩
  · rw [← heq, Nat.mul_comm Q J]
    exact hlo
  · omega

end Erdos1133.Band

end

section

/-! Uniform truncation bound for the real modulated harmonic kernel. -/
namespace Erdos1133.KernelBound

open Finset
open scoped BigOperators

private theorem sin_multiple (x : ℝ) (j : ℕ) :
    |Real.sin ((j : ℝ)*x)| ≤ (j : ℝ)*|Real.sin x| := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((j : ℝ)*x) * Real.cos x| +
          |Real.cos ((j : ℝ)*x) * Real.sin x| := abs_add_le _ _
      _ ≤ |Real.sin ((j : ℝ)*x)| + |Real.sin x| := by
        simp only [abs_mul]
        apply add_le_add
        · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
        · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ _ := by linarith

private theorem abel_diff (c f : ℕ → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (hf : ∀ i, 0 ≤ f i) (hm : ∀ i, f (i+1) ≤ f i) (m : ℕ) :
    |∑ i ∈ range m, (c i - c (i+1)) * f i| ≤ 2 * f 0 := by
  let S := fun n : ℕ => ∑ i ∈ range n, (c i - c (i+1)) * f i
  have h (n : ℕ) : |S n + c n * f n - c 0 * f 0| ≤ f 0 - f n := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have hs : S (n+1) = S n + (c n - c (n+1)) * f n := sum_range_succ _ _
      rw [show S (n+1) + c (n+1) * f (n+1) - c 0 * f 0 =
          (S n + c n * f n - c 0 * f 0) + c (n+1) * (f (n+1) - f n) by rw [hs]; ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hm n))]
      have h' := mul_le_of_le_one_left (neg_nonneg.mpr (sub_nonpos.mpr (hm n))) (hc (n+1))
      linarith
  have hsum : S m = (S m + c m*f m - c 0*f 0) + (c 0*f 0 - c m*f m) := by ring
  change |S m| ≤ _
  rw [hsum]
  refine (abs_add_le _ _).trans ?_
  have hdiff := abs_sub (c 0*f 0) (c m*f m)
  simp only [abs_mul, abs_of_nonneg (hf 0), abs_of_nonneg (hf m)] at hdiff
  linarith [h m, mul_le_of_le_one_left (hf 0) (hc 0), mul_le_of_le_one_left (hf m) (hc m)]

private noncomputable def term (x : ℝ) (j : ℕ) := Real.sin ((j : ℝ)*x)/(j : ℝ)

private theorem term_bound (x : ℝ) (j : ℕ) : |term x j| ≤ 2*|Real.sin (x/2)| := by
  by_cases hj : j=0
  · simp [hj,term]
  have hd : (0:ℝ)<j := by exact_mod_cast (Nat.pos_of_ne_zero hj)
  rw [term, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have h := sin_multiple (x/2) (2*j)
  push_cast at h
  rw [show 2*(j : ℝ)*(x/2) = (j : ℝ)*x by ring] at h
  calc
    _ ≤ 2 * (j : ℝ) * |Real.sin (x/2)| := h
    _ = _ := by ring

private theorem tail_bound (x : ℝ) (J m : ℕ) (hJ : 0 < J)
    (hs : 1 ≤ (J : ℝ)*|Real.sin (x/2)|) :
    |∑ i ∈ range m, term x (J+i)| ≤ 1 := by
  let c := fun i : ℕ => Real.cos ((((J : ℝ)+i)-1/2)*x)
  let f := fun i : ℕ => 1 / ((J : ℝ)+i)
  have hd : (0 : ℝ) < J := by exact_mod_cast hJ
  have hf : ∀ i, 0 ≤ f i := by intro i; dsimp [f]; positivity
  have hm : ∀ i, f (i+1) ≤ f i := by
    intro i
    apply one_div_le_one_div_of_le (by positivity : 0 < (J : ℝ)+i)
    push_cast
    linarith
  have he (i : ℕ) : (c i-c (i+1))*f i = (2*Real.sin (x/2)) * term x (J+i) := by
    dsimp [c,f,term]
    rw [Real.cos_sub_cos]
    push_cast
    rw [show (((J : ℝ)+i-1/2)*x+((J : ℝ)+((i : ℝ)+1)-1/2)*x)/2 = ((J : ℝ)+i)*x by ring,
      show (((J : ℝ)+i-1/2)*x-((J : ℝ)+((i : ℝ)+1)-1/2)*x)/2 = -(x/2) by ring,
      Real.sin_neg]
    ring
  have h := abel_diff c f (fun i => Real.abs_cos_le_one _) hf hm m
  simp_rw [he] at h
  rw [← mul_sum, abs_mul, abs_mul] at h
  rw [abs_of_pos (show (0:ℝ)<2 by norm_num)] at h
  have hs' : 0 < |Real.sin (x/2)| := by
    by_contra! hh
    have hz := le_antisymm hh (abs_nonneg (Real.sin (x/2)))
    rw [hz, mul_zero] at hs
    norm_num at hs
  have hbound : |Real.sin (x/2)| *
      |∑ i ∈ range m, term x (J+i)| ≤ 1/(J : ℝ) := by
    change 2 * |Real.sin (x / 2)| * |∑ i ∈ range m, term x (J+i)| ≤ 2 * (1 / ((J:ℝ) + ↑(0:ℕ))) at h
    rw [Nat.cast_zero, add_zero] at h
    linarith
  have hinv : 1/(J : ℝ) ≤ |Real.sin (x/2)| :=
    (div_le_iff₀ hd).mpr (by linarith [mul_comm (J : ℝ) |Real.sin (x/2)|])
  apply (mul_le_mul_iff_right₀ hs').mp
  rw [mul_one]
  exact hbound.trans hinv

private theorem prefix_bound (x : ℝ) (L : ℕ) :
    |∑ j ∈ range L, term x j| ≤ 5 := by
  let s := |Real.sin (x/2)|
  have hs0 : 0 ≤ s := abs_nonneg _
  have hs1 : s ≤ 1 := Real.abs_sin_le_one _
  have hsmall (m : ℕ) : |∑ j ∈ range m, term x j| ≤ (m : ℝ) * (2*s) := by
    calc
      _ ≤ ∑ j ∈ range m, |term x j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range m, 2*s := sum_le_sum fun j _ => term_bound x j
      _ = _ := by simp
  rcases hs0.eq_or_lt with hz | hs
  · have h := hsmall L
    rw [← hz] at h
    linarith
  let M := ⌈1/s⌉₊
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hm1 : 1 ≤ (M : ℝ)*s := by
    apply (div_le_iff₀ hs).mp
    exact Nat.le_ceil _
  have hm2 : (M : ℝ)*s ≤ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 1/s by positivity)
    have hh := mul_lt_mul_of_pos_right h hs
    rw [add_mul, div_mul_cancel₀ _ hs.ne', one_mul] at hh
    dsimp [M]
    linarith
  by_cases hLM : L ≤ M
  · have hl : (L : ℝ)*s ≤ (M : ℝ)*s :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hLM) hs0
    nlinarith [hsmall L]
  have hML : M ≤ L := by omega
  rw [← sum_range_add_sum_Ico _ hML]
  refine (abs_add_le _ _).trans ?_
  have ht : |∑ j ∈ Ico M L, term x j| ≤ 1 := by
    rw [sum_Ico_eq_sum_range]
    exact tail_bound x M (L-M) hM hm1
  nlinarith [hsmall M]

theorem sine_harmonic_bound (x : ℝ) (J L : ℕ) :
    |∑ j ∈ Ico J L, Real.sin ((j : ℝ)*x)/(j : ℝ)| ≤ 10 := by
  by_cases h : J ≤ L
  · change |∑ j ∈ Ico J L, term x j| ≤ _
    rw [sum_Ico_eq_sub _ h]
    exact (abs_sub _ _).trans (by linarith [prefix_bound x L, prefix_bound x J])
  · simp [Ico_eq_empty_of_le (by omega : L ≤ J)]

theorem cosine_kernel_bound (N J L : ℕ) (θ φ : ℝ) :
    |∑ j ∈ Ico J L,
      (Real.cos (((N:ℝ)-j)*θ) * Real.cos (((N:ℝ)-j)*φ) -
       Real.cos (((N:ℝ)+j)*θ) * Real.cos (((N:ℝ)+j)*φ)) / (j:ℝ)| ≤ 20 := by
  have prod (n x y : ℝ) : Real.cos (n*x) * Real.cos (n*y) =
      (Real.cos (n*(x+y)) + Real.cos (n*(x-y)))/2 := by
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring
  have shift (n j x : ℝ) : Real.cos ((n-j)*x)-Real.cos ((n+j)*x)=
      2*Real.sin (n*x)*Real.sin (j*x) := by
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  have he (j : ℕ) :
      (Real.cos (((N:ℝ)-j)*θ)*Real.cos (((N:ℝ)-j)*φ) -
       Real.cos (((N:ℝ)+j)*θ)*Real.cos (((N:ℝ)+j)*φ))/(j:ℝ) =
      Real.sin ((N:ℝ)*(θ+φ))*term (θ+φ) j +
      Real.sin ((N:ℝ)*(θ-φ))*term (θ-φ) j := by
    rw [prod,prod]
    dsimp [term]
    have hn : (Real.cos (((N:ℝ)-j)*(θ+φ))+Real.cos (((N:ℝ)-j)*(θ-φ)))/2 -
        (Real.cos (((N:ℝ)+j)*(θ+φ))+Real.cos (((N:ℝ)+j)*(θ-φ)))/2 =
        Real.sin ((N:ℝ)*(θ+φ))*Real.sin ((j:ℝ)*(θ+φ)) +
        Real.sin ((N:ℝ)*(θ-φ))*Real.sin ((j:ℝ)*(θ-φ)) := by
      linear_combination (shift (N:ℝ) (j:ℝ) (θ+φ) + shift (N:ℝ) (j:ℝ) (θ-φ)) / 2
    rw [hn]
    ring
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h (x : ℝ) : |Real.sin ((N:ℝ)*x)| * |∑ j ∈ Ico J L, term x j| ≤ 10 :=
    (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans (sine_harmonic_bound x J L)
  linarith [h (θ+φ), h (θ-φ)]

end Erdos1133.KernelBound

end

section

/-! Quantitative choice of the oversampling ratio in the high-trace estimate. -/
namespace Erdos1133.Ratio

theorem scaled_trace_bound {B C n r J D T : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hn : 0 ≤ n) (_hr : 0 ≤ r)
    (hJ : 0 < J) (hD : 0 < D) (hwidth : n ≤ D * J)
    (hcodim : r ≤ n / D^2) (htrace : T ≤ C * Real.sqrt ((B*n)*r)) :
    1 / J * T ≤ C * Real.sqrt B := by
  have hnJ : n/D ≤ J := (div_le_iff₀ hD).2 (by simpa [mul_comm] using hwidth)
  have hnr : n*r ≤ J^2 := calc
    n*r ≤ n*(n/D^2) := mul_le_mul_of_nonneg_left hcodim hn
    _ = (n/D)^2 := by ring
    _ ≤ J^2 := by gcongr
  have hroot : Real.sqrt ((B*n)*r) ≤ Real.sqrt B * J := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hB]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnr hB
  calc
    1 / J * T ≤ 1 / J * (C * (Real.sqrt B * J)) := by
      apply mul_le_mul_of_nonneg_left (htrace.trans (mul_le_mul_of_nonneg_left hroot hC))
      positivity
    _ = C * Real.sqrt B := by field_simp

/-- The floor in the official H2 statement respects the continuous oversampling bound. -/
theorem floor_size {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    ((⌊(1+ε)*(n:ℝ)⌋₊:ℕ):ℝ) ≤ (1+ε)*(n:ℝ) := Nat.floor_le (by positivity)

/-- The dyadic aspect ratio gives an admissible positive oversampling ratio. -/
theorem epsilon_choice (q : ℕ) : 0 < (1:ℝ)/(4*2^q)^2 := by positivity

end Erdos1133.Ratio

end

section

open scoped BigOperators InnerProductSpace

namespace Erdos1133.RankBound

variable {κ ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bessel's inequality summed over all sample coordinates. -/
theorem coordinate_bessel [Fintype ι] (s : Finset κ) (z : κ → V)
    (hz : Orthonormal ℝ z) (w : ι → V) :
    (∑ k ∈ s, ∑ i, ⟪z k, w i⟫_ℝ ^ 2) ≤ ∑ i, ‖w i‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs, sq_abs] using
    (hz.sum_inner_products_le (s := s) (w i))

/-- Transpose a real-coordinate sampling estimate using only finite Cauchy–Schwarz. -/
theorem scalar_frame_of_synthesis {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset κ) (t : Finset ι) (v : κ → ι → R) (L : R) (hL : 0 ≤ L)
    (hSynth : ∀ a : κ → R, (∑ i ∈ t, (∑ k ∈ s, a k * v k i) ^ 2) ≤
      L * ∑ k ∈ s, a k ^ 2) (h : ι → R) :
    (∑ k ∈ s, (∑ i ∈ t, h i * v k i) ^ 2) ≤ L * ∑ i ∈ t, h i ^ 2 := by
  let a (k : κ) := ∑ i ∈ t, h i * v k i
  let u (i : ι) := ∑ k ∈ s, a k * v k i
  let Q := ∑ k ∈ s, a k ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun k _ => sq_nonneg (a k)
  have hEq : (∑ i ∈ t, h i * u i) = Q := by
    calc
      _ = ∑ k ∈ s, ∑ i ∈ t, h i * (a k * v k i) := by
        simp only [u, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ k ∈ s, a k * ∑ i ∈ t, h i * v k i := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ = Q := by simp only [Q, a, sq]
  have base := Finset.sum_mul_sq_le_sq_mul_sq t h u
  rw [hEq] at base
  have bound := base.trans (mul_le_mul_of_nonneg_left (hSynth a)
    (Finset.sum_nonneg fun i _ => sq_nonneg (h i)))
  change Q ≤ L * ∑ i ∈ t, h i ^ 2
  rcases eq_or_lt_of_le hQ with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hL (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · apply le_of_mul_le_mul_right _ hpos
    calc
      Q * Q = Q ^ 2 := (sq Q).symm
      _ ≤ (∑ i ∈ t, h i ^ 2) * (L * Q) := bound
      _ = (L * ∑ i ∈ t, h i ^ 2) * Q := by ac_rfl

/-- A bound on finite linear combinations also bounds the transposed sampling map. -/
theorem frame_of_synthesis (s : Finset κ) (v : κ → V) (L : ℝ)
    (hL : 0 ≤ L) (hSynth : ∀ a : κ → ℝ, ‖∑ k ∈ s, a k • v k‖ ^ 2 ≤ L * ∑ k ∈ s, (a k) ^ 2)
    (h : V) : (∑ k ∈ s, ⟪h, v k⟫_ℝ ^ 2) ≤ L * ‖h‖ ^ 2 := by
  classical
  let a : κ → ℝ := fun k => ⟪h, v k⟫_ℝ
  let S : ℝ := ∑ k ∈ s, a k ^ 2
  let u : V := ∑ k ∈ s, a k • v k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg (a k)
  have hu : ‖u‖ ^ 2 ≤ L * S := hSynth a
  have hu' : ⟪h, u⟫_ℝ = S := by
    simp only [u, S, inner_sum, real_inner_smul_right, a, sq]
  have hcs : S ^ 2 ≤ ‖h‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [hu', sq_abs, mul_pow] using
      (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm h u) 2)
  change S ≤ L * ‖h‖ ^ 2
  rcases eq_or_lt_of_le hS with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hL (sq_nonneg _)
  · apply le_of_mul_le_mul_right _ hpos
    calc
      S * S = S ^ 2 := (sq S).symm
      _ ≤ ‖h‖ ^ 2 * ‖u‖ ^ 2 := hcs
      _ ≤ ‖h‖ ^ 2 * (L * S) := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = (L * ‖h‖ ^ 2) * S := by ac_rfl

/-- The squared norms of the projected sampling columns sum to at most
the frame bound times the dimension of the target subspace. -/
theorem projection_energy (s : Finset κ) (v : κ → V) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] (L : ℝ)
    (hFrame : ∀ h : V, (∑ k ∈ s, ⟪h, v k⟫_ℝ ^ 2) ≤ L * ‖h‖ ^ 2) :
    (∑ k ∈ s, ‖W.orthogonalProjectionOnto (v k)‖ ^ 2) ≤ L * Module.finrank ℝ W := by
  classical
  let e := stdOrthonormalBasis ℝ W
  calc
    (∑ k ∈ s, ‖W.orthogonalProjectionOnto (v k)‖ ^ 2)
        = ∑ k ∈ s, ∑ j, ⟪e j, W.orthogonalProjectionOnto (v k)⟫_ℝ ^ 2 := by
          exact Finset.sum_congr rfl fun k _ => (e.sum_sq_inner_right _).symm
    _ = ∑ j, ∑ k ∈ s, ⟪(e j : V), v k⟫_ℝ ^ 2 := by
          simp only [W.inner_orthogonalProjectionOnto_eq_of_mem_left]
          rw [Finset.sum_comm]
    _ ≤ ∑ _j : Fin (Module.finrank ℝ W), L := by
          apply Finset.sum_le_sum
          intro j _
          have hn : ‖(e j : V)‖ = 1 := e.norm_eq_one j
          simpa only [hn, one_pow, mul_one] using hFrame (e j : V)
    _ = L * Module.finrank ℝ W := by simp [nsmul_eq_mul, mul_comm]

/-- In coordinates indexed by r basis elements, a per-coordinate frame bound gives
an absolute diagonal trace bound with squared factor L*r. -/
theorem coordinate_rank_trace_sq {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset κ) (t : Finset ι) (b v : κ → ι → R) (L : R)
    (hCol : ∀ i ∈ t, (∑ k ∈ s, v k i ^ 2) ≤ L) :
    (∑ k ∈ s, |∑ i ∈ t, b k i * v k i|) ^ 2 ≤
      (∑ k ∈ s, ∑ i ∈ t, b k i ^ 2) * (L * t.card) := by
  have hEnergy : (∑ k ∈ s, ∑ i ∈ t, v k i ^ 2) ≤ L * t.card := by
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum hCol).trans_eq (by simp [nsmul_eq_mul, mul_comm])
  have hk (k : κ) : |∑ i ∈ t, b k i * v k i| ^ 2 ≤
      (∑ i ∈ t, b k i ^ 2) * ∑ i ∈ t, v k i ^ 2 := by
    simpa only [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq t (b k) (v k)
  exact (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg (b k i))
    (fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg (v k i))
    (fun k _ => hk k)).trans (mul_le_mul_of_nonneg_left hEnergy
      (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg (b k i)))

/-- Absolute high-frequency diagonal trace bound when all coefficient vectors lie in W. -/
theorem high_trace_sq (s : Finset κ) (v : κ → V) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] (b : κ → W) (L : ℝ)
    (hFrame : ∀ h : V, (∑ k ∈ s, ⟪h, v k⟫_ℝ ^ 2) ≤ L * ‖h‖ ^ 2) :
    (∑ k ∈ s, |⟪(b k : V), v k⟫_ℝ|) ^ 2 ≤
      (∑ k ∈ s, ‖b k‖ ^ 2) * (L * Module.finrank ℝ W) := by
  classical
  have entry (k : κ) : |⟪(b k : V), v k⟫_ℝ| ^ 2 ≤
      ‖b k‖ ^ 2 * ‖W.orthogonalProjectionOnto (v k)‖ ^ 2 := by
    rw [← W.inner_orthogonalProjectionOnto_eq_of_mem_left (b k)]
    simpa only [mul_pow] using (pow_le_pow_left₀ (abs_nonneg _)
      (abs_real_inner_le_norm (b k) (W.orthogonalProjectionOnto (v k))) 2)
  exact (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun k _ => sq_nonneg ‖b k‖) (fun k _ => sq_nonneg ‖W.orthogonalProjectionOnto (v k)‖)
    (fun k _ => entry k)).trans (mul_le_mul_of_nonneg_left (projection_energy s v W L hFrame)
      (Finset.sum_nonneg fun k _ => sq_nonneg ‖b k‖))

/-- Bessel on raw scalar arrays, without introducing normalized cosine vectors.
Here H is the common squared length of the rows of z. -/
theorem scalar_bessel {R τ : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset κ) (t : Finset τ) (z : κ → τ → R)
    (w : τ → R) (H : R) (hH : 0 ≤ H) [DecidableEq κ]
    (hOrth : ∀ j ∈ s, ∀ k ∈ s,
      (∑ i ∈ t, z j i * z k i) = if j = k then H else 0) :
    (∑ k ∈ s, (∑ i ∈ t, z k i * w i) ^ 2) ≤ H * ∑ i ∈ t, w i ^ 2 := by
  classical
  let b (k : κ) := ∑ i ∈ t, z k i * w i
  let u (i : τ) := ∑ k ∈ s, b k * z k i
  let Q := ∑ k ∈ s, b k ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun k _ => sq_nonneg (b k)
  have mix (f : τ → R) :
      (∑ i ∈ t, u i * f i) = ∑ k ∈ s, b k * ∑ i ∈ t, z k i * f i := by
    simp only [u, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hw : (∑ i ∈ t, u i * w i) = Q := by
    simpa only [Q, b, sq] using mix w
  have hz (k : κ) (hk : k ∈ s) : (∑ i ∈ t, z k i * u i) = b k * H := by
    calc
      (∑ i ∈ t, z k i * u i) = ∑ i ∈ t, u i * z k i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ j ∈ s, b j * ∑ i ∈ t, z j i * z k i := mix (z k)
      _ = ∑ j ∈ s, if j = k then b j * H else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hOrth j hj k hk]
        split <;> simp_all
      _ = b k * H := by simp [hk]
  have hu : (∑ i ∈ t, u i ^ 2) = H * Q := by
    calc
      (∑ i ∈ t, u i ^ 2) = ∑ i ∈ t, u i * u i := by simp only [sq]
      _ = ∑ k ∈ s, b k * ∑ i ∈ t, z k i * u i := mix u
      _ = ∑ k ∈ s, H * (b k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hz k hk, sq]
        ac_rfl
      _ = H * Q := (Finset.mul_sum ..).symm
  have bound := Finset.sum_mul_sq_le_sq_mul_sq t u w
  rw [hw, hu] at bound
  change Q ≤ H * ∑ i ∈ t, w i ^ 2
  rcases eq_or_lt_of_le hQ with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hH (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  · apply le_of_mul_le_mul_right _ hpos
    calc
      Q * Q = Q ^ 2 := (sq Q).symm
      _ ≤ (H * Q) * ∑ i ∈ t, w i ^ 2 := bound
      _ = (H * ∑ i ∈ t, w i ^ 2) * Q := by ac_rfl

/-- Apply the trace estimate to the orthogonal complement of the low modes.
The result only depends on the common coefficient norm bound M and the codimension r. -/
theorem high_trace_of_codimension [FiniteDimensional ℝ V]
    (s : Finset κ) (v : κ → V) (U : Submodule ℝ V) (b : κ → Uᗮ)
    (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (r : ℕ)
    (hr : Module.finrank ℝ U + r = Module.finrank ℝ V)
    (hB : (∑ k ∈ s, ‖b k‖ ^ 2) ≤ M ^ 2)
    (hSynth : ∀ a : κ → ℝ, ‖∑ k ∈ s, a k • v k‖ ^ 2 ≤ L * ∑ k ∈ s, (a k) ^ 2) :
    (∑ k ∈ s, |⟪(b k : V), v k⟫_ℝ|) ≤ M * Real.sqrt (L * r) := by
  have h := high_trace_sq s v Uᗮ b L (frame_of_synthesis s v L hL hSynth)
  rw [Submodule.finrank_add_finrank_orthogonal' hr] at h
  have hh := h.trans (mul_le_mul_of_nonneg_right hB (mul_nonneg hL (Nat.cast_nonneg r)))
  simpa only [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] using Real.le_sqrt_of_sq_le hh

/-- Recovering an orthogonal family with nonzero diagonal Gram entries from the sampled
columns makes those columns linearly independent. The row for the constant mode may
have a different squared length. -/
theorem independent_of_reproduced_modes {R E τ : Type*} [Field R] [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι]
    (t : Finset τ) (v : ι → E) (z : ι → τ → R) (w : τ → E →ₗ[R] R)
    (d : ι → R) (hd : ∀ j, d j ≠ 0)
    (hRep : ∀ i ∈ t, ∀ j, w i (v j) = z j i)
    (hGram : ∀ j k, (∑ i ∈ t, z j i * z k i) = if j = k then d j else 0) :
    LinearIndependent R v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a haz k
  have hRow (i : τ) (hi : i ∈ t) : (∑ j, a j * z j i) = 0 := by
    have h := congrArg (w i) haz
    simpa only [map_sum, map_smul, smul_eq_mul, hRep i hi, map_zero] using h
  have hk : a k * d k = 0 := by
    calc
      a k * d k = ∑ j, a j * ∑ i ∈ t, z k i * z j i := by
        simp_rw [hGram]
        simp [mul_ite]
      _ = ∑ i ∈ t, z k i * ∑ j, a j * z j i := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ac_rfl
      _ = 0 := Finset.sum_eq_zero fun i hi => by rw [hRow i hi, mul_zero]
  exact (mul_eq_zero.mp hk).resolve_right (hd k)

/-- Convert the exact dimension sum n+1+r=p into the real-valued defect bound. -/
theorem codimension_numeric {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n r p : ℕ} (ε : R) (hsplit : n+1+r=p) (hsize : (p : R) ≤ (1+ε)*n) :
    (r : R) ≤ ε*n := by
  have hsum : (n : R) + 1 + (r : R) = (p : R) := by exact_mod_cast hsplit
  rw [add_mul, one_mul] at hsize
  linarith

/-- Rank and codimension arithmetic for n+1 sampled columns, valid for every
complement whose dimension adds to the ambient dimension p. -/
theorem sampled_rank_given_complement {R E : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommGroup E] [Module R E] {n p r : ℕ}
    (v : Fin (n+1) → E) (hv : LinearIndependent R v) (ε : R)
    (hsplit : Module.finrank R (Submodule.span R (Set.range v)) + r = p)
    (hsize : (p : R) ≤ (1+ε) * n) :
    Module.finrank R (Submodule.span R (Set.range v)) = n+1 ∧ (r : R) ≤ ε * n := by
  have hdim : Module.finrank R (Submodule.span R (Set.range v)) = n+1 := by
    simpa using (finrank_span_eq_card hv)
  rw [hdim] at hsplit
  exact ⟨hdim, codimension_numeric ε hsplit hsize⟩

/-- Exact rank and real codimension estimate, including the constant column. -/
theorem sampled_span_rank_codim [FiniteDimensional ℝ V] {n : ℕ}
    (v : Fin (n+1) → V) (hv : LinearIndependent ℝ v) (ε : ℝ)
    (hsize : (Module.finrank ℝ V : ℝ) ≤ (1+ε) * n) :
    let U := Submodule.span ℝ (Set.range v)
    Module.finrank ℝ U = n+1 ∧ (Module.finrank ℝ Uᗮ : ℝ) ≤ ε * n := by
  let U := Submodule.span ℝ (Set.range v)
  exact sampled_rank_given_complement v hv ε U.finrank_add_finrank_orthogonal hsize

/-- Squared energy of the normalized Fourier coefficients. This statement uses the same
raw arrays, row bounds and common Gram entry N/2 as the finite cosine trace. -/
theorem averaged_coefficient_energy {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ℕ) (N p : ℕ) (hN : 0 < N)
    (z w : ℕ → ℕ → R) (C : R)
    (hGram : ∀ j ∈ s, ∀ k ∈ s, (∑ t ∈ Finset.range N, z j t * z k t) =
      if j = k then (N : R)/2 else 0)
    (hRows : ∀ t < N, (∑ i ∈ Finset.range p, |w t i|) ≤ C) :
    (∑ k ∈ s, ∑ i ∈ Finset.range p,
      ((∑ t ∈ Finset.range N, z k t * w t i) / (N : R)) ^ 2) ≤ C ^ 2 := by
  have hNr : 0 < (N : R) := Nat.cast_pos.mpr hN
  let H := (N : R)/2
  have hH : 0 ≤ H := div_nonneg hNr.le zero_le_two
  have hHN : H ≤ (N : R) := by dsimp [H]; linarith
  have row (t : ℕ) (ht : t ∈ Finset.range N) :
      (∑ i ∈ Finset.range p, w t i ^ 2) ≤ C ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range p, |w t i| ^ 2 := by simp only [sq_abs]
      _ ≤ (∑ i ∈ Finset.range p, |w t i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg (w t i)
      _ ≤ C ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (hRows t (Finset.mem_range.mp ht)) 2
  have total : (∑ i ∈ Finset.range p, ∑ t ∈ Finset.range N, w t i ^ 2) ≤
      (N : R) * C ^ 2 := by
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum row).trans_eq (by simp [nsmul_eq_mul])
  have raw : (∑ i ∈ Finset.range p, ∑ k ∈ s, (∑ t ∈ Finset.range N, z k t * w t i) ^ 2)
      ≤ C ^ 2 * (N : R) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range p, H * ∑ t ∈ Finset.range N, w t i ^ 2 :=
        Finset.sum_le_sum fun i _ => scalar_bessel s _ z (fun t => w t i) H hH hGram
      _ = H * (∑ i ∈ Finset.range p, ∑ t ∈ Finset.range N, w t i ^ 2) :=
        (Finset.mul_sum ..).symm
      _ ≤ H * ((N : R) * C ^ 2) := mul_le_mul_of_nonneg_left total hH
      _ ≤ (N : R) * ((N : R) * C ^ 2) :=
        mul_le_mul_of_nonneg_right hHN (mul_nonneg hNr.le (sq_nonneg _))
      _ = C ^ 2 * (N : R) ^ 2 := by rw [sq (N : R)]; ac_rfl
  have hSumDiv (u : Finset ℕ) (f : ℕ → R) (a : R) : (∑ i ∈ u, f i) / a = ∑ i ∈ u, f i / a := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp only [div_pow, ← hSumDiv]
  rw [Finset.sum_comm]
  exact (div_le_iff₀ (sq_pos_of_pos hNr)).mpr raw

noncomputable def sampleVec (p : ℕ) (x : ℕ → ℝ) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun i => x i

theorem sampleVec_inner (p : ℕ) (x y : ℕ → ℝ) :
    ⟪sampleVec p x, sampleVec p y⟫_ℝ = ∑ i ∈ Finset.range p, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => x i * y i) p

theorem sampleVec_norm_sq (p : ℕ) (x : ℕ → ℝ) :
    ‖sampleVec p x‖ ^ 2 = ∑ i ∈ Finset.range p, x i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fin.sum_univ_eq_sum_range (fun i => x i ^ 2) p

/-- The synthesis vector in Euclidean space is the coordinatewise scalar synthesis sum. -/
theorem sampleVec_sum_smul (p : ℕ) (s : Finset κ) (a : κ → ℝ) (v : κ → ℕ → ℝ) :
    (∑ k ∈ s, a k • sampleVec p (v k)) =
      sampleVec p (fun i => ∑ k ∈ s, a k * v k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext i
    simp [sampleVec]
  | @insert k t hk ih =>
    rw [Finset.sum_insert hk, ih]
    ext i
    simp [sampleVec, Finset.sum_insert hk, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Pointwise annihilation of the low columns suffices for membership in their
orthogonal complement, also when a frequency lives in a restricted high-frequency set. -/
theorem mem_span_orthogonal_of_annihilates (v : ι → V) (y : V)
    (hy : ∀ i, ⟪y, v i⟫_ℝ = 0) :
    y ∈ (Submodule.span ℝ (Set.range v))ᗮ := by
  have hker : Submodule.span ℝ (Set.range v) ≤ (innerSL ℝ y).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hy i
  exact (Submodule.mem_orthogonal' _ _).mpr fun u hu => hker hu

end Erdos1133.RankBound

end

section

/-! Separated angular sampling on one full period for the R1.H2 cosine matrix. -/
open Set MeasureTheory
open scoped BigOperators Interval

namespace Erdos1133.Sampling

private theorem young_neg {u v c : ℝ} (hc : 0 < c) :
    -(2*u*v) ≤ c*u^2 + v^2/c := by
  have H : -(2*u*v) - c*u^2 ≤ v^2/c := by
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c*u+v)]
  linarith

/-- Endpoint value is controlled by the energy of one forward interval. -/
theorem sample_on_arc {F D : ℝ → ℝ}
    (hD : Continuous D) (hFD : ∀ x, HasDerivAt F (D x) x)
    {h c : ℝ} (hh : 0 < h) (hc : 0 < c) (u : ℝ) :
    h * F u ^ 2 ≤ ∫ x in u..u+h, F x^2 + h*(c*F x^2 + D x^2/c) := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hFD x).continuousAt
  let E := fun x => c*F x^2 + D x^2/c
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hE0 (x : ℝ) : 0 ≤ E x := by dsimp [E]; positivity
  have hG : Continuous (fun x => -(2*F x*D x)) := by fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc u (u+h)) :
      F u^2 ≤ F x^2 + ∫ y in u..u+h, E y := by
    have hd (y : ℝ) : HasDerivAt (fun z => -(F z^2)) (-(2*F y*D y)) y := by
      convert! ((hFD y).pow 2).neg using 1
      norm_num
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := u) (b := x) (fun y _ => hd y) (hG.intervalIntegrable _ _)
    have hs := intervalIntegral.integral_mono_on (μ := volume) hx.1 (hG.intervalIntegrable _ _)
      (hE.intervalIntegrable _ _) (fun y _ => young_neg (u := F y) (v := D y) hc)
    have ht := intervalIntegral.integral_mono_interval (μ := volume) (le_refl u) hx.1 hx.2
      (Filter.Eventually.of_forall hE0) (hE.intervalIntegrable u (u+h))
    linarith
  have hSq : Continuous (fun x => F x^2) := by fun_prop
  have ha : u ≤ u+h := by linarith
  have hj := intervalIntegral.integral_mono_on (μ := volume) ha
    (f := fun _ => F u^2) (g := fun x => F x^2 + ∫ y in u..u+h, E y)
    (continuous_const.intervalIntegrable _ _)
    ((hSq.add continuous_const).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_add (g := fun _ => ∫ y in u..u+h, E y)
      (hSq.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)] at hj
  have hW : Continuous (fun x => h*E x) := by fun_prop
  rw [intervalIntegral.integral_add (hSq.intervalIntegrable _ _)
      (hW.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using hj

/-- Summing the disjoint arc bounds loses no factor in the number of nodes.
The orientation of nodes is unrestricted. -/
theorem separated_energy {ι : Type*} [Fintype ι] {F D : ℝ → ℝ}
    (hD : Continuous D) (hFD : ∀ x, HasDerivAt F (D x) x)
    (φ : ι → ℝ) {h c a b : ℝ} (hh : 0 < h) (hc : 0 < c) (hab : a ≤ b)
    (hlo : ∀ i, a ≤ φ i) (hhi : ∀ i, φ i + h ≤ b)
    (hsep : ∀ i j, i ≠ j → h ≤ |φ i - φ j|) :
    h * (∑ i, F (φ i)^2) ≤ ∫ x in a..b, F x^2 + h*(c*F x^2 + D x^2/c) := by
  classical
  let W := fun x => F x^2 + h*(c*F x^2 + D x^2/c)
  let S := fun i => Ioc (φ i) (φ i+h)
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hFD x).continuousAt
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hW0 (x : ℝ) : 0 ≤ W x := by dsimp [W]; positivity
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    rcases le_abs.mp (hsep i j hij) with hij | hji
    · exact (Set.Ioc_disjoint_Ioc_of_le (show φ j+h ≤ φ i by linarith)).symm
    · exact Set.Ioc_disjoint_Ioc_of_le (show φ i+h ≤ φ j by linarith)
  have hi := MeasureTheory.integral_iUnion_fintype (f := W) (s := S) (μ := volume)
    (fun _ => measurableSet_Ioc) hd (fun i => (hW.intervalIntegrable (φ i) (φ i+h)).1)
  have hsub : (⋃ i, S i) ⊆ Ioc a b := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨(hlo i).trans_lt hi.1, hi.2.trans (hhi i)⟩
  calc
    h * (∑ i, F (φ i)^2) = ∑ i, h * F (φ i)^2 := Finset.mul_sum ..
    _ ≤ ∑ i, ∫ x in S i, W x := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [S, W, ← intervalIntegral.integral_of_le (show φ i ≤ φ i+h by linarith)]
        using sample_on_arc hD hFD hh hc (φ i)
    _ = ∫ x in ⋃ i, S i, W x := hi.symm
    _ ≤ ∫ x in Ioc a b, W x := MeasureTheory.setIntegral_mono_set
      (hW.intervalIntegrable a b).1 (Filter.Eventually.of_forall hW0) hsub.eventuallyLE
    _ = _ := (intervalIntegral.integral_of_le hab).symm


private theorem integral_cos_integer (z : ℤ) :
    (∫ x in (0:ℝ)..2*Real.pi, Real.cos ((z:ℝ)*x)) =
      if z = 0 then 2*Real.pi else 0 := by
  by_cases hz : z = 0
  · simp [hz]
  rw [if_neg hz]
  have hz' : (z:ℝ) ≠ 0 := by exact_mod_cast hz
  have hd (x : ℝ) :
      HasDerivAt (fun t : ℝ => Real.sin ((z:ℝ)*t)/(z:ℝ)) (Real.cos ((z:ℝ)*x)) x := by
    convert! (((hasDerivAt_id x).const_mul (z:ℝ)).sin.div_const (z:ℝ)) using 1
    simp [hz']
  have hc : Continuous (fun x : ℝ => Real.cos ((z:ℝ)*x)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable _ _)]
  have hm : (z:ℝ)*(2*Real.pi) = ((2*z:ℤ):ℝ)*Real.pi := by push_cast; ring
  rw [hm, Real.sin_int_mul_pi (2*z)]
  simp

/-- Full-period real sine and cosine orthogonality with matching normalization. -/
theorem integral_mode_pair (sinMode : Bool) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    (∫ x in (0:ℝ)..2*Real.pi,
      (if sinMode then Real.sin ((k:ℝ)*x) else Real.cos ((k:ℝ)*x)) *
      (if sinMode then Real.sin ((l:ℝ)*x) else Real.cos ((l:ℝ)*x))) =
      if k = l then Real.pi else 0 := by
  let plus := fun x : ℝ => Real.cos ((((k:ℤ)+(l:ℤ):ℤ):ℝ)*x)
  let minus := fun x : ℝ => Real.cos ((((k:ℤ)-(l:ℤ):ℤ):ℝ)*x)
  have hp : Continuous plus := by dsimp [plus]; fun_prop
  have hm : Continuous minus := by dsimp [minus]; fun_prop
  have hplus : (∫ x in (0:ℝ)..2*Real.pi, plus x) = 0 := by
    exact (integral_cos_integer _).trans (if_neg (by omega))
  have hminus : (∫ x in (0:ℝ)..2*Real.pi, minus x) = if k = l then 2*Real.pi else 0 := by
    rw [show (∫ x in (0:ℝ)..2*Real.pi, minus x) = _ from integral_cos_integer _]
    split_ifs <;> first | rfl | omega
  have htrig (x : ℝ) :
      (if sinMode then Real.sin ((k:ℝ)*x) else Real.cos ((k:ℝ)*x)) *
      (if sinMode then Real.sin ((l:ℝ)*x) else Real.cos ((l:ℝ)*x)) =
        (minus x + (if sinMode then (-1:ℝ) else 1)*plus x)/2 := by
    dsimp [plus,minus]
    push_cast
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    cases sinMode <;> simp <;> ring
  simp_rw [htrig]
  have hsign : Continuous (fun x => (if sinMode then (-1:ℝ) else 1)*plus x) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hm.intervalIntegrable _ _)
    (hsign.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    hplus, hminus]
  split_ifs <;> ring

private theorem parseval_of_pair {κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → ℝ → ℝ)
    (hv : ∀ k, Continuous (v k))
    (ho : ∀ k l, (∫ x in (0:ℝ)..2*Real.pi, v k x*v l x) = if k=l then Real.pi else 0)
    (a : κ → ℝ) :
    (∫ x in (0:ℝ)..2*Real.pi, (∑ k, a k*v k x)^2) = Real.pi*(∑ k, a k^2) := by
  let T := fun (k l : κ) (x : ℝ) => (a k*a l)*(v k x*v l x)
  have hT (k l : κ) : Continuous (T k l) := by dsimp [T]; fun_prop
  have hsum (x : ℝ) : (∑ k, a k*v k x)^2 = ∑ k, ∑ l, T k l x := by
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by dsimp [T]; ring
  have htotal (k : κ) : Continuous (fun x => ∑ l, T k l x) :=
    continuous_finsetSum _ fun _ _ => hT _ _
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (htotal k).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun l _ => (hT _ l).intervalIntegrable _ _)]
  simp only [T, intervalIntegral.integral_const_mul, ho, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The separated high-frequency matrix has squared operator norm bounded by
π(1/h+5n). Here 1/h is proportional to n for the arcs used in R1.H2. -/
theorem high_band_sampling {ι κ : Type*} [Fintype ι] [Fintype κ]
    (φ : ι → ℝ) (k : κ → ℕ) (hinj : Function.Injective k) (a : κ → ℝ)
    {n : ℕ} (hn : 0 < n) (hfreq : ∀ j, 0 < k j ∧ k j ≤ 2*n)
    {h : ℝ} (hh : 0 < h) (hfit : h ≤ Real.pi)
    (hφ : ∀ i, φ i ∈ Icc 0 Real.pi) (hsep : ∀ i j, i ≠ j → h ≤ |φ i-φ j|) :
    (∑ i, (∑ j, a j * Real.cos ((k j:ℝ) * φ i))^2) ≤
      Real.pi*(1/h + 5*(n:ℝ))*(∑ j, a j^2) := by
  classical
  let C := fun (j : κ) (x : ℝ) => Real.cos ((k j:ℝ)*x)
  let S := fun (j : κ) (x : ℝ) => Real.sin ((k j:ℝ)*x)
  let F := fun x => ∑ j, a j * C j x
  let b := fun j => -(a j * (k j:ℝ))
  let D := fun x => ∑ j, b j * S j x
  have hC (j : κ) : Continuous (C j) := by dsimp [C]; fun_prop
  have hS (j : κ) : Continuous (S j) := by dsimp [S]; fun_prop
  have hF : Continuous F := continuous_finsetSum _ fun j _ => continuous_const.mul (hC j)
  have hD : Continuous D := continuous_finsetSum _ fun j _ => continuous_const.mul (hS j)
  have hFD (x : ℝ) : HasDerivAt F (D x) x := by
    apply HasDerivAt.fun_sum
    intro j _
    change HasDerivAt (fun y => a j * Real.cos ((k j:ℝ)*y))
      ((-(a j * (k j:ℝ))) * Real.sin ((k j:ℝ)*x)) x
    convert! (((hasDerivAt_id x).const_mul (k j:ℝ)).cos.const_mul (a j)) using 1
    simp only [id_eq, mul_one]
    ring
  have eqC : (∫ x in (0:ℝ)..2*Real.pi, F x^2) = Real.pi*(∑ j, a j^2) :=
    parseval_of_pair C hC (fun i j => by
      simpa [C,hinj.eq_iff] using integral_mode_pair false (hfreq i).1 (hfreq j).1) a
  have eqD : (∫ x in (0:ℝ)..2*Real.pi, D x^2) = Real.pi*(∑ j, b j^2) :=
    parseval_of_pair S hS (fun i j => by
      simpa [S,hinj.eq_iff] using integral_mode_pair true (hfreq i).1 (hfreq j).1) b
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hb : (∑ j, b j^2) ≤ (2*(n:ℝ))^2*(∑ j, a j^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj : (k j:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast (hfreq j).2
    calc
      b j^2 = (k j:ℝ)^2 * a j^2 := by dsimp [b]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by gcongr) (sq_nonneg _)
  have H := separated_energy hD hFD φ hh hnr (by positivity : (0:ℝ) ≤ 2*Real.pi)
    (fun i => (hφ i).1) (fun i => by linarith [(hφ i).2]) hsep
  have hF2 : Continuous (fun x => F x^2) := hF.pow 2
  have hE : Continuous (fun x => (n:ℝ)*F x^2 + D x^2/(n:ℝ)) := by fun_prop
  have hW : Continuous (fun x => h*((n:ℝ)*F x^2 + D x^2/(n:ℝ))) := by fun_prop
  have hA : Continuous (fun x => (n:ℝ)*F x^2) := by fun_prop
  have hB : Continuous (fun x => D x^2/(n:ℝ)) := by fun_prop
  rw [intervalIntegral.integral_add (hF2.intervalIntegrable _ _)
    (hW.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div, eqC, eqD] at H
  have HD : Real.pi*(∑ j, b j^2)/(n:ℝ) ≤
      Real.pi*4*(n:ℝ)*(∑ j, a j^2) := by
    apply (div_le_iff₀ hnr).2
    have := mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    nlinarith
  change (∑ i, F (φ i)^2) ≤ _
  refine le_of_mul_le_mul_left (a := h) ?_ hh
  calc
    h*(∑ i, F (φ i)^2) ≤ _ := H
    _ ≤ Real.pi*(∑ j, a j^2) + h*((n:ℝ)*(Real.pi*(∑ j, a j^2)) +
      Real.pi*4*(n:ℝ)*(∑ j, a j^2)) := by gcongr
    _ = _ := by field_simp; ring


/-- Direct scalar synthesis estimate for the indexed rows returned by
`Erdos1133.SparseSampling`. It applies to any subset of positive distinct
frequencies at most 2n, including a shifted dyadic band. No fit hypothesis
on C or L is needed, since we truncate the forward arcs at length one. -/
theorem separated_range_synthesis (p : ℕ) (φ : ℕ → ℝ) (s : Finset ℕ)
    (k : ℕ → ℕ) (a : ℕ → ℝ) {n : ℕ} {C L : ℝ} (hn : 0 < n)
    (hC : 0 < C) (hL : 0 < L) (hφ : ∀ i < p, φ i ∈ Icc 0 Real.pi)
    (hsep : ∀ i < p, ∀ j < p, i ≠ j → 1/(2*C*(L*n)) < |φ i - φ j|)
    (hk : Set.InjOn k (s : Set ℕ)) (hfreq : ∀ j ∈ s, 0 < k j ∧ k j ≤ 2*n) :
    (∑ i ∈ Finset.range p, (∑ j ∈ s, a j * Real.cos ((k j:ℝ)*φ i))^2) ≤
      (Real.pi*(2*C*L+6))*(n:ℝ)*(∑ j ∈ s, a j^2) := by
  classical
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnone : (1:ℝ) ≤ n := by exact_mod_cast hn
  let η : ℝ := 1/(2*C*(L*n))
  let h : ℝ := min η 1
  have hη : 0 < η := by dsimp [η]; positivity
  have hh : 0 < h := lt_min hη zero_lt_one
  have hfit : h ≤ Real.pi :=
    (min_le_right ..).trans (by linarith [Real.one_le_pi_div_two])
  have hnodes (i j : Fin p) (hij : i ≠ j) : h ≤ |φ i - φ j| :=
    (min_le_left ..).trans (hsep i i.isLt j j.isLt (fun he => hij (Fin.ext he))).le
  have hinj : Function.Injective (fun j : s => k j) := by
    intro i j he
    exact Subtype.ext (hk i.2 j.2 he)
  have H := high_band_sampling (fun i : Fin p => φ i) (fun j : s => k j)
    hinj (fun j => a j) hn (fun j => hfreq j j.2) hh hfit (fun i => hφ i i.isLt) hnodes
  have hf (i : ℕ) : (∑ j : s, a j * Real.cos ((k j:ℝ)*φ i)) =
      ∑ j ∈ s, a j * Real.cos ((k j:ℝ)*φ i) :=
    Finset.sum_coe_sort s (fun j => a j * Real.cos ((k j:ℝ)*φ i))
  simp only [hf, Finset.sum_coe_sort s (fun j => a j^2),
    Fin.sum_univ_eq_sum_range (fun i => (∑ j ∈ s, a j*Real.cos ((k j:ℝ)*φ i))^2) p] at H
  have hinv : 1/h ≤ 2*C*L*n+n := by
    by_cases ha : η ≤ 1
    · simp only [h, min_eq_left ha, η, one_div, inv_inv]
      nlinarith
    · simp only [h, min_eq_right (le_of_not_ge ha), div_one]
      linarith [show 0 ≤ 2*C*L*(n:ℝ) by positivity]
  have hconstant : Real.pi*(1/h+5*(n:ℝ)) ≤ (Real.pi*(2*C*L+6))*(n:ℝ) := by
    calc
      Real.pi*(1/h+5*(n:ℝ)) ≤ Real.pi*(2*C*L*n+n+5*n) :=
        mul_le_mul_of_nonneg_left (add_le_add hinv (le_refl _)) Real.pi_pos.le
      _ = _ := by ring
  exact H.trans (mul_le_mul_of_nonneg_right hconstant
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Erdos1133.Sampling

end

section

open scoped BigOperators
namespace Erdos1133Reconstruction

/-- A bounded functional on a finite supremum-norm product has real
coordinate weights whose absolute values sum to at most the bound. -/
theorem weights_of_functional {ι : Type*} [Fintype ι] (g : (ι → ℝ) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖) :
    ∃ w : ι → ℝ, (∑ i, |w i|) ≤ C ∧ ∀ v, (∑ i, w i * v i) = g v := by
  classical
  let e (i : ι) : ι → ℝ := fun j => if i = j then 1 else 0
  let w (i : ι) : ℝ := g (e i)
  have repr (v : ι → ℝ) : (∑ i, w i * v i) = g v := by
    have hex : (∑ i, v i • e i) = v := by
      funext j
      simp [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
    calc
      (∑ i, w i * v i) = ∑ i, g (v i • e i) := by simp [w, smul_eq_mul, mul_comm]
      _ = g v := by rw [← map_sum, hex]
  let s (i : ι) : ℝ := if 0 ≤ w i then 1 else -1
  have hs : ‖s‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    by_cases hi : 0 ≤ w i <;> simp [s, hi]
  have hw (i : ι) : |w i| = w i * s i := by
    by_cases hi : 0 ≤ w i
    · simp [s, hi, abs_of_nonneg hi]
    · simp [s, hi, abs_of_neg (lt_of_not_ge hi)]
  refine ⟨w, ?_, repr⟩
  calc
    (∑ i, |w i|) = g s := by simp_rw [hw]; exact repr s
    _ ≤ ‖g s‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ C * ‖s‖ := hg s
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hs hC
    _ = C := mul_one _

end Erdos1133Reconstruction

end

section

/-! Sparsifying finite angular samples without losing more than a factor two
in the norming constant. The Lipschitz bound is passed as a hypothesis. -/

open scoped NNReal ENNReal

namespace Erdos1133.SparseSampling

/-- A finite set of real nodes contains a covering subset with pairwise
distance strictly greater than the covering radius. -/
theorem separated_cover (X : Finset ℝ) (h : ℝ≥0) :
    ∃ Y : Finset ℝ, Y ⊆ X ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → (h : ℝ) < |x-y|) ∧
      ∀ x ∈ X, ∃ y ∈ Y, |x-y| ≤ (h : ℝ) := by
  classical
  let Z := Metric.maximalSeparatedSet h (X : Set ℝ)
  have hsub : Z ⊆ (X : Set ℝ) := Metric.maximalSeparatedSet_subset
  have hf : Z.Finite := X.finite_toSet.subset hsub
  have hp : Metric.packingNumber h (X : Set ℝ) ≠ ⊤ :=
    ((Metric.packingNumber_le_encard_self (X : Set ℝ)).trans_lt
      X.finite_toSet.encard_lt_top).ne
  have hs : Metric.IsSeparated (h : ℝ≥0∞) Z := Metric.isSeparated_maximalSeparatedSet
  have hc : Metric.IsCover h (X : Set ℝ) Z := Metric.isCover_maximalSeparatedSet hp
  refine ⟨hf.toFinset, fun x hx => hsub (hf.mem_toFinset.mp hx), ?_, ?_⟩
  · intro x hx y hy hxy
    have hh := hs (hf.mem_toFinset.mp hx) (hf.mem_toFinset.mp hy) hxy
    change (h : ℝ≥0∞) < edist x y at hh
    rw [edist_nndist, ENNReal.coe_lt_coe] at hh
    simpa only [coe_nndist, Real.dist_eq] using (NNReal.coe_lt_coe.mpr hh)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hc (show x ∈ (X : Set ℝ) from hx)
    change edist x y ≤ (h : ℝ≥0∞) at hxy
    rw [edist_nndist, ENNReal.coe_le_coe] at hxy
    exact ⟨y, hf.mem_toFinset.mpr hy,
      by simpa only [coe_nndist, Real.dist_eq] using (NNReal.coe_le_coe.mpr hxy)⟩

/-- The same subset works for every member of the function family. In the
application, M is the continuous supremum and L*n is its Bernstein factor. -/
theorem sparsify_norming_set {α : Type*} (X : Finset ℝ) (Q : α → ℝ → ℝ)
    (M : α → ℝ) {C L : ℝ} (n : ℕ) (h : ℝ≥0)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : ∀ a, 0 ≤ M a)
    (hsmall : C * (L*n) * (h : ℝ) ≤ 1/2)
    (hnorm : ∀ a, ∃ x ∈ X, M a ≤ C * |Q a x|)
    (hlip : ∀ a x, x ∈ X → ∀ y, y ∈ X →
      |Q a x - Q a y| ≤ (L*n) * M a * |x-y|) :
    ∃ Y : Finset ℝ, Y ⊆ X ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → (h : ℝ) < |x-y|) ∧
      ∀ a, ∃ y ∈ Y, M a ≤ (2*C) * |Q a y| := by
  obtain ⟨Y, hYX, hsep, hcov⟩ := separated_cover X h
  refine ⟨Y, hYX, hsep, ?_⟩
  intro a
  obtain ⟨x, hx, hdominates⟩ := hnorm a
  obtain ⟨y, hy, hxy⟩ := hcov x hx
  refine ⟨y, hy, ?_⟩
  have hdiff := (hlip a x hx y (hYX hy)).trans
    (mul_le_mul_of_nonneg_left hxy (mul_nonneg (mul_nonneg hL (Nat.cast_nonneg _)) (hM a)))
  have htriangle := abs_sub_abs_le_abs_sub (Q a x) (Q a y)
  have hxyval : |Q a x| ≤ |Q a y| + (L*n) * M a * (h : ℝ) := by
    linarith only [hdiff, htriangle]
  have hbound := hdominates.trans (mul_le_mul_of_nonneg_left hxyval hC)
  have habsorb := mul_le_mul_of_nonneg_right hsmall (hM a)
  nlinarith only [hbound, habsorb]

/-- At positive degree and positive constants, the radius can be chosen to be
exactly the reciprocal of 2*C*L*n, uniformly over the input node set. -/
theorem sparsify_at_degree {α : Type*} (X : Finset ℝ) (Q : α → ℝ → ℝ)
    (M : α → ℝ) {C L : ℝ} {n : ℕ} (hC : 0 < C) (hL : 0 < L) (hn : 0 < n)
    (hM : ∀ a, 0 ≤ M a)
    (hnorm : ∀ a, ∃ x ∈ X, M a ≤ C * |Q a x|)
    (hlip : ∀ a x, x ∈ X → ∀ y, y ∈ X →
      |Q a x - Q a y| ≤ (L*n) * M a * |x-y|) :
    ∃ Y : Finset ℝ, Y ⊆ X ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1/(2*C*(L*n)) < |x-y|) ∧
      ∀ a, ∃ y ∈ Y, M a ≤ (2*C) * |Q a y| := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let h : ℝ≥0 := ⟨1/(2*C*(L*n)), by positivity⟩
  have hsmall : C * (L*n) * (h : ℝ) ≤ 1/2 := by
    change C * (L*n) * (1/(2*C*(L*n))) ≤ 1/2
    apply le_of_eq
    field_simp [hC.ne', hL.ne', hn'.ne']
  exact sparsify_norming_set X Q M n h hC.le hL.le hM hsmall hnorm hlip

end Erdos1133.SparseSampling

end

section

/-! A sharp endpoint bound for the odd part of a trigonometric polynomial. -/

open Polynomial
open scoped BigOperators

namespace Erdos1133.BernsteinEndpoint

/-- The bound follows by applying the one-sided Chebyshev endpoint derivative
estimate to a degree-`2*n` polynomial taking values in `[-1,1]`. -/
theorem odd_endpoint {n : ℕ} (B : Polynomial ℝ) (hdeg : B.natDegree < n)
    {M : ℝ} (hM : 0 < M)
    (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, (1-u^2) * (B.eval u)^2 ≤ M^2) :
    |B.eval 1| ≤ (n : ℝ) * M := by
  let G : Polynomial ℝ := (1-X^2) * B^2
  let P : Polynomial ℝ := 1 - C (2 / M^2) * G
  have hX : ((1 : Polynomial ℝ) - X^2).natDegree ≤ 2 := by
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hG : G.natDegree ≤ 2*n := by
    have hd := natDegree_mul_le (p := (1:Polynomial ℝ)-X^2) (q := B^2)
    have hp := natDegree_pow_le (p := B) (n := 2)
    dsimp [G]
    omega
  have hP : P.degree ≤ ↑(2*n) := by
    apply degree_le_of_natDegree_le
    apply (natDegree_sub_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_le _ _).trans hG)
  have hMsq : 0 < M^2 := by positivity
  have hbP (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : |P.eval u| ≤ 1 := by
    have hu2 : u^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hu.1)]
    have ha := mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg (B.eval u))
    have hh := hb u hu
    change |(1 - C (2 / M^2) * ((1-X^2)*B^2)).eval u| ≤ 1
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X]
    apply abs_le.mpr
    constructor
    · field_simp [hMsq.ne']
      nlinarith
    · have := mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hMsq.le) ha
      linarith
  have hupper : P.derivative.eval 1 ≤ ((2*n:ℕ):ℝ)^2 := by
    simpa [Chebyshev.derivative_T_eval_one] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
        (k := 1) (x := 1) le_rfl hP hbP)
  have heval : P.derivative.eval 1 = 4*(B.eval 1)^2/M^2 := by
    simp [P, G, derivative_mul, derivative_pow]
    ring
  rw [heval, div_le_iff₀ hMsq] at hupper
  push_cast at hupper
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hM.le)).mp
  rw [sq_abs]
  nlinarith [hupper]

private theorem weighted_odd (B : Polynomial ℝ) (Q : ℝ → ℝ) (x : ℝ) {M : ℝ}
    (hM : 0 < M) (hb : ∀ y, |Q y| ≤ M)
    (hodd : ∀ t, Q (x+t) - Q (x-t) = 2 * (B.eval (Real.cos t) * Real.sin t))
    (u : ℝ) (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    (1-u^2)*(B.eval u)^2 ≤ M^2 := by
  let t := Real.arccos u
  have hc : Real.cos t = u := Real.cos_arccos hu.1 hu.2
  have hdiff := (abs_sub (Q (x+t)) (Q (x-t))).trans (add_le_add (hb _) (hb _))
  rw [hodd, abs_mul, abs_of_pos (show (0:ℝ)<2 by norm_num), hc] at hdiff
  have hprod : |B.eval u * Real.sin t| ≤ M := by linarith
  have hh := (sq_le_sq₀ (abs_nonneg _) hM.le).mpr hprod
  rw [sq_abs, mul_pow] at hh
  have hs := Real.sin_sq_add_cos_sq t
  rw [hc] at hs
  rw [show 1-u^2 = Real.sin t^2 by linarith, mul_comm]
  exact hh

/-- The endpoint estimate applied to the scaled polynomial yields a bound on the whole interval. -/
theorem odd_point {n : ℕ} (B : Polynomial ℝ) (hdeg : B.natDegree < n)
    {M : ℝ} (hM : 0 < M)
    (hb : ∀ u ∈ Set.Icc (-1:ℝ) 1, (1-u^2)*(B.eval u)^2 ≤ M^2)
    (v : ℝ) (hv : |v| ≤ 1) : |B.eval v| ≤ (n:ℝ)*M := by
  let L : Polynomial ℝ := C v * X
  have hL : L.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hD : (B.comp L).natDegree < n :=
    lt_of_le_of_lt (natDegree_comp_le.trans
      ((Nat.mul_le_mul_left _ hL).trans_eq (Nat.mul_one _))) hdeg
  have b (u : ℝ) (hu : u ∈ Set.Icc (-1:ℝ) 1) :
      (1-u^2)*((B.comp L).eval u)^2 ≤ M^2 := by
    have hau : |u| ≤ 1 := abs_le.mpr hu
    have hvu : |v*u| ≤ |u| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hv
    have hs := (sq_le_sq).mpr hvu
    have he := hb (v*u) (abs_le.mp (hvu.trans hau))
    simp only [L, eval_comp, eval_mul, eval_C, eval_X]
    exact (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)).trans he
  simpa [L, eval_comp] using odd_endpoint (B.comp L) hD hM b

private theorem sin_abs_bound (x : ℝ) : |Real.sin x| ≤ |x| := by
  have hp (u : ℝ) (hu : 0 ≤ u) : |Real.sin u| ≤ u := by
    by_cases h1 : 1 ≤ u
    · exact (Real.abs_sin_le_one u).trans h1
    have hu1 : u ≤ 1 := le_of_not_ge h1
    rcases hu.eq_or_lt with hz | hz
    · subst u; simp
    have ht := (abs_le.mp (Real.sin_bound (x := u) (by rwa [abs_of_nonneg hu]))).2
    rw [abs_of_nonneg hu] at ht
    have hs2 : u^2 ≤ 1 := (sq_le_one_iff_abs_le_one u).mpr (by rwa [abs_of_nonneg hu])
    have hs5 : u^5 ≤ u^3 := by
      rw [show u^5=u^3*u^2 by ring]
      exact mul_le_of_le_one_right (by positivity) hs2
    rw [abs_of_nonneg (Real.sin_pos_of_pos_of_le_one hz hu1).le]
    linarith [show 0 ≤ u^3 by positivity]
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using hp x hx
  · have hnx : x ≤ 0 := le_of_not_ge hx
    simpa only [Real.sin_neg, abs_neg, abs_of_nonpos hnx] using hp (-x) (neg_nonneg.mpr hnx)

open Finset

noncomputable def trig (n : ℕ) (a b : ℕ → ℝ) (c y : ℝ) : ℝ :=
  c + ∑ k ∈ range n,
    (a k * Real.cos (((k:ℝ)+1)*y) + b k * Real.sin (((k:ℝ)+1)*y))

private theorem odd_representation (n : ℕ) (hn : n ≠ 0) (a b : ℕ → ℝ) (c x : ℝ) :
    ∃ B : Polynomial ℝ, B.natDegree < n ∧ ∀ t,
      trig n a b c (x+t)-trig n a b c (x-t) = 2*(B.eval (Real.cos t)*Real.sin t) := by
  let s := fun k : ℕ =>
    -a k * Real.sin (((k:ℝ)+1)*x) + b k * Real.cos (((k:ℝ)+1)*x)
  let B := ∑ k ∈ range n, C (s k) * Chebyshev.U ℝ (k:ℤ)
  have hBd : B.natDegree ≤ n-1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    have hk' := mem_range.mp hk
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Chebyshev.natDegree_U_natCast]
    omega
  have hodd (t : ℝ) :
      trig n a b c (x+t) - trig n a b c (x-t) =
      2*(B.eval (Real.cos t)*Real.sin t) := by
    let v := fun (k : ℕ) (z : ℝ) =>
      a k * Real.cos (((k:ℝ)+1)*z) + b k * Real.sin (((k:ℝ)+1)*z)
    change (c + ∑ k ∈ range n, v k (x+t)) - (c + ∑ k ∈ range n, v k (x-t)) = _
    rw [show (c + ∑ k ∈ range n, v k (x+t)) - (c + ∑ k ∈ range n, v k (x-t))
        = (∑ k ∈ range n, v k (x+t)) - ∑ k ∈ range n, v k (x-t) by ring,
      ←sum_sub_distrib]
    simp only [B, eval_finsetSum, eval_mul, eval_C, sum_mul, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hu : (Chebyshev.U ℝ (k:ℤ)).eval (Real.cos t)*Real.sin t =
        Real.sin (((k:ℝ)+1)*t) := by simp
    rw [mul_assoc (s k), hu]
    simp only [v, s, mul_add, mul_sub, Real.cos_add, Real.sin_add,
      Real.cos_sub, Real.sin_sub]
    ring
  exact ⟨B, by omega, hodd⟩

theorem lipschitz (n : ℕ) (a b : ℕ → ℝ) (c : ℝ) {M : ℝ}
    (hM : 0 < M) (hb : ∀ y, |trig n a b c y| ≤ M) (x y : ℝ) :
    |trig n a b c x-trig n a b c y| ≤ (n:ℝ)*M*|x-y| := by
  by_cases hn : n=0
  · simp [hn,trig]
  let z := (x+y)/2
  let t := (x-y)/2
  obtain ⟨B,hd,ho⟩ := odd_representation n hn a b c z
  have hB := odd_point B hd hM (weighted_odd B _ z hM hb ho) (Real.cos t) (Real.abs_cos_le_one t)
  have he := ho t
  rw [show z+t=x by dsimp [z,t]; ring, show z-t=y by dsimp [z,t]; ring] at he
  rw [he, abs_mul, abs_mul, abs_of_pos (show (0:ℝ)<2 by norm_num)]
  have hi := mul_le_mul hB (sin_abs_bound t) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hM.le)
  dsimp [t] at hi
  rw [abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num)] at hi
  linarith

private theorem sequence_expansion (S : Polynomial.Sequence ℝ) (n : ℕ)
    (P : Polynomial ℝ) (hd : P.natDegree < n) :
    ∃ c : ℕ → ℝ, ∑ k ∈ range n, C (c k) * S k = P := by
  have hm : P ∈ Submodule.span ℝ (S '' (range n : Set ℕ)) := by
    rw [Finset.coe_range, S.span_degreeLT (fun k _ =>
      isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero k)))]
    apply Polynomial.mem_degreeLT.mpr
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hm
  exact ⟨c, by simpa only [Polynomial.smul_eq_C_mul] using hc⟩

/-- The `A(cos x) + sin x B(cos x)` form in the proposed reduction. -/
theorem polynomial_lipschitz (d : ℕ) (A B : Polynomial ℝ) (hA : A.natDegree ≤ d)
    (hB : B.natDegree < d) :
    let q := fun s : ℝ => A.eval (Real.cos s) + Real.sin s * B.eval (Real.cos s)
    ∀ M : ℝ, (∀ s, |q s| ≤ M) →
      ∀ s u : ℝ, |q s - q u| ≤ d*M*|s-u| := by
  dsimp only
  intro M hbd s u
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbd 0)
  rcases hM0.eq_or_lt with heq | hM
  · subst M
    have hz (y : ℝ) : A.eval (Real.cos y) + Real.sin y * B.eval (Real.cos y) = 0 :=
      abs_nonpos_iff.mp (hbd y)
    simp [hz]
  let U : Polynomial.Sequence ℝ :=
    ⟨fun k => Chebyshev.U ℝ (k:ℤ), fun k => Chebyshev.degree_U_natCast ℝ k⟩
  obtain ⟨a, ha⟩ := sequence_expansion (Chebyshev.chebyshevTsequence ℝ) (d+1) A (by omega)
  obtain ⟨b, hb⟩ := sequence_expansion U d B hB
  change ∑ k ∈ range (d+1), C (a k) * Chebyshev.T ℝ (k:ℤ) = A at ha
  change ∑ k ∈ range d, C (b k) * Chebyshev.U ℝ (k:ℤ) = B at hb
  have hrep (y : ℝ) : trig d (fun k => a (k+1)) b (a 0) y =
      A.eval (Real.cos y) + Real.sin y * B.eval (Real.cos y) := by
    have h₁ := congrArg (fun P : Polynomial ℝ => P.eval (Real.cos y)) ha
    have h₂ := congrArg (fun P : Polynomial ℝ => P.eval (Real.cos y)) hb
    simp only [eval_finsetSum, eval_mul, eval_C, Chebyshev.T_real_cos,
      Int.cast_natCast] at h₁ h₂
    rw [sum_range_succ'] at h₁
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Real.cos_zero,
      mul_one] at h₁
    have hsin : ∑ k ∈ range d, b k * Real.sin (((k:ℝ)+1)*y) =
        B.eval (Real.cos y) * Real.sin y := by
      rw [← h₂, sum_mul]
      apply sum_congr rfl
      intro k hk
      rw [mul_assoc, Chebyshev.U_real_cos]
      simp
    dsimp only [trig]
    rw [sum_add_distrib, hsin]
    linarith
  simpa only [hrep] using
    lipschitz d (fun k => a (k+1)) b (a 0) hM (fun y => by simpa only [hrep] using hbd y) s u

end Erdos1133.BernsteinEndpoint

end

section

namespace Erdos1133.CircleTransfer

open Polynomial Real Set
open scoped BigOperators

theorem circle_of_growth
    (growth : ∀ C : ℝ, 0 < C →
      ∃ ε > (0:ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ, (m:ℝ) ≤ (1+ε)*n →
      ∀ node : Fin m → ℝ, (∀ i, node i ∈ Set.Icc 0 Real.pi) →
      ∃ (a : Fin (n+1) → ℝ) (x : ℝ), 0 < |Norming.value a x| ∧
        ∀ i, C*|Norming.value a (node i)| < |Norming.value a x|) :
    ∀ K > (0 : ℝ), ∃ η > (0 : ℝ), ∃ D : ℕ, ∀ d ≥ D,
      ∀ Y : Finset ℝ, (Y.card : ℝ) ≤ (1+η)*d →
        ∃ A B : Polynomial ℝ, A.natDegree ≤ d ∧ B.natDegree < d ∧
          let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
          (∀ s ∈ Y, |q s| ≤ 1 ∧ |q (-s)| ≤ 1) ∧
            ∃ t ∈ Icc (0 : ℝ) π, K < |q t| ∧ ∀ s, |q s| ≤ |q t| := by
  classical
  intro K hK
  have hC : 0 < K+1 := by linarith
  obtain ⟨η,hη,D,hgrow⟩ := growth (K+1) hC
  refine ⟨η,hη,max 1 D,?_⟩
  intro d hd Y hY
  have hd0 : 0 < d := (le_max_left 1 D).trans hd
  let e : Y ≃ Fin Y.card := Fintype.equivFinOfCardEq (Fintype.card_coe Y)
  let fold := fun u : ℝ => arccos (cos u)
  have hfold (u : ℝ) : cos (fold u) = cos u :=
    cos_arccos (neg_one_le_cos _) (cos_le_one _)
  let node := fun i : Fin Y.card => fold (e.symm i : ℝ)
  have hrange (i : Fin Y.card) : node i ∈ Icc 0 π := ⟨arccos_nonneg _, arccos_le_pi _⟩
  obtain ⟨a,x,hx,hsmall⟩ := hgrow d ((le_max_right 1 D).trans hd) Y.card hY node hrange
  let P : Polynomial ℝ := ∑ k : Fin (d+1), C (a k)*Chebyshev.T ℝ (k.val:ℤ)
  have hPdeg : P.natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    simpa [Chebyshev.natDegree_T] using (Nat.le_of_lt_succ k.isLt)
  have heval (t : ℝ) : P.eval (cos t) = Norming.value a t := by
    simp [P, Norming.value, Polynomial.eval_finsetSum, Chebyshev.T_real_cos]
  have hval (u v : ℝ) (h : cos u = cos v) : Norming.value a u = Norming.value a v := by
    rw [←heval, ←heval, h]
  let r := (K+1)/|Norming.value a x|
  have hr : 0 < r := div_pos hC hx
  have hrx : r*|Norming.value a x| = K+1 := div_mul_cancel₀ _ hx.ne'
  have hsam (s : ℝ) (hs : s ∈ Y) : r*|Norming.value a s| ≤ 1 := by
    let i := e ⟨s,hs⟩
    have hs' : cos (node i) = cos s := by simp [node, i, hfold]
    have h := hsmall i
    rw [hval _ _ hs'] at h
    dsimp [r]
    rw [div_mul_eq_mul_div, div_le_iff₀ hx, one_mul]
    exact h.le
  obtain ⟨z,hmax⟩ := Norming.exists_peak a
  let t := fold z
  have ht : Norming.value a t = Norming.value a z := hval _ _ (hfold z)
  refine ⟨C r * P,0,(natDegree_C_mul_le _ _).trans hPdeg,by simpa using hd0,?_⟩
  dsimp only
  have hq (u : ℝ) :
      |(C r * P).eval (cos u) + sin u * (0:Polynomial ℝ).eval (cos u)|
        = r*|Norming.value a u| := by simp [heval, abs_mul, abs_of_pos hr]
  simp only [hq]
  constructor
  · intro s hs
    exact ⟨hsam s hs, by rw [hval _ _ (cos_neg s)]; exact hsam s hs⟩
  · refine ⟨t, ⟨arccos_nonneg _, arccos_le_pi _⟩, ?_, ?_⟩
    · rw [ht]
      have h := mul_le_mul_of_nonneg_left (hmax x) hr.le
      linarith
    · intro s
      rw [ht]
      exact mul_le_mul_of_nonneg_left (hmax s) hr.le

end Erdos1133.CircleTransfer

end

section

/-! Finite cosine orthogonality and the trace comparison for Erdős 1133, R1.H2. -/

namespace Erdos1133.CosineTrace

open Finset
open scoped BigOperators

noncomputable def angle (N t : ℕ) : ℝ := ((t : ℝ) + 1/2) * Real.pi / N
noncomputable def mode (N k t : ℕ) : ℝ := Real.cos ((k : ℝ) * angle N t)

theorem sum_mode_zero {N k : ℕ} (hk : 0 < k) (hkn : k < 2*N) :
    ∑ t ∈ range N, mode N k t = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) < 2*(N : ℝ) := by exact_mod_cast hkn
  let a : ℝ := (k : ℝ) * Real.pi / N
  have ha : 0 < a := by dsimp [a]; positivity
  have hapi : a / 2 < Real.pi := by
    dsimp [a]
    rw [div_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hkn' Real.pi_pos]
  have hsin := Real.sin_pos_of_pos_of_lt_pi (show 0 < a/2 by linarith) hapi
  have hNa : (N : ℝ) * a = (k : ℝ) * Real.pi := by
    dsimp [a]; field_simp
  have hzero : Real.sin ((N : ℝ)*a) = 0 := by rw [hNa, Real.sin_nat_mul_pi]
  have h := midpoint_cosine_sum N a
  rw [hzero] at h
  have hsum := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hsin.ne')
  have hterm (t : ℕ) : mode N k t = Real.cos (((t:ℝ)+1/2)*a) := by
    unfold mode angle
    congr 1
    dsimp [a]; ring
  simpa only [hterm] using hsum

theorem mode_product {N k l : ℕ} (hle : l ≤ k) (t : ℕ) :
    2*(mode N k t * mode N l t) = mode N (k+l) t + mode N (k-l) t := by
  unfold mode
  push_cast [Nat.cast_sub hle]
  rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  ring

theorem sum_mode_product {N k l : ℕ} (hlo : l < k) (hhi : k+l < 2*N) :
    ∑ t ∈ range N, mode N k t * mode N l t = 0 := by
  have hsum := Finset.sum_congr (s₁ := range N) rfl
    (fun t _ => mode_product (N := N) hlo.le t)
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
      sum_mode_zero (by omega) hhi,
      sum_mode_zero (by omega) (by omega)] at hsum
  linarith

theorem sum_mode_square {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    ∑ t ∈ range N, mode N k t * mode N k t = (N : ℝ)/2 := by
  have hsum := Finset.sum_congr (s₁ := range N) rfl
    (fun t _ => mode_product (N := N) (k := k) (l := k) le_rfl t)
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
      sum_mode_zero (by omega) (by omega)] at hsum
  simp [mode] at hsum
  unfold mode
  linarith


/-- Orthogonality in the normalization used by the rank estimate. -/
theorem gram_positive {N k l : ℕ} (hk : 0 < k) (hkN : k < N) (hlN : l < N) :
    (∑ t ∈ range N, mode N k t * mode N l t) =
      if k = l then (N : ℝ)/2 else 0 := by
  split_ifs with h
  · subst l
    exact sum_mode_square hk hkN
  · rcases lt_or_gt_of_ne h with hkl | hlk
    · simpa only [mul_comm] using sum_mode_product (N := N) hkl (by omega)
    · exact sum_mode_product hlk (by omega)


/-- Includes the constant column, whose unnormalized squared length is N. -/
theorem gram_all_low {N k l : ℕ} (hkN : k < N) (hlN : l < N) :
    (∑ t ∈ range N, mode N k t * mode N l t) =
      if k = l then (if k = 0 then (N : ℝ) else (N : ℝ)/2) else 0 := by
  by_cases hk : k = 0
  · subst k
    by_cases hl : l = 0
    · subst l
      simp [mode]
    · have h := sum_mode_product (N := N) (l := 0) (k := l) (Nat.pos_of_ne_zero hl) (by omega)
      simpa [mode, hl, Ne.symm hl] using h
  · simpa [hk] using gram_positive (Nat.pos_of_ne_zero hk) hkN hlN

/-- The diagonal of the evaluation/reconstruction matrix at frequency k. -/
noncomputable def diag (N p : ℕ) (w : ℕ → ℕ → ℝ) (v : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ t ∈ range N, mode N k t * ∑ i ∈ range p, w t i * v k i) / N

/-- Coordinate form of the high-frequency diagonal for connecting the rank bound. -/
theorem diag_as_coeff_sum (N p : ℕ) (w v : ℕ → ℕ → ℝ) (k : ℕ) :
    diag N p w v k =
      ∑ i ∈ range p, ((∑ t ∈ range N, mode N k t * w t i)/(N : ℝ)) * v k i := by
  exact coordinate_diagonal N p (mode N k) w (v k)

theorem low_diag {N p k : ℕ} {w v : ℕ → ℕ → ℝ} (hk : 0 < k) (hkN : k < N)
    (hw : ∀ t < N, ∑ i ∈ range p, w t i * v k i = mode N k t) :
    diag N p w v k = 1/2 := by
  unfold diag
  have hr : (∑ t ∈ range N, mode N k t * ∑ i ∈ range p, w t i * v k i) =
      ∑ t ∈ range N, mode N k t * mode N k t :=
    Finset.sum_congr rfl (fun t ht => by rw [hw t (mem_range.mp ht)])
  rw [hr, sum_mode_square hk hkN]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

theorem high_annihilates_low {N p k l : ℕ} {w v : ℕ → ℕ → ℝ}
    (hlo : l < k) (hhi : k+l < 2*N)
    (hw : ∀ t < N, ∑ i ∈ range p, w t i * v l i = mode N l t) :
    ∑ i ∈ range p, (∑ t ∈ range N, mode N k t * w t i) * v l i = 0 := by
  exact reconstructed_orthogonality N p (mode N k) (mode N l) w (v l) hw
    (sum_mode_product hlo hhi)

noncomputable def tensorMode (N : ℕ) (v : ℕ → ℕ → ℝ) (k : ℕ) (t i : ℕ) : ℝ :=
  mode N k t * v k i

theorem trace_tensor (N p : ℕ) (w v : ℕ → ℕ → ℝ) (k : ℕ) :
    rowTrace N p w (tensorMode N v k) = diag N p w v k := by
  exact trace_elementary_tensor N p w (mode N k) (v k)

/-- Final contradiction once the node separation and high-frequency estimates are supplied. -/
theorem impossible_trace {N p : ℕ} (S : Finset ℕ)
    (w v : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (b : ℕ → ℝ)
    {C D E : ℝ} (hN : 0 < N) (hD : 0 ≤ D) (hb : ∀ j ∈ S, 0 ≤ b j)
    (hw : ∀ t < N, ∑ i ∈ range p, |w t i| ≤ C)
    (hfreq : ∀ j ∈ S, 0 < lo j ∧ lo j < N)
    (hrep : ∀ j ∈ S, ∀ t < N, ∑ i ∈ range p, w t i * v (lo j) i = mode N (lo j) t)
    (hk : let K := ∑ j ∈ S, b j • (tensorMode N v (lo j) - tensorMode N v (hi j))
          ∀ t < N, ∀ i < p, |K t i| ≤ D)
    (hhigh : ∑ j ∈ S, b j * |diag N p w v (hi j)| ≤ E)
    (hlarge : C*D + E < (1/2 : ℝ) * ∑ j ∈ S, b j) : False := by
  apply finite_trace_contradiction S N p w b
    (fun j => tensorMode N v (lo j)) (fun j => tensorMode N v (hi j))
    hN hD hb hw _ hk _ hlarge
  · intro j hj
    rw [trace_tensor]
    exact low_diag (hfreq j hj).1 (hfreq j hj).2 (hrep j hj)
  · simpa only [trace_tensor] using hhigh

/-- Converts an unweighted high-frequency estimate into the term needed in the trace. -/
theorem weighted_high {J L : ℕ} (hJ : 0 < J) (d : ℕ → ℝ) :
    (∑ j ∈ Ico J L, (1/(j : ℝ)) * |d j|) ≤
      (1/(J : ℝ)) * ∑ j ∈ Ico J L, |d j| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact one_div_le_one_div_of_le (by exact_mod_cast hJ) (by exact_mod_cast (mem_Ico.mp hj).1)


/-- Combines the dyadic harmonic lower bound with the cosine trace comparison.
The only analytic inputs left here are a kernel bound and a high-frequency estimate. -/
theorem dyadic_contradiction {N p n J q : ℕ} (w v : ℕ → ℕ → ℝ)
    {C D E : ℝ} (hJ : 0 < J) (hD : 0 ≤ D) (hnN : n < N)
    (hend : 2^q*J ≤ n)
    (hw : ∀ t < N, ∑ i ∈ range p, |w t i| ≤ C)
    (hrep : ∀ k ≤ n, ∀ t < N, ∑ i ∈ range p, w t i * v k i = mode N k t)
    (hk : ∀ t < N, ∀ i < p, |∑ j ∈ Ico J (2^q*J),
      (mode N (n-j) t * v (n-j) i - mode N (n+j) t * v (n+j) i)/(j : ℝ)| ≤ D)
    (hhigh : (1/(J : ℝ)) * ∑ j ∈ Ico J (2^q*J), |diag N p w v (n+j)| ≤ E)
    (hlarge : C*D + E < (1/2 : ℝ) * ∑ j ∈ Ico J (2^q*J), 1/(j : ℝ)) : False := by
  let S := Ico J (2^q*J)
  let b := fun j : ℕ => 1/(j : ℝ)
  let lo := fun j : ℕ => n-j
  let hi := fun j : ℕ => n+j
  apply impossible_trace S w v lo hi b (by omega) hD (by intro j hj; dsimp [b]; positivity) hw
  · intro j hj
    have h := (mem_Ico.mp hj).2
    dsimp [lo]
    omega
  · intro j hj t ht
    exact hrep _ (Nat.sub_le _ _) t ht
  · dsimp only
    intro t ht i hi'
    simpa [S, b, lo, hi, tensorMode, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hk t ht i hi'
  · exact (weighted_high hJ (fun j => diag N p w v (n+j))).trans hhigh
  · exact hlarge

theorem normalized_annihilates_low {N p k l : ℕ} {w v : ℕ → ℕ → ℝ}
    (hlo : l < k) (hhi : k+l < 2*N)
    (hw : ∀ t < N, ∑ i ∈ range p, w t i * v l i = mode N l t) :
    ∑ i ∈ range p, ((∑ t ∈ range N, mode N k t * w t i)/(N:ℝ)) * v l i = 0 := by
  calc
    _ = (∑ i ∈ range p, (∑ t ∈ range N, mode N k t * w t i) * v l i)/(N:ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = 0 := by rw [high_annihilates_low hlo hhi hw, zero_div]

theorem gram_low_fin {N n : ℕ} (hn : n < N) (k l : Fin (n+1)) :
    (∑ t ∈ range N, mode N k.val t * mode N l.val t) =
      if k = l then (if k.val = 0 then (N:ℝ) else (N:ℝ)/2) else 0 := by
  have hg := gram_all_low (show k.val < N by omega) (show l.val < N by omega)
  by_cases he : k = l
  · subst l
    simpa only [if_pos rfl] using hg
  · have hv : k.val ≠ l.val := fun heq => he (Fin.ext heq)
    simpa only [if_neg he, if_neg hv] using hg

theorem gram_shifted {N n j k : ℕ} (hN : 2*n < N) (hj : 0 < j) (hjn : j ≤ n)
    (hkn : k ≤ n) :
    (∑ t ∈ range N, mode N (n+j) t * mode N (n+k) t) = if j = k then (N:ℝ)/2 else 0 := by
  simpa only [Nat.add_left_cancel_iff] using
    gram_positive (N := N) (k := n+j) (l := n+k) (by omega) (by omega) (by omega)


end Erdos1133.CosineTrace

end

section

/-! Finite dyadic lower bound used to contradict a uniform trace estimate. -/

namespace Erdos1133.HarmonicGap

open Finset

theorem dyadic_block {J : ℕ} (hJ : 0 < J) :
    (1/2 : ℝ) ≤ ∑ j ∈ Ico J (2*J), (1:ℝ)/j := by
  have hc : (Ico J (2*J)).card = J := by rw [Nat.card_Ico]; omega
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  calc
    (1/2 : ℝ) = ∑ _j ∈ Ico J (2*J), (1:ℝ)/(2*J) := by
      rw [sum_const, hc, nsmul_eq_mul]
      field_simp [ne_of_gt hJR]
    _ ≤ _ := sum_le_sum fun j hj => by
      have hj₁ : (0:ℝ) < j := by exact_mod_cast (hJ.trans_le (mem_Ico.mp hj).1)
      have hj₂ : (j:ℝ) ≤ 2*J := by exact_mod_cast (mem_Ico.mp hj).2.le
      exact one_div_le_one_div_of_le hj₁ hj₂

theorem dyadic_tail {J : ℕ} (hJ : 0 < J) (k : ℕ) :
    (k:ℝ)/2 ≤ ∑ j ∈ Ico J (2^k*J), (1:ℝ)/j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2^k * J := by positivity
    have hpow : 1 ≤ (2:ℕ)^k := Nat.pow_pos (by decide)
    have hstart : J ≤ 2^k * J := by simpa using Nat.mul_le_mul_right J hpow
    have hstop : 2^k*J ≤ 2*(2^k*J) := by omega
    rw [show 2^(k+1)*J = 2*(2^k*J) by ring,
        ← Finset.sum_Ico_consecutive _ hstart hstop, Nat.cast_succ]
    linarith [dyadic_block hpos]

/-- Every uniform trace bound eventually fails on an explicitly chosen band. -/
theorem eventually_large_band (W : ℝ) :
    ∃ k : ℕ, ∀ n : ℕ, 2*2^k ≤ n →
      ∃ J : ℕ, 0 < J ∧ 2*(2^k*J) ≤ n ∧ n ≤ 4*(2^k*J) ∧
        W < (1/2 : ℝ) * ∑ j ∈ Ico J (2^k*J), (1:ℝ)/j := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4*W)
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨J,hJ,hlo,hhi⟩ := Erdos1133.Band.choose_band k n hn
  exact ⟨J,hJ,hlo,hhi,by linarith [dyadic_tail hJ k]⟩

end Erdos1133.HarmonicGap

end

section

/-! Finite reconstruction weights for the sampling estimate in Erdős 1133.R1.H2. -/

open scoped BigOperators

namespace Erdos1133Reconstruction

/-- Extend a functional on a subspace of a finite product, keeping its bound as
an ℓ¹ estimate on its representing weights. The product has the supremum norm. -/
theorem weights_on_subspace {ι : Type*} [Fintype ι]
    (U : Submodule ℝ (ι → ℝ)) (L : U →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : U, ‖L x‖ ≤ C * ‖x‖) :
    ∃ w : ι → ℝ, (∑ i, |w i|) ≤ C ∧
      ∀ x : U, (∑ i, w i * (x : ι → ℝ) i) = L x := by
  classical
  let f : (ι → ℝ) →ₗ.[ℝ] ℝ := ⟨U, L⟩
  let N (x : ι → ℝ) := C * ‖x‖
  have hhom (c : ℝ) (hc : 0 < c) (x : ι → ℝ) : N (c • x) = c * N x := by
    simp [N, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_left_comm]
  have hadd (x y : ι → ℝ) : N (x + y) ≤ N x + N y := by
    simpa [N, mul_add] using mul_le_mul_of_nonneg_left (norm_add_le x y) hC
  have hf (x : f.domain) : f x ≤ N x := (le_abs_self (L x)).trans (hb x)
  obtain ⟨g, hmatch, hg⟩ := exists_extension_of_le_sublinear f N hhom hadd hf
  have hgb (x : ι → ℝ) : ‖g x‖ ≤ C * ‖x‖ := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hminus : -(g x) ≤ C * ‖x‖ := by simpa [N] using hg (-x)
    exact ⟨neg_le.mp hminus, hg x⟩
  obtain ⟨w, hw, hrep⟩ := weights_of_functional g hC hgb
  exact ⟨w, hw, fun x => (hrep x).trans (hmatch x)⟩

/-- A point evaluation dominated by finite samples factors through their values
even if the sampling map has a kernel. -/
theorem weights_of_sampling_bound {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] (S : E →ₗ[ℝ] (ι → ℝ)) (eval : E →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ a : E, ‖eval a‖ ≤ C * ‖S a‖) :
    ∃ w : ι → ℝ, (∑ i, |w i|) ≤ C ∧
      ∀ a : E, (∑ i, w i * S a i) = eval a := by
  have hker : LinearMap.ker S ≤ LinearMap.ker eval := by
    intro x hx
    change S x = 0 at hx
    change eval x = 0
    exact norm_le_zero_iff.mp (by simpa [hx] using hb x)
  let L := ((LinearMap.ker S).liftQ eval hker).comp S.quotKerEquivRange.symm.toLinearMap
  have hfac (a : E) : L ⟨S a, LinearMap.mem_range_self S a⟩ = eval a := by
    exact congrArg ((LinearMap.ker S).liftQ eval hker)
      (S.quotKerEquivRange_symm_apply_image a (LinearMap.mem_range_self S a))
  have hL (x : LinearMap.range S) : ‖L x‖ ≤ C * ‖x‖ := by
    rcases x with ⟨_, ⟨a, rfl⟩⟩
    rw [hfac]
    exact hb a
  obtain ⟨w, hw, h⟩ := weights_on_subspace (LinearMap.range S) L hC hL
  exact ⟨w, hw, fun a => (h ⟨S a, LinearMap.mem_range_self S a⟩).trans (hfac a)⟩

/-- Matrix-row formulation ready to apply to v k i = cos (k * φ i) and
p k = cos (k * θ), choosing one row of reconstruction weights per θ. -/
theorem weights_for_modes {κ ι : Type*} [Fintype κ] [Fintype ι]
    (v : κ → ι → ℝ) (p : κ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : κ → ℝ, ‖∑ k, a k * p k‖ ≤ C * ‖fun i => ∑ k, a k * v k i‖) :
    ∃ w : ι → ℝ, (∑ i, |w i|) ≤ C ∧ ∀ k, (∑ i, w i * v k i) = p k := by
  classical
  let S : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun a i => ∑ k, a k * v k i
      map_add' := by intro a b; ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; ext i; simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  let T : (κ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun a => ∑ k, a k * p k
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  obtain ⟨w, hw, h⟩ := weights_of_sampling_bound S T hC hb
  refine ⟨w, hw, fun k => ?_⟩
  simpa [S, T, ite_mul] using h (fun j => if j = k then 1 else 0)

/-- Select reconstruction rows for every reference evaluation. The sampling
hypothesis allows the witnessing node to depend on the coefficients and row. -/
theorem reconstruction_matrix {κ ι τ : Type*} [Fintype κ] [Fintype ι]
    (v : κ → ι → ℝ) (p : τ → κ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t (a : κ → ℝ), ∃ i : ι,
      |∑ k, a k * p t k| ≤ C * |∑ k, a k * v k i|) :
    ∃ W : τ → ι → ℝ, (∀ t, (∑ i, |W t i|) ≤ C) ∧
      ∀ t k, (∑ i, W t i * v k i) = p t k := by
  classical
  have hrow (t : τ) := weights_for_modes v (p t) hC
  have hall (t : τ) : ∃ w : ι → ℝ, (∑ i, |w i|) ≤ C ∧
      ∀ k, (∑ i, w i * v k i) = p t k := by
    apply hrow t
    intro a
    obtain ⟨i, hi⟩ := hb t a
    have hv := norm_le_pi_norm (fun i : ι => ∑ k, a k * v k i) i
    rw [Real.norm_eq_abs] at hv ⊢
    exact hi.trans (mul_le_mul_of_nonneg_left hv hC)
  exact ⟨fun t => (hall t).choose, fun t => (hall t).choose_spec.1,
    fun t => (hall t).choose_spec.2⟩

end Erdos1133Reconstruction

end

section

namespace Erdos1133.CosineTrace

open Finset
open scoped BigOperators

/-- A uniform high trace and a bounded cosine reconstruction cannot coexist at critical density.
The selected aspect ratio bounds are the ones needed to estimate the high trace
in terms of the original node oversampling ratio. -/
theorem choose_impossible_band (C E : ℝ) :
    ∃ q : ℕ, ∀ n : ℕ, 2*2^q ≤ n →
      ∃ J : ℕ, 0 < J ∧ 2*(2^q*J) ≤ n ∧ n ≤ 4*(2^q*J) ∧
      ∀ (p : ℕ) (φ : ℕ → ℝ) (w : ℕ → ℕ → ℝ),
        (∀ t < 4*n+1, ∑ i ∈ range p, |w t i| ≤ C) →
        (∀ k ≤ n, ∀ t < 4*n+1, ∑ i ∈ range p, w t i * Real.cos ((k : ℝ) * φ i)
          = mode (4*n+1) k t) →
        (1/(J : ℝ)) * (∑ j ∈ Ico J (2^q*J),
          |diag (4*n+1) p w (fun k i => Real.cos ((k : ℝ)*φ i)) (n+j)|) > E := by
  obtain ⟨q,hq⟩ := Erdos1133.HarmonicGap.eventually_large_band (C*20+E)
  refine ⟨q, fun n hn => ?_⟩
  obtain ⟨J,hJ,hend,hwidth,hlarge⟩ := hq n hn
  refine ⟨J,hJ,hend,hwidth,?_⟩
  intro p φ w hw hrep
  apply lt_of_not_ge
  intro hhigh
  apply dyadic_contradiction (N := 4*n+1) (p := p) (n := n) (q := q)
    w (fun k i => Real.cos ((k : ℝ)*φ i)) hJ (by norm_num : (0 : ℝ) ≤ 20)
    (by omega) (by omega) hw hrep _ hhigh hlarge
  intro t ht i hi
  have h := Erdos1133.KernelBound.cosine_kernel_bound n J (2^q*J) (angle (4*n+1) t) (φ i)
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have h := (mem_Ico.mp hj).2; omega
  simp only [mode, Nat.cast_sub hjn, Nat.cast_add]


end Erdos1133.CosineTrace

end

section

/-! Connect the sparse norming set and Hahn–Banach reconstruction to the
zero-based natural-number indexing used by the cosine trace estimates. -/

open scoped BigOperators

namespace Erdos1133.SparseSampling

/-- Simultaneously thin the angular nodes and reconstruct all reference
evaluations, in the finite-range format expected by the trace comparison. -/
theorem sparse_reconstruction_rows {κ : Type*} [Fintype κ]
    (X : Finset ℝ) (v : κ → ℝ → ℝ) (r : ℕ → κ → ℝ) (N n : ℕ)
    (M : (κ → ℝ) → ℝ) {C L : ℝ} (hC : 0 < C) (hL : 0 < L) (hn : 0 < n)
    (hM : ∀ a, 0 ≤ M a)
    (hdom : ∀ t < N, ∀ a, |∑ k, a k * r t k| ≤ M a)
    (hnorm : ∀ a, ∃ x ∈ X, M a ≤ C * |∑ k, a k * v k x|)
    (hlip : ∀ a x, x ∈ X → ∀ y, y ∈ X →
      |(∑ k, a k * v k x) - (∑ k, a k * v k y)| ≤ (L*n) * M a * |x-y|) :
    ∃ (p : ℕ) (φ : ℕ → ℝ) (w : ℕ → ℕ → ℝ),
      p ≤ X.card ∧ (∀ i < p, φ i ∈ X) ∧
      (∀ i < p, ∀ j < p, i ≠ j → 1/(2*C*(L*n)) < |φ i - φ j|) ∧
      (∀ t < N, (∑ i ∈ Finset.range p, |w t i|) ≤ 2*C) ∧
      ∀ k t, t < N → (∑ i ∈ Finset.range p, w t i * v k (φ i)) = r t k := by
  classical
  obtain ⟨Y, hYX, hsep, hs⟩ := sparsify_at_degree X
    (fun a x => ∑ k, a k * v k x) M hC hL hn hM hnorm hlip
  let e := Y.orderIsoOfFin (k := Y.card) rfl
  let φ (i : ℕ) : ℝ := if h : i < Y.card then (e ⟨i, h⟩ : Y) else 0
  have hφ (i : Fin Y.card) : φ i = (e i : ℝ) := by simp [φ, i.isLt]
  have hrows (t : Fin N) (a : κ → ℝ) : ∃ i : Fin Y.card,
      |∑ k, a k * r t k| ≤ 2*C * |∑ k, a k * v k (φ i)| := by
    obtain ⟨y, hy, hb⟩ := hs a
    let i : Fin Y.card := e.symm ⟨y, hy⟩
    refine ⟨i, ?_⟩
    simpa [hφ, i] using (hdom t t.isLt a).trans hb
  obtain ⟨W, hW, hrep⟩ := Erdos1133Reconstruction.reconstruction_matrix
    (fun k (i : Fin Y.card) => v k (φ i)) (fun (t : Fin N) k => r t k)
    (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) hC.le) hrows
  let w (t i : ℕ) : ℝ := if ht : t < N then
      if hi : i < Y.card then W ⟨t,ht⟩ ⟨i,hi⟩ else 0 else 0
  refine ⟨Y.card, φ, w, Finset.card_le_card hYX, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [show φ i = (e ⟨i, hi⟩ : ℝ) from hφ ⟨i, hi⟩]
    exact hYX (e ⟨i, hi⟩).property
  · intro i hi j hj hij
    rw [show φ i = (e ⟨i, hi⟩ : ℝ) from hφ ⟨i, hi⟩,
      show φ j = (e ⟨j, hj⟩ : ℝ) from hφ ⟨j, hj⟩]
    apply hsep _ (e ⟨i, hi⟩).property _ (e ⟨j, hj⟩).property
    intro heq
    have hsub : e ⟨i, hi⟩ = e ⟨j, hj⟩ := Subtype.ext heq
    exact hij (congrArg Fin.val (e.injective hsub))
  · intro t ht
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [w, ht, Fin.isLt] using hW ⟨t, ht⟩
  · intro k t ht
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [w, ht, Fin.isLt] using hrep ⟨t, ht⟩ k

end Erdos1133.SparseSampling

end

section

namespace Erdos1133.CosineTrace

open Finset
open scoped BigOperators

open scoped InnerProductSpace
open Erdos1133.RankBound

/-- From raw DCT reconstruction and a scalar synthesis inequality on the selected band
to the high-frequency diagonal estimate. All arrays use the same natural indices. -/
theorem high_diagonal_from_rows {N p n : ℕ} (s : Finset ℕ) (w v : ℕ → ℕ → ℝ)
    {C ε L : ℝ} (hN : 2*n < N) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hsize : (p:ℝ) ≤ (1+ε)*n)
    (hj : ∀ j ∈ s, 0 < j ∧ j ≤ n)
    (hrow : ∀ t < N, ∑ i ∈ range p, |w t i| ≤ C)
    (hrep : ∀ k ≤ n, ∀ t < N, ∑ i ∈ range p, w t i * v k i = mode N k t)
    (hSynth : ∀ a : ℕ → ℝ, (∑ i ∈ range p, (∑ j ∈ s, a j * v (n+j) i)^2)
        ≤ L * ∑ j ∈ s, a j ^ 2) :
    ∃ r : ℕ, (r : ℝ) ≤ ε*n ∧
      (∑ j ∈ s, |diag N p w v (n+j)|) ≤ C * Real.sqrt (L*r) := by
  classical
  let vL (k : Fin (n+1)) := sampleVec p (v k.val)
  let U := Submodule.span ℝ (Set.range vL)
  let col (j : ℕ) := sampleVec p (v (n+j))
  let f (j i : ℕ) := (∑ t ∈ range N, mode N (n+j) t * w t i)/(N:ℝ)
  let rowF (t : ℕ) := (innerSL ℝ (sampleVec p (w t))).toLinearMap
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hind : LinearIndependent ℝ vL := by
    apply independent_of_reproduced_modes (range N) vL
      (fun k t => mode N k.val t) rowF
      (fun k => if k.val = 0 then (N : ℝ) else (N : ℝ)/2)
    · intro k; split <;> positivity
    · intro t ht k
      change ⟪sampleVec p (w t), sampleVec p (v k.val)⟫_ℝ = _
      rw [sampleVec_inner]
      exact hrep k.val (by omega) t (mem_range.mp ht)
    · intro k l
      exact gram_low_fin (by omega) k l
  obtain ⟨hdim,hcodim⟩ := sampled_span_rank_codim vL hind ε
      (by simpa [finrank_euclideanSpace_fin] using hsize)
  have hmem (j : ℕ) (hj' : j ∈ s) : sampleVec p (f j) ∈ Uᗮ := by
    apply mem_span_orthogonal_of_annihilates vL
    intro k
    rw [show vL k = sampleVec p (v k.val) by rfl, sampleVec_inner]
    exact normalized_annihilates_low (N := N) (p := p) (k := n+j) (l := k.val)
      (w := w) (v := v) (by have := hj j hj'; omega)
      (by have := hj j hj'; omega) (hrep k.val (by omega))
  let b (j : ℕ) : Uᗮ := if h : j ∈ s then ⟨sampleVec p (f j), hmem j h⟩ else 0
  have bval (j) (h : j ∈ s) : ((b j : Uᗮ) : EuclideanSpace ℝ (Fin p)) = sampleVec p (f j) := by
    simp [b,h]
  have hEnergy : ∑ j ∈ s, ‖b j‖^2 ≤ C^2 := by
    have hG (j : ℕ) (hj' : j ∈ s) (k : ℕ) (hk' : k ∈ s) :
        (∑ t ∈ range N, mode N (n+j) t * mode N (n+k) t) =
          if j=k then (N:ℝ)/2 else 0 := by
      exact gram_shifted hN (hj j hj').1 (hj j hj').2 (hj k hk').2
    calc
      _ = ∑ j ∈ s, ∑ i ∈ range p, (f j i)^2 := by
        apply Finset.sum_congr rfl
        intro j hj'
        change ‖((b j : Uᗮ) : EuclideanSpace ℝ (Fin p))‖^2 = _
        rw [bval j hj', sampleVec_norm_sq]
      _ ≤ C^2 := averaged_coefficient_energy s N p (by omega) (fun j t => mode N (n+j) t)
        w C hG hrow
  have hSy (a : ℕ → ℝ) : ‖∑ j ∈ s, a j • col j‖^2 ≤ L * ∑ j ∈ s, a j^2 := by
    change ‖∑ j ∈ s, a j • sampleVec p (v (n+j))‖^2 ≤ _
    rw [sampleVec_sum_smul p s a (fun j => v (n+j)), sampleVec_norm_sq]
    exact hSynth a
  refine ⟨Module.finrank ℝ Uᗮ, hcodim, ?_⟩
  have htrace := high_trace_of_codimension s col U b L C hL hC (Module.finrank ℝ Uᗮ)
    U.finrank_add_finrank_orthogonal hEnergy hSy
  calc
    _ = ∑ j ∈ s, |⟪((b j : Uᗮ) : EuclideanSpace ℝ (Fin p)), col j⟫_ℝ| := by
      apply Finset.sum_congr rfl
      intro j hj'
      rw [bval j hj', show col j = sampleVec p (v (n+j)) by rfl, sampleVec_inner]
      exact congrArg abs (diag_as_coeff_sum N p w v (n+j))
    _ ≤ _ := htrace

/-- Use the verified-paper choice epsilon = (4*2^q)^(-2). -/
theorem impossible_sparse_rows (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ ε > (0:ℝ), ∃ q : ℕ, ∀ n : ℕ, 2*2^q ≤ n →
      ∃ J : ℕ, 0 < J ∧ 2*(2^q*J) ≤ n ∧ n ≤ 4*(2^q*J) ∧
      ∀ (p : ℕ) (φ : ℕ → ℝ) (w : ℕ → ℕ → ℝ),
        (p : ℝ) ≤ (1+ε)*n →
        (∀ t < 4*n+1, ∑ i ∈ range p, |w t i| ≤ C) →
        (∀ k ≤ n, ∀ t < 4*n+1, ∑ i ∈ range p, w t i * Real.cos ((k : ℝ)*φ i)
          = mode (4*n+1) k t) →
        ¬ ∀ a : ℕ → ℝ, (∑ i ∈ range p, (∑ j ∈ Ico J (2^q*J),
          a j * Real.cos (((n+j : ℕ):ℝ)*φ i))^2) ≤ (B*n) * ∑ j ∈ Ico J (2^q*J), a j^2 := by
  obtain ⟨q,hq⟩ := choose_impossible_band C (C*Real.sqrt B)
  let D := 4*(2:ℝ)^q
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1/D^2, Erdos1133.Ratio.epsilon_choice q, q, fun n hn => ?_⟩
  obtain ⟨J,hJ,hend,hwidth,hgap⟩ := hq n hn
  refine ⟨J,hJ,hend,hwidth,?_⟩
  intro p φ w hsize hrow hrep hSyn
  let s := Ico J (2^q*J)
  let v (k i : ℕ) := Real.cos ((k:ℝ)*φ i)
  obtain ⟨r,hr,ht⟩ := high_diagonal_from_rows (N := 4*n+1) (n := n) s w v
    (by omega) hC (mul_nonneg hB (Nat.cast_nonneg n)) hsize
    (fun j hj => by have h := mem_Ico.mp hj; omega) hrow hrep hSyn
  have hw' : (n:ℝ) ≤ D*J := by
    dsimp [D]
    exact_mod_cast (show n ≤ (4*2^q)*J by simpa [Nat.mul_assoc] using hwidth)
  have hrs : (r:ℝ) ≤ n / D^2 := by simpa [div_eq_mul_inv, mul_comm] using hr
  have hup := Erdos1133.Ratio.scaled_trace_bound hB hC (Nat.cast_nonneg n) (Nat.cast_nonneg r)
    (Nat.cast_pos.mpr hJ) hD hw' hrs ht
  exact (not_lt_of_ge hup) (hgap p φ w hrow hrep)


end Erdos1133.CosineTrace

end

section

/-! From absence of a large cosine-polynomial witness at the original nodes
to a separated reconstruction matrix at arbitrary reference angles. -/

open scoped BigOperators
open Finset

namespace Erdos1133.SparseSampling

/-- The finite cosine coefficient convention includes its constant term. -/
theorem cosine_lipschitz {n : ℕ} (a : Fin (n+1) → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ z, |Norming.value a z| ≤ M) (x y : ℝ) :
    |Norming.value a x - Norming.value a y| ≤ (n : ℝ)*M*|x-y| := by
  by_cases hpos : 0 < M
  · let A (k : ℕ) : ℝ := if hk : k < n then a ⟨k+1, Nat.succ_lt_succ hk⟩ else 0
    have heq (z : ℝ) :
        Norming.value a z = BernsteinEndpoint.trig n A 0 (a 0) z := by
      rw [Norming.value, Fin.sum_univ_succ, BernsteinEndpoint.trig]
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      simp [A, k.isLt, Fin.val_succ]
      exact Or.inl rfl
    have hh := BernsteinEndpoint.lipschitz n A 0 (a 0) hpos
      (fun z => (heq z) ▸ hb z) x y
    simpa only [← heq] using hh
  · have hz : M = 0 := le_antisymm (le_of_not_gt hpos) hM
    have ha (z : ℝ) : Norming.value a z = 0 := abs_nonpos_iff.mp (hz ▸ hb z)
    simp [ha x, ha y, hz]

/-- Every reference angle has a uniformly bounded exact reconstruction row
using a single separated subset of the original sampling angles. -/
theorem rows_of_no_witness {n m N : ℕ} (hn : 0 < n) (hm : 0 < m)
    {C : ℝ} (hC : 0 < C) (node : Fin m → ℝ) (θ : ℕ → ℝ)
    (h : ¬ ∃ (a : Fin (n+1) → ℝ) (x : ℝ), 0 < |Norming.value a x| ∧
      ∀ i, C*|Norming.value a (node i)| < |Norming.value a x|) :
    ∃ (p : ℕ) (φ : ℕ → ℝ) (w : ℕ → ℕ → ℝ),
      p ≤ m ∧ (∀ i < p, ∃ j, φ i = node j) ∧
      (∀ i < p, ∀ j < p, i ≠ j → 1/(2*C*n) < |φ i-φ j|) ∧
      (∀ t < N, (∑ i ∈ range p, |w t i|) ≤ 2*C) ∧
      ∀ k ≤ n, ∀ t < N, (∑ i ∈ range p, w t i * Real.cos ((k:ℝ)*φ i)) =
        Real.cos ((k:ℝ)*θ t) := by
  classical
  obtain ⟨M,hM,hglob,hold⟩ := Norming.bounded_family hm hC.le node h
  let X : Finset ℝ := Finset.univ.image node
  let v (k : Fin (n+1)) (x : ℝ) := Real.cos ((k.val : ℝ)*x)
  have hin (a : Fin (n+1) → ℝ) : ∃ x ∈ X, M a ≤ C*|∑ k, a k * v k x| := by
    obtain ⟨i, hi⟩ := hold a
    exact ⟨node i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  obtain ⟨p, φ, w, hp, hmem, hsep, hrows, hrep⟩ :=
    sparse_reconstruction_rows X v (fun t k => v k (θ t)) N n M hC zero_lt_one hn
      hM (fun t _ a => hglob a (θ t)) hin
      (fun a x _ y _ => by simpa only [one_mul, Norming.value, v] using cosine_lipschitz a (hM a) (hglob a) x y)
  refine ⟨p, φ, w, hp.trans ?_, ?_, ?_, hrows, ?_⟩
  · exact (Finset.card_image_le : X.card ≤ (Finset.univ : Finset (Fin m)).card).trans_eq
      (by simp)
  · intro i hi
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp (hmem i hi)
    exact ⟨j, heq.symm⟩
  · simpa only [one_mul] using hsep
  · intro k hk t ht
    exact hrep ⟨k,Nat.lt_succ_of_le hk⟩ t ht

end Erdos1133.SparseSampling

end

section

namespace Erdos1133.CosineTrace

open Finset
open scoped BigOperators

/-- Every sufficiently large degree admits a cosine polynomial whose value at one
angle exceeds C times its absolute value at each near-critical sampling node. -/
theorem exists_cosine_growth (C : ℝ) (hC : 0 < C) :
    ∃ ε > (0:ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ, (m:ℝ) ≤ (1+ε)*n →
      ∀ node : Fin m → ℝ, (∀ i, node i ∈ Set.Icc 0 Real.pi) →
      ∃ (a : Fin (n+1) → ℝ) (x : ℝ), 0 < |Erdos1133.Norming.value a x| ∧
        ∀ i, C*|Erdos1133.Norming.value a (node i)| < |Erdos1133.Norming.value a x| := by
  classical
  let B := Real.pi*(2*C*1+6)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨ε,hε,q,hq⟩ := impossible_sparse_rows (2*C) B (by positivity) hB
  refine ⟨ε,hε,2*2^q,?_⟩
  intro n hn m hm node hnode
  have hpw : 0 < (2:ℕ)^q := Nat.pow_pos (by decide)
  have hn' : 0 < n := by omega
  by_cases hm' : 0 < m
  · by_contra h
    obtain ⟨p,φ,w,hp,hφ,hsep,hrow,hrep⟩ :=
      Erdos1133.SparseSampling.rows_of_no_witness (N := 4*n+1) hn' hm'
        hC node (angle (4*n+1)) h
    obtain ⟨J,hJ,hend,hwidth,hNo⟩ := hq n hn
    apply hNo p φ w ((Nat.cast_le.mpr hp).trans hm) hrow hrep
    intro a
    apply Erdos1133.Sampling.separated_range_synthesis p φ (Ico J (2^q*J))
      (fun j => n+j) a hn' hC (L := 1) zero_lt_one
    · intro i hi
      obtain ⟨j,hj⟩ := hφ i hi
      simpa [hj] using hnode j
    · simpa only [one_mul] using hsep
    · intro i hi j hj hij
      exact Nat.add_left_cancel hij
    · intro j hj
      have hj' := (mem_Ico.mp hj).2
      omega
  · have hz : m = 0 := by omega
    subst m
    refine ⟨fun k => if k = 0 then 1 else 0, 0, ?_, fun i => Fin.elim0 i⟩
    simp [Erdos1133.Norming.value]


end Erdos1133.CosineTrace

end

section

private theorem h2_h1_proof : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.H1 :=
  Erdos1133.CircleTransfer.circle_of_growth Erdos1133.CosineTrace.exists_cosine_growth

end

section
namespace TrigBernstein

open Real Polynomial

def Rep (d : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ U V : ℝ[X], U.natDegree ≤ d ∧ (V = 0 ∨ V.natDegree < d) ∧
    ∀ s, f s = U.eval (cos s) + sin s * V.eval (cos s)

theorem timesLinear {d : ℕ} {f : ℝ → ℝ} (hf : Rep d f) (a b c : ℝ) :
    Rep (d+1) (fun s => (a*cos s + b*sin s)*f s + c) := by
  obtain ⟨U,V,hu,hv,he⟩ := hf
  refine ⟨C a * X * U + C b * (1-X^2) * V + C c, C b * U + C a * X * V, ?_, Or.inr ?_, ?_⟩
  · rcases hv with rfl|hv
    · simp only [mul_zero,add_zero]; compute_degree; omega
    · compute_degree; omega
  · rcases hv with rfl|hv
    · simp only [mul_zero,add_zero]; exact Nat.lt_succ_of_le ((natDegree_C_mul_le _ _).trans hu)
    · apply Nat.lt_succ_of_le; compute_degree; omega
  · intro s
    simp only [he,eval_add,eval_mul,eval_sub,eval_pow,eval_one,eval_X,eval_C]
    linear_combination b * V.eval (cos s) * Real.sin_sq_add_cos_sq s

theorem polyRep (a b : ℝ) (d : ℕ) (P : ℝ[X]) (hp : P.natDegree ≤ d) :
    Rep d (fun s => P.eval (a*cos s+b*sin s)) := by
  induction d generalizing P with
  | zero =>
    exact ⟨P,0,hp,Or.inl rfl, fun s => by rw [eq_C_of_natDegree_le_zero hp]; simp⟩
  | succ d ih =>
    have hr := ih P.divX (by rw [natDegree_divX_eq_natDegree_tsub_one]; omega)
    have h := timesLinear hr a b (P.coeff 0)
    convert h using 1
    funext s
    have hP := congrArg (fun Q : ℝ[X] => Q.eval (a*cos s+b*sin s)) (divX_mul_X_add P)
    simpa only [eval_add, eval_mul, eval_X, eval_C, mul_comm] using hP.symm

theorem translated {d : ℕ} (A B : ℝ[X]) (ha : A.natDegree ≤ d) (hb : B.natDegree < d)
    (t : ℝ) : Rep d (fun s => A.eval (cos (t+s)) + sin (t+s) * B.eval (cos (t+s))) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨U,V,hu,hv,he⟩ := polyRep (cos t) (-sin t) (k+1) A ha
  have h := timesLinear (polyRep (cos t) (-sin t) k B (by omega)) (sin t) (cos t) 0
  obtain ⟨W,Z,hw,hz,hh⟩ := h
  refine ⟨U+W,V+Z,(natDegree_add_le _ _).trans (max_le hu hw),Or.inr ?_, ?_⟩
  · apply lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rcases hv with rfl|h <;> simp_all
    · rcases hz with rfl|h <;> simp_all
  · intro s
    simp only [Real.cos_add,Real.sin_add,eval_add]
    simp only [neg_mul,← sub_eq_add_neg,add_zero] at he hh
    rw [he s, hh s]
    ring

theorem endpoint {d : ℕ} {V : ℝ[X]} (hv : V.natDegree < d) {M : ℝ} (hp : 0 < M)
    (hb : ∀ s, |sin s * V.eval (cos s)| ≤ M) : |V.eval 1| ≤ d*M := by
  let P : ℝ[X] := 1 - C (2/M^2) * (1-X^2) * V^2
  have hdeg : P.natDegree ≤ 2*d := by
    unfold P
    compute_degree; omega
  have hbnd (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) : |P.eval x| ≤ 1 := by
    have h := hb (arccos x)
    rw [cos_arccos hx.1 hx.2] at h
    have hid := sin_sq_add_cos_sq (arccos x)
    rw [cos_arccos hx.1 hx.2] at hid
    have hb2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rw [mul_pow,show sin (arccos x)^2 = 1-x^2 by linarith] at hb2
    have hxx : 0 ≤ 1-x^2 := by nlinarith [sq_nonneg (sin (arccos x))]
    simp only [P,eval_sub,eval_mul,eval_pow,eval_one,eval_X,eval_C]
    apply abs_le.mpr
    constructor
    · field_simp [hp.ne']; nlinarith
    · nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2/M^2) hxx) (sq_nonneg (V.eval x))]
  have he : P.derivative.eval 1 ≤ ((2*d:ℕ):ℝ)^2 := by
    simpa [Chebyshev.derivative_T_eval_one] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1)
        le_rfl (degree_le_of_natDegree_le hdeg) hbnd)
  have hder : P.derivative.eval 1 = 4/M^2*(V.eval 1)^2 := by
    simp [P,derivative_mul,derivative_pow]; ring_nf; simp
  rw [hder] at he
  push_cast at he
  have he' : (V.eval 1)^2 ≤ (d*M)^2 := by
    field_simp [hp.ne'] at he
    nlinarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' he' (by positivity))

end TrigBernstein

open Real Polynomial TrigBernstein

private theorem h2_h2_proof : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.H2 := by
  intro d A B hA hB
  dsimp only
  intro M hb s u
  let q := fun z : ℝ => A.eval (cos z) + sin z * B.eval (cos z)
  have hd (z : ℝ) : DifferentiableAt ℝ q z := by dsimp [q]; fun_prop
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  rcases hM.eq_or_lt with rfl|hM
  · have hq (z : ℝ) : q z = 0 := abs_nonpos_iff.mp (hb z)
    change |q s-q u| ≤ _
    simp [hq]
  have bound (z : ℝ) : |deriv q z| ≤ d*M := by
    obtain ⟨U,V,_,hv,he⟩ := translated A B hA hB z
    dsimp only at he
    have oddBound (v : ℝ) : |sin v * V.eval (cos v)| ≤ M := by
      have hplus := abs_le.mp (hb (z+v))
      have hminus := abs_le.mp (hb (z+ -v))
      rw [he v] at hplus
      rw [he (-v),sin_neg,cos_neg] at hminus
      apply abs_le.mpr; constructor <;> linarith
    have hrep : (fun v => q (z+v)) = (fun v => U.eval (cos v) + sin v * V.eval (cos v)) := funext he
    have hz0 : HasDerivAt q (deriv q z) (z + id 0) := by simpa using (hd z).hasDerivAt
    have hl := hz0.comp 0 ((hasDerivAt_const (0:ℝ) z).fun_add (hasDerivAt_id 0))
    have hr := (((U.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0))).fun_add
      ((hasDerivAt_sin 0).fun_mul ((V.hasDerivAt (cos 0)).comp 0 (hasDerivAt_cos 0)))
    have hl' : HasDerivAt (fun v => q (z+v)) (deriv q z) 0 := by
      simpa [Function.comp_def] using hl
    have hr' : HasDerivAt (fun v => U.eval (cos v) + sin v * V.eval (cos v)) (V.eval 1) 0 := by
      simpa [Function.comp_def] using hr
    rw [hrep] at hl'
    rw [hl'.unique hr']
    rcases hv with rfl|hv
    · simp; positivity
    · exact endpoint hv hM oddBound
  simpa [Real.norm_eq_abs,q] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (f := q) (fun z _ => hd z) (fun z _ => by simpa [Real.norm_eq_abs] using bound z)
      (Set.mem_univ u) (Set.mem_univ s)

end

private theorem h2_proof : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H2 :=
  OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1.main h2_h1_proof h2_h2_proof

theorem OMA.solution : type_of% @Erdos1133.erdos_1133.variants.weaker :=
  OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.main h1_proof h2_proof
