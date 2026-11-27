import FormalConjectures.ErdosProblems.«995»
import Mathlib

/-!
# Erdos Problem 995

The core of this file (namespace OMA995, renamed from Erdos995 to avoid clashing with the
upstream statement file) is adapted from the Lean 4 formalization in
https://github.com/hongjin-he/erdos-lean (directory ErdosLean/Erdos995, commit efede969),
released under the Apache License 2.0. Changes: the modules are concatenated in dependency order, comments are removed, the namespace
is renamed, and Mathlib API drift is repaired. The final section bridges the source statement
to the one in FormalConjectures.ErdosProblems.995 and derives the target statement.
-/

-- Statement
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA995

def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

def IsDyadicLacunary (n : ℕ → ℕ) : Prop := 1 ≤ n 0 ∧ ∀ k, 2 * n k ≤ n (k + 1)

lemma IsDyadicLacunary.isLacunary {n : ℕ → ℕ} (hn : IsDyadicLacunary n) : IsLacunary n := by
  refine ⟨3 / 2, by norm_num, Eventually.of_forall fun k => ?_⟩
  have hpos : ∀ k, 1 ≤ n k := by
    intro k
    induction k with
    | zero => exact hn.1
    | succ k ih => have := hn.2 k; omega
  have h1 : (1 : ℝ) ≤ n k := by exact_mod_cast hpos k
  have h2 : (2 : ℝ) * n k ≤ n (k + 1) := by exact_mod_cast hn.2 k
  linarith

noncomputable def lacSum (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ)
    (x : AddCircle (1 : ℝ)) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, f (n k • x)

def ErdosUpperBound : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n → ∀ ε : ℝ, 0 < ε →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =o[atTop]
        (fun N : ℕ => (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 + ε))

def HoLowerBound : Prop :=
  ∃ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsDyadicLacunary n ∧ (∀ᵐ x ∂(haarAddCircle (T := 1)), (f x).im = 0) ∧
    ∫ x, f x ∂(haarAddCircle (T := 1)) = 0 ∧
    ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∃ᶠ N : ℕ in atTop,
      C * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) ≤ (lacSum f n x N).re

def LogLogQuestion : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =o[atTop]
        (fun N : ℕ => (N : ℝ) * Real.sqrt (Real.log (Real.log N)))

def GrowthBoundHolds (θ : ℝ) : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =O[atTop] (fun N : ℕ => (N : ℝ) * Real.log N ^ θ)

def Erdos995CriticalExponent : Prop :=
  (∀ θ : ℝ, 1 / 2 < θ → GrowthBoundHolds θ) ∧ (∀ θ : ℝ, θ < 1 / 2 → ¬ GrowthBoundHolds θ)

def Erdos995Answer : Prop :=
  ErdosUpperBound ∧ HoLowerBound ∧ Erdos995CriticalExponent ∧ ¬ LogLogQuestion

end OMA995
end

-- Statement
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-k : ℤ) k, fourierCoeff f i • fourier i x

def FourierTailBound (C : ℝ) (f : Lp ℂ 2 (haarAddCircle (T := 1))) : Prop :=
  (fun k : ℕ => (eLpNorm (⇑f - fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k : ℕ => 1 / (log (log (log k))) ^ C)

def LacunaryAveragesConverge (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) : Prop :=
  ∀ᵐ x ∂(haarAddCircle (T := 1)),
    Tendsto (fun N : ℕ => (∑ k ∈ range N, f (n k • x)) / N) atTop
      (𝓝 (∫ t, f t ∂haarAddCircle))

def Erdos996Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n → FourierTailBound C f → LacunaryAveragesConverge f n

def IsDyadicLacunary (n : ℕ → ℕ) : Prop := 1 ≤ n 0 ∧ ∀ k, 2 * n k ≤ n (k + 1)

lemma IsDyadicLacunary.isLacunary {n : ℕ → ℕ} (hn : IsDyadicLacunary n) : IsLacunary n := by
  refine ⟨3 / 2, by norm_num, Eventually.of_forall fun k => ?_⟩
  have hpos : ∀ k, 1 ≤ n k := by
    intro k
    induction k with
    | zero => exact hn.1
    | succ k ih => have := hn.2 k; omega
  have h1 : (1 : ℝ) ≤ n k := by exact_mod_cast hpos k
  have h2 : (2 : ℝ) * n k ≤ n (k + 1) := by exact_mod_cast hn.2 k
  linarith

end OMA996
end

-- Defs
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

noncomputable def spike (d : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  ((Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) 1 x : ℝ) -
      (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))

def DeterminedByWindow (a b : ℕ) (E : Set (AddCircle (1 : ℝ))) : Prop :=
  ∀ x y : (AddCircle (1 : ℝ)), (∀ j, a ≤ j → j < b →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹) → (x ∈ E ↔ y ∈ E)

noncomputable def block (lam : ℝ) (L d D U : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  Real.sqrt (lam / L) * ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x)

end OMA996
end

-- Construction
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA996
namespace Asm

def aExp (A k : ℕ) : ℕ := A * (k + 1)

noncomputable def lam (A k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ aExp A k

def nTrials (A k : ℕ) : ℕ := 2 ^ (aExp A k + k + 24)

def firstTrial (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstTrial A k + nTrials A k

def blockLen (A k : ℕ) : ℕ := 8 * 21 ^ firstTrial A (k + 1)

def depth (A k : ℕ) : ℕ := Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)

def spacing (A k : ℕ) : ℕ := depth A k + 2

def shift (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => shift A k + blockLen A k * spacing A k + depth A k

def logQ (A k : ℕ) : ℕ := shift A (k + 1) + 2

def stage (A s : ℕ) : ℕ := Nat.findGreatest (fun k => firstTrial A k ≤ s) s

def trialLen (s : ℕ) : ℕ := 20 * 21 ^ s

def trialStart (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => trialStart A s + (blockLen A (stage A s) + 2) * spacing A (stage A s)

def trialOf (j : ℕ) : ℕ := Nat.log 21 (j + 1)

def mExp (A j : ℕ) : ℕ :=
  trialStart A (trialOf j) + (j + 2 - 21 ^ trialOf j) * spacing A (stage A (trialOf j))

def nSeq (A j : ℕ) : ℕ := 2 ^ mExp A j

noncomputable def blk (A k : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k) x

noncomputable def atom (A k q : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  spike (depth A k) ((2 ^ (shift A k + q * spacing A k) : ℕ) • x)

noncomputable def floorC (A k : ℕ) : ℝ := lam A k / 100

noncomputable def gPos (A : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (blk A k x + floorC A k)

noncomputable def gFun (A : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  (gPos A x).toReal - ∑' k, floorC A k

def spikeSet (d : ℕ) : Set (AddCircle (1 : ℝ)) := QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)

def hitSet (d v : ℕ) : Set (AddCircle (1 : ℝ)) := {x | (2 ^ v : ℕ) • x ∈ spikeSet d}

def goodSet (A s : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ h ∈ Finset.Icc (trialLen s + 1) (blockLen A (stage A s) + 1),
    hitSet (depth A (stage A s)) (shift A (stage A s) + trialStart A s + h * spacing A (stage A s))

def stageGood (A k : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)), goodSet A s

end Asm
end OMA996
end

-- Defs
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995

namespace Upper

noncomputable def sumNorm (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (M : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  ∑ k ∈ range M, ‖f (n k • x)‖

end Upper

namespace Con

def aExp (k : ℕ) : ℕ := k + 1

noncomputable def lam (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ aExp k

def bExp (k : ℕ) : ℕ := 8 * (k + 1) ^ 2 + 7

noncomputable def sig (k : ℕ) : ℝ := (2 : ℝ) ^ bExp k

def nTrials (k : ℕ) : ℕ := 2 ^ (aExp k + 2 * bExp k + k + 24)

def firstTrial : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstTrial k + nTrials k

def blockLen (k : ℕ) : ℕ := 8 * 21 ^ firstTrial (k + 1)

def depth (k : ℕ) : ℕ := Nat.clog 2 (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k)

def spacing (k : ℕ) : ℕ := depth k + 2

def shift : ℕ → ℕ
  | 0 => 0
  | k + 1 => shift k + blockLen k * spacing k + depth k

def stage (s : ℕ) : ℕ := Nat.findGreatest (fun k => firstTrial k ≤ s) s

def trialLen (s : ℕ) : ℕ := 20 * 21 ^ s

def trialStart : ℕ → ℕ
  | 0 => 0
  | s + 1 => trialStart s + (blockLen (stage s) + 2) * spacing (stage s)

def trialOf (j : ℕ) : ℕ := Nat.log 21 (j + 1)

def mExp (j : ℕ) : ℕ :=
  trialStart (trialOf j) + (j + 2 - 21 ^ trialOf j) * spacing (stage (trialOf j))

def nSeq (j : ℕ) : ℕ := 2 ^ mExp j

noncomputable def blk (k : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  OMA996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k) x

noncomputable def atom (k q : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  OMA996.spike (depth k) ((2 ^ (shift k + q * spacing k) : ℕ) • x)

noncomputable def floorC (k : ℕ) : ℝ := lam k / sig k

noncomputable def gPos (x : (AddCircle (1 : ℝ))) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (blk k x + floorC k)

noncomputable def gFun (x : (AddCircle (1 : ℝ))) : ℝ :=
  (gPos x).toReal - ∑' k, floorC k

def goodSet (s : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ h ∈ Finset.Icc (trialLen s + 1) (blockLen (stage s) + 1),
    OMA996.Asm.hitSet (depth (stage s)) (shift (stage s) + trialStart s + h * spacing (stage s))

def stageGood (k : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)), goodSet s

end Con

end OMA995
end

-- UpperL2
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Upper

lemma norm_lacSum_le_sumNorm (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (x : (AddCircle (1 : ℝ))) {N M : ℕ} (h : N ≤ M) :
    ‖lacSum f n x N‖ ≤ sumNorm f n M x := by
  unfold lacSum sumNorm
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
      (fun _ _ _ => norm_nonneg _))

lemma measurePreserving_nsmul' (n : ℕ) (hn : n ≠ 0) :
    MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => n • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := by
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) :=
    Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) (by exact_mod_cast hn)
  have e : (fun x : (AddCircle (1 : ℝ)) => n • x) = fun x => (n : ℤ) • x := by
    funext x; exact (natCast_zsmul x n).symm
  rw [e]; exact hmp

lemma aestronglyMeasurable_comp_nsmul (f : Lp ℂ 2 (haarAddCircle (T := 1))) (m : ℕ) :
    AEStronglyMeasurable (fun x : (AddCircle (1 : ℝ)) => f (m • x)) (haarAddCircle (T := 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_smul]; exact aestronglyMeasurable_const
  · exact (Lp.aestronglyMeasurable f).comp_measurePreserving
      (measurePreserving_nsmul' m hm.ne')

lemma lintegral_comp_nsmul_le (f : Lp ℂ 2 (haarAddCircle (T := 1))) (m : ℕ) :
    ∫⁻ x, ‖f (m • x)‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) + ‖f 0‖ₑ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_smul, lintegral_const, measure_univ, mul_one]
    exact le_add_self
  · have hmp := measurePreserving_nsmul' m hm.ne'
    have hg : AEMeasurable (fun x : (AddCircle (1 : ℝ)) => ‖f x‖ₑ ^ 2) (Measure.map (fun x : (AddCircle (1 : ℝ)) => m • x) (haarAddCircle (T := 1))) := by
      rw [hmp.map_eq]; exact (Lp.aestronglyMeasurable f).enorm.pow_const 2
    rw [← lintegral_map' hg hmp.measurable.aemeasurable, hmp.map_eq]
    exact le_self_add

lemma aemeasurable_sumNorm (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (M : ℕ) :
    AEMeasurable (sumNorm f n M) (haarAddCircle (T := 1)) := by
  unfold sumNorm
  exact Finset.aemeasurable_fun_sum _ fun k _ =>
    (aestronglyMeasurable_comp_nsmul f (n k)).norm.aemeasurable

lemma lintegral_enorm_sq_ne_top (f : Lp ℂ 2 (haarAddCircle (T := 1))) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) ≠ ∞ := by
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    (Lp.memLp f).eLpNorm_lt_top
  have e : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [e, ENNReal.rpow_natCast] at h2
  simpa using h2.ne

lemma lintegral_sumNorm_sq_le (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (M : ℕ) :
    ∫⁻ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ∂(haarAddCircle (T := 1)) ≤
      (M : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) + ‖f 0‖ₑ ^ 2) := by
  set C := ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) + ‖f 0‖ₑ ^ 2
  have hpt : ∀ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ≤
      (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 := by
    intro x
    have hreal : (sumNorm f n M x) ^ 2 ≤ (M : ℝ) * ∑ k ∈ range M, ‖f (n k • x)‖ ^ 2 := by
      unfold sumNorm
      simpa using sq_sum_le_card_mul_sum_sq (s := range M) (f := fun k => ‖f (n k • x)‖)
    calc ENNReal.ofReal (sumNorm f n M x) ^ 2
        = ENNReal.ofReal ((sumNorm f n M x) ^ 2) := by
          have h0 : (0 : ℝ) ≤ sumNorm f n M x := Finset.sum_nonneg fun _ _ => norm_nonneg _
          rw [ENNReal.ofReal_pow h0]
      _ ≤ ENNReal.ofReal ((M : ℝ) * ∑ k ∈ range M, ‖f (n k • x)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  calc ∫⁻ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ∂(haarAddCircle (T := 1))
      ≤ ∫⁻ x, (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) := lintegral_mono hpt
    _ = (M : ℝ≥0∞) * ∑ k ∈ range M, ∫⁻ x, ‖f (n k • x)‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M), lintegral_finsetSum']
        intro k _
        exact (aestronglyMeasurable_comp_nsmul f (n k)).enorm.pow_const 2
    _ ≤ (M : ℝ≥0∞) * ∑ k ∈ range M, C := by
        gcongr with k hk
        exact lintegral_comp_nsmul_le f (n k)
    _ = (M : ℝ≥0∞) ^ 2 * C := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul, ← mul_assoc, sq]

end Upper
end OMA995
end

-- UpperBorelCantelli
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Upper

lemma ae_eventually_sumNorm_le (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ᶠ j : ℕ in atTop,
      sumNorm f n (2 ^ (j + 1)) x ≤ δ * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
  set p : ℝ := 1 + 2 * ε with hp
  set C : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(haarAddCircle (T := 1)) + ‖f 0‖ₑ ^ 2 with hCdef
  have hC : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨lintegral_enorm_sq_ne_top f, by simp⟩
  set t : ℕ → ℝ := fun J => δ * ((2 : ℝ) ^ J * (J : ℝ) ^ ((1 : ℝ) / 2 + ε)) with htdef
  set s : ℕ → Set (AddCircle (1 : ℝ)) := fun j => {x | t (j + 1) < sumNorm f n (2 ^ (j + 1 + 1)) x} with hsdef
  have key : ∀ j : ℕ, (haarAddCircle (T := 1)) (s j) ≤
      ENNReal.ofReal (4 * C.toReal / δ ^ 2 * ((((j + 1 : ℕ) : ℝ)) ^ p)⁻¹) := by
    intro j
    have hJ : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have ht : 0 < t (j + 1) := by simp only [htdef]; positivity
    have hsub : s j ⊆ {x | ENNReal.ofReal (t (j + 1)) ^ 2 ≤
        ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2} := by
      intro x hx
      simp only [hsdef, Set.mem_ofPred_eq] at hx ⊢
      exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hx.le) 2
    have hne : ENNReal.ofReal (t (j + 1)) ^ 2 ≠ 0 := by
      apply pow_ne_zero; simpa using ht
    calc (haarAddCircle (T := 1)) (s j) ≤ (haarAddCircle (T := 1)) {x | ENNReal.ofReal (t (j + 1)) ^ 2 ≤
          ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2} := measure_mono hsub
      _ ≤ (∫⁻ x, ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2 ∂(haarAddCircle (T := 1))) /
            ENNReal.ofReal (t (j + 1)) ^ 2 :=
          meas_ge_le_lintegral_div
            ((aemeasurable_sumNorm f n _).ennreal_ofReal.pow_const 2) hne
            (by simp)
      _ ≤ ((2 ^ (j + 1 + 1) : ℕ) : ℝ≥0∞) ^ 2 * C / ENNReal.ofReal (t (j + 1)) ^ 2 := by
          gcongr; exact lintegral_sumNorm_sq_le f n _
      _ = ENNReal.ofReal ((((2 ^ (j + 1 + 1) : ℕ) : ℝ)) ^ 2 * C.toReal / (t (j + 1)) ^ 2) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < t (j + 1) ^ 2),
            ENNReal.ofReal_pow ht.le,
            ENNReal.ofReal_mul (p := (((2 ^ (j + 1 + 1) : ℕ) : ℝ)) ^ 2) (by positivity),
            ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hC]
      _ = _ := by
          congr 1
          have hrp : (((j + 1 : ℕ) : ℝ)) ^ p = ((((j + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hJ.le]
            congr 1; rw [hp]; push_cast; ring
          have hpos : 0 < (((j + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε) := Real.rpow_pos_of_pos hJ _
          rw [hrp]
          simp only [htdef]
          have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
          field_simp
          push_cast
          ring
  have hs : Summable (fun j : ℕ => 4 * C.toReal / δ ^ 2 * ((((j + 1 : ℕ) : ℝ)) ^ p)⁻¹) :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by rw [hp]; linarith))).mul_left _
  have hsum : ∑' j, (haarAddCircle (T := 1)) (s j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with x hx
  rw [eventually_atTop] at hx ⊢
  obtain ⟨N, hN⟩ := hx
  refine ⟨N + 1, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := hN i (by omega)
  simp only [hsdef, htdef, Set.mem_ofPred_eq, not_lt] at this
  exact this

end Upper
end OMA995
end

-- UpperDyadic
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Upper

lemma isLittleO_of_dyadic (S : ℕ → ℂ) (G : ℕ → ℝ)
    (hSG : ∀ N : ℕ, ‖S N‖ ≤ G (2 ^ (Nat.log 2 N + 1))) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ m : ℕ, ∀ᶠ j : ℕ in atTop,
      G (2 ^ (j + 1)) ≤ (1 / ((m : ℝ) + 1)) * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    S =o[atTop] (fun N : ℕ => (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 + ε)) := by
  set a : ℝ := (1 : ℝ) / 2 + ε with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨m, hm⟩ := exists_nat_gt ((2 : ℝ) ^ a / c)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (h m)
  rw [Filter.eventually_atTop]
  refine ⟨2 ^ J + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN1
  have hJN : 2 ^ J ≤ N := le_trans (Nat.le_succ _) hN
  set j := Nat.log 2 N with hj
  have hjJ : J ≤ j := Nat.le_log_of_pow_le (by norm_num) hJN
  have hG := hJ j hjJ
  have h2j : (2 : ℝ) ^ j ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 hN0
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hjlog : (j : ℝ) ≤ 2 * Real.log N := by
    have h1 : (j : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h2j
    have h2 := Real.log_two_gt_d9
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hjrpow : (j : ℝ) ^ a ≤ (2 : ℝ) ^ a * Real.log N ^ a := by
    rw [← Real.mul_rpow (by norm_num) hlogN]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hjlog ha0.le
  have hm1 : (2 : ℝ) ^ a / ((m : ℝ) + 1) ≤ c := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at hm
    nlinarith
  have hnorm : ‖(N : ℝ) * Real.log N ^ a‖ = N * Real.log N ^ a :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm]
  calc ‖S N‖ ≤ G (2 ^ (j + 1)) := hSG N
    _ ≤ 1 / ((m : ℝ) + 1) * ((2 : ℝ) ^ j * (j : ℝ) ^ a) := hG
    _ ≤ 1 / ((m : ℝ) + 1) * ((N : ℝ) * ((2 : ℝ) ^ a * Real.log N ^ a)) := by
        gcongr
    _ = (2 : ℝ) ^ a / ((m : ℝ) + 1) * (N * Real.log N ^ a) := by ring
    _ ≤ c * (N * Real.log N ^ a) := by gcongr

end Upper
end OMA995
end

-- BlockFloor
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

lemma spike_ge_floor_aux (d : ℕ) (x : (AddCircle (1 : ℝ))) :
    -((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) ≤ spike d x := by
  unfold spike
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : (AddCircle (1 : ℝ)) → ℝ) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  linarith

lemma spike_floor_exists (d : ℕ) :
    ∃ g : ℝ, 0 ≤ g ∧ g ^ 2 ≤ 2 * (2 : ℝ)⁻¹ ^ d ∧ ∀ y : (AddCircle (1 : ℝ)), -g ≤ spike d y := by
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨(2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)),
    div_nonneg ht0.le (Real.sqrt_nonneg _), ?_, fun y => spike_ge_floor_aux d y⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · simp
  · have ht2 : (2 : ℝ)⁻¹ ^ d ≤ 1 / 2 := by
      have := pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) hd1
      simpa using this
    have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
        = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (by nlinarith)
    rw [div_pow, hs, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sq_nonneg ((2 : ℝ)⁻¹ ^ d)) (sub_nonneg.2 ht2)]

lemma block_lower_floor (lam B : ℝ) (L d D U : ℕ) (hlam : 0 < lam) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (x : (AddCircle (1 : ℝ))) :
    -(lam / B) ≤ block lam L d D U x := by
  obtain ⟨g, hg0, hg2, hspk⟩ := spike_floor_exists d
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hB0 : 0 < B := by linarith
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hsum : -((L : ℝ) * g) ≤
      ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x) := by
    have h := Finset.sum_le_sum (s := Finset.Icc 1 L)
      (fun q _ => hspk ((2 ^ (U + q * D) : ℕ) • x))
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
    linarith
  have htd : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have h1 : 64 * B ^ 2 * L ≤ 2 ^ d * lam := (div_le_iff₀ hlam).1 hd
  have h2 := mul_le_mul_of_nonneg_right h1 ht0.le
  have e : 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d = lam := by linear_combination lam * htd
  have hkey : (L : ℝ) * g ^ 2 * B ^ 2 ≤ lam := by
    have := mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ L * B ^ 2)
    nlinarith
  have hsq : Real.sqrt (lam / L) ^ 2 = lam / L := Real.sq_sqrt (div_nonneg hlam.le hLpos.le)
  have hAB : Real.sqrt (lam / L) * (L * g) * B ≤ lam := by
    apply (pow_le_pow_iff_left₀ (by positivity) hlam.le two_ne_zero).1
    rw [mul_pow, mul_pow, hsq]
    have e2 : lam / L * ((L : ℝ) ^ 2 * g ^ 2) * B ^ 2 = lam * (L * g ^ 2 * B ^ 2) := by
      field_simp
    rw [mul_pow, e2]
    have := mul_le_mul_of_nonneg_left hkey hlam.le
    nlinarith
  have h3 : Real.sqrt (lam / L) * (L * g) ≤ lam / B := (le_div_iff₀ hB0).2 hAB
  have h4 := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg (lam / L))
  unfold block
  linarith

end OMA996
end

-- Params
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma lam_pos (k : ℕ) : 0 < lam k := by
  unfold lam; positivity

lemma lam_le_one (k : ℕ) : lam k ≤ 1 := by
  unfold lam; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma lam_eq (k : ℕ) : lam k = (2 : ℝ)⁻¹ ^ (k + 1) := rfl

lemma geomSucc_summable : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) := by
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right (2⁻¹)
  exact this.congr (fun k => (pow_succ _ _).symm)

lemma geomSucc_tsum : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma summable_lam : Summable lam := by
  exact geomSucc_summable.congr (fun k => (lam_eq k).symm)

lemma tsum_lam_le_one : ∑' k, lam k ≤ 1 := by
  have : ∑' k, lam k = 1 := by
    rw [show lam = fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) from funext lam_eq]
    exact geomSucc_tsum
  rw [this]

lemma sig_ge (k : ℕ) : 128 ≤ sig k := by
  unfold sig bExp
  calc (128 : ℝ) = 2 ^ 7 := by norm_num
    _ ≤ 2 ^ (8 * (k + 1) ^ 2 + 7) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma sig_pos (k : ℕ) : 0 < sig k := by
  have := sig_ge k; linarith

lemma floorC_nonneg (k : ℕ) : 0 ≤ floorC k := by
  unfold floorC; exact div_nonneg (lam_pos k).le (sig_pos k).le

lemma floorC_le (k : ℕ) : floorC k ≤ lam k / 128 := by
  unfold floorC
  exact div_le_div_of_nonneg_left (lam_pos k).le (by norm_num) (sig_ge k)

lemma summable_floorC : Summable floorC := by
  exact Summable.of_nonneg_of_le floorC_nonneg floorC_le (summable_lam.div_const 128)

lemma tsum_floorC_le : ∑' k, floorC k ≤ 1 / 100 := by
  have h1 : ∑' k, floorC k ≤ ∑' k, lam k / 128 :=
    Summable.tsum_le_tsum floorC_le summable_floorC (summable_lam.div_const 128)
  rw [tsum_div_const] at h1
  have := tsum_lam_le_one
  have h2 : (∑' k, lam k) / 128 ≤ 1 / 128 := div_le_div_of_nonneg_right this (by norm_num)
  linarith [h1, h2, show (1 : ℝ) / 128 ≤ 1 / 100 by norm_num]

lemma one_le_blockLen (k : ℕ) : 1 ≤ blockLen k := by
  unfold blockLen
  have : 0 < 21 ^ firstTrial (k + 1) := by positivity
  omega

lemma depthArg_gt (k : ℕ) : 1 < 64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k := by
  have hP : 0 < 4 ^ bExp k := by positivity
  have hQ : 0 < 2 ^ aExp k := by positivity
  have hL := one_le_blockLen k
  generalize 4 ^ bExp k = P at hP ⊢
  generalize 2 ^ aExp k = Q at hQ ⊢
  generalize blockLen k = L at hL ⊢
  have : 1 ≤ P * L * Q := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

lemma depth_nat (k : ℕ) :
    64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k ≤ 2 ^ depth k ∧
      2 ^ depth k < 2 * (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) := by
  have hN1 := depthArg_gt k
  have hd : depth k = Nat.clog 2 (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) := rfl
  rw [hd]
  generalize 64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k = N at hN1 ⊢
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hN1
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  have e : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N).pred := by
    rw [← pow_succ']
    exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma one_le_depth (k : ℕ) : 1 ≤ depth k :=
  Nat.clog_pos (b := 2) (by norm_num) (depthArg_gt k)

lemma depth_spec (k : ℕ) :
    64 * sig k ^ 2 * (blockLen k : ℝ) / lam k ≤ 2 ^ depth k ∧
      (2 : ℝ) ^ depth k < 128 * sig k ^ 2 * (blockLen k : ℝ) / lam k := by
  obtain ⟨h1, h2⟩ := depth_nat k
  have hlam : (lam k)⁻¹ = (2 : ℝ) ^ aExp k := by unfold lam; rw [inv_pow, inv_inv]
  have hsig : sig k ^ 2 = (4 : ℝ) ^ bExp k := by
    unfold sig; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : 64 * sig k ^ 2 * (blockLen k : ℝ) / lam k =
      ((64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam, hsig]; push_cast; ring
  have e2 : 128 * sig k ^ 2 * (blockLen k : ℝ) / lam k =
      ((2 * (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam, hsig]; push_cast; ring
  rw [e1, e2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma firstTrial_strictMono : StrictMono firstTrial := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  show firstTrial k < firstTrial k + nTrials k
  have : 0 < nTrials k := by unfold nTrials; positivity
  omega

lemma le_firstTrial (k : ℕ) : k ≤ firstTrial k :=
  firstTrial_strictMono.id_le k

lemma stage_spec (s : ℕ) : firstTrial (stage s) ≤ s ∧ s < firstTrial (stage s + 1) := by
  have h0 : firstTrial (stage s) ≤ s :=
    Nat.findGreatest_spec (P := fun k => firstTrial k ≤ s) (Nat.zero_le s) (by simp [firstTrial])
  refine ⟨h0, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hle : stage s + 1 ≤ s := le_trans (le_firstTrial _) h
  exact Nat.findGreatest_is_greatest (P := fun k => firstTrial k ≤ s)
    (Nat.lt_succ_self _) hle h

lemma stage_eq (s k : ℕ) (h1 : firstTrial k ≤ s) (h2 : s < firstTrial (k + 1)) : stage s = k := by
  obtain ⟨a1, a2⟩ := stage_spec s
  have hm := firstTrial_strictMono.monotone
  rcases lt_trichotomy (stage s) k with h | h | h
  · have := hm (show stage s + 1 ≤ k from h); omega
  · exact h
  · have := hm (show k + 1 ≤ stage s from h); omega

lemma trialLen_le (s : ℕ) : 8 * trialLen s ≤ blockLen (stage s) := by
  unfold trialLen blockLen
  have h1 : s + 1 ≤ firstTrial (stage s + 1) := Nat.succ_le_of_lt (stage_spec s).2
  have h2 : 21 ^ (s + 1) ≤ 21 ^ firstTrial (stage s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h2
  omega

lemma trialStart_mono : Monotone trialStart := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show trialStart k ≤ trialStart k + (blockLen (stage k) + 2) * spacing (stage k)
  omega

lemma blk_floor (k : ℕ) (x : (AddCircle (1 : ℝ))) : -(floorC k) ≤ blk k x := by
  have := OMA996.block_lower_floor (lam k) (sig k) (blockLen k) (depth k) (spacing k) (shift k)
    (lam_pos k) (by linarith [sig_ge k]) (one_le_blockLen k) (depth_spec k).1 x
  unfold blk floorC
  exact this

end Con
end OMA995
end

-- Sequence
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma trialOf_trial (s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    trialOf (21 ^ s + r - 2) = s := by
  unfold trialOf
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  unfold trialLen at hr2
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]; omega

lemma exists_trial (j : ℕ) : ∃ s r, 1 ≤ r ∧ r ≤ trialLen s ∧ j = 21 ^ s + r - 2 := by
  have h1 := Nat.pow_log_le_self 21 (by omega : j + 1 ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 21) (j + 1)
  rw [Nat.pow_succ] at h2
  refine ⟨Nat.log 21 (j + 1), j + 2 - 21 ^ Nat.log 21 (j + 1), ?_, ?_, ?_⟩
  · omega
  · unfold trialLen; omega
  · omega

lemma mExp_trial (s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    mExp (21 ^ s + r - 2) = trialStart s + r * spacing (stage s) := by
  unfold mExp
  rw [trialOf_trial s r hr1 hr2]
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have : 21 ^ s + r - 2 + 2 - 21 ^ s = r := by omega
  rw [this]

lemma mExp_strictMono : StrictMono mExp := by
  apply strictMono_nat_of_lt_succ
  intro j
  obtain ⟨s, r, h1, h2, rfl⟩ := exists_trial j
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  by_cases hr : r < trialLen s
  · have e : 21 ^ s + r - 2 + 1 = 21 ^ s + (r + 1) - 2 := by omega
    rw [e, mExp_trial s (r + 1) (by omega) hr, mExp_trial s r h1 h2, add_mul, one_mul]
    have : 0 < spacing (stage s) := by unfold spacing; omega
    omega
  · have hr' : r = trialLen s := by omega
    have e : 21 ^ s + r - 2 + 1 = 21 ^ (s + 1) + 1 - 2 := by
      rw [pow_succ]; unfold trialLen at hr'; omega
    have hlen : 1 ≤ trialLen (s + 1) := by
      unfold trialLen; have := Nat.one_le_pow (s + 1) 21 (by norm_num); omega
    rw [e, mExp_trial (s + 1) 1 le_rfl hlen, mExp_trial s r h1 h2, trialStart]
    have hL := trialLen_le s
    have hm : r * spacing (stage s) ≤
        (blockLen (stage s) + 2) * spacing (stage s) :=
      Nat.mul_le_mul_right _ (by omega)
    have : 0 < spacing (stage (s + 1)) := by unfold spacing; omega
    omega

lemma one_le_nSeq (j : ℕ) : 1 ≤ nSeq j := by
  unfold nSeq; exact Nat.one_le_two_pow

lemma isDyadicLacunary_nSeq : IsDyadicLacunary nSeq := by
  refine ⟨one_le_nSeq 0, fun k => ?_⟩
  unfold nSeq
  have h := mExp_strictMono (Nat.lt_succ_self k)
  calc 2 * 2 ^ mExp k = 2 ^ (mExp k + 1) := by ring
    _ ≤ 2 ^ mExp (k + 1) := Nat.pow_le_pow_right (by norm_num) h

end Con
end OMA995
end

-- SpikeMeasure
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA996
namespace Asm

lemma measurableSet_spikeSet (d : ℕ) : MeasurableSet (spikeSet d) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  unfold spikeSet
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

lemma haar_eq_volume_Ico (U : Set (AddCircle (1 : ℝ))) (hU : MeasurableSet U) :
    (haarAddCircle (T := 1)) U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' U)) := by
  have h1 : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma measure_spikeSet (d : ℕ) : (haarAddCircle (T := 1)) (spikeSet d) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [haar_eq_volume_Ico _ (measurableSet_spikeSet d)]
  have hset : Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' spikeSet d) =
      Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
    ext x
    constructor
    · rintro ⟨hx01, ⟨u, hu, hux⟩⟩
      have hx' : x ∈ Set.Ico (0 : ℝ) (0 + 1) := by rw [zero_add]; exact hx01
      have hu' : u ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have e1 := AddCircle.equivIco_coe_of_mem hx'
      have e2 := AddCircle.equivIco_coe_of_mem hu'
      have hxu : x = u := by
        have : (AddCircle.equivIco 1 0 (x : (AddCircle (1 : ℝ))) : ℝ) = (AddCircle.equivIco 1 0 (u : (AddCircle (1 : ℝ))) : ℝ) := by
          rw [hux]
        rw [e1, e2] at this
        exact this
      rw [hxu]; exact hu
    · intro hx
      exact ⟨⟨hx.1, lt_of_lt_of_le hx.2 ht1⟩, ⟨x, hx, rfl⟩⟩
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma spike_eq (d : ℕ) (x : (AddCircle (1 : ℝ))) :
    spike d x = ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  have : spike d = fun x => ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl
  rw [this]
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma abs_spike_le (d : ℕ) (x : (AddCircle (1 : ℝ))) : |spike d x| ≤ 2 ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [spike]
  rw [spike_eq]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hct : t ≤ Real.sqrt (t * (1 - t)) := by
    have := Real.abs_le_sqrt (x := t) (y := t * (1 - t)) (by nlinarith)
    rwa [abs_of_pos ht0] at this
  have hc : 0 < Real.sqrt (t * (1 - t)) := lt_of_lt_of_le ht0 hct
  have hnum : |(spikeSet d).indicator 1 x - t| ≤ 1 := by
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]
      simp only [Pi.one_apply]
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem h]
      rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos hc]
  calc |(spikeSet d).indicator 1 x - t| / Real.sqrt (t * (1 - t))
      ≤ 1 / Real.sqrt (t * (1 - t)) := div_le_div_of_nonneg_right hnum hc.le
    _ ≤ 1 / t := one_div_le_one_div_of_le ht0 hct
    _ = 2 ^ d := by rw [ht, one_div, inv_pow, inv_inv]

lemma measurableSet_hitSet (d v : ℕ) : MeasurableSet (hitSet d v) :=
  (continuous_nsmul (2 ^ v)).measurable (measurableSet_spikeSet d)

lemma measurePreserving_nsmul (n : ℕ) (hn : n ≠ 0) :
    MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => n • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := by
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) :=
    Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) (by exact_mod_cast hn)
  have e : (fun x : (AddCircle (1 : ℝ)) => n • x) = fun x => (n : ℤ) • x := by
    funext x; exact (natCast_zsmul x n).symm
  rw [e]; exact hmp

lemma measure_hitSet (d v : ℕ) : (haarAddCircle (T := 1)) (hitSet d v) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have hmp := measurePreserving_nsmul (2 ^ v) (by positivity)
  have : hitSet d v = (fun x : (AddCircle (1 : ℝ)) => (2 ^ v : ℕ) • x) ⁻¹' spikeSet d := rfl
  rw [this, hmp.measure_preimage (measurableSet_spikeSet d).nullMeasurableSet]
  exact measure_spikeSet d

lemma integral_nsmul_comp (n : ℕ) (hn : n ≠ 0) (g : (AddCircle (1 : ℝ)) → ℝ) (hg : Measurable g) :
    ∫ x, g (n • x) ∂(haarAddCircle (T := 1)) = ∫ x, g x ∂(haarAddCircle (T := 1)) := by
  have hmp := measurePreserving_nsmul n hn
  rw [← integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable), hmp.map_eq]

lemma integral_indicator_spikeSet (d : ℕ) :
    ∫ x, (spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x ∂(haarAddCircle (T := 1)) = (2 : ℝ)⁻¹ ^ d := by
  rw [integral_indicator_one (measurableSet_spikeSet d), measureReal_def, measure_spikeSet]
  simp

lemma integrable_indicator_spikeSet (d : ℕ) :
    Integrable (fun x => (spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x) (haarAddCircle (T := 1)) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_spikeSet d)

lemma integral_spike_nsmul (d n : ℕ) (hn : n ≠ 0) : ∫ x, spike d (n • x) ∂(haarAddCircle (T := 1)) = 0 := by
  rw [integral_nsmul_comp n hn _ (measurable_spike d)]
  simp only [spike_eq]
  rw [integral_div, integral_sub (integrable_indicator_spikeSet d) (integrable_const _),
    integral_indicator_spikeSet, integral_const]
  simp

lemma integral_spike_nsmul_sq (d n : ℕ) (hd : 1 ≤ d) (hn : n ≠ 0) :
    ∫ x, spike d (n • x) ^ 2 ∂(haarAddCircle (T := 1)) = 1 := by
  rw [integral_nsmul_comp n hn (fun y => spike d y ^ 2) ((measurable_spike d).pow_const 2)]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpos : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hpt : ∀ x : (AddCircle (1 : ℝ)), spike d x ^ 2 =
      ((spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x * (1 - 2 * t) + t ^ 2) / (t * (1 - t)) := by
    intro x
    rw [spike_eq, div_pow, Real.sq_sqrt hpos.le]
    congr 1
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]; simp only [Pi.one_apply]; ring
    · rw [Set.indicator_of_notMem h]; ring
  simp only [hpt]
  rw [integral_div, integral_add ((integrable_indicator_spikeSet d).mul_const _)
    (integrable_const _), integral_mul_const, integral_indicator_spikeSet, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [div_eq_one_iff_eq hpos.ne']
  ring

end Asm
end OMA996
end

-- HitWindow
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA996
namespace Asm

lemma coe_mem_image_Ico_iff (z c : ℝ) (hc : c ≤ 1) :
    ((z : (AddCircle (1 : ℝ))) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) c : Set (AddCircle (1 : ℝ)))) ↔ Int.fract z < c := by
  constructor
  · rintro ⟨w, hw, h⟩
    have h1 : ((w : ℝ) : (AddCircle (1 : ℝ))) = ((Int.fract z : ℝ) : (AddCircle (1 : ℝ))) := by
      rw [AddCircle.coe_fract]; exact h
    have hw' : w ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hw.1, by linarith [hw.2]⟩
    have hf' : Int.fract z ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg z, by simpa using Int.fract_lt_one z⟩
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hw' hf').1 h1
    rw [← this]; exact hw.2
  · intro h
    exact ⟨Int.fract z, ⟨Int.fract_nonneg z, h⟩, AddCircle.coe_fract z⟩

lemma fract_lt_two_inv_pow_succ (z : ℝ) (d : ℕ) :
    Int.fract z < (2 : ℝ)⁻¹ ^ (d + 1) ↔
      Int.fract z < 2⁻¹ ∧ Int.fract (2 * z) < (2 : ℝ)⁻¹ ^ d := by
  have hpow : (2 : ℝ)⁻¹ ^ (d + 1) = 2⁻¹ * (2 : ℝ)⁻¹ ^ d := by rw [pow_succ]; ring
  have hle : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  by_cases hf : Int.fract z < 2⁻¹
  · have h2 : Int.fract (2 * z) = 2 * Int.fract z := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [Int.fract_nonneg z], by linarith, 2 * ⌊z⌋, ?_⟩
      rw [Int.fract]; push_cast; ring
    rw [h2, hpow]
    constructor
    · intro h; exact ⟨hf, by linarith⟩
    · rintro ⟨-, h⟩; linarith
  · constructor
    · intro h; exfalso; apply hf; rw [hpow] at h; nlinarith
    · rintro ⟨h, -⟩; exact absurd h hf

lemma fract_lt_two_inv_pow_iff (d : ℕ) : ∀ z : ℝ,
    Int.fract z < (2 : ℝ)⁻¹ ^ d ↔ ∀ i < d, Int.fract ((2 : ℝ) ^ i * z) < 2⁻¹ := by
  induction d with
  | zero =>
    intro z
    simp only [pow_zero, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true]
    exact Int.fract_lt_one z
  | succ d ih =>
    intro z
    rw [fract_lt_two_inv_pow_succ, ih (2 * z)]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h i (by omega)
        rw [pow_succ, mul_assoc]; exact this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rw [pow_succ, mul_assoc] at this; exact this

lemma mem_hitSet_iff (d v : ℕ) (x : (AddCircle (1 : ℝ))) :
    x ∈ hitSet d v ↔ ∀ j, v ≤ j → j < v + d →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ := by
  set y : ℝ := (AddCircle.equivIco 1 0 x : ℝ)
  have hx : ((y : ℝ) : (AddCircle (1 : ℝ))) = x := AddCircle.coe_equivIco
  have hsmul : (2 ^ v : ℕ) • x = (((2 : ℝ) ^ v * y : ℝ) : (AddCircle (1 : ℝ))) := by
    rw [← hx, ← AddCircle.coe_nsmul, nsmul_eq_mul]; push_cast; rfl
  simp only [hitSet, spikeSet, Set.mem_ofPred_eq]
  rw [hsmul, coe_mem_image_Ico_iff _ _ (pow_le_one₀ (by norm_num) (by norm_num)),
    fract_lt_two_inv_pow_iff]
  constructor
  · intro h j hj1 hj2
    have := h (j - v) (by omega)
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj1] at this
    exact this
  · intro h i hi
    rw [← mul_assoc, ← pow_add]
    exact h (i + v) (by omega) (by omega)

lemma determinedByWindow_hitSet (d v : ℕ) : DeterminedByWindow v (v + d) (hitSet d v) := by
  intro x y h
  rw [mem_hitSet_iff, mem_hitSet_iff]
  constructor
  · intro hx j hj1 hj2; exact (h j).1 (fun _ _ => hx j hj1 hj2)
  · intro hy j hj1 hj2; exact (h j).2 (hy j hj1 hj2) hj1 hj2

lemma DeterminedByWindow.compl' {a b : ℕ} {E : Set (AddCircle (1 : ℝ))} (h : DeterminedByWindow a b E) :
    DeterminedByWindow a b Eᶜ := by
  intro x y hxy
  exact not_congr (h x y hxy)

end Asm
end OMA996
end

-- DigitIndependence
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

namespace DigitIndep

lemma haar_eq (U : Set (AddCircle (1 : ℝ))) (hU : MeasurableSet U) :
    (haarAddCircle (T := 1)) U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' U)) := by
  have h1 : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma digit_mk (j : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 (y : (AddCircle (1 : ℝ))) : ℝ)) =
      Int.fract ((2 : ℝ) ^ j * y) := by
  rw [coe_equivIco_mk_apply, div_one, mul_one]
  have hy : Int.fract y = y - ⌊y⌋ := rfl
  have : (2 : ℝ) ^ j * ⌊y⌋ = ((2 ^ j * ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [hy, mul_sub, this, Int.fract_sub_intCast]

lemma digit_shift {A j : ℕ} (hj : A ≤ j) (m : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A)) = Int.fract ((2 : ℝ) ^ j * y) := by
  have h : (2 : ℝ) ^ j = 2 ^ (j - A) * 2 ^ A := by rw [← pow_add, Nat.sub_add_cancel hj]
  have : (2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A) = 2 ^ j * y + ((m * 2 ^ (j - A) : ℕ) : ℝ) := by
    rw [h]; push_cast; field_simp
  rw [this, Int.fract_add_natCast]

lemma fract_lt_half_iff (u : ℝ) : Int.fract u < 2⁻¹ ↔ ⌊2 * u⌋ % 2 = 0 := by
  have h1 := Int.fract_nonneg u
  have h2 := Int.fract_lt_one u
  have h3 : (⌊u⌋ : ℝ) + Int.fract u = u := Int.floor_add_fract u
  by_cases hf : Int.fract u < 2⁻¹
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp [hf]
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp only [hf, false_iff]; omega

lemma floor_le_of_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (hy : (m : ℝ) ≤ 2 ^ A * y') (hy' : 2 ^ A * y < m + 1) :
    ⌊2 * (2 ^ j * y)⌋ ≤ ⌊2 * (2 ^ j * y')⌋ := by
  by_contra hlt
  push_neg at hlt
  have e1 : 2 * (2 ^ j * y') < (⌊2 * (2 ^ j * y')⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have e2 : ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) ≤ 2 * (2 ^ j * y) :=
    (Int.cast_le.mpr (Int.add_one_le_of_lt hlt)).trans (Int.floor_le _)
  have hA : (2 : ℝ) ^ A = 2 * 2 ^ j * 2 ^ (A - j - 1) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (A - j - 1) := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) :=
    ⟨2 ^ (A - j - 1) * (⌊2 * (2 ^ j * y')⌋ + 1), by push_cast; ring⟩
  have h1 : (m : ℝ) < c :=
    calc (m : ℝ) ≤ 2 ^ A * y' := hy
      _ = 2 ^ (A - j - 1) * (2 * (2 ^ j * y')) := by rw [hA]; ring
      _ < 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left e1 hpos
      _ = c := hc.symm
  have h2 : (c : ℝ) < m + 1 :=
    calc (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) := by
          rw [hc]; push_cast; ring
      _ ≤ 2 ^ (A - j - 1) * (2 * (2 ^ j * y)) := mul_le_mul_of_nonneg_left e2 hpos.le
      _ = 2 ^ A * y := by rw [hA]; ring
      _ < m + 1 := hy'
  have h1' : m < c := by exact_mod_cast h1
  have h2' : c < m + 1 := by exact_mod_cast h2
  omega

lemma digit_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (h1 : (m : ℝ) ≤ 2 ^ A * y) (h2 : 2 ^ A * y < m + 1)
    (h1' : (m : ℝ) ≤ 2 ^ A * y') (h2' : 2 ^ A * y' < m + 1) :
    Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * y') < 2⁻¹ := by
  rw [fract_lt_half_iff, fract_lt_half_iff,
    le_antisymm (floor_le_of_block hj h1' h2) (floor_le_of_block hj h1 h2')]

def StrongDet (a b : ℕ) (E : Set (AddCircle (1 : ℝ))) : Prop :=
  ∀ x y : (AddCircle (1 : ℝ)), (∀ j, a ≤ j → j < b →
      (Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹)) → (x ∈ E ↔ y ∈ E)

noncomputable def proj (a b : ℕ) (y : ℝ) : ℝ :=
  ((⌊(2 : ℝ) ^ b * y⌋ - 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ : ℤ) : ℝ) / 2 ^ b

lemma proj_digits {a b : ℕ} (hab : a ≤ b) (y : ℝ) (j : ℕ) :
    (a ≤ j → j < b → (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹)) ∧
    (¬(a ≤ j ∧ j < b) → Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹) := by
  have hK1 : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := Int.floor_le _
  have hK2 : (2 : ℝ) ^ b * y < ⌊(2 : ℝ) ^ b * y⌋ + 1 := Int.lt_floor_add_one _
  have hL1 : (⌊(2 : ℝ) ^ a * y⌋ : ℝ) ≤ 2 ^ a * y := Int.floor_le _
  have hL2 : (2 : ℝ) ^ a * y < ⌊(2 : ℝ) ^ a * y⌋ + 1 := Int.lt_floor_add_one _
  have hba : (2 : ℝ) ^ b = 2 ^ (b - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hpb : (0 : ℝ) < 2 ^ b := by positivity
  have hpba : (0 : ℝ) < 2 ^ (b - a) := by positivity
  have hN0 : 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ ≤ ⌊(2 : ℝ) ^ b * y⌋ := by
    rw [Int.le_floor]; push_cast; rw [hba, mul_assoc]
    exact mul_le_mul_of_nonneg_left hL1 hpba.le
  have hN1 : ⌊(2 : ℝ) ^ b * y⌋ < 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) := by
    have : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) <
        ((2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) : ℤ) : ℝ) := by
      push_cast
      calc (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := hK1
        _ = 2 ^ (b - a) * (2 ^ a * y) := by rw [hba]; ring
        _ < 2 ^ (b - a) * ((⌊(2 : ℝ) ^ a * y⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left hL2 hpba
        _ = _ := by ring
    exact_mod_cast this
  set K := ⌊(2 : ℝ) ^ b * y⌋ with hK
  set L := ⌊(2 : ℝ) ^ a * y⌋ with hL
  set N : ℤ := K - 2 ^ (b - a) * L with hN
  have hN0' : (0 : ℝ) ≤ N := by
    have : (0 : ℤ) ≤ N := by rw [hN]; linarith
    exact_mod_cast this
  have hN1' : (N : ℝ) + 1 ≤ 2 ^ (b - a) := by
    have : N + 1 ≤ 2 ^ (b - a) := by rw [hN]; linarith
    exact_mod_cast this
  have hp : proj a b y = (N : ℝ) / 2 ^ b := rfl
  constructor
  · intro h1 h2
    have hja : (2 : ℝ) ^ j = 2 ^ (j - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h1]
    have e : (2 : ℝ) ^ j * proj a b y = 2 ^ j * ((K : ℝ) / 2 ^ b) - ((2 ^ (j - a) * L : ℤ) : ℝ) := by
      rw [hp, hN]; push_cast; rw [hja, hba]; field_simp
    rw [e, Int.fract_sub_intCast]
    have e2 : (2 : ℝ) ^ b * ((K : ℝ) / 2 ^ b) = K := by field_simp
    exact digit_block h2 (m := K) hK1 hK2 (le_of_eq e2.symm) (by rw [e2]; linarith)
  · intro hj
    by_cases hjb : b ≤ j
    · have hjb' : (2 : ℝ) ^ j = 2 ^ (j - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hjb]
      have e : (2 : ℝ) ^ j * proj a b y = ((N * 2 ^ (j - b) : ℤ) : ℝ) := by
        rw [hp, hjb']; push_cast; field_simp
      rw [e, Int.fract_intCast]; norm_num
    · have hja : j < a := by omega
      have h2j : (2 : ℝ) * 2 ^ j ≤ 2 ^ a := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hja
      have hlt : 2 * (2 ^ j * (N : ℝ)) < 2 ^ b :=
        calc 2 * (2 ^ j * (N : ℝ)) = (2 * 2 ^ j) * N := by ring
          _ ≤ 2 ^ a * N := mul_le_mul_of_nonneg_right h2j hN0'
          _ < 2 ^ a * 2 ^ (b - a) := mul_lt_mul_of_pos_left (by linarith) hpa
          _ = 2 ^ b := by rw [hba]; ring
      have h0 : 0 ≤ (2 : ℝ) ^ j * proj a b y := by
        rw [hp]; exact mul_nonneg (by positivity) (div_nonneg hN0' hpb.le)
      have hhalf : (2 : ℝ) ^ j * proj a b y < 2⁻¹ := by
        rw [hp, ← mul_div_assoc, div_lt_iff₀ hpb]; linarith
      rw [Int.fract_eq_self.mpr ⟨h0, by linarith⟩]
      exact hhalf

lemma strong_of_det {a b : ℕ} {E : Set (AddCircle (1 : ℝ))} (hE : DeterminedByWindow a b E) : StrongDet a b E := by
  intro x x' hxx'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective x'
  by_cases hab : a ≤ b
  · have key : ∀ w : ℝ, (∀ j, a ≤ j → j < b →
        (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * w) < 2⁻¹)) →
        (((w : ℝ) : (AddCircle (1 : ℝ))) ∈ E ↔ ((proj a b y : ℝ) : (AddCircle (1 : ℝ))) ∈ E) := by
      intro w hw
      apply hE
      intro j
      rw [digit_mk, digit_mk]
      by_cases hj : a ≤ j ∧ j < b
      · have hc := (hw j hj.1 hj.2).symm.trans ((proj_digits hab y j).1 hj.1 hj.2)
        constructor
        · intro h; exact hc.1 (h hj.1 hj.2)
        · intro h _ _; exact hc.2 h
      · have := (proj_digits hab y j).2 hj
        constructor
        · intro _; exact this
        · intro _ h1 h2; exact absurd ⟨h1, h2⟩ hj
    refine (key y (fun j _ _ => Iff.rfl)).trans (key y' (fun j h1 h2 => ?_)).symm
    have := hxx' j h1 h2
    rwa [digit_mk, digit_mk] at this
  · have key : ∀ w : ℝ, (((w : ℝ) : (AddCircle (1 : ℝ))) ∈ E ↔ (((0 : ℝ) : ℝ) : (AddCircle (1 : ℝ))) ∈ E) := by
      intro w
      apply hE
      intro j
      rw [digit_mk, digit_mk, mul_zero, Int.fract_zero]
      constructor
      · intro _; norm_num
      · intro _ h1 h2; omega
    exact (key y).trans (key y').symm

def dyBlock (A m : ℕ) : Set ℝ := {y | (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1}

lemma mem_dyBlock {A m : ℕ} {y : ℝ} :
    y ∈ dyBlock A m ↔ (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1 := Iff.rfl

lemma measurableSet_dyBlock (A m : ℕ) : MeasurableSet (dyBlock A m) :=
  show MeasurableSet ({y : ℝ | (m : ℝ) ≤ 2 ^ A * y} ∩ {y : ℝ | 2 ^ A * y < m + 1}) from
    (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)

lemma Ico_decomp (A : ℕ) (X : Set ℝ) (hX : MeasurableSet X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ X) = ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ X) := by
  have hpos : (0 : ℝ) < 2 ^ A := by positivity
  have hset : Set.Ico (0 : ℝ) 1 ∩ X = ⋃ m ∈ range (2 ^ A), (dyBlock A m ∩ X) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop,
      mem_dyBlock]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      have hnn : 0 ≤ (2 : ℝ) ^ A * y := mul_nonneg hpos.le h0
      refine ⟨⌊(2 : ℝ) ^ A * y⌋₊, ?_, ⟨Nat.floor_le hnn, Nat.lt_floor_add_one _⟩, hx⟩
      rw [Nat.floor_lt hnn]; push_cast
      calc (2 : ℝ) ^ A * y < 2 ^ A * 1 := mul_lt_mul_of_pos_left h1 hpos
        _ = 2 ^ A := mul_one _
    · rintro ⟨m, hm, ⟨h1, h2⟩, hx⟩
      have hm' : (m : ℝ) + 1 ≤ 2 ^ A := by exact_mod_cast Nat.succ_le_of_lt hm
      refine ⟨⟨?_, ?_⟩, hx⟩
      · by_contra h
        push_neg at h
        have := mul_neg_of_pos_of_neg hpos h
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      · by_contra h
        push_neg at h
        have := mul_le_mul_of_nonneg_left h hpos.le
        linarith
  rw [hset, measure_biUnion_finset]
  · intro m _ m' _ hne
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨⟨a1, a2⟩, _⟩ ⟨⟨b1, b2⟩, _⟩
    have e1 : (m : ℝ) < m' + 1 := by linarith
    have e2 : (m' : ℝ) < m + 1 := by linarith
    have e1' : m < m' + 1 := by exact_mod_cast e1
    have e2' : m' < m + 1 := by exact_mod_cast e2
    exact hne (by omega)
  · intro m _
    exact (measurableSet_dyBlock A m).inter hX

lemma dyBlock_shift (A m : ℕ) (X : Set ℝ) (hinv : ∀ y : ℝ, y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (dyBlock A m ∩ X) = volume (dyBlock A 0 ∩ X) := by
  have : dyBlock A 0 ∩ X = (fun y => y + (m : ℝ) / 2 ^ A) ⁻¹' (dyBlock A m ∩ X) := by
    ext y
    have e : (2 : ℝ) ^ A * (y + m / 2 ^ A) = 2 ^ A * y + m := by
      rw [mul_add]; congr 1; field_simp
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_dyBlock, e, hinv, Nat.cast_zero]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [this, measure_preimage_add_right]

open Classical in
lemma sum_formula (A : ℕ) (G X : Set ℝ) (hG : MeasurableSet G) (hX : MeasurableSet X)
    (hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ G) ∨ (∀ y ∈ dyBlock A m, y ∉ G))
    (hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ (G ∩ X)) =
      ((range (2 ^ A)).filter (fun m => ∀ y ∈ dyBlock A m, y ∈ G)).card *
        volume (dyBlock A 0 ∩ X) := by
  rw [Ico_decomp A _ (hG.inter hX)]
  calc ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ (G ∩ X))
      = ∑ m ∈ range (2 ^ A),
          (if (∀ y ∈ dyBlock A m, y ∈ G) then volume (dyBlock A 0 ∩ X) else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases h : ∀ y ∈ dyBlock A m, y ∈ G
        · rw [if_pos h, ← dyBlock_shift A m X (hinv m)]
          congr 1
          ext y
          constructor
          · rintro ⟨hy, _, hx⟩; exact ⟨hy, hx⟩
          · rintro ⟨hy, hx⟩; exact ⟨hy, h y hy, hx⟩
        · rw [if_neg h]
          have h' := (hblock m).resolve_left h
          have : dyBlock A m ∩ (G ∩ X) = ∅ :=
            Set.subset_empty_iff.mp (fun y hy => (h' y hy.1 hy.2.1).elim)
          rw [this, measure_empty]
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma ennreal_aux (cG cU u t : ENNReal) (h : cU * u = 1) : cG * t = cG * u * (cU * t) := by
  calc cG * t = cG * t * (cU * u) := by rw [h, mul_one]
    _ = cG * u * (cU * t) := by ring

lemma indep_two {A B : ℕ} {F E : Set (AddCircle (1 : ℝ))} (hF : StrongDet 0 A F)
    (hE : StrongDet A B E) (mF : MeasurableSet F) (mE : MeasurableSet E) :
    (haarAddCircle (T := 1)) (F ∩ E) = (haarAddCircle (T := 1)) F * (haarAddCircle (T := 1)) E := by
  have hG : MeasurableSet (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) := AddCircle.measurable_mk' mF
  have hX : MeasurableSet (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E) := AddCircle.measurable_mk' mE
  have hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∨
      (∀ y ∈ dyBlock A m, y ∉ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) := by
    intro m
    by_cases h : ∃ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F
    · left
      obtain ⟨y0, hy0, hy0G⟩ := h
      intro y hy
      rw [mem_dyBlock] at hy0 hy
      exact (hF (y0 : (AddCircle (1 : ℝ))) (y : (AddCircle (1 : ℝ))) (fun j _ hj => by
        rw [digit_mk, digit_mk]
        exact digit_block hj (m := (m : ℤ)) (by exact_mod_cast hy0.1) (by exact_mod_cast hy0.2)
          (by exact_mod_cast hy.1) (by exact_mod_cast hy.2))).1 hy0G
    · right
      push_neg at h
      exact h
  have hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E ↔
      y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E := by
    intro m y
    apply hE
    intro j hj _
    rw [digit_mk, digit_mk, digit_shift hj]
  have hinvU : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ (Set.univ : Set ℝ) ↔
      y ∈ (Set.univ : Set ℝ) := fun _ _ => Iff.rfl
  have hblockU : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ (Set.univ : Set ℝ)) ∨
      (∀ y ∈ dyBlock A m, y ∉ (Set.univ : Set ℝ)) := fun _ => Or.inl fun _ _ => trivial
  have kFE := sum_formula A _ _ hG hX hblock hinv
  have kF := sum_formula A _ _ hG MeasurableSet.univ hblock hinvU
  have kE := sum_formula A _ _ MeasurableSet.univ hX hblockU hinv
  have kU := sum_formula A _ _ MeasurableSet.univ MeasurableSet.univ hblockU hinvU
  rw [haar_eq _ (mF.inter mE), haar_eq _ mF, haar_eq _ mE]
  have e1 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' (F ∩ E))) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E))) := rfl
  have e2 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∩ Set.univ)) := by
    rw [Set.inter_univ]
  have e3 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ (Set.univ ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E))) := by
    rw [Set.univ_inter]
  have e4 : volume (Set.Ico (0 : ℝ) 1 ∩ ((Set.univ : Set ℝ) ∩ Set.univ)) = 1 := by simp
  rw [e1, e2, e3, kFE, kF, kE]
  rw [kU] at e4
  exact ennreal_aux _ _ _ _ e4

lemma det_mono {a b a' b' : ℕ} {E : Set (AddCircle (1 : ℝ))} (h : StrongDet a b E)
    (hw : ∀ j, a ≤ j → j < b → a' ≤ j ∧ j < b') : StrongDet a' b' E :=
  fun x y hxy => h x y (fun j h1 h2 => hxy j (hw j h1 h2).1 (hw j h1 h2).2)

lemma det_iInter {ι : Type*} {a b : ℕ} (s : Finset ι) (E : ι → Set (AddCircle (1 : ℝ)))
    (h : ∀ i ∈ s, StrongDet a b (E i)) : StrongDet a b (⋂ i ∈ s, E i) := by
  intro x y hxy
  simp only [Set.mem_iInter]
  exact forall₂_congr fun i hi => h i hi x y hxy

end DigitIndep

open DigitIndep in

lemma measure_iInter_of_disjoint_windows {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (E : ι → Set (AddCircle (1 : ℝ))) (hE : ∀ i ∈ s, DeterminedByWindow (a i) (b i) (E i))
    (hmeas : ∀ i ∈ s, MeasurableSet (E i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (haarAddCircle (T := 1)) (⋂ i ∈ s, E i) = ∏ i ∈ s, (haarAddCircle (T := 1)) (E i) := by
  classical
  have hE' : ∀ i ∈ s, StrongDet (a i) (b i) (E i) := fun i hi => strong_of_det (hE i hi)
  clear hE
  revert hE' hmeas hdisj
  induction s using Finset.induction_on_max_value (f := b) with
  | empty => intro _ _ _; simp
  | insert i s hi hmax ih =>
    intro hmeas hdisj hE
    rw [Finset.prod_insert hi, Finset.set_biInter_insert, Set.inter_comm]
    have hF : StrongDet 0 (a i) (⋂ j ∈ s, E j) := by
      refine det_iInter s E (fun j hj => det_mono (hE j (Finset.mem_insert_of_mem hj)) ?_)
      intro k hk1 hk2
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hb := hmax j hj
      rcases hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) hij with h | h
      · omega
      · omega
    rw [indep_two hF (hE i (Finset.mem_insert_self i s))
      (Finset.measurableSet_biInter s (fun j hj => hmeas j (Finset.mem_insert_of_mem hj)))
      (hmeas i (Finset.mem_insert_self i s))]
    rw [ih (fun j hj => hmeas j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj => hE j (Finset.mem_insert_of_mem hj)),
      mul_comm]

end OMA996
end

-- StageProb
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma one_sub_pow_le_aux (r : ℝ) (n m : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hn : (2 : ℝ) ^ m ≤ n * r) : (1 - r) ^ n ≤ (2⁻¹ : ℝ) ^ m := by
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ r) n
  have h1 : (2 : ℝ) ^ m ≤ (1 + r) ^ n := by linarith
  have h2 : (1 - r) ^ n * (1 + r) ^ n ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - r) ^ n := pow_nonneg (by linarith) n
  have h4 : (1 - r) ^ n * 2 ^ m ≤ 1 := le_trans (mul_le_mul_of_nonneg_left h1 h3) h2
  rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
  exact h4

lemma ennreal_inv_two_pow (m : ℕ) :
    ((2⁻¹ : ℝ≥0∞)) ^ m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ m) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

def stagePairs (k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Ico (firstTrial k) (firstTrial (k + 1))).sigma
    (fun s => Finset.Icc (trialLen s + 1) (blockLen k + 1))

def pairStart (k : ℕ) (i : Σ _ : ℕ, ℕ) : ℕ :=
  shift k + trialStart i.1 + i.2 * spacing k

lemma stage_of_mem_Ico {k s : ℕ} (hs : s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1))) :
    stage s = k := by
  rw [Finset.mem_Ico] at hs
  exact stage_eq s k hs.1 hs.2

lemma compl_stageGood_eq (k : ℕ) :
    (stageGood k)ᶜ = ⋂ i ∈ stagePairs k, (OMA996.Asm.hitSet (depth k) (pairStart k i))ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, stageGood, Set.mem_iInter]
  constructor
  · intro h i hi hx
    rw [stagePairs, Finset.mem_sigma] at hi
    apply h
    refine Set.mem_iUnion₂.mpr ⟨i.1, hi.1, ?_⟩
    rw [goodSet, stage_of_mem_Ico hi.1]
    exact Set.mem_iUnion₂.mpr ⟨i.2, hi.2, hx⟩
  · intro h hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [goodSet, stage_of_mem_Ico hs] at hx
    obtain ⟨hh, hhm, hx⟩ := Set.mem_iUnion₂.mp hx
    exact h ⟨s, hh⟩ (by rw [stagePairs, Finset.mem_sigma]; exact ⟨hs, hhm⟩) hx

lemma pairStart_lt_of_lt (k : ℕ) {s h s' h' : ℕ}
    (hs : s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)))
    (hh : h ≤ blockLen k + 1) (hss' : s < s') :
    pairStart k ⟨s, h⟩ + depth k ≤ pairStart k ⟨s', h'⟩ := by
  have hM : trialStart (s + 1) = trialStart s + (blockLen k + 2) * spacing k := by
    show trialStart s + (blockLen (stage s) + 2) * spacing (stage s) = _
    rw [stage_of_mem_Ico hs]
  have hmono : trialStart (s + 1) ≤ trialStart s' := trialStart_mono hss'
  have e1 : h * spacing k ≤ (blockLen k + 1) * spacing k := Nat.mul_le_mul_right _ hh
  have e2 : (blockLen k + 2) * spacing k = (blockLen k + 1) * spacing k + spacing k := by
    ring
  have hD : spacing k = depth k + 2 := rfl
  simp only [pairStart]
  omega

lemma pairStart_disj (k : ℕ) :
    ∀ i ∈ stagePairs k, ∀ j ∈ stagePairs k, i ≠ j →
      pairStart k i + depth k ≤ pairStart k j ∨
        pairStart k j + depth k ≤ pairStart k i := by
  intro i hi j hj hij
  rcases i with ⟨s, h⟩
  rcases j with ⟨s', h'⟩
  rw [stagePairs, Finset.mem_sigma, Finset.mem_Icc] at hi hj
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · left; exact pairStart_lt_of_lt k hi.1 hi.2.2 hlt
  · subst heq
    have hne : h ≠ h' := by
      intro e; subst e; exact hij rfl
    have hD : spacing k = depth k + 2 := rfl
    simp only [pairStart]
    rcases lt_or_gt_of_ne hne with hl | hl
    · left
      have : (h + 1) * spacing k ≤ h' * spacing k := Nat.mul_le_mul_right _ hl
      have e2 : (h + 1) * spacing k = h * spacing k + spacing k := by ring
      omega
    · right
      have : (h' + 1) * spacing k ≤ h * spacing k := Nat.mul_le_mul_right _ hl
      have e2 : (h' + 1) * spacing k = h' * spacing k + spacing k := by ring
      omega
  · right; exact pairStart_lt_of_lt k hj.1 hj.2.2 hgt

lemma card_stagePairs (k : ℕ) :
    7 * nTrials k * blockLen k ≤ 8 * (stagePairs k).card := by
  have hS : firstTrial (k + 1) = firstTrial k + nTrials k := rfl
  rw [stagePairs, Finset.card_sigma, Finset.mul_sum]
  calc 7 * nTrials k * blockLen k
      = ∑ _s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)), 7 * blockLen k := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, hS, Nat.add_sub_cancel_left]; ring
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Nat.card_Icc]
        have := trialLen_le s
        rw [stage_of_mem_Ico hs] at this
        omega

lemma stage_count_nat (k : ℕ) :
    2 ^ (k + 3) * 2 ^ depth k ≤ (stagePairs k).card := by
  have hcard := card_stagePairs k
  have hd := (depth_nat k).2
  set X := 4 ^ bExp k * blockLen k * 2 ^ aExp k with hX
  have hT : nTrials k * blockLen k = 2 ^ k * 2 ^ 24 * X := by
    simp only [nTrials, hX, pow_add, pow_mul]; norm_num; ring
  have hd' : 2 ^ depth k < 128 * X := by rw [hX]; linarith
  have h2k : 0 < 2 ^ k := by positivity
  have hle : 2 ^ (k + 3) * 2 ^ depth k ≤ 2 ^ k * 1024 * X := by
    rw [pow_add]
    calc 2 ^ k * 2 ^ 3 * 2 ^ depth k ≤ 2 ^ k * 2 ^ 3 * (128 * X) :=
          Nat.mul_le_mul_left _ hd'.le
      _ = 2 ^ k * 1024 * X := by ring
  have h7 : 7 * (2 ^ k * 2 ^ 24 * X) ≤ 8 * (stagePairs k).card := by
    rw [← hT, ← mul_assoc]; exact hcard
  have : 8 * (2 ^ k * 1024 * X) ≤ 7 * (2 ^ k * 2 ^ 24 * X) := by
    have : 8 * (2 ^ k * 1024 * X) = 8192 * (2 ^ k * X) := by ring
    have h' : 7 * (2 ^ k * 2 ^ 24 * X) = 117440512 * (2 ^ k * X) := by ring
    rw [this, h']; exact Nat.mul_le_mul_right _ (by norm_num)
  omega

lemma stage_count_real (k : ℕ) :
    (2 : ℝ) ^ (k + 3) ≤ ((stagePairs k).card : ℝ) * (2⁻¹ : ℝ) ^ depth k := by
  rw [inv_pow, le_mul_inv_iff₀ (by positivity)]
  exact_mod_cast stage_count_nat k

lemma measure_compl_stageGood_le (k : ℕ) :
    (haarAddCircle (T := 1)) (stageGood k)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 3) := by
  classical
  have hmeasI : (haarAddCircle (T := 1)) (⋂ i ∈ stagePairs k, (OMA996.Asm.hitSet (depth k) (pairStart k i))ᶜ) =
      ∏ i ∈ stagePairs k, (haarAddCircle (T := 1)) (OMA996.Asm.hitSet (depth k) (pairStart k i))ᶜ :=
    OMA996.measure_iInter_of_disjoint_windows (stagePairs k) (pairStart k)
      (fun i => pairStart k i + depth k)
      (fun i => (OMA996.Asm.hitSet (depth k) (pairStart k i))ᶜ)
      (fun i _ => OMA996.Asm.DeterminedByWindow.compl'
        (OMA996.Asm.determinedByWindow_hitSet _ _))
      (fun i _ => (OMA996.Asm.measurableSet_hitSet _ _).compl) (pairStart_disj k)
  have hEi : ∀ i, (haarAddCircle (T := 1)) (OMA996.Asm.hitSet (depth k) (pairStart k i))ᶜ =
      1 - (2⁻¹ : ℝ≥0∞) ^ depth k := by
    intro i
    rw [measure_compl (OMA996.Asm.measurableSet_hitSet _ _) (measure_ne_top _ _), measure_univ,
      OMA996.Asm.measure_hitSet]
  have hr1 : (2⁻¹ : ℝ) ^ depth k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ depth k := by positivity
  have hfin := one_sub_pow_le_aux _ (stagePairs k).card (k + 3) hr0 hr1 (stage_count_real k)
  rw [compl_stageGood_eq, hmeasI, Finset.prod_congr rfl (fun i _ => hEi i), Finset.prod_const,
    ennreal_inv_two_pow, ennreal_inv_two_pow, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal hfin

end Con
end OMA995
end

-- BorelCantelli
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma ae_eventually_stageGood : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ᶠ k in atTop, x ∈ stageGood k := by
  have hsum : ∑' k, (haarAddCircle (T := 1)) (stageGood k)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum measure_compl_stageGood_le)
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_ ?_
    · rw [ENNReal.tsum_geometric]; simp
    · exact ENNReal.tsum_le_tsum fun k => pow_le_pow_of_le_one (by simp) (by norm_num) (by omega)
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with k hk
  simpa using hk

end Con
end OMA995
end

-- SpikeFourierSupport
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

lemma fourierCoeff_nsmul_comp_eq_zero (n : ℕ) (hn : 0 < n) (g : (AddCircle (1 : ℝ)) → ℂ) (r : ℤ)
    (h : ¬ (n : ℤ) ∣ r) : fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r = 0 := by
  obtain ⟨a, ha_def⟩ : ∃ a : (AddCircle (1 : ℝ)), a = (((1 : ℝ) / n : ℝ) : (AddCircle (1 : ℝ))) := ⟨_, rfl⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : n • a = 0 := by
    have e : ((n • ((1 : ℝ) / n) : ℝ) : (AddCircle (1 : ℝ))) = n • (((1 : ℝ) / n : ℝ) : (AddCircle (1 : ℝ))) :=
      AddCircle.coe_nsmul (1 : ℝ)
    rw [ha_def, ← e, nsmul_eq_mul, mul_one_div_cancel hn']
    exact AddCircle.coe_period (1 : ℝ)
  have hI : fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r =
      fourier (-r) a * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    have hshift := integral_add_right_eq_self (μ := (haarAddCircle (T := 1)))
      (fun x : (AddCircle (1 : ℝ)) => fourier (-r) x • g (n • x)) a
    rw [← hshift]
    congr 1
    funext x
    have hf : fourier (-r) (x + a) = fourier (-r) x * fourier (-r) a := by
      rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
      rfl
    simp only [smul_add, ha, add_zero, smul_eq_mul, hf]
    ring
  have hne : fourier (-r) a ≠ 1 := by
    rw [ha_def, fourier_coe_apply]
    intro he
    rw [Complex.exp_eq_one_iff] at he
    obtain ⟨k, hk⟩ := he
    push_cast at hk
    have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : -(r : ℂ) * (1 / (n : ℂ)) = k := by
      apply mul_left_cancel₀ hpi
      linear_combination hk
    have h2 : (r : ℂ) = -(k : ℂ) * n := by
      rw [← h1]; field_simp
    have h3 : r = -k * n := by exact_mod_cast h2
    exact h ⟨-k, by rw [h3]; ring⟩
  have : (1 - fourier (-r) a) * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

lemma fourierCoeff_nsmul_comp_mul (n : ℕ) (hn : 0 < n) (g : (AddCircle (1 : ℝ)) → ℂ)
    (hg : AEStronglyMeasurable g (haarAddCircle (T := 1))) (s : ℤ) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) ((n : ℤ) * s) = fourierCoeff g s := by
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) :=
    Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) (by exact_mod_cast hn.ne')
  have hF : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) (haarAddCircle (T := 1)) :=
    (map_continuous (fourier (-s))).aestronglyMeasurable.smul hg
  have hpt : ∀ x : (AddCircle (1 : ℝ)), fourier (-((n : ℤ) * s)) x • g (n • x) =
      (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) ((n : ℤ) • x) := by
    intro x
    show fourier (-((n : ℤ) * s)) x • g (n • x) = fourier (-s) ((n : ℤ) • x) • g ((n : ℤ) • x)
    have e : n • x = (n : ℤ) • x := (natCast_zsmul x n).symm
    rw [e, fourier_apply, fourier_apply, smul_smul, show -((n : ℤ) * s) = -s * (n : ℤ) by ring]
  rw [fourierCoeff, fourierCoeff]
  calc ∫ t, fourier (-((n : ℤ) * s)) t • g (n • t) ∂(haarAddCircle (T := 1))
      = ∫ t, (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) ((n : ℤ) • t) ∂(haarAddCircle (T := 1)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ y, fourier (-s) y • g y ∂(Measure.map (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1))) :=
        (integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF)).symm
    _ = ∫ y, fourier (-s) y • g y ∂(haarAddCircle (T := 1)) := by rw [hmp.map_eq]

lemma measurableSet_spikeSet (d : ℕ) :
    MeasurableSet (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ))) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  unfold spike
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma mem_spikeSet_iff (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : x ∈ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d)) :
    ((x : (AddCircle (1 : ℝ))) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ)))) ↔
      x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
  constructor
  · rintro ⟨u, hu, hux⟩
    have hb : (2 : ℝ)⁻¹ ^ d ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have hux' : ((x : ℝ) : (AddCircle (1 : ℝ))) = ((u : ℝ) : (AddCircle (1 : ℝ))) := hux.symm
    have h0 : ((x - u : ℝ) : (AddCircle (1 : ℝ))) = 0 := by
      rw [AddCircle.coe_sub, hux', sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    rw [zsmul_eq_mul, mul_one] at hk
    have hk1 : (k : ℝ) < 1 := by linarith [hx.2, hu.1]
    have hk2 : (-1 : ℝ) < k := by linarith [hx.1, hu.2]
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hk1
      have : -1 < k := by exact_mod_cast hk2
      omega
    rw [hk0] at hk
    push_cast at hk
    have : x = u := by linarith
    rw [this]; exact hu
  · intro hx'
    exact ⟨x, hx', rfl⟩

lemma fourierCoeff_spike_eq_zero (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (hm : m ≠ 0) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) ((2 : ℤ) ^ d * m) = 0 := by
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  obtain ⟨C, hC_def⟩ : ∃ C : ℂ, C = 2 * π * Complex.I * (((-((2 : ℤ) ^ d * m)) : ℤ) : ℂ) :=
    ⟨_, rfl⟩
  have hC : C ≠ 0 := by
    rw [hC_def]; simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  have h2 : (2 : ℂ) ^ d * ((2 : ℂ)⁻¹) ^ d = 1 := by rw [← mul_pow]; norm_num
  have hCb : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨-m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hCb1 : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d - 1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨2 ^ d * m - m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hC0 : Complex.exp (C * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-((2 : ℤ) ^ d * m)) (x : (AddCircle (1 : ℝ))) • (spike d (x : (AddCircle (1 : ℝ))) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            Complex.exp (C * x) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    have hf : fourier (-((2 : ℤ) ^ d * m)) (x : (AddCircle (1 : ℝ))) = Complex.exp (C * x) := by
      rw [fourier_coe_apply, hC_def]
      congr 1
      push_cast; ring
    rw [hf]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun y : ℝ => Complex.exp (C * y)) := by fun_prop
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), Complex.exp (C * x) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) ((hcont.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI1,
    integral_exp_mul_complex hC, integral_exp_mul_complex hC, hCb, hCb1, hC0]
  simp

lemma fourierCoeff_spike_dilate_eq_zero (d v : ℕ) (r : ℤ) (hr : r ≠ 0)
    (h : ¬ (2 ^ v ∣ r ∧ ¬ 2 ^ (v + d) ∣ r)) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d ((2 ^ v : ℕ) • x) : ℂ)) r = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : (AddCircle (1 : ℝ)) => (spike 0 ((2 ^ v : ℕ) • x) : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hn : 0 < 2 ^ v := by positivity
  rw [not_and, not_not] at h
  by_cases hv : (2 : ℤ) ^ v ∣ r
  · obtain ⟨m, rfl⟩ := h hv
    have hm : m ≠ 0 := by rintro rfl; simp at hr
    have hr' : (2 : ℤ) ^ (v + d) * m = ((2 ^ v : ℕ) : ℤ) * ((2 : ℤ) ^ d * m) := by
      push_cast; ring
    have hmeas : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) (haarAddCircle (T := 1)) :=
      (Complex.measurable_ofReal.comp (measurable_spike d)).aestronglyMeasurable
    rw [hr']
    refine (fourierCoeff_nsmul_comp_mul (2 ^ v) hn (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) hmeas _).trans ?_
    exact fourierCoeff_spike_eq_zero d hd m hm
  · exact fourierCoeff_nsmul_comp_eq_zero (2 ^ v) hn (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) r
      (by push_cast; exact hv)

end OMA996
end

-- Params
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA996
namespace Asm

lemma lam_pos (A k : ℕ) : 0 < lam A k := by
  unfold lam; positivity

lemma lam_le_one (A k : ℕ) : lam A k ≤ 1 := by
  unfold lam; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma lam_le (A : ℕ) (hA : 1 ≤ A) (k : ℕ) : lam A k ≤ (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold lam aExp
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)

lemma geomSucc_summable : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) := by
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right (2⁻¹)
  exact this.congr (fun k => (pow_succ _ _).symm)

lemma geomSucc_tsum : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma summable_lam (A : ℕ) (hA : 1 ≤ A) : Summable (lam A) := by
  exact Summable.of_nonneg_of_le (fun k => (lam_pos A k).le) (lam_le A hA) geomSucc_summable

lemma tsum_lam_le_one (A : ℕ) (hA : 1 ≤ A) : ∑' k, lam A k ≤ 1 := by
  calc ∑' k, lam A k ≤ ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) :=
        Summable.tsum_le_tsum (lam_le A hA) (summable_lam A hA) geomSucc_summable
    _ = 1 := geomSucc_tsum

lemma floorC_nonneg (A k : ℕ) : 0 ≤ floorC A k := by
  unfold floorC; exact div_nonneg (lam_pos A k).le (by norm_num)

lemma summable_floorC (A : ℕ) (hA : 1 ≤ A) : Summable (floorC A) := by
  exact (summable_lam A hA).div_const 100

lemma tsum_floorC_le (A : ℕ) (hA : 1 ≤ A) : ∑' k, floorC A k ≤ 1 / 100 := by
  show ∑' k, lam A k / 100 ≤ 1 / 100
  rw [tsum_div_const]
  have := tsum_lam_le_one A hA
  linarith

lemma one_le_blockLen (A k : ℕ) : 1 ≤ blockLen A k := by
  unfold blockLen
  have : 0 < 21 ^ firstTrial A (k + 1) := by positivity
  omega

lemma depth_nat (A k : ℕ) :
    640000 * blockLen A k * 2 ^ aExp A k ≤ 2 ^ depth A k ∧
      2 ^ depth A k < 2 * (640000 * blockLen A k * 2 ^ aExp A k) := by
  have hN1 : 1 < 640000 * blockLen A k * 2 ^ aExp A k := by
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  have hd : depth A k = Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) := rfl
  rw [hd]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hN1
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  have e : 2 ^ Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) =
      2 * 2 ^ (Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)).pred := by
    rw [← pow_succ']
    exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma one_le_depth (A k : ℕ) : 1 ≤ depth A k := by
  obtain ⟨h1, _⟩ := depth_nat A k
  rcases Nat.eq_zero_or_pos (depth A k) with h | h
  · rw [h] at h1
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  · exact h

lemma depth_spec (A k : ℕ) :
    64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k ≤ 2 ^ depth A k ∧
      (2 : ℝ) ^ depth A k < 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k := by
  obtain ⟨h1, h2⟩ := depth_nat A k
  have hlam : (lam A k)⁻¹ = (2 : ℝ) ^ aExp A k := by unfold lam; rw [inv_pow, inv_inv]
  have e1 : 64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((640000 * blockLen A k * 2 ^ aExp A k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  have e2 : 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((2 * (640000 * blockLen A k * 2 ^ aExp A k) : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  rw [e1, e2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma firstTrial_strictMono (A : ℕ) : StrictMono (firstTrial A) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  show firstTrial A k < firstTrial A k + nTrials A k
  have : 0 < nTrials A k := by unfold nTrials; positivity
  omega

lemma le_firstTrial (A k : ℕ) : k ≤ firstTrial A k := by
  exact (firstTrial_strictMono A).id_le k

lemma stage_spec (A s : ℕ) :
    firstTrial A (stage A s) ≤ s ∧ s < firstTrial A (stage A s + 1) := by
  have h0 : firstTrial A (stage A s) ≤ s :=
    Nat.findGreatest_spec (P := fun k => firstTrial A k ≤ s) (Nat.zero_le s) (by simp [firstTrial])
  refine ⟨h0, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hle : stage A s + 1 ≤ s := le_trans (le_firstTrial A _) h
  exact Nat.findGreatest_is_greatest (P := fun k => firstTrial A k ≤ s)
    (Nat.lt_succ_self _) hle h

lemma stage_eq (A s k : ℕ) (h1 : firstTrial A k ≤ s) (h2 : s < firstTrial A (k + 1)) :
    stage A s = k := by
  obtain ⟨a1, a2⟩ := stage_spec A s
  have hm := (firstTrial_strictMono A).monotone
  rcases lt_trichotomy (stage A s) k with h | h | h
  · have := hm (show stage A s + 1 ≤ k from h); omega
  · exact h
  · have := hm (show k + 1 ≤ stage A s from h); omega

lemma stage_mono (A : ℕ) : Monotone (stage A) := by
  intro s t hst
  by_contra h
  rw [not_le] at h
  obtain ⟨a1, _⟩ := stage_spec A s
  obtain ⟨_, b2⟩ := stage_spec A t
  have := (firstTrial_strictMono A).monotone (show stage A t + 1 ≤ stage A s from h)
  omega

lemma trialLen_le (A s : ℕ) : 8 * trialLen s ≤ blockLen A (stage A s) := by
  unfold trialLen blockLen
  have h1 : s + 1 ≤ firstTrial A (stage A s + 1) := Nat.succ_le_of_lt (stage_spec A s).2
  have h2 : 21 ^ (s + 1) ≤ 21 ^ firstTrial A (stage A s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h2
  omega

lemma shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show shift A k ≤ shift A k + blockLen A k * spacing A k + depth A k
  omega

lemma trialStart_mono (A : ℕ) : Monotone (trialStart A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show trialStart A k ≤ trialStart A k + (blockLen A (stage A k) + 2) * spacing A (stage A k)
  omega

lemma blk_floor (A k : ℕ) (x : (AddCircle (1 : ℝ))) : -(floorC A k) ≤ blk A k x := by
  have := block_lower_floor (lam A k) 100 (blockLen A k) (depth A k) (spacing A k) (shift A k)
    (lam_pos A k) (by norm_num) (one_le_blockLen A k) (depth_spec A k).1 x
  unfold blk floorC
  exact this

lemma lt_two_pow_aux (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma firstTrial_le_pow (A k : ℕ) : firstTrial A k ≤ 2 ^ (A * k + k + 24) := by
  induction k with
  | zero => simp [firstTrial]
  | succ k ih =>
    show firstTrial A k + nTrials A k ≤ _
    unfold nTrials aExp
    have h1 : 2 ^ (A * k + k + 24) ≤ 2 ^ (A * (k + 1) + k + 24) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ (A * (k + 1) + (k + 1) + 24) = 2 * 2 ^ (A * (k + 1) + k + 24) := by ring
    omega

lemma aExp_le_firstTrial (A k : ℕ) : aExp A k ≤ firstTrial A (k + 1) := by
  show aExp A k ≤ firstTrial A k + nTrials A k
  unfold nTrials
  have h1 := lt_two_pow_aux (aExp A k)
  have h2 : 2 ^ aExp A k ≤ 2 ^ (aExp A k + k + 24) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma depth_le (A k : ℕ) : depth A k ≤ 6 * firstTrial A (k + 1) + 23 := by
  obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
  have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
  have ha := aExp_le_firstTrial A k
  rw [hS] at ha ⊢
  apply Nat.clog_le_of_le_pow
  rw [hL]
  have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
  have h2a : 2 ^ aExp A k ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) ha
  have e : 2 ^ (6 * S + 23) = 2 ^ 23 * (2 ^ (5 * S) * 2 ^ S) := by ring
  rw [e]
  have h3 : 21 ^ S * 2 ^ aExp A k ≤ 2 ^ (5 * S) * 2 ^ S := Nat.mul_le_mul h21 h2a
  have e2 : 640000 * (8 * 21 ^ S) * 2 ^ aExp A k = 5120000 * (21 ^ S * 2 ^ aExp A k) := by ring
  rw [e2]
  exact Nat.mul_le_mul (by norm_num) h3

lemma shift_le (A k : ℕ) : shift A k ≤ 2 ^ (6 * firstTrial A k + 10) := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
    show shift A k + blockLen A k * spacing A k + depth A k ≤ 2 ^ (6 * firstTrial A (k + 1) + 10)
    have hmono : firstTrial A k + 1 ≤ firstTrial A (k + 1) :=
      Nat.succ_le_of_lt (firstTrial_strictMono A (Nat.lt_succ_self k))
    have hd := depth_le A k
    obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
    have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
    rw [hS] at hd hmono ⊢
    have hL' : blockLen A k ≤ 2 ^ (5 * S + 3) := by
      rw [hL]
      have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
      have : 2 ^ (5 * S + 3) = 8 * 2 ^ (5 * S) := by ring
      omega
    have hsp : spacing A k = depth A k + 2 := rfl
    have hlin : 12 * S + 48 ≤ 2 ^ (S + 6) := by
      have := lt_two_pow_aux S
      have : 2 ^ (S + 6) = 64 * 2 ^ S := by ring
      omega
    have hb1 := one_le_blockLen A k
    have h1 : blockLen A k * spacing A k + depth A k ≤ blockLen A k * (2 * depth A k + 2) := by
      rw [hsp]; nlinarith
    have h2 : blockLen A k * (2 * depth A k + 2) ≤ 2 ^ (5 * S + 3) * 2 ^ (S + 6) :=
      Nat.mul_le_mul hL' (by omega)
    have h3 : 2 ^ (6 * firstTrial A k + 10) ≤ 2 ^ (6 * S + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (6 * S + 10) = 64 * 2 ^ (6 * S + 4) := by ring
    have e2 : 2 ^ (5 * S + 3) * 2 ^ (S + 6) = 32 * 2 ^ (6 * S + 4) := by ring
    omega

lemma twoLogQ_le (A k : ℕ) : 2 * logQ A k ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) := by
  have h1 := shift_le A (k + 1)
  have h2 := firstTrial_le_pow A (k + 1)
  have hq : logQ A k = shift A (k + 1) + 2 := rfl
  have hM : A * (k + 1) + (k + 1) + 24 = (A + 1) * (k + 1) + 24 := by ring
  rw [hM] at h2
  have hpM : 2 ^ ((A + 1) * (k + 1) + 30) = 64 * 2 ^ ((A + 1) * (k + 1) + 24) := by ring
  have hpos : 0 < 2 ^ ((A + 1) * (k + 1) + 24) := by positivity
  have h3 : 6 * firstTrial A (k + 1) + 12 ≤ 2 ^ ((A + 1) * (k + 1) + 30) := by omega
  have h4 : 2 ^ (6 * firstTrial A (k + 1) + 12) ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) :=
    Nat.pow_le_pow_right (by norm_num) h3
  have h5 : 2 ^ (6 * firstTrial A (k + 1) + 12) = 4 * 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    ring
  have h6 : 4 ≤ 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma scale_bound (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * logQ A k)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30 := by
  have hn := twoLogQ_le A k
  have hq2 : 2 ≤ logQ A k := by show 2 ≤ shift A (k + 1) + 2; omega
  obtain ⟨T, hT⟩ : ∃ T, (A + 1) * (k + 1) + 30 = T := ⟨_, rfl⟩
  rw [hT] at hn
  obtain ⟨E, hE0⟩ : ∃ E, 2 * logQ A k = E := ⟨_, rfl⟩
  rw [hE0] at hn
  have hE4 : 4 ≤ E := by omega
  rw [hE0]
  have hlt := Real.log_two_lt_d9
  have hgt := Real.log_two_gt_d9
  have hx1 : Real.log ((2 : ℝ) ^ E) = (E : ℝ) * Real.log 2 := Real.log_pow _ _
  have hE : (E : ℝ) ≤ (2 : ℝ) ^ (2 ^ T) := by
    have := (Nat.cast_le (α := ℝ)).2 hn
    rw [Nat.cast_pow, Nat.cast_ofNat] at this
    exact this
  have hEge : (4 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE4
  have hx1pos : 1 < Real.log ((2 : ℝ) ^ E) := by
    rw [hx1]
    have := mul_le_mul_of_nonneg_right hEge (by linarith : (0 : ℝ) ≤ Real.log 2)
    linarith
  have hx1le : Real.log ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ (2 ^ T) := by
    rw [hx1]
    have : (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hx2pos : 0 < Real.log (Real.log ((2 : ℝ) ^ E)) := Real.log_pos hx1pos
  have hx2le : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ (2 : ℝ) ^ T := by
    have h1 : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ Real.log ((2 : ℝ) ^ (2 ^ T)) :=
      Real.log_le_log (by linarith) hx1le
    have h2 : Real.log ((2 : ℝ) ^ (2 ^ T)) = ((2 ^ T : ℕ) : ℝ) * Real.log 2 := Real.log_pow _ _
    have h3 : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ T := by push_cast; rfl
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ T := by positivity
    have h5 : (2 : ℝ) ^ T * Real.log 2 ≤ (2 : ℝ) ^ T * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    rw [h2, h3] at h1
    linarith
  have h1 : Real.log (Real.log (Real.log ((2 : ℝ) ^ E))) ≤ Real.log ((2 : ℝ) ^ T) :=
    Real.log_le_log hx2pos hx2le
  have h2 : Real.log ((2 : ℝ) ^ T) = (T : ℝ) * Real.log 2 := Real.log_pow _ _
  have h3 : (T : ℝ) = ((A : ℝ) + 1) * (k + 1) + 30 := by rw [← hT]; push_cast; ring
  have h4 : (T : ℝ) * Real.log 2 ≤ (T : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [h2] at h1
  linarith

end Asm
end OMA996
end

-- Atoms
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA996
namespace Asm

lemma alt_shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  show shift A n ≤ shift A n + blockLen A n * spacing A n + depth A n
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

lemma alt_band_sep (A k k' q q' : ℕ) (hk : k < k') (hq : q ≤ blockLen A k) :
    shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' := by
  have h1 : shift A (k + 1) ≤ shift A k' := alt_shift_mono A (by omega)
  have h2 : shift A (k + 1) = shift A k + blockLen A k * spacing A k + depth A k := rfl
  have h3 : q * spacing A k ≤ blockLen A k * spacing A k := Nat.mul_le_mul_right _ hq
  generalize q * spacing A k = a at *
  generalize blockLen A k * spacing A k = b at *
  generalize q' * spacing A k' = c at *
  omega

lemma alt_band_sep_same (A k q q' : ℕ) (hq : q < q') :
    shift A k + q * spacing A k + depth A k ≤ shift A k + q' * spacing A k := by
  have h1 : (q + 1) * spacing A k ≤ q' * spacing A k := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * spacing A k = q * spacing A k + (depth A k + 2) := by
    rw [add_mul, one_mul]; rfl
  generalize q * spacing A k = a at *
  generalize q' * spacing A k = c at *
  omega

lemma alt_integrable_spike (d : ℕ) : Integrable (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) (haarAddCircle (T := 1)) := by
  have h : Integrable (spike d) (haarAddCircle (T := 1)) := by
    unfold spike
    exact (((integrable_const (1 : ℝ)).indicator (OMA996.measurableSet_spikeSet d)).sub
      (integrable_const _)).div_const _
  exact h.ofReal

lemma alt_integrable_atom (A k q : ℕ) : Integrable (fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) (haarAddCircle (T := 1)) := by
  have hn : ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) ≠ 0 := by positivity
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x)
      (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) hn
  have e : (fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) = (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) ∘
      (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x) := by
    funext x
    simp only [Function.comp, atom, natCast_zsmul]
  rw [e]
  exact Integrable.comp_measurable (by rw [hmp.map_eq]; exact alt_integrable_spike _)
    hmp.measurable

lemma alt_fourierCoeff_spike_zero (d : ℕ) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) 0 = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : (AddCircle (1 : ℝ)) => (spike 0 x : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-(0 : ℤ)) (x : (AddCircle (1 : ℝ))) • (spike d (x : (AddCircle (1 : ℝ))) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    rw [neg_zero, fourier_zero, one_smul]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), (1 : ℂ) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hI1, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, sub_sub_cancel, one_div, one_smul, inv_one]
  rw [Complex.real_smul]
  push_cast
  ring

lemma blk_eq_sum_atom (A k : ℕ) (x : (AddCircle (1 : ℝ))) :
    blk A k x = Real.sqrt (lam A k / blockLen A k) *
      ∑ q ∈ Finset.Icc 1 (blockLen A k), atom A k q x := by
  rfl

lemma fourierCoeff_blk (A k : ℕ) (r : ℤ) :
    fourierCoeff (fun x => (blk A k x : ℂ)) r =
      (Real.sqrt (lam A k / blockLen A k) : ℂ) *
        ∑ q ∈ Finset.Icc 1 (blockLen A k), fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  have hfun : (fun x => (blk A k x : ℂ)) = fun x => (Real.sqrt (lam A k / blockLen A k) : ℂ) *
      (∑ q ∈ Finset.Icc 1 (blockLen A k), fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) x := by
    funext x
    rw [blk_eq_sum_atom, Finset.sum_apply]
    push_cast
    rfl
  rw [hfun, fourierCoeff.const_mul,
    fourierCoeff.sum _ _ (fun q _ => alt_integrable_atom A k q), Finset.sum_apply]

lemma fourierCoeff_atom_zero (A k q : ℕ) : fourierCoeff (fun x => (atom A k q x : ℂ)) 0 = 0 := by
  have hmeas : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) (haarAddCircle (T := 1)) :=
    (Complex.measurable_ofReal.comp (OMA996.measurable_spike _)).aestronglyMeasurable
  have h := fourierCoeff_nsmul_comp_mul (2 ^ (shift A k + q * spacing A k)) (by positivity)
    (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) hmeas 0
  rw [mul_zero] at h
  exact h.trans (alt_fourierCoeff_spike_zero _)

lemma fourierCoeff_atom_disjoint (A k q k' q' : ℕ) (r : ℤ)
    (hq : q ∈ Finset.Icc 1 (blockLen A k)) (hq' : q' ∈ Finset.Icc 1 (blockLen A k'))
    (hne : (k, q) ≠ (k', q')) :
    fourierCoeff (fun x => (atom A k q x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (atom A k' q' x : ℂ)) r = 0 := by
  by_cases hr : r = 0
  · subst hr; left; exact fourierCoeff_atom_zero A k q
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have e1 : (2 : ℤ) ^ (shift A k + q * spacing A k) ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k + q * spacing A k + depth A k) ∣ r := by
    by_contra h
    exact h1 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  have e2 : (2 : ℤ) ^ (shift A k' + q' * spacing A k') ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k' + q' * spacing A k' + depth A k') ∣ r := by
    by_contra h
    exact h2 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  rw [Finset.mem_Icc] at hq hq'
  have sep : shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' ∨
      shift A k' + q' * spacing A k' + depth A k' ≤ shift A k + q * spacing A k := by
    rcases lt_trichotomy k k' with hk | rfl | hk
    · exact Or.inl (alt_band_sep A k k' q q' hk hq.2)
    · have hqq : q ≠ q' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hqq with h | h
      · exact Or.inl (alt_band_sep_same A k q q' h)
      · exact Or.inr (alt_band_sep_same A k q' q h)
    · exact Or.inr (alt_band_sep A k' k q' q hk hq'.2)
  rcases sep with h | h
  · exact e1.2 (dvd_trans (pow_dvd_pow 2 h) e2.1)
  · exact e2.2 (dvd_trans (pow_dvd_pow 2 h) e1.1)

end Asm
end OMA996
end

-- Atoms
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma blk_eq_sum_atom (k : ℕ) (x : (AddCircle (1 : ℝ))) :
    blk k x = Real.sqrt (lam k / blockLen k) * ∑ q ∈ Finset.Icc 1 (blockLen k), atom k q x := by
  rfl

lemma shift_mono' : Monotone shift := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  show shift n ≤ shift n + blockLen n * spacing n + depth n
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

lemma band_sep (k k' q q' : ℕ) (hk : k < k') (hq : q ≤ blockLen k) :
    shift k + q * spacing k + depth k ≤ shift k' + q' * spacing k' := by
  have h1 : shift (k + 1) ≤ shift k' := shift_mono' (by omega)
  have h2 : shift (k + 1) = shift k + blockLen k * spacing k + depth k := rfl
  have h3 : q * spacing k ≤ blockLen k * spacing k := Nat.mul_le_mul_right _ hq
  generalize q * spacing k = a at *
  generalize blockLen k * spacing k = b at *
  generalize q' * spacing k' = c at *
  omega

lemma band_sep_same (k q q' : ℕ) (hq : q < q') :
    shift k + q * spacing k + depth k ≤ shift k + q' * spacing k := by
  have h1 : (q + 1) * spacing k ≤ q' * spacing k := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * spacing k = q * spacing k + (depth k + 2) := by
    rw [add_mul, one_mul]; rfl
  generalize q * spacing k = a at *
  generalize q' * spacing k = c at *
  omega

lemma integrable_atom (k q : ℕ) : Integrable (fun x : (AddCircle (1 : ℝ)) => (atom k q x : ℂ)) (haarAddCircle (T := 1)) := by
  have hn : ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) ≠ 0 := by positivity
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) • x)
      (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) hn
  have e : (fun x : (AddCircle (1 : ℝ)) => (atom k q x : ℂ)) =
      (fun y : (AddCircle (1 : ℝ)) => (OMA996.spike (depth k) y : ℂ)) ∘
      (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) • x) := by
    funext x
    simp only [Function.comp, atom, natCast_zsmul]
  rw [e]
  exact Integrable.comp_measurable
    (by rw [hmp.map_eq]; exact OMA996.Asm.alt_integrable_spike _) hmp.measurable

lemma fourierCoeff_atom_zero (k q : ℕ) : fourierCoeff (fun x => (atom k q x : ℂ)) 0 = 0 := by
  have hmeas : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => (OMA996.spike (depth k) y : ℂ)) (haarAddCircle (T := 1)) :=
    (Complex.measurable_ofReal.comp (OMA996.measurable_spike _)).aestronglyMeasurable
  have h := OMA996.fourierCoeff_nsmul_comp_mul (2 ^ (shift k + q * spacing k)) (by positivity)
    (fun y : (AddCircle (1 : ℝ)) => (OMA996.spike (depth k) y : ℂ)) hmeas 0
  rw [mul_zero] at h
  exact h.trans (OMA996.Asm.alt_fourierCoeff_spike_zero _)

lemma fourierCoeff_blk (k : ℕ) (r : ℤ) :
    fourierCoeff (fun x => (blk k x : ℂ)) r =
      (Real.sqrt (lam k / blockLen k) : ℂ) *
        ∑ q ∈ Finset.Icc 1 (blockLen k), fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  have hfun : (fun x => (blk k x : ℂ)) = fun x => (Real.sqrt (lam k / blockLen k) : ℂ) *
      (∑ q ∈ Finset.Icc 1 (blockLen k), fun x : (AddCircle (1 : ℝ)) => (atom k q x : ℂ)) x := by
    funext x
    rw [blk_eq_sum_atom, Finset.sum_apply]
    push_cast
    rfl
  rw [hfun, fourierCoeff.const_mul,
    fourierCoeff.sum _ _ (fun q _ => integrable_atom k q), Finset.sum_apply]

lemma fourierCoeff_atom_disjoint (k q k' q' : ℕ) (r : ℤ)
    (hq : q ∈ Finset.Icc 1 (blockLen k)) (hq' : q' ∈ Finset.Icc 1 (blockLen k'))
    (hne : (k, q) ≠ (k', q')) :
    fourierCoeff (fun x => (atom k q x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (atom k' q' x : ℂ)) r = 0 := by
  by_cases hr : r = 0
  · subst hr; left; exact fourierCoeff_atom_zero k q
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have e1 : (2 : ℤ) ^ (shift k + q * spacing k) ∣ r ∧
      ¬ (2 : ℤ) ^ (shift k + q * spacing k + depth k) ∣ r := by
    by_contra h
    exact h1 (OMA996.fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  have e2 : (2 : ℤ) ^ (shift k' + q' * spacing k') ∣ r ∧
      ¬ (2 : ℤ) ^ (shift k' + q' * spacing k' + depth k') ∣ r := by
    by_contra h
    exact h2 (OMA996.fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  rw [Finset.mem_Icc] at hq hq'
  have sep : shift k + q * spacing k + depth k ≤ shift k' + q' * spacing k' ∨
      shift k' + q' * spacing k' + depth k' ≤ shift k + q * spacing k := by
    rcases lt_trichotomy k k' with hk | rfl | hk
    · exact Or.inl (band_sep k k' q q' hk hq.2)
    · have hqq : q ≠ q' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hqq with h | h
      · exact Or.inl (band_sep_same k q q' h)
      · exact Or.inr (band_sep_same k q' q h)
    · exact Or.inr (band_sep k' k q' q hk hq'.2)
  rcases sep with h | h
  · exact e1.2 (dvd_trans (pow_dvd_pow 2 h) e2.1)
  · exact e2.2 (dvd_trans (pow_dvd_pow 2 h) e1.1)

end Con
end OMA995
end

-- GlobalL2
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

private lemma measurable_atom' (k q : ℕ) : Measurable (atom k q) :=
  (OMA996.Asm.measurable_spike _).comp (continuous_nsmul _).measurable

lemma measurable_blk (k : ℕ) : Measurable (blk k) := by
  have e : blk k = fun x => Real.sqrt (lam k / blockLen k) *
      ∑ q ∈ Finset.Icc 1 (blockLen k), atom k q x := funext (blk_eq_sum_atom k)
  rw [e]
  exact (Finset.measurable_sum _ fun q _ => measurable_atom' k q).const_mul _

lemma integrable_blk (k : ℕ) : Integrable (blk k) (haarAddCircle (T := 1)) := by
  refine Integrable.of_bound (measurable_blk k).aestronglyMeasurable
    (Real.sqrt (lam k / blockLen k) * ∑ q ∈ Finset.Icc 1 (blockLen k), (2 : ℝ) ^ depth k)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, blk_eq_sum_atom, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun q _ => OMA996.Asm.abs_spike_le _ _)

private lemma fourierCoeff_blk_zero (k : ℕ) : fourierCoeff (fun x => (blk k x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero k q), mul_zero]

private lemma integral_blk (k : ℕ) : ∫ x, blk k x ∂(haarAddCircle (T := 1)) = 0 := by
  have h := fourierCoeff_blk_zero k
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma measurable_gPos : Measurable gPos := by
  unfold gPos
  exact Measurable.ennreal_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal

private lemma measurable_gFun : Measurable gFun := by
  unfold gFun
  exact measurable_gPos.ennreal_toReal.sub_const _

private lemma lintegral_gPos :
    ∫⁻ x, gPos x ∂(haarAddCircle (T := 1)) = ∑' k, ENNReal.ofReal (floorC k) := by
  unfold gPos
  rw [lintegral_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal.aemeasurable]
  congr 1
  ext k
  have hi : Integrable (fun x => blk k x + floorC k) (haarAddCircle (T := 1)) :=
    (integrable_blk k).add (integrable_const _)
  have hnn : (0 : (AddCircle (1 : ℝ)) → ℝ) ≤ᵐ[(haarAddCircle (T := 1))] fun x => blk k x + floorC k :=
    ae_of_all _ fun x => by
      have := blk_floor k x
      simp only [Pi.zero_apply]
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add (integrable_blk k) (integrable_const _), integral_blk, integral_const]
  simp

lemma lintegral_gPos_ne_top : ∫⁻ x, gPos x ∂(haarAddCircle (T := 1)) ≠ ∞ := by
  rw [lintegral_gPos, ← ENNReal.ofReal_tsum_of_nonneg floorC_nonneg summable_floorC]
  exact ENNReal.ofReal_ne_top

lemma ae_gPos_ne_top : ∀ᵐ x ∂(haarAddCircle (T := 1)), gPos x ≠ ∞ :=
  (ae_lt_top' measurable_gPos.aemeasurable lintegral_gPos_ne_top).mono fun _ hx => hx.ne

lemma gPos_toReal_eq (x : (AddCircle (1 : ℝ))) (hx : gPos x ≠ ∞) :
    Summable (fun k => blk k x + floorC k) ∧ (gPos x).toReal = ∑' k, (blk k x + floorC k) := by
  have hnn : ∀ k, 0 ≤ blk k x + floorC k := fun k => by linarith [blk_floor k x]
  have e : ∀ k, (ENNReal.ofReal (blk k x + floorC k)).toReal = blk k x + floorC k :=
    fun k => ENNReal.toReal_ofReal (hnn k)
  constructor
  · have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (blk k x + floorC k)) hx
    simp only [e] at this
    exact this
  · unfold gPos
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    simp only [e]

private lemma hasSum_blk (x : (AddCircle (1 : ℝ))) (hx : gPos x ≠ ∞) :
    HasSum (fun k => blk k x) (gFun x) := by
  obtain ⟨hs, htr⟩ := gPos_toReal_eq x hx
  have h := hs.hasSum.sub summable_floorC.hasSum
  simp only [add_sub_cancel_right] at h
  unfold gFun
  rw [htr]
  exact h

lemma tendsto_partialSum_gFun (x : (AddCircle (1 : ℝ))) (hx : gPos x ≠ ∞) :
    Tendsto (fun K => ∑ k ∈ range K, blk k x) atTop (𝓝 (gFun x)) :=
  (hasSum_blk x hx).tendsto_sum_nat

private lemma memLp_atomC (k q : ℕ) : MemLp (fun x => (atom k q x : ℂ)) 2 (haarAddCircle (T := 1)) :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' k q)).aestronglyMeasurable)
    (2 ^ depth k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact OMA996.Asm.abs_spike_le _ _)

private noncomputable def aLp (k q : ℕ) : Lp ℂ 2 (haarAddCircle (T := 1)) := (memLp_atomC k q).toLp _

private lemma coeFn_aLp (k q : ℕ) : ⇑(aLp k q) =ᵐ[(haarAddCircle (T := 1))] fun x => (atom k q x : ℂ) :=
  (memLp_atomC k q).coeFn_toLp

private lemma fourierCoeff_aLp (k q : ℕ) (r : ℤ) :
    fourierCoeff (⇑(aLp k q)) r = fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  unfold fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [coeFn_aLp k q] with x hx
  rw [hx]

private lemma inner_fourierBasis_aLp (k q : ℕ) (r : ℤ) :
    inner ℂ (fourierBasis r) (aLp k q) = fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  rw [← fourierBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_aLp]

private lemma inner_aLp_eq_zero (k q k' q' : ℕ)
    (hq : q ∈ Finset.Icc 1 (blockLen k)) (hq' : q' ∈ Finset.Icc 1 (blockLen k'))
    (hne : (k, q) ≠ (k', q')) : inner ℂ (aLp k q) (aLp k' q') = 0 := by
  rw [← fourierBasis.tsum_inner_mul_inner]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  rw [← inner_conj_symm, inner_fourierBasis_aLp, inner_fourierBasis_aLp]
  rcases fourierCoeff_atom_disjoint k q k' q' r hq hq' hne with h | h <;> simp [h]

private lemma inner_aLp_self (k q : ℕ) : inner ℂ (aLp k q) (aLp k q) = 1 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ x ∂(haarAddCircle (T := 1)), inner ℂ ((aLp k q) x) ((aLp k q) x) =
      ((OMA996.spike (depth k) ((2 ^ (shift k + q * spacing k) : ℕ) • x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [coeFn_aLp k q] with x hx
    rw [hx, RCLike.inner_apply', atom, Complex.conj_ofReal]
    push_cast; ring
  rw [integral_congr_ae h, integral_complex_ofReal,
    OMA996.Asm.integral_spike_nsmul_sq _ _ (one_le_depth k) (pow_ne_zero _ two_ne_zero)]
  simp

private lemma coeFn_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (haarAddCircle (T := 1))) :
    ⇑(∑ i ∈ s, f i) =ᵐ[(haarAddCircle (T := 1))] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 (haarAddCircle (T := 1))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

lemma eLpNorm_partialSum_le (K : ℕ) :
    eLpNorm (fun x => ∑ k ∈ range K, blk k x) 2 (haarAddCircle (T := 1)) ≤ 1 := by
  set c : ℕ → ℝ := fun k => Real.sqrt (lam k / blockLen k) with hc
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Lp ℂ 2 (haarAddCircle (T := 1)),
      Gc = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q := ⟨_, rfl⟩
  have hae : ⇑Gc =ᵐ[(haarAddCircle (T := 1))] fun x => (((∑ k ∈ range K, blk k x : ℝ)) : ℂ) := by
    have h1 := coeFn_finset_sum' (range K)
      (fun k => ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)
    have h2 : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ k : ℕ,
        (⇑(∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)) x =
          ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) * (atom k q x : ℂ) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [coeFn_finset_sum' (Icc 1 (blockLen k))
          (fun q => ((c k : ℝ) : ℂ) • aLp k q),
        ae_all_iff.2 fun q => Lp.coeFn_smul ((c k : ℝ) : ℂ) (aLp k q),
        ae_all_iff.2 fun q => coeFn_aLp k q] with x hx hs ha
      rw [hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs q, Pi.smul_apply, smul_eq_mul, ha q]
    filter_upwards [h1, h2] with x hx h2x
    rw [hGc, hx]
    simp only [h2x]
    simp only [blk_eq_sum_atom, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, hc]
  have key : ∀ k ∈ range K, ∀ q ∈ Icc 1 (blockLen k),
      inner ℂ (aLp k q) Gc = ((c k : ℝ) : ℂ) := by
    intro k hk q hq
    rw [hGc, inner_sum, Finset.sum_eq_single k]
    · rw [inner_sum, Finset.sum_eq_single q]
      · rw [inner_smul_right, inner_aLp_self, mul_one]
      · intro q' hq' hne
        rw [inner_smul_right, inner_aLp_eq_zero k q k q' hq hq'
          (fun h => hne (Prod.ext_iff.1 h).2.symm), mul_zero]
      · intro h; exact absurd hq h
    · intro k' _ hne
      rw [inner_sum]
      refine Finset.sum_eq_zero fun q' hq' => ?_
      rw [inner_smul_right, inner_aLp_eq_zero k q k' q' hq hq'
        (fun h => hne (Prod.ext_iff.1 h).1.symm), mul_zero]
    · intro h; exact absurd hk h
  have hinner : inner ℂ Gc Gc = (((∑ k ∈ range K, lam k : ℝ)) : ℂ) := by
    calc inner ℂ Gc Gc
        = inner ℂ (∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)
            Gc := by rw [← hGc]
      _ = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k),
            (starRingEnd ℂ) ((c k : ℝ) : ℂ) * inner ℂ (aLp k q) Gc := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_inner]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [inner_smul_left]
      _ = (((∑ k ∈ range K, lam k : ℝ)) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_congr rfl fun q hq => by rw [key k hk q hq]]
          have hL : (blockLen k : ℝ) ≠ 0 := by
            have := one_le_blockLen k
            exact_mod_cast (show blockLen k ≠ 0 by omega)
          have h0 : 0 ≤ lam k / blockLen k :=
            div_nonneg (lam_pos k).le (Nat.cast_nonneg _)
          rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
            Complex.conj_ofReal, ← Complex.ofReal_mul, hc, Real.mul_self_sqrt h0,
            ← Complex.ofReal_natCast, ← Complex.ofReal_mul, mul_div_cancel₀ _ hL]
  have hnorm_sq : ‖Gc‖ ^ 2 = ∑ k ∈ range K, lam k := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Gc
    rw [hinner] at this
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact this.symm)
  have hsum : ∑ k ∈ range K, lam k ≤ 1 :=
    (summable_lam.sum_le_tsum (range K) (fun k _ => (lam_pos k).le)).trans tsum_lam_le_one
  have hnorm : ‖Gc‖ ≤ 1 := by nlinarith [norm_nonneg Gc]
  have hmeas : AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk k x) (haarAddCircle (T := 1)) :=
    (Finset.measurable_sum _ fun k _ => measurable_blk k).aestronglyMeasurable
  have e1 : eLpNorm (fun x => ∑ k ∈ range K, blk k x) 2 (haarAddCircle (T := 1)) ≤
      eLpNorm (fun x => (((∑ k ∈ range K, blk k x : ℝ)) : ℂ)) 2 (haarAddCircle (T := 1)) :=
    eLpNorm_mono fun x => le_of_eq (Complex.norm_real _).symm
  refine e1.trans ?_
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hnorm

lemma memLp_gFun : MemLp (fun x => (gFun x : ℂ)) 2 (haarAddCircle (T := 1)) := by
  have hlim : ∀ᵐ x ∂(haarAddCircle (T := 1)), Tendsto (fun K => ∑ k ∈ range K, blk k x) atTop (𝓝 (gFun x)) :=
    ae_gPos_ne_top.mono fun x hx => tendsto_partialSum_gFun x hx
  have hmeas : ∀ K, AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk k x) (haarAddCircle (T := 1)) := fun K =>
    (Finset.measurable_sum _ fun k _ => measurable_blk k).aestronglyMeasurable
  refine MemLp.ofReal ⟨measurable_gFun.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ hlim) ?_
  refine lt_of_le_of_lt (liminf_le_of_frequently_le'
    (Frequently.of_forall fun K => eLpNorm_partialSum_le K)) ?_
  exact ENNReal.one_lt_top

end Con
end OMA995
end

-- MeanZero
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma meanZero_integral_blk (k : ℕ) : ∫ x, blk k x ∂(haarAddCircle (T := 1)) = 0 := by
  have h : fourierCoeff (fun x => (blk k x : ℂ)) 0 = 0 := by
    rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero k q), mul_zero]
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma meanZero_integral_partialSum (K : ℕ) : ∫ x, ∑ k ∈ range K, blk k x ∂(haarAddCircle (T := 1)) = 0 := by
  rw [integral_finsetSum _ (fun k _ => integrable_blk k)]
  exact Finset.sum_eq_zero fun k _ => meanZero_integral_blk k

lemma meanZero_integral_gFun_real : ∫ x, gFun x ∂(haarAddCircle (T := 1)) = 0 := by
  have hS : ∀ K, Measurable (fun x => ∑ k ∈ range K, blk k x) := fun K =>
    Finset.measurable_sum _ fun k _ => measurable_blk k
  have hG : Integrable (fun x => (gPos x).toReal + ∑' k, floorC k) (haarAddCircle (T := 1)) :=
    (integrable_toReal_of_lintegral_ne_top measurable_gPos.aemeasurable
      lintegral_gPos_ne_top).add (integrable_const _)
  have ht : Tendsto (fun K => ∫ x, ∑ k ∈ range K, blk k x ∂(haarAddCircle (T := 1))) atTop
      (𝓝 (∫ x, gFun x ∂(haarAddCircle (T := 1)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (gPos x).toReal + ∑' k, floorC k) (fun K => (hS K).aestronglyMeasurable)
      hG ?_ ?_
    · intro K
      filter_upwards [ae_gPos_ne_top] with x hx
      obtain ⟨hs, htr⟩ := gPos_toReal_eq x hx
      rw [Real.norm_eq_abs, htr]
      have h1 : |∑ k ∈ range K, blk k x| ≤
          ∑ k ∈ range K, (blk k x + floorC k) + ∑ k ∈ range K, floorC k := by
        rw [← Finset.sum_add_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        have h1 := blk_floor k x
        have h2 := floorC_nonneg k
        rw [abs_le]
        constructor <;> linarith
      have h2 : ∑ k ∈ range K, (blk k x + floorC k) ≤ ∑' k, (blk k x + floorC k) :=
        hs.sum_le_tsum _ fun k _ => by linarith [blk_floor k x]
      have h3 : ∑ k ∈ range K, floorC k ≤ ∑' k, floorC k :=
        summable_floorC.sum_le_tsum _ fun k _ => floorC_nonneg k
      linarith
    · filter_upwards [ae_gPos_ne_top] with x hx
      exact tendsto_partialSum_gFun x hx
  simp only [meanZero_integral_partialSum] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma integral_gFun : ∫ x, (gFun x : ℂ) ∂(haarAddCircle (T := 1)) = 0 := by
  rw [integral_complex_ofReal, meanZero_integral_gFun_real, Complex.ofReal_zero]

end Con
end OMA995
end

-- TrialSignal
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA996

lemma spike_ge_neg (d : ℕ) (y : (AddCircle (1 : ℝ))) :
    -((2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ≤ spike d y := by
  unfold spike
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : (AddCircle (1 : ℝ)) → ℝ) y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
  linarith

lemma spike_eq_of_mem (d : ℕ) (y : (AddCircle (1 : ℝ)))
    (hy : y ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    spike d y = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
  unfold spike
  rw [Set.indicator_of_mem hy]
  simp

lemma trial_signal (lam B : ℝ) (L ℓ d D U M : ℕ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hB : 100 ≤ B) (hL : 1 ≤ L) (hℓ : 8 * ℓ ≤ L) (hD : d + 2 ≤ D)
    (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (hd' : (2 : ℝ) ^ d < 128 * B ^ 2 * L / lam) (x : (AddCircle (1 : ℝ)))
    (hgood : ∃ h ∈ Finset.Icc (ℓ + 1) (L + 1),
      (2 ^ (U + M + h * D) : ℕ) • x ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    2 * B * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ, block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
  obtain ⟨h, hh, hx⟩ := hgood
  rw [Finset.mem_Icc] at hh
  have hppos : 0 < (2 : ℝ)⁻¹ ^ d := by positivity
  have hp2 : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hkey : 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ lam := by
    have h0 := (div_le_iff₀ hlam).1 hd
    have h1 := mul_le_mul_of_nonneg_right h0 hppos.le
    calc 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d := h1
      _ = lam := by linear_combination lam * hp2
  have hB2 : (10000 : ℝ) ≤ B ^ 2 := by nlinarith
  have hLp0 : 0 ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by positivity
  have hLp : (L : ℝ) * (2 : ℝ)⁻¹ ^ d ≤ 1 / 640000 := by
    nlinarith [mul_le_mul_of_nonneg_right hB2 hLp0]
  have hpL : (2 : ℝ)⁻¹ ^ d ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by nlinarith
  have hp1 : 0 < 1 - (2 : ℝ)⁻¹ ^ d := by linarith
  have hs : 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) :=
    Real.sqrt_pos.2 (mul_pos hppos hp1)
  have hs2 : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
      = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (mul_pos hppos hp1).le
  have ha : 0 ≤ Real.sqrt (lam / L) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (lam / L) ^ 2 * L = lam := by
    rw [Real.sq_sqrt (div_nonneg hlam.le hLpos.le)]; field_simp

  have hmain : 2 * B ≤ Real.sqrt (lam / L) *
      ((1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
    rw [← mul_div_assoc, le_div_iff₀ hs]
    by_contra hcon
    push_neg at hcon
    have h0 : 0 ≤ Real.sqrt (lam / L) * (1 - L * (2 : ℝ)⁻¹ ^ d) :=
      mul_nonneg ha (by linarith)
    have h1 := mul_self_lt_mul_self h0 hcon
    have h2 : Real.sqrt (lam / L) ^ 2 * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      rw [← hs2]; nlinarith [h1]
    have h3 : lam * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L := by
      rw [← ha2]; nlinarith [mul_lt_mul_of_pos_right h2 hLpos]
    have h4 : 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L
        ≤ 4 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d := by
      have : 0 ≤ B ^ 2 * L * (2 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ d := by positivity
      nlinarith
    have h5 : lam * (L * (2 : ℝ)⁻¹ ^ d) ≤ lam * (1 / 640000) :=
      mul_le_mul_of_nonneg_left hLp hlam.le
    have h6 : 0 ≤ lam * (L * (2 : ℝ)⁻¹ ^ d) ^ 2 := by positivity
    nlinarith
  have hterm : ∀ r ∈ Finset.Icc 1 ℓ,
      2 * B ≤ block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    obtain ⟨q, rfl⟩ : ∃ q, h = q + r := ⟨h - r, by omega⟩
    have hq0 : q ∈ Finset.Icc 1 L := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hbig : spike d ((2 ^ (U + q * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
        = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      apply spike_eq_of_mem
      rw [smul_smul, ← pow_add]
      have he : U + q * D + (M + r * D) = U + M + (q + r) * D := by ring
      rw [he]; exact hx
    have hnn : ∀ q' ∈ Finset.Icc 1 L,
        0 ≤ spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
          + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      intro q' _
      have := spike_ge_neg d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
      rw [neg_div] at this
      linarith
    have hsingle := Finset.single_le_sum hnn hq0
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hbig,
      Nat.add_sub_cancel] at hsingle
    have hsum : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
        ≤ ∑ q' ∈ Finset.Icc 1 L,
          spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x)) := by
      have hid : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
          = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            - (L : ℝ) * ((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
        field_simp; ring
      rw [hid]; linarith
    unfold block
    exact hmain.trans (mul_le_mul_of_nonneg_left hsum ha)
  calc 2 * B * (ℓ : ℝ) = ∑ r ∈ Finset.Icc 1 ℓ, 2 * B := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

end OMA996
end

-- Master
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma gFun_ge (x : (AddCircle (1 : ℝ))) : -(1 / 100 : ℝ) ≤ gFun x := by
  unfold gFun
  have h1 := tsum_floorC_le
  have h2 : 0 ≤ (gPos x).toReal := ENNReal.toReal_nonneg
  linarith

lemma blk_sub_le_gFun (x : (AddCircle (1 : ℝ))) (hx : gPos x ≠ ∞) (k : ℕ) :
    blk k x - 1 / 100 ≤ gFun x := by
  unfold gFun
  have h1 := tsum_floorC_le
  have h0 := floorC_nonneg k
  have hle : ENNReal.ofReal (blk k x + floorC k) ≤ gPos x := by
    unfold gPos
    exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (blk k x + floorC k)) k
  have h3 : (ENNReal.ofReal (blk k x + floorC k)).toReal ≤ (gPos x).toReal :=
    ENNReal.toReal_mono hx hle
  have h4 : blk k x + floorC k ≤ (ENNReal.ofReal (blk k x + floorC k)).toReal := by
    rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
  linarith

lemma ae_forall_nSeq {P : (AddCircle (1 : ℝ)) → Prop} (h : ∀ᵐ y ∂(haarAddCircle (T := 1)), P y) :
    ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ j, P (nSeq j • x) := by
  have hv : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (fun y : (AddCircle (1 : ℝ)) => nSeq j • y) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := by
    by_cases h1 : 1 < nSeq j
    · rw [← hv]; exact (ergodic_nsmul h1).toMeasurePreserving
    · have h2 : 1 ≤ nSeq j := one_le_nSeq j
      have h3 : nSeq j = 1 := by omega
      simp only [h3, one_smul]
      exact MeasurePreserving.id _
  exact hmp.quasiMeasurePreserving.ae h

lemma master_trial (x : (AddCircle (1 : ℝ))) (s : ℕ) (hfin : ∀ j, gPos (nSeq j • x) ≠ ∞) (hx : x ∈ goodSet s) :
    ∃ N : ℕ, s ≤ N ∧ N ≤ 21 ^ (s + 1) ∧
      sig (stage s) * N ≤ ∑ j ∈ range N, gFun (nSeq j • x) := by
  set k := stage s with hk
  set ℓ := trialLen s with hℓ
  set P := 21 ^ s - 1 with hP
  have ht : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hsl : s < 21 ^ s := Nat.lt_pow_self (by norm_num)
  have hℓv : ℓ = 20 * 21 ^ s := rfl
  have h21 : 21 ^ (s + 1) = 21 * 21 ^ s := by rw [pow_succ]; ring
  have hℓP : 19 * (P + 1) ≤ ℓ := by omega
  refine ⟨P + ℓ, by omega, by omega, ?_⟩
  have hB := sig_ge k

  have hsig : 2 * sig k * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ,
      OMA996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k)
        ((2 ^ (trialStart s + r * spacing k) : ℕ) • x) := by
    have hd := depth_spec k
    apply OMA996.trial_signal (lam k) (sig k) (blockLen k) ℓ (depth k) (spacing k) (shift k)
      (trialStart s) (lam_pos k) (lam_le_one k) (by linarith) (one_le_blockLen k)
      (trialLen_le s) (by simp [spacing]) hd.1 hd.2 x
    simp only [goodSet, Set.mem_iUnion] at hx
    obtain ⟨h, hh, hx⟩ := hx
    exact ⟨h, hh, by simpa [OMA996.Asm.hitSet, OMA996.Asm.spikeSet, add_assoc] using hx⟩

  have hre : ∑ r ∈ Finset.Icc 1 ℓ,
      OMA996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k)
        ((2 ^ (trialStart s + r * spacing k) : ℕ) • x)
      = ∑ j ∈ Finset.Ico P (P + ℓ), blk k (nSeq j • x) := by
    apply Finset.sum_nbij' (fun r => 21 ^ s + r - 2) (fun j => j + 2 - 21 ^ s)
    · intro r hr; simp only [Finset.mem_Icc, Finset.mem_Ico] at hr ⊢
      omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      unfold blk nSeq
      rw [mExp_trial s r hr.1 hr.2]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => gFun (nSeq j • x))
    (Nat.le_add_right P ℓ)
  have hA1 : -((P : ℝ) * (1 / 100)) ≤ ∑ j ∈ range P, gFun (nSeq j • x) := by
    have := Finset.card_nsmul_le_sum (range P) (fun j => gFun (nSeq j • x)) (-(1 / 100))
      (fun j _ => gFun_ge _)
    simp only [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hA2 : ∑ j ∈ Finset.Ico P (P + ℓ), (blk k (nSeq j • x) - 1 / 100)
      ≤ ∑ j ∈ Finset.Ico P (P + ℓ), gFun (nSeq j • x) :=
    Finset.sum_le_sum (fun j _ => blk_sub_le_gFun _ (hfin j) k)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul, ← hre] at hA2
  rw [← hsplit]
  have hℓP' : 19 * ((P : ℝ) + 1) ≤ ℓ := by exact_mod_cast hℓP
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  push_cast
  nlinarith

end Con
end OMA995
end

-- Growth
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995
namespace Con

lemma bExp_le_succ (k : ℕ) : bExp k ≤ bExp (k + 1) := by
  unfold bExp; have : (k + 1) ^ 2 ≤ (k + 1 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

lemma firstTrial_succ_le (k : ℕ) : firstTrial (k + 1) ≤ 2 ^ (2 * bExp k + 3 * k + 25) := by
  induction k with
  | zero =>
    rw [show firstTrial (0 + 1) = 0 + nTrials 0 from rfl, zero_add]
    unfold nTrials aExp
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  | succ k ih =>
    have e : firstTrial (k + 1 + 1) = firstTrial (k + 1) + nTrials (k + 1) := rfl
    rw [e]
    have hb := bExp_le_succ k
    have h1 : 2 ^ (2 * bExp k + 3 * k + 25) ≤ 2 ^ (2 * bExp (k + 1) + 3 * k + 27) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : nTrials (k + 1) ≤ 2 ^ (2 * bExp (k + 1) + 3 * k + 27) := by
      unfold nTrials aExp
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (2 * bExp (k + 1) + 3 * (k + 1) + 25) =
        2 * 2 ^ (2 * bExp (k + 1) + 3 * k + 27) := by
      rw [← pow_succ', show 2 * bExp (k + 1) + 3 * (k + 1) + 25 = 2 * bExp (k + 1) + 3 * k + 27 + 1 by ring]
    rw [h3]; omega

lemma log_le_aux (S B N : ℕ) (hS : S ≤ 2 ^ B) (hN : N ≤ 21 ^ S) :
    Real.log N ≤ 4 * (2 : ℝ) ^ B := by
  have hl21 : Real.log 21 ≤ 4 := by
    have h1 : Real.log 21 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1; linarith
  have hS' : (S : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast hS
  have hl0 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
  have hF0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ 2 ^ B := by positivity
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN' : (N : ℝ) ≤ (21 : ℝ) ^ S := by exact_mod_cast hN
  have h1 : Real.log N ≤ Real.log ((21 : ℝ) ^ S) := Real.log_le_log hNr hN'
  rw [Real.log_pow] at h1
  nlinarith

lemma log_le_of_le (k N : ℕ) (hN : N ≤ 21 ^ firstTrial (k + 1)) :
    Real.log N ≤ (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) := by
  have h := log_le_aux _ _ N (firstTrial_succ_le k) hN
  have e : (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) = 4 * (2 : ℝ) ^ (2 * bExp k + 3 * k + 25) := by
    rw [show 2 * bExp k + 3 * k + 27 = (2 * bExp k + 3 * k + 25) + 2 by ring, pow_add]; norm_num; ring
  rw [e]; exact h

lemma natCast_le_sig (k : ℕ) : (k : ℝ) ≤ sig k := by
  unfold sig
  have h1 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ bExp k :=
    pow_le_pow_right₀ (by norm_num) (by unfold bExp; nlinarith)
  linarith

lemma growth {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, N ≤ 21 ^ firstTrial (k + 1) →
      C * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) ≤ sig k * N := by
  set p : ℝ := 1 / 2 - ε with hp_def
  set K : ℝ := max 1 (Real.log 2 ^ p) with hK
  filter_upwards [eventually_ge_atTop ⌈1 / ε⌉₊, eventually_ge_atTop ⌈C⌉₊,
    eventually_ge_atTop ⌈C * K⌉₊] with k hk1 hk2 hk3
  intro N hN
  have hlogE : Real.log N ≤ (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) := log_le_of_le k N hN
  clear hN
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · rw [h0]; simp only [Nat.cast_zero, zero_mul, mul_zero, le_refl]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  suffices h : C * Real.log N ^ p ≤ sig k by
    have := mul_le_mul_of_nonneg_left h hNr.le
    calc C * ((N : ℝ) * Real.log N ^ p) = N * (C * Real.log N ^ p) := by ring
      _ ≤ N * sig k := this
      _ = sig k * N := by ring
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hNpos)
  have hx0 : 0 ≤ Real.log N ^ p := Real.rpow_nonneg hlog0 _
  have hks := natCast_le_sig k
  rcases le_or_gt C 0 with hC | hC
  · have := sig_pos k; nlinarith
  rcases le_or_gt p 0 with hp | hp
  · have hxK : Real.log N ^ p ≤ K := by
      rcases Nat.lt_or_ge N 2 with h2 | h2
      · have : N = 1 := by omega
        subst this; simp only [Nat.cast_one, Real.log_one]
        exact le_trans (Real.zero_rpow_le_one p) (le_max_left _ _)
      · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        exact le_trans (Real.rpow_le_rpow_of_nonpos hl2 this hp) (le_max_right _ _)
    have hk3' : C * K ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk3)
    calc C * Real.log N ^ p ≤ C * K := by gcongr
      _ ≤ k := hk3'
      _ ≤ sig k := hks
  · set E : ℕ := 2 * bExp k + 3 * k + 27 with hE
    have h1 : Real.log N ^ p ≤ ((2 : ℝ) ^ E) ^ p := Real.rpow_le_rpow hlog0 hlogE hp.le
    rw [← Real.rpow_natCast_mul (by norm_num)] at h1
    have hk1' : 1 / ε ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
    have hεk : 1 ≤ ε * k := by
      rw [div_le_iff₀ hε] at hk1'; linarith
    have hCk : C ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk2)
    have hk2pow : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self).le
    have hexp : (E : ℝ) * p + k ≤ (bExp k : ℝ) := by
      rw [hE, hp_def]; unfold bExp; push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hεk (by linarith : (0 : ℝ) ≤ k + 1),
        mul_nonneg hε.le hk0]
    have hsig : sig k = (2 : ℝ) ^ ((bExp k : ℕ) : ℝ) := by unfold sig; rw [Real.rpow_natCast]
    have h3 : (2 : ℝ) ^ ((E : ℝ) * p) * (2 : ℝ) ^ (k : ℝ) ≤ sig k := by
      rw [← Real.rpow_add (by norm_num), hsig]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hpos : 0 ≤ (2 : ℝ) ^ ((E : ℝ) * p) := Real.rpow_nonneg (by norm_num) _
    calc C * Real.log N ^ p ≤ C * (2 : ℝ) ^ ((E : ℝ) * p) := by gcongr
      _ ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ ((E : ℝ) * p) := by
          gcongr; linarith
      _ ≤ sig k := by linarith

end Con
end OMA995
end

-- Consequences
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995

lemma one_le_log_nat {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  have := Real.exp_one_lt_d9
  linarith

lemma sqrt_log_le {y : ℝ} (hy : 1 ≤ y) : Real.sqrt (Real.log y) ≤ 2 * y ^ ((1 : ℝ) / 4) := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : Real.log y ≤ y ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hy0 (by norm_num)
  have hq : 0 ≤ y ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hy0 _
  have hsq : (y ^ ((1 : ℝ) / 4)) ^ 2 = y ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hh : 0 ≤ y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0 _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

lemma criticalExponent_of (hU : ErdosUpperBound) (hL : HoLowerBound) : Erdos995CriticalExponent := by
  refine ⟨fun θ hθ f n hn => ?_, fun θ hθ hG => ?_⟩
  · have h := hU f n hn (θ - 1 / 2) (by linarith)
    have e : (1 : ℝ) / 2 + (θ - 1 / 2) = θ := by ring
    rw [e] at h
    filter_upwards [h] with x hx using hx.isBigO
  · obtain ⟨f, n, hn, -, -, hlow⟩ := hL
    have hup := hG f n hn.isLacunary
    obtain ⟨x, hx1, hx2⟩ := (hup.and hlow).exists
    obtain ⟨K, hK, hB⟩ := hx1.exists_pos
    have hb := hB.bound
    set ε : ℝ := (1 / 2 - θ) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hfr := hx2 ε hεpos (K + 1)
    obtain ⟨N, hN1, hN2, hN3⟩ :=
      (hfr.and_eventually (hb.and (eventually_ge_atTop 3))).exists
    have hlog := one_le_log_nat hN3
    have hNpos : (0 : ℝ) < N := by have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
                                   linarith
    have hr1 : 0 < Real.log N ^ ((1 : ℝ) / 2 - ε) := Real.rpow_pos_of_pos (by linarith) _
    have hr2 : 0 ≤ Real.log N ^ θ := Real.rpow_nonneg (by linarith) _
    have hmono : Real.log N ^ θ ≤ Real.log N ^ ((1 : ℝ) / 2 - ε) :=
      Real.rpow_le_rpow_of_exponent_le hlog (by rw [hε]; linarith)
    have hnorm : ‖(N : ℝ) * Real.log N ^ θ‖ = (N : ℝ) * Real.log N ^ θ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm] at hN2
    have hre : (lacSum f n x N).re ≤ ‖lacSum f n x N‖ := Complex.re_le_norm _
    have h4 : K * ((N : ℝ) * Real.log N ^ θ) ≤ K * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul_of_nonneg_left hmono hNpos.le
    have h5 : 0 < (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε) := mul_pos hNpos hr1
    nlinarith

lemma not_logLogQuestion_of (hL : HoLowerBound) : ¬ LogLogQuestion := by
  intro hQ
  obtain ⟨f, n, hn, -, -, hlow⟩ := hL
  have hup := hQ f n hn.isLacunary
  obtain ⟨x, hx1, hx2⟩ := (hup.and hlow).exists
  have hb := hx1.bound (show (0 : ℝ) < 1 by norm_num)
  have hfr := hx2 (1 / 4) (by norm_num) 3
  obtain ⟨N, hN1, hN2, hN3⟩ := (hfr.and_eventually (hb.and (eventually_ge_atTop 3))).exists
  have hlog := one_le_log_nat hN3
  have hNpos : (0 : ℝ) < N := by have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
                                 linarith
  have hsq := sqrt_log_le hlog
  have hnorm : ‖(N : ℝ) * Real.sqrt (Real.log (Real.log N))‖
      = (N : ℝ) * Real.sqrt (Real.log (Real.log N)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm] at hN2
  have hre : (lacSum f n x N).re ≤ ‖lacSum f n x N‖ := Complex.re_le_norm _
  have e : (1 : ℝ) / 2 - 1 / 4 = 1 / 4 := by norm_num
  rw [e] at hN1
  have hr1 : 0 < Real.log N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have h4 : (N : ℝ) * Real.sqrt (Real.log (Real.log N)) ≤ N * (2 * Real.log N ^ ((1 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hsq hNpos.le
  have h5 : 0 < (N : ℝ) * Real.log N ^ ((1 : ℝ) / 4) := mul_pos hNpos hr1
  nlinarith

end OMA995
end

-- Main
section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA995

theorem erdosUpperBound : ErdosUpperBound := by
  intro f n _ ε hε
  have h : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, Upper.sumNorm f n (2 ^ (j + 1)) x ≤
      (1 / ((m : ℝ) + 1)) * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε)) :=
    ae_all_iff.2 fun m => Upper.ae_eventually_sumNorm_le f n hε (by positivity)
  filter_upwards [h] with x hx
  exact Upper.isLittleO_of_dyadic (fun N => lacSum f n x N) (fun M => Upper.sumNorm f n M x)
    (fun N => Upper.norm_lacSum_le_sumNorm f n x (Nat.lt_pow_succ_log_self (by norm_num) N).le)
    hε hx

theorem hoLowerBound : HoLowerBound := by
  have hmem := Con.memLp_gFun
  set f : Lp ℂ 2 (haarAddCircle (T := 1)) := hmem.toLp _ with hfdef
  have hfg : (f : (AddCircle (1 : ℝ)) → ℂ) =ᵐ[(haarAddCircle (T := 1))] fun x => (Con.gFun x : ℂ) := hmem.coeFn_toLp
  refine ⟨f, Con.nSeq, Con.isDyadicLacunary_nSeq, ?_, ?_, ?_⟩
  · filter_upwards [hfg] with x hx
    rw [hx, Complex.ofReal_im]
  · rw [integral_congr_ae hfg]
    exact Con.integral_gFun
  · have hall : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ j, Con.gPos (Con.nSeq j • x) ≠ ∞ ∧
        f (Con.nSeq j • x) = (Con.gFun (Con.nSeq j • x) : ℂ) :=
      Con.ae_forall_nSeq (P := fun y => Con.gPos y ≠ ∞ ∧ f y = (Con.gFun y : ℂ))
        (by filter_upwards [Con.ae_gPos_ne_top, hfg] with y h1 h2 using ⟨h1, h2⟩)
    filter_upwards [hall, Con.ae_eventually_stageGood] with x hx hgood
    intro ε hε C
    rw [frequently_atTop]
    intro N0
    obtain ⟨k, ⟨hxk, hgr⟩, hkN0⟩ :=
      ((hgood.and (Con.growth hε C)).and (eventually_ge_atTop N0)).exists
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hxk
    rw [Finset.mem_Ico] at hs
    have hstage : Con.stage s = k := Con.stage_eq s k hs.1 hs.2
    obtain ⟨N, hsN, hN21, hsig⟩ := Con.master_trial x s (fun j => (hx j).1) hxs
    refine ⟨N, ?_, ?_⟩
    · have := Con.le_firstTrial k
      omega
    · have hre : (lacSum f Con.nSeq x N).re = ∑ j ∈ range N, Con.gFun (Con.nSeq j • x) := by
        unfold lacSum
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(hx j).2, Complex.ofReal_re]
      rw [hre]
      have hNle : N ≤ 21 ^ Con.firstTrial (k + 1) :=
        hN21.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hstage] at hsig
      exact (hgr N hNle).trans hsig

theorem erdos_995 : Erdos995Answer :=
  ⟨erdosUpperBound, hoLowerBound, criticalExponent_of erdosUpperBound hoLowerBound,
    not_logLogQuestion_of hoLowerBound⟩

theorem erdos_995_logLog : ¬ LogLogQuestion := erdos_995.2.2.2

end OMA995
end

section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA995Bridge

lemma haar_eq_volume : (haarAddCircle (T := 1) : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma restrict_Icc_eq :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)) := by
  rw [zero_add]
  exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

lemma mp : MeasurePreserving (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (haarAddCircle (T := 1)) := by
  rw [restrict_Icc_eq, haar_eq_volume]
  exact AddCircle.measurePreserving_mk 1 0

lemma ae_transfer {p : AddCircle (1 : ℝ) → Prop} (h : ∀ᵐ x ∂(haarAddCircle (T := 1)), p x) :
    ∀ᵐ α : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), p (α : AddCircle (1 : ℝ)) :=
  mp.quasiMeasurePreserving.ae h

noncomputable def gOf (f : Lp ℂ 2 (haarAddCircle (T := 1))) (t : ℝ) : ℝ :=
  (f (t : AddCircle (1 : ℝ))).re

lemma memLp_gOf (f : Lp ℂ 2 (haarAddCircle (T := 1))) :
    MemLp (gOf f) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h : MemLp (fun x => (f x).re) 2 (haarAddCircle (T := 1)) := (Lp.memLp f).re
  exact h.comp_measurePreserving mp

lemma integral_gOf (f : Lp ℂ 2 (haarAddCircle (T := 1)))
    (hf : ∫ x, f x ∂(haarAddCircle (T := 1)) = 0) : ∫ x in (0 : ℝ)..1, gOf f x = 0 := by
  have h1 := AddCircle.intervalIntegral_preimage 1 0 (fun x => (f x).re)
  rw [zero_add] at h1
  unfold gOf
  rw [h1, ← haar_eq_volume]
  have hi : Integrable (fun x => f x) (haarAddCircle (T := 1)) :=
    (Lp.memLp f).integrable (by norm_num)
  have h2 := integral_re hi
  simp only [RCLike.re_to_complex] at h2
  rw [h2, hf, Complex.zero_re]

lemma partialSum_gOf (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (α : ℝ) (N : ℕ) :
    Erdos995.partialSum n (gOf f) α N = (OMA995.lacSum f n (α : AddCircle (1 : ℝ)) N).re := by
  unfold Erdos995.partialSum OMA995.lacSum gOf
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [AddCircle.coe_fract, mul_comm, ← nsmul_eq_mul, AddCircle.coe_nsmul]

lemma isLacunary_of {n : ℕ → ℕ} (h : OMA995.IsDyadicLacunary n) : IsLacunary n := by
  obtain ⟨c, hc, h⟩ := h.isLacunary
  exact ⟨c, hc, h⟩

end OMA995Bridge
end

section
open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA995Bridge

lemma restrict_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  norm_num

end OMA995Bridge
end

theorem OMA.disproof : ¬ (type_of% @Erdos995.erdos_995) := by
  intro H
  obtain ⟨f, n, hn, -, hint, hlow⟩ := OMA995.hoLowerBound
  have hup := H n (OMA995Bridge.isLacunary_of hn) (OMA995Bridge.gOf f)
    (OMA995Bridge.memLp_gOf f) (OMA995Bridge.integral_gOf f hint)
  have hlow' := OMA995Bridge.ae_transfer hlow
  have := MeasureTheory.ae_neBot.2 OMA995Bridge.restrict_ne_zero
  obtain ⟨α, hx1, hx2⟩ := (hup.and hlow').exists
  have hb := hx1.bound (show (0 : ℝ) < 1 by norm_num)
  have hfr := hx2 (1 / 4) (by norm_num) 3
  obtain ⟨N, hN1, hN2, hN3⟩ :=
    (hfr.and_eventually (hb.and (Filter.eventually_ge_atTop 3))).exists
  have hlog := OMA995.one_le_log_nat hN3
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hsq := OMA995.sqrt_log_le hlog
  have hnorm : ‖(N : ℝ) * Real.sqrt (Real.log (Real.log N))‖
      = (N : ℝ) * Real.sqrt (Real.log (Real.log N)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm, OMA995Bridge.partialSum_gOf] at hN2
  have hre : (OMA995.lacSum f n (α : AddCircle (1 : ℝ)) N).re
      ≤ ‖(OMA995.lacSum f n (α : AddCircle (1 : ℝ)) N).re‖ := by
    rw [Real.norm_eq_abs]; exact le_abs_self _
  have e : (1 : ℝ) / 2 - 1 / 4 = 1 / 4 := by norm_num
  rw [e] at hN1
  have hr1 : 0 < Real.log N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have h4 : (N : ℝ) * Real.sqrt (Real.log (Real.log N)) ≤ N * (2 * Real.log N ^ ((1 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hsq hNpos.le
  have h5 : 0 < (N : ℝ) * Real.log N ^ ((1 : ℝ) / 4) := mul_pos hNpos hr1
  nlinarith
