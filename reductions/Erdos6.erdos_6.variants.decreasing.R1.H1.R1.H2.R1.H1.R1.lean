import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1
import Mathlib

/-! Siegel–Walfisz from the prime number theorem with a possible exceptional
real character zero and Siegel's ineffective lower bound on its distance
from one. The decay exponent is uniform in the logarithmic modulus cutoff. -/
open Filter Finset Real ArithmeticFunction
open scoped Classical Topology

namespace OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1_H1_R1

/-- The classical character explicit-formula estimate with its possible real zero. -/
def H1 : Prop := ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, [NeZero q] →
  (q:ℝ)≤exp (sqrt (log x)/2) → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ≠1 →
  let S := ‖∑ n ∈ range (⌊x⌋₊+1), χ (n:ZMod q)*(Λ n:ℂ)‖
  S ≤ C*x*exp (-c*sqrt (log x)) ∨
    ∃ β : ℝ, χ^2=1 ∧ χ.LFunction (β:ℂ)=0 ∧ S ≤ C*x*exp (-c*sqrt (log x)) + 2*x^β

/-- Siegel's zero exclusion for quadratic nonprincipal characters. -/
def H2 : Prop := ∀ ε : ℝ, 0<ε → ∃ b : ℝ, 0<b ∧
  ∀ q : ℕ, [NeZero q] → ∀ χ : DirichletCharacter ℂ q, χ^2=1 → χ≠1 →
  ∀ t : ℝ, χ.LFunction (t:ℂ)=0 → t ≤ 1-b*(q:ℝ)^(-ε)

lemma crude {x : ℝ} (hx : 4≤x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ range (⌊x⌋₊+1), χ (n:ZMod q)*(Λ n:ℂ)‖ ≤ 2*x*log x := by
  have lx := log_nonneg (show 1≤x by linarith)
  calc
    _ ≤ ∑ n ∈ range (⌊x⌋₊+1), ‖χ (n:ZMod q)*(Λ n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (⌊x⌋₊+1), log x := by
      apply sum_le_sum
      intro n hn
      have nx : (n:ℝ) ≤ x := (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hn))).trans
        (Nat.floor_le (by linarith))
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg vonMangoldt_nonneg]
      apply (mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)).trans
      by_cases en : n=0
      · simpa [en] using lx
      · exact vonMangoldt_le_log.trans (log_le_log (by exact_mod_cast Nat.pos_of_ne_zero en) nx)
    _ = ((⌊x⌋₊:ℝ)+1)*log x := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Nat.floor_le (show 0≤x by linarith)]) lx

lemma log_cutoff (D : ℝ) (hp : 0<D) :
    ∀ᶠ L : ℝ in atTop, L^D ≤ exp (sqrt L/2) := by
  have little := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
    (show 0<1/(2*D) by positivity)
  filter_upwards [little,eventually_gt_atTop (1:ℝ)] with L h L1
  have L0 : 0<L := by linarith
  change ‖log L‖ ≤ 1/(2*D)*‖L^(1/2:ℝ)‖ at h
  rw [←sqrt_eq_rpow,Real.norm_of_nonneg (sqrt_nonneg _),Real.norm_of_nonneg (log_nonneg L1.le)] at h
  rw [←Real.log_le_log_iff (rpow_pos_of_pos L0 D) (exp_pos _),Real.log_rpow L0,Real.log_exp]
  calc
    _ ≤ D*(1/(2*D)*sqrt L) := mul_le_mul_of_nonneg_left h hp.le
    _ = _ := by field_simp

lemma exceptional_decay {D b x β : ℝ} (D0 : 0<D) (b0 : 0<b) (x1 : 1<x)
    (tlarge : 1/b ≤ (log x)^(1/4:ℝ)) {q : ℕ} [NeZero q] (qsmall : (q:ℝ)≤(log x)^D)
    (gap : β≤1-b*(q:ℝ)^(-(1/(4*D)))) : x^β ≤ x*exp (-sqrt (log x)) := by
  let L := log x
  let t := L^(1/4:ℝ)
  let ε := 1/(4*D)
  have x0 : 0<x := by linarith
  have L0 : 0<L := log_pos x1
  have t0 : 0<t := rpow_pos_of_pos L0 _
  have e0 : 0<ε := by dsimp [ε]; positivity
  have q0 : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have qp := rpow_pos_of_pos q0 ε
  have qs : (q:ℝ)^ε ≤ t := by
    calc
      _ ≤ (L^D)^ε := rpow_le_rpow q0.le qsmall e0.le
      _ = _ := by rw [←rpow_mul L0.le]; dsimp [t,ε]; congr 1; field_simp
  have t2 : t^2=sqrt L := by
    rw [sqrt_eq_rpow]
    dsimp only [t]
    rw [←rpow_mul_natCast L0.le]
    norm_num
  have t4 : t^2*t^2=L := by rw [t2,←sq,Real.sq_sqrt L0.le]
  change β≤1-b*(q:ℝ)^(-ε) at gap
  rw [rpow_neg q0.le] at gap
  have bq : b≤(1-β)*(q:ℝ)^ε := (div_le_iff₀ qp).mp (by rw [div_eq_mul_inv]; linarith)
  have positive : 0≤1-β := by have := mul_pos b0 (inv_pos.mpr qp); linarith
  have b_le := bq.trans (mul_le_mul_of_nonneg_left qs positive)
  have one : 1≤b*t := by
    change 1/b≤t at tlarge
    linarith only [(div_le_iff₀ b0).mp tlarge,mul_comm t b]
  have a : 1≤(1-β)*t^2 := one.trans (by
    calc b*t ≤ ((1-β)*t)*t := mul_le_mul_of_nonneg_right b_le t0.le
         _ = _ := by ring)
  have bound : sqrt L ≤ (1-β)*L := by
    calc
      _ = 1*t^2 := by rw [t2,one_mul]
      _ ≤ ((1-β)*t^2)*t^2 := mul_le_mul_of_nonneg_right a (sq_nonneg _)
      _ = _ := by rw [mul_assoc,t4]
  calc
    x^β = exp (L*β) := rpow_def_of_pos x0 β
    _ ≤ exp (L-sqrt L) := exp_le_exp.mpr (by nlinarith only [bound])
    _ = _ := by rw [sub_eq_add_neg,exp_add]; dsimp [L]; rw [exp_log x0]

theorem main : H1 → H2 → OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨c,C,c0,C0,explicit⟩ siegel
  let a := min c 1
  have a0 : 0<a := lt_min c0 zero_lt_one
  have ac : a≤c := min_le_left _ _
  have a1 : a≤1 := min_le_right _ _
  refine ⟨a,a0,?_⟩
  intro D D0
  obtain ⟨b,b0,hβ⟩ := siegel (1/(4*D)) (by positivity)
  have big := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_log_atTop).eventually_ge_atTop (1/b)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (explicit.and ((tendsto_log_atTop.eventually (log_cutoff D D0)).and big))
  let N := max R 4
  have N4 : 4≤N := le_max_right _ _
  have logN := log_nonneg (show 1≤N by linarith)
  let B := 2*log N*exp (a*sqrt (log N))
  have B0 : 0≤B := by dsimp [B]; positivity
  refine ⟨max (C+2) B,lt_of_lt_of_le (by linarith) (le_max_left _ _),?_⟩
  intro x hx q inst qsize χ pr ne
  have xp : 0<x := by linarith
  have s0 := sqrt_nonneg (log x)
  by_cases Rle : R≤x
  · obtain ⟨core,cut,large⟩ := hR x Rle
    change 1/b≤(log x)^(1/4:ℝ) at large
    have save : C*x*exp (-c*sqrt (log x)) ≤ C*x*exp (-a*sqrt (log x)) := by
      gcongr <;> linarith only [mul_le_mul_of_nonneg_right ac s0]
    have ordinary : x*exp (-sqrt (log x)) ≤ x*exp (-a*sqrt (log x)) := by
      gcongr <;> linarith only [mul_le_mul_of_nonneg_right a1 s0,one_mul (sqrt (log x))]
    have result := core q (qsize.trans cut) χ pr ne
    rcases result with s | ⟨β,quad,zero,s⟩
    · refine (s.trans save).trans ?_
      gcongr <;> exact le_trans (by linarith : C≤C+2) (le_max_left _ _)
    · have e := exceptional_decay D0 b0 (show 1<x by linarith) large qsize (hβ q χ quad ne β zero)
      calc
        _ ≤ _ := s
        _ ≤ C*x*exp (-a*sqrt (log x))+2*(x*exp (-a*sqrt (log x))) :=
          add_le_add save (mul_le_mul_of_nonneg_left (e.trans ordinary) (by norm_num))
        _ = (C+2)*x*exp (-a*sqrt (log x)) := by ring
        _ ≤ _ := by gcongr <;> exact le_max_left _ _
  · have xN : x≤N := (le_of_not_ge Rle).trans (le_max_left _ _)
    have lN := log_le_log xp xN
    have decay := exp_le_exp.mpr (show -a*sqrt (log N) ≤ -a*sqrt (log x) by
      have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt lN) a0.le
      linarith)
    calc
      _ ≤ 2*x*log x := crude hx q χ
      _ ≤ 2*x*log N := by gcongr
      _ = B*x*exp (-a*sqrt (log N)) := by
        dsimp [B]
        rw [neg_mul,exp_neg]
        field_simp
      _ ≤ B*x*exp (-a*sqrt (log x)) := by gcongr
      _ ≤ _ := by gcongr <;> exact le_max_right _ _

end OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1_H1_R1
