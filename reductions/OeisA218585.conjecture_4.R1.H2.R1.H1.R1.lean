import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1
import Mathlib

/-! We separate the boundary behavior of the angular Dirichlet series
from the real Tauberian theorem and the ordinary prime number theorem in
the progression one modulo three. Subtracting the two nonnegative
coefficient sequences gives the signed angular series. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
open Finset OeisA218585 Filter Real ArithmeticFunction
open scoped Topology

/-- Hecke's boundary theorem for the two nonnegative shifts of each angular mode. -/
def H1 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → ∀ e : ℝ, |e| = 1 →
    let w (n : ℕ) := if n.Prime ∧ n%3=1 then cos ((k:ℝ)*(6*(z n).arg)) else 0
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
      Set.EqOn G (fun s => LSeries (fun n => ((Λ n * (1+e*w n) : ℝ) : ℂ)) s -
        1/(s-1)) {s | 1 < s.re}

/-- A dominated form of the Wiener–Ikehara theorem for a pole with residue one. -/
def H2 : Prop := ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ 2*Λ n) →
  (∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
    Set.EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - 1/(s-1)) {s | 1 < s.re}) →
  Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 1)

/-- The ordinary prime number theorem and its theta form, with the same strict cutoff. -/
def H3 : Prop :=
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p%3=1
  Tendsto (fun N : ℕ => ((P N).card:ℝ)*Real.log N/N) atTop (𝓝 (1/2:ℝ)) ∧
  Tendsto (fun N : ℕ => (∑ p ∈ P N, Real.log p)/N) atTop (𝓝 (1/2:ℝ))

theorem main : H1 → H2 → H3 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1.H1 := by
  classical
  intro boundary tauberian counts k hk
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let u (n : ℕ) := cos ((k:ℝ)*(6*(z n).arg))
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p%3=1
  let w (n : ℕ) := if n.Prime ∧ n%3=1 then u n else 0
  let f (e : ℝ) (n : ℕ) := Λ n*(1+e*w n)
  have hw (n) : |w n| ≤ 1 := by dsimp [w]; split <;> simp [u,abs_cos_le_one]
  have mean (e : ℝ) (he : |e|=1) :
      Tendsto (fun N : ℕ => (∑ n ∈ range N, f e n)/N) atTop (𝓝 1) := by
    apply tauberian (f e) _ (boundary k hk e he)
    intro n
    have h : |e*w n| ≤ 1 := by simpa [abs_mul,he] using hw n
    obtain ⟨lo,hi⟩ := abs_le.mp h
    dsimp [f]
    exact ⟨mul_nonneg vonMangoldt_nonneg (by linarith),
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left (by linarith : 1+e*w n≤2) (vonMangoldt_nonneg (n:=n))⟩
  let W (N : ℕ) := ∑ p ∈ P N, Real.log p*u p
  let T (N : ℕ) := ∑ p ∈ P N, u p
  have canc : Tendsto (fun N : ℕ => W N/N) atTop (𝓝 0) := by
    have h := ((mean 1 (by norm_num)).sub (mean (-1) (by norm_num))).div_const 2
    rw [sub_self,zero_div] at h
    apply h.congr
    intro N
    change ((∑ n ∈ range N, f 1 n)/N - (∑ n ∈ range N, f (-1) n)/N)/2 = W N/N
    rw [←sub_div,←sum_sub_distrib]
    have sumid : (∑ n ∈ range N, (f 1 n-f (-1) n)) = 2*W N := by
      dsimp only [W,P]
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro n _
      by_cases b : n.Prime ∧ n%3=1
      · simp [f,w,b,vonMangoldt_apply_prime b.1]; ring
      · simp [f,w,b]
    rw [sumid]; ring
  obtain ⟨pc,theta⟩ := counts
  have gap := pc.sub theta
  rw [sub_self] at gap
  have diff : Tendsto (fun N : ℕ => (Real.log N*T N-W N)/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ gap
    filter_upwards [eventually_gt_atTop 0] with N hn
    change ‖(Real.log N*T N-W N)/N‖ ≤ ((P N).card:ℝ)*Real.log N/N - (∑ p ∈ P N, Real.log p)/N
    rw [Real.norm_eq_abs,abs_div,show |(N:ℝ)| = (N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N),←sub_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    dsimp only [T,W]
    rw [mul_sum,← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P N, |Real.log N*u p-Real.log p*u p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P N, (Real.log N-Real.log p) := by
        apply sum_le_sum
        intro p hp
        have hpr := (mem_filter.mp hp).2.1
        have hpN := mem_range.mp (mem_filter.mp hp).1
        have hpos : 0 ≤ Real.log N-Real.log p := sub_nonneg.mpr (Real.log_le_log
          (by exact_mod_cast hpr.pos) (by exact_mod_cast hpN.le))
        rw [←sub_mul,abs_mul,abs_of_nonneg hpos]
        exact mul_le_of_le_one_right hpos (abs_cos_le_one _)
      _ = _ := by rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
  have recombined := diff.add canc
  rw [zero_add] at recombined
  have result := recombined.div pc (by norm_num : (1/2:ℝ) ≠ 0)
  rw [zero_div] at result
  apply result.congr'
  filter_upwards [eventually_ge_atTop 2] with N hn
  have hN : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hl : 0<Real.log N := log_pos (by exact_mod_cast (by omega : 1<N))
  change (((Real.log N*T N-W N)/N+W N/N)/(((P N).card:ℝ)*Real.log N/N)) = T N/(P N).card
  by_cases hc : (P N).card=0
  · simp [hc]
  have hcard : ((P N).card:ℝ) ≠ 0 := by exact_mod_cast hc
  field_simp
  <;> ring

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1

