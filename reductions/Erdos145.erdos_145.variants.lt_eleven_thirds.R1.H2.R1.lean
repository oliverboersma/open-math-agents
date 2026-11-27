import OMAReductions.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1
import Mathlib

/-! Each long squarefree gap provides many disjoint starting positions for
squarefree-free intervals. A bound of order h^(-r) for their frequency
gives every gap moment of order below 1+r by summing geometric scales. -/
namespace OMA.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1_H2_R1
open Finset Filter Erdos145
open scoped Topology

def H1 : Prop :=
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  ∀ x : ℝ, 1 ≤ x → ∀ k : ℕ,
    2^k * ((A x).filter (fun n => Nat.log 2 (s (n+1)-s n) = k)).card ≤ 4 * (bad x k).card

def H2 : Prop :=
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  ∀ r : ℝ, 0 < r → r < 8/3 → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ k : ℕ,
    ((2:ℝ)^r)^k * ((bad x k).card : ℝ) ≤ C*x

theorem main : H1 → H2 → OMA.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1.H2 := by
  classical
  intro packing estimate q hq hlim
  let r := (max 0 (q-1) + 8/3)/2
  have r0 : 0 < r := by dsimp [r]; linarith [le_max_left (0:ℝ) (q-1)]
  have rt : r < 8/3 := by dsimp [r]; rw [max_def]; split <;> linarith
  have qr : q < 1+r := by dsimp [r]; linarith [le_max_right (0:ℝ) (q-1)]
  obtain ⟨C,hC,hb⟩ := estimate r r0 rt
  let d := (2:ℝ)^q / (2*2^r)
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have d1 : d < 1 := by
    dsimp [d]
    rw [div_lt_one (by positivity)]
    simpa [Real.rpow_add (by norm_num : (0:ℝ)<2)] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) qr
  refine ⟨4*C*2^q*(1-d)⁻¹,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with x hx xpos
  have xp : 0<x := by linarith
  let g (n : ℕ) := s (n+1) - s n
  let bin (n : ℕ) := Nat.log 2 (g n)
  let T := (A x).image bin
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  have block (k : ℕ) :
      (∑ n ∈ (A x).filter (fun n => bin n=k), (g n:ℝ)^q) ≤ (4*C*x*2^q)*d^k := by
    let S := (A x).filter (fun n => bin n=k)
    have pack : (2:ℝ)^k * S.card ≤ 4*(bad x k).card := by exact_mod_cast packing x xpos k
    have cnt : ((2:ℝ)^r)^k*((bad x k).card:ℝ) ≤ C*x := hx k
    have scaled : (2*(2:ℝ)^r)^k * S.card ≤ 4*C*x := by
      rw [mul_pow]
      have tmp := mul_le_mul_of_nonneg_left pack (show 0 ≤ ((2:ℝ)^r)^k by positivity)
      linarith only [show ((2:ℝ)^r)^k*((2:ℝ)^k * S.card) ≤ ((2:ℝ)^r)^k*(4*(bad x k).card) from tmp,cnt]
    have bound : ∀ n ∈ S, (g n:ℝ)^q ≤ 2^q*((2:ℝ)^q)^k := by
      intro n hn
      have e : Nat.log 2 (g n)=k := (mem_filter.mp hn).2
      have upper := Nat.lt_pow_succ_log_self (by decide : 1<2) (g n)
      rw [e,pow_succ] at upper
      have hu : (g n:ℝ) ≤ (2:ℝ)^k*2 := by exact_mod_cast upper.le
      apply (Real.rpow_le_rpow (by positivity) hu hq.le).trans_eq
      rw [Real.mul_rpow (by positivity) (by norm_num),← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (k:ℝ) q,Real.rpow_mul_natCast (by norm_num)]
      ring
    calc
      _ ≤ ∑ _n ∈ S, 2^q*((2:ℝ)^q)^k := sum_le_sum bound
      _ = S.card * (2^q*((2:ℝ)^q)^k) := by simp
      _ ≤ _ := by
        dsimp [d]
        rw [div_pow]
        rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
        convert mul_le_mul_of_nonneg_right scaled (show 0 ≤ 2^q*((2:ℝ)^q)^k by positivity) using 1 <;> ring
  have total := sum_le_sum (s := T) (fun k _ => block k)
  rw [sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem bin hn),← mul_sum] at total
  have geom := (summable_geometric_of_lt_one d0 d1).sum_le_tsum T (fun i _ => pow_nonneg d0 i)
  rw [tsum_geometric_of_lt_one d0 d1] at geom
  change 1/x * (∑ n ∈ A x,(g n:ℝ)^q) ≤ _
  calc
    _ ≤ 1/x*((4*C*x*2^q)*(1-d)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact total.trans (mul_le_mul_of_nonneg_left geom (by positivity))
    _ = _ := by field_simp <;> ring

end OMA.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1_H2_R1
