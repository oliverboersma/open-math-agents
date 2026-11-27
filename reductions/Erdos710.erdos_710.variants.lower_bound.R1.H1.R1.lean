import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1
import Mathlib

/-! Based on Erdős and Pomerance, Matching the natural numbers up to n with
distinct multiples in another interval, Section 2. At a supporting point of
the smooth counting function, two powers bound the counts at the endpoints.
The hyperbolic cosine estimate supplies the strict deficit. -/
namespace OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1

open Finset Filter Real
open scoped Topology

/-- A supporting power at an integer near the prescribed logarithmic scale. -/
def H1 : Prop := ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ᶠ y : ℕ in atTop, ∃ m : ℕ, 0 < m ∧
  (1-ξ)*y*log y/4 ≤ log m ∧ log m ≤ (1+ξ)*y*log y/4 ∧
  ∀ z : ℕ, m/y ≤ z → z ≤ m*y →
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
      (Nat.smoothNumbersUpTo m y).card * ((z:ℝ)/m)^(4/(log y)^2 : ℝ)

/-- Choice of smoothness scale and integer endpoint with room for rounding. -/
def H2 : Prop := ∀ η : ℝ, 0 < η → η < 1 → ∃ ξ h : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < h ∧
  ∀ Y : ℕ, ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, Y ≤ y ∧ 2 ≤ y ∧
    ∀ m : ℕ, 0 < m → (1-ξ)*y*log y/4 ≤ log m → log m ≤ (1+ξ)*y*log y/4 →
      (m:ℝ) ≤ η*n ∧ ∃ B : ℕ, m ≤ B ∧ B ≤ m*y ∧
        (1-η)*(2/√(exp 1))*m*√(log n/log (log n)) ≤ B ∧
        (B:ℝ)/m ≤ exp (log y/2-(1/2+h))

lemma power_sum {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    (exp (w/2-(1/2+h)))^(4/w^2 : ℝ) +
    (exp (-w/2-(1/2+h)))^(4/w^2 : ℝ) < 2 := by
  let a := -(1/2+h)*(4/w^2)
  have h₁ : (w/2-(1/2+h))*(4/w^2) = a+2/w := by
    dsimp [a]; field_simp; ring
  have h₂ : (-w/2-(1/2+h))*(4/w^2) = a+ -(2/w) := by
    dsimp [a]; field_simp; ring
  have h₃ : a+(2/w)^2/2 < 0 := by
    have he : a+(2/w)^2/2 = -4*h/w^2 := by dsimp [a]; field_simp; ring
    rw [he]
    exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hw)
  rw [← exp_mul, ← exp_mul, h₁, h₂, exp_add, exp_add, ← mul_add]
  calc
    _ = 2*(exp a * cosh (2/w)) := by rw [Real.cosh_eq]; ring
    _ ≤ 2*(exp a * exp ((2/w)^2/2)) := by
      gcongr
      exact cosh_le_exp_half_sq _
    _ = 2*exp (a+(2/w)^2/2) := by rw [exp_add]
    _ < 2 := by linarith [Real.exp_lt_one_iff.mpr h₃]

private lemma counts {m y B : ℕ} (hm : 0 < m) (hy : 2 ≤ y) (hB : m ≤ B) (hBy : B ≤ m*y)
    {h : ℝ} (hh : 0 < h) (hb : (B:ℝ)/m ≤ exp (log y/2-(1/2+h)))
    (support : ∀ z : ℕ, m/y ≤ z → z ≤ m*y →
      ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
        (Nat.smoothNumbersUpTo m y).card * ((z:ℝ)/m)^(4/(log y)^2 : ℝ)) :
    ((Ioc m B).filter (· ∈ Nat.smoothNumbers y)).card <
      ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)).card := by
  let F := fun z : ℕ => Nat.smoothNumbersUpTo z y
  have monoF : Monotone F := by
    intro i j hij d hd
    obtain ⟨hd,hs⟩ := Nat.mem_smoothNumbersUpTo.mp hd
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨hd.trans hij,hs⟩
  have hyN : 0 < y := by omega
  have hyr : 0 < (y:ℝ) := by exact_mod_cast hyN
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hw : 0 < log y := log_pos (by exact_mod_cast (show 1 < y by omega))
  have hq : B/y ≤ m := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hyN).mpr
    rw [Nat.succ_mul]
    omega
  have hpos : 0 < ((F m).card:ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨1,Nat.mem_smoothNumbersUpTo.mpr ⟨hm,by simp [Nat.mem_smoothNumbers]⟩⟩ : 0 < (F m).card)
  have hqR : ((B/y:ℕ):ℝ) ≤ (B:ℝ)/y := by
    apply (le_div_iff₀ hyr).mpr
    exact_mod_cast Nat.div_mul_le_self B y
  have hr : ((B/y:ℕ):ℝ)/m ≤ exp (-log y/2-(1/2+h)) := by
    calc
      _ ≤ ((B:ℝ)/y)/m := div_le_div_of_nonneg_right hqR hmr.le
      _ = ((B:ℝ)/m)/y := by ring
      _ ≤ exp (log y/2-(1/2+h))/y := div_le_div_of_nonneg_right hb hyr.le
      _ = exp (-log y/2-(1/2+h)) := by
        nth_rw 2 [← Real.exp_log hyr]
        rw [← Real.exp_sub]
        congr 1 <;> ring
  have top := support B ((Nat.div_le_self m y).trans hB) hBy
  have bot := support (B/y) (Nat.div_le_div_right hB) (hq.trans (hB.trans hBy))
  change ((F B).card:ℝ) ≤ (F m).card * _ at top
  change ((F (B/y)).card:ℝ) ≤ (F m).card * _ at bot
  have σ : 0 ≤ (4:ℝ)/(log y)^2 := by positivity
  have s₁ := Real.rpow_le_rpow (by positivity : 0 ≤ (B:ℝ)/m) hb σ
  have s₂ := Real.rpow_le_rpow (by positivity : 0 ≤ ((B/y:ℕ):ℝ)/m) hr σ
  have total : ((F B).card:ℝ)+(F (B/y)).card < 2*(F m).card := calc
    _ ≤ (F m).card * (((B:ℝ)/m)^(4/(log y)^2:ℝ)+(((B/y:ℕ):ℝ)/m)^(4/(log y)^2:ℝ)) := by
      rw [mul_add]; linarith only [top,bot]
    _ < _ := by
      rw [mul_comm (2:ℝ)]
      exact mul_lt_mul_of_pos_left ((add_le_add s₁ s₂).trans_lt (power_sum hw hh)) hpos
  have totalN : (F B).card + (F (B/y)).card < 2*(F m).card := by exact_mod_cast total
  have e₁ : ((Ioc m B).filter (· ∈ Nat.smoothNumbers y)) = F B \ F m := by
    ext d
    simp only [F, mem_filter, mem_Ioc, Finset.mem_sdiff, Nat.mem_smoothNumbersUpTo]
    by_cases hd : d ∈ Nat.smoothNumbers y <;> simp [hd] <;> omega
  have e₂ : ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)) = F m \ F (B/y) := by
    ext d
    simp only [F, mem_filter, mem_Icc, Finset.mem_sdiff, Nat.mem_smoothNumbersUpTo]
    rw [← Nat.div_lt_iff_lt_mul hyN]
    have hp : d ∈ Nat.smoothNumbers y → d ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers
    by_cases hd : d ∈ Nat.smoothNumbers y
    · have hdpos : 1 ≤ d := Nat.pos_of_ne_zero (hp hd)
      simp [hd,hdpos,and_comm]
    · simp [hd]
  rw [e₁,e₂,card_sdiff_of_subset (monoF hB),card_sdiff_of_subset (monoF hq)]
  have := card_le_card (monoF hB)
  have := card_le_card (monoF hq)
  omega

theorem main : H1 → H2 → OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H1 := by
  intro tangent scale η hη η1
  obtain ⟨ξ,h,ξp,ξ1,hp,choice⟩ := scale η hη η1
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (tangent ξ ξp ξ1)
  filter_upwards [choice Y] with n hn
  obtain ⟨y,hy,hy2,allm⟩ := hn
  obtain ⟨m,hm,lo,hi,support⟩ := hY y hy
  obtain ⟨small,B,hmB,hBy,lower,upper⟩ := allm m hm lo hi
  exact ⟨m,y,B,hm,small,lower,counts hm hy2 hmB hBy hp upper support⟩

end OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1
