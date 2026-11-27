import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1
import Mathlib

/-! Prachar's shifted-prime construction (1955, Satz 2). The analytic input is
a divisor-rich modulus with uniform progression bounds. The finite averaging
step can be carried out by grouping its divisors into dyadic intervals and
pigeonholing the cofactor of a shifted prime. We absorb the dyadic loss here. -/
namespace OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R1
open Finset Real Filter
open scoped Topology

/-- The primorial with one exceptional prime removed, and its progression bounds. -/
def H1 : Prop :=
  ∃ a A : ℝ, 0 < a ∧ 1 ≤ A ∧ ∃ᶠ K : ℕ in atTop, ∃ X : ℕ, K ≤ X ∧
    log X ≤ A * log K * log (log K) ∧
    exp (a * log K / log (log K)) ≤ (K.divisors.card:ℝ) ∧ (∀ d ∈ K.divisors, (X:ℝ) ≤ A * d * log X *
    (((range (X+1)).filter (fun p => p.Prime ∧ d ∣ p-1)).card:ℝ))

/-- A finite counting statement, with no hypothesis about asymptotic prime distribution. -/
def H2 : Prop :=
  ∀ K X : ℕ, 2 ≤ K → K ≤ X → ∀ A : ℝ, 1 ≤ A → (∀ d ∈ K.divisors, (X:ℝ) ≤ A * d * log X *
    (((range (X+1)).filter (fun p => p.Prime ∧ d ∣ p-1)).card:ℝ)) →
    ∃ n : ℕ, K ≤ n ∧ n ≤ K*X ∧ (K.divisors.card:ℝ) ≤
      2 * ((Nat.log 2 K:ℝ)+1) * A * log X *
      (((range (n+2)).filter (fun p => p.Prime ∧ p-1 ∣ n)).card:ℝ)

private lemma absorb (a A : ℝ) (ha : 0<a) (hA : 1≤A) :
    ∀ᶠ L : ℝ in atTop, 6*A^2*L^3 ≤ exp (a*L/(2*log L)) := by
  let C := |log (6*A^2)| + 3
  have cp : 0<C := by dsimp [C]; positivity
  have small := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).bound
    (div_pos ha (mul_pos (by norm_num : (0:ℝ)<2) cp))
  filter_upwards [small,tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop 0] with L h l1 L0
  change ‖(log L)^(2:ℝ)‖ ≤ a/(2*C) * ‖L^(1:ℝ)‖ at h
  rw [Real.rpow_two,Real.rpow_one,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg L0.le] at h
  have sm : 2*C*(log L)^2 ≤ a*L := by
    calc
      _ ≤ 2*C*(a/(2*C)*L) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by field_simp
  change 1≤log L at l1
  have l0 : 0<log L := by linarith
  have coeff : log (6*A^2) + 3*log L ≤ C*log L := by
    have hh := le_mul_of_one_le_right (abs_nonneg (log (6*A^2))) l1
    dsimp [C]
    linarith [le_abs_self (log (6*A^2))]
  have prodpos : 0<6*A^2*L^3 := by positivity
  rw [← Real.log_le_log_iff prodpos (Real.exp_pos _),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_pow]
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ C*log L*(2*log L) := mul_le_mul_of_nonneg_right coeff (by positivity)
    _ = 2*C*(log L)^2 := by ring
    _ ≤ _ := sm

theorem main : H1 → H2 → OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H1 := by
  rintro ⟨a,A,ha,hA,data⟩ havg
  have A0 : 0<A := by linarith
  refine ⟨a/(8*A),by positivity,frequently_atTop.2 ?_⟩
  intro M
  have lim := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨K,⟨X,KX,hX,divs,prog⟩,⟨hcost,l1⟩,K2,KM⟩ :=
    (data.and_eventually (((lim.eventually (absorb a A ha hA)).and
     ((tendsto_log_atTop.comp lim).eventually_ge_atTop 1)).and
     ((eventually_ge_atTop 2).and (eventually_ge_atTop M)))).exists
  obtain ⟨n,Kn,nKX,avg⟩ := havg K X K2 KX A hA prog
  refine ⟨n,KM.trans Kn,?_⟩
  let L := log (K:ℝ)
  let l := log L
  change 1≤l at l1
  change 6*A^2*L^3 ≤ exp (a*L/(2*l)) at hcost
  change log X ≤ A*L*l at hX
  change exp (a*L/l) ≤ _ at divs
  have Kpos : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have Xpos : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have npos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have L0 : 0<L := log_pos (by exact_mod_cast (by omega : 1<K))
  have l0 : 0<l := by linarith
  have lL : l ≤ L := (log_le_sub_one_of_pos L0).trans (by linarith)
  have Ln : L ≤ log n := log_le_log Kpos (by exact_mod_cast Kn)
  have ln : l ≤ log (log n) := log_le_log L0 Ln
  have up : log n ≤ 2*A*L*l := by
    have q : (n:ℝ) ≤ (K:ℝ)*X := by exact_mod_cast nKX
    have H := log_le_log npos q
    rw [Real.log_mul Kpos.ne' Xpos.ne'] at H
    have LL : L ≤ A*L*l := by
      calc
        L ≤ A*L := le_mul_of_one_le_left L0.le hA
        _ ≤ _ := le_mul_of_one_le_right (by positivity) l1
    change log n ≤ L + log X at H
    linarith only [H,hX,LL]
  have nd := Real.natLog_le_logb K 2
  change (Nat.log 2 K:ℝ) ≤ L / log 2 at nd
  replace nd := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp nd
  have log2 := Real.log_two_gt_d9
  have h2K : log 2 ≤ L := log_le_log (by norm_num) (by exact_mod_cast K2)
  have dyad : (Nat.log 2 K:ℝ)+1 ≤ 3*L := by
    change (Nat.log 2 K:ℝ)*log 2 ≤ L at nd
    have := Nat.cast_nonneg (α:=ℝ) (Nat.log 2 K)
    nlinarith
  have logX0 := Real.log_natCast_nonneg X
  have cost : 2*((Nat.log 2 K:ℝ)+1)*A*log X ≤ exp (a*L/(2*l)) := by
    refine le_trans ?_ hcost
    calc
      _ ≤ (2*(3*L)*A)*(A*L*l) := by gcongr
      _ ≤ (2*(3*L)*A)*(A*L*L) := by gcongr
      _ = _ := by ring
  let D : ℝ := (((range (n+2)).filter (fun p => p.Prime ∧ p-1 ∣ n)).card:ℝ)
  have low : exp (a*L/(2*l)) ≤ D := by
    apply le_of_mul_le_mul_left (a:=exp (a*L/(2*l))) _ (exp_pos _)
    calc
      _ = exp (a*L/l) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := divs.trans avg
      _ ≤ exp (a*L/(2*l))*D := mul_le_mul_of_nonneg_right cost (Nat.cast_nonneg _)
  refine le_trans ?_ low
  rw [Real.rpow_def_of_pos npos,Real.exp_le_exp]
  have sq0 : 0 < (log (log n))^2 := by have : 0<log (log n) := l0.trans_le ln; positivity
  calc
    log n*(a/(8*A)/(log (log n))^2) = (log n*(a/(8*A)))/(log (log n))^2 := by ring
    _ ≤ (2*A*L*l*(a/(8*A)))/l^2 := by gcongr
    _ ≤ a*L/(2*l) := by
      field_simp
      nlinarith [mul_pos (mul_pos (mul_pos A0 ha) L0) l0]

end OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R1
