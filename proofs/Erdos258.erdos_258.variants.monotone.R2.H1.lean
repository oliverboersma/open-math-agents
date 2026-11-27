import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2
import Mathlib

/-! If every scaled tail stays above 1/q, its first-step recurrence forces
the divisor sum over a dyadic interval to grow as N log² N. Double-counting
divisors gives at most order N log N, and the endpoint tail costs order N. -/
namespace DivisorTail258

open Finset Filter Real
open OMA.R_Erdos258_erdos_258_variants_monotone_R2
open scoped Topology

private lemma divisor_sum (n : ℕ) :
    (∑ j ∈ Ioc 0 n, (j.divisors.card:ℝ)) ≤ n*(1+log n) := by
  classical
  let I := Ioc 0 n
  have row (j : ℕ) (hj : j ∈ I) : j.divisors = I.filter (· ∣ j) := by
    ext p
    simp only [I,Nat.mem_divisors,mem_filter,mem_Ioc]
    obtain ⟨jp,jn⟩ := mem_Ioc.mp hj
    constructor
    · rintro ⟨hp,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hp jp,(Nat.le_of_dvd jp hp).trans jn⟩,hp⟩
    · exact fun h => ⟨h.2,jp.ne'⟩
  change (∑ j ∈ I, (j.divisors.card:ℝ)) ≤ _
  have count : (∑ j ∈ I, (j.divisors.card:ℝ)) = ∑ p ∈ I, ((n/p:ℕ):ℝ) := by
    calc
      _ = ∑ j ∈ I, ∑ p ∈ I, (if p ∣ j then (1:ℝ) else 0) := by
        apply sum_congr rfl
        intro j hj
        rw [row j hj, ← Finset.sum_filter]
        simp
      _ = _ := by
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro p hp
        rw [←Finset.sum_filter]
        simp [I,Nat.Ioc_filter_dvd_card_eq_div]
  rw [count]
  have h : ∑ p ∈ I, ((n/p:ℕ):ℝ) ≤ ∑ p ∈ I, (n:ℝ)*(p:ℝ)⁻¹ := by
    apply sum_le_sum
    intro p hp
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ (by exact_mod_cast (mem_Ioc.mp hp).1 : 0 < (p:ℝ))).mpr
    exact_mod_cast Nat.div_mul_le_self n p
  rw [←mul_sum] at h
  have same : I = Icc 1 n := by ext p; simp [I,Nat.succ_le_iff]
  rw [same] at h
  have H := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at H
  push_cast at H
  exact h.trans (mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _))

noncomputable def pref (a : ℕ → ℕ) (n : ℕ) : ℝ := (∏ i ∈ Icc 1 n, a i : ℕ)
noncomputable def raw (a : ℕ → ℕ) (n : ℕ) : ℝ := (n+1).divisors.card/pref a (n+1)
noncomputable def tail (a : ℕ → ℕ) (n : ℕ) : ℝ := pref a n * ∑' k, raw a (k+n)

private lemma rec_tail (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    a (n+1)*tail a n = (n+1).divisors.card + tail a (n+1) := by
  have shift : Summable (fun k => raw a (k+n)) := (summable_nat_add_iff n).mpr (summable_raw a ha)
  have eq := shift.tsum_eq_zero_add
  change (∑' k, raw a (k+n)) = raw a (0+n) + ∑' k : ℕ, raw a (k+1+n) at eq
  simp only [zero_add, Nat.add_right_comm _ 1 n] at eq
  have step : pref a (n+1) = pref a n*a (n+1) := by
    dsimp [pref]
    rw [prod_split a (by omega : n ≤ n+1),Icc_self,prod_singleton,Nat.cast_mul]
  have pp : pref a (n+1) ≠ 0 := by dsimp [pref]; exact_mod_cast (prod_pos a ha (n+1)).ne'
  unfold tail
  rw [eq,mul_left_comm,←mul_assoc,←step,mul_add]
  simp only [Nat.add_assoc,raw] at *
  field_simp [pp]

private lemma tail_bound (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, tail a n ≤ (n+1)*C := by
  let g := fun k : ℕ => ((k:ℝ)+1)*((1:ℝ)/2)^k
  have gsum : Summable g := by
    have h₁ : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2) (by norm_num)
    simpa [g,add_mul] using h₁.add (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))
  refine ⟨∑' k, g k,tsum_nonneg (fun k => by dsimp [g]; positivity),?_⟩
  intro n
  rw [tail, ←tsum_mul_left, ←tsum_mul_left]
  have sm : Summable (fun k => raw a (k+n)) := (summable_nat_add_iff n).mpr (summable_raw a ha)
  apply (sm.mul_left _).tsum_le_tsum _ (gsum.mul_left _)
  intro k
  let J := Icc (n+1) (k+n+1)
  let Q := (∏ i ∈ J, a i : ℕ)
  have Qp : 0 < Q := Finset.prod_pos (fun i _ => lt_of_lt_of_le (by decide) (ha i))
  have pn : 0 < pref a n := by dsimp [pref]; exact_mod_cast prod_pos a ha n
  have fact : pref a (k+n+1) = pref a n * Q := by
    dsimp [pref,Q,J]; rw [prod_split a (by omega : n ≤ k+n+1),Nat.cast_mul]
  have lower : (2:ℕ)^k ≤ Q := calc
    _ ≤ 2^J.card := Nat.pow_le_pow_right (by decide) (by dsimp [J]; rw [Nat.card_Icc]; omega)
    _ = ∏ _i ∈ J,(2:ℕ) := (prod_const _).symm
    _ ≤ _ := Finset.prod_le_prod (by simp) (fun i _ => ha i)
  have t : ((k+n+1).divisors.card:ℝ) ≤ (n+1:ℝ)*((k:ℝ)+1) := by
    have H : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
    push_cast at H
    nlinarith only [H,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg k : (0:ℝ)≤k)]
  change pref a n * ((k+n+1).divisors.card/pref a (k+n+1)) ≤ (n+1:ℝ)*g k
  rw [fact,←mul_div_assoc,mul_div_mul_left _ _ pn.ne']
  have qr : (2:ℝ)^k ≤ Q := by exact_mod_cast lower
  calc
    _ ≤ ((n+1:ℝ)*((k:ℝ)+1))/(2:ℝ)^k :=
      div_le_div₀ (by positivity) t (by positivity) qr
    _ = _ := by dsimp [g]; rw [div_pow,one_pow]; ring

lemma fast : OMA.R_Erdos258_erdos_258_variants_monotone_R2.H1 := by
  intro a ha mono _ growth q hq
  change ∃ N, tail a N < 1/(q:ℝ)
  by_contra! allLarge
  obtain ⟨C,Cp,cap⟩ := tail_bound a ha
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X,good,Xpos,lg₁,lg₂⟩ := (growth.and ((eventually_ge_atTop (1:ℕ)).and
    ((hl.eventually_ge_atTop (2*(q:ℝ)+1)).and
      (hl.eventually_ge_atTop ((q:ℝ)*(2+2*log 2+3*C)+2))))).exists
  let w := log (X:ℝ)
  change 2*(q:ℝ)+1 ≤ w at lg₁
  change (q:ℝ)*(2+2*log 2+3*C)+2 ≤ w at lg₂
  change w^2 ≤ a X at good
  have xp : 0 < (X:ℝ) := by exact_mod_cast Xpos
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq
  have per (i : ℕ) : (w^2-1)/q ≤ ((X+i+1).divisors.card:ℝ) +
      (tail a (X+(i+1))-tail a (X+i)) := by
    have h := rec_tail a ha (X+i)
    rw [Nat.add_assoc] at h
    have an : (a X:ℝ) ≤ a (X+(i+1)) := by exact_mod_cast mono (Nat.le_add_right X (i+1))
    have hk : 0 ≤ (a (X+(i+1)):ℝ)-1 := by
      have := ha (X+(i+1)); exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ a (X+(i+1)) by omega))
    have l := mul_le_mul (sub_le_sub_right (good.trans an) 1) (allLarge (X+i))
      (by positivity : 0 ≤ 1/(q:ℝ)) hk
    rw [Nat.add_assoc X i 1]
    rw [mul_one_div] at l
    linarith only [h,l]
  have total := sum_le_sum (s := range X) (fun i _ => per i)
  rw [sum_const,card_range,nsmul_eq_mul,sum_add_distrib,
    Finset.sum_range_sub (fun i => tail a (X+i))] at total
  simp only [Nat.add_zero] at total
  have subs : (range X).image (fun i => X+i+1) ⊆ Ioc 0 (2*X) := by
    intro n hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    have := mem_range.mp hi
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  have divs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ => (j.divisors.card:ℝ)) subs
    (fun _ _ _ => Nat.cast_nonneg _)
  rw [sum_image (fun i _ j _ eq => by omega)] at divs
  have upper := divs.trans (divisor_sum (2*X))
  push_cast at upper
  rw [Real.log_mul (by norm_num) xp.ne'] at upper
  change _ ≤ 2*(X:ℝ)*(1+(log 2+w)) at upper
  have endle := cap (X+X)
  push_cast at endle
  have end₀ : 0 ≤ tail a X := (by positivity : 0 ≤ 1/(q:ℝ)).trans (allLarge X)
  have X1 : 1 ≤ (X:ℝ) := by exact_mod_cast Xpos
  have capC := mul_le_mul_of_nonneg_right X1 Cp
  have small : (w^2-1)/q ≤ 2*(1+log 2+w)+3*C := by
    apply (mul_le_mul_iff_right₀ xp).mp
    linarith only [total,upper,endle,end₀,capC]
  have bad := (div_le_iff₀ qp).mp small
  have wp : 0 ≤ w := by linarith
  nlinarith only [bad,lg₂,mul_nonneg (sub_nonneg.mpr lg₁) wp]

end DivisorTail258

theorem OMA.solution : OMA.R_Erdos258_erdos_258_variants_monotone_R2.H1 := DivisorTail258.fast
