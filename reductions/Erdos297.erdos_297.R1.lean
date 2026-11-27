import FormalConjectures.ErdosProblems.«297»
import Mathlib

/-!
# Dyadic completion and the tilted upper bound for unit reciprocal mass

A partial sum on a dyadic grid below one can be completed by changing only
the available powers of two. Remembering the original dyadic entries costs
at most a factor 2N in the count. The upper bound uses a tilted product and
a monotone integral comparison.
-/

namespace OMA.R_Erdos297_erdos_297_R1

open Filter Finset Real Erdos297
open scoped Topology Classical

/-- A positive calibrating parameter and uniqueness among all real parameters. -/
def H1 : Prop := ∃ l : ℝ, 0 < l ∧ massIntegral l = 1 ∧ ∀ t : ℝ, massIntegral t = 1 → t = l

/-- Many subsets have reciprocal mass anywhere on one dyadic grid in [0,1].
The grid, including its finest denominator, must fit in the original interval. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∃ k : ℕ, 2^k ≤ N ∧
  exp (((erdos_297.answer * log 2)-ε)*N) ≤
    ((((Icc 1 N).powerset.filter (fun A : Finset ℕ =>
      ∃ j ∈ range (2^k+1), (∑ n ∈ A, (1:ℚ)/n) = j/(2:ℚ)^k)).card : ℕ) : ℝ)

lemma dyadic_fill (k j : ℕ) (hj : j ≤ 2^k) :
    ∃ S ⊆ (range (k+1)).image (fun e : ℕ => (2:ℕ)^e),
      (∑ n ∈ S, (1:ℚ)/n) = j/(2:ℚ)^k := by
  induction k generalizing j with
  | zero =>
    have : j = 0 ∨ j = 1 := by simpa using (show j ≤ 1 → j = 0 ∨ j = 1 by omega) (by simpa using hj)
    rcases this with rfl|rfl
    · exact ⟨∅,empty_subset _,by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ k ih =>
    have hm := Nat.mod_add_div j 2
    have hj' : j/2 ≤ 2^k := by rw [pow_succ] at hj; omega
    obtain ⟨S,hS,hval⟩ := ih (j/2) hj'
    let d : ℕ := 2^(k+1)
    let D : Finset ℕ := (range (k+1+1)).image (fun e : ℕ => (2:ℕ)^e)
    have hsub : S ⊆ D := hS.trans (Finset.image_subset_image (Finset.range_mono (Nat.le_succ (k+1))))
    have hd : d ∈ D := mem_image.mpr ⟨k+1,mem_range.mpr (by omega),rfl⟩
    have hnot : d ∉ S := by
      intro h
      obtain ⟨e,he,heq⟩ := mem_image.mp (hS h)
      have he' := mem_range.mp he
      exact (ne_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) he')) heq
    have hjQ := congrArg (fun t : ℕ => (t:ℚ)) hm
    push_cast at hjQ
    rcases Nat.mod_two_eq_zero_or_one j with ht|ht
    · refine ⟨S,hsub,?_⟩
      rw [ht] at hjQ
      rw [hval,pow_succ]
      field_simp
      nlinarith
    · refine ⟨insert d S,insert_subset hd hsub,?_⟩
      rw [ht] at hjQ
      rw [sum_insert hnot,hval]
      dsimp [d]
      push_cast
      rw [pow_succ]
      field_simp
      nlinarith

lemma dyadic_completions (k N : ℕ) (hk : 2^k ≤ N) :
    ((Icc 1 N).powerset.filter (fun A : Finset ℕ =>
      ∃ j ∈ range (2^k+1), (∑ n ∈ A, (1:ℚ)/n) = j/(2:ℚ)^k)).card ≤
        count 1 N * (2*N) := by
  classical
  let D := (range (k+1)).image (fun e : ℕ => (2:ℕ)^e)
  let F := (Icc 1 N).powerset.filter (fun A : Finset ℕ =>
      ∃ j ∈ range (2^k+1), (∑ n ∈ A, (1:ℚ)/n) = j/(2:ℚ)^k)
  let E := (Icc 1 N).powerset.filter (fun A : Finset ℕ => (∑ n ∈ A, (1:ℚ)/n) = 1)
  have hD : D ⊆ Icc 1 N := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := mem_image.mp hx
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2:ℕ)) _),(Nat.pow_le_pow_right (by decide) (show e ≤ k from Nat.le_of_lt_succ (mem_range.mp he))).trans hk⟩
  have complete (A : Finset ℕ) (hA : A ∈ F) : ∃ B ∈ E, B \ D = A \ D := by
    simp only [F, mem_filter] at hA
    obtain ⟨ha,j,hj,hv⟩ := hA
    have ha' := mem_powerset.mp ha
    have hj' := mem_range.mp hj
    let P := A ∩ D
    let t (n : ℕ) := 2^k / n
    have grid : (∑ n ∈ P, (1:ℚ)/n) = (∑ n ∈ P, t n : ℕ)/(2:ℚ)^k := by
      push_cast
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      obtain ⟨e,he,rfl⟩ := mem_image.mp (mem_inter.mp hn).2
      have hd : 2^e ∣ 2^k := pow_dvd_pow _ (Nat.le_of_lt_succ (mem_range.mp he))
      have hh := Nat.div_mul_cancel hd
      have heq' := congrArg (fun u : ℕ => (u : ℚ)) hh
      push_cast at heq' ⊢
      dsimp [t]
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      simpa using heq'.symm
    let M := ∑ n ∈ P, t n
    have hdec : (∑ n ∈ A \ D, (1:ℚ)/n) + ∑ n ∈ P, (1:ℚ)/n = ∑ n ∈ A, (1:ℚ)/n := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun x hx hp => (mem_sdiff.mp hx).2 (mem_inter.mp hp).2))]
      congr 1
      ext x
      by_cases h : x ∈ D <;> simp [P,h]
    have hnon : 0 ≤ ∑ n ∈ A \ D, (1:ℚ)/n := by positivity
    rw [grid,hv] at hdec
    change _ + (M:ℚ)/(2:ℚ)^k = _ at hdec
    have hm : M ≤ j := by
      have h : (M:ℚ)/(2:ℚ)^k ≤ j/(2:ℚ)^k := by linarith
      exact_mod_cast (div_le_div_iff_of_pos_right (by positivity)).mp h
    have hcomp : 2^k-j+M ≤ 2^k := by omega
    obtain ⟨S,hs,hsm⟩ := dyadic_fill k _ hcomp
    refine ⟨(A \ D) ∪ S, mem_filter.mpr ⟨mem_powerset.mpr
      (union_subset (Finset.sdiff_subset.trans ha') (hs.trans hD)),?_⟩,?_⟩
    · have hdis : Disjoint (A \ D) S := disjoint_left.mpr
        (fun x hx h => (mem_sdiff.mp hx).2 (hs h))
      rw [sum_union hdis,hsm]
      push_cast [Nat.cast_sub (show j ≤ 2^k by omega)]
      field_simp at hdec ⊢
      linarith
    · ext x
      by_cases hx : x ∈ D
      · simp [hx]
      · have hns : x ∉ S := fun h => hx (hs h)
        simp [hx,hns]
  choose B hB hd using complete
  let f (A : Finset ℕ) := if ha : A ∈ F then (B A ha, A ∩ D) else (∅,∅)
  have hcard : F.card ≤ (E ×ˢ D.powerset).card := by
    apply Finset.card_le_card_of_injOn f
    · intro A ha
      change A ∈ F at ha
      change f A ∈ E ×ˢ D.powerset
      simp only [f,dif_pos ha,mem_product,mem_powerset]
      exact ⟨hB A ha,inter_subset_right⟩
    · intro A ha A' ha' he
      change A ∈ F at ha
      change A' ∈ F at ha'
      change f A = f A' at he
      simp only [f,dif_pos ha,dif_pos ha',Prod.mk.injEq] at he
      have he1 := congrArg (fun T : Finset ℕ => T \ D) he.1
      rw [hd,hd] at he1
      ext x
      by_cases hx : x ∈ D
      · simpa [hx] using Finset.ext_iff.mp he.2 x
      · simpa [hx] using Finset.ext_iff.mp he1 x
  have hdc : D.card ≤ k+1 := (Finset.card_image_le).trans_eq (card_range _)
  have bound : 2^D.card ≤ 2*N := by
    calc
      _ ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) hdc
      _ ≤ _ := by rw [pow_succ]; omega
  exact hcard.trans (by rw [card_product,card_powerset]; exact Nat.mul_le_mul_left _ bound)

lemma positive_count (N : ℕ) (hN : 1 ≤ N) : 0 < count 1 N := by
  apply Finset.card_pos.mpr
  refine ⟨{1}, mem_filter.mpr ⟨mem_powerset.mpr ?_,by simp⟩⟩
  simpa using hN

lemma tilted_upper (N : ℕ) (hN : 1 ≤ N) (l : ℝ) (hl : 0 < l) :
    log (count 1 N) ≤ (l + ∫ x in (0:ℝ)..1, log (1+exp (-l/x))) * N + log 2 := by
  classical
  let I := Icc 1 N
  let F := I.powerset.filter (fun A : Finset ℕ => (∑ n ∈ A, (1:ℚ)/n) = 1)
  let w (n : ℕ) := exp (-l*(N:ℝ)/n)
  have hw (A : Finset ℕ) (hA : A ∈ F) : (∏ n ∈ A, w n) = exp (-l*N) := by
    have hv : (∑ n ∈ A, (1:ℝ)/n) = 1 := by
      simpa using congrArg (fun t : ℚ => (t:ℝ)) (mem_filter.mp hA).2
    dsimp [w]
    rw [← Real.exp_sum]
    congr 1
    calc
      _ = (-l*N) * ∑ n ∈ A, (1:ℝ)/n := by rw [mul_sum]; simp [div_eq_mul_inv]
      _ = _ := by rw [hv,mul_one]
  have weight : (count 1 N : ℝ) * exp (-l*N) ≤ ∏ n ∈ I, (1+w n) := by
    rw [Finset.prod_one_add]
    calc
      _ = ∑ A ∈ F, ∏ n ∈ A, w n := by
        rw [sum_congr rfl hw, sum_const, nsmul_eq_mul]
        rfl
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun A _ _ =>
        prod_nonneg (fun n _ => (exp_pos _).le))
  have hc : (0:ℝ) < count 1 N := by exact_mod_cast positive_count N hN
  have hwlog := Real.log_le_log (mul_pos hc (exp_pos _)) weight
  rw [Real.log_mul hc.ne' (exp_pos _).ne', Real.log_exp, Real.log_prod (fun n _ =>
    (show 0 < 1+w n by dsimp [w]; positivity).ne')] at hwlog
  let g (x : ℝ) := if 0 < x then log (1+exp (-l/x)) else 0
  have hgn (x : ℝ) : 0 ≤ g x := by
    dsimp [g]
    split_ifs
    · apply Real.log_nonneg; linarith [exp_pos (-l/x)]
    · rfl
  have hmono : Monotone g := by
    intro x y hxy
    by_cases hx : 0 < x
    · have hy := hx.trans_le hxy
      simp only [g, if_pos hx, if_pos hy]
      apply Real.log_le_log (by positivity)
      apply add_le_add (le_refl _)
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ hx hy]
      nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hxy)]
    · simpa only [g,if_neg hx] using hgn y
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hI : (∫ x in (0:ℝ)..1, g x) = ∫ x in (0:ℝ)..1, log (1+exp (-l/x)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    simp [g,hx.1]
  have hRi : ∑ n ∈ range N, g ((n:ℝ)/N) ≤ (N:ℝ)*(∫ x in (0:ℝ)..1, g x) := by
    have hf : Monotone (fun x : ℝ => g (x/N)) := fun _ _ h => hmono (div_le_div_of_nonneg_right h hNR.le)
    have hi := (hf.monotoneOn _).sum_le_integral_Ico (Nat.zero_le N)
    simpa [Nat.Ico_zero_eq_range, intervalIntegral.integral_comp_div g hNR.ne',hNR.ne',
      smul_eq_mul] using hi
  have hend : g ((N:ℝ)/N) ≤ log 2 := by
    simp only [div_self hNR.ne',g,if_pos zero_lt_one,div_one]
    apply Real.log_le_log (by positivity)
    linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.le)]
  have hs : (∑ n ∈ I, log (1 + w n)) ≤ (N:ℝ)*(∫ x in (0:ℝ)..1, g x) + log 2 := by
    calc
      _ = ∑ n ∈ I, g ((n:ℝ)/N) := by
        apply sum_congr rfl
        intro n hn
        have hnR : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        simp only [g, if_pos (div_pos hnR hNR),w]
        congr 2
        field_simp
      _ ≤ ∑ n ∈ range (N+1), g ((n:ℝ)/N) := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => hgn _)
        exact fun i hi => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hi).2)
      _ ≤ _ := by rw [sum_range_succ]; exact add_le_add hRi hend
  rw [hI] at hs
  linarith

theorem main : H1 → H2 → type_of% @Erdos297.erdos_297 := by
  intro hcal hmany
  obtain ⟨l,hl,hM,huniq⟩ := hcal
  have hsol : {t : ℝ | massIntegral t = 1} = {l} := by
    ext t
    change massIntegral t = 1 ↔ t = l
    exact ⟨huniq t, fun h => h ▸ hM⟩
  have hLambda : lambdaOf 1 = l := by simp only [lambdaOf, Rat.cast_one, hsol,csInf_singleton]
  have hlog := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hans : erdos_297.answer * log 2 = l + ∫ x in (0:ℝ)..1, log (1+exp (-l/x)) := by
    unfold erdos_297.answer
    rw [hLambda, div_mul_cancel₀ _ hlog.ne']
  refine ⟨⟨l,hM,huniq⟩,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let c := ε*log 2/6
  have hc : 0 < c := by dsimp [c]; positivity
  have hbig := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ) by norm_num)).bound
    (show 0 < c/2 by positivity)
  have ht : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hmany c hc, ht.eventually hbig, eventually_ge_atTop (1:ℕ)] with N hg hlogerr hn
  obtain ⟨k,hk,hm⟩ := hg
  have hnR : (0:ℝ) < N := by exact_mod_cast hn
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hn
  have hcount := positive_count N hn
  have hcnt : (0:ℝ) < count 1 N := by exact_mod_cast hcount
  have hmul : ((2:ℝ)*N) > 0 := by positivity
  have hl2 : 0 ≤ log ((2:ℝ)*N) := log_nonneg (by linarith)
  have hsmall : log ((2:ℝ)*N) ≤ c*N := by
    simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hl2, abs_of_pos hmul] at hlogerr
    linarith
  have hsmall2 : log 2 ≤ c*N :=
    (Real.log_le_log (by norm_num) (by linarith : (2:ℝ) ≤ 2*N)).trans hsmall
  have hb := dyadic_completions k N hk
  have hsize : exp ((erdos_297.answer*log 2-c)*N) ≤ (count 1 N:ℝ)*(2*N) :=
    hm.trans (by exact_mod_cast hb)
  have hlo := Real.log_le_log (exp_pos _) hsize
  rw [Real.log_exp, Real.log_mul hcnt.ne' hmul.ne'] at hlo
  have hhi := tilted_upper N hn l hl
  rw [← hans] at hhi
  change dist (Real.logb 2 (count 1 N)/N) erdos_297.answer < ε
  rw [Real.dist_eq, abs_lt, Real.logb, div_div]
  constructor
  · apply (lt_sub_iff_add_lt).mpr
    apply (lt_div_iff₀ (mul_pos hlog hnR)).mpr
    dsimp [c] at *
    nlinarith [mul_pos (mul_pos hε hlog) hnR]
  · apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ (mul_pos hlog hnR)).mpr
    dsimp [c] at *
    nlinarith [mul_pos (mul_pos hε hlog) hnR]

end OMA.R_Erdos297_erdos_297_R1
