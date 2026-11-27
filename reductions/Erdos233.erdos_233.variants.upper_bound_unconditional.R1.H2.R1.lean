import OMAReductions.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1

-- Reduction Erdos233.erdos_233.variants.upper_bound_unconditional.R1.H2.R1 of step Erdos233.erdos_233.variants.upper_bound_unconditional.R1.H2
-- Credit: @marcusbuffett

/-! Selberg’s mean square bounds the total length of large prime gaps. We isolate the
unconditional lower bound on the integral inside prime-free intervals from the conditional
upper bound for the zero sum. The prime indexing and telescoping lemmas are adapted
from @senamakel’s conditional Erdős 233 reduction. -/
namespace OMA.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1_H2_R1

section

open Nat

lemma nth_lt_of_lt_idx {n m : ℕ} (h : n < Nat.primeCounting' m) : nth Nat.Prime n < m :=
  Nat.nth_lt_of_lt_count h

lemma le_nth_of_idx_le {n m : ℕ} (h : Nat.primeCounting' m ≤ n) : m ≤ nth Nat.Prime n :=
  (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).1 h

lemma mem_block {x n : ℕ} (h : n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x)))) :
    x ≤ nth Nat.Prime n ∧ nth Nat.Prime n < 2 * x := by
  rw [Finset.mem_Ico] at h
  exact ⟨le_nth_of_idx_le h.1, nth_lt_of_lt_idx h.2⟩

lemma nth_succ_le_two_mul (n : ℕ) : nth Nat.Prime (n + 1) ≤ 2 * nth Nat.Prime n := by
  have h0 : nth Nat.Prime n ≠ 0 := (Nat.prime_nth_prime n).ne_zero
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  have e := Nat.nth_count hq
  rw [← e] at hlt hle
  rw [Nat.nth_lt_nth Nat.infinite_setOfPred_prime] at hlt
  exact le_trans ((Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt) hle

lemma nth_le_nth_succ (n : ℕ) : nth Nat.Prime n ≤ nth Nat.Prime (n + 1) :=
  (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (Nat.le_succ n)

lemma primeGap_cast (n : ℕ) :
    (primeGap n : ℝ) = (nth Nat.Prime (n + 1) : ℝ) - nth Nat.Prime n := by
  unfold primeGap
  rw [Nat.cast_sub (nth_le_nth_succ n)]

lemma sum_Ico_primeGap (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (primeGap n : ℝ) = (nth Nat.Prime b : ℝ) - nth Nat.Prime a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Finset.sum_Ico_eq_sum_range, show a + k - a = k by omega]
  simp_rw [primeGap_cast, show ∀ i, a + i + 1 = a + (i + 1) from fun i => by ring]
  exact Finset.sum_range_sub (fun i => (nth Nat.Prime (a + i) : ℝ)) k

lemma sum_block_primeGap_le (x : ℕ) :
    ∑ n ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))), (primeGap n : ℝ) ≤ 4 * x := by
  by_cases hab : Nat.primeCounting' x < Nat.primeCounting' (2 * x)
  · rw [sum_Ico_primeGap _ _ hab.le]
    have hb : Nat.primeCounting' (2 * x) - 1 ∈ (Finset.Ico (Nat.primeCounting' x) (Nat.primeCounting' (2 * x))) := by
      rw [Finset.mem_Ico]; omega
    have h1 := (mem_block hb).2
    have h2 := nth_succ_le_two_mul (Nat.primeCounting' (2 * x) - 1)
    rw [show Nat.primeCounting' (2 * x) - 1 + 1 = Nat.primeCounting' (2 * x) by omega] at h2
    have h3 : (nth Nat.Prime (Nat.primeCounting' (2 * x)) : ℝ) ≤ 4 * x := by
      exact_mod_cast (by omega : nth Nat.Prime (Nat.primeCounting' (2 * x)) ≤ 4 * x)
    have h4 : (0 : ℝ) ≤ nth Nat.Prime (Nat.primeCounting' x) := Nat.cast_nonneg _
    linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity


end


open Finset Filter Real MeasureTheory

/-- A gap of length at least 16h forces a large second difference on disjoint
subintervals of at least half the gap's length. -/
def H1 : Prop :=
  let W (δ y : ℝ) := ‖∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ)+1) *
      ((((1+2*δ : ℝ) : ℂ)^((ρ : ℂ)+1) - 2*((1+δ : ℝ) : ℂ)^((ρ : ℂ)+1) + 1) /
        ((ρ : ℂ)*((ρ : ℂ)+1))))‖^2
  ∀ᶠ x : ℕ in atTop, ∀ h : ℝ, 1 ≤ h → 128*(log x)^2 ≤ h → h ≤ x/8 →
    IntervalIntegrable (W (h/x)) volume x (4*x) →
    (∑ n ∈ (Ico (Nat.primeCounting' x) (Nat.primeCounting' (2*x))).filter
      (fun n => 16*h ≤ (primeGap n : ℝ)), (primeGap n : ℝ)) * h^4 ≤
      8 * ∫ y in (x:ℝ)..4*x, W (h/x) y

/-- The mean square of the zero sum in the additive scale h = δx. -/
def H2 : Prop :=
  let W (δ y : ℝ) := ‖∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * ((y : ℂ) ^ ((ρ : ℂ)+1) *
      ((((1+2*δ : ℝ) : ℂ)^((ρ : ℂ)+1) - 2*((1+δ : ℝ) : ℂ)^((ρ : ℂ)+1) + 1) /
        ((ρ : ℂ)*((ρ : ℂ)+1))))‖^2
  RiemannHypothesis → ∃ B > (0:ℝ), ∀ x : ℕ, 2 ≤ x → ∀ h : ℝ, 1 ≤ h → h ≤ x/8 →
    IntervalIntegrable (W (h/x)) volume x (4*x) ∧
      ∫ y in (x:ℝ)..4*x, W (h/x) y ≤ B*x*h^3*(log x)^2

theorem main : H1 → H2 → OMA.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1.H2 := by
  intro lower upper rh
  obtain ⟨B,hB,mean⟩ := upper rh
  obtain ⟨X,lower⟩ := eventually_atTop.mp lower
  let C := 8192 + 128*B + 32*(X:ℝ)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun r k hk => ?_⟩
  rcases r with _|r
  · have e : Nat.primeCounting' 1 = Nat.primeCounting' 2 := by decide
    simp [e]
  let x : ℕ := 2^(r+1)
  have hx : 2 ≤ x := by dsimp [x]; rw [pow_succ]; have := Nat.two_pow_pos r; omega
  have hxR : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0:ℝ)<x := by linarith
  let T := Ico (Nat.primeCounting' x) (Nat.primeCounting' (2*x))
  let S := T.filter fun n => k ≤ primeGap n
  have recast : (2:ℕ)^(r+1+1) = 2*x := by simp [x,pow_succ,mul_comm]
  have realX : (2:ℝ)^(r+1) = (x:ℝ) := by simp [x]
  rw [recast,←sum_filter,realX]
  change (∑ n ∈ S, (primeGap n:ℝ)) ≤ C*(x:ℝ)*(log x)^2/k
  let s : ℝ := ∑ n ∈ S, (primeGap n:ℝ)
  change s ≤ _
  have loglb : 1/2 ≤ log x := by
    have := Real.log_two_gt_d9
    exact le_trans (by linarith : 1/2 ≤ log 2) (log_le_log (by norm_num) hxR)
  have kpos : (0:ℝ) < k := by exact_mod_cast hk
  have total : s ≤ 4*x := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun n _ _ => Nat.cast_nonneg (primeGap n))).trans (sum_block_primeGap_le x)
  by_cases big : 2*x < k
  · have emp : S = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro j hj bad
      have ha := (mem_block hj).2
      have hb := nth_succ_le_two_mul j
      unfold primeGap at bad
      omega
    simp [s,emp]
    positivity
  have kup : (k:ℝ) ≤ 2*x := by exact_mod_cast (Nat.le_of_not_gt big)
  have elementary (coeff : 4*(k:ℝ) ≤ C*(log x)^2) : s ≤ C*(x:ℝ)*(log x)^2/k := by
    apply (le_div_iff₀ kpos).mpr
    calc s*k ≤ (4*x)*k := mul_le_mul_of_nonneg_right total kpos.le
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right coeff hxpos.le]
  by_cases early : x < X
  · have early' : (x:ℝ) ≤ X := by exact_mod_cast early.le
    have c : 32*(X:ℝ) ≤ C := by dsimp [C]; linarith
    have l : (1/4:ℝ) ≤ (log x)^2 := by nlinarith [sq_nonneg (log x-1/2)]
    apply elementary
    nlinarith only [kup,early',c,mul_le_mul_of_nonneg_left l hC.le]
  by_cases small : (k:ℝ) ≤ 2048*(log x)^2
  · apply elementary
    have c : 8192 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) X]
    nlinarith only [small,mul_le_mul_of_nonneg_right c (sq_nonneg (log (x:ℝ)))]
  let h : ℝ := k/16
  have hth : 128*(log x)^2 ≤ h := by dsimp [h]; linarith
  have hone : 1 ≤ h := by nlinarith [sq_nonneg (log x-1/2)]
  have hmax : h ≤ x/8 := by dsimp [h]; linarith
  obtain ⟨integrable,ms⟩ := mean x hx h hone hmax
  have low := lower x (Nat.le_of_not_gt early) h hone hth hmax integrable
  have ident : (T.filter fun n => 16*h ≤ (primeGap n:ℝ)) = S := by
    apply filter_congr
    intro n _
    rw [show 16*h = (k:ℝ) by dsimp [h]; ring]
    exact_mod_cast Iff.rfl
  change (∑ n ∈ T.filter (fun n => 16*h ≤ (primeGap n:ℝ)), (primeGap n:ℝ)) * h^4 ≤ _ at low
  rw [ident] at low
  have bound : s*h^4 ≤ 8*(B*x*h^3*(log x)^2) := low.trans (mul_le_mul_of_nonneg_left ms (by norm_num))
  have sh : s*h ≤ 8*B*x*(log x)^2 := by
    have eqn : (s*h)*h^3 ≤ (8*B*x*(log x)^2)*h^3 := by nlinarith only [bound]
    exact le_of_mul_le_mul_right eqn (by positivity)
  rw [le_div_iff₀ kpos]
  have c : 128*B ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) X]
  dsimp [h] at sh
  nlinarith only [sh,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c hxpos.le) (sq_nonneg (log (x:ℝ)))]

end OMA.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1_H2_R1
