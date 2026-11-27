import FormalConjectures.Wikipedia.CramerConjecture
import Mathlib

/-! The second difference of the integrated Chebyshev sum localizes the
von Mangoldt mass to a short interval. Removing the higher prime powers and
applying the resulting interval theorem at one plus the preceding prime gives
the indexed gap bound. The finite tent estimate is adapted from @senamakel's
merged Cramér conditional-RH proof in this repository. -/
namespace OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1

open Filter Real Asymptotics ArithmeticFunction Finset
open scoped Topology

/-- Analytic short-interval input, with triangular weights. -/
def H1 : Prop :=
  let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
  ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℕ in atTop,
    let h := ⌈2*(x:ℝ)^(0.525:ℝ)⌉₊
    c*(h:ℝ)^2 ≤ F (x+2*h)-2*F (x+h)+F x

/-- Negligibility of higher prime powers on the gap scale. -/
def H2 : Prop :=
  (fun x : ℕ => ∑ d ∈ (Ico x (x+2*⌈2*(x:ℝ)^(0.525:ℝ)⌉₊)).filter (fun d => ¬ d.Prime), (Λ d:ℝ))
    =o[atTop] fun x : ℕ => (x:ℝ)^(0.525:ℝ)

lemma truncate_sum {n N : ℕ} (hn : n ≤ N) :
    (fun n : ℕ => ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)) n = ∑ k ∈ range N, (Λ k : ℝ) * max ((n : ℝ) - k) 0 := by
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun k hk => ?_
    have : (k : ℝ) < n := by exact_mod_cast mem_range.mp hk
    rw [max_eq_left (by linarith)]
  · intro k _ hk
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (by simpa using hk)
    rw [max_eq_right (by linarith), mul_zero]
lemma tent_bound (a h : ℕ) :
    (fun n : ℕ => ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)) (a + 2 * h) - 2 * (fun n : ℕ => ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)) (a + h) + (fun n : ℕ => ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)) a
      ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
  set b := a + 2 * h
  rw [truncate_sum (N := b) le_rfl, truncate_sum (N := b) (by omega),
    truncate_sum (n := a) (N := b) (by omega), mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  rw [← sum_range_add_sum_Ico _ (show a ≤ b by omega)]
  have h0 : ∑ k ∈ range a, ((Λ k : ℝ) * max ((b : ℝ) - k) 0 - 2 * ((Λ k : ℝ) *
      max (((a + h : ℕ) : ℝ) - k) 0) + (Λ k : ℝ) * max ((a : ℝ) - k) 0) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : (k : ℝ) < a := by exact_mod_cast mem_range.mp hk
    have hb : (b : ℝ) = a + 2 * h := by simp [b]
    push_cast
    have hh : (0 : ℝ) ≤ h := h.cast_nonneg
    rw [max_eq_left (by rw [hb]; linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), hb]
    ring
  rw [h0, zero_add, Finset.mul_sum]
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  have hΛ : (0 : ℝ) ≤ Λ k := vonMangoldt_nonneg
  have hak : (a : ℝ) ≤ k := by exact_mod_cast hk1
  have hkb : (k : ℝ) < a + 2 * h := by exact_mod_cast hk2
  have hb : (b : ℝ) = a + 2 * h := by simp [b]
  rw [max_eq_right (show (a : ℝ) - k ≤ 0 by linarith), hb]
  push_cast
  have key : max ((a : ℝ) + 2 * h - k) 0 - 2 * max ((a : ℝ) + h - k) 0 ≤ h := by
    rcases le_total ((a : ℝ) + h) k with h1 | h1
    · rw [max_eq_right (show (a : ℝ) + h - k ≤ 0 by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
    · rw [max_eq_left (show (0 : ℝ) ≤ a + h - k by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
  nlinarith
theorem main : H1 → H2 → type_of% @CramerConjecture.cramer_conjecture.variants.baker_harman_pintz := by
  rintro ⟨c,hc,hcF⟩ hpowers
  let h (x : ℕ) := ⌈2*(x:ℝ)^(0.525:ℝ)⌉₊
  have interval : ∀ᶠ x : ℕ in atTop, ∃ p ∈ Ico x (x+2*h x), Nat.Prime p := by
    filter_upwards [hcF,hpowers.bound hc,eventually_gt_atTop (0:ℕ)] with x hx hpow hxp
    have xr : 0 < (x:ℝ)^(0.525:ℝ) := rpow_pos_of_pos (by exact_mod_cast hxp) _
    have hh : 2*(x:ℝ)^(0.525:ℝ) ≤ (h x:ℝ) := Nat.le_ceil _
    have hp : (0:ℝ) < h x := by linarith
    have ht := tent_bound x (h x)
    have hbig : c*(h x:ℝ)^2 ≤ (h x:ℝ) * ∑ k ∈ Ico x (x+2*h x), (Λ k:ℝ) := hx.trans ht
    by_contra! absent
    have eqn : (Ico x (x+2*h x)).filter (fun k => ¬ k.Prime) = Ico x (x+2*h x) :=
      filter_eq_self.mpr absent
    change ‖∑ k ∈ (Ico x (x+2*h x)).filter (fun k => ¬ k.Prime), (Λ k:ℝ)‖ ≤ c*‖(x:ℝ)^(0.525:ℝ)‖ at hpow
    rw [eqn,Real.norm_of_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg),Real.norm_of_nonneg xr.le] at hpow
    have hb : c*h x ≤ ∑ k ∈ Ico x (x+2*h x), (Λ k:ℝ) := by
      apply (le_of_mul_le_mul_left _ hp)
      nlinarith only [hbig]
    nlinarith [mul_pos hc xr,mul_le_mul_of_nonneg_left hh hc.le]
  let p := Nat.nth Nat.Prime
  have mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have ind : Tendsto (fun n => p n+1) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_succ (p n)) mono.tendsto_atTop
  refine isBigO_iff.mpr ⟨11,?_⟩
  filter_upwards [ind.eventually interval] with n hn
  obtain ⟨q,hq,hqp⟩ := hn
  have bounds := mem_Ico.mp hq
  have hnq : p (n+1) ≤ q := by
    by_contra! hlt
    have : q ≤ p n := Nat.le_nth_of_lt_nth_succ hlt hqp
    omega
  have pp : 1 ≤ (p n:ℝ) := by exact_mod_cast (Nat.prime_nth_prime n).one_le
  have pp' := Real.one_le_rpow pp (by norm_num : (0:ℝ) ≤ 0.525)
  have pb : ((p n:ℝ)+1)^(0.525:ℝ) ≤ 2*(p n:ℝ)^(0.525:ℝ) := calc
    _ ≤ (2*(p n:ℝ))^(0.525:ℝ) := rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = 2^(0.525:ℝ)*(p n:ℝ)^(0.525:ℝ) := mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := by gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have ch : (h (p n+1):ℝ) < 2*((p n:ℝ)+1)^(0.525:ℝ)+1 := by
    simpa only [h,Nat.cast_add_one] using Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*((p n+1:ℕ):ℝ)^(0.525:ℝ))
  have gp : primeGap n ≤ 1+2*h (p n+1) := by change p (n+1)-p n ≤ _; omega
  have gr : (primeGap n:ℝ) ≤ 1+2*(h (p n+1):ℝ) := by exact_mod_cast gp
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)]
  change (primeGap n:ℝ) ≤ 11*(p n:ℝ)^(0.525:ℝ)
  linarith

end OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1
