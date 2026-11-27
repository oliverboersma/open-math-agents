import FormalConjectures.ErdosProblems.«66»
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Compactness.Compact

/-!
Credit: @Iraeeee

The fractional density is decreasing and has a self-convolution of logarithmic
size. In rounding it to a set, bounded prefix discrepancy controls both linear
terms by summation by parts. The other term is a signed quadratic convolution.
Only finite roundings are required, with a common error envelope. Compactness
supplies consistency across lengths.
-/

namespace OMA.R_Erdos66_erdos_66_R1

open AdditiveCombinatorics Finset Filter
open scoped Topology

/-- Calibration of the fractional weights. The constant is pi times the square of a.
On delta*n <= i <= (1-delta)*n the normalized sum is a Riemann sum with integrand
a^2/sqrt(t*(1-t)). Each omitted end contributes O(a^2*sqrt(delta)), since its ith
term is O(a^2/sqrt(n*(i+1))) after dividing by log n. Let delta decrease to zero.
Compare Táfula, Representation functions with prescribed rates of growth, Lemma 3.3. -/
def H1 : Prop := ∀ a : ℝ, 0 < a →
  let p : ℕ → ℝ := fun i ↦ a * Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))
  Antitone p ∧ (∀ i, 0 ≤ p i) ∧ ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ ↦ sumConv p p n / Real.log n) atTop (𝓝 c)

/-- Simultaneous finite rounding with bounded prefix-sum error and
sublogarithmic centered quadratic error. Prefixes may be chosen independently. -/
def H2 : Prop := ∃ a : ℝ, 0 < a ∧
  let p : ℕ → ℝ := fun i ↦ a * Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))
  ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
    ∀ N : ℕ, ∃ S : Finset ℕ, S ⊆ range (N + 1) ∧
      let d : ℕ → ℝ := fun i ↦ (if i ∈ S then 1 else 0) - p i
      ∀ n ≤ N, |∑ i ∈ range (n + 1), d i| ≤ D ∧
        |sumConv d d n / Real.log n| ≤ e n

/-- The prefix discrepancy condition alone is attainable at every finite horizon.
Take the positions where the floor of the cumulative fractional mass increases. -/
theorem round_prefix (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1)
    (N : ℕ) : ∃ S : Finset ℕ, S ⊆ range (N + 1) ∧ ∀ n ≤ N,
      |∑ i ∈ range (n + 1), ((if i ∈ S then (1 : ℝ) else 0) - p i)| ≤ 1 := by
  let F := fun n ↦ ∑ i ∈ range n, p i
  let b : ℕ → ℤ := fun n ↦ ⌊F n⌋
  let S := (range (N + 1)).filter fun i ↦ b i < b (i + 1)
  have hF (i : ℕ) : F (i + 1) = F i + p i := Finset.sum_range_succ _ _
  have hstep (i : ℕ) : b i ≤ b (i + 1) ∧ b (i + 1) ≤ b i + 1 := by
    dsimp only [b]
    rw [hF]
    constructor
    · exact Int.floor_mono (le_add_of_nonneg_right (hp i))
    · rw [← Int.floor_add_one]
      exact Int.floor_mono (add_le_add_right (hp' i) (F i))
  refine ⟨S, Finset.filter_subset _ _, fun n hn ↦ ?_⟩
  have hi' (i : ℕ) (hi : i ∈ range (n + 1)) :
      (if i ∈ S then (1 : ℝ) else 0) = (b (i + 1) : ℝ) - b i := by
    have hiN : i ∈ range (N + 1) := mem_range.mpr (by have := mem_range.mp hi; omega)
    have hmem : i ∈ S ↔ b i < b (i + 1) := by simp [S, hiN]
    have := hstep i
    by_cases hlt : b i < b (i + 1)
    · rw [if_pos (hmem.mpr hlt)]
      exact_mod_cast (show (1 : ℤ) = b (i + 1) - b i by omega)
    · rw [if_neg (fun hm ↦ hlt (hmem.mp hm))]
      exact_mod_cast (show (0 : ℤ) = b (i + 1) - b i by omega)
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl hi',
    Finset.sum_range_sub (fun i ↦ (b i : ℝ)) (n + 1)]
  have hb0 : b 0 = 0 := by simp [b, F]
  rw [hb0, Int.cast_zero, sub_zero]
  change |(⌊F (n + 1)⌋ : ℝ) - F (n + 1)| ≤ 1
  rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
  linarith [Int.lt_floor_add_one (F (n + 1))]

/-- Abel summation bounds the mixed convolution by twice the prefix discrepancy
times the largest weight. Only prefix sums up to the current index are used. -/
theorem mixed_bound (p d : ℕ → ℝ) (hp : Antitone p) (hpos : ∀ i, 0 ≤ p i)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ)
    (h : ∀ k ≤ n, |∑ i ∈ range (k + 1), d i| ≤ D) :
    |sumConv d p n| ≤ 2 * p 0 * D := by
  let w : ℕ → ℝ := fun k ↦ p (n - k)
  have hw : Monotone w := fun i j hij ↦ hp (Nat.sub_le_sub_left hij n)
  have hab : sumConv d p n = w n * (∑ i ∈ range (n + 1), d i) -
      ∑ i ∈ range n, (w (i + 1) - w i) * (∑ j ∈ range (i + 1), d j) := by
    rw [sumConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simpa only [Nat.add_sub_cancel, smul_eq_mul, mul_comm] using
      (Finset.sum_range_by_parts w d (n + 1))
  have he : |∑ i ∈ range n, (w (i + 1) - w i) * (∑ j ∈ range (i + 1), d j)| ≤
      (w n - w 0) * D := by
    calc
      _ ≤ ∑ i ∈ range n, |(w (i + 1) - w i) * (∑ j ∈ range (i + 1), d j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range n, (w (i + 1) - w i) * D := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hwi := sub_nonneg.mpr (hw (Nat.le_succ i))
        rw [abs_mul, abs_of_nonneg hwi]
        exact mul_le_mul_of_nonneg_left (h i (Finset.mem_range.mp hi).le) hwi
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub]
  have hwn : w n = p 0 := by simp [w]
  have hw0 : 0 ≤ w 0 := hpos _
  rw [hab]
  apply (abs_sub _ _).trans
  rw [abs_mul, hwn, abs_of_nonneg (hpos 0)]
  have hfirst := mul_le_mul_of_nonneg_left (h n le_rfl) (hpos 0)
  rw [hwn] at he
  nlinarith [mul_nonneg hw0 hD]

theorem conv_expand (x p : ℕ → ℝ) (n : ℕ) :
    sumConv x x n = sumConv p p n + 2 * sumConv (fun i ↦ x i - p i) p n +
      sumConv (fun i ↦ x i - p i) (fun i ↦ x i - p i) n := by
  let d := fun i ↦ x i - p i
  have hswap : sumConv p d n = sumConv d p n := by
    unfold sumConv
    simpa only [Prod.swap, mul_comm] using
      (Finset.Nat.sum_antidiagonal_swap (n := n) (f := fun q ↦ d q.1 * p q.2))
  change _ = _ + 2 * sumConv d p n + sumConv d d n
  rw [two_mul]
  calc
    _ = sumConv p p n + (sumConv p d n + sumConv d p n) + sumConv d d n := by
      simp only [sumConv, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [d]
      ring
    _ = _ := by rw [hswap]

theorem real_count (x : ℕ → Bool) (n : ℕ) :
    (sumRep {i | x i = true} n : ℝ) =
    sumConv (fun i ↦ if x i = true then (1 : ℝ) else 0)
      (fun i ↦ if x i = true then (1 : ℝ) else 0) n := by
  classical
  rw [sumRep_def, sumConv, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rcases ij with ⟨i,j⟩
  cases hi : x i <;> cases hj : x j <;> simp [hi, hj]

/-- A predicate depending on the count at each index can be imposed on an
infinite set if it can be imposed through every finite horizon. -/
theorem compact_counts (P : ℕ → ℕ → Prop)
    (h : ∀ N : ℕ, ∃ x : ℕ → Bool, ∀ n ≤ N, P n (sumRep {i | x i = true} n)) :
    ∃ A : Set ℕ, ∀ n, P n (sumRep A n) := by
  classical
  let K (N : ℕ) : Set (ℕ → Bool) := {x | ∀ n ≤ N, P n (sumRep {i | x i = true} n)}
  have hclosed (N : ℕ) : IsClosed (K N) := by
    apply isOpen_compl_iff.mp
    refine isOpen_pi_iff.mpr ?_
    intro x hx
    refine ⟨range (N + 1), fun i ↦ {x i}, fun i _ ↦ ⟨isOpen_discrete _, by simp⟩, ?_⟩
    intro y hy hyK
    apply hx
    intro n hn
    have heq (i : ℕ) (hi : i ≤ n) : y i = x i :=
      Set.mem_singleton_iff.mp (Set.mem_pi.mp hy i (mem_range.mpr (by omega)))
    have hrep : sumRep {i | x i = true} n = sumRep {i | y i = true} n := by
      simp only [sumRep_def]
      congr 1
      ext ij
      simp only [Finset.mem_filter]
      by_cases hij : ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n
      · have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        simp only [hij, true_and, Set.mem_ofPred_eq]
        rw [heq _ (by omega : ij.1 ≤ n), heq _ (by omega : ij.2 ≤ n)]
      · simp [hij]
    rw [hrep]
    exact hyK n hn
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun i y hy n hn ↦ hy n (by omega)) h (hclosed 0).isCompact hclosed
  exact ⟨{i | x i = true}, fun n ↦ Set.mem_iInter.mp hx n n le_rfl⟩

theorem main : H1 → H2 → type_of% @Erdos66.erdos_66 := by
  intro h₁ h₂
  obtain ⟨a, ha, D, hD, e, he, hfin⟩ := h₂
  let p : ℕ → ℝ := fun i ↦ a * Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))
  obtain ⟨hmono, hpos, c, hc, hlim⟩ := h₁ a ha
  let err := fun n : ℕ ↦ (4 * p 0 * D) / Real.log n + e n
  let P := fun (n r : ℕ) ↦ |(r : ℝ) / Real.log n - sumConv p p n / Real.log n| ≤ err n
  have hf (N : ℕ) : ∃ x : ℕ → Bool, ∀ n ≤ N, P n (sumRep {i | x i = true} n) := by
    obtain ⟨S, _, hS⟩ := hfin N
    let x : ℕ → Bool := fun i ↦ decide (i ∈ S)
    let f : ℕ → ℝ := fun i ↦ if x i = true then 1 else 0
    let d := fun i ↦ f i - p i
    have hcounts (n : ℕ) (hn : n ≤ N) :
        |∑ i ∈ range (n + 1), d i| ≤ D ∧ |sumConv d d n / Real.log n| ≤ e n := by
      simpa only [d, f, x, decide_eq_true_eq, p] using hS n hn
    refine ⟨x, fun n hn ↦ ?_⟩
    change |(sumRep _ n : ℝ) / _ - _| ≤ _
    rw [real_count]
    change |sumConv f f n / Real.log n - sumConv p p n / Real.log n| ≤ err n
    have hm := mixed_bound p d hmono hpos D hD n (fun k hk ↦ (hcounts k (hk.trans hn)).1)
    have hl : 0 ≤ Real.log (n : ℝ) := by
      cases n with
      | zero => simp
      | succ n => apply Real.log_nonneg; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have heq : sumConv f f n / Real.log n - sumConv p p n / Real.log n =
        2 * sumConv d p n / Real.log n + sumConv d d n / Real.log n := by
      rw [conv_expand f p]
      dsimp [d]
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add _ (hcounts n hn).2
    rw [abs_div, abs_of_nonneg hl, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply div_le_div_of_nonneg_right _ hl
    linarith only [hm]
  obtain ⟨A, hA⟩ := compact_counts P hf
  refine ⟨A, c, hc.ne', ?_⟩
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, zero_add] using
      ((tendsto_const_nhds (x := 4 * p 0 * D)).div_atTop hlog).add he
  have hdiff : Tendsto (fun n : ℕ ↦ (sumRep A n : ℝ) / Real.log n -
      sumConv p p n / Real.log n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ by simpa only [Real.norm_eq_abs] using hA n) herr
  change Tendsto (fun n : ℕ ↦ sumConv p p n / Real.log n) atTop (𝓝 c) at hlim
  simpa only [sub_add_cancel, zero_add] using hdiff.add hlim

end OMA.R_Erdos66_erdos_66_R1
