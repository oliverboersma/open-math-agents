import FormalConjectures.ErdosProblems.«145»
import Mathlib

/-! Consecutive differences of truncated quadratic moments recover the frequency
of every individual gap. A convergent cubic moment then controls the tails of
all strictly lower powers. -/
-- Credit: @marcusbuffett
namespace OMA.R_Erdos145_erdos_145_variants_le_three_R1
open Filter Finset Erdos145
open scoped Topology BigOperators

/-- Quadratic contributions of gaps below each fixed cutoff have a limiting density. -/
def H1 : Prop := ∀ K : ℕ, ∃ L : ℝ, Tendsto (fun x : ℝ => 1/x *
  ∑ n ∈ (A x).filter (fun n => s (n+1) - s n < K), ((s (n+1) - s n : ℕ) : ℝ)^2) atTop (𝓝 L)

/-- The endpoint cubic moment of the squarefree gaps has a limit. -/
def H2 : Prop := ∃ L : ℝ, Tendsto (fun x : ℝ => 1/x *
  ∑ n ∈ A x, ((s (n+1) - s n : ℕ) : ℝ)^3) atTop (𝓝 L)

lemma frequencies (trunc : H1) (k : ℕ) :
    ∃ d : ℝ, Tendsto (fun x : ℝ => 1/x * ((A x).filter fun n => s (n+1) - s n = k).card) atTop (𝓝 d) := by
  classical
  let g (n : ℕ) := s (n+1) - s n
  have hpos (n : ℕ) : 0 < g n := Nat.sub_pos_of_lt ((Nat.nth_strictMono Nat.squarefree_infinite) (Nat.lt_succ_self n))
  rcases k.eq_zero_or_pos with rfl|hk
  · refine ⟨0, ?_⟩
    have he (x : ℝ) : ((A x).filter fun n => g n = 0) = ∅ := by
      ext n
      simp [(hpos n).ne']
    change Tendsto (fun x : ℝ => 1/x * ((A x).filter fun n => g n = 0).card) _ _
    simp [he]
  obtain ⟨u,hu⟩ := trunc (k+1)
  obtain ⟨v,hv⟩ := trunc k
  refine ⟨(u-v)/(k:ℝ)^2, ((hu.sub hv).div_const ((k:ℝ)^2)).congr' ?_⟩
  filter_upwards with x
  let D := A x
  have split : (D.filter (fun n => g n < k)) ∪ (D.filter (fun n => g n = k)) =
      D.filter (fun n => g n < k+1) := by
    ext n
    by_cases hn : n ∈ D <;> simp [hn] <;> omega
  have dis : Disjoint (D.filter (fun n => g n < k)) (D.filter (fun n => g n = k)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    exact (mem_filter.mp hn).2.ne (mem_filter.mp hn').2
  have eqs : (∑ n ∈ D.filter (fun n => g n=k), (g n : ℝ)^2) =
      ((D.filter fun n => g n=k).card : ℝ)*(k:ℝ)^2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    exact fun n hn => by rw [(mem_filter.mp hn).2]
  change (1/x * (∑ n ∈ D.filter (fun n => g n < k+1), (g n:ℝ)^2) -
    1/x * (∑ n ∈ D.filter (fun n => g n < k), (g n:ℝ)^2))/(k:ℝ)^2 = _
  rw [← split, sum_union dis, eqs]
  change _ = 1/x * ((D.filter fun n => g n=k).card : ℝ)
  field_simp <;> ring

private lemma truncated (D : Finset ℕ) (g : ℕ → ℕ) (a : ℝ) (K : ℕ) :
    (∑ k ∈ range K, ((D.filter fun n => g n=k).card : ℝ) * (k:ℝ)^a) =
    ∑ n ∈ D.filter (fun n => g n < K), (g n:ℝ)^a := by
  calc
    _ = ∑ k ∈ range K, ∑ n ∈ D.filter (fun n => g n=k), (g n:ℝ)^a := by
      apply sum_congr rfl
      intro k _
      rw [← nsmul_eq_mul,← sum_const]
      apply sum_congr rfl
      intro n hn
      rw [(mem_filter.mp hn).2]
    _ = _ := by simpa only [mem_range] using sum_fiberwise_eq_sum_filter D (range K) g (fun n => (g n:ℝ)^a)

theorem main : H1 → H2 → type_of% @Erdos145.erdos_145.variants.le_three := by
  classical
  intro trunc endpoint a ha
  obtain ⟨L,hL⟩ := endpoint
  let g (n : ℕ) := s (n+1) - s n
  have hg (n : ℕ) : ((g n : ℕ) : ℝ) = (s (n+1) : ℝ) - s n :=
    Nat.cast_sub ((Nat.nth_strictMono Nat.squarefree_infinite).monotone (Nat.le_succ n))
  let f (x : ℝ) := (1/x) * ∑ n ∈ A x, (g n:ℝ)^a
  suffices h : ∃ β, Tendsto f atTop (𝓝 β) by simpa only [f,hg] using h
  by_cases h3 : a = 3
  · subst a
    exact ⟨L, by simpa [f, g] using hL⟩
  let q : ℝ := 3
  have aq : a < q := lt_of_le_of_ne ha.2 h3
  let B := L+1
  have hB : ∀ᶠ x : ℝ in atTop, (1/x) * ∑ n ∈ A x, (g n:ℝ)^q ≤ B := by
    have hh := hL.eventually_lt_const (show L < B by dsimp [B]; linarith)
    filter_upwards [hh] with x hx
    simpa [q, g] using hx.le
  choose d hd using frequencies trunc
  let T (K : ℕ) (x : ℝ) := ∑ k ∈ range K, (1/x * ((A x).filter fun n => g n=k).card) * (k:ℝ)^a
  have tend (K : ℕ) : Tendsto (T K) atTop (𝓝 (∑ k ∈ range K,d k*(k:ℝ)^a)) :=
    tendsto_finsetSum _ (fun k _ => (hd k).mul_const _)
  have terr (K : ℕ) (hK : 0 < K) : ∀ᶠ x : ℝ in atTop,
      |f x - T K x| ≤ B * (K:ℝ)^(a-q) := by
    filter_upwards [hB,eventually_gt_atTop (0:ℝ)] with x hb hx
    have te : T K x = (1/x) * ∑ n ∈ (A x).filter (fun n => g n < K), (g n:ℝ)^a := by
      unfold T
      rw [← truncated (A x) g a K,mul_sum]
      exact sum_congr rfl (fun k _ => by ring)
    let D := (A x).filter (fun n => ¬ g n < K)
    have split := sum_filter_add_sum_filter_not (A x) (fun n => g n < K) (fun n => (g n:ℝ)^a)
    have diff : f x - T K x = (1/x) * ∑ n ∈ D, (g n:ℝ)^a := by
      rw [te]
      unfold f
      dsimp [D]
      rw [← split,mul_add]
      ring
    rw [diff, abs_of_nonneg (by positivity)]
    have hKr : (0:ℝ) < K := by exact_mod_cast hK
    have sumBound : ∑ n ∈ D, (g n:ℝ)^a ≤ (∑ n ∈ A x, (g n:ℝ)^q) * (K:ℝ)^(a-q) := by
      rw [sum_mul]
      apply (sum_le_sum (g := fun n => (g n:ℝ)^q*(K:ℝ)^(a-q)) ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity))
      intro n hn
      have h : (K:ℝ) ≤ g n := by exact_mod_cast (le_of_not_gt (mem_filter.mp hn).2 : K ≤ g n)
      have pos := hKr.trans_le h
      calc
        (g n:ℝ)^a = (g n:ℝ)^q * (g n:ℝ)^(a-q) := by rw [← Real.rpow_add pos]; ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hKr h (by linarith)) (by positivity)
    change 1/x * (∑ n ∈ A x, (g n:ℝ)^q) ≤ B at hb
    calc
      _ ≤ (1/x) * ((∑ n ∈ A x, (g n:ℝ)^q) * (K:ℝ)^(a-q)) :=
        mul_le_mul_of_nonneg_left sumBound (by positivity)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hb (by positivity)
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have lim : Tendsto (fun K : ℕ => B*(K:ℝ)^(a-q)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_const_nhds (x := B)).mul
      ((tendsto_rpow_neg_atTop (by linarith : 0 < q-a)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨K,hK,hsmall⟩ := ((eventually_gt_atTop 0).and (lim.eventually_lt_const (by linarith : 0 < ε/4))).exists
  have cauch := Metric.cauchySeq_iff.mp (tend K).cauchySeq (ε/4) (by linarith)
  obtain ⟨N,hN⟩ := cauch
  obtain ⟨M,hM⟩ := eventually_atTop.mp (terr K hK)
  refine ⟨max N M,?_⟩
  intro x hx y hy
  have ht := hN x (le_trans (le_max_left _ _) hx) y (le_trans (le_max_left _ _) hy)
  have h₁ := hM x (le_trans (le_max_right _ _) hx)
  have h₂ := hM y (le_trans (le_max_right _ _) hy)
  rw [Real.dist_eq] at ht ⊢
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2,ht.1,ht.2]

end OMA.R_Erdos145_erdos_145_variants_le_three_R1
