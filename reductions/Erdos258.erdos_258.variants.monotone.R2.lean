import FormalConjectures.ErdosProblems.«258»
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OMA.R_Erdos258_erdos_258_variants_monotone_R2

/-- Fast case: `a n ≥ (log n)^2` eventually. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ), (∀ n, 2 ≤ a n) → Monotone a → Filter.Tendsto a Filter.atTop Filter.atTop →
    (∀ᶠ (n : ℕ) in Filter.atTop, (Real.log (n : ℝ)) ^ 2 ≤ (a n : ℝ)) →
    ∀ q : ℕ, 0 < q → ∃ N : ℕ,
      (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
        ∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ))) <
        (1 : ℝ) / q

/-- Slow case: `a n < (log n)^2` infinitely often. -/
def H2 : Prop :=
  ∀ (a : ℕ → ℕ), (∀ n, 2 ≤ a n) → Monotone a → Filter.Tendsto a Filter.atTop Filter.atTop →
    (∃ᶠ (n : ℕ) in Filter.atTop, (a n : ℝ) < (Real.log (n : ℝ)) ^ 2) →
    ∀ q : ℕ, 0 < q → ∃ N : ℕ,
      ((q : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
        ∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ))))
        ∉ Set.range (Int.cast : ℤ → ℝ)

/-! ## Framework: the target follows from the core tail lemma -/

lemma prod_pos (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 n, a i :=
  Finset.prod_pos fun i _ => by have := ha i; omega

lemma two_pow_le_prod (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    2 ^ n ≤ ∏ i ∈ Finset.Icc 1 n, a i := by
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  calc 2 ^ n = 2 ^ (Finset.Icc 1 n).card := by rw [hcard]
    _ = ∏ _i ∈ Finset.Icc 1 n, (2 : ℕ) := (Finset.prod_const 2).symm
    _ ≤ ∏ i ∈ Finset.Icc 1 n, a i :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le 2) (fun i _ => ha i)

lemma prod_split (a : ℕ → ℕ) {m N : ℕ} (h : m ≤ N) :
    (∏ i ∈ Finset.Icc 1 N, a i) =
      (∏ i ∈ Finset.Icc 1 m, a i) * (∏ i ∈ Finset.Icc (m + 1) N, a i) := by
  have hunion : Finset.Icc 1 N = Finset.Icc 1 m ∪ Finset.Icc (m + 1) N := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) N) := by
    rw [Finset.disjoint_left]
    intro i hi hi2
    simp only [Finset.mem_Icc] at hi hi2
    omega
  rw [hunion, Finset.prod_union hdisj]

lemma card_divisors_pos (n : ℕ) : 0 < (n + 1).divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩

lemma raw_pos (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 < (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ)) :=
  div_pos (by exact_mod_cast card_divisors_pos n)
    (by exact_mod_cast prod_pos a ha (n + 1))

lemma raw_nonneg (a : ℕ → ℕ) (n : ℕ) :
    0 ≤ (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ)) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma raw_le (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      ≤ ((n + 1 : ℕ) : ℝ) / ((2 : ℕ) ^ (n + 1) : ℝ) := by
  have hP : (0 : ℝ) < ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ) := by
    exact_mod_cast prod_pos a ha (n + 1)
  have h2 : (0 : ℝ) < ((2 : ℕ) ^ (n + 1) : ℝ) := by positivity
  have h1 : ((n + 1).divisors.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self (n + 1)
  have h2le : ((2 : ℕ) ^ (n + 1) : ℝ) ≤ ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ) := by
    exact_mod_cast two_pow_le_prod a ha (n + 1)
  have e1 : (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      ≤ (((n + 1 : ℕ) : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
  have e2 : (((n + 1 : ℕ) : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      ≤ (((n + 1 : ℕ) : ℝ) / ((2 : ℕ) ^ (n + 1) : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) h2 h2le
  exact e1.trans e2

lemma summable_raw (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) :
    Summable (fun n => (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * ((1 : ℝ) / 2) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2) (by norm_num)
  have h2 : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h3 : Summable (fun n : ℕ => ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ n) := by
    have h := h1.add h2
    simpa [add_mul, one_mul] using h
  have h4 : Summable (fun n : ℕ => ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (n + 1)) := by
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (n + 1))
        = fun n : ℕ => ((1 : ℝ) / 2) * (((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ n) := by
      funext n
      rw [pow_succ]
      ring
    rw [heq]
    exact h3.mul_left _
  have hle : ∀ (n : ℕ), (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      ≤ ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (n + 1) := by
    intro n
    have h := raw_le a ha n
    have hcast : ((n + 1 : ℕ) : ℝ) / ((2 : ℕ) ^ (n + 1) : ℝ)
        = ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (n + 1) := by
      rw [div_pow, one_pow, mul_one_div]
      push_cast
      ring_nf
    rw [hcast] at h
    exact h
  exact Summable.of_nonneg_of_le (fun n => raw_nonneg a n) hle h4

/-- For `n < N`, the summand equals an integer over `∏_{i≤N} a i`. -/
lemma raw_eq_div (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) {n N : ℕ} (h : n < N) :
    (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      = (Nat.cast ((n + 1).divisors.card * (∏ i ∈ Finset.Icc (n + 2) N, a i)) : ℝ)
          / ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) := by
  have hR : ((∏ i ∈ Finset.Icc (n + 2) N, a i : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.prod_pos fun i _ => by have := ha i; omega))
  rw [prod_split a (by omega : n + 1 ≤ N), Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hR]

lemma partial_sum (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) (N : ℕ) :
    ∃ M : ℕ, ∑ n ∈ Finset.range N,
        (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      = (M : ℝ) / ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) := by
  refine ⟨∑ n ∈ Finset.range N,
      (n + 1).divisors.card * (∏ i ∈ Finset.Icc (n + 2) N, a i), ?_⟩
  have hcongr : ∑ n ∈ Finset.range N,
      (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      = ∑ n ∈ Finset.range N,
          (Nat.cast ((n + 1).divisors.card * (∏ i ∈ Finset.Icc (n + 2) N, a i)) : ℝ)
            / ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun n hn => raw_eq_div a ha (Finset.mem_range.mp hn)
  rw [hcongr, ← Finset.sum_div, Nat.cast_sum]

/-- If the sum is `p / q`, the scaled tail `q * (∏_{i≤N} a i) * (tail)` is a positive integer. -/
lemma tail_int (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hS : ∑' n, (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      = (p : ℝ) / (q : ℝ)) (N : ℕ) :
    ∃ z : ℤ, 0 < z ∧ ((z : ℝ) = (q : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
      ∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ)))) := by
  have hsum := summable_raw a ha
  obtain ⟨M, hM⟩ := partial_sum a ha N
  have htail := hsum.sum_add_tsum_nat_add N
  have hTsum : Summable (fun k : ℕ =>
      (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ))) :=
    (summable_nat_add_iff N).mpr hsum
  have hTpos : 0 < ∑' k, (((k + N + 1).divisors.card : ℝ)
      / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ)) := by
    refine hTsum.tsum_pos (fun k => raw_nonneg a (k + N)) 0 ?_
    simpa using raw_pos a ha N
  have hST : (∑' k, (((k + N + 1).divisors.card : ℝ)
      / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ)))
      = ∑' n, (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
        - ∑ n ∈ Finset.range N,
            (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ)) := by
    linarith
  have hP : (0 : ℝ) < ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) := by exact_mod_cast prod_pos a ha N
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hkey : (q : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
      (∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ))))
      = (p : ℝ) * ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) - (q : ℝ) * (M : ℝ) := by
    rw [hST, hS, hM]
    field_simp [hq', hP.ne']
  have hpos : (0 : ℝ) < (q : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
      (∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ)))) := by
    exact mul_pos (by exact_mod_cast hq) (mul_pos hP hTpos)
  have hc : (((p * ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℤ) - (q : ℤ) * (M : ℤ) : ℤ) : ℝ))
      = (q : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
        (∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ)))) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    linarith
  refine ⟨p * ((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℤ) - (q : ℤ) * (M : ℤ), ?_, hc⟩
  refine (Int.cast_pos (R := ℝ)).mp ?_
  rw [hc]
  exact hpos

theorem main : H1 → H2 → type_of% @Erdos258.erdos_258.variants.monotone := by
  intro H1 H2 a ha hm ht
  unfold Irrational
  intro hmem
  obtain ⟨r, hr⟩ := hmem
  have hS : ∑' n, (((n + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))
      = (r.num : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def] at hr
    exact hr.symm
  by_cases hfast : ∀ᶠ (n : ℕ) in Filter.atTop, (Real.log (n : ℝ)) ^ 2 ≤ (a n : ℝ)
  · obtain ⟨N, hN⟩ := H1 a ha hm ht hfast r.den r.den_pos
    obtain ⟨z, hz, hc⟩ := tail_int a ha r.den_pos hS N
    have h1 : (1 : ℤ) ≤ z := by omega
    have h1' : (1 : ℝ) ≤ (r.den : ℝ) * (((∏ i ∈ Finset.Icc 1 N, a i : ℕ) : ℝ) *
        ∑' k, (((k + N + 1).divisors.card : ℝ) / ((∏ i ∈ Finset.Icc 1 (k + N + 1), a i : ℕ) : ℝ))) := by
      have h3 := (Int.cast_le (R := ℝ)).mpr h1
      rw [hc] at h3
      exact_mod_cast h3
    rw [lt_div_iff₀ (by exact_mod_cast r.den_pos)] at hN
    linarith
  · have hfast' := Filter.not_eventually.mp hfast
    have hslow : ∃ᶠ (n : ℕ) in Filter.atTop, (a n : ℝ) < (Real.log (n : ℝ)) ^ 2 :=
      hfast'.mono fun n hn => not_le.mp hn
    obtain ⟨x, hx⟩ := H2 a ha hm ht hslow r.den r.den_pos
    obtain ⟨z, hz, hc⟩ := tail_int a ha r.den_pos hS x
    exact hx ⟨z, hc⟩

end OMA.R_Erdos258_erdos_258_variants_monotone_R2
