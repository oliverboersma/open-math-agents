import FormalConjectures.ErdosProblems.«258»
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib

-- Combines the divisor-series reduction by @cosmaticdev with the short-interval and divisor-tail proofs by @marcusbuffett.

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

theorem OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H1 : OMA.R_Erdos258_erdos_258_variants_monotone_R2.H1 := DivisorTail258.fast

/-! Based on Erdős and Straus, Some number theoretic results, Section 2.
Large bases allow a small first digit and a geometrically weighted divisor
tail. Small bases give a long constant interval on which congruences make
the initial digits integral. In either case a strictly positive remainder
less than one rules out an integral scaled tail. -/
namespace OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1

open Finset Filter Real
open OMA.R_Erdos258_erdos_258_variants_monotone_R2
open scoped Topology

/-- A typical divisor digit and a controlled weighted tail suffice at the
intermediate scale. This estimate only concerns the divisor function. -/
def H1 : Prop := ∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, X ≤ N ∧
  let L := (log X)^(7/8:ℝ)
  let G := ∑' k : ℕ, ((k+(N+1)+1).divisors.card:ℝ)/(2:ℝ)^k
  (q:ℝ)*((N+1).divisors.card+G/L) < L

/-- A congruence window in a long integer interval. Each initial divisor
digit is divisible by the appropriate power of the prescribed base. -/
def H2 : Prop := ∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∀ t : ℕ, 2 ≤ t →
  (t:ℝ) ≤ (log X)^(7/8:ℝ) → ∀ I : Finset ℕ, I ⊆ Icc 1 X →
  (∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I) → X/⌊(log X)^(7/8:ℝ)⌋₊ ≤ I.card →
  ∃ N k : ℕ, Icc (N+1) (N+k) ⊆ I ∧ (∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧
    (q:ℝ)*(∑' i : ℕ, ((i+(N+k)+1).divisors.card:ℝ)/(2:ℝ)^i) < (t:ℝ)^k

lemma prepare (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) :
    let T := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ) *
      ∑' k, ((k+n+1).divisors.card:ℝ)/((∏ i ∈ Icc 1 (k+n+1), a i:ℕ):ℝ)
    let G := fun n : ℕ => ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
    (∀ n, 0 < T n) ∧ (∀ n, a (n+1)*T n = (n+1).divisors.card + T (n+1)) ∧
    ∀ n, T n*a (n+1) ≤ G n := by
  intro T G
  let pref := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ)
  let raw := fun n : ℕ => ((n+1).divisors.card:ℝ)/pref (n+1)
  have ps (n : ℕ) : 0 < pref n := by dsimp [pref]; exact_mod_cast prod_pos a ha n
  have sm (n : ℕ) : Summable (fun k => raw (k+n)) := (summable_nat_add_iff n).mpr (summable_raw a ha)
  have step (n : ℕ) : pref (n+1) = pref n*a (n+1) := by
    dsimp [pref]
    rw [prod_split a (by omega : n ≤ n+1),Icc_self,prod_singleton,Nat.cast_mul]
  refine ⟨?_,?_,?_⟩
  · intro n
    exact mul_pos (ps n) ((sm n).tsum_pos (fun k => raw_nonneg a _) 0 (raw_pos a ha _))
  · intro n
    have eq := (sm n).tsum_eq_zero_add
    change (∑' k,raw (k+n)) = raw (0+n)+∑' k : ℕ, raw (k+1+n) at eq
    simp only [zero_add,Nat.add_right_comm _ 1 n] at eq
    change a (n+1)*(pref n * ∑' k,raw (k+n)) = _ + pref (n+1)*∑' k,raw (k+(n+1))
    rw [eq,mul_left_comm,←mul_assoc,←step,mul_add]
    simp only [Nat.add_assoc,raw]
    field_simp [(ps (n+1)).ne']
  · intro n
    have gsum : Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) := by
      have h₁ : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2) (by norm_num)
      have h₂ := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_left ((n:ℝ)+1)
      apply Summable.of_nonneg_of_le (fun k => by positivity) _ (h₁.add h₂)
      intro k
      change _ ≤ (k:ℝ)*(1/2:ℝ)^k+((n:ℝ)+1)*(1/2:ℝ)^k
      rw [←add_mul,div_pow,one_pow,mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
      push_cast at hh
      linarith
    change (pref n*(∑' k,raw (k+n)))*a (n+1) ≤ _
    rw [mul_right_comm,←step,←tsum_mul_left]
    apply ((sm n).mul_left _).tsum_le_tsum _ gsum
    intro k
    let P := ∏ i ∈ Icc (n+1+1) (k+n+1), a i
    have fact : pref (k+n+1) = pref (n+1)*P := by
      dsimp [pref,P]; rw [prod_split a (by omega : n+1 ≤ k+n+1),Nat.cast_mul]
    have lower : 2^k ≤ P := calc
      _ = 2^(Icc (n+1+1) (k+n+1)).card := by rw [Nat.card_Icc]; congr 1; omega
      _ = ∏ _i ∈ Icc (n+1+1) (k+n+1),(2:ℕ) := (prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod (by simp) (fun i _ => ha i)
    change pref (n+1)*((k+n+1).divisors.card/pref (k+n+1)) ≤ _
    rw [fact,←mul_div_assoc,mul_div_mul_left _ _ (ps _).ne']
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast lower)

private lemma integral_prefix (a : ℕ → ℕ) (T : ℕ → ℝ)
    (step : ∀ n, a (n+1)*T n = (n+1).divisors.card + T (n+1))
    (t N k : ℕ) (ht : 0 < t) (bases : ∀ j ∈ Icc 1 k, a (N+j) = t)
    (digits : ∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) :
    ∃ b : ℕ, T N = b+T (N+k)/(t:ℝ)^k := by
  induction k with
  | zero => exact ⟨0,by simp⟩
  | succ k ih =>
    have sub : Icc 1 k ⊆ Icc 1 (k+1) := fun j hj => mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans (by omega)⟩
    obtain ⟨b,hb⟩ := ih (fun j hj => bases j (sub hj)) (fun j hj => digits j (sub hj))
    have endmem : k+1 ∈ Icc 1 (k+1) := mem_Icc.mpr ⟨by omega,le_rfl⟩
    obtain ⟨c,hc⟩ := digits (k+1) endmem
    have eq := step (N+k)
    rw [Nat.add_assoc,bases _ endmem,hc,Nat.cast_mul,Nat.cast_pow] at eq
    refine ⟨b+c,?_⟩
    rw [hb,Nat.cast_add]
    have tp : (0:ℝ) < t := by exact_mod_cast ht
    rw [pow_succ] at eq ⊢
    have divEq : T (N+k)/(t:ℝ)^k = c + T (N+(k+1))/((t:ℝ)^k*t) := by
      field_simp [tp.ne']
      linear_combination eq
    rw [divEq]
    ring

theorem main : H1 → H2 → OMA.R_Erdos258_erdos_258_variants_monotone_R2.H2 := by
  intro typical window a ha mono _ _ q hq
  let T := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ) *
      ∑' k, ((k+n+1).divisors.card:ℝ)/((∏ i ∈ Icc 1 (k+n+1), a i:ℕ):ℝ)
  let G := fun n : ℕ => ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
  let L := fun X : ℕ => (log X)^(7/8:ℝ)
  obtain ⟨pos,step,bound⟩ := prepare a ha
  change ∀ n, 0 < T n at pos
  change ∀ n, (a (n+1):ℝ)*T n = (n+1).divisors.card + T (n+1) at step
  change ∀ n, T n*a (n+1) ≤ G n at bound
  have qp : (0:ℝ)<q := by exact_mod_cast hq
  have ap (n : ℕ) : 1 ≤ (a n:ℝ) := by exact_mod_cast (show 1 ≤ a n by have := ha n; omega)
  by_cases fast : ∀ᶠ X : ℕ in atTop, L X ≤ a X
  · obtain ⟨X,fx,minX,N,XN,good⟩ := (fast.and ((eventually_gt_atTop (1:ℕ)).and (typical q hq))).exists
    change (q:ℝ)*((N+1).divisors.card+G (N+1)/L X)<L X at good
    have Lp : 0 < L X := Real.rpow_pos_of_pos (log_pos (by exact_mod_cast minX)) _
    have hbase (k : ℕ) (hk : X ≤ k) : L X ≤ a k := fx.trans (by exact_mod_cast mono hk)
    have hT : T (N+1) ≤ G (N+1)/L X := (le_div_iff₀ Lp).mpr <|
      (mul_le_mul_of_nonneg_left (hbase _ (by omega)) (pos _).le).trans (bound _)
    have lt : (q:ℝ)*T N < 1 := by
      have r := step N
      have H : (q:ℝ)*((a (N+1):ℝ)*T N) < a (N+1) := by
        rw [r]; apply lt_of_le_of_lt _ (good.trans_le (hbase _ (by omega)))
        exact mul_le_mul_of_nonneg_left (by linarith only [hT]) qp.le
      have posA : (0:ℝ) < a (N+1) := by linarith [ap (N+1)]
      apply (mul_lt_mul_iff_right₀ posA).mp
      linarith only [H]
    refine ⟨N,?_⟩
    rintro ⟨z,hz⟩
    change (z:ℝ) = q*T N at hz
    have zpos : (0:ℤ) < z := by exact_mod_cast (show (0:ℝ)<z by rw [hz]; exact mul_pos qp (pos N))
    have zsmall : z < (1:ℤ) := by exact_mod_cast (show (z:ℝ)<1 by rw [hz]; exact lt)
    omega
  · have often : ∃ᶠ X : ℕ in atTop, a X < L X := by
      simpa only [Filter.Frequently,not_lt] using fast
    obtain ⟨X,small,windows,Xlarge⟩ := (often.and_eventually ((window q hq).and
      ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (Real.exp 1)))).exists
    let h := ⌊L X⌋₊
    have Lp : 0 ≤ L X := (Nat.cast_nonneg _).trans small.le
    have ax : a X ≤ h := (Nat.le_floor_iff Lp).mpr small.le
    have hh : 1 ≤ h := by have := ha X; omega
    have map (i : ℕ) (hi : i ∈ Icc 1 X) : a i ∈ Icc 1 h := mem_Icc.mpr
      ⟨by have := ha i; omega,(mono (mem_Icc.mp hi).2).trans ax⟩
    have num : (Icc 1 h).card*(X/h) ≤ (Icc 1 X).card := by
      simp only [Nat.card_Icc]; simpa using Nat.mul_div_le X h
    obtain ⟨t,ht,hcount⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (f := a) map
      (Finset.nonempty_Icc.mpr hh) num
    let I := (Icc 1 X).filter (fun n => a n=t)
    have Iin : I ⊆ Icc 1 X := filter_subset _ _
    have Xr : 0 < (X:ℝ) := (Real.exp_pos 1).trans Xlarge
    have lg : 1 ≤ log (X:ℝ) := (Real.le_log_iff_exp_le Xr).mpr Xlarge.le
    have Lbound : L X ≤ X := calc
      _ ≤ (log (X:ℝ))^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le lg (by norm_num)
      _ ≤ _ := by rw [Real.rpow_one]; linarith [Real.log_le_sub_one_of_pos Xr]
    have hX : h ≤ X := by exact_mod_cast ((Nat.floor_le Lp).trans Lbound : ((h:ℕ):ℝ)≤(X:ℝ))
    have has : I.Nonempty := Finset.card_pos.mp ((Nat.div_pos hX (by omega)).trans_le hcount)
    obtain ⟨i,hi⟩ := has
    have t2 : 2 ≤ t := (mem_filter.mp hi).2 ▸ ha i
    have convexI (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) : Icc i j ⊆ I := by
      intro k hk
      obtain ⟨ir,hit⟩ := mem_filter.mp hi
      obtain ⟨jr,hjt⟩ := mem_filter.mp hj
      obtain ⟨ik,kj⟩ := mem_Icc.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ir).1.trans ik,kj.trans (mem_Icc.mp jr).2⟩,
        le_antisymm ((mono kj).trans_eq hjt) (hit.symm.le.trans (mono ik))⟩
    obtain ⟨N,k,rangeI,digits,cost⟩ := windows t t2 ((Nat.le_floor_iff Lp).mp (mem_Icc.mp ht).2)
      I Iin convexI hcount
    change (q:ℝ)*G (N+k) < (t:ℝ)^k at cost
    have base (j : ℕ) (hj : j ∈ Icc 1 k) : a (N+j)=t :=
      (mem_filter.mp (rangeI (mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega,
        Nat.add_le_add_left (mem_Icc.mp hj).2 N⟩))).2
    obtain ⟨b,eq⟩ := integral_prefix a T step t N k (by omega) base digits
    have qt : (q:ℝ)*T (N+k) < (t:ℝ)^k := by
      apply lt_of_le_of_lt _ cost
      apply mul_le_mul_of_nonneg_left _ qp.le
      have leProd : T (N+k) ≤ T (N+k)*a (N+k+1) := by
        simpa using (mul_le_mul_of_nonneg_left (ap (N+k+1)) (pos (N+k)).le)
      exact leProd.trans (bound _)
    have tk : 0 < (t:ℝ)^k := by
      have ht : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
      positivity
    refine ⟨N,?_⟩
    rintro ⟨z,hz⟩
    change (z:ℝ) = q*T N at hz
    rw [eq,mul_add,←mul_div_assoc] at hz
    have l : 0 < (q:ℝ)*T (N+k)/(t:ℝ)^k := div_pos (mul_pos qp (pos _)) tk
    have u : (q:ℝ)*T (N+k)/(t:ℝ)^k < 1 := (div_lt_one tk).mpr qt
    have z₁ : (q:ℤ)*b < z := by exact_mod_cast (by linarith only [hz,l] : (q:ℝ)*b < z)
    have z₂ : z < (q:ℤ)*b+1 := by exact_mod_cast (by linarith only [hz,u] : (z:ℝ) < q*b+1)
    omega

end OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1

/-! The upper normal order of the prime-factor count is adapted from
@marcusbuffett's merged Erdős 1100 proof, d11bab2e5cca11149ef46efd98a8acd1f654c894,
including the first Mertens estimate credited to @senamakel. The harmonic
divisor-sum bound follows the Erdős 258 fast-base proof by @marcusbuffett.
Combining the density estimate with a first-moment bound for the shifted
divisor tail gives simultaneous control at an index in every dyadic interval. -/
section
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
end Mass377
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev mass (P : Finset ℕ) := ∑ p ∈ P, (1:ℝ)/p
def cnt (P : Finset ℕ) (n : ℕ) := (P.filter (· ∣ n)).card
def hit (p n : ℕ) : ℝ := if p ∣ n then 1 else 0
lemma sum_hit (N p : ℕ) : ∑ n ∈ Ioc 0 N, hit p n = (N/p:ℕ) := by
  simp [hit, ← Nat.Ioc_filter_dvd_card_eq_div]
lemma cnt_sum (P : Finset ℕ) (n : ℕ) : (cnt P n : ℝ) = ∑ p ∈ P, hit p n := by
  simp [cnt,hit]
lemma first (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    N*mass P - P.card ≤ ∑ n ∈ Ioc 0 N, (cnt P n:ℝ) := by
  simp_rw [cnt_sum]
  rw [sum_comm]
  simp_rw [sum_hit]
  calc _ = ∑ p ∈ P, ((N:ℝ)/p-1) := by simp [mass,mul_sum,sum_sub_distrib,div_eq_mul_inv]
       _ ≤ _ := sum_le_sum fun p hp => OMALib.Mertens.real_div_sub_one_le_nat_div N p (hP p hp).pos

lemma pair_sum (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Ioc 0 N, hit p n * hit q n ≤
      (N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0) := by
  by_cases he : p=q
  · subst q
    simp only [if_pos rfl]
    have h : ∀ n, hit p n * hit p n = hit p n := fun n => by unfold hit; split_ifs <;> norm_num
    simp_rw [h,sum_hit]
    exact (Nat.cast_div_le (α:=ℝ)).trans (le_add_of_nonneg_left (by positivity))
  · have hc := (Nat.coprime_primes hp hq).mpr he
    have h (n) : hit p n * hit q n = hit (p*q) n := by
      have eq : p*q ∣ n ↔ p∣n ∧ q∣n := ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩, fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      simp only [hit,eq]
      split_ifs <;> simp_all
    simp_rw [h,sum_hit,if_neg he,add_zero]
    calc _ ≤ (N:ℝ)/(p*q:ℕ) := Nat.cast_div_le
         _ = _ := by push_cast; ring

lemma second (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ n ∈ Ioc 0 N, (cnt P n:ℝ)^2 ≤ (N:ℝ) * (mass P)^2 + N * mass P := by
  have eq (n) : (cnt P n:ℝ)^2 = ∑ p ∈ P, ∑ q ∈ P, hit p n * hit q n := by
    rw [cnt_sum,pow_two,sum_mul]
    exact sum_congr rfl fun p _ => mul_sum ..
  simp_rw [eq]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc 0 N) (t := P)]
  calc _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0)) :=
            sum_le_sum fun p hp => sum_le_sum fun q hq => pair_sum N p q (hP p hp) (hP q hq)
       _ = _ := by
         simp only [sum_add_distrib, ←mul_sum, ←sum_mul, sum_ite_eq, mass]
         simp only [sum_ite_mem, inter_self]
         simp [mul_sum, sum_mul, pow_two, mul_assoc, div_eq_mul_inv]

lemma variance (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) :
    ∑ n ∈ Ioc 0 N, ((cnt P n:ℝ)-mass P)^2 ≤ 3*N*mass P := by
  have hm : 0 ≤ mass P := sum_nonneg fun _ _ => by positivity
  have e (n) : ((cnt P n:ℝ)-mass P)^2 =
      (cnt P n:ℝ)^2 - 2*mass P*(cnt P n:ℝ) + (mass P)^2 := by ring
  simp_rw [e]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum]
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hcr : (P.card:ℝ) ≤ N := by exact_mod_cast hc
  nlinarith only [first P N hP,second P N hP,
    mul_nonneg hm (sub_nonneg.mpr (first P N hP)), mul_nonneg hm (sub_nonneg.mpr hcr)]

lemma cheb (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    (((Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)).card:ℝ)*t^2 ≤ 3*N*mass P := by
  classical
  let E := (Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)
  calc (E.card:ℝ)*t^2 = ∑ _n ∈ E, t^2 := by simp
         _ ≤ ∑ n ∈ E, ((cnt P n:ℝ)-mass P)^2 := sum_le_sum fun n hn => by
           have h := (mem_filter.mp hn).2
           simpa using (sq_le_sq' (by linarith [abs_nonneg ((cnt P n:ℝ)-mass P)] : -|(cnt P n:ℝ)-mass P| ≤ t) h)
         _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans (variance P N hP hc)
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
lemma bad_count (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N)
    (δ t : ℝ) (ht : 0 < t) (hd : 3*mass P ≤ δ*t^2) :
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧
      ∀ n ∈ Ioc 0 N, n ∉ E → |(cnt P n:ℝ)-mass P| < t := by
  classical
  let E := (Ioc 0 N).filter fun n => t ≤ |(cnt P n:ℝ)-mass P|
  refine ⟨E, (le_of_mul_le_mul_right ?_ (sq_pos_of_pos ht)), fun n hn he => ?_⟩
  · calc (E.card:ℝ)*t^2 ≤ 3*N*mass P := cheb P N hP hc t ht.le
         _ ≤ (δ*N)*t^2 := by nlinarith only [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)]
  · exact lt_of_not_ge (fun h => he (mem_filter.mpr ⟨hn,h⟩))

lemma primes_card (N : ℕ) : (Nat.primesLE N).card ≤ N := by
  calc _ ≤ (Ioc 0 N).card := card_le_card fun p h => by
          obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp h
          exact mem_Ioc.mpr ⟨hp.pos,hle⟩
       _ = _ := by simp

noncomputable abbrev w (N : ℕ) := log (log N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop

end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
lemma square_tail (δ : ℝ) (hδ : 0<δ) : ∃ A : ℕ, ∀ N : ℕ,
    (∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2) ≤ δ := by
  have hs : Summable (fun a : ℕ => (1:ℝ)/(a:ℝ)^2) := by
    simpa only [one_div] using (Real.summable_nat_pow_inv.mpr (by decide : 1<2))
  let s := ∑' a : ℕ, (1:ℝ)/(a:ℝ)^2
  obtain ⟨A,hA⟩ := (hs.hasSum.tendsto_sum_nat.eventually_const_lt (show s-δ < s by linarith)).exists
  refine ⟨A,fun N => ?_⟩
  have hd : Disjoint (range A) (Icc A N) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (mem_range.mp hx).not_ge (mem_Icc.mp hy).1
  have h := hs.sum_le_tsum (range A ∪ Icc A N) (fun a _ => by positivity)
  rw [sum_union hd] at h
  change _ ≤ s at h
  linarith

lemma square_mult (N A : ℕ) :
    ((((Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)).card):ℝ) ≤
      N * ∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2 := by
  calc _ ≤ ((∑ a ∈ Icc A N, ((Ioc 0 N).filter (a^2 ∣ ·)).card:ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ a ∈ Icc A N, ((N/a^2:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ a ∈ Icc A N, (N:ℝ)/(a^2:ℕ) := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299

lemma small (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n : ℕ, n ∉ E → 0<n ∧ (N:ℝ)^(1-1/w N) ≤ n := by
  have hg := (tendsto_exp_div_pow_atTop 1).comp wtop
  filter_upwards [hg.eventually_gt_atTop (-log δ), Mass377.logTop.eventually_gt_atTop 0,
    eventually_ge_atTop 1, (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/δ)] with N hh hl hN hbig
  change -log δ < exp (w N)/(w N)^1 at hh
  rw [pow_one, show exp (w N) = log N from exp_log hl] at hh
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have h1 := (div_le_iff₀ hδ).mp hbig
  let E := range (⌊δ*N⌋₊+1)
  refine ⟨E,?_,fun n hn => ?_⟩
  · simp only [E,card_range,Nat.cast_add,Nat.cast_one]
    have hf := Nat.floor_le (mul_nonneg hδ.le hNr.le)
    nlinarith
  · have hfn : ⌊δ*N⌋₊ < n := by simpa [E, Nat.succ_le_iff] using hn
    have hsmall : (N:ℝ)^(1-1/w N) ≤ δ*N := by
      rw [Real.rpow_def_of_pos hNr, show log (N:ℝ)*(1-1/w N) = log N + -(log N/w N) by ring,exp_add,exp_log hNr]
      have he : exp (-(log N/w N)) ≤ δ := by rw [←Real.exp_log hδ]; exact exp_le_exp.mpr (by linarith)
      linarith only [mul_le_mul_of_nonneg_left he hNr.le]
    exact ⟨by omega,hsmall.trans (Nat.lt_of_floor_lt hfn).le⟩

end Regular299
end

section
open Finset Real Filter ArithmeticFunction
open scoped BigOperators Topology
open Regular299
namespace Omega1100

lemma distinct_upper (η δ : ℝ) (hη : 0<η) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop,
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E →
      (n.primeFactors.card:ℝ) ≤ (1+η)*w N := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  let t := η/2
  have ht : 0<t := by dsimp [t]; positivity
  filter_upwards [hb.eventually_lt_const (show b < b+1 by linarith),
    wtop.eventually_gt_atTop (|b|+1),wtop.eventually_gt_atTop ((|b|+1)/t),
    wtop.eventually_gt_atTop (6/(δ*t^2))] with N hu hw hw₁ hw₂
  let P := Nat.primesLE N
  change mass P - w N < b+1 at hu
  have hm : mass P ≤ 2*w N := by linarith [le_abs_self b]
  have hw0 : 0<w N := by linarith [abs_nonneg b]
  have hh := (div_lt_iff₀ (by positivity : 0<δ*t^2)).mp hw₂
  have h1 := (div_lt_iff₀ ht).mp hw₁
  obtain ⟨E,hE,he⟩ := bad_count P N (fun p hp => (Nat.mem_primesLE.mp hp).2) (primes_card N)
    δ (t*w N) (by positivity) (by nlinarith only [hm,mul_lt_mul_of_pos_right hh hw0])
  refine ⟨E,hE,fun n hn hx => ?_⟩
  have hn' := mem_Ioc.mp hn
  have eq : P.filter (· ∣ n) = n.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE,Nat.mem_primeFactors,P]
    exact ⟨fun h => ⟨h.1.2,h.2,hn'.1.ne'⟩,fun h => ⟨⟨(Nat.le_of_dvd hn'.1 h.2.1).trans hn'.2,h.1⟩,h.2.1⟩⟩
  have h := (abs_lt.mp (he n hn hx)).2
  simp only [cnt,eq] at h
  dsimp [t] at h h1
  linarith [le_abs_self b]

lemma bounded_excess (δ : ℝ) (hδ : 0<δ) : ∃ M : ℕ, ∀ N : ℕ, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E → cardFactors n ≤ n.primeFactors.card + M := by
  classical
  obtain ⟨A,hA⟩ := square_tail δ hδ
  let M := ∑ b ∈ range A, 2 * cardFactors b
  refine ⟨M,fun N => ?_⟩
  let E := (Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)
  have hc := (square_mult N A).trans (mul_le_mul_of_nonneg_left (hA N) (Nat.cast_nonneg N))
  refine ⟨E,by simpa [E,mul_comm] using hc,fun n hn he => ?_⟩
  obtain ⟨hn0,hnN⟩ := mem_Ioc.mp hn
  obtain ⟨a,b,ha,hb,eq,sf⟩ := Nat.sq_mul_squarefree_of_pos hn0
  have dvd : b^2 ∣ n := ⟨a,eq.symm⟩
  have bd : b ≤ N := (Nat.le_of_dvd hn0 ((dvd_pow_self b (by decide : 2≠0)).trans dvd)).trans hnN
  have hbA : b < A := lt_of_not_ge (fun h => he (mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨h,bd⟩, mem_filter.mpr ⟨hn,dvd⟩⟩))
  have hm : 2*cardFactors b ≤ M := single_le_sum (f:=fun j => 2*cardFactors j) (fun _ _ => Nat.zero_le _) (mem_range.mpr hbA)
  have eq1 : cardFactors n = 2*cardFactors b + cardFactors a := by
    rw [←eq,cardFactors_mul (pow_ne_zero _ hb.ne') ha.ne',cardFactors_pow]
  have eq2 : cardFactors a = a.primeFactors.card := by
    rw [cardFactors_apply,←Nat.toFinset_factors]
    exact (List.toFinset_card_of_nodup sf.nodup_primeFactorsList).symm
  have hsub := card_le_card (Nat.primeFactors_mono (show a∣n from eq ▸ dvd_mul_left a (b^2)) hn0.ne')
  omega

lemma bad_count_final (η ε : ℝ) (hη : 0<η) (hε : 0<ε) : ∀ᶠ N : ℕ in atTop,
    (((range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n)).card:ℝ) ≤ ε*N := by
  classical
  let δ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨M,hM⟩ := bounded_excess δ hδ
  filter_upwards [distinct_upper (η/2) δ (by positivity) hδ,small δ hδ,
    wtop.eventually_gt_atTop (2*((M:ℝ)+(1+η)*Real.log 2)/η),
    wtop.eventually_gt_atTop 2, Mass377.logTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with N hd hs hslack hw hl hN
  obtain ⟨E,hE,ee⟩ := hd
  obtain ⟨S,hS,ss⟩ := hs
  obtain ⟨T,hT,tt⟩ := hM N
  have sub : (range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n) ⊆ E∪S∪T := by
    intro n hn
    obtain ⟨hnN,hbad⟩ := mem_filter.mp hn
    by_contra h
    simp only [mem_union,not_or] at h
    obtain ⟨hn0,hscale⟩ := ss n h.1.2
    have hi : n ∈ Ioc 0 N := mem_Ioc.mpr ⟨hn0,(mem_range.mp hnN).le⟩
    have ho := ee n hi h.1.1
    have ht : (cardFactors n:ℝ) ≤ n.primeFactors.card + (M:ℝ) := by exact_mod_cast tt n hi h.2
    have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    have hlog := log_le_log (rpow_pos_of_pos hNr _) hscale
    rw [log_rpow hNr] at hlog
    have hw' : 1/w N ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hw.le
    have hlow : log (N:ℝ)/2 ≤ Real.log n := by nlinarith only [hlog,mul_le_mul_of_nonneg_right hw' hl.le]
    have hlow2 := log_le_log (div_pos hl (by norm_num : (0:ℝ)<2)) hlow
    rw [log_div hl.ne' (by norm_num : (2:ℝ)≠0)] at hlow2
    change w N - Real.log 2 ≤ w n at hlow2
    have hsl := (div_lt_iff₀ hη).mp hslack
    apply hbad
    nlinarith only [ht,ho,hsl,mul_le_mul_of_nonneg_left hlow2 (by linarith : 0≤1+η)]
  have h1 : (((range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n)).card:ℝ) ≤ (E∪S∪T).card := by exact_mod_cast card_le_card sub
  have upper (A B : Finset ℕ) : ((A∪B).card:ℝ) ≤ A.card + B.card := by exact_mod_cast card_union_le A B
  dsimp [δ] at hE hS hT
  linarith [upper E S,upper (E∪S) T]
end Omega1100
end

namespace TypicalDivisor258
open Finset Filter Real
open ArithmeticFunction (cardFactors cardFactors_eq_sum_factorization)
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

noncomputable def G (n : ℕ) : ℝ := ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
noncomputable def b (k : ℕ) : ℝ := ((k:ℝ)+1)*((1:ℝ)/2)^k

lemma bsum : Summable b := by
  have h : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 1 (r:=1/2) (by norm_num)
  change Summable (fun k : ℕ => b k)
  simpa [b,add_mul] using h.add (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))

lemma dom (n k : ℕ) : ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k ≤ ((n:ℝ)+1)*b k := by
  have h : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
  push_cast at h
  unfold b
  rw [div_pow,one_pow,←mul_assoc,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [h,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg k : (0:ℝ)≤k)]

lemma gs (n : ℕ) : Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (dom n) (bsum.mul_left _)

lemma gpos (n : ℕ) : 0 ≤ G n := tsum_nonneg fun k => by positivity

lemma recur (n : ℕ) : G n = (n+1).divisors.card + G (n+1)/2 := by
  rw [G,(gs n).tsum_eq_zero_add]
  simp only [zero_add,pow_zero,div_one]
  congr 1
  rw [G,←tsum_div_const]
  apply tsum_congr
  intro k
  rw [show k+1+n+1 = k+(n+1)+1 by omega,pow_succ]
  ring

lemma mean : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 1≤n → (∑ j ∈ range n,G j) ≤ C*n*(1+log n) := by
  let B := ∑' k, b k
  have b0 : 0 ≤ B := tsum_nonneg fun k => by dsimp [b]; positivity
  refine ⟨2+2*B,by linarith,?_⟩
  intro n hn
  have cap : G n ≤ ((n:ℝ)+1)*B := by
    change _ ≤ _*∑' k,b k
    rw [←tsum_mul_left]
    exact (gs n).tsum_le_tsum (dom n) (bsum.mul_left _)
  have sum := Finset.sum_congr (s₁:=range n) (s₂:=range n) rfl
    (show ∀ i ∈ range n,G i=2*((i+1).divisors.card:ℝ)+(G (i+1)-G i) by
      intro i _; linarith only [recur i])
  rw [sum_add_distrib,sum_range_sub,←mul_sum] at sum
  have E : (range n).image (fun i : ℕ => i+1) = Ioc 0 n := by
    ext j
    simp only [mem_image,mem_range,mem_Ioc]
    exact ⟨fun ⟨i,h,e⟩ => by omega,fun h => ⟨j-1,by omega,by omega⟩⟩
  have ds := divisor_sum n
  rw [←E,sum_image (by intro i _ j _ e; exact Nat.add_right_cancel e)] at ds
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have lp := log_nonneg n1
  nlinarith only [sum,cap,ds,gpos 0,mul_nonneg (sub_nonneg.mpr n1) b0,
    mul_nonneg (mul_nonneg b0 (Nat.cast_nonneg n)) lp]

lemma divpow (n : ℕ) (hn : n ≠ 0) : n.divisors.card ≤ 2^(cardFactors n) := by
  rw [Nat.card_divisors hn, cardFactors_eq_sum_factorization,Finsupp.sum,Nat.support_factorization,
    ←Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (by simp) fun i _ => (n.factorization i).lt_two_pow_self

lemma digit (n : ℕ) (lp : 1 ≤ log (n:ℝ))
    (h : (cardFactors n:ℝ) ≤ (1+1/20:ℝ)*log (log n)) :
    (n.divisors.card:ℝ) ≤ (log n)^(3/4:ℝ) := by
  have np : n≠0 := by rintro rfl; norm_num at lp
  have bound : (n.divisors.card:ℝ) ≤ (2:ℝ)^cardFactors n := by exact_mod_cast divpow n np
  apply bound.trans
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos (zero_lt_one.trans_le lp)]
  apply exp_le_exp.mpr
  have ll := log_nonneg lp
  have h2 : log 2 ≤ 7/10 := by linarith [log_two_lt_d9]
  nlinarith only [mul_le_mul_of_nonneg_left h (log_nonneg (by norm_num : (1:ℝ)≤2)),
    mul_le_mul_of_nonneg_right h2 ll]

lemma choose_good (C : ℝ) (c0 : 0<C)
    (avg : ∀ n : ℕ, 1≤n → (∑ j ∈ range n,G j) ≤ C*n*(1+log n))
    (typ : ∀ᶠ M : ℕ in atTop,
      (((range M).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+1/20:ℝ)*log (log n))).card:ℝ) ≤ (1/8:ℝ)*M) :
    ∀ᶠ X : ℕ in atTop, ∃ j : ℕ, X<j ∧ j≤2*X ∧
      (cardFactors j:ℝ) ≤ (1+1/20:ℝ)*log (log j) ∧ G j ≤ 32*C*log X := by
  classical
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨K,hK⟩ := eventually_atTop.mp typ
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1, hl.eventually_ge_atTop 1] with X hX X1 lx
  let M := 2*X+1
  let A := (range M).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+1/20:ℝ)*log (log n))
  let S := Ioc X (2*X) \ A
  have x1 : 1≤(X:ℝ) := by exact_mod_cast X1
  have xp : 0 < (X:ℝ) := zero_lt_one.trans_le x1
  have minM : K≤M := by dsimp [M]; omega
  have bad := hK M minM
  change (A.card:ℝ) ≤ (1/8:ℝ)*M at bad
  have cardI : (Ioc X (2*X)).card=X := by rw [Nat.card_Ioc]; omega
  have count : (X:ℝ)/2 ≤ S.card := by
    have h : X ≤ S.card+A.card := by
      dsimp [S]
      conv_lhs => rw [←cardI]
      exact (Finset.card_le_card (s:=Ioc X (2*X)) (t:=((Ioc X (2*X)) \ A) ∪ A)
        (by intro i hi; by_cases mem : i∈A <;> simp [hi,mem])).trans (Finset.card_union_le _ _)
    have hr : (X:ℝ) ≤ S.card+A.card := by exact_mod_cast h
    dsimp [M] at bad
    push_cast at bad
    linarith
  have subset : S ⊆ range M := by
    intro j hj
    have lo := mem_Ioc.mp (mem_sdiff.mp hj).1
    exact mem_range.mpr (by dsimp [M]; omega)
  have m1 : 1≤M := by dsimp [M]; omega
  have Mr : (M:ℝ) ≤ 3*X := by dsimp [M]; push_cast; linarith
  have ml : log (M:ℝ) ≤ 2+log X := by
    have t := log_le_log (by exact_mod_cast m1 : 0<(M:ℝ)) Mr
    rw [log_mul (by norm_num) xp.ne'] at t
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have wl : 1 ≤ log (X:ℝ) := lx
  have total := (sum_le_sum_of_subset_of_nonneg subset (fun i _ _ => gpos i)).trans (avg M m1)
  have hi : ∑ j ∈ S,G j ≤ 12*C*X*log X := by
    apply total.trans
    have b := mul_le_mul Mr (show 1+log (M:ℝ) ≤ 4*log X by linarith)
      (by linarith [log_nonneg (by exact_mod_cast m1 : 1≤(M:ℝ))]) (by positivity)
    linarith only [mul_le_mul_of_nonneg_left b c0.le]
  have ex : ∃ j ∈ S, G j ≤ 32*C*log X := by
    by_contra! hh
    have ge := sum_le_sum (s:=S) fun j hj => (hh j hj).le
    rw [sum_const,nsmul_eq_mul] at ge
    have hmul := mul_le_mul_of_nonneg_right count (show 0≤32*C*log X by positivity [show 0≤log (X:ℝ) by linarith])
    have p := mul_pos (mul_pos c0 xp) (zero_lt_one.trans_le wl)
    nlinarith only [hi,ge,hmul,p]
  obtain ⟨j,hj,hg⟩ := ex
  obtain ⟨rng,hnot⟩ := mem_sdiff.mp hj
  obtain ⟨xj,jx⟩ := mem_Ioc.mp rng
  exact ⟨j,xj,jx,not_not.mp (fun badj => hnot (mem_filter.mpr ⟨subset hj,badj⟩)),hg⟩

lemma finish (typ : ∀ᶠ M : ℕ in atTop,
      (((range M).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+1/20:ℝ)*log (log n))).card:ℝ) ≤ (1/8:ℝ)*M) :
    OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.H1 := by
  intro q hq
  obtain ⟨C,c0,avg⟩ := mean
  let l (X : ℕ) := log (X:ℝ)^(1/8:ℝ)
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have big : Tendsto l atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp hl
  filter_upwards [choose_good C c0 avg typ, hl.eventually_ge_atTop 1, eventually_ge_atTop 2,
    big.eventually_gt_atTop ((q:ℝ)*(2+32*C)+1)] with X choice lx X2 huge
  obtain ⟨j,xj,jx,normal,tail⟩ := choice
  have xp : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have wl : 1 ≤ log (X:ℝ) := lx
  have wp := zero_lt_one.trans_le wl
  have lp : 1 ≤ l X := one_le_rpow wl (by norm_num)
  have lp0 := zero_lt_one.trans_le lp
  have pow (e : ℕ) : (l X)^e = (log (X:ℝ))^((1/8:ℝ)*e) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul wp.le]
  have pow7 : (l X)^7 = (log (X:ℝ))^(7/8:ℝ) := by rw [pow]; norm_num
  have pow6 : (l X)^6 = (log (X:ℝ))^(3/4:ℝ) := by rw [pow]; norm_num
  have pow8 : (l X)^8 = log (X:ℝ) := by rw [pow]; norm_num
  have ld := log_le_log xp (by exact_mod_cast xj.le : (X:ℝ) ≤ j)
  have jp : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have logj : log (j:ℝ) ≤ 2*log X := by
    have ub : (j:ℝ) ≤ 2*X := by exact_mod_cast jx
    have eq := log_le_log jp ub
    rw [log_mul (by norm_num) xp.ne'] at eq
    linarith [log_two_lt_d9]
  have tau : (j.divisors.card:ℝ) ≤ 2*(l X)^6 := by
    apply (digit j (wl.trans ld) normal).trans
    calc
      _ ≤ (2*log (X:ℝ))^(3/4:ℝ) := rpow_le_rpow (by linarith) logj (by norm_num)
      _ = (2:ℝ)^(3/4:ℝ)*(l X)^6 := by rw [mul_rpow (by norm_num) wp.le,pow6]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (3/4:ℝ)≤1)) (by positivity)
  have tail' : G j/(l X)^7 ≤ 32*C*l X := by
    apply (div_le_iff₀ (pow_pos lp0 _)).mpr
    rw [←pow8] at tail
    linarith only [tail]
  refine ⟨j-1,by omega,?_⟩
  change (q:ℝ)*(((j-1+1).divisors.card:ℝ)+G (j-1+1)/(log X)^(7/8:ℝ)) < (log X)^(7/8:ℝ)
  rw [show j-1+1=j by omega,←pow7]
  have L6 : l X ≤ (l X)^6 := by simpa using pow_le_pow_right₀ lp (by decide : 1≤6)
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add tau tail') (Nat.cast_nonneg q)) _
  have h1 := mul_le_mul_of_nonneg_left L6 (show 0≤32*C by positivity)
  have h2 := mul_lt_mul_of_pos_right (show (q:ℝ)*(2+32*C)<l X by linarith) (pow_pos lp0 6)
  nlinarith only [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg q : (0:ℝ)≤q),h2]

end TypicalDivisor258

theorem OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H1 : OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.H1 := by
  apply TypicalDivisor258.finish
  exact Omega1100.bad_count_final (1/20) (1/8) (by norm_num) (by norm_num)

/-! A square array of distinct primes prescribes exact valuations in an
initial block. Later shifts are coprime to the CRT modulus, so counting
small divisor pairs on one progression bounds their first moment.
The summability and pointwise geometric majorant are reused from
@marcusbuffett's merged companion proof of Erdős 258, monotone H1. -/
open Finset Real
namespace Window258
-- The polynomial nth-prime estimate is adapted from @loremcdmx's merged Erdős 5
-- proof via @marcusbuffett's Erdős 980 quadratic reduction.

lemma key (m : ℕ) (hm : 16 ≤ m) : Nat.nth Nat.Prime m ≤ m ^ 2 := by
  have hm' : (16:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Chebyshev.pi_ge (m ^ 2)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2 : Real.log (((m ^ 2 : ℕ) : ℝ)) = 2 * Real.log m := by
    push_cast; rw [Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hA : Real.log (m : ℝ) ≤ m / 8 + 3 := by
    have h8 : Real.log ((m:ℝ) / 8) ≤ m / 8 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h2' := Real.log_two_lt_d9
    linarith
  have h2' := Real.log_two_lt_d9
  have hB : Real.log (((m ^ 2 : ℕ) : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log m := by
    have e : Real.log (2 * (m:ℝ) ^ 2) = Real.log 2 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    rw [← e]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have h3 : (m:ℝ) * Real.log m ≤ (m:ℝ) * (m / 8 + 3) := mul_le_mul_of_nonneg_left hA hm0
  have h4 : (m:ℝ)^2 * 0.69 ≤ (m:ℝ)^2 * Real.log 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlt : (m : ℝ) < (((m ^ 2 : ℕ) : ℝ) * Real.log 2 - Real.log (((m ^ 2 : ℕ) : ℝ) + 1)) / Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    rw [hl2, lt_div_iff₀ (by linarith)]
    push_cast at hB ⊢
    nlinarith
  have hcnt : (m : ℝ) < (Nat.primeCounting (m ^ 2) : ℝ) := lt_of_lt_of_le hlt hpi
  have hcnt' : m < Nat.primeCounting (m ^ 2) := by exact_mod_cast hcnt
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m ^ 2 + 1) (k := m) hcnt'
  omega

lemma windowCRT (k J t : ℕ) (ht : 2 ≤ t) : ∃ M a : ℕ,
    a < M ∧ M ≤ (J+k+20+k*k)^(2*t*(k*k)) ∧ ∀ N : ℕ, N ≡ a [MOD M] →
    (∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧
    (∀ i < J, (i+(N+k)+1).Coprime M) := by
  classical
  let L := Fin k × Fin k
  let base := J+k+20
  let idx (x : L) : ℕ := base + (finProdFinEquiv x).val
  let p (x : L) := Nat.nth Nat.Prime (idx x)
  have pp (x : L) : (p x).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have pinj : Function.Injective p := by
    intro x y he
    have he' := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective he
    exact finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel he'))
  have plo (x : L) : J+k+1 < p x := by
    have hl : idx x ≤ p x := Nat.le_nth (fun h => (Nat.infinite_setOfPred_prime h).elim)
    dsimp [idx,base] at hl
    omega
  have phi (x : L) : p x ≤ (base+k*k)^2 := by
    refine (key _ (by dsimp [idx,base]; omega)).trans (Nat.pow_le_pow_left ?_ 2)
    exact Nat.add_le_add_left (finProdFinEquiv x).isLt.le _
  let m (x : L) := p x ^ t
  let v (x : L) := p x ^ (t-1) - (x.1.val+1)
  let M := ∏ x, m x
  have hm (x : L) (_ : x ∈ (univ : Finset L)) : m x ≠ 0 := pow_ne_zero _ (pp x).ne_zero
  have pair : Set.Pairwise (↑(univ : Finset L)) (fun x y => (m x).Coprime (m y)) := by
    intro x _ y _ h
    exact (((Nat.coprime_primes (pp x) (pp y)).mpr (pinj.ne h)).pow_left _).pow_right _
  let a := Nat.chineseRemainderOfFinset v m univ hm pair
  refine ⟨M,a,Nat.chineseRemainderOfFinset_lt_prod v m hm pair,?_,?_⟩
  · calc
      M ≤ ∏ _x : L, ((base+k*k)^2)^t := prod_le_prod' fun x _ => Nat.pow_le_pow_left (phi x) _
      _ = _ := by simp [L,base,←pow_mul]
  intro N hN
  have congru (x : L) : N+(x.1.val+1) ≡ p x^(t-1) [MOD m x] := by
    have h := ((hN.of_dvd (dvd_prod_of_mem m (mem_univ x))).trans (a.2 x (mem_univ x))).add_right (x.1.val+1)
    have hsmall : x.1.val+1 ≤ p x ^ (t-1) :=
      (by have := plo x; have := x.1.isLt; omega : x.1.val+1 ≤ p x).trans (Nat.le_self_pow (by omega : t-1≠0) _)
    simpa [v,Nat.sub_add_cancel hsmall] using h
  have val (x : L) : (N+(x.1.val+1)).factorization (p x) = t-1 := by
    have h := congru x
    have hne : N+(x.1.val+1) ≠ 0 := by omega
    have lo := ((pp x).pow_dvd_iff_le_factorization hne).mp ((h.dvd_iff (pow_dvd_pow _ (Nat.sub_le t 1))).mpr dvd_rfl)
    have hi : ¬p x^t ∣ N+(x.1.val+1) := by
      rw [h.dvd_iff (dvd_refl (m x)),Nat.pow_dvd_pow_iff_le_right (pp x).one_lt]
      omega
    rw [(pp x).pow_dvd_iff_le_factorization hne] at hi
    omega
  have dvd (x : L) : p x ∣ N+(x.1.val+1) := by
    apply (Nat.Prime.dvd_iff_one_le_factorization (pp x) (by omega)).mpr
    rw [val]; omega
  constructor
  · intro j hj
    obtain ⟨hj0,hjk⟩ := mem_Icc.mp hj
    let u : Fin k := ⟨j-1,by omega⟩
    have eu : u.val+1=j := by dsimp [u]; omega
    let S := univ.image (fun l : Fin k => p (u,l))
    have hsub : S ⊆ (N+j).primeFactors := by
      intro n hn
      obtain ⟨l,_,rfl⟩ := mem_image.mp hn
      exact Nat.mem_primeFactors.mpr ⟨pp _,by simpa [eu] using dvd (u,l),by omega⟩
    have prodS : S.prod (fun n => (N+j).factorization n+1) = t^k := by
      rw [show S = univ.image (fun l : Fin k => p (u,l)) by rfl,
        prod_image (fun x _ y _ h => congrArg Prod.snd (pinj h))]
      have H (l : Fin k) : (N+j).factorization (p (u,l))+1=t := by
        have := val (u,l); simp only [eu] at this; omega
      simp [H]
    rw [Nat.card_divisors (by omega : N+j≠0)]
    exact (pow_dvd_pow _ hjk).trans (prodS ▸ prod_dvd_prod_of_subset S _ (fun n => (N+j).factorization n+1) hsub)
  · intro i hi
    apply Nat.coprime_prod_right_iff.mpr
    intro x _
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (pp x).coprime_iff_not_dvd.mpr
    intro hd
    have hdiff := Nat.dvd_sub hd (dvd x)
    have e : i+(N+k)+1-(N+(x.1.val+1))=i+k-x.1.val := by omega
    rw [e] at hdiff
    have hx := x.1.isLt
    have hpos : 0 < i+k-x.1.val := by omega
    have := Nat.le_of_dvd hpos hdiff
    have := plo x
    omega
end Window258
open Finset Real
namespace Window258
lemma hyperbola {n D : ℕ} (hn : n ≠ 0) (hD : n ≤ D * D) :
    n.divisors.card ≤ 2 * ((Icc 1 D).filter (· ∣ n)).card := by
  classical
  let S := (Icc 1 D).filter (· ∣ n)
  have sub : n.divisors ⊆ S ∪ S.image (n / ·) := by
    intro d hd
    obtain ⟨hdn,_⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
    by_cases h : d ≤ D
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,h⟩,hdn⟩)
    · have hdq := Nat.div_mul_cancel hdn
      have hq : n / d ≤ D := by
        by_contra! hh
        nlinarith only [Nat.mul_lt_mul_of_lt_of_lt hh (lt_of_not_ge h),hdq,hD]
      have hdvd := Nat.div_dvd_of_dvd hdn
      exact mem_union_right _ (mem_image.mpr ⟨n/d,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn),hq⟩,hdvd⟩,
        Nat.div_div_self hdn hn⟩)
  calc
    _ ≤ (S ∪ S.image (n / ·)).card := card_le_card sub
    _ ≤ S.card + (S.image (n / ·)).card := card_union_le ..
    _ ≤ _ := by have h := card_image_le (f := (n / ·)) (s := S); dsimp [S] at *; omega

lemma hits (A M B d : ℕ) (hc : ∀ r < B, (A+M*r).Coprime M) :
    ((range B).filter (fun r => d ∣ A+M*r)).card ≤ B/d+1 := by
  classical
  rw [← card_range (B/d+1)]
  apply card_le_card_of_injOn (fun r => r/d)
  · intro r hr
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hr).1).le))
  · intro r hr s hs he
    obtain ⟨hrB,hrd⟩ := mem_filter.mp hr
    obtain ⟨hsB,hsd⟩ := mem_filter.mp hs
    have h1 := (Nat.modEq_zero_iff_dvd.mpr hrd).trans (Nat.modEq_zero_iff_dvd.mpr hsd).symm
    have hm := Nat.ModEq.add_left_cancel' A h1
    have hc' := (hc r (mem_range.mp hrB)).coprime_dvd_left hrd
    have h2 := Nat.ModEq.cancel_left_of_coprime hc' hm
    change r % d = s % d at h2
    change r / d = s / d at he
    have h3 := Nat.mod_add_div r d
    rw [h2,he,Nat.mod_add_div] at h3
    exact h3.symm

lemma mean (A M B : ℕ) (hc : ∀ r < B, (A+M*r).Coprime M)
    (hB : ∀ r < B, 0 < A+M*r ∧ A+M*r ≤ B*B) :
    (∑ r ∈ range B, ((A+M*r).divisors.card : ℝ)) ≤ 2*B*(2+log B) := by
  classical
  let I := Icc 1 B
  have count : (∑ r ∈ range B, (((I.filter (· ∣ A+M*r)).card):ℝ)) =
      ∑ d ∈ I, (((range B).filter (fun r => d ∣ A+M*r)).card:ℝ) := by
    calc
      _ = ∑ r ∈ range B, ∑ d ∈ I, if d ∣ A+M*r then (1:ℝ) else 0 := by
        apply sum_congr rfl; intro r hr; rw [←sum_filter]; simp
      _ = _ := by
        rw [sum_comm]; apply sum_congr rfl; intro d hd; rw [←sum_filter]; simp
  have har := harmonic_le_one_add_log B
  rw [harmonic_eq_sum_Icc] at har
  push_cast at har
  calc
    _ ≤ ∑ r ∈ range B, 2 * (((I.filter (· ∣ A+M*r)).card):ℝ) := by
      apply sum_le_sum; intro r hr
      obtain ⟨h1,h2⟩ := hB r (mem_range.mp hr)
      exact_mod_cast hyperbola h1.ne' h2
    _ = 2 * ∑ d ∈ I, (((range B).filter (fun r => d ∣ A+M*r)).card:ℝ) := by rw [←mul_sum,count]
    _ ≤ 2 * ∑ d ∈ I, ((B:ℝ)*(d:ℝ)⁻¹+1) := by
      gcongr with d hd
      have hd0 : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
      have hdiv : ((B/d:ℕ):ℝ) ≤ (B:ℝ)/d := by
        apply (le_div_iff₀ hd0).mpr; exact_mod_cast Nat.div_mul_le_self B d
      have h := hits A M B d hc
      rw [←div_eq_mul_inv]
      exact (by exact_mod_cast h : _ ≤ ((B/d:ℕ):ℝ)+1) |>.trans (by linarith)
    _ ≤ _ := by
      rw [sum_add_distrib, ←mul_sum]
      simp [I] at *
      nlinarith only [mul_le_mul_of_nonneg_left har (Nat.cast_nonneg B : (0:ℝ)≤B)]
noncomputable def G (n : ℕ) : ℝ := ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
noncomputable def b (k : ℕ) : ℝ := ((k:ℝ)+1)*((1:ℝ)/2)^k

lemma bsum : Summable b := by
  have h : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 1 (r:=1/2) (by norm_num)
  change Summable (fun k : ℕ => b k)
  simpa [b,add_mul] using h.add (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))

lemma dom (n k : ℕ) : ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k ≤ ((n:ℝ)+1)*b k := by
  have h : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
  push_cast at h
  unfold b
  rw [div_pow,one_pow,←mul_assoc,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [h,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg k : (0:ℝ)≤k)]

lemma gs (n : ℕ) : Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (dom n) (bsum.mul_left _)

lemma tail_select (A M B k J : ℕ) (hBp : 0 < B)
    (hc : ∀ i < J, ∀ r < B, (i+(A+M*r+k)+1).Coprime M)
    (hn : ∀ i < J, ∀ r < B, i+(A+M*r+k)+1 ≤ B*B)
    (hcut : ∀ r < B, J+(A+M*r+k)+1 ≤ 2^J) :
    ∃ r < B, G (A+M*r+k) ≤ 4*(2+log B) + ∑' i, b i := by
  classical
  let f (r i : ℕ) : ℝ := ((i+(A+M*r+k)+1).divisors.card:ℝ) / 2^i
  have m (i : ℕ) (hi : i < J) : (∑ r ∈ range B, f r i) ≤ 2*B*(2+log B)/(2:ℝ)^i := by
    dsimp [f]; rw [←sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      mean (i+A+k+1) M B (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc i hi)
        (fun r hr => ⟨by omega, by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn i hi r hr⟩)
  have g : (∑ i ∈ range J, (2:ℝ)⁻¹^i) ≤ 2 := by
    have h := (summable_geometric_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)).sum_le_tsum
      (range J) (fun _ _ => by positivity)
    rwa [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num),show (1-(2:ℝ)⁻¹)⁻¹=2 by norm_num] at h
  have p : 0 ≤ 2*(B:ℝ)*(2+log B) := by
    have := Real.log_nonneg (show 1 ≤ (B:ℝ) by exact_mod_cast hBp); positivity
  have mainSum : (∑ r ∈ range B, ∑ i ∈ range J, f r i) ≤ ∑ _r ∈ range B, 4*(2+log (B:ℝ)) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ i ∈ range J, (2*(B:ℝ)*(2+log B)) * ((2:ℝ)⁻¹)^i :=
        sum_le_sum fun i hi => by simpa only [div_eq_mul_inv,inv_pow] using m i (mem_range.mp hi)
      _ ≤ _ := by
        rw [←mul_sum]
        simp only [sum_const,card_range,nsmul_eq_mul]
        nlinarith only [mul_le_mul_of_nonneg_left g p]
  obtain ⟨r,hr,hs⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr hBp.ne') mainSum
  refine ⟨r,mem_range.mp hr,?_⟩
  have tail (i : ℕ) : f r (i+J) ≤ b i := by
    change ((i+J+(A+M*r+k)+1).divisors.card:ℝ)/(2:ℝ)^(i+J) ≤ _
    rw [show i+J+(A+M*r+k)+1=i+(J+(A+M*r+k))+1 by omega,pow_add,←div_div]
    apply (div_le_iff₀ (by positivity)).mpr
    have H := dom (J+(A+M*r+k)) i
    have hcap : ((J+(A+M*r+k):ℕ):ℝ)+1 ≤ (2:ℝ)^J := by exact_mod_cast hcut r (mem_range.mp hr)
    exact H.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hcap (by dsimp [b]; positivity : 0 ≤ b i))
  change (∑' i, f r i) ≤ _
  have sf : Summable (f r) := gs _
  rw [←sf.sum_add_tsum_nat_add J]
  exact add_le_add hs (((summable_nat_add_iff J).mpr sf).tsum_le_tsum tail bsum)
end Window258
namespace Window258
open Filter
lemma assemble (q X t k J B : ℕ) (ht : 2 ≤ t) (hBp : 0 < B)
    (hroom : ((B+2)*(J+k+20+k*k)^(2*t*(k*k))+k+1)*⌊(log X)^(7/8:ℝ)⌋₊ ≤ X)
    (hbase : 0 < ⌊(log X)^(7/8:ℝ)⌋₊)
    (hsq : J+X+1 ≤ B*B) (hcut : J+X+1 ≤ 2^J)
    (hgoal : (q:ℝ)*(4*(2+log B)+∑' i,b i) < (2:ℝ)^k)
    (I : Finset ℕ) (hI : I ⊆ Icc 1 X) (convex : ∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I)
    (hsize : X/⌊(log X)^(7/8:ℝ)⌋₊ ≤ I.card) :
    ∃ N k : ℕ, Icc (N+1) (N+k) ⊆ I ∧ (∀ j ∈ Icc 1 k,t^j ∣ (N+j).divisors.card) ∧
       (q:ℝ)*G (N+k) < (t:ℝ)^k := by
  obtain ⟨M,a,ha,hM,good⟩ := windowCRT k J t ht
  have span : (B+2)*M+k+1 ≤ I.card := by
    refine le_trans ?_ ((Nat.le_div_iff_mul_le hbase).mpr hroom |>.trans hsize)
    gcongr
  have ne : I.Nonempty := card_pos.mp (by omega)
  let lo := I.min' ne
  let hi := I.max' ne
  have hlo : lo ∈ I := I.min'_mem ne
  have hhi : hi ∈ I := I.max'_mem ne
  have len : I.card ≤ hi+1-lo := by
    rw [←Nat.card_Icc]
    exact card_le_card (fun i h => mem_Icc.mpr ⟨I.min'_le i h,I.le_max' i h⟩)
  have lh : lo ≤ hi := I.min'_le _ hhi
  let A := a+M*(lo/M+1)
  have hmp : M ≠ 0 := by omega
  have lb : lo ≤ A := by
    have h := Nat.mod_add_div lo M
    have := Nat.mod_lt lo (Nat.pos_of_ne_zero hmp)
    dsimp [A]; rw [Nat.mul_add]; omega
  have ub : A ≤ lo+2*M := by
    have := Nat.div_mul_le_self lo M
    dsimp [A]; rw [Nat.mul_add,Nat.mul_comm M (lo/M)]; omega
  have con (r : ℕ) : A+M*r ≡ a [MOD M] := by
    simp [A,Nat.ModEq,Nat.add_mod]
  have endpt (r : ℕ) (hr : r < B) : A+M*r+k ≤ hi := by
    have H := Nat.mul_le_mul_left M hr.le
    rw [Nat.add_mul,Nat.mul_comm B M] at span
    omega
  have endX (r : ℕ) (hr : r < B) := (endpt r hr).trans (mem_Icc.mp (hI hhi)).2
  obtain ⟨r,hr,hgood⟩ := tail_select A M B k J hBp
    (fun i hi r _ => (good _ (con r)).2 _ hi)
    (fun i hi r hr => by have := endX r hr; omega)
    (fun r hr => by have := endX r hr; omega)
  refine ⟨A+M*r,k,fun n hn => convex lo hlo hi hhi ?_,(good _ (con r)).1,?_⟩
  · have hn' := mem_Icc.mp hn
    have := endpt r hr
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · exact (mul_le_mul_of_nonneg_left hgood (Nat.cast_nonneg q)).trans_lt
      (hgoal.trans_le (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast ht) k))

end Window258
namespace Window258
open Filter Asymptotics
lemma parameters (q : ℕ) (C : ℝ) : ∀ᶠ X : ℕ in atTop, ∀ t : ℕ, (t:ℝ) ≤ (log X)^(7/8:ℝ) →
    ∃ k J B : ℕ, 0 < B ∧
    ((B+2)*(J+k+20+k*k)^(2*t*(k*k))+k+1)*⌊(log X)^(7/8:ℝ)⌋₊ ≤ X ∧
    0 < ⌊(log X)^(7/8:ℝ)⌋₊ ∧ J+X+1 ≤ B*B ∧ J+X+1 ≤ 2^J ∧
    (q:ℝ)*(4*(2+log B)+C) < (2:ℝ)^k := by
  have hX := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hY := Real.tendsto_log_atTop.comp hX
  have hW := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp hY
  have hZ := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp hX
  have evW := hY.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).bound
    (by norm_num : (0:ℝ)<1/8))
  have evZ := hX.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/8)).bound
    (by norm_num : (0:ℝ)<1))
  filter_upwards [hW.eventually_ge_atTop 64,hZ.eventually_ge_atTop 64,hY.eventually_ge_atTop 32,
    hY.eventually_gt_atTop ((q:ℝ)*(12+|C|)),evW,evZ,eventually_ge_atTop 1]
    with X hw hz hy hq ew ez hXp t ht
  let y := log (X:ℝ)
  let w := y^(1/32:ℝ)
  let z := (X:ℝ)^(1/8:ℝ)
  change 64 ≤ w at hw
  change 64 ≤ z at hz
  change 32 ≤ y at hy
  change (q:ℝ)*(12+|C|)<y at hq
  change (t:ℝ) ≤ y^(7/8:ℝ) at ht
  change ‖log y‖ ≤ (1/8:ℝ)*‖w‖ at ew
  change ‖y‖ ≤ 1*‖z‖ at ez
  have ly := log_nonneg (show 1 ≤ y by linarith)
  rw [Real.norm_of_nonneg ly,Real.norm_of_nonneg (by linarith)] at ew
  rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith),one_mul] at ez
  have wp : 0 ≤ w := by linarith
  have zp : 0 ≤ z := by linarith
  have wpow (n : ℕ) : w^n = y^((1/32:ℝ)*n) := (rpow_mul_natCast (by linarith : 0≤y) _ _).symm
  have yw : w^32 = y := by rw [wpow]; norm_num
  have tw : y^(7/8:ℝ) = w^28 := by rw [wpow]; norm_num
  have zx : z^8 = (X:ℝ) := by dsimp [z]; rw [←rpow_mul_natCast (Nat.cast_nonneg X)]; norm_num
  have incw {a b : ℕ} (h : a ≤ b) : w^a ≤ w^b := pow_le_pow_right₀ (by linarith) h
  have incz {a b : ℕ} (h : a ≤ b) : z^a ≤ z^b := pow_le_pow_right₀ (by linarith) h
  let k := ⌈4*log y⌉₊
  let J := ⌈4*y⌉₊
  let B := ⌈z^5⌉₊
  have kw : (k:ℝ) ≤ w := by
    have h : (k:ℝ) < 4*log y+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have Jy : (J:ℝ) ≤ 5*y := by
    have h : (J:ℝ) < 4*y+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have Jlo : 4*y ≤ (J:ℝ) := Nat.le_ceil _
  have klo : 4*log y ≤ (k:ℝ) := Nat.le_ceil _
  have Blo : z^5 ≤ (B:ℝ) := Nat.le_ceil _
  have Bhi : (B:ℝ) < z^5+1 := Nat.ceil_lt_add_one (by positivity)
  have Bp : 0 < B := by
    have : 0 < (B:ℝ) := (pow_pos (by linarith : 0<z) 5).trans_le Blo
    exact_mod_cast this
  have wy : w ≤ y := by simpa [yw] using incw (show 1≤32 by decide)
  have w2y : w*w ≤ y := by simpa [←pow_two,yw] using incw (show 2≤32 by decide)
  let base := J+k+20+k*k
  have Hbase : (base:ℝ) ≤ 8*y := by
    dsimp [base]; push_cast
    have hkk := mul_self_le_mul_self (Nat.cast_nonneg k : (0:ℝ)≤k) kw
    linarith
  have HBpos : 0 < (base:ℝ) := by dsimp [base]; positivity
  have logbase : log (base:ℝ) ≤ 2*w := by
    have H := Real.log_le_log HBpos Hbase
    rw [log_mul (by norm_num : (8:ℝ)≠0) (by linarith : y≠0)] at H
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
  have ht' : (t:ℝ) ≤ w^28 := tw ▸ ht
  have Mz : ((base^(2*t*(k*k)):ℕ):ℝ) ≤ z := by
    push_cast
    apply (Real.log_le_log_iff (pow_pos HBpos _) (by linarith)).mp
    rw [Real.log_pow,show log z = (1/8:ℝ)*y by exact Real.log_rpow (by exact_mod_cast hXp : (0:ℝ)<X) _]
    push_cast
    calc
      _ ≤ (2*w^28*(w*w))*(2*w) := by
        gcongr
      _ = 4*w^31 := by ring
      _ ≤ _ := by
        rw [←yw,show w^32=w^31*w by ring]
        nlinarith only [mul_nonneg (pow_nonneg wp 31) (show 0≤w-32 by linarith)]
  have z5 : 1 ≤ z^5 := one_le_pow₀ (by linarith)
  have zpwr (i : ℕ) : 32*z^i ≤ z^(i+1) := by
    rw [pow_succ]; nlinarith only [mul_nonneg (pow_nonneg zp i) (show 0≤z-32 by linarith)]
  have z56 : 32*z^5 ≤ z^6 := zpwr 5
  have z67 : 32*z^6 ≤ z^7 := zpwr 6
  have z78 : 32*z^7 ≤ z^8 := zpwr 7
  have z89 : 32*z^8 ≤ z^9 := zpwr 8
  have Bx : (B:ℝ) ≤ X := by
    rw [←zx]; linarith only [Bhi,z5,z56,incz (show 6≤8 by decide)]
  have floorle : (⌊y^(7/8:ℝ)⌋₊:ℝ) ≤ z := by
    refine (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans ?_
    rw [tw]; exact (incw (by decide : 28≤32)).trans (yw ▸ ez)
  have room : ((((B+2)*base^(2*t*(k*k))+k+1)*⌊y^(7/8:ℝ)⌋₊:ℕ):ℝ) ≤ X := by
    push_cast
    calc
      _ ≤ (((z^5+1)+2)*z+z+1)*z := by
        gcongr
        · exact_mod_cast Mz
        · exact kw.trans (wy.trans ez)
      _ ≤ z^8 := by
        have zs : z ≤ z^6 := by simpa using incz (show 1≤6 by decide)
        nlinarith only [z78,z67,incz (show 2≤6 by decide),zs,hz]
      _ = _ := zx
  have X2 : (J:ℝ)+1 ≤ X := by
    have zs : z ≤ z^7 := by simpa using incz (show 1≤7 by decide)
    linarith only [Jy,ez,zs,z78,zx,hz]
  have sqcap : (J:ℝ)+X+1 ≤ (B:ℝ)*B := by
    have hbb := mul_self_le_mul_self (pow_nonneg zp 5) Blo
    have e : z^5*z^5=z^10 := by ring
    linarith only [X2,zx,z89,incz (by decide : 9≤10),hbb,e,Nat.cast_nonneg X (α:=ℝ)]
  have expo : 2*(X:ℝ) ≤ (2:ℝ)^J := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by exact_mod_cast hXp : (0:ℝ)<X).ne',Real.log_pow]
    change log 2+y ≤ (J:ℝ)*log 2
    have e2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
    nlinarith only [mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg J),Jlo,hy,log_two_lt_d9]
  have scale : y^2 ≤ (2:ℝ)^k := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have e2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
    nlinarith only [mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg k),klo]
  have fp : 0 < ⌊y^(7/8:ℝ)⌋₊ := by
    apply Nat.floor_pos.mpr
    rw [tw]; exact one_le_pow₀ (by linarith)
  refine ⟨k,J,B,Bp,by exact_mod_cast room,fp,by exact_mod_cast sqcap,?_,?_⟩
  · exact_mod_cast (show (J:ℝ)+X+1 ≤ (2:ℝ)^J by linarith only [expo,X2])
  · have hlogB : log (B:ℝ) ≤ y := Real.log_le_log (by exact_mod_cast Bp) Bx
    have hfac : 4*(2+log B)+C ≤ (12+|C|)*y := by
      nlinarith only [hlogB,le_abs_self C,abs_nonneg C,hy,
        mul_nonneg (abs_nonneg C) (show 0≤y-1 by linarith)]
    calc
      _ ≤ (q:ℝ)*((12+|C|)*y) := mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg q)
      _ < y^2 := by nlinarith only [mul_lt_mul_of_pos_right hq (by linarith : 0<y)]
      _ ≤ _ := scale
end Window258

theorem OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2 : OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.H2 := by
  intro q _
  filter_upwards [Window258.parameters q (∑' i, Window258.b i)] with X hX t ht ht' I hI hconv hsize
  obtain ⟨k,J,B,hB,hroom,hfloor,hsq,hcut,hgoal⟩ := hX t ht'
  exact Window258.assemble q X t k J B ht hB hroom hfloor hsq hcut hgoal I hI hconv hsize

theorem OMA.solution : type_of% @Erdos258.erdos_258.variants.monotone :=
  (OMA.R_Erdos258_erdos_258_variants_monotone_R2.main OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H1 (OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.main OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H1 OMA.assembled_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2))
