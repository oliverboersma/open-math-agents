import OMAReductions.R_Erdos344_erdos_344_variants_sqrt_two_R1
import Mathlib

/-! The count immediately before the next term is exactly the prefix
size. The resulting quadratic bound also gives an interval-extension
criterion for finite subset sums. -/

open Filter Finset

namespace OMA.Erdos344Quadratic

private theorem square_count {A : Set ℕ} {N : ℕ}
    (h : Real.sqrt (2 * N) ≤ A.countUpTo N) : 2 * N ≤ A.countUpTo N ^ 2 := by
  exact_mod_cast (Real.sqrt_le_iff.mp h).2

theorem ordered_enumeration (A : Set ℕ)
    (hA : ∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, a n ∈ A ∧ 0 < a n) ∧
      ∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2 := by
  classical
  let p : ℕ → Prop := fun n => n ∈ A ∧ 0 < n
  obtain ⟨N, hN⟩ := eventually_atTop.mp hA
  have hinf : (Set.ofPred p).Infinite := by
    intro hfin
    let m := (Set.ofPred p).ncard
    let K := max N (m ^ 2 + 1)
    have hsub : A ∩ Set.Icc 1 K ⊆ Set.ofPred p := by
      rintro x ⟨hx, hpos, _⟩
      exact ⟨hx, hpos⟩
    have hm : A.countUpTo K ≤ m := Set.ncard_le_ncard hsub hfin
    have hm2 : A.countUpTo K ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
    have hK := square_count (hN K (le_max_left _ _))
    have hKm : m ^ 2 + 1 ≤ K := le_max_right _ _
    omega
  let a := Nat.nth p
  have hmono : StrictMono a := Nat.nth_strictMono hinf
  have hmem (n : ℕ) : a n ∈ A ∧ 0 < a n := Nat.nth_mem_of_infinite hinf n
  have hbound (n : ℕ) : n + 1 ≤ a n := by
    induction n with
    | zero => exact (hmem 0).2
    | succ n ih =>
      have hs : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  refine ⟨a, hmono, hmem, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcount : A.countUpTo (a n - 1) = n := by
    have hp := (hmem n).2
    have he : A ∩ Set.Icc 1 (a n - 1) =
        (↑((Finset.range (a n)).filter p) : Set ℕ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range, p]
      constructor
      · rintro ⟨hx, h1, h2⟩
        exact ⟨by omega, hx, h1⟩
      · rintro ⟨hlt, hx, h1⟩
        exact ⟨hx, h1, by omega⟩
    rw [Set.countUpTo, he, Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
    exact Nat.count_nth_of_infinite hinf n
  have hcrit := square_count (hN (a n - 1) (by have := hbound n; omega))
  rw [hcount] at hcrit
  have hp := (hmem n).2
  omega

theorem prefix_frontier (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 0 < a 0)
    (n : ℕ) (hbound : 2 * a n ≤ n ^ 2 + 2) :
    2 * a n + n ≤ 2 * (∑ i ∈ Finset.range n, a i) + 2 := by
  have hpoint (i : ℕ) : i + 1 ≤ a i := by
    induction i with
    | zero => exact ha0
    | succ i ih =>
      have hi : a i < a (i + 1) := ha (Nat.lt_succ_self i)
      omega
  have hsum (k : ℕ) : k * (k + 1) ≤ 2 * (∑ i ∈ Finset.range k, a i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      nlinarith [hpoint k]
  have hs := hsum n
  nlinarith

theorem covers_from_seed (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 0 < a 0)
    (N C b : ℕ) (hsize : 2 * C ≤ N)
    (hbound : ∀ n ≥ N, 2 * a n ≤ n ^ 2 + 2)
    (hCN : C ≤ ∑ i ∈ Finset.range N, a i)
    (hseed : ∀ t ≤ (∑ i ∈ Finset.range N, a i) - C,
      b + t ∈ subsetSums (a '' Set.Iio N)) :
    ∀ t : ℕ, b + t ∈ subsetSums (Set.range a) := by
  let S := fun n : ℕ => ∑ i ∈ Finset.range n, a i
  let P := fun n : ℕ => a '' Set.Iio n
  have hS (n : ℕ) : S (n + 1) = S n + a n := Finset.sum_range_succ a n
  have hmono : Monotone S := monotone_nat_of_le_succ fun n => by rw [hS]; omega
  have hstep : ∀ n ≥ N, ∀ t ≤ S n - C, b + t ∈ subsetSums (P n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hseed
    | succ n hn ih =>
      intro t ht
      have hP : P n ⊆ P (n + 1) := by
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i, by exact Nat.lt_succ_of_lt hi, rfl⟩
      by_cases hsmall : t ≤ S n - C
      · exact subsetSums_mono hP (ih t hsmall)
      have hCn : C ≤ S n := hCN.trans (hmono hn)
      have hfront := prefix_frontier a ha ha0 n (hbound n hn)
      change 2 * a n + n ≤ 2 * S n + 2 at hfront
      have hnext : a n ≤ S n - C + 1 := by omega
      have hnt : a n ≤ t := by omega
      have htail : t - a n ≤ S n - C := by
        rw [hS] at ht
        omega
      obtain ⟨F, hF, he⟩ := ih (t - a n) htail
      have hnF : a n ∉ F := by
        intro hnF
        obtain ⟨m, hm, heq⟩ := hF hnF
        have hmn := ha.injective heq
        have hm' : m < n := hm
        omega
      refine ⟨insert (a n) F, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨n, Nat.lt_succ_self _, rfl⟩
        · exact hP (hF hx)
      · rw [Finset.sum_insert hnF, ← he]
        omega
  intro t
  let n := max N (t + C)
  have hn : N ≤ n := le_max_left _ _
  have ht : t + C ≤ n := le_max_right _ _
  have hSn : n ≤ S n := by
    have hsum : (∑ _ ∈ Finset.range n, (1 : ℕ)) ≤ S n := by
      apply Finset.sum_le_sum
      intro i _
      exact ha0.trans_le (ha.monotone (Nat.zero_le i))
    simpa using hsum
  apply subsetSums_mono (Set.image_subset_range _ _)
  exact hstep n hn t (by omega)

end OMA.Erdos344Quadratic

theorem OMA.solution : OMA.R_Erdos344_erdos_344_variants_sqrt_two_R1.H1 :=
  OMA.Erdos344Quadratic.ordered_enumeration
