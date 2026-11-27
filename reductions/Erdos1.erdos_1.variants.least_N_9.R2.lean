import FormalConjectures.ErdosProblems.«1»
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! A second-moment pruning rule for the finite search below 161. -/

-- Reduction Erdos1.erdos_1.variants.least_N_9.R2 of Erdős Problem 1 — least N 9
-- Credit: @ysanatomic
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R2

open Finset Erdos1

private theorem square_deviations (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [sum_powerset_insert ha, card_insert_of_notMem ha, sum_insert ha, ← sum_add_distrib]
    let v (S : Finset ℕ) : ℝ := 2 * ∑ x ∈ S, (x : ℝ) - ∑ x ∈ A, (x : ℝ)
    have hterm (S : Finset ℕ) (hS : S ∈ A.powerset) :
        (2 * ∑ x ∈ S, (x : ℝ) - ((a : ℝ) + ∑ x ∈ A, (x : ℝ))) ^ 2 +
          (2 * ∑ x ∈ insert a S, (x : ℝ) - ((a : ℝ) + ∑ x ∈ A, (x : ℝ))) ^ 2 =
          2 * v S ^ 2 + 2 * (a : ℝ) ^ 2 := by
      rw [sum_insert (fun hs => ha (mem_powerset.mp hS hs))]
      dsimp [v]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_const, card_powerset, nsmul_eq_mul]
    change 2 * (∑ S ∈ A.powerset, (2 * ∑ x ∈ S, (x : ℝ) - ∑ x ∈ A, (x : ℝ)) ^ 2) + _ = _
    rw [ih, Nat.cast_pow, Nat.cast_ofNat, pow_succ, sum_insert ha]
    ring

private theorem strictMono_nat_gap {d : ℕ} {f : Fin d → ℕ} (hf : StrictMono f) :
    ∀ i j : Fin d, i ≤ j → f i + (j.val - i.val) ≤ f j := by
  suffices key : ∀ (j : ℕ) (hj : j < d) (i : Fin d), i.val ≤ j →
      f i + (j - i.val) ≤ f ⟨j, hj⟩ by
    intro i j h
    exact key j.val j.isLt i h
  intro j
  induction j with
  | zero =>
    intro hj i h
    have hi : i = ⟨0, hj⟩ := Fin.ext (Nat.eq_zero_of_le_zero h)
    simp [hi]
  | succ j ih =>
    intro hj i h
    by_cases hi : i.val = j + 1
    · have he : i = ⟨j + 1, hj⟩ := Fin.ext hi
      simp [he]
    · have hj' : j < d := by omega
      have hgap := ih hj' i (by omega)
      have hlt : f ⟨j, hj'⟩ < f ⟨j + 1, hj⟩ := hf (show (⟨j, hj'⟩ : Fin d) < ⟨j+1,hj⟩ by
        exact Nat.lt_succ_self _)
      omega

private theorem centered_square_bound (f : Fin 512 → ℕ) (hf : StrictMono f) (c : ℝ) :
    (512 : ℝ) * 87381 ≤ ∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2 := by
  let v (i : ℕ) : ℝ := if h : i < 512 then (2 * (f ⟨i,h⟩ : ℝ) - c) ^ 2 else 0
  have hsum : (∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2) = ∑ i ∈ range 512, v i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun i _ ↦ by simp [v, i.isLt]
  rw [hsum, show (512 : ℕ) = 256 + 256 by decide, sum_range_add]
  rw [← sum_range_reflect (fun i ↦ v (256 + i)) 256, ← sum_add_distrib]
  have hc : (512 : ℝ) * 87381 = ∑ i ∈ range 256, 2 * ((511 - 2 * i : ℕ) : ℝ) ^ 2 := by
    have h : ∑ i ∈ range 256, 2 * (511 - 2 * i) ^ 2 = 44739072 := by decide +kernel
    exact_mod_cast h.symm
  rw [hc]
  refine sum_le_sum fun i hi ↦ ?_
  have hi' : i < 256 := mem_range.mp hi
  have hi512 : i < 512 := by omega
  have hj512 : 511 - i < 512 := by omega
  have hidx : 256 + (256 - 1 - i) = 511 - i := by omega
  rw [hidx]
  simp only [v, dif_pos hi512, dif_pos hj512]
  have hgap := strictMono_nat_gap hf ⟨i,hi512⟩ ⟨511-i,hj512⟩ (show i ≤ 511-i by omega)
  dsimp only at hgap
  have hd := (show f ⟨i,hi512⟩ + (511 - 2 * i) ≤ f ⟨511-i,hj512⟩ by omega)
  let x : ℝ := f ⟨i,hi512⟩
  let y : ℝ := f ⟨511-i,hj512⟩
  let d : ℝ := ((511 - 2*i : ℕ) : ℝ)
  have hdxy : x + d ≤ y := by
    dsimp [x,y,d]
    exact_mod_cast hd
  have hdnonneg : 0 ≤ d := Nat.cast_nonneg _
  have hsq : d ^ 2 ≤ (y - x) ^ 2 := by nlinarith
  change 2 * d ^ 2 ≤ (2*x-c)^2 + (2*y-c)^2
  nlinarith [sq_nonneg (x+y-c)]

theorem distinct_nine_square_sum {A : Finset ℕ} {N : ℕ}
    (hA : Erdos1.IsSumDistinctSet A N) (hc : A.card = 9) : 87381 ≤ ∑ x ∈ A, x ^ 2 := by
  classical
  let T := A.powerset.image (fun S : Finset ℕ ↦ S.sum id)
  have hinj : Set.InjOn (fun S : Finset ℕ ↦ S.sum id) (A.powerset : Set (Finset ℕ)) := by
    intro S hs U hu h
    exact congrArg Subtype.val (@hA.2 ⟨S, hs⟩ ⟨U, hu⟩ h)
  have hcard : T.card = 512 := by
    rw [card_image_of_injOn hinj, card_powerset, hc]
    decide
  let e := T.orderIsoOfFin hcard
  let f : Fin 512 → ℕ := fun i ↦ (e i).val
  have hf : StrictMono f := fun _ _ h ↦ e.strictMono h
  let c : ℝ := ∑ a ∈ A, (a : ℝ)
  have hsum : (∑ i : Fin 512, (2 * (f i : ℝ) - c) ^ 2) =
      ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - c) ^ 2 := by
    calc
      _ = ∑ i : T, (2 * (i.val : ℝ) - c) ^ 2 :=
        Fintype.sum_equiv e.toEquiv _ _ (fun _ ↦ rfl)
      _ = ∑ i ∈ T, (2 * (i : ℝ) - c) ^ 2 := sum_coe_sort T (fun i : ℕ ↦ (2 * (i : ℝ) - c)^2)
      _ = _ := by
        dsimp [T]
        rw [sum_image hinj]
        simp [Nat.cast_sum]
  have h := centered_square_bound f hf c
  rw [hsum] at h
  change (512 : ℝ) * 87381 ≤
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 at h
  rw [square_deviations, hc] at h
  have hh : (87381 : ℝ) ≤ ∑ a ∈ A, (a : ℝ) ^ 2 := by norm_num at h; linarith
  exact_mod_cast hh


private theorem small_max_excluded {A : Finset ℕ}
    (hA : A ⊆ Icc 1 102) (hcard : A.card = 9) :
    (∑ x ∈ A, x ^ 2) < 87381 := by
  let e := A.orderIsoOfFin hcard
  let f : Fin 9 → ℕ := fun i ↦ (e i).val
  have hf : StrictMono f := fun _ _ h ↦ e.strictMono h
  have hlast : f 8 ≤ 102 := (mem_Icc.mp (hA (e 8).property)).2
  have hpoint (i : Fin 9) : f i ≤ 94 + i.val := by
    have hi : i ≤ 8 := by
      change i.val ≤ 8
      exact Nat.le_of_lt_succ i.isLt
    have hgap := strictMono_nat_gap hf i 8 hi
    change f i + (8 - i.val) ≤ f 8 at hgap
    omega
  have hs : (∑ i : Fin 9, (94 + i.val) ^ 2) < 87381 := by decide +kernel
  calc
    (∑ x ∈ A, x ^ 2) = ∑ x : A, x.val ^ 2 := (sum_coe_sort A (fun x : ℕ ↦ x ^ 2)).symm
    _ = ∑ i : Fin 9, f i ^ 2 := (Fintype.sum_equiv e.toEquiv _ _ (fun _ ↦ rfl)).symm
    _ ≤ ∑ i : Fin 9, (94 + i.val) ^ 2 := sum_le_sum fun i _ ↦ Nat.pow_le_pow_left (hpoint i) 2
    _ < 87381 := hs

private theorem subset_sum_total {A : Finset ℕ} {N : ℕ}
    (hA : IsSumDistinctSet A N) (hc : A.card = 9) : 511 ≤ A.sum id := by
  let f (S : Finset ℕ) := S.sum id
  have hinj : Set.InjOn f (A.powerset : Set (Finset ℕ)) := by
    intro S hs T ht h
    exact congrArg Subtype.val (@hA.2 ⟨S, hs⟩ ⟨T, ht⟩ h)
  have hsub : A.powerset.image f ⊆ range (A.sum id + 1) := by
    intro s hs
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hs
    apply mem_range.mpr
    exact Nat.lt_add_one_of_le (sum_le_sum_of_subset (mem_powerset.mp hS))
  have h := card_le_card hsub
  rw [card_image_of_injOn hinj, card_powerset, hc, card_range] at h
  omega

/-- The middle range, after excluding small maxima and pruning by both moments. -/
def H1 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 151 → (∃ x ∈ A, 103 ≤ x) → A.card = 9 →
    87381 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

/-- The last nine possible maxima, with the same moment constraints. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 160 → (∃ x ∈ A, 152 ≤ x) → A.card = 9 →
    87381 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

theorem main : H1 → H2 → type_of% @Erdos1.erdos_1.variants.least_N_9 := by
  intro middle large
  let W : Finset ℕ := {77, 117, 137, 148, 154, 157, 159, 160, 161}
  refine ⟨⟨W, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rintro N ⟨A, hA, hc⟩
    by_contra! hN
    have hs := distinct_nine_square_sum hA hc
    have ht := subset_sum_total hA hc
    have hib (k : ℕ) (h : ∀ x ∈ A, x ≤ k) : A ⊆ Icc 1 k :=
      fun _ hx ↦ mem_Icc.mpr ⟨(mem_Icc.mp (hA.1 hx)).1, h _ hx⟩
    have hx : ∃ x ∈ A, 103 ≤ x := by
      by_contra! hn
      exact (not_lt_of_ge hs) (small_max_excluded (hib 102 (fun x hx ↦ Nat.le_of_lt_succ (hn x hx))) hc)
    have hf :
        ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id := by
      by_cases h : ∃ x ∈ A, 152 ≤ x
      · exact large A (hib 160 (fun x hx ↦ (mem_Icc.mp (hA.1 hx)).2.trans (by omega))) h hc hs ht
      · push Not at h
        exact middle A (hib 151 (fun x hx ↦ Nat.le_of_lt_succ (h x hx))) hx hc hs ht
    obtain ⟨S, hS, T, hT, hne, heq⟩ := hf
    exact hne (congrArg Subtype.val (@hA.2 ⟨S, mem_powerset.mpr hS⟩ ⟨T, mem_powerset.mpr hT⟩ heq))

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R2
