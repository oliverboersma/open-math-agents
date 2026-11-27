import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1
import Mathlib

-- Step CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1.H1.R1.H2: hypothesis H2 of reduction CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1.H1.R1
-- Credit: @ivillar

/-!
# A second difference of the integrated Chebyshev sum dominates the central mass

With `F n = ∑_{k < n} Λ k * (n - k)`, the second difference `F (a + 2h) - 2 F (a + h) + F a` equals
`∑_{k < a + 2h} Λ k * w k`, where `w k = (a + 2h - k)⁺ - 2 (a + h - k)⁺ + (a - k)⁺` is the tent
function of height `h` centred at `a + h`. The weight `w` is nonnegative and at least `h / 2` on the
central window, and `Λ` is nonnegative.
-/

namespace CramerTentStep

open Real Filter ArithmeticFunction Finset

lemma extend_sum (g : ℕ → ℝ) {n N : ℕ} (hn : n ≤ N) :
    ∑ k ∈ range n, g k * ((n : ℝ) - k) = ∑ k ∈ range N, g k * max ((n : ℝ) - k) 0 := by
  have h1 : ∑ k ∈ range n, g k * ((n : ℝ) - k) = ∑ k ∈ range n, g k * max ((n : ℝ) - k) 0 := by
    refine sum_congr rfl (fun k hk => ?_)
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast (mem_range.mp hk).le
    rw [max_eq_left (by linarith)]
  rw [h1]
  refine sum_subset (range_subset_range.mpr hn) (fun k _ hk => ?_)
  have hk' : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (fun h => hk (mem_range.mpr h))
  rw [max_eq_right (by linarith), mul_zero]

theorem tent_general (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (a h : ℕ) :
    (h : ℝ) / 2 * (∑ k ∈ Ico (a + h - h / 2) (a + h + h / 2), g k) ≤
      (∑ k ∈ range (a + 2 * h), g k * (((a + 2 * h : ℕ) : ℝ) - k)) -
        2 * (∑ k ∈ range (a + h), g k * (((a + h : ℕ) : ℝ) - k)) +
        ∑ k ∈ range a, g k * ((a : ℝ) - k) := by
  have hH : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hm1 : 2 * ((h / 2 : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.mul_div_le h 2
  rw [extend_sum g (le_refl (a + 2 * h)), extend_sum g (show a + h ≤ a + 2 * h by omega),
    extend_sum g (show a ≤ a + 2 * h by omega)]
  have hcomb : (∑ k ∈ range (a + 2 * h), g k * max (((a + 2 * h : ℕ) : ℝ) - k) 0) -
      2 * (∑ k ∈ range (a + 2 * h), g k * max (((a + h : ℕ) : ℝ) - k) 0) +
      ∑ k ∈ range (a + 2 * h), g k * max ((a : ℝ) - k) 0 =
      ∑ k ∈ range (a + 2 * h), g k * (max (((a + 2 * h : ℕ) : ℝ) - k) 0 -
        2 * max (((a + h : ℕ) : ℝ) - k) 0 + max ((a : ℝ) - k) 0) := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  rw [hcomb]
  have hw0 : ∀ k : ℕ, 0 ≤ max (((a + 2 * h : ℕ) : ℝ) - k) 0 -
      2 * max (((a + h : ℕ) : ℝ) - k) 0 + max ((a : ℝ) - k) 0 := by
    intro k
    push_cast
    simp only [max_def]
    split_ifs <;> linarith
  have hsub : Ico (a + h - h / 2) (a + h + h / 2) ⊆ range (a + 2 * h) := by
    intro k hk
    rw [mem_Ico] at hk
    rw [mem_range]
    have := Nat.div_le_self h 2
    omega
  calc (h : ℝ) / 2 * (∑ k ∈ Ico (a + h - h / 2) (a + h + h / 2), g k)
      = ∑ k ∈ Ico (a + h - h / 2) (a + h + h / 2), g k * ((h : ℝ) / 2) := by
        rw [mul_sum]
        exact sum_congr rfl (fun k _ => by ring)
    _ ≤ ∑ k ∈ Ico (a + h - h / 2) (a + h + h / 2), g k *
          (max (((a + 2 * h : ℕ) : ℝ) - k) 0 - 2 * max (((a + h : ℕ) : ℝ) - k) 0 +
            max ((a : ℝ) - k) 0) := by
        refine sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left ?_ (hg k))
        rw [mem_Ico] at hk
        have hx1 : (a : ℝ) + h - ((h / 2 : ℕ) : ℝ) ≤ k := by
          have h1 : a + h ≤ k + h / 2 := by omega
          have h2 : ((a + h : ℕ) : ℝ) ≤ ((k + h / 2 : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          linarith
        have hx2 : (k : ℝ) + 1 ≤ (a : ℝ) + h + ((h / 2 : ℕ) : ℝ) := by
          have h1 : k + 1 ≤ a + h + h / 2 := by omega
          have h2 : ((k + 1 : ℕ) : ℝ) ≤ ((a + h + h / 2 : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          linarith
        push_cast
        simp only [max_def]
        split_ifs <;> linarith
    _ ≤ ∑ k ∈ range (a + 2 * h), g k *
          (max (((a + 2 * h : ℕ) : ℝ) - k) 0 - 2 * max (((a + h : ℕ) : ℝ) - k) 0 +
            max ((a : ℝ) - k) 0) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (hg k) (hw0 k))

theorem tent :
  let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
  ∀ a h : ℕ, (h : ℝ)/2 * (∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)) ≤
    F (a+2*h) - 2*F (a+h) + F a := by
  intro F a h
  exact tent_general (fun k => (Λ k : ℝ)) (fun k => vonMangoldt_nonneg) a h

end CramerTentStep

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1.H2 :=
  CramerTentStep.tent
