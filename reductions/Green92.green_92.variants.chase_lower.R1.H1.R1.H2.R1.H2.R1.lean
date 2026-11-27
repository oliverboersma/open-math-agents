import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1

/-!
Split the weighted second moment in Chase, arXiv:1905.03031v2,
Sections 3.3 and 3.4. Nearby insertion positions can be estimated
in absolute value. Separated positions require cancellation.
The normalizing binomial coefficient is the alternating contribution
from the parent reduction and is the same in both steps.
-/

namespace OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1

open Finset Filter Real
open scoped Pointwise

private theorem split_square (s : Finset ℕ) (a : ℕ → ℝ) (q : ℝ) :
    (∑ j ∈ s, a j)^2 / q ≤
      (∑ p ∈ (s.product s).filter (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
        |a p.1 * a p.2 / q|) +
      (∑ p ∈ (s.product s).filter (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),
        a p.1 * a p.2 / q) := by
  classical
  have heq : (∑ j ∈ s, a j)^2 / q =
      ∑ p ∈ s.product s, a p.1 * a p.2 / q := by
    change _ = ∑ p ∈ s ×ˢ s, a p.1 * a p.2 / q
    rw [← Finset.sum_div, Finset.sum_product, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [heq, ← Finset.sum_filter_add_sum_filter_not (p := fun p : ℕ × ℕ =>
    p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)]
  exact add_le_add (Finset.sum_le_sum fun (p : ℕ × ℕ) _ => le_abs_self (a p.1 * a p.2 / q)) le_rfl

def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, n % 4 = 3 →
    let k := n / 4
    let F (a : ℕ) (w : List Bool) := (a + (w.zip w.tail).count (false, true)).choose w.length
    let B (w : List Bool) := F (2*k+1) w
    let P (b : ℕ) (w : List Bool) (j : ℕ) := if w[j]? = some true then
      F b (w.take j) * F (2*k+1-b) (w.drop (j+1)) else 0
    let A (w : List Bool) (j : ℕ) := (P k w j : ℝ) - P (k+1) w j
    let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m → Bool)).image List.ofFn
    let E (w : List Bool) := |(w.length : ℝ)-2*k| ≤ sqrt k*log k ∧
      |(((w.zip w.tail).count (false,true) : ℕ) : ℝ)-2*k/3| ≤ sqrt k*log k
    (∑ w ∈ U.filter E,
      ∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
        |A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))|) ≤
      C * (log n)^7 / (n : ℝ)^(3/2 : ℝ)

def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, n % 4 = 3 →
    let k := n / 4
    let F (a : ℕ) (w : List Bool) := (a + (w.zip w.tail).count (false, true)).choose w.length
    let B (w : List Bool) := F (2*k+1) w
    let P (b : ℕ) (w : List Bool) (j : ℕ) := if w[j]? = some true then
      F b (w.take j) * F (2*k+1-b) (w.drop (j+1)) else 0
    let A (w : List Bool) (j : ℕ) := (P k w j : ℝ) - P (k+1) w j
    let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m → Bool)).image List.ofFn
    let E (w : List Bool) := |(w.length : ℝ)-2*k| ≤ sqrt k*log k ∧
      |(((w.zip w.tail).count (false,true) : ℕ) : ℝ)-2*k/3| ≤ sqrt k*log k
    (∑ w ∈ U.filter E,
      ∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),
        A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))) ≤
      C * (log n)^7 / (n : ℝ)^(3/2 : ℝ)

theorem main : H1 → H2 → OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1.H2 := by
  classical
  rintro ⟨C₁, hC₁, hnear⟩ ⟨C₂, hC₂, hfar⟩
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hnear, hfar] with n hn₁ hn₂
  intro hn k F B D U E
  specialize hn₁ hn
  specialize hn₂ hn
  let P (b : ℕ) (w : List Bool) (j : ℕ) := if w[j]? = some true then
    F b (w.take j) * F (2*k+1-b) (w.drop (j+1)) else 0
  let A (w : List Bool) (j : ℕ) : ℝ := (P k w j : ℝ) - P (k+1) w j
  let L (w : List Bool) : ℝ :=
      ∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
        |A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))|
  let R (w : List Bool) : ℝ :=
      ∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),
        A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))
  change (∑ w ∈ U.filter E, L w) ≤ _ at hn₁
  change (∑ w ∈ U.filter E, R w) ≤ _ at hn₂
  have hp (w : List Bool) : ((D k w : ℝ) - D (k+1) w) = ∑ j ∈ range w.length, A w j := by
    simp only [D, A, P, Nat.cast_sum, Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ U.filter E, (L w + R w) := by
      apply Finset.sum_le_sum
      intro w _
      rw [hp]
      exact split_square _ _ _
    _ = (∑ w ∈ U.filter E, L w) + (∑ w ∈ U.filter E, R w) := Finset.sum_add_distrib
    _ ≤ _ := by
      simpa only [add_mul, add_div] using add_le_add hn₁ hn₂

end OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1
