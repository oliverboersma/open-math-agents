import Mathlib

/-!
# OEIS A121669

Count integers up to 10^n with decimal digit sum 19 that are divisible
by 19 and contain the consecutive digits 19. Each integer below 10^n is
represented once by its n decimal places, starting at the units place
and allowing leading zeros. Padding does not change any of the three
conditions. The endpoint 10^n itself has digit sum 1.

In 2022 Charles R. Greathouse IV conjectured that this count is
approximately k(n−1)(n−2)^(n−2), with k about e/(19e−19). The statement
allows any positive asymptotic constant.

Source: https://oeis.org/A121669
-/

namespace OMA.S_oeis_a121669

abbrev Word (n : ℕ) := Fin n → Fin 10

def qualifies {n : ℕ} (w : Word n) : Prop :=
  (∑ i, (w i : ℕ)) = 19 ∧ 19 ∣ ∑ i, (w i : ℕ)*10^(i : ℕ) ∧
  ∃ i j : Fin n, (j : ℕ) = (i : ℕ)+1 ∧ w i = 9 ∧ w j = 1

noncomputable def count (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : Word n => qualifies w)).card

def proposed (n : ℕ) : ℝ := (n-1 : ℕ) * ((n-2 : ℕ) : ℝ)^(n-2)

open Filter Topology in
theorem main : ∃ k : ℝ, 0 < k ∧ Tendsto (fun n : ℕ => (count n : ℝ)/proposed n) atTop (𝓝 k) := by
  sorry

end OMA.S_oeis_a121669
