import Mathlib

/-!
# Distribution and upper bound of mimic numbers

Source: https://www.openproblemgarden.org/op/distribution_and_upper_bound_of_mimic_numbers
Definitions 1 and 2 of Bhattacharyya, Bandyopadhyay and Maulik,
“Non-primes are recursively divisible,” Acta Universitatis Apulensis 19 (2009).
Credit: @rleshner

M is a radix of at least two. The source theorem assumes positive D ≤ M.
Evaluating the base-M digit polynomial at M-D is the mimic step. The mimic
number is the first hitting time of D, when it exists. The two requested
quantities are the exact histogram on any initial window and the support
of possible hitting times for positive multiples of D.
-/

namespace OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers

def step (M D n : ℕ) : ℕ := Nat.ofDigits (M-D) (M.digits n)
def First (M D h n : ℕ) : Prop :=
  (step M D)^[h] n = D ∧ ∀ j < h, (step M D)^[j] n ≠ D

open scoped Polynomial

/-- The coefficient at t counts inputs below N whose first step has value t. -/
noncomputable def windowPoly (M D N : ℕ) : ℕ[X] :=
  ∑ n ∈ Finset.range N, Polynomial.X ^ step M D n

noncomputable def digitPoly (r : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range r, Polynomial.X ^ i

open scoped Classical in
/-- A digit recursion for the entire histogram, on arbitrary initial windows.
The correction excludes an input already at the target at time zero. -/
def HistogramLaw (M D : ℕ) : Prop :=
  (∀ q r : ℕ, r ≤ M →
    windowPoly M D (M*q+r) =
      (windowPoly M D q).comp (Polynomial.X ^ (M-D)) * digitPoly M +
        Polynomial.X ^ ((M-D) * step M D q) * digitPoly r) ∧
  (∀ N h : ℕ,
    ((Finset.range N).filter (First M D (h+1))).card =
      (∑ t ∈ (Finset.range N).filter (First M D h), (windowPoly M D N).coeff t) -
        (if D < N ∧ First M D h (step M D D) then 1 else 0))

theorem main : ∀ M D : ℕ, 1 < M → 0 < D → D ≤ M →
    HistogramLaw M D ∧
    (∀ n h, First M D h n → 0 < n ∧ D ∣ n) ∧
    ((D = M ∨ D < M-D) → ∀ n h, D ∣ n → (First M D h n ↔ n = D ∧ h = 0)) ∧
    ((D < M ∧ M-D ≤ D) →
      (∀ n, 0 < n → D ∣ n → ∃ h, First M D h n) ∧
      (∀ h, ∃ n, D ≤ n ∧ D ∣ n ∧ First M D h n)) ∧
    (2 ≤ M-D → ∀ h, ∃ N, ∀ n, First M D h n → n < N) ∧
    (M-D = 1 → ∀ h K, ∃ n, K < n ∧ D ∣ n ∧ First M D (h+1) n) := by
  sorry

end OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers
