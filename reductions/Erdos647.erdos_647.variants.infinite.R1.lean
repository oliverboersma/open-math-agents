import FormalConjectures.ErdosProblems.«647»

/-! An exact search criterion for the fixed-window variant of Erdős 647.
For each window length it suffices to find one integer parameter above that length.
Six divisor tests become primality tests on a single progression. -/

namespace OMA.R_Erdos647_erdos_647_variants_infinite_R1

open ArithmeticFunction.sigma

/-- For each length, find one sufficiently large parameter with the six required
prime cofactors and the divisor bounds at the remaining offsets. -/
def H1 : Prop :=
  ∀ K : ℕ, ∃ t : ℕ, K < t ∧
    (∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime) ∧
    ∀ j : ℕ, 0 < j → j < K → j ∉ ({1, 2, 3, 4, 6, 12} : Finset ℕ) →
      (2520 * t - j).divisors.card ≤ j + 2

/-- Beyond the small exceptions, the six selected divisor bounds hold precisely
on multiples of 2520 whose six indicated cofactors are prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 24 < n →
    ((∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (n - j).divisors.card ≤ j + 2) ↔
      ∃ t : ℕ, 0 < t ∧ n = 2520 * t ∧
        ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime)

/-- The search criterion loses no solutions at infinity. -/
lemma candidates_of_windows (classify : H2)
    (windows : type_of% @Erdos647.erdos_647.variants.infinite) : H1 := by
  intro K
  let L := max K 13
  obtain ⟨n, hn, hlarge⟩ := (windows L).exists_gt (2520 * K + L + 24)
  change (⨆ m : Set.Ioo (n - L) n, (m : ℕ) + σ 0 m) ≤ n + 2 at hn
  have hshift (j : ℕ) (hj : 0 < j) (hjl : j < L) :
      (n - j).divisors.card ≤ j + 2 := by
    let m : Set.Ioo (n - L) n := ⟨n - j, by constructor <;> omega⟩
    let f := fun x : Set.Ioo (n - L) n => (x : ℕ) + σ 0 x
    have h := (le_ciSup (f := f) (Set.finite_range f).bddAbove m).trans hn
    change (n - j) + σ 0 (n - j) ≤ n + 2 at h
    rw [ArithmeticFunction.sigma_zero_apply] at h
    omega
  have hhead : ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (n - j).divisors.card ≤ j + 2 := by
    intro j hj
    have h13 : 13 ≤ L := le_max_right _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    apply hshift <;> omega
  obtain ⟨t, _, heq, hprimes⟩ := (classify n (by omega)).1 hhead
  refine ⟨t, by omega, hprimes, ?_⟩
  intro j hj hjk _
  rw [← heq]
  exact hshift j hj (lt_of_lt_of_le hjk (le_max_left _ _))

theorem main : H1 → H2 → type_of% @Erdos647.erdos_647.variants.infinite := by
  intro candidates classify k
  apply Set.infinite_of_forall_exists_gt
  intro bound
  obtain ⟨t, ht, hprimes, hrest⟩ := candidates (max k bound)
  have hk := le_max_left k bound
  have hb := le_max_right k bound
  have hhead := (classify (2520 * t) (by omega)).2 ⟨t, by omega, rfl, hprimes⟩
  refine ⟨2520 * t, ?_, by omega⟩
  change (⨆ m : Set.Ioo (2520 * t - k) (2520 * t), (m : ℕ) + σ 0 m) ≤ 2520 * t + 2
  apply ciSup_le'
  rintro ⟨m, hlow, hhigh⟩
  change m + σ 0 m ≤ 2520 * t + 2
  rw [ArithmeticFunction.sigma_zero_apply]
  let j := 2520 * t - m
  have hj : 0 < j := by dsimp [j]; omega
  have hjk : j < max k bound := by dsimp [j]; omega
  have hcount : (2520 * t - j).divisors.card ≤ j + 2 := by
    by_cases hm : j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ)
    · exact hhead j hm
    · exact hrest j hj hjk hm
  have heq : 2520 * t - j = m := by dsimp [j]; omega
  rw [heq] at hcount
  dsimp [j] at hcount
  omega

end OMA.R_Erdos647_erdos_647_variants_infinite_R1
