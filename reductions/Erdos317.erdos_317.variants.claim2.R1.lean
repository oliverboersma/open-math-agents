import FormalConjectures.ErdosProblems.«317»

/-! Reduction by @Burntgogi. On an interval where the least common multiple stays
constant, appending zero coefficients preserves both sides of a putative equality.
It therefore suffices to exclude equality just before each sufficiently large
prime power. The weak inequality is the proved companion lemma in the source. -/

open Finset Filter

namespace OMA.R_Erdos317_erdos_317_variants_claim2_R1

/-- Every positive index extends to a prime-power predecessor with the same LCM. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ u : ℕ, n < u ∧ IsPrimePow u ∧
    (Icc 1 n).lcm id = (Icc 1 (u - 1)).lcm id

/-- At large prime-power predecessors, signed reciprocal sums avoid the critical magnitude. -/
def H2 : Prop :=
  ∀ᶠ u : ℕ in atTop, IsPrimePow u → ∀ δ : Fin (u - 1) → ℚ,
    δ '' Set.univ ⊆ {-1, 0, 1} →
    |∑ k, δ k / (k + 1)| ≠ 1 / ((Icc 1 (u - 1)).lcm id : ℕ)

lemma extend_by_zero {n m : ℕ} (hnm : n ≤ m) (δ : Fin n → ℚ)
    (hδ : δ '' Set.univ ⊆ {-1, 0, 1}) :
    ∃ ε : Fin m → ℚ, ε '' Set.univ ⊆ {-1, 0, 1} ∧
      (∑ k, ε k / (k + 1)) = ∑ k, δ k / (k + 1) := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨δ, hδ, rfl⟩
  | succ m _ ih =>
    obtain ⟨ε, hε, hsum⟩ := ih
    refine ⟨Fin.snoc ε 0, ?_, ?_⟩
    · rintro _ ⟨i, _, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa using hε ⟨j, trivial, rfl⟩
    · simpa [Fin.sum_univ_castSucc] using hsum

theorem main : H1 → H2 → type_of% @Erdos317.erdos_317.variants.claim2 := by
  intro hplateau hendpoint
  obtain ⟨N, hN⟩ := eventually_atTop.1 hendpoint
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1,
    Erdos317.claim2_inequality] with n hNn hn hweak
  intro δ hδ hnonzero
  obtain ⟨u, hnu, hu, hL⟩ := hplateau n hn
  obtain ⟨ε, hε, hsum⟩ := extend_by_zero (m := u - 1) (by omega) δ hδ
  have hne := hN u (by omega) hu ε hε
  rw [hsum, ← hL] at hne
  exact lt_of_le_of_ne (hweak δ hδ hnonzero) hne.symm

end OMA.R_Erdos317_erdos_317_variants_claim2_R1
