import FormalConjectures.ErdosProblems.«161»

-- Reduction Erdos161.erdos_161.parts.ii.R2 of Erdős Problem 161 — ii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Split of the density-comparison question at the pivot density `1/4`.
Write `F_t(n, γ)` for the least `m` such that some red/blue colouring of the `t`-subsets of `Fin n`
gives every vertex set of size at least `m` a positive and at least `γ`-fraction of edges of
each colour (this is `Hypergraph.balancedColoringThreshold`, inlined below).

* `H1` (high-density regime): for `γ ∈ [1/4, 1/2)`, `F_t(·, γ) = O(F_t(·, 1/4))`.
* `H2` (low-density regime): for `γ ∈ (0, 1/4]`, `F_t(·, 1/4) = O(F_t(·, γ))`.

The remaining comparisons follow from monotonicity of `F_t(n, γ)` in `γ`, which is proved here.
-/

namespace OMA.R_Erdos161_erdos_161_parts_ii_R2

open Filter Asymptotics

private lemma threshold_feasible (n t : ℕ) (α : ℝ) :
    ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n),
      Hypergraph.balancedColoringThreshold n t α ≤ X.card →
      ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e ↦ c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤ ((X.powersetCard t).filter (fun e ↦ c e = b)).card := by
  classical
  unfold Hypergraph.balancedColoringThreshold
  have := Nat.sInf_mem (s := {m | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
    0 < count ∧ α * (X.card.choose t : ℝ) ≤ count}) ⟨n + 1, fun _ ↦ false, fun X hX ↦ by
      have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
      omega⟩
  obtain ⟨c, hc⟩ := this
  refine ⟨c, fun X hX b ↦ ?_⟩
  have h := hc X hX b
  simp only at h
  convert h using 3

private lemma threshold_mono_density (n t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    Hypergraph.balancedColoringThreshold n t α ≤ Hypergraph.balancedColoringThreshold n t β := by
  classical
  obtain ⟨col, hcol⟩ := threshold_feasible n t β
  unfold Hypergraph.balancedColoringThreshold
  apply Nat.sInf_le
  refine ⟨col, fun X hm b ↦ ?_⟩
  obtain ⟨hpos, hβ⟩ := hcol X hm b
  simp only
  constructor
  · convert hpos using 2
  · refine (mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)).trans (le_of_eq_of_le rfl ?_)
    convert hβ using 3

private lemma bigO_of_le (t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n t α : ℝ)) =O[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n t β : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using
    (show (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤
      Hypergraph.balancedColoringThreshold n t β by exact_mod_cast threshold_mono_density n t hαβ)

open scoped Classical in
/-- High-density regime: densities in `[1/4, 1/2)` are no harder than density `1/4`. -/
def H1 : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ γ : ℝ, 1 / 4 ≤ γ → γ < 1 / 2 →
    (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
        ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ γ * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ)) =O[atTop]
    (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
        ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ (1 / 4 : ℝ) * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ))

open scoped Classical in
/-- Low-density regime: density `1/4` is no harder than any density in `(0, 1/4]`. -/
def H2 : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 4 →
    (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
        ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ (1 / 4 : ℝ) * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ)) =O[atTop]
    (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
        ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ γ * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ))

theorem main : H1 → H2 → type_of% @Erdos161.erdos_161.parts.ii := by
  intro h1 h2 t ht α β hα0 hα1 hβ0 hβ1
  have key : ∀ γ : ℝ, 0 < γ → γ < 1 / 2 →
      (fun n ↦ (Hypergraph.balancedColoringThreshold n t γ : ℝ)) =Θ[atTop]
        (fun n ↦ (Hypergraph.balancedColoringThreshold n t (1 / 4) : ℝ)) := by
    intro γ h0 h12
    rcases le_total (1 / 4 : ℝ) γ with hq | hq
    · exact ⟨h1 t ht γ hq h12, bigO_of_le t hq⟩
    · exact ⟨bigO_of_le t hq, h2 t ht γ h0 hq⟩
  exact (key α hα0 hα1).trans (key β hβ0 hβ1).symm

end OMA.R_Erdos161_erdos_161_parts_ii_R2
