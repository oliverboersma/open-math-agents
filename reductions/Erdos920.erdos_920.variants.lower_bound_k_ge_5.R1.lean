import FormalConjectures.ErdosProblems.«920»
import Mathlib

/-! Bradač's Ramsey lower bound supplies an independent-set obstruction.
The passage from a graph to its chromatic number adapts the four-clique
argument of @hyprspacecoyote and @ivillar in this repository. -/
namespace OMA.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1
open Filter Asymptotics SimpleGraph

/-- Bradač's polynomial-over-polylogarithm lower bound for each fixed clique size. -/
def H1 : Prop := ∀ k : ℕ, 5≤k → ∃ a : ℕ, ∃ C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ m : ℕ in atTop,
  C*(m:ℝ)^(k-1)/(Real.log m)^a ≤ (SimpleGraph.classicalRamsey k m : ℝ)

/-- Numerical inversion, with no graphs in the statement. -/
def H2 : Prop := ∀ d : ℕ, 2≤d → ∀ a C : ℝ, 0<a → 0<C → ∀ R F : ℕ → ℕ,
  (∀ᶠ m : ℕ in atTop, C*(m:ℝ)^d/(Real.log m)^a ≤ (R m:ℝ)) →
  (∀ n m : ℕ, 0<n → n<R m → (n:ℝ)/m ≤ F n) →
  (fun n : ℕ => (n:ℝ)^(1-1/(d:ℝ))/(Real.log n)^(a/(d:ℝ))) =O[atTop] (fun n => (F n:ℝ))

lemma chi_le_f {k : ℕ} (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree k) :
    G.chromaticNumber ≤ (Erdos920.f k n : ℕ∞) := by
  have hle : G.chromaticNumber ≤ (n : ℕ∞) := by
    have := G.chromaticNumber_le_card
    simpa using this
  have hfin : G.chromaticNumber ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.1 hfin
  have hbdd : BddAbove {x : ℕ | ∃ G : SimpleGraph (Fin n), ∃ (_ : G.CliqueFree k),
      G.chromaticNumber = ↑x} := by
    refine ⟨n, fun y ⟨H, _, hH⟩ => ?_⟩
    have := H.chromaticNumber_le_card
    rw [hH] at this
    simpa using this
  have hmem : x ∈ {x : ℕ | ∃ G : SimpleGraph (Fin n), ∃ (_ : G.CliqueFree k),
      G.chromaticNumber = ↑x} := ⟨G, hG, hx.symm⟩
  rw [← hx]
  exact_mod_cast le_csSup hbdd hmem

/-- `χ(G) ≥ n / α(G)` in real form. -/
lemma n_div_le_f {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree k)
    (m : ℕ) (hα : G.indepNum < m) : (n : ℝ) / m ≤ Erdos920.f k n := by
  have hα1 : 1 ≤ G.indepNum := by
    have : ({⟨0, by omega⟩} : Finset (Fin n)).card ≤ G.indepNum := by
      apply IsIndepSet.card_le_indepNum
      intro u hu v hv huv
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
      exact absurd (hu.trans hv.symm) huv
    simpa using this
  have h1 := G.card_div_indepNum_le_chromaticNumber
  have h2 := h1.trans (chi_le_f n G hG)
  have h3 : ⌈((Nat.card (Fin n) : ℚ≥0) / (G.indepNum : ℚ≥0))⌉₊ ≤ Erdos920.f k n := by
    exact_mod_cast h2
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have h4 : ((n : ℚ≥0) / (G.indepNum : ℚ≥0)) ≤ Erdos920.f k n :=
    (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have h5 : (n : ℝ) / G.indepNum ≤ Erdos920.f k n := by
    have := (NNRat.cast_le (K := ℝ)).2 h4
    push_cast at this
    exact this
  have hmR : (G.indepNum : ℝ) ≤ m := by exact_mod_cast hα.le
  have hαpos : (0 : ℝ) < G.indepNum := by exact_mod_cast hα1
  refine le_trans ?_ h5
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hαpos hmR


lemma witness (k m N : ℕ) (hN : N<SimpleGraph.classicalRamsey k m) : ∃ G : SimpleGraph (Fin N), G.CliqueFree k ∧ G.indepNum < m := by
  unfold SimpleGraph.classicalRamsey SimpleGraph.graphRamsey at hN
  have hnot := Nat.notMem_of_lt_sInf hN
  simp only [Set.mem_setOf_eq, not_forall, not_or] at hnot
  obtain ⟨C, h4, hm⟩ := hnot
  refine ⟨C, ?_, ?_⟩
  · by_contra h
    exact h4 ((SimpleGraph.not_cliqueFree_iff_top_isContained k).mp h)
  · by_contra h
    rw [not_lt] at h
    have hfree : Cᶜ.CliqueFree m := by
      by_contra h'
      exact hm ((SimpleGraph.not_cliqueFree_iff_top_isContained m).mp h')
    have hfree' : Cᶜ.CliqueFree Cᶜ.cliqueNum := by
      apply hfree.mono
      rw [SimpleGraph.cliqueNum_compl]
      exact h
    obtain ⟨s, hs⟩ := Cᶜ.exists_isNClique_cliqueNum
    exact hfree' s hs

theorem main : H1 → H2 → type_of% @Erdos920.erdos_920.variants.lower_bound_k_ge_5 := by
  intro ramsey inv k hk
  obtain ⟨a,C,ap,cp,lb⟩ := ramsey k hk
  have bridge (n m : ℕ) (hn : 0<n) (cross : n<SimpleGraph.classicalRamsey k m) : (n:ℝ)/m ≤ Erdos920.f k n := by
    obtain ⟨G,hG,ind⟩ := witness k m n cross
    exact n_div_le_f _ hn G hG m ind
  have cast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
  have ar : (0:ℝ)<a := by exact_mod_cast ap
  have dr : (1:ℝ)≤(k-1:ℕ) := by exact_mod_cast (show 1≤k-1 by omega)
  have expBound : (a:ℝ)/(k-1:ℕ)≤a := div_le_self ar.le dr
  refine ⟨a,ap,?_⟩
  have lb' : ∀ᶠ m : ℕ in atTop, C*(m:ℝ)^(k-1)/(Real.log m)^(a:ℝ) ≤ (SimpleGraph.classicalRamsey k m:ℝ) := by
    simpa only [Real.rpow_natCast] using lb
  have res := inv (k-1) (by omega) (a:ℝ) C ar cp (SimpleGraph.classicalRamsey k) (Erdos920.f k) lb' bridge
  apply IsBigO.trans _ res
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 3] with n hn
  have nr : (3:ℝ)≤n := by exact_mod_cast hn
  have lg : 1≤Real.log n := by
    rw [←Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have den := Real.rpow_le_rpow_of_exponent_le lg expBound
  rw [Real.rpow_natCast] at den
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(n:ℝ)^(1-1/((k:ℝ)-1))/(Real.log n)^a),
    abs_of_nonneg (by positivity : 0≤(n:ℝ)^(1-1/((k-1:ℕ):ℝ))/(Real.log n)^((a:ℝ)/((k-1:ℕ):ℝ))),one_mul]
  rw [cast] at den ⊢
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _) den
end OMA.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1
