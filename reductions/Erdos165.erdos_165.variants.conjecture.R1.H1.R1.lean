import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1

/-!
Copyright 2026 Wesley Pegden. Licensed under Apache License 2.0.
Source: https://github.com/wpegden/twobites/tree/d9d2f5562c4b15e50a9baa2a597357cb4ea87a23
Trellis autoformalization, with Codex-directed manual repairs.
Mathematical result: Zion Hefty, Paul Horn, Dylan King, Florian Pfender,
"Improving R(3,k) in just two bites", arXiv:2510.19718.
Adaptation, reduction, and Lean 4.33.1 compatibility: Hanan Beer (@hananzlt).
Parent reduction: @skytracker404.
Ramsey-interface lemmas reused from @ysanatomic, PR1323, commit
8f2b3b6266c64207844faee4ca45175fb06c5c76 (Erdos812 lower bound).
Changes: selected mathematical dependencies; exposed graph construction and analytic inversion;
added the bridge to Mathlib's classicalRamsey and the official target.
-/

namespace OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1

/-- Hefty–Horn–King–Pfender triangle-free construction with the stated
independence bound. This is the combinatorial input. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      ∀ I : Finset (Fin n), G.IsIndepSet (↑I : Set (Fin n)) →
        (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))

/-- Analytic inversion of the independence threshold, including integer rounding. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → η < (1 / 2 : ℝ) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ n0 : ℕ, ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ N : ℕ, n0 ≤ N ∧
        ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) ≤ (N : ℝ) ∧
        (1 + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) < (k : ℝ)

/-- Finite Ramsey witnesses are smaller than the Ramsey number.
The elementary interface proof is adapted from @ysanatomic, PR1323. -/
lemma witness_lt_classicalRamsey {N k : ℕ} (G : SimpleGraph (Fin N))
    (htriangle : G.CliqueFree 3) (hindep : G.IndepSetFree k) :
    N < SimpleGraph.classicalRamsey 3 k := by
  classical
  let GraphRamseyOn (v a b : ℕ) : Prop :=
    ∀ G : SimpleGraph (Fin v), ¬ (G.CliqueFree a ∧ (Gᶜ).CliqueFree b)

  let Mono {v : ℕ} (c : Finset (Fin v) → Bool) (color : Bool)
      (a : ℕ) (S : Finset (Fin v)) : Prop :=
    S.card = a ∧ ∀ e ⊆ S, e.card = 2 → c e = color

  have isNClique_iff_mono {v a : ℕ} {G : SimpleGraph (Fin v)}
      {c : Finset (Fin v) → Bool} {color : Bool} {S : Finset (Fin v)}
      (h : ∀ x y, x ≠ y → (G.Adj x y ↔ c {x, y} = color)) :
      G.IsNClique a S ↔ Mono c color a S := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · rintro ⟨hc, hcard⟩
      refine ⟨hcard, ?_⟩
      intro e he hecard
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
      apply (h x y hxy).mp
      exact hc (he (by simp)) (he (by simp)) hxy
    · rintro ⟨hcard, hc⟩
      refine ⟨?_, hcard⟩
      intro x hx y hy hxy
      exact (h x y hxy).mpr (hc {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (Finset.card_pair hxy))

  have compl_adj_iff_false {v : ℕ} {G : SimpleGraph (Fin v)}
      {c : Finset (Fin v) → Bool}
      (h : ∀ x y, x ≠ y → (G.Adj x y ↔ c {x, y} = true)) :
      ∀ x y, x ≠ y → ((Gᶜ).Adj x y ↔ c {x, y} = false) := by
    intro x y hxy
    simp [h x y hxy, SimpleGraph.compl_adj, hxy]

  have graphRamseyOn_iff_mono (v a b : ℕ) :
      GraphRamseyOn v a b ↔ ∀ c : Finset (Fin v) → Bool,
        (∃ S, Mono c true a S) ∨ (∃ S, Mono c false b S) := by
    classical
    constructor
    · intro h c
      let G : SimpleGraph (Fin v) :=
        { Adj := fun x y ↦ x ≠ y ∧ c {x, y} = true
          symm := ⟨by
            intro x y hxy
            exact ⟨hxy.1.symm, by rw [Finset.pair_comm y x]; exact hxy.2⟩⟩
          loopless := ⟨fun _ hxx ↦ hxx.1 rfl⟩ }
      have hG (x y : Fin v) (hxy : x ≠ y) : G.Adj x y ↔ c {x, y} = true := by
        exact and_iff_right hxy
      have hc := h G
      rw [SimpleGraph.CliqueFree, SimpleGraph.CliqueFree, not_and_or] at hc
      push Not at hc
      obtain ⟨S, hS⟩ | ⟨S, hS⟩ := hc
      · exact Or.inl ⟨S, (isNClique_iff_mono hG).mp hS⟩
      · exact Or.inr ⟨S, (isNClique_iff_mono (compl_adj_iff_false hG)).mp hS⟩
    · intro h G ⟨hG, hGc⟩
      let c (e : Finset (Fin v)) : Bool := decide (G.IsClique (e : Set (Fin v)))
      have hc (x y : Fin v) (hxy : x ≠ y) : G.Adj x y ↔ c {x, y} = true := by
        simp [c, hxy]
      obtain ⟨S, hS⟩ | ⟨S, hS⟩ := h c
      · exact hG S ((isNClique_iff_mono hc).mpr hS)
      · exact hGc S ((isNClique_iff_mono (compl_adj_iff_false hc)).mpr hS)

  have classicalRamsey_eq_sInf (a b : ℕ) :
      SimpleGraph.classicalRamsey a b = sInf {v : ℕ | GraphRamseyOn v a b} := by
    classical
    simp only [SimpleGraph.classicalRamsey, SimpleGraph.graphRamsey,
      GraphRamseyOn, not_and_or, SimpleGraph.not_cliqueFree_iff_top_isContained]

  have graphRamseyOn_nonempty (a b : ℕ) :
      {v : ℕ | GraphRamseyOn v a b}.Nonempty := by
    refine ⟨Nat.choose (b + a) b, (graphRamseyOn_iff_mono _ _ _).mpr ?_⟩
    intro c
    obtain ⟨S, _, hcard, hS⟩ | ⟨S, _, hcard, hS⟩ :=
      Combinatorics.Diagonal.hasRamseyProperty_choose b a c Finset.univ (by simp)
    · exact Or.inr ⟨S, hcard, hS⟩
    · exact Or.inl ⟨S, hcard, hS⟩

  have graphRamseyOn_mono {v w a b : ℕ} (hvw : v ≤ w) :
      GraphRamseyOn v a b → GraphRamseyOn w a b := by
    intro h G ⟨hG, hGc⟩
    let e : Fin v ↪ Fin w := Fin.castLEEmb hvw
    let H : SimpleGraph (Fin v) := G.comap e
    let emb : H ↪g G := SimpleGraph.Embedding.comap e G
    let embc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv emb
    exact h H ⟨hG.comap emb.isContained, hGc.comap embc.isContained⟩

  have classicalRamsey_le_iff {v a b : ℕ} :
      SimpleGraph.classicalRamsey a b ≤ v ↔ GraphRamseyOn v a b := by
    rw [classicalRamsey_eq_sInf]
    exact ⟨fun hv ↦ graphRamseyOn_mono hv (Nat.sInf_mem (graphRamseyOn_nonempty a b)),
      fun hv ↦ Nat.sInf_le (show v ∈ {v : ℕ | GraphRamseyOn v a b} from hv)⟩

  have lt_classicalRamsey_iff {v a b : ℕ} :
      v < SimpleGraph.classicalRamsey a b ↔
        ∃ G : SimpleGraph (Fin v), G.CliqueFree a ∧ (Gᶜ).CliqueFree b := by
    rw [← not_le, classicalRamsey_le_iff]
    dsimp [GraphRamseyOn]
    push Not
    rfl
  exact lt_classicalRamsey_iff.mpr ⟨G, htriangle, G.cliqueFree_compl.mpr hindep⟩

theorem main : H1 → H2 →
    OMA.R_Erdos165_erdos_165_variants_conjecture_R1.H1 := by
  intro h1 h2 δ hδ
  by_cases hlarge : 1 ≤ δ
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
    have hkreal : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkreal
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (div_nonneg (sq_nonneg _) (by positivity))) (Nat.cast_nonneg _)
  · have hη : (0 : ℝ) < δ / 2 := by positivity
    obtain ⟨ε, hε, hwindow⟩ := h2 (δ / 2) hη (by linarith)
    obtain ⟨n0, hn0⟩ := h1 ε hε
    obtain ⟨k0, hk0⟩ := hwindow n0
    apply Filter.eventually_atTop.mpr
    refine ⟨k0, ?_⟩
    intro k hk
    obtain ⟨N, hNlarge, hscale, hthreshold⟩ := hk0 k hk
    obtain ⟨G, htriangle, hindependent⟩ := hn0 N hNlarge
    have hindep : G.IndepSetFree k := by
      intro I hI
      have hlt := hindependent I hI.1
      rw [hI.2] at hlt
      exact (lt_irrefl (k : ℝ)) (hlt.trans hthreshold)
    have hRamsey : (N : ℝ) ≤ (SimpleGraph.classicalRamsey 3 k : ℝ) := by
      exact_mod_cast (witness_lt_classicalRamsey G htriangle hindep).le
    calc
      (1 - δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) =
          ((1 : ℝ) / 2 - δ / 2) * ((k : ℝ) ^ 2 / Real.log k) := by ring
      _ ≤ (N : ℝ) := hscale
      _ ≤ (SimpleGraph.classicalRamsey 3 k : ℝ) := hRamsey

end OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1
