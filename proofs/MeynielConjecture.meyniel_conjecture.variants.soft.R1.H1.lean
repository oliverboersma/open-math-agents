import OMAReductions.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1

-- Step MeynielConjecture.meyniel_conjecture.variants.soft.R1.H1: hypothesis H1 of reduction MeynielConjecture.meyniel_conjecture.variants.soft.R1
-- Credit: @tatashbar
-- H1 := ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ), G.Connected →     (∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →       CopsWin (G.induce s) k) →     CopsWin G (k + 1)  /-- **Soft Meyniel for graphs of small maximum degree (open).** There are `δ, ε, C > 0` such that every connected graph on at most `N` vertices with maximum degree at most `N ^ δ` has cop number at most `C N ^ (1 - ε)`. -/

/-!
One cop guards a closed neighbourhood. The cops start on `v`. A robber who starts in `N[v]` is
caught at once. Otherwise one cop stays on `v` for the rest of the game, and the other `k` cops
walk along shortest paths to the starting squares of a winning strategy on the component `s`
of the robber inside `G - N[v]`. Then they play that strategy. The robber can leave `s` only by
stepping into `N[v]`, where the cop on `v` catches him in the next round.
-/

namespace OMA

open SimpleGraph MeynielConjecture

variable {V : Type} {G : SimpleGraph V}

/-- One more round never hurts the cops. -/
theorem catch_succ {k : ℕ} : ∀ (m : ℕ) (c : Fin k → V) (r : V),
    CopsCatchWithin G k m c r → CopsCatchWithin G k (m + 1) c r := by
  intro m
  induction m with
  | zero => intro c r h; exact Or.inl h
  | succ m ih =>
    rintro c r (h | ⟨c', hs, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c', hs, Or.inl h⟩
    · exact Or.inr ⟨c', hs, Or.inr fun r' hr' => ih c' r' (h r' hr')⟩

theorem catch_mono {k m m' : ℕ} (hm : m ≤ m') {c : Fin k → V} {r : V}
    (h : CopsCatchWithin G k m c r) : CopsCatchWithin G k m' c r := by
  induction hm with
  | refl => exact h
  | step _ ih => exact catch_succ _ _ _ ih

/-- A cop on `v` catches a robber in the closed neighbourhood of `v` in one round. -/
theorem guard {k : ℕ} (v : V) (d : Fin k → V) (r : V) (hr : r = v ∨ G.Adj v r) :
    CopsCatchWithin G (k + 1) 1 (Fin.cons v d) r := by
  rcases hr with rfl | hr
  · exact Or.inl ⟨0, by simp⟩
  · refine Or.inr ⟨Fin.cons r d, fun i => ?_, Or.inl ⟨0, by simp⟩⟩
    cases i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; exact Or.inr hr
    | succ j => simp only [Fin.cons_succ]; exact Or.inl rfl

/-- A strategy on the induced subgraph on `s` lifts to `G`, with one extra cop guarding `v`. -/
theorem transfer {k : ℕ} (v : V) (s : Set V)
    (hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y = v ∨ G.Adj v y) :
    ∀ (m : ℕ) (c : Fin k → s) (r : s), CopsCatchWithin (G.induce s) k m c r →
      CopsCatchWithin G (k + 1) (m + 1) (Fin.cons v (fun i => (c i : V))) r := by
  intro m
  induction m with
  | zero =>
    rintro c r ⟨i, hi⟩
    exact Or.inl ⟨i.succ, by simp [hi]⟩
  | succ m ih =>
    rintro c r (⟨i, hi⟩ | ⟨c', hs, h⟩)
    · exact Or.inl ⟨i.succ, by simp [hi]⟩
    · refine Or.inr ⟨Fin.cons v (fun i => (c' i : V)), fun i => ?_, ?_⟩
      · cases i using Fin.cases with
        | zero => simp only [Fin.cons_zero]; exact Or.inl rfl
        | succ j =>
          simp only [Fin.cons_succ]
          rcases hs j with h1 | h1
          · exact Or.inl (congrArg Subtype.val h1)
          · exact Or.inr h1
      · rcases h with ⟨i, hi⟩ | h
        · exact Or.inl ⟨i.succ, by simp [hi]⟩
        · right
          intro r' hr'
          by_cases hrs : r' ∈ s
          · refine ih c' ⟨r', hrs⟩ (h ⟨r', hrs⟩ ?_)
            rcases hr' with h2 | h2
            · exact Or.inl (Subtype.ext h2)
            · exact Or.inr h2
          · have hv : r' = v ∨ G.Adj v r' := by
              rcases hr' with h2 | h2
              · exact absurd (by rw [← h2]; exact r.2) hrs
              · exact (hcl r r.2 r' h2).resolve_left hrs
            exact catch_mono (by omega) (guard v _ r' hv)

/-- From `c ≠ r` one can step to a neighbour of `c` that is closer to `r`. -/
theorem step_toward (hc : G.Connected) {c r : V} (hne : c ≠ r) :
    ∃ c', G.Adj c c' ∧ G.dist c' r + 1 = G.dist c r := by
  obtain ⟨p, hpl⟩ := hc.exists_walk_length_eq_dist c r
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ c' _ h q =>
    refine ⟨c', h, ?_⟩
    rw [Walk.length_cons] at hpl
    have h1 := dist_le q
    have h2 := hc.dist_triangle (u := c) (v := c') (w := r)
    have h3 : G.dist c c' = 1 := dist_eq_one_iff_adj.mpr h
    omega

/-- The cops off `v` walk to their starting squares in `s` while the robber is trapped there. -/
theorem walk_in (hG : G.Connected) {k : ℕ} (v : V) (s : Set V)
    (hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y = v ∨ G.Adj v y)
    (t : Fin k → s) (M : ℕ) (hM : ∀ r : s, CopsCatchWithin (G.induce s) k M t r) :
    ∀ (D : ℕ) (d : Fin k → V), (∀ i, G.dist (d i) (t i) ≤ D) →
      ∀ r ∈ s, CopsCatchWithin G (k + 1) (D + M + 1) (Fin.cons v d) r := by
  intro D
  induction D with
  | zero =>
    intro d hd r hr
    have hdt : d = fun i => (t i : V) :=
      funext fun i => hG.dist_eq_zero_iff.mp (by have := hd i; omega)
    subst hdt
    rw [Nat.zero_add]
    exact transfer v s hcl M t ⟨r, hr⟩ (hM ⟨r, hr⟩)
  | succ D ih =>
    intro d hd r hr
    have hstep : ∀ i, ∃ e, Step G (d i) e ∧ G.dist e (t i) ≤ D := by
      intro i
      by_cases hi : d i = t i
      · exact ⟨d i, Or.inl rfl, by rw [hi, dist_self]; omega⟩
      · obtain ⟨e, he, hde⟩ := step_toward hG hi
        exact ⟨e, Or.inr he, by have := hd i; omega⟩
    choose e he hed using hstep
    refine Or.inr ⟨Fin.cons v e, fun i => ?_, Or.inr fun r' hr' => ?_⟩
    · cases i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact Or.inl rfl
      | succ j => simp only [Fin.cons_succ]; exact he j
    · have hlev : D + 1 + M = D + M + 1 := by omega
      rw [hlev]
      by_cases hrs : r' ∈ s
      · exact ih e hed r' hrs
      · have hv : r' = v ∨ G.Adj v r' := by
          rcases hr' with h2 | h2
          · exact absurd (by rw [← h2]; exact hr) hrs
          · exact (hcl r hr r' h2).resolve_left hrs
        exact catch_mono (by omega) (guard v e r' hv)

end OMA

open SimpleGraph MeynielConjecture OMA

/-- Step `H1` of the reduction: one cop guards a closed neighbourhood. -/
theorem OMA.solution : OMA.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1.H1 := by
  intro V _ G v k hG hyp
  classical
  refine ⟨Fin.cons v (fun _ => v), fun r => ?_⟩
  by_cases hrv : r = v ∨ G.Adj v r
  · exact ⟨1, guard v _ r hrv⟩
  · have hrR : r ∈ {u | u ≠ v ∧ ¬ G.Adj v u} := by
      simp only [not_or] at hrv
      exact hrv
    let R : Set V := {u | u ≠ v ∧ ¬ G.Adj v u}
    let s : Set V := {u | ∃ hu : u ∈ R, (G.induce R).Reachable ⟨r, hrR⟩ ⟨u, hu⟩}
    have hsR : s ⊆ R := fun u hu => hu.1
    have hrs : r ∈ s := ⟨hrR, Reachable.refl _⟩
    have hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y = v ∨ G.Adj v y := by
      rintro x ⟨hxR, hx⟩ y hxy
      by_cases hyR : y ∈ R
      · exact Or.inl ⟨hyR, hx.trans
          (Adj.reachable (show (G.induce R).Adj ⟨x, hxR⟩ ⟨y, hyR⟩ from hxy))⟩
      · right
        by_cases hyv : y = v
        · exact Or.inl hyv
        · right
          by_contra hny
          exact hyR ⟨hyv, hny⟩
    have key : ∀ b : R, Relation.ReflTransGen (G.induce R).Adj ⟨r, hrR⟩ b →
        ∀ hb : (b : V) ∈ s, (G.induce s).Reachable ⟨r, hrs⟩ ⟨b, hb⟩ := by
      intro b hb
      induction hb with
      | refl => intro _; exact Reachable.refl _
      | @tail b' c' hab hbc ih =>
        intro hc
        have hb's : (b' : V) ∈ s := ⟨b'.2, (reachable_iff_reflTransGen _ _).mpr hab⟩
        exact (ih hb's).trans
          (Adj.reachable (show (G.induce s).Adj ⟨b', hb's⟩ ⟨c', hc⟩ from hbc))
    have hbase : ∀ a : s, (G.induce s).Reachable ⟨r, hrs⟩ a := fun a =>
      key ⟨a.1, a.2.1⟩ ((reachable_iff_reflTransGen _ _).mp a.2.2) a.2
    have hconn : (G.induce s).Connected := by
      rw [connected_iff]
      exact ⟨fun a b => (hbase a).symm.trans (hbase b), ⟨⟨r, hrs⟩⟩⟩
    obtain ⟨t, ht⟩ := hyp s hsR hconn
    choose f hf using ht
    have hM : ∀ r : s, CopsCatchWithin (G.induce s) k (Finset.univ.sup f) t r :=
      fun r => catch_mono (Finset.le_sup (Finset.mem_univ r)) (hf r)
    exact ⟨_, walk_in hG v s hcl t _ hM (Finset.univ.sup fun i => G.dist v (t i)) _
      (fun i => Finset.le_sup (f := fun i => G.dist v (t i)) (Finset.mem_univ i)) r hrs⟩

