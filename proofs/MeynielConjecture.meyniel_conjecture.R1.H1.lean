import OMAReductions.R_MeynielConjecture_meyniel_conjecture_R1
import Mathlib

-- Step MeynielConjecture.meyniel_conjecture.R1.H1: hypothesis H1 of reduction MeynielConjecture.meyniel_conjecture.R1
-- Credit: @ivillar
-- Proof: the classical guarding argument. One cop stays on v and catches any robber that steps into
-- N[v]. The robber starts in some component s of G - N[v] (G.induce s is connected), on which k cops
-- win by hypothesis. The other k cops walk to that strategy's starting positions along shortest paths,
-- then copy the strategy move for move; a robber leaving s can only step into N[v], where it is caught.


namespace OMA.MeynielGuard

open MeynielConjecture

variable {V : Type} (G : SimpleGraph V)

theorem catch_succ {k : ℕ} : ∀ (m : ℕ) (c : Fin k → V) (r : V),
    CopsCatchWithin G k m c r → CopsCatchWithin G k (m + 1) c r
  | 0, c, r, h => Or.inl h
  | m + 1, c, r, h => by
    rcases h with h | ⟨c', hc', h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨c', hc', Or.inl h⟩
    · exact Or.inr ⟨c', hc', Or.inr fun r' hr' => catch_succ m c' r' (h r' hr')⟩

theorem catch_mono {k : ℕ} (c : Fin k → V) (r : V) {m m' : ℕ} (hmm : m ≤ m')
    (h : CopsCatchWithin G k m c r) : CopsCatchWithin G k m' c r := by
  induction m', hmm using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact catch_succ G n c r ih

/-- A cop at `v` catches a robber standing on `v` at any level. -/
theorem catch_at_v {k : ℕ} (m : ℕ) (v : V) (p : Fin k → V) :
    CopsCatchWithin G (k + 1) m (Fin.cons v p) v := by
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ m => exact Or.inl ⟨0, rfl⟩

/-- A cop at `v` catches a robber next to `v` within one round. -/
theorem catch_adj_v {k : ℕ} (m : ℕ) (v r : V) (p : Fin k → V) (h : G.Adj v r) :
    CopsCatchWithin G (k + 1) (m + 1) (Fin.cons v p) r := by
  refine Or.inr ⟨Fin.cons r p, ?_, Or.inl ⟨0, rfl⟩⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact Or.inr h
  · simp only [Fin.cons_succ]
    exact Or.inl rfl

/-- Simulating a strategy on an induced subgraph, with one extra cop parked at `v`. -/
theorem simulate {k : ℕ} (s : Set V) (v : V)
    (hs : ∀ u ∈ s, ∀ w, Step G u w → w ∈ s ∨ w = v ∨ G.Adj v w) :
    ∀ (m : ℕ) (c : Fin k → s) (r : s), CopsCatchWithin (G.induce s) k m c r →
      CopsCatchWithin G (k + 1) (m + 1) (Fin.cons v (fun i => (c i : V))) r := by
  intro m
  induction m with
  | zero =>
    intro c r h
    obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i.succ, by simp [hi]⟩
  | succ m ih =>
    intro c r h
    rcases h with ⟨i, hi⟩ | ⟨c₁, hc₁, h | h⟩
    · exact Or.inl ⟨i.succ, by simp [hi]⟩
    · refine Or.inr ⟨Fin.cons v (fun i => (c₁ i : V)), ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact Or.inl rfl
        · simp only [Fin.cons_succ]
          rcases hc₁ j with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr h
      · obtain ⟨i, hi⟩ := h
        exact Or.inl ⟨i.succ, by simp [hi]⟩
    · refine Or.inr ⟨Fin.cons v (fun i => (c₁ i : V)), ?_, Or.inr ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact Or.inl rfl
        · simp only [Fin.cons_succ]
          rcases hc₁ j with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr h
      · intro r' hr'
        rcases hs r r.2 r' hr' with hrs | hrv | hra
        · have hstep : Step (G.induce s) r ⟨r', hrs⟩ := by
            rcases hr' with h' | h'
            · exact Or.inl (Subtype.ext h')
            · exact Or.inr h'
          exact ih c₁ ⟨r', hrs⟩ (h _ hstep)
        · subst hrv
          exact catch_at_v G _ _ _
        · exact catch_adj_v G _ _ _ _ hra

theorem step_toward (hG : G.Connected) (u t : V) :
    ∃ w, Step G u w ∧ G.dist w t ≤ G.dist u t - 1 := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u t
  cases p with
  | nil => exact ⟨_, Or.inl rfl, by simp⟩
  | cons h q =>
    refine ⟨_, Or.inr h, ?_⟩
    have := SimpleGraph.dist_le q
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Walking the `k` free cops to their targets, while the cop at `v` guards `N[v]`. -/
theorem travel {k : ℕ} (hG : G.Connected) (s : Set V) (v : V)
    (hs : ∀ u ∈ s, ∀ w, Step G u w → w ∈ s ∨ w = v ∨ G.Adj v w) (t : Fin k → V) (M : ℕ)
    (hM : ∀ r ∈ s, CopsCatchWithin G (k + 1) M (Fin.cons v t) r) :
    ∀ (D : ℕ) (p : Fin k → V), (∀ i, G.dist (p i) (t i) ≤ D) →
      ∀ r, (r ∈ s ∨ r = v ∨ G.Adj v r) → CopsCatchWithin G (k + 1) (D + M + 1) (Fin.cons v p) r := by
  intro D
  induction D with
  | zero =>
    intro p hp r hr
    have hpt : p = t := by
      funext i
      exact ((hG.preconnected (p i) (t i)).dist_eq_zero_iff).mp (by have := hp i; omega)
    subst hpt
    rcases hr with hr | hr | hr
    · exact catch_mono G _ _ (by omega) (hM r hr)
    · subst hr
      exact catch_at_v G _ _ _
    · exact catch_adj_v G _ _ _ _ hr
  | succ D ih =>
    intro p hp r hr
    rcases hr with hr | hr | hr
    · have hex : ∀ i, ∃ w, Step G (p i) w ∧ G.dist w (t i) ≤ G.dist (p i) (t i) - 1 :=
        fun i => step_toward G hG (p i) (t i)
      choose p' hp'1 hp'2 using hex
      have hrw : D + 1 + M + 1 = (D + M + 1) + 1 := by omega
      rw [hrw]
      refine Or.inr ⟨Fin.cons v p', ?_, Or.inr ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact Or.inl rfl
        · simp only [Fin.cons_succ]
          exact hp'1 j
      · intro r' hr'
        exact ih p' (fun i => by have := hp'2 i; have := hp i; omega) r' (hs r hr r' hr')
    · subst hr
      exact catch_at_v G _ _ _
    · have hrw : D + 1 + M + 1 = (D + 1 + M) + 1 := by omega
      rw [hrw]
      exact catch_adj_v G _ _ _ _ hr

/-- The vertices reachable from `a0` inside `A`, lifted to `V`. -/
def comp (A : Set V) (a0 : A) : Set V :=
  {u | ∃ hu : u ∈ A, (G.induce A).Reachable a0 ⟨u, hu⟩}

theorem lift_walk (A : Set V) (a0 : A) {a b : A} (w : (G.induce A).Walk a b) :
    ∀ ha : (G.induce A).Reachable a0 a,
      (G.induce (comp G A a0)).Reachable ⟨a.1, a.2, ha⟩ ⟨b.1, b.2, ha.trans ⟨w⟩⟩ := by
  induction w with
  | nil => intro ha; exact SimpleGraph.Reachable.refl _
  | @cons a c b h w' ih =>
    intro ha
    have hc : (G.induce A).Reachable a0 c := ha.trans h.reachable
    have hadj : (G.induce (comp G A a0)).Adj ⟨a.1, a.2, ha⟩ ⟨c.1, c.2, hc⟩ := h
    exact hadj.reachable.trans (ih hc)

theorem guard : OMA.R_MeynielConjecture_meyniel_conjecture_R1.H1 := by
  intro V _ G v k hG hyp
  classical
  refine ⟨fun _ => v, fun r0 => ?_⟩
  by_cases hA : r0 ≠ v ∧ ¬ G.Adj v r0
  · set A : Set V := {u | u ≠ v ∧ ¬ G.Adj v u} with hAdef
    set a0 : A := ⟨r0, hA⟩
    set s := comp G A a0 with hsdef
    have hsA : s ⊆ A := fun u hu => hu.1
    have hr0s : r0 ∈ s := ⟨hA, SimpleGraph.Reachable.refl _⟩
    have hclos : ∀ u ∈ s, ∀ w, Step G u w → w ∈ s ∨ w = v ∨ G.Adj v w := by
      intro u hu w hw
      by_cases hwA : w ∈ A
      · left
        obtain ⟨huA, hreach⟩ := hu
        rcases hw with h | h
        · subst h
          exact ⟨huA, hreach⟩
        · exact ⟨hwA, hreach.trans (SimpleGraph.Adj.reachable (G := G.induce A)
            (u := ⟨u, huA⟩) (v := ⟨w, hwA⟩) h)⟩
      · right
        simp only [hAdef, Set.mem_ofPred_eq, not_and, not_not] at hwA
        by_cases hwv : w = v
        · exact Or.inl hwv
        · exact Or.inr (hwA hwv)
    have hconn : (G.induce s).Connected := by
      have hne : Nonempty s := ⟨⟨r0, hr0s⟩⟩
      rw [SimpleGraph.connected_iff]
      refine ⟨?_, hne⟩
      suffices hr : ∀ x : s, (G.induce s).Reachable ⟨r0, hr0s⟩ x by
        intro x y
        exact (hr x).symm.trans (hr y)
      rintro ⟨x, hxA, hreach⟩
      obtain ⟨w⟩ := hreach
      exact lift_walk G A a0 w (SimpleGraph.Reachable.refl _)
    obtain ⟨cs, hcs⟩ := hyp s hsA hconn
    choose f hf using hcs
    set M := Finset.univ.sup f with hMdef
    have hM : ∀ r ∈ s, CopsCatchWithin G (k + 1) (M + 1) (Fin.cons v (fun i => (cs i : V))) r := by
      intro r hr
      apply simulate G s v hclos M cs ⟨r, hr⟩
      exact catch_mono (G.induce s) _ _ (Finset.le_sup (Finset.mem_univ _)) (hf ⟨r, hr⟩)
    set D := Finset.univ.sup (fun i => G.dist v (cs i : V)) with hDdef
    have hinit : (fun _ : Fin (k + 1) => v) = Fin.cons v (fun _ : Fin k => v) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    refine ⟨D + (M + 1) + 1, ?_⟩
    rw [hinit]
    exact travel G hG s v hclos _ (M + 1) hM D (fun _ => v)
      (fun i => Finset.le_sup (f := fun i => G.dist v (cs i : V)) (Finset.mem_univ i)) r0 (Or.inl hr0s)
  · by_cases h : r0 = v
    · exact ⟨0, ⟨0, h.symm⟩⟩
    · have hadj : G.Adj v r0 := by
        by_contra hna
        exact hA ⟨h, hna⟩
      exact ⟨1, Or.inr ⟨fun _ => r0, fun _ => Or.inr hadj, Or.inl ⟨0, rfl⟩⟩⟩

end OMA.MeynielGuard

theorem OMA.solution : OMA.R_MeynielConjecture_meyniel_conjecture_R1.H1 := OMA.MeynielGuard.guard
