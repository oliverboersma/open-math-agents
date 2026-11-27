import FormalConjectures.ErdosProblems.«61»

/-!
The Erdős–Hajnal bound for the five-vertex path.

The two sparsification stages and the induced-path obstructions follow Nguyen,
Scott, and Seymour, [Induced subgraph density. VII](https://arxiv.org/abs/2312.15333),
Sections 4–7. The covering and equalization steps use deterministic pruning.
The initial sparse-side conclusion follows Fox and Sudakov,
[Induced Ramsey-type theorems](https://arxiv.org/abs/0706.4112), Section 2.
The bipartite comb estimate follows Chudnovsky, Scott, Seymour, and Spirkl,
[Erdős–Hajnal for graphs with no 5-hole](https://arxiv.org/abs/2102.04994), Section 2.
-/

open SimpleGraph
open scoped BigOperators

namespace FivePath

def Free {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (H ↪g G)

abbrev PathFree {V : Type*} (G : SimpleGraph V) := Free (pathGraph 5) G
abbrev HouseFree {V : Type*} (G : SimpleGraph V) := Free (pathGraph 5)ᶜ G

theorem free_of_embedding {V W T : Type*} {G : SimpleGraph V}
    {G' : SimpleGraph W} {H : SimpleGraph T} (h : Free H G) (e : G' ↪g G) : Free H G' :=
  fun ⟨f⟩ => h ⟨e.comp f⟩

theorem free_compl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} :
    Free Hᶜ Gᶜ ↔ Free H G :=
  not_congr Embedding.complEquiv.symm.nonempty_congr

private theorem reverse_not_adj {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : ¬ G.Adj x y) : ¬ G.Adj y x :=
  fun he => h he.symm

theorem induced_path {V : Type*} {G : SimpleGraph V} {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hce : ¬ G.Adj c e) :
    Nonempty (pathGraph 5 ↪g G) := by
  let f : Fin 5 → V := ![a, b, c, d, e]
  have hf : ∀ i j, G.Adj (f i) (f j) ↔ (pathGraph 5).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [f] <;>
      first
      | exact iff_of_true (by solve_by_elim [SimpleGraph.Adj.symm]) (by simp only [pathGraph_adj]; decide)
      | exact iff_of_false (by solve_by_elim [reverse_not_adj, SimpleGraph.irrefl]) (by simp only [pathGraph_adj]; decide)
  have hdist : ∀ i j : Fin 5, i ≠ j → ∃ k : Fin 5,
      ((pathGraph 5).Adj i k ∧ ¬ (pathGraph 5).Adj j k) ∨
        ((pathGraph 5).Adj j k ∧ ¬ (pathGraph 5).Adj i k) := by
    simp only [pathGraph_adj]
    decide
  refine ⟨⟨⟨f, ?_⟩, fun {i j} => hf i j⟩⟩
  intro i j h
  by_contra! hij
  obtain ⟨k, h₁ | h₁⟩ := hdist i j hij
  · exact h₁.2 ((hf j k).mp (h ▸ (hf i k).mpr h₁.1))
  · exact h₁.2 ((hf i k).mp (h.symm ▸ (hf j k).mpr h₁.1))

def Uniform {V : Type*} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ x ∈ A, ∀ y ∈ B, G.Adj x y) ∨ (∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)

def Mixed {V : Type*} (G : SimpleGraph V) (x : V) (A : Finset V) : Prop :=
  (∃ a ∈ A, G.Adj x a) ∧ (∃ a ∈ A, ¬ G.Adj x a)

def internallyConnected {V : Type*} (G : SimpleGraph V) (A : Finset V) : Prop :=
  (G.induce (A : Set V)).Connected

theorem not_mixed {V : Type*} {G : SimpleGraph V} {x : V} {A : Finset V} :
    ¬ Mixed G x A ↔ (∀ a ∈ A, G.Adj x a) ∨ (∀ a ∈ A, ¬ G.Adj x a) := by
  classical
  simp only [Mixed, not_and_or, not_exists, not_not, ← imp_iff_not_or, or_comm]

theorem edge_crossing {V : Type*} {G : SimpleGraph V} {A : Finset V}
    (hconn : internallyConnected G A) (P : V → Prop)
    {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hpa : P a) (hpb : ¬ P b) :
    ∃ x ∈ A, ∃ y ∈ A, G.Adj x y ∧ P x ∧ ¬ P y := by
  classical
  obtain ⟨w⟩ := hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have hc {u v : (A : Set V)} (w : (G.induce (A : Set V)).Walk u v)
      (hu : P u) (hv : ¬ P v) :
      ∃ x ∈ A, ∃ y ∈ A, G.Adj x y ∧ P x ∧ ¬ P y := by
    induction w with
    | nil => exact (hv hu).elim
    | @cons u w v huw rest ih =>
      by_cases h : P w
      · exact ih h hv
      · exact ⟨u, u.property, w, w.property, huw, hu, h⟩
  exact hc w hpa hpb

theorem mixed_edge_compl {V : Type*} {G : SimpleGraph V} {A : Finset V}
    (hconn : internallyConnected Gᶜ A) {v : V} (hv : Mixed G v A) :
    ∃ a ∈ A, ∃ b ∈ A, Gᶜ.Adj a b ∧ G.Adj v a ∧ ¬ G.Adj v b := by
  obtain ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩ := hv
  exact edge_crossing hconn (G.Adj v) ha hb hva hvb

/-- The comb used on the sparse side when the excluded induced graph is the house. -/
structure NeighborhoodComb {V : Type*} (G : SimpleGraph V) (n : ℕ) where
  root : V
  tooth : Fin n → V
  block : Fin n → Finset V
  disjoint : Pairwise (Function.onFun Disjoint block)
  tooth_outside : ∀ i j, tooth i ∉ block j
  root_ne_tooth : ∀ i, root ≠ tooth i
  root_miss : ∀ i, ¬ G.Adj root (tooth i)
  root_sees : ∀ i x, x ∈ block i → G.Adj root x
  cross : ∀ i j x, x ∈ block j → (G.Adj (tooth i) x ↔ i = j)

theorem NeighborhoodComb.no_mixed {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (C : NeighborhoodComb G n) (hfree : HouseFree G) {i j : Fin n} (hij : i ≠ j)
    (hconn : internallyConnected Gᶜ (C.block i)) {u : V} (hu : u ∈ C.block j) :
    ¬ Mixed G u (C.block i) := by
  intro huMix
  obtain ⟨w, hw, z, hz, hwz, huw, huz⟩ := mixed_edge_compl hconn huMix
  have hfree' : PathFree Gᶜ := by
    simpa using (free_compl (G := G) (H := (pathGraph 5)ᶜ)).mpr hfree
  apply hfree'
  have htu : ¬ G.Adj (C.tooth i) u := fun h => hij ((C.cross i j u hu).mp h)
  have htz := (C.cross i i z hz).mpr rfl
  have htw := (C.cross i i w hw).mpr rfl
  have huz' : u ≠ z := by
    intro eq
    exact Finset.disjoint_left.mp (C.disjoint hij) hz (eq ▸ hu)
  exact induced_path ((G.compl_adj _ _).mpr ⟨C.root_ne_tooth i, C.root_miss i⟩)
    ((G.compl_adj _ _).mpr ⟨fun he => C.tooth_outside i j (he ▸ hu), htu⟩)
    ((G.compl_adj _ _).mpr ⟨huz', huz⟩) hwz.symm
    (fun h => ((G.compl_adj _ _).mp h).2 (C.root_sees j u hu))
    (fun h => ((G.compl_adj _ _).mp h).2 (C.root_sees i z hz))
    (fun h => ((G.compl_adj _ _).mp h).2 (C.root_sees i w hw))
    (fun h => ((G.compl_adj _ _).mp h).2 htz)
    (fun h => ((G.compl_adj _ _).mp h).2 htw)
    (fun h => ((G.compl_adj _ _).mp h).2 huw)

theorem NeighborhoodComb.pure {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (C : NeighborhoodComb G n) (hfree : HouseFree G)
    (hc : ∀ i, internallyConnected Gᶜ (C.block i)) {i j : Fin n} (hij : i ≠ j) :
    Uniform G (C.block i) (C.block j) := by
  classical
  by_cases he : ∃ u ∈ C.block i, ∃ v ∈ C.block j, G.Adj u v
  · obtain ⟨u, hu, v, hv, huv⟩ := he
    have h₁ : ∀ w ∈ C.block j, G.Adj u w := by
      rcases not_mixed.mp (C.no_mixed hfree hij.symm (hc j) hu) with h | h
      · exact h
      · exact (h v hv huv).elim
    refine Or.inl fun w hw z hz => ?_
    rcases not_mixed.mp (C.no_mixed hfree hij (hc i) hz) with h | h
    · exact (h w hw).symm
    · exact (h u hu (h₁ z hz).symm).elim
  · exact Or.inr fun u hu v hv huv => he ⟨u, hu, v, hv, huv⟩

theorem double_mixed_induces_p5 {V : Type*} {G : SimpleGraph V} {A B : Finset V} {v : V}
    (hcA : internallyConnected Gᶜ A) (hcB : internallyConnected Gᶜ B)
    (hmA : Mixed G v A) (hmB : Mixed G v B)
    (hvoA : v ∉ A) (hvoB : v ∉ B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    Nonempty (pathGraph 5 ↪g Gᶜ) := by
  obtain ⟨a, ha, a', ha', haadj, hva, hva'⟩ := mixed_edge_compl hcA hmA
  obtain ⟨b, hb, b', hb', hbadj, hvb, hvb'⟩ := mixed_edge_compl hcB hmB
  have hav : Gᶜ.Adj v a' := (G.compl_adj _ _).mpr ⟨fun he => hvoA (he ▸ ha'), hva'⟩
  have hbv : Gᶜ.Adj v b' := (G.compl_adj _ _).mpr ⟨fun he => hvoB (he ▸ hb'), hvb'⟩
  exact induced_path haadj hav.symm hbv hbadj.symm
    (fun h => ((G.compl_adj _ _).mp h).2 hva.symm)
    (fun h => ((G.compl_adj _ _).mp h).2 (hc a ha b' hb'))
    (fun h => ((G.compl_adj _ _).mp h).2 (hc a ha b hb))
    (fun h => ((G.compl_adj _ _).mp h).2 (hc a' ha' b' hb'))
    (fun h => ((G.compl_adj _ _).mp h).2 (hc a' ha' b hb))
    (fun h => ((G.compl_adj _ _).mp h).2 hvb)

end FivePath

/- The constant-density Rödl conclusion for a forbidden induced graph on five vertices.
The proof uses the recursion of Fox and Sudakov, [Induced Ramsey-type theorems](https://arxiv.org/abs/0706.4112), Section 2. -/

namespace FivePath

noncomputable def neighborsIn {V : Type*} (G : SimpleGraph V) (x : V) (U : Finset V) :
    Finset V := by
  classical
  exact U.filter (G.Adj x)

@[simp] theorem mem_neighborsIn {V : Type*} {G : SimpleGraph V} {x y : V} {U : Finset V} :
    y ∈ neighborsIn G x U ↔ y ∈ U ∧ G.Adj x y := by
  classical
  simp [neighborsIn]

theorem neighborsIn_mono {V : Type*} {G : SimpleGraph V} {x : V} {U W : Finset V}
    (h : U ⊆ W) : neighborsIn G x U ⊆ neighborsIn G x W := by
  intro y hy
  exact mem_neighborsIn.mpr ⟨h (mem_neighborsIn.mp hy).1, (mem_neighborsIn.mp hy).2⟩

def SparseSide (F : SimpleGraph (Fin 5)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ > (0 : ℝ), ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    Free F G → ∃ X : Finset V, δ * (Fintype.card V : ℝ) ≤ X.card ∧
      ((∀ x ∈ X, (neighborsIn G x X).card ≤ ε * (X.card : ℝ)) ∨
       (∀ x ∈ X, (neighborsIn Gᶜ x X).card ≤ ε * (X.card : ℝ)))

end FivePath

namespace FivePath

private noncomputable def edgeCountBetween {V : Type*}
    (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ((neighborsIn G x B).card : ℝ)

private def Sparse {V : Type*} (G : SimpleGraph V) (A : Finset V) (c : ℝ) : Prop :=
  edgeCountBetween G A A ≤ c * (A.card : ℝ)^2

private theorem edgeCount_comm {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    edgeCountBetween G A B = edgeCountBetween G B A := by
  classical
  unfold edgeCountBetween
  simp only [neighborsIn, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [Finset.sum_comm]
  simp only [SimpleGraph.adj_comm]

private theorem edgeCount_le_mul {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    (c : ℝ) (h : ∀ x ∈ A, ((neighborsIn G x B).card : ℝ) ≤ c * B.card) :
    edgeCountBetween G A B ≤ c * A.card * B.card := by
  unfold edgeCountBetween
  calc
    _ ≤ ∑ _ ∈ A, c * (B.card : ℝ) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem edgeCount_union_left {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} (C : Finset V) (h : Disjoint A B) :
    edgeCountBetween G (A ∪ B) C = edgeCountBetween G A C + edgeCountBetween G B C := by
  unfold edgeCountBetween
  exact Finset.sum_union h

private theorem edgeCount_union {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} (h : Disjoint A B) :
    edgeCountBetween G (A ∪ B) (A ∪ B) =
      edgeCountBetween G A A + edgeCountBetween G B B + 2 * edgeCountBetween G B A := by
  rw [edgeCount_union_left G _ h, edgeCount_comm G A (A ∪ B), edgeCount_comm G B (A ∪ B),
    edgeCount_union_left G A h, edgeCount_union_left G B h, edgeCount_comm G A B]
  ring

private theorem edgeCount_compl_le {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    edgeCountBetween G A A + edgeCountBetween Gᶜ A A ≤ (A.card : ℝ)^2 := by
  classical
  have hrow (x : V) : ((neighborsIn G x A).card : ℝ) + (neighborsIn Gᶜ x A).card ≤ A.card := by
    have hd : Disjoint (neighborsIn G x A) (neighborsIn Gᶜ x A) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact ((G.compl_adj _ _).mp (mem_neighborsIn.mp hz).2).2 (mem_neighborsIn.mp hy).2
    have hs : neighborsIn G x A ∪ neighborsIn Gᶜ x A ⊆ A := by
      apply Finset.union_subset <;> intro _ h <;> exact (mem_neighborsIn.mp h).1
    have h := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd] at h
    exact_mod_cast h
  unfold edgeCountBetween
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _ ∈ A, (A.card : ℝ) := Finset.sum_le_sum fun x _ => hrow x
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, sq]

private theorem sparse_pick_card {V : Type*} (G : SimpleGraph V) (A : Finset V)
    {m : ℕ} (hm : m ≤ A.card) {c : ℝ} (hc : 0 ≤ c) (hA : Sparse G A c) :
    ∃ B : Finset V, B ⊆ A ∧ B.card = m ∧ Sparse G B c := by
  classical
  by_cases hm0 : m = 0
  · subst m
    exact ⟨∅, Finset.empty_subset _, rfl, by simp [Sparse, edgeCountBetween]⟩
  have recPick (n : ℕ) : ∀ A : Finset V, A.card = n → m ≤ n → Sparse G A c →
      ∃ B : Finset V, B ⊆ A ∧ B.card = m ∧ Sparse G B c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hn hm hA
      by_cases he : m = n
      · exact ⟨A, Finset.Subset.refl _, hn.trans he.symm, hA⟩
      have ha : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image A
        (fun v => (neighborsIn G v A).card) ha
      let E := A.erase x
      have hE : E ⊆ A := Finset.erase_subset _ _
      have heq : E ∪ {x} = A := by dsimp [E]; simp [hx]
      have hdis : Disjoint E {x} := by simp [E]
      have hEc : E.card + 1 = A.card := by
        have h := Finset.card_union_of_disjoint hdis
        rw [heq, Finset.card_singleton] at h
        exact h.symm
      have hEcR : (E.card : ℝ) + 1 = A.card := by exact_mod_cast hEc
      have hac : (2 : ℝ) ≤ A.card := by
        have h : 2 ≤ A.card := by omega
        exact_mod_cast h
      let d : ℝ := (neighborsIn G x A).card
      have hdecomp : edgeCountBetween G A A = edgeCountBetween G E E + 2 * d := by
        have hs : neighborsIn G x ({x} : Finset V) = ∅ := by
          ext y
          simp only [mem_neighborsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl, h⟩
          exact G.irrefl h
        have hdeq : neighborsIn G x E = neighborsIn G x A := by
          ext y
          simp only [mem_neighborsIn, E, Finset.mem_erase]
          constructor
          · tauto
          · rintro ⟨hy, hadj⟩
            exact ⟨⟨hadj.ne.symm, hy⟩, hadj⟩
        rw [← heq, edgeCount_union G hdis]
        simp [edgeCountBetween, hs, hdeq, d]
      have hdeg : edgeCountBetween G A A ≤ d * A.card := by
        unfold edgeCountBetween
        calc
          _ ≤ ∑ _ ∈ A, d := Finset.sum_le_sum fun y hy => by
            dsimp [d]
            exact_mod_cast hxmax y hy
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hprior : edgeCountBetween G A A ≤ c * (A.card : ℝ)^2 := hA
      have hpos : (0 : ℝ) < A.card := by linarith
      have hnew : Sparse G E c := by
        change edgeCountBetween G E E ≤ c * (E.card : ℝ)^2
        apply (le_of_mul_le_mul_right ?_ hpos)
        have hmul := mul_le_mul_of_nonneg_right hprior (show 0 ≤ (A.card : ℝ) - 2 by linarith)
        have hsq : ((A.card : ℝ) - 2) * (A.card : ℝ)^2 ≤ (E.card : ℝ)^2 * A.card := by
          rw [← hEcR]
          nlinarith [Nat.cast_nonneg (α := ℝ) E.card]
        have hmul' := mul_le_mul_of_nonneg_left hsq hc
        have hstart : edgeCountBetween G E E * (A.card : ℝ) ≤
            edgeCountBetween G A A * ((A.card : ℝ) - 2) := by
          rw [hdecomp] at hdeg ⊢
          nlinarith
        nlinarith
      obtain ⟨B, hBE, hBc, hB⟩ := ih E.card (by omega) E rfl (by omega) hnew
      exact ⟨B, hBE.trans hE, hBc, hB⟩
  exact recPick A.card A rfl hm hA

private theorem good_row_subset {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    {γ : ℝ} (hγ : 0 < γ) (hA : A.Nonempty)
    (h : edgeCountBetween G A B ≤ γ * A.card * B.card) :
    ∃ B' : Finset V, B' ⊆ B ∧ (B.card : ℝ)/2 ≤ B'.card ∧
      ∀ x ∈ B', (neighborsIn G x A).card ≤ (2*γ) * (A.card : ℝ) := by
  classical
  let c : ℝ := (2*γ) * (A.card : ℝ)
  let D := B.filter fun x => c < ((neighborsIn G x A).card : ℝ)
  let B' := B \ D
  have hd : D ⊆ B := Finset.filter_subset _ _
  have hdc : (B'.card : ℝ) + D.card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hd
  have hcount : (D.card : ℝ) * c ≤ edgeCountBetween G B A := by
    unfold edgeCountBetween
    calc
      _ = ∑ _ ∈ D, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ D, ((neighborsIn G x A).card : ℝ) :=
        Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hd (fun _ _ _ => by positivity)
  have hc : 0 < c := by dsimp [c]; have := Finset.card_pos.mpr hA; positivity
  have hsize : (B.card : ℝ)/2 ≤ B'.card := by
    rw [edgeCount_comm] at hcount
    have he : γ * (A.card : ℝ) * B.card = ((B.card : ℝ)/2) * c := by dsimp [c]; ring
    have hdc' := le_of_mul_le_mul_right (hcount.trans (h.trans_eq he)) hc
    linarith
  refine ⟨B', Finset.sdiff_subset, hsize, fun x hx => ?_⟩
  exact le_of_not_gt fun ht => (Finset.mem_sdiff.mp hx).2
    (Finset.mem_filter.mpr ⟨Finset.sdiff_subset hx, ht⟩)

end FivePath

namespace FivePath

private def correct {V : Type*} (G : SimpleGraph V) (F : SimpleGraph (Fin 5)) (i j : Fin 5) (x y : V) : Prop :=
  G.Adj x y ↔ F.Adj i j

private noncomputable def candidates {V : Type*} (G : SimpleGraph V) (F : SimpleGraph (Fin 5)) (i j : Fin 5) (x : V)
    (S : Finset V) : Finset V := by
  classical
  exact S.filter (correct G F i j x)

private theorem mem_candidates {V : Type*} {G : SimpleGraph V} {F : SimpleGraph (Fin 5)} {i j : Fin 5} {x y : V}
    {S : Finset V} : y ∈ candidates G F i j x S ↔ y ∈ S ∧ correct G F i j x y := by
  classical
  simp [candidates]

private theorem embedding_of_five_parts {V : Type*} {G : SimpleGraph V} {F : SimpleGraph (Fin 5)}
    {S : Fin 5 → Finset V} (hS : ∀ i, (S i).Nonempty)
    (hd : Pairwise (Function.onFun Disjoint S))
    (hc : ∀ i j, i < j → ∀ x ∈ S i, ∀ y ∈ S j, correct G F i j x y) :
    Nonempty (F ↪g G) := by
  classical
  choose f hf using hS
  have hinj : Function.Injective f := by
    intro i j h
    by_contra hne
    exact Finset.disjoint_left.mp (hd hne) (hf i) (h ▸ hf j)
  refine ⟨⟨⟨f, hinj⟩, ?_⟩⟩
  intro i j
  change correct G F i j (f i) (f j)
  rcases lt_trichotomy i j with hij | heq | hji
  · exact hc i j hij _ (hf i) _ (hf j)
  · subst j
    simp [correct]
  · have h := hc j i hji _ (hf j) _ (hf i)
    unfold correct at h ⊢
    exact ⟨fun h' => (h.mp h'.symm).symm, fun h' => (h.mpr h'.symm).symm⟩

private theorem sparse_pair_from_parts {V : Type*} {G : SimpleGraph V}
    {F : SimpleGraph (Fin 5)} (hfree : Free F G)
    {U : Finset V} {P : Fin 5 → Finset V}
    (hPU : ∀ i, P i ⊆ U) (hP : Pairwise (Function.onFun Disjoint P))
    {γ M : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 < M)
    (hPsize : ∀ i, M ≤ (P i).card) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      γ^5 * M / 5 ≤ (A.card : ℝ) ∧ γ^5 * M / 5 ≤ (B.card : ℝ) ∧
      ((∀ x ∈ A, (neighborsIn G x B).card ≤ γ * (B.card : ℝ)) ∨
       (∀ x ∈ A, (neighborsIn Gᶜ x B).card ≤ γ * (B.card : ℝ))) := by
  classical
  by_contra! hnone
  have recParts (k : ℕ) (hk : k ≤ 5) :
      ∃ S : Fin 5 → Finset V, (∀ i, S i ⊆ P i) ∧ (∀ i, (S i).Nonempty) ∧
        (∀ j : Fin 5, k ≤ (j : ℕ) → γ^k * M ≤ ((S j).card : ℝ)) ∧
        (∀ i j : Fin 5, (i : ℕ) < k → i < j → ∀ x ∈ S i, ∀ y ∈ S j, correct G F i j x y) := by
    induction k with
    | zero =>
      refine ⟨P, fun _ => Finset.Subset.refl _, ?_, ?_, by simp⟩
      · intro i
        have hs : (0 : ℝ) < (P i).card := hM.trans_le (hPsize i)
        exact Finset.card_pos.mp (by exact_mod_cast hs)
      · intro j _
        simpa using hPsize j
    | succ k ih =>
      obtain ⟨S, hSP, hS, hsz, hc⟩ := ih (by omega)
      let i : Fin 5 := ⟨k, by omega⟩
      let bad (j : Fin 5) := if i < j then (S i).filter fun x =>
        ((candidates G F i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ) else ∅
      have hbase (j : Fin 5) (hj : k ≤ (j : ℕ)) :
          γ^5 * M ≤ ((S j).card : ℝ) :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hγ.le hγ1 (by omega)) hM.le).trans
          (hsz j hj)
      have hbd : ∀ j, ((bad j).card : ℝ) < ((S i).card : ℝ) / 5 := by
        intro j
        by_cases hij : i < j
        swap
        · simp only [bad, if_neg hij, Finset.card_empty, Nat.cast_zero]
          have hp : (0 : ℝ) < (S i).card := Nat.cast_pos.mpr (Finset.card_pos.mpr (hS i))
          positivity
        by_contra! hbad
        have hbadSub : bad j ⊆ S i := by
          simpa only [bad, if_pos hij] using Finset.filter_subset
            (fun x => ((candidates G F i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ)) (S i)
        have hdis : Disjoint (bad j) (S j) :=
          Disjoint.mono (hbadSub.trans (hSP i)) (hSP j) (hP hij.ne)
        have hbadSize : γ^5 * M / 5 ≤ ((bad j).card : ℝ) := by
          exact (div_le_div_of_nonneg_right (hbase i (by rfl)) (by norm_num)).trans hbad
        have hSsize : γ^5 * M / 5 ≤ ((S j).card : ℝ) := by
          have hh := hbase j (Nat.le_of_lt hij)
          have hp : 0 ≤ γ^5 * M := by positivity
          linarith
        obtain ⟨he, hn⟩ := hnone (bad j) (S j) (hbadSub.trans ((hSP i).trans (hPU i)))
          ((hSP j).trans (hPU j)) hdis hbadSize hSsize
        have hh (x : V) (hx : x ∈ bad j) :
            ((candidates G F i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ) := by
          have hx' : x ∈ (S i).filter (fun x =>
              ((candidates G F i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ)) := by
            simpa only [bad, if_pos hij] using hx
          exact (Finset.mem_filter.mp hx').2
        by_cases hcy : F.Adj i j
        · obtain ⟨x, hx, hxd⟩ := he
          apply hxd.not_gt
          have eq : neighborsIn G x (S j) = candidates G F i j x (S j) := by
            ext y
            simp [mem_candidates, correct, hcy]
          simpa [eq] using hh x hx
        · obtain ⟨x, hx, hxd⟩ := hn
          apply hxd.not_gt
          have eq : neighborsIn Gᶜ x (S j) = candidates G F i j x (S j) := by
            ext y
            rw [mem_neighborsIn, mem_candidates]
            refine and_congr_right fun hy => ?_
            have hxy : x ≠ y := fun heq => Finset.disjoint_left.mp hdis hx (heq ▸ hy)
            simp [compl_adj, hxy, correct, hcy]
          simpa [eq] using hh x hx
      let T := Finset.univ.biUnion bad
      have htlt : (T.card : ℝ) < ((S i).card : ℝ) := by
        have ht : (T.card : ℝ) ≤ ∑ j : Fin 5, ((bad j).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := bad))
        have hs : (∑ j : Fin 5, ((bad j).card : ℝ)) < ∑ _j : Fin 5, ((S i).card : ℝ) / 5 := by
          exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hbd j)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        norm_num at hs
        linarith
      obtain ⟨x, hx, hxT⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (by exact_mod_cast htlt : T.card < (S i).card)
      let S' (j : Fin 5) :=
        if j = i then {x} else if i < j then candidates G F i j x (S j) else S j
      have hf : ∀ j, S' j ⊆ S j := by
        intro j y hy
        by_cases hj : j = i
        · subst j
          have hyx : y = x := by simpa [S'] using hy
          exact hyx.symm ▸ hx
        · by_cases hij : i < j
          · exact (mem_candidates.mp (by simpa [S', hj, hij] using hy)).1
          · simpa [S', hj, hij] using hy
      have hnext (j : Fin 5) (hij : i < j) :
          γ * ((S j).card : ℝ) ≤ ((S' j).card : ℝ) := by
        simp only [S', if_neg hij.ne.symm, if_pos hij]
        apply le_of_not_gt
        intro h
        apply hxT
        apply Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
        simp [bad, hij, hx, h]
      have hFsize (j : Fin 5) (hkj : k + 1 ≤ (j : ℕ)) : γ^(k+1)*M ≤ ((S' j).card : ℝ) := by
        have hij : i < j := hkj
        calc
          _ = γ * (γ ^ k * M) := by rw [pow_succ]; ring
          _ ≤ γ * ((S j).card : ℝ) := mul_le_mul_of_nonneg_left (hsz j (Nat.le_of_lt hij)) hγ.le
          _ ≤ _ := hnext j hij
      refine ⟨S', fun j => (hf j).trans (hSP j), ?_, hFsize, ?_⟩
      · intro j
        rcases lt_trichotomy j i with hj | rfl | hij
        · simpa [S', hj.ne, not_lt_of_gt hj] using hS j
        · simp [S']
        · have hp : (0 : ℝ) < γ ^ (k+1) * M := by positivity
          have hh := hp.trans_le (hFsize j hij)
          exact Finset.card_pos.mp (by exact_mod_cast hh)
      · intro j l hj hjl y hy z hz
        by_cases hjk : (j : ℕ) < k
        · exact hc j l hjk hjl y (hf j hy) z (hf l hz)
        · have heq : j = i := Fin.ext (by change (j : ℕ) = k; omega)
          subst j
          have hyx : y = x := by simpa [S'] using hy
          subst y
          have hzc : z ∈ candidates G F i l x (S l) := by simpa [S', hjl.ne.symm, hjl] using hz
          exact (mem_candidates.mp hzc).2
  obtain ⟨S, hSP, hS, _, hc⟩ := recParts 5 le_rfl
  exact hfree (embedding_of_five_parts hS
    (fun i j hij => Disjoint.mono (hSP i) (hSP j) (hP hij))
    (fun i j hij => hc i j i.isLt hij))

theorem sparse_pair {V : Type*} {G : SimpleGraph V}
    {F : SimpleGraph (Fin 5)} (hfree : Free F G)
    (U : Finset V) (hU : 10 ≤ U.card) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      (γ^5 / 50) * U.card ≤ (A.card : ℝ) ∧ (γ^5 / 50) * U.card ≤ (B.card : ℝ) ∧
      ((∀ x ∈ A, (neighborsIn G x B).card ≤ γ * (B.card : ℝ)) ∨
       (∀ x ∈ A, (neighborsIn Gᶜ x B).card ≤ γ * (B.card : ℝ))) := by
  classical
  let m := U.card / 5
  have hm : 0 < m := by dsimp [m]; omega
  have hmU : 5*m ≤ U.card := by dsimp [m]; omega
  have hcard : U.card ≤ 10*m := by dsimp [m]; omega
  let e : (U : Set V) ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let block (i : Fin 5) (j : Fin m) : Fin U.card :=
    ⟨(i : ℕ) * m + j, by
      calc
        (i : ℕ) * m + j < ((i : ℕ)+1) * m := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left j.isLt _
        _ ≤ 5*m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := hmU⟩
  have hinj (i j : Fin 5) (u v : Fin m) (h : block i u = block j v) : i = j ∧ u = v := by
    have hh : (i : ℕ)*m + u = (j : ℕ)*m + v := congrArg Fin.val h
    have hi : i = j := by
      apply Fin.ext
      have hx (i : Fin 5) (v : Fin m) : (((i : ℕ)*m + v) / m) = i := by
        rw [Nat.mul_comm (i : ℕ) m, Nat.mul_add_div hm, Nat.div_eq_of_lt v.isLt, add_zero]
      rw [← hx i u, ← hx j v, hh]
    subst j
    exact ⟨rfl, Fin.ext (by omega)⟩
  let part (i : Fin 5) : Fin m ↪ V :=
    ⟨fun j => e.symm (block i j), fun u v h => (hinj i i u v
      (e.symm.injective (Subtype.ext h))).2⟩
  let P (i : Fin 5) : Finset V := Finset.univ.map (part i)
  have hPU : ∀ i, P i ⊆ U := by
    intro i x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e.symm (block i j)).property
  have hP : Pairwise (Function.onFun Disjoint P) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨v, _, he⟩ := Finset.mem_map.mp hxj
    exact hij (hinj i j u v (e.symm.injective (Subtype.ext he.symm))).1
  have hM : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hPsize : ∀ i, (m : ℝ) ≤ ((P i).card : ℝ) := by
    intro i
    simp [P]
  obtain ⟨A, B, hAU, hBU, hAB, hA, hB, hchoice⟩ :=
    sparse_pair_from_parts hfree hPU hP hγ hγ1 hM hPsize
  have hle : (γ^5 / 50) * (U.card : ℝ) ≤ γ^5 * m / 5 := by
    have hcard' : (U.card : ℝ) ≤ (10 : ℝ) * m := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_left hcard' (pow_nonneg hγ.le 5)]
  exact ⟨A, B, hAU, hBU, hAB, hle.trans hA, hle.trans hB, hchoice⟩

end FivePath

namespace FivePath

private theorem sparse_merge_step {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} {m : ℕ} {α β γ K : ℝ}
    (hm : 0 < m) (hγ : 0 < γ) (hαγ : 4*γ ≤ α)
    (hAB : Disjoint A B) (hA : K * (m : ℝ) ≤ A.card) (hB : 2 * K * (m : ℝ) ≤ B.card)
    (hpoint : ∀ a ∈ A, (neighborsIn G a B).card ≤ γ * (B.card : ℝ))
    (rec : ∀ U : Finset V, K * (m : ℝ) ≤ U.card →
      ∃ X : Finset V, X ⊆ U ∧ X.card = m ∧ (Sparse G X (3*α/2) ∨ Sparse Gᶜ X β)) :
    ∃ X : Finset V, X ⊆ A ∪ B ∧ X.card = m ∧ (Sparse G X α ∨ Sparse Gᶜ X β) := by
  classical
  obtain ⟨A', hAA', hAc, hSparse | hDense⟩ := rec A hA
  swap
  · exact ⟨A', hAA'.trans Finset.subset_union_left, hAc, Or.inr hDense⟩
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (hAc.symm ▸ hm)
  have hcount := edgeCount_le_mul G A' B γ (fun a ha => hpoint a (hAA' ha))
  obtain ⟨B₁, hBB₁, hBsize, hB₁⟩ := good_row_subset G A' B hγ hA'ne hcount
  have hB₁size : K * (m : ℝ) ≤ B₁.card := by linarith
  obtain ⟨B', hBB', hBc, hSparseB | hDense⟩ := rec B₁ hB₁size
  swap
  · exact ⟨B', (hBB'.trans hBB₁).trans Finset.subset_union_right, hBc, Or.inr hDense⟩
  have hd : Disjoint A' B' := Disjoint.mono hAA' (hBB'.trans hBB₁) hAB
  have hUB : A' ∪ B' ⊆ A ∪ B := Finset.union_subset_union hAA' (hBB'.trans hBB₁)
  have hcount' := edgeCount_le_mul G B' A' (2*γ) (fun b hb => hB₁ b (hBB' hb))
  have hcard : (A' ∪ B').card = m + m := by rw [Finset.card_union_of_disjoint hd, hAc, hBc]
  have hmerge : Sparse G (A' ∪ B') α := by
    unfold Sparse at *
    rw [edgeCount_union G hd, hcard, Nat.cast_add]
    rw [hAc] at hSparse
    rw [hBc] at hSparseB
    rw [hAc, hBc] at hcount'
    have hα := mul_le_mul_of_nonneg_right hαγ (sq_nonneg (m : ℝ))
    nlinarith
  obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card G (A' ∪ B') (m := m)
    (by rw [hcard]; omega) (by linarith) hmerge
  exact ⟨X, hX.trans hUB, hXm, Or.inl hXS⟩

private theorem sparse_find_card {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {V : Type} (G : SimpleGraph V) (F : SimpleGraph (Fin 5)), Free F G → ∀ (U : Finset V) (m : ℕ),
      0 < m → K * (m : ℝ) ≤ U.card → ∀ α β : ℝ,
      4*γ ≤ α → 4*γ ≤ β → (1/4 : ℝ) ≤ (3/2 : ℝ)^k * α * β →
      ∃ X : Finset V, X ⊆ U ∧ X.card = m ∧ (Sparse G X α ∨ Sparse Gᶜ X β) := by
  classical
  induction k with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    intro V G F _ U m _ hKm α β hα hβ hprod
    have hmc : (m : ℝ) ≤ U.card := by simpa using hKm
    have hmU : m ≤ U.card := by exact_mod_cast hmc
    have hsum : 1 ≤ α + β := by
      simp only [pow_zero, one_mul] at hprod
      have hsq : (1 : ℝ)^2 ≤ (α + β)^2 := by nlinarith [sq_nonneg (α - β)]
      exact (sq_le_sq₀ (by norm_num) (by linarith)).mp hsq
    have hchoice : Sparse G U α ∨ Sparse Gᶜ U β := by
      by_contra! h
      simp only [Sparse, not_le] at h
      have hc := edgeCount_compl_le G U
      have hs := mul_le_mul_of_nonneg_right hsum (sq_nonneg (U.card : ℝ))
      nlinarith [h.1, h.2]
    rcases hchoice with h | h
    · obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card G U hmU (by linarith) h
      exact ⟨X, hX, hXm, Or.inl hXS⟩
    · obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card Gᶜ U hmU (by linarith) h
      exact ⟨X, hX, hXm, Or.inr hXS⟩
  | succ k ih =>
    obtain ⟨K, hK, ih⟩ := ih
    let ρ := γ^5 / 50
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    let L := max (2*K/ρ) 10
    have hL : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 10).trans (le_max_right _ _)
    refine ⟨L, hL, ?_⟩
    intro V G F hfree U m hm hLm α β hα hβ hprod
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hU10 : 10 ≤ U.card := by
      have hL10 : (10 : ℝ) ≤ L := le_max_right _ _
      have h : (10 : ℝ) ≤ U.card := calc
        _ ≤ L := hL10
        _ ≤ L * (m : ℝ) := le_mul_of_one_le_right (by linarith) hmR
        _ ≤ _ := hLm
      exact_mod_cast h
    have hlow : 2 * K * (m : ℝ) ≤ ρ * (U.card : ℝ) := by
      have hhead : (2*K/ρ) * (m : ℝ) ≤ U.card :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hLm
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ] at hhead
      simpa [mul_comm] using hhead
    obtain ⟨A, B, hAU, hBU, hAB, hcardA, hcardB, hside⟩ := sparse_pair hfree U hU10 hγ hγ1
    have hcapA : K * (m : ℝ) ≤ A.card := by
      have h := hlow.trans hcardA
      nlinarith [mul_nonneg (show 0 ≤ K by linarith) (Nat.cast_nonneg (α := ℝ) m)]
    have hcapB := hlow.trans hcardB
    have recProd {a b : ℝ} (h : (1/4 : ℝ) ≤ (3/2 : ℝ)^(k+1)*a*b) :
        (1/4 : ℝ) ≤ (3/2 : ℝ)^k*(3*a/2)*b := by
      convert h using 1
      rw [pow_succ]
      ring
    rcases hside with hG | hGc
    · obtain ⟨X, hX, hmX, hs⟩ := sparse_merge_step G hm hγ hα hAB hcapA hcapB hG
        (fun U' hU' => ih G F hfree U' m hm hU' (3*α/2) β (by linarith) hβ (recProd hprod))
      exact ⟨X, hX.trans (Finset.union_subset hAU hBU), hmX, hs⟩
    · have hprod' : (1/4 : ℝ) ≤ (3/2 : ℝ)^(k+1)*β*α := by
        convert hprod using 1
        ring
      obtain ⟨X, hX, hmX, hs⟩ := sparse_merge_step Gᶜ hm hγ hβ hAB hcapA hcapB hGc
        (fun U' hU' => ih Gᶜ Fᶜ (free_compl.mpr hfree) U' m hm hU' (3*β/2) α
          (by linarith) hα (recProd hprod'))
      exact ⟨X, hX.trans (Finset.union_subset hAU hBU), hmX, by simpa [or_comm] using hs⟩

theorem sparse_side (F : SimpleGraph (Fin 5)) : SparseSide F := by
  classical
  intro ε hε
  let η : ℝ := min (ε/4) 1
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : 4*η ≤ ε := by linarith [min_le_left (ε/4) (1 : ℝ)]
  have hη2 : 0 < η^2 := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1/4 : ℝ)/η^2)
    (by norm_num : (1 : ℝ) < 3/2)
  have hprod : (1/4 : ℝ) ≤ (3/2 : ℝ)^k * η * η := by
    have hh := (div_lt_iff₀ hη2).mp hk
    nlinarith
  obtain ⟨K, hK, hd⟩ := sparse_find_card (γ := η/4)
    (by positivity) (by linarith : η/4 ≤ 1) k
  have hK0 : 0 < K := by linarith
  refine ⟨1/(4*K), by positivity, ?_⟩
  intro V _ G hfree
  let n := Fintype.card V
  by_cases hn : 0 < n
  swap
  · have hn0 : n = 0 := by omega
    exact ⟨∅, by simp [show Fintype.card V = 0 from hn0], Or.inl (by simp)⟩
  by_cases hub : (n : ℝ) < 2*K
  · have hnV : 0 < Fintype.card V := hn
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hnV
    refine ⟨{x}, ?_, Or.inl ?_⟩
    · rw [Finset.card_singleton, Nat.cast_one]
      have hh : (n : ℝ)/(4*K) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : 0 < 4*K)).mpr
        linarith
      simpa [div_eq_mul_inv, mul_comm] using hh
    · intro y hy
      have hye : y = x := Finset.mem_singleton.mp hy
      subst y
      have he : neighborsIn G x ({x} : Finset V) = ∅ := by
        ext y
        simp only [mem_neighborsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, h⟩
        exact G.irrefl h
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  let m := ⌊(n : ℝ)/K⌋₊
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmK : K * (m : ℝ) ≤ n := by
    have h := Nat.floor_le (show 0 ≤ (n : ℝ)/K by positivity)
    have hh := (le_div_iff₀ hK0).mp h
    simpa [mul_comm] using hh
  have hdiv2 : (2 : ℝ) ≤ (n : ℝ)/K := (le_div_iff₀ hK0).mpr (le_of_not_gt hub)
  have hmL : (n : ℝ)/(2*K) ≤ (m : ℝ) := by
    have hh := Nat.lt_floor_add_one ((n : ℝ)/K)
    change (n : ℝ)/K < (m : ℝ) + 1 at hh
    have he : (n : ℝ)/(2*K) = ((n : ℝ)/K)/2 := by ring
    rw [he]
    linarith
  have hm : 0 < m := by
    have h : (0 : ℝ) < m := (by positivity : 0 < (n : ℝ)/(2*K)).trans_le hmL
    exact_mod_cast h
  obtain ⟨X, _, hXm, hside⟩ := hd G F hfree Finset.univ m hm
    (by simpa using hmK) η η (by linarith) (by linarith) hprod
  have finish {H : SimpleGraph V} (hH : Sparse H X η) :
      ∃ Y : Finset V, (1/(4*K)) * (Fintype.card V : ℝ) ≤ Y.card ∧
        ∀ y ∈ Y, (neighborsIn H y Y).card ≤ ε * (Y.card : ℝ) := by
    have hXne : X.Nonempty := Finset.card_pos.mp (hXm.symm ▸ hm)
    have hX := hH
    unfold Sparse at hX
    rw [sq, ← mul_assoc] at hX
    obtain ⟨Y, hYX, hYsz, hdt⟩ := good_row_subset H X X hη hXne hX
    refine ⟨Y, ?_, fun y hy => ?_⟩
    · have he : (1/(4*K)) * (n : ℝ) = ((n : ℝ)/(2*K))/2 := by ring
      change (1/(4*K)) * (n : ℝ) ≤ Y.card
      rw [he]
      rw [hXm] at hYsz
      linarith
    · have hm' : ((neighborsIn H y Y).card : ℝ) ≤ (neighborsIn H y X).card := by
        exact_mod_cast Finset.card_le_card (neighborsIn_mono hYX)
      refine hm'.trans ((hdt y hy).trans ?_)
      have hh := mul_le_mul_of_nonneg_left (show (X.card : ℝ) ≤ 2 * Y.card by linarith)
        (by positivity : 0 ≤ 2*η)
      have hε' := mul_le_mul_of_nonneg_right hηε (Nat.cast_nonneg (α := ℝ) Y.card)
      nlinarith
  rcases hside with hG | hGc
  · obtain ⟨Y, hY, hD⟩ := finish hG
    exact ⟨Y, hY, Or.inl hD⟩
  · obtain ⟨Y, hY, hD⟩ := finish hGc
    exact ⟨Y, hY, Or.inr hD⟩

end FivePath

namespace FivePath

private noncomputable def uncovered {V : Type*} (G : SimpleGraph V) (S B : Finset V) :
    Finset V := by
  classical
  exact B.filter fun b => ∀ a ∈ S, ¬ G.Adj a b

private theorem mem_uncovered {V : Type*} {G : SimpleGraph V} {S B : Finset V} {b : V} :
    b ∈ uncovered G S B ↔ b ∈ B ∧ ∀ a ∈ S, ¬ G.Adj a b := by
  classical
  simp [uncovered]

private theorem product_pow_count {x : ℝ} (hx' : x ≤ 1) (k : ℕ) :
    (1-x)^k * (1 + (k : ℝ)*x) ≤ 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : (1-x)*(1+(↑k+1 : ℝ)*x) ≤ 1 + (k : ℝ)*x := by
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ)+1 by positivity) (sq_nonneg x)]
    rw [pow_succ, Nat.cast_succ, mul_assoc]
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg (sub_nonneg.mpr hx') k)).trans ih

noncomputable def covered {V : Type*} (G : SimpleGraph V) (S B : Finset V) :
    Finset V := by
  classical
  exact B.filter fun b => ∃ a ∈ S, G.Adj a b

/-- A deterministic version of the covering lemma, with a ceiling in the cardinal bound. -/
theorem small_cover {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    (hA : A.Nonempty) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hd : ∀ b ∈ B, x * (A.card : ℝ) ≤ (neighborsIn G b A).card) :
    ∃ S : Finset V, S ⊆ A ∧ S.card ≤ ⌈1/x⌉₊ ∧
      (B.card : ℝ)/2 ≤ ((covered G S B).card : ℝ) := by
  classical
  have hA0 : (0 : ℝ) < A.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have build (k : ℕ) : ∃ S : Finset V, S ⊆ A ∧ S.card ≤ k ∧
      ((uncovered G S B).card : ℝ) ≤ (1-x)^k * B.card := by
    induction k with
    | zero =>
      have he : uncovered G ∅ B = B := by ext b; simp [mem_uncovered]
      exact ⟨∅, Finset.empty_subset _, by simp, by simp [he]⟩
    | succ k ih =>
      obtain ⟨S, hSA, hSk, hS⟩ := ih
      let U := uncovered G S B
      obtain ⟨a, haA, hamax⟩ := Finset.exists_max_image A
        (fun a => (neighborsIn G a U).card) hA
      have hcount : x * (A.card : ℝ) * U.card ≤ edgeCountBetween G U A := by
        unfold edgeCountBetween
        calc
          _ = ∑ _ ∈ U, x * (A.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun b hb => hd b (mem_uncovered.mp hb).1
      have hrev : edgeCountBetween G A U ≤ (A.card : ℝ) * (neighborsIn G a U).card := by
        unfold edgeCountBetween
        calc
          _ ≤ ∑ _ ∈ A, ((neighborsIn G a U).card : ℝ) :=
            Finset.sum_le_sum fun b hb => by exact_mod_cast hamax b hb
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hmax : x * (U.card : ℝ) ≤ (neighborsIn G a U).card := by
        rw [edgeCount_comm] at hcount
        apply (mul_le_mul_iff_left₀ hA0).mp
        have h := hcount.trans hrev
        nlinarith
      have he : uncovered G (insert a S) B = U \ neighborsIn G a U := by
        ext b
        simp only [U, mem_uncovered, Finset.mem_sdiff, mem_neighborsIn, Finset.mem_insert]
        constructor
        · rintro ⟨hb, hn⟩
          exact ⟨⟨hb, fun c hc => hn c (Or.inr hc)⟩, fun h => hn a (Or.inl rfl) h.2⟩
        · rintro ⟨⟨hb, hn⟩, ha⟩
          refine ⟨hb, fun c hc => ?_⟩
          rcases hc with he | he
          · subst c
            exact fun h => ha ⟨⟨hb, hn⟩, h⟩
          · exact hn c he
      have hc : ((uncovered G (insert a S) B).card : ℝ) + (neighborsIn G a U).card = U.card := by
        rw [he]
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (fun _ hv => (mem_neighborsIn.mp hv).1)
      refine ⟨insert a S, Finset.insert_subset_iff.mpr ⟨haA, hSA⟩,
        (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hSk), ?_⟩
      calc
        _ ≤ (1-x) * (U.card : ℝ) := by linarith
        _ ≤ (1-x) * ((1-x)^k * (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hx1)
        _ = _ := by rw [pow_succ]; ring
  let k := ⌈1/x⌉₊
  obtain ⟨S, hSA, hSk, hleft⟩ := build k
  have hk : (1/x : ℝ) ≤ k := Nat.le_ceil _
  have hy : (1 : ℝ) ≤ (k : ℝ)*x := by
    rw [div_le_iff₀ hx] at hk
    exact hk
  have hpow : (1-x)^k ≤ (1/2 : ℝ) := by
    have hp := product_pow_count hx1 k
    have hh := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 1 + (k : ℝ)*x by linarith)
      (pow_nonneg (sub_nonneg.mpr hx1) k)
    linarith
  have hleft' : ((uncovered G S B).card : ℝ) ≤ (1/2 : ℝ) * B.card :=
    hleft.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
  let C := covered G S B
  have he : uncovered G S B = B \ C := by
    ext b
    simp only [mem_uncovered, C, covered, Finset.mem_sdiff, Finset.mem_filter, not_and, not_exists, and_congr_right_iff]
    intro hb
    simp [hb]
  have hparts : ((uncovered G S B).card : ℝ) + C.card = B.card := by
    rw [he]
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  exact ⟨S, hSA, hSk, by linarith⟩

end FivePath

namespace FivePath

def DegreeBound {V : Type*} (G : SimpleGraph V) (U : Finset V) (x : ℝ) : Prop :=
  ∀ v ∈ U, (neighborsIn G v U).card ≤ x * (U.card : ℝ)

private theorem sparse_rows_from_total {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    {T D : ℝ} (hT : 0 < T) (hAB : edgeCountBetween G A B ≤ D*T) :
    ∃ A' : Finset V, A' ⊆ A ∧ (A.card : ℝ) ≤ (A'.card : ℝ) + D ∧
      ∀ a ∈ A', ((neighborsIn G a B).card : ℝ) ≤ T := by
  classical
  let C := A.filter (fun a => T < ((neighborsIn G a B).card : ℝ))
  let A' := A \ C
  have hCA : C ⊆ A := Finset.filter_subset _ _
  have hc : ((C.card : ℝ)*T) ≤ edgeCountBetween G A B := by
    unfold edgeCountBetween
    calc
      _ = ∑ _ ∈ C, T := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ C, ((neighborsIn G a B).card : ℝ) :=
        Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hCA (fun _ _ _ => by positivity)
  have hd : (C.card : ℝ) ≤ D := le_of_mul_le_mul_right (hc.trans hAB) hT
  have hcount : (A'.card : ℝ) + C.card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hCA
  refine ⟨A', Finset.sdiff_subset, by linarith, fun a ha => ?_⟩
  apply le_of_not_gt
  intro hadd
  exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_filter.mpr ⟨Finset.sdiff_subset ha, hadd⟩)

private theorem edgeCount_degree_cap {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    {t : ℝ} (h : ∀ a ∈ A, (neighborsIn G a B).card ≤ t) :
    edgeCountBetween G A B ≤ (A.card : ℝ)*t := by
  unfold edgeCountBetween
  calc
    _ ≤ ∑ _ ∈ A, t := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

def SparsePair {V : Type*} (G : SimpleGraph V) (U : Finset V) (x y : ℝ) : Prop :=
  ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧ Disjoint X Y ∧
    y^4 * (U.card : ℝ) ≤ (X.card : ℝ) ∧ (1-4*y) * (U.card : ℝ) ≤ (Y.card : ℝ) ∧
    ∀ z ∈ Y, (neighborsIn G z X).card ≤ x * (X.card : ℝ)

/-- Find a large sparse pair or the two layers of the neighborhood comb. -/
theorem sparse_pair_or_comb_input {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1/256)
    (hsize : 1 ≤ y^4 * (U.card : ℝ)) (hdeg : DegreeBound G U (y^3))
    (hbig : ¬ DegreeBound G U (2*y^4)) :
    SparsePair G U x y ∨
    ∃ v ∈ U, ∃ A B : Finset V, A ⊆ U ∧ B ⊆ neighborsIn G v U ∧ Disjoint A B ∧
      (∀ a ∈ A, v ≠ a ∧ ¬ G.Adj v a) ∧
      (1-3*y) * (U.card : ℝ) ≤ (A.card : ℝ) ∧
      y^4 * (U.card : ℝ) ≤ (B.card : ℝ) ∧
      (∀ a ∈ A, (neighborsIn G a B).card ≤ y^2 * (B.card : ℝ)) ∧
      (∀ b ∈ B, x^2 * (A.card : ℝ) ≤ (neighborsIn G b A).card) := by
  classical
  let W : ℝ := U.card
  have hW : 0 < W := by
    by_contra! h
    have hz : W = 0 := le_antisymm h (by dsimp [W]; positivity)
    change 1 ≤ y^4*W at hsize
    rw [hz, mul_zero] at hsize
    norm_num at hsize
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := by linarith
  simp only [DegreeBound, not_forall, not_le] at hbig
  obtain ⟨v, hv, hvbig⟩ := hbig
  let N := neighborsIn G v U
  have hNU : N ⊆ U := fun _ hz => (mem_neighborsIn.mp hz).1
  have hNbig : 2*y^4*W < (N.card : ℝ) := hvbig
  have hNpos : (0 : ℝ) < N.card := (by positivity : 0 < 2*y^4*W).trans hNbig
  let R := U \ insert v N
  have hRU : R ⊆ U := Finset.sdiff_subset
  have hRN : Disjoint R N := Finset.disjoint_left.mpr fun _ hR hN =>
    (Finset.mem_sdiff.mp hR).2 (Finset.mem_insert_of_mem hN)
  have hRsize : (1-y)*W ≤ (R.card : ℝ) := by
    have hparts : (R.card : ℝ) + (insert v N).card = W := by
      dsimp [W]
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.insert_subset_iff.mpr ⟨hv, hNU⟩)
    have hcap : ((insert v N).card : ℝ) ≤ (N.card : ℝ)+1 := by
      exact_mod_cast Finset.card_insert_le v N
    have hNv : (N.card : ℝ) ≤ y^3*W := hdeg v hv
    have hpow : y^3+y^4 ≤ y := by
      have h₃ : y^3 ≤ y^2 := pow_le_pow_of_le_one hy0.le hy1 (by decide)
      have h₄ : y^4 ≤ y^2 := pow_le_pow_of_le_one hy0.le hy1 (by decide)
      have hs : y^2 ≤ y/2 := by nlinarith [mul_le_mul_of_nonneg_left (show y≤1/2 by linarith) hy0.le]
      linarith
    change 1 ≤ y^4*W at hsize
    nlinarith [mul_le_mul_of_nonneg_right hpow hW.le]
  have hgood_total : edgeCountBetween G R N ≤ (2*y*W)*(y^2*(N.card : ℝ)/2) := by
    rw [edgeCount_comm]
    have hh : edgeCountBetween G N R ≤ (N.card : ℝ)*(y^3*W) := by
      apply edgeCount_degree_cap
      intro b hb
      exact (by exact_mod_cast Finset.card_le_card (neighborsIn_mono hRU) :
        ((neighborsIn G b R).card : ℝ) ≤ (neighborsIn G b U).card).trans
        (hdeg b (hNU hb))
    convert hh using 1
    ring
  obtain ⟨A, hAR, hAsize, hadjA⟩ := sparse_rows_from_total G R N (by positivity) hgood_total
  have hAV : A ⊆ U := hAR.trans hRU
  have hAcard : (1-3*y)*W ≤ (A.card : ℝ) := by nlinarith
  have hA0 : (0 : ℝ) < A.card := (mul_pos (by linarith) hW).trans_le hAcard
  let C := N.filter fun z => ((neighborsIn G z A).card : ℝ) < x^2 * (A.card : ℝ)
  have hCN : C ⊆ N := Finset.filter_subset _ _
  by_cases hc : y^4*W ≤ (C.card : ℝ)
  · apply Or.inl
    have hCpos : (0 : ℝ) < C.card := (by positivity : 0 < y^4*W).trans_le hc
    have htotal : edgeCountBetween G A C ≤ (x*(A.card : ℝ))*(x*(C.card : ℝ)) := by
      rw [edgeCount_comm]
      have hh := edgeCount_degree_cap G C A (fun z hz => ((Finset.mem_filter.mp hz).2 :
        ((neighborsIn G z A).card : ℝ) < x^2*(A.card : ℝ)).le)
      convert hh using 1
      ring
    obtain ⟨Y, hYA, hYsize, hYdeg⟩ := sparse_rows_from_total G A C (by positivity) htotal
    have hYcard : (1-4*y)*W ≤ (Y.card : ℝ) := by
      have Hz : 0 ≤ 1-x := by linarith
      have hmul := mul_le_mul_of_nonneg_left hAcard Hz
      have hh : 1-4*y ≤ (1-x)*(1-3*y) := by
        nlinarith [mul_nonneg hx.le hy0.le]
      nlinarith [mul_le_mul_of_nonneg_right hh hW.le]
    exact ⟨C, Y, hCN.trans hNU, hYA.trans hAV,
      (Disjoint.mono (hYA.trans hAR) hCN hRN).symm, hc, hYcard, hYdeg⟩
  · let B := N \ C
    have hBN : B ⊆ N := Finset.sdiff_subset
    have hBsum : (B.card : ℝ) + C.card = N.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hCN
    have hBcard : y^4*W ≤ (B.card : ℝ) := by linarith
    have hBhalf : (N.card : ℝ)/2 ≤ (B.card : ℝ) := by linarith
    apply Or.inr
    refine ⟨v, hv, A, B, hAV, hBN, Disjoint.mono hAR hBN hRN, ?_, hAcard, hBcard, ?_, ?_⟩
    · intro a ha
      have hn := (Finset.mem_sdiff.mp (hAR ha)).2
      exact ⟨fun eq => hn (Finset.mem_insert.mpr (Or.inl eq.symm)), fun he =>
        hn (Finset.mem_insert_of_mem (mem_neighborsIn.mpr ⟨hAV ha, he⟩))⟩
    · intro a ha
      calc
        (neighborsIn G a B).card ≤ ((neighborsIn G a N).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (neighborsIn_mono hBN)
        _ ≤ y^2 * (N.card : ℝ) / 2 := hadjA a ha
        _ ≤ y^2 * (B.card : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hBhalf (sq_nonneg y)]
    · intro b hb
      apply le_of_not_gt
      intro h
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨hBN hb, h⟩)

end FivePath

namespace FivePath

def ClosedWithin {V : Type*} (G : SimpleGraph V) (U A : Finset V) : Prop :=
  A ⊆ U ∧ ∀ x ∈ A, ∀ y ∈ U, G.Adj x y → y ∈ A

theorem connected_component_within {V : Type*} (G : SimpleGraph V)
    {U : Finset V} {v : V} (hv : v ∈ U) :
    ∃ A : Finset V, v ∈ A ∧ ClosedWithin G U A ∧ internallyConnected G A := by
  classical
  let H := G.induce (U : Set V)
  let c := H.connectedComponentMk ⟨v, hv⟩
  let val : (U : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let A := c.supp.toFinset.map val
  have hmem {x : V} : x ∈ A ↔ ∃ hx : x ∈ U, (⟨x, hx⟩ : (U : Set V)) ∈ c.supp := by
    constructor
    · intro hx
      obtain ⟨⟨y, hy⟩, h, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨hy, Set.mem_toFinset.mp h⟩
    · rintro ⟨hx, hc⟩
      exact Finset.mem_map.mpr ⟨⟨x, hx⟩, Set.mem_toFinset.mpr hc, rfl⟩
  have hAU : A ⊆ U := fun _ hx => (hmem.mp hx).choose
  refine ⟨A, hmem.mpr ⟨hv, rfl⟩, ⟨hAU, ?_⟩, ?_⟩
  · intro x hx y hy hadj
    obtain ⟨hxu, hxc⟩ := hmem.mp hx
    exact hmem.mpr ⟨hy, c.mem_supp_of_adj_mem_supp hxc (show H.Adj ⟨x, hxu⟩ ⟨y, hy⟩ from hadj)⟩
  · let e : c.toSimpleGraph ≃g G.induce (A : Set V) := {
      toFun := fun x => ⟨x.val.val, hmem.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x => ⟨⟨x.val, hAU x.property⟩, (hmem.mp x.property).choose_spec⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl
      map_rel_iff' := Iff.rfl }
    exact c.connected_toSimpleGraph.map e.toHom e.surjective

def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y

theorem closed_anticomplete {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U A : Finset V}
    (h : ClosedWithin G U A) : Anticomplete G A (U \ A) := by
  intro x hx y hy hadj
  exact (Finset.mem_sdiff.mp hy).2 (h.2 x hx y (Finset.mem_sdiff.mp hy).1 hadj)

theorem closed_disjoint_union {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U A B : Finset V}
    (hA : ClosedWithin G U A) (hB : ClosedWithin G U B) : ClosedWithin G U (A ∪ B) := by
  refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
  intro x hx y hy hadj
  rcases Finset.mem_union.mp hx with hxA | hxB
  · exact Finset.mem_union_left _ (hA.2 x hxA y hy hadj)
  · exact Finset.mem_union_right _ (hB.2 x hxB y hy hadj)

theorem component_of_no_large_pair {V : Type*} (G : SimpleGraph V) (U : Finset V)
    {t : ℝ} (ht : 0 < t) (hU : 3*t ≤ (U.card : ℝ))
    (hno : ∀ A B : Finset V, A ⊆ U → B ⊆ U → Disjoint A B →
      t ≤ (A.card : ℝ) → t ≤ (B.card : ℝ) → Anticomplete G A B → False) :
    ∃ A : Finset V, ClosedWithin G U A ∧ internallyConnected G A ∧
      (U.card : ℝ) - t < (A.card : ℝ) := by
  classical
  let L := U.powerset.filter fun A => ClosedWithin G U A ∧ (A.card : ℝ) < t
  have hm {A : Finset V} : A ∈ L ↔ ClosedWithin G U A ∧ (A.card : ℝ) < t := by
    simp only [L, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩
  have hL : L.Nonempty := ⟨∅, hm.mpr ⟨⟨Finset.empty_subset _, by simp⟩, by simpa using ht⟩⟩
  obtain ⟨A, hA, hAmax⟩ := Finset.exists_max_image L Finset.card hL
  have hAU := (hm.mp hA).1
  have hAt := (hm.mp hA).2
  have hAlt : A.card < U.card := by
    have hr : (A.card : ℝ) < U.card := by linarith
    exact_mod_cast hr
  obtain ⟨v, hv, hvA⟩ := Finset.exists_mem_notMem_of_card_lt_card hAlt
  obtain ⟨C, hvC, hC, hConn⟩ := connected_component_within G hv
  have hDis : Disjoint A C := by
    by_contra! hn
    obtain ⟨x, hAx, hCx⟩ := Finset.not_disjoint_iff.mp hn
    obtain ⟨a, ha, b, hb, hab, hap, hbp⟩ := edge_crossing hConn (· ∈ A) hCx hvC hAx hvA
    exact hbp (hAU.2 a hap b (hC.1 hb) hab)
  have hCge : t ≤ (C.card : ℝ) := by
    by_contra! hCt
    have hc : (0 : ℕ) < C.card := Finset.card_pos.mpr ⟨v, hvC⟩
    have hAC := closed_disjoint_union hAU hC
    have hACcard : (A ∪ C).card = A.card + C.card := Finset.card_union_of_disjoint hDis
    have hACcardR : ((A ∪ C).card : ℝ) = (A.card : ℝ) + C.card := by exact_mod_cast hACcard
    have hACsize : t ≤ ((A ∪ C).card : ℝ) := by
      by_contra! h
      have hh := hAmax (A ∪ C) (hm.mpr ⟨hAC, h⟩)
      omega
    have h1 : ((U \ (A ∪ C)).card : ℝ) + (A ∪ C).card = U.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hAC.1
    exact hno _ _ hAC.1 Finset.sdiff_subset
      (Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
      hACsize (by linarith) (closed_anticomplete hAC)
  refine ⟨C, hC, hConn, ?_⟩
  by_contra! h
  have hsum : ((U \ C).card : ℝ) + C.card = U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hC.1
  exact hno _ _ hC.1 Finset.sdiff_subset
    (Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
    hCge (by linarith) (closed_anticomplete hC)

theorem sparse_path_has_large_pair {V : Type*} {G : SimpleGraph V} (hfree : PathFree G)
    (U : Finset V) (hU : 2 ≤ U.card)
    (hdeg : ∀ u ∈ U, (neighborsIn G u U).card ≤ (U.card : ℝ)/32) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      (U.card : ℝ)/32 ≤ A.card ∧ (U.card : ℝ)/32 ≤ B.card ∧ Anticomplete G A B := by
  classical
  let t : ℝ := (U.card : ℝ)/32
  have ht : 0 < t := by
    dsimp [t]
    have h : 0 < U.card := by omega
    positivity
  by_cases ht1 : t < 1
  · have hUc : 1 < Fintype.card ↥U := by rw [Fintype.card_coe]; omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hUc
    have hne : (a : V) ≠ (b : V) := fun he => hab (Subtype.ext he)
    refine ⟨{a.val}, {b.val}, Finset.singleton_subset_iff.mpr a.property, Finset.singleton_subset_iff.mpr b.property,
      by simpa using hne, by simpa using ht1.le, by simpa using ht1.le, ?_⟩
    intro u hu v hv he
    have hue : u = a.val := Finset.mem_singleton.mp hu
    have hve : v = b.val := Finset.mem_singleton.mp hv
    subst u v
    have hn : b.val ∈ neighborsIn G a.val U := mem_neighborsIn.mpr ⟨b.property, he⟩
    have hp : (1 : ℝ) ≤ (neighborsIn G a.val U).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨b.val, hn⟩
    exact ht1.not_ge (hp.trans (hdeg _ a.property))
  have ht1' : 1 ≤ t := le_of_not_gt ht1
  by_contra hno
  have big (X : Finset V) (hX : X ⊆ U) (hXc : 3*t ≤ (X.card : ℝ)) :
      ∃ A : Finset V, ClosedWithin G X A ∧ internallyConnected G A ∧
        (X.card : ℝ) - t < A.card := by
    apply component_of_no_large_pair G X ht hXc
    intro A B hA hB hd hAc hBc hab
    exact hno ⟨A, B, hA.trans hX, hB.trans hX, hd, hAc, hBc, hab⟩
  have hun : (U.card : ℝ) = 32*t := by dsimp [t]; ring
  obtain ⟨F, hF, hFc, hFbig⟩ := big U (Finset.Subset.refl _) (by linarith)
  have nonempty (X : Finset V) (h : (0 : ℝ) < X.card) : X.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast h)
  obtain ⟨v, hv⟩ := nonempty F (by linarith)
  let N := neighborsIn G v F
  have hdeg' {w : V} (hw : w ∈ U) {X : Finset V} (hX : X ⊆ U) :
      (neighborsIn G w X).card ≤ t := by
    have hh : ((neighborsIn G w X).card : ℝ) ≤ (neighborsIn G w U).card := by
      exact_mod_cast Finset.card_le_card (neighborsIn_mono hX)
    exact hh.trans (hdeg w hw)
  have hN : insert v N ⊆ F :=
    Finset.insert_subset_iff.mpr ⟨hv, fun _ h => (mem_neighborsIn.mp h).1⟩
  let R := F \ insert v N
  have hRF : R ⊆ F := Finset.sdiff_subset
  have hRsize : 29*t < (R.card : ℝ) := by
    have hsplit : (R.card : ℝ) + (insert v N).card = F.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hN
    have hNcard : ((insert v N).card : ℝ) ≤ (N.card : ℝ)+1 := by
      exact_mod_cast Finset.card_insert_le v N
    have hn := hdeg' (hF.1 hv) hF.1
    change (N.card : ℝ) ≤ t at hn
    linarith
  obtain ⟨J, hJ, hJc, hJbig⟩ := big R (hRF.trans hF.1) (by linarith)
  have hJR : J ⊆ R := hJ.1
  have hJF : J ⊆ F := hJR.trans hRF
  have hvR : v ∉ R := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
  have hnAdj {w : V} (hw : w ∈ R) : ¬ G.Adj v w := fun he =>
    (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem (mem_neighborsIn.mpr ⟨hRF hw, he⟩))
  obtain ⟨w₀, hw₀⟩ := nonempty J (by linarith)
  obtain ⟨b, hbF, u, huF, hbu, hbJ, huJ⟩ := edge_crossing hFc (· ∈ J)
    (hJF hw₀) hv hw₀ (fun h => hvR (hJR h))
  have huN : u ∈ N := by
    by_contra hn
    have huv : u ≠ v := fun he => hnAdj (hJR hbJ) (he ▸ hbu.symm)
    have huR : u ∈ R := Finset.mem_sdiff.mpr ⟨huF, by simp [huv, hn]⟩
    exact huJ (hJ.2 b hbJ u huR hbu)
  have hvu : G.Adj v u := (mem_neighborsIn.mp huN).2
  let B := neighborsIn G u J
  have hb : b ∈ B := mem_neighborsIn.mpr ⟨hbJ, hbu.symm⟩
  have hBJ : B ⊆ J := fun _ h => (mem_neighborsIn.mp h).1
  have hBsmall : (B.card : ℝ) ≤ t := hdeg' (hF.1 huF) (hJF.trans hF.1)
  let R' := J \ B
  have hR'J : R' ⊆ J := Finset.sdiff_subset
  have hR'size : 27*t < (R'.card : ℝ) := by
    have hh : (R'.card : ℝ) + B.card = J.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hBJ
    linarith
  obtain ⟨K, hK, hKc, hKbig⟩ := big R' (hR'J.trans (hJF.trans hF.1)) (by linarith)
  obtain ⟨q, hq⟩ := nonempty K (by linarith)
  obtain ⟨z, hzJ, w, hwJ, hzw, hzK, hwK⟩ := edge_crossing hJc (· ∈ K)
    (hR'J (hK.1 hq)) hbJ hq (fun h => (Finset.mem_sdiff.mp (hK.1 h)).2 hb)
  have hwB : w ∈ B := by
    by_contra hn
    have hwR' : w ∈ R' := Finset.mem_sdiff.mpr ⟨hwJ, hn⟩
    exact hwK (hK.2 z hzK w hwR' hzw)
  have hwdeg := hdeg' (hF.1 (hJF hwJ)) (hK.1.trans (hR'J.trans (hJF.trans hF.1)))
  have hwlt : (neighborsIn G w K).card < K.card := by
    have hh : ((neighborsIn G w K).card : ℝ) < K.card := by linarith
    exact_mod_cast hh
  obtain ⟨z', hz', hmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card hwlt
  obtain ⟨a, ha, c, hc, hac, hwa, hwc⟩ := edge_crossing hKc (G.Adj w)
    hzK hz' hzw.symm (fun hadj => hmiss (mem_neighborsIn.mpr ⟨hz', hadj⟩))
  have hnAdj' {w : V} (hw : w ∈ K) : ¬ G.Adj u w := fun h =>
    (Finset.mem_sdiff.mp (hK.1 hw)).2 (mem_neighborsIn.mpr ⟨hR'J (hK.1 hw), h⟩)
  exact hfree (induced_path hvu (mem_neighborsIn.mp hwB).2 hwa hac
    (hnAdj (hJR hwJ)) (hnAdj (hJR (hR'J (hK.1 ha)))) (hnAdj (hJR (hR'J (hK.1 hc))))
    (hnAdj' ha) (hnAdj' hc) hwc)

private theorem choose_closed_of_width {V : Type*} (G : SimpleGraph V) (U : Finset V)
    {d w : ℝ} (hw : 0 < w) (hwd : 2*w ≤ d) (hwU : w ≤ U.card)
    (hsmall : ∀ A : Finset V, A ⊆ U → internallyConnected G A → (A.card : ℝ) ≤ d) :
    ∃ A : Finset V, ClosedWithin G U A ∧ w ≤ (A.card : ℝ) ∧ (A.card : ℝ) ≤ d := by
  classical
  let L := U.powerset.filter fun A => ClosedWithin G U A ∧ (A.card : ℝ) < w
  have hm {A : Finset V} : A ∈ L ↔ ClosedWithin G U A ∧ (A.card : ℝ) < w := by
    simp only [L, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩
  have hL : L.Nonempty := ⟨∅, hm.mpr ⟨⟨Finset.empty_subset _, by simp⟩, by simpa using hw⟩⟩
  obtain ⟨A, hA, hAmax⟩ := Finset.exists_max_image L Finset.card hL
  have hAU := (hm.mp hA).1
  have hAw := (hm.mp hA).2
  have hAlt : A.card < U.card := by
    exact_mod_cast hAw.trans_le hwU
  obtain ⟨v, hv, hvA⟩ := Finset.exists_mem_notMem_of_card_lt_card hAlt
  obtain ⟨C, hvC, hC, hConn⟩ := connected_component_within G hv
  by_cases hcw : w ≤ (C.card : ℝ)
  · exact ⟨C, hC, hcw, hsmall C hC.1 hConn⟩
  have hDis : Disjoint A C := by
    by_contra! hn
    obtain ⟨x, hAx, hCx⟩ := Finset.not_disjoint_iff.mp hn
    obtain ⟨a, _, b, hb, hab, hap, hbp⟩ := edge_crossing hConn (· ∈ A) hCx hvC hAx hvA
    exact hbp (hAU.2 a hap b (hC.1 hb) hab)
  have hAC := closed_disjoint_union hAU hC
  have hACcard : (A ∪ C).card = A.card + C.card := Finset.card_union_of_disjoint hDis
  have hACcardR : ((A ∪ C).card : ℝ) = (A.card : ℝ) + C.card := by exact_mod_cast hACcard
  have hACsize : w ≤ ((A ∪ C).card : ℝ) := by
    by_contra! h
    have hh := hAmax (A ∪ C) (hm.mpr ⟨hAC, h⟩)
    have hc : 0 < C.card := Finset.card_pos.mpr ⟨v, hvC⟩
    omega
  exact ⟨A ∪ C, hAC, hACsize, by linarith⟩

private theorem pick_anticomplete_parts {V : Type*} (G : SimpleGraph V) {U : Finset V}
    {d w : ℝ} (hw : 0 < w) (hwd : 2*w ≤ d)
    (hsmall : ∀ A : Finset V, A ⊆ U → internallyConnected G A → (A.card : ℝ) ≤ d)
    (k : ℕ) (hk : (k : ℝ)*d ≤ U.card) :
    ∃ P : Finset (Finset V), P.card = k ∧
      (∀ A ∈ P, A ⊆ U ∧ w ≤ (A.card : ℝ)) ∧
      (P : Set (Finset V)).Pairwise fun A B => Disjoint A B ∧ Anticomplete G A B := by
  classical
  have recPick (k : ℕ) : ∀ R : Finset V, R ⊆ U → (k : ℝ)*d ≤ R.card →
      ∃ P : Finset (Finset V), P.card = k ∧
        (∀ A ∈ P, A ⊆ R ∧ w ≤ (A.card : ℝ)) ∧
        (P : Set (Finset V)).Pairwise fun A B => Disjoint A B ∧ Anticomplete G A B := by
    induction k with
    | zero =>
      intro R _ _
      exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      intro R hRU hk
      have hsize : w ≤ (R.card : ℝ) := by
        have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (show 0 ≤ d by linarith)
        push_cast at hk
        nlinarith
      obtain ⟨A, hA, hAw, hAd⟩ := choose_closed_of_width G R hw hwd hsize
        (fun D hD hDc => hsmall D (hD.trans hRU) hDc)
      have hpart : ((R \ A).card : ℝ) + A.card = R.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hA.1
      have hsz : (k : ℝ)*d ≤ ((R \ A).card : ℝ) := by
        push_cast at hk
        nlinarith
      obtain ⟨P, hPc, hP, hpw⟩ := ih (R \ A) (Finset.sdiff_subset.trans hRU) hsz
      have hDis {B : Finset V} (hB : B ∈ P) : Disjoint A B :=
        Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp ((hP B hB).1 hy)).2 hx
      have hnot : A ∉ P := by
        intro h
        have h := hDis h
        have hA0 : (0 : ℝ) < A.card := hw.trans_le hAw
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (by exact_mod_cast hA0)
        exact Finset.disjoint_left.mp h ha ha
      refine ⟨insert A P, by rw [Finset.card_insert_of_notMem hnot, hPc], ?_, ?_⟩
      · intro B hb
        rcases Finset.mem_insert.mp hb with h | h
        · simpa [h] using And.intro hA.1 hAw
        · exact ⟨(hP B h).1.trans Finset.sdiff_subset, (hP B h).2⟩
      · intro B hB C hC hne
        rcases Finset.mem_insert.mp hB with hBE | hBp <;>
          rcases Finset.mem_insert.mp hC with hCE | hCp
        · exact (hne (hBE.trans hCE.symm)).elim
        · subst B
          exact ⟨hDis hCp, fun a ha c hc => closed_anticomplete hA a ha c ((hP C hCp).1 hc)⟩
        · subst C
          exact ⟨(hDis hBp).symm, fun b hb a ha =>
            reverse_not_adj (closed_anticomplete hA a ha b ((hP B hBp).1 hb))⟩
        · exact hpw hBp hCp hne
  exact recPick k U (Finset.Subset.refl _) hk

/-- Either find a relatively large connected set or pack anticomplete blocks. -/
theorem components_or_anticomplete {V : Type*} (G : SimpleGraph V) (U : Finset V)
    (hU : U.Nonempty) {k : ℕ} (hk : 2 ≤ k) :
    (∃ A : Finset V, A ⊆ U ∧ internallyConnected G A ∧ (U.card : ℝ)/(k : ℝ) ≤ A.card) ∨
    (∃ B : Fin k → Finset V, (∀ i, B i ⊆ U ∧ (U.card : ℝ)/(k : ℝ)^2 ≤ (B i).card) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j) ∧ Anticomplete G (B i) (B j))) := by
  classical
  by_cases he : ∃ A : Finset V, A ⊆ U ∧ internallyConnected G A ∧ (U.card : ℝ)/(k : ℝ) ≤ A.card
  · exact Or.inl he
  apply Or.inr
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let d := (U.card : ℝ)/(k : ℝ)
  let w := (U.card : ℝ)/(k : ℝ)^2
  have wpos : 0 < w := by dsimp [w]; have := Finset.card_pos.mpr hU; positivity
  have hwd : 2*w ≤ d := by
    dsimp [w, d]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hk0]
    nlinarith [mul_le_mul_of_nonneg_right hk2
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) U.card) hk0.le)]
  have hsmall (A : Finset V) (hA : A ⊆ U) (hAc : internallyConnected G A) :
      (A.card : ℝ) ≤ d := le_of_lt (lt_of_not_ge fun ha => he ⟨A, hA, hAc, ha⟩)
  have hEq : (k : ℝ)*d = U.card := by dsimp [d]; field_simp
  obtain ⟨P, hPc, hP, hpw⟩ := pick_anticomplete_parts G wpos hwd hsmall k hEq.le
  let e : (P : Set (Finset V)) ≃ Fin k :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe P).trans hPc)
  refine ⟨fun i => (e.symm i).val, fun i => hP _ (e.symm i).property, ?_⟩
  intro i j hij
  apply hpw (e.symm i).property (e.symm j).property
  exact fun h => hij (e.symm.injective (Subtype.ext h))

end FivePath

namespace FivePath

structure BipartiteComb {V : Type*} (G : SimpleGraph V) (A B : Finset V) (t : ℕ) where
  tooth : Fin t ↪ V
  tooth_mem : ∀ i, tooth i ∈ A
  block : Fin t → Finset V
  block_sub : ∀ i, block i ⊆ B
  disjoint : Pairwise (Function.onFun Disjoint block)
  cross : ∀ i j x, x ∈ block j → (G.Adj (tooth i) x ↔ i = j)

def BipartiteBound {V : Type*} (G : SimpleGraph V) (K : ℝ) : Prop :=
  ∀ (A B : Finset V) (Γ Δ : ℝ), 0 < Γ → 0 ≤ Δ → Disjoint A B →
    (∀ b ∈ B, ∃ a ∈ A, G.Adj a b) →
    (∀ a ∈ A, (neighborsIn G a B).card ≤ Δ) →
    (∃ t > (0 : ℕ), ∃ C : BipartiteComb G A B t,
      ∀ i, Γ / (t : ℝ)^2 ≤ (C.block i).card) ∨ (B.card : ℝ) ≤ K * Real.sqrt (Γ * Δ)

end FivePath

namespace FivePath

theorem neighborsIn_card_sdiff_add {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a : V}
    {P B : Finset V} (h : P ⊆ B) :
    (neighborsIn G a (B \ P)).card + (neighborsIn G a P).card =
      (neighborsIn G a B).card := by
  classical
  have heq : neighborsIn G a (B \ P) = neighborsIn G a B \ neighborsIn G a P := by
    ext b
    simp only [mem_neighborsIn, Finset.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_add_card_eq_card (neighborsIn_mono h)]

private noncomputable def touched {V : Type*} (G : SimpleGraph V) (S P : Finset V) :
    Finset V := by
  classical
  exact S.biUnion (fun x => neighborsIn G x P)

private theorem mem_touched {V : Type*} {G : SimpleGraph V} {S P : Finset V} {b : V} :
    b ∈ touched G S P ↔ b ∈ P ∧ ∃ a ∈ S, G.Adj a b := by
  classical
  simp only [touched, Finset.mem_biUnion, mem_neighborsIn]
  tauto

private theorem touched_card_le {V : Type*} {G : SimpleGraph V} {S P : Finset V} :
    (touched G S P).card ≤ ∑ a ∈ S, (neighborsIn G a P).card := by
  classical
  exact Finset.card_biUnion_le

private structure CombRound {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B : Finset V) (d : ℝ) where
  remainder : Finset V
  remainder_sub : remainder ⊆ B
  remainder_bound : ∀ a ∈ A, (neighborsIn G a remainder).card ≤ d / 2
  teeth : Finset V
  teeth_sub : teeth ⊆ A
  high : ∀ a ∈ teeth, d / 2 ≤ (neighborsIn G a B).card
  part : V → Finset V
  part_sub : ∀ a ∈ teeth, part a ⊆ B \ remainder
  width : ∀ a ∈ teeth, d / 4 ≤ (part a).card
  cross : ∀ a ∈ teeth, ∀ b ∈ teeth, ∀ z ∈ part b, G.Adj a z ↔ a = b
  budget : ((B \ remainder).card : ℝ) ≤
    d * teeth.card + 4 * ∑ a ∈ teeth, ((neighborsIn G a B).card - d / 2 : ℝ)

private theorem comb_round {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    {d : ℝ} (hd : 0 < d) (hcap : ∀ a ∈ A, (neighborsIn G a B).card ≤ d) :
    Nonempty (CombRound G A B d) := by
  classical
  have recRound (n : ℕ) : ∀ U : Finset V, U ⊆ B → U.card = n →
      Nonempty (CombRound G A U d) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hUB hn
      by_cases hex : ∃ a ∈ A, d / 2 < (neighborsIn G a U).card
      swap
      · have hbound : ∀ a ∈ A, (neighborsIn G a U).card ≤ d / 2 := by
          simpa [not_lt] using hex
        exact ⟨⟨U, fun _ h => h, hbound, ∅, by simp, by simp, fun _ => ∅,
          by simp, by simp, by simp, by simp⟩⟩
      obtain ⟨a, haA, ha⟩ := hex
      let P := neighborsIn G a U
      let U' := U \ P
      have hPU : P ⊆ U := fun _ hz => (mem_neighborsIn.mp hz).1
      have hU'U : U' ⊆ U := Finset.sdiff_subset
      have hp : d / 2 < (P.card : ℝ) := ha
      have hPn : 0 < P.card := by
        have hp' : (0 : ℝ) < P.card := by linarith
        exact_mod_cast hp'
      have hparts := Finset.card_sdiff_add_card_eq_card hPU
      change U'.card + P.card = U.card at hparts
      have hlt : U'.card < n := by omega
      obtain ⟨R⟩ := ih U'.card hlt U' (hU'U.trans hUB) rfl
      have hRsub := R.remainder_sub.trans hU'U
      let T := touched G R.teeth P
      let P' := P \ T
      have hTP : T ⊆ P := fun _ hz => (mem_touched.mp hz).1
      have haS : a ∉ R.teeth := by
        intro h
        have ha0 : neighborsIn G a U' = ∅ := by
          ext z
          simp only [U', Finset.mem_sdiff, mem_neighborsIn, Finset.notMem_empty, iff_false]
          intro hz
          exact hz.1.2 (mem_neighborsIn.mpr ⟨hz.1.1, hz.2⟩)
        have hz := R.high a h
        rw [ha0, Finset.card_empty, Nat.cast_zero] at hz
        linarith
      have hsplit : ((U \ R.remainder).card : ℝ) =
          (P.card : ℝ) + ((U' \ R.remainder).card : ℝ) := by
        have h₁ := Finset.card_sdiff_add_card_eq_card hRsub
        have h₂ := Finset.card_sdiff_add_card_eq_card R.remainder_sub
        exact_mod_cast (show (U \ R.remainder).card = P.card + (U' \ R.remainder).card by omega)
      have hcharge (x : V) :
          ((neighborsIn G x U').card - d / 2 : ℝ) + (neighborsIn G x P).card =
          ((neighborsIn G x U).card - d / 2 : ℝ) := by
        have hh : ((neighborsIn G x U').card : ℝ) + (neighborsIn G x P).card =
            (neighborsIn G x U).card := by exact_mod_cast neighborsIn_card_sdiff_add (G := G) (a := x) hPU
        linarith
      have hpay :
          (∑ x ∈ R.teeth, ((neighborsIn G x U').card - d / 2 : ℝ)) + T.card ≤
          ∑ x ∈ R.teeth, ((neighborsIn G x U).card - d / 2 : ℝ) := by
        have hT : (T.card : ℝ) ≤ ∑ x ∈ R.teeth, ((neighborsIn G x P).card : ℝ) := by
          exact_mod_cast touched_card_le (G := G) (S := R.teeth) (P := P)
        calc
          _ ≤ _ + ∑ x ∈ R.teeth, ((neighborsIn G x P).card : ℝ) := add_le_add_right hT _
          _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => hcharge x
      have hhigh : ∀ b ∈ R.teeth, d / 2 ≤ (neighborsIn G b U).card := by
        intro b hb
        exact (R.high b hb).trans (by exact_mod_cast Finset.card_le_card (neighborsIn_mono hU'U))
      have hpartsub : ∀ b ∈ R.teeth, R.part b ⊆ U \ R.remainder := by
        intro b hb z hz
        obtain ⟨hZU, hZR⟩ := Finset.mem_sdiff.mp (R.part_sub b hb hz)
        exact Finset.mem_sdiff.mpr ⟨hU'U hZU, hZR⟩
      by_cases hw : d / 4 ≤ (P'.card : ℝ)
      · let F := fun b => if b = a then P' else R.part b
        refine ⟨⟨R.remainder, hRsub, R.remainder_bound, insert a R.teeth,
          Finset.insert_subset_iff.mpr ⟨haA, R.teeth_sub⟩, ?_, F, ?_, ?_, ?_, ?_⟩⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha.le
          · exact hhigh b hb
        · intro b hb z hz
          rcases Finset.mem_insert.mp hb with rfl | hb
          · have hzP' : z ∈ P' := by simpa [F] using hz
            have hzP : z ∈ P := Finset.sdiff_subset hzP'
            apply Finset.mem_sdiff.mpr ⟨hPU hzP, fun h => ?_⟩
            exact (Finset.mem_sdiff.mp (R.remainder_sub h)).2 hzP
          · have hba : b ≠ a := fun h => haS (h ▸ hb)
            exact hpartsub b hb (by simpa [F, hba] using hz)
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · simpa [F] using hw
          · have hba : b ≠ a := fun h => haS (h ▸ hb)
            simpa [F, hba] using R.width b hb
        · intro b hb c hc z hz
          rcases Finset.mem_insert.mp hb with hba | hb <;>
            rcases Finset.mem_insert.mp hc with hca | hc
          · subst b c
            have hzP' : z ∈ P' := by simpa [F] using hz
            exact iff_of_true (mem_neighborsIn.mp
              (Finset.sdiff_subset hzP' : z ∈ P)).2 rfl
          · subst b
            have hca : c ≠ a := fun h => haS (h ▸ hc)
            have hzR : z ∈ R.part c := by simpa [F, hca] using hz
            have hzU := (Finset.mem_sdiff.mp (R.part_sub c hc hzR)).1
            exact iff_of_false (fun he => (Finset.mem_sdiff.mp hzU).2
              (mem_neighborsIn.mpr ⟨hU'U hzU, he⟩)) hca.symm
          · subst c
            have hba : b ≠ a := fun h => haS (h ▸ hb)
            have hzP : z ∈ P' := by simpa [F] using hz
            exact iff_of_false (fun he => (Finset.mem_sdiff.mp hzP).2
              (mem_touched.mpr ⟨Finset.sdiff_subset hzP, b, hb, he⟩)) hba
          · have hca : c ≠ a := fun h => haS (h ▸ hc)
            apply R.cross b hb c hc z
            simpa [F, hca] using hz
        · rw [hsplit, Finset.card_insert_of_notMem haS, Finset.sum_insert haS]
          push_cast
          have hPcap : (P.card : ℝ) ≤ d := (by
            exact_mod_cast Finset.card_le_card (neighborsIn_mono (G := G) (x := a) hUB) :
              (P.card : ℝ) ≤ (neighborsIn G a B).card).trans (hcap a haA)
          have h0 : (0 : ℝ) ≤ T.card := by positivity
          linarith [R.budget]
      · refine ⟨⟨R.remainder, hRsub, R.remainder_bound, R.teeth, R.teeth_sub,
          hhigh, R.part, hpartsub, R.width, R.cross, ?_⟩⟩
        rw [hsplit]
        have hpt : (P'.card : ℝ) + T.card = P.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card hTP
        have hw' : (P'.card : ℝ) < d / 4 := lt_of_not_ge hw
        have hP : (P.card : ℝ) ≤ 4 * T.card := by linarith
        linarith [R.budget]
  exact recRound B.card B (Finset.Subset.refl _) rfl

private def bipartite_comb_transfer {V : Type*} {G : SimpleGraph V} {A B E : Finset V}
    {t : ℕ} (C : BipartiteComb G A E t) (hEB : E ⊆ B) : BipartiteComb G A B t where
  tooth := C.tooth
  tooth_mem := C.tooth_mem
  block := C.block
  block_sub i := (C.block_sub i).trans hEB
  disjoint := C.disjoint
  cross := C.cross

private noncomputable def CombRound.toComb {V : Type*} [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    {d : ℝ} (R : CombRound G A B d) : BipartiteComb G A B R.teeth.card := by
  classical
  let e : (R.teeth : Set V) ≃ Fin R.teeth.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let a : Fin R.teeth.card ↪ V :=
    ⟨fun i => (e.symm i).val, Subtype.val_injective.comp e.symm.injective⟩
  have ha : ∀ i, a i ∈ R.teeth := fun i => (e.symm i).property
  refine ⟨a, fun i => R.teeth_sub (ha i), fun i => R.part (a i),
    fun i => (R.part_sub _ (ha i)).trans Finset.sdiff_subset, ?_, ?_⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have adj := (R.cross _ (ha i) _ (ha i) _ hx).mpr rfl
    exact hij (a.injective ((R.cross _ (ha i) _ (ha j) _ hy).mp adj))
  · intro i j x hx
    exact (R.cross _ (ha i) _ (ha j) _ hx).trans a.injective.eq_iff

theorem bipartite_bound {V : Type*} (G : SimpleGraph V) : BipartiteBound G 24 := by
  classical
  intro A B Γ Δ hΓ hΔ hAB hcover hcap
  by_cases hcomb : ∃ t > (0 : ℕ), ∃ C : BipartiteComb G A B t,
      ∀ i, Γ / (t : ℝ)^2 ≤ (C.block i).card
  · exact Or.inl hcomb
  apply Or.inr
  have recBound (n : ℕ) : ∀ (U : Finset V) (D : ℝ), U ⊆ B → U.card = n → 0 ≤ D →
      (∀ a ∈ A, (neighborsIn G a U).card ≤ D) →
      (U.card : ℝ) ≤ 24 * Real.sqrt (Γ * D) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U D hUB hn hD hcap
      by_cases hU : U.Nonempty
      swap
      · have hu := Finset.not_nonempty_iff_eq_empty.mp hU
        subst U
        simp
      obtain ⟨b, hbU⟩ := hU
      obtain ⟨a, haA, hab⟩ := hcover b (hUB hbU)
      obtain ⟨x, hxA, hxmax⟩ := Finset.exists_max_image A
        (fun y => (neighborsIn G y U).card) ⟨a, haA⟩
      let d : ℝ := (neighborsIn G x U).card
      have hcap' : ∀ y ∈ A, (neighborsIn G y U).card ≤ d := by
        intro y hy
        dsimp [d]
        exact_mod_cast hxmax y hy
      have hdD : d ≤ D := hcap x hxA
      have hd : 0 < d := by
        dsimp [d]
        exact_mod_cast (Finset.card_pos.mpr ⟨b, mem_neighborsIn.mpr ⟨hbU, hab⟩⟩).trans_le
          (hxmax a haA)
      obtain ⟨R⟩ := comb_round G A U hd hcap'
      have hRproper : R.remainder.card < U.card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨R.remainder_sub, fun eq => ?_⟩
        have he : d ≤ d / 2 := by simpa only [eq] using R.remainder_bound x hxA
        linarith
      have hRbd := ih R.remainder.card (by omega) R.remainder (d/2) (R.remainder_sub.trans hUB)
        rfl (by positivity : 0 ≤ d/2) R.remainder_bound
      let t : ℕ := R.teeth.card
      have hdrop : ((U \ R.remainder).card : ℝ) ≤ 3 * d * t := by
        have hsum : (∑ a ∈ R.teeth, ((neighborsIn G a U).card - d / 2 : ℝ)) ≤
            (t : ℝ) * (d/2) := by
          calc
            _ ≤ ∑ a ∈ R.teeth, (d/2 : ℝ) := Finset.sum_le_sum fun a ha => by
              linarith [hcap' a (R.teeth_sub ha)]
            _ = _ := by simp [t, nsmul_eq_mul]
        dsimp [t] at hsum ⊢
        linarith [R.budget]
      have ht : 0 < t := by
        by_contra! h
        have hte : t = 0 := by omega
        have hcard := Finset.card_sdiff_add_card_eq_card R.remainder_sub
        have hdrop' : ((U \ R.remainder).card : ℝ) ≤ 0 := by simpa [hte] using hdrop
        norm_cast at hdrop'
        omega
      let C := bipartite_comb_transfer R.toComb hUB
      have hw : d/4 < Γ / (t : ℝ)^2 := by
        by_contra! h
        apply hcomb
        refine ⟨t, ht, C, fun i => h.trans (R.width (R.toComb.tooth i) ?_)⟩
        exact (Fintype.equivFinOfCardEq (Fintype.card_coe R.teeth)).symm i |>.property
      have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
      have hsq : (d * (t : ℝ))^2 ≤ (2 * Real.sqrt (Γ * d))^2 := by
        have h := (lt_div_iff₀ (sq_pos_of_pos ht0)).mp hw
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith [mul_lt_mul_of_pos_left h hd]
      have hdt : d * t ≤ 2 * Real.sqrt (Γ * d) := by
        exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
      have hsqrt : Real.sqrt (Γ * (d/2)) ≤ (3/4) * Real.sqrt (Γ*d) := by
        have h := Real.sq_sqrt (show 0 ≤ Γ * (d/2) by positivity)
        have hh := Real.sq_sqrt (show 0 ≤ Γ * d by positivity)
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow, h, hh]
        nlinarith
      have hu : ((U \ R.remainder).card : ℝ) + R.remainder.card = U.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card R.remainder_sub
      calc
        (U.card : ℝ) ≤ 24 * Real.sqrt (Γ * d) := by linarith
        _ ≤ 24 * Real.sqrt (Γ * D) := by gcongr
  exact recBound B.card B Δ (Finset.Subset.refl _) rfl hΔ hcap

end FivePath


namespace FivePath

private theorem comb_length_choice {ℓ : ℕ} {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1/256)
    (hlo : 1 ≤ y * (ℓ : ℝ)) (hhi : x^2 * (ℓ : ℝ) ≤ 2) :
    ∃ k : ℕ, 4 ≤ k ∧ k ≤ ℓ ∧ x * (k : ℝ) ≤ 1 ∧ (ℓ : ℝ) ≤ (k : ℝ)^6 := by
  let z : ℝ := (ℓ : ℝ)^(1/4 : ℝ)
  let k := ⌊z⌋₊
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpow : z^4 = (ℓ : ℝ) := by
    dsimp [z]
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (Nat.cast_nonneg ℓ)]
    norm_num
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hzk : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hklo' : (256 : ℝ) ≤ ℓ := by
    nlinarith [mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg (α := ℝ) ℓ)]
  have h4z : (4 : ℝ) ≤ z := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hz (by decide : 4 ≠ 0)
    norm_num [hpow] at hh
    exact (not_lt_of_ge (by exact_mod_cast hklo' : 256 ≤ ℓ)) hh
  have hlo4 : 4 ≤ k := (Nat.le_floor_iff' (by decide : (4:ℕ) ≠ 0)).mpr h4z
  have hlo4' : (4 : ℝ) ≤ k := by exact_mod_cast hlo4
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hkpow : (k : ℝ)^4 ≤ ℓ := (pow_le_pow_left₀ hk0 hkz 4).trans_eq hpow
  have hkℓ : k ≤ ℓ := by
    have hh : (k : ℝ) ≤ ℓ := (by
      have ht := pow_le_pow_right₀ hk1 (show 1 ≤ 4 by decide)
      simpa only [pow_one] using ht : (k : ℝ) ≤ (k : ℝ)^4).trans hkpow
    exact_mod_cast hh
  have hxsq : 2*x^2 ≤ 1 := by
    have hh : x ≤ 1/2 := by linarith
    have hh' := pow_le_pow_left₀ hx.le hh 2
    norm_num at hh'
    linarith
  have hxk : x * (k : ℝ) ≤ 1 := by
    have ht : (x * (k : ℝ))^4 ≤ 1 := calc
      _ = x^2 * (x^2 * (k : ℝ)^4) := by ring
      _ ≤ x^2 * (x^2 * (ℓ : ℝ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hkpow (sq_nonneg x)) (sq_nonneg x)
      _ ≤ x^2*2 := mul_le_mul_of_nonneg_left hhi (sq_nonneg x)
      _ ≤ _ := by linarith
    by_contra! h
    have hh := pow_lt_pow_left₀ h (by norm_num : (0:ℝ) ≤ 1) (by decide : 4 ≠ 0)
    norm_num at hh
    exact hh.not_ge ht
  have hell : (ℓ : ℝ) ≤ (k : ℝ)^6 := calc
    _ = z^4 := hpow.symm
    _ ≤ ((k : ℝ)+1)^4 := pow_le_pow_left₀ hz hzk.le 4
    _ ≤ (2*(k : ℝ))^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    _ = 16*(k : ℝ)^4 := by ring
    _ ≤ (k : ℝ)^2*(k : ℝ)^4 := mul_le_mul_of_nonneg_right
      (by have ht := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hlo4' 2; norm_num at ht; exact ht)
      (by positivity)
    _ = _ := by ring
  exact ⟨k, hlo4, hkℓ, hxk, hell⟩

structure PureBlockade {V : Type*} (G : SimpleGraph V) (U : Finset V) (k : ℕ) where
  part : Fin k → Finset V
  part_sub : ∀ i, part i ⊆ U
  disjoint : Pairwise (Function.onFun Disjoint part)
  pure : ∀ i j, i ≠ j → Uniform G (part i) (part j)

private theorem pure_from_neighborhood_comb {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {k : ℕ} (C : NeighborhoodComb G k) (hfree : HouseFree G) (hk : 2 ≤ k)
    (hsub : ∀ i, C.block i ⊆ U) {w : ℝ} (hw : 0 < w) (hwC : ∀ i, w ≤ (C.block i).card) :
    ∃ B : PureBlockade G U k, ∀ i, w/(k : ℝ)^2 ≤ (B.part i).card := by
  classical
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hpart (i : Fin k) := components_or_anticomplete Gᶜ (C.block i)
    (Finset.card_pos.mp (by exact_mod_cast hw.trans_le (hwC i))) hk
  by_cases hconn : ∀ i, ∃ A : Finset V, A ⊆ C.block i ∧ internallyConnected Gᶜ A ∧
    ((C.block i).card : ℝ)/(k : ℝ) ≤ A.card
  · choose A hA hcon hsize using hconn
    let D : NeighborhoodComb G k := {
      root := C.root,
      tooth := C.tooth,
      block := A,
      disjoint := fun i j hij => Disjoint.mono (hA i) (hA j) (C.disjoint hij),
      tooth_outside := fun i j h => C.tooth_outside i j (hA j h),
      root_ne_tooth := C.root_ne_tooth,
      root_miss := C.root_miss,
      root_sees := fun i u hu => C.root_sees i u (hA i hu),
      cross := fun i j u hu => C.cross i j u (hA j hu) }
    have hcomp : (k : ℝ) ≤ (k : ℝ)^2 := by
      have h := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ k by linarith) hk0.le
      simpa [sq] using h
    refine ⟨⟨A, fun i => (hA i).trans (hsub i), D.disjoint, fun i j hij =>
      D.pure hfree hcon hij⟩, fun i => ?_⟩
    exact (div_le_div_of_nonneg_left hw.le hk0 hcomp).trans
      ((div_le_div_of_nonneg_right (hwC i) hk0.le).trans (hsize i))
  · push Not at hconn
    obtain ⟨i, hn⟩ := hconn
    rcases hpart i with ⟨A, hA, hac, hasize⟩ | ⟨B, hB, hpw⟩
    · exact ((hn A hA hac).not_ge hasize).elim
    · refine ⟨⟨B, fun j => (hB j).1.trans (hsub i), fun j l hjl => (hpw j l hjl).1,
        fun j l hjl => Or.inl fun p hp q hq => ?_⟩, fun j =>
        (div_le_div_of_nonneg_right (hwC i) (by positivity)).trans (hB j).2⟩
      by_contra hpq
      have hpneq : p ≠ q := fun he => Finset.disjoint_left.mp (hpw j l hjl).1 hp (he ▸ hq)
      exact (hpw j l hjl).2 p hp q hq ((G.compl_adj _ _).mpr ⟨hpneq, hpq⟩)

theorem house_sparse_trichotomy {V : Type*} {G : SimpleGraph V} {U : Finset V}
    (hfree : HouseFree G) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1/256)
    (hsize : 1 ≤ y^4 * (U.card : ℝ)) (hdeg : DegreeBound G U (y^3)) :
    DegreeBound G U (2*y^4) ∨ SparsePair G U x y ∨
      ∃ k : ℕ, 4 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ 1 ≤ y*(k : ℝ)^6 ∧
        ∃ P : PureBlockade G U k, ∀ i, (U.card : ℝ)/(k : ℝ)^38 ≤ (P.part i).card := by
  classical
  by_cases hsmall : DegreeBound G U (2*y^4)
  · exact Or.inl hsmall
  apply Or.inr
  rcases sparse_pair_or_comb_input hx hxy hy hsize hdeg hsmall with
    hp | ⟨v, hv, A, B, hAU, hB, hAB, hAv, hAcard, hBcard, hdegA, hdegB⟩
  · exact Or.inl hp
  apply Or.inr
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := by linarith
  have hW : (0 : ℝ) < U.card := by
    by_contra! h
    have hnon : 0 ≤ y^4 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hnon h]
  have hB0 : (0 : ℝ) < B.card := (by positivity : 0 < y^4 * (U.card : ℝ)).trans_le hBcard
  have hA0 : (0 : ℝ) < A.card := (mul_pos (by linarith) hW).trans_le hAcard
  obtain ⟨S, hSA, hSc, hcover⟩ := small_cover G A B
    (Finset.card_pos.mp (by exact_mod_cast hA0)) (x := x^2)
    (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left (show x ≤ 1 by linarith) hx.le]) hdegB
  let T := covered G S B
  have hTB : T ⊆ B := Finset.filter_subset _ _
  have hcT : ∀ b ∈ T, ∃ a ∈ S, G.Adj a b := fun b hb => (Finset.mem_filter.mp hb).2
  have hSdeg : ∀ a ∈ S, (neighborsIn G a T).card ≤ y^2*(B.card : ℝ) := by
    intro a ha
    have hm : ((neighborsIn G a T).card : ℝ) ≤ (neighborsIn G a B).card := by
      exact_mod_cast Finset.card_le_card (neighborsIn_mono hTB)
    exact hm.trans (hdegA a (hSA ha))
  have hTpos : (0 : ℝ) < T.card := (by positivity : 0 < (B.card : ℝ)/2).trans_le hcover
  rcases bipartite_bound G S T B.card (y^2*(B.card : ℝ)) hB0 (by positivity)
    (Disjoint.mono hSA hTB hAB) hcT hSdeg with ⟨l, hl, C, hCw⟩ | hbad
  swap
  · exfalso
    have hsqrt : Real.sqrt ((B.card : ℝ)*(y^2*(B.card : ℝ))) = y*B.card := by
      rw [show (B.card : ℝ)*(y^2*(B.card : ℝ)) = (y*B.card)^2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [hsqrt] at hbad
    have hh := mul_le_mul_of_nonneg_right hy hB0.le
    change (B.card : ℝ)/2 ≤ T.card at hcover
    linarith
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  have hllo : 1 ≤ y*(l : ℝ) := by
    let i : Fin l := ⟨0, hl⟩
    have hblock : C.block i ⊆ neighborsIn G (C.tooth i) B := by
      intro b hb
      exact mem_neighborsIn.mpr ⟨hTB (C.block_sub i hb), (C.cross i i b hb).mpr rfl⟩
    have hbc : ((C.block i).card : ℝ) ≤ y^2*(B.card : ℝ) := by
      exact (by exact_mod_cast Finset.card_le_card hblock :
        ((C.block i).card : ℝ) ≤ (neighborsIn G (C.tooth i) B).card).trans
        (hdegA _ (hSA (C.tooth_mem i)))
    have hh := (div_le_iff₀ (sq_pos_of_pos hl0)).mp ((hCw i).trans hbc)
    have hsq : (1 : ℝ)^2 ≤ (y*(l : ℝ))^2 := by
      apply le_of_mul_le_mul_left ?_ hB0
      nlinarith [hh]
    exact (sq_le_sq₀ (by norm_num) (by positivity)).mp hsq
  have hcnt : l ≤ S.card := by
    have h := Fintype.card_le_of_injective (fun i => (⟨C.tooth i, C.tooth_mem i⟩ : ↥S))
      (fun i j eq => C.tooth.injective (congrArg Subtype.val eq))
    simpa only [Fintype.card_fin, Fintype.card_coe] using h
  have hhi : x^2*(l : ℝ) ≤ 2 := by
    have hh : (l : ℝ) ≤ (⌈1/x^2⌉₊ : ℝ) := by exact_mod_cast hcnt.trans hSc
    have hh' := Nat.ceil_lt_add_one (show 0 ≤ 1/x^2 by positivity)
    have hs := mul_le_mul_of_nonneg_left (hh.trans hh'.le) (sq_nonneg x)
    have hxe : x^2 * (1/x^2 + 1) = 1 + x^2 := by field_simp
    have he : x^2 ≤ (1 : ℝ) := (pow_le_pow_left₀ hx.le (show x ≤ 1 by linarith) 2).trans_eq
      (by norm_num)
    rw [hxe] at hs
    linarith
  obtain ⟨k, hk, hkl, hxk, hlk⟩ := comb_length_choice hx hxy hy hllo hhi
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hyr : 1 ≤ y*(k : ℝ)^6 := hllo.trans (mul_le_mul_of_nonneg_left hlk hy0.le)
  let f : Fin k ↪ Fin l :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hkl⟩, fun _ _ h => Fin.ext (congrArg (fun j : Fin l => j.val) h)⟩
  let Q : NeighborhoodComb G k := {
    root := v,
    tooth := fun i => C.tooth (f i),
    block := fun i => C.block (f i),
    disjoint := fun _ _ hij => C.disjoint (fun eq => hij (f.injective eq)),
    tooth_outside := fun i j hu => Finset.disjoint_left.mp hAB (hSA (C.tooth_mem (f i)))
      (hTB (C.block_sub (f j) hu)),
    root_ne_tooth := fun i => (hAv _ (hSA (C.tooth_mem (f i)))).1,
    root_miss := fun i => (hAv _ (hSA (C.tooth_mem (f i)))).2,
    root_sees := fun i u hu => (mem_neighborsIn.mp (hB (hTB (C.block_sub (f i) hu)))).2,
    cross := fun i j u hu => (C.cross (f i) (f j) u hu).trans f.injective.eq_iff }
  have hBSub : B ⊆ U := fun _ hb => (mem_neighborsIn.mp (hB hb)).1
  have hQsub (i : Fin k) : Q.block i ⊆ U := ((C.block_sub (f i)).trans hTB).trans hBSub
  have hwidth (i : Fin k) : (U.card : ℝ)/(k : ℝ)^36 ≤ (Q.block i).card := by
    have hyinv : 1/(k : ℝ)^6 ≤ y := (div_le_iff₀ (by positivity)).mpr hyr
    have hp := pow_le_pow_left₀ (show 0 ≤ 1/(k : ℝ)^6 by positivity) hyinv 4
    rw [div_pow, one_pow, ← pow_mul] at hp
    norm_num at hp
    have hBwide : (U.card : ℝ)/(k : ℝ)^24 ≤ B.card := by
      rw [← one_div_mul_eq_div]
      have hp' : 1/(k : ℝ)^24 ≤ y^4 := by simpa [one_div] using hp
      exact (mul_le_mul_of_nonneg_right hp' hW.le).trans hBcard
    have hlpower : (l : ℝ)^2 ≤ (k : ℝ)^12 := by
      have hh := pow_le_pow_left₀ hl0.le hlk 2
      rw [← pow_mul] at hh
      exact hh
    calc
      _ = ((U.card : ℝ)/(k : ℝ)^24) / (k : ℝ)^12 := by
        rw [div_div, ← pow_add]
      _ ≤ (B.card : ℝ)/(l : ℝ)^2 :=
        div_le_div₀ (by positivity) hBwide (by positivity) hlpower
      _ ≤ _ := hCw (f i)
  obtain ⟨D, hDw⟩ := pure_from_neighborhood_comb Q hfree (by omega) hQsub
    (by positivity : 0 < (U.card : ℝ)/(k : ℝ)^36) hwidth
  refine ⟨k, hk, hxk, hyr, D, fun i => ?_⟩
  simpa only [div_div, ← pow_add] using hDw i

end FivePath

namespace FivePath

structure OrderedBlockade {V : Type*} (U : Finset V) (P : Finset V → Finset V → Prop)
    (m : ℕ) where
  part : Fin m → Finset V
  sub : ∀ i, part i ⊆ U
  disjoint : Pairwise (Function.onFun Disjoint part)
  ordered : ∀ i j, i < j → P (part i) (part j)

/-- Repeatedly split a large remainder, unless an alternate conclusion occurs. -/
theorem grow_blockade {V : Type*} {U : Finset V} {P : Finset V → Finset V → Prop}
    {stop : Prop} {m : ℕ} {loss width : ℝ} (hloss : 0 ≤ loss)
    (hP : ∀ A B C, C ⊆ B → P A B → P A C)
    (step : ∀ R : Finset V, R ⊆ U → (U.card : ℝ) - (m : ℝ)*loss ≤ R.card →
      stop ∨ ∃ X Y : Finset V, X ⊆ R ∧ Y ⊆ R ∧ Disjoint X Y ∧
        width ≤ (X.card : ℝ) ∧ (R.card : ℝ) - loss ≤ (Y.card : ℝ) ∧ P X Y) :
    stop ∨ ∃ A : OrderedBlockade U P m, ∀ i, width ≤ (A.part i).card := by
  classical
  have recGrow (j : ℕ) (hj : j ≤ m) :
      stop ∨ ∃ (A : OrderedBlockade U P j) (R : Finset V), R ⊆ U ∧
        (U.card : ℝ)-(j : ℝ)*loss ≤ R.card ∧
        ∀ i, width ≤ (A.part i).card ∧ Disjoint (A.part i) R ∧ P (A.part i) R := by
    induction j with
    | zero =>
      refine Or.inr ⟨⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
        U, Finset.Subset.refl _, by simp, fun i => i.elim0⟩
    | succ j ih =>
      rcases ih (by omega) with hs | ⟨A, R, hRU, hR, hA⟩
      · exact Or.inl hs
      have hjR : (j : ℝ) ≤ m := by exact_mod_cast (show j ≤ m by omega)
      have hb : (U.card : ℝ)-(m : ℝ)*loss ≤ R.card := by
        linarith [mul_le_mul_of_nonneg_right hjR hloss]
      rcases step R hRU hb with hs | ⟨X, Y, hX, hY, hd, hw, hYsize, hXY⟩
      · exact Or.inl hs
      let f : Fin (j+1) → Finset V := Fin.snoc A.part X
      have hf : ∀ i, f i ⊆ U := by
        intro i
        cases i using Fin.lastCases with
        | last => simpa [f] using hX.trans hRU
        | cast i => simpa [f] using A.sub i
      have hDis : Pairwise (Function.onFun Disjoint f) := by
        intro i k hne
        change Disjoint (f i) (f k)
        cases i using Fin.lastCases with
        | last =>
          cases k using Fin.lastCases with
          | last => exact (hne rfl).elim
          | cast k =>
            simpa [f] using (Disjoint.mono_right hX (hA k).2.1).symm
        | cast i =>
          cases k using Fin.lastCases with
          | last =>
            simpa [f] using Disjoint.mono_right hX (hA i).2.1
          | cast k =>
            have hc : i ≠ k := fun h => hne (congrArg Fin.castSucc h)
            simpa [f] using (A.disjoint hc : Disjoint (A.part i) (A.part k))
      have hOrd : ∀ i k, i < k → P (f i) (f k) := by
        intro i k hi
        cases i using Fin.lastCases with
        | last => exact ((not_lt_of_ge (Fin.le_last k)) hi).elim
        | cast i =>
          cases k using Fin.lastCases with
          | last => simpa [f] using hP _ _ _ hX (hA i).2.2
          | cast k =>
            exact by simpa [f] using A.ordered i k (Fin.castSucc_lt_castSucc_iff.mp hi)
      refine Or.inr ⟨⟨f, hf, hDis, hOrd⟩, Y, hY.trans hRU, ?_, ?_⟩
      · push_cast
        linarith
      · intro i
        cases i using Fin.lastCases with
        | last => simpa [f] using And.intro hw (And.intro hd hXY)
        | cast i =>
          simp only [f, Fin.snoc_castSucc]
          exact ⟨(hA i).1, Disjoint.mono_right hY (hA i).2.1, hP _ _ _ hY (hA i).2.2⟩
  rcases recGrow m le_rfl with hs | ⟨A, R, _, _, hA⟩
  · exact Or.inl hs
  · exact Or.inr ⟨A, fun i => (hA i).1⟩

def OneWaySparse {V : Type*} (G : SimpleGraph V) (x : ℝ) (A B : Finset V) : Prop :=
  ∀ b ∈ B, (neighborsIn G b A).card ≤ x * (A.card : ℝ)

end FivePath

namespace FivePath

/-- Minimize a continuous sparsity scale over finitely many induced vertex sets. -/
theorem minimum_degree_scale {V : Type*} (G : SimpleGraph V) (U : Finset V)
    {lo hi : ℝ} (hli : lo ≤ hi) (T H : ℝ → ℝ) (hT : Continuous T) (hH : Continuous H)
    (hT0 : T hi ≤ 1) (h0 : DegreeBound G U (H hi)) :
    ∃ y ∈ Set.Icc lo hi, ∃ A : Finset V, A ⊆ U ∧
      T y * (U.card : ℝ) ≤ A.card ∧ DegreeBound G A (H y) ∧
      ∀ z ∈ Set.Icc lo hi, ∀ B : Finset V, B ⊆ U →
        T z * (U.card : ℝ) ≤ B.card → DegreeBound G B (H z) → y ≤ z := by
  classical
  let B (A : Finset V) := {y : ℝ | T y * (U.card : ℝ) ≤ A.card ∧ DegreeBound G A (H y)}
  let S := Set.Icc lo hi ∩ ⋃ A ∈ U.powerset, B A
  have hmem {y : ℝ} :
      y ∈ S ↔ y ∈ Set.Icc lo hi ∧
        ∃ A : Finset V, A ⊆ U ∧ T y * (U.card : ℝ) ≤ A.card ∧ DegreeBound G A (H y) := by
    simp [S, B, Finset.mem_powerset]
    aesop
  have hS : IsClosed S := by
    apply isClosed_Icc.inter (isClosed_biUnion_finset fun A _ => ?_)
    have hdeg : IsClosed {y : ℝ | DegreeBound G A (H y)} := by
      have he : {y : ℝ | DegreeBound G A (H y)} =
          ⋂ v : V, ⋂ (_ : v ∈ A),
            {y : ℝ | ((neighborsIn G v A).card : ℝ) ≤ H y * (A.card : ℝ)} := by
        ext y
        simp [DegreeBound]
      rw [he]
      exact isClosed_iInter fun v => isClosed_iInter fun _ =>
        isClosed_le continuous_const (hH.mul continuous_const)
    exact (isClosed_le (hT.mul continuous_const) continuous_const).inter hdeg
  have hhi : hi ∈ S := hmem.mpr ⟨⟨hli, le_rfl⟩, U, Finset.Subset.refl _, by
    simpa using mul_le_mul_of_nonneg_right hT0 (Nat.cast_nonneg (α := ℝ) U.card), h0⟩
  have hb : BddBelow S := ⟨lo, fun y hy => (hmem.mp hy).1.1⟩
  obtain ⟨hy, A, hAU, hAc, hdegree⟩ := hmem.mp (hS.csInf_mem ⟨hi, hhi⟩ hb)
  exact ⟨sInf S, hy, A, hAU, hAc, hdegree, fun z hz X hX hXc hd =>
    csInf_le hb (hmem.mpr ⟨hz, X, hX, hXc, hd⟩)⟩

theorem equal_parts {V : Type*} (U : Finset V) {k m : ℕ} (hm : 0 < m)
    (hU : k*m ≤ U.card) :
    ∃ A : Fin k → Finset V, (∀ i, A i ⊆ U ∧ (A i).card = m) ∧
      Pairwise (Function.onFun Disjoint A) := by
  classical
  let e : (U : Set V) ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let block (i : Fin k) (j : Fin m) : Fin U.card :=
    ⟨(i : ℕ) * m + j, by
      calc
        (i : ℕ) * m + j < ((i : ℕ)+1) * m := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left j.isLt _
        _ ≤ k*m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := hU⟩
  have hinj (i j : Fin k) (u v : Fin m) (h : block i u = block j v) : i = j ∧ u = v := by
    have hh : (i : ℕ)*m + u = (j : ℕ)*m + v := congrArg Fin.val h
    have hi : i = j := by
      apply Fin.ext
      have hx (i : Fin k) (v : Fin m) : (((i : ℕ)*m + v) / m) = i := by
        rw [Nat.mul_comm (i : ℕ) m, Nat.mul_add_div hm, Nat.div_eq_of_lt v.isLt, add_zero]
      rw [← hx i u, ← hx j v, hh]
    subst j
    exact ⟨rfl, Fin.ext (by omega)⟩
  let part (i : Fin k) : Fin m ↪ V :=
    ⟨fun j => e.symm (block i j), fun u v h => (hinj i i u v
      (e.symm.injective (Subtype.ext h))).2⟩
  let A (i : Fin k) : Finset V := Finset.univ.map (part i)
  refine ⟨A, fun i => ⟨?_, by simp [A]⟩, ?_⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e.symm (block i j)).property
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨v, _, he⟩ := Finset.mem_map.mp hxj
    exact hij (hinj i j u v (e.symm.injective (Subtype.ext he.symm))).1

end FivePath

namespace FivePath

structure DensityBlockade {V : Type*} (G : SimpleGraph V) (U : Finset V) (k : ℕ) (x : ℝ) where
  part : Fin k → Finset V
  sub : ∀ i, part i ⊆ U
  disjoint : Pairwise (Function.onFun Disjoint part)
  restricted : ∀ i j, i ≠ j →
    (∀ a ∈ part i, ∀ b ∈ part j, G.Adj a b) ∨
      edgeCountBetween G (part i) (part j) ≤ x * (part i).card * (part j).card

private def PureBlockade.toDensity {V : Type*} {G : SimpleGraph V} {U : Finset V} {k : ℕ}
    (B : PureBlockade G U k) {x : ℝ} (hx : 0 ≤ x) : DensityBlockade G U k x where
  part := B.part
  sub := B.part_sub
  disjoint := B.disjoint
  restricted i j hij := by
    rcases B.pure i j hij with h | h
    · exact Or.inl h
    · apply Or.inr
      have hz := edgeCount_degree_cap G (B.part i) (B.part j) (t := 0) fun a ha => by
        have he : neighborsIn G a (B.part j) = ∅ := by
          ext b
          simp only [mem_neighborsIn, Finset.notMem_empty, iff_false]
          rintro ⟨hb, hadj⟩
          exact h a ha b hb hadj
        simp [he]
      exact (by simpa using hz : edgeCountBetween G (B.part i) (B.part j) ≤ 0).trans (by positivity)

private def OrderedBlockade.toDensity {V : Type*} {G : SimpleGraph V} {U : Finset V} {k : ℕ}
    {x : ℝ} (C : OrderedBlockade U (OneWaySparse G x) k) : DensityBlockade G U k x where
  part := C.part
  sub := C.sub
  disjoint := C.disjoint
  restricted i j hij := by
    classical
    apply Or.inr
    rcases lt_or_gt_of_ne hij with h | h
    · rw [edgeCount_comm]
      have hcount := edgeCount_le_mul G (C.part j) (C.part i) x (C.ordered i j h)
      convert hcount using 1
      ring
    · exact edgeCount_le_mul G (C.part i) (C.part j) x (C.ordered j i h)

private theorem first_growth {V : Type*} {G : SimpleGraph V} {U : Finset V}
    (hfree : HouseFree G) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1/256) (hU : 2 ≤ y^4 * (U.card : ℝ))
    (hdeg : DegreeBound G U (y^3/2)) :
    (∃ A : Finset V, A ⊆ U ∧ (U.card : ℝ)/2 ≤ A.card ∧ DegreeBound G A ((y/2)^3/2)) ∨
    (∃ k : ℕ, 2 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ 1 ≤ 16*y*(k : ℝ) ∧
      ∃ P : OrderedBlockade U (OneWaySparse G x) k,
        (∀ i, y^5*(U.card : ℝ) ≤ (P.part i).card)) ∨
    ∃ k : ℕ, 4 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ 1 ≤ y*(k : ℝ)^6 ∧
      ∃ P : PureBlockade G U k, ∀ i, (U.card : ℝ)/(k : ℝ)^39 ≤ (P.part i).card := by
  classical
  let W : ℝ := U.card
  let m := ⌊1/(8*y)⌋₊
  have hy0 : 0 < y := hx.trans_le hxy
  have hmlo0 : (2 : ℝ) ≤ 1/(8*y) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hmlo : 2 ≤ m := (Nat.le_floor_iff' (by decide : (2:ℕ) ≠ 0)).mpr hmlo0
  have hmup0 : (m : ℝ) ≤ 1/(8*y) := Nat.floor_le (by positivity)
  have hmup : (m : ℝ)*(8*y) ≤ 1 := (le_div_iff₀ (by positivity)).mp hmup0
  have hmfloor : 1/(8*y) < (m : ℝ)+1 := Nat.lt_floor_add_one _
  have hmlo1 : 1 ≤ 16*y*(m : ℝ) := by
    have he := (div_lt_iff₀ (show 0 < 8*y by positivity)).mp hmfloor
    linarith
  have hmup1 : x*(m : ℝ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg (α := ℝ) m)
    have h0 : 0 ≤ y*(m : ℝ) := by positivity
    linarith
  let T : Prop := ∃ A : Finset V, A ⊆ U ∧ W/2 ≤ A.card ∧ DegreeBound G A ((y/2)^3/2)
  let S : Prop := ∃ k : ℕ, 4 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ 1 ≤ y*(k : ℝ)^6 ∧
    ∃ P : PureBlockade G U k, ∀ i, W/(k : ℝ)^39 ≤ (P.part i).card
  have hW : 0 < W := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ y^4 by positivity) h]
  have hGrow := grow_blockade (U := U) (P := OneWaySparse G x) (stop := T ∨ S)
    (m := m) (loss := 4*y*W) (width := y^5*W) (by positivity)
    (fun _ _ _ hC hP b hb => hP b (hC hb))
  have hs := hGrow fun R hRU hR => by
    have hHalf : W/2 ≤ (R.card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hmup hW.le]
    have hsize : 1 ≤ y^4*(R.card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hHalf (pow_nonneg hy0.le 4)]
    have hd : DegreeBound G R (y^3) := by
      intro v hv
      have hm : ((neighborsIn G v R).card : ℝ) ≤ (neighborsIn G v U).card := by
        exact_mod_cast Finset.card_le_card (neighborsIn_mono hRU)
      have huh := hdeg v (hRU hv)
      nlinarith [mul_le_mul_of_nonneg_left hHalf (pow_nonneg hy0.le 3)]
    rcases house_sparse_trichotomy hfree hx hxy hy hsize hd with hsmall | hp | ⟨k, hk, hX, hY, P, hP⟩
    · apply Or.inl
      apply Or.inl
      refine ⟨R, hRU, hHalf, fun v hv => (hsmall v hv).trans ?_⟩
      have he : 2*y^4 ≤ (y/2)^3/2 := by
        nlinarith [mul_le_mul_of_nonneg_right (show 2*y ≤ 1/16 by linarith) (pow_nonneg hy0.le 3)]
      exact mul_le_mul_of_nonneg_right he (by positivity)
    · obtain ⟨X, Y, hX, hY, hXY, hXc, hYc, hXYdeg⟩ := hp
      apply Or.inr
      refine ⟨X, Y, hX, hY, hXY, ?_, ?_, hXYdeg⟩
      · have hh : y^5*W ≤ y^4*(W/2) := by
          nlinarith [mul_le_mul_of_nonneg_right (show y ≤ 1/2 by linarith)
            (mul_nonneg (pow_nonneg hy0.le 4) hW.le)]
        exact hh.trans ((mul_le_mul_of_nonneg_left hHalf (by positivity)).trans hXc)
      · have hRW : (R.card : ℝ) ≤ W := by
          dsimp [W]
          exact_mod_cast Finset.card_le_card hRU
        nlinarith [mul_le_mul_of_nonneg_left hRW (show 0 ≤ 4*y by positivity)]
    · apply Or.inl
      apply Or.inr
      let B : PureBlockade G U k := ⟨P.part, fun i => (P.part_sub i).trans hRU, P.disjoint, P.pure⟩
      refine ⟨k, hk, hX, hY, B, fun i => ?_⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      have hden : (2 : ℝ)*(k : ℝ)^38 ≤ (k : ℝ)^39 := by
        rw [show (39:ℕ) = 38+1 from rfl, pow_succ (k : ℝ) 38]
        simpa only [mul_comm ((k : ℝ)^38) (k : ℝ)] using
          mul_le_mul_of_nonneg_right hk2 (pow_nonneg hk0.le 38)
      calc
        _ ≤ W/(2*(k : ℝ)^38) := div_le_div_of_nonneg_left hW.le (by positivity) hden
        _ = (W/2)/(k : ℝ)^38 := by rw [div_div]
        _ ≤ ((R.card : ℝ)/(k : ℝ)^38) := div_le_div_of_nonneg_right hHalf (by positivity)
        _ ≤ (B.part i).card := hP i
  rcases hs with (hT | hS) | ⟨P, hP⟩
  · exact Or.inl hT
  · exact Or.inr (Or.inr hS)
  · exact Or.inr (Or.inl ⟨m, hmlo, hmup1, hmlo1, P, hP⟩)

private theorem rescale_width {k a b : ℕ} {y W A : ℝ} (hk : (0 : ℝ) < k) (hW : 0 ≤ W)
    (hA : y*W ≤ A) (hy : 1 ≤ y*(k : ℝ)^a) :
    W/(k : ℝ)^(a+b) ≤ A/(k : ℝ)^b := by
  have h : 1/(k : ℝ)^a ≤ y := (div_le_iff₀ (by positivity)).mpr hy
  rw [pow_add, ← div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← one_div_mul_eq_div]
  exact (mul_le_mul_of_nonneg_right h hW).trans hA

private theorem first_exit {V : Type*} {G : SimpleGraph V} {U A : Finset V} {x y : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1/256) (hlo : x/2 ≤ y) (hhi : y ≤ x)
    (hsize : 2 ≤ x^5 * (U.card : ℝ))
    (hAU : A ⊆ U) (hA : y*(U.card : ℝ) ≤ A.card) (hdeg : DegreeBound G A (y^3/2)) :
    ∃ k : ℕ, 2 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ ∃ B : DensityBlockade G U k x,
      ∀ i, (U.card : ℝ)/(k : ℝ)^45 ≤ (B.part i).card := by
  classical
  let k := ⌊1/(2*x)⌋₊
  have hx2 : x ≤ 1 := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hlo
  have hk2 : 2 ≤ k := (Nat.le_floor_iff' (by decide : (2:ℕ) ≠ 0)).mpr
    ((le_div_iff₀ (show 0 < 2*x by positivity)).mpr (by norm_num; linarith))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < k := by linarith
  have hKup : (k : ℝ)*(2*x) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hKlow : 1 ≤ 4*x*(k : ℝ) := by
    have h := (div_lt_iff₀ (show 0 < 2*x by positivity)).mp (Nat.lt_floor_add_one (1/(2*x)))
    change 1 < ((k : ℝ)+1)*(2*x) at h
    linarith
  have hAlo : (x/2)*(U.card : ℝ) ≤ A.card :=
    (mul_le_mul_of_nonneg_right hlo (by positivity)).trans hA
  have hUle : 1 ≤ x*(A.card : ℝ) := by
    have hpow : x^5 ≤ x^2 := pow_le_pow_of_le_one hx.le hx2 (by decide)
    nlinarith [mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg (α := ℝ) U.card),
      mul_le_mul_of_nonneg_left hAlo hx.le]
  have h2ka : 2*k ≤ A.card := by
    have h : (2 : ℝ)*k ≤ A.card := by
      apply (mul_le_mul_iff_right₀ hx).mp
      nlinarith
    exact_mod_cast h
  let m := A.card / k
  have hkN : 0 < k := by omega
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.div_pos (by omega) hkN
  have hmA : k*m ≤ A.card := Nat.mul_div_le _ _
  obtain ⟨B, hB, hdis⟩ := equal_parts A hm hmA
  have hmul : (A.card : ℝ) ≤ 2*(k : ℝ)*m := by
    have hmod : ((A.card % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt _ hkN
    have hh : ((A.card % k : ℕ) : ℝ) + (k : ℝ)*m = A.card := by
      dsimp [m]
      exact_mod_cast Nat.mod_add_div A.card k
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    nlinarith [mul_le_mul_of_nonneg_left hmR hk0.le]
  have hmX : x*(A.card : ℝ) ≤ m := by
    have ht := mul_le_mul_of_nonneg_left hmul hx.le
    have hh := mul_le_mul_of_nonneg_right hKup (Nat.cast_nonneg (α := ℝ) m)
    nlinarith
  have hxs : y^3/2 ≤ x^2 := by
    have hh := pow_le_pow_left₀ hy0.le hhi 3
    have hp : x^3 ≤ x^2 := pow_le_pow_of_le_one hx.le hx2 (by decide)
    nlinarith
  have hwidth : (U.card : ℝ)/(k : ℝ)^45 ≤ (m : ℝ) := by
    have hxB : 1/(k : ℝ)^3 ≤ x := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hPow : (4 : ℝ) ≤ (k : ℝ)^2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hkR 2
        norm_num at h
        exact h
      rw [show (3:ℕ)=2+1 from rfl, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hPow (show 0 ≤ x*(k : ℝ) by positivity)]
    have hk1 : (1 : ℝ) ≤ k := by linarith
    have hp : 1 ≤ x*(k : ℝ)^3 := (div_le_iff₀ (by positivity)).mp hxB
    have hh : 1 ≤ (x/2)*(k : ℝ)^4 := by
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hkR (show 0 ≤ x*(k : ℝ)^3 by positivity)]
    have hres1 := rescale_width (k := k) (a := 4) (b := 0) hk0 (by positivity) hAlo hh
    simp only [Nat.add_zero, pow_zero, div_one] at hres1
    have hres2 := rescale_width (k := k) (a := 3) (b := 0) hk0 (by positivity) hmX hp
    simp only [Nat.add_zero, pow_zero, div_one] at hres2
    have hres3 : (U.card : ℝ)/(k : ℝ)^7 ≤ (m : ℝ) := by
      rw [show (7:ℕ) = 4+3 from rfl, pow_add, ← div_div]
      exact (div_le_div_of_nonneg_right hres1 (by positivity)).trans hres2
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hk1 (show 7 ≤ 45 by decide))).trans hres3
  let P : OrderedBlockade U (OneWaySparse G x) k := {
    part := B,
    sub := fun i => (hB i).1.trans hAU,
    disjoint := hdis,
    ordered := fun i j _ b hb => by
      have hdeg' := hdeg b ((hB j).1 hb)
      have hM : ((neighborsIn G b (B i)).card : ℝ) ≤ (neighborsIn G b A).card := by
        exact_mod_cast Finset.card_le_card (neighborsIn_mono (hB i).1)
      rw [(hB i).2]
      exact hM.trans (hdeg'.trans
        ((mul_le_mul_of_nonneg_right hxs (by positivity)).trans
          (by nlinarith [mul_le_mul_of_nonneg_left hmX hx.le]))) }
  exact ⟨k, hk2, by linarith, P.toDensity, fun i => by simpa [OrderedBlockade.toDensity, P, (hB i).2] using hwidth⟩

/-- The first sparsification iteration, from an initially sparse house-free induced graph. -/
theorem house_first_blockade {V : Type*} {G : SimpleGraph V} {U : Finset V}
    (hfree : HouseFree G) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1/256)
    (hU : 2 ≤ x^5 * (U.card : ℝ))
    (hdeg : DegreeBound G U (((1:ℝ)/256)^3/2)) :
    ∃ k : ℕ, 2 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ ∃ B : DensityBlockade G U k x,
      ∀ i, (U.card : ℝ)/(k : ℝ)^45 ≤ (B.part i).card := by
  classical
  obtain ⟨y, hy, A, hAU, hA, hAd, hmin⟩ := minimum_degree_scale G U
    (lo := x/2) (hi := 1/256) (by linarith)
    (fun y => y) (fun y => y^3/2) continuous_id (by fun_prop) (by norm_num) hdeg
  by_cases hxy : x ≤ y
  swap
  · exact first_exit hx hx1 hy.1 (le_of_not_ge hxy) hU hAU hA hAd
  have hy0 : 0 < y := hx.trans_le hxy
  have hsize : 2 ≤ y^4*(A.card : ℝ) := by
    have hp := pow_le_pow_left₀ hx.le hxy 5
    nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) U.card),
      mul_le_mul_of_nonneg_left hA (pow_nonneg hy0.le 4)]
  rcases first_growth hfree hx hxy hy.2 hsize hAd with
    ⟨R, hRA, hRc, hRd⟩ | ⟨k, hk, hX, hY, P, hP⟩ | ⟨k, hk, hX, hY, P, hP⟩
  · exfalso
    have hh := hmin (y/2) ⟨by linarith, by linarith [hy.2]⟩ R (hRA.trans hAU)
      (by linarith) hRd
    linarith
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hk5 : (16 : ℝ)*(k : ℝ) ≤ (k : ℝ)^5 := by
      rw [pow_succ]
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hkR 4
      norm_num at h
      exact mul_le_mul_of_nonneg_right h hk0.le
    have hkY : 1 ≤ y*(k : ℝ)^5 := by
      nlinarith [mul_le_mul_of_nonneg_left hk5 hy0.le]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1/(k : ℝ)^5)
      ((div_le_iff₀ (by positivity)).mpr hkY) 6
    rw [div_pow, one_pow, ← pow_mul] at hp
    have hp' : 1/(k : ℝ)^30 ≤ y^6 := hp
    let B : OrderedBlockade U (OneWaySparse G x) k :=
      ⟨P.part, fun i => (P.sub i).trans hAU, P.disjoint, P.ordered⟩
    refine ⟨k, hk, hX, B.toDensity, fun i => ?_⟩
    change (U.card : ℝ)/(k : ℝ)^45 ≤ (P.part i).card
    calc
      _ ≤ (U.card : ℝ)/(k : ℝ)^30 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by linarith) (by decide : 30 ≤ 45))
      _ = (1/(k : ℝ)^30)*(U.card : ℝ) := one_div_mul_eq_div _ _ |>.symm
      _ ≤ y^6*(U.card : ℝ) := mul_le_mul_of_nonneg_right hp' (by positivity)
      _ ≤ y^5*(A.card : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hA (pow_nonneg hy0.le 5)]
      _ ≤ _ := hP i
  · have hk' : 2 ≤ k := by omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    let B : PureBlockade G U k := ⟨P.part, fun i => (P.part_sub i).trans hAU, P.disjoint, P.pure⟩
    refine ⟨k, hk', hX, B.toDensity hx.le, fun i => ?_⟩
    exact (rescale_width (k := k) (a := 6) (b := 39) hk0 (by positivity) hA hY).trans (hP i)

private theorem neighborsIn_subtype_card {V : Type*} (G : SimpleGraph V) (U : Finset V)
    (A : Finset (U : Set V)) (x : (U : Set V)) :
    let f : (U : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    (neighborsIn (G.induce (U : Set V)) x A).card =
      (neighborsIn G x.val (A.map f)).card := by
  classical
  let f : (U : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  change (neighborsIn (G.induce (U : Set V)) x A).card =
    (neighborsIn G x.val (A.map f)).card
  have h : (neighborsIn (G.induce (U : Set V)) x A).map f =
      neighborsIn G x.val (A.map f) := by
    ext v
    simp only [Finset.mem_map, mem_neighborsIn]
    constructor
    · rintro ⟨y, ⟨hy, hadj⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hadj⟩
    · rintro ⟨⟨y, hy, rfl⟩, hadj⟩
      exact ⟨y, ⟨hy, hadj⟩, rfl⟩
  rw [← h, Finset.card_map]

theorem sparse_side_in (F : SimpleGraph (Fin 5)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ {V : Type} (G : SimpleGraph V), Free F G → ∀ U : Finset V,
      ∃ A : Finset V, A ⊆ U ∧ δ * (U.card : ℝ) ≤ A.card ∧
        (DegreeBound G A ε ∨ DegreeBound Gᶜ A ε) := by
  classical
  obtain ⟨δ, hδ, h⟩ := sparse_side F ε hε
  refine ⟨δ,hδ,?_⟩
  intro V G hG U
  let H := G.induce (U : Set V)
  have hh : Free F H := free_of_embedding hG (Embedding.induce (U : Set V))
  obtain ⟨B, hB, hbd⟩ := h H hh
  let f : (U : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨B.map f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
    exact v.property
  · rw [Finset.card_map]
    have hc : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
    simpa only [hc] using hB
  have map_degree (K : SimpleGraph V)
      (hg : DegreeBound (K.induce (U : Set V)) B ε) :
      DegreeBound K (B.map f) ε := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    rw [Finset.card_map]
    change ((neighborsIn K v.val (B.map f)).card : ℝ) ≤ ε * B.card
    rw [← neighborsIn_subtype_card K U B v]
    exact hg v hv
  rcases hbd with hb | hb
  · exact Or.inl (map_degree G hb)
  · apply Or.inr
    apply map_degree Gᶜ
    have eq : Gᶜ.induce (U : Set V) = Hᶜ := by
      ext x y
      change ((x : V) ≠ (y : V) ∧ ¬ G.Adj x y) ↔ x ≠ y ∧ ¬ G.Adj x y
      exact and_congr_left' (not_congr Subtype.val_injective.eq_iff)
    rw [eq]
    exact hb

theorem first_blockade :
    ∃ d : ℕ, 45 ≤ d ∧ ∀ {V : Type} (G : SimpleGraph V), HouseFree G →
      ∀ (U : Finset V) (x : ℝ), 0 < x → x ≤ 1/256 → 1 ≤ x^d*(U.card : ℝ) →
      ∃ k : ℕ, 2 ≤ k ∧ x*(k : ℝ) ≤ 1 ∧ ∃ B : DensityBlockade G U k x,
        ∀ i, (U.card : ℝ)/(k : ℝ)^d ≤ (B.part i).card := by
  classical
  let ε : ℝ := ((1:ℝ)/256)^3/2
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨δ,hδ,hd⟩ := sparse_side_in (pathGraph 5)ᶜ ε hε
  obtain ⟨D,hD⟩ := pow_unbounded_of_one_lt (32/δ : ℝ) (by norm_num : (1:ℝ)<2)
  have hδ32 : 1/(2:ℝ)^D ≤ δ/32 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^D)).mpr
    have hh := (div_lt_iff₀ hδ).mp hD
    linarith
  refine ⟨D+45, by omega, ?_⟩
  intro V G hfree U x hx hx1 hU
  obtain ⟨A,hAU,hAc,hAd⟩ := hd G hfree U
  have hpos : (0 : ℝ) < U.card := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.le (D+45)) h]
  have hxle : x ≤ 1 := by linarith
  have hDle : x^D ≤ δ/32 := by
    have hxbound : x ≤ 1/(2:ℝ) := by linarith
    have ht := pow_le_pow_left₀ hx.le hxbound D
    rw [div_pow, one_pow] at ht
    exact ht.trans hδ32
  have hlarge : 2 ≤ x^5*(A.card : ℝ) := by
    have hpow : x^(D+45) ≤ (δ/32)*x^5 := by
      rw [pow_add]
      exact mul_le_mul hDle (pow_le_pow_of_le_one hx.le hxle (by decide))
        (pow_nonneg hx.le 45) (by positivity)
    have hh := mul_le_mul_of_nonneg_right hpow hpos.le
    have ha := mul_le_mul_of_nonneg_left hAc (pow_nonneg hx.le 5)
    nlinarith
  rcases hAd with h | h
  · obtain ⟨k,hk,hxk,B,hB⟩ := house_first_blockade hfree hx hx1 hlarge h
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hw : 1/(k : ℝ)^D ≤ δ := calc
      _ ≤ 1/(2:ℝ)^D := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by norm_num) hk2 D)
      _ ≤ _ := hδ32.trans (by linarith)
    let P : DensityBlockade G U k x :=
      ⟨B.part, fun i => (B.sub i).trans hAU, B.disjoint, B.restricted⟩
    refine ⟨k,hk,hxk,P,fun i => ?_⟩
    have ht : 1 ≤ δ*(k : ℝ)^D := (div_le_iff₀ (by positivity)).mp hw
    exact (rescale_width (k := k) (a := D) (b := 45) hk0 hpos.le hAc ht).trans (hB i)
  · have hfc : PathFree Gᶜ := by
      simpa using (free_compl (G := G) (H := (pathGraph 5)ᶜ)).mpr hfree
    have hA2 : 2 ≤ A.card := by
      have hpow : x^5 ≤ 1 := pow_le_one₀ hx.le hxle
      have hh := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg (α := ℝ) A.card)
      have h' : (2 : ℝ) ≤ A.card := by linarith
      exact_mod_cast h'
    obtain ⟨B,C,hBA,hCA,hBC,hBc,hCc,hanti⟩ := sparse_path_has_large_pair hfc A hA2
      (fun a ha => (h a ha).trans (by dsimp [ε]; nlinarith [Nat.cast_nonneg (α := ℝ) A.card]))
    let P : Fin 2 → Finset V := ![B,C]
    have hPwidth (i : Fin 2) : (A.card : ℝ)/32 ≤ (P i).card := by
      fin_cases i
      · exact hBc
      · exact hCc
    have hPsub (i : Fin 2) : P i ⊆ U := by
      fin_cases i
      · exact hBA.trans hAU
      · exact hCA.trans hAU
    have hPdis : Pairwise (Function.onFun Disjoint P) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hBC
      · exact hBC.symm
      · exact (hij rfl).elim
    have hcompl : ∀ b ∈ B, ∀ c ∈ C, G.Adj b c := fun b hb c hc => by
      by_contra hnc
      have hne : b ≠ c := fun he => Finset.disjoint_left.mp hBC hb (he ▸ hc)
      exact hanti b hb c hc ((G.compl_adj _ _).mpr ⟨hne,hnc⟩)
    let Q : DensityBlockade G U 2 x := {
      part := P
      sub := hPsub
      disjoint := hPdis
      restricted := fun i j hij => Or.inl <| by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hcompl
        · exact fun c hc b hb => (hcompl b hb c hc).symm
        · exact (hij rfl).elim }
    refine ⟨2, le_rfl, by norm_num; linarith, Q, fun i => ?_⟩
    have hb : (U.card : ℝ)/(2:ℝ)^D ≤ (A.card : ℝ)/32 := by
      rw [← one_div_mul_eq_div]
      nlinarith [mul_le_mul_of_nonneg_right hδ32 hpos.le]
    have hp : (2:ℝ)^D ≤ (2:ℝ)^(D+45) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (div_le_div_of_nonneg_left hpos.le (by positivity) hp).trans (hb.trans (hPwidth i))

end FivePath

namespace FivePath

private theorem prune_many {V ι : Type*} [Fintype ι] (A : Finset V)
    (Good : ι → Finset V) (hsub : ∀ i, Good i ⊆ A) {p : ℝ}
    (hLoss : ∀ i, (A.card : ℝ) ≤ (Good i).card + p*A.card) :
    ∃ D : Finset V, D ⊆ A ∧ (1-(Fintype.card ι : ℝ)*p)*(A.card : ℝ) ≤ D.card ∧
      ∀ i, D ⊆ Good i := by
  classical
  let Bad := fun i => A \ Good i
  let C := Finset.univ.biUnion Bad
  let D := A \ C
  have hCsub : C ⊆ A := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.sdiff_subset hi
  have hcount : (C.card : ℝ) ≤ (Fintype.card ι : ℝ) * (p*(A.card : ℝ)) := by
    have h := Finset.card_biUnion_le (s := Finset.univ) (t := Bad)
    calc
      _ ≤ ∑ i, ((Bad i).card : ℝ) := by exact_mod_cast h
      _ ≤ ∑ _i : ι, p*(A.card : ℝ) := Finset.sum_le_sum fun i _ => by
        have hh : ((Bad i).card : ℝ) + (Good i).card = A.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card (hsub i)
        linarith [hLoss i]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
  have hSplit : (D.card : ℝ) + C.card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hCsub
  refine ⟨D, Finset.sdiff_subset, by linarith, ?_⟩
  intro i x hx
  by_contra hn
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.sdiff_subset hx, hn⟩⟩)

private theorem trim_one_pair {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hB : (0 : ℝ) < B.card)
    (h : edgeCountBetween G A B ≤ q*(A.card : ℝ)*B.card) :
    ∃ D : Finset V, D ⊆ A ∧ (A.card : ℝ) ≤ D.card + p*A.card ∧
      ∀ a ∈ D, (neighborsIn G a B).card ≤ (q/p)*(B.card : ℝ) := by
  apply sparse_rows_from_total G A B (by positivity)
  convert h using 1
  field_simp

private def PairComplete {V : Type*} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

private theorem pair_complete_symm {V : Type*} {G : SimpleGraph V} {A B : Finset V}
    (h : PairComplete G A B) : PairComplete G B A :=
  fun b hb a ha => (h a ha b hb).symm

/-- Select equal-sized blocks using only deterministic row pruning. -/
theorem equalize_density_blockade {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {k m : ℕ} {q p : ℝ} (B : DensityBlockade G U k q) (hq : 0 < q) (hp : 0 < p)
    (hm : 0 < m) (hkp : (k : ℝ)*p ≤ 1/2)
    (hB : ∀ i, 2*m ≤ (B.part i).card) :
    ∃ X : Fin k → Finset V, (∀ i, X i ⊆ B.part i ∧ (X i).card=m) ∧
      ∀ i j, i ≠ j → ¬ PairComplete G (B.part i) (B.part j) →
        edgeCountBetween G (X i) (X j) ≤ (q/p/p)*(m:ℝ)^2 := by
  classical
  let f : ℝ := q/p
  let t : ℝ := f/p
  have hf : 0 < f := by dsimp [f]; positivity
  have hBn (i : Fin k) : (0 : ℝ) < (B.part i).card := by
    have ht := hB i
    exact_mod_cast (show 0 < (B.part i).card by omega)
  have build (j : ℕ) (hj : j ≤ k) :
      ∃ X : Fin k → Finset V, (∀ i : Fin k, (i : ℕ) < j → X i ⊆ B.part i ∧ (X i).card=m) ∧
        (∀ (a b : Fin k), (a : ℕ) < j → j ≤ (b : ℕ) →
          ¬ PairComplete G (B.part a) (B.part b) →
            ∀ v ∈ X a, (neighborsIn G v (B.part b)).card ≤ f*(B.part b).card) ∧
        (∀ a b : Fin k, a < b → (b : ℕ) < j →
          ¬ PairComplete G (B.part a) (B.part b) →
            edgeCountBetween G (X a) (X b) ≤ t*(m:ℝ)^2) := by
    induction j with
    | zero => exact ⟨fun _ => ∅, by simp⟩
    | succ j ih =>
      obtain ⟨X, hX, hFuture, hPast⟩ := ih (by omega)
      let i : Fin k := ⟨j, by omega⟩
      have good (b : Fin k) :
          ∃ D : Finset V, D ⊆ B.part i ∧ (B.part i).card ≤ (D.card : ℝ) + p*(B.part i).card ∧
            ((b < i → ¬PairComplete G (B.part b) (B.part i) →
              ∀ z ∈ D, (neighborsIn G z (X b)).card ≤ t*(X b).card) ∧
             (i < b → ¬PairComplete G (B.part i) (B.part b) →
              ∀ z ∈ D, (neighborsIn G z (B.part b)).card ≤ f*(B.part b).card)) := by
        rcases lt_trichotomy b i with hbi | he | hib
        · by_cases h : PairComplete G (B.part b) (B.part i)
          · exact ⟨_, Finset.Subset.refl _, by linarith [mul_nonneg hp.le (hBn i).le],
              fun _ hn => (hn h).elim, fun hh => (asymm hbi hh).elim⟩
          have hD := edgeCount_le_mul G (X b) (B.part i) f (hFuture b i hbi le_rfl h)
          rw [edgeCount_comm] at hD
          have hD' : edgeCountBetween G (B.part i) (X b) ≤ f * (B.part i).card * (X b).card := by
            convert hD using 1
            ring
          have hXpos : (0 : ℝ) < (X b).card := by rw [(hX b hbi).2]; exact_mod_cast hm
          obtain ⟨D, hD, hLoss,hBound⟩ := trim_one_pair G (B.part i) (X b) hf hp hXpos hD'
          exact ⟨D, hD, hLoss, fun _ _ => hBound, fun hh => (asymm hbi hh).elim⟩
        · subst b
          exact ⟨_, Finset.Subset.refl _, by linarith [mul_nonneg hp.le (hBn i).le],
            fun h => (lt_irrefl _ h).elim, fun h => (lt_irrefl _ h).elim⟩
        · by_cases h : PairComplete G (B.part i) (B.part b)
          · exact ⟨_, Finset.Subset.refl _, by linarith [mul_nonneg hp.le (hBn i).le],
              fun hh => (asymm hib hh).elim, fun _ hn => (hn h).elim⟩
          have hh := (B.restricted i b hib.ne).resolve_left h
          obtain ⟨D,hD,hLoss,hBound⟩ := trim_one_pair G (B.part i) (B.part b) hq hp (hBn b) hh
          exact ⟨D, hD, hLoss, fun hh => (asymm hib hh).elim, fun _ _ => hBound⟩
      choose D hD hLoss hBound using good
      obtain ⟨Z,hZ,hZc,hZD⟩ := prune_many (B.part i) D hD hLoss
      have hmZ : m ≤ Z.card := by
        have hh : (2*(m:ℝ)) ≤ (B.part i).card := by exact_mod_cast hB i
        have hc : (1/2:ℝ)*(B.part i).card ≤ (Z.card:ℝ) := by
          have h := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-(k:ℝ)*p by linarith)
            (hBn i).le
          exact h.trans (by simpa using hZc)
        have hl : (m:ℝ) ≤ Z.card := by linarith
        exact_mod_cast hl
      obtain ⟨Y,hY,hYm⟩ := Finset.exists_subset_card_eq hmZ
      let X' := Function.update X i Y
      refine ⟨X', ?_, ?_, ?_⟩
      · intro a ha
        by_cases h : a = i
        · subst a
          simpa [X'] using And.intro (hY.trans hZ) hYm
        · have ha' : (a : ℕ) < j := by
            by_contra! he
            exact h (Fin.ext (by change (a : ℕ) = j; omega))
          simpa [X', Function.update_of_ne h] using hX a ha'
      · intro a b ha hb hcp v hv
        by_cases h : a = i
        · subst a
          have hb' : i < b := by change j < (b : ℕ); omega
          exact (hBound b).2 hb' hcp v (hZD b (hY (by simpa [X'] using hv)))
        · have ha' : (a : ℕ) < j := by
            by_contra! he
            exact h (Fin.ext (by change (a : ℕ) = j; omega))
          have hv' : v ∈ X a := by simpa [X', Function.update_of_ne h] using hv
          exact hFuture a b ha' (by omega) hcp v hv'
      · intro a b hab hb hcp
        by_cases h : b = i
        · subst b
          have ha : a ≠ i := hab.ne
          have hYdeg : ∀ z ∈ Y, (neighborsIn G z (X a)).card ≤ t*(X a).card :=
            fun z hz => (hBound a).1 hab hcp z (hZD a (hY hz))
          have hcount := edgeCount_le_mul G Y (X a) t hYdeg
          rw [hYm, (hX a hab).2, edgeCount_comm] at hcount
          simpa [X', Function.update_of_ne ha, sq, mul_assoc] using hcount
        · have hb' : (b : ℕ) < j := by
            by_contra! h'
            exact h (Fin.ext (by change (b : ℕ) = j; omega))
          have ha : a ≠ i := by
            intro he
            subst a
            exact (not_lt_of_ge (show (b : ℕ) ≤ (i : ℕ) by dsimp [i]; omega)) hab
          simpa [X', Function.update_of_ne ha, Function.update_of_ne h] using hPast a b hab hb' hcp
  obtain ⟨X,hX,_,hW⟩ := build k le_rfl
  refine ⟨X,fun i => hX i i.isLt,?_⟩
  intro i j hij hcomp
  rcases lt_or_gt_of_ne hij with h | h
  · exact hW i j h j.isLt hcomp
  · rw [edgeCount_comm]
    exact hW j i h i.isLt (fun hc => hcomp (pair_complete_symm hc))

private abbrev CompleteBlockade {V : Type*} (G : SimpleGraph V) (U : Finset V) (k : ℕ) :=
  OrderedBlockade U (PairComplete G) k

theorem anticonnected_refinement {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {k m : ℕ} {q p : ℝ} (B : DensityBlockade G U k q) (hk : 2 ≤ k)
    (hq : 0 < q) (hp : 0 < p) (hm : 0 < m)
    (hkp : (k : ℝ)*p ≤ 1/2) (hB : ∀ i, 2*m ≤ (B.part i).card) :
    (∃ C : CompleteBlockade G U k, ∀ i, (m : ℝ)/(2*(k : ℝ)^2) ≤ (C.part i).card) ∨
    ∃ A : Fin k → Finset V,
      (∀ i, A i ⊆ B.part i ∧ internallyConnected Gᶜ (A i) ∧
        p*(m:ℝ) ≤ (A i).card ∧ (A i).card ≤ m) ∧
      ∀ i j, i ≠ j → ¬PairComplete G (B.part i) (B.part j) →
        ∀ v ∈ A i, (neighborsIn G v (A j)).card ≤ (q/p/p/p)*(m:ℝ) := by
  classical
  obtain ⟨X,hX,hEx⟩ := equalize_density_blockade B hq hp hm hkp hB
  let r : ℝ := q/p/p
  let s : ℝ := r/p
  have hr : 0 < r := by dsimp [r]; positivity
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hGood (i j : Fin k) :
      ∃ D : Finset V, D ⊆ X i ∧ (X i).card ≤ (D.card:ℝ)+p*(X i).card ∧
        (i ≠ j → ¬ PairComplete G (B.part i) (B.part j) →
          ∀ v ∈ D, (neighborsIn G v (X j)).card ≤ s*(m:ℝ)) := by
    by_cases h : i ≠ j ∧ ¬ PairComplete G (B.part i) (B.part j)
    swap
    · refine ⟨X i,Finset.Subset.refl _,by linarith [mul_nonneg hp.le (Nat.cast_nonneg (α := ℝ) (X i).card)],?_⟩
      exact fun hij hj => (h ⟨hij,hj⟩).elim
    have he := hEx i j h.1 h.2
    have hh : edgeCountBetween G (X i) (X j) ≤ r * (X i).card * (X j).card := by
      rw [(hX i).2,(hX j).2]
      simpa [r,sq,mul_assoc] using he
    have hjp : (0 : ℝ) < (X j).card := by simpa [(hX j).2] using hmR
    obtain ⟨D,hD,hLoss,hBound⟩ := trim_one_pair G (X i) (X j) hr hp hjp hh
    exact ⟨D,hD,hLoss,fun _ _ v hv => by simpa [s,(hX j).2] using hBound v hv⟩
  have hPrune (i : Fin k) :
      ∃ D : Finset V, D ⊆ X i ∧ (m : ℝ)/2 ≤ D.card ∧
        ∀ j, i ≠ j → ¬ PairComplete G (B.part i) (B.part j) →
          ∀ v ∈ D, (neighborsIn G v (X j)).card ≤ s*(m:ℝ) := by
    choose F hF hLoss hBd using hGood i
    obtain ⟨D,hD,hDsize,hDF⟩ := prune_many (X i) F hF hLoss
    have hh : (m : ℝ)/2 ≤ (D.card : ℝ) := by
      rw [(hX i).2, Fintype.card_fin] at hDsize
      nlinarith [mul_le_mul_of_nonneg_right hkp hmR.le]
    exact ⟨D,hD,hh,fun j hij hj v hv => hBd j hij hj v (hDF j hv)⟩
  choose D hD hDc hDdeg using hPrune
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hDne (i : Fin k) : (D i).Nonempty := Finset.card_pos.mp (by
    have ht : (0 : ℝ) < (D i).card := (by positivity : 0 < (m:ℝ)/2).trans_le (hDc i)
    exact_mod_cast ht)
  by_cases H : ∀ i, ∃ Z : Finset V, Z ⊆ D i ∧ internallyConnected Gᶜ Z ∧
      ((D i).card : ℝ)/(k : ℝ) ≤ Z.card
  · apply Or.inr
    choose A hA hAc hAw using H
    have hAX i : A i ⊆ X i := (hA i).trans (hD i)
    refine ⟨A,fun i => ⟨(hAX i).trans (hX i).1,hAc i,?_,?_
      ⟩,fun i j hij hp v hv => ?_⟩
    · have hw : p ≤ 1/(2*(k:ℝ)) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      calc
        p*(m:ℝ) ≤ (1/(2*(k:ℝ)))*(m:ℝ) := mul_le_mul_of_nonneg_right hw hmR.le
        _ = ((m:ℝ)/2)/(k:ℝ) := by field_simp
        _ ≤ ((D i).card : ℝ)/(k:ℝ) := div_le_div_of_nonneg_right (hDc i) hkR.le
        _ ≤ _ := hAw i
    · simpa [(hX i).2] using Finset.card_le_card (hAX i)
    have hM : ((neighborsIn G v (A j)).card : ℝ) ≤ (neighborsIn G v (X j)).card := by
      exact_mod_cast Finset.card_le_card (neighborsIn_mono (hAX j))
    exact hM.trans (hDdeg i j hij hp v (hA i hv))
  push Not at H
  obtain ⟨i,hno⟩ := H
  rcases components_or_anticomplete Gᶜ (D i) (hDne i) hk with
    ⟨Z,hZ,hCon,hSize⟩ | ⟨C,hC,hP⟩
  · exact ((hno Z hZ hCon).not_ge hSize).elim
  apply Or.inl
  refine ⟨⟨C,fun j => ((hC j).1.trans (hD i)).trans ((hX i).1.trans (B.sub i)),
    fun j l hjl => (hP j l hjl).1, fun j l hjl a ha b hb => ?_⟩,fun j => ?_⟩
  · by_contra h
    have hne : a ≠ b := fun he => Finset.disjoint_left.mp (hP j l hjl.ne).1 ha (he ▸ hb)
    exact (hP j l hjl.ne).2 a ha b hb ((G.compl_adj _ _).mpr ⟨hne,h⟩)
  · rw [← div_div]
    exact (div_le_div_of_nonneg_right (hDc i) (by positivity)).trans (hC j).2

private theorem internallyConnected_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A : Finset V} (hA : internallyConnected G A) {v x : V} (hv : v ∈ A) (h : G.Adj v x) :
    internallyConnected G (insert x A) := by
  classical
  change (G.induce ((insert x A : Finset V) : Set V)).Connected
  rw [connected_iff_exists_forall_reachable]
  let e := induceHomOfLE (G := G) (s := (A : Set V)) (s' := ((insert x A : Finset V) : Set V))
    (fun _ ha => Finset.mem_insert_of_mem ha)
  refine ⟨e ⟨v,hv⟩, fun w => ?_⟩
  rcases Finset.mem_insert.mp w.property with hw | hw
  · have h' : (G.induce ((insert x A : Finset V) : Set V)).Adj (e ⟨v,hv⟩) w := by
      change G.Adj v w.val
      rwa [hw]
    exact h'.reachable
  · have hr := (hA.preconnected ⟨v,hv⟩ ⟨w.val,hw⟩).map e.toHom
    exact hr

theorem internallyConnected_pick_card {V : Type*} {G : SimpleGraph V} {U : Finset V}
    (hU : internallyConnected G U) {m : ℕ} (hm : 0 < m) (hcard : m ≤ U.card) :
    ∃ A : Finset V, A ⊆ U ∧ internallyConnected G A ∧ A.card = m := by
  classical
  obtain ⟨⟨v,hv⟩⟩ := hU.nonempty
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : m = 0
    · subst m
      refine ⟨{v},Finset.singleton_subset_iff.mpr hv, ?_, Finset.card_singleton _⟩
      change (G.induce (({v} : Finset V) : Set V)).Connected
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨v,Finset.mem_singleton_self _⟩, fun x => ?_⟩
      have hx : x = ⟨v,Finset.mem_singleton_self _⟩ :=
        Subtype.ext (Finset.mem_singleton.mp x.property)
      rw [hx]
    obtain ⟨A,hAU,hA,hAc⟩ := ih (by omega) (by omega)
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    obtain ⟨y,hy,hyA⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : A.card < U.card)
    obtain ⟨a,_,b,hb,hab,ha,hbA⟩ := edge_crossing hU (·∈A) (hAU hx) hy hx hyA
    exact ⟨insert b A,Finset.insert_subset_iff.mpr ⟨hb,hAU⟩,
      internallyConnected_insert hA ha hab, by rw [Finset.card_insert_of_notMem hbA,hAc]⟩

theorem equal_anticonnected_refinement {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {k m : ℕ} {q p : ℝ} (B : DensityBlockade G U k q) (hk : 2 ≤ k)
    (hq : 0 < q) (hp : 0 < p) (hm : 0 < m)
    (hkp : (k : ℝ)*p ≤ 1/2) (hB : ∀ i, 2*m ≤ (B.part i).card) :
    (∃ C : CompleteBlockade G U k, ∀ i, (m : ℝ)/(2*(k : ℝ)^2) ≤ (C.part i).card) ∨
    ∃ A : Fin k → Finset V,
      (∀ i, A i ⊆ B.part i ∧ internallyConnected Gᶜ (A i) ∧ (A i).card=⌈p*(m:ℝ)⌉₊) ∧
      ∀ i j, i ≠ j → ¬PairComplete G (B.part i) (B.part j) →
        ∀ v ∈ A i, (neighborsIn G v (A j)).card ≤ (q/p/p/p/p)*(⌈p*(m:ℝ)⌉₊ : ℝ) := by
  classical
  rcases anticonnected_refinement B hk hq hp hm hkp hB with he | ⟨D,hD,hDdeg⟩
  · exact Or.inl he
  let r := ⌈p*(m:ℝ)⌉₊
  have hr (i : Fin k) : r ≤ (D i).card := Nat.ceil_le.mpr (hD i).2.2.1
  have hr0 : 0 < r := Nat.one_le_ceil_iff.mpr (by positivity)
  choose A hA hAc hArc using fun i => internallyConnected_pick_card (hD i).2.1 hr0 (hr i)
  refine Or.inr ⟨A,fun i => ⟨(hA i).trans (hD i).1,hAc i,hArc i⟩,?_⟩
  intro i j hij hcp v hv
  have hm' : ((neighborsIn G v (A j)).card : ℝ) ≤ (neighborsIn G v (D j)).card := by
    exact_mod_cast Finset.card_le_card (neighborsIn_mono (hA j))
  apply hm'.trans ((hDdeg i j hij hcp v (hA i hv)).trans ?_)
  have hceil : p*(m:ℝ) ≤ r := Nat.le_ceil _
  have hpos : 0 ≤ q/p/p/p/p := by positivity
  have hmul := mul_le_mul_of_nonneg_left hceil hpos
  have he : (q/p/p/p/p)*(p*(m:ℝ)) = (q/p/p/p)*(m:ℝ) := by field_simp
  simpa only [he] using hmul

end FivePath

namespace FivePath

private theorem neighbor_card_biUnion_le {V ι : Type*} (G : SimpleGraph V) (x : V)
    [DecidableEq V] (I : Finset ι) (A : ι → Finset V) :
    (neighborsIn G x (I.biUnion A)).card ≤ ∑ i ∈ I, (neighborsIn G x (A i)).card := by
  classical
  have he : neighborsIn G x (I.biUnion A) = I.biUnion (fun i => neighborsIn G x (A i)) := by
    ext y
    simp only [mem_neighborsIn,Finset.mem_biUnion]
    aesop
  rw [he]
  exact Finset.card_biUnion_le

private theorem sparse_union {V ι : Type*} (G : SimpleGraph V) (U : Finset V)
    (I : Finset ι) (A : ι → Finset V) {r : ℕ} {z q : ℝ}
    (hr : 0 < r) (hq : 0 ≤ q) (hQ : 2*q ≤ z) (hI : (2:ℝ) ≤ z*(I.card:ℝ))
    (hAsub : ∀ i ∈ I, A i ⊆ U) (hAsize : ∀ i ∈ I, (A i).card = r)
    (hDis : (I : Set ι).PairwiseDisjoint A)
    (hSlim : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ v ∈ A i,
      (neighborsIn G v (A j)).card ≤ q*(r:ℝ)) :
    ∃ X : Finset V, X ⊆ U ∧ r ≤ X.card ∧ DegreeBound G X z := by
  classical
  let X := I.biUnion A
  have hc : X.card = I.card*r := by
    rw [Finset.card_biUnion hDis]
    simp only [Finset.sum_congr rfl hAsize, Finset.sum_const_nat]
  have hIpos : 0 < I.card := by
    by_contra! h
    have hz : I.card = 0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hI
    norm_num at hI
  refine ⟨X,Finset.biUnion_subset.mpr hAsub,?_,fun x hx => ?_⟩
  · rw [hc]
    exact (Nat.one_mul r).symm.le.trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
  let F j := ((neighborsIn G x (A j)).card : ℝ)
  have hF : ((neighborsIn G x X).card : ℝ) ≤ ∑ j ∈ I,F j := by
    dsimp [F,X]
    exact_mod_cast neighbor_card_biUnion_le G x I A
  have hself : F i ≤ r := by
    dsimp [F]
    rw [← hAsize i hi]
    exact_mod_cast Finset.card_le_card (fun _ h => (mem_neighborsIn.mp h).1)
  have hcount : (∑ j ∈ I,F j) ≤ (r:ℝ)+I.card*(q*(r:ℝ)) := by
    rw [← Finset.sum_erase_add _ _ hi]
    have hslim : (∑ j ∈ I.erase i,F j) ≤ (I.erase i).card*(q*(r:ℝ)) := by
      calc
       _ ≤ ∑ _ ∈ I.erase i,q*(r:ℝ) := Finset.sum_le_sum fun j hj =>
          hSlim i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm x hxi
       _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    have he : ((I.erase i).card : ℝ) ≤ I.card := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
    linarith [mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ q*(r:ℝ))]
  apply hF.trans (hcount.trans ?_)
  rw [hc,Nat.cast_mul]
  have h₁ := mul_le_mul_of_nonneg_right hI (Nat.cast_nonneg (α := ℝ) r)
  have h₂ := mul_le_mul_of_nonneg_right hQ (show 0 ≤ (I.card:ℝ)*(r:ℝ) by positivity)
  nlinarith

private noncomputable def mixedIndices {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (A : Fin k → Finset V) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => Mixed G v (A i)

private noncomputable def mixedVertices {V : Type*} (G : SimpleGraph V)
    (R A : Finset V) : Finset V := by
  classical
  exact R.filter fun v => Mixed G v A

private theorem exists_small_mixed_class {V : Type*} (G : SimpleGraph V) (R : Finset V)
    {k : ℕ} (hk : 0 < k) (A : Fin k → Finset V) {y : ℝ}
    (h : ∀ v ∈ R, ((mixedIndices G A v).card : ℝ)
      ≤ y*(k : ℝ)) :
    ∃ i : Fin k, ((mixedVertices G R (A i)).card : ℝ) ≤ y*(R.card : ℝ) := by
  classical
  have hsum : (∑ i : Fin k, ((mixedVertices G R (A i)).card : ℝ)) ≤
      (k:ℝ)*(y*(R.card:ℝ)) := by
    have he :
        (∑ i : Fin k, ((mixedVertices G R (A i)).card : ℝ)) =
          ∑ v ∈ R, ((mixedIndices G A v).card : ℝ) := by
      simp only [mixedIndices, mixedVertices, Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      rw [Finset.sum_comm]
    rw [he]
    calc
      _ ≤ ∑ _ ∈ R,y*(k:ℝ) := Finset.sum_le_sum h
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring
  by_contra! hn
  have hpositive : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset (Fin k)).Nonempty)
    (fun i _ => hn i)
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlt
  exact hlt.not_ge hsum

theorem split_mixed_blocks {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r) (hfree : HouseFree G)
    (A : Fin k → Finset V) (hA : ∀ i, A i ⊆ U ∧ internallyConnected Gᶜ (A i) ∧ (A i).card = r)
    (hdis : Pairwise (Function.onFun Disjoint A)) {y z q : ℝ}
    (hy : 0 < y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hq : 0 ≤ q) (hQ : 2*q ≤ z)
    (hK : (2:ℝ) ≤ z*(y*(k:ℝ))) (hU : (k:ℝ)*r ≤ y^2*(U.card:ℝ))
    (hdeg : DegreeBound G U y)
    (hPair : ∀ i j, i ≠ j → PairComplete G (A i) (A j) ∨
      ∀ v ∈ A i, (neighborsIn G v (A j)).card ≤ q*(r:ℝ)) :
    (∃ X : Finset V, X ⊆ U ∧ r ≤ X.card ∧ DegreeBound G X z) ∨
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧ Disjoint X Y ∧ r ≤ X.card ∧
      (1-3*y)*(U.card:ℝ) ≤ (Y.card:ℝ) ∧ Anticomplete G X Y := by
  classical
  let S := (Finset.univ : Finset (Fin k)).biUnion A
  let R := U \ S
  have hS : S ⊆ U := Finset.biUnion_subset.mpr (fun i _ => (hA i).1)
  have hR : R ⊆ U := Finset.sdiff_subset
  have hSc : (S.card : ℝ) = (k:ℝ)*r := by
    have hd : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint A :=
      fun _ _ _ _ hij => hdis hij
    have hS' : S.card = k*r := by
      rw [Finset.card_biUnion hd]
      rw [Finset.sum_congr rfl (fun i _ => (hA i).2.2)]
      simp only [Finset.sum_const_nat,Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hS'
  have hRc : (1-y^2)*(U.card:ℝ) ≤ (R.card:ℝ) := by
    have hh : (R.card:ℝ) + S.card = U.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hS
    nlinarith
  by_cases hex : ∃ v ∈ R, y*(k:ℝ) ≤
      ((mixedIndices G A v).card : ℝ)
  · obtain ⟨v,hv,hvc⟩ := hex
    let I := mixedIndices G A v
    have hv' (i : Fin k) : v ∉ A i := fun hi => (Finset.mem_sdiff.mp hv).2
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
    apply Or.inl
    refine sparse_union G U I A hr hq hQ
      (hK.trans (mul_le_mul_of_nonneg_left hvc hz))
      (fun i _ => (hA i).1) (fun i _ => (hA i).2.2) (fun _ _ _ _ hij => hdis hij) ?_
    intro i hi j hj hij
    rcases hPair i j hij with hc | hh
    · exfalso
      have hfree' : PathFree Gᶜ := by
        simpa using (free_compl (G := G) (H := (pathGraph 5)ᶜ)).mpr hfree
      exact hfree' (double_mixed_induces_p5 (hA i).2.1 (hA j).2.1
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (hv' i) (hv' j) hc)
    · exact hh
  apply Or.inr
  obtain ⟨i,hi⟩ := exists_small_mixed_class G R hk A (fun v hv => by
    apply le_of_lt
    exact lt_of_not_ge (fun h => hex ⟨v,hv,h⟩))
  let M := mixedVertices G R (A i)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by simpa only [(hA i).2.2] using hr :
    0 < (A i).card)
  let T := M ∪ neighborsIn G x U
  let Y := R \ T
  have hanti : Anticomplete G (A i) Y := by
    intro a ha y hy' hadj
    have hyr := (Finset.mem_sdiff.mp hy').1
    have hyM : ¬Mixed G y (A i) := fun hm => (Finset.mem_sdiff.mp hy').2
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyr,hm⟩))
    rcases not_mixed.mp hyM with hc | hc
    · exact (Finset.mem_sdiff.mp hy').2 (Finset.mem_union_right _
        (mem_neighborsIn.mpr ⟨hR hyr,(hc x hx).symm⟩))
    · exact hc a ha hadj.symm
  have hDis : Disjoint (A i) Y := by
    apply Finset.disjoint_left.mpr
    intro a ha hy'
    exact (Finset.mem_sdiff.mp (Finset.sdiff_subset hy' : a ∈ R)).2
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
  have hY : (1-3*y)*(U.card:ℝ) ≤ (Y.card:ℝ) := by
    have ht : (T.card:ℝ) ≤ (M.card:ℝ) + (neighborsIn G x U).card := by
      exact_mod_cast Finset.card_union_le M (neighborsIn G x U)
    have hYc : (Y.card : ℝ) + T.card ≥ R.card := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card
    have hd := hdeg x ((hA i).1 hx)
    have hRle : (R.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hR
    have ht' := mul_le_mul_of_nonneg_left hRle hy.le
    have hYY : y^2 ≤ y := by nlinarith [mul_le_mul_of_nonneg_left hy1 hy.le]
    nlinarith [mul_le_mul_of_nonneg_right hYY (Nat.cast_nonneg (α := ℝ) U.card)]
  exact ⟨A i,Y,(hA i).1,Finset.sdiff_subset.trans hR,hDis,
    (hA i).2.2.ge,hY,hanti⟩

end FivePath

namespace FivePath

theorem edgeCount_mono {V : Type*} {G : SimpleGraph V} {A B C D : Finset V}
    (hAC : A ⊆ C) (hBD : B ⊆ D) : edgeCountBetween G A B ≤ edgeCountBetween G C D := by
  classical
  unfold edgeCountBetween
  calc
    _ ≤ ∑ a ∈ A, ((neighborsIn G a D).card : ℝ) := Finset.sum_le_sum fun a _ => by
      exact_mod_cast Finset.card_le_card (neighborsIn_mono hBD)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hAC (fun _ _ _ => by positivity)

private def LayoutPair {V : Type*} (G : SimpleGraph V) (e : ℝ) (A B : Finset V) : Prop :=
  Disjoint A B ∧ ((∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ edgeCountBetween G A B ≤ e)

private theorem LayoutPair.symm {V : Type*} {G : SimpleGraph V} {e : ℝ} {A B : Finset V}
    (h : LayoutPair G e A B) : LayoutPair G e B A := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with h | h
  · exact Or.inl fun b hb a ha => (h a ha b hb).symm
  · rw [edgeCount_comm]
    exact Or.inr h

private theorem LayoutPair.mono_left {V : Type*} {G : SimpleGraph V} {e : ℝ} {A B C : Finset V}
    (h : LayoutPair G e A B) (hc : C ⊆ A) : LayoutPair G e C B := by
  refine ⟨Disjoint.mono_left hc h.1, ?_⟩
  rcases h.2 with ha | he
  · exact Or.inl (fun a ha' => ha a (hc ha'))
  · exact Or.inr ((edgeCount_mono hc (Finset.Subset.refl _)).trans he)

private theorem positive_parts_injective {V : Type*} {ι : Type*} {B : ι → Finset V}
    (hp : ∀ i, (B i).Nonempty) (hd : Pairwise (Function.onFun Disjoint B)) :
    Function.Injective B := by
  intro i j he
  by_contra hij
  obtain ⟨a, ha⟩ := hp i
  exact Finset.disjoint_left.mp (hd hij) ha (he ▸ ha)

private theorem block_rpow_mass {V : Type*} {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    {A : Finset V} {B : Fin k → Finset V}
    (hsize : ∀ i, (A.card : ℝ)/(k : ℝ)^d ≤ (B i).card) :
    (A.card : ℝ)^(1/(d : ℝ)) ≤ ∑ i, ((B i).card : ℝ)^(1/(d : ℝ)) := by
  classical
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ht : 0 ≤ (1/(d : ℝ)) := by positivity
  have hconst := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    Real.rpow_le_rpow (by positivity) (hsize i) ht)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul hkR.le,
    show (d : ℝ)*(1/(d:ℝ)) = 1 by field_simp, Real.rpow_one] at hconst
  have he : (k : ℝ) * ((A.card : ℝ)^(1/(d : ℝ)) / (k : ℝ)) =
      (A.card : ℝ)^(1/(d : ℝ)) := by field_simp
  rwa [he] at hconst

theorem first_to_long {V : Type*} {G : SimpleGraph V} (U : Finset V) {d : ℕ} (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/256)
    (hW : (0 : ℝ) < U.card)
    (hsplit : ∀ A : Finset V, A ⊆ U → ε^d*(U.card : ℝ) ≤ A.card →
      ∃ k : ℕ, 2 ≤ k ∧ ε^(5*d)*(k : ℝ) ≤ 1 ∧
        ∃ B : DensityBlockade G A k (ε^(5*d)),
          ∀ i, (A.card : ℝ)/(k : ℝ)^d ≤ (B.part i).card) :
    ∃ B : DensityBlockade G U ⌈1/ε⌉₊ (ε^d),
      ∀ i, ε^(6*d*d) * (U.card : ℝ) ≤ (B.part i).card := by
  classical
  let W : ℝ := U.card
  let m := ⌈1/ε⌉₊
  let x := ε^(5*d)
  let q := ε^d
  let a := 1/(d : ℝ)
  have hε' : ε ≤ 1 := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hq1 : q ≤ 1 := pow_le_one₀ hε.le hε'
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hxx : x = q^5 := by dsimp [x,q]; rw [← pow_mul, Nat.mul_comm]
  have hxq : x ≤ q := by rw [hxx]; exact (pow_le_pow_of_le_one hq.le hq1 (by decide : 1 ≤ 5)).trans_eq (pow_one q)
  let valid (L : Finset (Finset V)) :=
    (∀ A ∈ L, A ⊆ U ∧ q^2*W ≤ A.card) ∧
    (L : Set (Finset V)).Pairwise (LayoutPair G (x*W^2)) ∧
    W^a ≤ ∑ A ∈ L, (A.card : ℝ)^a
  let S := (U.powerset.powerset).filter valid
  have hSmem {L : Finset (Finset V)} : L ∈ S ↔ valid L := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨fun A hA => Finset.mem_powerset.mpr (h.1 A hA).1, h⟩⟩
  have hS : S.Nonempty := by
    refine ⟨{U}, hSmem.mpr ?_⟩
    refine ⟨?_, ?_, by simp [W]⟩
    · intro A hA
      rw [Finset.mem_singleton.mp hA]
      exact ⟨Finset.Subset.refl _, mul_le_of_le_one_left hW.le (pow_le_one₀ hq.le hq1)⟩
    · intro A hA B hB hAB
      exact (hAB ((Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm)).elim
  obtain ⟨L, hLS, hLmax⟩ := Finset.exists_max_image S Finset.card hS
  have hL := hSmem.mp hLS
  have hLne : L.Nonempty := by
    by_contra! h
    have hh := hL.2.2
    rw [h, Finset.sum_empty] at hh
    exact (Real.rpow_pos_of_pos hW a).not_ge hh
  have hnum : 6*d*d ≥ 2*d := by
    have h := Nat.le_mul_of_pos_right (2*d) hd
    nlinarith
  have hlarge_width : ε^(6*d*d)*W ≤ q^2*W := by
    rw [show q^2 = ε^(2*d) by dsimp [q]; rw [← pow_mul,Nat.mul_comm]]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hε.le hε' hnum) hW.le
  by_cases hlm : m ≤ L.card
  · obtain ⟨K, hKL, hKm⟩ := Finset.exists_subset_card_eq hlm
    let e : ↥K ≃ Fin m := Fintype.equivFinOfCardEq ((Fintype.card_coe K).trans hKm)
    let P : Fin m → Finset V := fun i => (e.symm i).val
    have hP (i : Fin m) : P i ∈ L := hKL (e.symm i).property
    have hPi : Function.Injective P := Subtype.val_injective.comp e.symm.injective
    have hPair (i j : Fin m) (hij : i ≠ j) := hL.2.1 (hP i) (hP j) (fun he => hij (hPi he))
    refine ⟨⟨P, fun i => (hL.1 _ (hP i)).1, fun i j hij => (hPair i j hij).1, ?_⟩,
      fun i => hlarge_width.trans (hL.1 _ (hP i)).2⟩
    intro i j hij
    rcases (hPair i j hij).2 with h | h
    · exact Or.inl h
    · apply Or.inr
      have hi := (hL.1 _ (hP i)).2
      have hj := (hL.1 _ (hP j)).2
      have hh := mul_le_mul hi hj (by positivity : 0 ≤ q^2*W)
        (Nat.cast_nonneg (α := ℝ) (P i).card)
      have hh' := mul_le_mul_of_nonneg_left hh hq.le
      rw [hxx] at h
      nlinarith [h]
  have hlR : (L.card : ℝ) < 1/ε := Nat.lt_ceil.mp (lt_of_not_ge hlm)
  obtain ⟨A, hA, hAmax⟩ := Finset.exists_max_image L Finset.card hLne
  have hqA : q*W ≤ (A.card : ℝ) := by
    have hsum : W^a ≤ (L.card : ℝ) * (A.card : ℝ)^a := by
      apply hL.2.2.trans
      calc
        _ ≤ ∑ _ ∈ L, (A.card : ℝ)^a := Finset.sum_le_sum fun C hC =>
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hAmax C hC) ha.le
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hwa : ε * W^a ≤ (A.card : ℝ)^a := by
      have hmul := mul_le_mul_of_nonneg_left hsum hε.le
      have hl := (lt_div_iff₀ hε).mp hlR
      have hh := mul_le_mul_of_nonneg_right hl.le (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) A.card) a)
      nlinarith
    have hqpow :
        (q*W)^a = ε * W^a := by
      rw [Real.mul_rpow hq.le hW.le, show q = ε^d from rfl,
        ← Real.rpow_natCast_mul hε.le,
        show (d : ℝ)*a = 1 by dsimp [a]; field_simp, Real.rpow_one]
    rw [← hqpow] at hwa
    exact (Real.rpow_le_rpow_iff (by positivity) (by positivity) ha).mp hwa
  obtain ⟨k,hk,hkx,B,hB⟩ := hsplit A (hL.1 A hA).1 hqA
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hAn : (0 : ℝ) < A.card := (mul_pos hq hW).trans_le hqA
  have hBn (i : Fin k) : (B.part i).Nonempty := Finset.card_pos.mp (by
    have hh := (by positivity : 0 < (A.card : ℝ)/(k : ℝ)^d).trans_le (hB i)
    exact_mod_cast hh)
  by_cases hkM : m ≤ k
  · let f : Fin m ↪ Fin k := ⟨fun i => ⟨i.val, i.isLt.trans_le hkM⟩,
      fun _ _ he => Fin.ext (congrArg (fun j : Fin k => j.val) he)⟩
    refine ⟨⟨fun i => B.part (f i), fun i => (B.sub (f i)).trans (hL.1 A hA).1,
      fun _ _ hij => B.disjoint (fun he => hij (f.injective he)), ?_⟩, fun i => ?_⟩
    · intro i j hij
      rcases B.restricted (f i) (f j) (fun he => hij (f.injective he)) with ha | hs
      · exact Or.inl ha
      · exact Or.inr (hs.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hxq (by positivity)) (by positivity)))
    · have hkx' : x ≤ 1/(k : ℝ) := (le_div_iff₀ hkR).mpr hkx
      have hp := pow_le_pow_left₀ hx.le hkx' d
      rw [div_pow, one_pow] at hp
      have hnum' : 5*d*d+d ≤ 6*d*d := by
        have ht : d ≤ d*d := Nat.le_mul_of_pos_right d hd
        nlinarith
      calc
        ε^(6*d*d)*W ≤ ε^(5*d*d+d)*W := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hε.le hε' hnum') hW.le
        _ = x^d*(q*W) := by
          dsimp [x,q]
          rw [pow_add, pow_mul]
          ring
        _ ≤ (1/(k : ℝ)^d)*(A.card : ℝ) :=
          mul_le_mul hp hqA (by positivity) (by positivity)
        _ = (A.card : ℝ)/(k : ℝ)^d := one_div_mul_eq_div _ _
        _ ≤ _ := hB (f i)
  exfalso
  have hkε : (k : ℝ) < 1/ε := Nat.lt_ceil.mp (lt_of_not_ge hkM)
  have hr : q ≤ 1/(k : ℝ)^d := by
    have hh : ε ≤ 1/(k : ℝ) := (le_div_iff₀ hkR).mpr (by linarith [(lt_div_iff₀ hε).mp hkε])
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ hε.le hh d
  let T := Finset.univ.image B.part
  let K := (L.erase A) ∪ T
  have hT {C : Finset V} : C ∈ T ↔ ∃ i, B.part i = C := by simp [T]
  have hTc : T.card = k := by
    rw [Finset.card_image_of_injective _ (positive_parts_injective hBn B.disjoint)]
    simp
  have hdT : Disjoint (L.erase A) T := by
    apply Finset.disjoint_left.mpr
    intro C hC hCT
    obtain ⟨i, rfl⟩ := hT.mp hCT
    obtain ⟨z,hz⟩ := hBn i
    have hp := hL.2.1 hA (Finset.mem_erase.mp hC).2 (Finset.mem_erase.mp hC).1.symm
    exact Finset.disjoint_left.mp hp.1 (B.sub i hz) hz
  have hK : valid K := by
    refine ⟨?_, ?_, ?_⟩
    · intro C hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact hL.1 _ (Finset.mem_erase.mp hc).2
      obtain ⟨i, rfl⟩ := hT.mp hc
      refine ⟨(B.sub i).trans (hL.1 A hA).1, ?_⟩
      calc
        q^2*W = q*(q*W) := by ring
        _ ≤ (1/(k : ℝ)^d)*(A.card : ℝ) :=
          mul_le_mul hr hqA (by positivity) (by positivity)
        _ ≤ _ := (one_div_mul_eq_div _ _).le.trans (hB i)
    · intro C hc D hd hne
      have mixed {C D : Finset V} (hc : C ∈ L.erase A) (hd : D ∈ T) :
          LayoutPair G (x*W^2) C D := by
        obtain ⟨i, rfl⟩ := hT.mp hd
        exact (hL.2.1 hA (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hc).1.symm).mono_left
          (B.sub i) |>.symm
      rcases Finset.mem_union.mp hc with hc | hc <;> rcases Finset.mem_union.mp hd with hd | hd
      · exact hL.2.1 (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hd).2 hne
      · exact mixed hc hd
      · exact (mixed hd hc).symm
      · obtain ⟨i, rfl⟩ := hT.mp hc
        obtain ⟨j, rfl⟩ := hT.mp hd
        have hij : i ≠ j := fun h => hne (congrArg B.part h)
        refine ⟨B.disjoint hij, ?_⟩
        rcases B.restricted i j hij with h | h
        · exact Or.inl h
        · apply Or.inr
          have hcap (i : Fin k) : ((B.part i).card : ℝ) ≤ W := by
            dsimp [W]
            exact_mod_cast Finset.card_le_card ((B.sub i).trans (hL.1 A hA).1)
          rw [sq, ← mul_assoc]
          exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hcap i) hx.le) (hcap j)
            (by positivity) (by positivity))
    · change W^a ≤ ∑ C ∈ (L.erase A) ∪ T, (C.card : ℝ)^a
      rw [Finset.sum_union hdT]
      have hs := block_rpow_mass hd (show 0 < k by omega) hB
      have hi : (∑ C ∈ T, (C.card : ℝ)^a) = ∑ i, ((B.part i).card : ℝ)^a := by
        dsimp [T]
        exact Finset.sum_image (positive_parts_injective hBn B.disjoint).injOn
      rw [hi]
      have h₀ := hL.2.2
      have he := Finset.sum_erase_add (s := L) (a := A) (f := fun C => (C.card : ℝ)^a) hA
      change (A.card : ℝ)^a ≤ ∑ i, ((B.part i).card : ℝ)^a at hs
      linarith
  have hc : K.card = L.card-1+k := by
    dsimp [K]
    rw [Finset.card_union_of_disjoint hdT, Finset.card_erase_of_mem hA, hTc]
  have hmax := hLmax K (hSmem.mpr hK)
  omega

end FivePath

namespace FivePath

def StrongSplit {V : Type*} (G : SimpleGraph V) (U : Finset V) (E : ℕ) (y : ℝ) : Prop :=
  (∃ S : Finset V, S ⊆ U ∧ y^E*(U.card : ℝ) ≤ S.card ∧ DegreeBound G S (y^2)) ∨
  (∃ k : ℕ, 2 ≤ k ∧ 1 ≤ y*(k : ℝ) ∧ ∃ P : CompleteBlockade G U k,
    ∀ i, y^E*(U.card : ℝ) ≤ (P.part i).card) ∨
  ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧ Disjoint X Y ∧
    y^E*(U.card : ℝ) ≤ X.card ∧ (1-3*y)*(U.card : ℝ) ≤ Y.card ∧ Anticomplete G X Y

theorem second_split :
    ∃ E : ℕ, 1 ≤ E ∧ ∀ {V : Type} (G : SimpleGraph V), HouseFree G →
      ∀ (U : Finset V) (y : ℝ), 0 < y → y ≤ 1/256 →
        1 ≤ y^E*(U.card : ℝ) → DegreeBound G U y → StrongSplit G U E y := by
  classical
  obtain ⟨d,hd,hsplit⟩ := first_blockade
  let D := 6*d*d
  let E := 4*D+9
  refine ⟨E,by dsimp [E]; omega,?_⟩
  intro V G hfree U y hy hy1 hu hdeg
  let W : ℝ := U.card
  let ε := y^4
  let X := ε^D*W
  let k := ⌈1/ε⌉₊
  let m := ⌊X/2⌋₊
  let p := ε^2
  let q := ε^d
  let r := ⌈p*(m:ℝ)⌉₊
  have hd0 : 0 < d := by omega
  have hy2 : y ≤ 1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεy : ε ≤ y := by
    dsimp [ε]
    exact (pow_le_pow_of_le_one hy.le hy2 (by decide : 1 ≤ 4)).trans_eq (pow_one _)
  have hε1 : ε ≤ 1/256 := hεy.trans hy1
  have hε2 : ε ≤ 1 := by linarith
  have hW : 0 < W := by
    by_contra! h
    have hp : y^E*W ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hE : y^E*W = y*(p*X) := by
    have h1 : ε^D = y^(4*D) := (pow_mul y 4 D).symm
    have h2 : p = y^8 := by dsimp [p,ε]; rw [← pow_mul]
    rw [show E = 4*D+8+1 from rfl, pow_succ, pow_add, h2, show X = ε^D*W from rfl, h1]
    ring
  have hX : 4 ≤ X := by
    have hp : p ≤ 1 := pow_le_one₀ hε.le hε2
    have hle : y*(p*X) ≤ (1/4 : ℝ)*X := by
      have h' : y*p ≤ 1/4 := by
        have h'' := mul_le_mul_of_nonneg_left hp hy.le
        linarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ X)
    nlinarith only [hle, hE, hu]
  have hX1 : 1 ≤ X := by linarith
  have hwidth : y^E*W ≤ p*X/32 := by
    rw [hE]
    have h' : y ≤ 1/32 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ p*X)]
  have hmUp : (m:ℝ) ≤ X/2 := Nat.floor_le (by positivity)
  have hmLow : X/4 ≤ (m:ℝ) := by
    have hh := Nat.lt_floor_add_one (X/2)
    change X/2 < (m:ℝ)+1 at hh
    linarith
  have hm : 0 < m := by
    have hh : (0:ℝ) < m := by linarith
    exact_mod_cast hh
  have hkLow : (1:ℝ) ≤ (k:ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil _)
  have hkUp : (k:ℝ)*ε ≤ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 1/ε by positivity)
    change (k:ℝ) < 1/ε+1 at h
    have hh := mul_lt_mul_of_pos_right h hε
    have he : (1/ε+1)*ε = 1+ε := by field_simp
    rw [he] at hh
    linarith
  have hk : 2 ≤ k := by
    have hh : (2:ℝ) ≤ k := by
      apply le_of_mul_le_mul_right ?_ hε
      linarith
    exact_mod_cast hh
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hky : (1:ℝ) ≤ y*(k:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hεy hkR.le
    linarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hkp : (k:ℝ)*p ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_right hkUp hε.le
    dsimp [p]
    nlinarith
  obtain ⟨B,hB⟩ := first_to_long U hd0 hε hε1 (show (0:ℝ)<U.card from hW)
    (fun A hA hAc => by
      have hex : ε^(5*d) ≤ ε := by
        exact (pow_le_pow_of_le_one hε.le hε2 (show 1 ≤ 5*d by omega)).trans_eq (pow_one _)
      have hnum : 5*d*d+d ≤ D := by
        dsimp [D]
        have hh : d ≤ d*d := Nat.le_mul_of_pos_right d hd0
        nlinarith
      have hprod : 1 ≤ (ε^(5*d))^d*(A.card : ℝ) := by
        have hw : X ≤ ε^(5*d*d+d)*W := by
          dsimp [X]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hε.le hε2 hnum) hW.le
        have hh := mul_le_mul_of_nonneg_left hAc (pow_nonneg (pow_nonneg hε.le (5*d)) d)
        rw [← pow_mul, ← mul_assoc, ← pow_add] at hh
        rw [← pow_mul]
        exact hX1.trans (hw.trans hh)
      exact hsplit G hfree A _ (by positivity) (hex.trans hε1) hprod)
  have hBm (i : Fin k) : 2*m ≤ (B.part i).card := by
    have hh : (2:ℝ)*m ≤ (B.part i).card := by linarith [hB i]
    exact_mod_cast hh
  rcases equal_anticonnected_refinement B hk hq hp hm hkp hBm with he | ⟨A,hA,hAs⟩
  · obtain ⟨P,hP⟩ := he
    refine Or.inr (Or.inl ⟨k,hk,hky,P,fun i => ?_⟩)
    refine hwidth.trans (le_trans ?_ (hP i))
    have hkE : k ≤ (2:ℝ)/ε := (le_div_iff₀ hε).mpr hkUp
    have hkSq : (k:ℝ)^2 ≤ (2/ε)^2 := pow_le_pow_left₀ hkR.le hkE 2
    have hkDen : 2*(k:ℝ)^2 ≤ 8/p := calc
      _ ≤ 2*(2/ε)^2 := mul_le_mul_of_nonneg_left hkSq (by norm_num)
      _ = _ := by dsimp [p]; rw [div_pow]; ring
    calc
      p*X/32 = (X/4)/(8/p) := by field_simp; ring
      _ ≤ (m:ℝ)/(8/p) := div_le_div_of_nonneg_right hmLow (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hkDen
  have hr : 0 < r := Nat.one_le_ceil_iff.mpr (by positivity)
  have hrm : r ≤ m := Nat.ceil_le.mpr (mul_le_of_le_one_left (by positivity)
    (show p ≤ 1 from pow_le_one₀ hε.le hε2))
  have hrLower : y^E*W ≤ (r:ℝ) := by
    have ht : p*X/32 ≤ p*(m:ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hmLow hp.le]
    exact hwidth.trans (ht.trans (Nat.le_ceil _))
  have hTotal : (k:ℝ)*r ≤ y^2*W := by
    have htt : (k:ℝ)*r ≤ (k:ℝ)*m := mul_le_mul_of_nonneg_left (by exact_mod_cast hrm) hkR.le
    have hPow : ε^D ≤ y^2*ε := by
      have hD2 : 2 ≤ D := by
        dsimp [D]
        have h : 1 ≤ d*d := Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith
      have hle : ε^D ≤ ε^2 := pow_le_pow_of_le_one hε.le hε2 hD2
      have hh : ε ≤ y^2 := by
        dsimp [ε]
        exact pow_le_pow_of_le_one hy.le hy2 (by decide)
      nlinarith [mul_le_mul_of_nonneg_right hh hε.le]
    apply htt.trans
    apply le_of_mul_le_mul_right ?_ hε
    have h₁ := mul_le_mul_of_nonneg_right hkUp (Nat.cast_nonneg (α := ℝ) m)
    have h₂ := mul_le_mul_of_nonneg_right hPow hW.le
    dsimp [X] at hmUp
    nlinarith only [h₁,h₂,hmUp]
  have hqSmall : 2*(q/p/p/p/p) ≤ y^2 := by
    have hqEq : q/p/p/p/p = ε^(d-8) := by
      have hPow : q = ε^(d-8)*ε^8 := by
        dsimp [q]
        rw [← pow_add]
        congr 1
        omega
      rw [hPow]
      dsimp [p]
      field_simp
    rw [hqEq]
    have hle : ε^(d-8) ≤ ε := (pow_le_pow_of_le_one hε.le hε2 (show 1 ≤ d-8 by omega)).trans_eq (pow_one _)
    have h' : 2*ε ≤ y^2 := by
      dsimp [ε]
      have ht : 2*y^2 ≤ 1 := by
        have h := pow_le_pow_left₀ hy.le (show y ≤ 1/2 by linarith) 2
        have hh : y^2 ≤ (1/4:ℝ) := h.trans_eq (by norm_num)
        linarith
      nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg y)]
    exact (mul_le_mul_of_nonneg_left hle (by norm_num)).trans h'
  have hK : (2:ℝ) ≤ y^2*(y*(k:ℝ)) := by
    apply le_of_mul_le_mul_right ?_ hy
    dsimp [ε] at hkLow
    nlinarith only [hkLow, (show 2*y ≤ 1 by linarith)]
  have hPair : ∀ i j, i ≠ j → PairComplete G (A i) (A j) ∨
      ∀ v ∈ A i, (neighborsIn G v (A j)).card ≤ (q/p/p/p/p)*(r:ℝ) := by
    intro i j hij
    by_cases h : PairComplete G (B.part i) (B.part j)
    · exact Or.inl (fun a ha b hb => h a ((hA i).1 ha) b ((hA j).1 hb))
    · exact Or.inr (hAs i j hij h)
  rcases split_mixed_blocks (show 0<k by omega) hr hfree A
    (fun i => ⟨(hA i).1.trans (B.sub i),(hA i).2⟩)
    (fun i j hij => Disjoint.mono (hA i).1 (hA j).1 (B.disjoint hij))
    hy hy2 (by positivity) (by positivity) hqSmall hK hTotal hdeg hPair with
    ⟨S,hS,hSr,hSd⟩ | ⟨Y,Z,hY,hZ,hYZ,hYr,hZr,hanti⟩
  · exact Or.inl ⟨S,hS,hrLower.trans (by exact_mod_cast hSr),hSd⟩
  · exact Or.inr (Or.inr ⟨Y,Z,hY,hZ,hYZ,hrLower.trans (by exact_mod_cast hYr),hZr,hanti⟩)

end FivePath

namespace FivePath

noncomputable def independenceIn {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  (G.induce (A : Set V)).indepNum

theorem exists_independent_in {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    ∃ S : Finset V, S ⊆ A ∧ G.IsIndepSet (S : Set V) ∧ S.card = independenceIn G A := by
  classical
  obtain ⟨S, hS⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  let val : (A : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨S.map val, ?_, ?_, by simpa [independenceIn] using hS.card_eq⟩
  · intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
    exact u.property
  · intro x hx y hy hxy hxyAdj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact hS.isIndepSet hu hv (fun eq => hxy (congrArg val eq)) hxyAdj

theorem sum_independence_le {V : Type*} [Finite V] {I : Type*} [Fintype I]
    {G : SimpleGraph V} {A : I → Finset V}
    (hD : Pairwise (Function.onFun Disjoint A))
    (hA : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, ¬ G.Adj x y) :
    ∑ i, independenceIn G (A i) ≤ G.indepNum := by
  classical
  choose S hsub hS hcard using fun i => exists_independent_in G (A i)
  let U := Finset.univ.biUnion S
  have hdS : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint S := by
    intro i _ j _ hij
    exact Disjoint.mono (hsub i) (hsub j) (hD hij)
  have hU : G.IsIndepSet (U : Set V) := by
    intro x hx y hy hxy
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hS i hx hy hxy
    · exact hA i j hij x (hsub i hx) y (hsub j hy)
  have hu := hU.card_le_indepNum
  change (Finset.univ.biUnion S).card ≤ G.indepNum at hu
  simpa only [Finset.card_biUnion hdS, hcard] using hu

noncomputable def profile {V : Type*} (G : SimpleGraph V) : ℝ :=
  (G.indepNum : ℝ) * G.cliqueNum

@[simp] theorem profile_compl {V : Type*} (G : SimpleGraph V) :
    profile Gᶜ = profile G := by
  simp [profile, mul_comm]

def Critical {V : Type*} [Fintype V] (G : SimpleGraph V) (τ : ℝ) : Prop :=
  profile G < (Fintype.card V : ℝ) ^ τ ∧
    ∀ A : Finset V, A.card < Fintype.card V →
      (A.card : ℝ) ^ τ ≤ profile (G.induce (A : Set V))

theorem critical_compl {V : Type*} [Fintype V] {G : SimpleGraph V} {τ : ℝ}
    (hG : Critical G τ) : Critical Gᶜ τ := by
  refine ⟨by simpa using hG.1, fun A hA => ?_⟩
  have h : Gᶜ.induce (A : Set V) = (G.induce (A : Set V))ᶜ := by
    ext x y
    change ((x : V) ≠ (y : V) ∧ ¬ G.Adj x y) ↔ x ≠ y ∧ ¬ G.Adj x y
    exact and_congr_left' (not_congr Subtype.val_injective.eq_iff)
  simpa only [h, profile_compl] using hG.2 A hA

private theorem cliqueNum_one_le {V : Type*} [Finite V] (G : SimpleGraph V) (x : V) :
    1 ≤ G.cliqueNum := by
  classical
  have h : G.IsClique (({x} : Finset V) : Set V) := by simp
  simpa using h.card_le_cliqueNum

private theorem profile_one_le {V : Type*} [Finite V] (G : SimpleGraph V) (x : V) :
    1 ≤ profile G := by
  classical
  have hc := cliqueNum_one_le G x
  have hi := cliqueNum_one_le Gᶜ x
  rw [cliqueNum_compl] at hi
  unfold profile
  have hc' : (1 : ℝ) ≤ G.cliqueNum := by exact_mod_cast hc
  have hi' : (1 : ℝ) ≤ G.indepNum := by exact_mod_cast hi
  simpa using mul_le_mul hi' hc' (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

private theorem profile_ge_indepNum {V : Type*} [Finite V] {G : SimpleGraph V}
    (x : V) : (G.indepNum : ℝ) ≤ profile G := by
  have h : (1 : ℝ) ≤ (G.cliqueNum : ℝ) := by exact_mod_cast cliqueNum_one_le G x
  exact le_mul_of_one_le_right (by positivity) h

private theorem exists_greedy_independent {V : Type*} (G : SimpleGraph V) {D : ℝ}
    (A : Finset V) (hA : ∀ x ∈ A, (neighborsIn G x A).card ≤ D) :
    ∃ I : Finset V, I ⊆ A ∧ G.IsIndepSet (I : Set V) ∧ (A.card : ℝ) ≤ (D+1) * I.card := by
  classical
  have build (n : ℕ) : ∀ U : Finset V, U ⊆ A → U.card = n →
      ∃ I : Finset V, I ⊆ U ∧ G.IsIndepSet (I : Set V) ∧
        (U.card : ℝ) ≤ (D+1) * I.card := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hUA hUn
      by_cases hU : U.Nonempty
      swap
      · have hu := Finset.not_nonempty_iff_eq_empty.mp hU
        subst U
        exact ⟨∅, Finset.empty_subset _, by simp⟩
      obtain ⟨x, hx⟩ := hU
      let N := insert x (neighborsIn G x U)
      let R := U \ N
      have hNU : N ⊆ U := Finset.insert_subset_iff.mpr
        ⟨hx, fun _ hy => (mem_neighborsIn.mp hy).1⟩
      have hxN : x ∈ N := Finset.mem_insert_self _ _
      have hcount := Finset.card_sdiff_add_card_eq_card hNU
      change R.card + N.card = U.card at hcount
      have hnpos := Finset.card_pos.mpr ⟨x, hxN⟩
      have hRsize : R.card < n := by omega
      have hRU : R ⊆ U := Finset.sdiff_subset
      obtain ⟨I, hIR, hIi, hI⟩ := ih R.card hRsize R (hRU.trans hUA) rfl
      have hxI : x ∉ I := fun h => (Finset.mem_sdiff.mp (hIR h)).2 hxN
      have hNX : ∀ y ∈ I, ¬ G.Adj x y := fun y hy he =>
        (Finset.mem_sdiff.mp (hIR hy)).2
          (Finset.mem_insert_of_mem (mem_neighborsIn.mpr ⟨hRU (hIR hy), he⟩))
      refine ⟨insert x I, Finset.insert_subset_iff.mpr ⟨hx, hIR.trans hRU⟩, ?_, ?_⟩
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with hye | hyI <;>
          rcases Finset.mem_insert.mp hz with hze | hzI
        · exact (hyz (hye.trans hze.symm)).elim
        · exact hye.symm ▸ hNX z hzI
        · exact hze.symm ▸ reverse_not_adj (hNX y hyI)
        · exact hIi hyI hzI hyz
      · have hN' : (N.card : ℝ) ≤ D+1 := by
          dsimp [N]
          rw [Finset.card_insert_of_notMem (by simp)]
          push_cast
          have hle : ((neighborsIn G x U).card : ℝ) ≤ (neighborsIn G x A).card := by
            exact_mod_cast Finset.card_le_card (neighborsIn_mono hUA)
          linarith [hle.trans (hA x (hUA hx))]
        have he : (R.card : ℝ) + N.card = U.card := by exact_mod_cast hcount
        rw [Finset.card_insert_of_notMem hxI]
        push_cast
        linarith
  exact build A.card A (Finset.Subset.refl _) rfl

def Restricted {V : Type*} (G : SimpleGraph V) (A : Finset V) (x : ℝ) : Prop :=
  (∀ v ∈ A, (neighborsIn G v A).card ≤ x * (A.card : ℝ)) ∨
  (∀ v ∈ A, (neighborsIn Gᶜ v A).card ≤ x * (A.card : ℝ))

structure HomogeneousBlockade {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  part : Fin k → Finset V
  disjoint : Pairwise (Function.onFun Disjoint part)
  homogeneous :
    (∀ i j, i ≠ j → ∀ x ∈ part i, ∀ y ∈ part j, G.Adj x y) ∨
    (∀ i j, i ≠ j → ∀ x ∈ part i, ∀ y ∈ part j, ¬ G.Adj x y)

def ProfileAlternative (a b : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), PathFree G →
    ∀ x : ℝ, 0 < x → x < b →
      (∃ A : Finset V, x^a * (Fintype.card V : ℝ) ≤ A.card ∧ Restricted G A x) ∨
      ∃ k ≥ (2 : ℕ), ∃ B : HomogeneousBlockade G k,
        ∀ i, (Fintype.card V : ℝ) / (k : ℝ)^a ≤ ((B.part i).card : ℝ)

private theorem blockade_part_proper {V : Type*} [Fintype V] {k : ℕ} (hk : 2 ≤ k)
    {A : Fin k → Finset V} (hdis : Pairwise (Function.onFun Disjoint A))
    (hn : ∀ i, (A i).Nonempty) (i : Fin k) : (A i).card < Fintype.card V := by
  classical
  have hntr : 1 < Fintype.card (Fin k) := by simp; omega
  have : Nontrivial (Fin k) := Fintype.one_lt_card_iff_nontrivial.mp hntr
  obtain ⟨j, hij⟩ := exists_ne i
  obtain ⟨v, hv⟩ := hn j
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  exact ⟨Finset.subset_univ _, fun h => Finset.disjoint_left.mp (hdis hij.symm)
    (h (Finset.mem_univ v)) hv⟩

private theorem blockade_profile {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a τ M : ℝ} (hτ : 0 < τ) (haτ : a * τ ≤ 1) (hM : 0 < M)
    (hn : (0 : ℝ) < Fintype.card V) {k : ℕ} (hk : 2 ≤ k)
    (B : HomogeneousBlockade G k)
    (hwidth : ∀ i, (Fintype.card V : ℝ) / (k : ℝ)^a ≤ ((B.part i).card : ℝ))
    (hInd : ∀ A : Finset V, A.card < Fintype.card V →
      (A.card : ℝ)^τ / M ≤ profile (G.induce (A : Set V))) :
    (Fintype.card V : ℝ)^τ / M ≤ profile G := by
  classical
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hnonempty (i : Fin k) : (B.part i).Nonempty := by
    have hp : (0 : ℝ) < (B.part i).card := (by positivity : 0 < (Fintype.card V : ℝ)/(k : ℝ)^a).trans_le (hwidth i)
    exact Finset.card_pos.mp (by exact_mod_cast hp)
  have core (H : SimpleGraph V) (hh : ∀ i j, i ≠ j → ∀ x ∈ B.part i, ∀ y ∈ B.part j, ¬ H.Adj x y)
      (hIndH : ∀ A : Finset V, A.card < Fintype.card V →
        (A.card : ℝ)^τ / M ≤ profile (H.induce (A : Set V))) :
      (Fintype.card V : ℝ)^τ / M ≤ profile H := by
    have hsum : (∑ i, (independenceIn H (B.part i) : ℝ)) ≤ H.indepNum := by
      exact_mod_cast sum_independence_le B.disjoint hh
    have hindiv (i : Fin k) :
        ((Fintype.card V : ℝ)/(k : ℝ)^a)^τ / M ≤
          (independenceIn H (B.part i) : ℝ) * H.cliqueNum := by
      calc
        _ ≤ ((B.part i).card : ℝ)^τ / M := div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) (hwidth i) hτ.le) hM.le
        _ ≤ profile (H.induce (B.part i : Set V)) :=
          hIndH _ (blockade_part_proper hk B.disjoint hnonempty i)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast H.cliqueNum_induce_le (B.part i : Set V))
          (by positivity)
    have hcomp :
        (k : ℝ) * (((Fintype.card V : ℝ)/(k : ℝ)^a)^τ / M) ≤ profile H := by
      have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hindiv i
      rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hsum (by positivity))
    have hpower :
        (k : ℝ) * (((Fintype.card V : ℝ)/(k : ℝ)^a)^τ / M) =
          (Fintype.card V : ℝ)^τ / M * (k : ℝ)^(1-a*τ) := by
      rw [Real.div_rpow hn.le (by positivity), ← Real.rpow_mul hk0.le,
        Real.rpow_sub hk0, Real.rpow_one]
      ring
    rw [hpower] at hcomp
    exact (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hk1 (by linarith))).trans hcomp
  rcases B.homogeneous with h | h
  · rw [← profile_compl (G := G)]
    apply core Gᶜ (fun i j hij x hx y hy he => ((G.compl_adj x y).mp he).2 (h i j hij x hx y hy))
    intro A hA
    have eq : Gᶜ.induce (A : Set V) = (G.induce (A : Set V))ᶜ := by
      ext x y
      change ((x : V) ≠ (y : V) ∧ ¬ G.Adj x y) ↔ x ≠ y ∧ ¬ G.Adj x y
      exact and_congr_left' (not_congr Subtype.val_injective.eq_iff)
    simpa only [eq, profile_compl] using hInd A hA
  · exact core G h hInd

theorem finish_from_alternative {a b : ℝ} (ha : 1 ≤ a) (hb : 0 < b)
    (halt : ProfileAlternative a b) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound (pathGraph 5)
      (fun n : ℕ => (n : ℝ)^c) := by
  classical
  let s : ℝ := 1 / (a+1)
  have ha1 : 0 < a+1 := by linarith
  have hs : 0 < s := by positivity
  have hsa : (a+1)*s = 1 := by dsimp [s]; field_simp
  have hsa' : a*s ≤ 1 := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 + (1/b) ^ (a+1))
  have hN2 : (2 : ℝ) ≤ N := by linarith [Real.rpow_nonneg (by positivity : 0 ≤ 1/b) (a+1)]
  have hN0 : (0 : ℝ) < N := by linarith
  have build (n : ℕ) : ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → PathFree G → (n : ℝ)^s / N ≤ profile G := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G hn hfree
      by_cases hn0 : n = 0
      · rw [hn0, Nat.cast_zero, Real.zero_rpow hs.ne', zero_div]
        unfold profile
        positivity
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      have hnV : 0 < Fintype.card V := by rw [hn]; exact Nat.pos_of_ne_zero hn0
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hnV
      by_cases hsmall : n ≤ N
      · have hh : (n : ℝ)^s ≤ N := calc
          _ ≤ (n : ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn1 hs1
          _ = _ := Real.rpow_one _
          _ ≤ _ := by exact_mod_cast hsmall
        exact ((div_le_one hN0).mpr hh).trans (profile_one_le G v)
      let w := (n : ℝ)^s
      let x := (n : ℝ)^(-s)
      have hw : 0 < w := Real.rpow_pos_of_pos hnpos s
      have hx : 0 < x := Real.rpow_pos_of_pos hnpos (-s)
      have hxw : x*w = 1 := by
        dsimp [x, w]
        rw [← Real.rpow_add hnpos, neg_add_cancel, Real.rpow_zero]
      have hxb : x < b := by
        have hnl : (N : ℝ) < n := by exact_mod_cast (lt_of_not_ge hsmall)
        have hbig : (1/b)^(a+1) < (n : ℝ) := by linarith
        have hw' : 1/b < w := by
          have hh := Real.rpow_lt_rpow (by positivity) hbig hs
          rw [← Real.rpow_mul (by positivity), hsa, Real.rpow_one] at hh
          exact hh
        apply (mul_lt_mul_iff_right₀ hw).mp
        rw [mul_comm w x, hxw]
        have h := (div_lt_iff₀ hb).mp hw'
        simpa [mul_comm] using h
      have hwidth : x^a * (n : ℝ) = w := by
        dsimp [x, w]
        rw [← Real.rpow_mul hnpos.le]
        conv_lhs =>
          arg 2
          rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnpos]
        congr 1
        nlinarith
      rcases halt G hfree x hx hxb with ⟨A, hA, hside⟩ | ⟨k, hk, B, hB⟩
      · have hA' : w ≤ A.card := by simpa [hn, hwidth] using hA
        have hApos : (0 : ℝ) < A.card := hw.trans_le hA'
        have hD : (1 : ℝ) ≤ x * (A.card : ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hA' hx.le
          rwa [hxw] at hh
        have core (H : SimpleGraph V)
            (hHR : ∀ v ∈ A, (neighborsIn H v A).card ≤ x * (A.card : ℝ)) :
            w / 2 ≤ profile H := by
          obtain ⟨I, _, hI, hgreedy⟩ := exists_greedy_independent H A hHR
          have hcount : (1 : ℝ) ≤ 2*x*(I.card : ℝ) := by
            have hh := mul_le_mul_of_nonneg_right (show x*(A.card : ℝ)+1 ≤ 2*x*A.card by linarith)
              (Nat.cast_nonneg (α := ℝ) I.card)
            apply (mul_le_mul_iff_left₀ hApos).mp
            nlinarith [hgreedy.trans hh]
          have hI' : w / 2 ≤ (I.card : ℝ) := by
            have hh := mul_le_mul_of_nonneg_right hcount hw.le
            nlinarith [mul_le_mul_of_nonneg_right (le_of_eq hxw) (Nat.cast_nonneg (α := ℝ) I.card)]
          exact hI'.trans ((by exact_mod_cast hI.card_le_indepNum : (I.card : ℝ) ≤ H.indepNum).trans
            (profile_ge_indepNum v))
        have hresult : w/2 ≤ profile G := by
          rcases hside with hG | hGc
          · exact core G hG
          · simpa using core Gᶜ hGc
        exact (div_le_div_of_nonneg_left hw.le (by norm_num) hN2).trans hresult
      · rw [← hn]
        apply blockade_profile hs hsa' hN0 (by simpa [hn] using hnpos) hk B hB
        intro A hA
        exact ih A.card (by simpa [hn] using hA) (G.induce (A : Set V))
          (Fintype.card_coe A) (free_of_embedding hfree (Embedding.induce (A : Set V)))
  obtain ⟨M, hM⟩ := exists_nat_gt ((N : ℝ)^(2/s))
  refine ⟨s/4, by positivity, Filter.eventually_atTop.mpr ⟨M, fun n hn G hNfree => ?_⟩⟩
  have hfree : PathFree G := by
    rintro ⟨f⟩
    apply hNfree
    refine ⟨f.toEmbedding, ?_⟩
    ext x y
    exact f.map_adj_iff.symm
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hNth : (N : ℝ) ≤ (n : ℝ)^(s/2) := by
    have hh : (N : ℝ)^(2/s) ≤ n := hM.le.trans (by exact_mod_cast hn)
    have hpow := Real.rpow_le_rpow (by positivity) hh (by positivity : 0 ≤ s/2)
    rw [← Real.rpow_mul hN0.le, show (2/s)*(s/2) = 1 by field_simp, Real.rpow_one] at hpow
    exact hpow
  have hprof := build n G (Fintype.card_fin n) hfree
  have hsq : ((n : ℝ)^(s/2))^2 = (n : ℝ)^s := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR]
    congr 1
    push_cast
    ring
  have hprof' : (n : ℝ)^(s/2) ≤ profile G := by
    apply le_trans ?_ hprof
    apply (le_div_iff₀ hN0).mpr
    rw [← hsq, sq]
    exact mul_le_mul_of_nonneg_left hNth (by positivity)
  have hsq' : ((n : ℝ)^(s/4))^2 = (n : ℝ)^(s/2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR]
    congr 1
    push_cast
    ring
  by_contra! h
  rw [← hsq', sq, profile] at hprof'
  exact hprof'.not_gt (mul_lt_mul'' h.1 h.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end FivePath

namespace FivePath

private def complete_homogeneous {V : Type*} {G : SimpleGraph V} {U : Finset V} {k : ℕ}
    (C : CompleteBlockade G U k) : HomogeneousBlockade G k where
  part := C.part
  disjoint := C.disjoint
  homogeneous := Or.inl fun i j hij => by
    classical
    rcases lt_or_gt_of_ne hij with h | h
    · exact C.ordered i j h
    · exact pair_complete_symm (C.ordered j i h)

private def anticomplete_homogeneous {V : Type*} {G : SimpleGraph V} {U : Finset V} {k : ℕ}
    (C : OrderedBlockade U (Anticomplete G) k) : HomogeneousBlockade G k where
  part := C.part
  disjoint := C.disjoint
  homogeneous := Or.inr fun i j hij => by
    classical
    rcases lt_or_gt_of_ne hij with h | h
    · exact C.ordered i j h
    · exact fun x hx y hy => reverse_not_adj (C.ordered j i h y hy x hx)

private def HomogeneousBlockade.compl {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (C : HomogeneousBlockade G k) : HomogeneousBlockade Gᶜ k where
  part := C.part
  disjoint := C.disjoint
  homogeneous := by
    rcases C.homogeneous with h | h
    · exact Or.inr fun i j hij x hx y hy he => ((G.compl_adj x y).mp he).2 (h i j hij x hx y hy)
    · exact Or.inl fun i j hij x hx y hy =>
        (G.compl_adj x y).mpr ⟨fun he => Finset.disjoint_left.mp (C.disjoint hij) hx (he ▸ hy),
          h i j hij x hx y hy⟩

private theorem second_growth {V : Type} {G : SimpleGraph V} {U : Finset V}
    {E : ℕ} {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/256)
    (hU : 2 ≤ y^E*(U.card : ℝ)) (hdeg : DegreeBound G U (y/2))
    (hstep : ∀ R : Finset V, R ⊆ U → 1 ≤ y^E*(R.card : ℝ) →
      DegreeBound G R y → StrongSplit G R E y) :
    (∃ S : Finset V, S ⊆ U ∧ y^E*(U.card : ℝ)/2 ≤ S.card ∧ DegreeBound G S (y^2)) ∨
    ∃ k : ℕ, 2 ≤ k ∧ 1 ≤ y*(k : ℝ)^5 ∧ ∃ C : HomogeneousBlockade G k,
      ∀ i, y^E*(U.card : ℝ)/2 ≤ (C.part i).card := by
  classical
  let W : ℝ := U.card
  let m := ⌊1/(6*y)⌋₊
  have hW : 0 < W := by
    by_contra! h
    have hh : y^E*W ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hm : 2 ≤ m := (Nat.le_floor_iff' (by decide : (2:ℕ) ≠ 0)).mpr
    ((le_div_iff₀ (show 0 < 6*y by positivity)).mpr (by norm_num; linarith))
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmUp : (m:ℝ)*(6*y) ≤ 1 := (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hmLo : 1 ≤ 12*y*(m:ℝ) := by
    have h := (div_lt_iff₀ (show 0 < 6*y by positivity)).mp (Nat.lt_floor_add_one (1/(6*y)))
    change 1 < ((m:ℝ)+1)*(6*y) at h
    linarith
  let T : Prop := ∃ S : Finset V, S ⊆ U ∧ y^E*W/2 ≤ S.card ∧ DegreeBound G S (y^2)
  let B : Prop := ∃ k : ℕ, 2 ≤ k ∧ 1 ≤ y*(k:ℝ)^5 ∧ ∃ C : HomogeneousBlockade G k,
    ∀ i, y^E*W/2 ≤ (C.part i).card
  have hGrow := grow_blockade (U := U) (P := Anticomplete G) (stop := T ∨ B)
    (m := m) (loss := 3*y*W) (width := y^E*W/2) (by positivity)
    (fun _ _ _ hC hP a ha b hb => hP a ha b (hC hb))
  have hc := hGrow fun R hRU hR => by
    have hHalf : W/2 ≤ (R.card:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hmUp hW.le]
    have hSize : 1 ≤ y^E*(R.card:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hHalf (pow_nonneg hy.le E)]
    have hDeg : DegreeBound G R y := by
      intro v hv
      have hh : ((neighborsIn G v R).card:ℝ) ≤ (neighborsIn G v U).card := by
        exact_mod_cast Finset.card_le_card (neighborsIn_mono hRU)
      have hh' := hdeg v (hRU hv)
      nlinarith [mul_le_mul_of_nonneg_left hHalf hy.le]
    have hWide : y^E*W/2 ≤ y^E*(R.card:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hHalf (pow_nonneg hy.le E)]
    rcases hstep R hRU hSize hDeg with hs | hb | hpair
    · obtain ⟨S,hSR,hSw,hSd⟩ := hs
      exact Or.inl (Or.inl ⟨S,hSR.trans hRU,hWide.trans hSw,hSd⟩)
    · obtain ⟨k,hk,hK,C,hC⟩ := hb
      have hkR : (1:ℝ) ≤ k := by exact_mod_cast (show 1≤k by omega)
      have hkpow : (k:ℝ) ≤ (k:ℝ)^5 := (pow_one _).symm.le.trans
        (pow_le_pow_right₀ hkR (by decide : 1≤5))
      exact Or.inl (Or.inr ⟨k,hk,hK.trans (mul_le_mul_of_nonneg_left hkpow hy.le),
        complete_homogeneous C, fun i => hWide.trans (hC i)⟩)
    · obtain ⟨X,Y,hX,hY,hXY,hXc,hYc,hAnti⟩ := hpair
      refine Or.inr ⟨X,Y,hX,hY,hXY,hWide.trans hXc,?_,hAnti⟩
      have hRW : (R.card:ℝ) ≤ W := by dsimp [W]; exact_mod_cast Finset.card_le_card hRU
      nlinarith [mul_le_mul_of_nonneg_left hRW (show 0 ≤ 3*y by positivity)]
  rcases hc with he | ⟨C,hC⟩
  · exact he
  have hmPow : (12:ℝ)*(m:ℝ) ≤ (m:ℝ)^5 := by
    rw [pow_succ (m:ℝ) 4]
    have h : 12 ≤ (m:ℝ)^4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hmR 4
      norm_num at hh
      linarith
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hmY : 1 ≤ y*(m:ℝ)^5 := by
    have hh := mul_le_mul_of_nonneg_left hmPow hy.le
    linarith
  exact Or.inr ⟨m,hm,hmY,anticomplete_homogeneous C,hC⟩

private theorem squared_scale_width {E : ℕ} {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/256) :
    (2*y^2)^(2*E+2) ≤ y^(E+(2*E+2))/2 := by
  let T := 2*E+2
  let L := E+2
  have hL : y^L ≤ 1/(2:ℝ)^(2*L) := by
    have hy' : y ≤ (1/(2:ℝ))^2 := by norm_num; linarith
    have hh := pow_le_pow_left₀ hy.le hy' L
    rw [← pow_mul,div_pow,one_pow] at hh
    exact hh
  have hpow : 2^(T+1)*y^L ≤ (1:ℝ) := by
    have hden : (2:ℝ)^(T+1) ≤ (2:ℝ)^(2*L) :=
      pow_le_pow_right₀ (by norm_num) (by dsimp [T,L]; omega)
    calc
      _ ≤ (2:ℝ)^(T+1)*(1/(2:ℝ)^(2*L)) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ (2:ℝ)^(2*L)*(1/(2:ℝ)^(2*L)) :=
        mul_le_mul_of_nonneg_right hden (by positivity)
      _ = 1 := by field_simp
  change (2*y^2)^T ≤ y^(E+T)/2
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have heExp : 2*T = L+(E+T) := by dsimp [L,T]; omega
  have he : (2*y^2)^T*2 = ((2:ℝ)^(T+1)*y^L)*y^(E+T) := calc
    _ = ((2:ℝ)^T * y^(2*T))*2 := by rw [mul_pow,← pow_mul]
    _ = (2:ℝ)^(T+1)*y^(2*T) := by rw [pow_succ (2:ℝ) T]; ring
    _ = _ := by rw [heExp,pow_add y L (E+T)]; ring
  rw [he]
  simpa using mul_le_mul_of_nonneg_right hpow (pow_nonneg hy.le _)

private theorem width_of_homogeneous_blocks {k E : ℕ} {y W : ℝ} (hk : 2 ≤ k)
    (hW : 0 ≤ W) (h : 1 ≤ y*(k:ℝ)^5) :
    W/(k:ℝ)^(5*E+1) ≤ y^E*W/2 := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0:ℝ) < k := by linarith
  have h0 : 1/(k:ℝ)^5 ≤ y := (div_le_iff₀ (by positivity)).mpr h
  have h1 := pow_le_pow_left₀ (show 0 ≤ 1/(k:ℝ)^5 by positivity) h0 E
  rw [div_pow,one_pow,← pow_mul] at h1
  have h2 : (2:ℝ)*(k:ℝ)^(5*E) ≤ (k:ℝ)^(5*E+1) := by
    rw [pow_succ]
    simpa only [mul_comm ((k:ℝ)^(5*E)) (k:ℝ)] using
      mul_le_mul_of_nonneg_right hk2 (pow_nonneg hkR.le (5*E))
  calc
    _ ≤ W/(2*(k:ℝ)^(5*E)) := div_le_div_of_nonneg_left hW (by positivity) h2
    _ = ((1/(k:ℝ)^(5*E))*W)/2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hW) (by norm_num)

private theorem profile_alternative_exists : ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ ProfileAlternative a b := by
  classical
  obtain ⟨E,hE,hsec⟩ := second_split
  let T := 2*E+2
  let L := 5*(E+T)+1
  let y₀ : ℝ := 1/256
  obtain ⟨δ,hδ,hreg⟩ := sparse_side_in (pathGraph 5)ᶜ (y₀/2) (by norm_num [y₀])
  obtain ⟨D,hD⟩ := pow_unbounded_of_one_lt (32/δ : ℝ) (by norm_num : (1:ℝ)<2)
  have hδ32 : 1/(2:ℝ)^D ≤ δ/32 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^D)).mpr
    linarith [(div_lt_iff₀ hδ).mp hD]
  let a := L+D+2
  let b := min δ (y₀/2)
  have ha : 1 ≤ a := by dsimp [a,L]; omega
  have hab : 2*T+1 ≤ a := by dsimp [a,L]; omega
  have hax : E+T+2 ≤ a := by dsimp [a,L]; omega
  refine ⟨(a:ℝ),b,by exact_mod_cast ha,
    lt_min hδ (by norm_num [y₀]),?_⟩
  intro V _ G hfree x hx hxb
  let H := Gᶜ
  have hHF : HouseFree H := free_compl.mpr hfree
  let U : Finset V := Finset.univ
  let W : ℝ := Fintype.card V
  have hWc : (U.card : ℝ) = W := by simp [U,W]
  have hxδ : x ≤ δ := hxb.le.trans (min_le_left _ _)
  have hxy₀ : x ≤ y₀ := by
    have hh := hxb.le.trans (min_le_right δ (y₀/2))
    dsimp [y₀] at *
    linarith
  have hx1 : x ≤ 1/2 := by dsimp [y₀] at hxy₀; linarith
  have hxle : x ≤ 1 := by linarith
  by_cases hsmall : x^a*W ≤ 1
  · apply Or.inl
    by_cases he : IsEmpty V
    · exact ⟨∅,by simp,Or.inl (by simp)⟩
    obtain ⟨v⟩ : Nonempty V := not_isEmpty_iff.mp he
    refine ⟨{v},by simpa only [Real.rpow_natCast,Finset.card_singleton,Nat.cast_one] using hsmall,
      Or.inl fun u hu => ?_⟩
    have hu' : u = v := Finset.mem_singleton.mp hu
    subst u
    have he : neighborsIn G v ({v} : Finset V) = ∅ := by
      ext u
      simp only [mem_neighborsIn,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hh⟩
      exact G.irrefl hh
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨R, hRU,hR,hsub⟩ := hreg H hHF U
  rw [hWc] at hR
  have hW0 : 0 < W := by
    by_contra! h
    have hh : x^a*W ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith [lt_of_not_ge hsmall]
  have hxR : x*W ≤ (R.card : ℝ) := (mul_le_mul_of_nonneg_right hxδ hW0.le).trans hR
  have hRlarge : 2 ≤ x^(E+T)*(R.card:ℝ) := by
    have hpow : x^a ≤ x^(E+T+2) := pow_le_pow_of_le_one hx.le hxle hax
    have he : x^(E+T+2)*W ≤ (x^(E+T)*(x*W))/2 := by
      rw [pow_succ x (E+T+1),pow_succ x (E+T)]
      nlinarith [mul_le_mul_of_nonneg_right hx1
        (show 0 ≤ x^(E+T)*x*W by positivity)]
    have hhalf : x^a*W ≤ (x^(E+T)*(R.card:ℝ))/2 :=
      (mul_le_mul_of_nonneg_right hpow hW0.le).trans (he.trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxR (pow_nonneg hx.le (E+T))) (by norm_num)))
    linarith [lt_of_not_ge hsmall]
  rcases hsub with hH | hGc
  swap
  · have hR2 : 2 ≤ R.card := by
      have h' : (2:ℝ) ≤ R.card :=
        hRlarge.trans (mul_le_of_le_one_left (by positivity) (pow_le_one₀ hx.le hxle))
      exact_mod_cast h'
    have hGc' : DegreeBound G R (y₀/2) := by simpa only [H,compl_compl] using hGc
    obtain ⟨A,B,hAR,hBR,hAB,hAs,hBs,hanti⟩ := sparse_path_has_large_pair hfree R hR2
      (fun z hz => (hGc' z hz).trans
        (by dsimp [y₀]; nlinarith [Nat.cast_nonneg (α := ℝ) R.card]))
    let P : Fin 2 → Finset V := ![A,B]
    let C : HomogeneousBlockade G 2 := {
      part := P
      disjoint := fun i j hij => by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hAB
        · exact hAB.symm
        · exact (hij rfl).elim
      homogeneous := Or.inr fun i j hij => by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hanti
        · exact fun b hb a ha => reverse_not_adj (hanti a ha b hb)
        · exact (hij rfl).elim }
    refine Or.inr ⟨2,le_rfl,C,fun i => ?_⟩
    have hD₀ : D ≤ a := by dsimp [a]; omega
    have hWsmall : W/(2:ℝ)^D ≤ (R.card : ℝ)/32 := by
      rw [← one_div_mul_eq_div]
      nlinarith [mul_le_mul_of_nonneg_right hδ32 hW0.le]
    have hf : W/(2:ℝ)^a ≤ (R.card : ℝ)/32 :=
      (div_le_div_of_nonneg_left hW0.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hD₀)).trans hWsmall
    rw [Real.rpow_natCast]
    fin_cases i
    · exact hf.trans hAs
    · exact hf.trans hBs
  have hx2 : x^2 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hxle hx.le]
  obtain ⟨y,hy,F,hFR,hFsize,hFd,hmin⟩ := minimum_degree_scale H R
    (lo := x^2) (hi := y₀) (hx2.trans hxy₀)
    (fun z => z^T) (fun z => z/2) (by fun_prop) (by fun_prop)
    (pow_le_one₀ (by norm_num [y₀]) (by norm_num [y₀])) hH
  have hy0 : 0 < y := (sq_pos_of_pos hx).trans_le hy.1
  have hy1 : y ≤ 1/256 := hy.2
  by_cases hxy : x ≤ y
  swap
  · refine Or.inl ⟨F,?_,Or.inr fun z hz => (hFd z hz).trans ?_⟩
    · rw [Real.rpow_natCast]
      have ha' : x^a ≤ x^(2*T+1) := pow_le_pow_of_le_one hx.le hxle hab
      have hpy := pow_le_pow_left₀ (sq_nonneg x) hy.1 T
      rw [← pow_mul] at hpy
      have ht : x^(2*T+1)*W ≤ y^T*(R.card:ℝ) := by
        rw [pow_succ,mul_assoc]
        exact mul_le_mul hpy hxR (by positivity) (by positivity)
      exact (mul_le_mul_of_nonneg_right ha' hW0.le).trans (ht.trans hFsize)
    · have hh : y/2 ≤ x := by linarith [lt_of_not_ge hxy]
      exact mul_le_mul_of_nonneg_right hh (by positivity)
  have hFlarge : 2 ≤ y^E*(F.card:ℝ) := calc
    _ ≤ x^(E+T)*(R.card:ℝ) := hRlarge
    _ ≤ y^(E+T)*(R.card:ℝ) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hx.le hxy (E+T)) (by positivity)
    _ = y^E*(y^T*(R.card:ℝ)) := by rw [pow_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hFsize (pow_nonneg hy0.le E)
  rcases second_growth hy0 hy1 hFlarge hFd (fun Q _ hQ hdeg =>
    hsec H hHF Q y hy0 hy1 hQ hdeg) with
    ⟨S,hSF,hSsize,hSd⟩ | ⟨k,hk,hY,C,hC⟩
  · exfalso
    have hz := squared_scale_width (E := E) hy0 hy1
    change (2*y^2)^T ≤ y^(E+T)/2 at hz
    have hScale : (2*y^2)^T*(R.card:ℝ) ≤ S.card := calc
      _ ≤ (y^(E+T)/2)*(R.card:ℝ) := mul_le_mul_of_nonneg_right hz (by positivity)
      _ = (y^E*(y^T*(R.card:ℝ)))/2 := by rw [pow_add]; ring
      _ ≤ y^E*(F.card:ℝ)/2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFsize (pow_nonneg hy0.le E)) (by norm_num)
      _ ≤ _ := hSsize
    have hZ : 2*y^2 ∈ Set.Icc (x^2) y₀ := by
      constructor
      · have h := pow_le_pow_left₀ hx.le hxy 2
        nlinarith
      · have h := mul_le_mul_of_nonneg_right (show 2*y ≤ 1 by linarith) hy0.le
        nlinarith [hy.2]
    have hdZ : DegreeBound H S ((2*y^2)/2) := by simpa using hSd
    have hContr := hmin (2*y^2) hZ S (hSF.trans hFR) hScale hdZ
    have hMul := mul_lt_mul_of_pos_right (show 2*y < 1 by linarith) hy0
    nlinarith
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hdk : 1/(k:ℝ)^D ≤ δ := calc
    _ ≤ 1/(2:ℝ)^D := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by norm_num) hk2 D)
    _ ≤ _ := hδ32.trans (by linarith)
  have hδk : 1 ≤ δ*(k:ℝ)^D := (div_le_iff₀ (by positivity)).mp hdk
  have hCL (i : Fin k) : (R.card : ℝ)/(k:ℝ)^L ≤ (C.part i).card := by
    have ht := width_of_homogeneous_blocks (E := E+T) hk
      (Nat.cast_nonneg (α := ℝ) R.card) hY
    apply ht.trans
    have hh := mul_le_mul_of_nonneg_left hFsize (pow_nonneg hy0.le E)
    rw [pow_add]
    linarith [hC i]
  let C' : HomogeneousBlockade G k :=
    ⟨C.part,C.disjoint,by simpa only [H,HomogeneousBlockade.compl,compl_compl] using C.compl.homogeneous⟩
  refine Or.inr ⟨k,hk,C',fun i => ?_⟩
  rw [Real.rpow_natCast]
  have he : W/(k:ℝ)^a ≤ W/(k:ℝ)^(D+L) :=
    div_le_div_of_nonneg_left hW0.le (by positivity)
      (pow_le_pow_right₀ (by linarith) (by dsimp [a]; omega))
  exact he.trans ((rescale_width (k := k) (a := D) (b := L) hk0 hW0.le hR hδk).trans (hCL i))

end FivePath

theorem OMA.solution : type_of% @Erdos61.erdos_61.variants.p5 := by
  obtain ⟨a,b,ha,hb,h⟩ := FivePath.profile_alternative_exists
  exact FivePath.finish_from_alternative ha hb h