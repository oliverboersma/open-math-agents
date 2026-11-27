import FormalConjectures.Arxiv.«2001.02665».RingelConjecture
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Reduction of Kotzig's Conjecture for Large n (Montgomery–Pokrovskiy–Sudakov, arXiv:2001.02665)

Unconditionally proved in this reduction file (zero sorry, zero extra defs):
1. Rosa–Kotzig Cyclic Decomposition Theorem: any tree T with n edges that admits a rainbow
   embedding into the near-distance (ND-)coloured complete graph K_{2n+1} decomposes K_{2n+1}
   into 2n+1 edge-disjoint cyclic shifts f_i(v) = f_0(v) + i.
2. Montgomery's Tree Splitting Lemma (Lemma 3.6 of arXiv:2001.02665): every tree on m vertices
   either has at least m / (6k) leaves or at least m / (6k) vertex-disjoint bare paths of length k.
3. MPS Case Division Lemma (Lemma 3.7 of arXiv:2001.02665): setting L(n) = 2 ^ ⌊√(log₂ n)⌋,
   for all sufficiently large n, every n-edge tree falls into one of the three MPS structural cases:
   - H1 (Case A, not C): pruned core has > n/100 vertices and T has ≥ n / L(n)^6 non-neighbouring
     leaves (a leaf-matching); proved in Sections 4 and 6 of arXiv:2001.02665.
   - H2 (Case B, not C): pruned core has > n/100 vertices and T has ≥ n / (800 L(n))
     vertex-disjoint bare paths of length L(n); proved in Sections 5 and 6 of arXiv:2001.02665.
   - H3 (Case C): removing leaves next to vertices with ≥ L(n)^4 leaf-neighbours leaves ≤ n/100
     vertices; proved deterministically in Section 7 of arXiv:2001.02665.
-/

namespace OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1

open SimpleGraph

/-- MPS Case A (Sections 4 & 6): rainbow embedding in the ND-coloured K_{2n+1} for large n-edge
trees outside Case C that possess at least n / L(n)^6 non-neighbouring leaves (a leaf-matching),
where L(n) = 2 ^ ⌊√(log₂ n)⌋. -/
def H1 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj],
      T.IsTree →
      n / 100 < (Finset.univ.filter (fun w : Fin (n + 1) =>
        ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
          (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 4 ≤
            (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))).card →
      (∃ S : Finset (Fin (n + 1)),
        n / (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 6 ≤ S.card ∧
        (∀ x ∈ S, T.degree x = 1) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ T.Adj x y ∧ ∀ z, ¬ (T.Adj x z ∧ T.Adj y z))) →
      ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
        ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
          (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
          s(u₁, v₁) = s(u₂, v₂)

/-- MPS Case B (Sections 5 & 6): rainbow embedding in the ND-coloured K_{2n+1} for large n-edge
trees outside Case C that possess at least n / (800 L(n)) vertex-disjoint bare paths of length
L(n) = 2 ^ ⌊√(log₂ n)⌋. -/
def H2 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj],
      T.IsTree →
      n / 100 < (Finset.univ.filter (fun w : Fin (n + 1) =>
        ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
          (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 4 ≤
            (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))).card →
      (∃ P : Fin (n / (800 * 2 ^ Nat.sqrt (Nat.log 2 n))) →
          Fin (2 ^ Nat.sqrt (Nat.log 2 n) + 1) → Fin (n + 1),
        (∀ a₁ b₁ a₂ b₂, P a₁ b₁ = P a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂) ∧
        (∀ a (j : Fin (2 ^ Nat.sqrt (Nat.log 2 n))),
          T.Adj (P a j.castSucc) (P a j.succ)) ∧
        (∀ a (j : Fin (2 ^ Nat.sqrt (Nat.log 2 n) + 1)),
          0 < j.val → j.val < 2 ^ Nat.sqrt (Nat.log 2 n) → T.degree (P a j) = 2)) →
      ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
        ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
          (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
          s(u₁, v₁) = s(u₂, v₂)

/-- MPS Case C (Section 7, deterministic): rainbow embedding in the ND-coloured K_{2n+1} for large
n-edge trees whose pruned core (after removing leaves adjacent to vertices with at least L(n)^4
leaf-neighbours) has at most n / 100 vertices, where L(n) = 2 ^ ⌊√(log₂ n)⌋. -/
def H3 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj],
      T.IsTree →
      (Finset.univ.filter (fun w : Fin (n + 1) =>
        ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
          (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 4 ≤
            (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))).card ≤ n / 100 →
      ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
        ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
          (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
          s(u₁, v₁) = s(u₂, v₂)

-- ============================================================================
-- SECTION 1: Rosa–Kotzig Cyclic Shift Decomposition Theorem
-- ============================================================================

section Helpers

private lemma fin_odd_add_self_inj {n : ℕ} {i j : Fin (2 * n + 1)}
    (h : i + i = j + j) : i = j := by
  have hval := congrArg Fin.val h
  simp only [Fin.val_add] at hval
  have hi := i.isLt
  have hj := j.isLt
  ext
  by_cases h1 : i.val + i.val < 2 * n + 1 <;> by_cases h2 : j.val + j.val < 2 * n + 1
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hval
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega

private lemma fin_sub_val_add_symm {n : ℕ} {x y : Fin (2 * n + 1)} (hne : x ≠ y) :
    (x - y).val + (y - x).val = 2 * n + 1 := by
  have h1 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h2 : y - x ≠ 0 := sub_ne_zero.mpr hne.symm
  have h1' : 0 < (x - y).val := Nat.pos_of_ne_zero (fun h => h1 (Fin.ext h))
  have h2' : 0 < (y - x).val := Nat.pos_of_ne_zero (fun h => h2 (Fin.ext h))
  have hsum : (x - y) + (y - x) = 0 := by abel
  have hval := congrArg Fin.val hsum
  simp only [Fin.val_add, Fin.val_zero] at hval
  have hlt1 := (x - y).isLt
  have hlt2 := (y - x).isLt
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hval
  have hk1 : k = 1 := by nlinarith
  rw [hk1, mul_one] at hk
  exact hk

private lemma fin_nd_eq_iff {n : ℕ} {x₁ y₁ x₂ y₂ : Fin (2 * n + 1)}
    (h1 : x₁ ≠ y₁) (h2 : x₂ ≠ y₂)
    (hmin : min (x₁ - y₁).val (y₁ - x₁).val = min (x₂ - y₂).val (y₂ - x₂).val) :
    x₁ - y₁ = x₂ - y₂ ∨ x₁ - y₁ = y₂ - x₂ := by
  have hs1 := fin_sub_val_add_symm h1
  have hs2 := fin_sub_val_add_symm h2
  by_cases ha : (x₁ - y₁).val ≤ (y₁ - x₁).val <;> by_cases hb : (x₂ - y₂).val ≤ (y₂ - x₂).val
  · left; ext; simp only [min_eq_left ha, min_eq_left hb] at hmin; exact hmin
  · right; ext; simp only [min_eq_left ha, min_eq_right (le_of_not_ge hb)] at hmin; exact hmin
  · right; ext; simp only [min_eq_right (le_of_not_ge ha), min_eq_left hb] at hmin; omega
  · left; ext
    simp only [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb)] at hmin
    omega

private lemma rosa_kotzig_cyclic {n : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : T.edgeSet.ncard = n)
    (g : V ↪ Fin (2 * n + 1))
    (hrain : ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
      (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
      s(u₁, v₁) = s(u₂, v₂)) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  let f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)) :=
    fun i => g.trans ⟨(· + i), add_left_injective i⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i v
    simp [f]
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hi hj
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet, SimpleGraph.map_adj] at hi hj
      obtain ⟨u₁, v₁, hT1, hx1, hy1⟩ := hi
      obtain ⟨u₂, v₂, hT2, hx2, hy2⟩ := hj
      simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk] at hx1 hy1 hx2 hy2
      have hdiff : g u₁ - g v₁ = g u₂ - g v₂ := by
        calc g u₁ - g v₁ = (g u₁ + i) - (g v₁ + i) := by abel
          _ = x - y := by rw [hx1, hy1]
          _ = (g u₂ + j) - (g v₂ + j) := by rw [hx2, hy2]
          _ = g u₂ - g v₂ := by abel
      have hsym := hrain u₁ v₁ u₂ v₂ hT1 hT2 (Or.inl hdiff)
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : g u₁ + i = g u₁ + j := hx1.trans hx2.symm
        exact hij (add_left_cancel this)
      · have h1 : g u₁ + i = g v₁ + j := hx1.trans hx2.symm
        have h2 : g v₁ + i = g u₁ + j := hy1.trans hy2.symm
        have hadd : (g u₁ + g v₁) + (i + i) = (g u₁ + g v₁) + (j + j) := by
          calc (g u₁ + g v₁) + (i + i) = (g u₁ + i) + (g v₁ + i) := by abel
            _ = (g v₁ + j) + (g u₁ + j) := by rw [h1, h2]
            _ = (g u₁ + g v₁) + (j + j) := by abel
        exact hij (fin_odd_add_self_inj (add_left_cancel hadd))
  · apply le_antisymm le_top
    intro x y htop
    have hxy : x ≠ y := htop
    rw [SimpleGraph.iSup_adj]
    let col : Sym2 V → ℕ :=
      Sym2.lift ⟨fun u v => min (g u - g v).val (g v - g u).val, fun u v => min_comm _ _⟩
    have hsub : T.edgeFinset.image col ⊆ Finset.Icc 1 n := by
      intro c hc
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        have hne : g u ≠ g v := fun h => he.ne (g.injective h)
        have hsum := fin_sub_val_add_symm hne
        have h1 : 0 < (g u - g v).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hne (Fin.ext h))
        have h2 : 0 < (g v - g u).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hne.symm (Fin.ext h))
        simp only [col, Sym2.lift_mk, Finset.mem_Icc]
        omega
    have hinj : Set.InjOn col (T.edgeFinset : Set (Sym2 V)) := by
      intro e₁ he₁ e₂ he₂ hceq
      induction e₁ using Sym2.ind with
      | _ u₁ v₁ =>
        induction e₂ using Sym2.ind with
        | _ u₂ v₂ =>
          simp only [Finset.mem_coe, mem_edgeFinset, mem_edgeSet] at he₁ he₂
          simp only [col, Sym2.lift_mk] at hceq
          have h1 : g u₁ ≠ g v₁ := fun h => he₁.ne (g.injective h)
          have h2 : g u₂ ≠ g v₂ := fun h => he₂.ne (g.injective h)
          exact hrain u₁ v₁ u₂ v₂ he₁ he₂ (fin_nd_eq_iff h1 h2 hceq)
    have hcard_fin : T.edgeFinset.card = n := by
      rw [← Set.ncard_coe_finset, coe_edgeFinset]
      exact hcard
    have himg : T.edgeFinset.image col = Finset.Icc 1 n := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_image_of_injOn hinj, hcard_fin, Nat.card_Icc]
      omega
    have hmem : min (x - y).val (y - x).val ∈ T.edgeFinset.image col := by
      rw [himg, Finset.mem_Icc]
      have hsum := fin_sub_val_add_symm hxy
      have h1 : 0 < (x - y).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hxy (Fin.ext h))
      have h2 : 0 < (y - x).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hxy.symm (Fin.ext h))
      omega
    obtain ⟨e, he, hcol⟩ := Finset.mem_image.mp hmem
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      simp only [col, Sym2.lift_mk] at hcol
      have hguv : g u ≠ g v := fun h => he.ne (g.injective h)
      rcases fin_nd_eq_iff hguv hxy hcol with hd | hd
      · refine ⟨x - g u, ?_⟩
        rw [SimpleGraph.map_adj]
        refine ⟨u, v, he, ?_, ?_⟩
        · simp [f]
        · simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
          have : g v + (x - g u) = x - (g u - g v) := by abel
          rw [this, hd]; abel
      · refine ⟨x - g v, ?_⟩
        rw [SimpleGraph.map_adj]
        refine ⟨v, u, he.symm, ?_, ?_⟩
        · simp [f]
        · simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
          have : g u + (x - g v) = x + (g u - g v) := by abel
          rw [this, hd]; abel

-- ============================================================================
-- SECTION 2: Longest-Path Characterization of Degree-≤-2 Trees
-- ============================================================================

private lemma walk_exists_boundary_edge {U : Type*} {G : SimpleGraph U} {s : Set U}
    {x y : U} (q : G.Walk x y) (hx : x ∉ s) (hy : y ∈ s) :
    ∃ a b : U, G.Adj a b ∧ a ∉ s ∧ b ∈ s := by
  induction q with
  | nil => exact absurd hy hx
  | @cons u v w hadj tail ih =>
    by_cases hv : v ∈ s
    · exact ⟨u, v, hadj, hx, hv⟩
    · exact ih hv hy

private lemma tree_maxDeg_le_two_hamiltonian {U : Type*} [Fintype U] [DecidableEq U]
    (C : SimpleGraph U) [DecidableRel C.Adj] (hC : C.IsTree) (hdeg : ∀ x, C.degree x ≤ 2) :
    ∃ f : Fin (Fintype.card U) → U,
      Function.Injective f ∧
      ∀ (i : ℕ) (hi : i + 1 < Fintype.card U),
        C.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
  have : Nonempty U := hC.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length C
  have hcov : ∀ w : U, w ∈ p.support := by
    intro w
    by_contra hw
    obtain ⟨q⟩ := hC.connected w u
    obtain ⟨a, b, hab, ha, hb⟩ :=
      walk_exists_boundary_edge (s := {z | z ∈ p.support}) q hw p.start_mem_support
    have hmem : b ∈ p.support := hb
    obtain ⟨i, hi_len, hi_eq⟩ := List.mem_iff_getElem.mp hmem
    have hlen_supp : p.support.length = p.length + 1 := p.length_support
    have hi_le : i ≤ p.length := by omega
    have hget : p.getVert i = b := by
      rw [Walk.getVert_eq_support_getElem p hi_le]
      exact hi_eq
    by_cases hi0 : i = 0
    · subst hi0
      have hbu : b = u := by simpa using hget.symm
      subst hbu
      have hp' : (Walk.cons hab p).IsPath := Walk.IsPath.cons hp ha
      have hle := hmax a v (Walk.cons hab p) hp'
      simp only [Walk.length_cons] at hle
      omega
    · by_cases hil : i = p.length
      · subst hil
        have hbv : b = v := by simpa [Walk.getVert_length] using hget.symm
        subst hbv
        have hp' : (p.concat hab.symm).IsPath := hp.concat ha hab.symm
        have hle := hmax u a (p.concat hab.symm) hp'
        simp only [Walk.length_concat] at hle
        omega
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
        have hi_lt : i < p.length := lt_of_le_of_ne hi_le hil
        let x₁ := p.getVert (i - 1)
        let x₂ := p.getVert (i + 1)
        have hadj1 : C.Adj b x₁ := by
          have h := p.adj_getVert_succ (by omega : i - 1 < p.length)
          have hidx : i - 1 + 1 = i := by omega
          rw [hidx, hget] at h
          exact h.symm
        have hadj2 : C.Adj b x₂ := by
          have h := p.adj_getVert_succ hi_lt
          rw [hget] at h
          exact h
        have hx1_mem : x₁ ∈ p.support := p.getVert_mem_support (i - 1)
        have hx2_mem : x₂ ∈ p.support := p.getVert_mem_support (i + 1)
        have ha1 : a ≠ x₁ := fun h => ha (h ▸ hx1_mem)
        have ha2 : a ≠ x₂ := fun h => ha (h ▸ hx2_mem)
        have h12 : x₁ ≠ x₂ := by
          intro heq
          have h1 : x₁ = p.support[i - 1]'(by omega) := p.getVert_eq_support_getElem (by omega)
          have h2 : x₂ = p.support[i + 1]'(by omega) := p.getVert_eq_support_getElem (by omega)
          rw [h1, h2] at heq
          have := (List.Nodup.getElem_inj_iff hp.support_nodup).mp heq
          omega
        have hsub : ({a, x₁, x₂} : Finset U) ⊆ C.neighborFinset b := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [mem_neighborFinset]
          rcases hz with rfl | rfl | rfl
          · exact hab.symm
          · exact hadj1
          · exact hadj2
        have hcard3 : ({a, x₁, x₂} : Finset U).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [h12]
          · simp [ha1, ha2]
        have hle2 := hdeg b
        rw [← card_neighborFinset_eq_degree] at hle2
        have := Finset.card_le_card hsub
        omega
  have htoFinset : p.support.toFinset = Finset.univ := by
    ext w
    simp [hcov w]
  have hcard_eq : p.length + 1 = Fintype.card U := by
    calc p.length + 1 = p.support.length := p.length_support.symm
      _ = p.support.toFinset.card := (List.toFinset_card_of_nodup hp.support_nodup).symm
      _ = Fintype.card U := by rw [htoFinset, Finset.card_univ]
  have hsupp_len : p.support.length = Fintype.card U := by
    rw [p.length_support, hcard_eq]
  refine ⟨fun j => p.getVert j.val, ?_, ?_⟩
  · intro j₁ j₂ hj
    dsimp only at hj
    have h1 : p.getVert j₁.val = p.support[j₁.val]'(by omega) :=
      p.getVert_eq_support_getElem (by omega)
    have h2 : p.getVert j₂.val = p.support[j₂.val]'(by omega) :=
      p.getVert_eq_support_getElem (by omega)
    rw [h1, h2] at hj
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp.support_nodup).mp hj)
  · intro i hi
    dsimp only
    exact p.adj_getVert_succ (by omega)

-- ============================================================================
-- SECTION 3: Montgomery's Tree Splitting Lemma (Lemma 3.6 of arXiv:2001.02665)
-- ============================================================================

private lemma component_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : G.ConnectedComponent) [Fintype ↥c]
    [DecidableRel c.toSimpleGraph.Adj] (x : ↥c) :
    c.toSimpleGraph.degree x = G.degree x.val := by
  let e : c.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val := {
    toFun := fun y => ⟨y.val.val, y.property⟩
    invFun := fun y => ⟨⟨y.val, c.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr e

private lemma card_filter_add_card_filter_not_eq {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2

private lemma tree_degree_pos_of_two_le_card {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (hG : G.IsTree) (hm : 2 ≤ Fintype.card W)
    (v : W) : 1 ≤ G.degree v := by
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := hG.minDegree_eq_one_of_nontrivial
  have := G.minDegree_le_degree v
  omega

private lemma tree_leaves_or_bare_paths {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (hG : G.IsTree) (hm : 2 ≤ Fintype.card W)
    {k : ℕ} (hk : 3 ≤ k) :
    Fintype.card W / (6 * k) ≤ (Finset.univ.filter (fun v : W => G.degree v = 1)).card ∨
    ∃ P : Fin (Fintype.card W / (6 * k)) → Fin (k + 1) → W,
      (∀ a₁ b₁ a₂ b₂, P a₁ b₁ = P a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂) ∧
      (∀ a (j : Fin k), G.Adj (P a j.castSucc) (P a j.succ)) ∧
      (∀ a (j : Fin (k + 1)), G.degree (P a j) = 2) := by
  classical
  let m := Fintype.card W
  let L := Finset.univ.filter (fun v : W => G.degree v = 1)
  let D2 := Finset.univ.filter (fun v : W => G.degree v = 2)
  let B := Finset.univ.filter (fun v : W => 3 ≤ G.degree v)
  by_cases hL : m / (6 * k) ≤ L.card
  · exact Or.inl hL
  · right
    have hL_lt : L.card < m / (6 * k) := not_le.mp hL
    have hpart : ∀ v : W, v ∈ L ∨ v ∈ D2 ∨ v ∈ B := by
      intro v
      have hpos := tree_degree_pos_of_two_le_card G hG hm v
      simp only [L, D2, B, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hdisj_LD : Disjoint L D2 := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [L, D2, Finset.mem_filter] at h1 h2; omega
    have hdisj_LB : Disjoint L B := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [L, B, Finset.mem_filter] at h1 h2; omega
    have hdisj_DB : Disjoint D2 B := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [D2, B, Finset.mem_filter] at h1 h2; omega
    have huniv : L ∪ D2 ∪ B = Finset.univ := by
      ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rcases hpart v with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hcard_sum : L.card + D2.card + B.card = m := by
      have h1 : (L ∪ D2 ∪ B).card = m := by rw [huniv, Finset.card_univ]
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_LB, hdisj_DB⟩),
          Finset.card_union_of_disjoint hdisj_LD] at h1
      exact h1
    have hdeg_sum : ∑ v : W, G.degree v = L.card + 2 * D2.card + ∑ v ∈ B, G.degree v := by
      have h1 : ∑ v : W, G.degree v = ∑ v ∈ L ∪ D2 ∪ B, G.degree v := by rw [huniv]
      rw [h1, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj_LB, hdisj_DB⟩),
          Finset.sum_union hdisj_LD]
      have hsumL : ∑ v ∈ L, G.degree v = L.card := by
        calc ∑ v ∈ L, G.degree v = ∑ _v ∈ L, 1 := Finset.sum_congr rfl fun v hv =>
              (Finset.mem_filter.mp hv).2
          _ = L.card := by simp
      have hsumD2 : ∑ v ∈ D2, G.degree v = 2 * D2.card := by
        calc ∑ v ∈ D2, G.degree v = ∑ _v ∈ D2, 2 := Finset.sum_congr rfl fun v hv =>
              (Finset.mem_filter.mp hv).2
          _ = 2 * D2.card := by simp [mul_comm]
      rw [hsumL, hsumD2]
    have htree_deg : ∑ v : W, G.degree v + 2 = 2 * m := by
      have h1 := G.sum_degrees_eq_twice_card_edges
      have h2 := hG.card_edgeFinset
      omega
    have hB_deg_lb : 3 * B.card ≤ ∑ v ∈ B, G.degree v := by
      calc 3 * B.card = ∑ _v ∈ B, 3 := by simp [mul_comm]
        _ ≤ ∑ v ∈ B, G.degree v := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
    have hB_le_L : B.card ≤ L.card := by omega
    have hD2_lb : m ≤ D2.card + 2 * L.card := by omega
    have hcompl_eq : D2ᶜ = L ∪ B := by
      ext v
      simp only [Finset.mem_compl, Finset.mem_union]
      constructor
      · intro hv
        rcases hpart v with h | h | h
        · exact Or.inl h
        · exact absurd h hv
        · exact Or.inr h
      · rintro (h | h)
        · exact Finset.disjoint_left.mp hdisj_LD h
        · exact Finset.disjoint_right.mp hdisj_DB h
    have hcompl_deg : ∑ v ∈ D2ᶜ, G.degree v ≤ 4 * L.card := by
      rw [hcompl_eq, Finset.sum_union hdisj_LB]
      have hsumL : ∑ v ∈ L, G.degree v = L.card := by
        calc ∑ v ∈ L, G.degree v = ∑ _v ∈ L, 1 := Finset.sum_congr rfl fun v hv =>
              (Finset.mem_filter.mp hv).2
          _ = L.card := by simp
      omega
    -- Induced forest on degree-2 vertices
    let H : SimpleGraph (D2 : Set W) := G.induce (D2 : Set W)
    have hH_acyc : H.IsAcyclic := hG.isAcyclic.induce _
    have hcard_D2 : Fintype.card (D2 : Set W) = D2.card := Fintype.card_coe D2
    -- Relate degrees in H and G
    have hdeg_split : ∀ x : (D2 : Set W),
        H.degree x + (Finset.univ.filter (fun w : W => w ∉ D2 ∧ G.Adj x.val w)).card =
          G.degree x.val := by
      intro x
      have hbij : H.degree x =
          (Finset.univ.filter (fun w : W => w ∈ D2 ∧ G.Adj x.val w)).card := by
        rw [← card_neighborFinset_eq_degree]
        refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
        · intro y hy
          rw [mem_neighborFinset] at hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.property, hy⟩
        · intro y₁ _ y₂ _ heq; exact Subtype.ext heq
        · intro w hw
          obtain ⟨_, hwD2, hadj⟩ := Finset.mem_filter.mp hw
          exact ⟨⟨w, hwD2⟩, (mem_neighborFinset _ _ _).mpr hadj, rfl⟩
      rw [hbij, ← Finset.card_union_of_disjoint, ← card_neighborFinset_eq_degree]
      · congr 1
        ext w
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          mem_neighborFinset]
        tauto
      · rw [Finset.disjoint_left]
        intro w h1 h2
        exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
    have hdegH_le2 : ∀ x : (D2 : Set W), H.degree x ≤ 2 := by
      intro x
      have h1 := hdeg_split x
      have h2 : G.degree x.val = 2 := (Finset.mem_filter.mp x.property).2
      omega
    have hcross_le : ∑ x : (D2 : Set W),
        (Finset.univ.filter (fun w : W => w ∉ D2 ∧ G.Adj x.val w)).card ≤ 4 * L.card := by
      have hstep1 : ∑ x : (D2 : Set W),
          (Finset.univ.filter (fun w : W => w ∉ D2 ∧ G.Adj x.val w)).card =
          ∑ x ∈ D2, ∑ w ∈ D2ᶜ, (if G.Adj x w then 1 else 0) := by
        rw [← Finset.sum_coe_sort D2]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hfil : Finset.univ.filter (fun w : W => w ∉ D2 ∧ G.Adj x.val w) =
            D2ᶜ.filter (fun w => G.Adj x.val w) := by
          ext w; simp [Finset.mem_compl]
        rw [hfil, Finset.card_filter]
      rw [hstep1, Finset.sum_comm]
      calc ∑ w ∈ D2ᶜ, ∑ x ∈ D2, (if G.Adj x w then 1 else 0)
          ≤ ∑ w ∈ D2ᶜ, ∑ x : W, (if G.Adj w x then 1 else 0) := by
            refine Finset.sum_le_sum fun w _ => ?_
            have hsym : ∀ x, (if G.Adj x w then 1 else 0) = (if G.Adj w x then 1 else 0) :=
              fun x => by simp only [G.adj_comm]
            simp_rw [hsym]
            exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∑ w ∈ D2ᶜ, G.degree w := by
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [← card_neighborFinset_eq_degree, Finset.card_eq_sum_ones,
                ← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext x
            simp [mem_neighborFinset]
        _ ≤ 4 * L.card := hcompl_deg
    have h2D2_le : 2 * D2.card ≤ 2 * H.edgeFinset.card + 4 * L.card := by
      have hsumG : ∑ x : (D2 : Set W), G.degree x.val = 2 * D2.card := by
        calc ∑ x : (D2 : Set W), G.degree x.val
            = ∑ _x : (D2 : Set W), 2 := Finset.sum_congr rfl fun x _ =>
                (Finset.mem_filter.mp x.property).2
          _ = 2 * Fintype.card (D2 : Set W) := by simp [mul_comm]
          _ = 2 * D2.card := by rw [hcard_D2]
      have hsum_split : (∑ x : (D2 : Set W), H.degree x) +
          (∑ x : (D2 : Set W),
            (Finset.univ.filter (fun w : W => w ∉ D2 ∧ G.Adj x.val w)).card) =
          ∑ x : (D2 : Set W), G.degree x.val := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => hdeg_split x
      have h2E := H.sum_degrees_eq_twice_card_edges
      omega
    -- Component decomposition of H
    have hcomp_card_sum : ∑ c : H.ConnectedComponent, Fintype.card ↥c = D2.card := by
      have e : (Σ c : H.ConnectedComponent, ↥c) ≃ (D2 : Set W) :=
        Equiv.sigmaFiberEquiv H.connectedComponentMk
      rw [← Fintype.card_sigma, Fintype.card_congr e, hcard_D2]
    have hcomp_edge_sum : ∑ c : H.ConnectedComponent, c.toSimpleGraph.edgeFinset.card =
        H.edgeFinset.card := by
      have h2 : 2 * (∑ c : H.ConnectedComponent, c.toSimpleGraph.edgeFinset.card) =
          2 * H.edgeFinset.card := by
        rw [Finset.mul_sum, ← H.sum_degrees_eq_twice_card_edges]
        have hstep : ∑ c : H.ConnectedComponent, 2 * c.toSimpleGraph.edgeFinset.card =
            ∑ c : H.ConnectedComponent, ∑ y : ↥c, H.degree y.val := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← c.toSimpleGraph.sum_degrees_eq_twice_card_edges]
          exact Finset.sum_congr rfl fun y _ => component_degree H c y
        rw [hstep, ← Fintype.sum_sigma (fun p : (Σ c : H.ConnectedComponent, ↥c) => H.degree p.2.val)]
        let e : (Σ c : H.ConnectedComponent, ↥c) ≃ (D2 : Set W) :=
          { toFun := fun p => p.2.val
            invFun := fun x => ⟨H.connectedComponentMk x, ⟨x, rfl⟩⟩
            left_inv := fun ⟨c, ⟨x, hx⟩⟩ => by subst hx; rfl
            right_inv := fun _ => rfl }
        exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      omega
    have hcomp_euler :
        H.edgeFinset.card + Fintype.card H.ConnectedComponent = D2.card := by
      have hsum : ∑ c : H.ConnectedComponent, (c.toSimpleGraph.edgeFinset.card + 1) =
          ∑ c : H.ConnectedComponent, Fintype.card ↥c :=
        Finset.sum_congr rfl fun c _ => (hH_acyc.isTree_connectedComponent c).card_edgeFinset
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          hcomp_edge_sum, hcomp_card_sum] at hsum
      exact hsum
    have hcomp_le : Fintype.card H.ConnectedComponent ≤ 2 * L.card := by omega
    -- Count total blocks of size k + 1 across components
    have hblocks_lb : m / (6 * k) ≤
        ∑ c : H.ConnectedComponent, Fintype.card ↥c / (k + 1) := by
      have hdiv_sum :
          D2.card ≤ (k + 1) * (∑ c : H.ConnectedComponent, Fintype.card ↥c / (k + 1)) +
            k * Fintype.card H.ConnectedComponent := by
        rw [← hcomp_card_sum, Finset.mul_sum]
        have hconst : k * Fintype.card H.ConnectedComponent =
            ∑ _c : H.ConnectedComponent, k := by simp [mul_comm]
        rw [hconst, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun c _ => ?_
        have hmod := Nat.mod_lt (Fintype.card ↥c) (by omega : 0 < k + 1)
        have hdm := Nat.div_add_mod (Fintype.card ↥c) (k + 1)
        omega
      have hL_mul : 6 * k * L.card ≤ m := by
        have := Nat.mul_div_le m (6 * k)
        nlinarith
      have hq_mul : 6 * k * (m / (6 * k)) ≤ m := Nat.mul_div_le m (6 * k)
      have h9 : 9 * ((k + 1) * (m / (6 * k))) ≤
          9 * ((k + 1) * (∑ c : H.ConnectedComponent, Fintype.card ↥c / (k + 1))) := by
        nlinarith
      have hpos : 0 < 9 * (k + 1) := by positivity
      nlinarith
    -- Build Hamiltonian path for each component of H
    have hpath_ex : ∀ c : H.ConnectedComponent,
        ∃ f : Fin (Fintype.card ↥c) → ↥c,
          Function.Injective f ∧
          ∀ (i : ℕ) (hi : i + 1 < Fintype.card ↥c),
            c.toSimpleGraph.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
      intro c
      refine tree_maxDeg_le_two_hamiltonian c.toSimpleGraph
        (hH_acyc.isTree_connectedComponent c) (fun x => ?_)
      rw [component_degree H c x]
      exact hdegH_le2 x.val
    choose path hpath_inj hpath_adj using hpath_ex
    -- Pack all disjoint blocks of length k into Fin (m / (6 * k))
    let Idx := Σ c : H.ConnectedComponent, Fin (Fintype.card ↥c / (k + 1))
    have hIdx_card : Fintype.card Idx =
        ∑ c : H.ConnectedComponent, Fintype.card ↥c / (k + 1) := by
      simp [Idx, Fintype.card_sigma]
    have hle_Idx : m / (6 * k) ≤ Fintype.card Idx := by omega
    let enum : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
    have hblock_lt : ∀ (p : Idx) (j : Fin (k + 1)),
        p.2.val * (k + 1) + j.val < Fintype.card ↥p.1 := by
      intro p j
      have h1 : (p.2.val + 1) * (k + 1) ≤ Fintype.card ↥p.1 / (k + 1) * (k + 1) :=
        Nat.mul_le_mul_right (k + 1) p.2.isLt
      have h2 : Fintype.card ↥p.1 / (k + 1) * (k + 1) ≤ Fintype.card ↥p.1 :=
        Nat.div_mul_le_self _ _
      have h3 : p.2.val * (k + 1) + (k + 1) ≤ Fintype.card ↥p.1 := by
        calc p.2.val * (k + 1) + (k + 1) = (p.2.val + 1) * (k + 1) := by ring
          _ ≤ Fintype.card ↥p.1 / (k + 1) * (k + 1) := h1
          _ ≤ Fintype.card ↥p.1 := h2
      have hj := j.isLt
      omega
    have hP_aux_inj : ∀ (p₁ p₂ : Idx) (b₁ b₂ : Fin (k + 1)),
        (path p₁.1 ⟨p₁.2.val * (k + 1) + b₁.val, hblock_lt p₁ b₁⟩).val.val =
        (path p₂.1 ⟨p₂.2.val * (k + 1) + b₂.val, hblock_lt p₂ b₂⟩).val.val →
        p₁ = p₂ ∧ b₁ = b₂ := by
      rintro ⟨c₁, q₁⟩ ⟨c₂, q₂⟩ b₁ b₂ hEq
      have hsub1 :
          (path c₁ ⟨q₁.val * (k + 1) + b₁.val, hblock_lt ⟨c₁, q₁⟩ b₁⟩).val =
          (path c₂ ⟨q₂.val * (k + 1) + b₂.val, hblock_lt ⟨c₂, q₂⟩ b₂⟩).val :=
        Subtype.ext hEq
      have hc1 : H.connectedComponentMk
          (path c₁ ⟨q₁.val * (k + 1) + b₁.val, hblock_lt ⟨c₁, q₁⟩ b₁⟩).val = c₁ :=
        (path c₁ ⟨q₁.val * (k + 1) + b₁.val, hblock_lt ⟨c₁, q₁⟩ b₁⟩).property
      have hc2 : H.connectedComponentMk
          (path c₂ ⟨q₂.val * (k + 1) + b₂.val, hblock_lt ⟨c₂, q₂⟩ b₂⟩).val = c₂ :=
        (path c₂ ⟨q₂.val * (k + 1) + b₂.val, hblock_lt ⟨c₂, q₂⟩ b₂⟩).property
      have hceq : c₁ = c₂ := by rw [← hc1, hsub1, hc2]
      subst hceq
      have hsub2 :
          path c₁ ⟨q₁.val * (k + 1) + b₁.val, hblock_lt ⟨c₁, q₁⟩ b₁⟩ =
          path c₁ ⟨q₂.val * (k + 1) + b₂.val, hblock_lt ⟨c₁, q₂⟩ b₂⟩ :=
        Subtype.ext hsub1
      have hidx := congrArg Fin.val (hpath_inj c₁ hsub2)
      dsimp only at hidx
      have hb1 := b₁.isLt
      have hb2 := b₂.isLt
      have hq : q₁.val = q₂.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (q₁.val + 1) * (k + 1) ≤ q₂.val * (k + 1) :=
            Nat.mul_le_mul_right (k + 1) hlt
          rw [Nat.add_mul, one_mul] at hle
          omega
        · have hle : (q₂.val + 1) * (k + 1) ≤ q₁.val * (k + 1) :=
            Nat.mul_le_mul_right (k + 1) hgt
          rw [Nat.add_mul, one_mul] at hle
          omega
      have hb : b₁.val = b₂.val := by rw [hq] at hidx; omega
      exact ⟨by congr 1; exact Fin.ext hq, Fin.ext hb⟩
    let P : Fin (m / (6 * k)) → Fin (k + 1) → W := fun a j =>
      let p := enum ⟨a.val, lt_of_lt_of_le a.isLt hle_Idx⟩
      (path p.1 ⟨p.2.val * (k + 1) + j.val, hblock_lt p j⟩).val.val
    refine ⟨P, ?_, ?_, ?_⟩
    · intro a₁ b₁ a₂ b₂ hEq
      have h := hP_aux_inj _ _ _ _ hEq
      have ha_fin : (⟨a₁.val, lt_of_lt_of_le a₁.isLt hle_Idx⟩ : Fin (Fintype.card Idx)) =
          ⟨a₂.val, lt_of_lt_of_le a₂.isLt hle_Idx⟩ := enum.injective h.1
      have ha_val : a₁.val = a₂.val :=
        congrArg (fun x : Fin (Fintype.card Idx) => x.val) ha_fin
      exact ⟨Fin.ext ha_val, h.2⟩
    · intro a j
      dsimp only [P]
      set p := enum ⟨a.val, lt_of_lt_of_le a.isLt hle_Idx⟩
      have hlt : p.2.val * (k + 1) + j.val + 1 < Fintype.card ↥p.1 := by
        have h := hblock_lt p j.succ
        simpa [Fin.val_succ, Nat.add_assoc] using h
      exact hpath_adj p.1 (p.2.val * (k + 1) + j.val) hlt
    · intro a j
      dsimp only [P]
      set p := enum ⟨a.val, lt_of_lt_of_le a.isLt hle_Idx⟩
      exact (Finset.mem_filter.mp (path p.1 _).val.property).2

-- ============================================================================
-- SECTION 4: MPS Case Division & Main Reduction Proof
-- ============================================================================

private lemma tree_leaves_not_adj {n : ℕ} (hn : 2 ≤ n)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    {x y : Fin (n + 1)} (hx : T.degree x = 1) (hy : T.degree y = 1) : ¬ T.Adj x y := by
  intro hadj
  obtain ⟨u, hux, hu_uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  obtain ⟨v, hvy, hv_uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hy
  have huv : y = u := hu_uniq y hadj
  have hvx : x = v := hv_uniq x hadj.symm
  have hcard3 : 3 ≤ Fintype.card (Fin (n + 1)) := by simp; omega
  have hex : ∃ z : Fin (n + 1), z ≠ x ∧ z ≠ y := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ {x, y} := by
      intro z _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (hall z hzx)
    have := Finset.card_le_card hsub
    have h2 : ({x, y} : Finset (Fin (n + 1))).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨z, hzx, hzy⟩ := hex
  obtain ⟨q⟩ := hT.connected z x
  obtain ⟨a, b, hab, ha, hb⟩ :=
    walk_exists_boundary_edge (s := ({x, y} : Set (Fin (n + 1)))) q
      (by simp [hzx, hzy]) (by simp)
  rcases hb with rfl | rfl
  · exact ha (Or.inr ((hu_uniq a hab.symm).trans huv.symm))
  · exact ha (Or.inl ((hv_uniq a hab.symm).trans hvx.symm))

private lemma mps_case_division {n : ℕ} (hn : 2 ^ 144 ≤ n)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree) :
    let L := 2 ^ Nat.sqrt (Nat.log 2 n)
    let core := Finset.univ.filter (fun w : Fin (n + 1) =>
      ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
        L ^ 4 ≤ (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))
    core.card ≤ n / 100 ∨
    (n / 100 < core.card ∧
      ∃ S : Finset (Fin (n + 1)),
        n / L ^ 6 ≤ S.card ∧
        (∀ x ∈ S, T.degree x = 1) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ T.Adj x y ∧ ∀ z, ¬ (T.Adj x z ∧ T.Adj y z))) ∨
    (n / 100 < core.card ∧
      ∃ P : Fin (n / (800 * L)) → Fin (L + 1) → Fin (n + 1),
        (∀ a₁ b₁ a₂ b₂, P a₁ b₁ = P a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂) ∧
        (∀ a (j : Fin L), T.Adj (P a j.castSucc) (P a j.succ)) ∧
        (∀ a (j : Fin (L + 1)), 0 < j.val → j.val < L → T.degree (P a j) = 2)) := by
  classical
  dsimp only
  set L := 2 ^ Nat.sqrt (Nat.log 2 n)
  set core := Finset.univ.filter (fun w : Fin (n + 1) =>
    ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
      L ^ 4 ≤ (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))
  have hlog : 144 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hsqrt : 12 ≤ Nat.sqrt (Nat.log 2 n) := by
    rw [Nat.le_sqrt]; omega
  have hL : 4096 ≤ L := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ Nat.sqrt (Nat.log 2 n) := Nat.pow_le_pow_right (by norm_num) hsqrt
  have hn_big : 1000000 ≤ n := by
    have : 1000000 ≤ 2 ^ 144 := by norm_num
    omega
  by_cases hC : core.card ≤ n / 100
  · exact Or.inl hC
  · right
    have hcore_gt : n / 100 < core.card := not_le.mp hC
    have hcore_ge2 : 2 ≤ core.card := by omega
    -- Every removed vertex is a leaf of T
    have hrem_leaf : ∀ w : Fin (n + 1), w ∉ core → T.degree w = 1 := by
      intro w hw
      simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
      exact hw.1
    -- The induced subgraph T' on core is a tree
    let T' : SimpleGraph (core : Set (Fin (n + 1))) := T.induce (core : Set (Fin (n + 1)))
    have hT'_pre : T'.Preconnected := by
      refine hT.connected.preconnected.induce_of_degree_eq_one ?_
      intro w hw
      have hdeg1 : T.degree w = 1 := hrem_leaf w (by simpa using hw)
      obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg1
      intro a ha b hb
      exact (hu a ha).trans (hu b hb).symm
    have hcore_nonempty : Nonempty (core : Set (Fin (n + 1))) := by
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < core.card)
      exact ⟨⟨w, hw⟩⟩
    have hT'_tree : T'.IsTree := ⟨⟨hT'_pre⟩, hT.isAcyclic.induce _⟩
    have hcard_core : Fintype.card (core : Set (Fin (n + 1))) = core.card := Fintype.card_coe core
    have hm_ge2 : 2 ≤ Fintype.card (core : Set (Fin (n + 1))) := by omega
    have hsplit := tree_leaves_or_bare_paths T' hT'_tree hm_ge2 (k := L) (by omega)
    have hdiv_core : n / (600 * L) ≤ Fintype.card (core : Set (Fin (n + 1))) / (6 * L) := by
      rw [hcard_core]
      calc n / (600 * L) = n / (100 * (6 * L)) := by ring_nf
        _ = (n / 100) / (6 * L) := (Nat.div_div_eq_div_mul n 100 (6 * L)).symm
        _ ≤ core.card / (6 * L) := Nat.div_le_div_right (le_of_lt hcore_gt)
    rcases hsplit with hleaves | hpaths
    · -- Case A (many leaves in T')
      left
      refine ⟨hcore_gt, ?_⟩
      let L' := Finset.univ.filter (fun x : (core : Set (Fin (n + 1))) => T'.degree x = 1)
      have hL'_lb : n / (600 * L) ≤ L'.card := hdiv_core.trans hleaves
      let L_same := L'.filter (fun x => T.degree x.val = 1)
      let L_chg := L'.filter (fun x => T.degree x.val ≠ 1)
      have hL'_split : L_same.card + L_chg.card = L'.card :=
        card_filter_add_card_filter_not_eq L' (fun x => T.degree x.val = 1)
      by_cases hhalf : n / (600 * L) ≤ 2 * L_same.card
      · -- Subcase 2a: many leaves of T' are still leaves of T
        have hpar_ex : ∀ x : ↥(core : Set (Fin (n + 1))),
            x ∈ L_same → ∃ v : Fin (n + 1), T.Adj x.val v := by
          intro x hx
          have hd1 : T.degree x.val = 1 := (Finset.mem_filter.mp hx).2
          obtain ⟨v, hv, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
          exact ⟨v, hv⟩
        let par : ↥(core : Set (Fin (n + 1))) → Fin (n + 1) := fun x =>
          if hx : x ∈ L_same then (hpar_ex x hx).choose else 0
        have hpar_adj : ∀ x ∈ L_same, T.Adj x.val (par x) := by
          intro x hx; simp only [par, dif_pos hx]; exact (hpar_ex x hx).choose_spec
        have hpar_uniq : ∀ x ∈ L_same, ∀ z, T.Adj x.val z → z = par x := by
          intro x hx z hz
          have hd1 : T.degree x.val = 1 := (Finset.mem_filter.mp hx).2
          obtain ⟨v, _, hv⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
          exact (hv z hz).trans (hv (par x) (hpar_adj x hx)).symm
        let Pars := L_same.image par
        -- Each fiber of par on L_same has size < L^4
        have hfiber : ∀ v ∈ Pars, (L_same.filter (fun x => par x = v)).card ≤ L ^ 4 := by
          intro v hv
          obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hv
          have hx0_core := x0.property
          simp only [Finset.mem_coe, core, Finset.mem_filter, Finset.mem_univ, true_and] at hx0_core
          have hx0_d1 : T.degree x0.val = 1 := (Finset.mem_filter.mp hx0).2
          have hlt_L4 : (Finset.univ.filter (fun u => T.Adj (par x0) u ∧ T.degree u = 1)).card <
              L ^ 4 := by
            by_contra hge
            exact hx0_core ⟨hx0_d1, par x0, (hpar_adj x0 hx0).symm, not_lt.mp hge⟩
          have hcard_le : (L_same.filter (fun x => par x = par x0)).card ≤
              (Finset.univ.filter (fun u => T.Adj (par x0) u ∧ T.degree u = 1)).card := by
            refine Finset.card_le_card_of_injOn (fun x => x.val) ?_ ?_
            · intro x hx
              simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
                true_and] at hx ⊢
              exact ⟨hx.2 ▸ (hpar_adj x hx.1).symm, (Finset.mem_filter.mp hx.1).2⟩
            · intro x₁ _ x₂ _ heq; exact Subtype.ext heq
          omega
        have hL_same_le : L_same.card ≤ Pars.card * L ^ 4 := by
          have hpart_fib : L_same.card =
              ∑ v ∈ Pars, (L_same.filter (fun x => par x = v)).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext x
              simp only [Finset.mem_biUnion, Finset.mem_filter, Pars, Finset.mem_image]
              constructor
              · intro hx; exact ⟨par x, ⟨x, hx, rfl⟩, hx, rfl⟩
              · rintro ⟨_, _, hx, _⟩; exact hx
            · intro v₁ _ v₂ _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]; intro x h1 h2
              exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
          rw [hpart_fib]
          calc ∑ v ∈ Pars, (L_same.filter (fun x => par x = v)).card
              ≤ ∑ _v ∈ Pars, L ^ 4 := Finset.sum_le_sum hfiber
            _ = Pars.card * L ^ 4 := by simp
        -- Pick one leaf per parent in Pars
        have hrep_ex : ∀ v ∈ Pars, ∃ x ∈ L_same, par x = v := by
          intro v hv; exact Finset.mem_image.mp hv
        let rep : Fin (n + 1) → Fin (n + 1) := fun v =>
          if hv : v ∈ Pars then (hrep_ex v hv).choose.val else 0
        have hrep_mem : ∀ v (hv : v ∈ Pars),
            (hrep_ex v hv).choose ∈ L_same ∧ par (hrep_ex v hv).choose = v :=
          fun v hv => (hrep_ex v hv).choose_spec
        let S := Pars.image rep
        have hrep_inj : Set.InjOn rep (Pars : Set (Fin (n + 1))) := by
          intro v₁ hv₁ v₂ hv₂ heq
          simp only [Finset.mem_coe] at hv₁ hv₂
          simp only [rep, dif_pos hv₁, dif_pos hv₂] at heq
          have hsub : (hrep_ex v₁ hv₁).choose = (hrep_ex v₂ hv₂).choose := Subtype.ext heq
          rw [← (hrep_mem v₁ hv₁).2, ← (hrep_mem v₂ hv₂).2, hsub]
        have hS_card : S.card = Pars.card := Finset.card_image_of_injOn hrep_inj
        refine ⟨S, ?_, ?_, ?_⟩
        · by_contra hlt
          have h1 : S.card + 1 ≤ n / L ^ 6 := not_le.mp hlt
          have h2 : L ^ 6 * (S.card + 1) ≤ n :=
            (Nat.mul_le_mul_left (L ^ 6) h1).trans (Nat.mul_div_le n (L ^ 6))
          have h3 : n < 600 * L * (n / (600 * L)) + 600 * L := by
            have := Nat.div_add_mod n (600 * L)
            have := Nat.mod_lt n (by positivity : 0 < 600 * L)
            omega
          have h4 : 600 * L * (n / (600 * L)) ≤ 1200 * L ^ 5 * S.card := by
            rw [hS_card]
            have hstep : 600 * L * (n / (600 * L)) ≤ 600 * L * (2 * L_same.card) :=
              Nat.mul_le_mul_left _ hhalf
            have hstep2 : 600 * L * (2 * L_same.card) ≤ 600 * L * (2 * (Pars.card * L ^ 4)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hL_same_le)
            calc 600 * L * (n / (600 * L)) ≤ 600 * L * (2 * (Pars.card * L ^ 4)) :=
                  hstep.trans hstep2
              _ = 1200 * L ^ 5 * Pars.card := by ring
          have h5 : 1200 * L ^ 5 ≤ L ^ 6 := by
            have : L ^ 6 = L * L ^ 5 := by ring
            rw [this]
            exact Nat.mul_le_mul_right (L ^ 5) (by omega)
          have h6 : 600 * L ≤ L ^ 6 := by
            have : 600 ≤ L ^ 5 := by
              have hL1 : 1 ≤ L := by omega
              calc 600 ≤ L := by omega
                _ = L * 1 := by ring
                _ ≤ L * L ^ 4 := Nat.mul_le_mul_left L (Nat.one_le_pow 4 L hL1)
                _ = L ^ 5 := by ring
            calc 600 * L ≤ L ^ 5 * L := Nat.mul_le_mul_right L this
              _ = L ^ 6 := by ring
          have h7 : 1200 * L ^ 5 * S.card ≤ L ^ 6 * S.card := Nat.mul_le_mul_right S.card h5
          have h8 : L ^ 6 * (S.card + 1) = L ^ 6 * S.card + L ^ 6 := by ring
          omega
        · intro x hx
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
          have hrv : rep v = (hrep_ex v hv).choose.val := dif_pos hv
          have hdeg_eq : ∀ a b : Fin (n + 1), a = b → T.degree a = T.degree b := by
            intro a b hab; subst hab; rfl
          rw [hdeg_eq _ _ hrv]
          exact (Finset.mem_filter.mp (hrep_mem v hv).1).2
        · intro x hx y hy hxy
          obtain ⟨v₁, hv₁, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨v₂, hv₂, rfl⟩ := Finset.mem_image.mp hy
          have hvne : v₁ ≠ v₂ := fun h => hxy (by rw [h])
          simp only [rep, dif_pos hv₁, dif_pos hv₂] at hxy ⊢
          have hx_deg : T.degree (hrep_ex v₁ hv₁).choose.val = 1 :=
            (Finset.mem_filter.mp (hrep_mem v₁ hv₁).1).2
          have hy_deg : T.degree (hrep_ex v₂ hv₂).choose.val = 1 :=
            (Finset.mem_filter.mp (hrep_mem v₂ hv₂).1).2
          refine ⟨tree_leaves_not_adj (by omega) T hT hx_deg hy_deg, ?_⟩
          intro z ⟨hz1, hz2⟩
          have h1 := hpar_uniq _ (hrep_mem v₁ hv₁).1 z hz1
          have h2 := hpar_uniq _ (hrep_mem v₂ hv₂).1 z hz2
          rw [(hrep_mem v₁ hv₁).2] at h1
          rw [(hrep_mem v₂ hv₂).2] at h2
          exact hvne (h1.symm.trans h2)
      · -- Subcase 2b: many leaves of T' are NOT leaves of T
        have hchg_lb : n / (600 * L) ≤ 2 * L_chg.card := by omega
        -- Every x ∈ L_chg has a neighbour w ∉ core (which is a leaf of T with unique neighbour x.val)
        have hleaf_ex : ∀ x ∈ L_chg, ∃ w : Fin (n + 1), w ∉ core ∧ T.Adj x.val w := by
          intro x hx
          have hxL' : T'.degree x = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
          have hxne1 : T.degree x.val ≠ 1 := (Finset.mem_filter.mp hx).2
          by_contra hall
          push Not at hall
          have heq : T'.degree x = T.degree x.val := by
            rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
            refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
            · intro y hy
              rw [mem_neighborFinset] at hy ⊢
              exact hy
            · intro y₁ _ y₂ _ h; exact Subtype.ext h
            · intro w hw
              rw [mem_neighborFinset] at hw
              have hw_core : w ∈ core := by
                by_contra hnc; exact hall w hnc hw
              exact ⟨⟨w, hw_core⟩, (mem_neighborFinset _ _ _).mpr hw, rfl⟩
          exact hxne1 (heq.symm.trans hxL')
        let pick : ↥(core : Set (Fin (n + 1))) → Fin (n + 1) := fun x =>
          if hx : x ∈ L_chg then (hleaf_ex x hx).choose else 0
        have hpick_spec : ∀ x ∈ L_chg, pick x ∉ core ∧ T.Adj x.val (pick x) := by
          intro x hx; simp only [pick, dif_pos hx]; exact (hleaf_ex x hx).choose_spec
        have hpick_deg : ∀ x ∈ L_chg, T.degree (pick x) = 1 :=
          fun x hx => hrem_leaf _ (hpick_spec x hx).1
        have hpick_uniq : ∀ x ∈ L_chg, ∀ z, T.Adj (pick x) z → z = x.val := by
          intro x hx z hz
          obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp (hpick_deg x hx)
          exact (hu z hz).trans (hu x.val (hpick_spec x hx).2.symm).symm
        let S := L_chg.image pick
        have hpick_inj : Set.InjOn pick (L_chg : Set ↥(core : Set (Fin (n + 1)))) := by
          intro x₁ hx₁ x₂ hx₂ heq
          simp only [Finset.mem_coe] at hx₁ hx₂
          have hadj : T.Adj (pick x₁) x₂.val := heq ▸ (hpick_spec x₂ hx₂).2.symm
          exact Subtype.ext (hpick_uniq x₁ hx₁ x₂.val hadj).symm
        have hS_card : S.card = L_chg.card := Finset.card_image_of_injOn hpick_inj
        refine ⟨S, ?_, ?_, ?_⟩
        · by_contra hlt
          have h1 : S.card + 1 ≤ n / L ^ 6 := not_le.mp hlt
          have h2 : L ^ 6 * (S.card + 1) ≤ n :=
            (Nat.mul_le_mul_left (L ^ 6) h1).trans (Nat.mul_div_le n (L ^ 6))
          have h3 : n < 600 * L * (n / (600 * L)) + 600 * L := by
            have := Nat.div_add_mod n (600 * L)
            have := Nat.mod_lt n (by positivity : 0 < 600 * L)
            omega
          have h4 : 600 * L * (n / (600 * L)) ≤ 1200 * L * S.card := by
            rw [hS_card]
            calc 600 * L * (n / (600 * L)) ≤ 600 * L * (2 * L_chg.card) :=
                  Nat.mul_le_mul_left _ hchg_lb
              _ = 1200 * L * L_chg.card := by ring
          have h5 : 1200 * L ≤ L ^ 6 := by
            have hL1 : 1 ≤ L := by omega
            have : 1200 ≤ L ^ 5 := by
              calc 1200 ≤ L := by omega
                _ = L * 1 := by ring
                _ ≤ L * L ^ 4 := Nat.mul_le_mul_left L (Nat.one_le_pow 4 L hL1)
                _ = L ^ 5 := by ring
            calc 1200 * L ≤ L ^ 5 * L := Nat.mul_le_mul_right L this
              _ = L ^ 6 := by ring
          have h6 : 600 * L ≤ L ^ 6 := by omega
          have h7 : 1200 * L * S.card ≤ L ^ 6 * S.card := Nat.mul_le_mul_right S.card h5
          have h8 : L ^ 6 * (S.card + 1) = L ^ 6 * S.card + L ^ 6 := by ring
          omega
        · intro u hu
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
          exact hpick_deg x hx
        · intro u hu w hw huw
          obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw
          have hxne : x₁ ≠ x₂ := fun h => huw (by rw [h])
          refine ⟨tree_leaves_not_adj (by omega) T hT (hpick_deg x₁ hx₁) (hpick_deg x₂ hx₂), ?_⟩
          intro z ⟨hz1, hz2⟩
          have h1 := hpick_uniq x₁ hx₁ z hz1
          have h2 := hpick_uniq x₂ hx₂ z hz2
          exact hxne (Subtype.ext (h1.symm.trans h2))
    · -- Case B (many vertex-disjoint bare paths in T')
      right
      refine ⟨hcore_gt, ?_⟩
      set M := Fintype.card (core : Set (Fin (n + 1))) / (6 * L)
      obtain ⟨P', hP'_inj, hP'_adj, hP'_deg⟩ := hpaths
      -- Vertices of core that lost a leaf-neighbour when passing from T to T'
      let Bad := core.filter (fun v => ∃ w ∉ core, T.Adj v w)
      have hBad_deg : ∀ v ∈ Bad,
          L ^ 4 ≤ (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card := by
        intro v hv
        obtain ⟨_, w, hw_nc, hvw⟩ := Finset.mem_filter.mp hv
        simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw_nc
        obtain ⟨hw1, v', hv'w, hge⟩ := hw_nc
        obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hw1
        have hvv' : v' = v := (hu v' hv'w.symm).trans (hu v hvw.symm).symm
        exact hvv' ▸ hge
      have hBad_card : Bad.card * L ^ 4 ≤ n + 1 := by
        let fL : Fin (n + 1) → Finset (Fin (n + 1)) :=
          fun v => Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)
        have hdisj : Set.PairwiseDisjoint (Bad : Set (Fin (n + 1))) fL := by
          intro v₁ _ v₂ _ hne
          change Disjoint (fL v₁) (fL v₂)
          rw [Finset.disjoint_left]
          intro u hu₁ hu₂
          obtain ⟨_, hadj1, hd1⟩ := Finset.mem_filter.mp hu₁
          obtain ⟨_, hadj2, _⟩ := Finset.mem_filter.mp hu₂
          obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
          exact hne ((hw v₁ hadj1.symm).trans (hw v₂ hadj2.symm).symm)
        calc Bad.card * L ^ 4 = ∑ _v ∈ Bad, L ^ 4 := by simp
          _ ≤ ∑ v ∈ Bad, (fL v).card := Finset.sum_le_sum fun v hv => hBad_deg v hv
          _ = (Bad.biUnion fL).card := (Finset.card_biUnion hdisj).symm
          _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
          _ = n + 1 := by simp
      let BadIdx := Finset.univ.filter (fun a : Fin M => ∃ j : Fin (L + 1), (P' a j).val ∈ Bad)
      have hBadIdx_le : BadIdx.card ≤ Bad.card := by
        let wit : Fin M → Fin (n + 1) := fun a =>
          if ha : a ∈ BadIdx then (P' a (Finset.mem_filter.mp ha).2.choose).val else 0
        refine Finset.card_le_card_of_injOn wit ?_ ?_
        · intro a ha
          simp only [Finset.mem_coe] at ha ⊢
          simp only [wit, dif_pos ha]
          exact (Finset.mem_filter.mp ha).2.choose_spec
        · intro a₁ ha₁ a₂ ha₂ heq
          simp only [Finset.mem_coe] at ha₁ ha₂
          simp only [wit, dif_pos ha₁, dif_pos ha₂] at heq
          exact (hP'_inj _ _ _ _ (Subtype.ext heq)).1
      let GoodIdx := Finset.univ.filter (fun a : Fin M => ¬ ∃ j : Fin (L + 1), (P' a j).val ∈ Bad)
      have hGood_sum : BadIdx.card + GoodIdx.card = M :=
        (card_filter_add_card_filter_not_eq
          (Finset.univ : Finset (Fin M))
          (fun a => ∃ j : Fin (L + 1), (P' a j).val ∈ Bad)).trans (by simp)
      have hGood_lb : n / (800 * L) ≤ GoodIdx.card := by
        have hq1 : n < 600 * L * (n / (600 * L) + 1) := by
          have := Nat.div_add_mod n (600 * L)
          have := Nat.mod_lt n (by positivity : 0 < 600 * L)
          nlinarith
        have hq2 : 800 * L * (n / (800 * L)) ≤ n := Nat.mul_div_le n (800 * L)
        have h4800 : 4800 * L ≤ L ^ 4 := by
          have hL3 : 4800 ≤ L ^ 3 := by
            calc 4800 ≤ 4096 ^ 3 := by norm_num
              _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3
          calc 4800 * L ≤ L ^ 3 * L := Nat.mul_le_mul_right L hL3
            _ = L ^ 4 := by ring
        have hbad_bound : 4800 * L * Bad.card ≤ n + 1 := by
          calc 4800 * L * Bad.card = Bad.card * (4800 * L) := by ring
            _ ≤ Bad.card * L ^ 4 := Nat.mul_le_mul_left _ h4800
            _ ≤ n + 1 := hBad_card
        have hsum_le : n / (800 * L) + Bad.card ≤ n / (600 * L) := by
          by_contra hgt
          have hge : n / (600 * L) + 1 ≤ n / (800 * L) + Bad.card := not_le.mp hgt
          have hmul : 600 * L * (n / (600 * L) + 1) ≤ 600 * L * (n / (800 * L) + Bad.card) :=
            Nat.mul_le_mul_left _ hge
          nlinarith
        omega
      let eGood : Fin GoodIdx.card ≃ GoodIdx :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe GoodIdx)).symm
      let P : Fin (n / (800 * L)) → Fin (L + 1) → Fin (n + 1) := fun a j =>
        (P' (eGood ⟨a.val, lt_of_lt_of_le a.isLt hGood_lb⟩).val j).val
      refine ⟨P, ?_, ?_, ?_⟩
      · intro a₁ b₁ a₂ b₂ hEq
        have h := hP'_inj _ _ _ _ (Subtype.ext hEq)
        have ha : (⟨a₁.val, lt_of_lt_of_le a₁.isLt hGood_lb⟩ : Fin GoodIdx.card) =
            ⟨a₂.val, lt_of_lt_of_le a₂.isLt hGood_lb⟩ :=
          eGood.injective (Subtype.ext h.1)
        have ha_val : a₁.val = a₂.val := congrArg (fun x : Fin GoodIdx.card => x.val) ha
        exact ⟨Fin.ext ha_val, h.2⟩
      · intro a j
        exact hP'_adj _ j
      · intro a j _ _
        dsimp only [P]
        set gIdx := eGood ⟨a.val, lt_of_lt_of_le a.isLt hGood_lb⟩
        have hnotbad : (P' gIdx.val j).val ∉ Bad := by
          have hg := (Finset.mem_filter.mp gIdx.property).2
          exact fun hmem => hg ⟨j, hmem⟩
        have hno_out : ∀ w, T.Adj (P' gIdx.val j).val w → w ∈ core := by
          intro w hw
          by_contra hnc
          exact hnotbad (Finset.mem_filter.mpr ⟨(P' gIdx.val j).property, w, hnc, hw⟩)
        have hdeg_eq : T.degree (P' gIdx.val j).val = T'.degree (P' gIdx.val j) := by
          rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
          refine Eq.symm (Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_)
          · intro y hy; rw [mem_neighborFinset] at hy ⊢; exact hy
          · intro y₁ _ y₂ _ h; exact Subtype.ext h
          · intro w hw
            rw [mem_neighborFinset] at hw
            exact ⟨⟨w, hno_out w hw⟩, (mem_neighborFinset _ _ _).mpr hw, rfl⟩
        rw [hdeg_eq]
        exact hP'_deg gIdx.val j

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2001.02665».kotzig_conjecture_large := by
  intro h1 h2 h3
  filter_upwards [h1, h2, h3, Filter.eventually_ge_atTop (2 ^ 144)] with n hn1 hn2 hn3 hn_big
  intro V _ T hT hcard
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcard_fin : T.edgeFinset.card = n := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
    exact hcard
  have hVcard : Fintype.card V = n + 1 := by
    have := hT.card_edgeFinset
    omega
  let e : V ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hVcard
  let T₀ : SimpleGraph (Fin (n + 1)) := T.map e.toEmbedding
  have hiso : T ≃g T₀ := SimpleGraph.Iso.map e T
  have hT₀ : T₀.IsTree := hiso.isTree_iff.mp hT
  have hrain0 : ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁ u₂ v₂, T₀.Adj u₁ v₁ → T₀.Adj u₂ v₂ →
        (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
        s(u₁, v₁) = s(u₂, v₂) := by
    rcases mps_case_division hn_big T₀ hT₀ with hC | ⟨hgt, hA⟩ | ⟨hgt, hB⟩
    · exact hn3 T₀ hT₀ hC
    · exact hn1 T₀ hT₀ hgt hA
    · exact hn2 T₀ hT₀ hgt hB
  obtain ⟨g₀, hg₀⟩ := hrain0
  let g : V ↪ Fin (2 * n + 1) := e.toEmbedding.trans g₀
  refine rosa_kotzig_cyclic T hcard g ?_
  intro u₁ v₁ u₂ v₂ h1' h2' hdiff
  have h1'' : T₀.Adj (e u₁) (e v₁) := (SimpleGraph.map_adj _ _ _ _).mpr ⟨u₁, v₁, h1', rfl, rfl⟩
  have h2'' : T₀.Adj (e u₂) (e v₂) := (SimpleGraph.map_adj _ _ _ _).mpr ⟨u₂, v₂, h2', rfl, rfl⟩
  have hsym := hg₀ (e u₁) (e v₁) (e u₂) (e v₂) h1'' h2'' hdiff
  rw [Sym2.eq_iff] at hsym ⊢
  rcases hsym with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨e.injective ha, e.injective hb⟩
  · exact Or.inr ⟨e.injective ha, e.injective hb⟩

end OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1
