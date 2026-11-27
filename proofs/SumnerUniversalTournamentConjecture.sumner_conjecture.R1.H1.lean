import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Standalone Lean 4 proof of Dross-Havet (2021) Theorem 4 & Corollary 5:
Every oriented tree of order n with k leaves embeds in every tournament of order m
with 2 * m >= 3 * n + 3 * k - 4. In particular, when 3 * k <= n, every oriented tree
embeds in every tournament of order 2 * n - 2.
-/

namespace ProofWork.DrossHavet

open SimpleGraph Digraph SumnerUniversalTournamentConjecture

lemma adj_ne_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (h : D.Adj u v) : u ≠ v :=
  T.ne_of_adj (hO.1 u v h)

lemma not_adj_rev_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (h : D.Adj u v) : ¬ D.Adj v u :=
  (hO.2 u v (hO.1 u v h)).mp h

lemma adj_or_rev_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (hT : T.Adj u v) : D.Adj u v ∨ D.Adj v u := by
  by_cases h : D.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hO.2 u v hT).not.mp h))

lemma adj_or_rev_of_isTournament {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (hne : u ≠ v) : G.Adj u v ∨ G.Adj v u := by
  by_cases h : G.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hG.2 u v hne).not.mp h))

lemma embeds_of_le_subdigraph {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    {D1 D2 : Digraph W} {G : Digraph V} (hle : ∀ u v, D1.Adj u v → D2.Adj u v)
    (hemb : Embeds D2 G) : Embeds D1 G := by
  obtain ⟨f, hf⟩ := hemb
  exact ⟨⟨f.toFun, fun h => f.map_adj' (hle _ _ h)⟩, hf⟩

lemma isTournament_induce {V : Type*} {G : Digraph V} (hG : G.IsTournament) (S : Finset V) :
    (⟨fun u v : S => G.Adj u.1 v.1⟩ : Digraph S).IsTournament :=
  ⟨fun u => hG.1 u.1, fun u v huv => hG.2 u.1 v.1 (fun h => huv (Subtype.ext h))⟩

lemma card_filter_add_card_filter_not_eq {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2; exact hx2.2 hx1.2


-- ============================================================================

lemma median_right_of_max {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hG : G.IsTournament)
    (σ : Fin (Fintype.card V) ≃ V)
    (hmax : ∀ σ' : Fin (Fintype.card V) ≃ V,
      ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
        (fun p => p.1 < p.2 ∧ G.Adj (σ' p.1) (σ' p.2))).card ≤
      ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
        (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))).card)
    (i j : Fin (Fintype.card V)) (hij : i < j) :
    j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card := by
  classical
  let m := Fintype.card V
  have hij_val : i.val < j.val := hij
  have hj_lt : j.val < m := j.isLt
  let toF : Fin m → Fin m := fun k =>
    if k.val < i.val then k
    else if hkj : k.val < j.val then ⟨k.val + 1, by omega⟩
    else if k.val = j.val then i
    else k
  let invF : Fin m → Fin m := fun k =>
    if k.val < i.val then k
    else if k.val = i.val then j
    else if k.val ≤ j.val then ⟨k.val - 1, by omega⟩
    else k
  have htoF_val : ∀ k : Fin m, (toF k).val =
      if k.val < i.val then k.val
      else if k.val < j.val then k.val + 1
      else if k.val = j.val then i.val
      else k.val := fun k => by dsimp [toF]; split_ifs <;> rfl
  have hinvF_val : ∀ k : Fin m, (invF k).val =
      if k.val < i.val then k.val
      else if k.val = i.val then j.val
      else if k.val ≤ j.val then k.val - 1
      else k.val := fun k => by dsimp [invF]; split_ifs <;> rfl
  have hleft : Function.LeftInverse invF toF := by
    intro k; apply Fin.ext
    rw [hinvF_val, htoF_val]
    split_ifs <;> omega
  have hright : Function.RightInverse invF toF := by
    intro k; apply Fin.ext
    rw [htoF_val, hinvF_val]
    split_ifs <;> omega
  let τ : Fin m ≃ Fin m := ⟨toF, invF, hleft, hright⟩
  let σ' : Fin m ≃ V := τ.trans σ
  have hle := hmax σ'
  let A := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))
  let A' := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ' p.1) (σ' p.2))
  let F_i := (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))
  let B_i := (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j ∧ G.Adj (σ k) (σ i))
  have hFB_sum : F_i.card + B_i.card = j.val - i.val := by
    have hdisj : Disjoint F_i B_i := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [F_i, B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
      have hne_ik : σ i ≠ σ k := fun h => absurd (σ.injective h) (ne_of_lt hk1.1)
      exact (hG.2 _ _ hne_ik).mp hk1.2.2 hk2.2.2
    have hunion : F_i ∪ B_i = (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j) := by
      ext k
      simp only [F_i, B_i, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have hne_ik : σ i ≠ σ k := fun h => absurd (σ.injective h) (ne_of_lt h1)
        rcases adj_or_rev_of_isTournament hG hne_ik with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hbij : ((Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j)).card =
        (Finset.Ioc i.val j.val).card := by
      refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_Ioc.mpr ⟨hk.1, hk.2⟩
      · intro a _ b _ h; exact Fin.ext h
      · intro n hn
        have ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
        refine ⟨⟨n, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h1, h2⟩
    rw [hbij, Nat.card_Ioc]
  let A_flip := A.filter (fun p => p.1 = i ∧ p.2 ≤ j)
  let A_keep := A.filter (fun p => ¬ (p.1 = i ∧ p.2 ≤ j))
  let A'_flip := A'.filter (fun p => p.2 = j ∧ i ≤ p.1)
  let A'_keep := A'.filter (fun p => ¬ (p.2 = j ∧ i ≤ p.1))
  have hA_split : A.card = A_flip.card + A_keep.card :=
    (card_filter_add_card_filter_not_eq A _).symm
  have hA'_split : A'.card = A'_flip.card + A'_keep.card :=
    (card_filter_add_card_filter_not_eq A' _).symm
  have hflip1 : A_flip.card = F_i.card := by
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [A_flip, A, F_i, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, rfl, hle_j⟩
      exact ⟨hlt, hle_j, hadj⟩
    · intro p hp q hq h
      simp only [A_flip, Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.1.trans hq.2.1.symm) h
    · intro k hk
      simp only [F_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact ⟨(i, k), by simp [A_flip, A, hk.1, hk.2.1, hk.2.2], rfl⟩
  have hτj : τ j = i := by
    apply Fin.ext; change (toF j).val = i.val; rw [htoF_val]; split_ifs <;> omega
  have hflip2 : A'_flip.card = B_i.card := by
    refine Finset.card_bij (fun p _ => τ p.1) ?_ ?_ ?_
    · intro p hp
      simp only [A'_flip, A', B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, h2j, hi1⟩
      have h1_lt : p.1.val < j.val := h2j ▸ hlt
      have h1_ge : i.val ≤ p.1.val := hi1
      have hv : (τ p.1).val = (toF p.1).val := rfl
      rw [htoF_val] at hv
      have hτ1 : i < τ p.1 ∧ τ p.1 ≤ j := by
        constructor <;> (simp only [Fin.lt_def, Fin.le_def]; split_ifs at hv <;> omega)
      refine ⟨hτ1.1, hτ1.2, ?_⟩
      simpa [σ', Equiv.trans_apply, h2j, hτj] using hadj
    · intro p hp q hq h
      simp only [A'_flip, Finset.mem_filter] at hp hq
      exact Prod.ext (τ.injective h) (hp.2.1.trans hq.2.1.symm)
    · intro k hk
      simp only [B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨(τ.symm k, j), ?_, τ.apply_symm_apply k⟩
      have h1 : i.val < k.val := hk.1
      have h2 : k.val ≤ j.val := hk.2.1
      have hv : (τ.symm k).val = (invF k).val := rfl
      rw [hinvF_val] at hv
      have hsk1 : i ≤ τ.symm k := by
        change i.val ≤ (τ.symm k).val; split_ifs at hv <;> omega
      have hsk2 : τ.symm k < j := by
        change (τ.symm k).val < j.val; split_ifs at hv <;> omega
      simp only [A'_flip, A', Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨hsk2, ?_⟩, hsk1⟩
      simpa [σ', Equiv.trans_apply, hτj] using hk.2.2
  have hkeep : A_keep.card = A'_keep.card := by
    refine Finset.card_bij (fun p _ => (τ.symm p.1, τ.symm p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [A_keep, A, A'_keep, A', Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, hnot⟩
      have hlt_val : p.1.val < p.2.val := hlt
      have hnot' : ¬ (p.1.val = i.val ∧ p.2.val ≤ j.val) := fun ⟨h1, h2⟩ =>
        hnot ⟨Fin.ext h1, h2⟩
      have hv1 : (τ.symm p.1).val = (invF p.1).val := rfl
      have hv2 : (τ.symm p.2).val = (invF p.2).val := rfl
      rw [hinvF_val] at hv1 hv2
      have hlt' : τ.symm p.1 < τ.symm p.2 := by
        change (τ.symm p.1).val < (τ.symm p.2).val
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      have hnot2 : ¬ (τ.symm p.2 = j ∧ i ≤ τ.symm p.1) := by
        rintro ⟨h1, h2⟩
        have h1v : (τ.symm p.2).val = j.val := congrArg Fin.val h1
        have h2v : i.val ≤ (τ.symm p.1).val := h2
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      exact ⟨⟨hlt', by simpa [σ', Equiv.trans_apply] using hadj⟩, hnot2⟩
    · intro p _ q _ h
      exact Prod.ext (τ.symm.injective (congrArg Prod.fst h))
        (τ.symm.injective (congrArg Prod.snd h))
    · intro q hq
      simp only [A'_keep, A', Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rcases hq with ⟨⟨hlt, hadj⟩, hnot⟩
      refine ⟨(τ q.1, τ q.2), ?_, by simp⟩
      simp only [A_keep, A, Finset.mem_filter, Finset.mem_univ, true_and]
      have hlt_val : q.1.val < q.2.val := hlt
      have hnot' : ¬ (q.2.val = j.val ∧ i.val ≤ q.1.val) := fun ⟨h1, h2⟩ =>
        hnot ⟨Fin.ext h1, h2⟩
      have hv1 : (τ q.1).val = (toF q.1).val := rfl
      have hv2 : (τ q.2).val = (toF q.2).val := rfl
      rw [htoF_val] at hv1 hv2
      have hlt1 : τ q.1 < τ q.2 := by
        change (τ q.1).val < (τ q.2).val
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      have hnot1 : ¬ (τ q.1 = i ∧ τ q.2 ≤ j) := by
        rintro ⟨h1, h2⟩
        have h1v : (τ q.1).val = i.val := congrArg Fin.val h1
        have h2v : (τ q.2).val ≤ j.val := h2
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      exact ⟨⟨hlt1, by simpa [σ', Equiv.trans_apply] using hadj⟩, hnot1⟩
  change A'.card ≤ A.card at hle
  change j.val - i.val ≤ 2 * F_i.card
  omega

lemma exists_median_order {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hG : G.IsTournament) :
    ∃ σ : Fin (Fintype.card V) ≃ V,
      (∀ i j : Fin (Fintype.card V), i < j →
        j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card) ∧
      (∀ i j : Fin (Fintype.card V), i < j →
        j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) := by
  classical
  let m := Fintype.card V
  let fwd : (Fin m ≃ V) → ℕ := fun σ =>
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))).card
  have hne : (Finset.univ : Finset (Fin m ≃ V)).Nonempty :=
    ⟨(Fintype.equivFin V).symm, Finset.mem_univ _⟩
  obtain ⟨σ, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m ≃ V)) fwd hne
  refine ⟨σ, fun i j hij => median_right_of_max G hG σ (fun σ' => hmax σ' (Finset.mem_univ _)) i j hij, ?_⟩
  let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
  have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun u v huv => hG.2 v u huv.symm⟩
  let revFin : Fin m ≃ Fin m := Fin.revPerm
  let σrev : Fin m ≃ V := revFin.trans σ
  have hfwd_eq : ∀ τ : Fin m ≃ V,
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (τ p.1) (τ p.2))).card =
      fwd (revFin.trans τ) := by
    intro τ
    refine Finset.card_bij (fun p _ => (revFin p.2, revFin p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨Fin.rev_lt_rev.mpr hp.1, ?_⟩
      simpa [revFin, Grev, Equiv.trans_apply] using hp.2
    · intro p _ q _ h
      exact Prod.ext (revFin.injective (congrArg Prod.snd h))
        (revFin.injective (congrArg Prod.fst h))
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(revFin q.2, revFin q.1), ?_, by simp [revFin]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Fin.rev_lt_rev.mpr hq.1, ?_⟩
      simpa [revFin, Grev, Equiv.trans_apply] using hq.2
  have hmax_rev : ∀ τ : Fin m ≃ V,
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (τ p.1) (τ p.2))).card ≤
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (σrev p.1) (σrev p.2))).card := by
    intro τ
    rw [hfwd_eq τ, hfwd_eq σrev]
    have hinv : revFin.trans σrev = σ := by
      ext k; simp [σrev, revFin, Equiv.trans_apply]
    rw [hinv]
    exact hmax (revFin.trans τ) (Finset.mem_univ _)
  intro i j hij
  have hij_rev : revFin j < revFin i := Fin.rev_lt_rev.mpr hij
  have hstep := median_right_of_max Grev hGrev σrev hmax_rev (revFin j) (revFin i) hij_rev
  have hdiff : (revFin i).val - (revFin j).val = j.val - i.val := by
    simp only [revFin, Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt; have := j.isLt; have : i.val < j.val := hij; omega
  have hcard_eq : (Finset.univ.filter (fun k : Fin m =>
      revFin j < k ∧ k ≤ revFin i ∧ Grev.Adj (σrev (revFin j)) (σrev k))).card =
    (Finset.univ.filter (fun k : Fin m => i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card := by
    refine Finset.card_bij (fun k _ => revFin k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨Fin.rev_le_rev.mp (by simpa [revFin] using hk.2.1),
        Fin.rev_lt_rev.mp (by simpa [revFin] using hk.1), ?_⟩
      simpa [σrev, revFin, Grev, Equiv.trans_apply] using hk.2.2
    · intro a _ b _ h; exact revFin.injective h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨revFin k, ?_, by simp [revFin]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Fin.rev_lt_rev.mpr hk.2.1, Fin.rev_le_rev.mpr hk.1, ?_⟩
      simpa [σrev, revFin, Grev, Equiv.trans_apply] using hk.2.2
  rw [hdiff, hcard_eq] at hstep
  exact hstep

lemma median_adj_succ {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (i : Fin (Fintype.card V)) (hi : i.val + 1 < Fintype.card V) :
    G.Adj (σ i) (σ ⟨i.val + 1, hi⟩) := by
  let j : Fin (Fintype.card V) := ⟨i.val + 1, hi⟩
  have hij : i < j := by change i.val < i.val + 1; omega
  have h := hR i j hij
  have hjv : j.val = i.val + 1 := rfl
  have hpos : 0 < (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card := by
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hkj : k = ⟨i.val + 1, hi⟩ := Fin.ext (by
    have h1 : i.val < k.val := hk.1
    have h2 : k.val ≤ j.val := hk.2.1
    omega)
  simpa [hkj] using hk.2.2

-- ============================================================================
-- MODULE 3: Online Greedy Branching Theorem + Prefix Refinement (Theorem 4.1)
-- ============================================================================

lemma branching_ancestors_comparable {W : Type*} {D : Digraph W}
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {x1 x2 w : W} (h1 : Relation.ReflTransGen D.Adj x1 w)
    (h2 : Relation.ReflTransGen D.Adj x2 w) :
    Relation.ReflTransGen D.Adj x1 x2 ∨ Relation.ReflTransGen D.Adj x2 x1 := by
  induction h1 with
  | refl => exact Or.inr h2
  | @tail b c h1b hbc ih =>
    cases h2 with
    | refl => exact Or.inl (Relation.ReflTransGen.tail h1b hbc)
    | tail h2b' hb'c =>
      rename_i b'
      have hbb' : b = b' := hInDeg c b b' hbc hb'c
      subst hbb'
      exact ih h2b'

lemma exists_smallest_subset {m : ℕ} (A : Finset (Fin m)) :
    ∀ (d : ℕ), d ≤ A.card →
      ∃ S ⊆ A, S.card = d ∧ ∀ x ∈ S, ∀ y ∈ A, y ∉ S → x < y := by
  intro d
  induction d with
  | zero =>
    intro _; exact ⟨∅, Finset.empty_subset A, rfl, fun _ hx => absurd hx (Finset.notMem_empty _)⟩
  | succ d' ih =>
    intro hle
    obtain ⟨S', hS'sub, hS'card, hS'min⟩ := ih (by omega)
    have hne : (A \ S').Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS'sub]
      omega
    let z := (A \ S').min' hne
    have hz_mem : z ∈ A \ S' := Finset.min'_mem (A \ S') hne
    have hzA : z ∈ A := (Finset.mem_sdiff.mp hz_mem).1
    have hznot : z ∉ S' := (Finset.mem_sdiff.mp hz_mem).2
    refine ⟨insert z S', Finset.insert_subset_iff.mpr ⟨hzA, hS'sub⟩,
      by rw [Finset.card_insert_of_notMem hznot, hS'card], ?_⟩
    intro x hx y hyA hynot
    have hy_not_z : y ≠ z := fun h => hynot (h ▸ Finset.mem_insert_self z S')
    have hy_not_S' : y ∉ S' := fun h => hynot (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hx with rfl | hxS'
    · have hle_zy : z ≤ y := Finset.min'_le (A \ S') y (Finset.mem_sdiff.mpr ⟨hyA, hy_not_S'⟩)
      exact lt_of_le_of_ne hle_zy hy_not_z.symm
    · exact hS'min x hxS' y hyA hy_not_S'

-- Dross-Havet (2021) Theorem 12 with online sibling oracle!
lemma online_greedy_out_arborescence
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank u < rank v)
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    (r : W) (hroot : ∀ w : W, (∀ u, ¬ D.Adj u w) ↔ w = r)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      Fintype.card V + 1)
    (oracle : ∀ (a : W) (S : Finset (Fin (Fintype.card V))),
      S.card = (Finset.univ.filter (fun c : W => D.Adj a c)).card →
      ↥(Finset.univ.filter (fun c : W => D.Adj a c)) ≃ ↥S) :
    ∃ (f : W → Fin (Fintype.card V)),
      Function.Injective f ∧
      (∀ (hmpos : 0 < Fintype.card V), f r = ⟨0, hmpos⟩) ∧
      (∀ u v : W, D.Adj u v → G.Adj (σ (f u)) (σ (f v))) ∧
      (∀ (a : W), ∃ (S : Finset (Fin (Fintype.card V)))
        (hSc : S.card = (Finset.univ.filter (fun c : W => D.Adj a c)).card),
        ∀ (c : W) (hc : D.Adj a c),
          f c = (oracle a S hSc ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩).1) := by
  classical
  let m := Fintype.card V
  obtain ⟨rank, hrank⟩ := hRank
  have hW_pos : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr ⟨r⟩
  have hk_pos : 1 ≤ (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card := by
    obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image (Finset.univ : Finset W) rank ⟨r, Finset.mem_univ _⟩
    refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩⟩
    have := hrank w u hu; have := hwmax u (Finset.mem_univ _); omega
  have hm_pos : 0 < m := by omega
  have hbuild : ∀ t : ℕ, t ≤ m →
      ∃ g : Fin m → Option W,
        g ⟨0, hm_pos⟩ = some r ∧
        (∀ i1 i2 : Fin m, ∀ w : W, g i1 = some w → g i2 = some w → i1 = i2) ∧
        (∀ j : Fin m, ∀ w : W, g j = some w →
          w = r ∨ ∃ i : Fin m, i.val < t ∧ i < j ∧ ∃ p : W, g i = some p ∧ D.Adj p w ∧ G.Adj (σ i) (σ j)) ∧
        (∀ i : Fin m, i.val < t → ∀ a : W, g i = some a →
          (∃ (S : Finset (Fin m)) (hSc : S.card = (Finset.univ.filter (fun c : W => D.Adj a c)).card),
            (∀ s ∈ S, i < s ∧ G.Adj (σ i) (σ s)) ∧
            (∀ (c : W) (hc : D.Adj a c),
              g (oracle a S hSc ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩).1 = some c) ∧
            (∀ j : Fin m, i < j → G.Adj (σ i) (σ j) →
              (g j = none ∨ ∃ w : W, g j = some w ∧ ∃ i' : Fin m, i < i' ∧ i' < j ∧ ∃ p : W, g i' = some p ∧ D.Adj p w) →
              ∀ s ∈ S, s < j)) ∨
          ((∃ c : W, D.Adj a c ∧ ∀ j : Fin m, g j ≠ some c) ∧
            (∀ j : Fin m, i < j → G.Adj (σ i) (σ j) →
              ∃ w : W, g j = some w ∧
                (w = r ∨ ∃ i' : Fin m, i' ≤ i ∧ i' < j ∧ ∃ p : W, g i' = some p ∧ D.Adj p w)))) := by
    intro t
    induction t with
    | zero =>
      intro _
      let g0 : Fin m → Option W := fun i => if i.val = 0 then some r else none
      refine ⟨g0, by simp [g0], ?_, ?_, ?_⟩
      · intro i1 i2 w h1 h2
        dsimp only [g0] at h1 h2
        split_ifs at h1 h2
        all_goals simp_all [Fin.ext_iff]
      · intro j w hj
        dsimp only [g0] at hj
        split_ifs at hj
        all_goals simp_all
      · intro i hi; omega
    | succ t' ih =>
      intro ht
      obtain ⟨g, hroot0, hinj, hpar, hproc⟩ := ih (by omega)
      let it : Fin m := ⟨t', by omega⟩
      cases hgit : g it with
      | none =>
        refine ⟨g, hroot0, hinj, ?_, ?_⟩
        · intro j w hj
          rcases hpar j w hj with rfl | ⟨i, hit', hij, p, hgi, hDpw, hGij⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨i, by omega, hij, p, hgi, hDpw, hGij⟩
        · intro i hilt a hgia
          by_cases hieq : i.val = t'
          · have hiit : i = it := Fin.ext hieq
            rw [hiit, hgit] at hgia; cases hgia
          · exact hproc i (by omega) a hgia
      | some a =>
        let avail := Finset.univ.filter (fun j : Fin m => it < j ∧ g j = none ∧ G.Adj (σ it) (σ j))
        let Ch := Finset.univ.filter (fun c : W => D.Adj a c)
        have hCh_fresh : ∀ c ∈ Ch, ∀ j : Fin m, g j ≠ some c := by
          intro c hc j hgj
          have hDac : D.Adj a c := (Finset.mem_filter.mp hc).2
          rcases hpar j c hgj with hcr | ⟨i, hit', _, p, hgi, hDpc, _⟩
          · exact ((hroot c).mpr hcr) a hDac
          · have hpa : p = a := hInDeg c p a hDpc hDac
            subst hpa
            have hi_eq : i = it := hinj i it p hgi hgit
            have hv : i.val = t' := congrArg Fin.val hi_eq
            omega
        have hstep_lift : ∀ (S : Finset (Fin m)) (hSsub : S ⊆ avail)
            (assign : ↥S → W) (hassign_inj : Function.Injective assign)
            (hassign_Ch : ∀ s : ↥S, assign s ∈ Ch),
            let g' : Fin m → Option W := fun j => if hj : j ∈ S then some (assign ⟨j, hj⟩) else g j
            g' ⟨0, hm_pos⟩ = some r ∧
            (∀ i1 i2 : Fin m, ∀ w : W, g' i1 = some w → g' i2 = some w → i1 = i2) ∧
            (∀ j : Fin m, ∀ w : W, g' j = some w →
              w = r ∨ ∃ i : Fin m, i.val < t' + 1 ∧ i < j ∧ ∃ p : W, g' i = some p ∧ D.Adj p w ∧ G.Adj (σ i) (σ j)) ∧
            (∀ i : Fin m, i.val < t' → ∀ a0 : W, g' i = some a0 →
              (∃ (S0 : Finset (Fin m)) (hSc0 : S0.card = (Finset.univ.filter (fun c : W => D.Adj a0 c)).card),
                (∀ s ∈ S0, i < s ∧ G.Adj (σ i) (σ s)) ∧
                (∀ (c : W) (hc : D.Adj a0 c),
                  g' (oracle a0 S0 hSc0 ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩).1 = some c) ∧
                (∀ j : Fin m, i < j → G.Adj (σ i) (σ j) →
                  (g' j = none ∨ ∃ w : W, g' j = some w ∧ ∃ i' : Fin m, i < i' ∧ i' < j ∧ ∃ p : W, g' i' = some p ∧ D.Adj p w) →
                  ∀ s ∈ S0, s < j)) ∨
              ((∃ c : W, D.Adj a0 c ∧ ∀ j : Fin m, g' j ≠ some c) ∧
                (∀ j : Fin m, i < j → G.Adj (σ i) (σ j) →
                  ∃ w : W, g' j = some w ∧
                    (w = r ∨ ∃ i' : Fin m, i' ≤ i ∧ i' < j ∧ ∃ p : W, g' i' = some p ∧ D.Adj p w)))) := by
          intro S hSsub assign hassign_inj hassign_Ch g'
          have hS_none : ∀ s ∈ S, g s = none := fun s hs => (Finset.mem_filter.mp (hSsub hs)).2.2.1
          have hS_gt : ∀ s ∈ S, it < s := fun s hs => (Finset.mem_filter.mp (hSsub hs)).2.1
          have hS_adj : ∀ s ∈ S, G.Adj (σ it) (σ s) := fun s hs => (Finset.mem_filter.mp (hSsub hs)).2.2.2
          have hg'_of_some : ∀ j w, g j = some w → g' j = some w := by
            intro j w hj
            have hnot : j ∉ S := fun h => by rw [hS_none j h] at hj; cases hj
            simp only [g', hnot, ↓reduceDIte, hj]
          have hg'_it : g' it = some a := hg'_of_some it a hgit
          have hg'_0 : g' ⟨0, hm_pos⟩ = some r := hg'_of_some ⟨0, hm_pos⟩ r hroot0
          have hg'_inj : ∀ i1 i2 : Fin m, ∀ w : W, g' i1 = some w → g' i2 = some w → i1 = i2 := by
            intro i1 i2 w h1 h2
            by_cases hs1 : i1 ∈ S <;> by_cases hs2 : i2 ∈ S
            · simp only [g', hs1, hs2, ↓reduceDIte] at h1 h2
              have heq := hassign_inj ((Option.some.inj h1).trans (Option.some.inj h2).symm)
              exact congrArg (fun z : ↥S => z.1) heq
            · simp only [g', hs1, hs2, ↓reduceDIte] at h1 h2
              have hw : w = assign ⟨i1, hs1⟩ := (Option.some.inj h1).symm
              exact absurd (hw ▸ h2) (hCh_fresh (assign ⟨i1, hs1⟩) (hassign_Ch ⟨i1, hs1⟩) i2)
            · simp only [g', hs1, hs2, ↓reduceDIte] at h1 h2
              have hw : w = assign ⟨i2, hs2⟩ := (Option.some.inj h2).symm
              exact absurd (hw ▸ h1) (hCh_fresh (assign ⟨i2, hs2⟩) (hassign_Ch ⟨i2, hs2⟩) i1)
            · simp only [g', hs1, hs2, ↓reduceDIte] at h1 h2
              exact hinj i1 i2 w h1 h2
          have hg'_par : ∀ j : Fin m, ∀ w : W, g' j = some w →
              w = r ∨ ∃ i : Fin m, i.val < t' + 1 ∧ i < j ∧ ∃ p : W, g' i = some p ∧ D.Adj p w ∧ G.Adj (σ i) (σ j) := by
            intro j w hj
            by_cases hs : j ∈ S
            · simp only [g', hs, ↓reduceDIte] at hj
              have hw : assign ⟨j, hs⟩ = w := Option.some.inj hj
              refine Or.inr ⟨it, by dsimp only [it]; omega, hS_gt j hs, a, hg'_it, ?_, hS_adj j hs⟩
              rw [← hw]; exact (Finset.mem_filter.mp (hassign_Ch ⟨j, hs⟩)).2
            · simp only [g', hs, ↓reduceDIte] at hj
              rcases hpar j w hj with rfl | ⟨i, hit', hij, p, hgi, hDpw, hGij⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨i, by omega, hij, p, hg'_of_some i p hgi, hDpw, hGij⟩
          refine ⟨hg'_0, hg'_inj, hg'_par, ?_⟩
          intro i hit' a0 hgia0
          have hi_notS : i ∉ S := fun hs => by
            have := hS_gt i hs; have : t' < i.val := this; omega
          simp only [g', hi_notS, ↓reduceDIte] at hgia0
          rcases hproc i hit' a0 hgia0 with ⟨S0, hSc0, hS0_gt, hS0_or, hS0_min⟩ | ⟨⟨c0, hDc0, hc0_un⟩, hpart_cov⟩
          · left
            refine ⟨S0, hSc0, hS0_gt,
              fun c hc => hg'_of_some _ c (hS0_or c hc), ?_⟩
            intro j hij hGij hcond s0 hs0
            rcases hcond with hnone | ⟨w, hgjw, i', hii', hi'j, p, hgi'p, hDpw⟩
            · have hgj_none : g j = none := by
                by_cases hsj : j ∈ S
                · simp only [g', hsj, ↓reduceDIte] at hnone; cases hnone
                · simpa [g', hsj] using hnone
              exact hS0_min j hij hGij (Or.inl hgj_none) s0 hs0
            · by_cases hsj : j ∈ S
              · exact hS0_min j hij hGij (Or.inl (hS_none j hsj)) s0 hs0
              · simp only [g', hsj, ↓reduceDIte] at hgjw
                rcases hpar j w hgjw with rfl | ⟨i1, _, hi1j, p1, hgi1, hDp1w, _⟩
                · exact absurd hDpw ((hroot w).mpr rfl p)
                · have hp_eq : p1 = p := hInDeg w p1 p hDp1w hDpw
                  subst hp_eq
                  have hi1_eq : i1 = i' := hg'_inj i1 i' p1 (hg'_of_some i1 p1 hgi1) hgi'p
                  subst hi1_eq
                  exact hS0_min j hij hGij (Or.inr ⟨w, hgjw, i1, hii', hi1j, p1, hgi1, hDp1w⟩) s0 hs0
          · right
            refine ⟨⟨c0, hDc0, ?_⟩, ?_⟩
            · intro j hgj
              by_cases hsj : j ∈ S
              · simp only [g', hsj, ↓reduceDIte] at hgj
                have hc0_eq : assign ⟨j, hsj⟩ = c0 := Option.some.inj hgj
                have hDac0 : D.Adj a c0 := hc0_eq ▸ (Finset.mem_filter.mp (hassign_Ch ⟨j, hsj⟩)).2
                have ha_eq : a0 = a := hInDeg c0 a0 a hDc0 hDac0
                subst ha_eq
                have hi_eq : i = it := hinj i it a0 hgia0 hgit
                have hv : i.val = t' := congrArg Fin.val hi_eq
                omega
              · simp only [g', hsj, ↓reduceDIte] at hgj
                exact hc0_un j hgj
            · intro j hij hGij
              obtain ⟨w, hgj, hrest⟩ := hpart_cov j hij hGij
              refine ⟨w, hg'_of_some j w hgj, ?_⟩
              rcases hrest with rfl | ⟨i', hi'i, hi'j, p, hgi', hDpw⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨i', hi'i, hi'j, p, hg'_of_some i' p hgi', hDpw⟩
        by_cases hfit : Ch.card ≤ avail.card
        · obtain ⟨S, hSsub, hScard, hSmin⟩ := exists_smallest_subset avail Ch.card hfit
          let e := oracle a S hScard
          let assign : ↥S → W := fun s => (e.symm s).1
          have hassign_inj : Function.Injective assign := fun s1 s2 h =>
            e.symm.injective (Subtype.ext h)
          have hassign_Ch : ∀ s : ↥S, assign s ∈ Ch := fun s => (e.symm s).2
          obtain ⟨h0', hinj', hpar', hproc_prev⟩ := hstep_lift S hSsub assign hassign_inj hassign_Ch
          let g' : Fin m → Option W := fun j => if hj : j ∈ S then some (assign ⟨j, hj⟩) else g j
          refine ⟨g', h0', hinj', hpar', ?_⟩
          intro i hilt a1 hgia1
          by_cases hilt' : i.val < t'
          · exact hproc_prev i hilt' a1 hgia1
          · have hi_eq : i = it := Fin.ext (by dsimp only [it]; omega)
            subst hi_eq
            have hit_notS : it ∉ S := fun hs => by
              have := (Finset.mem_filter.mp (hSsub hs)).2.1; exact lt_irrefl it this
            simp only [g', hit_notS, ↓reduceDIte, hgit] at hgia1
            have ha1 : a = a1 := Option.some.inj hgia1
            subst ha1
            left
            refine ⟨S, hScard,
              fun s hs => ⟨(Finset.mem_filter.mp (hSsub hs)).2.1, (Finset.mem_filter.mp (hSsub hs)).2.2.2⟩,
              ?_, ?_⟩
            · intro c hc
              have hs_mem : (oracle a S hScard ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩).1 ∈ S :=
                (oracle a S hScard _).2
              dsimp only [g', assign]
              rw [dif_pos hs_mem]
              congr 1
              exact congrArg (fun z : ↥Ch => z.1)
                (e.symm_apply_apply ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩)
            · intro j hitj hGij hcond s hs
              rcases hcond with hnone | ⟨w, hgjw, i', hiti', hi'j, p, hgi'p, hDpw⟩
              · have hgj_notS : j ∉ S := fun hjS => by simp only [g', hjS, ↓reduceDIte] at hnone; cases hnone
                have hgj_none : g j = none := by simpa [g', hgj_notS] using hnone
                exact hSmin s hs j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hitj, hgj_none, hGij⟩) hgj_notS
              · exfalso
                rcases hpar' j w hgjw with rfl | ⟨i1, hi1t, _, p1, hgi1, hDp1w, _⟩
                · exact absurd hDpw ((hroot w).mpr rfl p)
                · have hp_eq : p1 = p := hInDeg w p1 p hDp1w hDpw
                  subst hp_eq
                  have hi1_eq : i1 = i' := hinj' i1 i' p1 hgi1 hgi'p
                  have hv1 : i1.val = i'.val := congrArg Fin.val hi1_eq
                  have hv2 : t' < i'.val := hiti'
                  omega
        · have hlt : avail.card ≤ Ch.card := by omega
          obtain ⟨Ch0, hCh0sub, hCh0card⟩ := Finset.exists_subset_card_eq hlt
          let e0 : avail ≃ Ch0 := Fintype.equivOfCardEq (by simp [hCh0card])
          let assign : ↥avail → W := fun s => (e0 s).1
          have hassign_inj : Function.Injective assign := fun s1 s2 h => e0.injective (Subtype.ext h)
          have hassign_Ch : ∀ s : ↥avail, assign s ∈ Ch := fun s => hCh0sub (e0 s).2
          obtain ⟨h0', hinj', hpar', hproc_prev⟩ :=
            hstep_lift avail (Finset.Subset.refl avail) assign hassign_inj hassign_Ch
          let g' : Fin m → Option W := fun j => if hj : j ∈ avail then some (assign ⟨j, hj⟩) else g j
          refine ⟨g', h0', hinj', hpar', ?_⟩
          intro i hilt a1 hgia1
          by_cases hilt' : i.val < t'
          · exact hproc_prev i hilt' a1 hgia1
          · have hi_eq : i = it := Fin.ext (by dsimp only [it]; omega)
            subst hi_eq
            have hit_notA : it ∉ avail := fun hs => lt_irrefl it (Finset.mem_filter.mp hs).2.1
            simp only [g', hit_notA, ↓reduceDIte, hgit] at hgia1
            have ha1 : a = a1 := Option.some.inj hgia1
            subst ha1
            right
            have hmiss : ∃ c ∈ Ch, c ∉ Ch0 := Finset.exists_mem_notMem_of_card_lt_card (by omega)
            obtain ⟨c0, hc0Ch, hc0not⟩ := hmiss
            refine ⟨⟨c0, (Finset.mem_filter.mp hc0Ch).2, ?_⟩, ?_⟩
            · intro j hgj
              by_cases hjA : j ∈ avail
              · simp only [g', hjA, ↓reduceDIte] at hgj
                have hEq : (e0 ⟨j, hjA⟩).1 = c0 := Option.some.inj hgj
                exact hc0not (hEq ▸ (e0 ⟨j, hjA⟩).2)
              · simp only [g', hjA, ↓reduceDIte] at hgj
                exact hCh_fresh c0 hc0Ch j hgj
            · intro j hitj hGij
              by_cases hjA : j ∈ avail
              · simp only [g', hjA, ↓reduceDIte]
                refine ⟨assign ⟨j, hjA⟩, rfl, Or.inr ⟨it, le_refl _, hitj, a, ?_,
                  (Finset.mem_filter.mp (hassign_Ch ⟨j, hjA⟩)).2⟩⟩
                simp only [hit_notA, ↓reduceDIte, hgit]
              · cases hgj : g j with
                | none =>
                  exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hitj, hgj, hGij⟩) hjA
                | some w =>
                  refine ⟨w, by simp only [g', hjA, ↓reduceDIte, hgj], ?_⟩
                  rcases hpar j w hgj with rfl | ⟨i1, hi1t, hi1j, p1, hgi1, hDp1w, _⟩
                  · exact Or.inl rfl
                  · have hi1_notA : i1 ∉ avail := fun hs => by
                      have : t' < i1.val := (Finset.mem_filter.mp hs).2.1; omega
                    exact Or.inr ⟨i1, by change i1.val ≤ t'; omega, hi1j, p1,
                      by dsimp only [g']; rw [dif_neg hi1_notA]; exact hgi1, hDp1w⟩
  obtain ⟨g, hroot0, hinj, hpar, hproc⟩ := hbuild m (le_refl m)
  have hActive_cov : ∀ (ℓ k : Fin m) (a : W), ℓ < k → g ℓ = some a →
      (∃ c : W, D.Adj a c ∧ ∀ j : Fin m, j ≤ k → g j ≠ some c) →
      ∀ j : Fin m, ℓ < j → j ≤ k → G.Adj (σ ℓ) (σ j) →
      ∃ w : W, g j = some w ∧
        (w = r ∨ ∃ i' : Fin m, i' ≤ ℓ ∧ i' < j ∧ ∃ p : W, g i' = some p ∧ D.Adj p w) := by
    intro ℓ k a hℓk hgℓ ⟨c, hDac, hc_after⟩ j hℓj hjk hGℓj
    rcases hproc ℓ ℓ.isLt a hgℓ with ⟨S, hSc, hS_gt, hS_or, hS_min⟩ | ⟨_, hpart_cov⟩
    · let s0 := oracle a S hSc ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDac⟩⟩
      have hgs0 : g s0.1 = some c := hS_or c hDac
      have hs0_gt_k : k < s0.1 := by
        by_contra hle; push Not at hle
        exact hc_after s0.1 hle hgs0
      have hgj_not_none : g j ≠ none := fun hnone => by
        have hlt := hS_min j hℓj hGℓj (Or.inl hnone) s0.1 s0.2
        have h1 : s0.1.val < j.val := hlt
        have h2 : j.val ≤ k.val := hjk
        have h3 : k.val < s0.1.val := hs0_gt_k
        omega
      cases hgj : g j with
      | none => exact absurd hgj hgj_not_none
      | some w =>
        refine ⟨w, rfl, ?_⟩
        rcases hpar j w hgj with rfl | ⟨i', _, hi'j, p, hgi', hDpw, _⟩
        · exact Or.inl rfl
        · by_cases hi'le : i' ≤ ℓ
          · exact Or.inr ⟨i', hi'le, hi'j, p, hgi', hDpw⟩
          · exfalso
            push Not at hi'le
            have hlt := hS_min j hℓj hGℓj (Or.inr ⟨w, hgj, i', hi'le, hi'j, p, hgi', hDpw⟩) s0.1 s0.2
            have h1 : s0.1.val < j.val := hlt
            have h2 : j.val ≤ k.val := hjk
            have h3 : k.val < s0.1.val := hs0_gt_k
            omega
    · exact hpart_cov j hℓj hGℓj
  have hall_emb : ∀ w : W, ∃ j : Fin m, g j = some w := by
    by_contra hnot_all
    push Not at hnot_all
    let F := Finset.univ.filter (fun j : Fin m => g j = none)
    let Hit := Finset.univ.filter (fun j : Fin m => (g j).isSome)
    let Lout := Finset.univ.filter (fun w : W => ∀ u : W, ¬ D.Adj w u)
    let Lhit := Finset.univ.filter (fun j : Fin m => ∃ w ∈ Lout, g j = some w)
    have hLhit_lt : Lhit.card + 1 ≤ Lout.card := by
      have hex_unemb_leaf : ∃ w ∈ Lout, ∀ j : Fin m, g j ≠ some w := by
        obtain ⟨u0, hu0⟩ := hnot_all
        let Un := Finset.univ.filter (fun w : W => ∀ j : Fin m, g j ≠ some w)
        obtain ⟨w, hwUn, hwmax⟩ := Finset.exists_max_image Un rank
          ⟨u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0⟩⟩
        have hw_no_g : ∀ j : Fin m, g j ≠ some w := (Finset.mem_filter.mp hwUn).2
        refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, hw_no_g⟩
        have hu_un : u ∈ Un := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hju => ?_⟩
          rcases hpar j u hju with hur | ⟨i, _, _, p, hgi, hDpu, _⟩
          · exact ((hroot u).mpr hur) w hu
          · exact hw_no_g i (hInDeg u p w hDpu hu ▸ hgi)
        have := hrank w u hu; have := hwmax u hu_un; omega
      obtain ⟨w0, hw0L, hw0_no⟩ := hex_unemb_leaf
      have hcard_le : Lhit.card ≤ (Lout.erase w0).card := by
        refine Finset.card_le_card_of_injOn (fun j => (g j).getD w0) ?_ ?_
        · intro j hj
          dsimp only
          obtain ⟨w, hwL, hgj⟩ := (Finset.mem_filter.mp hj).2
          have hval : (g j).getD w0 = w := by simp [hgj]
          rw [hval]
          exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun heq => hw0_no j (heq ▸ hgj), hwL⟩)
        · intro j1 hj1 j2 hj2 hEq
          dsimp only at hEq
          obtain ⟨w1, _, hgj1⟩ := (Finset.mem_filter.mp hj1).2
          obtain ⟨w2, _, hgj2⟩ := (Finset.mem_filter.mp hj2).2
          have h1 : (g j1).getD w0 = w1 := by simp [hgj1]
          have h2 : (g j2).getD w0 = w2 := by simp [hgj2]
          rw [h1, h2] at hEq
          exact hinj j1 j2 w1 hgj1 (hEq.symm ▸ hgj2)
      rw [Finset.card_erase_of_mem hw0L] at hcard_le
      have hLout_pos : 1 ≤ Lout.card := hk_pos
      omega
    have hex_act : ∀ k ∈ F, ∃ ℓ : Fin m, ℓ < k ∧ ∃ a : W, g ℓ = some a ∧
        ∃ c : W, D.Adj a c ∧ ∀ j : Fin m, j ≤ k → g j ≠ some c := by
      intro k hk
      obtain ⟨u0, hu0⟩ := hnot_all
      let Unk := Finset.univ.filter (fun w : W => ∀ j : Fin m, j ≤ k → g j ≠ some w)
      obtain ⟨c, hcUnk, hcmin⟩ := Finset.exists_min_image Unk rank
        ⟨u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j _ => hu0 j⟩⟩
      have hc_after : ∀ j : Fin m, j ≤ k → g j ≠ some c := (Finset.mem_filter.mp hcUnk).2
      have hcr : c ≠ r := fun h => hc_after ⟨0, hm_pos⟩ (Nat.zero_le k.val) (h ▸ hroot0)
      have hex_par : ∃ a : W, D.Adj a c := by
        by_contra hno; push Not at hno; exact hcr ((hroot c).mp hno)
      obtain ⟨a, hDac⟩ := hex_par
      have ha_not_Unk : a ∉ Unk := fun haU => by
        have := hrank a c hDac; have := hcmin a haU; omega
      have ha_emb : ∃ ℓ : Fin m, ℓ ≤ k ∧ g ℓ = some a := by
        by_contra hno; push Not at hno
        exact ha_not_Unk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno⟩)
      obtain ⟨ℓ, hℓle, hgℓ⟩ := ha_emb
      have hℓlt : ℓ < k := lt_of_le_of_ne hℓle (fun h => by
        have hgk : g k = none := (Finset.mem_filter.mp hk).2
        rw [h, hgk] at hgℓ; cases hgℓ)
      exact ⟨ℓ, hℓlt, a, hgℓ, c, hDac, hc_after⟩
    have hact_max : ∀ k : Fin m, k ∈ F →
        ∃ ℓ : Fin m, ℓ < k ∧
          (∃ a : W, g ℓ = some a ∧ ∃ c : W, D.Adj a c ∧ ∀ j : Fin m, j ≤ k → g j ≠ some c) ∧
          (∀ ℓ' : Fin m, ℓ' < k →
            (∃ a : W, g ℓ' = some a ∧ ∃ c : W, D.Adj a c ∧ ∀ j : Fin m, j ≤ k → g j ≠ some c) →
            ℓ' ≤ ℓ) := by
      intro k hk
      let S := Finset.univ.filter (fun ℓ : Fin m => ℓ < k ∧
        ∃ a : W, g ℓ = some a ∧ ∃ c : W, D.Adj a c ∧ ∀ j : Fin m, j ≤ k → g j ≠ some c)
      obtain ⟨ℓ0, hℓ0lt, hℓ0act⟩ := hex_act k hk
      have hSne : S.Nonempty := ⟨ℓ0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ0lt, hℓ0act⟩⟩
      let ℓ := S.max' hSne
      have hℓmem := Finset.mem_filter.mp (Finset.max'_mem S hSne)
      exact ⟨ℓ, hℓmem.2.1, hℓmem.2.2, fun ℓ' hℓ'lt hℓ'act =>
        Finset.le_max' S ℓ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ'lt, hℓ'act⟩)⟩
    choose aF haF_lt haF_act haF_max using hact_max
    have hI_bound : ∀ (k : Fin m) (hk : k ∈ F),
        (F.filter (fun j : Fin m => aF k hk < j ∧ j ≤ k)).card ≤
        (Lhit.filter (fun j : Fin m => aF k hk < j ∧ j ≤ k)).card := by
      intro k hk
      let ℓ := aF k hk
      obtain ⟨a0, hgℓ, hact0⟩ := haF_act k hk
      let Np := Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k ∧ G.Adj (σ ℓ) (σ j))
      let Nm := Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k ∧ ¬ G.Adj (σ ℓ) (σ j))
      have hF_sub : F.filter (fun j : Fin m => ℓ < j ∧ j ≤ k) ⊆ Nm := by
        intro j hj
        simp only [F, Nm, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        refine ⟨hj.2.1, hj.2.2, fun hGℓj => ?_⟩
        obtain ⟨w, hgjw, _⟩ := hActive_cov ℓ k a0 (haF_lt k hk) hgℓ hact0 j hj.2.1 hj.2.2 hGℓj
        rw [hj.1] at hgjw; cases hgjw
      have hM2 := hR ℓ k (haF_lt k hk)
      have hcard_int : (Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card = k.val - ℓ.val := by
        have hbij : (Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card =
            (Finset.Ioc ℓ.val k.val).card := by
          refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact Finset.mem_Ioc.mpr ⟨hj.1, hj.2⟩
          · intro j1 _ j2 _ h; exact Fin.ext h
          · intro n hn
            have h1 := (Finset.mem_Ioc.mp hn).1
            have h2 := (Finset.mem_Ioc.mp hn).2
            refine ⟨⟨n, by have := k.isLt; omega⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨by change ℓ.val < n; omega, by change n ≤ k.val; omega⟩
        rw [hbij, Nat.card_Ioc]
      have hsplit : Np.card + Nm.card = k.val - ℓ.val := by
        have h := card_filter_add_card_filter_not_eq
          (Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)) (fun j => G.Adj (σ ℓ) (σ j))
        have heq1 : (Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).filter (fun j => G.Adj (σ ℓ) (σ j)) = Np := by
          ext j; simp only [Np, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        have heq2 : (Finset.univ.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).filter (fun j => ¬ G.Adj (σ ℓ) (σ j)) = Nm := by
          ext j; simp only [Nm, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        rw [heq1, heq2, hcard_int] at h; exact h
      change k.val - ℓ.val ≤ 2 * Np.card at hM2
      have hNm_le_Np : Nm.card ≤ Np.card := by omega
      have hreach_leaf : ∀ (d : ℕ) (j : Fin m) (w : W),
          (∀ u : W, rank u ≤ d + rank w) → ℓ < j → j ≤ k → g j = some w →
          ∃ jL : Fin m, ℓ < jL ∧ jL ≤ k ∧ ∃ wL ∈ Lout, g jL = some wL ∧ Relation.ReflTransGen D.Adj w wL := by
        intro d
        induction d with
        | zero =>
          intro j w hmax hℓj hjk hgj
          refine ⟨j, hℓj, hjk, w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, hgj, .refl⟩
          have := hrank w u hu; have := hmax u; omega
        | succ d' ih =>
          intro j w hmax hℓj hjk hgj
          by_cases hwL : ∀ u : W, ¬ D.Adj w u
          · exact ⟨j, hℓj, hjk, w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwL⟩, hgj, .refl⟩
          · push Not at hwL
            obtain ⟨c, hDwc⟩ := hwL
            have hc_in : ∃ jc : Fin m, jc ≤ k ∧ g jc = some c := by
              by_contra hno; push Not at hno
              have hjlt : j < k := lt_of_le_of_ne hjk (fun heq => by
                have hgk : g k = none := (Finset.mem_filter.mp hk).2
                rw [heq, hgk] at hgj; cases hgj)
              have hle := haF_max k hk j hjlt ⟨w, hgj, c, hDwc, hno⟩
              exact not_lt_of_ge hle hℓj
            obtain ⟨jc, hjck, hgjc⟩ := hc_in
            have hj_lt_jc : j < jc := by
              rcases hpar jc c hgjc with hcr | ⟨i1, _, hi1jc, p1, hgi1, hDp1c, _⟩
              · exact absurd hDwc ((hroot c).mpr hcr w)
              · have hp_eq : p1 = w := hInDeg c p1 w hDp1c hDwc
                subst hp_eq
                have hi1_eq : i1 = j := hinj i1 j p1 hgi1 hgj
                exact hi1_eq ▸ hi1jc
            obtain ⟨jL, hℓjL, hjLk, wL, hwLL, hgjL, hpath⟩ := ih jc c
              (fun u => by have := hrank w c hDwc; have := hmax u; omega)
              (lt_trans hℓj hj_lt_jc) hjck hgjc
            exact ⟨jL, hℓjL, hjLk, wL, hwLL, hgjL, .head hDwc hpath⟩
      have hex_max_rank : ∃ M : ℕ, ∀ u : W, rank u ≤ M := by
        obtain ⟨u, _, humax⟩ := Finset.exists_max_image (Finset.univ : Finset W) rank ⟨r, Finset.mem_univ _⟩
        exact ⟨rank u, fun v => humax v (Finset.mem_univ _)⟩
      obtain ⟨M, hM⟩ := hex_max_rank
      have hNp_map : ∀ j : Fin m, j ∈ Np →
          ∃ jL : Fin m, jL ∈ Lhit.filter (fun x : Fin m => ℓ < x ∧ x ≤ k) ∧
            ∃ w wL : W, g j = some w ∧ g jL = some wL ∧ Relation.ReflTransGen D.Adj w wL := by
        intro j hj
        have hj' := Finset.mem_filter.mp hj
        obtain ⟨w, hgjw, _⟩ := hActive_cov ℓ k a0 (haF_lt k hk) hgℓ hact0 j hj'.2.1 hj'.2.2.1 hj'.2.2.2
        obtain ⟨jL, hℓjL, hjLk, wL, hwLL, hgjL, hpath⟩ :=
          hreach_leaf M j w (fun u => by have := hM u; omega) hj'.2.1 hj'.2.2.1 hgjw
        exact ⟨jL, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, wL, hwLL, hgjL⟩,
          hℓjL, hjLk⟩, w, wL, hgjw, hgjL, hpath⟩
      choose phiL hphiL_mem hphiL_rel using hNp_map
      have hNp_le_L : Np.card ≤ (Lhit.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card := by
        refine Finset.card_le_card_of_injOn (fun j => if hj : j ∈ Np then phiL j hj else j) ?_ ?_
        · intro j hj
          have hj' : j ∈ Np := hj
          dsimp only; rw [dif_pos hj']
          exact Finset.mem_coe.mpr (hphiL_mem j hj')
        · intro j1 hj1 j2 hj2 hEq
          have hj1' : j1 ∈ Np := hj1
          have hj2' : j2 ∈ Np := hj2
          dsimp only at hEq; rw [dif_pos hj1', dif_pos hj2'] at hEq
          obtain ⟨w1, wL1, hgw1, hgwL1, hp1⟩ := hphiL_rel j1 hj1'
          obtain ⟨w2, wL2, hgw2, hgwL2, hp2⟩ := hphiL_rel j2 hj2'
          rw [hEq] at hgwL1
          have hwL_eq : wL1 = wL2 := Option.some.inj (hgwL1.symm.trans hgwL2)
          subst hwL_eq
          have hno_anc : ∀ (ja jb : Fin m) (hja : ja ∈ Np) (hjb : jb ∈ Np) (wa wb : W),
              g ja = some wa → g jb = some wb → wa ≠ wb → ¬ Relation.ReflTransGen D.Adj wa wb := by
            intro ja jb hja hjb wa wb hgwa hgwb hne hpath
            have hjb' := Finset.mem_filter.mp hjb
            obtain ⟨wb', hgwb', hpar_b⟩ :=
              hActive_cov ℓ k a0 (haF_lt k hk) hgℓ hact0 jb hjb'.2.1 hjb'.2.2.1 hjb'.2.2.2
            have hwb_eq : wb' = wb := Option.some.inj (hgwb'.symm.trans hgwb)
            subst hwb_eq
            cases hpath with
            | refl => exact hne rfl
            | tail hwa_u hu_wb =>
              rename_i u
              rcases hpar_b with hwbr | ⟨i', hi'ℓ, _, p', hgi', hDp'⟩
              · exact ((hroot wb').mpr hwbr) u hu_wb
              · have hp'_eq : p' = u := hInDeg wb' p' u hDp' hu_wb
                subst hp'_eq
                have hanc_le : ∀ (x y : W), Relation.ReflTransGen D.Adj x y →
                    ∀ (ix iy : Fin m), g ix = some x → g iy = some y → ix ≤ iy := by
                  intro x y hxy
                  induction hxy with
                  | refl => intro ix iy hx hy; exact (hinj ix iy x hx hy).le
                  | @tail z1 z2 _ hstep ihxy =>
                    intro ix iz2 hx hz2
                    rcases hpar iz2 z2 hz2 with hz2r | ⟨iz1, _, hlt12, pz, hgiz1, hDpz, _⟩
                    · exact absurd hstep ((hroot z2).mpr hz2r z1)
                    · have hpz : pz = z1 := hInDeg z2 pz z1 hDpz hstep
                      subst hpz
                      exact le_trans (ihxy ix iz1 hx hgiz1) hlt12.le
                have hja_le : ja ≤ i' := hanc_le wa p' hwa_u ja i' hgwa hgi'
                have hja_gt : ℓ < ja := (Finset.mem_filter.mp hja).2.1
                exact not_lt_of_ge (le_trans hja_le hi'ℓ) hja_gt
          rcases branching_ancestors_comparable hInDeg hp1 hp2 with h12 | h21
          · by_cases hw12 : w1 = w2
            · exact hinj j1 j2 w1 hgw1 (hw12 ▸ hgw2)
            · exact absurd h12 (hno_anc j1 j2 hj1' hj2' w1 w2 hgw1 hgw2 hw12)
          · by_cases hw21 : w2 = w1
            · exact hinj j1 j2 w1 hgw1 (hw21.symm ▸ hgw2)
            · exact absurd h21 (hno_anc j2 j1 hj2' hj1' w2 w1 hgw2 hgw1 hw21)
      have hF_le_Nm := Finset.card_le_card hF_sub
      change (F.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card ≤
        (Lhit.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card
      omega
    have hF_le_Lhit : ∀ (b : ℕ),
        (F.filter (fun j : Fin m => j.val < b)).card ≤
        (Lhit.filter (fun j : Fin m => j.val < b)).card := by
      intro b
      induction b using Nat.strong_induction_on with
      | h b ih =>
        by_cases hne : (F.filter (fun j : Fin m => j.val < b)).Nonempty
        · let k := (F.filter (fun j : Fin m => j.val < b)).max' hne
          have hk_mem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
          have hkF : k ∈ F := hk_mem.1
          have hkb : k.val < b := hk_mem.2
          let ℓ := aF k hkF
          have hℓk : ℓ < k := haF_lt k hkF
          have hih := ih (ℓ.val + 1) (by have : ℓ.val < k.val := hℓk; omega)
          have hIb := hI_bound k hkF
          have hF_split : F.filter (fun j : Fin m => j.val < b) ⊆
              F.filter (fun j : Fin m => j.val < ℓ.val + 1) ∪
              F.filter (fun j : Fin m => ℓ < j ∧ j ≤ k) := by
            intro j hj
            have hj' := Finset.mem_filter.mp hj
            have hjk : j ≤ k := Finset.le_max' _ j hj
            by_cases hjℓ : j.val < ℓ.val + 1
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj'.1, hjℓ⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj'.1, by change ℓ.val < j.val; omega, hjk⟩)
          have hL_sub : Lhit.filter (fun j : Fin m => j.val < ℓ.val + 1) ∪
              Lhit.filter (fun j : Fin m => ℓ < j ∧ j ≤ k) ⊆
              Lhit.filter (fun j : Fin m => j.val < b) := by
            intro j hj
            rcases Finset.mem_union.mp hj with h1 | h2
            · have h1' := Finset.mem_filter.mp h1
              have : ℓ.val < k.val := hℓk
              exact Finset.mem_filter.mpr ⟨h1'.1, by omega⟩
            · have h2' := Finset.mem_filter.mp h2
              have : j.val ≤ k.val := h2'.2.2
              exact Finset.mem_filter.mpr ⟨h2'.1, by omega⟩
          have hL_disj : Disjoint (Lhit.filter (fun j : Fin m => j.val < ℓ.val + 1))
              (Lhit.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)) :=
            Finset.disjoint_left.mpr (fun j h1 h2 => by
              have h1' := (Finset.mem_filter.mp h1).2
              have h2' : ℓ.val < j.val := (Finset.mem_filter.mp h2).2.1
              omega)
          have h1 := Finset.card_le_card hF_split
          have h2 := Finset.card_union_le (F.filter (fun j : Fin m => j.val < ℓ.val + 1))
            (F.filter (fun j : Fin m => ℓ < j ∧ j ≤ k))
          have h3 := Finset.card_le_card hL_sub
          rw [Finset.card_union_of_disjoint hL_disj] at h3
          change (F.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card ≤
            (Lhit.filter (fun j : Fin m => ℓ < j ∧ j ≤ k)).card at hIb
          omega
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; exact Nat.zero_le _
    have hF_all := hF_le_Lhit m
    have hF_eq : F.filter (fun j : Fin m => j.val < m) = F := by
      ext j; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact j.isLt
    have hL_eq : Lhit.filter (fun j : Fin m => j.val < m) = Lhit := by
      ext j; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact j.isLt
    rw [hF_eq, hL_eq] at hF_all
    obtain ⟨u0, hu0⟩ := hnot_all
    have hHit_lt : Hit.card + 1 ≤ Fintype.card W := by
      have hle : Hit.card ≤ (Finset.univ.erase u0).card := by
        refine Finset.card_le_card_of_injOn (fun j => (g j).getD u0) ?_ ?_
        · intro j hj
          dsimp only
          have hsome := (Finset.mem_filter.mp hj).2
          cases hgj : g j with
          | none => simp [hgj] at hsome
          | some w =>
            dsimp only [Option.getD]
            exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun heq => hu0 j (heq ▸ hgj), Finset.mem_univ _⟩)
        · intro j1 hj1 j2 hj2 hEq
          dsimp only at hEq
          have hs1 := (Finset.mem_filter.mp hj1).2
          have hs2 := (Finset.mem_filter.mp hj2).2
          cases hgj1 : g j1 with
          | none => simp [hgj1] at hs1
          | some w1 =>
            cases hgj2 : g j2 with
            | none => simp [hgj2] at hs2
            | some w2 =>
              simp only [hgj1, hgj2, Option.getD_some] at hEq
              exact hinj j1 j2 w1 hgj1 (hEq.symm ▸ hgj2)
      rw [Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ] at hle
      omega
    have hHit_F : Hit.card + F.card = m := by
      have h := card_filter_add_card_filter_not_eq (Finset.univ : Finset (Fin m)) (fun j => (g j).isSome)
      have heq : (Finset.univ : Finset (Fin m)).filter (fun j => ¬ (g j).isSome) = F := by
        ext j; simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Option.not_isSome_iff_eq_none]
      rw [heq, Finset.card_univ, Fintype.card_fin] at h; exact h
    change Fintype.card W + Lout.card ≤ m + 1 at hm
    omega
  choose f hf using hall_emb
  refine ⟨f, fun u v h => Option.some.inj ((hf u).symm.trans (h ▸ hf v)), ?_, ?_, ?_⟩
  · intro _; exact hinj (f r) ⟨0, hm_pos⟩ r (hf r) hroot0
  · intro u v hDuv
    rcases hpar (f v) v (hf v) with hvr | ⟨i, _, _, p, hgi, hDpv, hGiv⟩
    · exact absurd hDuv ((hroot v).mpr hvr u)
    · have hpu : p = u := hInDeg v p u hDpv hDuv
      subst hpu
      have hif : i = f p := hinj i (f p) p hgi (hf p)
      exact hif ▸ hGiv
  · intro a
    rcases hproc (f a) (f a).isLt a (hf a) with ⟨S, hSc, _, hS_or, _⟩ | ⟨⟨c, _, hc_un⟩, _⟩
    · refine ⟨S, hSc, fun c hc => ?_⟩
      exact hinj (f c) _ c (hf c) (hS_or c hc)
    · exact absurd (hf c) (hc_un (f c))

-- ============================================================================
-- STAGE 2A: Tree Parent Uniqueness, Finset Partition, and Dross-Havet Lemma 15
-- ============================================================================

lemma tree_exists_unique_parent {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) (r w : W) (hwr : w ≠ r) :
    ∃! p : W, T.Adj p w ∧ T.dist r p < T.dist r w := by
  classical
  have hex : ∃ p : W, T.Adj p w ∧ T.dist r p < T.dist r w := by
    obtain ⟨pwalk, _, hp_len⟩ := (hT.connected r w).exists_path_of_dist
    have hpos : 0 < T.dist r w := by
      by_contra h0
      have hdist0 : T.dist r w = 0 := by omega
      have hrw : r = w := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hdist0).resolve_right
        (not_not.mpr (hT.connected r w))
      exact hwr hrw.symm
    have hrev_len : pwalk.reverse.length = T.dist r w := by simpa using hp_len
    generalize hq : pwalk.reverse = q at hrev_len
    cases q with
    | nil => simp only [SimpleGraph.dist_self] at hpos; omega
    | @cons _ p _ hTwp q' =>
      have hTpw : T.Adj p w := hTwp.symm
      have hqlen : q'.length + 1 = T.dist r w := by simp at hrev_len; omega
      have hle : T.dist r p ≤ q'.length := by
        have := SimpleGraph.dist_le q'.reverse; simpa using this
      exact ⟨p, hTpw, by omega⟩
  obtain ⟨p, hTpw, hdist_p⟩ := hex
  refine ⟨p, ⟨hTpw, hdist_p⟩, fun p' ⟨hTp'w, hdist_p'⟩ => ?_⟩
  -- Uniqueness: shortest path r ~> p extended by w equals shortest path r ~> p' extended by w!
  obtain ⟨q1, hq1p, hq1len⟩ := (hT.connected r p).exists_path_of_dist
  obtain ⟨q2, hq2p, hq2len⟩ := (hT.connected r p').exists_path_of_dist
  have hw_not_q1 : w ∉ q1.support := fun hw => by
    have hle : T.dist r w ≤ (q1.takeUntil w hw).length := SimpleGraph.dist_le _
    have hlt : (q1.takeUntil w hw).length ≤ q1.length := SimpleGraph.Walk.length_takeUntil_le_length q1 hw
    omega
  have hw_not_q2 : w ∉ q2.support := fun hw => by
    have hle : T.dist r w ≤ (q2.takeUntil w hw).length := SimpleGraph.dist_le _
    have hlt : (q2.takeUntil w hw).length ≤ q2.length := SimpleGraph.Walk.length_takeUntil_le_length q2 hw
    omega
  let w1 : T.Walk w r := SimpleGraph.Walk.cons hTpw.symm q1.reverse
  let w2 : T.Walk w r := SimpleGraph.Walk.cons hTp'w.symm q2.reverse
  have hw1p : w1.IsPath := SimpleGraph.Walk.IsPath.cons hq1p.reverse (by simpa using hw_not_q1)
  have hw2p : w2.IsPath := SimpleGraph.Walk.IsPath.cons hq2p.reverse (by simpa using hw_not_q2)
  have heq : w1 = w2 := congrArg Subtype.val ((hT.isAcyclic.subsingleton_path w r).elim ⟨w1, hw1p⟩ ⟨w2, hw2p⟩)
  -- Second vertex of w1 is p, second vertex of w2 is p'!
  have hsnd := congrArg (fun q : T.Walk w r => q.support[1]?) heq
  simp only [w1, w2, SimpleGraph.Walk.support_cons, List.getElem?_cons_succ] at hsnd
  have h1 : q1.reverse.support[0]? = some p := by
    cases hq : q1.reverse <;> simp [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons]
  have h2 : q2.reverse.support[0]? = some p' := by
    cases hq : q2.reverse <;> simp [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons]
  rw [h1, h2] at hsnd
  exact (Option.some.inj hsnd).symm

lemma finset_partition_by_sizes {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (sz : ι → ℕ) :
    ∀ (S : Finset α), (∑ i ∈ I, sz i) = S.card →
      ∃ P : ι → Finset α,
        (∀ i ∈ I, P i ⊆ S) ∧
        (∀ i ∈ I, (P i).card = sz i) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ x ∈ S, ∃ i ∈ I, x ∈ P i) := by
  classical
  induction I using Finset.induction with
  | empty =>
    intro S hS
    simp only [Finset.sum_empty] at hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp hS.symm
    exact ⟨fun _ => ∅, fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (Finset.notMem_empty _),
      fun x hx => absurd (hSe ▸ hx) (Finset.notMem_empty x)⟩
  | @insert a I' ha ih =>
    intro S hS
    rw [Finset.sum_insert ha] at hS
    obtain ⟨Pa, hPasub, hPacard⟩ := Finset.exists_subset_card_eq (by omega : sz a ≤ S.card)
    have hS'card : (∑ i ∈ I', sz i) = (S \ Pa).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPasub]; omega
    obtain ⟨P', hP'sub, hP'card, hP'disj, hP'cov⟩ := ih (S \ Pa) hS'card
    let P : ι → Finset α := fun i => if i = a then Pa else P' i
    refine ⟨P, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simp only [P, ↓reduceIte]; exact hPasub
      · have hne : i ≠ a := fun h => ha (h ▸ hi')
        simp only [P, hne, ↓reduceIte]
        exact fun x hx => (Finset.mem_sdiff.mp (hP'sub i hi' hx)).1
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simp only [P, ↓reduceIte]; exact hPacard
      · have hne : i ≠ a := fun h => ha (h ▸ hi')
        simp only [P, hne, ↓reduceIte]; exact hP'card i hi'
    · intro i hi j hj hij
      rcases Finset.mem_insert.mp hi with rfl | hi' <;>
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact absurd rfl hij
      · have hne : j ≠ i := fun h => ha (h ▸ hj')
        simp only [P, ↓reduceIte, hne]
        exact Finset.disjoint_left.mpr (fun x hxa hxj => (Finset.mem_sdiff.mp (hP'sub j hj' hxj)).2 hxa)
      · have hne : i ≠ j := fun h => ha (h ▸ hi')
        simp only [P, ↓reduceIte, hne]
        exact Finset.disjoint_right.mpr (fun x hxa hxi => (Finset.mem_sdiff.mp (hP'sub i hi' hxi)).2 hxa)
      · have hni : i ≠ a := fun h => ha (h ▸ hi')
        have hnj : j ≠ a := fun h => ha (h ▸ hj')
        simp only [P, hni, hnj, ↓reduceIte]
        exact hP'disj i hi' j hj' hij
    · intro x hx
      by_cases hxa : x ∈ Pa
      · exact ⟨a, Finset.mem_insert_self a I', by simp only [P, ↓reduceIte]; exact hxa⟩
      · obtain ⟨i, hi', hxi⟩ := hP'cov x (Finset.mem_sdiff.mpr ⟨hx, hxa⟩)
        have hni : i ≠ a := fun h => ha (h ▸ hi')
        exact ⟨i, Finset.mem_insert_of_mem hi', by simp only [P, hni, ↓reduceIte]; exact hxi⟩

lemma exists_step_of_reflTransGen_step {α : Type*} {R : α → α → Prop} {a b c : α}
    (hab : R a b) (hbc : Relation.ReflTransGen R b c) : ∃ x, R x c := by
  induction hbc with
  | refl => exact ⟨a, hab⟩
  | tail _ hlast _ => exact ⟨_, hlast⟩

section Stage2
open Classical

-- Core structural lemma for downward forest of an oriented tree (T, D) rooted at r!
lemma down_forest_structure {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) {D : Digraph W} [DecidableRel D.Adj]
    (hO : D.IsOrientation T) (r : W) :
    let DownAdj : W → W → Prop := fun x y => D.Adj x y ∧ T.dist r y < T.dist r x
    let DownRoots : Finset W := Finset.univ.filter (fun c : W =>
      (∃ x : W, DownAdj x c) ∧ (∀ p : W, ¬ DownAdj c p))
    let compDown : W → Finset W := fun c =>
      Finset.univ.filter (fun w : W => Relation.ReflTransGen DownAdj w c)
    -- (1) Unique DownAdj out-neighbor (must be tree parent)
    (∀ x y1 y2 : W, DownAdj x y1 → DownAdj x y2 → y1 = y2) ∧
    -- (2) ReflTransGen DownAdj decreases dist
    (∀ x y : W, Relation.ReflTransGen DownAdj x y → T.dist r y ≤ T.dist r x ∧ (T.dist r y = T.dist r x → x = y)) ∧
    -- (3) Every vertex w reaches a unique maximal vertex topDown w (with no outgoing DownAdj)
    (∀ w : W, ∃! c : W, Relation.ReflTransGen DownAdj w c ∧ ∀ p : W, ¬ DownAdj c p) ∧
    -- (4) Distinct DownRoots have disjoint compDowns
    (∀ c1 ∈ DownRoots, ∀ c2 ∈ DownRoots, c1 ≠ c2 → Disjoint (compDown c1) (compDown c2)) ∧
    -- (5) Inside compDown c, every arc of D is a DownAdj arc!
    (∀ c ∈ DownRoots, ∀ x ∈ compDown c, ∀ y ∈ compDown c, D.Adj x y → DownAdj x y) := by
  intro DownAdj DownRoots compDown
  have huniq_down : ∀ x y1 y2 : W, DownAdj x y1 → DownAdj x y2 → y1 = y2 := by
    intro x y1 y2 h1 h2
    have hxr : x ≠ r := fun h => by subst h; have := h1.2; simp only [SimpleGraph.dist_self] at this; omega
    obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r x hxr
    exact (hpu y1 ⟨(hO.1 x y1 h1.1).symm, h1.2⟩).trans (hpu y2 ⟨(hO.1 x y2 h2.1).symm, h2.2⟩).symm
  have hdist_le : ∀ x y : W, Relation.ReflTransGen DownAdj x y →
      T.dist r y ≤ T.dist r x ∧ (T.dist r y = T.dist r x → x = y) := by
    intro x y hxy
    induction hxy with
    | refl => exact ⟨le_refl _, fun _ => rfl⟩
    | @tail b c hxb hbc ih =>
      have hlt : T.dist r c < T.dist r b := hbc.2
      exact ⟨by omega, fun heq => by omega⟩
  have htop : ∀ w : W, ∃! c : W, Relation.ReflTransGen DownAdj w c ∧ ∀ p : W, ¬ DownAdj c p := by
    intro w
    have hex : ∀ d : ℕ, ∀ x : W, T.dist r x = d →
        ∃ c : W, Relation.ReflTransGen DownAdj x c ∧ ∀ p : W, ¬ DownAdj c p := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro x hxd
        by_cases hstep : ∃ p : W, DownAdj x p
        · obtain ⟨p, hxp⟩ := hstep
          obtain ⟨c, hpc, hcn⟩ := ih (T.dist r p) (by omega) p rfl
          exact ⟨c, .head hxp hpc, hcn⟩
        · push Not at hstep
          exact ⟨x, .refl, hstep⟩
    obtain ⟨c, hwc, hcn⟩ := hex (T.dist r w) w rfl
    refine ⟨c, ⟨hwc, hcn⟩, fun c' ⟨hwc', hc'n⟩ => ?_⟩
    -- Follow both paths from w: by huniq_down, one extends the other!
    have hcomp : ∀ (a b1 b2 : W), Relation.ReflTransGen DownAdj a b1 → Relation.ReflTransGen DownAdj a b2 →
        Relation.ReflTransGen DownAdj b1 b2 ∨ Relation.ReflTransGen DownAdj b2 b1 := by
      intro a b1 b2 h1 h2
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => exact Or.inl h2
      | @head x y hxy _ ih =>
        rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨x', hxx', hx'b2⟩
        · exact Or.inr (.head hxy ‹_›)
        · have hyx' : y = x' := huniq_down x y x' hxy hxx'
          subst hyx'
          exact ih hx'b2
    rcases hcomp w c c' hwc hwc' with h12 | h21
    · rcases Relation.ReflTransGen.cases_head h12 with rfl | ⟨_, hstep, _⟩
      · rfl
      · exact absurd hstep (hcn _)
    · rcases Relation.ReflTransGen.cases_head h21 with rfl | ⟨_, hstep, _⟩
      · rfl
      · exact absurd hstep (hc'n _)
  have hdisj : ∀ c1 ∈ DownRoots, ∀ c2 ∈ DownRoots, c1 ≠ c2 → Disjoint (compDown c1) (compDown c2) := by
    intro c1 hc1 c2 hc2 hne
    refine Finset.disjoint_left.mpr (fun w hw1 hw2 => ?_)
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    have hc1n := (Finset.mem_filter.mp hc1).2.2
    have hc2n := (Finset.mem_filter.mp hc2).2.2
    obtain ⟨c0, _, hc0u⟩ := htop w
    exact hne ((hc0u c1 ⟨h1, hc1n⟩).trans (hc0u c2 ⟨h2, hc2n⟩).symm)
  have hclosed : ∀ c ∈ DownRoots, ∀ x ∈ compDown c, ∀ y ∈ compDown c, D.Adj x y → DownAdj x y := by
    intro c _ x hx y hy hDxy
    have hTxy : T.Adj x y := hO.1 x y hDxy
    rcases hT.dist_eq_dist_add_one_of_adj r hTxy with h1 | h2
    · exact ⟨hDxy, by omega⟩
    · exfalso
      have hx_path : Relation.ReflTransGen DownAdj x c := (Finset.mem_filter.mp hx).2
      have hy_path : Relation.ReflTransGen DownAdj y c := (Finset.mem_filter.mp hy).2
      rcases Relation.ReflTransGen.cases_head hy_path with rfl | ⟨z, hyz, _⟩
      · have := (hdist_le x _ hx_path).1; omega
      · have hyr : y ≠ r := fun h => by subst h; simp only [SimpleGraph.dist_self] at h2; omega
        obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r y hyr
        have hz_eq : z = p := hpu z ⟨(hO.1 y z hyz.1).symm, hyz.2⟩
        have hx_eq : x = p := hpu x ⟨hTxy, by omega⟩
        rw [hx_eq, ← hz_eq] at hDxy
        exact not_adj_rev_of_isOrientation hO hyz.1 hDxy
  exact ⟨huniq_down, hdist_le, htop, hdisj, hclosed⟩

-- Dross-Havet (2021) Lemma 15 (lem:t_tree): If r has in-degree 0,
-- then D embeds in every tournament on m >= n + k - 1 + gamma_r^down vertices!
lemma dross_havet_rooted_source {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (r : W) (hr_src : ∀ x : W, ¬ D.Adj x r)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hG : G.IsTournament)
    (hm : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card +
      (∑ c ∈ Finset.univ.filter (fun c : W =>
          (∃ x : W, D.Adj x c ∧ T.dist r c < T.dist r x) ∧
          (∀ p : W, ¬ (D.Adj c p ∧ T.dist r p < T.dist r c))),
        ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).card +
         ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).filter
           (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r w < T.dist r x))).card - 2)) ≤
      Fintype.card V + 1) :
    Embeds D G := by
  let DownAdj : W → W → Prop := fun x y => D.Adj x y ∧ T.dist r y < T.dist r x
  let UpAdj : W → W → Prop := fun x y => D.Adj x y ∧ T.dist r x < T.dist r y
  let DownRoots : Finset W := Finset.univ.filter (fun c : W =>
    (∃ x : W, DownAdj x c) ∧ (∀ p : W, ¬ DownAdj c p))
  let compDown : W → Finset W := fun c =>
    Finset.univ.filter (fun w : W => Relation.ReflTransGen DownAdj w c)
  let inLeavesDown : W → Finset W := fun c =>
    (compDown c).filter (fun w => ∀ x : W, ¬ DownAdj x w)
  obtain ⟨huniq_down, hdist_le, htop, hdisj_comp, hclosed_comp⟩ := down_forest_structure hT hO r
  -- For every c ∈ DownRoots: c ≠ r, and c has a unique parent f_c with UpAdj f_c c!
  have hc_ne_r : ∀ c ∈ DownRoots, c ≠ r := by
    intro c hc hcr; subst hcr
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hc).2.1
    exact hr_src x hx.1
  have hup_uniq : ∀ v u1 u2 : W, UpAdj u1 v → UpAdj u2 v → u1 = u2 := by
    intro v u1 u2 h1 h2
    have hvr : v ≠ r := fun h => by subst h; have := h1.2; simp only [SimpleGraph.dist_self] at this; omega
    obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r v hvr
    exact (hpu u1 ⟨hO.1 u1 v h1.1, h1.2⟩).trans (hpu u2 ⟨hO.1 u2 v h2.1, h2.2⟩).symm
  have hc_up_par : ∀ c ∈ DownRoots, ∃! f : W, UpAdj f c := by
    intro c hc
    obtain ⟨f, ⟨hTfc, hdist_fc⟩, hfu⟩ := tree_exists_unique_parent hT r c (hc_ne_r c hc)
    have hDfc : D.Adj f c := by
      rcases adj_or_rev_of_isOrientation hO hTfc with h | h
      · exact h
      · exact absurd ⟨h, hdist_fc⟩ ((Finset.mem_filter.mp hc).2.2 f)
    exact ⟨f, ⟨hDfc, hdist_fc⟩, fun f' hf' => hfu f' ⟨hO.1 f' c hf'.1, hf'.2⟩⟩
  -- For every c ∈ DownRoots: 2 <= (compDown c).card and 1 <= (inLeavesDown c).card <= (compDown c).card - 1!
  have hc_sizes : ∀ c ∈ DownRoots,
      2 ≤ (compDown c).card ∧ 1 ≤ (inLeavesDown c).card ∧ (inLeavesDown c).card < (compDown c).card := by
    intro c hc
    obtain ⟨x0, hx0⟩ := (Finset.mem_filter.mp hc).2.1
    have hc_mem : c ∈ compDown c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
    have hx0_mem : x0 ∈ compDown c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .single hx0⟩
    have hx0_ne : x0 ≠ c := fun h => by subst h; exact lt_irrefl _ hx0.2
    have hcard_ge2 : 2 ≤ (compDown c).card := by
      have hsub : ({x0, c} : Finset W) ⊆ compDown c := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub; rw [Finset.card_pair hx0_ne] at this; exact this
    obtain ⟨wmax, hwmax_mem, hwmax⟩ := Finset.exists_max_image (compDown c) (T.dist r) ⟨c, hc_mem⟩
    have h1 : 1 ≤ (inLeavesDown c).card := by
      refine Finset.one_le_card.mpr ⟨wmax, Finset.mem_filter.mpr ⟨hwmax_mem, fun y hy => ?_⟩⟩
      have hy_mem : y ∈ compDown c :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, .head hy (Finset.mem_filter.mp hwmax_mem).2⟩
      have := hwmax y hy_mem; have := hy.2; omega
    have hlt : (inLeavesDown c).card < (compDown c).card := by
      have hsub : inLeavesDown c ⊆ (compDown c).erase c := by
        intro w hw; have hw' := Finset.mem_filter.mp hw
        refine Finset.mem_erase.mpr ⟨fun hwc => hw'.2 x0 (hwc ▸ hx0), hw'.1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hc_mem] at this; omega
    exact ⟨hcard_ge2, h1, hlt⟩
  -- Build the equivalent out-arborescence W' = W ⊕ Σ (c : DownRoots), Fin ((inLeavesDown c).card - 1)!
  let W' := W ⊕ Σ (c : ↥DownRoots), Fin ((inLeavesDown c.1).card - 1)
  let inAnyComp : W → Prop := fun w => ∃ c ∈ DownRoots, w ∈ compDown c
  have hcomp_uniq : ∀ w c1 c2, c1 ∈ DownRoots → w ∈ compDown c1 → c2 ∈ DownRoots → w ∈ compDown c2 → c1 = c2 := by
    intro w c1 c2 hc1 hw1 hc2 hw2
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj_comp c1 hc1 c2 hc2 hne) hw1 hw2
  let D' : Digraph W' := ⟨fun a b =>
    match a, b with
    | Sum.inl u, Sum.inl v =>
        (¬ inAnyComp v ∧ UpAdj u v) ∨ (∃ c ∈ DownRoots, v ∈ compDown c ∧ UpAdj u c)
    | Sum.inl u, Sum.inr ⟨c, _⟩ => UpAdj u c.1
    | Sum.inr _, _ => False⟩
  -- Rank function on W'
  let rk' : W' → ℕ := fun a => match a with
    | Sum.inl w => T.dist r w
    | Sum.inr ⟨c, _⟩ => T.dist r c.1
  have hRank' : ∀ a b : W', D'.Adj a b → rk' a < rk' b := by
    intro a b hab
    cases a with
    | inr p => exact False.elim hab
    | inl u =>
      cases b with
      | inr p => exact hab.2
      | inl v =>
        rcases hab with ⟨_, huv⟩ | ⟨c, _, hvc, huc⟩
        · exact huv.2
        · have hle := (hdist_le v c (Finset.mem_filter.mp hvc).2).1
          have hlt := huc.2; dsimp only [rk']; omega
  have hInDeg' : ∀ b a1 a2 : W', D'.Adj a1 b → D'.Adj a2 b → a1 = a2 := by
    intro b a1 a2 h1 h2
    cases a1 with
    | inr _ => exact False.elim h1
    | inl u1 =>
      cases a2 with
      | inr _ => exact False.elim h2
      | inl u2 =>
        congr 1
        cases b with
        | inr p => exact hup_uniq p.1.1 u1 u2 h1 h2
        | inl v =>
          rcases h1 with ⟨hno, huv1⟩ | ⟨c1, hc1, hvc1, huc1⟩ <;>
          rcases h2 with ⟨hno2, huv2⟩ | ⟨c2, hc2, hvc2, huc2⟩
          · exact hup_uniq v u1 u2 huv1 huv2
          · exact absurd ⟨c2, hc2, hvc2⟩ hno
          · exact absurd ⟨c1, hc1, hvc1⟩ hno2
          · have hc_eq := hcomp_uniq v c1 c2 hc1 hvc1 hc2 hvc2
            subst hc_eq; exact hup_uniq c1 u1 u2 huc1 huc2
  have hroot' : ∀ b : W', (∀ a : W', ¬ D'.Adj a b) ↔ b = Sum.inl r := by
    intro b
    constructor
    · intro hno
      cases b with
      | inr p =>
        obtain ⟨f, hfc, _⟩ := hc_up_par p.1.1 p.1.2
        exact absurd hfc (hno (Sum.inl f))
      | inl v =>
        by_contra hvr
        have hvr' : v ≠ r := fun h => hvr (congrArg Sum.inl h)
        by_cases hcomp : inAnyComp v
        · obtain ⟨c, hc, hvc⟩ := hcomp
          obtain ⟨f, hfc, _⟩ := hc_up_par c hc
          exact hno (Sum.inl f) (Or.inr ⟨c, hc, hvc, hfc⟩)
        · obtain ⟨p, ⟨hTpv, hdist_pv⟩, _⟩ := tree_exists_unique_parent hT r v hvr'
          rcases adj_or_rev_of_isOrientation hO hTpv with hDpv | hDvp
          · exact hno (Sum.inl p) (Or.inl ⟨hcomp, hDpv, hdist_pv⟩)
          · -- DownAdj v p implies v belongs to compDown (topDown v) where topDown v ∈ DownRoots!
            obtain ⟨c, ⟨hvc, hcn⟩, _⟩ := htop v
            have hc_has_in : ∃ x : W, DownAdj x c := by
              cases hvc using Relation.ReflTransGen.head_induction_on with
              | refl => exact absurd ⟨hDvp, hdist_pv⟩ (hcn p)
              | head hstep hrest => exact exists_step_of_reflTransGen_step hstep hrest
            have hcDR : c ∈ DownRoots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_has_in, hcn⟩
            exact hcomp ⟨c, hcDR, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvc⟩⟩
    · rintro rfl a ha
      cases a with
      | inr _ => exact ha
      | inl u =>
        rcases ha with ⟨_, hur⟩ | ⟨c, hc, hrc, _⟩
        · exact hr_src u hur.1
        · have hle := (hdist_le r c (Finset.mem_filter.mp hrc).2)
          have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
          have hcr : c = r := (hle.2 (by have := hle.1; omega)).symm
          exact hc_ne_r c hc hcr
  -- Cardinality bound: Fintype.card W' + |OutLeaves(D')| <= n + k + gammaDown <= Fintype.card V + 1!
  have hcardW' : Fintype.card W' = n + ∑ c ∈ DownRoots, ((inLeavesDown c).card - 1) := by
    rw [Fintype.card_sum, hW, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← Finset.sum_coe_sort DownRoots]
  have hleavesD' : (Finset.univ.filter (fun a : W' => ∀ b : W', ¬ D'.Adj a b)).card ≤
      (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card +
      (∑ c ∈ DownRoots, ((compDown c).card - (inLeavesDown c).card)) +
      (∑ c ∈ DownRoots, ((inLeavesDown c).card - 1)) := by
    let LeavesW := Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)
    let NonLeafDown := DownRoots.biUnion (fun c => compDown c \ inLeavesDown c)
    let Dummies : Finset W' := Finset.univ.filter (fun a : W' => match a with | Sum.inl _ => False | Sum.inr _ => True)
    have hsub : Finset.univ.filter (fun a : W' => ∀ b : W', ¬ D'.Adj a b) ⊆
        (LeavesW.image Sum.inl ∪ NonLeafDown.image Sum.inl) ∪ Dummies := by
      intro a ha
      have hno := (Finset.mem_filter.mp ha).2
      cases a with
      | inr p =>
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩)
      | inl u =>
        refine Finset.mem_union_left _ ?_
        by_cases huL : u ∈ LeavesW
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ huL)
        · refine Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_)
          -- u has no upward outgoing arc!
          have hno_up : ∀ v : W, ¬ UpAdj u v := by
            intro v huv
            by_cases hvcomp : inAnyComp v
            · obtain ⟨c, hc, hvc⟩ := hvcomp
              -- Since UpAdj u v (T.dist r u < T.dist r v) and v ∈ compDown c, we MUST have v = c!
              have hvc_eq : v = c := by
                have hpath := (Finset.mem_filter.mp hvc).2
                rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨z, hvz, _⟩
                · rfl
                · have hvr : v ≠ r := fun h => by subst h; have := huv.2; simp only [SimpleGraph.dist_self] at this; omega
                  obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r v hvr
                  have hu_eq : u = p := hpu u ⟨hO.1 u v huv.1, huv.2⟩
                  have hz_eq : z = p := hpu z ⟨(hO.1 v z hvz.1).symm, hvz.2⟩
                  exact absurd (hu_eq ▸ hz_eq ▸ hvz.1) (not_adj_rev_of_isOrientation hO huv.1)
              subst hvc_eq
              exact hno (Sum.inl v) (Or.inr ⟨v, hc, hvc, huv⟩)
            · exact hno (Sum.inl v) (Or.inl ⟨hvcomp, huv⟩)
          -- Since u ∉ LeavesW and n >= 2, u has degree >= 2 in T, hence has a child x in (T, r)!
          have hex_child : ∃ x : W, T.Adj u x ∧ T.dist r u < T.dist r x := by
            have hdeg_ge2 : 2 ≤ (Finset.univ.filter (fun z : W => T.Adj u z)).card := by
              have hdeg_eq : (Finset.univ.filter (fun z : W => D.Adj u z ∨ D.Adj z u)).card =
                  (Finset.univ.filter (fun z : W => T.Adj u z)).card := by
                congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => by rcases h with h1 | h2; exact hO.1 u z h1; exact (hO.1 z u h2).symm,
                  fun h => adj_or_rev_of_isOrientation hO h⟩
              have hne1 : (Finset.univ.filter (fun z : W => T.Adj u z)).card ≠ 1 := fun h1 =>
                huL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg_eq.trans h1⟩)
              have hpos : 1 ≤ (Finset.univ.filter (fun z : W => T.Adj u z)).card := by
                obtain ⟨v1, v2, hv12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
                have hex_ne : ∃ v0 : W, v0 ≠ u := by
                  by_cases h1 : v1 = u; exact ⟨v2, fun h => hv12 (h1.trans h.symm)⟩; exact ⟨v1, h1⟩
                obtain ⟨v0, hv0⟩ := hex_ne
                obtain ⟨p⟩ := hT.connected u v0
                cases p with
                | nil => exact absurd rfl hv0
                | @cons _ w _ hadj _ => exact Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩
              omega
            by_cases hur : u = r
            · subst hur
              obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => T.Adj u z)).card)
              have hTux := (Finset.mem_filter.mp hx).2
              refine ⟨x, hTux, ?_⟩
              have huu0 : T.dist u u = 0 := SimpleGraph.dist_self
              rcases hT.dist_eq_dist_add_one_of_adj u hTux with h1 | h2 <;> omega
            · obtain ⟨p, ⟨hTpu, hdist_pu⟩, hpu⟩ := tree_exists_unique_parent hT r u hur
              have hne : ((Finset.univ.filter (fun z : W => T.Adj u z)).erase p).Nonempty := by
                refine Finset.card_pos.mp ?_
                have hp_mem : p ∈ Finset.univ.filter (fun z : W => T.Adj u z) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTpu.symm⟩
                rw [Finset.card_erase_of_mem hp_mem]; omega
              obtain ⟨x, hx⟩ := hne
              have hxne : x ≠ p := (Finset.mem_erase.mp hx).1
              have hTux : T.Adj u x := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
              rcases hT.dist_eq_dist_add_one_of_adj r hTux with h1 | h2
              · exact absurd (hpu x ⟨hTux.symm, by omega⟩) hxne
              · exact ⟨x, hTux, by omega⟩
          obtain ⟨x, hTux, hdist_ux⟩ := hex_child
          have hDxu : DownAdj x u := by
            rcases adj_or_rev_of_isOrientation hO hTux with h | h
            · exact absurd ⟨h, hdist_ux⟩ (hno_up x)
            · exact ⟨h, hdist_ux⟩
          obtain ⟨c, ⟨huc, hcn⟩, _⟩ := htop u
          have hc_has : ∃ y : W, DownAdj y c := by
            cases huc using Relation.ReflTransGen.head_induction_on with
            | refl => exact ⟨x, hDxu⟩
            | head hstep hrest => exact exists_step_of_reflTransGen_step hstep hrest
          have hcDR : c ∈ DownRoots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_has, hcn⟩
          refine Finset.mem_biUnion.mpr ⟨c, hcDR, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huc⟩, ?_⟩⟩
          intro hu_inL; exact (Finset.mem_filter.mp hu_inL).2 x hDxu
    have hDummies_card : Dummies.card = ∑ c ∈ DownRoots, ((inLeavesDown c).card - 1) := by
      have hbij : Dummies.card = Fintype.card (Σ (c : ↥DownRoots), Fin ((inLeavesDown c.1).card - 1)) := by
        refine Finset.card_bij (fun a ha => match a, ha with
          | Sum.inr p, _ => p
          | Sum.inl _, ha => False.elim (Finset.mem_filter.mp ha).2) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a1 ha1 a2 ha2 h
          cases a1 with
          | inl _ => exact False.elim (Finset.mem_filter.mp ha1).2
          | inr p1 =>
            cases a2 with
            | inl _ => exact False.elim (Finset.mem_filter.mp ha2).2
            | inr p2 => exact congrArg Sum.inr h
        · intro p _; exact ⟨Sum.inr p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩, rfl⟩
      rw [hbij, Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rw [← Finset.sum_coe_sort DownRoots]
    have hNLD_card : NonLeafDown.card ≤ ∑ c ∈ DownRoots, ((compDown c).card - (inLeavesDown c).card) := by
      calc NonLeafDown.card ≤ ∑ c ∈ DownRoots, (compDown c \ inLeavesDown c).card := Finset.card_biUnion_le
        _ = ∑ c ∈ DownRoots, ((compDown c).card - (inLeavesDown c).card) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le (LeavesW.image (Sum.inl : W → W') ∪ NonLeafDown.image (Sum.inl : W → W')) Dummies
    have hc3 := Finset.card_union_le (LeavesW.image (Sum.inl : W → W')) (NonLeafDown.image (Sum.inl : W → W'))
    have hc4 := Finset.card_image_le (f := (Sum.inl : W → W')) (s := LeavesW)
    have hc5 := Finset.card_image_le (f := (Sum.inl : W → W')) (s := NonLeafDown)
    change (Finset.univ.filter (fun a : W' => ∀ b : W', ¬ D'.Adj a b)).card ≤
      LeavesW.card + (∑ c ∈ DownRoots, ((compDown c).card - (inLeavesDown c).card)) +
      (∑ c ∈ DownRoots, ((inLeavesDown c).card - 1))
    omega
  have hm' : Fintype.card W' + (Finset.univ.filter (fun a : W' => ∀ b : W', ¬ D'.Adj a b)).card ≤
      Fintype.card V + 1 := by
    have hsum_combine :
        (∑ c ∈ DownRoots, ((inLeavesDown c).card - 1)) +
        (∑ c ∈ DownRoots, ((compDown c).card - (inLeavesDown c).card)) +
        (∑ c ∈ DownRoots, ((inLeavesDown c).card - 1)) =
        ∑ c ∈ DownRoots, ((compDown c).card + (inLeavesDown c).card - 2) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have ⟨h1, h2, h3⟩ := hc_sizes c hc
      omega
    have hm_loc : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card +
        (∑ c ∈ DownRoots, ((compDown c).card + (inLeavesDown c).card - 2)) ≤ Fintype.card V + 1 := hm
    omega
  -- Step 2: Construct the online sibling oracle!
  obtain ⟨σ, hR, _⟩ := exists_median_order G hG
  -- Helper: embed an in-arborescence compDown c into any subtournament T_c of size n_c + k_c - 1!
  have hembed_comp : ∀ (c : W) (hc : c ∈ DownRoots) (Tc : Finset (Fin (Fintype.card V))),
      Tc.card = (compDown c).card + ((inLeavesDown c).card - 1) →
      ∃ fc : ↥(compDown c) → Fin (Fintype.card V),
        Function.Injective fc ∧ (∀ x, fc x ∈ Tc) ∧
        (∀ x y : ↥(compDown c), D.Adj x.1 y.1 → G.Adj (σ (fc x)) (σ (fc y))) := by
    intro c hc Tc hTccard
    let DcRev : Digraph ↥(compDown c) := ⟨fun x y => DownAdj y.1 x.1⟩
    let GTcRev : Digraph ↥Tc := ⟨fun i j => G.Adj (σ j.1) (σ i.1)⟩
    have hGTcRev_tourn : GTcRev.IsTournament :=
      ⟨fun i => hG.1 (σ i.1), fun i j hij =>
        hG.2 (σ j.1) (σ i.1) (fun h => hij (Subtype.ext (σ.injective h.symm)))⟩
    obtain ⟨σc, hRc, _⟩ := exists_median_order GTcRev hGTcRev_tourn
    have hRank_c : ∃ rk : ↥(compDown c) → ℕ, ∀ x y, DcRev.Adj x y → rk x < rk y :=
      ⟨fun x => T.dist r x.1, fun x y h => h.2⟩
    have hInDeg_c : ∀ y x1 x2 : ↥(compDown c), DcRev.Adj x1 y → DcRev.Adj x2 y → x1 = x2 :=
      fun y x1 x2 h1 h2 => Subtype.ext (huniq_down y.1 x1.1 x2.1 h1 h2)
    have hc_mem : c ∈ compDown c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
    have hroot_c : ∀ x : ↥(compDown c), (∀ y : ↥(compDown c), ¬ DcRev.Adj y x) ↔ x = ⟨c, hc_mem⟩ := by
      intro x
      constructor
      · intro hno
        rcases x with ⟨x0, hx0⟩
        have hpath := (Finset.mem_filter.mp hx0).2
        rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨z, hxz, hzc⟩
        · rfl
        · exact absurd hxz (hno ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzc⟩⟩)
      · rintro rfl y hy
        exact (Finset.mem_filter.mp hc).2.2 y.1 hy
    have hleaves_c : (Finset.univ.filter (fun x : ↥(compDown c) => ∀ y : ↥(compDown c), ¬ DcRev.Adj x y)).card =
        (inLeavesDown c).card := by
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx
        refine Finset.mem_filter.mpr ⟨x.2, fun y hy => ?_⟩
        have hy_mem : y ∈ compDown c :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, .head hy (Finset.mem_filter.mp x.2).2⟩
        exact (Finset.mem_filter.mp hx).2 ⟨y, hy_mem⟩ hy
      · intro x1 _ x2 _ h; exact Subtype.ext h
      · intro w hw
        have hw' := Finset.mem_filter.mp hw
        exact ⟨⟨w, hw'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => hw'.2 y.1 hy⟩, rfl⟩
    have hmc : Fintype.card ↥(compDown c) +
        (Finset.univ.filter (fun x : ↥(compDown c) => ∀ y : ↥(compDown c), ¬ DcRev.Adj x y)).card ≤
        Fintype.card ↥Tc + 1 := by
      rw [Fintype.card_coe, Fintype.card_coe, hleaves_c, hTccard]
      have ⟨_, h2, _⟩ := hc_sizes c hc
      omega
    obtain ⟨fc0, hfc0_inj, _, hfc0_adj, _⟩ := online_greedy_out_arborescence DcRev hRank_c hInDeg_c
      ⟨c, hc_mem⟩ hroot_c GTcRev hRc hmc
      (fun _ S hS => Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS]))
    refine ⟨fun x => (σc (fc0 x)).1, fun x1 x2 h => hfc0_inj (σc.injective (Subtype.ext h)),
      fun x => (σc (fc0 x)).2, fun x y hDxy => ?_⟩
    exact hfc0_adj y x (hclosed_comp c hc x.1 x.2 y.1 y.2 hDxy)
  -- Build the oracle on every vertex a : W'!
  have horacle_ex : ∀ (a : W') (S : Finset (Fin (Fintype.card V))),
      S.card = (Finset.univ.filter (fun b : W' => D'.Adj a b)).card →
      ∃ e : ↥(Finset.univ.filter (fun b : W' => D'.Adj a b)) ≃ ↥S,
        ∀ (u : W) (ha : a = Sum.inl u),
          ∀ (c : W) (hc : c ∈ DownRoots) (huc : UpAdj u c),
            ∀ (x y : W) (hx : x ∈ compDown c) (hy : y ∈ compDown c),
              D.Adj x y →
              G.Adj (σ (e ⟨Sum.inl x, by subst ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨c, hc, hx, huc⟩⟩⟩).1)
                    (σ (e ⟨Sum.inl y, by subst ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨c, hc, hy, huc⟩⟩⟩).1) := by
    intro a S hSc
    cases a with
    | inr p =>
      exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hSc]), fun _ h => by cases h⟩
    | inl u =>
      let Ch := Finset.univ.filter (fun b : W' => D'.Adj (Sum.inl u) b)
      let Att := DownRoots.filter (fun c => UpAdj u c)
      let Singles := Finset.univ.filter (fun v : W => ¬ inAnyComp v ∧ UpAdj u v)
      -- Index the partition pieces by Option ↥Att: none = Singles, some c = compDown c ∪ dummies c!
      let piece : Option ↥Att → Finset W' := fun o =>
        match o with
        | none => Singles.image Sum.inl
        | some ⟨c, hc⟩ =>
          (compDown c).image Sum.inl ∪
          (Finset.univ : Finset (Fin ((inLeavesDown c).card - 1))).image
            (fun j => Sum.inr ⟨⟨c, (Finset.mem_filter.mp hc).1⟩, j⟩)
      have hpiece_disj : ∀ o1 o2 : Option ↥Att, o1 ≠ o2 → Disjoint (piece o1) (piece o2) := by
        intro o1 o2 hne
        cases o1 with
        | none =>
          cases o2 with
          | none => exact absurd rfl hne
          | some c2 =>
            refine Finset.disjoint_left.mpr (fun b hb1 hb2 => ?_)
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb1
            rcases Finset.mem_union.mp hb2 with hb2l | hb2r
            · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hb2l
              have hwv : w = v := Sum.inl.inj hEq
              exact (Finset.mem_filter.mp hv).2.1 ⟨c2.1, (Finset.mem_filter.mp c2.2).1, hwv ▸ hw⟩
            · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hb2r; cases hEq
        | some c1 =>
          cases o2 with
          | none =>
            refine Finset.disjoint_right.mpr (fun b hb2 hb1 => ?_)
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb2
            rcases Finset.mem_union.mp hb1 with hb1l | hb1r
            · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hb1l
              have hwv : w = v := Sum.inl.inj hEq
              exact (Finset.mem_filter.mp hv).2.1 ⟨c1.1, (Finset.mem_filter.mp c1.2).1, hwv ▸ hw⟩
            · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hb1r; cases hEq
          | some c2 =>
            have hc12 : c1.1 ≠ c2.1 := fun h => hne (congrArg some (Subtype.ext h))
            refine Finset.disjoint_left.mpr (fun b hb1 hb2 => ?_)
            rcases Finset.mem_union.mp hb1 with hb1l | hb1r <;>
            rcases Finset.mem_union.mp hb2 with hb2l | hb2r
            · obtain ⟨w1, hw1, rfl⟩ := Finset.mem_image.mp hb1l
              obtain ⟨w2, hw2, hEq⟩ := Finset.mem_image.mp hb2l
              have hw : w2 = w1 := Sum.inl.inj hEq
              exact Finset.disjoint_left.mp
                (hdisj_comp c1.1 (Finset.mem_filter.mp c1.2).1 c2.1 (Finset.mem_filter.mp c2.2).1 hc12)
                hw1 (hw ▸ hw2)
            · obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hb1l
              obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hb2r; cases hEq
            · obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hb1r
              obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hb2l; cases hEq
            · obtain ⟨j1, _, rfl⟩ := Finset.mem_image.mp hb1r
              obtain ⟨j2, _, hEq⟩ := Finset.mem_image.mp hb2r
              have hsig := Sum.inr.inj hEq
              exact hc12 (congrArg (fun p : Σ c : ↥DownRoots, Fin ((inLeavesDown c.1).card - 1) => p.1.1) hsig).symm
      have hCh_eq : Ch = Finset.univ.biUnion piece := by
        ext b
        simp only [Ch, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        cases b with
        | inl v =>
          constructor
          · intro h
            rcases h with ⟨hno, huv⟩ | ⟨c, hc, hvc, huc⟩
            · exact ⟨none, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno, huv⟩)⟩
            · exact ⟨some ⟨c, Finset.mem_filter.mpr ⟨hc, huc⟩⟩,
                Finset.mem_union_left _ (Finset.mem_image_of_mem _ hvc)⟩
          · rintro ⟨o, ho⟩
            cases o with
            | none =>
              obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp ho
              have hvw : w = v := Sum.inl.inj hEq
              subst hvw; exact Or.inl (Finset.mem_filter.mp hw).2
            | some c =>
              rcases Finset.mem_union.mp ho with hol | hor
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hol
                have hvw : w = v := Sum.inl.inj hEq
                subst hvw
                exact Or.inr ⟨c.1, (Finset.mem_filter.mp c.2).1, hw, (Finset.mem_filter.mp c.2).2⟩
              · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hor; cases hEq
        | inr p =>
          constructor
          · intro hup
            refine ⟨some ⟨p.1.1, Finset.mem_filter.mpr ⟨p.1.2, hup⟩⟩,
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩)⟩
          · rintro ⟨o, ho⟩
            cases o with
            | none => obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp ho; cases hEq
            | some c =>
              rcases Finset.mem_union.mp ho with hol | hor
              · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hol; cases hEq
              · obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hor
                have hc_eq : c.1 = p.1.1 :=
                  congrArg (fun q : Σ c : ↥DownRoots, Fin ((inLeavesDown c.1).card - 1) => q.1.1) (Sum.inr.inj hEq)
                change UpAdj u p.1.1
                exact hc_eq ▸ (Finset.mem_filter.mp c.2).2
      have hsum_sz : (∑ o : Option ↥Att, (piece o).card) = S.card := by
        rw [hSc, show (Finset.univ.filter (fun b : W' => D'.Adj (Sum.inl u) b)).card = Ch.card from rfl,
          hCh_eq, Finset.card_biUnion (fun o1 _ o2 _ h => hpiece_disj o1 o2 h)]
      obtain ⟨P, hPsub, hPcard, hPdisj, hPcov⟩ := finset_partition_by_sizes Finset.univ (fun o => (piece o).card) S hsum_sz
      -- For each piece o, construct a bijection piece o ≃ P o (using hembed_comp for o = some c)!
      have hpiece_bij : ∀ o : Option ↥Att,
          ∃ eo : ↥(piece o) ≃ ↥(P o),
            ∀ (c : ↥Att) (ho : o = some c),
              ∀ (x y : W) (hx : x ∈ compDown c.1) (hy : y ∈ compDown c.1), D.Adj x y →
                G.Adj (σ (eo ⟨Sum.inl x, by subst ho; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)⟩).1)
                      (σ (eo ⟨Sum.inl y, by subst ho; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)⟩).1) := by
        intro o
        cases o with
        | none =>
          exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hPcard none (Finset.mem_univ _)]), fun _ h => by cases h⟩
        | some c =>
          have hcDR : c.1 ∈ DownRoots := (Finset.mem_filter.mp c.2).1
          have hpiece_card : (piece (some c)).card = (compDown c.1).card + ((inLeavesDown c.1).card - 1) := by
            dsimp only [piece]
            rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h),
              Finset.card_image_of_injective _ (fun j1 j2 h => by
                have h1 := Sum.inr.inj h; exact eq_of_heq (Sigma.ext_iff.mp h1).2),
              Finset.card_univ, Fintype.card_fin]
            refine Finset.disjoint_left.mpr (fun b h1 h2 => ?_)
            obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
            obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2; cases hEq
          have hPccard : (P (some c)).card = (compDown c.1).card + ((inLeavesDown c.1).card - 1) :=
            (hPcard (some c) (Finset.mem_univ _)).trans hpiece_card
          obtain ⟨fc, hfc_inj, hfc_mem, hfc_adj⟩ := hembed_comp c.1 hcDR (P (some c)) hPccard
          let imgc : Finset (Fin (Fintype.card V)) := Finset.univ.image fc
          have himgc_sub : imgc ⊆ P (some c) := fun j hj => by
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hj; exact hfc_mem x
          have himgc_card : imgc.card = (compDown c.1).card := by
            rw [Finset.card_image_of_injective _ hfc_inj, Finset.card_univ, Fintype.card_coe]
          have hrem_card : (P (some c) \ imgc).card = (inLeavesDown c.1).card - 1 := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr himgc_sub, hPccard, himgc_card]; omega
          let edum : Fin ((inLeavesDown c.1).card - 1) ≃ ↥(P (some c) \ imgc) :=
            Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hrem_card])
          let fwd : ↥(piece (some c)) → ↥(P (some c)) := fun b =>
            match b with
            | ⟨Sum.inl w, hm⟩ =>
              have hw : w ∈ compDown c.1 := by
                rcases Finset.mem_union.mp hm with hl | hr
                · obtain ⟨w', hw', hEq⟩ := Finset.mem_image.mp hl; exact Sum.inl.inj hEq ▸ hw'
                · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hr; cases hEq
              ⟨fc ⟨w, hw⟩, hfc_mem ⟨w, hw⟩⟩
            | ⟨Sum.inr p, hm⟩ =>
              have hp : p.1.1 = c.1 := by
                rcases Finset.mem_union.mp hm with hl | hr
                · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hl; cases hEq
                · obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hr
                  exact (congrArg (fun q : Σ c0 : ↥DownRoots, Fin ((inLeavesDown c0.1).card - 1) => q.1.1) (Sum.inr.inj hEq)).symm
              let j : Fin ((inLeavesDown c.1).card - 1) := hp ▸ p.2
              ⟨(edum j).1, (Finset.mem_sdiff.mp (edum j).2).1⟩
          have hfwd_inj : Function.Injective fwd := by
            rintro ⟨w1 | p1, hm1⟩ ⟨w2 | p2, hm2⟩ hEq
            · dsimp only [fwd] at hEq
              have hw := hfc_inj (congrArg Subtype.val hEq)
              exact Subtype.ext (congrArg (fun z : ↥(compDown c.1) => Sum.inl z.1) hw)
            · exfalso
              dsimp only [fwd] at hEq
              have hw1 : w1 ∈ compDown c.1 := by
                rcases Finset.mem_union.mp hm1 with hl | hr
                · obtain ⟨w', hw', hE⟩ := Finset.mem_image.mp hl; exact Sum.inl.inj hE ▸ hw'
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hr; cases hE
              have hv := congrArg (fun z : ↥(P (some c)) => z.1) hEq
              dsimp only at hv
              have hm_img : fc ⟨w1, hw1⟩ ∈ imgc := Finset.mem_image_of_mem fc (Finset.mem_univ (⟨w1, hw1⟩ : ↥(compDown c.1)))
              rw [hv] at hm_img
              exact (Finset.mem_sdiff.mp (edum _).2).2 hm_img
            · exfalso
              dsimp only [fwd] at hEq
              have hw2 : w2 ∈ compDown c.1 := by
                rcases Finset.mem_union.mp hm2 with hl | hr
                · obtain ⟨w', hw', hE⟩ := Finset.mem_image.mp hl; exact Sum.inl.inj hE ▸ hw'
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hr; cases hE
              have hv := congrArg (fun z : ↥(P (some c)) => z.1) hEq
              dsimp only at hv
              have hm_img : fc ⟨w2, hw2⟩ ∈ imgc := Finset.mem_image_of_mem fc (Finset.mem_univ (⟨w2, hw2⟩ : ↥(compDown c.1)))
              rw [← hv] at hm_img
              exact (Finset.mem_sdiff.mp (edum _).2).2 hm_img
            · dsimp only [fwd] at hEq
              have hj := edum.injective (Subtype.ext (congrArg (fun z : ↥(P (some c)) => z.1) hEq))
              have hp1 : p1.1 = ⟨c.1, hcDR⟩ := by
                rcases Finset.mem_union.mp hm1 with hl | hr
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hl; cases hE
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hr
                  exact Subtype.ext (congrArg (fun q : Σ c0 : ↥DownRoots, Fin ((inLeavesDown c0.1).card - 1) => q.1.1) (Sum.inr.inj hE)).symm
              have hp2 : p2.1 = ⟨c.1, hcDR⟩ := by
                rcases Finset.mem_union.mp hm2 with hl | hr
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hl; cases hE
                · obtain ⟨_, _, hE⟩ := Finset.mem_image.mp hr
                  exact Subtype.ext (congrArg (fun q : Σ c0 : ↥DownRoots, Fin ((inLeavesDown c0.1).card - 1) => q.1.1) (Sum.inr.inj hE)).symm
              rcases p1 with ⟨c1', j1'⟩; rcases p2 with ⟨c2', j2'⟩
              dsimp only at hp1 hp2
              subst hp1; subst hp2
              have hj' : j1' = j2' := hj
              subst hj'
              rfl
          let eo : ↥(piece (some c)) ≃ ↥(P (some c)) :=
            Equiv.ofBijective fwd ((Fintype.bijective_iff_injective_and_card fwd).mpr
              ⟨hfwd_inj, by rw [Fintype.card_coe, Fintype.card_coe, hPcard (some c) (Finset.mem_univ _)]⟩)
          refine ⟨eo, fun c' hc' x y hx hy hDxy => ?_⟩
          have hc_eq : c = c' := Option.some.inj hc'
          subst hc_eq
          exact hfc_adj ⟨x, hx⟩ ⟨y, hy⟩ hDxy
      choose eP heP_adj using hpiece_bij
      -- Assemble all eP into a single bijection Ch ≃ S!
      have hex_piece : ∀ b : ↥Ch, ∃! o : Option ↥Att, b.1 ∈ piece o := by
        intro b
        have hb : b.1 ∈ Finset.univ.biUnion piece := hCh_eq ▸ b.2
        obtain ⟨o, _, hbo⟩ := Finset.mem_biUnion.mp hb
        exact ⟨o, hbo, fun o' hbo' => by
          by_contra hne; exact Finset.disjoint_left.mp (hpiece_disj o' o hne) hbo' hbo⟩
      choose pieceOf hpieceOf_mem hpieceOf_uniq using hex_piece
      let fwdAll : ↥Ch → ↥S := fun b =>
        ⟨(eP (pieceOf b) ⟨b.1, hpieceOf_mem b⟩).1,
          hPsub (pieceOf b) (Finset.mem_univ _) (eP (pieceOf b) ⟨b.1, hpieceOf_mem b⟩).2⟩
      have hfwdAll_inj : Function.Injective fwdAll := by
        intro b1 b2 hEq
        have hv : (eP (pieceOf b1) ⟨b1.1, hpieceOf_mem b1⟩).1 =
            (eP (pieceOf b2) ⟨b2.1, hpieceOf_mem b2⟩).1 := congrArg Subtype.val hEq
        have ho_eq : pieceOf b1 = pieceOf b2 := by
          by_contra hne
          exact Finset.disjoint_left.mp (hPdisj (pieceOf b1) (Finset.mem_univ _) (pieceOf b2) (Finset.mem_univ _) hne)
            (eP (pieceOf b1) ⟨b1.1, hpieceOf_mem b1⟩).2 (hv ▸ (eP (pieceOf b2) ⟨b2.1, hpieceOf_mem b2⟩).2)
        have hcast : ∀ (o1 o2 : Option ↥Att) (h : o1 = o2) (x : W') (hx : x ∈ piece o2),
            (eP o2 ⟨x, hx⟩).1 = (eP o1 ⟨x, h ▸ hx⟩).1 := by rintro o _ rfl _ _; rfl
        have hb_eq : (⟨b1.1, hpieceOf_mem b1⟩ : ↥(piece (pieceOf b1))) =
            ⟨b2.1, ho_eq ▸ hpieceOf_mem b2⟩ := by
          apply (eP (pieceOf b1)).injective
          apply Subtype.ext
          rw [hv, hcast (pieceOf b1) (pieceOf b2) ho_eq b2.1 (hpieceOf_mem b2)]
        exact Subtype.ext (congrArg (fun z : ↥(piece (pieceOf b1)) => z.1) hb_eq)
      let eAll : ↥Ch ≃ ↥S := Equiv.ofBijective fwdAll ((Fintype.bijective_iff_injective_and_card fwdAll).mpr
        ⟨hfwdAll_inj, by rw [Fintype.card_coe, Fintype.card_coe, hSc]⟩)
      refine ⟨eAll, fun u' hu' c hc huc x y hx hy hDxy => ?_⟩
      have hu_eq : u = u' := Sum.inl.inj hu'
      subst hu_eq
      let cAtt : ↥Att := ⟨c, Finset.mem_filter.mpr ⟨hc, huc⟩⟩
      let bx : ↥Ch := ⟨Sum.inl x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨c, hc, hx, huc⟩⟩⟩
      let by_ : ↥Ch := ⟨Sum.inl y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨c, hc, hy, huc⟩⟩⟩
      have hpx : pieceOf bx = some cAtt :=
        (hpieceOf_uniq bx (some cAtt) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))).symm
      have hpy : pieceOf by_ = some cAtt :=
        (hpieceOf_uniq by_ (some cAtt) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy))).symm
      have heqx : (eAll bx).1 = (eP (some cAtt) ⟨Sum.inl x, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)⟩).1 := by
        change (eP (pieceOf bx) ⟨bx.1, hpieceOf_mem bx⟩).1 = _
        generalize_proofs hp1; revert hp1; rw [hpx]; intro; rfl
      have heqy : (eAll by_).1 = (eP (some cAtt) ⟨Sum.inl y, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)⟩).1 := by
        change (eP (pieceOf by_) ⟨by_.1, hpieceOf_mem by_⟩).1 = _
        generalize_proofs hp2; revert hp2; rw [hpy]; intro; rfl
      rw [heqx, heqy]
      exact heP_adj (some cAtt) cAtt rfl x y hx hy hDxy
  choose oracle horacle_adj using horacle_ex
  -- Step 3: Run online_greedy_out_arborescence on (W', D') and restrict to W!
  obtain ⟨f', hf'_inj, _, hf'_adj, hf'_or⟩ := online_greedy_out_arborescence D' ⟨rk', hRank'⟩ hInDeg'
    (Sum.inl r) hroot' G hR hm' oracle
  refine ⟨⟨fun w => σ (f' (Sum.inl w)), ?_⟩, fun u v h => Sum.inl.inj (hf'_inj (σ.injective h))⟩
  intro x y hDxy
  have hTxy : T.Adj x y := hO.1 x y hDxy
  rcases hT.dist_eq_dist_add_one_of_adj r hTxy with hdown | hup
  · -- DownAdj x y: x and y lie in the same compDown c for c = topDown x ∈ DownRoots!
    have hDxy_down : DownAdj x y := ⟨hDxy, by omega⟩
    obtain ⟨c, ⟨hxc, hcn⟩, _⟩ := htop x
    have hc_has : ∃ z : W, DownAdj z c := by
      cases hxc using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd hDxy_down (hcn y)
      | head hstep hrest => exact exists_step_of_reflTransGen_step hstep hrest
    have hcDR : c ∈ DownRoots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_has, hcn⟩
    have hx_comp : x ∈ compDown c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxc⟩
    have hy_comp : y ∈ compDown c := by
      rcases Relation.ReflTransGen.cases_head hxc with rfl | ⟨z, hxz, hzc⟩
      · exact absurd hDxy_down (hcn y)
      · have hzy : z = y := huniq_down x z y hxz hDxy_down
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy ▸ hzc⟩
    obtain ⟨u, huc, _⟩ := hc_up_par c hcDR
    obtain ⟨S, hSc, hfor⟩ := hf'_or (Sum.inl u)
    have hfx := hfor (Sum.inl x) (Or.inr ⟨c, hcDR, hx_comp, huc⟩)
    have hfy := hfor (Sum.inl y) (Or.inr ⟨c, hcDR, hy_comp, huc⟩)
    rw [hfx, hfy]
    exact horacle_adj (Sum.inl u) S hSc u rfl c hcDR huc x y hx_comp hy_comp hDxy
  · -- UpAdj x y: D'.Adj (Sum.inl x) (Sum.inl y) holds directly!
    have hDxy_up : UpAdj x y := ⟨hDxy, by omega⟩
    by_cases hycomp : inAnyComp y
    · obtain ⟨c, hcDR, hyc⟩ := hycomp
      have hyc_eq : y = c := by
        have hpath := (Finset.mem_filter.mp hyc).2
        rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨z, hyz, _⟩
        · rfl
        · have hyr : y ≠ r := fun h => by subst h; have := hup; simp only [SimpleGraph.dist_self] at this; omega
          obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r y hyr
          have hx_eq : x = p := hpu x ⟨hTxy, by omega⟩
          have hz_eq : z = p := hpu z ⟨(hO.1 y z hyz.1).symm, hyz.2⟩
          exact absurd (hx_eq ▸ hz_eq ▸ hyz.1) (not_adj_rev_of_isOrientation hO hDxy)
      subst hyc_eq
      exact hf'_adj (Sum.inl x) (Sum.inl y) (Or.inr ⟨y, hcDR, hyc, hDxy_up⟩)
    · exact hf'_adj (Sum.inl x) (Sum.inl y) (Or.inl ⟨hycomp, hDxy_up⟩)

-- ============================================================================
-- Stage 2B: Gamma sum bound, optimal root is a source, Theorem 4 & Corollary 5
-- ============================================================================

-- Tree re-rooting lemma across an edge s ~ r: every other edge {x, y} != {s, r}
-- preserves the relative distance ordering between s and r!
lemma tree_dist_lt_iff_of_adj_root {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) {s r x y : W}
    (hTsr : T.Adj s r) (hTxy : T.Adj x y)
    (hne1 : ¬ (x = s ∧ y = r)) (hne2 : ¬ (x = r ∧ y = s)) :
    T.dist s y < T.dist s x ↔ T.dist r y < T.dist r x := by
  have himp : ∀ (a b u v : W), T.Adj a b → T.Adj u v → ¬ (u = a ∧ v = b) →
      T.dist b v < T.dist b u → T.dist a v < T.dist a u := by
    intro a b u v hTab hTuv hne hlt_b
    rcases hT.dist_eq_dist_add_one_of_adj a hTuv with h1 | h2
    · omega
    · exfalso
      have hbu : T.dist b u = T.dist b v + 1 := by
        rcases hT.dist_eq_dist_add_one_of_adj b hTuv with h3 | h4 <;> omega
      have hdu : T.dist u b = T.dist u a + 1 ∨ T.dist u a = T.dist u b + 1 :=
        hT.dist_eq_dist_add_one_of_adj u hTab.symm
      have hdv : T.dist v b = T.dist v a + 1 ∨ T.dist v a = T.dist v b + 1 :=
        hT.dist_eq_dist_add_one_of_adj v hTab.symm
      rw [SimpleGraph.dist_comm (u := u) (v := b), SimpleGraph.dist_comm (u := u) (v := a)] at hdu
      rw [SimpleGraph.dist_comm (u := v) (v := b), SimpleGraph.dist_comm (u := v) (v := a)] at hdv
      have h_eq : T.dist b v = T.dist a u ∧ T.dist a v = T.dist b v + 1 := by omega
      -- Build two distinct paths from v to a: one via b (if q : b ~> v), one via u (u ~> a)!
      obtain ⟨q, hqp, hqlen⟩ := (hT.connected b v).exists_path_of_dist
      have ha_not_q : a ∉ q.support := fun ha => by
        have hle : T.dist a v ≤ (q.dropUntil a ha).length := SimpleGraph.dist_le _
        have hlt : (q.dropUntil a ha).length ≤ q.length := SimpleGraph.Walk.length_dropUntil_le_length q ha
        omega
      let w1 : T.Walk a v := SimpleGraph.Walk.cons hTab q
      have hw1p : w1.IsPath := SimpleGraph.Walk.IsPath.cons hqp ha_not_q
      obtain ⟨q2, hq2p, hq2len⟩ := (hT.connected a u).exists_path_of_dist
      have hv_not_q2 : v ∉ q2.support := fun hv => by
        have hle : T.dist a v ≤ (q2.takeUntil v hv).length := SimpleGraph.dist_le _
        have hlt : (q2.takeUntil v hv).length ≤ q2.length := SimpleGraph.Walk.length_takeUntil_le_length q2 hv
        omega
      let w2 : T.Walk v a := SimpleGraph.Walk.cons hTuv.symm q2.reverse
      have hw2p : w2.IsPath := SimpleGraph.Walk.IsPath.cons hq2p.reverse (by simpa using hv_not_q2)
      have heq : w1.reverse = w2 := congrArg Subtype.val
        ((hT.isAcyclic.subsingleton_path v a).elim ⟨w1.reverse, hw1p.reverse⟩ ⟨w2, hw2p⟩)
      have hsnd := congrArg (fun p : T.Walk v a => p.support[1]?) heq
      have h2_snd : w2.support[1]? = some u := by
        simp only [w2, SimpleGraph.Walk.support_cons, List.getElem?_cons_succ]
        cases hq2 : q2.reverse <;> simp [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons]
      rw [h2_snd] at hsnd
      -- Inspect q.reverse to find w1.reverse.support[1]?
      have hqrev_len : q.reverse.length = T.dist b v := by simpa using hqlen
      cases hqr : q.reverse with
      | nil =>
        -- Here v has been unified with b! So q = nil and w1.reverse = cons hTab.symm nil.
        have hqnil : q = SimpleGraph.Walk.nil := by
          have := congrArg SimpleGraph.Walk.reverse hqr
          simpa using this
        have hw1r : w1.reverse = SimpleGraph.Walk.cons hTab.symm SimpleGraph.Walk.nil := by
          simp only [w1, hqnil, SimpleGraph.Walk.reverse_cons, SimpleGraph.Walk.reverse_nil,
            SimpleGraph.Walk.nil_append]
        rw [hw1r] at hsnd
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.getElem?_cons_succ, List.getElem?_cons_zero] at hsnd
        exact hne ⟨(Option.some.inj hsnd).symm, rfl⟩
      | @cons _ z _ hTvz q' =>
        have hw1r : w1.reverse = SimpleGraph.Walk.cons hTvz (q'.concat hTab.symm) := by
          simp only [w1, SimpleGraph.Walk.reverse_cons, hqr, SimpleGraph.Walk.cons_append,
            SimpleGraph.Walk.concat_eq_append]
        rw [hw1r] at hsnd
        simp only [SimpleGraph.Walk.support_cons, List.getElem?_cons_succ] at hsnd
        have hzu : z = u := by
          have h0 : (q'.concat hTab.symm).support[0]? = some z := by
            cases hqc : q'.concat hTab.symm <;> simp [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons]
          rw [h0] at hsnd
          exact Option.some.inj hsnd
        subst hzu
        have hq'len : q'.length + 1 = T.dist b v := by
          rw [hqr, SimpleGraph.Walk.length_cons] at hqrev_len; omega
        have hdz : T.dist b z ≤ q'.length := by
          have := SimpleGraph.dist_le q'.reverse; simpa using this
        omega
  exact ⟨fun h => himp r s x y hTsr.symm hTxy hne2 h, fun h => himp s r x y hTsr hTxy hne1 h⟩

-- Dross-Havet gamma sum bound (sharpened by 1 for leaf OR mixed roots!):
-- If r is a leaf OR r has both an in-neighbor and an out-neighbor, then
-- gamma_r^down(D) + gamma_r^down(D_rev) <= n + k - 3!
lemma dross_havet_gamma_sum_le_of_leaf_or_mixed {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (r : W)
    (hr_good : (Finset.univ.filter (fun z : W => D.Adj r z ∨ D.Adj z r)).card = 1 ∨
      ((∃ s : W, D.Adj s r) ∧ (∃ t : W, D.Adj r t))) :
    (∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj x c ∧ T.dist r c < T.dist r x) ∧
        (∀ p : W, ¬ (D.Adj c p ∧ T.dist r p < T.dist r c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r w < T.dist r x))).card - 2)) +
    (∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj c x ∧ T.dist r c < T.dist r x) ∧
        (∀ p : W, ¬ (D.Adj p c ∧ T.dist r p < T.dist r c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r y < T.dist r x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r y < T.dist r x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r w < T.dist r x))).card - 2)) ≤
      n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card - 3 := by
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  have hOrev : Drev.IsOrientation T :=
    ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
  let DownAdj : W → W → Prop := fun x y => D.Adj x y ∧ T.dist r y < T.dist r x
  let UpAdj : W → W → Prop := fun x y => Drev.Adj x y ∧ T.dist r y < T.dist r x
  let DownRoots : Finset W := Finset.univ.filter (fun c : W => (∃ x, DownAdj x c) ∧ ∀ p, ¬ DownAdj c p)
  let UpRoots : Finset W := Finset.univ.filter (fun c : W => (∃ x, UpAdj x c) ∧ ∀ p, ¬ UpAdj c p)
  let compD : W → Finset W := fun c => Finset.univ.filter (fun w => Relation.ReflTransGen DownAdj w c)
  let compU : W → Finset W := fun c => Finset.univ.filter (fun w => Relation.ReflTransGen UpAdj w c)
  let leavesD : W → Finset W := fun c => (compD c).filter (fun w => ∀ x, ¬ DownAdj x w)
  let leavesU : W → Finset W := fun c => (compU c).filter (fun w => ∀ x, ¬ UpAdj x w)
  obtain ⟨huniqD, hdistD, _, hdisjD, _⟩ := down_forest_structure hT hO r
  obtain ⟨huniqU, hdistU, _, hdisjU, _⟩ := down_forest_structure hT hOrev r
  -- Basic size bounds for each component in DownRoots and UpRoots
  have hsz_gen : ∀ (D0 : Digraph W) [DecidableRel D0.Adj] (hO0 : D0.IsOrientation T),
      let adj0 : W → W → Prop := fun x y => D0.Adj x y ∧ T.dist r y < T.dist r x
      let roots0 := Finset.univ.filter (fun c : W => (∃ x, adj0 x c) ∧ ∀ p, ¬ adj0 c p)
      let comp0 : W → Finset W := fun c => Finset.univ.filter (fun w => Relation.ReflTransGen adj0 w c)
      let leaves0 : W → Finset W := fun c => (comp0 c).filter (fun w => ∀ x, ¬ adj0 x w)
      ∀ c ∈ roots0, c ∈ comp0 c ∧ 1 ≤ (comp0 c).card ∧ 1 ≤ (leaves0 c).card ∧ c ∉ leaves0 c := by
    intro D0 _ hO0 adj0 roots0 comp0 leaves0 c hc
    obtain ⟨x0, hx0⟩ := (Finset.mem_filter.mp hc).2.1
    have hcm : c ∈ comp0 c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
    obtain ⟨wmax, hwmax, hmax⟩ := Finset.exists_max_image (comp0 c) (T.dist r) ⟨c, hcm⟩
    have hl1 : 1 ≤ (leaves0 c).card := by
      refine Finset.one_le_card.mpr ⟨wmax, Finset.mem_filter.mpr ⟨hwmax, fun y hy => ?_⟩⟩
      have hym : y ∈ comp0 c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .head hy (Finset.mem_filter.mp hwmax).2⟩
      have := hmax y hym; have := hy.2; omega
    have hcnl : c ∉ leaves0 c := fun h => (Finset.mem_filter.mp h).2 x0 hx0
    exact ⟨hcm, Finset.one_le_card.mpr ⟨c, hcm⟩, hl1, hcnl⟩
  have hszD := hsz_gen D hO
  have hszU := hsz_gen Drev hOrev
  -- Helper: any w ∈ (compD c).erase c has an outgoing DownAdj to its parent; similarly for compU.
  -- Hence (compD c).erase c and (compU c').erase c' are ALL pairwise disjoint subsets of univ.erase r!
  have hhas_step_D : ∀ c ∈ DownRoots, ∀ w ∈ (compD c).erase c, ∃ p, DownAdj w p := by
    intro c _ w hw
    have hne : w ≠ c := (Finset.mem_erase.mp hw).1
    have hp := (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).2
    rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨p, hwp, _⟩
    · exact absurd rfl hne
    · exact ⟨p, hwp⟩
  have hhas_step_U : ∀ c ∈ UpRoots, ∀ w ∈ (compU c).erase c, ∃ p, UpAdj w p := by
    intro c _ w hw
    have hne : w ≠ c := (Finset.mem_erase.mp hw).1
    have hp := (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).2
    rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨p, hwp, _⟩
    · exact absurd rfl hne
    · exact ⟨p, hwp⟩
  have hno_both_step : ∀ w p1 p2, DownAdj w p1 → UpAdj w p2 → False := by
    intro w p1 p2 h1 h2
    have hwr : w ≠ r := fun h => by subst h; have := h1.2; simp only [SimpleGraph.dist_self] at this; omega
    obtain ⟨p, _, hpu⟩ := tree_exists_unique_parent hT r w hwr
    have hp1 : p1 = p := hpu p1 ⟨(hO.1 w p1 h1.1).symm, h1.2⟩
    have hp2 : p2 = p := hpu p2 ⟨(hOrev.1 w p2 h2.1).symm, h2.2⟩
    exact not_adj_rev_of_isOrientation hO h1.1 (hp1 ▸ hp2 ▸ h2.1)
  -- Part 1: Sum of (|comp| - 1) <= n - 1!
  let NonRootD := DownRoots.biUnion (fun c => (compD c).erase c)
  let NonRootU := UpRoots.biUnion (fun c => (compU c).erase c)
  have hPart1 : (∑ c ∈ DownRoots, ((compD c).card - 1)) + (∑ c ∈ UpRoots, ((compU c).card - 1)) ≤ n - 1 := by
    have hD_eq : NonRootD.card = ∑ c ∈ DownRoots, ((compD c).card - 1) := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun c hc => Finset.card_erase_of_mem (hszD c hc).1)
      · intro c1 hc1 c2 hc2 hne
        exact (hdisjD c1 hc1 c2 hc2 hne).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hU_eq : NonRootU.card = ∑ c ∈ UpRoots, ((compU c).card - 1) := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun c hc => Finset.card_erase_of_mem (hszU c hc).1)
      · intro c1 hc1 c2 hc2 hne
        exact (hdisjU c1 hc1 c2 hc2 hne).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hdisj_DU : Disjoint NonRootD NonRootU := by
      refine Finset.disjoint_left.mpr (fun w hw1 hw2 => ?_)
      obtain ⟨c1, hc1, hw1'⟩ := Finset.mem_biUnion.mp hw1
      obtain ⟨c2, hc2, hw2'⟩ := Finset.mem_biUnion.mp hw2
      obtain ⟨p1, hp1⟩ := hhas_step_D c1 hc1 w hw1'
      obtain ⟨p2, hp2⟩ := hhas_step_U c2 hc2 w hw2'
      exact hno_both_step w p1 p2 hp1 hp2
    have hsub : NonRootD ∪ NonRootU ⊆ Finset.univ.erase r := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hwr
      have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
      rcases Finset.mem_union.mp hw with h1 | h2
      · obtain ⟨c1, hc1, hw1'⟩ := Finset.mem_biUnion.mp h1
        obtain ⟨p1, hp1⟩ := hhas_step_D c1 hc1 w hw1'
        have := hp1.2; rw [hwr] at this; omega
      · obtain ⟨c2, hc2, hw2'⟩ := Finset.mem_biUnion.mp h2
        obtain ⟨p2, hp2⟩ := hhas_step_U c2 hc2 w hw2'
        have := hp2.2; rw [hwr] at this; omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_DU, hD_eq, hU_eq,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, hW] at hcard
    exact hcard
  -- Part 2: Sum of (|leaves| - 1) <= k - 2 (since r is a leaf and r ∉ AllLD ∪ AllLU)!
  let LeavesW := Finset.univ.filter (fun w : W =>
    (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)
  let AllLD := DownRoots.biUnion leavesD
  let AllLU := UpRoots.biUnion leavesU
  have hPart2 : (∑ c ∈ DownRoots, ((leavesD c).card - 1)) + (∑ c ∈ UpRoots, ((leavesU c).card - 1)) + 2 ≤
      LeavesW.card := by
    have hLD_eq : AllLD.card = ∑ c ∈ DownRoots, (leavesD c).card := by
      rw [Finset.card_biUnion]
      intro c1 hc1 c2 hc2 hne
      exact (hdisjD c1 hc1 c2 hc2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hLU_eq : AllLU.card = ∑ c ∈ UpRoots, (leavesU c).card := by
      rw [Finset.card_biUnion]
      intro c1 hc1 c2 hc2 hne
      exact (hdisjU c1 hc1 c2 hc2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hdisj_L : Disjoint AllLD AllLU := by
      refine Finset.disjoint_left.mpr (fun w hw1 hw2 => ?_)
      obtain ⟨c1, hc1, hw1'⟩ := Finset.mem_biUnion.mp hw1
      obtain ⟨c2, hc2, hw2'⟩ := Finset.mem_biUnion.mp hw2
      have hne1 : w ≠ c1 := fun h => (hszD c1 hc1).2.2.2 (h ▸ hw1')
      have hne2 : w ≠ c2 := fun h => (hszU c2 hc2).2.2.2 (h ▸ hw2')
      obtain ⟨p1, hp1⟩ := hhas_step_D c1 hc1 w (Finset.mem_erase.mpr ⟨hne1, (Finset.mem_filter.mp hw1').1⟩)
      obtain ⟨p2, hp2⟩ := hhas_step_U c2 hc2 w (Finset.mem_erase.mpr ⟨hne2, (Finset.mem_filter.mp hw2').1⟩)
      exact hno_both_step w p1 p2 hp1 hp2
    -- Every w ∈ AllLD ∪ AllLU satisfies w ≠ r, hence belongs to LeavesW.erase r ∪ (DownRoots.erase r ∪ UpRoots.erase r)!
    have hsub_L : AllLD ∪ AllLU ⊆ LeavesW.erase r ∪ (DownRoots.erase r ∪ UpRoots.erase r) := by
      intro w hw
      have hwr : w ≠ r := by
        intro hweq
        have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
        rcases Finset.mem_union.mp hw with h1 | h2
        · obtain ⟨c1, hc1, hw1'⟩ := Finset.mem_biUnion.mp h1
          have hne1 : w ≠ c1 := fun h => (hszD c1 hc1).2.2.2 (h ▸ hw1')
          obtain ⟨p1, hp1⟩ := hhas_step_D c1 hc1 w (Finset.mem_erase.mpr ⟨hne1, (Finset.mem_filter.mp hw1').1⟩)
          have := hp1.2; rw [hweq] at this; omega
        · obtain ⟨c2, hc2, hw2'⟩ := Finset.mem_biUnion.mp h2
          have hne2 : w ≠ c2 := fun h => (hszU c2 hc2).2.2.2 (h ▸ hw2')
          obtain ⟨p2, hp2⟩ := hhas_step_U c2 hc2 w (Finset.mem_erase.mpr ⟨hne2, (Finset.mem_filter.mp hw2').1⟩)
          have := hp2.2; rw [hweq] at this; omega
      by_cases hwL : w ∈ LeavesW
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwr, hwL⟩)
      · refine Finset.mem_union_right _ ?_
        -- w has a tree-child x (since w ∉ LeavesW and w ≠ r)!
        have hex_child : ∃ x : W, T.Adj w x ∧ T.dist r w < T.dist r x := by
          have hdeg_eq : (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card =
              (Finset.univ.filter (fun z : W => T.Adj w z)).card := by
            congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun h => by rcases h with h1 | h2; exact hO.1 w z h1; exact (hO.1 z w h2).symm,
              fun h => adj_or_rev_of_isOrientation hO h⟩
          have hne1 : (Finset.univ.filter (fun z : W => T.Adj w z)).card ≠ 1 := fun h1 =>
            hwL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg_eq.trans h1⟩)
          obtain ⟨p, ⟨hTpw, hdist_pw⟩, hpu⟩ := tree_exists_unique_parent hT r w hwr
          have hp_mem : p ∈ Finset.univ.filter (fun z : W => T.Adj w z) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTpw.symm⟩
          have hpos : 1 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card :=
            Finset.one_le_card.mpr ⟨p, hp_mem⟩
          have hrem : ((Finset.univ.filter (fun z : W => T.Adj w z)).erase p).Nonempty := by
            refine Finset.card_pos.mp ?_; rw [Finset.card_erase_of_mem hp_mem]; omega
          obtain ⟨x, hx⟩ := hrem
          have hxne : x ≠ p := (Finset.mem_erase.mp hx).1
          have hTwx : T.Adj w x := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
          rcases hT.dist_eq_dist_add_one_of_adj r hTwx with h1 | h2
          · exact absurd (hpu x ⟨hTwx.symm, by omega⟩) hxne
          · exact ⟨x, hTwx, by omega⟩
        obtain ⟨x, hTwx, hdist_wx⟩ := hex_child
        rcases Finset.mem_union.mp hw with h1 | h2
        · -- w ∈ AllLD → w ∈ UpRoots.erase r!
          obtain ⟨c1, hc1, hw1'⟩ := Finset.mem_biUnion.mp h1
          have hne1 : w ≠ c1 := fun h => (hszD c1 hc1).2.2.2 (h ▸ hw1')
          obtain ⟨p1, hp1⟩ := hhas_step_D c1 hc1 w (Finset.mem_erase.mpr ⟨hne1, (Finset.mem_filter.mp hw1').1⟩)
          have hno_in_D : ∀ y, ¬ DownAdj y w := (Finset.mem_filter.mp hw1').2
          have hUxw : UpAdj x w := by
            rcases adj_or_rev_of_isOrientation hO hTwx with h | h
            · exact ⟨h, hdist_wx⟩
            · exact absurd ⟨h, hdist_wx⟩ (hno_in_D x)
          refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hUxw⟩, ?_⟩⟩)
          intro p2 hp2; exact hno_both_step w p1 p2 hp1 hp2
        · -- w ∈ AllLU → w ∈ DownRoots.erase r!
          obtain ⟨c2, hc2, hw2'⟩ := Finset.mem_biUnion.mp h2
          have hne2 : w ≠ c2 := fun h => (hszU c2 hc2).2.2.2 (h ▸ hw2')
          obtain ⟨p2, hp2⟩ := hhas_step_U c2 hc2 w (Finset.mem_erase.mpr ⟨hne2, (Finset.mem_filter.mp hw2').1⟩)
          have hno_in_U : ∀ y, ¬ UpAdj y w := (Finset.mem_filter.mp hw2').2
          have hDxw : DownAdj x w := by
            rcases adj_or_rev_of_isOrientation hO hTwx with h | h
            · exact absurd ⟨h, hdist_wx⟩ (hno_in_U x)
            · exact ⟨h, hdist_wx⟩
          refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hDxw⟩, ?_⟩⟩)
          intro p1 hp1; exact hno_both_step w p1 p2 hp1 hp2
    -- Since n >= 2, r has a neighbor x, so r ∈ DownRoots ∨ r ∈ UpRoots!
    have hr_in_root : r ∈ DownRoots ∨ r ∈ UpRoots := by
      obtain ⟨v1, v2, hv12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
      have hex_ne : ∃ v0 : W, v0 ≠ r := by
        by_cases h1 : v1 = r; exact ⟨v2, fun h => hv12 (h1.trans h.symm)⟩; exact ⟨v1, h1⟩
      obtain ⟨v0, hv0⟩ := hex_ne
      obtain ⟨p⟩ := hT.connected r v0
      cases p with
      | nil => exact absurd rfl hv0
      | @cons _ x _ hTrx _ =>
        have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
        have hlt : T.dist r r < T.dist r x := by
          rcases hT.dist_eq_dist_add_one_of_adj r hTrx with h1 | h2 <;> omega
        rcases adj_or_rev_of_isOrientation hO hTrx with h | h
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, h, hlt⟩, fun q hq => by have := hq.2; omega⟩)
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, h, hlt⟩, fun q hq => by have := hq.2; omega⟩)
    have herase_le : (DownRoots.erase r).card + (UpRoots.erase r).card + 1 ≤ DownRoots.card + UpRoots.card := by
      rcases hr_in_root with hrD | hrU
      · rw [Finset.card_erase_of_mem hrD]
        have h1 : 1 ≤ DownRoots.card := Finset.one_le_card.mpr ⟨r, hrD⟩
        have h2 : (UpRoots.erase r).card ≤ UpRoots.card := Finset.card_erase_le
        omega
      · rw [Finset.card_erase_of_mem hrU]
        have h1 : 1 ≤ UpRoots.card := Finset.one_le_card.mpr ⟨r, hrU⟩
        have h2 : (DownRoots.erase r).card ≤ DownRoots.card := Finset.card_erase_le
        omega
    have hsumD_sub : (∑ c ∈ DownRoots, ((leavesD c).card - 1)) + DownRoots.card = ∑ c ∈ DownRoots, (leavesD c).card := by
      have h1 : DownRoots.card = ∑ _c ∈ DownRoots, (1 : ℕ) := by simp
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have hl : 1 ≤ (leavesD c).card := (hszD c hc).2.2.1
      exact Nat.sub_add_cancel hl
    have hsumU_sub : (∑ c ∈ UpRoots, ((leavesU c).card - 1)) + UpRoots.card = ∑ c ∈ UpRoots, (leavesU c).card := by
      have h1 : UpRoots.card = ∑ _c ∈ UpRoots, (1 : ℕ) := by simp
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have hl : 1 ≤ (leavesU c).card := (hszU c hc).2.2.1
      exact Nat.sub_add_cancel hl
    have hsave : (LeavesW.erase r).card + (DownRoots.erase r).card + (UpRoots.erase r).card + 2 ≤
        LeavesW.card + DownRoots.card + UpRoots.card := by
      rcases hr_good with hr_leaf | ⟨⟨s, hsr⟩, ⟨t, hrt⟩⟩
      · have hr_memL : r ∈ LeavesW := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_leaf⟩
        have hLer_card : (LeavesW.erase r).card + 1 = LeavesW.card := by
          rw [Finset.card_erase_of_mem hr_memL]
          exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨r, hr_memL⟩)
        exact (by intros; omega : ∀ a b c d e f : ℕ, a + 1 = d → b + c + 1 ≤ e + f → a + b + c + 2 ≤ d + e + f)
          _ _ _ _ _ _ hLer_card herase_le
      · have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
        have hlt_s : T.dist r r < T.dist r s := by
          rcases hT.dist_eq_dist_add_one_of_adj r (hO.1 s r hsr).symm with h1 | h2 <;> omega
        have hlt_t : T.dist r r < T.dist r t := by
          rcases hT.dist_eq_dist_add_one_of_adj r (hO.1 r t hrt) with h1 | h2 <;> omega
        have hrD : r ∈ DownRoots :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, hsr, hlt_s⟩, fun q hq => by have := hq.2; omega⟩
        have hrU : r ∈ UpRoots :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, hrt, hlt_t⟩, fun q hq => by have := hq.2; omega⟩
        have hDer : (DownRoots.erase r).card + 1 = DownRoots.card := by
          rw [Finset.card_erase_of_mem hrD]; exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨r, hrD⟩)
        have hUer : (UpRoots.erase r).card + 1 = UpRoots.card := by
          rw [Finset.card_erase_of_mem hrU]; exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨r, hrU⟩)
        have hLer : (LeavesW.erase r).card ≤ LeavesW.card := Finset.card_erase_le
        exact (by intros; omega : ∀ a b c d e f : ℕ, a ≤ d → b + 1 = e → c + 1 = f → a + b + c + 2 ≤ d + e + f)
          _ _ _ _ _ _ hLer hDer hUer
    have hc1 := Finset.card_le_card hsub_L
    have hc2 := Finset.card_union_le (LeavesW.erase r) (DownRoots.erase r ∪ UpRoots.erase r)
    have hc3 := Finset.card_union_le (DownRoots.erase r) (UpRoots.erase r)
    rw [Finset.card_union_of_disjoint hdisj_L, hLD_eq, hLU_eq] at hc1
    have harith : ∀ a b c d e f g h i j k : ℕ,
        a + c = e → b + d = f → e + f ≤ g → g ≤ h + i → i ≤ j + k →
        h + j + k + 2 ≤ LeavesW.card + c + d → a + b + 2 ≤ LeavesW.card := by
      intros; omega
    exact harith _ _ _ _ _ _ _ _ _ _ _ hsumD_sub hsumU_sub hc1 hc2 hc3 hsave
  -- Combine Part 1 + Part 2 using Finset.sum_congr (avoiding DecidablePred definitional unfolding)!
  have hsplitD : (∑ c ∈ DownRoots, ((compD c).card + (leavesD c).card - 2)) =
      (∑ c ∈ DownRoots, ((compD c).card - 1)) + (∑ c ∈ DownRoots, ((leavesD c).card - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have h1 : 1 ≤ (compD c).card := (hszD c hc).2.1
    have h2 : 1 ≤ (leavesD c).card := (hszD c hc).2.2.1
    omega
  have hsplitU : (∑ c ∈ UpRoots, ((compU c).card + (leavesU c).card - 2)) =
      (∑ c ∈ UpRoots, ((compU c).card - 1)) + (∑ c ∈ UpRoots, ((leavesU c).card - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have h1 : 1 ≤ (compU c).card := (hszU c hc).2.1
    have h2 : 1 ≤ (leavesU c).card := (hszU c hc).2.2.1
    omega
  have hgoalD : (∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj x c ∧ T.dist r c < T.dist r x) ∧
        (∀ p : W, ¬ (D.Adj c p ∧ T.dist r p < T.dist r c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r y < T.dist r x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r w < T.dist r x))).card - 2)) =
      ∑ c ∈ DownRoots, ((compD c).card + (leavesD c).card - 2) := by
    refine Finset.sum_congr (by ext c; simp only [DownRoots, DownAdj, Finset.mem_filter, Finset.mem_univ, true_and]) (fun c _ => ?_)
    congr 1
  have hgoalU : (∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj c x ∧ T.dist r c < T.dist r x) ∧
        (∀ p : W, ¬ (D.Adj p c ∧ T.dist r p < T.dist r c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r y < T.dist r x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r y < T.dist r x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r w < T.dist r x))).card - 2)) =
      ∑ c ∈ UpRoots, ((compU c).card + (leavesU c).card - 2) := by
    refine Finset.sum_congr (by ext c; simp only [UpRoots, UpAdj, Drev, Finset.mem_filter, Finset.mem_univ, true_and]) (fun c _ => ?_)
    congr 1
  have hfin : ∀ a b c d k : ℕ, 2 ≤ n → a + b ≤ n - 1 → c + d + 2 ≤ k → (a + c) + (b + d) ≤ n + k - 3 := by
    intros; omega
  rw [hgoalD, hgoalU, hsplitD, hsplitU]
  exact hfin _ _ _ _ _ hn hPart1 hPart2

-- Re-rooting monotonicity: if D.Adj s r, then gamma_s^down(D) < gamma_r^down(D)!
lemma dross_havet_gamma_lt_of_in_neighbor
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    {s r : W} (hDsr : D.Adj s r) :
    let gammaAt : W → ℕ := fun r0 =>
      ∑ c ∈ Finset.univ.filter (fun c : W =>
          (∃ x : W, D.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
          (∀ p : W, ¬ (D.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
        ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
         ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
           (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)
    gammaAt s < gammaAt r := by
  intro gammaAt
  have hTsr : T.Adj s r := hO.1 s r hDsr
  have hsr_ne : s ≠ r := T.ne_of_adj hTsr
  let adjR : W → W → Prop := fun x y => D.Adj x y ∧ T.dist r y < T.dist r x
  let adjS : W → W → Prop := fun x y => D.Adj x y ∧ T.dist s y < T.dist s x
  let rootsR := Finset.univ.filter (fun c : W => (∃ x, adjR x c) ∧ ∀ p, ¬ adjR c p)
  let rootsS := Finset.univ.filter (fun c : W => (∃ x, adjS x c) ∧ ∀ p, ¬ adjS c p)
  let compR : W → Finset W := fun c => Finset.univ.filter (fun w => Relation.ReflTransGen adjR w c)
  let compS : W → Finset W := fun c => Finset.univ.filter (fun w => Relation.ReflTransGen adjS w c)
  let leavesR : W → Finset W := fun c => (compR c).filter (fun w => ∀ x, ¬ adjR x w)
  let leavesS : W → Finset W := fun c => (compS c).filter (fun w => ∀ x, ¬ adjS x w)
  obtain ⟨huniqR, _, _, hdisjR, _⟩ := down_forest_structure hT hO r
  obtain ⟨_, _, htopS, _, _⟩ := down_forest_structure hT hO s
  have hrr0 : T.dist r r = 0 := SimpleGraph.dist_self
  have hss0 : T.dist s s = 0 := SimpleGraph.dist_self
  have hadjR_sr : adjR s r := ⟨hDsr, by rcases hT.dist_eq_dist_add_one_of_adj r hTsr with h1 | h2 <;> omega⟩
  have hnot_adjS_sr : ¬ adjS s r := fun h => by have := h.2; omega
  -- Key characterization: adjS x y ↔ adjR x y ∧ ¬ (x = s ∧ y = r)!
  have hadjS_iff : ∀ x y : W, adjS x y ↔ adjR x y ∧ ¬ (x = s ∧ y = r) := by
    intro x y
    by_cases h1 : x = s ∧ y = r
    · rcases h1 with ⟨rfl, rfl⟩; exact ⟨fun h => absurd h hnot_adjS_sr, fun h => absurd ⟨rfl, rfl⟩ h.2⟩
    · by_cases h2 : x = r ∧ y = s
      · rcases h2 with ⟨rfl, rfl⟩
        exact ⟨fun h => absurd h.1 (not_adj_rev_of_isOrientation hO hDsr),
          fun h => absurd h.1.1 (not_adj_rev_of_isOrientation hO hDsr)⟩
      · constructor
        · intro h; exact ⟨⟨h.1, (tree_dist_lt_iff_of_adj_root hT hTsr (hO.1 x y h.1) h1 h2).mp h.2⟩, h1⟩
        · intro h; exact ⟨h.1.1, (tree_dist_lt_iff_of_adj_root hT hTsr (hO.1 x y h.1.1) h1 h2).mpr h.1.2⟩
  have hr_rootR : r ∈ rootsR :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, hadjR_sr⟩, fun p hp => by have := hp.2; omega⟩
  have hno_out_rS : ∀ p, ¬ adjS r p := fun p hp => by
    have := ((hadjS_iff r p).mp hp).1.2; omega
  have hno_out_sS : ∀ p, ¬ adjS s p := fun p hp => by
    have h1 := (hadjS_iff s p).mp hp
    exact h1.2 ⟨rfl, huniqR s p r h1.1 hadjR_sr⟩
  -- Every c ∈ rootsR.erase r is also in rootsS with identical comp and leaves!
  have hpath_imp : ∀ x y, Relation.ReflTransGen adjS x y → Relation.ReflTransGen adjR x y :=
    Relation.ReflTransGen.mono (fun x y h => ((hadjS_iff x y).mp h).1)
  have hother_eq : ∀ c ∈ rootsR.erase r,
      c ∈ rootsS ∧ compS c = compR c ∧ leavesS c = leavesR c := by
    intro c hc
    have hcr : c ≠ r := (Finset.mem_erase.mp hc).1
    have hcR : c ∈ rootsR := (Finset.mem_erase.mp hc).2
    have hdisj_cr : Disjoint (compR c) (compR r) := hdisjR c hcR r hr_rootR hcr
    have hs_in_r : s ∈ compR r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .single hadjR_sr⟩
    have hr_in_r : r ∈ compR r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
    have hnot_sr : ∀ w ∈ compR c, w ≠ s ∧ w ≠ r := fun w hw =>
      ⟨fun h => Finset.disjoint_left.mp hdisj_cr hw (h ▸ hs_in_r),
       fun h => Finset.disjoint_left.mp hdisj_cr hw (h ▸ hr_in_r)⟩
    have hcS : c ∈ rootsS := by
      obtain ⟨x, hxc⟩ := (Finset.mem_filter.mp hcR).2.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨x, (hadjS_iff x c).mpr ⟨hxc, fun h => hcr h.2⟩⟩,
        fun p hp => (Finset.mem_filter.mp hcR).2.2 p ((hadjS_iff c p).mp hp).1⟩
    have hcomp_eq : compS c = compR c := by
      ext w
      simp only [compS, compR, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hpath_imp w c, fun hp => ?_⟩
      induction hp using Relation.ReflTransGen.head_induction_on with
      | refl => exact .refl
      | @head a b hab hbc ih =>
        have ha_mem : a ∈ compR c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .head hab hbc⟩
        have ha_ne_s : a ≠ s := (hnot_sr a ha_mem).1
        exact .head ((hadjS_iff a b).mpr ⟨hab, fun h => ha_ne_s h.1⟩) ih
    have hleaves_eq : leavesS c = leavesR c := by
      ext w
      simp only [leavesS, leavesR, hcomp_eq, Finset.mem_filter]
      refine ⟨fun ⟨hw, hno⟩ => ⟨hw, fun x hxw => hno x ((hadjS_iff x w).mpr ⟨hxw, fun h => (hnot_sr w hw).2 h.2⟩)⟩,
        fun ⟨hw, hno⟩ => ⟨hw, fun x hxw => hno x ((hadjS_iff x w).mp hxw).1⟩⟩
    exact ⟨hcS, hcomp_eq, hleaves_eq⟩
  -- Every c ∈ rootsS belongs to rootsR.erase r ∪ ({r, s} ∩ rootsS)!
  have hrootsS_sub : rootsS ⊆ rootsR.erase r ∪ ({r, s} : Finset W).filter (fun c => c ∈ rootsS) := by
    intro c hcS
    by_cases hcr : c = r
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp [hcr], hcS⟩)
    · by_cases hcs : c = s
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp [hcs], hcS⟩)
      · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hcr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩)
        · obtain ⟨x, hxc⟩ := (Finset.mem_filter.mp hcS).2.1
          exact ⟨x, ((hadjS_iff x c).mp hxc).1⟩
        · intro p hp
          exact (Finset.mem_filter.mp hcS).2.2 p ((hadjS_iff c p).mpr ⟨hp, fun h => hcs h.1⟩)
  have hrootsS_eq : rootsS = rootsR.erase r ∪ ({r, s} : Finset W).filter (fun c => c ∈ rootsS) := by
    refine Finset.Subset.antisymm hrootsS_sub (Finset.union_subset ?_ (fun c hc => (Finset.mem_filter.mp hc).2))
    intro c hc; exact (hother_eq c hc).1
  have hdisj_rs : Disjoint (rootsR.erase r) (({r, s} : Finset W).filter (fun c => c ∈ rootsS)) := by
    refine Finset.disjoint_left.mpr (fun c hc1 hc2 => ?_)
    have hcr : c ≠ r := (Finset.mem_erase.mp hc1).1
    have hmem := (Finset.mem_filter.mp hc2).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hcr rfl
    · exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc1).2).2.2 r hadjR_sr
  -- Compare compS r, compS s inside compR r, and leavesS r, leavesS s inside leavesR r!
  have hAr_sub : compS r ⊆ compR r := fun w hw =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpath_imp w r (Finset.mem_filter.mp hw).2⟩
  have hAs_sub : compS s ⊆ compR r := fun w hw =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpath_imp w s (Finset.mem_filter.mp hw).2).tail hadjR_sr⟩
  have hdisj_ArAs : Disjoint (compS r) (compS s) := by
    refine Finset.disjoint_left.mpr (fun w hwr hws => ?_)
    obtain ⟨c0, _, hc0u⟩ := htopS w
    exact hsr_ne.symm ((hc0u r ⟨(Finset.mem_filter.mp hwr).2, hno_out_rS⟩).trans
      (hc0u s ⟨(Finset.mem_filter.mp hws).2, hno_out_sS⟩).symm)
  have hr_in_Ar : r ∈ compS r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  have hs_in_As : s ∈ compS s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  have hcard_ArAs : (compS r).card + (compS s).card ≤ (compR r).card := by
    rw [← Finset.card_union_of_disjoint hdisj_ArAs]
    exact Finset.card_le_card (Finset.union_subset hAr_sub hAs_sub)
  have hAr_pos : 1 ≤ (compS r).card := Finset.one_le_card.mpr ⟨r, hr_in_Ar⟩
  have hAs_pos : 1 ≤ (compS s).card := Finset.one_le_card.mpr ⟨s, hs_in_As⟩
  have hLr_sub : r ∈ rootsS → leavesS r ⊆ leavesR r := by
    intro hrS w hw
    have hw' := Finset.mem_filter.mp hw
    have hwr : w ≠ r := by
      rintro rfl; obtain ⟨x, hxr⟩ := (Finset.mem_filter.mp hrS).2.1; exact hw'.2 x hxr
    exact Finset.mem_filter.mpr ⟨hAr_sub hw'.1, fun x hxw => hw'.2 x ((hadjS_iff x w).mpr ⟨hxw, fun h => hwr h.2⟩)⟩
  have hLs_sub : leavesS s ⊆ leavesR r := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    have hwr : w ≠ r := fun h => Finset.disjoint_left.mp hdisj_ArAs hr_in_Ar (h ▸ hw'.1)
    exact Finset.mem_filter.mpr ⟨hAs_sub hw'.1, fun x hxw => hw'.2 x ((hadjS_iff x w).mpr ⟨hxw, fun h => hwr h.2⟩)⟩
  have hdisj_LrLs : Disjoint (leavesS r) (leavesS s) :=
    hdisj_ArAs.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hA_ge2 : 2 ≤ (compR r).card := by omega
  have hL_ge1 : 1 ≤ (leavesR r).card := by
    obtain ⟨wmax, hwmax, hmax⟩ := Finset.exists_max_image (compR r) (T.dist r) ⟨r, hAr_sub hr_in_Ar⟩
    refine Finset.one_le_card.mpr ⟨wmax, Finset.mem_filter.mpr ⟨hwmax, fun y hy => ?_⟩⟩
    have hym : y ∈ compR r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .head hy (Finset.mem_filter.mp hwmax).2⟩
    have := hmax y hym; have := hy.2; omega
  -- Rewrite gammaAt s and gammaAt r!
  have hgammaR : gammaAt r = (∑ c ∈ rootsR.erase r, ((compR c).card + (leavesR c).card - 2)) +
      ((compR r).card + (leavesR r).card - 2) := by
    change (∑ c ∈ rootsR, ((compR c).card + (leavesR c).card - 2)) = _
    rw [← Finset.sum_erase_add _ _ hr_rootR]
  have hgammaS : gammaAt s = (∑ c ∈ rootsR.erase r, ((compR c).card + (leavesR c).card - 2)) +
      ∑ c ∈ ({r, s} : Finset W).filter (fun c => c ∈ rootsS), ((compS c).card + (leavesS c).card - 2) := by
    change (∑ c ∈ rootsS, ((compS c).card + (leavesS c).card - 2)) = _
    conv_lhs => rw [hrootsS_eq]
    rw [Finset.sum_union hdisj_rs]
    congr 1
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have ⟨_, h1, h2⟩ := hother_eq c hc; rw [h1, h2]
  have htail_lt : (∑ c ∈ ({r, s} : Finset W).filter (fun c => c ∈ rootsS), ((compS c).card + (leavesS c).card - 2)) <
      (compR r).card + (leavesR r).card - 2 := by
    by_cases hrS : r ∈ rootsS <;> by_cases hsS : s ∈ rootsS
    · have hfilt : ({r, s} : Finset W).filter (fun c => c ∈ rootsS) = {r, s} := by
        ext c; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl <;> assumption⟩⟩
      rw [hfilt, Finset.sum_pair hsr_ne.symm]
      have hLsum : (leavesS r).card + (leavesS s).card ≤ (leavesR r).card := by
        rw [← Finset.card_union_of_disjoint hdisj_LrLs]
        exact Finset.card_le_card (Finset.union_subset (hLr_sub hrS) hLs_sub)
      have hAr_ge2 : 2 ≤ (compS r).card := by
        obtain ⟨x, hxr⟩ := (Finset.mem_filter.mp hrS).2.1
        have hxr_ne : x ≠ r := fun h => by subst h; exact lt_irrefl _ hxr.2
        have hx_mem : x ∈ compS r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .single hxr⟩
        have hsub : ({x, r} : Finset W) ⊆ compS r := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        have := Finset.card_le_card hsub; rw [Finset.card_pair hxr_ne] at this; exact this
      have hAs_ge2 : 2 ≤ (compS s).card := by
        obtain ⟨x, hxs⟩ := (Finset.mem_filter.mp hsS).2.1
        have hxs_ne : x ≠ s := fun h => by subst h; exact lt_irrefl _ hxs.2
        have hx_mem : x ∈ compS s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .single hxs⟩
        have hsub : ({x, s} : Finset W) ⊆ compS s := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        have := Finset.card_le_card hsub; rw [Finset.card_pair hxs_ne] at this; exact this
      omega
    · have hfilt : ({r, s} : Finset W).filter (fun c => c ∈ rootsS) = {r} := by
        ext c; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_right (fun h => hsS (h ▸ h2)), fun h => ⟨Or.inl h, h ▸ hrS⟩⟩
      rw [hfilt, Finset.sum_singleton]
      have hLle := Finset.card_le_card (hLr_sub hrS)
      omega
    · have hfilt : ({r, s} : Finset W).filter (fun c => c ∈ rootsS) = {s} := by
        ext c; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left (fun h => hrS (h ▸ h2)), fun h => ⟨Or.inr h, h ▸ hsS⟩⟩
      rw [hfilt, Finset.sum_singleton]
      have hLle := Finset.card_le_card hLs_sub
      omega
    · have hfilt : ({r, s} : Finset W).filter (fun c => c ∈ rootsS) = ∅ := by
        ext c; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl | rfl, h2⟩ <;> contradiction
      rw [hfilt, Finset.sum_empty]; omega
  omega

-- Shared wrapper: if ANY root r1 achieves gammaD r1 <= g or gammaU r1 <= g,
-- and n + k + g <= Fintype.card V + 1, then D embeds in G!
lemma dross_havet_embed_of_exists_gamma_le {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hG : G.IsTournament) (g : ℕ)
    (hm : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card + g ≤
      Fintype.card V + 1)
    (hex : ∃ r1 : W,
      (∑ c ∈ Finset.univ.filter (fun c : W =>
          (∃ x : W, D.Adj x c ∧ T.dist r1 c < T.dist r1 x) ∧
          (∀ p : W, ¬ (D.Adj c p ∧ T.dist r1 p < T.dist r1 c))),
        ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r1 y < T.dist r1 x) w c)).card +
         ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r1 y < T.dist r1 x) w c)).filter
           (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r1 w < T.dist r1 x))).card - 2)) ≤ g ∨
      (∑ c ∈ Finset.univ.filter (fun c : W =>
          (∃ x : W, D.Adj c x ∧ T.dist r1 c < T.dist r1 x) ∧
          (∀ p : W, ¬ (D.Adj p c ∧ T.dist r1 p < T.dist r1 c))),
        ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c)).card +
         ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c)).filter
           (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r1 w < T.dist r1 x))).card - 2)) ≤ g) :
    Embeds D G := by
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  have hOrev : Drev.IsOrientation T :=
    ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
  let gammaD : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (D.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  let gammaU : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, Drev.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (Drev.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (Drev.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  have hW_ne : (Finset.univ : Finset W).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ, hW]; omega)
  obtain ⟨r0, _, hr0_min⟩ := Finset.exists_min_image Finset.univ (fun r => min (gammaD r) (gammaU r)) hW_ne
  obtain ⟨r1, hr1⟩ := hex
  have hmin_le : min (gammaD r0) (gammaU r0) ≤ g := by
    have h1 := hr0_min r1 (Finset.mem_univ r1)
    rcases hr1 with hD | hU
    · exact le_trans h1 (le_trans (min_le_left _ _) hD)
    · have hU_eq : gammaU r1 = (∑ c ∈ Finset.univ.filter (fun c : W =>
            (∃ x : W, D.Adj c x ∧ T.dist r1 c < T.dist r1 x) ∧
            (∀ p : W, ¬ (D.Adj p c ∧ T.dist r1 p < T.dist r1 c))),
          ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c)).card +
           ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c)).filter
             (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r1 w < T.dist r1 x))).card - 2)) := by
        refine Finset.sum_congr (by ext c; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]) (fun c _ => ?_)
        congr 1
      exact le_trans h1 (le_trans (min_le_right _ _) (hU_eq ▸ hU))
  let k := (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  have hcontra : ∀ a b c : ℕ, a < b → b ≤ c → c ≤ a → False := by intros; omega
  by_cases hle : gammaD r0 ≤ gammaU r0
  · have hr0_src : ∀ x : W, ¬ D.Adj x r0 := by
      intro x hxr
      have hlt : gammaD x < gammaD r0 := dross_havet_gamma_lt_of_in_neighbor D hT hO hxr
      have hmin : min (gammaD r0) (gammaU r0) ≤ min (gammaD x) (gammaU x) := hr0_min x (Finset.mem_univ x)
      rw [min_eq_left hle] at hmin
      exact hcontra _ _ _ hlt hmin (min_le_left _ _)
    have hgr0 : gammaD r0 ≤ g := (min_eq_left hle) ▸ hmin_le
    exact dross_havet_rooted_source hn D hW hT hO r0 hr0_src G hG
      (le_trans (Nat.add_le_add_left hgr0 (n + k)) hm)
  · have hlt_rev : gammaU r0 ≤ gammaD r0 := Nat.le_of_not_ge hle
    have hr0_src : ∀ x : W, ¬ Drev.Adj x r0 := by
      intro x hxr
      have hlt : gammaU x < gammaU r0 := dross_havet_gamma_lt_of_in_neighbor Drev hT hOrev hxr
      have hmin : min (gammaD r0) (gammaU r0) ≤ min (gammaD x) (gammaU x) := hr0_min x (Finset.mem_univ x)
      rw [min_eq_right hlt_rev] at hmin
      exact hcontra _ _ _ hlt hmin (min_le_right _ _)
    let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
    have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun u v huv => hG.2 v u huv.symm⟩
    have hleaves_eq : (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)).card = 1)).card = k := by
      congr 1; ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)) =
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)) := by
        ext z; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]; exact or_comm
      rw [this]
    have hgr0 : gammaU r0 ≤ g := (min_eq_right hlt_rev) ▸ hmin_le
    have hm_rev : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)).card = 1)).card + gammaU r0 ≤
        Fintype.card V + 1 := by
      rw [hleaves_eq]; exact le_trans (Nat.add_le_add_left hgr0 (n + k)) hm
    obtain ⟨⟨fn, hfn⟩, hfinj⟩ := dross_havet_rooted_source hn Drev hW hT hOrev r0 hr0_src Grev hGrev hm_rev
    exact ⟨⟨fn, fun hxy => hfn hxy⟩, hfinj⟩

-- Sharpened Dross-Havet (2021) Theorem 4 (1 full vertex stronger for ALL n, k!):
-- Every oriented tree on n >= 2 vertices with k leaves embeds in every tournament on
-- m >= n + k - 1 + (n + k - 4) / 2 vertices!
theorem embeds_dross_havet_three_halves {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hG : G.IsTournament)
    (hm : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card - 1 +
      (n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card - 4) / 2 ≤
      Fintype.card V) :
    Embeds D G := by
  obtain ⟨T, hT, hO⟩ := hTree
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  have hOrev : Drev.IsOrientation T :=
    ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
  have hW_ne : (Finset.univ : Finset W).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ, hW]; omega)
  have ⟨v0, _⟩ := hW_ne
  obtain ⟨r1, _, hr1_max⟩ := Finset.exists_max_image Finset.univ (T.dist v0) hW_ne
  have hr1_ne_v0 : r1 ≠ v0 := by
    intro hEq
    obtain ⟨u1, u2, hu12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
    have hex : ∃ u : W, u ≠ v0 := by
      by_cases h1 : u1 = v0; exact ⟨u2, fun h => hu12 (h1.trans h.symm)⟩; exact ⟨u1, h1⟩
    obtain ⟨u, huv⟩ := hex
    have hle := hr1_max u (Finset.mem_univ u)
    rw [hEq, SimpleGraph.dist_self] at hle
    have h0 : T.dist v0 u = 0 := by omega
    exact huv ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
      (not_not.mpr (hT.connected v0 u))).symm
  obtain ⟨s, ⟨hTsr1, _⟩, hpu⟩ := tree_exists_unique_parent hT v0 r1 hr1_ne_v0
  have hr1_leaf : (Finset.univ.filter (fun z : W => D.Adj r1 z ∨ D.Adj z r1)).card = 1 := by
    have hfilt_eq : Finset.univ.filter (fun z : W => D.Adj r1 z ∨ D.Adj z r1) = {s} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hz
        have hTr1z : T.Adj r1 z := by
          rcases hz with h1 | h2; exact hO.1 r1 z h1; exact (hO.1 z r1 h2).symm
        have hle := hr1_max z (Finset.mem_univ z)
        rcases hT.dist_eq_dist_add_one_of_adj v0 hTr1z with h1 | h2
        · exact hpu z ⟨hTr1z.symm, by omega⟩
        · omega
      · rintro rfl; exact adj_or_rev_of_isOrientation hO hTsr1.symm
    rw [hfilt_eq, Finset.card_singleton]
  let k := (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  have hk_ge1 : 1 ≤ k := Finset.one_le_card.mpr ⟨r1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1_leaf⟩⟩
  let gD : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (D.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  let gU : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj c x ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (D.Adj p c ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  have hsum_r1 : gD r1 + gU r1 ≤ n + k - 3 :=
    dross_havet_gamma_sum_le_of_leaf_or_mixed hn D hW hT hO r1 (Or.inl hr1_leaf)
  have hex_g : ∃ r0 : W, gD r0 ≤ (n + k - 4) / 2 ∨ gU r0 ≤ (n + k - 4) / 2 := by
    by_cases hlt1 : gD r1 < gU r1
    · exact ⟨r1, Or.inl ((by intros; omega : ∀ a b : ℕ, a < b → a + b ≤ n + k - 3 → a ≤ (n + k - 4) / 2) _ _ hlt1 hsum_r1)⟩
    · by_cases hlt2 : gU r1 < gD r1
      · exact ⟨r1, Or.inr ((by intros; omega : ∀ a b : ℕ, b < a → a + b ≤ n + k - 3 → b ≤ (n + k - 4) / 2) _ _ hlt2 hsum_r1)⟩
      · have heq : gD r1 = gU r1 := (by intros; omega : ∀ a b : ℕ, ¬ a < b → ¬ b < a → a = b) _ _ hlt1 hlt2
        rcases adj_or_rev_of_isOrientation hO hTsr1 with hDsr1 | hDr1s
        · have hlt_s : gD s < gD r1 := dross_havet_gamma_lt_of_in_neighbor D hT hO hDsr1
          exact ⟨s, Or.inl ((by intros; omega : ∀ a b c : ℕ, a < b → b = c → b + c ≤ n + k - 3 → a ≤ (n + k - 4) / 2) _ _ _ hlt_s heq hsum_r1)⟩
        · have hlt_s_raw := dross_havet_gamma_lt_of_in_neighbor Drev hT hOrev hDr1s
          have hgU_eq : ∀ r0 : W, gU r0 =
              (∑ c ∈ Finset.univ.filter (fun c : W =>
                  (∃ x : W, Drev.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
                  (∀ p : W, ¬ (Drev.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
                ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
                 ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
                   (fun w => ∀ x : W, ¬ (Drev.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)) := by
            intro r0
            refine Finset.sum_congr (by ext c; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]) (fun c _ => ?_)
            congr 1
          have hlt_s : gU s < gU r1 := by rw [hgU_eq s, hgU_eq r1]; exact hlt_s_raw
          exact ⟨s, Or.inr ((by intros; omega : ∀ a b c : ℕ, a < c → b = c → b + c ≤ n + k - 3 → a ≤ (n + k - 4) / 2) _ _ _ hlt_s heq hsum_r1)⟩
  have hm' : n + k + (n + k - 4) / 2 ≤ Fintype.card V + 1 :=
    (by intros; omega : ∀ m : ℕ, 2 ≤ n → 1 ≤ k → n + k - 1 + (n + k - 4) / 2 ≤ m → n + k + (n + k - 4) / 2 ≤ m + 1)
      _ hn hk_ge1 hm
  exact dross_havet_embed_of_exists_gamma_le hn D hW hT hO G hG ((n + k - 4) / 2) hm' hex_g

-- Sharpened Dross-Havet Corollary 5: Every oriented tree on n >= 2 vertices with 3k <= n + 3
-- embeds in every tournament on 2n - 2 vertices!
-- (Subsumes ALL k = 2 paths for n >= 3, ALL k = 3 trees for n >= 6 [Ceroi-Havet 2004],
--  ALL k = 4 trees for n >= 9, and ALL 3k <= n [Dross-Havet 2021]!)
theorem embeds_dross_havet_3k_le_n_add_3 {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hk : 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n + 3) :
    Embeds D G :=
  embeds_dross_havet_three_halves hn D hW hTree G hG (by omega)

-- Dross-Havet (2021) Corollary 5 (original 3k <= n bound) as an immediate corollary:
theorem embeds_dross_havet_3k_le_n {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hk : 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n) :
    Embeds D G :=
  embeds_dross_havet_3k_le_n_add_3 hn D hW hTree G hV hG (by omega)

-- Non-antidirected sharpening: if D contains ANY directed 2-path s -> v -> t, then
-- min(gammaD s, gammaU t) <= (n + k - 5) / 2, embedding D whenever 3k <= n + 4!
theorem embeds_dross_havet_non_antidirected {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    (hNotAnti : ∃ v s t : W, D.Adj s v ∧ D.Adj v t)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hG : G.IsTournament)
    (hm : n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card - 1 +
      (n + (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card - 5) / 2 ≤
      Fintype.card V) :
    Embeds D G := by
  obtain ⟨T, hT, hO⟩ := hTree
  obtain ⟨v, s, t, hsv, hvt⟩ := hNotAnti
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  have hOrev : Drev.IsOrientation T :=
    ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
  let k := (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  let gD : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (D.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  let gU : W → ℕ := fun r0 =>
    ∑ c ∈ Finset.univ.filter (fun c : W =>
        (∃ x : W, D.Adj c x ∧ T.dist r0 c < T.dist r0 x) ∧
        (∀ p : W, ¬ (D.Adj p c ∧ T.dist r0 p < T.dist r0 c))),
      ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r0 y < T.dist r0 x) w c)).card +
       ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D.Adj y x ∧ T.dist r0 y < T.dist r0 x) w c)).filter
         (fun w => ∀ x : W, ¬ (D.Adj w x ∧ T.dist r0 w < T.dist r0 x))).card - 2)
  have hsum_v : gD v + gU v ≤ n + k - 3 :=
    dross_havet_gamma_sum_le_of_leaf_or_mixed hn D hW hT hO v (Or.inr ⟨⟨s, hsv⟩, ⟨t, hvt⟩⟩)
  have hlt_s : gD s < gD v := dross_havet_gamma_lt_of_in_neighbor D hT hO hsv
  have hlt_t_raw := dross_havet_gamma_lt_of_in_neighbor Drev hT hOrev hvt
  have hgU_eq : ∀ r0 : W, gU r0 =
      (∑ c ∈ Finset.univ.filter (fun c : W =>
          (∃ x : W, Drev.Adj x c ∧ T.dist r0 c < T.dist r0 x) ∧
          (∀ p : W, ¬ (Drev.Adj c p ∧ T.dist r0 p < T.dist r0 c))),
        ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).card +
         ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => Drev.Adj x y ∧ T.dist r0 y < T.dist r0 x) w c)).filter
           (fun w => ∀ x : W, ¬ (Drev.Adj x w ∧ T.dist r0 w < T.dist r0 x))).card - 2)) := by
    intro r0
    refine Finset.sum_congr (by ext c; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]) (fun c _ => ?_)
    congr 1
  have hlt_t : gU t < gU v := by rw [hgU_eq t, hgU_eq v]; exact hlt_t_raw
  have hex_g : ∃ r0 : W, gD r0 ≤ (n + k - 5) / 2 ∨ gU r0 ≤ (n + k - 5) / 2 := by
    by_cases hst : gD s ≤ gU t
    · exact ⟨s, Or.inl ((by intros; omega : ∀ a b c d : ℕ, a < c → b < d → c + d ≤ n + k - 3 → a ≤ b → a ≤ (n + k - 5) / 2) _ _ _ _ hlt_s hlt_t hsum_v hst)⟩
    · exact ⟨t, Or.inr ((by intros; omega : ∀ a b c d : ℕ, a < c → b < d → c + d ≤ n + k - 3 → ¬ a ≤ b → b ≤ (n + k - 5) / 2) _ _ _ _ hlt_s hlt_t hsum_v hst)⟩
  -- Since n >= 2, at least 1 leaf exists so k >= 1!
  have hW_ne : (Finset.univ : Finset W).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ, hW]; omega)
  have ⟨v0, _⟩ := hW_ne
  obtain ⟨r1, _, hr1_max⟩ := Finset.exists_max_image Finset.univ (T.dist v0) hW_ne
  have hr1_ne_v0 : r1 ≠ v0 := by
    intro hEq
    obtain ⟨u1, u2, hu12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
    have hex : ∃ u : W, u ≠ v0 := by
      by_cases h1 : u1 = v0; exact ⟨u2, fun h => hu12 (h1.trans h.symm)⟩; exact ⟨u1, h1⟩
    obtain ⟨u, huv⟩ := hex
    have hle := hr1_max u (Finset.mem_univ u)
    rw [hEq, SimpleGraph.dist_self] at hle
    have h0 : T.dist v0 u = 0 := by omega
    exact huv ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
      (not_not.mpr (hT.connected v0 u))).symm
  obtain ⟨p1, ⟨hTp1, _⟩, hp1u⟩ := tree_exists_unique_parent hT v0 r1 hr1_ne_v0
  have hr1_leaf : (Finset.univ.filter (fun z : W => D.Adj r1 z ∨ D.Adj z r1)).card = 1 := by
    have hfilt_eq : Finset.univ.filter (fun z : W => D.Adj r1 z ∨ D.Adj z r1) = {p1} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hz
        have hTr1z : T.Adj r1 z := by rcases hz with h1 | h2; exact hO.1 r1 z h1; exact (hO.1 z r1 h2).symm
        have hle := hr1_max z (Finset.mem_univ z)
        rcases hT.dist_eq_dist_add_one_of_adj v0 hTr1z with h1 | h2
        · exact hp1u z ⟨hTr1z.symm, by omega⟩
        · omega
      · rintro rfl; exact adj_or_rev_of_isOrientation hO hTp1.symm
    rw [hfilt_eq, Finset.card_singleton]
  have hk_ge1 : 1 ≤ k := Finset.one_le_card.mpr ⟨r1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1_leaf⟩⟩
  have hm' : n + k + (n + k - 5) / 2 ≤ Fintype.card V + 1 :=
    (by intros; omega : ∀ m : ℕ, 2 ≤ n → 1 ≤ k → n + k - 1 + (n + k - 5) / 2 ≤ m → n + k + (n + k - 5) / 2 ≤ m + 1)
      _ hn hk_ge1 hm
  exact dross_havet_embed_of_exists_gamma_le hn D hW hT hO G hG ((n + k - 5) / 2) hm' hex_g

-- ============================================================================
-- Stage 3: Antidirected P_4-internal trees + Complete proof of R1.H1!
-- ============================================================================

-- In any no-source/no-sink tournament G on 2n - 2 vertices (n >= 3),
-- partitioning V = V+ ⊔ V- by d^+(v) >= n - 1 vs d^-(v) >= n - 1 yields a cross P_4:
-- v1, v2 ∈ V+ (v1 != v2) and w1, w2 ∈ V- (w1 != w2) with v1 -> w1 <- v2 -> w2!
lemma tournament_exists_cross_P4 {n : ℕ} (hn : 3 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≤ 2 * n - 4)
    (hNoSnk : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card ≤ 2 * n - 4) :
    let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
    let Vm := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card)
    ∃ v1 v2 w1 w2 : V, v1 ∈ Vp ∧ v2 ∈ Vp ∧ w1 ∈ Vm ∧ w2 ∈ Vm ∧
      v1 ≠ v2 ∧ w1 ≠ w2 ∧ G.Adj v1 w1 ∧ G.Adj v2 w1 ∧ G.Adj v2 w2 := by
  intro Vp Vm
  -- Out-degree + in-degree = 2n - 3 for every v : V!
  have hdeg_sum : ∀ v : V,
      (Finset.univ.filter (fun u : V => G.Adj v u)).card +
      (Finset.univ.filter (fun u : V => G.Adj u v)).card = 2 * n - 3 := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
        (Finset.univ.filter (fun u : V => G.Adj u v)) := by
      refine Finset.disjoint_left.mpr (fun u h1 h2 => ?_)
      have hvu := (Finset.mem_filter.mp h1).2
      have huv := (Finset.mem_filter.mp h2).2
      have hne : v ≠ u := fun h => hG.1 v (h ▸ hvu)
      exact ((hG.2 v u hne).mp hvu) huv
    have hunion : Finset.univ.filter (fun u : V => G.Adj v u) ∪
        Finset.univ.filter (fun u : V => G.Adj u v) = Finset.univ.erase v := by
      ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro h; rcases h with h1 | h2
        · exact fun heq => hG.1 u (heq ▸ h1)
        · exact fun heq => hG.1 u (heq ▸ h2)
      · intro hne
        by_cases h : G.Adj v u
        · exact Or.inl h
        · exact Or.inr ((hG.2 u v hne).mpr h)
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
    omega
  have hdisj_pm : Disjoint Vp Vm := by
    refine Finset.disjoint_left.mpr (fun v h1 h2 => ?_)
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    have := hdeg_sum v; omega
  have hunion_pm : Vp ∪ Vm = Finset.univ := by
    ext v; simp only [Vp, Vm, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have := hdeg_sum v; omega
  have hcard_pm : Vp.card + Vm.card = 2 * n - 2 := by
    rw [← Finset.card_union_of_disjoint hdisj_pm, hunion_pm, Finset.card_univ, hV]
  -- Handshake identity in any subtournament S: 2 * sum_{v in S} d_S^+(v) = |S| * (|S| - 1)!
  have hsub_arcs : ∀ S : Finset V,
      2 * (∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card) = S.card * (S.card - 1) := by
    intro S
    have hsum_eq : (∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card) +
        (∑ v ∈ S, (S.filter (fun u => G.Adj u v)).card) = S.card * (S.card - 1) := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ v ∈ S, (S.filter (fun u => G.Adj v u)).card + (S.filter (fun u => G.Adj u v)).card = S.card - 1 := by
        intro v hv
        have hd : Disjoint (S.filter (fun u => G.Adj v u)) (S.filter (fun u => G.Adj u v)) := by
          refine Finset.disjoint_left.mpr (fun u h1 h2 => ?_)
          have hvu := (Finset.mem_filter.mp h1).2
          have huv := (Finset.mem_filter.mp h2).2
          exact ((hG.2 v u (fun h => hG.1 v (h ▸ hvu))).mp hvu) huv
        have hu : S.filter (fun u => G.Adj v u) ∪ S.filter (fun u => G.Adj u v) = S.erase v := by
          ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro (⟨huS, h1⟩ | ⟨huS, h2⟩)
            · exact ⟨fun heq => hG.1 u (heq ▸ h1), huS⟩
            · exact ⟨fun heq => hG.1 u (heq ▸ h2), huS⟩
          · rintro ⟨hne, huS⟩
            by_cases h : G.Adj v u
            · exact Or.inl ⟨huS, h⟩
            · exact Or.inr ⟨huS, (hG.2 u v hne).mpr h⟩
        rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_erase_of_mem hv]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
    have hswap : (∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card) =
        (∑ v ∈ S, (S.filter (fun u => G.Adj u v)).card) := by
      have h1 : ∀ f : V → V → Prop, [DecidableRel f] →
          (∑ v ∈ S, (S.filter (fun u => f v u)).card) = ((S ×ˢ S).filter (fun p => f p.1 p.2)).card := by
        intro f _
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.card_filter]
      rw [h1 G.Adj, h1 (fun v u => G.Adj u v)]
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hmem := Finset.mem_product.mp hp'.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, hp'.2⟩
      · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hmem := Finset.mem_product.mp hp'.1
        exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, hp'.2⟩, rfl⟩
    omega
  -- Prove 2 <= Vp.card and 2 <= Vm.card using hNoSrc and hNoSnk!
  set m := n - 2 with hm_def
  have hn_eq : n = m + 2 := by omega
  have hVp_ge2 : 2 ≤ Vp.card := by
    by_contra hlt
    have hVp_le1 : Vp.card ≤ 1 := by omega
    have htot := hsub_arcs Finset.univ
    rw [Finset.card_univ, hV] at htot
    have hsplit : (∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card) =
        (∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card) +
        (∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj v u)).card) := by
      rw [← Finset.sum_union hdisj_pm, hunion_pm]
    have h1 : (∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card) ≤ Vp.card * (2 * m) := by
      calc _ ≤ ∑ _v ∈ Vp, (2 * m) := Finset.sum_le_sum (fun v _ => by have := hNoSrc v; omega)
        _ = Vp.card * (2 * m) := by simp
    have h2 : (∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj v u)).card) ≤ Vm.card * m := by
      calc _ ≤ ∑ _v ∈ Vm, m := Finset.sum_le_sum (fun v hv => by
            have := (Finset.mem_filter.mp hv).2; have := hdeg_sum v; omega)
        _ = Vm.card * m := by simp
    have htot' : (2 * m + 2) * (2 * m + 1) ≤ 2 * (Vp.card * (2 * m) + Vm.card * m) := by
      have hsub1 : (2 * n - 2) * (2 * n - 2 - 1) = (2 * m + 2) * (2 * m + 1) := by
        congr 1 <;> omega
      rw [hsub1] at htot; omega
    have hpm' : Vp.card + Vm.card = 2 * m + 2 := by omega
    nlinarith
  have hVm_ge2 : 2 ≤ Vm.card := by
    by_contra hlt
    have hVm_le1 : Vm.card ≤ 1 := by omega
    have htot := hsub_arcs Finset.univ
    rw [Finset.card_univ, hV] at htot
    -- Total in-degrees = total out-degrees!
    have hswap_univ : (∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card) =
        (∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card) := by
      have h1 : ∀ f : V → V → Prop, [DecidableRel f] →
          (∑ v : V, (Finset.univ.filter (fun u => f v u)).card) = ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => f p.1 p.2)).card := by
        intro f _
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
      rw [h1 (fun v u => G.Adj u v), h1 G.Adj]
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
      · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp; exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
    have hsplit : (∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card) =
        (∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card) +
        (∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj u v)).card) := by
      rw [← Finset.sum_union hdisj_pm.symm, Finset.union_comm, hunion_pm]
    have h1 : (∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card) ≤ Vm.card * (2 * m) := by
      calc _ ≤ ∑ _v ∈ Vm, (2 * m) := Finset.sum_le_sum (fun v _ => by have := hNoSnk v; omega)
        _ = Vm.card * (2 * m) := by simp
    have h2 : (∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj u v)).card) ≤ Vp.card * m := by
      calc _ ≤ ∑ _v ∈ Vp, m := Finset.sum_le_sum (fun v hv => by
            have := (Finset.mem_filter.mp hv).2; have := hdeg_sum v; omega)
        _ = Vp.card * m := by simp
    have htot' : (2 * m + 2) * (2 * m + 1) ≤ 2 * (Vm.card * (2 * m) + Vp.card * m) := by
      have hsub1 : (2 * n - 2) * (2 * n - 2 - 1) = (2 * m + 2) * (2 * m + 1) := by
        congr 1 <;> omega
      rw [hsub1] at htot; omega
    have hpm' : Vp.card + Vm.card = 2 * m + 2 := by omega
    nlinarith
  -- Count cross arcs E = {(v, w) ∈ Vp × Vm : G.Adj v w}! Prove E.card >= 2n - 3!
  let E := (Vp ×ˢ Vm).filter (fun p : V × V => G.Adj p.1 p.2)
  have hE_ge : 2 * n - 3 ≤ E.card := by
    have hE_sum : E.card = ∑ v ∈ Vp, (Vm.filter (fun w => G.Adj v w)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
    have hout_split : ∀ v ∈ Vp,
        (Finset.univ.filter (fun u : V => G.Adj v u)).card =
        (Vp.filter (fun u => G.Adj v u)).card + (Vm.filter (fun u => G.Adj v u)).card := by
      intro v _
      rw [← Finset.card_union_of_disjoint (hdisj_pm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ← Finset.filter_union, hunion_pm]
    have hsum_ge : Vp.card * (m + 1) ≤ (∑ v ∈ Vp, (Vp.filter (fun u => G.Adj v u)).card) + E.card := by
      rw [hE_sum, ← Finset.sum_add_distrib]
      calc Vp.card * (m + 1) = ∑ _v ∈ Vp, (m + 1) := by simp
        _ ≤ ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card :=
            Finset.sum_le_sum (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
        _ = ∑ v ∈ Vp, ((Vp.filter (fun u => G.Adj v u)).card + (Vm.filter (fun u => G.Adj v u)).card) :=
            Finset.sum_congr rfl hout_split
    have hVp_arcs := hsub_arcs Vp
    set p0 := Vp.card - 1 with hp0_def
    have hVp_eq : Vp.card = p0 + 1 := by omega
    have h2E : 2 * ((p0 + 1) * (m + 1)) ≤ (p0 + 1) * p0 + 2 * E.card := by
      have h1 : Vp.card * (m + 1) = (p0 + 1) * (m + 1) := by rw [hVp_eq]
      have h2 : Vp.card * (Vp.card - 1) = (p0 + 1) * p0 := by rw [← hp0_def, hVp_eq]
      rw [h1] at hsum_ge
      rw [h2] at hVp_arcs
      omega
    have hp0_ge : 1 ≤ p0 := by omega
    have hp0_le : p0 + 1 ≤ 2 * m := by omega
    have hgoal : 2 * m + 1 ≤ E.card := by nlinarith
    omega
  -- Bipartite P_4 lemma: if no cross edge (v, w) has BOTH deg_E(v) >= 2 and deg_E(w) >= 2, then E.card <= 2n - 4!
  by_contra hnoP4
  have hno_both : ∀ p ∈ E, (Vm.filter (fun w => G.Adj p.1 w)).card ≤ 1 ∨
      (Vp.filter (fun v => G.Adj v p.2)).card ≤ 1 := by
    intro p hp
    by_contra h
    push Not at h
    have hp' := Finset.mem_filter.mp hp
    have hv1 : p.1 ∈ Vp := (Finset.mem_product.mp hp'.1).1
    have hw1 : p.2 ∈ Vm := (Finset.mem_product.mp hp'.1).2
    have hadj : G.Adj p.1 p.2 := hp'.2
    have hex_w2 : ((Vm.filter (fun w => G.Adj p.1 w)).erase p.2).Nonempty := by
      refine Finset.card_pos.mp ?_
      have hmem : p.2 ∈ Vm.filter (fun w => G.Adj p.1 w) := Finset.mem_filter.mpr ⟨hw1, hadj⟩
      rw [Finset.card_erase_of_mem hmem]; have := h.1; omega
    have hex_v2 : ((Vp.filter (fun v => G.Adj v p.2)).erase p.1).Nonempty := by
      refine Finset.card_pos.mp ?_
      have hmem : p.1 ∈ Vp.filter (fun v => G.Adj v p.2) := Finset.mem_filter.mpr ⟨hv1, hadj⟩
      rw [Finset.card_erase_of_mem hmem]; have := h.2; omega
    obtain ⟨w2, hw2⟩ := hex_w2
    obtain ⟨v2, hv2⟩ := hex_v2
    have hw2_ne : w2 ≠ p.2 := (Finset.mem_erase.mp hw2).1
    have hw2_f := Finset.mem_filter.mp (Finset.mem_erase.mp hw2).2
    have hv2_ne : v2 ≠ p.1 := (Finset.mem_erase.mp hv2).1
    have hv2_f := Finset.mem_filter.mp (Finset.mem_erase.mp hv2).2
    -- Wait: v2 -> p.2 <- p.1 -> w2 gives (v1 := v2, v2 := p.1, w1 := p.2, w2 := w2)!
    exact hnoP4 ⟨v2, p.1, p.2, w2, hv2_f.1, hv1, hw1, hw2_f.1, hv2_ne, hw2_ne.symm, hv2_f.2, hadj, hw2_f.2⟩
  -- Split E into E1 (deg_E(v) = 1) and E2 (deg_E(v) >= 2, hence deg_E(w) = 1)!
  let E1 := E.filter (fun p => (Vm.filter (fun w => G.Adj p.1 w)).card ≤ 1)
  let E2 := E.filter (fun p => 2 ≤ (Vm.filter (fun w => G.Adj p.1 w)).card)
  have hE_split : E.card = E1.card + E2.card := by
    have hd : Disjoint E1 E2 := Finset.disjoint_left.mpr (fun p h1 h2 => by
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega)
    have hu : E1 ∪ E2 = E := by
      ext p; simp only [E1, E2, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hc : (Vm.filter (fun w => G.Adj p.1 w)).card ≤ 1
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hd, hu]
  -- Projection onto Vp is injective on E1, and projection onto Vm is injective on E2!
  have hE1_inj : ∀ p1 ∈ E1, ∀ p2 ∈ E1, p1.1 = p2.1 → p1 = p2 := by
    intro p1 h1 p2 h2 heq
    have h1' := Finset.mem_filter.mp h1
    have h2' := Finset.mem_filter.mp h2
    have h1e := Finset.mem_filter.mp h1'.1
    have h2e := Finset.mem_filter.mp h2'.1
    have hm1 : p1.2 ∈ Vm.filter (fun w => G.Adj p1.1 w) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h1e.1).2, h1e.2⟩
    have hm2 : p2.2 ∈ Vm.filter (fun w => G.Adj p1.1 w) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h2e.1).2, heq ▸ h2e.2⟩
    have hcard1 : (Vm.filter (fun w => G.Adj p1.1 w)).card ≤ 1 := h1'.2
    have hw_eq : p1.2 = p2.2 := Finset.card_le_one.mp hcard1 _ hm1 _ hm2
    exact Prod.ext heq hw_eq
  have hE2_inj : ∀ p1 ∈ E2, ∀ p2 ∈ E2, p1.2 = p2.2 → p1 = p2 := by
    intro p1 h1 p2 h2 heq
    have h1' := Finset.mem_filter.mp h1
    have h2' := Finset.mem_filter.mp h2
    have h1e := Finset.mem_filter.mp h1'.1
    have h2e := Finset.mem_filter.mp h2'.1
    have hcard1 : (Vp.filter (fun v => G.Adj v p1.2)).card ≤ 1 := (hno_both p1 h1'.1).resolve_left (by omega)
    have hm1 : p1.1 ∈ Vp.filter (fun v => G.Adj v p1.2) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h1e.1).1, h1e.2⟩
    have hm2 : p2.1 ∈ Vp.filter (fun v => G.Adj v p1.2) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h2e.1).1, heq ▸ h2e.2⟩
    have hv_eq : p1.1 = p2.1 := Finset.card_le_one.mp hcard1 _ hm1 _ hm2
    exact Prod.ext hv_eq heq
  by_cases hE1_ne : E1.Nonempty
  · by_cases hE2_ne : E2.Nonempty
    · -- Both nonempty: E1 projects into Vp.erase p2.1 (size <= |Vp| - 1), E2 into Vm.erase p1.2 (size <= |Vm| - 1)!
      obtain ⟨p2, hp2⟩ := hE2_ne
      obtain ⟨p1, hp1⟩ := hE1_ne
      have hp2_vp : p2.1 ∈ Vp := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1).1
      have hp1_vm : p1.2 ∈ Vm := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1).2
      have hE1_le : E1.card ≤ (Vp.erase p2.1).card := by
        refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun a ha b hb h => hE1_inj a ha b hb h)
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1⟩)
        intro heq
        have h1 := (Finset.mem_filter.mp hp).2
        have h2 := (Finset.mem_filter.mp hp2).2
        rw [heq] at h1; omega
      have hE2_le : E2.card ≤ (Vm.erase p1.2).card := by
        refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun a ha b hb h => hE2_inj a ha b hb h)
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2⟩)
        intro heq
        have hdeg_w : (Vp.filter (fun v => G.Adj v p.2)).card ≤ 1 :=
          (hno_both p (Finset.mem_filter.mp hp).1).resolve_left (by have := (Finset.mem_filter.mp hp).2; omega)
        have hp_e := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
        have hp1_e := Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1
        have hm1 : p.1 ∈ Vp.filter (fun v => G.Adj v p.2) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp_e.1).1, hp_e.2⟩
        have hm2 : p1.1 ∈ Vp.filter (fun v => G.Adj v p.2) := Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp1_e.1).1, heq ▸ hp1_e.2⟩
        have hv_eq : p.1 = p1.1 := Finset.card_le_one.mp hdeg_w _ hm1 _ hm2
        have h1 := (Finset.mem_filter.mp hp1).2
        have h2 := (Finset.mem_filter.mp hp).2
        rw [hv_eq] at h2; omega
      rw [Finset.card_erase_of_mem hp2_vp] at hE1_le
      rw [Finset.card_erase_of_mem hp1_vm] at hE2_le
      omega
    · have hE2_0 : E2.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hE2_ne)
      have hE1_le : E1.card ≤ Vp.card :=
        Finset.card_le_card_of_injOn Prod.fst (fun p hp =>
          Finset.mem_coe.mpr (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1)
          (fun a ha b hb h => hE1_inj a ha b hb h)
      omega
  · have hE1_0 : E1.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hE1_ne)
    have hE2_le : E2.card ≤ Vm.card :=
      Finset.card_le_card_of_injOn Prod.snd (fun p hp =>
        Finset.mem_coe.mpr (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2)
        (fun a ha b hb h => hE2_inj a ha b hb h)
    omega

-- Antidirected P_4-internal tree embedding: ANY antidirected tree on n >= 5 vertices whose
-- internal vertices form a P_4 (a1 -> b1 <- a2 -> b2) embeds in every no-source/no-sink tournament on 2n - 2 vertices!
lemma embeds_antidirected_P4_internal {n : ℕ} (hn : 5 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (hAnti : ∀ w : W, (∀ x : W, ¬ D.Adj x w) ∨ (∀ x : W, ¬ D.Adj w x))
    (a1 b1 a2 b2 : W)
    (hab : a1 ≠ b1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ a2 ≠ b2)
    (hP4 : D.Adj a1 b1 ∧ D.Adj a2 b1 ∧ D.Adj a2 b2)
    (hInt_eq : Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card) = {a1, b1, a2, b2})
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≤ 2 * n - 4)
    (hNoSnk : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card ≤ 2 * n - 4) :
    Embeds D G := by
  let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
  let Vm := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card)
  obtain ⟨v1, v2, w1, w2, hv1, hv2, hw1, hw2, hv12, hw12, hG1, hG2, hG3⟩ :=
    tournament_exists_cross_P4 (by omega) G hV hG hNoSrc hNoSnk
  have hdisj_pm : Disjoint Vp Vm := by
    refine Finset.disjoint_left.mpr (fun v h1 h2 => ?_)
    have hdisj_io : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
        (Finset.univ.filter (fun u : V => G.Adj u v)) := Finset.disjoint_left.mpr (fun u ha hb =>
      ((hG.2 v u (fun h => hG.1 v (h ▸ (Finset.mem_filter.mp ha).2))).mp (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hb).2)
    have hsub_er : Finset.univ.filter (fun u : V => G.Adj v u) ∪
        Finset.univ.filter (fun u : V => G.Adj u v) ⊆ Finset.univ.erase v := by
      intro u hu; refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl; rcases Finset.mem_union.mp hu with h | h <;> exact hG.1 u (Finset.mem_filter.mp h).2
    have hc := Finset.card_le_card hsub_er
    rw [Finset.card_union_of_disjoint hdisj_io, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV] at hc
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  -- Note: a1, a2 are sources (no in-neighbors) and b1, b2 are sinks (no out-neighbors)!
  have ha1_src : ∀ x, ¬ D.Adj x a1 := (hAnti a1).resolve_right (fun h => h b1 hP4.1)
  have ha2_src : ∀ x, ¬ D.Adj x a2 := (hAnti a2).resolve_right (fun h => h b1 hP4.2.1)
  have hb1_snk : ∀ x, ¬ D.Adj b1 x := (hAnti b1).resolve_left (fun h => h a1 hP4.1)
  have hb2_snk : ∀ x, ¬ D.Adj b2 x := (hAnti b2).resolve_left (fun h => h a2 hP4.2.2)
  -- No other D-edges exist inside I = {a1, b1, a2, b2}!
  -- Because a1, a2 are sources and b1, b2 are sinks, the ONLY possible extra edge inside I is a1 -> b2,
  -- which would close a 4-cycle a1 - b1 - a2 - b2 - a1 in the tree T!
  have hnot_a1b2 : ¬ D.Adj a1 b2 := by
    intro h
    let p1 : T.Walk a1 b2 := SimpleGraph.Walk.cons (hO.1 a1 b2 h) SimpleGraph.Walk.nil
    let p2 : T.Walk a1 b2 := SimpleGraph.Walk.cons (hO.1 a1 b1 hP4.1)
      (SimpleGraph.Walk.cons (hO.1 a2 b1 hP4.2.1).symm
        (SimpleGraph.Walk.cons (hO.1 a2 b2 hP4.2.2) SimpleGraph.Walk.nil))
    have hp1 : p1.IsPath := by
      refine SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil ?_
      simp [hab.2.2.1]
    have hp2 : p2.IsPath := by
      refine SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.cons
        (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hab.2.2.2.2.2]))
        (by simp [hab.2.2.2.1, hab.2.2.2.2.1]))
        (by simp [hab.1, hab.2.1, hab.2.2.1])
    have heq := congrArg (fun p : T.Walk a1 b2 => p.length)
      (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path a1 b2).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
    simp [p1, p2] at heq
  let I : Finset W := {a1, b1, a2, b2}
  -- Every w ∉ I is a leaf whose unique T-neighbor lies in I!
  have hleaf_nb : ∀ w : W, w ∉ I → ∃! p : W, T.Adj w p ∧ p ∈ I := by
    intro w hwI
    have hdeg_le1 : (Finset.univ.filter (fun z : W => T.Adj w z)).card ≤ 1 := by
      by_contra h2
      have : w ∈ Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [hInt_eq] at this; exact hwI this
    have hex_nb : ∃ p : W, T.Adj w p := by
      obtain ⟨p⟩ := hT.connected w a1
      cases p with
      | nil => exact absurd (by simp [I]) hwI
      | @cons _ z _ hadj _ => exact ⟨z, hadj⟩
    obtain ⟨p, hTwp⟩ := hex_nb
    have hp_inI : p ∈ I := by
      by_contra hpI
      have hdeg_p : (Finset.univ.filter (fun z : W => T.Adj p z)).card ≤ 1 := by
        by_contra h2
        have : p ∈ Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        rw [hInt_eq] at this; exact hpI this
      -- Both w and p have deg <= 1 and T.Adj w p, so {w, p} is disconnected from a1 ∈ I!
      have hwa1 : w ≠ a1 := fun h => hwI (h ▸ by simp [I])
      have hpa1 : p ≠ a1 := fun h => hpI (h ▸ by simp [I])
      obtain ⟨qp, hqp, _⟩ := (hT.connected w a1).exists_path_of_dist
      cases qp with
      | nil => exact hwa1 rfl
      | @cons _ z1 _ hTwz1 qp1 =>
        have hz1p : z1 = p := Finset.card_le_one.mp hdeg_le1 _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwz1⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwp⟩)
        subst z1
        cases qp1 with
        | nil => exact hpa1 rfl
        | @cons _ z2 _ hTpz2 _ =>
          have hz2w : z2 = w := Finset.card_le_one.mp hdeg_p _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTpz2⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwp.symm⟩)
          subst z2
          have hnodup := hqp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons,
            SimpleGraph.Walk.start_mem_support, or_true, not_true_eq_false, false_and] at hnodup
    refine ⟨p, ⟨hTwp, hp_inI⟩, fun p' ⟨hTwp', _⟩ => ?_⟩
    exact Finset.card_le_one.mp hdeg_le1 _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwp'⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTwp⟩)
  -- Inductively extend embedding from I to any S with I ⊆ S!
  have hext : ∀ (Lsub : Finset W), Disjoint Lsub I →
      ∃ f : W → V,
        (∀ x ∈ I ∪ Lsub, ∀ y ∈ I ∪ Lsub, f x = f y → x = y) ∧
        (∀ x ∈ I ∪ Lsub, ∀ y ∈ I ∪ Lsub, D.Adj x y → G.Adj (f x) (f y)) ∧
        f a1 ∈ Vp ∧ f a2 ∈ Vp ∧ f b1 ∈ Vm ∧ f b2 ∈ Vm := by
    intro Lsub
    induction Lsub using Finset.induction with
    | empty =>
      intro _
      let f0 : W → V := fun x =>
        if x = a1 then v1 else if x = b1 then w1 else if x = a2 then v2 else w2
      have hvw_ne : ∀ x ∈ Vp, ∀ y ∈ Vm, x ≠ y := fun x hx y hy h =>
        Finset.disjoint_left.mp hdisj_pm hx (h ▸ hy)
      refine ⟨f0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hfxy
        simp only [Finset.union_empty, I, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
        all_goals try rfl
        all_goals (simp only [f0, hab.1.symm, hab.2.1.symm, hab.2.2.1.symm, hab.2.2.2.1.symm,
          hab.2.2.2.2.1.symm, hab.2.2.2.2.2.symm, ↓reduceIte] at hfxy)
        · exact absurd hfxy (hvw_ne v1 hv1 w1 hw1)
        · exact absurd hfxy hv12
        · exact absurd hfxy (hvw_ne v1 hv1 w2 hw2)
        · exact absurd hfxy.symm (hvw_ne v1 hv1 w1 hw1)
        · exact absurd hfxy.symm (hvw_ne v2 hv2 w1 hw1)
        · exact absurd hfxy hw12
        · exact absurd hfxy.symm hv12
        · exact absurd hfxy (hvw_ne v2 hv2 w1 hw1)
        · exact absurd hfxy (hvw_ne v2 hv2 w2 hw2)
        · exact absurd hfxy.symm (hvw_ne v1 hv1 w2 hw2)
        · exact absurd hfxy.symm hw12
        · exact absurd hfxy.symm (hvw_ne v2 hv2 w2 hw2)
      · intro x hx y hy hDxy
        simp only [Finset.union_empty, I, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
        all_goals (try exact absurd hDxy (ha1_src _))
        all_goals (try exact absurd hDxy (ha2_src _))
        all_goals (try exact absurd hDxy (hb1_snk _))
        all_goals (try exact absurd hDxy (hb2_snk _))
        all_goals (try exact absurd hDxy hnot_a1b2)
        all_goals (simp only [f0, hab.1.symm, hab.2.1.symm, hab.2.2.1.symm, hab.2.2.2.1.symm,
          hab.2.2.2.2.1.symm, hab.2.2.2.2.2.symm, ↓reduceIte])
        · exact hG1
        · exact hG2
        · exact hG3
      · simp [f0]; exact hv1
      · simp [f0, hab.2.1.symm, hab.2.2.2.1.symm]; exact hv2
      · simp [f0, hab.1.symm]; exact hw1
      · simp [f0, hab.2.2.1.symm, hab.2.2.2.2.1.symm, hab.2.2.2.2.2.symm]; exact hw2
    | @insert l L' hl ih =>
      intro hdisj
      have hdisj' : Disjoint L' I := hdisj.mono_left (Finset.subset_insert l L')
      have hlI : l ∉ I := fun h => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self l L') h
      obtain ⟨f, hfinj, hfadj, hfa1, hfa2, hfb1, hfb2⟩ := ih hdisj'
      obtain ⟨p, ⟨hTlp, hpI⟩, hpu⟩ := hleaf_nb l hlI
      let S := I ∪ L'
      have hl_notS : l ∉ S := fun h => by
        rcases Finset.mem_union.mp h with h1 | h2
        · exact hlI h1
        · exact hl h2
      have hS_lt : S.card < n := by
        have hsub : insert l S ⊆ Finset.univ := Finset.subset_univ _
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hl_notS, Finset.card_univ, hW] at hc; omega
      have himg_le : (S.image f).card ≤ n - 1 := by
        have := Finset.card_image_le (f := f) (s := S); omega
      have hpS : p ∈ S := Finset.mem_union_left L' hpI
      -- Find an unused neighbor u of f p in the required direction!
      have hex_u : ∃ u : V, u ∉ S.image f ∧ (D.Adj p l → G.Adj (f p) u) ∧ (D.Adj l p → G.Adj u (f p)) := by
        rcases adj_or_rev_of_isOrientation hO hTlp.symm with hDpl | hDlp
        · -- p -> l: p is a source in I, so p ∈ {a1, a2}, so f p ∈ Vp!
          have hfp_Vp : f p ∈ Vp := by
            simp only [I, Finset.mem_insert, Finset.mem_singleton] at hpI
            rcases hpI with rfl | rfl | rfl | rfl
            · exact hfa1
            · exact absurd hDpl (hb1_snk l)
            · exact hfa2
            · exact absurd hDpl (hb2_snk l)
          let Nout := Finset.univ.filter (fun u : V => G.Adj (f p) u)
          have hNcard : n - 1 ≤ Nout.card := (Finset.mem_filter.mp hfp_Vp).2
          have hfp_not_N : f p ∉ Nout := fun h => hG.1 (f p) (Finset.mem_filter.mp h).2
          have hfp_in_img : f p ∈ S.image f := Finset.mem_image_of_mem f hpS
          have hinter_le : (Nout ∩ S.image f).card ≤ (S.image f).card - 1 := by
            have hsub : Nout ∩ S.image f ⊆ (S.image f).erase (f p) := fun u hu =>
              Finset.mem_erase.mpr ⟨fun h => hfp_not_N (h ▸ (Finset.mem_inter.mp hu).1), (Finset.mem_inter.mp hu).2⟩
            have hc := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hfp_in_img] at hc; exact hc
          have hsdiff_pos : 0 < (Nout \ S.image f).card := by
            rw [Finset.card_sdiff, Finset.inter_comm]; omega
          obtain ⟨u, hu⟩ := Finset.card_pos.mp hsdiff_pos
          exact ⟨u, (Finset.mem_sdiff.mp hu).2, fun _ => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2,
            fun h => absurd h (not_adj_rev_of_isOrientation hO hDpl)⟩
        · -- l -> p: p is a sink in I, so p ∈ {b1, b2}, so f p ∈ Vm!
          have hfp_Vm : f p ∈ Vm := by
            simp only [I, Finset.mem_insert, Finset.mem_singleton] at hpI
            rcases hpI with rfl | rfl | rfl | rfl
            · exact absurd hDlp (ha1_src l)
            · exact hfb1
            · exact absurd hDlp (ha2_src l)
            · exact hfb2
          let Nin := Finset.univ.filter (fun u : V => G.Adj u (f p))
          have hNcard : n - 1 ≤ Nin.card := (Finset.mem_filter.mp hfp_Vm).2
          have hfp_not_N : f p ∉ Nin := fun h => hG.1 (f p) (Finset.mem_filter.mp h).2
          have hfp_in_img : f p ∈ S.image f := Finset.mem_image_of_mem f hpS
          have hinter_le : (Nin ∩ S.image f).card ≤ (S.image f).card - 1 := by
            have hsub : Nin ∩ S.image f ⊆ (S.image f).erase (f p) := fun u hu =>
              Finset.mem_erase.mpr ⟨fun h => hfp_not_N (h ▸ (Finset.mem_inter.mp hu).1), (Finset.mem_inter.mp hu).2⟩
            have hc := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hfp_in_img] at hc; exact hc
          have hsdiff_pos : 0 < (Nin \ S.image f).card := by
            rw [Finset.card_sdiff, Finset.inter_comm]; omega
          obtain ⟨u, hu⟩ := Finset.card_pos.mp hsdiff_pos
          exact ⟨u, (Finset.mem_sdiff.mp hu).2,
            fun h => absurd h (not_adj_rev_of_isOrientation hO hDlp),
            fun _ => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2⟩
      obtain ⟨u, hu_not, hu_pl, hu_lp⟩ := hex_u
      let f' : W → V := fun x => if x = l then u else f x
      have hunion_eq : I ∪ insert l L' = insert l S := by
        ext x; simp only [S, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)
        · rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)
      have hne_I : ∀ x ∈ I, x ≠ l := fun x hx h => hlI (h ▸ hx)
      refine ⟨f', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hEq
        rw [hunion_eq] at hx hy
        rcases Finset.mem_insert.mp hx with hxl | hxS <;> rcases Finset.mem_insert.mp hy with hyl | hyS
        · exact hxl.trans hyl.symm
        · subst x
          have hny : y ≠ l := fun h => hl_notS (h ▸ hyS)
          simp only [f', ↓reduceIte, hny] at hEq
          exact absurd (hEq ▸ Finset.mem_image_of_mem f hyS) hu_not
        · subst y
          have hnx : x ≠ l := fun h => hl_notS (h ▸ hxS)
          simp only [f', ↓reduceIte, hnx] at hEq
          exact absurd (hEq.symm ▸ Finset.mem_image_of_mem f hxS) hu_not
        · have hnx : x ≠ l := fun h => hl_notS (h ▸ hxS)
          have hny : y ≠ l := fun h => hl_notS (h ▸ hyS)
          simp only [f', hnx, hny, ↓reduceIte] at hEq
          exact hfinj x hxS y hyS hEq
      · intro x hx y hy hDxy
        rw [hunion_eq] at hx hy
        rcases Finset.mem_insert.mp hx with hxl | hxS <;> rcases Finset.mem_insert.mp hy with hyl | hyS
        · subst x; subst y; exact absurd rfl (T.ne_of_adj (hO.1 l l hDxy))
        · subst x
          have hny : y ≠ l := fun h => hl_notS (h ▸ hyS)
          have hyp : y = p := by
            have hTly : T.Adj l y := hO.1 l y hDxy
            have hdeg_le1 : (Finset.univ.filter (fun z : W => T.Adj l z)).card ≤ 1 := by
              by_contra h2
              have : l ∈ Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
              rw [hInt_eq] at this; exact hlI this
            exact Finset.card_le_one.mp hdeg_le1 _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTly⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlp⟩)
          subst y
          simp only [f', ↓reduceIte, hny]; exact hu_lp hDxy
        · subst y
          have hnx : x ≠ l := fun h => hl_notS (h ▸ hxS)
          have hxp : x = p := by
            have hTlx : T.Adj l x := (hO.1 x l hDxy).symm
            have hdeg_le1 : (Finset.univ.filter (fun z : W => T.Adj l z)).card ≤ 1 := by
              by_contra h2
              have : l ∈ Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
              rw [hInt_eq] at this; exact hlI this
            exact Finset.card_le_one.mp hdeg_le1 _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlx⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlp⟩)
          subst x
          simp only [f', ↓reduceIte, hnx]; exact hu_pl hDxy
        · have hnx : x ≠ l := fun h => hl_notS (h ▸ hxS)
          have hny : y ≠ l := fun h => hl_notS (h ▸ hyS)
          simp only [f', hnx, hny, ↓reduceIte]; exact hfadj x hxS y hyS hDxy
      · simp only [f', hne_I a1 (by simp [I]), ↓reduceIte]; exact hfa1
      · simp only [f', hne_I a2 (by simp [I]), ↓reduceIte]; exact hfa2
      · simp only [f', hne_I b1 (by simp [I]), ↓reduceIte]; exact hfb1
      · simp only [f', hne_I b2 (by simp [I]), ↓reduceIte]; exact hfb2
  obtain ⟨f, hfinj, hfadj, _, _, _, _⟩ := hext (Finset.univ \ I) Finset.sdiff_disjoint
  have hmem_cov : ∀ z : W, z ∈ I ∪ (Finset.univ \ I) := fun z => by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ I)]; exact Finset.mem_univ z
  refine ⟨⟨f, fun hxy => hfadj _ (hmem_cov _) _ (hmem_cov _) hxy⟩,
    fun x y h => hfinj x (hmem_cov x) y (hmem_cov y) h⟩

-- COMPLETE CLOSER FOR R1.H1: Every oriented tree on n >= 6 vertices with 4 <= n - k
-- and (k <= 4 ∨ 3k <= n) embeds in every no-source/no-sink (hence every 2-strong!) tournament on 2n - 2 vertices!
theorem embeds_R1_H1 {n : ℕ} (hn : 6 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≤ 2 * n - 4)
    (hNoSnk : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card ≤ 2 * n - 4)
    (hInt : 4 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card)
    (hk : (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ 4 ∨
      3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n) :
    Embeds D G := by
  let LeavesW := Finset.univ.filter (fun w : W =>
    (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)
  by_cases h3k : 3 * LeavesW.card ≤ n + 3
  · exact embeds_dross_havet_3k_le_n_add_3 (by omega) D hW hTree G hV hG h3k
  · -- Only remaining pair is n = 8, k = 4!
    have hInt' : 4 ≤ n - LeavesW.card := hInt
    have hk' : LeavesW.card ≤ 4 ∨ 3 * LeavesW.card ≤ n := hk
    have hnk : n = 8 ∧ LeavesW.card = 4 := by
      rcases hk' with h4 | h3 <;> omega
    rcases hnk with ⟨hn8, hk4⟩
    by_cases hNotAnti : ∃ v s t : W, D.Adj s v ∧ D.Adj v t
    · exact embeds_dross_havet_non_antidirected (by omega) D hW hTree hNotAnti G hG (by omega)
    · -- D is antidirected with n = 8, k = 4!
      have hAnti : ∀ w : W, (∀ x : W, ¬ D.Adj x w) ∨ (∀ x : W, ¬ D.Adj w x) := by
        intro w
        by_contra h
        push Not at h
        obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := h
        exact hNotAnti ⟨w, s, t, hs, ht⟩
      obtain ⟨T, hT, hO⟩ := hTree
      have hdeg_eq : ∀ w : W, (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card =
          (Finset.univ.filter (fun z : W => T.Adj w z)).card := by
        intro w; congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => by rcases h with h1 | h2; exact hO.1 w z h1; exact (hO.1 z w h2).symm,
          fun h => adj_or_rev_of_isOrientation hO h⟩
      let IntW := Finset.univ.filter (fun w : W => 2 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card)
      have hdeg_pos : ∀ w : W, 1 ≤ (Finset.univ.filter (fun z : W => T.Adj w z)).card := by
        intro w
        obtain ⟨u1, u2, hu12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
        have hex : ∃ u : W, u ≠ w := by
          by_cases h1 : u1 = w; exact ⟨u2, fun h => hu12 (h1.trans h.symm)⟩; exact ⟨u1, h1⟩
        obtain ⟨u, huw⟩ := hex
        obtain ⟨p⟩ := hT.connected w u
        cases p with
        | nil => exact absurd rfl huw
        | @cons _ z _ hadj _ => exact Finset.one_le_card.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩
      have hInt_comp : IntW = Finset.univ \ LeavesW := by
        ext w; simp only [IntW, LeavesW, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hdeg_eq]
        have := hdeg_pos w; omega
      have hInt_card : IntW.card = 4 := by
        rw [hInt_comp, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, hW, hk4, hn8]
      -- Internal vertices are closed under tree paths (so T[IntW] is connected)!
      have hInt_path : ∀ u ∈ IntW, ∀ v ∈ IntW, ∀ (p : T.Walk u v), p.IsPath → ∀ z ∈ p.support, z ∈ IntW := by
        intro u hu v hv p hp z hz
        by_cases hzu : z = u; · exact hzu ▸ hu
        by_cases hzv : z = v; · exact hzv ▸ hv
        -- z is an internal vertex of the path p, so it has 2 distinct neighbors on p!
        have hp_split := SimpleGraph.Walk.take_spec p hz
        let p1 := p.takeUntil z hz
        let p2 := p.dropUntil z hz
        have hp1_ne : p1.length ≠ 0 := fun h => hzu (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
        have hp2_ne : p2.length ≠ 0 := fun h => hzv (SimpleGraph.Walk.eq_of_length_eq_zero h)
        cases h1 : p1.reverse with
        | nil =>
          have := congrArg SimpleGraph.Walk.length h1
          simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_nil] at this
          exact absurd this hp1_ne
        | @cons _ x1 _ hTzx1 _ =>
          cases h2 : p2 with
          | nil =>
            have := congrArg SimpleGraph.Walk.length h2
            simp only [SimpleGraph.Walk.length_nil] at this
            exact absurd this hp2_ne
          | @cons _ x2 _ hTzx2 _ =>
            have hx12 : x1 ≠ x2 := by
              intro hEq
              have hnodup := hp.support_nodup
              rw [← hp_split, SimpleGraph.Walk.support_append, List.nodup_append] at hnodup
              have hx1_mem : x1 ∈ p1.support := by
                have hm : x1 ∈ p1.reverse.support := by
                  rw [h1]; simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support]
                rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm
                exact hm
              have hx2_mem : x2 ∈ p2.support.tail := by
                rw [h2]; simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support]
              exact hnodup.2.2 x1 hx1_mem x2 hx2_mem hEq
            have hsub : ({x1, x2} : Finset W) ⊆ Finset.univ.filter (fun w => T.Adj z w) := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
            have hc := Finset.card_le_card hsub; rw [Finset.card_pair hx12] at hc
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      -- Every vertex in IntW has internal degree >= 1 (since IntW has 4 vertices and T[IntW] is connected)!
      have hdegI_pos : ∀ x ∈ IntW, 1 ≤ (IntW.filter (fun y => T.Adj x y)).card := by
        intro x hx
        have hne : (IntW.erase x).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx, hInt_card]; omega)
        obtain ⟨y, hy⟩ := hne
        have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
        have hyI : y ∈ IntW := (Finset.mem_erase.mp hy).2
        obtain ⟨p, hp, _⟩ := (hT.connected x y).exists_path_of_dist
        cases p with
        | nil => exact absurd rfl hyne.symm
        | @cons _ z _ hTxz p' =>
          have hzI : z ∈ IntW := hInt_path x hx y hyI (SimpleGraph.Walk.cons hTxz p') hp z
            (by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
          exact Finset.one_le_card.mpr ⟨z, Finset.mem_filter.mpr ⟨hzI, hTxz⟩⟩
      -- Case split on whether IntW has a vertex of internal degree 3 (K_{1,3}) or max internal degree <= 2 (P_4)!
      by_cases hstar : ∃ c ∈ IntW, (IntW.filter (fun y => T.Adj c y)).card = 3
      · -- Case 1: K_{1,3} internal subtree centered at c!
        -- Prove min(gammaD, gammaU) <= 3, then apply dross_havet_embed_of_exists_gamma_le!
        obtain ⟨c, hcI, hcdeg⟩ := hstar
        have hc_adj_all : ∀ y ∈ IntW, y ≠ c → T.Adj c y := by
          intro y hyI hyne
          have hsub : IntW.filter (fun z => T.Adj c z) ⊆ IntW.erase c := fun z hz =>
            Finset.mem_erase.mpr ⟨(T.ne_of_adj (Finset.mem_filter.mp hz).2).symm, (Finset.mem_filter.mp hz).1⟩
          have heq : IntW.filter (fun z => T.Adj c z) = IntW.erase c :=
            Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hcI, hInt_card, hcdeg])
          have : y ∈ IntW.filter (fun z => T.Adj c z) := heq ▸ Finset.mem_erase.mpr ⟨hyne, hyI⟩
          exact (Finset.mem_filter.mp this).2
        -- No two vertices of IntW \ {c} are adjacent (else triangle in tree T)!
        have hno_tri : ∀ y1 ∈ IntW, ∀ y2 ∈ IntW, y1 ≠ c → y2 ≠ c → ¬ T.Adj y1 y2 := by
          intro y1 hy1 y2 hy2 h1c h2c h12
          let p1 : T.Walk y1 y2 := SimpleGraph.Walk.cons h12 SimpleGraph.Walk.nil
          let p2 : T.Walk y1 y2 := SimpleGraph.Walk.cons (hc_adj_all y1 hy1 h1c).symm
            (SimpleGraph.Walk.cons (hc_adj_all y2 hy2 h2c) SimpleGraph.Walk.nil)
          have h12ne : y1 ≠ y2 := T.ne_of_adj h12
          have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h12ne])
          have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h2c.symm]))
            (by simp [h1c, h12ne])
          have heq := congrArg (fun p : T.Walk y1 y2 => p.length)
            (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path y1 y2).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
          simp [p1, p2] at heq
        -- Every leaf l ∈ LeavesW has a unique T-neighbor in IntW!
        have hleaf_to_I : ∀ l ∈ LeavesW, ∃! x : W, x ∈ IntW ∧ T.Adj l x := by
          intro l hl
          have hdeg1 : (Finset.univ.filter (fun z : W => T.Adj l z)).card = 1 := by
            rw [← hdeg_eq]; exact (Finset.mem_filter.mp hl).2
          obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => T.Adj l z)).card)
          have hTlx : T.Adj l x := (Finset.mem_filter.mp hx).2
          have hxI : x ∈ IntW := by
            by_contra hxnot
            have hxL : x ∈ LeavesW := by
              rw [hInt_comp, Finset.mem_sdiff] at hxnot; exact by_contra (fun h => hxnot ⟨Finset.mem_univ x, h⟩)
            have hxdeg1 : (Finset.univ.filter (fun z : W => T.Adj x z)).card = 1 := by
              rw [← hdeg_eq]; exact (Finset.mem_filter.mp hxL).2
            have hlc : l ≠ c := fun h => by rw [← h, hInt_comp, Finset.mem_sdiff] at hcI; exact hcI.2 hl
            have hxc : x ≠ c := fun h => hxnot (h ▸ hcI)
            obtain ⟨qp, hqp, _⟩ := (hT.connected l c).exists_path_of_dist
            cases qp with
            | nil => exact hlc rfl
            | @cons _ z1 _ hTlz1 qp1 =>
              have hz1x : z1 = x := Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj l z)).card ≤ 1) _
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlz1⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlx⟩)
              subst z1
              cases qp1 with
              | nil => exact hxc rfl
              | @cons _ z2 _ hTxz2 _ =>
                have hz2l : z2 = l := Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj x z)).card ≤ 1) _
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxz2⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlx.symm⟩)
                subst z2
                have hnd := hqp.support_nodup
                simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons,
                  SimpleGraph.Walk.start_mem_support, or_true, not_true_eq_false, false_and] at hnd
          exact ⟨x, ⟨hxI, hTlx⟩, fun x' ⟨_, hTlx'⟩ => Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj l z)).card ≤ 1) _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlx'⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTlx⟩)⟩
        -- Helper: given an orientation D0 of T where c is a SOURCE (∀ x, ¬ D0.Adj x c),
        -- we get ∃ r1, gD0 r1 <= 3 ∨ gU0 r1 <= 3!
        have hK13_core : ∀ (D0 : Digraph W) [DecidableRel D0.Adj] (hO0 : D0.IsOrientation T),
            (∀ w : W, (∀ x : W, ¬ D0.Adj x w) ∨ (∀ x : W, ¬ D0.Adj w x)) →
            (∀ x : W, ¬ D0.Adj x c) →
            ∃ r1 : W,
              (∑ c0 ∈ Finset.univ.filter (fun c0 : W =>
                  (∃ x : W, D0.Adj x c0 ∧ T.dist r1 c0 < T.dist r1 x) ∧
                  (∀ p : W, ¬ (D0.Adj c0 p ∧ T.dist r1 p < T.dist r1 c0))),
                ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D0.Adj x y ∧ T.dist r1 y < T.dist r1 x) w c0)).card +
                 ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D0.Adj x y ∧ T.dist r1 y < T.dist r1 x) w c0)).filter
                   (fun w => ∀ x : W, ¬ (D0.Adj x w ∧ T.dist r1 w < T.dist r1 x))).card - 2)) ≤ 3 ∨
              (∑ c0 ∈ Finset.univ.filter (fun c0 : W =>
                  (∃ x : W, D0.Adj c0 x ∧ T.dist r1 c0 < T.dist r1 x) ∧
                  (∀ p : W, ¬ (D0.Adj p c0 ∧ T.dist r1 p < T.dist r1 c0))),
                ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D0.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c0)).card +
                 ((Finset.univ.filter (fun w : W => Relation.ReflTransGen (fun x y => D0.Adj y x ∧ T.dist r1 y < T.dist r1 x) w c0)).filter
                   (fun w => ∀ x : W, ¬ (D0.Adj w x ∧ T.dist r1 w < T.dist r1 x))).card - 2)) ≤ 3 := by
          intro D0 _ hO0 hAnti0 hc_src
          -- Every b ∈ IntW.erase c has D0.Adj c b, hence b is a SINK in D0!
          have hb_snk : ∀ b ∈ IntW.erase c, D0.Adj c b ∧ ∀ x : W, ¬ D0.Adj b x := by
            intro b hb
            have hTcb : T.Adj c b := hc_adj_all b (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1
            have hDcb : D0.Adj c b := (adj_or_rev_of_isOrientation hO0 hTcb).resolve_right (hc_src b)
            exact ⟨hDcb, (hAnti0 b).resolve_left (fun h => h c hDcb)⟩
          -- Check if c has a leaf neighbor!
          by_cases hc_leaf : ∃ l ∈ LeavesW, T.Adj l c
          · -- Subcase 1: c has a leaf l0 -> at root r1 = c, DownAdj consists ONLY of edges l -> b (l ∈ LeavesW \ {l0}, b ∈ IntW.erase c)!
            obtain ⟨l0, hl0L, hTl0c⟩ := hc_leaf
            refine ⟨c, Or.inl ?_⟩
            -- Every DownAdj(D0, c) edge has head b ∈ IntW.erase c and tail l ∈ LeavesW.erase l0!
            let dA : W → W → Prop := fun x y => D0.Adj x y ∧ T.dist c y < T.dist c x
            have hdA_char : ∀ x y : W, dA x y → x ∈ LeavesW.erase l0 ∧ y ∈ IntW.erase c := by
              intro x y hxy
              have hTxy : T.Adj x y := hO0.1 x y hxy.1
              have hyne : y ≠ c := fun h => hc_src x (h ▸ hxy.1)
              have hxne : x ≠ c := fun h => by subst h; have := hxy.2; rw [SimpleGraph.dist_self] at this; omega
              have hyI : y ∈ IntW := by
                by_contra hynot
                have hyL : y ∈ LeavesW := by
                  rw [hInt_comp, Finset.mem_sdiff] at hynot; exact by_contra (fun h => hynot ⟨Finset.mem_univ y, h⟩)
                obtain ⟨p, ⟨hpI, hTyp⟩, hpu⟩ := hleaf_to_I y hyL
                have hxp : x = p := by
                  have hdeg1 : (Finset.univ.filter (fun z : W => T.Adj y z)).card = 1 := by
                    rw [← hdeg_eq]; exact (Finset.mem_filter.mp hyL).2
                  exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj y z)).card ≤ 1) _
                    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy.symm⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTyp⟩)
                subst x
                have hx_er : p ∈ IntW.erase c := Finset.mem_erase.mpr ⟨hxne, hpI⟩
                exact (hb_snk p hx_er).2 y hxy.1
              have hy_er : y ∈ IntW.erase c := Finset.mem_erase.mpr ⟨hyne, hyI⟩
              have hxL : x ∈ LeavesW := by
                by_contra hxnot
                have hxI : x ∈ IntW := by rw [hInt_comp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnot⟩
                exact hno_tri x hxI y hyI hxne hyne hTxy
              have hxl0 : x ≠ l0 := by
                intro hx_eq; subst x
                obtain ⟨p, _, hpu⟩ := hleaf_to_I l0 hl0L
                exact hyne ((hpu y ⟨hyI, hTxy⟩).trans (hpu c ⟨hcI, hTl0c⟩).symm)
              exact ⟨Finset.mem_erase.mpr ⟨hxl0, hxL⟩, hy_er⟩
            -- Hence EVERY DownRoot b belongs to IntW.erase c, and every compDown b is {b} ∪ (leaves attached to b),
            -- so (|comp b| + |inLeaves b| - 2) <= 2 * |{l ∈ LeavesW.erase l0 : dA l b}| - 1!
            let DR := Finset.univ.filter (fun c0 : W => (∃ x, dA x c0) ∧ ∀ p, ¬ dA c0 p)
            let comp0 : W → Finset W := fun c0 => Finset.univ.filter (fun w => Relation.ReflTransGen dA w c0)
            let lv0 : W → Finset W := fun c0 => (comp0 c0).filter (fun w => ∀ x, ¬ dA x w)
            have hDR_sub : DR ⊆ IntW.erase c := fun b hb => by
              obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hb).2.1
              exact (hdA_char x b hx).2
            have hcomp_eq : ∀ b ∈ DR, comp0 b = insert b ((LeavesW.erase l0).filter (fun l => dA l b)) := by
              intro b hb
              ext w; simp only [comp0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · intro hp
                rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨z, hwz, hzb⟩
                · exact Or.inl rfl
                · have hzb_eq : z = b := by
                    rcases Relation.ReflTransGen.cases_head hzb with rfl | ⟨u, hzu, _⟩
                    · rfl
                    · have h1 := (Finset.mem_erase.mp (hdA_char w z hwz).2).2
                      have h2 := (hdA_char z u hzu).1
                      have hzL : z ∈ LeavesW := (Finset.mem_erase.mp h2).2
                      rw [hInt_comp, Finset.mem_sdiff] at h1
                      exact absurd hzL h1.2
                  subst z
                  exact Or.inr ⟨(hdA_char w b hwz).1, hwz⟩
              · rintro (rfl | ⟨_, hwb⟩)
                · exact .refl
                · exact .single hwb
            -- Each b ∈ IntW.erase c has deg_T(b) >= 2 and only 1 neighbor in IntW (namely c), so at least 1 leaf in LeavesW.erase l0!
            -- Since |IntW.erase c| = 3 and |LeavesW.erase l0| = 3, EVERY b ∈ DR has AT MOST 1 leaf in LeavesW.erase l0!
            have hEach_ge1 : ∀ b ∈ IntW.erase c, 1 ≤ ((LeavesW.erase l0).filter (fun l => T.Adj l b)).card := by
              intro b hb
              have hbI := (Finset.mem_erase.mp hb).2
              have hbne := (Finset.mem_erase.mp hb).1
              have hdeg2 : 2 ≤ (Finset.univ.filter (fun z : W => T.Adj b z)).card := (Finset.mem_filter.mp hbI).2
              have hcb : c ∈ Finset.univ.filter (fun z : W => T.Adj b z) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hc_adj_all b hbI hbne).symm⟩
              obtain ⟨l, hl⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hcb]; omega :
                0 < ((Finset.univ.filter (fun z : W => T.Adj b z)).erase c).card)
              have hlne : l ≠ c := (Finset.mem_erase.mp hl).1
              have hTbl : T.Adj b l := (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2
              have hlL : l ∈ LeavesW := by
                by_contra hnot
                have hlI : l ∈ IntW := by rw [hInt_comp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ l, hnot⟩
                exact hno_tri b hbI l hlI hbne hlne hTbl
              have hll0 : l ≠ l0 := by
                intro hl_eq; subst l
                obtain ⟨p, _, hpu⟩ := hleaf_to_I l0 hl0L
                exact hbne ((hpu b ⟨hbI, hTbl.symm⟩).trans (hpu c ⟨hcI, hTl0c⟩).symm)
              exact Finset.one_le_card.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hll0, hlL⟩, hTbl.symm⟩⟩
            have hdisj_f : ∀ b1 ∈ IntW.erase c, ∀ b2 ∈ IntW.erase c, b1 ≠ b2 →
                Disjoint ((LeavesW.erase l0).filter (fun l => T.Adj l b1)) ((LeavesW.erase l0).filter (fun l => T.Adj l b2)) := by
              intro b1 hb1 b2 hb2 hne
              refine Finset.disjoint_left.mpr (fun l h1 h2 => ?_)
              have hlL := (Finset.mem_erase.mp (Finset.mem_filter.mp h1).1).2
              obtain ⟨p, _, hpu⟩ := hleaf_to_I l hlL
              exact hne ((hpu b1 ⟨(Finset.mem_erase.mp hb1).2, (Finset.mem_filter.mp h1).2⟩).trans
                (hpu b2 ⟨(Finset.mem_erase.mp hb2).2, (Finset.mem_filter.mp h2).2⟩).symm)
            have hsum_f : (∑ b ∈ IntW.erase c, ((LeavesW.erase l0).filter (fun l => T.Adj l b)).card) ≤ 3 := by
              rw [← Finset.card_biUnion (fun b1 hb1 b2 hb2 h => hdisj_f b1 hb1 b2 hb2 h)]
              have hsub : (IntW.erase c).biUnion (fun b => (LeavesW.erase l0).filter (fun l => T.Adj l b)) ⊆ LeavesW.erase l0 := by
                intro l hl; obtain ⟨_, _, hl'⟩ := Finset.mem_biUnion.mp hl; exact (Finset.mem_filter.mp hl').1
              have hc := Finset.card_le_card hsub
              rw [Finset.card_erase_of_mem hl0L, hk4] at hc; exact hc
            have hEach_eq1 : ∀ b ∈ IntW.erase c, ((LeavesW.erase l0).filter (fun l => T.Adj l b)).card = 1 := by
              intro b hb
              have h1 := hEach_ge1 b hb
              have hrest : 2 ≤ ∑ b' ∈ (IntW.erase c).erase b, ((LeavesW.erase l0).filter (fun l => T.Adj l b')).card := by
                calc 2 = ((IntW.erase c).erase b).card := by
                      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem hcI, hInt_card]
                  _ = ∑ _b' ∈ (IntW.erase c).erase b, 1 := by simp
                  _ ≤ _ := Finset.sum_le_sum (fun b' hb' => hEach_ge1 b' (Finset.mem_erase.mp hb').2)
              rw [← Finset.add_sum_erase _ _ hb] at hsum_f; omega
            -- Therefore every b ∈ DR has (comp0 b).card <= 2 and (lv0 b).card <= 1, so sum <= 3!
            calc ∑ b ∈ DR, ((comp0 b).card + (lv0 b).card - 2)
                ≤ ∑ _b ∈ DR, 1 := by
                  refine Finset.sum_le_sum (fun b hb => ?_)
                  have hsub1 : (LeavesW.erase l0).filter (fun l => dA l b) ⊆ (LeavesW.erase l0).filter (fun l => T.Adj l b) :=
                    fun l hl => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1, hO0.1 l b (Finset.mem_filter.mp hl).2.1⟩
                  have hcle : ((LeavesW.erase l0).filter (fun l => dA l b)).card ≤ 1 := by
                    have := Finset.card_le_card hsub1; rw [hEach_eq1 b (hDR_sub hb)] at this; exact this
                  have hcomp_le : (comp0 b).card ≤ 2 := by
                    rw [hcomp_eq b hb]; have := Finset.card_insert_le b ((LeavesW.erase l0).filter (fun l => dA l b)); omega
                  have hb_not_lv : b ∉ lv0 b := fun h => by
                    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hb).2.1; exact (Finset.mem_filter.mp h).2 x hx
                  have hlv_le : (lv0 b).card ≤ (comp0 b).card - 1 := by
                    have hsub2 : lv0 b ⊆ (comp0 b).erase b := fun w hw =>
                      Finset.mem_erase.mpr ⟨fun h => hb_not_lv (h ▸ hw), (Finset.mem_filter.mp hw).1⟩
                    have := Finset.card_le_card hsub2
                    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩)] at this; exact this
                  omega
              _ = DR.card := by simp
              _ ≤ (IntW.erase c).card := Finset.card_le_card hDR_sub
              _ = 3 := by rw [Finset.card_erase_of_mem hcI, hInt_card]
          · -- Subcase 2: c has NO leaf neighbor! Pick any b1 ∈ IntW.erase c -> at root r1 = b1,
            -- UpAdj(D0, b1) consists ONLY of edges c -> b for b ∈ (IntW.erase c).erase b1 (2 edges, 1 component of size 3)!
            push Not at hc_leaf
            have hne_er : (IntW.erase c).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hcI, hInt_card]; omega)
            obtain ⟨b1, hb1⟩ := hne_er
            refine ⟨b1, Or.inr ?_⟩
            let uA : W → W → Prop := fun x y => D0.Adj y x ∧ T.dist b1 y < T.dist b1 x
            -- Characterize uA x y (i.e. D0.Adj y x ∧ T.dist b1 y < T.dist b1 x): ONLY y = c and x ∈ (IntW.erase c).erase b1!
            have huA_char : ∀ x y : W, uA x y → y = c ∧ x ∈ (IntW.erase c).erase b1 := by
              intro x y hxy
              have hTxy : T.Adj y x := hO0.1 y x hxy.1
              -- Can y be in IntW.erase c? NO, those are sinks (∀ z, ¬ D0.Adj y z)!
              -- Can y be in LeavesW? Then its unique T-neighbor is x ∈ IntW.erase c (since c has no leaf)!
              -- Wait: if y ∈ LeavesW, its unique neighbor is x ∈ IntW.erase c.
              -- Then T.dist b1 y = T.dist b1 x + 1 > T.dist b1 x (unless x = b1? Even if x = b1, dist b1 b1 = 0 < 1 = dist b1 y!),
              -- contradicting T.dist b1 y < T.dist b1 x!
              have hy_not_er : y ∉ IntW.erase c := fun hy => (hb_snk y hy).2 x hxy.1
              have hy_not_L : y ∉ LeavesW := by
                intro hyL
                obtain ⟨p, ⟨hpI, hTyp⟩, _⟩ := hleaf_to_I y hyL
                have hdeg1 : (Finset.univ.filter (fun z : W => T.Adj y z)).card = 1 := by
                  rw [← hdeg_eq]; exact (Finset.mem_filter.mp hyL).2
                have hxp : x = p := Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj y z)).card ≤ 1) _
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTyp⟩)
                subst x
                have hy_ne_b1 : y ≠ b1 := fun h => by
                  rw [h] at hyL; have hb1I := (Finset.mem_erase.mp hb1).2
                  rw [hInt_comp, Finset.mem_sdiff] at hb1I; exact hb1I.2 hyL
                obtain ⟨q, ⟨hTqy, hdist_q⟩, _⟩ := tree_exists_unique_parent hT b1 y hy_ne_b1
                have hqx : q = p := Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => T.Adj y z)).card ≤ 1) _
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTqy.symm⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy⟩)
                subst q; have := hxy.2; omega
              have hyI : y ∈ IntW := by rw [hInt_comp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy_not_L⟩
              have hyc : y = c := by_contra (fun h => hy_not_er (Finset.mem_erase.mpr ⟨h, hyI⟩))
              subst y
              -- Now T.Adj c x and T.dist b1 c < T.dist b1 x, so x ≠ b1 (since dist b1 b1 = 0) and x ∉ LeavesW (hc_leaf)!
              have hxne_b1 : x ≠ b1 := fun h => by subst h; have := hxy.2; rw [SimpleGraph.dist_self] at this; omega
              have hxne_c : x ≠ c := (T.ne_of_adj hTxy).symm
              have hxI : x ∈ IntW := by
                rw [hInt_comp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxL => hc_leaf x hxL hTxy.symm⟩
              exact ⟨rfl, Finset.mem_erase.mpr ⟨hxne_b1, Finset.mem_erase.mpr ⟨hxne_c, hxI⟩⟩⟩
            let UR := Finset.univ.filter (fun c0 : W => (∃ x, uA x c0) ∧ ∀ p, ¬ uA c0 p)
            let compU0 : W → Finset W := fun c0 => Finset.univ.filter (fun w => Relation.ReflTransGen uA w c0)
            let lvU0 : W → Finset W := fun c0 => (compU0 c0).filter (fun w => ∀ x, ¬ uA x w)
            have hUR_sub : UR ⊆ {c} := fun c0 hc0 => by
              obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hc0).2.1
              exact Finset.mem_singleton.mpr (huA_char x c0 hx).1
            have hcompU_sub : compU0 c ⊆ insert c ((IntW.erase c).erase b1) := by
              intro w hw
              rcases Relation.ReflTransGen.cases_head (Finset.mem_filter.mp hw).2 with rfl | ⟨z, hwz, _⟩
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (huA_char w z hwz).2
            have hcompU_le : (compU0 c).card ≤ 3 := by
              have h1 := Finset.card_le_card hcompU_sub
              have h2 := Finset.card_insert_le c ((IntW.erase c).erase b1)
              rw [Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem hcI, hInt_card] at h2; omega
            calc ∑ c0 ∈ UR, ((compU0 c0).card + (lvU0 c0).card - 2)
                ≤ ∑ _c0 ∈ UR, 3 := by
                  refine Finset.sum_le_sum (fun c0 hc0 => ?_)
                  have hc0_eq : c0 = c := Finset.mem_singleton.mp (hUR_sub hc0)
                  subst c0
                  have hlv_le2 : (lvU0 c).card ≤ 2 := by
                    have hsub : lvU0 c ⊆ (IntW.erase c).erase b1 := fun w hw => by
                      have hw' := Finset.mem_filter.mp hw
                      rcases Finset.mem_insert.mp (hcompU_sub hw'.1) with rfl | hmem
                      · obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hc0).2.1; exact absurd hx (hw'.2 x)
                      · exact hmem
                    have := Finset.card_le_card hsub
                    rw [Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem hcI, hInt_card] at this; exact this
                  omega
              _ = UR.card * 3 := by simp
              _ ≤ 1 * 3 := Nat.mul_le_mul_right 3 (by have := Finset.card_le_card hUR_sub; simpa using this)
              _ = 3 := by omega
        -- Apply hK13_core to D (if c is source) or Drev (if c is sink)!
        rcases hAnti c with hc_src | hc_snk
        · exact dross_havet_embed_of_exists_gamma_le (by omega) D hW hT hO G hG 3 (by omega)
            (hK13_core D hO hAnti hc_src)
        · let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
          have hOrev : Drev.IsOrientation T := ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
          have hAnti_rev : ∀ w : W, (∀ x : W, ¬ Drev.Adj x w) ∨ (∀ x : W, ¬ Drev.Adj w x) :=
            fun w => (hAnti w).symm
          let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
          have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun u v huv => hG.2 v u huv.symm⟩
          have hleaves_eq : (Finset.univ.filter (fun w : W =>
              (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)).card = 1)).card = LeavesW.card := by
            congr 1; ext w; simp only [LeavesW, Finset.mem_filter, Finset.mem_univ, true_and]
            have : Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w) =
                Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) := by
              ext z; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]; exact or_comm
            rw [this]
          obtain ⟨⟨fn, hfn⟩, hfinj⟩ := dross_havet_embed_of_exists_gamma_le (by omega) Drev hW hT hOrev Grev hGrev 3
            (by rw [hleaves_eq]; omega) (hK13_core Drev hOrev hAnti_rev hc_snk)
          exact ⟨⟨fn, fun hxy => hfn hxy⟩, hfinj⟩
      · -- Case 2: Every vertex in IntW has internal degree in {1, 2}! So T[IntW] is a P_4!
        push Not at hstar
        have hdegI_le2 : ∀ x ∈ IntW, (IntW.filter (fun y => T.Adj x y)).card ≤ 2 := by
          intro x hx
          have hsub : IntW.filter (fun y => T.Adj x y) ⊆ IntW.erase x := fun y hy =>
            Finset.mem_erase.mpr ⟨(T.ne_of_adj (Finset.mem_filter.mp hy).2).symm, (Finset.mem_filter.mp hy).1⟩
          have hle3 : (IntW.filter (fun y => T.Adj x y)).card ≤ 3 := by
            have := Finset.card_le_card hsub; rw [Finset.card_erase_of_mem hx, hInt_card] at this; exact this
          have hne3 := hstar x hx
          omega
        -- Find a vertex x1 ∈ IntW of internal degree 1 (take furthest pair in IntW from an arbitrary x0 ∈ IntW)!
        obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < IntW.card)
        obtain ⟨x1, hx1I, hx1_max⟩ := Finset.exists_max_image IntW (T.dist x0) ⟨x0, hx0⟩
        have hx1_ne_x0 : x1 ≠ x0 := by
          intro hEq
          have hne : (IntW.erase x0).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx0, hInt_card]; omega)
          obtain ⟨y, hy⟩ := hne
          have hle := hx1_max y (Finset.mem_erase.mp hy).2
          rw [hEq, SimpleGraph.dist_self] at hle
          have h0 : T.dist x0 y = 0 := by omega
          exact (Finset.mem_erase.mp hy).1 ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
            (not_not.mpr (hT.connected x0 y))).symm
        obtain ⟨x2, ⟨hTx2x1, hdist_x2⟩, hx2u⟩ := tree_exists_unique_parent hT x0 x1 hx1_ne_x0
        have hx2I : x2 ∈ IntW := by
          obtain ⟨p, hp, hplen⟩ := (hT.connected x0 x1).exists_path_of_dist
          -- x2 is the predecessor of x1 on the shortest path x0 ~> x1!
          obtain ⟨q, hqp, hqlen⟩ := (hT.connected x0 x2).exists_path_of_dist
          have hx1_not_q : x1 ∉ q.support := fun hx1q => by
            have h1 : T.dist x0 x1 ≤ (q.takeUntil x1 hx1q).length := SimpleGraph.dist_le _
            have h2 : (q.takeUntil x1 hx1q).length ≤ q.length := SimpleGraph.Walk.length_takeUntil_le_length q hx1q
            omega
          let w1 : T.Walk x1 x0 := SimpleGraph.Walk.cons hTx2x1.symm q.reverse
          have hw1p : w1.IsPath := SimpleGraph.Walk.IsPath.cons hqp.reverse (by simpa using hx1_not_q)
          exact hInt_path x1 hx1I x0 hx0 w1 hw1p x2
            (by simp [w1, SimpleGraph.Walk.support_cons])
        have hx1_deg1 : IntW.filter (fun y => T.Adj x1 y) = {x2} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hyI, hTx1y⟩
            have hle := hx1_max y hyI
            rcases hT.dist_eq_dist_add_one_of_adj x0 hTx1y with h1 | h2
            · exact hx2u y ⟨hTx1y.symm, by omega⟩
            · omega
          · rintro rfl; exact ⟨hx2I, hTx2x1.symm⟩
        have hx12 : x1 ≠ x2 := (T.ne_of_adj hTx2x1).symm
        -- x2 must have a second neighbor x3 ∈ IntW \ {x1} (else {x1, x2} is disconnected from the other 2 vertices of IntW)!
        have hex_x3 : ∃ x3 ∈ IntW, x3 ≠ x1 ∧ T.Adj x2 x3 := by
          have hrem : ((IntW.erase x1).erase x2).Nonempty := Finset.card_pos.mp (by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx12.symm, hx2I⟩), Finset.card_erase_of_mem hx1I, hInt_card]; omega)
          obtain ⟨y, hy⟩ := hrem
          have hyne2 : y ≠ x2 := (Finset.mem_erase.mp hy).1
          have hyne1 : y ≠ x1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
          have hyI : y ∈ IntW := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).2
          obtain ⟨p, hp, _⟩ := (hT.connected x2 y).exists_path_of_dist
          cases p with
          | nil => exact absurd rfl hyne2.symm
          | @cons _ z _ hTx2z p' =>
            have hzI : z ∈ IntW := hInt_path x2 hx2I y hyI (SimpleGraph.Walk.cons hTx2z p') hp z
              (by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
            have hzne1 : z ≠ x1 := by
              rintro rfl
              cases p' with
              | nil => exact hyne1 rfl
              | @cons _ z2 _ hTx1z2 p'' =>
                have hz2I : z2 ∈ IntW := hInt_path x2 hx2I y hyI (SimpleGraph.Walk.cons hTx2z (SimpleGraph.Walk.cons hTx1z2 p'')) hp z2
                  (by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
                have hz2_eq : z2 = x2 := Finset.mem_singleton.mp (hx1_deg1 ▸ Finset.mem_filter.mpr ⟨hz2I, hTx1z2⟩)
                subst z2
                have hnd := hp.support_nodup
                simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons,
                  SimpleGraph.Walk.start_mem_support, or_true, not_true_eq_false, false_and] at hnd
            exact ⟨z, hzI, hzne1, hTx2z⟩
        obtain ⟨x3, hx3I, hx31, hTx2x3⟩ := hex_x3
        have hx23 : x2 ≠ x3 := T.ne_of_adj hTx2x3
        -- Since deg_I(x2) <= 2, x2's ONLY neighbors in IntW are {x1, x3}!
        have hx2_nbs : IntW.filter (fun y => T.Adj x2 y) = {x1, x3} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hx1I, hTx2x1⟩
            · exact Finset.mem_filter.mpr ⟨hx3I, hTx2x3⟩
          · rw [Finset.card_pair hx31.symm]; exact hdegI_le2 x2 hx2I
        -- Pick the 4th vertex x4 ∈ IntW \ {x1, x2, x3}! Its neighbor in IntW MUST be x3!
        have hrem4 : (((IntW.erase x1).erase x2).erase x3).Nonempty := Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx23.symm, Finset.mem_erase.mpr ⟨hx31, hx3I⟩⟩),
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx12.symm, hx2I⟩),
            Finset.card_erase_of_mem hx1I, hInt_card]; omega)
        obtain ⟨x4, hx4⟩ := hrem4
        have hx43 : x4 ≠ x3 := (Finset.mem_erase.mp hx4).1
        have hx42 : x4 ≠ x2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx4).2).1
        have hx41 : x4 ≠ x1 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx4).2).2).1
        have hx4I : x4 ∈ IntW := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx4).2).2).2
        have hInt_4 : IntW = {x1, x2, x3, x4} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl | rfl <;> assumption
          · rw [hInt_card, Finset.card_insert_of_notMem (by simp [hx12, hx31.symm, hx41.symm]),
              Finset.card_insert_of_notMem (by simp [hx23, hx42.symm]),
              Finset.card_pair hx43.symm]
        have hTx3x4 : T.Adj x3 x4 := by
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by have := hdegI_pos x4 hx4I; omega :
            0 < (IntW.filter (fun y => T.Adj x4 y)).card)
          have hzI := (Finset.mem_filter.mp hz).1
          have hTx4z := (Finset.mem_filter.mp hz).2
          rw [hInt_4] at hzI
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzI
          rcases hzI with rfl | rfl | rfl | rfl
          · have h1 := Finset.mem_singleton.mp (hx1_deg1 ▸ Finset.mem_filter.mpr ⟨hx4I, hTx4z.symm⟩)
            exact absurd h1 hx42
          · have h2 : x4 ∈ ({x1, x3} : Finset W) := hx2_nbs ▸ Finset.mem_filter.mpr ⟨hx4I, hTx4z.symm⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at h2
            rcases h2 with h | h; exact absurd h hx41; exact absurd h hx43
          · exact hTx4z.symm
          · exact absurd rfl (T.ne_of_adj hTx4z)
        -- Now D is antidirected on the path x1 - x2 - x3 - x4, so either x1 -> x2 <- x3 -> x4 or x4 -> x3 <- x2 -> x1!
        rcases adj_or_rev_of_isOrientation hO hTx2x1.symm with h12 | h21
        · -- x1 -> x2, so x2 is a sink -> x3 -> x2, so x3 is a source -> x3 -> x4!
          have hx2_snk := (hAnti x2).resolve_left (fun h => h x1 h12)
          have h32 : D.Adj x3 x2 := (adj_or_rev_of_isOrientation hO hTx2x3.symm).resolve_right (hx2_snk x3)
          have hx3_src := (hAnti x3).resolve_right (fun h => h x2 h32)
          have h34 : D.Adj x3 x4 := (adj_or_rev_of_isOrientation hO hTx3x4).resolve_right (hx3_src x4)
          exact embeds_antidirected_P4_internal (by omega) D hW hT hO hAnti x1 x2 x3 x4
            ⟨hx12, hx31.symm, hx41.symm, hx23, hx42.symm, hx43.symm⟩ ⟨h12, h32, h34⟩ hInt_4 G hV hG hNoSrc hNoSnk
        · -- x2 -> x1, so x2 is a source -> x2 -> x3, so x3 is a sink -> x4 -> x3!
          have hx2_src := (hAnti x2).resolve_right (fun h => h x1 h21)
          have h23 : D.Adj x2 x3 := (adj_or_rev_of_isOrientation hO hTx2x3).resolve_right (hx2_src x3)
          have hx3_snk := (hAnti x3).resolve_left (fun h => h x2 h23)
          have h43 : D.Adj x4 x3 := (adj_or_rev_of_isOrientation hO hTx3x4.symm).resolve_right (hx3_snk x4)
          have hInt_4' : IntW = {x4, x3, x2, x1} := by
            rw [hInt_4]; ext y; simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (h | h | h | h)
              · exact Or.inr (Or.inr (Or.inr h))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
            · rintro (h | h | h | h)
              · exact Or.inr (Or.inr (Or.inr h))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
          exact embeds_antidirected_P4_internal (by omega) D hW hT hO hAnti x4 x3 x2 x1
            ⟨hx43, hx42, hx41, hx23.symm, hx31, hx12.symm⟩ ⟨h43, h23, h21⟩ hInt_4' G hV hG hNoSrc hNoSnk

end Stage2

end ProofWork.DrossHavet

theorem OMA.solution : OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1.H1 := by
  intro n hn W _ _ D _ hW hTree _ hInt hk V _ _ G _ hV hG h2S
  have hNoSrc : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≤ 2 * n - 4 := by
    intro v
    have hv_ne_univ : ((∅ : Finset V) ∪ {v}) ≠ Finset.univ := by
      intro hEq
      have hc := congrArg Finset.card hEq
      rw [Finset.empty_union, Finset.card_singleton, Finset.card_univ, hV] at hc
      omega
    obtain ⟨u, hu, w, _, hw_not, hGwu⟩ := h2S ∅ (by simp) {v} (Finset.disjoint_empty_left _)
      (Finset.singleton_nonempty v) hv_ne_univ
    have huv : u = v := Finset.mem_singleton.mp hu
    subst u
    have hwv : w ≠ v := fun h => hw_not (Finset.mem_singleton.mpr h)
    have hsub : Finset.univ.filter (fun z : V => G.Adj v z) ⊆ (Finset.univ.erase v).erase w := by
      intro z hz
      have hGvz : G.Adj v z := (Finset.mem_filter.mp hz).2
      refine Finset.mem_erase.mpr ⟨fun hzw => ?_, Finset.mem_erase.mpr ⟨fun hzv => hG.1 v (hzv ▸ hGvz), Finset.mem_univ z⟩⟩
      exact (hG.2 w v hwv).mp hGwu (hzw ▸ hGvz)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩),
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV] at hc
    omega
  have hNoSnk : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card ≤ 2 * n - 4 := by
    intro v
    have hV1_ne : (Finset.univ.erase v).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]; omega)
    have hV1_not_univ : ((∅ : Finset V) ∪ Finset.univ.erase v) ≠ Finset.univ := by
      intro hEq
      have hv_mem : v ∈ (∅ : Finset V) ∪ Finset.univ.erase v := by rw [hEq]; exact Finset.mem_univ v
      rw [Finset.empty_union] at hv_mem
      exact (Finset.mem_erase.mp hv_mem).1 rfl
    obtain ⟨u, hu, w, _, hw_not, hGwu⟩ := h2S ∅ (by simp) (Finset.univ.erase v)
      (Finset.disjoint_empty_left _) hV1_ne hV1_not_univ
    have huv : u ≠ v := (Finset.mem_erase.mp hu).1
    have hwv : w = v := by
      by_contra hne
      exact hw_not (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w⟩)
    subst w
    have hsub : Finset.univ.filter (fun z : V => G.Adj z v) ⊆ (Finset.univ.erase v).erase u := by
      intro z hz
      have hGzv : G.Adj z v := (Finset.mem_filter.mp hz).2
      refine Finset.mem_erase.mpr ⟨fun hzu => ?_, Finset.mem_erase.mpr ⟨fun hzv => hG.1 v (hzv ▸ hGzv), Finset.mem_univ z⟩⟩
      exact (hG.2 v u huv.symm).mp hGwu (hzu ▸ hGzv)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩),
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV] at hc
    omega
  exact ProofWork.DrossHavet.embeds_R1_H1 hn D hW hTree G hV hG hNoSrc hNoSnk hInt hk
