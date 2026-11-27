import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1

/-!
Thomason's rotation argument with an exceptional initial edge.  The rotation
and walk-indexing code is adapted from the repository's proof of
LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1.H2 by
luciusacarr.  Here we use every Hamilton path with the chosen initial edge.
-/

namespace OMA.SheehanEdgeParity
open SimpleGraph Finset

private def rotIdx (n k j : ℕ) : ℕ :=
  if j ≤ k then j else n + k - j

private lemma rotIdx_lt {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) : rotIdx n k j < n := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_invol {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) :
    rotIdx n k (rotIdx n k j) = j := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_eq_iff {n k j₁ j₂ : ℕ} (hk : k + 2 < n) (h1 : j₁ < n) (h2 : j₂ < n) :
    rotIdx n k j₁ = rotIdx n k j₂ ↔ j₁ = j₂ := by
  constructor
  · intro h
    have := congrArg (rotIdx n k) h
    rwa [rotIdx_invol hk h1, rotIdx_invol hk h2] at this
  · rintro rfl; rfl

private def rotFin {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) : Fin n → Fin n :=
  fun j => P ⟨rotIdx n k j.val, rotIdx_lt hk j.isLt⟩

private lemma rotFin_invol {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) :
    rotFin (rotFin P k hk) k hk = P := by
  ext ⟨j, hj⟩
  simp only [rotFin, rotIdx_invol hk hj]

private lemma rotFin_inj {n : ℕ} {P : Fin n → Fin n} (hP : Function.Injective P)
    {k : ℕ} (hk : k + 2 < n) : Function.Injective (rotFin P k hk) := by
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ h
  have h1 := hP h
  simp only [Fin.mk.injEq, rotIdx_eq_iff hk hj₁ hj₂] at h1
  exact Fin.ext h1

private lemma walkOfChain_exists {V : Type*} (G : SimpleGraph V) (l : List V) (hl : l ≠ [])
    (hadj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1]) :
    ∃ p : G.Walk (l.head hl) (l.getLast hl),
      p.support = l ∧ p.length + 1 = l.length ∧
      ∀ e, e ∈ p.edges ↔ ∃ i : ℕ, ∃ (hi : i + 1 < l.length), e = s(l[i], l[i + 1]) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    cases t with
    | nil =>
      refine ⟨Walk.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | cons b t' =>
      have ht_ne : b :: t' ≠ [] := List.cons_ne_nil _ _
      have hadj_t : ∀ i : ℕ, (hi : i + 1 < (b :: t').length) →
          G.Adj (b :: t')[i] (b :: t')[i + 1] := by
        intro i hi
        have h1 := hadj (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa only [List.getElem_cons_succ] using h1
      obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := ih ht_ne hadj_t
      have hab : G.Adj a ((b :: t').head ht_ne) := hadj 0 (by simp)
      refine ⟨(Walk.cons hab q).copy (List.head_cons (a := a) (l := b :: t') (h := hl)).symm
          (List.getLast_cons ht_ne).symm, ?_, ?_, ?_⟩
      · simp only [Walk.support_copy, Walk.support_cons, hq_sup]
      · rw [Walk.length_copy, Walk.length_cons, hq_len]
        rfl
      · intro e
        simp only [Walk.edges_copy, Walk.edges_cons, List.mem_cons, hq_edges]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨0, by simp, rfl⟩
          · exact ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega, by simp⟩
        · rintro ⟨i, hi, rfl⟩
          cases i with
          | zero => left; rfl
          | succ i' =>
            right
            exact ⟨i', by simp only [List.length_cons] at hi ⊢; omega, by simp⟩

private lemma cycle_indexing {V : Type} [Fintype V] [DecidableEq V] [NeZero (Fintype.card V)]
    (G : SimpleGraph V) (v : V) (c : G.Walk v v)
    (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c) :
    3 ≤ Fintype.card V ∧
    ∃ (e : Fin (Fintype.card V) ≃ V),
      (∀ i : Fin (Fintype.card V), G.Adj (e i) (e (i + 1))) ∧
      (∀ x y : V, s(x, y) ∈ c.edges ↔
        ∃ i : Fin (Fintype.card V), s(x, y) = s(e i, e (i + 1))) := by
  have hcyc : c.IsCycle := hc.1
  have hham : ∀ w, w ∈ c.support := hc.2
  have h3 : 3 ≤ c.length := hcyc.three_le_length
  have hnodup : c.support.dropLast.Nodup := hcyc.nodup_dropLast_support
  have hlen_sup : c.support.length = c.length + 1 := Walk.length_support c
  have hlen_dl : c.support.dropLast.length = c.length := by
    rw [List.length_dropLast, hlen_sup]; omega
  have hmem_dl : ∀ w : V, w ∈ c.support.dropLast := by
    intro w
    have hw := hham w
    have hne : c.support ≠ [] := Walk.support_ne_nil c
    have hsplit : c.support = c.support.dropLast ++ [c.support.getLast hne] :=
      (List.dropLast_append_getLast hne).symm
    rw [hsplit, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hw
    · have hlast : c.support.getLast hne = v := Walk.getLast_support c
      have hpos : 0 < c.support.dropLast.length := by rw [hlen_dl]; omega
      have h0 : c.support.dropLast[0] = v := by
        rw [List.getElem_dropLast (by omega), ← List.head_eq_getElem_zero hne, Walk.head_support c]
      have hmem : v ∈ c.support.dropLast :=
        Eq.subst (motive := fun x => x ∈ c.support.dropLast) h0 (List.getElem_mem hpos)
      rw [hlast]
      exact hmem
  have hcard : c.length = Fintype.card V := by
    have h1 : c.support.dropLast.toFinset = Finset.univ := by
      ext w; simp [hmem_dl w]
    have h2 := congrArg Finset.card h1
    rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ, hlen_dl] at h2
    exact h2
  have hn3 : 3 ≤ Fintype.card V := hcard ▸ h3
  have hbij : Function.Bijective (fun i : Fin (Fintype.card V) =>
      c.support.dropLast[i.val]'(by rw [hlen_dl, hcard]; exact i.isLt)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j hij => ?_, by simp⟩
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij)
  let e : Fin (Fintype.card V) ≃ V := Equiv.ofBijective _ hbij
  have he_def : ∀ i : Fin (Fintype.card V),
      e i = c.support.dropLast[i.val]'(by rw [hlen_dl, hcard]; exact i.isLt) :=
    fun _ => rfl
  have hgetVert_eq : ∀ i : ℕ, (hi : i < Fintype.card V) →
      c.getVert i = e ⟨i, hi⟩ := by
    intro i hi
    rw [he_def, Walk.getVert_eq_support_getElem c (by rw [hcard]; omega),
      List.getElem_dropLast]
  have hlast_eq : c.getVert (Fintype.card V) = e ⟨0, by omega⟩ := by
    calc
      c.getVert (Fintype.card V) = c.getVert c.length := by rw [hcard]
      _ = v := Walk.getVert_length c
      _ = c.support.head (Walk.support_ne_nil c) := (Walk.head_support c).symm
      _ = c.support[0]'(by rw [hlen_sup]; omega) := List.head_eq_getElem_zero _
      _ = c.support.dropLast[0]'(by rw [hlen_dl]; omega) := (List.getElem_dropLast _).symm
      _ = e ⟨0, by omega⟩ := (he_def ⟨0, by omega⟩).symm
  have hfin_last : ∀ i : Fin (Fintype.card V), i.val + 1 = Fintype.card V →
      i + 1 = ⟨0, by omega⟩ := fun i h => by
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < Fintype.card V), h]
  have hfin_lt : ∀ (i : Fin (Fintype.card V)) (hlt : i.val + 1 < Fintype.card V),
      i + 1 = ⟨i.val + 1, hlt⟩ := fun i hlt => by
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < Fintype.card V),
      Nat.mod_eq_of_lt hlt]
  have hadj : ∀ i : Fin (Fintype.card V), G.Adj (e i) (e (i + 1)) := by
    intro i
    have hi_len : i.val < c.length := by rw [hcard]; exact i.isLt
    have hadj_i := c.adj_getVert_succ hi_len
    rw [hgetVert_eq i.val i.isLt] at hadj_i
    by_cases hlast : i.val + 1 = Fintype.card V
    · have hi1 := hfin_last i hlast
      have hgv : c.getVert (i.val + 1) = e (i + 1) := by
        rw [hlast, hi1]; exact hlast_eq
      rwa [hgv] at hadj_i
    · have hi_lt : i.val + 1 < Fintype.card V := by omega
      have hi1 := hfin_lt i hi_lt
      have hgv : c.getVert (i.val + 1) = e (i + 1) := by
        rw [hi1]; exact hgetVert_eq (i.val + 1) hi_lt
      rwa [hgv] at hadj_i
  have hedges : ∀ x y : V, s(x, y) ∈ c.edges ↔
      ∃ i : Fin (Fintype.card V), s(x, y) = s(e i, e (i + 1)) := by
    intro x y
    rw [Walk.mk_mem_edges_iff_exists]
    constructor
    · rintro ⟨i, hi, hs⟩
      have hiV : i < Fintype.card V := hcard ▸ hi
      refine ⟨⟨i, hiV⟩, ?_⟩
      rw [← hs, hgetVert_eq i hiV]
      by_cases hlast : i + 1 = Fintype.card V
      · have hi1 := hfin_last ⟨i, hiV⟩ hlast
        rw [hlast, hi1, hlast_eq]
      · have hi_lt : i + 1 < Fintype.card V := by omega
        have hi1 := hfin_lt ⟨i, hiV⟩ hi_lt
        rw [hi1, hgetVert_eq (i + 1) hi_lt]
    · rintro ⟨i, hs⟩
      refine ⟨i.val, by rw [hcard]; exact i.isLt, ?_⟩
      rw [hs, hgetVert_eq i.val i.isLt]
      by_cases hlast : i.val + 1 = Fintype.card V
      · have hi1 := hfin_last i hlast
        rw [hlast, hi1, hlast_eq]
      · have hi_lt : i.val + 1 < Fintype.card V := by omega
        have hi1 := hfin_lt i hi_lt
        rw [hi1, hgetVert_eq (i.val + 1) hi_lt]
  exact ⟨hn3, e, hadj, hedges⟩
/-- With the starting edge fixed, a path has odd rotation degree exactly
when its endpoint is adjacent to its start. The endpoints of the starting
edge never occur as the terminal vertex. -/
private lemma second_ordering (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ i : Fin n, G.Adj i (i + 1))
    (oddAway : ∀ z : Fin n, z ≠ 0 → z ≠ 1 → G.degree z % 2 = 1) :
    ∃ (p : Fin n → Fin n), Function.Injective p ∧
      p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 1 ∧
      (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (p ⟨i, by omega⟩) (p ⟨i + 1, hi⟩)) ∧
      G.Adj (p ⟨n - 1, by omega⟩) 0 ∧
      ∃ i : ℕ, ∃ (hi : i < n), p ⟨i, hi⟩ ≠ ⟨i, hi⟩ := by
  classical
  let IsGood (P : Fin n → Fin n) : Prop :=
    Function.Injective P ∧
    P ⟨0, by omega⟩ = 0 ∧
    P ⟨1, by omega⟩ = 1 ∧
    (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (P ⟨i, by omega⟩) (P ⟨i + 1, hi⟩))
  let LVert := { P : Fin n → Fin n // IsGood P }
  let LAdj : LVert → LVert → Prop := fun P Q =>
    ∃ k : ℕ, ∃ hk : k + 2 < n, 1 ≤ k ∧
      G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) ∧
      Q.1 = rotFin P.1 k hk
  have hL_symm : ∀ P Q, LAdj P Q → LAdj Q P := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ ⟨k, hk, hk1, hadj, hQ_eq⟩
    dsimp only at hadj hQ_eq
    refine ⟨k, hk, hk1, ?_, ?_⟩
    · have hQ_n1 : Q ⟨n - 1, by omega⟩ = P ⟨k + 1, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k (n - 1), rotIdx_lt hk (by omega : n - 1 < n)⟩ : Fin n) =
            ⟨k + 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (n - 1 ≤ k) by omega, ↓reduceIte]; omega
        rw [hidx]
      have hQ_k : Q ⟨k, by omega⟩ = P ⟨k, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) =
            ⟨k, by omega⟩ := by
          ext; simp only [rotIdx, le_refl, ↓reduceIte]
        rw [hidx]
      change G.Adj (Q ⟨n - 1, by omega⟩) (Q ⟨k, by omega⟩)
      rw [hQ_n1, hQ_k]
      exact (hP.2.2.2 k (by omega)).symm
    · exact (rotFin_invol P k hk).symm.trans (congrArg (fun f => rotFin f k hk) hQ_eq.symm)
  have hL_irrefl : ∀ P, ¬ LAdj P P := by
    rintro ⟨P, hP⟩ ⟨k, hk, _, _, hP_eq⟩
    dsimp only at hP_eq
    have hv := congrArg (fun f => f ⟨k + 1, by omega⟩) hP_eq
    have hidx : (⟨rotIdx n k (k + 1), rotIdx_lt hk (by omega : k + 1 < n)⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := by
      ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
    have hrot : rotFin P k hk ⟨k + 1, by omega⟩ = P ⟨n - 1, by omega⟩ := by
      dsimp only [rotFin]; rw [hidx]
    rw [hrot] at hv
    have hval := congrArg Fin.val (hP.1 hv)
    simp at hval
    omega
  let L : SimpleGraph LVert := ⟨LAdj, ⟨fun _ _ => hL_symm _ _⟩, ⟨hL_irrefl⟩⟩
  have hrot_good : ∀ (P : LVert) (k : ℕ) (hk : k + 2 < n), 1 ≤ k →
      G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) →
      IsGood (rotFin P.1 k hk) := by
    intro ⟨P, hP⟩ k hk hk1 hadj
    dsimp only at hadj
    refine ⟨rotFin_inj hP.1 hk, ?_, ?_, ?_⟩
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 0, rotIdx_lt hk (by omega : 0 < n)⟩ : Fin n) = ⟨0, by omega⟩ := by
        ext; simp [rotIdx]
      rw [hidx]; exact hP.2.1
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 1, rotIdx_lt hk (by omega : 1 < n)⟩ : Fin n) = ⟨1, by omega⟩ := by
        ext; simp [rotIdx, hk1]
      rw [hidx]; exact hP.2.2.1
    · intro i hi
      dsimp only [rotFin]
      by_cases hik : i + 1 ≤ k
      · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp [rotIdx, show i ≤ k by omega]
        have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp [rotIdx, hik]
        rw [hidx1, hidx2]
        exact hP.2.2.2 i hi
      · by_cases hik0 : i ≤ k
        · have hik_eq : i = k := by omega
          subst i
          have hidx1 : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) = ⟨k, by omega⟩ := by
            ext; simp [rotIdx]
          have hidx2 : (⟨rotIdx n k (k + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
            ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
          rw [hidx1, hidx2]
          exact hadj.symm
        · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) =
              ⟨n + k - i, by omega⟩ := by
            ext; simp [rotIdx, hik0]
          have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) =
              ⟨n + k - (i + 1), by omega⟩ := by
            ext; simp [rotIdx, hik]
          rw [hidx1, hidx2]
          have hm_lt : n + k - (i + 1) + 1 < n := by omega
          have hchain := (hP.2.2.2 (n + k - (i + 1)) hm_lt).symm
          convert hchain using 2 <;> ext <;> dsimp <;> omega
  have hP0_good : IsGood (fun i : Fin n => i) := by
    refine ⟨Function.injective_id, rfl, by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)], ?_⟩
    intro i hi
    have hnext : (⟨i, by omega⟩ : Fin n) + 1 = ⟨i + 1, hi⟩ := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hi]
    exact hnext ▸ hc ⟨i, by omega⟩
  let P0 : LVert := ⟨fun i : Fin n => i, hP0_good⟩
  have hdeg_eq : ∀ P : LVert, L.degree P =
      (Finset.univ.filter fun k : Fin n =>
        1 ≤ k.val ∧ k.val < n - 2 ∧ G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card := by
    intro P
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    have hmap :
        (Finset.univ.filter fun k : Fin n =>
          1 ≤ k.val ∧ k.val < n - 2 ∧ G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card =
        (L.neighborSet P).toFinset.card := by
      have inj_lt : ∀ (a b : Fin n), 1 ≤ a.val → ∀ (hlt : a.val < b.val) (hb2 : b.val + 2 < n),
          rotFin P.1 a.val (lt_trans (Nat.add_lt_add_right hlt 2) hb2) ≠
            rotFin P.1 b.val hb2 := by
        intro a b _ hlt hb2 heq
        have ha2 : a.val + 2 < n := lt_trans (Nat.add_lt_add_right hlt 2) hb2
        have hv := congrArg (fun f => f ⟨a.val + 1, by omega⟩) heq
        have hidx1 : (⟨rotIdx n a.val (a.val + 1), rotIdx_lt ha2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (a.val + 1 ≤ a.val) by omega, ↓reduceIte]; omega
        have hidx2 : (⟨rotIdx n b.val (a.val + 1), rotIdx_lt hb2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨a.val + 1, by omega⟩ := by
          ext; simp only [rotIdx, show a.val + 1 ≤ b.val by omega, ↓reduceIte]
        have h1 : rotFin P.1 a.val ha2 ⟨a.val + 1, by omega⟩ = P.1 ⟨n - 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx1]
        have h2 : rotFin P.1 b.val hb2 ⟨a.val + 1, by omega⟩ = P.1 ⟨a.val + 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx2]
        rw [h1, h2] at hv
        have hval := congrArg Fin.val (P.2.1 hv)
        simp at hval; omega
      refine Finset.card_bij
        (fun k hk =>
          have hkm := (mem_filter.mp hk).2
          have hk2 : k.val + 2 < n := by omega
          ⟨rotFin P.1 k.val hk2, hrot_good P k.val hk2 hkm.1 hkm.2.2⟩)
        ?_ ?_ ?_
      · intro k hk
        have hkm := (mem_filter.mp hk).2
        rw [Set.mem_toFinset, mem_neighborSet]
        exact ⟨k.val, by omega, hkm.1, hkm.2.2, rfl⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have hk1_mem := (mem_filter.mp hk₁).2
        have hk2_mem := (mem_filter.mp hk₂).2
        have hfun : rotFin P.1 k₁.val (by omega) = rotFin P.1 k₂.val (by omega) :=
          congrArg Subtype.val heq
        rcases lt_trichotomy k₁.val k₂.val with hlt | heqv | hgt
        · exact absurd hfun (inj_lt k₁ k₂ hk1_mem.1 hlt (by omega))
        · exact Fin.ext heqv
        · exact absurd hfun.symm (inj_lt k₂ k₁ hk2_mem.1 hgt (by omega))
      · rintro ⟨Q, hQ⟩ hmem
        rw [Set.mem_toFinset, mem_neighborSet] at hmem
        rcases hmem with ⟨k, hk, hk1, hadj, hQ_eq⟩
        refine ⟨⟨k, by omega⟩, mem_filter.mpr ⟨mem_univ _, hk1, by simp; omega, hadj⟩, ?_⟩
        exact Subtype.ext hQ_eq.symm
    exact hmap.symm.trans (by simp)
  have hdeg_char : ∀ P : LVert,
      (Odd (L.degree P) ↔ G.Adj (P.1 ⟨n - 1, by omega⟩) 0) := by
    intro P
    rw [hdeg_eq P]
    set z := P.1 ⟨n - 1, by omega⟩
    have hzOdd : G.degree z % 2 = 1 := by
      apply oddAway
      · intro h
        have heq := P.2.1 (h.trans P.2.2.1.symm)
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      · intro h
        have heq := P.2.1 (h.trans P.2.2.2.1.symm)
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
    have hP_bij : Function.Bijective P.1 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨P.2.1, rfl⟩
    let S_idx : Finset (Fin n) := (Finset.univ.filter fun i : Fin n => G.Adj z (P.1 i))
    have hS_card : S_idx.card = G.degree z := by
      have : S_idx.card = (G.neighborFinset z).card := by
        refine Finset.card_bij (fun i _ => P.1 i) ?_ ?_ ?_
        · intro i hi; rw [mem_neighborFinset]; exact (mem_filter.mp hi).2
        · intro i₁ _ i₂ _ h; exact P.2.1 h
        · intro w hw
          rw [mem_neighborFinset] at hw
          obtain ⟨i, rfl⟩ := hP_bij.2 w
          exact ⟨i, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
      exact this
    let nm2 : Fin n := ⟨n - 2, by omega⟩
    have hnm2_mem : nm2 ∈ S_idx := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hnm1_eq : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; simp; omega
      have hadj_nm2 := (P.2.2.2.2 (n - 2) (by omega)).symm
      rwa [hnm1_eq] at hadj_nm2
    have hS_sub : ∀ i ∈ S_idx, i = nm2 ∨ i = ⟨0, by omega⟩ ∨ (1 ≤ i.val ∧ i.val < n - 2) := by
      intro i hi
      by_cases h1 : i = nm2
      · left; exact h1
      · by_cases h0 : i = ⟨0, by omega⟩
        · right; left; exact h0
        · right; right
          have hne_last : i ≠ ⟨n - 1, by omega⟩ := by
            intro heq
            exact G.loopless.irrefl z (by simpa [z, heq] using (mem_filter.mp hi).2)
          have hiv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hiv2 : i.val ≠ n - 2 := fun h => h1 (Fin.ext h)
          have hiv1 : i.val ≠ n - 1 := fun h => hne_last (Fin.ext h)
          omega
    let K_idx : Finset (Fin n) := Finset.univ.filter fun i : Fin n =>
      1 ≤ i.val ∧ i.val < n - 2 ∧ G.Adj z (P.1 i)
    change Odd K_idx.card ↔ G.Adj z 0
    have hS_part : (S_idx.erase nm2).card = G.degree z - 1 := by
      rw [Finset.card_erase_of_mem hnm2_mem, hS_card]
    by_cases hadj0 : G.Adj z 0
    · have h0_mem : (⟨0, by omega⟩ : Fin n) ∈ S_idx.erase nm2 := by
        rw [mem_erase, mem_filter]
        refine ⟨?_, mem_univ _, by rw [P.2.2.1]; exact hadj0⟩
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [nm2] at hval
        omega
      have hK_eq_erase : K_idx = (S_idx.erase nm2).erase ⟨0, by omega⟩ := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2, hiH⟩
          refine ⟨fun h => by have hv : i.val = 0 := congrArg Fin.val h; omega,
            fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h0, h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exact absurd rfl h0
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, Finset.card_erase_of_mem h0_mem, hS_part]
      have hpos := Finset.card_pos.mpr ⟨_, h0_mem⟩
      rw [hS_part] at hpos
      simp only [hadj0, iff_true, Nat.odd_iff]
      omega
    · have hK_eq_erase : K_idx = S_idx.erase nm2 := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨_, h2, hiH⟩
          exact ⟨fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exfalso
            apply hadj0
            rwa [P.2.2.1] at hiH
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, hS_part]
      simp only [hadj0, iff_false, Nat.odd_iff]
      omega
  have hP0_odd : Odd (L.degree P0) := by
    rw [hdeg_char P0]
    change G.Adj ⟨n - 1, by omega⟩ 0
    have wrap : (⟨n - 1, by omega⟩ : Fin n) + 1 = 0 := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
    exact wrap ▸ hc ⟨n - 1, by omega⟩
  obtain ⟨P1, hP1_ne, hP1_odd⟩ := L.exists_ne_odd_degree_of_exists_odd_degree P0 hP0_odd
  have hP1_closes : G.Adj (P1.1 ⟨n - 1, by omega⟩) 0 := (hdeg_char P1).mp hP1_odd
  have hP1_ne_fun : P1.1 ≠ fun i : Fin n => i := by
    intro heq
    exact hP1_ne (Subtype.ext heq)
  have hdiff : ∃ i : Fin n, P1.1 i ≠ i := by
    by_contra h
    push Not at h
    exact hP1_ne_fun (funext h)
  rcases hdiff with ⟨i_diff, hi_diff⟩
  exact ⟨P1.1, P1.2.1, P1.2.2.1, P1.2.2.2.1, P1.2.2.2.2, hP1_closes,
    i_diff.val, i_diff.isLt, hi_diff⟩

private lemma second_cycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (c : G.Walk v v)
    (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c)
    (edge : Sym2 V) (onCycle : edge ∈ c.edges)
    (exceptional : ∀ u, G.degree u % 2 ≠ 1 → u ∈ edge) :
    ∃ (w : V) (c' : G.Walk w w), LovaszPlummerConjecture.IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset := by
  have : Nonempty V := ⟨v⟩
  obtain ⟨hn3, e₀, hadj₀, hedges₀⟩ := cycle_indexing G v c hc
  let n := Fintype.card V
  have hn : 3 ≤ n := hn3
  have numbered : ∀ f ∈ c.edges, ∃ i : Fin n, f = s(e₀ i, e₀ (i + 1)) := by
    intro f
    induction f using Sym2.inductionOn with
    | _ x y => exact (hedges₀ x y).mp
  obtain ⟨i₀, hedge⟩ := numbered edge onCycle
  let rotEquiv : Fin n ≃ Fin n :=
    ⟨fun i => i + i₀, fun i => i - i₀, fun i => add_sub_cancel_right i i₀, fun i => sub_add_cancel i i₀⟩
  let e : Fin n ≃ V := rotEquiv.trans e₀
  have hfixed : edge = s(e 0, e 1) := by
    simpa [e, rotEquiv, add_comm] using hedge
  have he_adj : ∀ i : Fin n, G.Adj (e i) (e (i + 1)) := by
    intro i
    dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk]
    have hadd : i + 1 + i₀ = (i + i₀) + 1 := by abel
    rw [hadd]
    exact hadj₀ (i + i₀)
  have he_edges : ∀ x y : V, s(x, y) ∈ c.edges ↔ ∃ i : Fin n, s(x, y) = s(e i, e (i + 1)) := by
    intro x y
    rw [hedges₀ x y]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j - i₀, ?_⟩
      dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk]
      have h1 : j - i₀ + i₀ = j := sub_add_cancel j i₀
      have h2 : j - i₀ + 1 + i₀ = j + 1 := by abel
      rw [h1, h2, hj]
    · rintro ⟨i, hi⟩
      refine ⟨i + i₀, ?_⟩
      dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk] at hi
      have h2 : i + 1 + i₀ = i + i₀ + 1 := by abel
      rwa [h2] at hi
  let G' : SimpleGraph (Fin n) := SimpleGraph.comap e G
  let ge : G' ≃g G := ⟨e, Iff.rfl⟩
  have oddAway (z : Fin n) (hz0 : z ≠ 0) (hz1 : z ≠ 1) : G'.degree z % 2 = 1 := by
    have hdegree : G.degree (e z) = G'.degree z := ge.degree_eq z
    by_contra h
    have hz := exceptional (e z) (by rwa [hdegree])
    rw [hfixed, Sym2.mem_iff] at hz
    exact hz.elim (fun h0 => hz0 (e.injective h0)) (fun h1 => hz1 (e.injective h1))
  obtain ⟨p, hp_inj, hp0, hp1, hp_adj, hp_last, i_diff, hi_diff_lt, hi_diff⟩ :=
    second_ordering n hn G' he_adj oddAway
  let l : List V := List.ofFn fun i : Fin n => e (p i)
  have hl_ne : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [l] at this
    omega
  have hl_len : l.length = n := by simp [l]
  have hl_nodup : l.Nodup := by
    rw [List.nodup_ofFn]
    exact e.injective.comp hp_inj
  have hl_adj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1] := by
    intro i hi
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn]
    exact hp_adj i hi
  obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := walkOfChain_exists G l hl_ne hl_adj
  have hhead : l.head hl_ne = e ⟨0, by omega⟩ := by
    rw [List.head_eq_getElem_zero]
    simp only [l, List.getElem_ofFn, hp0]
    rfl
  have hlast : l.getLast hl_ne = e (p ⟨n - 1, by omega⟩) := by
    rw [List.getLast_eq_getElem]
    simp only [l, hl_len, List.getElem_ofFn]
  have hadj_close : G.Adj (l.head hl_ne) (l.getLast hl_ne) := by
    rw [hhead, hlast]
    exact hp_last.symm
  let c' : G.Walk (l.head hl_ne) (l.head hl_ne) := Walk.cons hadj_close q.reverse
  have hc'_edge_not : s(l.head hl_ne, l.getLast hl_ne) ∉ q.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse, hq_edges]
    rintro ⟨i, hi, heq⟩
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn] at heq
    rw [hhead, hlast] at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i, by omega⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i + 1, hi⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
  have hc'_cyc : c'.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, hc'_edge_not⟩
    rw [Walk.isPath_def, Walk.support_reverse, hq_sup]
    exact List.nodup_reverse.mpr hl_nodup
  have hc'_ham : ∀ w : V, w ∈ c'.support := by
    intro w
    simp only [c', Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse, hq_sup]
    right
    have hp_bij : Function.Bijective p := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hp_inj, rfl⟩
    obtain ⟨i, hi⟩ := (e.bijective.comp hp_bij).2 w
    rw [← hi]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  refine ⟨l.head hl_ne, c', ⟨hc'_cyc, hc'_ham⟩, ?_⟩
  intro hfin
  have hedge_sub : ∀ i : ℕ, (hi : i + 1 < n) →
      ∃ j : Fin n, s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) = s(e j, e (j + 1)) := by
    intro i hi
    have hmem : s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) ∈ c'.edges.toFinset := by
      rw [List.mem_toFinset]
      simp only [c', Walk.edges_cons, List.mem_cons, Walk.edges_reverse, List.mem_reverse, hq_edges]
      right
      refine ⟨i, by rw [hl_len]; exact hi, ?_⟩
      simp [l]
    rw [hfin, List.mem_toFinset] at hmem
    exact (he_edges _ _).mp hmem
  have hp_eq_id : ∀ k : ℕ, (hk : k < n) → p ⟨k, hk⟩ = ⟨k, hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk0
      · exact hp0
      · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk0)) with rfl | hk1
        · exact hp1.trans (by ext; simp [Nat.mod_eq_of_lt hk])
        · have hk_m1 : k - 1 < k := by omega
          have hk_m2 : k - 2 < k := by omega
          have hpm1 := ih (k - 1) hk_m1 (by omega)
          have hpm2 := ih (k - 2) hk_m2 (by omega)
          obtain ⟨j, hj⟩ := hedge_sub (k - 1) (by omega)
          rw [Sym2.eq_iff] at hj
          have hstep : p ⟨k, hk⟩ = p ⟨k - 1, by omega⟩ + 1 ∨
              p ⟨k - 1, by omega⟩ = p ⟨k, hk⟩ + 1 := by
            rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
            · right
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
          rw [hpm1] at hstep
          rcases hstep with hplus | hminus
          · have h1val : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
            rw [hplus, Fin.ext_iff, Fin.val_add, h1val]
            change (k - 1 + 1) % n = k
            rw [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.mod_eq_of_lt hk]
          · exfalso
            have hkp : p ⟨k, hk⟩ = ⟨k - 2, by omega⟩ := by
              have h1 := congrArg (· - 1) hminus
              have h2 : p ⟨k, hk⟩ = (⟨k - 1, by omega⟩ : Fin n) - 1 := by
                simpa using h1.symm
              rw [h2]
              ext
              have hv : ((⟨k - 1, by omega⟩ : Fin n) - 1).val = k - 2 := by
                rw [Fin.val_sub_one_of_ne_zero (by intro h; have := congrArg Fin.val h; simp at this; omega)]
                simp; omega
              exact hv
            have heq := hp_inj (hkp.trans hpm2.symm)
            have hval := congrArg Fin.val heq
            simp at hval; omega
  exact hi_diff (hp_eq_id i_diff hi_diff_lt)
end OMA.SheehanEdgeParity

theorem OMA.solution : OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1.H1 := by
  intro V _ _ G _ v c hc edge onCycle exceptional
  exact OMA.SheehanEdgeParity.second_cycle G v c hc edge onCycle exceptional
