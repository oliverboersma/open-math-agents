import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1
import Mathlib.Data.Fin.Parity

/-! Minimum degree three and the two-step rotation of a marked rim suffice.
At even order, either the boundary-domination criterion applies or both
parity classes carry a chord orbit. Equal displacements give a two-edge
exchange. Unequal ones reconnect four intervals in a different order.

The dominated-boundary and walk lemmas below are adapted from
open-math-agents PRs 6167 and 5313, building on luciusacarr, PR 4484. -/
namespace OMA.SheehanTwoStep
open SimpleGraph Finset LovaszPlummerConjecture
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

private lemma h2_on_fin (n : ℕ) [NeZero n] (hn3 : 3 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ i : Fin n, G.Adj i (i + 1))
    (I : Finset (Fin n)) (h0I : (0 : Fin n) ∈ I)
    (hI_ind : ∀ x ∈ I, x+1 ∈ I → x = 0)
    (hI_dom : ∀ u : Fin n, u ∉ I → (u - 1 ∈ I ∨ u + 1 ∈ I) →
      ∃ w ∈ I, G.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1) :
    ∃ (p : Fin n → Fin n), Function.Injective p ∧
      p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 1 ∧
      (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (p ⟨i, by omega⟩) (p ⟨i + 1, hi⟩)) ∧
      G.Adj (p ⟨n - 1, by omega⟩) 0 ∧
      ∃ i : ℕ, ∃ (hi : i < n), p ⟨i, hi⟩ ≠ ⟨i, hi⟩ := by
  classical
  have h2ne0 : (2 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  have hprev_ne_next : ∀ u : Fin n, u - 1 ≠ u + 1 := by
    intro u h
    apply h2ne0
    have h1 := congrArg (fun x => x - (u - 1)) h
    have h2 : u + 1 - (u - 1) = (2 : Fin n) := by
      have htwo : (2 : Fin n) = (1 : Fin n) + 1 := by
        ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
          Nat.mod_eq_of_lt (by omega : 2 < n)]
      rw [htwo]
      abel
    simpa [sub_self, h2] using h1.symm
  let B : Finset (Fin n) := Finset.univ.filter fun u => u ∉ I ∧ (u - 1 ∈ I ∨ u + 1 ∈ I)
  have hg_exists : ∀ u : Fin n, u ∈ B → ∃ w ∈ I, G.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1 := by
    intro u hu
    rw [mem_filter] at hu
    exact hI_dom u hu.2.1 hu.2.2
  let g : Fin n → Fin n := fun u =>
    if hu : u ∈ B then Classical.choose (hg_exists u hu) else 0
  have hg_spec : ∀ u ∈ B, g u ∈ I ∧ G.Adj u (g u) ∧ g u ≠ u + 1 ∧ u ≠ g u + 1 := by
    intro u hu
    simp only [g, dif_pos hu]
    exact Classical.choose_spec (hg_exists u hu)
  let CAdj : Fin n → Fin n → Prop := fun u w => w = u + 1 ∨ u = w + 1
  let HAdj : Fin n → Fin n → Prop := fun u w =>
    CAdj u w ∨ (u ∈ B ∧ w = g u) ∨ (w ∈ B ∧ u = g w)
  have hH_symm : ∀ u w, HAdj u w → HAdj w u := by
    rintro u w (h | h | h)
    · exact Or.inl (Or.symm h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hH_irrefl : ∀ u, ¬ HAdj u u := by
    rintro u (⟨h | h⟩ | ⟨hu, hgu⟩ | ⟨hu, hgu⟩)
    · have : (1 : Fin n) = 0 := by
        have := congrArg (· - u) h
        simpa using this.symm
      have hv := congrArg Fin.val this
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    · have : (1 : Fin n) = 0 := by
        have := congrArg (· - u) h
        simpa using this
      have hv := congrArg Fin.val this
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    · have huB := (mem_filter.mp hu).2.1
      have hgI := (hg_spec u hu).1
      exact huB (hgu ▸ hgI)
    · have huB := (mem_filter.mp hu).2.1
      have hgI := (hg_spec u hu).1
      exact huB (hgu ▸ hgI)
  let H : SimpleGraph (Fin n) := ⟨HAdj, ⟨fun _ _ => hH_symm _ _⟩, ⟨hH_irrefl⟩⟩
  have hH_le_G : H ≤ G := by
    rintro u w (⟨rfl | rfl⟩ | ⟨hu, rfl⟩ | ⟨hw, rfl⟩)
    · exact hc u
    · exact (hc w).symm
    · exact (hg_spec u hu).2.1
    · exact (hg_spec w hw).2.1.symm
  have hH_ind (u w : Fin n) (hadj : H.Adj u w) (huI : u ∈ I) (hwI : w ∈ I) :
      w = 0 ∨ w = 1 := by
    rcases hadj with (⟨rfl | rfl⟩ | ⟨hu, _⟩ | ⟨hw, _⟩)
    · exact Or.inr (by rw [hI_ind u huI hwI,zero_add])
    · exact Or.inl (hI_ind w hwI huI)
    · exact ((mem_filter.mp hu).2.1 huI).elim
    · exact ((mem_filter.mp hw).2.1 hwI).elim
  have hH_nbr_B : ∀ u ∈ B, ∀ w : Fin n, H.Adj u w ↔ w = u - 1 ∨ w = u + 1 ∨ w = g u := by
    intro u hu w
    constructor
    · rintro (⟨rfl | rfl⟩ | ⟨_, rfl⟩ | ⟨hw, hgw⟩)
      · right; left; rfl
      · left; abel
      · right; right; rfl
      · exfalso
        exact (mem_filter.mp hu).2.1 (hgw ▸ (hg_spec w hw).1)
    · rintro (rfl | rfl | rfl)
      · left; right; abel
      · left; left; rfl
      · right; left; exact ⟨hu, rfl⟩
  have hH_nbr_nonB : ∀ u : Fin n, u ∉ I → u ∉ B → ∀ w : Fin n,
      H.Adj u w ↔ w = u - 1 ∨ w = u + 1 := by
    intro u huI huB w
    constructor
    · rintro (⟨rfl | rfl⟩ | ⟨hu, _⟩ | ⟨hw, hgw⟩)
      · right; rfl
      · left; abel
      · exact absurd hu huB
      · exact absurd (hgw ▸ (hg_spec w hw).1) huI
    · rintro (rfl | rfl)
      · left; right; abel
      · left; left; rfl
  let IsGood (P : Fin n → Fin n) : Prop :=
    Function.Injective P ∧
    P ⟨0, by omega⟩ = 0 ∧
    P ⟨1, by omega⟩ = 1 ∧
    (∀ i : ℕ, (hi : i + 1 < n) → H.Adj (P ⟨i, by omega⟩) (P ⟨i + 1, hi⟩)) ∧
    (∀ u : Fin n, u ∉ I → u + 1 ∉ I →
      ∃ i : ℕ, ∃ (hi : i + 1 < n),
        ((P ⟨i, by omega⟩ = u ∧ P ⟨i + 1, hi⟩ = u + 1) ∨
          (P ⟨i, by omega⟩ = u + 1 ∧ P ⟨i + 1, hi⟩ = u))) ∧
    P ⟨n - 1, by omega⟩ ∉ I
  let LVert := { P : Fin n → Fin n // IsGood P }
  have hgood_end_B : ∀ P : LVert, P.1 ⟨n - 1, by omega⟩ ∈ B := by
    intro ⟨P, hP⟩
    set z := P ⟨n - 1, by omega⟩
    have hzI : z ∉ I := hP.2.2.2.2.2
    by_contra hzB
    have hzm1 : z - 1 ∉ I := fun h => hzB (mem_filter.mpr ⟨mem_univ _, hzI, Or.inl h⟩)
    have hzp1 : z + 1 ∉ I := fun h => hzB (mem_filter.mpr ⟨mem_univ _, hzI, Or.inr h⟩)
    have hp1 := hP.2.2.2.2.1 z hzI hzp1
    have hzm1p1 : (z - 1) + 1 = z := by abel
    have hm1 := hP.2.2.2.2.1 (z - 1) hzm1 (by rwa [hzm1p1])
    rw [hzm1p1] at hm1
    have extract_prev : ∀ w : Fin n,
        (∃ i : ℕ, ∃ (hi : i + 1 < n),
          ((P ⟨i, by omega⟩ = z ∧ P ⟨i + 1, hi⟩ = w) ∨
            (P ⟨i, by omega⟩ = w ∧ P ⟨i + 1, hi⟩ = z))) →
        w = P ⟨n - 2, by omega⟩ := by
      intro w ⟨i, hi, hpair⟩
      rcases hpair with ⟨hi_z, _⟩ | ⟨hi_w, hi1_z⟩
      · have heq := hP.1 hi_z
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      · have heq := hP.1 hi1_z
        have hval := congrArg Fin.val heq
        simp at hval
        have hi2 : i = n - 2 := by omega
        subst hi2
        exact hi_w.symm
    have hm1' : ∃ i : ℕ, ∃ (hi : i + 1 < n),
        (P ⟨i, by omega⟩ = z ∧ P ⟨i + 1, hi⟩ = z - 1) ∨
          (P ⟨i, by omega⟩ = z - 1 ∧ P ⟨i + 1, hi⟩ = z) :=
      let ⟨i, hi, hp⟩ := hm1; ⟨i, hi, hp.symm⟩
    exact hprev_ne_next z ((extract_prev (z - 1) hm1').trans (extract_prev (z + 1) hp1).symm)
  have hgood_nbr_I : ∀ P : LVert, ∀ w : Fin n,
      H.Adj (P.1 ⟨n - 1, by omega⟩) w → w ≠ P.1 ⟨n - 2, by omega⟩ → w ∈ I := by
    intro ⟨P, hP⟩ w hw hne
    set z := P ⟨n - 1, by omega⟩
    have hzB : z ∈ B := hgood_end_B ⟨P, hP⟩
    have hzI : z ∉ I := hP.2.2.2.2.2
    rw [hH_nbr_B z hzB] at hw
    rcases hw with rfl | rfl | rfl
    · by_contra hzmI
      have hzm1p1 : (z - 1) + 1 = z := by abel
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 (z - 1) hzmI (by rwa [hzm1p1])
      rw [hzm1p1] at hpair
      apply hne
      rcases hpair with ⟨hi_w, hi1_z⟩ | ⟨hi_z, _⟩
      · have hval := congrArg Fin.val (hP.1 hi1_z)
        simp at hval
        have : i = n - 2 := by omega
        subst this; exact hi_w.symm
      · have hval := congrArg Fin.val (hP.1 hi_z)
        simp at hval; omega
    · by_contra hzpI
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 z hzI hzpI
      apply hne
      rcases hpair with ⟨hi_z, hi1_w⟩ | ⟨hi_w, hi1_z⟩
      · have hval := congrArg Fin.val (hP.1 hi_z)
        simp at hval; omega
      · have hval := congrArg Fin.val (hP.1 hi1_z)
        simp at hval
        have : i = n - 2 := by omega
        subst this; exact hi_w.symm
    · exact (hg_spec z hzB).1
  let LAdj : LVert → LVert → Prop := fun P Q =>
    ∃ k : ℕ, ∃ hk : k + 2 < n, 1 ≤ k ∧
      H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) ∧
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
      change H.Adj (Q ⟨n - 1, by omega⟩) (Q ⟨k, by omega⟩)
      rw [hQ_n1, hQ_k]
      exact (hP.2.2.2.1 k (by omega)).symm
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
      H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) →
      IsGood (rotFin P.1 k hk) := by
    intro ⟨P, hP⟩ k hk hk1 hadj
    dsimp only at hadj
    have hPkI : P ⟨k, by omega⟩ ∈ I := by
      apply hgood_nbr_I ⟨P, hP⟩ _ hadj
      intro heq
      have hval := congrArg Fin.val (hP.1 heq)
      simp at hval
      omega
    have hPk1_notI : P ⟨k + 1, by omega⟩ ∉ I := by
      intro member
      rcases hH_ind _ _ (hP.2.2.2.1 k (by omega)) hPkI member with zero|one
      · have v := congrArg Fin.val (hP.1 (zero.trans hP.2.1.symm))
        dsimp at v
        omega
      · have v := congrArg Fin.val (hP.1 (one.trans hP.2.2.1.symm))
        dsimp at v
        omega
    refine ⟨rotFin_inj hP.1 hk, ?_, ?_, ?_, ?_, ?_⟩
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
        exact hP.2.2.2.1 i hi
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
          have hchain := (hP.2.2.2.1 (n + k - (i + 1)) hm_lt).symm
          convert hchain using 2; ext; dsimp; omega
    · intro u huI hu1I
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 u huI hu1I
      have hineq : i ≠ k := by
        rintro rfl
        rcases hpair with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact huI (h1 ▸ hPkI)
        · exact hu1I (h2 ▸ hPkI)
      by_cases hik : i + 1 ≤ k
      · refine ⟨i, hi, ?_⟩
        dsimp only [rotFin]
        have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp [rotIdx, show i ≤ k by omega]
        have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp [rotIdx, hik]
        rw [hidx1, hidx2]
        exact hpair
      · have ik_gt : k < i := by omega
        let j := n + k - 1 - i
        have hj_lt : j + 1 < n := by omega
        have hj_gt : ¬ (j ≤ k) := by omega
        have hj1_gt : ¬ (j + 1 ≤ k) := by omega
        refine ⟨j, hj_lt, ?_⟩
        have hidx1 : (⟨rotIdx n k j, rotIdx_lt hk (by omega : j < n)⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp only [rotIdx, hj_gt, ↓reduceIte, j]; omega
        have hidx2 : (⟨rotIdx n k (j + 1), rotIdx_lt hk hj_lt⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp only [rotIdx, hj1_gt, ↓reduceIte, j]; omega
        dsimp only [rotFin]
        rw [hidx1, hidx2]
        rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inr ⟨hb, ha⟩
        · exact Or.inl ⟨hb, ha⟩
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k (n - 1), rotIdx_lt hk (by omega : n - 1 < n)⟩ : Fin n) =
          ⟨k + 1, by omega⟩ := by
        ext; simp only [rotIdx, show ¬ (n - 1 ≤ k) by omega, ↓reduceIte]; omega
      rw [hidx]
      exact hPk1_notI
  have hP0_good : IsGood (fun i : Fin n => i) := by
    refine ⟨Function.injective_id, rfl, by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)],
      fun i hi => ?_, fun u _ _ => ?_, ?_⟩
    · left; left; ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hi]
    · by_cases hu : u.val + 1 < n
      · refine ⟨u.val, hu, Or.inl ⟨rfl, ?_⟩⟩
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hu]
      · exfalso
        have hu_lt := u.isLt
        have huv : u = ⟨n - 1, by omega⟩ := Fin.ext (by change u.val = n - 1; omega)
        have hu1 : u + 1 = 0 := by
          rw [huv]
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
        exact absurd h0I (hu1 ▸ ‹u + 1 ∉ I›)
    · intro hnm1
      have h0_eq : (0 : Fin n) = (⟨n - 1, by omega⟩ : Fin n) + 1 := by
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
      have eq := hI_ind ⟨n-1,by omega⟩ hnm1 (h0_eq ▸ h0I)
      have v := congrArg Fin.val eq
      dsimp at v
      omega
  let P0 : LVert := ⟨fun i : Fin n => i, hP0_good⟩
  have hdeg_eq : ∀ P : LVert, L.degree P =
      (Finset.univ.filter fun k : Fin n =>
        1 ≤ k.val ∧ k.val < n - 2 ∧ H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card := by
    intro P
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    have hmap :
        (Finset.univ.filter fun k : Fin n =>
          1 ≤ k.val ∧ k.val < n - 2 ∧ H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card =
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
      (Odd (L.degree P) ↔ H.Adj (P.1 ⟨n - 1, by omega⟩) 0) := by
    intro P
    rw [hdeg_eq P]
    set z := P.1 ⟨n - 1, by omega⟩
    have hzB : z ∈ B := hgood_end_B P
    have hz_nbrs : H.neighborFinset z = {z - 1, z + 1, g z} := by
      ext w
      rw [mem_neighborFinset, hH_nbr_B z hzB]
      simp
    have hcard_z : (H.neighborFinset z).card = 3 := by
      rw [hz_nbrs]
      have h12 : z - 1 ≠ z + 1 := hprev_ne_next z
      have h13 : z - 1 ≠ g z := by
        intro h
        have hg := (hg_spec z hzB).2.2.2
        apply hg
        calc
          z = z - 1 + 1 := by abel
          _ = g z + 1 := by rw [h]
      have h23 : z + 1 ≠ g z := (hg_spec z hzB).2.2.1.symm
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    have hP_bij : Function.Bijective P.1 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨P.2.1, rfl⟩
    let S_idx : Finset (Fin n) := (Finset.univ.filter fun i : Fin n => H.Adj z (P.1 i))
    have hS_card : S_idx.card = 3 := by
      have : S_idx.card = (H.neighborFinset z).card := by
        refine Finset.card_bij (fun i _ => P.1 i) ?_ ?_ ?_
        · intro i hi; rw [mem_neighborFinset]; exact (mem_filter.mp hi).2
        · intro i₁ _ i₂ _ h; exact P.2.1 h
        · intro w hw
          rw [mem_neighborFinset] at hw
          obtain ⟨i, rfl⟩ := hP_bij.2 w
          exact ⟨i, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
      rw [this, hcard_z]
    let nm2 : Fin n := ⟨n - 2, by omega⟩
    have hnm2_mem : nm2 ∈ S_idx := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hnm1_eq : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; simp; omega
      have hadj_nm2 := (P.2.2.2.2.1 (n - 2) (by omega)).symm
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
            exact H.loopless.irrefl z (by simpa [z, heq] using (mem_filter.mp hi).2)
          have hiv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hiv2 : i.val ≠ n - 2 := fun h => h1 (Fin.ext h)
          have hiv1 : i.val ≠ n - 1 := fun h => hne_last (Fin.ext h)
          omega
    let K_idx : Finset (Fin n) := Finset.univ.filter fun i : Fin n =>
      1 ≤ i.val ∧ i.val < n - 2 ∧ H.Adj z (P.1 i)
    change Odd K_idx.card ↔ H.Adj z 0
    have hS_part : (S_idx.erase nm2).card = 2 := by
      rw [Finset.card_erase_of_mem hnm2_mem, hS_card]
    by_cases hadj0 : H.Adj z 0
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
      simp [hadj0]
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
      simp [hadj0]
  have hP0_odd : Odd (L.degree P0) := by
    rw [hdeg_char P0]
    refine Or.inl (Or.inl ?_)
    ext
    dsimp [P0]
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  obtain ⟨P1, hP1_ne, hP1_odd⟩ := L.exists_ne_odd_degree_of_exists_odd_degree P0 hP0_odd
  have hP1_closes : H.Adj (P1.1 ⟨n - 1, by omega⟩) 0 := (hdeg_char P1).mp hP1_odd
  have hP1_ne_fun : P1.1 ≠ fun i : Fin n => i := by
    intro heq
    exact hP1_ne (Subtype.ext heq)
  have hdiff : ∃ i : Fin n, P1.1 i ≠ i := by
    by_contra h
    push Not at h
    exact hP1_ne_fun (funext h)
  rcases hdiff with ⟨i_diff, hi_diff⟩
  refine ⟨P1.1, P1.2.1, P1.2.2.1, P1.2.2.2.1, ?_, ?_, i_diff.val, i_diff.isLt, hi_diff⟩
  · intro i hi
    exact hH_le_G (P1.2.2.2.2.1 i hi)
  · exact hH_le_G hP1_closes

/-- An independent set on the cycle whose cycle-neighbors all see the set
by a chord certifies the existence of a second Hamilton cycle. -/
theorem second_cycle_of_dominated_boundary {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (c : G.Walk v v)
    (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c) (I : Finset V) (nonempty : I.Nonempty)
    (hI_ind : ∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges)
    (hI_dom : ∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
      ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges) :
    ∃ (w : V) (c' : G.Walk w w), LovaszPlummerConjecture.IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset := by
  have : Nonempty V := ⟨v⟩
  obtain ⟨hn3, e₀, hadj₀, hedges₀⟩ := cycle_indexing G v c hc
  let n := Fintype.card V
  obtain ⟨s₀, hs₀⟩ := nonempty
  let i₀ : Fin n := e₀.symm s₀
  let rotEquiv : Fin n ≃ Fin n :=
    ⟨fun i => i + i₀, fun i => i - i₀, fun i => add_sub_cancel_right i i₀, fun i => sub_add_cancel i i₀⟩
  let e : Fin n ≃ V := rotEquiv.trans e₀
  have he0 : e ⟨0, by omega⟩ = s₀ := by
    simp [e, rotEquiv, i₀]
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
  let I' : Finset (Fin n) := Finset.univ.filter fun i => e i ∈ I
  have h0I' : (⟨0, by omega⟩ : Fin n) ∈ I' := by
    rw [mem_filter]
    exact ⟨mem_univ _, by rw [he0]; exact hs₀⟩
  have hI'_ind : ∀ x ∈ I', x+1 ∈ I' → x = 0 := by
    intro x hx hy
    exact (hI_ind (e x) (mem_filter.mp hx).2 (e (x+1)) (mem_filter.mp hy).2
      ((he_edges _ _).mpr ⟨x,rfl⟩)).elim
  have hI'_dom : ∀ u : Fin n, u ∉ I' → (u - 1 ∈ I' ∨ u + 1 ∈ I') →
      ∃ w ∈ I', G'.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1 := by
    intro u hu hboundary
    have huI : e u ∉ I := fun h => hu (mem_filter.mpr ⟨mem_univ _, h⟩)
    have hneighbor : ∃ x ∈ I, s(e u, x) ∈ c.edges := by
      rcases hboundary with h | h
      · refine ⟨e (u - 1), (mem_filter.mp h).2, (he_edges _ _).mpr ⟨u - 1, ?_⟩⟩
        rw [sub_add_cancel]
        exact Sym2.eq_swap
      · exact ⟨e (u + 1), (mem_filter.mp h).2, (he_edges _ _).mpr ⟨u, rfl⟩⟩
    obtain ⟨w, hwI, hadj_w, hnotc⟩ := hI_dom (e u) huI hneighbor
    refine ⟨e.symm w, mem_filter.mpr ⟨mem_univ _, by simpa using hwI⟩, ?_, ?_, ?_⟩
    · simpa [G'] using hadj_w
    · intro h
      apply hnotc
      have hwu : w = e (u + 1) := by rw [← h]; simp
      rw [hwu]
      exact (he_edges _ _).mpr ⟨u, rfl⟩
    · intro h
      apply hnotc
      have huw : e u = e (e.symm w + 1) := congrArg e h
      rw [huw]
      refine (he_edges _ _).mpr ⟨e.symm w, ?_⟩
      simp [Sym2.eq_swap]
  obtain ⟨p, hp_inj, hp0, hp1, hp_adj, hp_last, i_diff, hi_diff_lt, hi_diff⟩ :=
    h2_on_fin n hn3 G' (fun i => by simpa [G'] using he_adj i) I' h0I' hI'_ind hI'_dom
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

private theorem cycle_from_order {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph V)
    {v : V} (c : G.Walk v v) (e : Fin n ≃ V)
    (he_edges : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(e i, e (i+1)))
    (p : Fin n → Fin n) (hp_inj : Function.Injective p)
    (hp0 : p ⟨0, by omega⟩ = 0) (hp1 : p ⟨1, by omega⟩ = 1)
    (hp_adj : ∀ i : ℕ, (hi : i + 1 < n) →
      G.Adj (e (p ⟨i, by omega⟩)) (e (p ⟨i+1, hi⟩)))
    (hp_last : G.Adj (e (p ⟨n-1, by omega⟩)) (e 0))
    (i_diff : ℕ) (hi_diff_lt : i_diff < n)
    (hi_diff : p ⟨i_diff, hi_diff_lt⟩ ≠ ⟨i_diff, hi_diff_lt⟩) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
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

private theorem succ_in_bounds {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : ℕ) (h : i+1 < n) :
    (⟨i, by omega⟩ : Fin n) + 1 = ⟨i+1,h⟩ := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt h]

theorem second_of_two_chords {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph V) {v : V}
    (c : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(e i,e (i+1)))
    (k : ℕ) (lo : 1 ≤ k) (hi : k+2 < n)
    (first : G.Adj (e ⟨k,by omega⟩) (e ⟨n-1,by omega⟩))
    (second : G.Adj (e ⟨k+1,by omega⟩) (e 0)) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  let p := rotFin (id : Fin n → Fin n) k hi
  have pref (i : ℕ) (h : i ≤ k) : p ⟨i,by omega⟩ = ⟨i,by omega⟩ := by
    apply Fin.ext
    simp [p,rotFin,rotIdx,h]
  have tailv (i : ℕ) (h : k < i) (hi' : i < n) : p ⟨i,hi'⟩ = ⟨n+k-i,by omega⟩ := by
    apply Fin.ext
    simp [p,rotFin,rotIdx,show ¬i≤k by omega]
  have atCut : p ⟨k+1,by omega⟩ = ⟨n-1,by omega⟩ := by
    rw [tailv (k+1) (by omega)]
    apply Fin.ext
    dsimp
    omega
  have atEnd : p ⟨n-1,by omega⟩ = ⟨k+1,by omega⟩ := by
    rw [tailv (n-1) (by omega)]
    apply Fin.ext
    dsimp
    omega
  have chain (i : ℕ) (h : i+1 < n) : G.Adj (e ⟨i,by omega⟩) (e ⟨i+1,h⟩) := by
    rw [← succ_in_bounds hn i h]
    exact red _
  refine cycle_from_order hn G c e rim p (rotFin_inj Function.injective_id hi) ?_ ?_ ?_ ?_ (k+1) (by omega) ?_
  · exact (pref 0 (by omega)).trans (Fin.ext rfl)
  · apply (pref 1 lo).trans
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (by omega : 1 < n)).symm
  · intro i h
    by_cases hbefore : i+1 ≤ k
    · rw [pref _ (by omega),pref _ hbefore]
      exact chain _ _
    · by_cases heq : i = k
      · subst i
        rw [pref k (by omega),atCut]
        exact first
      · rw [tailv _ (by omega),tailv _ (by omega)]
        have he := (chain (n+k-(i+1)) (by omega)).symm
        convert he using 2 <;> apply Fin.ext <;> dsimp <;> omega
  · rw [atEnd]
    exact second
  · rw [atCut]
    intro eq
    have := congrArg Fin.val eq
    dsimp at this
    omega

/-- Invariance under the one-step rotation of the marked cycle turns any
non-rim neighbor of its last vertex into the second chord of a two-edge exchange. -/
theorem second_of_rotation {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (c : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(e i,e (i+1)))
    (symm : ∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+1)) (e (j+1)))
    (deg : 3 ≤ G.degree (e ⟨n-1,by omega⟩)) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  let last : Fin n := ⟨n-1,by omega⟩
  let prev : Fin n := ⟨n-2,by omega⟩
  obtain ⟨i,adj,h0,hpre⟩ : ∃ i : Fin n, G.Adj (e i) (e last) ∧ i ≠ 0 ∧ i ≠ prev := by
    by_contra! no
    have sub : G.neighborFinset (e last) ⊆ {e 0,e prev} := by
      intro w hw
      have hadj := (mem_neighborFinset G _ _).mp hw
      let i := e.symm w
      have ei : e i = w := e.apply_symm_apply w
      by_cases h : i = 0
      · rw [← ei,h]; simp
      · have h' := no i (ei ▸ hadj.symm) h
        rw [← ei,h']; simp
    have bound := Finset.card_le_card sub
    have pair := Finset.card_insert_le (e 0) ({e prev} : Finset V)
    rw [card_neighborFinset_eq_degree] at bound
    simp only [Finset.card_singleton] at pair
    change 3 ≤ G.degree (e last) at deg
    omega
  have none : i ≠ last := fun h => adj.ne (congrArg e h)
  have vi0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have vip : i.val ≠ n-2 := fun h => hpre (Fin.ext h)
  have vil : i.val ≠ n-1 := fun h => none (Fin.ext h)
  have lo : 1 ≤ i.val := by omega
  have hi : i.val+2 < n := by have := i.isLt; omega
  have end0 : last+1 = 0 := by
    apply Fin.ext
    change ((n-1) + (1 : Fin n).val) % n = 0
    rw [show (1 : Fin n).val = 1 from Nat.mod_eq_of_lt (by omega : (1:ℕ) < n)]
    rw [show n-1+1 = n by omega, Nat.mod_self]
  have second := symm i last adj
  rw [end0,show i+1 = ⟨i.val+1,by omega⟩ from succ_in_bounds hn i.val (by omega)] at second
  exact second_of_two_chords hn G c e red rim i.val lo hi adj second

open scoped Fin.CommRing

private theorem end_succ {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    (⟨n-1,by omega⟩ : Fin n)+1 = 0 := by
  apply Fin.ext
  change ((n-1)+(1 : Fin n).val)%n = 0
  rw [show (1 : Fin n).val = 1 from Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [show n-1+1 = n by omega,Nat.mod_self]

private theorem paired_chords {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph V) {v : V}
    (c : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(e i,e (i+1)))
    (a b : Fin n) (ab : G.Adj (e a) (e b)) (na : a ≠ b+1) (nb : b ≠ a+1)
    (both : G.Adj (e (a+1)) (e (b+1))) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  let s := a+1
  let t : Fin n ≃ V := (Equiv.addLeft s).trans e
  let last : Fin n := ⟨n-1,by omega⟩
  let prev : Fin n := ⟨n-2,by omega⟩
  have hl : last+1 = 0 := end_succ hn
  have hp : prev+1 = last := by
    rw [show prev+1 = ⟨n-2+1,by omega⟩ from succ_in_bounds hn (n-2) (by omega)]
    apply Fin.ext; dsimp [last]; omega
  have sl : s+last = a := by
    calc
      _ = a+(last+1) := by dsimp [s]; abel
      _ = a := by rw [hl,add_zero]
  let z := b-s
  have sz : s+z = b := by dsimp [z]; abel
  have nz : z.val ≠ 0 := by
    intro h
    have hz : z = 0 := Fin.ext h
    exact nb (by simpa [hz,s] using sz.symm)
  have nl : z.val ≠ n-1 := by
    intro h
    have hz : z = last := Fin.ext h
    rw [hz,sl] at sz
    exact ab.ne (congrArg e sz)
  have np : z.val ≠ n-2 := by
    intro h
    have hz : z = prev := Fin.ext h
    apply na
    calc
      a = s+last := sl.symm
      _ = s+z+1 := by rw [hz,← hp]; abel
      _ = b+1 := by rw [sz]
  have lo : 1 ≤ z.val := by omega
  have hi : z.val+2 < n := by have := z.isLt; omega
  have redt (i : Fin n) : G.Adj (t i) (t (i+1)) := by
    change G.Adj (e (s+i)) (e (s+(i+1)))
    rw [← add_assoc]
    exact red _
  have rimt (x y : V) : s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(t i,t (i+1)) := by
    rw [rim]
    constructor
    · rintro ⟨i,h⟩
      refine ⟨i-s,?_⟩
      change s(x,y) = s(e (s+(i-s)),e (s+(i-s+1)))
      rw [show s+(i-s) = i by abel,show s+(i-s+1) = i+1 by abel]
      exact h
    · rintro ⟨i,h⟩
      refine ⟨s+i,?_⟩
      simpa [t,add_assoc] using h
  apply second_of_two_chords hn G c t redt rimt z.val lo hi
  · change G.Adj (e (s+z)) (e (s+last))
    rw [sz,sl]
    exact ab.symm
  · change G.Adj (e (s+⟨z.val+1,by omega⟩)) (e (s+0))
    rw [← succ_in_bounds hn z.val (by omega),← add_assoc,sz,add_zero]
    exact both.symm

private def rearrange (n a b c j : ℕ) : ℕ :=
  if j<a then j
  else if j<a+(n-c) then n-1-(j-a)
  else if j<b+(n-c) then a+(j-(a+(n-c)))
  else c-1-(j-(b+(n-c)))

theorem four_interval_exchange {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (G : SimpleGraph V) {v : V} (cycle : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y, s(x,y) ∈ cycle.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1)))
    (a b c : ℕ) (lo : 2≤a) (ab : a<b) (bc : b<c) (cn : c<n)
    (l₁ : G.Adj (e ⟨a-1,by omega⟩) (e ⟨n-1,by omega⟩))
    (r₁ : G.Adj (e ⟨c,cn⟩) (e ⟨a,by omega⟩))
    (l₂ : G.Adj (e ⟨b-1,by omega⟩) (e ⟨c-1,by omega⟩))
    (r₂ : G.Adj (e ⟨b,by omega⟩) (e 0)) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ cycle.edges.toFinset := by
  have hn : 3 ≤ n := by omega
  let f := rearrange n a b c
  have bound {j : ℕ} (hj : j<n) : f j<n := by
    simp only [f,rearrange]
    split_ifs <;> omega
  let p (i : Fin n) : Fin n := ⟨f i.val,bound i.isLt⟩
  have inj : Function.Injective p := by
    intro x y eq
    have ex : f x.val=f y.val := congrArg Fin.val eq
    apply Fin.ext
    simp only [f,rearrange] at ex
    split_ifs at ex <;> have := x.isLt <;> have := y.isLt <;> omega
  have normal {x y : Fin n} (h : x.val+1=y.val) : G.Adj (e x) (e y) := by
    have eq : x+1=y := (succ_in_bounds hn x.val (by have := y.isLt; omega)).trans (Fin.ext h)
    exact eq ▸ red x
  have varying (j : ℕ) (hj : j+1<n) :
      f j+1=f (j+1) ∨ f (j+1)+1=f j ∨
      (f j=a-1 ∧ f (j+1)=n-1) ∨ (f j=c ∧ f (j+1)=a) ∨ (f j=b-1 ∧ f (j+1)=c-1) := by
    simp only [f,rearrange]
    split_ifs <;> omega
  apply cycle_from_order hn G cycle e rim p inj ?_ ?_ ?_ ?_ a (by omega) ?_
  · apply Fin.ext
    change f 0=0
    simp [f,rearrange,show 0<a by omega]
  · apply Fin.ext
    change f 1=(1:Fin n).val
    simp [f,rearrange,show 1<a by omega,Nat.mod_eq_of_lt (show 1<n by omega)]
  · intro j hj
    rcases varying j hj with up | down | ⟨x,y⟩ | ⟨x,y⟩ | ⟨x,y⟩
    · exact normal up
    · exact (normal down).symm
    · convert l₁ using 2 <;> apply Fin.ext <;> assumption
    · convert r₁ using 2 <;> apply Fin.ext <;> assumption
    · convert l₂ using 2 <;> apply Fin.ext <;> assumption
  · have eq : p ⟨n-1,by omega⟩ = ⟨b,by omega⟩ := by
      apply Fin.ext
      change f (n-1)=b
      simp only [f,rearrange]
      split_ifs <;> omega
    rw [eq]
    exact r₂
  · intro eq
    have bad : f a=a := congrArg Fin.val eq
    simp only [f,rearrange] at bad
    split_ifs at bad <;> omega

def Orbit {V : Type} {n : ℕ} [NeZero n] (G : SimpleGraph V) (e : Fin n ≃ V)
    (par step : ℕ) : Prop :=
  ∀ j : ℕ, j%2=par → G.Adj (e (j:Fin n)) (e ((j+step:ℕ):Fin n))

private theorem cast_small {n : ℕ} [NeZero n] (i : ℕ) (hi : i<n) :
    (i:Fin n)=⟨i,hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)

private theorem cast_period {n : ℕ} [NeZero n] (i : ℕ) : ((i+n:ℕ):Fin n)=(i:Fin n) := by simp

private theorem spread {V : Type} {n : ℕ} [NeZero n] (G : SimpleGraph V) (e : Fin n ≃ V)
    (symm : ∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2))) :
    ∀ k : ℕ, ∀ i j : ℕ, G.Adj (e (i:Fin n)) (e (j:Fin n)) →
      G.Adj (e ((i+2*k:ℕ):Fin n)) (e ((j+2*k:ℕ):Fin n)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro i j edge
    have shifted := symm _ _ (ih i j edge)
    simpa only [Nat.mul_succ,←Nat.add_assoc,Nat.cast_add,Nat.cast_ofNat] using shifted

private theorem full_orbit {V : Type} {n : ℕ} [NeZero n] (G : SimpleGraph V) (e : Fin n ≃ V)
    (en : n%2=0) (symm : ∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2)))
    (base step : ℕ) (small : base<n)
    (edge : G.Adj (e (base:Fin n)) (e ((base+step:ℕ):Fin n))) :
    Orbit G e (base%2) step := by
  intro j parity
  let k := (j+n-base)/2
  have align : base+2*k = j+n := by dsimp [k]; omega
  have h := spread G e symm k base (base+step) edge
  rw [align,show base+step+2*k=(j+step)+n by omega,cast_period,cast_period] at h
  exact h

private theorem short_orbit {V : Type} {n : ℕ} [NeZero n] (G : SimpleGraph V) (e : Fin n ≃ V)
    (en : n%2=0) (symm : ∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2)))
    (color : ℕ) (mono : ∃ u v : Fin n, u.val%2=color ∧ v.val%2=color ∧ G.Adj (e u) (e v)) :
    ∃ d : ℕ, 2≤d ∧ d%2=0 ∧ 2*d≤n ∧ Orbit G e color d := by
  obtain ⟨u,v,up,vp,adj⟩ := mono
  obtain ⟨x,y,less,xpar,ypar,edge⟩ : ∃ x y : Fin n, x.val<y.val ∧ x.val%2=color ∧ y.val%2=color ∧ G.Adj (e x) (e y) := by
    rcases lt_trichotomy u.val v.val with lt | eq | gt
    · exact ⟨u,v,lt,up,vp,adj⟩
    · exact (adj.ne (congrArg e (Fin.ext eq))).elim
    · exact ⟨v,u,gt,vp,up,adj.symm⟩
  let gap := y.val-x.val
  have defGap : x.val+gap=y.val := by dsimp [gap]; omega
  have gapEven : gap%2=0 := by omega
  have small := y.isLt
  by_cases near : 2*gap≤n
  · refine ⟨gap,by omega,gapEven,near,?_⟩
    rw [←xpar]
    apply full_orbit G e en symm x.val gap x.isLt
    rw [defGap,cast_small _ x.isLt,cast_small _ y.isLt]
    exact edge
  · refine ⟨n-gap,by omega,by omega,by omega,?_⟩
    rw [←ypar]
    apply full_orbit G e en symm y.val (n-gap) y.isLt
    rw [show y.val+(n-gap)=x.val+n by omega,cast_period]
    rw [cast_small _ x.isLt,cast_small _ y.isLt]
    exact edge.symm

private theorem alternating_ordered {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1)))
    (en : n%2=0) (a b : ℕ) (lo : 2≤a) (ab : a<b) (bound : 2*b≤n)
    (ae : a%2=0) (be : b%2=0) (short : Orbit G e 1 a) (long : Orbit G e 0 b) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  apply four_interval_exchange G c e red rim a b (a+b) lo ab (by omega) (by omega)
  · have h := (short (n-1) (by omega)).symm
    rw [show n-1+a=(a-1)+n by omega,cast_period] at h
    simpa only [cast_small (a-1) (by omega : a-1<n),cast_small (n-1) (by omega : n-1<n)] using h
  · have h := (long a ae).symm
    simpa only [cast_small (a+b) (by omega : a+b<n),cast_small a (by omega : a<n)] using h
  · have h := short (b-1) (by omega)
    rw [show b-1+a=a+b-1 by omega] at h
    simpa only [cast_small (b-1) (by omega : b-1<n),cast_small (a+b-1) (by omega : a+b-1<n)] using h
  · have h := (long 0 rfl).symm
    simpa only [Nat.zero_add,Nat.cast_zero,cast_small b (by omega : b<n)] using h

theorem alternating_steps {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin n ≃ V)
    (red : ∀ i : Fin n, G.Adj (e i) (e (i+1)))
    (rim : ∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1)))
    (en : n%2=0) (a b : ℕ) (alo : 2≤a) (blo : 2≤b) (amax : 2*a≤n) (bmax : 2*b≤n)
    (ae : a%2=0) (be : b%2=0) (evenOrbit : Orbit G e 0 a) (oddOrbit : Orbit G e 1 b) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  rcases lt_trichotomy b a with lt | eq | gt
  · exact alternating_ordered G c e red rim en b a blo lt amax be ae oddOrbit evenOrbit
  · subst b
    have lon := evenOrbit 0 rfl
    have ron := oddOrbit 1 rfl
    have hn : 3≤n := by omega
    have far : (0:Fin n) ≠ (a:Fin n)+1 := by
      intro bad
      have val := congrArg Fin.val bad
      simp [Fin.val_add,Nat.mod_eq_of_lt (by omega : a<n),Nat.mod_eq_of_lt (by omega : a+1<n),
        Nat.mod_eq_of_lt (by omega : 1<n)] at val
    have far' : (a:Fin n) ≠ (0:Fin n)+1 := by
      intro bad
      have val := congrArg Fin.val bad
      simp [Nat.mod_eq_of_lt (by omega : a<n),Nat.mod_eq_of_lt (by omega : 1<n)] at val
      omega
    apply paired_chords hn G c e red rim 0 (a:Fin n) (by simpa using lon) far far'
    simpa only [zero_add,Nat.cast_one,Nat.cast_add,add_comm] using ron
  · let e' : Fin n ≃ V := (Equiv.addRight 1).trans e
    have red' (j : Fin n) : G.Adj (e' j) (e' (j+1)) := red (j+1)
    have rim' (x y : V) : s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e' i,e' (i+1)) := by
      rw [rim]
      constructor
      · rintro ⟨i,h⟩
        refine ⟨i-1,?_⟩
        change s(x,y)=s(e (i-1+1),e (i-1+1+1))
        simpa only [sub_add_cancel] using h
      · rintro ⟨i,h⟩
        exact ⟨i+1,h⟩
    apply alternating_ordered G c e' red' rim' en a b alo gt bmax ae be
    · intro j hj
      have h := evenOrbit (j+1) (by omega)
      change G.Adj (e ((j:Fin n)+1)) (e (((j+a:ℕ):Fin n)+1))
      simpa only [show j+1+a=j+a+1 by omega,Nat.cast_add,Nat.cast_one] using h
    · intro j hj
      have h := oddOrbit (j+1) (by omega)
      change G.Adj (e ((j:Fin n)+1)) (e (((j+b:ℕ):Fin n)+1))
      simpa only [show j+1+b=j+b+1 by omega,Nat.cast_add,Nat.cast_one] using h

private theorem unused_neighbor {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (degree : ∀ x, 3≤G.degree x)
    {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c) (u : V) :
    ∃ w, G.Adj u w ∧ s(u,w) ∉ c.edges := by
  classical
  by_contra! all
  have sub : G.neighborSet u ⊆ c.toSubgraph.neighborSet u :=
    fun w hw => Walk.adj_toSubgraph_iff_mem_edges.mpr (all w hw)
  have bound := Set.ncard_le_ncard sub
  rw [hc.1.ncard_neighborSet_toSubgraph_eq_two (hc.2 u)] at bound
  have size : (G.neighborSet u).ncard=G.degree u := by
    rw [Set.ncard_eq_toFinset_card']
    exact G.card_neighborFinset_eq_degree u
  have large := degree u
  omega

private theorem mono_of_unique {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3≤n) (en : n%2=0)
    (G : SimpleGraph V) [DecidableRel G.Adj] (degree : ∀ x, 3≤G.degree x)
    {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c) (e : Fin n ≃ V)
    (rim : ∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1)))
    (unique : ¬ ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset)
    (color : ℕ) (binary : color<2) :
    ∃ u v : Fin n, u.val%2=color ∧ v.val%2=color ∧ G.Adj (e u) (e v) := by
  classical
  by_contra! absent
  let I : Finset V := univ.filter fun x => (e.symm x).val%2 ≠ color
  have inI (x : V) : x ∈ I ↔ (e.symm x).val%2 ≠ color := by simp [I]
  have positive : I.Nonempty := by
    let j : Fin n := ⟨1-color,by omega⟩
    refine ⟨e j,(inI _).mpr ?_⟩
    rw [e.symm_apply_apply]
    change (1-color)%2 ≠ color
    omega
  have opposite (i : Fin n) : (i+1).val%2 ≠ i.val%2 := by
    rw [Fin.val_add,show (1:Fin n).val=1 from Nat.mod_eq_of_lt (by omega : 1<n)]
    by_cases small : i.val+1<n
    · rw [Nat.mod_eq_of_lt small]; omega
    · rw [show i.val+1=n by have := i.isLt; omega,Nat.mod_self]; omega
  apply unique
  apply second_cycle_of_dominated_boundary G v c hc I positive
  · intro x hx y hy edge
    obtain ⟨i,eq⟩ := (rim _ _).mp edge
    have px := (inI _).mp hx
    have py := (inI _).mp hy
    have op := opposite i
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp only [e.symm_apply_apply] at px py <;> omega
  · intro x hx _
    obtain ⟨y,adj,green⟩ := unused_neighbor G degree c hc x
    have xcol : (e.symm x).val%2=color := not_not.mp (fun neq => hx ((inI _).mpr neq))
    have ycol : (e.symm y).val%2 ≠ color := fun eq =>
      absent (e.symm x) (e.symm y) xcol eq (by simpa using adj)
    exact ⟨y,(inI _).mpr ycol,adj,green⟩

theorem second_of_two_step_rotation {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3≤n) (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ x, 3≤G.degree x) {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c)
    (e : Fin n ≃ V)
    (rim : ∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1)))
    (symm : ∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2))) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  have red (i : Fin n) : G.Adj (e i) (e (i+1)) :=
    c.adj_of_mem_edges ((rim _ _).mpr ⟨i,rfl⟩)
  by_cases even : n%2=0
  · by_contra unique
    have mono := mono_of_unique hn even G degree c hc e rim unique
    obtain ⟨a,alo,ae,amax,evenOrbit⟩ := short_orbit G e even symm 0 (mono 0 (by decide))
    obtain ⟨b,blo,be,bmax,oddOrbit⟩ := short_orbit G e even symm 1 (mono 1 (by decide))
    exact unique (alternating_steps G c e red rim even a b alo blo amax bmax ae be evenOrbit oddOrbit)
  · apply second_of_rotation hn G c e red rim _ (degree _)
    intro i j edge
    have step := spread G e symm ((n+1)/2) i.val j.val (by
      simpa only [cast_small _ i.isLt,cast_small _ j.isLt] using edge)
    have len : 2*((n+1)/2)=n+1 := by omega
    rw [len] at step
    simpa only [Nat.cast_add,Fin.natCast_self,Nat.cast_one,zero_add,
      cast_small _ i.isLt,cast_small _ j.isLt] using step

end OMA.SheehanTwoStep

theorem OMA.solution : OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1.H1 := by
  intro V _ _ G _ degree v c hc n _ hn e rim rotates
  exact OMA.SheehanTwoStep.second_of_two_step_rotation hn G degree c hc e rim rotates
