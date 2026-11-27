import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# The Ramsey number R(3,7)

Graver and Yackel established this value in 1968. The lower bound uses a
22-vertex graph in Brendan McKay's collection. TheWaler certified that
witness and reduced the upper bound to degrees five and six in PR #937.
For the needed 18-vertex bound, PR #1995 by Pantelis Papageorgiou incorporates
Yordan's (@ysanatomic) formalization in PR #1699, following Cariolaro (2007).

The 17-vertex extremal bound forces degree six. Counting quadrilaterals then
produces a vertex with a sparse non-neighbourhood. Its possible graphs are
classified using certificates checked by the kernel. The incidence proof
adapts Hiphex's PR #3150, and the degree-sum proof adapts TheWaler's PR #2943.


J. E. Graver and J. Yackel, Some Graph Theoretic Results Associated with
Ramsey's Theorem, Journal of Combinatorial Theory 4 (1968), 125–175.
D. Cariolaro, On the Ramsey number R(3,6) (2007).
-/

section RamseyBounds
open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_three_seven_R1

-- A clique search branches on its least vertex, retaining only larger neighbours.
lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      change (vs.any _) = true
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all

-- First 22-vertex graph in Brendan McKay's collection of Ramsey(3,7) graphs.
-- The table lists each vertex's larger neighbours.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 16000000 in
lemma twentytwo_fails : ¬ IsGraphRamsey 22 3 7 := by
  let edge (i j : ℕ) : Bool :=
    match i with
    | 0 => j == 11 || j == 12 || j == 15 || j == 17 || j == 21
    | 1 => j == 10 || j == 13 || j == 14 || j == 20 || j == 21
    | 2 => j == 9 || j == 16 || j == 17 || j == 18 || j == 19
    | 3 => j == 8 || j == 16 || j == 18 || j == 19 || j == 20
    | 4 => j == 7 || j == 11 || j == 13 || j == 17 || j == 19 || j == 21
    | 5 => j == 6 || j == 10 || j == 12 || j == 18 || j == 19 || j == 21
    | 6 => j == 13 || j == 14 || j == 15 || j == 16 || j == 20
    | 7 => j == 12 || j == 14 || j == 15 || j == 18 || j == 20
    | 8 => j == 9 || j == 13 || j == 14 || j == 17 || j == 21
    | 9 => j == 11 || j == 12 || j == 15 || j == 20
    | 10 => j == 11 || j == 15 || j == 16 || j == 17
    | 11 => j == 14 || j == 18
    | 12 => j == 13 || j == 16
    | 13 => j == 18
    | 14 => j == 19
    | 15 => j == 19
    | 16 => j == 21
    | 17 => j == 20
    | _ => false
  let G : SimpleGraph (Fin 22) :=
    { Adj := fun u v => u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v =>
    inferInstanceAs (Decidable (u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true))
  intro h
  apply h G
  constructor
  · exact exclude_search G 3 (by decide +kernel)
  · exact exclude_search Gᶜ 7 (by decide +kernel)

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

-- The smaller Ramsey upper bound controls the number of non-neighbours.
def H1 : Prop := IsGraphRamsey 18 3 6

-- Only triangle-free graphs of degrees five and six with a degree-six vertex remain.
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ v, G.degree v = 5 ∨ G.degree v = 6) → (∃ v, G.degree v = 6) → ¬ Gᶜ.CliqueFree 7

theorem main : H1 → H2 → SimpleGraph.classicalRamsey 3 7 = 23 := by
  classical
  intro smaller restricted
  have upper : IsGraphRamsey 23 3 7 := by
    rintro G ⟨ht, hc⟩
    have degrees (v : Fin 23) : G.degree v = 5 ∨ G.degree v = 6 := by
      have hd := degree_lt G ht hc v
      have hdc := nonneighbors_lt smaller G ht hc v
      rw [G.degree_compl, Fintype.card_fin] at hdc
      omega
    apply restricted G ht degrees _ hc
    by_contra! h
    have regular (v : Fin 23) : G.degree v = 5 := (degrees v).resolve_right (h v)
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp [regular] at hsum
    omega
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have hmono : Monotone (fun m => IsGraphRamsey m 3 7) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 7
  exact twentytwo_fails (hmono (show n ≤ 22 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_three_seven_R1
end RamseyBounds

section EighteenVertices
/-!
This discharges the 18-vertex hypothesis in TheWaler's reduction of R(3,7)
(open-math-agents PR 937). The upper-bound proof below is by Yordan
(@ysanatomic), from https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1699.
It follows David Cariolaro, *On the Ramsey number R(3,6)* (2007).
The 17-vertex lower-bound construction is unnecessary for this step.
-/

open Finset SimpleGraph

private theorem ramsey36_not_triangle {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (ht : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c :=
  fun hbc ↦ ht _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

private theorem ramsey36_no_three_common {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    {a b c d e : V} (hab : a ≠ b) (hn : ¬ G.Adj a b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e) : False := by
  have hsub : ({c, d, e} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have ht := (Finset.card_le_card hsub).trans (hupper a b hab hn)
  simp [card_insert_of_notMem, hcd, hce, hde] at ht

/-- A triangle-free graph on four vertices of degree two has two common
neighbors in that set for each nonadjacent pair. -/
private theorem ramsey36_no_external_common {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : G.CliqueFree 3)
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (P : Finset V) (hP : P.card = 4)
    (hd : ∀ p ∈ P, (G.neighborFinset p ∩ P).card = 2)
    {p q x : V} (hp : p ∈ P) (hq : q ∈ P) (hx : x ∉ P)
    (hpx : G.Adj p x) (hqx : G.Adj q x) : p = q := by
  by_contra hpq
  have hn := ramsey36_not_triangle ht hpx.symm hqx.symm
  let R := (P.erase p).erase q
  have hqp : q ≠ p := fun he ↦ hpq he.symm
  have hpq' : q ∈ P.erase p := by simp [hqp, hq]
  have hR : R.card = 2 := by
    rw [Finset.card_erase_of_mem hpq', Finset.card_erase_of_mem hp, hP]
  have hnp : G.neighborFinset p ∩ P = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have ⟨ha, hmem⟩ := Finset.mem_inter.mp hy
      have ha' := (G.mem_neighborFinset _ _).mp ha
      simp only [R, Finset.mem_erase]
      exact ⟨fun h ↦ hn (h ▸ ha'), ha'.ne.symm, hmem⟩
    · rw [hR, hd p hp]
  have hnq : G.neighborFinset q ∩ P = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have ⟨ha, hmem⟩ := Finset.mem_inter.mp hy
      have ha' := (G.mem_neighborFinset _ _).mp ha
      simp only [R, Finset.mem_erase]
      exact ⟨ha'.ne.symm, fun h ↦ hn (h ▸ ha'.symm), hmem⟩
    · rw [hR, hd q hq]
  have hsub : insert x R ⊆ G.neighborFinset p ∩ G.neighborFinset q := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp [hpx, hqx]
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (hnp ▸ hy)).1, (Finset.mem_inter.mp (hnq ▸ hy)).1⟩
  have hnX : x ∉ R := fun hm ↦ hx (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
  have hbound := (Finset.card_le_card hsub).trans (hupper p q hpq hn)
  rw [Finset.card_insert_of_notMem hnX, hR] at hbound
  omega

private theorem ramsey36_matching {V : Type} {G : SimpleGraph V}
    {P Q : Finset V} (hcard : P.card = Q.card)
    (hex : ∀ p ∈ P, ∃ q ∈ Q, G.Adj p q)
    (huniq : ∀ {p p' q}, p ∈ P → p' ∈ P → q ∈ Q → G.Adj p q → G.Adj p' q → p = p') :
    ∃ e : ↥P ≃ ↥Q, ∀ p : ↥P, ∀ q : ↥Q, G.Adj p.1 q.1 ↔ e p = q := by
  choose f hf hfAdj using fun p : ↥P ↦ hex p.1 p.2
  let g (p : ↥P) : ↥Q := ⟨f p, hf p⟩
  have hi : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hval : f x = f y := congrArg Subtype.val hxy
    refine huniq x.2 y.2 (hf x) (hfAdj x) ?_
    rw [hval]
    exact hfAdj y
  let e₀ : ↥P ≃ ↥Q := Fintype.equivOfCardEq (by simpa using hcard)
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp (e₀.symm.injective.comp hi)) (e₀.symm q)
    exact ⟨a, e₀.symm.injective ha⟩
  let e := Equiv.ofBijective g ⟨hi, hsurj⟩
  refine ⟨e, fun p q ↦ ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨r, hr⟩ := hsurj q
    have hp : p = r := Subtype.ext <| huniq p.2 r.2 q.2 h
      (congrArg Subtype.val hr ▸ hfAdj r)
    change g p = q
    rwa [hp]
  · rintro rfl
    exact hfAdj p

private theorem ramsey36_last_contradiction {V ι : Type}
    [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : G.CliqueFree 3)
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (p s t w : ι → V) (hc : Fintype.card ι = 4)
    (hps : ∀ i j, G.Adj (p i) (s j) ↔ i = j)
    (hpt : ∀ i j, G.Adj (p i) (t j) ↔ i = j)
    (hpw : ∀ i j, G.Adj (p i) (w j) ↔ i = j)
    (hps' : ∀ i j, p i ≠ s j) (hpt' : ∀ i j, p i ≠ t j)
    (hpw' : ∀ i j, p i ≠ w j) (hst' : ∀ i j, s i ≠ t j) (htw' : ∀ i j, t i ≠ w j)
    (hpd : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (p i) (p j)).card = 2)
    (hws : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (w i) (s j)).card = 2)
    (hwt : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (w i) (t j)).card = 2)
    (hst : ∀ i, ∃ j, G.Adj (s i) (t j)) : False := by
  have := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  let i : ι := Classical.choice inferInstance
  let S := Finset.univ.filter fun j ↦ G.Adj (w i) (s j)
  let T := Finset.univ.filter fun j ↦ G.Adj (w i) (t j)
  have hcS : S.card = 2 := hws i
  have hcT : T.card = 2 := hwt i
  have hiS : i ∉ S := by
    intro h
    exact ramsey36_not_triangle ht ((hpw i i).mpr rfl) ((hps i i).mpr rfl)
      (Finset.mem_filter.mp h).2
  have hiT : i ∉ T := by
    intro h
    exact ramsey36_not_triangle ht ((hpw i i).mpr rfl) ((hpt i i).mpr rfl)
      (Finset.mem_filter.mp h).2
  have hST : (S ∩ T).Nonempty := by
    by_contra h
    have hempty : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hcard := Finset.card_union_add_card_inter S T
    rw [hempty, card_empty, add_zero, hcS, hcT] at hcard
    have hfin : S ∪ T ⊆ (Finset.univ : Finset ι).erase i := by
      intro x hx
      have hne : x ≠ i := fun hx' ↦ by
        subst x
        exact (Finset.mem_union.mp hx).elim hiS hiT
      simp [hne]
    have hle := Finset.card_le_card hfin
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc] at hle
    omega
  obtain ⟨j, hj⟩ := hST
  have hjS := (Finset.mem_inter.mp hj).1
  have hjT := (Finset.mem_inter.mp hj).2
  have hji : j ≠ i := fun h ↦ hiS (h ▸ hjS)
  have hnot (k : ι) (hne : k ≠ i) (hS : k ∈ S) (hT : k ∈ T) :
      ¬ G.Adj (p i) (p k) := by
    intro h
    exact ramsey36_no_three_common hupper (hpw' k i).symm (fun h' ↦ hne ((hpw k i).mp h'.symm))
      (hps' i k) (hpt' i k) (hst' k k) ((hpw i i).mpr rfl).symm
      (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2 h.symm
      ((hps k k).mpr rfl) ((hpt k k).mpr rfl)
  obtain ⟨k, hk⟩ : (S.erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hjS, hcS]
    decide
  obtain ⟨hkj, hkS⟩ := Finset.mem_erase.mp hk
  have hki : k ≠ i := fun e ↦ hiS (e ▸ hkS)
  let I := ((Finset.univ : Finset ι).erase i).erase j
  have hI : I.card = 2 := by
    have hj' : j ∈ (Finset.univ : Finset ι).erase i := by simp [hji]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hc]
  have hP : (Finset.univ.filter fun a ↦ G.Adj (p i) (p a)) = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have h := (Finset.mem_filter.mp ha).2
      simp only [I, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun e ↦ hnot j hji hjS hjT (e ▸ h), fun e ↦ G.loopless.irrefl (p i) (e ▸ h)⟩
    · rw [hI, hpd]
  have hik : G.Adj (p i) (p k) := by
    have hmem : k ∈ I := by simp [I, hki, hkj]
    rw [← hP] at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hkT : k ∉ T := fun h ↦ hnot k hki hkS h hik
  let J := ((Finset.univ : Finset ι).erase i).erase k
  have hJ : J.card = 2 := by
    have hk' : k ∈ (Finset.univ : Finset ι).erase i := by simp [hki]
    rw [Finset.card_erase_of_mem hk', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hc]
  have hT : T = J := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have h₁ : a ≠ i := fun e ↦ hiT (e ▸ ha)
      have h₂ : a ≠ k := fun e ↦ hkT (e ▸ ha)
      simp [J, h₁, h₂]
    · rw [hJ, hcT]
  obtain ⟨a, ha⟩ := hst k
  have hak : a ≠ k := fun e ↦ ramsey36_not_triangle ht ((hps k k).mpr rfl)
    ((hpt k k).mpr rfl) (e ▸ ha)
  have haT : a ∉ T := fun h ↦
    ramsey36_not_triangle ht (Finset.mem_filter.mp hkS).2 (Finset.mem_filter.mp h).2 ha
  have hai : a = i := by
    by_contra hn
    exact haT (hT.symm ▸ (show a ∈ J by simp [J, hn, hak]))
  exact ramsey36_no_three_common hupper (hps' i k) (fun h ↦ hki.symm ((hps i k).mp h))
    (hpw' k i) (hpt' k i) (htw' i i).symm hik ((hpw i i).mpr rfl) ((hpt i i).mpr rfl)
    ((hps k k).mpr rfl).symm (Finset.mem_filter.mp hkS).2.symm (hai ▸ ha)

namespace OMA

open Finset SimpleGraph

private lemma ramsey36_nclique_pair {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b) : G.IsNClique 2 {a,b} := by
  refine ⟨?_, Finset.card_pair hab.ne⟩
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    G.isClique_pair.mpr (fun _ ↦ hab)

private lemma ramsey36_map_clique {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g G) {S : Finset U} {k : ℕ} (hS : H.IsNClique k S) :
    G.IsNClique k (S.map e.toEmbedding) := by
  refine ⟨?_, by rw [Finset.card_map, hS.card_eq]⟩
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
  exact e.toHom.map_adj (hS.isClique hi hj (fun h ↦ hab (congrArg e h)))

private lemma ramsey36_on_subset {V : Type*} [DecidableEq V] (G : SimpleGraph V) {n k : ℕ}
    (hR : RamseyNumbers.IsGraphRamsey n 3 k) (ht : G.CliqueFree 3)
    {S : Finset V} (hcard : n ≤ S.card) :
    ∃ I : Finset V, I ⊆ S ∧ Gᶜ.IsNClique k I := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin n ↪ V :=
    (Finset.equivFinOfCardEq hT).symm.toEmbedding.trans (Function.Embedding.subtype _)
  let H : SimpleGraph (Fin n) := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  let fc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv f
  have htc : H.CliqueFree 3 := ht.comap f.isContained
  have hrc : ¬ Hᶜ.CliqueFree k := fun h ↦ hR H ⟨htc, h⟩
  unfold SimpleGraph.CliqueFree at hrc
  push Not at hrc
  obtain ⟨I, hI⟩ := hrc
  refine ⟨I.map fc.toEmbedding, ?_, ramsey36_map_clique fc hI⟩
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  exact hTS ((Finset.equivFinOfCardEq hT).symm i).property

private lemma ramsey36_neighbors_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : V) :
    Gᶜ.IsClique (G.neighborFinset v : Set V) := by
  intro a ha b hb hab
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, fun hadj ↦ ?_⟩
  apply ht (insert v {a,b})
  exact (ramsey36_nclique_pair hadj).insert (by
    intro w hw
    rcases (by simpa using hw : w = a ∨ w = b) with hwa | hwb
    · rw [hwa]
      exact (G.mem_neighborFinset v a).mp ha
    · rw [hwb]
      exact (G.mem_neighborFinset v b).mp hb)

private lemma ramsey36_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree k) (v : V) :
    G.degree v < k := by
  by_contra! h
  exact (hi.mono h) _ ⟨ramsey36_neighbors_clique G ht v, rfl⟩

private lemma ramsey36_compl_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k : ℕ}
    (hR : RamseyNumbers.IsGraphRamsey n 3 k) (ht : G.CliqueFree 3)
    (hi : Gᶜ.CliqueFree (k + 1)) (v : V) :
    Gᶜ.degree v < n := by
  by_contra! h
  obtain ⟨I, hI, hIc⟩ := ramsey36_on_subset G hR ht (S := Gᶜ.neighborFinset v) h
  exact hi _ (hIc.insert fun a ha ↦ (Gᶜ.mem_neighborFinset v a).mp (hI ha))

private lemma ramsey36_R32 : RamseyNumbers.IsGraphRamsey 3 3 2 := by
  classical
  intro G ⟨ht, hi⟩
  apply ht Finset.univ
  refine ⟨?_, by simp⟩
  intro a _ b _ hab
  by_contra hn
  exact hi _ (ramsey36_nclique_pair ((SimpleGraph.compl_adj G a b).mpr ⟨hab, hn⟩))

private lemma ramsey36_R33 : RamseyNumbers.IsGraphRamsey 6 3 3 := by
  classical
  intro G ⟨ht, hi⟩
  have hd := ramsey36_degree_lt G ht hi 0
  have hc := ramsey36_compl_degree_lt G ramsey36_R32 ht hi 0
  rw [G.degree_compl] at hc
  simp at hc
  omega

private lemma ramsey36_R34 : RamseyNumbers.IsGraphRamsey 9 3 4 := by
  classical
  intro G ⟨ht, hi⟩
  have hd (v : Fin 9) := ramsey36_degree_lt G ht hi v
  have hc (v : Fin 9) := ramsey36_compl_degree_lt G ramsey36_R33 ht hi v
  have heq (v : Fin 9) : G.degree v = 3 := by
    have h := hc v
    rw [G.degree_compl] at h
    simp at h
    have := hd v
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  omega

private lemma ramsey36_R35 : RamseyNumbers.IsGraphRamsey 14 3 5 := by
  classical
  intro G ⟨ht, hi⟩
  have hd := ramsey36_degree_lt G ht hi 0
  have hc := ramsey36_compl_degree_lt G ramsey36_R34 ht hi 0
  rw [G.degree_compl] at hc
  simp at hc
  omega

private lemma ramsey36_degree_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 13)
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 5) (v : V) :
    G.degree v = 4 := by
  have hd := ramsey36_degree_lt G ht hi v
  have hc := ramsey36_compl_degree_lt G ramsey36_R34 ht hi v
  rw [G.degree_compl, hV] at hc
  omega

private lemma ramsey36_degree_at_least_four
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) (v : Fin 18) : 4 ≤ G.degree v := by
  have hc := ramsey36_compl_degree_lt G ramsey36_R35 ht hi v
  rw [G.degree_compl] at hc
  simp at hc
  omega

/-- An eighteen-vertex triangle-free graph without an independent set of size six is 5-regular. -/
lemma ramsey36_degree_eq_five (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) (v : Fin 18) :
    G.degree v = 5 := by
  classical
  have hd (w : Fin 18) := ramsey36_degree_lt G ht hi w
  have hl (w : Fin 18) := ramsey36_degree_at_least_four G ht hi w
  by_contra hneq
  have h4 : G.degree v = 4 := by have := hd v; have := hl v; omega
  let S := Gᶜ.neighborFinset v
  let H := G.induce (S : Set (Fin 18))
  let e : H ↪g G := SimpleGraph.Embedding.induce (G := G) (S : Set (Fin 18))
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have h13 : S.card = 13 := by
    rw [show S = Gᶜ.neighborFinset v from rfl, card_neighborFinset_eq_degree,
      G.degree_compl, h4]
    decide
  have hHV : Fintype.card ↥(S : Set (Fin 18)) = 13 := (Fintype.card_coe S).trans h13
  have hHt : H.CliqueFree 3 := ht.comap e.isContained
  have hHi : Hᶜ.CliqueFree 5 := by
    intro I hI
    apply hi _
    apply (ramsey36_map_clique ec hI).insert
    intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset v z.val).mp z.property
  have h4S (u : Fin 18) (hu : u ∈ S) : (G.neighborFinset u ∩ S).card = 4 := by
    let w : (S : Set (Fin 18)) := ⟨u, hu⟩
    have hw := ramsey36_degree_four H hHV hHt hHi w
    have hmap := G.map_neighborFinset_induce (s := (S : Set (Fin 18))) w
    rw [Finset.toFinset_coe] at hmap
    rw [← hmap, Finset.card_map, card_neighborFinset_eq_degree]
    exact (congrArg (fun J : Fintype (H.neighborSet w) ↦ @SimpleGraph.degree _ H w J)
      (Subsingleton.elim _ _)).trans hw
  have hpos : (G.neighborFinset v).Nonempty := Finset.card_pos.mp (by
    simpa only [card_neighborFinset_eq_degree, h4] using (by decide : 0 < 4))
  obtain ⟨t, htA⟩ := hpos
  have hvt := (G.mem_neighborFinset v t).mp htA
  let A := (G.neighborFinset v).erase t
  let B := (G.neighborFinset t).erase v
  have hAcard : A.card = 3 := by
    simp [A, Finset.card_erase_of_mem htA, h4]
  have hBcard : 3 ≤ B.card := by
    have hvt' := (G.mem_neighborFinset t v).mpr hvt.symm
    have hlt := hl t
    simp only [B, Finset.card_erase_of_mem hvt', card_neighborFinset_eq_degree]
    omega
  obtain ⟨J, hJB, hJcard⟩ := Finset.exists_subset_card_eq hBcard
  have hJS : J ⊆ S := by
    intro u hu
    obtain ⟨huv, huA⟩ := Finset.mem_erase.mp (hJB hu)
    apply (Gᶜ.mem_neighborFinset v u).mpr
    rw [SimpleGraph.compl_adj]
    exact ⟨huv.symm, fun hadj ↦
      (ramsey36_neighbors_clique G ht v htA ((G.mem_neighborFinset v u).mpr hadj)
        ((G.mem_neighborFinset t u).mp huA).ne).2 ((G.mem_neighborFinset t u).mp huA)⟩
  have hSnot {u : Fin 18} (hu : u ∈ G.neighborFinset v) : u ∉ S := by
    intro h
    exact ((Gᶜ.mem_neighborFinset v u).mp h).2 ((G.mem_neighborFinset v u).mp hu)
  have hdis : Disjoint A J := Finset.disjoint_left.mpr fun _ ha hj ↦
    hSnot (Finset.mem_of_mem_erase ha) (hJS hj)
  have hcross (a : Fin 18) (ha : a ∈ A) (b : Fin 18) (hb : b ∈ J) :
      ¬ G.Adj a b := by
    intro hab
    let W := G.neighborFinset b ∩ S
    have hWcard : W.card = 4 := h4S b (hJS hb)
    have haW : a ∉ W := fun h ↦ hSnot (Finset.mem_of_mem_erase ha) (Finset.mem_inter.mp h).2
    have htW : t ∉ W := fun h ↦ hSnot htA (Finset.mem_inter.mp h).2
    have hat := (Finset.mem_erase.mp ha).1
    have hmem : insert t (insert a W) ⊆ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with hzt | hza | hz
      · rw [hzt]
        exact (G.mem_neighborFinset b t).mpr
          ((G.mem_neighborFinset t b).mp (Finset.mem_of_mem_erase (hJB hb))).symm
      · rw [hza]
        exact (G.mem_neighborFinset b a).mpr hab.symm
      · exact (Finset.mem_inter.mp hz).1
    have hcard := Finset.card_le_card hmem
    rw [Finset.card_insert_of_notMem (by simp [hat.symm, htW]),
      Finset.card_insert_of_notMem haW, hWcard, card_neighborFinset_eq_degree] at hcard
    have := hd b
    omega
  apply hi (A ∪ J)
  refine ⟨?_, by rw [Finset.card_union_of_disjoint hdis, hAcard, hJcard]⟩
  rw [Finset.coe_union]
  change ((↑A : Set (Fin 18)) ∪ ↑J).Pairwise Gᶜ.Adj
  rw [Set.pairwise_union]
  refine ⟨(ramsey36_neighbors_clique G ht v).subset ?_,
    (ramsey36_neighbors_clique G ht t).subset ?_, ?_⟩
  · exact fun _ ha ↦ Finset.mem_of_mem_erase ha
  · exact fun _ hb ↦ Finset.mem_of_mem_erase (hJB hb)
  · intro a ha b hb hab
    have h := (SimpleGraph.compl_adj G a b).mpr ⟨hab, hcross a ha b hb⟩
    exact ⟨h, h.symm⟩

/-- Distinct nonadjacent vertices have either one or two common neighbors. -/
lemma ramsey36_common_bounds (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    {x y : Fin 18} (hne : x ≠ y) (hnadj : ¬ G.Adj x y) :
    1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2 := by
  classical
  have hx := ramsey36_degree_eq_five G ht hi x
  have hy := ramsey36_degree_eq_five G ht hi y
  have hcx : Gᶜ.IsNClique 5 (G.neighborFinset x) :=
    ⟨ramsey36_neighbors_clique G ht x, hx⟩
  constructor
  · by_contra! hz
    have hz' : G.neighborFinset x ∩ G.neighborFinset y = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply hi _
    apply hcx.insert (a := y)
    intro z hz
    rw [SimpleGraph.compl_adj]
    constructor
    · intro h
      apply hnadj
      rw [h]
      exact (G.mem_neighborFinset x z).mp hz
    · intro haz
      have him : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
        Finset.mem_inter.mpr ⟨hz, (G.mem_neighborFinset y z).mpr haz⟩
      simp [hz'] at him
  · by_contra! hlarge
    let U := G.neighborFinset x ∪ G.neighborFinset y
    let W := Finset.univ \ insert x (insert y U)
    have hUc : U.card + (G.neighborFinset x ∩ G.neighborFinset y).card = 10 := by
      simpa only [U, card_neighborFinset_eq_degree, hx, hy] using
        Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
    have hUc' := Finset.card_insert_le x (insert y U)
    have hUc'' := Finset.card_insert_le y U
    have hWc : W.card + (insert x (insert y U)).card = 18 := by
      simpa [W] using Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (insert x (insert y U)))
    have hW9 : 9 ≤ W.card := by omega
    obtain ⟨I, hIW, hIc⟩ := ramsey36_on_subset G ramsey36_R34 ht hW9
    have hIx (z : Fin 18) (hz : z ∈ I) : Gᶜ.Adj x z := by
      have h := hIW hz
      simp only [W, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_union, G.mem_neighborFinset, not_or] at h
      exact (SimpleGraph.compl_adj G x z).mpr ⟨fun hxz ↦ h.1 hxz.symm, h.2.2.1⟩
    have hIy (z : Fin 18) (hz : z ∈ I) : Gᶜ.Adj y z := by
      have h := hIW hz
      simp only [W, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_union, G.mem_neighborFinset, not_or] at h
      exact (SimpleGraph.compl_adj G y z).mpr ⟨fun hyz ↦ h.2.1 hyz.symm, h.2.2.2⟩
    apply hi _
    apply (hIc.insert hIx).insert
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hz
    · rw [hzx]
      exact (SimpleGraph.compl_adj G y x).mpr ⟨hne.symm, fun h ↦ hnadj h.symm⟩
    · exact hIy z hz

end OMA

namespace OMA.RamseyThreeSix

open Finset SimpleGraph

lemma has_neighbor_in_fourth_part {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p v t : V} {S P T W : Finset V}
    (cover : ∀ x, x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W)
    (hpv : ¬ G.Adj p v) (hpt : ¬ G.Adj p t) (hdegree : G.degree p = 5)
    (hs : (G.neighborFinset p ∩ S).card = 1) (hp : (G.neighborFinset p ∩ P).card = 2)
    (ht : (G.neighborFinset p ∩ T).card = 1) : ∃ w ∈ W, G.Adj p w := by
  by_contra hnone
  let N := G.neighborFinset p
  have hcover : N ⊆ (N ∩ S) ∪ (N ∩ P) ∪ (N ∩ T) := by
    intro x hx
    have hAdj : G.Adj p x := by simpa [N] using hx
    rcases cover x with rfl | rfl | hS | hP | hT | hW
    · exact (hpv hAdj).elim
    · exact (hpt hAdj).elim
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx, hS⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx, hP⟩))
    · exact mem_union_right _ (mem_inter.mpr ⟨hx, hT⟩)
    · exact (hnone ⟨x, hW, hAdj⟩).elim
  have hcount : N.card ≤ 4 := calc
    N.card ≤ ((N ∩ S) ∪ (N ∩ P) ∪ (N ∩ T)).card := card_le_card hcover
    _ ≤ ((N ∩ S) ∪ (N ∩ P)).card + (N ∩ T).card := card_union_le _ _
    _ ≤ (N ∩ S).card + (N ∩ P).card + (N ∩ T).card :=
      Nat.add_le_add_right (card_union_le _ _) _
    _ = 4 := by simp [N, hs, hp, ht]
  have hcard : N.card = 5 := hdegree
  omega

lemma card_neighborFinset_inter_equiv {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {S : Finset V} (f : ι ≃ ↥S) :
    (G.neighborFinset v ∩ S).card =
      ((Finset.univ : Finset ι).filter (fun i => G.Adj v (f i).val)).card := by
  symm
  refine Finset.card_bij (fun i _ => (f i).val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_inter.mpr ⟨by simpa using (Finset.mem_filter.mp hi).2, (f i).property⟩
  · intro i _ j _ hij
    exact f.injective (Subtype.ext hij)
  · intro x hx
    let y : ↥S := ⟨x, (Finset.mem_inter.mp hx).2⟩
    have hadj : G.Adj v x := by simpa using (Finset.mem_inter.mp hx).1
    refine ⟨f.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa [y] using hadj
    · simp [y]

end OMA.RamseyThreeSix

namespace OMA.ER36

open Finset SimpleGraph

abbrev V := Fin 18

structure LocalConfiguration (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) where
  t : V
  P : Finset V
  S : Finset V
  T : Finset V
  W : Finset V
  t_adj : G.Adj v t
  P_eq : P = (univ.erase v \ G.neighborFinset v).filter
    (fun p ↦ ((G.neighborFinset v) ∩ (G.neighborFinset p)).card = 1)
  S_eq : S = (G.neighborFinset v).erase t
  T_eq : T = (G.neighborFinset t).erase v
  P_card : P.card = 4
  S_card : S.card = 4
  T_card : T.card = 4
  W_card : W.card = 4
  P_outside : P ⊆ univ.erase v \ G.neighborFinset v
  T_outside : T ⊆ univ.erase v \ G.neighborFinset v
  W_outside : W ⊆ univ.erase v \ G.neighborFinset v
  P_disj_T : Disjoint P T
  P_disj_W : Disjoint P W
  T_disj_W : Disjoint T W
  cover : ∀ x : V, x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W
  P_one_S : ∀ p ∈ P, (G.neighborFinset p ∩ S).card = 1
  S_one_P : ∀ s ∈ S, (G.neighborFinset s ∩ P).card = 1
  T_one_S : ∀ u ∈ T, (G.neighborFinset u ∩ S).card = 1
  S_one_T : ∀ s ∈ S, (G.neighborFinset s ∩ T).card = 1
  W_two_S : ∀ w ∈ W, (G.neighborFinset w ∩ S).card = 2
  P_reg : ∀ p ∈ P, (G.neighborFinset p ∩ P).card = 2
  P_has_T : ∀ p ∈ P, (G.neighborFinset p ∩ T).Nonempty

variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem neighborhood_independent (htriangle : G.CliqueFree 3) (v : V)
    {x y : V} (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v) : ¬ G.Adj x y := by
  intro hxy
  exact htriangle {v, x, y}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨(G.mem_neighborFinset _ _).mp hx, (G.mem_neighborFinset _ _).mp hy, hxy⟩)

omit [DecidableRel G.Adj] in
private theorem independent_card_le (hindep : Gᶜ.CliqueFree 6) {A : Finset V}
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) : A.card ≤ 5 := by
  by_contra! hn
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (n := 6) (by omega)
  refine hindep B ⟨?_, hBcard⟩
  intro x hx y hy hxy
  exact ⟨hxy, hA x (hBA hx) y (hBA hy)⟩

omit [DecidableRel G.Adj] in
private theorem independent_insert {A : Finset V} {a : V}
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) (ha : ∀ x ∈ A, ¬ G.Adj a x) :
    ∀ x ∈ insert a A, ∀ y ∈ insert a A, ¬ G.Adj x y := by
  intro x hx y hy
  rcases mem_insert.mp hx with hxa | hxA
  · subst x
    rcases mem_insert.mp hy with hya | hyA
    · subst y
      exact fun hadj ↦ (G.ne_of_adj hadj) rfl
    · exact ha y hyA
  · rcases mem_insert.mp hy with hya | hyA
    · subst y
      exact fun hadj ↦ ha x hxA hadj.symm
    · exact hA x hxA y hyA

private theorem incidence_count (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) = ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  have hd (a : V) (S : Finset V) :
      (G.neighborFinset a ∩ S).card = ∑ x ∈ S, if G.Adj a x then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext x
    simp [and_comm]
  simp_rw [hd]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by
    simp only [G.adj_comm a b]

private theorem reverse_matching {A B : Finset V}
    (hcard : A.card = B.card)
    (hA : ∀ a ∈ A, (G.neighborFinset a ∩ B).card = 1)
    (hB : ∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ 1) :
    ∀ b ∈ B, (G.neighborFinset b ∩ A).card = 1 := by
  have hsum : ∑ b ∈ B, (G.neighborFinset b ∩ A).card = B.card := by
    rw [incidence_count G B A]
    calc
      _ = ∑ _a ∈ A, 1 := Finset.sum_congr rfl hA
      _ = _ := by simpa using hcard
  intro b hb
  have hrest : ∑ z ∈ B.erase b, (G.neighborFinset z ∩ A).card ≤ (B.erase b).card := by
    calc
      _ ≤ ∑ _z ∈ B.erase b, 1 := Finset.sum_le_sum fun z hz ↦ hB z (Finset.mem_of_mem_erase hz)
      _ = _ := by simp
  rw [Finset.card_erase_of_mem hb] at hrest
  rw [← Finset.sum_erase_add B (fun z ↦ (G.neighborFinset z ∩ A).card) hb] at hsum
  have hb' := hB b hb
  have hBpos := Finset.card_pos.mpr ⟨b, hb⟩
  omega

private theorem inter_card_union {B C : Finset V} (A : Finset V) (h : Disjoint B C) :
    (A ∩ (B ∪ C)).card = (A ∩ B).card + (A ∩ C).card := by
  rw [inter_union_distrib_left, Finset.card_union_of_disjoint]
  exact h.mono Finset.inter_subset_right Finset.inter_subset_right

private theorem common_neighbor_unique_pair
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y → ((G.neighborFinset x) ∩ (G.neighborFinset y)).card ≤ 2)
    {v s t a b : V} (hst : s ≠ t) (hsnt : ¬ G.Adj s t)
    (hvs : G.Adj s v) (hvt : G.Adj t v)
    (hav : a ≠ v) (hbv : b ≠ v)
    (hsa : G.Adj s a) (hta : G.Adj t a)
    (hsb : G.Adj s b) (htb : G.Adj t b) : a = b := by
  by_contra hab
  have hsub : ({a, b, v} : Finset V) ⊆ G.neighborFinset s ∩ G.neighborFinset t := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hvs, hvt, hsa, hta, hsb, htb]
  have hcard := Finset.card_le_card hsub
  simp [hab, hav, hbv] at hcard
  have hbound := hcommon s t hst hsnt
  omega

theorem local_configuration (htriangle : G.CliqueFree 3) (hindep : Gᶜ.CliqueFree 6)
    (hdeg : ∀ x, (G.neighborFinset x).card = 5)
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y →
      1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧ (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (v : V) : Nonempty (LocalConfiguration G v) := by
  let U := G.neighborFinset v
  let H := (univ.erase v) \ U
  have hU : U.card = 5 := hdeg v
  have hHmem {x : V} : x ∈ H ↔ x ≠ v ∧ ¬ G.Adj v x := by simp [H, U]
  have hUind {x y : V} (hx : x ∈ U) (hy : y ∈ U) : ¬ G.Adj x y :=
    neighborhood_independent G htriangle v hx hy
  have hHcard : H.card = 12 := by
    have hsub : U ⊆ (univ : Finset V).erase v := by
      intro x hx
      exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).mp hx)).symm, mem_univ _⟩
    dsimp only [H]
    rw [card_sdiff_of_subset hsub, card_erase_of_mem (mem_univ _), hU]
    decide
  have hNoutside {x : V} (hx : x ∈ U) : G.neighborFinset x ∩ H = (G.neighborFinset x).erase v := by
    ext z
    simp only [mem_inter, hHmem, mem_erase, mem_neighborFinset]
    constructor
    · exact fun h ↦ ⟨h.2.1, h.1⟩
    · rintro ⟨hne, hadj⟩
      exact ⟨hadj, hne, fun hz ↦ hUind hx ((G.mem_neighborFinset _ _).mpr hz) hadj⟩
  have hNoutside_card {x : V} (hx : x ∈ U) : (G.neighborFinset x ∩ H).card = 4 := by
    rw [hNoutside hx, card_erase_of_mem, hdeg]
    exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hx).symm
  let P := H.filter fun x ↦ (U ∩ G.neighborFinset x).card = 1
  let Q := H.filter fun x ↦ (U ∩ G.neighborFinset x).card = 2
  have hPsub : P ⊆ H := filter_subset _ _
  have hQsub : Q ⊆ H := filter_subset _ _
  have hPdeg {x : V} (hx : x ∈ P) : (G.neighborFinset x ∩ U).card = 1 := by
    rw [inter_comm]
    exact (mem_filter.mp hx).2
  have hQdeg {x : V} (hx : x ∈ Q) : (G.neighborFinset x ∩ U).card = 2 := by
    rw [inter_comm]
    exact (mem_filter.mp hx).2
  have hPQ : P ∪ Q = H := by
    ext x
    constructor
    · exact fun hx ↦ (mem_union.mp hx).elim (fun hp ↦ hPsub hp) (fun hq ↦ hQsub hq)
    · intro hx
      obtain ⟨hne, hnadj⟩ := hHmem.mp hx
      have h := hcommon v x hne.symm hnadj
      have hc : (U ∩ G.neighborFinset x).card = 1 ∨ (U ∩ G.neighborFinset x).card = 2 := by
        change 1 ≤ (U ∩ G.neighborFinset x).card ∧ (U ∩ G.neighborFinset x).card ≤ 2 at h
        omega
      exact mem_union.mpr (hc.imp (fun hc ↦ mem_filter.mpr ⟨hx, hc⟩)
        (fun hc ↦ mem_filter.mpr ⟨hx, hc⟩))
  have hPQ_disj : Disjoint P Q := by
    refine Finset.disjoint_left.mpr fun x hp hq ↦ ?_
    exact (by decide : 1 ≠ 2) ((hPdeg hp).symm.trans (hQdeg hq))
  have hPcard : P.card = 4 := by
    have htot : (∑ x ∈ U, (G.neighborFinset x ∩ H).card) = 20 := by
      calc
        _ = ∑ _x ∈ U, 4 := sum_congr rfl fun _ hx ↦ hNoutside_card hx
        _ = _ := by simp [hU]
    rw [incidence_count G U H, ← hPQ, sum_union hPQ_disj,
      sum_congr rfl (fun _ hx ↦ hPdeg hx),
      sum_congr rfl (fun _ hx ↦ hQdeg hx)] at htot
    simp at htot
    have hcards := card_union_of_disjoint hPQ_disj
    rw [hPQ, hHcard] at hcards
    omega
  have hQcard : Q.card = 8 := by
    have h := card_union_of_disjoint hPQ_disj
    rw [hPQ, hHcard, hPcard] at h
    omega
  have hPunique {p x y : V} (hp : p ∈ P) (hx : x ∈ U) (hy : y ∈ U)
      (hpx : G.Adj p x) (hpy : G.Adj p y) : x = y :=
    Finset.card_le_one_iff.mp (hPdeg hp).le
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpx, hx⟩)
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpy, hy⟩)
  have hUPle {x : V} (hx : x ∈ U) : (G.neighborFinset x ∩ P).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro p q hp hq
    obtain ⟨hxp', hpP⟩ := mem_inter.mp hp
    obtain ⟨hxq', hqP⟩ := mem_inter.mp hq
    have hxp := (G.mem_neighborFinset _ _).mp hxp'
    have hxq := (G.mem_neighborFinset _ _).mp hxq'
    by_contra hpq
    have hp_out : p ∉ U := (mem_sdiff.mp (hPsub hpP)).2
    have hq_out : q ∉ U := (mem_sdiff.mp (hPsub hqP)).2
    have hn : ¬ G.Adj p q := neighborhood_independent G htriangle x hxp' hxq'
    have hpU (z : V) (hz : z ∈ U.erase x) : ¬ G.Adj p z := fun h ↦
      (mem_erase.mp hz).1 (hPunique hpP (mem_of_mem_erase hz) hx h hxp.symm)
    have hqU (z : V) (hz : z ∈ U.erase x) : ¬ G.Adj q z := fun h ↦
      (mem_erase.mp hz).1 (hPunique hqP (mem_of_mem_erase hz) hx h hxq.symm)
    have hi : ∀ a ∈ insert p (insert q (U.erase x)), ∀ b ∈ insert p (insert q (U.erase x)),
        ¬ G.Adj a b := by
      intro a ha b hb
      simp only [mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
      · exact fun hadj ↦ (G.ne_of_adj hadj) rfl
      · exact hn
      · exact hpU _ hb
      · exact fun h ↦ hn h.symm
      · exact fun hadj ↦ (G.ne_of_adj hadj) rfl
      · exact hqU _ hb
      · exact fun h ↦ hpU _ ha h.symm
      · exact fun h ↦ hqU _ ha h.symm
      · exact hUind (mem_of_mem_erase ha) (mem_of_mem_erase hb)
    have hpc : p ∉ insert q (U.erase x) := by
      simp only [mem_insert]
      exact fun h ↦ h.elim hpq (fun hp ↦ hp_out (mem_of_mem_erase hp))
    have hqc : q ∉ U.erase x := fun hq ↦ hq_out (mem_of_mem_erase hq)
    have hbound := independent_card_le G hindep hi
    rw [card_insert_of_notMem hpc, card_insert_of_notMem hqc, card_erase_of_mem hx, hU] at hbound
    omega
  let S := U.filter fun x ↦ (G.neighborFinset x ∩ P).Nonempty
  have hSsub : S ⊆ U := filter_subset _ _
  have hSPdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ P).card = 1 := by
    have hp := Finset.card_pos.mpr (mem_filter.mp hs).2
    have hle := hUPle (hSsub hs)
    omega
  have hPSdeg {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ S).card = 1 := by
    have heq : G.neighborFinset p ∩ S = G.neighborFinset p ∩ U := by
      ext s
      constructor
      · exact fun h ↦ mem_inter.mpr ⟨(mem_inter.mp h).1, hSsub (mem_inter.mp h).2⟩
      · rintro h
        obtain ⟨hps, hs⟩ := mem_inter.mp h
        exact mem_inter.mpr ⟨hps, mem_filter.mpr ⟨hs, ⟨p, mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hps).symm, hp⟩⟩⟩⟩
    rw [heq, hPdeg hp]
  have hScard : S.card = 4 := by
    have hs : (∑ s ∈ S, (G.neighborFinset s ∩ P).card) = S.card := by
      calc
        _ = ∑ _s ∈ S, 1 := Finset.sum_congr rfl fun _ hs ↦ hSPdeg hs
        _ = _ := by simp
    rw [incidence_count G S P, sum_congr rfl (fun _ hp ↦ hPSdeg hp)] at hs
    simpa [hPcard] using hs.symm
  obtain ⟨t, ht⟩ := card_eq_one.mp
    (show (U \ S).card = 1 by rw [card_sdiff_of_subset hSsub, hU, hScard])
  have htu : t ∈ U := (mem_sdiff.mp (show t ∈ U \ S by simp [ht])).1
  have htS : t ∉ S := (mem_sdiff.mp (show t ∈ U \ S by simp [ht])).2
  have htAdj : G.Adj v t := (G.mem_neighborFinset _ _).mp htu
  have hS_eq : S = U.erase t := by
    ext x
    have heq : (x ∈ U ∧ x ∉ S) ↔ x = t := by
      simpa only [mem_sdiff, mem_singleton] using Finset.ext_iff.mp ht x
    simp only [mem_erase]
    constructor
    · exact fun hx ↦ ⟨fun h ↦ htS (h ▸ hx), hSsub hx⟩
    · exact fun h ↦ by_contra fun hn ↦ h.1 (heq.mp ⟨h.2, hn⟩)
  let T := (G.neighborFinset t).erase v
  have hTH : T ⊆ H := by
    rw [show T = G.neighborFinset t ∩ H from (hNoutside htu).symm]
    exact inter_subset_right
  have hTcard : T.card = 4 := by
    simpa only [T, ← hNoutside htu] using hNoutside_card htu
  have hTP_disj : Disjoint T P := by
    refine Finset.disjoint_left.mpr fun x hxt hxp ↦ htS ?_
    have htx := (G.mem_neighborFinset _ _).mp (mem_of_mem_erase hxt)
    exact mem_filter.mpr ⟨htu, ⟨x, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr htx, hxp⟩⟩⟩
  have hTQ : T ⊆ Q := by
    intro x hx
    have hh : x ∈ P ∪ Q := hPQ ▸ hTH hx
    exact (mem_union.mp hh).resolve_left fun hp ↦ Finset.disjoint_left.mp hTP_disj hx hp
  let W := Q \ T
  have hWQ : W ⊆ Q := sdiff_subset
  have hWcard : W.card = 4 := by
    dsimp only [W]
    rw [card_sdiff_of_subset hTQ, hQcard, hTcard]
  have hWnotT {x : V} (hx : x ∈ W) : x ∉ T := (mem_sdiff.mp hx).2
  have hSTdeg {u : V} (hu : u ∈ T) : (G.neighborFinset u ∩ S).card = 1 := by
    have htu' := (G.mem_neighborFinset _ _).mp (mem_of_mem_erase hu)
    have hmem : t ∈ G.neighborFinset u ∩ U := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr htu'.symm, htu⟩
    rw [hS_eq, inter_erase, card_erase_of_mem hmem, hQdeg (hTQ hu)]
  have hTSle {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ T).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr fun hx hy ↦ ?_
    obtain ⟨hxs, hxT⟩ := mem_inter.mp hx
    obtain ⟨hys, hyT⟩ := mem_inter.mp hy
    have hsv := (G.mem_neighborFinset _ _).mp (hSsub hs)
    have hst : s ≠ t := (mem_erase.mp (hS_eq ▸ hs)).1
    exact common_neighbor_unique_pair G (fun x y hne hadj ↦ (hcommon x y hne hadj).2)
      hst (hUind (hSsub hs) htu) hsv.symm htAdj.symm
      (mem_erase.mp hxT).1 (mem_erase.mp hyT).1
      ((G.mem_neighborFinset _ _).mp hxs) ((G.mem_neighborFinset _ _).mp (mem_of_mem_erase hxT))
      ((G.mem_neighborFinset _ _).mp hys) ((G.mem_neighborFinset _ _).mp (mem_of_mem_erase hyT))
  have hTSdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ T).card = 1 :=
    reverse_matching G (hTcard.trans hScard.symm) (fun _ ↦ hSTdeg) (fun _ ↦ hTSle) s hs
  have hWSdeg {w : V} (hw : w ∈ W) : (G.neighborFinset w ∩ S).card = 2 := by
    have hne := (hHmem.mp (hQsub (hWQ hw))).1
    have hnot : t ∉ G.neighborFinset w ∩ U := by
      intro ht
      have hadj := (G.mem_neighborFinset _ _).mp (mem_inter.mp ht).1
      exact hWnotT hw (mem_erase.mpr ⟨hne, (G.mem_neighborFinset _ _).mpr hadj.symm⟩)
    rw [hS_eq, inter_erase, erase_eq_of_notMem hnot, hQdeg (hWQ hw)]
  have hPW_disj : Disjoint P W := hPQ_disj.mono_right hWQ
  have hTW_disj : Disjoint T W := Finset.disjoint_left.mpr fun _ hx hy ↦ hWnotT hy hx
  have hQTW : T ∪ W = Q := by
    rw [union_comm]
    exact Finset.sdiff_union_of_subset hTQ
  have hcover (x : V) : x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W := by
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxu : x ∈ U
    · by_cases hxt : x = t
      · exact Or.inr (Or.inl hxt)
      · exact Or.inr (Or.inr (Or.inl (hS_eq.symm ▸ mem_erase.mpr ⟨hxt, hxu⟩)))
    · have hxH : x ∈ H := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hxv, mem_univ _⟩, hxu⟩
      rcases mem_union.mp (hPQ.symm ▸ hxH) with hp | hq
      · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      · rcases mem_union.mp (hQTW.symm ▸ hq) with ht | hw
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hw))))
  have hPTnonempty {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ T).Nonempty := by
    obtain ⟨hpv, hvp⟩ := hHmem.mp (hPsub hp)
    have hpt : ¬ G.Adj p t := by
      intro hadj
      exact htS (mem_filter.mpr ⟨htu, ⟨p,
        mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hp⟩⟩⟩)
    have hpne : p ≠ t := fun h ↦ (mem_sdiff.mp (hPsub hp)).2 (h.symm ▸ htu)
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (hcommon p t hpne hpt).1
    obtain ⟨hpu, htu⟩ := mem_inter.mp hu
    have hne : u ≠ v := fun h ↦ hvp (h ▸ ((G.mem_neighborFinset _ _).mp hpu).symm)
    exact ⟨u, mem_inter.mpr ⟨hpu, mem_erase.mpr ⟨hne, htu⟩⟩⟩
  have hSWdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ W).card = 2 := by
    have h := hNoutside_card (hSsub hs)
    rw [← hPQ, inter_card_union _ hPQ_disj, hSPdeg hs, ← hQTW,
      inter_card_union _ hTW_disj, hTSdeg hs] at h
    omega
  have hforce {p q w s r : V} (hp : p ∈ P) (hq : q ∈ P) (hw : w ∈ W)
      (hpq : p ≠ q) (hs : s ∈ S) (hr : r ∈ S) (hsr : s ≠ r)
      (hps : G.Adj p s) (hqr : G.Adj q r) (hws : G.Adj w s) (hwr : G.Adj w r) :
      G.Adj p q := by
    by_contra hnadj
    let R := (U.erase s).erase r
    have hRU {x : V} (hx : x ∈ R) : x ∈ U :=
      mem_of_mem_erase (mem_of_mem_erase hx)
    have hmR {x : V} (hx : x ∈ R) : x ≠ s ∧ x ≠ r :=
      ⟨(mem_erase.mp (mem_of_mem_erase hx)).1, (mem_erase.mp hx).1⟩
    have hRcard : R.card = 3 := by
      dsimp only [R]
      rw [card_erase_of_mem (mem_erase.mpr ⟨hsr.symm, hSsub hr⟩),
        card_erase_of_mem (hSsub hs), hU]
    have hi_R : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y :=
      fun _ hx _ hy ↦ hUind (hRU hx) (hRU hy)
    have hpR {x : V} (hx : x ∈ R) : ¬ G.Adj p x := fun hadj ↦
      (hmR hx).1 (hPunique hp (hRU hx) (hSsub hs) hadj hps)
    have hqR {x : V} (hx : x ∈ R) : ¬ G.Adj q x := fun hadj ↦
      (hmR hx).2 (hPunique hq (hRU hx) (hSsub hr) hadj hqr)
    have hwsr : ({s, r} : Finset V) = G.neighborFinset w ∩ U := by
      apply Finset.eq_of_subset_of_card_le
      · exact insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hws, hSsub hs⟩)
          (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hwr, hSsub hr⟩))
      · rw [card_pair hsr, hQdeg (hWQ hw)]
    have hwR {x : V} (hx : x ∈ R) : ¬ G.Adj w x := by
      intro hadj
      have hmem : x ∈ G.neighborFinset w ∩ U := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hRU hx⟩
      rw [← hwsr] at hmem
      exact (mem_insert.mp hmem).elim (hmR hx).1 (fun h ↦ (hmR hx).2 (mem_singleton.mp h))
    have hpw : ¬ G.Adj p w := neighborhood_independent G htriangle s
      ((G.mem_neighborFinset _ _).mpr hps.symm) ((G.mem_neighborFinset _ _).mpr hws.symm)
    have hqw : ¬ G.Adj q w := neighborhood_independent G htriangle r
      ((G.mem_neighborFinset _ _).mpr hqr.symm) ((G.mem_neighborFinset _ _).mpr hwr.symm)
    have hiw := independent_insert G hi_R (fun _ ↦ hwR)
    have hiq := independent_insert G hiw (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hqw
      · exact hqR hx)
    have hip := independent_insert G hiq (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hnadj
      · rcases mem_insert.mp hx with rfl | hx
        · exact hpw
        · exact hpR hx)
    have hpU : p ∉ U := (mem_sdiff.mp (hPsub hp)).2
    have hqU : q ∉ U := (mem_sdiff.mp (hPsub hq)).2
    have hwU : w ∉ U := (mem_sdiff.mp (hQsub (hWQ hw))).2
    have hpw_ne : p ≠ w := fun h ↦ Finset.disjoint_left.mp hPW_disj hp (h.symm ▸ hw)
    have hqw_ne : q ≠ w := fun h ↦ Finset.disjoint_left.mp hPW_disj hq (h.symm ▸ hw)
    have hw_not : w ∉ R := fun h ↦ hwU (hRU h)
    have hq_not : q ∉ insert w R := by
      rw [mem_insert, not_or]
      exact ⟨hqw_ne, fun h ↦ hqU (hRU h)⟩
    have hp_not : p ∉ insert q (insert w R) := by
      simp only [mem_insert, not_or]
      exact ⟨hpq, hpw_ne, fun h ↦ hpU (hRU h)⟩
    have hsmall := independent_card_le G hindep hip
    rw [card_insert_of_notMem hp_not, card_insert_of_notMem hq_not,
      card_insert_of_notMem hw_not, hRcard] at hsmall
    omega
  have hWother {w s : V} (hw : w ∈ W) (hs : s ∈ S) (hws : G.Adj w s) :
      ∃ r ∈ S, r ≠ s ∧ G.Adj w r := by
    have hmem : s ∈ G.neighborFinset w ∩ S := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hws, hs⟩
    have hcard : ((G.neighborFinset w ∩ S).erase s).card = 1 := by
      rw [card_erase_of_mem hmem, hWSdeg hw]
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (by rw [hcard]; decide)
    obtain ⟨hrs, hm⟩ := mem_erase.mp hr
    exact ⟨r, (mem_inter.mp hm).2, hrs, (G.mem_neighborFinset _ _).mp (mem_inter.mp hm).1⟩
  have hSchoose {s : V} (hs : s ∈ S) : ∃ p ∈ P, G.Adj p s := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset s ∩ P).card by rw [hSPdeg hs]; decide)
    exact ⟨p, (mem_inter.mp hp).2, ((G.mem_neighborFinset _ _).mp (mem_inter.mp hp).1).symm⟩
  have hPdeg_lower {p : V} (hp : p ∈ P) : 2 ≤ (G.neighborFinset p ∩ P).card := by
    obtain ⟨s, hps⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset p ∩ S).card by rw [hPSdeg hp]; decide)
    obtain ⟨hps, hs⟩ := mem_inter.mp hps
    have hpsA := (G.mem_neighborFinset _ _).mp hps
    obtain ⟨w₁, w₂, hne, heq⟩ := Finset.card_eq_two.mp (hSWdeg hs)
    obtain ⟨hsw₁, hw₁⟩ := mem_inter.mp (show w₁ ∈ G.neighborFinset s ∩ W by simp [heq])
    obtain ⟨hsw₂, hw₂⟩ := mem_inter.mp (show w₂ ∈ G.neighborFinset s ∩ W by simp [heq])
    have hw₁s := ((G.mem_neighborFinset _ _).mp hsw₁).symm
    have hw₂s := ((G.mem_neighborFinset _ _).mp hsw₂).symm
    obtain ⟨r₁, hr₁, hr₁s, hw₁r⟩ := hWother hw₁ hs hw₁s
    obtain ⟨r₂, hr₂, hr₂s, hw₂r⟩ := hWother hw₂ hs hw₂s
    have hrne : r₁ ≠ r₂ := by
      intro heq
      subst r₂
      exact hne (common_neighbor_unique_pair G (fun x y hne hadj ↦ (hcommon x y hne hadj).2)
        hr₁s.symm (hUind (hSsub hs) (hSsub hr₁)) (G.adj_symm ((G.mem_neighborFinset _ _).mp (hSsub hs)))
        (G.adj_symm ((G.mem_neighborFinset _ _).mp (hSsub hr₁)))
        (hHmem.mp (hQsub (hWQ hw₁))).1 (hHmem.mp (hQsub (hWQ hw₂))).1
        hw₁s.symm hw₁r.symm hw₂s.symm hw₂r.symm)
    obtain ⟨p₁, hp₁, hp₁r⟩ := hSchoose hr₁
    obtain ⟨p₂, hp₂, hp₂r⟩ := hSchoose hr₂
    have hp₁_ne : p ≠ p₁ := by
      intro heq
      subst p₁
      exact hr₁s (hPunique hp (hSsub hr₁) (hSsub hs) hp₁r hpsA)
    have hp₂_ne : p ≠ p₂ := by
      intro heq
      subst p₂
      exact hr₂s (hPunique hp (hSsub hr₂) (hSsub hs) hp₂r hpsA)
    have hpp_ne : p₁ ≠ p₂ := by
      intro heq
      subst p₂
      exact hrne (hPunique hp₁ (hSsub hr₁) (hSsub hr₂) hp₁r hp₂r)
    have h₁ := hforce hp hp₁ hw₁ hp₁_ne hs hr₁ hr₁s.symm hpsA hp₁r hw₁s hw₁r
    have h₂ := hforce hp hp₂ hw₂ hp₂_ne hs hr₂ hr₂s.symm hpsA hp₂r hw₂s hw₂r
    have hsub : ({p₁, p₂} : Finset V) ⊆ G.neighborFinset p ∩ P :=
      insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h₁, hp₁⟩)
        (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h₂, hp₂⟩))
    simpa only [card_pair hpp_ne] using Finset.card_le_card hsub
  have hPreg {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ P).card = 2 := by
    have hlo := hPdeg_lower hp
    by_contra! hne
    have hbig : 3 ≤ (G.neighborFinset p ∩ P).card := by omega
    have hsub : G.neighborFinset p ∩ P ⊆ P.erase p := by
      intro q hq
      obtain ⟨hpq, hqP⟩ := mem_inter.mp hq
      exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).mp hpq)).symm, hqP⟩
    have hfull : G.neighborFinset p ∩ P = P.erase p :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [card_erase_of_mem hp, hPcard] using hbig)
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset p ∩ P).card)
    have hqP := (mem_inter.mp hq).2
    have hlow := hPdeg_lower hqP
    have hqsub : G.neighborFinset q ∩ P ⊆ {p} := by
      intro r hr
      apply mem_singleton.mpr
      by_contra hrp
      have hrp' : r ∈ G.neighborFinset p ∩ P := by
        rw [hfull]
        exact mem_erase.mpr ⟨hrp, (mem_inter.mp hr).2⟩
      exact neighborhood_independent G htriangle p (mem_inter.mp hq).1 (mem_inter.mp hrp').1
        ((G.mem_neighborFinset _ _).mp (mem_inter.mp hr).1)
    have hsmall := Finset.card_le_card hqsub
    rw [card_singleton] at hsmall
    omega
  exact ⟨{ t := t, P := P, S := S, T := T, W := W, t_adj := htAdj, P_eq := rfl, S_eq := hS_eq
           T_eq := rfl, P_card := hPcard, S_card := hScard, T_card := hTcard, W_card := hWcard
           P_outside := hPsub, T_outside := hTH, W_outside := hWQ.trans hQsub
           P_disj_T := hTP_disj.symm, P_disj_W := hPW_disj, T_disj_W := hTW_disj, cover := hcover
           P_one_S := fun _ ↦ hPSdeg, S_one_P := fun _ ↦ hSPdeg
           T_one_S := fun _ ↦ hSTdeg, S_one_T := fun _ ↦ hTSdeg
           W_two_S := fun _ ↦ hWSdeg, P_reg := fun _ ↦ hPreg, P_has_T := fun _ ↦ hPTnonempty }⟩

end OMA.ER36

private theorem ramsey36_use_configuration (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5)
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y →
      1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (v : Fin 18) (F : OMA.ER36.LocalConfiguration G v)
    (F' : OMA.ER36.LocalConfiguration G F.t) : False := by
  have hupper (x y) (hne : x ≠ y) (hn : ¬ G.Adj x y) := (hcommon x y hne hn).2
  have hexternal {p q x} (hp : p ∈ F.P) (hq : q ∈ F.P) (hx : x ∉ F.P)
      (hpx : G.Adj p x) (hqx : G.Adj q x) : p = q :=
    ramsey36_no_external_common ht hupper F.P F.P_card F.P_reg hp hq hx hpx hqx
  have outside {x} (hx : x ∈ Finset.univ.erase v \ G.neighborFinset v) :
      x ≠ v ∧ ¬ G.Adj v x := by
    obtain ⟨hm, hn⟩ := mem_sdiff.mp hx
    exact ⟨(mem_erase.mp hm).1, fun h ↦ hn ((G.mem_neighborFinset _ _).mpr h)⟩
  have not_t {x} (hv : ¬ G.Adj v x) : x ≠ F.t := fun h ↦ hv (h ▸ F.t_adj)
  have nt_adj {x} (hv : x ≠ v) (hx : x ∉ F.T) : ¬ G.Adj F.t x := by
    intro h
    apply hx
    rw [F.T_eq]
    exact mem_erase.mpr ⟨hv, (G.mem_neighborFinset _ _).mpr h⟩
  have s_not_outside {x} (hs : x ∈ F.S) :
      x ∉ Finset.univ.erase v \ G.neighborFinset v := by
    rw [F.S_eq] at hs
    exact fun h ↦ (mem_sdiff.mp h).2 (mem_of_mem_erase hs)
  have s_disj_p : Disjoint F.S F.P :=
    disjoint_left.mpr fun _ hS hP ↦ s_not_outside hS (F.P_outside hP)
  have s_disj_t : Disjoint F.S F.T :=
    disjoint_left.mpr fun _ hS hT ↦ s_not_outside hS (F.T_outside hT)
  obtain ⟨eS, heS⟩ := ramsey36_matching (G := G) (F.P_card.trans F.S_card.symm)
    (fun p hp ↦ by
      obtain ⟨x,hx⟩ := (Finset.card_pos.mp (by rw [F.P_one_S p hp]; decide))
      exact ⟨x, (mem_inter.mp hx).2, (G.mem_neighborFinset _ _).mp (mem_inter.mp hx).1⟩)
    (fun hp hq hx hpx hqx ↦ (Finset.card_le_one_iff.mp (by rw [F.S_one_P _ hx]))
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpx.symm, hp⟩)
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hqx.symm, hq⟩))
  obtain ⟨eT, heT⟩ := ramsey36_matching (G := G) (F.P_card.trans F.T_card.symm)
    (fun p hp ↦ by
      obtain ⟨x,hx⟩ := F.P_has_T p hp
      exact ⟨x, (mem_inter.mp hx).2, (G.mem_neighborFinset _ _).mp (mem_inter.mp hx).1⟩)
    (fun hp hq hx hpx hqx ↦ hexternal hp hq
      (fun h ↦ Finset.disjoint_left.mp F.P_disj_T h hx) hpx hqx)
  have hPT (p : ↥F.P) : (G.neighborFinset p.val ∩ F.T).card = 1 := by
    have heq : G.neighborFinset p.val ∩ F.T = {(eT p).val} := by
      ext x
      constructor
      · intro hx
        obtain ⟨ha, hm⟩ := mem_inter.mp hx
        exact mem_singleton.mpr (congrArg Subtype.val ((heT p ⟨x, hm⟩).mp
          ((G.mem_neighborFinset _ _).mp ha))).symm
      · intro hx
        obtain rfl := mem_singleton.mp hx
        exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ((heT p (eT p)).mpr rfl), (eT p).property⟩
    rw [heq, card_singleton]
  have hpW (p : Fin 18) (hp : p ∈ F.P) : ∃ w ∈ F.W, G.Adj p w := by
    exact OMA.RamseyThreeSix.has_neighbor_in_fourth_part G F.cover
      (fun h ↦ (outside (F.P_outside hp)).2 h.symm)
      (fun h ↦ nt_adj (outside (F.P_outside hp)).1
        (Finset.disjoint_left.mp F.P_disj_T hp) h.symm)
      (hdeg p) (F.P_one_S _ hp) (F.P_reg _ hp) (hPT ⟨p, hp⟩)
  obtain ⟨eW, heW⟩ := ramsey36_matching (G := G) (F.P_card.trans F.W_card.symm) hpW
    (fun hp hq hx hpx hqx ↦ hexternal hp hq
      (fun h ↦ Finset.disjoint_left.mp F.P_disj_W h hx) hpx hqx)
  have hT_eq {x} (hx : ¬ G.Adj v x) :
      G.neighborFinset F.t ∩ G.neighborFinset x = G.neighborFinset x ∩ F.T := by
    ext y
    rw [F.T_eq]
    simp only [mem_inter, mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨ht, hx'⟩
      exact ⟨hx', fun he ↦ hx (he ▸ hx'.symm), ht⟩
    · rintro ⟨hx', _, ht⟩
      exact ⟨ht, hx'⟩
  have hP'_eq : F.P = F'.P := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have ⟨hnv, hnvAdj⟩ := outside (F.P_outside hx)
      have hntAdj : ¬ G.Adj F.t x := nt_adj hnv (Finset.disjoint_left.mp F.P_disj_T hx)
      rw [F'.P_eq]
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨not_t hnvAdj, mem_univ _⟩,
          fun h ↦ hntAdj ((G.mem_neighborFinset _ _).mp h)⟩,
        by rw [hT_eq hnvAdj]; exact hPT ⟨x, hx⟩⟩
    · rw [F.P_card, F'.P_card]
  have hWT (w : Fin 18) (hw : w ∈ F.W) : (G.neighborFinset w ∩ F.T).card = 2 := by
    have ⟨hnv, hnvAdj⟩ := outside (F.W_outside hw)
    have hntAdj : ¬ G.Adj F.t w := nt_adj hnv
      (fun h ↦ Finset.disjoint_left.mp F.T_disj_W h hw)
    have hne : w ≠ F.t := not_t hnvAdj
    have hb := hcommon F.t w hne.symm hntAdj
    rw [hT_eq hnvAdj] at hb
    have hone : (G.neighborFinset w ∩ F.T).card ≠ 1 := by
      intro h1
      have hP' : w ∈ F'.P := by
        rw [F'.P_eq]
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨hne, mem_univ _⟩,
          fun h ↦ hntAdj ((G.mem_neighborFinset _ _).mp h)⟩, by rw [hT_eq hnvAdj, h1]⟩
      exact Finset.disjoint_left.mp F.P_disj_W (hP'_eq.symm ▸ hP') hw
    omega
  have hmatched {Q : Finset (Fin 18)} (e : ↥F.P ≃ ↥Q)
      (he : ∀ p : ↥F.P, ∀ q : ↥Q, G.Adj p.1 q.1 ↔ e p = q) (i j : ↥F.P) :
      G.Adj i.1 (e j).1 ↔ i = j := (he i (e j)).trans e.injective.eq_iff
  refine ramsey36_last_contradiction ht hupper Subtype.val
    (fun i ↦ (eS i).val) (fun i ↦ (eT i).val) (fun i ↦ (eW i).val)
    (by simpa using F.P_card) (hmatched eS heS) (hmatched eT heT) (hmatched eW heW)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j he
    exact Finset.disjoint_left.mp s_disj_p (he ▸ (eS j).property) i.property
  · intro i j he
    exact Finset.disjoint_left.mp F.P_disj_T i.property (he ▸ (eT j).property)
  · intro i j he
    exact Finset.disjoint_left.mp F.P_disj_W i.property (he ▸ (eW j).property)
  · intro i j he
    exact Finset.disjoint_left.mp s_disj_t (eS i).property (he ▸ (eT j).property)
  · intro i j he
    exact Finset.disjoint_left.mp F.T_disj_W (eT i).property (he ▸ (eW j).property)
  · intro i
    exact (OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G i.val
      (Equiv.refl ↥F.P)).symm.trans (F.P_reg _ i.property)
  · intro i
    rw [← OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G (eW i).val eS]
    exact F.W_two_S _ (eW i).property
  · intro i
    rw [← OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G (eW i).val eT]
    exact hWT _ (eW i).property
  · intro i
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [F.S_one_T _ (eS i).property]; decide)
    obtain ⟨ha, hm⟩ := mem_inter.mp hx
    refine ⟨eT.symm ⟨x, hm⟩, ?_⟩
    rw [eT.apply_symm_apply]
    exact (G.mem_neighborFinset _ _).mp ha

theorem Deldor14.Ramsey.complete_eighteen : OMA.R_RamseyNumbers_ramsey_number_three_seven_R1.H1 := by
  intro G hbad
  classical
  obtain ⟨ht, hi⟩ := hbad
  have hdeg := OMA.ramsey36_degree_eq_five G ht hi
  have hcommon (x y : Fin 18) (hne : x ≠ y) (hn : ¬ G.Adj x y) :=
    OMA.ramsey36_common_bounds G ht hi hne hn
  let v : Fin 18 := 0
  obtain ⟨F⟩ := OMA.ER36.local_configuration G ht hi hdeg hcommon v
  obtain ⟨F'⟩ := OMA.ER36.local_configuration G ht hi hdeg hcommon F.t
  exact ramsey36_use_configuration G ht hdeg hcommon v F F'
end EighteenVertices

section SixteenVertices
/-! Building on the R(3,7) reduction and on the extremal method of Graver and
Yackel (1968), we classify rooted graphs by their independent neighbourhoods.
In a six-regular counterexample the sixteen non-neighbours of a root have
at most 33 edges. Counting quadrilaterals yields a root whose non-neighbour graph has minimum
degree at most three. Bit masks classify the extensions on thirteen bases.
For each candidate, assign integer weights to its independent five-sets.
Each five-set misses the contacts of at most one neighbour of the root,
yet every contact set misses more than a sixth of the total weight.
Graph relabellings and all finite inequalities are checked by the kernel.
The incidence-sum argument follows @TheWaler's R(3,9) reduction. -/
open SimpleGraph
namespace OMA.RamseyFinite

private def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

private theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

private theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

private theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

private theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

private def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

private def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

private def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

private theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

private theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

private def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

private theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

private theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

private def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
private def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

private def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

private theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

private theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

private theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


private def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

private def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

private def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

private def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

private theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

private theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

private theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

private theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

private theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

private theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


private def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

private theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

private theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

private theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

private def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

private theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


private theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

private theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

private def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
private def universal (I : List (Nat × Nat)) := bits (I.map fun _=>true)
private def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

private theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

private theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e] <;> omega

private def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

private def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

private theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

private theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

private def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

private theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0<k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


private def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

private def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

private def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·<k)

private def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

private def assemble (_k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

private def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

private theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0<k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

private def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

private theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

private theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


private def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

private theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

private def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

private theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

private theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

private def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

private theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

private def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤l.length then swapCode i l else l) rows

private theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


private theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

private theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

private def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

private theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

private theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

private theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

private theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

private theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]


private def weighted (cost : Nat × Nat → Nat) (xs : List (Nat × Nat)) := (xs.map cost).sum

private theorem trace_size (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) (positive : ∀ a∈opts,floor≤cost a)
    (n lo : Nat) (acc : List (Nat × Nat)) (st : List Nat) {xs : List (Nat × Nat)}
    (hx : xs∈traverse opts u ending n lo acc st) :
    xs.length = acc.length+n ∧ weighted cost acc+n*floor≤weighted cost xs := by
  induction n generalizing lo acc st with
  | zero =>
    simp only [traverse] at hx
    split at hx
    · obtain rfl := List.mem_singleton.mp hx
      simp
    · contradiction
  | succ n ih =>
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hx
    split at mem
    · obtain ⟨lh,wh⟩ := ih _ _ _ mem
      have h := positive a ha
      simp only [List.length_cons,weighted,List.map_cons,List.sum_cons] at lh wh ⊢
      rw [Nat.succ_mul]
      omega
    · contradiction

private def trimmed (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) : Nat → Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,_,acc,_ => if ending acc then [acc] else []
  | n+1,lo,budget,acc,st => if (n+1)*floor≤budget then opts.flatMap fun a =>
    if lo≤a.1 && a.2 &&& st.headD u == 0 && cost a ≤ budget then
      trimmed opts u ending cost floor n a.1 (budget-cost a) (a::acc) (tick u a.2 st) else []
    else []

private theorem trace_trim (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) (positive : ∀ a∈opts,floor≤cost a)
    (n lo budget : Nat) (acc : List (Nat × Nat)) (st : List Nat) {xs : List (Nat × Nat)}
    (hx : xs∈traverse opts u ending n lo acc st) (hw : weighted cost xs≤budget+weighted cost acc) :
    xs∈trimmed opts u ending cost floor n lo budget acc st := by
  induction n generalizing lo budget acc st with
  | zero => exact hx
  | succ n ih =>
    have needed := (trace_size opts u ending cost floor positive _ _ _ _ hx).2
    have enough : (n+1)*floor ≤ budget := by omega
    simp only [trimmed,if_pos enough,List.mem_flatMap]
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hx
    split at mem
    next hok =>
      have lower := (trace_size opts u ending cost floor positive _ _ _ _ mem).2
      have e : weighted cost (a::acc)=cost a+weighted cost acc := rfl
      rw [e] at lower
      have haff : cost a≤budget := by omega
      refine ⟨a,ha,?_⟩
      simp only [hok,Bool.true_and,haff,decide_true,if_true]
      exact ih _ (budget-cost a) _ _ mem (by rw [e]; omega)
    next => contradiction

private def costAt (b : List Nat) (a : Nat × Nat) := countBits b.length a.1
private def cutGrow (d edgeBound : Nat) (base : List Nat) (opts : List (Nat × Nat)) (u : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (trimmed opts u ending (costAt base) (d-1) d 0 (edgeBound-edges_ base-d) [] lims).map
    (fun cs => attach (cs.reverse.map Prod.fst) base)

private theorem cut_contains {k d edgeBound : Nat} {base : List Nat} {opts : List (Nat × Nat)} {u : Nat} {lims g : List Nat}
    (minimum : ∀ a∈opts,d-1≤costAt base a)
    (hg : g∈assemble k d base opts u lims) (he : edges_ g ≤ edgeBound) :
    g∈cutGrow d edgeBound base opts u lims := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hg
  have sz := (trace_size opts u _ (costAt base) (d-1) minimum _ _ _ _ hx).1
  have ln : xs.length=d := by simpa using sz
  rw [edges_attached] at he
  have sum' : ((xs.reverse.map Prod.fst).map (countBits base.length)).sum = weighted (costAt base) xs := by
    simp [weighted,List.map_reverse,List.sum_reverse,Function.comp_def]
    rfl
  rw [sum'] at he
  simp only [List.length_map,List.length_reverse,ln] at he
  apply List.mem_map.mpr
  refine ⟨xs,trace_trim _ _ _ _ _ minimum _ _ _ _ _ hx ?_,rfl⟩
  change weighted (costAt base) xs ≤ edgeBound-edges_ base-d+0
  omega


private theorem point_weight (b : List Nat) {a : Nat × Nat} (ha : a∈inds b) :
    countBits b.length a.1=a.2 := by
  induction b generalizing a with
  | nil => obtain rfl := List.mem_singleton.mp ha; rfl
  | cons m b ih =>
    simp only [inds,List.mem_append,List.mem_map,List.mem_filter] at ha
    rcases ha with ⟨t,ht,rfl⟩|⟨t,⟨ht,_⟩,rfl⟩
    · simp [ind0,countBits,ih ht]
    · simp [ind1,countBits,half_step,ih ht]; omega
private theorem tag_floor (k d : Nat) (b : List Nat) (a : Nat × Nat) (ha : a∈tagged k d b) :
    d-1 ≤ costAt b a := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  obtain ⟨t,hh,rfl⟩ := List.mem_map.mp hx
  obtain ⟨ht,sz⟩ := List.mem_filter.mp hh
  have ds := of_decide_eq_true (Bool.and_eq_true_iff.mp sz).1
  change d-1≤countBits b.length t.1
  rw [point_weight b ht]
  omega
private theorem parent_low {k d : Nat} {b g : List Nat} (hg : g∈grow k d b) (he : edges_ g≤33) :
    edges_ b+d*(d-1)+d≤33 := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hg
  have ⟨len,wt⟩ := trace_size _ _ _ (costAt b) (d-1) (tag_floor k d b) _ _ _ _ hx
  have e : xs.length=d := by simpa using len
  rw [edges_attached] at he
  have sum' : ((xs.reverse.map Prod.fst).map (countBits b.length)).sum=weighted (costAt b) xs := by
    simp [weighted,List.map_reverse,List.sum_reverse,Function.comp_def]
    rfl
  simp only [List.length_map,List.length_reverse,e,sum'] at he
  change 0+d*(d-1)≤weighted (costAt b) xs at wt
  omega

private def fives (b : List Nat) := ((inds b).filter (fun p=>p.2==5)).map Prod.fst
private def score (W : List (Nat × Nat)) (x : Nat) := ((W.filter (fun w => x &&& w.1 == 0)).map Prod.snd).sum
private def weightCheck (b : List Nat) (W : List (Nat × Nat)) (lo : Nat) :=
  W.all (fun w=>decide (w.1∈fives b)) && (fives b).all (fun x=>decide (lo≤ score W x)) &&
    decide ((W.map Prod.snd).sum<6*lo)

private theorem score_row (w : Nat × Nat) (W : List (Nat × Nat)) (cs : List Nat) :
    (cs.map (score (w::W))).sum =
    (cs.filter (fun x => x &&& w.1 == 0)).length*w.2 + (cs.map (score W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1 = 0
    · simp [score,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [score,e] at ih ⊢
      omega

private theorem pack_bound (b cs : List Nat) (W : List (Nat × Nat))
    (valid : ∀ w∈W,w.1∈fives b) (good : okContacts 7 (inds b) cs=true) :
    (cs.map (score W)).sum ≤ (W.map Prod.snd).sum := by
  induction W with
  | nil =>
    have e : score [] = fun _ => 0 := rfl
    simp [e]
  | cons w W ih =>
    have sub := ih (fun q hq => valid q (.tail _ hq))
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp (valid w (.head _))
    obtain ⟨ht,sz⟩ := List.mem_filter.mp ht
    have sz' : t.2=5 := beq_iff_eq.mp sz
    have n := of_decide_eq_true (List.all_eq_true.mp good t ht)
    rw [eq,sz'] at n
    have le1 : (cs.filter (fun x => x &&& w.1 == 0)).length≤1 := by omega
    have lh := Nat.mul_le_mul_right w.2 le1
    rw [score_row]
    simp only [Nat.one_mul,List.map_cons,List.sum_cons] at lh ⊢
    omega

private theorem pack_lower (cs : List Nat) (W : List (Nat × Nat)) (lo : Nat)
    (h : ∀ x∈cs,lo≤ score W x) : cs.length*lo≤(cs.map (score W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    have hh := ih (fun y hy => h y (.tail _ hy))
    have hx := h x (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons]
    omega

private theorem no_packing (b cs : List Nat) (W : List (Nat × Nat)) (lo : Nat)
    (cert : weightCheck b W lo=true) (len : cs.length=6) (mem : ∀ x∈cs,x∈fives b)
    (good : okContacts 7 (inds b) cs=true) : False := by
  obtain ⟨both,total⟩ := Bool.and_eq_true_iff.mp cert
  obtain ⟨valid,each⟩ := Bool.and_eq_true_iff.mp both
  have up := pack_bound b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have low := pack_lower cs W lo (fun x hx => of_decide_eq_true (List.all_eq_true.mp each x (mem x hx)))
  rw [len] at low
  exact (Nat.not_lt_of_ge (low.trans up)) (of_decide_eq_true total)

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true ∧ cs.Pairwise (·≤·) ∧ (degrees (attach cs b)).all (d≤·)=true
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·)=true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1, horder, final_⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ attach cs b∈grow (k+1) d b ∧ encode G vs=attach cs b := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    have gg := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    rw [enc] at gg
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, gg, enc⟩

theorem classify_by_extension (norm : List Nat → List Nat) (atlas : List (List Nat))
    (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
    (hnorm : ∀ l : List (Fin 23),
      ∃ v,v.Perm l ∧ encode G v=norm (encode G l))
    (classify : ∀ d≤3,∀ b∈levels norm 5 (15-d) 4,∀ cs,Extension 6 d b cs → attach cs b∈grow 6 d b →
      edges_ (attach cs b)≤33 → norm (attach cs b)∈atlas)
    (B : Finset (Fin 23))
    (bc : B.card=16) (internal : (∑ x∈B,(B.filter (G.Adj x)).card)≤66)
    (ht : G.CliqueFree 3) (small : Small G B 6)
    (low : B.Nonempty → ∃ x∈B,(B.filter (G.Adj x)).card≤3) :
    ∃ base : List (Fin 23), base.Nodup ∧ base.toFinset=B ∧ encode G base∈atlas := by
  classical
  obtain ⟨vs,d,b,cs,hv,cover,hd,hb,ex,gg,enc⟩ := rootSplitting G ht norm hnorm 5 B
    (Finset.card_pos.mp (by omega)) 3 small low
  have re : (degrees (encode G vs)).sum=∑ x∈B,(B.filter (G.Adj x)).card := by
    have eq : degrees (encode G vs)=vs.map (fun x => (B.filter (G.Adj x)).card) := by
      rw [degrees_encode]
      apply List.map_congr_left
      intro x _
      rw [sizeAt_finset G hv,cover]
    rw [eq,← List.sum_toFinset _ hv,cover]
  have htri : edges_ (attach cs b)≤33 := by rw [enc,energy] at re; omega
  obtain ⟨ordered,hperm,he⟩ := hnorm vs
  refine ⟨ordered,hperm.nodup_iff.mpr hv,?_,?_⟩
  · rw [← cover]
    ext x
    exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
  · rw [he,enc]
    apply classify d hd b _ cs ex gg htri
    simpa only [bc] using hb

private theorem regular_absurd (norm : List Nat → List Nat) (atlas : List (List Nat))
    (class16 : ∀ d≤3,∀ b∈levels norm 5 (15-d) 4,∀ cs,Extension 6 d b cs →
      attach cs b∈grow 6 d b → edges_ (attach cs b)≤33 → norm (attach cs b)∈atlas)
    (noext : ∀ b∈atlas, ∃ W lo,weightCheck b W lo=true)
    (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7)
    (reg : ∀ x,G.degree x=6) (r : Fin 23)
    (w : Fin 23) (hw : w∈Gᶜ.neighborFinset r)
    (many : 3≤(G.neighborFinset r ∩ G.neighborFinset w).card)
    (hnorm : ∀ l : List (Fin 23), ∃ l',l'.Perm l ∧ encode G l'=norm (encode G l))
    (count : let B := Gᶜ.neighborFinset r; B.card=16 ∧ (∑ x∈B,(B.filter (G.Adj x)).card)≤66) : False := by
  classical
  let A : Finset (Fin 23) := Finset.univ
  let N := G.neighborFinset r
  let B := Gᶜ.neighborFinset r
  have bc : B.card=16 := count.1
  have internal : (∑ x∈B,(B.filter (G.Adj x)).card)≤66 := count.2
  have hreg (x : Fin 23) : (A.filter (G.Adj x)).card=6 := by
    simpa only [A,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree] using reg x
  have bound : Small G A 7 := by
    intro I _ hI
    by_contra! h
    exact (hi.mono h) I ⟨hI,rfl⟩
  have rN : r∉N := by simp [N]
  have rB : r∉B := by simp [B]
  have low : B.Nonempty → ∃ x∈B,(B.filter (G.Adj x)).card≤3 := by
    intro _
    let C := G.neighborFinset r ∩ G.neighborFinset w
    let D := B.filter (G.Adj w)
    have dis : Disjoint C D := by
      apply Finset.disjoint_left.mpr
      intro x hC hD
      have hx := (Finset.mem_inter.mp hC).1
      have hy := (Finset.mem_filter.mp hD).1
      exact ((Gᶜ.mem_neighborFinset ..).mp hy).2 ((G.mem_neighborFinset ..).mp hx)
    have sub : C∪D⊆G.neighborFinset w := by
      intro x hx
      rcases Finset.mem_union.mp hx with c|d
      · exact (Finset.mem_inter.mp c).2
      · exact (G.mem_neighborFinset ..).mpr (Finset.mem_filter.mp d).2
    have le := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint dis,SimpleGraph.card_neighborFinset_eq_degree,reg w] at le
    change 3≤C.card at many
    exact ⟨w,hw,show D.card≤3 by omega⟩
  have small : Small G B 6 := by
    intro S hS hI
    have rn : r∉S := fun h => rB (hS h)
    have ii : Gᶜ.IsClique (insert r S : Finset (Fin 23)) := by
      rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
      exact ⟨hI,fun x hx => (Gᶜ.mem_neighborFinset ..).mp (hS hx)⟩
    have h := bound (insert r S) (Finset.subset_univ _) ii
    rw [Finset.card_insert_of_notMem rn] at h
    omega
  obtain ⟨base,hbn,hb,ab⟩ := classify_by_extension norm atlas G hnorm class16 B bc internal ht small low
  obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
  have ha (x) (hx : x∈front) : G.Adj r x := (G.mem_neighborFinset ..).mp (show x∈N from hf ▸ List.mem_toFinset.mpr hx)
  have hnot (x) (hx : x∈base) : ¬G.Adj r x := ((Gᶜ.mem_neighborFinset ..).mp (show x∈B from hb ▸ List.mem_toFinset.mpr hx)).2
  have dl : front.length=6 := by rw [← List.toFinset_card_of_nodup hfn,hf]; exact reg r
  have nodup : (r::front++base).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · change r ∉ front++base
      rw [List.mem_append,not_or]
      exact ⟨fun h => rN (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
    · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
  have cover : (r::front++base).toFinset=A := by
    ext x
    simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,N,Finset.mem_insert,Finset.mem_union,
      SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj,A,Finset.mem_univ,iff_true]
    by_cases e : x=r <;> by_cases a : G.Adj r x <;> grind
  have hcount (x) (hx : x∈front) : 6≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < 7 := by
    have adj := ha x hx
    have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
      ext y
      simp only [A,B,Finset.mem_filter,Finset.mem_insert,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj]
      constructor
      · intro xy
        by_cases e : y=r
        · exact Or.inl e
        · refine Or.inr ⟨⟨Ne.symm e,fun ra => ?_⟩,xy⟩
          exact G.isIndepSet_neighborSet_of_triangleFree ht r adj ra xy.ne xy
      · rintro (rfl|⟨_,xy⟩)
        · exact adj.symm
        · exact xy
    have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
    have mm := hreg x
    rw [eq,Finset.card_insert_of_notMem rn] at mm
    rw [sizeAt_finset G hbn,hb]; omega
  let cs := contactsOf G base front
  have inc (a) (hh : a∈cs) : a∈fives (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    let S := base.toFinset.filter (G.Adj x)
    have ind := inds_complete G base hbn S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have sz := hcount x hx
    rw [sizeAt_finset G hbn] at sz
    have five : S.card=5 := by change (base.toFinset.filter (G.Adj x)).card=5; omega
    apply List.mem_map.mpr
    refine ⟨_,List.mem_filter.mpr ⟨ind,by simp [five]⟩,?_⟩
    exact (row_mark G base x).symm
  have indep : Gᶜ.IsClique (front.toFinset : Set (Fin 23)) := by
    rw [G.isClique_compl]
    intro x hx y hy e
    exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha x (List.mem_toFinset.mp hx)) (ha y (List.mem_toFinset.mp hy)) e
  have on : (front++base).toFinset⊆A := Finset.subset_univ _
  have ok := ok_contacts G A 7 bound front base (List.nodup_cons.mp nodup).2 on indep
  have len : cs.length=6 := by simp [cs,contactsOf,dl]
  obtain ⟨W,lo,cert⟩ := noext _ ab
  exact no_packing _ _ W lo cert len inc ok

theorem regular_non_neighbors (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (regular : ∀ i, G.degree i = 6) (v : Fin 23) :
    let B := Gᶜ.neighborFinset v
    B.card = 16 ∧ (∑ i ∈ B, (B.filter (G.Adj i)).card) ≤ 66 := by
  classical
  let U : Finset (Fin 23) := Finset.univ
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  change B.card = 16 ∧ _
  constructor
  · change Gᶜ.degree v = 16
    rw [G.degree_compl, Fintype.card_fin, regular]
  let W (S T : Finset (Fin 23)) := ∑ i ∈ S, ∑ j ∈ T, (if G.Adj i j then 1 else 0 : ℕ)
  have sym (S T) : W S T = W T S := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have split (S T) : W S T + W Sᶜ T = W U T := Finset.sum_add_sum_compl S _
  have total (S) : W S U = 6 * S.card := by
    have h : W S U = ∑ i ∈ S, G.degree i := by
      unfold W U
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    simpa [regular, Nat.mul_comm] using h
  have bsub : B ⊆ Nᶜ := by
    intro i h
    exact Finset.mem_compl.mpr fun hn => ((Gᶜ.mem_neighborFinset _ _).mp h).2
      ((G.mem_neighborFinset _ _).mp hn)
  have inc (S T V : Finset (Fin 23)) (h : S ⊆ T) : W S V ≤ W T V :=
    Finset.sum_le_sum_of_subset_of_nonneg h (by intros; omega)
  have hsub : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B bsub).trans ((sym Nᶜ B) ▸ inc B Nᶜ Nᶜ bsub)
  have zero : W N N = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hh : ¬ G.Adj i j := by
      intro edge
      exact G.isIndepSet_neighborSet_of_triangleFree ht v
        ((G.mem_neighborFinset _ _).mp hi) ((G.mem_neighborFinset _ _).mp hj) edge.ne edge
    simp [hh]
  have a := split N U
  have b := split N N
  have c := split N Nᶜ
  have s1 := sym Nᶜ U
  have s2 := sym N U
  have s3 := sym Nᶜ N
  have nc : N.card = 6 := regular v
  have uc : U.card = 23 := by simp [U]
  have t1 := total U
  have t2 := total N
  have count : W B B ≤ 66 := by omega
  have eqn : W B B = ∑ i ∈ B, (B.filter (G.Adj i)).card := by
    unfold W
    exact Finset.sum_congr rfl fun i _ => Finset.sum_boole (R := ℕ) (G.Adj i) B
  exact eqn ▸ count


private structure Move where
  source : List Nat
  target : List Nat
  swaps : List Nat
  verify : relabel swaps source = target
private def decodeRows : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,z => (z % 2^n) :: decodeRows n (z / 2^n)
private def nibbles : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,z => (z%16)::nibbles n (z/16)
private def mkMove (n s t l p : Nat) (h : relabel (nibbles l p) (decodeRows n s)=decodeRows n t) : Move :=
  ⟨decodeRows n s,decodeRows n t,nibbles l p,h⟩
private def trivialMove : Move := ⟨[],[],[],rfl⟩
private def keyRows (xs : List Nat) := xs.foldl (fun n x => (65599*n+x)%4294967291) 0


set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit8_0 (k : Nat) : Move := (if k < 0x96e98a3a then (if k < 0x78b32d61 then (if k < 0x5a7cd088 then mkMove 8 0xc8e4803 0xc8cc103 6 0x564345 (by decide +kernel) else mkMove 8 0xc8e0c03 0xc8cc103 9 0x564534561 (by decide +kernel)) else (if k < 0x926f7a64 then mkMove 8 0xc8e2c03 0xc8d2603 8 0x56453456 (by decide +kernel) else mkMove 8 0xc8d2203 0xc8cc103 2 0x53 (by decide +kernel))) else (if k < 0xcd8ae691 then (if k < 0xb50c23a0 then mkMove 8 0xc8e4c03 0xc8d2603 10 0x6564563456 (by decide +kernel) else mkMove 8 0xc8e2403 0xc8cc103 4 0x5634 (by decide +kernel)) else (if k < 0xe5f5e60f then mkMove 8 0xc8e4903 0xc8d2603 4 0x6453 (by decide +kernel) else mkMove 8 0xc8e2603 0xc8d2603 2 0x64 (by decide +kernel))))

private def orbit8 (k : Nat) : Move := orbit8_0 k

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit4_0 (k : Nat) : Move := mkMove 4 0x31 0x29 1 0x2 (by decide +kernel)

private def orbit4 (k : Nat) : Move := orbit4_0 k

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit13_0 (k : Nat) : Move := mkMove 13 0x3233040e4618c424800f 0x3233040e4a24c223000f 2 0x75 (by decide +kernel)

private def orbit13 (k : Nat) : Move := orbit13_0 k

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit12_0 (k : Nat) : Move := (if k < 0x1751cedf then (if k < 0x8e8d422 then (if k < 0x38448c0 then (if k < 0xc47db3 then mkMove 12 0x3233040e4618c0007 0x3233040e45240c007 27 0x9a89789a6789a56789a456789a2 (by decide +kernel) else mkMove 12 0x3233040e2618c0007 0x3233040e45840c007 27 0x9a89789a6789a56789a456789a2 (by decide +kernel)) else (if k < 0x89e3e88 then mkMove 12 0x3234980e5224c2007 0x3234980e261862007 29 0xa9a89a7896789a56789a456789a12 (by decide +kernel) else mkMove 12 0x3233040e25840c007 0x3233040e45240c007 3 0xa82 (by decide +kernel))) else (if k < 0x14f22115 then (if k < 0x13dbd503 then mkMove 12 0x3233040e05840c007 0x3233040e45040c007 3 0xa82 (by decide +kernel) else mkMove 12 0x3233040e492484007 0x3233040e45840c007 32 0x9a89789a678567845634523123450123 (by decide +kernel)) else (if k < 0x15874c49 then mkMove 12 0x3233040e45848c007 0x3233040e45248c007 36 0xa86453456789a23456789a1230123456789a (by decide +kernel) else mkMove 12 0x3233040e05848c007 0x3233040e45240c007 36 0xa86453456789a23456789a1230123456789a (by decide +kernel)))) else (if k < 0x25b39e4d then (if k < 0x1cdc718f then (if k < 0x1addeb62 then mkMove 12 0x3234980e5224c0007 0x3234980e24c40c007 28 0xa9a89a7896789a56789a456789a2 (by decide +kernel) else mkMove 12 0x3233040e4a24c4007 0x3233040e45248c007 34 0xa896745345678923456789a10123456789 (by decide +kernel)) else (if k < 0x1db06cf7 then mkMove 12 0x3234980e461892007 0x3234980e261862007 3 0x975 (by decide +kernel) else mkMove 12 0x2991074a89489800f 0x3233032631889400f 33 0xa9786756345623456789123456789a012 (by decide +kernel))) else (if k < 0x4197de9d then (if k < 0x2eab7181 then mkMove 12 0x3233040e411882007 0x3233040e45040c007 26 0x9a89789a678956789a45678912 (by decide +kernel) else mkMove 12 0x3233040e4a24c2007 0x3233040e25848c007 26 0x9a89789a6789a56789a456789a (by decide +kernel)) else (if k < 0x4278f7a0 then mkMove 12 0x3234980e4618c2007 0x3234980e2618c2007 3 0x975 (by decide +kernel) else mkMove 12 0x3233040e4a24c0007 0x3233040e45240c007 29 0xa9a89a789a6789a56789a456789a2 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit12_1 (k : Nat) : Move := (if k < 0x5d89bb2b then (if k < 0x54fb73c7 then (if k < 0x4cfc13b5 then (if k < 0x455896d0 then mkMove 12 0x3233040e41248c007 0x3233040e45840c007 27 0x9a89789a678956789a456789212 (by decide +kernel) else mkMove 12 0x3233040e4a248c007 0x3233040e25848c007 6 0xa86421 (by decide +kernel)) else (if k < 0x53e527b5 then mkMove 12 0x3234980e45240c007 0x3234980e24c40c007 3 0x975 (by decide +kernel) else mkMove 12 0x3233040e452484007 0x3233040e45240c007 21 0x9a8678943456234101234 (by decide +kernel))) else (if k < 0x55affa56 then (if k < 0x556564bc then mkMove 12 0x3233040e41848c007 0x3233040e45240c007 27 0x9a89789a678956789a456789212 (by decide +kernel) else mkMove 12 0x3234980e4618c0007 0x3233040e45248c007 42 0xa89a78675678456783456782345671234560123456 (by decide +kernel)) else (if k < 0x5d3f2591 then mkMove 12 0x3234980e2618c0007 0x3233040e45248c007 43 0xa89a786756784567834567892345671234501234567 (by decide +kernel) else mkMove 12 0x3234980e45840c007 0x3233040e45248c007 47 0xa89786756789a4567893456782345678123456780123456 (by decide +kernel)))) else (if k < 0x6379ba78 then (if k < 0x62e48f44 then (if k < 0x5dd450c5 then mkMove 12 0x3234980e25840c007 0x3233040e45248c007 48 0xa89786756789a45678934567234567812345678901234567 (by decide +kernel) else mkMove 12 0x3234980e05840c007 0x3233040e45840c007 19 0x9a89789a54534523450 (by decide +kernel)) else (if k < 0x63546fab then mkMove 12 0x3233040e498812007 0x3233040e45840c007 2 0x64 (by decide +kernel) else mkMove 12 0x3233040e198812007 0x3233040e45240c007 5 0xa8642 (by decide +kernel))) else (if k < 0x6b37707e then (if k < 0x665d25e4 then mkMove 12 0x3233040e098812007 0x3233040e45040c007 5 0xa8642 (by decide +kernel) else mkMove 12 0x3233040e461882007 0x3233040e45240c007 32 0xa8645345678923456789a10123456789 (by decide +kernel)) else (if k < 0x6f83076b then mkMove 12 0x3233040e1a04c4007 0x3233040e45240c007 23 0x9a896789a45345234120123 (by decide +kernel) else mkMove 12 0x3233040e498892007 0x3233040e45248c007 38 0xa8967453456789a23456789a1230123456789a (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit12_2 (k : Nat) : Move := (if k < 0x94ebc9ec then (if k < 0x8e22e79d then (if k < 0x7f04f69d then (if k < 0x7018329f then mkMove 12 0x3233040e198892007 0x3233040e25848c007 2 0x64 (by decide +kernel) else mkMove 12 0x3233040e098892007 0x3233040e45240c007 38 0xa8967453456789a23456789a1230123456789a (by decide +kernel)) else (if k < 0x811e43cd then mkMove 12 0x3233040e1a04c2007 0x3233040e45840c007 32 0x9a878967856745634523412345601234 (by decide +kernel) else mkMove 12 0x3233040e2608c4007 0x3233040e45840c007 30 0x9a8789678567456345234123450123 (by decide +kernel))) else (if k < 0x93ee7a67 then (if k < 0x92d27cbc then mkMove 12 0x3233032629889800f 0x3233032631889400f 6 0xa82312 (by decide +kernel) else mkMove 12 0x3233040e1a04c0007 0x3233040e45040c007 26 0x9a89789a6789a56789a456789a (by decide +kernel)) else (if k < 0x948eaf4c then mkMove 12 0x3233040e412484007 0x3233040e45040c007 28 0xa9a89a789a678956789a45678912 (by decide +kernel) else mkMove 12 0x3233040e4a2484007 0x3233040e45240c007 34 0xa896745345678923456789a10123456789 (by decide +kernel)))) else (if k < 0xa28b221d then (if k < 0x99a30c40 then (if k < 0x95dcdd63 then mkMove 12 0x3233040e2608c2007 0x3233040e45240c007 25 0x9a896789a4534562341201234 (by decide +kernel) else mkMove 12 0x3234980e2610c2007 0x3234980e261842007 28 0xa9a89a7896789a56789a456789a1 (by decide +kernel)) else (if k < 0x9ce5b86a then mkMove 12 0x3234980e4628c2007 0x3234980e261862007 27 0xa989a789a6789a56789456789a1 (by decide +kernel) else mkMove 12 0x3234980e45040c007 0x3233040e45240c007 16 0x9a87894534523450 (by decide +kernel))) else (if k < 0xa8b9500b then (if k < 0xa5a0f8e4 then mkMove 12 0x3233040e490812007 0x3233040e45040c007 2 0x64 (by decide +kernel) else mkMove 12 0x3233040e491882007 0x3233040e45240c007 19 0x9a86789434523410123 (by decide +kernel)) else (if k < 0xa9aa6382 then mkMove 12 0x3233040e2608c0007 0x3233040e45040c007 28 0xa9a89a789a6789a56789a456789a (by decide +kernel) else mkMove 12 0x3234980e2610c0007 0x3233040e45240c007 28 0xa8978456789a3456789234567890 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit12_3 (k : Nat) : Move := (if k < 0xdcd6e0dd then (if k < 0xc7f0f4e7 then (if k < 0xbb48a287 then (if k < 0xaf8c5a1d then mkMove 12 0x3234980e4628c0007 0x3234980e24c40c007 26 0xa989a789a6789a56789456789a (by decide +kernel) else mkMove 12 0x3233040e458892007 0x3233040e25848c007 26 0x9a89789a678956789a45678912 (by decide +kernel)) else (if k < 0xc4a5bc82 then mkMove 12 0x3234980e461882007 0x3234980e261842007 3 0x975 (by decide +kernel) else mkMove 12 0x3233040e49248c007 0x3233040e45248c007 3 0x641 (by decide +kernel))) else (if k < 0xd8dedbd6 then (if k < 0xd4e8ce5e then mkMove 12 0x3233040e461892007 0x3233040e25848c007 4 0xa821 (by decide +kernel) else mkMove 12 0x3233040e49848c007 0x3233040e25848c007 28 0xa9a89a789a678956789a45678912 (by decide +kernel)) else (if k < 0xd9297170 then mkMove 12 0x3233040e4618c4007 0x3233040e25848c007 28 0xa9a89a789a6789a56789a456789a (by decide +kernel) else mkMove 12 0x3233040e2618c4007 0x3233040e45248c007 7 0xa864212 (by decide +kernel)))) else (if k < 0xecac61f5 then (if k < 0xe7bdf95f then (if k < 0xe5aa4b96 then mkMove 12 0x3234980e24840c007 0x3233040e45240c007 13 0x9a78453452340 (by decide +kernel) else mkMove 12 0x3233040e451882007 0x3233040e45840c007 34 0x9a89789a67856784563452312345601234 (by decide +kernel)) else (if k < 0xe98cb0f5 then mkMove 12 0x3234980e1a04c0007 0x3233040e45840c007 23 0x8456789a345678923456780 (by decide +kernel) else mkMove 12 0x3234980e4608c2007 0x3234980e261842007 27 0xa989a789a6789a56789456789a1 (by decide +kernel))) else (if k < 0xef95accf then (if k < 0xecf6f78f then mkMove 12 0x3233040e4618c2007 0x3233040e45248c007 32 0xa8645345678923456789a10123456789 (by decide +kernel) else mkMove 12 0x3233040e2618c2007 0x3233040e45248c007 4 0xa821 (by decide +kernel)) else (if k < 0xfa964fc0 then mkMove 12 0x3233040e418892007 0x3233040e45240c007 29 0xa9a89a789a678956789a456789212 (by decide +kernel) else mkMove 12 0x3233040e491812007 0x3233040e45240c007 2 0x64 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit12_4 (k : Nat) : Move := mkMove 12 0x3234980e4608c0007 0x3233040e45240c007 27 0xa89a7456789a345678923456780 (by decide +kernel)

private def orbit12 (k : Nat) : Move := (if k < 0x6ff2e7d2 then (if k < 0x44b861eb then orbit12_0 k else orbit12_1 k) else (if k < 0xad70925f then orbit12_2 k else (if k < 0xfd5a3714 then orbit12_3 k else orbit12_4 k)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit7_0 (k : Nat) : Move := (if k < 0x51256a35 then (if k < 0x1518d17e then (if k < 0x8ab5aad then (if k < 0x6cbb84b then mkMove 7 0x191c41 0x191981 4 0x4523 (by decide +kernel) else mkMove 7 0x14cc03 0x14c883 5 0x23450 (by decide +kernel)) else (if k < 0x14c70dfc then mkMove 7 0x14c283 0x14c883 11 0x32341230123 (by decide +kernel) else mkMove 7 0x191a41 0x191981 2 0x42 (by decide +kernel))) else (if k < 0x29d45961 then (if k < 0x24b051a2 then mkMove 7 0x14ca03 0x10d283 12 0x234512012345 (by decide +kernel) else mkMove 7 0x191c81 0x191981 6 0x453234 (by decide +kernel)) else (if k < 0x414a8408 then mkMove 7 0x19c203 0x14c883 15 0x434523451230123 (by decide +kernel) else mkMove 7 0x191881 0x191841 2 0x42 (by decide +kernel)))) else (if k < 0x8c12a280 then (if k < 0x72ae89e4 then (if k < 0x6f6a2487 then mkMove 7 0x19a083 0x14c883 18 0x434523451234012345 (by decide +kernel) else mkMove 7 0x191b01 0x191981 8 0x45342345 (by decide +kernel)) else (if k < 0x7db73dba then mkMove 7 0x19ca03 0x14cc83 13 0x3423451230123 (by decide +kernel) else mkMove 7 0x191901 0x191841 4 0x4523 (by decide +kernel))) else (if k < 0x9a5fbbb3 then (if k < 0x8d74355c then mkMove 7 0x14d483 0x14ca83 7 0x5453451 (by decide +kernel) else mkMove 7 0x10cb03 0x10d283 2 0x51 (by decide +kernel)) else (if k < 0x9c3f5e15 then mkMove 7 0x14d283 0x14ca83 12 0x545342123012 (by decide +kernel) else mkMove 7 0x14c903 0x10d283 8 0x52312012 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit7_1 (k : Nat) : Move := (if k < 0xe2d9cb3b then (if k < 0xb0fae5f8 then (if k < 0xa8acd4e6 then mkMove 7 0x19c303 0x14cc83 10 0x3234123012 (by decide +kernel) else mkMove 7 0x14d083 0x14c883 16 0x3423451234501234 (by decide +kernel)) else (if k < 0xbf71092a then mkMove 7 0x19c103 0x14c883 16 0x4345234512301234 (by decide +kernel) else mkMove 7 0x199083 0x14c883 19 0x4345234512345012345 (by decide +kernel))) else (if k < 0xf690b11e then (if k < 0xe84397eb then mkMove 7 0x19b083 0x14cc83 16 0x3423451234012345 (by decide +kernel) else mkMove 7 0x191c01 0x191841 8 0x45342345 (by decide +kernel)) else (if k < 0xf9d5167b then mkMove 7 0x191a01 0x191841 6 0x453234 (by decide +kernel) else mkMove 7 0x19c903 0x14cc83 14 0x34234512301234 (by decide +kernel))))

private def orbit7 (k : Nat) : Move := (if k < 0xa2adccc5 then orbit7_0 k else orbit7_1 k)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_0 (k : Nat) : Move := (if k < 0x823fa85 then (if k < 0x63204f3 then (if k < 0x5a8fbb5 then (if k < 0x482c763 then mkMove 16 0xc8cc103916103001e20a084c100007 0xc8cc103916103001e4112088420007 5 0xec621 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c1900220003 0xc8cc10392893088c003d0820060003 28 0xdecdbcde9789a678545678345678 (by decide +kernel)) else (if k < 0x5e5a0e2 then mkMove 16 0xc8cc103916103001e4111848040007 0xc8cc103914103001cc8430401c0007 85 0xedecdebcdeabc9abc89a786789a56789abc456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel) else mkMove 16 0xc8cc103914103001e24a090c400007 0xc8cc103914103001d204c8410c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel))) else (if k < 0x7b23fa9 then (if k < 0x7a99613 then mkMove 16 0xc8cc10392893088c003e200c080003 0xc8cc10392893088c003d0820060003 57 0xdebabc9abcde89abcd786789abc56789abc456789abcde3456789abc1 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0198280c20007 0xc8cc103914103001e30488401c0007 16 0xdecbcd8978967842 (by decide +kernel)) else (if k < 0x7fc8e80 then mkMove 16 0xc8cc103914903001e3008384020007 0xc8cc103914103001cc842441180007 100 0xdecdbcdeabcd9abcde89abcde789abcde67856789abc456789abcd34567823456789abcd123456789abcde0123456789abcd (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d1800220003 0xc8cc10392893088c003d0820060003 36 0xcbcde9abcd8789abc6789abc567843456789 (by decide +kernel)))) else (if k < 0x970068d then (if k < 0x900ea5e then (if k < 0x8e7d7fe then mkMove 16 0xc8cc10392893088c003e2400480003 0xc8cc10392893088c003d0820060003 42 0xcbcde9abcde89a789abc6789ab567894563456789a (by decide +kernel) else mkMove 16 0xc8cc103914103001cc902441180007 0xc8cc103914103001d244c841080007 75 0xecdbc89abcde789abc6789abcde4563456789abcd234567123456789abcde0123456789abcd (by decide +kernel)) else (if k < 0x90b6314 then mkMove 16 0xc8cc103914103001cc8024411c0007 0xc8cc103914103001cc8430401c0007 39 0xecabc989abc789abc6789abc56789456789a212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3008444180007 0xc8cc103914103001cc0430401c0007 68 0xdecdabcde8789a67854567893456789abcd23456789abcde1234560123456789abcd (by decide +kernel))) else (if k < 0xbf88518 then (if k < 0x9ad742a then mkMove 16 0xc8cc103914903001e0098288420007 0xc8cc103914903001e00588401c0007 67 0xedecdbcdabcde9abcd89abcde789abcde67856789abcd42345123456789abcde012 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30188440c0007 0xc8cc103914103001e20588401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)) else (if k < 0xcbd2cc6 then mkMove 16 0xc8cc103914103001d204c8010c0007 0xc8cc103914103001e20488401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel) else mkMove 16 0xc8cc103914903001e2018284420007 0xc8cc103914903001e18580400c0007 54 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc12 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_1 (k : Nat) : Move := (if k < 0x104a80fa then (if k < 0xde786b9 then (if k < 0xd493b18 then (if k < 0xd22c0fc then mkMove 16 0xc8cc103914103001d044c181880007 0xc8cc103914103001e30484401c0007 58 0xecdab8789abc6789abc5456789a345678923456123456789a012345678 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c8420840003 0xc8cc10392893088c003d0820060003 28 0xedcdeabcd8786789567894534567 (by decide +kernel)) else (if k < 0xdb444bb then mkMove 16 0xc8cc103916103001e4090280c20007 0xc8cc103914103001e30488401c0007 78 0xdecbcdabc9ab89a789a656789abc456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel) else mkMove 16 0xc8cc103914103001e182048c500007 0xc8cc103914103001cc842441180007 35 0xdecdbcdeabc9abc89a789656789a4567821 (by decide +kernel))) else (if k < 0xfd525ef then (if k < 0xe708857 then mkMove 16 0xc8cc103914103001e186008c100007 0xc8cc103914103001cc0430401c0007 78 0xdecdbcdeabcde9abcde89abcde789abcde656789abc4567834562345678123456789abcd012345 (by decide +kernel) else mkMove 16 0xc8cc103914103001e31104440c0007 0xc8cc103914103001d204c8401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel)) else (if k < 0xfff015e then mkMove 16 0xc8cc10392893088c003e4048800003 0xc8cc10392893088c003d0820060003 54 0xdbcab9abcde89abcd789a6789abc56789ab456789abcd3456789ab (by decide +kernel) else mkMove 16 0xc8cc103914103001e3008b04220007 0xc8cc103914103001e30484401c0007 44 0xecdeabc8789678545678934567892345678123401234 (by decide +kernel)))) else (if k < 0x1407d25a then (if k < 0x11f785dc then (if k < 0x10eaf40f then mkMove 16 0xc8cc103914103001e0818a01240007 0xc8cc103914103001cc8420401c0007 34 0xdecdbcdeabc9abc89a789656789a456782 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4111808240007 0xc8cc103914103001cc0430401c0007 35 0xdecabcd8789678545673456234512340123 (by decide +kernel)) else (if k < 0x135a1887 then mkMove 16 0xc8cc103916103001e204c801140007 0xc8cc103914103001d204c8410c0007 79 0xedcdebcdeabc9abc89a7678956789a4567893456789abcde23456789abc1234560123456789abcd (by decide +kernel) else mkMove 16 0xc8cc103914103001e24a090c100007 0xc8cc103914103001d204c8401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel))) else (if k < 0x1798c033 then (if k < 0x174b57ff then mkMove 16 0xc8cc103914103001e3018444080007 0xc8cc103914103001cc8420401c0007 54 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc12 (by decide +kernel) else mkMove 16 0xc8cc103916103001e0198080c20007 0xc8cc103914103001e30488401c0007 80 0xdecdbcdeabc9abc89a789a656789abc456789abc3456789abc23456789ab1234567890123456789a (by decide +kernel)) else (if k < 0x19104b22 then mkMove 16 0xc8cc103914103001e4818a01240007 0xc8cc103914103001cc8430401c0007 34 0xdecdbcdeabc9abc89a789656789a456782 (by decide +kernel) else mkMove 16 0xc8cc103914103001d244c801180007 0xc8cc103914103001e304c0401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_2 (k : Nat) : Move := (if k < 0x2710d847 then (if k < 0x219d5d7a then (if k < 0x2000ca42 then (if k < 0x1f58a4f4 then mkMove 16 0xc8cc103914903001e1818840240007 0xc8cc103914903001e0858840140007 43 0xedecdebcdabcde9ab89abc6789a5456783452345670 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e3004080003 0xc8cc10392893088c003d0820060003 45 0xecdbab9abc89ab789abc6789a567456789abc3456789a (by decide +kernel)) else (if k < 0x202b0057 then mkMove 16 0xc8cc103914103001e300c444180007 0xc8cc103914103001cc4430401c0007 68 0xdecdabcde8789a67854567893456789abcd23456789abcde1234560123456789abcd (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e008c200003 0xc8cc10392893088c003d0820060003 44 0xebc9ab89789abc6789abc56789abcde453456789abc1 (by decide +kernel))) else (if k < 0x268fb678 then (if k < 0x23b53f4b then mkMove 16 0xc8cc103914103001e4192088420007 0xc8cc103914103001d204c8410c0007 16 0xdecbcd8978967842 (by decide +kernel) else mkMove 16 0xc8cc103914103001d044c901880007 0xc8cc103914103001e304c0401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4512 (by decide +kernel)) else (if k < 0x26ecf4ad then mkMove 16 0xc8cc10392893088c003c2440480003 0xc8cc10392893088c003d0820060003 24 0xdecbcd789675674567834567 (by decide +kernel) else mkMove 16 0xc8d2603893103001e10580400c0007 0xc8cc103914903001e2098280420007 36 0xecdbc89abcde789abcd6789abcd534523450 (by decide +kernel)))) else (if k < 0x30555bb5 then (if k < 0x2d4eedb6 then (if k < 0x2c3a8918 then mkMove 16 0xc8cc10392893088c003cc041800003 0xc8cc10392893088c003d0820060003 43 0xabc989abc789abcd678956789ab456789a3456789ab (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e4008180003 0xc8cc10392893088c003d0820060003 45 0xedcbcabcd9a89abc6789a56789abc456789abcde34561 (by decide +kernel)) else (if k < 0x2f2d80cc then mkMove 16 0xc8cc103914103001cc8030411c0007 0xc8cc103914103001cc8424401c0007 39 0xecabc989abc789abc6789abc56789456789a212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3018446080007 0xc8cc103914103001cc8424401c0007 54 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc12 (by decide +kernel))) else (if k < 0x31221f0b then (if k < 0x30a86e47 then mkMove 16 0xc8cc103914103001e4190080c20007 0xc8cc103914103001cc8420401c0007 15 0xdecbcd897896784 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d3202000003 0xc8cc10392893088c003c03c0010003 43 0xecbc9abc8789abc6789ab56789abcd45673456789ab (by decide +kernel)) else (if k < 0x316c740e then mkMove 16 0xc8cc103914103001d044c9010c0007 0xc8cc103914103001e30580401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4512 (by decide +kernel) else mkMove 16 0xc8cc103914103001cc0430411c0007 0xc8cc103914103001cc842441180007 39 0x8978967843456789a2345612345678012345678 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_3 (k : Nat) : Move := (if k < 0x390cad76 then (if k < 0x36494806 then (if k < 0x3539a520 then (if k < 0x35240c26 then mkMove 16 0xc8cc103916103001e0098280c20007 0xc8cc103914103001cc8430401c0007 77 0xdecbcdabc9ab89a789a656789abc456789abc3456789abc23456789ab1234567890123456789a (by decide +kernel) else mkMove 16 0xc8cc103916103001cc802441180007 0xc8cc103914103001d244c901080007 75 0xecdbc89abcde789abc6789abcde4563456789abcd234567123456789abcde0123456789abcd (by decide +kernel)) else (if k < 0x35839e8b then mkMove 16 0xc8cc10392893088c003e40c8000003 0xc8cc10392893088c003c03c0010003 37 0xecdb9789abcd656456789abcde3456789abcd (by decide +kernel) else mkMove 16 0xc8cc103914103001e1918801240007 0xc8cc103914103001e24488401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel))) else (if k < 0x38f18e3e then (if k < 0x36b9526a then mkMove 16 0xc8cc103914103001e244c801180007 0xc8cc103914103001e30484401c0007 67 0xdecabcd89789a67854567893456789abcd23456789abcde1234560123456789abcd (by decide +kernel) else mkMove 16 0xc8cc103916103001d30440401c0007 0xc8cc103914103001d244c841080007 48 0xdecdabcde9abcde8978956789abcde45673423456789ab01 (by decide +kernel)) else (if k < 0x38fe176e then mkMove 16 0xc8cc103914103001e4192488400007 0xc8cc103914103001d244c841080007 16 0xdecbcd8978967842 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4112488420007 0xc8cc103914103001e30488401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel)))) else (if k < 0x3e9cea30 then (if k < 0x3951a058 then (if k < 0x392c3da8 then mkMove 16 0xc8cc10392893088c003cc400840003 0xc8cc10392893088c003d0820060003 54 0xecdebca9abcde89abcde789abc6789abcde56456789a3456789abc (by decide +kernel) else mkMove 16 0xc8cc103914103001e20488411c0007 0xc8cc103914103001d204c8410c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel)) else (if k < 0x3bd00f4c then mkMove 16 0xc8cc10392893088c003e1084200003 0xc8cc10392893088c003d0820060003 39 0xedcdebabcd9abcde8789abcd5678456789abc34 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4192080c20007 0xc8cc103914103001d204c8401c0007 16 0xdecbcd8978967842 (by decide +kernel))) else (if k < 0x40a0545d then (if k < 0x3fbc1f33 then mkMove 16 0xc8cc103914103001cc803301220007 0xc8cc103914103001cc4430401c0007 38 0xa8789678545678934567892345678123401234 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4112488500007 0xc8cc103914103001e30484401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel)) else (if k < 0x40bb9cb5 then mkMove 16 0xc8cc103914103001e20a084c100007 0xc8cc103914103001e20488401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e24a180c100007 0xc8cc103914103001cc8430401c0007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_4 (k : Nat) : Move := (if k < 0x4c88ae1d then (if k < 0x48c47273 then (if k < 0x46593f05 then (if k < 0x454f8e8e then mkMove 16 0xc8cc10392893088c003e4820100003 0xc8cc10392893088c003c03c0010003 37 0xdecbc89abcde789a6789abc56789abcde3456 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4111848040007 0xc8cc103914103001cc8420401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel)) else (if k < 0x46cec743 then mkMove 16 0xc8cc10392893088c003c1820120003 0xc8cc10392893088c003d0820060003 35 0xdecbcdabcd9ab89ab7896789a5674345678 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30180440c0007 0xc8cc103914103001e20488401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel))) else (if k < 0x4b907ece then (if k < 0x4a04cdc5 then mkMove 16 0xc8cc10392893088c003c1180210003 0xc8cc10392893088c003d0820060003 32 0xdcdbcdab9ab789abcd6789abcd456734 (by decide +kernel) else mkMove 16 0xc8cc103914103001e40a184c100007 0xc8cc103914103001e30484401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel)) else (if k < 0x4c1a1f83 then mkMove 16 0xc8cc10392893088c003e000c180003 0xc8cc10392893088c003c03c0010003 42 0xec9789abcde6785678456789abcde3456789abcde1 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4091848140007 0xc8cc103914103001cc842441180007 43 0xdec89789a6789453456789abcd23451234567012345 (by decide +kernel)))) else (if k < 0x4f348e46 then (if k < 0x4dcc14e5 then (if k < 0x4cefcdf1 then mkMove 16 0xc8cc103914103001e4812488500007 0xc8cc103914103001d244c841080007 43 0xdec89a789ab674534567823456789abcd1234012345 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4090280c20007 0xc8cc103914103001cc0430401c0007 15 0xdecbcd897896784 (by decide +kernel)) else (if k < 0x4f00894a then mkMove 16 0xc8cc103914103001d304c8010c0007 0xc8cc103914103001e24488401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel) else mkMove 16 0xc8cc103914103001d244c801880007 0xc8cc103914103001e30484401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel))) else (if k < 0x5155ae4b then (if k < 0x514c3c86 then mkMove 16 0xc8cc103914103001e24a080c140007 0xc8cc103914103001cc902381020007 35 0xdecdbcdeabc9abc89a789656789a4567821 (by decide +kernel) else mkMove 16 0xc8cc103914103001e186008c500007 0xc8cc103914103001d244c841080007 34 0xdecdbcdeabc9abc89a789656789a456781 (by decide +kernel)) else (if k < 0x51afde26 then mkMove 16 0xc8cc10392893088c003d1820020003 0xc8cc10392893088c003c03c0010003 26 0xdcdebcd89a789abcd678956783 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c4801300003 0xc8cc10392893088c003d0820060003 44 0xdba9abc89abc7896789abc56789ab4567893456789a1 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_5 (k : Nat) : Move := (if k < 0x586a8188 then (if k < 0x54d23096 then (if k < 0x52d0d964 then (if k < 0x52c7bf2b then mkMove 16 0xc8cc103914103001e1818a01240007 0xc8cc103914103001cc8424401c0007 34 0xdecdbcdeabc9abc89a789656789a456782 (by decide +kernel) else mkMove 16 0xc8cc103914103001e300c0441c0007 0xc8cc103914103001e30484401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)) else (if k < 0x548f9ad6 then mkMove 16 0xc8cc103914103001e4911801240007 0xc8cc103914103001e30484401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e00cc000003 0xc8cc10392893088c003d0820060003 38 0xedcbcabcd89ab678956789abcd456789abcd34 (by decide +kernel))) else (if k < 0x576c8827 then (if k < 0x56f1ead8 then mkMove 16 0xc8cc10392893088c003c0820160003 0xc8cc10392893088c003d0820060003 27 0xdcdebcd89a789abcd6789567831 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0198080c20007 0xc8cc103914103001e20488401c0007 16 0xdecbcd8978967842 (by decide +kernel)) else (if k < 0x579be45e then mkMove 16 0xc8cc103914103001e3018444480007 0xc8cc103914103001d204c8401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3008384020007 0xc8cc103914103001cc0430401c0007 81 0xdecdbcdeabcde9abcde89abcde789abc67856789ab456789a3456723456789123456789a012345678 (by decide +kernel)))) else (if k < 0x5af9908c then (if k < 0x5a4f52df then (if k < 0x5932864f then mkMove 16 0xc8cc103914103001e4092280c20007 0xc8cc103914103001e30484401c0007 82 0xdeab89789abc6789abcde567456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c4901200003 0xc8cc10392893088c003d0820060003 39 0xedcdebcdabc9ab89a789656789456789a345678 (by decide +kernel)) else (if k < 0x5aa4a4a0 then mkMove 16 0xc8cc103914903001e4018848140007 0xc8cc103914903001e0858840140007 40 0x9678456789abcde3456789abcde23456789ab012 (by decide +kernel) else mkMove 16 0xc8cc103914903001e30480401c0007 0xc8cc103914103001cc842441180007 66 0xdecdbcdabcde9abc89a789656789abcd456783456789a234567812345012345678 (by decide +kernel))) else (if k < 0x5cd1b28a then (if k < 0x5c6d690a then mkMove 16 0xc8cc103914103001e4191808240007 0xc8cc103914103001cc842441180007 16 0xdecbcd8978967841 (by decide +kernel) else mkMove 16 0xc8cc103914103001d244c8010c0007 0xc8cc103914103001e30488401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel)) else (if k < 0x5e402a11 then mkMove 16 0xc8cc103914103001d204c8011c0007 0xc8cc103914103001e204c8401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4198080c20007 0xc8cc103914103001e204c8401c0007 16 0xdecbcd8978967842 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_6 (k : Nat) : Move := (if k < 0x629e7454 then (if k < 0x6046c886 then (if k < 0x5e85da48 then (if k < 0x5e6cc7e8 then mkMove 16 0xc8cc103914103001e4112088c20007 0xc8cc103914103001e204c8401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103914103001e192048c100007 0xc8cc103914103001e30484401c0007 39 0xdecdabcde897896785645673456234512340123 (by decide +kernel)) else (if k < 0x6043900b then mkMove 16 0xc8cc103914103001e182048c140007 0xc8cc103914103001d244c841080007 42 0xec89abcde789abcd6789abcd434562345123450123 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d1002220003 0xc8cc10392893088c003d0820060003 31 0xedecabcd9a789a56789abcd45678931 (by decide +kernel))) else (if k < 0x61e4c353 then (if k < 0x60d69264 then mkMove 16 0xc8cc103914103001e0918809240007 0xc8cc103914103001d204c9010c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde1 (by decide +kernel) else mkMove 16 0xc8cc103914103001d044c101880007 0xc8cc103914103001cc0430401c0007 35 0xdecdbcdeabcd9abcde87856789abcd45212 (by decide +kernel)) else (if k < 0x61f475b5 then mkMove 16 0xc8cc103914103001e20488441c0007 0xc8cc103914103001d204c9010c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30180460c0007 0xc8cc103914103001e24488401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)))) else (if k < 0x66958c81 then (if k < 0x657bfc15 then (if k < 0x64e0ffcc then mkMove 16 0xc8cc103914103001e2192046400007 0xc8cc103914103001e20588401c0007 37 0xecabc989abc789abc6789abc56789456789a2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3018444180007 0xc8cc103914103001cc8430401c0007 54 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc12 (by decide +kernel)) else (if k < 0x66435c54 then mkMove 16 0xc8cc10392893088c003c8400c40003 0xc8cc10392893088c003d0820060003 44 0xdebcab9abc89abc76789abc56789abc4567834567891 (by decide +kernel) else mkMove 16 0xc8cc103914103001e186018c100007 0xc8cc103914103001e30580401c0007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel))) else (if k < 0x6ae7b67c then (if k < 0x6989c2a5 then mkMove 16 0xc8cc10392893088c003c1980200003 0xc8cc10392893088c003c03c0010003 24 0xdecbcd789675674567834567 (by decide +kernel) else mkMove 16 0xc8d2603893103001e106018c000007 0xc8cc103914903001e2098280420007 41 0xdbc8786756789abcde3456789abcd23456789abc0 (by decide +kernel)) else (if k < 0x6b149e32 then mkMove 16 0xc8cc103916103001e30480401c0007 0xc8cc103914103001d244c841080007 47 0xdecdabcde9abcde8978956789abcd4563423456789abc01 (by decide +kernel) else mkMove 16 0xc8cc103914903001e24a080c100007 0xc8cc103914103001cc8424401c0007 49 0xedcdebcdabc9ab89a78967895678945673456234512340123 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_7 (k : Nat) : Move := (if k < 0x75ac5d5b then (if k < 0x70b22d05 then (if k < 0x6f6b4ba0 then (if k < 0x6f56dd2a then mkMove 16 0xc8cc103914903001e182048c400007 0xc8cc103914903001e10580401c0007 39 0xdecdabcde897896785645673456234512340123 (by decide +kernel) else mkMove 16 0xc8cc103914103001e186048c100007 0xc8cc103914103001e304c0401c0007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel)) else (if k < 0x6f7310d6 then mkMove 16 0xc8cc103914103001e4811a01240007 0xc8cc103914103001cc4430401c0007 34 0xdecdbcdeabc9abc89a789656789a456782 (by decide +kernel) else mkMove 16 0xc8cc103914103001d844c101880007 0xc8cc103914103001cc842441180007 68 0xdecdbcde989a789a674563456789abcde23456789abcde12345670123456789abcde (by decide +kernel))) else (if k < 0x738c5d14 then (if k < 0x715784e4 then mkMove 16 0xc8cc103914103001cc048381820007 0xc8cc103914103001d244c841080007 69 0xdecdbcde989789678945345678923456789abcde123456789abcde0123456789abcde (by decide +kernel) else mkMove 16 0xc8d2603893103001e4010848140007 0xc8cc103914903001e2098280420007 49 0xdcbabc8789ab656789abcde43456789abcde23456789ab012 (by decide +kernel)) else (if k < 0x74ca9eff then mkMove 16 0xc8cc103914103001e0098280c20007 0xc8cc103914103001cc0430401c0007 77 0xdecbcdabc9ab89a789a656789abc456789abc3456789abc23456789ab1234567890123456789a (by decide +kernel) else mkMove 16 0xc8cc103914103001cc802441180007 0xc8cc103914103001cc0430401c0007 39 0xa87896785645678934567892345678123401234 (by decide +kernel)))) else (if k < 0x79ff2e48 then (if k < 0x78471eac then (if k < 0x76732100 then mkMove 16 0xc8cc103914103001e4112488c00007 0xc8cc103914103001e304c0401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103914903001e4090848140007 0xc8cc103914903001e10580401c0007 81 0xdeab8789abc6789abcde567456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel)) else (if k < 0x787888e1 then mkMove 16 0xc8cc10392893088c003e0820120003 0xc8cc10392893088c003d0820060003 29 0xedecdebcdeabcd9abcde89abcd456 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4912088420007 0xc8cc103914103001d204c9010c0007 16 0xdecbcd8978967842 (by decide +kernel))) else (if k < 0x7a3a3cf8 then (if k < 0x7a0aaf6e then mkMove 16 0xc8cc103914103001e2112446400007 0xc8cc103914103001e30580401c0007 37 0xecabc989abc789abc6789abc56789456789a2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e204c8011c0007 0xc8cc103914103001d204c8401c0007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel)) else (if k < 0x7a46d2e5 then mkMove 16 0xc8cc103914103001e3110444080007 0xc8cc103914103001cc8420401c0007 33 0xdecdbcdeabcd9abcde87856789abcd451 (by decide +kernel) else mkMove 16 0xc8cc103914903001e101884c040007 0xc8cc103914903001e0858840140007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_8 (k : Nat) : Move := (if k < 0x80c8475c then (if k < 0x7bcb62f8 then (if k < 0x7aed577f then (if k < 0x7ada9c4d then mkMove 16 0xc8cc103914903001e182048c100007 0xc8cc103914103001e30580401c0007 39 0xdecdabcde897896785645673456234512340123 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4098280c20007 0xc8cc103914103001e304c0401c0007 16 0xdecbcd8978967842 (by decide +kernel)) else (if k < 0x7b57b00e then mkMove 16 0xc8cc10392893088c003cc440800003 0xc8cc10392893088c003c03c0010003 36 0xcbcde9abcd8789abc6789abc567843456789 (by decide +kernel) else mkMove 16 0xc8cc103916103001e24a080c100007 0xc8cc103914103001cc8430401c0007 49 0xedcdebcdabc9ab89a78967895678945673456234512340123 (by decide +kernel))) else (if k < 0x7d29dae1 then (if k < 0x7ce13ac2 then mkMove 16 0xc8cc103914103001e2110444480007 0xc8cc103914103001e20488401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0818a09240007 0xc8cc103914103001cc902381020007 62 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde212 (by decide +kernel)) else (if k < 0x7dcb2ad1 then mkMove 16 0xc8cc103914903001e4910801240007 0xc8cc103914103001cc4430401c0007 48 0xdecdbcdeabc9abc89a789656789456734562345612340123 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4910a01240007 0xc8cc103914103001e304c0401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel)))) else (if k < 0x85b4f08f then (if k < 0x84050a2a then (if k < 0x83b48d70 then mkMove 16 0xc8cc103914103001e4118088c20007 0xc8cc103914103001d204c8401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103916103001cc802381020007 0xc8cc103914103001cc842381020007 102 0xdecdbcdeabcd9abcde89abcde789abcde67856789abcd456789abcde34567823456789abcd123456789abcde0123456789abcd (by decide +kernel)) else (if k < 0x84a6c5da then mkMove 16 0xc8cc103914103001e20a084c500007 0xc8cc103914103001d204c8410c0007 35 0xdecdbcdeabc9abc89a789656789a4567812 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e2024080003 0xc8cc10392893088c003d0820060003 39 0xa897896789abcde56789abcd4563456789abcde (by decide +kernel))) else (if k < 0x8746168f then (if k < 0x865ac971 then mkMove 16 0xc8cc103914103001e3112444080007 0xc8cc103914103001cc902381020007 53 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc2 (by decide +kernel) else mkMove 16 0xc8cc103914903001e3008844140007 0xc8cc103914903001e10580401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)) else (if k < 0x87a51c43 then mkMove 16 0xc8cc103914103001e2112444480007 0xc8cc103914103001d204c9010c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914903001e4112088420007 0xc8cc103914103001e24488401c0007 95 0xdecbcdeabc9abcd89abc789abcde67856789ab456789abcd3456789abc23456789ab123456789abcde0123456789abc (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_9 (k : Nat) : Move := (if k < 0x8eb54013 then (if k < 0x8aa8fc10 then (if k < 0x89f35905 then (if k < 0x88908ad2 then mkMove 16 0xc8cc103914103001e4112288420007 0xc8cc103914103001e24488401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103916103001d244c801080007 0xc8cc103914103001d244c841080007 56 0xecdabc9abcde89abcd789abc56789abcde456789abc3456789a23450 (by decide +kernel)) else (if k < 0x8a975df9 then mkMove 16 0xc8cc10392893088c003e208c000003 0xc8cc10392893088c003d0820060003 66 0xedcdebcdeabcde9abcde89abcde789678956789abcde456789abcd3456789abcde (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e4008900003 0xc8cc10392893088c003d0820060003 59 0xedcdebcdabcde9abcd89abcde76756789abcde456789abc3456789abcd1 (by decide +kernel))) else (if k < 0x8c55d151 then (if k < 0x8ad2894f then mkMove 16 0xc8cc103916103001e182048c100007 0xc8cc103914103001e304c0401c0007 39 0xdecdabcde897896785645673456234512340123 (by decide +kernel) else mkMove 16 0xc8cc103914103001cc848381020007 0xc8cc103914103001cc902381020007 37 0xecabc989abc789abc6789abc56789456789a2 (by decide +kernel)) else (if k < 0x8d6cecbd then mkMove 16 0xc8cc10392893088c003c24200c0003 0xc8cc10392893088c003d0820060003 37 0xdecdbcdabcde9ab89abc78967895645634567 (by decide +kernel) else mkMove 16 0xc8cc103916103001e4910801240007 0xc8cc103914103001cc8430401c0007 48 0xdecdbcdeabc9abc89a789656789456734562345612340123 (by decide +kernel)))) else (if k < 0x915738b7 then (if k < 0x8fccb9a5 then (if k < 0x8f5e2b0b then mkMove 16 0xc8cc103914103001e4850a01240007 0xc8cc103914103001e30484401c0007 59 0xecdab89789abcd6789abcde56456783456782345123456789abcd012345 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4191848040007 0xc8cc103914103001cc842381020007 15 0xdecbcd897896784 (by decide +kernel)) else (if k < 0x9115384f then mkMove 16 0xc8cc103914103001e4912488400007 0xc8cc103914103001d244c901080007 16 0xdecbcd8978967842 (by decide +kernel) else mkMove 16 0xc8cc103914103001e24a084c100007 0xc8cc103914103001e204c8401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel))) else (if k < 0x92bfe753 then (if k < 0x91c4b226 then mkMove 16 0xc8cc103914903001e3018844040007 0xc8cc103914903001e00588401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4190480c20007 0xc8cc103914103001cc8424401c0007 15 0xdecbcd897896784 (by decide +kernel)) else (if k < 0x955feb6a then mkMove 16 0xc8cc103914903001e4058840140007 0xc8cc103914903001e18580400c0007 37 0xedecdebcdeabcd9abcde89abcd54534562340 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3110446080007 0xc8cc103914103001cc8430401c0007 33 0xdecdbcdeabcd9abcde87856789abcd451 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_10 (k : Nat) : Move := (if k < 0x9d289c0e then (if k < 0x99c44d1d then (if k < 0x97a7f4b5 then (if k < 0x96f1116a then mkMove 16 0xc8cc103914103001e4111848140007 0xc8cc103914103001cc8424401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103914103001e2110446480007 0xc8cc103914103001e30488401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel)) else (if k < 0x981c7820 then mkMove 16 0xc8cc103914103001e30180441c0007 0xc8cc103914103001e30488401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4118488c00007 0xc8cc103914103001e30484401c0007 69 0xdecabcd8789abc67895456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel))) else (if k < 0x9b44f1ec then (if k < 0x9b08fdf1 then mkMove 16 0xc8cc103914903001e4810a01240007 0xc8cc103914103001e30484401c0007 47 0xdecdbcdeabc9abc89a78965678945673456234512340123 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c4821100003 0xc8cc10392893088c003d0820060003 34 0xedecdeabcde897678956789a4567345678 (by decide +kernel)) else (if k < 0x9cebd3ac then mkMove 16 0xc8cc103914103001e482248c100007 0xc8cc103914103001cc8424401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel) else mkMove 16 0xc8cc103914103001d044c901080007 0xc8cc103914103001cc0430401c0007 65 0xdecdbcdeabcd9abcde89abcd78967856789456789345678923456789123401234 (by decide +kernel)))) else (if k < 0x9ef94d07 then (if k < 0x9d64b1e3 then (if k < 0x9d41ae6e then mkMove 16 0xc8cc103914103001e3108444180007 0xc8cc103914103001cc842441180007 33 0xdecdbcdeabcd9abcde87856789abcd451 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30084441c0007 0xc8cc103914103001e304c0401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)) else (if k < 0x9dd91158 then mkMove 16 0xc8cc103914103001e4490280c20007 0xc8cc103914103001cc4430401c0007 15 0xdecbcd897896784 (by decide +kernel) else mkMove 16 0xc8cc103914903001e3018084420007 0xc8cc103914903001e08580401c0007 54 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc12 (by decide +kernel))) else (if k < 0xa21dd213 then (if k < 0xa1d31051 then mkMove 16 0xc8cc103914903001e4112488400007 0xc8cc103914103001cc4430401c0007 94 0xdecdbcdabcd9ab89abc789abcde67856789ab456789abcd3456789abc23456789ab123456789abcde0123456789abc (by decide +kernel) else mkMove 16 0xc8cc10392893088c003cc001900003 0xc8cc10392893088c003d0820060003 49 0xeabcde9ab89abcde789ab67856789abc456789ab3456789a1 (by decide +kernel)) else (if k < 0xa319f906 then mkMove 16 0xc8cc103914103001e186008c140007 0xc8cc103914103001d244c901080007 35 0xeca89789abcd6789abcde56456789abcd21 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e3084000003 0xc8cc10392893088c003c03c0010003 43 0xebc9ab89789abc6789abc56789abcde453456789abc (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_11 (k : Nat) : Move := (if k < 0xa85e4ad5 then (if k < 0xa75ca61e then (if k < 0xa44ab39f then (if k < 0xa3c66a04 then mkMove 16 0xc8cc103914103001e4910841240007 0xc8cc103914103001e30580401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel) else mkMove 16 0xc8cc103914903001e0918801240007 0xc8cc103914103001e24488401c0007 45 0xdecbcdabc9ab89a789656789456734562345612340123 (by decide +kernel)) else (if k < 0xa467b9f4 then mkMove 16 0xc8cc103914103001d304c0401c0007 0xc8cc103914103001e30484401c0007 82 0xea89789abcde6789abcde56456789abcde345678923456789abcde123456789abcd0123456789abcde (by decide +kernel) else mkMove 16 0xc8cc103914103001e0918a01240007 0xc8cc103914103001e204c8401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel))) else (if k < 0xa8250b54 then (if k < 0xa7efbc3b then mkMove 16 0xc8cc10392893088c003c8440c00003 0xc8cc10392893088c003d0820060003 41 0xedecdebcdeabc9abc89a786785678945678934567 (by decide +kernel) else mkMove 16 0xc8cc103914103001e40a1848140007 0xc8cc103914103001d244c841080007 68 0xedecbcd989786789abc453456789abc23456789abcde123456789ab0123456789abc (by decide +kernel)) else (if k < 0xa83e1db4 then mkMove 16 0xc8cc103914103001e3118444080007 0xc8cc103914103001cc842381020007 32 0xdecdbcdeabcd9abcde87856789abcd45 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30184440c0007 0xc8cc103914103001e204c8401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)))) else (if k < 0xa9b63154 then (if k < 0xa99cafd6 then (if k < 0xa955b87a then mkMove 16 0xc8cc103914103001e4822488500007 0xc8cc103914103001cc842441180007 68 0xdecdbcd989abc789ab678453456789abcde23456789ab123456789a0123456789abc (by decide +kernel) else mkMove 16 0xc8cc10392893088c003cc101800003 0xc8cc10392893088c003d0820060003 45 0xcabc9a89ab789abcde6756789ab456789ab3456789abc (by decide +kernel)) else (if k < 0xa9a07a3c then mkMove 16 0xc8cc10392893088c003d1022020003 0xc8cc10392893088c003d0820060003 35 0xdab8976789abcde56789abc43456789abcd (by decide +kernel) else mkMove 16 0xc8cc103914103001e186018c040007 0xc8cc103914103001d204c9010c0007 35 0xeca89789abcd6789abcde56456789abcd21 (by decide +kernel))) else (if k < 0xaa8e4955 then (if k < 0xaa075ef9 then mkMove 16 0xc8cc103914103001e2118444480007 0xc8cc103914103001d204c8410c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103916103001e4810a01240007 0xc8cc103914103001e30488401c0007 47 0xdecdbcdeabc9abc89a78965678945673456234512340123 (by decide +kernel)) else (if k < 0xaaaf49ff then mkMove 16 0xc8cc103914103001e30480401c0007 0xc8cc103914103001cc0430401c0007 75 0xdecdbcdabc9ab89a789656789a4567893456789abcde23456789abc1234560123456789abcd (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e4020180003 0xc8cc10392893088c003d0820060003 58 0xdecbcdeabcd9abcde89abcd789abcde6789abcd56745673456789abcde (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_12 (k : Nat) : Move := (if k < 0xb1afbfd6 then (if k < 0xaf627401 then (if k < 0xaedacaf5 then (if k < 0xae12b150 then mkMove 16 0xc8cc103914103001d844c901080007 0xc8cc103914103001d244c841080007 53 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3048444180007 0xc8cc103914103001d244c841080007 50 0xcbc989abcd789abcde6789a456345678923451234567801234 (by decide +kernel)) else (if k < 0xaf3c5ee3 then mkMove 16 0xc8cc10392893088c003c2640400003 0xc8cc10392893088c003c03c0010003 28 0xdecdbcde9789a678545678345678 (by decide +kernel) else mkMove 16 0xc8cc103916103001e4112488400007 0xc8cc103914103001cc8430401c0007 52 0xedecdebcdeabc9abc89a78678956789456734562345612340123 (by decide +kernel))) else (if k < 0xaffbdd2a then (if k < 0xafcabf67 then mkMove 16 0xc8cc103914903001e1018844240007 0xc8cc103914903001e18580400c0007 50 0xeabc989abc789abc456789abcd3456789a23456789abcde012 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e2420080003 0xc8cc10392893088c003c03c0010003 30 0xdcdebc9a89a789abcde6789a567345 (by decide +kernel)) else (if k < 0xb0896a5a then mkMove 16 0xc8cc10392893088c003e4088100003 0xc8cc10392893088c003d0820060003 41 0xec9789abcde6785678456789abcde3456789abcde (by decide +kernel) else mkMove 16 0xc8cc103914903001e186008c400007 0xc8cc103914903001e00588401c0007 42 0xedecbca9a89a789a6789a5423456789abcde123401 (by decide +kernel)))) else (if k < 0xb7c46f7f then (if k < 0xb4097be0 then (if k < 0xb1d4bbf3 then mkMove 16 0xc8cc103914103001d044c101980007 0xc8cc103914103001cc4430401c0007 35 0xdecdbcdeabcd9abcde87856789abcd45212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4911808240007 0xc8cc103914103001d244c841080007 75 0xedcdebcde989abcde789a6789abcde4563456789abc23456789a123456789abc0123456789a (by decide +kernel)) else (if k < 0xb551cf36 then mkMove 16 0xc8cc103916103001e0918801240007 0xc8cc103914103001e30488401c0007 45 0xdecbcdabc9ab89a789656789456734562345612340123 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0858a01240007 0xc8cc103914103001d204c8401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel))) else (if k < 0xb821208e then (if k < 0xb815a167 then mkMove 16 0xc8cc103916103001d20448401c0007 0xc8cc103914103001d204c8410c0007 104 0xedcdebcdeabcd9abcde89abcde786789abcde56789abcd456789abcde3456789abcde2345678123456789abcd0123456789abcde (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d0022060003 0xc8cc10392893088c003d0820060003 38 0xdcdebcdabcde9abc89789a6789456789abcd31 (by decide +kernel)) else (if k < 0xb8614149 then mkMove 16 0xc8cc103914103001e30480411c0007 0xc8cc103914103001d244c841080007 37 0xecabc989abc789abc6789abc56789456789a1 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0198480c20007 0xc8cc103914103001e24488401c0007 16 0xdecbcd8978967842 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_13 (k : Nat) : Move := (if k < 0xc1014f55 then (if k < 0xbd9ef2c5 then (if k < 0xbafe42e7 then (if k < 0xb921be5a then mkMove 16 0xc8cc103914103001e3058444080007 0xc8cc103914103001cc902381020007 32 0xdecdbcdeabcd9abcde87856789abcd45 (by decide +kernel) else mkMove 16 0xc8cc103914903001e3008444180007 0xc8cc103914103001d244c841080007 70 0xedecdebcdabcde9abc89a7678956789abcd45678345678923456789a12345012345678 (by decide +kernel)) else (if k < 0xbb2fbdfe then mkMove 16 0xc8cc103914103001e24a080c100007 0xc8cc103914103001cc8420401c0007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel) else mkMove 16 0xc8d2603893103001e4090280420007 0xc8cc103914903001e2098280420007 42 0xedcdbabc89abcde789abc6789abcde543423456780 (by decide +kernel))) else (if k < 0xc060dc40 then (if k < 0xbdfde1ff then mkMove 16 0xc8cc103914103001e3110444480007 0xc8cc103914103001e204c8401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel) else mkMove 16 0xc8cc103914903001e186008c100007 0xc8cc103914903001e0098280c20007 53 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc2 (by decide +kernel)) else (if k < 0xc081bd7d then mkMove 16 0xc8cc103914903001e0818a01240007 0xc8cc103914103001cc8424401c0007 44 0xdecbcdabc9ab89a78965678945673456234512340123 (by decide +kernel) else mkMove 16 0xc8cc103914903001e4110848140007 0xc8cc103914903001e1818801240007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel)))) else (if k < 0xc388a4a0 then (if k < 0xc1bd04fe then (if k < 0xc1a29f45 then mkMove 16 0xc8cc103914903001e4111808240007 0xc8cc103914103001e30484401c0007 94 0xdecbcdabcd9ab89abc789abcde67856789ab456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel) else mkMove 16 0xc8cc103914103001e4111a08240007 0xc8cc103914103001cc4430401c0007 35 0xdecabcd8789678545673456234512340123 (by decide +kernel)) else (if k < 0xc35b2049 then mkMove 16 0xc8cc103914903001e0058844140007 0xc8cc103914903001e1058844040007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914103001cc802381020007 0xc8cc103914103001cc8420401c0007 38 0xecabc989abc789abc6789abc56789456789a12 (by decide +kernel))) else (if k < 0xc41e2da0 then (if k < 0xc4014106 then mkMove 16 0xc8cc103914103001e0198088c20007 0xc8cc103914103001d204c8410c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103914103001e0498280c20007 0xc8cc103914103001e30484401c0007 16 0xdecbcd8978967842 (by decide +kernel)) else (if k < 0xc462bc4f then mkMove 16 0xc8cc103914903001e3018444080007 0xc8cc103914103001cc902381020007 58 0xecdabc9abcde89abcd789abc6789abc56789abcde4345623456789abc0 (by decide +kernel) else mkMove 16 0xc8cc103914103001e44a180c100007 0xc8cc103914103001cc4430401c0007 73 0xdecdabcde89789abc678956456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_14 (k : Nat) : Move := (if k < 0xca053fb5 then (if k < 0xc6ab3fd6 then (if k < 0xc5d9ff75 then (if k < 0xc5808a28 then mkMove 16 0xc8cc10392893088c003d00200e0003 0xc8cc10392893088c003d0820060003 38 0xdecbcda989abcde7896789abcd56789abcd341 (by decide +kernel) else mkMove 16 0xc8cc103914903001e186018c000007 0xc8cc103914903001e2098280420007 53 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc2 (by decide +kernel)) else (if k < 0xc65dae26 then mkMove 16 0xc8cc103914103001e2190444480007 0xc8cc103914103001e20588401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel) else mkMove 16 0xc8cc103914103001e20a184c100007 0xc8cc103914103001e30488401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel))) else (if k < 0xc8371dab then (if k < 0xc6ac9f41 then mkMove 16 0xc8cc103914103001e4118809240007 0xc8cc103914103001e30580401c0007 36 0xeca89789abcd6789abcde56456789abcd212 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e4808100003 0xc8cc10392893088c003d0820060003 43 0xecbc9abc8789abc6789ab56789abcd45673456789ab (by decide +kernel)) else (if k < 0xc9c70421 then mkMove 16 0xc8cc103914103001d244c801080007 0xc8cc103914103001cc0430401c0007 100 0xdecdbcdabcde9abc89abcde789abcde6756789abcd456789abcde3456789abcde2345678123456789abcd0123456789abcde (by decide +kernel) else mkMove 16 0xc8cc103914103001e0918841240007 0xc8cc103914103001e20588401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel)))) else (if k < 0xcb136a6a then (if k < 0xca4f8ee9 then (if k < 0xca0be8b9 then mkMove 16 0xc8cc10392893088c003e0024180003 0xc8cc10392893088c003d0820060003 40 0xcdebcdabcde9abcd8789ab678456789abcde3451 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d3002020003 0xc8cc10392893088c003d0820060003 43 0xecdebcabc9abc89ab789abc67895456789ab3456789 (by decide +kernel)) else (if k < 0xcadac151 then mkMove 16 0xc8cc103914103001e182048c100007 0xc8cc103914103001cc0430401c0007 74 0xdecdabcde89789abc6789567456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel) else mkMove 16 0xc8cc10392893088c003d8020060003 0xc8cc10392893088c003d0820060003 50 0xdecbcdeabc9abcde89abc789abcde6789abc5453456789abcd (by decide +kernel))) else (if k < 0xcca4906a then (if k < 0xcc51f23a then mkMove 16 0xc8cc103914103001e3110444180007 0xc8cc103914103001cc8424401c0007 33 0xdecdbcdeabcd9abcde87856789abcd451 (by decide +kernel) else mkMove 16 0xc8cc103916103001d204c8010c0007 0xc8cc103914103001d204c8410c0007 82 0xedcdebcdeabc9abc89a7678956789a4567893456789abcde23456789abcd12345670123456789abcde (by decide +kernel)) else (if k < 0xcd137f96 then mkMove 16 0xc8cc103914103001e2110444580007 0xc8cc103914103001e24488401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4910801240007 0xc8cc103914103001cc0430401c0007 48 0xdecdbcdeabc9abc89a789656789456734562345612340123 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_15 (k : Nat) : Move := (if k < 0xd4bd8d57 then (if k < 0xd1191411 then (if k < 0xcf51d2e0 then (if k < 0xce40f3db then mkMove 16 0xc8cc103916103001e244c801100007 0xc8cc103914103001d244c841080007 55 0xecdabc9abcde89abcd789abc56789abcd456789ab3456789a234560 (by decide +kernel) else mkMove 16 0xc8cc103916103001e186008c100007 0xc8cc103914103001cc8430401c0007 82 0xedcdebcdabc9ab89a7896789a56789abc456789abc3456789abc23456789ab1234567890123456789a (by decide +kernel)) else (if k < 0xd0a3ee1c then mkMove 16 0xc8cc10392893088c003e008c100003 0xc8cc10392893088c003d0820060003 38 0xecdb9789abcd656456789abcde3456789abcd1 (by decide +kernel) else mkMove 16 0xc8cc103916103001e0818a01240007 0xc8cc103914103001cc8430401c0007 44 0xdecbcdabc9ab89a78965678945673456234512340123 (by decide +kernel))) else (if k < 0xd1b44b2c then (if k < 0xd1446131 then mkMove 16 0xc8cc103916103001e2048841140007 0xc8cc103916103001d20448410c0007 3 0xec6 (by decide +kernel) else mkMove 16 0xc8cc103916103001e4111808240007 0xc8cc103914103001e304c0401c0007 36 0xdecabcd87896785456734562345612340123 (by decide +kernel)) else (if k < 0xd3eff81b then mkMove 16 0xc8cc10392893088c003c04201c0003 0xc8cc10392893088c003d0820060003 31 0xdcdebc9a89a789abcde6789a5673451 (by decide +kernel) else mkMove 16 0xc8cc103914903001cc0430401c0007 0xc8cc103914103001d244c841080007 100 0xedcdebcdeabcd9abcde89abcde786789abcde56789abc456789abcd3456789abcd234567123456789abcde0123456789abcd (by decide +kernel)))) else (if k < 0xdaec003d then (if k < 0xd78ec0f8 then (if k < 0xd4d69fb7 then mkMove 16 0xc8cc103914103001e21a084c100007 0xc8cc103914103001e20588401c0007 60 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e20a084c140007 0xc8cc103914103001d204c9010c0007 35 0xdecdbcdeabc9abc89a789656789a4567812 (by decide +kernel)) else (if k < 0xda990a72 then mkMove 16 0xc8cc103914103001e4112088420007 0xc8cc103914103001e20488401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel) else mkMove 16 0xc8cc103914103001e2198080c20007 0xc8cc103914103001e20588401c0007 16 0xdecbcd8978967842 (by decide +kernel))) else (if k < 0xdcb0ba72 then (if k < 0xdbafc1b5 then mkMove 16 0xc8cc103914103001e31180440c0007 0xc8cc103914103001d204c8410c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel) else mkMove 16 0xc8cc103914903001e20488401c0007 0xc8cc103914103001d204c9010c0007 101 0xedcdebcdeabcd9abcde89abcde786789abcde56789abcd456789abcde3456789abcde234567123456789abc0123456789abcd (by decide +kernel)) else (if k < 0xdd0000f3 then mkMove 16 0xc8cc10392893088c003d04200c0003 0xc8cc10392893088c003d0820060003 29 0xdecdbcdeabcde9abcde89abcde654 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e2004480003 0xc8cc10392893088c003d0820060003 35 0xedecabc9a8978956789abcde456789a3451 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_16 (k : Nat) : Move := (if k < 0xe47db1fe then (if k < 0xe06bb6fb then (if k < 0xdedce9b7 then (if k < 0xdde85199 then mkMove 16 0xc8cc10392893088c003e00201a0003 0xc8cc10392893088c003d0820060003 38 0xdecbc89abcde789a6789abc56789abcde34561 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003cc801100003 0xc8cc10392893088c003d0820060003 56 0xecdbcabc9abcde89abcde789abc6789abcd5678456789ab3456789ab (by decide +kernel)) else (if k < 0xe02316dc then mkMove 16 0xc8cc103914103001e486208c100007 0xc8cc103914103001e24488401c0007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel) else mkMove 16 0xc8cc103914103001e0098288c20007 0xc8cc103914103001d244c841080007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel))) else (if k < 0xe22ef215 then (if k < 0xe10d06eb then mkMove 16 0xc8cc103914903001e4190080c20007 0xc8cc103914103001cc8424401c0007 99 0xedcdebcdeabc9abcd89abc7896789abcde56789ab456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel) else mkMove 16 0xc8cc103914103001e4190280c20007 0xc8cc103914103001cc8430401c0007 15 0xdecbcd897896784 (by decide +kernel)) else (if k < 0xe43309f7 then mkMove 16 0xc8cc10392893088c003d8420040003 0xc8cc10392893088c003c03c0010003 37 0xdecbcda989abcde7896789abcd56789abcd34 (by decide +kernel) else mkMove 16 0xc8cc103916103001cc0430401c0007 0xc8cc103914103001d244c901080007 65 0xdecdbcde9897896789434567823456789abcd123456789abcde0123456789abcd (by decide +kernel)))) else (if k < 0xe6395672 then (if k < 0xe5302e39 then (if k < 0xe4af0c6a then mkMove 16 0xc8cc103914103001d244c101880007 0xc8cc103914103001d244c841080007 47 0xdcb89789abcd67456345678923456789a12345012345678 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c24004c0003 0xc8cc10392893088c003d0820060003 40 0xedebcdeabc989abcd6789abcde56789a45673451 (by decide +kernel)) else (if k < 0xe56af9c2 then mkMove 16 0xc8cc10392893088c003cc001840003 0xc8cc10392893088c003d0820060003 43 0xeabcde989abcd789a656789abc456789abc34567891 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003cc901000003 0xc8cc10392893088c003c03c0010003 42 0xcbcde9abcde89a789abc6789ab567894563456789a (by decide +kernel))) else (if k < 0xe98e87e0 then (if k < 0xe701e972 then mkMove 16 0xc8cc103914103001e4911848040007 0xc8cc103914103001cc902381020007 15 0xdecbcd897896784 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4111848240007 0xc8cc103914103001cc8430401c0007 35 0xeca89789abcd6789abcde56456789abcd12 (by decide +kernel)) else (if k < 0xe9adf1d2 then mkMove 16 0xc8cc103914903001e2048844140007 0xc8cc103914903001e10580440c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4810a01240007 0xc8cc103914103001cc0430401c0007 34 0xdecdbcdeabc9abc89a789656789a456782 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_17 (k : Nat) : Move := (if k < 0xef1c6636 then (if k < 0xebf2d391 then (if k < 0xebb91d58 then (if k < 0xeba2565d then mkMove 16 0xc8cc103914103001e41a1848040007 0xc8cc103914103001cc902381020007 34 0xeca89789abcd6789abcde56456789abcd2 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4922488400007 0xc8cc103914103001d244c841080007 59 0xedcdebcdeabcde9abcde89abcde7896789abcde56789abcd456789abcde (by decide +kernel)) else (if k < 0xebd6157f then mkMove 16 0xc8cc103914103001e3108384020007 0xc8cc103914103001d244c841080007 33 0xdecdbcdeabcd9abcde87856789abcd452 (by decide +kernel) else mkMove 16 0xc8cc103914103001e30580440c0007 0xc8cc103914103001d204c9010c0007 34 0xdecdbcdeabcd9abcde87856789abcd4521 (by decide +kernel))) else (if k < 0xee4fca46 then (if k < 0xedc5011e then mkMove 16 0xc8cc103916103001e20488401c0007 0xc8cc103914103001d204c8410c0007 101 0xedcdebcdeabcd9abcde89abcde786789abcde56789abcd456789abcde3456789abcde234567123456789abc0123456789abcd (by decide +kernel) else mkMove 16 0xc8cc103914103001d044c901180007 0xc8cc103914103001e30484401c0007 34 0xdecdbcdeabcd9abcde87856789abcd4512 (by decide +kernel)) else (if k < 0xeee2f1bc then mkMove 16 0xc8cc10392893088c003d2202400003 0xc8cc10392893088c003d0820060003 39 0xedcdeabc9abcde789abcde56789456789ab3456 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4112488400007 0xc8cc103914103001cc0430401c0007 94 0xdecdbcdabcd9ab89abc789abcde67856789ab456789abcd3456789abc23456789ab123456789abcde0123456789abc (by decide +kernel)))) else (if k < 0xf3b00eb9 then (if k < 0xf0b6afa3 then (if k < 0xf0aec8d7 then mkMove 16 0xc8cc103914903001cc8420401c0007 0xc8cc103914103001cc902381020007 18 0xa987653456789a2301 (by decide +kernel) else mkMove 16 0xc8cc103916103001e4190080c20007 0xc8cc103914103001cc8430401c0007 81 0xdecdbcdeabc9abc89a789a656789abc456789abc3456789abc23456789abc1234567890123456789a (by decide +kernel)) else (if k < 0xf2790758 then mkMove 16 0xc8cc103914903001e20a084c100007 0xc8cc103914903001e0198080c20007 52 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc (by decide +kernel) else mkMove 16 0xc8cc10392893088c003c2240410003 0xc8cc10392893088c003d0820060003 38 0xdcdbcdab9abc89789abc6789abcde456783456 (by decide +kernel))) else (if k < 0xf565e9d4 then (if k < 0xf5293942 then mkMove 16 0xc8cc103914103001e0918801240007 0xc8cc103914103001e20488401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel) else mkMove 16 0xc8cc10392893088c003e0420180003 0xc8cc10392893088c003d0820060003 8 0xeca85645 (by decide +kernel)) else (if k < 0xf6e52289 then mkMove 16 0xc8cc103914903001e4111848040007 0xc8cc103914103001cc8424401c0007 97 0xdecdbcdeabc9abcd89abc789abcde67856789ab456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel) else mkMove 16 0xc8cc103914903001e30180440c0007 0xc8cc103914103001d204c9010c0007 70 0xedecdebcdabcde9abc89abcd7867895678945673456723456789a12345678012345678 (by decide +kernel)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private def orbit16_18 (k : Nat) : Move := (if k < 0xfd001f35 then (if k < 0xfb0fda55 then (if k < 0xfafe4df2 then mkMove 16 0xc8cc103914103001e2098280c20007 0xc8cc103914103001e30580401c0007 16 0xdecbcd8978967842 (by decide +kernel) else mkMove 16 0xc8cc103914103001e4918801240007 0xc8cc103914103001e30488401c0007 33 0xdecdbcdeabc9abc89a789656789a45678 (by decide +kernel)) else (if k < 0xfca3329a then mkMove 16 0xc8cc103914103001e4118849040007 0xc8cc103914103001e20588401c0007 36 0xeca89789abcd6789abcde56456789abcd212 (by decide +kernel) else mkMove 16 0xc8cc103914103001e3048384020007 0xc8cc103914103001d244c901080007 36 0xecabc989abc789abc6789abc56789456789a (by decide +kernel))) else (if k < 0xfe62f8b4 then (if k < 0xfd062937 then mkMove 16 0xc8cc10392893088c003c1800320003 0xc8cc10392893088c003d0820060003 38 0xedecbcdeabc9a89abc6789abcd567894567831 (by decide +kernel) else mkMove 16 0xc8cc103914903001e4090280c20007 0xc8cc103914103001e30580401c0007 82 0xdeab89789abc6789abcde567456789abcd3456789abc23456789abc123456789abcde0123456789abc (by decide +kernel)) else (if k < 0xfeb104df then mkMove 16 0xc8cc103914103001e24a080c500007 0xc8cc103914103001cc842381020007 35 0xdecdbcdeabc9abc89a789656789a4567821 (by decide +kernel) else (if k < 0xff5f7812 then mkMove 16 0xc8cc103914103001e30088441c0007 0xc8cc103914103001e30580401c0007 55 0xecdbcabc9abcde89abcd789abc6789abc56789abcde456789abc212 (by decide +kernel) else mkMove 16 0xc8cc103916103001cc8420401c0007 0xc8cc103914103001cc842381020007 79 0xdecdbcdeabc9abc89a789656789a4567893456789abcd234567123456789abcde0123456789abcd (by decide +kernel)))))

private def orbit16 (k : Nat) : Move := (if k < 0x88466c33 then (if k < 0x4521602d then (if k < 0x1a00df06 then (if k < 0xd047d34 then orbit16_0 k else orbit16_1 k) else (if k < 0x33e5ca3b then orbit16_2 k else orbit16_3 k)) else (if k < 0x5e582c97 then (if k < 0x521e10c7 then orbit16_4 k else orbit16_5 k) else (if k < 0x6cf1728f then orbit16_6 k else (if k < 0x7a65ea34 then orbit16_7 k else orbit16_8 k)))) else (if k < 0xc55c89ae then (if k < 0xa32a74fe then (if k < 0x9628bc00 then orbit16_9 k else orbit16_10 k) else (if k < 0xab88521e then orbit16_11 k else (if k < 0xb90f2096 then orbit16_12 k else orbit16_13 k))) else (if k < 0xddd5087e then (if k < 0xce361e6f then orbit16_14 k else orbit16_15 k) else (if k < 0xeb33c7c3 then orbit16_16 k else (if k < 0xf7337cae then orbit16_17 k else orbit16_18 k)))))

private def pickMove (g : List Nat) := match g.length with
  | 4 => orbit4 (keyRows g)
  | 7 => orbit7 (keyRows g)
  | 8 => orbit8 (keyRows g)
  | 12 => orbit12 (keyRows g)
  | 13 => orbit13 (keyRows g)
  | 16 => orbit16 (keyRows g)
  | _ => trivialMove


private def norm2 (g : List Nat) := if 33<edges_ g then g else
  let move := pickMove g
  if g=move.source then move.target else g
private theorem norm2_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) :
    ∃ t, t.Perm l ∧ encode G t=norm2 (encode G l) := by
  unfold norm2
  split
  · exact ⟨l,List.Perm.refl _,rfl⟩
  dsimp only
  split
  next e =>
    let m := pickMove (encode G l)
    obtain ⟨t,perm,eq⟩ := relabel_real G m.swaps l
    refine ⟨t,perm,eq.trans ?_⟩
    change relabel m.swaps (encode G l) = m.target
    have root : encode G l = m.source := e
    exact (congrArg (relabel m.swaps) root).trans m.verify
  next => exact ⟨l,List.Perm.refl _,rfl⟩




private def atlas : List (List Nat) := [[3,2,30,15,560,388,274,146,3,2,6,3,2,2,1,0],
  [3,12,2113,15,560,388,274,146,3,2,6,3,2,2,1,0],
  [7,56,258,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,290,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,769,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,785,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1058,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2193,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1538,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1602,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,3138,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,516,284,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,516,284,804,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,528,1602,1169,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,528,1608,1169,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,536,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,536,1608,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,560,290,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,3074,2145,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,40,3138,2081,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2081,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3138,2049,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,132,3092,2178,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,388,3076,2054,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,388,3092,2050,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,584,3136,2144,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,2056,3138,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,2072,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,536,578,1153,7,24,194,145,3,2,6,3,2,2,1,0],
  [7,4228,2308,2308,7,24,194,145,3,2,6,3,2,2,1,0],
  [15,4144,3076,2194,1170,3,2,6,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1161,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1169,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2340,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,3108,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2082,1092,3,34,68,3,2,6,3,2,2,1,0],
  [15,2192,2084,2082,1094,3,34,68,3,2,6,3,2,2,1,0]]

structure TrioAtom where
  mask : Nat
  cost : Nat
  miss4 : Nat
  miss3 : Nat
  later : Nat
deriving Inhabited
structure TriFeature where
  subset : Nat
  blocked : Nat
deriving Inhabited

def tableBits {α : Type*} (xs : List α) (pred : α → Bool) := bits (xs.map pred)
def missWord (sets : List Nat) (x : Nat) := tableBits sets (fun s=>x &&& s == 0)
def allowedPair (a b : TrioAtom) := decide (a.mask≤b.mask) && (a.miss4 &&& b.miss4 == 0)
def fitMask (xs : List TrioAtom) (k : Nat) := tableBits xs (fun a=>decide (a.cost≤k))

def removeHits (fs : Array TriFeature) : Nat → Nat → Nat → Nat
  | 0,_,pool => pool
  | t+1,sel,pool => if sel=0 || pool=0 then pool else
    let i := sel.log2
    let bad := (fs[i]?.getD default).blocked
    removeHits fs t (sel % (2^i)) (pool ^^^ (pool &&& bad))

def eachBit (fn : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | s+1,pool => if pool=0 then true else
    let i := pool.log2
    fn i && eachBit fn s (pool % (2^i))

def trioTest (as_ : List TrioAtom) (fs : Array TriFeature) (costs : Array Nat) (budget : Nat)
    (done_ : Nat → Nat → Nat → Bool) :=
  as_.all fun x => as_.all fun y =>
    if allowedPair x y && (x.cost+y.cost≤budget) then
      let pool := x.later &&& y.later &&& costs[budget-x.cost-y.cost]?.getD 0
      let live := removeHits fs fs.size (x.miss3 &&& y.miss3) pool
      eachBit (fun k=> done_ x.mask y.mask (as_[k]?.getD default).mask) as_.length live
    else true

theorem testbit_of_get {α : Type*} (xs : List α) (fn : α→Bool) (i : Nat) {a : α}
    (h : xs[i]?=some a) : (tableBits xs fn).testBit i=fn a := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst a; cases e : fn x <;> simp [tableBits,bits,e,Nat.testBit]
    | succ i =>
      have he := ih i (by simpa using h)
      change (2*bits (xs.map fn)+(fn x).toNat).testBit (i+1)=fn a
      rw [Nat.testBit_add_one]
      cases hh : fn x <;> simpa [hh,half_step,tableBits] using he

theorem visit_hits (fn : Nat → Bool) (n pool i : Nat) (hi : pool.testBit i=true)
    (sz : pool<2^n) (h : eachBit fn n pool=true) : fn i=true := by
  induction n generalizing pool with
  | zero =>
    have e : pool=0 := by simpa using sz
    simp [e] at hi
  | succ n ih =>
    have nz : pool≠0 := by intro e; simp [e] at hi
    simp only [eachBit,nz,if_false,Bool.and_eq_true_iff] at h
    by_cases e : i=pool.log2
    · simpa [e] using h.1
    have upper : i≤pool.log2 := by
      by_contra! hn
      have lt : pool<2^i := (Nat.lt_log2_self (n:=pool)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit_lt_two_pow lt] at hi
    have logle : pool.log2≤n := by
      by_contra! hn
      have lp := Nat.log2_self_le nz
      have mono := Nat.pow_le_pow_right (n:=2) (by decide) (show n+1≤pool.log2 by omega)
      omega
    apply ih (pool % 2^pool.log2)
    · simp [Nat.testBit_mod_two_pow,show i<pool.log2 by omega,hi]
    · exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) logle)
    · exact h.2

theorem remove_keeps (fs : Array TriFeature) (fuel sel pool j : Nat)
    (bit : pool.testBit j=true)
    (safe : ∀ i,sel.testBit i=true → ((fs[i]?.getD default).blocked).testBit j=false) :
    (removeHits fs fuel sel pool).testBit j=true := by
  induction fuel generalizing sel pool with
  | zero => exact bit
  | succ fuel ih =>
    simp only [removeHits]
    split
    · exact bit
    next h =>
      have nz : sel≠0 := by intro e; simp [e] at h
      have v := safe sel.log2 (Nat.testBit_log2 nz)
      apply ih
      · simp [Nat.testBit_xor,Nat.testBit_and,bit,v]
      · intro i hi
        apply safe i
        simp only [Nat.testBit_mod_two_pow,Bool.and_eq_true_iff] at hi
        exact hi.2

def trioValidated (b : List Nat) (as_ : List TrioAtom) (quads : List Nat) (fs : Array TriFeature)
    (costs : Array Nat) (budget : Nat) :=
  (quads.all (fun s=>decide ((s,4)∈inds b))) &&
  (fs.toList.all (fun f=> decide ((f.subset,3)∈inds b) && (f.blocked == tableBits as_ (fun z=>z.mask &&& f.subset == 0)))) &&
  (as_.all (fun a=>a.cost == countBits b.length a.mask && a.miss4 == missWord quads a.mask &&
    a.miss3 == missWord (fs.toList.map TriFeature.subset) a.mask && a.later == tableBits as_ (allowedPair a))) &&
  ((List.range (budget+1)).all (fun k=>decide (costs[k]?=some (fitMask as_ k)))) &&
  ((usable 6 3 b).all (fun x=>decide (x∈as_.map TrioAtom.mask)))

theorem pair_lim (I : List (Nat × Nat)) (Q cs : List Nat)
    (qok : ∀ s∈Q,(s,4)∈I) (ok : okContacts 6 I cs=true) :
    cs.Pairwise (fun x y=>missWord Q x &&& missWord Q y = 0) := by
  rw [List.pairwise_iff_forall_sublist]
  intro x y sub
  apply (and_mask Q _ _).mpr
  intro m hm hx
  by_contra! hy
  have yhit : (y &&& m == 0)=true := by simpa using hy
  have a := of_decide_eq_true (List.all_eq_true.mp ok (m,4) (qok m hm))
  have b := (sub.filter (p:=fun z=> z &&& m == 0)).length_le
  simp [hx,yhit] at b
  change 4+(cs.filter (fun z=> z &&& m == 0)).length < 6 at a
  omega

theorem trioTest_sound (b : List Nat) (as_ : List TrioAtom) (Q : List Nat) (fs : Array TriFeature)
    (costs : Array Nat) (budget : Nat) (done_ : Nat→Nat→Nat→Bool)
    (verified : trioValidated b as_ Q fs costs budget=true)
    (passed : trioTest as_ fs costs budget done_=true)
    (x y z : Nat) (inc : ∀ t∈[x,y,z],t∈usable 6 3 b)
    (ord : [x,y,z].Pairwise (·≤·)) (ok : okContacts 6 (inds b) [x,y,z]=true)
    (small : countBits b.length x+countBits b.length y+countBits b.length z≤budget) : done_ x y z=true := by
  obtain ⟨vleft,cover⟩ := Bool.and_eq_true_iff.mp verified
  obtain ⟨vhead,costOK⟩ := Bool.and_eq_true_iff.mp vleft
  obtain ⟨vf,atomsOK⟩ := Bool.and_eq_true_iff.mp vhead
  obtain ⟨quadsOK,triOK⟩ := Bool.and_eq_true_iff.mp vf
  have get_ (t) (ht : t∈[x,y,z]) : ∃ a∈as_,a.mask=t := List.mem_map.mp (of_decide_eq_true (List.all_eq_true.mp cover t (inc t ht)))
  obtain ⟨a,ha,rfl⟩ := get_ x (by simp)
  obtain ⟨c,hc,rfl⟩ := get_ y (by simp)
  obtain ⟨e,he,rfl⟩ := get_ z (by simp)
  obtain ⟨j,hj⟩ : ∃ j,as_[j]?=some e := List.mem_iff_getElem?.mp he
  have rec_ (w) (hw : w∈as_) := List.all_eq_true.mp atomsOK w hw
  have A := rec_ a ha
  have C := rec_ c hc
  have E := rec_ e he
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at A C E
  have pairs := pair_lim (inds b) Q [a.mask,c.mask,e.mask] (fun s hs=>of_decide_eq_true (List.all_eq_true.mp quadsOK s hs)) ok
  simp [List.pairwise_cons] at pairs ord
  have ac : allowedPair a c=true := by simp [allowedPair,ord,pairs,A.1.1.2,C.1.1.2]
  have ae : allowedPair a e=true := by simp [allowedPair,ord,pairs,A.1.1.2,E.1.1.2]
  have ce : allowedPair c e=true := by simp [allowedPair,ord,pairs,C.1.1.2,E.1.1.2]
  have enough : a.cost+c.cost+e.cost≤budget := by simpa [A.1.1.1,C.1.1.1,E.1.1.1] using small
  have hk : budget-a.cost-c.cost ∈ List.range (budget+1) := List.mem_range.mpr (by omega)
  have costeq := of_decide_eq_true (List.all_eq_true.mp costOK _ hk)
  have inner := List.all_eq_true.mp (List.all_eq_true.mp passed a ha) c hc
  simp only [ac,Bool.true_and,show a.cost+c.cost≤budget by omega,decide_true,if_true,costeq,Option.getD_some] at inner
  have inpool : (a.later &&& c.later &&& fitMask as_ (budget-a.cost-c.cost)).testBit j=true := by
    rw [A.2,C.2]
    simp only [Nat.testBit_and,Bool.and_eq_true_iff]
    exact ⟨⟨(testbit_of_get _ _ _ hj).trans ae,(testbit_of_get _ _ _ hj).trans ce⟩,
      (testbit_of_get _ _ _ hj).trans (decide_eq_true (by omega))⟩
  have alive := remove_keeps fs fs.size (a.miss3 &&& c.miss3) _ j inpool (by
    intro i hi
    cases hh : fs[i]? with
    | none => change (0:Nat).testBit j=false; simp
    | some f =>
      have fl : fs.toList[i]?=some f := by simpa using hh
      have hmem : f∈fs.toList := List.mem_iff_getElem?.mpr ⟨i,fl⟩
      obtain ⟨fi,mask⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp triOK _ hmem)
      simp only [A.1.2,C.1.2,Nat.testBit_and,Bool.and_eq_true_iff] at hi
      have si : (fs.toList.map TriFeature.subset)[i]?=some f.subset := by simp [List.getElem?_map,fl]
      have ax := (testbit_of_get _ _ _ si).symm.trans hi.1
      have cx := (testbit_of_get _ _ _ si).symm.trans hi.2
      simp only [Option.getD_some,beq_iff_eq.mp mask,testbit_of_get _ _ _ hj]
      apply Bool.eq_false_iff.mpr
      intro ex
      have h := of_decide_eq_true (List.all_eq_true.mp ok (f.subset,3) (of_decide_eq_true fi))
      simp [show (a.mask &&& f.subset == 0)=true from ax,show (c.mask &&& f.subset == 0)=true from cx,ex] at h)
  have cnt : (removeHits fs fs.size (a.miss3 &&& c.miss3) (a.later &&& c.later &&& fitMask as_ (budget-a.cost-c.cost))) < 2^as_.length := by
    have bound (fs : Array TriFeature) (n s p : Nat) : removeHits fs n s p≤p := by
      induction n generalizing s p with
      | zero => rfl
      | succ n ih =>
        simp only [removeHits]
        split
        · rfl
        · apply le_trans (ih _ _)
          apply Nat.le_of_testBit
          intro i hi
          by_contra! hh
          simp [Nat.testBit_xor,Nat.testBit_and,hh] at hi
    apply (bound ..).trans_lt
    apply Nat.lt_of_le_of_lt Nat.and_le_right
    simpa [fitMask,tableBits] using bits_lt (as_.map fun o=>decide (o.cost≤budget-a.cost-c.cost))
  have answer := visit_hits _ _ _ _ alive cnt inner
  simpa [hj] using answer

theorem triExtension (norm : List Nat→List Nat) (atlas : List (List Nat))
    (b : List Nat) (as_ : List TrioAtom) (Q : List Nat) (fs : Array TriFeature)
    (costs : Array Nat) (budget : Nat) (known : List (List Nat))
    (bound : 33-edges_ b-3 = budget)
    (valid : trioValidated b as_ Q fs costs budget=true)
    (run : trioTest as_ fs costs budget (fun x y z=> decide ([x,y,z]∈known))=true)
    (close : known.all (fun cs=>decide (norm (attach cs b)∈atlas))=true)
    {cs : List Nat} (ex : Extension 6 3 b cs) (he : edges_ (attach cs b)≤33) :
    norm (attach cs b)∈atlas := by
  obtain ⟨x,y,z,rfl⟩ : ∃ x y z,cs=[x,y,z] :=
    ⟨_,_,_,List.eq_getElem_of_length_eq_three cs ex.1⟩
  have en := edges_attached [x,y,z] b
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at en
  have cost : countBits b.length x+countBits b.length y+countBits b.length z≤budget := by omega
  have k := trioTest_sound b as_ Q fs costs budget _ valid run x y z ex.2.1 ex.2.2.2.1 ex.2.2.1 cost
  exact of_decide_eq_true (List.all_eq_true.mp close [x,y,z] (of_decide_eq_true k))
private abbrev B2_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
private def B2_0opt : List (Nat × Nat) := [(4096,0x5bdb7b6dbdfabffedadbffeaaabfffffffffdbdb7b6dbd),(2048,0x3eb7d6dbebffffffffffffffffeababaaaaabeb7d6dbeb),(1024,0x767ecfff67ffeadbb7b7fffffff9e9e9e7f9f67ecfff67),(3072,0x3636c6db63ffeadbb7b7ffffffe8a8a8a2a8b636c6db63),(512,0x71fe3fff1fbe79ff8f8fdbf9fe7fe7e7fffff1fe3fff1f),(4608,0x51da3b6d1dba39fe8a8bdbe8aa3fe7e7ffffd1da3b6d1d),(1536,0x707e0fff07be68db8787dbf9fe79e1e1e7f9f07e0fff07),(256,0xffffe38ffe9ffb67e7ffebf99ffffff9e678ffffe38ff),(4352,0xbdb7a28bde8bfb65a5bfeaa88bfffff9e678bdb7a28bd),(2304,0xeb7d618ebe9ffb67e7ffebf99eababa8a228eb7d618eb),(128,0x7ff1fe07fffffffffffeb66787e79f9ffe1ffff1fe07ff),(4224,0x5bd17a05bdfabffedadab66282a79f9ffe1fdbd17a05bd),(2176,0x3eb1d603ebfffffffffeb66787e29a9aaa0abeb1d603eb),(384,0xff1fe00ffe9ffb67e7eb62781e79f9f9e078ff1fe00ff),(4480,0xbd17a00bde8bfb65a5ab62280a79f9f9e078bd17a00bd),(2432,0xeb1d600ebe9ffb67e7eb62781e29a9a8a028eb1d600eb),(64,0x7ff001ffffffffffffff8fe07fff807ffffffff001ffff),(4160,0x5bd0016dbdfabffedadb8fe02abf807fffffdbd0016dbd),(2112,0x3eb000dbebffffffffff8fe07fea803aaaaabeb000dbeb),(1088,0x767001ff67ffeadbb7b78fe07ff98069e7f9f67001ff67),(3136,0x363000db63ffeadbb7b78fe07fe88028a2a8b63000db63),(576,0x71f001ff1fbe79ff8f8f8be07e7f8067fffff1f001ff1f),(4672,0x51d0016d1dba39fe8a8b8be02a3f8067ffffd1d0016d1d),(1600,0x707001ff07be68db87878be07e798061e7f9f07001ff07),(192,0x7ff00007fffffffffffe866007e7801ffe1ffff00007ff),(4288,0x5bd00005bdfabffedada866002a7801ffe1fdbd00005bd),(2240,0x3eb00003ebfffffffffe866007e2801aaa0abeb00003eb),(32,0xfffffffffff8e01ffffffffffffff81ff800fffffff),(4128,0xb7b6dbdfabf8e00dbffeaaabfffff81ff800b7b6dbd),(2080,0x7d6dbebffff8e01ffffffffeababa80aa8007d6dbeb),(1056,0xecfff67ffea8a01b7fffffff9e9e981f9800ecfff67),(3104,0x6c6db63ffea8a01b7ffffffe8a8a880a88006c6db63),(544,0xe3fff1fbe798e018fdbf9fe7fe7e781ff800e3fff1f),(4640,0xa3b6d1dba398e008bdbe8aa3fe7e781ff800a3b6d1d),(1568,0xe0fff07be688a0187dbf9fe79e1e181f9800e0fff07),(288,0xffe38ffe9ff86007ffebf99ffffff8067800ffe38ff),(4384,0xb7a28bde8bf86005bfeaa88bfffff8067800b7a28bd),(2336,0x7d618ebe9ff86007ffebf99eababa80228007d618eb),(16,0x7fffffffff67e781fffe7e1fffe07fff80007fffffffff),(2064,0x3eb7d6dbeb67e781fffe7e1fffe03aba80003eb7d6dbeb),(1040,0x767ecfff6767e281b7b67e1fffe069e98000767ecfff67),(3088,0x3636c6db6367e281b7b67e1fffe028a880003636c6db63),(272,0xffffe38ff61e7807e7e7e1f99e07fff80000ffffe38ff),(2320,0xeb7d618eb61e7807e7e7e1f99e03aba80000eb7d618eb),(144,0x7ff1fe07ff67e781fffe360787e01f9f80007ff1fe07ff),(2192,0x3eb1d603eb67e781fffe360787e01a9a80003eb1d603eb),(400,0xff1fe00ff61e7807e7e360781e01f9f80000ff1fe00ff),(2448,0xeb1d600eb61e7807e7e360781e01a9a80000eb1d600eb),(48,0xfffffff67e78001fe7e1fffe07fff8000000fffffff),(2096,0x7d6dbeb67e78001fe7e1fffe03aba80000007d6dbeb),(1072,0xecfff6767e28001b67e1fffe069e98000000ecfff67),(3120,0x6c6db6367e28001b67e1fffe028a880000006c6db63),(304,0xffe38ff61e780007e7e1f99e07fff8000000ffe38ff),(2352,0x7d618eb61e780007e7e1f99e03aba80000007d618eb),(8,0x7fffffffff1fe07ffffe01ffffe000007fffffffffffff),(2056,0x3eb7d6dbeb1fe07ffffe01ffffe000002aaabeb7d6dbeb),(1032,0x767ecfff671fe05bb7b601ffffe0000067f9f67ecfff67),(3080,0x3636c6db631fe05bb7b601ffffe0000022a8b636c6db63),(520,0x71fe3fff1f1e607f8f8e01f9fe6000007ffff1fe3fff1f),(1544,0x707e0fff071e605b878601f9fe60000067f9f07e0fff07),(136,0x7ff1fe07ff1fe07ffffe006787e000007e1ffff1fe07ff),(2184,0x3eb1d603eb1fe07ffffe006787e000002a0abeb1d603eb),(72,0x7ff001ffff1fe07ffffe01e07fe000007ffffff001ffff),(2120,0x3eb000dbeb1fe07ffffe01e07fe000002aaabeb000dbeb),(1096,0x767001ff671fe05bb7b601e07fe0000067f9f67001ff67),(3144,0x363000db631fe05bb7b601e07fe0000022a8b63000db63),(584,0x71f001ff1f1e607f8f8e01e07e6000007ffff1f001ff1f),(1608,0x707001ff071e605b878601e07e60000067f9f07001ff07),(200,0x7ff00007ff1fe07ffffe006007e000007e1ffff00007ff),(2248,0x3eb00003eb1fe07ffffe006007e000002a0abeb00003eb),(24,0x7fffffffff07e001fffe001fffe0000000007fffffffff),(2072,0x3eb7d6dbeb07e001fffe001fffe0000000003eb7d6dbeb),(1048,0x767ecfff6707e001b7b6001fffe000000000767ecfff67),(3096,0x3636c6db6307e001b7b6001fffe0000000003636c6db63),(152,0x7ff1fe07ff07e001fffe000787e0000000007ff1fe07ff),(2200,0x3eb1d603eb07e001fffe000787e0000000003eb1d603eb),(4,0x7fffffffff001ffffffe0000001fffffffffffffffffff),(4100,0x5bdb7b6dbd001ffedada0000001fffffffffdbdb7b6dbd),(516,0x71fe3fff1f0019ff8f8e0000001fe7e7fffff1fe3fff1f),(4612,0x51da3b6d1d0019fe8a8a0000001fe7e7ffffd1da3b6d1d),(260,0xffffe38ff001fb67e7e0000001fffff9e678ffffe38ff),(4356,0xbdb7a28bd001fb65a5a0000001fffff9e678bdb7a28bd),(132,0x7ff1fe07ff001ffffffe000000079f9ffe1ffff1fe07ff),(4228,0x5bd17a05bd001ffedada000000079f9ffe1fdbd17a05bd),(388,0xff1fe00ff001fb67e7e000000079f9f9e078ff1fe00ff),(4484,0xbd17a00bd001fb65a5a000000079f9f9e078bd17a00bd),(68,0x7ff001ffff001ffffffe0000001f807ffffffff001ffff),(4164,0x5bd0016dbd001ffedada0000001f807fffffdbd0016dbd),(580,0x71f001ff1f0019ff8f8e0000001f8067fffff1f001ff1f),(4676,0x51d0016d1d0019fe8a8a0000001f8067ffffd1d0016d1d),(196,0x7ff00007ff001ffffffe00000007801ffe1ffff00007ff),(4292,0x5bd00005bd001ffedada00000007801ffe1fdbd00005bd),(20,0x7fffffffff000781fffe000000007fff80007fffffffff),(276,0xffffe38ff0007807e7e000000007fff80000ffffe38ff),(148,0x7ff1fe07ff000781fffe000000001f9f80007ff1fe07ff),(404,0xff1fe00ff0007807e7e000000001f9f80000ff1fe00ff),(12,0x7fffffffff00007ffffe0000000000007fffffffffffff),(524,0x71fe3fff1f00007f8f8e0000000000007ffff1fe3fff1f),(140,0x7ff1fe07ff00007ffffe0000000000007e1ffff1fe07ff),(76,0x7ff001ffff00007ffffe0000000000007ffffff001ffff),(588,0x71f001ff1f00007f8f8e0000000000007ffff1f001ff1f),(204,0x7ff00007ff00007ffffe0000000000007e1ffff00007ff),(28,0x7fffffffff000001fffe00000000000000007fffffffff),(156,0x7ff1fe07ff000001fffe00000000000000007ff1fe07ff),(2,0x7fffffffff0000000001ffffffffffffffffffffffffff),(4098,0x5bdb7b6dbd0000000001ffeaaabfffffffffdbdb7b6dbd),(1026,0x767ecfff670000000001fffffff9e9e9e7f9f67ecfff67),(514,0x71fe3fff1f0000000001dbf9fe7fe7e7fffff1fe3fff1f),(4610,0x51da3b6d1d0000000001dbe8aa3fe7e7ffffd1da3b6d1d),(1538,0x707e0fff070000000001dbf9fe79e1e1e7f9f07e0fff07),(258,0xffffe38ff0000000001febf99ffffff9e678ffffe38ff),(4354,0xbdb7a28bd0000000001feaa88bfffff9e678bdb7a28bd),(34,0xfffffff0000000001ffffffffffff81ff800fffffff),(4130,0xb7b6dbd0000000001ffeaaabfffff81ff800b7b6dbd),(1058,0xecfff670000000001fffffff9e9e981f9800ecfff67),(546,0xe3fff1f0000000001dbf9fe7fe7e781ff800e3fff1f),(4642,0xa3b6d1d0000000001dbe8aa3fe7e781ff800a3b6d1d),(1570,0xe0fff070000000001dbf9fe79e1e181f9800e0fff07),(290,0xffe38ff0000000001febf99ffffff8067800ffe38ff),(4386,0xb7a28bd0000000001feaa88bfffff8067800b7a28bd),(18,0x7fffffffff00000000007e1fffe07fff80007fffffffff),(1042,0x767ecfff6700000000007e1fffe069e98000767ecfff67),(274,0xffffe38ff00000000007e1f99e07fff80000ffffe38ff),(50,0xfffffff00000000007e1fffe07fff8000000fffffff),(1074,0xecfff6700000000007e1fffe069e98000000ecfff67),(306,0xffe38ff00000000007e1f99e07fff8000000ffe38ff),(10,0x7fffffffff000000000001ffffe000007fffffffffffff),(1034,0x767ecfff67000000000001ffffe0000067f9f67ecfff67),(522,0x71fe3fff1f000000000001f9fe6000007ffff1fe3fff1f),(1546,0x707e0fff07000000000001f9fe60000067f9f07e0fff07),(26,0x7fffffffff0000000000001fffe0000000007fffffffff),(1050,0x767ecfff670000000000001fffe000000000767ecfff67),(6,0x7fffffffff00000000000000001fffffffffffffffffff),(4102,0x5bdb7b6dbd00000000000000001fffffffffdbdb7b6dbd),(518,0x71fe3fff1f00000000000000001fe7e7fffff1fe3fff1f),(4614,0x51da3b6d1d00000000000000001fe7e7ffffd1da3b6d1d),(262,0xffffe38ff00000000000000001fffff9e678ffffe38ff),(4358,0xbdb7a28bd00000000000000001fffff9e678bdb7a28bd),(22,0x7fffffffff0000000000000000007fff80007fffffffff),(278,0xffffe38ff0000000000000000007fff80000ffffe38ff),(14,0x7fffffffff00000000000000000000007fffffffffffff),(526,0x71fe3fff1f00000000000000000000007ffff1fe3fff1f),(30,0x7fffffffff000000000000000000000000007fffffffff),(1,0xffffffffffffffffffffffffffffffffffff),(4097,0xfabffedadbffeaaabfffffffffdbdb7b6dbd),(2049,0xffffffffffffffffeababaaaaabeb7d6dbeb),(1025,0xffeadbb7b7fffffff9e9e9e7f9f67ecfff67),(3073,0xffeadbb7b7ffffffe8a8a8a2a8b636c6db63),(513,0xbe79ff8f8fdbf9fe7fe7e7fffff1fe3fff1f),(4609,0xba39fe8a8bdbe8aa3fe7e7ffffd1da3b6d1d),(1537,0xbe68db8787dbf9fe79e1e1e7f9f07e0fff07),(257,0xe9ffb67e7ffebf99ffffff9e678ffffe38ff),(4353,0xe8bfb65a5bfeaa88bfffff9e678bdb7a28bd),(2305,0xe9ffb67e7ffebf99eababa8a228eb7d618eb),(129,0xfffffffffeb66787e79f9ffe1ffff1fe07ff),(4225,0xfabffedadab66282a79f9ffe1fdbd17a05bd),(2177,0xfffffffffeb66787e29a9aaa0abeb1d603eb),(385,0xe9ffb67e7eb62781e79f9f9e078ff1fe00ff),(4481,0xe8bfb65a5ab62280a79f9f9e078bd17a00bd),(2433,0xe9ffb67e7eb62781e29a9a8a028eb1d600eb),(65,0xffffffffff8fe07fff807ffffffff001ffff),(4161,0xfabffedadb8fe02abf807fffffdbd0016dbd),(2113,0xffffffffff8fe07fea803aaaaabeb000dbeb),(1089,0xffeadbb7b78fe07ff98069e7f9f67001ff67),(3137,0xffeadbb7b78fe07fe88028a2a8b63000db63),(577,0xbe79ff8f8f8be07e7f8067fffff1f001ff1f),(4673,0xba39fe8a8b8be02a3f8067ffffd1d0016d1d),(1601,0xbe68db87878be07e798061e7f9f07001ff07),(193,0xfffffffffe866007e7801ffe1ffff00007ff),(4289,0xfabffedada866002a7801ffe1fdbd00005bd),(2241,0xfffffffffe866007e2801aaa0abeb00003eb),(33,0xffff8e01ffffffffffffff81ff800fffffff),(4129,0xfabf8e00dbffeaaabfffff81ff800b7b6dbd),(2081,0xffff8e01ffffffffeababa80aa8007d6dbeb),(1057,0xffea8a01b7fffffff9e9e981f9800ecfff67),(3105,0xffea8a01b7ffffffe8a8a880a88006c6db63),(545,0xbe798e018fdbf9fe7fe7e781ff800e3fff1f),(4641,0xba398e008bdbe8aa3fe7e781ff800a3b6d1d),(1569,0xbe688a0187dbf9fe79e1e181f9800e0fff07),(289,0xe9ff86007ffebf99ffffff8067800ffe38ff),(4385,0xe8bf86005bfeaa88bfffff8067800b7a28bd),(2337,0xe9ff86007ffebf99eababa80228007d618eb)]
private def B2_0lim : List Nat := [0x0,0x6d0da18000d51461600161144014540051000000000000,0x7feffdf6d0ffdf7dfd61fddf751f7f547dd46d0da18000,0x7ffffffffefffffffffdffffffdfffff7fff7feffdf6d0,0x7ffffffffffffffffffffffffffffffffffffffffffffe,0x7fffffffffffffffffffffffffffffffffffffffffffff]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem B2_0ok {g : List Nat} (hg : g∈grow 6 2 B2_0) (he : edges_ g≤33) : norm2 g∈atlas := by
  have opt : tagged 6 2 B2_0=B2_0opt := by decide +kernel
  have uni : universal (inds B2_0)=0x7fffffffffffffffffffffffffffffffffffffffffffff := by decide +kernel
  have lim : cells 6 (inds B2_0) [] 6 1=B2_0lim := by decide +kernel
  have hx := cut_contains (tag_floor 6 2 B2_0) hg he
  rw [opt,uni,lim] at hx
  have chk : (cutGrow 2 33 B2_0 B2_0opt 0x7fffffffffffffffffffffffffffffffffffffffffffff B2_0lim).all (fun x=>decide (norm2 x∈atlas))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp chk _ hx)

private def T0a : List TrioAtom := [⟨6,2,0x3ffc00007,0xffffc00000007ffff,0x10001212424921000000000000008000⟩,
⟨10,2,0x3ffc00078,0xffffc00000ff80fff,0x4840010400000004000000000000000008000⟩,
⟨12,2,0x3ffc07c00,0xffffc03ff00000fff,0x801000080200400020080040010010000010⟩,
⟨14,3,0x3ffc00000,0xffffc000000000fff,0x4849092485212424921484240290890088450⟩,
⟨17,2,0x3f83ff,0x3fc1ffffff07f,0x1018000406042200⟩,
⟨18,2,0x1fc003ff,0x7ffc0000fffff07f,0x3800000000e00000000000000007c000⟩,
⟨33,2,0x3ffc89,0x3ffff70f8ff83,0x2500000000940000000010000025500000⟩,
⟨36,2,0x3e0c1fc01,0xf83fc1fff0000ff83,0x2000000200e00020000000000020000000⟩,
⟨40,2,0x3e0ce7c08,0xf83fde3ff00f80f83,0x802000000000800000000000000020000000⟩,
⟨44,3,0x3e0c07c00,0xf83fc03ff00000f83,0x803800080200e00020080040010038000000⟩,
⟨65,2,0x3ffd32,0x3ffffb73b3f9c,0x128011000004000000⟩,
⟨68,2,0x3e701fc02,0xfbc7c1fff00033f9c,0x200400020100000000000000000⟩,
⟨72,2,0x3e70e7c30,0xfbc7de3ff07380f9c,0x800000000000000000100000000000000000⟩,
⟨76,3,0x3e7007c00,0xfbc7c03ff00000f9c,0x8010000802004000201c0040010010000000⟩,
⟨96,2,0x3e03ffc00,0xf807fffff30383f80,0x1002000100400800040100080020020000000⟩,
⟨97,3,0x3ffc00,0x3ffff30383f80,0x12825001284a094004a128095425025500000⟩,
⟨100,3,0x3e001fc00,0xf807c1fff00003f80,0x1002000100700e00070100080020020000000⟩,
⟨104,3,0x3e00e7c00,0xf807de3ff00380f80,0x1c02000100400800040100080020020000000⟩,
⟨108,4,0x3e0007c00,0xf807c03ff00000f80,0x1c038001c0700e000701c00e0038038000000⟩,
⟨129,2,0x169f76,0x2ede7df5f53fc,0xe00010000004000000⟩,
⟨130,2,0xff000376,0x7fd9c0000df5f53fc,0x4000010401000004100e00200080000000000⟩,
⟨132,2,0xff009c06,0x7fd9c0de7000753fc,0x200400020e00000000000000000⟩,
⟨134,3,0xff000006,0x7fd9c0000000753fc,0x4000010401212424921e00200080000000000⟩,
⟨136,2,0xff061c70,0x7fd9ce1e70f5803fc,0x800000000000000000e00000000000000000⟩,
⟨138,3,0xff000070,0x7fd9c00000f5803fc,0x4840010401000004100e00200080000000000⟩,
⟨140,3,0xff001c00,0x7fd9c01e7000003fc,0x801000080200400020e84040010010000000⟩,
⟨142,4,0xff000000,0x7fd9c0000000003fc,0x4849092485212424921e84240290890000000⟩,
⟨144,2,0x1f168376,0x7d9eec07df5f507c,0xe01400000000000000⟩,
⟨145,3,0x168376,0x2ec07df5f507c,0xe01418000400000000⟩,
⟨146,3,0x1f000376,0x7d9c0000df5f507c,0xe000038e0380000e380e01f001c0000000000⟩,
⟨192,2,0xe7169d32,0x7bc1eede7971b139c,0xffe000000000000000⟩,
⟨193,3,0x169d32,0x2ede7971b139c,0xffe011000000000000⟩,
⟨196,3,0xe7009c02,0x7bc1c0de70003139c,0x200400020ffe040000000000000⟩,
⟨200,3,0xe7061c30,0x7bc1ce1e70718039c,0x800000000000000000ffe000010000000000⟩,
⟨204,4,0xe7001c00,0x7bc1c01e70000039c,0x801000080200400020ffe040010000000000⟩,
⟨257,2,0x39e7cf,0x37ef9fbe7fce7,0x4000000000010000000000000⟩,
⟨258,2,0x339c003cf,0xbdfe40000fbe7fce7,0x10000004004000000000000000000000⟩,
⟨260,2,0x339c1e407,0xbdfe41ef90007fce7,0x207420020000000000000000000⟩,
⟨262,3,0x339c00007,0xbdfe400000007fce7,0x10001217424921000000000000000000⟩,
⟨272,2,0x19f983cf,0x5fe77c19fbe7f067,0x4000000000000000000000000⟩,
⟨273,3,0x3983cf,0x37c19fbe7f067,0x4000000001018000000000000⟩,
⟨274,3,0x19c003cf,0x5fe40000fbe7f067,0x3800000400f000000000000000000000⟩,
⟨288,2,0x320f9e489,0xb83e77ef970e0fc83,0x20000000049c0000000000000000000000⟩,
⟨289,3,0x39e489,0x37ef970e0fc83,0x25000000049c0000000010000000000000⟩,
⟨292,3,0x320c1e401,0xb83e41ef90000fc83,0x2000000207ff0020000000000000000000⟩,
⟨513,2,0x2b6add,0x3b77aededed6b,0x1c000000000000000000010000000000000⟩,
⟨514,2,0x35ac002dd,0xdefe80000ededed6b,0x1c012000000004000000000000000000000⟩,
⟨516,2,0x35ac16805,0xdefe8177a0005ed6b,0x1c000000200400020000000000000000000⟩,
⟨518,3,0x35ac00005,0xdefe800000005ed6b,0x1c012001212424921000000000000000000⟩,
⟨520,2,0x35aca6858,0xdefe9a37a0de80d6b,0x81d080080000000000000000000000000000⟩,
⟨522,3,0x35ac00058,0xdefe800000de80d6b,0x485d092484000004000000000000000000000⟩,
⟨524,3,0x35ac06800,0xdefe8037a00000d6b,0x81d080080200400020080040000000000000⟩,
⟨526,4,0x35ac00000,0xdefe8000000000d6b,0x485d092485212424921484240000000000000⟩,
⟨528,2,0x1aeb02dd,0x6febb41aedede06b,0x1c000000000000000000000000000000000⟩,
⟨529,3,0x2b02dd,0x3b41aedede06b,0x1c000000000000000001000000000000000⟩,
⟨530,3,0x1ac002dd,0x6fe80000edede06b,0x1c03f00000000e000000000000000000000⟩,
⟨544,2,0x340eb6889,0xd83ebb77a60e8ed03,0x1ffc0000000800000000000000000000000⟩,
⟨545,3,0x2b6889,0x3b77a60e8ed03,0x1ffc0000000940000000000000000000000⟩,
⟨548,3,0x340c16801,0xd83e8177a0000ed03,0x1ffc0000200e00020000000000000000000⟩,
⟨552,3,0x340ca6808,0xd83e9a37a00e80d03,0x81ffc0080000800000000000000000000000⟩,
⟨556,4,0x340c06800,0xd83e8037a00000d03,0x81ffc0080200e00020080000000000000000⟩,
⟨768,2,0x318e962cd,0x9cfe33678e9e5ec63,0x1c000000007000000000000000000000000⟩,
⟨769,3,0x2962cd,0x33678e9e5ec63,0x1c000000007000000000000000000000000⟩,
⟨770,3,0x318c002cd,0x9cfe00000e9e5ec63,0x1c012000007004800000000000000000000⟩,
⟨772,3,0x318c16005,0x9cfe016780005ec63,0x1c000000207420020000000000000000000⟩,
⟨774,4,0x318c00005,0x9cfe000000005ec63,0x1c012001217424921000000000000000000⟩,
⟨784,3,0x18e902cd,0x4fe33418e9e5e063,0x1c000000007000000000000000000000000⟩,
⟨785,4,0x2902cd,0x33418e9e5e063,0x1c000000007000000000000000000000000⟩,
⟨786,4,0x18c002cd,0x4fe00000e9e5e063,0x1c03f00000700fc00000000000000000000⟩,
⟨800,3,0x300e96089,0x983e3367860e0ec03,0x1ffc0000007ff0000000000000000000000⟩,
⟨801,4,0x296089,0x3367860e0ec03,0x1ffc0000007ff0000000000000000000000⟩,
⟨804,4,0x300c16001,0x983e016780000ec03,0x1ffc0000207ff0020000000000000000000⟩,
⟨1025,2,0x3e3bf8,0x3fbaefffe8739,0x8300400020000000000000000000000000000⟩,
⟨1026,2,0x1ce4003f8,0xef6b80000fffe8739,0x8300010000000004000000000000000000000⟩,
⟨1032,2,0x1ce4e3878,0xef6b9e3ae0ff80739,0xffe0000000000000000000000000000000000⟩,
⟨1034,3,0x1ce400078,0xef6b800000ff80739,0xffe0010400000004000000000000000000000⟩,
⟨1040,2,0xe7e03f8,0x76bbf80efffe8039,0x8300020800000000000000000000000000000⟩,
⟨1041,3,0x3e03f8,0x3f80efffe8039,0x8310624830000000000000000000000000000⟩,
⟨1042,3,0xe4003f8,0x76b80000fffe8039,0x830003880000000e000000000000000000000⟩,
⟨1056,2,0x1c07e3888,0xe82bbfbae70f88701,0x8302000000000800000000000000000000000⟩,
⟨1057,3,0x3e3888,0x3fbae70f88701,0x8302500020000940000000000000000000000⟩,
⟨1064,3,0x1c04e3808,0xe82b9e3ae00f80701,0xffe2000100000800000000000000000000000⟩,
⟨1088,2,0x1c63e3930,0xeb43bfbaeb73a0718,0x8300000000000000000000000000000000000⟩,
⟨1089,3,0x3e3930,0x3fbaeb73a0718,0x8300400020000000000000000000000000000⟩,
⟨1096,3,0x1c60e3830,0xeb439e3ae07380718,0xffe0000000000000000000000000000000000⟩,
⟨1120,3,0x1c03e3800,0xe803bfbae30380700,0x9382000100400800000000000000000000000⟩,
⟨1121,4,0x3e3800,0x3fbae30380700,0x93825001284a0940000000000000000000000⟩,
⟨1128,4,0x1c00e3800,0xe8039e3ae00380700,0xffe2000100400800000000000000000000000⟩,
⟨1152,2,0xce161b70,0x6f49ae9a6df5e0338,0x8300000000000000000000000000000000000⟩,
⟨1153,3,0x161b70,0x2e9a6df5e0338,0x8300400020000000000000000000000000000⟩,
⟨1154,3,0xce000370,0x6f4980000df5e0338,0xe300010401000000000000000000000000000⟩,
⟨1160,3,0xce061870,0x6f498e1a60f580338,0xffe0000000000000000000000000000000000⟩,
⟨1162,4,0xce000070,0x6f49800000f580338,0xffe0010401000000000000000000000000000⟩,
⟨1168,3,0xe160370,0x749ae806df5e0038,0x8300020800000000000000000000000000000⟩,
⟨1169,4,0x160370,0x2e806df5e0038,0x8310624830000000000000000000000000000⟩,
⟨1170,4,0xe000370,0x74980000df5e0038,0xe300038e03800000000000000000000000000⟩,
⟨1216,3,0xc6161930,0x6b41ae9a6971a0318,0x8300000000000000000000000000000000000⟩,
⟨1217,4,0x161930,0x2e9a6971a0318,0x8300400020000000000000000000000000000⟩,
⟨1224,4,0xc6061830,0x6b418e1a607180318,0xffe0000000000000000000000000000000000⟩,
⟨1536,2,0x14a6a2ad8,0xce6abb32aedec8529,0x831c624830000000000000000000000000000⟩,
⟨1537,3,0x2a2ad8,0x3b32aedec8529,0x831c624830000000000000000000000000000⟩,
⟨1538,3,0x14a4002d8,0xce6a80000edec8529,0x831c63f830000000000000000000000000000⟩,
⟨1544,3,0x14a4a2858,0xce6a9a32a0de80529,0xfffffffffc000000000000000000000000000⟩,
⟨1546,4,0x14a400058,0xce6a800000de80529,0xfffffffffc000000000000000000000000000⟩,
⟨1552,3,0xa6a02d8,0x66abb00aedec8029,0x831c624830000000000000000000000000000⟩,
⟨1553,4,0x2a02d8,0x3b00aedec8029,0x831c624830000000000000000000000000000⟩,
⟨1554,4,0xa4002d8,0x66a80000edec8029,0x831c63f830000000000000000000000000000⟩,
⟨1568,3,0x1406a2888,0xc82abb32a60e88501,0x831ffe4830000000000000000000000000000⟩,
⟨1569,4,0x2a2888,0x3b32a60e88501,0x831ffe4830000000000000000000000000000⟩,
⟨1576,4,0x1404a2808,0xc82a9a32a00e80501,0xfffffffffc000000000000000000000000000⟩,
⟨2049,2,0x35d7a7,0x3dfd5fe97fad6,0x0⟩,
⟨2050,2,0x2b58003a7,0xf7b540000fe97fad6,0x10000000000000000000000000000000⟩,
⟨2052,2,0x2b581d407,0xf7b541fd50007fad6,0x0⟩,
⟨2054,3,0x2b5800007,0xf7b5400000007fad6,0x10000000000000000000000000000000⟩,
⟨2064,2,0x15b583a7,0x7b57dc15fe97f056,0x0⟩,
⟨2065,3,0x3583a7,0x3dc15fe97f056,0x0⟩,
⟨2066,3,0x158003a7,0x7b540000fe97f056,0x38000000000000000000000000000000⟩,
⟨2080,2,0x2a0b5d481,0xf0357dfd57090fa82,0x2000000000000000000000000000000000⟩,
⟨2081,3,0x35d481,0x3dfd57090fa82,0x2500000000000000000000000000000000⟩,
⟨2084,3,0x2a081d401,0xf03541fd50000fa82,0x2000000000000000000000000000000000⟩,
⟨2112,2,0x2a535d522,0xf3857dfd5b6133a94,0x0⟩,
⟨2113,3,0x35d522,0x3dfd5b6133a94,0x0⟩,
⟨2116,3,0x2a501d402,0xf38541fd500033a94,0x0⟩,
⟨2144,3,0x2a035d400,0xf0057dfd530103a80,0x1002000000000000000000000000000000000⟩,
⟨2145,4,0x35d400,0x3dfd530103a80,0x1282500000000000000000000000000000000⟩,
⟨2148,4,0x2a001d400,0xf00541fd500003a80,0x1002000000000000000000000000000000000⟩,
⟨2176,2,0xb5149726,0x77916cdc5de1752d4,0x0⟩,
⟨2177,3,0x149726,0x2cdc5de1752d4,0x0⟩,
⟨2178,3,0xb5000326,0x779140000de1752d4,0x4000000000000000000000000000000000000⟩,
⟨2180,3,0xb5009406,0x779140dc5000752d4,0x0⟩,
⟨2182,4,0xb5000006,0x779140000000752d4,0x4000000000000000000000000000000000000⟩,
⟨2192,3,0x15148326,0x7916cc05de175054,0x0⟩,
⟨2193,4,0x148326,0x2cc05de175054,0x0⟩,
⟨2194,4,0x15000326,0x79140000de175054,0xe000000000000000000000000000000000000⟩,
⟨2240,3,0xa5149522,0x73816cdc596131294,0x0⟩,
⟨2241,4,0x149522,0x2cdc596131294,0x0⟩,
⟨2244,4,0xa5009402,0x738140dc500031294,0x0⟩,
⟨2304,2,0x231b1c787,0xb5b475ed1fa87f8c6,0x0⟩,
⟨2305,3,0x31c787,0x35ed1fa87f8c6,0x0⟩,
⟨2306,3,0x231800387,0xb5b440000fa87f8c6,0x0⟩,
⟨2308,3,0x23181c407,0xb5b441ed10007f8c6,0x0⟩,
⟨2310,4,0x231800007,0xb5b4400000007f8c6,0x0⟩,
⟨2320,3,0x11b18387,0x5b475c11fa87f046,0x0⟩,
⟨2321,4,0x318387,0x35c11fa87f046,0x0⟩,
⟨2322,4,0x11800387,0x5b440000fa87f046,0x0⟩,
⟨2336,3,0x220b1c481,0xb03475ed17080f882,0x0⟩,
⟨2337,4,0x31c481,0x35ed17080f882,0x0⟩,
⟨2340,4,0x22081c401,0xb03441ed10000f882,0x0⟩]
private def T0f : Array TriFeature := #[⟨2240,0x3ff80003fffffffffff8000003ff⟩,
⟨1216,0xffe0000ffc000000000fffffffff8000003ff⟩,
⟨1568,0x1ffffc71fc00000000000000003fffff83c3f⟩,
⟨2336,0x7ffff1c7f0000ffe007fff83c3f⟩,
⟨800,0x1ffc71fc007ff1c7f0000000007fff83c3f⟩,
⟨2144,0x7f8ff007f1fe0ffe3f83ff8003f⟩,
⟨1120,0x1fe3fc01fc0000000001fe0ffe3f83ff8003f⟩,
⟨1552,0xe3fc7ffe3c0000000000000001c7fc7ffffcf⟩,
⟨2320,0x38ff1fff8f001f1fe007c7ffffcf⟩,
⟨784,0x1c7ffe3c0071fff8f0000000007c7ffffcf⟩,
⟨2192,0x38f800ff8fe3ff1ffc780007ffcf⟩,
⟨1168,0xe3e003fe3c000000000e3ff1ffc780007ffcf⟩,
⟨1544,0xfffffffffc0000000000000001ff9f879ccf1⟩,
⟨1160,0xffe003fffc000000000ffe7e1fff80001ccf1⟩,
⟨1096,0xffe3fc0ffc000000000ffe7e1fff8387800f1⟩,
⟨200,0xffe0000ffdf380001f3ffe7e1fff8000000f1⟩,
⟨1064,0x1ffffc71fc0000000001fe0e1e3f9f8780c31⟩,
⟨552,0x1ffffc71fc003e70c7300000003f9f8780c31⟩,
⟨104,0x1fe3fc01fc738e700731fe0e1e3f838780031⟩,
⟨2308,0x3fffffffff000be66002f99ad572⟩,
⟨772,0xf9db7cc007ffffff0000000002f99ad572⟩,
⟨2180,0x3ff800ffff7cebe66f980002d572⟩,
⟨2116,0x3ff8ff03ff7cebe66f9839980172⟩,
⟨196,0x7ce00007cfff80003ff7cebe66f9800000172⟩,
⟨2084,0x7ffff1c7f1ce0e6639af9981432⟩,
⟨548,0x1cef9c31cc007ff1c7f000000039af9981432⟩,
⟨292,0xf9c31cc7ffff1c7f0000e66002f9981432⟩,
⟨100,0x1ce39c01cc7f8ff007f1ce0e6639839980032⟩,
⟨524,0x7cef9db7cc003e76df30000000f98f818c470⟩,
⟨140,0x7ce001b7cdf38006df37ce3e06f980000c470⟩,
⟨76,0x7ce39c07cdf38e701f37ce3e06f9838180070⟩,
⟨44,0x1cef9c31cc73be70c731ce0e06398f8180430⟩,
⟨1538,0xed7daffed40000000000000001dafdaafffd4⟩,
⟨2306,0x3b5f6bffb5001f6aa007daafffd4⟩,
⟨770,0x1daffed40076bffb50000000007daafffd4⟩,
⟨2178,0x3b5800ffb5ed7f6abda80007ffd4⟩,
⟨1154,0xed6003fed4000000000ed7f6abda80007ffd4⟩,
⟨2066,0x385f0bff85e17f0abc2fc2afffc4⟩,
⟨1042,0xe17c2ffe14000000000e17f0abc2fc2afffc4⟩,
⟨530,0xe17c2ffe140070bff850000001c2fc2afffc4⟩,
⟨274,0x1c2ffe1785f0bff85001f0aa007c2afffc4⟩,
⟨146,0xe16003fe1785800ff85e17f0abc280007ffc4⟩,
⟨1034,0xed7daffed4000000000ed6760bda9d829ccd0⟩,
⟨522,0xed7daffed4003636db10000001da9d829ccd0⟩,
⟨138,0xed6003fed5b18006db1ed6760bda80001ccd0⟩,
⟨2054,0x3b5f6bffb56c6b622d8ad88ad550⟩,
⟨518,0x6c6d8db6c40076bffb50000000d8ad88ad550⟩,
⟨262,0xd8db6c7b5f6bffb5000b622002d88ad550⟩,
⟨134,0x6c6001b6c7b5800ffb56c6b622d880002d550⟩,
⟨14,0x6c6d8db6c5b1b636db16c63602d88d808c450⟩,
⟨1537,0xb7b6f6db7800000000000000016f76ff77baf⟩,
⟨2305,0x2dedbdb6de001dbfc0076ff77baf⟩,
⟨769,0x16f6db78005bdb6de00000000076ff77baf⟩,
⟨2177,0x2de800b6deb7bdbfd6f000077baf⟩,
⟨1153,0xb7a002db78000000000b7bdbfd6f000077baf⟩,
⟨2113,0x2de8bd02deb7bdbfd6f02ff003af⟩,
⟨1089,0xb7a2f40b78000000000b7bdbfd6f02ff003af⟩,
⟨193,0xb7a0000b7ade80002deb7bdbfd6f0000003af⟩,
⟨2081,0x5edbd145e17a0bfc2f76ff0382f⟩,
⟨1057,0x17b6f4517800000000017a0bfc2f76ff0382f⟩,
⟨545,0x17b6f45178005bd145e00000002f76ff0382f⟩,
⟨289,0x16f451785edbd145e0000bfc0076ff0382f⟩,
⟨97,0x17a2f401785e8bd005e17a0bfc2f02ff0002f⟩,
⟨2065,0x28ed1db68ea3bd1fd47747f77b8f⟩,
⟨1041,0xa3b476da38000000000a3bd1fd47747f77b8f⟩,
⟨529,0xa3b476da380051db68e000000147747f77b8f⟩,
⟨273,0x1476da3a8ed1db68e001d1fc00747f77b8f⟩,
⟨145,0xa3a002da3a8e800b68ea3bd1fd47000077b8f⟩]
private def T0c : Array Nat := #[0x0,0x0,0x2004125c008010497002122e4b848b85df7,0x25e4bcfffc9792f3fff25efeffffbfbfbffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffff]
private abbrev T0b : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private def T0q : List Nat := [1224,1576,1128,2244,2340,804,2148,204,556,108,1554,2322,786,2194,1170,1546,1162,2310,774,2182,526,142,2241,1217,1569,2337,801,2145,1121,1553,2321,785,2193,1169]
private def T0k : List (List Nat) := [[14,129,801],[14,145,801],[14,193,769],[14,193,785],[14,193,801],[14,513,2241],[14,529,2241],[14,545,2177],[14,545,2193],[14,545,2241],[14,769,1217],[14,769,2241],[14,801,1153],[14,801,2177],[14,1537,2241],[14,1569,2177],[97,1026,2310],[97,1034,2306],[97,1034,2310],[97,1034,2322],[97,1042,2310],[97,1154,2310],[97,1162,2306],[97,1538,2054],[97,1538,2182],[97,1538,2310],[97,1546,2050],[97,1546,2054],[97,1546,2066],[97,1546,2178],[97,1546,2306],[97,1554,2054],[129,142,800],[129,142,801],[129,142,804],[129,526,801],[132,800,1169],[132,801,1169],[132,804,1041],[132,804,1169],[132,804,1553],[134,800,1153],[134,800,1169],[134,800,1217],[134,801,1153],[134,804,1041],[134,804,1153],[140,145,800],[140,145,801],[140,145,804],[140,800,1169],[140,800,2193],[140,804,1041],[142,145,800],[142,193,769],[142,193,800],[142,513,2241],[142,545,2177],[142,800,1153],[142,800,2177],[145,204,800],[146,1056,2340],[146,1057,2340],[146,1064,2336],[146,1064,2337],[146,1064,2340],[146,1120,2340],[146,1128,2336],[146,1568,2084],[146,1568,2148],[146,1568,2340],[146,1569,2084],[146,1576,2080],[146,1576,2081],[146,1576,2084],[146,1576,2144],[146,1576,2336],[193,526,769],[196,772,1041],[196,772,1169],[196,772,1553],[196,774,1041],[196,800,1169],[196,804,1041],[204,772,1041],[513,526,2240],[513,526,2241],[513,526,2244],[516,1041,2244],[516,1169,2244],[516,1553,2240],[516,1553,2241],[516,1553,2244],[518,1041,2244],[518,1537,2240],[518,1537,2241],[518,1537,2244],[518,1553,2240],[518,1569,2240],[524,529,2240],[524,529,2241],[524,529,2244],[524,785,2240],[524,1041,2244],[524,1553,2240],[526,529,2240],[526,545,2177],[526,545,2240],[526,769,2240],[526,1537,2240],[529,556,2240],[548,1041,2180],[548,1041,2182],[548,1041,2244],[548,1169,2180],[548,1553,2180],[548,1553,2240],[556,1041,2180],[772,1041,2244],[772,1553,2240],[774,1537,2240],[800,1153,2182],[800,1169,2180],[804,1041,2180],[1026,1121,2308],[1026,1121,2310],[1026,1121,2340],[1026,2145,2310],[1034,1121,2306],[1034,1121,2308],[1034,2145,2306],[1042,1120,2308],[1042,1120,2310],[1042,1120,2340],[1042,1121,2308],[1042,1128,2308],[1056,1170,2308],[1056,1170,2310],[1056,1170,2340],[1056,2194,2340],[1057,1154,2308],[1057,1154,2310],[1057,1154,2340],[1057,1162,2308],[1057,1170,2308],[1064,1170,2308],[1064,1170,2336],[1064,2194,2336],[1120,1170,2308],[1120,1554,2308],[1121,1154,2308],[1121,1538,2054],[1121,1538,2308],[1121,1546,2050],[1154,1569,2308],[1170,1568,2084],[1170,1568,2308],[1170,1576,2080],[1538,2054,2145],[1544,2050,2145],[1544,2054,2145],[1544,2066,2144],[1544,2066,2145],[1544,2066,2148],[1544,2080,2194],[1544,2081,2178],[1544,2081,2182],[1544,2081,2194],[1544,2084,2194],[1544,2144,2194],[1544,2144,2322],[1544,2145,2178],[1544,2145,2306],[1544,2178,2337],[1544,2194,2336],[1546,2050,2145],[1546,2066,2144],[1546,2080,2194],[1546,2081,2178],[1568,2084,2194],[1576,2050,2145],[1576,2066,2144],[1576,2080,2194],[1576,2081,2178]]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T0checked : trioTest T0a T0f T0c 10 (fun x y z=>decide ([x,y,z]∈T0k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T0valid : trioValidated T0b T0a T0q T0f T0c 10=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T0close : T0k.all (fun cs=>decide (norm2 (attach cs T0b)∈atlas))=true := by decide +kernel
private theorem B3_0ok {cs : List Nat} (ex : Extension 6 3 T0b cs) (he : edges_ (attach cs T0b)≤33) : norm2 (attach cs T0b)∈atlas :=
  triExtension norm2 atlas T0b T0a T0q T0f T0c 10 T0k (by decide +kernel) T0valid T0checked T0close ex he
private def T1a : List TrioAtom := [⟨6,2,0x3ffc0007,0xffffc0000007ffff,0x400048490924840000000000008000⟩,
⟨10,2,0x3ffc0038,0xffffc00003f80fff,0x24200410040000104010008002000008040⟩,
⟨12,2,0x3ffc1f00,0xffffc07fe0000fff,0x4010002008010000802001000401000010⟩,
⟨14,3,0x3ffc0000,0xffffc00000000fff,0x2429249214849092485210900a429088450⟩,
⟨17,2,0x3e0ff,0x3f83fffff07f,0x40600000042200⟩,
⟨18,2,0x1fc00ff,0x7ffc0001ffff07f,0xe0004000038400000000000007c000⟩,
⟨33,2,0x3ff01,0x3fffec38ff83,0x24000012825001280000500002500000⟩,
⟨36,2,0x3e0c7f01,0xf83fc3ffe000ff83,0x20000008038000800000000002000000⟩,
⟨40,2,0x3e0d9f00,0xf83fdc7fe0380f83,0x4020000000020000002000000402000000⟩,
⟨44,3,0x3e0c1f00,0xf83fc07fe0000f83,0x4038002008038000802001000403800000⟩,
⟨65,2,0x3ff5a,0x3ffff5db3f9c,0x4a00440000000000⟩,
⟨68,2,0x3e707f02,0xfbc7c3ffe0033f9c,0x8010000804000000000000000⟩,
⟨72,2,0x3e719f18,0xfbc7dc7fe1d80f9c,0x4000000000000000007000000400000000⟩,
⟨76,3,0x3e701f00,0xfbc7c07fe0000f9c,0x4010002008010000807001000401000000⟩,
⟨96,2,0x3e03ff00,0xf807ffffe4183f80,0x8020004010020001004002000802000000⟩,
⟨97,3,0x3ff00,0x3fffe4183f80,0x9424004a12825001284a02550942500000⟩,
⟨100,3,0x3e007f00,0xf807c3ffe0003f80,0x802000401c038001c04002000802000000⟩,
⟨104,3,0x3e019f00,0xf807dc7fe0180f80,0xe020004010020001007002000e02000000⟩,
⟨108,4,0x3e001f00,0xf807c07fe0000f80,0xe03800701c038001c07003800e03800000⟩,
⟨129,2,0x3a7fe,0x3dbcffff53fc,0x38000400000000000⟩,
⟨130,2,0xff000fe,0x7fd9c0001fff53fc,0x20000410040000104038008002000000000⟩,
⟨136,2,0xff18738,0x7fd9dc3ce3f803fc,0x4000000000000000038000000000000000⟩,
⟨138,3,0xff00038,0x7fd9c00003f803fc,0x24200410040000104038008002000000000⟩,
⟨144,2,0x1f3a0fe,0x7d9fd80ffff507c,0x38050000000000000⟩,
⟨145,3,0x3a0fe,0x3d80ffff507c,0x38050600000000000⟩,
⟨146,3,0x1f000fe,0x7d9c0001fff507c,0x70000e380e000038e03807c007000000000⟩,
⟨192,2,0xe73a75a,0x7bc1fdbcf5db139c,0x3ff80000000000000⟩,
⟨193,3,0x3a75a,0x3dbcf5db139c,0x3ff80440000000000⟩,
⟨200,3,0xe718718,0x7bc1dc3ce1d8039c,0x400000000000000003ff80000400000000⟩,
⟨257,2,0x279e7,0x2fdf3ee7fce7,0x100000000000400000000000⟩,
⟨258,2,0x339c00e7,0xbdfe40001ee7fce7,0x400040100104000000000000000000⟩,
⟨260,2,0x339c7907,0xbdfe43df2007fce7,0x81d0800800000000000000000⟩,
⟨262,3,0x339c0007,0xbdfe40000007fce7,0x4000485d0924840000000000000000⟩,
⟨272,2,0x19e60e7,0x5fe6f833ee7f067,0x40100240000000000000000000⟩,
⟨273,3,0x260e7,0x2f833ee7f067,0xe0100248000060600000000000⟩,
⟨274,3,0x19c00e7,0x5fe40001ee7f067,0xe000401003c4000000000000000000⟩,
⟨288,2,0x320e7901,0xb83e6fdf2c20fc83,0x20000008127000000000000000000000⟩,
⟨289,3,0x27901,0x2fdf2c20fc83,0x2400001e927001280000500000000000⟩,
⟨292,3,0x320c7901,0xb83e43df2000fc83,0x200000081ffc00800000000000000000⟩,
⟨513,2,0xdaad,0x36ef5b6ded6b,0xc0000000000000000000400000000000⟩,
⟨514,2,0x35ac00ad,0xdefe80001b6ded6b,0xc0480040000104000000000000000000⟩,
⟨516,2,0x35ac5a05,0xdefe82ef4005ed6b,0xc0000008010000800000000000000000⟩,
⟨518,3,0x35ac0005,0xdefe80000005ed6b,0xc0480048490924840000000000000000⟩,
⟨520,2,0x35ac9a28,0xdefe946f43680d6b,0x40d2002000000000000000000000000000⟩,
⟨522,3,0x35ac0028,0xdefe800003680d6b,0x242d2492140000104010008000000000000⟩,
⟨524,3,0x35ac1a00,0xdefe806f40000d6b,0x40d2002008010000802001000000000000⟩,
⟨526,4,0x35ac0000,0xdefe800000000d6b,0x242d2492148490924852109000000000000⟩,
⟨528,2,0x1acc0ad,0x6feb6835b6de06b,0xc0000000000000000000000000000000⟩,
⟨529,3,0xc0ad,0x36835b6de06b,0xc0000000000000000040000000000000⟩,
⟨530,3,0x1ac00ad,0x6fe80001b6de06b,0xc0fc0040000384000000000000000000⟩,
⟨544,2,0x340cda01,0xd83eb6ef4828ed03,0xff000000020000000000000000000000⟩,
⟨545,3,0xda01,0x36ef4828ed03,0xff000012825001280000000000000000⟩,
⟨548,3,0x340c5a01,0xd83e82ef4000ed03,0xff000008038000800000000000000000⟩,
⟨552,3,0x340c9a00,0xd83e946f40280d03,0x40ff002000020000002000000000000000⟩,
⟨556,4,0x340c1a00,0xd83e806f40000d03,0x40ff002008038000802000000000000000⟩,
⟨768,2,0x318c58a5,0x9cfe26cf1a65ec63,0xc00000001c0000000000000000000000⟩,
⟨769,3,0x58a5,0x26cf1a65ec63,0xc00000001c0000000000000000000000⟩,
⟨770,3,0x318c00a5,0x9cfe00001a65ec63,0xc04800401c0124000000000000000000⟩,
⟨772,3,0x318c5805,0x9cfe02cf0005ec63,0xc00000081d0800800000000000000000⟩,
⟨774,4,0x318c0005,0x9cfe00000005ec63,0xc04800485d0924840000000000000000⟩,
⟨784,3,0x18c40a5,0x4fe26831a65e063,0xc00000401c03f4000000000000000000⟩,
⟨785,4,0x40a5,0x26831a65e063,0xc00000e01c03fe000000000000000000⟩,
⟨786,4,0x18c00a5,0x4fe00001a65e063,0xc0fc00401c03f4000000000000000000⟩,
⟨800,3,0x300c5801,0x983e26cf0820ec03,0xff0000081ffc00800000000000000000⟩,
⟨801,4,0x5801,0x26cf0820ec03,0xff00001e9ffc01e80000000000000000⟩,
⟨804,4,0x300c5801,0x983e02cf0000ec03,0xff0000081ffc00800000000000000000⟩,
⟨1025,2,0x38ef8,0x3f75dffe8739,0x41800000800000000000000000000000000⟩,
⟨1026,2,0x1ce400f8,0xef6b80001ffe8739,0x71800410040000104000000000000000000⟩,
⟨1032,2,0x1ce58e38,0xef6b9c75c3f80739,0x7ff00000000000000000000000000000000⟩,
⟨1034,3,0x1ce40038,0xef6b800003f80739,0x7ff00410040000104000000000000000000⟩,
⟨1040,2,0xe780f8,0x76bbf01dffe8039,0x41800820000000000000000000000000000⟩,
⟨1041,3,0x380f8,0x3f01dffe8039,0x41800920c00000000000000000000000000⟩,
⟨1042,3,0xe400f8,0x76b80001ffe8039,0x71800e38040000384000000000000000000⟩,
⟨1056,2,0x1c078e00,0xe82bbf75cc388701,0x49c20004000020000000000000000000000⟩,
⟨1057,3,0x38e00,0x3f75cc388701,0x49c24004a12825000000000000000000000⟩,
⟨1064,3,0x1c058e00,0xe82b9c75c0380701,0x7ff20004000020000000000000000000000⟩,
⟨1088,2,0x1c638e58,0xeb43bf75d5da0718,0x41800000000000000000000000000000000⟩,
⟨1089,3,0x38e58,0x3f75d5da0718,0x41800000800000000000000000000000000⟩,
⟨1096,3,0x1c618e18,0xeb439c75c1d80718,0x7ff00000000000000000000000000000000⟩,
⟨1120,3,0x1c038e00,0xe803bf75c4180700,0x49c20004010020000000000000000000000⟩,
⟨1121,4,0x38e00,0x3f75c4180700,0x49c24004a12825000000000000000000000⟩,
⟨1128,4,0x1c018e00,0xe8039c75c0180700,0x7ff20004010020000000000000000000000⟩,
⟨1152,2,0xce386f8,0x6f49bd34dffe0338,0x41800000000000000000000000000000000⟩,
⟨1153,3,0x386f8,0x3d34dffe0338,0x41800000800000000000000000000000000⟩,
⟨1154,3,0xce000f8,0x6f4980001ffe0338,0x71800410040000000000000000000000000⟩,
⟨1160,3,0xce18638,0x6f499c34c3f80338,0x7ff00000000000000000000000000000000⟩,
⟨1162,4,0xce00038,0x6f49800003f80338,0x7ff00410040000000000000000000000000⟩,
⟨1168,3,0xe380f8,0x749bd00dffe0038,0x41800820000000000000000000000000000⟩,
⟨1169,4,0x380f8,0x3d00dffe0038,0x41800920c00000000000000000000000000⟩,
⟨1170,4,0xe000f8,0x74980001ffe0038,0x71800e380e0000000000000000000000000⟩,
⟨1216,3,0xc638658,0x6b41bd34d5da0318,0x41800000000000000000000000000000000⟩,
⟨1217,4,0x38658,0x3d34d5da0318,0x41800000800000000000000000000000000⟩,
⟨1224,4,0xc618618,0x6b419c34c1d80318,0x7ff00000000000000000000000000000000⟩,
⟨1536,2,0x14a48aa8,0xce6ab6655b6c8529,0x718c0ff8c00000000000000000000000000⟩,
⟨1537,3,0x8aa8,0x36655b6c8529,0x718c0ff8c00000000000000000000000000⟩,
⟨1538,3,0x14a400a8,0xce6a80001b6c8529,0x718c0ff8c40000000000000000000000000⟩,
⟨1544,3,0x14a48a28,0xce6a946543680529,0x7ffffffff00000000000000000000000000⟩,
⟨1546,4,0x14a40028,0xce6a800003680529,0x7ffffffff40000000000000000000000000⟩,
⟨1552,3,0xa480a8,0x66ab6015b6c8029,0x718c0ff8c00000000000000000000000000⟩,
⟨1553,4,0x80a8,0x36015b6c8029,0x718c0ff8c00000000000000000000000000⟩,
⟨1554,4,0xa400a8,0x66a80001b6c8029,0x718c0ff8c40000000000000000000000000⟩,
⟨1568,3,0x14048a00,0xc82ab66548288501,0x7ffffffff00000000000000000000000000⟩,
⟨1569,4,0x8a00,0x366548288501,0x7ffffffff00000000000000000000000000⟩,
⟨1576,4,0x14048a00,0xc82a946540280501,0x7ffffffff00000000000000000000000000⟩,
⟨2049,2,0x375d7,0x3bfabf97fad6,0x0⟩,
⟨2050,2,0x2b5800d7,0xf7b540001f97fad6,0x400000000000000000000000000000⟩,
⟨2052,2,0x2b587507,0xf7b543faa007fad6,0x0⟩,
⟨2054,3,0x2b580007,0xf7b540000007fad6,0x400000000000000000000000000000⟩,
⟨2064,2,0x15b60d7,0x7b57b82bf97f056,0x0⟩,
⟨2065,3,0x360d7,0x3b82bf97f056,0x0⟩,
⟨2066,3,0x15800d7,0x7b540001f97f056,0xe00000000000000000000000000000⟩,
⟨2080,2,0x2a0b7501,0xf0357bfaac10fa82,0x20000000000000000000000000000000⟩,
⟨2081,3,0x37501,0x3bfaac10fa82,0x24000000000000000000000000000000⟩,
⟨2084,3,0x2a087501,0xf03543faa000fa82,0x20000000000000000000000000000000⟩,
⟨2112,2,0x2a537552,0xf3857bfab5933a94,0x0⟩,
⟨2113,3,0x37552,0x3bfab5933a94,0x0⟩,
⟨2116,3,0x2a507502,0xf38543faa0033a94,0x0⟩,
⟨2144,3,0x2a037500,0xf0057bfaa4103a80,0x8020000000000000000000000000000000⟩,
⟨2145,4,0x37500,0x3bfaa4103a80,0x9424000000000000000000000000000000⟩,
⟨2148,4,0x2a007500,0xf00543faa0003a80,0x8020000000000000000000000000000000⟩,
⟨2176,2,0xb5325d6,0x779179b8bf9752d4,0x0⟩,
⟨2177,3,0x325d6,0x39b8bf9752d4,0x0⟩,
⟨2178,3,0xb5000d6,0x779140001f9752d4,0x20000000000000000000000000000000000⟩,
⟨2192,3,0x15320d6,0x7917980bf975054,0x0⟩,
⟨2193,4,0x320d6,0x3980bf975054,0x0⟩,
⟨2194,4,0x15000d6,0x79140001f975054,0x70000000000000000000000000000000000⟩,
⟨2240,3,0xa532552,0x738179b8b5931294,0x0⟩,
⟨2241,4,0x32552,0x39b8b5931294,0x0⟩,
⟨2304,2,0x231a71c7,0xb5b46bda3e87f8c6,0x0⟩,
⟨2305,3,0x271c7,0x2bda3e87f8c6,0x0⟩,
⟨2306,3,0x231800c7,0xb5b440001e87f8c6,0x0⟩,
⟨2308,3,0x23187107,0xb5b443da2007f8c6,0x0⟩,
⟨2310,4,0x23180007,0xb5b440000007f8c6,0x0⟩,
⟨2320,3,0x11a60c7,0x5b46b823e87f046,0x0⟩,
⟨2321,4,0x260c7,0x2b823e87f046,0x0⟩,
⟨2322,4,0x11800c7,0x5b440001e87f046,0x0⟩,
⟨2336,3,0x220a7101,0xb0346bda2c00f882,0x0⟩,
⟨2337,4,0x27101,0x2bda2c00f882,0x0⟩,
⟨2340,4,0x22087101,0xb03443da2000f882,0x0⟩]
private def T1f : Array TriFeature := #[⟨2240,0xffe0000fffffffffffe00003ff⟩,
⟨1216,0x7ff0003ff0000000003ffffffffe00003ff⟩,
⟨1568,0xffff1c7f00000000000000000ffff83c3f⟩,
⟨2336,0x1ffffc71fc0003ff801ff83c3f⟩,
⟨800,0xff1c7f001ffc71fc000000001ff83c3f⟩,
⟨2144,0x1fe3fc01fc7f83ff8fe3f8003f⟩,
⟨1120,0xff3f007f00000000007f83ff8fe3f8003f⟩,
⟨1552,0x71fc7ff8f000000000000000071fc7fffcf⟩,
⟨2320,0xe3fc7ffe3c007c7f801c7fffcf⟩,
⟨784,0xc7ff8f001c7ffe3c000000001c7fffcf⟩,
⟨2192,0xe3e003fe3f8ffc7ff1e007ffcf⟩,
⟨1168,0x71f00ff8f00000000038ffc7ff1e007ffcf⟩,
⟨1544,0x7ffffffff00000000000000007fef99ccf1⟩,
⟨1160,0x7ff00ffff0000000003ff9f87ffe001ccf1⟩,
⟨1096,0x7ff3f03ff0000000003ff9f87ffe39800f1⟩,
⟨200,0x7ff0003ff7ce00007cfff9f87ffe00000f1⟩,
⟨1064,0xffff1c7f00000000007f83878fef980c31⟩,
⟨552,0xffff1c7f000f9c31cc0000000fef980c31⟩,
⟨104,0xff3f007f1ce39c01cc7f83878fe3980031⟩,
⟨2308,0xfffffffffc002f99801ffad572⟩,
⟨772,0xff6df3001ffffffc000000001ffad572⟩,
⟨2116,0xffe3fc0ffdf3af99be63f80172⟩,
⟨2084,0x1ffffc71fc7383998e7ff81432⟩,
⟨548,0xe7ff0c73001ffc71fc0000000e7ff81432⟩,
⟨292,0xff0c731ffffc71fc000399801ff81432⟩,
⟨100,0xe73f00731fe3fc01fc7383998e63f80032⟩,
⟨524,0x3e7ff6df3000f9db7cc0000003e6f98c470⟩,
⟨76,0x3e73f01f37ce39c07cdf38f81be63980070⟩,
⟨44,0xe7ff0c731cef9c31cc7383818e6f980430⟩,
⟨1538,0x76bdbffb5000000000000000076bdafffd4⟩,
⟨2306,0xed7daffed4007daa801dafffd4⟩,
⟨770,0xdbffb5001daffed4000000001dafffd4⟩,
⟨2178,0xed6003fed7b5fdaaf6a007ffd4⟩,
⟨1154,0x76b00ffb50000000003b5fdaaf6a007ffd4⟩,
⟨2066,0xe17c2ffe1785fc2af0bc2fffc4⟩,
⟨1042,0x70bc3ff85000000000385fc2af0bc2fffc4⟩,
⟨530,0x70bc3ff85001c2ffe1400000070bc2fffc4⟩,
⟨274,0xc3ff85e17c2ffe14007c2a801c2fffc4⟩,
⟨146,0x70b00ff85e16003fe1785fc2af0a007ffc4⟩,
⟨1034,0x76bdbffb50000000003b59d82f6ad89ccd0⟩,
⟨522,0x76bdbffb5000d8db6c400000076ad89ccd0⟩,
⟨138,0x76b00ffb56c6001b6c7b59d82f6a001ccd0⟩,
⟨2054,0xed7daffed5b1ad88b63daad550⟩,
⟨518,0x363db6db1001daffed4000000363daad550⟩,
⟨262,0xdb6db1ed7daffed4002d88801daad550⟩,
⟨14,0x363db6db16c6d8db6c5b18d80b62d88c450⟩,
⟨1537,0x5bd6db6de00000000000000005bd6f77baf⟩,
⟨2305,0xb7b6f6db780076ff0016f77baf⟩,
⟨769,0x6db6de0016f6db780000000016f77baf⟩,
⟨2177,0xb7a002db7adef6ff5bc0077baf⟩,
⟨1153,0x5bd00b6de0000000002def6ff5bc0077baf⟩,
⟨2113,0xb7a2f40b7adef6ff5bc2f003af⟩,
⟨1089,0x5bd2d02de0000000002def6ff5bc2f003af⟩,
⟨193,0x5bd0002deb7a0000b7adef6ff5bc00003af⟩,
⟨2081,0x17b6f451785e82ff0bd6f0382f⟩,
⟨1057,0xbd6d145e00000000005e82ff0bd6f0382f⟩,
⟨545,0xbd6d145e0016f451780000000bd6f0382f⟩,
⟨289,0x6d145e17b6f451780002ff0016f0382f⟩,
⟨97,0xbd2d005e17a2f401785e82ff0bc2f0002f⟩,
⟨2065,0xa3b476da3a8ef47f51d4777b8f⟩,
⟨1041,0x51d45b68e00000000028ef47f51d4777b8f⟩,
⟨529,0x51d45b68e001476da3800000051d4777b8f⟩,
⟨273,0x45b68ea3b476da3800747f0014777b8f⟩,
⟨145,0x51d00b68ea3a002da3a8ef47f51c0077b8f⟩]
private def T1c : Array Nat := #[0x0,0x0,0x1010497002004125c00848b92e4b85df7,0x12f4f3fff25e4bcfffc97bfbffffffbffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff]
private abbrev T1b : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private def T1q : List Nat := [1224,1576,1128,2340,804,2148,556,108,1554,2322,786,2194,1170,1546,1162,2310,774,526,2241,1217,1569,2337,801,2145,1121,1553,2321,785,2193,1169]
private def T1k : List (List Nat) := [[6,1537,2145],[10,1569,2081],[10,1569,2305],[14,129,801],[14,193,769],[14,513,2241],[14,545,2177],[14,1537,2081],[14,1537,2113],[14,1569,2049],[18,1569,2144],[33,1546,2178],[97,1026,2310],[97,1034,2306],[97,1538,2054],[97,1546,2050],[146,1056,2340],[146,1064,2336],[146,1568,2084],[146,1568,2144],[146,1576,2080],[513,526,2240],[514,1569,2113],[514,1569,2240],[516,1553,2240],[518,1537,2113],[518,1537,2240],[522,545,2177],[522,545,2240],[522,1569,2049],[524,529,2240],[530,1569,2112],[545,1538,2240],[545,1546,2176],[1026,1121,2308],[1034,1057,2306],[1034,1057,2308],[1034,1569,2304],[1042,1120,2308],[1056,1170,2308],[1057,1154,2308],[1057,1546,2050],[1536,2054,2145],[1538,1569,2112],[1544,2050,2145],[1544,2066,2144],[1544,2080,2194],[1544,2081,2178],[1568,2050,2145],[1568,2066,2144]]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T1checked : trioTest T1a T1f T1c 9 (fun x y z=>decide ([x,y,z]∈T1k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T1valid : trioValidated T1b T1a T1q T1f T1c 9=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T1close : T1k.all (fun cs=>decide (norm2 (attach cs T1b)∈atlas))=true := by decide +kernel
private theorem B3_1ok {cs : List Nat} (ex : Extension 6 3 T1b cs) (he : edges_ (attach cs T1b)≤33) : norm2 (attach cs T1b)∈atlas :=
  triExtension norm2 atlas T1b T1a T1q T1f T1c 9 T1k (by decide +kernel) T1valid T1checked T1close ex he
private def T2a : List TrioAtom := [⟨6,2,0x3ffc0007,0xffffc0000007ffff,0x80009092124908000000000008000⟩,
⟨10,2,0x3ffc0038,0xffffc00003f80fff,0x24248492420000020000000000000008000⟩,
⟨12,2,0x3ffc1f00,0xffffc07fe0000fff,0x4008000401002000100804010010000010⟩,
⟨14,3,0x3ffc0000,0xffffc00000000fff,0x2424849242909212490c924290890088450⟩,
⟨17,2,0x3e0ff,0x3f83fffff07f,0x406042200⟩,
⟨18,2,0x1fc00ff,0x7ffc0001ffff07f,0x1c000000007000000000000007c000⟩,
⟨33,2,0x3ff49,0x3fffec78ff83,0x12800000004a00000000000025500000⟩,
⟨36,2,0x3e0c7f01,0xf83fc3ffe000ff83,0x10000001007000100000000020000000⟩,
⟨40,2,0x3e0d9f08,0xf83fdc7fe0780f83,0x401c000400004000000000000020000000⟩,
⟨44,3,0x3e0c1f00,0xf83fc07fe0000f83,0x401c000401007000100804010038000000⟩,
⟨65,2,0x3ff12,0x3ffff59b3f9c,0x1200000004000000⟩,
⟨68,2,0x3e707f02,0xfbc7c3ffe0033f9c,0x1002000101000000000000000⟩,
⟨72,2,0x3e719f10,0xfbc7dc7fe1980f9c,0x4008000400000000001000000000000000⟩,
⟨76,3,0x3e701f00,0xfbc7c07fe0000f9c,0x4008000401002000101c04010010000000⟩,
⟨96,2,0x3e03ff00,0xf807ffffe4183f80,0x8010000802004000201008020020000000⟩,
⟨97,3,0x3ff00,0x3fffe4183f80,0x9412800942504a00251209425025500000⟩,
⟨100,3,0x3e007f00,0xf807c3ffe0003f80,0x8010000803807000381008020020000000⟩,
⟨104,3,0x3e019f00,0xf807dc7fe0180f80,0xe01c000e02004000201008020020000000⟩,
⟨108,4,0x3e001f00,0xf807c07fe0000f80,0xe01c000e03807000381c0e038038000000⟩,
⟨129,2,0xa7b6,0x2dbcfbaf53fc,0x6000000004000000⟩,
⟨130,2,0xff000b6,0x7fd9c0001baf53fc,0x20000082008000020806020080000000000⟩,
⟨132,2,0xff02706,0x7fd9c1bce00753fc,0x1002000106000000000000000⟩,
⟨134,3,0xff00006,0x7fd9c000000753fc,0x2000008200909212490e020080000000000⟩,
⟨136,2,0xff08730,0x7fd9cc3ce3a803fc,0x4008000400000000006000000000000000⟩,
⟨138,3,0xff00030,0x7fd9c00003a803fc,0x24248492428000020806020080000000000⟩,
⟨140,3,0xff00700,0x7fd9c03ce00003fc,0x4008000401002000106904010010000000⟩,
⟨142,4,0xff00000,0x7fd9c000000003fc,0x2424849242909212490e924290890000000⟩,
⟨144,2,0x1f0a0b6,0x7d9ed80fbaf507c,0x6000000000000000⟩,
⟨145,3,0xa0b6,0x2d80fbaf507c,0x6000000400000000⟩,
⟨146,3,0x1f000b6,0x7d9c0001baf507c,0x700001c701c000071c060701c0000000000⟩,
⟨192,2,0xe70a712,0x7bc1edbcf18b139c,0x7f80000000000000⟩,
⟨193,3,0xa712,0x2dbcf18b139c,0x7f80000000000000⟩,
⟨196,3,0xe702702,0x7bc1c1bce003139c,0x1002000107f84000000000000⟩,
⟨200,3,0xe708710,0x7bc1cc3ce188039c,0x4008000400000000007f80010000000000⟩,
⟨204,4,0xe700700,0x7bc1c03ce000039c,0x4008000401002000107f84010000000000⟩,
⟨257,2,0x379ef,0x37df3ef7fce7,0x38000000000000000000000⟩,
⟨258,2,0x339c00ef,0xbdfe40001ef7fce7,0x80000038024000000000000000000⟩,
⟨260,2,0x339c7907,0xbdfe43df2007fce7,0x103a100100000000000000000⟩,
⟨262,3,0x339c0007,0xbdfe40000007fce7,0x800090ba124908000000000000000⟩,
⟨272,2,0x19f60ef,0x5fe77833ef7f067,0x38000000000000000000000⟩,
⟨273,3,0x360ef,0x37833ef7f067,0x38000000000000000000000⟩,
⟨274,3,0x19c00ef,0x5fe40001ef7f067,0x1c000003807e000000000000000000⟩,
⟨288,2,0x320f7949,0xb83e77df2c70fc83,0x1000000003ff80000000000000000000⟩,
⟨289,3,0x37949,0x37df2c70fc83,0x1280000003ff80000000000000000000⟩,
⟨292,3,0x320c7901,0xb83e43df2000fc83,0x1000000103ff80100000000000000000⟩,
⟨513,2,0x3dafd,0x3eef5ffded6b,0xe0000000000000000000000000000000⟩,
⟨514,2,0x35ac00fd,0xdefe80001ffded6b,0xe0090000000020000000000000000000⟩,
⟨520,2,0x35ad9a38,0xdefe9c6f43f80d6b,0x40e8400400000000000000000000000000⟩,
⟨522,3,0x35ac0038,0xdefe800003f80d6b,0x242e8492420000020000000000000000000⟩,
⟨528,2,0x1afc0fd,0x6febe835ffde06b,0xe0000000000000000000000000000000⟩,
⟨529,3,0x3c0fd,0x3e835ffde06b,0xe0000000000000000000000000000000⟩,
⟨530,3,0x1ac00fd,0x6fe80001ffde06b,0xe01f8000000070000000000000000000⟩,
⟨544,2,0x340fda49,0xd83ebeef4c78ed03,0xffe00000004000000000000000000000⟩,
⟨545,3,0x3da49,0x3eef4c78ed03,0xffe00000004a00000000000000000000⟩,
⟨552,3,0x340d9a08,0xd83e9c6f40780d03,0x40ffe00400004000000000000000000000⟩,
⟨768,2,0x318f58ed,0x9cfe36cf1ef5ec63,0xe0000000038000000000000000000000⟩,
⟨769,3,0x358ed,0x36cf1ef5ec63,0xe0000000038000000000000000000000⟩,
⟨770,3,0x318c00ed,0x9cfe00001ef5ec63,0xe0090000038024000000000000000000⟩,
⟨784,3,0x18f40ed,0x4fe36831ef5e063,0xe0000000038000000000000000000000⟩,
⟨785,4,0x340ed,0x36831ef5e063,0xe0000000038000000000000000000000⟩,
⟨786,4,0x18c00ed,0x4fe00001ef5e063,0xe01f800003807e000000000000000000⟩,
⟨800,3,0x300f5849,0x983e36cf0c70ec03,0xffe0000003ff80000000000000000000⟩,
⟨801,4,0x35849,0x36cf0c70ec03,0xffe0000003ff80000000000000000000⟩,
⟨1025,2,0x38ef8,0x3f75dffe8739,0x41802000100000000000000000000000000⟩,
⟨1026,2,0x1ce400f8,0xef6b80001ffe8739,0x41840090000000020000000000000000000⟩,
⟨1032,2,0x1ce58e38,0xef6b9c75c3f80739,0x7ff08000400000000000000000000000000⟩,
⟨1034,3,0x1ce40038,0xef6b800003f80739,0x7ff48492420000020000000000000000000⟩,
⟨1040,2,0xe780f8,0x76bbf01dffe8039,0x41840104000000000000000000000000000⟩,
⟨1041,3,0x380f8,0x3f01dffe8039,0x418e3124180000000000000000000000000⟩,
⟨1042,3,0xe400f8,0x76b80001ffe8039,0x418401d4000000070000000000000000000⟩,
⟨1056,2,0x1c078e48,0xe82bbf75cc788701,0x4181c000000004000000000000000000000⟩,
⟨1057,3,0x38e48,0x3f75cc788701,0x4181e800100004a00000000000000000000⟩,
⟨1064,3,0x1c058e08,0xe82b9c75c0780701,0x7ff1c000e00004000000000000000000000⟩,
⟨1088,2,0x1c638e10,0xeb43bf75d59a0718,0x49c08000000000000000000000000000000⟩,
⟨1089,3,0x38e10,0x3f75d59a0718,0x49c1e800940000000000000000000000000⟩,
⟨1096,3,0x1c618e10,0xeb439c75c1980718,0x7ff08000400000000000000000000000000⟩,
⟨1120,3,0x1c038e00,0xe803bf75c4180700,0x49c1c000802004000000000000000000000⟩,
⟨1121,4,0x38e00,0x3f75c4180700,0x49c1e800942504a00000000000000000000⟩,
⟨1128,4,0x1c018e00,0xe8039c75c0180700,0x7ff1c000e02004000000000000000000000⟩,
⟨1152,2,0xce086b0,0x6f49ad34dbae0338,0x71800000000000000000000000000000000⟩,
⟨1153,3,0x86b0,0x2d34dbae0338,0x71802000100000000000000000000000000⟩,
⟨1154,3,0xce000b0,0x6f4980001bae0338,0x71840092008000000000000000000000000⟩,
⟨1160,3,0xce08630,0x6f498c34c3a80338,0x7ff08000400000000000000000000000000⟩,
⟨1162,4,0xce00030,0x6f49800003a80338,0x7ff48492428000000000000000000000000⟩,
⟨1168,3,0xe080b0,0x749ad00dbae0038,0x718401d7000000000000000000000000000⟩,
⟨1169,4,0x80b0,0x2d00dbae0038,0x718e31ff180000000000000000000000000⟩,
⟨1170,4,0xe000b0,0x74980001bae0038,0x718401d701c000000000000000000000000⟩,
⟨1216,3,0xc608610,0x6b41ad34d18a0318,0x7ff08000400000000000000000000000000⟩,
⟨1217,4,0x8610,0x2d34d18a0318,0x7ff1e800f40000000000000000000000000⟩,
⟨1224,4,0xc608610,0x6b418c34c1880318,0x7ff08000400000000000000000000000000⟩,
⟨1536,2,0x14a78af8,0xce6abe655ffc8529,0x418e3124180000000000000000000000000⟩,
⟨1537,3,0x38af8,0x3e655ffc8529,0x418e3124180000000000000000000000000⟩,
⟨1538,3,0x14a400f8,0xce6a80001ffc8529,0x418e31fc180000000000000000000000000⟩,
⟨1544,3,0x14a58a38,0xce6a9c6543f80529,0x7ffffffffe0000000000000000000000000⟩,
⟨1546,4,0x14a40038,0xce6a800003f80529,0x7ffffffffe0000000000000000000000000⟩,
⟨1552,3,0xa780f8,0x66abe015ffc8029,0x418e3124180000000000000000000000000⟩,
⟨1553,4,0x380f8,0x3e015ffc8029,0x418e3124180000000000000000000000000⟩,
⟨1554,4,0xa400f8,0x66a80001ffc8029,0x418e31fc180000000000000000000000000⟩,
⟨1568,3,0x14078a48,0xc82abe654c788501,0x418fff24180000000000000000000000000⟩,
⟨1569,4,0x38a48,0x3e654c788501,0x418fff24180000000000000000000000000⟩,
⟨1576,4,0x14058a08,0xc82a9c6540780501,0x7ffffffffe0000000000000000000000000⟩,
⟨2049,2,0x275c7,0x3bfabf47fad6,0x0⟩,
⟨2050,2,0x2b5800c7,0xf7b540001f47fad6,0x80000000000000000000000000000⟩,
⟨2052,2,0x2b587507,0xf7b543faa007fad6,0x0⟩,
⟨2054,3,0x2b580007,0xf7b540000007fad6,0x80000000000000000000000000000⟩,
⟨2064,2,0x15a60c7,0x7b57b82bf47f056,0x0⟩,
⟨2065,3,0x260c7,0x3b82bf47f056,0x0⟩,
⟨2066,3,0x15800c7,0x7b540001f47f056,0x1c0000000000000000000000000000⟩,
⟨2080,2,0x2a0a7541,0xf0357bfaac40fa82,0x10000000000000000000000000000000⟩,
⟨2081,3,0x27541,0x3bfaac40fa82,0x12800000000000000000000000000000⟩,
⟨2084,3,0x2a087501,0xf03543faa000fa82,0x10000000000000000000000000000000⟩,
⟨2112,2,0x2a527502,0xf3857bfab5033a94,0x0⟩,
⟨2113,3,0x27502,0x3bfab5033a94,0x0⟩,
⟨2116,3,0x2a507502,0xf38543faa0033a94,0x0⟩,
⟨2144,3,0x2a027500,0xf0057bfaa4003a80,0x8010000000000000000000000000000000⟩,
⟨2145,4,0x27500,0x3bfaa4003a80,0x9412800000000000000000000000000000⟩,
⟨2148,4,0x2a007500,0xf00543faa0003a80,0x8010000000000000000000000000000000⟩,
⟨2176,2,0xb502586,0x779169b8bb0752d4,0x0⟩,
⟨2177,3,0x2586,0x29b8bb0752d4,0x0⟩,
⟨2178,3,0xb500086,0x779140001b0752d4,0x20000000000000000000000000000000000⟩,
⟨2180,3,0xb502506,0x779141b8a00752d4,0x0⟩,
⟨2182,4,0xb500006,0x77914000000752d4,0x20000000000000000000000000000000000⟩,
⟨2192,3,0x1502086,0x7916980bb075054,0x0⟩,
⟨2193,4,0x2086,0x2980bb075054,0x0⟩,
⟨2194,4,0x1500086,0x79140001b075054,0x70000000000000000000000000000000000⟩,
⟨2240,3,0xa502502,0x738169b8b1031294,0x0⟩,
⟨2241,4,0x2502,0x29b8b1031294,0x0⟩,
⟨2244,4,0xa502502,0x738141b8a0031294,0x0⟩,
⟨2304,2,0x231a71c7,0xb5b473da3e47f8c6,0x0⟩,
⟨2305,3,0x271c7,0x33da3e47f8c6,0x0⟩,
⟨2306,3,0x231800c7,0xb5b440001e47f8c6,0x0⟩,
⟨2308,3,0x23187107,0xb5b443da2007f8c6,0x0⟩,
⟨2310,4,0x23180007,0xb5b440000007f8c6,0x0⟩,
⟨2320,3,0x11a60c7,0x5b473823e47f046,0x0⟩,
⟨2321,4,0x260c7,0x33823e47f046,0x0⟩,
⟨2322,4,0x11800c7,0x5b440001e47f046,0x0⟩,
⟨2336,3,0x220a7141,0xb03473da2c40f882,0x0⟩,
⟨2337,4,0x27141,0x33da2c40f882,0x0⟩,
⟨2340,4,0x22087101,0xb03443da2000f882,0x0⟩]
private def T2f : Array TriFeature := #[⟨2240,0x1ffc0001fffffffff8000003ff⟩,
⟨1216,0x7ff00007fe0000000007ffffff8000003ff⟩,
⟨1568,0xffffe38fe000000000000003fffff83c3f⟩,
⟨2336,0x3ffff8e3f800fe007fff83c3f⟩,
⟨800,0xffe38fe003ff8e3f80000007fff83c3f⟩,
⟨2144,0x3fc7f803f9f8fe3f83ff8003f⟩,
⟨1120,0xff1fe00fe0000000001f8fe3f83ff8003f⟩,
⟨1552,0x71fe3fff1e00000000000001c7fc7ffffcf⟩,
⟨2320,0x1c7f8fffc78071e007c7ffffcf⟩,
⟨784,0xe3fff1e0038fffc780000007c7ffffcf⟩,
⟨2192,0x1c7c007fc7e3f1fc780007ffcf⟩,
⟨1168,0x71f001ff1e00000000063f1fc780007ffcf⟩,
⟨1544,0x7ffffffffe00000000000001ff9f879ccf1⟩,
⟨1160,0x7ff001fffe0000000007fbe7ff80001ccf1⟩,
⟨1096,0x7ff1fe07fe0000000007fbe7ff8387800f1⟩,
⟨200,0x7ff00007fef9c0000f9ffbe7ff8000000f1⟩,
⟨1064,0xffffe38fe0000000001f8e63f9f8780c31⟩,
⟨552,0xffffe38fe001f38639800003f9f8780c31⟩,
⟨104,0xff1fe00fe39c7380399f8e63f838780031⟩,
⟨2308,0x1fffffffff807fe002f99ad572⟩,
⟨2180,0x1ffc007fffffffef980002d572⟩,
⟨2116,0x1ffc7f81ffffffef9839980172⟩,
⟨196,0x3e700003e7ffc0001ffffffef9800000172⟩,
⟨2084,0x3ffff8e3f9f8fe39af9981432⟩,
⟨292,0x7ce18e63ffff8e3f800fe002f9981432⟩,
⟨100,0xe71ce00e63fc7f803f9f8fe39839980032⟩,
⟨140,0x3e7000dbe6f9c0036f9ffbe6f980000c470⟩,
⟨76,0x3e71ce03e6f9c7380f9ffbe6f9838180070⟩,
⟨44,0xe77ce18e639df386399f8e6398f8180430⟩,
⟨1538,0x76bed7ff6a00000000000001dafdaafffd4⟩,
⟨2306,0x1dafb5ffda8076a007daafffd4⟩,
⟨770,0xed7ff6a003b5ffda80000007daafffd4⟩,
⟨2178,0x1dac007fdaedf6bda80007ffd4⟩,
⟨1154,0x76b001ff6a0000000006df6bda80007ffd4⟩,
⟨2066,0x1c2f85ffc2e1f0bc2fc2afffc4⟩,
⟨1042,0x70be17ff0a00000000061f0bc2fc2afffc4⟩,
⟨530,0x70be17ff0a00385ffc280001c2fc2afffc4⟩,
⟨274,0xe17ff0bc2f85ffc28070a007c2afffc4⟩,
⟨146,0x70b001ff0bc2c007fc2e1f0bc280007ffc4⟩,
⟨1034,0x76bed7ff6a0000000006db63da9d829ccd0⟩,
⟨522,0x76bed7ff6a001b1b6d880001da9d829ccd0⟩,
⟨138,0x76b001ff6ad8c0036d8edb63da80001ccd0⟩,
⟨2054,0x1dafb5ffdaedf6ad8ad88ad550⟩,
⟨262,0x6c6db63dafb5ffda8076a002d88ad550⟩,
⟨134,0x363000db63dac007fdaedf6ad880002d550⟩,
⟨14,0x3636c6db62d8db1b6d8edb62d88d808c450⟩,
⟨1537,0x5bdb7b6dbc000000000000016f76ff77baf⟩,
⟨2305,0x16f6dedb6f005bc0076ff77baf⟩,
⟨769,0xb7b6dbc002dedb6f000000076ff77baf⟩,
⟨2177,0x16f4005b6f36dbd6f000077baf⟩,
⟨1153,0x5bd0016dbc00000000036dbd6f000077baf⟩,
⟨2113,0x16f45e816f36dbd6f02ff003af⟩,
⟨1089,0x5bd17a05bc00000000036dbd6f02ff003af⟩,
⟨193,0x5bd00005bd6f400016f36dbd6f0000003af⟩,
⟨2081,0x2f6de8a2f168bc2f76ff0382f⟩,
⟨1057,0xbdb7a28bc000000000168bc2f76ff0382f⟩,
⟨545,0xbdb7a28bc002de8a2f000002f76ff0382f⟩,
⟨289,0xb7a28bc2f6de8a2f000bc0076ff0382f⟩,
⟨97,0xbd17a00bc2f45e802f168bc2f02ff0002f⟩,
⟨2065,0x14768edb4722d1d47747f77b8f⟩,
⟨1041,0x51da3b6d1c00000000022d1d47747f77b8f⟩,
⟨529,0x51da3b6d1c0028edb470000147747f77b8f⟩,
⟨273,0xa3b6d1d4768edb470051c00747f77b8f⟩,
⟨145,0x51d0016d1d474005b4722d1d47000077b8f⟩]
private def T2c : Array Nat := #[0x0,0x0,0x1002092e00400824b8092e4b848b85df7,0x12f25e7ffe4bc979fffa7fffffbfbfbffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffffff]
private abbrev T2b : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private def T2q : List Nat := [1224,1576,1128,2244,2340,2148,204,108,1554,2322,786,2194,1170,1546,1162,2310,2182,142,2241,1217,1569,2337,801,2145,1121,1553,2321,785,2193,1169]
private def T2k : List (List Nat) := [[14,129,801],[14,193,769],[14,257,1217],[14,289,1153],[14,513,2241],[14,545,2177],[97,1026,2310],[97,1034,2306],[97,1538,2054],[97,1546,2050],[129,142,800],[132,800,1169],[134,289,1153],[134,800,1153],[136,800,2193],[138,545,2177],[138,800,2177],[140,145,800],[146,1056,2340],[146,1064,2336],[146,1568,2084],[146,1576,2080],[1026,1121,2308],[1042,1120,2308],[1056,1170,2308],[1057,1154,2308],[1544,2050,2145],[1544,2066,2144],[1544,2080,2194],[1544,2081,2178]]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T2checked : trioTest T2a T2f T2c 9 (fun x y z=>decide ([x,y,z]∈T2k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T2valid : trioValidated T2b T2a T2q T2f T2c 9=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T2close : T2k.all (fun cs=>decide (norm2 (attach cs T2b)∈atlas))=true := by decide +kernel
private theorem B3_2ok {cs : List Nat} (ex : Extension 6 3 T2b cs) (he : edges_ (attach cs T2b)≤33) : norm2 (attach cs T2b)∈atlas :=
  triExtension norm2 atlas T2b T2a T2q T2f T2c 9 T2k (by decide +kernel) T2valid T2checked T2close ex he
private def T3a : List TrioAtom := [⟨6,2,0x3ffc007,0xffffc000007ffff,0x2000292924a40000000000008000⟩,
⟨10,2,0x3ffc038,0xffffc0003f80fff,0x121002080200020810008002000008040⟩,
⟨12,2,0x3ffc700,0xffffc0fe0000fff,0x121080010080800202001000401000010⟩,
⟨14,3,0x3ffc000,0xffffc0000000fff,0x121492490a92924a5210900a429088450⟩,
⟨17,2,0x38ff,0x3f0fffff07f,0x4000000000000040600000052200⟩,
⟨18,2,0x1fc0ff,0x7ffc001ffff07f,0x700020007080000000000007c000⟩,
⟨33,2,0x3f01,0x3ffec38ff83,0x120000000000000000500002500000⟩,
⟨36,2,0x3e0c701,0xf83fc3fe000ff83,0x1c0000080c00200000000003800000⟩,
⟨40,2,0x3e0df00,0xf83fdcfe0380f83,0x121100000000000002000000402000000⟩,
⟨44,3,0x3e0c700,0xf83fc0fe0000f83,0x1211c0010080c00202001000403800000⟩,
⟨65,2,0x3f5a,0x3fff5db3f9c,0x200000000000000007a00440000000000⟩,
⟨68,2,0x3e70702,0xfbc7c3fe0033f9c,0x100000000080800207001000000000000⟩,
⟨72,2,0x3e71f18,0xfbc7dcfe1d80f9c,0x121000000000000007000000400000000⟩,
⟨76,3,0x3e70700,0xfbc7c0fe0000f9c,0x121080010080800207001000401000000⟩,
⟨96,2,0x3e03f00,0xf807fffe4183f80,0x40100020000000007002000802000000⟩,
⟨97,3,0x3f00,0x3ffe4183f80,0x24e120025000000007a02550942500000⟩,
⟨100,3,0x3e00700,0xf807c3fe0003f80,0x1711c00380c0c00307003800e03800000⟩,
⟨104,3,0x3e01f00,0xf807dcfe0180f80,0x171100020000000007002000e02000000⟩,
⟨108,4,0x3e00700,0xf807c0fe0000f80,0x1711c00380c0c00307003800e03800000⟩,
⟨129,2,0x3bfe,0x3d77fff53fc,0x200000000000000038000404000000000⟩,
⟨130,2,0xff00fe,0x7fd9c001fff53fc,0x100002080200020838008002000000000⟩,
⟨136,2,0xff1b38,0x7fd9dc763f803fc,0x121000000000000038000002000000000⟩,
⟨138,3,0xff0038,0x7fd9c0003f803fc,0x121002080200020838008002000000000⟩,
⟨144,2,0x1f38fe,0x7d9fd07fff507c,0x200004100000000038050004000000000⟩,
⟨145,3,0x38fe,0x3d07fff507c,0x200004100000000038050604000000000⟩,
⟨146,3,0x1f00fe,0x7d9c001fff507c,0x3800071c0700071c3807c007000000000⟩,
⟨192,2,0xe73b5a,0x7bc1fd775db139c,0x3ff80000000000000⟩,
⟨193,3,0x3b5a,0x3d775db139c,0x20000000000000003ff80444000000000⟩,
⟨200,3,0xe71b18,0x7bc1dc761d8039c,0x12100000000000003ff80002420000000⟩,
⟨257,2,0x24e7,0x2fb9ee7fce7,0x4000004000000000400000000000⟩,
⟨258,2,0x339c0e7,0xbdfe4001ee7fce7,0x2000204020800000000000000000⟩,
⟨260,2,0x339c407,0xbdfe43b8007fce7,0x2000087900200000000000000000⟩,
⟨262,3,0x339c007,0xbdfe4000007fce7,0x2000297924a40000000000000000⟩,
⟨272,2,0x19e0e7,0x5fe6f09ee7f067,0x4000204048000000000000000000⟩,
⟨273,3,0x20e7,0x2f09ee7f067,0x4000704049000060600000000000⟩,
⟨274,3,0x19c0e7,0x5fe4001ee7f067,0x7000204078800000000000000000⟩,
⟨288,2,0x320e401,0xb83e6fb8c20fc83,0x100000084200000000000000000000⟩,
⟨289,3,0x2401,0x2fb8c20fc83,0x1248000c4200000000500000000000⟩,
⟨292,3,0x320c401,0xb83e43b8000fc83,0x5d2400087f80200000000000000000⟩,
⟨513,2,0xdad,0x36dbb6ded6b,0x607e00000000000000400000000000⟩,
⟨514,2,0x35ac0ad,0xdefe8001b6ded6b,0x602400200020800000000000000000⟩,
⟨516,2,0x35ac505,0xdefe82da005ed6b,0x602400080800200000000000000000⟩,
⟨518,3,0x35ac005,0xdefe8000005ed6b,0x602400292924a40000000000000000⟩,
⟨520,2,0x35acd28,0xdefe94da3680d6b,0x121692490800000000000000000000000⟩,
⟨522,3,0x35ac028,0xdefe80003680d6b,0x121692490a00020810008000000000000⟩,
⟨524,3,0x35ac500,0xdefe80da0000d6b,0x121692490880800202001000000000000⟩,
⟨526,4,0x35ac000,0xdefe80000000d6b,0x121692490a92924a52109000000000000⟩,
⟨528,2,0x1ac8ad,0x6feb60bb6de06b,0x607e00000000000000000000000000⟩,
⟨529,3,0x8ad,0x360bb6de06b,0x607e00000000000040000000000000⟩,
⟨530,3,0x1ac0ad,0x6fe8001b6de06b,0x607e00200070800000000000000000⟩,
⟨544,2,0x340cd01,0xd83eb6da828ed03,0x7fa400000000000000000000000000⟩,
⟨545,3,0xd01,0x36da828ed03,0x7ffe00000000000000000000000000⟩,
⟨548,3,0x340c501,0xd83e82da000ed03,0x7fa400080c00200000000000000000⟩,
⟨552,3,0x340cd00,0xd83e94da0280d03,0x1217fa490800000002000000000000000⟩,
⟨556,4,0x340c500,0xd83e80da0000d03,0x1217fa490880c00202000000000000000⟩,
⟨768,2,0x318c4a5,0x9cfe2699a65ec63,0x602400007000000000000000000000⟩,
⟨769,3,0x4a5,0x2699a65ec63,0x607e00007000000000000000000000⟩,
⟨770,3,0x318c0a5,0x9cfe0001a65ec63,0x602400207024800000000000000000⟩,
⟨772,3,0x318c405,0x9cfe0298005ec63,0x602400087900200000000000000000⟩,
⟨774,4,0x318c005,0x9cfe0000005ec63,0x602400297924a40000000000000000⟩,
⟨784,3,0x18c0a5,0x4fe2609a65e063,0x607e0020707e800000000000000000⟩,
⟨785,4,0xa5,0x2609a65e063,0x607e0070707fc00000000000000000⟩,
⟨786,4,0x18c0a5,0x4fe0001a65e063,0x607e0020707e800000000000000000⟩,
⟨800,3,0x300c401,0x983e2698820ec03,0x7fa400087f80200000000000000000⟩,
⟨801,4,0x401,0x2698820ec03,0x7ffe000c7f80300000000000000000⟩,
⟨804,4,0x300c401,0x983e0298000ec03,0x7fa400087f80200000000000000000⟩,
⟨1025,2,0x3ff8,0x3fffffe8739,0x20c000004000000000000000000000000⟩,
⟨1032,2,0x1ce5f38,0xef6b9cfe3f80739,0x3ff800000000000000000000000000000⟩,
⟨1040,2,0xe78f8,0x76bbf0fffe8039,0x20c004100000000000000000000000000⟩,
⟨1041,3,0x38f8,0x3f0fffe8039,0x20c004906000000000000000000000000⟩,
⟨1056,2,0x1c07f00,0xe82bbffec388701,0x24e100020000000000000000000000000⟩,
⟨1057,3,0x3f00,0x3ffec388701,0x24e120025000000000000000000000000⟩,
⟨1064,3,0x1c05f00,0xe82b9cfe0380701,0x3ff900020000000000000000000000000⟩,
⟨1088,2,0x1c63f58,0xeb43bfff5da0718,0x20c000000000000000000000000000000⟩,
⟨1089,3,0x3f58,0x3fff5da0718,0x20c000004000000000000000000000000⟩,
⟨1096,3,0x1c61f18,0xeb439cfe1d80718,0x3ff800000000000000000000000000000⟩,
⟨1120,3,0x1c03f00,0xe803bffe4180700,0x24e100020000000000000000000000000⟩,
⟨1121,4,0x3f00,0x3ffe4180700,0x24e120025000000000000000000000000⟩,
⟨1128,4,0x1c01f00,0xe8039cfe0180700,0x3ff900020000000000000000000000000⟩,
⟨1152,2,0xce3bf8,0x6f49bd77ffe0338,0x20c000000000000000000000000000000⟩,
⟨1153,3,0x3bf8,0x3d77ffe0338,0x20c000004000000000000000000000000⟩,
⟨1160,3,0xce1b38,0x6f499c763f80338,0x3ff800000000000000000000000000000⟩,
⟨1168,3,0xe38f8,0x749bd07ffe0038,0x20c004100000000000000000000000000⟩,
⟨1169,4,0x38f8,0x3d07ffe0038,0x20c004906000000000000000000000000⟩,
⟨1216,3,0xc63b58,0x6b41bd775da0318,0x20c000000000000000000000000000000⟩,
⟨1217,4,0x3b58,0x3d775da0318,0x20c000004000000000000000000000000⟩,
⟨1224,4,0xc61b18,0x6b419c761d80318,0x3ff800000000000000000000000000000⟩,
⟨1536,2,0x14a4da8,0xce6ab6dbb6c8529,0x38c607fc6000000000000000000000000⟩,
⟨1537,3,0xda8,0x36dbb6c8529,0x38c607fc6000000000000000000000000⟩,
⟨1544,3,0x14a4d28,0xce6a94da3680529,0x3ffffffff800000000000000000000000⟩,
⟨1552,3,0xa48a8,0x66ab60bb6c8029,0x38c607fc6000000000000000000000000⟩,
⟨1553,4,0x8a8,0x360bb6c8029,0x38c607fc6000000000000000000000000⟩,
⟨1568,3,0x1404d00,0xc82ab6da8288501,0x3ffffffff800000000000000000000000⟩,
⟨1569,4,0xd00,0x36da8288501,0x3ffffffff800000000000000000000000⟩,
⟨1576,4,0x1404d00,0xc82a94da0280501,0x3ffffffff800000000000000000000000⟩,
⟨2049,2,0x32d7,0x3be5f97fad6,0x0⟩,
⟨2050,2,0x2b580d7,0xf7b54001f97fad6,0x2000000000000000000000000000⟩,
⟨2052,2,0x2b58207,0xf7b543e4007fad6,0x0⟩,
⟨2054,3,0x2b58007,0xf7b54000007fad6,0x2000000000000000000000000000⟩,
⟨2064,2,0x15b0d7,0x7b57b05f97f056,0x4000000000000000000000000000⟩,
⟨2065,3,0x30d7,0x3b05f97f056,0x4000000000000000000000000000⟩,
⟨2066,3,0x1580d7,0x7b54001f97f056,0x7000000000000000000000000000⟩,
⟨2080,2,0x2a0b201,0xf0357be4c10fa82,0x100000000000000000000000000000⟩,
⟨2081,3,0x3201,0x3be4c10fa82,0x120000000000000000000000000000⟩,
⟨2084,3,0x2a08201,0xf03543e4000fa82,0x1c0000000000000000000000000000⟩,
⟨2112,2,0x2a53252,0xf3857be55933a94,0x0⟩,
⟨2113,3,0x3252,0x3be55933a94,0x200000000000000000000000000000000⟩,
⟨2116,3,0x2a50202,0xf38543e40033a94,0x100000000000000000000000000000000⟩,
⟨2144,3,0x2a03200,0xf0057be44103a80,0x40100000000000000000000000000000⟩,
⟨2145,4,0x3200,0x3be44103a80,0x24e120000000000000000000000000000⟩,
⟨2148,4,0x2a00200,0xf00543e40003a80,0x1711c0000000000000000000000000000⟩,
⟨2176,2,0xb532d6,0x77917965f9752d4,0x0⟩,
⟨2177,3,0x32d6,0x3965f9752d4,0x200000000000000000000000000000000⟩,
⟨2178,3,0xb500d6,0x77914001f9752d4,0x100000000000000000000000000000000⟩,
⟨2192,3,0x1530d6,0x7917905f975054,0x200000000000000000000000000000000⟩,
⟨2193,4,0x30d6,0x3905f975054,0x200000000000000000000000000000000⟩,
⟨2194,4,0x1500d6,0x7914001f975054,0x380000000000000000000000000000000⟩,
⟨2240,3,0xa53252,0x738179655931294,0x0⟩,
⟨2241,4,0x3252,0x39655931294,0x200000000000000000000000000000000⟩,
⟨2304,2,0x231a0c7,0xb5b46ba1e87f8c6,0x0⟩,
⟨2305,3,0x20c7,0x2ba1e87f8c6,0x0⟩,
⟨2306,3,0x23180c7,0xb5b44001e87f8c6,0x0⟩,
⟨2308,3,0x2318007,0xb5b443a0007f8c6,0x0⟩,
⟨2310,4,0x2318007,0xb5b44000007f8c6,0x0⟩,
⟨2320,3,0x11a0c7,0x5b46b01e87f046,0x0⟩,
⟨2321,4,0x20c7,0x2b01e87f046,0x0⟩,
⟨2322,4,0x1180c7,0x5b44001e87f046,0x0⟩,
⟨2336,3,0x220a001,0xb0346ba0c00f882,0x0⟩,
⟨2337,4,0x2001,0x2ba0c00f882,0x0⟩,
⟨2340,4,0x2208001,0xb03443a0000f882,0x0⟩]
private def T3f : Array TriFeature := #[⟨2240,0x7f8001ffffffffffe00003ff⟩,
⟨1216,0x3ff8001ff80000003ffffffffe00003ff⟩,
⟨1568,0x7fff8e3f800000000000000ffff83c3f⟩,
⟨2336,0xfff8e3c0003ff801ff83c3f⟩,
⟨800,0x7f8e3f807f8e3c000000001ff83c3f⟩,
⟨2144,0xf8f803c7f83ff8fe3f8003f⟩,
⟨1120,0x7f9f803f800000007f83ff8fe3f8003f⟩,
⟨1552,0x38fe3ffc78000000000000071fc7fffcf⟩,
⟨2320,0x73f3ffcc007c7f801c7fffcf⟩,
⟨784,0x63ffc78073ffcc000000001c7fffcf⟩,
⟨2192,0x73807fcf8ffc7ff1e007ffcf⟩,
⟨1168,0x38f807fc7800000038ffc7ff1e007ffcf⟩,
⟨1544,0x3ffffffff800000000000007fef99ccf1⟩,
⟨1160,0x3ff807fff80000003ff9f87ffe001ccf1⟩,
⟨1096,0x3ff9f81ff80000003ff9f87ffe39800f1⟩,
⟨200,0x3ff8001ffbd8000f7ff9f87ffe00000f1⟩,
⟨1064,0x7fff8e3f800000007f83878fef980c31⟩,
⟨552,0x7fff8e3f803d86340000000fef980c31⟩,
⟨104,0x7f9f803f8d8d80347f83878fe3980031⟩,
⟨2308,0x7ffffffc002f99801ffad572⟩,
⟨772,0x7fb6f9807ffffc000000001ffad572⟩,
⟨2116,0x7f8f81fdf3af99be63f80172⟩,
⟨2084,0xfff8e3c7383998e7ff81432⟩,
⟨548,0x73ff8639807f8e3c0000000e7ff81432⟩,
⟨292,0x7f86398fff8e3c000399801ff81432⟩,
⟨100,0x739f80398f8f803c7383998e63f80032⟩,
⟨524,0x1f3ffb6f9803db6f40000003e6f98c470⟩,
⟨76,0x1f39f80f9bd8d80f5f38f81be63980070⟩,
⟨44,0x73ff86398dbd86347383818e6f980430⟩,
⟨2306,0x7ffffffc007daa801dafffd4⟩,
⟨770,0x6dffda807ffffc000000001dafffd4⟩,
⟨2178,0x7f807fffb5fdaaf6a007ffd4⟩,
⟨2066,0x73f3ffcf85fc2af0bc2fffc4⟩,
⟨530,0x385e1ffc28073ffcc00000070bc2fffc4⟩,
⟨274,0x61ffc2f3f3ffcc007c2a801c2fffc4⟩,
⟨146,0x385807fc2f3807fcf85fc2af0a007ffc4⟩,
⟨522,0x3b5edffda803db6f400000076ad89ccd0⟩,
⟨138,0x3b5807fdabd8036f7b59d82f6a001ccd0⟩,
⟨2054,0x7ffffffdb1ad88b63daad550⟩,
⟨518,0x1b1edb6d8807ffffc000000363daad550⟩,
⟨262,0x6db6d8fffffffc002d88801daad550⟩,
⟨14,0x1b1edb6d8bdbdb6f5b18d80b62d88c450⟩,
⟨1537,0x2deb6db6f000000000000005bd6f77baf⟩,
⟨2305,0x56d6db580076ff0016f77baf⟩,
⟨769,0x36db6f0056db580000000016f77baf⟩,
⟨2177,0x56805b5adef6ff5bc0077baf⟩,
⟨1153,0x2de805b6f00000002def6ff5bc0077baf⟩,
⟨2113,0x5686815adef6ff5bc2f003af⟩,
⟨1089,0x2de96816f00000002def6ff5bc2f003af⟩,
⟨193,0x2de80016f5680015adef6ff5bc00003af⟩,
⟨2081,0x6d68a185e82ff0bd6f0382f⟩,
⟨1057,0x5eb68a2f000000005e82ff0bd6f0382f⟩,
⟨545,0x5eb68a2f00568a180000000bd6f0382f⟩,
⟨289,0x368a2f06d68a180002ff0016f0382f⟩,
⟨97,0x5e96802f068680185e82ff0bc2f0002f⟩,
⟨2065,0x52d2db4a8ef47f51d4777b8f⟩,
⟨1041,0x28ea2db47000000028ef47f51d4777b8f⟩,
⟨529,0x28ea2db470052db4800000051d4777b8f⟩,
⟨273,0x22db4752d2db4800747f0014777b8f⟩,
⟨145,0x28e805b4752805b4a8ef47f51c0077b8f⟩]
private def T3c : Array Nat := #[0x0,0x0,0x80824b8080825c00848b92e4b85df7,0x97a79fff97979ffc97bfbffffffbffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff]
private abbrev T3b : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
private def T3q : List Nat := [1224,1576,1128,2340,804,2148,556,108,2322,786,2194,2310,774,526,2241,1217,1569,2337,801,2145,1121,1553,2321,785,2193,1169]
private def T3k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T3checked : trioTest T3a T3f T3c 8 (fun x y z=>decide ([x,y,z]∈T3k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T3valid : trioValidated T3b T3a T3q T3f T3c 8=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T3close : T3k.all (fun cs=>decide (norm2 (attach cs T3b)∈atlas))=true := by decide +kernel
private theorem B3_3ok {cs : List Nat} (ex : Extension 6 3 T3b cs) (he : edges_ (attach cs T3b)≤33) : norm2 (attach cs T3b)∈atlas :=
  triExtension norm2 atlas T3b T3a T3q T3f T3c 8 T3k (by decide +kernel) T3valid T3checked T3close ex he
private def T4a : List TrioAtom := [⟨6,2,0x7ff8007,0xffffc000007ffff,0x2000008200a4020810020020000008040⟩,
⟨10,2,0x7ff8038,0xffffc0003f80fff,0x242484924200020000000000000008000⟩,
⟨12,2,0x7ff8700,0xffffc0fe0000fff,0x242080004020400202004004001000010⟩,
⟨14,3,0x7ff8000,0xffffc0000000fff,0x2424849242a5524a52124224029088450⟩,
⟨17,2,0x78ff,0x3f0fffff07f,0x700000000000000000000141800042200⟩,
⟨18,2,0x3f80ff,0x7ffc001ffff07f,0x200001c2000007000000000000007c000⟩,
⟨33,2,0x7f08,0x3ffec787f83,0x7ff128009400000000000001102500000⟩,
⟨36,2,0x7c18f00,0xf83fc3fe0007f83,0x242100000020000002004004002000000⟩,
⟨40,2,0x7c1b708,0xf83fdcfe0780f83,0x2421c0004000000000000000002000000⟩,
⟨44,3,0x7c18700,0xf83fc0fe0000f83,0x2421c0004020600202004004003800000⟩,
⟨65,2,0x7f53,0x3fff59bbf9c,0x700000000000000004a00001400000000⟩,
⟨68,2,0x7ce0f03,0xfbc7c3fe003bf9c,0x200000000020000007004000000000000⟩,
⟨72,2,0x7ce3710,0xfbc7dcfe1980f9c,0x242080004000000004000000000000000⟩,
⟨76,3,0x7ce0700,0xfbc7c0fe0000f9c,0x242080004020400207004004001000000⟩,
⟨96,2,0x7c07f00,0xf807fffe4183f80,0x2e2100008000000004008008002000000⟩,
⟨97,3,0x7f00,0x3ffe4183f80,0x7ff128009400000004a09409542500000⟩,
⟨100,3,0x7c00f00,0xf807c3fe0003f80,0x2e210000803000000700e00e002000000⟩,
⟨104,3,0x7c03700,0xf807dcfe0180f80,0x2e21c000e000000004008008002000000⟩,
⟨108,4,0x7c00700,0xf807c0fe0000f80,0x2e21c000e03060030700e00e003800000⟩,
⟨129,2,0x5bf7,0x2f77faff3fc,0x7000000000000000380001f1800000000⟩,
⟨130,2,0x1fe00f7,0x7fd9c001faff3fc,0x200000820080020838020020000000000⟩,
⟨132,2,0x1fe0b07,0x7fd9c376007f3fc,0x200000000020000038000020000000000⟩,
⟨134,3,0x1fe0007,0x7fd9c000007f3fc,0x2000008200a4020838020020000000000⟩,
⟨144,2,0x3e58f7,0x7d9ef07faff07c,0x7000000000000000380001f0000000000⟩,
⟨145,3,0x58f7,0x2f07faff07c,0x7000000000000000380001f1800000000⟩,
⟨146,3,0x3e00f7,0x7d9c001faff07c,0x700001c701c0071c380701f0000000000⟩,
⟨192,2,0x1ce5b53,0x7bc1ef7758bb39c,0x20000000000000003ff80020000000000⟩,
⟨193,3,0x5b53,0x2f7758bb39c,0x70000000000000003ff801f1e00000000⟩,
⟨196,3,0x1ce0b03,0x7bc1c376003b39c,0x20000000002000003ff84020000000000⟩,
⟨257,2,0x24ad,0x35b9af5dce7,0x700001c70001800000000001000000000⟩,
⟨258,2,0x67380ad,0xbdfe4001af5dce7,0x200000820001824000000000000000000⟩,
⟨260,2,0x6738405,0xbdfe41b8005dce7,0x200000820021d00200000000000000000⟩,
⟨262,3,0x6738005,0xbdfe4000005dce7,0x2000008200a5d24a50020020000000000⟩,
⟨264,2,0x673a428,0xbdfe54b82f00ce7,0x242484924201800000000000000000000⟩,
⟨266,3,0x6738028,0xbdfe40002f00ce7,0x242484924201824000000000000000000⟩,
⟨268,3,0x6738400,0xbdfe40b80000ce7,0x242484924221d00202004004000000000⟩,
⟨270,4,0x6738000,0xbdfe40000000ce7,0x2424849242a5d24a52124224000000000⟩,
⟨272,2,0x33a0ad,0x5fe7509af5d067,0x200001c20001800000000000000000000⟩,
⟨273,3,0x20ad,0x3509af5d067,0x700001c70001800000000140000000000⟩,
⟨274,3,0x3380ad,0x5fe4001af5d067,0x200001c2000187e000000000000000000⟩,
⟨288,2,0x641a408,0xb83e75b88705c83,0x2425c4924201f80000000000000000000⟩,
⟨289,3,0x2408,0x35b88705c83,0x7ffffffffe01f80000000000000000000⟩,
⟨292,3,0x6418400,0xb83e41b80005c83,0x2425c4924221f80202004000000000000⟩,
⟨296,3,0x641a408,0xb83e54b80700c83,0x2425c4924201f80000000000000000000⟩,
⟨300,4,0x6418400,0xb83e40b80000c83,0x2425c4924221f80202004000000000000⟩,
⟨513,2,0x75fc,0x3edbffecd6b,0x700801240000000000000000000000000⟩,
⟨514,2,0x6b580fc,0xdefe8001ffecd6b,0x200800820000020000000000000000000⟩,
⟨520,2,0x6b5b538,0xdefe9cda3f80d6b,0x242e84924200000000000000000000000⟩,
⟨522,3,0x6b58038,0xdefe80003f80d6b,0x242e84924200020000000000000000000⟩,
⟨528,2,0x35f0fc,0x6febe0bffec06b,0x200801200000000000000000000000000⟩,
⟨529,3,0x70fc,0x3e0bffec06b,0x700801240000000000000000000000000⟩,
⟨530,3,0x3580fc,0x6fe8001ffec06b,0x200801e20000070000000000000000000⟩,
⟨544,2,0x681f508,0xd83ebedac784d03,0x242938000000000000000000000000000⟩,
⟨545,3,0x7508,0x3edac784d03,0x7ff939249c00000000000000000000000⟩,
⟨552,3,0x681b508,0xd83e9cda0780d03,0x242ffe924200000000000000000000000⟩,
⟨768,2,0x631a4ac,0x9cfe3499af4cc63,0x200e00920001800000000000000000000⟩,
⟨769,3,0x24ac,0x3499af4cc63,0x700e01ff0001800000000000000000000⟩,
⟨770,3,0x63180ac,0x9cfe0001af4cc63,0x200e00920001824000000000000000000⟩,
⟨776,3,0x631a428,0x9cfe14982f00c63,0x242e84924201800000000000000000000⟩,
⟨778,4,0x6318028,0x9cfe00002f00c63,0x242e84924201824000000000000000000⟩,
⟨784,3,0x31a0ac,0x4fe3409af4c063,0x200e01fa0001800000000000000000000⟩,
⟨785,4,0x20ac,0x3409af4c063,0x700e01ff0001800000000000000000000⟩,
⟨786,4,0x3180ac,0x4fe0001af4c063,0x200e01fa000187e000000000000000000⟩,
⟨800,3,0x601a408,0x983e34988704c03,0x242ffe924201f80000000000000000000⟩,
⟨801,4,0x2408,0x34988704c03,0x7ffffffffe01f80000000000000000000⟩,
⟨808,4,0x601a408,0x983e14980700c03,0x242ffe924201f80000000000000000000⟩,
⟨1025,2,0x7ffa,0x3ffffff2739,0x718000000000000000000000000000000⟩,
⟨1032,2,0x39cb738,0xef6b9cfe3f80739,0x7ff080004000000000000000000000000⟩,
⟨1040,2,0x1cf8fa,0x76bbf0ffff2039,0x718000000000000000000000000000000⟩,
⟨1041,3,0x78fa,0x3f0ffff2039,0x718000000000000000000000000000000⟩,
⟨1056,2,0x380ff08,0xe82bbffec782701,0x7ff100008000000000000000000000000⟩,
⟨1057,3,0x7f08,0x3ffec782701,0x7ff128009400000000000000000000000⟩,
⟨1064,3,0x380b708,0xe82b9cfe0780701,0x7ff1c000e000000000000000000000000⟩,
⟨1088,2,0x38c7f52,0xeb43bfff59b2718,0x7ff000000000000000000000000000000⟩,
⟨1089,3,0x7f52,0x3fff59b2718,0x7ff000000000000000000000000000000⟩,
⟨1096,3,0x38c3710,0xeb439cfe1980718,0x7ff080004000000000000000000000000⟩,
⟨1120,3,0x3807f00,0xe803bffe4182700,0x7ff100008000000000000000000000000⟩,
⟨1121,4,0x7f00,0x3ffe4182700,0x7ff128009400000000000000000000000⟩,
⟨1128,4,0x3803700,0xe8039cfe0180700,0x7ff1c000e000000000000000000000000⟩,
⟨1152,2,0x19c5bf2,0x6f49af77faf2338,0x718000000000000000000000000000000⟩,
⟨1153,3,0x5bf2,0x2f77faf2338,0x718000000000000000000000000000000⟩,
⟨1168,3,0x1c58f2,0x749af07faf2038,0x718000000000000000000000000000000⟩,
⟨1169,4,0x58f2,0x2f07faf2038,0x718000000000000000000000000000000⟩,
⟨1216,3,0x18c5b52,0x6b41af7758b2318,0x7ff000000000000000000000000000000⟩,
⟨1217,4,0x5b52,0x2f7758b2318,0x7ff000000000000000000000000000000⟩,
⟨1536,2,0x294f5f8,0xce6abedbffe0529,0x718831241800000000000000000000000⟩,
⟨1537,3,0x75f8,0x3edbffe0529,0x718831241800000000000000000000000⟩,
⟨1544,3,0x294b538,0xce6a9cda3f80529,0x7ffffffffe00000000000000000000000⟩,
⟨1552,3,0x14f0f8,0x66abe0bffe0029,0x718831241800000000000000000000000⟩,
⟨1553,4,0x70f8,0x3e0bffe0029,0x718831241800000000000000000000000⟩,
⟨1568,3,0x280f508,0xc82abedac780501,0x7ff939249c00000000000000000000000⟩,
⟨1569,4,0x7508,0x3edac780501,0x7ff939249c00000000000000000000000⟩,
⟨1576,4,0x280b508,0xc82a9cda0780501,0x7ffffffffe00000000000000000000000⟩,
⟨2049,2,0x4ac7,0x3be5f47fad6,0x700000000000000000000000000000000⟩,
⟨2050,2,0x56b00c7,0xf7b54001f47fad6,0x200000820000000000000000000000000⟩,
⟨2052,2,0x56b0a07,0xf7b543e4007fad6,0x200000000000000000000000000000000⟩,
⟨2054,3,0x56b0007,0xf7b54000007fad6,0x200000820000000000000000000000000⟩,
⟨2064,2,0x2b48c7,0x7b57b05f47f056,0x200000000000000000000000000000000⟩,
⟨2065,3,0x48c7,0x3b05f47f056,0x700000000000000000000000000000000⟩,
⟨2066,3,0x2b00c7,0x7b54001f47f056,0x200001c20000000000000000000000000⟩,
⟨2080,2,0x5414a00,0xf0357be4c407a82,0x242100000000000000000000000000000⟩,
⟨2081,3,0x4a00,0x3be4c407a82,0x7ff128000000000000000000000000000⟩,
⟨2084,3,0x5410a00,0xf03543e40007a82,0x242100000000000000000000000000000⟩,
⟨2112,2,0x54a4a43,0xf3857be5503ba94,0x200000000000000000000000000000000⟩,
⟨2113,3,0x4a43,0x3be5503ba94,0x700000000000000000000000000000000⟩,
⟨2116,3,0x54a0a03,0xf38543e4003ba94,0x200000000000000000000000000000000⟩,
⟨2144,3,0x5404a00,0xf0057be44003a80,0x2e2100000000000000000000000000000⟩,
⟨2145,4,0x4a00,0x3be44003a80,0x7ff128000000000000000000000000000⟩,
⟨2148,4,0x5400a00,0xf00543e40003a80,0x2e2100000000000000000000000000000⟩,
⟨2176,2,0x16a4ac7,0x77916b65f07f2d4,0x200000000000000000000000000000000⟩,
⟨2177,3,0x4ac7,0x2b65f07f2d4,0x700000000000000000000000000000000⟩,
⟨2178,3,0x16a00c7,0x77914001f07f2d4,0x200000000000000000000000000000000⟩,
⟨2180,3,0x16a0a07,0x77914364007f2d4,0x200000000000000000000000000000000⟩,
⟨2182,4,0x16a0007,0x77914000007f2d4,0x200000000000000000000000000000000⟩,
⟨2192,3,0x2a48c7,0x7916b05f07f054,0x700000000000000000000000000000000⟩,
⟨2193,4,0x48c7,0x2b05f07f054,0x700000000000000000000000000000000⟩,
⟨2194,4,0x2a00c7,0x7914001f07f054,0x700000000000000000000000000000000⟩,
⟨2240,3,0x14a4a43,0x73816b65503b294,0x200000000000000000000000000000000⟩,
⟨2241,4,0x4a43,0x2b65503b294,0x700000000000000000000000000000000⟩,
⟨2244,4,0x14a0a03,0x73814364003b294,0x200000000000000000000000000000000⟩,
⟨2304,2,0x4630085,0xb5b471a1a45d8c6,0x200000000000000000000000000000000⟩,
⟨2305,3,0x85,0x31a1a45d8c6,0x700000000000000000000000000000000⟩,
⟨2306,3,0x4630085,0xb5b44001a45d8c6,0x200000000000000000000000000000000⟩,
⟨2308,3,0x4630005,0xb5b441a0005d8c6,0x200000000000000000000000000000000⟩,
⟨2310,4,0x4630005,0xb5b44000005d8c6,0x200000000000000000000000000000000⟩,
⟨2320,3,0x230085,0x5b47101a45d046,0x200000000000000000000000000000000⟩,
⟨2321,4,0x85,0x3101a45d046,0x700000000000000000000000000000000⟩,
⟨2322,4,0x230085,0x5b44001a45d046,0x200000000000000000000000000000000⟩,
⟨2336,3,0x4410000,0xb03471a08405882,0x200000000000000000000000000000000⟩,
⟨2337,4,0x0,0x31a08405882,0x600000000000000000000000000000000⟩,
⟨2340,4,0x4410000,0xb03441a00005882,0x0⟩]
private def T4f : Array TriFeature := #[⟨2240,0x1fe001ffffffffffe00003ff⟩,
⟨1216,0x7ff00007fe0000003ffffffffe00003ff⟩,
⟨1568,0xffffe38fe0000000000000fffff83c3f⟩,
⟨2336,0x3ff8e3c000fe0001ff83c3f⟩,
⟨800,0xffe38fe01f8e3c000000001ff83c3f⟩,
⟨2144,0x3e7803c7f8fe0ffe3f8003f⟩,
⟨1120,0xff1fe00fe00000007f8fe0ffe3f8003f⟩,
⟨1552,0x71fe3fff1e000000000001f1ffc7fffcf⟩,
⟨2320,0x1cf9ffcc0071e0001c7fffcf⟩,
⟨784,0xe3fff1e019ffcc000000001c7fffcf⟩,
⟨2192,0x1ce07fcf8ff1ff1fe007ffcf⟩,
⟨1168,0x71f001ff1e00000038ff1ff1fe007ffcf⟩,
⟨1544,0x7ffffffffe0000000000007e1fff9ccf1⟩,
⟨776,0xffffffe01fb6f4000000001ff9ccf1⟩,
⟨1096,0x7ff1fe07fe0000001f3be67e1e3f800f1⟩,
⟨1064,0xffffe38fe0000000738e60e1fff80c31⟩,
⟨552,0xffffe38fe01f8634000000e1fff80c31⟩,
⟨296,0xffe38fe37f8634000e60001ff80c31⟩,
⟨104,0xff1fe00fe3678034738e60e1e3f80031⟩,
⟨2308,0x1ffffffc007fe0000f9ad572⟩,
⟨2180,0x1fe07fffffffebe66002d572⟩,
⟨2116,0x1fe781ffffffebe663980172⟩,
⟨196,0x3e700003e7fe001ffffffebe660000172⟩,
⟨2084,0x3ff8e3c7f8fe0e66f981432⟩,
⟨292,0x7ce18e63ff8e3c000fe0000f981432⟩,
⟨100,0xe71ce00e63e7803c7f8fe0e663980032⟩,
⟨268,0x7cedbe6f7fb6f4003e60000f98c470⟩,
⟨76,0x3e71ce03e6f6780f5f3be63e063980070⟩,
⟨44,0xe77ce18e637f8634738e60e06f980430⟩,
⟨2306,0x1ffffffc0076a0001dafffd4⟩,
⟨770,0xed7ff6a01ffffc000000001dafffd4⟩,
⟨2178,0x1fe07fffb5f6bf6aa007ffd4⟩,
⟨2066,0x1cf9ffcf85f0bf0abc2fffc4⟩,
⟨530,0x70be17ff0a019ffcc00001f0abc2fffc4⟩,
⟨274,0xe17ff0bcf9ffcc0070a0001c2fffc4⟩,
⟨146,0x70b001ff0bce07fcf85f0bf0aa007ffc4⟩,
⟨522,0x76bed7ff6a01fb6f400000760bda9ccd0⟩,
⟨266,0xed7ff6af7fb6f4003620001da9ccd0⟩,
⟨2054,0x1fffffffb5f6ab622d8ad550⟩,
⟨262,0x6c6db63ffffffc0076a0000d8ad550⟩,
⟨134,0x363000db63fe07fffb5f6ab622002d550⟩,
⟨14,0x3636c6db62f7fb6f5b1b623602d88c450⟩,
⟨1537,0x5bdb7b6dbc000000000001dbfd6f77baf⟩,
⟨2305,0x15aadb58005bc00016f77baf⟩,
⟨769,0xb7b6dbc00adb580000000016f77baf⟩,
⟨2177,0x15a05b5adedbddbfc0077baf⟩,
⟨1153,0x5bd0016dbc0000002dedbddbfc0077baf⟩,
⟨2113,0x15a2815adedbddbfc2f003af⟩,
⟨1089,0x5bd17a05bc0000002dedbddbfc2f003af⟩,
⟨193,0x5bd00005bd5a0015adedbddbfc00003af⟩,
⟨2081,0x1aa8a185e8bc0bfd6f0382f⟩,
⟨1057,0xbdb7a28bc00000005e8bc0bfd6f0382f⟩,
⟨545,0xbdb7a28bc00a8a18000000bfd6f0382f⟩,
⟨289,0xb7a28bc1aa8a18000bc00016f0382f⟩,
⟨97,0xbd17a00bc1a280185e8bc0bfc2f0002f⟩,
⟨2065,0x14a8db4a8ed1dd1fd4777b8f⟩,
⟨1041,0x51da3b6d1c00000028ed1dd1fd4777b8f⟩,
⟨529,0x51da3b6d1c008db4800001d1fd4777b8f⟩,
⟨273,0xa3b6d1d4a8db480051c00014777b8f⟩,
⟨145,0x51d0016d1d4a05b4a8ed1dd1fc0077b8f⟩]
private def T4c : Array Nat := #[0x0,0x0,0x1002092e020825c0092e122e4b85df7,0x12f25e7ffe5eb9ffc97ffefeffffbffff,0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff]
private abbrev T4b : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
private def T4q : List Nat := [1576,808,1128,2244,2340,2148,300,108,2322,786,2194,778,2310,2182,270,2241,1217,1569,2337,801,2145,1121,1553,2321,785,2193,1169]
private def T4k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T4checked : trioTest T4a T4f T4c 8 (fun x y z=>decide ([x,y,z]∈T4k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T4valid : trioValidated T4b T4a T4q T4f T4c 8=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T4close : T4k.all (fun cs=>decide (norm2 (attach cs T4b)∈atlas))=true := by decide +kernel
private theorem B3_4ok {cs : List Nat} (ex : Extension 6 3 T4b cs) (he : edges_ (attach cs T4b)≤33) : norm2 (attach cs T4b)∈atlas :=
  triExtension norm2 atlas T4b T4a T4q T4f T4c 8 T4k (by decide +kernel) T4valid T4checked T4close ex he
private def T5a : List TrioAtom := [⟨6,2,0x3ff0001,0xffff8000000ffff,0x24800240021000000048490a420008400⟩,
⟨10,2,0x3ff000e,0xffff800007f03ff,0x1212080002001000000000008008040⟩,
⟨12,2,0x3ff07c0,0xffff80ffc0003ff,0x40200010200400200080100401000010⟩,
⟨14,3,0x3ff0000,0xffff800000003ff,0x249212490a1242120148490a429088450⟩,
⟨17,2,0xf83f,0x7f07ffffc1f,0x80c0000000000042200⟩,
⟨18,2,0x1f003f,0x7ff80003fffc1f,0x700000000000000000000007c000⟩,
⟨33,2,0xffc1,0x7fffd873fe3,0x900000004a00000a0128250940000000⟩,
⟨36,2,0x3e31fc1,0xf87f87ffc003fe3,0x800000002000000001c0100800000000⟩,
⟨40,2,0x3e367c0,0xf87fb8ffc0703e3,0x80200000000400000100000801000000⟩,
⟨44,3,0x3e307c0,0xf87f80ffc0003e3,0xe02000102004002001c0100e01000000⟩,
⟨65,2,0xffd6,0x7fffebb4fec,0x80004000940088000000000400000⟩,
⟨68,2,0x3ec1fc0,0xfb8f87ffc004fec,0x400000200800000080100002000000⟩,
⟨72,2,0x3ec67c6,0xfb8fb8ffc3b03ec,0x700000000e00000000000003800000⟩,
⟨76,3,0x3ec07c0,0xfb8f80ffc0003ec,0x40700010200e00200080100403800000⟩,
⟨96,2,0x3e0ffc0,0xf80fffffc830fe0,0x80400020400800400100200802000000⟩,
⟨97,3,0xffc0,0x7fffc830fe0,0x904a00254a09404aa128250942500000⟩,
⟨100,3,0x3e01fc0,0xf80f87ffc000fe0,0x804000207008004001c0380802000000⟩,
⟨104,3,0x3e067c0,0xf80fb8ffc0303e0,0x80700020400e00400100200803800000⟩,
⟨108,4,0x3e007c0,0xf80f80ffc0003e0,0xe0700038700e007001c0380e03800000⟩,
⟨129,2,0x99f9,0x5f79fdcfcf3,0x80800000000000000⟩,
⟨130,2,0xf30039,0x7df380003dcfcf3,0x2000000000000800000000000000⟩,
⟨132,2,0xf319c1,0x7df38779c00fcf3,0x80000000200000000e84100000000000⟩,
⟨134,3,0xf30001,0x7df38000000fcf3,0x2e8002400210000000e8490a420000000⟩,
⟨144,2,0x139839,0x5f3df01fdcfc13,0x801004000000000⟩,
⟨145,3,0x9839,0x5f01fdcfc13,0xc0c0801004000000000⟩,
⟨146,3,0x130039,0x5f380003dcfc13,0x7800000000000801004000000000⟩,
⟨160,2,0xe399c1,0x7873df79d843ce3,0x80000000200000000938000800000000⟩,
⟨161,3,0x99c1,0x5f79d843ce3,0x900000007a00000a0938250940000000⟩,
⟨164,3,0xe319c1,0x78738779c003ce3,0x80000000200000000ffe100800000000⟩,
⟨257,2,0xee7e,0x7bbe7ffd73c,0x80004007180088000000000000000⟩,
⟨258,2,0x33c003e,0xbfbc80003ffd73c,0x1002080007001000000000000000000⟩,
⟨264,2,0x33c664e,0xbfbcb8be47f033c,0x700000007000000000000000000000⟩,
⟨266,3,0x33c000e,0xbfbc800007f033c,0x1712080007001000000000000000000⟩,
⟨272,2,0x1ce83e,0x7bcfb067ffd41c,0x8000000700a000000000000000000⟩,
⟨273,3,0xe83e,0x7b067ffd41c,0x8000400718a0cc000000000000000⟩,
⟨274,3,0x1c003e,0x7bc80003ffd41c,0x38c71c000700f800000000000000000⟩,
⟨320,2,0x32cee56,0xbb8cfbbe6bb472c,0x7ff0000000000000000000⟩,
⟨321,3,0xee56,0x7bbe6bb472c,0x80004007ff0088000000000000000⟩,
⟨328,3,0x32c6646,0xbb8cb8be43b032c,0x700000007ff0000000000000000000⟩,
⟨513,2,0xe6be,0x7ddebffe35d,0x20c0004000100088000000000000000⟩,
⟨514,2,0x35d003e,0xdfdd00003ffe35d,0x38c2080002001000000000000000000⟩,
⟨520,2,0x35d668e,0xdfdd38de87f035d,0x3ff8000000000000000000000000000⟩,
⟨522,3,0x35d000e,0xdfdd000007f035d,0x3ffa080002001000000000000000000⟩,
⟨528,2,0x1de03e,0x7dd7d06bffe01d,0x20c4100002000000000000000000000⟩,
⟨529,3,0xe03e,0x7d06bffe01d,0x20c490600718a0cc000000000000000⟩,
⟨530,3,0x1d003e,0x7dd00003ffe01d,0x38c71c0002001000000000000000000⟩,
⟨576,2,0x34ce696,0xdb8d7ddeabb434c,0x20c0000000e00000000000000000000⟩,
⟨577,3,0xe696,0x7ddeabb434c,0x20c0004000f40088000000000000000⟩,
⟨584,3,0x34c6686,0xdb8d38de83b034c,0x3ff8000000e00000000000000000000⟩,
⟨768,2,0x31ce63e,0x9f9c799e3ffc31c,0x20c0000007000000000000000000000⟩,
⟨769,3,0xe63e,0x799e3ffc31c,0x20c0004007180088000000000000000⟩,
⟨770,3,0x31c003e,0x9f9c00003ffc31c,0x38c2080007001000000000000000000⟩,
⟨776,3,0x31c660e,0x9f9c389e07f031c,0x3ff8000007000000000000000000000⟩,
⟨778,4,0x31c000e,0x9f9c000007f031c,0x3ffa080007001000000000000000000⟩,
⟨784,3,0x1ce03e,0x79c79063ffc01c,0x20c410000700a000000000000000000⟩,
⟨785,4,0xe03e,0x79063ffc01c,0x20c490600718a0cc000000000000000⟩,
⟨786,4,0x1c003e,0x79c00003ffc01c,0x38c71c000700f800000000000000000⟩,
⟨832,3,0x30ce616,0x9b8c799e2bb430c,0x20c0000007ff0000000000000000000⟩,
⟨833,4,0xe616,0x799e2bb430c,0x20c0004007ff0088000000000000000⟩,
⟨840,4,0x30c6606,0x9b8c389e03b030c,0x3ff8000007ff0000000000000000000⟩,
⟨1025,2,0x33ab,0x6eebb6db9d7,0x300000000000000080000000000000000⟩,
⟨1026,2,0x1d7002b,0xeef7000036db9d7,0x300002400000000000000000000000000⟩,
⟨1028,2,0x1d71381,0xeef706eb800b9d7,0x3fc000000200000000000000000000000⟩,
⟨1030,3,0x1d70001,0xeef70000000b9d7,0x3fc002400210000000000000000000000⟩,
⟨1032,2,0x1d7238a,0xeef728eb86d01d7,0x3fc200010000000000000000000000000⟩,
⟨1034,3,0x1d7000a,0xeef7000006d01d7,0x3fd212490802001000000000000000000⟩,
⟨1036,3,0x1d70380,0xeef700eb80001d7,0x3fc200010200400200000000000000000⟩,
⟨1038,4,0x1d70000,0xeef7000000001d7,0x3fd212490a12421200000000000000000⟩,
⟨1040,2,0x17302b,0x6f76e03b6db817,0x300000000000000000000000000000000⟩,
⟨1041,3,0x302b,0x6e03b6db817,0x300000000000008000000000000000000⟩,
⟨1042,3,0x17002b,0x6f7000036db817,0x300007e00000000000000000000000000⟩,
⟨1056,2,0x1c33381,0xe8776eeb90539c3,0x3fc000000000000000000000000000000⟩,
⟨1057,3,0x3381,0x6eeb90539c3,0x3fc0000004a0000000000000000000000⟩,
⟨1060,3,0x1c31381,0xe87706eb80039c3,0x3fc000000200000000000000000000000⟩,
⟨1064,3,0x1c32380,0xe87728eb80501c3,0x3fc200010000400000000000000000000⟩,
⟨1068,4,0x1c30380,0xe87700eb80001c3,0x3fc200010200400000000000000000000⟩,
⟨1152,2,0xd311a9,0x6cf34e69b4cb8d3,0x300000000000000000000000000000000⟩,
⟨1153,3,0x11a9,0x4e69b4cb8d3,0x300000000000000000000000000000000⟩,
⟨1154,3,0xd30029,0x6cf3000034cb8d3,0x300002400000000000000000000000000⟩,
⟨1156,3,0xd31181,0x6cf30669800b8d3,0x3fc000000200000000000000000000000⟩,
⟨1158,4,0xd30001,0x6cf30000000b8d3,0x3fc002400210000000000000000000000⟩,
⟨1168,3,0x131029,0x4f34e01b4cb813,0x300000000000000000000000000000000⟩,
⟨1169,4,0x1029,0x4e01b4cb813,0x300000000000000000000000000000000⟩,
⟨1170,4,0x130029,0x4f3000034cb813,0x300007e00000000000000000000000000⟩,
⟨1184,3,0xc31181,0x68734e6990438c3,0x3fc000000200000000000000000000000⟩,
⟨1185,4,0x1181,0x4e6990438c3,0x3fc0000007a0000000000000000000000⟩,
⟨1188,4,0xc31181,0x6873066980038c3,0x3fc000000200000000000000000000000⟩,
⟨1536,2,0x15522aa,0xced56ccab6da155,0x3038c7fc6000000000000000000000000⟩,
⟨1537,3,0x22aa,0x6ccab6da155,0x3038c7fc6000000000000000000000000⟩,
⟨1538,3,0x155002a,0xced5000036da155,0x3038c7fc6000000000000000000000000⟩,
⟨1544,3,0x155228a,0xced528ca86d0155,0x3ffffffff800000000000000000000000⟩,
⟨1546,4,0x155000a,0xced5000006d0155,0x3ffffffff800000000000000000000000⟩,
⟨1552,3,0x15202a,0x6d56c02b6da015,0x3038c7fc6000000000000000000000000⟩,
⟨1553,4,0x202a,0x6c02b6da015,0x3038c7fc6000000000000000000000000⟩,
⟨1554,4,0x15002a,0x6d5000036da015,0x3038c7fc6000000000000000000000000⟩,
⟨2049,2,0xdd75,0x77f57f2feaa,0x0⟩,
⟨2050,2,0x2aa0035,0xf76a80003f2feaa,0x2000000000000000000000000000⟩,
⟨2052,2,0x2aa1d41,0xf76a87f5400feaa,0x0⟩,
⟨2054,3,0x2aa0001,0xf76a8000000feaa,0x248002400000000000000000000000000⟩,
⟨2064,2,0xad835,0x76af7057f2fc0a,0x0⟩,
⟨2065,3,0xd835,0x77057f2fc0a,0x0⟩,
⟨2066,3,0xa0035,0x76a80003f2fc0a,0x7000000000000000000000000000⟩,
⟨2080,2,0x2a2dd41,0xf06af7f55823ea2,0x80000000000000000000000000000000⟩,
⟨2081,3,0xdd41,0x77f55823ea2,0x90000000000000000000000000000000⟩,
⟨2084,3,0x2a21d41,0xf06a87f54003ea2,0x80000000000000000000000000000000⟩,
⟨2112,2,0x2a8dd54,0xf30af7f56b24ea8,0x0⟩,
⟨2113,3,0xdd54,0x77f56b24ea8,0x80000000000000000000000000000⟩,
⟨2116,3,0x2a81d40,0xf30a87f54004ea8,0x400000000000000000000000000000⟩,
⟨2144,3,0x2a0dd40,0xf00af7f54820ea0,0x80400000000000000000000000000000⟩,
⟨2145,4,0xdd40,0x77f54820ea0,0x904a0000000000000000000000000000⟩,
⟨2148,4,0x2a01d40,0xf00a87f54000ea0,0x80400000000000000000000000000000⟩,
⟨2176,2,0xa29971,0x7562d7717d0fca2,0x0⟩,
⟨2177,3,0x9971,0x57717d0fca2,0x0⟩,
⟨2178,3,0xa20031,0x756280003d0fca2,0x0⟩,
⟨2180,3,0xa21941,0x75628771400fca2,0x80000000000000000000000000000000⟩,
⟨2182,4,0xa20001,0x75628000000fca2,0x2e8000000000000000000000000000000⟩,
⟨2192,3,0x29831,0x562d7017d0fc02,0x0⟩,
⟨2193,4,0x9831,0x57017d0fc02,0x0⟩,
⟨2194,4,0x20031,0x56280003d0fc02,0x0⟩,
⟨2208,3,0xa29941,0x7062d7715803ca2,0x80000000000000000000000000000000⟩,
⟨2209,4,0x9941,0x57715803ca2,0x90000000000000000000000000000000⟩,
⟨2212,4,0xa21941,0x706287714003ca2,0x80000000000000000000000000000000⟩,
⟨2304,2,0x228cc74,0xb728f3b47f2d628,0x0⟩,
⟨2305,3,0xcc74,0x73b47f2d628,0x0⟩,
⟨2306,3,0x2280034,0xb72880003f2d628,0x0⟩,
⟨2320,3,0x8c834,0x728f3047f2d408,0x0⟩,
⟨2321,4,0xc834,0x73047f2d408,0x0⟩,
⟨2322,4,0x80034,0x72880003f2d408,0x0⟩,
⟨2368,3,0x228cc54,0xb308f3b46b24628,0x0⟩,
⟨2369,4,0xcc54,0x73b46b24628,0x0⟩]
private def T5f : Array TriFeature := #[⟨2368,0x7ffffffff0003f801ff803ff⟩,
⟨832,0x3ff81ff807ffffff00000001ff803ff⟩,
⟨2208,0x7f80007fffffffffe0003c3f⟩,
⟨1184,0x3fc000e3f800000000fffffffe0003c3f⟩,
⟨2144,0x7f8ff07ff1fe3f8fe3f8003f⟩,
⟨1552,0x31f8fffc78000000000000071fc7fffcf⟩,
⟨2320,0xff1ff8ff001c7801c7fffcf⟩,
⟨784,0x38fffc78071ff8ff00000001c7fffcf⟩,
⟨2192,0xf800f8ffe3fc7f1e007ffcf⟩,
⟨1168,0x31c007fc7800000000e3fc7f1e007ffcf⟩,
⟨1544,0x3ffffffff800000000000003e7ff9ccf1⟩,
⟨776,0x3ffffff807ff3f0f00000001ff9ccf1⟩,
⟨584,0xffff81ff807ff3f0f000000e7ff800f1⟩,
⟨328,0x3ff81fff3fff3f0f00039801ff800f1⟩,
⟨1064,0x3fc7f8e3f8000000007cef9be63f80c31⟩,
⟨104,0xfc7f803ff38ff070f1ce398e63f80031⟩,
⟨2180,0x7f8005f33fffffffe002d572⟩,
⟨1156,0x3fc0036f9800000000fffffffe002d572⟩,
⟨2116,0x7fbe75f331fe3f8fef980172⟩,
⟨2084,0x7f8e70733fffffffe3981432⟩,
⟨1060,0x3fc738639800000000fffffffe3981432⟩,
⟨164,0x3fc000639ff8000733fffffffe0001432⟩,
⟨100,0xfc738039ff8e707331fe3f8fe3980032⟩,
⟨1036,0x3fdf3b6f98000000007cef9be6f98c470⟩,
⟨76,0xfdf380f9f3be71f031ce398e6f980070⟩,
⟨44,0x3fc738639f38e707037cef9be63980430⟩,
⟨1538,0x36fb5ffda8000000000000076bdafffd4⟩,
⟨2306,0x35f6bfb55001da801dafffd4⟩,
⟨770,0x3b5ffda8076bfb5500000001dafffd4⟩,
⟨2178,0x35800fb55ed7daf6a007ffd4⟩,
⟨1154,0x36c007fda800000000ed7daf6a007ffd4⟩,
⟨2066,0x5f0bf855e17c2f0bc2fffc4⟩,
⟨1042,0x30f85ffc2800000000e17c2f0bc2fffc4⟩,
⟨530,0x30f85ffc28070bf8550000070bc2fffc4⟩,
⟨274,0x385ffc285f0bf855001c2801c2fffc4⟩,
⟨146,0x30c007fc285800f855e17c2f0a007ffc4⟩,
⟨1034,0x36fb5ffda8000000006c6d8b63da9ccd0⟩,
⟨522,0x36fb5ffda8076b3b0500000363da9ccd0⟩,
⟨266,0x3b5ffdab1f6b3b05000d8801da9ccd0⟩,
⟨2054,0x35b635b11ed7daf6ad8ad550⟩,
⟨1030,0x36db1b6d8800000000ed7daf6ad8ad550⟩,
⟨134,0x36c0036d8b58005b11ed7daf6a002d550⟩,
⟨14,0x36db1b6d8b1b631b016c6d8b62d88c450⟩,
⟨1537,0x1b6dedb6f000000000000005bd6f77baf⟩,
⟨2305,0x5edbdedfe0016f0016f77baf⟩,
⟨769,0x2dedb6f005bdedfe000000016f77baf⟩,
⟨2177,0x5e800edfeb7b6f5bc0077baf⟩,
⟨1153,0x1b4005b6f000000000b7b6f5bc0077baf⟩,
⟨2113,0x5edbdedfe17a2f0bd6f003af⟩,
⟨577,0xb6de816f005bdedfe000000bd6f003af⟩,
⟨321,0x2de816f5edbdedfe0002f0016f003af⟩,
⟨2081,0x5e8bd05feb7b6f5bc2f0382f⟩,
⟨1057,0x1b45e8a2f000000000b7b6f5bc2f0382f⟩,
⟨161,0x1b4000a2f5e80005feb7b6f5bc000382f⟩,
⟨97,0xb45e802f5e8bd05fe17a2f0bc2f0002f⟩,
⟨2065,0xed1de8fea3b4751d4777b8f⟩,
⟨1041,0x1168edb47000000000a3b4751d4777b8f⟩,
⟨529,0x1168edb470051de8fe0000051d4777b8f⟩,
⟨273,0x28edb470ed1de8fe001470014777b8f⟩,
⟨145,0x114005b470e800e8fea3b4751c0077b8f⟩]
private def T5c : Array Nat := #[0x0,0x0,0x400824b8080109170024b92e4b85df7,0x13c979fff9792f7f7f25ffffffffbffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff]
private abbrev T5b : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
private def T5q : List Nat := [840,2212,1188,2148,1068,108,1554,2322,786,2194,1170,1546,778,2182,1158,1038,2369,833,2209,1185,2145,1553,2321,785,2193,1169]
private def T5k : List (List Nat) := [[6,1537,2113],[33,1034,2306],[1034,1057,2304],[1536,2054,2113]]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T5checked : trioTest T5a T5f T5c 8 (fun x y z=>decide ([x,y,z]∈T5k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T5valid : trioValidated T5b T5a T5q T5f T5c 8=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T5close : T5k.all (fun cs=>decide (norm2 (attach cs T5b)∈atlas))=true := by decide +kernel
private theorem B3_5ok {cs : List Nat} (ex : Extension 6 3 T5b cs) (he : edges_ (attach cs T5b)≤33) : norm2 (attach cs T5b)∈atlas :=
  triExtension norm2 atlas T5b T5a T5q T5f T5c 8 T5k (by decide +kernel) T5valid T5checked T5close ex he
private def T6a : List TrioAtom := [⟨6,2,0x3ff0001,0xffff8000000ffff,0x148012008400000012124224020008400⟩,
⟨10,2,0x3ff000e,0xffff800007f03ff,0x40400108410008002004004001000010⟩,
⟨12,2,0x3ff03c0,0xffff807fc0003ff,0x1490400000000000000000000008000⟩,
⟨14,3,0x3ff0000,0xffff800000003ff,0x149492528490848052124224029088450⟩,
⟨17,2,0xfff1,0x7ffff87fc1f,0x202800000101500042200⟩,
⟨20,2,0x1f1fc1,0x7ff87ffc00fc1f,0x3800000000000000000000007c000⟩,
⟨33,2,0xe47f,0x7b87fff3fe3,0x2004a00009980000000⟩,
⟨34,2,0x3e3003f,0xf87f80003ff3fe3,0x8400000007004008000000000⟩,
⟨40,2,0x3e3204e,0xf87fb807c7f03e3,0x400000000000004000008000000000⟩,
⟨42,3,0x3e3000e,0xf87f800007f03e3,0x6040010841000800700400e001000000⟩,
⟨65,2,0xe9be,0x7db9fff4fec,0x26002200000001100400000⟩,
⟨66,2,0x3ec003e,0xfb8f80003ff4fec,0x8420000002004000002000000⟩,
⟨72,2,0x3ec218e,0xfb8fb839c7f03ec,0x600000038000000000000003800000⟩,
⟨74,3,0x3ec000e,0xfb8f800007f03ec,0x40600108438008002004004003800000⟩,
⟨96,2,0x3e0e03e,0xf80ff981fff0fe0,0x10020010004008008002000000⟩,
⟨97,3,0xe03e,0x7981fff0fe0,0x13826013304a09409982600000⟩,
⟨98,3,0x3e0003e,0xf80f80003ff0fe0,0x1c42001000700e008002000000⟩,
⟨104,3,0x3e0200e,0xf80fb801c7f03e0,0x60001c43801c004008008003800000⟩,
⟨106,4,0x3e0000e,0xf80f800007f03e0,0x6060019c43801c00700e00e003800000⟩,
⟨129,2,0xde77,0x5fde7bbfcf3,0x2020040001100000000⟩,
⟨130,2,0xf30037,0x7df380003bbfcf3,0x840000003a124200000000000⟩,
⟨132,2,0xf31e41,0x7df387de400fcf3,0x10000000000020000000000000000⟩,
⟨134,3,0xf30001,0x7df38000000fcf3,0x16801200840000003a124224020000000⟩,
⟨144,2,0x13de71,0x5f3dfde783fc13,0x20040180000000000⟩,
⟨145,3,0xde71,0x5fde783fc13,0x202820040181500000000⟩,
⟨148,3,0x131e41,0x5f387de400fc13,0x21003c0000000000200401c0000000000⟩,
⟨160,2,0xe3c477,0x7873db867bb3ce3,0x24e00008000000000⟩,
⟨161,3,0xc477,0x5b867bb3ce3,0x2024e40009980000000⟩,
⟨162,3,0xe30037,0x787380003bb3ce3,0x840000003ffa4208000000000⟩,
⟨257,2,0x7b9a,0x6efb9ddd73c,0x1c53e2a80000001100000000⟩,
⟨258,2,0x33c001a,0xbfbc80001ddd73c,0x85d0848042004000000000000⟩,
⟨260,2,0x33c1b80,0xbfbc86fb800d73c,0x10104001c0040000000000000000000⟩,
⟨262,3,0x33c0000,0xbfbc8000000d73c,0x1496925285d0848052124224000000000⟩,
⟨264,2,0x33c238a,0xbfbca87b85d033c,0x6000001c0040000000000000000000⟩,
⟨266,3,0x33c000a,0xbfbc800005d033c,0x406001085d0848042004004000000000⟩,
⟨268,3,0x33c0380,0xbfbc807b800033c,0x16904001c0040000000000000000000⟩,
⟨270,4,0x33c0000,0xbfbc8000000033c,0x1496925285d0848052124224000000000⟩,
⟨272,2,0x1c7b90,0x7bceefb985d41c,0x1c03e0000000000000000000⟩,
⟨273,3,0x7b90,0x6efb985d41c,0x1c53e2a80000100000000000⟩,
⟨276,3,0x1c1b80,0x7bc86fb800d41c,0x3938e001c03e0000000000000000000⟩,
⟨320,2,0x32c699a,0xbb8cecb99dd472c,0x1ffc40000000000000000000⟩,
⟨321,3,0x699a,0x6cb99dd472c,0x1fffe2a80000000000000000⟩,
⟨322,3,0x32c001a,0xbb8c80001dd472c,0x85ffc48042004000000000000⟩,
⟨328,3,0x32c218a,0xbb8ca83985d032c,0x6000001ffc40000000000000000000⟩,
⟨330,4,0x32c000a,0xbb8c800005d032c,0x406001085ffc48042004000000000000⟩,
⟨513,2,0xffc8,0x7fffeece35d,0x2100000105282a80000000000000000⟩,
⟨516,2,0x35d1fc0,0xdfdd07ffc00e35d,0x2110000000000000000000000000000⟩,
⟨520,2,0x35d23c8,0xdfdd387fc6c035d,0x3fc0000000000000000000000000000⟩,
⟨524,3,0x35d03c0,0xdfdd007fc00035d,0x3fd0400000000000000000000000000⟩,
⟨528,2,0x1dffc0,0x7dd7fffe84e01d,0x2120800000000000000000000000000⟩,
⟨529,3,0xffc0,0x7fffe84e01d,0x212124840105282a80000000000000000⟩,
⟨532,3,0x1d1fc0,0x7dd07ffc00e01d,0x2138800000000000000000000000000⟩,
⟨576,2,0x34ce988,0xdb8d7db9eec434c,0x2100000020000000000000000000000⟩,
⟨577,3,0xe988,0x7db9eec434c,0x2100000127382a80000000000000000⟩,
⟨584,3,0x34c2188,0xdb8d3839c6c034c,0x3fc00000b8840000000000000000000⟩,
⟨768,2,0x31c7b88,0x9f9c6efb8ccc31c,0x21000001c0040000000000000000000⟩,
⟨769,3,0x7b88,0x6efb8ccc31c,0x21000001c53e2a80000000000000000⟩,
⟨772,3,0x31c1b80,0x9f9c06fb800c31c,0x39104001c0040000000000000000000⟩,
⟨776,3,0x31c2388,0x9f9c287b84c031c,0x3fc00001c0040000000000000000000⟩,
⟨780,4,0x31c0380,0x9f9c007b800031c,0x3fd04001c0040000000000000000000⟩,
⟨784,3,0x1c7b80,0x79c6efb884c01c,0x21208001c03e0000000000000000000⟩,
⟨785,4,0x7b80,0x6efb884c01c,0x2121248401c53e2a80000000000000000⟩,
⟨788,4,0x1c1b80,0x79c06fb800c01c,0x3938e001c03e0000000000000000000⟩,
⟨832,3,0x30c6988,0x9b8c6cb98cc430c,0x21000001ffc40000000000000000000⟩,
⟨833,4,0x6988,0x6cb98cc430c,0x21000001fffe2a80000000000000000⟩,
⟨840,4,0x30c2188,0x9b8c283984c030c,0x3fc00001ffc40000000000000000000⟩,
⟨1025,2,0x96e5,0x776ef72b9d7,0x390000000000002000000000000000000⟩,
⟨1026,2,0x1d70025,0xeef70000372b9d7,0x3fc000008400000000000000000000000⟩,
⟨1028,2,0x1d716c1,0xeef7076ec00b9d7,0x390012000000000000000000000000000⟩,
⟨1030,3,0x1d70001,0xeef70000000b9d7,0x3fc012008400000000000000000000000⟩,
⟨1032,2,0x1d702c4,0xeef7306ec7201d7,0x3fc400100000000000000000000000000⟩,
⟨1034,3,0x1d70004,0xeef7000007201d7,0x3fc400108410008000000000000000000⟩,
⟨1036,3,0x1d702c0,0xeef7006ec0001d7,0x3fd492520000000000000000000000000⟩,
⟨1038,4,0x1d70000,0xeef7000000001d7,0x3fd492528490848000000000000000000⟩,
⟨1040,2,0x1796e1,0x6f7776ef02b817,0x390000000000000000000000000000000⟩,
⟨1041,3,0x96e1,0x776ef02b817,0x390000000000200000000000000000000⟩,
⟨1044,3,0x1716c1,0x6f7076ec00b817,0x39003f000000000000000000000000000⟩,
⟨1056,2,0x1c38465,0xe8777306f7239c3,0x3fc000000000000000000000000000000⟩,
⟨1057,3,0x8465,0x7306f7239c3,0x3fc000000000000000000000000000000⟩,
⟨1058,3,0x1c30025,0xe877000037239c3,0x3fc000008400000000000000000000000⟩,
⟨1064,3,0x1c30044,0xe8773006c7201c3,0x3fc400100000000000000000000000000⟩,
⟨1066,4,0x1c30004,0xe877000007201c3,0x3fc400108410000000000000000000000⟩,
⟨1152,2,0xd39665,0x6cf3574e732b8d3,0x390000000000000000000000000000000⟩,
⟨1153,3,0x9665,0x574e732b8d3,0x390000000000000000000000000000000⟩,
⟨1154,3,0xd30025,0x6cf30000332b8d3,0x3fc000008400000000000000000000000⟩,
⟨1156,3,0xd31641,0x6cf3074e400b8d3,0x390012000000000000000000000000000⟩,
⟨1158,4,0xd30001,0x6cf30000000b8d3,0x3fc012008400000000000000000000000⟩,
⟨1168,3,0x139661,0x4f3574e702b813,0x390000000000000000000000000000000⟩,
⟨1169,4,0x9661,0x574e702b813,0x390000000000000000000000000000000⟩,
⟨1172,4,0x131641,0x4f3074e400b813,0x39003f000000000000000000000000000⟩,
⟨1184,3,0xc38465,0x6873530673238c3,0x3fc000000000000000000000000000000⟩,
⟨1185,4,0x8465,0x530673238c3,0x3fc000000000000000000000000000000⟩,
⟨1186,4,0xc30025,0x6873000033238c3,0x3fc000008400000000000000000000000⟩,
⟨1536,2,0x15596c0,0xced5776ee60a155,0x392124840000000000000000000000000⟩,
⟨1537,3,0x96c0,0x776ee60a155,0x392124840000000000000000000000000⟩,
⟨1540,3,0x15516c0,0xced5076ec00a155,0x39213f840000000000000000000000000⟩,
⟨1544,3,0x15502c0,0xced5306ec600155,0x3ffffffe0000000000000000000000000⟩,
⟨1548,4,0x15502c0,0xced5006ec000155,0x3ffffffe0000000000000000000000000⟩,
⟨1552,3,0x1596c0,0x6d5776ee00a015,0x392124840000000000000000000000000⟩,
⟨1553,4,0x96c0,0x776ee00a015,0x392124840000000000000000000000000⟩,
⟨1556,4,0x1516c0,0x6d5076ec00a015,0x39213f840000000000000000000000000⟩,
⟨2049,2,0xfd3f,0x7ff53fffeaa,0x0⟩,
⟨2050,2,0x2aa003f,0xf76a80003fffeaa,0x0⟩,
⟨2064,2,0xafd31,0x76afff5387fc0a,0x0⟩,
⟨2065,3,0xfd31,0x7ff5387fc0a,0x0⟩,
⟨2080,2,0x2a2e43f,0xf06afb853ff3ea2,0x0⟩,
⟨2081,3,0xe43f,0x7b853ff3ea2,0x0⟩,
⟨2082,3,0x2a2003f,0xf06a80003ff3ea2,0x0⟩,
⟨2112,2,0x2a8e93e,0xf30afdb13ff4ea8,0x0⟩,
⟨2113,3,0xe93e,0x7db13ff4ea8,0x0⟩,
⟨2114,3,0x2a8003e,0xf30a80003ff4ea8,0x0⟩,
⟨2144,3,0x2a0e03e,0xf00af9813ff0ea0,0x0⟩,
⟨2145,4,0xe03e,0x79813ff0ea0,0x0⟩,
⟨2146,4,0x2a0003e,0xf00a80003ff0ea0,0x0⟩,
⟨2176,2,0xa2dc37,0x7562dfd43bbfca2,0x0⟩,
⟨2177,3,0xdc37,0x5fd43bbfca2,0x0⟩,
⟨2178,3,0xa20037,0x756280003bbfca2,0x0⟩,
⟨2192,3,0x2dc31,0x562dfd4383fc02,0x0⟩,
⟨2193,4,0xdc31,0x5fd4383fc02,0x0⟩,
⟨2208,3,0xa2c437,0x7062db843bb3ca2,0x0⟩,
⟨2209,4,0xc437,0x5b843bb3ca2,0x0⟩,
⟨2210,4,0xa20037,0x706280003bb3ca2,0x0⟩,
⟨2304,2,0x228791a,0xb728eef11ddd628,0x0⟩,
⟨2305,3,0x791a,0x6ef11ddd628,0x0⟩,
⟨2306,3,0x228001a,0xb72880001ddd628,0x0⟩,
⟨2320,3,0x87910,0x728eef1185d408,0x0⟩,
⟨2321,4,0x7910,0x6ef1185d408,0x0⟩,
⟨2368,3,0x228691a,0xb308ecb11dd4628,0x0⟩,
⟨2369,4,0x691a,0x6cb11dd4628,0x0⟩,
⟨2370,4,0x228001a,0xb30880001dd4628,0x0⟩]
private def T6f : Array TriFeature := #[⟨2368,0x1ffffffffc000fe0001ff803ff⟩,
⟨832,0x3fc0fe01ffffffc000000001ff803ff⟩,
⟨2208,0x1fe0001fffffffffffe0003c3f⟩,
⟨1184,0x3fc0071e000000003ffffffffe0003c3f⟩,
⟨2144,0x1fe3fc1ffc7f8fe0ffe3f8003f⟩,
⟨1552,0x39f9ffe600000000000001f1ffc7fffcf⟩,
⟨2320,0x3fc7fe3fc0071e0001c7fffcf⟩,
⟨784,0x39ffe601c7fe3fc000000001c7fffcf⟩,
⟨2192,0x3e003e3ff8ff1ff1fe007ffcf⟩,
⟨1168,0x39c03fe60000000038ff1ff1fe007ffcf⟩,
⟨1544,0x3ffffffe000000000000007e1fff9ccf1⟩,
⟨776,0x3ffffe01ffcfc3c000000001ff9ccf1⟩,
⟨584,0x7ffc0fe01ffcfc3c000000e1fff800f1⟩,
⟨328,0x3fc0ffcfffcfc3c000e60001ff800f1⟩,
⟨1064,0x3fc7c71e000000001f3be67e1e3f80c31⟩,
⟨104,0x7c7c01fce3fc1c3c738e60e1e3f80031⟩,
⟨1540,0x3ffffffe00000000000001f667d9fffd2⟩,
⟨772,0x3ffffe01d9feccc000000001d9fffd2⟩,
⟨1156,0x3fc03ffe000000003b5f6bf666007ffd2⟩,
⟨1044,0x39f9ffe600000000385f0bf067c1fffc2⟩,
⟨532,0x39f9ffe601c1fe0cc00001f067c1fffc2⟩,
⟨276,0x39ffe617c1fe0cc0070a0001c1fffc2⟩,
⟨148,0x39c03fe616003e0cf85f0bf066007ffc2⟩,
⟨1036,0x3ffffffe000000001b1b627607d99ccd0⟩,
⟨524,0x3ffffffe01d9cec0c000007607d99ccd0⟩,
⟨268,0x3ffffec7d9cec0c003620001d99ccd0⟩,
⟨2306,0x1fefad7d54007fe0000faad574⟩,
⟨2178,0x1fe0017d57ffffebeaa002d574⟩,
⟨1154,0x1ec01b7a000000003ffffebeaa002d574⟩,
⟨2114,0x1fefad7d547f8fe0eaafa80174⟩,
⟨322,0x1ec07bfefad7d54000fe0000fa80174⟩,
⟨2082,0x1fe3ac1d57ffffebeaa3a81434⟩,
⟨1058,0x1ec6c31a000000003ffffebeaa3a81434⟩,
⟨162,0x1ec0031bfe0001d57ffffebeaa0001434⟩,
⟨98,0x6c6c01bfe3ac1d547f8fe0eaa3a80034⟩,
⟨1034,0x1ededb7a000000001f3be63e0afa8c470⟩,
⟨266,0x1edb7bcefac7c14003e60000fa8c470⟩,
⟨74,0x6dec07bcefac7c14738e60e0afa80070⟩,
⟨42,0x1ec6c31bce3ac1c15f3be63e0a3a80430⟩,
⟨1030,0x1ededb7a000000003b5f6ab622d8ad550⟩,
⟨262,0x1edb7ad6d8d6c440076a0000d8ad550⟩,
⟨134,0x1ec01b7ad60016c47b5f6ab622002d550⟩,
⟨14,0x1ededb7ac6d8c6c05b1b623602d88c450⟩,
⟨1537,0x2b6b6dac00000000000001dbfd6f77baf⟩,
⟨2305,0x17b6f7b7f8005bc00016f77baf⟩,
⟨769,0x2b6dac016f7b7f80000000016f77baf⟩,
⟨2177,0x17a003b7fadedbddbfc0077baf⟩,
⟨1153,0x2b402dac000000002dedbddbfc0077baf⟩,
⟨2113,0x17b6f7b7f85e8bc0bfd6f003af⟩,
⟨577,0x36b40ac016f7b7f8000000bfd6f003af⟩,
⟨321,0x2b40ad7b6f7b7f8000bc00016f003af⟩,
⟨2081,0x17a2f417fadedbddbfc2f0382f⟩,
⟨1057,0x2b43450c000000002dedbddbfc2f0382f⟩,
⟨161,0x2b40050d7a00017fadedbddbfc000382f⟩,
⟨97,0x343400d7a2f417f85e8bc0bfc2f0002f⟩,
⟨2065,0x3b477a3fa8ed1dd1fd4777b8f⟩,
⟨1041,0x29696da40000000028ed1dd1fd4777b8f⟩,
⟨529,0x29696da401477a3f800001d1fd4777b8f⟩,
⟨273,0x296da43b477a3f80051c00014777b8f⟩,
⟨145,0x29402da43a003a3fa8ed1dd1fc0077b8f⟩]
private def T6c : Array Nat := #[0x0,0x0,0x40412e02004245c0092e122e4b85df7,0xbcbcffe5e4bdfdfc97ffefeffffbffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff]
private abbrev T6b : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
private def T6q : List Nat := [840,1556,788,1172,1548,780,2370,2210,1186,2146,330,1066,106,1158,1038,270,2369,833,2209,1185,2145,1553,2321,785,2193,1169]
private def T6k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T6checked : trioTest T6a T6f T6c 8 (fun x y z=>decide ([x,y,z]∈T6k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T6valid : trioValidated T6b T6a T6q T6f T6c 8=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T6close : T6k.all (fun cs=>decide (norm2 (attach cs T6b)∈atlas))=true := by decide +kernel
private theorem B3_6ok {cs : List Nat} (ex : Extension 6 3 T6b cs) (he : edges_ (attach cs T6b)≤33) : norm2 (attach cs T6b)∈atlas :=
  triExtension norm2 atlas T6b T6a T6q T6f T6c 8 T6k (by decide +kernel) T6valid T6checked T6close ex he
private def T7a : List TrioAtom := [⟨6,2,0x7fe001,0xffff800000ffff,0x2a0048021000000048490a420008400⟩,
⟨10,2,0x7fe00e,0xffff80007f03ff,0x810004210400200080100401000010⟩,
⟨12,2,0x7fe1c0,0xffff81fc0003ff,0x52410002001000000000008008040⟩,
⟨14,3,0x7fe000,0xffff80000003ff,0x2a52494a1242120148490a429088450⟩,
⟨17,2,0x1ff1,0x7fff87fc1f,0xc0a0000000000042200⟩,
⟨20,2,0x3e7c1,0x7ff8ffc00fc1f,0xe0000000000000000000007c000⟩,
⟨33,2,0x183f,0x761fff3fe3,0x7f80000c0128250940000000⟩,
⟨34,2,0x7c603f,0xf87f8003ff3fe3,0x2100000001c0100800000000⟩,
⟨40,2,0x7c680e,0xf87fb01c7f03e3,0x10000210400200100000801000000⟩,
⟨42,3,0x7c600e,0xf87f80007f03e3,0xc100042104002001c0100e01000000⟩,
⟨65,2,0x1afe,0x7aefff4fec,0x980088000000000400000⟩,
⟨66,2,0x7d803e,0xfb8f8003ff4fec,0x210800000080100002000000⟩,
⟨72,2,0x7d88ce,0xfb8fb0ec7f03ec,0x18000000e00000000000003800000⟩,
⟨74,3,0x7d800e,0xfb8f80007f03ec,0x818004210e00200080100403800000⟩,
⟨96,2,0x7c183e,0xf80ff20fff0fe0,0x710800400100200802000000⟩,
⟨97,3,0x183e,0x720fff0fe0,0x7f89804cc128250942600000⟩,
⟨98,3,0x7c003e,0xf80f8003ff0fe0,0x7108004001c0380802000000⟩,
⟨104,3,0x7c080e,0xf80fb00c7f03e0,0x18000710e00700100200803800000⟩,
⟨106,4,0x7c000e,0xf80f80007f03e0,0xc18006710e007001c0380e03800000⟩,
⟨129,2,0x1737,0x5f73bbfcf3,0x80801000000000000⟩,
⟨130,2,0x1e6037,0x7df38003bbfcf3,0x210000000e84908000000000⟩,
⟨132,2,0x1e6701,0x7df38f7000fcf3,0x400000000000800000000000000⟩,
⟨134,3,0x1e6001,0x7df3800000fcf3,0x2e00480210000000e8490a420000000⟩,
⟨144,2,0x27731,0x5f3df7383fc13,0x801004000000000⟩,
⟨145,3,0x1731,0x5f7383fc13,0xc0a0801004000000000⟩,
⟨148,3,0x26701,0x5f38f7000fc13,0xf00000000000801004000000000⟩,
⟨160,2,0x1c7037,0x7873d613bb3ce3,0x210000000938000800000000⟩,
⟨161,3,0x1037,0x5613bb3ce3,0x7f80000c0939270940000000⟩,
⟨162,3,0x1c6037,0x78738003bb3ce3,0x210000000ffe908800000000⟩,
⟨257,2,0x1fda,0x7ffdddd73c,0x714f8aa000000000000000⟩,
⟨260,2,0x6787c0,0xbfbc8ffc00d73c,0x40410007001000000000000000000⟩,
⟨264,2,0x6789ca,0xbfbcb1fc5d033c,0x18000007001000000000000000000⟩,
⟨268,3,0x6781c0,0xbfbc81fc00033c,0x5a410007001000000000000000000⟩,
⟨272,2,0x39fd0,0x7bcfffd85d41c,0x700f800000000000000000⟩,
⟨273,3,0x1fd0,0x7ffd85d41c,0x714f8aa000000000000000⟩,
⟨276,3,0x387c0,0x7bc8ffc00d41c,0xe4e3800700f800000000000000000⟩,
⟨320,2,0x659ada,0xbb8cfaeddd472c,0x7ff1000000000000000000⟩,
⟨321,3,0x1ada,0x7aeddd472c,0x7fff8aa000000000000000⟩,
⟨328,3,0x6588ca,0xbb8cb0ec5d032c,0x18000007ff1000000000000000000⟩,
⟨513,2,0x1fc8,0x7ffeece35d,0x8400000714f8aa000000000000000⟩,
⟨516,2,0x6ba7c0,0xdfdd0ffc00e35d,0xe4410002001000000000000000000⟩,
⟨520,2,0x6ba9c8,0xdfdd31fc6c035d,0xff000002001000000000000000000⟩,
⟨524,3,0x6ba1c0,0xdfdd01fc00035d,0xff410002001000000000000000000⟩,
⟨528,2,0x3bfc0,0x7dd7ffe84e01d,0x84820002001000000000000000000⟩,
⟨529,3,0x1fc0,0x7ffe84e01d,0x8492100714f8aa000000000000000⟩,
⟨532,3,0x3a7c0,0x7dd0ffc00e01d,0xe4e38002001000000000000000000⟩,
⟨576,2,0x699ac8,0xdb8d7aeeec434c,0x84000002e21000000000000000000⟩,
⟨577,3,0x1ac8,0x7aeeec434c,0x84000007fff8aa000000000000000⟩,
⟨584,3,0x6988c8,0xdb8d30ec6c034c,0xff000002e21000000000000000000⟩,
⟨768,2,0x639fc8,0x9f9c7ffcccc31c,0x84000007001000000000000000000⟩,
⟨769,3,0x1fc8,0x7ffcccc31c,0x8400000714f8aa000000000000000⟩,
⟨772,3,0x6387c0,0x9f9c0ffc00c31c,0xe4410007001000000000000000000⟩,
⟨776,3,0x6389c8,0x9f9c31fc4c031c,0xff000007001000000000000000000⟩,
⟨780,4,0x6381c0,0x9f9c01fc00031c,0xff410007001000000000000000000⟩,
⟨784,3,0x39fc0,0x79c7ffc84c01c,0x8482000700f800000000000000000⟩,
⟨785,4,0x1fc0,0x7ffc84c01c,0x8492100714f8aa000000000000000⟩,
⟨788,4,0x387c0,0x79c0ffc00c01c,0xe4e3800700f800000000000000000⟩,
⟨832,3,0x619ac8,0x9b8c7aeccc430c,0x84000007ff1000000000000000000⟩,
⟨833,4,0x1ac8,0x7aeccc430c,0x84000007fff8aa000000000000000⟩,
⟨840,4,0x6188c8,0x9b8c30ec4c030c,0xff000007ff1000000000000000000⟩,
⟨1025,2,0x565,0x6db772b9d7,0x3000000000000080000000000000000⟩,
⟨1026,2,0x3ae025,0xeef7000372b9d7,0x3f00000210000000000000000000000⟩,
⟨1028,2,0x3ae541,0xeef70db400b9d7,0x3000480000000000000000000000000⟩,
⟨1030,3,0x3ae001,0xeef7000000b9d7,0x3f00480210000000000000000000000⟩,
⟨1032,2,0x3ae144,0xeef721b47201d7,0x3f10004000000000000000000000000⟩,
⟨1034,3,0x3ae004,0xeef700007201d7,0x3f10004210400200000000000000000⟩,
⟨1036,3,0x3ae140,0xeef701b40001d7,0x3f52494802001000000000000000000⟩,
⟨1038,4,0x3ae000,0xeef700000001d7,0x3f52494a12421200000000000000000⟩,
⟨1040,2,0x2e561,0x6f76db702b817,0x3000000000000000000000000000000⟩,
⟨1041,3,0x561,0x6db702b817,0x300000000000c000000000000000000⟩,
⟨1044,3,0x2e541,0x6f70db400b817,0x3000fc0000000000000000000000000⟩,
⟨1056,2,0x386025,0xe87764177239c3,0x3f00000210000000000000000000000⟩,
⟨1057,3,0x25,0x64177239c3,0x3f000007f8000000000000000000000⟩,
⟨1058,3,0x386025,0xe87700037239c3,0x3f00000210000000000000000000000⟩,
⟨1064,3,0x386004,0xe87720147201c3,0x3f10004210400000000000000000000⟩,
⟨1066,4,0x386004,0xe87700007201c3,0x3f10004210400000000000000000000⟩,
⟨1152,2,0x1a6525,0x6cf34d3332b8d3,0x3000000000000000000000000000000⟩,
⟨1153,3,0x525,0x4d3332b8d3,0x3000000000000000000000000000000⟩,
⟨1154,3,0x1a6025,0x6cf3000332b8d3,0x3f00000210000000000000000000000⟩,
⟨1156,3,0x1a6501,0x6cf30d3000b8d3,0x3000480000000000000000000000000⟩,
⟨1158,4,0x1a6001,0x6cf3000000b8d3,0x3f00480210000000000000000000000⟩,
⟨1168,3,0x26521,0x4f34d3302b813,0x3000000000000000000000000000000⟩,
⟨1169,4,0x521,0x4d3302b813,0x3000000000000000000000000000000⟩,
⟨1172,4,0x26501,0x4f30d3000b813,0x3000fc0000000000000000000000000⟩,
⟨1184,3,0x186025,0x687344133238c3,0x3f00000210000000000000000000000⟩,
⟨1185,4,0x25,0x44133238c3,0x3f000007f8000000000000000000000⟩,
⟨1186,4,0x186025,0x687300033238c3,0x3f00000210000000000000000000000⟩,
⟨1536,2,0x2aa540,0xced56db660a155,0x30e4ff9000000000000000000000000⟩,
⟨1537,3,0x540,0x6db660a155,0x30e4ff9000000000000000000000000⟩,
⟨1540,3,0x2aa540,0xced50db400a155,0x30e4ff9000000000000000000000000⟩,
⟨1544,3,0x2aa140,0xced521b4600155,0x3ffffff800000000000000000000000⟩,
⟨1548,4,0x2aa140,0xced501b4000155,0x3ffffff800000000000000000000000⟩,
⟨1552,3,0x2a540,0x6d56db600a015,0x30e4ff9000000000000000000000000⟩,
⟨1553,4,0x540,0x6db600a015,0x30e4ff9000000000000000000000000⟩,
⟨1556,4,0x2a540,0x6d50db400a015,0x30e4ff9000000000000000000000000⟩,
⟨2049,2,0x1ebf,0x7fcbfffeaa,0x0⟩,
⟨2050,2,0x55403f,0xf76a8003fffeaa,0x0⟩,
⟨2064,2,0x15eb1,0x76affcb87fc0a,0x0⟩,
⟨2065,3,0x1eb1,0x7fcb87fc0a,0x0⟩,
⟨2080,2,0x54583f,0xf06af60bff3ea2,0x0⟩,
⟨2081,3,0x183f,0x760bff3ea2,0x0⟩,
⟨2082,3,0x54403f,0xf06a8003ff3ea2,0x0⟩,
⟨2112,2,0x551abe,0xf30afacbff4ea8,0x0⟩,
⟨2113,3,0x1abe,0x7acbff4ea8,0x0⟩,
⟨2114,3,0x55003e,0xf30a8003ff4ea8,0x0⟩,
⟨2144,3,0x54183e,0xf00af20bff0ea0,0x0⟩,
⟨2145,4,0x183e,0x720bff0ea0,0x0⟩,
⟨2146,4,0x54003e,0xf00a8003ff0ea0,0x0⟩,
⟨2176,2,0x145637,0x7562df43bbfca2,0x0⟩,
⟨2177,3,0x1637,0x5f43bbfca2,0x0⟩,
⟨2178,3,0x144037,0x75628003bbfca2,0x0⟩,
⟨2192,3,0x5631,0x562df4383fc02,0x0⟩,
⟨2193,4,0x1631,0x5f4383fc02,0x0⟩,
⟨2208,3,0x145037,0x7062d603bb3ca2,0x0⟩,
⟨2209,4,0x1037,0x5603bb3ca2,0x0⟩,
⟨2210,4,0x144037,0x70628003bb3ca2,0x0⟩,
⟨2304,2,0x451e9a,0xb728ffc9ddd628,0x0⟩,
⟨2305,3,0x1e9a,0x7fc9ddd628,0x0⟩,
⟨2320,3,0x11e90,0x728ffc985d408,0x0⟩,
⟨2321,4,0x1e90,0x7fc985d408,0x0⟩,
⟨2368,3,0x451a9a,0xb308fac9dd4628,0x0⟩,
⟨2369,4,0x1a9a,0x7ac9dd4628,0x0⟩]
private def T7f : Array TriFeature := #[⟨2368,0x7ffffffff0003f801ff803ff⟩,
⟨832,0xff03f807ffffff00000001ff803ff⟩,
⟨2208,0x7f80007fffffffffe0003c3f⟩,
⟨1184,0x3f001c7800000000fffffffe0003c3f⟩,
⟨2144,0x7f8ff07ff1fe3f8fe3f8003f⟩,
⟨1552,0x33e7ff98000000000000071fc7fffcf⟩,
⟨2320,0xff1ff8ff001c7801c7fffcf⟩,
⟨784,0xe7ff98071ff8ff00000001c7fffcf⟩,
⟨2192,0xf800f8ffe3fc7f1e007ffcf⟩,
⟨1168,0x3300ff9800000000e3fc7f1e007ffcf⟩,
⟨1544,0x3ffffff800000000000003e7ff9ccf1⟩,
⟨776,0xfffff807ff3f0f00000001ff9ccf1⟩,
⟨584,0xfff03f807ff3f0f000000e7ff800f1⟩,
⟨328,0xff03ff3fff3f0f00039801ff800f1⟩,
⟨1064,0x3f1f1c78000000007cef9be63f80c31⟩,
⟨104,0xf1f007f38ff070f1ce398e63f80031⟩,
⟨1540,0x3ffffff8000000000000076bd9fffd2⟩,
⟨772,0xfffff80767fb3300000001d9fffd2⟩,
⟨1156,0x3f00fff800000000ed7daf6a007ffd2⟩,
⟨1044,0x33e7ff9800000000e17c2f0bc1fffc2⟩,
⟨532,0x33e7ff980707f8330000070bc1fffc2⟩,
⟨276,0xe7ff985f07f833001c2801c1fffc2⟩,
⟨148,0x3300ff985800f833e17c2f0a007ffc2⟩,
⟨1036,0x3ffffff8000000006c6d8b63d99ccd0⟩,
⟨524,0x3ffffff807673b0300000363d99ccd0⟩,
⟨268,0xfffffb1f673b03000d8801d99ccd0⟩,
⟨2178,0x7f8005f55fffffffe002d574⟩,
⟨1154,0x3f006de800000000fffffffe002d574⟩,
⟨2114,0x7fbeb5f551fe3f8fefa80174⟩,
⟨2082,0x7f8eb0755fffffffe3a81434⟩,
⟨1058,0x3f1b0c6800000000fffffffe3a81434⟩,
⟨162,0x3f000c6ff8000755fffffffe0001434⟩,
⟨98,0xf1b006ff8eb07551fe3f8fe3a80034⟩,
⟨1034,0x3f7b6de8000000007cef9be6fa8c470⟩,
⟨74,0xf7b01ef3beb1f051ce398e6fa80070⟩,
⟨42,0x3f1b0c6f38eb07057cef9be63a80430⟩,
⟨1030,0x3f7b6de800000000ed7daf6ad8ad550⟩,
⟨134,0x3f006deb58005b11ed7daf6a002d550⟩,
⟨14,0x3f7b6deb1b631b016c6d8b62d88c450⟩,
⟨1537,0x15adb6b000000000000005bd6f77baf⟩,
⟨2305,0x5edbdedfe0016f0016f77baf⟩,
⟨769,0xadb6b005bdedfe000000016f77baf⟩,
⟨2177,0x5e800edfeb7b6f5bc0077baf⟩,
⟨1153,0x1500b6b000000000b7b6f5bc0077baf⟩,
⟨2113,0x5edbdedfe17a2f0bd6f003af⟩,
⟨577,0x5ad02b005bdedfe000000bd6f003af⟩,
⟨321,0xad02b5edbdedfe0002f0016f003af⟩,
⟨2081,0x5e8bd05feb7b6f5bc2f0382f⟩,
⟨1057,0x150d143000000000b7b6f5bc2f0382f⟩,
⟨161,0x15001435e80005feb7b6f5bc000382f⟩,
⟨97,0x50d0035e8bd05fe17a2f0bc2f0002f⟩,
⟨2065,0xed1de8fea3b4751d4777b8f⟩,
⟨1041,0x11a5b69000000000a3b4751d4777b8f⟩,
⟨529,0x11a5b690051de8fe0000051d4777b8f⟩,
⟨273,0xa5b690ed1de8fe001470014777b8f⟩,
⟨145,0x1100b690e800e8fea3b4751c0077b8f⟩]
private def T7c : Array Nat := #[0x0,0x0,0x10104b8080109170024b92e4b85df7,0x172f3ff9792f7f7f25ffffffffbffff,0x3ffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffff]
private abbrev T7b : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
private def T7q : List Nat := [840,1556,788,1172,1548,780,2210,1186,2146,1066,106,1158,1038,2369,833,2209,1185,2145,1553,2321,785,2193,1169]
private def T7k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T7checked : trioTest T7a T7f T7c 7 (fun x y z=>decide ([x,y,z]∈T7k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T7valid : trioValidated T7b T7a T7q T7f T7c 7=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T7close : T7k.all (fun cs=>decide (norm2 (attach cs T7b)∈atlas))=true := by decide +kernel
private theorem B3_7ok {cs : List Nat} (ex : Extension 6 3 T7b cs) (he : edges_ (attach cs T7b)≤33) : norm2 (attach cs T7b)∈atlas :=
  triExtension norm2 atlas T7b T7a T7q T7f T7c 7 T7k (by decide +kernel) T7valid T7checked T7close ex he
private def T8a : List TrioAtom := [⟨6,2,0x3ff0007,0xffff8000001ffff,0x40400108410020080100100010000010⟩,
⟨10,2,0x3ff0018,0xffff80001fe03ff,0x10008400000000000000000008000⟩,
⟨12,2,0x3ff0700,0xffff80fe00003ff,0x149492520000000000000000000008000⟩,
⟨14,3,0x3ff0000,0xffff800000003ff,0x149492528490921484908900890088450⟩,
⟨17,2,0xfff8,0x7fffffe1c1f,0x4044404462200⟩,
⟨24,2,0x1f3f18,0x7ffbcfe1fe001f,0x3800000000000000000000007c000⟩,
⟨33,2,0xc9ef,0x5f1fe3fffe3,0x130000278004000000⟩,
⟨34,2,0x3e300ef,0xf87f8001e3fffe3,0x8400000100000200000000000⟩,
⟨36,2,0x3e30107,0xf87f831e001ffe3,0x604001000000001c0000380000000000⟩,
⟨38,3,0x3e30007,0xf87f8000001ffe3,0x604001084100201c0100380010000000⟩,
⟨65,2,0xd2f7,0x6f67ecfffec,0x26000000000040027800000⟩,
⟨66,2,0x3ec00f7,0xfb8f8001ecfffec,0x8420000000000000020000000⟩,
⟨68,2,0x3ec0207,0xfb8f8366001ffec,0x40600100038000000000000038000000⟩,
⟨70,3,0x3ec0007,0xfb8f8000001ffec,0x40600108438020080100100038000000⟩,
⟨96,2,0x3e0c0e7,0xf80fcf07e0fffe0,0x10020040100200200020000000⟩,
⟨97,3,0xc0e7,0x4f07e0fffe0,0x1382604c130260278027800000⟩,
⟨98,3,0x3e000e7,0xf80f8001e0fffe0,0x1c420040100200200020000000⟩,
⟨100,3,0x3e00007,0xf80f8306001ffe0,0x6060019c4380701c0380380038000000⟩,
⟨102,4,0x3e00007,0xf80f8000001ffe0,0x6060019c4380701c0380380038000000⟩,
⟨129,2,0x6d6b,0x75baf76ecf3,0xe01000050004000000⟩,
⟨130,2,0xf3006b,0x7df38000f76ecf3,0x8400000e84908000000000000⟩,
⟨132,2,0xf30503,0x7df381ba000ecf3,0x60400100000000e00800000000000000⟩,
⟨134,3,0xf30003,0x7df38000000ecf3,0x60400108410020e84908100010000000⟩,
⟨136,2,0xf32d08,0x7df3b4ba17600f3,0x100012000000000e00800800000000000⟩,
⟨138,3,0xf30008,0x7df3800017600f3,0x168012008400000e84908900800000000⟩,
⟨140,3,0xf30500,0x7df380ba00000f3,0x169492520000000e00800800000000000⟩,
⟨142,4,0xf30000,0x7df3800000000f3,0x169492528490921e84908900890000000⟩,
⟨144,2,0x136d68,0x5f3f5baf760c13,0xe01006000000000000⟩,
⟨145,3,0x6d68,0x75baf760c13,0xe01006054400000000⟩,
⟨152,3,0x132d08,0x5f3b4ba1760013,0x39003f000000000e01c07c00000000000⟩,
⟨160,2,0xe3496b,0x7873d51ae36ece3,0xffe000200000000000⟩,
⟨161,3,0x496b,0x551ae36ece3,0xfff000278000000000⟩,
⟨162,3,0xe3006b,0x78738000e36ece3,0x8400000ffe908200000000000⟩,
⟨164,3,0xe30103,0x7873811a000ece3,0x60400100000000ffe800380000000000⟩,
⟨166,4,0xe30003,0x78738000000ece3,0x60400108410020ffe908380000000000⟩,
⟨257,2,0xb6b5,0x7aed7db773c,0x1c0200000000040000000000⟩,
⟨258,2,0x33c00b5,0xbfbc80017db773c,0x85d0921000000000000000000⟩,
⟨260,2,0x33c0605,0xbfbc82ec001773c,0x406001001c0100000000000000000000⟩,
⟨262,3,0x33c0005,0xbfbc8000001773c,0x406001085d0921080100100000000000⟩,
⟨264,2,0x33c3610,0xbfbcb8ec1da033c,0x10104001c0100000000000000000000⟩,
⟨266,3,0x33c0010,0xbfbc80001da033c,0x16904085d0921000000000000000000⟩,
⟨268,3,0x33c0600,0xbfbc80ec000033c,0x1496925201c0100000000000000000000⟩,
⟨270,4,0x33c0000,0xbfbc8000000033c,0x1496925285d0921484908900000000000⟩,
⟨272,2,0x1cb6b0,0x7bcfaed7da141c,0x1c0200000000000000000000⟩,
⟨273,3,0xb6b0,0x7aed7da141c,0x1c0200000004000000000000⟩,
⟨280,3,0x1c3610,0x7bcb8ec1da001c,0x3938e001c0380000000000000000000⟩,
⟨320,2,0x32c92b5,0xbb8cea656cb772c,0x1ffc00000000000000000000⟩,
⟨321,3,0x92b5,0x6a656cb772c,0x1ffe00000000000000000000⟩,
⟨322,3,0x32c00b5,0xbb8c80016cb772c,0x85ffd21000000000000000000⟩,
⟨324,3,0x32c0205,0xbb8c8264001772c,0x406001001ffd00000000000000000000⟩,
⟨326,4,0x32c0005,0xbb8c8000001772c,0x406001085ffd21080100000000000000⟩,
⟨513,2,0xff94,0x7fffbe9b35d,0x2100000000000000000000000000000⟩,
⟨516,2,0x35d0704,0xdfdd03fe001b35d,0x43fc0100000000000000000000000000⟩,
⟨520,2,0x35d3f10,0xdfdd3cfe1e8035d,0x2110000000000000000000000000000⟩,
⟨524,3,0x35d0700,0xdfdd00fe000035d,0x14bfd2520000000000000000000000000⟩,
⟨528,2,0x1dff90,0x7dd7fffbe8101d,0x2100000000000000000000000000000⟩,
⟨529,3,0xff90,0x7fffbe8101d,0x2100000000000000000000000000000⟩,
⟨536,3,0x1d3f10,0x7dd3cfe1e8001d,0x2138800000000000000000000000000⟩,
⟨576,2,0x34cd294,0xdb8d6f67ac9b34c,0x2100000020000000000000000000000⟩,
⟨577,3,0xd294,0x6f67ac9b34c,0x2100000127200000000000000000000⟩,
⟨580,3,0x34c0204,0xdb8d0366001b34c,0x43fc01000b8900000000000000000000⟩,
⟨768,2,0x31cb694,0x9f9c7aed3c9331c,0x39000001c0000000000000000000000⟩,
⟨769,3,0xb694,0x7aed3c9331c,0x39000001c0200000000000000000000⟩,
⟨772,3,0x31c0604,0x9f9c02ec001331c,0x43fc01001c0100000000000000000000⟩,
⟨776,3,0x31c3610,0x9f9c38ec1c8031c,0x39104001c0100000000000000000000⟩,
⟨780,4,0x31c0600,0x9f9c00ec000031c,0x14bfd25201c0100000000000000000000⟩,
⟨784,3,0x1cb690,0x79c7aed3c8101c,0x39000001c0200000000000000000000⟩,
⟨785,4,0xb690,0x7aed3c8101c,0x39000001c0200000000000000000000⟩,
⟨792,4,0x1c3610,0x79c38ec1c8001c,0x3938e001c0380000000000000000000⟩,
⟨832,3,0x30c9294,0x9b8c6a652c9330c,0x3fc00001ffc00000000000000000000⟩,
⟨833,4,0x9294,0x6a652c9330c,0x3fc00001ffe00000000000000000000⟩,
⟨836,4,0x30c0204,0x9b8c0264001330c,0x43fc01001ffd00000000000000000000⟩,
⟨1025,2,0xff4a,0x7fffdb5c9d7,0x210000000000000000000000000000000⟩,
⟨1028,2,0x1d70702,0xeef703fe001c9d7,0x3fc400100000000000000000000000000⟩,
⟨1032,2,0x1d73f08,0xeef73cfe1b401d7,0x210010000000000000000000000000000⟩,
⟨1036,3,0x1d70700,0xeef700fe00001d7,0x3fd492520000000000000000000000000⟩,
⟨1040,2,0x17ff48,0x6f77fffdb40817,0x210000000000000000000000000000000⟩,
⟨1041,3,0xff48,0x7fffdb40817,0x210000000000000000000000000000000⟩,
⟨1048,3,0x173f08,0x6f73cfe1b40017,0x21003c000000000000000000000000000⟩,
⟨1056,2,0x1c3c94a,0xe8775f1fc35c9c3,0x210000000000000000000000000000000⟩,
⟨1057,3,0xc94a,0x5f1fc35c9c3,0x210000000000000000000000000000000⟩,
⟨1060,3,0x1c30102,0xe877031e001c9c3,0x3fc400100000000000000000000000000⟩,
⟨1152,2,0xd36d4a,0x6cf375bad34c8d3,0x390000000000000000000000000000000⟩,
⟨1153,3,0x6d4a,0x75bad34c8d3,0x390000000000000000000000000000000⟩,
⟨1156,3,0xd30502,0x6cf301ba000c8d3,0x3fc400100000000000000000000000000⟩,
⟨1160,3,0xd32d08,0x6cf334ba13400d3,0x390012000000000000000000000000000⟩,
⟨1164,4,0xd30500,0x6cf300ba00000d3,0x3fd492520000000000000000000000000⟩,
⟨1168,3,0x136d48,0x4f375bad340813,0x390000000000000000000000000000000⟩,
⟨1169,4,0x6d48,0x75bad340813,0x390000000000000000000000000000000⟩,
⟨1176,4,0x132d08,0x4f334ba1340013,0x39003f000000000000000000000000000⟩,
⟨1184,3,0xc3494a,0x6873551ac34c8c3,0x3fc000000000000000000000000000000⟩,
⟨1185,4,0x494a,0x551ac34c8c3,0x3fc000000000000000000000000000000⟩,
⟨1188,4,0xc30102,0x6873011a000c8c3,0x3fc400100000000000000000000000000⟩,
⟨1536,2,0x155ff00,0xced57fff9a18155,0x212124840000000000000000000000000⟩,
⟨1537,3,0xff00,0x7fff9a18155,0x212124840000000000000000000000000⟩,
⟨1540,3,0x1550700,0xced503fe0018155,0x3ffffffe0000000000000000000000000⟩,
⟨1544,3,0x1553f00,0xced53cfe1a00155,0x21213c840000000000000000000000000⟩,
⟨1548,4,0x1550700,0xced500fe0000155,0x3ffffffe0000000000000000000000000⟩,
⟨1552,3,0x15ff00,0x6d57fff9a00015,0x212124840000000000000000000000000⟩,
⟨1553,4,0xff00,0x7fff9a00015,0x212124840000000000000000000000000⟩,
⟨1560,4,0x153f00,0x6d53cfe1a00015,0x21213c840000000000000000000000000⟩,
⟨2049,2,0xf8ff,0x7fd1ffffeaa,0x0⟩,
⟨2050,2,0x2aa00ff,0xf76a8001ffffeaa,0x0⟩,
⟨2064,2,0xaf8f8,0x76affd1ffe1c0a,0x0⟩,
⟨2065,3,0xf8f8,0x7fd1ffe1c0a,0x0⟩,
⟨2080,2,0x2a2c8ef,0xf06adf11e3ffea2,0x0⟩,
⟨2081,3,0xc8ef,0x5f11e3ffea2,0x0⟩,
⟨2082,3,0x2a200ef,0xf06a8001e3ffea2,0x0⟩,
⟨2112,2,0x2a8d0f7,0xf30aef41ecffea8,0x0⟩,
⟨2113,3,0xd0f7,0x6f41ecffea8,0x0⟩,
⟨2114,3,0x2a800f7,0xf30a8001ecffea8,0x0⟩,
⟨2144,3,0x2a0c0e7,0xf00acf01e0ffea0,0x0⟩,
⟨2145,4,0xc0e7,0x4f01e0ffea0,0x0⟩,
⟨2146,4,0x2a000e7,0xf00a8001e0ffea0,0x0⟩,
⟨2176,2,0xa2686b,0x7562f590f76eca2,0x0⟩,
⟨2177,3,0x686b,0x7590f76eca2,0x0⟩,
⟨2178,3,0xa2006b,0x75628000f76eca2,0x0⟩,
⟨2192,3,0x26868,0x562f590f760c02,0x0⟩,
⟨2193,4,0x6868,0x7590f760c02,0x0⟩,
⟨2208,3,0xa2486b,0x7062d510e36eca2,0x0⟩,
⟨2209,4,0x486b,0x5510e36eca2,0x0⟩,
⟨2210,4,0xa2006b,0x70628000e36eca2,0x0⟩,
⟨2304,2,0x228b0b5,0xb728fac17db7628,0x0⟩,
⟨2305,3,0xb0b5,0x7ac17db7628,0x0⟩,
⟨2306,3,0x22800b5,0xb72880017db7628,0x0⟩,
⟨2320,3,0x8b0b0,0x728fac17da1408,0x0⟩,
⟨2321,4,0xb0b0,0x7ac17da1408,0x0⟩,
⟨2368,3,0x22890b5,0xb308ea416cb7628,0x0⟩,
⟨2369,4,0x90b5,0x6a416cb7628,0x0⟩,
⟨2370,4,0x22800b5,0xb30880016cb7628,0x0⟩]
private def T8f : Array TriFeature := #[⟨2368,0x1fffffff0003f80007fff803ff⟩,
⟨832,0x3fc0fe01fffff0000000007fff803ff⟩,
⟨2208,0x1fe0007ffffffffff800003c3f⟩,
⟨1184,0x3fc0071e0000000fffffffff800003c3f⟩,
⟨2144,0x1fe3fc7f1fe3f83ff83ff8003f⟩,
⟨1552,0x39f9ffe60000000000007c7ffc7ffffcf⟩,
⟨2320,0x3fc7f8f001c780007c7ffffcf⟩,
⟨784,0x39ffe601c7f8f0000000007c7ffffcf⟩,
⟨2192,0x3e0038fe3fc7fc7f80007ffcf⟩,
⟨1168,0x39c03fe60000000e3fc7fc7f80007ffcf⟩,
⟨1544,0x3ffffffe0000000000007d87fd87fffd1⟩,
⟨776,0x3ffffe01d9fb30000000007d87fffd1⟩,
⟨1160,0x3fc03ffe0000000ecfd9fd8780007ffd1⟩,
⟨1048,0x39f9ffe60000000e0fc1fc07fc07fffc1⟩,
⟨536,0x39f9ffe601c1f83000007c07fc07fffc1⟩,
⟨280,0x39ffe60fc1f83001c180007c07fffc1⟩,
⟨152,0x39c03fe60e00383e0fc1fc0780007ffc1⟩,
⟨1540,0x3ffffffe0000000000001f999f999ccf2⟩,
⟨772,0x3ffffe00fadf50000000001f999ccf2⟩,
⟨1156,0x3fc03ffe00000007d6fa9f9980001ccf2⟩,
⟨580,0x7ffc0fe00fadf50000003999f99800f2⟩,
⟨324,0x3fc0ffd6fadf50003a80001f99800f2⟩,
⟨1060,0x3fc7c71e00000007d6fa9f99839980c32⟩,
⟨164,0x3fc0071fd6000757d6fa9f99800000c32⟩,
⟨100,0x7c7c01fd63ac751d63a8399839980032⟩,
⟨1036,0x3ffffffe00000006c6d89d819d819ccd0⟩,
⟨524,0x3ffffffe00d8db1000001d819d819ccd0⟩,
⟨268,0x3ffffec6d8db1000d880001d819ccd0⟩,
⟨140,0x3fc03ffec6001b16c6d89d8180001ccd0⟩,
⟨2306,0x1fffffff001ff80002faaad574⟩,
⟨2178,0x1fe003fffffffafaa80002d574⟩,
⟨2114,0x1fffffff1fe3f83aaafaa80174⟩,
⟨322,0x1ec07bfffffff0003f80002faa80174⟩,
⟨2082,0x1fe3fc7ffffffafaa83aa81434⟩,
⟨162,0x1ec0031bfe0007ffffffafaa800001434⟩,
⟨98,0x6c6c01bfe3fc7f1fe3f83aa83aa80034⟩,
⟨266,0x1edb7acfd9fb3001d980002d82ad550⟩,
⟨138,0x1ec01b7ace003b3ecfd9ad8280002d550⟩,
⟨262,0x1edb7bd6fadf5000fa80000f888c470⟩,
⟨134,0x1ec01b7bd6001f57d6fa8f8880000c470⟩,
⟨70,0x6dec07bd6fadf51d63a83888f8880070⟩,
⟨38,0x1ec6c31bd63ac757d6fa8f88838880430⟩,
⟨14,0x1ededb7ac6d8db16c6d88d808d808c450⟩,
⟨1537,0x2b6b6dac00000000000076ff76ff77baf⟩,
⟨2305,0x17b6f6de0016f000076ff77baf⟩,
⟨769,0x2b6dac016f6de00000000076ff77baf⟩,
⟨2177,0x17a002deb7b6f76ff000077baf⟩,
⟨1153,0x2b402dac0000000b7b6f76ff000077baf⟩,
⟨2113,0x17b6f6de17a2f02ff76ff003af⟩,
⟨577,0x36b40ac016f6de0000002ff76ff003af⟩,
⟨321,0x2b40ad7b6f6de0002f000076ff003af⟩,
⟨2081,0x17a2f45eb7b6f76ff02ff0382f⟩,
⟨1057,0x2b43450c0000000b7b6f76ff02ff0382f⟩,
⟨161,0x2b40050d7a0005eb7b6f76ff00000382f⟩,
⟨97,0x343400d7a2f45e17a2f02ff02ff0002f⟩,
⟨2065,0x3b4768ea3b47747f747f77b8f⟩,
⟨1041,0x29696da40000000a3b47747f747f77b8f⟩,
⟨529,0x29696da4014768e00000747f747f77b8f⟩,
⟨273,0x296da43b4768e001470000747f77b8f⟩,
⟨145,0x29402da43a0028ea3b47747f000077b8f⟩]
private def T8c : Array Nat := #[0x0,0x0,0x40412e02004970024b848b848b85df7,0xbcbcffe5e4bfff25fffbfbfbfbfbffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffff]
private abbrev T8b : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
private def T8q : List Nat := [1560,792,1176,836,1188,1548,780,1164,2370,2210,2146,326,166,102,270,142,2369,833,2209,1185,2145,1553,2321,785,2193,1169]
private def T8k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T8checked : trioTest T8a T8f T8c 8 (fun x y z=>decide ([x,y,z]∈T8k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T8valid : trioValidated T8b T8a T8q T8f T8c 8=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T8close : T8k.all (fun cs=>decide (norm2 (attach cs T8b)∈atlas))=true := by decide +kernel
private theorem B3_8ok {cs : List Nat} (ex : Extension 6 3 T8b cs) (he : edges_ (attach cs T8b)≤33) : norm2 (attach cs T8b)∈atlas :=
  triExtension norm2 atlas T8b T8a T8q T8f T8c 8 T8k (by decide +kernel) T8valid T8checked T8close ex he
private def T9a : List TrioAtom := [⟨6,2,0x3ff001,0xffff800000ffff,0xa40090042000012124224020008400⟩,
⟨10,2,0x3ff00e,0xffff80007f03ff,0x202000842100802004004001000010⟩,
⟨12,2,0x3ff1c0,0xffff81fc0003ff,0xa4a492900000000000000000008000⟩,
⟨14,3,0x3ff000,0xffff80000003ff,0xa4a492942924852124224029088450⟩,
⟨17,2,0xff1,0x7fff87fc1f,0x101500062200⟩,
⟨20,2,0x1f7c1,0x7ff8ffc00fc1f,0x8001d000000000000000000007c000⟩,
⟨33,2,0xa7f,0x763fff3fe3,0x7a00009980000000⟩,
⟨34,2,0x3e303f,0xf87f8003ff3fe3,0x42000007004008000000000⟩,
⟨40,2,0x3e304e,0xf87fb03c7f03e3,0x30200080000000700000e000000000⟩,
⟨42,3,0x3e300e,0xf87f80007f03e3,0x30200084210080700400e001000000⟩,
⟨65,2,0x8be,0x7acfff4fec,0x240000000001102600000⟩,
⟨66,2,0x3ec03e,0xfb8f8003ff4fec,0x42200002004000002000000⟩,
⟨72,2,0x3ec08e,0xfb8fb0cc7f03ec,0x203000800380000000000003800000⟩,
⟨74,3,0x3ec00e,0xfb8f80007f03ec,0x203000842380802004004003800000⟩,
⟨96,2,0x3e083e,0xf80ff20fff0fe0,0x80201007008008002000000⟩,
⟨97,3,0x83e,0x720fff0fe0,0x9c241287a09409982600000⟩,
⟨98,3,0x3e003e,0xf80f8003ff0fe0,0xe220100700e008002000000⟩,
⟨104,3,0x3e000e,0xf80fb00c7f03e0,0x303000ce2381c0700e00e003800000⟩,
⟨106,4,0x3e000e,0xf80f80007f03e0,0x303000ce2381c0700e00e003800000⟩,
⟨129,2,0xf77,0x5f77bbfcf3,0x38040001100000000⟩,
⟨130,2,0xf3037,0x7df38003bbfcf3,0x4200003a124200000000000⟩,
⟨132,2,0xf3741,0x7df38f7400fcf3,0x800090000000038020020000000000⟩,
⟨134,3,0xf3001,0x7df3800000fcf3,0xb4009004200003a124224020000000⟩,
⟨144,2,0x13f71,0x5f3df7783fc13,0x38040180000000000⟩,
⟨145,3,0xf71,0x5f7783fc13,0x38040181500000000⟩,
⟨148,3,0x13741,0x5f38f7400fc13,0x1c801f80000000380701f0000000000⟩,
⟨160,2,0xe3a77,0x7873d637bb3ce3,0x3ff80008000000000⟩,
⟨161,3,0xa77,0x5637bb3ce3,0x3ffc0009980000000⟩,
⟨162,3,0xe3037,0x78738003bb3ce3,0x4200003ffa4208000000000⟩,
⟨257,2,0x59a,0x6dd9ddd73c,0xc0e000000001100000000⟩,
⟨258,2,0x33c01a,0xbfbc8001ddd73c,0x42d24842004000000000000⟩,
⟨260,2,0x33c580,0xbfbc8dd800d73c,0x808092000c04000000000000000000⟩,
⟨262,3,0x33c000,0xbfbc800000d73c,0xa4b492942d24852124224000000000⟩,
⟨264,2,0x33c18a,0xbfbca1d85d033c,0x203000800c04000000000000000000⟩,
⟨266,3,0x33c00a,0xbfbc80005d033c,0x203000842d24842004004000000000⟩,
⟨268,3,0x33c180,0xbfbc81d800033c,0xa4b492900c04000000000000000000⟩,
⟨270,4,0x33c000,0xbfbc800000033c,0xa4b492942d24852124224000000000⟩,
⟨272,2,0x1c590,0x7bcedd985d41c,0xc0e000000000000000000⟩,
⟨273,3,0x590,0x6dd985d41c,0xc0e000000100000000000⟩,
⟨276,3,0x1c580,0x7bc8dd800d41c,0x81c9d7000c0e000000000000000000⟩,
⟨320,2,0x32c09a,0xbb8ce8c9dd472c,0xff4000000000000000000⟩,
⟨321,3,0x9a,0x68c9dd472c,0xffe000000000000000000⟩,
⟨322,3,0x32c01a,0xbb8c8001dd472c,0x42ff4842004000000000000⟩,
⟨328,3,0x32c08a,0xbb8ca0c85d032c,0x203000800ff4000000000000000000⟩,
⟨330,4,0x32c00a,0xbb8c80005d032c,0x203000842ff4842004000000000000⟩,
⟨513,2,0xfc8,0x7ffeece35d,0x10800000000000000000000000000⟩,
⟨516,2,0x35d7c0,0xdfdd0ffc00e35d,0x810890000000000000000000000000⟩,
⟨520,2,0x35d1c8,0xdfdd31fc6c035d,0x21fe00800000000000000000000000⟩,
⟨524,3,0x35d1c0,0xdfdd01fc00035d,0xa5fe92900000000000000000000000⟩,
⟨528,2,0x1dfc0,0x7dd7ffe84e01d,0x810904000000000000000000000000⟩,
⟨529,3,0xfc0,0x7ffe84e01d,0x1c90924200000000000000000000000⟩,
⟨532,3,0x1d7c0,0x7dd0ffc00e01d,0x8109d4000000000000000000000000⟩,
⟨576,2,0x34c888,0xdb8d7aceec434c,0x210800000200000000000000000000⟩,
⟨577,3,0x888,0x7aceec434c,0x310800000248000000000000000000⟩,
⟨584,3,0x34c088,0xdb8d30cc6c034c,0x21fe00800ba4000000000000000000⟩,
⟨768,2,0x31c588,0x9f9c6dd8ccc31c,0x1c800000c04000000000000000000⟩,
⟨769,3,0x588,0x6dd8ccc31c,0x1c800000c0e000000000000000000⟩,
⟨772,3,0x31c580,0x9f9c0dd800c31c,0x81c892000c04000000000000000000⟩,
⟨776,3,0x31c188,0x9f9c21d84c031c,0x21fe00800c04000000000000000000⟩,
⟨780,4,0x31c180,0x9f9c01d800031c,0xa5fe92900c04000000000000000000⟩,
⟨784,3,0x1c580,0x79c6dd884c01c,0x81c9d7000c0e000000000000000000⟩,
⟨785,4,0x580,0x6dd884c01c,0x1c9c9ff200c0e000000000000000000⟩,
⟨788,4,0x1c580,0x79c0dd800c01c,0x81c9d7000c0e000000000000000000⟩,
⟨832,3,0x30c088,0x9b8c68c8cc430c,0x21fe00800ff4000000000000000000⟩,
⟨833,4,0x88,0x68c8cc430c,0x31fe00c00ffe000000000000000000⟩,
⟨840,4,0x30c088,0x9b8c20c84c030c,0x21fe00800ff4000000000000000000⟩,
⟨1025,2,0xfe5,0x7fff72b9d7,0x1c80000000000000000000000000000⟩,
⟨1028,2,0x1d77c1,0xeef70ffc00b9d7,0x1c80090000000000000000000000000⟩,
⟨1032,2,0x1d71c4,0xeef731fc7201d7,0x1fe2000800000000000000000000000⟩,
⟨1036,3,0x1d71c0,0xeef701fc0001d7,0x1fea492900000000000000000000000⟩,
⟨1040,2,0x17fe1,0x6f77fff02b817,0x1c80000000000000000000000000000⟩,
⟨1041,3,0xfe1,0x7fff02b817,0x1c80000000000000000000000000000⟩,
⟨1044,3,0x177c1,0x6f70ffc00b817,0x1c801f8000000000000000000000000⟩,
⟨1056,2,0x1c3a65,0xe877763f7239c3,0x1fe0000000000000000000000000000⟩,
⟨1057,3,0xa65,0x763f7239c3,0x1fe0000000000000000000000000000⟩,
⟨1064,3,0x1c3044,0xe877303c7201c3,0x1fe2000800000000000000000000000⟩,
⟨1152,2,0xd3f65,0x6cf35f7732b8d3,0x1c80000000000000000000000000000⟩,
⟨1153,3,0xf65,0x5f7732b8d3,0x1c80000000000000000000000000000⟩,
⟨1156,3,0xd3741,0x6cf30f7400b8d3,0x1c80090000000000000000000000000⟩,
⟨1168,3,0x13f61,0x4f35f7702b813,0x1c80000000000000000000000000000⟩,
⟨1169,4,0xf61,0x5f7702b813,0x1c80000000000000000000000000000⟩,
⟨1172,4,0x13741,0x4f30f7400b813,0x1c801f8000000000000000000000000⟩,
⟨1184,3,0xc3a65,0x687356373238c3,0x1fe0000000000000000000000000000⟩,
⟨1185,4,0xa65,0x56373238c3,0x1fe0000000000000000000000000000⟩,
⟨1536,2,0x155fc0,0xced57ffe60a155,0x1c90924200000000000000000000000⟩,
⟨1537,3,0xfc0,0x7ffe60a155,0x1c90924200000000000000000000000⟩,
⟨1540,3,0x1557c0,0xced50ffc00a155,0x1c909fc200000000000000000000000⟩,
⟨1544,3,0x1551c0,0xced531fc600155,0x1fffffff00000000000000000000000⟩,
⟨1548,4,0x1551c0,0xced501fc000155,0x1fffffff00000000000000000000000⟩,
⟨1552,3,0x15fc0,0x6d57ffe00a015,0x1c90924200000000000000000000000⟩,
⟨1553,4,0xfc0,0x7ffe00a015,0x1c90924200000000000000000000000⟩,
⟨1556,4,0x157c0,0x6d50ffc00a015,0x1c909fc200000000000000000000000⟩,
⟨2049,2,0xe3f,0x7fa3fffeaa,0x0⟩,
⟨2050,2,0x2aa03f,0xf76a8003fffeaa,0x0⟩,
⟨2064,2,0xae31,0x76affa387fc0a,0x0⟩,
⟨2065,3,0xe31,0x7fa387fc0a,0x0⟩,
⟨2080,2,0x2a2a3f,0xf06af623ff3ea2,0x0⟩,
⟨2081,3,0xa3f,0x7623ff3ea2,0x0⟩,
⟨2082,3,0x2a203f,0xf06a8003ff3ea2,0x0⟩,
⟨2112,2,0x2a883e,0xf30afa83ff4ea8,0x0⟩,
⟨2113,3,0x83e,0x7a83ff4ea8,0x0⟩,
⟨2114,3,0x2a803e,0xf30a8003ff4ea8,0x0⟩,
⟨2144,3,0x2a083e,0xf00af203ff0ea0,0x0⟩,
⟨2145,4,0x83e,0x7203ff0ea0,0x0⟩,
⟨2146,4,0x2a003e,0xf00a8003ff0ea0,0x0⟩,
⟨2176,2,0xa2e37,0x7562df23bbfca2,0x0⟩,
⟨2177,3,0xe37,0x5f23bbfca2,0x0⟩,
⟨2178,3,0xa2037,0x75628003bbfca2,0x0⟩,
⟨2192,3,0x2e31,0x562df2383fc02,0x0⟩,
⟨2193,4,0xe31,0x5f2383fc02,0x0⟩,
⟨2208,3,0xa2a37,0x7062d623bb3ca2,0x0⟩,
⟨2209,4,0xa37,0x5623bb3ca2,0x0⟩,
⟨2210,4,0xa2037,0x70628003bb3ca2,0x0⟩,
⟨2304,2,0x22841a,0xb728ed81ddd628,0x0⟩,
⟨2305,3,0x41a,0x6d81ddd628,0x0⟩,
⟨2306,3,0x22801a,0xb7288001ddd628,0x0⟩,
⟨2320,3,0x8410,0x728ed8185d408,0x0⟩,
⟨2321,4,0x410,0x6d8185d408,0x0⟩,
⟨2368,3,0x22801a,0xb308e881dd4628,0x0⟩,
⟨2369,4,0x1a,0x6881dd4628,0x0⟩,
⟨2370,4,0x22801a,0xb3088001dd4628,0x0⟩]
private def T9f : Array TriFeature := #[⟨2368,0xffffffc000fe0001ff803ff⟩,
⟨832,0x1fe07f00ffffc000000001ff803ff⟩,
⟨2208,0xff001ffffffffffe0003c3f⟩,
⟨1184,0x1fe0038f0000003ffffffffe0003c3f⟩,
⟨2144,0xff3f1fc7f8fe0ffe3f8003f⟩,
⟨1552,0x1cfcfff3000000000001f1ffc7fffcf⟩,
⟨2320,0x1fc7e3c0071e0001c7fffcf⟩,
⟨784,0x1cfff300c7e3c000000001c7fffcf⟩,
⟨2192,0x1f00e3f8ff1ff1fe007ffcf⟩,
⟨1168,0x1ce01ff300000038ff1ff1fe007ffcf⟩,
⟨1544,0x1fffffff0000000000007e1fff9ccf1⟩,
⟨776,0x1fffff00ff7cc000000001ff9ccf1⟩,
⟨584,0x3ffe07f00ff7cc000000e1fff800f1⟩,
⟨328,0x1fe07fe7ff7cc000e60001ff800f1⟩,
⟨1064,0x1fe3e38f0000001f3be67e1e3f80c31⟩,
⟨104,0x3e3e00fe73f1cc738e60e1e3f80031⟩,
⟨1540,0x1fffffff000000000001f667d9fffd2⟩,
⟨772,0x1fffff00dbed4000000001d9fffd2⟩,
⟨1156,0x1fe01fff0000003b5f6bf666007ffd2⟩,
⟨1044,0x1cfcfff3000000385f0bf067c1fffc2⟩,
⟨532,0x1cfcfff300c3e1400001f067c1fffc2⟩,
⟨276,0x1cfff30bc3e140070a0001c1fffc2⟩,
⟨148,0x1ce01ff30b00e1785f0bf066007ffc2⟩,
⟨1036,0x1fffffff0000001b1b627607d99ccd0⟩,
⟨524,0x1fffffff00db6c4000007607d99ccd0⟩,
⟨268,0x1fffff63db6c4003620001d99ccd0⟩,
⟨2306,0xffffffc007fe0000faad574⟩,
⟨2178,0xff00fffffffebeaa002d574⟩,
⟨2114,0xffffffc7f8fe0eaafa80174⟩,
⟨322,0xf603dffffffc000fe0000fa80174⟩,
⟨2082,0xff3f1ffffffebeaa3a81434⟩,
⟨162,0xf60018dff001ffffffebeaa0001434⟩,
⟨98,0x363600dff3f1fc7f8fe0eaa3a80034⟩,
⟨266,0xf6dbde7ff7cc003e60000fa8c470⟩,
⟨74,0x36f603de7ff7cc738e60e0afa80070⟩,
⟨42,0xf63618de73f1cdf3be63e0a3a80430⟩,
⟨262,0xf6dbd6bdbed40076a0000d8ad550⟩,
⟨134,0xf600dbd6b00ed7b5f6ab622002d550⟩,
⟨14,0xf6f6dbd63db6c5b1b623602d88c450⟩,
⟨1537,0x15b5b6d6000000000001dbfd6f77baf⟩,
⟨2305,0xbd6db78005bc00016f77baf⟩,
⟨769,0x15b6d6006db780000000016f77baf⟩,
⟨2177,0xbd00b7adedbddbfc0077baf⟩,
⟨1153,0x15a016d60000002dedbddbfc0077baf⟩,
⟨2113,0xbd6db785e8bc0bfd6f003af⟩,
⟨577,0x1b5a056006db78000000bfd6f003af⟩,
⟨321,0x15a056bd6db78000bc00016f003af⟩,
⟨2081,0xbd2d17adedbddbfc2f0382f⟩,
⟨1057,0x15a1a2860000002dedbddbfc2f0382f⟩,
⟨161,0x15a00286bd0017adedbddbfc000382f⟩,
⟨97,0x1a1a006bd2d1785e8bc0bfc2f0002f⟩,
⟨2065,0x1d45a3a8ed1dd1fd4777b8f⟩,
⟨1041,0x14b4b6d200000028ed1dd1fd4777b8f⟩,
⟨529,0x14b4b6d20045a3800001d1fd4777b8f⟩,
⟨273,0x14b6d21d45a380051c00014777b8f⟩,
⟨145,0x14a016d21d00a3a8ed1dd1fc0077b8f⟩]
private def T9c : Array Nat := #[0x0,0x0,0x202097010125c0092e122e4b85df7,0x5e5e7ff2f4fffc97ffefeffffbffff,0x1ffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffff]
private abbrev T9b : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
private def T9q : List Nat := [840,1556,788,1172,1548,780,2370,2210,2146,330,106,270,2369,833,2209,1185,2145,1553,2321,785,2193,1169]
private def T9k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T9checked : trioTest T9a T9f T9c 7 (fun x y z=>decide ([x,y,z]∈T9k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T9valid : trioValidated T9b T9a T9q T9f T9c 7=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T9close : T9k.all (fun cs=>decide (norm2 (attach cs T9b)∈atlas))=true := by decide +kernel
private theorem B3_9ok {cs : List Nat} (ex : Extension 6 3 T9b cs) (he : edges_ (attach cs T9b)≤33) : norm2 (attach cs T9b)∈atlas :=
  triExtension norm2 atlas T9b T9a T9q T9f T9c 7 T9k (by decide +kernel) T9valid T9checked T9close ex he
private def T10a : List TrioAtom := [⟨6,2,0xfe00f,0xfff800003ffff,0x4218080000000000000000⟩,
⟨10,2,0xfe031,0xfff8000fc07ff,0x2d080005a400000000016202000⟩,
⟨12,2,0xfe001,0xfff807c0007ff,0x2d080425a484000000016202000⟩,
⟨14,3,0xfe001,0xfff80000007ff,0x2d080425a484000000016202000⟩,
⟨18,2,0xfe016,0xfff80013cf87f,0x200c0200018000000000006000000⟩,
⟨20,2,0xfe046,0xfff819c00f87f,0x200000042000010900a0000000000⟩,
⟨22,3,0xfe006,0xfff800000f87f,0x200c02042180810900a0006000800⟩,
⟨24,2,0xfe310,0xfff9c1c3c007f,0x212d0a10000000000000000000000⟩,
⟨26,3,0xfe010,0xfff80003c007f,0x212d0a1005a400000000016202000⟩,
⟨28,3,0xfe000,0xfff801c00007f,0x212d0a1425a4850900a0116202800⟩,
⟨30,4,0xfe000,0xfff800000007f,0x212d0a1425a4850900a0116202800⟩,
⟨33,2,0x1ff9,0x7fffff1f83,0x140000⟩,
⟨40,2,0x6731,0x7fbc7cfc0783,0x727c000000000000000a15dc000⟩,
⟨65,2,0x19ce,0x6faf4ff9fc,0x270554f000000000⟩,
⟨66,2,0xf800e,0xf8f80034ff9fc,0xe2181c38b80c0000000000⟩,
⟨68,2,0xf80ce,0xf8f83ac03f9fc,0xe2001038b80c0000000000⟩,
⟨70,3,0xf800e,0xf8f800003f9fc,0xe2181c38b80c0000000000⟩,
⟨80,2,0xf8946,0xf8fcd8d0cf87c,0x30000000000003880070000000000⟩,
⟨82,3,0xf8006,0xf8f80010cf87c,0x300c030e2181c38b80f0006000000⟩,
⟨84,3,0xf8046,0xf8f818c00f87c,0x3000000e2001038b80f0000000000⟩,
⟨86,4,0xf8006,0xf8f800000f87c,0x300c030e2181c38b80f0006000000⟩,
⟨129,2,0x1fce,0x7fff97fa9c,0x50550e000000000⟩,
⟨132,2,0x380ce,0x7b383fc03fa9c,0xe200103ff80c0000000000⟩,
⟨144,2,0x38b46,0x7b3dd9d14f81c,0x30000000000000500000000000000⟩,
⟨148,3,0x38046,0x7b3819c00f81c,0x3000000e200103ff80f0000000000⟩,
⟨160,2,0x1fc8,0x33ffff971a80,0x50550e000000000⟩,
⟨161,3,0x1fc8,0x7fff971a80,0x50550e000000000⟩,
⟨192,2,0x399ce,0x783efaf07f89c,0x2700040000000000⟩,
⟨193,3,0x19ce,0x6faf07f89c,0x270554f000000000⟩,
⟨196,3,0x380ce,0x78383ac03f89c,0xe200103ff80c0000000000⟩,
⟨208,3,0x38946,0x783cd8d04f81c,0x30000000000003fc0070000000000⟩,
⟨212,4,0x38046,0x783818c00f81c,0x3000000e200103ff80f0000000000⟩,
⟨257,2,0x16bb,0x76f2fb6fe7,0x80800000000000000000⟩,
⟨258,2,0xce03b,0xbfc8002fb6fe7,0xff400000000000000000⟩,
⟨260,2,0xce08b,0xbfc82f0036fe7,0x4284000000000000000000⟩,
⟨262,3,0xce00b,0xbfc8000036fe7,0x42ff484000000000000000⟩,
⟨264,2,0xce631,0xbfcb470f807e7,0x2008000e0400000000000000000⟩,
⟨266,3,0xce031,0xbfc8000f807e7,0x2d08000ff400000000000000000⟩,
⟨268,3,0xce001,0xbfc80700007e7,0x2d08042ff484000000000000000⟩,
⟨270,4,0xce001,0xbfc80000007e7,0x2d08042ff484000000000000000⟩,
⟨288,2,0x76b9,0x7cf6f2fb0f83,0x80800000000000000000⟩,
⟨289,3,0x16b9,0x76f2fb0f83,0x80800000000000000000⟩,
⟨296,3,0x6631,0x7cb470f80783,0x727c000e0e00000000000000000⟩,
⟨513,2,0x1f31,0x7f57fda76b,0x427000000000000000000000000⟩,
⟨514,2,0xd6031,0xdfd0003fda76b,0x7f880005a400000000000000000⟩,
⟨520,2,0xd6731,0xdfd3c54fc076b,0x720800000000000000000000000⟩,
⟨522,3,0xd6031,0xdfd0000fc076b,0x7f880005a400000000000000000⟩,
⟨528,2,0xd6b10,0xdfd5d153ca06b,0x21420000000000000000000000000⟩,
⟨530,3,0xd6010,0xdfd00013ca06b,0x217f8a1005a400000000000000000⟩,
⟨536,3,0xd6310,0xdfd1c143c006b,0x217f8a10000000000000000000000⟩,
⟨538,4,0xd6010,0xdfd00003c006b,0x217f8a1005a400000000000000000⟩,
⟨544,2,0x7f31,0x7d7f57fd0703,0x427000000000000000000000000⟩,
⟨545,3,0x1f31,0x7f57fd0703,0x427000000000000000000000000⟩,
⟨552,3,0x6731,0x7d3c54fc0703,0x727c00000000000000000000000⟩,
⟨768,2,0xc7631,0x9fc7652f92763,0x420000080000000000000000000⟩,
⟨769,3,0x1631,0x7652f92763,0x427000080800000000000000000⟩,
⟨770,3,0xc6031,0x9fc0002f92763,0x7f88000ff400000000000000000⟩,
⟨776,3,0xc6631,0x9fc3450f80763,0x7208000e0400000000000000000⟩,
⟨778,4,0xc6031,0x9fc0000f80763,0x7f88000ff400000000000000000⟩,
⟨800,3,0x7631,0x7c7652f90703,0x427000080800000000000000000⟩,
⟨801,4,0x1631,0x7652f90703,0x427000080800000000000000000⟩,
⟨808,4,0x6631,0x7c3450f80703,0x727c000e0e00000000000000000⟩,
⟨1025,2,0x1ff4,0x7ffffed439,0x8000000000000000000000000000⟩,
⟨1032,2,0x72730,0xed73c7cfc0439,0xc200800000000000000000000000⟩,
⟨1040,2,0x72b54,0xed75d9d3cd039,0x3f800000000000000000000000000⟩,
⟨1048,3,0x72310,0xed71c1c3c0039,0x3fad0b10000000000000000000000⟩,
⟨1056,2,0x3ff0,0x577ffffe1401,0x8005080000000000000000000000⟩,
⟨1057,3,0x1ff0,0x7ffffe1401,0x8005080000000000000000000000⟩,
⟨1064,3,0x2730,0x573c7cfc0401,0xc727cc0000000000000000000000⟩,
⟨1088,2,0x719c4,0xe876faf4ed038,0xa000000000000000000000000000⟩,
⟨1089,3,0x19c4,0x6faf4ed038,0xa000000000000000000000000000⟩,
⟨1104,3,0x70944,0xe874d8d0cd038,0x3f800000000000000000000000000⟩,
⟨1152,2,0x31fc4,0x6937fff96d018,0xa000000000000000000000000000⟩,
⟨1153,3,0x1fc4,0x7fff96d018,0xa000000000000000000000000000⟩,
⟨1168,3,0x30b44,0x6935d9d14d018,0x3f800000000000000000000000000⟩,
⟨1184,3,0x1fc0,0x137fff961000,0xa0050a0000000000000000000000⟩,
⟨1185,4,0x1fc0,0x7fff961000,0xa0050a0000000000000000000000⟩,
⟨1216,3,0x319c4,0x6836faf06d018,0xa000000000000000000000000000⟩,
⟨1217,4,0x19c4,0x6faf06d018,0xa000000000000000000000000000⟩,
⟨1232,4,0x30944,0x6834d8d04d018,0x3f800000000000000000000000000⟩,
⟨1536,2,0x53f30,0xcd57f57fc8429,0xc4270c0000000000000000000000⟩,
⟨1537,3,0x1f30,0x7f57fc8429,0xc4270c0000000000000000000000⟩,
⟨1544,3,0x52730,0xcd53c54fc0429,0xc727cc0000000000000000000000⟩,
⟨1552,3,0x52b10,0xcd55d153c8029,0x3fc270e0000000000000000000000⟩,
⟨1560,4,0x52310,0xcd51c143c0029,0x3ffffff0000000000000000000000⟩,
⟨1568,3,0x3f30,0x557f57fc0401,0xc4270c0000000000000000000000⟩,
⟨1569,4,0x1f30,0x7f57fc0401,0xc4270c0000000000000000000000⟩,
⟨1576,4,0x2730,0x553c54fc0401,0xc727cc0000000000000000000000⟩,
⟨2049,2,0x1cef,0x7bebe3ffd6,0x0⟩,
⟨2050,2,0xac02f,0xf6a8003e3ffd6,0x0⟩,
⟨2052,2,0xac0cf,0xf6a83e803ffd6,0x0⟩,
⟨2054,3,0xac00f,0xf6a800003ffd6,0x0⟩,
⟨2080,2,0x5ce9,0x6afbebe31f82,0x0⟩,
⟨2081,3,0x1ce9,0x7bebe31f82,0x0⟩,
⟨2112,2,0xa98ce,0xf0aebab43f9d4,0x0⟩,
⟨2113,3,0x18ce,0x6bab43f9d4,0x0⟩,
⟨2114,3,0xa800e,0xf0a800343f9d4,0x0⟩,
⟨2116,3,0xa80ce,0xf0a83a803f9d4,0x0⟩,
⟨2118,4,0xa800e,0xf0a800003f9d4,0x0⟩,
⟨2176,2,0x29cce,0x722fbeb83fa94,0x0⟩,
⟨2177,3,0x1cce,0x7beb83fa94,0x0⟩,
⟨2180,3,0x280ce,0x72283e803fa94,0x0⟩,
⟨2208,3,0x1cc8,0x22fbeb831a80,0x0⟩,
⟨2209,4,0x1cc8,0x7beb831a80,0x0⟩,
⟨2240,3,0x298ce,0x702ebab03f894,0x0⟩,
⟨2241,4,0x18ce,0x6bab03f894,0x0⟩,
⟨2244,4,0x280ce,0x70283a803f894,0x0⟩,
⟨2304,2,0x8d4ab,0xb68f2e2e36fc6,0x0⟩,
⟨2305,3,0x14ab,0x72e2e36fc6,0x0⟩,
⟨2306,3,0x8c02b,0xb688002e36fc6,0x0⟩,
⟨2308,3,0x8c08b,0xb6882e0036fc6,0x0⟩,
⟨2310,4,0x8c00b,0xb688000036fc6,0x0⟩,
⟨2336,3,0x54a9,0x68f2e2e30f82,0x0⟩,
⟨2337,4,0x14a9,0x72e2e30f82,0x0⟩]
private def T10f : Array TriFeature := #[⟨2240,0xff001fffffffff00001fff⟩,
⟨1216,0x3f8003f0000003fffffff00001fff⟩,
⟨1568,0xff3fcf000000000000fff9ffe7ff⟩,
⟨2336,0x1fe7e3c007f800f9ffe7ff⟩,
⟨800,0x73fcf00e7e3c0000000f9ffe7ff⟩,
⟨2208,0x1f00e3c7c7f8ff001fe7ff⟩,
⟨1184,0xf807cf00000007c7f8ff001fe7ff⟩,
⟨1552,0x3ffffff000000000007ff3e61f80f⟩,
⟨1168,0x3f807ff0000003ff87fff0001f80f⟩,
⟨1104,0x3f8f83f0000003ff87fff0660180f⟩,
⟨208,0x3f8003fe7001cfff87fff0000180f⟩,
⟨1544,0x3ffffff0000000000030fffffe871⟩,
⟨776,0x7ffff00ffed40000000ffffe871⟩,
⟨1064,0xff3fcf00000001c1980ff9ffe071⟩,
⟨552,0xff3fcf00e7e14000000ff9ffe071⟩,
⟨296,0x73fcf0be7e140019800f9ffe071⟩,
⟨1048,0x3ffffff00000019d81b0f3e61e801⟩,
⟨536,0x3ffffff007b6c4000030f3e61e801⟩,
⟨2308,0xffffffc03ff8005ea67992⟩,
⟨2180,0xff00ffffffff3300067992⟩,
⟨2116,0xff1f1fffffff3306a01992⟩,
⟨196,0x3380033ff001fffffff3300001992⟩,
⟨148,0x33801f3e7007cfff87f3300007802⟩,
⟨84,0x338d833e71b1cfff87f3306201802⟩,
⟨268,0x3d9f36bffed401998005ea66810⟩,
⟨28,0x33bd9f3637b6c59d81b031e206800⟩,
⟨2306,0xffffffc03aa800ffeabaa4⟩,
⟨770,0x7faf500ffffc0000000ffeabaa4⟩,
⟨2114,0xff1f1ffafaaf5507e01aa4⟩,
⟨530,0x35ffaf5007b7cc00007553e60b804⟩,
⟨82,0x358f835e71b1cfaf82f5506601804⟩,
⟨522,0x35ffaf500ffed40000305ffeaa820⟩,
⟨266,0x7faf56bffed40188800ffeaa820⟩,
⟨26,0x35ffaf5637b6c58d80b053e60a800⟩,
⟨2054,0xfffffffafaaf115ea23880⟩,
⟨262,0x3d8f1ffffffc03aa8005ea23880⟩,
⟨70,0x318d831ff1f1ffafaaf1106a01880⟩,
⟨22,0x31bd8f1e77b7cfaf82f111e203800⟩,
⟨14,0x31bd8f16bffed58d88b015ea22800⟩,
⟨1537,0x1ed6f5e000000000005feebdfd7ff⟩,
⟨2305,0xbdadb7802ff000ebdfd7ff⟩,
⟨769,0x56f5e00adb780000000ebdfd7ff⟩,
⟨2177,0xbd00b7af6ff5fe001fd7ff⟩,
⟨1153,0x1e8075e0000002f6ff5fe001fd7ff⟩,
⟨2113,0xbd0d17af6ff5fe03c017ff⟩,
⟨1089,0x1e8681e0000002f6ff5fe03c017ff⟩,
⟨193,0x1e8001ebd0017af6ff5fe000017ff⟩,
⟨2081,0x1da5a38747f0fee9dfc7ff⟩,
⟨1057,0xed2f4e0000000747f0fee9dfc7ff⟩,
⟨545,0xed2f4e00a5a3800000fee9dfc7ff⟩,
⟨289,0x52f4e1da5a38007f000e9dfc7ff⟩,
⟨161,0xe8074e1d00a38747f0fe001fc7ff⟩]
private def T10c : Array Nat := #[0x0,0x0,0x80857010125c048b9170ae2f8b7,0x1797bff2f2fffcbfbff7f7feffbff,0x3ffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffff]
private abbrev T10b : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
private def T10q : List Nat := [1232,1576,808,1560,2244,212,778,538,2310,2118,86,270,30,2241,1217,1569,2337,801,2209,1185]
private def T10k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T10checked : trioTest T10a T10f T10c 6 (fun x y z=>decide ([x,y,z]∈T10k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T10valid : trioValidated T10b T10a T10q T10f T10c 6=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T10close : T10k.all (fun cs=>decide (norm2 (attach cs T10b)∈atlas))=true := by decide +kernel
private theorem B3_10ok {cs : List Nat} (ex : Extension 6 3 T10b cs) (he : edges_ (attach cs T10b)≤33) : norm2 (attach cs T10b)∈atlas :=
  triExtension norm2 atlas T10b T10a T10q T10f T10c 6 T10k (by decide +kernel) T10valid T10checked T10close ex he
private def T11a : List TrioAtom := [⟨6,2,0x3f007,0xfff800001ffff,0x3492121000100000000000⟩,
⟨10,2,0x3f00b,0xfff80007e07ff,0x68000092100000121000000000⟩,
⟨12,2,0x3f0c3,0xfff80fc0007ff,0x68003400000000000000000000⟩,
⟨14,3,0x3f003,0xfff80000007ff,0x68003492121000121000000000⟩,
⟨18,2,0x3f010,0xfff80019e783f,0x4000400080100100100100808000⟩,
⟨20,2,0x3f1c0,0xfff837c00783f,0x4900403400000121000000000000⟩,
⟨22,3,0x3f000,0xfff800000783f,0x4968487492121121121100808800⟩,
⟨24,2,0x3f2c0,0xfff987c1e003f,0x4968484000000100000000000000⟩,
⟨26,3,0x3f000,0xfff80001e003f,0x4968487492121121121100808800⟩,
⟨28,3,0x3f0c0,0xfff807c00003f,0x4968487400000121000000000000⟩,
⟨30,4,0x3f000,0xfff800000003f,0x4968487492121121121100808800⟩,
⟨33,2,0xf7d,0x7f1ffff9c3,0xe00000000⟩,
⟨34,2,0x303d,0xff8003fff9c3,0x80100000100f80800000⟩,
⟨48,2,0x3750,0xffdb1d9e7803,0x4000400000000100000f80008000⟩,
⟨50,3,0x3010,0xff80019e7803,0x4010400880100100100f80808000⟩,
⟨65,2,0x8af,0x6de6e79ffd,0x20040000040000000000⟩,
⟨66,2,0x3d02f,0xf1f8002e79ffd,0xa0140000140000000000⟩,
⟨68,2,0x3d087,0xf1f85e4019ffd,0x3438070000040000000000⟩,
⟨70,3,0x3d007,0xf1f8000019ffd,0x34ba171000140000000000⟩,
⟨72,2,0x3d08b,0xf1fa8e46607fd,0x68000038040000070000000000⟩,
⟨74,3,0x3d00b,0xf1f80006607fd,0x680000ba140000171000000000⟩,
⟨76,3,0x3d083,0xf1f80e40007fd,0x68003438070000070000000000⟩,
⟨78,4,0x3d003,0xf1f80000007fd,0x680034ba171000171000000000⟩,
⟨129,2,0xfc2,0x7fff2aae7e,0x1000100000000040000000000000⟩,
⟨132,2,0x3e1c2,0xf6787fc00ae7e,0x1c00103400000070000000000000⟩,
⟨136,2,0x3e2c2,0xf67b8fc2a067e,0x1c681c0000000040000000000000⟩,
⟨140,3,0x3e0c2,0xf6780fc00067e,0x1c681c3400000070000000000000⟩,
⟨144,2,0x3e7c0,0xf67db7d0a283e,0x5000500000000140000000000000⟩,
⟨148,3,0x3e1c0,0xf67837c00283e,0x5d00503400000171000000000000⟩,
⟨152,3,0x3e2c0,0xf67987c0a003e,0x5d685c4000000140000000000000⟩,
⟨156,4,0x3e0c0,0xf67807c00003e,0x5d685c7400000171000000000000⟩,
⟨192,2,0x3c882,0xf07ede6228e7c,0x1000100020040040040000000000⟩,
⟨193,3,0x882,0x6de6228e7c,0x1010100820040040040000000000⟩,
⟨196,3,0x3c082,0xf0785e4008e7c,0x1c681c3438070070070000000000⟩,
⟨200,3,0x3c082,0xf07a8e422067c,0x1c681c3438070070070000000000⟩,
⟨204,4,0x3c082,0xf0780e400067c,0x1c681c3438070070070000000000⟩,
⟨257,2,0xff4,0x7fffd9fa8e,0xc08000000000000⟩,
⟨260,2,0xe1c4,0x7e987fc01fa8e,0x3e00000c0c000000000000⟩,
⟨272,2,0xe7d0,0x7e9db7d98780e,0xe000400000000f88000000000000⟩,
⟨276,3,0xe1c0,0x7e9837c00780e,0xff80503e00000fff000000000000⟩,
⟨288,2,0x2f74,0xe9ff1fd9f882,0xc08000000000000⟩,
⟨289,3,0xf74,0x7f1fd9f882,0xc08000000000000⟩,
⟨304,3,0x2750,0xe9db1d987802,0xe003e20000000f88000000000000⟩,
⟨384,2,0xefc0,0x761ffff08aa0e,0x9200100000000e4a000000000000⟩,
⟨385,3,0xfc0,0x7fff08aa0e,0x9203928000000e4a000000000000⟩,
⟨388,3,0xe1c0,0x76187fc00aa0e,0xff80503e00000fff000000000000⟩,
⟨400,3,0xe7c0,0x761db7d08280e,0xf200500000000fca000000000000⟩,
⟨404,4,0xe1c0,0x761837c00280e,0xff80503e00000fff000000000000⟩,
⟨513,2,0xe3f,0x7eabffd7f1,0x0⟩,
⟨514,2,0x3103f,0xbbe0003ffd7f1,0x1c0100000000000000000⟩,
⟨520,2,0x3120b,0xbbe38a87e07f1,0x7c000000000000000000000000⟩,
⟨522,3,0x3100b,0xbbe00007e07f1,0x7c0001ff140000000000000000⟩,
⟨544,2,0x1e3d,0xbe7e0bffd1c1,0x0⟩,
⟨545,3,0xe3d,0x7e0bffd1c1,0x0⟩,
⟨546,3,0x103d,0xbe0003ffd1c1,0x1c0f88000000000000000⟩,
⟨576,2,0x3182f,0xb1e6ca2e797f1,0x124040000000000000000⟩,
⟨577,3,0x82f,0x6ca2e797f1,0x124e4c000000000000000⟩,
⟨578,3,0x3102f,0xb1e0002e797f1,0x1e4140000000000000000⟩,
⟨584,3,0x3100b,0xb1e28a06607f1,0x7c0001ff140000000000000000⟩,
⟨586,4,0x3100b,0xb1e00006607f1,0x7c0001ff140000000000000000⟩,
⟨1025,2,0xff8,0x7fffff6516,0x3020000000000000000000000⟩,
⟨1032,2,0x162c8,0xdf2b8fc7e0516,0x7f030000000000000000000000⟩,
⟨1040,2,0x167d0,0xdf2db7d9e6016,0xe003e20000000000000000000000⟩,
⟨1048,3,0x162c0,0xdf2987c1e0016,0xffffffc000000000000000000000⟩,
⟨1056,2,0x2f78,0xf2ff1fff6102,0x3020000000000000000000000⟩,
⟨1057,3,0xf78,0x7f1fff6102,0x3020000000000000000000000⟩,
⟨1072,3,0x2750,0xf2db1d9e6002,0xe003e20000000000000000000000⟩,
⟨1152,2,0x16fc0,0xd62ffff2a2416,0x9203928000000000000000000000⟩,
⟨1153,3,0xfc0,0x7fff2a2416,0x9203928000000000000000000000⟩,
⟨1160,3,0x162c0,0xd62b8fc2a0416,0xffffffc000000000000000000000⟩,
⟨1168,3,0x167c0,0xd62db7d0a2016,0xf203f28000000000000000000000⟩,
⟨1176,4,0x162c0,0xd62987c0a0016,0xffffffc000000000000000000000⟩,
⟨1280,2,0x6ff0,0x5e0ffffd96006,0x3020000000000000000000000⟩,
⟨1281,3,0xff0,0x7fffd96006,0x3020000000000000000000000⟩,
⟨1296,3,0x67d0,0x5e0db7d986006,0xe003e20000000000000000000000⟩,
⟨1312,3,0x2f70,0xe0ff1fd96002,0x3020000000000000000000000⟩,
⟨1313,4,0xf70,0x7f1fd96002,0x3020000000000000000000000⟩,
⟨1328,4,0x2750,0xe0db1d986002,0xe003e20000000000000000000000⟩,
⟨1408,3,0x6fc0,0x560ffff082006,0x9203928000000000000000000000⟩,
⟨1409,4,0xfc0,0x7fff082006,0x9203928000000000000000000000⟩,
⟨1424,4,0x67c0,0x560db7d082006,0xf203f28000000000000000000000⟩,
⟨1536,2,0x10e38,0x9b27eabff4510,0x13030000000000000000000000⟩,
⟨1537,3,0xe38,0x7eabff4510,0x13030000000000000000000000⟩,
⟨1544,3,0x10208,0x9b238a87e0510,0x7f030000000000000000000000⟩,
⟨1568,3,0xe38,0xb27e0bff4100,0x13030000000000000000000000⟩,
⟨1569,4,0xe38,0x7e0bff4100,0x13030000000000000000000000⟩,
⟨2049,2,0xd3f,0x77d3f5ffe9,0x0⟩,
⟨2050,2,0x2903f,0xedd0003f5ffe9,0x0⟩,
⟨2052,2,0x29107,0xedd07d001ffe9,0x0⟩,
⟨2054,3,0x29007,0xedd000001ffe9,0x0⟩,
⟨2080,2,0x1d3d,0xdd7713f5f9c1,0x0⟩,
⟨2081,3,0xd3d,0x7713f5f9c1,0x0⟩,
⟨2082,3,0x103d,0xdd0003f5f9c1,0x0⟩,
⟨2112,2,0x2982f,0xe1d65c2e59fe9,0x0⟩,
⟨2113,3,0x82f,0x65c2e59fe9,0x0⟩,
⟨2114,3,0x2902f,0xe1d0002e59fe9,0x0⟩,
⟨2116,3,0x29007,0xe1d05c0019fe9,0x0⟩,
⟨2118,4,0x29007,0xe1d0000019fe9,0x0⟩,
⟨2304,2,0x8d34,0x6c977d3d1fa88,0x0⟩,
⟨2305,3,0xd34,0x77d3d1fa88,0x0⟩,
⟨2308,3,0x8104,0x6c907d001fa88,0x0⟩,
⟨2336,3,0xd34,0xc97713d1f880,0x0⟩,
⟨2337,4,0xd34,0x7713d1f880,0x0⟩,
⟨2560,2,0x21c3f,0xa9c7683f5d7e1,0x0⟩,
⟨2561,3,0xc3f,0x7683f5d7e1,0x0⟩,
⟨2562,3,0x2103f,0xa9c0003f5d7e1,0x0⟩,
⟨2592,3,0x1c3d,0x9c7603f5d1c1,0x0⟩,
⟨2593,4,0xc3d,0x7603f5d1c1,0x0⟩,
⟨2594,4,0x103d,0x9c0003f5d1c1,0x0⟩,
⟨2624,3,0x2182f,0xa1c6482e597e1,0x0⟩,
⟨2625,4,0x82f,0x6482e597e1,0x0⟩,
⟨2626,4,0x2102f,0xa1c0002e597e1,0x0⟩]
private def T11f : Array TriFeature := #[⟨1408,0xff83ffc000000fff0000007fffff⟩,
⟨2624,0x1fffff000fff07f807fff⟩,
⟨2592,0x1c7f8f000f8ffffff87ff⟩,
⟨1568,0x1fe3c000000000f8ffffff87ff⟩,
⟨2336,0xe00f8ff8f000fffff87ff⟩,
⟨1312,0xe383e3c000000f8f000fffff87ff⟩,
⟨1296,0xff83ffc000000fff000f87ff980f⟩,
⟨1168,0xffffffc000000fff0330007f980f⟩,
⟨400,0xff83fffe00033fff0000007f980f⟩,
⟨1072,0xe39fe3c000000f8f383f87ff800f⟩,
⟨304,0xe383e3ce00383f8f000f87ff800f⟩,
⟨1544,0x7fffc000000000fff39987f871⟩,
⟨1160,0xffffffc0000003f307f00007f871⟩,
⟨584,0x7c1fc1ff5f5000fff019807871⟩,
⟨200,0x1ffc1ff63f07507307f000007871⟩,
⟨1048,0xffffffc0000003f33b3381879801⟩,
⟨152,0xfffffff61b0313f3033000079801⟩,
⟨2308,0x3e00ffffff0005aa99f992⟩,
⟨388,0xff80fcfe0007ffff00000019f992⟩,
⟨2116,0x3ffffff07f5f502a807992⟩,
⟨196,0x1fec1cfe3f07f07f075000007992⟩,
⟨276,0xff80fcfe003b3fff000582999802⟩,
⟨148,0xffecfcfe1b033fff031000199802⟩,
⟨140,0xffecfcf63f0753f307500001f810⟩,
⟨76,0x1fec1cf7ff5f50735f5008807810⟩,
⟨28,0xffecfcf6db1b13f31b1180819800⟩,
⟨2562,0x1fffff000ffffffaaaaa4⟩,
⟨2114,0x3ffffff035fff07f802aa4⟩,
⟨578,0x7c0d41fffff000fff07f802aa4⟩,
⟨2082,0xfc7f8f585f8ffffaa82a4⟩,
⟨546,0x1d6141c7f8f000f8ffffaa82a4⟩,
⟨50,0x619d614ec3383585383f87aa8004⟩,
⟨522,0x7d6d41ff5f5000fff39982a820⟩,
⟨74,0xdfc0d77ff5f5031fff019802820⟩,
⟨26,0x6dfd6d76db1b11b13b3381828800⟩,
⟨2054,0x3ffffff5b55f55aa88a880⟩,
⟨70,0xdec0c7ffffff0355f502a802880⟩,
⟨22,0x6dec6c7edb3b35b51b1582888800⟩,
⟨14,0x6dec6c77ff5f51b15f518880a800⟩,
⟨2561,0x16dede000edeeff7f77ff⟩,
⟨1537,0x37b78000000000edeeff7f77ff⟩,
⟨2305,0x1a00edeede000eff7f77ff⟩,
⟨1281,0xb683b78000000ede000eff7f77ff⟩,
⟨1153,0xb6b7b78000000ede05e0007f77ff⟩,
⟨385,0xb683b79a0005eede0000007f77ff⟩,
⟨2113,0x1b6dede05eede07f0077ff⟩,
⟨577,0x3417816dede000ede07f0077ff⟩,
⟨193,0x16b4179a2d05e05e05e0000077ff⟩,
⟨2081,0xb45e8ee8ee8eeff7f07ff⟩,
⟨1057,0xa297a38000000e8ee8eeff7f07ff⟩,
⟨545,0x17a38145e8e000e8eeff7f07ff⟩,
⟨289,0xa283a38a00e8ee8e000eff7f07ff⟩]
private def T11c : Array Nat := #[0x0,0x0,0x8425c20109709709708b8bb8b7,0x27bdffde4f7ff7ff7ff7bfbffbff,0xffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffff]
private abbrev T11b : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]
private def T11q : List Nat := [1424,1328,1176,404,204,156,2626,2594,586,2118,78,30,1409,2625,2593,1569,2337,1313]
private def T11k : List (List Nat) := []
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T11checked : trioTest T11a T11f T11c 6 (fun x y z=>decide ([x,y,z]∈T11k))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T11valid : trioValidated T11b T11a T11q T11f T11c 6=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem T11close : T11k.all (fun cs=>decide (norm2 (attach cs T11b)∈atlas))=true := by decide +kernel
private theorem B3_11ok {cs : List Nat} (ex : Extension 6 3 T11b cs) (he : edges_ (attach cs T11b)≤33) : norm2 (attach cs T11b)∈atlas :=
  triExtension norm2 atlas T11b T11a T11q T11f T11c 6 T11k (by decide +kernel) T11valid T11checked T11close ex he
private def viable0 : List (List Nat) := []
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem allsmall0 : (levels norm2 5 15 4).all (fun b=> decide (33 < edges_ b+0*(0-1)+0 ∨ b∈viable0)) = true := by decide +kernel


private theorem bybase0 {b g : List Nat} (hb : b∈levels norm2 5 15 4) (hg : g∈grow 6 0 b) (he : edges_ g≤33) : norm2 g∈atlas := by
  have h := of_decide_eq_true (List.all_eq_true.mp allsmall0 b hb)
  have allowed := h.resolve_left (Nat.not_lt.mpr (parent_low hg he))
  simp [viable0] at allowed


private def viable1 : List (List Nat) := []
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem allsmall1 : (levels norm2 5 14 4).all (fun b=> decide (33 < edges_ b+1*(1-1)+1 ∨ b∈viable1)) = true := by decide +kernel


private theorem bybase1 {b g : List Nat} (hb : b∈levels norm2 5 14 4) (hg : g∈grow 6 1 b) (he : edges_ g≤33) : norm2 g∈atlas := by
  have h := of_decide_eq_true (List.all_eq_true.mp allsmall1 b hb)
  have allowed := h.resolve_left (Nat.not_lt.mpr (parent_low hg he))
  simp [viable1] at allowed


private def viable2 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem allsmall2 : (levels norm2 5 13 4).all (fun b=> decide (33 < edges_ b+2*(2-1)+2 ∨ b∈viable2)) = true := by decide +kernel


private theorem bybase2 {b g : List Nat} (hb : b∈levels norm2 5 13 4) (hg : g∈grow 6 2 b) (he : edges_ g≤33) : norm2 g∈atlas := by
  have h := of_decide_eq_true (List.all_eq_true.mp allsmall2 b hb)
  have allowed := h.resolve_left (Nat.not_lt.mpr (parent_low hg he))
  simp only [viable2,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl
  · exact B2_0ok hg he


private def viable3 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],[7,24,146,145,3,2,6,3,2,2,1,0],[7,24,194,145,3,2,6,3,2,2,1,0],[7,280,146,145,3,2,6,3,2,2,1,0],[7,280,194,137,3,2,6,3,2,2,1,0],[7,24,98,137,3,12,9,3,2,2,1,0],[7,132,268,137,3,12,9,3,2,2,1,0],[7,196,268,137,3,12,9,3,2,2,1,0],[7,388,258,134,3,12,9,3,2,2,1,0],[7,388,268,137,3,12,9,3,2,2,1,0],[15,296,196,140,73,1,6,3,2,2,1,0],[15,352,196,146,82,3,10,10,1,0,1,0]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem allsmall3 : (levels norm2 5 12 4).all (fun b=> decide (33 < edges_ b+3*(3-1)+3 ∨ b∈viable3)) = true := by decide +kernel


private theorem bybase3 {b cs : List Nat} (hb : b∈levels norm2 5 12 4) (ex : Extension 6 3 b cs) (hg : attach cs b∈grow 6 3 b) (he : edges_ (attach cs b)≤33) : norm2 (attach cs b)∈atlas := by
  have h := of_decide_eq_true (List.all_eq_true.mp allsmall3 b hb)
  have allowed := h.resolve_left (Nat.not_lt.mpr (parent_low hg he))
  simp only [viable3,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact B3_0ok ex he
  · exact B3_1ok ex he
  · exact B3_2ok ex he
  · exact B3_3ok ex he
  · exact B3_4ok ex he
  · exact B3_5ok ex he
  · exact B3_6ok ex he
  · exact B3_7ok ex he
  · exact B3_8ok ex he
  · exact B3_9ok ex he
  · exact B3_10ok ex he
  · exact B3_11ok ex he


private theorem classify16 (d : Nat) (hd : d≤3) (b : List Nat) (hb : b∈levels norm2 5 (15-d) 4)
    (cs : List Nat) (ex : Extension 6 d b cs) (hg : attach cs b∈grow 6 d b) (he : edges_ (attach cs b)≤33) :
    norm2 (attach cs b)∈atlas := by
  interval_cases d
  · exact bybase0 hb hg he
  · exact bybase1 hb hg he
  · exact bybase2 hb hg he
  · exact bybase3 hb ex hg he
private abbrev Top0 : List Nat := [3,2,30,15,560,388,274,146,3,2,6,3,2,2,1,0]
private def Top0w : List (Nat × Nat) := [(35852,1),(19468,1),(25100,1),(37388,1),(12812,1),(34316,1),(17932,1),(24844,1),(37132,1),(12556,1),(35084,1),(18700,1),(24770,1),(17602,1),(3234,1),(4706,1),(1634,1),(8594,1),(2450,1),(12370,1),(36914,1),(34866,1),(242,3),(24769,1),(17601,1),(3233,1),(4705,1),(1633,1),(8593,1),(2449,1),(12369,1),(36913,1),(34865,1),(241,3)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top0ok : weightCheck Top0 Top0w 7=true := by
  have f : fives Top0 = [35852,19468,25100,37388,12812,34316,17932,24844,37132,12556,35084,18700,19586,24962,18818,25154,12866,17986,24770,17602,35874,37410,34338,3234,4706,1634,1250,37138,12562,35090,8594,2450,12370,8402,36914,34866,2226,4210,242,35846,19462,25094,37382,12806,34310,17926,24838,37126,12550,35078,18694,19585,24961,18817,25153,12865,17985,24769,17601,35873,37409,34337,3233,4705,1633,1249,37137,12561,35089,8593,2449,12369,8401,36913,34865,2225,4209,241,35849,19465,25097,37385,12809,34313,17929,24841,37129,12553,35081,18697] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top1 : List Nat := [3,12,2113,15,560,388,274,146,3,2,6,3,2,2,1,0]
private def Top1w : List (Nat × Nat) := [(35876,2),(3236,19),(1252,32),(12564,30),(8596,4),(2452,22),(8404,7),(36916,19),(4212,14),(19586,7),(12866,26),(17986,26),(37386,51),(12810,7),(34314,15),(17930,7),(24842,7),(35082,14),(18698,12),(35846,31),(12550,11),(3206,7),(8582,14),(2438,18),(8390,26),(1222,8),(25153,26),(37409,24),(3233,24),(12561,2),(8401,24),(34865,55),(4209,29),(19465,10),(25097,37),(12809,14),(34313,32),(17929,11)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top1ok : weightCheck Top1 Top1w 132=true := by
  have f : fives Top1 = [35876,3236,1252,37140,12564,35092,8596,2452,12372,8404,36916,34868,2228,4212,244,19586,24962,18818,25154,12866,17986,24770,17602,35850,19466,25098,37386,12810,34314,17930,24842,37130,12554,35082,18698,35846,37126,12550,35078,3206,8582,2438,12358,8390,1222,19585,24961,18817,25153,12865,17985,24769,17601,35873,37409,34337,3233,4705,1633,1249,37137,12561,35089,8593,2449,12369,8401,36913,34865,2225,4209,241,35849,19465,25097,37385,12809,34313,17929,24841,37129,12553,35081,18697] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top2 : List Nat := [7,56,258,801,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top2w : List (Nat × Nat) := [(19592,5),(35912,5),(3272,4),(18600,14),(34920,14),(2280,2),(12868,8),(8900,9),(12388,9),(1228,10),(236,7),(35858,9),(19474,9),(25106,14),(37394,14),(12818,2),(24850,13),(37138,5),(12562,4),(18706,1),(35850,9),(35082,9),(18698,9),(12806,8),(12550,10),(3265,10),(8897,9),(12385,9),(2273,16),(12817,7),(12561,10)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top2ok : weightCheck Top2 Top2w 51=true := by
  have f : fives Top2 = [19592,35912,3272,35112,18728,18600,34920,2280,25220,18052,37444,12868,34372,8900,1732,24868,37156,12580,24740,36964,12388,8420,17548,33868,1228,33068,16684,16556,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,35850,19466,35082,18698,25094,37382,12806,34310,17926,24838,37126,12550,33806,17422,33038,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top3 : List Nat := [7,56,290,801,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top3w : List (Nat × Nat) := [(19592,41),(35912,55),(35112,8),(18728,6),(34920,6),(8900,16),(1732,70),(12388,9),(8420,52),(1228,6),(236,31),(35858,1),(19474,7),(25106,6),(37394,5),(12818,10),(34322,9),(24850,44),(37138,36),(12562,48),(35082,40),(18698,48),(12806,38),(12865,6),(12577,10),(8417,22),(2273,77),(12561,31)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top3ok : weightCheck Top3 Top3w 146=true := by
  have f : fives Top3 = [19592,35912,3272,35112,18728,18600,34920,2280,25220,18052,37444,12868,34372,8900,1732,24740,36964,12388,8420,17548,33868,1228,16556,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,35850,19466,35082,18698,25094,37382,12806,34310,17926,33806,17422,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top4 : List Nat := [7,56,386,769,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top4w : List (Nat × Nat) := [(35912,1),(3272,3),(2280,2),(12868,1),(8900,1),(12388,1),(8420,1),(716,4),(35858,2),(19474,2),(12818,2),(24850,4),(37138,3),(35082,4),(18698,4),(12806,2),(12550,2),(3265,2),(8897,1),(1729,2),(12577,2),(12385,1),(8417,1),(2273,2),(12817,1),(12561,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top4ok : weightCheck Top4 Top4w 10=true := by
  have f : fives Top4 = [19592,18056,35912,34376,3272,1736,35112,18728,18600,34920,2280,25220,37444,12868,8900,24868,37156,12580,24740,36964,12388,8420,17036,33356,716,33068,16684,16556,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,35850,19466,34314,17930,35082,18698,25094,37382,12806,24838,37126,12550,33294,16910,33038,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top5 : List Nat := [7,56,386,785,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top5w : List (Nat × Nat) := [(19592,1),(35912,1),(1736,1),(2280,2),(12868,1),(12580,1),(716,1),(24850,2),(37138,1),(35090,1),(35850,1),(19466,1),(12806,1),(12550,1),(3265,1),(8417,1),(12561,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top5ok : weightCheck Top5 Top5w 4=true := by
  have f : fives Top5 = [19592,18056,35912,34376,3272,1736,18600,34920,2280,25220,37444,12868,8900,24868,37156,12580,24740,36964,12388,8420,17036,33356,716,16556,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,35850,19466,34314,17930,25094,37382,12806,24838,37126,12550,33294,16910,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top6 : List Nat := [7,56,386,801,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top6w : List (Nat × Nat) := [(19592,4),(35912,6),(3272,1),(12868,1),(8900,4),(12580,4),(12388,4),(236,1),(35858,1),(12818,5),(24850,2),(37138,1),(35850,4),(19466,3),(18698,3),(12806,2),(12550,3),(3265,4),(8417,2),(2273,1),(12817,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top6ok : weightCheck Top6 Top6w 12=true := by
  have f : fives Top6 = [19592,35912,3272,35112,18728,18600,34920,2280,25220,37444,12868,8900,24868,37156,12580,24740,36964,12388,8420,33068,16684,16556,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,35850,19466,35082,18698,25094,37382,12806,24838,37126,12550,33038,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top7 : List Nat := [7,56,1058,2241,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top7w : List (Nat × Nat) := [(12872,5),(8904,16),(8424,16),(19588,8),(1732,45),(36964,8),(34916,8),(2276,38),(236,10),(35858,3),(19474,22),(24850,17),(37138,39),(12562,19),(35090,6),(18706,25),(12810,9),(24842,19),(12554,11),(35846,27),(4622,16),(35905,6),(3265,8),(8417,46),(2273,13),(35857,2),(24849,8),(12561,8),(35089,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top7ok : weightCheck Top7 Top7w 91=true := by
  have f : fives Top7 = [25224,12872,8904,24872,12584,24744,12392,8424,19588,18052,35908,37444,34372,3268,1732,18596,36964,34916,2276,17036,4684,716,16556,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,24842,12554,35846,19462,37382,34310,17926,16910,4622,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top8 : List Nat := [7,56,1090,2177,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top8w : List (Nat × Nat) := [(25224,7),(12872,13),(1736,12),(12584,2),(12392,6),(8424,6),(3268,7),(37156,4),(35108,2),(18724,4),(18596,9),(36964,9),(2276,5),(17548,7),(1228,12),(4396,2),(4204,7),(236,3),(19474,13),(25106,7),(37394,12),(12818,7),(34322,12),(17938,3),(24850,12),(37138,3),(12562,5),(35090,6),(18706,8),(24842,15),(35846,13),(37126,5),(35078,6),(4366,11),(18049,3),(37441,7),(3265,7),(8897,13),(1729,3),(12577,4),(34913,15),(8417,8),(2273,12),(35857,7),(12561,9)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top8ok : weightCheck Top8 Top8w 68=true := by
  have f : fives Top8 = [25224,18056,12872,8904,1736,24872,12584,24744,12392,8424,19588,35908,3268,37156,35108,18724,18596,36964,34916,2276,17548,1228,16684,4396,16556,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,17930,24842,12554,35846,19462,37126,35078,18694,17422,16654,4366,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top9 : List Nat := [7,56,1090,2193,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top9w : List (Nat × Nat) := [(25224,557),(18056,282),(8904,21),(1736,148),(24744,165),(12392,204),(8424,378),(35908,76),(18724,678),(18596,458),(36964,430),(34916,378),(1228,514),(4204,310),(19474,225),(25106,176),(37394,264),(34322,854),(24850,392),(12562,225),(35090,153),(18706,275),(25098,286),(12810,408),(35846,353),(37126,458),(35078,51),(18694,16),(19585,16),(8897,498),(36961,574),(12385,76),(34913,193),(2273,144),(12817,310),(37137,148),(35089,266)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top9ok : weightCheck Top9 Top9w 2209=true := by
  have f : fives Top9 = [25224,18056,12872,8904,1736,24744,12392,8424,19588,35908,3268,37156,35108,18724,18596,36964,34916,2276,17548,1228,16556,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,17930,35846,19462,37126,35078,18694,17422,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top10 : List Nat := [7,56,1090,2241,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top10w : List (Nat × Nat) := [(25224,1),(12872,2),(8904,5),(12584,1),(12392,2),(3268,4),(18596,2),(34916,2),(4204,2),(19474,4),(37394,3),(12818,2),(34322,1),(17938,1),(12810,1),(24842,6),(12554,1),(35846,4),(35078,2),(4366,2),(3265,1),(8417,2),(2273,3),(35857,4),(34321,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top10ok : weightCheck Top10 Top10w 12=true := by
  have f : fives Top10 = [25224,12872,8904,24872,12584,24744,12392,8424,19588,35908,3268,37156,35108,18724,18596,36964,34916,2276,16684,4396,16556,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,24842,12554,35846,19462,37126,35078,18694,16654,4366,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top11 : List Nat := [7,56,1538,2241,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top11w : List (Nat × Nat) := [(12872,3),(8904,8),(12584,4),(24744,1),(12392,5),(19588,9),(35908,5),(3268,5),(1732,1),(34916,4),(236,2),(35858,5),(37394,1),(12818,8),(37138,2),(18706,7),(25098,1),(12810,3),(24842,6),(12554,5),(35846,5),(34310,2),(35078,4),(16654,1),(36961,1),(12385,6),(2273,7),(35857,9),(12817,1),(12561,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top11ok : weightCheck Top11 Top11w 24=true := by
  have f : fives Top11 = [25224,12872,8904,24872,12584,24744,12392,8424,19588,18052,35908,34372,3268,1732,35108,18724,18596,34916,2276,17036,716,16684,16556,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,24842,12554,35846,19462,34310,17926,35078,18694,16910,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top12 : List Nat := [7,56,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top12w : List (Nat × Nat) := [(1736,3),(12584,3),(12392,3),(19588,4),(35908,3),(35108,2),(18724,3),(18596,4),(33868,5),(1228,4),(236,4),(19474,3),(25106,4),(34322,2),(17938,3),(24850,3),(37138,4),(18706,2),(12810,5),(12554,4),(35846,2),(35078,3),(8897,3),(1729,2),(12577,2),(18593,5),(8417,4),(2273,1),(12817,4)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top12ok : weightCheck Top12 Top12w 19=true := by
  have f : fives Top12 = [37448,12872,34376,8904,1736,37160,12584,36968,12392,8424,19588,35908,3268,35108,18724,18596,34916,2276,33868,1228,33068,32876,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,37386,12810,34314,37130,12554,35846,19462,35078,18694,33806,33038,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top13 : List Nat := [7,56,1602,2177,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top13w : List (Nat × Nat) := [(8904,4),(1736,3),(12584,2),(12392,1),(19588,3),(35908,3),(3268,2),(35108,2),(34916,3),(17548,2),(1228,1),(236,3),(35858,4),(37394,1),(12818,2),(34322,3),(24850,4),(37138,3),(12810,3),(24842,1),(12554,3),(35078,1),(18694,5),(12385,5),(34913,1),(2273,4),(37393,2),(12817,3)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top13ok : weightCheck Top13 Top13w 15=true := by
  have f : fives Top13 = [25224,18056,12872,8904,1736,24872,12584,24744,12392,8424,19588,35908,3268,35108,18724,18596,34916,2276,17548,1228,16684,16556,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,17930,24842,12554,35846,19462,35078,18694,17422,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top14 : List Nat := [7,56,3074,2241,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top14w : List (Nat × Nat) := [(12872,2),(8904,1),(12584,1),(24744,1),(34372,1),(3268,1),(34916,1),(35858,1),(19474,1),(25098,1),(24842,2),(12554,1),(35846,1),(35078,1),(2273,2),(35857,1),(19473,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top14ok : weightCheck Top14 Top14w 4=true := by
  have f : fives Top14 = [25224,12872,8904,24872,12584,24744,12392,8424,35908,37444,34372,3268,1732,37156,35108,36964,34916,2276,4684,716,4396,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,24842,12554,35846,37382,34310,37126,35078,4622,4366,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top15 : List Nat := [7,56,3138,2177,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top15w : List (Nat × Nat) := [(12872,61),(8904,9),(1736,60),(24744,57),(12392,26),(35908,22),(3268,34),(37156,33),(35108,15),(36964,5),(2276,51),(1228,27),(4204,9),(236,22),(35858,11),(19474,68),(25106,62),(37394,47),(34322,15),(24850,20),(12562,42),(35090,31),(18706,46),(12810,41),(24842,69),(12554,9),(35846,44),(37126,28),(35078,45),(4366,17),(3265,34),(1729,10),(34913,61),(8417,95),(35857,43),(25105,12),(17937,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top15ok : weightCheck Top15 Top15w 260=true := by
  have f : fives Top15 = [25224,18056,12872,8904,1736,24872,12584,24744,12392,8424,35908,3268,37156,35108,36964,34916,2276,1228,4396,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,17930,24842,12554,35846,37126,35078,4366,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top16 : List Nat := [7,516,284,801,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top16w : List (Nat × Nat) := [(19592,1),(35912,1),(35112,1),(18728,1),(34324,1),(17940,1),(24852,1),(37140,1),(1730,1),(234,1),(12806,1),(12550,1),(1729,1),(2273,1),(12817,1),(12561,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top16ok : weightCheck Top16 Top16w 3=true := by
  have f : fives Top16 = [19592,35912,3272,35112,18728,18600,34920,2280,25108,37396,12820,34324,17940,24852,37140,12564,25218,18050,37442,12866,34370,8898,1730,24866,37154,12578,24738,36962,12386,8418,17546,33866,1226,33066,16682,16554,32874,234,25094,37382,12806,34310,17926,24838,37126,12550,33806,17422,33038,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top17 : List Nat := [7,516,284,804,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top17w : List (Nat × Nat) := [(19592,2),(35112,3),(18728,1),(18600,3),(35864,3),(35096,1),(25108,5),(37396,2),(37140,2),(17436,1),(16668,3),(25218,1),(8898,1),(1730,3),(36962,5),(8418,3),(16554,3),(12806,2),(24838,1),(12550,2),(33806,5),(35905,1),(3265,2),(1729,1),(12577,4),(24737,1),(12385,2),(2273,2),(35857,3),(19473,2),(37393,1),(12817,3),(12561,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top17ok : weightCheck Top17 Top17w 13=true := by
  have f : fives Top17 = [19592,35112,18728,18600,35864,19480,35096,18712,25108,37396,12820,34324,17940,24852,37140,12564,33820,17436,33052,16668,25218,18050,37442,12866,34370,8898,1730,24866,37154,12578,24738,36962,12386,8418,17546,33066,16682,16554,25094,37382,12806,34310,17926,24838,37126,12550,33806,17422,33038,16654,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top18 : List Nat := [7,528,1602,1169,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top18w : List (Nat × Nat) := [(37448,3),(34376,2),(1736,2),(12392,2),(19588,2),(35908,2),(35108,5),(18724,1),(18596,4),(2276,3),(24866,2),(12578,2),(17938,7),(24850,2),(37138,5),(12810,2),(8842,3),(12330,3),(8362,2),(16678,1),(33806,5),(1166,3),(35905,4),(3265,4),(8897,3),(12577,4),(2273,3),(19473,3),(25105,3),(12817,2),(37137,3),(35089,3),(18705,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top18ok : weightCheck Top18 Top18w 17=true := by
  have f : fives Top18 = [37448,12872,34376,8904,1736,36968,12392,8424,19588,35908,3268,35108,18724,18596,34916,2276,33868,1228,32876,236,25218,18050,24866,37154,12578,24738,25106,37394,12818,34322,17938,24850,37138,12562,37386,12810,34314,8842,1674,36906,12330,8362,17542,33062,16678,16550,33806,1166,32814,174,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top19 : List Nat := [7,528,1608,1169,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top19w : List (Nat × Nat) := [(34376,2),(8904,1),(36968,2),(8424,1),(18724,1),(18596,1),(19476,1),(35092,1),(12578,1),(25106,1),(12810,1),(16662,1),(33806,1),(1166,1),(35905,1),(12865,1),(3265,1),(12577,1),(25105,1),(18705,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top19ok : weightCheck Top19 Top19w 4=true := by
  have f : fives Top19 = [37448,12872,34376,8904,1736,36968,12392,8424,19588,35108,18724,18596,35860,19476,35092,18708,25218,18050,24866,37154,12578,24738,25106,37394,12818,34322,17938,24850,37138,12562,37386,12810,34314,8842,1674,36906,12330,8362,17542,33062,16678,16550,33814,17430,33046,16662,33806,1166,32814,174,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top20 : List Nat := [7,536,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top20w : List (Nat × Nat) := [(1736,27),(37160,4),(12584,42),(36968,19),(19588,27),(35908,45),(35108,23),(18724,69),(18596,23),(34916,2),(32876,14),(236,30),(25218,45),(34322,65),(17938,30),(24850,30),(37138,30),(37386,1),(12810,27),(37130,14),(12554,3),(8842,20),(33806,11),(33038,16),(1166,18),(24737,5),(18593,40),(12385,15),(34913,15),(2273,15),(25105,65),(12817,27),(35089,45)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top20ok : weightCheck Top20 Top20w 167=true := by
  have f : fives Top20 = [37448,12872,34376,8904,1736,37160,12584,36968,12392,8424,19588,35908,3268,35108,18724,18596,34916,2276,33868,1228,33068,32876,236,25218,18050,25106,37394,12818,34322,17938,24850,37138,12562,37386,12810,34314,37130,12554,8842,1674,17542,33806,33038,1166,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top21 : List Nat := [7,536,1608,1153,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top21w : List (Nat × Nat) := [(8904,39),(12584,86),(36968,131),(19588,4),(35108,18),(18724,57),(18596,113),(35860,76),(19476,14),(35092,70),(25218,113),(18050,4),(37394,23),(34322,51),(37386,54),(12810,18),(12554,128),(17542,85),(16662,39),(33806,74),(33038,36),(1166,125),(12865,131),(3265,82),(1729,68),(24865,39),(35105,50),(24737,11),(18593,14),(34913,39),(2273,64),(25105,14),(18705,111)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top21ok : weightCheck Top21 Top21w 384=true := by
  have f : fives Top21 = [37448,12872,34376,8904,1736,37160,12584,36968,12392,8424,19588,35108,18724,18596,35860,19476,35092,18708,33068,25218,18050,25106,37394,12818,34322,17938,24850,37138,12562,37386,12810,34314,37130,12554,8842,1674,17542,33814,17430,33046,16662,33806,33038,1166,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top22 : List Nat := [7,560,290,801,7,24,130,145,3,2,6,3,2,2,1,0]
private def Top22w : List (Nat × Nat) := [(19592,1),(35912,1),(35112,1),(18728,1),(1732,1),(17548,1),(236,1),(12578,2),(37394,1),(17938,1),(24850,1),(37138,1),(12806,1),(33806,1),(1729,2),(2273,2),(12817,1),(35089,1),(18705,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top22ok : weightCheck Top22 Top22w 4=true := by
  have f : fives Top22 = [19592,35912,3272,35112,18728,18600,34920,2280,25220,18052,37444,12868,34372,8900,1732,24740,36964,12388,8420,17548,33868,1228,16556,32876,236,24866,37154,12578,25106,37394,12818,34322,17938,24850,37138,12562,33066,16682,25094,37382,12806,34310,17926,24614,36902,12326,33806,17422,32814,16430,19585,25217,18049,35905,37441,12865,34369,3265,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,34913,8417,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top23 : List Nat := [7,24,3074,2145,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top23w : List (Nat × Nat) := [(12584,21),(18728,40),(24744,7),(18600,8),(12392,20),(8424,28),(37444,19),(34372,59),(1732,25),(4396,6),(2348,60),(4204,15),(236,19),(18050,7),(12818,18),(34322,3),(17938,62),(37138,29),(35090,8),(18706,11),(18698,5),(24714,12),(35078,1),(3206,18),(1670,36),(4366,32),(2318,9),(19585,21),(34369,14),(1729,2),(37153,27),(24737,44),(18593,12),(36961,33),(25105,40),(34321,8),(17937,19),(37137,19)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top23ok : weightCheck Top23 Top23w 160=true := by
  have f : fives Top23 = [24872,12584,18728,24744,18600,12392,8424,37444,34372,1732,37156,35108,36964,4396,2348,2220,4204,236,19586,25218,18050,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,24842,12554,18698,24714,18570,35846,37382,34310,37126,35078,3206,1670,4366,2318,2190,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top24 : List Nat := [7,40,3138,2081,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top24w : List (Nat × Nat) := [(19592,10),(12584,11),(24744,17),(12392,2),(35108,7),(36964,17),(3212,24),(1228,29),(4396,10),(2348,6),(2220,5),(12866,19),(37394,5),(17938,18),(37138,15),(18706,17),(19466,11),(33862,13),(4366,14),(2318,19),(4174,26),(1102,7),(25217,8),(18049,19),(37441,8),(8897,10),(1729,15),(12577,23),(24737,1),(18593,28),(36961,1),(12385,17),(35857,21),(25105,8),(37393,21),(12817,2),(34321,16),(18705,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top24ok : weightCheck Top24 Top24w 99=true := by
  have f : fives Top24 = [19592,24872,12584,18728,24744,18600,12392,8424,37156,35108,36964,3212,1228,4396,2348,2220,4204,236,37442,12866,34370,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,19466,24842,12554,18698,12362,35846,37126,35078,36934,33862,3086,4366,2318,4174,1102,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top25 : List Nat := [7,56,3074,2081,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top25w : List (Nat × Nat) := [(19592,6),(18728,35),(24744,26),(37444,29),(34372,35),(1732,62),(3212,44),(1228,1),(4396,25),(2348,3),(4204,36),(236,42),(25106,26),(12818,30),(17938,38),(37138,38),(35090,8),(18706,35),(24842,3),(12554,4),(35078,21),(4366,21),(2318,5),(19585,26),(18049,12),(37441,20),(12865,2),(8897,30),(1729,5),(37153,6),(12577,3),(24737,26),(12385,4),(8417,38),(25105,3),(34321,6),(17937,11),(12561,25)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top25ok : weightCheck Top25 Top25w 157=true := by
  have f : fives Top25 = [19592,24872,12584,18728,24744,18600,12392,8424,37444,34372,1732,37156,35108,36964,3212,1228,4396,2348,2220,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,19466,24842,12554,18698,35846,37382,34310,37126,35078,3086,4366,2318,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top26 : List Nat := [7,56,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top26w : List (Nat × Nat) := [(25224,10),(12872,6),(24872,10),(12584,3),(18600,15),(37444,8),(1732,13),(35108,14),(36964,7),(4684,8),(716,7),(236,6),(19474,6),(37394,4),(17938,15),(37138,6),(12562,3),(18698,1),(34310,10),(37126,5),(4622,1),(2318,19),(19585,1),(18049,4),(12865,3),(1729,5),(35105,24),(24737,16),(8417,3),(35857,6),(19473,2),(34321,12),(17937,8),(18705,4)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top26ok : weightCheck Top26 Top26w 51=true := by
  have f : fives Top26 = [25224,12872,8904,24872,12584,18728,24744,18600,12392,8424,37444,34372,1732,37156,35108,36964,4684,716,4396,2348,2220,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,25098,12810,24842,12554,18698,35846,37382,34310,37126,35078,4622,4366,2318,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top27 : List Nat := [7,56,3138,2049,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top27w : List (Nat × Nat) := [(25224,1),(18056,1),(12872,2),(1736,1),(8424,1),(35108,2),(1228,1),(2348,1),(2220,1),(4204,1),(37394,1),(34322,1),(18706,2),(3086,2),(4366,2),(19585,2),(37441,1),(1729,2),(12385,2),(35857,2),(37393,1),(37137,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top27ok : weightCheck Top27 Top27w 6=true := by
  have f : fives Top27 = [19592,25224,18056,12872,8904,1736,24872,12584,18728,24744,18600,12392,8424,37156,35108,36964,3212,1228,4396,2348,2220,4204,236,35858,19474,25106,37394,12818,34322,17938,24850,37138,12562,35090,18706,19466,25098,12810,17930,24842,12554,18698,35846,37126,35078,3086,4366,2318,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top28 : List Nat := [7,132,3092,2178,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top28w : List (Nat × Nat) := [(25224,27),(18056,33),(12872,33),(1736,8),(24856,19),(37444,45),(34372,37),(35860,35),(34324,25),(37140,44),(35092,37),(19586,33),(12578,15),(35106,70),(18594,60),(36962,8),(24842,8),(24714,103),(17546,8),(8394,19),(35846,52),(37126,4),(35078,8),(36934,81),(4366,26),(19585,35),(25217,48),(18049,22),(12577,37),(18593,33),(36961,8),(25105,49),(37393,46),(12817,2),(34321,35),(17937,9),(12561,16)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top28ok : weightCheck Top28 Top28w 231=true := by
  have f : fives Top28 = [25224,18056,12872,8904,1736,25112,12824,17944,24856,12568,37444,34372,35860,37396,34324,37140,35092,4684,1612,4636,1564,4380,19586,24866,37154,12578,35106,18722,24738,18594,36962,12386,8418,24842,12554,24714,17546,12362,8394,1226,35846,37126,35078,36934,33862,4366,4174,1102,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top29 : List Nat := [7,388,3076,2054,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top29w : List (Nat × Nat) := [(25224,9),(18056,8),(18712,7),(34372,20),(1732,7),(37396,7),(1676,6),(1564,16),(24866,2),(37154,2),(12578,11),(35106,4),(18722,17),(24738,4),(18594,16),(36962,18),(12386,5),(8418,7),(12554,1),(24714,11),(35078,20),(36934,6),(4366,7),(34369,17),(1729,6),(37153,7),(24737,6),(8417,1),(25105,6),(17937,21),(37137,6)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top29ok : weightCheck Top29 Top29w 57=true := by
  have f : fives Top29 = [19592,25224,18056,19480,25112,12824,17944,24856,12568,18712,37444,34372,1732,35860,37396,34324,37140,35092,3212,1676,3100,4636,1564,4380,2332,24866,37154,12578,35106,18722,24738,18594,36962,12386,8418,24842,12554,18698,24714,18570,37126,35078,36934,4366,2318,2190,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top30 : List Nat := [7,388,3092,2050,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top30w : List (Nat × Nat) := [(19592,2),(25224,5),(18056,3),(8904,2),(1736,2),(19480,2),(34372,9),(35860,3),(37140,5),(35092,1),(1564,4),(12578,5),(35106,1),(18722,3),(18594,9),(36962,6),(12386,1),(8418,3),(24714,5),(35078,6),(36934,4),(2318,4),(4174,4),(19585,2),(18049,3),(8897,2),(1729,2),(35105,4),(24737,4),(36961,4),(19473,2),(34321,8),(17937,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top30ok : weightCheck Top30 Top30w 25=true := by
  have f : fives Top30 = [19592,25224,18056,12872,8904,1736,19480,25112,12824,17944,24856,12568,18712,37444,34372,35860,37396,34324,37140,35092,4684,1612,3100,4636,1564,4380,2332,24866,37154,12578,35106,18722,24738,18594,36962,12386,8418,24842,12554,18698,24714,18570,12362,8394,37126,35078,36934,4366,2318,4174,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top31 : List Nat := [7,584,3136,2144,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top31w : List (Nat × Nat) := [(18728,1),(24744,1),(35108,1),(236,1),(2332,1),(18050,1),(1730,1),(37394,1),(17938,1),(12362,1),(36934,1),(34369,1),(24865,1),(35105,1),(18705,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top31ok : weightCheck Top31 Top31w 3=true := by
  have f : fives Top31 = [24872,12584,18728,24744,18600,12392,8424,24856,12568,18712,37156,35108,36964,35860,37140,35092,4396,2348,2220,4204,236,4380,2332,25218,18050,37442,12866,34370,8898,1730,25106,37394,12818,34322,17938,24714,12362,8394,24602,12314,36934,33862,1222,36886,33814,4174,206,4126,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top32 : List Nat := [7,2056,3138,2113,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top32w : List (Nat × Nat) := [(25224,17),(12872,31),(24872,1),(18728,14),(24744,11),(18600,14),(35108,17),(36964,31),(2348,11),(2220,1),(19586,17),(34370,12),(1730,30),(19474,1),(37394,14),(34322,17),(17938,11),(37138,16),(18706,31),(18570,4),(17034,24),(4682,14),(37126,15),(3206,13),(36934,7),(33862,2),(1222,2),(4366,31),(2318,31),(2190,18),(4174,8),(206,30),(19585,31),(12865,7),(34369,14),(8897,15),(1729,16),(24865,18),(12577,30),(35105,24),(18721,4),(24737,31),(36961,14),(12385,8),(8417,31),(35857,11),(19473,1),(37393,12),(12817,2),(34321,17),(24849,13),(37137,30),(12561,2),(18705,17)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top32ok : weightCheck Top32 Top32w 167=true := by
  have f : fives Top32 = [25224,12872,8904,24872,12584,18728,24744,18600,12392,8424,37156,35108,36964,4396,2348,2220,4204,236,19586,18050,37442,34370,1730,35858,19474,37394,34322,17938,37138,35090,18706,18698,18570,17034,4682,714,35846,37126,35078,3206,36934,33862,1222,4366,2318,2190,4174,206,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top33 : List Nat := [7,2072,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0]
private def Top33w : List (Nat × Nat) := [(25224,209),(12872,184),(8904,23),(24872,64),(18728,143),(24744,112),(18600,88),(37444,66),(1732,115),(37156,87),(35108,176),(36964,145),(4684,64),(716,86),(2348,222),(236,2),(19586,112),(18050,146),(37394,147),(17938,90),(37138,145),(18706,2),(18570,88),(34310,232),(37126,87),(3206,64),(1670,3),(4622,159),(4366,176),(2318,222),(2190,143),(654,181),(19585,209),(37441,21),(12865,113),(34369,114),(1729,180),(24865,3),(12577,232),(35105,159),(18721,181),(24737,146),(36961,147),(8417,90),(35857,184),(19473,23),(25105,180),(12817,135),(34321,134),(24849,115),(37137,66),(35089,64),(18705,86)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top33ok : weightCheck Top33 Top33w 1260=true := by
  have f : fives Top33 = [25224,12872,8904,24872,12584,18728,24744,18600,12392,8424,37444,34372,1732,37156,35108,36964,4684,716,4396,2348,2220,4204,236,19586,18050,35858,19474,37394,34322,17938,37138,35090,18706,18698,18570,17034,35846,37382,34310,37126,35078,3206,1670,4622,4366,2318,2190,654,19585,25217,18049,37441,12865,34369,8897,1729,24865,37153,12577,35105,18721,24737,18593,36961,12385,8417,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top34 : List Nat := [7,536,578,1153,7,24,194,145,3,2,6,3,2,2,1,0]
private def Top34w : List (Nat × Nat) := [(37448,14),(34376,1),(37160,1),(36968,1),(35908,11),(24868,7),(35108,15),(24740,13),(1228,5),(8492,16),(32876,5),(18050,16),(25106,13),(34322,6),(37138,11),(37386,1),(12554,8),(1674,7),(24710,11),(33806,18),(33038,9),(8462,5),(8334,11),(1166,8),(25217,9),(35905,11),(34369,1),(1729,15),(37153,4),(12577,6),(35105,1),(18721,1),(24737,18),(34913,11),(2273,11),(19473,6),(37393,11),(12817,11),(34321,4),(17937,1),(24849,6),(37137,11),(18705,9)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top34ok : weightCheck Top34 Top34w 71=true := by
  have f : fives Top34 = [37448,34376,1736,37160,12584,36968,19588,35908,3268,24868,35108,18724,24740,18596,34916,2276,33868,1228,33068,8492,8364,32876,236,25218,18050,25106,37394,12818,34322,17938,24850,37138,12562,37386,12810,34314,37130,12554,8842,1674,24838,24710,17542,33806,33038,8462,8334,1166,19585,25217,18049,35905,37441,34369,3265,1729,24865,37153,12577,35105,18721,24737,18593,36961,34913,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top35 : List Nat := [7,4228,2308,2308,7,24,194,145,3,2,6,3,2,2,1,0]
private def Top35w : List (Nat × Nat) := [(19592,22),(25224,27),(18056,25),(24872,25),(24744,15),(18600,3),(25112,3),(24856,22),(37444,25),(34372,3),(1732,6),(12820,7),(34324,16),(37140,21),(8844,11),(1564,16),(35906,21),(37154,1),(12578,6),(35106,6),(36962,25),(2274,7),(2346,28),(8362,11),(37126,16),(12550,31),(33862,14),(1222,31),(8334,6),(18049,6),(35905,7),(1729,16),(24865,6),(12577,16),(18721,15),(36961,12),(34913,38),(37393,38),(17937,15),(37137,7)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top35ok : weightCheck Top35 Top35w 132=true := by
  have f : fives Top35 = [19592,25224,18056,24872,18728,24744,18600,19480,25112,17944,24856,18712,37444,34372,1732,37396,12820,34324,37140,12564,8844,1676,8732,1564,8476,35906,3266,37154,12578,35106,36962,34914,2274,3210,8490,2346,8362,2218,37126,12550,36934,33862,1222,8462,8334,1166,19585,25217,18049,35905,37441,34369,3265,1729,24865,37153,12577,35105,18721,24737,18593,36961,34913,2273,35857,19473,25105,37393,12817,34321,17937,24849,37137,12561,35089,18705] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top36 : List Nat := [15,4144,3076,2194,1170,3,2,6,3,2,6,3,2,2,1,0]
private def Top36w : List (Nat × Nat) := [(24976,2),(18832,1),(18736,1),(25160,7),(17992,2),(12488,2),(24728,1),(35908,5),(37444,3),(2452,3),(1612,2),(4300,1),(3122,2),(8498,6),(12810,5),(34310,3),(37126,3),(2326,6),(4622,1),(1550,1),(1054,2),(24961,2),(18625,6),(25121,4),(35105,1),(18721,2)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top36ok : weightCheck Top36 Top36w 15=true := by
  have f : fives Top36 = [24976,18832,19504,24880,18736,25160,12872,17992,24776,12488,24728,37252,35204,35908,37444,34372,37060,35012,2452,4684,1612,4300,35874,37410,12834,34338,37154,12578,35106,3122,8498,2354,12810,35846,37382,34310,37126,35078,3094,2326,4622,1550,1054,24961,37249,12673,35201,18817,35905,19521,25153,37441,12865,34369,17985,24769,37057,12481,35009,18625,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top37 : List Nat := [15,2192,2084,2180,1153,3,2,70,3,2,6,3,2,2,1,0]
private def Top37w : List (Nat × Nat) := [(19536,4),(25168,2),(18000,4),(12840,3),(17960,4),(24856,4),(8600,2),(37444,2),(12868,1),(12484,1),(8788,1),(1620,4),(2260,4),(12812,1),(12428,1),(8732,1),(1564,2),(8348,1),(37250,4),(35202,4),(35874,1),(19490,1),(37154,2),(35106,1),(18722,1),(18706,2),(17450,2),(16682,4),(16666,4),(35846,3),(36998,4),(4238,2),(158,4),(12673,4),(35201,2),(35905,4),(19521,2),(37441,4),(12865,4),(12481,2),(35873,1),(19489,1),(37409,4),(34337,2),(24865,4),(35105,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top37ok : weightCheck Top37 Top37w 25=true := by
  have f : fives Top37 = [19536,25168,18000,12680,25128,12840,17960,24872,12584,25112,17944,24856,8600,35908,37444,12868,34372,37060,12484,35012,3156,8788,1620,8404,2260,12812,12428,8732,1564,8348,37250,35202,35874,19490,37154,35106,18722,19474,18706,2450,4490,17450,16682,4394,17434,16666,410,35846,36998,34950,3094,2198,4238,1054,158,37249,12673,35201,35905,19521,25153,37441,12865,34369,17985,37057,12481,35009,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top38 : List Nat := [15,2192,2084,2180,1161,3,2,70,3,2,6,3,2,2,1,0]
private def Top38w : List (Nat × Nat) := [(19536,1),(25168,2),(12680,2),(12840,2),(17960,2),(24872,2),(12484,3),(35012,1),(3156,1),(8788,1),(1620,2),(8404,1),(2260,2),(8732,1),(1564,1),(8348,2),(37154,1),(35106,1),(18722,2),(19474,2),(4490,3),(17450,1),(16682,1),(4394,2),(17434,3),(35846,2),(36998,2),(2198,2),(4238,1),(1054,2),(158,1),(12673,1),(35201,2),(35905,3),(19521,1),(12865,3),(17985,2),(37057,2),(12481,1),(19489,3),(25121,1),(24865,2),(37153,2),(12577,1),(35105,1),(18721,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top38ok : weightCheck Top38 Top38w 17=true := by
  have f : fives Top38 = [19536,25168,18000,12680,25128,12840,17960,24872,12584,25112,17944,35908,37444,12868,34372,37060,12484,35012,3156,8788,1620,8404,2260,12812,12428,8732,1564,8348,37250,35202,35874,19490,37154,35106,18722,19474,4490,17450,16682,4394,17434,35846,36998,34950,3094,2198,4238,1054,158,37249,12673,35201,35905,19521,25153,37441,12865,34369,17985,37057,12481,35009,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top39 : List Nat := [15,2192,2084,2180,1169,3,2,70,3,2,6,3,2,2,1,0]
private def Top39w : List (Nat × Nat) := [(19536,394),(25128,155),(12840,285),(17960,386),(12584,178),(12868,288),(34372,22),(37060,178),(3156,155),(8404,115),(2260,378),(12812,236),(8348,548),(35874,155),(19490,260),(18706,29),(2450,117),(4490,65),(17450,3),(16682,237),(4394,78),(17434,95),(16666,283),(410,318),(36998,145),(34950,404),(4238,166),(1054,571),(12673,373),(35905,469),(19521,17),(25153,289),(37441,94),(12865,284),(34369,1),(17985,123),(37057,117),(12481,136),(35009,56),(19489,500),(37409,329),(34337,49),(24865,155),(12577,164),(18721,22)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top39ok : weightCheck Top39 Top39w 2019=true := by
  have f : fives Top39 = [19536,12680,25128,12840,17960,24872,12584,24856,8600,35908,37444,12868,34372,37060,12484,35012,3156,8404,2260,12812,12428,8348,37250,35202,35874,19490,37154,35106,18722,19474,18706,2450,4490,17450,16682,4394,17434,16666,410,35846,36998,34950,3094,2198,4238,1054,158,37249,12673,35201,35905,19521,25153,37441,12865,34369,17985,37057,12481,35009,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top40 : List Nat := [15,2192,2340,2180,1153,3,2,70,3,2,6,3,2,2,1,0]
private def Top40w : List (Nat × Nat) := [(19536,761),(12680,131),(25112,226),(17944,369),(37444,47),(12868,313),(34372,496),(12484,498),(1620,360),(8404,327),(12812,741),(12428,189),(8732,332),(1564,17),(35202,95),(35874,311),(19490,151),(35106,247),(18722,568),(19474,142),(2450,731),(4490,94),(16682,137),(4394,120),(16666,416),(36998,779),(4238,446),(1054,687),(158,213),(37249,226),(12673,139),(35201,432),(35905,300),(19521,102),(25153,149),(37441,581),(17985,402),(35009,482),(35873,148),(19489,191),(37409,180),(17953,136),(35105,147),(18721,709)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top40ok : weightCheck Top40 Top40w 3045=true := by
  have f : fives Top40 = [19536,25168,18000,12680,25128,12840,17960,24872,12584,25112,17944,24856,8600,37444,12868,34372,37060,12484,8788,1620,8404,12812,12428,8732,1564,8348,37250,35202,35874,19490,37154,35106,18722,19474,18706,2450,4490,17450,16682,4394,17434,16666,410,36998,4238,1054,158,37249,12673,35201,35905,19521,25153,37441,12865,34369,17985,37057,12481,35009,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top41 : List Nat := [15,2192,3108,2180,1153,3,2,70,3,2,6,3,2,2,1,0]
private def Top41w : List (Nat × Nat) := [(19536,8),(25168,29),(12680,28),(12840,14),(17960,8),(24872,1),(25112,14),(24856,16),(8600,29),(35908,1),(37444,29),(34372,2),(37060,28),(1620,28),(2260,14),(1564,29),(37250,18),(35202,14),(37154,21),(19474,14),(18706,21),(2450,8),(17450,21),(4394,22),(17434,18),(16666,18),(35846,31),(36998,2),(34950,1),(3094,1),(4238,29),(1054,16),(158,14),(37249,18),(12673,2),(35201,21),(19521,21),(25153,16),(12865,14),(34369,18),(17985,18),(12481,29),(35009,22),(25121,1),(37409,22),(34337,21),(17953,14),(24865,31),(12577,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top41ok : weightCheck Top41 Top41w 177=true := by
  have f : fives Top41 = [19536,25168,18000,12680,25128,12840,17960,24872,12584,25112,17944,24856,8600,35908,37444,34372,37060,35012,3156,1620,2260,1564,37250,35202,35874,19490,37154,35106,18722,19474,18706,2450,4490,17450,16682,4394,17434,16666,410,35846,36998,34950,3094,2198,4238,1054,158,37249,12673,35201,35905,19521,25153,37441,12865,34369,17985,37057,12481,35009,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top42 : List Nat := [15,2192,2084,2082,1092,3,34,68,3,2,6,3,2,2,1,0]
private def Top42w : List (Nat × Nat) := [(12848,1),(17968,1),(24880,1),(12680,1),(24664,1),(17496,1),(34372,1),(35012,1),(8788,1),(3148,1),(8396,1),(12316,1),(35106,1),(4402,1),(19466,1),(18698,1),(4378,1),(35846,1),(36998,1),(4238,1),(1054,1),(12929,1),(37249,1),(35201,1),(19521,1),(34369,1),(8897,1),(35873,1),(37409,1),(17953,1),(12577,1),(18721,1)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top42ok : weightCheck Top42 Top42w 7=true := by
  have f : fives Top42 = [25168,18000,25136,12848,17968,24880,12592,12680,19528,24856,12568,24664,17496,37508,12932,35908,34372,35012,33476,8900,12820,8788,1620,12428,3148,8396,2252,12316,8284,1116,37250,35202,35874,19490,37154,35106,18722,17458,16690,4402,19466,18698,4490,2442,17434,16666,4378,35846,36998,34950,3086,4238,2190,4126,1054,37505,12929,37249,12673,35201,35905,19521,25153,34369,17985,35009,33473,8897,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private abbrev Top43 : List Nat := [15,2192,2084,2082,1094,3,34,68,3,2,6,3,2,2,1,0]
private def Top43w : List (Nat × Nat) := [(25136,16),(12848,1),(17968,16),(12680,13),(19528,8),(24856,7),(37508,5),(34372,7),(8900,16),(12820,16),(3148,16),(8396,8),(2252,9),(12316,16),(35874,8),(19490,10),(18722,12),(17458,1),(4402,17),(18698,13),(4490,12),(17434,16),(35846,5),(36998,8),(34950,12),(4238,10),(2190,10),(4126,1),(1054,16),(37505,12),(12929,10),(19521,9),(25153,8),(17985,16),(35009,17),(8897,9),(35873,12),(19489,10),(37409,8),(12833,10),(34337,5),(24865,13),(12577,12)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 50000000 in
private theorem Top43ok : weightCheck Top43 Top43w 99=true := by
  have f : fives Top43 = [25136,12848,17968,24880,12592,12680,19528,24856,12568,37508,12932,35908,34372,35012,33476,8900,12820,12428,3148,8396,2252,12316,37250,35202,35874,19490,37154,35106,18722,17458,16690,4402,19466,18698,4490,2442,17434,16666,4378,35846,36998,34950,3086,4238,2190,4126,1054,37505,12929,37249,12673,35201,35905,19521,25153,34369,17985,35009,33473,8897,35873,19489,25121,37409,12833,34337,17953,24865,37153,12577,35105,18721] := by decide +kernel
  rw [weightCheck,f]
  decide +kernel

private theorem noextend (b : List Nat) (hb : b∈atlas) : ∃ W lo,weightCheck b W lo=true := by
  simp only [atlas,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,_,Top0ok⟩
  · exact ⟨_,_,Top1ok⟩
  · exact ⟨_,_,Top2ok⟩
  · exact ⟨_,_,Top3ok⟩
  · exact ⟨_,_,Top4ok⟩
  · exact ⟨_,_,Top5ok⟩
  · exact ⟨_,_,Top6ok⟩
  · exact ⟨_,_,Top7ok⟩
  · exact ⟨_,_,Top8ok⟩
  · exact ⟨_,_,Top9ok⟩
  · exact ⟨_,_,Top10ok⟩
  · exact ⟨_,_,Top11ok⟩
  · exact ⟨_,_,Top12ok⟩
  · exact ⟨_,_,Top13ok⟩
  · exact ⟨_,_,Top14ok⟩
  · exact ⟨_,_,Top15ok⟩
  · exact ⟨_,_,Top16ok⟩
  · exact ⟨_,_,Top17ok⟩
  · exact ⟨_,_,Top18ok⟩
  · exact ⟨_,_,Top19ok⟩
  · exact ⟨_,_,Top20ok⟩
  · exact ⟨_,_,Top21ok⟩
  · exact ⟨_,_,Top22ok⟩
  · exact ⟨_,_,Top23ok⟩
  · exact ⟨_,_,Top24ok⟩
  · exact ⟨_,_,Top25ok⟩
  · exact ⟨_,_,Top26ok⟩
  · exact ⟨_,_,Top27ok⟩
  · exact ⟨_,_,Top28ok⟩
  · exact ⟨_,_,Top29ok⟩
  · exact ⟨_,_,Top30ok⟩
  · exact ⟨_,_,Top31ok⟩
  · exact ⟨_,_,Top32ok⟩
  · exact ⟨_,_,Top33ok⟩
  · exact ⟨_,_,Top34ok⟩
  · exact ⟨_,_,Top35ok⟩
  · exact ⟨_,_,Top36ok⟩
  · exact ⟨_,_,Top37ok⟩
  · exact ⟨_,_,Top38ok⟩
  · exact ⟨_,_,Top39ok⟩
  · exact ⟨_,_,Top40ok⟩
  · exact ⟨_,_,Top41ok⟩
  · exact ⟨_,_,Top42ok⟩
  · exact ⟨_,_,Top43ok⟩

end OMA.RamseyFinite
end SixteenVertices

section FourCycles
namespace Deldor14.RamseyParity
open Finset SimpleGraph

private def cross {V : Type*} (G : SimpleGraph V) (p q : V × V) : Prop :=
  G.Adj p.1 q.1 ∧ G.Adj p.1 q.2 ∧ G.Adj p.2 q.1 ∧ G.Adj p.2 q.2

variable {V : Type*} [LinearOrder V]

/-- A quadrilateral rooted at `v`: record its opposite vertex and order its two neighbors. -/
private def Rooted (G : SimpleGraph V) (v : V) :=
  {p : V × (V × V) // v ≠ p.1 ∧ p.2.1 < p.2.2 ∧ cross G (v, p.1) p.2}

private def Oriented (G : SimpleGraph V) :=
  {p : (V × V) × (V × V) //
    p.1.1 ≠ p.1.2 ∧ p.2.1 < p.2.2 ∧ cross G p.1 p.2}

private def firstLt (G : SimpleGraph V) (p : Oriented G) : Prop :=
  p.val.1.1 < p.val.1.2

private def Ordered (G : SimpleGraph V) := Subtype (firstLt G)

private def pairLt (G : SimpleGraph V) (p : Ordered G) : Prop :=
  p.val.val.1.1 < p.val.val.2.1

private def rootedEquiv (G : SimpleGraph V) : (Σ v, Rooted G v) ≃ Oriented G where
  toFun x := ⟨((x.1, x.2.val.1), x.2.val.2), x.2.property⟩
  invFun x := ⟨x.val.1.1, ⟨(x.val.1.2, x.val.2), x.property⟩⟩
  left_inv := by rintro ⟨v, ⟨⟨u, a, b⟩, h⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨v, u⟩, a, b⟩, h⟩; rfl

private def flipFirst (G : SimpleGraph V) (p : Oriented G) : Oriented G :=
  ⟨(p.val.1.swap, p.val.2), p.property.1.symm, p.property.2.1,
    p.property.2.2.2.2.1, p.property.2.2.2.2.2, p.property.2.2.1, p.property.2.2.2.1⟩

private theorem flipFirst_involutive (G : SimpleGraph V) :
    Function.Involutive (flipFirst G) := by
  rintro ⟨⟨⟨v, u⟩, a, b⟩, h⟩
  rfl

private theorem flipFirst_switch (G : SimpleGraph V) (p : Oriented G) :
    firstLt G (flipFirst G p) ↔ ¬ firstLt G p := by
  change p.val.1.2 < p.val.1.1 ↔ ¬ p.val.1.1 < p.val.1.2
  exact ⟨not_lt_of_gt, fun h => lt_of_le_of_ne (le_of_not_gt h) p.property.1.symm⟩

private def flipPairs (G : SimpleGraph V) (p : Ordered G) : Ordered G :=
  ⟨⟨(p.val.val.2, p.val.val.1), p.val.property.2.1.ne, p.property,
    p.val.property.2.2.1.symm, p.val.property.2.2.2.2.1.symm,
    p.val.property.2.2.2.1.symm, p.val.property.2.2.2.2.2.symm⟩,
    p.val.property.2.1⟩

private theorem flipPairs_involutive (G : SimpleGraph V) :
    Function.Involutive (flipPairs G) := by
  rintro ⟨⟨⟨⟨v, u⟩, a, b⟩, h⟩, h'⟩
  rfl

private theorem flipPairs_switch (G : SimpleGraph V) (p : Ordered G) :
    pairLt G (flipPairs G p) ↔ ¬ pairLt G p := by
  change p.val.val.2.1 < p.val.val.1.1 ↔ ¬ p.val.val.1.1 < p.val.val.2.1
  exact ⟨not_lt_of_gt, fun h =>
    lt_of_le_of_ne (le_of_not_gt h) p.val.property.2.2.1.ne.symm⟩

/-- An involution switching the two sides of a predicate gives two copies of either side. -/
private def splitBool {α : Type*} (p : α → Prop) [DecidablePred p]
    (s : α → α) (hs : Function.Involutive s) (hp : ∀ x, p (s x) ↔ ¬ p x) :
    α ≃ Bool × Subtype p where
  toFun x := if h : p x then (false, ⟨x, h⟩) else (true, ⟨s x, (hp x).mpr h⟩)
  invFun x := if x.1 = true then s x.2.val else x.2.val
  left_inv x := by
    by_cases h : p x <;> simp [h, hs x]
  right_inv := by
    rintro ⟨b, x, hx⟩
    cases b
    · simp [hx]
    · simp [show ¬ p (s x) from fun h => (hp x).mp h hx, hs x]

private theorem incidence_divisible_by_four [Fintype V] (G : SimpleGraph V) :
    4 ∣ ∑ v, Nat.card (Rooted G v) := by
  classical
  let (v : V) : Fintype (Rooted G v) := by
    unfold Rooted
    exact Fintype.ofFinite _
  let : Fintype (Oriented G) := by
    unfold Oriented
    exact Fintype.ofFinite _
  let : Fintype (Ordered G) := by
    unfold Ordered
    exact Fintype.ofFinite _
  let : Fintype (Subtype (pairLt G)) := Fintype.ofFinite _
  let e₁ := splitBool (firstLt G) (flipFirst G) (flipFirst_involutive G) (flipFirst_switch G)
  let e₂ := splitBool (pairLt G) (flipPairs G) (flipPairs_involutive G) (flipPairs_switch G)
  have h := Fintype.card_congr ((rootedEquiv G).trans
    (e₁.trans ((Equiv.refl Bool).prodCongr e₂)))
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool] at h
  simp_rw [Nat.card_eq_fintype_card]
  rw [h]
  exact ⟨Fintype.card (Subtype (pairLt G)), by omega⟩

section Census
open Finset SimpleGraph
variable (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
variable (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 7) (reg : ∀ x, G.degree x = 6)

private abbrev common (v w : Fin 23) := G.neighborFinset v ∩ G.neighborFinset w

include ht in
private theorem no_triangle {a v w : Fin 23} (av : G.Adj a v) (aw : G.Adj a w)
    (ne : v ≠ w) : ¬ G.Adj v w :=
  G.isIndepSet_neighborSet_of_triangleFree ht a av aw ne

include ht hc reg in
private theorem row_positive (v w : Fin 23) (hw : w ∈ Gᶜ.neighborFinset v) :
    0 < (common G v w).card := by
  classical
  rw [Finset.card_pos]
  by_contra none
  have cw := (Gᶜ.mem_neighborFinset _ _).mp hw
  have wn : w ∉ G.neighborFinset v := fun h => cw.2 ((G.mem_neighborFinset _ _).mp h)
  apply hc (insert w (G.neighborFinset v))
  constructor
  · rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem wn]
    constructor
    · rw [G.isClique_compl, G.coe_neighborFinset]
      exact G.isIndepSet_neighborSet_of_triangleFree ht v
    · intro a ha
      refine ⟨?_,?_⟩
      · rintro rfl
        exact wn ha
      · intro adj
        exact none ⟨a,mem_inter.mpr ⟨ha,(G.mem_neighborFinset _ _).mpr adj⟩⟩
  · rw [card_insert_of_notMem wn,card_neighborFinset_eq_degree,reg]

include ht reg in
private theorem row_sum (v : Fin 23) :
    ∑ w ∈ Gᶜ.neighborFinset v, (common G v w).card = 30 := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have eq (u) (hu : u ∈ N) : B.filter (G.Adj u) = (G.neighborFinset u).erase v := by
    ext w
    have uv := ((G.mem_neighborFinset _ _).mp hu).symm
    simp only [B,mem_filter,mem_neighborFinset,compl_adj,mem_erase]
    constructor
    · rintro ⟨⟨vw,_⟩,uw⟩
      exact ⟨vw.symm,uw⟩
    · rintro ⟨wv,uw⟩
      exact ⟨⟨wv.symm,no_triangle G ht uv uw wv.symm⟩,uw⟩
  calc
    _ = ∑ w ∈ B, ∑ u ∈ N, (if G.Adj u w then 1 else 0 : ℕ) := by
      apply sum_congr rfl
      intro w _
      rw [sum_boole]
      congr 1
      ext a
      simp [common,N,G.adj_comm]
    _ = ∑ u ∈ N, ∑ w ∈ B, (if G.Adj u w then 1 else 0 : ℕ) := by rw [Finset.sum_comm]
    _ = ∑ _ ∈ N, 5 := by
      apply sum_congr rfl
      intro u hu
      have vu := (G.mem_neighborFinset _ _).mp hu
      rw [sum_boole,eq u hu,card_erase_of_mem ((G.mem_neighborFinset _ _).mpr vu.symm),
        card_neighborFinset_eq_degree,reg]
      norm_num
    _ = 30 := by simp [N,reg]

include ht hc reg in
private theorem opposite_count (v : Fin 23)
    (small : ∀ w ∈ Gᶜ.neighborFinset v, (common G v w).card ≤ 2) :
    ((Gᶜ.neighborFinset v).filter (fun w => (common G v w).card = 2)).card = 14 := by
  classical
  let B := Gᶜ.neighborFinset v
  have size : B.card = 16 := by
    change Gᶜ.degree v = 16
    rw [G.degree_compl,Fintype.card_fin,reg]
  have value :
      ∑ w ∈ B, (common G v w).card =
      ∑ w ∈ B, (1 + if (common G v w).card = 2 then 1 else 0) := by
    apply sum_congr rfl
    intro w hw
    have lo := row_positive G ht hc reg v w hw
    have hi := small w hw
    split_ifs <;> omega
  rw [sum_add_distrib,sum_boole,sum_const,nsmul_eq_mul,mul_one,size] at value
  have total := row_sum G ht reg v
  change ∑ w ∈ B, (common G v w).card = 30 at total
  rw [total] at value
  change 30 = 16 + (B.filter (fun w => (common G v w).card = 2)).card at value
  change (B.filter _).card=14
  omega
include ht in
private theorem pair_info {v w a b : Fin 23} (vw : v ≠ w) (ab : a<b)
    (x : cross G (v,w) (a,b))
    (small : ∀ w ∈ Gᶜ.neighborFinset v, (common G v w).card ≤ 2) :
    w ∈ Gᶜ.neighborFinset v ∧ common G v w = {a,b} := by
  obtain ⟨va,vb,wa,wb⟩ := x
  have hw : w ∈ Gᶜ.neighborFinset v :=
    (Gᶜ.mem_neighborFinset _ _).mpr ⟨vw,no_triangle G ht va.symm wa.symm vw⟩
  refine ⟨hw,(eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl <;> simp [common,va,vb,wa,wb]
  · rw [card_pair ab.ne]
    exact small w hw

include ht hc reg in
private theorem rooted_count (v : Fin 23)
    (small : ∀ w ∈ Gᶜ.neighborFinset v, (common G v w).card ≤ 2) :
    Nat.card (Rooted G v) = 14 := by
  classical
  let S := (Gᶜ.neighborFinset v).filter (fun w => (common G v w).card=2)
  let f (p : Rooted G v) : ↥S := ⟨p.val.1,by
    obtain ⟨h,eq⟩ := pair_info G ht p.property.1 p.property.2.1 p.property.2.2 small
    exact mem_filter.mpr ⟨h,(congrArg Finset.card eq).trans (card_pair p.property.2.1.ne)⟩⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨w,a,b⟩,vw,ab,x⟩ ⟨⟨w',c,d⟩,vw',cd,x'⟩ e
    obtain rfl : w=w' := congrArg Subtype.val e
    change a<b at ab
    change c<d at cd
    have eq : common G v w = {a,b} := (pair_info G ht vw ab x small).2
    obtain ⟨vc,vd,wc,wd⟩ := x'
    have hc : c ∈ common G v w := by simp [common,vc,wc]
    have hd : d ∈ common G v w := by simp [common,vd,wd]
    rw [eq] at hc hd
    simp only [mem_insert,mem_singleton] at hc hd
    have ac : a=c := by rcases hc with hc|hc <;> rcases hd with hd|hd <;> omega
    have bd : b=d := by rcases hc with hc|hc <;> rcases hd with hd|hd <;> omega
    subst c; subst d; rfl
  have onto : Function.Surjective f := by
    rintro ⟨w,hw⟩
    obtain ⟨hw,cw⟩ := mem_filter.mp hw
    have vw := ((Gᶜ.mem_neighborFinset _ _).mp hw).1
    obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp cw
    have make (i j : Fin 23) (lt : i<j) (hi : i∈common G v w) (hj : j∈common G v w) :
        ∃ p : Rooted G v, (f p).val=w := by
      simp only [common,mem_inter,mem_neighborFinset] at hi hj
      exact ⟨⟨⟨w,i,j⟩,vw,lt,hi.1,hj.1,hi.2,hj.2⟩,rfl⟩
    have ha : a ∈ common G v w := by simp [eq]
    have hb : b ∈ common G v w := by simp [eq]
    rcases lt_or_gt_of_ne ne with ab|ba
    · obtain ⟨p,hp⟩ := make a b ab ha hb
      exact ⟨p,Subtype.ext hp⟩
    · obtain ⟨p,hp⟩ := make b a ba hb ha
      exact ⟨p,Subtype.ext hp⟩
  have e := Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)
  calc
    _ = Nat.card ↥S := e
    _ = S.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = 14 := opposite_count G ht hc reg v small

theorem exists_three_common (ht' : G.CliqueFree 3) (hc' : Gᶜ.CliqueFree 7)
    (regular : ∀ x, G.degree x=6) :
    ∃ v w : Fin 23, w ∈ Gᶜ.neighborFinset v ∧
      3 ≤ ((G.neighborFinset v) ∩ (G.neighborFinset w)).card := by
  classical
  by_contra! all
  have ct (v : Fin 23) := rooted_count G ht' hc' regular v (fun w hw => Nat.le_of_lt_succ (all v w hw))
  have four := incidence_divisible_by_four G
  simp_rw [ct] at four
  norm_num at four
end Census
end Deldor14.RamseyParity
end FourCycles

section SeventeenVertices
/-! The low-degree neighbourhood counting argument adapts @TheWaler's
proof for R(3,9), `RamseyNumbers.ramsey_number_three_nine.R1.H2.R1`, #2943.
The final 17-vertex extension is excluded by exact rational packing bounds.
For one 12-vertex base the argument separates two integer incidences at a fixed vertex.
We verify the extremal bound of Graver and Yackel (1968): a triangle-free
17-vertex graph without an independent set of six has at least 40 edges.
Choose a minimum-degree vertex. Its neighbours are independent. Deleting
it and its neighbours reduces the permitted independence number by one.
To reverse the deletion, choose for each neighbour an independent set of
contacts in the smaller graph. Sorting the contact masks only relabels the
neighbours. The search discards exactly enumerated forbidden independent sets,
vertices of excessive degree, and final graphs below the chosen minimum degree.
An explicit table of adjacent swaps relabels isomorphic intermediate graphs.
For the final search only the 12 graphs of order 12 and the single graph of
order 13 survive. All search and relabelling checks reduce in the kernel.
-/


open SimpleGraph
namespace Deldor14.RamseyDensity
open OMA.RamseyFinite

private def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

private def normalized (g : List Nat) := relabel (renumber g) g

private def roots0 : List (List Nat) := []
private def roots1 : List (List Nat) := []
private def roots2 : List (List Nat) := []
private def roots3 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
private def roots4 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,146,145,3,2,6,3,2,2,1,0],
  [7,24,194,145,3,2,6,3,2,2,1,0],
  [7,280,146,145,3,2,6,3,2,2,1,0],
  [7,280,194,137,3,2,6,3,2,2,1,0],
  [7,24,98,137,3,12,9,3,2,2,1,0],
  [7,132,268,137,3,12,9,3,2,2,1,0],
  [7,196,268,137,3,12,9,3,2,2,1,0],
  [7,388,258,134,3,12,9,3,2,2,1,0],
  [7,388,268,137,3,12,9,3,2,2,1,0],
  [15,296,196,140,73,1,6,3,2,2,1,0],
  [15,352,196,146,82,3,10,10,1,0,1,0]]

private def densityStatement := ∀ (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj],
  G.CliqueFree 3 → Gᶜ.CliqueFree 6 → 40 ≤ G.edgeFinset.card

private def denseRows (g : List Nat) := decide (80 ≤ (degrees g).sum)

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc⟩

theorem density_of_packing (hnum : ∀ d ≤ 4, ∀ b ∈ levels normalized 5 (16-d) 4, ∀ cs, Extension 6 d b cs → 40 ≤ edges_ (attach cs b)) : densityStatement := by
  classical
  intro G inst ht hi
  by_contra! hsmall
  let U : Finset (Fin 17) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI,rfl⟩
  have low : U.Nonempty → ∃ x∈U,(U.filter (G.Adj x)).card≤4 := by
    intro _
    by_contra! hn
    have h5 (x : Fin 17) : 5≤G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s:=U) (f:=fun _=>5) (g:= fun x => G.degree x) (fun x _ => h5 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 17)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs,d,b,cs,hv,cover,hd,hb,hcs,enc⟩ := rootSplitting G ht normalized hn 5 U (by simp [U]) 4 bounded low
  have r := hnum d hd b (by simpa [U] using hb) cs hcs
  rw [← enc] at r
  have dg : degrees (encode G vs)=vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv,cover]
    simp only [U,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 80≤(degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg,← w] at hh
  exact (by change 80 ≤ ∑ i, G.degree i at hh; omega : False)



private abbrev WeightedRow := (Nat × Nat) × Nat

private def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

private def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

private def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat

private def dualCheck (b : List Nat) (d : Nat) (f : Nat → Bool)
    (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide
    (low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x)) &&
  decide ((39 - edges_ b - d) * edgeWeight + cap * extraWeight + rowCapacity W < d * low)

private theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

private theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega

private theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega

private theorem viaDual (b cs : List Nat) (d : Nat) (ext : Extension 6 d b cs)
    (f : Nat → Bool) (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (check : dualCheck b d f cap edgeWeight extraWeight low W = true) (bound : (cs.map (penalty f)).sum ≤ cap) :
    40 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len,mem,good⟩ := ext
  obtain ⟨both,last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid,opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b f edgeWeight extraWeight low W cs
    (fun x hx => of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx)))
  rw [edges_attached,len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 39 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hf := Nat.mul_le_mul_right extraWeight bound
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private theorem complementaryPenalty (f : Nat → Bool) (cs : List Nat) :
    (cs.map (penalty f)).sum + (cs.map (penalty (fun x => !(f x)))).sum = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases eq : f c <;> simp [penalty,eq] at ih ⊢ <;> omega

private theorem zeroPenalty (cs : List Nat) :
    (cs.map (penalty (fun _ => false))).sum ≤ 0 := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    change 0 + (cs.map (penalty (fun _ => false))).sum ≤ 0
    rwa [Nat.zero_add]

private abbrev b3_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
private def b3_0w : List WeightedRow := [((2448,4),3),((1608,4),3),((3096,4),3),((4484,4),3),((204,4),3),((1570,4),3),((306,4),3),((4614,4),3),((30,4),3),((4673,4),3),((2241,4),3),((3105,4),3),((4385,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0cert : dualCheck b3_0 3 (fun _ => false) 0 3 0 24 b3_0w = true := by decide +kernel
private theorem b3_0ok (cs : List Nat) (h : Extension 6 3 b3_0 cs) : 40 ≤ edges_ (attach cs b3_0) := by
  exact viaDual b3_0 cs 3 h (fun _ => false) 0 3 0 24 b3_0w b3_0cert (zeroPenalty cs)

private abbrev b4_0 : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private def b4_0w0 : List WeightedRow := [((1224,4),2),((1576,4),6),((2244,4),2),((2340,4),2),((108,4),2),((786,4),2),((1170,4),4),((1546,4),6),((2310,4),2),((142,4),2),((801,4),2),((1121,4),4),((1553,4),2),((2321,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0cert0 : dualCheck b4_0 4 (fun x => x &&& 2048 == 0) 2 2 8 22 b4_0w0 = true := by decide +kernel
private def b4_0w1 : List WeightedRow := [((1224,4),62),((1576,4),59),((1128,4),2),((2244,4),42),((2340,4),49),((804,4),22),((2148,4),4),((204,4),2),((556,4),2),((108,4),61),((1554,4),2),((2322,4),6),((786,4),59),((2194,4),66),((1546,4),2),((1162,4),2),((2310,4),59),((526,4),59),((142,4),81),((2241,4),44),((2337,4),6),((801,4),64),((2145,4),49),((1121,4),17),((1553,4),59),((2321,4),59),((785,4),4),((2193,4),4),((1169,4),77)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0cert1 : dualCheck b4_0 4 (fun x => !(x &&& 2048 == 0)) 1 62 51 503 b4_0w1 = true := by decide +kernel
private theorem b4_0ok (cs : List Nat) (h : Extension 6 4 b4_0 cs) : 40 ≤ edges_ (attach cs b4_0) := by
  by_cases yes : (cs.map (penalty (fun x => x &&& 2048 == 0))).sum ≤ 2
  · exact viaDual b4_0 cs 4 h (fun x => x &&& 2048 == 0) 2 2 8 22 b4_0w0 b4_0cert0 yes
  · apply viaDual b4_0 cs 4 h (fun x => !(x &&& 2048 == 0)) 1 62 51 503 b4_0w1 b4_0cert1
    have cp := complementaryPenalty (fun x => x &&& 2048 == 0) cs
    rw [h.1] at cp
    omega

private abbrev b4_1 : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private def b4_1w : List WeightedRow := [((2240,3),7),((272,2),22),((144,2),18),((200,3),20),((1224,4),40),((1576,4),39),((1128,4),11),((260,2),18),((2340,4),16),((804,4),27),((2148,4),38),((76,3),20),((556,4),6),((108,4),40),((1554,4),15),((786,4),30),((2194,4),55),((1170,4),16),((1546,4),18),((1162,4),38),((2310,4),55),((14,3),7),((526,4),42),((2241,4),42),((1217,4),6),((2337,4),10),((801,4),27),((2145,4),23),((1121,4),39),((1553,4),27),((2321,4),30),((785,4),18),((1169,4),27)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_1cert : dualCheck b4_1 4 (fun _ => false) 0 71 0 505 b4_1w = true := by decide +kernel
private theorem b4_1ok (cs : List Nat) (h : Extension 6 4 b4_1 cs) : 40 ≤ edges_ (attach cs b4_1) := by
  exact viaDual b4_1 cs 4 h (fun _ => false) 0 71 0 505 b4_1w b4_1cert (zeroPenalty cs)

private abbrev b4_2 : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private def b4_2w : List WeightedRow := [((1224,4),10),((1576,4),17),((2244,4),10),((2340,4),17),((204,4),4),((108,4),13),((786,4),13),((2194,4),7),((1170,4),7),((1546,4),17),((2310,4),17),((14,3),4),((142,4),10),((801,4),13),((2145,4),7),((1121,4),7),((1553,4),10),((2321,4),10),((785,4),4),((2193,4),7),((1169,4),7)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_2cert : dualCheck b4_2 4 (fun _ => false) 0 13 0 102 b4_2w = true := by decide +kernel
private theorem b4_2ok (cs : List Nat) (h : Extension 6 4 b4_2 cs) : 40 ≤ edges_ (attach cs b4_2) := by
  exact viaDual b4_2 cs 4 h (fun _ => false) 0 13 0 102 b4_2w b4_2cert (zeroPenalty cs)

private abbrev b4_3 : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
private def b4_3w : List WeightedRow := [((1168,3),4),((1224,4),11),((1576,4),7),((804,4),7),((2148,4),11),((76,3),4),((108,4),11),((786,4),14),((146,3),4),((2194,4),14),((138,3),7),((2310,4),14),((14,3),4),((526,4),14),((2241,4),7),((2337,4),4),((801,4),4),((1121,4),18),((1553,4),11),((2321,4),7),((1169,4),11)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_3cert : dualCheck b4_3 4 (fun _ => false) 0 14 0 102 b4_3w = true := by decide +kernel
private theorem b4_3ok (cs : List Nat) (h : Extension 6 4 b4_3 cs) : 40 ≤ edges_ (attach cs b4_3) := by
  exact viaDual b4_3 cs 4 h (fun _ => false) 0 14 0 102 b4_3w b4_3cert (zeroPenalty cs)

private abbrev b4_4 : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
private def b4_4w : List WeightedRow := [((1216,3),3),((1544,3),3),((808,4),3),((2244,4),3),((108,4),3),((786,4),3),((146,3),3),((2310,4),3),((14,3),3),((2337,4),3),((1121,4),3),((1553,4),3),((2193,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_4cert : dualCheck b4_4 4 (fun _ => false) 0 3 0 24 b4_4w = true := by decide +kernel
private theorem b4_4ok (cs : List Nat) (h : Extension 6 4 b4_4 cs) : 40 ≤ edges_ (attach cs b4_4) := by
  exact viaDual b4_4 cs 4 h (fun _ => false) 0 3 0 24 b4_4w b4_4cert (zeroPenalty cs)

private abbrev b4_5 : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
private def b4_5w : List WeightedRow := [((144,2),2),((840,4),4),((2212,4),4),((1188,4),2),((1068,4),2),((108,4),4),((2322,4),2),((786,4),2),((1546,4),4),((778,4),2),((2182,4),2),((2369,4),2),((1185,4),2),((2145,4),2),((1553,4),2),((785,4),4)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_5cert : dualCheck b4_5 4 (fun _ => false) 0 4 0 26 b4_5w = true := by decide +kernel
private theorem b4_5ok (cs : List Nat) (h : Extension 6 4 b4_5 cs) : 40 ≤ edges_ (attach cs b4_5) := by
  exact viaDual b4_5 cs 4 h (fun _ => false) 0 4 0 26 b4_5w b4_5cert (zeroPenalty cs)

private abbrev b4_6 : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
private def b4_6w : List WeightedRow := [((2192,3),2),((584,3),2),((840,4),2),((104,3),2),((788,4),3),((148,3),2),((1172,4),2),((1548,4),3),((2370,4),3),((2210,4),3),((1066,4),2),((106,4),2),((1158,4),3),((270,4),3),((833,4),2),((1185,4),3),((2145,4),3),((1553,4),3),((2321,4),3),((2193,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6cert : dualCheck b4_6 4 (fun _ => false) 0 4 0 28 b4_6w = true := by decide +kernel
private theorem b4_6ok (cs : List Nat) (h : Extension 6 4 b4_6 cs) : 40 ≤ edges_ (attach cs b4_6) := by
  exact viaDual b4_6 cs 4 h (fun _ => false) 0 4 0 28 b4_6w b4_6cert (zeroPenalty cs)

private abbrev b4_7 : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
private def b4_7w : List WeightedRow := [((2368,3),5),((840,4),5),((788,4),5),((1172,4),5),((1548,4),5),((2210,4),5),((1186,4),5),((106,4),5),((14,3),5),((2145,4),5),((785,4),5),((2193,4),5)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_7cert : dualCheck b4_7 4 (fun _ => false) 0 0 0 20 b4_7w = true := by decide +kernel
private theorem b4_7ok (cs : List Nat) (h : Extension 6 4 b4_7 cs) : 40 ≤ edges_ (attach cs b4_7) := by
  exact viaDual b4_7 cs 4 h (fun _ => false) 0 0 0 20 b4_7w b4_7cert (zeroPenalty cs)

private abbrev b4_8 : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
private def b4_8w : List WeightedRow := [((792,4),3),((1176,4),3),((836,4),3),((1188,4),3),((1548,4),3),((2370,4),3),((2210,4),3),((102,4),3),((270,4),3),((142,4),3),((833,4),3),((1185,4),3),((2145,4),3),((1553,4),3),((2321,4),3),((2193,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_8cert : dualCheck b4_8 4 (fun _ => false) 0 3 0 24 b4_8w = true := by decide +kernel
private theorem b4_8ok (cs : List Nat) (h : Extension 6 4 b4_8 cs) : 40 ≤ edges_ (attach cs b4_8) := by
  exact viaDual b4_8 cs 4 h (fun _ => false) 0 3 0 24 b4_8w b4_8cert (zeroPenalty cs)

private abbrev b4_9 : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
private def b4_9w : List WeightedRow := [((840,4),3),((1064,3),3),((788,4),3),((1172,4),3),((1548,4),3),((2370,4),3),((2210,4),3),((106,4),3),((134,3),3),((270,4),3),((2369,4),3),((1185,4),3),((2145,4),3),((1553,4),3),((2193,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_9cert : dualCheck b4_9 4 (fun _ => false) 0 3 0 24 b4_9w = true := by decide +kernel
private theorem b4_9ok (cs : List Nat) (h : Extension 6 4 b4_9 cs) : 40 ≤ edges_ (attach cs b4_9) := by
  exact viaDual b4_9 cs 4 h (fun _ => false) 0 3 0 24 b4_9w b4_9cert (zeroPenalty cs)

private abbrev b4_10 : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
private def b4_10w : List WeightedRow := [((1232,4),5),((808,4),5),((1560,4),5),((2244,4),5),((778,4),5),((2310,4),5),((86,4),5),((30,4),5),((2241,4),5),((1569,4),5),((2337,4),5),((1185,4),5)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_10cert : dualCheck b4_10 4 (fun _ => false) 0 0 0 20 b4_10w = true := by decide +kernel
private theorem b4_10ok (cs : List Nat) (h : Extension 6 4 b4_10 cs) : 40 ≤ edges_ (attach cs b4_10) := by
  exact viaDual b4_10 cs 4 h (fun _ => false) 0 0 0 20 b4_10w b4_10cert (zeroPenalty cs)

private abbrev b4_11 : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]
private def b4_11w : List WeightedRow := [((1328,4),2),((1544,3),2),((1176,4),2),((2308,3),2),((404,4),2),((204,4),2),((2594,4),2),((50,3),2),((586,4),2),((2118,4),2),((30,4),2),((1409,4),2),((2625,4),2),((193,3),2),((1569,4),2),((2337,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_11cert : dualCheck b4_11 4 (fun _ => false) 0 4 0 24 b4_11w = true := by decide +kernel
private theorem b4_11ok (cs : List Nat) (h : Extension 6 4 b4_11 cs) : 40 ≤ edges_ (attach cs b4_11) := by
  exact viaDual b4_11 cs 4 h (fun _ => false) 0 4 0 24 b4_11w b4_11cert (zeroPenalty cs)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller0 : (levels normalized 5 16 4).all (fun b => decide (b∈roots0)) = true := by decide +kernel

private theorem root0 {b : List Nat} (hb : b∈levels normalized 5 16 4) (cs : List Nat) (h : Extension 6 0 b cs) : 40 ≤ edges_ (attach cs b) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller0 b hb)
  simp [roots0] at ok

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller1 : (levels normalized 5 15 4).all (fun b => decide (b∈roots1)) = true := by decide +kernel

private theorem root1 {b : List Nat} (hb : b∈levels normalized 5 15 4) (cs : List Nat) (h : Extension 6 1 b cs) : 40 ≤ edges_ (attach cs b) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller1 b hb)
  simp [roots1] at ok

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller2 : (levels normalized 5 14 4).all (fun b => decide (b∈roots2)) = true := by decide +kernel

private theorem root2 {b : List Nat} (hb : b∈levels normalized 5 14 4) (cs : List Nat) (h : Extension 6 2 b cs) : 40 ≤ edges_ (attach cs b) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller2 b hb)
  simp [roots2] at ok

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller3 : (levels normalized 5 13 4).all (fun b => decide (b∈roots3)) = true := by decide +kernel

private theorem root3 {b : List Nat} (hb : b∈levels normalized 5 13 4) (cs : List Nat) (h : Extension 6 3 b cs) : 40 ≤ edges_ (attach cs b) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb)
  simp only [roots3,List.mem_cons,List.not_mem_nil,or_false] at ok
  rcases ok with rfl
  · exact b3_0ok cs h

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller4 : (levels normalized 5 12 4).all (fun b => decide (b∈roots4)) = true := by decide +kernel

private theorem root4 {b : List Nat} (hb : b∈levels normalized 5 12 4) (cs : List Nat) (h : Extension 6 4 b cs) : 40 ≤ edges_ (attach cs b) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb)
  simp only [roots4,List.mem_cons,List.not_mem_nil,or_false] at ok
  rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b4_0ok cs h
  · exact b4_1ok cs h
  · exact b4_2ok cs h
  · exact b4_3ok cs h
  · exact b4_4ok cs h
  · exact b4_5ok cs h
  · exact b4_6ok cs h
  · exact b4_7ok cs h
  · exact b4_8ok cs h
  · exact b4_9ok cs h
  · exact b4_10ok cs h
  · exact b4_11ok cs h

private theorem density_done : densityStatement := by
  apply density_of_packing
  intro d hd b hb cs h
  interval_cases d
  · exact root0 hb cs h
  · exact root1 hb cs h
  · exact root2 hb cs h
  · exact root3 hb cs h
  · exact root4 hb cs h
def Density : Prop := ∀ (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj],
  H.CliqueFree 3 → Hᶜ.CliqueFree 6 → 40 ≤ H.edgeFinset.card

theorem regular (density : Density) : ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
    Gᶜ.CliqueFree 7 → (∀ x,G.degree x=5 ∨ G.degree x=6) → ∀ x,G.degree x=6 := by
  classical
  intro G inst ht hi degrees
  let U : Finset (Fin 23) := Finset.univ
  let L := U.filter fun i => G.degree i = 5
  let low (S : Finset (Fin 23)) := S.filter fun i => G.degree i = 5
  -- Each vertex of degree five contributes one unit below the maximum degree.
  have deficit (S : Finset (Fin 23)) :
      (∑ i ∈ S, G.degree i) + (low S).card = 6 * S.card := by
    have one (i : Fin 23) : G.degree i + (if G.degree i = 5 then 1 else 0) = 6 := by
      rcases degrees i with h | h <;> simp [h]
    have eq := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun i _ => one i)
    simpa [Finset.sum_add_distrib, low, Nat.mul_comm] using eq
  let W (S T : Finset (Fin 23)) := ∑ i ∈ S, ∑ j ∈ T, (if G.Adj i j then 1 else 0 : ℕ)
  have sym (S T) : W S T = W T S := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have split (S T) : W S T + W Sᶜ T = W U T := by
    exact Finset.sum_add_sum_compl S _
  have total (S) : W S U = ∑ i ∈ S, G.degree i := by
    unfold W U
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  -- Counting the edges among the 17 non-neighbours forces a strict majority.
  have majority (v : Fin 23) (hv : G.degree v = 5) :
      L.card < 2 * (low (G.neighborFinset v)).card := by
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    have bcard : B.card = 17 := by
      change Gᶜ.degree v = 17
      rw [G.degree_compl, Fintype.card_fin, hv]
    have lower : 80 ≤ W B B := by
      obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin 17) (s := B) (by simp [bcard])
      have im : (Finset.univ.map f) = B := by
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
          exact hf ⟨i, rfl⟩
        · simp [bcard]
      let H := G.comap f
      let e : H ↪g G := SimpleGraph.Embedding.comap f G
      let ec := SimpleGraph.Embedding.complEquiv e
      have free : Hᶜ.CliqueFree 6 := by
        intro S hs
        have mapped : Gᶜ.IsNClique 6 (S.map f) := by
          refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
          intro x hx y hy hxy
          obtain ⟨i, hi', rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨j, hj', rfl⟩ := Finset.mem_map.mp hy
          exact ec.map_adj_iff.mpr (hs.isClique hi' hj' (fun h => hxy (congrArg f h)))
        apply hi _ (mapped.insert (a := v) ?_)
        intro w hw
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
        exact (Gᶜ.mem_neighborFinset _ _).mp (hf ⟨i, rfl⟩)
      have bound := density H (CliqueFree.comap e.isContained ht) free
      have sumdeg := H.sum_degrees_eq_twice_card_edges
      have count : W B B = ∑ i, H.degree i := by
        unfold W
        rw [← im]
        simp only [Finset.sum_map]
        change (∑ i : Fin 17, ∑ j : Fin 17, (if H.Adj i j then 1 else 0 : ℕ)) = _
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R := ℕ) (H.Adj i) Finset.univ
      omega
    have bsub : B ⊆ Nᶜ := by
      intro i h
      exact Finset.mem_compl.mpr fun hn => ((Gᶜ.mem_neighborFinset _ _).mp h).2
        ((G.mem_neighborFinset _ _).mp hn)
    have inc (S T V : Finset (Fin 23)) (h : S ⊆ T) : W S V ≤ W T V :=
      Finset.sum_le_sum_of_subset_of_nonneg h (by intros; omega)
    have hsub : W B B ≤ W Nᶜ Nᶜ :=
      (inc B Nᶜ B bsub).trans ((sym Nᶜ B) ▸ inc B Nᶜ Nᶜ bsub)
    have zero : W N N = 0 := by
      apply Finset.sum_eq_zero
      intro i hI
      apply Finset.sum_eq_zero
      intro j hJ
      have hh : ¬ G.Adj i j := by
        intro ha
        exact G.isIndepSet_neighborSet_of_triangleFree ht v
          ((G.mem_neighborFinset _ _).mp hI) ((G.mem_neighborFinset _ _).mp hJ) ha.ne ha
      simp [hh]
    have a := split N U
    have b := split N N
    have c := split N Nᶜ
    have s1 := sym Nᶜ U
    have s2 := sym N U
    have s3 := sym Nᶜ N
    have dd := deficit N
    have allD := deficit U
    have nc : N.card = 5 := hv
    have uc : U.card = 23 := by simp [U]
    change (∑ i ∈ U, G.degree i) + L.card = 6 * U.card at allD
    have t1 := total U
    have t2 := total N
    change L.card < 2 * (low N).card
    omega
  intro v
  rcases degrees v with h | h
  · exfalso
    let A := low (G.neighborFinset v)
    have ma : L.card < 2 * A.card := majority v h
    have pos : 0 < A.card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp pos
    obtain ⟨hvn, hw7⟩ := Finset.mem_filter.mp hw
    have adj := (G.mem_neighborFinset _ _).mp hvn
    let D := low (G.neighborFinset w)
    have md : L.card < 2 * D.card := majority w hw7
    -- Adjacent vertices in a triangle-free graph have disjoint neighbourhoods.
    have dis : Disjoint A D := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      have vz := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz).1
      have wz := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz').1
      exact G.isIndepSet_neighborSet_of_triangleFree ht v adj vz wz.ne wz
    have sub : A ∪ D ⊆ L := by
      intro z hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hz with hz | hz <;> exact (Finset.mem_filter.mp hz).2
    have bound := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint dis] at bound
    omega
  · omega

end Deldor14.RamseyDensity
end SeventeenVertices

theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_seven := by
  apply OMA.R_RamseyNumbers_ramsey_number_three_seven_R1.main Deldor14.Ramsey.complete_eighteen
  intro G dec ht degrees _ hi
  have reg := Deldor14.RamseyDensity.regular Deldor14.RamseyDensity.density_done G ht hi degrees
  obtain ⟨v,w,hw,high⟩ := Deldor14.RamseyParity.exists_three_common G ht hi reg
  exact OMA.RamseyFinite.regular_absurd OMA.RamseyFinite.norm2 OMA.RamseyFinite.atlas
    OMA.RamseyFinite.classify16 OMA.RamseyFinite.noextend G ht hi reg v w hw high
    (OMA.RamseyFinite.norm2_real G) (OMA.RamseyFinite.regular_non_neighbors G ht reg v)
