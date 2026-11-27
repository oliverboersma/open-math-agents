import OMAReductions.R_Erdos128_erdos_128_R1_H2_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Sparse halves when an independent set contains at least two fifths of the vertices

Credit: Hanan Beer (@hananzlt), exact-step specialization and verification.
The helper proofs below are reproduced from @iskamag's accepted reduction
`Erdos128.erdos_128.R2`, PR1798, at repository commit
a63eaf8926de7d32e16e008700174318c0fa0fa9. Their mathematical and formalization
attribution remains @iskamag; the independent-set result is attributed there
to Razborov (2021). The target reduction is by @ashnewmanjones, PR4700.

The Formal Conjectures Authors' definitions are reused under Apache-2.0.
This closes one existing auxiliary step and does not settle Erdős 128.
-/

namespace HananBeer.Erdos128Reuse
open Finset SimpleGraph

/-- Exact bridge between induced edgeSet.ncard and Finset directed adjacency sum. -/
lemma two_mul_induce_edgeSet_ncard {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2 * (G.induce (S : Set V)).edgeSet.ncard = ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  classical
  have h1 : (G.induce (S : Set V)).edgeSet.ncard = #(G.induce (S : Set V)).edgeFinset := by
    rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort S (fun u => #(S.filter (G.Adj u)))]
  apply Finset.sum_congr rfl
  intro u _
  rw [SimpleGraph.degree, ← Finset.card_map (Function.Embedding.subtype (· ∈ S))]
  congr 1
  ext v
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj,
    Function.Embedding.coe_subtype, Subtype.exists, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, hadj, rfl⟩
    exact ⟨hw, hadj⟩
  · rintro ⟨hv, hadj⟩
    exact ⟨v, hv, hadj, rfl⟩

/-- Directed edge count in a union of a disjoint independent set I and a set S. -/
lemma sum_adj_union_indep {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I S : Finset V}
    (hdisj : Disjoint I S)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) :
    ∑ u ∈ I ∪ S, #((I ∪ S).filter (G.Adj u)) =
      2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  rw [Finset.sum_union hdisj]
  have hfilter : ∀ u, #((I ∪ S).filter (G.Adj u)) = #(I.filter (G.Adj u)) + #(S.filter (G.Adj u)) := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp_rw [hfilter, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, #(I.filter (G.Adj u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact hI u hu v hv
  have hIS : ∑ u ∈ I, #(S.filter (G.Adj u)) = ∑ w ∈ S, #(I.filter (G.Adj w)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm]
  omega

/-- Number of r-subsets of R containing a fixed element w ∈ R. -/
lemma card_powersetCard_mem {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {w : V} (hw : w ∈ R) (hr : 1 ≤ r) :
    #((R.powersetCard r).filter (w ∈ ·)) = (#R - 1).choose (r - 1) := by
  have hbij : #((R.powersetCard r).filter (w ∈ ·)) = #((R.erase w).powersetCard (r - 1)) := by
    refine Finset.card_bij (fun S _ => S.erase w) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      exact ⟨Finset.erase_subset_erase w hS.1.1, by rw [Finset.card_erase_of_mem hS.2, hS.1.2]⟩
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      rw [← Finset.insert_erase hS₁.2, ← Finset.insert_erase hS₂.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hwT : w ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      refine ⟨insert w T, ?_, Finset.erase_insert hwT⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, and_true]
      refine ⟨Finset.insert_subset hw (hT.1.trans (Finset.erase_subset _ _)), ?_⟩
      rw [Finset.card_insert_of_notMem hwT, hT.2]
      omega
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hw]

/-- Number of r-subsets of R containing two distinct fixed elements u, v ∈ R. -/
lemma card_powersetCard_mem_pair {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {u v : V}
    (hu : u ∈ R) (hv : v ∈ R) (huv : u ≠ v) (hr : 2 ≤ r) :
    #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) = (#R - 2).choose (r - 2) := by
  have hv' : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hbij : #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
      #(((R.erase u).erase v).powersetCard (r - 2)) := by
    refine Finset.card_bij (fun S _ => (S.erase u).erase v) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      have hvS : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS.2.2⟩
      refine ⟨Finset.erase_subset_erase v (Finset.erase_subset_erase u hS.1.1), ?_⟩
      rw [Finset.card_erase_of_mem hvS, Finset.card_erase_of_mem hS.2.1, hS.1.2]
      omega
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      have hv1 : v ∈ S₁.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₁.2.2⟩
      have hv2 : v ∈ S₂.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₂.2.2⟩
      have heq1 : S₁.erase u = S₂.erase u := by
        rw [← Finset.insert_erase hv1, ← Finset.insert_erase hv2, heq]
      rw [← Finset.insert_erase hS₁.2.1, ← Finset.insert_erase hS₂.2.1, heq1]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hvT : v ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      have huT : u ∉ insert v T := by
        intro h
        rcases Finset.mem_insert.mp h with rfl | h'
        · exact huv rfl
        · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 h')).2).1 rfl
      refine ⟨insert u (insert v T), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, or_true, and_true]
        refine ⟨Finset.insert_subset hu (Finset.insert_subset hv
          (hT.1.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))), ?_⟩
        rw [Finset.card_insert_of_notMem huT, Finset.card_insert_of_notMem hvT, hT.2]
        omega
      · rw [Finset.erase_insert huT, Finset.erase_insert hvT]
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu,
    show #R - 1 - 1 = #R - 2 by omega]

/-- Master exact averaging identity over all r-subsets S ⊆ R added to a disjoint independent set I. -/
lemma avg_indep_union_ge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T ≤ 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) ≤
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hsum_le : (#R).choose r * T ≤
      ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard := by
    calc (#R).choose r * T
        = ∑ _S ∈ R.powersetCard r, T := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsum_eq : ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
      2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      (if 2 ≤ r then (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u))) else 0) := by
    have hstep : ∀ S ∈ R.powersetCard r,
        2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
        2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
      intro S hS
      rw [two_mul_induce_edgeSet_ncard]
      exact sum_adj_union_indep G (hdisj.mono_right (Finset.mem_powersetCard.mp hS).1) hI
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · have h1 : ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w)) =
          ∑ w ∈ R, #((R.powersetCard r).filter (w ∈ ·)) * #(I.filter (G.Adj w)) := by
        calc ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w))
            = ∑ S ∈ R.powersetCard r, ∑ w ∈ R, if w ∈ S then #(I.filter (G.Adj w)) else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
          _ = ∑ w ∈ R, ∑ S ∈ R.powersetCard r, if w ∈ S then #(I.filter (G.Adj w)) else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro w _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [h1, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [card_powersetCard_mem R hw hr1]
    · by_cases hr2 : 2 ≤ r
      · rw [if_pos hr2]
        have h2 : ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u)) =
            ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) := by
          calc ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u))
              = ∑ S ∈ R.powersetCard r, ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro S hS
                have hSR := (Finset.mem_powersetCard.mp hS).1
                calc ∑ u ∈ S, #(S.filter (G.Adj u))
                    = ∑ u ∈ R, if u ∈ S then #(S.filter (G.Adj u)) else 0 := by
                      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSR]
                  _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), if u ∈ S ∧ v ∈ S then 1 else 0 := by
                      apply Finset.sum_congr rfl
                      intro u _
                      by_cases hu : u ∈ S
                      · simp only [hu, true_and, if_true, ← Finset.card_filter]
                        congr 1
                        ext v
                        simp only [Finset.mem_filter]
                        exact ⟨fun ⟨hv, hadj⟩ => ⟨⟨hSR hv, hadj⟩, hv⟩, fun ⟨⟨_, hadj⟩, hv⟩ => ⟨hv, hadj⟩⟩
                      · simp [hu]
            _ = ∑ u ∈ R, ∑ S ∈ R.powersetCard r, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := Finset.sum_comm
            _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), ∑ S ∈ R.powersetCard r,
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                exact Finset.sum_comm
            _ = _ := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro v _
                rw [← Finset.card_filter]
        rw [h2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have hinner : ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
            ∑ _v ∈ R.filter (G.Adj u), (#R - 2).choose (r - 2) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hv' := Finset.mem_filter.mp hv
          exact card_powersetCard_mem_pair R hu hv'.1 (G.ne_of_adj hv'.2) hr2
        rw [hinner, Finset.sum_const, smul_eq_mul, mul_comm]
      · rw [if_neg hr2]
        have hr_eq : r = 1 := by omega
        apply Finset.sum_eq_zero
        intro S hS
        have hScard : #S = 1 := by rw [(Finset.mem_powersetCard.mp hS).2, hr_eq]
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hScard
        simp
  rw [hsum_eq] at hsum_le
  have hpos : 0 < (#R).choose r := Nat.choose_pos hrR
  have hc1 : (#R).choose r * r = #R * (#R - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#R - 1) (r - 1)
    rw [show #R - 1 + 1 = #R by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hc2 : 2 ≤ r → (#R).choose r * r * (r - 1) = #R * (#R - 1) * (#R - 2).choose (r - 2) := by
    intro hr2
    have hstep1 : (#R - 1).choose (r - 1) * (r - 1) = (#R - 1) * (#R - 2).choose (r - 2) := by
      have := Nat.add_one_mul_choose_eq (#R - 2) (r - 2)
      rw [show #R - 2 + 1 = #R - 1 by omega, show r - 2 + 1 = r - 1 by omega] at this
      linarith
    calc (#R).choose r * r * (r - 1)
        = (#R * (#R - 1).choose (r - 1)) * (r - 1) := by rw [hc1]
      _ = #R * ((#R - 1).choose (r - 1) * (r - 1)) := by ring
      _ = #R * ((#R - 1) * (#R - 2).choose (r - 2)) := by rw [hstep1]
      _ = #R * (#R - 1) * (#R - 2).choose (r - 2) := by ring
  have hmul := Nat.mul_le_mul_left (#R * (#R - 1)) hsum_le
  by_cases hr2 : 2 ≤ r
  · rw [if_pos hr2] at hmul
    have hkey : (#R).choose r * (T * #R * (#R - 1)) ≤
        (#R).choose r * (2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose r * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose r * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
              (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (r - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            (#R * (#R - 1) * (#R - 2).choose (r - 2)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by ring
        _ = 2 * ((#R).choose r * r) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            ((#R).choose r * r * (r - 1)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by rw [← hc1, ← hc2 hr2]
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hkey hpos
  · rw [if_neg hr2, add_zero] at hmul
    have hr_eq : r = 1 := by omega
    subst hr_eq
    have hkey : (#R).choose 1 * (T * #R * (#R - 1)) ≤
        (#R).choose 1 * (2 * 1 * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          1 * (1 - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose 1 * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose 1 * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (1 - 1) * (∑ w ∈ R, #(I.filter (G.Adj w)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (1 - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by ring
        _ = 2 * ((#R).choose 1 * 1) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by rw [← hc1]
        _ = _ := by simp; ring
    exact Nat.le_of_mul_le_mul_left hkey hpos

/-- Strict version of the master averaging lemma. -/
lemma avg_indep_union_gt {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T < 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) <
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hge := avg_indep_union_ge G hdisj hI hr1 hrR hR2 (fun S hS => Nat.succ_le_of_lt (hbound S hS))
  have hpos : 0 < #R * (#R - 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith

/-- In a triangle-free graph, no three pairwise adjacent vertices exist. -/
lemma not_adj_of_cliqueFree_three {V : Type} {G : SimpleGraph V}
    (hTF : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    False := by
  classical
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_bc : b ≠ c := G.ne_of_adj hbc
  have hne_ac : a ≠ c := G.ne_of_adj hac
  apply hTF {a, b, c}
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hac | exact hac.symm
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne_bc]
    · simp [hne_ab, hne_ac]

/-- In a triangle-free graph, every neighborhood (filtered to any set) is an independent set. -/
lemma filter_adj_indep {V : Type} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (A : Finset V) (v : V) :
    ∀ x ∈ A.filter (G.Adj v), ∀ y ∈ A.filter (G.Adj v), ¬ G.Adj x y := by
  intro x hx y hy hxy
  exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2

/-- Theorem A (Master α < 2n/5 theorem): 12-line elementary all-finite-n proof of Razborov (2021). -/
theorem five_mul_indep_lt_two_mul_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (I₀ : Set V) (hI₀ : G.IsIndepSet I₀) :
    5 * I₀.ncard < 2 * Fintype.card V := by
  classical
  by_contra hge
  push Not at hge
  set n := Fintype.card V
  set k := n / 2
  have hk_cond : ∀ S : Finset V, #S = k → 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
    intro S hS
    apply hH (S : Set V)
    rw [Set.ncard_coe_finset, hS]
    omega
  -- Pick maximum independent Finset I
  let indepSets : Finset (Finset V) :=
    Finset.univ.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hI₀_mem : I₀.toFinset ∈ indepSets := by
    simp only [indepSets, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    intro x hx y hy hadj
    exact hI₀ hx hy (G.ne_of_adj hadj) hadj
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image indepSets Finset.card ⟨I₀.toFinset, hI₀_mem⟩
  have hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := (Finset.mem_filter.mp hI_mem).2
  have hI_le : ∀ J : Finset V, (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) → #J ≤ #I := by
    intro J hJ
    exact hI_max J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  set α := #I
  have h5a : 2 * n ≤ 5 * α := by
    have hcard : I₀.ncard = #I₀.toFinset := Set.ncard_eq_toFinset_card' I₀
    have hle : #I₀.toFinset ≤ α := hI_max I₀.toFinset hI₀_mem
    omega
  -- Step 1: α < k (else k-subset of I has 0 edges)
  have hα_lt_k : α < k := by
    by_contra hka
    push Not at hka
    obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq hka
    have hpos := hk_cond S hScard
    have hzero : 2 * (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hI u (hSI hu) v (hSI hv)
    omega
  set r := k - α
  have hr1 : 1 ≤ r := by omega
  have hα_pos : 0 < α := by omega
  -- Step 2: every k-subset has 2 * e > α * r
  have h_gt_ar : ∀ S : Finset V, #S = k → α * r < 2 * (G.induce (S : Set V)).edgeSet.ncard := by
    intro S hS
    have h50 := hk_cond S hS
    have h50ar : 50 * (α * r) ≤ 2 * n ^ 2 := by
      have h2r : 2 * r + 2 * α ≤ n := by omega
      have h1 : (0 : ℤ) ≤ (5 * (α : ℤ) - 2 * n) * (10 * α - n) :=
        mul_nonneg (by omega) (by omega)
      zify
      nlinarith
    omega
  -- Step 3: Partition V \ I into R₁ (high deg into I) and R₀ (low deg into I)
  let R₁ : Finset V := (Finset.univ \ I).filter (fun v => α < 2 * #(I.filter (G.Adj v)))
  let R₀ : Finset V := (Finset.univ \ I).filter (fun v => 2 * #(I.filter (G.Adj v)) ≤ α)
  have hR₁_indep : ∀ u ∈ R₁, ∀ v ∈ R₁, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    have hdisj : Disjoint (I.filter (G.Adj u)) (I.filter (G.Adj v)) := by
      rw [Finset.disjoint_left]
      intro x hxu hxv
      exact not_adj_of_cliqueFree_three hTF huv (Finset.mem_filter.mp hxv).2 (Finset.mem_filter.mp hxu).2
    have hunion : #(I.filter (G.Adj u)) + #(I.filter (G.Adj v)) ≤ #I := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  set m₁ := #R₁
  set m₀ := #R₀
  have hm₁_le : m₁ ≤ α := hI_le R₁ hR₁_indep
  have hdisj_IR₀ : Disjoint I R₀ := by
    rw [Finset.disjoint_left]
    intro x hx hx0
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx0).1).2 hx
  have hdisj_IR₁ : Disjoint I R₁ := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2 hx
  have hdisj_R₁R₀ : Disjoint R₁ R₀ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx0
    have h1 := (Finset.mem_filter.mp hx1).2
    have h0 := (Finset.mem_filter.mp hx0).2
    omega
  have hpart : α + m₁ + m₀ = n := by
    have hR : m₁ + m₀ = #(Finset.univ \ I) := by
      rw [← Finset.card_union_of_disjoint hdisj_R₁R₀]
      congr 1
      ext x
      simp only [R₁, R₀, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h : α < 2 * #(I.filter (G.Adj x))
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hsdiff : #(Finset.univ \ I) + α = n := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
    omega
  set r₁ := k - m₁
  have hr_le_r₁ : r ≤ r₁ := by omega
  have hr_sum : r + r₁ ≤ m₀ := by omega
  have hm₀_ge_2r : 2 * r ≤ m₀ := by omega
  -- Step 4: Max independent subset J ⊆ R₀
  let indepR₀ : Finset (Finset V) :=
    R₀.powerset.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hEmpty_R₀ : (∅ : Finset V) ∈ indepR₀ := by
    simp [indepR₀]
  obtain ⟨J, hJ_mem, hJ_max⟩ := Finset.exists_max_image indepR₀ Finset.card ⟨∅, hEmpty_R₀⟩
  have hJ_sub : J ⊆ R₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
  have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := (Finset.mem_filter.mp hJ_mem).2
  set β := #J
  -- Case 1: r ≤ β
  by_cases hβ : r ≤ β
  · obtain ⟨S, hSJ, hScard⟩ := Finset.exists_subset_card_eq hβ
    have hSR₀ : S ⊆ R₀ := hSJ.trans hJ_sub
    have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := fun x hx y hy => hJ_indep x (hSJ hx) y (hSJ hy)
    have hcard_IS : #(I ∪ S) = k := by
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right hSR₀), hScard]
      omega
    have hgt := h_gt_ar (I ∪ S) hcard_IS
    rw [two_mul_induce_edgeSet_ncard, sum_adj_union_indep G (hdisj_IR₀.mono_right hSR₀) hI] at hgt
    have hSS : ∑ u ∈ S, #(S.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hS_indep u hu v hv
    have hIS : 2 * ∑ w ∈ S, #(I.filter (G.Adj w)) ≤ r * α := by
      calc 2 * ∑ w ∈ S, #(I.filter (G.Adj w))
          = ∑ w ∈ S, 2 * #(I.filter (G.Adj w)) := Finset.mul_sum _ _ _
        _ ≤ ∑ _w ∈ S, α := Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp (hSR₀ hw)).2)
        _ = r * α := by rw [Finset.sum_const, hScard, smul_eq_mul]
    nlinarith
  -- Case 2: β < r
  · push Not at hβ
    -- Show 1 ≤ β (hence 2 ≤ r and 4 ≤ m₀)
    have hβ_pos : 1 ≤ β := by
      have hm₀_pos : 0 < #R₀ := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hm₀_pos
      have hw_mem : ({w} : Finset V) ∈ indepR₀ := by
        simp only [indepR₀, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
          Finset.mem_singleton]
        refine ⟨hw, ?_⟩
        rintro _ rfl _ rfl
        exact G.loopless.irrefl _
      have := hJ_max {w} hw_mem
      simpa using this
    have hr2 : 2 ≤ r := by omega
    have hm₀2 : 2 ≤ m₀ := by omega
    set e₁ := ∑ w ∈ R₀, #(I.filter (G.Adj w))
    set e₂ := ∑ w ∈ R₀, #(R₁.filter (G.Adj w))
    set d₀ := ∑ u ∈ R₀, #(R₀.filter (G.Adj u))
    -- (F1): e₁ + e₂ + d₀ ≤ m₀ * α
    have hF1 : e₁ + e₂ + d₀ ≤ m₀ * α := by
      have hsum : e₁ + e₂ + d₀ =
          ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w))) := by
        simp only [e₁, e₂, d₀, Finset.sum_add_distrib]
      rw [hsum]
      calc ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w)))
          ≤ ∑ _w ∈ R₀, α := by
            apply Finset.sum_le_sum
            intro w _
            have hd1 : Disjoint (I.filter (G.Adj w)) (R₁.filter (G.Adj w)) :=
              hdisj_IR₁.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            have hd2 : Disjoint (I.filter (G.Adj w) ∪ R₁.filter (G.Adj w)) (R₀.filter (G.Adj w)) :=
              (Finset.disjoint_union_left.mpr ⟨hdisj_IR₀, hdisj_R₁R₀⟩).mono
                (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                (Finset.filter_subset _ _)
            rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
            have hsub : I.filter (G.Adj w) ∪ R₁.filter (G.Adj w) ∪ R₀.filter (G.Adj w) ⊆
                Finset.univ.filter (G.Adj w) := by
              intro x hx
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rcases hx with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ <;> exact h
            exact (Finset.card_le_card hsub).trans (hI_le _ (filter_adj_indep hTF Finset.univ w))
        _ = m₀ * α := by rw [Finset.sum_const, smul_eq_mul]
    -- (F2): e₁ ≤ α * (r - 1)
    have hF2 : e₁ ≤ α * (r - 1) := by
      have hswap : e₁ = ∑ x ∈ I, #(R₀.filter (G.Adj x)) := by
        simp only [e₁, Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro w _
        simp [G.adj_comm]
      rw [hswap]
      calc ∑ x ∈ I, #(R₀.filter (G.Adj x))
          ≤ ∑ _x ∈ I, (r - 1) := by
            apply Finset.sum_le_sum
            intro x _
            have hmem : R₀.filter (G.Adj x) ∈ indepR₀ :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
                filter_adj_indep hTF R₀ x⟩
            have hle := hJ_max _ hmem
            omega
        _ = α * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
    -- (F3): averaging over r-subsets S ⊆ R₀ added to I
    have hF3_raw : α * r * m₀ * (m₀ - 1) < 2 * r * (m₀ - 1) * e₁ + r * (r - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_IR₀ hI hr1 (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (I ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    have hF3 : α * m₀ * (m₀ - 1) < 2 * (m₀ - 1) * e₁ + (r - 1) * d₀ := by
      have hrpos : 0 < r := by omega
      nlinarith
    -- (F4): averaging over r₁-subsets S' ⊆ R₀ added to R₁
    have hF4 : α * r * m₀ * (m₀ - 1) < 2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_R₁R₀ hR₁_indep (by omega) (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (R₁ ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_R₁R₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    -- Exact integer cancellation ending in d² + (r+d)*s + 2r + 3d > 0
    have hfinal : False := by
      have hA : (0 : ℤ) < (α : ℤ) := Nat.cast_pos.mpr hα_pos
      have hR : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr2
      have hRR1 : (r : ℤ) ≤ (r₁ : ℤ) := Nat.cast_le.mpr hr_le_r₁
      have hsumR : (r : ℤ) + (r₁ : ℤ) ≤ (m₀ : ℤ) := by exact_mod_cast hr_sum
      have hD0 : (0 : ℤ) ≤ (d₀ : ℤ) := Nat.cast_nonneg d₀
      have h1z : (e₁ : ℤ) + (e₂ : ℤ) + (d₀ : ℤ) ≤ (m₀ : ℤ) * (α : ℤ) := by exact_mod_cast hF1
      have h2z : (e₁ : ℤ) ≤ (α : ℤ) * ((r : ℤ) - 1) := by
        have : (e₁ : ℤ) ≤ ((α * (r - 1) : ℕ) : ℤ) := Nat.cast_le.mpr hF2
        rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this
        simpa using this
      have h3z : (α : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * ((m₀ : ℤ) - 1) * (e₁ : ℤ) + ((r : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * m₀ * (m₀ - 1) : ℕ) : ℤ) < ((2 * (m₀ - 1) * e₁ + (r - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF3
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r by omega)] at this
        simpa using this
      have h4z : (α : ℤ) * (r : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * (r₁ : ℤ) * ((m₀ : ℤ) - 1) * (e₂ : ℤ) + (r₁ : ℤ) * ((r₁ : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * r * m₀ * (m₀ - 1) : ℕ) : ℤ) <
            ((2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF4
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r₁ by omega)] at this
        simpa using this
      set A : ℤ := (α : ℤ)
      set M : ℤ := (m₀ : ℤ)
      set R : ℤ := (r : ℤ)
      set R1 : ℤ := (r₁ : ℤ)
      set E1 : ℤ := (e₁ : ℤ)
      set E2 : ℤ := (e₂ : ℤ)
      set D0 : ℤ := (d₀ : ℤ)
      have hM1 : 0 < M - 1 := by linarith
      have hMpos : 0 < M := by linarith
      have hR1pos : 0 < R1 := by linarith
      have hR1m : 0 < R - 1 := by linarith
      have hw1 : 0 < R1 * (M + R - 1) := mul_pos hR1pos (by linarith)
      have hc1 := mul_lt_mul_of_pos_left h3z hw1
      have hc2 := mul_lt_mul_of_pos_left h4z hR1m
      have hadd : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) <
          R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) := add_lt_add hc1 hc2
      have hnn1 : 0 ≤ 2 * (M - 1) * R1 * (R - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hR1m.le
      have hnn2 : 0 ≤ 2 * (M - 1) * R1 * M :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hMpos.le
      have hnn3 : 0 ≤ (R - 1) * R1 * D0 :=
        mul_nonneg (mul_nonneg hR1m.le hR1pos.le) hD0
      have hterm1 : 2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) ≤
          2 * (M - 1) * R1 * (R - 1) * (M * A) := mul_le_mul_of_nonneg_left h1z hnn1
      have hterm2 : 2 * (M - 1) * R1 * M * E1 ≤ 2 * (M - 1) * R1 * M * (A * (R - 1)) :=
        mul_le_mul_of_nonneg_left h2z hnn2
      have hterm3 : (R - 1) * R1 * D0 * (R + R1 - M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnn3 (by linarith)
      have hrhs : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) ≤
          4 * A * M * (M - 1) * R1 * (R - 1) := by
        have hid : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
            (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) =
            2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) +
            2 * (M - 1) * R1 * M * E1 +
            (R - 1) * R1 * D0 * (R + R1 - M) := by ring
        have hsum4 : 2 * (M - 1) * R1 * (R - 1) * (M * A) +
            2 * (M - 1) * R1 * M * (A * (R - 1)) = 4 * A * M * (M - 1) * R1 * (R - 1) := by ring
        linarith
      have hcore : 0 < R1 * (M - 3 * R + 3) + R * (R - 1) := by
        have hdecomp : R1 * (M - 3 * R + 3) + R * (R - 1) =
            (R1 - R) ^ 2 + R1 * (M - R - R1) + 2 * R + 3 * (R1 - R) := by ring
        have hnonneg1 : 0 ≤ (R1 - R) ^ 2 := sq_nonneg _
        have hnonneg2 : 0 ≤ R1 * (M - R - R1) := mul_nonneg hR1pos.le (by linarith)
        linarith
      have hlhs : 4 * A * M * (M - 1) * R1 * (R - 1) <
          R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) := by
        have hid2 : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) -
            4 * A * M * (M - 1) * R1 * (R - 1) =
            (A * M * (M - 1)) * (R1 * (M - 3 * R + 3) + R * (R - 1)) := by ring
        have hpos_f : 0 < A * M * (M - 1) := mul_pos (mul_pos hA hMpos) hM1
        have := mul_pos hpos_f hcore
        linarith
      linarith
    exact hfinal

end HananBeer.Erdos128Reuse

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R1_H2_R1_H2_R1.H1 := by
  classical
  intro V _ G hTF _ _ _ hlarge _
  obtain ⟨I, hI, hsize⟩ := hlarge
  by_contra hnone
  have hdense : ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce S).edgeSet.ncard > Fintype.card V ^ 2 := by
    intro S hS
    by_contra hle
    exact hnone ⟨S, hS, by omega⟩
  have hlt := HananBeer.Erdos128Reuse.five_mul_indep_lt_two_mul_card G hTF hdense I hI
  omega
