import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1
import Mathlib

/-!
Local deletion bound for the Havel-Hakimi residue.
Adapted from the proof of Arxiv.2507.17780.tx_graffiti_conjecture_1 by
@irwincollin, merged in pull request 2789 (commit 4ceed91). The inequality
is that proof's valid_and_residue_le_delete_max.
-/

namespace OMA.TxG1

open Finset

/- Section 3: Havel-Hakimi Residue Bound -/

/-- A list of natural numbers is sorted in non-increasing order. -/
def SortedDesc (L : List ℕ) : Prop := L.Pairwise (· ≥ ·)

/-- One Havel-Hakimi reduction step applied to the tail `L` given head `d`. -/
def decTop (d : ℕ) (L : List ℕ) : List ℕ :=
  ((L.take d).map (· - 1) ++ L.drop d).mergeSort (· ≥ ·)

theorem havelHakimiStep_eq_decTop (d : ℕ) (r : List ℕ) :
    SimpleGraph.havelHakimiStep (d :: r) = decTop d r := by
  simp [SimpleGraph.havelHakimiStep, decTop]

theorem sortedDesc_mergeSort (L : List ℕ) : SortedDesc (L.mergeSort (· ≥ ·)) := by
  have htrans : ∀ a b c : ℕ, decide (a ≥ b) = true → decide (b ≥ c) = true →
      decide (a ≥ c) = true := fun a b c => by simp; omega
  have htot : ∀ a b : ℕ, (decide (a ≥ b) || decide (b ≥ a)) = true := fun a b => by
    simp; omega
  have hpw := List.pairwise_mergeSort htrans htot L
  exact hpw.imp fun {a b} h => by simpa using h

theorem sortedDesc_decTop (d : ℕ) (L : List ℕ) : SortedDesc (decTop d L) :=
  sortedDesc_mergeSort _

theorem multiset_decTop (d : ℕ) (L : List ℕ) :
    (decTop d L : Multiset ℕ) = ((L.take d).map (· - 1) : Multiset ℕ) + (L.drop d : Multiset ℕ) := by
  rw [decTop]
  have hp := Multiset.coe_eq_coe.mpr (List.mergeSort_perm ((L.take d).map (· - 1) ++ L.drop d) (· ≥ ·))
  rw [hp, ← Multiset.coe_add]

theorem length_decTop (d : ℕ) (L : List ℕ) : (decTop d L).length = L.length := by
  simp [decTop, List.length_mergeSort, List.length_append, List.length_map,
    List.length_take, List.length_drop]
  omega

theorem sortedDesc_eq_of_coe {A B : List ℕ} (hA : SortedDesc A) (hB : SortedDesc B)
    (hM : (A : Multiset ℕ) = (B : Multiset ℕ)) : A = B :=
  (Multiset.coe_eq_coe.mp hM).eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h2 h1) hA hB

theorem exists_sortedDesc_of_multiset (M : Multiset ℕ) :
    ∃ L : List ℕ, SortedDesc L ∧ (L : Multiset ℕ) = M := by
  refine Quotient.inductionOn M fun l => ?_
  refine ⟨l.mergeSort (· ≥ ·), sortedDesc_mergeSort l, ?_⟩
  exact Multiset.coe_eq_coe.mpr (List.mergeSort_perm l (· ≥ ·))

theorem sortedDesc_tail {a : ℕ} {r : List ℕ} (h : SortedDesc (a :: r)) : SortedDesc r :=
  (List.pairwise_cons.mp h).2

theorem sortedDesc_head_ge {a : ℕ} {r : List ℕ} (h : SortedDesc (a :: r)) :
    ∀ x ∈ r, x ≤ a :=
  (List.pairwise_cons.mp h).1

theorem sortedDesc_antitone {A : List ℕ} (hA : SortedDesc A) {i j : ℕ}
    (hij : i ≤ j) (hj : j < A.length) : A[j] ≤ A[i] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp hA i j (by omega) hj hlt

theorem getD_eq_getElem {A : List ℕ} {i : ℕ} (hi : i < A.length) : A.getD i 0 = A[i] := by
  induction A generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i => exact ih (by simpa using hi)

theorem getD_of_length_le {A : List ℕ} {i : ℕ} (hi : A.length ≤ i) : A.getD i 0 = 0 := by
  induction A generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp at hi
    | succ i => exact ih (by simpa using hi)

theorem getD_cons_pred {d : ℕ} {r : List ℕ} (hd : 1 ≤ d) :
    (d :: r).getD d 0 = r.getD (d - 1) 0 := by
  cases d with
  | zero => omega
  | succ d => simp

theorem sortedDesc_getD_antitone {A : List ℕ} (hA : SortedDesc A) {i j : ℕ}
    (hij : i ≤ j) : A.getD j 0 ≤ A.getD i 0 := by
  by_cases hj : j < A.length
  · rw [getD_eq_getElem (by omega : i < A.length), getD_eq_getElem hj]
    exact sortedDesc_antitone hA hij hj
  · rw [getD_of_length_le (by omega)]
    exact Nat.zero_le _

theorem list_split_getElem (A : List ℕ) (i v : ℕ) (hi : i < A.length) :
    A = A.take i ++ A[i] :: A.drop (i + 1) ∧ A.set i v = A.take i ++ v :: A.drop (i + 1) := by
  induction A generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i =>
      obtain ⟨h1, h2⟩ := ih i (by simpa using hi)
      refine ⟨?_, ?_⟩
      · exact congrArg (a :: ·) h1
      · simp [h2]

theorem multiset_split_set (A : List ℕ) (i v : ℕ) (hi : i < A.length) :
    ∃ M : Multiset ℕ, (A : Multiset ℕ) = A[i] ::ₘ M ∧ ((A.set i v : List ℕ) : Multiset ℕ) = v ::ₘ M := by
  obtain ⟨h1, h2⟩ := list_split_getElem A i v hi
  refine ⟨((A.take i ++ A.drop (i + 1) : List ℕ) : Multiset ℕ), ?_, ?_⟩
  · calc (A : Multiset ℕ)
        = ↑(A.take i ++ A[i] :: A.drop (i + 1)) := congrArg (Coe.coe : List ℕ → Multiset ℕ) h1
      _ = (A.take i : Multiset ℕ) + (A[i] ::ₘ (A.drop (i + 1) : Multiset ℕ)) := by
          rw [← Multiset.coe_add]; rfl
      _ = A[i] ::ₘ ((A.take i : Multiset ℕ) + (A.drop (i + 1) : Multiset ℕ)) := by
          rw [Multiset.add_cons]
      _ = A[i] ::ₘ ((A.take i ++ A.drop (i + 1) : List ℕ) : Multiset ℕ) := by
          rw [← Multiset.coe_add]
  · calc ((A.set i v : List ℕ) : Multiset ℕ)
        = ↑(A.take i ++ v :: A.drop (i + 1)) := congrArg (Coe.coe : List ℕ → Multiset ℕ) h2
      _ = (A.take i : Multiset ℕ) + (v ::ₘ (A.drop (i + 1) : Multiset ℕ)) := by
          rw [← Multiset.coe_add]; rfl
      _ = v ::ₘ ((A.take i : Multiset ℕ) + (A.drop (i + 1) : Multiset ℕ)) := by
          rw [Multiset.add_cons]
      _ = v ::ₘ ((A.take i ++ A.drop (i + 1) : List ℕ) : Multiset ℕ) := by
          rw [← Multiset.coe_add]

theorem take_set_list (A : List ℕ) (i d v : ℕ) :
    (A.set i v).take d = if i < d then (A.take d).set i v else A.take d := by
  induction A generalizing i d with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero =>
      cases d with
      | zero => simp
      | succ d => simp
    | succ i =>
      cases d with
      | zero => simp
      | succ d =>
        simp only [List.set_cons_succ, List.take_succ_cons, ih i d]
        by_cases h : i < d <;> simp [h]

theorem drop_set_list (A : List ℕ) (i d v : ℕ) :
    (A.set i v).drop d = if i < d then A.drop d else (A.drop d).set (i - d) v := by
  induction A generalizing i d with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero =>
      cases d with
      | zero => simp
      | succ d => simp
    | succ i =>
      cases d with
      | zero => simp
      | succ d =>
        simp only [List.set_cons_succ, List.drop_succ_cons, ih i d]
        by_cases h : i < d <;> simp [h]

theorem take_succ_getElem (A : List ℕ) (d : ℕ) (hd : d < A.length) :
    A.take (d + 1) = A.take d ++ [A[d]] := by
  induction A generalizing d with
  | nil => simp at hd
  | cons a t ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ,
        List.cons.injEq, true_and]
      exact ih d (by simpa using hd)

theorem drop_eq_cons_getElem (A : List ℕ) (d : ℕ) (hd : d < A.length) :
    A.drop d = A[d] :: A.drop (d + 1) := by
  induction A generalizing d with
  | nil => simp at hd
  | cons a t ih =>
    cases d with
    | zero => simp
    | succ d => exact ih d (by simpa using hd)

theorem getD_set_list (A : List ℕ) (i v k : ℕ) :
    (A.set i v).getD k 0 = if k = i ∧ i < A.length then v else A.getD k 0 := by
  by_cases hk : k < A.length
  · have hk' : k < (A.set i v).length := by simpa using hk
    rw [getD_eq_getElem hk', getD_eq_getElem hk]
    by_cases hki : k = i
    · subst hki; simp [hk]
    · simp [hki, List.getElem_set_ne (Ne.symm hki)]
  · have hk' : (A.set i v).length ≤ k := by simpa using Nat.le_of_not_lt hk
    rw [getD_of_length_le hk', getD_of_length_le (Nat.le_of_not_lt hk)]
    split_ifs with h
    · omega
    · rfl

/-- Valid descending sequences for the Havel-Hakimi recurrence. -/
def Valid : List ℕ → Prop
  | [] => True
  | 0 :: _ => True
  | (d + 1) :: rest =>
    d + 1 ≤ rest.length ∧ (∀ x ∈ rest.take (d + 1), 1 ≤ x) ∧ Valid (decTop (d + 1) rest)
termination_by L => L.length
decreasing_by simp_wf; rw [length_decTop]

/-- Peeled-head sequence produced by Havel-Hakimi reduction. -/
def E : List ℕ → List ℕ
  | [] => []
  | 0 :: rest => 0 :: List.replicate rest.length 0
  | (d + 1) :: rest => (d + 1) :: E (decTop (d + 1) rest)
termination_by L => L.length
decreasing_by simp_wf; rw [length_decTop]

theorem length_E (L : List ℕ) : (E L).length = L.length := by
  match L with
  | [] => rw [E.eq_1]
  | 0 :: rest => rw [E.eq_2]; simp
  | (d + 1) :: rest =>
    rw [E.eq_3]
    simp [length_E (decTop (d + 1) rest), length_decTop]
termination_by L.length
decreasing_by simp_wf; rw [length_decTop]

theorem E_of_all_zero {L : List ℕ} (h : ∀ x ∈ L, x = 0) : E L = List.replicate L.length 0 := by
  cases L with
  | nil => rw [E.eq_1]; simp
  | cons a r =>
    have ha : a = 0 := h a (by simp)
    subst ha
    rw [E.eq_2]
    simp [List.replicate_succ]

theorem E_cons_of_sortedDesc {d : ℕ} {r : List ℕ} (h : SortedDesc (d :: r)) :
    E (d :: r) = d :: E (decTop d r) := by
  cases d with
  | zero =>
    have hr0 : ∀ x ∈ r, x = 0 := fun x hx => Nat.eq_zero_of_le_zero (sortedDesc_head_ge h x hx)
    have hdec0 : decTop 0 r = r := by
      apply sortedDesc_eq_of_coe (sortedDesc_decTop 0 r) (sortedDesc_tail h)
      rw [multiset_decTop]
      simp
    rw [hdec0, E_of_all_zero hr0, E.eq_2]
  | succ d => rw [E.eq_3]

theorem valid_decTop_zero {r : List ℕ} (h : SortedDesc (0 :: r)) : Valid (decTop 0 r) := by
  have hdec0 : decTop 0 r = r := by
    apply sortedDesc_eq_of_coe (sortedDesc_decTop 0 r) (sortedDesc_tail h)
    rw [multiset_decTop]
    simp
  rw [hdec0]
  cases r with
  | nil => rw [Valid.eq_1]; trivial
  | cons a t =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero (sortedDesc_head_ge h a (by simp))
    subst ha
    rw [Valid.eq_2]; trivial

theorem valid_take_le {d : ℕ} {r : List ℕ} (hV : Valid (d :: r)) :
    d ≤ r.length ∧ (∀ x ∈ r.take d, 1 ≤ x) ∧ (SortedDesc (d :: r) → Valid (decTop d r)) := by
  cases d with
  | zero =>
    refine ⟨Nat.zero_le _, by simp, fun hs => valid_decTop_zero hs⟩
  | succ d =>
    rw [Valid.eq_3] at hV
    exact ⟨hV.1, hV.2.1, fun _ => hV.2.2⟩

theorem E_residue_partition : ∀ (n : ℕ) (L : List ℕ), L.length = n → SortedDesc L → Valid L →
    SimpleGraph.residueAux L ≤ L.length ∧
    (∀ x ∈ (E L).take (L.length - SimpleGraph.residueAux L), 1 ≤ x) ∧
    (∀ x ∈ (E L).drop (L.length - SimpleGraph.residueAux L), x = 0) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih L hlen hS hV
  cases L with
  | nil =>
    rw [SimpleGraph.residueAux.eq_1, E.eq_1]
    simp
  | cons d r =>
    cases d with
    | zero =>
      rw [SimpleGraph.residueAux.eq_2, E.eq_2]
      simp; omega
    | succ d =>
      rw [SimpleGraph.residueAux.eq_3 (d + 1) r (by omega), havelHakimiStep_eq_decTop, E.eq_3]
      have hlt : (decTop (d + 1) r).length < n := by rw [length_decTop, ← hlen]; simp
      have hV' := (valid_take_le hV).2.2 hS
      obtain ⟨h1, h2, h3⟩ := ih (decTop (d + 1) r).length hlt (decTop (d + 1) r) rfl
        (sortedDesc_decTop (d + 1) r) hV'
      rw [length_decTop] at h1 h2 h3
      have hsub : ((d + 1) :: r).length - SimpleGraph.residueAux (decTop (d + 1) r) =
          (r.length - SimpleGraph.residueAux (decTop (d + 1) r)) + 1 := by
        simp only [List.length_cons]; omega
      refine ⟨by simp; omega, ?_, ?_⟩
      · rw [hsub, List.take_succ_cons]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact h2 x hx'
      · rw [hsub, List.drop_succ_cons]
        exact h3

theorem sum_eq_zero_of_all_zero {L : List ℕ} (h : ∀ x ∈ L, x = 0) : L.sum = 0 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp [h a (by simp), ih fun z hz => h z (by simp [hz])]

/-- Prefix-sum dominance between two lists of equal length and sum. -/
def DomLe (A B : List ℕ) : Prop :=
  A.length = B.length ∧ A.sum = B.sum ∧ ∀ k, (A.take k).sum ≤ (B.take k).sum

theorem residue_le_of_domLe {X Y : List ℕ} (hSX : SortedDesc X) (hSY : SortedDesc Y)
    (hVX : Valid X) (hVY : Valid Y) (hDom : DomLe (E X) (E Y)) :
    SimpleGraph.residueAux X ≤ SimpleGraph.residueAux Y := by
  obtain ⟨rX_le, hX_pos, hX_zero⟩ := E_residue_partition X.length X rfl hSX hVX
  obtain ⟨rY_le, hY_pos, hY_zero⟩ := E_residue_partition Y.length Y rfl hSY hVY
  have hXYlen : X.length = Y.length := by
    have := hDom.1
    rwa [length_E, length_E] at this
  by_contra hlt
  have hr : SimpleGraph.residueAux Y < SimpleGraph.residueAux X := Nat.lt_of_not_le hlt
  let kX := X.length - SimpleGraph.residueAux X
  let kY := Y.length - SimpleGraph.residueAux Y
  have hklt : kX < kY := by omega
  have hEX_split : (E X).sum = ((E X).take kX).sum + ((E X).drop kX).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hEX_drop0 : ((E X).drop kX).sum = 0 := sum_eq_zero_of_all_zero hX_zero
  have hEY_split : (E Y).sum = ((E Y).take kX).sum + ((E Y).drop kX).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hk_sum : ((E X).take kX).sum ≤ ((E Y).take kX).sum := hDom.2.2 kX
  have hEY_drop0 : ((E Y).drop kX).sum = 0 := by
    have hsum := hDom.2.1
    omega
  have hkX_lt_EY : kX < (E Y).length := by rw [length_E]; omega
  have hmem_drop : (E Y)[kX] ∈ (E Y).drop kX := by
    rw [drop_eq_cons_getElem (E Y) kX hkX_lt_EY]
    exact List.mem_cons_self
  have helem0 : (E Y)[kX] = 0 := by
    have hle := List.le_sum_of_mem hmem_drop
    omega
  have hmem_take : (E Y)[kX] ∈ (E Y).take kY := by
    have hkY_le : kY ≤ (E Y).length := by rw [length_E]; omega
    rw [List.mem_iff_getElem]
    refine ⟨kX, ?_, ?_⟩
    · rw [List.length_take]; omega
    · simp [List.getElem_take]
  have hge1 := hY_pos (E Y)[kX] hmem_take
  omega

/-- Single-element increment by `1` between sorted descending lists. -/
def Inc1 (A B : List ℕ) (x : ℕ) : Prop :=
  SortedDesc A ∧ SortedDesc B ∧ ∃ M : Multiset ℕ,
    (A : Multiset ℕ) = x ::ₘ M ∧ (B : Multiset ℕ) = (x + 1) ::ₘ M

/-- Single-element decrement by `1` between sorted descending lists. -/
def Dec1 (A B : List ℕ) (y : ℕ) : Prop :=
  1 ≤ y ∧ Inc1 B A (y - 1)

theorem inc1_length {A B : List ℕ} {x : ℕ} (h : Inc1 A B x) : A.length = B.length := by
  obtain ⟨_, _, M, hA, hB⟩ := h
  have := congrArg Multiset.card hA
  have := congrArg Multiset.card hB
  simp only [Multiset.coe_card, Multiset.card_cons] at *
  omega

theorem dec1_length {A B : List ℕ} {y : ℕ} (h : Dec1 A B y) : A.length = B.length :=
  (inc1_length h.2).symm

theorem inc1_eq_set {A B : List ℕ} {x : ℕ} (h : Inc1 A B x) :
    ∃ i, ∃ hi : i < A.length, A[i] = x ∧ (∀ j (hj : j < i), x < A[j]'(by omega)) ∧ B = A.set i (x + 1) := by
  obtain ⟨hSA, hSB, M, hMA, hMB⟩ := h
  have hx_mem : x ∈ A := by
    have : x ∈ (A : Multiset ℕ) := by rw [hMA]; simp
    simpa using this
  let S : Finset ℕ := (Finset.range A.length).filter (fun i => A.getD i 0 = x)
  have hS : S.Nonempty := by
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx_mem
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [getD_eq_getElem hk, hkx]⟩⟩
  let i := S.min' hS
  have hiS := S.min'_mem hS
  have hi : i < A.length := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
  have hAi : A[i] = x := by
    have hD := (Finset.mem_filter.mp hiS).2
    rwa [getD_eq_getElem hi] at hD
  have hlt : ∀ j (hj : j < i), x < A[j]'(by omega) := by
    intro j hj
    have hj_len : j < A.length := by omega
    have hge : A[i] ≤ A[j] := sortedDesc_antitone hSA (Nat.le_of_lt hj) hi
    have hne : A[j] ≠ x := by
      intro heq
      have hjS : j ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hj_len, by rw [getD_eq_getElem hj_len, heq]⟩
      have := S.min'_le j hjS
      omega
    omega
  have hSset : SortedDesc (A.set i (x + 1)) := by
    rw [SortedDesc, List.pairwise_iff_getElem]
    intro p q hp hq hpq
    have hpA : p < A.length := by simpa using hp
    have hqA : q < A.length := by simpa using hq
    by_cases hpi : p = i
    · subst hpi
      rw [List.getElem_set_self, List.getElem_set_ne (by omega : i ≠ q)]
      have := sortedDesc_antitone hSA (Nat.le_of_lt hpq) hqA
      omega
    · by_cases hqi : q = i
      · subst hqi
        rw [List.getElem_set_self, List.getElem_set_ne (by omega : i ≠ p)]
        have := hlt p hpq
        omega
      · rw [List.getElem_set_ne (Ne.symm hpi), List.getElem_set_ne (Ne.symm hqi)]
        exact sortedDesc_antitone hSA (Nat.le_of_lt hpq) hqA
  obtain ⟨M', hMA', hMset⟩ := multiset_split_set A i (x + 1) hi
  rw [hAi, hMA] at hMA'
  have hMM' : M = M' := (Multiset.cons_inj_right x).mp hMA'
  have hBset : B = A.set i (x + 1) := by
    apply sortedDesc_eq_of_coe hSB hSset
    rw [hMB, hMM', hMset]
  exact ⟨i, hi, hAi, hlt, hBset⟩

theorem dec1_eq_set {A B : List ℕ} {y : ℕ} (h : Dec1 A B y) :
    ∃ j, ∃ hj : j < A.length, A[j] = y ∧ (∀ k, j < k → ∀ hk : k < A.length, A[k] < y) ∧
      B = A.set j (y - 1) := by
  obtain ⟨hy1, hInc⟩ := h
  obtain ⟨hSB, hSA, M, hMB, hMA⟩ := hInc
  have hy_eq : (y - 1) + 1 = y := Nat.sub_add_cancel hy1
  rw [hy_eq] at hMA
  have hy_mem : y ∈ A := by
    have : y ∈ (A : Multiset ℕ) := by rw [hMA]; simp
    simpa using this
  let S : Finset ℕ := (Finset.range A.length).filter (fun j => A.getD j 0 = y)
  have hS : S.Nonempty := by
    obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hy_mem
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [getD_eq_getElem hk, hky]⟩⟩
  let j := S.max' hS
  have hjS := S.max'_mem hS
  have hj : j < A.length := Finset.mem_range.mp (Finset.mem_filter.mp hjS).1
  have hAj : A[j] = y := by
    have hD := (Finset.mem_filter.mp hjS).2
    rwa [getD_eq_getElem hj] at hD
  have hlt : ∀ k, j < k → ∀ hk : k < A.length, A[k] < y := by
    intro k hjk hk
    have hle : A[k] ≤ A[j] := sortedDesc_antitone hSA (Nat.le_of_lt hjk) hk
    have hne : A[k] ≠ y := by
      intro heq
      have hkS : k ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk, by rw [getD_eq_getElem hk, heq]⟩
      have := S.le_max' k hkS
      omega
    omega
  have hSset : SortedDesc (A.set j (y - 1)) := by
    rw [SortedDesc, List.pairwise_iff_getElem]
    intro p q hp hq hpq
    have hpA : p < A.length := by simpa using hp
    have hqA : q < A.length := by simpa using hq
    by_cases hpj : p = j
    · subst hpj
      rw [List.getElem_set_self, List.getElem_set_ne (by omega : j ≠ q)]
      have := hlt q hpq hqA
      omega
    · by_cases hqj : q = j
      · subst hqj
        rw [List.getElem_set_self, List.getElem_set_ne (by omega : j ≠ p)]
        have := sortedDesc_antitone hSA (Nat.le_of_lt hpq) hqA
        omega
      · rw [List.getElem_set_ne (Ne.symm hpj), List.getElem_set_ne (Ne.symm hqj)]
        exact sortedDesc_antitone hSA (Nat.le_of_lt hpq) hqA
  obtain ⟨M', hMA', hMset⟩ := multiset_split_set A j (y - 1) hj
  rw [hAj, hMA] at hMA'
  have hMM' : M = M' := (Multiset.cons_inj_right y).mp hMA'
  have hBset : B = A.set j (y - 1) := by
    apply sortedDesc_eq_of_coe hSB hSset
    rw [hMB, hMM', hMset]
  exact ⟨j, hj, hAj, hlt, hBset⟩

theorem inc1_lt_iff {A B : List ℕ} {x d : ℕ} (h : Inc1 A B x) (hd : d ≤ A.length)
    {i : ℕ} (hi : i < A.length) (hAi : A[i] = x) (hlt : ∀ j (hj : j < i), x < A[j]'(by omega)) :
    i < d ↔ (1 ≤ d ∧ A.getD (d - 1) 0 ≤ x) := by
  constructor
  · intro hid
    refine ⟨by omega, ?_⟩
    have hd1 : d - 1 < A.length := by omega
    rw [getD_eq_getElem hd1]
    have := sortedDesc_antitone h.1 (by omega : i ≤ d - 1) hd1
    omega
  · rintro ⟨hd1, hAd⟩
    have hd1_len : d - 1 < A.length := by omega
    rw [getD_eq_getElem hd1_len] at hAd
    by_contra hnot
    have := hlt (d - 1) (by omega)
    omega

theorem dec1_lt_iff {A B : List ℕ} {y d : ℕ} (h : Dec1 A B y) (hd : d ≤ A.length)
    {j : ℕ} (hj : j < A.length) (hAj : A[j] = y) (hlt : ∀ k, j < k → ∀ hk : k < A.length, A[k] < y) :
    j < d ↔ A.getD d 0 < y := by
  have hy1 : 1 ≤ y := h.1
  by_cases hdlen : d = A.length
  · subst hdlen
    rw [getD_of_length_le le_rfl]
    exact ⟨fun _ => hy1, fun _ => hj⟩
  · have hdlt : d < A.length := by omega
    rw [getD_eq_getElem hdlt]
    constructor
    · intro hjd
      exact hlt d hjd hdlt
    · intro hAd
      by_contra hnot
      have hdj : d ≤ j := Nat.le_of_not_lt hnot
      have := sortedDesc_antitone h.2.2.1 hdj hj
      omega

theorem decTop_inc1 {A B : List ℕ} {x d : ℕ} (h : Inc1 A B x) (hd : d ≤ A.length)
    (hpos : ∀ z ∈ A.take d, 1 ≤ z) :
    Inc1 (decTop d A) (decTop d B) (if 1 ≤ d ∧ A.getD (d - 1) 0 ≤ x then x - 1 else x) := by
  obtain ⟨i, hi, hAi, hlt, rfl⟩ := inc1_eq_set h
  have hiff := inc1_lt_iff h hd hi hAi hlt
  refine ⟨sortedDesc_decTop d A, sortedDesc_decTop d _, ?_⟩
  by_cases hid : i < d
  · have hcond : 1 ≤ d ∧ A.getD (d - 1) 0 ≤ x := hiff.mp hid
    rw [if_pos hcond]
    have hx1 : 1 ≤ x := by
      have hmem : A[i] ∈ A.take d := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
      rw [← hAi]
      exact hpos A[i] hmem
    have hit : i < (A.take d).length := by rw [List.length_take]; omega
    have hmap : ((A.take d).set i (x + 1)).map (· - 1) =
        ((A.take d).map (· - 1)).set i x := by
      rw [List.map_set]; simp
    obtain ⟨M1, hM1A, hM1B⟩ := multiset_split_set ((A.take d).map (· - 1)) i x (by simpa using hit)
    have hget : ((A.take d).map (· - 1))[i]'(by simpa using hit) = x - 1 := by
      simp [List.getElem_take, hAi]
    rw [hget] at hM1A
    refine ⟨M1 + (A.drop d : Multiset ℕ), ?_, ?_⟩
    · rw [multiset_decTop, hM1A, Multiset.cons_add]
    · rw [multiset_decTop, take_set_list, drop_set_list, if_pos hid, if_pos hid, hmap, hM1B,
        show (x - 1) + 1 = x by omega, Multiset.cons_add]
  · have hnot : ¬(1 ≤ d ∧ A.getD (d - 1) 0 ≤ x) := fun hc => hid (hiff.mpr hc)
    rw [if_neg hnot]
    have hid_le : d ≤ i := Nat.le_of_not_lt hid
    have hlen_drop : i - d < (A.drop d).length := by rw [List.length_drop]; omega
    obtain ⟨M2, hM2A, hM2B⟩ := multiset_split_set (A.drop d) (i - d) (x + 1) hlen_drop
    have hget : (A.drop d)[i - d]'hlen_drop = x := by
      simp [List.getElem_drop, show d + (i - d) = i by omega, hAi]
    rw [hget] at hM2A
    refine ⟨((A.take d).map (· - 1) : Multiset ℕ) + M2, ?_, ?_⟩
    · rw [multiset_decTop, hM2A, Multiset.add_cons]
    · rw [multiset_decTop, take_set_list, drop_set_list, if_neg hid, if_neg hid, hM2B,
        Multiset.add_cons]

theorem decTop_dec1 {A B : List ℕ} {y d : ℕ} (h : Dec1 A B y) (hd : d ≤ A.length)
    (hpos : ∀ z ∈ B.take d, 1 ≤ z) :
    Dec1 (decTop d A) (decTop d B) (if A.getD d 0 < y then y - 1 else y) := by
  obtain ⟨j, hj, hAj, hlt, rfl⟩ := dec1_eq_set h
  have hy1 : 1 ≤ y := h.1
  have hiff := dec1_lt_iff h hd hj hAj hlt
  by_cases hjd : j < d
  · have hcond : A.getD d 0 < y := hiff.mp hjd
    rw [if_pos hcond]
    have hj_mem : ((A.set j (y - 1)).take d)[j]'(by
        rw [List.length_take]; simp; omega) = y - 1 := by
      simp [List.getElem_take]
    have hposj : 1 ≤ y - 1 := by
      have hmem : y - 1 ∈ (A.set j (y - 1)).take d := by
        rw [List.mem_iff_getElem]
        exact ⟨j, by rw [List.length_take]; simp; omega, hj_mem⟩
      exact hpos (y - 1) hmem
    have hjt : j < (A.take d).length := by rw [List.length_take]; omega
    have hmap : ((A.take d).set j (y - 1)).map (· - 1) =
        ((A.take d).map (· - 1)).set j (y - 2) := by
      rw [List.map_set]; simp [show y - 1 - 1 = y - 2 by omega]
    obtain ⟨M1, hM1A, hM1B⟩ := multiset_split_set ((A.take d).map (· - 1)) j (y - 2)
      (by simpa using hjt)
    have hget : ((A.take d).map (· - 1))[j]'(by simpa using hjt) = y - 1 := by
      simp [List.getElem_take, hAj]
    rw [hget] at hM1A
    refine ⟨by omega, sortedDesc_decTop d _, sortedDesc_decTop d A,
      M1 + (A.drop d : Multiset ℕ), ?_, ?_⟩
    · rw [multiset_decTop, take_set_list, drop_set_list, if_pos hjd, if_pos hjd, hmap, hM1B,
        Multiset.cons_add, show y - 2 = y - 1 - 1 by omega]
    · rw [multiset_decTop, hM1A, show (y - 1 - 1) + 1 = y - 1 by omega, Multiset.cons_add]
  · have hnot : ¬(A.getD d 0 < y) := fun hc => hjd (hiff.mpr hc)
    rw [if_neg hnot]
    have hdj : d ≤ j := Nat.le_of_not_lt hjd
    have hlen_drop : j - d < (A.drop d).length := by rw [List.length_drop]; omega
    obtain ⟨M2, hM2A, hM2B⟩ := multiset_split_set (A.drop d) (j - d) (y - 1) hlen_drop
    have hget : (A.drop d)[j - d]'hlen_drop = y := by
      simp [List.getElem_drop, show d + (j - d) = j by omega, hAj]
    rw [hget] at hM2A
    refine ⟨hy1, sortedDesc_decTop d _, sortedDesc_decTop d A,
      ((A.take d).map (· - 1) : Multiset ℕ) + M2, ?_, ?_⟩
    · rw [multiset_decTop, take_set_list, drop_set_list, if_neg hjd, if_neg hjd, hM2B,
        Multiset.add_cons]
    · rw [multiset_decTop, hM2A, show (y - 1) + 1 = y by omega, Multiset.add_cons]

theorem decTop_succ {A : List ℕ} {d : ℕ} (hd : d + 1 ≤ A.length)
    (hpos : 1 ≤ A.getD d 0) :
    Dec1 (decTop d A) (decTop (d + 1) A) (A.getD d 0) := by
  have hdlt : d < A.length := by omega
  rw [getD_eq_getElem hdlt] at hpos ⊢
  refine ⟨hpos, sortedDesc_decTop (d + 1) A, sortedDesc_decTop d A,
    ((A.take d).map (· - 1) : Multiset ℕ) + (A.drop (d + 1) : Multiset ℕ), ?_, ?_⟩
  · rw [multiset_decTop, take_succ_getElem A d hdlt, List.map_append, List.map_singleton,
      ← Multiset.coe_add]
    change ((A.take d).map (· - 1) : Multiset ℕ) + ((A[d] - 1) ::ₘ 0) + (A.drop (d + 1) : Multiset ℕ) = _
    rw [Multiset.add_cons, Multiset.add_zero, Multiset.cons_add]
  · rw [multiset_decTop, drop_eq_cons_getElem A d hdlt, Nat.sub_add_cancel hpos]
    change ((A.take d).map (· - 1) : Multiset ℕ) + (A[d] ::ₘ (A.drop (d + 1) : Multiset ℕ)) = _
    rw [Multiset.add_cons]

theorem sortedDesc_filter_le_idx : ∀ (L : List ℕ), SortedDesc L → ∀ k v,
    ∀ hk : k < L.length, L[k]'hk < v → (L.filter (fun z => decide (v ≤ z))).length ≤ k := by
  intro L
  induction L with
  | nil => intro _ k _ hk; simp at hk
  | cons a t ih =>
    intro hS k v hk hlt
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hlt
      have hall : ∀ z ∈ a :: t, ¬(decide (v ≤ z) = true) := by
        intro z hz
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hz with rfl | hzt
        · omega
        · have := sortedDesc_head_ge hS z hzt
          omega
      have hf : (a :: t).filter (fun z => decide (v ≤ z)) = [] := by
        rw [List.filter_eq_nil_iff]
        exact fun z hz => by simpa using hall z hz
      simp [hf]
    | succ k =>
      have hk' : k < t.length := by simpa using hk
      have hlt' : t[k]'hk' < v := by simpa using hlt
      have ht := ih (sortedDesc_tail hS) k v hk' hlt'
      simp only [List.filter_cons]
      split_ifs <;> simp <;> omega

theorem sortedDesc_le_getD_of_filter {L : List ℕ} (hS : SortedDesc L) {k v : ℕ}
    (hk : k < L.length) (hc : k + 1 ≤ (L.filter (fun z => decide (v ≤ z))).length) :
    v ≤ L.getD k 0 := by
  rw [getD_eq_getElem hk]
  by_contra hnot
  have := sortedDesc_filter_le_idx L hS k v hk (Nat.lt_of_not_le hnot)
  omega

theorem decTop_getD_ge_pred {A : List ℕ} {d : ℕ} (hS : SortedDesc A) (hd1 : 1 ≤ d)
    (hd : d ≤ A.length) :
    A.getD (d - 1) 0 ≤ (decTop d A).getD (d - 1) 0 + 1 := by
  let v := A.getD (d - 1) 0 - 1
  have hlen : d - 1 < (decTop d A).length := by rw [length_decTop]; omega
  have hp : (decTop d A).Perm ((A.take d).map (· - 1) ++ A.drop d) :=
    List.mergeSort_perm _ _
  have hflt : ((decTop d A).filter (fun z => decide (v ≤ z))).length =
      (((A.take d).map (· - 1) ++ A.drop d).filter (fun z => decide (v ≤ z))).length :=
    (hp.filter _).length_eq
  have htake : ((A.take d).map (· - 1)).filter (fun z => decide (v ≤ z)) = (A.take d).map (· - 1) := by
    rw [List.filter_eq_self]
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
    have hid : i < d := by rw [List.length_take] at hi; omega
    have hiA : i < A.length := by omega
    simp only [List.getElem_take] at hiw
    have hanti := sortedDesc_getD_antitone hS (by omega : i ≤ d - 1)
    rw [getD_eq_getElem hiA, hiw] at hanti
    simp only [decide_eq_true_eq, v]
    omega
  have hc : (d - 1) + 1 ≤ ((decTop d A).filter (fun z => decide (v ≤ z))).length := by
    rw [hflt, List.filter_append, htake, List.length_append, List.length_map, List.length_take]
    omega
  have hle := sortedDesc_le_getD_of_filter (sortedDesc_decTop d A) hlen hc
  simp only [v] at hle
  omega

theorem decTop_getD_ge_curr {A : List ℕ} {d : ℕ} (hS : SortedDesc A) (hd : d < A.length) :
    A.getD d 0 ≤ (decTop d A).getD d 0 + 1 := by
  let v := A.getD d 0 - 1
  have hlen : d < (decTop d A).length := by rw [length_decTop]; exact hd
  have hp : (decTop d A).Perm ((A.take d).map (· - 1) ++ A.drop d) :=
    List.mergeSort_perm _ _
  have hflt : ((decTop d A).filter (fun z => decide (v ≤ z))).length =
      (((A.take d).map (· - 1) ++ A.drop d).filter (fun z => decide (v ≤ z))).length :=
    (hp.filter _).length_eq
  have htake : ((A.take d).map (· - 1)).filter (fun z => decide (v ≤ z)) = (A.take d).map (· - 1) := by
    rw [List.filter_eq_self]
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
    have hid : i < d := by rw [List.length_take] at hi; omega
    have hiA : i < A.length := by omega
    simp only [List.getElem_take] at hiw
    have hanti := sortedDesc_getD_antitone hS (by omega : i ≤ d)
    rw [getD_eq_getElem hiA, hiw] at hanti
    simp only [decide_eq_true_eq, v]
    omega
  have hdrop : 1 ≤ ((A.drop d).filter (fun z => decide (v ≤ z))).length := by
    rw [drop_eq_cons_getElem A d hd, List.filter_cons]
    have hdec : decide (v ≤ A[d]) = true := by
      rw [decide_eq_true_eq]
      simp only [v, getD_eq_getElem hd]
      omega
    rw [if_pos hdec]
    simp
  have hc : d + 1 ≤ ((decTop d A).filter (fun z => decide (v ≤ z))).length := by
    rw [hflt, List.filter_append, htake, List.length_append, List.length_map, List.length_take]
    omega
  have hle := sortedDesc_le_getD_of_filter (sortedDesc_decTop d A) hlen hc
  simp only [v] at hle
  omega

/-- Elementary degree-transfer relation on valid sorted descending sequences. -/
def ElemTrans (X Y : List ℕ) : Prop :=
  SortedDesc X ∧ SortedDesc Y ∧ Valid X ∧ Valid Y ∧
  ∃ M : Multiset ℕ, ∃ a b : ℕ, 1 ≤ b ∧ b ≤ a ∧
    (X : Multiset ℕ) = a ::ₘ b ::ₘ M ∧ (Y : Multiset ℕ) = (a + 1) ::ₘ (b - 1) ::ₘ M

/-- Two-decrement relation (either two slots by 1, or one slot ≤ `U[d]` by 2) on valid sorted lists. -/
def Step2 (U V : List ℕ) : Prop :=
  SortedDesc U ∧ SortedDesc V ∧ Valid U ∧ Valid V ∧
  ∃ d ru, U = d :: ru ∧ 1 ≤ d ∧
  ((∃ M : Multiset ℕ, ∃ a b : ℕ, 1 ≤ b ∧ b ≤ a ∧ b ≤ U.getD d 0 + 1 ∧
      (U : Multiset ℕ) = a ::ₘ b ::ₘ M ∧ (V : Multiset ℕ) = (a - 1) ::ₘ (b - 1) ::ₘ M) ∨
   (∃ M : Multiset ℕ, ∃ a : ℕ, 2 ≤ a ∧ a ≤ U.getD d 0 ∧
      (U : Multiset ℕ) = a ::ₘ M ∧ (V : Multiset ℕ) = (a - 2) ::ₘ M))

theorem elemTrans_length {X Y : List ℕ} (h : ElemTrans X Y) : X.length = Y.length := by
  obtain ⟨_, _, _, _, M, a, b, hb1, _, hX, hY⟩ := h
  have := congrArg Multiset.card hX
  have := congrArg Multiset.card hY
  simp only [Multiset.coe_card, Multiset.card_cons] at *
  omega

theorem step2_length {U V : List ℕ} (h : Step2 U V) : U.length = V.length := by
  obtain ⟨_, _, _, _, _, _, _, _, hcase⟩ := h
  rcases hcase with ⟨M, a, b, _, _, _, hU, hV⟩ | ⟨M, a, _, _, hU, hV⟩
  · have := congrArg Multiset.card hU
    have := congrArg Multiset.card hV
    simp only [Multiset.coe_card, Multiset.card_cons] at *
    omega
  · have := congrArg Multiset.card hU
    have := congrArg Multiset.card hV
    simp only [Multiset.coe_card, Multiset.card_cons] at *
    omega

theorem sortedDesc_eq_head_of_le {d : ℕ} {ru : List ℕ} (hS : SortedDesc (d :: ru))
    (hle : d ≤ (d :: ru).getD d 0) :
    ∀ k ≤ d, (d :: ru).getD k 0 = d := by
  intro k hk
  have hk_anti := sortedDesc_getD_antitone hS hk
  have hk_ge0 := sortedDesc_getD_antitone hS (Nat.zero_le k)
  simp only [List.getD_cons_zero] at hk_ge0
  omega

theorem step2_heads {U V : List ℕ} (h : Step2 U V) :
    ∃ d ru rv, U = d :: ru ∧ 1 ≤ d ∧ (V = (d - 1) :: rv ∨ V = d :: rv) := by
  have hlen_UV := step2_length h
  obtain ⟨hSU, hSV, hVU, _, d, ru, rfl, hd1, hcase⟩ := h
  rcases hcase with ⟨M, a, b, hb1, hba, _, hU, hV⟩ | ⟨M, a, ha2, hale, hU, hV⟩
  · have hlen : 2 ≤ (d :: ru).length := by
      have := congrArg Multiset.card hU
      simp only [Multiset.coe_card, Multiset.card_cons] at this
      omega
    have hVlen : 2 ≤ V.length := by rw [← hlen_UV]; exact hlen
    cases V with
    | nil => simp at hVlen
    | cons d' rv =>
      have had : a ≤ d := by
        have : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
        rcases List.mem_cons.mp this with rfl | hmem
        · exact le_rfl
        · exact sortedDesc_head_ge hSU a hmem
      have hbd : b ≤ d := Nat.le_trans hba had
      have hle_d : d' ≤ d := by
        have : d' ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by simp
        rw [hV] at this
        rcases Multiset.mem_cons.mp this with rfl | hthis
        · omega
        · rcases Multiset.mem_cons.mp hthis with rfl | hm
          · omega
          · have : d' ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp [hm]
            rcases List.mem_cons.mp this with rfl | hmem
            · exact le_rfl
            · exact sortedDesc_head_ge hSU d' hmem
      have hge_d1 : d - 1 ≤ d' := by
        have hd_mem : d ∈ ((d :: ru : List ℕ) : Multiset ℕ) := by simp
        rw [hU] at hd_mem
        rcases Multiset.mem_cons.mp hd_mem with hda | h1
        · have : a - 1 ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by rw [hV]; simp
          rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
          · omega
          · exact le_trans (by omega) (sortedDesc_head_ge hSV (a - 1) hmem)
        · rcases Multiset.mem_cons.mp h1 with hdb | hm
          · have : b - 1 ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by rw [hV]; simp
            rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
            · omega
            · exact le_trans (by omega) (sortedDesc_head_ge hSV (b - 1) hmem)
          · have : d ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by rw [hV]; simp [hm]
            rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
            · omega
            · exact le_trans (Nat.sub_le d 1) (sortedDesc_head_ge hSV d hmem)
      refine ⟨d, ru, rv, rfl, hd1, ?_⟩
      rcases eq_or_lt_of_le hge_d1 with h1 | h2
      · exact Or.inl (by congr 1; omega)
      · exact Or.inr (by congr 1; omega)
  · have hlen : 1 ≤ (d :: ru).length := by simp
    have hVlen : 1 ≤ V.length := by rw [← hlen_UV]; exact hlen
    cases V with
    | nil => simp at hVlen
    | cons d' rv =>
      have had : a ≤ d := by
        have : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
        rcases List.mem_cons.mp this with rfl | hmem
        · exact le_rfl
        · exact sortedDesc_head_ge hSU a hmem
      have hd_len : d ≤ ru.length := (valid_take_le hVU).1
      have hdM : d ∈ M := by
        by_cases hda : a = d
        · subst hda
          have hle_dd : a ≤ (a :: ru).getD a 0 := hale
          have hru_head : ∃ ru', ru = a :: ru' := by
            cases ru with
            | nil => simp at hd_len; omega
            | cons r0 rs =>
              have hr0_le : r0 ≤ a := sortedDesc_head_ge hSU r0 (by simp)
              have heq : (a :: r0 :: rs).getD 1 0 = a :=
                sortedDesc_eq_head_of_le hSU hle_dd 1 (by omega)
              simp only [List.getD_cons_succ, List.getD_cons_zero] at heq
              exact ⟨rs, congrArg (· :: rs) heq⟩
          obtain ⟨ru', rfl⟩ := hru_head
          have hU' : a ::ₘ a ::ₘ (ru' : Multiset ℕ) = a ::ₘ M := hU
          have : a ::ₘ (ru' : Multiset ℕ) = M := (Multiset.cons_inj_right a).mp hU'
          rw [← this]; simp
        · have : d ∈ a ::ₘ M := by rw [← hU]; simp
          exact (Multiset.mem_cons.mp this).resolve_left (Ne.symm hda)
      have hge_d : d ≤ d' := by
        have : d ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by rw [hV]; simp [hdM]
        rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with rfl | hmem
        · exact le_rfl
        · exact sortedDesc_head_ge hSV d hmem
      have hle_d : d' ≤ d := by
        have : d' ∈ ((d' :: rv : List ℕ) : Multiset ℕ) := by simp
        rw [hV] at this
        rcases Multiset.mem_cons.mp this with heq | hm
        · omega
        · have : d' ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp [hm]
          rcases List.mem_cons.mp this with rfl | hmem
          · exact le_rfl
          · exact sortedDesc_head_ge hSU d' hmem
      exact ⟨d, ru, rv, rfl, hd1, Or.inr (by congr 1; omega)⟩

theorem elemTrans_heads {X Y : List ℕ} (h : ElemTrans X Y) :
    ∃ d rx ry, X = d :: rx ∧ (Y = d :: ry ∨ Y = (d + 1) :: ry) := by
  have hlen_XY := elemTrans_length h
  obtain ⟨hSX, hSY, _, _, M, a, b, hb1, hba, hX, hY⟩ := h
  have hlen : 2 ≤ X.length := by
    have := congrArg Multiset.card hX
    simp only [Multiset.coe_card, Multiset.card_cons] at this
    omega
  have hYlen : 2 ≤ Y.length := by rw [← hlen_XY]; exact hlen
  cases X with
  | nil => simp at hlen
  | cons d rx =>
    cases Y with
    | nil => simp at hYlen
    | cons d' ry =>
      have had : a ≤ d := by
        have : a ∈ d :: rx := by rw [← Multiset.mem_coe, hX]; simp
        rcases List.mem_cons.mp this with rfl | hmem
        · exact le_rfl
        · exact sortedDesc_head_ge hSX a hmem
      have hbd : b ≤ d := Nat.le_trans hba had
      have hle_d1 : d' ≤ d + 1 := by
        have : d' ∈ ((d' :: ry : List ℕ) : Multiset ℕ) := by simp
        rw [hY] at this
        rcases Multiset.mem_cons.mp this with heq | hthis
        · omega
        · rcases Multiset.mem_cons.mp hthis with heq | hm
          · omega
          · have : d' ∈ d :: rx := by rw [← Multiset.mem_coe, hX]; simp [hm]
            rcases List.mem_cons.mp this with heq | hmem
            · omega
            · have := sortedDesc_head_ge hSX d' hmem; omega
      have hge_d : d ≤ d' := by
        have hd_mem : d ∈ ((d :: rx : List ℕ) : Multiset ℕ) := by simp
        rw [hX] at hd_mem
        rcases Multiset.mem_cons.mp hd_mem with hda | h1
        · have : a + 1 ∈ ((d' :: ry : List ℕ) : Multiset ℕ) := by rw [hY]; simp
          rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
          · omega
          · have := sortedDesc_head_ge hSY (a + 1) hmem; omega
        · rcases Multiset.mem_cons.mp h1 with hdb | hM
          · have : a + 1 ∈ ((d' :: ry : List ℕ) : Multiset ℕ) := by rw [hY]; simp
            rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
            · omega
            · have := sortedDesc_head_ge hSY (a + 1) hmem; omega
          · have : d ∈ ((d' :: ry : List ℕ) : Multiset ℕ) := by rw [hY]; simp [hM]
            rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
            · exact le_of_eq heq
            · exact sortedDesc_head_ge hSY d hmem
      rcases eq_or_lt_of_le hge_d with hdeq | hlt
      · exact ⟨d, rx, ry, rfl, Or.inl (by congr 1; omega)⟩
      · exact ⟨d, rx, ry, rfl, Or.inr (by congr 1; omega)⟩

theorem elemTrans_same_head {d : ℕ} {rx ry : List ℕ} (h : ElemTrans (d :: rx) (d :: ry)) :
    decTop d rx = decTop d ry ∨ ElemTrans (decTop d rx) (decTop d ry) := by
  obtain ⟨hSX, hSY, hVX, hVY, M, a, b, hb1, hba, hX, hY⟩ := h
  have had : a < d := by
    have : a + 1 ∈ ((d :: ry : List ℕ) : Multiset ℕ) := by rw [hY]; simp
    rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
    · omega
    · have := sortedDesc_head_ge hSY (a + 1) hmem; omega
  have hbd : b < d := Nat.lt_of_le_of_lt hba had
  have hdM : d ∈ M := by
    have : d ∈ ((d :: rx : List ℕ) : Multiset ℕ) := by simp
    rw [hX] at this
    rcases Multiset.mem_cons.mp this with heq | h1
    · omega
    · rcases Multiset.mem_cons.mp h1 with heq | hm
      · omega
      · exact hm
  obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hdM
  have hrx : (rx : Multiset ℕ) = a ::ₘ b ::ₘ M' := by
    have hX' : d ::ₘ (rx : Multiset ℕ) = d ::ₘ (a ::ₘ b ::ₘ M') := by
      calc d ::ₘ (rx : Multiset ℕ) = ((d :: rx : List ℕ) : Multiset ℕ) := rfl
        _ = a ::ₘ b ::ₘ (d ::ₘ M') := hX
        _ = d ::ₘ (a ::ₘ b ::ₘ M') := by simp [Multiset.cons_swap]
    exact (Multiset.cons_inj_right d).mp hX'
  have hry : (ry : Multiset ℕ) = (a + 1) ::ₘ (b - 1) ::ₘ M' := by
    have hY' : d ::ₘ (ry : Multiset ℕ) = d ::ₘ ((a + 1) ::ₘ (b - 1) ::ₘ M') := by
      calc d ::ₘ (ry : Multiset ℕ) = ((d :: ry : List ℕ) : Multiset ℕ) := rfl
        _ = (a + 1) ::ₘ (b - 1) ::ₘ (d ::ₘ M') := hY
        _ = d ::ₘ ((a + 1) ::ₘ (b - 1) ::ₘ M') := by simp [Multiset.cons_swap]
    exact (Multiset.cons_inj_right d).mp hY'
  obtain ⟨W, hSW, hMW⟩ := exists_sortedDesc_of_multiset ((a + 1) ::ₘ b ::ₘ M')
  have hInc : Inc1 rx W a := ⟨sortedDesc_tail hSX, hSW, b ::ₘ M',
    by rw [hrx, Multiset.cons_swap], by rw [hMW, Multiset.cons_swap]⟩
  have hDec : Dec1 W ry b := ⟨hb1, sortedDesc_tail hSY, hSW, (a + 1) ::ₘ M',
    by rw [hry, Multiset.cons_swap (b - 1) (a + 1)],
    by rw [hMW, Nat.sub_add_cancel hb1, Multiset.cons_swap]⟩
  obtain ⟨hdx, hposx, hVx⟩ := valid_take_le hVX
  obtain ⟨hdy, hposy, hVy⟩ := valid_take_le hVY
  have hInc' := decTop_inc1 hInc hdx hposx
  have hDec' := decTop_dec1 hDec (by rw [← inc1_length hInc]; exact hdx) hposy
  set a' := if 1 ≤ d ∧ rx.getD (d - 1) 0 ≤ a then a - 1 else a
  set b' := if W.getD d 0 < b then b - 1 else b
  obtain ⟨_, _, M1, hM1A, hM1W⟩ := hInc'
  obtain ⟨hb'1, _, _, M2, hM2y, hM2W⟩ := hDec'
  have hba' : b' ≤ a' + 1 := by
    have ha'_lo : a - 1 ≤ a' := by dsimp [a']; split_ifs <;> omega
    have hb'_hi : b' ≤ b := by dsimp [b']; split_ifs <;> omega
    omega
  rcases eq_or_lt_of_le hba' with h_eq_succ | h_le_a'
  · left
    apply sortedDesc_eq_of_coe (sortedDesc_decTop d rx) (sortedDesc_decTop d ry)
    have hM2W' : (decTop d W : Multiset ℕ) = b' ::ₘ M2 := by
      simpa [Nat.sub_add_cancel hb'1] using hM2W
    have hMM : M1 = M2 := by
      have hW : (a' + 1) ::ₘ M1 = (a' + 1) ::ₘ M2 := by
        rw [← hM1W, hM2W', h_eq_succ]
      exact (Multiset.cons_inj_right _).mp hW
    rw [hM1A, hM2y, hMM, h_eq_succ]
    simp
  · right
    have hb'_le : b' ≤ a' := by omega
    have hM2W' : (decTop d W : Multiset ℕ) = b' ::ₘ M2 := by
      simpa [Nat.sub_add_cancel hb'1] using hM2W
    have hM12 : (a' + 1) ::ₘ M1 = b' ::ₘ M2 := by rw [← hM1W, hM2W']
    have ha1_mem : a' + 1 ∈ M2 := by
      have hmem : a' + 1 ∈ (a' + 1) ::ₘ M1 := Multiset.mem_cons_self _ _
      rw [hM12] at hmem
      rcases Multiset.mem_cons.mp hmem with heq | hm
      · omega
      · exact hm
    obtain ⟨M0, hM0⟩ := Multiset.exists_cons_of_mem ha1_mem
    have hM1eq : M1 = b' ::ₘ M0 := by
      have h1 : (a' + 1) ::ₘ M1 = (a' + 1) ::ₘ (b' ::ₘ M0) := by
        rw [hM12, hM0, Multiset.cons_swap]
      exact (Multiset.cons_inj_right _).mp h1
    refine ⟨sortedDesc_decTop d rx, sortedDesc_decTop d ry, hVx hSX, hVy hSY, M0, a', b', hb'1, hb'_le, ?_, ?_⟩
    · rw [hM1A, hM1eq]
    · rw [hM2y, hM0, Multiset.cons_swap]

theorem head_decTop_le {d : ℕ} {r : List ℕ} (hS : SortedDesc (d :: r)) :
    ∀ z ∈ decTop d r, z ≤ d := by
  intro z hz
  have hmem : z ∈ (r.take d).map (· - 1) ++ r.drop d :=
    (List.mergeSort_perm _ _).mem_iff.mp hz
  rcases List.mem_append.mp hmem with h1 | h2
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
    have hwr : w ∈ r := List.mem_of_mem_take hw
    have := sortedDesc_head_ge hS w hwr
    omega
  · have hwr : z ∈ r := List.mem_of_mem_drop h2
    exact sortedDesc_head_ge hS z hwr

theorem sortedDesc_nonempty_pos_of_two_dec1 {U W V : List ℕ} {a b : ℕ}
    (h1 : Dec1 U W a) (_h2 : Dec1 W V b) :
    ∃ u0 rU, U = u0 :: rU ∧ 1 ≤ u0 := by
  have hlen : 1 ≤ U.length := by
    obtain ⟨_, _, _, M, _, hU⟩ := h1
    have := congrArg Multiset.card hU
    simp only [Multiset.coe_card, Multiset.card_cons] at this
    omega
  cases U with
  | nil => simp at hlen
  | cons u0 rU =>
    refine ⟨u0, rU, rfl, ?_⟩
    obtain ⟨ha1, _, hSU, M1, _, hU1⟩ := h1
    rw [Nat.sub_add_cancel ha1] at hU1
    have ha_mem : a ∈ u0 :: rU := by rw [← Multiset.mem_coe, hU1]; simp
    rcases List.mem_cons.mp ha_mem with rfl | hm
    · exact ha1
    · exact le_trans ha1 (sortedDesc_head_ge hSU a hm)

theorem decTop_caseB_bound {A : List ℕ} {d b : ℕ} (hSA : SortedDesc A)
    (hd : d < A.length) (hb : b = A.getD d 0)
    (hnot : b - 1 ∉ decTop d A) :
    b ≤ (decTop d A).getD d 0 := by
  have hlen : d < (decTop d A).length := by rw [length_decTop]; exact hd
  have hp : (decTop d A).Perm ((A.take d).map (· - 1) ++ A.drop d) := List.mergeSort_perm _ _
  have hflt : ((decTop d A).filter (fun z => decide (b ≤ z))).length =
      (((A.take d).map (· - 1) ++ A.drop d).filter (fun z => decide (b ≤ z))).length :=
    (hp.filter _).length_eq
  have htake : ((A.take d).map (· - 1)).filter (fun z => decide (b ≤ z)) = (A.take d).map (· - 1) := by
    rw [List.filter_eq_self]
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
    have hid : i < d := by rw [List.length_take] at hi; omega
    have hiA : i < A.length := by omega
    simp only [List.getElem_take] at hiw
    have hanti := sortedDesc_getD_antitone hSA (by omega : i ≤ d)
    rw [getD_eq_getElem hiA, hiw] at hanti
    have hmem_z : w - 1 ∈ decTop d A :=
      hp.mem_iff.mpr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩)))
    have hne : w - 1 ≠ b - 1 := fun heq => hnot (heq ▸ hmem_z)
    simp only [decide_eq_true_eq]
    omega
  have hdrop : 1 ≤ ((A.drop d).filter (fun z => decide (b ≤ z))).length := by
    rw [drop_eq_cons_getElem A d hd, List.filter_cons]
    have hdec : decide (b ≤ A[d]) = true := by
      rw [decide_eq_true_eq, hb, getD_eq_getElem hd]
    rw [if_pos hdec]
    simp
  have hc : d + 1 ≤ ((decTop d A).filter (fun z => decide (b ≤ z))).length := by
    rw [hflt, List.filter_append, htake, List.length_append, List.length_map, List.length_take]
    omega
  exact sortedDesc_le_getD_of_filter (sortedDesc_decTop d A) hlen hc

theorem take_pos_of_dec1 {W V : List ℕ} {y d : ℕ} (h : Dec1 W V y) (hd : d ≤ V.length)
    (hpos : ∀ z ∈ V.take d, 1 ≤ z) : ∀ z ∈ W.take d, 1 ≤ z := by
  obtain ⟨j, hj, hWj, _, hVW⟩ := dec1_eq_set h
  intro z hz
  rw [List.mem_iff_getElem] at hz
  obtain ⟨k, hk, hkz⟩ := hz
  have hkd : k < d := by rw [List.length_take] at hk; omega
  have hkV : k < V.length := by omega
  have hkW : k < W.length := by rw [dec1_length h]; exact hkV
  have hle : V[k]'hkV ≤ z := by
    rw [← hkz, List.getElem_take]
    calc V[k]'hkV = (W.set j (y - 1))[k]'(by simpa [← hVW] using hkV) := by simp [hVW]
      _ ≤ W[k]'hkW := by
        by_cases hkj : k = j
        · subst hkj; simp [List.getElem_set_self]; omega
        · simp [List.getElem_set_ne (Ne.symm hkj)]
  have hmem : V[k]'hkV ∈ V.take d := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
  exact le_trans (hpos (V[k]'hkV) hmem) hle

theorem step2_of_two_dec1_caseA {U W V : List ℕ} {a b d : ℕ} {ru : List ℕ}
    (h1 : Dec1 U W a) (h2 : Dec1 W V b)
    (hVU : Valid U) (hVV : Valid V)
    (hUeq : U = d :: ru) (hd1 : 1 ≤ d)
    (hmin : min a b ≤ U.getD d 0 + 1)
    (hsplit : ∃ M : Multiset ℕ, (U : Multiset ℕ) = max a b ::ₘ min a b ::ₘ M ∧
      (V : Multiset ℕ) = (max a b - 1) ::ₘ (min a b - 1) ::ₘ M) :
    Step2 U V := by
  obtain ⟨M, hU, hV⟩ := hsplit
  have ha1 : 1 ≤ a := h1.1
  have hb1 : 1 ≤ b := h2.1
  exact ⟨h1.2.2.1, h2.2.1, hVU, hVV, d, ru, hUeq, hd1,
    Or.inl ⟨M, max a b, min a b, by omega, min_le_max, hmin, hU, hV⟩⟩

theorem elemTrans_inc_head {d : ℕ} {rx ry : List ℕ} (h : ElemTrans (d :: rx) ((d + 1) :: ry)) :
    Step2 (decTop d rx) (decTop (d + 1) ry) := by
  obtain ⟨hSX, hSY, hVX, hVY, M, a, b, hb1, hba, hX, hY⟩ := h
  have had_le : a ≤ d := by
    have : a ∈ ((d :: rx : List ℕ) : Multiset ℕ) := by rw [hX]; simp
    rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with rfl | hm
    · exact le_rfl
    · exact sortedDesc_head_ge hSX a hm
  have ha_eq : a = d := by
    have : d + 1 ∈ (((d + 1) :: ry : List ℕ) : Multiset ℕ) := by simp
    rw [hY] at this
    rcases Multiset.mem_cons.mp this with heq | h1
    · omega
    · rcases Multiset.mem_cons.mp h1 with heq | hm
      · have hbd : b ≤ d := Nat.le_trans hba had_le; omega
      · have : d + 1 ∈ ((d :: rx : List ℕ) : Multiset ℕ) := by rw [hX]; simp [hm]
        rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hm'
        · omega
        · have := sortedDesc_head_ge hSX (d + 1) hm'; omega
  subst ha_eq
  have hrx : (rx : Multiset ℕ) = b ::ₘ M :=
    (Multiset.cons_inj_right a).mp hX
  have hry : (ry : Multiset ℕ) = (b - 1) ::ₘ M :=
    (Multiset.cons_inj_right (a + 1)).mp hY
  have hDec_rx_ry : Dec1 rx ry b := ⟨hb1, sortedDesc_tail hSY, sortedDesc_tail hSX, M, hry,
    by rw [hrx, Nat.sub_add_cancel hb1]⟩
  obtain ⟨ha_len, hpos_rx, hVx⟩ := valid_take_le hVX
  obtain ⟨ha1_len, hpos_ry, hVy⟩ := valid_take_le hVY
  have hpos_ry_take : ∀ z ∈ ry.take a, 1 ≤ z := fun z hz => by
    have hsub : ry.take a = (ry.take (a + 1)).take a := by
      rw [List.take_take]; simp
    rw [hsub] at hz
    exact hpos_ry z (List.mem_of_mem_take hz)
  have hDec1 := decTop_dec1 hDec_rx_ry (by omega : a ≤ rx.length) hpos_ry_take
  have hpos_ry_d : 1 ≤ ry.getD a 0 := by
    have ha_ry : a < ry.length := by omega
    rw [getD_eq_getElem ha_ry]
    have hmem : ry[a] ∈ ry.take (a + 1) := by
      rw [List.mem_iff_getElem]
      exact ⟨a, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    exact hpos_ry ry[a] hmem
  have hDec2 := decTop_succ (A := ry) (d := a) ha1_len hpos_ry_d
  set b' := if rx.getD a 0 < b then b - 1 else b
  set c' := ry.getD a 0
  obtain ⟨u0, rU, hUeq, hu0_pos⟩ := sortedDesc_nonempty_pos_of_two_dec1 hDec1 hDec2
  have hu0_le : u0 ≤ a := by
    have hmem : u0 ∈ decTop a rx := by rw [hUeq]; simp
    exact head_decTop_le hSX u0 hmem
  have hrx_len : a < rx.length := by
    rw [dec1_length hDec_rx_ry]; omega
  have hc'_le_rx : c' ≤ rx.getD a 0 := by
    obtain ⟨j, hj, hrxj, _, hry_set⟩ := dec1_eq_set hDec_rx_ry
    change ry.getD a 0 ≤ rx.getD a 0
    rw [hry_set, getD_set_list]
    split_ifs with hcond
    · rw [hcond.1, getD_eq_getElem hj, hrxj]; exact Nat.sub_le _ _
    · exact le_rfl
  have hc'_bound : c' ≤ (decTop a rx).getD u0 0 + 1 := by
    have hge1 := decTop_getD_ge_curr (sortedDesc_tail hSX) hrx_len
    have hanti := sortedDesc_getD_antitone (sortedDesc_decTop a rx) hu0_le
    omega
  have hDec1' := hDec1
  have hDec2' := hDec2
  obtain ⟨hb'1, _, hSU, M1, hW1, hU1⟩ := hDec1
  obtain ⟨hc'1, hSV, hSW, M2, hV2, hW2⟩ := hDec2
  rw [Nat.sub_add_cancel hb'1] at hU1
  rw [Nat.sub_add_cancel hc'1] at hW2
  have hMW : (b' - 1) ::ₘ M1 = c' ::ₘ M2 := by rw [← hW1, hW2]
  by_cases hmem_M1 : c' ∈ M1
  · obtain ⟨M0, rfl⟩ := Multiset.exists_cons_of_mem hmem_M1
    have hM2eq : M2 = (b' - 1) ::ₘ M0 := by
      have : c' ::ₘ M2 = c' ::ₘ ((b' - 1) ::ₘ M0) := by
        rw [← hMW, Multiset.cons_swap]
      exact (Multiset.cons_inj_right c').mp this
    refine step2_of_two_dec1_caseA hDec1' hDec2' (hVx hSX) (hVy hSY) hUeq hu0_pos
      (le_trans (min_le_right _ _) hc'_bound) ⟨M0, ?_, ?_⟩
    · rw [hU1]
      rcases le_or_gt b' c' with hle | hlt
      · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
      · rw [max_eq_left hlt.le, min_eq_right hlt.le]
    · rw [hV2, hM2eq]
      rcases le_or_gt b' c' with hle | hlt
      · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
      · rw [max_eq_left hlt.le, min_eq_right hlt.le, Multiset.cons_swap]
  · have hc'_eq : c' = b' - 1 := by
      have : c' ∈ (b' - 1) ::ₘ M1 := by rw [hMW]; simp
      rcases Multiset.mem_cons.mp this with h1 | h2
      · exact h1
      · exact (hmem_M1 h2).elim
    have hM12 : M1 = M2 := by
      have : c' ::ₘ M1 = c' ::ₘ M2 := by simpa [← hc'_eq] using hMW
      exact (Multiset.cons_inj_right c').mp this
    have hc'_not_U : c' ∉ decTop a rx := by
      intro hmem
      have : c' ∈ (decTop a rx : Multiset ℕ) := Multiset.mem_coe.mpr hmem
      rw [hU1] at this
      rcases Multiset.mem_cons.mp this with heq | hm
      · omega
      · exact hmem_M1 hm
    obtain ⟨j, hj, hrxj, _, hry_set⟩ := dec1_eq_set hDec_rx_ry
    have hj_eq_a : j = a := by
      have hne_ad : ry.getD a 0 ≠ rx.getD a 0 := by
        intro heq
        have hmem_rx : rx.getD a 0 ∈ decTop a rx := by
          have hmem_app : rx[a] ∈ (rx.take a).map (· - 1) ++ rx.drop a := by
            apply List.mem_append.mpr; right
            rw [drop_eq_cons_getElem rx a hrx_len]; exact List.mem_cons_self
          rw [getD_eq_getElem hrx_len, decTop]
          exact (List.mergeSort_perm _ _).mem_iff.mpr hmem_app
        apply hc'_not_U
        show ry.getD a 0 ∈ decTop a rx
        rw [heq]; exact hmem_rx
      have h_eq_if : a ≠ j → ry.getD a 0 = rx.getD a 0 := by
        intro hne
        rw [hry_set, getD_set_list, if_neg (by omega)]
      by_contra hne
      exact hne_ad (h_eq_if (Ne.symm hne))
    have hrx_a_eq_b : rx.getD a 0 = b := by
      rw [getD_eq_getElem hrx_len]
      calc rx[a]'hrx_len = rx[j]'hj := by simp [hj_eq_a]
        _ = b := hrxj
    have hb'_eq : b' = rx.getD a 0 := by
      simp only [b', hrx_a_eq_b, lt_self_iff_false, ↓reduceIte]
    have hle_caseB := decTop_caseB_bound (sortedDesc_tail hSX) hrx_len hb'_eq
      (by simpa [hc'_eq] using hc'_not_U)
    have hanti := sortedDesc_getD_antitone (sortedDesc_decTop a rx) hu0_le
    refine ⟨hSU, hSV, hVx hSX, hVy hSY, u0, rU, hUeq, hu0_pos,
      Or.inr ⟨M1, b', by omega, le_trans hle_caseB hanti, hU1, ?_⟩⟩
    rw [hV2, ← hM12, show c' - 1 = b' - 2 by omega]

theorem step2_dec_head {d : ℕ} {ru rv : List ℕ} (h : Step2 (d :: ru) ((d - 1) :: rv)) :
    decTop d ru = decTop (d - 1) rv ∨ ElemTrans (decTop d ru) (decTop (d - 1) rv) := by
  obtain ⟨hSU, hSV, hVU, hVV, d', ru', hUeq, hd1, hcase⟩ := h
  injection hUeq with hd_eq hru_eq
  subst hd_eq hru_eq
  rcases hcase with ⟨M, a, b, hb1, hba, hble, hU, hV⟩ | ⟨M, a, ha2, hale, hU, hV⟩
  · have ha_eq : a = d := by
      have hd_not_V : d ∉ (((d - 1) :: rv : List ℕ) : Multiset ℕ) := by
        intro hm
        rcases List.mem_cons.mp (Multiset.mem_coe.mp hm) with heq | hmem
        · omega
        · have := sortedDesc_head_ge hSV d hmem; omega
      have hd_mem_U : d ∈ ((d :: ru : List ℕ) : Multiset ℕ) := by simp
      rw [hU] at hd_mem_U
      rcases Multiset.mem_cons.mp hd_mem_U with hda | h1
      · exact hda.symm
      · rcases Multiset.mem_cons.mp h1 with hdb | hm
        · have ha_mem : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
          have had : a ≤ d := by
            rcases List.mem_cons.mp ha_mem with heq | hm'
            · omega
            · exact sortedDesc_head_ge hSU a hm'
          omega
        · exfalso; apply hd_not_V; rw [hV]; simp [hm]
    subst ha_eq
    have hru : (ru : Multiset ℕ) = b ::ₘ M := (Multiset.cons_inj_right a).mp hU
    have hrv : (rv : Multiset ℕ) = (b - 1) ::ₘ M := (Multiset.cons_inj_right (a - 1)).mp hV
    have hDec_ru_rv : Dec1 ru rv b := ⟨hb1, sortedDesc_tail hSV, sortedDesc_tail hSU, M, hrv,
      by rw [hru, Nat.sub_add_cancel hb1]⟩
    obtain ⟨hd_len, hpos_ru, hVu⟩ := valid_take_le hVU
    obtain ⟨hd1_len, hpos_rv, hVv⟩ := valid_take_le hVV
    have hpos_ru_d1 : 1 ≤ ru.getD (a - 1) 0 := by
      have ha1_lt : a - 1 < ru.length := by omega
      rw [getD_eq_getElem ha1_lt]
      have hmem : ru[a - 1] ∈ ru.take a := by
        rw [List.mem_iff_getElem]
        exact ⟨a - 1, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
      exact hpos_ru ru[a - 1] hmem
    have hSucc : Dec1 (decTop (a - 1) ru) (decTop a ru) (ru.getD (a - 1) 0) := by
      have heq : (a - 1) + 1 = a := Nat.sub_add_cancel hd1
      simpa [heq] using decTop_succ (A := ru) (d := a - 1) (by omega) hpos_ru_d1
    have hInc1 : Inc1 (decTop a ru) (decTop (a - 1) ru) (ru.getD (a - 1) 0 - 1) := hSucc.2
    have hDec1 := decTop_dec1 hDec_ru_rv (by omega : a - 1 ≤ ru.length) hpos_rv
    set a' := ru.getD (a - 1) 0 - 1
    set b' := if ru.getD (a - 1) 0 < b then b - 1 else b
    have hble' : b ≤ ru.getD (a - 1) 0 + 1 := by
      rw [← getD_cons_pred hd1]; exact hble
    have hba' : b' ≤ a' + 1 := by
      dsimp [a', b']
      split_ifs <;> omega
    obtain ⟨_, _, M1, hM1A, hM1W⟩ := hInc1
    obtain ⟨hb'1, _, _, M2, hM2y, hM2W⟩ := hDec1
    rcases eq_or_lt_of_le hba' with h_eq_succ | h_le_a'
    · left
      apply sortedDesc_eq_of_coe (sortedDesc_decTop a ru) (sortedDesc_decTop (a - 1) rv)
      have hM2W' : (decTop (a - 1) ru : Multiset ℕ) = b' ::ₘ M2 := by
        simpa [Nat.sub_add_cancel hb'1] using hM2W
      have hMM : M1 = M2 := by
        have hW : (a' + 1) ::ₘ M1 = (a' + 1) ::ₘ M2 := by
          rw [← hM1W, hM2W', h_eq_succ]
        exact (Multiset.cons_inj_right _).mp hW
      rw [hM1A, hM2y, hMM, h_eq_succ]
      simp
    · right
      have hb'_le : b' ≤ a' := by omega
      have hM2W' : (decTop (a - 1) ru : Multiset ℕ) = b' ::ₘ M2 := by
        simpa [Nat.sub_add_cancel hb'1] using hM2W
      have hM12 : (a' + 1) ::ₘ M1 = b' ::ₘ M2 := by rw [← hM1W, hM2W']
      have ha1_mem : a' + 1 ∈ M2 := by
        have hmem : a' + 1 ∈ (a' + 1) ::ₘ M1 := Multiset.mem_cons_self _ _
        rw [hM12] at hmem
        rcases Multiset.mem_cons.mp hmem with heq | hm
        · omega
        · exact hm
      obtain ⟨M0, hM0⟩ := Multiset.exists_cons_of_mem ha1_mem
      have hM1eq : M1 = b' ::ₘ M0 := by
        have h1 : (a' + 1) ::ₘ M1 = (a' + 1) ::ₘ (b' ::ₘ M0) := by
          rw [hM12, hM0, Multiset.cons_swap]
        exact (Multiset.cons_inj_right _).mp h1
      refine ⟨sortedDesc_decTop a ru, sortedDesc_decTop (a - 1) rv, hVu hSU, hVv hSV,
        M0, a', b', hb'1, hb'_le, ?_, ?_⟩
      · rw [hM1A, hM1eq]
      · rw [hM2y, hM0, Multiset.cons_swap]
  · exfalso
    have had : a ≤ d := by
      have : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
      rcases List.mem_cons.mp this with rfl | hmem
      · exact le_rfl
      · exact sortedDesc_head_ge hSU a hmem
    have hd_len : d ≤ ru.length := (valid_take_le hVU).1
    have hdM : d ∈ M := by
      by_cases hda : a = d
      · subst hda
        have hle_dd : a ≤ (a :: ru).getD a 0 := hale
        have hru_head : ∃ ru', ru = a :: ru' := by
          cases ru with
          | nil => simp at hd_len; omega
          | cons r0 rs =>
            have hr0_le : r0 ≤ a := sortedDesc_head_ge hSU r0 (by simp)
            have heq : (a :: r0 :: rs).getD 1 0 = a :=
              sortedDesc_eq_head_of_le hSU hle_dd 1 (by omega)
            simp only [List.getD_cons_succ, List.getD_cons_zero] at heq
            exact ⟨rs, congrArg (· :: rs) heq⟩
        obtain ⟨ru', rfl⟩ := hru_head
        have hU' : a ::ₘ a ::ₘ (ru' : Multiset ℕ) = a ::ₘ M := hU
        have : a ::ₘ (ru' : Multiset ℕ) = M := (Multiset.cons_inj_right a).mp hU'
        rw [← this]; simp
      · have : d ∈ a ::ₘ M := by rw [← hU]; simp
        exact (Multiset.mem_cons.mp this).resolve_left (Ne.symm hda)
    have : d ∈ (((d - 1) :: rv : List ℕ) : Multiset ℕ) := by rw [hV]; simp [hdM]
    rcases List.mem_cons.mp (Multiset.mem_coe.mp this) with heq | hmem
    · omega
    · have := sortedDesc_head_ge hSV d hmem; omega

theorem decTop_same_head_u0_d {d : ℕ} {ru : List ℕ} (hd1 : 1 ≤ d) (hS : SortedDesc (d :: ru))
    (hmem : d ∈ decTop d ru) :
    d < ru.length ∧ ru.getD d 0 = d := by
  have hmem_raw : d ∈ (ru.take d).map (· - 1) ++ ru.drop d :=
    (List.mergeSort_perm _ _).mem_iff.mp hmem
  have hmem_drop : d ∈ ru.drop d := by
    rcases List.mem_append.mp hmem_raw with h1 | h2
    · obtain ⟨w, hw, hw1⟩ := List.mem_map.mp h1
      have := sortedDesc_head_ge hS w (List.mem_of_mem_take hw)
      omega
    · exact h2
  have hd_lt_ru : d < ru.length := by
    by_contra hnot
    have : ru.drop d = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [this] at hmem_drop
    simp at hmem_drop
  refine ⟨hd_lt_ru, ?_⟩
  rw [getD_eq_getElem hd_lt_ru]
  have h1 := sortedDesc_head_ge hS ru[d] (List.getElem_mem hd_lt_ru)
  have h2 : d ≤ ru[d] := by
    obtain ⟨t, ht, htd⟩ := List.mem_iff_getElem.mp hmem_drop
    have ht_lt : d + t < ru.length := by rw [List.length_drop] at ht; omega
    have hanti := sortedDesc_getD_antitone (sortedDesc_tail hS) (by omega : d ≤ d + t)
    rw [getD_eq_getElem hd_lt_ru, getD_eq_getElem ht_lt] at hanti
    simp only [List.getElem_drop] at htd
    omega
  omega

theorem step2_same_head {d : ℕ} {ru rv : List ℕ} (h : Step2 (d :: ru) (d :: rv)) :
    Step2 (decTop d ru) (decTop d rv) := by
  obtain ⟨hSU, hSV, hVU, hVV, d', ru', hUeq, hd1, hcase⟩ := h
  injection hUeq with hd_eq hru_eq
  subst hd_eq hru_eq
  obtain ⟨hd_len, hpos_ru, hVu⟩ := valid_take_le hVU
  obtain ⟨hd_lenv, hpos_rv, hVv⟩ := valid_take_le hVV
  rcases hcase with ⟨M, a, b, hb1, hba, hble, hU, hV⟩ | ⟨M, a, ha2, hale, hU, hV⟩
  · have had : a ≤ d := by
      have : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
      rcases List.mem_cons.mp this with rfl | hm
      · exact le_rfl
      · exact sortedDesc_head_ge hSU a hm
    have hdM : d ∈ M := by
      have : d ∈ ((d :: rv : List ℕ) : Multiset ℕ) := by simp
      rw [hV] at this
      rcases Multiset.mem_cons.mp this with heq | h1
      · omega
      · rcases Multiset.mem_cons.mp h1 with heq | hm
        · have : b ≤ d := le_trans hba had; omega
        · exact hm
    obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hdM
    have hru : (ru : Multiset ℕ) = a ::ₘ b ::ₘ M' := by
      have : d ::ₘ (ru : Multiset ℕ) = d ::ₘ (a ::ₘ b ::ₘ M') := by
        calc d ::ₘ (ru : Multiset ℕ) = ((d :: ru : List ℕ) : Multiset ℕ) := rfl
          _ = a ::ₘ b ::ₘ (d ::ₘ M') := hU
          _ = d ::ₘ (a ::ₘ b ::ₘ M') := by simp [Multiset.cons_swap]
      exact (Multiset.cons_inj_right d).mp this
    have hrv : (rv : Multiset ℕ) = (a - 1) ::ₘ (b - 1) ::ₘ M' := by
      have : d ::ₘ (rv : Multiset ℕ) = d ::ₘ ((a - 1) ::ₘ (b - 1) ::ₘ M') := by
        calc d ::ₘ (rv : Multiset ℕ) = ((d :: rv : List ℕ) : Multiset ℕ) := rfl
          _ = (a - 1) ::ₘ (b - 1) ::ₘ (d ::ₘ M') := hV
          _ = d ::ₘ ((a - 1) ::ₘ (b - 1) ::ₘ M') := by simp [Multiset.cons_swap]
      exact (Multiset.cons_inj_right d).mp this
    obtain ⟨W, hSW, hMW⟩ := exists_sortedDesc_of_multiset ((a - 1) ::ₘ b ::ₘ M')
    have ha1 : 1 ≤ a := le_trans hb1 hba
    have hDec1_raw : Dec1 ru W a := ⟨ha1, hSW, sortedDesc_tail hSU, b ::ₘ M',
      by rw [hMW, Multiset.cons_swap],
      by rw [hru, Nat.sub_add_cancel ha1, Multiset.cons_swap]⟩
    have hDec2_raw : Dec1 W rv b := ⟨hb1, sortedDesc_tail hSV, hSW, (a - 1) ::ₘ M',
      by rw [hrv, Multiset.cons_swap],
      by rw [hMW, Nat.sub_add_cancel hb1, Multiset.cons_swap]⟩
    have hpos_W : ∀ z ∈ W.take d, 1 ≤ z := take_pos_of_dec1 hDec2_raw hd_lenv hpos_rv
    have hDec1 := decTop_dec1 hDec1_raw hd_len hpos_W
    have hDec2 := decTop_dec1 hDec2_raw (by rw [← dec1_length hDec1_raw]; exact hd_len) hpos_rv
    set a' := if ru.getD d 0 < a then a - 1 else a
    set b' := if W.getD d 0 < b then b - 1 else b
    obtain ⟨u0, rU, hUeq', hu0_pos⟩ := sortedDesc_nonempty_pos_of_two_dec1 hDec1 hDec2
    have hu0_le : u0 ≤ d := by
      have hmem : u0 ∈ decTop d ru := by rw [hUeq']; simp
      exact head_decTop_le hSU u0 hmem
    have hble_ru : b ≤ ru.getD (d - 1) 0 + 1 := by
      rw [← getD_cons_pred hd1]; exact hble
    have hW_getD : W.getD d 0 ≤ ru.getD d 0 := by
      obtain ⟨j, hj, hruj, _, hWset⟩ := dec1_eq_set hDec1_raw
      rw [hWset, getD_set_list]
      split_ifs with hcond
      · rw [hcond.1, getD_eq_getElem hj, hruj]; exact Nat.sub_le _ _
      · exact le_rfl
    have hb'_le_ru : b' ≤ ru.getD (d - 1) 0 := by
      by_cases hbc : b ≤ ru.getD (d - 1) 0
      · have : b' ≤ b := by dsimp [b']; split_ifs <;> omega
        omega
      · have hb_eq : b = ru.getD (d - 1) 0 + 1 := by omega
        have hanti_ru := sortedDesc_getD_antitone (sortedDesc_tail hSU) (Nat.sub_le d 1)
        have hWlt : W.getD d 0 < b := by omega
        dsimp [b']
        rw [if_pos hWlt, hb_eq]
        omega
    have hbound_U : min a' b' ≤ (decTop d ru).getD u0 0 + 1 := by
      by_cases hu0_lt : u0 ≤ d - 1
      · have hanti_U := sortedDesc_getD_antitone (sortedDesc_decTop d ru) hu0_lt
        have hpred := decTop_getD_ge_pred (sortedDesc_tail hSU) hd1 hd_len
        exact le_trans (min_le_right _ _) (by omega)
      · have hu0_eq : u0 = d := by omega
        rw [hu0_eq]
        obtain ⟨hd_lt_ru, _⟩ := decTop_same_head_u0_d hd1 hSU (by rw [hUeq', hu0_eq]; simp)
        have hcurr := decTop_getD_ge_curr (sortedDesc_tail hSU) hd_lt_ru
        have ha'_le : a' ≤ d := by
          have : a' ≤ a := by dsimp [a']; split_ifs <;> omega
          omega
        exact le_trans (min_le_left _ _) (by omega)
    have hDec1' := hDec1
    have hDec2' := hDec2
    obtain ⟨ha'1, _, hSU', M1, hW1', hU1'⟩ := hDec1
    obtain ⟨hb'1, hSV', hSW', M2, hV2', hW2'⟩ := hDec2
    rw [Nat.sub_add_cancel ha'1] at hU1'
    rw [Nat.sub_add_cancel hb'1] at hW2'
    have hMW' : (a' - 1) ::ₘ M1 = b' ::ₘ M2 := by rw [← hW1', hW2']
    by_cases hmem_M1 : b' ∈ M1
    · obtain ⟨M0, rfl⟩ := Multiset.exists_cons_of_mem hmem_M1
      have hM2eq : M2 = (a' - 1) ::ₘ M0 := by
        have : b' ::ₘ M2 = b' ::ₘ ((a' - 1) ::ₘ M0) := by
          rw [← hMW', Multiset.cons_swap]
        exact (Multiset.cons_inj_right b').mp this
      refine step2_of_two_dec1_caseA hDec1' hDec2' (hVu hSU) (hVv hSV) hUeq' hu0_pos hbound_U ⟨M0, ?_, ?_⟩
      · rw [hU1']
        rcases le_or_gt a' b' with hle | hlt
        · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
        · rw [max_eq_left hlt.le, min_eq_right hlt.le]
      · rw [hV2', hM2eq]
        rcases le_or_gt a' b' with hle | hlt
        · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
        · rw [max_eq_left hlt.le, min_eq_right hlt.le, Multiset.cons_swap]
    · have hb'_eq : b' = a' - 1 := by
        have : b' ∈ (a' - 1) ::ₘ M1 := by rw [hMW']; simp
        rcases Multiset.mem_cons.mp this with h1 | h2
        · exact h1
        · exact (hmem_M1 h2).elim
      have hM12 : M1 = M2 := by
        have : b' ::ₘ M1 = b' ::ₘ M2 := by simpa [← hb'_eq] using hMW'
        exact (Multiset.cons_inj_right b').mp this
      have hb'_not_U : b' ∉ decTop d ru := by
        intro hmem
        have : b' ∈ (decTop d ru : Multiset ℕ) := Multiset.mem_coe.mpr hmem
        rw [hU1'] at this
        rcases Multiset.mem_cons.mp this with heq | hm
        · omega
        · exact hmem_M1 hm
      have hcaseB_le : a' ≤ (decTop d ru).getD u0 0 := by
        have hanti_U := sortedDesc_getD_antitone (sortedDesc_decTop d ru) hu0_le
        by_cases hru_a : ru.getD d 0 < a
        · have ha'_eq : a' = a - 1 := by simp only [a', if_pos hru_a]
          by_cases hW_b : W.getD d 0 < b
          · have hb'_eq2 : b' = b - 1 := by simp only [b', if_pos hW_b]
            have hbeq : b = a' := by omega
            by_cases hru_b : ru.getD d 0 < b
            · exfalso
              have hb_mem_ru : b ∈ ru := by rw [← Multiset.mem_coe, hru]; simp
              obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp hb_mem_ru
              have hkd : k < d := by
                by_contra hnot
                have hdk : d ≤ k := Nat.le_of_not_lt hnot
                have := sortedDesc_getD_antitone (sortedDesc_tail hSU) hdk
                rw [getD_eq_getElem hk, hkb] at this
                omega
              have hmem_U : b - 1 ∈ decTop d ru := by
                have htake : b - 1 ∈ (ru.take d).map (· - 1) := by
                  refine List.mem_map.mpr ⟨b, ?_, rfl⟩
                  rw [List.mem_iff_getElem]
                  exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take, hkb]⟩
                exact (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_append.mpr (Or.inl htake))
              exact hb'_not_U (hb'_eq2 ▸ hmem_U)
            · have hru_eq_a' : ru.getD d 0 = a' := by omega
              have hd_lt_ru : d < ru.length := by
                by_contra hnot
                have := getD_of_length_le (Nat.le_of_not_lt hnot : ru.length ≤ d)
                omega
              have hle := decTop_caseB_bound (sortedDesc_tail hSU) hd_lt_ru hru_eq_a'.symm
                (by simpa [hb'_eq] using hb'_not_U)
              exact le_trans hle hanti_U
          · have hb'_eq2 : b' = b := by simp only [b', if_neg hW_b]
            have hle_ru_d : b' ≤ ru.getD d 0 := by omega
            have hcases : ru.getD d 0 = b' ∨ ru.getD d 0 = a' := by omega
            rcases hcases with h_eq_b' | h_eq_a'
            · exfalso
              have hd_lt_ru : d < ru.length := by
                by_contra hnot
                have := getD_of_length_le (Nat.le_of_not_lt hnot : ru.length ≤ d)
                omega
              have hmem_U : b' ∈ decTop d ru := by
                have hmem_app : ru[d] ∈ (ru.take d).map (· - 1) ++ ru.drop d := by
                  apply List.mem_append.mpr; right
                  rw [drop_eq_cons_getElem ru d hd_lt_ru]; exact List.mem_cons_self
                rw [← h_eq_b', getD_eq_getElem hd_lt_ru, decTop]
                exact (List.mergeSort_perm _ _).mem_iff.mpr hmem_app
              exact hb'_not_U hmem_U
            · have hd_lt_ru : d < ru.length := by
                by_contra hnot
                have := getD_of_length_le (Nat.le_of_not_lt hnot : ru.length ≤ d)
                omega
              have hle := decTop_caseB_bound (sortedDesc_tail hSU) hd_lt_ru h_eq_a'.symm
                (by simpa [hb'_eq] using hb'_not_U)
              exact le_trans hle hanti_U
        · have ha'_eq : a' = a := by simp only [a', if_neg hru_a]
          have hd_lt_ru : d < ru.length := by
            by_contra hnot
            have := getD_of_length_le (Nat.le_of_not_lt hnot : ru.length ≤ d)
            omega
          by_cases hlt_a : a < ru.getD d 0
          · have hge := decTop_getD_ge_curr (sortedDesc_tail hSU) hd_lt_ru
            omega
          · have hru_eq_a : ru.getD d 0 = a' := by omega
            have hle := decTop_caseB_bound (sortedDesc_tail hSU) hd_lt_ru hru_eq_a.symm
              (by simpa [hb'_eq] using hb'_not_U)
            exact le_trans hle hanti_U
      refine ⟨hSU', hSV', hVu hSU, hVv hSV, u0, rU, hUeq', hu0_pos,
        Or.inr ⟨M1, a', by omega, hcaseB_le, hU1', ?_⟩⟩
      rw [hV2', ← hM12, show b' - 1 = a' - 2 by omega]
  · have had : a ≤ d := by
      have : a ∈ d :: ru := by rw [← Multiset.mem_coe, hU]; simp
      rcases List.mem_cons.mp this with rfl | hm
      · exact le_rfl
      · exact sortedDesc_head_ge hSU a hm
    have hdM : d ∈ M := by
      have : d ∈ ((d :: rv : List ℕ) : Multiset ℕ) := by simp
      rw [hV] at this
      rcases Multiset.mem_cons.mp this with heq | hm
      · omega
      · exact hm
    obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hdM
    have hru : (ru : Multiset ℕ) = a ::ₘ M' := by
      have : d ::ₘ (ru : Multiset ℕ) = d ::ₘ (a ::ₘ M') := by
        calc d ::ₘ (ru : Multiset ℕ) = ((d :: ru : List ℕ) : Multiset ℕ) := rfl
          _ = a ::ₘ (d ::ₘ M') := hU
          _ = d ::ₘ (a ::ₘ M') := Multiset.cons_swap _ _ _
      exact (Multiset.cons_inj_right d).mp this
    have hrv : (rv : Multiset ℕ) = (a - 2) ::ₘ M' := by
      have : d ::ₘ (rv : Multiset ℕ) = d ::ₘ ((a - 2) ::ₘ M') := by
        calc d ::ₘ (rv : Multiset ℕ) = ((d :: rv : List ℕ) : Multiset ℕ) := rfl
          _ = (a - 2) ::ₘ (d ::ₘ M') := hV
          _ = d ::ₘ ((a - 2) ::ₘ M') := Multiset.cons_swap _ _ _
      exact (Multiset.cons_inj_right d).mp this
    obtain ⟨W, hSW, hMW⟩ := exists_sortedDesc_of_multiset ((a - 1) ::ₘ M')
    have ha1 : 1 ≤ a := by omega
    have hDec1_raw : Dec1 ru W a := ⟨ha1, hSW, sortedDesc_tail hSU, M', hMW,
      by rw [hru, Nat.sub_add_cancel ha1]⟩
    have hDec2_raw : Dec1 W rv (a - 1) := ⟨by omega, sortedDesc_tail hSV, hSW, M',
      by rw [hrv, show (a - 1) - 1 = a - 2 by omega],
      by rw [hMW, show (a - 1) - 1 + 1 = a - 1 by omega]⟩
    have hpos_W : ∀ z ∈ W.take d, 1 ≤ z := take_pos_of_dec1 hDec2_raw hd_lenv hpos_rv
    have hDec1 := decTop_dec1 hDec1_raw hd_len hpos_W
    have hDec2 := decTop_dec1 hDec2_raw (by rw [← dec1_length hDec1_raw]; exact hd_len) hpos_rv
    set a' := if ru.getD d 0 < a then a - 1 else a
    set b' := if W.getD d 0 < a - 1 then (a - 1) - 1 else a - 1
    obtain ⟨u0, rU, hUeq', hu0_pos⟩ := sortedDesc_nonempty_pos_of_two_dec1 hDec1 hDec2
    have hu0_le : u0 ≤ d := by
      have hmem : u0 ∈ decTop d ru := by rw [hUeq']; simp
      exact head_decTop_le hSU u0 hmem
    have hale_ru : a ≤ ru.getD (d - 1) 0 := by rw [← getD_cons_pred hd1]; exact hale
    have hDec1' := hDec1
    have hDec2' := hDec2
    obtain ⟨ha'1, _, hSU', M1, hW1', hU1'⟩ := hDec1
    obtain ⟨hb'1, hSV', hSW', M2, hV2', hW2'⟩ := hDec2
    rw [Nat.sub_add_cancel ha'1] at hU1'
    rw [Nat.sub_add_cancel hb'1] at hW2'
    have hMW' : (a' - 1) ::ₘ M1 = b' ::ₘ M2 := by rw [← hW1', hW2']
    by_cases hmem_M1 : b' ∈ M1
    · obtain ⟨M0, rfl⟩ := Multiset.exists_cons_of_mem hmem_M1
      have hM2eq : M2 = (a' - 1) ::ₘ M0 := by
        have : b' ::ₘ M2 = b' ::ₘ ((a' - 1) ::ₘ M0) := by
          rw [← hMW', Multiset.cons_swap]
        exact (Multiset.cons_inj_right b').mp this
      have hb'_bound : b' ≤ (decTop d ru).getD u0 0 + 1 := by
        have hb'_le : b' ≤ a - 1 := by dsimp [b']; split_ifs <;> omega
        by_cases hu0_lt : u0 ≤ d - 1
        · have hanti_U := sortedDesc_getD_antitone (sortedDesc_decTop d ru) hu0_lt
          have hpred := decTop_getD_ge_pred (sortedDesc_tail hSU) hd1 hd_len
          omega
        · have hu0_eq : u0 = d := by omega
          rw [hu0_eq]
          obtain ⟨hd_lt_ru, _⟩ := decTop_same_head_u0_d hd1 hSU (by rw [hUeq', hu0_eq]; simp)
          have hcurr := decTop_getD_ge_curr (sortedDesc_tail hSU) hd_lt_ru
          omega
      refine step2_of_two_dec1_caseA hDec1' hDec2' (hVu hSU) (hVv hSV) hUeq' hu0_pos
        (le_trans (min_le_right _ _) hb'_bound) ⟨M0, ?_, ?_⟩
      · rw [hU1']
        rcases le_or_gt a' b' with hle | hlt
        · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
        · rw [max_eq_left hlt.le, min_eq_right hlt.le]
      · rw [hV2', hM2eq]
        rcases le_or_gt a' b' with hle | hlt
        · rw [max_eq_right hle, min_eq_left hle, Multiset.cons_swap]
        · rw [max_eq_left hlt.le, min_eq_right hlt.le, Multiset.cons_swap]
    · have hb'_eq : b' = a' - 1 := by
        have : b' ∈ (a' - 1) ::ₘ M1 := by rw [hMW']; simp
        rcases Multiset.mem_cons.mp this with h1 | h2
        · exact h1
        · exact (hmem_M1 h2).elim
      have hM12 : M1 = M2 := by
        have : b' ::ₘ M1 = b' ::ₘ M2 := by simpa [← hb'_eq] using hMW'
        exact (Multiset.cons_inj_right b').mp this
      have hb'_not_U : b' ∉ decTop d ru := by
        intro hmem
        have : b' ∈ (decTop d ru : Multiset ℕ) := Multiset.mem_coe.mpr hmem
        rw [hU1'] at this
        rcases Multiset.mem_cons.mp this with heq | hm
        · omega
        · exact hmem_M1 hm
      have hcaseB_le : a' ≤ (decTop d ru).getD u0 0 := by
        have hanti_U := sortedDesc_getD_antitone (sortedDesc_decTop d ru) hu0_le
        by_cases hru_a : ru.getD d 0 < a
        · have ha'_eq : a' = a - 1 := by simp only [a', if_pos hru_a]
          have hu0_ne_d : u0 ≠ d := by
            intro heq
            obtain ⟨_, hru_d⟩ := decTop_same_head_u0_d hd1 hSU (by rw [hUeq', heq]; simp)
            omega
          have hu0_lt : u0 ≤ d - 1 := by omega
          have hanti_U' := sortedDesc_getD_antitone (sortedDesc_decTop d ru) hu0_lt
          have hpred := decTop_getD_ge_pred (sortedDesc_tail hSU) hd1 hd_len
          omega
        · have ha'_eq : a' = a := by simp only [a', if_neg hru_a]
          have hd_lt_ru : d < ru.length := by
            by_contra hnot
            have := getD_of_length_le (Nat.le_of_not_lt hnot : ru.length ≤ d)
            omega
          by_cases hlt_a : a < ru.getD d 0
          · have hcurr := decTop_getD_ge_curr (sortedDesc_tail hSU) hd_lt_ru
            omega
          · have hru_eq : ru.getD d 0 = a' := by omega
            have hle := decTop_caseB_bound (sortedDesc_tail hSU) hd_lt_ru hru_eq.symm
              (by simpa [hb'_eq] using hb'_not_U)
            exact le_trans hle hanti_U
      refine ⟨hSU', hSV', hVu hSU, hVv hSV, u0, rU, hUeq', hu0_pos,
        Or.inr ⟨M1, a', by omega, hcaseB_le, hU1', ?_⟩⟩
      rw [hV2', ← hM12, show b' - 1 = a' - 2 by omega]

theorem sum_map_sub_one {L : List ℕ} (h : ∀ x ∈ L, 1 ≤ x) :
    (L.map (· - 1)).sum + L.length = L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ a := h a (by simp)
    have ht := ih fun x hx => h x (by simp [hx])
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sum_decTop {d : ℕ} {r : List ℕ} (hd : d ≤ r.length) (hpos : ∀ x ∈ r.take d, 1 ≤ x) :
    (decTop d r).sum + d = r.sum := by
  have hp : (decTop d r).Perm ((r.take d).map (· - 1) ++ r.drop d) := List.mergeSort_perm _ _
  rw [hp.sum_eq, List.sum_append]
  have hsub := sum_map_sub_one hpos
  have hlen : (r.take d).length = d := by rw [List.length_take]; omega
  have hr : r.sum = (r.take d).sum + (r.drop d).sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

theorem two_mul_E_sum_eq : ∀ (n : ℕ) (L : List ℕ), L.length = n →
    SortedDesc L → Valid L → 2 * (E L).sum = L.sum := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih L hlen hS hV
  cases L with
  | nil => rw [E.eq_1]; simp
  | cons d r =>
    cases d with
    | zero =>
      have hr0 : ∀ x ∈ r, x = 0 := fun x hx => Nat.eq_zero_of_le_zero (sortedDesc_head_ge hS x hx)
      have hsum0 : r.sum = 0 := sum_eq_zero_of_all_zero hr0
      rw [E.eq_2]
      simp [List.sum_replicate, hsum0]
    | succ d =>
      obtain ⟨hd_len, hpos, hV'⟩ := valid_take_le hV
      have hlt : (decTop (d + 1) r).length < n := by rw [length_decTop, ← hlen]; simp
      have hIH := ih (decTop (d + 1) r).length hlt (decTop (d + 1) r) rfl
        (sortedDesc_decTop (d + 1) r) (hV' hS)
      have hs := sum_decTop hd_len hpos
      rw [E.eq_3, List.sum_cons]
      simp only [List.sum_cons]
      omega

theorem main_induction : ∀ n : ℕ,
    (∀ X Y : List ℕ, X.length = n → ElemTrans X Y → DomLe (E X) (E Y)) ∧
    (∀ U V : List ℕ, U.length = n → Step2 U V →
      (E U).length = (E V).length ∧ (E U).sum = (E V).sum + 1 ∧
      ∀ k, ((E U).take k).sum ≤ ((E V).take k).sum + 1) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  constructor
  · intro X Y hlen hXY
    obtain ⟨d, rx, ry, rfl, hY⟩ := elemTrans_heads hXY
    have hSX : SortedDesc (d :: rx) := hXY.1
    have hSY : SortedDesc Y := hXY.2.1
    have hVX : Valid (d :: rx) := hXY.2.2.1
    have hVY : Valid Y := hXY.2.2.2.1
    have hlen' : (d :: rx).length = Y.length := elemTrans_length hXY
    have hsum_eq : (d :: rx).sum = Y.sum := by
      obtain ⟨_, _, _, _, M, a, b, hb1, _, hMX, hMY⟩ := hXY
      have h1 := congrArg Multiset.sum hMX
      have h2 := congrArg Multiset.sum hMY
      simp only [Multiset.sum_coe, Multiset.sum_cons] at h1 h2
      omega
    have hEsum : (E (d :: rx)).sum = (E Y).sum := by
      have h1 := two_mul_E_sum_eq (d :: rx).length (d :: rx) rfl hSX hVX
      have h2 := two_mul_E_sum_eq Y.length Y rfl hSY hVY
      omega
    refine ⟨by rw [length_E, length_E, hlen'], hEsum, ?_⟩
    rcases hY with rfl | rfl
    · rw [E_cons_of_sortedDesc hSX, E_cons_of_sortedDesc hSY]
      rcases elemTrans_same_head hXY with heq | hET'
      · rw [heq]
        intro k; exact le_rfl
      · have hlt : (decTop d rx).length < n := by rw [length_decTop, ← hlen]; simp
        have hDom' := (ih (decTop d rx).length hlt).1 (decTop d rx) (decTop d ry) rfl hET'
        intro k
        cases k with
        | zero => simp
        | succ k =>
          simp only [List.take_succ_cons, List.sum_cons]
          exact Nat.add_le_add_left (hDom'.2.2 k) d
    · rw [E_cons_of_sortedDesc hSX, E_cons_of_sortedDesc hSY]
      have hSt2 := elemTrans_inc_head hXY
      have hlt : (decTop d rx).length < n := by rw [length_decTop, ← hlen]; simp
      have hIH2 := (ih (decTop d rx).length hlt).2 (decTop d rx) (decTop (d + 1) ry) rfl hSt2
      intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons, List.sum_cons]
        have := hIH2.2.2 k
        omega
  · intro U V hlen hUV
    obtain ⟨d, ru, rv, rfl, hd1, hV⟩ := step2_heads hUV
    have hSU : SortedDesc (d :: ru) := hUV.1
    have hSV : SortedDesc V := hUV.2.1
    have hVU : Valid (d :: ru) := hUV.2.2.1
    have hVV : Valid V := hUV.2.2.2.1
    have hlen' : (d :: ru).length = V.length := step2_length hUV
    have hsum_eq : (d :: ru).sum = V.sum + 2 := by
      obtain ⟨_, _, _, _, _, _, _, _, hcase⟩ := hUV
      rcases hcase with ⟨M, a, b, hb1, hba, _, hMU, hMV⟩ | ⟨M, a, ha2, _, hMU, hMV⟩
      · have h1 := congrArg Multiset.sum hMU
        have h2 := congrArg Multiset.sum hMV
        simp only [Multiset.sum_coe, Multiset.sum_cons] at h1 h2
        have ha1 : 1 ≤ a := le_trans hb1 hba
        omega
      · have h1 := congrArg Multiset.sum hMU
        have h2 := congrArg Multiset.sum hMV
        simp only [Multiset.sum_coe, Multiset.sum_cons] at h1 h2
        omega
    have hEsum : (E (d :: ru)).sum = (E V).sum + 1 := by
      have h1 := two_mul_E_sum_eq (d :: ru).length (d :: ru) rfl hSU hVU
      have h2 := two_mul_E_sum_eq V.length V rfl hSV hVV
      omega
    refine ⟨by rw [length_E, length_E, hlen'], hEsum, ?_⟩
    rcases hV with rfl | rfl
    · rw [E_cons_of_sortedDesc hSU, E_cons_of_sortedDesc hSV]
      rcases step2_dec_head hUV with heq | hET'
      · rw [heq]
        intro k
        cases k with
        | zero => simp
        | succ k => simp only [List.take_succ_cons, List.sum_cons]; omega
      · have hlt : (decTop d ru).length < n := by rw [length_decTop, ← hlen]; simp
        have hDom' := (ih (decTop d ru).length hlt).1 (decTop d ru) (decTop (d - 1) rv) rfl hET'
        intro k
        cases k with
        | zero => simp
        | succ k =>
          simp only [List.take_succ_cons, List.sum_cons]
          have := hDom'.2.2 k
          omega
    · rw [E_cons_of_sortedDesc hSU, E_cons_of_sortedDesc hSV]
      have hSt2' := step2_same_head hUV
      have hlt : (decTop d ru).length < n := by rw [length_decTop, ← hlen]; simp
      have hIH2 := (ih (decTop d ru).length hlt).2 (decTop d ru) (decTop d rv) rfl hSt2'
      intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons, List.sum_cons]
        have := hIH2.2.2 k
        omega

/-- Descending sorted degree sequence of a finite simple graph. -/
noncomputable def degSeq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)

theorem residue_eq_residueAux {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph.residue G = SimpleGraph.residueAux (degSeq G) := rfl

theorem sortedDesc_multiset_sort (s : Multiset ℕ) : SortedDesc (s.sort (· ≥ ·)) := by
  refine Quotient.inductionOn s fun l => ?_
  change SortedDesc ((l : Multiset ℕ).sort (· ≥ ·))
  rw [Multiset.coe_sort]
  exact sortedDesc_mergeSort l

theorem sortedDesc_degSeq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SortedDesc (degSeq G) :=
  sortedDesc_multiset_sort _

theorem coe_degSeq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degSeq G : Multiset ℕ) = Finset.univ.val.map fun v => G.degree v :=
  Multiset.sort_eq _ (· ≥ ·)

theorem induce_ne_degree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (x : {y : V | y ≠ v}) :
    (G.induce {y : V | y ≠ v}).degree x + (if G.Adj v x.1 then 1 else 0) = G.degree x.1 := by
  let U : Set V := {y | y ≠ v}
  have hsub : G.neighborFinset x.1 =
      ((G.induce U).neighborFinset x).map (Function.Embedding.subtype _) ∪
        (if G.Adj v x.1 then {v} else ∅) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · intro hy
      have hadj : G.Adj x.1 y := (G.mem_neighborFinset x.1 y).mp hy
      by_cases hyv : y = v
      · right; subst hyv; simp [hadj.symm]
      · left; exact ⟨⟨y, hyv⟩, ((G.induce U).mem_neighborFinset x ⟨y, hyv⟩).mpr hadj, rfl⟩
    · intro hy
      rcases hy with ⟨⟨y', hy'⟩, hyadj, rfl⟩ | h2
      · exact (G.mem_neighborFinset x.1 y').mpr (((G.induce U).mem_neighborFinset x ⟨y', hy'⟩).mp hyadj)
      · split_ifs at h2 with hadj
        · simp only [Finset.mem_singleton] at h2; subst h2
          exact (G.mem_neighborFinset x.1 y).mpr hadj.symm
        · simp at h2
  have hdisj : Disjoint (((G.induce U).neighborFinset x).map (Function.Embedding.subtype _))
      (if G.Adj v x.1 then {v} else ∅) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hy1
    obtain ⟨y', _, rfl⟩ := hy1
    split_ifs at hy2 with hadj
    · simp only [Finset.mem_singleton] at hy2; exact y'.2 hy2
    · simp at hy2
  have hcard := congrArg Finset.card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  dsimp [U] at hcard
  by_cases hadj : G.Adj v x.1
  · rw [if_pos hadj] at hcard ⊢; simpa using hcard.symm
  · rw [if_neg hadj] at hcard ⊢; simpa using hcard.symm

theorem degSeq_induce_ne_map {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (degSeq (G.induce {y : V | y ≠ v}) : Multiset ℕ) =
      (Finset.univ.erase v).val.map
        (fun y => if y ∈ G.neighborFinset v then G.degree y - 1 else G.degree y) := by
  rw [coe_degSeq]
  let f : {y : V | y ≠ v} → V := Subtype.val
  have hmap : (Finset.univ.val.map f) = (Finset.univ.erase v).val := by
    have hs : Finset.univ.map (Function.Embedding.subtype (fun y : V => y ≠ v)) =
        Finset.univ.erase v := by
      ext y; simp
    rw [← hs]
    rfl
  rw [← hmap, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  have hdeg := induce_ne_degree G v x
  simp only [Function.comp_apply, f]
  by_cases hadj : G.Adj v x.1
  · have hmem : x.1 ∈ G.neighborFinset v := (G.mem_neighborFinset v x.1).mpr hadj
    rw [if_pos hmem, if_pos hadj] at *
    omega
  · have hnmem : x.1 ∉ G.neighborFinset v := fun hm => hadj ((G.mem_neighborFinset v x.1).mp hm)
    rw [if_neg hnmem, if_neg hadj] at *
    omega

def switchPairs {V : Type} [DecidableEq V] (v u w z : V) : Finset (Sym2 V) :=
  {s(v, w), s(u, z), s(v, u), s(w, z)}

def switchGraph {V : Type} [DecidableEq V] (G0 : SimpleGraph V) (v u w z : V)
    (huv : u ≠ v) (hwv : w ≠ v) (hzw : z ≠ w) (hzu : z ≠ u) : SimpleGraph V where
  Adj x y := if s(x, y) ∈ switchPairs v u w z then ¬ G0.Adj x y else G0.Adj x y
  symm := ⟨by
    intro x y hxy
    by_cases hmem : s(x, y) ∈ switchPairs v u w z
    · have hmem' : s(y, x) ∈ switchPairs v u w z := by rwa [Sym2.eq_swap]
      rw [if_pos hmem] at hxy
      rw [if_pos hmem']
      exact fun h => hxy h.symm
    · have hmem' : s(y, x) ∉ switchPairs v u w z := by rwa [Sym2.eq_swap]
      rw [if_neg hmem] at hxy
      rw [if_neg hmem']
      exact hxy.symm⟩
  loopless := ⟨by
    intro x hx
    have hdiag : s(x, x) ∉ switchPairs v u w z := by
      intro hmem
      simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
      rcases hmem with (⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h⟩ | ⟨rfl, h⟩) |
        (⟨rfl, h⟩ | ⟨rfl, h⟩) | (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact hwv h.symm
      · exact hwv h
      · exact hzu h.symm
      · exact hzu h
      · exact huv h.symm
      · exact huv h
      · exact hzw h.symm
      · exact hzw h
    rw [if_neg hdiag] at hx
    exact G0.ne_of_adj hx rfl⟩

instance instDecidableRelSwitchGraph {V : Type} [DecidableEq V] (G0 : SimpleGraph V)
    [DecidableRel G0.Adj] (v u w z : V) (huv : u ≠ v) (hwv : w ≠ v) (hzw : z ≠ w) (hzu : z ≠ u) :
    DecidableRel (switchGraph G0 v u w z huv hwv hzw hzu).Adj := fun x y =>
  inferInstanceAs (Decidable (if s(x, y) ∈ switchPairs v u w z then ¬ G0.Adj x y else G0.Adj x y))

theorem switchGraph_props {V : Type} [Fintype V] [DecidableEq V]
    (G0 : SimpleGraph V) [DecidableRel G0.Adj] (v u w z : V)
    (huv : u ≠ v) (hwv : w ≠ v) (huw : u ≠ w) (hzw : z ≠ w) (hzu : z ≠ u) (hzv : z ≠ v)
    (hadj_uz : G0.Adj u z) (h_nadj_wz : ¬ G0.Adj w z) (hadj_vw : G0.Adj v w) (h_nadj_vu : ¬ G0.Adj v u) :
    let G' := switchGraph G0 v u w z huv hwv hzw hzu
    G'.neighborFinset v = insert u ((G0.neighborFinset v).erase w) ∧
    (∀ x : V, G'.degree x = G0.degree x) ∧
    degSeq G' = degSeq G0 ∧
    G'.maxDegree = G0.maxDegree ∧
    SimpleGraph.residue G0 = SimpleGraph.residue G' := by
  intro G'
  have h_not_sp : ∀ x y : V, x ≠ v → x ≠ u → x ≠ w → x ≠ z → s(x, y) ∉ switchPairs v u w z := by
    intro x y hxv hxu hxw hxz hmem
    simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
    rcases hmem with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩) |
      (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact hxv rfl
    · exact hxw rfl
    · exact hxu rfl
    · exact hxz rfl
    · exact hxv rfl
    · exact hxu rfl
    · exact hxw rfl
    · exact hxz rfl
  have hG'nb_v : G'.neighborFinset v = insert u ((G0.neighborFinset v).erase w) := by
    ext y
    rw [G'.mem_neighborFinset]
    dsimp only [G', switchGraph]
    by_cases hyu : y = u
    · have hmem : s(v, u) ∈ switchPairs v u w z := by simp [switchPairs]
      rw [hyu, if_pos hmem]; simp [Finset.mem_insert, h_nadj_vu]
    · by_cases hyw : y = w
      · have hmem : s(v, w) ∈ switchPairs v u w z := by simp [switchPairs]
        rw [hyw, if_pos hmem]; simp [Finset.mem_insert, Finset.mem_erase, hadj_vw, huw.symm]
      · have hnot : s(v, y) ∉ switchPairs v u w z := by
          intro hmem
          simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
          rcases hmem with (⟨_, h2⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨h1, _⟩) |
            (⟨_, h2⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨h1, _⟩)
          · exact hyw h2
          · exact hwv h1.symm
          · exact huv h1.symm
          · exact hzv h1.symm
          · exact hyu h2
          · exact huv h1.symm
          · exact hwv h1.symm
          · exact hzv h1.symm
        rw [if_neg hnot]; simp [Finset.mem_insert, Finset.mem_erase, hyu, hyw]
  have hG'nb_u : G'.neighborFinset u = insert v ((G0.neighborFinset u).erase z) := by
    ext y
    rw [G'.mem_neighborFinset]
    dsimp only [G', switchGraph]
    by_cases hyv : y = v
    · have hmem : s(u, v) ∈ switchPairs v u w z := by simp [switchPairs, Sym2.eq_swap]
      have h_nadj_uv : ¬ G0.Adj u v := fun h => h_nadj_vu h.symm
      rw [hyv, if_pos hmem]; simp [Finset.mem_insert, h_nadj_uv]
    · by_cases hyz : y = z
      · have hmem : s(u, z) ∈ switchPairs v u w z := by simp [switchPairs]
        rw [hyz, if_pos hmem]; simp [Finset.mem_insert, Finset.mem_erase, hadj_uz, hzv]
      · have hnot : s(u, y) ∉ switchPairs v u w z := by
          intro hmem
          simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
          rcases hmem with (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨_, h2⟩ | ⟨h1, _⟩) |
            (⟨h1, _⟩ | ⟨_, h2⟩) | (⟨h1, _⟩ | ⟨h1, _⟩)
          · exact huv h1
          · exact huw h1
          · exact hyz h2
          · exact hzu h1.symm
          · exact huv h1
          · exact hyv h2
          · exact huw h1
          · exact hzu h1.symm
        rw [if_neg hnot]; simp [Finset.mem_insert, Finset.mem_erase, hyv, hyz]
  have hG'nb_w : G'.neighborFinset w = insert z ((G0.neighborFinset w).erase v) := by
    ext y
    rw [G'.mem_neighborFinset]
    dsimp only [G', switchGraph]
    by_cases hyz : y = z
    · have hmem : s(w, z) ∈ switchPairs v u w z := by simp [switchPairs]
      rw [hyz, if_pos hmem]; simp [Finset.mem_insert, h_nadj_wz]
    · by_cases hyv : y = v
      · have hmem : s(w, v) ∈ switchPairs v u w z := by simp [switchPairs, Sym2.eq_swap]
        rw [hyv, if_pos hmem]; simp [Finset.mem_insert, Finset.mem_erase, hadj_vw.symm, hzv.symm]
      · have hnot : s(w, y) ∉ switchPairs v u w z := by
          intro hmem
          simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
          rcases hmem with (⟨h1, _⟩ | ⟨_, h2⟩) | (⟨h1, _⟩ | ⟨h1, _⟩) |
            (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨_, h2⟩ | ⟨h1, _⟩)
          · exact hwv h1
          · exact hyv h2
          · exact huw h1.symm
          · exact hzw h1.symm
          · exact hwv h1
          · exact huw h1.symm
          · exact hyz h2
          · exact hzw h1.symm
        rw [if_neg hnot]; simp [Finset.mem_insert, Finset.mem_erase, hyz, hyv]
  have hG'nb_z : G'.neighborFinset z = insert w ((G0.neighborFinset z).erase u) := by
    ext y
    rw [G'.mem_neighborFinset]
    dsimp only [G', switchGraph]
    by_cases hyw : y = w
    · have hmem : s(z, w) ∈ switchPairs v u w z := by simp [switchPairs, Sym2.eq_swap]
      have h_nadj_zw : ¬ G0.Adj z w := fun h => h_nadj_wz h.symm
      rw [hyw, if_pos hmem]; simp [Finset.mem_insert, h_nadj_zw]
    · by_cases hyu : y = u
      · have hmem : s(z, u) ∈ switchPairs v u w z := by simp [switchPairs, Sym2.eq_swap]
        rw [hyu, if_pos hmem]; simp [Finset.mem_insert, Finset.mem_erase, hadj_uz.symm, huw]
      · have hnot : s(z, y) ∉ switchPairs v u w z := by
          intro hmem
          simp only [switchPairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
          rcases hmem with (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨_, h2⟩) |
            (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact hzv h1
          · exact hzw h1
          · exact hzu h1
          · exact hyu h2
          · exact hzv h1
          · exact hzu h1
          · exact hzw h1
          · exact hyw h2
        rw [if_neg hnot]; simp [Finset.mem_insert, Finset.mem_erase, hyw, hyu]
  have hw_nb : w ∈ G0.neighborFinset v := (G0.mem_neighborFinset v w).mpr hadj_vw
  have hu_nnb : u ∉ G0.neighborFinset v := fun h => h_nadj_vu ((G0.mem_neighborFinset v u).mp h)
  have hdeg_same : ∀ x : V, G'.degree x = G0.degree x := by
    intro x
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    by_cases hxv : x = v
    · rw [hxv, hG'nb_v]
      have hnu : u ∉ (G0.neighborFinset v).erase w := fun h => hu_nnb (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hnu, Finset.card_erase_of_mem hw_nb]
      have : 1 ≤ (G0.neighborFinset v).card := Finset.card_pos.mpr ⟨w, hw_nb⟩
      omega
    · by_cases hxu : x = u
      · rw [hxu, hG'nb_u]
        have hnv : v ∉ (G0.neighborFinset u).erase z := fun h =>
          h_nadj_vu ((G0.mem_neighborFinset u v).mp (Finset.mem_of_mem_erase h)).symm
        have hzm : z ∈ G0.neighborFinset u := (G0.mem_neighborFinset u z).mpr hadj_uz
        rw [Finset.card_insert_of_notMem hnv, Finset.card_erase_of_mem hzm]
        have : 1 ≤ (G0.neighborFinset u).card := Finset.card_pos.mpr ⟨z, hzm⟩
        omega
      · by_cases hxw : x = w
        · rw [hxw, hG'nb_w]
          have hnz : z ∉ (G0.neighborFinset w).erase v := fun h =>
            h_nadj_wz ((G0.mem_neighborFinset w z).mp (Finset.mem_of_mem_erase h))
          have hvm : v ∈ G0.neighborFinset w := (G0.mem_neighborFinset w v).mpr hadj_vw.symm
          rw [Finset.card_insert_of_notMem hnz, Finset.card_erase_of_mem hvm]
          have : 1 ≤ (G0.neighborFinset w).card := Finset.card_pos.mpr ⟨v, hvm⟩
          omega
        · by_cases hxz : x = z
          · rw [hxz, hG'nb_z]
            have hnw : w ∉ (G0.neighborFinset z).erase u := fun h =>
              h_nadj_wz ((G0.mem_neighborFinset z w).mp (Finset.mem_of_mem_erase h)).symm
            have hum : u ∈ G0.neighborFinset z := (G0.mem_neighborFinset z u).mpr hadj_uz.symm
            rw [Finset.card_insert_of_notMem hnw, Finset.card_erase_of_mem hum]
            have : 1 ≤ (G0.neighborFinset z).card := Finset.card_pos.mpr ⟨u, hum⟩
            omega
          · have hnb_eq : G'.neighborFinset x = G0.neighborFinset x := by
              ext y
              rw [G'.mem_neighborFinset, G0.mem_neighborFinset]
              have hnot := h_not_sp x y hxv hxu hxw hxz
              dsimp only [G', switchGraph]
              rw [if_neg hnot]
            rw [hnb_eq]
  have hdegSeq_eq : degSeq G' = degSeq G0 := by
    apply sortedDesc_eq_of_coe (sortedDesc_degSeq G') (sortedDesc_degSeq G0)
    rw [coe_degSeq, coe_degSeq]
    exact Multiset.map_congr rfl fun x _ => hdeg_same x
  have hmax_eq : G'.maxDegree = G0.maxDegree := by
    refine le_antisymm ?_ ?_
    · exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun x =>
        hdeg_same x ▸ G0.degree_le_maxDegree x
    · exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun x =>
        (hdeg_same x).symm ▸ G'.degree_le_maxDegree x
  have hres_eq : SimpleGraph.residue G0 = SimpleGraph.residue G' := by
    rw [residue_eq_residueAux, residue_eq_residueAux, hdegSeq_eq]
  exact ⟨hG'nb_v, hdeg_same, hdegSeq_eq, hmax_eq, hres_eq⟩

theorem switchGraph_induce_residue_le {V : Type} [Fintype V] [DecidableEq V]
    (G0 G' : SimpleGraph V) [DecidableRel G0.Adj] [DecidableRel G'.Adj]
    (v u w : V) (huv : u ≠ v) (hwv : w ≠ v) (huw : u ≠ w)
    (h_nadj_vu : ¬ G0.Adj v u) (hadj_vw : G0.Adj v w) (hw_le_u : G0.degree w ≤ G0.degree u)
    (hG'nb_v : G'.neighborFinset v = insert u ((G0.neighborFinset v).erase w))
    (hdeg_same : ∀ x : V, G'.degree x = G0.degree x)
    (hIH_G'U : Valid (degSeq (G'.induce {y : V | y ≠ v})))
    (hIH_U : Valid (degSeq (G0.induce {y : V | y ≠ v}))) :
    SimpleGraph.residue (G'.induce {y : V | y ≠ v}) ≤
      SimpleGraph.residue (G0.induce {y : V | y ≠ v}) := by
  let u' : {y : V | y ≠ v} := ⟨u, huv⟩
  let w' : {y : V | y ≠ v} := ⟨w, hwv⟩
  have huw' : u' ≠ w' := fun h => huw (congrArg Subtype.val h)
  have h_same_rest : ∀ x : {y : V | y ≠ v}, x ≠ u' → x ≠ w' →
      (G'.induce {y : V | y ≠ v}).degree x = (G0.induce {y : V | y ≠ v}).degree x := by
    intro x hxu hxw
    have h1 := induce_ne_degree G' v x
    have h2 := induce_ne_degree G0 v x
    have hadj_same : G'.Adj v x.1 ↔ G0.Adj v x.1 := by
      rw [← G'.mem_neighborFinset, ← G0.mem_neighborFinset, hG'nb_v,
        Finset.mem_insert, Finset.mem_erase]
      have hx1 : x.1 ≠ u := fun h => hxu (Subtype.ext h)
      have hx2 : x.1 ≠ w := fun h => hxw (Subtype.ext h)
      simp [hx1, hx2]
    rw [hdeg_same x.1] at h1
    by_cases h_a : G'.Adj v x.1 <;> by_cases h_b : G0.Adj v x.1
    · rw [if_pos h_a] at h1; rw [if_pos h_b] at h2; omega
    · exact (h_b (hadj_same.mp h_a)).elim
    · exact (h_a (hadj_same.mpr h_b)).elim
    · rw [if_neg h_a] at h1; rw [if_neg h_b] at h2; omega
  have h_u'_G' : (G'.induce {y : V | y ≠ v}).degree u' = G0.degree u - 1 := by
    have h1 := induce_ne_degree G' v u'
    have hadj' : G'.Adj v u'.1 := (G'.mem_neighborFinset v u).mp (by rw [hG'nb_v]; simp)
    have hdeg_u' : G'.degree u'.1 = G0.degree u := hdeg_same u
    rw [if_pos hadj', hdeg_u'] at h1
    exact Nat.eq_sub_of_add_eq h1
  have h_u'_G0 : (G0.induce {y : V | y ≠ v}).degree u' = G0.degree u := by
    have h2 := induce_ne_degree G0 v u'
    have hnadj : ¬ G0.Adj v u'.1 := h_nadj_vu
    rw [if_neg hnadj, add_zero] at h2
    exact h2
  have h_w'_G' : (G'.induce {y : V | y ≠ v}).degree w' = G0.degree w := by
    have h1 := induce_ne_degree G' v w'
    have hnadj' : ¬ G'.Adj v w'.1 := by
      intro hadj
      have := (G'.mem_neighborFinset v w).mpr hadj
      rw [hG'nb_v, Finset.mem_insert, Finset.mem_erase] at this
      rcases this with h | ⟨hne, _⟩
      · exact huw h.symm
      · exact hne rfl
    have hdeg_w' : G'.degree w'.1 = G0.degree w := hdeg_same w
    rw [if_neg hnadj', add_zero, hdeg_w'] at h1
    exact h1
  have h_w'_G0 : (G0.induce {y : V | y ≠ v}).degree w' = G0.degree w - 1 := by
    have h2 := induce_ne_degree G0 v w'
    have hadj : G0.Adj v w'.1 := hadj_vw
    rw [if_pos hadj] at h2
    exact Nat.eq_sub_of_add_eq h2
  have hw_ge1 : 1 ≤ G0.degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, (G0.mem_neighborFinset w v).mpr hadj_vw.symm⟩
  have hu_ge1 : 1 ≤ G0.degree u := le_trans hw_ge1 hw_le_u
  have hcoe_split : ∀ f : {y : V | y ≠ v} → ℕ, (Finset.univ.val.map f) =
      f u' ::ₘ f w' ::ₘ (((Finset.univ.erase u').erase w').val.map f) := by
    intro f
    let rest := (Finset.univ.erase u').erase w'
    have h1 : Finset.univ = insert u' (insert w' rest) := by
      ext x; simp only [rest, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_iff]
      by_cases hxu : x = u'
      · exact Or.inl hxu
      · by_cases hxw : x = w'
        · exact Or.inr (Or.inl hxw)
        · exact Or.inr (Or.inr ⟨hxw, hxu, trivial⟩)
    have hn1 : u' ∉ insert w' rest := by simp [rest, huw']
    have hn2 : w' ∉ rest := Finset.notMem_erase w' _
    conv_lhs => rw [h1, Finset.insert_val_of_notMem hn1, Finset.insert_val_of_notMem hn2]
    rw [Multiset.map_cons, Multiset.map_cons]
  have hrest_eq : (((Finset.univ.erase u').erase w').val.map fun x =>
      (G'.induce {y : V | y ≠ v}).degree x) =
      (((Finset.univ.erase u').erase w').val.map fun x =>
      (G0.induce {y : V | y ≠ v}).degree x) := by
    refine Multiset.map_congr rfl fun x hx => ?_
    have hxw : x ≠ w' := (Finset.mem_erase.mp hx).1
    have hxu : x ≠ u' := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    exact h_same_rest x hxu hxw
  rcases eq_or_lt_of_le hw_le_u with h_eq | h_lt
  · have hds_same : degSeq (G'.induce {y : V | y ≠ v}) = degSeq (G0.induce {y : V | y ≠ v}) := by
      apply sortedDesc_eq_of_coe (sortedDesc_degSeq _) (sortedDesc_degSeq _)
      rw [coe_degSeq, coe_degSeq, hcoe_split, hcoe_split, hrest_eq, h_u'_G', h_u'_G0,
        h_w'_G', h_w'_G0, h_eq, Multiset.cons_swap]
    rw [residue_eq_residueAux, residue_eq_residueAux, hds_same]
  · have hET : ElemTrans (degSeq (G'.induce {y : V | y ≠ v})) (degSeq (G0.induce {y : V | y ≠ v})) := by
      refine ⟨sortedDesc_degSeq _, sortedDesc_degSeq _, hIH_G'U, hIH_U,
        (((Finset.univ.erase u').erase w').val.map fun x => (G0.induce {y : V | y ≠ v}).degree x),
        G0.degree u - 1, G0.degree w, hw_ge1, by omega, ?_, ?_⟩
      · rw [coe_degSeq, hcoe_split, hrest_eq, h_u'_G', h_w'_G']
      · rw [coe_degSeq, hcoe_split, h_u'_G0, h_w'_G0, Nat.sub_add_cancel hu_ge1]
    have hDom := (main_induction (degSeq (G'.induce {y : V | y ≠ v})).length).1 _ _ rfl hET
    rw [residue_eq_residueAux, residue_eq_residueAux]
    exact residue_le_of_domLe (sortedDesc_degSeq _) (sortedDesc_degSeq _) hIH_G'U hIH_U hDom

theorem valid_and_residue_le_delete_max : ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    Valid (degSeq G) ∧
    (∀ v : V, G.degree v = G.maxDegree → 1 ≤ G.degree v →
      SimpleGraph.residue G ≤ SimpleGraph.residue (G.induce {y : V | y ≠ v})) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih_outer V _ _ G _ hcard
  by_cases hzero : G.maxDegree = 0
  · have hdeg0 : ∀ v : V, G.degree v = 0 := fun v =>
      Nat.eq_zero_of_le_zero (hzero ▸ G.degree_le_maxDegree v)
    have hV0 : Valid (degSeq G) := by
      have hall0 : ∀ x ∈ degSeq G, x = 0 := by
        intro x hx
        have : x ∈ (degSeq G : Multiset ℕ) := Multiset.mem_coe.mpr hx
        rw [coe_degSeq] at this
        obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp this
        exact hdeg0 v
      cases hds : degSeq G with
      | nil => rw [Valid.eq_1]; trivial
      | cons a t =>
        have ha : a = 0 := hall0 a (by rw [hds]; simp)
        subst ha; rw [Valid.eq_2]; trivial
    refine ⟨hV0, fun v hv h1 => by omega⟩
  · have hmax_pos : 1 ≤ G.maxDegree := Nat.pos_of_ne_zero hzero
    have hV_pos : 0 < Fintype.card V := by
      by_contra hnot
      have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
      have : G.maxDegree = 0 := by simp [SimpleGraph.maxDegree]
      omega
    have : Nonempty V := Fintype.card_pos_iff.mp hV_pos
    have h_inner : ∀ (k : ℕ) (G0 : SimpleGraph V) [DecidableRel G0.Adj] (v : V) (S : Finset V),
        G0.degree v = G0.maxDegree → 1 ≤ G0.degree v →
        S ∈ (Finset.univ.erase v).powersetCard (G0.degree v) →
        (∀ T ∈ (Finset.univ.erase v).powersetCard (G0.degree v),
          ∑ x ∈ T, G0.degree x ≤ ∑ x ∈ S, G0.degree x) →
        (S \ G0.neighborFinset v).card = k →
        Valid (degSeq G0) ∧
        SimpleGraph.residue G0 ≤ SimpleGraph.residue (G0.induce {y : V | y ≠ v}) := by
      intro k
      refine Nat.strong_induction_on k ?_
      intro k ih_inner G0 _ v S hv_max hv_pos hS_mem hS_opt hk_eq
      let d := G0.degree v
      let U : Set V := {y | y ≠ v}
      have hU_lt : Fintype.card U < n := by
        rw [← hcard, Fintype.card_subtype]
        have hflt : Finset.univ.filter (· ∈ U) = Finset.univ.erase v := by ext y; simp [U]
        rw [hflt, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
        omega
      have hIH_U := (ih_outer (Fintype.card U) hU_lt U (G0.induce U) rfl).1
      rw [Finset.mem_powersetCard] at hS_mem
      obtain ⟨hS_sub, hS_card⟩ := hS_mem
      by_cases hk0 : k = 0
      · subst hk0
        have hS_sdiff : S \ G0.neighborFinset v = ∅ := Finset.card_eq_zero.mp hk_eq
        have hS_sub_nb : S ⊆ G0.neighborFinset v := Finset.sdiff_eq_empty_iff_subset.mp hS_sdiff
        have hS_eq_nb : G0.neighborFinset v = S :=
          (Finset.eq_of_subset_of_card_le hS_sub_nb
            (by rw [hS_card, SimpleGraph.card_neighborFinset_eq_degree])).symm
        have hS_ge_rest : ∀ u ∈ S, ∀ w ∈ Finset.univ.erase v \ S, G0.degree w ≤ G0.degree u := by
          intro u hu w hw
          by_contra hlt
          have hlt' : G0.degree u < G0.degree w := Nat.lt_of_not_le hlt
          have hw_er : w ∈ Finset.univ.erase v := (Finset.mem_sdiff.mp hw).1
          have hw_notS : w ∉ S := (Finset.mem_sdiff.mp hw).2
          let T := insert w (S.erase u)
          have hT_mem : T ∈ (Finset.univ.erase v).powersetCard (G0.degree v) := by
            rw [Finset.mem_powersetCard]
            refine ⟨Finset.insert_subset_iff.mpr ⟨hw_er, (Finset.erase_subset u S).trans hS_sub⟩, ?_⟩
            rw [Finset.card_insert_of_notMem (fun h => hw_notS (Finset.mem_of_mem_erase h)),
              Finset.card_erase_of_mem hu, hS_card]
            omega
          have hT_sum := hS_opt T hT_mem
          have hsum1 : ∑ x ∈ T, G0.degree x = G0.degree w + ∑ x ∈ S.erase u, G0.degree x :=
            Finset.sum_insert (fun h => hw_notS (Finset.mem_of_mem_erase h))
          have hsum2 : ∑ x ∈ S, G0.degree x = G0.degree u + ∑ x ∈ S.erase u, G0.degree x :=
            (Finset.add_sum_erase S (fun x => G0.degree x) hu).symm
          omega
        let L1 := (S.val.map fun x => G0.degree x).sort (· ≥ ·)
        let L2 := (((Finset.univ.erase v \ S).val.map fun x => G0.degree x)).sort (· ≥ ·)
        have hSL1 : SortedDesc L1 := sortedDesc_multiset_sort _
        have hSL2 : SortedDesc L2 := sortedDesc_multiset_sort _
        have hL1_coe : (L1 : Multiset ℕ) = S.val.map fun x => G0.degree x := Multiset.sort_eq _ _
        have hL2_coe : (L2 : Multiset ℕ) = (Finset.univ.erase v \ S).val.map fun x => G0.degree x :=
          Multiset.sort_eq _ _
        have hL1_len : L1.length = d := by
          have := congrArg Multiset.card hL1_coe
          simpa [d, hS_card] using this
        have hL12_pw : SortedDesc (L1 ++ L2) := by
          rw [SortedDesc, List.pairwise_append]
          refine ⟨hSL1, hSL2, fun a ha b hb => ?_⟩
          have ha' : a ∈ (L1 : Multiset ℕ) := Multiset.mem_coe.mpr ha
          have hb' : b ∈ (L2 : Multiset ℕ) := Multiset.mem_coe.mpr hb
          rw [hL1_coe] at ha'; rw [hL2_coe] at hb'
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp ha'
          obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hb'
          exact hS_ge_rest u hu w hw
        have h_erase_split : (Finset.univ.erase v).val = S.val + (Finset.univ.erase v \ S).val := by
          apply Multiset.ext.mpr
          intro a
          rw [Multiset.count_add]
          by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ Finset.univ.erase v \ S
          · exfalso; exact (Finset.mem_sdiff.mp h2).2 h1
          · have h1' : a ∈ Finset.univ.erase v := hS_sub h1
            rw [Multiset.count_eq_one_of_mem (Finset.univ.erase v).nodup (Finset.mem_val.mpr h1'),
              Multiset.count_eq_one_of_mem S.nodup (Finset.mem_val.mpr h1),
              Multiset.count_eq_zero.mpr (mt Finset.mem_val.mp h2)]
          · have h2' : a ∈ Finset.univ.erase v := (Finset.mem_sdiff.mp h2).1
            rw [Multiset.count_eq_one_of_mem (Finset.univ.erase v).nodup (Finset.mem_val.mpr h2'),
              Multiset.count_eq_zero.mpr (mt Finset.mem_val.mp h1),
              Multiset.count_eq_one_of_mem (Finset.univ.erase v \ S).nodup (Finset.mem_val.mpr h2)]
          · have hn : a ∉ Finset.univ.erase v := fun h => h2 (Finset.mem_sdiff.mpr ⟨h, h1⟩)
            rw [Multiset.count_eq_zero.mpr (mt Finset.mem_val.mp hn),
              Multiset.count_eq_zero.mpr (mt Finset.mem_val.mp h1),
              Multiset.count_eq_zero.mpr (mt Finset.mem_val.mp h2)]
        have hds_eq : degSeq G0 = d :: (L1 ++ L2) := by
          apply sortedDesc_eq_of_coe (sortedDesc_degSeq G0)
          · rw [SortedDesc, List.pairwise_cons]
            refine ⟨fun x hx => ?_, hL12_pw⟩
            have hx' : x ∈ (L1 ++ L2 : Multiset ℕ) := Multiset.mem_coe.mpr hx
            rw [← Multiset.coe_add, hL1_coe, hL2_coe, ← Multiset.map_add, ← h_erase_split] at hx'
            obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx'
            exact le_trans (G0.degree_le_maxDegree y) hv_max.symm.le
          · rw [coe_degSeq]
            have hu_v : (Finset.univ : Finset V).val = v ::ₘ (Finset.univ.erase v).val := by
              have h1 : insert v (Finset.univ.erase v) = Finset.univ :=
                Finset.insert_erase (Finset.mem_univ v)
              have hnot : v ∉ (Finset.univ.erase v).val := Finset.notMem_erase v _
              conv_lhs => rw [← h1]
              exact Finset.insert_val_of_notMem hnot
            rw [hu_v, Multiset.map_cons, h_erase_split, Multiset.map_add, ← hL1_coe, ← hL2_coe]
            change d ::ₘ (L1 : Multiset ℕ) + (L2 : Multiset ℕ) = _
            rw [Multiset.cons_add, Multiset.coe_add]
            rfl
        have htake_d : (L1 ++ L2).take d = L1 := by
          rw [List.take_append_of_le_length hL1_len.symm.le, List.take_of_length_le hL1_len.le]
        have hdrop_d : (L1 ++ L2).drop d = L2 := by
          rw [List.drop_append_of_le_length hL1_len.symm.le, List.drop_of_length_le hL1_len.le]; simp
        have hpos_L1 : ∀ z ∈ (L1 ++ L2).take d, 1 ≤ z := by
          rw [htake_d]
          intro z hz
          have hz' : z ∈ (L1 : Multiset ℕ) := Multiset.mem_coe.mpr hz
          rw [hL1_coe] at hz'
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hz'
          have hu_adj : G0.Adj v u := (G0.mem_neighborFinset v u).mp (hS_eq_nb.symm ▸ hu)
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨v, (G0.mem_neighborFinset u v).mpr hu_adj.symm⟩
        have hdec_eq_U : degSeq (G0.induce U) = decTop d (L1 ++ L2) := by
          apply sortedDesc_eq_of_coe (sortedDesc_degSeq (G0.induce U)) (sortedDesc_decTop d _)
          rw [degSeq_induce_ne_map, multiset_decTop, htake_d, hdrop_d, h_erase_split, Multiset.map_add]
          have hm1 : S.val.map (fun y => if y ∈ G0.neighborFinset v then G0.degree y - 1 else G0.degree y) =
              ((L1.map (· - 1) : List ℕ) : Multiset ℕ) := by
            rw [← Multiset.map_coe, hL1_coe, Multiset.map_map]
            refine Multiset.map_congr rfl fun y hy => ?_
            rw [if_pos (hS_eq_nb ▸ hy)]
            rfl
          have hm2 : (Finset.univ.erase v \ S).val.map
              (fun y => if y ∈ G0.neighborFinset v then G0.degree y - 1 else G0.degree y) =
              (L2 : Multiset ℕ) := by
            rw [hL2_coe]
            refine Multiset.map_congr rfl fun y hy => ?_
            have hy_not : y ∉ G0.neighborFinset v := by
              rw [hS_eq_nb]; exact (Finset.mem_sdiff.mp hy).2
            rw [if_neg hy_not]
          rw [hm1, hm2]
        have hV_G0 : Valid (degSeq G0) := by
          rw [hds_eq]
          obtain ⟨d0, hd0⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
          rw [hd0, Valid.eq_3]
          refine ⟨by rw [← hd0, List.length_append, hL1_len]; omega, by rwa [← hd0], ?_⟩
          rw [← hd0, ← hdec_eq_U]
          exact hIH_U
        have hres_eq : SimpleGraph.residue G0 = SimpleGraph.residue (G0.induce U) := by
          rw [residue_eq_residueAux, residue_eq_residueAux, hds_eq]
          obtain ⟨d0, hd0⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
          rw [hd0, SimpleGraph.residueAux.eq_3 (d0 + 1) (L1 ++ L2) (by omega),
            havelHakimiStep_eq_decTop, ← hd0, ← hdec_eq_U]
        exact ⟨hV_G0, le_of_eq hres_eq⟩
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hS_sdiff_ne : (S \ G0.neighborFinset v).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨u, hu_sdiff⟩ := hS_sdiff_ne
        have huS : u ∈ S := (Finset.mem_sdiff.mp hu_sdiff).1
        have hu_nnb : u ∉ G0.neighborFinset v := (Finset.mem_sdiff.mp hu_sdiff).2
        have hnb_sdiff_ne : (G0.neighborFinset v \ S).Nonempty := by
          by_contra hnot
          rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hnot
          have hsub_eq := Finset.eq_of_subset_of_card_le hnot
            (by rw [SimpleGraph.card_neighborFinset_eq_degree, hS_card])
          rw [hsub_eq, Finset.sdiff_self] at hk_eq
          simp at hk_eq; omega
        obtain ⟨w, hw_sdiff⟩ := hnb_sdiff_ne
        have hw_nb : w ∈ G0.neighborFinset v := (Finset.mem_sdiff.mp hw_sdiff).1
        have hw_notS : w ∉ S := (Finset.mem_sdiff.mp hw_sdiff).2
        have huv : u ≠ v := (Finset.mem_erase.mp (hS_sub huS)).1
        have hwv : w ≠ v := (G0.ne_of_adj ((G0.mem_neighborFinset v w).mp hw_nb)).symm
        have huw : u ≠ w := fun h => hw_notS (h ▸ huS)
        have hw_le_u : G0.degree w ≤ G0.degree u := by
          by_contra hlt
          have hlt' : G0.degree u < G0.degree w := Nat.lt_of_not_le hlt
          let T := insert w (S.erase u)
          have hw_er : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩
          have hT_mem : T ∈ (Finset.univ.erase v).powersetCard (G0.degree v) := by
            rw [Finset.mem_powersetCard]
            refine ⟨Finset.insert_subset_iff.mpr ⟨hw_er, (Finset.erase_subset u S).trans hS_sub⟩, ?_⟩
            rw [Finset.card_insert_of_notMem (fun h => hw_notS (Finset.mem_of_mem_erase h)),
              Finset.card_erase_of_mem huS, hS_card]
            omega
          have hT_sum := hS_opt T hT_mem
          have hsum1 : ∑ x ∈ T, G0.degree x = G0.degree w + ∑ x ∈ S.erase u, G0.degree x :=
            Finset.sum_insert (fun h => hw_notS (Finset.mem_of_mem_erase h))
          have hsum2 : ∑ x ∈ S, G0.degree x = G0.degree u + ∑ x ∈ S.erase u, G0.degree x :=
            (Finset.add_sum_erase S (fun x => G0.degree x) huS).symm
          omega
        have hz_ex : ((G0.neighborFinset u).erase w \ (G0.neighborFinset w).erase u).Nonempty := by
          by_contra hnot
          rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hnot
          have hv_mem_w : v ∈ (G0.neighborFinset w).erase u :=
            Finset.mem_erase.mpr ⟨huv.symm, (G0.mem_neighborFinset w v).mpr
              ((G0.mem_neighborFinset v w).mp hw_nb).symm⟩
          have hv_not_u : v ∉ (G0.neighborFinset u).erase w := fun h =>
            hu_nnb ((G0.mem_neighborFinset v u).mpr ((G0.mem_neighborFinset u v).mp
              (Finset.mem_of_mem_erase h)).symm)
          have hss : (G0.neighborFinset u).erase w ⊂ (G0.neighborFinset w).erase u :=
            Finset.ssubset_iff_of_subset hnot |>.mpr ⟨v, hv_mem_w, hv_not_u⟩
          have hlt := Finset.card_lt_card hss
          by_cases hadj_uw : G0.Adj u w
          · have hu_w : w ∈ G0.neighborFinset u := (G0.mem_neighborFinset u w).mpr hadj_uw
            have hw_u : u ∈ G0.neighborFinset w := (G0.mem_neighborFinset w u).mpr hadj_uw.symm
            rw [Finset.card_erase_of_mem hu_w, Finset.card_erase_of_mem hw_u,
              SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hlt
            have : 1 ≤ G0.degree w := Finset.card_pos.mpr ⟨v, Finset.mem_of_mem_erase hv_mem_w⟩
            omega
          · have hu_w : w ∉ G0.neighborFinset u := fun h => hadj_uw ((G0.mem_neighborFinset u w).mp h)
            have hw_u : u ∉ G0.neighborFinset w := fun h => hadj_uw ((G0.mem_neighborFinset w u).mp h).symm
            rw [Finset.erase_eq_self.mpr hu_w, Finset.erase_eq_self.mpr hw_u,
              SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hlt
            omega
        obtain ⟨z, hz_sdiff⟩ := hz_ex
        have hz_u : z ∈ (G0.neighborFinset u).erase w := (Finset.mem_sdiff.mp hz_sdiff).1
        have hz_not_w : z ∉ (G0.neighborFinset w).erase u := (Finset.mem_sdiff.mp hz_sdiff).2
        have hzw : z ≠ w := (Finset.mem_erase.mp hz_u).1
        have hadj_uz : G0.Adj u z := (G0.mem_neighborFinset u z).mp (Finset.mem_of_mem_erase hz_u)
        have hzu : z ≠ u := (G0.ne_of_adj hadj_uz).symm
        have hzv : z ≠ v := fun h => hu_nnb ((G0.mem_neighborFinset v u).mpr (h ▸ hadj_uz.symm))
        have h_nadj_wz : ¬ G0.Adj w z := fun h =>
          hz_not_w (Finset.mem_erase.mpr ⟨hzu, (G0.mem_neighborFinset w z).mpr h⟩)
        have hadj_vw : G0.Adj v w := (G0.mem_neighborFinset v w).mp hw_nb
        have h_nadj_vu : ¬ G0.Adj v u := fun h => hu_nnb ((G0.mem_neighborFinset v u).mpr h)
        let G' := switchGraph G0 v u w z huv hwv hzw hzu
        obtain ⟨hG'nb_v, hdeg_same, hdegSeq_eq, hmax_eq, hres_G'⟩ :=
          switchGraph_props G0 v u w z huv hwv huw hzw hzu hzv hadj_uz h_nadj_wz hadj_vw h_nadj_vu
        have hsdiff_lt : (S \ G'.neighborFinset v).card = k - 1 := by
          have hsdiff_eq : S \ G'.neighborFinset v = (S \ G0.neighborFinset v).erase u := by
            ext x
            rw [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_sdiff, hG'nb_v,
              Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hxS, hnx⟩
              refine ⟨fun h => hnx (Or.inl h), hxS, fun h => ?_⟩
              by_cases hxw : x = w
              · exact hw_notS (hxw ▸ hxS)
              · exact hnx (Or.inr ⟨hxw, h⟩)
            · rintro ⟨hxne, hxS, hnx⟩
              refine ⟨hxS, ?_⟩
              rintro (rfl | ⟨_, hxnb⟩)
              · exact hxne rfl
              · exact hnx hxnb
          rw [hsdiff_eq, Finset.card_erase_of_mem hu_sdiff, hk_eq]
        have hS_mem' : S ∈ (Finset.univ.erase v).powersetCard (G'.degree v) := by
          rw [Finset.mem_powersetCard, hdeg_same v]
          exact ⟨hS_sub, hS_card⟩
        have hS_opt' : ∀ T ∈ (Finset.univ.erase v).powersetCard (G'.degree v),
            ∑ x ∈ T, G'.degree x ≤ ∑ x ∈ S, G'.degree x := by
          intro T hT
          rw [hdeg_same v] at hT
          rw [Finset.sum_congr rfl fun x _ => hdeg_same x,
            Finset.sum_congr rfl fun x _ => hdeg_same x]
          exact hS_opt T hT
        have hIH_G' := ih_inner (k - 1) (by omega) G' v S (by rw [hdeg_same v, hmax_eq]; exact hv_max)
          (by rw [hdeg_same v]; exact hv_pos) hS_mem' hS_opt' hsdiff_lt
        have hV_G0 : Valid (degSeq G0) := hdegSeq_eq ▸ hIH_G'.1
        have hIH_G'U := (ih_outer (Fintype.card U) hU_lt U (G'.induce U) rfl).1
        have hG'U_rel := switchGraph_induce_residue_le G0 G' v u w huv hwv huw h_nadj_vu hadj_vw
          hw_le_u hG'nb_v hdeg_same hIH_G'U hIH_U
        exact ⟨hV_G0, le_trans (hres_G' ▸ hIH_G'.2) hG'U_rel⟩
    obtain ⟨v0, hv0⟩ := G.exists_maximal_degree_vertex
    have hv0_pos : 1 ≤ G.degree v0 := by rw [← hv0]; exact hmax_pos
    have hnb_mem : G.neighborFinset v0 ∈ (Finset.univ.erase v0).powersetCard (G.degree v0) := by
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => Finset.mem_erase.mpr
        ⟨(G.ne_of_adj ((G.mem_neighborFinset v0 x).mp hx)).symm, Finset.mem_univ x⟩,
        by rw [SimpleGraph.card_neighborFinset_eq_degree]⟩
    have hpow_ne : ((Finset.univ.erase v0).powersetCard (G.degree v0)).Nonempty :=
      ⟨_, hnb_mem⟩
    obtain ⟨S0, hS0_mem, hS0_opt⟩ :=
      Finset.exists_max_image _ (fun T : Finset V => ∑ x ∈ T, G.degree x) hpow_ne
    have hV_G := (h_inner (S0 \ G.neighborFinset v0).card G v0 S0 hv0.symm hv0_pos hS0_mem hS0_opt rfl).1
    refine ⟨hV_G, fun v hv h1 => ?_⟩
    have hnb_mem' : G.neighborFinset v ∈ (Finset.univ.erase v).powersetCard (G.degree v) := by
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => Finset.mem_erase.mpr
        ⟨(G.ne_of_adj ((G.mem_neighborFinset v x).mp hx)).symm, Finset.mem_univ x⟩,
        by rw [SimpleGraph.card_neighborFinset_eq_degree]⟩
    obtain ⟨S, hS_mem, hS_opt⟩ :=
      Finset.exists_max_image _ (fun T : Finset V => ∑ x ∈ T, G.degree x) ⟨_, hnb_mem'⟩
    exact (h_inner (S \ G.neighborFinset v).card G v S hv h1 hS_mem hS_opt rfl).2

end OMA.TxG1

theorem OMA.solution :
    OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H1 := by
  intro V _ _ G _ v hvpos hvle
  haveI : Nonempty V := ⟨v⟩
  obtain ⟨w, hw⟩ := G.exists_maximal_degree_vertex
  have hdeg : G.degree v = G.maxDegree :=
    le_antisymm (G.degree_le_maxDegree v) (hw ▸ hvle w)
  exact ((OMA.TxG1.valid_and_residue_le_delete_max (Fintype.card V) V G rfl).2
    v hdeg (Nat.succ_le_of_lt hvpos))
