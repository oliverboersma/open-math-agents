import FormalConjectures.ErdosProblems.«556»
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The three-colour even-cycle Ramsey number and balanced EC2 colourings

Write n = 2m. In the EC2 configuration of Benevides and Skokan, C and D
each send almost all of their edges to U = A ∪ B in a designated colour.
If either block has enough vertices of degree at least 3|U|/5, Hall's theorem
constructs the desired cycle. A degree count also covers a block of size at
least (1 + 11α/4)m. The two inputs below isolate the other colourings
and the remaining balanced absorption problem.

The sharp lower-bound colouring is from @senamakel's R1 reduction.
-/

open Filter SimpleGraph
open scoped Fin.NatCast

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2

theorem rc4_no_cycle (N m : ℕ) (G : SimpleGraph (Fin N)) (P : Fin N → Prop)
    (hP : ∀ u v, P u → P v → u = v) (L : Fin N → ℕ)
    (hL : ∀ u v, G.Adj u v → ¬ P u → ¬ P v → L u = L v)
    (hc : ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ P v → L v = j →
      (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m)) :
    ¬ cycleGraph (2 * m + 2) ⊑ G := by
  classical
  have : NeZero (2 * m + 2) := ⟨by omega⟩
  rintro ⟨f⟩
  have hinj := f.injective
  -- choose the base index
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (2 * m + 2), ∀ i, P (f i) → i = i0 := by
    by_cases hh : ∃ i, P (f i)
    · obtain ⟨i, hi⟩ := hh
      exact ⟨i, fun j hj => hinj (hP _ _ hj hi)⟩
    · push Not at hh
      exact ⟨0, fun j hj => absurd hj (hh j)⟩
  let idx : ℕ → Fin (2 * m + 2) := fun t => i0 + ((t + 1 : ℕ) : Fin (2 * m + 2))
  have hidx_ne : ∀ t, t < 2 * m + 1 → idx t ≠ i0 := by
    intro t ht h
    have h2 : ((t + 1 : ℕ) : Fin (2 * m + 2)) = 0 := by
      have := congrArg (fun x => x - i0) h
      simpa [idx] using this
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    simp at this
  have hidx_inj : ∀ a b, a < 2 * m + 1 → b < 2 * m + 1 → idx a = idx b → a = b := by
    intro a b ha hb h
    have h2 : ((a + 1 : ℕ) : Fin (2 * m + 2)) = ((b + 1 : ℕ) : Fin (2 * m + 2)) := by
      simpa [idx] using h
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hnP : ∀ t, t < 2 * m + 1 → ¬ P (f (idx t)) := by
    intro t ht h
    exact hidx_ne t ht (hi0 _ h)
  have hadj : ∀ t, G.Adj (f (idx (t + 1))) (f (idx t)) := by
    intro t
    apply f.toHom.map_adj
    rw [cycleGraph_adj]
    left
    simp only [idx]
    push_cast
    abel
  have hlab : ∀ t, t < 2 * m + 1 → L (f (idx t)) = L (f (idx 0)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [← ih (by omega)]
      exact hL _ _ (hadj t) (hnP _ ht) (hnP _ (by omega))
  obtain ⟨a, b, hab⟩ := hc (L (f (idx 0)))
  let S : Finset ℕ := Finset.range (2 * m + 1)
  have hmaps : ∀ t ∈ S, (f (idx t)).val ∈ Finset.Ico a (a + m) ∪ Finset.Ico b (b + m) := by
    intro t ht
    have ht' : t < 2 * m + 1 := Finset.mem_range.mp ht
    rcases hab _ (hnP t ht') (hlab t ht') with h | h
    · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr h)
  have hinjOn : Set.InjOn (fun t => (f (idx t)).val) S := by
    intro x hx y hy hxy
    exact hidx_inj x y (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
      (hinj (Fin.ext hxy))
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinjOn
  have h2 := Finset.card_union_le (Finset.Ico a (a + m)) (Finset.Ico b (b + m))
  simp [S] at h1 h2
  omega


theorem rc4_key_red : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 4 → t ≠ 4 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 0 →
    (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_green : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 5 → t ≠ 5 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 1 →
    (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_blue : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 6 → t ≠ 6 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 2 →
    (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_lower (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN : N ≤ 4 * m + 3)
    (ty : ℕ → ℕ) (hty : ∀ v, ty v = if v < m then 0 else if v < 2 * m then 1 else
      if v < 3 * m then 2 else if v < 4 * m then 3 else v - 4 * m + 4)
    (κ : ℕ → ℕ → ℕ) (hκ : ∀ s t, κ s t = if s = 6 ∨ t = 6 then 2 else
      if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else
      if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) :
    ∃ c : Fin 3 → SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c ∧
      ∀ i, ¬ cycleGraph (2 * m + 2) ⊑ c i := by
  have hκs : ∀ s t, κ s t = κ t s := by
    intro s t; rw [hκ, hκ]; split_ifs <;> omega
  have hκ3 : ∀ s t, κ s t < 3 := by
    intro s t; rw [hκ]; split_ifs <;> omega
  have hty6 : ∀ v : Fin N, ty v.val ≤ 6 := by
    intro v; have := v.isLt; rw [hty]; split_ifs <;> omega
  let c : Fin 3 → SimpleGraph (Fin N) := fun i =>
    SimpleGraph.fromRel (fun u v : Fin N => κ (ty u.val) (ty v.val) = i.val)
  have hcadj : ∀ i u v, (c i).Adj u v ↔ u ≠ v ∧ κ (ty u.val) (ty v.val) = i.val := by
    intro i u v
    simp only [c, fromRel_adj]
    rw [hκs (ty v.val)]
    simp
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · ext u v
    simp only [top_adj, iSup_adj, hcadj]
    constructor
    · intro h; exact ⟨⟨_, hκ3 _ _⟩, h, rfl⟩
    · rintro ⟨_, h, _⟩; exact h
  · intro i j hij
    rw [SimpleGraph.disjoint_left]
    intro u v h1 h2
    rw [hcadj] at h1 h2
    exact hij (Fin.ext (h1.2.symm.trans h2.2))
  · have hP : ∀ k : ℕ, 4 ≤ k → k ≤ 6 → ∀ u v : Fin N, ty u.val = k → ty v.val = k → u = v := by
      intro k _ _ u v hu hv
      apply Fin.ext
      rw [hty] at hu hv
      split_ifs at hu hv <;> omega
    have hcl : ∀ (f : ℕ → ℕ) (A0 B0 A1 B1 : ℕ) (k : ℕ), 4 ≤ k → k ≤ 6 →
        (∀ s, s < 4 → f s ≤ 1) → (∀ s, 4 ≤ s → f s = s + 10) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 0 →
          (A0 ≤ v.val ∧ v.val < A0 + m) ∨ (B0 ≤ v.val ∧ v.val < B0 + m)) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 1 →
          (A1 ≤ v.val ∧ v.val < A1 + m) ∨ (B1 ≤ v.val ∧ v.val < B1 + m)) →
        ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ ty v.val = k → f (ty v.val) = j →
          (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m) := by
      intro f A0 B0 A1 B1 k _ _ hf1 hf2 h0 h1 j
      by_cases hj0 : j = 0
      · refine ⟨A0, B0, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h0 v hlt (hv.trans hj0)
      by_cases hj1 : j = 1
      · refine ⟨A1, B1, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h1 v hlt (hv.trans hj1)
      refine ⟨4 * m + j - 14, 4 * m + j - 14, fun v _ hv => ?_⟩
      have hge : 4 ≤ ty v.val := by
        by_contra hc; have := hf1 (ty v.val) (by omega); omega
      rw [hf2 _ hge] at hv
      left
      have hv' := hv
      rw [hty] at hv'
      have := v.isLt
      split_ifs at hv' <;> omega
    have hint : ∀ v : Fin N, (ty v.val = 0 → v.val < m) ∧ (ty v.val = 1 → m ≤ v.val ∧ v.val < 2 * m) ∧
        (ty v.val = 2 → 2 * m ≤ v.val ∧ v.val < 3 * m) ∧ (ty v.val = 3 → 3 * m ≤ v.val ∧ v.val < 4 * m) := by
      intro v; refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have e := hty v.val <;> split_ifs at e <;> omega
    intro i
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · -- red, hub r
      refine rc4_no_cycle N m (c 0) (fun v => ty v.val = 4) (fun u v hu hv => hP 4 le_rfl
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_red
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) 0 m (2 * m) (3 * m)
          4 le_rfl (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- green, hub g
      refine rc4_no_cycle N m (c 1) (fun v => ty v.val = 5) (fun u v hu hv => hP 5 (by norm_num)
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_green
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) 0 (3 * m) m
          (2 * m) 5 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- blue, hub b
      refine rc4_no_cycle N m (c 2) (fun v => ty v.val = 6) (fun u v hu hv => hP 6 (by norm_num)
        le_rfl u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_blue
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) 0 (2 * m) m
          (3 * m) 6 (by norm_num) le_rfl ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega

open Finset

theorem ec2_common_with_exceptions {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U C : Finset V) (m : ℕ) (α : ℝ)
    (hm : 0 < m) (hα : 0 ≤ α) (hα' : α ≤ 1 / 1000)
    (hU : 2 * (1 - α) * (m : ℝ) ≤ (U.card : ℝ))
    (hC : (1 + 11 / 4 * α) * (m : ℝ) ≤ (C.card : ℝ) ∨
      m ≤ (C.filter (fun x => 3 * U.card ≤ 5 * (U.filter (G.Adj x)).card)).card)
    (hC' : (C.card : ℝ) ≤ 4 * (m : ℝ))
    (hd : (1 - α) * (C.card : ℝ) * (U.card : ℝ) ≤
      ∑ x ∈ C, ((U.filter (G.Adj x)).card : ℝ)) :
    ∃ S ⊆ C, S.card = m ∧ ∃ P ⊆ S,
      (∀ x ∈ S, ∀ y ∈ S, 2 * P.card ≤ (U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ∉ P → y ∉ P → m ≤ (U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card) := by
  classical
  let nbr (x : V) := U.filter (G.Adj x)
  let miss (x : V) : ℝ := U.card - ((nbr x).card : ℝ)
  have hmiss (x : V) : 0 ≤ miss x := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
  have htot : ∑ x ∈ C, miss x ≤ α * (C.card : ℝ) * (U.card : ℝ) := by
    simp only [miss, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change (1 - α) * (C.card : ℝ) * (U.card : ℝ) ≤ ∑ x ∈ C, ((nbr x).card : ℝ) at hd
    linarith only [hd]
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hαm := mul_le_mul_of_nonneg_right hα' hmpos.le
  have hUpos : 0 < (U.card : ℝ) := by linarith only [hU, hαm, hmpos]
  have hmark (t : ℝ) (A : Finset V) (hA : A ⊆ C)
      (hcut : ∀ x ∈ A, t * (U.card : ℝ) ≤ 5 * miss x) :
      t * (A.card : ℝ) ≤ 5 * α * (C.card : ℝ) := by
    have hsum : ∑ x ∈ A, miss x ≤ ∑ x ∈ C, miss x :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun x _ _ => hmiss x)
    have hlow : (A.card : ℝ) * (t * (U.card : ℝ)) ≤ 5 * (∑ x ∈ A, miss x) := by
      calc (A.card : ℝ) * (t * (U.card : ℝ)) = ∑ _x ∈ A, (t * (U.card : ℝ)) := by
             simp [Finset.sum_const, nsmul_eq_mul]
           _ ≤ ∑ x ∈ A, 5 * miss x := Finset.sum_le_sum hcut
           _ = _ := (Finset.mul_sum ..).symm
    apply (mul_le_mul_iff_left₀ hUpos).mp
    linarith only [hlow, hsum, htot]
  let B := C.filter fun x => 2 * (U.card : ℝ) < 5 * miss x
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hgood : m ≤ (C \ B).card := by
    rcases hC with hC | hC
    · have hbad := hmark 2 B hBC (fun x hx => (Finset.mem_filter.mp hx).2.le)
      have hprod : 1 ≤ (1 - 5 / 2 * α) * (1 + 11 / 4 * α) := by
        nlinarith only [mul_nonneg hα (show 0 ≤ 1 / 4 - 55 / 8 * α by linarith only [hα'])]
      have hmore : (m : ℝ) ≤ (1 - 5 / 2 * α) * (C.card : ℝ) := by
        calc (m : ℝ) ≤ ((1 - 5 / 2 * α) * (1 + 11 / 4 * α)) * m := by
               simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod hmpos.le
             _ = (1 - 5 / 2 * α) * ((1 + 11 / 4 * α) * m) := mul_assoc _ _ _
             _ ≤ _ := mul_le_mul_of_nonneg_left hC (by linarith only [hα'])
      have hcard : (C \ B).card + B.card = C.card := Finset.card_sdiff_add_card_eq_card hBC
      have hcardR : ((C \ B).card : ℝ) + (B.card : ℝ) = C.card := by exact_mod_cast hcard
      exact_mod_cast (show (m : ℝ) ≤ ((C \ B).card : ℝ) by linarith only [hmore, hcardR, hbad])
    · apply hC.trans
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxC, hxdeg⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_sdiff.mpr
      refine ⟨hxC, ?_⟩
      intro hxB
      have hxmiss := (Finset.mem_filter.mp hxB).2
      have hxdegR : 3 * (U.card : ℝ) ≤ 5 * ((nbr x).card : ℝ) := by
        exact_mod_cast hxdeg
      change 2 * (U.card : ℝ) < 5 * ((U.card : ℝ) - ((nbr x).card : ℝ)) at hxmiss
      linarith only [hxdegR, hxmiss]
  obtain ⟨S, hS, hSm⟩ := Finset.exists_subset_card_eq hgood
  have hSC : S ⊆ C := fun x hx => (Finset.mem_sdiff.mp (hS hx)).1
  let P := S.filter fun x => (U.card : ℝ) < 5 * miss x
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hpoor := hmark 1 P (hPS.trans hSC) (by
    intro x hx
    rw [one_mul]
    exact (Finset.mem_filter.mp hx).2.le)
  have hαC' := mul_le_mul_of_nonneg_right hα' (Nat.cast_nonneg (α := ℝ) C.card)
  have hpU : 10 * (P.card : ℝ) ≤ U.card := by
    linarith only [hpoor, hαC', hC', hU, hαm, hmpos]
  have htyp {x : V} (hx : x ∈ S) : 5 * miss x ≤ 2 * (U.card : ℝ) := by
    obtain ⟨hxC, hxB⟩ := Finset.mem_sdiff.mp (hS hx)
    exact le_of_not_gt fun hb => hxB (Finset.mem_filter.mpr ⟨hxC, hb⟩)
  have hhigh {x : V} (hx : x ∈ S) (hxp : x ∉ P) : 5 * miss x ≤ U.card := by
    exact le_of_not_gt fun hb => hxp (Finset.mem_filter.mpr ⟨hx, hb⟩)
  have hcodeg (x y : V) :
      (U.card : ℝ) - miss x - miss y ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) := by
    have hu : (nbr x ∪ nbr y) ⊆ U :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hi := Finset.card_union_add_card_inter (nbr x) (nbr y)
    have hib : (nbr x).card + (nbr y).card ≤ U.card + (nbr x ∩ nbr y).card := by
      rw [← hi]
      exact Nat.add_le_add_right (Finset.card_le_card hu) _
    have heq : nbr x ∩ nbr y = U.filter (fun z => G.Adj x z ∧ G.Adj y z) := by
      ext z
      simp [nbr, and_assoc, and_left_comm, and_comm]
    rw [heq] at hib
    have hr : ((nbr x).card : ℝ) + ((nbr y).card : ℝ) ≤ U.card +
        ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) := by exact_mod_cast hib
    dsimp only [miss]
    linarith only [hr]
  refine ⟨S, hSC, hSm, P, hPS, ?_, ?_⟩
  · intro x hx y hy
    exact_mod_cast (show 2 * (P.card : ℝ) ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) by
      linarith only [hcodeg x y, htyp hx, htyp hy, hpU])
  · intro x hx y hy hxp hyp
    exact_mod_cast (show (m : ℝ) ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) by
      linarith only [hcodeg x y, hhigh hx hxp, hhigh hy hyp, hU, hαm, hmpos])

open SimpleGraph

theorem cycle_rotate_val {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    (finRotate m i).val = (i.val + 1) % m := by
  haveI : NeZero m := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]

theorem cycle_of_alternating_representatives {V : Type*} (G : SimpleGraph V)
    {m : ℕ} (hm : 2 ≤ m) (U : Finset V) (x y : Fin m → V)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxu : ∀ i, x i ∉ U)
    (hmem : ∀ i, y i ∈ U ∧ G.Adj (x i) (y i) ∧ G.Adj (x (finRotate m i)) (y i)) :
    (cycleGraph (2 * m)).IsContained G := by
  have hxy (i j : Fin m) : x i ≠ y j := fun h => hxu i (by simpa only [h] using (hmem j).1)
  let half (a : Fin (2 * m)) : Fin m := ⟨a.val / 2, by have := a.isLt; omega⟩
  let f (a : Fin (2 * m)) := if a.val % 2 = 0 then x (half a) else y (half a)
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0
    · have he := congrArg Fin.val (hx (by simpa [f, ha, hb] using hab : x (half a) = x (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab : x (half a) = y (half b))).elim
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab.symm : x (half b) = y (half a))).elim
    · have he := congrArg Fin.val (hy (by simpa [f, ha, hb] using hab : y (half a) = y (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
  have step (a b : Fin (2 * m)) (hz : (b - a).val = 1) : G.Adj (f a) (f b) := by
    have hsize := a.isLt
    have hbsize := b.isLt
    rw [Fin.coe_sub] at hz
    have hab : b.val = a.val + 1 ∨ (a.val + 1 = 2 * m ∧ b.val = 0) := by
      by_cases hle : a.val ≤ b.val
      · rw [show 2 * m - a.val + b.val = 2 * m + (b.val - a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inr (by omega)
    rcases hab with h | ⟨haLast, hbZero⟩
    · by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 ≠ 0 := by omega
        have he : half a = half b := Fin.ext (by dsimp [half]; omega)
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.1
      · have hb : b.val % 2 = 0 := by omega
        have he : finRotate m (half a) = half b := by
          apply Fin.ext
          rw [cycle_rotate_val hm]
          dsimp [half]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
    · have ha : a.val % 2 ≠ 0 := by omega
      have he : finRotate m (half a) = half b := by
        apply Fin.ext
        rw [cycle_rotate_val hm]
        dsimp [half]
        simp [show a.val / 2 + 1 = m by omega, hbZero]
      have hb : b.val % 2 = 0 := by omega
      simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
  let hom : cycleGraph (2 * m) →g G := ⟨f, by
    intro a b hab
    rcases cycleGraph_adj'.mp hab with h | h
    · exact (step b a h).symm
    · exact step a b h⟩
  exact ⟨⟨hom, hinj⟩⟩

theorem hall_cycle_with_exceptions {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℕ} (hm : 2 ≤ m) (U S P : Finset V) (hSU : Disjoint S U)
    (hs : S.card = m)
    (hmin : ∀ a ∈ S, ∀ b ∈ S, 2 * P.card ≤ (U.filter fun z => G.Adj a z ∧ G.Adj b z).card)
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a ∉ P → b ∉ P → m ≤ (U.filter fun z => G.Adj a z ∧ G.Adj b z).card) :
    (cycleGraph (2 * m)).IsContained G := by
  classical
  let e : S ≃ Fin m := Finset.equivFinOfCardEq hs
  let x (i : Fin m) : V := (e.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have hxS (i : Fin m) : x i ∈ S := (e.symm i).property
  let t (i : Fin m) := U.filter fun z => G.Adj (x i) z ∧ G.Adj (x (finRotate m i)) z
  let bad (g : Fin m → V) := Finset.univ.filter fun i => g i ∈ P
  have bad_card (g : Fin m → V) (hg : Function.Injective g) : (bad g).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact hg.injOn
  have hHall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    have sub (j : Fin m) (hj : j ∈ s) : (t j).card ≤ (s.biUnion t).card :=
      Finset.card_le_card (fun v hv => Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
    by_cases hh : ∃ j ∈ s, x j ∉ P ∧ x (finRotate m j) ∉ P
    · obtain ⟨j, hj, hj₁, hj₂⟩ := hh
      have hs' : s.card ≤ m := by simpa using Finset.card_le_univ s
      exact hs'.trans ((hgood _ (hxS j) _ (hxS (finRotate m j)) hj₁ hj₂).trans (sub j hj))
    · have hsub : s ⊆ bad x ∪ bad (x ∘ finRotate m) := by
        intro j hj
        by_cases hp : x j ∈ P
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
        · have hnext : x (finRotate m j) ∈ P := by
            by_contra hn
            exact hh ⟨j, hj, hp, hn⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩)
      have hab := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h₁ := bad_card x hx
      have h₂ := bad_card (x ∘ finRotate m) (hx.comp (finRotate m).injective)
      have hs' : s.card ≤ 2 * P.card := by omega
      exact hs'.trans ((hmin _ (hxS i) _ (hxS (finRotate m i))).trans (sub i hi))
  obtain ⟨y, hy, hyt⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  apply cycle_of_alternating_representatives G hm U x y hx hy
  · exact fun i => Finset.disjoint_left.mp hSU (hxS i)
  · exact fun i => Finset.mem_filter.mp (hyt i)

theorem cycle_from_dense_block {m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (U C : Finset (Fin (4 * m))) (hCU : Disjoint C U) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1/1000)
    (hU : 2*(1-α)*(m : ℝ) ≤ U.card)
    (hC : (1+11/4*α)*(m : ℝ) ≤ C.card ∨
      m ≤ (C.filter (fun x => 3*U.card ≤ 5*(U.filter (G.Adj x)).card)).card)
    (hd : (1-α)*(C.card : ℝ)*U.card ≤ ∑ x ∈ C, ((U.filter (G.Adj x)).card : ℝ)) :
    cycleGraph (2*m) ⊑ G := by
  have hupp : C.card ≤ 4*m := by simpa using Finset.card_le_univ C
  obtain ⟨S,hSC,hs,P,_,hmin,hgood⟩ := ec2_common_with_exceptions G U C m α
    (by omega) hα.le hα' hU hC (by exact_mod_cast hupp) hd
  exact hall_cycle_with_exceptions G hm U S P (hCU.mono_left hSC) hs hmin hgood

theorem eq_from_upper (m : ℕ) (hm : 2 ≤ m) (up : ∀ c : Fin 3 → SimpleGraph (Fin (4*m)),
    (⊤ : SimpleGraph (Fin (4*m))).IsEdgeColouring c → ∃ i, cycleGraph (2*m) ⊑ c i) :
    multicolourRamsey (cycleGraph (2*m)) 3 = 4*m := by
  unfold multicolourRamsey
  apply le_antisymm
  · exact Nat.sInf_le up
  refine le_csInf ⟨4*m,up⟩ ?_
  intro N hN
  by_contra h
  obtain ⟨c,hc,hno⟩ := rc4_lower (m-1) (by omega) N (by omega)
    (fun v => if v < m-1 then 0 else if v < 2*(m-1) then 1 else
      if v < 3*(m-1) then 2 else if v < 4*(m-1) then 3 else v-4*(m-1)+4)
    (fun _ => rfl)
    (fun s t => if s=6 ∨ t=6 then 2 else if s=5 ∨ t=5 then 1 else
      if s=4 ∨ t=4 then 0 else if s/2=t/2 then 0 else if s+t=3 then 1 else 2)
    (fun _ _ => rfl)
  obtain ⟨i,hi⟩ := hN c hc
  have hlen : 2*m = 2*(m-1)+2 := by omega
  rw [hlen] at hi
  exact hno i hi

/-- Outside EC2 the embeddings in EC1 and EC3 together with the stability theorem
give a monochromatic cycle. Inside EC2 we retain a partition and its colour permutation. -/
def H1 : Prop := ∀ α : ℝ, 0 < α → ∀ᶠ m : ℕ in atTop,
  ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
    (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
    (∃ i, cycleGraph (2 * m) ⊑ c i) ∨
    ∃ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)),
    let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
    let U := W 0 ∪ W 1
    let dense := fun (i : Fin 3) (X Y : Finset (Fin (4 * m))) =>
      (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
    (∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
    dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U

/-- The remaining EC2 absorption problem. In each of C and D there are fewer than
m vertices with at least three fifths of U as neighbours in the designated colour.
Both blocks also have fewer than (1 + 11α/4)m vertices. -/
def H2 : Prop := ∃ α : ℝ, 0 < α ∧ α ≤ 1/1000 ∧ ∀ᶠ m : ℕ in atTop,
  ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
    (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
    ∀ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)),
    let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
    let U := W 0 ∪ W 1
    let dense := fun (i : Fin 3) (X Y : Finset (Fin (4 * m))) =>
      (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
    let narrow := fun (i : Fin 3) (j : Fin 4) =>
      ((W j).card : ℝ) < (1 + 11/4 * α) * m ∧
      ((W j).filter (fun x => 3 * U.card ≤ 5 * (U.filter ((c (σ i)).Adj x)).card)).card < m
    ((∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
    dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U) → narrow 1 2 → narrow 2 3 → ∃ i, cycleGraph (2 * m) ⊑ c i

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  classical
  intro h1 h2
  obtain ⟨α,ha,ha',hclose⟩ := h2
  have evenBound : ∀ᶠ m : ℕ in atTop, multicolourRamsey (cycleGraph (2*m)) 3 = 4*m := by
    filter_upwards [h1 α ha,hclose,eventually_ge_atTop 2] with m hclass hcore hm
    apply eq_from_upper m hm
    intro c hc
    letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
    rcases hclass c hc with done | ⟨f,σ,hparts⟩
    · exact done
    let W (j : Fin 4) := Finset.univ.filter (fun v : Fin (4*m) => f v = j)
    let U := W 0 ∪ W 1
    let dense (i : Fin 3) (X Y : Finset (Fin (4*m))) : Prop :=
      (1-α)*(X.card : ℝ)*Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
    change (∀ j, (1-α)*(m : ℝ) ≤ (W j).card) ∧ dense 0 (W 0) (W 1) ∧
      dense 1 (W 2) U ∧ dense 2 (W 3) U at hparts
    have blocksDisjoint {j k : Fin 4} (hjk : j ≠ k) : Disjoint (W j) (W k) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      exact hjk ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)
    have h01 : Disjoint (W 0) (W 1) := blocksDisjoint (by decide)
    have hU : 2*(1-α)*(m : ℝ) ≤ U.card := by
      dsimp only [U]
      rw [Finset.card_union_of_disjoint h01, Nat.cast_add]
      linarith [hparts.1 0,hparts.1 1]
    by_contra hno
    have thin (i : Fin 3) (j : Fin 4) (h0 : j ≠ 0) (h1 : j ≠ 1) (hd : dense i (W j) U) :
        ((W j).card : ℝ) < (1+11/4*α)*m ∧
        ((W j).filter (fun x => 3*U.card ≤ 5*(U.filter ((c (σ i)).Adj x)).card)).card < m := by
      by_contra hn
      have halt : (1+11/4*α)*(m : ℝ) ≤ (W j).card ∨
          m ≤ ((W j).filter (fun x => 3*U.card ≤ 5*(U.filter ((c (σ i)).Adj x)).card)).card := by
        by_cases h : (1+11/4*α)*(m : ℝ) ≤ (W j).card
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt (fun hg => hn ⟨lt_of_not_ge h,hg⟩))
      have hju : Disjoint (W j) U := Finset.disjoint_union_right.mpr ⟨blocksDisjoint h0,blocksDisjoint h1⟩
      exact hno ⟨σ i, cycle_from_dense_block hm (c (σ i)) U (W j) hju ha ha' hU halt hd⟩
    exact hno (hcore c hc f σ hparts
      (thin 1 2 (by decide) (by decide) hparts.2.2.1)
      (thin 2 3 (by decide) (by decide) hparts.2.2.2))
  obtain ⟨M,hM⟩ := eventually_atTop.mp evenBound
  filter_upwards [eventually_ge_atTop (2*M)] with n hn he
  obtain ⟨m, rfl⟩ := he
  have hlen : m+m = 2*m := by omega
  rw [hlen, show 2*(2*m)=4*m by omega]
  exact hM m (by omega)

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2
