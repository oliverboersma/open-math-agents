import FormalConjectures.ErdosProblems.«480»
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Chung-Graham Sharp Bound for Erdos Problem 480

Proof of Theorem 1 of Chung and Graham (1984), establishing the reciprocal-Fibonacci
upper bound for the clustering functional on sequences in the unit interval.
-/

namespace Erdos480CGAux

open Filter
open scoped Topology List

noncomputable def jumpWeight : List ℕ → ℝ
  | a :: b :: l => 1 / (Nat.dist a b : ℝ) + jumpWeight (b :: l)
  | _ => 0

lemma jumpWeight_nonneg : ∀ l : List ℕ, 0 ≤ jumpWeight l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => add_nonneg (by positivity) (jumpWeight_nonneg (b :: l))

lemma jumpWeight_append_pair : ∀ (l : List ℕ) (a b : ℕ),
    jumpWeight (l ++ [a, b]) = jumpWeight (l ++ [a]) + 1 / (Nat.dist a b : ℝ)
  | [], a, b => by simp [jumpWeight]
  | [x], a, b => by simp [jumpWeight]
  | x :: y :: t, a, b => by
    have ih := jumpWeight_append_pair (y :: t) a b
    simp only [List.cons_append] at ih ⊢
    simp only [jumpWeight, ih]
    ring

lemma jumpWeight_reverse : ∀ l : List ℕ, jumpWeight l.reverse = jumpWeight l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have ih := jumpWeight_reverse (b :: t)
    have hrev : (a :: b :: t).reverse = t.reverse ++ [b, a] := by
      simp [List.reverse_cons, List.append_assoc]
    have hrev1 : (b :: t).reverse = t.reverse ++ [b] := by
      simp [List.reverse_cons]
    rw [hrev, jumpWeight_append_pair, ← hrev1, ih, jumpWeight, Nat.dist_comm a b, add_comm]

lemma jumpWeight_shift_add : ∀ (s : List ℕ) (lo : ℕ),
    jumpWeight (s.map (· + lo)) = jumpWeight s
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, lo => by
    have ih := jumpWeight_shift_add (b :: t) lo
    simp only [List.map_cons] at ih ⊢
    have hd : Nat.dist (a + lo) (b + lo) = Nat.dist a b := by
      simp only [Nat.dist]
      omega
    simp only [jumpWeight, ih, hd]

lemma nat_dist_comp (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) :
    Nat.dist (m + 1 - a) (m + 1 - b) = Nat.dist a b := by
  simp only [Nat.dist]
  omega

lemma jumpWeight_comp (m : ℕ) : ∀ (s : List ℕ),
    (∀ v ∈ s, 1 ≤ v ∧ v ≤ m) →
      jumpWeight (s.map (fun v => m + 1 - v)) = jumpWeight s
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, hmem => by
    have ha : a ≤ m := (hmem a (by simp)).2
    have hb : b ≤ m := (hmem b (by simp)).2
    have htail : ∀ v ∈ b :: t, 1 ≤ v ∧ v ≤ m := fun v hv => hmem v (by simp [hv])
    have ih := jumpWeight_comp m (b :: t) htail
    simp only [List.map_cons] at ih ⊢
    simp only [jumpWeight, ih, nat_dist_comp m a b ha hb]

lemma jumpWeight_cons_two_ge (x y : ℕ) : ∀ (s : List ℕ), s ≠ [] →
    1 / (Nat.dist x y : ℝ) + jumpWeight s ≤ jumpWeight (x :: y :: s)
  | [], hs => absurd rfl hs
  | z :: t, _ => by
    simp only [jumpWeight]
    have h0 : (0 : ℝ) ≤ 1 / (Nat.dist y z : ℝ) := by positivity
    linarith

lemma jumpWeight_snoc_ge : ∀ (s : List ℕ) (y : ℕ), s ≠ [] →
    jumpWeight s ≤ jumpWeight (s ++ [y])
  | [], _, hs => absurd rfl hs
  | [a], y, _ => by
    simp only [List.cons_append, List.nil_append, jumpWeight]
    positivity
  | a :: b :: t, y, _ => by
    have ih := jumpWeight_snoc_ge (b :: t) y (by simp)
    simp only [List.cons_append] at ih ⊢
    simp only [jumpWeight]
    linarith

lemma jumpWeight_snoc_two_ge (s : List ℕ) (y x : ℕ) (hs : s ≠ []) :
    jumpWeight s + 1 / (Nat.dist y x : ℝ) ≤ jumpWeight (s ++ [y, x]) := by
  have h1 := jumpWeight_snoc_ge s y hs
  have h2 := jumpWeight_append_pair s y x
  linarith

def IsPerm1To (m : ℕ) (l : List ℕ) : Prop :=
  l.Nodup ∧ l.length = m ∧ ∀ v ∈ l, 1 ≤ v ∧ v ≤ m

lemma IsPerm1To.ne_nil {m : ℕ} {l : List ℕ} (hl : IsPerm1To m l) (hm : 1 ≤ m) : l ≠ [] := by
  intro h
  have := hl.2.1
  simp [h] at this
  omega

lemma IsPerm1To.reverse {m : ℕ} {l : List ℕ} (hl : IsPerm1To m l) :
    IsPerm1To m l.reverse :=
  ⟨List.nodup_reverse.mpr hl.1, by simp [hl.2.1], fun v hv => hl.2.2 v (List.mem_reverse.mp hv)⟩

lemma IsPerm1To.comp {m : ℕ} {l : List ℕ} (hl : IsPerm1To m l) :
    IsPerm1To m (l.map (fun v => m + 1 - v)) := by
  refine ⟨?_, by simp [hl.2.1], ?_⟩
  · refine hl.1.map_on ?_
    intro a ha b hb heq
    have ha' := hl.2.2 a ha
    have hb' := hl.2.2 b hb
    omega
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have hv' := hl.2.2 v hv
    omega

lemma IsPerm1To.toFinset_eq {m : ℕ} {l : List ℕ} (hl : IsPerm1To m l) :
    l.toFinset = Finset.Icc 1 m := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    exact Finset.mem_Icc.mpr (hl.2.2 v (List.mem_toFinset.mp hv))
  · rw [List.toFinset_card_of_nodup hl.1, hl.2.1, Nat.card_Icc]
    omega

lemma IsPerm1To.mem_of_bounds {m : ℕ} {l : List ℕ} (hl : IsPerm1To m l)
    {v : ℕ} (h1 : 1 ≤ v) (h2 : v ≤ m) : v ∈ l := by
  rw [← List.mem_toFinset, hl.toFinset_eq]
  exact Finset.mem_Icc.mpr ⟨h1, h2⟩

def blockFilter (lo k : ℕ) (l : List ℕ) : List ℕ :=
  l.filter (fun v => decide (lo + 1 ≤ v ∧ v ≤ lo + k))

lemma blockFilter_props {m lo k : ℕ} {l : List ℕ} (hl : IsPerm1To m l) (hbound : lo + k ≤ m) :
    let lB := blockFilter lo k l
    lB <+ l ∧ lB.Nodup ∧ lB.length = k ∧
      (∀ v ∈ lB, lo + 1 ≤ v ∧ v ≤ lo + k) ∧
      IsPerm1To k (lB.map (· - lo)) := by
  intro lB
  have hsub : lB <+ l := List.filter_sublist
  have hnodup : lB.Nodup := hl.1.sublist hsub
  have hmemB : ∀ v ∈ lB, lo + 1 ≤ v ∧ v ≤ lo + k := by
    intro v hv
    simpa [lB, blockFilter] using (List.mem_filter.mp hv).2
  have hfin : lB.toFinset = Finset.Icc (lo + 1) (lo + k) := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_Icc, lB, blockFilter, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨hl.mem_of_bounds (by omega) (by omega), hv⟩
  have hlen : lB.length = k := by
    rw [← List.toFinset_card_of_nodup hnodup, hfin, Nat.card_Icc]
    omega
  refine ⟨hsub, hnodup, hlen, hmemB, ?_, by simp [hlen], ?_⟩
  · refine hnodup.map_on ?_
    intro a ha b hb heq
    have ha' := hmemB a ha
    have hb' := hmemB b hb
    omega
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have hv' := hmemB v hv
    omega

lemma map_sub_map_add_eq {lo : ℕ} :
    ∀ {lB : List ℕ}, (∀ v ∈ lB, lo ≤ v) → (lB.map (· - lo)).map (· + lo) = lB
  | [], _ => rfl
  | v :: t, h => by
    have hv : v - lo + lo = v := Nat.sub_add_cancel (h v (by simp))
    have ih := map_sub_map_add_eq (lo := lo) (lB := t) (fun u hu => h u (by simp [hu]))
    simp only [List.map_cons, hv, ih]

lemma lift_sublist_shift {lo k : ℕ} {lB s' : List ℕ}
    (hmemB : ∀ v ∈ lB, lo + 1 ≤ v ∧ v ≤ lo + k)
    (hs'_ne : s' ≠ []) (hs'_sub : s' <+ lB.map (· - lo)) :
    ∃ s : List ℕ, s ≠ [] ∧ s <+ lB ∧ jumpWeight s = jumpWeight s' := by
  refine ⟨s'.map (· + lo), by simp [hs'_ne], ?_, jumpWeight_shift_add s' lo⟩
  have h1 : s'.map (· + lo) <+ (lB.map (· - lo)).map (· + lo) := hs'_sub.map (· + lo)
  rwa [map_sub_map_add_eq (fun v hv => by have := (hmemB v hv).1; omega)] at h1

lemma getLast_append_singleton : ∀ (xs : List ℕ) (b : ℕ) (h : xs ++ [b] ≠ []),
    (xs ++ [b]).getLast h = b
  | [], _, _ => rfl
  | x :: xs, b, _ => by
    have hne : xs ++ [b] ≠ [] := by simp
    simp only [List.cons_append, List.getLast_cons hne]
    exact getLast_append_singleton xs b hne

lemma list_snoc : ∀ (l : List ℕ) (hl : l ≠ []),
    ∃ init : List ℕ, l = init ++ [l.getLast hl]
  | [], hl => absurd rfl hl
  | [a], _ => ⟨[], rfl⟩
  | a :: b :: t, _ => by
    have hbt : b :: t ≠ [] := by simp
    obtain ⟨init, hinit⟩ := list_snoc (b :: t) hbt
    refine ⟨a :: init, ?_⟩
    simp only [List.getLast_cons hbt, List.cons_append]
    exact congrArg (a :: ·) hinit

lemma list_eq_head_mid_last {l : List ℕ} (hl : l ≠ []) (hlen : 2 ≤ l.length) :
    ∃ mid : List ℕ, l = l.head hl :: mid ++ [l.getLast hl] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a rest =>
    have hrest : rest ≠ [] := by
      intro hr
      simp [hr] at hlen
    obtain ⟨mid, hmid⟩ := list_snoc rest hrest
    refine ⟨mid, ?_⟩
    simp only [List.head_cons, List.getLast_cons hrest, List.cons_append]
    exact congrArg (a :: ·) hmid

lemma head_ne_getLast_of_nodup {l : List ℕ} (hl : l ≠ []) (hnodup : l.Nodup) (hlen : 2 ≤ l.length) :
    l.head hl ≠ l.getLast hl := by
  obtain ⟨mid, hmid⟩ := list_eq_head_mid_last hl hlen
  intro heq
  have hnodup' : (l.head hl :: (mid ++ [l.getLast hl])).Nodup := by
    have h1 : (l.head hl :: mid ++ [l.getLast hl]).Nodup := by rwa [← hmid]
    simpa only [List.cons_append] using h1
  have hnotmem : l.head hl ∉ mid ++ [l.getLast hl] := (List.nodup_cons.mp hnodup').1
  exact hnotmem (by simp [heq])

lemma prepend_before_block {x : ℕ} {tail lB s : List ℕ}
    (hlB_sub : lB <+ tail) (hlB_ne : lB ≠ []) (hs_sub : s <+ lB) (hs_ne : s ≠ []) :
    ∃ t : List ℕ, ∃ ht : t ≠ [],
      t <+ x :: tail ∧ t.head ht = x ∧
      1 / (Nat.dist x (lB.head hlB_ne) : ℝ) + jumpWeight s ≤ jumpWeight t := by
  cases lB with
  | nil => exact absurd rfl hlB_ne
  | cons y tailB =>
    simp only [List.head_cons]
    rcases List.sublist_cons_iff.mp hs_sub with hs_tail | ⟨s_rest, rfl, hs_rest⟩
    · refine ⟨x :: y :: s, by simp, ?_, rfl, jumpWeight_cons_two_ge x y s hs_ne⟩
      exact List.Sublist.cons_cons x ((List.Sublist.cons_cons y hs_tail).trans hlB_sub)
    · refine ⟨x :: y :: s_rest, by simp, ?_, rfl, by simp [jumpWeight]⟩
      exact List.Sublist.cons_cons x ((List.Sublist.cons_cons y hs_rest).trans hlB_sub)

lemma surround_around_block {x x' : ℕ} {mid lB s : List ℕ}
    (hlB_sub : lB <+ mid) (hlB_ne : lB ≠ []) (hs_sub : s <+ lB) (hs_ne : s ≠ []) :
    ∃ t : List ℕ, t ≠ [] ∧ t <+ x :: mid ++ [x'] ∧
      1 / (Nat.dist x (lB.head hlB_ne) : ℝ) +
        1 / (Nat.dist x' (lB.getLast hlB_ne) : ℝ) + jumpWeight s ≤ jumpWeight t := by
  obtain ⟨initB, hinitB⟩ := list_snoc lB hlB_ne
  set y := lB.head hlB_ne
  set y' := lB.getLast hlB_ne
  have hs_app : s <+ initB ++ [y'] := hinitB ▸ hs_sub
  have hright : ∃ s₁ : List ℕ, s₁ ≠ [] ∧ s₁ <+ lB ++ [x'] ∧
      jumpWeight s + 1 / (Nat.dist y' x' : ℝ) ≤ jumpWeight s₁ := by
    obtain ⟨sL, sR, rfl, hsL, hsR⟩ := List.sublist_append_iff.mp hs_app
    rcases List.sublist_cons_iff.mp hsR with hsR_nil | ⟨r_rest, rfl, hr_nil⟩
    · have rfl_sR : sR = [] := List.sublist_nil.mp hsR_nil
      subst rfl_sR
      simp only [List.append_nil] at hs_ne ⊢
      refine ⟨sL ++ [y', x'], by simp [hs_ne], ?_, jumpWeight_snoc_two_ge sL y' x' hs_ne⟩
      rw [hinitB, List.append_assoc]
      exact hsL.append (List.Sublist.refl [y', x'])
    · have rfl_rest : r_rest = [] := List.sublist_nil.mp hr_nil
      subst rfl_rest
      refine ⟨sL ++ [y', x'], by simp, ?_, by rw [jumpWeight_append_pair]⟩
      rw [hinitB, List.append_assoc]
      exact hsL.append (List.Sublist.refl [y', x'])
  obtain ⟨s₁, hs₁_ne, hs₁_sub, hs₁_w⟩ := hright
  have hlBx_ne : lB ++ [x'] ≠ [] := by simp [hlB_ne]
  have hlBx_sub : lB ++ [x'] <+ mid ++ [x'] := hlB_sub.append (List.Sublist.refl [x'])
  have hhead_eq : (lB ++ [x']).head hlBx_ne = y := List.head_append_of_ne_nil hlB_ne
  obtain ⟨t, ht_ne, ht_sub, _, ht_w⟩ :=
    prepend_before_block (x := x) hlBx_sub hlBx_ne hs₁_sub hs₁_ne
  refine ⟨t, ht_ne, ?_, ?_⟩
  · simpa [List.cons_append] using ht_sub
  · rw [hhead_eq] at ht_w
    rw [Nat.dist_comm x' y']
    linarith

noncomputable def fOdd (n : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.Ico 1 n, (1 : ℝ) / (Nat.fib (2 * k) : ℝ)

noncomputable def fEven (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else fOdd (n - 1) + 1 / (Nat.fib (2 * n - 1) : ℝ)

lemma fOdd_one : fOdd 1 = 1 := by simp [fOdd]

lemma fEven_one : fEven 1 = 0 := by simp [fEven]

lemma fOdd_two : fOdd 2 = 2 := by
  unfold fOdd
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [hIco, Finset.sum_singleton]
  have hfib : Nat.fib 2 = 1 := by decide
  norm_num [hfib]

lemma fOdd_succ_of_ge_two {n : ℕ} (hn : 2 ≤ n) :
    fOdd n = fOdd (n - 1) + 1 / (Nat.fib (2 * n - 2) : ℝ) := by
  unfold fOdd
  have h1 : 1 ≤ n - 1 := by omega
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn_eq, Finset.sum_Ico_succ_top h1]
  have hmul : 2 * (n - 1) = 2 * n - 2 := by omega
  rw [hmul]
  ring

lemma fEven_of_ge_two {n : ℕ} (hn : 2 ≤ n) :
    fEven n = fOdd (n - 1) + 1 / (Nat.fib (2 * n - 1) : ℝ) := by
  unfold fEven
  rw [if_neg (by omega)]

lemma fib_cassini_step : ∀ m : ℕ,
    (Nat.fib (2 * m + 3) : ℝ) ^ 2 -
      (Nat.fib (2 * m + 2) : ℝ) * (Nat.fib (2 * m + 3) : ℝ) -
      (Nat.fib (2 * m + 2) : ℝ) ^ 2 - 1 = 0
  | 0 => by
    have h2 : Nat.fib 2 = 1 := by decide
    have h3 : Nat.fib 3 = 2 := by decide
    norm_num [h2, h3]
  | m + 1 => by
    have ih := fib_cassini_step m
    have h4 : (Nat.fib (2 * (m + 1) + 2) : ℝ) =
        (Nat.fib (2 * m + 2) : ℝ) + (Nat.fib (2 * m + 3) : ℝ) := by
      have h4_nat : Nat.fib (2 * (m + 1) + 2) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := by
        have hstep := Nat.fib_add_two (n := 2 * m + 2)
        have hidx : 2 * (m + 1) + 2 = 2 * m + 2 + 2 := by omega
        rw [hidx, hstep]
      exact_mod_cast h4_nat
    have h5 : (Nat.fib (2 * (m + 1) + 3) : ℝ) =
        (Nat.fib (2 * m + 2) : ℝ) + 2 * (Nat.fib (2 * m + 3) : ℝ) := by
      have h5_nat : Nat.fib (2 * (m + 1) + 3) = Nat.fib (2 * m + 2) + 2 * Nat.fib (2 * m + 3) := by
        have hstep1 := Nat.fib_add_two (n := 2 * m + 3)
        have hstep2 := Nat.fib_add_two (n := 2 * m + 2)
        have hidx1 : 2 * (m + 1) + 3 = 2 * m + 3 + 2 := by omega
        have hidx2 : 2 * m + 3 + 1 = 2 * m + 2 + 2 := by omega
        have hidx3 : 2 * m + 2 + 1 = 2 * m + 3 := by omega
        rw [hidx1, hstep1, hidx2, hstep2, hidx3]
        omega
      exact_mod_cast h5_nat
    rw [h4, h5]
    linear_combination ih

lemma fib_relations_of_ge_two {n : ℕ} (hn : 2 ≤ n) :
    let a : ℝ := Nat.fib (2 * n - 2)
    let b : ℝ := Nat.fib (2 * n - 1)
    1 ≤ Nat.fib (2 * n - 2) ∧
    2 ≤ Nat.fib (2 * n - 1) ∧
    Nat.fib (2 * n - 2) + 1 ≤ Nat.fib (2 * n - 1) ∧
    Nat.fib (2 * n) = Nat.fib (2 * n - 2) + Nat.fib (2 * n - 1) ∧
    Nat.fib (2 * n + 1) = Nat.fib (2 * n - 2) + 2 * Nat.fib (2 * n - 1) ∧
    b ^ 2 - a * b - a ^ 2 - 1 = 0 := by
  intro a b
  have hm : 2 * n - 2 = 2 * (n - 2) + 2 := by omega
  have hm1 : 2 * n - 1 = 2 * (n - 2) + 3 := by omega
  have ha_ge : 1 ≤ Nat.fib (2 * n - 2) := by
    have hpos : 0 < 2 * n - 2 := by omega
    exact Nat.succ_le_of_lt (Nat.fib_pos.mpr hpos)
  have hprev_pos : 1 ≤ Nat.fib (2 * n - 3) := by
    have hpos : 0 < 2 * n - 3 := by omega
    exact Nat.succ_le_of_lt (Nat.fib_pos.mpr hpos)
  have hb_eq : Nat.fib (2 * n - 1) = Nat.fib (2 * n - 3) + Nat.fib (2 * n - 2) := by
    have hstep := Nat.fib_add_two (n := 2 * n - 3)
    have hidx1 : 2 * n - 3 + 2 = 2 * n - 1 := by omega
    have hidx2 : 2 * n - 3 + 1 = 2 * n - 2 := by omega
    rw [hidx1, hidx2] at hstep
    exact hstep
  have h2n_eq : Nat.fib (2 * n) = Nat.fib (2 * n - 2) + Nat.fib (2 * n - 1) := by
    have hstep := Nat.fib_add_two (n := 2 * n - 2)
    have hidx1 : 2 * n - 2 + 2 = 2 * n := by omega
    have hidx2 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [hidx1, hidx2] at hstep
    exact hstep
  have h2np1_eq : Nat.fib (2 * n + 1) = Nat.fib (2 * n - 2) + 2 * Nat.fib (2 * n - 1) := by
    have hstep := Nat.fib_add_two (n := 2 * n - 1)
    have hidx1 : 2 * n - 1 + 2 = 2 * n + 1 := by omega
    have hidx2 : 2 * n - 1 + 1 = 2 * n := by omega
    rw [hidx1, hidx2] at hstep
    omega
  refine ⟨ha_ge, by omega, by omega, h2n_eq, h2np1_eq, ?_⟩
  dsimp only [a, b]
  rw [hm, hm1]
  exact fib_cassini_step (n - 2)

lemma fib_bounds_ge_three {n : ℕ} (hn : 3 ≤ n) :
    3 ≤ Nat.fib (2 * n - 2) ∧ 5 ≤ Nat.fib (2 * n - 1) := by
  have h4 : 4 ≤ 2 * n - 2 := by omega
  have h5 : 5 ≤ 2 * n - 1 := by omega
  have hf4 : Nat.fib 4 = 3 := by decide
  have hf5 : Nat.fib 5 = 5 := by decide
  exact ⟨hf4 ▸ Nat.fib_mono h4, hf5 ▸ Nat.fib_mono h5⟩

lemma ineq_b1_i {n : ℕ} (hn : 2 ≤ n) :
    1 / (Nat.fib (2 * n - 2) : ℝ) ≤
      1 / (Nat.fib (2 * n - 1) : ℝ) + 1 / ((Nat.fib (2 * n) : ℝ) - 1) := by
  obtain ⟨ha1, hb2, hab, h2n, _, hcas⟩ := fib_relations_of_ge_two hn
  have h2nR : (Nat.fib (2 * n) : ℝ) = (Nat.fib (2 * n - 2) : ℝ) + (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2n
  have ha_pos : (0 : ℝ) < (Nat.fib (2 * n - 2) : ℝ) := by
    exact_mod_cast (by omega : 0 < Nat.fib (2 * n - 2))
  have hb_pos : (0 : ℝ) < (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < Nat.fib (2 * n - 1))
  have habR : (Nat.fib (2 * n - 2) : ℝ) + 1 ≤ (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast hab
  set a : ℝ := (Nat.fib (2 * n - 2) : ℝ)
  set b : ℝ := (Nat.fib (2 * n - 1) : ℝ)
  have hab1 : 1 ≤ b - a := by linarith
  have hd_pos : 0 < a + b - 1 := by linarith
  rw [h2nR]
  have hdiff : 0 ≤ 1 / b + 1 / (a + b - 1) - 1 / a := by
    have hnum : 0 ≤ a * (a + b - 1) + a * b - b * (a + b - 1) := by
      have hid : a * (a + b - 1) + a * b - b * (a + b - 1) = (b - a - 1) - (b ^ 2 - a * b - a ^ 2 - 1) := by
        ring
      rw [hid, hcas]
      linarith
    have hfrac : 1 / b + 1 / (a + b - 1) - 1 / a =
        (a * (a + b - 1) + a * b - b * (a + b - 1)) / (b * (a + b - 1) * a) := by
      field_simp (disch := linarith)
    rw [hfrac]
    exact div_nonneg hnum (by positivity)
  linarith

lemma ineq_b1_ii {n : ℕ} (hn : 2 ≤ n) :
    1 / (Nat.fib (2 * n - 2) : ℝ) ≤
      1 / (Nat.fib (2 * n) : ℝ) + 1 / ((Nat.fib (2 * n - 1) : ℝ) - 1) := by
  obtain ⟨ha1, hb2, _, h2n, _, hcas⟩ := fib_relations_of_ge_two hn
  have h2nR : (Nat.fib (2 * n) : ℝ) = (Nat.fib (2 * n - 2) : ℝ) + (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2n
  have ha_pos : (0 : ℝ) < (Nat.fib (2 * n - 2) : ℝ) := by
    exact_mod_cast (by omega : 0 < Nat.fib (2 * n - 2))
  have hb_ge2 : (2 : ℝ) ≤ (Nat.fib (2 * n - 1) : ℝ) := by exact_mod_cast hb2
  set a : ℝ := (Nat.fib (2 * n - 2) : ℝ)
  set b : ℝ := (Nat.fib (2 * n - 1) : ℝ)
  have hb1_pos : 0 < b - 1 := by linarith
  have hab_pos : 0 < a + b := by linarith
  rw [h2nR]
  have hdiff : 0 ≤ 1 / (a + b) + 1 / (b - 1) - 1 / a := by
    have hnum : 0 ≤ a * (b - 1) + a * (a + b) - (a + b) * (b - 1) := by
      have hid : a * (b - 1) + a * (a + b) - (a + b) * (b - 1) =
          (b - 1) - (b ^ 2 - a * b - a ^ 2 - 1) := by ring
      rw [hid, hcas]
      linarith
    have hfrac : 1 / (a + b) + 1 / (b - 1) - 1 / a =
        (a * (b - 1) + a * (a + b) - (a + b) * (b - 1)) / ((a + b) * (b - 1) * a) := by
      field_simp (disch := linarith)
    rw [hfrac]
    exact div_nonneg hnum (by positivity)
  linarith

lemma ineq_b1p {n : ℕ} (hn : 3 ≤ n) :
    fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ) <
      1 / (Nat.fib (2 * n) : ℝ) + 1 / ((Nat.fib (2 * n + 1) : ℝ) - 2) +
        (fEven n + 1 / (Nat.fib (2 * n) : ℝ)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨_, _, _, h2n, h2np1, hcas⟩ := fib_relations_of_ge_two hn2
  obtain ⟨ha3, hb5⟩ := fib_bounds_ge_three hn
  rw [fOdd_succ_of_ge_two hn2, fEven_of_ge_two hn2]
  have h2nR : (Nat.fib (2 * n) : ℝ) = (Nat.fib (2 * n - 2) : ℝ) + (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2n
  have h2np1R : (Nat.fib (2 * n + 1) : ℝ) =
      (Nat.fib (2 * n - 2) : ℝ) + 2 * (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2np1
  have ha : (3 : ℝ) ≤ (Nat.fib (2 * n - 2) : ℝ) := by exact_mod_cast ha3
  have hb : (5 : ℝ) ≤ (Nat.fib (2 * n - 1) : ℝ) := by exact_mod_cast hb5
  set a : ℝ := (Nat.fib (2 * n - 2) : ℝ)
  set b : ℝ := (Nat.fib (2 * n - 1) : ℝ)
  rw [h2nR, h2np1R]
  set u : ℝ := a - 3
  set v : ℝ := b - 5
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hd1 : 0 < a + b := by linarith
  have hd2 : 0 < a + 2 * b - 2 := by linarith
  have hd3 : 0 < a + 2 * b := by linarith
  have hpos_diff : 0 < 2 * (1 / (a + b)) + 1 / (a + 2 * b - 2) + 1 / b - 1 / a - 1 / (a + 2 * b) := by
    have hnum : 0 < 2 * a * b * (a + 2 * b - 2) * (a + 2 * b) +
        a * b * (a + b) * (a + 2 * b) + a * (a + b) * (a + 2 * b - 2) * (a + 2 * b) -
        b * (a + b) * (a + 2 * b - 2) * (a + 2 * b) - a * b * (a + b) * (a + 2 * b - 2) := by
      have hid : 2 * a * b * (a + 2 * b - 2) * (a + 2 * b) +
          a * b * (a + b) * (a + 2 * b) + a * (a + b) * (a + 2 * b - 2) * (a + 2 * b) -
          b * (a + b) * (a + 2 * b - 2) * (a + 2 * b) - a * b * (a + b) * (a + 2 * b - 2) =
          (7 * a ^ 2 - 4 * b ^ 2 + 4 * b - 4) * (b ^ 2 - a * b - a ^ 2 - 1) +
          (8 * u ^ 4 + 13 * u ^ 3 * v + 159 * u ^ 3 + 115 * u ^ 2 * v + 992 * u ^ 2 +
            335 * u * v + 2503 * u + 325 * v + 2242) := by
        dsimp only [u, v]
        ring
      rw [hid, hcas, mul_zero, zero_add]
      positivity
    have hfrac : 2 * (1 / (a + b)) + 1 / (a + 2 * b - 2) + 1 / b - 1 / a - 1 / (a + 2 * b) =
        (2 * a * b * (a + 2 * b - 2) * (a + 2 * b) +
          a * b * (a + b) * (a + 2 * b) + a * (a + b) * (a + 2 * b - 2) * (a + 2 * b) -
          b * (a + b) * (a + 2 * b - 2) * (a + 2 * b) - a * b * (a + b) * (a + 2 * b - 2)) /
        ((a + b) * (a + 2 * b - 2) * b * a * (a + 2 * b)) := by
      field_simp (disch := linarith)
    rw [hfrac]
    exact div_pos hnum (by positivity)
  linarith

lemma ineq_b2p {n : ℕ} (hn : 3 ≤ n) :
    fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ) <
      1 / (Nat.fib (2 * n - 1) : ℝ) + 1 / ((Nat.fib (2 * n + 1) : ℝ) - 1) + fEven n := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨_, _, _, _, h2np1, hcas⟩ := fib_relations_of_ge_two hn2
  obtain ⟨ha3, hb5⟩ := fib_bounds_ge_three hn
  rw [fOdd_succ_of_ge_two hn2, fEven_of_ge_two hn2]
  have h2np1R : (Nat.fib (2 * n + 1) : ℝ) =
      (Nat.fib (2 * n - 2) : ℝ) + 2 * (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2np1
  have ha : (3 : ℝ) ≤ (Nat.fib (2 * n - 2) : ℝ) := by exact_mod_cast ha3
  have hb : (5 : ℝ) ≤ (Nat.fib (2 * n - 1) : ℝ) := by exact_mod_cast hb5
  set a : ℝ := (Nat.fib (2 * n - 2) : ℝ)
  set b : ℝ := (Nat.fib (2 * n - 1) : ℝ)
  rw [h2np1R]
  set u : ℝ := a - 3
  set v : ℝ := b - 5
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hd1 : 0 < a + 2 * b - 1 := by linarith
  have hd2 : 0 < a + 2 * b := by linarith
  have hpos_diff : 0 < 2 * (1 / b) + 1 / (a + 2 * b - 1) - 1 / a - 1 / (a + 2 * b) := by
    have hnum : 0 < 2 * a * (a + 2 * b - 1) * (a + 2 * b) + a * b * (a + 2 * b) -
        b * (a + 2 * b - 1) * (a + 2 * b) - a * b * (a + 2 * b - 1) := by
      have hid : 2 * a * (a + 2 * b - 1) * (a + 2 * b) + a * b * (a + 2 * b) -
          b * (a + 2 * b - 1) * (a + 2 * b) - a * b * (a + 2 * b - 1) =
          (2 - 4 * b) * (b ^ 2 - a * b - a ^ 2 - 1) +
          (2 * u ^ 3 + 3 * u ^ 2 * v + 33 * u ^ 2 + 18 * u * v + 144 * u + 23 * v + 171) := by
        dsimp only [u, v]
        ring
      rw [hid, hcas, mul_zero, zero_add]
      positivity
    have hfrac : 2 * (1 / b) + 1 / (a + 2 * b - 1) - 1 / a - 1 / (a + 2 * b) =
        (2 * a * (a + 2 * b - 1) * (a + 2 * b) + a * b * (a + 2 * b) -
          b * (a + 2 * b - 1) * (a + 2 * b) - a * b * (a + 2 * b - 1)) /
        (b * (a + 2 * b - 1) * a * (a + 2 * b)) := by
      field_simp (disch := linarith)
    rw [hfrac]
    exact div_pos hnum (by positivity)
  linarith

lemma ineq_b2pp {n : ℕ} (hn : 3 ≤ n) :
    fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ) <
      1 / (Nat.fib (2 * n) : ℝ) + 1 / (2 * (Nat.fib (2 * n - 1) : ℝ) - 1) + fEven n := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨_, _, _, h2n, h2np1, hcas⟩ := fib_relations_of_ge_two hn2
  obtain ⟨ha3, hb5⟩ := fib_bounds_ge_three hn
  rw [fOdd_succ_of_ge_two hn2, fEven_of_ge_two hn2]
  have h2nR : (Nat.fib (2 * n) : ℝ) = (Nat.fib (2 * n - 2) : ℝ) + (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2n
  have h2np1R : (Nat.fib (2 * n + 1) : ℝ) =
      (Nat.fib (2 * n - 2) : ℝ) + 2 * (Nat.fib (2 * n - 1) : ℝ) := by
    exact_mod_cast h2np1
  have ha : (3 : ℝ) ≤ (Nat.fib (2 * n - 2) : ℝ) := by exact_mod_cast ha3
  have hb : (5 : ℝ) ≤ (Nat.fib (2 * n - 1) : ℝ) := by exact_mod_cast hb5
  set a : ℝ := (Nat.fib (2 * n - 2) : ℝ)
  set b : ℝ := (Nat.fib (2 * n - 1) : ℝ)
  rw [h2nR, h2np1R]
  set u : ℝ := a - 3
  set v : ℝ := b - 5
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hd1 : 0 < a + b := by linarith
  have hd2 : 0 < 2 * b - 1 := by linarith
  have hd3 : 0 < a + 2 * b := by linarith
  have hpos_diff : 0 < 1 / (a + b) + 1 / (2 * b - 1) + 1 / b - 1 / a - 1 / (a + 2 * b) := by
    have hnum : 0 < a * b * (2 * b - 1) * (a + 2 * b) +
        a * b * (a + b) * (a + 2 * b) + a * (a + b) * (2 * b - 1) * (a + 2 * b) -
        b * (a + b) * (2 * b - 1) * (a + 2 * b) - a * b * (a + b) * (2 * b - 1) := by
      have hid : a * b * (2 * b - 1) * (a + 2 * b) +
          a * b * (a + b) * (a + 2 * b) + a * (a + b) * (2 * b - 1) * (a + 2 * b) -
          b * (a + b) * (2 * b - 1) * (a + 2 * b) - a * b * (a + b) * (2 * b - 1) =
          (a ^ 2 + 2 * a - 4 * b ^ 2 + b * (2 - 2 * a) - 4) * (b ^ 2 - a * b - a ^ 2 - 1) +
          (u ^ 4 + 2 * u ^ 3 * v + 23 * u ^ 3 + 20 * u ^ 2 * v + 160 * u ^ 2 +
            60 * u * v + 419 * u + 56 * v + 363) := by
        dsimp only [u, v]
        ring
      rw [hid, hcas, mul_zero, zero_add]
      positivity
    have hfrac : 1 / (a + b) + 1 / (2 * b - 1) + 1 / b - 1 / a - 1 / (a + 2 * b) =
        (a * b * (2 * b - 1) * (a + 2 * b) +
          a * b * (a + b) * (a + 2 * b) + a * (a + b) * (2 * b - 1) * (a + 2 * b) -
          b * (a + b) * (2 * b - 1) * (a + 2 * b) - a * b * (a + b) * (2 * b - 1)) /
        ((a + b) * (2 * b - 1) * b * a * (a + 2 * b)) := by
      field_simp (disch := linarith)
    rw [hfrac]
    exact div_pos hnum (by positivity)
  linarith

def HasGoodSublist (l : List ℕ) (c : ℝ) : Prop :=
  ∃ s : List ℕ, s ≠ [] ∧ s <+ l ∧ c ≤ jumpWeight s

def HasStrictSublist (l : List ℕ) (c : ℝ) : Prop :=
  ∃ s : List ℕ, s ≠ [] ∧ s <+ l ∧ c < jumpWeight s

lemma HasGoodSublist.of_reverse {l : List ℕ} {c : ℝ} (h : HasGoodSublist l.reverse c) :
    HasGoodSublist l c := by
  obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := h
  refine ⟨s.reverse, by simp [hs_ne], List.reverse_sublist.mp (by simpa using hs_sub), ?_⟩
  rwa [jumpWeight_reverse]

lemma HasStrictSublist.of_reverse {l : List ℕ} {c : ℝ} (h : HasStrictSublist l.reverse c) :
    HasStrictSublist l c := by
  obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := h
  refine ⟨s.reverse, by simp [hs_ne], List.reverse_sublist.mp (by simpa using hs_sub), ?_⟩
  rwa [jumpWeight_reverse]

lemma HasGoodSublist.of_comp {m : ℕ} {l : List ℕ} {c : ℝ} (hl : IsPerm1To m l)
    (h : HasGoodSublist (l.map (fun v => m + 1 - v)) c) :
    HasGoodSublist l c := by
  obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := h
  obtain ⟨s, hs_sub, rfl⟩ := List.sublist_map_iff.mp hs'_sub
  refine ⟨s, fun hnil => hs'_ne (by simp [hnil]), hs_sub, ?_⟩
  rwa [jumpWeight_comp m s (fun v hv => hl.2.2 v (hs_sub.subset hv))] at hs'_w

lemma HasStrictSublist.of_comp {m : ℕ} {l : List ℕ} {c : ℝ} (hl : IsPerm1To m l)
    (h : HasStrictSublist (l.map (fun v => m + 1 - v)) c) :
    HasStrictSublist l c := by
  obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := h
  obtain ⟨s, hs_sub, rfl⟩ := List.sublist_map_iff.mp hs'_sub
  refine ⟨s, fun hnil => hs'_ne (by simp [hnil]), hs_sub, ?_⟩
  rwa [jumpWeight_comp m s (fun v hv => hl.2.2 v (hs_sub.subset hv))] at hs'_w

lemma one_div_nat_dist_ge {a b d : ℕ} (_hd : 1 ≤ d) (h1 : 1 ≤ Nat.dist a b)
    (h2 : Nat.dist a b ≤ d) :
    1 / (d : ℝ) ≤ 1 / (Nat.dist a b : ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast h1
  · exact_mod_cast h2

lemma one_div_nat_dist_ge_sub1 {a b m : ℕ}
    (h1 : 1 ≤ Nat.dist a b) (h2 : Nat.dist a b + 1 ≤ m) :
    1 / ((m : ℝ) - 1) ≤ 1 / (Nat.dist a b : ℝ) := by
  have hd_pos : (0 : ℝ) < (Nat.dist a b : ℝ) := by exact_mod_cast h1
  have h2R : (Nat.dist a b : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h2
  exact one_div_le_one_div_of_le hd_pos (by linarith)

lemma one_div_nat_dist_ge_sub2 {a b m : ℕ}
    (h1 : 1 ≤ Nat.dist a b) (h2 : Nat.dist a b + 2 ≤ m) :
    1 / ((m : ℝ) - 2) ≤ 1 / (Nat.dist a b : ℝ) := by
  have hd_pos : (0 : ℝ) < (Nat.dist a b : ℝ) := by exact_mod_cast h1
  have h2R : (Nat.dist a b : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast h2
  exact one_div_le_one_div_of_le hd_pos (by linarith)

lemma one_div_nat_dist_ge_two_mul_sub1 {a b m : ℕ}
    (h1 : 1 ≤ Nat.dist a b) (h2 : Nat.dist a b + 1 ≤ 2 * m) :
    1 / (2 * (m : ℝ) - 1) ≤ 1 / (Nat.dist a b : ℝ) := by
  have hd_pos : (0 : ℝ) < (Nat.dist a b : ℝ) := by exact_mod_cast h1
  have h2R : (Nat.dist a b : ℝ) + 1 ≤ 2 * (m : ℝ) := by exact_mod_cast h2
  exact one_div_le_one_div_of_le hd_pos (by linarith)

lemma swap_two_inv_le {b c : ℝ} (hb : 5 ≤ b) (hbc : b + 3 ≤ c) :
    1 / b + 1 / (c - 2) ≤ 1 / (b - 1) + 1 / (c - 1) := by
  have h1 : 1 / (b - 1) - 1 / b = 1 / ((b - 1) * b) := by field_simp (disch := linarith); ring
  have h2 : 1 / (c - 2) - 1 / (c - 1) = 1 / ((c - 2) * (c - 1)) := by field_simp (disch := linarith); ring
  have hprod : (b - 1) * b ≤ (c - 2) * (c - 1) := by nlinarith
  have hdiv : 1 / ((c - 2) * (c - 1)) ≤ 1 / ((b - 1) * b) :=
    one_div_le_one_div_of_le (by nlinarith) hprod
  linarith

structure ChungGrahamStep (n : ℕ) : Prop where
  stmtA : ∀ l, IsPerm1To (Nat.fib (2 * n)) l → HasGoodSublist l (fEven n)
  stmtAp : ∀ l (hl : l ≠ []), IsPerm1To (Nat.fib (2 * n)) l →
    Nat.fib (2 * n - 1) < l.head hl → Nat.fib (2 * n - 1) < l.getLast hl →
    HasStrictSublist l (fEven n + 1 / (Nat.fib (2 * n) : ℝ))
  stmtB : ∀ l, IsPerm1To (Nat.fib (2 * n + 1)) l → HasGoodSublist l (fOdd n)
  stmtBp : ∀ l (hl : l ≠ []), IsPerm1To (Nat.fib (2 * n + 1)) l →
    Nat.fib (2 * n) < l.head hl → Nat.fib (2 * n) < l.getLast hl →
    HasStrictSublist l (fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ))

lemma cg_base : ChungGrahamStep 1 := by
  have hf1 : Nat.fib 1 = 1 := by decide
  have hf2 : Nat.fib 2 = 1 := by decide
  have hf3 : Nat.fib 3 = 2 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    rw [hf2] at hl
    rw [fEven_one]
    have hne : l ≠ [] := hl.ne_nil (by omega)
    exact ⟨l, hne, List.Sublist.refl l, jumpWeight_nonneg l⟩
  · intro l hl hperm hhead _
    rw [hf2] at hperm
    change Nat.fib 1 < l.head hl at hhead
    rw [hf1] at hhead
    have hmem : l.head hl ∈ l := List.head_mem hl
    have hb := (hperm.2.2 _ hmem).2
    omega
  · intro l hl
    rw [hf3] at hl
    rw [fOdd_one]
    rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · have := hl.2.1; simp at this
    · have := hl.2.1; simp at this
    · have ha := hl.2.2 a (by simp)
      have hb := hl.2.2 b (by simp)
      have hab : a ≠ b := by
        intro h
        subst h
        exact (List.nodup_cons.mp hl.1).1 (by simp)
      have hdist : Nat.dist a b = 1 := by
        simp only [Nat.dist]
        omega
      refine ⟨[a, b], by simp, List.Sublist.refl _, ?_⟩
      simp [jumpWeight, hdist]
    · have := hl.2.1; simp at this
  · intro l hl hperm hhead hlast
    rw [hf3] at hperm
    change Nat.fib 2 < l.head hl at hhead
    change Nat.fib 2 < l.getLast hl at hlast
    rw [hf2] at hhead hlast
    have hne_ends : l.head hl ≠ l.getLast hl :=
      head_ne_getLast_of_nodup hl hperm.1 (by rw [hperm.2.1])
    have hb1 := (hperm.2.2 _ (List.head_mem hl)).2
    have hb2 := (hperm.2.2 _ (List.getLast_mem hl)).2
    omega

lemma bp_two_aux (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To 5 l)
    (hhead : 3 < l.head hl) (hlast : 3 < l.getLast hl) (hlt : l.head hl < l.getLast hl) :
    HasStrictSublist l (2 + 1 / (5 : ℝ)) := by
  rcases l with _ | ⟨x, _ | ⟨u, _ | ⟨v, _ | ⟨w, _ | ⟨xp, rest⟩⟩⟩⟩⟩
  · exact absurd rfl hl
  · have := hperm.2.1; simp at this
  · have := hperm.2.1; simp at this
  · have := hperm.2.1; simp at this
  · have := hperm.2.1; simp at this
  · have hrest : rest = [] := by
      have := hperm.2.1
      simp at this
      exact this
    subst hrest
    simp at hhead hlast hlt
    have hx_b := hperm.2.2 x (by simp)
    have hxp_b := hperm.2.2 xp (by simp)
    have hx4 : x = 4 := by omega
    have hxp5 : xp = 5 := by omega
    subst hx4; subst hxp5
    have hnodup := hperm.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnodup
    have hu_b := hperm.2.2 u (by simp)
    have hv_b := hperm.2.2 v (by simp)
    have hw_b := hperm.2.2 w (by simp)
    have hu13 : 1 ≤ u ∧ u ≤ 3 := ⟨hu_b.1, by omega⟩
    have hv13 : 1 ≤ v ∧ v ≤ 3 := ⟨hv_b.1, by omega⟩
    have hw13 : 1 ≤ w ∧ w ≤ 3 := ⟨hw_b.1, by omega⟩
    rcases hu13 with ⟨hu1, hu3⟩
    rcases hv13 with ⟨hv1, hv3⟩
    rcases hw13 with ⟨hw1, hw3⟩
    interval_cases u <;> interval_cases v <;> interval_cases w
    all_goals try (exfalso; omega)
    · refine ⟨[4, 1, 2, 3, 5], by simp, List.Sublist.refl _, ?_⟩
      norm_num [jumpWeight, Nat.dist]
    · refine ⟨[4, 3, 2, 5], by simp, ?_, ?_⟩
      · exact List.Sublist.cons_cons 4 (List.Sublist.cons 1 (List.Sublist.refl [3, 2, 5]))
      · norm_num [jumpWeight, Nat.dist]
    · refine ⟨[4, 2, 1, 3, 5], by simp, List.Sublist.refl _, ?_⟩
      norm_num [jumpWeight, Nat.dist]
    · refine ⟨[4, 2, 3, 1, 5], by simp, List.Sublist.refl _, ?_⟩
      norm_num [jumpWeight, Nat.dist]
    · refine ⟨[4, 3, 1, 2, 5], by simp, List.Sublist.refl _, ?_⟩
      norm_num [jumpWeight, Nat.dist]
    · refine ⟨[4, 3, 2, 1, 5], by simp, List.Sublist.refl _, ?_⟩
      norm_num [jumpWeight, Nat.dist]

lemma blockFilter_head_tail {lo k x : ℕ} {tail : List ℕ}
    (hx_out : ¬ (lo + 1 ≤ x ∧ x ≤ lo + k)) :
    blockFilter lo k (x :: tail) = blockFilter lo k tail := by
  unfold blockFilter
  rw [List.filter_cons_of_neg]
  simpa using hx_out

lemma blockFilter_mid {lo k x x' : ℕ} {mid : List ℕ}
    (hx_out : ¬ (lo + 1 ≤ x ∧ x ≤ lo + k))
    (hx'_out : ¬ (lo + 1 ≤ x' ∧ x' ≤ lo + k)) :
    blockFilter lo k (x :: mid ++ [x']) = blockFilter lo k mid := by
  unfold blockFilter
  rw [List.cons_append, List.filter_cons_of_neg (by simpa using hx_out), List.filter_append,
    List.filter_cons_of_neg (by simpa using hx'_out), List.filter_nil, List.append_nil]

lemma blockFilter_ends_in {lo k x x' : ℕ} {mid : List ℕ}
    (hx_in : lo + 1 ≤ x ∧ x ≤ lo + k)
    (hx'_in : lo + 1 ≤ x' ∧ x' ≤ lo + k) :
    blockFilter lo k (x :: mid ++ [x']) = x :: blockFilter lo k mid ++ [x'] := by
  unfold blockFilter
  rw [List.cons_append, List.filter_cons_of_pos (by simpa using hx_in), List.filter_append,
    List.filter_cons_of_pos (by simpa using hx'_in), List.filter_nil, List.cons_append]

lemma cg_step_A_low {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n)) l)
    (hx_le : l.head hl ≤ Nat.fib (2 * n - 2)) :
    HasGoodSublist l (fEven n) := by
  obtain ⟨_, hb2, _, h2n_eq, _, _⟩ := fib_relations_of_ge_two hn
  have h2nm1_idx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  have ihB : ∀ u, IsPerm1To (Nat.fib (2 * n - 1)) u → HasGoodSublist u (fOdd (n - 1)) := by
    have h := ih.stmtB
    rwa [h2nm1_idx] at h
  cases l with
  | nil => exact absurd rfl hl
  | cons x tail =>
    simp only [List.head_cons] at hx_le
    have hbound : x + Nat.fib (2 * n - 1) ≤ Nat.fib (2 * n) := by omega
    obtain ⟨_, _, hlenB, hmemB, hpermB⟩ := blockFilter_props hperm hbound
    set lB := blockFilter x (Nat.fib (2 * n - 1)) (x :: tail)
    have hlB_eq : lB = blockFilter x (Nat.fib (2 * n - 1)) tail :=
      blockFilter_head_tail (by omega)
    have hlB_sub_tail : lB <+ tail := hlB_eq ▸ List.filter_sublist
    have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
    obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := ihB _ hpermB
    obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
    obtain ⟨t, ht_ne, ht_sub, _, ht_w⟩ :=
      prepend_before_block (x := x) hlB_sub_tail hlB_ne hs_sub hs_ne
    set y := lB.head hlB_ne
    have hy_mem : x + 1 ≤ y ∧ y ≤ x + Nat.fib (2 * n - 1) := hmemB y (List.head_mem hlB_ne)
    have hjump : 1 / (Nat.fib (2 * n - 1) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
      one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
    refine ⟨t, ht_ne, ht_sub, ?_⟩
    rw [fEven_of_ge_two hn]
    linarith

lemma cg_step_A {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hperm : IsPerm1To (Nat.fib (2 * n)) l) :
    HasGoodSublist l (fEven n) := by
  obtain ⟨ha1, hb2, _, h2n_eq, _, _⟩ := fib_relations_of_ge_two hn
  have h2nm1_idx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  have h2nm2_idx : 2 * (n - 1) = 2 * n - 2 := by omega
  have ihBp : ∀ u (hu : u ≠ []), IsPerm1To (Nat.fib (2 * n - 1)) u →
      Nat.fib (2 * n - 2) < u.head hu → Nat.fib (2 * n - 2) < u.getLast hu →
      HasStrictSublist u (fOdd (n - 1) + 1 / (Nat.fib (2 * n - 1) : ℝ)) := by
    have h := ih.stmtBp
    rwa [h2nm1_idx, h2nm2_idx] at h
  have hA_head : ∀ u (hu : u ≠ []), IsPerm1To (Nat.fib (2 * n)) u →
      (u.head hu ≤ Nat.fib (2 * n - 2) ∨ Nat.fib (2 * n - 1) < u.head hu) →
      HasGoodSublist u (fEven n) := by
    intro u hu hpu hcond
    rcases hcond with hlow | hhigh
    · exact cg_step_A_low hn ih u hu hpu hlow
    · apply HasGoodSublist.of_comp hpu
      have hne_c : u.map (fun v => Nat.fib (2 * n) + 1 - v) ≠ [] := by simp [hu]
      apply cg_step_A_low hn ih _ hne_c hpu.comp
      simp only [List.head_map]
      have hx_b := hpu.2.2 (u.head hu) (List.head_mem hu)
      omega
  have hl : l ≠ [] := hperm.ne_nil (by omega)
  by_cases h1 : l.head hl ≤ Nat.fib (2 * n - 2) ∨ Nat.fib (2 * n - 1) < l.head hl
  · exact hA_head l hl hperm h1
  · by_cases h2 : l.getLast hl ≤ Nat.fib (2 * n - 2) ∨ Nat.fib (2 * n - 1) < l.getLast hl
    · apply HasGoodSublist.of_reverse
      have hrev_ne : l.reverse ≠ [] := by simp [hl]
      apply hA_head l.reverse hrev_ne hperm.reverse
      rw [List.head_reverse]
      exact h2
    · have hx_mid : Nat.fib (2 * n - 2) < l.head hl ∧ l.head hl ≤ Nat.fib (2 * n - 1) :=
        ⟨Nat.lt_of_not_le fun h => h1 (Or.inl h), le_of_not_gt fun h => h1 (Or.inr h)⟩
      have hxp_mid : Nat.fib (2 * n - 2) < l.getLast hl ∧ l.getLast hl ≤ Nat.fib (2 * n - 1) :=
        ⟨Nat.lt_of_not_le fun h => h2 (Or.inl h), le_of_not_gt fun h => h2 (Or.inr h)⟩
      have hbound : 0 + Nat.fib (2 * n - 1) ≤ Nat.fib (2 * n) := by omega
      obtain ⟨hlB_sub, _, hlenB, _, hpermB⟩ := blockFilter_props hperm hbound
      set lB := blockFilter 0 (Nat.fib (2 * n - 1)) l
      have hlB_map : lB.map (· - 0) = lB := by simp
      rw [hlB_map] at hpermB
      have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
      obtain ⟨mid, hmid⟩ := list_eq_head_mid_last hl (by rw [hperm.2.1]; omega)
      have hlB_decomp : lB = l.head hl :: blockFilter 0 (Nat.fib (2 * n - 1)) mid ++ [l.getLast hl] := by
        dsimp only [lB]
        conv_lhs => rw [hmid]
        exact blockFilter_ends_in
          ⟨(hperm.2.2 _ (List.head_mem hl)).1, by omega⟩
          ⟨(hperm.2.2 _ (List.getLast_mem hl)).1, by omega⟩
      have hlB_head : lB.head hlB_ne = l.head hl := by
        simp [hlB_decomp]
      have hlB_last : lB.getLast hlB_ne = l.getLast hl := by
        have hne' : (l.head hl :: blockFilter 0 (Nat.fib (2 * n - 1)) mid) ++ [l.getLast hl] ≠ [] := by simp
        apply Option.some.inj
        rw [← List.getLast?_eq_some_getLast hlB_ne, hlB_decomp,
          List.getLast?_eq_some_getLast hne', getLast_append_singleton]
      obtain ⟨s, hs_ne, hs_sub, hs_strict⟩ :=
        ihBp lB hlB_ne hpermB (hlB_head ▸ hx_mid.1) (hlB_last ▸ hxp_mid.1)
      refine ⟨s, hs_ne, hs_sub.trans hlB_sub, ?_⟩
      rw [fEven_of_ge_two hn]
      linarith

lemma cg_step_Ap_lt {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n)) l)
    (hx : Nat.fib (2 * n - 1) < l.head hl) (hxp : Nat.fib (2 * n - 1) < l.getLast hl)
    (hlt : l.head hl < l.getLast hl) :
    HasStrictSublist l (fEven n + 1 / (Nat.fib (2 * n) : ℝ)) := by
  obtain ⟨_, _, _, h2n_eq, _, _⟩ := fib_relations_of_ge_two hn
  have h2nm1_idx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  have ihB : ∀ u, IsPerm1To (Nat.fib (2 * n - 1)) u → HasGoodSublist u (fOdd (n - 1)) := by
    have h := ih.stmtB
    rwa [h2nm1_idx] at h
  have hxp_le : l.getLast hl ≤ Nat.fib (2 * n) := (hperm.2.2 _ (List.getLast_mem hl)).2
  by_cases hn2_eq : n = 2
  · subst hn2_eq
    have hf3 : Nat.fib 3 = 2 := by decide
    have hf4 : Nat.fib 4 = 3 := by decide
    change Nat.fib 3 < l.head hl at hx
    rw [hf3] at hx
    rw [hf4] at hxp_le
    omega
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨ha3, hb5⟩ := fib_bounds_ge_three hn3
    obtain ⟨mid, hmid⟩ := list_eq_head_mid_last hl (by rw [hperm.2.1]; omega)
    set x := l.head hl
    set xp := l.getLast hl
    set lo := x - 1 - Nat.fib (2 * n - 1)
    have hbound : lo + Nat.fib (2 * n - 1) ≤ Nat.fib (2 * n) := by omega
    obtain ⟨_, hnodupB, hlenB, hmemB, hpermB⟩ := blockFilter_props hperm hbound
    set lB := blockFilter lo (Nat.fib (2 * n - 1)) l
    have hlB_mid : lB = blockFilter lo (Nat.fib (2 * n - 1)) mid := by
      dsimp only [lB]
      rw [hmid]
      exact blockFilter_mid (by omega) (by omega)
    have hlB_sub_mid : lB <+ mid := hlB_mid ▸ List.filter_sublist
    have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
    obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := ihB _ hpermB
    obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
    obtain ⟨t, ht_ne, ht_sub, ht_w⟩ := surround_around_block (x := x) (x' := xp) hlB_sub_mid hlB_ne hs_sub hs_ne
    set y := lB.head hlB_ne
    set yp := lB.getLast hlB_ne
    have hy_ne_yp : y ≠ yp := head_ne_getLast_of_nodup hlB_ne hnodupB (by omega)
    have hy_b := hmemB y (List.head_mem hlB_ne)
    have hyp_b := hmemB yp (List.getLast_mem hlB_ne)
    have hsum_jumps : 1 / (Nat.fib (2 * n - 1) : ℝ) + 1 / ((Nat.fib (2 * n) : ℝ) - 2) ≤
        1 / (Nat.dist x y : ℝ) + 1 / (Nat.dist xp yp : ℝ) := by
      by_cases hy_min : y = lo + 1
      · have hj1 : 1 / (Nat.fib (2 * n - 1) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
          one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        have hj2 : 1 / ((Nat.fib (2 * n) : ℝ) - 2) ≤ 1 / (Nat.dist xp yp : ℝ) :=
          one_div_nat_dist_ge_sub2 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        linarith
      · have hj1 : 1 / ((Nat.fib (2 * n - 1) : ℝ) - 1) ≤ 1 / (Nat.dist x y : ℝ) :=
          one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        have hj2 : 1 / ((Nat.fib (2 * n) : ℝ) - 1) ≤ 1 / (Nat.dist xp yp : ℝ) :=
          one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        have hb5R : (5 : ℝ) ≤ (Nat.fib (2 * n - 1) : ℝ) := by exact_mod_cast hb5
        have hbcR : (Nat.fib (2 * n - 1) : ℝ) + 3 ≤ (Nat.fib (2 * n) : ℝ) := by
          exact_mod_cast (by omega : Nat.fib (2 * n - 1) + 3 ≤ Nat.fib (2 * n))
        have hswap := swap_two_inv_le hb5R hbcR
        linarith
    have hstrict_frac : 1 / (Nat.fib (2 * n) : ℝ) < 1 / ((Nat.fib (2 * n) : ℝ) - 2) := by
      have h8 : (8 : ℝ) ≤ (Nat.fib (2 * n) : ℝ) := by
        exact_mod_cast (by omega : 8 ≤ Nat.fib (2 * n))
      exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
    refine ⟨t, ht_ne, hmid ▸ ht_sub, ?_⟩
    rw [fEven_of_ge_two hn]
    linarith

lemma cg_step_Ap {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n)) l)
    (hx : Nat.fib (2 * n - 1) < l.head hl) (hxp : Nat.fib (2 * n - 1) < l.getLast hl) :
    HasStrictSublist l (fEven n + 1 / (Nat.fib (2 * n) : ℝ)) := by
  obtain ⟨ha1, hb2, _, h2n_eq, _, _⟩ := fib_relations_of_ge_two hn
  have hne_ends : l.head hl ≠ l.getLast hl :=
    head_ne_getLast_of_nodup hl hperm.1 (by rw [hperm.2.1]; omega)
  rcases lt_or_gt_of_ne hne_ends with hlt | hgt
  · exact cg_step_Ap_lt hn ih l hl hperm hx hxp hlt
  · apply HasStrictSublist.of_reverse
    have hrev_ne : l.reverse ≠ [] := by simp [hl]
    apply cg_step_Ap_lt hn ih l.reverse hrev_ne hperm.reverse
    · rw [List.head_reverse]; exact hxp
    · rw [List.getLast_reverse]; exact hx
    · rw [List.head_reverse, List.getLast_reverse]; exact hgt

lemma cg_step_B_low {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n + 1)) l)
    (hx_le : l.head hl ≤ Nat.fib (2 * n - 1)) :
    HasGoodSublist l (fOdd n) := by
  obtain ⟨ha1, hb2, _, h2n_eq, h2np1_eq, _⟩ := fib_relations_of_ge_two hn
  have h2nm1_idx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  have ihB : ∀ u, IsPerm1To (Nat.fib (2 * n - 1)) u → HasGoodSublist u (fOdd (n - 1)) := by
    have h := ih.stmtB
    rwa [h2nm1_idx] at h
  cases l with
  | nil => exact absurd rfl hl
  | cons x tail =>
    simp only [List.head_cons] at hx_le
    have hbound : x + Nat.fib (2 * n) ≤ Nat.fib (2 * n + 1) := by omega
    obtain ⟨_, _, hlenB, hmemB, hpermB⟩ := blockFilter_props hperm hbound
    set lB := blockFilter x (Nat.fib (2 * n)) (x :: tail)
    have hlB_eq : lB = blockFilter x (Nat.fib (2 * n)) tail := blockFilter_head_tail (by omega)
    have hlB_sub_tail : lB <+ tail := hlB_eq ▸ List.filter_sublist
    have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
    set y := lB.head hlB_ne
    have hy_b := hmemB y (List.head_mem hlB_ne)
    by_cases hy_lt : y < x + Nat.fib (2 * n)
    · obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := cg_step_A hn ih _ hpermB
      obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
      obtain ⟨t, ht_ne, ht_sub, _, ht_w⟩ :=
        prepend_before_block (x := x) hlB_sub_tail hlB_ne hs_sub hs_ne
      have hj : 1 / ((Nat.fib (2 * n) : ℝ) - 1) ≤ 1 / (Nat.dist x y : ℝ) :=
        one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
      refine ⟨t, ht_ne, ht_sub, ?_⟩
      rw [fOdd_succ_of_ge_two hn]
      have hfE := fEven_of_ge_two hn
      have hineq := ineq_b1_i hn
      linarith
    · have hy_eq : y = x + Nat.fib (2 * n) := by omega
      have hbound2 : x + Nat.fib (2 * n - 1) ≤ Nat.fib (2 * n + 1) := by omega
      obtain ⟨_, _, hlenB2, hmemB2, hpermB2⟩ := blockFilter_props hperm hbound2
      set lB2 := blockFilter x (Nat.fib (2 * n - 1)) (x :: tail)
      have hlB2_ne : lB2 ≠ [] := fun h => by simp [h] at hlenB2; omega
      set z := lB2.head hlB2_ne
      have hz_b := hmemB2 z (List.head_mem hlB2_ne)
      obtain ⟨s2', hs2'_ne, hs2'_sub, hs2'_w⟩ := ihB _ hpermB2
      obtain ⟨s2, hs2_ne, hs2_sub, hs2_w⟩ := lift_sublist_shift hmemB2 hs2'_ne hs2'_sub
      by_cases hz_le : z ≤ x + Nat.fib (2 * n - 2)
      · have hlB2_eq : lB2 = blockFilter x (Nat.fib (2 * n - 1)) tail :=
          blockFilter_head_tail (by omega)
        have hlB2_sub_tail : lB2 <+ tail := hlB2_eq ▸ List.filter_sublist
        obtain ⟨t, ht_ne, ht_sub, _, ht_w⟩ :=
          prepend_before_block (x := x) hlB2_sub_tail hlB2_ne hs2_sub hs2_ne
        have hj : 1 / (Nat.fib (2 * n - 2) : ℝ) ≤ 1 / (Nat.dist x z : ℝ) :=
          one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        refine ⟨t, ht_ne, ht_sub, ?_⟩
        rw [fOdd_succ_of_ge_two hn]
        linarith
      · cases h_lB_cases : lB with
        | nil => exact absurd h_lB_cases hlB_ne
        | cons y0 tailB =>
          have hy0 : y0 = y := by simp [y, h_lB_cases]
          have hlB2_from_lB : lB2 = blockFilter x (Nat.fib (2 * n - 1)) lB := by
            dsimp only [lB2, lB, blockFilter]
            rw [List.filter_filter]
            congr 1
            ext v
            simp
            omega
          have hlB2_sub_tailB : lB2 <+ tailB := by
            rw [hlB2_from_lB, h_lB_cases, blockFilter_head_tail (by omega)]
            exact List.filter_sublist
          obtain ⟨s1, hs1_ne, hs1_sub, _, hs1_w⟩ :=
            prepend_before_block (x := y0) hlB2_sub_tailB hlB2_ne hs2_sub hs2_ne
          have hs1_sub_lB : s1 <+ lB := h_lB_cases ▸ hs1_sub
          obtain ⟨t, ht_ne, ht_sub, _, ht_w⟩ :=
            prepend_before_block (x := x) hlB_sub_tail hlB_ne hs1_sub_lB hs1_ne
          have hj1 : 1 / (Nat.dist x (lB.head hlB_ne) : ℝ) = 1 / (Nat.fib (2 * n) : ℝ) := by
            have hxy : Nat.dist x y = Nat.fib (2 * n) := by simp [Nat.dist, hy_eq]
            simp [y, hxy]
          have hj2 : 1 / ((Nat.fib (2 * n - 1) : ℝ) - 1) ≤ 1 / (Nat.dist y0 z : ℝ) :=
            one_div_nat_dist_ge_sub1 (by simp [Nat.dist, hy0, hy_eq]; omega)
              (by simp [Nat.dist, hy0, hy_eq]; omega)
          refine ⟨t, ht_ne, ht_sub, ?_⟩
          rw [fOdd_succ_of_ge_two hn]
          have hineq := ineq_b1_ii hn
          linarith

lemma cg_step_B_mid_lt {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n + 1)) l)
    (hx : Nat.fib (2 * n - 1) < l.head hl) (hxp : l.getLast hl ≤ Nat.fib (2 * n))
    (hlt : l.head hl < l.getLast hl) :
    HasGoodSublist l (fOdd n) := by
  obtain ⟨_, _, _, h2n_eq, h2np1_eq, _⟩ := fib_relations_of_ge_two hn
  have h2nm1_idx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  have ihB : ∀ u, IsPerm1To (Nat.fib (2 * n - 1)) u → HasGoodSublist u (fOdd (n - 1)) := by
    have h := ih.stmtB
    rwa [h2nm1_idx] at h
  by_cases hn2_eq : n = 2
  · subst hn2_eq
    have hf3 : Nat.fib 3 = 2 := by decide
    have hf4 : Nat.fib 4 = 3 := by decide
    change Nat.fib 3 < l.head hl at hx
    change l.getLast hl ≤ Nat.fib 4 at hxp
    rw [hf3] at hx; rw [hf4] at hxp
    omega
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨_, hb5⟩ := fib_bounds_ge_three hn3
    obtain ⟨mid, hmid⟩ := list_eq_head_mid_last hl (by rw [hperm.2.1]; omega)
    set x := l.head hl
    set xp := l.getLast hl
    set lo := x - 1 - Nat.fib (2 * n - 1)
    have hbound : lo + Nat.fib (2 * n - 1) ≤ Nat.fib (2 * n + 1) := by omega
    obtain ⟨_, hnodupB, hlenB, hmemB, hpermB⟩ := blockFilter_props hperm hbound
    set lB := blockFilter lo (Nat.fib (2 * n - 1)) l
    have hlB_mid : lB = blockFilter lo (Nat.fib (2 * n - 1)) mid := by
      dsimp only [lB]
      rw [hmid]
      exact blockFilter_mid (by omega) (by omega)
    have hlB_sub_mid : lB <+ mid := hlB_mid ▸ List.filter_sublist
    have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
    obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := ihB _ hpermB
    obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
    obtain ⟨t, ht_ne, ht_sub, ht_w⟩ := surround_around_block (x := x) (x' := xp) hlB_sub_mid hlB_ne hs_sub hs_ne
    set y := lB.head hlB_ne
    set yp := lB.getLast hlB_ne
    have hy_ne_yp : y ≠ yp := head_ne_getLast_of_nodup hlB_ne hnodupB (by omega)
    have hy_b := hmemB y (List.head_mem hlB_ne)
    have hyp_b := hmemB yp (List.getLast_mem hlB_ne)
    have hsum_jumps : 1 / (Nat.fib (2 * n - 1) : ℝ) + 1 / ((Nat.fib (2 * n) : ℝ) - 1) ≤
        1 / (Nat.dist x y : ℝ) + 1 / (Nat.dist xp yp : ℝ) := by
      have hj1 : 1 / (Nat.fib (2 * n - 1) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
        one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
      have hj2 : 1 / ((Nat.fib (2 * n) : ℝ) - 1) ≤ 1 / (Nat.dist xp yp : ℝ) :=
        one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
      linarith
    refine ⟨t, ht_ne, hmid ▸ ht_sub, ?_⟩
    rw [fOdd_succ_of_ge_two hn]
    have hineq := ineq_b1_i hn
    linarith

lemma cg_step_B {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hperm : IsPerm1To (Nat.fib (2 * n + 1)) l) :
    HasGoodSublist l (fOdd n) := by
  obtain ⟨ha1, hb2, _, h2n_eq, h2np1_eq, _⟩ := fib_relations_of_ge_two hn
  have hB_head : ∀ u (hu : u ≠ []), IsPerm1To (Nat.fib (2 * n + 1)) u →
      (u.head hu ≤ Nat.fib (2 * n - 1) ∨ Nat.fib (2 * n) < u.head hu) →
      HasGoodSublist u (fOdd n) := by
    intro u hu hpu hcond
    rcases hcond with hlow | hhigh
    · exact cg_step_B_low hn ih u hu hpu hlow
    · apply HasGoodSublist.of_comp hpu
      have hne_c : u.map (fun v => Nat.fib (2 * n + 1) + 1 - v) ≠ [] := by simp [hu]
      apply cg_step_B_low hn ih _ hne_c hpu.comp
      simp only [List.head_map]
      have hx_b := hpu.2.2 (u.head hu) (List.head_mem hu)
      omega
  have hl : l ≠ [] := hperm.ne_nil (by omega)
  by_cases h1 : l.head hl ≤ Nat.fib (2 * n - 1) ∨ Nat.fib (2 * n) < l.head hl
  · exact hB_head l hl hperm h1
  · by_cases h2 : l.getLast hl ≤ Nat.fib (2 * n - 1) ∨ Nat.fib (2 * n) < l.getLast hl
    · apply HasGoodSublist.of_reverse
      have hrev_ne : l.reverse ≠ [] := by simp [hl]
      apply hB_head l.reverse hrev_ne hperm.reverse
      rw [List.head_reverse]
      exact h2
    · have hx_mid : Nat.fib (2 * n - 1) < l.head hl ∧ l.head hl ≤ Nat.fib (2 * n) :=
        ⟨Nat.lt_of_not_le fun h => h1 (Or.inl h), le_of_not_gt fun h => h1 (Or.inr h)⟩
      have hxp_mid : Nat.fib (2 * n - 1) < l.getLast hl ∧ l.getLast hl ≤ Nat.fib (2 * n) :=
        ⟨Nat.lt_of_not_le fun h => h2 (Or.inl h), le_of_not_gt fun h => h2 (Or.inr h)⟩
      have hne_ends : l.head hl ≠ l.getLast hl :=
        head_ne_getLast_of_nodup hl hperm.1 (by rw [hperm.2.1]; omega)
      rcases lt_or_gt_of_ne hne_ends with hlt | hgt
      · exact cg_step_B_mid_lt hn ih l hl hperm hx_mid.1 hxp_mid.2 hlt
      · apply HasGoodSublist.of_reverse
        have hrev_ne : l.reverse ≠ [] := by simp [hl]
        apply cg_step_B_mid_lt hn ih l.reverse hrev_ne hperm.reverse
        · rw [List.head_reverse]; exact hxp_mid.1
        · rw [List.getLast_reverse]; exact hx_mid.2
        · rw [List.head_reverse, List.getLast_reverse]; exact hgt

lemma cg_step_Bp_lt {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n + 1)) l)
    (hx : Nat.fib (2 * n) < l.head hl) (hxp : Nat.fib (2 * n) < l.getLast hl)
    (hlt : l.head hl < l.getLast hl) :
    HasStrictSublist l (fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ)) := by
  obtain ⟨_, _, _, h2n_eq, h2np1_eq, _⟩ := fib_relations_of_ge_two hn
  by_cases hn2_eq : n = 2
  · subst hn2_eq
    have hf4 : Nat.fib 4 = 3 := by decide
    have hf5 : Nat.fib 5 = 5 := by decide
    rw [hf5] at hperm ⊢
    rw [hf4] at hx hxp
    rw [fOdd_two]
    exact bp_two_aux l hl hperm hx hxp hlt
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨ha3, hb5⟩ := fib_bounds_ge_three hn3
    have hxp_le : l.getLast hl ≤ Nat.fib (2 * n + 1) := (hperm.2.2 _ (List.getLast_mem hl)).2
    obtain ⟨mid, hmid⟩ := list_eq_head_mid_last hl (by rw [hperm.2.1]; omega)
    set x := l.head hl
    set xp := l.getLast hl
    set lo := x - 1 - Nat.fib (2 * n)
    have hbound : lo + Nat.fib (2 * n) ≤ Nat.fib (2 * n + 1) := by omega
    obtain ⟨_, hnodupB, hlenB, hmemB, hpermB⟩ := blockFilter_props hperm hbound
    set lB := blockFilter lo (Nat.fib (2 * n)) l
    have hlB_mid : lB = blockFilter lo (Nat.fib (2 * n)) mid := by
      dsimp only [lB]
      rw [hmid]
      exact blockFilter_mid (by omega) (by omega)
    have hlB_sub_mid : lB <+ mid := hlB_mid ▸ List.filter_sublist
    have hlB_ne : lB ≠ [] := fun h => by simp [h] at hlenB; omega
    set y := lB.head hlB_ne
    set yp := lB.getLast hlB_ne
    have hy_ne_yp : y ≠ yp := head_ne_getLast_of_nodup hlB_ne hnodupB (by omega)
    have hy_b := hmemB y (List.head_mem hlB_ne)
    have hyp_b := hmemB yp (List.getLast_mem hlB_ne)
    by_cases hboth_low : y < x - Nat.fib (2 * n - 1) ∧ yp < x - Nat.fib (2 * n - 1)
    · set lB_sh := lB.map (· - lo)
      have hlB_sh_ne : lB_sh ≠ [] := by simp [lB_sh, hlB_ne]
      set lB_comp := lB_sh.map (fun v => Nat.fib (2 * n) + 1 - v)
      have hlB_comp_ne : lB_comp ≠ [] := by simp [lB_comp, hlB_sh_ne]
      have hcomp_head : Nat.fib (2 * n - 1) < lB_comp.head hlB_comp_ne := by
        simp only [lB_comp, lB_sh, List.head_map]
        change Nat.fib (2 * n - 1) < Nat.fib (2 * n) + 1 - (y - lo)
        omega
      have hcomp_last : Nat.fib (2 * n - 1) < lB_comp.getLast hlB_comp_ne := by
        simp only [lB_comp, lB_sh, List.getLast_map]
        change Nat.fib (2 * n - 1) < Nat.fib (2 * n) + 1 - (yp - lo)
        omega
      have hstrict_sh : HasStrictSublist lB_sh (fEven n + 1 / (Nat.fib (2 * n) : ℝ)) :=
        HasStrictSublist.of_comp hpermB
          (cg_step_Ap hn ih lB_comp hlB_comp_ne hpermB.comp hcomp_head hcomp_last)
      obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := hstrict_sh
      obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
      obtain ⟨t, ht_ne, ht_sub, ht_w⟩ := surround_around_block (x := x) (x' := xp) hlB_sub_mid hlB_ne hs_sub hs_ne
      have hsum_jumps : 1 / (Nat.fib (2 * n) : ℝ) + 1 / ((Nat.fib (2 * n + 1) : ℝ) - 2) ≤
          1 / (Nat.dist x y : ℝ) + 1 / (Nat.dist xp yp : ℝ) := by
        by_cases hyp_min : yp = lo + 1
        · have hj1 : 1 / ((Nat.fib (2 * n) : ℝ) - 1) ≤ 1 / (Nat.dist x y : ℝ) :=
            one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
          have hj2 : 1 / ((Nat.fib (2 * n + 1) : ℝ) - 1) ≤ 1 / (Nat.dist xp yp : ℝ) :=
            one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
          have hc8R : (5 : ℝ) ≤ (Nat.fib (2 * n) : ℝ) := by
            exact_mod_cast (by omega : 5 ≤ Nat.fib (2 * n))
          have hcdR : (Nat.fib (2 * n) : ℝ) + 3 ≤ (Nat.fib (2 * n + 1) : ℝ) := by
            exact_mod_cast (by omega : Nat.fib (2 * n) + 3 ≤ Nat.fib (2 * n + 1))
          have hswap := swap_two_inv_le hc8R hcdR
          linarith
        · have hj1 : 1 / (Nat.fib (2 * n) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
            one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
          have hj2 : 1 / ((Nat.fib (2 * n + 1) : ℝ) - 2) ≤ 1 / (Nat.dist xp yp : ℝ) :=
            one_div_nat_dist_ge_sub2 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
          linarith
      refine ⟨t, ht_ne, hmid ▸ ht_sub, ?_⟩
      have hineq := ineq_b1p hn3
      linarith
    · obtain ⟨s', hs'_ne, hs'_sub, hs'_w⟩ := cg_step_A hn ih _ hpermB
      obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := lift_sublist_shift hmemB hs'_ne hs'_sub
      obtain ⟨t, ht_ne, ht_sub, ht_w⟩ := surround_around_block (x := x) (x' := xp) hlB_sub_mid hlB_ne hs_sub hs_ne
      by_cases hy_hi : x - Nat.fib (2 * n - 1) ≤ y
      · have hj1 : 1 / (Nat.fib (2 * n - 1) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
          one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        have hj2 : 1 / ((Nat.fib (2 * n + 1) : ℝ) - 1) ≤ 1 / (Nat.dist xp yp : ℝ) :=
          one_div_nat_dist_ge_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        refine ⟨t, ht_ne, hmid ▸ ht_sub, ?_⟩
        have hineq := ineq_b2p hn3
        linarith
      · have hj1 : 1 / (Nat.fib (2 * n) : ℝ) ≤ 1 / (Nat.dist x y : ℝ) :=
          one_div_nat_dist_ge (by omega) (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        have hj2 : 1 / (2 * (Nat.fib (2 * n - 1) : ℝ) - 1) ≤ 1 / (Nat.dist xp yp : ℝ) :=
          one_div_nat_dist_ge_two_mul_sub1 (by simp [Nat.dist]; omega) (by simp [Nat.dist]; omega)
        refine ⟨t, ht_ne, hmid ▸ ht_sub, ?_⟩
        have hineq := ineq_b2pp hn3
        linarith

lemma cg_step_Bp {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1))
    (l : List ℕ) (hl : l ≠ []) (hperm : IsPerm1To (Nat.fib (2 * n + 1)) l)
    (hx : Nat.fib (2 * n) < l.head hl) (hxp : Nat.fib (2 * n) < l.getLast hl) :
    HasStrictSublist l (fOdd n + 1 / (Nat.fib (2 * n + 1) : ℝ)) := by
  obtain ⟨ha1, hb2, _, h2n_eq, h2np1_eq, _⟩ := fib_relations_of_ge_two hn
  have hne_ends : l.head hl ≠ l.getLast hl :=
    head_ne_getLast_of_nodup hl hperm.1 (by rw [hperm.2.1]; omega)
  rcases lt_or_gt_of_ne hne_ends with hlt | hgt
  · exact cg_step_Bp_lt hn ih l hl hperm hx hxp hlt
  · apply HasStrictSublist.of_reverse
    have hrev_ne : l.reverse ≠ [] := by simp [hl]
    apply cg_step_Bp_lt hn ih l.reverse hrev_ne hperm.reverse
    · rw [List.head_reverse]; exact hxp
    · rw [List.getLast_reverse]; exact hx
    · rw [List.head_reverse, List.getLast_reverse]; exact hgt

lemma cg_step {n : ℕ} (hn : 2 ≤ n) (ih : ChungGrahamStep (n - 1)) : ChungGrahamStep n :=
  ⟨cg_step_A hn ih, cg_step_Ap hn ih, cg_step_B hn ih, cg_step_Bp hn ih⟩

lemma cg_all : ∀ k : ℕ, ChungGrahamStep (k + 1)
  | 0 => cg_base
  | k + 1 => cg_step (by omega) (cg_all k)

noncomputable def pathVariation (g : ℕ → ℝ) : List ℕ → ℝ
  | a :: b :: t => |g b - g a| + pathVariation g (b :: t)
  | _ => 0

lemma pathVariation_eq_sub_of_pairwise (g : ℕ → ℝ) :
    ∀ (s : List ℕ) (hs : s ≠ []),
      s.Pairwise (fun i j => g i ≤ g j) →
      pathVariation g s = g (s.getLast hs) - g (s.head hs)
  | [], hs, _ => absurd rfl hs
  | [a], _, _ => by simp [pathVariation]
  | a :: b :: t, _, hpw => by
    have hbt : b :: t ≠ [] := by simp
    have hab : g a ≤ g b := (List.pairwise_cons.mp hpw).1 b (by simp)
    have ih := pathVariation_eq_sub_of_pairwise g (b :: t) hbt (List.pairwise_cons.mp hpw).2
    simp only [pathVariation, ih, List.head_cons, List.getLast_cons hbt,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    ring

lemma weighted_jump_lt_variation {g : ℕ → ℝ} {γ : ℝ} (_hγ : 0 < γ) :
    ∀ (s : List ℕ), s.Nodup → 0 < jumpWeight s →
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → γ < (Nat.dist a b : ℝ) * |g b - g a|) →
      γ * jumpWeight s < pathVariation g s
  | [], _, hpos, _ => by simp [jumpWeight] at hpos
  | [_], _, hpos, _ => by simp [jumpWeight] at hpos
  | a :: b :: t, hnodup, _, hbad => by
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ List.mem_cons_self)
    have hd_pos : (0 : ℝ) < (Nat.dist a b : ℝ) :=
      by exact_mod_cast (Nat.dist_pos_of_ne hab)
    have hedge : γ * (1 / (Nat.dist a b : ℝ)) < |g b - g a| := by
      rw [mul_one_div, div_lt_iff₀' hd_pos]
      exact hbad a (by simp) b (by simp) hab
    have htail_le : ∀ (u : List ℕ), u.Nodup →
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → γ < (Nat.dist x y : ℝ) * |g y - g x|) →
        γ * jumpWeight u ≤ pathVariation g u := by
      intro u
      induction u with
      | nil => intros; simp [jumpWeight, pathVariation]
      | cons x rest ih =>
        intro hnu hbu
        cases rest with
        | nil => simp [jumpWeight, pathVariation]
        | cons y r2 =>
          have hxy : x ≠ y := fun h => (List.nodup_cons.mp hnu).1 (h ▸ List.mem_cons_self)
          have hxy_pos : (0 : ℝ) < (Nat.dist x y : ℝ) := by exact_mod_cast (Nat.dist_pos_of_ne hxy)
          have he : γ * (1 / (Nat.dist x y : ℝ)) ≤ |g y - g x| := by
            rw [mul_one_div, div_le_iff₀' hxy_pos]
            exact (hbu x (by simp) y (by simp) hxy).le
          have hr := ih (List.nodup_cons.mp hnu).2 (fun p hp q hq => hbu p (by simp [hp]) q (by simp [hq]))
          simp only [jumpWeight, pathVariation]
          linarith
    have htr := htail_le (b :: t) (List.nodup_cons.mp hnodup).2
      (fun x hx y hy => hbad x (by simp [hx]) y (by simp [hy]))
    simp only [jumpWeight, pathVariation]
    linarith

lemma close_pair_in_window (x : ℕ → ℝ) (hx : ∀ k, x k ∈ Set.Icc 0 1) (n : ℕ) (hn : 2 ≤ n) (M : ℕ) :
    ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ Nat.fib (2 * n + 1) ∧
      ((j - i : ℕ) : ℝ) * |x (M + j) - x (M + i)| ≤ 1 / fOdd n := by
  classical
  set m := Nat.fib (2 * n + 1)
  have hm_ge : 5 ≤ m := by
    have h5 : 5 ≤ 2 * n + 1 := by omega
    have hf5 : Nat.fib 5 = 5 := by decide
    exact hf5 ▸ Nat.fib_mono h5
  let g : ℕ → ℝ := fun k => x (M + k)
  let r : ℕ → ℕ → Prop := fun i j => g i ≤ g j
  let L₀ : List ℕ := (List.range m).map (· + 1)
  have hL₀_perm1 : IsPerm1To m L₀ := by
    refine ⟨?_, by simp [L₀], ?_⟩
    · exact List.nodup_range.map (fun _ _ h => by omega)
    · intro v hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      rw [List.mem_range] at hk
      omega
  let l : List ℕ := List.insertionSort r L₀
  have hperm_sort : l.Perm L₀ := List.perm_insertionSort r L₀
  have hl_perm : IsPerm1To m l :=
    ⟨hperm_sort.nodup_iff.mpr hL₀_perm1.1,
     hperm_sort.length_eq.trans hL₀_perm1.2.1,
     fun v hv => hL₀_perm1.2.2 v (hperm_sort.mem_iff.mp hv)⟩
  have hl_pw : l.Pairwise r :=
    @List.pairwise_insertionSort ℕ r _ ⟨fun i j => le_total (g i) (g j)⟩
      ⟨fun _ _ _ => le_trans⟩ L₀
  have hstep : ChungGrahamStep n := by
    have heq : n = (n - 1) + 1 := by omega
    exact heq ▸ cg_all (n - 1)
  obtain ⟨s, hs_ne, hs_sub, hs_w⟩ := hstep.stmtB l hl_perm
  have hfOdd_pos : 1 ≤ fOdd n := by
    unfold fOdd
    have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.Ico 1 n, (1 : ℝ) / (Nat.fib (2 * k) : ℝ) :=
      Finset.sum_nonneg fun k _ => by positivity
    linarith
  have hγ_pos : 0 < 1 / fOdd n := by positivity
  by_contra hnone
  have hbad : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      1 / fOdd n < (Nat.dist a b : ℝ) * |g b - g a| := by
    intro a ha b hb hab
    have ha_b := hl_perm.2.2 a (hs_sub.subset ha)
    have hb_b := hl_perm.2.2 b (hs_sub.subset hb)
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hnot : ¬ (((b - a : ℕ) : ℝ) * |g b - g a| ≤ 1 / fOdd n) :=
        fun hle => hnone ⟨a, b, ha_b.1, hlt, hb_b.2, hle⟩
      simpa [Nat.dist_eq_sub_of_le hlt.le] using lt_of_not_ge hnot
    · have hnot : ¬ (((a - b : ℕ) : ℝ) * |g a - g b| ≤ 1 / fOdd n) :=
        fun hle => hnone ⟨b, a, hb_b.1, hgt, ha_b.2, hle⟩
      simpa [Nat.dist_eq_sub_of_le_right hgt.le, abs_sub_comm] using lt_of_not_ge hnot
  have hs_nodup : s.Nodup := hl_perm.1.sublist hs_sub
  have hs_pw : s.Pairwise r := hl_pw.sublist hs_sub
  have hw_pos : 0 < jumpWeight s := by linarith
  have hlt_var := weighted_jump_lt_variation hγ_pos s hs_nodup hw_pos hbad
  have hvar_le : pathVariation g s ≤ 1 := by
    rw [pathVariation_eq_sub_of_pairwise g s hs_ne hs_pw]
    have hlast := hx (M + s.getLast hs_ne)
    have hhead := hx (M + s.head hs_ne)
    dsimp only [g]
    linarith [hlast.2, hhead.1]
  have hprod_ge : 1 ≤ (1 / fOdd n) * jumpWeight s := by
    calc
      (1 : ℝ) = (1 / fOdd n) * fOdd n := by field_simp
      _ ≤ (1 / fOdd n) * jumpWeight s :=
        mul_le_mul_of_nonneg_left hs_w (by positivity)
  linarith

lemma inf_liminf_le_inv_fOdd (x : ℕ → ℝ) (hx : ∀ k, x k ∈ Set.Icc 0 1) (n : ℕ) (hn : 2 ≤ n) :
    (⨅ (q : ℕ+), atTop.liminf (fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|)) ≤ 1 / fOdd n := by
  set M_len := Nat.fib (2 * n + 1)
  have hall : ∃ᶠ m in atTop,
      ∃ d ∈ Finset.Icc 1 M_len, (d : ℝ) * |x (m + d) - x m| ≤ 1 / fOdd n := by
    rw [Filter.frequently_atTop]
    intro M
    obtain ⟨i, j, hi1, hij, hjM, hclose⟩ := close_pair_in_window x hx n hn M
    refine ⟨M + i, by omega, j - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hidx : M + i + (j - i) = M + j := by omega
    rw [hidx]
    exact hclose
  obtain ⟨d, hd_mem, hfreq⟩ := (Finset.frequently_exists (Finset.Icc 1 M_len)).mp hall
  let p : ℕ+ := ⟨d, lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd_mem).1⟩
  let u : ℕ → ℝ := fun m => (p : ℕ) * |x (m + (p : ℕ)) - x m|
  have hfreq' : ∃ᶠ m in atTop, u m ≤ 1 / fOdd n := by simpa [u, p] using hfreq
  have hlim : atTop.liminf u ≤ 1 / fOdd n :=
    Filter.liminf_le_of_frequently_le hfreq'
      (Filter.isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall fun m => by positivity))
  have hbdd : BddBelow (Set.range fun q : ℕ+ =>
      atTop.liminf (fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    let v : ℕ → ℝ := fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|
    have hv_upper : ∀ m, v m ≤ (q : ℕ) := by
      intro m
      have h1 := hx (m + (q : ℕ))
      have h2 := hx m
      have habs : |x (m + (q : ℕ)) - x m| ≤ 1 :=
        abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      calc
        (q : ℕ) * |x (m + (q : ℕ)) - x m| ≤ (q : ℕ) * 1 := by gcongr
        _ = (q : ℕ) := mul_one _
    exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le atTop (Filter.Eventually.of_forall hv_upper))
      (Filter.Eventually.of_forall fun m => by positivity)
  exact (ciInf_le hbdd p).trans hlim

lemma fib_even_ge_pow_two : ∀ k : ℕ, 2 ^ k ≤ Nat.fib (2 * (k + 1))
  | 0 => by decide
  | k + 1 => by
    have ih := fib_even_ge_pow_two k
    have h1 : 2 * (k + 2) = 2 * (k + 1) + 2 := by omega
    have h2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h3 : 2 * k + 3 = (2 * k + 1) + 2 := by omega
    have h4 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [h1, Nat.fib_add_two, h2, h3, Nat.fib_add_two, h4]
    have hpos : 0 ≤ Nat.fib (2 * k + 1) := Nat.zero_le _
    omega

lemma tendsto_inv_fOdd :
    Tendsto (fun k : ℕ => 1 / fOdd (k + 2)) atTop
      (𝓝 (1 / (1 + ∑' (k : ℕ+), (1 : ℝ) / (2 * (k : ℕ)).fib))) := by
  let gNat : ℕ → ℝ := fun k => (1 : ℝ) / (Nat.fib (2 * (k + 1)) : ℝ)
  have hg_nonneg : ∀ k, 0 ≤ gNat k := fun _ => by positivity
  have hg_le : ∀ k, gNat k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have hpow : (2 : ℝ) ^ k ≤ (Nat.fib (2 * (k + 1)) : ℝ) := by
      exact_mod_cast fib_even_ge_pow_two k
    rw [one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hsumm : Summable gNat :=
    Summable.of_nonneg_of_le hg_nonneg hg_le summable_geometric_two
  have htsum_eq : (∑' (k : ℕ+), (1 : ℝ) / (2 * (k : ℕ)).fib) = ∑' k : ℕ, gNat k := by
    rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
    refine tsum_congr fun k => ?_
    simp [gNat, Equiv.pnatEquivNat]
  have hfOdd_eq : ∀ k : ℕ, fOdd (k + 2) = 1 + ∑ m ∈ Finset.range (k + 1), gNat m := by
    intro k
    unfold fOdd
    congr 1
    induction k with
    | zero =>
      have hIco : Finset.Ico 1 2 = {1} := by decide
      rw [hIco, Finset.range_one, Finset.sum_singleton, Finset.sum_singleton]
    | succ k ih =>
      have h1 : 1 ≤ k + 2 := by omega
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Finset.sum_Ico_succ_top h1,
        Finset.sum_range_succ, ih]
  have htend_sum : Tendsto (fun k : ℕ => 1 + ∑ m ∈ Finset.range (k + 1), gNat m) atTop
      (𝓝 (1 + ∑' k : ℕ, gNat k)) := by
    have h1 := hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.add h1
  have hc_ne : 1 + ∑' k : ℕ, gNat k ≠ 0 := by
    have htsum_nonneg : 0 ≤ ∑' k : ℕ, gNat k := tsum_nonneg hg_nonneg
    linarith
  rw [htsum_eq]
  simp_rw [hfOdd_eq]
  exact tendsto_const_nhds.div htend_sum hc_ne

end Erdos480CGAux

theorem prove_erdos480_cg : type_of% @Erdos480.erdos_480.variants.chung_graham := by
  intro c x hx
  have hle : ∀ k : ℕ,
      (⨅ (n : ℕ+), Filter.atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|)) ≤
        1 / Erdos480CGAux.fOdd (k + 2) :=
    fun k => Erdos480CGAux.inf_liminf_le_inv_fOdd x hx (k + 2) (by omega)
  exact ge_of_tendsto Erdos480CGAux.tendsto_inv_fOdd (Filter.Eventually.of_forall hle)

theorem OMA.solution : type_of% @Erdos480.erdos_480.variants.chung_graham :=
  prove_erdos480_cg
