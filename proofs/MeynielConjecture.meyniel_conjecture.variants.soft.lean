import FormalConjectures.Wikipedia.MeynielConjecture
import Mathlib

/-!
# Proof of the Soft / Weak Meyniel Conjecture (`MeynielConjecture.meyniel_conjecture.variants.soft`)

Mathematical proof and original Lean 4 formalization by Jesse Geneson
(The weak Meyniel conjecture is true, November 2026; Lean 4 formalization
`jgeneson/weak-meyniel` at commit `836439032cc9`, PALOMAR-2026-11-26-000031,
licensed under the Apache License, Version 2.0).

Adapted into a single self-contained file targeting the pinned
`FormalConjectures.Wikipedia.MeynielConjecture` declarations on Lean v4.33.1,
using the explicit three-page `O(n^(3/4) log(2n))` upper bound (`copNumber_three_quarters`)
and deriving `c(G) <= C * n^(1 - 1/8)` (`soft_of_bound`).

Licensed under the Apache License, Version 2.0 (the License);
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0
-/

-- === BEGIN Meyniel.Game ===
section Meyniel_Game

/-! # The ordinary visible game of cops and robber
The robber and each cop can wait or traverse one edge. Histories supplied to a policy
are stored newest observation first. Test walks supplied to `Hits` are chronological.
-/

namespace Meyniel
universe u
variable {V : Type u}

def Step (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

structure Policy (G : SimpleGraph V) where
  pos : List V → V
  legal : ∀ x h, Step G (pos h) (pos (x :: h))

def Policy.stay (G : SimpleGraph V) (v : V) : Policy G where
  pos := fun _ => v
  legal := fun _ _ => Or.inl rfl

/-- A capture by the end of a fixed walk. On a singleton only coincidence can count:
there is no additional cop move after the final robber move. -/
def Hits {G : SimpleGraph V} (s : Policy G) (h : List V) : List V → Prop
  | [] => False
  | [x] => s.pos h = x
  | x :: y :: xs => s.pos h = x ∨ s.pos (x :: h) = x ∨ Hits s (x :: h) (y :: xs)

/-- All consecutive robber positions are joined by a step. -/
def LegalWord (G : SimpleGraph V) (w : List V) : Prop := w.IsChain (Step G)

/-- A bounded perfect-information game tree. After the cops move they must be able
to handle every legal response by the robber. -/
def CatchesWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | t+1, c, r => (∃ i, c i = r) ∨ ∃ c' : Fin k → V,
      (∀ i, Step G (c i) (c' i)) ∧
      ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CatchesWithin G k t c' r')

def WinsWith (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ t, CatchesWithin G k t c r

noncomputable def copNumber (G : SimpleGraph V) : ℕ := sInf {k | WinsWith G k}

/-- Cop number bounded by the size of any winning team. -/
theorem copNumber_le_of_win {G : SimpleGraph V} {k : ℕ} (hk : WinsWith G k) :
    copNumber G ≤ k := Nat.sInf_le hk

theorem winsWith_card [Fintype V] (G : SimpleGraph V) : WinsWith G (Fintype.card V) := by
  classical
  exact ⟨(Fintype.equivFin V).symm, fun r => ⟨0, Fintype.equivFin V r, by simp⟩⟩

end Meyniel
end Meyniel_Game
-- === END Meyniel.Game ===

-- === BEGIN Meyniel.Cover ===
section Meyniel_Cover

/-! # Deterministic covering and adaptive robbers -/

namespace Meyniel

universe u v

/-- Choosing the strategies successively on the *remaining* walks pays a logarithmic
factor, and requires no control over overlaps outside that remaining set. -/
theorem greedy_residual {W : Type u} {S : Type v} (C : S → W → Prop) [∀ s, DecidablePred (C s)] (p : ℝ)
    (hp : p ≤ 1) (U : Finset W)
    (select : ∀ R ⊆ U, R.Nonempty → ∃ s, p * R.card ≤ (R.filter (C s)).card)
    (m : ℕ) :
    ∃ team : List S, team.length ≤ m ∧
      (↑(U.filter (fun w => ∀ s ∈ team, ¬ C s w)).card : ℝ) ≤ U.card * (1-p)^m := by
  classical
  induction m with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ m ih =>
    obtain ⟨team, hl, hb⟩ := ih
    let R := U.filter (fun w => ∀ s ∈ team, ¬ C s w)
    by_cases hR : R.Nonempty
    · obtain ⟨s, hs⟩ := select R (Finset.filter_subset ..) hR
      refine ⟨s :: team, by simp; omega, ?_⟩
      have hsame : U.filter (fun w => ∀ z ∈ s :: team, ¬ C z w) =
          R.filter (fun w => ¬ C s w) := by
        ext w
        simp [R, and_left_comm, and_comm]
      rw [hsame]
      have hc := Finset.card_filter_add_card_filter_not (s := R) (C s)
      have hadd : (((R.filter (C s)).card : ℝ) +
          ((R.filter (fun w => ¬ C s w)).card : ℝ)) = R.card := by exact_mod_cast hc
      have hstep : ((R.filter (fun w => ¬ C s w)).card : ℝ) ≤ R.card * (1-p) := by nlinarith
      change (R.card : ℝ) ≤ _ at hb
      calc
        _ ≤ (R.card : ℝ) * (1-p) := hstep
        _ ≤ (U.card * (1-p)^m) * (1-p) := mul_le_mul_of_nonneg_right hb (by linarith)
        _ = _ := by ring
    · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      refine ⟨team, by omega, ?_⟩
      change (R.card : ℝ) ≤ _
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)

/-- An actual cover once the residual bound drops below one. -/
theorem greedy_cover {W : Type u} {S : Type v} (C : S → W → Prop)
    [∀ s, DecidablePred (C s)] (p : ℝ) (hp : p ≤ 1) (U : Finset W)
    (select : ∀ R ⊆ U, R.Nonempty → ∃ s, p * R.card ≤ (R.filter (C s)).card)
    (m : ℕ) (small : (U.card : ℝ) * (1-p)^m < 1) :
    ∃ team : List S, team.length ≤ m ∧ ∀ w ∈ U, ∃ s ∈ team, C s w := by
  classical
  obtain ⟨team, hl, hb⟩ := greedy_residual C p hp U select m
  refine ⟨team, hl, ?_⟩
  have hlt := hb.trans_lt small
  have hempty : (U.filter (fun w => ∀ s ∈ team, ¬ C s w)).card < 1 := by
    exact_mod_cast hlt
  intro w hw
  by_contra! hmiss
  have hm : w ∈ U.filter (fun w => ∀ s ∈ team, ¬ C s w) := Finset.mem_filter.mpr ⟨hw, hmiss⟩
  have := Finset.card_pos.mpr ⟨_, hm⟩
  omega

variable {V : Type u} {G : SimpleGraph V}

/-- Following the covering team produces a winning game tree, even when the robber
sees all moves before choosing its next vertex. -/
theorem catchesWithin_of_cover {k : ℕ} (team : Fin k → Policy G) (t : ℕ)
    (h : List V) (r : V)
    (cover : ∀ tail : List V, tail.length = t → LegalWord G (r :: tail) →
      ∃ i, Hits (team i) h (r :: tail)) :
    CatchesWithin G k t (fun i => (team i).pos h) r := by
  induction t generalizing h r with
  | zero =>
    exact cover [] rfl (by simp [LegalWord])
  | succ t ih =>
    by_cases hstart : ∃ i, (team i).pos h = r
    · exact Or.inl hstart
    refine Or.inr ⟨fun i => (team i).pos (r::h), fun i => (team i).legal r h, ?_⟩
    by_cases hmove : ∃ i, (team i).pos (r :: h) = r
    · exact Or.inl hmove
    refine Or.inr (fun y hy => ih (r :: h) y ?_)
    intro tail ht hw
    obtain ⟨i, hit⟩ := cover (y :: tail) (by simp [ht]) (List.isChain_cons_cons.mpr ⟨hy, hw⟩)
    rcases hit with hc | hc | hc
    · exact (hstart ⟨i, hc⟩).elim
    · exact (hmove ⟨i, hc⟩).elim
    · exact ⟨i, hc⟩

/-- The subtype of legal chronological words is a subset of all `n^(T+1)` words. -/
noncomputable def walks [Fintype V] (G : SimpleGraph V) (T : ℕ) : Finset (Fin (T+1) → V) := by
  classical
  exact Finset.univ.filter (fun w => LegalWord G (List.ofFn w))

theorem walks_card_le [Fintype V] (G : SimpleGraph V) (T : ℕ) :
    (walks G T).card ≤ Fintype.card V ^ (T+1) := by
  classical
  simpa [walks] using Finset.card_le_card (Finset.filter_subset
    (fun w : Fin (T+1) → V => LegalWord G (List.ofFn w)) Finset.univ)

theorem winsWith_of_word_cover [Fintype V] {k T : ℕ} (team : Fin k → Policy G)
    (cover : ∀ w ∈ walks G T, ∃ i, Hits (team i) [] (List.ofFn w)) :
    WinsWith G k := by
  refine ⟨fun i => (team i).pos [], fun r => ⟨T, catchesWithin_of_cover team T [] r ?_⟩⟩
  intro tail ht hw
  let l := r :: tail
  have hlen : l.length = T+1 := by simp [l, ht]
  let w : Fin (T+1) → V := fun i => l.get (Fin.cast hlen.symm i)
  have hword : List.ofFn w = l := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  have hm : w ∈ walks G T := by
    classical
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hword.symm ▸ hw⟩
  have hc := cover w hm
  rw [hword] at hc
  exact hc

end Meyniel
end Meyniel_Cover
-- === END Meyniel.Cover ===

-- === BEGIN Meyniel.Bounds ===
section Meyniel_Bounds

/-! # Choosing the time horizon and the number of cops -/

namespace Meyniel
open scoped Classical

noncomputable def horizon (N D : ℕ) : ℕ := ⌈(D : ℝ) * Real.log N / Real.log 2⌉₊
noncomputable def diamThreshold (N : ℕ) : ℕ := ⌈(N : ℝ) ^ (1/4 : ℝ) / Real.log (2*N)⌉₊
noncomputable def budget (N T : ℕ) : ℕ :=
  ⌊Real.sqrt (2*N) * ((T+1 : ℕ) : ℝ) * Real.log N⌋₊ + 1

theorem horizon_large (N D : ℕ) :
    D * Real.log N ≤ (horizon N D : ℝ) * Real.log 2 :=
  (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp (Nat.le_ceil _)

theorem power_decay {x p : ℝ} (hx : 0 < x) (hp : p ≤ 1) {m : ℕ}
    (hm : Real.log x < (m : ℝ) * p) : x * (1-p)^m < 1 := by
  have he : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    x * (1-p)^m ≤ x * (Real.exp (-p))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) he _) hx.le
    _ = x / Real.exp ((m:ℝ)*p) := by
      rw [← Real.exp_nat_mul, mul_neg, Real.exp_neg, div_eq_mul_inv]
    _ < 1 := (div_lt_one (Real.exp_pos _)).mpr ((Real.log_lt_iff_lt_exp hx).mp hm)

/-- The one-cop estimate on arbitrary residual walk families. All seed choices have
already been fixed when the policy in the conclusion is selected. -/
def WalkFraction {V : Type*} [Fintype V] (G : SimpleGraph V) (T : ℕ) (p : ℝ) : Prop :=
  ∀ R ⊆ walks G T, R.Nonempty → ∃ s : Policy G,
    p * R.card ≤ (R.filter (fun w => Hits s [] (List.ofFn w))).card

theorem winsWith_budget {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    {N T : ℕ} (hN : 1 ≤ N) (hsize : Fintype.card V ≤ N)
    (hf : WalkFraction G T (1 / Real.sqrt (2*N))) : WinsWith G (budget N T) := by
  classical
  let p : ℝ := 1 / Real.sqrt (2*N)
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (2*N) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs0 : 0 < Real.sqrt (2*N) := by linarith
  have hp : p ≤ 1 := (div_le_one hs0).mpr hs
  have hb : Real.sqrt (2*N) * ((T+1 : ℕ) : ℝ) * Real.log N < (budget N T : ℝ) := by
    unfold budget
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one
      (Real.sqrt (2*N) * ((T : ℝ)+1) * Real.log N)
  have hdec : (N : ℝ)^(T+1) * (1-p)^(budget N T) < 1 := by
    apply power_decay (pow_pos (by linarith) _) hp
    rw [Real.log_pow]
    dsimp [p]
    rw [mul_one_div, lt_div_iff₀ hs0]
    nlinarith [hb]
  have hcard : ((walks G T).card : ℝ) ≤ (N:ℝ)^(T+1) := by
    exact_mod_cast (walks_card_le G T).trans (Nat.pow_le_pow_left hsize _)
  have hsmall := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (sub_nonneg.mpr hp) (budget N T))) hdec
  obtain ⟨L, hlen, hc⟩ := greedy_cover (fun (s : Policy G) w => Hits s [] (List.ofFn w))
    p hp (walks G T) hf (budget N T) hsmall
  let team (i : Fin (budget N T)) : Policy G :=
    if hi : i.val < L.length then L.get ⟨i.val,hi⟩ else Policy.stay G (Classical.arbitrary V)
  apply winsWith_of_word_cover team
  intro w hw
  obtain ⟨s, hmem, hit⟩ := hc w hw
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hlen⟩, ?_⟩
  simpa [team, i.isLt] using hit

end Meyniel
end Meyniel_Bounds
-- === END Meyniel.Bounds ===

-- === BEGIN Meyniel.Extension ===
section Meyniel_Extension

namespace Meyniel.Extension
variable {V : Type*} {G : SimpleGraph V} {T : ℕ}

/-- A fixed shortest route from each possible endpoint to the common home. -/
noncomputable def route (hc : G.Connected) (x home : V) : G.Walk x home :=
  (hc.exists_walk_length_eq_dist x home).choose

theorem route_length (hc : G.Connected) (x home : V) :
    (route hc x home).length = G.dist x home :=
  (hc.exists_walk_length_eq_dist x home).choose_spec

noncomputable def extendWord (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    (t : ℕ) : V :=
  if h : t < T then w ⟨t, by omega⟩
  else (route hc (w (Fin.last T)) home).getVert (t-T)

theorem extendWord_at (hc : G.Connected) (home : V) (w : Fin (T+1) → V) (i : Fin (T+1)) :
    extendWord hc home w i.val = w i := by
  obtain ⟨t, ht⟩ := i
  by_cases h : t < T
  · simp [extendWord, h]
  · have he : t = T := by omega
    subst t
    simp [extendWord, Fin.last]

theorem extendWord_after (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    {t : ℕ} (ht : T ≤ t) :
    extendWord hc home w t = (route hc (w (Fin.last T)) home).getVert (t-T) := by
  simp [extendWord, Nat.not_lt.mpr ht]

theorem extendWord_home [Finite V] (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    {t : ℕ} (ht : T + G.diam ≤ t) : extendWord hc home w t = home := by
  letI : Nonempty V := ⟨home⟩
  rw [extendWord_after hc home w (by omega)]
  apply SimpleGraph.Walk.getVert_of_length_le
  rw [route_length]
  have hd : G.dist (w (Fin.last T)) home ≤ G.diam :=
    SimpleGraph.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)
  omega

theorem extendWord_step (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    (hw : LegalWord G (List.ofFn w)) (t : ℕ) :
    Step G (extendWord hc home w t) (extendWord hc home w (t+1)) := by
  by_cases ht : t < T
  · have he (i : ℕ) (hi : i < T+1) : extendWord hc home w i = w ⟨i, hi⟩ :=
      extendWord_at hc home w ⟨i, hi⟩
    rw [he t (by omega), he (t+1) (by omega)]
    exact List.isChain_ofFn.mp hw t (by omega)
  · have h : T ≤ t := by omega
    rw [extendWord_after hc home w h, extendWord_after hc home w (by omega)]
    let path := route hc (w (Fin.last T)) home
    change Step G (path.getVert (t - T)) (path.getVert (t + 1 - T))
    rw [show t+1-T = (t-T)+1 by omega]
    by_cases hl : t - T < path.length
    · exact Or.inr (path.adj_getVert_succ hl)
    · left
      rw [path.getVert_of_length_le (by omega : path.length ≤ t - T),
        path.getVert_of_length_le (by omega : path.length ≤ t - T + 1)]

end Meyniel.Extension
end Meyniel_Extension
-- === END Meyniel.Extension ===

-- === BEGIN Meyniel.Guard ===
section Meyniel_Guard

/-! A legal cop on a geodesic, with the precise move order of the game. -/
namespace Meyniel.Guard

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V}

/-- The projection index measured in the current connected territory. -/
noncomputable def shadow (p : G.Walk a b) (r : V) : ℕ := min p.length (G.dist a r)

lemma shadow_on_path (p : G.Walk a b) (geo : p.length = G.dist a b)
    (i : ℕ) (hi : i ≤ p.length) : shadow p (p.getVert i) = i := by
  have eqn := length_eq_dist_of_subwalk geo (p.isSubwalk_take i)
  rw [p.take_length, inf_eq_left.mpr hi] at eqn
  simp [shadow, ← eqn, hi]

lemma shadow_step (p : G.Walk a b) {r s : V} (h : r = s ∨ G.Adj r s) :
    shadow p r ≤ shadow p s + 1 ∧ shadow p s ≤ shadow p r + 1 := by
  rcases h with rfl | hadj
  · omega
  have hdist := hadj.diff_dist_adj (u := a)
  unfold shadow
  omega

/-- Move one integer step towards a requested index. An illegal input jump
is harmless: the cop still makes a legal move. -/
def approach (i goal : ℕ) : ℕ := max (i - 1) (min (i + 1) goal)

lemma approach_step (i goal : ℕ) : approach i goal ≤ i + 1 ∧ i ≤ approach i goal + 1 := by
  unfold approach
  omega

/-- At a cop turn the most recent robber observation heads the list. -/
noncomputable def index (p : G.Walk a b) : List V → ℕ
  | [] => 0
  | r :: h => approach (index p h) (shadow p r)

lemma index_le (p : G.Walk a b) (h : List V) : index p h ≤ p.length := by
  induction h with
  | nil => simp [index]
  | cons x h ih =>
    simp only [index, approach, shadow]
    omega

lemma vertices_step (p : G.Walk a b) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : i ≤ j + 1 ∧ j ≤ i + 1) : p.getVert i = p.getVert j ∨ G.Adj (p.getVert i) (p.getVert j) := by
  rcases (lt_trichotomy i j) with hlt | rfl | hgt
  · have e : j = i + 1 := by omega
    subst j
    exact Or.inr (p.adj_getVert_succ (by omega))
  · exact Or.inl rfl
  · have e : i = j + 1 := by omega
    subst i
    exact Or.inr (p.adj_getVert_succ (by omega)).symm

noncomputable def position (p : G.Walk a b) (h : List V) : V := p.getVert (index p h)

lemma legal (p : G.Walk a b) (r : V) (h : List V) :
    position p h = position p (r :: h) ∨ G.Adj (position p h) (position p (r :: h)) := by
  apply vertices_step p (index_le p _) (index_le p _)
  simpa [index, and_comm] using approach_step (index p h) (shadow p r)

@[simp] lemma position_nil (p : G.Walk a b) : position p [] = a := by simp [position, index]

/-- On any legal history the actual position has a closed form. In particular
acquisition takes at most the path length, irrespective of the robber moves. -/
lemma index_on_legal_history (p : G.Walk a b) (r : V) (h : List V)
    (hw : (r :: h).IsChain (fun x y ↦ x = y ∨ G.Adj x y)) :
    index p (r :: h) = min (h.length + 1) (shadow p r) := by
  induction h generalizing r with
  | nil => simp [index, approach]
  | cons s tail ih =>
    obtain ⟨hrs, htail⟩ := List.isChain_cons_cons.mp hw
    have hs := shadow_step p hrs
    rw [index, ih s htail, List.length_cons]
    unfold approach
    omega

/-- If the robber visits any vertex of the path after acquisition, the next
cop move lands on that vertex, before the robber gets another move. -/
lemma capture_on_path (p : G.Walk a b) (geo : p.length = G.dist a b) (r : V) (h : List V)
    (hw : (r :: h).IsChain (fun x y ↦ x = y ∨ G.Adj x y))
    (acquired : p.length ≤ h.length + 1) (hr : r ∈ p.support) : position p (r :: h) = r := by
  obtain ⟨i, hi, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  subst r
  rw [position, index_on_legal_history p _ _ hw, shadow_on_path p geo _ hlen,
    min_eq_right (by omega)]

/-- A diametral geodesic has exactly `diam + 1` distinct vertices available
for deletion, even when the diameter is zero. -/
lemma exists_diametral_guard_path [DecidableEq V] (conn : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), p.length = G.dist a b ∧ p.length = G.diam ∧
      p.support.toFinset.card = G.diam + 1 := by
  letI : Nonempty V := conn.nonempty
  obtain ⟨a, b, hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist a b
  have hpath := p.isPath_of_length_eq_dist hp
  refine ⟨a, b, p, hp, hp.trans hab, ?_⟩
  rw [List.toFinset_card_of_nodup hpath.support_nodup, p.length_support, hp, hab]

end Meyniel.Guard

namespace Meyniel.Guard
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a b : V} {k : ℕ}

noncomputable def policy (p : G.Walk a b) : Policy G where
  pos := position p
  legal := legal p

private lemma add_time {t : ℕ} {c : Fin k → V} {r : V} (h : CatchesWithin G k t c r) :
    CatchesWithin G k (t+1) c r := by
  induction t generalizing c r with
  | zero => exact Or.inl h
  | succ t ih =>
    rcases h with cap | ⟨d, hd, cap | hnext⟩
    · exact Or.inl cap
    · exact Or.inr ⟨d, hd, Or.inl cap⟩
    · exact Or.inr ⟨d, hd, Or.inr (fun r' hr' => ih (hnext r' hr'))⟩

private lemma more_time {t t' : ℕ} {c : Fin k → V} {r : V} (h : CatchesWithin G k t c r)
    (ht : t ≤ t') : CatchesWithin G k t' c r := by
  induction t', ht using Nat.le_induction with
  | base => exact h
  | succ t' _ ih => exact add_time ih

/-- Finite branching turns separate finite capture times after each possible
robber reply into a uniform finite time before the cops' move. -/
private lemma advance [Fintype V] {c d : Fin k → V} {r : V} (hm : ∀ i, Step G (c i) (d i))
    (hw : ∀ s, Step G r s → ∃ t, CatchesWithin G k t d s) : ∃ t, CatchesWithin G k t c r := by
  classical
  have hp : ∀ s, ∃ t, Step G r s → CatchesWithin G k t d s := by
    intro s
    by_cases h : Step G r s
    · obtain ⟨t, ht⟩ := hw s h
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun hs => False.elim (h hs)⟩
  choose times htimes using hp
  exact ⟨Finset.univ.sup times + 1, Or.inr ⟨d, hm, Or.inr (fun s hs =>
    more_time (htimes s hs) (Finset.le_sup (f := times) (Finset.mem_univ s)))⟩⟩

/-- The path guard is slot zero. The other cops retain their local numbering. -/
private def team (g : V) (c : Fin k → V) : Fin (k+1) → V := Fin.cons g c

private lemma team_step {g g' : V} {c d : Fin k → V} (h : Step G g g')
    (hc : ∀ i, Step G (c i) (d i)) : ∀ i, Step G (team g c i) (team g' d i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [team] using h
  · simpa [team] using hc j

private noncomputable abbrev target (p : G.Walk a b) (r : V) := p.getVert (shadow p r)

private lemma target_step (p : G.Walk a b) {r s : V} (h : Step G r s) :
    Step G (target p r) (target p s) :=
  vertices_step p (min_le_left ..) (min_le_left ..) (shadow_step p h)

private lemma target_eq (p : G.Walk a b) (geo : p.length = G.dist a b) {r : V}
    (hr : r ∈ p.support) : target p r = r := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  rw [target, shadow_on_path p geo i hi]

private lemma hit_guard (p : G.Walk a b) (geo : p.length = G.dist a b) {r g : V}
    (aligned : Step G g (target p r)) (hr : r ∈ p.support) (c : Fin k → V) :
    ∃ t, CatchesWithin G (k+1) t (team g c) r := by
  have hg : Step G g r := target_eq p geo hr ▸ aligned
  exact ⟨1, Or.inr ⟨team r c, team_step hg (fun _ => Or.inl rfl), Or.inl ⟨0, rfl⟩⟩⟩

/-- The residual component uses distances within its own induced graph. -/
abbrev Outside (p : G.Walk a b) := G.induce {x : V | x ∉ p.support}

private abbrev embed {p : G.Walk a b} {C : (Outside p).ConnectedComponent} (v : C) : V :=
  v.val.val

private lemma embed_step {p : G.Walk a b} {C : (Outside p).ConnectedComponent} {v w : C}
    (h : Step C.toSimpleGraph v w) : Step G (embed v) (embed w) := by
  rcases h with rfl | adj
  · exact Or.inl rfl
  · exact Or.inr adj

private lemma reply {p : G.Walk a b} {C : (Outside p).ConnectedComponent} (v : C)
    {r : V} (h : Step G (embed v) r) :
    r ∈ p.support ∨ ∃ w : C, embed w = r ∧ Step C.toSimpleGraph v w := by
  classical
  by_cases hr : r ∈ p.support
  · exact Or.inl hr
  right
  rcases h with he | adj
  · exact ⟨v, he, Or.inl rfl⟩
  · let s : {x : V | x ∉ p.support} := ⟨r, hr⟩
    have hadj : (Outside p).Adj v.val s := adj
    exact ⟨⟨s, C.mem_supp_of_adj_mem_supp v.property hadj⟩, rfl, Or.inr hadj⟩

/-- Once the remaining team occupies local cop positions, it can follow a
winning strategy inside the component. Any attempted exit gives the guard
a capture on its next turn. -/
private lemma play_inside [Fintype V] {p : G.Walk a b} (geo : p.length = G.dist a b)
    {C : (Outside p).ConnectedComponent} {t : ℕ} {c : Fin k → C} {r : C}
    (win : CatchesWithin C.toSimpleGraph k t c r) {g : V}
    (aligned : Step G g (target p (embed r))) :
    ∃ m, CatchesWithin G (k+1) m (team g (fun i => embed (c i))) (embed r) := by
  induction t generalizing c r g with
  | zero =>
    obtain ⟨i, hi⟩ := win
    exact ⟨0, i.succ, by simpa [team] using congrArg embed hi⟩
  | succ t ih =>
    rcases win with ⟨i, hi⟩ | ⟨d, hd, ⟨i, hi⟩ | cont⟩
    · exact ⟨0, i.succ, by simpa [team] using congrArg embed hi⟩
    · refine ⟨1, Or.inr ⟨team (target p (embed r)) (fun j => embed (d j)),
        team_step aligned (fun j => embed_step (hd j)), Or.inl ⟨i.succ, ?_⟩⟩⟩
      simpa [team] using congrArg embed hi
    · apply advance (team_step aligned (fun j => embed_step (hd j)))
      intro s hs
      have ready := target_step p hs
      obtain hpath | ⟨w, rfl, hw⟩ := reply r hs
      · exact hit_guard p geo ready hpath _
      · exact ih (cont w hw) ready

end Meyniel.Guard

namespace Meyniel.Guard

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V} {k : ℕ}

/-- Once the guard has synchronized, the other cops can travel along any
fixed routes in the full graph. The robber can enter the boundary during
deployment, in which event the guard immediately finishes the game. -/
private lemma deploy [Fintype V] {p : G.Walk a b} (geo : p.length = G.dist a b)
    {C : (Outside p).ConnectedComponent} (route : ℕ → Fin k → V)
    (moves : ∀ j i, Step G (route j i) (route (j+1) i)) (L : ℕ)
    (finish : ∀ (r : C) (g : V), Step G g (target p (embed r)) →
      ∃ t, CatchesWithin G (k+1) t (team g (route L)) (embed r)) :
    ∀ (remaining j : ℕ), j + remaining = L → ∀ (r : C) (g : V),
      Step G g (target p (embed r)) →
      ∃ t, CatchesWithin G (k+1) t (team g (route j)) (embed r) := by
  intro remaining
  induction remaining with
  | zero =>
    intro j hj
    have e : j = L := by omega
    subst j
    exact finish
  | succ m ih =>
    intro j hj r g hg
    apply advance (team_step hg (moves j))
    intro s hs
    have ready := target_step p hs
    obtain hpath | ⟨w, rfl, _⟩ := reply r hs
    · exact hit_guard p geo ready hpath _
    · exact ih (j+1) (by omega) w _ ready

private lemma walk_step (w : G.Walk a b) (j : ℕ) :
    Step G (w.getVert j) (w.getVert (j+1)) := by
  by_cases hj : j < w.length
  · exact Or.inr (w.adj_getVert_succ hj)
  · exact Or.inl ((w.getVert_of_length_le (by omega)).trans
      (w.getVert_of_length_le (by omega)).symm)

private lemma start_in_component [Fintype V] (conn : G.Connected) {p : G.Walk a b}
    (geo : p.length = G.dist a b) {C : (Outside p).ConnectedComponent}
    (win : WinsWith C.toSimpleGraph k) (r : C) (g : V) (ready : Step G g (target p (embed r))) :
    ∃ t, CatchesWithin G (k+1) t (team g (fun _ => a : Fin k → V)) (embed r) := by
  classical
  obtain ⟨c, hc⟩ := win
  let ws (i : Fin k) : G.Walk a (embed (c i)) := (conn a (embed (c i))).some
  let L := Finset.univ.sup (fun i => (ws i).length)
  let route (j : ℕ) (i : Fin k) := (ws i).getVert j
  have endroute : route L = (fun i => embed (c i)) := by
    funext i
    exact (ws i).getVert_of_length_le (Finset.le_sup (f := fun i => (ws i).length) (Finset.mem_univ i))
  have start : route 0 = (fun _ => a) := by funext i; simp [route]
  have finish : ∀ (s : C) (u : V), Step G u (target p (embed s)) →
      ∃ t, CatchesWithin G (k+1) t (team u (route L)) (embed s) := by
    intro s u hu
    rw [endroute]
    obtain ⟨t, ht⟩ := hc s
    exact play_inside geo ht hu
  rw [← start]
  exact deploy geo route (fun j i => walk_step (ws i) j) L finish L 0 (by omega) r g ready

private lemma acquire [Fintype V] (p : G.Walk a b) (tail : Fin k → V)
    (finish : ∀ r g, Step G g (target p r) → ∃ t, CatchesWithin G (k+1) t (team g tail) r) :
    ∀ (fuel i : ℕ), i ≤ p.length → p.length ≤ i + fuel → ∀ r, i ≤ shadow p r + 1 →
      ∃ t, CatchesWithin G (k+1) t (team (p.getVert i) tail) r := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi hf r hnear
    apply finish
    apply vertices_step p hi (min_le_left ..)
    have : shadow p r ≤ p.length := min_le_left .. 
    exact ⟨hnear, show shadow p r ≤ i + 1 by omega⟩
  | succ m ih =>
    intro i hi hf r hnear
    by_cases ready : shadow p r ≤ i + 1
    · exact finish _ _ (vertices_step p hi (min_le_left ..) ⟨hnear, ready⟩)
    · have hbound : shadow p r ≤ p.length := min_le_left ..
      have hadj : G.Adj (p.getVert i) (p.getVert (i+1)) := p.adj_getVert_succ (by omega)
      apply advance (team_step (Or.inr hadj) (fun _ => Or.inl rfl))
      intro s hs
      have hstep := shadow_step p hs
      exact ih (i+1) (by omega) (by omega) s (by omega)

/-- One geodesic guard plus a team that wins in each possible residual
component wins in the full graph. The team starts together before the robber
is placed. The winning component and the routes to its starts are chosen
only after the guard acquires its projection. -/
theorem wins_with_guard [Fintype V] (conn : G.Connected) (p : G.Walk a b)
    (geo : p.length = G.dist a b)
    (win : ∀ C : (Outside p).ConnectedComponent, WinsWith C.toSimpleGraph k) :
    WinsWith G (k+1) := by
  classical
  let tail : Fin k → V := fun _ => a
  refine ⟨team a tail, fun r => ?_⟩
  have finish : ∀ s g, Step G g (target p s) →
      ∃ t, CatchesWithin G (k+1) t (team g tail) s := by
    intro s g hs
    by_cases hp : s ∈ p.support
    · exact hit_guard p geo hs hp tail
    · let v : {x : V | x ∉ p.support} := ⟨s, hp⟩
      let C := (Outside p).connectedComponentMk v
      let w : C := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
      exact start_in_component conn geo (win C) w g hs
  simpa only [Walk.getVert_zero] using acquire p tail finish p.length 0 (by omega)
    (by omega) r (by omega)

end Meyniel.Guard

namespace Meyniel.Guard

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} {a b : V}

private lemma keep_extra {k t : ℕ} {c : Fin k → V} {r : V}
    (h : CatchesWithin G k t c r) (extra : V) : CatchesWithin G (k+1) t (team extra c) r := by
  induction t generalizing c r with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i.succ, by simpa [team] using hi⟩
  | succ t ih =>
    rcases h with ⟨i, hi⟩ | ⟨d, hd, ⟨i, hi⟩ | cont⟩
    · exact Or.inl ⟨i.succ, by simpa [team] using hi⟩
    · exact Or.inr ⟨team extra d, team_step (Or.inl rfl) hd, Or.inl ⟨i.succ, by simpa [team] using hi⟩⟩
    · exact Or.inr ⟨team extra d, team_step (Or.inl rfl) hd, Or.inr (fun s hs => ih (cont s hs))⟩

theorem winsWith_more [Nonempty V] {k m : ℕ} (hm : k ≤ m) (w : WinsWith G k) : WinsWith G m := by
  classical
  induction m, hm using Nat.le_induction with
  | base => exact w
  | succ j _ ih =>
    obtain ⟨c, hc⟩ := ih
    let extra : V := Classical.arbitrary V
    refine ⟨team extra c, fun r => ?_⟩
    obtain ⟨t, ht⟩ := hc r
    exact ⟨t, keep_extra ht extra⟩

/-- A surviving component excludes every vertex of the guarded path, even
when deletion has removed further components as well. -/
lemma component_card_add_path_le [Fintype V] [DecidableEq V] (p : G.Walk a b)
    (C : (Outside p).ConnectedComponent) [Fintype C] :
    Fintype.card C + p.support.toFinset.card ≤ Fintype.card V := by
  classical
  have hcard : Fintype.card C ≤ Fintype.card {x : V | x ∉ p.support} :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hsize : Fintype.card {x : V | x ∈ p.support} = p.support.toFinset.card :=
    Fintype.card_of_subtype _ (by simp)
  have hle : p.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  have compl : Fintype.card {x : V | x ∉ p.support} = Fintype.card V - Fintype.card {x : V | x ∈ p.support} :=
    @Fintype.card_subtype_compl V _ (fun x => x ∈ p.support)
      (inferInstanceAs (Fintype ↑({x : V | x ∈ p.support} : Set V)))
      (inferInstanceAs (Fintype ↑({x : V | x ∉ p.support} : Set V)))
  rw [compl, hsize] at hcard
  omega

/-- With a uniform budget K for connected graphs of diameter at most D and
order at most N, an arbitrary connected graph in that order range needs at
most K plus ⌊|V|/D⌋ cops. Each new guard consumes at least D vertices.
The proof recursively restarts inside the intrinsic residual graph. -/
theorem diameter_reduction [Fintype V] (conn : G.Connected) {N K D : ℕ}
    (hsize : Fintype.card V ≤ N) (hD : 0 < D)
    (hsmall : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), H.Connected →
      Fintype.card W ≤ N → H.diam ≤ D → WinsWith H K) :
    WinsWith G (K + Fintype.card V / D) := by
  classical
  have all : ∀ m : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.Connected → Fintype.card W = m → m ≤ N → WinsWith H (K + m / D) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W _ H hc hm hmN
      letI : Nonempty W := hc.nonempty
      by_cases hd : H.diam ≤ D
      · exact winsWith_more (Nat.le_add_right K (m / D)) (hsmall W H hc (hm.le.trans hmN) hd)
      obtain ⟨u, v, p, geo, _, hp⟩ := exists_diametral_guard_path hc
      have cardP : p.support.toFinset.card ≤ Fintype.card W := Finset.card_le_univ _
      have one : 1 ≤ m / D := (Nat.le_div_iff_mul_le hD).mpr (by simpa using (show D ≤ m by omega))
      have w : WinsWith H ((K + (m / D - 1)) + 1) := by
        apply wins_with_guard hc p geo
        intro C
        letI : Fintype C := Fintype.ofFinite C
        letI : Nonempty C := C.connected_toSimpleGraph.nonempty
        have dec := component_card_add_path_le p C
        have less : Fintype.card C < m := by omega
        have sub := ih (Fintype.card C) less C C.toSimpleGraph C.connected_toSimpleGraph rfl (by omega)
        have addD : Fintype.card C + D ≤ m := by omega
        have ddiv : Fintype.card C / D + 1 ≤ m / D := by
          rw [← Nat.add_div_right _ hD]
          exact Nat.div_le_div_right addD
        exact winsWith_more (by omega) sub
      exact winsWith_more (by omega) w
  exact all (Fintype.card V) V G conn rfl hsize

end Meyniel.Guard
end Meyniel_Guard
-- === END Meyniel.Guard ===

-- === BEGIN Meyniel.Optimize ===
section Meyniel_Optimize

/-! # Balancing the two teams -/

namespace Meyniel

/-- A global logarithmic factor can be absorbed in any fixed positive power. -/
theorem log_two_mul_le {x e : ℝ} (hx : 1 ≤ x) (he : 0 < e) :
    Real.log (2*x) ≤ (1+1/e) * x ^ e := by
  have hxp : 0 < x := by linarith
  rw [Real.log_mul (by norm_num) hxp.ne']
  have ht : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have h1 := Real.one_le_rpow hx he.le
  have he' := Real.log_le_rpow_div hxp.le he
  rw [add_mul, one_mul, one_div_mul_eq_div]
  linarith

theorem diamThreshold_pos {N : ℕ} (hN : 1 ≤ N) : 0 < diamThreshold N := by
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos (by linarith))

/-- An explicit universal constant; the conservative rounding covers small graphs too. -/
theorem budget_add_guards_le {N : ℕ} (hN : 1 ≤ N) :
    ((budget N (horizon N (diamThreshold N)) + N / diamThreshold N : ℕ) : ℝ) ≤
      31 * (N:ℝ) ^ (3/4:ℝ) * Real.log (2*N) := by
  let x : ℝ := N
  let L := Real.log (2*x)
  let a := x ^ (1/4:ℝ)
  let b := x ^ (3/4:ℝ)
  let D := diamThreshold N
  let T := horizon N D
  have hx : 1 ≤ x := by change (1:ℝ) ≤ (N:ℝ); exact_mod_cast hN
  have hxp : 0 < x := by linarith
  have ha : 1 ≤ a := Real.one_le_rpow hx (by norm_num)
  have hb : 1 ≤ b := Real.one_le_rpow hx (by norm_num)
  have hL : (1/2:ℝ) ≤ L := by
    have h : Real.log 2 ≤ Real.log (2*x) := Real.log_le_log (by norm_num) (by linarith)
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hLp : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ L := Real.log_le_log hxp (by linarith)
  have hla : L ≤ 5*a := by
    have h := log_two_mul_le (e := (1/4:ℝ)) hx (by norm_num)
    norm_num at h
    exact h
  have hDp : 0 < (D:ℝ) := by exact_mod_cast diamThreshold_pos hN
  have hlo : a ≤ D * L := (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi : (D:ℝ)*L ≤ 6*a := by
    have he : (D:ℝ) < a/L+1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hLp.le)
    have hm := mul_lt_mul_of_pos_right he hLp
    rw [add_mul, div_mul_cancel₀ _ hLp.ne', one_mul] at hm
    linarith
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2pos : 0 < Real.log 2 := by linarith
  have htime : (T:ℝ)+1 ≤ 14*a := by
    have ht : (T:ℝ) < (D:ℝ)*Real.log x/Real.log 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hDp.le hlog0) h2pos.le)
    have he : (D:ℝ)*Real.log x/Real.log 2 ≤ 12*a := by
      apply (div_le_iff₀ h2pos).mpr
      have h12 : 6*a ≤ (12*a)*Real.log 2 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ a) (sub_nonneg.mpr h2)]
      exact ((mul_le_mul_of_nonneg_left hlog hDp.le).trans hhi).trans h12
    linarith
  have hsqrt : Real.sqrt (2*x) ≤ 2* Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg x)
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hprod : Real.sqrt x * a = b := by
    dsimp [a,b]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxp]
    norm_num
  have hab : b*a = x := by
    dsimp [a,b]
    rw [← Real.rpow_add hxp]
    norm_num
  have hbase : (1/2:ℝ) ≤ b*L := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) hLp.le]
  have hteam : (budget N T : ℝ) ≤ 30*b*L := by
    have hfl : (budget N T : ℝ) ≤ Real.sqrt (2*x) * ((T:ℝ)+1) * Real.log x + 1 := by
      dsimp [budget]
      push_cast
      gcongr
      apply Nat.floor_le
      positivity
    have hupper := mul_le_mul hsqrt htime (by positivity : (0:ℝ) ≤ T+1)
      (by positivity : 0 ≤ 2 * Real.sqrt x)
    have hmore := mul_le_mul hupper hlog hlog0 (by positivity : 0 ≤ (2 * Real.sqrt x) * (14*a))
    have he : (2 * Real.sqrt x) * (14*a) = 28*b := by rw [← hprod]; ring
    rw [he] at hmore
    linarith
  have hguards : ((N / D : ℕ) : ℝ) ≤ b*L := by
    refine Nat.cast_div_le.trans ((div_le_iff₀ hDp).mpr ?_)
    have h := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ b)
    rw [hab] at h
    change x ≤ _
    linarith only [h, show b*((D:ℝ)*L) = b*L*D by ring]
  push_cast
  change (budget N T : ℝ) + ((N / D : ℕ) : ℝ) ≤ 31*b*L
  linarith

end Meyniel
end Meyniel_Optimize
-- === END Meyniel.Optimize ===

-- === BEGIN Meyniel.Interception ===
section Meyniel_Interception

/-! Finite counting and the diagonal estimate in the one-cop interception argument.
The type of walks below is the original nonempty family, with its uniform law.
-/ 

open Finset
open scoped BigOperators

namespace Meyniel.Interception

noncomputable section

variable {W K V : Type*}

def mean (s : Finset W) (f : W → ℝ) : ℝ :=
  (∑ w ∈ s, f w) / s.card

theorem mean_pos {s : Finset W} {f : W → ℝ} (hs : s.Nonempty)
    (hf : ∀ w ∈ s, 0 < f w) : 0 < mean s f := by
  exact div_pos (sum_pos hf hs) (by exact_mod_cast hs.card_pos)

theorem sum_log_le_card_mul_log_mean {s : Finset W} {f : W → ℝ} (hs : s.Nonempty)
    (hf : ∀ w ∈ s, 0 < f w) :
    ∑ w ∈ s, Real.log (f w) ≤ s.card * Real.log (mean s f) := by
  have hm := mean_pos hs hf
  have h := sum_le_sum (s := s) (fun w hw =>
    Real.log_le_sub_one_of_pos (div_pos (hf w hw) hm))
  have heq : ∑ w ∈ s, Real.log (f w / mean s f) =
      ∑ w ∈ s, Real.log (f w) - s.card * Real.log (mean s f) := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    exact sum_congr rfl fun w hw => Real.log_div (hf w hw).ne' hm.ne'
  have hr : ∑ w ∈ s, (f w / mean s f - 1) = 0 := by
    rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one, sub_eq_zero,
      div_eq_iff hm.ne']
    unfold mean
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    field_simp
  linarith [heq, hr]

def fiber [Fintype W] [DecidableEq K] (key : W → K) (k : K) : Finset W :=
  univ.filter fun w => key w = k

def blockMean [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ) (w : W) : ℝ :=
  mean (fiber key (key w)) f

theorem mem_own_fiber [Fintype W] [DecidableEq K] (key : W → K) (w : W) :
    w ∈ fiber key (key w) := by simp [fiber]

theorem blockMean_pos [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ)
    (hf : ∀ w, 0 < f w) (w : W) : 0 < blockMean key f w :=
  mean_pos ⟨w, mem_own_fiber key w⟩ (fun v _ => hf v)

theorem sum_by_fiber [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ) :
    ∑ k ∈ univ.image key, ∑ w ∈ fiber key k, f w = ∑ w, f w := by
  classical
  exact sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem key hw) f

theorem block_log_le [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ)
    (hf : ∀ w, 0 < f w) :
    ∑ w, Real.log (f w) ≤ ∑ w, Real.log (blockMean key f w) := by
  classical
  rw [← sum_by_fiber key (fun w => Real.log (f w)),
    ← sum_by_fiber key (fun w => Real.log (blockMean key f w))]
  apply sum_le_sum
  intro k hk
  obtain ⟨w, _, rfl⟩ := mem_image.mp hk
  let s := fiber key (key w)
  have hs : s.Nonempty := ⟨w, mem_own_fiber key w⟩
  calc
    _ ≤ s.card * Real.log (mean s f) :=
      sum_log_le_card_mul_log_mean hs (fun v _ => hf v)
    _ = ∑ v ∈ s, Real.log (mean s f) := by simp
    _ = _ := sum_congr rfl fun v hv => by
      have h : key v = key w := (mem_filter.mp hv).2
      simp [blockMean, h, s]

def logMean [Fintype W] (f : W → ℝ) : ℝ := mean univ (fun w => Real.log (f w))

theorem logMean_le_log_mean [Fintype W] [Nonempty W] {f : W → ℝ} (hf : ∀ w, 0 < f w) :
    logMean f ≤ Real.log (mean univ f) := by
  have h := sum_log_le_card_mul_log_mean (s := univ) univ_nonempty (fun w _ => hf w)
  unfold logMean mean
  apply (div_le_iff₀ (by exact_mod_cast (univ_nonempty : (univ : Finset W).Nonempty).card_pos)).2
  simpa [mean, mul_comm] using h

theorem logMean_update [Fintype W] [Nonempty W] [DecidableEq K]
    (key : W → K) (old new pre post : W → ℝ)
    (ho : ∀ w, 0 < old w) (hp : ∀ w, 0 < pre w) (hq : ∀ w, 0 < post w)
    (hu : ∀ w, new w = blockMean key old w * pre w / post w) :
    logMean old + (logMean pre - logMean post) ≤ logMean new := by
  have he : ∀ w, Real.log (new w) =
      Real.log (blockMean key old w) + Real.log (pre w) - Real.log (post w) := by
    intro w
    rw [hu w, Real.log_div (mul_pos (blockMean_pos key old ho _) (hp _)).ne' (hq _).ne',
      Real.log_mul (blockMean_pos key old ho _).ne' (hp _).ne']
  simp only [logMean, mean, he, sum_sub_distrib, sum_add_distrib]
  simp only [sub_div, add_div]
  have hh := div_le_div_of_nonneg_right (block_log_le key old ho) (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)
  linarith


theorem logMean_mono [Fintype W] {f g : W → ℝ} (hf : ∀ w, 0 < f w) (h : ∀ w, f w ≤ g w) :
    logMean f ≤ logMean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun w _ => Real.log_le_log (hf w) (h w)))
    (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)

theorem logMean_bellman [Fintype W] [Nonempty W] [DecidableEq K]
    (key : W → K) (old new pre post : W → ℝ)
    (hn : ∀ w, 0 < new w) (hp : ∀ w, 0 < pre w) (hq : ∀ w, 0 < post w)
    (hu : ∀ w, blockMean key (fun z => new z * pre z / post z) w ≤ old w) :
    logMean new + (logMean pre - logMean post) ≤ logMean old := by
  let f := fun z => new z * pre z / post z
  have hf : ∀ z, 0 < f z := fun z => div_pos (mul_pos (hn z) (hp z)) (hq z)
  calc
    logMean new + (logMean pre - logMean post) = logMean f := by
      have he (w : W) : Real.log (f w) = Real.log (new w) + Real.log (pre w) - Real.log (post w) := by
        dsimp only [f]
        rw [Real.log_div (mul_pos (hn w) (hp w)).ne' (hq w).ne',
          Real.log_mul (hn w).ne' (hp w).ne']
      simp only [logMean, mean, he, sum_sub_distrib, sum_add_distrib, sub_div, add_div]
      ring
    _ ≤ logMean (blockMean key f) := div_le_div_of_nonneg_right (block_log_le key f hf)
      (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)
    _ ≤ _ := logMean_mono (blockMean_pos key f hf) hu

/-- Marginal mass of the tagged walk's own vertex at one specified time. -/
def frequency [Fintype W] [DecidableEq V] (position : W → V) (w : W) : ℝ :=
  ((fiber position (position w)).card : ℝ) / Fintype.card W

theorem frequency_pos [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) (w : W) :
    0 < frequency position w := by
  have hc := (show (fiber position (position w)).Nonempty from ⟨w, mem_own_fiber position w⟩).card_pos
  exact div_pos (by exact_mod_cast hc) (by exact_mod_cast Fintype.card_pos (α := W))

theorem mean_inv_frequency [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) :
    mean univ (fun w => (frequency position w)⁻¹) = (univ.image position).card := by
  classical
  have h (v : V) (hv : v ∈ univ.image position) :
      ∑ w ∈ fiber position v, (frequency position w)⁻¹ = Fintype.card W := by
    obtain ⟨w, _, rfl⟩ := mem_image.mp hv
    let s := fiber position (position w)
    have hs : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (show s.Nonempty from ⟨w, mem_own_fiber position w⟩).card_pos.ne'
    calc
      _ = ∑ _v ∈ s, ((s.card : ℝ) / Fintype.card W)⁻¹ := by
        apply sum_congr rfl
        intro v hv
        have hh : position v = position w := (mem_filter.mp hv).2
        simp [frequency, hh, s]
      _ = _ := by simp only [sum_const, nsmul_eq_mul, inv_div]; field_simp
  unfold mean
  rw [← sum_by_fiber position (fun w => (frequency position w)⁻¹), sum_congr rfl h]
  have hw : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp [hw]

theorem logMean_frequency_ge [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) :
    -Real.log ((univ.image position).card) ≤ logMean (frequency position) := by
  have h := logMean_le_log_mean (fun w => inv_pos.mpr (frequency_pos position w))
  rw [mean_inv_frequency] at h
  simpa [logMean, mean, Real.log_inv, Finset.sum_neg_distrib, neg_div, neg_le] using h

/-- Total along a diagonal, from time zero to the meeting row. -/
def diagonalSum (b : ℕ) (a : ℕ → ℕ → ℝ) :=
  ∑ t ∈ range (b / 2 + 1), a t (b - t)

theorem backward_telescope (b : ℕ) (a : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (h : ∀ t ≤ b / 2, v (t+1) + a t (b-t) ≤ v t) :
    diagonalSum b a ≤ v 0 - v (b / 2 + 1) := by
  unfold diagonalSum
  rw [← sum_range_sub' v]
  apply sum_le_sum
  intro t ht
  have := h t (by simpa using ht)
  linarith

theorem forward_telescope (b : ℕ) (a : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (h : ∀ t ≤ b / 2, v t + a t (b-t) ≤ v (t+1)) :
    diagonalSum b a ≤ v (b / 2 + 1) - v 0 := by
  unfold diagonalSum
  rw [← sum_range_sub v]
  apply sum_le_sum
  intro t ht
  have := h t (by simpa using ht)
  linarith

private def cells (T : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2*T+1)) ×ˢ (range (2*T+1))).filter fun q => q.1 ≤ q.2 ∧ q.1+q.2 ≤ 2*T

private theorem mem_cells {T t j : ℕ} :
    (t,j) ∈ cells T ↔ t ≤ j ∧ t+j ≤ 2*T := by
  simp only [cells, mem_filter, mem_product, mem_range]
  omega

theorem sum_diagonals_eq_sum_columns (T : ℕ) (a : ℕ → ℕ → ℝ) :
    ∑ b ∈ range (2*T+1), diagonalSum b a =
      ∑ j ∈ range (2*T+1), ∑ t ∈ range (min j (2*T-j)+1), a t j := by
  classical
  let f := fun q : ℕ × ℕ => a q.1 q.2
  have hdiag (b : ℕ) (hb : b ∈ range (2*T+1)) : diagonalSum b a =
      ∑ q ∈ (cells T).filter (fun q => q.1+q.2=b), f q := by
    apply sum_bij (fun t _ => (t,b-t))
    · intro t ht
      simp only [mem_range] at ht hb
      simp only [mem_filter, mem_cells]
      omega
    · intro i _ j _ hij
      exact congrArg Prod.fst hij
    · rintro ⟨t,j⟩ h
      simp only [mem_filter, mem_cells] at h
      exact ⟨t, by simp only [mem_range]; omega, by exact Prod.ext rfl (by change b - t = j; omega)⟩
    · intros; rfl
  have hcol (j : ℕ) (hj : j ∈ range (2*T+1)) :
      ∑ t ∈ range (min j (2*T-j)+1), a t j =
      ∑ q ∈ (cells T).filter (fun q => q.2=j), f q := by
    apply sum_bij (fun t _ => (t,j))
    · intro t ht
      have hm : t ≤ min j (2*T-j) := by simpa using ht
      have h₁ := (le_min_iff.mp hm).1
      have h₂ := (le_min_iff.mp hm).2
      have hj' : j ≤ 2*T := by simpa using hj
      apply mem_filter.mpr
      exact ⟨mem_cells.mpr ⟨h₁, by omega⟩, rfl⟩
    · intro i _ k _ hik
      exact congrArg Prod.fst hik
    · rintro ⟨t,j'⟩ h
      simp only [mem_filter, mem_cells] at h
      exact ⟨t, by simp only [mem_range]; omega, by exact Prod.ext rfl h.2.symm⟩
    · intros; rfl
  rw [sum_congr rfl hdiag, sum_congr rfl hcol]
  have hd (q : ℕ × ℕ) (hq : q ∈ cells T) : q.1+q.2 ∈ range (2*T+1) := by
    obtain ⟨t,j⟩ := q
    simp only [mem_cells] at hq
    simp only [mem_range]
    omega
  have hc (q : ℕ × ℕ) (hq : q ∈ cells T) : q.2 ∈ range (2*T+1) := by
    obtain ⟨t,j⟩ := q
    simp only [mem_cells] at hq
    simp only [mem_range]
    omega
  rw [sum_fiberwise_of_maps_to hd f, sum_fiberwise_of_maps_to hc f]


/-- The global log bound resulting from summing the costs of revealing each
column. Once the original column is constant its log marginal contributes zero. -/
theorem summed_diagonal_lower (T cut : ℕ) (L : ℝ) (q : ℕ → ℕ → ℝ)
    (hL : 0 ≤ L) (hfirst : ∀ j ≤ 2*T, -L ≤ q 0 j)
    (hhome : ∀ j ≤ 2*T, cut ≤ j → 0 ≤ q 0 j)
    (hlast : ∀ j ≤ 2*T, q (min j (2*T-j)+1) j ≤ 0) :
    -(cut : ℝ) * L ≤ ∑ b ∈ range (2*T+1),
      diagonalSum b (fun t j => q t j - q (t+1) j) := by
  rw [sum_diagonals_eq_sum_columns]
  simp only [sum_range_sub']
  let J := (range (2*T+1)).filter (fun j => j < cut)
  have hc : J.card ≤ cut := by
    rw [← card_range cut]
    exact card_le_card (fun j hj => mem_range.mpr (mem_filter.mp hj).2)
  have hsum : (∑ j ∈ range (2*T+1), if j < cut then -L else 0) = J.card * (-L) := by
    rw [← sum_filter]
    simp [J]
  calc
    _ ≤ J.card * (-L) := by
      have hcr : (J.card : ℝ) ≤ cut := by exact_mod_cast hc
      nlinarith [mul_le_mul_of_nonneg_right hcr hL]
    _ = _ := hsum.symm
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have hj' : j ≤ 2*T := by simpa using hj
      by_cases h : j < cut
      · simp only [h, if_true]
        linarith [hfirst j hj', hlast j hj']
      · simpa [h] using (sub_nonneg.mpr ((hlast j hj').trans (hhome j hj' (by omega))))

/-- Some diagonal has the required success fraction as soon as its log fraction
dominates the sum of the one-step changes in log weight along that diagonal. -/
theorem exists_good_diagonal (T d n : ℕ) (q : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (hn : 1 ≤ n) (ht : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (hs : ∀ b ≤ 2*T, 0 < s b)
    (hfirst : ∀ j ≤ 2*T, -Real.log n ≤ q 0 j)
    (hhome : ∀ j ≤ 2*T, T+d ≤ j → 0 ≤ q 0 j)
    (hlast : ∀ j ≤ 2*T, q (min j (2*T-j)+1) j ≤ 0)
    (hdiag : ∀ b ≤ 2*T,
      diagonalSum b (fun t j => q t j - q (t+1) j) ≤ Real.log (s b)) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have hln := Real.log_nonneg hn'
  have hl2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have hq := summed_diagonal_lower T (T+d) (Real.log n) q hln hfirst hhome hlast
  have hsum := hq.trans (sum_le_sum (s := range (2*T+1))
    (fun b hb => hdiag b (by simpa using hb)))
  by_contra! hc
  have hlt := sum_lt_sum_of_nonempty (s := range (2*T+1))
    (show (range (2*T+1)).Nonempty from ⟨0, mem_range.mpr (by omega)⟩)
    (fun b hb => Real.strictMonoOn_log (hs b (by simpa using hb))
      (show 0 < 1 / Real.sqrt (2*(n:ℝ)) by positivity) (hc b (by simpa using hb)))
  rw [sum_const, nsmul_eq_mul, card_range] at hlt
  rw [one_div, Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hnpos.ne'] at hlt
  push_cast at hsum hlt
  nlinarith

/-- Converting the paper's natural-valued inequality to the logarithmic
initialization used by the diagonal estimate. -/
theorem horizon_log_of_pow {d T n : ℕ} (hn : 0 < n) (h : n^d ≤ 2^T) :
    (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2 := by
  have h' : (n : ℝ)^d ≤ (2 : ℝ)^T := by exact_mod_cast h
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by exact_mod_cast hn) d) h'


@[simp] theorem logMean_one [Fintype W] : logMean (fun _ : W => 1) = 0 := by
  simp [logMean, mean]

theorem logMean_nonpos [Fintype W] (f : W → ℝ) (h : ∀ w, 0 < f w ∧ f w ≤ 1) :
    logMean f ≤ 0 := by
  exact (logMean_mono (fun w => (h w).1) (fun w => (h w).2)).trans_eq logMean_one

theorem logMean_frequency_ge_of_card_le [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    (position : W → V) (n : ℕ) (hn : Fintype.card V ≤ n) :
    -Real.log n ≤ logMean (frequency position) := by
  have hcard : (univ.image position).card ≤ n := (card_le_univ _).trans hn
  have hnz : 0 < (univ.image position).card :=
    (univ_nonempty.image position).card_pos
  have hl := Real.log_le_log (show 0 < (((univ.image position).card : ℕ) : ℝ) by exact_mod_cast hnz)
    (show (((univ.image position).card : ℕ) : ℝ) ≤ n by exact_mod_cast hcard)
  exact (neg_le_neg hl).trans (logMean_frequency_ge position)

theorem frequency_of_constant [Fintype W] [Nonempty W] [DecidableEq V] {position : W → V}
    (h : ∀ v w, position v = position w) (w : W) : frequency position w = 1 := by
  have hs : fiber position (position w) = univ := by
    ext v
    simp [fiber, h v w]
  simp [frequency, hs, Fintype.card_ne_zero]

/-- Supply a cell-by-cell Bellman bound and a terminal condition, and obtain a
good diagonal. The columns and their marginal frequencies are ordinary maps
on the original finite family of walks. -/
theorem exists_good_of_bellman [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    [DecidableEq K] (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (position : ℕ → W → V) (p v : ℕ → ℕ → W → ℝ) (key : ℕ → ℕ → W → K)
    (s : ℕ → ℝ)
    (hpos : ∀ t j w, 0 < p t j w ∧ p t j w ≤ 1)
    (hzero : ∀ j, p 0 j = frequency (position j))
    (hhome : ∀ j, T+d ≤ j → ∀ x y, position j x = position j y)
    (hvend : ∀ b ≤ 2*T, v b (b/2+1) = fun _ => 1)
    (hv : ∀ b ≤ 2*T, ∀ t ≤ b/2+1, ∀ w, 0 < v b t w)
    (hstep : ∀ b ≤ 2*T, ∀ t ≤ b/2, ∀ w,
      blockMean (key t (b-t))
        (fun z => v b (t+1) z * p t (b-t) z / p (t+1) (b-t) z) w ≤ v b t w)
    (hstart : ∀ b ≤ 2*T, mean univ (v b 0) ≤ s b) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  apply exists_good_diagonal T d n (fun t j => logMean (p t j)) s hn hT
  · intro b hb
    exact (mean_pos univ_nonempty (fun w _ => hv b hb 0 (by omega) w)).trans_le (hstart b hb)
  · intro j _
    rw [hzero]
    exact logMean_frequency_ge_of_card_le _ _ hsize
  · intro j _ hj
    rw [hzero]
    have hh := funext (frequency_of_constant (hhome j hj))
    rw [hh, logMean_one]
  · intro j _
    exact logMean_nonpos _ (hpos _ _)
  · intro b hb
    have ht := backward_telescope b (fun t j => logMean (p t j) - logMean (p (t+1) j))
      (fun t => logMean (v b t))
      (fun t hd => logMean_bellman (key t (b-t)) _ _ _ _ (hv b hb (t+1) (by omega))
        (fun w => (hpos _ _ w).1) (fun w => (hpos _ _ w).1) (hstep b hb t hd))
    rw [hvend b hb, logMean_one, sub_zero] at ht
    have hp := hv b hb 0 (by omega)
    exact ht.trans ((logMean_le_log_mean hp).trans
      (Real.log_le_log (mean_pos univ_nonempty (fun w _ => hp w)) (hstart b hb)))


@[simp] theorem logMean_const [Fintype W] [Nonempty W] (r : ℝ) :
    logMean (fun _ : W => r) = Real.log r := by
  simp [logMean, mean, Fintype.card_ne_zero]

/-- For one diagonal it is enough to bound the first backward value by the
success rate. Positivity of every intermediate value follows from the recursion. -/
theorem bellman_diagonal [Fintype W] [Nonempty W] [DecidableEq K]
    (b : ℕ) (p : ℕ → ℕ → W → ℝ) (v : ℕ → W → ℝ) (key : ℕ → W → K) (s : ℝ)
    (hp : ∀ t j w, 0 < p t j w)
    (hend : ∀ w, v (b/2+1) w = 1) (hstart : ∀ w, v 0 w ≤ s)
    (hstep : ∀ t ≤ b/2, ∀ w, blockMean (key t)
      (fun z => v (t+1) z * p t (b-t) z / p (t+1) (b-t) z) w ≤ v t w) :
    0 < s ∧ diagonalSum b (fun t j => logMean (p t j) - logMean (p (t+1) j)) ≤
      Real.log s := by
  have hv (t : ℕ) (ht : t ≤ b/2+1) : ∀ w, 0 < v t w := by
    induction ht using Nat.decreasingInduction with
    | self => intro w; rw [hend w]; norm_num
    | of_succ i hi ih =>
      intro w
      exact (blockMean_pos (key i) _
        (fun z => div_pos (mul_pos (ih z) (hp i (b-i) z)) (hp (i+1) (b-i) z)) w).trans_le
        (hstep i (by omega) w)
  have hv0 := hv 0 (by omega)
  constructor
  · let w : W := Classical.choice (inferInstance : Nonempty W)
    exact (hv0 w).trans_le (hstart w)
  · have ht := backward_telescope b (fun t j => logMean (p t j) - logMean (p (t+1) j))
      (fun t => logMean (v t))
      (fun t hd => logMean_bellman (key t) _ _ _ _ (hv (t+1) (by omega))
        (hp t (b-t)) (hp (t+1) (b-t)) (hstep t hd))
    rw [funext hend, logMean_one, sub_zero] at ht
    exact ht.trans ((logMean_mono hv0 hstart).trans_eq (logMean_const s))

/-- Direct bridge from a fixed-diagonal strategy and the actual column marginal
frequencies to a strategy attaining the claimed fraction. -/
theorem exists_good_from_diagonal [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (position : ℕ → W → V) (p : ℕ → ℕ → W → ℝ) (s : ℕ → ℝ)
    (hpos : ∀ t j w, 0 < p t j w ∧ p t j w ≤ 1)
    (hzero : ∀ j, p 0 j = frequency (position j))
    (hhome : ∀ j, T+d ≤ j → ∀ x y, position j x = position j y)
    (hdiag : ∀ b ≤ 2*T, 0 < s b ∧
      diagonalSum b (fun t j => logMean (p t j) - logMean (p (t+1) j)) ≤ Real.log (s b)) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  apply exists_good_diagonal T d n (fun t j => logMean (p t j)) s hn hT
    (fun b hb => (hdiag b hb).1)
  · intro j _
    rw [hzero]
    exact logMean_frequency_ge_of_card_le _ _ hsize
  · intro j _ hj
    rw [hzero, funext (frequency_of_constant (hhome j hj)), logMean_one]
  · intro j _
    exact logMean_nonpos _ (hpos _ _)
  · exact fun b hb => (hdiag b hb).2

end
end Meyniel.Interception
end Meyniel_Interception
-- === END Meyniel.Interception ===

-- === BEGIN Meyniel.Sampler ===
section Meyniel_Sampler

/-! # Deterministic backward interception on a family of walks

A cop can choose a different continuation for every revealed vertex. Maximizing
its capture count on each child prefix implements the backward sampling bound
with deterministic policies; the only randomness needed is the averaging over
the tagged walks in the given finite family.
-/

namespace Meyniel.Sampler

open Finset

variable {V W : Type*} {G : SimpleGraph V}

private def splicePos (x : V) (q : V → Policy G) (h : List V) : V :=
  match h.getLast? with
  | none => x
  | some r => (q r).pos h.dropLast

@[simp] private theorem splicePos_append (x : V) (q : V → Policy G) (h : List V) (r : V) :
    splicePos x q (h ++ [r]) = (q r).pos h := by
  simp [splicePos]

/-- After observing r, switch to its preselected continuation; all other choices
remain functions solely of the robber observations. -/
def splice (x : V) (q : V → Policy G) (legal : ∀ r, Step G x ((q r).pos [])) : Policy G where
  pos := splicePos x q
  legal := by
    intro y h
    induction h using List.reverseRecOn with
    | nil => exact legal y
    | append_singleton h r _ =>
      change Step G (splicePos x q (h ++ [r])) (splicePos x q ((y :: h) ++ [r]))
      simp only [splicePos_append]
      exact (q r).legal y h

@[simp] theorem splice_nil (x : V) (q : V → Policy G) (L) : (splice x q L).pos [] = x := rfl

@[simp] theorem splice_append (x : V) (q : V → Policy G) (L) (h : List V) (r : V) :
    (splice x q L).pos (h ++ [r]) = (q r).pos h := splicePos_append ..

private theorem hits_splice (x : V) (q : V → Policy G) (L) (r : V) :
    ∀ (w h : List V), Hits (splice x q L) (h ++ [r]) w ↔ Hits (q r) h w
  | [], _ => Iff.rfl
  | [v], h => by simp [Hits]
  | v :: z :: zs, h => by
    change ((_ = v) ∨ (splice x q L).pos ((v :: h) ++ [r]) = v ∨
      Hits (splice x q L) ((v :: h) ++ [r]) (z :: zs)) ↔ _
    rw [hits_splice x q L r (z :: zs) (v :: h)]
    rw [splice_append x q L (v :: h) r, splice_append x q L h r]
    rfl

/-- What is captured after revealing r and committing to q, including immediate
collision and the absence of a final cop turn on a singleton walk. -/
def stageHits (x r : V) (q : Policy G) : List V → Prop
  | [] => x = r
  | z :: zs => x = r ∨ q.pos [] = r ∨ Hits q [] (z :: zs)

theorem stageHits_splice (x r : V) (q : V → Policy G) (L) (w : List V) :
    Hits (splice x q L) [] (r :: w) ↔ stageHits x r (q r) w := by
  cases w with
  | nil => rfl
  | cons z zs =>
    change (x = r ∨ _ = r ∨ Hits (splice x q L) ([] ++ [r]) (z :: zs)) ↔ _
    rw [hits_splice]
    rfl

noncomputable def count (A : Finset W) (P : W → Prop) : ℕ := by
  classical exact (A.filter P).card

theorem count_le (A : Finset W) (P : W → Prop) : count A P ≤ A.card := by
  classical exact card_filter_le ..

private theorem exists_best {S : Type*} (witness : S) (f : S → ℕ) (cap : ℕ)
    (hle : ∀ q, f q ≤ cap) : ∃ q, ∀ z, f z ≤ f q := by
  have hb : BddAbove (Set.range f) := ⟨cap, by rintro _ ⟨s,rfl⟩; exact hle s⟩
  obtain ⟨q, hq⟩ := Nat.sSup_mem (s := Set.range f) ⟨f witness, witness, rfl⟩ hb
  exact ⟨q, fun z => hq ▸ le_csSup hb ⟨z,rfl⟩⟩

/-- An optimal single cop among all policies with the indicated initial vertex. -/
noncomputable def optimal (G : SimpleGraph V) (A : Finset W) (route : W → List V) (x : V) :
    {s : Policy G // s.pos [] = x} :=
  Classical.choose (exists_best (⟨Policy.stay G x, rfl⟩ : {s : Policy G // s.pos [] = x})
    (fun s => count A fun w => Hits s.1 [] (route w)) A.card (fun _ => count_le ..))

noncomputable def bestCount (G : SimpleGraph V) (A : Finset W) (route : W → List V) (x : V) : ℕ :=
  count A fun w => Hits (optimal G A route x).1 [] (route w)

theorem count_le_best (A : Finset W) (route : W → List V) (x : V) (q : Policy G) (hq : q.pos [] = x) :
    (count A fun w => Hits q [] (route w)) ≤ bestCount G A route x := by
  exact (Classical.choose_spec (exists_best (⟨Policy.stay G x, rfl⟩ : {s : Policy G // s.pos [] = x})
    (fun s => count A fun w => Hits s.1 [] (route w)) A.card (fun _ => count_le ..))) ⟨q,hq⟩

/-- The strategy selected for a child prefix can commit to any legal first move. -/
noncomputable def bestChild (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V) :
    {q : Policy G // Step G x (q.pos [])} :=
  Classical.choose (exists_best (⟨Policy.stay G x, Or.inl rfl⟩ : {s : Policy G // Step G x (s.pos [])})
    (fun q => count A fun w => stageHits x r q.1 (tail w)) A.card (fun _ => count_le ..))

noncomputable def childCount (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V) : ℕ :=
  count A fun w => stageHits x r (bestChild G A tail x r).1 (tail w)

theorem count_le_child (A : Finset W) (tail : W → List V) (x r : V) (q : Policy G)
    (hq : Step G x (q.pos [])) :
    (count A fun w => stageHits x r q (tail w)) ≤ childCount G A tail x r := by
  exact (Classical.choose_spec (exists_best (⟨Policy.stay G x, Or.inl rfl⟩ : {s : Policy G // Step G x (s.pos [])})
    (fun s => count A fun w => stageHits x r s.1 (tail w)) A.card (fun _ => count_le ..))) ⟨q,hq⟩

/-- Splitting the capture count among the possible revealed vertices is exact. -/
private theorem count_partition [Fintype V] [DecidableEq V] (A : Finset W) (obs : W → V) (P : W → Prop) :
    (∑ r, count (A.filter fun z => obs z = r) P) = count A P := by
  classical
  simpa only [count, Finset.card_filter] using Finset.sum_fiberwise A obs (fun z => if P z then 1 else (0:ℕ))

/-- Maximizing the first response independently at each possible revelation is
realizable by one policy starting at x, even for prefixes outside the family. -/
theorem sum_childCount_le_best [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset W)
    (obs : W → V) (tail : W → List V) (x : V) :
    (∑ r, childCount G (A.filter fun z => obs z = r) tail x r) ≤
      bestCount G A (fun z => obs z :: tail z) x := by
  classical
  let q := fun r => bestChild G (A.filter fun z => obs z = r) tail x r
  let s := splice x (fun r => (q r).1) (fun r => (q r).2)
  calc
    _ = ∑ r, count (A.filter fun z => obs z = r) (fun z => Hits s [] (obs z :: tail z)) := by
      apply Finset.sum_congr rfl; intro r _
      change ((A.filter _).filter _).card = ((A.filter _).filter _).card
      congr 1
      apply Finset.filter_congr
      intro w hw
      obtain ⟨_,hr⟩ := Finset.mem_filter.mp hw
      rw [hr]; exact (stageHits_splice x r (fun u => (q u).1) (fun u => (q u).2) (tail w)).symm
    _ = _ := count_partition A obs _
    _ ≤ _ := count_le_best A _ x s rfl

/-- Every compatible tag may propose its own legal backward move. The value
of each such proposal is bounded by the same best response for this child. -/
theorem best_next_le_child (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r y : V)
    (hxy : Step G x y) : bestCount G A tail y ≤ childCount G A tail x r := by
  classical
  let s := optimal G A tail y
  apply le_trans _ (count_le_child A tail x r s.1 (s.2.symm ▸ hxy))
  apply Finset.card_le_card; intro w hmem
  obtain ⟨ha,hw⟩ := Finset.mem_filter.mp hmem
  refine Finset.mem_filter.mpr ⟨ha,?_⟩
  change Hits s.1 [] (tail w) at hw
  cases H : tail w with
  | nil => simp [H,Hits] at hw
  | cons z zs => exact Or.inr (Or.inr (H ▸ hw))

/-- At a terminal entry every walk with the compatible revealed vertex is
captured, either immediately or on the next cop turn if there is one. -/
theorem all_le_child (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V)
    (hxy : Step G x r) (ht : ∀ w ∈ A, x = r ∨ tail w ≠ []) :
    A.card ≤ childCount G A tail x r := by
  classical
  apply le_trans _ (count_le_child A tail x r (Policy.stay G r) hxy)
  apply Finset.card_le_card
  intro w hw; apply Finset.mem_filter.mpr; refine ⟨hw, ?_⟩
  cases H : tail w with
  | nil => exact (ht w hw).resolve_right (not_not.mpr H)
  | cons z zs => exact Or.inr (Or.inl rfl)

/-- Each tag in one observed child is weighted by the inverse size of its
fiber. This permits the guesses for different tags to overlap arbitrarily. -/
theorem sum_div_fiber_le [Fintype V] [DecidableEq V] (M : Finset W) (obs : W → V)
    (a : W → ℝ) (c : V → ℕ) (h : ∀ w ∈ M, a w ≤ c (obs w)) :
    (∑ w ∈ M, a w / (M.filter fun z => obs z = obs w).card) ≤ ∑ r, (c r : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise M obs]
  apply Finset.sum_le_sum
  intro r _
  let B := M.filter fun z => obs z = r
  change (∑ w ∈ B, _) ≤ _
  calc
    _ ≤ ∑ _w ∈ B, (c r : ℝ) / B.card := by
      apply Finset.sum_le_sum; intro w hw
      obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hw
      rw [hr]; exact div_le_div_of_nonneg_right (hr ▸ h w hm) (Nat.cast_nonneg _)
    _ ≤ _ := by
      by_cases hb : B.Nonempty
      · have h0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hb
        simp only [Finset.sum_const, nsmul_eq_mul]; field_simp; exact le_rfl
      · simp [Finset.not_nonempty_iff_eq_empty.mp hb]

open Interception

/-- The observed prefix before reveal t (newest observation first). -/
def past (X : ℕ → W → V) : ℕ → W → List V
  | 0, _ => []
  | t+1, w => X t w :: past X t w

/-- Chronological, with exactly the real robber observations still available. -/
def remainder (X : ℕ → W → V) (T t : ℕ) (w : W) : List V :=
  List.ofFn (fun i : Fin (T+1-t) => X (t+i.val) w)

private theorem remainder_cons (X : ℕ → W → V) (T t : ℕ) (ht : t ≤ T) (w : W) :
    remainder X T t w = X t w :: remainder X T (t+1) w := by
  unfold remainder
  have hh : T+1-t = (T+1-(t+1))+1 := by omega
  conv_lhs => rw [hh]
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn; funext i; congr 1; simp [Fin.val_succ]; omega

variable [Fintype W] [DecidableEq V]

def oldPrefix (X : ℕ → W → V) (t : ℕ) (w : W) := fiber (past X t) (past X t w)

def key (X : ℕ → W → V) (t j : ℕ) (w : W) := (past X t w, X j w)

def tags (X : ℕ → W → V) (t j : ℕ) (w : W) := fiber (key X t j) (key X t j w)

noncomputable def conditional (X : ℕ → W → V) (t j : ℕ) (w : W) : ℝ :=
  ((tags X t j w).card : ℝ)/(oldPrefix X t w).card

private theorem mem_prefix {X : ℕ→W→V} {t : ℕ} {w z : W} :
    z ∈ oldPrefix X t w ↔ past X t z = past X t w := by simp [oldPrefix,fiber]

private theorem mem_tags {X : ℕ→W→V} {t j : ℕ} {w z : W} :
    z ∈ tags X t j w ↔ past X t z = past X t w ∧ X j z = X j w := by simp [tags,key,fiber]

private theorem prefix_pos (X : ℕ→W→V) (t : ℕ) (w : W) : 0 < ((oldPrefix X t w).card : ℝ) := by
  exact_mod_cast (show (oldPrefix X t w).Nonempty from ⟨w, mem_prefix.mpr rfl⟩).card_pos

private theorem tags_pos (X : ℕ→W→V) (t j : ℕ) (w : W) : 0 < ((tags X t j w).card : ℝ) := by
  exact_mod_cast (show (tags X t j w).Nonempty from ⟨w, mem_tags.mpr ⟨rfl,rfl⟩⟩).card_pos

theorem conditional_pos (X : ℕ→W→V) (t j : ℕ) (w : W) : 0 < conditional X t j w :=
  div_pos (tags_pos ..) (prefix_pos ..)

private theorem child_prefix {X : ℕ→W→V} {t j : ℕ} {w z : W} (hz : z ∈ tags X t j w) :
    (oldPrefix X t w).filter (fun y => X t y = X t z) = oldPrefix X (t+1) z := by
  ext u
  obtain ⟨hp,-⟩ := mem_tags.mp hz
  simp only [Finset.mem_filter, mem_prefix, past, List.cons.injEq]
  rw [hp]; tauto

private theorem child_tags {X : ℕ→W→V} {t j : ℕ} {w z : W} (hz : z ∈ tags X t j w) :
    (tags X t j w).filter (fun y => X t y = X t z) = tags X (t+1) j z := by
  ext u
  obtain ⟨hp,hx⟩ := mem_tags.mp hz
  simp only [Finset.mem_filter, mem_tags, past, List.cons.injEq]
  rw [hp,hx]; tauto

/-- At the fictitious row after the terminal entry the value is one. -/
noncomputable def value (G : SimpleGraph V) (X : ℕ→W→V) (T b t : ℕ) (w : W) : ℝ :=
  if t ≤ b/2 then (bestCount G (oldPrefix X t w) (remainder X T t) (X (b-t) w) : ℝ) /
    (oldPrefix X t w).card else 1

omit [DecidableEq V] in
private theorem step_symm {x y : V} (h : Step G x y) : Step G y x :=
  h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)

/-- The best number of continuations after one observed vertex dominates every
compatible tag's next value, including both types of terminal entry. -/
private theorem child_dominates (G : SimpleGraph V) (X : ℕ→W→V) (T b t j : ℕ)
    (hb : b ≤ 2*T) (ht : t ≤ b/2) (hj : j=b-t) (w z : W) (hz : z ∈ tags X t j w)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    value G X T b (t+1) z * (oldPrefix X (t+1) z).card ≤
    childCount G ((oldPrefix X t w).filter fun y => X t y = X t z)
      (remainder X T (t+1)) (X j w) (X t z) := by
  rw [child_prefix hz, ← (mem_tags.mp hz).2]
  by_cases hnext : t+1 ≤ b/2
  · have hi : b-(t+1)+1 = j := by omega
    have hmove := step_symm (leg (b-(t+1)) z)
    rw [hi] at hmove
    simp only [value, if_pos hnext, div_mul_cancel₀ _ (prefix_pos X (t+1) z).ne']
    exact_mod_cast best_next_le_child G _ _ _ _ _ hmove
  · simp only [value, if_neg hnext, one_mul]
    have split : j=t ∨ j=t+1 := by omega
    apply Nat.cast_le.mpr
    apply all_le_child
    · rcases split with rfl | rfl
      · exact Or.inl rfl
      · exact step_symm (leg t z)
    · intro u _
      rcases split with rfl | rfl
      · exact Or.inl rfl
      · right; intro he
        have hlen := congrArg List.length he
        simp [remainder] at hlen; omega

variable [Fintype V]

/-- The finite Bellman inequality on each old-prefix, guessed-vertex fiber. -/
theorem cell_bound (G : SimpleGraph V) (X : ℕ→W→V) (T b t j : ℕ)
    (hb : b ≤ 2*T) (ht : t ≤ b/2) (hj : j=b-t) (w : W)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    blockMean (key X t j) (fun z => value G X T b (t+1) z * conditional X t j z /
      conditional X (t+1) j z) w ≤ value G X T b t w := by
  classical
  let A := oldPrefix X t w
  let M := tags X t j w
  let c := fun r => childCount G (A.filter fun y => X t y = r) (remainder X T (t+1)) (X j w) r
  let N := fun z => value G X T b (t+1) z * (oldPrefix X (t+1) z).card
  let f := fun z => N z / (M.filter fun y => X t y = X t z).card
  have hsum : (∑ z ∈ M, f z) ≤ ∑ r, (c r : ℝ) :=
    sum_div_fiber_le M (X t) N c (fun z hz => child_dominates G X T b t j hb ht hj w z hz leg)
  have hroute : (fun z => X t z :: remainder X T (t+1) z) = remainder X T t := by
    funext z; exact (remainder_cons X T t (by omega) z).symm
  have hcount := sum_childCount_le_best G A (X t) (remainder X T (t+1)) (X j w)
  rw [hroute] at hcount
  have htotal : (∑ r, (c r : ℝ)) ≤ (bestCount G A (remainder X T t) (X j w) : ℝ) := by
    exact_mod_cast hcount
  have hterm (z : W) (hz : z ∈ M) :
      value G X T b (t+1) z * conditional X t j z / conditional X (t+1) j z =
        f z * ((M.card : ℝ) / A.card) := by
    obtain ⟨hp,hx⟩ := mem_tags.mp hz
    have hM : tags X t j z = M := by simp [tags, key, M, hp, hx]
    have hA : oldPrefix X t z = A := by simp [oldPrefix,A,hp]
    dsimp only [f,N]; unfold conditional
    rw [hM,hA, child_tags hz]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hm : (M.card : ℝ) ≠ 0 := (tags_pos X t j w).ne'
  change (∑ z ∈ M, _) / (M.card : ℝ) ≤ _
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  rw [value, if_pos ht, ←hj]
  calc
    _ = (∑ z ∈ M, f z) / A.card := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (hsum.trans htotal) (Nat.cast_nonneg _)

/-- The optimal strategy when the starting vertex is also at the cop's disposal. -/
noncomputable def unrestricted (G : SimpleGraph V) (A : Finset W) (route : W → List V) (base : V) : Policy G :=
  Classical.choose (exists_best (Policy.stay G base)
    (fun s => count A fun w => Hits s [] (route w)) A.card (fun _ => count_le ..))

omit [Fintype W] [DecidableEq V] [Fintype V] in
private theorem le_unrestricted (G : SimpleGraph V) (A : Finset W) (route : W → List V) (base x : V) :
    bestCount G A route x ≤ count A (fun w => Hits (unrestricted G A route base) [] (route w)) :=
  (Classical.choose_spec (exists_best (Policy.stay G base)
    (fun s => count A fun w => Hits s [] (route w)) A.card (fun _ => count_le ..))) (optimal G A route x).1

omit [Fintype V] in
private theorem prefix_zero (X : ℕ→W→V) (w : W) : oldPrefix X 0 w = Finset.univ := by
  simp [oldPrefix, fiber, past]

omit [Fintype V] in
private theorem cond_zero (X : ℕ→W→V) (j : ℕ) : conditional X 0 j = frequency (X j) := by
  funext w
  have htag : tags X 0 j w = fiber (X j) (X j w) := by
    ext z; simp [tags, key, fiber, past]
  simp [conditional, prefix_zero, frequency, htag]

omit [Fintype V] in
private theorem cond_le_one (X : ℕ→W→V) (t j : ℕ) (w : W) : conditional X t j w ≤ 1 := by
  unfold conditional
  rw [div_le_one (prefix_pos X t w)]
  exact_mod_cast Finset.card_le_card (show tags X t j w ⊆ oldPrefix X t w from
    fun _ hz => mem_prefix.mpr (mem_tags.mp hz).1)

variable [Nonempty W]

/-- One actual deterministic strategy catches the stated fraction of every
nonempty tagged family. Only the first T+1 vertices are tested for capture;
the later vertices, and the common home, are used solely for choosing guesses. -/
theorem tagged_one_cop (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ s : Policy G, 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
      (count Finset.univ (fun w => Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  classical
  let s := unrestricted G Finset.univ (remainder X T 0) home
  let success : ℝ := (count Finset.univ (fun w => Hits s [] (remainder X T 0 w)) : ℝ) / Fintype.card W
  let q := fun t j => logMean (conditional X t j)
  have hd (b : ℕ) (hb : b ≤ 2*T) : 0 < success ∧
      diagonalSum b (fun t j => q t j - q (t+1) j) ≤ Real.log success := by
    apply bellman_diagonal b (conditional X) (value G X T b) (fun t => key X t (b-t)) success
    · exact conditional_pos X
    · intro w; simp [value]
    · intro w; simp only [value, Nat.zero_le, if_true, prefix_zero, Finset.card_univ]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast le_unrestricted G Finset.univ (remainder X T 0) home (X (b-0) w)
    · intro t ht w; exact cell_bound G X T b t (b-t) hb ht rfl w leg
  have he : 1 ≤ n := (Fintype.card_pos_iff.mpr ⟨home⟩).trans_le hcard
  obtain ⟨_, _, hbound⟩ := exists_good_from_diagonal T d n he hcard htime X (conditional X)
    (fun _ => success) (fun t j w => ⟨conditional_pos X t j w, cond_le_one X t j w⟩) (cond_zero X)
    (fun j hj w z => (hhome j hj w).trans (hhome j hj z).symm) hd
  refine ⟨s,?_⟩
  have hh := (le_div_iff₀ (show 0 < (Fintype.card W : ℝ) by exact_mod_cast Fintype.card_pos)).mp hbound
  simpa [remainder] using hh

end Meyniel.Sampler
end Meyniel_Sampler
-- === END Meyniel.Sampler ===

-- === BEGIN Meyniel.Weights ===
section Meyniel_Weights

/-! The posted proof's forward probability calculation. For a specified observed
prefix, a vector stores the conditional probability of each live guessed walk.
A reveal first adds all live mass arriving at the same vertex and then divides
that mass equally among the compatible walks. Missing matches contribute zero.
-/

namespace Meyniel.ForwardWeights

open Finset Interception

noncomputable section

variable {W K V : Type*} [Fintype W] [DecidableEq K] [DecidableEq V]

def block (k : W → K) (w : W) : Finset W := fiber k (k w)

def joint (k : W → K) (x : W → V) (w : W) : Finset W :=
  fiber (fun z => (k z, x z)) (k w, x w)

def conditional (k : W → K) (x : W → V) (w : W) : ℝ :=
  ((joint k x w).card : ℝ) / (block k w).card

theorem block_pos (k : W → K) (w : W) : 0 < ((block k w).card : ℝ) := by
  exact_mod_cast (show (block k w).Nonempty from ⟨w, mem_own_fiber k w⟩).card_pos

theorem joint_pos (k : W → K) (x : W → V) (w : W) : 0 < ((joint k x w).card : ℝ) :=
  block_pos (fun z => (k z,x z)) w

theorem conditional_bound (k : W → K) (x : W → V) (w : W) :
    0 < conditional k x w ∧ conditional k x w ≤ 1 := by
  have h : joint k x w ⊆ block k w := by
    intro v hv
    apply mem_filter.mpr
    exact ⟨mem_univ _, congrArg Prod.fst (mem_filter.mp hv).2⟩
  exact ⟨div_pos (joint_pos k x w) (block_pos k w), (div_le_one (block_pos k w)).mpr
    (by exact_mod_cast card_le_card h)⟩

/-- Splitting the old conditional mass at the current vertex equally among the
compatible new guesses. Only the positive-sized block of a tagged walk is used. -/
def splitMass (oldKey newKey : W → K) (x : W → V) (mass : W → ℝ) (w : W) : ℝ :=
  (∑ z ∈ joint oldKey x w, mass z) / (joint newKey x w).card

def weight (k : W → K) (mass : W → ℝ) (w : W) : ℝ := (block k w).card * mass w

theorem split_weight (oldKey newKey : W → K) (x : W → V) (mass : W → ℝ) (w : W) :
    weight newKey (splitMass oldKey newKey x mass) w =
      blockMean (fun z => (oldKey z, x z)) (weight oldKey mass) w *
        conditional oldKey x w / conditional newKey x w := by
  have sum_weight :
      ∑ z ∈ joint oldKey x w, weight oldKey mass z =
      (block oldKey w).card * ∑ z ∈ joint oldKey x w, mass z := by
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    have he : oldKey z = oldKey w := congrArg Prod.fst (mem_filter.mp hz).2
    simp [weight, block, he]
  change (block newKey w).card * ((∑ z ∈ joint oldKey x w, mass z) / _) =
    ((∑ z ∈ joint oldKey x w, weight oldKey mass z) / (joint oldKey x w).card) *
    (((joint oldKey x w).card : ℝ) / (block oldKey w).card) /
    (((joint newKey x w).card : ℝ) / (block newKey w).card)
  rw [sum_weight]
  field_simp [ne_of_gt (block_pos oldKey w), ne_of_gt (block_pos newKey w),
    ne_of_gt (joint_pos oldKey x w), ne_of_gt (joint_pos newKey x w)]

/-- Averaging weights over all tagged walks is exactly the expectation of the
total live probability conditional on the independently sampled true prefix. -/
theorem mean_total_live (k : W → K) (mass : W → ℝ) :
    mean univ (fun w => ∑ z ∈ block k w, mass z) = mean univ (weight k mass) := by
  unfold mean
  congr 1
  rw [← sum_by_fiber k (fun w => ∑ z ∈ block k w, mass z), ← sum_by_fiber k (weight k mass)]
  apply sum_congr rfl
  intro h _
  calc
    _ = ∑ _w ∈ fiber k h, ∑ z ∈ fiber k h, mass z := by
      apply sum_congr rfl
      intro w hw
      simp [block, (mem_filter.mp hw).2]
    _ = ((fiber k h).card : ℝ) * ∑ z ∈ fiber k h, mass z := by simp
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w hw
      simp [weight, block, (mem_filter.mp hw).2]

theorem conditional_initial (k : W → K) (hk : ∀ v w, k v = k w) (x : W → V) :
    conditional k x = frequency x := by
  funext w
  have hb : block k w = univ := by ext v; simp [block,fiber,hk v w]
  have hj : joint k x w = fiber x (x w) := by ext v; simp [joint,fiber,hk v w]
  simp [conditional, frequency, hb, hj]

variable [Nonempty W]

/-- Live guess mass for one fixed diagonal. The initial guess is uniformly
sampled from the original family before the first reveal. -/
def guessMass (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ) : ℕ → W → ℝ
  | 0 => fun _ => 1 / Fintype.card W
  | t+1 => splitMass (history t) (history (t+1)) (X (b-t)) (guessMass history X b t)

theorem guessMass_pos (history : ℕ → W → K) (X : ℕ → W → V) (b t : ℕ) :
    ∀ w, 0 < guessMass history X b t w := by
  induction t with
  | zero => intro w; exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := W))
  | succ t ih =>
    intro w
    exact div_pos (sum_pos (fun z _ => ih z)
      ⟨w, mem_own_fiber (fun z => (history t z,X (b-t) z)) w⟩) (joint_pos ..)

def terminalLive (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ) : ℝ :=
  mean univ (fun w => ∑ z ∈ block (history (b/2+1)) w, guessMass history X b (b/2+1) z)

theorem forward_diagonal (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ)
    (hinit : ∀ x y, history 0 x = history 0 y) :
    0 < terminalLive history X b ∧ diagonalSum b (fun t j =>
      logMean (conditional (history t) (X j)) - logMean (conditional (history (t+1)) (X j))) ≤
      Real.log (terminalLive history X b) := by
  let mass := guessMass history X b
  let wt := fun t => weight (history t) (mass t)
  have hwt t w : 0 < wt t w := mul_pos (block_pos _ w) (guessMass_pos history X b t w)
  have hzero : wt 0 = fun _ => 1 := by
    funext w
    have h : block (history 0) w = univ := by
      ext z; simp [block,fiber,hinit z w]
    simp [wt,weight,mass,guessMass,h,Fintype.card_ne_zero]
  have he := forward_telescope b (fun t j =>
      logMean (conditional (history t) (X j)) - logMean (conditional (history (t+1)) (X j)))
    (fun t => logMean (wt t)) (fun t _ =>
      logMean_update (fun z => (history t z,X (b-t) z)) (wt t) (wt (t+1)) _ _
        (hwt t) (fun w => (conditional_bound _ _ w).1) (fun w => (conditional_bound _ _ w).1)
        (split_weight _ _ _ _))
  rw [hzero, logMean_one, sub_zero] at he
  unfold terminalLive
  rw [mean_total_live]
  exact ⟨mean_pos univ_nonempty (fun w _ => hwt _ w), he.trans (logMean_le_log_mean (hwt _))⟩

/-- The posted forward-sampler estimate on terminal live mass for concrete
history and position tables, obtained directly from the uniform split law. -/
theorem exists_good_forward [Fintype V] (history : ℕ → W → K) (X : ℕ → W → V)
    (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ)*Real.log n ≤ (T : ℝ)*Real.log 2)
    (hinit : ∀ x y, history 0 x = history 0 y)
    (hhome : ∀ j, T+d ≤ j → ∀ x y, X j x = X j y) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ terminalLive history X b := by
  exact exists_good_from_diagonal T d n hn hsize hT X
    (fun t j => conditional (history t) (X j)) (terminalLive history X)
    (fun _ _ => conditional_bound _ _) (fun _ => conditional_initial _ hinit _)
    hhome (fun b _ => forward_diagonal history X b hinit)


omit [Nonempty W] in
/-- Uniform averaging on fibers is self-adjoint for the counting measure. -/
theorem sum_blockMean_mul (k : W → K) (f g : W → ℝ) :
    (∑ w, blockMean k f w * g w) = ∑ w, f w * blockMean k g w := by
  rw [← sum_by_fiber k (fun w => blockMean k f w * g w),
      ← sum_by_fiber k (fun w => f w * blockMean k g w)]
  apply sum_congr rfl
  intro i _
  let A := fiber k i
  calc
    _ = ∑ w ∈ A, mean A f * g w := by
      apply sum_congr rfl
      intro w hw
      simp [blockMean, (mem_filter.mp hw).2, A]
    _ = (∑ w ∈ A, f w) * mean A g := by rw [← mul_sum]; unfold mean; ring
    _ = ∑ w ∈ A, f w * mean A g := by rw [sum_mul]
    _ = _ := by
      apply sum_congr rfl
      intro w hw
      simp [blockMean, (mem_filter.mp hw).2, A]

omit [Nonempty W] in
/-- The live forward mass paired with a backward value cannot increase when
the latter dominates the conditional arithmetic mean of all next positions. -/
theorem pairing_step (k : W → K) (old new pre post vOld vNew : W → ℝ)
    (hpos : ∀ w, 0 ≤ old w)
    (hnew : ∀ w, new w = blockMean k old w * pre w / post w)
    (hv : ∀ w, blockMean k (fun z => vNew z * pre z / post z) w ≤ vOld w) :
    mean univ (fun w => new w * vNew w) ≤ mean univ (fun w => old w * vOld w) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ∑ w, new w * vNew w = ∑ w, blockMean k old w * (vNew w * pre w / post w) := by
      apply sum_congr rfl
      intro w _
      rw [hnew]
      ring
    _ = _ := sum_blockMean_mul k old (fun z => vNew z * pre z / post z)
    _ ≤ _ := sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hv w) (hpos w))

/-- The same explicit forward mass can be compared directly with *any*
Bellman supersolution, using the arithmetic adjoint at each cell. -/
theorem terminalLive_le_bellman (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ)
    (hinit : ∀ x y, history 0 x = history 0 y)
    (v : ℕ → W → ℝ) (s : ℝ) (hend : ∀ w, v (b/2+1) w = 1) (hstart : ∀ w, v 0 w ≤ s)
    (hstep : ∀ t ≤ b/2, ∀ w,
      blockMean (fun z => (history t z,X (b-t) z))
        (fun z => v (t+1) z * conditional (history t) (X (b-t)) z /
           conditional (history (t+1)) (X (b-t)) z) w ≤ v t w) :
    terminalLive history X b ≤ s := by
  let wt := fun t => weight (history t) (guessMass history X b t)
  let pair := fun t => mean univ (fun w => wt t w * v t w)
  have hs (t : ℕ) (ht : t ≤ b/2) : pair (t+1) ≤ pair t := by
    exact pairing_step (fun z => (history t z,X (b-t) z)) _ _ _ _ _ _
      (fun z => (mul_pos (block_pos _ z) (guessMass_pos history X b t z)).le)
      (split_weight _ _ _ _) (hstep t ht)
  have hm (t : ℕ) (ht : t ≤ b/2+1) : pair t ≤ pair 0 := by
    induction t with
    | zero => rfl
    | succ i ih => exact (hs i (by omega)).trans (ih (by omega))
  have he : pair (b/2+1) = terminalLive history X b := by
    simp only [pair, hend, mul_one, terminalLive, mean_total_live, wt]
  have hw (w : W) : wt 0 w = 1 := by
    have h : block (history 0) w = univ := by ext z; simp [block,fiber,hinit z w]
    simp [wt,weight,guessMass,h,Fintype.card_ne_zero]
  have h0 : pair 0 ≤ s := by
    simp only [pair,hw,one_mul,mean]
    apply (div_le_iff₀ (by exact_mod_cast (univ_nonempty : (univ : Finset W).Nonempty).card_pos)).2
    simpa [Finset.sum_const, mul_comm] using sum_le_sum (s := (univ : Finset W)) (fun w _ => hstart w)
  rw [← he]
  exact (hm _ le_rfl).trans h0


omit [Nonempty W] in
/-- For a prescribed next robber observation the total live guess mass can
only decrease. The only loss is old mass at vertices with no compatible tag. -/
theorem splitMass_total_le [Fintype V] (oldKey newKey : W → K) (x : W → V)
    (mass : W → ℝ) (w : W) (hn : ∀ z, 0 ≤ mass z)
    (refines : ∀ a b, newKey a = newKey b → oldKey a = oldKey b) :
    ∑ z ∈ block newKey w, splitMass oldKey newKey x mass z ≤ ∑ z ∈ block oldKey w, mass z := by
  classical
  rw [← sum_fiberwise (block newKey w) x, ← sum_fiberwise (block oldKey w) x]
  apply sum_le_sum
  intro y _
  let A := (block oldKey w).filter fun z => x z = y
  let B := (block newKey w).filter fun z => x z = y
  change (∑ z ∈ B, splitMass oldKey newKey x mass z) ≤ ∑ z ∈ A, mass z
  by_cases hB : B.Nonempty
  · have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
    have he (z : W) (hz : z ∈ B) : splitMass oldKey newKey x mass z = (∑ v ∈ A, mass v)/B.card := by
      obtain ⟨hnw, hxy⟩ := mem_filter.mp hz
      have hnew : newKey z = newKey w := (mem_filter.mp hnw).2
      have hold := refines _ _ hnew
      have ha : joint oldKey x z = A := by
        ext v; simp only [joint,block,fiber,A,mem_filter,mem_univ,true_and,Prod.mk.injEq,hold,hxy]
      have hc : joint newKey x z = B := by
        ext v; simp only [joint,block,fiber,B,mem_filter,mem_univ,true_and,Prod.mk.injEq,hnew,hxy]
      simp [splitMass, ha,hc]
    rw [sum_congr rfl he, sum_const,nsmul_eq_mul]
    exact le_of_eq (by field_simp)
  · rw [not_nonempty_iff_eq_empty.mp hB, sum_empty]
    exact sum_nonneg (fun z _ => hn z)

theorem total_live_le_one [Fintype V] (history : ℕ → W → K) (X : ℕ → W → V)
    (refines : ∀ t a b, history (t+1) a = history (t+1) b → history t a = history t b)
    (b t : ℕ) (w : W) :
    ∑ z ∈ block (history t) w, guessMass history X b t z ≤ 1 := by
  induction t with
  | zero =>
    have h : (block (history 0) w).card ≤ Fintype.card W := card_le_univ _
    simp only [guessMass, sum_const, nsmul_eq_mul]
    rw [mul_one_div, div_le_one (by exact_mod_cast Fintype.card_pos (α := W))]
    exact_mod_cast h
  | succ t ih =>
    exact (splitMass_total_le _ _ _ _ w (fun z => (guessMass_pos history X b t z).le) (refines t)).trans ih

end
end Meyniel.ForwardWeights
end Meyniel_Weights
-- === END Meyniel.Weights ===

-- === BEGIN Meyniel.RandomTable ===
section Meyniel_RandomTable

/-! A finite uniform source of compatible guesses. One row of the source
chooses a member of every nonempty subset of tags. Splitting off a specified
coordinate proves that it is uniform on that subset. -/

namespace Meyniel.RandomTable

open Finset
noncomputable section

variable {A B I W : Type*}

def avg [Fintype A] (f : A → ℝ) : ℝ := (∑ a, f a) / Fintype.card A

@[simp] theorem avg_const [Fintype A] [Nonempty A] (c : ℝ) :
    avg (fun _ : A => c) = c := by
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (by exact_mod_cast Fintype.card_ne_zero)

theorem avg_prod [Fintype A] [Fintype B] (f : A × B → ℝ) :
    avg f = avg (fun a : A => avg (fun b : B => f (a,b))) := by
  simp only [avg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← sum_div]
  ring

theorem avg_sum_finset [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  simp only [avg, ← sum_div]
  rw [sum_comm]

theorem avg_sum [Fintype A] [Fintype I] (f : I → A → ℝ) :
    avg (fun a => ∑ i, f i a) = ∑ i, avg (f i) := avg_sum_finset univ f

theorem avg_mul_const [Fintype A] (f : A → ℝ) (c : ℝ) :
    avg (fun a => f a * c) = avg f * c := by
  simp only [avg, ← sum_mul]
  ring

theorem avg_equiv [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  simp only [avg, e.sum_comp, Fintype.card_congr e]

@[simp] theorem avg_indicator_unique [Fintype A] [DecidableEq A] (a : A) :
    avg (fun z : A => if z = a then (1 : ℝ) else 0) = 1 / Fintype.card A := by
  simp [avg]

/-- Every coordinate of a uniform finite dependent product has its own
uniform marginal, provided the other coordinates are inhabited. -/
theorem avg_coordinate [Fintype I] [DecidableEq I] (P : I → Type*) [∀ i, Fintype (P i)]
    (hne : ∀ i, Nonempty (P i)) (i : I) (f : P i → ℝ) :
    avg (fun row : ∀ j, P j => f (row i)) = avg f := by
  classical
  let e := Equiv.piSplitAt i P
  letI : Nonempty ((j : {j : I // j ≠ i}) → P j) :=
    ⟨fun j => Classical.choice (hne j)⟩
  have h := avg_equiv e (fun z => f z.1)
  calc
    _ = avg (fun z : P i × ((j : {j : I // j ≠ i}) → P j) => f z.1) := h
    _ = _ := by rw [avg_prod]; simp

abbrev Key (W : Type*) := {B : Finset W // B.Nonempty}
abbrev Row (W : Type*) := (B : Key W) → {w : W // w ∈ B.val}

instance rowNonempty : Nonempty (Row W) :=
  ⟨fun B => Classical.choice B.property.to_subtype⟩

def select [DecidableEq W] (row : Row W) (B : Finset W) : Option W :=
  if hb : B.Nonempty then some ((row ⟨B,hb⟩).val) else none

theorem avg_select [Fintype W] [DecidableEq W] (B : Finset W) (w : W) :
    avg (fun row : Row W => if select row B = some w then (1:ℝ) else 0) =
      if w ∈ B then (1 : ℝ) / (B.card : ℝ) else 0 := by
  classical
  by_cases hb : B.Nonempty
  · let i : Key W := ⟨B,hb⟩
    let P := fun j : Key W => {z : W // z ∈ j.val}
    let f : P i → ℝ := fun z => if z.val = w then 1 else 0
    have hu : avg (fun row : Row W => if select row B = some w then (1:ℝ) else 0) = avg f := by
      simpa [select,hb,f,i,P] using avg_coordinate P (fun j => j.property.to_subtype) i f
    rw [hu]
    by_cases hw : w ∈ B
    · let v : P i := ⟨w,hw⟩
      have he : f = fun z => if z = v then 1 else 0 := by
        funext z
        change (if z.val = v.val then (1 : ℝ) else 0) = if z = v then 1 else 0
        by_cases hz : z = v
        · have hval : z.val = v.val := congrArg Subtype.val hz
          simp only [if_pos hz, if_pos hval]
        · have hval : z.val ≠ v.val := fun h => hz (Subtype.ext h)
          simp only [if_neg hz, if_neg hval]
      have hc : Fintype.card (P i) = B.card := Fintype.card_coe B
      rw [he, avg_indicator_unique, hc, if_pos hw]
    · have he : f = fun _ => 0 := by
        funext z
        have hne : z.val ≠ w := fun h => hw (h ▸ z.property)
        simp [f, hne]
      rw [he, if_neg hw]
      simp [avg]
  · rw [not_nonempty_iff_eq_empty.mp hb]
    simp [select,avg]

end
end Meyniel.RandomTable
end Meyniel_RandomTable
-- === END Meyniel.RandomTable ===

-- === BEGIN Meyniel.RandomPolicy ===
section Meyniel_RandomPolicy

/-! # The backward sampler as finite random tapes of legal ordinary policies

At each row a fresh table selects a uniform tagged walk from each nonempty
compatible set. A fixed tape assigns all these choices before the robber starts.
The table is queried only after computing the compatible set from the real cop
vertex and the observed robber prefix.
-/

namespace Meyniel.RandomPolicy

open Finset

noncomputable section

variable {V W : Type*}

/-- A set of candidates that is safe to sample uniformly. -/
abbrev Key (W : Type*) := RandomTable.Key W

/-- One sample for every possible nonempty query at a fixed row. -/
abbrev Row (W : Type*) := RandomTable.Row W

def defaultRow (W : Type*) : Row W := fun B => ⟨B.prop.choose, B.prop.choose_spec⟩

/-- An initial guess and one independent response table for each subsequent reveal. -/
def Tape (W : Type*) : ℕ → Type _
  | 0 => W
  | t+1 => Tape W t × Row W

instance tapeFinite [Fintype W] : ∀ t, Fintype (Tape W t)
  | 0 => inferInstanceAs (Fintype W)
  | t+1 => by
    classical
    letI := tapeFinite t
    exact inferInstanceAs (Fintype (Tape W t × Row W))

instance tapeNonempty [Nonempty W] : ∀ t, Nonempty (Tape W t)
  | 0 => inferInstanceAs (Nonempty W)
  | t+1 => by
    letI := tapeNonempty t
    exact inferInstanceAs (Nonempty (Tape W t × Row W))

def initial : ∀ t, Tape W t → W
  | 0, s => s
  | t+1, (s,_) => initial t s

def rowAt : ∀ t, Tape W t → ℕ → Row W
  | 0, _, _ => defaultRow W
  | t+1, (s,row), k => if k=t then row else rowAt t s k

variable [Fintype W] [DecidableEq W] [DecidableEq V]

def pool (X : ℕ→W→V) (t j : ℕ) (h : List V) (cop : V) : Finset W :=
  Finset.univ.filter fun w => Sampler.past X t w = h ∧ X j w = cop

abbrev select (rows : Row W) (B : Finset W) : Option W := RandomTable.select rows B

omit [Fintype W] in
theorem select_mem {q : Row W} {B : Finset W} {w : W} (h : select q B = some w) : w ∈ B := by
  unfold select RandomTable.select at h; split at h
  next hb => exact (Option.some.inj h) ▸ (q ⟨B,hb⟩).property
  next => contradiction

/-- One transition of the exact guessing rule. Permanent failure retains the
physical vertex. The final odd entry also takes its last legal backward step. -/
def advance (X : ℕ→W→V) (b t : ℕ) (h : List V) (row : Row W) (st : V × Option W) : V × Option W :=
  if t ≤ b/2 then
    match st.2 with
    | none => st
    | some _ => match select row (pool X (t+1) (b-t) h st.1) with
      | none => (st.1,none)
      | some z => (if t < b-t then X (b-t-1) z else st.1,some z)
  else st

/-- Computing the physical state requires only the revealed prefix. -/
def state (X : ℕ→W→V) (b : ℕ) (w₀ : W) (rows : ℕ→Row W) : List V → V × Option W
  | [] => (X b w₀, some w₀)
  | r :: h => advance X b h.length (r::h) (rows h.length) (state X b w₀ rows h)

private theorem advance_legal (G : SimpleGraph V) (X : ℕ→W→V)
    (legal : ∀i w, Step G (X i w) (X (i+1) w)) (b t) (h) (row) (st) :
    Step G st.1 (advance X b t h row st).1 := by
  unfold advance
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      next z he =>
        split_ifs with hj
        · have hz := (Finset.mem_filter.mp (select_mem he)).2.2
          have hs := legal (b-t-1) z
          have hn : b-t-1+1=b-t := by omega
          rw [hn,hz] at hs
          exact hs.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)
        · exact Or.inl rfl
  · exact Or.inl rfl

/-- Fixing each coin is exactly one legal strategy with a public initial vertex. -/
def policy (G : SimpleGraph V) (X : ℕ→W→V) (legal : ∀i w, Step G (X i w) (X (i+1) w))
    (b k : ℕ) (tape : Tape W k) : Policy G where
  pos := fun h => (state X b (initial k tape) (rowAt k tape) h).1
  legal := fun r h => advance_legal G X legal b h.length (r::h) _ _

private theorem state_rows_congr (X : ℕ→W→V) (b) (w₀) (rows rows' : ℕ→Row W) (h : List V)
    (he : ∀ i < h.length, rows i = rows' i) : state X b w₀ rows h = state X b w₀ rows' h := by
  induction h with
  | nil => rfl
  | cons r h ih =>
    simp only [state,he h.length (by simp),ih (fun i hi => he i (by simp; omega))]

omit [Fintype W] [DecidableEq W] [DecidableEq V] in
@[simp] theorem length_past (X : ℕ→W→V) (t : ℕ) (w : W) : (Sampler.past X t w).length=t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Sampler.past,ih]

/-- The next independent row cannot affect the cop's state before this reveal. -/
theorem state_before_new_row (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (row : Row W) (h : List V)
    (hh : h.length ≤ t) :
    state X b (initial (t+1) (s,row)) (rowAt (t+1) (s,row)) h = state X b (initial t s) (rowAt t s) h := by
  apply state_rows_congr
  intro i hi; simp [rowAt,show i ≠ t by omega]

/-- A live guess is always physically at its current target time. -/
theorem live_vertex (X : ℕ→W→V) (b) (w₀) (rows : ℕ→Row W) (h : List V) (z : W)
    (ht : h.length ≤ b/2) (hz : (state X b w₀ rows h).2 = some z) :
    (state X b w₀ rows h).1 = X (b-h.length) z := by
  cases h with
  | nil => simp [state] at hz ⊢; exact congrArg (X b) hz
  | cons r h =>
    have hk : h.length < b/2 := by simpa using ht
    simp only [state, advance, if_pos hk.le] at hz ⊢
    split at hz
    · next he => simp [he] at hz
    · next old he =>
        split at hz
        · contradiction
        next guess hguess =>
          simp only [Option.some.injEq] at hz
          simp only [if_pos (show h.length < b-h.length by omega),hz,List.length_cons]
          congr 1

/-- State after the first t reveals on the independently prescribed walk. -/
def outcome (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (actual : W) : V × Option W :=
  state X b (initial t s) (rowAt t s) (Sampler.past X t actual)

theorem outcome_succ (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (row : Row W) (actual : W) :
    outcome X b (t+1) (s,row) actual =
      advance X b t (Sampler.past X (t+1) actual) row (outcome X b t s actual) := by
  change advance X b _ _ _ (state X b _ _ (Sampler.past X t actual)) = _
  rw [length_past, state_before_new_row X b t s row _ (by simp)]
  simp [rowAt,outcome,Sampler.past]

end
end Meyniel.RandomPolicy
end Meyniel_RandomPolicy
-- === END Meyniel.RandomPolicy ===

-- === BEGIN Meyniel.RandomLaw ===
section Meyniel_RandomLaw

/-! Exact law of the seeded backward policy under the uniform tape distribution. -/

namespace Meyniel.RandomLaw

open Finset RandomPolicy
open RandomTable (avg)

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V] [Nonempty W]

private theorem avg_div {A : Type*} [Fintype A] (f : A→ℝ) (c : ℝ) :
    avg (fun a => f a / c) = avg f / c := by
  simp only [div_eq_mul_inv, RandomTable.avg_mul_const]

omit [Nonempty W] in
private theorem live_choice (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2) (h : List V) (row : Row W)
    (st : V × Option W) : (advance X b t h row st).2 =
      match st.2 with | none => none | some _ => select row (pool X (t+1) (b-t) h st.1) := by
  rcases st with ⟨x, _ | g⟩
  · simp [advance,ht]
  · simp only [advance,if_pos ht]; split <;> rename_i he <;> exact he.symm

omit [Nonempty W] in
private theorem one_row (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2) (a z : W)
    (st : V × Option W) (phys : ∀ g, st.2 = some g → st.1 = X (b-t) g) :
    avg (fun row : Row W => if (advance X b t (Sampler.past X (t+1) a) row st).2=some z
      then (1:ℝ) else 0) =
      if Sampler.past X (t+1) z = Sampler.past X (t+1) a then
        (∑ g ∈ (Finset.univ.filter fun g => X (b-t) g = X (b-t) z),
          if st.2=some g then (1:ℝ) else 0) /
          (ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z).card else 0 := by
  classical
  simp only [live_choice X b t ht]
  cases hg : st.2 with
  | none => simp [RandomTable.avg_const]
  | some g =>
    rw [phys g hg]
    let B := pool X (t+1) (b-t) (Sampler.past X (t+1) a) (X (b-t) g)
    change avg (fun row : RandomTable.Row W => if RandomTable.select row B = some z then (1:ℝ) else 0) = _
    rw [RandomTable.avg_select]
    have hmem : z ∈ B ↔ Sampler.past X (t+1) z = Sampler.past X (t+1) a ∧
      X (b-t) z = X (b-t) g := by simp [B,pool]
    by_cases hpre : Sampler.past X (t+1) z = Sampler.past X (t+1) a
    · simp only [if_pos hpre, Option.some.injEq]
      by_cases hx : X (b-t) g = X (b-t) z
      · have he : B = ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z := by
          ext u; simp [B,pool,ForwardWeights.joint,Interception.fiber,hpre,hx]
        simp [hpre,hx,he,ForwardWeights.joint,Interception.fiber]
      · simp [hmem,hpre,hx,Ne.symm hx]
    · simp [hmem,hpre]

omit [Nonempty W] in
private theorem avg_tape_succ (t : ℕ) (f : Tape W (t+1) → ℝ) :
    avg f = avg (fun s : Tape W t => avg (fun row : Row W => f (s,row))) := by
  classical
  let g : Tape W t × Row W → ℝ := f
  have h := RandomTable.avg_prod g
  apply Eq.trans _ h
  exact congrArg (fun F : Fintype (Tape W (t+1)) => @avg _ F f) (Subsingleton.elim _ _)

/-- The probability that a fixed tag is the currently live guess, conditioned on
observing the prescribed walk's real prefix, using an independent uniform tape. -/
def liveProbability (X : ℕ→W→V) (b t : ℕ) (a z : W) : ℝ :=
  avg (fun tape : Tape W t => if (outcome X b t tape a).2 = some z then 1 else 0)

/-- The paper's forward guess mass is the exact fraction of pure tapes whose
guess equals z at the indicated prefix. Off-prefix guesses have probability zero. -/
theorem liveProbability_eq (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2+1) (a z : W) :
    liveProbability X b t a z = if Sampler.past X t z = Sampler.past X t a then
      ForwardWeights.guessMass (Sampler.past X) X b t z else 0 := by
  classical
  induction t generalizing a z with
  | zero =>
    simp only [liveProbability, outcome, Sampler.past, initial, state, if_true,
      ForwardWeights.guessMass, RandomTable.avg]
    dsimp only [Tape, tapeFinite]
    congr 1
    trans (∑ w : W, if w = z then (1 : ℝ) else 0)
    · refine Finset.sum_congr rfl fun w _ => ?_
      by_cases h : w = z <;> simp [h]
    · simp
  | succ t ih =>
    have hk : t ≤ b/2 := by omega
    let B := Finset.univ.filter fun g => X (b-t) g = X (b-t) z
    let J := ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z
    let pre := Sampler.past X (t+1) z = Sampler.past X (t+1) a
    let score := fun (s : Tape W t) (g : W) => if (outcome X b t s a).2=some g then (1:ℝ) else 0
    have he : liveProbability X b (t+1) a z =
        avg (fun s : Tape W t => if pre then (∑ g ∈ B, score s g) / J.card else 0) := by
      unfold liveProbability
      rw [avg_tape_succ]
      apply congrArg avg; funext s
      simp only [outcome_succ]
      apply one_row X b t hk a z
      intro g hg
      simpa [outcome] using live_vertex X b (initial t s) (rowAt t s) (Sampler.past X t a) g
        (by simp [hk]) hg
    rw [he]
    by_cases hp : pre
    · have hparent : Sampler.past X t z = Sampler.past X t a := (List.cons.inj hp).2
      have hp' : Sampler.past X (t+1) z = Sampler.past X (t+1) a := hp
      simp only [if_pos hp,if_pos hp',ForwardWeights.guessMass,ForwardWeights.splitMass]
      rw [avg_div, RandomTable.avg_sum_finset]
      apply congrArg (fun q : ℝ => q/J.card)
      change (∑ g ∈ B, liveProbability X b t a g) = _
      have hs : (∑ g ∈ B, liveProbability X b t a g) = ∑ g ∈ B,
          if Sampler.past X t g = Sampler.past X t a then ForwardWeights.guessMass (Sampler.past X) X b t g else 0 :=
        Finset.sum_congr rfl (fun g _ => ih (by omega) a g)
      rw [hs, ← Finset.sum_filter]
      congr 1
      ext u; simp [B,ForwardWeights.joint,Interception.fiber,hparent,and_comm]
    · have hp' : Sampler.past X (t+1) z ≠ Sampler.past X (t+1) a := hp
      simp [hp,hp']

/-- Under a fixed prescribed walk, total terminal-live mass in the manuscript
is exactly the probability that the presampled table still has a guess. -/
theorem terminal_probability (X : ℕ→W→V) (b : ℕ) (a : W) :
    avg (fun tape : Tape W (b/2+1) => if (outcome X b (b/2+1) tape a).2.isSome then (1:ℝ) else 0) =
      ∑ z ∈ ForwardWeights.block (Sampler.past X (b/2+1)) a,
        ForwardWeights.guessMass (Sampler.past X) X b (b/2+1) z := by
  classical
  let k := b/2+1
  have hsum (s : Tape W k) : (if (outcome X b k s a).2.isSome then (1:ℝ) else 0) =
      ∑ z : W, if (outcome X b k s a).2=some z then 1 else 0 := by
    cases h : (outcome X b k s a).2 <;> simp
  change avg (fun s : Tape W k => if (outcome X b k s a).2.isSome then (1:ℝ) else 0) = _
  simp_rw [hsum]
  rw [RandomTable.avg_sum]
  change (∑ z : W, liveProbability X b k a z) = _
  simp_rw [liveProbability_eq X b k (le_refl _) a]
  rw [← Finset.sum_filter]; rfl

end
end Meyniel.RandomLaw
end Meyniel_RandomLaw
-- === END Meyniel.RandomLaw ===

-- === BEGIN Meyniel.RandomCapture ===
section Meyniel_RandomCapture

/-! # Capture on the terminal diagonal

On an even diagonal the live cop already occupies the robber's current
vertex before its next move. On an odd diagonal the cop gets one last legal
move by the deadline. In particular there is no extra cop turn after time T.
-/

namespace Meyniel.RandomCapture

open Sampler

variable {V W : Type*} {G : SimpleGraph V}

private theorem remainder_at (X : ℕ → W → V) (T t : ℕ) (ht : t ≤ T) (w : W) :
    remainder X T t w = X t w :: remainder X T (t+1) w := by
  unfold remainder
  have hlen : T+1-t = (T+1-(t+1))+1 := by omega
  conv_lhs => rw [hlen]
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  simp [Fin.val_succ]
  omega

/-- A capture on the suffix, using its actual prior observations, counts
as a capture on the original word. -/
private theorem hits_from_time (s : Policy G) (X : ℕ → W → V) (T t : ℕ) (w : W)
    (ht : t ≤ T) (hit : Hits s (past X t w) (remainder X T t w)) :
    Hits s [] (remainder X T 0 w) := by
  induction t with
  | zero => exact hit
  | succ t ih =>
    apply ih (by omega)
    rw [remainder_at X T t (by omega) w, remainder_at X T (t+1) ht w]
    rw [remainder_at X T (t+1) ht w] at hit
    exact Or.inr (Or.inr hit)

private theorem hits_at_time (s : Policy G) (X : ℕ → W → V) (T t : ℕ) (w : W)
    (ht : t ≤ T) (meet : s.pos (past X t w) = X t w ∨
      (t < T ∧ s.pos (past X (t+1) w) = X t w)) :
    Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w)) := by
  suffices full : Hits s [] (remainder X T 0 w) by simpa [remainder] using full
  apply hits_from_time s X T t w ht
  rw [remainder_at X T t ht w]
  by_cases ends : t = T
  · subst t
    have empty : remainder X T (T+1) w = [] := by simp [remainder]
    rw [empty]
    exact meet.elim id (fun h => (Nat.lt_irrefl T h.1).elim)
  · rw [remainder_at X T (t+1) (by omega) w]
    exact meet.elim Or.inl (fun h => Or.inr (Or.inl h.2))

end Meyniel.RandomCapture

namespace Meyniel.RandomCapture

open RandomPolicy Sampler

variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

/-- A surviving final resampling step either certifies an existing
coincidence (even b), or puts the cop on the robber (odd b). -/
private theorem terminal_advance (X : ℕ → W → V) (b t : ℕ) (ht : t = b/2)
    (w : W) (row : Row W) (st : V × Option W)
    (alive : (advance X b t (past X (t+1) w) row st).2.isSome) :
    (b = 2*t ∧ st.1 = X t w) ∨
    (b = 2*t+1 ∧ (advance X b t (past X (t+1) w) row st).1 = X t w) := by
  have ha : t ≤ b/2 := ht.le
  rcases st with ⟨v, prev⟩
  cases prev with
  | none => simp [advance, ha] at alive
  | some old =>
    cases chosen : select row (pool X (t+1) (b-t) (past X (t+1) w) v) with
    | none => simp [advance, ha, chosen] at alive
    | some z =>
      have mem := select_mem chosen
      have both := (Finset.mem_filter.mp mem).2
      have hp : past X (t+1) z = past X (t+1) w := both.1
      have hx : X (b-t) z = v := both.2
      have hz : X t z = X t w := (List.cons.inj hp).1
      by_cases heven : b = 2*t
      · have jt : b-t = t := by omega
        rw [jt] at hx
        exact Or.inl ⟨heven, hx.symm.trans hz⟩
      · have hodd : b = 2*t+1 := by omega
        have hmove : t < b-t := by omega
        have jprev : b-t-1 = t := by omega
        exact Or.inr ⟨hodd, by simpa [advance,ha,chosen,hmove,jprev] using hz⟩

/-- A live terminal match on the diagonal is genuine capture by round T.
This holds on each true walk and for each fixed seed. -/
theorem terminal_seed_hits (G : SimpleGraph V) (X : ℕ → W → V)
    (legal : ∀ i w, Step G (X i w) (X (i+1) w))
    (T b : ℕ) (hb : b ≤ 2*T) (seed : Tape W (b/2+1)) (actual : W)
    (live : (outcome X b (b/2+1) seed actual).2.isSome) :
    Hits (policy G X legal b (b/2+1) seed) [] (List.ofFn (fun i : Fin (T+1) => X i.val actual)) := by
  let t := b/2
  let w₀ := initial (t+1) seed
  let rows := rowAt (t+1) seed
  let st := state X b w₀ rows (past X t actual)
  have hstate : state X b w₀ rows (past X (t+1) actual) =
      advance X b t (past X (t+1) actual) (rows t) st := by
    simp [state,st,past,length_past]
  change (state X b w₀ rows (past X (t+1) actual)).2.isSome at live
  rw [hstate] at live
  obtain ⟨he,hm⟩ | ⟨ho,hm⟩ := terminal_advance X b t rfl actual (rows t) st live
  · apply hits_at_time _ X T t actual (by dsimp [t]; omega)
    exact Or.inl hm
  · apply hits_at_time _ X T t actual (by dsimp [t]; omega)
    refine Or.inr ⟨by omega, ?_⟩
    change (state X b w₀ rows (past X (t+1) actual)).1 = _
    rw [hstate]
    exact hm

end Meyniel.RandomCapture
end Meyniel_RandomCapture
-- === END Meyniel.RandomCapture ===

-- === BEGIN Meyniel.RandomConclusion ===
section Meyniel_RandomConclusion

/-! Averaging over actual fixed tapes yields one deterministic cop from the
posted backward sampler. The robber may subsequently see its full strategy. -/

namespace Meyniel.RandomConclusion

open Finset RandomPolicy
open RandomTable (avg)

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W] [Nonempty W] [Fintype V] [DecidableEq V]

private theorem avg_swap {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    avg (fun a => avg (f a)) = avg (fun b => avg (fun a => f a b)) := by
  unfold RandomTable.avg
  simp only [← Finset.sum_div]; rw [Finset.sum_comm]; ring

private theorem exists_above_avg {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, avg f ≤ f a := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  refine ⟨a,?_⟩
  rw [← RandomTable.avg_const (A := A) (f a)]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum ha) (Nat.cast_nonneg _)

/-- This theorem returns not only an ordinary policy but a diagonal and a
specific finite random tape producing a covering fraction on the prescribed family. -/
theorem exists_covering_tape (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ b ≤ 2*T, ∃ tape : Tape W (b/2+1), 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
       (Sampler.count Finset.univ (fun w => Hits (policy G X leg b (b/2+1) tape) []
          (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  classical
  have hn : 1 ≤ n := (Fintype.card_pos_iff.mpr ⟨home⟩).trans_le hcard
  obtain ⟨b,hb,hgood⟩ := ForwardWeights.exists_good_forward (Sampler.past X) X T d n hn hcard htime
    (fun _ _ => rfl) (fun j hj w z => (hhome j hj w).trans (hhome j hj z).symm)
  let live := fun (tape : Tape W (b/2+1)) (w : W) => if (outcome X b (b/2+1) tape w).2.isSome then (1:ℝ) else 0
  have hlive : avg (fun tape => avg (live tape)) = ForwardWeights.terminalLive (Sampler.past X) X b := by
    rw [avg_swap]
    change avg (fun w => avg (fun tape => if (outcome X b (b/2+1) tape w).2.isSome then (1:ℝ) else 0)) = _
    simp_rw [RandomLaw.terminal_probability]
    rfl
  obtain ⟨tape,htape⟩ := exists_above_avg (fun tape => avg (live tape))
  rw [hlive] at htape
  have hbound := (le_div_iff₀ (show 0 < (Fintype.card W : ℝ) by exact_mod_cast Fintype.card_pos)).mp (hgood.trans htape)
  refine ⟨b,hb,tape,hbound.trans ?_⟩
  change (∑ w, live tape w) ≤ ((Finset.univ.filter (fun w => Hits (policy G X leg b (b/2+1) tape) []
    (List.ofFn (fun i : Fin (T+1) => X i.val w)))).card : ℝ)
  rw [← Finset.sum_boole (R := ℝ)]
  apply Finset.sum_le_sum; intro w _
  dsimp only [live]
  by_cases h : (outcome X b (b/2+1) tape w).2.isSome
  · rw [if_pos h, if_pos (RandomCapture.terminal_seed_hits G X leg T b hb tape w h)]
  · simp [h]; positivity

/-- The arbitrary-family interception lemma with the literal fixed-tape strategy. -/
theorem tagged_one_cop_seed (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ s : Policy G, 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
      (Sampler.count Finset.univ (fun w => Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  obtain ⟨b, _, seed, h⟩ := exists_covering_tape G X T d n home leg hhome hcard htime
  exact ⟨policy G X leg b (b/2+1) seed, h⟩

end
end Meyniel.RandomConclusion
end Meyniel_RandomConclusion
-- === END Meyniel.RandomConclusion ===

-- === BEGIN Meyniel.Theorem ===
section Meyniel_Theorem

/-! # The weak Meyniel bound for the ordinary cop game -/

namespace Meyniel

universe u
variable {V : Type u}

/-- Restrict the tagged-walk calculation to the given finite family of actual walks.
The artificial continuation is used only in predicting vertices; the capture policy
is evaluated on the original T-round words. -/
theorem walks_interception [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    (T D N : ℕ) (hcard : Fintype.card V ≤ N) (hdiam : G.diam ≤ D)
    (htime : (D:ℝ) * Real.log N ≤ T * Real.log 2) :
    WalkFraction G T (1 / Real.sqrt (2*N)) := by
  classical
  let home := Classical.choice hc.nonempty
  intro R hR hne
  letI : Nonempty R := hne.to_subtype
  let X (t : ℕ) (w : R) := Extension.extendWord hc home w.val t
  have leg (i : ℕ) (w : R) : Step G (X i w) (X (i+1) w) := by
    have hw : w.val ∈ walks G T := hR w.property
    exact Extension.extendWord_step hc home w.val (Finset.mem_filter.mp hw).2 i
  have last (j : ℕ) (hj : T+D ≤ j) (w : R) : X j w = home :=
    Extension.extendWord_home hc home w.val (by omega)
  obtain ⟨s, hs⟩ := RandomConclusion.tagged_one_cop_seed G X T D N home leg last hcard htime
  refine ⟨s, ?_⟩
  have he (w : R) : (fun i : Fin (T+1) => X i.val w) = w.val := by
    funext i
    exact Extension.extendWord_at hc home w.val i
  simp only [he, Fintype.card_coe] at hs
  have eqcount : Sampler.count Finset.univ (fun w : R => Hits s [] (List.ofFn w.val)) =
      (R.filter (fun w => Hits s [] (List.ofFn w))).card := by
    unfold Sampler.count
    change (R.attach.filter (fun w : R => Hits s [] (List.ofFn w.val))).card = _
    rw [Finset.filter_attach (fun w => Hits s [] (List.ofFn w))]
    simp
  rwa [eqcount] at hs

/-- Lemma 2, with precisely the ceiling of diameter times the base-two log. -/
theorem oneCop_lemma [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    WalkFraction G (horizon (Fintype.card V) G.diam) (1 / Real.sqrt (2*Fintype.card V)) :=
  walks_interception hc _ _ _ le_rfl le_rfl (horizon_large ..)

/-- An explicit form of the manuscript's order estimate, uniform in the graph. -/
theorem copNumber_three_quarters [Fintype V] (G : SimpleGraph V) (hc : G.Connected) :
    (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3/4:ℝ) *
      Real.log (2 * (Fintype.card V : ℝ)) := by
  let n := Fintype.card V
  let D := diamThreshold n
  let T := horizon n D
  have hn : 1 ≤ n := by
    letI := hc.nonempty
    exact Fintype.card_pos
  have win : WinsWith G (budget n T + n/D) := by
    apply Guard.diameter_reduction hc (N := n) (K := budget n T) (D := D) le_rfl (diamThreshold_pos hn)
    intro W inst H hconn hs hd
    letI := hconn.nonempty
    exact winsWith_budget hn hs (walks_interception hconn T D n hs hd (horizon_large ..))
  exact (Nat.cast_le.mpr (copNumber_le_of_win win)).trans (budget_add_guards_le hn)

end Meyniel
end Meyniel_Theorem
-- === END Meyniel.Theorem ===

-- === BEGIN Meyniel.Corollary ===
section Meyniel_Corollary

/-! # The polynomial saving in the weak Meyniel conjecture

The constant may depend on the exponent but is uniform over all graphs.
The existential statement uses the quantifier order of the Formal
Conjectures project's `meyniel_conjecture.variants.soft`.
-/

namespace Meyniel

universe u

/-- The main quantitative estimate yields every fixed saving below one fourth. -/
theorem weak_forall_epsilon_of_bound
    (main : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3 / 4 : ℝ) *
        Real.log (2 * (Fintype.card V : ℝ)))
    (ε : ℝ) (_hε : 0 < ε) (hε' : ε < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) := by
  let δ : ℝ := 1/4 - ε
  have hδ : 0 < δ := sub_pos.mpr hε'
  refine ⟨31 * (2 : ℝ) ^ δ / δ, by positivity, ?_⟩
  intro V _ G conn
  letI : Nonempty V := conn.nonempty
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hsum : 1 - ε = 3 / 4 + δ := by dsimp [δ]; ring
  calc
    (copNumber G : ℝ) ≤ 31 * n ^ (3/4 : ℝ) * Real.log (2*n) := main V G conn
    _ ≤ 31 * n ^ (3/4 : ℝ) * ((2*n) ^ δ / δ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (by positivity) hδ) (by positivity)
    _ = (31 * (2 : ℝ) ^ δ / δ) * n ^ (1 - ε) := by
      rw [hsum, Real.rpow_add hn, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn.le]
      ring

/-- The soft conjecture, with globally chosen exponent and multiplicative constant. -/
theorem soft_of_bound
    (main : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3 / 4 : ℝ) *
        Real.log (2 * (Fintype.card V : ℝ))) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      G.Connected → (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) := by
  obtain ⟨C, hC, hg⟩ := weak_forall_epsilon_of_bound main (1 / 8) (by norm_num) (by norm_num)
  exact ⟨1 / 8, C, by norm_num, hC, hg⟩

end Meyniel
end Meyniel_Corollary
-- === END Meyniel.Corollary ===

-- === BRIDGE TO FormalConjectures.Wikipedia.MeynielConjecture ===
section OMA_Bridge

private theorem oma_copsCatchWithin_iff {V : Type*} (G : SimpleGraph V) (k t : ℕ)
    (c : Fin k → V) (r : V) :
    MeynielConjecture.CopsCatchWithin G k t c r ↔ Meyniel.CatchesWithin G k t c r := by
  induction t generalizing c r with
  | zero => rfl
  | succ t ih =>
    simp only [MeynielConjecture.CopsCatchWithin, Meyniel.CatchesWithin, ih,
      MeynielConjecture.Step, Meyniel.Step]

private theorem oma_copsWin_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    MeynielConjecture.CopsWin G k ↔ Meyniel.WinsWith G k := by
  simp only [MeynielConjecture.CopsWin, Meyniel.WinsWith, oma_copsCatchWithin_iff]

private theorem oma_copNumber_eq {V : Type*} (G : SimpleGraph V) :
    MeynielConjecture.copNumber G = Meyniel.copNumber G := by
  simp only [MeynielConjecture.copNumber, Meyniel.copNumber, oma_copsWin_iff]

end OMA_Bridge

theorem OMA.solution : type_of% @MeynielConjecture.meyniel_conjecture.variants.soft := by
  simpa only [oma_copNumber_eq] using
    Meyniel.soft_of_bound (fun _ _ G conn => Meyniel.copNumber_three_quarters G conn)
