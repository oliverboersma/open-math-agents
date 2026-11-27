import OMAStatements.S_opg_jaegers_modular_orientation_conjecture
import Mathlib

/-!
# A counterexample to Jaeger's modular orientation conjecture for k = 3

A finite 12-edge-connected multigraph with no modulo-seven orientation.

The graph and the proof that it has no modulo-seven orientation (`nonmodular`) are taken from the
proof of opg-circular-flow-number-of-regular-class-1-graphs in PR #7972 by AkiRA-COM-FP. That
graph is the p = 3 case of Mattiolo and Steffen, Edge colorings and circular flows on regular
graphs, arXiv:2001.02484, Section 3, and its obstruction follows Han, Li, Wu and Zhang,
Counterexamples to Jaeger's Circular Flow Conjecture, JCTB 131 (2018), Section 3, who first
refuted the conjecture for every k >= 3.

New here: the graph is 12-edge-connected. The proof is a Menger certificate: from the centre to
each vertex of block 0 there are 12 edge-disjoint walks (checked by `decide`), and the rotation
of the 13 blocks moves them to every other vertex. Deleting fewer than 12 edges leaves one walk
of each family intact.
-/

noncomputable section

namespace JaegerCounterexample

open Finset

/-- An integer assignment of objects to allowed recipients with prescribed counts exists
when there is a fractional assignment with those counts. -/
private theorem integral_assignment {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (allowed : E → V → Prop) (mass : E → V → ℝ) (cap : V → ℕ)
    (hnonneg : ∀ e v, 0 ≤ mass e v)
    (hallowed : ∀ e v, ¬ allowed e v → mass e v = 0)
    (hrow : ∀ e, (∑ v, mass e v) = 1)
    (hcol : ∀ v, (∑ e, mass e v) = cap v) :
    ∃ a : E → V, (∀ e, allowed e (a e)) ∧
      ∀ v, (∑ e, if a e = v then (1 : ℤ) else 0) = cap v := by
  classical
  let Slot := Σ v : V, Fin (cap v)
  let T (e : E) : Finset Slot := univ.filter fun s => allowed e s.1
  have hall (I : Finset E) : I.card ≤ (I.biUnion T).card := by
    let N : Finset V := univ.filter fun v => ∃ e ∈ I, allowed e v
    have hslots : I.biUnion T = N.sigma (fun v => (univ : Finset (Fin (cap v)))) := by
      ext s
      rw [Finset.mem_sigma]
      simp [T, N]
    have hrow' (e : E) (he : e ∈ I) : (∑ v ∈ N, mass e v) = 1 := by
      rw [← hrow e]
      apply sum_subset (subset_univ _)
      intro v _ hv
      exact hallowed e v (fun h => hv (mem_filter.mpr ⟨mem_univ _, e, he, h⟩))
    have hreal : (I.card : ℝ) ≤ ∑ v ∈ N, (cap v : ℝ) := by
      calc
        (I.card : ℝ) = ∑ e ∈ I, ∑ v ∈ N, mass e v := by
          rw [sum_congr rfl (fun e he => hrow' e he)]
          simp
        _ = ∑ v ∈ N, ∑ e ∈ I, mass e v := sum_comm
        _ ≤ ∑ v ∈ N, ∑ e, mass e v :=
          sum_le_sum fun v _ => sum_le_sum_of_subset_of_nonneg (subset_univ I)
            (fun e _ _ => hnonneg e v)
        _ = _ := by simp only [hcol]
    rw [hslots, card_sigma]
    simp only [card_univ, Fintype.card_fin]
    exact_mod_cast hreal
  obtain ⟨f, hf, hmem⟩ := (all_card_le_biUnion_card_iff_exists_injective T).mp hall
  have htotal : (Fintype.card E : ℝ) = ∑ v, (cap v : ℝ) := by
    calc
      _ = ∑ e : E, ∑ v : V, mass e v := by simp [hrow]
      _ = ∑ v : V, ∑ e : E, mass e v := sum_comm
      _ = _ := by simp only [hcol]
  have hcard : Fintype.card E = Fintype.card Slot := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using
      (by exact_mod_cast htotal : Fintype.card E = ∑ v, cap v)
  let g := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).2 ⟨hf, hcard⟩)
  refine ⟨fun e => (f e).1, fun e => (mem_filter.mp (hmem e)).2, fun v => ?_⟩
  calc
    (∑ e, if (f e).1 = v then (1 : ℤ) else 0) =
        ∑ s : Slot, if s.1 = v then (1 : ℤ) else 0 := g.sum_comp (fun s => if s.1 = v then 1 else 0)
    _ = cap v := by
      rw [Fintype.sum_sigma]
      have hsum (x : V) : (∑ _ : Fin (cap x), if x = v then (1 : ℤ) else 0) =
          if x = v then (cap x : ℤ) else 0 := by
        by_cases h : x = v <;> simp [h]
      simp_rw [hsum]
      simp

/-- Divergence with the given orientation of the edges. -/
def divergence {R V E : Type*} [AddCommGroup R] [Fintype E] [DecidableEq V]
    (src tgt : E → V) (flow : E → R) (v : V) : R :=
  (∑ e, if src e = v then flow e else 0) -
    ∑ e, if tgt e = v then flow e else 0

private theorem divergence_add {R V E : Type*} [AddCommGroup R] [Fintype E] [DecidableEq V]
    (s t : E → V) (f g : E → R) (v : V) :
    divergence s t (fun e => f e + g e) v = divergence s t f v + divergence s t g v := by
  unfold divergence
  have h (u : E → V) (e : E) :
      (if u e = v then f e + g e else 0) =
        (if u e = v then f e else 0) + (if u e = v then g e else 0) := by split <;> simp
  simp only [h, sum_add_distrib]
  abel

private theorem divergence_cast {V E : Type*} [Fintype E] [DecidableEq V]
    (s t : E → V) (f : E → ℤ) (v : V) :
    divergence s t (fun e => (f e : ℝ)) v = ((divergence s t f v : ℤ) : ℝ) := by
  unfold divergence
  push_cast
  rfl

set_option maxHeartbeats 900000 in
/-- Round a circulation satisfying integral unit-width edge bounds to an integral circulation. -/
theorem round_unit_circulation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) (hne : ∀ e, s e ≠ t e) (lo : E → ℤ) (w : E → ℝ)
    (hbound : ∀ e, (lo e : ℝ) ≤ w e ∧ w e ≤ (lo e : ℝ) + 1)
    (hdiv : ∀ v, divergence s t w v = 0) :
    ∃ z : E → ℤ, (∀ e, z e = lo e ∨ z e = lo e + 1) ∧
      ∀ v, divergence s t z v = 0 := by
  classical
  let frac (e : E) := w e - lo e
  have hfrac (e : E) : 0 ≤ frac e ∧ frac e ≤ 1 := by
    have hh := hbound e
    constructor <;> dsimp [frac] <;> linarith [hh.1, hh.2]
  let mass (e : E) (v : V) :=
    (if s e = v then 1 - frac e else 0) + (if t e = v then frac e else 0)
  let raw (v : V) : ℤ := (∑ e, if s e = v then (1 : ℤ) else 0) + divergence s t lo v
  have hmass (e : E) (v : V) : 0 ≤ mass e v := by
    dsimp [mass]
    have hh := hfrac e
    split_ifs <;> linarith [hh.1, hh.2]
  have hrow (e : E) : (∑ v, mass e v) = 1 := by simp [mass, sum_add_distrib]
  have hraw (v : V) : (∑ e, mass e v) = raw v := by
    have hsplit : (fun e => (lo e : ℝ) + frac e) = w := by funext e; dsimp [frac]; ring
    have hf := divergence_add s t (fun e => (lo e : ℝ)) frac v
    rw [hsplit, hdiv v, divergence_cast] at hf
    have hm (e : E) : mass e v = (if s e = v then 1 else 0) -
        ((if s e = v then frac e else 0) - (if t e = v then frac e else 0)) := by
      dsimp [mass]
      split_ifs <;> ring
    simp_rw [hm]
    rw [sum_sub_distrib, sum_sub_distrib]
    change (∑ e, if s e = v then (1 : ℝ) else 0) - divergence s t frac v = (raw v : ℝ)
    unfold raw
    push_cast
    linarith
  have hraw_pos (v : V) : 0 ≤ raw v := by
    have h := sum_nonneg (s := (univ : Finset E)) fun e _ => hmass e v
    rw [hraw v] at h
    exact_mod_cast h
  let cap (v : V) := (raw v).toNat
  have hcap (v : V) : (cap v : ℤ) = raw v := Int.toNat_of_nonneg (hraw_pos v)
  obtain ⟨f, hallowed, hcount⟩ := integral_assignment (fun e v => s e = v ∨ t e = v)
    mass cap hmass (fun e v h => by
      push Not at h
      simp [mass, h.1, h.2]) hrow
    (fun v => by rw [hraw v, ← hcap v]; norm_num)
  let up (e : E) : ℤ := if f e = t e then 1 else 0
  refine ⟨fun e => lo e + up e, fun e => by by_cases h : f e = t e <;> simp [up, h], ?_⟩
  intro v
  have hentry (e : E) : (if f e = v then (1 : ℤ) else 0) =
      (if s e = v then 1 else 0) -
      ((if s e = v then up e else 0) - (if t e = v then up e else 0)) := by
    rcases hallowed e with hh | hh
    · simp [← hh, up, hne e]
    · by_cases hv : t e = v
      · have hs : s e ≠ v := fun he => hne e (he.trans hv.symm)
        simp [← hh, up, hv, hs]
      · by_cases hs : s e = v <;> simp [← hh, up, hv, hs]
  have hc := hcount v
  simp_rw [hentry, sum_sub_distrib] at hc
  change (∑ e, if s e = v then (1 : ℤ) else 0) - divergence s t up v = (cap v : ℤ) at hc
  rw [hcap] at hc
  dsimp [raw] at hc
  rw [divergence_add]
  omega



def vertexBalance {R V E : Type*} [AddCommGroup R] [Fintype E] [DecidableEq V]
    (s t : E → V) (f : E → R) (v : V) : R :=
  ∑ e, ((if s e = v then f e else 0) - (if t e = v then f e else 0))

def degree {V E : Type*} [Fintype E] [DecidableEq V] (s t : E → V) (v : V) : ℕ :=
  (univ.filter fun e => s e = v ∨ t e = v).card

private theorem balance_total {R V E : Type*} [AddCommGroup R] [Fintype V] [Fintype E]
    [DecidableEq V] (s t : E → V) (f : E → R) :
    (∑ v, vertexBalance s t f v) = 0 := by
  unfold vertexBalance
  rw [sum_comm]
  simp [sum_sub_distrib]

private theorem balance_cut {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) (f : E → ℤ) (hf : ∀ e, f e = 1 ∨ f e = -1) (S : Finset V) :
    (∑ v ∈ S, vertexBalance s t f v) ≤
      ((univ.filter fun e => (s e ∈ S ∧ t e ∉ S) ∨ (t e ∈ S ∧ s e ∉ S)).card : ℤ) := by
  classical
  unfold vertexBalance
  rw [sum_comm]
  rw [card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_le_sum
  intro e _
  rw [sum_sub_distrib]
  have hsum (v : V) : (∑ x ∈ S, if v = x then f e else 0) =
      if v ∈ S then f e else 0 := by simp
  rw [hsum, hsum]
  rcases hf e with he | he <;> by_cases hs : s e ∈ S <;> by_cases ht : t e ∈ S <;>
    simp [he, hs, ht]

private theorem balance_as_count {V E : Type*} [Fintype E] [DecidableEq V]
    (s t : E → V) (hne : ∀ e, s e ≠ t e) (f : E → ℤ)
    (hf : ∀ e, f e = 1 ∨ f e = -1) (v : V) :
    ∃ n : ℕ, n ≤ degree s t v ∧ vertexBalance s t f v = 2 * (n : ℤ) - degree s t v := by
  classical
  let P := univ.filter fun e => (s e = v ∧ f e = 1) ∨ (t e = v ∧ f e = -1)
  let D := univ.filter fun e => s e = v ∨ t e = v
  have hPD : P ⊆ D := by
    intro e he
    rcases (mem_filter.mp he).2 with h | h
    · exact mem_filter.mpr ⟨mem_univ _, Or.inl h.1⟩
    · exact mem_filter.mpr ⟨mem_univ _, Or.inr h.1⟩
  refine ⟨P.card, card_le_card hPD, ?_⟩
  change vertexBalance s t f v = 2 * (P.card : ℤ) - D.card
  unfold vertexBalance P D
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  rcases hf e with he | he
  all_goals
    by_cases hs : s e = v
    · have ht : t e ≠ v := fun ht => hne e (hs.trans ht.symm)
      simp [he, hs, ht]
    · by_cases ht : t e = v <;> simp [he, hs, ht]

private theorem balance_seven_of_odd {V E : Type*} [Fintype E] [DecidableEq V]
    (s t : E → V) (hne : ∀ e, s e ≠ t e) (f : E → ℤ)
    (hf : ∀ e, f e = 1 ∨ f e = -1) (v : V)
    (hd : degree s t v = 11 ∨ degree s t v = 13)
    (hm : ((vertexBalance s t f v : ℤ) : ZMod 7) = 0) :
    vertexBalance s t f v = 7 ∨ vertexBalance s t f v = -7 := by
  obtain ⟨k, hk, hb⟩ := balance_as_count s t hne f hf v
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hm
  omega

abbrev BaseVertex := Fin 12
abbrev TriangleEdge := Fin 2 × Fin 3
abbrev CliqueEdge := {p : BaseVertex × BaseVertex // p.1 < p.2}
abbrev InnerEdge := CliqueEdge ⊕ TriangleEdge

def triangleVertex (b : Fin 2) (i : Fin 3) : BaseVertex :=
  ⟨3 + 3 * b.val + i.val, by omega⟩

def innerSrc : InnerEdge → BaseVertex
  | .inl p => p.val.1
  | .inr (b, i) => triangleVertex b i

def innerTgt : InnerEdge → BaseVertex
  | .inl p => p.val.2
  | .inr (b, i) => triangleVertex b (i + 1)

/-- The additional triangles account for exactly the vertices of degree thirteen. -/
theorem inner_degree (v : BaseVertex) :
    degree innerSrc innerTgt v = 11 ∨ degree innerSrc innerTgt v = 13 := by
  revert v
  decide

theorem inner_loopless : ∀ e, innerSrc e ≠ innerTgt e := by decide

def crosses (b : BaseVertex → Bool) (e : InnerEdge) : Bool :=
  b (innerSrc e) != b (innerTgt e)

private theorem inner_cut_card (b : BaseVertex → Bool) :
    (univ.filter fun e => crosses b e = true).card ≤ 40 := by
  classical
  let S : Finset BaseVertex := univ.filter fun v => b v = true
  let T : Finset BaseVertex := univ \ S
  let U : Finset CliqueEdge := univ.filter fun e => b e.val.1 ≠ b e.val.2
  let send (e : CliqueEdge) : BaseVertex × BaseVertex :=
    if b e.val.1 then e.val else e.val.swap
  have hsend : U.card ≤ (S ×ˢ T).card := by
    apply card_le_card_of_injOn send
    · intro e he
      have hn := (mem_filter.mp he).2
      simp only [send, S, T]
      cases hs : b e.val.1 <;> cases ht : b e.val.2 <;> simp_all
    · intro e _ f _ h
      have he := e.property
      have hf := f.property
      apply Subtype.ext
      cases hs : b e.val.1 <;> cases ht : b f.val.1 <;>
        simp only [send, hs, ht, Bool.false_eq_true, ↓reduceIte] at h
      · simpa only [Prod.swap_inj] using h
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        dsimp at h₁ h₂
        rw [← h₁, ← h₂] at hf
        exact (not_lt_of_gt he hf).elim
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        dsimp at h₁ h₂
        rw [h₁, h₂] at he
        exact (not_lt_of_gt hf he).elim
      · exact h
  have hST : T.card + S.card = 12 := by
    simpa [T] using card_sdiff_add_card_eq_card (subset_univ S)
  have hpart : S.card * T.card ≤ 36 := by
    have h := sq_nonneg ((S.card : ℤ) - 6)
    have hS : (S.card : ℤ) + (T.card : ℤ) = 12 := by exact_mod_cast ((add_comm S.card T.card).trans hST)
    have hle : (S.card : ℤ) * (T.card : ℤ) ≤ 36 := by nlinarith
    exact_mod_cast hle
  have hU : U.card ≤ 36 := hsend.trans (by rw [card_product]; exact hpart)
  have htriPair (x y z : Bool) :
      (if x ≠ y then (1 : ℕ) else 0) + (if y ≠ z then 1 else 0) +
        (if z ≠ x then 1 else 0) ≤ 2 := by revert x y z; decide
  have htri (i : Fin 2) : (∑ j : Fin 3,
      if b (triangleVertex i j) ≠ b (triangleVertex i (j + 1)) then (1 : ℕ) else 0) ≤ 2 := by
    rw [Fin.sum_univ_three]
    exact htriPair _ _ _
  have hv : (univ.filter fun e => crosses b e = true).card =
      U.card + ∑ i : Fin 2, ∑ j : Fin 3,
        if b (triangleVertex i j) ≠ b (triangleVertex i (j + 1)) then 1 else 0 := by
    simp only [card_filter, Fintype.sum_sum_type, Fintype.sum_prod_type, U,
      crosses, bne_iff_ne, innerSrc, innerTgt]
  rw [hv]
  have ht : (∑ i : Fin 2, ∑ j : Fin 3,
      if b (triangleVertex i j) ≠ b (triangleVertex i (j + 1)) then (1 : ℕ) else 0) ≤ 4 := by
    calc
      _ ≤ ∑ _ : Fin 2, (2 : ℕ) := sum_le_sum fun i _ => htri i
      _ = _ := by decide
  omega

set_option maxHeartbeats 900000 in
theorem inner_not_modulo_seven (f : InnerEdge → ℤ)
    (hf : ∀ e, f e = 1 ∨ f e = -1) :
    ¬ (∀ v, ((vertexBalance innerSrc innerTgt f v : ℤ) : ZMod 7) = 0) := by
  intro h
  classical
  let B (v : BaseVertex) := vertexBalance innerSrc innerTgt f v
  let S : Finset BaseVertex := univ.filter fun v => B v = 7
  have hbal (v : BaseVertex) : B v = 7 ∨ B v = -7 :=
    balance_seven_of_odd _ _ inner_loopless _ hf v (inner_degree v) (h v)
  have hcount : (S.card : ℤ) = 6 := by
    have htotal := balance_total innerSrc innerTgt f
    have hb (v : BaseVertex) : B v = 14 * (if B v = 7 then 1 else 0) - 7 := by
      rcases hbal v with h₁ | h₁ <;> simp [h₁]
    change (∑ v, B v) = 0 at htotal
    rw [show (∑ v, B v) = ∑ v, (14 * (if B v = 7 then 1 else 0) - 7) from
      sum_congr rfl fun v _ => hb v, sum_sub_distrib, ← mul_sum] at htotal
    have he : (∑ v : BaseVertex, if B v = 7 then (1 : ℤ) else 0) = S.card := by
      simp only [S, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [he] at htotal
    norm_num at htotal
    omega
  have hcut := balance_cut innerSrc innerTgt f hf S
  have hs : (∑ v ∈ S, B v) = 42 := by
    calc
      _ = ∑ _ ∈ S, (7 : ℤ) := sum_congr rfl fun v hv => (mem_filter.mp hv).2
      _ = _ := by simp [hcount]
  let b (v : BaseVertex) := decide (v ∈ S)
  have hrel (e : InnerEdge) :
      ((innerSrc e ∈ S ∧ innerTgt e ∉ S) ∨ (innerTgt e ∈ S ∧ innerSrc e ∉ S)) ↔
        crosses b e = true := by
    by_cases h₁ : innerSrc e ∈ S <;> by_cases h₂ : innerTgt e ∈ S <;>
      simp [crosses, b, h₁, h₂]
  simp_rw [hrel] at hcut
  change (∑ v ∈ S, B v) ≤ _ at hcut
  rw [hs] at hcut
  have hc := inner_cut_card b
  omega



/-- The sum of signs has the same parity as the number of signs. -/
private theorem sum_signs {I : Type*} [Fintype I] (f : I → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    ∃ k : ℕ, k ≤ Fintype.card I ∧ (∑ i, f i) = 2 * (k : ℤ) - Fintype.card I := by
  classical
  let S : Finset I := univ.filter fun i => f i = 1
  refine ⟨S.card, card_le_univ _, ?_⟩
  have hs (i : I) : f i = 2 * (if f i = 1 then (1 : ℤ) else 0) - 1 := by
    rcases hf i with h | h <;> simp [h]
  rw [show (∑ i, f i) = ∑ i, (2 * (if f i = 1 then (1 : ℤ) else 0) - 1) from
    sum_congr rfl fun i _ => hs i, sum_sub_distrib, ← mul_sum]
  have he : (∑ i, if f i = 1 then (1 : ℤ) else 0) = S.card := by
    simp only [S, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [he]
  simp

private theorem port_uniform (a : ℤ) (p : Fin 6 → ℤ)
    (ha : a = 1 ∨ a = -1) (hp : ∀ i, p i = 1 ∨ p i = -1)
    (hz : (a : ZMod 7) + ∑ i, (p i : ZMod 7) = 0) (i : Fin 6) : p i = a := by
  classical
  obtain ⟨k, hk, hs⟩ := sum_signs p hp
  have hcast : ((a + ∑ i, p i : ℤ) : ZMod 7) = 0 := by push_cast; exact hz
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hcast
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hk hs
  have hsum : (∑ j, p j) = 6 * a := by omega
  have hrest : (∑ j ∈ univ.erase i, p j) ≤ 5 ∧ -5 ≤ ∑ j ∈ univ.erase i, p j := by
    constructor
    · calc
        _ ≤ ∑ _ ∈ univ.erase i, (1 : ℤ) := sum_le_sum (fun j _ => (hp j).elim (by omega) (by omega))
        _ = 5 := by simp
    · calc
        (-5 : ℤ) = ∑ _ ∈ univ.erase i, (-1 : ℤ) := by simp
        _ ≤ _ := sum_le_sum (fun j _ => (hp j).elim (by omega) (by omega))
  have he := sum_erase_add (s := (univ : Finset (Fin 6))) p (mem_univ i)
  have hi := hp i
  omega

abbrev Connector := ZMod 13

def outerVertex (j : Fin 6) : BaseVertex :=
  ⟨if j.val < 3 then j.val else j.val + 6, by split <;> omega⟩

private theorem block_port_nonzero (f : InnerEdge → ℤ) (p q : Fin 6 → ℤ) (a : ℤ)
    (hf : ∀ e, f e = 1 ∨ f e = -1) (hp : ∀ j, p j = 1 ∨ p j = -1)
    (hq : ∀ j, q j = 1 ∨ q j = -1) (ha : a = 1 ∨ a = -1)
    (hB : ∀ v, ((vertexBalance innerSrc innerTgt f v : ℤ) : ZMod 7) =
      ∑ j, if outerVertex j = v then (p j : ZMod 7) + q j else 0) :
    (a : ZMod 7) + ∑ j, (p j : ZMod 7) ≠ 0 := by
  intro hpl
  have htotal : (∑ j, (p j : ZMod 7)) + ∑ j, (q j : ZMod 7) = 0 := by
    have hs := congrArg (fun g : BaseVertex → ZMod 7 => ∑ v, g v) (funext hB)
    change (∑ v, ((vertexBalance innerSrc innerTgt f v : ℤ) : ZMod 7)) =
      ∑ v, ∑ j, if outerVertex j = v then (p j : ZMod 7) + q j else 0 at hs
    rw [← Int.cast_sum, balance_total, Int.cast_zero, sum_comm] at hs
    simpa [sum_add_distrib] using hs.symm
  have hqr : ((-a : ℤ) : ZMod 7) + ∑ j, (q j : ZMod 7) = 0 := by
    push_cast
    linear_combination htotal - hpl
  have hp' := port_uniform a p ha hp hpl
  have hna : -a = 1 ∨ -a = -1 := by omega
  have hq' := port_uniform (-a) q hna hq hqr
  apply inner_not_modulo_seven f hf
  intro v
  rw [hB v]
  simp [hp', hq']

private theorem nonzero_as_five_signs (d : ZMod 7) (hd : d ≠ 0) :
    ∃ k : Fin 6, ((2 * (k.val : ℤ) - 5 : ℤ) : ZMod 7) = d := by
  revert d
  decide

/-- Nonzero block transfers and one signed edge per rim vertex cannot balance
around a cycle of length thirteen modulo seven. -/
theorem odd_wheel_obstruction (d : Connector → ZMod 7) (arc : Connector → ℤ)
    (hd : ∀ i, d i ≠ 0) (ha : ∀ i, arc i = 1 ∨ arc i = -1)
    (h : ∀ i, d i - d (i - 1) + (arc i : ZMod 7) = 0) : False := by
  choose k hk using fun i => nonzero_as_five_signs (d i) (hd i)
  let u (i : Connector) : ℤ := 2 * ((k i).val : ℤ) - 5
  let b (i : Connector) : ℤ := u i - u (i - 1) + arc i
  have hu (i : Connector) : -5 ≤ u i ∧ u i ≤ 5 := by
    have h := (k i).isLt
    dsimp [u]
    omega
  have hb (i : Connector) : b i = 7 ∨ b i = -7 := by
    have hz : (b i : ZMod 7) = 0 := by
      change ((u i - u (i - 1) + arc i : ℤ) : ZMod 7) = 0
      push_cast
      change (((2 * ((k i).val : ℤ) - 5 : ℤ) : ZMod 7) -
        ((2 * ((k (i - 1)).val : ℤ) - 5 : ℤ) : ZMod 7)) + (arc i : ZMod 7) = 0
      rw [hk, hk]
      exact h i
    obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
    have h₁ := hu i
    have h₂ := hu (i - 1)
    have h₃ := ha i
    dsimp [b] at hj ⊢
    dsimp [u] at hj ⊢
    omega
  have hp (i : Connector) : b i + b (i + 1) = 0 := by
    have hlu := hu (i + 1)
    have hru := hu (i - 1)
    have hi := hb i
    have hj := hb (i + 1)
    have he : b i + b (i + 1) = u (i + 1) - u (i - 1) + arc i + arc (i + 1) := by
      dsimp [b]
      rw [add_sub_cancel_right]
      ring
    have he₁ := ha i
    have he₂ := ha (i + 1)
    omega
  have hsumB := sum_signs (fun i => if b i = 7 then (1 : ℤ) else -1) (fun i => by split <;> simp)
  have he (i : Connector) : b i = 7 * (if b i = 7 then (1 : ℤ) else -1) := by
    rcases hb i with h₁ | h₁ <;> simp [h₁]
  have hz : (∑ i, b i) = 0 := by
    have hs : (∑ i, (b i + b (i + 1))) = 0 := by simp [hp]
    have hshift : (∑ i, b (i + 1)) = ∑ i, b i :=
      Equiv.sum_comp (Equiv.addRight (1 : Connector)) b
    rw [sum_add_distrib, hshift] at hs
    omega
  obtain ⟨j, _, hj⟩ := hsumB
  rw [show (∑ i, b i) = ∑ i, 7 * (if b i = 7 then (1 : ℤ) else -1) from
    sum_congr rfl fun i _ => he i, ← mul_sum, hj, ZMod.card] at hz
  omega


abbrev BlockEdge := InnerEdge ⊕ (Bool × Fin 6)
abbrev Vertex := (Connector × BaseVertex) ⊕ Option Connector
abbrev Edge := (Connector × BlockEdge) ⊕ Connector

def innerVertex (i : Connector) (v : BaseVertex) : Vertex := .inl (i, v)
def rimVertex (i : Connector) : Vertex := .inr (some i)
def centre : Vertex := .inr none

def localPort (i : Connector) (right : Bool) : Connector := if right then i + 1 else i

def src : Edge → Vertex
  | .inl (i, .inl e) => innerVertex i (innerSrc e)
  | .inl (i, .inr (b, _)) => rimVertex (localPort i b)
  | .inr i => rimVertex i

def tgt : Edge → Vertex
  | .inl (i, .inl e) => innerVertex i (innerTgt e)
  | .inl (i, .inr (_, j)) => innerVertex i (outerVertex j)
  | .inr _ => centre

private theorem loopless : ∀ e, src e ≠ tgt e := by
  intro e
  rcases e with ⟨i, e⟩ | i
  · rcases e with e | ⟨b, j⟩
    · simpa [src, tgt, innerVertex] using inner_loopless e
    · simp [src, tgt, innerVertex, rimVertex]
  · simp [src, tgt, rimVertex, centre]

def blockWeight {R : Type*} (f : Edge → R) (i : Connector) (e : InnerEdge) : R :=
  f (.inl (i, .inl e))

def portWeight {R : Type*} (f : Edge → R) (i : Connector) (b : Bool) (j : Fin 6) : R :=
  f (.inl (i, .inr (b, j)))

def spokeWeight {R : Type*} (f : Edge → R) (i : Connector) : R := f (.inr i)

private theorem balance_inside {R : Type*} [AddCommGroup R] (f : Edge → R)
    (i : Connector) (v : BaseVertex) :
    vertexBalance src tgt f (innerVertex i v) =
      vertexBalance innerSrc innerTgt (blockWeight f i) v -
        ∑ j, if outerVertex j = v then portWeight f i false j + portWeight f i true j else 0 := by
  simp only [vertexBalance, Fintype.sum_sum_type, Fintype.sum_prod_type, src, tgt,
    innerVertex, rimVertex, centre, Sum.inl.injEq, Prod.mk.injEq,
    reduceCtorEq, if_false, sub_zero, zero_sub, sum_const_zero, add_zero,
    Fintype.sum_bool, blockWeight, portWeight]
  simp_rw [ite_and, sum_add_distrib, sum_sub_distrib, sum_ite_irrel, sum_neg_distrib]
  have splitPort (j : Fin 6) :
      (if outerVertex j = v then f (Sum.inl (i, Sum.inr (false, j))) +
          f (Sum.inl (i, Sum.inr (true, j))) else 0) =
        (if outerVertex j = v then f (Sum.inl (i, Sum.inr (false, j))) else 0) +
          (if outerVertex j = v then f (Sum.inl (i, Sum.inr (true, j))) else 0) := by
    split <;> simp
  simp [splitPort, sum_add_distrib]
  abel

private theorem balance_rim {R : Type*} [AddCommGroup R] (f : Edge → R) (i : Connector) :
    vertexBalance src tgt f (rimVertex i) =
      (∑ j, portWeight f i false j) + (∑ j, portWeight f (i - 1) true j) + spokeWeight f i := by
  simp only [vertexBalance, Fintype.sum_sum_type, Fintype.sum_prod_type, src, tgt,
    innerVertex, rimVertex, centre, Sum.inr.injEq, reduceCtorEq,
    Option.some.injEq, sub_zero, sum_const_zero, zero_add,
    Fintype.sum_bool, localPort, Bool.false_eq_true, ↓reduceIte, portWeight, spokeWeight]
  have hshift (a : Connector) : a + 1 = i ↔ a = i - 1 := eq_sub_iff_add_eq.symm
  simp_rw [hshift, sum_add_distrib, sum_ite_irrel]
  simp [add_comm]

private theorem balance_centre {R : Type*} [AddCommGroup R] (f : Edge → R) :
    vertexBalance src tgt f centre = - ∑ i, spokeWeight f i := by
  simp only [vertexBalance, Fintype.sum_sum_type, Fintype.sum_prod_type, src, tgt,
    innerVertex, rimVertex, centre, Sum.inr.injEq, reduceCtorEq, if_false,
    sub_zero, sum_const_zero, zero_add, spokeWeight, zero_sub, sum_neg_distrib, if_true]

private theorem cast_balance (f : Edge → ℤ) (v : Vertex) :
    ((vertexBalance src tgt f v : ℤ) : ZMod 7) =
      vertexBalance src tgt (fun e => (f e : ZMod 7)) v := by
  unfold vertexBalance
  push_cast
  rfl

private theorem nonmodular (f : Edge → ℤ) (hf : ∀ e, f e = 1 ∨ f e = -1) :
    ¬ ∀ v, ((vertexBalance src tgt f v : ℤ) : ZMod 7) = 0 := by
  intro h
  let g (e : Edge) := (f e : ZMod 7)
  let left (i : Connector) := ∑ j, portWeight g i false j
  let right (i : Connector) := ∑ j, portWeight g i true j
  let arc := spokeWeight f
  have hf' (v : Vertex) : vertexBalance src tgt g v = 0 := (cast_balance f v).symm.trans (h v)
  have hinner (i : Connector) (v : BaseVertex) :
      ((vertexBalance innerSrc innerTgt (blockWeight f i) v : ℤ) : ZMod 7) =
        ∑ j, if outerVertex j = v then portWeight g i false j + portWeight g i true j else 0 := by
    have hh := hf' (innerVertex i v)
    rw [balance_inside] at hh
    unfold vertexBalance
    push_cast
    exact sub_eq_zero.mp hh
  have hsum (i : Connector) : left i + right i = 0 := by
    have hs := congrArg (fun g : BaseVertex → ZMod 7 => ∑ v, g v) (funext (hinner i))
    change (∑ v, ((vertexBalance innerSrc innerTgt (blockWeight f i) v : ℤ) : ZMod 7)) =
      ∑ v, ∑ j, if outerVertex j = v then portWeight g i false j + portWeight g i true j else 0 at hs
    rw [← Int.cast_sum, balance_total, Int.cast_zero, sum_comm] at hs
    simpa [left, right, sum_add_distrib] using hs.symm
  have hr (i : Connector) : left i + right (i - 1) + (arc i : ZMod 7) = 0 := by
    simpa [left, right, arc, g, spokeWeight, balance_rim] using hf' (rimVertex i)
  let d (i : Connector) := (arc i : ZMod 7) + left i
  have hd (i : Connector) : d i ≠ 0 := block_port_nonzero (blockWeight f i)
    (portWeight f i false) (portWeight f i true) (arc i)
    (fun e => hf _) (fun j => hf _) (fun j => hf _) (hf _) (hinner i)
  apply odd_wheel_obstruction d (fun i => arc (i - 1)) hd (fun i => hf _)
  intro i
  dsimp [d]
  linear_combination hr i - hsum (i - 1)

/-! ## 12-edge-connectivity -/

instance : DecidableEq InnerEdge := instDecidableEqSum
instance : DecidableEq BlockEdge := instDecidableEqSum
instance : DecidableEq Edge := instDecidableEqSum

def cE (i : Connector) (p q : ℕ) : Edge :=
  if h : p < q ∧ q < 12 then
    .inl (i, .inl (.inl ⟨(⟨p, by omega⟩, ⟨q, h.2⟩), Fin.mk_lt_mk.mpr h.1⟩))
  else .inr 0

def tE (i : Connector) (b : Fin 2) (k : Fin 3) : Edge := .inl (i, .inl (.inr (b, k)))

def pE (i : Connector) (b : Bool) (j : Fin 6) : Edge := .inl (i, .inr (b, j))

def sE (i : Connector) : Edge := .inr i

/-- `l` is a walk from `u` to `w`, each edge traversed in either direction. -/
def walkOK : Vertex → List Edge → Vertex → Bool
  | u, [], w => decide (u = w)
  | u, e :: l, w =>
      if src e = u then walkOK (tgt e) l w else if tgt e = u then walkOK (src e) l w else false

def cert : List (Vertex × List (List Edge)) := [
  (rimVertex 0, [
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, pE 0 false 5],
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 4, pE 0 false 4],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 3, pE 0 false 3],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 2, pE 0 false 2],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 1, pE 0 false 1],
    [sE 12, pE 12 false 0, pE 12 true 0],
    [sE 1, pE 0 true 0, pE 0 false 0],
    [sE 0]]),
  (innerVertex 0 0, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 5, cE 0 7 11, cE 0 0 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 4, cE 0 6 10, cE 0 0 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 3, cE 0 5 9, cE 0 0 5],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 2, cE 0 2 4, cE 0 0 4],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 3, cE 0 0 3],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 5, cE 0 0 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 4, cE 0 0 10],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 3, cE 0 0 9],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 2, cE 0 0 2],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 1, cE 0 0 1],
    [sE 1, pE 0 true 0],
    [sE 0, pE 0 false 0]]),
  (innerVertex 0 1, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 5, cE 0 7 11, cE 0 1 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 4, cE 0 6 10, cE 0 1 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 3, cE 0 5 9, cE 0 1 5],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 2, cE 0 2 4, cE 0 1 4],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 0, cE 0 0 3, cE 0 1 3],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 5, cE 0 1 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 4, cE 0 1 10],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 3, cE 0 1 9],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 2, cE 0 1 2],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 0, cE 0 0 1],
    [sE 1, pE 0 true 1],
    [sE 0, pE 0 false 1]]),
  (innerVertex 0 2, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 5, cE 0 7 11, cE 0 2 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 4, cE 0 6 10, cE 0 2 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 3, cE 0 5 9, cE 0 2 5],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 1, cE 0 1 4, cE 0 2 4],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 0, cE 0 0 3, cE 0 2 3],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 5, cE 0 2 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 4, cE 0 2 10],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 3, cE 0 2 9],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 1, cE 0 1 2],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 0, cE 0 0 2],
    [sE 1, pE 0 true 2],
    [sE 0, pE 0 false 2]]),
  (innerVertex 0 3, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 7 10, cE 0 3 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 6 11, cE 0 3 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 5, tE 0 0 2],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 5 9, cE 0 3 5],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 4, tE 0 0 0],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 4, cE 0 3 4],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 3 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 3 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 3 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 3],
    [sE 1, pE 0 true 1, cE 0 1 3],
    [sE 0, pE 0 false 0, cE 0 0 3]]),
  (innerVertex 0 4, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 7 10, cE 0 4 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 6 11, cE 0 4 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 5, tE 0 0 1],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 5 9, cE 0 4 5],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 3, tE 0 0 0],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 3, cE 0 3 4],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 4 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 4 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 4 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 4],
    [sE 1, pE 0 true 1, cE 0 1 4],
    [sE 0, pE 0 false 0, cE 0 0 4]]),
  (innerVertex 0 5, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 7 10, cE 0 5 7],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 6 11, cE 0 5 6],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 4, tE 0 0 1],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 4 9, cE 0 4 5],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 3, tE 0 0 2],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 3, cE 0 3 5],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 5 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 5 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 5 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 5],
    [sE 1, pE 0 true 1, cE 0 1 5],
    [sE 0, pE 0 false 0, cE 0 0 5]]),
  (innerVertex 0 6, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 8 10, cE 0 6 8],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 7 11, tE 0 1 0],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 7, cE 0 6 7],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 5 9, cE 0 5 6],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 4, cE 0 4 6],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 3, cE 0 3 6],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 6 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 6 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 6 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 6],
    [sE 1, pE 0 true 1, cE 0 1 6],
    [sE 0, pE 0 false 0, cE 0 0 6]]),
  (innerVertex 0 7, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 8 10, cE 0 7 8],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 6 11, tE 0 1 0],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 6, cE 0 6 7],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 5 9, cE 0 5 7],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 4, cE 0 4 7],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 3, cE 0 3 7],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 7 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 7 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 7 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 7],
    [sE 1, pE 0 true 1, cE 0 1 7],
    [sE 0, pE 0 false 0, cE 0 0 7]]),
  (innerVertex 0 8, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 7 10, cE 0 7 8],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 5, cE 0 6 11, tE 0 1 2],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 6, cE 0 6 8],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 3, cE 0 5 9, cE 0 5 8],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 1, cE 0 1 4, cE 0 4 8],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 0, cE 0 0 3, cE 0 3 8],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 5, cE 0 8 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 4, cE 0 8 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 3, cE 0 8 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 2, cE 0 2 8],
    [sE 1, pE 0 true 1, cE 0 1 8],
    [sE 0, pE 0 false 0, cE 0 0 8]]),
  (innerVertex 0 9, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 5, cE 0 7 11, cE 0 7 9],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 4, cE 0 6 10, cE 0 6 9],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 5, cE 0 5 9],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 1, cE 0 1 4, cE 0 4 9],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 0, cE 0 0 3, cE 0 3 9],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 5, cE 0 9 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 4, cE 0 9 10],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 2, cE 0 2 9],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 1, cE 0 1 9],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 0, cE 0 0 9],
    [sE 1, pE 0 true 3],
    [sE 0, pE 0 false 3]]),
  (innerVertex 0 10, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 5, cE 0 7 11, cE 0 7 10],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 3, cE 0 6 9, cE 0 6 10],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 5, cE 0 5 10],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 1, cE 0 1 4, cE 0 4 10],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 0, cE 0 0 3, cE 0 3 10],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 5, cE 0 10 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 3, cE 0 9 10],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 2, cE 0 2 10],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 1, cE 0 1 10],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 0, cE 0 0 10],
    [sE 1, pE 0 true 4],
    [sE 0, pE 0 false 4]]),
  (innerVertex 0 11, [
    [sE 8, pE 8 false 0, pE 8 true 0, pE 9 false 1, pE 9 true 1, pE 10 false 2, pE 10 true 2, pE 11 false 3, pE 11 true 3, pE 12 false 4, pE 12 true 4, pE 0 false 4, cE 0 7 10, cE 0 7 11],
    [sE 6, pE 5 true 0, pE 5 false 0, pE 4 true 1, pE 4 false 1, pE 3 true 2, pE 3 false 2, pE 2 true 3, pE 2 false 3, pE 1 true 4, pE 1 false 4, pE 0 true 3, cE 0 6 9, cE 0 6 11],
    [sE 9, pE 9 false 0, pE 9 true 0, pE 10 false 1, pE 10 true 1, pE 11 false 2, pE 11 true 2, pE 12 false 3, pE 12 true 3, pE 0 false 2, cE 0 2 5, cE 0 5 11],
    [sE 5, pE 4 true 0, pE 4 false 0, pE 3 true 1, pE 3 false 1, pE 2 true 2, pE 2 false 2, pE 1 true 3, pE 1 false 3, pE 0 true 1, cE 0 1 4, cE 0 4 11],
    [sE 10, pE 10 false 0, pE 10 true 0, pE 11 false 1, pE 11 true 1, pE 12 false 2, pE 12 true 2, pE 0 false 0, cE 0 0 3, cE 0 3 11],
    [sE 4, pE 3 true 0, pE 3 false 0, pE 2 true 1, pE 2 false 1, pE 1 true 2, pE 1 false 2, pE 0 true 4, cE 0 10 11],
    [sE 11, pE 11 false 0, pE 11 true 0, pE 12 false 1, pE 12 true 1, pE 0 false 3, cE 0 9 11],
    [sE 3, pE 2 true 0, pE 2 false 0, pE 1 true 1, pE 1 false 1, pE 0 true 2, cE 0 2 11],
    [sE 12, pE 12 false 0, pE 12 true 0, pE 0 false 1, cE 0 1 11],
    [sE 2, pE 1 true 0, pE 1 false 0, pE 0 true 0, cE 0 0 11],
    [sE 1, pE 0 true 5],
    [sE 0, pE 0 false 5]])
]


def certOK : Bool :=
  cert.all fun p => p.2.length == 12 && p.2.all (fun l => walkOK centre l p.1) &&
    decide p.2.flatten.Nodup

set_option maxRecDepth 100000 in
theorem cert_ok : certOK = true := by decide +kernel

def coversOK : Bool :=
  (cert.map Prod.fst).any (fun x => decide (x = rimVertex 0)) &&
    (List.finRange 12).all fun v => (cert.map Prod.fst).any (fun x => decide (x = innerVertex 0 v))

theorem covers_ok : coversOK = true := by decide +kernel

theorem mem_of_any {l : List Vertex} {y : Vertex}
    (h : l.any (fun x => decide (x = y)) = true) : y ∈ l := by
  obtain ⟨x, hx, hxy⟩ := List.any_eq_true.mp h
  rw [decide_eq_true_eq] at hxy
  exact hxy ▸ hx

theorem cert_covers : rimVertex 0 ∈ cert.map Prod.fst ∧
    ∀ v : BaseVertex, innerVertex 0 v ∈ cert.map Prod.fst := by
  have h := covers_ok
  simp only [coversOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨mem_of_any h.1, fun v => mem_of_any (h.2 v (List.mem_finRange v))⟩

open OMA.S_opg_jaegers_modular_orientation_conjecture in
theorem walk_reach (S : Set Edge) : ∀ (l : List Edge) (u w : Vertex), walkOK u l w = true →
    (∀ e ∈ l, e ∉ S) → (underlying src tgt S).Reachable u w := by
  intro l
  induction l with
  | nil =>
    intro u w h _
    have : u = w := by simpa [walkOK] using h
    subst this; rfl
  | cons e l ih =>
    intro u w h hS
    have heS : e ∉ S := hS e (by simp)
    have hlS : ∀ e' ∈ l, e' ∉ S := fun e' he' => hS e' (by simp [he'])
    by_cases h1 : src e = u
    · simp only [walkOK, h1, if_true] at h
      have hadj : (underlying src tgt S).Adj u (tgt e) := by
        rw [underlying, SimpleGraph.fromRel_adj]
        exact ⟨h1 ▸ loopless e, Or.inl ⟨e, heS, h1, rfl⟩⟩
      exact hadj.reachable.trans (ih _ _ h hlS)
    · by_cases h2 : tgt e = u
      · simp only [walkOK, h1, h2, if_true, if_false] at h
        have hadj : (underlying src tgt S).Adj u (src e) := by
          rw [underlying, SimpleGraph.fromRel_adj]
          exact ⟨fun h' => loopless e (h'.symm.trans h2.symm),
            Or.inr ⟨e, heS, rfl, h2⟩⟩
        exact hadj.reachable.trans (ih _ _ h hlS)
      · simp [walkOK, h1, h2] at h

theorem le_length_filter_flatten {α : Type*} (p : α → Bool) :
    ∀ ps : List (List α), (∀ l ∈ ps, ∃ e ∈ l, p e = true) →
      ps.length ≤ (ps.flatten.filter p).length := by
  intro ps
  induction ps with
  | nil => simp
  | cons l ps ih =>
    intro h
    obtain ⟨e, he, hpe⟩ := h l (by simp)
    have h1 : 0 < (l.filter p).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨he, hpe⟩)
    have h2 := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [List.flatten_cons, List.filter_append, List.length_append, List.length_cons]
    omega

theorem pigeon (ps : List (List Edge)) (hlen : ps.length = 12) (hnd : ps.flatten.Nodup)
    (S : Finset Edge) (hS : S.card < 12) : ∃ l ∈ ps, ∀ e ∈ l, e ∉ S := by
  classical
  by_contra hcon
  push Not at hcon
  have hle := le_length_filter_flatten (fun e => decide (e ∈ S)) ps
    (fun l hl => by obtain ⟨e, he, heS⟩ := hcon l hl; exact ⟨e, he, by simpa using heS⟩)
  set F := ps.flatten.filter (fun e => decide (e ∈ S))
  have hFnd : F.Nodup := hnd.filter _
  have hsub : F.toFinset ⊆ S := by
    intro e he
    simpa [F] using (List.mem_filter.mp (List.mem_toFinset.mp he)).2
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hFnd] at this
  omega

def shV (c : Connector) : Vertex → Vertex
  | .inl (i, v) => .inl (i + c, v)
  | .inr (some i) => .inr (some (i + c))
  | .inr none => .inr none

def shE (c : Connector) : Edge → Edge
  | .inl (i, be) => .inl (i + c, be)
  | .inr i => .inr (i + c)

theorem src_shE (c : Connector) (e : Edge) : src (shE c e) = shV c (src e) := by
  rcases e with ⟨i, e | ⟨b, j⟩⟩ | i
  · simp [shE, shV, src, innerVertex]
  · cases b <;> simp [shE, shV, src, rimVertex, localPort, add_right_comm]
  · simp [shE, shV, src, rimVertex]

theorem tgt_shE (c : Connector) (e : Edge) : tgt (shE c e) = shV c (tgt e) := by
  rcases e with ⟨i, e | ⟨b, j⟩⟩ | i
  · simp [shE, shV, tgt, innerVertex]
  · simp [shE, shV, tgt, innerVertex]
  · simp [shE, shV, tgt, centre]

theorem shV_injective (c : Connector) : Function.Injective (shV c) := by
  have : Function.LeftInverse (shV (-c)) (shV c) := by
    intro x; rcases x with ⟨i, v⟩ | (_ | i) <;> simp [shV]
  exact this.injective

theorem shE_injective (c : Connector) : Function.Injective (shE c) := by
  have : Function.LeftInverse (shE (-c)) (shE c) := by
    intro x; rcases x with ⟨i, e⟩ | i <;> simp [shE]
  exact this.injective

open OMA.S_opg_jaegers_modular_orientation_conjecture in
theorem reach_shift (S : Finset Edge) (hS : S.card < 12) (c : Connector) (w : Vertex)
    (hw : w ∈ cert.map Prod.fst) :
    (underlying src tgt (S : Set Edge)).Reachable centre (shV c w) := by
  classical
  obtain ⟨⟨w', ps⟩, hmem, rfl⟩ := List.mem_map.mp hw
  have hok := List.all_eq_true.mp cert_ok (w', ps) hmem
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hlen, hwalks⟩, hnd⟩ := hok
  let S' : Finset Edge := Finset.univ.filter fun e => shE c e ∈ S
  have hS' : S'.card ≤ S.card :=
    Finset.card_le_card_of_injOn (shE c) (fun e he => by simpa [S'] using he)
      (fun a _ b _ h => shE_injective c h)
  obtain ⟨l, hl, hlS⟩ := pigeon ps hlen hnd S' (by omega)
  have hr := walk_reach (S' : Set Edge) l centre w' (hwalks l hl)
    (fun e he => by simpa using hlS e he)
  let φ : underlying src tgt (S' : Set Edge) →g underlying src tgt (S : Set Edge) :=
    { toFun := shV c
      map_rel' := by
        intro u v huv
        rw [underlying, SimpleGraph.fromRel_adj] at huv ⊢
        obtain ⟨hne, h | h⟩ := huv
        · obtain ⟨e, heS, hs, ht⟩ := h
          refine ⟨fun h' => hne (shV_injective c h'), Or.inl ⟨shE c e, ?_, ?_, ?_⟩⟩
          · simpa [S'] using heS
          · rw [src_shE, hs]
          · rw [tgt_shE, ht]
        · obtain ⟨e, heS, hs, ht⟩ := h
          refine ⟨fun h' => hne (shV_injective c h'), Or.inr ⟨shE c e, ?_, ?_, ?_⟩⟩
          · simpa [S'] using heS
          · rw [src_shE, hs]
          · rw [tgt_shE, ht] }
  have := hr.map φ
  simpa [φ, shV, centre] using this

open OMA.S_opg_jaegers_modular_orientation_conjecture in
theorem reach_centre (S : Finset Edge) (hS : S.card < 12) (x : Vertex) :
    (underlying src tgt (S : Set Edge)).Reachable centre x := by
  rcases x with ⟨i, v⟩ | (_ | i)
  · simpa [shV, innerVertex] using reach_shift S hS i (innerVertex 0 v) (cert_covers.2 v)
  · rfl
  · simpa [shV, rimVertex] using reach_shift S hS i (rimVertex 0) cert_covers.1

open OMA.S_opg_jaegers_modular_orientation_conjecture in
theorem edge_connected : IsEdgeConnected src tgt 12 := by
  intro S hS
  have : Nonempty Vertex := ⟨centre⟩
  exact ⟨fun u w => (reach_centre S hS u).symm.trans (reach_centre S hS w)⟩

end JaegerCounterexample

open JaegerCounterexample OMA.S_opg_jaegers_modular_orientation_conjecture in
theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_jaegers_modular_orientation_conjecture.main) := by
  intro h
  obtain ⟨o, ho⟩ := h 3 (by norm_num) Vertex Edge src tgt edge_connected
  let f : Edge → ℤ := fun e => if o e then 1 else -1
  apply nonmodular f (fun e => by by_cases h : o e <;> simp [f, h])
  intro v
  have key : vertexBalance src tgt f v =
      -(((Finset.univ.filter fun e => head src tgt o e = v).card : ℤ) -
        (Finset.univ.filter fun e => tail src tgt o e = v).card) := by
    unfold vertexBalance
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hoe : o e <;> by_cases h1 : src e = v <;> by_cases h2 : tgt e = v <;>
      simp [f, head, tail, hoe, h1, h2]
  have hv := ho v
  have h7 : (7 : ℤ) ∣ ((Finset.univ.filter fun e => head src tgt o e = v).card : ℤ) -
      (Finset.univ.filter fun e => tail src tgt o e = v).card := by
    have := Int.ModEq.dvd hv.symm
    simpa using this
  rw [key, Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast h7
