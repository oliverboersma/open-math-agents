import OMAStatements.S_opg_circular_flow_numbers_of_r_graphs
import Mathlib

/-!
# A counterexample to Steffen's circular flow bound for r-graphs

Every `(2t+1)`-regular class 1 graph is a `(2t+1)`-graph: each colour class is a perfect matching
and so crosses every odd cut. Hence a 13-regular class 1 graph with circular flow number greater
than `7/3 = 2 + 2/6` refutes the bound for `t = 6`.

The construction and the bound on its circular flow number are taken from the proof of
opg-circular-flow-number-of-regular-class-1-graphs in PR #7972 by AkiRA-COM-FP, which formalizes
the p = 3 case of Mattiolo and Steffen, Edge colorings and circular flows on regular graphs,
arXiv:2001.02484, Section 3, with the modulo-seven obstruction of Han, Li, Wu and Zhang,
Counterexamples to Jaeger's Circular Flow Conjecture, JCTB 131 (2018), Section 3.
New here: the odd-cut lemma `oddCut_of_coloring` and the final step.
-/

noncomputable section

namespace RGraphCounterexample

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

/-- A circulation in the clique and the two extra triangles provides nonzero
values on all internal edges. -/
def internalFlow : InnerEdge → ℤ
  | .inl e =>
    let g (i : BaseVertex) : ℤ := if i = 11 then -11 else 1
    let h (i : BaseVertex) : ℤ := if i = 11 then -2047 else 2 ^ i.val
    g e.val.1 * h e.val.2 - g e.val.2 * h e.val.1
  | .inr _ => 1

set_option maxRecDepth 3000 in
private theorem internal_balance : ∀ v, vertexBalance innerSrc innerTgt internalFlow v = 0 := by
  decide

private theorem internal_nonzero : ∀ e, internalFlow e ≠ 0 := by decide

def coreValue (i : Connector) : ℤ := (i.val : ℤ) + 1

def concreteFlow : Edge → ℤ
  | .inl (_, .inl e) => internalFlow e
  | .inl (i, .inr (b, _)) => if b then -coreValue i else coreValue i
  | .inr i => 6 * (coreValue (i - 1) - coreValue i)

private theorem concrete_balance (v : Vertex) : vertexBalance src tgt concreteFlow v = 0 := by
  rcases v with ⟨i, v⟩ | i
  · change vertexBalance src tgt concreteFlow (innerVertex i v) = 0
    rw [balance_inside]
    change vertexBalance innerSrc innerTgt internalFlow v -
      (∑ j, if outerVertex j = v then coreValue i + -coreValue i else 0) = 0
    simp [internal_balance]
  · cases i with
    | none =>
      change vertexBalance src tgt concreteFlow centre = 0
      rw [balance_centre]
      have h : (∑ i : Connector, coreValue (i - 1)) = ∑ i, coreValue i := by
        simpa [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-1 : Connector)) coreValue
      change -(∑ i : Connector, (6 : ℤ) * (coreValue (i - 1) - coreValue i)) = 0
      rw [← mul_sum, sum_sub_distrib, h, sub_self, mul_zero, neg_zero]
    | some i =>
      change vertexBalance src tgt concreteFlow (rimVertex i) = 0
      rw [balance_rim]
      simp only [portWeight, spokeWeight, concreteFlow, Bool.false_eq_true, ↓reduceIte,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring

private theorem nonzero_spokes (i : Connector) :
    coreValue (i - 1) - coreValue i ≠ 0 := by revert i; decide

private theorem concrete_nonzero (e : Edge) : concreteFlow e ≠ 0 := by
  rcases e with ⟨i, e⟩ | i
  · rcases e with e | ⟨b, j⟩
    · exact internal_nonzero e
    · have hp : 0 < coreValue i := by unfold coreValue; positivity
      cases b <;> simp [concreteFlow, hp.ne']
  · exact mul_ne_zero (by norm_num) (nonzero_spokes i)


def edgeOn (a b : BaseVertex) (e : CliqueEdge) : Bool :=
  (e.val.1 == a && e.val.2 == b) || (e.val.1 == b && e.val.2 == a)

def recoloredCycle (v : Fin 6 → BaseVertex) (e : CliqueEdge) : Option (Fin 13) :=
  ((List.finRange 6).find? fun i => edgeOn (v i) (v (i + 1)) e).map
    (fun i => if i.val % 2 = 0 then 11 else 12)

def rawCliqueColor (e : CliqueEdge) : Fin 13 :=
  ((recoloredCycle ![3, 8, 4, 6, 5, 7] e).or (recoloredCycle ![0, 1, 2, 11, 9, 10] e)).getD
    (if e.val.2 = 11 then ⟨e.val.1.val, by omega⟩ else
      ⟨6 * (e.val.1.val + e.val.2.val) % 11, by omega⟩)

def palette (c : Fin 13) : Connector := ![0, 2, 5, 4, 9, 11, 1, 3, 6, 7, 8, 10, 12] c

def blockColor : BlockEdge → Connector
  | .inl (.inl e) => palette (rawCliqueColor e)
  | .inl (.inr (_, i)) => palette (![5, 6, 0] i)
  | .inr (false, j) => palette (![6, 7, 2, 4, 5, 9] j)
  | .inr (true, j) => palette (![5, 6, 7, 9, 4, 2] j)

def color : Edge → Connector
  | .inl (i, e) => i + blockColor e
  | .inr i => i + 12

def localHit (v : BaseVertex) : BlockEdge → Bool
  | .inl e => innerSrc e == v || innerTgt e == v
  | .inr (_, j) => outerVertex j == v

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem one_local_edge (v : BaseVertex) (k : Connector) :
    (univ.filter fun e : BlockEdge => localHit v e = true ∧ blockColor e = k).card = 1 := by
  revert v k
  decide

def insideEdge (i : Connector) (e : BlockEdge) : Edge := .inl (i, e)

def rimEdge (i : Connector) : ((Bool × Fin 6) ⊕ Unit) → Edge
  | .inl (false, j) => .inl (i, .inr (false, j))
  | .inl (true, j) => .inl (i - 1, .inr (true, j))
  | .inr _ => .inr i

def rimColor : ((Bool × Fin 6) ⊕ Unit) → Connector
  | .inl (false, j) => blockColor (.inr (false, j))
  | .inl (true, j) => blockColor (.inr (true, j)) - 1
  | .inr _ => 12

private theorem rim_color_bijective : Function.Bijective rimColor := by decide

private theorem rim_edge_color (i : Connector) (e : (Bool × Fin 6) ⊕ Unit) :
    color (rimEdge i e) = i + rimColor e := by
  rcases e with ⟨b, j⟩ | j
  · cases b
    · rfl
    · simp only [rimEdge, rimColor, color]
      ring
  · rfl

def incident (v : Vertex) (e : Edge) : Prop := src e = v ∨ tgt e = v

private theorem incident_inside_iff (i : Connector) (v : BaseVertex) (e : Edge) :
    incident (innerVertex i v) e ↔
      ∃ a : BlockEdge, e = insideEdge i a ∧ localHit v a = true := by
  constructor
  · rcases e with ⟨i', e⟩ | i'
    · rcases e with e | ⟨b, j⟩
      · intro h
        have hh : i' = i ∧ (innerSrc e = v ∨ innerTgt e = v) := by
          simpa only [incident, src, tgt, innerVertex, Sum.inl.injEq, Prod.mk.injEq,
            and_or_left] using h
        obtain ⟨rfl, he⟩ := hh
        exact ⟨.inl e, rfl, by simpa [localHit] using he⟩
      · intro h
        have hh : i' = i ∧ outerVertex j = v := by
          simpa [incident, src, tgt, innerVertex, rimVertex] using h
        obtain ⟨rfl, hj⟩ := hh
        exact ⟨.inr (b, j), rfl, by simpa [localHit] using hj⟩
    · simp [incident, src, tgt, innerVertex, rimVertex, centre]
  · rintro ⟨a, rfl, ha⟩
    rcases a with a | ⟨b, j⟩
    · simpa [incident, insideEdge, src, tgt, innerVertex, localHit] using ha
    · simpa [incident, insideEdge, src, tgt, innerVertex, rimVertex, localHit] using ha

private theorem incident_rim_iff (i : Connector) (e : Edge) :
    incident (rimVertex i) e ↔ ∃ e', e = rimEdge i e' := by
  rcases e with ⟨i', e⟩ | i'
  · rcases e with e | ⟨b, j⟩
    · constructor
      · simp [incident, src, tgt, innerVertex, rimVertex]
      · rintro ⟨⟨b, k⟩ | _, h⟩
        · cases b <;> simp [rimEdge] at h
        · simp [rimEdge] at h
    · cases b
      · constructor
        · intro h
          have hi : i' = i := by simpa [incident, src, tgt, innerVertex, rimVertex, localPort] using h
          subst i'
          exact ⟨.inl (false, j), rfl⟩
        · rintro ⟨⟨b, k⟩ | _, h⟩
          · cases b <;> simp_all [rimEdge, incident, src, tgt, localPort, rimVertex]
          · simp [rimEdge] at h
      · constructor
        · intro h
          have hi : i' + 1 = i := by simpa [incident, src, tgt, innerVertex, rimVertex, localPort] using h
          rw [← hi]
          exact ⟨.inl (true, j), by simp [rimEdge]⟩
        · rintro ⟨⟨b, k⟩ | _, h⟩
          · cases b <;> simp_all [rimEdge, incident, src, tgt, localPort, rimVertex]
          · simp [rimEdge] at h
  · constructor
    · intro h
      have hi : i' = i := by simpa [incident, src, tgt, centre, rimVertex] using h
      exact ⟨.inr (), hi ▸ rfl⟩
    · rintro ⟨⟨b, j⟩ | _, h⟩
      · cases b <;> simp [rimEdge] at h
      · simpa [rimEdge, incident, src, tgt, centre, rimVertex] using h

private theorem incident_centre_iff (e : Edge) :
    incident centre e ↔ ∃ i, e = Sum.inr i := by
  rcases e with ⟨i, e⟩ | i
  · rcases e with e | ⟨b, j⟩ <;> simp [incident, src, tgt, innerVertex, rimVertex, centre]
  · simp [incident, tgt, centre]

private theorem unique_color_edge (v : Vertex) (c : Connector) :
    ∃! e, incident v e ∧ color e = c := by
  classical
  rcases v with ⟨i, v⟩ | v
  · change ∃! e, incident (innerVertex i v) e ∧ color e = c
    obtain ⟨e, he⟩ := card_eq_one.mp (one_local_edge v (c - i))
    have get (a : BlockEdge) :
        a = e ↔ localHit v a = true ∧ blockColor a = c - i := by
      have h' := show a ∈ (univ.filter fun e : BlockEdge =>
        localHit v e = true ∧ blockColor e = c - i) ↔ a = e by rw [he, mem_singleton]
      exact h'.symm.trans (by simp)
    obtain ⟨h₁, h₂⟩ := (get e).mp rfl
    refine ⟨insideEdge i e, ⟨(incident_inside_iff _ _ _).2 ⟨e, rfl, h₁⟩, ?_⟩, ?_⟩
    · simp [insideEdge, color, h₂]
    · rintro a ⟨hm, hc⟩
      obtain ⟨u, rfl, hu⟩ := (incident_inside_iff _ _ _).1 hm
      have huc : blockColor u = c - i := by
        change i + blockColor u = c at hc
        rw [← hc]
        ring
      rw [(get u).2 ⟨hu, huc⟩]
  · cases v with
    | none =>
      change ∃! e, incident centre e ∧ color e = c
      refine ⟨.inr (c - 12), ⟨(incident_centre_iff _).2 ⟨_, rfl⟩, by simp [color]⟩, ?_⟩
      rintro a ⟨hm, hc⟩
      obtain ⟨i, rfl⟩ := (incident_centre_iff _).1 hm
      change i + 12 = c at hc
      rw [← hc, add_sub_cancel_right]
    | some i =>
      change ∃! e, incident (rimVertex i) e ∧ color e = c
      obtain ⟨e, he⟩ := rim_color_bijective.2 (c - i)
      refine ⟨rimEdge i e, ⟨(incident_rim_iff _ _).2 ⟨e, rfl⟩, by rw [rim_edge_color, he]; ring⟩, ?_⟩
      rintro a ⟨hm, hc⟩
      obtain ⟨u, rfl⟩ := (incident_rim_iff _ _).1 hm
      rw [rim_edge_color] at hc
      have hh : rimColor u = c - i := by rw [← hc]; ring
      rw [rim_color_bijective.1 (hh.trans he.symm)]

private theorem proper (e f : Edge) (hne : e ≠ f)
    (h : src e = src f ∨ src e = tgt f ∨ tgt e = src f ∨ tgt e = tgt f) :
    color e ≠ color f := by
  intro hc
  have hmeet : ∃ v, incident v e ∧ incident v f := by
    rcases h with h | h | h | h
    · exact ⟨src f, Or.inl h, Or.inl rfl⟩
    · exact ⟨tgt f, Or.inl h, Or.inr rfl⟩
    · exact ⟨src f, Or.inr h, Or.inl rfl⟩
    · exact ⟨tgt f, Or.inr h, Or.inr rfl⟩
  obtain ⟨v, he, hf⟩ := hmeet
  obtain ⟨a, _, hu⟩ := unique_color_edge v (color f)
  exact hne ((hu e ⟨he, hc⟩).trans (hu f ⟨hf, rfl⟩).symm)

private theorem regular (v : Vertex) :
    (univ.filter fun e => src e = v).card + (univ.filter fun e => tgt e = v).card = 13 := by
  classical
  let I : Finset Edge := univ.filter (incident v)
  let f : I → Connector := fun e => color e.val
  have hbij : Function.Bijective f := by
    constructor
    · intro e g h
      obtain ⟨_, _, hu⟩ := unique_color_edge v (f g)
      exact Subtype.ext ((hu e.val ⟨(mem_filter.mp e.property).2, h⟩).trans
        (hu g.val ⟨(mem_filter.mp g.property).2, rfl⟩).symm)
    · intro c
      obtain ⟨e, he, _⟩ := unique_color_edge v c
      exact ⟨⟨e, mem_filter.mpr ⟨mem_univ _, he.1⟩⟩, he.2⟩
  have hk := Fintype.card_congr (Equiv.ofBijective f hbij)
  have hk' : I.card = 13 := by simpa [ZMod.card] using hk
  have hd : Disjoint (univ.filter fun e => src e = v) (univ.filter fun e => tgt e = v) := by
    rw [disjoint_left]
    intro e h₁ h₂
    exact loopless e ((mem_filter.mp h₁).2.trans (mem_filter.mp h₂).2.symm)
  rw [← card_union_of_disjoint hd, filter_union_right]
  convert hk' using 1
  congr 1
  ext e
  simp [I, incident]


private theorem real_flow_signs (w : Edge → ℝ)
    (hw : ∀ e, 1 ≤ |w e| ∧ |w e| ≤ 4 / 3)
    (hd : ∀ v, vertexBalance src tgt w v = 0) :
    ∃ f : Edge → ℤ, (∀ e, f e = 1 ∨ f e = -1) ∧
      ∀ v, ((vertexBalance src tgt f v : ℤ) : ZMod 7) = 0 := by
  let lo (e : Edge) : ℤ := if 0 ≤ w e then 3 else -4
  have hlo (e : Edge) : (lo e : ℝ) ≤ 3 * w e ∧ 3 * w e ≤ (lo e : ℝ) + 1 := by
    have h := hw e
    by_cases he : 0 ≤ w e
    · rw [abs_of_nonneg he] at h
      simp only [lo, he, if_true, Int.cast_ofNat]
      constructor <;> linarith [h.1, h.2]
    · rw [abs_of_neg (lt_of_not_ge he)] at h
      simp only [lo, he, if_false, Int.cast_neg, Int.cast_ofNat]
      constructor <;> linarith [h.1, h.2]
  have hd₃ (v : Vertex) : divergence src tgt (fun e => 3 * w e) v = 0 := by
    have hz := hd v
    unfold divergence
    unfold vertexBalance at hz
    have h (p : Edge → Vertex) (e : Edge) :
        (if p e = v then (3 : ℝ) * w e else 0) = 3 * (if p e = v then w e else 0) := by
      split <;> simp
    simp only [h, ← mul_sum]
    rw [sum_sub_distrib] at hz
    linarith
  obtain ⟨z, hz, hdiv⟩ := round_unit_circulation src tgt loopless lo (fun e => 3 * w e) hlo hd₃
  let f (e : Edge) : ℤ := if z e = 3 ∨ z e = -4 then 1 else -1
  have hf (e : Edge) : f e = 1 ∨ f e = -1 := by
    unfold f
    split <;> simp
  have hcast (e : Edge) : (z e : ZMod 7) = 3 * (f e : ZMod 7) := by
    have he := hz e
    by_cases h : 0 ≤ w e <;> simp [lo, h] at he
    all_goals rcases he with h₁ | h₁ <;> (norm_num [f, h₁] <;> decide)
  refine ⟨f, hf, fun v => ?_⟩
  have hZ := congrArg (fun z : ℤ => (z : ZMod 7)) (hdiv v)
  unfold divergence at hZ
  push_cast at hZ
  simp only [hcast] at hZ
  have ho (p : Edge → Vertex) (e : Edge) :
      (if p e = v then (3 : ZMod 7) * (f e : ZMod 7) else 0) =
        3 * (if p e = v then (f e : ZMod 7) else 0) := by split <;> simp
  simp only [ho, ← mul_sum, ← mul_sub] at hZ
  rw [cast_balance, vertexBalance, sum_sub_distrib]
  have hInv : (5 : ZMod 7) * 3 = 1 := by decide
  have hfive := congrArg (fun x : ZMod 7 => 5 * x) hZ
  change 5 * (3 * _) = 5 * 0 at hfive
  simpa only [← mul_assoc, hInv, one_mul, mul_zero] using hfive

private def Feasible (r : ℝ) (w : Edge → ℝ) : Prop :=
  (∀ e, 1 ≤ |w e| ∧ |w e| ≤ r - 1) ∧ ∀ v, vertexBalance src tgt w v = 0

private theorem goodFlow (r : ℝ) (w : Edge → ℝ) :
    OMA.S_opg_circular_flow_numbers_of_r_graphs.IsNowhereZeroRealFlow src tgt r w
      ↔ Feasible r w := by
  unfold OMA.S_opg_circular_flow_numbers_of_r_graphs.IsNowhereZeroRealFlow Feasible
  apply and_congr Iff.rfl
  apply forall_congr'
  intro v
  rw [vertexBalance, sum_sub_distrib, sub_eq_zero, sum_filter, sum_filter]
  exact eq_comm

private theorem flow_exists : ∃ r w, Feasible r w := by
  let w (e : Edge) : ℝ := concreteFlow e
  let r := 1 + ∑ e, |w e|
  refine ⟨r, w, fun e => ⟨?_, ?_⟩, fun v => ?_⟩
  · have he : (1 : ℤ) ≤ |concreteFlow e| := by
      rcases lt_or_gt_of_ne (concrete_nonzero e) with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    change (1 : ℝ) ≤ |(concreteFlow e : ℝ)|
    exact_mod_cast he
  · dsimp [r]
    rw [add_sub_cancel_left]
    exact single_le_sum (fun x _ => abs_nonneg (w x)) (mem_univ e)
  · have h := congrArg (fun z : ℤ => (z : ℝ)) (concrete_balance v)
    unfold vertexBalance at h ⊢
    push_cast at h
    exact h

set_option maxHeartbeats 1200000 in
private theorem no_small_infimum : ¬ sInf {r : ℝ | ∃ w, Feasible r w} ≤ 7 / 3 := by
  intro h
  let A : Set ℝ := {r | ∃ w, Feasible r w}
  obtain ⟨r, w, hw⟩ := flow_exists
  have hA : A.Nonempty := ⟨r, w, hw⟩
  have hmin (r : ℝ) (hr : r ∈ A) : 2 ≤ r := by
    obtain ⟨w, hw⟩ := hr
    have h := hw.1 (.inr 0)
    linarith [h.1, h.2]
  let S : Set (ℝ × (Edge → ℝ)) := {p | p.1 ∈ Set.Icc 2 3 ∧ Feasible p.1 p.2}
  have hclosed : IsClosed S := by
    have habs (e : Edge) : Continuous (fun p : ℝ × (Edge → ℝ) => |p.2 e|) :=
      ((continuous_apply e).comp continuous_snd).abs
    have hc (v : Vertex) : Continuous (fun p : ℝ × (Edge → ℝ) => vertexBalance src tgt p.2 v) := by
      have he (u : Edge → Vertex) (e : Edge) :
          Continuous (fun p : ℝ × (Edge → ℝ) => if u e = v then p.2 e else 0) := by
        by_cases h : u e = v
        · simpa only [h, if_true, Function.comp_def] using (continuous_apply e).comp
            (continuous_snd : Continuous (Prod.snd : ℝ × (Edge → ℝ) → Edge → ℝ))
        · simpa only [h, if_false] using (continuous_const : Continuous (fun _ : ℝ × (Edge → ℝ) => (0 : ℝ)))
      unfold vertexBalance
      exact continuous_finsetSum _ (fun e _ => (he src e).sub (he tgt e))
    change IsClosed {p : ℝ × (Edge → ℝ) | p.1 ∈ Set.Icc 2 3 ∧
      (∀ e, 1 ≤ |p.2 e| ∧ |p.2 e| ≤ p.1 - 1) ∧ ∀ v, vertexBalance src tgt p.2 v = 0}
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_iInter fun e => (isClosed_le continuous_const (habs e)).inter
        (isClosed_le (habs e) (continuous_fst.sub continuous_const))).inter
          (isClosed_iInter fun v => isClosed_eq (hc v) continuous_const))
  have hc : IsCompact S := by
    apply (isCompact_Icc.prod (isCompact_Icc (α := Edge → ℝ))).of_isClosed_subset hclosed
    intro p hp
    change p.1 ∈ Set.Icc 2 3 ∧ Feasible p.1 p.2 at hp
    refine ⟨hp.1, ?_⟩
    change (∀ e, (-2 : ℝ) ≤ p.2 e) ∧ ∀ e, p.2 e ≤ 2
    constructor <;> intro e
    · linarith [hp.1.2, (hp.2.1 e).2, neg_abs_le (p.2 e)]
    · linarith [hp.1.2, (hp.2.1 e).2, le_abs_self (p.2 e)]
  obtain ⟨r₁, hr₁, hlt⟩ := exists_lt_of_csInf_lt hA (lt_of_le_of_lt h (by norm_num : (7 / 3 : ℝ) < 3))
  obtain ⟨w₁, hw₁⟩ := hr₁
  have hS : S.Nonempty := ⟨(r₁, w₁), ⟨hmin _ ⟨w₁, hw₁⟩, hlt.le⟩, hw₁⟩
  obtain ⟨q, hq, hqmin⟩ := hc.exists_isMinOn hS continuous_fst.continuousOn
  change q.1 ∈ Set.Icc 2 3 ∧ Feasible q.1 q.2 at hq
  have hq₀ : q.1 ≤ sInf A := by
    apply le_csInf hA
    intro R hR
    by_cases hR' : R ≤ 3
    · obtain ⟨w, hw⟩ := hR
      exact hqmin (show (R, w) ∈ S from ⟨⟨hmin _ ⟨w, hw⟩, hR'⟩, hw⟩)
    · exact hq.1.2.trans (le_of_lt (lt_of_not_ge hR'))
  obtain ⟨f, hf, hm⟩ := real_flow_signs q.2 (fun e => ⟨(hq.2.1 e).1,
    (hq.2.1 e).2.trans (by linarith [show sInf A ≤ 7 / 3 from h])⟩) hq.2.2
  exact nonmodular f hf hm

private theorem incident_color_card_one {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (s t : E → V) (hl : ∀ e, s e ≠ t e) (n : ℕ)
    (hreg : ∀ v, (univ.filter fun e => s e = v).card + (univ.filter fun e => t e = v).card = n)
    (c : E → Fin n)
    (hc : ∀ e f, e ≠ f → (s e = s f ∨ s e = t f ∨ t e = s f ∨ t e = t f) → c e ≠ c f)
    (v : V) (k : Fin n) :
    ((univ.filter fun e => s e = v ∨ t e = v).filter fun e => c e = k).card = 1 := by
  classical
  set I := univ.filter fun e => s e = v ∨ t e = v with hI
  have hIcard : I.card = n := by
    rw [hI, Finset.filter_or, Finset.card_union_of_disjoint, hreg v]
    rw [Finset.disjoint_filter]
    intro e _ h1 h2
    exact hl e (h1.trans h2.symm)
  have hinj : Set.InjOn c I := by
    intro e he f hf hcef
    by_contra hne
    simp only [hI, coe_filter, mem_univ, true_and] at he hf
    apply hc e f hne _ hcef
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Or.inl (he.trans hf.symm)
    · exact Or.inr (Or.inl (he.trans hf.symm))
    · exact Or.inr (Or.inr (Or.inl (he.trans hf.symm)))
    · exact Or.inr (Or.inr (Or.inr (he.trans hf.symm)))
  have himage : I.image c = univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hIcard, Fintype.card_fin]
  have hk : k ∈ I.image c := by rw [himage]; exact mem_univ k
  obtain ⟨e, he, hek⟩ := Finset.mem_image.mp hk
  apply le_antisymm
  · rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  · exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hek⟩⟩

private theorem oddCut_of_coloring {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (s t : E → V) (hl : ∀ e, s e ≠ t e) (n : ℕ)
    (hreg : ∀ v, (univ.filter fun e => s e = v).card + (univ.filter fun e => t e = v).card = n)
    (c : E → Fin n)
    (hc : ∀ e f, e ≠ f → (s e = s f ∨ s e = t f ∨ t e = s f ∨ t e = t f) → c e ≠ c f)
    (X : Finset V) (hX : Odd X.card) :
    n ≤ (univ.filter fun e => (s e ∈ X ∧ t e ∉ X) ∨ (t e ∈ X ∧ s e ∉ X)).card := by
  classical
  set C := univ.filter fun e => (s e ∈ X ∧ t e ∉ X) ∨ (t e ∈ X ∧ s e ∉ X) with hC
  -- each colour class meets the cut
  have hcol : ∀ k : Fin n, 1 ≤ (C.filter fun e => c e = k).card := by
    intro k
    set M := univ.filter fun e => c e = k with hM
    let a : E → ℕ := fun e => (if s e ∈ X then 1 else 0) + (if t e ∈ X then 1 else 0)
    have hA : ∑ v ∈ X, ((univ.filter fun e => s e = v ∨ t e = v).filter fun e => c e = k).card
        = X.card := by
      rw [Finset.card_eq_sum_ones X]
      exact Finset.sum_congr rfl fun v _ => incident_color_card_one s t hl n hreg c hc v k
    have hB : ∑ v ∈ X, ((univ.filter fun e => s e = v ∨ t e = v).filter fun e => c e = k).card
        = ∑ e ∈ M, a e := by
      have h1 : ∀ v, ((univ.filter fun e => s e = v ∨ t e = v).filter fun e => c e = k).card
          = ∑ e ∈ M, ((if s e = v then 1 else 0) + (if t e = v then 1 else 0)) := by
        intro v
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter, hM, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h1 : s e = v <;> by_cases h2 : t e = v <;> by_cases h3 : c e = k <;>
          simp_all
        exact hl e (h1.trans h2.symm)
      rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    have hpar : (∑ e ∈ M, a e) % 2 = (C.filter fun e => c e = k).card % 2 := by
      rw [Finset.sum_nat_mod]
      have : ∀ e ∈ M, a e % 2 = if ((s e ∈ X ∧ t e ∉ X) ∨ (t e ∈ X ∧ s e ∉ X)) then 1 else 0 := by
        intro e _
        by_cases h1 : s e ∈ X <;> by_cases h2 : t e ∈ X <;> simp [a, h1, h2]
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      congr 2
      ext e; simp [hM, hC, and_comm]
    have hodd : X.card % 2 = 1 := Nat.odd_iff.mp hX
    omega
  calc n = ∑ _k : Fin n, 1 := by simp
    _ ≤ ∑ k : Fin n, (C.filter fun e => c e = k).card := Finset.sum_le_sum fun k _ => hcol k
    _ = C.card := (Finset.card_eq_sum_card_fiberwise (fun e _ => mem_univ (c e))).symm


end RGraphCounterexample

open RGraphCounterexample in
theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_circular_flow_numbers_of_r_graphs.main) := by
  intro h
  have hreg : ∀ v : Vertex, (Finset.univ.filter fun e => src e = v).card +
      (Finset.univ.filter fun e => tgt e = v).card = 13 := regular
  let c : Edge → Fin 13 := fun e => ⟨(color e).val, ZMod.val_lt _⟩
  have hc : ∀ e f, e ≠ f → (src e = src f ∨ src e = tgt f ∨ tgt e = src f ∨ tgt e = tgt f) →
      c e ≠ c f := fun e f hne hi hEq =>
    proper e f hne hi (ZMod.val_injective 13 (congrArg Fin.val hEq))
  have h₁ := h 6 (by norm_num) Vertex Edge src tgt loopless
    (by intro v; simpa using hreg v)
    (fun X hX => by simpa using oddCut_of_coloring src tgt loopless 13 hreg c hc X hX)
  unfold OMA.S_opg_circular_flow_numbers_of_r_graphs.circularFlowNumber at h₁
  apply no_small_infimum
  convert h₁ using 1
  · congr 1
    ext r
    exact exists_congr (fun w => (goodFlow r w).symm)
  · norm_num
