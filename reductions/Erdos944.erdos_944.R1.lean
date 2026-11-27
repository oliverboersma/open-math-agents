import FormalConjectures.ErdosProblems.«944»

-- Credit: @marcusbuffett
-- Adapted from @Genbox (Ian Qvist), large_k_for_any_r in this repository:
-- 06931ba9cd1275b7be95b521c8cb233028ae849b.
-- Separate the phase widths of the one- and two-cluster constructions.
-- Periods of 6m and 18m suffice, leaving only k = 4, 5, 6, 8.

/-!
# A circulant for vertex-criticality with many redundant edges

The distance sets and vertex deletion colorings are due to Skottova and
Steiner, *Critical edge sets in vertex-critical graphs*, Section 4 and
Appendix A (https://arxiv.org/abs/2508.08703).
-/

open scoped BigOperators


namespace DiracPhase

private theorem phase_card {X : Type*} (S : Finset X) (z : X → ℤ) (a : ℤ) (b : ℕ)
    (hinj : Set.InjOn z ↑S) (hspan : ∀ x ∈ S, a ≤ z x ∧ z x < a+2*(b:ℤ))
    (hpar : ∀ x ∈ S, ∀ y ∈ S, z x % 2 = z y % 2) :
    S.card ≤ b := by
  let f (x : S) : Fin b := ⟨((z x.val-a)/2).toNat, by
    have := hspan x.val x.property
    omega⟩
  have hf : Function.Injective f := by
    intro x y h
    have hv := congrArg Fin.val h
    change ((z x.val-a)/2).toNat = ((z y.val-a)/2).toNat at hv
    have hx := hspan x.val x.property
    have hy := hspan y.val y.property
    have hp := hpar x.val x.property y.val y.property
    exact Subtype.ext (hinj x.property y.property (by omega))
  simpa using Fintype.card_le_of_injective f hf

private theorem min_phase {X : Type*} (S : Finset X) (z : X → ℤ)
    (h : S.Nonempty) : ∃ a ∈ S, ∀ x ∈ S, z a ≤ z x := by
  classical
  have hn : (S.image z).Nonempty := h.image z
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (Finset.min'_mem _ hn)
  refine ⟨a,ha,fun x hx => ?_⟩
  rw [he]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)

private theorem far_of_large {X : Type*} (S : Finset X) (z : X → ℤ)
    (D : Finset (Sym2 X)) (m r : ℕ) (hD : D.card ≤ r) (hrm : r < m)
    (hinj : Set.InjOn z ↑S) (hlarge : m < S.card)
    (hodd : ∀ x ∈ S, ∀ y ∈ S, (z x-z y).natAbs < 2*m → z x % 2 ≠ z y % 2 →
      s(x,y) ∈ D) :
    ∃ x ∈ S, ∃ y ∈ S, z x + 2*(m:ℤ) ≤ z y := by
  classical
  by_contra! hnear
  obtain ⟨a,ha,hmin⟩ := min_phase S z (Finset.card_pos.mp (by omega))
  have hspan (x : X) (hx : x ∈ S) : z a ≤ z x ∧ z x < z a+2*(m:ℤ) :=
    ⟨hmin x hx, hnear a ha x hx⟩
  let E := S.filter fun x => z x % 2 = 0
  let O := S.filter fun x => z x % 2 ≠ 0
  have hE : E.card ≤ m := phase_card E z (z a) m
    (hinj.mono fun _ hx => (Finset.mem_filter.mp hx).1)
    (fun x hx => hspan x (Finset.mem_filter.mp hx).1)
    (fun x hx y hy => ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm)
  have hO : O.card ≤ m := phase_card O z (z a) m
    (hinj.mono fun _ hx => (Finset.mem_filter.mp hx).1)
    (fun x hx => hspan x (Finset.mem_filter.mp hx).1)
    (by
      intro x hx y hy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      omega)
  have hsum : E.card + O.card = S.card := Finset.card_filter_add_card_filter_not _
  have hprod : E.card * O.card ≤ r := by
    rw [← Finset.card_product]
    apply le_trans _ hD
    refine Finset.card_le_card_of_injOn (fun p : X × X => s(p.1,p.2)) ?_ ?_
    · intro p hp
      obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
      obtain ⟨hx,hp₁⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨hy,hp₂⟩ := Finset.mem_filter.mp hp₂
      have hx' := hspan p.1 hx
      have hy' := hspan p.2 hy
      apply hodd p.1 hx p.2 hy (by omega)
      omega
    · intro p hp q hq he
      rcases (Sym2.mk_eq_mk_iff (p := p) (q := q)).mp he with h | h
      · exact h
      · have hp₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
        have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
        have hphase := congrArg (fun x => z x.1 % 2) h
        exact (hq₂ (hphase.symm.trans hp₁)).elim
  have hsumprod : E.card + O.card ≤ E.card * O.card + 1 := by
    obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : E.card ≠ 0)
    obtain ⟨o,ho⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : O.card ≠ 0)
    rw [he,ho]
    nlinarith
  omega

theorem card_bound {X : Type*} (s q m r : ℕ) (hm : r < m) (hq : 2*r < q)
    (S C : Finset X) (hC : C ⊆ S) (hremove : S.card ≤ C.card+2*r)
    (D : Finset (Sym2 X)) (hD : D.card ≤ r)
    (layer : X → Fin s × Fin q) (z : X → ℤ)
    (hinj : Set.InjOn (fun x => (layer x,z x)) ↑S)
    (hodd : ∀ x ∈ S, ∀ y ∈ S, layer x = layer y → (z x-z y).natAbs < 2*m →
      z x % 2 ≠ z y % 2 → s(x,y) ∈ D)
    (hclean : ∀ x ∈ C, ∀ y ∈ C, layer x = layer y →
      (z x-z y).natAbs < 2*m ∧ z x % 2 = z y % 2)
    (hband : ∀ x ∈ S, ∀ y ∈ C, (layer x).1 = (layer y).1 → (layer x).2 ≠ (layer y).2 →
      let d := if (layer x).2 < (layer y).2 then z y-z x else z x-z y;
      -(2*(m:ℤ))+2 ≤ d ∧ d ≤ 2*(m:ℤ)-1) :
    S.card ≤ s*q*m := by
  classical
  by_contra! hlarge
  let load (i : Fin s × Fin q) := S.filter fun x => layer x = i
  let clean (i : Fin s × Fin q) := C.filter fun x => layer x = i
  have hsum : S.card = ∑ i, (load i).card :=
    Finset.card_eq_sum_card_fiberwise (f := layer) (by simp)
  have hcsum : C.card = ∑ i, (clean i).card :=
    Finset.card_eq_sum_card_fiberwise (f := layer) (by simp)
  have hindex : Fintype.card (Fin s × Fin q) = s*q := by simp
  obtain ⟨i, hi⟩ : ∃ i, m < (load i).card := by
    by_contra! h
    have ht := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
    simp only [Finset.sum_const, Finset.card_univ, hindex, smul_eq_mul, ← hsum] at ht
    omega
  have hload (i : Fin s × Fin q) (x : X) (hx : x ∈ load i) :
      x ∈ S ∧ layer x = i := Finset.mem_filter.mp hx
  have hclean' (i : Fin s × Fin q) (x : X) (hx : x ∈ clean i) :
      x ∈ C ∧ layer x = i := Finset.mem_filter.mp hx
  have hlInj (i : Fin s × Fin q) : Set.InjOn z ↑(load i) := by
    intro x hx y hy he
    exact hinj (hload i x hx).1 (hload i y hy).1
      (Prod.ext ((hload i x hx).2.trans (hload i y hy).2.symm) he)
  obtain ⟨u,hu,v,hv,huv⟩ := far_of_large (load i) z D m r hD hm (hlInj i) hi (by
    intro x hx y hy hdist hp
    obtain ⟨hxS,hxI⟩ := hload i x hx
    obtain ⟨hyS,hyI⟩ := hload i y hy
    exact hodd x hxS y hyS (hxI.trans hyI.symm) hdist hp)
  have hcInj (j : Fin s × Fin q) : Set.InjOn z ↑(clean j) :=
    (hlInj j).mono (by
      intro x hx
      obtain ⟨hxC,hxJ⟩ := hclean' j x hx
      exact Finset.mem_filter.mpr ⟨hC hxC,hxJ⟩)
  have hcPair (j : Fin s × Fin q) (x : X) (hx : x ∈ clean j) (y : X) (hy : y ∈ clean j) :
      (z x-z y).natAbs < 2*m ∧ z x % 2 = z y % 2 := by
    obtain ⟨hxC,hxJ⟩ := hclean' j x hx
    obtain ⟨hyC,hyJ⟩ := hclean' j y hy
    exact hclean x hxC y hyC (hxJ.trans hyJ.symm)
  have hsmall (j : Fin s × Fin q) : (clean j).card ≤ m := by
    by_cases hn : (clean j).Nonempty
    · obtain ⟨w,hw,hmin⟩ := min_phase (clean j) z hn
      apply phase_card (clean j) z (z w) m (hcInj j)
      · intro x hx
        have h := (hcPair j x hx w hw).1
        exact ⟨hmin x hx, by omega⟩
      · exact fun x hx y hy => (hcPair j x hx y hy).2
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have hstrong (j : Fin s × Fin q) (hcluster : i.1 = j.1) (hne : j.2 ≠ i.2) :
      (clean j).card ≤ m-1 := by
    have hspec (x : X) (hx : x ∈ load i) (y : X) (hy : y ∈ clean j) :
        let d := if i.2 < j.2 then z y-z x else z x-z y;
        -(2*(m:ℤ))+2 ≤ d ∧ d ≤ 2*(m:ℤ)-1 := by
      obtain ⟨hxS,hxI⟩ := hload i x hx
      obtain ⟨hyC,hyJ⟩ := hclean' j y hy
      simpa only [hxI,hyJ] using hband x hxS y hyC
        (by simpa only [hxI,hyJ] using hcluster)
        (by simpa only [hxI,hyJ] using hne.symm)
    let low := if i.2 < j.2 then z v-2*(m:ℤ)+2 else z v-2*(m:ℤ)+1
    apply phase_card (clean j) z low (m-1) (hcInj j)
    · intro y hy
      have ha := hspec u hu y hy
      have hb := hspec v hv y hy
      by_cases horder : i.2 < j.2
      · simp only [low, horder, if_true] at ha hb ⊢
        omega
      · simp only [low, horder, if_false] at ha hb ⊢
        omega
    · exact fun x hx y hy => (hcPair j x hx y hy).2
  let deficient : Finset (Fin s × Fin q) := {i.1} ×ˢ (Finset.univ.erase i.2)
  have hdef : deficient.card = q-1 := by simp [deficient]
  have htot := Finset.sum_le_sum (s := Finset.univ) (f := fun j : Fin s × Fin q =>
    (clean j).card + if j ∈ deficient then 1 else 0) (g := fun _ => m) (by
    intro j _
    by_cases hj : j ∈ deficient
    · have hj' := Finset.mem_product.mp hj
      have h₁ := Finset.mem_singleton.mp hj'.1
      have h₂ := (Finset.mem_erase.mp hj'.2).1
      have hs := hstrong j h₁.symm h₂
      simp only [hj, if_true]
      omega
    · simpa [hj] using hsmall j)
  have hsumDef : (∑ j : Fin s × Fin q, if j ∈ deficient then 1 else 0) = q-1 := by
    rw [Finset.sum_boole]
    simpa using hdef
  rw [Finset.sum_add_distrib, ← hcsum, hsumDef] at htot
  simp only [Finset.sum_const, Finset.card_univ, hindex, smul_eq_mul] at htot
  omega

end DiracPhase

namespace DiracLarge

private def Band (p : ℕ) (a lo hi d : ℤ) : Prop :=
  ∃ j t : ℤ, lo ≤ t ∧ t ≤ hi ∧ d = j*(p:ℤ)+a+t

private def Allowed (m p q : ℕ) (two : Bool) (d : ℤ) : Prop :=
  (Band p 0 (-2*(m:ℤ)+2) (2*(m:ℤ)-1) d ∨
    (two = true ∧ Band p ((p/2 : ℕ):ℤ) (-3*(m:ℤ)+3) (3*(m:ℤ)-2) d)) ∧
  (d < 2*(m:ℤ) → d%2=0) ∧
  (((q*p+1 : ℕ):ℤ)-d < 2*(m:ℤ) → (((q*p+1 : ℕ):ℤ)-d)%2=0)

private def graph (m p q : ℕ) (two : Bool) : SimpleGraph (ZMod (q*p+1)) where
  Adj x y := x ≠ y ∧ ¬ (Allowed m p q two ↑(y-x).val ∧ Allowed m p q two ↑(x-y).val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2,h'.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def VertexDeleteColorable {X : Type*} (G : SimpleGraph X) (a : ℕ) : Prop :=
  ∀ v : X, ∃ f : {x : X // x ≠ v} → Fin a, ∀ x y, G.Adj x.val y.val → f x ≠ f y

private theorem doubled_half {p : ℕ} (h : Even p) : (p:ℤ) = 2*((p/2 : ℕ):ℤ) := by
  obtain ⟨a,ha⟩ := h
  omega

theorem allowed_mirror (m p q : ℕ) (two : Bool) (hp : Even p) {d : ℤ}
    (h : Allowed m p q two d) : Allowed m p q two (((q*p+1 : ℕ):ℤ)-d) := by
  obtain ⟨hband,h₁,h₂⟩ := h
  refine ⟨?_,h₂,?_⟩
  · rcases hband with ⟨j,t,ht₀,ht₁,he⟩ | ⟨htrue,j,t,ht₀,ht₁,he⟩
    · left
      refine ⟨(q:ℤ)-j,1-t,by omega,by omega,?_⟩
      rw [he]
      push_cast
      ring
    · right
      refine ⟨htrue,(q:ℤ)-j-1,1-t,by omega,by omega,?_⟩
      rw [he]
      push_cast
      rw [show ((p:ℤ)/2) = ((p/2:ℕ):ℤ) by omega]
      linear_combination doubled_half hp
  · intro ht
    have hh : ((q*p+1 : ℕ):ℤ) - (((q*p+1 : ℕ):ℤ)-d) = d := by ring
    rw [hh] at ht ⊢
    exact h₁ ht

theorem graph_translate (m p q : ℕ) (two : Bool) (x y z : ZMod (q*p+1)) :
    (graph m p q two).Adj (x+z) (y+z) ↔ (graph m p q two).Adj x y := by
  have hne : x+z ≠ y+z ↔ x ≠ y := not_congr (add_left_inj z)
  simp only [graph,hne,add_sub_add_right_eq_sub]

theorem nonadj_of_lift {m p q : ℕ} {two : Bool} (hp : Even p)
    {x y : ZMod (q*p+1)} {d : ℤ}
    (hd₀ : 0 < d) (hdN : d < ((q*p+1:ℕ):ℤ))
    (he : (d : ZMod (q*p+1)) = y-x) (ha : Allowed m p q two d) :
    ¬ (graph m p q two).Adj x y := by
  have h₁ : (↑(y-x).val : ℤ) = d := by
    rw [← he, ZMod.val_intCast, Int.emod_eq_of_lt hd₀.le hdN]
  let N := q*p+1
  have hc : ((((N:ℤ)-d) : ℤ) : ZMod N) = x-y := by
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, zero_sub, he, neg_sub]
  have h₂ : (↑(x-y).val : ℤ) = ((N:ℤ)-d) := by
    rw [← hc, ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
  intro h
  apply h.2
  rw [h₁,h₂]
  exact ⟨ha, allowed_mirror m p q two hp ha⟩

theorem allowed_of_nonadj_lift {m p q : ℕ} {two : Bool}
    {x y : ZMod (q*p+1)} {d : ℤ}
    (hd₀ : 0 < d) (hdN : d < ((q*p+1:ℕ):ℤ))
    (he : (d : ZMod (q*p+1)) = y-x) (ha : ¬ (graph m p q two).Adj x y) :
    Allowed m p q two d := by
  classical
  have h₁ : (↑(y-x).val : ℤ) = d := by
    rw [← he, ZMod.val_intCast, Int.emod_eq_of_lt hd₀.le hdN]
  have hne : x ≠ y := by
    intro h
    subst y
    simp at h₁
    omega
  by_contra hn
  exact ha ⟨hne, fun h => hn (h₁ ▸ h.1)⟩


private def clusterCount (two : Bool) : ℕ := if two then 2 else 1

private structure Point (m p q : ℕ) (two : Bool) where
  cluster : Fin (clusterCount two)
  period : Fin q
  phase : ℤ
  phase_lo : -(3*(m:ℤ)) ≤ phase
  phase_hi : phase ≤ 3*(m:ℤ)
  phase_one_lo : two = false → -(2*(m:ℤ)) ≤ phase
  phase_one_hi : two = false → phase ≤ 2*(m:ℤ)

private def Point.raw {m p q : ℕ} {two : Bool} (x : Point m p q two) : ℤ :=
  (x.period.val:ℤ)*p + (x.cluster.val:ℤ)*((p/2 : ℕ):ℤ) + x.phase

private theorem band_index {p q : ℕ} {d j t : ℤ} (hp : 0 < p)
    (hd₀ : 0 ≤ d) (hdN : d ≤ (q:ℤ)*p)
    (ht₀ : -(p:ℤ) < t) (ht₁ : t < (p:ℤ)) (he : d = j*p+t) :
    0 ≤ j ∧ j ≤ (q:ℤ) := by
  have hp₀ : (0:ℤ) ≤ p := by omega
  constructor
  · by_contra! hn
    have hh := mul_le_mul_of_nonneg_right (show j ≤ -1 by omega) hp₀
    linarith
  · by_contra! hn
    have hh := mul_le_mul_of_nonneg_right (show (q:ℤ)+1 ≤ j by omega) hp₀
    linarith

private theorem point_repr {m p q : ℕ} {two : Bool} (hm : 0 < m) (hp : (if two then 18 else 6)*m ≤ p)
    (hq : 0 < q) {d : ℤ} (hd₀ : 0 ≤ d) (hdN : d < ((q*p+1:ℕ):ℤ))
    (h : d = 0 ∨ Allowed m p q two d) :
    ∃ x : Point m p q two, (x.raw : ZMod (q*p+1)) = (d : ZMod (q*p+1)) := by
  have hs : 6*m ≤ p := by cases two <;> simp_all <;> omega
  have hq' : d ≤ (q:ℤ)*p := by
    push_cast at hdN
    omega
  have hc₀ : 0 < clusterCount two := by cases two <;> decide
  have hp₀ : 0 < p := by omega
  have hband : Band p 0 (-2*(m:ℤ)+2) (2*(m:ℤ)-1) d ∨
      (two = true ∧ Band p ((p/2 : ℕ):ℤ) (-3*(m:ℤ)+3) (3*(m:ℤ)-2) d) := by
    rcases h with rfl | h
    · exact Or.inl ⟨0,0,by omega,by omega,by simp⟩
    · exact h.1
  rcases hband with ⟨j,t,ht₀,ht₁,he⟩ | ⟨heven,j,t,ht₀,ht₁,he⟩
  · simp only [add_zero] at he
    obtain ⟨hj₀,hj₁⟩ := band_index hp₀ hd₀ hq' (by omega) (by omega) he
    by_cases hj : j = (q:ℤ)
    · let x : Point m p q two := ⟨⟨0,hc₀⟩,⟨0,hq⟩,t-1,by omega,by omega,fun _ => by omega,fun _ => by omega⟩
      refine ⟨x, ?_⟩
      have hx : x.raw = d - ((q*p+1:ℕ):ℤ) := by
        push_cast
        simp [Point.raw,x,he,hj]
      rw [hx, Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero]
    · let x : Point m p q two := ⟨⟨0,hc₀⟩,⟨j.toNat,by omega⟩,t,by omega,by omega,fun _ => by omega,fun _ => by omega⟩
      refine ⟨x, ?_⟩
      have hx : x.raw = d := by
        simp [Point.raw,x,Int.toNat_of_nonneg hj₀,he]
      rw [hx]
  · have he' : d = j*(p:ℤ) + (((p/2:ℕ):ℤ)+t) := by linarith
    obtain ⟨hj₀,hj₁⟩ := band_index hp₀ hd₀ hq' (by omega) (by omega) he'
    have hj : j < (q:ℤ) := by
      by_contra! hn
      have hj' : j = (q:ℤ) := le_antisymm hj₁ hn
      rw [hj'] at he'
      omega
    have hc₁ : 1 < clusterCount two := by simp [clusterCount,heven]
    let x : Point m p q two := ⟨⟨1,hc₁⟩,⟨j.toNat,by omega⟩,t,by omega,by omega,by simp [heven],by simp [heven]⟩
    refine ⟨x,?_⟩
    have hx : x.raw = d := by
      simp [Point.raw,x,Int.toNat_of_nonneg hj₀,he]
    rw [hx]

private theorem raw_bounds {m p q : ℕ} {two : Bool} (x : Point m p q two) :
    -(3*(m:ℤ)) ≤ x.raw ∧ x.raw ≤ (q:ℤ)*p-p+((p/2:ℕ):ℤ)+3*(m:ℤ) := by
  have hp₀ : (0:ℤ) ≤ p := by omega
  have hhalf₀ : (0:ℤ) ≤ ((p/2:ℕ):ℤ) := by omega
  have hcl : clusterCount two ≤ 2 := by cases two <;> decide
  have hc := x.cluster.isLt
  have hj := x.period.isLt
  have hlo₁ := mul_nonneg (show 0 ≤ (x.period.val:ℤ) by omega) hp₀
  have hlo₂ := mul_nonneg (show 0 ≤ (x.cluster.val:ℤ) by omega) hhalf₀
  have hhi₁ := mul_le_mul_of_nonneg_right (show (x.period.val:ℤ) ≤ (q:ℤ)-1 by omega) hp₀
  have hhi₂ := mul_le_mul_of_nonneg_right (show (x.cluster.val:ℤ) ≤ 1 by omega) hhalf₀
  unfold Point.raw
  constructor <;> linarith [x.phase_lo,x.phase_hi]

private theorem raw_sub_lt {m p q : ℕ} {two : Bool} (hp : (if two then 18 else 6)*m ≤ p)
    (x y : Point m p q two) : y.raw-x.raw < ((q*p+1:ℕ):ℤ) := by
  cases two with
  | false =>
    have hc (v : Point m p q false) : v.cluster.val = 0 := by
      have h := v.cluster.isLt
      simp [clusterCount] at h
      omega
    have hy := y.period.isLt
    have hj : (y.period.val : ℤ) - x.period.val ≤ (q:ℤ) - 1 := by omega
    have hh := mul_le_mul_of_nonneg_right hj (show (0:ℤ) ≤ p by omega)
    simp only [Point.raw,hc, Nat.cast_zero,zero_mul,add_zero]
    push_cast
    simp only [Bool.false_eq_true,if_false] at hp
    linarith [x.phase_one_lo rfl, y.phase_one_hi rfl, show (6:ℤ)*m ≤ p by exact_mod_cast hp]
  | true =>
    simp only [if_true] at hp
    have hx := (raw_bounds x).1
    have hy := (raw_bounds y).2
    push_cast
    have h : ((p/2:ℕ):ℤ) + 6*(m:ℤ) ≤ (p:ℤ) := by omega
    linarith

private theorem raw_sub {m p q : ℕ} {two : Bool} {x y : Point m p q two}
    (hc : x.cluster = y.cluster) :
    y.raw-x.raw = ((y.period.val:ℤ)-(x.period.val:ℤ))*p+(y.phase-x.phase) := by
  simp only [Point.raw,hc]
  ring

private theorem raw_order {m p q : ℕ} {two : Bool} (hp : (if two then 18 else 6)*m ≤ p) (hm : 0 < m)
    {x y : Point m p q two} (hc : x.cluster = y.cluster) (hj : x.period < y.period) :
    0 < y.raw-x.raw := by
  rw [raw_sub hc]
  have hp₀ : (0:ℤ) ≤ p := by omega
  have hj' : 1 ≤ (y.period.val:ℤ)-(x.period.val:ℤ) := by
    change x.period.val < y.period.val at hj
    omega
  have hh := mul_le_mul_of_nonneg_right hj' hp₀
  cases two with
  | true =>
    simp at hp
    linarith [x.phase_hi,y.phase_lo,show (18:ℤ)*m ≤ p by exact_mod_cast hp]
  | false =>
    simp at hp
    linarith [x.phase_one_hi rfl,y.phase_one_lo rfl,show (6:ℤ)*m ≤ p by exact_mod_cast hp]

private theorem band_small {m p q : ℕ} {two : Bool} (hp : (if two then 18 else 6)*m ≤ p) (hpEven : Even p)
    {x y : Point m p q two} (hc : x.cluster = y.cluster)
    (h : Allowed m p q two (y.raw-x.raw)) :
    -(2*(m:ℤ))+2 ≤ y.phase-x.phase ∧ y.phase-x.phase ≤ 2*(m:ℤ)-1 := by
  have hlo : -(6*(m:ℤ)) ≤ y.phase-x.phase := by linarith [x.phase_hi,y.phase_lo]
  have hhi : y.phase-x.phase ≤ 6*(m:ℤ) := by linarith [x.phase_lo,y.phase_hi]
  rcases h.1 with ⟨j,t,ht₀,ht₁,he⟩ | ⟨_,j,t,ht₀,ht₁,he⟩
  · rw [raw_sub hc] at he
    have hdvd : (p:ℤ) ∣ y.phase-x.phase-t := by
      refine ⟨j-((y.period.val:ℤ)-(x.period.val:ℤ)),?_⟩
      linear_combination he
    have hlt : (y.phase-x.phase-t).natAbs < (p:ℤ).natAbs := by
      simp only [Int.natAbs_natCast]
      cases two with
      | true => simp at hp; omega
      | false =>
        simp at hp
        have := x.phase_one_hi rfl
        have := x.phase_one_lo rfl
        have := y.phase_one_hi rfl
        have := y.phase_one_lo rfl
        omega
    have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
    omega
  · rename_i ht
    subst two
    simp at hp
    rw [raw_sub hc] at he
    let z : ℤ := ((p/2:ℕ):ℤ)+t-(y.phase-x.phase)
    have hdvd : (p:ℤ) ∣ z := by
      refine ⟨(y.period.val:ℤ)-(x.period.val:ℤ)-j,?_⟩
      dsimp [z]
      rw [show ((p/2:ℕ):ℤ) = (p:ℤ)/2 by omega] at he
      linear_combination -he
    have hhalf := doubled_half hpEven
    have hz₀ : 0 < z := by dsimp [z]; omega
    have hz₁ : z < (p:ℤ) := by dsimp [z]; omega
    exact (ne_of_gt hz₀ (Int.eq_zero_of_dvd_of_nonneg_of_lt hz₀.le hz₁ hdvd)).elim

theorem card_class (m p q r : ℕ) (two : Bool) (hm : r < m) (hq : 2*r < q)
    (hp : (if two then 18 else 6)*m ≤ p) (hpEven : Even p) (D : Finset (Sym2 (ZMod (q*p+1))))
    (hD : D.card ≤ r) (S : Finset (ZMod (q*p+1)))
    (hcompat : ∀ x ∈ S, ∀ y ∈ S, (graph m p q two).Adj x y → s(x,y) ∈ D) :
    S.card ≤ (if two then 2 else 1)*q*m := by
  classical
  change S.card ≤ clusterCount two * q * m
  by_contra! hlarge
  let N := q*p+1
  let touched : Finset (ZMod N) := D.biUnion Sym2.toFinset
  let C := S \ touched
  have htouched : touched.card ≤ D.card*2 := by
    apply Finset.card_biUnion_le_card_mul
    intro e _
    rw [Sym2.card_toFinset]
    split <;> omega
  have hC : C ⊆ S := Finset.sdiff_subset
  have hremove : S.card ≤ C.card+2*r := by
    have hi : (S ∩ touched).card ≤ touched.card :=
      Finset.card_le_card (Finset.inter_subset_right (s₁ := S))
    have h := Finset.card_sdiff_add_card_inter S touched
    dsimp [C]
    omega
  have hq₀ : 0 < q := by omega
  have hm₀ : 0 < m := by omega
  have hcount : 0 < clusterCount two := by cases two <;> decide
  have hqLe : q ≤ clusterCount two*q*m := by
    exact le_trans (by simpa using (Nat.mul_le_mul_right q hcount)) (by
      simpa using Nat.mul_le_mul_left (clusterCount two*q) hm₀)
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
  have hno (x : ZMod N) (hx : x ∈ S) (y : ZMod N) (hy : y ∈ C) :
      ¬ (graph m p q two).Adj x y := by
    intro he
    have hmem := hcompat x hx y (hC hy) he
    exact (Finset.mem_sdiff.mp hy).2
      (Finset.mem_biUnion.mpr ⟨_,hmem,Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)⟩)
  have hrepr (x : ZMod N) (hx : x ∈ S) :
      ∃ v : Point m p q two, (v.raw : ZMod N) = x-w := by
    let d : ℤ := (x-w).val
    have hd₀ : 0 ≤ d := by dsimp [d]; omega
    have hdN : d < (N:ℤ) := by
      change ((x-w).val : ℤ) < (N:ℤ)
      exact_mod_cast ZMod.val_lt (x-w)
    have he : (d : ZMod N) = x-w := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hn : d = 0 ∨ Allowed m p q two d := by
      by_cases hz : d = 0
      · exact Or.inl hz
      · exact Or.inr (allowed_of_nonadj_lift (by omega) hdN he (fun hh => hno x hx w hw hh.symm))
    obtain ⟨v,hv⟩ := point_repr hm₀ hp hq₀ hd₀ hdN hn
    exact ⟨v,hv.trans he⟩
  let defPoint : Point m p q two := ⟨⟨0,hcount⟩,⟨0,hq₀⟩,0,by omega,by omega,fun _ => by omega,fun _ => by omega⟩
  let pt (x : ZMod N) : Point m p q two :=
    if hx : x ∈ S then (hrepr x hx).choose else defPoint
  have hpt (x : ZMod N) (hx : x ∈ S) : ((pt x).raw : ZMod N) = x-w := by
    simpa only [pt,dif_pos hx] using (hrepr x hx).choose_spec
  let layer (x : ZMod N) : Fin (clusterCount two) × Fin q := ((pt x).cluster,(pt x).period)
  let phase (x : ZMod N) : ℤ := (pt x).phase
  have hinj : Set.InjOn (fun x => (layer x,phase x)) ↑S := by
    intro x hx y hy he
    obtain ⟨he₁,he₂⟩ := Prod.mk.inj he
    obtain ⟨hc,hp'⟩ := Prod.mk.inj he₁
    change (pt x).phase = (pt y).phase at he₂
    have hr : (pt x).raw = (pt y).raw := by
      simp only [Point.raw,hc,hp',he₂]
    exact sub_left_inj.mp ((hpt x hx).symm.trans ((congrArg (fun z : ℤ => (z : ZMod N)) hr).trans
      (hpt y hy)))
  have hcast (x : ZMod N) (hx : x ∈ S) (y : ZMod N) (hy : y ∈ S) :
      (((pt y).raw-(pt x).raw : ℤ) : ZMod N) = y-x := by
    rw [Int.cast_sub,hpt x hx,hpt y hy]
    abel
  have hSame (x y : ZMod N) (he : layer x = layer y) :
      (pt y).raw-(pt x).raw = phase y-phase x := by
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj he
    rw [raw_sub h₁,h₂,sub_self,zero_mul,zero_add]
  have hsmall (x y : ZMod N) (hx : x ∈ S) (hy : y ∈ S) (he : layer x = layer y)
      (hlt : phase x < phase y) (hn : ¬ (graph m p q two).Adj x y) :
      (phase x-phase y).natAbs < 2*m ∧ phase x % 2 = phase y % 2 := by
    have ha := allowed_of_nonadj_lift
      (by rw [hSame x y he]; omega)
      (raw_sub_lt hp (pt x) (pt y)) (hcast x hx y hy) hn
    have hb : phase y-phase x ≤ 2*(m:ℤ)-1 :=
      (band_small hp hpEven (congrArg Prod.fst he) ha).2
    have hs : phase y-phase x < 2*(m:ℤ) := lt_of_le_of_lt hb (by omega)
    have hpar := ha.2.1 (by rw [hSame x y he]; exact hs)
    rw [hSame x y he] at hpar
    constructor <;> omega
  have hodd (x : ZMod N) (hx : x ∈ S) (y : ZMod N) (hy : y ∈ S)
      (he : layer x = layer y) (_ : (phase x-phase y).natAbs < 2*m)
      (hn : phase x % 2 ≠ phase y % 2) : s(x,y) ∈ D := by
    by_cases hlt : phase x < phase y
    · apply hcompat x hx y hy
      by_contra h
      exact hn (hsmall x y hx hy he hlt h).2
    · have hgt : phase y < phase x := by omega
      apply hcompat x hx y hy
      by_contra h
      exact hn (hsmall y x hy hx he.symm hgt (fun hh => h hh.symm)).2.symm
  have hclean (x : ZMod N) (hx : x ∈ C) (y : ZMod N) (hy : y ∈ C)
      (he : layer x = layer y) :
      (phase x-phase y).natAbs < 2*m ∧ phase x % 2 = phase y % 2 := by
    rcases lt_trichotomy (phase x) (phase y) with hlt | hEq | hgt
    · exact hsmall x y (hC hx) (hC hy) he hlt (hno x (hC hx) y hy)
    · simp [hEq,hm₀]
    · have h := hsmall y x (hC hy) (hC hx) he.symm hgt (hno y (hC hy) x hx)
      constructor <;> omega
  have hband (x : ZMod N) (hx : x ∈ S) (y : ZMod N) (hy : y ∈ C)
      (hc : (layer x).1 = (layer y).1) (hn : (layer x).2 ≠ (layer y).2) :
      let d := if (layer x).2 < (layer y).2 then phase y-phase x else phase x-phase y;
      -(2*(m:ℤ))+2 ≤ d ∧ d ≤ 2*(m:ℤ)-1 := by
    by_cases hlt : (layer x).2 < (layer y).2
    · simp only [hlt,if_true]
      apply band_small hp hpEven hc
      exact allowed_of_nonadj_lift (raw_order hp hm₀ hc hlt) (raw_sub_lt hp _ _)
        (hcast x hx y (hC hy)) (hno x hx y hy)
    · simp only [hlt,if_false]
      have hgt : (layer y).2 < (layer x).2 := lt_of_le_of_ne (le_of_not_gt hlt) hn.symm
      apply band_small hp hpEven hc.symm
      exact allowed_of_nonadj_lift (raw_order hp hm₀ hc.symm hgt) (raw_sub_lt hp _ _)
        (hcast y (hC hy) x hx) (fun hh => hno x hx y hy hh.symm)
  exact hlarge.not_ge
    (DiracPhase.card_bound _ _ _ _ hm hq S C hC hremove D hD layer phase hinj hodd hclean hband)

theorem no_colorable_deleteEdges (m p q K r : ℕ) (two : Bool) (hm : r < m) (hq : 2*r < q)
    (hp : (if two then 18 else 6)*m ≤ p) (hpEven : Even p) (hprod : q*p = ((if two then 2 else 1)*q*m)*K)
    (D : Finset (Sym2 (ZMod (q*p+1)))) (hD : D.card ≤ r) :
    ¬ ((graph m p q two).deleteEdges D).Colorable K := by
  classical
  rintro ⟨c⟩
  let a := (if two then 2 else 1)*q*m
  have hclass (i : Fin K) : (Finset.univ.filter (fun x => c x = i)).card ≤ a := by
    apply card_class m p q r two hm hq hp hpEven D hD
    intro x hx y hy he
    by_contra hd
    exact c.valid (SimpleGraph.deleteEdges_adj.mpr ⟨he,hd⟩)
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have hsum : q*p+1 ≤ K*a := by
    calc
      q*p+1 = Fintype.card (ZMod (q*p+1)) := (ZMod.card _).symm
      _ = ∑ i : Fin K, (Finset.univ.filter (fun x => c x = i)).card :=
        Finset.card_eq_sum_card_fiberwise (f := fun x => c x) (by simp)
      _ ≤ ∑ _i : Fin K, a := Finset.sum_le_sum fun i _ => hclass i
      _ = K*a := by simp
  change q*p = a*K at hprod
  rw [Nat.mul_comm K a, ← hprod] at hsum
  omega

end DiracLarge

/-
# Vertex-deletion coloring

The residue coloring below is the coloring in Appendix A of Skottova and Steiner,
Critical edge sets in vertex-critical graphs (arXiv:2508.08703), with zero-based colors.
-/

namespace DiracLarge

private def deleteBlock (m i : ℤ) := (i - 1) / (2 * m)

private def deleteOffset (m i : ℤ) := (i - 1) % (2 * m) / 2

private def deleteParity (m i : ℤ) := (i - 1) % (2 * m) % 2

private def deleteIndex (m i : ℤ) := 2 * deleteBlock m i + deleteParity m i

private def deleteColor (K m i : ℤ) := deleteIndex m i % K

private theorem deleteCoordinates {m i : ℤ} (hm : 0 < m) :
    i = 2 * (m * deleteBlock m i) + 2 * deleteOffset m i + deleteParity m i + 1 ∧
      0 ≤ deleteOffset m i ∧ deleteOffset m i < m ∧
      0 ≤ deleteParity m i ∧ deleteParity m i ≤ 1 := by
  have hp : 0 < 2 * m := by omega
  have h₁ := Int.emod_add_ediv_mul (i - 1) (2 * m)
  have h₂ := Int.emod_add_ediv_mul ((i - 1) % (2 * m)) 2
  have h₃ := Int.emod_lt_of_pos (i - 1) hp
  have h₄ := Int.emod_nonneg (i - 1) hp.ne'
  have h₅ := Int.emod_nonneg ((i - 1) % (2 * m)) (by decide : (2 : ℤ) ≠ 0)
  have h₆ := Int.emod_lt_of_pos ((i - 1) % (2 * m)) (by decide : (0 : ℤ) < 2)
  unfold deleteBlock deleteOffset deleteParity
  rw [mul_comm ((i - 1) / (2 * m)) (2 * m), mul_assoc] at h₁
  rw [mul_comm ((i - 1) % (2 * m) / 2) 2] at h₂
  omega

private theorem deleteSmallMultiple {K h : ℤ} (hK : 4 ≤ K)
    (hlo : -3 ≤ h * K) (hhi : h * K ≤ 3) : h = 0 := by
  by_contra h₀
  rcases lt_or_gt_of_ne h₀ with hneg | hpos
  · nlinarith [mul_nonneg (show 0 ≤ K by omega) (show 0 ≤ -h - 1 by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ K by omega) (show 0 ≤ h - 1 by omega)]

private theorem deletePeriods {K m p q : ℕ} {two : Bool}
    (hP : (p : ℤ) = (if two then 2 else 1) * (K : ℤ) * (m : ℤ))
    (hParity : (K : ℤ) % 2 = if two then 1 else 0) :
    ∃ B W : ℤ, (q : ℤ) * (p : ℤ) = 2 * (m : ℤ) * B ∧ 2 * B = W * (K : ℤ) := by
  cases two
  · simp only [Bool.false_eq_true, if_false] at hP hParity
    have hK₂ : (K : ℤ) = 2 * ((K : ℤ) / 2) := by omega
    refine ⟨(q : ℤ) * ((K : ℤ) / 2), q, ?_, ?_⟩
    · conv_lhs => rw [hP, one_mul, hK₂]
      ring
    · conv_rhs => rw [hK₂]
      ring
  · simp only [if_true] at hP
    refine ⟨(q : ℤ) * (K : ℤ), 2 * (q : ℤ), ?_, ?_⟩
    · rw [hP]
      ring
    · ring

private theorem deleteEqualColorAllowed {K m p q : ℕ} {two : Bool} (hK : 4 ≤ K) (hm : 0 < m)
    (hP : (p : ℤ) = (if two then 2 else 1) * (K : ℤ) * (m : ℤ))
    (hParity : (K : ℤ) % 2 = if two then 1 else 0)
    {i j : ℤ} (hi : 0 < i) (hij : i < j) (hj : j ≤ (q : ℤ) * (p : ℤ))
    (hc : deleteColor K m i = deleteColor K m j) : Allowed m p q two (j - i) := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hKZ : (4 : ℤ) ≤ K := by exact_mod_cast hK
  let bi := deleteBlock m i
  let bj := deleteBlock m j
  let ui := deleteOffset m i
  let uj := deleteOffset m j
  let ei := deleteParity m i
  let ej := deleteParity m j
  obtain ⟨hiRep, hui₀, hui, hei₀, hei⟩ := deleteCoordinates (i := i) hmZ
  obtain ⟨hjRep, huj₀, huj, hej₀, hej⟩ := deleteCoordinates (i := j) hmZ
  change i = 2 * ((m : ℤ) * bi) + 2 * ui + ei + 1 at hiRep
  change j = 2 * ((m : ℤ) * bj) + 2 * uj + ej + 1 at hjRep
  change 0 ≤ ui at hui₀
  change ui < (m : ℤ) at hui
  change 0 ≤ uj at huj₀
  change uj < (m : ℤ) at huj
  change 0 ≤ ei at hei₀
  change ei ≤ 1 at hei
  change 0 ≤ ej at hej₀
  change ej ≤ 1 at hej
  let h := deleteIndex m j / (K : ℤ) - deleteIndex m i / (K : ℤ)
  have hgap : 2 * (bj - bi) + ej - ei = h * (K : ℤ) := by
    have h₁ := Int.emod_add_ediv_mul (deleteIndex m i) (K : ℤ)
    have h₂ := Int.emod_add_ediv_mul (deleteIndex m j) (K : ℤ)
    change deleteIndex m i % (K : ℤ) = deleteIndex m j % (K : ℤ) at hc
    rw [hc] at h₁
    unfold h
    change _ = _ at h₁ h₂
    unfold deleteIndex at h₁ h₂ ⊢
    change 2 * (deleteBlock m j - deleteBlock m i) + deleteParity m j -
      deleteParity m i = _
    linear_combination h₁ - h₂
  let δ : ℤ := 2 * (uj - ui) + (1 - (m : ℤ)) * (ej - ei)
  have hdiff : j - i = h * (K : ℤ) * (m : ℤ) + δ := by
    unfold δ
    linear_combination hjRep - hiRep + (m : ℤ) * hgap
  have hBandSame (he : ej = ei) : -2 * (m : ℤ) + 2 ≤ δ ∧ δ ≤ 2 * (m : ℤ) - 1 := by
    dsimp only [δ]
    rw [he, sub_self, mul_zero, add_zero]
    omega
  refine ⟨?_, fun hsmall => ?_, fun hsmall => ?_⟩
  -- A same-color pair lies in the full-period band or the even-k half-period band.
  · cases two
    · simp only [Bool.false_eq_true, if_false, one_mul] at hP hParity
      have hk₂ : (K : ℤ) = 2 * ((K : ℤ) / 2) := by omega
      have hgap₀ : 2 * (bj - bi) + ej - ei = 2 * (h * ((K : ℤ) / 2)) := by
        rw [hgap]
        linear_combination h * hk₂
      have he : ej = ei := by omega
      obtain ⟨hl, hh⟩ := hBandSame he
      exact Or.inl ⟨h, δ, hl, hh, by rw [hdiff, hP, add_zero, mul_assoc]⟩
    · simp only [if_true] at hP hParity
      have hk₂ : (K : ℤ) = 2 * ((K : ℤ) / 2) + 1 := by omega
      have hgap₀ : 2 * (bj - bi) + ej - ei = 2 * (h * ((K : ℤ) / 2)) + h := by
        rw [hgap]
        linear_combination h * hk₂
      by_cases he : ej = ei
      · have hh₂ : h = 2 * (h / 2) := by omega
        obtain ⟨hl, hh⟩ := hBandSame he
        exact Or.inl ⟨h / 2, δ, hl, hh, by
          rw [hdiff, hP]
          linear_combination ((K : ℤ) * (m : ℤ)) * hh₂⟩
      · have hh₂ : h = 2 * (h / 2) + 1 := by omega
        have hp₂ : ((p / 2 : ℕ) : ℤ) = (K : ℤ) * (m : ℤ) := by
          rw [Int.natCast_ediv, hP]
          have heq : (2 : ℤ) * K * m = 2 * ((K : ℤ) * m) := by ring
          rw [heq]
          omega
        have hδ : -3 * (m : ℤ) + 3 ≤ δ ∧ δ ≤ 3 * (m : ℤ) - 2 := by
          rcases (show ej - ei = 1 ∨ ej - ei = -1 by omega) with hsign | hsign
          · dsimp only [δ]
            rw [hsign, mul_one]
            omega
          · dsimp only [δ]
            rw [hsign, mul_neg_one]
            omega
        exact Or.inr ⟨rfl, h / 2, δ, hδ.1, hδ.2, by
          rw [hdiff, hP, hp₂]
          linear_combination ((K : ℤ) * (m : ℤ)) * hh₂⟩
  -- A short forward gap spans at most two adjacent blocks.
  · have hblock₀ : bi ≤ bj := by
      by_contra! hn
      nlinarith [mul_nonneg hmZ.le (show 0 ≤ bi - bj - 1 by omega)]
    have hblock₁ : bj ≤ bi + 1 := by
      by_contra! hn
      nlinarith [mul_nonneg hmZ.le (show 0 ≤ bj - bi - 2 by omega)]
    have hh : h = 0 := deleteSmallMultiple hKZ (by omega) (by omega)
    have he : ej = ei := by
      rw [hh, zero_mul] at hgap
      omega
    omega
  -- A short gap through zero would join the first and last blocks.
  · have hsmall' : (q : ℤ) * (p : ℤ) + 1 - (j - i) < 2 * (m : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hsmall
    obtain ⟨B, W, hTotal, hMultiple⟩ := deletePeriods (q := q) hP hParity
    have hbi₀ : 0 ≤ bi := Int.ediv_nonneg (by omega) (by omega)
    have hbi : bi = 0 := by
      by_contra hn
      nlinarith [mul_nonneg hmZ.le (show 0 ≤ bi - 1 by omega)]
    have hbj₁ : bj < B := by
      by_contra! hn
      nlinarith [mul_nonneg hmZ.le (show 0 ≤ bj - B by omega)]
    have hbj₂ : B ≤ bj + 1 := by
      by_contra! hn
      nlinarith [mul_nonneg hmZ.le (show 0 ≤ B - bj - 2 by omega)]
    have hbj : bj = B - 1 := by omega
    have hwrap : (W - h) * (K : ℤ) = 2 - ej + ei := by
      rw [hbi, hbj] at hgap
      linear_combination hgap - hMultiple
    have hWh := deleteSmallMultiple hKZ (by omega : -3 ≤ (W - h) * (K : ℤ))
      (by omega : (W - h) * (K : ℤ) ≤ 3)
    rw [hWh, zero_mul] at hwrap
    omega

theorem vertex_delete_colorable {K m p q : ℕ} {two : Bool} (hK : 4 ≤ K) (hm : 0 < m)
    (hP : (p : ℤ) = (if two then 2 else 1) * (K : ℤ) * (m : ℤ))
    (hParity : (K : ℤ) % 2 = if two then 1 else 0) :
    VertexDeleteColorable (graph m p q two) K := by
  have hp : Even p := by
    have hh : (p : ℤ) % 2 = 0 := by
      cases two
      · simp only [Bool.false_eq_true, if_false, one_mul] at hP hParity
        simp [hP, Int.mul_emod, hParity]
      · simp only [if_true] at hP
        simp [hP, Int.mul_emod]
    exact Nat.even_iff.2 (by exact_mod_cast hh)
  have hKZ : (0 : ℤ) < K := by omega
  have hnonneg (i : ℤ) : 0 ≤ deleteColor K m i := Int.emod_nonneg _ hKZ.ne'
  let f (x : {x : ZMod (q * p + 1) // x ≠ 0}) : Fin K :=
    ⟨(deleteColor K m x.1.val).toNat, by
      apply Int.ofNat_lt.mp
      rw [Int.toNat_of_nonneg (hnonneg _)]
      exact Int.emod_lt_of_pos _ hKZ⟩
  have hOrdered (x y : {x : ZMod (q * p + 1) // x ≠ 0}) (hxy : x.1.val < y.1.val)
      (hAdj : (graph m p q two).Adj x.1 y.1) : f x ≠ f y := by
    intro he
    have hc := congrArg (fun c : Fin K => (c.1 : ℤ)) he
    change (((deleteColor K m x.1.val).toNat : ℕ) : ℤ) =
      (((deleteColor K m y.1.val).toNat : ℕ) : ℤ) at hc
    rw [Int.toNat_of_nonneg (hnonneg _), Int.toNat_of_nonneg (hnonneg _)] at hc
    have hi : 0 < (x.1.val : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => x.2 ((ZMod.val_eq_zero x.1).1 h))
    have hij : (x.1.val : ℤ) < (y.1.val : ℤ) := by exact_mod_cast hxy
    have hj : (y.1.val : ℤ) ≤ (q : ℤ) * (p : ℤ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp (ZMod.val_lt y.1) : y.1.val ≤ q * p)
    have hAllowed := deleteEqualColorAllowed hK hm hP hParity hi hij hj hc
    apply nonadj_of_lift hp (d := (y.1.val : ℤ) - (x.1.val : ℤ)) _ _ _ hAllowed hAdj
    · omega
    · push_cast
      omega
    · simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hBase (x y : {x : ZMod (q * p + 1) // x ≠ 0})
      (hAdj : (graph m p q two).Adj x.1 y.1) : f x ≠ f y := by
    have hne : x.1.val ≠ y.1.val := fun he => hAdj.ne (ZMod.val_injective _ he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hOrdered x y hlt hAdj
    · exact (hOrdered y x hgt hAdj.symm).symm
  intro v
  let translate (x : {x : ZMod (q * p + 1) // x ≠ v}) :
      {x : ZMod (q * p + 1) // x ≠ 0} :=
    ⟨x.1 - v, sub_ne_zero.mpr x.2⟩
  refine ⟨fun x => f (translate x), fun x y hAdj => hBase _ _ ?_⟩
  simpa only [translate, sub_eq_add_neg] using
    (graph_translate m p q two x.1 y.1 (-v)).mpr hAdj

end DiracLarge

/- The graph-theoretic interface for the eventual Erdős 944 variant. -/

namespace DiracLarge

open Erdos944

/-- Vertex-deletion colorings and a bound on the effect of edge deletions certify
the required vertex-critical graph. -/
theorem critical_of_deletion {V : Type*} [Finite V] (G : SimpleGraph V)
    (s r : ℕ) (v₀ : V)
    (hdel : ∀ v : V, ∃ c : {x : V // x ≠ v} → Fin s,
      ∀ x y, G.Adj x.val y.val → c x ≠ c y)
    (hn : ∀ D : Finset (Sym2 V), D.card ≤ r →
      ¬ (G.deleteEdges (D : Set (Sym2 V))).Colorable s) :
    G.IsErdos944 (s + 1) r := by
  classical
  have hc : G.Colorable (s + 1) := by
    obtain ⟨c, hc⟩ := hdel v₀
    let g (x : V) : Fin (s + 1) :=
      if hx : x = v₀ then Fin.last s else (c ⟨x, hx⟩).castSucc
    refine ⟨SimpleGraph.Coloring.mk g ?_⟩
    intro x y hxy
    by_cases hx : x = v₀ <;> by_cases hy : y = v₀
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · rw [show g x = Fin.last s from dif_pos hx,
        show g y = (c ⟨y, hy⟩).castSucc from dif_neg hy]
      exact (Fin.castSucc_ne_last _).symm
    · simp [g, hx, hy]
    · simpa [g, hx, hy] using hc ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hG : ¬ G.Colorable s := by
    simpa using hn ∅ (by simp)
  have hχ : G.chromaticNumber = (s : ℕ∞) + 1 :=
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr ⟨hc, hG⟩
  refine ⟨⟨by simpa using hχ, ?_⟩, ?_⟩
  · intro v
    obtain ⟨c, hc⟩ := hdel v
    let H := (⊤ : G.Subgraph).deleteVerts ({v} : Set V)
    have hv (x : H.verts) : x.val ≠ v := x.property.2
    have hcol : H.coe.Colorable s :=
      ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x.val, hv x⟩) (by
        intro x y hxy
        exact hc _ _ (H.coe_adj_sub x y hxy))⟩
    change H.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    have htop := SimpleGraph.chromaticNumber_mono_of_hom
      (SimpleGraph.Subgraph.topIso (G := G)).symm.toHom
    apply lt_of_lt_of_le _ htop
    rw [hχ]
    exact hcol.chromaticNumber_le.trans_lt (ENat.natCast_lt_add_one_iff.mpr le_rfl)
  · intro edges hcrit
    by_contra! hncard
    let hfin : edges.Finite := Set.toFinite _
    have hD : hfin.toFinset.card ≤ r := (Set.ncard_eq_toFinset_card _ hfin).symm ▸ hncard
    apply hn hfin.toFinset hD
    rw [hfin.coe_toFinset]
    have hlt : (G.deleteEdges edges).chromaticNumber < (s : ℕ∞) + 1 := hχ ▸ hcrit
    have hle : (G.deleteEdges edges).chromaticNumber ≤ (s : ℕ∞) :=
      (ENat.lt_add_one_iff (ENat.natCast_ne_top s)).mp hlt
    exact SimpleGraph.chromaticNumber_le_iff_colorable.mp hle

universe u

/-- Transport the deletion coloring hypotheses to the vertex universe of the target. -/
theorem exists_of_finite_deletion {V : Type} [Finite V] (G : SimpleGraph V)
    (s r : ℕ) (v₀ : V)
    (hdel : ∀ v : V, ∃ c : {x : V // x ≠ v} → Fin s,
      ∀ x y, G.Adj x.val y.val → c x ≠ c y)
    (hn : ∀ D : Finset (Sym2 V), D.card ≤ r →
      ¬ (G.deleteEdges (D : Set (Sym2 V))).Colorable s) :
    ∃ (T : Type u) (H : SimpleGraph T), H.IsErdos944 (s + 1) r := by
  classical
  let T := ULift.{u} V
  let enc : T ≃ V := Equiv.ulift
  let H := G.comap enc
  refine ⟨T, H, critical_of_deletion H s r (enc.symm v₀) ?_ ?_⟩
  · intro v
    obtain ⟨c, hc⟩ := hdel (enc v)
    let f (x : {x : T // x ≠ v}) : {y : V // y ≠ enc v} :=
      ⟨enc x.val, fun h => x.property (enc.injective h)⟩
    exact ⟨fun x => c (f x), fun _ _ h => hc _ _ h⟩
  · intro D hD ⟨c⟩
    apply hn (D.image (Sym2.map enc)) (Finset.card_image_le.trans hD)
    refine ⟨SimpleGraph.Coloring.mk (fun x => c (enc.symm x)) ?_⟩
    intro x y hxy
    obtain ⟨hadj, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    apply c.valid
    refine SimpleGraph.deleteEdges_adj.mpr ⟨?_, ?_⟩
    · change G.Adj (enc (enc.symm x)) (enc (enc.symm y))
      simpa using hadj
    · intro he
      apply hnot
      have hm := Finset.mem_image_of_mem (Sym2.map enc) (Finset.mem_coe.mp he)
      simpa [Sym2.map_mk] using hm

end DiracLarge

namespace DiracLarge

open Erdos944

universe u

/-- Use a period at least twenty times the width of the near-zero band. -/
theorem explicit_witness (k r : ℕ) (hk : 7 ≤ k) (he : k % 2 = 0 → 10 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k r := by
  let K := k - 1
  let m := r + 1
  let q := 2 * r + 1
  let two := decide (K % 2 = 1)
  let p := (if two then 2 else 1) * K * m
  have hK : 6 ≤ K := by dsimp [K]; omega
  have hm : 0 < m := Nat.succ_pos r
  have hrm : r < m := Nat.lt_succ_self r
  have hqr : 2 * r < q := Nat.lt_succ_self (2 * r)
  have hEq : q * p = ((if two then 2 else 1) * q * m) * K := by
    dsimp only [p]
    ac_rfl
  have hP : (p : ℤ) = (if two then 2 else 1) * (K : ℤ) * (m : ℤ) := by
    cases ht : two <;> simp [p, ht]
  have hParity : (K : ℤ) % 2 = if two then 1 else 0 := by
    by_cases h : K % 2 = 1 <;> simp [two, h] <;> omega
  have heven : Even p := by
    apply Nat.even_iff.mpr
    cases ht : two
    · have hzero : K % 2 = 0 := by
        simp [ht] at hParity
        omega
      simp [p, ht, Nat.mul_mod, hzero]
    · simp [p, ht, Nat.mul_mod]
  have hbig : (if two then 18 else 6) * m ≤ p := by
    change (if two then 18 else 6) * m ≤ ((if two then 2 else 1) * K) * m
    apply Nat.mul_le_mul_right
    by_cases h : K % 2 = 1
    · have hk' : k % 2 = 0 := by dsimp [K] at h; omega
      have := he hk'
      simp [two, h, K]
      omega
    · simp [two,h]
      omega
  have hex := exists_of_finite_deletion (graph m p q two) K r 0
    (vertex_delete_colorable (by omega) hm hP hParity)
    (no_colorable_deleteEdges m p q K r two hrm hqr hbig heven hEq)
  have hk' : K + 1 = k := by dsimp [K]; omega
  simpa only [hk'] using hex

end DiracLarge



namespace OMA.R_Erdos944_erdos_944_R1
open Erdos944
universe u

/-- A finite graph equipped with its vertex-deletion colorings, with an obstruction
to every coloring after at most r edge deletions. -/
private def FiniteWitness (colors r : ℕ) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin (n+1))),
    (∀ v, ∃ c : {x : Fin (n+1) // x ≠ v} → Fin colors,
      ∀ x y, G.Adj x.val y.val → c x ≠ c y) ∧
    ∀ D : Finset (Sym2 (Fin (n+1))), D.card ≤ r →
      ¬ (G.deleteEdges (D : Set _)).Colorable colors

private theorem FiniteWitness.realize {s r : ℕ} (h : FiniteWitness s r) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 (s+1) r := by
  obtain ⟨n,G,hv,he⟩ := h
  exact DiracLarge.exists_of_finite_deletion G s r 0 hv he

/-- The remaining even chromatic numbers, using k-1 coloring obstructions. -/
def H1 : Prop := ∀ s ∈ ({3, 5, 7} : Finset ℕ), ∀ r ≥ 2, FiniteWitness s r

/-- The remaining odd chromatic number. -/
def H2 : Prop := ∀ r ≥ 2, FiniteWitness 4 r

theorem main : H1 → H2 → type_of% @Erdos944.erdos_944 := by
  intro h₁ h₂ k hk r hr
  suffices hh : ∃ (V : Type _) (G : SimpleGraph V), G.IsErdos944 k (max r 2) by
    obtain ⟨V,G,hv,hrob⟩ := hh
    exact ⟨V,G,hv,fun E hE => (le_max_left r 2).trans_lt (hrob E hE)⟩
  by_cases he : k = 4 ∨ k = 6 ∨ k = 8
  · have hs : k-1 ∈ ({3, 5, 7} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hw := (h₁ (k-1) hs (max r 2) (le_max_right _ _)).realize
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hw
  by_cases h₅ : k = 5
  · subst k
    exact (h₂ (max r 2) (le_max_right _ _)).realize
  exact DiracLarge.explicit_witness k (max r 2) (by omega) (by omega)
end OMA.R_Erdos944_erdos_944_R1
