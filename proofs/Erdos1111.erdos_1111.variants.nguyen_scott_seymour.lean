import FormalConjectures.ErdosProblems.«1111»
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
Dense vertex sets in the proof of Theorem 3.1 of Nguyen, Scott, and Seymour,
[On a problem of El-Zahar and Erdős](https://arxiv.org/abs/2303.13449).
-/

open SimpleGraph Finset
open scoped BigOperators

namespace NSS1111

noncomputable def degreeOn {V : Type*} (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  open Classical in (A.filter (G.Adj v)).card

noncomputable def arcs {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  ∑ v ∈ A, degreeOn G A v

def Dense {V : Type*} (G : SimpleGraph V) (p : ℕ) (A : Finset V) : Prop :=
  A.Nonempty ∧ 2*p*A.card ≤ arcs G A

theorem degreeOn_le_card {V : Type*} (G : SimpleGraph V) (A : Finset V) (v : V) :
    degreeOn G A v ≤ A.card := by
  classical
  unfold degreeOn
  exact Finset.card_filter_le _ _

theorem degreeOn_lt_card {V : Type*} (G : SimpleGraph V) (A : Finset V) {v : V} (hv : v ∈ A) :
    degreeOn G A v < A.card := by
  classical
  unfold degreeOn
  have h : A.filter (G.Adj v) ⊆ A.erase v := by
    intro x hx
    obtain ⟨hx,hvx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨hvx.ne',hx⟩
  exact (Finset.card_le_card h).trans_lt (Finset.card_erase_lt_of_mem hv)

theorem degreeOn_erase_add {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) {u : V} (hu : u ∈ A) (v : V) :
    degreeOn G (A.erase u) v + (open Classical in if G.Adj v u then 1 else 0) =
      degreeOn G A v := by
  classical
  unfold degreeOn
  rw [Finset.filter_erase]
  by_cases hv : G.Adj v u
  · have hmem : u ∈ A.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hu,hv⟩
    rw [if_pos hv]
    exact Finset.card_erase_add_one hmem
  · have hmem : u ∉ A.filter (G.Adj v) := fun h => hv (Finset.mem_filter.mp h).2
    rw [if_neg hv,Finset.erase_eq_of_notMem hmem,Nat.add_zero]

theorem degreeOn_erase_le_and_add_one {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) {u : V} (hu : u ∈ A) (v : V) :
    degreeOn G (A.erase u) v ≤ degreeOn G A v ∧
      degreeOn G A v ≤ degreeOn G (A.erase u) v + 1 := by
  classical
  have h := degreeOn_erase_add G A hu v
  split at h <;> omega

theorem arcs_erase_add {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    {u : V} (hu : u ∈ A) :
    arcs G (A.erase u) + 2 * degreeOn G A u = arcs G A := by
  classical
  have hsum : ∑ v ∈ A.erase u, (if G.Adj v u then 1 else 0) = degreeOn G A u := by
    have he : (A.erase u).filter (G.Adj u) = A.filter (G.Adj u) := by
      rw [Finset.filter_erase,Finset.erase_eq_of_notMem]
      simp
    simp_rw [fun v : V => show G.Adj v u = G.Adj u v from propext (G.adj_comm v u)]
    rw [← Finset.sum_filter]
    simp [he,degreeOn]
  have he : (∑ v ∈ A.erase u, (degreeOn G (A.erase u) v + (if G.Adj v u then 1 else 0))) =
      (∑ v ∈ A.erase u, degreeOn G A v) :=
    Finset.sum_congr rfl (fun v _ => degreeOn_erase_add G A hu v)
  rw [Finset.sum_add_distrib,hsum] at he
  have htotal := Finset.sum_erase_add A (degreeOn G A) hu
  unfold arcs
  omega

theorem arcs_insert_add {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    {u : V} (hu : u ∉ A) :
    arcs G (insert u A) = arcs G A + 2 * degreeOn G A u := by
  classical
  have e : (insert u A).erase u = A := Finset.erase_insert hu
  have h := arcs_erase_add G (insert u A) (Finset.mem_insert_self u A)
  have h' := degreeOn_erase_add G (insert u A) (Finset.mem_insert_self u A) u
  rw [e,if_neg G.irrefl,Nat.add_zero] at h'
  rwa [e,← h',eq_comm] at h

theorem dense_card_at_least_three {V : Type*} (G : SimpleGraph V) {p : ℕ} (hp : 1 ≤ p)
    {A : Finset V} (ha : Dense G p A) : 3 ≤ A.card := by
  have ha' := ha.1.card_pos
  have hs : arcs G A ≤ A.card * (A.card - 1) := by
    unfold arcs
    calc
      _ ≤ ∑ v ∈ A, (A.card - 1) := Finset.sum_le_sum (fun v hv => by
        have h := degreeOn_lt_card G A hv
        omega)
      _ = _ := by simp
  have h := ha.2.trans hs
  have h' : (2*p)*A.card ≤ (A.card - 1)*A.card := by rwa [Nat.mul_comm A.card] at h
  have he := Nat.le_of_mul_le_mul_right h'
  omega

def Rock {V : Type*} (G : SimpleGraph V) (p : ℕ) (A : Finset V) : Prop :=
  Dense G p A ∧
  (∀ B, Dense G p B → A.card ≤ B.card) ∧
  (∀ B : Finset V, B.card = A.card → arcs G B ≤ arcs G A)

theorem exists_rock {V : Type*} [Fintype V] (G : SimpleGraph V) (p : ℕ)
    (h : ∃ A : Finset V, Dense G p A) : ∃ A : Finset V, Rock G p A := by
  classical
  let D := (Finset.univ : Finset (Finset V)).filter (Dense G p)
  have hd : D.Nonempty := by obtain ⟨A,hA⟩ := h; exact ⟨A,by simp [D,hA]⟩
  obtain ⟨B,hB,hm⟩ := Finset.exists_min_image D Finset.card hd
  have hDense : Dense G p B := (Finset.mem_filter.mp hB).2
  let C := (Finset.univ : Finset (Finset V)).filter (fun X => X.card = B.card)
  have hc : C.Nonempty := ⟨B,by simp [C]⟩
  obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image C (arcs G) hc
  have hc' : A.card = B.card := (Finset.mem_filter.mp hA).2
  have h₁ : Dense G p A :=
    ⟨Finset.card_pos.mp (hc'.symm ▸ hDense.1.card_pos),
      (hc' ▸ hDense.2).trans (hmax B (by simp [C]))⟩
  exact ⟨A,h₁,fun X hX => hc'.symm ▸ hm X (by simp [D,hX]),
    fun X hX => hmax X (by simp [C,hX,hc'])⟩

private theorem erase_lt_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {p : ℕ} (hp : 1 ≤ p) {A : Finset V} (hA : Rock G p A) {u : V} (hu : u ∈ A) :
    arcs G (A.erase u) < 2*p*(A.card-1) := by
  have hc := dense_card_at_least_three G hp hA.1
  have hs := Finset.card_erase_of_mem hu
  by_contra! he
  have hDense : Dense G p (A.erase u) := ⟨Finset.card_pos.mp (by omega), by simpa [hs] using he⟩
  have h := hA.2.1 _ hDense
  omega

theorem rock_arc_bound {V : Type*} (G : SimpleGraph V)
    {p : ℕ} (hp : 1 ≤ p) {A : Finset V} (hA : Rock G p A) :
    arcs G A < 4*p*A.card := by
  classical
  have hc := dense_card_at_least_three G hp hA.1
  have hsum : (∑ u ∈ A, arcs G (A.erase u)) < A.card * (2*p*(A.card-1)) := by
    calc
      _ < ∑ _ ∈ A, (2*p*(A.card-1)) :=
        Finset.sum_lt_sum_of_nonempty hA.1.1 (fun u hu => erase_lt_density G hp hA hu)
      _ = _ := by simp
  have he : (∑ u ∈ A, (arcs G (A.erase u) + 2*degreeOn G A u)) =
      ∑ _ ∈ A, arcs G A :=
    Finset.sum_congr rfl (fun u hu => arcs_erase_add G A hu)
  rw [Finset.sum_add_distrib,← Finset.mul_sum, ← show arcs G A = ∑ u ∈ A, degreeOn G A u from rfl,
    Finset.sum_const, smul_eq_mul] at he
  have hsplit : (A.card - 2) + 2 = A.card := by omega
  have hsum_eq : (∑ u ∈ A, arcs G (A.erase u)) = (A.card - 2) * arcs G A := by
    rw [← hsplit,Nat.add_mul] at he
    exact Nat.add_right_cancel he
  rw [hsum_eq] at hsum
  have hx : A.card * (2*p*(A.card-1)) ≤ (A.card-2) * (4*p*A.card) := by
    calc
      _ = (2*p*A.card) * (A.card-1) := by ring
      _ ≤ (2*p*A.card) * (2*(A.card-2)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_left (hsum.trans_le hx)

theorem rock_outside_degree {V : Type*} (G : SimpleGraph V)
    {p : ℕ} (hp : 1 ≤ p) {A : Finset V} (hA : Rock G p A) {v : V} (hv : v ∉ A) :
    degreeOn G A v ≤ 4*p := by
  classical
  by_contra! h
  have hrow (u : V) (hu : u ∈ A) : 4*p ≤ degreeOn G A u := by
    let B := insert v (A.erase u)
    have hnv : v ∉ A.erase u := fun h => hv (Finset.mem_of_mem_erase h)
    have hc : B.card = A.card := by
      change (insert v (A.erase u)).card = A.card
      rw [Finset.card_insert_of_notMem hnv,Finset.card_erase_add_one hu]
    have hmax := hA.2.2 B hc
    change arcs G (insert v (A.erase u)) ≤ arcs G A at hmax
    rw [arcs_insert_add G (A.erase u) hnv] at hmax
    have he := arcs_erase_add G A hu
    have hl := (degreeOn_erase_le_and_add_one G A hu v).2
    omega
  have hs : A.card * (4*p) ≤ arcs G A := by
    unfold arcs
    simpa using Finset.sum_le_sum (fun u hu => hrow u hu)
  have ht := rock_arc_bound G hp hA
  rw [Nat.mul_comm A.card] at hs
  omega


section Coloring

variable {V : Type*} {G : SimpleGraph V}

private theorem partial_coloring (G : SimpleGraph V) {A : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ B ⊆ A, B.Nonempty → ∃ v ∈ B, degreeOn G B v < k) :
    ∃ f : V → Fin k, ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → f u ≠ f v := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx,hdeg⟩ := h A Subset.rfl hA
    obtain ⟨f,hf⟩ := partial_coloring G (A := A.erase x) hk
      (fun B hB => h B (hB.trans (Finset.erase_subset _ _)))
    let neighbors := A.filter (G.Adj x)
    let colors := neighbors.image f
    have hcard : colors.card < k := (Finset.card_image_le).trans_lt hdeg
    have hcard' : colors.card < (Finset.univ : Finset (Fin k)).card := by simpa using hcard
    obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
    let f' (u : V) := if u = x then c else f u
    have diff (v : V) (hv : v ∈ A) (hAdj : G.Adj x v) : c ≠ f v := by
      intro he
      apply hc
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hAdj⟩,he.symm⟩
    refine ⟨f',fun u hu v hv hadj => ?_⟩
    by_cases hux : u = x
    · subst u
      simpa [f',hadj.ne'] using diff v hv hadj
    · by_cases hvx : v = x
      · subst v
        simpa [f',hux] using (diff u hu hadj.symm).symm
      · simpa [f',hux,hvx] using
          hf u (Finset.mem_erase.mpr ⟨hux,hu⟩) v (Finset.mem_erase.mpr ⟨hvx,hv⟩) hadj
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    exact ⟨fun _ => ⟨0,hk⟩,by simp⟩
termination_by A.card
decreasing_by
  classical
  exact Finset.card_erase_lt_of_mem hx

theorem colorable_of_degenerate (G : SimpleGraph V) {A : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ B ⊆ A, B.Nonempty → ∃ v ∈ B, degreeOn G B v < k) :
    (G.induce (A : Set V)).Colorable k := by
  obtain ⟨f,hf⟩ := partial_coloring G hk h
  exact ⟨SimpleGraph.Coloring.mk (fun v => f v.val) (fun {u v} hadj =>
    hf u.val u.property v.val v.property hadj)⟩

theorem dense_of_not_colorable (G : SimpleGraph V) {p : ℕ} (hp : 1 ≤ p) {S : Finset V}
    (hc : ¬ (G.induce (S : Set V)).Colorable (2*p)) : ∃ A ⊆ S, Dense G p A := by
  classical
  by_contra! h
  apply hc
  apply colorable_of_degenerate G (by omega)
  intro B hB hn
  by_contra! he
  have hArc : (2*p)*B.card ≤ arcs G B := by
    unfold arcs
    calc
      _ = ∑ _ ∈ B, 2*p := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum he
  exact h B hB ⟨hn,hArc⟩

theorem core_of_dense {p : ℕ} (hp : 1 ≤ p) {A : Finset V} (hA : Dense G p A) :
    ∃ B ⊆ A, B.Nonempty ∧ ∀ v ∈ B, p ≤ degreeOn G B v := by
  classical
  let D := A.powerset.filter (Dense G p)
  have hD : D.Nonempty := ⟨A,by simp [D,hA]⟩
  obtain ⟨B,hB,hmin⟩ := Finset.exists_min_image D Finset.card hD
  have hs : B ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hd : Dense G p B := (Finset.mem_filter.mp hB).2
  refine ⟨B,hs,hd.1,fun v hv => ?_⟩
  by_contra! hdeg
  have hcard : 3 ≤ B.card := dense_card_at_least_three G hp hd
  have herase : (B.erase v).card = B.card-1 := Finset.card_erase_of_mem hv
  have hsub : B.erase v ⊆ A := (Finset.erase_subset v B).trans hs
  have hnon : (B.erase v).Nonempty := Finset.card_pos.mp (by omega)
  have ha := arcs_erase_add G B hv
  have hda := hd.2
  have hbound : 2*p*(B.erase v).card ≤ arcs G (B.erase v) := by
    rw [← Finset.card_erase_add_one hv,Nat.mul_add,Nat.mul_one] at hda
    omega
  have hv' := hmin (B.erase v) (by simp [D,hsub,show Dense G p (B.erase v) from ⟨hnon,hbound⟩])
  omega

theorem rock_colorable {V : Type*} (G : SimpleGraph V) {p : ℕ} (hp : 1 ≤ p) {A : Finset V}
    (hA : Rock G p A) : (G.induce (A : Set V)).Colorable (2*p+1) := by
  classical
  apply colorable_of_degenerate G (by omega)
  intro B hB hn
  by_contra! he
  obtain ⟨v,hv⟩ := hn
  have hcard : 1 < B.card := (by have hh := he v hv; omega : 1 < degreeOn G B v).trans
    (degreeOn_lt_card G B hv)
  have hdense : Dense G p (B.erase v) := by
    refine ⟨Finset.card_pos.mp (by simp [Finset.card_erase_of_mem hv]; omega),?_⟩
    unfold arcs
    rw [show 2*p*(B.erase v).card = ∑ _ ∈ B.erase v, 2*p from by simp [Nat.mul_comm]]
    apply Finset.sum_le_sum
    intro u hu
    have hg := he u (Finset.mem_of_mem_erase hu)
    have hj := (degreeOn_erase_le_and_add_one G B hv u).2
    omega
  have hlt := hA.2.1 _ hdense
  have hle := Finset.card_le_card hB
  have hErase := Finset.card_erase_lt_of_mem hv
  omega

theorem colorable_of_cover {I : Type*} [Fintype I] (G : SimpleGraph V)
    (S : Set V) (A : I → Set V) (k : I → ℕ)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ A i) (hcolor : ∀ i, (G.induce (A i)).Colorable (k i)) :
    (G.induce S).Colorable (∑ i, k i) := by
  classical
  choose i hi using (fun x : S => hcover x.val x.property)
  have color_eq {a b : I} (he : a = b) {x y : V} (hx : x ∈ A a) (hy : y ∈ A b)
      (hc : HEq ((hcolor a).some ⟨x,hx⟩) ((hcolor b).some ⟨y,hy⟩)) :
      (hcolor a).some ⟨x,hx⟩ =
        (hcolor a).some ⟨y,Eq.mp (congrArg (fun j => y ∈ A j) he.symm) hy⟩ := by
    subst b
    exact eq_of_heq hc
  let c : (G.induce S).Coloring (Σ j, Fin (k j)) :=
    SimpleGraph.Coloring.mk
      (fun x => ⟨i x,(hcolor (i x)).some ⟨x.val,hi x⟩⟩)
      (fun {u v} hadj he => by
        obtain ⟨hEq,hColor⟩ := Sigma.mk.inj_iff.mp he
        let j := i u
        let u' : A j := ⟨u.val,hi u⟩
        let v' : A j := ⟨v.val,Eq.mp (congrArg (fun j => v.val ∈ A j) hEq.symm) (hi v)⟩
        apply (hcolor j).some.valid (show (G.induce (A j)).Adj u' v' from hadj)
        exact color_eq hEq (hi u) (hi v) hColor)
  simpa only [Fintype.card_sigma,Fintype.card_fin] using c.colorable

end Coloring

end NSS1111

/- A finite second-moment estimate for the random partition in Theorem 3.1
of Nguyen, Scott, and Seymour (https://arxiv.org/abs/2303.13449). -/

open Finset
open scoped BigOperators

namespace NSSPartition

noncomputable def flag {C : Type*} (J : Finset C) (x : C) : ℝ :=
  open Classical in if x ∈ J then 1 else 0

noncomputable def retained {V C : Type*} (U : Finset V) (J : Finset C) (f : V → C) : ℝ :=
  ∏ v ∈ U, flag J (f v)

theorem retained_eq_ite {V C : Type*} (U : Finset V) (J : Finset C) (f : V → C) :
    retained U J f = (open Classical in if ∀ v ∈ U, f v ∈ J then 1 else 0) := by
  classical
  simp [retained,flag,Finset.prod_ite_zero]

private theorem expect_prod {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] (f : V → C → ℝ) :
    (𝔼 g : V → C, ∏ v, f v (g v)) = ∏ v, (𝔼 x : C, f v x) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib,Fintype.prod_sum,Finset.prod_const,Finset.card_univ,Fintype.card_fun,
    Nat.cast_pow]

theorem expect_retained {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C]
    (U : Finset V) (J : Finset C) :
    (𝔼 f : V → C, retained U J f) = ((J.card : ℝ) / Fintype.card C) ^ U.card := by
  classical
  let g (v : V) (x : C) : ℝ := if v ∈ U then flag J x else 1
  have hm (f : V → C) : retained U J f = ∏ v, g v (f v) := by
    simp [g,retained]
  simp_rw [hm]
  rw [expect_prod]
  have hFlag : (𝔼 x : C, flag J x) = (J.card : ℝ) / Fintype.card C := by
    rw [Fintype.expect_eq_sum_div_card]
    simp [flag]
  have hh (v : V) : (𝔼 x : C, g v x) =
      if v ∈ U then (J.card : ℝ) / Fintype.card C else 1 := by
    by_cases hv : v ∈ U
    · simpa [g,hv] using hFlag
    · simp [g,hv]
  simp_rw [hh]
  rw [Finset.prod_ite_mem_eq,Finset.prod_const]

private theorem moment_disjoint {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C]
    (J : Finset C) {U W : Finset V} (h : Disjoint U W) :
    (𝔼 f : V → C, retained U J f * retained W J f) =
      (𝔼 f : V → C, retained U J f) * (𝔼 f : V → C, retained W J f) := by
  classical
  have he (f : V → C) :
      retained U J f * retained W J f = retained (U ∪ W) J f := by
    unfold retained
    rw [Finset.prod_union h]
  simp_rw [he,expect_retained]
  rw [Finset.card_union_of_disjoint h,pow_add]

noncomputable def edgeCount {V E C : Type*} [Fintype E] (U : E → Finset V)
    (J : Finset C) (f : V → C) : ℝ := ∑ e, retained (U e) J f

noncomputable def overlap {V E : Type*} [Fintype E] (U : E → Finset V) : ℝ :=
  open Classical in ∑ e, ∑ f, if Disjoint (U e) (U f) then 0 else 1

private theorem mean_edgeCount_le {V E C : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype C] [Nonempty C]
    (U : E → Finset V) (hU : ∀ e, (U e).card ≤ 2) (J : Finset C)
    (hJ : 2*J.card = Fintype.card C) :
    (Fintype.card E : ℝ)/4 ≤ 𝔼 f : V → C, edgeCount U J f := by
  classical
  have hC : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR : ((J.card : ℝ) / Fintype.card C) = 1/2 := by
    field_simp
    rw [mul_comm]
    exact_mod_cast hJ
  have hLower (e : E) : (1/4 : ℝ) ≤ 𝔼 f : V → C, retained (U e) J f := by
    rw [expect_retained,hR]
    have hc := hU e
    interval_cases (U e).card <;> norm_num
  unfold edgeCount
  rw [Finset.expect_sum_comm]
  calc
    _ = ∑ _ : E, (1/4 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum (fun e _ => hLower e)

private theorem variance_le_overlap {V E C : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype C] [Nonempty C]
    (U : E → Finset V) (J : Finset C) :
    (𝔼 f : V → C, (edgeCount U J f - (𝔼 g : V → C, edgeCount U J g)) ^ 2) ≤ overlap U := by
  classical
  let F (e : E) (f : V → C) := retained (U e) J f
  let m (e : E) := 𝔼 f : V → C, F e f
  have hmean : (𝔼 f : V → C, edgeCount U J f) = ∑ e, m e := by
    exact Finset.expect_sum_comm _ _ (fun f e => F e f)
  have hzero (e f : E) (h : Disjoint (U e) (U f)) :
      (𝔼 g : V → C, (F e g - m e) * (F f g - m f)) = 0 := by
    have hEq (g : V → C) : (F e g - m e) * (F f g - m f) =
        ((F e g * F f g - F e g * m f) - m e * F f g) + m e * m f := by ring
    simp_rw [hEq]
    rw [Finset.expect_add_distrib,Finset.expect_sub_distrib,Finset.expect_sub_distrib,
      ← Finset.expect_mul,← Finset.mul_expect,Fintype.expect_const]
    change ((𝔼 g : V → C, retained (U e) J g * retained (U f) J g) - m e * m f) -
      m e * m f + m e * m f = 0
    rw [moment_disjoint J h]
    change (m e * m f - m e * m f) - m e * m f + m e * m f = 0
    ring
  have hbound (e f : E) :
      (𝔼 g : V → C, (F e g - m e) * (F f g - m f)) ≤
        if Disjoint (U e) (U f) then 0 else 1 := by
    split_ifs with h
    · exact (hzero e f h).le
    apply Finset.expect_le Finset.univ_nonempty
    intro g _
    have hF (i : E) (x : V → C) : 0 ≤ F i x ∧ F i x ≤ 1 := by
      unfold F
      rw [retained_eq_ite]
      split <;> norm_num
    have hm (i : E) : 0 ≤ m i ∧ m i ≤ 1 :=
      ⟨Finset.expect_nonneg (fun x _ => (hF i x).1),
       Finset.expect_le Finset.univ_nonempty (fun x _ => (hF i x).2)⟩
    have h₁ : |F e g - m e| ≤ 1 := abs_le.mpr ⟨by linarith [(hF e g).1,(hm e).2],
      by linarith [(hF e g).2,(hm e).1]⟩
    have h₂ : |F f g - m f| ≤ 1 := abs_le.mpr ⟨by linarith [(hF f g).1,(hm f).2],
      by linarith [(hF f g).2,(hm f).1]⟩
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul h₁ h₂ (abs_nonneg _) zero_le_one).trans (by norm_num))
  have hsq (g : V → C) : (edgeCount U J g - (𝔼 f : V → C, edgeCount U J f)) ^ 2 =
      ∑ e, ∑ f, (F e g - m e) * (F f g - m f) := by
    rw [hmean]
    change ((∑ e, F e g) - (∑ e, m e)) ^ 2 = _
    rw [← Finset.sum_sub_distrib,pow_two,Finset.sum_mul_sum]
  simp_rw [hsq,Finset.expect_sum_comm]
  apply Finset.sum_le_sum
  intro e _
  apply Finset.sum_le_sum
  intro f _
  by_cases h : Disjoint (U e) (U f) <;> simpa [h] using hbound e f

theorem color_many {V E C I : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype C] [Fintype I] [Nonempty C]
    (U : E → Finset V) (hU : ∀ e, (U e).card ≤ 2) (J : I → Finset C)
    (hJ : ∀ i, 2*(J i).card = Fintype.card C)
    (hO : (Fintype.card I : ℝ) * overlap U < (Fintype.card E : ℝ)^2/64) :
    ∃ f : V → C, ∀ i, (Fintype.card E : ℝ)/8 ≤ edgeCount U (J i) f := by
  classical
  let m (i : I) := 𝔼 g : V → C, edgeCount U (J i) g
  let F (f : V → C) := ∑ i, (edgeCount U (J i) f - m i)^2
  have hF : (𝔼 f : V → C, F f) < (Fintype.card E : ℝ)^2/64 := by
    unfold F
    rw [Finset.expect_sum_comm]
    apply lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => variance_le_overlap U (J i)))
    simpa using hO
  obtain ⟨f,_,hf⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty hF
  refine ⟨f,fun i => ?_⟩
  by_contra! hi
  have hle := mean_edgeCount_le U hU (J i) (hJ i)
  have hs : (edgeCount U (J i) f - m i)^2 ≤ F f :=
    Finset.single_le_sum (fun j _ => sq_nonneg (edgeCount U (J j) f - m j)) (Finset.mem_univ i)
  have hnon : (0 : ℝ) ≤ (Fintype.card E : ℝ)/8 := by positivity
  have hh : (Fintype.card E : ℝ)/8 ≤ m i - edgeCount U (J i) f := by
    change (Fintype.card E : ℝ)/4 ≤ m i at hle
    linarith
  have hsq := pow_le_pow_left₀ hnon hh 2
  nlinarith


section Incidence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

noncomputable def incidence (S : E → Finset V) (v : V) : ℝ :=
  ∑ e, if v ∈ S e then 1 else 0

omit [Fintype V] in
private theorem incidence_nonneg (S : E → Finset V) (v : V) : 0 ≤ incidence S v := by
  unfold incidence
  exact Finset.sum_nonneg (fun e _ => by split <;> norm_num)

omit [Fintype V] in
private theorem incidence_le_of_subset {U S : E → Finset V}
    (h : ∀ e, U e ⊆ S e) (v : V) : incidence U v ≤ incidence S v := by
  unfold incidence
  apply Finset.sum_le_sum
  intro e _
  by_cases hu : v ∈ U e
  · simp [hu,h e hu]
  · simp [hu]; split <;> norm_num

private theorem incidence_sum (S : E → Finset V) :
    ∑ v, incidence S v = ∑ e, ((S e).card : ℝ) := by
  unfold incidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

set_option maxHeartbeats 1000000 in
private theorem overlap_le_square_incidence (U : E → Finset V) :
    overlap U ≤ ∑ v, (incidence U v)^2 := by
  classical
  let h (v : V) (e : E) : ℝ := if v ∈ U e then 1 else 0
  have hn (v : V) (e : E) : 0 ≤ h v e := by unfold h; split <;> norm_num
  have h₁ (e f : E) :
      (if Disjoint (U e) (U f) then (0:ℝ) else 1) ≤ ∑ v, h v e * h v f := by
    by_cases hd : Disjoint (U e) (U f)
    · simp only [if_pos hd]
      exact Finset.sum_nonneg (fun v _ => mul_nonneg (hn v e) (hn v f))
    · obtain ⟨v,hv,hv'⟩ := Finset.not_disjoint_iff.mp hd
      have hs := Finset.single_le_sum
        (fun w (_ : w ∈ (Finset.univ : Finset V)) => mul_nonneg (hn w e) (hn w f))
        (Finset.mem_univ v)
      simpa [hd,h,hv,hv'] using hs
  have hle : overlap U ≤ ∑ e : E, ∑ f : E, ∑ v : V, h v e * h v f := by
    unfold overlap
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sum_le_sum
    intro f _
    by_cases hd : Disjoint (U e) (U f) <;> simpa [hd] using h₁ e f
  refine hle.trans_eq ?_
  calc
    _ = ∑ e, ∑ v, ∑ f, h v e * h v f := by
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ v, ∑ e, ∑ f, h v e * h v f := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [show incidence U v = ∑ e, h v e from rfl,pow_two,Finset.sum_mul_sum]

theorem extract_exceptional (A : Finset V) (S : E → Finset V) (hS : ∀ e, S e ⊆ A)
    (hcard : ∀ e, (S e).card ≤ 2) (hE : 0 < Fintype.card E)
    (L : ℕ) (hL : 0 < L) :
    ∃ X ⊆ A, X.card ≤ 2*L ∧
      overlap (fun e => S e \ X) ≤ 2*(Fintype.card E : ℝ)^2/L := by
  classical
  let m : ℝ := Fintype.card E
  have hm : 0 < m := by unfold m; exact_mod_cast hE
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  let X := A.filter (fun v => m ≤ L * incidence S v)
  let U (e : E) := S e \ X
  have htotal : ∑ v, incidence S v ≤ 2*m := by
    rw [incidence_sum,show 2*m = ∑ _ : E, (2:ℝ) from by simp [m,mul_comm]]
    exact Finset.sum_le_sum (fun e _ => by exact_mod_cast hcard e)
  have hX : (X.card : ℝ) * m ≤ (L:ℝ) * (2*m) := by
    calc
      _ = ∑ v ∈ X, m := by simp
      _ ≤ ∑ v ∈ X, (L:ℝ)*incidence S v :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = (L:ℝ) * ∑ v ∈ X, incidence S v := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ =>
          incidence_nonneg S v)).trans htotal) hL'.le
  have hX' : (X.card : ℝ) ≤ 2 * L := by
    apply le_of_mul_le_mul_right ?_ hm
    calc
      _ ≤ (L:ℝ)*(2*m) := hX
      _ = _ := by ring
  have hmU (v : V) : incidence U v ≤ m/L := by
    by_cases hv : v ∈ X
    · have hh (e : E) : v ∉ U e := fun he => (Finset.mem_sdiff.mp he).2 hv
      have hzero : incidence U v = 0 := by unfold incidence; simp [hh]
      rw [hzero]
      exact div_nonneg hm.le hL'.le
    have hu : incidence U v ≤ incidence S v :=
      incidence_le_of_subset (fun e => Finset.sdiff_subset) v
    by_cases ha : v ∈ A
    · have hlo : (L:ℝ) * incidence S v < m := by
        by_contra! hh
        exact hv (Finset.mem_filter.mpr ⟨ha,hh⟩)
      exact hu.trans (le_of_lt ((lt_div_iff₀ hL').mpr (by rwa [mul_comm])))
    · have hh (e : E) : v ∉ S e := fun h => ha (hS e h)
      have hzero : incidence S v = 0 := by unfold incidence; simp [hh]
      exact hu.trans (hzero.symm ▸ div_nonneg hm.le hL'.le)
  refine ⟨X,Finset.filter_subset _ _,by exact_mod_cast hX',?_⟩
  have htotalU : ∑ v, incidence U v ≤ 2*m :=
    (Finset.sum_le_sum (fun v _ => incidence_le_of_subset (fun e => Finset.sdiff_subset) v)).trans htotal
  apply (overlap_le_square_incidence U).trans
  calc
    _ ≤ ∑ v, (m/L)*incidence U v :=
      Finset.sum_le_sum (fun v _ => by rw [pow_two]; exact mul_le_mul_of_nonneg_right (hmU v) (incidence_nonneg U v))
    _ = (m/L)*∑ v, incidence U v := by rw [Finset.mul_sum]
    _ ≤ (m/L)*(2*m) := mul_le_mul_of_nonneg_left htotalU (div_nonneg hm.le hL'.le)
    _ = _ := by simp only [m]; ring

end Incidence

end NSSPartition

namespace NSS1111

open NSSPartition

noncomputable def pairs {V : Type*} (G : SimpleGraph V) (A : Finset V) : Finset (V×V) :=
  open Classical in (A ×ˢ A).filter (fun p => G.Adj p.1 p.2)

theorem mem_pairs {V : Type*} {G : SimpleGraph V} {A : Finset V} {u v : V} :
    (u,v) ∈ pairs G A ↔ u ∈ A ∧ v ∈ A ∧ G.Adj u v := by
  classical
  simp [pairs,and_assoc]

theorem arcs_eq_pairs_card {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    arcs G A = (pairs G A).card := by
  classical
  unfold arcs pairs
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v _
  unfold degreeOn
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]

noncomputable def chosen {V C : Type*} (A X : Finset V) (f : V → C)
    (J : Finset C) : Finset V :=
  open Classical in A.filter (fun v => v ∈ X ∨ f v ∈ J)

theorem mem_chosen {V C : Type*} {A X : Finset V} {f : V → C} {J : Finset C} {x : V} :
    x ∈ chosen A X f J ↔ x ∈ A ∧ (x ∈ X ∨ f x ∈ J) := by
  classical
  simp [chosen]

private theorem edges_inside {V C : Type*} [DecidableEq V] (G : SimpleGraph V) (A X : Finset V)
    (f : V → C) (J : Finset C) :
    let E := pairs G A
    let U : E → Finset V := fun e => ({e.val.1,e.val.2} : Finset V) \ X
    edgeCount U J f = (arcs G (chosen A X f J) : ℝ) := by
  classical
  intro E U
  let B := chosen A X f J
  have hval (e : E) : retained (U e) J f = if e.val.1 ∈ B ∧ e.val.2 ∈ B then 1 else 0 := by
    have hmem : e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ G.Adj e.val.1 e.val.2 := mem_pairs.mp e.property
    rw [retained_eq_ite]
    have hCond : (∀ v ∈ U e, f v ∈ J) ↔ e.val.1 ∈ B ∧ e.val.2 ∈ B := by
      constructor
      · intro h
        refine ⟨mem_chosen.mpr ⟨hmem.1,?_⟩,mem_chosen.mpr ⟨hmem.2.1,?_⟩⟩
        · exact or_iff_not_imp_left.mpr (fun h' =>
            h _ (Finset.mem_sdiff.mpr ⟨by simp,h'⟩))
        · exact or_iff_not_imp_left.mpr (fun h' =>
            h _ (Finset.mem_sdiff.mpr ⟨by simp,h'⟩))
      · rintro ⟨h₁,h₂⟩ v hv
        obtain ⟨hv,hX⟩ := Finset.mem_sdiff.mp hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with he|he
        · subst v; exact (mem_chosen.mp h₁).2.resolve_left hX
        · subst v; exact (mem_chosen.mp h₂).2.resolve_left hX
    simp only [hCond]
  have hfilter : E.filter (fun e => e.1 ∈ B ∧ e.2 ∈ B) = pairs G B := by
    ext e
    rcases e with ⟨u,v⟩
    simp only [Finset.mem_filter,mem_pairs, E]
    have hs : B ⊆ A := fun _ h => (mem_chosen.mp h).1
    constructor
    · exact fun ⟨⟨_,_,hadj⟩,hu,hv⟩ => ⟨hu,hv,hadj⟩
    · exact fun ⟨hu,hv,ha⟩ => ⟨⟨hs hu,hs hv,ha⟩,hu,hv⟩
  unfold edgeCount
  simp_rw [hval]
  rw [arcs_eq_pairs_card,← hfilter]
  have hs := Finset.sum_attach E
    (fun e : V×V => if e.1 ∈ B ∧ e.2 ∈ B then (1:ℝ) else 0)
  rw [Finset.attach_eq_univ] at hs
  rw [hs,← Finset.sum_filter]
  simp

abbrev HalfPalette (p : ℕ) :=
  {J : Finset (Fin (8*p)) // J.card = 4*p}

noncomputable def paletteBound (p : ℕ) : ℕ :=
  256 * (Fintype.card (HalfPalette p) + 1)

theorem balanced_partition {V : Type*} [Fintype V] (G : SimpleGraph V) {c : ℕ}
    (hc : 1 ≤ c) {A : Finset V} (hA : Dense G (8*c) A) :
    ∃ X ⊆ A, X.card ≤ 2*paletteBound (8*c) ∧
      ∃ f : V → Fin (8*(8*c)), ∀ J : HalfPalette (8*c),
        Dense G c (chosen A X f J.val) := by
  classical
  let p := 8*c
  let E := pairs G A
  let S : E → Finset V := fun e => {e.val.1,e.val.2}
  have hS (e : E) : S e ⊆ A := by
    have hmem : e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ G.Adj e.val.1 e.val.2 := mem_pairs.mp e.property
    intro v h
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · exact hmem.1
    · exact hmem.2.1
  have hSC (e : E) : (S e).card ≤ 2 := Finset.card_le_two
  have hE : Fintype.card E = arcs G A := by
    simp [E,arcs_eq_pairs_card]
  have hE' : 0 < Fintype.card E := by
    rw [hE]
    exact (Nat.mul_pos (by omega : 0 < 2*(8*c)) hA.1.card_pos).trans_le hA.2
  let L := paletteBound p
  have hL : 0 < L := by unfold L paletteBound; positivity
  obtain ⟨X,hX,hsize,hOverlap⟩ := extract_exceptional A S hS hSC hE' L hL
  let U (e : E) := S e \ X
  let Z := HalfPalette p
  have hL' : (L:ℝ) = 256 * ((Fintype.card Z : ℝ) + 1) := by simp [L,paletteBound,Z]
  have hO : (Fintype.card Z : ℝ) * overlap U < (Fintype.card E : ℝ)^2/64 := by
    have hpos : 0 < (Fintype.card E : ℝ) := by exact_mod_cast hE'
    have hden : 0 < (L:ℝ) := by exact_mod_cast hL
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hOverlap (by positivity))
    rw [← mul_div_assoc,div_lt_iff₀ hden,hL']
    nlinarith [sq_pos_of_pos hpos,mul_nonneg (show 0 ≤ (Fintype.card Z : ℝ) by positivity)
      (sq_nonneg (Fintype.card E : ℝ))]
  let _ : Nonempty (Fin (8*p)) := ⟨⟨0,by omega⟩⟩
  obtain ⟨f,hf⟩ := color_many U (fun e => (Finset.card_le_card Finset.sdiff_subset).trans (hSC e))
    (fun J : Z => J.val) (fun J => by rw [Fintype.card_fin,J.property]; omega) hO
  refine ⟨X,hX,hsize,f,fun J => ?_⟩
  let B := chosen A X f J.val
  have hp := hf J
  have hEq : edgeCount U J.val f = (arcs G B : ℝ) := edges_inside G A X f J.val
  rw [hEq,hE] at hp
  have hBA : B ⊆ A := fun _ h => (mem_chosen.mp h).1
  have hAB := Finset.card_le_card hBA
  have hArc : 2*c*A.card ≤ arcs G B := by
    have hn : (2:ℝ)*(8*(c:ℝ))*(A.card:ℝ) ≤ (arcs G A : ℝ) := by exact_mod_cast hA.2
    exact_mod_cast (show (2:ℝ)*(c:ℝ)*(A.card:ℝ) ≤ (arcs G B : ℝ) by linarith)
  have hPos : 0 < arcs G B := (Nat.mul_pos (by omega : 0 < 2*c) hA.1.card_pos).trans_le hArc
  refine ⟨?_,(Nat.mul_le_mul_left _ hAB).trans hArc⟩
  by_contra! he
  change B = ∅ at he
  rw [he,arcs,Finset.sum_empty] at hPos
  omega

end NSS1111


namespace NSS1111

open Erdos1111

def Witness {V : Type*} (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∃ (A : Finset V) (B : Set V), Dense G c A ∧ Anticomplete G (A : Set V) B ∧
    (c : ℕ∞) ≤ (G.induce B).chromaticNumber

private theorem map_degree {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (A : Finset V) (v : V) :
    degreeOn H (A.map f.toEmbedding) (f v) = degreeOn G A v := by
  classical
  unfold degreeOn
  rw [Finset.filter_map,Finset.card_map]
  congr 1
  ext x
  simp [f.map_adj_iff]

private theorem witness_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {c : ℕ} (hh : Witness G c) : Witness H c := by
  classical
  obtain ⟨A,B,hA,hab,hχ⟩ := hh
  let A' := A.map f.toEmbedding
  let B' := f '' B
  refine ⟨A',B',?_,?_,?_⟩
  · refine ⟨hA.1.map,?_⟩
    have he : arcs H A' = arcs G A := by
      unfold arcs
      rw [show A' = A.map f.toEmbedding from rfl,Finset.sum_map]
      exact Finset.sum_congr rfl (fun v _ => map_degree f A v)
    rw [he,show A'.card = A.card from Finset.card_map _]
    exact hA.2
  · refine ⟨Set.disjoint_left.mpr ?_,?_⟩
    · intro x hx hy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v,hv,he⟩ := hy
      have he' : v = u := f.injective he
      exact Set.disjoint_left.mp hab.1 hu (he' ▸ hv)
    · intro u hu v hv ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨y,hy,rfl⟩ := hv
      exact hab.2 x hx y hy (f.map_adj_iff.mp ha)
  · let e : G.induce B ↪g H.induce B' := {
      toFun := fun x => ⟨f x.val,⟨x.val,x.property,rfl⟩⟩
      inj' := fun _ _ he => Subtype.ext (f.injective (congrArg Subtype.val he))
      map_rel_iff' := f.map_adj_iff }
    exact hχ.trans (SimpleGraph.chromaticNumber_mono_of_hom e.toHom)

private theorem palette_avoids {V : Type*} (G : SimpleGraph V) {p : ℕ} {A : Finset V}
    (f : V → Fin (8*p)) {v : V} (hd : degreeOn G A v ≤ 4*p) :
    ∃ J : HalfPalette p, ∀ u ∈ A, G.Adj v u → f u ∉ J.val := by
  classical
  let C := (A.filter (G.Adj v)).image f
  have hc : C.card ≤ 4*p := (Finset.card_image_le).trans hd
  let D := Finset.univ \ C
  have hD : 4*p ≤ D.card := by
    unfold D
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C),Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨J,hJ,hcard⟩ := Finset.exists_subset_card_eq hD
  refine ⟨⟨J,hcard⟩,fun u hu ha hj => ?_⟩
  have hM : f u ∈ C := Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,ha⟩,rfl⟩
  exact (Finset.mem_sdiff.mp (hJ hj)).2 hM

private theorem neighbor_clique_free {V : Type*} {G : SimpleGraph V} {t : ℕ} {v : V}
    (h : G.CliqueFree (t+1)) : (G.induce (G.neighborSet v)).CliqueFree t := by
  have hu := (SimpleGraph.cliqueFreeOn_univ G).mpr h
  have hv := SimpleGraph.CliqueFreeOn.of_succ G hu (Set.mem_univ v)
  exact (G.cliqueFree_induce_iff _ _).mpr (by simpa using hv)

private theorem color_cover_rock {V : Type*} [Fintype V] (G : SimpleGraph V)
    {c d' : ℕ} (hc : 1 ≤ c) (hW : ¬ Witness G c) (hL : ∀ v, (G.induce (G.neighborSet v)).Colorable d')
    {A : Finset V} (hA : Rock G (8*c) A) :
    G.Colorable (2*(8*c)+1 + 2*paletteBound (8*c)*d' + Fintype.card (HalfPalette (8*c))*c) := by
  classical
  let p := 8*c
  obtain ⟨X,hXA,hX,f,hf⟩ := balanced_partition G hc hA.1
  let I := HalfPalette p
  let W₀ : Set V := {v | ∃ x ∈ X, G.Adj x v}
  let W (J : I) : Set V :=
    {v | v ∉ A ∧ ∀ u ∈ chosen A X f J.val, ¬ G.Adj u v}
  have hW₀ : (G.induce W₀).Colorable (X.card*d') := by
    have hh := colorable_of_cover G W₀ (fun x : X => G.neighborSet x.val) (fun _ => d')
      (by
        intro v hv
        obtain ⟨x,hx,ha⟩ := hv
        exact ⟨⟨x,hx⟩,ha⟩)
      (fun x => hL x.val)
    simpa using hh
  have hW' (J : I) : (G.induce (W J)).Colorable c := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
    apply le_of_lt
    by_contra! he
    apply hW
    refine ⟨chosen A X f J.val,W J,hf J,⟨Set.disjoint_left.mpr ?_,?_⟩,he⟩
    · intro u hu hw
      exact hw.1 (mem_chosen.mp hu).1
    · exact fun u hu v hv => hv.2 u hu
  let parts : Option (Option I) → Set V
    | none => A
    | some none => W₀
    | some (some i) => W i
  let counts : Option (Option I) → ℕ
    | none => 2*p+1
    | some none => X.card*d'
    | some (some _) => c
  have hC (j : Option (Option I)) : (G.induce (parts j)).Colorable (counts j) := by
    rcases j with _|j
    · exact rock_colorable G (by omega) hA
    rcases j with _|j
    · exact hW₀
    · exact hW' j
  have hp (v : V) : ∃ j, v ∈ parts j := by
    by_cases hv : v ∈ A
    · exact ⟨none,hv⟩
    by_cases hx : v ∈ W₀
    · exact ⟨some none,hx⟩
    have hd := rock_outside_degree G (by omega) hA hv
    obtain ⟨J,hJ⟩ := palette_avoids G f hd
    refine ⟨some (some J),hv,?_⟩
    intro u hu ha
    have hm := mem_chosen.mp hu
    rcases hm.2 with hXu|hfu
    · exact hx ⟨u,hXu,ha⟩
    · exact hJ u hm.1 ha.symm hfu
  have hh := colorable_of_cover G Set.univ parts counts (fun v _ => hp v) hC
  have hg : G.Colorable (∑ j, counts j) :=
    ⟨hh.some.comp (SimpleGraph.induceUnivIso G).symm.toHom⟩
  apply hg.mono
  simp only [Fintype.sum_option,counts,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have hMul := Nat.mul_le_mul_right d' hX
  dsimp [p,I] at *
  omega

theorem dense_witness (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
        (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t → Witness G c := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht0 : t = 0
    · subst t
      refine ⟨1,le_rfl,?_⟩
      intro V _ G hχ hcf
      let _ := SimpleGraph.cliqueFree_one.mp hcf
      let _ : Fintype V := Fintype.ofFinite V
      have hz : Fintype.card V = 0 := Fintype.card_eq_zero
      have hχ0 := G.colorable_of_fintype.chromaticNumber_le
      rw [hz,Nat.cast_zero] at hχ0
      exact (not_le_of_gt (by simp : (0:ℕ∞) < 1) (hχ.trans hχ0)).elim
    obtain ⟨d',hd',IH⟩ := ih (by omega)
    let p := 8*c
    let d := 2*p+1 + 2*paletteBound p*d' + Fintype.card (HalfPalette p)*c+1
    refine ⟨d,by unfold d; omega,?_⟩
    intro V _ G hχ hcf
    classical
    let _ : Fintype V := Fintype.ofFinite V
    by_contra hW
    have hlocal (v : V) : (G.induce (G.neighborSet v)).Colorable d' := by
      apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
      apply le_of_lt
      by_contra! hbad
      exact hW (witness_map (SimpleGraph.Embedding.induce _) (IH _ _ hbad (neighbor_clique_free hcf)))
    have hnot : ¬ (G.induce ((Finset.univ : Finset V) : Set V)).Colorable (2*p) := by
      intro hC
      have hGColor : G.Colorable (2*p) := by
        let e : G →g G.induce ((Finset.univ : Finset V) : Set V) :=
          ⟨fun v => ⟨v,Finset.mem_univ v⟩,fun {_ _} hadj => hadj⟩
        exact ⟨hC.some.comp e⟩
      have hle : d ≤ 2*p := by exact_mod_cast hχ.trans hGColor.chromaticNumber_le
      unfold d at hle
      omega
    have hA : ∃ A, Dense G p A := by
      obtain ⟨A,_,hA⟩ := dense_of_not_colorable G (by omega) hnot
      exact ⟨A,hA⟩
    obtain ⟨A,hA⟩ := exists_rock G p hA
    have hC := color_cover_rock G hc hW hlocal hA
    have hcontra := hχ.trans hC.chromaticNumber_le
    have hle : d ≤ 2*p+1 + 2*paletteBound p*d' + Fintype.card (HalfPalette p)*c := by
      exact_mod_cast hcontra
    unfold d at hle
    omega

theorem degreeOn_eq_ncard {V : Type*} [Finite V] (G : SimpleGraph V) (A : Finset V) (v : V) :
    (↑A ∩ G.neighborSet v : Set V).ncard = degreeOn G A v := by
  classical
  have he : (↑(A.filter (G.Adj v)) : Set V) = (↑A ∩ G.neighborSet v : Set V) := by
    ext x
    simp [SimpleGraph.mem_neighborSet]
  rw [← he,Set.ncard_coe_finset]
  rfl

end NSS1111

theorem OMA.solution : type_of% @Erdos1111.erdos_1111.variants.nguyen_scott_seymour := by
  intro t c ht hc
  obtain ⟨d,hd,h⟩ := NSS1111.dense_witness t c ht hc
  refine ⟨d,hd,fun V _ G hχ hcf => ?_⟩
  obtain ⟨A,B,hD,hA,hB⟩ := h V G hχ hcf
  obtain ⟨A',hsub,hne,hmin⟩ := NSS1111.core_of_dense hc hD
  refine ⟨A',B,⟨hA.1.mono_left (by exact_mod_cast hsub),?_⟩,?_,?_,hB⟩
  · exact fun a ha b hb => hA.2 a (hsub ha) b hb
  · exact hne
  · intro v hv
    rw [NSS1111.degreeOn_eq_ncard]
    exact hmin v hv