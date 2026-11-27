import OMAReductions.R_Erdos85_erdos_85_R1
import Mathlib

/-!
# The possible orders missed by interpolation in Erdős problem 85

A four-cycle-free graph of minimum degree d has at least d(d-1)+1 vertices.
Attainable orders at a fixed minimum degree are closed under addition.
Over a prime field the affine polarity graph has edges defined by
x₂ + y₂ = x₁y₁. Keep d+1 full first-coordinate classes, then add any
remaining vertices up to the full square. Every vertex has at least d
neighbors, so this gives every order from (d+1)p through p².

Together these lemmas reduce the plateau step to indecomposable orders.
Below or at (d+1)² only a window of width 3d remains. Above (d+1)²
an obstruction must lie below (d+1)p for every prime p greater than d+1.

The unique-common-neighbor lemma is from the parent reduction, PR 97.
For the affine polarity construction see Verstraëte, Extremal Problems for
Cycles in Graphs, section 4.2. The full-column argument handles intermediate orders.
-/
namespace OMA.R_Erdos85_erdos_85_R1_H1_R1
open SimpleGraph Finset OMA.R_Erdos85_erdos_85_R1
open scoped Classical

def H1 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ,
    (∃ j < n, d < Erdos85.f j) →
    (∀ j ≤ n+d+2, Erdos85.f j ≤ d+1) →
    (∀ i j, i+j=n → Erdos85.f i ≤ d ∨ Erdos85.f j ≤ d) →
    d*(d-1)+2 ≤ n → n ≤ (d+1)^2 → d < Erdos85.f n

def H2 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ,
    (∃ j < n, d < Erdos85.f j) →
    (∀ j ≤ n+d+2, Erdos85.f j ≤ d+1) →
    (∀ i j, i+j=n → Erdos85.f i ≤ d ∨ Erdos85.f j ≤ d) →
    (d+1)^2 < n →
    (∀ p, Nat.Prime p → d+1 < p → n < (d+1)*p) → d < Erdos85.f n

lemma unique_common {V : Type*} (G : SimpleGraph V) (hG : ¬ cycleGraph 4 ⊑ G)
    {v x a b : V} (hvx : v ≠ x) (hva : G.Adj v a) (hxa : G.Adj x a)
    (hvb : G.Adj v b) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  let p : Fin 4 → V := ![v, a, x, b]
  have hpair : ∀ i j : Fin 4, p i = p j → i = j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, hvx, hvx.symm, hab, Ne.symm hab,
      hva.ne, hva.ne.symm, hxa.ne, hxa.ne.symm, hvb.ne, hvb.ne.symm, hxb.ne, hxb.ne.symm]
  apply hG
  refine ⟨⟨⟨p, ?_⟩, fun {i j} => hpair i j⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact hva | exact hva.symm | exact hxa | exact hxa.symm
    | exact hvb | exact hvb.symm | exact hxb | exact hxb.symm
    | exact False.elim ((by decide : ¬ _) hij)

theorem moore {j d : ℕ} (hj : 0 < j) (hd : d < Erdos85.f j) : d*(d-1)+1 ≤ j := by
  classical
  obtain ⟨G,hG,hmin⟩ := lt_threshold_iff.mp hd
  let v : Fin j := ⟨0,hj⟩
  let T := G.neighborFinset v
  let U (a : Fin j) := (G.neighborFinset a).erase v
  have du : (T : Set (Fin j)).PairwiseDisjoint U := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    exact hab (unique_common G hG (ne_of_mem_erase hxa).symm
      ((G.mem_neighborFinset ..).mp ha) ((G.mem_neighborFinset ..).mp (mem_of_mem_erase hxa)).symm
      ((G.mem_neighborFinset ..).mp hb) ((G.mem_neighborFinset ..).mp (mem_of_mem_erase hxb)).symm)
  have hu : T.biUnion U ⊆ univ.erase v := by
    intro x hx
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hx
    exact mem_erase.mpr ⟨ne_of_mem_erase ha,mem_univ _⟩
  have cardU (a) (ha : a ∈ T) : d-1 ≤ (U a).card := by
    have hv : v ∈ G.neighborFinset a := (G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp ha).symm
    have h := hmin.trans (G.minDegree_le_degree a)
    simpa only [U,card_erase_of_mem hv, G.card_neighborFinset_eq_degree] using Nat.sub_le_sub_right h 1
  have hv := hmin.trans (G.minDegree_le_degree v)
  have hv' : d ≤ T.card := by simpa [T] using hv
  have sum : d*(d-1) ≤ (univ.erase v).card := calc
    _ ≤ T.card*(d-1) := Nat.mul_le_mul_right _ hv'
    _ = ∑ _a ∈ T, (d-1) := by simp
    _ ≤ ∑ a ∈ T, (U a).card := sum_le_sum cardU
    _ = (T.biUnion U).card := (card_biUnion du).symm
    _ ≤ _ := card_le_card hu
  simp only [card_erase_of_mem (mem_univ v),card_univ,Fintype.card_fin] at sum
  omega






lemma avoid_of_common {V : Type*} (G : SimpleGraph V)
    (hu : ∀ {x y a b}, x ≠ y → G.Adj x a → G.Adj y a → G.Adj x b → G.Adj y b → a = b) :
    ¬ cycleGraph 4 ⊑ G := by
  rintro ⟨c⟩
  have edge (i j : Fin 4) (h : (cycleGraph 4).Adj i j) := c.toHom.map_rel' h
  have h := hu (x := c.toHom 0) (y := c.toHom 2) (a := c.toHom 1) (b := c.toHom 3)
    (fun h => (by decide : (0 : Fin 4) ≠ 2) (c.injective h))
    (edge 0 1 (by decide)) (edge 2 1 (by decide)) (edge 0 3 (by decide)) (edge 2 3 (by decide))
  exact (by decide : (1 : Fin 4) ≠ 3) (c.injective h)

lemma avoid_sum {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B)
    (hg : ¬ cycleGraph 4 ⊑ G) (hh : ¬ cycleGraph 4 ⊑ H) : ¬ cycleGraph 4 ⊑ G.sum H := by
  apply avoid_of_common
  rintro (x|x) (y|y) (a|a) (b|b) hxy h1 h2 h3 h4 <;> simp_all [SimpleGraph.sum]
  · exact unique_common G (fun ⟨c⟩ => hg.false c) hxy h1 h2 h3 h4
  · exact unique_common H (fun ⟨c⟩ => hh.false c) hxy h1 h2 h3 h4

lemma degree_embed {A B : Type*} {G : SimpleGraph A}
    {H : SimpleGraph B} (e : G ↪g H) (v : A) [Fintype (G.neighborSet v)] [Fintype (H.neighborSet (e v))] : G.degree v ≤ H.degree (e v) := by
  let f (w : G.neighborSet v) : H.neighborSet (e v) := ⟨e w,e.map_adj_iff.mpr w.property⟩
  have inj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj

theorem add_orders {i j d : ℕ} (hi : d < Erdos85.f i) (hj : d < Erdos85.f j) :
    d < Erdos85.f (i+j) := by
  classical
  by_cases hz : i+j=0
  · have : j=0 := by omega
    simpa [this] using hi
  let _ : NeZero (i+j) := ⟨hz⟩
  obtain ⟨G,hg,h1⟩ := lt_threshold_iff.mp hi
  obtain ⟨H,hh,h2⟩ := lt_threshold_iff.mp hj
  let e : Fin (i+j) ≃ Fin i ⊕ Fin j := finSumFinEquiv.symm
  let K := (G.sum H).comap e
  let iso : K ≃g G.sum H := Iso.comap e _
  apply lt_threshold_iff.mpr
  refine ⟨K,fun hc => avoid_sum G H hg hh (hc.trans ⟨iso.toCopy⟩),?_⟩
  apply K.le_minDegree_of_forall_le_degree
  intro v
  rw [← iso.degree_eq v]
  cases he : iso v with
  | inl a => exact h1.trans ((G.minDegree_le_degree a).trans (degree_embed (Embedding.sumInl : G ↪g G.sum H) a))
  | inr b => exact h2.trans ((H.minDegree_le_degree b).trans (degree_embed (Embedding.sumInr : H ↪g G.sum H) b))



lemma affine_common {K : Type*} [Field K] {x y a b : K × K} (hxy : x ≠ y)
    (g1 : x.2+a.2=x.1*a.1) (g2 : y.2+a.2=y.1*a.1)
    (g3 : x.2+b.2=x.1*b.1) (g4 : y.2+b.2=y.1*b.1) : a = b := by
  have h : (x.1-y.1)*(a.1-b.1) = 0 := by linear_combination -g1+g2+g3-g4
  rcases mul_eq_zero.mp h with hx|ha
  · have he := sub_eq_zero.mp hx
    exfalso
    apply hxy (Prod.ext he ?_)
    rw [he] at g1
    linear_combination g1-g2
  · have he := sub_eq_zero.mp ha
    apply Prod.ext he
    rw [he] at g1
    linear_combination g1-g3

theorem strip {p n d : ℕ} (hp : Nat.Prime p) (hlo : (d+1)*p ≤ n) (hhi : n ≤ p*p) :
    d < Erdos85.f n := by
  classical
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let G : SimpleGraph (ZMod p × ZMod p) := {
    Adj := fun x y => x ≠ y ∧ x.2+y.2=x.1*y.1
    symm := ⟨fun {x y} h => ⟨h.1.symm, by simpa [add_comm,mul_comm] using h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have free : ¬ cycleGraph 4 ⊑ G := avoid_of_common G
    (fun h h1 h2 h3 h4 => affine_common h h1.2 h2.2 h3.2 h4.2)
  have hp0 := hp.pos
  have hdp : d+1 ≤ p := Nat.le_of_mul_le_mul_right (hlo.trans hhi) hp0
  obtain ⟨C,_,hc⟩ := exists_subset_card_eq (s := (univ : Finset (ZMod p)))
    (by simpa using hdp : d+1 ≤ univ.card)
  let B := C ×ˢ (univ : Finset (ZMod p))
  obtain ⟨S,hBS,_,hS⟩ := exists_subsuperset_card_eq (subset_univ B)
    (by simpa [B,hc] using hlo : B.card ≤ n) (by simpa using hhi)
  let e : Fin n ≃ S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let embed : Fin n ↪ ZMod p × ZMod p := e.toEmbedding.trans (Function.Embedding.subtype _)
  let H := G.comap embed
  let _ : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  let hom : H ↪g G := SimpleGraph.Embedding.comap embed _
  apply lt_threshold_iff.mpr
  refine ⟨H,fun h => free (h.trans ⟨hom.toCopy⟩),?_⟩
  have hn : 0 < n := (Nat.mul_pos (by omega) hp0).trans_le hlo
  let _ : NeZero n := ⟨hn.ne'⟩
  apply H.le_minDegree_of_forall_le_degree
  intro v
  let x := embed v
  let T := C.erase x.1
  let neighbor (t : T) : H.neighborSet v := by
    let y : ZMod p × ZMod p := (t.val, x.1*t.val-x.2)
    have hyt : y ∈ S := hBS (mem_product.mpr ⟨mem_of_mem_erase t.property,mem_univ _⟩)
    refine ⟨e.symm ⟨y,hyt⟩,?_⟩
    change G.Adj x (e (e.symm ⟨y,hyt⟩)).val
    rw [e.apply_symm_apply]
    exact ⟨fun h => ne_of_mem_erase t.property (congrArg Prod.fst h).symm, by dsimp [y]; ring⟩
  have inject : Function.Injective neighbor := by
    intro a b he
    apply Subtype.ext
    simpa [neighbor] using congrArg (fun z : H.neighborSet v => (e z.val).val.1) he
  calc
    d ≤ T.card := by
      by_cases hx : x.1 ∈ C
      · simp [T,card_erase_of_mem hx,hc]
      · simp [T,erase_eq_of_notMem hx,hc]
    _ = Fintype.card T := (Fintype.card_coe T).symm
    _ ≤ Fintype.card (H.neighborSet v) := Fintype.card_le_of_injective neighbor inject
    _ = H.degree v := H.card_neighborSet_eq_degree v


theorem main : H1 → H2 → OMA.R_Erdos85_erdos_85_R1.H1 := by
  rintro ⟨N,hnear⟩ ⟨M,hfar⟩
  refine ⟨max 2 (max N M),?_⟩
  intro n hn d earlier flat
  apply lt_threshold_iff.mp
  by_contra! miss
  have nodouble : ∀ i j, i+j=n → Erdos85.f i ≤ d ∨ Erdos85.f j ≤ d := by
    intro i j he
    by_contra! h
    exact (not_lt_of_ge miss) (he ▸ add_orders h.1 h.2)
  have minN : d*(d-1)+2 ≤ n := by
    obtain ⟨j,hj,hd⟩ := earlier
    by_cases hz : j=0
    · subst j
      obtain ⟨G,_,hg⟩ := lt_threshold_iff.mp hd
      simp at hg
      subst d
      simp_all
    · have := moore (Nat.pos_of_ne_zero hz) hd
      omega
  by_cases small : n ≤ (d+1)^2
  · exact (not_lt_of_ge miss) (hnear n (by omega) d earlier flat nodouble minN small)
  have window : ∀ p, Nat.Prime p → d+1 < p → n < (d+1)*p := by
    intro p hp h
    by_contra! lo
    have high : n ≤ p*p := by
      by_contra! hh
      have hf := strip (d := d+1) hp (Nat.mul_le_mul_right p h) (le_refl (p*p))
      have := flat (p*p) (by omega)
      omega
    exact (not_lt_of_ge miss) (strip hp lo high)
  exact (not_lt_of_ge miss) (hfar n (by omega) d earlier flat nodouble (by omega) window)

end OMA.R_Erdos85_erdos_85_R1_H1_R1
