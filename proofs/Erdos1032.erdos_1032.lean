import FormalConjectures.ErdosProblems.«1032»

/-!
# A sparse obstruction to three-colorability

We formalize EthanYang's sparse-obstruction argument for Erdős Problem 1032.
At each branch a color assignment removes many choices from the remaining vertex lists.
The two-choice subsystem has a small contradiction certificate supported on implication paths.
With linear minimum degree this process uses a bounded number of branches, so the union of the
certificates contains only linearly many edges. Edge-criticality forces that union to contain
every edge, which contradicts the degree sum.

The original disproof was verified at
https://conjectures.io/results/e76a593e-d1f7-4946-b724-a86f2b8ec5f8.
-/

namespace OMA.Erdos1032

open Relation

section Implication

variable {L : Type*} {neg : L → L} (inv : Function.Involutive neg)
variable {R : L → L → Prop}
variable (contra : ∀ {a b}, R a b → R (neg b) (neg a))

include contra in
private theorem reach_contra {a b : L} (h : ReflTransGen R a b) :
    ReflTransGen R (neg b) (neg a) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.head (contra h)

private def Consistent (neg : L → L) (S : Set L) : Prop :=
  ∀ ⦃a⦄, a ∈ S → neg a ∉ S

private def Closed (R : L → L → Prop) (S : Set L) : Prop :=
  ∀ ⦃a b⦄, a ∈ S → ReflTransGen R a b → b ∈ S

include inv contra in
private theorem add_reach {S : Set L} (hS : Consistent neg S) (hc : Closed R S)
    {a : L} (ha : neg a ∉ S) (har : ¬ ReflTransGen R a (neg a)) :
    Consistent neg (S ∪ {b | ReflTransGen R a b}) ∧
      Closed R (S ∪ {b | ReflTransGen R a b}) := by
  constructor
  · intro b hb hnb
    rcases hb with hb | hb <;> rcases hnb with hnb | hnb
    · exact hS hb hnb
    · exact ha (hc hb (by simpa only [inv b] using reach_contra contra hnb))
    · exact ha (hc hnb (reach_contra contra hb))
    · apply har
      exact (show ReflTransGen R a (neg b) from hnb).trans
        (reach_contra contra hb)
  · intro b c hb hbc
    rcases hb with hb | hb
    · exact Or.inl (hc hb hbc)
    · exact Or.inr ((show ReflTransGen R a b from hb).trans hbc)

include inv contra in
private theorem complement_assignment
    (noCycle : ∀ a, ¬ (ReflTransGen R a (neg a) ∧ ReflTransGen R (neg a) a))
    (S : Set L) (hS : Consistent neg S) (hc : Closed R S) :
    ∃ T : Set L, S ⊆ T ∧ Consistent neg T ∧ Closed R T ∧ ∀ a, a ∈ T ∨ neg a ∈ T := by
  let P : Set (Set L) := {T | S ⊆ T ∧ Consistent neg T ∧ Closed R T}
  have hP : S ∈ P := ⟨Set.Subset.rfl, hS, hc⟩
  have hup (chain : Set (Set L)) (hchain : chain ⊆ P) (horder : IsChain (· ⊆ ·) chain) :
      ∃ ub ∈ P, ∀ T ∈ chain, T ⊆ ub := by
    by_cases hn : chain.Nonempty
    · obtain ⟨U, hU⟩ := hn
      refine ⟨⋃₀ chain, ⟨?_, ?_, ?_⟩, fun T hT => Set.subset_sUnion_of_mem hT⟩
      · exact (hchain hU).1.trans (Set.subset_sUnion_of_mem hU)
      · intro a ha hna
        obtain ⟨T, hT, hat⟩ := Set.mem_sUnion.mp ha
        obtain ⟨W, hW, haw⟩ := Set.mem_sUnion.mp hna
        rcases horder.total hT hW with hle | hle
        · exact (hchain hW).2.1 (hle hat) haw
        · exact (hchain hT).2.1 hat (hle haw)
      · intro a b ha hr
        obtain ⟨T, hT, hat⟩ := Set.mem_sUnion.mp ha
        exact Set.mem_sUnion.mpr ⟨T, hT, (hchain hT).2.2 hat hr⟩
    · exact ⟨S, hP, fun T hT => (hn ⟨T, hT⟩).elim⟩
  obtain ⟨T, hT, hmax⟩ := zorn_subset P hup
  refine ⟨T, hT.1, hT.2.1, hT.2.2, ?_⟩
  intro a
  by_contra! hm
  have impossible (b : L) (hb : b ∉ T) (hnb : neg b ∉ T)
      (hr : ¬ ReflTransGen R b (neg b)) : False := by
    have hu := add_reach inv contra hT.2.1 hT.2.2 hnb hr
    have hnew : T ∪ {z | ReflTransGen R b z} ∈ P :=
      ⟨hT.1.trans Set.subset_union_left, hu.1, hu.2⟩
    exact hb (hmax hnew Set.subset_union_left (Or.inr .refl))
  apply noCycle a
  exact ⟨by_contradiction fun h => impossible a hm.1 hm.2 h,
    by_contradiction fun h => impossible (neg a) hm.2 (by simpa only [inv a] using hm.1) (by simpa only [inv a] using h)⟩

include inv contra in
private theorem implication_obstruction {U : Set L}
    (hn : ¬ ∃ T : Set L, U ⊆ T ∧ Consistent neg T ∧ Closed R T ∧
      ∀ a, a ∈ T ∨ neg a ∈ T) :
    (∃ a, ReflTransGen R a (neg a) ∧ ReflTransGen R (neg a) a) ∨
      ∃ a ∈ U, ∃ b ∈ U, ReflTransGen R a (neg b) := by
  classical
  by_contra! hb
  let S : Set L := {b | ∃ a ∈ U, ReflTransGen R a b}
  have hUS : U ⊆ S := fun a ha => ⟨a, ha, .refl⟩
  have hS : Consistent neg S := by
    rintro b ⟨a, ha, hab⟩ ⟨c, hc, hcb⟩
    exact hb.2 c hc a ha (hcb.trans (reach_contra contra hab))
  have hc : Closed R S := by
    rintro a b ⟨c, hc, hca⟩ hab
    exact ⟨c, hc, hca.trans hab⟩
  obtain ⟨T, hST, hT, hTc, htot⟩ := complement_assignment inv contra
    (fun a ha => hb.1 a ha.1 ha.2) S hS hc
  exact hn ⟨T, hUS.trans hST, hT, hTc, htot⟩

end Implication

section Support

variable {L E : Type*} [Fintype L] [DecidableEq E]
variable (step : E → L → L → Prop)

private def EdgeReach (A : Finset E) (a b : L) : Prop :=
  ReflTransGen (fun x y => ∃ e ∈ A, step e x y) a b

private theorem reach_mono {A B : Finset E} (h : A ⊆ B) {a b : L}
    (hab : EdgeReach step A a b) : EdgeReach step B a b := by
  have hstep : (fun x y : L => ∃ e ∈ A, step e x y) ≤
      (fun x y : L => ∃ e ∈ B, step e x y) :=
    fun _ _ ⟨e, he, hr⟩ => ⟨e, h he, hr⟩
  exact ReflTransGen.mono hstep a b hab

private theorem small_support {A : Finset E} {a b : L} (h : EdgeReach step A a b) :
    ∃ B ⊆ A, B.card ≤ Fintype.card L ∧ EdgeReach step B a b := by
  classical
  let reachable (B : Finset E) : Finset L :=
    Finset.univ.filter fun v => EdgeReach step B a v
  have mem_reachable (B : Finset E) (v : L) : v ∈ reachable B ↔ EdgeReach step B a v := by
    simp [reachable]
  have enough (B : Finset E) (hBA : B ⊆ A)
      (hsize : B.card < (reachable B).card) :
      ∃ C ⊆ A, C.card ≤ Fintype.card L ∧ EdgeReach step C a b := by
    generalize hm : Fintype.card L - (reachable B).card = m
    induction m using Nat.strong_induction_on generalizing B with
    | h m ih =>
      by_cases hb : EdgeReach step B a b
      · exact ⟨B, hBA, hsize.le.trans (Finset.card_le_univ _), hb⟩
      · have frontier {v : L} (hv : EdgeReach step A a v) (hnv : ¬ EdgeReach step B a v) :
            ∃ x y, EdgeReach step B a x ∧ ¬ EdgeReach step B a y ∧
              ∃ e ∈ A, step e x y := by
          induction hv with
          | refl => exact (hnv .refl).elim
          | @tail x y hv hxy ih =>
            by_cases hx : EdgeReach step B a x
            · exact ⟨x, y, hx, hnv, hxy⟩
            · exact ih hx
        obtain ⟨x, y, hx, hy, e, he, hxy⟩ := frontier h hb
        let C := insert e B
        have hinc : B ⊆ C := Finset.subset_insert _ _
        have hsubset : reachable B ⊆ reachable C := by
          intro v hv
          exact (mem_reachable C v).2 (reach_mono step hinc ((mem_reachable B v).1 hv))
        have hyC : y ∈ reachable C := (mem_reachable C y).2 <|
          (reach_mono step hinc hx).tail ⟨e, Finset.mem_insert_self _ _, hxy⟩
        have hcard : (reachable B).card < (reachable C).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hsubset, fun heq => hy ((mem_reachable B y).1 (heq ▸ hyC))⟩)
        have hbound : (reachable C).card ≤ Fintype.card L := Finset.card_le_univ _
        have hstep : Fintype.card L - (reachable C).card < m := by omega
        have hC : C ⊆ A := Finset.insert_subset_iff.mpr ⟨he, hBA⟩
        have hCsize : C.card < (reachable C).card := by
          have hcard' : C.card ≤ B.card + 1 := Finset.card_insert_le _ _
          omega
        exact ih _ hstep C hC hCsize rfl
  exact enough ∅ (Finset.empty_subset A)
    (by simpa using Finset.card_pos.mpr ⟨a, (mem_reachable ∅ a).2 .refl⟩)

end Support

section Binary

variable {W E : Type*} [Fintype W] [DecidableEq E]

private def opposite (l : W × Bool) : W × Bool := (l.1, !l.2)

private theorem opposite_opposite (l : W × Bool) : opposite (opposite l) = l := by
  cases l with
  | mk w b => cases b <;> rfl

private def TrueLiteral (f : W → Bool) (l : W × Bool) : Prop := f l.1 = l.2

private theorem true_opposite (f : W → Bool) (l : W × Bool) :
    TrueLiteral f (opposite l) ↔ ¬ TrueLiteral f l := by
  rcases l with ⟨w,b⟩
  unfold TrueLiteral opposite
  cases b <;> cases f w <;> simp

private theorem assignment_of_set {S : Set (W × Bool)}
    (hc : Consistent opposite S) (ht : ∀ a, a ∈ S ∨ opposite a ∈ S) :
    ∃ f : W → Bool, ∀ a, TrueLiteral f a ↔ a ∈ S := by
  classical
  let f (v : W) : Bool := if (v,true) ∈ S then true else false
  refine ⟨f, ?_⟩
  rintro ⟨v, b⟩
  by_cases h : (v,true) ∈ S
  · have hf : (v,false) ∉ S := hc h
    cases b <;> simp [TrueLiteral, f, h, hf]
  · have hf : (v,false) ∈ S := (ht (v,true)).resolve_left h
    cases b <;> simp [TrueLiteral, f, h, hf]

variable (step : E → (W × Bool) → (W × Bool) → Prop)

private def Respects (A : Finset E) (f : W → Bool) : Prop :=
  ∀ e ∈ A, ∀ a b, step e a b → TrueLiteral f a → TrueLiteral f b

private theorem respects_reach {A : Finset E} {f : W → Bool} (hf : Respects step A f)
    {a b : W × Bool} (h : EdgeReach step A a b) (ha : TrueLiteral f a) : TrueLiteral f b := by
  induction h with
  | refl => exact ha
  | tail _ hab ih =>
      obtain ⟨e, he, hstep⟩ := hab
      exact hf e he _ _ hstep ih

private theorem binary_obstruction {A : Finset E} {U : Set (W × Bool)}
    (contra : ∀ e a b, step e a b → step e (opposite b) (opposite a))
    (hno : ¬ ∃ f, Respects step A f ∧ ∀ a ∈ U, TrueLiteral f a) :
    (∃ B ⊆ A, B.card ≤ 4 * Fintype.card W ∧ ¬ ∃ f, Respects step B f) ∨
      ∃ a ∈ U, ∃ b ∈ U, ∃ B ⊆ A, B.card ≤ 2 * Fintype.card W ∧
        ∀ f, Respects step B f → TrueLiteral f a → ¬ TrueLiteral f b := by
  classical
  let R (a b : W × Bool) := ∃ e ∈ A, step e a b
  have reversal {a b : W × Bool} (h : R a b) : R (opposite b) (opposite a) := by
    obtain ⟨e, he, hstep⟩ := h
    exact ⟨e, he, contra e a b hstep⟩
  have obstruction := implication_obstruction (R := R) opposite_opposite (@reversal)
    (U := U) (by
      rintro ⟨T, hUT, hc, hclosed, htotal⟩
      obtain ⟨f, hf⟩ := assignment_of_set hc htotal
      apply hno
      exact ⟨f, fun e he a b hstep htrue =>
        (hf b).2 (hclosed ((hf a).1 htrue) (.single ⟨e, he, hstep⟩)),
        fun a ha => (hf a).2 (hUT ha)⟩)
  rcases obstruction with ⟨a, ha, hb⟩ | ⟨a, ha, b, hb, hab⟩
  · obtain ⟨X, hXA, hX, hx⟩ := small_support step ha
    obtain ⟨Y, hYA, hY, hy⟩ := small_support step hb
    refine Or.inl ⟨X ∪ Y, Finset.union_subset hXA hYA, ?_, ?_⟩
    · have hu := Finset.card_union_le X Y
      simp only [Fintype.card_prod, Fintype.card_bool] at hX hY
      omega
    · rintro ⟨f, hf⟩
      have hx' := respects_reach step hf (reach_mono step Finset.subset_union_left hx)
      have hy' := respects_reach step hf (reach_mono step Finset.subset_union_right hy)
      by_cases h : TrueLiteral f a
      · exact ((true_opposite f a).1 (hx' h)) h
      · exact h (hy' ((true_opposite f a).2 h))
  · obtain ⟨B, hBA, hcard, hB⟩ := small_support step hab
    refine Or.inr ⟨a, ha, b, hb, B, hBA, ?_, fun f hf hfa => ?_⟩
    · simpa [mul_comm] using hcard
    · exact (true_opposite f b).1 (respects_reach step hf hB hfa)

end Binary

section Coloring

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev Color := Fin 3
private abbrev Lists (V : Type*) := V → Finset Color

private def Fits (A : Lists V) (f : V → Color) : Prop :=
  ∀ v, f v ∈ A v

private def ProperOn (S : Finset (Sym2 V)) (f : V → Color) : Prop :=
  ∀ u v, s(u, v) ∈ S → f u ≠ f v

private theorem proper_subset {S T : Finset (Sym2 V)} {f : V → Color}
    (hST : S ⊆ T) (h : ProperOn T f) : ProperOn S f :=
  fun u v huv => h u v (hST huv)

private def mass (A : Lists V) : ℕ := ∑ v, (A v).card

private theorem mass_mono {A B : Lists V} (h : ∀ v, A v ⊆ B v) :
    mass A ≤ mass B :=
  Finset.sum_le_sum fun v _ => Finset.card_le_card (h v)

private theorem mass_account {A B : Lists V} (h : ∀ v, A v ⊆ B v)
    (S : Finset V) (hs : ∀ v ∈ S, (A v).card < (B v).card) :
    mass A + S.card ≤ mass B := by
  classical
  unfold mass
  calc
    (∑ v, (A v).card) + S.card =
        ∑ v, ((A v).card + if v ∈ S then 1 else 0) := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ ∑ v, (B v).card := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs with hv
      · exact hs v hv
      · simpa using Finset.card_le_card (h v)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Unit propagation. If a vertex already has a unique color, each neighbor must avoid it. -/
private def Stable (A : Lists V) : Prop :=
  ∀ u v c, G.Adj u v → A u = {c} → c ∉ A v

private theorem propagate (A : Lists V) :
    ∃ (B : Lists V) (S : Finset (Sym2 V)),
      (∀ v, B v ⊆ A v) ∧ S ⊆ G.edgeFinset ∧ S.card + mass B ≤ mass A ∧
      (∀ f, ProperOn S f → Fits A f → Fits B f) ∧ Stable G B := by
  classical
  generalize hmass : mass A = m
  induction m using Nat.strong_induction_on generalizing A with
  | h m ih =>
    by_cases hstable : Stable G A
    · exact ⟨A, ∅, fun _ => Finset.Subset.refl _, Finset.empty_subset _,
        by simp [hmass], fun _ _ h => h, hstable⟩
    · unfold Stable at hstable
      push Not at hstable
      obtain ⟨u, v, c, hadj, hau, hav⟩ := hstable
      let C := Function.update A v ((A v).erase c)
      have hC v' : C v' ⊆ A v' := by
        by_cases he : v' = v
        · subst v'
          simpa [C] using Finset.erase_subset c (A v)
        · simp [C, Function.update_of_ne he]
      have hcard : (C v).card < (A v).card := by
        simpa [C, Finset.card_erase_lt_of_mem hav]
      have hlt := mass_account hC {v} (by simpa using hcard)
      have hlt' : mass C < m := by
        simp only [Finset.card_singleton] at hlt
        omega
      obtain ⟨B, S, hB, hS, hcost, hforce, hBs⟩ := ih _ hlt' C rfl
      let T := insert s(u, v) S
      have hTe : T ⊆ G.edgeFinset :=
        Finset.insert_subset_iff.mpr ⟨by simpa using hadj, hS⟩
      have hTc : T.card + mass B ≤ m := by
        have hh : T.card ≤ S.card + 1 := Finset.card_insert_le _ _
        simp only [Finset.card_singleton] at hlt
        omega
      refine ⟨B, T, fun v' => (hB v').trans (hC v'), hTe, hTc, ?_, hBs⟩
      intro f hf hfits
      apply hforce f (proper_subset (Finset.subset_insert _ _) hf)
      intro v'
      by_cases e : v' = v
      · subst v'
        have hu : f u = c := Finset.mem_singleton.mp (hau ▸ hfits u)
        have hv : f v ≠ c := by
          rw [← hu]
          exact Ne.symm (hf u v (Finset.mem_insert_self _ _))
        simpa [C, Finset.mem_erase, hv] using hfits v
      · simpa [C, Function.update_of_ne e] using hfits v'

private def Cases (G : SimpleGraph V) [DecidableRel G.Adj] (A : Lists V)
    (d : ℕ) (S : Finset (Sym2 V)) (P : Fin 9 → Option (Lists V)) : Prop :=
  S ⊆ G.edgeFinset ∧ S.card ≤ 10 * Fintype.card V ∧
  (∀ i B, P i = some B → mass B + d ≤ mass A) ∧
  ∀ f, Fits A f → ProperOn S f → ∃ i B, P i = some B ∧ Fits B f

private theorem sparse_from_cases (d : ℕ) (hd : 0 < d)
    (hlocal : ∀ A : Lists V, ∃ S P, Cases G A d S P) :
    ∀ (k : ℕ) (A : Lists V), mass A < (k + 1) * d →
      ∃ S ⊆ G.edgeFinset, S.card ≤ (10 ^ (k + 1)) * Fintype.card V ∧
        ¬ ∃ f, Fits A f ∧ ProperOn S f := by
  classical
  intro k
  induction k with
  | zero =>
      intro A hA
      obtain ⟨S,P,hS,hcard,hdrop,hcases⟩ := hlocal A
      refine ⟨S,hS,?_,?_⟩
      · simpa using hcard
      · rintro ⟨f,hf,hproper⟩
        obtain ⟨i,B,hP,_⟩ := hcases f hf hproper
        have ht := hdrop i B hP
        simp only [zero_add, one_mul] at hA
        omega
  | succ k ih =>
      intro A hA
      obtain ⟨S,P,hS,hcard,hdrop,hcases⟩ := hlocal A
      have branch : ∀ i : Fin 9, ∃ T ⊆ G.edgeFinset,
          T.card ≤ 10 ^ (k + 1) * Fintype.card V ∧
          ∀ B, P i = some B → ¬ ∃ f, Fits B f ∧ ProperOn T f := by
        intro i
        cases hP : P i with
        | none => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
        | some B =>
            have hb : mass B < (k + 1) * d := by
              have h := hdrop i B hP
              rw [Nat.add_mul, one_mul] at hA
              omega
            obtain ⟨T,hT,hcard,hno⟩ := ih B hb
            exact ⟨T,hT,hcard,fun C hEq => (Option.some.inj hEq) ▸ hno⟩
      choose T hT hcardT hno using branch
      let U : Finset (Sym2 V) := Finset.univ.biUnion T
      have hU : U ⊆ G.edgeFinset := by
        intro e he
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
        exact hT i hi
      refine ⟨S ∪ U, Finset.union_subset hS hU, ?_, ?_⟩
      · have hu : U.card ≤ ∑ i, (T i).card := Finset.card_biUnion_le
        have hs : ∑ i, (T i).card ≤ 9 * (10 ^ (k + 1) * Fintype.card V) := by
          simpa using (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 9))) => hcardT i)
        have hsub : 10 * Fintype.card V ≤ 10 ^ (k + 1) * Fintype.card V := by
          apply Nat.mul_le_mul_right
          simpa using Nat.pow_le_pow_right (by decide : 0 < (10 : ℕ)) (show 1 ≤ k + 1 by omega)
        rw [pow_succ]
        calc
          (S ∪ U).card ≤ S.card + U.card := Finset.card_union_le _ _
          _ ≤ (10 ^ (k + 1) * Fintype.card V) +
              9 * (10 ^ (k + 1) * Fintype.card V) := by omega
          _ = 10 ^ (k + 1) * 10 * Fintype.card V := by ring
      · rintro ⟨f,hf,hproper⟩
        obtain ⟨i,B,hP,hfit⟩ := hcases f hf (proper_subset Finset.subset_union_left hproper)
        apply hno i B hP
        refine ⟨f,hfit,proper_subset (T := S ∪ U) ?_ hproper⟩
        intro e he
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩)

private def incident (a : V) : Finset (Sym2 V) :=
  (G.neighborFinset a).image fun w => s(a, w)

private theorem incident_mem {a w : V} (h : G.Adj a w) : s(a,w) ∈ incident G a :=
  Finset.mem_image.mpr ⟨w, by simpa using h, rfl⟩

private theorem incident_subset (a : V) : incident G a ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
  simpa using hw

private theorem incident_card (a : V) : (incident G a).card ≤ Fintype.card V :=
  (Finset.card_image_le).trans (Finset.card_le_univ _)

private def trim (A : Lists V) (a : V) (c : Color) (v : V) : Finset Color :=
  if v = a then (A v).filter (· = c)
  else if G.Adj a v then (A v).erase c else A v

private theorem trim_subset (A : Lists V) (a : V) (c : Color) (v : V) :
    trim G A a c v ⊆ A v := by
  unfold trim
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

private theorem trim_mono {A B : Lists V} (h : ∀ v, A v ⊆ B v)
    (a : V) (c : Color) (v : V) : trim G A a c v ⊆ trim G B a c v := by
  unfold trim
  split_ifs
  · exact Finset.filter_subset_filter _ (h v)
  · exact Finset.erase_subset_erase _ (h v)
  · exact h v

private theorem trim_fits {A : Lists V} {a : V} {c : Color} {f : V → Color}
    (hf : Fits A f) (hc : f a = c) (he : ProperOn (incident G a) f) :
    Fits (trim G A a c) f := by
  intro v
  unfold trim
  split_ifs with hv hadj
  · exact Finset.mem_filter.mpr ⟨hf v, hv.symm ▸ hc⟩
  · exact Finset.mem_erase.mpr ⟨hc ▸ (he a v (incident_mem G hadj)).symm, hf v⟩
  · exact hf v

private def colorNeighbors (A : Lists V) (a : V) (c : Color) : Finset V :=
  (G.neighborFinset a).filter fun v => c ∈ A v

private def Hard (A : Lists V) (d : ℕ) (a : V) (c : Color) : Prop :=
  d ≤ (colorNeighbors G A a c).card

private theorem mass_trim {A : Lists V} {d : ℕ} {a : V} {c : Color}
    (hd : Hard G A d a c) : mass (trim G A a c) + d ≤ mass A := by
  have h := mass_account (trim_subset G A a c) (colorNeighbors G A a c) (by
    intro v hv
    have h := Finset.mem_filter.mp hv
    have hadj : G.Adj a v := by simpa using h.1
    have hne : v ≠ a := (G.ne_of_adj hadj).symm
    simpa [trim, hne, hadj] using Finset.card_erase_lt_of_mem h.2)
  exact (Nat.add_le_add_left hd _).trans h

private theorem at_most_one_soft {A : Lists V} (hstable : Stable G A)
    (hne : ∀ v, (A v).Nonempty) {a : V} (ha : A a = Finset.univ)
    {d : ℕ} (hd : 2 * d ≤ G.degree a)
    {c e : Color} (hce : c ≠ e) (hc : ¬ Hard G A d a c) :
    Hard G A d a e := by
  classical
  have hcover : G.neighborFinset a ⊆ colorNeighbors G A a c ∪ colorNeighbors G A a e := by
    intro v hv
    have haadj : G.Adj a v := by simpa using hv
    have htwo : 2 ≤ (A v).card := by
      by_contra! hsmall
      have hcard : (A v).card = 1 := by
        have := Finset.card_pos.mpr (hne v)
        omega
      obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hcard
      exact (hstable v a b haadj.symm hb) (ha ▸ Finset.mem_univ b)
    have hce' : c ∈ A v ∨ e ∈ A v := by
      by_contra! hm
      have hsub : A v ⊆ (Finset.univ.erase c).erase e := by
        intro b hb
        exact Finset.mem_erase.mpr ⟨fun ht => hm.2 (ht ▸ hb),
          Finset.mem_erase.mpr ⟨fun ht => hm.1 (ht ▸ hb), Finset.mem_univ _⟩⟩
      have hg := Finset.card_le_card hsub
      have hes : e ∈ (Finset.univ : Finset Color).erase c := by simp [hce.symm]
      have hs : ((Finset.univ : Finset Color).erase c).card = 2 := by simp
      rw [Finset.card_erase_of_mem hes, hs] at hg
      omega
    rcases hce' with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,h⟩)
  have hcov := Finset.card_le_card hcover
  have hu := Finset.card_union_le (colorNeighbors G A a c) (colorNeighbors G A a e)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcov
  unfold Hard at *
  omega

private theorem terminal (A : Lists V) (d : ℕ) (S : Finset (Sym2 V))
    (hS : S ⊆ G.edgeFinset) (hcard : S.card ≤ 10 * Fintype.card V)
    (hno : ∀ f, Fits A f → ProperOn S f → False) :
    Cases G A d S (fun _ => none) :=
  ⟨hS, hcard, by simp, fun f hf hs => (hno f hf hs).elim⟩

private theorem branch_two {A B : Lists V} (d : ℕ) (S : Finset (Sym2 V))
    (hS : S ⊆ G.edgeFinset) (hcard : S.card ≤ 8 * Fintype.card V)
    (hsub : ∀ v, B v ⊆ A v)
    (a b : V) (allowed : Color → Color → Prop)
    (hbranch : ∀ f, Fits A f → ProperOn S f → Fits B f ∧ allowed (f a) (f b))
    (hHard : ∀ c e, allowed c e → Hard G B d a c ∨ Hard G B d b e) :
    ∃ T P, Cases G A d T P := by
  classical
  let assignments : Fin 9 ≃ Color × Color := (finProdFinEquiv (m := 3) (n := 3)).symm
  let children (i : Fin 9) : Option (Lists V) :=
    let ce := assignments i
    if allowed ce.1 ce.2 then
      some (trim G (trim G B a ce.1) b ce.2)
    else none
  let T := (S ∪ incident G a) ∪ incident G b
  refine ⟨T, children, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset (Finset.union_subset hS (incident_subset G a)) (incident_subset G b)
  · have h₁ := Finset.card_union_le S (incident G a)
    have h₂ := Finset.card_union_le (S ∪ incident G a) (incident G b)
    have h₃ := incident_card G a
    have h₄ := incident_card G b
    change ((S ∪ incident G a) ∪ incident G b).card ≤ _
    omega
  · intro i C hi
    rcases hce : assignments i with ⟨c,e⟩
    have hh : allowed c e := by
      by_contra hn
      simp [children, hce, hn] at hi
    have hC : trim G (trim G B a c) b e = C := by
      simpa [children, hce, hh] using hi
    subst C
    have hm := mass_mono hsub
    rcases hHard c e hh with ha | hb
    · have hord := mass_mono (trim_subset G (trim G B a c) b e)
      have hdrop := mass_trim G ha
      omega
    · have hord := mass_mono (trim_mono G (trim_subset G B a c) b e)
      have hdrop := mass_trim G hb
      omega
  · intro f hf hT
    have hTab : ProperOn (S ∪ incident G a) f := proper_subset Finset.subset_union_left hT
    have ⟨hB,hallowed⟩ := hbranch f hf (proper_subset Finset.subset_union_left hTab)
    refine ⟨assignments.symm (f a, f b), trim G (trim G B a (f a)) b (f b), ?_, ?_⟩
    · simp [children, hallowed]
    · exact trim_fits G (trim_fits G hB rfl
        (proper_subset Finset.subset_union_right hTab)) rfl
        (proper_subset Finset.subset_union_right hT)

private theorem choose_binary (S : Finset Color) (hS : S.card = 2) :
    ∃ c : Bool → Color, Function.Injective c ∧ ∀ a, a ∈ S ↔ ∃ b, c b = a := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  refine ⟨fun t => if t then a else b, ?_, ?_⟩
  · intro s t h
    cases s <;> cases t <;> simp_all [Ne.symm hab]
  · intro c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    · rintro ⟨t, rfl⟩
      cases t <;> simp

private theorem full_or_at_most_two (B : Lists V) (v : V) :
    B v = Finset.univ ∨ (B v).card ≤ 2 := by
  by_cases h : (B v).card = 3
  · exact Or.inl ((Finset.card_eq_iff_eq_univ (B v)).mp (by simpa using h))
  · exact Or.inr (by have hc := Finset.card_le_univ (B v); simp at hc; omega)

private theorem blocker_of_defaults {B : Lists V} (hB : Stable G B)
    (hne : ∀ v, (B v).Nonempty) (default : V → Color)
    (hno : ¬ G.Colorable 3) :
    (∃ S ⊆ G.edgeFinset, S.card ≤ 4 * Fintype.card V ∧
      ∀ f, Fits B f → ProperOn S f → False) ∨
      ∃ a b, B a = Finset.univ ∧ B b = Finset.univ ∧
        ∃ S ⊆ G.edgeFinset, S.card ≤ 4 * Fintype.card V ∧
          ∀ f, Fits B f → ProperOn S f → f a ≠ default a ∨ f b ≠ default b := by
  classical
  let W := {v : V // (B v).card = 2}
  have hW : Fintype.card W ≤ Fintype.card V :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have choices : ∀ w : W, ∃ c : Bool → Color, Function.Injective c ∧
      ∀ a, a ∈ B w.val ↔ ∃ b, c b = a := fun w => choose_binary (B w.val) w.property
  choose c hc using choices
  let pick (l : W × Bool) : Color := c l.1 l.2
  let step (e : Sym2 V) (a b : W × Bool) : Prop :=
    s(a.1.val,b.1.val) = e ∧ pick a = pick (opposite b)
  have step_reversal e a b (h : step e a b) : step e (opposite b) (opposite a) := by
    change s(b.1.val,a.1.val) = e ∧ pick (opposite b) = pick (opposite (opposite a))
    rw [opposite_opposite, Sym2.eq_swap]
    exact ⟨h.1,h.2.symm⟩
  let U : Set (W × Bool) :=
    {l | ∃ v, B v = Finset.univ ∧ G.Adj v l.1.val ∧ pick (opposite l) = default v}
  by_cases heq : ∃ a b, B a = Finset.univ ∧ B b = Finset.univ ∧
      G.Adj a b ∧ default a = default b
  · obtain ⟨a,b,ha,hb,hab,hd⟩ := heq
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    refine Or.inr ⟨a,b,ha,hb,{s(a,b)},?_,by simp; omega,?_⟩
    · simpa using hab
    · intro f hf hproper
      by_contra! hh
      exact hproper a b (Finset.mem_singleton_self _) (hh.1.trans (hd.trans hh.2.symm))
  have no_binary : ¬ ∃ g, Respects step G.edgeFinset g ∧ ∀ l ∈ U, TrueLiteral g l := by
    rintro ⟨g,hg,hU⟩
    let f (v : V) : Color :=
      if h : (B v).card = 2 then c ⟨v,h⟩ (g ⟨v,h⟩)
      else if B v = Finset.univ then default v else (hne v).choose
    have hfit : Fits B f := by
      intro v
      unfold f
      split_ifs with h₂ h₃
      · exact ((hc ⟨v,h₂⟩).2 _).2 ⟨_,rfl⟩
      · rw [h₃]
        exact Finset.mem_univ _
      · exact (hne v).choose_spec
    have hf₂ (v : W) : f v.val = pick (v,g v) := by simp [f, v.property, pick]
    have hf₃ (v : V) (h : B v = Finset.univ) : f v = default v := by
      simp [f, h]
    have singleton {u v : V} (huv : G.Adj u v) (hc : (B u).card = 1) :
        f u ≠ f v := by
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
      have hu : f u = a := Finset.mem_singleton.mp (ha ▸ hfit u)
      exact fun h => (hB u v a huv ha) ((h.symm.trans hu) ▸ hfit v)
    have full_two {u : V} {v : W} (huv : G.Adj u v.val) (hu : B u = Finset.univ) :
        f u ≠ f v.val := by
      intro h
      let l := (v,g v)
      have hneg : opposite l ∈ U := by
        refine ⟨u,hu,huv,?_⟩
        rw [opposite_opposite]
        exact (hf₂ v).symm.trans (h.symm.trans (hf₃ u hu))
      exact (true_opposite g l).1 (hU (opposite l) hneg) rfl
    have proper : ∀ u v, G.Adj u v → f u ≠ f v := by
      intro u v huv heq'
      have hcu := Finset.card_pos.mpr (hne u)
      have hcv := Finset.card_pos.mpr (hne v)
      rcases full_or_at_most_two B u with hu | hu <;>
        rcases full_or_at_most_two B v with hv | hv
      · exact heq ⟨u,v,hu,hv,huv,(hf₃ u hu).symm.trans (heq'.trans (hf₃ v hv))⟩
      · by_cases hv₂ : (B v).card = 2
        · exact full_two (v := ⟨v,hv₂⟩) huv hu heq'
        · exact singleton huv.symm (by omega) heq'.symm
      · by_cases hu₂ : (B u).card = 2
        · exact full_two (v := ⟨u,hu₂⟩) huv.symm hv heq'.symm
        · exact singleton huv (by omega) heq'
      · by_cases hu₂ : (B u).card = 2
        · by_cases hv₂ : (B v).card = 2
          · let l : W × Bool := (⟨u,hu₂⟩,g ⟨u,hu₂⟩)
            let m : W × Bool := (⟨v,hv₂⟩,g ⟨v,hv₂⟩)
            have hstep : step s(u,v) l (opposite m) := by
              refine ⟨rfl,?_⟩
              rw [opposite_opposite]
              exact (hf₂ ⟨u,hu₂⟩).symm.trans (heq'.trans (hf₂ ⟨v,hv₂⟩))
            have hneg := hg s(u,v) (by simpa using huv) l (opposite m) hstep rfl
            exact (true_opposite g m).1 hneg rfl
          · exact singleton huv.symm (by omega) heq'.symm
        · exact singleton huv (by omega) heq'
    exact hno ⟨SimpleGraph.Coloring.mk f (fun h => proper _ _ h)⟩
  have binary_of_fit {S : Finset (Sym2 V)} {f : V → Color}
      (hf : Fits B f) (hp : ProperOn S f) :
      ∃ g : W → Bool, Respects step S g ∧ ∀ w : W, pick (w,g w) = f w.val := by
    have ex (w : W) : ∃ b, c w b = f w.val :=
      ((hc w).2 _).1 (hf w.val)
    choose g hg using ex
    refine ⟨g, ?_, hg⟩
    intro e he a b hstep htrue
    by_contra hfalse
    have htrue' := (true_opposite g b).2 hfalse
    have ha : pick a = f a.1.val := by
      change c a.1 a.2 = _
      rw [← show g a.1 = a.2 from htrue]
      exact hg _
    have hb : pick (opposite b) = f b.1.val := by
      change c b.1 (!b.2) = _
      rw [← show g b.1 = !b.2 from htrue']
      exact hg _
    exact hp _ _ (hstep.1.symm ▸ he) (ha.symm.trans (hstep.2.trans hb))
  rcases binary_obstruction step step_reversal no_binary with
    ⟨S,hS,hcard,hbad⟩ | ⟨a,ha,b,hb,S,hS,hcard,hbad⟩
  · refine Or.inl ⟨S,hS,hcard.trans (Nat.mul_le_mul_left _ hW),?_⟩
    intro f hf hp
    obtain ⟨g,hg,_⟩ := binary_of_fit hf hp
    exact hbad ⟨g,hg⟩
  · obtain ⟨u,hu,hua,hda⟩ := ha
    obtain ⟨v,hv,hvb,hdb⟩ := hb
    let T := insert s(u,a.1.val) (insert s(v,b.1.val) S)
    have hT : T ⊆ G.edgeFinset :=
      Finset.insert_subset_iff.mpr ⟨by simpa using hua,
        Finset.insert_subset_iff.mpr ⟨by simpa using hvb,hS⟩⟩
    have hTsize : T.card ≤ 4 * Fintype.card V := by
      have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
      have h₁ := Finset.card_insert_le s(u,a.1.val) (insert s(v,b.1.val) S)
      have h₂ := Finset.card_insert_le s(v,b.1.val) S
      change (insert s(u,a.1.val) (insert s(v,b.1.val) S)).card ≤ _
      omega
    refine Or.inr ⟨u,v,hu,hv,T,hT,hTsize,?_⟩
    intro f hf hp
    by_contra! hdef
    have hps : ProperOn S f := proper_subset
      ((Finset.subset_insert s(v,b.1.val) S).trans (Finset.subset_insert _ _)) hp
    obtain ⟨g,hg,hgf⟩ := binary_of_fit hf hps
    have forced (l : W × Bool) (w : V) (hcol : pick (opposite l) = default w)
        (hfw : f w = default w) (he : s(w,l.1.val) ∈ T) : TrueLiteral g l := by
      by_contra hf'
      have h := (true_opposite g l).2 hf'
      have hcolor : pick (opposite l) = f l.1.val := by
        change c l.1 (!l.2) = _
        rw [← show g l.1 = !l.2 from h]
        exact hgf _
      exact hp w l.1.val he (hfw.trans (hcol.symm.trans hcolor))
    exact hbad g hg (forced a u hda hdef.1 (Finset.mem_insert_self _ _))
      (forced b v hdb hdef.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))

private theorem local_cases (d : ℕ)
    (hdegree : ∀ v, 2 * d ≤ G.degree v) (hno : ¬ G.Colorable 3)
    (A : Lists V) : ∃ S P, Cases G A d S P := by
  classical
  obtain ⟨B,F,hsub,hF,hcost,hforce,hstable⟩ := propagate G A
  have hA : mass A ≤ 3 * Fintype.card V := by
    unfold mass
    simpa [mul_comm] using
      (Finset.sum_le_sum fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        (Finset.card_le_univ (A v) : (A v).card ≤ Fintype.card Color))
  have hcardF : F.card ≤ 3 * Fintype.card V := by omega
  by_cases hab : ∀ v, (B v).Nonempty
  · by_cases hh : ∃ a, B a = Finset.univ ∧ ∀ c, Hard G B d a c
    · obtain ⟨a,ha,hac⟩ := hh
      exact branch_two G d F hF (by omega) hsub a a (fun _ _ => True)
        (fun f hf hp => ⟨hforce f hp hf, True.intro⟩)
        (fun c _ _ => Or.inl (hac c))
    · have def_exists (a : V) : ∃ c : Color, ∀ b : Color,
          B a = Finset.univ → b ≠ c → Hard G B d a b := by
        by_cases h : B a = Finset.univ
        · have hs : ¬ ∀ c, Hard G B d a c := fun hh' => hh ⟨a,h,hh'⟩
          push Not at hs
          obtain ⟨c,hc⟩ := hs
          exact ⟨c, fun b _ hb => at_most_one_soft G hstable hab h
            (hdegree a) hb.symm hc⟩
        · exact ⟨0, fun _ h' => (h h').elim⟩
      choose defColor hdef using def_exists
      rcases blocker_of_defaults G hstable hab defColor hno with
        ⟨S,hS,hcard,hbad⟩ | ⟨a,b,ha,hb,S,hS,hcard,hbad⟩
      · refine ⟨F ∪ S,_,terminal G A d (F ∪ S) (Finset.union_subset hF hS) ?_ ?_⟩
        · have h := Finset.card_union_le F S
          omega
        · intro f hf hp
          exact hbad f (hforce f (proper_subset Finset.subset_union_left hp) hf)
            (proper_subset Finset.subset_union_right hp)
      · refine branch_two G d (F ∪ S) (Finset.union_subset hF hS) ?_ hsub a b
          (fun c e => c ≠ defColor a ∨ e ≠ defColor b) ?_ ?_
        · have h := Finset.card_union_le F S
          omega
        · intro f hf hp
          have h := hforce f (proper_subset Finset.subset_union_left hp) hf
          exact ⟨h, hbad f h (proper_subset Finset.subset_union_right hp)⟩
        · intro c e h
          exact h.imp (hdef a c ha) (hdef b e hb)
  · push Not at hab
    obtain ⟨v,hv⟩ := hab
    refine ⟨F,_,terminal G A d F hF (by omega) ?_⟩
    intro f hf hp
    simpa [hv] using hforce f hp hf v

private theorem all_edges_of_obstruction {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hcrit : Erdos1032.IsKCritical G 4)
    (S : Finset (Sym2 (Fin n))) (hS : S ⊆ G.edgeFinset)
    (hno : ¬ ∃ f, ProperOn S f) : S = G.edgeFinset := by
  classical
  apply Finset.Subset.antisymm hS
  intro e he
  by_contra h
  have he' := hcrit.2 e (SimpleGraph.mem_edgeFinset.mp he)
  have hc : (G.deleteEdges {e}).Colorable 3 := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
    have hfour := hcrit.1.1
    change (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber at he'
    rw [hfour] at he'
    apply (ENat.lt_add_one_iff (by simp : (3 : ℕ∞) ≠ ⊤)).mp
    simpa [show (3 : ℕ∞) + 1 = 4 by norm_num] using he'
  obtain ⟨f⟩ := hc
  apply hno
  refine ⟨f,fun u v hmem => f.valid (SimpleGraph.deleteEdges_adj.mpr ⟨?_,?_⟩)⟩
  · exact (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp (hS hmem))
  · simpa only [Set.mem_singleton_iff] using fun hEq : s(u,v) = e => h (hEq ▸ hmem)

end Coloring

open Filter in
private theorem refutation : ¬ (type_of% @Erdos1032.erdos_1032) := by
  classical
  rintro ⟨ε,hε,hfreq⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (9 / ε)
  have hk' : (9 : ℝ) < ε * (k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hk
  let C : ℕ := 10 ^ (k + 1)
  obtain ⟨N,hN⟩ := exists_nat_gt ((4 + 2 * (C : ℝ)) / ε)
  have hN' : (4 : ℝ) + 2 * (C : ℝ) < ε * (N : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hN
  obtain ⟨n,hnN,G,hcrit,hmin⟩ := frequently_atTop.mp hfreq (N + 1)
  have hn : 0 < n := by omega
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hsize : (4 : ℝ) + 2 * (C : ℝ) < (G.minDegree : ℝ) :=
    hN'.trans_le ((mul_le_mul_of_nonneg_left hNr hε.le).trans hmin)
  have hmin2 : 2 ≤ G.minDegree := by
    have hC : (0 : ℝ) ≤ (C : ℝ) := by positivity
    exact_mod_cast (show (2 : ℝ) ≤ (G.minDegree : ℝ) by linarith)
  let d := G.minDegree / 2
  have hd : 0 < d := by dsimp [d]; omega
  have hthree : G.minDegree ≤ 3 * d := by dsimp [d]; omega
  have hthree' : (G.minDegree : ℝ) ≤ 3 * (d : ℝ) := by exact_mod_cast hthree
  have hprod : 3 * n < (k + 1) * d := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := mul_lt_mul_of_pos_right hk' hn'
    have hh' := mul_le_mul_of_nonneg_right (hmin.trans hthree') (Nat.cast_nonneg k)
    have hkr : (3 : ℝ) * n < (k : ℝ) * d := by nlinarith only [hh, hh']
    have ht : 3 * n < k * d := by exact_mod_cast hkr
    exact ht.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ k))
  have hdeg : ∀ v, 2 * d ≤ G.degree v :=
    fun v => (by dsimp [d]; omega : 2 * d ≤ G.minDegree).trans (G.minDegree_le_degree v)
  have hno : ¬ G.Colorable 3 := by
    intro h
    have hle := h.chromaticNumber_le
    rw [hcrit.1.1] at hle
    norm_num at hle
  have hA : mass (fun _ : Fin n => (Finset.univ : Finset Color)) < (k + 1) * d := by
    simpa [mass, mul_comm] using hprod
  obtain ⟨S,hS,hcard,hob⟩ :=
    sparse_from_cases G d hd (local_cases G d hdeg hno) k _ hA
  have hEq := all_edges_of_obstruction G hcrit S hS (by
    rintro ⟨f,h⟩
    exact hob ⟨f,(fun _ => Finset.mem_univ _),h⟩)
  rw [hEq] at hcard
  have hs : n * G.minDegree ≤ 2 * (C * n) := by
    calc
      n * G.minDegree = ∑ _ : Fin n, G.minDegree := by simp
      _ ≤ ∑ v : Fin n, G.degree v :=
        Finset.sum_le_sum fun v _ => G.minDegree_le_degree v
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * (C * n) := Nat.mul_le_mul_left 2 (by simpa [C] using hcard)
  have hbound : G.minDegree ≤ 2 * C := by
    apply Nat.le_of_mul_le_mul_left _ hn
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  have hr : (G.minDegree : ℝ) ≤ 2 * (C : ℝ) := by exact_mod_cast hbound
  linarith


end OMA.Erdos1032

theorem OMA.disproof : ¬ (type_of% @Erdos1032.erdos_1032) :=
  OMA.Erdos1032.refutation
