import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1

/-! The five-slice square family of Friedland's critical-format conjecture.

The generic rank at the dimension-count ceiling has three arithmetic
progressions. Start the construction at square side lengths 5, 6 and 21,
then enlarge both square axes by two for every five additional points.
The even progression starts at 6; the two odd progressions meet the
correct ceiling below 21 and from 21 onwards.

The 21-by-21 base partitions into seven groups of three on each axis.
A cyclic grid with one simple tensor per cell gives its 49 points. In the
growth step, extra points are supported on one new group together with
the base, and a common specialization of the local tangent matrices
covers every sector. Finally, the bounded-grid theorem places the factor
entries between zero and twice the ambient dimension.

For the general conjecture see [Friedland, Conjecture 5.1](https://arxiv.org/abs/0805.3777).
-/

namespace CriticalTensor

def Spans (a b c r : ℕ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

/-- A diagonal block with a regular coordinate part of length h and a base of length d. -/
def Border (a d h base extra : ℕ) : Prop :=
  ∃ X : Fin extra → Fin a → ℂ, ∃ Y Z : Fin extra → (Fin h ⊕ Fin d) → ℂ,
  ∃ x : Fin base → Fin a → ℂ, ∃ y z : Fin base → Fin d → ℂ,
    ∀ T : Fin a → (Fin h ⊕ Fin d) → (Fin h ⊕ Fin d) → ℂ,
    ∃ U : Fin extra → Fin a → ℂ, ∃ V W : Fin extra → (Fin h ⊕ Fin d) → ℂ,
    ∃ v w : Fin base → Fin h → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
      T i j k =
        (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
        ∑ t, (x t i*(j.elim (v t) (fun _ => 0) * k.elim (fun _ => 0) (z t)) +
          x t i*(j.elim (fun _ => 0) (y t) * k.elim (w t) (fun _ => 0)))

/-- Two independent regular groups interact through one partial variation
of each point in the opposite group. -/
def Cross (a h extra : ℕ) : Prop :=
  ∃ x₁ x₂ : Fin extra → Fin a → ℂ, ∃ y z : Fin extra → Fin h → ℂ,
    ∀ T : Fin a → Fin h → Fin h → ℂ, ∃ v w : Fin extra → Fin h → ℂ, ∀ i j k,
      T i j k = ∑ t, (x₂ t i*(v t j*z t k) + x₁ t i*(y t j*w t k))

end CriticalTensor

namespace CriticalTensor.Growth

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

/-- A priority for each sector is enough. Distinct sectors at the same priority
are disjoint on their diagonal rows and columns. -/
lemma graded_surjective {R C S : Type} [Fintype R] [Fintype C] [Fintype S] [DecidableEq S]
    (f : R → S) (g : C → S) (priority : S → Fin 3) (A : Matrix R C ℂ)
    (zero_above : ∀ i j, f i ≠ g j → priority (f i) ≤ priority (g j) → A i j=0)
    (local_maps : ∀ s : S, Function.Surjective
      (A.submatrix (fun i : {i // f i=s} => i.val) (fun j : {j // g j=s} => j.val)).mulVec) :
    Function.Surjective A.mulVec := by
  classical
  have hpre (j : R) : ∃ v : {k // g k=f j} → ℂ, ∀ i : {i // f i=f j},
      (∑ k, A i.val k.val * v k) = if i.val=j then 1 else 0 := by
    obtain ⟨v,hv⟩ := local_maps (f j) fun i => if i.val=j then 1 else 0
    exact ⟨v,fun i => congrFun hv i⟩
  choose v hv using hpre
  let B : Matrix C R ℂ := fun k j => if h : g k=f j then v j ⟨k,h⟩ else 0
  let L := A*B
  have entries (i j : R) : L i j = ∑ k : {k // g k=f j}, A i k.val*v j k := by
    change (∑ k : C, A i k*(if h : g k=f j then v j ⟨k,h⟩ else 0)) = _
    let F (k : C) := A i k * (if h : g k=f j then v j ⟨k,h⟩ else 0)
    have e := (Equiv.sumCompl (fun k : C => g k=f j)).sum_comp F
    rw [Fintype.sum_sum_type] at e
    have hp (q : {k // g k=f j}) : g q.val=f j := q.property
    have hn (q : {k // g k≠f j}) : g q.val≠f j := q.property
    simpa [F,hp,hn] using e.symm
  have off (i j : R) (h : f i ≠ f j) (hle : priority (f i) ≤ priority (f j)) : L i j=0 := by
    rw [entries]
    apply Finset.sum_eq_zero
    intro k _
    rw [zero_above i k.val (by simpa only [k.property] using h)
      (by simpa only [k.property] using hle),zero_mul]
  have triangular : L.BlockTriangular (fun i => OrderDual.toDual (priority (f i))) := by
    intro i j h
    change priority (f i) < priority (f j) at h
    exact off i j (fun he => (ne_of_lt h) (congrArg priority he)) (le_of_lt h)
  have diag (s : (Fin 3)ᵒᵈ) : L.toSquareBlock (fun i => OrderDual.toDual (priority (f i))) s = 1 := by
    ext i j
    obtain ⟨i,hi⟩ := i
    obtain ⟨j,hj⟩ := j
    have hlev : priority (f i)=priority (f j) := hi.trans hj.symm
    change L i j = _
    by_cases hij : f i=f j
    · rw [entries,hv j ⟨i,hij⟩,Matrix.one_apply]
      simp only [Subtype.mk.injEq]
    · rw [off i j hij (le_of_eq hlev),Matrix.one_apply]
      simp [show i ≠ j from fun h => hij (congrArg f h)]
  have detL : L.det=1 := by rw [triangular.det_fintype]; simp [diag]
  have hL : Function.Surjective L.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [detL]; exact isUnit_one))
  intro y
  obtain ⟨z,hz⟩ := hL y
  refine ⟨B.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  exact hz

/-- Transfer the row equations of a finite template to a global sector. Every
row needed by the sector has a local representative. Coincident selected
columns can be combined by summing their coefficients. -/
lemma cover_matrix {R C I J : Type} [Fintype C] [DecidableEq C] [Fintype J]
    (A : Matrix R C ℂ) (L : Matrix I J ℂ) (rmap : I → R) (cmap : J → C)
    (hR : Function.Surjective rmap) (hM : ∀ i j, A (rmap i) (cmap j)=L i j)
    (hs : Function.Surjective L.mulVec) : Function.Surjective A.mulVec := by
  classical
  let E : Matrix C J ℂ := fun k j => if k=cmap j then 1 else 0
  have hcols (i j) : (A*E) (rmap i) j=L i j := by
    rw [Matrix.mul_apply]
    simpa [E,mul_ite,Finset.sum_ite_eq'] using hM i j
  intro y
  obtain ⟨z,hz⟩ := hs (fun i => y (rmap i))
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec]
  funext r
  obtain ⟨i,rfl⟩ := hR r
  change (∑ j, (A*E) (rmap i) j*z j) = _
  simpa only [hcols,Matrix.mulVec,dotProduct] using congrFun hz i

end CriticalTensor.Growth

namespace CriticalTensor.Growth

open MvPolynomial

structure Dimensions where
  a : ℕ
  d : ℕ
  h : ℕ
  base : ℕ
  extra : ℕ

variable (p : Dimensions)

abbrev Pt (G : Type) := Fin p.base ⊕ (G × Fin p.extra)
abbrev Axis (G : Type) := Fin p.d ⊕ (G × Fin p.h)
abbrev LocalAxis := Fin p.h ⊕ Fin p.d
abbrev Dir (I : Type) := Fin p.a ⊕ (I ⊕ I)
abbrev V (G : Type) := (Fin p.base × Dir p (Fin p.d)) ⊕ (G × Fin p.extra × Dir p (LocalAxis p))
abbrev RR (G : Type) := Fin p.a × Axis p G × Axis p G
abbrev CC (G : Type) := Pt p G × Dir p (Axis p G)
abbrev Pair (G : Type) := {z : G × G // z.1 ≠ z.2}
abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
abbrev Arm := (Fin p.h × Fin p.d) ⊕ ((Fin p.d × Fin p.h) ⊕ (Fin p.h × Fin p.h))

def arms : Arm p → LocalAxis p × LocalAxis p
  | .inl (j,k) => (.inl j,.inr k)
  | .inr (.inl (j,k)) => (.inr j,.inl k)
  | .inr (.inr (j,k)) => (.inl j,.inl k)

def loc {G : Type} (g : G) : LocalAxis p → Axis p G
  | .inl u => .inr (g,u)
  | .inr j => .inl j

def Row {G : Type} : Sector G → Type
  | .inl _ => Fin p.a × Fin p.d × Fin p.d
  | .inr (.inl _) => Fin p.a × Arm p
  | .inr (.inr _) => Fin p.a × Fin p.h × Fin p.h

def Col {G : Type} : Sector G → Type
  | .inl _ => Fin p.base × Dir p (Fin p.d)
  | .inr (.inl _) => (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h))
  | .inr (.inr _) => Fin p.extra × (Fin p.h ⊕ Fin p.h)

instance {G : Type} (s : Sector G) : Fintype (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
instance {G : Type} (s : Sector G) : Fintype (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance
instance {G : Type} (s : Sector G) : DecidableEq (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance

def row {G : Type} : (s : Sector G) → Row p s → RR p G
  | .inl _,(i,j,k) => (i,.inl j,.inl k)
  | .inr (.inl g),(i,z) => (i,loc p g (arms p z).1,loc p g (arms p z).2)
  | .inr (.inr q),(i,j,k) => (i,.inr (q.val.1,j),.inr (q.val.2,k))

def col {G : Type} : (s : Sector G) → Col p s → CC p G
  | .inl _,(t,h) => (.inl t,h.map id (Sum.map Sum.inl Sum.inl))
  | .inr (.inl g),.inl (t,h) => (.inr (g,t),h.map id (Sum.map (loc p g) (loc p g)))
  | .inr (.inl g),.inr (t,.inl h) => (.inl t,.inr (.inl (.inr (g,h))))
  | .inr (.inl g),.inr (t,.inr h) => (.inl t,.inr (.inr (.inr (g,h))))
  | .inr (.inr q),(t,.inl h) => (.inr (q.val.2,t),.inr (.inl (.inr (q.val.1,h))))
  | .inr (.inr q),(t,.inr h) => (.inr (q.val.1,t),.inr (.inr (.inr (q.val.2,h))))

def lev {G : Type} : Sector G → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

section
variable {G K : Type} [DecidableEq G] [CommSemiring K]

def A (x : V p G → K) : Pt p G → Fin p.a → K
  | .inl t,i => x (.inl (t,.inl i))
  | .inr (g,t),i => x (.inr (g,t,.inl i))

def tail (b : Fin p.base → Fin p.d → K) (B : G → Fin p.extra → LocalAxis p → K) : Pt p G → Axis p G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (.inr j)
  | .inr (g,t),.inr (h,i) => if h=g then B g t (.inl i) else 0

def B (x : V p G → K) := tail p (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
def Cc (x : V p G → K) := tail p (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

def tangent (x : V p G → K) (r : RR p G) : CC p G → K
  | (t,.inl h) => if h=r.1 then B p x t r.2.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A p x t r.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A p x t r.1 * B p x t r.2.1 else 0

def full (x : V p G → K) : Matrix (Σ s : Sector G, Row p s) (Σ s : Sector G, Col p s) K :=
  fun r c => tangent p x (row p r.1 r.2) (col p c.1 c.2)

def block (x : V p G → K) (s : Sector G) : Matrix (Row p s) (Col p s) K :=
  fun r c => tangent p x (row p s r) (col p s c)

lemma tail_loc (b : Fin p.base → Fin p.d → K) (H : G → Fin p.extra → LocalAxis p → K)
    (g : G) (t : Fin p.extra) (j : LocalAxis p) : tail p b H (.inr (g,t)) (loc p g j) = H g t j := by
  cases j <;> simp [tail,loc]

omit [DecidableEq G] in
lemma loc_eq (g : G) (j k : LocalAxis p) : loc p g j=loc p g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] (φ : K →+* L) (b : Fin p.base → Fin p.d → K)
    (H : G → Fin p.extra → LocalAxis p → K) (t : Pt p G) (j : Axis p G) :
    φ (tail p b H t j) = tail p (fun t j => φ (b t j)) (fun g t j => φ (H g t j)) t j := by
  rcases t with t|⟨g,t⟩ <;> rcases j with j|⟨h,j⟩ <;> simp only [tail,map_zero]
  by_cases he : h=g <;> simp [he]

lemma block_eval (x : V p G → ℂ) (s : Sector G) :
    (block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s).map (eval x) = block p x s := by
  ext r j
  change eval x (tangent p MvPolynomial.X (row p s r) (col p s j)) = tangent p x (row p s r) (col p s j)
  generalize hc : col p s j = z
  rcases z with ⟨t,h|h|h⟩ <;> rcases t with t|⟨g,t⟩ <;>
    simp only [tangent,A,B,Cc,apply_ite,tail_map,map_mul,map_zero,eval_X]
  all_goals split <;> simp_all

end

lemma row_surj {G : Type} [DecidableEq G] : Function.Surjective (fun z : Σ s : Sector G, Row p s => row p z.1 z.2) := by
  rintro ⟨i,j|⟨g,j⟩,k|⟨l,k⟩⟩
  · exact ⟨⟨.inl (),i,j,k⟩,rfl⟩
  · exact ⟨⟨.inr (.inl l),i,.inr (.inl (j,k))⟩,rfl⟩
  · exact ⟨⟨.inr (.inl g),i,.inl (j,k)⟩,rfl⟩
  · by_cases h : g=l
    · subst l
      exact ⟨⟨.inr (.inl g),i,.inr (.inr (j,k))⟩,rfl⟩
    · exact ⟨⟨.inr (.inr ⟨(g,l),h⟩),i,j,k⟩,rfl⟩

end CriticalTensor.Growth

namespace CriticalTensor.Growth

variable (p : Dimensions) {G : Type} [DecidableEq G]

def param (a : Fin p.base → Fin p.a → ℂ) (b c : Fin p.base → Fin p.d → ℂ)
    (A : G → Fin p.extra → Fin p.a → ℂ) (B C : G → Fin p.extra → LocalAxis p → ℂ) : V p G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

lemma base_rank (hb : Spans p.a p.d p.d p.base) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inl ())).mulVec := by
  classical
  obtain ⟨a,b,c,hb⟩ := hb
  let x : V p G → ℂ := param p a b c 0 0 0
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,hu⟩ := hb fun i j k => y (i,j,k)
  let z : Fin p.base × Dir p (Fin p.d) → ℂ := fun (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.base × Dir p (Fin p.d), tangent p x (i,.inl j,.inl k) (col p (.inl ()) s) * z s) = y (i,j,k)
  rw [hu,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq']
  ring

def target (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) : LocalAxis p → LocalAxis p → ℂ
  | .inl j,.inl k => y (i,.inr (.inr (j,k)))
  | .inl j,.inr k => y (i,.inl (j,k))
  | .inr j,.inl k => y (i,.inr (.inl (j,k)))
  | .inr _,.inr _ => 0

lemma target_arms (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) (r : Arm p) :
    target p y i (arms p r).1 (arms p r).2=y (i,r) := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> rfl

lemma arms_hit (r : Arm p) : (arms p r).1.isLeft=true ∨ (arms p r).2.isLeft=true := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> simp [arms]

lemma border_rank (g : G) (hr : Border p.a p.d p.h p.base p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inl g))).mulVec := by
  classical
  obtain ⟨aa,bb,cc,a,b,c,hr⟩ := hr
  let x : V p G → ℂ := param p a b c (fun _ => aa) (fun _ => bb) (fun _ => cc)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨u,v,w,vb,wb,hu⟩ := hr (target p y)
  let z : (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)) → ℂ
    | .inl (t,h) => h.elim (u t) (Sum.elim (v t) (w t))
    | .inr (t,h) => h.elim (vb t) (wb t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,r⟩ := r
  change (∑ s : (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h)),
    tangent p x (i,loc p g (arms p r).1,loc p g (arms p r).2) (col p (.inr (.inl g)) s) * z s) = y (i,r)
  rw [← target_arms p y i r,hu i _ _ (arms_hit p r),Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [tangent,col,x,param,A,B,Cc,z,tail_loc,loc_eq,ite_mul,Finset.sum_ite_eq']
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type]
    rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;>
      simp [tangent,col,x,param,A,B,Cc,tail,z,arms,loc,ite_mul,Finset.sum_ite_eq'] <;> ring

lemma cross_rank (q : Pair G) (hc : Cross p.a p.h p.extra) :
    ∃ x : V p G → ℂ, Function.Surjective (block p x (.inr (.inr q))).mulVec := by
  classical
  obtain ⟨x₁,x₂,b,c,hc⟩ := hc
  let x : V p G → ℂ := param p 0 0 0 (fun g => if g=q.val.1 then x₁ else x₂)
    (fun _ t => Sum.elim (b t) 0) (fun _ t => Sum.elim (c t) 0)
  refine ⟨x,?_⟩
  intro y
  obtain ⟨v,w,hw⟩ := hc fun i j k => y (i,j,k)
  let z : Fin p.extra × (Fin p.h ⊕ Fin p.h) → ℂ := fun (t,h) => h.elim (v t) (w t)
  refine ⟨z,?_⟩
  funext r
  obtain ⟨i,j,k⟩ := r
  change (∑ s : Fin p.extra × (Fin p.h ⊕ Fin p.h),
    tangent p x (i,.inr (q.val.1,j),.inr (q.val.2,k)) (col p (.inr (.inr q)) s)*z s)=y (i,j,k)
  rw [hw,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type]
  simp [tangent,col,x,param,A,B,Cc,tail,z,ite_mul,Finset.sum_ite_eq',q.property.symm]
  ring

end CriticalTensor.Growth

namespace CriticalTensor.Growth

variable (p : Dimensions) {G : Type} [DecidableEq G] (x : V p G → ℂ)

private lemma arm_base (g : G) (r : Row p (.inr (.inl g))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,h|h|h⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail]

private lemma arm_other (g h : G) (gh : g ≠ h) (r : Row p (.inr (.inl g))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inl g)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases r with ⟨i,⟨j,k⟩|⟨j,k⟩|⟨j,k⟩⟩ <;> rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    simp [row,col,tangent,arms,loc,B,Cc,tail,gh,gh.symm]

private lemma pair_base (q : Pair G) (r : Row p (.inr (.inr q))) (z : Col p (G:=G) (.inl ())) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inl ()) z)=0 := by
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,h|h|h⟩ <;> simp [row,col,tangent,B,Cc,tail]

private lemma pair_arm (q : Pair G) (h : G) (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inl h))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inl h)) z)=0 := by
  rcases q with ⟨⟨g,l⟩,hg⟩
  change g≠l at hg
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,u|(u|u)|(u|u)⟩|⟨t,u|u⟩ <;>
    by_cases he : g=h <;> by_cases hf : l=h <;>
    simp_all [row,col,tangent,loc,B,Cc,tail]
  all_goals grind

private lemma pair_other (q q' : Pair G) (hpq : q≠q') (r : Row p (.inr (.inr q))) (z : Col p (.inr (.inr q'))) :
    tangent p x (row p (.inr (.inr q)) r) (col p (.inr (.inr q')) z)=0 := by
  rcases q with ⟨⟨a,b⟩,hab⟩
  rcases q' with ⟨⟨c,d⟩,hcd⟩
  have h : a=c → b≠d := by rintro rfl rfl; exact (hpq rfl).elim
  rcases r with ⟨i,j,k⟩
  rcases z with ⟨t,v|v⟩ <;> by_cases hac : a=c <;> by_cases hbd : b=d <;>
    simp_all [row,col,tangent,B,Cc,tail,eq_comm]

lemma off (s t : Sector G) (h : s≠t) (hl : lev s≤lev t) (r : Row p s) (z : Col p t) :
    tangent p x (row p s r) (col p t z)=0 := by
  rcases s with ⟨⟩|g|q <;> rcases t with ⟨⟩|h'|q'
  · exact (h rfl).elim
  · exact (by decide : ¬((2:Fin 3)≤1)) hl |>.elim
  · exact (by decide : ¬((2:Fin 3)≤0)) hl |>.elim
  · exact arm_base p x g r z
  · exact arm_other p x g h' (fun e => h (e ▸ rfl)) r z
  · exact (by decide : ¬((1:Fin 3)≤0)) hl |>.elim
  · exact pair_base p x q r z
  · exact pair_arm p x q h' r z
  · exact pair_other p x q q' (fun e => h (e ▸ rfl)) r z

end CriticalTensor.Growth

namespace CriticalTensor.Growth

open MvPolynomial

variable (p : Dimensions) {G : Type} [Fintype G] [DecidableEq G]

def actual (x : V p G → ℂ) : Matrix (RR p G) (CC p G) ℂ := tangent p x

lemma common (hb : Spans p.a p.d p.d p.base) (hr : Border p.a p.d p.h p.base p.extra)
    (hc : Cross p.a p.h p.extra) : ∃ x : V p G → ℂ, Function.Surjective (actual p x).mulVec := by
  classical
  have each (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective (block p x s).mulVec := by
    rcases s with ⟨⟩|g|q
    · exact base_rank p hb
    · exact border_rank p g hr
    · exact cross_rank p q hc
  let M (s : Sector G) := block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s
  have openSet (s : Sector G) : ∃ x : V p G → ℂ, Function.Surjective ((M s).map (eval x)).mulVec := by
    obtain ⟨x,h⟩ := each s
    exact ⟨x,by simpa only [M,block_eval] using h⟩
  obtain ⟨x,_,hx⟩ := simultaneous_surjectivity M openSet 1 one_ne_zero
  have hs (s : Sector G) : Function.Surjective (block p x s).mulVec := by simpa only [M,block_eval] using hx s
  have hfull : Function.Surjective (full p x).mulVec := by
    apply graded_surjective (fun r => r.1) (fun j => j.1) lev (full p x)
    · rintro ⟨s,i⟩ ⟨t,j⟩ h ht
      exact off p x s t h ht i j
    · intro s
      apply cover_matrix _ (block p x s) (fun i => ⟨⟨s,i⟩,rfl⟩) (fun j => ⟨⟨s,j⟩,rfl⟩)
      · rintro ⟨⟨t,i⟩,ht⟩
        change t=s at ht
        subst t
        exact ⟨i,rfl⟩
      · intro i j; rfl
      · exact hs s
  exact ⟨x,cover_matrix (actual p x) (full p x) (fun r => row p r.1 r.2) (fun j => col p j.1 j.2)
    (row_surj p) (fun _ _ => rfl) hfull⟩

lemma action (x : V p G → ℂ) (z : CC p G → ℂ) (i : Fin p.a) (j k : Axis p G) :
    (actual p x).mulVec z (i,j,k) = ∑ t : Pt p G,
      (z (t,.inl i)*(B p x t j*Cc p x t k) + A p x t i*(z (t,.inr (.inl j))*Cc p x t k) +
      A p x t i*(B p x t j*z (t,.inr (.inr k)))) := by
  classical
  change (∑ w : CC p G, tangent p x (i,j,k) w*z w)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [tangent,ite_mul,Finset.sum_ite_eq']
  ring

end CriticalTensor.Growth

namespace CriticalTensor

open Growth

/-- A base block, its border with one regular block, and an ordered pair of regular
blocks suffice for an arbitrary finite number of regular blocks along the two equal axes. -/
lemma grow (a d h base extra t : ℕ) (hb : Spans a d d base)
    (hr : Border a d h base extra) (hc : Cross a h extra) :
    Spans a (d+h*t) (d+h*t) (base+extra*t) := by
  classical
  let p : Dimensions := ⟨a,d,h,base,extra⟩
  let G := Fin t
  let e : Fin (d+h*t) ≃ Axis p G := Fintype.equivOfCardEq (by simp [G,p,Axis,Nat.mul_comm])
  let f : Fin (base+extra*t) ≃ Pt p G := Fintype.equivOfCardEq (by simp [G,p,Pt,Nat.mul_comm])
  obtain ⟨x,hx⟩ := common p (G:=G) hb hr hc
  refine ⟨fun t i => A p x (f t) i,fun t j => B p x (f t) (e j),fun t k => Cc p x (f t) (e k),?_⟩
  intro T
  obtain ⟨z,hz⟩ := hx fun r => T r.1 (e.symm r.2.1) (e.symm r.2.2)
  refine ⟨fun t i => z (f t,.inl i),fun t j => z (f t,.inr (.inl (e j))),
    fun t k => z (f t,.inr (.inr (e k))),?_⟩
  intro i j k
  have hw := (congrFun hz (i,e j,e k)).symm
  simp only [Equiv.symm_apply_apply] at hw
  rw [action] at hw
  exact hw.trans (f.sum_comp (fun t => z (t,Sum.inl i)*(B p x t (e j)*Cc p x t (e k)) +
    A p x t i*(z (t,Sum.inr (Sum.inl (e j)))*Cc p x t (e k)) +
    A p x t i*(B p x t (e j)*z (t,Sum.inr (Sum.inr (e k)))))).symm

end CriticalTensor

namespace CriticalTensor.FiveGrid

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

abbrev Slot (G : Type) (s : ℕ) := G × G × Fin s
abbrev Parameters (G W : Type) (s d : ℕ) := Slot G s × (Fin d ⊕ (Fin d ⊕ W))
abbrev Columns (G W : Type) (s d : ℕ) :=
  (G × Fin s × Fin d) ⊕ ((G × Fin s × Fin d) ⊕ (Fin s × W))

variable {s d : ℕ}

def LocalSpan {G W : Type} [Fintype G] (a b : Slot G s → Fin d → ℂ)
    (c : Slot G s → W → ℂ) (g h : G) : Prop :=
  ∀ T : Fin d → Fin d → W → ℂ,
    ∃ u v : G → Fin s → Fin d → ℂ, ∃ w : Fin s → W → ℂ, ∀ i j k,
      T i j k =
        (∑ l, ∑ t, u l t i * (b (l,h,t) j * c (l,h,t) k)) +
        (∑ l, ∑ t, a (g,l,t) i * (v l t j * c (g,l,t) k)) +
        ∑ t, a (g,h,t) i * (b (g,h,t) j * w t k)

def pad {G : Type} [DecidableEq G] (g : G) (v : Fin d → ℂ) (i : G × Fin d) : ℂ :=
  if g = i.1 then v i.2 else 0

lemma assemble {G W : Type} [Fintype G] [DecidableEq G] (a b : Slot G s → Fin d → ℂ)
    (c : Slot G s → W → ℂ) (H : ∀ g h, LocalSpan a b c g h)
    (T : (G × Fin d) → (G × Fin d) → W → ℂ) :
    ∃ u v : Slot G s → (G × Fin d) → ℂ, ∃ w : Slot G s → W → ℂ, ∀ i j k,
      T i j k = ∑ z, (u z i * (pad z.2.1 (b z) j * c z k) +
        pad z.1 (a z) i * (v z j * c z k) +
        pad z.1 (a z) i * (pad z.2.1 (b z) j * w z k)) := by
  classical
  choose U V Z h using fun g h => H g h (fun i j k => T (g,i) (h,j) k)
  refine ⟨fun z i => U i.1 z.2.1 z.1 z.2.2 i.2,
    fun z j => V z.1 j.1 z.2.1 z.2.2 j.2, fun z => Z z.1 z.2.1 z.2.2, ?_⟩
  rintro ⟨g,i⟩ ⟨f,j⟩ k
  rw [h g f i j k]
  simp only [Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]
    · simp [Fintype.sum_prod_type, pad, ite_mul, Finset.sum_ite_irrel]
  · simp [Fintype.sum_prod_type, pad, ite_mul, mul_ite, Finset.sum_ite_irrel]

def aval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (i : Fin d) := x (z, Sum.inl i)
def bval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (j : Fin d) := x (z, Sum.inr (Sum.inl j))
def cval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (k : W) := x (z, Sum.inr (Sum.inr k))

noncomputable def polynomialMatrix {G W : Type} [DecidableEq W] (g h : G) :
    Matrix (Fin d × Fin d × W) (Columns G W s d) (MvPolynomial (Parameters G W s d) ℂ)
  | (i,j,k), Sum.inl (l,t,q) =>
      if q = i then X ((l,h,t), Sum.inr (Sum.inl j)) * X ((l,h,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inl (l,t,q)) =>
      if q = j then X ((g,l,t), Sum.inl i) * X ((g,l,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inr (t,q)) =>
      if q = k then X ((g,h,t), Sum.inl i) * X ((g,h,t), Sum.inr (Sum.inl j)) else 0

lemma polynomial_action {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (g h : G) (x : Parameters G W s d → ℂ) (y : Columns G W s d → ℂ) (i j : Fin d) (k : W) :
    ((polynomialMatrix (s:=s) (d:=d) g h).map (eval x)).mulVec y (i,j,k) =
      (∑ l, ∑ t, y (Sum.inl (l,t,i)) * (bval x (l,h,t) j * cval x (l,h,t) k)) +
      (∑ l, ∑ t, aval x (g,l,t) i * (y (Sum.inr (Sum.inl (l,t,j))) * cval x (g,l,t) k)) +
      ∑ t, aval x (g,h,t) i * (bval x (g,h,t) j * y (Sum.inr (Sum.inr (t,k)))) := by
  classical
  change (∑ z : Columns G W s d, eval x (polynomialMatrix g h (i,j,k) z) * y z) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, polynomialMatrix, aval, bval, cval,
    apply_ite, Finset.sum_ite_eq', mul_assoc, mul_comm, add_assoc]

lemma local_iff_surjective {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (g h : G) (x : Parameters G W s d → ℂ) :
    LocalSpan (aval x) (bval x) (cval x) g h ↔
      Function.Surjective ((polynomialMatrix (s:=s) (d:=d) g h).map (eval x)).mulVec := by
  constructor
  · intro H T
    obtain ⟨u,v,w,hT⟩ := H fun i j k => T (i,j,k)
    let y : Columns G W s d → ℂ := Sum.elim (fun z => u z.1 z.2.1 z.2.2)
      (Sum.elim (fun z => v z.1 z.2.1 z.2.2) (fun z => w z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨i,j,k⟩ := z
    rw [polynomial_action]
    exact (hT i j k).symm
  · intro H T
    obtain ⟨y,hy⟩ := H fun z => T z.1 z.2.1 z.2.2
    refine ⟨fun l t i => y (Sum.inl (l,t,i)), fun l t j => y (Sum.inr (Sum.inl (l,t,j))),
      fun t k => y (Sum.inr (Sum.inr (t,k))), ?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (polynomial_action g h x y i j k)

lemma simultaneous_local {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (H : ∀ g h : G, ∃ x : Parameters G W s d → ℂ, LocalSpan (aval x) (bval x) (cval x) g h) :
    ∃ x : Parameters G W s d → ℂ, ∀ g h : G, LocalSpan (aval x) (bval x) (cval x) g h := by
  classical
  have h (p : G × G) : ∃ x : Parameters G W s d → ℂ,
      Function.Surjective ((polynomialMatrix p.1 p.2).map (eval x)).mulVec := by
    obtain ⟨x,hx⟩ := H p.1 p.2
    exact ⟨x, (local_iff_surjective _ _ _).mp hx⟩
  obtain ⟨x, _, hx⟩ := simultaneous_surjectivity (fun p : G × G => polynomialMatrix p.1 p.2)
    h 1 one_ne_zero
  exact ⟨x, fun g h => (local_iff_surjective g h x).mpr (hx (g,h))⟩

def relabel {G H : Type} (e f : G ≃ H) (z : Slot G s) : Slot H s := (e z.1, f z.2.1, z.2.2)

lemma relabel_local {G H W : Type} [Fintype G] [Fintype H] (e f : G ≃ H)
    (a b : Slot H s → Fin d → ℂ) (c : Slot H s → W → ℂ) (g h : G)
    (hs : LocalSpan a b c (e g) (f h)) :
    LocalSpan (fun z => a (relabel e f z)) (fun z => b (relabel e f z))
      (fun z => c (relabel e f z)) g h := by
  intro T
  obtain ⟨u,v,w,hT⟩ := hs T
  refine ⟨fun l => u (e l), fun l => v (f l), w, ?_⟩
  intro i j k
  rw [hT i j k]
  dsimp only [relabel]
  congr 1
  congr 1
  · exact (e.sum_comp (fun l => ∑ t, u l t i * (b (l,f h,t) j * c (l,f h,t) k))).symm
  · exact (f.sum_comp (fun l => ∑ t, a (e g,l,t) i * (v l t j * c (e g,l,t) k))).symm

set_option maxHeartbeats 800000 in
/-- One local witness works in every cell after relabeling the two group indices.
Their determinant conditions then hold at a single shared choice of the factors. -/
lemma spans_of_cell {g d s a : ℕ} [NeZero g]
    (x₀ : Parameters (Fin g) (Fin a) s d → ℂ)
    (h₀ : LocalSpan (aval x₀) (bval x₀) (cval x₀) 0 0) :
    CriticalTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
  classical
  let G := Fin g
  let W := Fin a
  have hw (i j : G) : ∃ x : Parameters G W s d → ℂ,
      LocalSpan (aval x) (bval x) (cval x) i j := by
    let e := Equiv.swap i 0
    let f := Equiv.swap j 0
    have ho : LocalSpan (aval x₀) (bval x₀) (cval x₀) (e i) (f j) := by simpa [e,f] using h₀
    exact ⟨fun z => x₀ (relabel e f z.1,z.2), relabel_local e f (aval x₀) (bval x₀) (cval x₀) i j ho⟩
  obtain ⟨x,h⟩ := simultaneous_local hw
  let A := fun z : Slot G s => pad z.1 (aval x z)
  let B := fun z : Slot G s => pad z.2.1 (bval x z)
  let C := cval x
  let e : (G × Fin d) ≃ Fin (g*d) := finProdFinEquiv
  let er : Slot G s ≃ Fin (g*(g*s)) := ((Equiv.refl G).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun t => C (er.symm t),fun t j => A (er.symm t) (e.symm j),
    fun t k => B (er.symm t) (e.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hw⟩ := assemble (aval x) (bval x) (cval x) h (fun j k i => T i (e j) (e k))
  refine ⟨fun t => w (er.symm t),fun t j => u (er.symm t) (e.symm j),
    fun t k => v (er.symm t) (e.symm k),?_⟩
  intro i j k
  have hv := hw (e.symm j) (e.symm k) i
  simp only [Equiv.apply_symm_apply] at hv
  rw [hv, ← er.sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.symm_apply_apply,A,B,C]
  ring

end CriticalTensor.FiveGrid

namespace CriticalTensor.FiveGrid.Binary

def intBit (b : Bool) : ℤ := if b then 1 else 0
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma cast_intBit (b : Bool) : ((intBit b : ℤ) : ZMod 2) = fieldBit b := by cases b <;> rfl

lemma fieldBit_xor (a b : Bool) : fieldBit (a ^^ b) = fieldBit a + fieldBit b := by
  cases a <;> cases b <;> decide

/-- XOR of the columns whose index occurs in the mask. -/
def xorColumns (cols : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => xorColumns cols mask m ^^^ (if mask.testBit m then cols m else 0)

lemma xorColumns_entry (cols : ℕ → ℕ) (mask row m : ℕ) :
    fieldBit ((xorColumns cols mask m).testBit row) =
      ∑ j ∈ Finset.range m, fieldBit ((cols j).testBit row) * fieldBit (mask.testBit j) := by
  induction m with
  | zero => simp [xorColumns, fieldBit]
  | succ m ih =>
    rw [xorColumns, Nat.testBit_xor, fieldBit_xor, ih, Finset.sum_range_succ]
    cases mask.testBit m <;> simp [fieldBit]

lemma complex_surjectivity {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (B : Matrix κ ι ℤ)
    (hab : A.map (Int.castRingHom (ZMod 2)) * B.map (Int.castRingHom (ZMod 2)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let C := A * B
  have h2 : ((C.det : ℤ) : ZMod 2) = 1 := by
    change (Int.castRingHom (ZMod 2)) C.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show C = A * B from rfl, Matrix.map_mul, hab,
      Matrix.det_one]
  have hne : C.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at h2
    exact zero_ne_one h2
  have hu : IsUnit (C.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (C.det : ℂ) ≠ 0
    exact_mod_cast hne
  have hsurj : Function.Surjective (C.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hx

lemma surjective_of_certificate {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℤ) (cols masks : ℕ → ℕ)
    (hcols : ∀ i j, A i j = intBit ((cols j.val).testBit i.val))
    (hcheck : ∀ i : Fin d, xorColumns cols (masks i.val) m = 2 ^ i.val) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let B : Matrix (Fin m) (Fin d) ℤ := fun j i => intBit ((masks i.val).testBit j.val)
  apply complex_surjectivity A B
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc
    _ = ∑ k : Fin m, fieldBit ((cols k.val).testBit i.val) * fieldBit ((masks j.val).testBit k.val) := by
      apply Finset.sum_congr rfl
      intro k _
      change ((A i k : ℤ) : ZMod 2) * ((intBit ((masks j.val).testBit k.val) : ℤ) : ZMod 2) = _
      rw [hcols, cast_intBit, cast_intBit]
    _ = ∑ k ∈ Finset.range m, fieldBit ((cols k).testBit i.val) * fieldBit ((masks j.val).testBit k) := by
      exact Fin.sum_univ_eq_sum_range (fun k => fieldBit ((cols k).testBit i.val) *
        fieldBit ((masks j.val).testBit k)) m
    _ = fieldBit ((xorColumns cols (masks j.val) m).testBit i.val) := (xorColumns_entry _ _ _ _).symm
    _ = _ := by
      rw [hcheck j, Nat.testBit_two_pow]
      by_cases h : i = j
      · subst j; simp [fieldBit]
      · have hji : j.val ≠ i.val := fun hv => h (Fin.ext hv.symm)
        simp [h, hji, fieldBit]

end CriticalTensor.FiveGrid.Binary

namespace CriticalTensor.FiveGrid

open MvPolynomial Binary

def prodFin {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A × B ≃ Fin (a*b) :=
  (e.prodCongr f).trans finProdFinEquiv

def sumFin {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A ⊕ B ≃ Fin (a+b) :=
  (Equiv.sumCongr e f).trans finSumFinEquiv

def rowOrder (d a : ℕ) : Fin d × Fin d × Fin a ≃ Fin (d*(d*a)) :=
  prodFin (Equiv.refl _) finProdFinEquiv

def colOrder (g s d a : ℕ) :
    Columns (Fin g) (Fin a) s d ≃ Fin (g*(s*d)+(g*(s*d)+s*a)) :=
  sumFin (prodFin (Equiv.refl _) finProdFinEquiv)
    (sumFin (prodFin (Equiv.refl _) finProdFinEquiv) finProdFinEquiv)

def factorBit {g s d a : ℕ} (masks : Array ℕ) (p : Parameters (Fin g) (Fin a) s d) : ℤ :=
  let z := p.1
  let idx := ((z.1.val*g+z.2.1.val)*s+z.2.2.val)*3
  match p.2 with
  | .inl i => intBit ((masks[idx]?.getD 0).testBit i.val)
  | .inr (.inl j) => intBit ((masks[idx+1]?.getD 0).testBit j.val)
  | .inr (.inr k) => intBit ((masks[idx+2]?.getD 0).testBit k.val)

def integerMatrix {g s d a : ℕ} [NeZero g] (masks : Array ℕ) :
    Matrix (Fin d × Fin d × Fin a) (Columns (Fin g) (Fin a) s d) ℤ
  | (i,j,k), .inl (l,t,q) =>
    if q=i then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inl j)) *
      factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((l,0,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inl (l,t,q)) =>
    if q=j then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,l,t), .inl i) *
      factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,l,t), Sum.inr (.inr k)) else 0
  | (i,j,k), .inr (.inr (t,q)) =>
    if q=k then factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inl i) * factorBit (g:=g) (s:=s) (d:=d) (a:=a) masks ((0,0,t), .inr (.inl j)) else 0

lemma evaluate_integer {g s d a : ℕ} [NeZero g] (masks : Array ℕ) :
    (integerMatrix (g:=g) (s:=s) (d:=d) (a:=a) masks).map (Int.castRingHom ℂ) =
      (polynomialMatrix (W:=Fin a) (s:=s) (d:=d) (0:Fin g) 0).map
        (eval (fun p => (factorBit masks p : ℂ))) := by
  ext ⟨i,j,k⟩ z
  rcases z with ⟨l,t,h⟩|⟨l,t,h⟩|⟨t,h⟩ <;>
    simp [Matrix.map_apply,integerMatrix,polynomialMatrix,apply_ite] <;> split <;> simp_all

def reduced {g s d a : ℕ} [NeZero g] (masks : Array ℕ) :
    Matrix (Fin (d*(d*a))) (Fin (g*(s*d)+(g*(s*d)+s*a))) ℤ :=
  (integerMatrix masks).submatrix (rowOrder d a).symm (colOrder g s d a).symm

def testEntries {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℤ) (columns : ℕ → ℕ) : Bool :=
  (List.finRange n).all fun i => (List.finRange k).all fun j =>
    A i j == intBit ((columns j.val).testBit i.val)

lemma entries_of_test {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℤ) (columns : ℕ → ℕ)
    (h : testEntries A columns = true) :
    ∀ i j, A i j = intBit ((columns j.val).testBit i.val) := by
  simpa [testEntries, List.all_eq_true] using h

lemma grid_of_certificate {g s d a : ℕ} [NeZero g] (masks : Array ℕ) (cols inv : ℕ → ℕ)
    (hcols : ∀ i j, reduced (g:=g) (s:=s) (d:=d) (a:=a) masks i j =
      intBit ((cols j.val).testBit i.val))
    (hinv : ∀ i : Fin (d*(d*a)), xorColumns cols (inv i.val) (g*(s*d)+(g*(s*d)+s*a)) = 2^i.val) :
    CriticalTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
  let e := rowOrder d a
  let f := colOrder g s d a
  let M := reduced (g:=g) (s:=s) (d:=d) (a:=a) masks
  have hrank := surjective_of_certificate M cols inv hcols hinv
  apply spans_of_cell (fun p => (factorBit masks p : ℂ))
  apply (local_iff_surjective _ _ _).mpr
  rw [← evaluate_integer]
  have he : (integerMatrix masks).map (Int.castRingHom ℂ) =
      (M.map (Int.castRingHom ℂ)).submatrix e f := by
    ext i j
    simp [M, reduced, e, f, Matrix.submatrix, Matrix.map_apply]
  rw [he]
  intro T
  obtain ⟨y,hy⟩ := hrank (T ∘ e.symm)
  refine ⟨y ∘ f, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have hf : (y ∘ f) ∘ f.symm = y := by ext; simp
  rw [hf,hy]
  ext
  simp

end CriticalTensor.FiveGrid

namespace CriticalTensor.FiveGrid.Six

open CriticalTensor.FiveGrid.Binary
def masks : Array ℕ := #[
  0x2, 0x1, 0x3, 0x3, 0x6, 0x1a, 0x6, 0x3,
  0x11, 0x7, 0x5, 0x5, 0x1, 0x7, 0x7, 0x5,
  0x2, 0x1e, 0x2, 0x2, 0x18, 0x6, 0x4, 0xd,
  0x3, 0x5, 0x16, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0]

def columns : Array ℕ := #[
  0x3, 0x18000, 0xc0000000, 0x6b40, 0x35a00000, 0x1ad000000000, 0x231, 0x1188000,
  0x8c40000000, 0x300, 0x1800000, 0xc000000000, 0x3400, 0x1a000000, 0xd0000000000, 0x5816,
  0x2c0b0000, 0x160580000000, 0x18000, 0x300000, 0x6000000, 0xd001a, 0x1a00340, 0x34006800,
  0x440088000, 0x8801100000, 0x110022000000, 0x140028005, 0x28005000a0, 0x5000a001400, 0x7, 0xe0,
  0x1c00, 0x78000001e, 0xf0000003c0, 0x1e0000007800, 0x8000, 0x10000, 0x20000, 0x40000,
  0x80000, 0x2100420, 0x4200840, 0x8401080, 0x10802100, 0x21004200, 0x840108000, 0x1080210000,
  0x2100420000, 0x4200840000, 0x8401080000]

def inverse : Array ℕ := #[
  0x2404208200d86, 0x2404208200d87, 0x40000001, 0x3dac640403742, 0x19b1448403ac7, 0xd844d0498cdc, 0x30042d0200d87, 0x3d8068069815b,
  0x303129029b9dd, 0x303129029bbdd, 0xdb14d040a8ce, 0x30512d0312995, 0x3de070071815b, 0x30513d0313995, 0x30043d0201f8f, 0x1000000000,
  0x1000000002, 0x4000000000, 0x8000000000, 0x10000000000, 0x30042d0680b87, 0x30042d0600b87, 0x1840c00980da, 0x30152d0680f07,
  0x30152d0680b07, 0x30112d0612f95, 0x30112d0712f95, 0x1641401180da, 0x3175390708f4f, 0x316039061af4d, 0x28d0ff132458d, 0x28d0ff1324589,
  0xcd1db112480a, 0xcd9ff032480d, 0x28c1ff032458d, 0x1cd5d215a4e0a, 0x10d5d21524e0c, 0x1d51d711bc8d0, 0x1cc4d205a470a, 0x1cc4d205a4f0a,
  0x1c15091424e22, 0xc95c94514e0c, 0x1d310f103c8f8, 0x12406041c6da, 0x1d641d542cefa]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma entries : ∀ i : Fin 45, ∀ j : Fin 51,
    reduced (g:=2) (s:=3) (d:=3) (a:=5) masks i j =
      intBit ((columns[j.val]?.getD 0).testBit i.val) := by
  apply entries_of_test _ (fun j => columns[j]?.getD 0)
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma inverse_ok : ∀ i : Fin 45,
    xorColumns (fun j => columns[j]?.getD 0) (inverse[i.val]?.getD 0) 51 = 2^i.val := by
  decide +kernel

end CriticalTensor.FiveGrid.Six

namespace CriticalTensor.FiveGrid

theorem base_six : CriticalTensor.Spans 5 6 6 12 :=
  grid_of_certificate (g:=2) (s:=3) (d:=3) (a:=5) Six.masks
    (fun j => Six.columns[j]?.getD 0) (fun i => Six.inverse[i]?.getD 0) Six.entries Six.inverse_ok

end CriticalTensor.FiveGrid

namespace CriticalTensor.FiveGrid.TwentyOne

open CriticalTensor.FiveGrid.Binary
def masks : Array ℕ := #[
  0x3, 0x7, 0xc, 0x6, 0x1, 0x16, 0x5, 0x5,
  0x9, 0x1, 0x5, 0x8, 0x4, 0x2, 0x14, 0x1,
  0x4, 0x3, 0x2, 0x5, 0x1d, 0x6, 0x5, 0x1,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x4, 0x3, 0x15, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x6,
  0x6, 0x17, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x6, 0x2, 0x1c, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x6, 0x2, 0x6, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2, 0x6,
  0x19, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  0x0, 0x0, 0x0]

def columns : Array ℕ := #[
  0x318c, 0x18c60000, 0xc6300000000, 0x401, 0x2008000, 0x10040000000, 0x2b5, 0x15a8000,
  0xad40000000, 0x5ee0, 0x2f700000, 0x17b800000000, 0x380, 0x1c00000, 0xe000000000, 0xc0,
  0x600000, 0x3000000000, 0x6720, 0x33900000, 0x19c800000000, 0x6000c, 0xc00180, 0x18003000,
  0x5800b0000, 0xb001600000, 0x16002c000000, 0x240000009, 0x4800000120, 0x90000002400, 0x8, 0x100,
  0x2000, 0x500000000, 0xa000000000, 0x140000000000, 0x3, 0x60, 0xc00, 0xe8000,
  0x1d00000, 0x3a000000, 0x2108421, 0x4210842, 0x8421084, 0x10842108, 0x21084210]

def inverse : Array ℕ := #[
  0x47e14000124b, 0x47f14000124b, 0x42810004305a, 0x40000000, 0x60c0041249, 0x50000002018, 0x52000002018, 0x5200000a018,
  0x80000000, 0x5208000b018, 0x47e140001243, 0x47a140001243, 0x47a0c0049043, 0x100000000, 0x47c040048243, 0x10606002d30,
  0x4ff1402c1448, 0x1301c0080001, 0x5180802c305b, 0x430746241d6a, 0x10000002000, 0x5520006d90c3, 0x5520006c90c3, 0x5000802c30db,
  0x52080408018, 0x10606002d20, 0x17a14041a49b, 0x5620006490c3, 0x1181c0000083, 0x44a7c664bd60, 0x50290006118, 0x1ff5c7000923,
  0x42e998107277, 0x42e398007353, 0x42eb98107277, 0x50490006018, 0x52482418018, 0x52482438018, 0x400004000, 0x52082438018,
  0x50290006138, 0x52e82418938, 0x47c87253b243, 0x42e2f000737b, 0x47c07253b243]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma entries : ∀ i : Fin 45, ∀ j : Fin 47,
    reduced (g:=7) (s:=1) (d:=3) (a:=5) masks i j =
      intBit ((columns[j.val]?.getD 0).testBit i.val) := by
  apply entries_of_test _ (fun j => columns[j]?.getD 0)
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma inverse_ok : ∀ i : Fin 45,
    xorColumns (fun j => columns[j]?.getD 0) (inverse[i.val]?.getD 0) 47 = 2^i.val := by
  decide +kernel

end CriticalTensor.FiveGrid.TwentyOne

namespace CriticalTensor.FiveGrid

theorem base_twentyOne : CriticalTensor.Spans 5 21 21 49 :=
  grid_of_certificate (g:=7) (s:=1) (d:=3) (a:=5) TwentyOne.masks
    (fun j => TwentyOne.columns[j]?.getD 0) (fun i => TwentyOne.inverse[i]?.getD 0) TwentyOne.entries TwentyOne.inverse_ok

end CriticalTensor.FiveGrid

namespace CriticalTensor.FiveGrid.Five

open CriticalTensor.FiveGrid.Binary
def masks : Array ℕ := #[
  0x1e, 0x12, 0x11, 0x8, 0x10, 0x1f, 0x19, 0x13,
  0x1e, 0xe, 0x8, 0x10, 0x4, 0x1f, 0x2, 0x1c,
  0x17, 0x1a, 0x12, 0x1c, 0xf, 0x14, 0x2, 0xc,
  0xb, 0x9, 0x14, 0x7, 0x4, 0x6]

def columns : Array ℕ := #[
  0x1100220, 0x2200440000000, 0x4400880000000000000, 0x8801100000000000000000000, 0x11002200000000000000000000000000, 0x1f00000, 0x3e00000000000, 0x7c00000000000000000,
  0xf800000000000000000000000, 0x1f000000000000000000000000000000, 0x1e003de, 0x3c007bc000000, 0x7800f78000000000000, 0xf001ef0000000000000000000, 0x1e003de0000000000000000000000000, 0x80000,
  0x100000000000, 0x200000000000000000, 0x400000000000000000000000, 0x800000000000000000000000000000, 0x210842, 0x421084000000, 0x842108000000000000, 0x1084210000000000000000000,
  0x2108420000000000000000000000000, 0x1a06b5a, 0x340d6b4000000, 0x681ad68000000000000, 0xd035ad0000000000000000000, 0x1a06b5a0000000000000000000000000, 0xf7bc00, 0x1ef7800000000,
  0x3def000000000000000, 0x7bde000000000000000000000, 0xf7bc000000000000000000000000000, 0x180, 0x300000000, 0x600000000000000, 0xc00000000000000000000, 0x1800000000000000000000000000,
  0xa0014, 0x140028000000, 0x280050000000000000, 0x5000a0000000000000000000, 0xa00140000000000000000000000000, 0x1800, 0x3000000000, 0x6000000000000000,
  0xc000000000000000000000, 0x18000000000000000000000000000, 0x110000088000044000022000000, 0x2200001100000880000440000000, 0x44000022000011000008800000000, 0x880000440000220000110000000000, 0x11000008800004400002200000000000, 0xf8000000000000000000,
  0x1f00000000000000000000, 0x3e000000000000000000000, 0x7c0000000000000000000000, 0xf800000000000000000000000, 0x1e00000f000000000000000001e, 0x3c00001e000000000000000003c0, 0x7800003c000000000000000007800, 0xf000007800000000000000000f0000,
  0x1e00000f000000000000000001e00000, 0x80000040000020000000, 0x1000000800000400000000, 0x20000010000008000000000, 0x400000200000100000000000, 0x8000004000002000000000000, 0x8000000000000, 0x100000000000000,
  0x2000000000000000, 0x40000000000000000, 0x800000000000000000, 0x1a00000d0000068000000000000, 0x3400001a00000d00000000000000, 0x6800003400001a000000000000000, 0xd00000680000340000000000000000, 0x1a00000d000006800000000000000000,
  0xf000000000000000001e000000, 0x1e000000000000000003c0000000, 0x3c000000000000000007800000000, 0x7800000000000000000f0000000000, 0xf000000000000000001e00000000000, 0xc0000000000030000000000000, 0x1800000000000600000000000000, 0x3000000000000c000000000000000,
  0x600000000000180000000000000000, 0xc000000000003000000000000000000, 0xa0000000000028000014, 0x1400000000000500000280, 0x2800000000000a000005000, 0x5000000000001400000a0000, 0xa000000000002800001400000, 0x1800000c000006,
  0x3000001800000c0, 0x6000003000001800, 0xc0000060000030000, 0x1800000c00000600000, 0x1000200800100400080200040000000, 0x2000401000200800100400080000000, 0x4000802000401000200800100000000, 0x8001004000802000401000200000000,
  0x10002008001004000802000400000000, 0x800000000000000000000000, 0x1000000000000000000000000, 0x2000000000000000000000000, 0x4000000000000000000000000, 0x8000000000000000000000000, 0x1000210800108000000000000100021, 0x2000421000210000000000000200042,
  0x4000842000420000000000000400084, 0x8001084000840000000000000800108, 0x10002108001080000000000001000210, 0x40000020000010000000000, 0x80000040000020000000000, 0x100000080000040000000000, 0x200000100000080000000000, 0x400000200000100000000000,
  0x421084000000000000, 0x842108000000000000, 0x1084210000000000000, 0x2108420000000000000, 0x4210840000000000000, 0x1004210802108401084000000000000, 0x2008421004210802108000000000000, 0x4010842008421004210000000000000,
  0x8021084010842008420000000000000, 0x10042108021084010840000000000000, 0x1084000000000000000210800000000, 0x2108000000000000000421000000000, 0x4210000000000000000842000000000, 0x8420000000000000001084000000000, 0x10840000000000000002108000000000, 0x200000000000080000000000000,
  0x400000000000100000000000000, 0x800000000000200000000000000, 0x1000000000000400000000000000, 0x2000000000000800000000000000, 0x40008000000010002008001, 0x80010000000020004010002, 0x100020000000040008020004, 0x200040000000080010040008,
  0x400080000000100020080010, 0x1000000800000400, 0x2000001000000800, 0x4000002000001000, 0x8000004000002000, 0x10000008000004000]

def inverse : Array ℕ := #[
  0x4218d316ade2483aa482e47333b970a4aa10f, 0x2988801184e0020020c04008a0f00b70154a, 0x4218cc450802d06a24a0e4700f196bfa2dcce, 0x4230100310ad400a230205701a9a21a20f744, 0x2a85447010e904025ace4009f864aef25f18, 0x4220849301474cc011926718fad9133468a6d, 0x21385542154b010091908a6188aa8ee0f976d, 0x219198533d0715fa452c0a0a6c4cc56cfca23,
  0x219198533d0715fa452c0a0a6c4c456cfca23, 0x618085d40448d940843c0879e55f573be546b, 0x60001c07b9e004c80210e4402e001960439c0, 0x80010000000021004000a0000a001400, 0x8001000000002100400080000a001400, 0x40988c1519a94150309ee00bda956b61bf542, 0x281c5510a5013a3192e47b48aa4974e1694, 0x3b0415594ea4cc8a73c8029f11c00084a2d1,
  0x40018000000002004003200032506400, 0x40b09802090c402a010c0070908f2115003d6, 0x989c94304c04ba349e6c6bd77f49ed2715c, 0x8000, 0x40a0d09610ecd84035ae83186dff59db1a6fe, 0x23a0d1430505012091ac8e613aa58dd3ff227, 0x2339cc562c0985fa6290ee0afb6a8c038e53b, 0x23391c522c03115a66920f0ade4945dffc93b,
  0x6300d1d115e34dc0a000ec7972791dd4978f9, 0x4000571591cad87a9408c06b81587393dba06, 0x40288040396edc82011e6000883b00151b44a, 0x40b0c55021264498d714a07b71f7480188c0c, 0x409845120843405ad68ac07bf95c4813dc058, 0x4000491211cad87ad40ac06bc1584b93dcbda, 0x40a0d0961103d84015a4c008edfd59db1c306, 0x10000001ce000000000010800b0000002d6,
  0x89cd11284c147ad5b4c26be4e4cb8c05d4e, 0x89cd11284c147ad5b4c26be4e5cb8c05d4e, 0x4028d09610c3d84015a4c0086dfd59db1c20e, 0x2890538109003a71ace01aeca551cca008a, 0x4000080010000000020004000a0000a001400, 0x4000080010000000020004000e0000a001400, 0x981c1431e5449832b0840b569a6ab9bda9c, 0x2898540109003a31aee01beca56a4ca714a,
  0x989911a84c04fab4be6069e5cf4a4c6155c, 0xb0884028ecdca2031e6410823f00b71a3d6, 0xb08c4230ec9ce2031e6010b08f0392447d6, 0x409888d211acd862368c000bc57f6853ad15c, 0x10000, 0x4038998610ccd87ac12e00732c3f124f8fb5c, 0x880000004c002000000000800f00000014a, 0x8984012986144003be0200252c839896694,
  0x898401280a146003be02002523839896694, 0x40b09986110cd87ac12e0073ac3f124f8fa56, 0x4018000211e4d84030822008409a0007499c6, 0x400000000000000000, 0x4018015408044050f0a2200b7cda2359bf1c2, 0x40a8d110092d4050f580c01b51bd6a81ea9d4, 0xa899540108003af1ae207beca5024cc7214, 0x40a8d09610cdd84035acc0186dff59db1c1d0,
  0x800000000000000000, 0x30000001ce10800100421080098000002d6, 0x30000001ce108001004210800b8000002d6, 0x40309986110dd87a012c4073ac3f5a4f8f808, 0x40288c5438e904f273bc045ac2a548ace394a, 0x1000000000000000000, 0x1000000800000000000, 0x4098001409e5405030a2600b749a6bd9be29c,
  0x28985400e9003a31ae607beca54a4ce714a, 0xb08c4628ecdcb2833e6452823f00abaa3d6, 0x2000000000000000000, 0x40b09800090c406a010c0070903f2115583d6, 0x18000000000002000000000008420000, 0x20000, 0x4028d096112cd840f5ac80186dff11db1c28a, 0x3c00000000000400000,
  0x98991400c610baf0be626b64ec824ce70c2, 0xd00401061080c402e200a52c81dc7499e, 0x40b0998610ecd87ac12c0073ac3f124f8fb56, 0x184910002e003a1488c063c1c2039491a0e, 0x40b00c403920dca203126000303403871c500, 0xa8c406292204c827b6a0700dcd6b5847dce, 0xa8511000ee00101588c00bd1c62294d1b0e, 0x40a8d04610c2d84025a4c0102dfd49df1b9ce,
  0x184910000e003a1488c07bc1c2039493b0e, 0x1c00000000000100004000000108, 0xa84910000e003a1588c06bc1c8039493b0e, 0xa84910000e003a1588c06bc1cc039493b0e, 0x18491001ce003a1488c07bc1c2039493a06, 0x4000091739e004f23212643b6e0a6af4d011e, 0x40008401104c0000002c0400b20f0338067de, 0x40008401104c0000002c0400a20f0338067de,
  0x40000917380004f23212647b7e0a4af49011e, 0x1e00000000000600000200040000, 0x28155700a0d8483780043b67f04ae7cb68a, 0xb0884128ecdca2033e6410823f00b71a3d6, 0x4000144039e0dc880212606020b022871c400, 0x4098895611acd86236ac000bc57f68d78d15c, 0x40000, 0x200000000000000000000000000,
  0x400000000000000000000000000, 0x800000000000000000000000000, 0x1000000000000000000000000000, 0x1e00000000000000000000000100, 0x40988713b848dcba80bc406ba49f3a4bdac92, 0x4028004038a0dc8201166010083000071b69c, 0x40b08c4220e844a2031e4010b0df03956c7d6, 0x40005c0621c144a0063ca0009db84a4d39fc0,
  0x409899143848dcba30be406be49f4a4bd955c, 0x40a0d09610cdd84035acc0186dff59db1c1d0, 0x10000000000000000800000000000000000, 0x10000001ce10800100421080098000002d6, 0x10000001ce10800100421080018000002d6, 0x40b09986110dd87a012c4073ac3f5a4f8f808, 0x280052a94504fa3192001a48aa5014a2f54, 0x40008c01104c0000023c04008a0f00b8017de,
  0x40008c01104c0000023c0400aa0f00b8017de, 0x988c1519a94058328e640bd6956b61bf542, 0x281542294504c00190006008a023803178a, 0x800000000000000200000000f0000, 0xb08c4128ecdca2031e6410823f00ab1a3d6, 0x28155618a0981833a0007b554049de3528a, 0x40988cd611acd862328c000bc57f684f4d15c, 0x80000,
  0x40a0d09610ccd84035ae80186dff59db1c1de, 0x88000000000020003c00000000000400294, 0x109914018610ba333c626b64ecc9cce7016, 0x88d004004610a00780e200a52cca5c7494a, 0x40b09986110cd87a012e0073ac3f5a4f8f816]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma entries : ∀ i : Fin 125, ∀ j : Fin 150,
    reduced (g:=1) (s:=10) (d:=5) (a:=5) masks i j =
      intBit ((columns[j.val]?.getD 0).testBit i.val) := by
  apply entries_of_test _ (fun j => columns[j]?.getD 0)
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
lemma inverse_ok : ∀ i : Fin 125,
    xorColumns (fun j => columns[j]?.getD 0) (inverse[i.val]?.getD 0) 150 = 2^i.val := by
  decide +kernel

end CriticalTensor.FiveGrid.Five

namespace CriticalTensor.FiveGrid

theorem base_five : CriticalTensor.Spans 5 5 5 10 :=
  grid_of_certificate (g:=1) (s:=10) (d:=5) (a:=5) Five.masks
    (fun j => Five.columns[j]?.getD 0) (fun i => Five.inverse[i]?.getD 0) Five.entries Five.inverse_ok

end CriticalTensor.FiveGrid

namespace CriticalTensor.FiveBorder

def outsideOnly {D : Type} (f : Fin 2 → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim f (fun _ => 0)
def insideOnly {D : Type} (f : D → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim (fun _ => 0) f
def edge {D : Type} : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → Prop
  | Sum.inr _, Sum.inr _ => False
  | _, _ => True
def delta {X : Type} [DecidableEq X] (x y : X) : ℂ := if x=y then 1 else 0

def Holds {D W X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (a b : X → (Fin 2 ⊕ D) → ℂ) (c : X → W → ℂ)
    (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → (Fin 2 ⊕ D) → ℂ) : Prop :=
  ∀ T : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → W → ℂ,
    ∃ u v : X → (Fin 2 ⊕ D) → ℂ, ∃ w : X → W → ℂ,
      ∃ ui vi : N → Fin 2 → ℂ, ∃ wq : Q → W → ℂ, ∀ i j k, edge i j →
        T i j k =
          (∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) + a t i * (b t j * w t k))) +
          (∑ t, (outsideOnly (ui t) i * (insideOnly (bi t) j * ci t k) +
            insideOnly (ai t) i * (outsideOnly (vi t) j * ci t k))) +
          ∑ t, aq t i * (bq t j * wq t k)

/-- The exterior part of one group of slices. The points in X have three
free factors. Points in N lie in the inner block, and those in Q contribute
only their third-factor variations to this pencil. -/
def PencilFor (D W X N Q : Type) [Fintype X] [Fintype N] [Fintype Q] : Prop :=
  ∃ a b : X → (Fin 2 ⊕ D) → ℂ, ∃ c : X → W → ℂ,
    ∃ ai bi : N → D → ℂ, ∃ ci : N → W → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ, Holds a b c ai bi ci aq bq

end CriticalTensor.FiveBorder

namespace CriticalTensor.FiveBorder

lemma pencil_transport {D W X N Q E Y S R : Type} [Fintype X] [Fintype N] [Fintype Q]
    [Fintype Y] [Fintype S] [Fintype R] (ed : E ≃ D) (ex : Y ≃ X) (en : S ≃ N) (eq : R ≃ Q)
    (h : PencilFor D W X N Q) : PencilFor E W Y S R := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hs⟩ := h
  let ez := Equiv.sumCongr (Equiv.refl (Fin 2)) ed
  have ho (f : Fin 2 → ℂ) (i : Fin 2 ⊕ E) : outsideOnly f (ez i) = outsideOnly f i := by
    cases i <;> rfl
  have hi (f : D → ℂ) (i : Fin 2 ⊕ E) :
      insideOnly f (ez i) = insideOnly (fun s => f (ed s)) i := by cases i <;> rfl
  refine ⟨fun y i => a (ex y) (ez i),fun y i => b (ex y) (ez i),fun y => c (ex y),
    fun z i => ai (en z) (ed i),fun z i => bi (en z) (ed i),fun z => ci (en z),
    fun z i => aq (eq z) (ez i),fun z i => bq (eq z) (ez i),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hs fun i j k => T (ez.symm i) (ez.symm j) k
  refine ⟨fun t i => u (ex t) (ez i),fun t j => v (ex t) (ez j),fun t => w (ex t),
    fun t => ui (en t),fun t => vi (en t),fun t => wq (eq t),?_⟩
  intro i j k he
  have hh : edge (ez i) (ez j) := by cases i <;> cases j <;> exact he
  have hT := hT (ez i) (ez j) k hh
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hT
  rw [hT]
  congr 1
  · congr 1
    · exact (ex.sum_comp (fun z => u z (ez i) * (b z (ez j) * c z k) +
        a z (ez i) * (v z (ez j) * c z k) + a z (ez i) * (b z (ez j) * w z k))).symm
    · have hsum := en.sum_comp (fun z => outsideOnly (ui z) (ez i) * (insideOnly (bi z) (ez j) * ci z k) +
        insideOnly (ai z) (ez i) * (outsideOnly (vi z) (ez j) * ci z k))
      simpa only [ho,hi] using hsum.symm
  · exact (eq.sum_comp (fun z => aq z (ez i) * (bq z (ez j) * wq z k))).symm

end CriticalTensor.FiveBorder

namespace CriticalTensor.FiveBorder.Pencils

abbrev Coord (D : Type) := Fin 2 ⊕ D
abbrev Rows (D W : Type) := {z : Coord D × Coord D × W // edge z.1 z.2.1}
abbrev Cols (D W X N Q : Type) :=
  (X × (Coord D ⊕ (Coord D ⊕ W))) ⊕ ((N × (Fin 2 ⊕ Fin 2)) ⊕ (Q × W))

def matrix {D W X N Q K : Type} [CommRing K] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → K) (c : X → W → K)
    (ai bi : N → D → K) (ci : N → W → K) (aq bq : Q → Coord D → K) :
    Matrix (Rows D W) (Cols D W X N Q) K
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inl h) => if h=i then b t j * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inl h)) => if h=j then a t i * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inr h)) => if h=k then a t i * b t j else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inl h)) =>
      if Sum.inl h=i then j.elim (fun _ => 0) (bi t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inr h)) =>
      if Sum.inl h=j then i.elim (fun _ => 0) (ai t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inr (t,h)) => if h=k then aq t i * bq t j else 0

lemma action {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) (y : Cols D W X N Q → ℂ) (i j : Coord D) (k : W) (e : edge i j) :
    (matrix a b c ai bi ci aq bq).mulVec y ⟨(i,j,k),e⟩ =
      (∑ t, (y (Sum.inl (t,Sum.inl i)) * (b t j * c t k) +
        a t i * (y (Sum.inl (t,Sum.inr (Sum.inl j))) * c t k) +
        a t i * (b t j * y (Sum.inl (t,Sum.inr (Sum.inr k)))))) +
      (∑ t, (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inl h)))) i * (insideOnly (bi t) j * ci t k) +
        insideOnly (ai t) i * (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inr h)))) j * ci t k))) +
      ∑ t, aq t i * (bq t j * y (Sum.inr (Sum.inr (t,k)))) := by
  change (∑ z : Cols D W X N Q, matrix a b c ai bi ci aq bq ⟨(i,j,k),e⟩ z * y z) = _
  cases i <;> cases j <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, matrix, outsideOnly, insideOnly, ite_mul,
      Finset.sum_ite_eq', Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, add_assoc]

lemma holds_iff {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) :
    Holds a b c ai bi ci aq bq ↔ Function.Surjective (matrix a b c ai bi ci aq bq).mulVec := by
  classical
  constructor
  · intro hh T
    let lift (i j : Coord D) (k : W) := if e : edge i j then T ⟨(i,j,k),e⟩ else 0
    obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hh lift
    let y : Cols D W X N Q → ℂ := Sum.elim (fun z => z.2.elim (u z.1) (Sum.elim (v z.1) (w z.1)))
      (Sum.elim (fun z => z.2.elim (ui z.1) (vi z.1)) (fun z => wq z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨⟨i,j,k⟩,e⟩ := z
    exact ((action a b c ai bi ci aq bq y i j k e).trans (hT i j k e).symm).trans (dif_pos e)
  · intro hh T
    obtain ⟨y,hy⟩ := hh fun z => T z.1.1 z.1.2.1 z.1.2.2
    refine ⟨fun t i => y (Sum.inl (t,Sum.inl i)),fun t j => y (Sum.inl (t,Sum.inr (Sum.inl j))),
      fun t k => y (Sum.inl (t,Sum.inr (Sum.inr k))),fun t i => y (Sum.inr (Sum.inl (t,Sum.inl i))),
      fun t j => y (Sum.inr (Sum.inl (t,Sum.inr j))),fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
    intro i j k e
    exact (congrFun hy ⟨(i,j,k),e⟩).symm.trans (action a b c ai bi ci aq bq y i j k e)

end CriticalTensor.FiveBorder.Pencils


namespace CriticalTensor.FiveBorder.Tiles

/-- The exterior parts of the active points are prescribed so that the same
points can serve an arbitrarily large number of independent interior rows. -/
def Anchored {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (A B : X → Fin 2 → ℂ) (C : X → Wh → ℂ) : Prop :=
  ∃ ax bx : X → D → ℂ, ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ,
      Holds (fun t => Sum.elim (A t) (ax t)) (fun t => Sum.elim (B t) (bx t)) C ai bi ci aq bq

def Limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (O : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) (a : N → D → ℂ) (ci : N → Wh → ℂ) (b : V → D → ℂ) (f : V → Fin 2 → ℂ) : Prop :=
  ∀ T : D → Fin 2 → Wh → ℂ, ∃ u₀ : X → D → ℂ, ∃ u : N → Fin 2 → ℂ, ∃ v : V → Wh → ℂ,
    ∀ i j k, T i j k =
      (∑ t, u₀ t i * (O t j * C t k)) + (∑ t, a t i * (u t j * ci t k)) +
      ∑ t, b t i * (f t j * v t k)

def Paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (A B : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) : Prop :=
  ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ, ∃ aq bq : V → D → ℂ, ∃ f g : V → Fin 2 → ℂ,
    Limb B C ai ci aq f ∧ Limb A C bi ci bq g

lemma to_pencil {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (h : Anchored (D:=D) (N:=N) (Q:=Q) A B C) :
    PencilFor D Wh X N Q := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := h
  exact ⟨_,_,C,ai,bi,ci,aq,bq,hs⟩

lemma repeat_limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {O : X → Fin 2 → ℂ} {C : X → Wh → ℂ} {a : N → D → ℂ} {ci : N → Wh → ℂ}
    {b : V → D → ℂ} {f : V → Fin 2 → ℂ} (L : Type) [Fintype L] [DecidableEq L] (h : Limb O C a ci b f) :
    Limb O C (fun (z : L×N) (i : L×D) => if z.1=i.1 then a z.2 i.2 else 0) (fun z => ci z.2)
      (fun (z : L×V) (i : L×D) => if z.1=i.1 then b z.2 i.2 else 0) (fun z => f z.2) := by
  classical
  intro T
  choose u₀ u v hv using fun l : L => h fun i j k => T (l,i) j k
  refine ⟨fun t i => u₀ i.1 t i.2,fun t => u t.1 t.2,fun t => v t.1 t.2,?_⟩
  rintro ⟨l,i⟩ j k
  simpa [Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using hv l i j k

lemma repeat_paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (L : Type) [Fintype L] [DecidableEq L]
    (h : Paired (D:=D) (N:=N) (V:=V) A B C) : Paired (D:=L×D) (N:=L×N) (V:=L×V) A B C := by
  obtain ⟨ai,bi,ci,aq,bq,f,g,ha,hb⟩ := h
  exact ⟨_,_,_,_,_,_,_,repeat_limb L ha,repeat_limb L hb⟩

lemma append {D E Wh X N Q M V : Type} [Fintype X] [Fintype N] [Fintype Q] [Fintype M] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ}
    (base : Anchored (D:=D) (N:=N) (Q:=Q) A B C) (arms : Paired (D:=E) (N:=M) (V:=V) A B C) :
    Anchored (D:=D⊕E) (N:=N⊕M) (Q:=Q⊕(V⊕V)) A B C := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := base
  obtain ⟨al,bl,cl,rl,sl,f,g,hl,hr⟩ := arms
  let lower (z : Fin 2 ⊕ D) : Fin 2 ⊕ (D⊕E) := z.elim Sum.inl (fun i => Sum.inr (Sum.inl i))
  let extend (t : (Fin 2⊕D) → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun j => t (Sum.inl j)) (Sum.elim (fun j => t (Sum.inr j)) (fun _ => 0))
  let eg (v : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ := insideOnly (Sum.elim (fun _ => 0) v)
  refine ⟨fun t => Sum.elim (ax t) (fun _ => 0),fun t => Sum.elim (bx t) (fun _ => 0),
    Sum.elim (fun t => Sum.elim (ai t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (al t)),
    Sum.elim (fun t => Sum.elim (bi t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (bl t)),Sum.elim ci cl,
    Sum.elim (fun t => extend (aq t)) (Sum.elim (fun t => eg (rl t)) (fun t => outsideOnly (g t))),
    Sum.elim (fun t => extend (bq t)) (Sum.elim (fun t => outsideOnly (f t)) (fun t => eg (sl t))),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hb⟩ := hs fun i j k => T (lower i) (lower j) k
  obtain ⟨y,l,t,hy⟩ := hl fun i j k => T (Sum.inr (Sum.inr i)) (Sum.inl j) k
  obtain ⟨z,r,s,hz⟩ := hr fun j i k => T (Sum.inl i) (Sum.inr (Sum.inr j)) k
  let join (v : (Fin 2⊕D) → ℂ) (r : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun i => v (Sum.inl i)) (Sum.elim (fun i => v (Sum.inr i)) r)
  refine ⟨fun t => join (u t) (y t),fun t => join (v t) (z t),w,Sum.elim ui r,Sum.elim vi l,
    Sum.elim wq (Sum.elim t s),?_⟩
  rintro (i|i) (j|j) k he
  · simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inl j) k (by trivial))
  · cases j with
    | inl j => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inr j) k (by trivial))
    | inr j => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type,mul_comm,mul_assoc,mul_left_comm] using hz j i k
  · cases i with
    | inl i => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inr i) (Sum.inl j) k (by trivial))
    | inr i => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using hy i j k
  · exact False.elim he

end CriticalTensor.FiveBorder.Tiles


namespace CriticalTensor.FiveBorder.Seven

/-- A digit of a row of a nonnegative integer matrix in the given binary width. -/
def digit (a : Array ℕ) (bits i j : ℕ) : ℕ := (a[i]?.getD 0 >>> (bits*j)) % 2^bits

def dot (a b : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => dot a b i j k + a i k * b k j

def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => allBelow p n && p n

lemma allBelow_iff (p : ℕ → Bool) (n : ℕ) :
    allBelow p n = true ↔ ∀ i<n, p i=true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨h,k⟩ i hi
      by_cases he : i=n
      · simpa [he] using k
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma dot_fin (a b : ℕ → ℕ → ℕ) (i j n : ℕ) :
    dot a b i j n = ∑ t : Fin n, a i t.val * b t.val j := by
  induction n with
  | zero => simp [dot]
  | succ n ih => rw [dot,Fin.sum_univ_castSucc,ih]; rfl

def valid (a b : ℕ → ℕ → ℕ) (m : ℕ) :=
  allBelow (fun i => allBelow (fun j => dot a b i j m % 7 == (if i=j then 1 else 0)) m) m

lemma valid_entry {a b : ℕ → ℕ → ℕ} {m : ℕ} (hv : valid a b m = true) (i j : Fin m) :
    dot a b i.val j.val m % 7 = (if i=j then 1 else 0) := by
  obtain h := (allBelow_iff _ _).mp ((allBelow_iff _ _).mp hv i.val i.isLt) j.val j.isLt
  simpa [Fin.ext_iff] using (beq_iff_eq.mp h)

lemma lift_rank {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I K ℤ) (B : Matrix K I ℤ)
    (hab : A.map (Int.castRingHom (ZMod 7)) * B.map (Int.castRingHom (ZMod 7)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let D := A*B
  have h7 : ((D.det : ℤ) : ZMod 7) = 1 := by
    change (Int.castRingHom (ZMod 7)) D.det = 1
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show D=A*B from rfl,Matrix.map_mul,hab,Matrix.det_one]
  have hn : D.det≠0 := by
    intro he
    rw [he, Int.cast_zero] at h7
    exact (by decide : (0 : ZMod 7) ≠ 1) h7
  have hu : IsUnit (D.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    change (D.det : ℂ) ≠ 0
    exact_mod_cast hn
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨z,hz⟩ := hs y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hz

lemma certified {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] {m : ℕ}
    (M : Matrix I K ℤ) (rows : I ≃ Fin m) (sel : Fin m → K) (a b : ℕ → ℕ → ℕ)
    (ha : ∀ i j : Fin m, M (rows.symm i) (sel j) = (a i.val j.val : ℤ))
    (hv : valid a b m = true) : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  let A : Matrix I (Fin m) ℤ := fun i j => M i (sel j)
  let B : Matrix (Fin m) I ℤ := fun t i => b t.val (rows i).val
  have hA (i : I) (t : Fin m) : A i t = (a (rows i).val t.val : ℤ) := by
    simpa only [A,Equiv.symm_apply_apply] using ha (rows i) t
  have mod7 : A.map (Int.castRingHom (ZMod 7)) * B.map (Int.castRingHom (ZMod 7)) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ t : Fin m, ((A i t : ℤ) : ZMod 7) * (((b t.val (rows j).val : ℕ) : ℤ) : ZMod 7)) = _
    simp only [hA,Int.cast_natCast]
    have H := congrArg (fun t : ℕ => (t : ZMod 7)) (valid_entry hv (rows i) (rows j))
    simpa only [ZMod.natCast_mod,dot_fin,Nat.cast_sum,Nat.cast_mul,Equiv.apply_eq_iff_eq,
      apply_ite,Nat.cast_one,Nat.cast_zero] using H
  have hsmall := lift_rank A B mod7
  let E : Matrix K (Fin m) ℂ := fun k i => if k=sel i then 1 else 0
  have hcols : M.map (Int.castRingHom ℂ) * E = A.map (Int.castRingHom ℂ) := by
    ext i t
    rw [Matrix.mul_apply]
    change (∑ k : K, ((M i k : ℤ) : ℂ) * (if k=sel t then 1 else 0)) = ((M i (sel t) : ℤ) : ℂ)
    simp [mul_ite,Finset.sum_ite_eq']
  intro y
  obtain ⟨z,hz⟩ := hsmall y
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,hcols]
  exact hz

def prodFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A×B ≃ Fin (a*b) :=
  (ea.prodCongr eb).trans finProdFinEquiv
def sumFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A⊕B ≃ Fin (a+b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

/-- Row order is the two outer rows followed by the two outer columns in
each interior row. The third index varies fastest. -/
def rowEquiv (d w : ℕ) : Pencils.Rows (Fin d) (Fin w) ≃ Fin (2*((2+d)*w)+d*(2*w)) :=
  let e : Pencils.Rows (Fin d) (Fin w) ≃ (Fin 2 × Pencils.Coord (Fin d) × Fin w) ⊕ (Fin d × Fin 2 × Fin w) :=
    { toFun := fun z => match z with
        | ⟨(Sum.inl i,j,k),_⟩ => Sum.inl (i,j,k)
        | ⟨(Sum.inr i,Sum.inl j,k),_⟩ => Sum.inr (i,j,k)
        | ⟨(Sum.inr _,Sum.inr _,_),h⟩ => False.elim h
      invFun := Sum.elim (fun z => ⟨(Sum.inl z.1,z.2.1,z.2.2),by cases z.2.1 <;> trivial⟩)
        (fun z => ⟨(Sum.inr z.1,Sum.inl z.2.1,z.2.2),by trivial⟩)
      left_inv := by rintro ⟨⟨i,j,k⟩,h⟩; cases i <;> cases j <;> first | rfl | exact False.elim h
      right_inv := by rintro (⟨i,j,k⟩|⟨i,j,k⟩) <;> rfl }
  e.trans (sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv (Equiv.refl _)))
    (prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))))

def colEquiv (d w x n q : ℕ) : Pencils.Cols (Fin d) (Fin w) (Fin x) (Fin n) (Fin q) ≃
    Fin (x*((2+d)+((2+d)+w))+(n*(2+2)+q*w)) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv (Equiv.refl _))))
    (sumFin (prodFin (Equiv.refl _) finSumFinEquiv) (prodFin (Equiv.refl _) (Equiv.refl _)))

end CriticalTensor.FiveBorder.Seven


namespace CriticalTensor.FiveBorder.Seven

open CriticalTensor.FiveBorder.Pencils CriticalTensor.FiveBorder.Tiles

def table {m n : ℕ} (v : Array ℕ) (i : Fin m) (j : Fin n) : ℤ := (v[i.val*n+j.val]?.getD 0 : ℕ)
def outA {x : ℕ} (t : Fin x) (i : Fin 2) : ℤ := if i=0 then 1 else (t.val+1 : ℕ)
def outB {x : ℕ} (t : Fin x) (i : Fin 2) : ℤ := if i=0 then 1 else (#[1,2,4,3][t.val]?.getD 0 : ℕ)
def basisC {x w : ℕ} (t : Fin x) (k : Fin w) : ℤ := if t.val=k.val then 1 else 0

def Room (d w x n q : ℕ) : Prop :=
  Anchored (D:=Fin d) (N:=Fin n) (Q:=Fin q) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

def Wing (d w x n v : ℕ) : Prop :=
  Paired (D:=Fin d) (N:=Fin n) (V:=Fin v) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

lemma pencil_cast {D Wh X N Q : Type} [DecidableEq D] [DecidableEq Wh]
    (a b : X → Coord D → ℤ) (c : X → Wh → ℤ) (ai bi : N → D → ℤ) (ci : N → Wh → ℤ)
    (aq bq : Q → Coord D → ℤ) :
    (Pencils.matrix a b c ai bi ci aq bq).map (Int.castRingHom ℂ) =
      Pencils.matrix (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ))
        (fun t i => (ai t i : ℂ)) (fun t i => (bi t i : ℂ)) (fun t i => (ci t i : ℂ))
        (fun t i => (aq t i : ℂ)) (fun t i => (bq t i : ℂ)) := by
  ext ⟨⟨i,j,h⟩,hz⟩ z
  rcases z with ⟨t,e|e|e⟩ | ⟨t,e|e⟩ | ⟨t,e⟩ <;> cases i <;> cases j <;>
    simp only [Pencils.matrix, Matrix.map_apply, Sum.elim_inl,Sum.elim_inr] <;> split <;> simp

lemma certified_room {d w x n q : ℕ} (ax bx : Fin x → Fin d → ℤ)
    (ai bi : Fin n → Fin d → ℤ) (ci : Fin n → Fin w → ℤ) (aq bq : Fin q → Coord (Fin d) → ℤ)
    (h : Function.Surjective ((Pencils.matrix (fun t => Sum.elim (outA t) (ax t))
      (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq).map (Int.castRingHom ℂ)).mulVec) :
    Room d w x n q := by
  classical
  refine ⟨fun t i => ax t i,fun t i => bx t i,fun t i => ai t i,fun t i => bi t i,
    fun t k => ci t k,fun t i => aq t i,fun t i => bq t i,?_⟩
  apply (holds_iff _ _ _ _ _ _ _ _).mpr
  rw [pencil_cast] at h
  have he (a : Fin 2 → ℤ) (b : Fin d → ℤ) :
      (fun i => ((Sum.elim a b i : ℤ) : ℂ)) = Sum.elim (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
    funext i
    cases i <;> rfl
  have hOut (op : Fin x → Fin 2 → ℤ) (ip : Fin x → Fin d → ℤ) :
      (fun t i => ((Sum.elim (op t) (ip t) i : ℤ) : ℂ)) =
        (fun t => Sum.elim (fun i => (op t i : ℂ)) (fun i => (ip t i : ℂ))) := by
    funext t
    exact he (op t) (ip t)
  rw [hOut outA ax,hOut outB bx] at h
  exact h

abbrev ArmCols (D Wh X N V : Type) := (X × D) ⊕ ((N × Fin 2) ⊕ (V × Wh))
def armMatrix {D Wh X N V : Type} [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ) :
    Matrix (D × Fin 2 × Wh) (ArmCols D Wh X N V) ℤ
  | (i,j,k),Sum.inl (t,h) => if h=i then O t j*C t k else 0
  | (i,j,k),Sum.inr (Sum.inl (t,h)) => if h=j then a t i*ci t k else 0
  | (i,j,k),Sum.inr (Sum.inr (t,h)) => if h=k then b t i*f t j else 0

lemma certified_limb {D Wh X N V : Type} [Fintype D] [Fintype Wh] [Fintype X] [Fintype N] [Fintype V]
    [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ)
    (h : Function.Surjective ((armMatrix O C a ci b f).map (Int.castRingHom ℂ)).mulVec) :
    Limb (fun t i => (O t i : ℂ)) (fun t k => (C t k : ℂ)) (fun t i => (a t i : ℂ))
      (fun t k => (ci t k : ℂ)) (fun t i => (b t i : ℂ)) (fun t j => (f t j : ℂ)) := by
  intro T
  obtain ⟨y,hy⟩ := h fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t i => y (Sum.inl (t,i)),fun t j => y (Sum.inr (Sum.inl (t,j))),
    fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : ArmCols D Wh X N V, ((armMatrix O C a ci b f (i,j,k) z : ℤ) : ℂ) * y z) = _
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,armMatrix,apply_ite,Finset.sum_ite_eq',
    mul_comm,mul_assoc,add_assoc]

def armRows (d w : ℕ) : Fin d × Fin 2 × Fin w ≃ Fin (d*(2*w)) :=
  prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))
def armCols (d w x n v : ℕ) : ArmCols (Fin d) (Fin w) (Fin x) (Fin n) (Fin v) ≃ Fin (x*d+(n*2+v*w)) :=
  sumFin (prodFin (Equiv.refl _) (Equiv.refl _)) (sumFin (prodFin (Equiv.refl _) (Equiv.refl _))
    (prodFin (Equiv.refl _) (Equiv.refl _)))

end CriticalTensor.FiveBorder.Seven


namespace CriticalTensor.FiveBorder.Seven
def window (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => window f start n && f (start+n)

def Before (f : ℕ → Bool) (b : ℕ) := ∀ i < b, f i = true

lemma before_zero (f : ℕ → Bool) : Before f 0 := fun _ h => by omega

lemma extend {f : ℕ → Bool} {b n : ℕ} (earlier : Before f b) (h : window f b n = true) :
    Before f (b+n) := by
  induction n with
  | zero => simpa using earlier
  | succ n ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    by_cases h' : i < b+n
    · exact ih h₁ i h'
    · have he : i=b+n := by omega
      exact he ▸ h₂

structure RowWindow (f : ℕ → Bool) (n : ℕ) : Type where
  verified : Before f n

def start (f : ℕ → Bool) : RowWindow f 0 := ⟨before_zero f⟩

def nextWindow {f : ℕ → Bool} {b : ℕ} (prev : RowWindow f b) (n : ℕ)
    (h : window f b n = true) : RowWindow f (b+n) := ⟨extend prev.verified h⟩

end CriticalTensor.FiveBorder.Seven

namespace CriticalTensor.FiveBorder.Seven

open CriticalTensor.FiveBorder.Pencils CriticalTensor.FiveBorder.Tiles

namespace RoomTwo

def ax : Fin 5 → Fin 2 → ℤ := table #[3, 4, 3, 3, 5, 0, 1, 6, 5, 4]
def bx : Fin 5 → Fin 2 → ℤ := table #[5, 5, 1, 0, 3, 5, 1, 5, 4, 0]
def ai : Fin 2 → Fin 2 → ℤ := table #[5, 4, 6, 4]
def bi : Fin 2 → Fin 2 → ℤ := table #[3, 1, 2, 1]
def ci : Fin 2 → Fin 5 → ℤ := table #[6, 5, 6, 4, 0, 4, 0, 5, 0, 4]
def aq (t : Fin 0) (j : Coord (Fin 2)) : ℤ := table #[] t (finSumFinEquiv j)
def bq (t : Fin 0) (j : Coord (Fin 2)) : ℤ := table #[] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 2) (Fin 5)) (Cols (Fin 2) (Fin 5) (Fin 5) (Fin 2) (Fin 0)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x1000000000000000000000100000000000000000000010000000000000000000001000000000000000000000000000100000001,
  0x100000000000000000000010000000000000000000001000000000000000000000000000001000000010000000100000000000000,
  0x10000000000000000000001000000000000000000000000000000010000000100000100000000000000000000010000000000000000,
  0x1000000000000000000000000000000000100000001000100000000000000000000010000000000000000000001000000000000000000,
  0x1000000010100000000000000000000010000000000000000000001000000000000000000000100000000000000000000,
  0x300000000000000000000040000000000000000000002000000000000000000000000010000000001,
  0x30000000000000000000004000000000000000000000000000100000000020000000100000000000000,
  0x3000000000000000000000000000001000000000400000200000000000000000000010000000000000000,
  0x10000000003000400000000000000000000020000000000000000000001000000000000000000,
  0x100000000000300000000000000000000040000000000000000000002000000000000000000000100000000000000000000,
  0x80000001200000004000000000000000000000100000000000000000000030000000000000000000001000000000000000000000001000000000005,
  0xf00000400000000000000000000010000000000000000000003000000000000000000000000000000000000010000000500000000000000,
  0xa0000001200040000000000000000000001000000000000000000000000000100000000000300000100000000000000000000050000000000000000,
  0xc04000000000000000000000000000001000000000001000300000000000000000000010000000000000000000005000000000000000000,
  0x80000000000000000000000000000040100000000000000000000030000000000000000000001000000000000000000000500000000000000000000,
  0x40000000600000000000000000000000000000500000000000000000000050000000000000000000000000000000000000000000000000000000005,
  0x500000000000000000000000000050000000000000000000005000000000000000000000000010000000000000000000500000000000000,
  0x50000000600000000000000000000000005000000000000000000000000000000000000000500000000000000000000000000050000000000000000,
  0x400000000000000000000000000000000000000000005000500000000000000000000000000000000000000000005000000000000000000,
  0x40000000000000000010000000000000500000000000000000000050000000000000000000000000000000000000000000500000000000000000000,
  0x5000000000000000000000400000000000000000000030000000000000000000002000000000000000000000000000100000100,
  0x500000000000000000000040000000000000000000003000000000000000000000000000002000001000000000100000000000000,
  0x50000000000000000000004000000000000000000000000000000030000010000000200000000000000000000010000000000000000,
  0x5000000000000000000000000000000000400000100000300000000000000000000020000000000000000000001000000000000000000,
  0x5000001000400000000000000000000030000000000000000000002000000000000000000000100000000000000000000,
  0xc000000000000000000000c0000000000000000000004000000000000000000000000010000000100,
  0xc000000000000000000000c000000000000000000000000000200000002000000000100000000000000,
  0xc000000000000000000000000000003000000040000000400000000000000000000010000000000000000,
  0x40000000300000c00000000000000000000040000000000000000000001000000000000000000,
  0x500000000000c000000000000000000000c0000000000000000000004000000000000000000000100000000000000000000,
  0x120000000014000000000000000000000400000000000000000000090000000000000000000002000000000000000000000001000000000500,
  0xf0000001400000000000000000000040000000000000000000009000000000000000000000000000000000001000000000500000000000000,
  0x120000140000000000000000000004000000000000000000000000000300000000030000000200000000000000000000050000000000000000,
  0xc0014000000000000000000000000000004000000000100000900000000000000000000020000000000000000000005000000000000000000,
  0x4000400000000000000000000090000000000000000000002000000000000000000000500000000000000000000,
  0x600000000000000000000000000000014000000000000000000000f0000000000000000000000000000000000000000000000000000000500,
  0x5000000000000000000000000000014000000000000000000000f000000000000000000000000020000000000000000000500000000000000,
  0x60000000000000000000000000014000000000000000000000000000000000000050000000000000000000000000000050000000000000000,
  0x40000000000000000000000000000000000000000000500000f00000000000000000000000000000000000000000005000000000000000000,
  0x500000000000014000000000000000000000f0000000000000000000000000000000000000000000500000000000000000000,
  0x1e000000000005000000000000000000000100000000000000000000050000000000000000000003000000000000000000000000000300010000,
  0x19000000000500000000000000000000010000000000000000000005000000000000000000000000000003000100000000000300000000000000,
  0x1e000000050000000000000000000001000000000000000000000000000000050001000000000300000000000000000000030000000000000000,
  0x14000005000000000000000000000000000000000100010000000500000000000000000000030000000000000000000003000000000000000000,
  0x5000100000100000000000000000000050000000000000000000003000000000000000000000300000000000000000000,
  0x1e00000000000000000000000000000000000300000000000000000000140000000000000000000006000000000000000000000000030000010000,
  0x1900000000000000000000000000000000030000000000000000000014000000000000000000000000000300000200000000000300000000000000,
  0x1e00000000000000000000000000000003000000000000000000000000000005000004000000000600000000000000000000030000000000000000,
  0x1400000000000000000000000000000000000000010000030000001400000000000000000000060000000000000000000003000000000000000000,
  0x500000000000300000000000000000000140000000000000000000006000000000000000000000300000000000000000000,
  0x18000000000004000000000000000000000600000000000000000000000000000000000000000003000000000000000000000000000401000000,
  0x14000000000400000000000000000000060000000000000000000000000000000000000000000000000003010000000000000400000000000000,
  0x18000000040000000000000000000006000000000000000000000000000000000100000000000300000000000000000000040000000000000000,
  0x10000004000000000000000000000000000000000601000000000000000000000000000000030000000000000000000004000000000000000000,
  0x4010000000600000000000000000000000000000000000000000003000000000000000000000400000000000000000000,
  0x1800000000000000000000000000000000001200000000000000000000000000000000000000000006000000000000000000000000040001000000,
  0x1400000000000000000000000000000000120000000000000000000000000000000000000000000000000300020000000000000400000000000000,
  0x1800000000000000000000000000000012000000000000000000000000000000000400000000000600000000000000000000040000000000000000,
  0x1000000000000000000000000000000000000000060003000000000000000000000000000000060000000000000000000004000000000000000000,
  0x400000000001200000000000000000000000000000000000000000006000000000000000000000400000000000000000000]
def rightInverse : Array ℕ := #[
  0x2160065104610024500544601015005400225101264030520340404222,
  0x304560054162555011423616064055403644144064423550421510612434,
  0x504230053430526001325011530025203162043030454600324010640446,
  0x604420056656544031636412455045103211346355431310622110026416,
  0x602040060356602034056440355002105051320555201310052140126204,
  0x2010060606603034040440505006005060320205206010010140306204,
  0x305150015266113033543434665016402424355165560510521130416520,
  0x300001001033040140306402025000050405602023060320603001053,
  0x101000030023304052031260326302600026530126304445055460053204,
  0x304200053061524041333111364022433124343163454550351110015444,
  0x600000000050000000001000030000500002000020000600003000040000,
  0x106600042024453025441554421005601056260621663430125352054633,
  0x205600012042122013352630544021502515153444502150563531032502,
  0x403400026016241036064466615024304643330215321210636166066331,
  0x106600043026446035611452125063601336362525636410545156056646,
  0x601300031053364052236222356052106221515156134340352424023134,
  0x502500064031640044605343032020205202421032210660104645041230,
  0x502500064034622024355544531021205012225431202630364340044242,
  0x606540044351452045456356452052101651464052623360452650121631,
  0x504000050036301032065410635504206042350235401616034120046301,
  0x522100165031612044555544534011255412525431262650564240045222,
  0x10000000006000040000400005000050000100003000030000,
  0x502300061032232016155665534331205512141434642655164530042062,
  0x605200013055620064306151053020105101653053150320302240025040,
  0x2300061003533052140255406035002550521606043040120440003563,
  0x306300051060430005103035060630402504011060540503101020010060,
  0x100400006021342042651352522341606216456422332465665620051412,
  0x504200053034621024365501631024206142243231251630334320044341,
  0x302100065064612024553544561211406414265461062532561310014422,
  0x2430066405644064630142203042005200626103235020650240405212,
  0x200003004065020220500201026000360206301005030310305004015,
  0x364200353066524031333011362022443124043160454560351510010444,
  0x40000000005000010000000003000030000200001000060000,
  0x611500434052352012456526555051106611514454122310462620024132,
  0x532500564032656014415246134053265632424534226650444540042236,
  0x166200343022420025301351020020651106563025650400305550052640,
  0x300101000036000110205106033020530601503046040140600005066,
  0x512000460031601044065040633004265042020234201620034440041201,
  0x641100235052315012526224250016166461015354165300512020021125,
  0x255600612046165033222033246066552365052344515150213030033555,
  0x306550044261454045433356562054401644464062622560431650611634,
  0x3052050450206506031000010504406022040160406003012,
  0x200000000045402065052110543101506015630443402124063240035102,
  0x600000000040000000006000040000600005000050000100003000030000,
  0x600000000020000000000000060000600004000000000000006000010000,
  0x400000000030000000003000040000500006000060000400000000050000,
  0x300000000030000100003000040000200005000060000400005000050000,
  0x500001000030000000000000030000200002000000000000004000000000,
  0x300000000050000000003000030000000002000060000400005000050000,
  0x400000000000000000005000010000400003000030000200000000060000,
  0x500000000020000000005000060000600004000040000500003000010000,
  0x603660022154262026256563151066104301232051316330212360524352,
  0x6034030130403305022000220301105014010350101006024,
  0x4603024040520401605005050210601103033020340004503,
  0x641400236053341052666322653044136241116252131320632320020111,
  0x601100035051315042526324252016106461415352165360512620021125,
  0x502300061030634004135045330032205522021130244600154040040264,
  0x502600062035662064255143533061205312622433212620264240045252,
  0x304300051063534051133215366032403524541166444540151410013464,
  0x300000000060000000003000060000400004000060000500001000010000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69]
def pick (t : Fin 60) := (colEquiv 2 5 5 2 0).symm (Fin.ofNat 73 (pivots[t.val]?.getD 0))
private def checkRow (i : ℕ) :=
  allBelow (fun j => decide (M ((rowEquiv 2 5).symm (Fin.ofNat 60 i)) (pick (Fin.ofNat 60 j)) = (digit original 8 i j : ℤ))) 60 &&
  allBelow (fun j => dot (digit original 8) (digit rightInverse 4) i j 60 % 7 == (if i=j then 1 else 0)) 60
private def w2 : RowWindow checkRow 2 := nextWindow (start checkRow) 2 (by decide +kernel)
private def w4 : RowWindow checkRow 4 := nextWindow w2 2 (by decide +kernel)
private def w6 : RowWindow checkRow 6 := nextWindow w4 2 (by decide +kernel)
private def w8 : RowWindow checkRow 8 := nextWindow w6 2 (by decide +kernel)
private def w10 : RowWindow checkRow 10 := nextWindow w8 2 (by decide +kernel)
private def w12 : RowWindow checkRow 12 := nextWindow w10 2 (by decide +kernel)
private def w14 : RowWindow checkRow 14 := nextWindow w12 2 (by decide +kernel)
private def w16 : RowWindow checkRow 16 := nextWindow w14 2 (by decide +kernel)
private def w18 : RowWindow checkRow 18 := nextWindow w16 2 (by decide +kernel)
private def w20 : RowWindow checkRow 20 := nextWindow w18 2 (by decide +kernel)
private def w22 : RowWindow checkRow 22 := nextWindow w20 2 (by decide +kernel)
private def w24 : RowWindow checkRow 24 := nextWindow w22 2 (by decide +kernel)
private def w26 : RowWindow checkRow 26 := nextWindow w24 2 (by decide +kernel)
private def w28 : RowWindow checkRow 28 := nextWindow w26 2 (by decide +kernel)
private def w30 : RowWindow checkRow 30 := nextWindow w28 2 (by decide +kernel)
private def w32 : RowWindow checkRow 32 := nextWindow w30 2 (by decide +kernel)
private def w34 : RowWindow checkRow 34 := nextWindow w32 2 (by decide +kernel)
private def w36 : RowWindow checkRow 36 := nextWindow w34 2 (by decide +kernel)
private def w38 : RowWindow checkRow 38 := nextWindow w36 2 (by decide +kernel)
private def w40 : RowWindow checkRow 40 := nextWindow w38 2 (by decide +kernel)
private def w42 : RowWindow checkRow 42 := nextWindow w40 2 (by decide +kernel)
private def w44 : RowWindow checkRow 44 := nextWindow w42 2 (by decide +kernel)
private def w46 : RowWindow checkRow 46 := nextWindow w44 2 (by decide +kernel)
private def w48 : RowWindow checkRow 48 := nextWindow w46 2 (by decide +kernel)
private def w50 : RowWindow checkRow 50 := nextWindow w48 2 (by decide +kernel)
private def w52 : RowWindow checkRow 52 := nextWindow w50 2 (by decide +kernel)
private def w54 : RowWindow checkRow 54 := nextWindow w52 2 (by decide +kernel)
private def w56 : RowWindow checkRow 56 := nextWindow w54 2 (by decide +kernel)
private def w58 : RowWindow checkRow 58 := nextWindow w56 2 (by decide +kernel)
private def w60 : RowWindow checkRow 60 := nextWindow w58 2 (by decide +kernel)
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  apply certified M (rowEquiv 2 5) pick (digit original 8) (digit rightInverse 4)
  · intro i j
    have h := (allBelow_iff _ _).mp (Bool.and_eq_true_iff.mp (w60.verified i.val i.isLt)).1 j.val j.isLt
    have hi : Fin.ofNat 60 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hj : Fin.ofNat 60 j.val=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa only [decide_eq_true_eq,hi,hj] using h
  · apply (allBelow_iff _ _).mpr
    intro i hi
    exact (Bool.and_eq_true_iff.mp (w60.verified i hi)).2

lemma spans : Room 2 5 5 2 0 := certified_room ax bx ai bi ci aq bq rank

end RoomTwo

namespace RoomThree

def ax : Fin 5 → Fin 3 → ℤ := table #[5, 5, 1, 0, 2, 2, 3, 6, 6, 2, 6, 1, 0, 2, 6]
def bx : Fin 5 → Fin 3 → ℤ := table #[3, 1, 0, 0, 2, 5, 3, 1, 4, 4, 2, 0, 0, 4, 1]
def ai : Fin 4 → Fin 3 → ℤ := table #[5, 0, 4, 5, 0, 0, 4, 6, 3, 0, 3, 2]
def bi : Fin 4 → Fin 3 → ℤ := table #[4, 2, 6, 4, 4, 6, 4, 6, 6, 3, 2, 0]
def ci : Fin 4 → Fin 5 → ℤ := table #[6, 4, 5, 6, 3, 2, 6, 5, 5, 0, 0, 2, 1, 2, 2, 3, 3, 0, 1, 2]
def aq (t : Fin 0) (j : Coord (Fin 3)) : ℤ := table #[] t (finSumFinEquiv j)
def bq (t : Fin 0) (j : Coord (Fin 3)) : ℤ := table #[] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 3) (Fin 5)) (Cols (Fin 3) (Fin 5) (Fin 5) (Fin 4) (Fin 0)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x100000000000000000000000001000000000000000000000000010000000000000000000000000100000000000000000000000000000000010000000001,
  0x10000000000000000000000000100000000000000000000000001000000000000000000000000000000000001000000000100000001000000000000000000,
  0x1000000000000000000000000010000000000000000000000000000000000000100000000010000010000000000000000000000000100000000000000000000,
  0x100000000000000000000000000000000000000010000000001000100000000000000000000000001000000000000000000000000010000000000000000000000,
  0x1000000000101000000000000000000000000010000000000000000000000000100000000000000000000000001000000000000000000000000,
  0x3000000000000000000000000040000000000000000000000000200000000000000000000000000000001000000000001,
  0x300000000000000000000000004000000000000000000000000000000000100000000000200000001000000000000000000,
  0x30000000000000000000000000000000000010000000000040000020000000000000000000000000100000000000000000000,
  0x1000000000003000400000000000000000000000002000000000000000000000000010000000000000000000000,
  0x100000000000003000000000000000000000000040000000000000000000000000200000000000000000000000001000000000000000000000000,
  0x90000000000000008000000180000000000000000000000000000000004000000000000000000000000030000000000000000000000000000000000000000000000000000000100000000000003,
  0x90000000800000018000000100000000000000000000000000000000400000000000000000000000003000000000000000000000000000000010000000000000000000003000000000000000000,
  0x400000014000000140000000000000000000000000000040000000000000000000000000000000001000000000000030000000000000000000000000000000300000000000000000000,
  0x30000000800000014000000180000000000000000000000000000000000000100000000000004000300000000000000000000000000000000000000000000000000030000000000000000000000,
  0x600000008000000000000000c0000000000010000000000000004000000000000000000000000030000000000000000000000000000000000000000000000000003000000000000000000000000,
  0x600000000000000080000000c0000000400000000000000000000000002000000000000000000000000010000000000000000000000000200000000000000000000000000000000000000000001,
  0x60000000c00000018000000080000040000000000000000000000000200000000000000000000000001000000000000000000000000000001000000000000000200000001000000000000000000,
  0x6000000140000000a0004000000000000000000000000020000000000000000000000000000000100000000000000010000020000000000000000000000000100000000000000000000,
  0x20000000c000000140000000c0400000000000000000000000000000000000000000000000002000100000000000000000000000002000000000000000000000000010000000000000000000000,
  0x40000000c00000000000000060000000001000000000000000402000000000000000000000000010000000000000000000000000200000000000000000000000001000000000000000000000000,
  0xc000000240000000100000000000000000000000000000000000000000000000000040000000000000000000000000500000000000000000000000000010000000000000000,
  0xc00000024000000180000010000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000500000000000000000000000000,
  0x60000001e0000001e0001000000000000000000000000000000000000000000000000000000000000000000000000040000050000000000000000000000000000000000000000000000,
  0xc0000001e000000240100000000000000000000000000000000010000000000000000000400000000000000000000000005000000000000000000000000000000000000000000000000,
  0xc00000000000000120000000000000000000000000100000000000000000000000000040000000000000000000000000500000000000000000000000000000000000000000000000000,
  0x500000000000000000000000004000000000000000000000000030000000000000000000000000200000000000000000000000000000000010000000100,
  0x50000000000000000000000000400000000000000000000000003000000000000000000000000000000000002000000010000000001000000000000000000,
  0x5000000000000000000000000040000000000000000000000000000000000000300000001000000020000000000000000000000000100000000000000000000,
  0x500000000000000000000000000000000000000040000000100000300000000000000000000000002000000000000000000000000010000000000000000000000,
  0x5000000010004000000000000000000000000030000000000000000000000000200000000000000000000000001000000000000000000000000,
  0xc0000000000000000000000000c0000000000000000000000000400000000000000000000000000000001000000000100,
  0xc0000000000000000000000000c000000000000000000000000000000000200000000020000000001000000000000000000,
  0xc0000000000000000000000000000000000030000000004000000040000000000000000000000000100000000000000000000,
  0x4000000000300000c00000000000000000000000004000000000000000000000000010000000000000000000000,
  0x50000000000000c0000000000000000000000000c0000000000000000000000000400000000000000000000000001000000000000000000000000,
  0x9000000000000000800000018000000000000000000000000000000000010000000000000000000000000090000000000000000000000000000000000000000000000000000000100000000000300,
  0x9000000080000001800000010000000000000000000000000000000001000000000000000000000000009000000000000000000000000000000020000000000000000000003000000000000000000,
  0x40000001400000014000000000000000000000000000000100000000000000000000000000000000003000000000003000000000000000000000000000000000300000000000000000000,
  0x3000000080000001400000018000000000000000000000000000000000000000400000000000400000900000000000000000000000000000000000000000000000000030000000000000000000000,
  0x600000008000000000000000c000000000000050000000000000010000000000000000000000000090000000000000000000000000000000000000000000000000003000000000000000000000000,
  0x600000000000000080000000c000000001400000000000000000000000008000000000000000000000000030000000000000000000000000400000000000000000000000000000000000000000100,
  0x60000000c0000001800000008000000140000000000000000000000000800000000000000000000000003000000000000000000000000000002000000000000020000000001000000000000000000,
  0x6000000140000000a000014000000000000000000000000080000000000000000000000000000000300000000000001000000040000000000000000000000000100000000000000000000,
  0x20000000c000000140000000c001400000000000000000000000000000000000000000000000200000300000000000000000000000004000000000000000000000000010000000000000000000000,
  0x40000000c0000000000000006000000000005000000000000040008000000000000000000000000030000000000000000000000000400000000000000000000000001000000000000000000000000,
  0xc000000240000000005000000000000000000000000000000000000000000000000000c0000000000000000000000000a00000000000000000000000000010000000000000000,
  0xc000000240000001800000005000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000050000000000000000000000000000,
  0x60000001e0000001e0000050000000000000000000000000000000000000000000000000000000000000000000000040000000a0000000000000000000000000000000000000000000000,
  0xc0000001e00000024000500000000000000000000000000000000040000000000000000000c0000000000000000000000000a000000000000000000000000000000000000000000000000,
  0xc00000000000000120000000000000000000000000100000000000000000000000000000c0000000000000000000000000a00000000000000000000000000000000000000000000000000,
  0xa0000001e00000000000000000000000000000000000002000000000000000000000000030000000000000000000000000000000000000000000000000000000000050000010000,
  0x80000001e0000001400000000000000000000000000000000000200000000000000000000000003000000000000000000000000000000000000000001000000000005000000000000000000,
  0x4000000190000001900000000000000000000000000000000020000000000000000000000000000000000000300000100000000000000000000000000000000000500000000000000000000,
  0x8000000190000001e00000000000000000000000000000000000000000000020000010000000300000000000000000000000000000000000000000000000000050000000000000000000000,
  0x8000000000000000f00000000000000000000000001000002000000000000000000000000030000000000000000000000000000000000000000000000000005000000000000000000000000,
  0xa0000001e00000000000000000000000000000000000000060000000000000000000000000c0000000000000000000000000000000000000000000000000000000005000000010000,
  0x80000001e00000014000000000000000000000000000000000000060000000000000000000000000c000000000000000000000000000000000000000002000000000005000000000000000000,
  0x400000019000000190000000000000000000000000000000000060000000000000000000000000000000000030000000400000000000000000000000000000000000500000000000000000000,
  0x8000000190000001e0000000000000000000000000000000000000000000002000000030000000c00000000000000000000000000000000000000000000000000050000000000000000000000,
  0x8000000000000000f00000000000000000000000000000000060000000000000000000000000c0000000000000000000000000000000000000000000000000005000000000000000000000000,
  0x200000000000000000000000006000000000000000000000000060000000000000000000000000200000000000000000000000000000000050001000000,
  0xc000000000000000000000000020000000000000000000000000600000000000000000000000006000000000000000000000000000000000002000100000000000005000000000000000000,
  0x6000000000000000000000002000000000000000000000000060000000000000000000000000000000000000600010000000000020000000000000000000000000500000000000000000000,
  0xc000000000000000000000200000000000000000000000000000000000000060001000000000600000000000000000000000002000000000000000000000000050000000000000000000000,
  0xc000000000000000000000000000000000002000100000006000000000000000000000000060000000000000000000000000200000000000000000000000005000000000000000000000000,
  0x900000000000000000000000000000000000000000000000000000000000012000000000000000000000000180000000000000000000000000400000000000000000000000000000005000001000000,
  0x900000c00000000000000000000000000000000000000000000000000001200000000000000000000000018000000000000000000000000000000000200000200000000000005000000000000000000,
  0x600000000000000000000000000000000000000000000000000120000000000000000000000000000000000060000040000000000040000000000000000000000000500000000000000000000,
  0x300000c00000000000000000000000000000000000000000000000000000000000006000003000000001800000000000000000000000004000000000000000000000000050000000000000000000000,
  0x600000c00000000000000000000000000000000000200000000000012000000000000000000000000180000000000000000000000000400000000000000000000000005000000000000000000000000,
  0x1800000000000600000000000000000000000001000000000000000000000000060000000000000000000000000200000000000000000000000000000000010100000000,
  0x6000000000000001000000000060000000000000000000000000100000000000000000000000006000000000000000000000000000000000002010000000000000001000000000000000000,
  0x3000000000000001400000006000000000000000000000000010000000000000000000000000000000000000601000000000000020000000000000000000000000100000000000000000000,
  0x6000000000000001800000600000000000000000000000000000000000000010100000000000600000000000000000000000002000000000000000000000000010000000000000000000000,
  0x6000000000000000c00000000000000000006010000000001000000000000000000000000060000000000000000000000000200000000000000000000000001000000000000000000000000,
  0x600000000000000000000180000000000000000000000000000000000000003000000000000000000000000180000000000000000000000000400000000000000000000000000000001000100000000,
  0x600000600000000000000100000000000000000000000000000000000000300000000000000000000000018000000000000000000000000000000000200020000000000000001000000000000000000,
  0x300000000000000140000000000000000000000000000000000030000000000000000000000000000000000060004000000000000040000000000000000000000000100000000000000000000,
  0x200000600000000000000180000000000000000000000000000000000000000000001000300000000001800000000000000000000000004000000000000000000000000010000000000000000000000,
  0x4000006000000000000000c0000000000000000000600000000000003000000000000000000000000180000000000000000000000000400000000000000000000000001000000000000000000000000]
def rightInverse : Array ℕ := #[
  0x22035010126363405413563020320565242633201342132241544335116552531222363251633044,
  0x56503031040464002460315130415446025150611155156020636241403221020236461032350550,
  0x51643044644420602601025210113024231462416245156525340154511614164562460362661000,
  0x43141053665663303415213600422024322223443256124444443234553546561666265606112631,
  0x65514061543463602411350120605534053004114414004265406316504400250154600151015130,
  0x35641064661465202445641610232610153516556403266564065262044433341550156215103544,
  0x61136043113110204305345300211034654046264021104125412206534305330101560454116412,
  0x20306002015102504032011440436352310262342316512014154153655044110424231501124264,
  0x44316022515662403433533550524242551413620604301140161431664013525040641640522446,
  0x55120063300555506142600000000063530351035006134031360005261061404300264561264404,
  0x41021040360365405443124340151366413563215663442426203125425434536343135433246154,
  0x34234026130346405523231320531530105420516226116212253216040216046561265441641045,
  0x41212046551525506642433550524226564255461543021205424434462341661212106132615120,
  0x22535011123400402003314050450204525511025643502036132550566233405342123602022123,
  0x55013060541322205635361560334143345461435163515326146441255214464333125144025044,
  0x60025000322263401413561630333426266316545614153025004524412163343344665630402433,
  0x63225056322655003150526500144021664316565231452132056314331363341365535501004564,
  0x51326042415654003160113600422053022300232131252041445643202560034435555261013332,
  0x34562021251626403623214050450231144030543654445252441236343302043646632131015332,
  0x12604014033115004340630240503334444363154431050665604146520364552155505030650246,
  0x42130013101601303054003310021633123526153522435506536256243436352611431556234051,
  0x12362012252431102256566330341403425430101634556156516600224212060245620164035221,
  0x40452005455621203655631320531500053041426435544466062450004405465555422554004323,
  0x11020040306554006160625420116532366565252545403261515336652134632412433254333440,
  0x66036030111420202605326500144036342114303532110150066646456523210615366125501405,
  0x60521001363141604551603310021605421004016312404350040110123600206524330655602030,
  0x31632044154425402643031320531541122353103254554004556221363561550666625255633402,
  0x33424055333246401523325420116562525216313452100312034315653243316656364253603255,
  0x65626064314051200155611650442253043541525600413366311013266435445340030263263455,
  0x43106053013006500122262640362321160341622561435314060534322065425413534000100006,
  0x36554032432200101006346450246261330625466240546235555625331056661562020625332314,
  0x13155053426244301564355660612110411353065442421230163332005661501352330654622425,
  0x43422055351624303664620650102201154213324246162526653030334343515162260565154234,
  0x33515051521431502252116210443601650422414324003120536560344016166122601116035151,
  0x63220056306443102516511440436321615122550333433155133364315226242025130101525005,
  0x34025020326054300164544220253554402302166254433233441603520560151566634413216452,
  0x36200036000520506602233550524235561435556441416200224246162612642552535430646134,
  0x11401045066501606051150120605522414440100346611164353264625315050022215410465300,
  0x45353062444434402263211440436332426344625461015304636616623165225353505513254530,
  0x22234016131001400053105540014310224003066564505263605642013304501513620621256245,
  0x45656064414122504632231320531526231641146050062103210404411650453506001320545166,
  0x21031040163333505212562150465260106466623316211526612505040115325624255035653602,
  0x51655044425250402103524340151331302152035143305052062406350524104332142561200553,
  0x5144003631052100136525420116511555434626343623500410512364216225522112042211104,
  0x41146043615216001320633550524205603062556261540620012010130400142563522234405152,
  0x32433015146461502452610360401111635614625303003031350242331255225320105330461255,
  0x42666014210365405443534630552441104315311615663124505451340361616254412442431611,
  0x1353042445256001120322110165622034315243150365611005004001363633636042554502521,
  0x3460055202460202405313600422021635123455312043344130454331226562324304161025325,
  0x20120003304506306024365250313200101113012156531021356340040623506436220301161351,
  0x26051030462034400263351200633002235210551360343544653230611243042223046062350544,
  0x4506021013404102066356040640310560165216001663246202032062024636500516625542420,
  0x50230006106353105116433550524206651240143221626512616641434645053661514140355455,
  0x44202026055121304654562640362313521453034565653132534550263611504113414126335314,
  0x65224066332420202605564101355031556260264426522312314456364144031151226041560602,
  0x56102033050563616411626500144031323442461465001002213361353415161253405531124065,
  0x43531151165204401063106620042501564535235400044205112166362332634350002420636454,
  0x24432025154404402063225420116512402623100016532644343421620556550004220266603062,
  0x32331012163060600401264100355044565435125150244263161531562212655336056553124220,
  0x66224036332601403053163020320521205106214034134042125214310220336205661000620615,
  0x12331012165604503062045300211025345153406502624460104230156231560510312142225132,
  0x20011000561431102256332400566004146646534515213553452220546155344114452030510644,
  0x64010020506354005160535010510621463114460431233314111254322423261055550222523220,
  0x32045010623016600321145300211003014350445130161166241310205361063335062043140466,
  0x50510001501000500002116210443651503515020402302215342553360433605050343423064414,
  0x60414005532155604141200000000005156101501334304630344150144120440225642653162111,
  0x64634024131100404003653430626456611366600505365106421463435664320010442211413245,
  0x34416025514503606011440530204421434100356346502153133454321320012522222613222314,
  0x2146013615001100056124340151332140401515104655616226336646010446330610262543500,
  0x13343052644314605361216210443653124121625026066665560103243326425301205230633023,
  0x60032000150551306154352350661233434525626123153036541236221336625531162460136154,
  0x6640034601062500432640110205645133024125325365465345651141406255321443104065054,
  0x25460065202332605231165510314613533365143162635211145252261464653633314103625302,
  0x63316052515041400553404460056165246236554545533052002265116142342112422620502041,
  0x55044060635045400543450120605505645505616624132422155610136230626541661566624435,
  0x15051060466201201055141610232624001412200553615102350314500613130016115412366541,
  0x20013000541130404203143140225310146031326365003634612312046102415523400246253450,
  0x31456045412520606601331320531566001651066533341456522405400651401515140151435354,
  0x16605034022326605621544220253506213420421566553420520440415416065213220555434226,
  0x25241066662661603451100000000011425354023356231303132432323261205626254464126450]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 90]
def pick (t : Fin 80) := (colEquiv 3 5 5 4 0).symm (Fin.ofNat 91 (pivots[t.val]?.getD 0))
private def checkRow (i : ℕ) :=
  allBelow (fun j => decide (M ((rowEquiv 3 5).symm (Fin.ofNat 80 i)) (pick (Fin.ofNat 80 j)) = (digit original 8 i j : ℤ))) 80 &&
  allBelow (fun j => dot (digit original 8) (digit rightInverse 4) i j 80 % 7 == (if i=j then 1 else 0)) 80
private def w2 : RowWindow checkRow 2 := nextWindow (start checkRow) 2 (by decide +kernel)
private def w4 : RowWindow checkRow 4 := nextWindow w2 2 (by decide +kernel)
private def w6 : RowWindow checkRow 6 := nextWindow w4 2 (by decide +kernel)
private def w8 : RowWindow checkRow 8 := nextWindow w6 2 (by decide +kernel)
private def w10 : RowWindow checkRow 10 := nextWindow w8 2 (by decide +kernel)
private def w12 : RowWindow checkRow 12 := nextWindow w10 2 (by decide +kernel)
private def w14 : RowWindow checkRow 14 := nextWindow w12 2 (by decide +kernel)
private def w16 : RowWindow checkRow 16 := nextWindow w14 2 (by decide +kernel)
private def w18 : RowWindow checkRow 18 := nextWindow w16 2 (by decide +kernel)
private def w20 : RowWindow checkRow 20 := nextWindow w18 2 (by decide +kernel)
private def w22 : RowWindow checkRow 22 := nextWindow w20 2 (by decide +kernel)
private def w24 : RowWindow checkRow 24 := nextWindow w22 2 (by decide +kernel)
private def w26 : RowWindow checkRow 26 := nextWindow w24 2 (by decide +kernel)
private def w28 : RowWindow checkRow 28 := nextWindow w26 2 (by decide +kernel)
private def w30 : RowWindow checkRow 30 := nextWindow w28 2 (by decide +kernel)
private def w32 : RowWindow checkRow 32 := nextWindow w30 2 (by decide +kernel)
private def w34 : RowWindow checkRow 34 := nextWindow w32 2 (by decide +kernel)
private def w36 : RowWindow checkRow 36 := nextWindow w34 2 (by decide +kernel)
private def w38 : RowWindow checkRow 38 := nextWindow w36 2 (by decide +kernel)
private def w40 : RowWindow checkRow 40 := nextWindow w38 2 (by decide +kernel)
private def w42 : RowWindow checkRow 42 := nextWindow w40 2 (by decide +kernel)
private def w44 : RowWindow checkRow 44 := nextWindow w42 2 (by decide +kernel)
private def w46 : RowWindow checkRow 46 := nextWindow w44 2 (by decide +kernel)
private def w48 : RowWindow checkRow 48 := nextWindow w46 2 (by decide +kernel)
private def w50 : RowWindow checkRow 50 := nextWindow w48 2 (by decide +kernel)
private def w52 : RowWindow checkRow 52 := nextWindow w50 2 (by decide +kernel)
private def w54 : RowWindow checkRow 54 := nextWindow w52 2 (by decide +kernel)
private def w56 : RowWindow checkRow 56 := nextWindow w54 2 (by decide +kernel)
private def w58 : RowWindow checkRow 58 := nextWindow w56 2 (by decide +kernel)
private def w60 : RowWindow checkRow 60 := nextWindow w58 2 (by decide +kernel)
private def w62 : RowWindow checkRow 62 := nextWindow w60 2 (by decide +kernel)
private def w64 : RowWindow checkRow 64 := nextWindow w62 2 (by decide +kernel)
private def w66 : RowWindow checkRow 66 := nextWindow w64 2 (by decide +kernel)
private def w68 : RowWindow checkRow 68 := nextWindow w66 2 (by decide +kernel)
private def w70 : RowWindow checkRow 70 := nextWindow w68 2 (by decide +kernel)
private def w72 : RowWindow checkRow 72 := nextWindow w70 2 (by decide +kernel)
private def w74 : RowWindow checkRow 74 := nextWindow w72 2 (by decide +kernel)
private def w76 : RowWindow checkRow 76 := nextWindow w74 2 (by decide +kernel)
private def w78 : RowWindow checkRow 78 := nextWindow w76 2 (by decide +kernel)
private def w80 : RowWindow checkRow 80 := nextWindow w78 2 (by decide +kernel)
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  apply certified M (rowEquiv 3 5) pick (digit original 8) (digit rightInverse 4)
  · intro i j
    have h := (allBelow_iff _ _).mp (Bool.and_eq_true_iff.mp (w80.verified i.val i.isLt)).1 j.val j.isLt
    have hi : Fin.ofNat 80 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hj : Fin.ofNat 80 j.val=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa only [decide_eq_true_eq,hi,hj] using h
  · apply (allBelow_iff _ _).mpr
    intro i hi
    exact (Bool.and_eq_true_iff.mp (w80.verified i hi)).2

lemma spans : Room 3 5 5 4 0 := certified_room ax bx ai bi ci aq bq rank

end RoomThree

namespace Pair

def ai : Fin 5 → Fin 2 → ℤ := table #[1, 2, 6, 0, 0, 4, 5, 5, 0, 4]
def bi : Fin 5 → Fin 2 → ℤ := table #[5, 1, 5, 4, 6, 5, 1, 2, 2, 0]
def ci : Fin 5 → Fin 5 → ℤ := table #[4, 3, 6, 1, 5, 3, 3, 3, 5, 0, 0, 6, 6, 4, 1, 3, 1, 3, 3, 0, 4, 5, 0, 4, 6]
def aq : Fin 0 → Fin 2 → ℤ := table #[]
def bq : Fin 0 → Fin 2 → ℤ := table #[]
def f : Fin 0 → Fin 2 → ℤ := table #[]
def g : Fin 0 → Fin 2 → ℤ := table #[]

namespace Left
def M : Matrix (Fin 2 × Fin 2 × Fin 5) (ArmCols (Fin 2) (Fin 5) (Fin 5) (Fin 5) (Fin 0)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0xf00000012000400000000000000000001,
  0x500000012000300000000000000010000,
  0xf00000012000600000000000100000000,
  0xf0000001e000100000001000000000000,
  0x500010000000000000000,
  0xf0000001200040000000000000000000001,
  0x50000001200030000000000000000020000,
  0xf0000001200060000000000000400000000,
  0xf0000001e00010000000003000000000000,
  0x50000000000000000000000,
  0x10000f00000000000800000000000000000100,
  0x14000500180000000600000000000001000000,
  0xf00180000000c00000000010000000000,
  0x10000f00100000000200000100000000000000,
  0x18000000040000000a01000000000000000000,
  0x10000f0000000000080000000000000000000100,
  0x1400050018000000060000000000000002000000,
  0xf00180000000c0000000000040000000000,
  0x10000f0010000000020000000300000000000000,
  0x18000000040000000a0000000000000000000000]
def rightInverse : Array ℕ := #[
  0x25106063010566306425,
  0x1220046311643403513,
  0x25106063010665003450,
  0x53556051511353105116,
  0x43205056022305405143,
  0x50666005215403202015,
  0x16403035040032201235,
  0x20360012203410402303,
  0x52601014065261611451,
  0x43540151602205101046,
  0x61304042036134304264,
  0x3000000000,
  0x16403035045316205325,
  0x43205056026450202105,
  0x30555001423403202015,
  0x41063040245445302544,
  0x52601014065063500412,
  0x34502021056021400653,
  0x55561061261042100536,
  0x21063040242445302544]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def pick (t : Fin 20) := (armCols 2 5 5 5 0).symm (Fin.ofNat 20 (pivots[t.val]?.getD 0))
private def checkRow (i : ℕ) :=
  allBelow (fun j => decide (M ((armRows 2 5).symm (Fin.ofNat 20 i)) (pick (Fin.ofNat 20 j)) = (digit original 8 i j : ℤ))) 20 &&
  allBelow (fun j => dot (digit original 8) (digit rightInverse 4) i j 20 % 7 == (if i=j then 1 else 0)) 20
private def w2 : RowWindow checkRow 2 := nextWindow (start checkRow) 2 (by decide +kernel)
private def w4 : RowWindow checkRow 4 := nextWindow w2 2 (by decide +kernel)
private def w6 : RowWindow checkRow 6 := nextWindow w4 2 (by decide +kernel)
private def w8 : RowWindow checkRow 8 := nextWindow w6 2 (by decide +kernel)
private def w10 : RowWindow checkRow 10 := nextWindow w8 2 (by decide +kernel)
private def w12 : RowWindow checkRow 12 := nextWindow w10 2 (by decide +kernel)
private def w14 : RowWindow checkRow 14 := nextWindow w12 2 (by decide +kernel)
private def w16 : RowWindow checkRow 16 := nextWindow w14 2 (by decide +kernel)
private def w18 : RowWindow checkRow 18 := nextWindow w16 2 (by decide +kernel)
private def w20 : RowWindow checkRow 20 := nextWindow w18 2 (by decide +kernel)
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  apply certified M (armRows 2 5) pick (digit original 8) (digit rightInverse 4)
  · intro i j
    have h := (allBelow_iff _ _).mp (Bool.and_eq_true_iff.mp (w20.verified i.val i.isLt)).1 j.val j.isLt
    have hi : Fin.ofNat 20 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hj : Fin.ofNat 20 j.val=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa only [decide_eq_true_eq,hi,hj] using h
  · apply (allBelow_iff _ _).mpr
    intro i hi
    exact (Bool.and_eq_true_iff.mp (w20.verified i hi)).2

end Left


namespace Right
def M : Matrix (Fin 2 × Fin 2 × Fin 5) (ArmCols (Fin 2) (Fin 5) (Fin 5) (Fin 5) (Fin 0)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x800030000000f001400000000000000000001,
  0xa00010024000f000f00000000000000010000,
  0x30024000f001e00000000000100000000,
  0x8000300180019000500000001000000000000,
  0xc000000060000001900010000000000000000,
  0x800030000000f00140000000000000000000001,
  0xa00010024000f000f0000000000000000020000,
  0x30024000f001e0000000000000300000000,
  0x800030018001900050000000004000000000000,
  0xc00000006000000190000050000000000000000,
  0x60000000c000400000000000000000100,
  0x2001e000c000300000000000001000000,
  0x6001e000c000600000000010000000000,
  0x600140014000100000100000000000000,
  0x50000000501000000000000000000,
  0x60000000c00040000000000000000000100,
  0x2001e000c00030000000000000002000000,
  0x6001e000c00060000000000030000000000,
  0x60014001400010000000400000000000000,
  0x5000000050005000000000000000000]
def rightInverse : Array ℕ := #[
  0x4213051541112223436,
  0x30604603045331432553,
  0x36401642060503001020,
  0x33104624131656624621,
  0x64264551233563661411,
  0x20105405023662164336,
  0x22460462202404246065,
  0x50123314345440635201,
  0x66666543210665014340,
  0x10506306012446345224,
  0x41545136620136203525,
  0x50545306624046410223,
  0x32060660201302022030,
  0x21002430055450635601,
  0x6135044121164323364,
  0x40433102141362022330,
  0x60543506643110563402,
  0x55525316324224116166,
  0x42260161203162663331,
  0x21246431610366102326]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def pick (t : Fin 20) := (armCols 2 5 5 5 0).symm (Fin.ofNat 20 (pivots[t.val]?.getD 0))
private def checkRow (i : ℕ) :=
  allBelow (fun j => decide (M ((armRows 2 5).symm (Fin.ofNat 20 i)) (pick (Fin.ofNat 20 j)) = (digit original 8 i j : ℤ))) 20 &&
  allBelow (fun j => dot (digit original 8) (digit rightInverse 4) i j 20 % 7 == (if i=j then 1 else 0)) 20
private def w2 : RowWindow checkRow 2 := nextWindow (start checkRow) 2 (by decide +kernel)
private def w4 : RowWindow checkRow 4 := nextWindow w2 2 (by decide +kernel)
private def w6 : RowWindow checkRow 6 := nextWindow w4 2 (by decide +kernel)
private def w8 : RowWindow checkRow 8 := nextWindow w6 2 (by decide +kernel)
private def w10 : RowWindow checkRow 10 := nextWindow w8 2 (by decide +kernel)
private def w12 : RowWindow checkRow 12 := nextWindow w10 2 (by decide +kernel)
private def w14 : RowWindow checkRow 14 := nextWindow w12 2 (by decide +kernel)
private def w16 : RowWindow checkRow 16 := nextWindow w14 2 (by decide +kernel)
private def w18 : RowWindow checkRow 18 := nextWindow w16 2 (by decide +kernel)
private def w20 : RowWindow checkRow 20 := nextWindow w18 2 (by decide +kernel)
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  apply certified M (armRows 2 5) pick (digit original 8) (digit rightInverse 4)
  · intro i j
    have h := (allBelow_iff _ _).mp (Bool.and_eq_true_iff.mp (w20.verified i.val i.isLt)).1 j.val j.isLt
    have hi : Fin.ofNat 20 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hj : Fin.ofNat 20 j.val=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa only [decide_eq_true_eq,hi,hj] using h
  · apply (allBelow_iff _ _).mpr
    intro i hi
    exact (Bool.and_eq_true_iff.mp (w20.verified i hi)).2

end Right

lemma spans : Wing 2 5 5 5 0 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end Pair

end CriticalTensor.FiveBorder.Seven

namespace CriticalTensor.FiveBorder

open Tiles Seven

/-- Repeat the same independent two-coordinate arm at the prescribed outer factors. -/
lemma grow_inner {d n : ℕ} (h : Room d 5 5 n 0) (r : ℕ) :
    PencilFor (Fin (d+r*2)) (Fin 5) (Fin 5) (Fin (n+r*5)) (Fin 0) := by
  have raw := to_pencil (append h (repeat_paired (Fin r) Pair.spans))
  refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals simp [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]

private lemma pad_inner {D W X N Z Q : Type} [Fintype X] [Fintype N] [Fintype Z] [Fintype Q]
    (h : PencilFor D W X N Q) : PencilFor D W X (N⊕Z) Q := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hh⟩ := h
  refine ⟨a,b,c,Sum.elim ai 0,Sum.elim bi 0,Sum.elim ci 0,aq,bq,?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hs⟩ := hh T
  refine ⟨u,v,w,Sum.elim ui 0,Sum.elim vi 0,wq,?_⟩
  intro i j k he
  cases i <;> cases j <;> simpa [outsideOnly,insideOnly,Fintype.sum_sum_type] using hs _ _ k he

private lemma to_border {d n : ℕ} (h : PencilFor (Fin d) (Fin 5) (Fin 5) (Fin n) (Fin 0)) :
    CriticalTensor.Border 5 d 2 n 5 := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hh⟩ := h
  refine ⟨c,a,b,ci,ai,bi,?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hs⟩ := hh fun j k i => T i j k
  refine ⟨w,u,v,ui,vi,?_⟩
  intro i j k hleft
  have he : edge j k := by cases j <;> cases k <;> simp_all [edge]
  simpa [outsideOnly,insideOnly,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hs j k i he

end CriticalTensor.FiveBorder

namespace CriticalTensor
open FiveBorder FiveBorder.Seven

lemma border_five : Border 5 5 2 10 5 := by
  apply FiveBorder.to_border
  have h := FiveBorder.pad_inner (Z:=Fin 1) (grow_inner RoomThree.spans 1)
  refine pencil_transport (Equiv.refl _) (Equiv.refl _) ?_ (Equiv.refl _) h
  apply Fintype.equivOfCardEq
  decide

lemma border_six : Border 5 6 2 12 5 := FiveBorder.to_border (grow_inner RoomTwo.spans 2)

lemma border_twentyone : Border 5 21 2 49 5 := FiveBorder.to_border (grow_inner RoomThree.spans 9)

/-- The left arm of the same finite pair supplies both off-diagonal families. -/
lemma cross_five : Cross 5 2 5 := by
  obtain ⟨ai,bi,ci,aq,bq,f,g,h,_⟩ := Pair.spans
  refine ⟨ci,fun t i => (basisC t i : ℂ),ai,fun t k => (outB t k : ℂ),?_⟩
  intro T
  obtain ⟨u₀,u,v,hs⟩ := h fun j k i => T i j k
  refine ⟨u₀,u,?_⟩
  intro i j k
  simpa [Finset.sum_add_distrib,mul_comm,mul_left_comm,mul_assoc] using hs j k i

end CriticalTensor

namespace CriticalTensor

private lemma ceiling_between {n d q : ℕ} (hd : 0<d) (hlo : d*q<n) (hhi : n≤d*(q+1)) :
    n ⌈/⌉ d=q+1 := by
  refine le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr hhi) ?_
  by_contra! h
  exact (not_le_of_gt hlo) ((ceilDiv_le_iff_le_mul hd).mp (show n ⌈/⌉ d ≤ q by omega))

/-- All square-ended five-slice formats in the critical conjecture. -/
theorem five_square (m : ℕ) (hm : 5 ≤ m) : Spans 5 m m (5*m*m ⌈/⌉ (5+m+m-2)) := by
  by_cases he : m%2=0
  · obtain ⟨t,rfl⟩ : ∃ t, m=6+2*t := ⟨(m-6)/2,by omega⟩
    have den : 5+(6+2*t)+(6+2*t)-2=15+4*t := by omega
    rw [den]
    have num : 5*(6+2*t)*(6+2*t) ⌈/⌉ (15+4*t) = 12+5*t := by
      convert ceiling_between (n:=5*(6+2*t)*(6+2*t)) (d:=15+4*t) (q:=11+5*t) (by omega) (by nlinarith) (by nlinarith) using 1
      omega
    rw [num]
    exact grow 5 6 2 12 5 t FiveGrid.base_six border_six cross_five
  · by_cases small : m<21
    · obtain ⟨t,ht,rfl⟩ : ∃ t, t≤7 ∧ m=5+2*t := ⟨(m-5)/2,by omega,by omega⟩
      have den : 5+(5+2*t)+(5+2*t)-2=13+4*t := by omega
      rw [den]
      have num : 5*(5+2*t)*(5+2*t) ⌈/⌉ (13+4*t) = 10+5*t := by
        convert ceiling_between (n:=5*(5+2*t)*(5+2*t)) (d:=13+4*t) (q:=9+5*t) (by omega) (by nlinarith) (by nlinarith) using 1
        omega
      rw [num]
      exact grow 5 5 2 10 5 t FiveGrid.base_five border_five cross_five
    · obtain ⟨t,rfl⟩ : ∃ t, m=21+2*t := ⟨(m-21)/2,by omega⟩
      have den : 5+(21+2*t)+(21+2*t)-2=45+4*t := by omega
      rw [den]
      have num : 5*(21+2*t)*(21+2*t) ⌈/⌉ (45+4*t) = 49+5*t := by
        convert ceiling_between (n:=5*(21+2*t)*(21+2*t)) (d:=45+4*t) (q:=48+5*t) (by omega) (by nlinarith) (by nlinarith) using 1
        omega
      rw [num]
      exact grow 5 21 2 49 5 t FiveGrid.base_twentyOne border_twentyone cross_five

end CriticalTensor

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.H1 := by
  intro m hm
  exact CriticalReduction.bounded_of_witness (CriticalTensor.five_square m hm)
