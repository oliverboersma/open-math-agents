import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1

/-! A six-slice square tangent construction and the remaining critical formats.

The block growth and grid gluing are adapted from mattdorman’s merged
five-slice square proof. The critical boundary is adapted from the merged
R1.H2.R1 reduction by the same author. -/

namespace SixSliceTensor

private def Spans (a b c r : ℕ) : Prop :=
  ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

/-- A diagonal block with a regular coordinate part of length h and a base of length d. -/
private def Border (a d h base extra : ℕ) : Prop :=
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
private def Cross (a h extra : ℕ) : Prop :=
  ∃ x₁ x₂ : Fin extra → Fin a → ℂ, ∃ y z : Fin extra → Fin h → ℂ,
    ∀ T : Fin a → Fin h → Fin h → ℂ, ∃ v w : Fin extra → Fin h → ℂ, ∀ i j k,
      T i j k = ∑ t, (x₂ t i*(v t j*z t k) + x₁ t i*(y t j*w t k))

end SixSliceTensor

namespace SixSliceTensor.Growth

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
private lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
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

private lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
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
private lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
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
private lemma graded_surjective {R C S : Type} [Fintype R] [Fintype C] [Fintype S] [DecidableEq S]
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
private lemma cover_matrix {R C I J : Type} [Fintype C] [DecidableEq C] [Fintype J]
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

end SixSliceTensor.Growth

namespace SixSliceTensor.Growth

open MvPolynomial

private structure Dimensions where
  a : ℕ
  d : ℕ
  h : ℕ
  base : ℕ
  extra : ℕ

variable (p : Dimensions)

private abbrev Pt (G : Type) := Fin p.base ⊕ (G × Fin p.extra)
private abbrev Axis (G : Type) := Fin p.d ⊕ (G × Fin p.h)
private abbrev LocalAxis := Fin p.h ⊕ Fin p.d
private abbrev Dir (I : Type) := Fin p.a ⊕ (I ⊕ I)
private abbrev V (G : Type) := (Fin p.base × Dir p (Fin p.d)) ⊕ (G × Fin p.extra × Dir p (LocalAxis p))
private abbrev RR (G : Type) := Fin p.a × Axis p G × Axis p G
private abbrev CC (G : Type) := Pt p G × Dir p (Axis p G)
private abbrev Pair (G : Type) := {z : G × G // z.1 ≠ z.2}
private abbrev Sector (G : Type) := Unit ⊕ (G ⊕ Pair G)
private abbrev Arm := (Fin p.h × Fin p.d) ⊕ ((Fin p.d × Fin p.h) ⊕ (Fin p.h × Fin p.h))

private def arms : Arm p → LocalAxis p × LocalAxis p
  | .inl (j,k) => (.inl j,.inr k)
  | .inr (.inl (j,k)) => (.inr j,.inl k)
  | .inr (.inr (j,k)) => (.inl j,.inl k)

private def loc {G : Type} (g : G) : LocalAxis p → Axis p G
  | .inl u => .inr (g,u)
  | .inr j => .inl j

private def Row {G : Type} : Sector G → Type
  | .inl _ => Fin p.a × Fin p.d × Fin p.d
  | .inr (.inl _) => Fin p.a × Arm p
  | .inr (.inr _) => Fin p.a × Fin p.h × Fin p.h

private def Col {G : Type} : Sector G → Type
  | .inl _ => Fin p.base × Dir p (Fin p.d)
  | .inr (.inl _) => (Fin p.extra × Dir p (LocalAxis p)) ⊕ (Fin p.base × (Fin p.h ⊕ Fin p.h))
  | .inr (.inr _) => Fin p.extra × (Fin p.h ⊕ Fin p.h)

private instance {G : Type} (s : Sector G) : Fintype (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
private instance {G : Type} (s : Sector G) : DecidableEq (Row p s) := by rcases s with u|g|z <;> dsimp [Row] <;> infer_instance
private instance {G : Type} (s : Sector G) : Fintype (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance
private instance {G : Type} (s : Sector G) : DecidableEq (Col p s) := by rcases s with u|g|z <;> dsimp [Col] <;> infer_instance

private def row {G : Type} : (s : Sector G) → Row p s → RR p G
  | .inl _,(i,j,k) => (i,.inl j,.inl k)
  | .inr (.inl g),(i,z) => (i,loc p g (arms p z).1,loc p g (arms p z).2)
  | .inr (.inr q),(i,j,k) => (i,.inr (q.val.1,j),.inr (q.val.2,k))

private def col {G : Type} : (s : Sector G) → Col p s → CC p G
  | .inl _,(t,h) => (.inl t,h.map id (Sum.map Sum.inl Sum.inl))
  | .inr (.inl g),.inl (t,h) => (.inr (g,t),h.map id (Sum.map (loc p g) (loc p g)))
  | .inr (.inl g),.inr (t,.inl h) => (.inl t,.inr (.inl (.inr (g,h))))
  | .inr (.inl g),.inr (t,.inr h) => (.inl t,.inr (.inr (.inr (g,h))))
  | .inr (.inr q),(t,.inl h) => (.inr (q.val.2,t),.inr (.inl (.inr (q.val.1,h))))
  | .inr (.inr q),(t,.inr h) => (.inr (q.val.1,t),.inr (.inr (.inr (q.val.2,h))))

private def lev {G : Type} : Sector G → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

section
variable {G K : Type} [DecidableEq G] [CommSemiring K]

private def A (x : V p G → K) : Pt p G → Fin p.a → K
  | .inl t,i => x (.inl (t,.inl i))
  | .inr (g,t),i => x (.inr (g,t,.inl i))

private def tail (b : Fin p.base → Fin p.d → K) (B : G → Fin p.extra → LocalAxis p → K) : Pt p G → Axis p G → K
  | .inl t,.inl j => b t j
  | .inl _,.inr _ => 0
  | .inr (g,t),.inl j => B g t (.inr j)
  | .inr (g,t),.inr (h,i) => if h=g then B g t (.inl i) else 0

private def B (x : V p G → K) := tail p (fun t j => x (.inl (t,.inr (.inl j)))) (fun g t j => x (.inr (g,t,.inr (.inl j))))
private def Cc (x : V p G → K) := tail p (fun t k => x (.inl (t,.inr (.inr k)))) (fun g t k => x (.inr (g,t,.inr (.inr k))))

private def tangent (x : V p G → K) (r : RR p G) : CC p G → K
  | (t,.inl h) => if h=r.1 then B p x t r.2.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inl h)) => if h=r.2.1 then A p x t r.1 * Cc p x t r.2.2 else 0
  | (t,.inr (.inr h)) => if h=r.2.2 then A p x t r.1 * B p x t r.2.1 else 0

private def full (x : V p G → K) : Matrix (Σ s : Sector G, Row p s) (Σ s : Sector G, Col p s) K :=
  fun r c => tangent p x (row p r.1 r.2) (col p c.1 c.2)

private def block (x : V p G → K) (s : Sector G) : Matrix (Row p s) (Col p s) K :=
  fun r c => tangent p x (row p s r) (col p s c)

private lemma tail_loc (b : Fin p.base → Fin p.d → K) (H : G → Fin p.extra → LocalAxis p → K)
    (g : G) (t : Fin p.extra) (j : LocalAxis p) : tail p b H (.inr (g,t)) (loc p g j) = H g t j := by
  cases j <;> simp [tail,loc]

omit [DecidableEq G] in
private lemma loc_eq (g : G) (j k : LocalAxis p) : loc p g j=loc p g k ↔ j=k := by cases j <;> cases k <;> simp [loc]

private lemma tail_map {L : Type} [CommSemiring L] (φ : K →+* L) (b : Fin p.base → Fin p.d → K)
    (H : G → Fin p.extra → LocalAxis p → K) (t : Pt p G) (j : Axis p G) :
    φ (tail p b H t j) = tail p (fun t j => φ (b t j)) (fun g t j => φ (H g t j)) t j := by
  rcases t with t|⟨g,t⟩ <;> rcases j with j|⟨h,j⟩ <;> simp only [tail,map_zero]
  by_cases he : h=g <;> simp [he]

private lemma block_eval (x : V p G → ℂ) (s : Sector G) :
    (block p (MvPolynomial.X : V p G → MvPolynomial (V p G) ℂ) s).map (eval x) = block p x s := by
  ext r j
  change eval x (tangent p MvPolynomial.X (row p s r) (col p s j)) = tangent p x (row p s r) (col p s j)
  generalize hc : col p s j = z
  rcases z with ⟨t,h|h|h⟩ <;> rcases t with t|⟨g,t⟩ <;>
    simp only [tangent,A,B,Cc,apply_ite,tail_map,map_mul,map_zero,eval_X]
  all_goals split <;> simp_all

end

private lemma row_surj {G : Type} [DecidableEq G] : Function.Surjective (fun z : Σ s : Sector G, Row p s => row p z.1 z.2) := by
  rintro ⟨i,j|⟨g,j⟩,k|⟨l,k⟩⟩
  · exact ⟨⟨.inl (),i,j,k⟩,rfl⟩
  · exact ⟨⟨.inr (.inl l),i,.inr (.inl (j,k))⟩,rfl⟩
  · exact ⟨⟨.inr (.inl g),i,.inl (j,k)⟩,rfl⟩
  · by_cases h : g=l
    · subst l
      exact ⟨⟨.inr (.inl g),i,.inr (.inr (j,k))⟩,rfl⟩
    · exact ⟨⟨.inr (.inr ⟨(g,l),h⟩),i,j,k⟩,rfl⟩

end SixSliceTensor.Growth

namespace SixSliceTensor.Growth

variable (p : Dimensions) {G : Type} [DecidableEq G]

private def param (a : Fin p.base → Fin p.a → ℂ) (b c : Fin p.base → Fin p.d → ℂ)
    (A : G → Fin p.extra → Fin p.a → ℂ) (B C : G → Fin p.extra → LocalAxis p → ℂ) : V p G → ℂ
  | .inl (t,.inl i) => a t i
  | .inl (t,.inr (.inl j)) => b t j
  | .inl (t,.inr (.inr k)) => c t k
  | .inr (g,t,.inl i) => A g t i
  | .inr (g,t,.inr (.inl j)) => B g t j
  | .inr (g,t,.inr (.inr k)) => C g t k

private lemma base_rank (hb : Spans p.a p.d p.d p.base) :
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

private def target (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) : LocalAxis p → LocalAxis p → ℂ
  | .inl j,.inl k => y (i,.inr (.inr (j,k)))
  | .inl j,.inr k => y (i,.inl (j,k))
  | .inr j,.inl k => y (i,.inr (.inl (j,k)))
  | .inr _,.inr _ => 0

private lemma target_arms (y : Fin p.a × Arm p → ℂ) (i : Fin p.a) (r : Arm p) :
    target p y i (arms p r).1 (arms p r).2=y (i,r) := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> rfl

private lemma arms_hit (r : Arm p) : (arms p r).1.isLeft=true ∨ (arms p r).2.isLeft=true := by
  rcases r with ⟨j,k⟩|⟨j,k⟩|⟨j,k⟩ <;> simp [arms]

private lemma border_rank (g : G) (hr : Border p.a p.d p.h p.base p.extra) :
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

private lemma cross_rank (q : Pair G) (hc : Cross p.a p.h p.extra) :
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

end SixSliceTensor.Growth

namespace SixSliceTensor.Growth

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

private lemma off (s t : Sector G) (h : s≠t) (hl : lev s≤lev t) (r : Row p s) (z : Col p t) :
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

end SixSliceTensor.Growth

namespace SixSliceTensor.Growth

open MvPolynomial

variable (p : Dimensions) {G : Type} [Fintype G] [DecidableEq G]

private def actual (x : V p G → ℂ) : Matrix (RR p G) (CC p G) ℂ := tangent p x

private lemma common (hb : Spans p.a p.d p.d p.base) (hr : Border p.a p.d p.h p.base p.extra)
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

private lemma action (x : V p G → ℂ) (z : CC p G → ℂ) (i : Fin p.a) (j k : Axis p G) :
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

end SixSliceTensor.Growth

namespace SixSliceTensor

open Growth

/-- A base block, its border with one regular block, and an ordered pair of regular
blocks suffice for an arbitrary finite number of regular blocks along the two equal axes. -/
private lemma grow (a d h base extra t : ℕ) (hb : Spans a d d base)
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

end SixSliceTensor

namespace SixSliceTensor.Grid

open MvPolynomial SixSliceTensor.Growth

private abbrev Slot (G : Type) (s : ℕ) := G × G × Fin s
private abbrev Parameters (G W : Type) (s d : ℕ) := Slot G s × (Fin d ⊕ (Fin d ⊕ W))
private abbrev Columns (G W : Type) (s d : ℕ) :=
  (G × Fin s × Fin d) ⊕ ((G × Fin s × Fin d) ⊕ (Fin s × W))

variable {s d : ℕ}

private def LocalSpan {G W : Type} [Fintype G] (a b : Slot G s → Fin d → ℂ)
    (c : Slot G s → W → ℂ) (g h : G) : Prop :=
  ∀ T : Fin d → Fin d → W → ℂ,
    ∃ u v : G → Fin s → Fin d → ℂ, ∃ w : Fin s → W → ℂ, ∀ i j k,
      T i j k =
        (∑ l, ∑ t, u l t i * (b (l,h,t) j * c (l,h,t) k)) +
        (∑ l, ∑ t, a (g,l,t) i * (v l t j * c (g,l,t) k)) +
        ∑ t, a (g,h,t) i * (b (g,h,t) j * w t k)

private def pad {G : Type} [DecidableEq G] (g : G) (v : Fin d → ℂ) (i : G × Fin d) : ℂ :=
  if g = i.1 then v i.2 else 0

private lemma assemble {G W : Type} [Fintype G] [DecidableEq G] (a b : Slot G s → Fin d → ℂ)
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

private def aval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (i : Fin d) := x (z, Sum.inl i)
private def bval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (j : Fin d) := x (z, Sum.inr (Sum.inl j))
private def cval {G W : Type} (x : Parameters G W s d → ℂ) (z : Slot G s) (k : W) := x (z, Sum.inr (Sum.inr k))

private noncomputable def polynomialMatrix {G W : Type} [DecidableEq W] (g h : G) :
    Matrix (Fin d × Fin d × W) (Columns G W s d) (MvPolynomial (Parameters G W s d) ℂ)
  | (i,j,k), Sum.inl (l,t,q) =>
      if q = i then X ((l,h,t), Sum.inr (Sum.inl j)) * X ((l,h,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inl (l,t,q)) =>
      if q = j then X ((g,l,t), Sum.inl i) * X ((g,l,t), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inr (t,q)) =>
      if q = k then X ((g,h,t), Sum.inl i) * X ((g,h,t), Sum.inr (Sum.inl j)) else 0

private lemma polynomial_action {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
    (g h : G) (x : Parameters G W s d → ℂ) (y : Columns G W s d → ℂ) (i j : Fin d) (k : W) :
    ((polynomialMatrix (s:=s) (d:=d) g h).map (eval x)).mulVec y (i,j,k) =
      (∑ l, ∑ t, y (Sum.inl (l,t,i)) * (bval x (l,h,t) j * cval x (l,h,t) k)) +
      (∑ l, ∑ t, aval x (g,l,t) i * (y (Sum.inr (Sum.inl (l,t,j))) * cval x (g,l,t) k)) +
      ∑ t, aval x (g,h,t) i * (bval x (g,h,t) j * y (Sum.inr (Sum.inr (t,k)))) := by
  classical
  change (∑ z : Columns G W s d, eval x (polynomialMatrix g h (i,j,k) z) * y z) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, polynomialMatrix, aval, bval, cval,
    apply_ite, Finset.sum_ite_eq', mul_assoc, mul_comm, add_assoc]

private lemma local_iff_surjective {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
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

private lemma simultaneous_local {G W : Type} [Fintype G] [Fintype W] [DecidableEq W]
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

private def relabel {G H : Type} (e f : G ≃ H) (z : Slot G s) : Slot H s := (e z.1, f z.2.1, z.2.2)

private lemma relabel_local {G H W : Type} [Fintype G] [Fintype H] (e f : G ≃ H)
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
private lemma spans_of_cell {g d s a : ℕ} [NeZero g]
    (x₀ : Parameters (Fin g) (Fin a) s d → ℂ)
    (h₀ : LocalSpan (aval x₀) (bval x₀) (cval x₀) 0 0) :
    SixSliceTensor.Spans a (g*d) (g*d) (g*(g*s)) := by
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

end SixSliceTensor.Grid



namespace SixSliceCertificate

private abbrev Packed := ℕ × ℕ

private def difference (a b : ℕ) : ℕ := a ^^^ (a &&& b)

private lemma difference_bit (a b i : ℕ) :
    (difference a b).testBit i = (a.testBit i && !b.testBit i) := by
  simp only [difference, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

private def read (p : Packed) (i : ℕ) : ℕ :=
  if p.2.testBit i then 2 else if p.1.testBit i then 1 else 0

private def add (p q : Packed) : Packed :=
  if p = (0,0) then q else if q = (0,0) then p else
  let p₁ := difference p.1 p.2
  let q₁ := difference q.1 q.2
  let pSupport := p.1 ||| p.2
  let qSupport := q.1 ||| q.2
  (difference p₁ qSupport ||| difference q₁ pSupport ||| (p.2 &&& q.2),
    difference p.2 qSupport ||| difference q.2 pSupport ||| (p₁ &&& q₁))

private def scale (n : ℕ) (p : Packed) : Packed :=
  if n % 3 = 0 then (0,0)
  else if n % 3 = 1 then p
  else (p.2, difference p.1 p.2)

private lemma read_zero (i : ℕ) : read (0,0) i = 0 := by simp [read]

private lemma read_add (p q : Packed) (i : ℕ) :
    (read (add p q) i : ZMod 3) = (read p i : ZMod 3) + read q i := by
  by_cases hp : p = (0,0)
  · simp [add, hp, read_zero]
  by_cases hq : q = (0,0)
  · simp [add, hp, hq, read_zero]
  simp only [add, hp, hq, if_false, read, difference_bit, Nat.testBit_and, Nat.testBit_or]
  cases p.1.testBit i <;> cases p.2.testBit i <;>
    cases q.1.testBit i <;> cases q.2.testBit i <;> decide

private lemma read_scale (n : ℕ) (p : Packed) (i : ℕ) :
    (read (scale n p) i : ZMod 3) = (n : ZMod 3) * read p i := by
  have hm : n % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [← ZMod.natCast_mod n 3]
  interval_cases h : n % 3
  · simp [scale, h, read_zero]
  · simp [scale, h]
  · simp only [scale, h, if_false, Nat.reduceEqDiff, read, difference_bit]
    cases p.1.testBit i <;> cases p.2.testBit i <;> decide

private def packedSum (f : ℕ → Packed) : ℕ → Packed
  | 0 => (0,0)
  | n+1 => add (packedSum f n) (f n)

private lemma read_sum (f : ℕ → Packed) (n i : ℕ) :
    (read (packedSum f n) i : ZMod 3) =
      ∑ t ∈ Finset.range n, (read (f t) i : ZMod 3) := by
  induction n with
  | zero => simp [packedSum, read_zero]
  | succ n ih => rw [packedSum, read_add, ih, Finset.sum_range_succ]

private abbrev Col (a b c r : ℕ) := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))

private def tangent {R : Type} {a b c r : ℕ} {K : Type} [CommSemiring K]
    (coords : R → Fin a × Fin b × Fin c) (x : Fin r → Fin a → K)
    (y : Fin r → Fin b → K) (z : Fin r → Fin c → K) : Matrix R (Col a b c r) K :=
  fun row (t, d) =>
    let (i,j,k) := coords row
    match d with
    | .inl i' => if i' = i then y t j * z t k else 0
    | .inr (.inl j') => if j' = j then x t i * z t k else 0
    | .inr (.inr k') => if k' = k then x t i * y t j else 0

private lemma matrix_action {R : Type} {a b c r : ℕ} {K : Type} [CommSemiring K]
    (coords : R → Fin a × Fin b × Fin c) (x : Fin r → Fin a → K)
    (y : Fin r → Fin b → K) (z : Fin r → Fin c → K) (w : Col a b c r → K)
    (row : R) :
    (tangent coords x y z).mulVec w row =
      let (i,j,k) := coords row
      ∑ t, (y t j * z t k * w (t,.inl i) +
        x t i * z t k * w (t,.inr (.inl j)) + x t i * y t j * w (t,.inr (.inr k))) := by
  classical
  rcases hcoord : coords row with ⟨i,j,k⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [tangent, hcoord, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  <;> ring

private def imageRow (a b c r : ℕ) (x y z : ℕ → ℕ → ℕ) (cert : ℕ → Packed)
    (i j k : ℕ) : Packed :=
  packedSum (fun t =>
    let offset := t * (a+b+c)
    add (add (scale (y t j * z t k) (cert (offset+i)))
      (scale (x t i * z t k) (cert (offset+a+j))))
      (scale (x t i * y t j) (cert (offset+a+b+k)))) r

private lemma complex_surjectivity {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (B : Matrix κ ι ℤ)
    (hab : A.map (Int.castRingHom (ZMod 3)) * B.map (Int.castRingHom (ZMod 3)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let C := A * B
  have h3 : ((C.det : ℤ) : ZMod 3) = 1 := by
    change (Int.castRingHom (ZMod 3)) C.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show C = A * B from rfl, Matrix.map_mul, hab,
      Matrix.det_one]
  have hne : C.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at h3
    exact zero_ne_one h3
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

private theorem checked {R : Type} [Fintype R] [DecidableEq R] {a b c r : ℕ}
    (coords : R → Fin a × Fin b × Fin c) (code : R → ℕ) (hcode : Function.Injective code)
    (x y z : ℕ → ℕ → ℕ) (cert : ℕ → Packed)
    (h : ∀ s : R, imageRow a b c r x y z cert
        (coords s).1.val (coords s).2.1.val (coords s).2.2.val = (2 ^ code s, 0)) :
    Function.Surjective
      (tangent (r:=r) coords (fun t i => (x t.val i.val : ℂ)) (fun t j => (y t.val j.val : ℂ))
        (fun t k => (z t.val k.val : ℂ))).mulVec := by
  let A : Matrix R (Col a b c r) ℤ :=
    tangent coords (fun t i => x t.val i.val) (fun t j => y t.val j.val) (fun t k => z t.val k.val)
  let B : Matrix (Col a b c r) R ℤ :=
    fun (t,d) s => read (cert (t.val*(a+b+c) + d.elim Fin.val
      (Sum.elim (fun j => a+j.val) (fun k => a+b+k.val)))) (code s)
  have acast {K : Type} [CommRing K] : A.map (Int.castRingHom K) =
      tangent coords (fun t i => (x t.val i.val : K)) (fun t j => (y t.val j.val : K))
        (fun t k => (z t.val k.val : K)) := by
    ext s ⟨t,d⟩
    rcases d with i|j|k <;>
      simp [A, tangent, apply_ite, Int.cast_mul] <;> split <;> simp_all
  rw [← acast]
  apply complex_surjectivity A B
  ext s u
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (A.map (Int.castRingHom (ZMod 3))).mulVec (fun l => (B l u : ZMod 3)) s = _
  rw [acast, matrix_action]
  have hh := congrArg (fun p => (read p (code u) : ZMod 3)) (h s)
  simp only [imageRow, read_sum, read_add, read_scale, Nat.cast_mul] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  refine Eq.trans ?_ (Eq.trans hh ?_)
  · simp only [B, Sum.elim_inl, Sum.elim_inr, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Nat.add_assoc]
  · by_cases he : s = u
    · subst u
      simp [read]
    · have hc : code s ≠ code u := fun h => he (hcode h)
      simp [read, hc, he]


open SixSliceTensor

private def prodCode {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A × B ≃ Fin (a*b) :=
  (e.prodCongr f).trans finProdFinEquiv

private def sumCode {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A ⊕ B ≃ Fin (a+b) :=
  (e.sumCongr f).trans finSumFinEquiv

private def squareCode (a d : ℕ) : Fin a × Fin d × Fin d ≃ Fin (a*(d*d)) :=
  prodCode (Equiv.refl _) finProdFinEquiv

private def covers {a b c r : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (z : Fin r → Fin c → ℂ) : Prop :=
  ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
    ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

private lemma covers_of_rank {a b c r : ℕ} {x : Fin r → Fin a → ℂ}
    {y : Fin r → Fin b → ℂ} {z : Fin r → Fin c → ℂ}
    (hs : Function.Surjective (tangent id x y z).mulVec) :
    covers x y z := by
  intro T
  obtain ⟨q,hq⟩ := hs fun p => T p.1 p.2.1 p.2.2
  refine ⟨fun t i => q (t,.inl i), fun t j => q (t,.inr (.inl j)), fun t k => q (t,.inr (.inr k)), ?_⟩
  intro i j k
  have he := congrFun hq (i,j,k)
  rw [matrix_action] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro t _
  ring

private lemma square {a d r : ℕ} (x y z : ℕ → ℕ → ℕ) (cert : ℕ → Packed)
    (h : ∀ s : Fin a × Fin d × Fin d, imageRow a d d r x y z cert s.1.val s.2.1.val s.2.2.val =
      (2 ^ (squareCode a d s).val, 0)) :
    Spans a d d r := by
  let e := squareCode a d
  have hr := checked id (fun s => (e s).val) (fun _ _ h => e.injective (Fin.ext h)) x y z cert h
  exact ⟨_,_,_,covers_of_rank hr⟩

private abbrev BorderAxis (d : ℕ) := Fin 2 ⊕ Fin d
private abbrev BorderRows (d : ℕ) := Fin 6 × ((Fin 2 × BorderAxis d) ⊕ (Fin d × Fin 2))

private def borderCoords {d : ℕ} (s : BorderRows d) : Fin 6 × Fin (2+d) × Fin (2+d) :=
  let e : BorderAxis d ≃ Fin (2+d) := finSumFinEquiv
  (s.1, match s.2 with
  | .inl (j,k) => (e (.inl j),e k)
  | .inr (j,k) => (e (.inr j),e (.inl k)))

private def borderCode (d : ℕ) : BorderRows d ≃ Fin (6*(2*(2+d)+d*2)) :=
  prodCode (Equiv.refl _) (sumCode (prodCode (Equiv.refl _) finSumFinEquiv) finProdFinEquiv)

private lemma border {d r : ℕ} (x y z : ℕ → ℕ → ℕ) (cert : ℕ → Packed)
    (hy : ∀ t : Fin r, ∀ j : Fin 2, y (6+t.val) j.val = 0)
    (hz : ∀ t : Fin r, ∀ k : Fin 2, z (6+t.val) k.val = 0)
    (h : ∀ s : BorderRows d, imageRow 6 (2+d) (2+d) (6+r) x y z cert
      (borderCoords s).1.val (borderCoords s).2.1.val (borderCoords s).2.2.val =
      (2 ^ (borderCode d s).val, 0)) : Border 6 d 2 r 6 := by
  let e : BorderAxis d ≃ Fin (2+d) := finSumFinEquiv
  let f : Fin 6 ⊕ Fin r ≃ Fin (6+r) := finSumFinEquiv
  let X : Fin (6+r) → Fin 6 → ℂ := fun t i => x t.val i.val
  let Y : Fin (6+r) → BorderAxis d → ℂ := fun t j => y t.val (e j).val
  let Z : Fin (6+r) → BorderAxis d → ℂ := fun t k => z t.val (e k).val
  have hy0 (t : Fin r) (j : Fin 2) : Y (f (.inr t)) (.inl j) = 0 := by
    change ((y (6+t.val) j.val : ℕ) : ℂ) = 0
    rw [hy, Nat.cast_zero]
  have hz0 (t : Fin r) (k : Fin 2) : Z (f (.inr t)) (.inl k) = 0 := by
    change ((z (6+t.val) k.val : ℕ) : ℂ) = 0
    rw [hz, Nat.cast_zero]
  have hsurj := checked borderCoords (fun s => (borderCode d s).val)
    (fun _ _ he => (borderCode d).injective (Fin.ext he)) x y z cert h
  refine ⟨fun t => X (f (.inl t)), fun t => Y (f (.inl t)), fun t => Z (f (.inl t)),
    fun t => X (f (.inr t)), fun t j => Y (f (.inr t)) (.inr j),
    fun t k => Z (f (.inr t)) (.inr k), ?_⟩
  intro T
  obtain ⟨q,hq⟩ := hsurj fun s =>
    let (i,j,k) := borderCoords s
    T i (e.symm j) (e.symm k)
  let U := fun t i => q (t,.inl i)
  let V := fun t j => q (t,.inr (.inl (e j)))
  let W := fun t k => q (t,.inr (.inr (e k)))
  refine ⟨fun t => U (f (.inl t)), fun t => V (f (.inl t)), fun t => W (f (.inl t)),
    fun t j => V (f (.inr t)) (.inl j), fun t k => W (f (.inr t)) (.inl k), ?_⟩
  intro i j k hit
  have existsRow : ∃ s : BorderRows d, borderCoords s = (i, e j, e k) := by
    cases j with
    | inl j => exact ⟨(i,.inl (j,k)),rfl⟩
    | inr j =>
      cases k with
      | inl k => exact ⟨(i,.inr (j,k)),rfl⟩
      | inr k => simp at hit
  obtain ⟨s,hs⟩ := existsRow
  have hs' := congrFun hq s
  rw [matrix_action, hs] at hs'
  simp only [Equiv.symm_apply_apply] at hs'
  have he : T i j k = ∑ t, (U t i * (Y t j * Z t k) +
      X t i * (V t j * Z t k) + X t i * (Y t j * W t k)) := by
    rw [← hs']
    apply Finset.sum_congr rfl
    intro t _
    simp [U,V,W,X,Y,Z]
    ring
  rw [he, ← f.sum_comp, Fintype.sum_sum_type]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  cases j <;> cases k
  · simp only [Sum.elim_inl, hy0, hz0, mul_zero, zero_mul, add_zero]
  · simp only [Sum.elim_inl, Sum.elim_inr, hy0, mul_zero, zero_mul, zero_add, add_zero]
  · simp only [Sum.elim_inl, Sum.elim_inr, hz0, mul_zero, zero_add, add_zero]
  · simp at hit

/-- The coordinate tangent at (t,t,t) covers precisely the rows which agree
with its base point in at least two positions. -/
private abbrev headHit {d : ℕ} (t i : Fin 6) (j k : Fin d) : Prop :=
  (j.val = t.val ∧ k.val = t.val) ∨
    (i = t ∧ k.val = t.val) ∨ (i = t ∧ j.val = t.val)

private lemma head_unique {d : ℕ} {s t i : Fin 6} {j k : Fin d}
    (hs : headHit s i j k) (ht : headHit t i j k) : s = t := by
  rcases hs with ⟨h₁,h₂⟩|⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;>
    rcases ht with ⟨h₃,h₄⟩|⟨h₃,h₄⟩|⟨h₃,h₄⟩ <;>
    apply Fin.ext <;> grind

/-- Solve the rows outside the six disjoint coordinate tangents first.
The coordinate tangents then supply the remaining entries of the residual. -/
private lemma fill_basis {d r n : ℕ} (hd : 6 ≤ d)
    (coords : Fin n → Fin 6 × Fin d × Fin d)
    (outside : ∀ i j k, (∃ t : Fin 6, headHit t i j k) ∨ ∃ s, coords s = (i,j,k))
    (x : Fin r → Fin 6 → ℂ) (y z : Fin r → Fin d → ℂ)
    (rank : Function.Surjective (tangent coords x y z).mulVec) :
    Spans 6 d d (6+r) := by
  classical
  let f : Fin 6 ⊕ Fin r ≃ Fin (6+r) := finSumFinEquiv
  let e (t : Fin 6) : Fin d := t.castLE hd
  let X (t i : Fin 6) : ℂ := if i = t then 1 else 0
  let Y (t : Fin 6) (j : Fin d) : ℂ := if j.val = t.val then 1 else 0
  refine ⟨fun t => (f.symm t).elim X x, fun t => (f.symm t).elim Y y,
    fun t => (f.symm t).elim Y z,?_⟩
  intro T
  obtain ⟨q,hq⟩ := rank fun s => T (coords s).1 (coords s).2.1 (coords s).2.2
  let u (t : Fin r) (i : Fin 6) := q (t,.inl i)
  let v (t : Fin r) (j : Fin d) := q (t,.inr (.inl j))
  let w (t : Fin r) (k : Fin d) := q (t,.inr (.inr k))
  let contribution (i : Fin 6) (j k : Fin d) : ℂ :=
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
  let R (i : Fin 6) (j k : Fin d) := T i j k - contribution i j k
  let U (t i : Fin 6) := R i (e t) (e t)
  let V (t : Fin 6) (j : Fin d) := if j.val = t.val then 0 else R t j (e t)
  let W (t : Fin 6) (k : Fin d) := if k.val = t.val then 0 else R t (e t) k
  refine ⟨fun t => (f.symm t).elim U u, fun t => (f.symm t).elim V v,
    fun t => (f.symm t).elim W w,?_⟩
  intro i j k
  rw [← f.sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  change T i j k = (∑ t, (U t i*(Y t j*Y t k) + X t i*(V t j*Y t k) +
    X t i*(Y t j*W t k))) + contribution i j k
  have hterm (t : Fin 6) :
      U t i*(Y t j*Y t k) + X t i*(V t j*Y t k) + X t i*(Y t j*W t k) =
        if headHit t i j k then R i j k else 0 := by
    have ej : j.val = t.val → e t = j := fun h => Fin.ext h.symm
    have ek : k.val = t.val → e t = k := fun h => Fin.ext h.symm
    by_cases hi : i=t <;> by_cases hj : j.val=t.val <;> by_cases hk : k.val=t.val <;>
      simp_all [U,V,W,X,Y]
  have hs : (∑ t, if headHit t i j k then R i j k else 0) = R i j k := by
    by_cases h : ∃ t : Fin 6, headHit t i j k
    · obtain ⟨t,ht⟩ := h
      calc
        _ = ∑ s : Fin 6, if s=t then R i j k else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases he : s=t
          · subst s
            simp [ht]
          · have hn : ¬headHit s i j k := fun hp => he (head_unique hp ht)
            simp [he, hn]
        _ = _ := by simp
    · have hzero : R i j k = 0 := by
        have ⟨s,hs⟩ := (outside i j k).resolve_left h
        have he := congrFun hq s
        rw [matrix_action, hs] at he
        apply sub_eq_zero.mpr
        conv_lhs => rw [← he]
        apply Finset.sum_congr rfl
        intro t _
        simp only [u,v,w]
        ring
      simp [hzero]
  simpa only [hterm,hs,R,sub_add_cancel]


namespace BasisSeed6

private def points : Array (Array ℕ) := #[
  #[0, 2, 0, 1, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 1, 1, 2, 0],
  #[2, 1, 1, 2, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 1, 2, 0, 1],
  #[2, 0, 2, 0, 1, 1, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 2, 2],
  #[0, 0, 2, 2, 1, 0, 2, 1, 2, 2, 2, 1, 2, 2, 0, 1, 1, 2],
  #[1, 2, 1, 2, 0, 1, 0, 2, 1, 1, 2, 0, 1, 2, 2, 2, 2, 1],
  #[0, 1, 2, 2, 0, 0, 2, 1, 1, 1, 2, 0, 1, 0, 1, 2, 2, 2],
  #[2, 1, 2, 0, 0, 2, 0, 0, 0, 2, 2, 0, 1, 2, 1, 2, 1, 1],
  #[1, 2, 2, 2, 2, 0, 1, 2, 2, 0, 2, 2, 0, 1, 0, 1, 1, 2]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x90900034440290322050c632386375, 0x303ae00ab390144c2871188810008),
 (0x1816978438628c4459f20420458ee5, 0x238848434009138aa20931cbba1110),
 (0x64b031801af0c31c21aa03490106f8, 0x8203c61be00300e3480538a438c105),
 (0x62a0404c1030fa9c530300c0432540, 0x801e818221800003000cbf0c805029),
 (0x324d0bd06d1a3c200800081f29045c, 0x8032a00810e0031034db8720d22302),
 (0x812006268a181844054282048aaa88, 0x2edbc1997041c3b052886952300404),
 (0x40a2d7f12a8c40328080101882068, 0xc1f51080c4412814850764ce649203),
 (0x8024311341c8c290221c11c29f4943, 0x2a8986848e2109211d814c01601080),
 (0x1444300a8c80c03a6ba0b64a0dc230, 0xe019c0a1234a3f44841508b100340f),
 (0,0),  (0x97826270515a20668a8964c96ecc6d, 0x4065918d08a0430151368204011312),
 (0x95519d041490840e01c1949bd74256, 0x2a2402a80a000b10662e4b202835a9),
 (0x282113a38720840496208212011128, 0x5184ac0848430b8a610c0c6056aad5),
 (0xa968a6d420598608c9c42e04108820, 0x428648021ba26857202bd10b2a75cb),
 (0x85ad0010a04a88f64086a851c9e615, 0x7012ed8a50000000206951a8041880),
 (0x80101158102144940100000240c0, 0xbe60664ca4e0c2ab489a6e61242d0b),
 (0,0),  (0x61cc1819b1322129c8f03a211d05c6, 0x8c21a280444998923107850c02d238),
 (0x30610a085a6396542171181963c6a1, 0xcd1491d42400608b5686c744801016),
 (0x4452f426ec00519203254550219b8f, 0xba250359111aa62d749a38229c2030),
 (0x3098ac18824a8000e2006124246001, 0x45034082251028fa08678c53490ed6),
 (0x19b1d648862a0142ec6d80541a80cc, 0xc004018410c0ea3901803a09800d33),
 (0x4268017f504188cf0b089b29494ee9, 0x8806b0802488300054b04452869112),
 (0x4c9aa851711a404c0a2cec06280b5d, 0x3060572a0cc0be304490016890f422),
 (0x1008909d8830c28a5012b0ea6620e4, 0xc4d3672225ca09342488041098df03),
 (0x9080007e223542227c70920440f04, 0x32b07f300000a9405030041db81028),
 (0xa784054107016c78210d811085906, 0x81060128238368183d8a2308e420b1),
 (0x4221c00312119e090b5401205a6a0, 0xcb15e200c408200f46481961a05051),
 (0x88c320000a0004c8531540a4aa2081, 0x54181d65d103b3038cc0155211074e),
 (0,0),  (0xf05e70ad180043940982b0a1342502, 0xd000b00c3a3200a76610248880204),
 (0xf0a188820410018618804409d29890, 0x64c244c7b604c31207511240c2068)],
  #[
 (0x7335a010321545c112088102d0b0a, 0x68c0840a709821038e5e372300c4f5),
 (0x1e0892005520b1e1cc20121eae2e00, 0x20d060db22c300182304412011503a),
 (0xa2106011b690480393c65d420282a2, 0xd8818e2016aa7100c29a288f92811),
 (0,0),  (0x8014888613dacdc0693907e06d1142, 0x44613018642020199444801202ee0c),
 (0x96520b29e09e41331c884020888b1, 0xb6125a4140e218a80e116bad116108),
 (0x520819a0fc23b138ac6908451c0486, 0x2c76660a021042c01110e03821b030),
 (0x6c780188994004db3924009700a024, 0x1103c67044b09b00469a3748ff0f40),
 (0x94c5d73d1e00408491cc0d10161c70, 0x6b120802e14a9f280a12b286c8838a),
 (0x770986e010d1a08e89010550498612, 0x806429174e08533112a830af366969),
 (0x403610060151a0b000386240574db1, 0x318087013228534850c0088f08000c),
 (0x186bac0e5889954758073540710c9f, 0x440040a084522a8025588aa90c9100),
 (0x310007013228534850c0088908000c, 0x40f6d0060151a0b000386244374db1),
 (0x240050bacd0999670433588d180b91, 0x5ea34510f200181a0ca63205f42a),
 (0,0),  (0xa0200f0941081a2822c4290dced030, 0x1613f0d69ce1a4571028d6a02028c7),
 (0x30060e3444000613ac880529a18a00, 0x684102235af8e452366a944665da),
 (0xc04da2420c810808c12a592004266d, 0x3a3259142268750304c526d0f81810),
 (0xa58115804200b10686348491db448, 0xf003ae23839384ef17901404a249a7),
 (0x8032a0085ce0031034db8720d22302, 0x324d0bd0a11a3c200800081f29045c),
 (0x2100910440c243a8c44223a54056a0, 0x42560ad31439385738845452aea803),
 (0,0),  (0xd4d0041a02400a1bb2800c0e170063, 0x2308c3412d9094e000578150a82604),
 (0x53c230462100a4048a024c10849025, 0x80158c8884c002b310a8108a43604a),
 (0x9220a6bb12e9284331c1d132028651, 0x91e1144cc0254900e162a44187804),
 (0x440f00c2b092922606f841c04e38b, 0xf1a30da1c422445c8a8068a3630844),
 (0xd45947002828149009800080a7b61c, 0x2a04000651418267645cb2760009c1),
 (0x40218c140871f8ea0800812854204c, 0xb59411404488060460bb328022da03),
 (0xa141131403281e4925901641a5382, 0xc021e80eabc9721829043299418035),
 (0xa58145814200b10686348491db448, 0xf003a223e19384ef17901404a249a7),
 (0x20341b3ca00c2d466ac65a28c4284, 0x8058aa4431ba392380418814108c58),
 (0x40140807e429b3df234310121068b1, 0x382110a8195204204028c364649204)],
  #[
 (0x86656138500520522694320417080, 0x8508a8887abaa9981d86189b960a04),
 (0,0),  (0xa020000981081a2822c4290dced030, 0x1613f8a63ce1a4571028d6a02028c7),
 (0xa020007121081a2822c4290dced030, 0x1613fc8a50e1a4571028d6a02028c7),
 (0x4268057f504188cf0b089b29494ee9, 0x8806b0802488300054b04452869112),
 (0xc0c00000000000000000000, 0x0),
 (0x42220021408a14220133452624448, 0x31c50d692bb10895880c8089018a03),
 (0,0),  (0x4aca220075c2902431440020932ef, 0xf841099ee08240f43cc11dac54c410),
 (0x8008861329252970008879481e0c3, 0x311e110ec9450d20b9b70008361c34),
 (0x8905828fd09d5005c080c38d9900b5, 0x70d2514024602ac833471c0240a408),
 (0x2a0089212000255400c6184214cc09, 0x9518509e09b6d22b9730403c481010),
 (0x42680173184188cf0b089b29494ee9, 0x8806b48c8088300054b04452869112),
 (0x4d314101284d0308663050960540e, 0x70208389c94b0cc7100082c6878b50),
 (0x10892261c39097c890a02092306821, 0x43748504342068324a03d84c44854e),
 (0x2d003a06433c380040944cf3214920, 0x804e85683442048aa2091204c2a0d1),
 (0x8290302c244809c4241680198a0800, 0x402ecd530017a61bca616b2201070d),
 (0xc85195ed24648c424061080d06630a, 0x16ac4a1000085031238c61b0981400),
 (0,0),  (0x7068c500532340a061201038200120, 0x8f86103188c00641968e4903c3368c),
 (0x97981a2e8f527ae4226b8228cc4890, 0x684320907089011204046c9701350f),
 (0x11cb500c573e20601823866801233, 0x4ae100a0388018e89c1c87910a488c),
 (0x980d283400106e298ac05590808121, 0x75215025b009006103728217d1450),
 (0xe06133c4fc30c8302a70a09042a11, 0x138c4032020a31c390800a4d114e6),
 (0x1ee6145543a05612b0045250020294, 0x4118a828941020680b9921a95cb008),
 (0,0),  (0x85c903d6390d0807044a0182724c, 0xac6210d0280282c1d0fb9400450992),
 (0x5a005a9c081a44128d80600044a59b, 0x80db0123f460110d60598328ab5260),
 (0x804349465140242a402d6801178107, 0x2d30808908800a4132c205fae818d0),
 (0xe00007118083105e9c89c348040c19, 0x1e6eb8e06820c4a0225410b4c1d080),
 (0x8032a0009ce0031034db8720d22302, 0x324d0bd4211a3c200800081f29045c),
 (0xba0840992e89362222805b01da082a, 0x41862124913240484c7920b22523c1)],
  #[
 (0xea064a8310294d24480502442d8b30, 0x1418b51061d2b012b27ae5934010cb),
 (0xd1f0094024295393688c005f0031bd, 0x2a0882b408d2a04c8772be20160a02),
 (0x2533046147926a82044f36a088745e, 0x1080900428298045a180814b718100),
 (0x929c226e442081224080838560520, 0x2684099018a96489c055b481898a0e),
 (0,0),  (0x1613f0d69ce1a457102816a02828c7, 0xa0200f0941081a2822c4490dc0d030),
 (0x78288a10089c84403258b18164a41, 0xc83d4000e85236ab8c12602749b5bc),
 (0x4cac8488621002599640401d3ca621, 0x5139720523b5a661079fa2820844),
 (0xd231070c31224400805c442d69547, 0x7258048c24891b9d45c81299204290),
 (0x90192542a8a20210b000905041, 0x81d600408ab90100a52903fa2d230a),
 (0x6344abc9810a1a215e842cc902aca5, 0x1c8900223ae004d6a13bd222281140),
 (0,0),  (0x826451100002035186860a4022a04c, 0x3119224cbe55600a291160044d48b2),
 (0x812a80893cd44e8820060f4477101d, 0x42055340402b016014a06010802d02),
 (0x7042008ed481b58c8e135e35908011, 0x8c1d14400244403030a821c24e4fac),
 (0x80502829c586a808a8801a84a19100, 0x7e281452127812704233416a582800),
 (0x42680133384188cf0b089b29494ee9, 0x8806b08c8088300054b04452869112),
 (0x511e180a2a4265f0062a3518943402, 0x2240600045ac8202c01002e2084a04),
 (0x22106db1b2b3430091382550a535de, 0xc46682484d0038a32801d82448c021),
 (0x9c355810802848e1713a844100a41a, 0x41c2a14d5101020c8cc13982314b04),
 (0x8c33160d82a08586a9001f00e4bc60, 0x108848a24c1a781902afc05a100301),
 (0x23055441902a128c40c50920cc0467, 0xcc2a29800a10cd411e30b0d9219808),
 (0,0),  (0x180004ec840244412656096c0dea05, 0xc23e80130239812809a1e011a214ca),
 (0x2608428542301b19611f020851a4dc, 0x9160970044a24c284e009c6a44223),
 (0x7469a668042338346e0004bbb5e8e4, 0x8a145902cb10430b900de30040100b),
 (0xd981a0119d56f41553173d22d21454, 0x634464a2080038028c8824520ea89),
 (0x90900034440290322050c63238a3d5, 0x303ae00ab390144c2871188814028),
 (0xd2700f100085f2bf71340553008228, 0x21880041e6220c008c00e0acc55810),
 (0,0),  (0x52aac00c0538a0c30134a784c48445, 0x891511601a014214548950580201aa),
 (0xc08a10010348f01e08b1400a4128e5, 0x305e8d444110f40b0461314b0d008)],
  #[
 (0x401d28cdb12a915b2203c044812ea, 0xa31429120489528248c500e0030515),
 (0x149640541139c27231031600186244, 0x2a60b52b464210810e1c48a0809420),
 (0x8806b0a04888300054b04452869112, 0x42680603944188cf0b089b29494ee9),
 (0xc9a487781cb10890c2244f81c08852, 0x24960804108a1480c53100e15408c),
 (0x1cf5087fc8200c18461009d9086124, 0x600a3580208022a03964640041060a),
 (0,0),  (0,0),  (0,0),  (0x8c8a88383a2a1083820843926141a, 0x9706067460594a5083596ac009ea04),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[12+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

private def rows : Array ℕ := #[
  8, 9, 10, 11, 13, 15, 16, 17, 19, 20, 22, 23, 25, 26, 27, 29, 31, 32, 33, 34, 38, 39, 40, 41,
  48, 51, 52, 53, 54, 56, 58, 59, 60, 62, 63, 65, 66, 68, 69, 70, 73, 75, 76, 77, 78, 81, 82, 83,
  90, 91, 94, 95, 96, 97, 99, 101, 102, 103, 105, 106, 109, 110, 112, 113, 114, 116, 118, 119, 120, 121, 124, 125,
  132, 133, 134, 137, 138, 139, 140, 142, 145, 146, 147, 149, 150, 152, 153, 155, 156, 157, 159, 161, 162, 163, 164, 167,
  174, 175, 176, 177, 181, 182, 183, 184, 186, 188, 189, 190, 192, 193, 195, 196, 198, 199, 200, 202, 204, 205, 206, 207]

private def reverseRows : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 4, 0, 5, 6, 7, 0, 8, 9, 0, 10, 11,
  0, 12, 13, 14, 0, 15, 0, 16, 17, 18, 19, 0, 0, 0, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0,
  24, 0, 0, 25, 26, 27, 28, 0, 29, 0, 30, 31, 32, 0, 33, 34, 0, 35, 36, 0, 37, 38, 39, 0,
  0, 40, 0, 41, 42, 43, 44, 0, 0, 45, 46, 47, 0, 0, 0, 0, 0, 0, 48, 49, 0, 0, 50, 51,
  52, 53, 0, 54, 0, 55, 56, 57, 0, 58, 59, 0, 0, 60, 61, 0, 62, 63, 64, 0, 65, 0, 66, 67,
  68, 69, 0, 0, 70, 71, 0, 0, 0, 0, 0, 0, 72, 73, 74, 0, 0, 75, 76, 77, 78, 0, 79, 0,
  0, 80, 81, 82, 0, 83, 84, 0, 85, 86, 0, 87, 88, 89, 0, 90, 0, 91, 92, 93, 94, 0, 0, 95,
  0, 0, 0, 0, 0, 0, 96, 97, 98, 99, 0, 0, 0, 100, 101, 102, 103, 0, 104, 0, 105, 106, 107, 0,
  108, 109, 0, 110, 111, 0, 112, 113, 114, 0, 115, 0, 116, 117, 118, 119, 0, 0, 0, 0, 0, 0, 0, 0]

end BasisSeed6

namespace BasisSeed6

private def row (s : ℕ) : Fin 6 × Fin 6 × Fin 6 :=
  (squareCode 6 6).symm (Fin.ofNat _ (rows[s]?.getD 0))

private def index (i : Fin 6) (j k : Fin 6) : Fin 120 :=
  Fin.ofNat _ (reverseRows[(squareCode 6 6 (i,j,k)).val]?.getD 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
private theorem covered :
    ∀ (i : Fin 6) (j k : Fin 6),
      (∃ t : Fin 6, headHit t i j k) ∨ row (index i j k).val = (i,j,k) := by
  decide +kernel

private abbrev Check (s : ℕ) : Prop :=
  imageRow 6 6 6 8 x y z inverse (row s).1.val (row s).2.1.val (row s).2.2.val =
    (2 ^ s, 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid0 : ∀ s : Fin 20, Check (0*20+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid1 : ∀ s : Fin 20, Check (1*20+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid2 : ∀ s : Fin 20, Check (2*20+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid3 : ∀ s : Fin 20, Check (3*20+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid4 : ∀ s : Fin 20, Check (4*20+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid5 : ∀ s : Fin 20, Check (5*20+s.val) := by
  decide +kernel

private theorem valid (s : Fin 120) : Check s.val := by
  obtain ⟨⟨q,t⟩,rfl⟩ := (finProdFinEquiv : Fin 6 × Fin 20 ≃ Fin 120).surjective s
  change Check (t.val + 20*q.val)
  rw [Nat.add_comm, Nat.mul_comm]
  fin_cases q
  · exact valid0 t
  · exact valid1 t
  · exact valid2 t
  · exact valid3 t
  · exact valid4 t
  · exact valid5 t

private theorem spanWitness : Spans 6 6 6 14 := by
  apply fill_basis (by decide) (fun s : Fin 120 => row s.val) ?_ _ _ _
    (checked (fun s : Fin 120 => row s.val) Fin.val Fin.val_injective x y z inverse valid)
  intro i j k
  exact (covered i j k).imp_right (fun h => ⟨index i j k,h⟩)

end BasisSeed6

private lemma square6 : Spans 6 6 6 14 := BasisSeed6.spanWitness

namespace BasisSeed7

private def points : Array (Array ℕ) := #[
  #[0, 2, 0, 1, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 1, 1, 2, 0, 2, 1],
  #[1, 2, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 1, 2, 0, 1, 2, 0, 2, 0],
  #[1, 1, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 2, 2, 0, 0, 2, 2, 1, 0],
  #[2, 1, 2, 2, 2, 1, 2, 2, 0, 1, 1, 2, 1, 2, 1, 2, 0, 1, 0, 2],
  #[1, 1, 2, 0, 1, 2, 2, 2, 2, 1, 0, 1, 2, 2, 0, 0, 2, 1, 1, 1],
  #[2, 0, 1, 0, 1, 2, 2, 2, 2, 1, 2, 0, 0, 2, 0, 0, 0, 2, 2, 0],
  #[1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 0, 1, 2, 2, 0, 2, 2, 0, 1],
  #[0, 1, 1, 2, 2, 0, 2, 1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 1, 1, 2],
  #[0, 0, 2, 0, 2, 2, 0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0, 1],
  #[0, 2, 0, 1, 1, 0, 0, 0, 1, 2, 0, 2, 1, 2, 2, 1, 1, 2, 1, 1],
  #[1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 2, 2, 0, 2, 1, 0, 0, 0, 1]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x394b440013c0c0bd6c1a121085423815374c0c308680013, 0x6a0a9164c1439021181c0c57821458888b140c77117d48),
 (0x3341252200c0d407142d0a00001c0a0b0150022010808d, 0x4081205dc3f2228a95051e4d3802554faac2548062642),
 (0x2e540e0125c601459a16480034b43051494081198050425, 0x120b19e0820da9820e002650949c72234394ca44ca6a10),
 (0x1504562c78491400408044800b093309c291500d8019202, 0xa11a890879283a3a71eb019a40444b01926a1b04504494),
 (0x2115053288e4e03901952a37a6a42388085b0b18e9d80b2, 0x1c60520140091342686800c0101b18519100e463042530d),
 (0x270382c874486423049940182a1b842496a0109307033c7, 0x18485d008b3190d84364b6a4d5804b40404e2a04e004428),
 (0x20c04cf35c4b4405c0441080210e01413ae0a90403c280b, 0x1d04220802901102061be52b9a604e06041f469a30186b0),
 (0x1013991b106012d1004977789523019edc2210163b8d4c1, 0x8c40e0eb186920593600076200e26123042da1406081c),
 (0x1c60682f822926899c79a4b42890845154c3f16ac9042ef, 0x38715003150911222845a41444f1324011c0c01122a500),
 (0xa48420d094a174629a081a654b70c80282bf9582a50434, 0x208590e0342829401a5e598940321693800403c0a410a),
 (0x2102b0045412e010409340965298da3bc7000c124861b03, 0x18e54ba2ab2917483c602a212964040010ae30a8b6900f0),
 (0x75ed104440af8696840fa030ac93d450e4cdc081000, 0x8390a0066932a10582153000b41106422250900365a8c8),
 (0,0),  (0xd0087284a65cc985082081ed7d34091031419810516008, 0x2a160c700820001255103a10828a2486043004cbae9e51),
 (0x1181880442051b80cb36bae09500a309ae989c2044104cc, 0x2e1072428d2a606c14c1040360274ce0510041c5b242831),
 (0x46f0409284558446546a0a119085090801b14b6dc2016, 0x2b1804056143a20a21800564e2424a04b37808809030121),
 (0x1106852b22a0a62d10e096c852e1920a84c1a081a40404, 0x2ec300a14494f515282034101a0026d80583e143813d3fa),
 (0x20bfd258c2001438a9a505006b2240a4041a03208700e00, 0x1a402c843db38107165262cd90c40f0b21e0cc16683b0a9),
 (0x25088c1402a108b0a051430851603c04819be001d18c982, 0x1ad0424b410ca40c428438010e13432352441abc2011210),
 (0,0),  (0x105b75a0b41ac58a9601c8b04108a4c29300660a3823b2c, 0xd00800f0bc40a54096826460413093c60ca80c4c3944c3),
 (0x2100080a085795c75002201412d3130008000c4005e448, 0xc2260630f30062282f415c0aed2048417741a32a280217),
 (0x112204088509090a04783360509b42214ada9688d011010, 0x4489a67014b0105a02080da3641d022400016021e28a5),
 (0xbd38524641ca0208a16c4c493a0413600d31424050606, 0x1a00840018b81039f7080130224122400752843080a3911),
 (0x85493484487c857081c0440518c80316406c3a488cd39, 0x1c70944b030001080e2432b2dac310d4292702c5a7300c6),
 (0x208060801342016a221e9014aa5001742c8c359aae45090, 0x1e76013b8091509494e068c95185548b921280011090523),
 (0x1f4c87018cd54dac18809683001e46010b9050084044102, 0x20a328dc330a00032534216c88e1b934046bab84941b2c0),
 (0x101ca8800a30298aca104038a0ec94880c948000e2681aa, 0x625049c14b826411caafc305030b54e263689f1d80414),
 (0x31000661944680a594253e3438f420506040a4b3485ca56, 0xed0481e68a119582a424009c4099125962703481123501),
 (0x10244916ea75c41084e50441094490522059a0007622a86, 0x201b1061158a32244b12bb2a80b22f88c9a65dc388cc061),
 (0x823f59a95265984d1811186101420911e60601816401d0, 0x32d0004448d0800a0268ce3148809b22e111932109be025),
 (0x3e142a9056c29888c8888aed18f219375028091f1302020, 0x6081298808424616376510c20042488ed57600e478d12)],
  #[
 (0,0),  (0xa2689005018d71014348400090e40e28650256f521003b, 0x105016402e2420e7a04b7aa76071131020075090208dac4),
 (0x12ee2a039cd90524500c100320e1d9248567055148050a8, 0x2d01808000065a49acc3ef0c4b1602c9108042208488f11),
 (0x850b782400958c0119c82d2649c6001a20902d230c4008, 0x31ac4829b442241aa821580c08628a70182650280c03b12),
 (0x12a28390c01c09928188813511b70506118ca0ae3011030, 0x450382d1d20c40508535ac8460092582c210740044a8c4),
 (0x1411067c634a3010000a302f49840c41869740c102aec0, 0x16a8c318110b489071b0443808601939e2908392a255002),
 (0,0),  (0x2cb41131102759062722aafe2981ec188309d28b532320, 0x1800a6ecace408658c8c84001460a01867cc20c14089882),
 (0x32d344007100f111708090b10ec8ac98d5b044e908b601a, 0x12022de843202cc0d2f6344e10503220a481806f0098e0),
 (0x40828fc94430540f01522008da64a81cbca02aa2c893ce, 0x19905701498832240ce80c424249a53a2430fc155114c00),
 (0x8a42181028022055504a00694a835645e51429988409e4, 0x1619181e345c01da80484c284045ca992184b16413a3001),
 (0x2624ac8e8a00021a2440120cf0183801394396a29031048, 0x18d00331043978c590afa8320882800a022049092a8a224),
 (0x13400682ce58996b54aa44e180147198007231c408d2569, 0xc07c80d110326940300ab1c180986451a80ce294228896),
 (0x4629896252500a4a0982680054da4b6762034a3011508b, 0x1a88416852d27c4801219843e2104941881d8b505ca8f50),
 (0x186c54a020c501a39c4b1cc940414001221010b9d02801, 0x2e381224a0318021062100232b0281f788c816006000376),
 (0x10215478a55401cda31498280c5afa0c012653632037860, 0x45422010289b2225c404016b1a005d14c1124845c4030c),
 (0x4a099a243661a27110a6143c4bea22217005027000e0aa, 0x19564444148064d82c95962011014959e89ea150f771900),
 (0x1c37820cd042a1134a60e0389f160a0a9738818644e42, 0x2d03805de32b9d14a014100ac04068504128444461a8005),
 (0x712a14245b214c0e11911046f26a890f23d00100c15202, 0x20815499a804832e0ea6e01190d047430c42ed852108ca8),
 (0x2e80114084202098d4484224280cdb0480805300ba8a280, 0x16fec3e78589a420bb20d0a9792203a084a08804550d39),
 (0,0),  (0x1d0828d119668fa5320828044560cb2522521c6831c1080, 0x96870ae69170100966854ab09c34d8892143914230009),
 (0x2010e1020008b4239f811a014ee68252d32110e600a0d1, 0x30c830020a07743d4403a4040a010402404c0891946042c),
 (0x127a30228568c9ea85a85208541d0089708ac6220680080, 0xd058e492a8334017857a19080629f520a450880c96fe0e),
 (0x3088900501283224507211020281260f20b510069a3432b, 0x76064cada4780d90100a8c96d04d0a0c240c1d104c2c84),
 (0x20fd586528385108009f74149208404a12c491860d0100, 0x14702a79296418ac632200b0a4cf232b428296221c2a611),
 (0,0),  (0x17081ca8bbe08004c0460ac80040590b0b590b294364a0c, 0x28a7e207401215121531f523372a04a0d426e45638924a1),
 (0x10639c42821c018d0fc9c44e0a2b649c4825a00914c801, 0x28c8c23953560aa706012102051508041949255f2c1264e),
 (0x216483a012809206068d323080980e00685ab402fd956c0, 0x140a081dc17b21008862088b0b2191e9042108a4004a831),
 (0x20201213cd6111169b39312411431b1e02817230004a805, 0x158d20228e6c004404044226242460d80c8903a0854da),
 (0x513fc5065c478cca176405810443588025850211574042, 0x2200038c1a108512540095240e134a709185a0084a8bc11)],
  #[
 (0x242fa484140818d5d42068816418a32a44080c48e100507, 0x107a603706002019957a9b6608c493d1e08706fd0e8),
 (0x19a1a10b8211820802319cc0c0a0409000962042d615112, 0x61c1ef40da221f5108c20362f1c9e40b3281935200a429),
 (0x1b77ce4ac01c24af1928471400053400810121048240451, 0x480019110021840a65218e388da409474e25e7a10aa9a2),
 (0x13c80040203860024204148a908089208081141979c42a8, 0x2014eb2f100017ec81b8eb602134041e232cc1a6023ac57),
 (0x284122da0028a049280e478c9186a12740b287444251842, 0x60250045a920c805451006040001e081f4d688a1d0a038),
 (0x320b6740520c81c11e0261a6180714cd38c8143f340040, 0x1c8c000be25f35224c0e4841000508812c2156280c3ed2b),
 (0x1148957d01310601108d9280d38901e842a132214338396, 0x2eb500826ecc6990a732042704365e043d140518bc84c61),
 (0x3865116180281500840d45820000a26a2b88090096a050, 0x8218c8125147085660602065f9b60c949475e4146957af),
 (0,0),  (0x235c80c454b27a2f7086219ba3300d42088004360914003, 0x102322000b0c01008d70960448c3d089c12d130040c8cf4),
 (0x1859a548bc208c008b0c0948ca0064c4540ac880881809d, 0x7a04a24418e724674f3849700ac08212110211f33e1620),
 (0xc0441808611149220a180250029323854800c2494211f7, 0x23da865d60428b609b0214882f14088680172058008ec00),
 (0xd4f92262448b03336c50338d14a08c53501541d0111471, 0xb06cc8c285090c8122288322a0d32008b0828024a228c),
 (0xc594a45003ea91180c004034409088220e1534616028a8, 0x104819230c000467927123428d2327c51128c392119115),
 (0xf61888261035c5c0484c0c22359003091098497019a04a, 0x30166429126020217a13290c0c22c983288638202e05e14),
 (0,0),  (0xe8c44a0d42164089332ab984893de3098216a80405d50c, 0x3153a3582bd8180048c4140035282109469a905e0e22282),
 (0x22000001011e4c766018c9887068864ca83a26a1360e650, 0x5c11e2682a1a100186626210582682246c10954c8e1909),
 (0x2810800c0809a642ca925084d0809d880c1b2305a0940e2, 0x15ee7ce385e2480c252c252b253d2253624018500129305),
 (0x7401b029109121a68200498170400a0884c6d70001d7d2, 0x300820244a24ad848109e20428d263436592900762e2828),
 (0x3a80b80365247a18428815120440348850c0388582e0000, 0x46447700adb81a48125c820d3120a53af3b81124911bc1),
 (0x7a1141e240133d4e00db10205208806d0518310814cde7, 0x180ae8a0819204231da20204a88152f908a648e21c93200),
 (0x9b71a469bf42762250887d1b3285ec0200228192476489, 0x224820806409800d8a9058000000202796e91286da88114),
 (0x22441029142c17416d06836100092851b2cccce04401d45, 0x10180494e100c82802403814b782942e0c10010aaa902b2),
 (0xcb0722a11a0074b0a0845114d0041c758164069a05249, 0x3704f8100ae1ea0a090f21088b28bac10a468b8101a2920),
 (0x2f004420ce06442a2e5290046320e0867bc5a400640a946, 0x1079a9130138239011a1412198061a51802a088891942b1),
 (0xc42340324516084441a202d1020898188893448581354c, 0x112d0a3042a2974220a455900403260c16644a968020ab0),
 (0xc1487000588d050151704948c2594d8248926120332945, 0x322b5810a865032c4ae8e108630243004060d8c4bc096ba),
 (0,0),  (0x3d28475af09548d4a04c40c14681d2c425e0b4805c42c05, 0x20290a50362b1220583890298622828181e027c201514a),
 (0x2754614592900546da1054a88a88c0492123dc054f466, 0x3390a8862a4d0d708824ebaa5144012fa6561c23a210989),
 (0x32c25e8004570d012d08d44d04090e5285825302c218440, 0x104213a5b08906a82b50a1062a2c1804a7ca4083042b0d)],
  #[
 (0xc28f8134f90701898119e60400061442480025208400d0, 0x2c406c8106f848767e8618318199a9a1a55dc88f71e30d),
 (0x18a241937a9000100e78a82f050a33018751c1d1032694, 0x1454d044881483b47e0864790ba510c2238a0282cd80828),
 (0x180206e00a6a8ce4e405a39045e4082825285a3c5041274, 0x20d838176105601a1a800863b2083357405220c1003c809),
 (0,0),  (0x2a23802a0c8e4255646e2043de0884001b4ca261018019b, 0x10102345b1713c809010d18c20b10a290493559ad63b064),
 (0xf0298b40b01a5442db51008000083010051100e2022130, 0xb00409206240b992482ec171663c9aab0442909859c42),
 (0x11d40780005c28099280f4408441024618ab0ed10a17da4, 0x2009086f35039620416b0b0a132a49b96310910c2068003),
 (0xe2e4c0d541011655880b802e0920c34065200590254062, 0x3111b1d203c0680a0042071d0369b08b49090782cd2940d),
 (0x12020610d892e610103034168001930ae00004305641003, 0x4e521270420112a4d0c0349606e44c01a6528c5a0385d8),
 (0x10020015040e83a99440f16141bcc7a901bbc9980995041, 0x2421cde8bb302856098004901e0038546c001400326aca6),
 (0x314410925201101a1189101f943206823ca04420a585906, 0x2388a0c001c6680ee4629404ac8380442120b535248200),
 (0x34088418270e91600032a541008680f21084a9507048, 0x12e09d2788550304612a5040a3ee8580501ee28062f8731),
 (0x25003602231d623320000b01f44039013e0281c10acd112, 0x851c048d0c010484c091040030a063c0038281a54326e4),
 (0x2887694a336090009647056881118e9dec86441c2af321e, 0x31016b0c00c00d5208050042eea316213589080c004cc1),
 (0,0),  (0x3a3501378c0844a000958c662b11100604ca91168290210, 0x96003387a855c9683100902206b0a30542810829921),
 (0x3585cdaaabb801a3884df090080403280a08e2a298e14c0, 0x232551002f41833300562e5b398d1b0c20909451293a),
 (0x9008a8a500654e11cfc900904858144014522283482008, 0x1259205121882a144201651079123881f42a54504248b55),
 (0x1601e0e065a116d22031de40007030002369a4f135cc032, 0x1cc181a9a1a810894880015fd8e4d3e1c920102400330c),
 (0x31681468600f0609683c60429c061245058742a91e8f121, 0xe954103101048e690438c996200a8aa8270b8460000ac4),
 (0x1141a0b124800c02cab019042585281216600d848080c88, 0x4004d0ac90ff23d154bc293004816450883f2394e1f132),
 (0x1a09aa69706421868433a10112401cb921b5085af0a42f8, 0xb415040701044022c0024c2da42000dc4aa7840d41907),
 (0,0),  (0x1c26d334005c818b5109f0439112206920484a9118004c4, 0x214904caf6025214884408344c2d80165b27940ec03e212),
 (0x58331d4aa284ccd003a2d0180903006cc8660094843182, 0x1278cc0a45932100e10400884f03c089311988241130435),
 (0xf826850ea211808a1a70a80294268202a31032880ca849, 0x300080ac144e62675a00643596a40402804494d272044b0),
 (0x288c0066221224c28c140522080948081238b008c2c81b, 0x2153387189505920931ea721432c62043e9c205562532e4),
 (0x3bc710180220205520a842429a88c064892a38419080054, 0x2868a05d1217289701b1b00116330026150438625332a),
 (0x20d3d4204d99814314340831484020e0805da2c700ceb01, 0x1604015680026228abc9478085b780111e804438af2043a),
 (0x201e1c018408d9002882ae04445806210023c80024300, 0x181fa08008501204878638118b33800984a9dc129e58402),
 (0x21012b211a0600a05a3ef08270583585c45190a901aca77, 0x14f0001ae4d1425280400e340627c04a030065440a00100),
 (0x2c0750e8a112012019400a095000202c481400213a03112, 0x11e8a5160049a6cb40049400803a8e52048acbde41786a1)],
  #[
 (0xa2b08a094716462a8b2c020070e940040219192390a4a9, 0x204022492288909d12092c81507100398056044d8065950),
 (0x2044a024244381a00802d440106020816094040841ac050, 0x1f221d5210b0101e70252a0f6a94555e134051470840b80),
 (0x1511a088bd8030b6400186058eac9c308798007455881f5, 0xc45806420b8a4094bc18200151000f480131080042802),
 (0x36528a931813f41ae4a9085b382118400820033293e8072, 0x2d1548658c02041814238447cca4a3c48070cc0816684),
 (0,0),  (0x101100e14d054174885ec0620050815c06ce4e462801d64, 0xa06991810a2aa8877812d981d8f1202801021308098280),
 (0x2e4a1f1108a70a46f5f8e427141b1626024dba600a4a050, 0x11a0487608912802020bd8ab40c840a122008220003ab),
 (0x1a8196338511208c4690108c78c05e56381b000002935, 0xa214e41487028d270382a2713870380288404273d75680),
 (0x391184804e1c4e00b0c588a0119a8402381a068d900b207, 0xae1b15110321a44e227149a66143ec07c088400e04138),
 (0x143435a813dd444a601495a26c460001ae45e00924b0d21, 0x20034241ec0208211e010a400131e8ee41801fb05803250),
 (0x1068ca01928c820c101d9214e68a000401a05100108e502, 0x58705a445411ca3acc201221940ed796e55aa964621078),
 (0,0),  (0x2b0b6488306080d817680657896301324a9144821b8060a, 0x4c48141470871228011e0283090f648016a11502465151),
 (0x1c0e913088108b0986088e8108c83d172387c4098a84010, 0x251428e0340600678c27066f212c0c04c7002e6210848c),
 (0x2438d9524512180042078048281560ea001490e80438800, 0x1a47240988a520c218f8380053e2141101020b1779c61db),
 (0x2400c49281a148108882441c43206b05c6985503c8929f0, 0x199a1961504eb7ab6351b0611c1b10783024a8303344401),
 (0x1a04a2830b4005412290e823087249290f20645000320da, 0x25611c58808628288568050857882486209f1a2f57c1100),
 (0x1271502800186222b5008f9c8009481f1021004490ad01, 0xa40aa34498619899480d40006e5630c00a82e39142107a),
 (0x24454e50000e48a102617c1200456b020a0b05990026148, 0x1b08108d9b619146151a81040290905925006a440018680),
 (0xb028db22a45c8a8396f04004000972210910b47c8606, 0x195068120dd5321014c610285c146c2055c5240410278a1),
 (0x2044c2392452a8a480469454013081b1180b80043d50110, 0x11283dc4da09434316290b006c82604a05e45a3002acc6e),
 (0x1800a29966011f109219304458f819218f0edc2b0835a9, 0x3e5bf5c02907cc0082d8404082207068810f02114b64a12),
 (0x180e6b008421020825ed7dddc93bd00a0008060f62544aa, 0x2721846171d4dd7258020002124020a41b8441608002205),
 (0,0),  (0x1a8100dca0f9ec888358426698047a83102c090bec04a17, 0x50ea4205f0402564407a10921398100ccc3d210128a0c8),
 (0x102069404a8b90402c0040bb00084080182104d40854010, 0x29b82320430448e519421447841237122144a0b072284d),
 (0x30240422089810002344080ec056420bc2a234851c26018, 0x3003a04750045769088d1f03fa00d20354d4b6aa148583),
 (0x183b08c3002c42a22f46104c005988e2944cc0602289310, 0x23c0d728db932d5450b12b83a68215140922119f1c64c86),
 (0x86618ba4112a6380400be81864f4068815e527600e005d, 0x61946452aad41422b6b015e3830bf0600a12100700d0a0),
 (0x204811040746a316209215241a99008fc81810249c829a0, 0x416ccd9800154e8400d22da210234603381059a2155645),
 (0x251af066103290a05240a10525c50003405a5c00c89487, 0x2d0a10c8867c96a4905090a68401aec301500a0fd372960),
 (0, 0)],
  #[
 (0x1665a400388320c2c15484668a8000061888a309832248c, 0x218a0ab9c054463418a26a81004bd3c9e14140824819a40),
 (0x3890522241c41650d30418330301113093c1bc6ac128631, 0x243811c8c3bc0a124f0c10418a68a0b680a03901254144),
 (0x63a904e01e30250ca3d190af081180284a054038222802, 0x10400330501041a820026000093e03ac321329f01d95041),
 (0x1c8861140c01896d0768f008601e8303682460a729c86, 0x21203798237354449000170bc484c120f0129a0340c6238),
 (0x9e5c1a989608e09e0001c0094b3100c0e3ca80a08ae829, 0x16123c00648951500b24c3e522446092f18306b59040744),
 (0x16021d0016a0b2668282224d84611d02a528200447c8e22, 0x20c0204b491c0408601d40b00216e27d120541e3881309d),
 (0x121ae547830318a8c0034ea2c6c830a609a021244210502, 0x5011aa0740005100f38911830124e5914049c8a388f210),
 (0x2620a848520a0001c998021044022210c26186390f2a481, 0x84342a3281062fc1004f062b3b4988a019278420081302),
 (0xa28600004e142020b256c412201021a6480289002404aa, 0x15d30a95c0128d29f44a0096dc1469a103729549d03f155),
 (0xf8944e006a94027a14816af01c80868a60852250042108, 0x2016991bb9129e080c24c1409030330618650088810c4b6),
 (0x2050d018822218104c87dd2014267e9ac0081686575d208, 0x1ba50105498062afa348005ae04081212102a95888a2dd0),
 (0,0),  (0x81293511c76000856cfe61935c93600000a72085b102c5, 0x25446402e18986c5a11000428206c1e8a3f50cf5a4cad08),
 (0xa36890451a1c0e110230078a8498841740f81c0d1fb085, 0xc026d38a5e1218e0101c80119647aa8a70740b0000628),
 (0x61005d880430348301804793671c3449080038a00598a1, 0x28ce3a210e2cdc020c204000090a0c220a13fc700ca0256),
 (0x183e08c3002c42a22d52104c005988e29c0480602009310, 0x7c0d728db932d54c0252b83a68215140028119b4cf4c86),
 (0x271a1082742c0b5161e3e4281a8058297fb82484c295838, 0x10e0c4090900d08e06080992616087c00003d16b25684c7),
 (0x28a00660385249388af896b213a009134760480100516f1, 0x544210e01a084c560060149841a300c0095b7f03d8c004),
 (0x2150840f006823188a0ad9820645c4ab0d5ee8281921111, 0xeab78700a964cc505940465e1ba2b1022a10185c252060),
 (0,0),  (0x206a540c040080216656204651008ab689244421f45291a, 0x3108322c02d509a0900d50180743048601980040a084c5),
 (0x202688020a8b1686001e15144208280ae6012e46208859, 0x820873059014a068dba188e308f415b4110ec021071502),
 (0x11c3042811c2848128202241e2541c84dd0c40e05c321, 0x188e24eb942a39523217d9911819aa435122a2a20821042),
 (0x80b216b262440192018222d0864301c52b8103e2f040c, 0x37c0c010d009b9a24bc65900159306008c436ec1d0d0c3),
 (0x18b3d1040250a819192170dd00aa2998507480d00203520, 0x4402dbbd8c546622d60000615490272a0a412f75a028b),
 (0xeb17809c40ee0a604549d2948f80490af05c9017c7ad54, 0x204e83b013611719f021220004026a051062167c8284088),
 (0x6006020244419e80a320218099e479a34431447ac0098, 0x101990f180b2be411558d3c62b220b02548ace21812de06),
 (0x256a061db12531500201588642090d08b46008468b018a8, 0x1080706242c2c4a1c4608549a49652b5038fb6a9749c352),
 (0x10cc00c86e00d269e3a2056c46c14406750310518d5502c, 0xc235500117d218418480210990a0a6000bca202208ac51),
 (0x1804c81829dc4a0194c08e001b2ad2e44660ca0098b6469, 0x21cb10849423252c222c701f00400912389c30cd2340884),
 (0x4ece410180103510c2036908d2b021304a30840c2b171a, 0x321000aa8608d028e215496a3214684ceb44750608428a1),
 (0x78438654022c302a015bc8d6c1497e2424012e8260c595, 0x346009f0d1c1451e00200102340049c8dcd0410b0062)],
  #[
 (0,0),  (0x2180d906884e88d22190310052c0a980436004070e81f18, 0xc2e00a951106720106448270d1c003500996388a0220a5),
 (0x1f84b5ce22156558002e471311484218942848078a07e8b, 0x4b40104c6098a6d04018286630192121d7a6987438000),
 (0x20590900284845620c9899100473a9102636640d204605d, 0xb26d612c785001c01476447b20850cd19c01a525039c20),
 (0x24325690800c08a28c74467418040172c107486b15b4511, 0x10c9a94701719314328229092350da0c169826808203a60),
 (0x2009a48fd7c91f882b6806cb98101aa91ce066067022642, 0xfe04b00080040150003f12047214056620581c90b1c0b9),
 (0x27458c934530543263062480c6e0044105408322300600d, 0x205324b08321400429110f210b88286aac209504d90d0),
 (0,0),  (0xc480600585c3a14d0e5314bf37100aeb830b97040915b2, 0x3297880221a304282202c82004025d40048b0406844e249),
 (0x28d214a0124681882704af1651109804d94508bb819600a, 0x1304e34ee0802460d0b300e0842322bb268a35404608595),
 (0x202210144aa01800668909001581020b86aa0853413e0c0, 0xfc126a2a04c2669117634ddc0542494580183a0384062e),
 (0x56258e1880bab9414008578a214f85cb52342042a90811, 0x1a81a50a5720102163ca7806188a0022089c15910102226),
 (0x12614d96110f22441008c803a4486221390001003004490, 0x2010b2200c50c1822d77175813351c0244f4064448e1302),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x284200044108400, 0x2010840003294800),
 (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[13+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

private def rows : Array ℕ := #[
  9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 22, 23, 25, 26, 27, 29, 30, 31, 33, 34, 36, 37, 38, 39,
  41, 43, 44, 45, 46, 47, 48, 51, 52, 53, 54, 55, 63, 66, 67, 68, 69, 70, 72, 74, 75, 76, 77, 79,
  80, 82, 83, 84, 86, 87, 88, 90, 91, 93, 94, 95, 96, 97, 99, 101, 102, 103, 104, 105, 108, 109, 110, 111,
  119, 120, 123, 124, 125, 126, 127, 129, 131, 132, 133, 134, 136, 137, 139, 140, 141, 143, 144, 145, 146, 148, 149, 151,
  152, 153, 154, 156, 158, 159, 160, 161, 162, 165, 166, 167, 175, 176, 177, 180, 181, 182, 183, 184, 186, 188, 189, 190,
  191, 193, 194, 195, 197, 198, 199, 201, 202, 203, 205, 206, 208, 209, 210, 211, 213, 215, 216, 217, 218, 219, 222, 223,
  231, 232, 233, 234, 237, 238, 239, 240, 241, 243, 244, 246, 247, 248, 249, 251, 252, 254, 255, 256, 258, 259, 260, 262,
  263, 265, 266, 267, 268, 270, 272, 273, 274, 275, 276, 279, 287, 288, 289, 290, 291, 293]

private def reverseRows : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 5, 0, 6, 7, 8, 9, 0, 10, 11,
  0, 12, 13, 14, 0, 15, 16, 17, 0, 18, 19, 0, 20, 21, 22, 23, 0, 24, 0, 25, 26, 27, 28, 29,
  30, 0, 0, 31, 32, 33, 34, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 37, 38, 39, 40, 41, 0,
  42, 0, 43, 44, 45, 46, 0, 47, 48, 0, 49, 50, 51, 0, 52, 53, 54, 0, 55, 56, 0, 57, 58, 59,
  60, 61, 0, 62, 0, 63, 64, 65, 66, 67, 0, 0, 68, 69, 70, 71, 0, 0, 0, 0, 0, 0, 0, 72,
  73, 0, 0, 74, 75, 76, 77, 78, 0, 79, 0, 80, 81, 82, 83, 0, 84, 85, 0, 86, 87, 88, 0, 89,
  90, 91, 92, 0, 93, 94, 0, 95, 96, 97, 98, 0, 99, 0, 100, 101, 102, 103, 104, 0, 0, 105, 106, 107,
  0, 0, 0, 0, 0, 0, 0, 108, 109, 110, 0, 0, 111, 112, 113, 114, 115, 0, 116, 0, 117, 118, 119, 120,
  0, 121, 122, 123, 0, 124, 125, 126, 0, 127, 128, 129, 0, 130, 131, 0, 132, 133, 134, 135, 0, 136, 0, 137,
  138, 139, 140, 141, 0, 0, 142, 143, 0, 0, 0, 0, 0, 0, 0, 144, 145, 146, 147, 0, 0, 148, 149, 150,
  151, 152, 0, 153, 154, 0, 155, 156, 157, 158, 0, 159, 160, 0, 161, 162, 163, 0, 164, 165, 166, 0, 167, 168,
  0, 169, 170, 171, 172, 0, 173, 0, 174, 175, 176, 177, 178, 0, 0, 179, 0, 0, 0, 0, 0, 0, 0, 180,
  181, 182, 183, 184, 0, 185]

end BasisSeed7

namespace BasisSeed7

private def row (s : ℕ) : Fin 6 × Fin 7 × Fin 7 :=
  (squareCode 6 7).symm (Fin.ofNat _ (rows[s]?.getD 0))

private def index (i : Fin 6) (j k : Fin 7) : Fin 186 :=
  Fin.ofNat _ (reverseRows[(squareCode 6 7 (i,j,k)).val]?.getD 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
private theorem covered :
    ∀ (i : Fin 6) (j k : Fin 7),
      (∃ t : Fin 6, headHit t i j k) ∨ row (index i j k).val = (i,j,k) := by
  decide +kernel

private abbrev Check (s : ℕ) : Prop :=
  imageRow 6 7 7 11 x y z inverse (row s).1.val (row s).2.1.val (row s).2.2.val =
    (2 ^ s, 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid0 : ∀ s : Fin 31, Check (0*31+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid1 : ∀ s : Fin 31, Check (1*31+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid2 : ∀ s : Fin 31, Check (2*31+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid3 : ∀ s : Fin 31, Check (3*31+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid4 : ∀ s : Fin 31, Check (4*31+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid5 : ∀ s : Fin 31, Check (5*31+s.val) := by
  decide +kernel

private theorem valid (s : Fin 186) : Check s.val := by
  obtain ⟨⟨q,t⟩,rfl⟩ := (finProdFinEquiv : Fin 6 × Fin 31 ≃ Fin 186).surjective s
  change Check (t.val + 31*q.val)
  rw [Nat.add_comm, Nat.mul_comm]
  fin_cases q
  · exact valid0 t
  · exact valid1 t
  · exact valid2 t
  · exact valid3 t
  · exact valid4 t
  · exact valid5 t

private theorem spanWitness : Spans 6 7 7 17 := by
  apply fill_basis (by decide) (fun s : Fin 186 => row s.val) ?_ _ _ _
    (checked (fun s : Fin 186 => row s.val) Fin.val Fin.val_injective x y z inverse valid)
  intro i j k
  exact (covered i j k).imp_right (fun h => ⟨index i j k,h⟩)

end BasisSeed7

private lemma square7 : Spans 6 7 7 17 := BasisSeed7.spanWitness

namespace Format6Border

private def points : Array (Array ℕ) := #[
  #[1, 1, 2, 2, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 2, 2, 0, 2, 0, 2, 2, 0],
  #[1, 1, 0, 1, 0, 0, 2, 0, 0, 2, 2, 1, 2, 1, 0, 0, 0, 2, 2, 0, 0, 1],
  #[1, 0, 2, 1, 0, 2, 1, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 2, 1, 2, 2, 1],
  #[1, 2, 1, 2, 0, 2, 2, 0, 0, 2, 1, 1, 1, 2, 1, 2, 1, 0, 1, 0, 1, 1],
  #[1, 2, 2, 2, 0, 0, 1, 1, 0, 2, 0, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 0],
  #[0, 2, 1, 0, 1, 1, 1, 1, 2, 2, 2, 0, 2, 1, 1, 0, 1, 1, 1, 1, 2, 1],
  #[0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0],
  #[0, 2, 0, 1, 2, 2, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 2, 2, 1, 1],
  #[2, 1, 1, 2, 1, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 1, 2, 2, 2, 1, 2],
  #[0, 2, 1, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 1],
  #[1, 0, 2, 2, 2, 2, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 1, 0, 2, 2, 1, 1],
  #[2, 2, 1, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 2],
  #[1, 0, 1, 1, 2, 2, 0, 0, 2, 1, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 1, 2],
  #[0, 0, 1, 1, 1, 0, 0, 0, 2, 1, 0, 2, 0, 2, 0, 0, 1, 1, 2, 0, 2, 2],
  #[2, 1, 1, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 2, 2, 1, 1, 0, 1],
  #[0, 0, 0, 1, 1, 1, 0, 0, 0, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1, 0, 2],
  #[1, 1, 2, 2, 2, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 2, 1, 2, 2, 1, 2],
  #[0, 0, 2, 2, 2, 1, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 2, 1, 0, 0, 1, 0],
  #[2, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 2, 2, 1, 0, 0, 1, 2, 1, 0, 0, 1],
  #[2, 0, 2, 2, 1, 1, 0, 0, 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0]]

private def inverses : Array (Array Packed) := #[
  #[
 (0xa823c19e02218cc4254820520a6b400428802006f4, 0x16c80860115c603308258a80f510b2d3025cde9903),
 (0xc9cad1694c80d01856102403db1038a40b0200921, 0x306200200b15127c7216a40242029421150899d240),
 (0x6ae554b194b48009b03c901041ca254d581c059494, 0x9110a14440027de24f4226c48820c8b007e3f04021),
 (0x3a1230062415103022068b01410040f115133ed142, 0x8c8d3011c80e09457120623cb0b70a6080c10a20),
 (0x1d7200307814102ce206864340020b11351ec2d040, 0xc08cbd0985c90dd2055110903db1a0aa40a1010a23),
 (0x8a43f18682208c83e5780b800a6a3034289a2904f6, 0x24180858345f613808058405f51085431245569901),
 (0x6694898096a9124721b29043458ac463d1ea44d96, 0x1963443068162d30800022b8182013842610a0241),
 (0xa20948aa096a9218023b1814355880362d1d2f4d94, 0x4966244480806082580027c880831e885242c00041),
 (0x7062444f580613c180000118082ae4842520e0040, 0x68895893086990c2e20b3e42355850961d2dd04e95),
 (0x1802034ba0301008010130200000360300d020000, 0xc06000030000028660200cd4020064800010840300),
 (0x489488f11689000920b3028345880060d20884c96, 0xca163450ac8061fb0830055181804ad85246200041),
 (0x41f60478518062010800254081823398625b450040, 0x20096882a66a9082920b00393659c4060d24384e97),
 (0x1100000ca0301b3500001880003e2400014060001, 0x48c0003b3500000420101451010009b0002a310000),
 (0,0),  (0xf840814602007cc04f6204118820a45027cd194123, 0x1255498c8b5833d801c9b6042ca00ad5802a29694),
 (0x423c8d1083cb0c022541182b3eb2140a4092a00a21, 0x1802000f481410b5923686d441014b41350006d142),
 (0x2083692616880005132ccc00100492834f09ada2c0, 0x1d409448685627e0000203d5e688697c901402511e),
 (0x5108d01301a480ac325e0812440a3b100c942642, 0x2b8ed00e80625824420c8075c122850028f00a59a9),
 (0x27103419c240140a18584a00d484b603aa03740980, 0x86e406215b62a34800594ec083a48a8158c82247c),
 (0x482408642b196003e245a19470130285824d281202, 0x115b1180d4c48f9809181a2a0e684d4a28a2952cf5),
 (0,0),  (0x454702843c458a1e01cab328c235294a8c840c5ab, 0x6ba088d60c08a6100262400170448c0a5037ba3040),
 (0xc041a90a05128c1f304b517d839012a1d22a000021, 0x26244644502143a0053426803c45cc1a2d40cea1c2),
 (0x30c29594801246448508030250381a0259b4164004, 0x4e352a694189208b522398ed0983a08d2241a91722),
 (0x88282f18082118485ab7c1600cc011ea200305e681, 0x4581d006d494e182a4080687530824111048120078),
 (0xf210b18a8060c8e90ca08c02c04800b27a6c232c92, 0x1474c013a0c2206a10221d81f16f64501900cc305),
 (0x5c85500562f027f5c881378121240525826705400b, 0x21782ae28005c002344480700ed1aac27410401b74),
 (0x3179ba16565a2384a021d3e1211df42c3d36060832, 0x860040e120808861039c000a48e00b51420951470c),
 (0,0),  (0x506a2c0ccd9c5942b20051109bacf10c00c8954674, 0x8c0141812240820c0170066900410ee1b735680009),
 (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x3206044841826178a8000f6083810e184241640240, 0xc42958b094689086423b2002345811e63d16824c95),
 (0x40600011170202a6001034710100a1102000110000, 0x3100000e80101195020010200014040003ea60001),
 (0x6ba86189c9621400455a40a13b68e58458a06f0a94, 0x10458e4000140a450aa5aa020415087a041510f063),
 (0x2b241090c389005202e18607ed6988b042182226cb, 0xc01263261c168f2ced0c50d81216410a09458cc024),
 (0x16080612587a0c4095410678add261b2d480806023, 0x8993a0090204528e0226890350219a000102201b90),
 (0x1232b22054810080005182ce732603209854643221, 0x488500450230ac0882ae1d010441b44807a802c146),
 (0x2458c923304ca28093e10e35a70c8800092043401a, 0x48822040c8225d2f4010e14a10512770a453302c84),
 (0,0),  (0x8e450c0029e55a6add2042a6a0af5052e0ee043174, 0x71a031860418801020c009485b40a1000700b10c09),
 (0x120461c4122b280c992405960222801a0194f945a4, 0x28b888000dd457b0408032605d057f246e4004121b),
 (0x8123c00910804e41314001343328040054d45f41a3, 0x26542892a259100aceaf4e4848105210810aa02618),
 (0xc448700580040846470b56d80734ace49aa6c871a0, 0x193096a7a723228a0d029026809031a200003001c),
 (0x5442e4a8003c062230902270c984008221231054cc, 0xa18101119682c881832f140e227a2d6042c8eb0820),
 (0x90ca00970218f12e9400941056044c6388a5d0a25, 0x441144528c10206c149464aef88b3b0886252060c8),
 (0xa22624660580612a28300134818008185244b00142, 0x55895890aa699291420b3688345b66660d2a4c4c94),
 (0x12d14f108259005084020408d4c6510344a8ab122, 0xf8820302a18800c0e7945c8722110ace8234214200),
 (0x849020001f030248800032b5010006400030470001, 0x5040002d200001214030050a000181201009b00302),
 (0x10200021150d634e125026112a9425d6400240f362, 0x21145f4c60420030cdaf40e0910312009961210c94),
 (0xc0396885406892b1120b000c3458a5960d2a264e94, 0x384614481e80614a68002a9281814a485245080142),
 (0x44903024320002ac5010188901009c501023270100, 0x932000028d010143a0002116000043800014580001),
 (0,0),  (0x50623318988801500784583e211060ceb200604200, 0xc9d04e3462690a1486001408c4f9130047d19b020),
 (0x80064580d1008880889b2121a360001a0cf60a8081, 0x2b182a1502dd237a00041842440662200001f0303e),
 (0x2819788815689065220b0b19365910063d29c04c94, 0x6660446208360084810000280824f884246210043),
 (0x1a34121440442701818214a1000428b04c81882800, 0x8049c8c9a9b9c87a107ceb4abc8b5048b05e540725),
 (0xaa3a6102481400a8115898604a8508698a39208395, 0xc196a025c1ec5568a244138178e5104180c33400),
 (0x6291049352658084200cad8090ca60080821611096, 0x800ee14c01127e690f6202740a20126647da046520),
 (0x303010a7123485074dcc001298d0ca6a0874c31080, 0x82cc070089413af03231924540273511b18120a75e)],
  #[
 (0x348e482174a4008a61068969be69c1106922261005, 0x4840a7d000508c641611740041102a8c80150182e8),
 (0,0),  (0x224600115831ca2a4032ab232400d90a9110981a40, 0x9499690e06482445890504c040b004a0608a608021),
 (0xb1296906c548262ed905067440b205204086208322, 0xe9610081831c9812032b183250062da8118421840),
 (0x61010aa501038fa1a08ab8811cb7224cc38805496, 0x49c02550a5a28705c1360406e6208c0223c0648b21),
 (0x13061191a4005594932c0b025268204c0c81b7c6f5, 0x60296c6812d90a4a4001b0a981114090a24a481002),
 (0x2400200000030010000031840103d9101010440302, 0xcbb01008b40000e510300c4b02000200002eab0000),
 (0x424601b25a0055c1132c005c51689f0c2c8002c5f4, 0x3d295c45a0d9083a60118000801100e0826a111202),
 (0x2036044084826044180022cc81806c284244a80140, 0x920948bc1068920a621b0c01365b13462d3b054c94),
 (0xfd801008800000460000062c020360103006100202, 0x21020360d00012170300152000080a00018640100),
 (0x110002a420101b150200b20020140602034240001, 0xe2602011bd0200040010345301020990000a990002),
 (0x800002b11010104a0301451020208c00000080201, 0x42203010e60000b1500001ae01000110302a310000),
 (0xe140000c010302895010097a0003ca702006da0101, 0x16a020008200016420202480030021000000210200),
 (0x80000153e00038000201009000282800000c00102, 0xf4d020024102007a201002f00200201020183e0200),
 (0x4c60464888362004810000880804f884246090041, 0x2219788237689067820b21b33659b0063d29624c96),
 (0,0),  (0x162025726aa08606511621f2e42158d213c2588820, 0x89d00085001038712a088c0513c82004ec08a05794),
 (0x70008e42103800ba28a0b112c80214ec00815494, 0x5500357181a286140106010ce52180a213cd288a22),
 (0x20a008962d165530c4134929539a4898cab8cb827, 0x30f58166140a02003332c0240a86021030102004d0),
 (0x1c0813d01050e16d0d8d6425a042080a4603042441, 0x3f7ec0d2c811c824070005a06000140b028ca83b6),
 (0x6d0520b17029043002a028580808100972e82842d1, 0xd2910c8402f0014c5c8626f53662168113470926),
 (0xe2190789e0748028bb2401263380198ade598c405a, 0x11a248061f0a19d3000262c94c5ba2140186639380),
 (0,0),  (0,0),  (0x44668049011828b60825bca9143a4100258127a37c, 0xa081742436a31709a58843520a85229cca36485880),
 (0xe50e08c10b43a4510f82641d2b4751e2a01cb81443, 0xaa1d00ef0305b04f01c9aa280200a1408e347e8a8),
 (0x10010009008473085816a149e1d4610a569821215, 0x68e8ac8e61d388c7321681eb20e2980a429220a528),
 (0xa21740414a1152b85a849f80a87883cea1c485882, 0xe4c68069031a28142805b40314386180058127a17c),
 (0xc4a624631880600a082007c6808088287251050341, 0x2b595890a76893c1c20b1021345b76460d006a4c94),
 (0xa1d94881726892d2b22b2440355bdd960d00524c97, 0x606345a8c83600d4810023080800208425b2c0340),
 (0x82460440828260024810006d828118684265650240, 0x1c3958b2356891cc122b0902355a83962d08004d97),
 (0x9076344ab581631e08000960828088285249a00041, 0x660948904a689041d20b1092345b56562d004d4c94)],
  #[
 (0x6a2958b3026990cae22b1e62355a58163d0d504c95, 0x586244455826134180000198080a4684272a60042),
 (0x8026144b428060204810041e8282b4086262520041, 0x2bc94894b56993c5822b0a20345809d61d14a44d94),
 (0x2c263455e083632068102ce880802218426a920140, 0x1349488017689044920b0215355940060d15004e95),
 (0x8c861455c0816380c8100642808088384260120140, 0x314968801d68906e320b00b5375962862d1f004c97),
 (0x600958938069924a420b144a355858161d05d04e95, 0xf0624647f80619498002a91808006e842780c0040),
 (0,0),  (0x2a696881e1689261922b2903345802061d24824c96, 0x8486144a1c83619a481004888181719842415c0240),
 (0x2de08c08040a6406f8248202944ac429004001641, 0x4421f0006a315937002ca3998223512428fa08e9a8),
 (0x9a050a5003910584887134b8c039e6e2462874b286, 0x21c2b1a0c060d26b058689473f84080c88d4814518),
 (0x238005dc01c7b0209985e03402d40d09102c018000, 0xdc7bf801bc30449626480fc898006042ed43521e89),
 (0xa74034423060620c347006c42e8125428252618242, 0x403bc8b4c41790b0c88b2932505ad21d5d20886195),
 (0,0),  (0x3006b15b33610068142cb15a2246612d539c4a2208, 0xd314684c884b60422c20ca5c5208452a803244953),
 (0x4872b00105450828732b581646354e376a9edccca0, 0x36044940b0b231108cd001e1290a1080800101101f),
 (0x26420300d888006957b4600721139a0e8230144300, 0xad24e103279316a84009108e4c24601444cab023),
 (0x15202411024980202091c0860dd1120183104c4091, 0xac18000d5241a4948480528a226a0da50a812a124),
 (0x4c90c3700808a080a85402033ab800c6cf4c5005, 0xce03233006e710522f45aad180844415111031a1b2),
 (0x600903808b20f2809584729204c94410c4041c0042, 0x97e2482a64c7010b006b08041a0438282b11e1bcb4),
 (0x1066807886ccea5200611c400774549011ead7e0f0, 0x41185886380301280a82c0bb980a206dec14000e02),
 (0x3c51942288607860429179880322586c91a04010d0, 0x80a44b454107801415468242344584836a4481ac20),
 (0x99580617d14a5512a8b3402685cbb580012031b0a, 0x460a1d1c024218821114009197a000243c85500070),
 (0x250a0d054a401a406104068796a232040c91100172, 0xc8d5a07a9414a59f8a9b1030695d4d48200eee1808),
 (0x162a0d10aa401926a1042c3097a1c0140cbd900073, 0xc98590464114a4d94abb1104685e28e81000201908),
 (0x28600014d002000a200010d000009ee030221a0000, 0x841030090601013010200d06020261100004200300),
 (0x200a1d3a404019700104080d94a3a0042c95a30271, 0x1c758044a916a4069a8b14a2685c19b8002a081908),
 (0x380948a10c689101220b1e08365803161d15004c95, 0x45b63456638362e648200036818378886262a10140),
 (0xec1461e140282881091429330320b61a0194a047a4, 0x2e8980211d5557a30a016c05c0540e45e430e1019),
 (0,0),  (0x888848901102024d0a82d0009a092a4dcc00100c01, 0x4746906f68cce802e04106470476902021c88de3f0),
 (0x28000000802000080002082020200002000200002, 0x8202020a200000820000028000002000020000200),
 (0xe408828b88c5101141100384360008a9640c165a, 0xa403c678545018c4ae96a8683808a13342036208a4),
 (0x228e102711248d41c02016b5816046b438b8680025, 0xcc104458ac0a222a0c04694a6c8aa90ac607804fca)],
  #[
 (0x8c86812022c042202016d310a00e8a4cf04450c814, 0x33286099542295c9482120a753501192023289124a),
 (0x2087052028d051001e66270bc08aac280146002180, 0x8c70609d80020ebc8188c8c01621024760b9e79c79),
 (0xca6aa33490961edce0e877c90a03a0cd041e90a138, 0x259100894b60e12205058812e4b00d12e260604e81),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb5ed1474451e184042a071b401890e241044cec666, 0x2120a8a2281a01c910e84488c46b108e8ba303889),
 (0x690082180418491d1e2c95e401410179e440082860, 0x165770004a6736020112020b9aae44840037c0d68c),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xf094890b4689076420b12c3345841a60d3b464c94, 0x6076244003826388a8000d3881813e186240a80040),
 (0x4060001b1502000c201014710100013020201b0002, 0x310000040010311d020010200014ac00014040001),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0x1c1008d289b51ee420306e000c5d61310080b30cd3, 0x1603029420ae01a9e4e90dbc0a006cc9369444120),
 (0x2080101c88110821244b40180a35d41f7a8022cca1, 0x890b096177cc339e810029e1d40a2940803811121c),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x870010328e0300c4902021b1020005100018020001, 0x38e0200c300002226010020a000068001024100300),
 (0x846604468281608048100a028280ef086264090243, 0x21958a83d68904f220b01b9345b10a61d03e24c94),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x647a9a37b44844ab8057c818b88960c7690a212313, 0x8a8065c84323b21429a81786064481280450401028),
 (0xc000a03518e000801060087ce300a8c09014620a03, 0x14b14002810602254e1020830400412f20211cf100),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xf995889806b9201920b0125355950b61d22854c94, 0x90660466558061ca48203e428280ae484250280242),
 (0xc00958b9806b9260420b14ca355a50b61d257a4c97, 0x2506044655806114b82000318280ae484258040240)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x89989d1112c348971548c58829ec218a7580000409, 0x602002608534122808262030940390600a105a7236),
 (0xa2402978982832c6b5002781320812c1000128291e, 0x11cc00643d108284a2b582ac83584184a985584a1),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2439488ea0689290721b0695345895f60d0b514c96, 0x82862471038161480820290880814a084254a20041),
 (0x9c9588842689178923b00023458b1463d33c74c94, 0xc41604772882620108001f60838104984240300240),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0xc0c004277c2e8087400056c493d5242404021e6138, 0x35202ac002111e281ccf2029040288905895c00086),
 (0x46ca04490032243852520b2f06891608403674181f, 0x9925b900334d02c2ad0ce490f104a8658f0982c0c0),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x81802032250100738010000b020020100002010103, 0x7430100d1000020010003794000387202008dc0000),
 (0xaa002000220000a0802000000002a000200a280200, 0x208000000a00000aa0020008200020020000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2121cc916c0500c220d0281402c0b6685d52691008, 0x2c8222482d8f605922c90a02c3c4186800482ae16),
 (0x70358c160258581acc4047221dae828130d1880c74, 0x878a11888c2483052310180962413562070406b30b),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0x64400032800200c6a0100970000084100001f00203, 0x18b020097b00003810201484000312a02026000100),
 (0x2f06246c5d82633e38000091808004c84258840240, 0xc0095891826990c0420b144a3558fa163d25504c95),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xe83d094000c755c61ee15d426f61850250143c91e0, 0x1102301a27082a28e1048010008840c48aa2802e1e),
 (0x2ae953c815842420e0b086d00938368a84b8c28c8, 0xd10020c17883a88531807780d564681255b0411020),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4010001aa10102a0c01010e00002e1c0000b070100, 0x1d6010015402004820202b0002010e302024980003),
 (0x24c6244420816088481000288080e5084246030241, 0x801958a2976a9247a22b0193345b10861d29484c96),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x6475a8aa0c0e4f06059622b001c8010caed604c263, 0x208524521f11049a068dc49a60650d31008722100),
 (0x6920240506281478b3284730018422c80a34250183, 0x48e905260512a07448590c3f63a99178588c8ce7c),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x9497882026b90ba322b381b345a8a060d21404e94, 0xf026047c8580634408100604808031c86246b20043),
 (0x6a895893206990c0420b1e60355858361d2d504c95, 0x52604645f82633e380000138280a6486252260240),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4f424114110c038524145c5135e0069135c852c14, 0xc00ada8696663d402d92ba2224a1d902c0a0628109),
 (0x25304014921259b1503ca443a320c6c898d10d11aa, 0xd24208c86461a6040d82402008443937000880e641),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0x8a36047ee18060c258002016838020f86260b20240, 0x65897881106a902da20b0c09345859061d10094d94),
 (0x281958a8976a9065222b0b19345b18063d09484c96, 0x46604460881600a48102022828047284266030241),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x92e4c8513188157a20759866a6444c0027202000d0, 0x600321a888226a044b0a2611198b92c8c080dbd700),
 (0x67128456616662415420010b2280d704f242c16040, 0x82508a80e09913c885b3ee0505900e00d250c8696),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x3000200c01002640202dc803020a702005a30002, 0x2d80000d2002008800101220000181801038540100),
 (0x24c6046620836022e810200880804508424c090041, 0x82197888156890cd020b01b33659baa63d01624c96),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x342011b501028c7023c6626b16061710518e249080, 0x82188e425a5c010ec4201d104061a002ae3192281c),
 (0x4cb6289b40699000c22b208a34580ac16d02519894, 0xb24904600182623338101625828004301260a22342),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x6170003c620102606020132b02006ab01009a00000, 0x100000001900011700000c440003800000141d0203),
 (0xe66244620836000c8300082808247086246290243, 0x209958881568906d220b0b11345910061d29404c94),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4820588a3c00b0811016180e60adb0f64ab08e2121, 0x1daa07580430160e8c8e19195000b00044520d404),
 (0x6e85252a41420a273b101d0191a8e00862d230ca, 0xfa9020c21510a9d4400069a24c641213d589288820),
 (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0xaa5968b297689040722b340c365885b62d22044e96, 0xa6144c608160a8080009c180813a0852596b0040),
 (0xe8c0003b150200a6001034510100a110200ab10000, 0x11000004001031950200b880003404000340c0003),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x41949084a545530008e21452004800d015494300, 0x918c016e4348228cf72414002197369e24681210c9),
 (0x222b08304e1044213a480ad1590221480d5c449289, 0x89035c9002eb1484185d00280d414279020034102),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xf3b95882c5689242020b1025355a13860d09084d96, 0x806247c2283610168102c408280c0485264570041),
 (0xcc624460a83620048100088808045a86246890041, 0x221958a815689065a22b0b33345b10061d09624e94),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xe21930422440581d1565ad20bf2845124cb0ee006a, 0x19c24404ca8287a02a0a425c0010a0e9a04d00df14),
 (0x8007e14c01127e69066202740a20126647da046520, 0x6298049352658084210cad8090ca60010821611096),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x110002ac001031350000b82020142c0201e0c0001, 0xe86020113702000420101451010209100000310202),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[14+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

end Format6Border
namespace Format6Border

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check0 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 0
        (borderCoords (0,jk)).2.1.val (borderCoords (0,jk)).2.2.val =
        (2 ^ (borderCode 6 (0,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check1 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 1
        (borderCoords (1,jk)).2.1.val (borderCoords (1,jk)).2.2.val =
        (2 ^ (borderCode 6 (1,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check2 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 2
        (borderCoords (2,jk)).2.1.val (borderCoords (2,jk)).2.2.val =
        (2 ^ (borderCode 6 (2,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check3 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 3
        (borderCoords (3,jk)).2.1.val (borderCoords (3,jk)).2.2.val =
        (2 ^ (borderCode 6 (3,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check4 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 4
        (borderCoords (4,jk)).2.1.val (borderCoords (4,jk)).2.2.val =
        (2 ^ (borderCode 6 (4,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check5 :
    ∀ jk : (Fin 2 × BorderAxis 6) ⊕ (Fin 6 × Fin 2),
      imageRow 6 (2+6) (2+6) (6+14) x y z inverse 5
        (borderCoords (5,jk)).2.1.val (borderCoords (5,jk)).2.2.val =
        (2 ^ (borderCode 6 (5,jk)).val, 0) := by
  decide +kernel

private theorem spans : Border 6 6 2 14 6 := by
  apply border x y z inverse
  · decide +kernel
  · decide +kernel
  rintro ⟨i,jk⟩
  fin_cases i
  · exact check0 jk
  · exact check1 jk
  · exact check2 jk
  · exact check3 jk
  · exact check4 jk
  · exact check5 jk

end Format6Border

namespace Format7Border

private def points : Array (Array ℕ) := #[
  #[1, 2, 1, 1, 0, 0, 2, 0, 1, 2, 1, 2, 0, 1, 2, 2, 2, 0, 2, 1, 0, 2, 1, 2],
  #[1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1],
  #[1, 1, 0, 0, 2, 0, 1, 0, 1, 1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 0, 0, 1, 0],
  #[0, 0, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0],
  #[1, 2, 2, 2, 0, 2, 1, 2, 2, 0, 0, 2, 1, 0, 0, 2, 2, 0, 2, 1, 2, 2, 2, 2],
  #[2, 0, 1, 0, 2, 1, 1, 0, 1, 0, 2, 2, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 1, 1],
  #[0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 1, 2, 1, 1, 1, 0, 0, 2, 0, 2, 2, 0, 1, 2],
  #[0, 0, 1, 2, 1, 2, 0, 0, 1, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2],
  #[0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 2, 0, 1, 1, 0, 0, 0, 1, 2, 1, 0, 0, 2, 2],
  #[1, 2, 0, 0, 1, 1, 0, 0, 0, 2, 2, 1, 2, 0, 2, 0, 0, 2, 1, 2, 2, 1, 1, 0],
  #[0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 2, 2, 1, 0, 0],
  #[2, 1, 2, 1, 2, 0, 0, 0, 2, 0, 2, 2, 1, 2, 1, 0, 0, 2, 2, 2, 2, 0, 2, 2],
  #[2, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 1, 2, 2, 0, 2, 2, 0],
  #[1, 0, 1, 0, 1, 2, 0, 0, 2, 2, 1, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 1, 1, 2],
  #[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 2, 1, 0, 2, 0, 1, 0],
  #[1, 0, 1, 1, 2, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 2],
  #[0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 2, 0, 2, 1, 0],
  #[1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 1, 2, 1, 1, 1],
  #[0, 0, 1, 1, 1, 1, 0, 0, 2, 2, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 2],
  #[0, 0, 0, 2, 1, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2, 0, 0, 2, 2, 1, 0, 2, 2, 1],
  #[0, 0, 2, 2, 1, 1, 0, 0, 0, 2, 1, 2, 2, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0],
  #[0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 1, 2, 1, 0, 0, 1, 2, 2, 0, 2, 2, 1]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x968d08002d07c20a0fa43402d23822102c00398241000208, 0x6940f388d23838750040c2882c031867936a006504500190),
 (0x2400a2509102a0c87e274152727df361c003560a441400e3, 0x8342598b26281e0780c022888500081c377c002500000200),
 (0x8a2020a4a304a000c480c080090750e1e202260000400e2, 0x140459850482907953b530860e27009001c00c9a54000200),
 (0x5390050001f82bc622a0b535ae29e01000d410604440089, 0x50c0080c0ae04c408084a40c010d41941ba0323000000172),
 (0x558951d94b295884640315d94540c9050f2d6dad5104006a, 0x8020202004686388b3480020a2a220a5010104204400111),
 (0xde0d000c36a108035445000c844c108662a0157845400089, 0x2132a802801ea00c02a8fa0323a04d79900a0a8700000172),
 (0x876918003442283800492a008cda400b2015024205500110, 0x309287d888991485091291da70040504c8caf9ad4004026b),
 (0x92000003c0000002d80000003c000000000000000000, 0x80000003c00000122000003c00000018c0000000000),
 (0x54092000103c0001402da0050403c014054020000000000, 0x1010080044403c01011520010107c00010018c0145140001),
 (0x618215d8998e008409400bdb6045810498ce77ad0450006a, 0x922902002410d4384008400099883a0b6110884241000311),
 (0x608615d8c9da0084480009da6101810498ce77ac4410026a, 0x932900003404d638100c420088983a0a6000884301440110),
 (0x100090000013c0004102da0010003c001044000000400001, 0x4414080114403e00040520000013c20145118e0040040200),
 (0x10080000043e00100520014107c00041458e0041100000, 0x44492000013c0014152da0010103c011010000014440200),
 (0x145000004100000040440001001400014400000000040001, 0x410402010044020104000200550000000100020000500000),
 (0,0),  (0x4502b1845004a40854118c84000511e251409b531400006b, 0x40465b004342c20104435a1152ee05041040a000500110),
 (0x8122ab8662a7b0089b0ab284904c45e162a38d500040006b, 0x7209145984080cc140244d5867a1a004810860a300000310),
 (0x43b50400008ac02662c88440ab24743500e000004040202, 0x5180021f5fa6415c90926619544890140af1ec4950500114),
 (0x600100d2810202543a2382d0273985178012694d44100190, 0x9616d921663d592081d43c29c0462008226c90a010440208),
 (0x80c87692284f944359a0818082a79452390c246855000120, 0x36140100c3a042b0a00060013c08010886b313130014028b),
 (0x64681d41966001a08d8905407c8001278237323804100190, 0x9383c00669901e11726012278362eec869800c0011400208),
 (0x10010a8501135bac501389c5044156aa0450486604500182, 0xb45a100024130440341a401201004103a01851000249),
 (0x141f875f11010a4e0e802edc008aa599001451c40514008a, 0x32058a0048874b1204dd02214414222058b841010400120),
 (0,0),  (0x818ba5c230f09472928815c1025e4109a1f4d1205000001b, 0x26640a3546086a0505534a3631a1a0e01609084c80420740),
 (0xc68215db2880148622342ddb8662050669c085ac5040006a, 0x2029c80096250238dcc80200299568099235424001100310),
 (0x206ec888c670f242988806882cd208138620c04240400009, 0x928103413880059523345940d325f14468c7160d11000390),
 (0xc68105db2880ec86223761db86627d0669c259ac5040006a, 0x202a320096250238dcc88600299580099235a04001100310),
 (0x82c46d4168d450ec66769d408223b11c7cd20a0e10100001, 0x742b8012862283019988001378900841832041e1000000e2),
 (0xc6833fdb28811086223641db8660010669c255ac5040006a, 0x2028400096262e38dcc91c00299640099234284001100310),
 (0x82c0030138c44c4c77209500962606003c83904c40000101, 0x212bb05ec62300b288cf685f28c128ec822441b205400200),
 (0x70605c081e1250c130704408a0cbf4074a0640c005100120, 0x808083e7e189ac0a4b06b3e41e1009e030989920d040040b)],
  #[
 (0xa3020a626c44064e1ad4586201395c02b8110b3c40500030, 0x5c5da10d013818b10422850c2c0420ed412070c290080143),
 (0x4cf885e593e1a80a4a5ab1e72c080de1c2c09b201110020a, 0xb1005a0a680a54c105a4460882a3f0062d2e44c044200120),
 (0xcd1142102124064e42f4081042c15c02a020000e04040040, 0x12e8b02e128018b03908362d313422ec4211da81d1800230),
 (0x8646842200088034499d64298106201a342293095500040, 0x66820731c94462001a200931244088025c11124302040133),
 (0x27f24129484684da11412103621b0014c940a0c01100040, 0x6c809a2c632090b01289ec2dc0c40eeea262e481cc040230),
 (0x1088cc2e112822b0c0098c2e28469cec012c548100540230, 0x4a2302106813d84e0a000010042802024c51880e25000040),
 (0,0),  (0x14002010140020104000200015000000010020001500000, 0x100400001004000010140001040000011544000004000001),
 (0xd680006339910a4c26678063823040012c80a73d05000230, 0x202ac10c862404b28898590c6dc428ec926650c000420543),
 (0xc7c32e6228d4004d22730c628623400038d50d3d00100031, 0x202c910d872222b29c88030c689404ec8320b2c001000b42),
 (0x100700001006800010140001040050011544680004000001, 0x1405c01014052010401f400015280000012860001521200),
 (0x142a2010143c20104006c0001503c000012040001520200, 0x1005080010043c00101400010403c0011545380004002001),
 (0xc68724622890604c32603862836128002980113d00400030, 0x3168d90c966008b3888e450d688404ed8631c0c004104142),
 (0xc7c12a6228d4c84d227060628623100038d6573d00120031, 0x202cc50d872212b29c8b990c6894acec832028c001008342),
 (0x14024010140160104024200015180000010060001500200, 0x100752001005800010141401040014011545a00004010001),
 (0,0),  (0x21186034c1848e5411ccaab43264a340018244541000000a, 0x18871c0936611122c033540a8590408ab635008b414401a1),
 (0x2852bbd8826a2e1e280903586c501220062b05b410440121, 0x56204025281591a053023ca79328094db8500a080100008a),
 (0x2205220188c8848002194000644511428c8a441805000390, 0xcc004cec25123834cc029eed889a420131442b2500040008),
 (0x1070fda0482a085482203d91e7123045080e1ac1140026b, 0x469820014a241838965128004080d40a0f651e4244040110),
 (0x104c12c9308825143c81424a8902100db08d552645500012, 0x22b3c510cc03d888832e9d11309c05600c120088100000a1),
 (0xc63458032848540387e63c00c7b70801290b040200000001, 0x3809000087a708006819020228085602d6b4300151500200),
 (0x1bc85d820011086880627da899c0107a01113ac0000026a, 0x2a024202c98a2c397239c8017002420848cc244210140111),
 (0x2400000031000000014000000c4000000f60000000000, 0x1b0000000c40000008200000310000001000000000000),
 (0xe247340182002200f0963a03509b5c021708840010500000, 0x1528480250cb5c03070980008244220040852a0205000201),
 (0x574ba802501498029801240011d806004005a80210000200, 0x8014500005c8040063b0da000004980391fa440104100001),
 (0x4a8b08018c6400005b56280117809800c8b2c00011000000, 0xa020e4004290980100819200883002000240020040440201),
 (0x410a88024308480208cf100030a3840000082c0200100000, 0x30b1440020a38401a030aa004758480334e1d00045400000),
 (0x852004004b000403c0d00803a188980116476c0345440000, 0x7a58b002b48c9800342f40001e400602e098020010100200),
 (0x202a80001eb0100034044a005018e8004ba0280044040200, 0x94c16202004cea01cabbb4000ba01201a409d00111000000),
 (0,0),  (0x10000000040000050400001050000010150000000440200, 0x1402010510000004000000505402005400000154100000)],
  #[
 (0x45014600414018200007100304100c281002341200000040, 0x104289fc001405045110657c4146c241005003e5551002b1),
 (0x450066004041a880000456044001cbb8140104c251400206, 0x4099091106563605408108050630404100e80500000071),
 (0x1000400700401e1100026206500419514505892345440163, 0x520f180510812a405595110000e0060012705010000210),
 (0x202c8c24c3641809ccca00a4788410cdc6601162115400e2, 0x829342592881647623208848837349202982a00c00000309),
 (0x838645042982036037200904d624f4096c926c4010100001, 0x2029a0e0c634d09a888890c029830976932193b345000308),
 (0x430001011018640115d000001459161112236401440158, 0x5414bb684445e382544003280141a2a944404c9910100202),
 (0,0),  (0xc78112232cc0184726368022823410023881221c0014006a, 0x203e25d49334808888891ad57c818e04876611a105400110),
 (0xc6c0450050520490829445008918e00100012c00000020, 0x2d1832b2148e007225054ab254106509509b205245040108),
 (0x8f27dd8937a9084090c45d838050105c22ad1ae4404026a, 0xe20800002c00483b06711801c238a4082844084101100111),
 (0x14e0c9260a16552118a4692634a50a065a52612040400001, 0x631a1040b4a1a856c2110041ca10b011a1a41a5701000200),
 (0x8f115d89379b084090e89d838042105c22847ae4404026a, 0xe2082a002c02443b06704401c23a88082847004101100111),
 (0x94119c669025330c14c032660c8b380b9031840600500310, 0x902009809cac4e1c12a88980020811009ca3a980404006b),
 (0x8f223d8937a4884090d61d838054905c22961ae4404026a, 0xe20818002c00303b06720001c238140828460e4101100111),
 (0xa8794cbe420a05914845aabf200257000608b2c84410006b, 0x780b10131154048b20a4500d65d881c7003413300000110),
 (0x287093461061800a35e8735820940063054268051400373, 0xf97844c80219c40d580138c830420a48470b117700000088),
 (0x8825cfaf44483858c0a423ad3981305d0508000011440088, 0x301a00503897c72712439c5280540a0028d3d2d444100372),
 (0x7844071072504032b8c0a51018a82a4563403090141400e3, 0x49b5826088f928806315a242704910a1c8fc44901000000),
 (0x417a24ec26698c36c97048ec9951c403723c252654400009, 0xb0045a03199622813405320326ac21400c80501800040190),
 (0xc4058f42004a20ec0a649141b204c71c1009800e10500000, 0x21da1011a5058f01801b4c10401b1041a14629e0040000e3),
 (0xcd190224ee8468884520642401676d08ba86484a10400001, 0x32402913016016308a810313769082450171b291440002e2),
 (0x9175040021542080930c0c02890135422100401855000190, 0x220222eccc02d234686340ec004688018c13112400440009),
 (0,0),  (0x100002011104000050400001044002001010020000000000, 0x5000000410020104000000401000004544000045140001),
 (0x7428001286208f019988c8137892044183229fe1000000e2, 0x82c51f4168d730ec667733408220511c7cd1200e10100001),
 (0x92968b4068c000ec323511418223cb1c2884080e55040000, 0x64692012933221008d88e8123cc03041c66137e1001000e3),
 (0x828503407dc136ed22368b40c672011c2982a00e10000000, 0x643aec1382264100c9c8741238804e41923505e1450400e2),
 (0x643856138227b100c9c80012388102419236d7e1450400e2, 0x828629407dc00aed2237d740c672c91c2980200e10000000),
 (0x82c44d4168d4d4ec66762d408223311c7cd24c0e10100001, 0x742a9212862203019989c01378904c41832013e1000000e2),
 (0,0),  (0x1000a801110408005042a4010440900010102a0000000000, 0x504400041192010400580040100a004546400045140001),
 (0x646a821293301d008d895c123cc08041c66205e1001000e3, 0x9294014068c1e0ec323421418222071c2885620e55040000)],
  #[
 (0x242a8400c2306a38d8ceee006dc40409c624924001440111, 0x82d511da2cc41086222111da82330306399265ad0000026a),
 (0x839009db2d801087362781da862303072c8645ad0010006b, 0x3469d600d2706838c8d80c0168940408c271184004040310),
 (0x83c18bda289444862226cbdac270c50778c36bad0404006a, 0x242a0401c3639238989904002c8738088320144041000310),
 (0x839093db2d804487362429da8620c7072c86c1ad0010006b, 0x34694c00d2739038c8d9560168973808c270164004040310),
 (0x100318011104000050406001044002001010800000000000, 0x5042000410000104029000401000004545280045140001),
 (0x839101db2d83a887362421da86203b072c86e1ad0010006b, 0x346a1c00d2700438c8d816016894c008c271184004040310),
 (0x92d4a4022dc5fa0c22711002c223177978c0b08605100173, 0x242b100cd22000028c8c4e0c298408868236077950040088),
 (0x504000004450000014000000404000010104000054540000, 0x51000000104020100100001010002005440020101000001),
 (0x14161e0414400436051434050041218100049094001400e3, 0x4000e1d141072a81504381d015068e724411404014000000),
 (0x7039aa0992252c31cc896808289624748226052844000008, 0x828251d66c92d08a233685d7d32092883c81601311000390),
 (0x353b100cd7200002cc984c0c6c800886c222057804000088, 0x8284a6022895fa0c236510039223177939c0b28610100373),
 (0x5000e1d044132a80440781d001068c735041424005000200, 0x5561e0401400437100036051051238005149095004000e3),
 (0,0),  (0x44021e0440100637544034051041218140009295115002e2, 0x154e1d104472880001781d001028e720005404004000001),
 (0x454e1d114132880400381d055568e724001404104100000, 0x21e0441000636110034050001218105109294414402e2),
 (0x2029440096240638dccaa6002994c0099234904001100310, 0xc68001db2883a886223451db8660390669c34bac5040006a),
 (0x2c5b440305db583825420a021453900a018c2c4215540110, 0x8019d80004a685d08515d8418825045011c1ad4000006b),
 (0x8f007d8937a9084090c45d838050105c229a1ae4404026a, 0xe20918002c00483b06711801c238a40828464a4101100111),
 (0xc683e3db28811086223451db8660010669c211ac5040006a, 0x2028040096262e38dcc8a800299640099235444001100310),
 (0x2029500096254238dcc800002995a8099234224001100310, 0xc6820fdb2882848622352fdb8660150669c1ddac5040006a),
 (0xca501000295c7202d3b1220193a000003858920204040000, 0x420400392a00001280a90026c4c700383a1000110400201),
 (0x8f0bfd893780884090f01d838079905c22945ae4404026a, 0xe20800002c00e03b0670c001c23804082846324101100111),
 (0x2028100096259238dcc83000299550099237c44001100310, 0xc68041db28822c86223747db8660ad0669c019ac5040006a),
 (0,0),  (0x74408460c3a6203670444761690a265587a002d500440200, 0x8ab0320a28189c088229b80896a581a2680e102a000000e2),
 (0x60000fda901200842a6429d8222d830495125dac4050026a, 0x97525000662cd63895829000d440380b2229004305040111),
 (0x28492643d0824805c221b14022201aac8580888510040190, 0xd32281b02224b48a2d0c06b280c204537224651241000008),
 (0x503b180240080200272c60010ee002000118800011540000, 0x1c442010ee0000080829002410c00001aa12a0144000201),
 (0x971099b06188b48bc900d6b1c9560452708c4d1205400209, 0x28a664409c124804349b014024881aac8c41008550000190),
 (0x19462392500008b0ce25f2934a7c22a04004654040000088, 0x49990290a2c620220500c2811039d590b6a983914400173),
 (0x9011202440686388b6402024b2a220a0100104344000110, 0x40dc09d81a3958843001e5d91404c9040a2cc7ac0140006b),
 (0x31a000000000000006000000000000000800000000000, 0x400000000000000290000000000000012a0000000000)],
  #[
 (0x400318010510000014446001544400000404820041400001, 0x155440000040000001029200001000005011280104040000),
 (0x418d51d84e295885644317d84104cb040a696dac4040006b, 0x8420202011286388b3480031a6a200b5010124314040310),
 (0x1cd51d90a295a85200315d80414cb040a6d6dac1010026a, 0x58120002051684389a2482031a6a200a4110124305400110),
 (0x540318001050020054146001000400015010800001100001, 0x14440014400000101029200005000000045280004000200),
 (0x5040400150000000115290004100020010012a0041000001, 0x1071a000544000100046201001000014014800100500000),
 (0x150000001100020040100001040000010000000010400201, 0x4002014010000111000200515000005000000045000000),
 (0,0),  (0x82c4ca6268d468366677416282202e547cd110d410100001, 0x7429240986218408998880097892d1a28320222a000000e2),
 (0xcee3180230062a390d91ca03888a400b3011004210100110, 0x311467d889c91484500831d86514070489caf9ad0140006a),
 (0x902d5240005b6009a7604210a2b99021053018010100101, 0xdd285a1e6a415d2000b95a451400b44f2c964d40000290),
 (0x19c8e021e2d8822610180021002085a5f2f2c8105000072, 0x5c4111a5415071048a2277ad4b2977000010425450100381),
 (0x932c148266701d9470c040808184600b6361da9500400108, 0x6482a8458185e240822e085676610b149494204800100200),
 (0x742801af8620c9a09988118e789001068323700a00000108, 0x82c68e5068d6165d66768a5082203ec87cd00cb5101000e3),
 (0x422c30015b0d84405428200114ca61005d10a01000380, 0x1141550c004243201052180c4500120944402e5154000072),
 (0x21842087919406789228030422301072d4c0109940400001, 0xc629d6682661f80261962868c582078c22222e60150000e2),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x10030a080111fc835010a208044313f00452080004500172, 0xa4821000000804421c82401008004100e7f151000289),
 (0x2000000800000000800000238000001440000000000, 0x1d8000002380000020600000080000000a80000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1400020041400001504000010000000044440201, 0x444402014140000114000200010400000000000000000000)],
  #[
 (0x922c420025d9883b2c0b1a008911600834db004114040110, 0x94011dbd8000684d1c4c1d974ca9705c904e1ae0100006a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x216802088671fbd39c8f600828d712a0c220800151400373, 0xc68641d33980040862309dd2c7200c0028c268a000000088),
 (0x40000000800000328000001d20000000000, 0x16e0000032800000190000000040000020c0000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x40000000000000051440001150000000000020000000000, 0x110002000000000000000200404400015144000144440201),
 (0x3c415602918064004d70bc034820880285d0bc0005500000, 0xc01220010c648802208f020085d464001822000200000201),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x41440400431022515416045101c54400401440450002e2, 0x5502bbd14114c455000081d0041430a21001609400000000),
 (0x40000002420000002000000114000001080000000000, 0x31a000001140000030000000242000000260000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4400000000020105500000001400015000000000100200, 0x501002005550000000000201550000000000000050440000),
 (0x20a0300194481838768348012390d008c048324054000110, 0xdd5047d82286a6868158b1dac04d2707368441ac0000006a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x105ad881100280141402f88501380120506a49040000191, 0x440240124012c4bc14161012004474a50051192404500008),
 (0x2500000020400000080000001400000004a0000000000, 0x8000001400000011600000204000000840000000000)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x50402000400000005040200000000001440000110040000, 0x4000011100020000400001000000000004000001400201),
 (0xce610200308c303b0d10000188001609309ba64010100110, 0x311c7dda89424a84508193d8659d4904894041af0140006a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x9382326669932e017261806783624ab26983c92211400380, 0x64688c01966001508d8820007c80a0058234168004100072),
 (0x2d8000000800000025800000238000000c60000000000, 0x122000002380000018400000080000001000000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x105400001400020000400200510000000014020114000200, 0x40000014140000145140000001402015100000041400001)],
  #[
 (0x248a020044845003b4604800b0230e001496a20241040001, 0x1341802b0330c004081a20341d05003e0601c0110500200),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4100a4004000b0515504a4510090e90040c451450002e2, 0x55006e5b41158e400000185a041440161000300200000000),
 (0x144000000040000007a00000328000001640000000000, 0x28a000003280000008400000004000000980000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x504002004444020040040200100000014114020100040001, 0x11000000110000000400001015400000400000015500000),
 (0x5902040340396438426ac0006d450a0b007c304254000310, 0x24903bd82c4402849d040fd8003a11047c01cdad0144006b),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x11405886004304e21050a886450129bc4442416254000190, 0x507410014490d440615400012004010051e1401000208),
 (0x204000002400000023a00000028000000880000000000, 0x170000000280000018000000240000003660000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x115400000110000000000201000402011004000000400200, 0x440002014444020055500000115000004440000101100000),
 (0xe4c41403058f24020318620086009001518b260345400000, 0x208620082409201f0c0140201db26028654900000100000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x92c0100829d48ba2237054089224e81138d0501001100373, 0x212b2f77c623341dd88f03766c930440c72422c510000088),
 (0x28000000280000000000000240000001bc0000000000, 0x24000000240000001bc00000028000000000000000000)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x40402000544000110540000000002014044000000400000, 0x410000005000000004000001555000000110000044100200),
 (0xb0080fd908b20086644029da811d83070ce65dac0500026a, 0xf925002c10cd63818aa90005ca03808d109004000140111),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x3028426987355c50888bdc6929864510d726c04854000008, 0xc68284922882838f72240292c220a0ac2890021600100191),
 (0x3a4000000b00000006e00000208000000040000000000, 0x5a0000020800000210000000b0000003280000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1000000110020005040200040400011140020105000201, 0x544400005440000040100001115002004004000010500000)],
  #[
 (0xd5f30dda080ea484a17201d8e06525051c0ce1ae0000006a, 0xa082001b4601a3a5c092a010918d008e0611a4054000110),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2169208e8670d3d39c8c008f28d5b945c220d1e451400210, 0xc68418303982000862333e30c720420228c120030000002e),
 (0x3e800000080000003c000000238000001440000000000, 0x2380000003c00000080000000a80000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x404000004400000151040000100000014010020010400000, 0x141002001050020000400001055402000544000001140200),
 (0xd98b39db09a116870d0243d9810c050758a253ad5144006b, 0x20444600901e2838f26d180218f24208811c284000000110),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1140a2800042019810505881450024aa4440000054000190, 0x5447e0015c0454406207e00125b011004b64c01000208),
 (0x80000005000000190000001240000000000, 0x39e000001900000032a00000008000002520000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x450000005000000010140200510002001100000144000000, 0x104002010544000104400000041400014450020010100001),
 (0x635504026c2162384158240051110c082c651e4140440111, 0x14aa61d8015400878c2059da2c661106511041ac0000026a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x110750080002cdad0500020814000c4d000422070000008a, 0x44002ed041012212400650d0000510004400893011000320),
 (0x80000025400000258000001a8000000920000000000, 0x92000001a80000018400000254000000240000000000)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x154400000140020110140001015000000400000101400201, 0x1002001004000004000200040000010150000010040000),
 (0x9c982a02709e443a31d846028802880920cf004040040110, 0x426115d88d41b2858e2689d921cc2304cd0047ae0440026b),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4c900141b25010150c81010a0185400d81c10000172, 0x4444e8364141e0901452ae3641044f060047044244000088),
 (0x204000000000000017000000000000000000000000000, 0x170000000000000020400000000000000000000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x411402014010000140400000100000014004000005000201, 0x40000001100020011140200055402001140020110500000)],
  #[
 (0xc72143d818e600862622dbd8800d810648e3d7ac4140006b, 0x10d408008118d639d98024011da03a08901c204100040310),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x105c100001002c91112010010405ae74054120815500200, 0x540226dd500070320045badd44178108010228d1400000e3),
 (0x92000003c0000000280000003c000003600000000000, 0x80000003c00000014000003c00000001a0000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x41400010040000005000000015400000014000115000000, 0x510002004114020040400201100000014400020000000000),
 (0x84c4dd88861b08452d05bd903902305dd6069ae4114006b, 0xf68222021682403a8926a400cc228c080282844004000310),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x92c157ba29d70c98237221bb9224905138d1c12201100373, 0x21280800c6205322d88c1a006c9169aac72424c810000088),
 (0x80000003c00000001a0000003c000002500000000000, 0x12a0000003c00000104000003c0000000080000000000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x10000001104000011540000401400005504020054100000, 0x1402010410020140000001104002000040000100440200),
 (0xd9122001cdfc4000200cc0162003a0018890c0051000200, 0x624a140363003800ed9320001ddbc4002340220004140001),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[15+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

end Format7Border
namespace Format7Border

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check0 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 0
        (borderCoords (0,jk)).2.1.val (borderCoords (0,jk)).2.2.val =
        (2 ^ (borderCode 7 (0,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check1 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 1
        (borderCoords (1,jk)).2.1.val (borderCoords (1,jk)).2.2.val =
        (2 ^ (borderCode 7 (1,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check2 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 2
        (borderCoords (2,jk)).2.1.val (borderCoords (2,jk)).2.2.val =
        (2 ^ (borderCode 7 (2,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check3 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 3
        (borderCoords (3,jk)).2.1.val (borderCoords (3,jk)).2.2.val =
        (2 ^ (borderCode 7 (3,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check4 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 4
        (borderCoords (4,jk)).2.1.val (borderCoords (4,jk)).2.2.val =
        (2 ^ (borderCode 7 (4,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check5 :
    ∀ jk : (Fin 2 × BorderAxis 7) ⊕ (Fin 7 × Fin 2),
      imageRow 6 (2+7) (2+7) (6+17) x y z inverse 5
        (borderCoords (5,jk)).2.1.val (borderCoords (5,jk)).2.2.val =
        (2 ^ (borderCode 7 (5,jk)).val, 0) := by
  decide +kernel

private theorem spans : Border 6 7 2 17 6 := by
  apply border x y z inverse
  · decide +kernel
  · decide +kernel
  rintro ⟨i,jk⟩
  fin_cases i
  · exact check0 jk
  · exact check1 jk
  · exact check2 jk
  · exact check3 jk
  · exact check4 jk
  · exact check5 jk

end Format7Border

namespace Format10Border

private def points : Array (Array ℕ) := #[
  #[0, 1, 1, 0, 0, 0, 1, 2, 2, 0, 2, 1, 2, 1, 2, 0, 0, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 2, 2],
  #[1, 1, 2, 0, 1, 1, 1, 2, 1, 2, 0, 2, 2, 0, 2, 0, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 0, 2],
  #[1, 0, 0, 1, 2, 1, 0, 2, 2, 2, 0, 1, 2, 1, 2, 0, 1, 0, 0, 2, 2, 2, 1, 0, 2, 2, 2, 2, 1, 2],
  #[0, 2, 2, 2, 0, 0, 2, 1, 2, 0, 2, 0, 2, 0, 0, 2, 0, 2, 1, 1, 2, 1, 2, 0, 2, 0, 2, 0, 0, 0],
  #[1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 1, 1, 2, 0, 0, 1, 0, 1, 2, 0, 0, 1],
  #[0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 1, 2, 1, 1, 0, 1, 0, 1, 1, 0],
  #[2, 1, 2, 2, 0, 1, 0, 0, 0, 0, 2, 2, 2, 1, 0, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 0, 2, 2, 0],
  #[2, 1, 1, 2, 0, 1, 0, 0, 2, 0, 2, 0, 0, 2, 1, 0, 1, 1, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1],
  #[0, 2, 2, 2, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0, 2, 1, 2, 0, 0, 2, 2, 1, 0, 1, 0, 1, 2, 2, 0],
  #[1, 1, 0, 1, 1, 1, 0, 0, 2, 0, 2, 1, 2, 1, 0, 0, 2, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 2, 1],
  #[0, 0, 2, 2, 2, 1, 0, 0, 2, 2, 0, 2, 1, 1, 2, 0, 1, 2, 0, 0, 1, 1, 2, 2, 0, 0, 2, 0, 2, 1],
  #[0, 1, 0, 1, 1, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 1, 1, 1, 2, 2, 0, 1, 2],
  #[1, 0, 2, 2, 0, 1, 0, 0, 1, 2, 2, 2, 1, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 2],
  #[2, 1, 2, 1, 2, 1, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 2, 2, 1],
  #[1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2, 0, 0, 1, 2, 2, 1, 1, 0, 0, 1, 0, 0, 0, 2, 2, 0, 2, 1, 2],
  #[2, 1, 1, 0, 0, 2, 0, 0, 0, 1, 2, 1, 2, 2, 1, 1, 2, 2, 0, 0, 0, 2, 2, 1, 1, 1, 1, 2, 1, 2],
  #[0, 2, 2, 1, 0, 2, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 2, 1, 2, 1, 0, 2],
  #[2, 1, 2, 2, 0, 0, 0, 0, 1, 2, 0, 0, 2, 2, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2, 0, 1, 2, 1, 0, 1],
  #[2, 2, 2, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 0, 0, 2, 1, 1, 1, 2, 1, 1, 0, 1],
  #[1, 2, 1, 1, 0, 2, 0, 0, 1, 2, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1],
  #[0, 2, 2, 2, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 0, 0, 0, 2, 0, 0, 1, 1, 2, 2, 2, 2, 0, 0, 1, 2],
  #[2, 2, 2, 2, 2, 0, 0, 0, 0, 1, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2, 1, 2, 0],
  #[0, 2, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 0, 2, 0, 0, 1, 2, 0, 2, 0, 2, 2, 1, 0, 2],
  #[0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 1, 2, 0, 0, 2, 1, 1, 0, 2, 2, 0, 1, 2, 0],
  #[1, 2, 1, 1, 0, 1, 0, 0, 2, 0, 2, 1, 1, 2, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1],
  #[2, 2, 0, 1, 0, 2, 0, 0, 0, 1, 2, 1, 2, 1, 1, 1, 0, 2, 0, 0, 2, 2, 0, 2, 0, 1, 1, 1, 2, 0],
  #[1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 1, 0, 1, 1, 1, 1, 2, 2, 0, 1],
  #[2, 2, 1, 1, 2, 0, 0, 0, 2, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 2, 2, 2],
  #[2, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 2, 2],
  #[1, 0, 1, 1, 0, 2, 0, 0, 0, 2, 0, 2, 0, 2, 1, 1, 1, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 2],
  #[0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 2, 2, 0, 0, 0, 2, 0, 0, 0, 1, 1, 1, 2, 2]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x86508304c12c43913d2525454447437429018205580144041742830a482084214c, 0x698a4c7b0c1080620010c2803b10ac0ad4e849caa38a903a00ad3c95330e3b96b2),
 (0x926d51615ea449b846212c00010a922910014040426a14011a9396d1128606a2cc, 0x40028c820142160090489373cc316c96ed4031183c14229c216c41280d38f11110),
 (0x54371e06b65808096b0c8a04085c3d43c440830d20a340190c3c40224188311134, 0xabc001980906d5d2847251b2b22202a000a93892c840a6a23202370424104c2881),
 (0x822a08132a88479dc34c54046842502519098c084165016902509920892150a491, 0x805d14c455720220c33026390b02102029610528a083290e020601536d02f594c),
 (0x86508304905c43913d2e54454447437429018205584244041742ad2a4820842342, 0x698a4c7b252080620010a8803b10ac0ad4e849caa128903a00ad1285330e3b9828),
 (0x86508304814c43913d201a4544474374290182055a0044041742825a4820842868, 0x698a4c7b6ca08062001ee5803b10ac0ad4e849caa19f903a00ad1d85330e3b9392),
 (0x111c2082006b8c00d1480c308210200200100a504462349640210c676310259368, 0xaa405564219470c40c02b003696bcfbcdd4be48b1a0543282bce838880a4c80c82),
 (0xaa405920c8c470c4857c07036960c00c0d4be4010244432820c0003880a412a019, 0x111c2611040b8c003200083082141d41f0100a5654833496441c7e876310484486),
 (0x9d92ac79c0962f00001c20222120ae0ae0a310ca9c1c266020ae0592d9ca3b8b8c, 0x604d43062e08d0d93d039494c80740741644a20561838099174162690034840441),
 (0xe1c2810086f0c0849546d10a8529209202050e8005544a80792145481881e5c0c2, 0x4103aaa480d10182018001540c6836814a8a10fd28a005086828826243c183a1c),
 (0x88588b0921f391cf6403460d001d00d030450ed4adb808041d01f47d1cf1d00334, 0x268604c406086c10080c207089604d04cc28f100524124d8604c0b808006005443),
 (0x11213ae08316291fa26b24421ac5d35d18c150144291420e85d2002902ae940100, 0xa004841c448052a018049b0581380c80e02aa049894a0491280c299248100098c0),
 (0xf068ae4e69018051b9603642a2a46e46c4652204b08d43b6b46e428992023580a0, 0x79550210068058840138830584280283018c95b042224480281351041b0087d13),
 (0x41194c43e2ec1100805513a01204c04c029410050227f01604c259ba5280062cf, 0x690a2b0940913a0964082e04fc1d03d029d036d48f5900fc1d03d24440c4d00d20),
 (0x26cbc80461912649064529042a16e16d2381e1803028552b16f3cf90245f107d1, 0xa40101618164e80b460a856bbd0a90a924c5214058a52aa94a904306700006900a),
 (0xeaa6baaa61589ba9200922c01c86836820950e0fc028c00886834002913318042b, 0x104041009a26045695629d0c02192092144220801ad409524920b749204ce5db00),
 (0x9c8548c20244ae49430dd19524801001012064c82cb0d4718010223a5c48127343, 0x6050a70921a1410424322442916c4cc4fccf9a17824f02846c4cd58420160c849c),
 (0,0),  (0xe09114c6180800b0c1248254880208222898a52970235489020202caa442f5203, 0xf0602810087e66f0c3603588b212522509742108405988b202538ad344125088a4),
 (0xe09114c1090800b0c1291254880200212898a52992c35489020426caa442f5400, 0xf0602810c72e66f0c36c6088b212522509742108405288b20253a803441250892e),
 (0xf0602810411e66f0c366a188b212522509742108424d88b2025309e34412508815, 0xe09114c88a0800b0c1810254880208272898a529c2035489020921caa442f51e8),
 (0x8102e70029a34988742824c280260d605424a20c18f08284760c122d2831022a38, 0x64a9007d5214b2660a1189084500b00b00884501c70a484000b1e88244806511c2),
 (0xf0602810108e66f0c3688188b212522409742108497888b2025331c34412508840, 0xe09114cce60800b0c1246254880200232898a52908235489020c82caa442f5436),
 (0x6300000000000000000005850000000022a0000000041a, 0xf6300000000e940000000082000000000a0a00000000d8500000000821),
 (0x6b22d61000952b6132021e6f08a41d45e60109564a8c3f0ce41d1a42c665486bb2, 0x10c00921f068141c8548a1003710c2881950c6011442403210c2240c2882128408),
 (0x8a80302104a25085402504a58d82802022256c5b018ff5888280626182d408483b, 0x154bce4c43198d12b950024272346fc6cdd800048c700276646e8d10002335b480),
 (0xf0602810741e66f0c3606388b212522509742108482888b2025325c34412508640, 0xe09114c8080800b0c1810254880201232898a52948235489020882caa442f501b),
 (0x120000000006b4000000000000000000016e00000000c1000000000408, 0xccc0000000010a00000000a00000000006100000000036e00000000304),
 (0x8a8030210162508540281fa58d8280e822256c5b0848f5888280e00182d408405c, 0x154bce4c76098d12b957c04272346f06cdd8000481940276646e1120002335b700),
 (0,0),  (0x3640db00d1e20404361309130bc61061020502c600e0530a861188163b4c5897f3, 0x82f0078020902d14128d028e411e31e15928000961328f001e237a98091a10004),
 (0x21f030d80191cf22f0b047808bc12c118c0001ccb943908bc130023887b020a80, 0x854030c22f4283080000a282264100102132a90334488622010077801584ccc048)],
  #[
 (0x3010c84582101a2618105241252b00b00b5782d8528240203b0004f422a2921a44, 0x8b2023b26ca0850966268990c884f14f24202905293995d884f1090a0c482544a2),
 (0x13bbc8188349c130111640040cd8028000804400c24f110898020c2811c1561881, 0x280416e308821449e0613d08b0048c48d118039e252008a4448c20d42404082616),
 (0x3640db0012020404361041130bc61061020502c60032530a8611a0463b4c58920d, 0x82f007808b902d141213a28e411e31e15928000940428f001e21a898091a10482),
 (0x3640db00b1320404361012130bc61061020502c600e5530a8611a9063b4c5892d0, 0x82f0078028902d14127e428e411e31e15928000940228f001e216f98091a10821),
 (0x47e5870353018022740114a990460c60c07b4b0c2000e8c0060c65828893020cdc, 0x981a107c8cd645440a062a562090b00b3e840001c008073490b002014060652223),
 (0x20aa2084a8200014081b012e818061060e26448004e13e91806180610b0021a601, 0x4845d6515146c642a0442c40587e0ee0f149b8455a00404c6e0e0d94b473424828),
 (0xd03416a90e01320c223818625c46dd6dd9aa08849a88275956dc50b21a2606950c, 0x8c221069036c971dc452394a388208202551548051790a288218f414589216811),
 (0x635b086451b72469a4604c8c18031033135039308138c84803105204c902b1c69, 0x384849602a44881805192925005a80a802c0680013c031501a8092159041102394),
 (0xc120130d824840022f1a2034043c10c13ca0241ce3c930503c10c000bd30020305, 0x1a8340c06c018c8800200149b1810010010d8903000448a0c100327640c5cce020),
 (0xcf082041424562b01201006d7b0a51a5183597122282682e0a518922e830088007, 0x10971fb4a98200452d20df920014ae4ac60840c45d04835154ae50c111c2714010),
 (0xa8b0d160768110884602446d8c0a91a910385040461078984a908840d51d068d4e, 0x57440c808872083790701a1203b16e16cf010c1821840307a16e168c2240f11231),
 (0x9aa9c30da06214292f1648a6a16c13c1081a2b1ce918e6b56c120476a659020007, 0x204030c048888804000124110e81001036e154030483010a91005b011024ccf1f0),
 (0x8977116060044dc046045c02280a90a92d34a2407946062d4a906d01828306a6d4, 0x5408ec831a0290189061a07091116f16c04a541800a071c0016f00e87920f11903),
 (0x485814019082a828032061ec1ab15e15c249c80800b4b90bf15f36910d68c201cc, 0x95268804627117d4481c120341000000011235c37e03061400000164b0121c8202),
 (0x9381fb4b2d403352d0cebb15874ad4ac90841c45004e04824ac06f369937152f3, 0x464640420022044a12231400870a50a52426881226e110861a51190c844c088004),
 (0,0),  (0x4020412324a2e4848449821e211180181322864a69024a210180e0e5e2ee881c01, 0xb52321489491813793205e084a442442408389406e8b080e442160204010662f6),
 (0x402041234822e4848449901e211180181322864a604a4a2101801225e2ee881050, 0xb52321413c91813793202e084a44244240838940184b080e44280c20401066e27),
 (0xb523214c1591813793040e084a44244240838940e41b080e4420d020401066688, 0x402041231a02e4848449ab1e211180181322864a60324a2101806075e2ee881070),
 (0x22f80e4cd28a2475b9624e5a1e046e46e2c2450482180a1b046f29e291c035a32e, 0xc400f02308559b00400d2021e1f281281821305b304224a4f280100d2e0f085401),
 (0xb52321420091813793041e084a44244240838940d97b080e442004204010666c0, 0x4020412342b2e484844c1e1e211180181322864a60404a2101805315e2ee88100a),
 (0x7a2000000000b800000000000000000000b90000000044400000000420, 0x81d00000000c420000000000000000000444000000000b90000000035c),
 (0x20883d48c9a158e044089c249aa12c12c1c0f310c022609ae12d40205521b1c087, 0x8d228010365627068051409b404201200e0b0c811e089e051200114888c0020568),
 (0x86508304080c43913d2a254544474374290182055bad44041742800a482084208a, 0x698a4c7bc2b0806200101a803b10ac0ad4e849caa012903a00ad0555330e3b9670),
 (0xb523214a1891813793250e084a4424424083894084ab080e44215120401066432, 0x402041234862e4848448ad1e211180181322864a61b54a2101800885e2ee8818c8),
 (0x8220000000034c00000000000000000008f40000000030100000000620, 0xc400000000c010000000000000000000301000000008f40000000005f),
 (0x86508304f43c43913d20d645444743742901820551a044041742205a4820842440, 0x698a4c7b02c08062001009803b10ac0ad4e849caa85d903a00ad01a5330e3b9903),
 (0,0),  (0xc102303198d9d489834b8cc14250e60e5410684084ac805340e601008454102832, 0x4184b4005022124509421200c870870a22d16246212610c870870ea700b2a10c0),
 (0x601cad62899d081593e320c042364c64e61248484ad294427e4c00a3f01f52507b, 0x1ee252053222a2a80c149f1a1941b11b11eca5a594284b0c01b0bc540da0010c80),
 (0x3228103401519028482195380048e38e1cc0cb1a6a06294108e3340358d46b9204, 0x1d72888b88c48c3110c6a43e7920020201610c190b846a69200c0080109144d3a),
 (0x44822a1037311642296a1e210304a049252340c0050a214384a44d0060b043ac8, 0xb06c5129400cc8804201001edcd10d100214151b98c05a9c511980b01e0d90513)],
  #[
 (0x3722612a3a3a618580f608594a1b84b84af985200911080a0b8408212882642928, 0xc0cd0c8041440c623201c7a2a1006006100222da42e0a7b05060d312d500021484),
 (0xc0cd059bd0240c62710933a2a1001001000222801344a7b05010f422d50034b020, 0x372268642f8a61850eb20c594a19c79c6af98528ec9a080a09c709012882094e52),
 (0x509000000000d000000000000000000000020000000023400000000006, 0xa220000000080200000000000000000002340000000000200000000fe9),
 (0xe08c0a120089303e30298234508500502401041d1110240495007620910990c808, 0x1a21f525a8624640ce4279000a709e09d0cae9802a22401a609f01c22c64441213),
 (0x116adc7b0006a8a8001102cb3010ae0ae18025ca810ace3000afd48f80ca3bb01c, 0x80503044ca956033d0e182089c741740649820554003088d7402b201910840cc0),
 (0x342b0078061381a14102540424f1e01e05a7d4009a5c0020b1e0eb2146afa10090, 0x40440b0118486842362d83b9cb061261180001c62120f8df46131444a040589864),
 (0x2d04a100c090a0230351260c01500500725181d00d0248045004238004290c9d0, 0x3820052543365180ce424c0922409f09e8c2268008215873009e19c3a994443008),
 (0x46cd46a8611810b322080262a4d6de6dc34f0684999d23a596de60a12401068300, 0x991281079e01480cdc426c090228218208b0f14804001c5268219e1c93da215ca1),
 (0x7194845290e822e180378ad9e2b00b0280401d86e82b98b6b008114e504921051, 0x680093b240a034c0661083104114f34f133a36050165004014f24c400848256924),
 (0x5214e70956030c60240f2488814c4cc4c9cc2c179baac9850c4c088310050c9319, 0x206a08c0a8b0401943301a203a8011011610d0c80044346ac011a06cef8a1260e4),
 (0xc922b82d3fb9589388541f210908c38c0561fc0a818b214808c29c22968f585100, 0x109845d2c000a70c1523601202610c10c214024024205617610c02d1690086283c),
 (0x110585256580d27cce4e0020c2409c09d0439d8016b371c6009cd08930ca442309, 0x8aa80a120a2c2c01301034da15b5005027b4601d00048e11f5012f728a0490d802),
 (0,0),  (0x1db3e04048582086b2c0a525a4c3cc3d8a01c0d1307024e1c3cfea00805310052, 0x1c20019a19425ca58440b18405b20220020ee192e8288001e2030153b3084c1ba5),
 (0x503004054c115d91201804d108a52a50e32201208000814ca535313048b08913f, 0x28409fb6022c2a042d367f92e164ad4ac0014ec472a5c3a024aca0c040647162c0),
 (0x2f0036e050074470000014c10117c07c00100746920c900507c09a0203e04500ac, 0x90b0410625300300389ae338e828358371a2f0a840f229a8783560247c0090cd12),
 (0x503010280a115d95e61424d10882a828e32200c08000814c82b3c93048b404022, 0x284092d1445c2a0421123992e160450440014ec22340c3a02044c040406408a558),
 (0x240a384740a69241008320a0053003010232940c1185a014300a11007040d00c0, 0xb8b350108a941089e8234ca419804f04ef8096292e01a018904e4ca5386b501409),
 (0x5030480a14115d93bc3104d10808808ae322042db4f0814c08994b3048b948808, 0x2840906c1e0c2a04843c6392e162472440014eb004a0c3a022464a4040646a1217),
 (0x2032e0304a252a940c90e14f0b111110e004123618311b1a1100811430b4d8014, 0x95f0c1848a492c548130c163084c66c6519198989a48620c1c66f1063884a03b61),
 (0x28409c05299c2a0402248292e169249260014e461a03c3a02925207040642b834c, 0x50303ba426115d921c2104d108658659e32201860040814c6580b83048b802c10),
 (0x2f00322c0c974470e67711c101100800a01007c830a090050008a0b203e00544a0, 0x90b044837160030008808438e82c96c941a2f0048a1c29a87c960e047c0000101b),
 (0xb8b3508247f4108918184fa4198e45e44f8096800404a0189e442c05386b910808, 0x240ae50200a69240004300a00510010102329651bc25a01410041100704007017),
 (0x240a01b066a6924233f050a0051001000232902a0a85a01410100000704c57d4f, 0xb8b355a491041089884078a4198856857f8096500817a01898564c35386b028020),
 (0xb8b35260e184108994d4b3a4198d04d04f8096587810a0189d050805386b504414, 0x240a5171a2a69246b0a4c0a00522b22a0232922822d5a01422a73a00704aabaa3),
 (0,0),  (0x8d22801051362706805c649b404201200e0b0c8110289e051200cb5888c0020104, 0x20883d48000158e0440180249aa12c12c1c0f310c783609ae12d30205521b1c8a8),
 (0xa05af0144a2a6942a160228190444254013d0c0e011984851443084308a78416f8, 0x52840408a4c186a94e95442a00a2202212c253a006463b50e220f1a84358680805),
 (0xdf0440c1b1d00a465294b3040a463460cf4530f14f32010e46296e3c1062611c8, 0xd2068950e4e2b10b8ac4b4850a410c00d009ac30ca00c54f110c00001e9859cc10),
 (0x101286545041212c1030086110a31021392729c994402404e3109c115000073885, 0x48c60218300c210acc8111eed148c58c240463641961af8148c42462cdc80424a),
 (0x8d228010552627068055009b404201200e0b0c8114729e0512008a0888c0020605, 0x20883d48228158e04400bf249aa12c12c1c0f310c38c609ae12d74c05521b1c1e2),
 (0x8d228010840627068053989b404201200e0b0c8116929e051200801888c0020100, 0x20883d48581158e0440c20249aa12c12c1c0f310c10d609ae12d5ac05521b1c4b3)],
  #[
 (0x3c12b092809317615c9113124180000002580020a04e02508000656218188e5057, 0x325082d3f282004a1408869a06f9ef9e8a72a571b012da02f9e1a8d6505510e80),
 (0xac85770a625b246424000c00094c4dc4d915d817815804085c4dc4eb00050c8300, 0x2288c10c845011433193aaa0b0120102ea25c83ca0bbf5a012030466f8126cea),
 (0x20000866a21080ca63892d2021e4cc4cff568364ab082031a4cc98e99cd2d78601, 0x5055270804437110907440c384112212000930814437d7c01123040443042830f2),
 (0x805e14d2c2111900c21b00432a0220202508252854d5067f023044038d22f7443, 0x876208129016662cc34800d2c502512535a475085010878002502a1ec224508094),
 (0xa84604601000015a28a8070a0d85805805b02826a39d0a4dd5808314570901285b, 0x5629eb0d4fc78a81d04368a0e0303003220655481860f1a020300c6200a0349120),
 (0x9a509e05ad46400c6b108fb9820c3cc3e441800d3c10b8865c3c0bc826493106be, 0x1af41981010ab128466504479c2012009a86592c26e44388201940508824c2000),
 (0x1983f1ca9a9a08123834142018650c50ea5002440201700c750d81854e484a2001, 0x46080831014474cd4383eac0a60aa2aa0508eda0a15e85a20aa25e488093b44b30),
 (0xfe4402e68c321c26a96024a486b48048276c40552050a193a481b0280467428289, 0x13bb019214000c9520d1941614950950893b88293aa546409504d07e218881d16),
 (0x145621638a0051024606a015102a91a9042b5240556214006a90a601bccc068213, 0x4a899c8045a002fc90500b006b816e16c3c08c182010403f816f01800033f11c80),
 (0x7ce0199c40803005cc505aa0349342341664c2118e28b021d3438f6104659201c8, 0x820b2202066f03002003a441c86c21c201801d4410c644cc2c201008e19a619826),
 (0xda870501306809847aa0c011840d00d026611c2e0c2000841d00340004ad01c4e8, 0x430dab68d83d623041e380e4040e10e0008c181f05d4e1140e08202c812702816),
 (0,0),  (0x999410400e02828412232900d40a52b51811c812080000c15a52367cac20088c0a, 0x222a0fb4816c71522d00946f0864ad4ac20617c464fb2b1c24acc1010315714345),
 (0xb1400000000022000000001020000000006100000000b0e00000000da7, 0x40b000000009c50000000000000000000b0e0000000006100000000018),
 (0x90a5041851a3002839d24162040801873b4208280350231008188a150354021b0, 0x4242f2c384185a42440daa81d395b85880318550d48b948295a144a80c01f1641),
 (0xa80b91c40cfa864005c3643444ee07e0e032b34221412004ae0702084801418800, 0x14b46802600411095a1090c11901a00a0088409982b4810911a06cc212243845c1),
 (0x2f0030d81d9744700a4bc1c101152443401007036022900505245a2203e02659db, 0x90b04f25a0000300b4b02038e8220920b1a2f044869829a8720905d47c0011a424),
 (0x949a200889c936221161c886c15380380204c08100509290538084072cd5469800, 0x220440916004c0d4889a3251340c76c579a12f10eaaf00640c776948d3002867cf),
 (0xa525a881362023428005808279870460530483112a18833c87044283081018aa04, 0x189a166a418f00ad79802c5d00507803a839680e01c7184010798560c2c1665000),
 (0x8e0076725c02e21b60144f8a450b0ab0829c840fc8028a100b0a090b1910008898, 0x1218800a0a4158408e0b0518880f00728212880039501c8c0f1b0e4e604304106),
 (0,0),  (0x222a0fb4b00c71522d00cb6f0864ad4ac20617c460102b1c24ac8b210315714022, 0x9994104041c2828412292000d40a52850811c8120e2e00c15a52108cac20088404),
 (0x189a166a415f00ad798c205d00507807a839680e0612184010797030c2c1665806, 0xa525a88198a023428002968279870430530483112088833c87040fc3081018a030),
 (0x4242f2c010185a4244484a81d395b15880318550020b948295ac2ca80c01f11da, 0x90a5041086a300283934a162040808833b42082885f0231008118015035402020),
 (0xc00a808161448130681602524619069042323ac41463524619060302240d028f4c, 0x21602d260e83260d04206d2c10664864ad0cc1324a18290126486429c1f2202002),
 (0xbb48a490df0a488a85698078000b05b041fa6468123128510b05a2704c8ba68448, 0x401749280064816522800c015de02a02b805121464ce150ce02a49062110483900),
 (0x58d971618012b094f062d7d84fc02302009005650274885f802200861900082c8a, 0x83020e0a168d4e0003880800002e84e8720d5202588801007e842238e299054220),
 (0x8ac505181a45442813009112a2aa03a0022b2fc22ca157a6aa0384221466816823, 0x441252a4a0a8a88280e344ec0c009c09c5504028805ca818509c008dc3004a9140),
 (0x2032020700252a940088214f0b280283e00415b164011b1a2801121430b085109, 0x95f0ce4c00592c54b972456308446c46c1919804800c620c146d4886388435a634),
 (0x240ae04249a69246b2b440a005c3ec3f023290d0c445a014c3e02b00704312202, 0xb8b3519b522410898454b9a4198201200f809692e0a9a0189200b945386b4c15c9),
 (0x9500000000ac100000000000000000004b30000000000800000000110, 0xb48000000000060000000000000000000008000000004b300000000428),
 (0x7004242a02102527c161405a01098c98d1b03081d53d4e14198c0ec01f5082f154, 0x54159d5e9a440881e06a300ae8012010e4b4902004011ab8013c117c0241802a1)],
  #[
 (0x208440408030e2510c09011b5a0da0c0a088110545505b0a0de5211087442a08, 0xd14913b21903841c242336b60085a25a3d07120e10a8a20085a21a98a318abc1f5),
 (0x20ac826964494890a14812d048390391312461010932c11839020012f40d6c328, 0x6474224969886046b0617480925422420869b88cc468918644239874401d213c82),
 (0x8c6d908355050042d140008ca0202002197a02505311c8e060202964ca1a258a44, 0x721225648a6a28980c232e010a0bcfbce404a48b0c0e150a0bcfd41010a4c83091),
 (0xec32421302881800108c0882752cc2cc2b1069059329c6712cc0c8308c5005ea0, 0x21304248c4015c32f2773751102531531946d9478648011065317060e412eb215c),
 (0x5248a5036f70401e0758530815e43e43d8c2206085820905e42041714281c40c0, 0x30c800810108710a03023a442a21301300038d494307506a213028a86090a11619),
 (0x248999f20d85668cc722120609340341b155311acc864208341a140c006920340, 0xe08162005f2229832008cc4a1e6c20c224ea284410261b5f3c201c2b24e9619431),
 (0x4365c32ca4f040e020150239439bc9be04665d11da7229129bc90809573b52846, 0x59c8208930204be1102427d06182402402099808a0588464d241281c6a08424289),
 (0xde12907c039000960a290a111900b20b10803601c688405800b3e026a187650a41, 0x208c0701c028bc417400e1c406d60c60c627800c18208003c60c0f88404002143e),
 (0x20520320c02981201aea03362c21c20640e14412dd03726c20a3a23346618003, 0x6a97099c562c943acc6115d088d34234101d06118502c48c93431c5504b19238f8),
 (0,0),  (0xa2475a17be390ba3401044020ea8e48e412423284300460be8e4802e24c98940a0, 0xc980160010294181d09b080e04403403c421cc32c4490e014035d110234641a52),
 (0xc01200c412d009450201401d426595594817282212024c0625951b4c28da041981, 0xa419120652ec02abc7ca440189222222668c28c44a401588222e4338105d1042a),
 (0xc38430150cf081ac12610206a520c00c2441f24688a803e030c000072006b50e15, 0x383a8aa2e2031841e58040215a0a02a012be01997654641f0a025818d0084280c0),
 (0x848a860812045d1120b409c0b2324124020cf40010b6d5b23241f42ca3e800050b, 0x680449b6e91382ccda00e41f0404144155510141c9090a4544140a010c06657280),
 (0x68044021406382cc8620201f04009409455101a102060a45409490310c06428166, 0x848a8d1ea3145d11605143c0b23f62f6320cf414acf9d5b23f622c0ca3e81c5410),
 (0x543408dbf044c49c01c666e64c19259264e304080344b2480925a01153e6612720, 0x30af5000b801a21942800181302d02d030c024654114c1242d0004a8c08161050),
 (0xc98028032029418d3a15e80e04c08c08c421c4c853890e01c08c5e1023461822d, 0xa247544e41a90ba3205e20020ea16116112423b30ac6460be161081e24c91e39c0),
 (0x5aa25815a1264a2551ca2164a255545569851a1e93ff64a25554742a551a3c2ae2, 0xa551a18a5809851a0601429851a22022164a25c02c009851a2200205aa2581d419),
 (0xa247512504190ba3ec02a4020ea004004124239cc808460be0041a0e24c9015002, 0xc9800d00002941812a10b80e04f61f61c421c63370590e01f61e1310234faa399),
 (0x46c91f8b94081476bc40e09da884cd4cc0311646e8ba98ac94cd01a20a2375ea32, 0x2014c05408954280022a0142545320320b0ac921030103114320e6508510080005),
 (0x54340c82a154c49c868a12e64c1d18d194e304599649b2480d18c0c153e613800a, 0x30af0091e001a21513021181300c30c030c020601044c1240c3233a8c08843850),
 (0,0),  (0x6502242804210c15c1720a840b498f98c825cd81e42ad50b098f3e88023a82e5e0, 0x10e1c9d68288824a1e01b521b080100107d81002124020f4d010c041d4c518001a),
 (0x81108380059026c438040d012b637a37807a8a876854406b6378258f82844f1aa5, 0x4a2a78080a2c903b8741206e408485486e0414408528af0088859870042b302052),
 (0x5aa2516076a64a2546124464a25a91a909851a40461264a25a91885a551a068d4c, 0xa551ac828859851a90401b9851a16e16c64a251831859851a16e1685aa25f12232),
 (0x28e04604e019100002a6320806d56d6069b6104404a24c0ad57963ac744049c8, 0x41430299e01266817418190c71110a10980440cd819b0c3141080090030a209423),
 (0x2f003085320744709a60c8c10110300300100793114290050030c04203e02b2600, 0x90b049608140030005010438e82a81a831a2f0002e2429a87a810d247c001001fc),
 (0,0),  (0x84a0000000080a00000000000000000000c10000000011400000000eca, 0xb4000000007a00000000000000000000114000000000c100000000135),
 (0x21382c9a1621e00f0300421214c58c58db03d63a0b0206409d8d139d287c1c1406, 0x82c6d060e00a00e074a485ad2a184284006421c0a09c383f40408462d4812263a0),
 (0x8541120e8a6ba542c840361e22e292293126023411154a2792924808e222a2b011, 0x3a10e031048002ac179e49c0091561560600f148aa8a90482d6012630059410344),
 (0x68a42044c20309009e5003896f340040308200700422183bf40163536604423005, 0x1753090a09d0906a608fa820000080080b291d8a099420000880980c00a9b809d2)],
  #[
 (0xc4913b0044198e99360464214276136102dce4c60215a0002612042108d0588a12, 0x2824807b91607002411b9344a501e01e00220800894a05e641e0c854b52da11484),
 (0xa0016040020981d0ca40083547127124602a02124009301f13c5204b480cdc01, 0x8614ca0234c0342c0414a2a5ca90a00a0a910164e58fe48280a0300a9085910052),
 (0x807500000c21d924110a40c250b47147210afd23a0194630a470510e06c38b44a1, 0x720adc53b290065a6684350d85038e38cc61001010e298855b8f84c1c82c542056),
 (0x9d1440023aaa042441921862d9ad20d203000e001421264da52190162c8005c8a6, 0x604203e441517b900a01c3090402002008eef0f5c31c18804a006400537fa23310),
 (0x61e86a121086455355308408213b12b10852e17606420a306312231b092838c88b, 0x8c1205ccc3610a208ac7722506c4ac4af28104001020a50694ad58c41492053504),
 (0x820d5023409e048a4028b6501192812824e7e65b06301100828114140d29085015, 0x38e08e4c09204815b9570009a6646c46cb180804b08b44f6646c42c3a256358080),
 (0x410328ccaa00ae4c2d8da022a40020023001f000488446e00020220420b455aa2b, 0x260c842304de41a3422051cd592f4ef4cc6e02213452281d274e98f3d04a221484),
 (0,0),  (0xcc81a2006d16810e20142e4004dd61d63250468640a500018d600a08d062af2a16, 0x3024059b10093c0187424018b3221c21c8889058824a0da6621c81d22b09009560),
 (0x3024022027193c017e31c418b3206806a888901c06030da668680a822b090541b8, 0xcc81a5c410e6810e0008394004d19219025046c05084000185912508d06242a003),
 (0x2f0032c81087447003080cc10115325300100704de1890050932745203e0600236, 0x90b0410427100300f816d338e820cc0cc1a2f06b00c229a870c809847c00987d49),
 (0x90b0420a16f00300c934a938e824c04c01a2f089848a29a870c84ad47c0068a210, 0x2f003cd4c0074470248b06c10118078050100720507090050c07250203e005502b),
 (0x90b046a95580030086210c38e82d50d521a2f03c4d8029a8794011647c00163115, 0x2f0030400a57447050dc73c10110ac0ac0100781b22c900500bcec9203e02186c2),
 (0x90090000031c31c000002a12a10000029129100000a81a8100000285285, 0xa10a100000048048000000900900000005245240000052052000000d30d30),
 (0xc14672105ae3a014cd184605a156456493a2626811a240b15256d140469832900, 0x5321981ada40c07e11226b99a4e0930932c09118604099a0e8d29208a8826886ab),
 (0xc146081504e3a014c22ab605a1a46a4693a26253001240b1247011404697e06c3, 0x5321906421a0c07e23014099a4e1b11b12c09188497099a0ed30e828a882801930),
 (0x5321902438b0c07e0c559c99a4e4204202c09130a0c899a0e5204c08a8821d40c5, 0xc146110444e3a01a38800605a101501593a268e1b17240b1814a0240469e08e3a),
 (0x6011c0c00c21860ea860c0204dc5c95cb36220a40650200c93c865ce8702670225, 0x8384112860487971420325811208368348084150c8a99402003788005089886d08),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x440000000000480000000000000000000291000000008680000000018a, 0x1be00000000a8500000000000000000008680000000029100000000c64),
 (0x2f003115710744700d2224c10114004020100704269c90050400a36203e0315a0f, 0x90b0446a0600030012d0d838e822d22d01a2f058592029a872d240947c000804b0),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xcbef14014b6a40000338393519015d15f5e1e00815d62149415c60bc405bc210c1, 0x10e806b0819db24805828a82200000081e16c34201de96200183418b241cae2e),
 (0x2000007e080041ac0a0003a09220b00b2c964001d1c9b49330b0064416a4650105, 0x8086a701f362b8117408e81761d60c60d349330c20144364860d78b08950023898),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xa0000000081800000000000000000008040000000063b00000000112, 0xcb5000000007a2000000000000000000063b0000000080400000000a89),
 (0x201e940000094046000000e00e00000000c2cd800000e0002100000104a0e, 0x6004b000002831190000002502500000b211060000002581a000004e3470),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0xa89001963aeb040522d120b219953952057da82904a5a20995241114625880a10, 0x3452f2e498404614a9520884c42480480d802155203185d524818e0aa082428007),
 (0x9014b81a31590188112e4480a03800801d032000df2e85e138005a02563c562e11, 0x45c246e0ce84fa53e041803c49848e48c05c999e00407818848fa0ec28810800aa),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x22300000000a8e0000000000000000000806000000006180000000004c, 0xd180000000055100000000000000000006180000000080600000000ba0),
 (0x90b048e06360030009245b38e828048041a2f001206329a8780401f47c00681993, 0x2f00301e98074470864a00c10116eb6e901007868600900506eb080203e007c26c),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0x672c014951b9160f070222804840700716010899aa8d904c00703648160461402a, 0x981054162a4401e0886dd85b36a30d30c98ce24205324a32a30c0096801a8c1845),
 (0xd13098c340020046430f842615101201056718c81021220050126f06414e126906, 0x2a89470827d1a2a824103210a04c4cc4f288a717a61854f10c4d10d93a300c9269),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xcb400000000bc000000000000000000000880000000032300000000903, 0x1400000000040800000000000000000003230000000008800000000014),
 (0x90b04240944003004bc00a38e822482481a2f02a816129a8724848547c00a1b6f6, 0x2f0039a94a874470940e60c1011c06c040100745580290050c0635a203e04a4108),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0x825eda5061282042e04bc604318e40e41091240610a040219e40c81030881c5184, 0x31a000800c0391800330310a827130132428194947150b92613127000947a12012),
 (0x83951c8028980c839041206111216c16e6967b1800842400616c02840961f106c0, 0x4c2ac16290248078463c8d04ee4a91a9086004404b5241ef1a904c63721406803b),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x19600000000450000000000000000000040d0000000080200000000032, 0x60100000000aae00000000000000000008020000000040d00000000f44),
 (0x802d110000021a80400000a0ca0c00000ab82b200000a0c20200000e4b129, 0x31808c000001a074a000004d34d300000000c05000004d30dc00000024e50),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xd40c082878920c0d14084c010f02302144011504b028050e022227c82bc25b800, 0xa0252564786099040c1f6033820bccbcc00f248b04e566831bcc59837441c803a7),
 (0xb21d23048a0070163d306318b0a74174168cc40550031da1a7407b00a401841121, 0x41a2dc7a646d8020000288a30450ae0ac9501aca8c48e24440af009801823b8888)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x5400000000000200000000000000000001120000000062900000000894, 0x2bf000000009300000000000000000000629000000001120000000034b),
 (0x2f0038c2ec074470a41b03c101166166101007206a5890050661f11203e0a10515, 0x90b04728026003001ac0b038e828948961a2f04815a329a878940a847c000e22c2),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x314081a310789781129927a8248008020a5bf00c0792b8608002e6361e4561a21, 0x604b06e148d81205e054400044948d48d818409e27040051d48c019c020908045c),
 (0x92865c81814b50c2400f78770e802f02e8002a0220c0774e802f0cdb44e07f0169, 0x2109225454002004ab508580c01f10f105d4408c1a2180800f10d104100e80f200),
 (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x50000000000240000000000000000000025500000000c8200000000608, 0x84b00000000d920000000000000000000c8200000000255000000000c4),
 (0x2f003ea2104744701036b7c1011094094010074d1c4490050094823203e0b98900, 0x90b04009a5300300a7880038e8206906b1a2f0b2019129a8706924847c0042441e),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x410b030e040803a42f29a45a681c13c102e6201ce88d5a290c1201088149020340, 0x121470c16833ec130016512005c100102d08920304502440810046303c90ccf496),
 (0x4100256740ca08c60c39c181380bcdbcf104908b2844c4281bcca1809087c8200e, 0x1ab8408038206318d140046080e022020e680350448230c1a02200624600259971),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb2100000000807000000000000000000014c00000000c2200000000187, 0x442000000002880000000000000000000c220000000014c00000000c00),
 (0x2f0030d312474470060801c10112142140100730003d9005021480b203e064ba10, 0x90b0440880b0030079340838e825e05e21a2f00bb88229a875e06d047c000a4182),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2b01615837a70c46033240716a90a921455340661101202a91986448600686d4, 0xbac4ac80a10810629078492200016c16ca38281810863655116c0691928ff12929),
 (0x4c6381aa30a418811387c7176a802800c3cc800c05a2422f8022c67202a5604a2, 0x3829c6e048251241e042008a89148d48d0c0279e0724cbcc048c01889211082311),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x82200000000d420000000000000000000ceb0000000010000000000495, 0x2d5000000002a9000000000000000000010000000000ceb00000000260),
 (0x2f0038a83ce744700b0027c101170c70c010070185049005070c001203e008a085, 0x90b0435703100300b4059838e828918931a2f0807a8029a87891a0c47c00f01d20),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x261ab1980000a053847288252802002004246692c8c8242902012d56a0304c2529, 0x214e047dcd14ac6b0571d215dc3cc3c2c2900d1105c244cc3cd081100d3110c2),
 (0xa2f61d02c03001f09649182b45a87d87c0c2e9034c023a41a87c00807b603b488a, 0x480122ad2e4a1e016936e2901a1782783b0c1244a328840e17820968009cc02260),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x6010000000001100000000000000000008020000000040d000000001a8, 0x19600000000220000000000000000000040d0000000080200000000805),
 (0x5822110000087ca4c0000086186100000424822000008610660000012a887, 0x2251a2000001821a30000029429400000bdb7d400000294e9800000690610),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x90c4424a10024c24f2784e0090653253301000479588108165324c582489eb1f82, 0x60984210d6c0290010000304f12cc2cc10a1e906a51210a02cd12a71b32006024),
 (0x805b4304464903143d22054411a7417413e6a80568950110f7419204b011843683, 0x3aa09c7801869c69001d6a192610ac0ae81107ca92481c6200ac20f140ae3b8904),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x28a0000000022b0000000000000000000061000000007820000000087c, 0x5410000000085400000000000000000007820000000006100000000703),
 (0x90b048b6981003004a1da838e82a08a081a2f0403ba129a87a084d847c00084324, 0x2f00374107874470914254c10110d20d001007a54000900500d2b26203e0459c4a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x300db08a0260200640616e0e33d02d02200d4d4a218a1b23d0302710234d01050, 0x8cf504c6584074a00810a80f14c04c04d013010055230a05c04ca184f582004b29),
 (0x893241ed31095c21810641313680e80e004194984981312280f82c1b131008442, 0xe4241ae12c072a09a26d8accc895d15d03138214716688c995d05d0c0c82940284),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x1be00000000127000000000000000000086800000000291000000001c6, 0x44000000000ec800000000000000000002910000000086800000000608),
 (0x2f003928a11744701c3158c101110010201007a81a0b90050100586203e0050104, 0x90b044851660030062c08638e820bb0b91a2f006a4e429a870bb03147c00b2ac58),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4144d01cc0018c1966100c024087c87c303900340808164487d889c110f3b4f82, 0x86912ac319b2500691af31f88a78278201c4e44950b1a99a7826342c800c03004),
 (0xa6074812b001b033c345489202025125014d24087cc0c302125042485300508146, 0x918814c0a9044040c10964168e020021e32835283181478e021a107a4be2f6601),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0x1f5000000000200000000000000000000100000000004ec00000000904, 0xa000000000060c00000000000000000004ec0000000010000000000639),
 (0x2f0032591e874470210d6cc101105a058010070048c59005005a821203e0f01092, 0x90b04c004110030084d21338e82b00b001a2f044973229a87b000d047c00016261),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb9629c78a719c06200072cf62060ad0ac0c208ca8cbea23460ad0b83a9423b8698, 0x12307502436803d18c209cc9742740021460572400c88874254485001842146),
 (0x9c88401b7807018b52210b69689950952549b08286c8286889500b30a108880d74, 0x334a2e486301230a95e1014914481480aa60a55081154910480240c42e7428008),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0x95000000000480000000000000000000a5a0000000008500000000d00, 0xb4800000000c12000000000000000000008500000000a5a00000000058),
 (0x90b04e00600003000db1d538e829639611a2f098810129a8796358447c00b00226, 0x2f0030ac98074470724a08c101149849a01007653ab690050498031203e04300d8),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xc005dae02a002d79a24a65008705d05d028985145085448705d06124c470942301, 0xb7a041e05c450021824021628280f80d462524986180238780f9cd91281008808),
 (0x8ca44c62cc04695081528f1a3204c04c17100004410e0a3704d9c80000e006a06, 0xe1058b091210292a642a470a509d00d0048a1fd490cc1f108d0001054011d01491),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x90b04f25c4000300b4b20538e8220920b1a2f044822929a87209c4e47c0011a120, 0x2f0030d8129744700a48d2c101152452401007036c0090050524110203e026568b),
 (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xa20660899158fd001035aca3040241242840c0089609a3001240d8224041424002, 0x5d598c322200026802000010eb39be9bc21201d120f204ae29bf05ddadb0b51a84),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x95000000000210000000000000000000c820000000025500000000114, 0xb48000000006dc000000000000000000025500000000c82000000000ab),
 (0x2f0032028ba74470130a88c101142042001007b2af0890050420080203e0064100, 0x90b0452154000300c0812738e8225d25f1a2f00110f329a8725d21d47c00d13896),
 (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x68ac8e4e9961444bb978d52431846c46c9808c0480286571846d80d243d035aaa2, 0x74350216010a8a44001225884228328065d325b1991188062822e05880e08414d),
 (0x402c800299805b2400000a98a2600000046b1400094099e620004236086100000f, 0xac823000425d24430039d145011003000b946a000423441140029408239e003d20),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x26200000000c800000000000000000000102000000008c10000000004a, 0x1080000000026100000000000000000008c10000000010200000000401),
 (0x2f0030220997447083072bc101151a518010078102209005051a26a203e02b4642, 0x90b04e95e200030040689038e828258251a2f028354529a8782559147c005091b0),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x7a2e4a134a208017300500c6a30503500088411d1000d2f345020e1c827190c125, 0x581b524055b2c00ce600a3910809c09f5271c8004a52804909dd0a34d8a441608),
 (0x9d8041490201ac122d507ef13a50a51464101204112ab46a5034670ccb088a0c, 0xb4624fb4a25906522d10a00008c4ae4ae801e4c460c2444984ae0090b230716141),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x3090000000087a00000000000000000009220000000028c00000000522, 0xc9400000000080000000000000000000028c000000009220000000084d),
 (0x90b04980310003004a853438e827c87c81a2f0c6018029a877c801647c00443092, 0x2f00343584d744701440c8c101101201001007119e2490050012b61203e0ab070d),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x900085648cc408110c0221249a9bcebcc6c6ea8b1610209acbce42d48a05c82608, 0x7b5208061311208d17c540a602021021029045068e74e642021042b65f22599e0),
 (0x10c0b078928cb4824133e806b2a1e31e08c17b00828843a2e1e2200d4024a1348c, 0x240b024c634a383608034948061061243884c60d020c1d161051228283588141),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x849000000001f600000000000000000001040000000041900000000750, 0x940000000020000000000000000000004190000000010400000000826),
 (0x90b044a05480030024015038e823123101a2f08814e229a8731206947c000609e2, 0x2f00300ca3474470c256a9c1011c08c0a0100766811090050c08112203e059b205),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0x548b21212e04d22984746551593181180860844a6585501d31800a099a93880c5c, 0x8210121690180d147909088200c44044070b719408408600c4405434600c0660a1),
 (0x55ca7960050628280504926083ca80a802651200007060869a8048658700101108, 0x8a210086b04942159a720901681030031c0ac193260604790030340068662b0291),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xd6000000001040000000000000000000c910000000030800000000124, 0x7290000000009a000000000000000000030800000000c9100000000ad0),
 (0x2f00388ae00744704e6406c10116106100100782c90190050610389203e0141645, 0x90b043351ad0030010199938e8210d10f1a2f06502aa29a8710d06247c008200ba),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0x81cca524a870c80fce52780728509f09d1449c800a23432c109e01c00169440213, 0x2c011a12008200c030298380138500502c92431d01109443c5007634e20490e808),
 (0xa05251a48bf14ce52c0019a009c09c380a980134004db009c05f0225c44008c, 0x905aa10e4b340a230013c9440450050086f101d0c1390001501a00a800090cc20),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x94800000000d710000000000000000000f0c00000000023000000000e1, 0x6230000000008e000000000000000000002300000000f0c00000000418),
 (0x2f003c3232874470080800c1011d00d0201007c1086890050d0084c203e0ec8a8f, 0x90b0424d4c30030006248f38e820770751a2f02af58329a8707730147c00127170),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4b0720110156444380404028055202202394c98104106c110203b4318c09020b48, 0x94f00d4aa008289044031002a8812d12c46b3210d06f13ec912c40c02234b1d026),
 (0x5aa9607a4600a08041296a082a41e01e18000800884a586e11e1ca234258a135b7, 0x5020b003898092436009564d5a612610786e3c631202080a61235088da5588040)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1b800000000c1400000000000000000001d50000000080000000000182, 0x2040000000024a0000000000000000000800000000001d500000000625),
 (0x90b040d10900030081cc2a38e82d60d601a2f08c4e2629a87d60a0047c00a43986, 0x2f003e26e2f74470603155c101128a288010070291499005028a128203e050c651),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb6061601e80908246231c65a16a90a90b021840410564e03a90290a6599068f07, 0x40120c82010722249040818040916d16e4ec23182cc29001816cc2d40846f130b8),
 (0x1540610044400401956b7858ac3920920186218018c14cb92920840595f0e5e952, 0xa0338aa8a80fb08220100400418680681e49180fc31e104096815030280918100c),
 (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x204000000003b800000000000000000001040000000041900000000b14, 0xc7100000000440000000000000000000041900000000104000000000c1),
 (0x90b04a2741200300029bb538e8205b0591a2f0c0815029a8705bf2047c0010ce16, 0x2f0031d8a4c74470686048c10112002020100735602d90050200053203e0e01068),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xc294312078c573b28444432d61e18218001a064a74642831b1822012d660881850, 0x1468421786128801791b2490800441442a2131940a01818044414805088b06432c),
 (0x21d7048c12c307235a19478109031c31c460ba02c9889018431cec82006f88c2e6, 0x98289031ac3038040102b87ea258a08a390b041004506ea308a01160c910210018),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xcb500000000b0000000000000000000000d60000000020100000000896, 0xa0000000042a0000000000000000000201000000000d600000000148),
 (0x1925250000054b0410000082a82a0000049944c0000082a8ed0000034ca82, 0x62da0200000020e0a00000111111000002440030000011130200000ca2578),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x80828429400b1269c151185d41898c98fa202a81e0880841898c7588202082e8ad, 0x6e0819d4b96060041e0482a23e101301000c10020e74a22a001200245fdd181252),
 (0xb16225646608000c0c3300f8ae1bcebce10a428b0412e8ba0bcf46c36ac5c80790, 0x204808088b02cb3d140820701e02102148120507a241204a02028288002258020),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4000000000300000000000000000000081600000000100000000004a1, 0x22900000000cde00000000000000000001000000000081600000000008),
 (0x7c85a000000255c090000020120100000539c2d00000201a1700000805ca4, 0x813a1a000000a2174000000800800000088418200000080180000007b8310),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x84e6b65388052796a056a0c242ae0ce0c4830d4566948203ae0dd4f028094245f4, 0x13010084269a586008001025191063063228b2801943601850620a055182218000),
 (0x256707d018122040a3e8c0a2010b00b103b0b01e1094a6440b00042426d650453, 0x9d2087020074d9b2740072f44c660e60e484440c0236a118360e569cb812020a88),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[18+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

end Format10Border
namespace Format10Border

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check0 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 0
        (borderCoords (0,jk)).2.1.val (borderCoords (0,jk)).2.2.val =
        (2 ^ (borderCode 10 (0,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check1 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 1
        (borderCoords (1,jk)).2.1.val (borderCoords (1,jk)).2.2.val =
        (2 ^ (borderCode 10 (1,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check2 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 2
        (borderCoords (2,jk)).2.1.val (borderCoords (2,jk)).2.2.val =
        (2 ^ (borderCode 10 (2,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check3 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 3
        (borderCoords (3,jk)).2.1.val (borderCoords (3,jk)).2.2.val =
        (2 ^ (borderCode 10 (3,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check4 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 4
        (borderCoords (4,jk)).2.1.val (borderCoords (4,jk)).2.2.val =
        (2 ^ (borderCode 10 (4,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check5 :
    ∀ jk : (Fin 2 × BorderAxis 10) ⊕ (Fin 10 × Fin 2),
      imageRow 6 (2+10) (2+10) (6+25) x y z inverse 5
        (borderCoords (5,jk)).2.1.val (borderCoords (5,jk)).2.2.val =
        (2 ^ (borderCode 10 (5,jk)).val, 0) := by
  decide +kernel

private theorem spans : Border 6 10 2 25 6 := by
  apply border x y z inverse
  · decide +kernel
  · decide +kernel
  rintro ⟨i,jk⟩
  fin_cases i
  · exact check0 jk
  · exact check1 jk
  · exact check2 jk
  · exact check3 jk
  · exact check4 jk
  · exact check5 jk

end Format10Border

namespace Format11Border

private def points : Array (Array ℕ) := #[
  #[1, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 2, 2, 1, 1, 2, 1, 2, 0, 2, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 1, 2],
  #[0, 2, 1, 0, 1, 2, 2, 1, 2, 2, 0, 0, 2, 1, 1, 0, 0, 1, 1, 0, 1, 2, 1, 2, 0, 0, 2, 2, 1, 2, 2, 1],
  #[1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2, 0, 2, 1, 1, 1, 0, 2, 2, 2, 1, 0, 0, 2, 1, 0, 0],
  #[2, 2, 1, 0, 0, 0, 2, 2, 0, 1, 1, 1, 1, 0, 2, 1, 2, 2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 1, 1, 0, 1],
  #[1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 1, 2, 1, 1, 2, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 1],
  #[0, 1, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 1, 0, 2, 0, 0, 2, 2, 2, 2, 1, 0, 2],
  #[2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 1, 2, 2, 2, 0, 0, 2, 2, 1, 0, 0, 0, 1, 1, 2, 2, 2, 0, 1, 0, 2, 1],
  #[0, 2, 2, 1, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 2, 1, 1, 1, 0, 0, 2, 0, 2, 0, 2, 2, 2, 1, 1, 2, 0],
  #[1, 2, 2, 0, 2, 0, 0, 0, 2, 1, 1, 0, 2, 2, 2, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2],
  #[1, 1, 1, 1, 1, 2, 0, 0, 2, 0, 1, 1, 1, 1, 0, 1, 0, 1, 2, 0, 0, 2, 2, 0, 2, 2, 1, 0, 0, 0, 1, 1],
  #[2, 0, 2, 2, 1, 2, 0, 0, 0, 2, 0, 0, 2, 2, 2, 0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 2, 1, 2, 1, 0, 1, 1],
  #[2, 0, 1, 1, 1, 2, 0, 0, 2, 2, 1, 2, 0, 1, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1, 1, 1, 0],
  #[2, 1, 1, 2, 1, 1, 0, 0, 2, 0, 0, 1, 2, 0, 2, 1, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 2],
  #[2, 2, 2, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 1, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0],
  #[2, 2, 1, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 0, 0, 1, 2, 1, 2, 0, 0, 2, 1, 1, 1, 1, 0, 1, 0, 0, 2, 2],
  #[2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2],
  #[2, 0, 1, 2, 2, 1, 0, 0, 1, 2, 1, 2, 2, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 2, 0, 2, 0, 2, 1, 1, 1, 2],
  #[0, 2, 2, 0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 0, 0, 0, 2, 2, 0, 0, 1, 1, 2, 2, 2, 2],
  #[1, 1, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 2, 2, 0, 0, 2, 0, 0, 0, 1, 2, 1, 1, 2, 1, 1, 0, 0, 2],
  #[1, 0, 0, 2, 1, 2, 0, 0, 1, 2, 0, 1, 2, 1, 0, 2, 2, 2, 0, 0, 0, 2, 1, 0, 2, 2, 1, 2, 2, 1, 1, 0],
  #[1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 2, 2, 1],
  #[0, 0, 2, 2, 1, 2, 0, 0, 2, 0, 2, 0, 2, 2, 1, 1, 2, 2, 2, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2],
  #[1, 1, 0, 2, 0, 1, 0, 0, 0, 1, 1, 1, 2, 1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 2],
  #[2, 2, 2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 1, 2, 0, 2, 1, 1, 1, 1],
  #[2, 1, 2, 1, 2, 2, 0, 0, 0, 0, 1, 2, 2, 2, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 2, 1, 2, 0, 1, 2, 2, 0],
  #[1, 0, 0, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 1, 2, 0, 0, 1],
  #[2, 2, 1, 2, 1, 2, 0, 0, 2, 2, 0, 2, 1, 2, 2, 1, 2, 2, 2, 0, 0, 0, 2, 0, 2, 2, 2, 0, 1, 0, 1, 0],
  #[1, 2, 1, 2, 2, 1, 0, 0, 1, 1, 2, 2, 0, 0, 2, 2, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 0, 0],
  #[0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 0, 2, 2, 1, 0, 0, 1, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0],
  #[1, 2, 1, 2, 1, 2, 0, 0, 1, 0, 1, 0, 2, 2, 2, 1, 1, 1, 0, 0, 0, 0, 2, 1, 2, 1, 1, 1, 0, 2, 1, 1],
  #[1, 0, 2, 2, 0, 1, 0, 0, 2, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 2, 2, 0, 1, 2],
  #[2, 0, 0, 2, 2, 1, 0, 0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 2, 1, 2, 1, 1],
  #[1, 0, 2, 1, 1, 0, 0, 0, 1, 2, 0, 0, 2, 1, 0, 1, 2, 1, 0, 0, 0, 1, 0, 1, 1, 2, 2, 1, 1, 0, 1, 1],
  #[0, 1, 2, 2, 1, 0, 0, 0, 0, 1, 2, 2, 2, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 1, 1, 1, 1]]

private def inverses : Array (Array Packed) := #[
  #[
 (0xc53e2585203906611c0d4b11064b52ba17125a7097084904402d05000040129488888110, 0x10419800d1c2d90a2032304009a4080508c585866020a29307c0d8929138086b13052a69),
 (0x6500096006044ebdb69c2801d01422940b34b40211800c20c980c042a1ec132812c11484, 0x122a3416a0f810400163557a23eb1c40e0c30155062b504e066a2e3c0210cc17e01eeb68),
 (0x261bf36008f3c4701c9025caca41c15a1064500100b82723bd8ad2a0fe4e0681135aea11, 0xc844008e06080080e20f503510321201818aa4be3c40d898421001090021e10ccc251186),
 (0xae9d64804500455d402fb2aa0ca84565ca306f048111dc8340812a7090400c90b123604d, 0x41028306982210223b1008046004381a350410c808ce2060913c91082d1983470ad487b0),
 (0x56000622602a022a02003290a8804c0147317814815000083c64c0f914836b01601b6a20, 0x29ced0010e453945c4778c215061a24eb88e0080748bcfa1011b3106030884500e448518),
 (0x81b267b9113430194895150e054508460400440145cc02110e060424e04d0071d13d556, 0xb0c4d0840a2480220912aaaa00ab005a863e332223a00c964c0d880811fa0fa062a82a01),
 (0x81e0201987a1b908604220008b414a108e20e60a05dca0069b431202a01f38658400d010, 0x741f05a4201204639dbc5a8c60a63002110e1061420158404484c9840b80470033f5010d),
 (0x46015e4db208200820002851ba37ea0a9c4091480a2c00813110010001a440f01804c8a3, 0xa12aa1b24d77163006fc070600c01585012c2eb680429634cca030631e0a2a042338115c),
 (0xd207465384422936a0c28731eb0693146592106c6a8c2ab0fa88c97d9e60e00498639010, 0xcb8110049ad0248161d284010c96ca91225cd110460c14b0450340040910bc1021829c3),
 (0x8a3680213c94c0b2982d021c06800a4ca8803d0e0760e593224a080d3014d29ee6cc4261, 0x11415b5082610804435078e1102d35a11005828118011200cd1053604b80056108311108),
 (0x9a2649858100c20588a0155b014c601b2136800e0a500bb2e82800015e01726600a3002, 0x8448196704ca03de2644c4aa480221e609e886391702e940513d39944008680885b004b5),
 (0x3834469900a0b0081262e09af11120910452a8d38f506095622a80700c3cdc01531820a4, 0x4c021441c4f0b304c8d0e010ecc4c2e01004300208b87629dd0568bb3c202d00c81dd41),
 (0x4b0ac57a3098824460082ab100d29890e04b5a2953b8cb831201e02008680b069100c2c0, 0x30541284c8677c310710c00aa829432c15b480c08c04344049860e4ed38640e0285e111e),
 (0x14a2ecae28282600251843ac0090219a431400e65105a80c040048c800a4484301004a09, 0x694d00518785c18ad2a79c00976b1e4130001a08882a0580f08f1233b65b848412d2a150),
 (0x10528a24c00585e54d1088a628c7a052bdec8eb00313e0a4201502304960024720222056, 0x40ac249302403a08b0ab5118c5001ea80001610dd4041b0bc44a500bb00e05888d5d0180),
 (0xd054afb3850004e178a000031204000e98989312dda030861100081c08a50002d9440007, 0xc8000440acc8b128516e8e00421e7a04525242d224f8201a498a4e2a250081524abeab0),
 (0x407bad111101a25010010456119ce0ae000ae0286ca412f855d28450529b186dea984ec8, 0x378002ce8622502248d8f821c821195180b5184093422c048a251aa22460051000213006),
 (0,0),  (0xd5822862038144b01086300920ab408d57a016310b03694cc6100645444a0148404e3082, 0x83c9088d87ca90bc65984c01d003a50804d080e908010a33949f1321214502786b00655),
 (0xc16605452435f240b2222832104808c08e31068130010d10000c8d0200705480c3e91140, 0x10899aa0184208110181d1098816e72d614021108004702b5ab37060e00eab2514026806),
 (0x2c2326a01840de75098191090001a32d0140800a3804102a00c55460800f0af264020805, 0xd20019452437008a06222830360e54c08e335ce0c4012d107a3281024070040d83e91140),
 (0xa8ac04008b054921214120131e7c1ca144c584a019b3580005202148031f12810e802a9, 0xb5601c9b250f20288ca8e49a0a081e01c080a424ce40427923281da827020414c105f112),
 (0xb834961390480d901f035dc40806015a9f058a0012a389002b27de8102d6c01b30681, 0x780430b018825879206a0fc0011e64006216028348a45505673c00820141c0915a40f824),
 (0x181a5622148a31020412888c08758e280a408191750924802830b283267cd00121448a, 0x92a6c1018843144e6d6a8d37701082105415a9266c8ae44137d7c30428d8800b86829165),
 (0x24a1eb8c547103115000223934210764110950af13f7e5f4a94da980f82031609554be10, 0x8b421050020e5484a6408400c952988060562150080812004292066303d2c802022801cb),
 (0x38100582b886b006924213218fd120609a2008c426682701466396ea452e9c011098e486, 0x4489da454118072828a4288a2022049b25838629910358de108c00018851602c09471259),
 (0x13b0587284011c09484100a388108804d4a018a930ca41a0424e2281908f356860cc7, 0xa82084803802adae2b0b20cd200456803cb084000568535ac0da5b104400d60481100008),
 (0xd0ed0c011a0a92b491472f508a95c6000a00810821642590d90509d184c05245f48941b2, 0x112134280f529426020d029252200a8109e5eb78a93da6d20f25600511d24280824aa05),
 (0x4e1b1842104ad304390415700090203a83210f4249809106828d3da3574a600c92a44018, 0x80642525a29400c8c2bb2a856b6c5c4474d4a0b430790c606550c244289507636c030223),
 (0xc86b7108129591888c10d0c0a7402146520010168ea01b592470321088180b4c1560080e, 0x32000a4169600e2160c70136580356b884e048c1110604041101802845225480a28174d1),
 (0x1d15182a08354020600481a0350ad471012204d2302b508040c000494c96880100865c2, 0x44202431527429854172312054a202b8424d11b2cc050a814851fbc1602417618d069815),
 (0, 0)],
  #[
 (0x61412712251fa861c43b8392f16e023d8709149014139004d29449c10b480e8e4820e845, 0x9a2ac0c90ae0050e0bc4500c0c8044c20860814d4ae045380928b63e3003c061360b009a),
 (0xea46860c01469124a5c1300c7cbc00000915096a85882c75921cc20424f5bdb0c6273178, 0x1802001d81842c1423ecd8101000715f66a10915a72000024e038415a0a004f00d00683),
 (0x8084384a48640c0488008dfc48850599423542597afe04ff3b594800f9046b880a81006a, 0x2532c4950201507147cb5003975a20042c4085260100190004a092a0026b1026100cf691),
 (0xab00d6506078d40c2098152044468822155126c6298c0b82094000c172898b1124d04209, 0x829851d830b83c045e0c01b9021c0ca22012090013024063d1e0480562484832fa5b6),
 (0x80320022020d140860e4211d0e0924bb508122072cf1060420481b10738d41051b809293, 0x2489b10558e0e381821a8000709698400d1e1c08d20a39f05920842684520c6864022440),
 (0x13081082c940c6102528a0903600332a0678560a0c8852090fd1fc04033b7151802a9308, 0xe4e4a94126b838434890582048a6445110030975237728a6000400610c0408aa7b5124a6),
 (0x8128c7c06420c0143809603219b54c0404b8a484201b228902284cc102d326386dc00a63, 0x14d130071101360a47c28981c44aa1c2ea015b614704491419978316852cc8460008c48c),
 (0x13210220ce3d806a07d10d28204066120e2c604940a4083a0000e201245bc240913801a0, 0xcc84314400427f81d82a60d4de3e09a421039f36831a80c58d2d1850532410b108059a52),
 (0x951050202410a487280c81b115b9d66137bd9808232940c1a106346d0d1089042828f8b, 0xa6ac72e0a824d0258901374024200281ec8026317c04223241a804910828e50b11051060),
 (0x1169d29802b12910000293772cf101ca25c83100d2b91508412d01009da8a0f533440811, 0x4e9205665140c28e37f8248843068200423586a7250628a53ad2442520115c0040aae6ce),
 (0x25001435030150ae82819780c00ae206c5296808721442b80800053146320304df03100b, 0x6b490acc1c00412426203a13440008089004d00c89a801457600881040e08a009c81f0),
 (0x10a3cc050a9c0d2a21092cf804d6acc7456a206a82100580120700813d27b525a88a91a, 0xa440411b8e12162c454d6c0048200403810001a9525a5486705582e7842980ac81424024),
 (0xc7030ec1800610752a0801596e400fe81888303c02052188a00871416049521700843015, 0x2cd00e7bd94c0294625226911b20032423054281805a664f0182288eb22048d148cd82),
 (0x206424c41123492321204410e42a81061a4208c646e3429a113094c0091911d56810e422, 0x9a92930962d43000161dbb2c12051aa1612c773029042145c0812a17d686260a114e0989),
 (0x2290840028b8813d4ec000081020801414600308861780e938010a003767eba13c8800ee, 0x94424b87d4436ec0a12bd781e7960ce3ca910c6708e82410424cb0538818140a81303f11),
 (0x118a260c2284015ec01424eb08cc55cbc8a5282202ad118e20a2eb4a8b06000248182e22, 0xec3119334840f0a024200104d40102343742d5555450c011db0404a4743124f190c491dc),
 (0x840052c8063a70851ba6a0621c05048f412841209699680978a46908081a120a2a1a001b, 0x40f08815c9440322640008804118d9601ac11c8128221484830396e68681ad24d4042e60),
 (0x1de6000026402330ad08012a064590a09943a020602d94913b798810522a8561aa424100, 0xc2097925d9050044504236d041982a0520384b411d12692a048244402dd57a1a508d1a05),
 (0,0),  (0x80995768100029d1e8480d0190468c8990821f5c040399e98740d00806911a84b0142912, 0x4960280160aad420040452ce0a203250005860801008420640902f26b96ca01a4de0c2a0),
 (0x100c0d2c852d70861001cba621cc982c19188dae404311e200409090c986e1c010360400, 0x4e1062c07a128329eec814491e3262d282272251989ce8044e8e436a10590c3d49098230),
 (0x9a8d00860181c5020008a8d54da01184c815600c1e1607f45b960145222a9d98228f86c, 0x565329a4882480009886254222248206911c29bb36140f00ba4092cb2d0c12000c920083),
 (0x104d01d58010991026022c246849100200028201196ad83c008c0fc8d580538654235291, 0x4d200020256846a91099431a9026460d28a420f4a6110481f961c014204828192148a964),
 (0x23aa590c2024a024000906804674c2886f1596d1484041484410c0802008a2480010010d, 0x88552013c3420549b4262936998a00228008280cb6b6b03330032357887158053fa086c2),
 (0x94064c10500a71208086b09ba108081503d5889e829101220acc0ce0031c2638a7a4a520, 0x41a992a986f586dc18180e641437a588e40a22004442f64484204006284180c008121284),
 (0x4c389c3b0c8d344aa8644004d394c5c2b1384059a4800009346b8700d922e002226e89c5, 0xb20360048320c130400890e8280a2a0d0a4323865b4cc2a0099458d3020c149809905220),
 (0x4473927c60ad1170034c20a07686d1a68281150a800bf2605508207084a1801603432a12, 0x3008488313000c08e8228f1088282c18302ca2016bd009038a148b8a21424aa1e0284441),
 (0xc5f018b034c321631074277c5202090632556c39d244991a8068255720062e5ad5590c30, 0x3a0027478a28d284cf00c88121682468c0a213c60db060a54b050020c4b050212aa4434a),
 (0x1d9638451812b2026b4988924e42180410d34334120033408c6914830d958185068d4006, 0x8221c79a23494ded84326700b18862688228b0896547cc1750106068d2604e78a0721561),
 (0x1a85500121eb1b00ce231410300434570204630243a9040632194e282042b44209a60221, 0xe4680d34060460e730cc6bea4b694a28589a9880981258e04d4030d3098d4b1984087454),
 (0x4dc3a20c0103006018012408718044867120095a0470208450d1080a130041030a34820a, 0x92041952a820ca8bc7c85163003f3a6008054225d981c1380a02376588f9b28c45013d90),
 (0, 0)],
  #[
 (0x44024d09caf01038d205c08d001069a4240141d0b80860228000602b0e5444c86b800a82, 0x2b2c32b63002a6c520901152aa0b8203c346ba0444811ac0273e930431809910141fe058),
 (0x914e3c3006022823222040282a0e8e0c820c032069082012040d0ca08803a840a128264, 0x24681838a59b8915c9ccaae4781a100d121b2b89012b542850360704a0084159d4e4488b),
 (0x252c250827028e704301e4ac033980009211a1800f6d1e9c1800003a00c014810cf0a204, 0x5a0248461065218f90a21252d440531f004a585a50928101e713b900d917034a61044d69),
 (0x826144464188028000c9965c20d83a0e7962504220a432202136af5d2a44d1e4315c5412, 0x6012ba308420c02b30220803c223c581021881844142441100081022d4910210c4220888),
 (0xa85a648f5104511034c8113c20c70120440a8a0e248dae282210b6a20830200be3ce5600, 0x412401608c6104ecc117aa02c00812561a0534408200008500cd405894c01c34101089ce),
 (0x622848021340b0b1100de540089dd605781539140020488963900758c12ec62c0261040, 0xc81d433d484940f0243821832f20221b8006040e06f019030946a30251e903082fc1422e),
 (0x48c439388098100684f0081ce6b20804318790340050889cd124280b109ac10204943980, 0x801804875702ced81a0ce541000d66e342386d8bb0006423221907900e6024b09b230224),
 (0x292248c45145c10233097651800460dec410a80a07a09098042eae8206ab8286a28538db, 0x409d162b022a140c846008220a491f2111eb51f5d84d252281005060f150747100588120),
 (0x3225583889c43092b00196a1cb6b445c01818185480647a49420a2808096f36044111400, 0xcd420787061bc44943ca401c0484a201c81218301288904942cf047b1c08041719aaea34),
 (0x4028838b3d2388d2830f204c2813c075109a2a10b3081551a2a8b442088192a00d0a9038, 0x98836044401845207400dbb192ac1e00462085cd448268a61556430c870a281322b40cc7),
 (0xa0a2c53c889990184929f00457241a7064c4182a0954452301805a300a2718044715065, 0x441153a0116660820a6840df8a0c9648e130b00c1c6a21a00206d05470180832208caf82),
 (0xa964293484104624507ebaa11b220eb286bcc9868804bb5274804419060a171d00042ca5, 0x40800002316e988aaa80000e0480c0402042364020d300ad88190b44a9f12840cd0a115a),
 (0x111700199eed830901310970b080f2a854061020b3021b4c8029908910713050c0051d00, 0xac00d6a420023c54f448c4020f5a005023218f040405a4320d524466898c80850178208d),
 (0x1c0ce8453800884042d468c1ac83c9500ad56044d140002b3055383cca9ca2a3eb106251, 0x21d21328414e24bf3122000c0250260e6528830b0aa6d114432201c10543501000af050e),
 (0x9b48cdc254cc8d11da80b68313814046c0439700898c6182d021b901e40b4b250cd2b308, 0x443632250821704e00314100a416b0203c14401900531241240406881a74a490b10148f4),
 (0x624403cb240381f218951e436c68a1f0ac3480e4acc15523420056180a40209449101484, 0x95a8a80008d458044668c0bc009118035108130a412602482850a085f439536210454000),
 (0xb91f5653c1920112c02500201845555584400d808049a22824d4584882c41390427cb1e4, 0x4000a028294a691b88130040a28aa25b1960194a245882da2183172031a86618000211),
 (0x949644d285209d4080a01a0c48acccd60840209255a3c0001d412f105319ba5d30004814, 0x109b00d3a47228a595aa52201510121653ed0490a44296ec28ec0c42c2605a0c15b0103),
 (0,0),  (0x6af0fe80420992f687b9441d008865d50448164514006155ae0532760a8d121080140e0, 0x215000104bd222400200600c2dd630a00eba5098a824d10a800d88508d5700168336bd19),
 (0x2f8b09040554399855203428080c860c0053386b8480220e2e08ba6c4b1500c03a9aa331, 0xc024420bf229c4042a8d48c5b732091012284214724ad9411025448284e0743185255c0c),
 (0x9350b16990d606e910deec1d8a8a941005a602282894016407049ced237a84b4a8d48004, 0x642d46864d0861126421036235756a8c38005485c34a581b90126200c000490917082f63),
 (0x8c06b0546ca18408856c404d8a82c9149680760a2a20220521102a02040c5830114d10, 0x9d51014428821802131a033c101131120008768054d054c9128c485458ab61058e2232cf),
 (0x11c120fb504133d1004080051300167972817220a26851204c20590d14279f4259189630, 0x81c0e008f3c000cc0a1660a808ea1028460040d5106864b234d00524058208080216041),
 (0x58201885b000a0a0f60a60e040280b04790362308ae00422982802511958180000084908, 0xa15ae738007f1a4708d594101b550068029895c4411aba1044506982c02143960a761092),
 (0x601cddc278b4e0c814b074a8d70100284a24868c407118cf001a88b8a00a0406e0158181, 0x98e30231064b0e30804a09532828e79485c849601e02c010096017024a94e0180aa03226),
 (0x803182a64d1024e5a24098c819098180481549ba5c000291f5261c487000042640004869, 0x66047c09228f591819a90121c2520e0db202a64580ac8d6200d0a1b28bca129102c22202),
 (0x2505961f810e447c0205c4103c0c3182c80aea0a8782d600c112042520fa0340c1044048, 0x984a69c00040b203892203a24063c66123801524205508152c40c348d204b01c0a7b34a5),
 (0xb504ea008a1016588000ac72812e28c08808c022bd4e5814445c8551d2210491d1400a10, 0x25810dd714ac9a32d69520c0840103c35f615180021a420aa816a0a2c1eb94c2a355041),
 (0,0),  (0x1716213880400200b3549a064af0214e009aa01d22900a08cc33a246c4a8600e08ce50cb, 0xe8a94a832f9bd0534022046195021411fa2051c05c2b80a22048013118021500d411a624),
 (0x1a20f005038491c42a6d4c28bc60b00372682615888c2a4178e0030ac7c140518108212e, 0x850409fad80a48394410b2c5421d429c8581414032609412840c3004003abdac00844ad0)],
  #[
 (0x312a234c61240a2840121017406d038ea84a68482260d0d952cb0c49c400908103123038, 0x4614d4b10251a1d58c2ca4a81c10dc31432107b718962104ad2411a633d300122c4d0745),
 (0xecd02021a503810729eca4c40700671e84014460786234e03261e051e806c42004c04ae3, 0x1108d5ce1ab446080601422b10ea98e03be6b30e0294c20189881f2800d92805913c0410),
 (0x4060201200048a419048100620804b529500a424148020091600e0f48454000414e31f43, 0x9396255bb121066c944b901f751008683859c1820fc0f68101080950a0d04241148030),
 (0xc710780014cfb10080484001a40540102b3020810150853202c34e670381121084283170, 0x20a7837e820002d84f801af2522a968e80434c240689688c181ca1000c0664ea6186c684),
 (0x4003120062540b41b29940118096a01520ad52114864133100004a026388820520444247, 0xb74c8cb78421e09a090629ee2a4117629a10ac62221be402f0b481cc8821545a8b39a198),
 (0x84c48426500ac508841d0420295a210c9a94215904069905201114c0242bd96850692a49, 0x1a1173410e900a6502223a431404803140288c04b1b8006adcacc13d9014228282008014),
 (0x610440406d0ac47120498c403f04a8c268d30003a4078a000013c1e3c0123080883d00b0, 0x860aa8b990100002980272ad00a9000d02200eac115010d6a884141c130c0c1a64004d41),
 (0x502128288807076951021e3447290b3f45f175caf10236332ed4d2044072688885c75681, 0x8b40508554d09006283d60c0209284401a0c82210aac0848912924b8970883160a28894c),
 (0x52a132948b1002a010c248821562815c9f820832814c2441082f68180d00049505628533, 0xa944412270228819ad1c2030ea0948822034704d1e22c0a0544011206044220a4a9420c4),
 (0xc13784e053c060400312f620055010141220245112706f438d010671400c81583949a0, 0x210e801307841b92885c6c0893aa24e1e165921306c102903c22381884a9531887400217),
 (0x4bb99c616a418c03020d2d5816d1bc660402125241247c1a90a1ce750288220980a10e62, 0x4440194159201b85d52c0a4e90a0118b3ad2c09909902802c52018a9c4418d07e44b191),
 (0x18a2541031000809513680541ca49201121d047538205986448324004384c2548792434a, 0x45118b0242c8c0e482c1288b02500962a460530a4504a011932018c7a86210ab584420b0),
 (0x5208548b043a9041823817b0c33808058ab66233a15200033ceb21a8ca892b040b831d2a, 0x88d62a442144441e79c2600024c576ca74001004020c96dcc11080453566c4fa8038e055),
 (0x1cb808c28a9c22932016f2a424200c22a986703a7b94b846081010e515b114608f446b05, 0xe144132c75409100c0480c10938550dc56408a8500014229c4c7e400c246689a60000452),
 (0x121a2440145040681c20000394302ca14000928520cd6dcf84704453566824c0038e057, 0x348e588b643891b0523817b14280ec058ab784968952000005b8f1a88a884903df831d28),
 (0x488892582a00617b7104400213c481a24069711d110c78a01a7fa16f088320c07800da82, 0xb7256507950c800486411348a00b78183a000c602221865640804210817c5c0881a10034),
 (0x4f80844ccb482a449228d68290d246302560050aa0c89143e060842006005cec8523b049, 0x10376a822011d4084dd0216823013089580ec04115126c1c0586228eb13103013a0c4090),
 (0,0),  (0x359084d8d828149315001b4040f43c09d40280a06804d032e180dfc42534680ab0a440, 0xbbc02620022016e200e8a8e4b5ab0bc1e40ab044170619254c0631200a8082030440023e),
 (0xe1099580a83c0801a202023e2128610784023440263a2084921a04c711104e43003c8023, 0x806287f0102b67c49c451404c508600724403048144dc436925830004e02018a942578c),
 (0xa0d1bc8c1002d4890c04bb8d0505208813784407200e5d5800690748001085761c8ccb2c, 0x4a040150ee442b72713100304080d071a48422e0070000814390b0a78f0c4a8821611491),
 (0x4410454848d195034943247684231011f006ea14a8a13a222a0200673184472812a807, 0xadb823b0351208683cb02cda88430443ce0f41102004580481053da010cc42b817ed5410),
 (0xd882934160d28030e24aa40372829305280409e98c041131045e9254e042328e5c380040, 0x22554088030166000da5028c884c00dac6506006315204ca7121412b1bbc853121411d32),
 (0x2094105a308442144801246501c8a004483882419868ac80f001410614074ec42448b942, 0x1f61ad00411a012030c80b10621445c995c2692a2097531004aeb421a2d01128519600a0),
 (0x4823010812353358a9c16202642c481011511eac0287c14201104895031817de02a65409, 0x3644dcd54d0804a7120015341b1211aa4c2ac1133c481eb9a069940280a7602069002192),
 (0x140a4b0044819c242028411539040025c064a204b46d24f432f37002c0200034d4e0912, 0x8497104c2084601d09011126ac0fa2b180e0845b24b925a02cc0800052bca39c10016288),
 (0x1c428610524d04a21504824ab6d814105060084188b13f080418297e654606110420a08c, 0x38168caa8103259087a55a10026e2c4aa9f573c104a00d472c01601983889c6299a4f13),
 (0x180d0f3a0a082064165a17e9a1610355d456320061dc202088250541822c10a105007054, 0x25c2e040f5b59303c80040105208340a2900ccd11e01180b0048609c18426e16f06f0d83),
 (0xe0044126c50232006c11a0445c82005983105000589236e29444a22bc82d004150310643, 0x510b0c02064c01912a04e2b224d972018ee03d02448881940990d8421c26d8e8a8e29a8),
 (0x702840cd08a001a12f56854853c8ea02245541840c22a22c505416102ac103e22246798b, 0xb141d20320dee18c0a05216841200098822226a6381549282a2c028011c981818300600),
 (0x2c225648451438fc870cd2939a270f80e5b11085a84a055950122ce0040920040d340a9a, 0xd1d52807a203400268110c044418602e0002a64814b4f2842241810843f6461390cbb560),
 (0, 0)],
  #[
 (0x9c2083b113767c40878380ae2000d844030840905414e35c35735588cc201fc209c9c08d, 0x60ca6c4c8080812d18500c4093052402a0f6b540218210814080022200dd600920200c10),
 (0x33c186280b088b8d48e02c1c484424338551844080128482094809602608ab242504cb14, 0xc412701280f77412240581e0a0a9818858a8718271a9523c1486268498f444825a403000),
 (0x6d8093df80a08c12005e0400063482109455991200081a3f38880e72ad4100b94c076051, 0x3f08201d5742a092218913598140696ba02060a47305c0836161895004a90083c89906),
 (0xb081c7b11374cd106383c0ad69bde04463098000c414835dc94505888c21828d21c9a08d, 0x81a084cc082300f88500c428200140280f4283d3182308000a8d22240dc6972c8200c10),
 (0xa82bd3a85844418411319320530c8580416cb980057446430106c0134680100c64d635a1, 0x14900856061212618e000002ac026a30229200375880881402181928b92280018029c802),
 (0x21c08c440229089529c2830000692a29104204244145dd03fc1409002530431af104b44, 0xb501c63a31802846ac01c50cea784d150c5a4e051ae28226c014322f4c08198800452022),
 (0x11c121438ef833d100a6071c1300157051487220a06263074c205a6190109f425a460665, 0x81c0cbc4003000cc101b0e0808ea20c04b7040d531c0c80234d019a6687208081281108),
 (0x51d200fd811065e002d029a059aa1b0a908c0b40d01472015a06c4c7005d9118069901b0, 0x862c0c0044e4020e5121804d825000410753b4802fea80ee04f03230a1a068661046c84d),
 (0x119000480021f980ca82400d0102696258b4929641340f161ed60c51049286e02110e68e, 0xc804ab26bd16005135542b3296201404234a2d681a81f0480028d18e996d210244ca1051),
 (0x568c044800200c111282200c3075416238b5919015340f1773148451649280403910a68c, 0x8433326dd15e268e5540b304002b804434a200aea8190480860698e996c408680ca5053),
 (0xa850177e820224df03805af31501468e804030007689288fbcaa61006c06e0713586a684, 0x1a4480054cdca0058482000c246b0102b3101800950c53043510a670380060888281172),
 (0x3249e8d0070964c040d04c8228818b1d19512409450012303a00055dc0d8142250c21958, 0xc1961608f0d20903b922310041265020808c9a76aa57210200f712202a0182898825a603),
 (0xeaea168881053d91b118340074148901b222850c4e01960006406c1aa95a8968904c8e2a, 0x15116126641842644262437201ab50b2499c28f1a18e08bc2887104544850094090111d4),
 (0xf53e4009b89fa05a0505c1a038d3046321128456838cac80c1027a5b0982012c22222800, 0x88f20160480462a222118520d910c6ec3108240311183c788480965044d0d89c9462),
 (0x27567e32184255ebac14425f033c81a3043807906134482a740ce041429843c3b8439d42, 0x4828004921b1081000a9bda08cc044142b03680a0c83154508f31b10a061b03c07386085),
 (0x9100f2c0acc0e60215c64441274738a101a4304abe4d64c309090aa43a20904038207853, 0x28a70d3e532211e5483822be9890c248481106b441a2101804b04449c0cd2b2704518620),
 (0xacc840c92ae200fa37c4300ebe0c14c26860d83546e0253825064e3e30000081aa0b0098, 0x10172b12451da301403b83914161a23d870800c290139006d2b0a1c14b487d5010208844),
 (0x2c10602301896081c801829d10429c011a4980043039328c40c90280d041103e9fa81acc, 0x8e139c6440834614704800e73060768410018289064c401a12055502aecb4100444032),
 (0,0),  (0x7072437e8202e10543801af0098c868e804300721e89088f191019000c04122e4986e684, 0x809100014cd14aa00486002e66248100b30f401a150a53060e7e6676382254084281170),
 (0x150701011ffb21004f05b0433c18c9230486540e0471004101200204cd20fd00c8a02420, 0x888b2f800000eb6b0720900c2e432486300a1b03a886328829e74fb221a0224061c9b58),
 (0x280480454a15801033c518a99d415488942b089d1611072314c3800215021dbc005608a8, 0xd76b648285c04640802805000082013142c01420410010c4a10835b968b8a24256a1a510),
 (0xc4d9810e54941ba8043a2118e2c08204882034150c9e1877c201910419890210b064a00, 0xb012670a0ab29e4066340dea2191d44bb060909c8e221220815ec485a6666d40e009818e),
 (0x4504b1249940a0853d9004008b940ab3d454ac2e460919640c453788874080a329a5904, 0x7204b441340a35120426d73324008904c0129418139522018c00ac80268010b48505a0b2),
 (0x613601446d3424d681781a4216200409a9e2a0125a4d72606787ec0a4091211434503801, 0x94413c1a108353285e84e498c05b4b9604000b2404b00d8b880802659c0cc4ab81ab02d6),
 (0x42c1800030424ce810124771289e89a804004869c4c0c80b23044cc02014056d8044c4d, 0xa883042b0c7b1a31005c0a0889521560658f231141b22315444081232446958120e08230),
 (0xc015270523a89ceafb4187020653832e990742101dd322000e2b864a808a069ba2518be0, 0x38858e04c06021500962878c1a850d066f03549402c58dd718051a56311c840100c4409),
 (0x4974002cc3c08981808144660200c4c300202012854d06249492529b68801a870180c38c, 0x688f7132c04367460348b09e58b0208b64f1ba82010c0510b05244080152408f6710c71),
 (0x9c51a60c0188e286202844780b2210e9a5e2a0ab0b009501d24c4aaa828c980222642e51, 0x220c5880080711384e05a98754980c0418181710100f2a5a0c83914465514355c00040a4),
 (0x24820929018dbc202050ceddb28494f60015854078bcea5845a3000d22114a844490441, 0xeca7954c03c02020c4ea3212049026b0138c852aa824104841a4c8980452e8049826fa8e),
 (0x38e21686441689cd604180b64306705440a0912241c48b4525483050c00348c485808914, 0x470168688221541207a46b4184088baa984d2a50aa194010d806c40b025c34327a5d40aa),
 (0, 0)],
  #[
 (0x66404886429c4208020160f145340461c8108489b30025a90444812001d2088441082c20, 0x82730613d4091d74d008f00b240720a32034a340cc20a5262197045f225824b34851106),
 (0x2044083e2c82195a42a2002a0264205cd18137a1d0ca8a0356a9c2180de8c188012b6143, 0xc01ba740d32c400188144e813d8850812612c85c2d041418001215065205026490141c84),
 (0x2424c18885520200c953c788620d20401129450112941a041520602a8c0012bd016113f2, 0x194b16252aa0397a3088187315b2da17e0443208ac40a1fa401c924123826800d6048808),
 (0x50c25ada1f36af218ec0004b88085038740e19f01e830e1043430b41089748bb2278b55c, 0x863d8124a088508e51231d8060b72c8508b16609415cb1ea98889484c24894005d854a80),
 (0x104a086505021023a1b00420044aa484a9871806a2063057d3b65d10226dc2309a20474e, 0x86b436882a110d58480d890009b11800440840391081492800008043dc00098965dc1000),
 (0x2c1d028e20c0010001c2244162a089c704a5ca2a0f022111427648004a10922c41202e9, 0xac2e230514e39666faa25419a1d4d1010235a24855034182c9409b45da5262052305cc04),
 (0x448940110dc110208801900701dbb385a7da2a65f621c880008710468371a800422e106e, 0x8b66a70cd20e258942144318560040220004d518095e332f0b4027395c8656d88c80cf90),
 (0x899610112048883634d019b648802404a225cc42401f4f8bc9a7008c08d5a3940021b128, 0x5661e20294850108830da249241b833b0d9833a4954020543458f0507720044b65da0443),
 (0xdb080884c41c04c0590a000111ad0aea04984d880da0309914142b0000420251254028c2, 0xb3f54b28e1520a84d1698a8e4051148a66023052160f20c1494028873d518e92bb0635),
 (0xc15010f001630510d13000644200806ad0a4c009247004250c2480481a62323b14531e80, 0x1eaca006140c92800a0705883dc72b04011a234281882858f35a3b3161184c04aa88e017),
 (0x646c31622a0120824c4920043a2451508c312c160d8c912d2e50923213a088e414b1f1c8, 0xa81c81194424d141132826a85d3a4a1510e0141521048d200ab6085cc12010881080e34),
 (0x2a094c098b738487ac00040725859004b00b4330d04c7b51a0bf051a5fca2a8652f2e2c6, 0x4536812254040b20518139189a3a4e500e902c4e29b1008243000865a0154541ad0c1908),
 (0xccc0316010620a142c9030a8454d16039e277242530040daa010510c8443105c248420a2, 0x122d449c448dc44b100b4e421822018001d00530889abd25448486610ba449a20a68d54d),
 (0x10440e6a8c003ac2307848ccd283426387bd30283e85ab10400a832d59a01830920e1329, 0xfbae18001c7451d008582120804190048028447003a0041aef404900018e28b0590a044),
 (0xa70a03144390113022c0cb130a91d00586e00d13d2c0ade6ff048cc1c442025224840858, 0x557cea884500474402142c81622ba8700aa220052d5219004b72381834788dda3bc702),
 (0x230064d201059680e2806c5b801c82562ae02a390b868e880aa818431501621e833a006b, 0xd43f00059618207d106911a061c171809412114284196047f04505a022cc812130c1db14),
 (0xada90100c50010056384acb4007984ec84e142220e320214c28250011b0008095542b06, 0x742565ce62a87aeb2044903400a0468030a002d506008e94104292492e02701728a85479),
 (0x57bb0e8a0210007846e859c21806480877202b8024933a223c1310290f401481a6027401, 0xa044f05025ebb48209138204e6b915b388c69461c948050081e06090902f093a198182aa),
 (0,0),  (0x2039269050980d206b70156d9510283b2393b00a886447254e06d110213908261024c494, 0x4ec4d80c2763a048900360824ac68380c82c09e4129b3848312800084c0456c04a403843),
 (0xb82aa08c48000430012a06c270a180516ba4092026661501402888c830a14a18001c262, 0xc47104e1181ec290bdad5180109083f0494037647590848e68d5463030e0eb1819422104),
 (0x13eb0846c52010b420926488336e4ee71e72680225248210001808028d124f0d8df0b890, 0xc814213838972543562d930780918018c1808048c8c34d200f4782b002a580924004412a),
 (0x4f05084c6012d04200862e8218a6482220ba09438c9338888140f1c216f3609199c4d120, 0xb0c2719319a00b91545141554051a0c8d141b60c100044525c1806186004082664332851),
 (0x402285118700654668a2e4811180406ae0a4404805182ae234a0d710f2b655692226041, 0x31b01320a60e802a8904012586a26259409409e9638e19018831308860d48080658001b2),
 (0xc0033209a0901787022cb24141aa2a3b450278494b10868fb36408002008660461230cb8, 0x1f8400421709002884c20db0aa119184aa81823610a160500c83b3348107099188d0d244),
 (0xe4c0624e8afa209b040692349120981220dd0d097c26015400430a5908282c8008749a1d, 0x9150c917101d020aa502182005f40e15a22b01402985a89392cf4a65795815054896402),
 (0x4810608292440844021040b0515090819107000885cb01824000f427882e5c4f50002510, 0xa5c509602c2af6895d819d4e02834e720c8061b27004560037e701183250a210a1e0ca8e),
 (0x3180200d0e836811432861c19358fd00538191c314886054900880a2292c8395118b0a9, 0x2867d9002e11487e630d5063c64a2007384242c200312030324f41548848128422e50c06),
 (0x7ab0b00820c390dca004d2803008589350313048858ee01088208ad8a5c000880242f80c, 0x4406028c1c21031ce22d5c4d53a424884c4d355a700ae7775a55021013b267a4390743),
 (0xc4005d1a728821584021f45268562f60ed7d5a44608066881ce2bcd120178b84ade03403, 0x29a220c48d718a05a05c090580214001120280198e6898726110432a5f00642952068244),
 (0x3408422414b0d108a18462c00220ad018606814481203062611327198416cc9d2dde0284, 0x80018889aa4620e20e620411cc42009028a152131c10490816e008c26a88024290004c59),
 (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xae0c3295862641032078611dc448682222f30033001267297b000a480d81d7589201309f, 0x1e148221099329017051c40132687d99408590465a50094846f3015e07e08a145304c20),
 (0x62cfc9104a854d28fc08012b3180468255c6610584eb80e084c2868c24a380a002364501, 0x1120026bb418b2410392a880482c885520109a8233140e03612501128b50754fb841a2da),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2051a85db644020c0498000c28915014708c10c504318a7810cd7549d12c0a0292aa14a0, 0x9f0a05a009bba900d24605800200858104236d3ab08c10800b200a160853e4906904e953),
 (0x12330462b29a0826785da90e020a081223808098bd5397621004caa00e4c19c50670866, 0x34c84ca800544864984a21020d930a4a1100b5606008c68050dd3014e9022c230580d211),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x380417894c4c121e480511c882a50314237c0229030c444505144100962bbe00010c82, 0xd0c02800502021e900a26826177c12ecaa4c81ac421cc29a189263a84669100195b2634d),
 (0x1400b1a0c0e65266003a52100d223f3463031540826222ed1201410623850de142151110, 0xa98e4a4e3608ac09a74520c4b01d408084b4e0b17c94d400a0128679547a4202314004ac),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x5500338327d5945884101310d929d584139c3006d1459a20ee0423a06dda001007116640, 0x82a98c7c902a09833aa988ae06820a5bcc2188e00822055010985c108225d64ad0e0188b),
 (0x507b610a00c6496ce509de1001199900561061412b40e3075c04eaa0c193164588c11105, 0x29000811dd2800110a14208d266026df21a51e9c10a41408239a114310482122620c4ec2),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xc40705811aa22118164c122200224060ae07418a10984860a00000b888280818b11c7002, 0x31689a6c20454a8249104d8807c8358d1188a4658900b40c4b170b453585c7c208408a0c),
 (0xe16429113861020136014a21930b02100009b01d2c2a40880741920c49a123f08b9a039, 0xe18984064439ab976c96e0414283479c0b00041e0c111a940f00e2122b64a94046425b04),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x80788a30c4200dc11822080109d6518142180c90c142641335200022d49001c540220889, 0x1f064046218b723040c9f65ef0088e0e396323021ca4122082dd0b5d2a443a101d5c7412),
 (0x281200032a2e989e00828216000961fa4002341a889289080012f9850014300a8359c41, 0x2456555dc809165215b7c44287cb08c013fc1c9e4352420756d28061288e28c447c860ae),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x830ba0e806e1824613a224a024605803150a565b945b42350e0262fa42e1939264848f08, 0x1c540503601410112414c9595899a43048e0a0a449a02942e1e11804841668651a7a0047),
 (0x62945444961450434005408c08460ab0053422165805c08b4014a00101384842540ae130, 0xc218a2148e98f2c311ab0439418a144fa404901232031748bca0e7e5642a0a9a1840687),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xca90001180215219c91bc0204889f101c2948d1163c004645098a86128b85986f35e5bc6, 0x216d34aa0e9a05643464135f2276028a346170ea04230b180467120c0002a6090ca02018),
 (0x3012d0822a91704476a00a04e04c101c92a2112620b28ac80440a4592101df60088da1d, 0x380a0230d146c8491001ec0da0f904901001c0651c349301742244186540a001f85201e0),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x900019d2923a3000233be14184701ca01021164006f38400626cc80020a0b688c06ca163, 0x2873a40c2cc40d8918c010803a07015a4858291b5004080a8990241e914c40071f93008c),
 (0x8fd0a5b8418add456298008948158a088d0024100e024204008a8df234a01420bae0560a, 0x700a1805324000101d27e260a06a047262f7c1c5c0d09cfaf2551000094aa39a40172920),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x8700cfde111d19f02d029a02601630ad08e8004c4141203416f64c7005f11c2129921b0, 0x6187300004e40c009121c04f01fe8c4107502d6203ea80ec90801a30c1a0c6018046c84f),
 (0x66092f02622001cc1061d21e083040c504020924c43348410d20b5578c21860b81484f38, 0x40081111996000d1821405607811018ed56d02a8c179cb0054080025868f472379004),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x8c380b001b290204200449470412004da806041221620071806e09181804ba1d1202b041, 0x13c534b6a0c69988c621a080ba2dd69011c169a44a882186778192e524d904c2c9fc451a),
 (0x40a02a500526ba5800104e670104606048481637771464d8b8da006255050405520cf342, 0x1e15d00eba580420a240000074019212330449800028902440202d18a2da81c82c7208b8),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x56204e438dccac885c5c12077cbb894e63831893350e407e414a32491858b3b88504637, 0xd8811913810014241a3816d28830060a00c682704c0e11e0180a1c53406874c4720a9088),
 (0x52404992cc1332a14a05d3d25862060a4d48310a30080093400100009202686db872a1c1, 0xa909060913cc8d0630702c01a790801022b5c6b145d79c48975c46340de913000384003a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x72b830e1e904a273e27845280021ca10aec071d0660204022407a2290f2910c1c553ca06, 0xd04070202a34984140500d6a3d0342d01318a2119b0f1304bb8091420d26f1e3aa42000),
 (0x841c484a081018000840cb08640031916b58e1001126e3fb181830dfac4005038db1528, 0x120812391b2c786a5939e34d3127b4464840200ce40d00000e6e38120423b5ab44246256),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x8848464b2a81a6a385da9004888081223b08d9c3d53977009508aa00e560488c674866, 0x973710a820545e511c4a21006b001e4a1100000030088680c022d414c90208046180b211),
 (0xdd680c90f855021c4124212c4af400109d0140440ab282058ce4e00a4b004538110602ac, 0x2296e34504aa28430ad3c882b501e10520a69428000841d213181b04043d0a02e270ac10),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xace104926302425004284f98140915009010c3153900134265242880d54806d1a6a22841, 0x5216886990a8a5a6088610060ad062e768ec1482c05720818842156b2804100a59555290),
 (0x2dcac60acc3e910c011b1024d040010c9488111d8c40c8942898780a893215411f008607, 0xd02010412201083226e40f91053d2ee248216282333e0622864403d120cce08ce0b21958),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2944e4b3d410b0841153db1d5a02101402958d86cb68018e041679f5388a69320349e494, 0x440a09440281401b68802400853c4b4a2508005904112c70c0880208003402c194220320),
 (0x68846992ac1132750205d3d3feb5020a2d4844092408009108134000920100822472e1c0, 0x1762020953cc0908b8702c000048e41042b5a00409d7bc4ae6a4a2346de8ce38c3840039),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x6320190c8a0281aa20602458032f5c8d051107fc0422828a4862aaa499c10f031d03481c, 0x459026331c15800d71d53853050831018028800cb88500120955158021ac09ca09cb583),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb406102b126659402c13d252210b639b09c498aa3811884a3011800223382d609ad02820, 0x4bf0efc42811060e12ac298d9e94180456126204016a46a107e201694484409720089548),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xc48a2940201b10415440d81010a860104216178720850a32872550660184109861f06a80, 0x283190b89aa069168b14272e8444830c2c20c0404b4a5504005a0109ac6a6800120c1154),
 (0x6410200a2e3c0831d020214341d924930d1f4cb4a042182c460a41c490220224e941d401, 0xbea8aa54083d040065704209022d10880601001593cc691b09110006a95a01202060bf4),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x83cc095da80a700d45b7c442216f48c053fd110d23520205ce5c7061088c20137bc800ac, 0x433940052a10f82800828200c00b61fa400a8b25089089211020b981001dd400035dc43),
 (0x138d842b5264600b7813b25331175f9b49c65022041188490d0000026338f56352d06820, 0x84601bc4281209c406ac098c0a4800041611ad94216a06a20277dd6904850808ac089548),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x15820ec454800a53880c68aa0c59a00510092700670640d011d4613adc9a0c04ad834600, 0xe01d70318368d18067831311f30250f0adc6c82f98803908e22318c40140305200389073),
 (0x84b09c008a98321d1a699817509c8b262f1d88e2c2c08000471612940042245c5080dc14, 0x694642251407c182a18226602a4364085060141d14183d95a881a12bdb3c59a0a6602149),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xbd079ca033107926436981c06018395403501421034758160110c12e50d15f1bc060151d, 0x5841000c4f0459bc060c2c0304c28aa0210b5e5820a068ca6e30808922802009130002),
 (0x82300c0858090c4c4424284220bac994106208c8140a06e3503081905030d0462883a709, 0xcbb1e62430813210c8573dd5041041a109f50320b041082f861c0420042a3914141872),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2482943113907a16007201f248c8203ae6622ca510846f803304c049c1a6672b5301b016, 0xcb4c2886cc0b85e8d985900197144ec511918350640a902cc0800584281118d0000a0841),
 (0x2c2a41c0048098c1b042f54aa01b40248088a702c0e51808405884a3034a8d60191103, 0x7b12c59e19107e653e473002a0026011d0371708652d1285c2aa8439040015621b6644f4),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1c64210ee0326a8436c0080b798930a3103019812134b4540c030943c307b10010150fc, 0xcc08308800f410510c006d4c00432cc54a58ee200568a09014020b6303800068acbaae00),
 (0x70208c46018a091d18c9d65d04c0ce0e1960ba30a0a45220804b335d4a45993b015c1412, 0xf487230e4213422e02228029a3821810218040f4d42241023248c22949206c0d0222889),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1428dadc80d0885300982091b8404a405e42582759105638800cbac0a09a882808b80c4, 0x6421521027f2c46ace6628d4407aa2507a18d26102082a9437eb34435132470815743922),
 (0x3814142299a01d0e0c10b4508081002c043201067701605c60280584a858a0b202342500, 0xc583c29d4403e2f1f104492a2f423591c0450461083e98a20354500844214f0df9839808),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x260040010e44c80240778c20d228064e988c0c18148bafa046184d06030bd0041244e518, 0x59958e22402b039192003292204518012732c1c30150000831c500f9748002aac81b0a20),
 (0x3540082b12650417c013b25241e2139b29c4e01be411c849962d00020339421662d00821, 0xc80083c46810cae022ac498d0005400456100364016a06a001c20d692484bc000c089548),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x5185c3d57819e81c81aa92a423085447d39441606841e86a43d07b03693920b300a9c00, 0x80278102a038611c02e54295a4483a928002ab814853a0595002d801084469808a9463fa),
 (0xcf8a04958f958311a14b064c9824831d00462069880152212c126a02caa85a1485544832, 0x20540068006064645400c0932182346225898b12132c215ad2c595f12003054942a804c5),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x53244c5dd64480a05098000c48d69814108e26001831aa7988820149912d60085aaa14a1, 0x248021a029b85e5ea246058214210181242018e3048c50826628c216485294e12504c950),
 (0x4c8849000c4ec26168060c2ec050d68ac02182028020c06b20def080a923d11419130003, 0x230314a01311009e0369c1c1252421542352003517473814d900052e10d02843c060151c),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x81248a9d316a53910a05782d492002a43c005a22a62ab05b09064958094078004070304, 0xa1e9375220a85082aa1b08110b40c5d53812e044159c501a084e8b2a0b41d012f3c89452),
 (0xc181e000d35a4584b1110228736885004b518a00840128ba1820ce0311207086417301c9, 0x2a281e39240438520084f0c18c113adf24a835d951aec00167c60138801800113a8c7210),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x9a841011a021020dd91be0204889f101c2948c0163c02464018cbc6108b85986f35e5bc6, 0x606920aa0e9a54602064135f2276028a346121ee10230b185463020c2002a6090ca02018),
 (0xb9e082890090a4e25213c1ec41484480c1c6bc842cb04430a49816901409100482e50121, 0x6094032c04f0811a9081e13a2b3b9442c284302c208a0cc4900010a0b30a2b07900d4c6),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x400281c013100cb9c81c0c40628a090023802002c093c4806188b608c5085d48d780680a, 0x9cc17a0604a68042148083229d402482c049c3b415442a519e4208011a3422b6285a9154),
 (0x6e88063cc01a10a4e3484140ca5c70a3303a61220de090160e1a8b4a25190a9003483e89, 0x153f9403e64041a0821ba96100101504e018a54d21f2fc1c16024800006e52e7ca64050),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x1a8cc2032089a8a829501a7c4489f20ad0eea243022022451001e20ed4284846f2002355, 0x444314dccb30430500862501a01009050f1005a8cd455d0ae78e113002d4102004820c80),
 (0x5893682b3264f2d52813d2512c51139b09c648723011884983613402433923922ad04821, 0x76087c448120d2286ac298e1322c4047610278c496a06a0488e49692486cc010408954a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xd4a605998a99044953a04b040005a01c4c45c401146312116306559444c6802a61813f90, 0x2918780651408ba6281b3071bb2a5621a2a012a0438825c28409024a8b203705881a4041),
 (0xa5452786054147f23704300a56807068e0532c2ef4cb04501bd848455059828219b0256, 0xb501a002800bcb00880f3cf8480028e841e84c001080483a624252410aaa0557c8607401),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xa44601c5025f01614c9b810d3352ea0a08a599a25021880048114892330d702a12431240, 0x58211a0814008c88924004e244a411d0a658444429c02143a548a06d04b00b95288c0013),
 (0x145011138102a380b63836d0c424160a20c4c665200e51e114319053006b30600a0af088, 0xa3a7ece418dc0c2301c5c12038410094863811028f50a40669860724b184c81610500635),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xc0e58203f185014184048ce40893c7b27752424a74484502b8c06258520bc3940474c6e1, 0x111069340c60ba0a3afa100af468200d00282c80019208490134110704f034081a0a181e),
 (0x58a4000a1733075849e1a0006114b35101001050c0110062436835d364064196357008, 0x968411b630888ce08730025d9a1c80480ef40345a23a46910d3c040a2810689229008ac7),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x6c1094e418df310481c5a121d475909486381250035084061bf403249185c98618500636, 0x800d6113e1008ce87a3856d02902660a20c485adc40e71e1c008985360682409460af089),
 (0x861020e458de68c1ddc5c121179b7094863a96400350a4042916e7249185609844500636, 0x282e0d13a101923c223836d26000060a40c42890540e51e2d640085340681764b20ad088),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb282014520394291592a5d222a340227c925050920885830f80e3910e22020781e04be48, 0x464cab2cb061d2482918049058a5d18208aa8825931810305d144c71c82d58581e34182),
 (0xeb20e311423d734050409049410411684028a2080068b24476f1000740b5a0d821c07224, 0x406142e100084bc2481029092132206898000d677900120880484003c025e03d0160cda),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x712212c550b3056589b0050028090e9b6185ac84ee0a01ad4288428a840d47319e01880e, 0x8e5c853087082010640a48408004a0401e70500001d53a42b917182012e0a006201473a0),
 (0x849a150b492283e451541a1ce293c04108845a8a0a34103740a10804124a1a6bc6a04835, 0x5965a26416093409a481c46304281510f560053520096e802a4c64c3cc140510214ba042),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xdd5200bb215c028495e265188324d66c114421a2c3a92580c8480b0c320da75a289a7303, 0x20a4b5445203584b0a110865144200106223924838101802243250f049605000c0400414),
 (0x26243e210108c8d44ca091b0230009158987129004050484a414616106021c005465a531, 0x491880444cb2330b200422025c53920070180541c3a0ea2b0ae21084c939a3af81905a88),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xaa1809b18277a121dc704d408800d80100c500821083cc13186044cdc10a6842d62d0ada, 0x1000600a318012c6220212b214b50054f5002a45cc041360600c0b023861108921920400),
 (0xb300210807019840030184ad170f000092112482136d5e9e00f2f43a00c0882340f08207, 0xccbd846106662a758a232524890bb1f0048532c609281012c050100f916575085042d68),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x984220401e2e0629cea30400d0862c7cc0245b88e508850c800221007c0013096690310, 0x9630d8ab9a141a0c60154490307594381119a206408603aa0600102c280f0e8660961c8f),
 (0x988712010088f024408610706008459ed00c071064b0497b3e8e00042e8298c4a0868c10, 0x26186430f4710fc11268a2861ac2904009213027924214800150e62b01152131556133e3),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xa40f8008180824062c2428401520999470608e81340a66e1089801907030042398838708, 0xbf041e62433d9b140c8573d2a442041810a610e48b00108e306a4040007229844141871),
 (0x6ce2011dd2804582214008f0434a6df21a549061ca4140840840543304810ba1a0c0ec1, 0xc1201d0a20c6c9a70509de105a8201001610a4006340c307b7126aa0c190890080c11104),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x9c15677a4ac7002c8102566411b941a048a084900a10e438640d0a632c80210a0044ba22, 0x2e09085a0286f10607020838042024326503a4274860a8713b2948c122b4275402b00cd),
 (0x311722954003500cc94a1a5814442f05e422eafe44426a001ca0fad7828a91b40d2a18f, 0xf80004448bac8021126b5e02242b3c00811cc100111008418c14905287c6466482205840),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x7044888860f4022e1c000d4f0e6100c50a58301421688090801b23630380d02c3cbaee01, 0xb9a02108e00f511436c6080109cf30a71018cea0a132b4466409c941c300281010110fc),
 (0xa8880656500c8610db0242078a74884e9863690de061054a0141510426e30286220074c, 0xe0514e880a13259c400dc9000418a0000408c12b00810929048200439c01478709dc5000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x320c00119208c1d020e4e2490a0241204018828150c10a5000083040d991a8066d4bc741, 0xcd22b3640c353e2acb011c90a4e4a25b1bc73830a020a5a91aa58c142240021100a0189a),
 (0x404234414c48a002964804504d4a4c8aecb3294888988218815552435503800551acf833, 0x8e394896910415e561b189a0a28012400244d225756401e228a88c94809452b080500144),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x8e90f28940928c05361381ec48158880c1c7341008b00431018ada9034081420bae54121, 0x214a0832a04c515049081e13a06a05442c2880859208a0cea215010a4b31a39a4100b4c4),
 (0x144588dcab309812708625020203a9052f13407521457d095988093002d510a810820c80, 0xc3aa22030089610189501a7c2554120a90ec1600c2200244a477520eb4282957aa002354),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x4c2549910a854cd58105b14a86075203947c393e2188168429087c572300123494a24009, 0x9208b042f150022a7cd202205938a5a42a01c2c01443e10b02208108442e48c04340b644),
 (0x84b10804a900421703002407e49b2faacd0202ee051084085810236028a411a40e2114a2, 0x730e857914518860e0b6d900092050500269b80130af49350168081d4512c8539140a811),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x5d008790a01940e28402016008840044f2704a590150033981394532c48247608c2024e0, 0xa0f740285da22e0570058003b4607e1b080811249c0c50c01c82aac92a61888471c98b01),
 (0x4415380000031476f40000010ad08000200021300c0040000d8294000002162000000000, 0xbaa880002000c2080000600221273c004000c608a0000001b21820000001e018b0004000),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x8a498c1d22c041e2620005100310a89330891854a2821602c5825200962103209a730053, 0x30327242841e340101221a6f0820170488268103145041fd127d0def081ef4dc61889320),
 (0x28c33802538e4f75432334576c88260885124244488c2f71c12835018b2c136314da1098, 0x462c826c2801a082a00c0ba09367199418e0a9b29660808e1815c0cc1010a084e201cf63),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xce0102b726450309813d2500213579b29c6d650f411a84906901002633982082ad04823, 0x930acfc40811224162ac298e7d2408041611018f016a46a2f9414d69048470e44408b548),
 (0xe8b4cc65050380c151b0042288882484e985a43636063055d750a910026c03459220274c, 0x60302886a1058108c0d890060169000040a09c000814928008304439c01582a25dc1003),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x411a8100b0e0007c20ae600180780043231988201c48263ad086a808111380341640080b, 0xb48174fb0a1fa900d2401b1a0c80151480a6264f2095c1852278037722247c8300127134),
 (0x5254bb8114e118d14b1436c4c6f2927f45b658a3018490161136a08d162209c16500a111, 0x2d08441e0818270cb021413b39096800b000a70818224129e0c84d12c808c63698d508e6),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x108488461065291e80a232520980c71f204864e04c92a10144585100d914b8b401042d6a, 0x24796108070014002b01c4acb4462000d213091b036d1e9c10240c3a20c1010114f0c204),
 (0x1255bc44458139de9aaa48cf846c8c00044a028a003614084c4162820847822141013229, 0xc9aa40138a4cc62144143230320131c0c1a539156009c99013000059c118445c0238c182),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x20024444963f88bc5c028205066020460009885017126b9104826b0118080890cd628038, 0x88b138910000504003b479323890de0167a2018fc8641008216090146580066f12955e84),
 (0x33870012890800af8557037066000768a00ca684904020388cf402984049210150409320, 0x4c40c18d00f343001800180809c6589215635008031559c3030148008ba25afa0bb22098),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xb4008f90e01841b20c02016165200044927240cdb150433980610532e481a884d02024e0, 0x3ab60281da18c459005a0009288ee1b68081220080c30c2780aeac90a6042282dc98b00),
 (0xc6a0450a20c401a98109de10e113d500561308a007408305dbe0e2a08191e5e0e8c11105, 0x31153011dd2a34504614208d06080adf01a4c34f40a4140804020543104a1007060c6ec0),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x2c11216ce594060b0a529ce809a520444c88163b10283c8730b05d868007044a2139707b, 0x82ce82101a2b8844112d0214d40ad13ab261a9048290c2108041200132682925cc048c84),
 (0xcd46383154688080451122626a25ac0a50281103c3116188208489e449538a19a124e928, 0x1280c146000433508828801d141811710945a6c8148a16669f58721390a411264c511291),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[19+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

end Format11Border
namespace Format11Border

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check0 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 0
        (borderCoords (0,jk)).2.1.val (borderCoords (0,jk)).2.2.val =
        (2 ^ (borderCode 11 (0,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check1 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 1
        (borderCoords (1,jk)).2.1.val (borderCoords (1,jk)).2.2.val =
        (2 ^ (borderCode 11 (1,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check2 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 2
        (borderCoords (2,jk)).2.1.val (borderCoords (2,jk)).2.2.val =
        (2 ^ (borderCode 11 (2,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check3 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 3
        (borderCoords (3,jk)).2.1.val (borderCoords (3,jk)).2.2.val =
        (2 ^ (borderCode 11 (3,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check4 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 4
        (borderCoords (4,jk)).2.1.val (borderCoords (4,jk)).2.2.val =
        (2 ^ (borderCode 11 (4,jk)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check5 :
    ∀ jk : (Fin 2 × BorderAxis 11) ⊕ (Fin 11 × Fin 2),
      imageRow 6 (2+11) (2+11) (6+28) x y z inverse 5
        (borderCoords (5,jk)).2.1.val (borderCoords (5,jk)).2.2.val =
        (2 ^ (borderCode 11 (5,jk)).val, 0) := by
  decide +kernel

private theorem spans : Border 6 11 2 28 6 := by
  apply border x y z inverse
  · decide +kernel
  · decide +kernel
  rintro ⟨i,jk⟩
  fin_cases i
  · exact check0 jk
  · exact check1 jk
  · exact check2 jk
  · exact check3 jk
  · exact check4 jk
  · exact check5 jk

end Format11Border

namespace BasisSeed11

private def points : Array (Array ℕ) := #[
  #[1, 2, 2, 2, 2, 0, 0, 1, 0, 2, 2, 1, 0, 1, 1, 0, 2, 1, 1, 1, 1, 2, 0, 2, 1, 1, 1, 0],
  #[1, 0, 1, 1, 2, 0, 2, 1, 0, 0, 0, 2, 1, 2, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0],
  #[0, 2, 1, 0, 0, 1, 2, 1, 0, 1, 2, 2, 1, 1, 0, 0, 1, 1, 2, 2, 2, 0, 2, 0, 2, 1, 1, 1],
  #[0, 2, 1, 0, 0, 1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 2, 1, 1, 2, 2, 2],
  #[1, 1, 1, 0, 0, 0, 1, 1, 1, 2, 0, 2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 2, 1, 1],
  #[0, 0, 0, 0, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0],
  #[0, 2, 2, 1, 2, 1, 1, 2, 0, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 0, 1, 2, 0, 0, 1, 1, 2, 0],
  #[1, 2, 1, 0, 1, 1, 0, 2, 1, 0, 2, 1, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0, 2, 1, 2, 2],
  #[1, 1, 2, 0, 1, 0, 2, 0, 2, 0, 1, 2, 1, 0, 1, 2, 1, 1, 1, 1, 2, 0, 0, 1, 0, 1, 1, 2],
  #[0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 1, 0, 2, 2, 0, 2, 0],
  #[0, 0, 2, 1, 2, 1, 0, 2, 2, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2, 0, 1, 2, 1, 1, 1, 2],
  #[2, 0, 0, 2, 2, 2, 0, 1, 2, 1, 1, 1, 0, 2, 2, 2, 1, 2, 1, 1, 0, 2, 2, 1, 0, 2, 2, 0],
  #[2, 0, 1, 1, 0, 0, 2, 1, 2, 2, 0, 1, 0, 2, 2, 2, 2, 1, 2, 0, 0, 1, 2, 2, 2, 2, 1, 1],
  #[1, 2, 2, 0, 0, 0, 2, 0, 0, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 1, 2, 2, 0, 2, 2, 1, 0, 1],
  #[1, 2, 1, 1, 0, 2, 0, 0, 1, 1, 2, 2, 0, 1, 2, 1, 0, 1, 1, 2, 0, 1, 0, 1, 1, 2, 0, 2],
  #[2, 2, 1, 1, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2, 1, 0, 2, 1, 1],
  #[1, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 1, 2, 1, 1, 0, 0, 1, 1, 2],
  #[2, 1, 0, 1, 2, 0, 2, 0, 1, 1, 0, 1, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 1, 1, 0, 0],
  #[1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 2, 2, 0, 2, 0, 1, 2, 2, 1, 1, 0, 0, 1, 1, 0, 0, 0],
  #[1, 2, 1, 1, 2, 1, 0, 1, 0, 2, 2, 1, 0, 2, 0, 1, 1, 0, 0, 0, 2, 2, 1, 0, 1, 1, 0, 0],
  #[2, 2, 2, 2, 0, 0, 2, 0, 2, 2, 1, 0, 2, 0, 0, 1, 2, 0, 2, 0, 1, 2, 2, 2, 1, 1, 2, 2],
  #[0, 1, 1, 2, 0, 0, 2, 2, 0, 1, 2, 2, 1, 2, 0, 2, 2, 0, 0, 1, 2, 2, 2, 1, 0, 2, 2, 2]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x2a9000104100f0be482084e5300822108cb49878b023620207c50594a8f0a64d41413060f860084a30978652484184daa42ea10c0420282bc000d8a025087b562036372d08100e7, 0x6c9da53c010701b2071012c22544ea7141248001d08dd8003a0823150b5922208ecd92078697254a40482423a4212448101ca24a924210091f271f0a578001cb4848824122110),
 (0xb6021aab9644cc02082582341e185328328017a46061089ba510670acb1ca116b004994d634048427814170812ac2e0c2f01890800810108c07117009a8b5785160c9cd6c10e10, 0x8bca00009a8029c4642140aa0e388860d230050011cd660080a802414424c2941094402889001bd81232007801390e1506412421e787a15328288416034a82869d143212a916b),
 (0x202c50c599a2a0278188364b50c44cd0c0b300335881451012000004050ad02062891731300981f5d01c1024800818ca00c211ab039081407020a00012625d14282209c01106108, 0xbd2ab08604455407267c9a00008322e0a489a4c07041289cc05915ae2b124890930e0c4c3462808264244535e0382044214a210c84938988e460bd6c81c80e806cc04170028603),
 (0x681ca0000148e025d0462b0054011b09db60c8909e0100022004546ccc999418a8880394415d731c4082d8988931c4070881ea0662f4000c47090446436b08606658041194148a, 0x197a1407ef2260a4009819410a91e40002015330f0188be8019a92282216641c11172242a1c0208a1bb34002542ce00b8c20415a18901d0621022f0292880e683918293c028e070),
 (0x141009805222020b37e4209c0c892084dc56830b7866100490c044144d65d2008800210c1c03b23a929b2c1c65f012c0b4340300680cca8808004093f0224e61b800626606148c8, 0x2227801701c4588408104e235234425a028018740711ad9948060acb8282045356e082b1c1e845454c60d2031801001402cb483492331116b181220c0284000a425d81113063006),
 (0x80d2229a43202277b00011f260092031c8108212637055a042403b15abc08749cfc0081d14911042ac01284d483ae8510427e550044bc01d8290a00e14a4395fbc084601d42284, 0x17c090d21a8da51884af3a2091890de0e31c4292c180c025ea5a84400503830a4300505a069466e9910f683b2a7001728cb181a894b2022e014410920a84344800227888e0b8043),
 (0x1168439a08008c8115289609baa219984af4483a12c00000088c9d0950c0008220421aa14c4a35930c0d62170218222be4629032200013000000cc0081211c39546c080f5ce8c21, 0xa803c00c7514030684629d44104a4439508a041493f837e146062508b012d54cd19601c202400604092108860a1508000182781c439285621d100371c4401c0210357f001103d8),
 (0x24044474291816f26788b1569b8255bc84309a0406301cf481ee0102801eee135403e0d241f4c001449388b080e424802c35a025219c952224019e02a83892130d0835209020980, 0x1982908282c4e90808544001446108404bc5212b494123006210f8a06e20116ca268030d220909002a2c464a7212833781805652c823029dc2f2207013c105c09237cad2238946f),
 (0x15fa8010b8036a8d62393f00063a5064a226e13091209e1816d083026a12fe2ad02500d8605c2a427ec6807228c609130201a12384882e7800548d2417a8b2881a4160411048422, 0x2804570600fc104015c2c06d6985aa00045802802a056141e82f4c8584c000d5081214051181410881191d894418b6e461dc00846052d100d9a000820805415201968ab8222001c),
 (0x20a00d00c118a00d11442242100d810aab438c0680048101608000b9e48381f0a821b24ccd05c014030124dc59e1484013323533b221002488610008b157c5f22009464e409116, 0x21f04d0c0042306d2063385950c004010501042c02d1a62320b001e0402506c0e079c0c2010d2212298a08122821ca410204d024c04dc2d991304c4920ca02205d3b229800b2c09),
 (0x2106082300065900021101c3149800c24a030121829d1390083120b319533d80e8c06289f0860088a0508a010f499b28b2093426ed1a9b58000801a638ea80a80e2005068b880b6, 0x1680e45c03e882bbe0ea4e102003df0cb4883e4a2800002ca08e1b08e6888250072f09520848f410518555d4300260810120029110c004057050b40886141314708050d83457009),
 (0x980cc0c4309011a4556a22367800b700a87ecc60ac904204919c082c08e234084d8144d14390b2b81222620ecc5854289c3b2c8e424125610b055e3c910634b930586ac2b0c2, 0x18462221212850dee48a0810dc802e300500400130d524025312c438691411d4991902e1324b02e4803cdd08cd000a1235200c05201b4b88a84c0fa20c04ce90b44c6a591314600),
 (0x1900b637240d28318c092440d284080308106610528099c78a24730800306e8c03052e4d12548a0b0208c080024c282e201190890041015103022241426b81497824508a815a65a, 0x42f4188997283ce737098b32d3a316cb62c816ea55c443014598492fd478003b8b0c1a0c02b614068202c3ba511c11150004f74293ec42e80991d9624146c1487db890576a5800),
 (0x21a0885140f460529211a51440550525024111c30a0140490292aa100280030300382610414320cc001a1ddf15c3a34a104505202a8812460c81190544ca94644aa801411d76e1b, 0x184241263b018b0405e648a92caa124ad51a6e10a0d08412a949440de95364c8cf85496d90801e3025c46000ca145c84459828d6c4012db0813a46680014699114541aa66089120),
 (0x905456242c66018c00a8948041906902b24949236002e110f241c33cd06d0c9886409065145548805369ab43da092801a1b092289c242091aec2a0c10d41d013228525dc4280c0, 0x2f23a043d0095a31604121278a6f00e1449282cc8f711c4301b218c32612734511b123822a0297130c86408400c247aa100d049461114d2e010d492e008c260049525802a04702),
 (0x2b25944107e02c82a63228c86ad4002071540681e21a9029c8226316438278014da83891408c0b21a880341361181d02b19402904d020415262022b088042fe2207c3607c4d940, 0xd09a6390f804804519800005000140d682a2807614e1638225510481384587aeb201076e23538440147d08648aa7e2b14c48316c00d8888280d9084a571940191e8048d803041a),
 (0,0),  (0x2142009284848601a0424e810b4832cd09c715f002aa81af003822c29e27fbb0062f0c823987431510a504c4404e6409003003e1d90846d00b5044285439186c122006620002308, 0x1ea0c50d0b211174410410305086491080000800e05502409c430d354050040688506304c21898ca0c122b1923a00ba6b7c880160685380a940530c78b026683cdce01191d0c442),
 (0x311915e215802324054e20694c10348006128225e84800c2147902029a00e2118c041c0020010289621331e4a8b61810a883856112a6164818b10200d0a2a14083821928400224a, 0x284a2014868905a0221488000e6c302c905489217118b10a0801169650518c41170c364cc94a0621da0441202412060054c0a8ae01941b74506d8460b580aa4544dc6c532f5591),
 (0x2a052080f8060221c2002c308052141ad43710c1095ca91000400a0c4880100c6185ce086882840d7a258000d0634941483010ab11248e0618224f72748808c83304908c0262049, 0x92490b04681c8820ee108723a0eb400a808a0c328250e61e2341a3130b8493926a21d3017012f201d867bd281404223680a0400a9031f02585b00d02041103080966633890c20),
 (0x24a08010880820229100143622ee5648150605420cb300a9243529a4794ac0a6201b21890243104212614071b040a09801f08884402e522400016aa0378140c18160bb30a00188, 0x1925f31af6463069804a540c8c101213620c14894d24ccf4289ca504180151650196014742da46c21ac90890405be1867d001255aadd1009351c2155b800c9234441b40c0596650),
 (0x3090c354344880815469dd79010a10155242d680a152401896c36290ac0454a78a041020816201306220209421a1c22140e358840800282ea982826884013986028540928c13938, 0x52b38234994407a208020044a9005c80918002d06259882203c8d20036a88501568ea811418c6c104961368401a1cc820108230876f475010083c10030ec63910608d0130c8646),
 (0x2b3820a13808c202292c60c680ae0081a002a324c02831089200240c642b54786013197e03c7400dd603443ad5c0813a03110c29f8a00d1002a00026446734490b8481a4163c40c, 0x10840c5a003605e4d4500c186800ee5608dc58c801d34e9040f59bd3919009068700260050309b20216083002831444590663190045d306e44508a49ab90c0b06470665021829a2),
 (0x125c0b00df5e824c5724854a02814d8045942710180301885d4052000c0003514283bd2c24402254cc482891300b0a8c8215da754a005dfe4348b09c0027800a84008f70680a, 0x11889a0101f20a170b3805310b4691aa028aa49184e05e08c2702938157a0210ca8316c025019319408220742080a60e531648a0408858c0200a4814423e08035d16b1c708590e5),
 (0x3076b5e09313b1483035d7801869011c304b9cc6a410c00048345711920620d10c1c04040816e581a03401084010e100641661f31116620289258d70ac99a5384970701923cd20c, 0x489400064444a22c6022852a490cc0284b422091a221054350180aa4d19cc02e1201379d7011a6c41cbd0760a8f1a601121860c04c915cc7490628650445085b68b89444000171),
 (0x187c9340106c46408876160143412014313880d00084034234009010032005241300104800bd8b62a099e800c089201000949e4820400a78c584c3400264820221201428803120, 0x282834027ad8328807000e12008801a2b4cc17129b543cc3803d12e8e70cf3011043664831b423008564212f63c749200104800a01289a1012a19183bf08a4919d68702c77b8497),
 (0,0),  (0x2d025a088d8c4244fcc14e039904b845a3923cb02020153a25d088315050946821015a021b5440838c730685d40250180084603aaacc207e02420c01020f80a0ab040846244282, 0x8240206720128c110028004060e30302104c004e568a08408a07364c08a42197d684816d40a389303004305023898c2480028e4555234b8169b971a6a960755c40828011d02075),
 (0x1174c995dcf980111028aee2900c0700100083801428214704a373b8b03c0101d1c24019d46b401500a413060a518920c2291042c3580ef0048811aebc06726890805819803a904, 0x80a144823003602200600110fb0787be1242c4041535e90cb5484010800ea2c28393a66231018c00a09acc9b12c62d93880c8801c23b106bb16281143088917086522c625c52b9),
 (0xe462601f482503acf105be0000c31801e28600801302b200f4846476301cf442b18c414c9196150718368960101c08891132c714a2038c92c500092ea030212020c52102c91a06, 0x1030913a036108803005201f0de34639e1c11a50b844144220b2a1089c8010098423104112e41caf88748048ce9c3d5508e8118890084700118947481034a4edbd00000282001c0),
 (0xa0002889826a0010d4452a0991a2012c588100290600040c53256d4666909c01415496c070c1d044281c04dc555194c0c6705a20ac48905a004c1c1522583dd430028624601e22, 0x20d44d0626100256603129044441876020402ef84a12caba088528081912a2266baa26010022e299a8320792380042a220109800e12220ca177b0834a5182422a0355008818804c),
 (0x25c89287b7221466385d108d60c24745b20a0488039960944310a77008041ca3e2c540a61288108420064412c51226c8224500020f14091e02008734c20360b1080929420000403, 0x836054008c10800c5a046528414088a44c1c87174641628200a088273d1c20c10288951e031674857489b0412645813598a4f1c00e1c0e1cdb700c81d349402f1d484b8e7930f0)],
  #[
 (0x28c581c894201416dd214504a828304c01111a10a9443821c2382968a6507bd814007009cd2a30484105599422024a90124100b6918430e894116a2920b20a4d81542028e204888, 0x4101e32284242e0229c187a1416849172806161148a46c80800400310270021628e09e610c101a318ba0602dce4104bccacaa014270010740408480cf49f0b2528844830d31553),
 (0x1cb11b3ec063c2a40312c43484181a9823d4d205224f1e481db4602c0e1037414370004515590938408f301a809d08038103aa030c8218c80324cc62500390404101404946403b0, 0x344248122002003a88120c00860a56598080038c4b0e1244208930181c248961c8020922222e6863c4086c1422004c8641841cca05dc50010c93381a1202c8514628a920808c02),
 (0x2d6406428236ca08019ccde029811100548511814032050012959c8902837c60cc005bc08064c7058c522280176ca8d412d014402243484200009c94c390542826014488112c509, 0x10137099244820c49843000b104028c6ab680a6c3a4dd2edad6a4070751003820011202f549820626320102a480050226d27898781b0b735bb90214924602a53d8161107aed2246),
 (0x2086c0090209644522b0e05404471ed000e0062ee76022c030820001ae14a8250790c9d0482a04200830506b0800f01f52423904020340013714e180e70450e8e3c0618d144d00, 0x3135116f6dd10892ad40504a86b38e0225c0830d01895983d456144fe510913c2e8011224a744c999868ca900960e0a002089862025f4134a40a0104d006287041c338a528800e7),
 (0x1811a31b81c1099c0954d40b11bdb0421024604b405708891426092202499817a4ce0c10ac22f546164c41280830e450256cb502d2e8e02c40a93411ed488227c827818a2492290, 0x16e4cc43c203602f68001148c4207b46c419f209688b504001014057c166708003011e511000281e1b3a6472344088b009148cc0c071ad3281008c402816cc005985c45010102a),
 (0x1585312012006f2418c3f200b0bb6caa607c06ce6de44203d1d864628d68220558c084c111401870106c4160311ee9a691133df20c3641a05a0a280ac02004250c0608926051528, 0xa30048628581089200c048c0a0082519d025030900094e40c039b104296d8f8a4341110648e24094402ae03c28102416a8c800510c08e1ba46512f42c9109daf291b54d0a2aa13),
 (0x3183e500f80d2508050c8b580660a8e25f480301d10304bf0908cc264d6dc258014f18cf129340108cd20912d1740f448814c020019532158d1334944a818b41a29208f05140280, 0xa3418f902d0483630030022701e5015202618fc24408a00928023c8b28029244ab00210cd643964422c90802480109202c326032a0ac96850ec0a6b157824204404640b2885922),
 (0x5aa180a96032427070488ff849604b44a82a1c5698429011488601b1500c04105c4e4c00204dd050081550eb0ec0f8021a0088db402486228b2c41b0015406e54912cc22334c82, 0x38104520699c829030a300005a49534b84405c00043312eee16602c448bc0200fa011a07f9fa02fa4a1288004d0320120016a20048ed951943452ba008c2ae91832a130dc409019),
 (0x4e131a2c1688205b14d25900170cc314081cb8a10200d940599de22418c790032238765208015e04a52860bb10958f4016a800211284841cb011110ae02022c88912413410e89b, 0xb188244321431ba46b0904dae0f02cc8508304047c482211a662040024284ef4c5478924e094208258468044834200258104788ae90b3142448aacf4128540250204380b6c1324),
 (0x226b4082604033000c48c70c182d0d440a830840d448a20ae846526a2fa2972b84a066c216970a83044422b238a39281237c03de8403030844a0000c830222ca00619852a8708, 0x1111909c348f1c40c632101030c1822283a00ca49a2b92180106812984104428807b40091140488574faa8c848c618291c1c00e420090020b18b4593e36884cd118712672805025),
 (0x1b10437b12800049d040e108b85a030208ebc215017f08214f90978030905030dad80224891329dc24c04988001e4281040108401439cb284c00890d0320a8006e47c22002c0d3c, 0xeb4004c37a1b4229218e107259424471429c0740062488022404182272fc42524205a3444462380133071eb600c1811bce1a380c61445029334720c4846ce81902004bd050c1),
 (0,0),  (0x185a870e98086c54fca425b086201c9018133022200419358538d907810c32f1101b1f10e00040012a4d234003315f045e4809270bc8140032a40031c043e9965a08733150050c4, 0x6a440d06221028b01099847391fe20b4760435804da42c87a4500f800d1c50c2b20206a107d33664030900f0c48009221b0a298f42443178c113b80130c1620a57188088920e03),
 (0x2160cc041a18511802e4a8221734ce144edce7943481468066403e1c11a472b09b01b94081508962820461090161111290c6201a2c401769a0b3d66600a0202086dc0d8d18cf381, 0x60831a120052685210a07c9c8880180100100604028885c902f8120e04a010600fe02372a2b34812563923438020ac822114585823900164a0400896d1b44086800c0624220418),
 (0x8064242560512d80cb24aa286804282a06e09402184d000909581202a6432000047f2b06123d841500ee83dc51899805d44587814c20354c428f07421a00200c21080328a20380, 0x17d81c2988ba8507710820186979b17c5d00708702110adf4e203049d58ac84f0f30014882dc241420e001c22a43663da21ba683c80dc80a2b500c03ce1e99ba11e8338451dd401),
 (0xbc06881a420a9000010760517d0920e21200c51311669a965ba101904400af30c7402b82c8f02a52c3380289a5202400ed012a00408062000a406100c531005b090e0bc200a047, 0x2432107640d8447ca3830140e0004541c681e32042a19212824546806a888408c18bc90711002d40504803d020217094e002281919e07855c5105943722823c8412d1a0309841b0),
 (0x3423161835c1090000eba94640908012536014b100e40e92a0205200100b15274504d508a110222cc0000642d01044a0020a8c4260039d812203204702022e00440002d0a3c798a, 0xac02987821a40b085000420a00e4381280b4b0c4d125008019805f2c6d4a040126328c650abc9423629b119058c984f8165731880c4224a544c080025b1116083cc35201418041),
 (0,0),  (0x81a084d950341910104380824000790a1190001080a805d9001e301041cd301500239d04f51a81af16c2400122420cc502ca1004e8c3a8c18c4a2823a0360b500caa0e90211744, 0x246017104ad89e28b0ca0626126be84f1a829c3c10c557826b00187e88c208740b804029108e04250a8398692c894512a4000848b0700010843011700004840a53250116fdc48a8),
 (0x147030ea9494bc904226d91040384e5409684e04c0012128e3a6084f300743ca0508841ba9e863123ba0a0001519d45506603cc0c03202203aa638033d0b6418090c084f48588c7, 0xb0145046163020b2c5004a2bc833181e080310a24eac0800000e0904748a0205a5061a00007846580450c1202622b00a895c308130c2957c158c5d442148125b0f3c6a023a0010),
 (0xea96d5121053109940126c87c14c2c42f30188b86c818000a46224a46200274f918028d54082740d89a0610cf09b082af855c2413401f22b4cb8244280438628406a82e029c4bc, 0x14480041ea00c5662f8c83500421501900181604110e5c1613814b1998ac50200869420a9c5c8bc012478081024487c40700251a488c00d09245d22c34306942bf016107020b41),
 (0x414310a0144032400969132173eca16d4823de01ad9822d0104a24880510a8700f830e90488bd0d5900b060651219902e8db040801364881801083782a47464a1142a087828221, 0x8e202a08820c01a1d4048c8a08130012b2c400be5062012a6b010a35522213873024506632142e0a47749850245624ac050441b1f0c9b0240b805086c4b8909126b10b18690492),
 (0x243e020e921294200615e60052903000268301f602a195c4002c400d068ce588a0940700f05408c0a05e0a5d10014c4b109500a4a369211a0090252293104380b02320a0443230e, 0x118198b0614d21d0012a186325088f67c138f000d516401a6b42ae8220600057170ac8c20a8b473616818100e32e3394406829425c029240d7644211602024360900dc58320cc60),
 (0xc00a7a98a01c202e0b52904162d6401381426509e2202880800704c053102bed25492063b6384f38c04f49682c086e046d65312844a13403039f56c92a950004d20006255d21c0, 0x128a4014604e1d601d48c4dbe8d08048c3225002018d715080c503318244c801250b09b94088730460b90849792e48012800a0ec4911e8840d800a8141102c34b0978c9ca228823),
 (0x253c18e9010a951de2ce8601b59361602038500988001382a8c66256004559e08860c6e904a6812c07378688e7564488c74d08b044b4431840990c81da1dd0e03f11c6d55029731, 0x1802450086306222012141f60a64828155030a3401504c45063018a9ef20a40271843004c8115c43d00061601028934008b24246b14a1c231f46d06004622f0480e6212220948c8),
 (0x223c420801068190346e5426012ddf5825887951325156254fa2411f70c0b4a611524e04000503501041dfc8787237c840f3400aa8f10349820a40fdc00b3344614b2261100f649, 0xc00b1779ac0580102100a10f6120007c075068e8c86098a900c3e2001380019aa8501db0182408d8a820017840c40043c0c1de1000ebc167ca10a0000c44c131c94148acf400a4),
 (0x2c602b9a82686a8042e30e91440c00240050201840f98004024980c2591501525ed851092893308401220821ce0a0cc52a4d2320084ba423c404210202858450615c51a0e5255, 0x1011c0021700514119914212a3b935e097c2780c607064a7288320d39a408e4a48105042011608e5b581df39000c1100ac0b2448334b0438c2a201408a908030e8601a85d1250a),
 (0x1945204048b03a18063093605b15385700c241cd925110806a04200e00dc12032005f91c0694400634b435c30c101410000a04404c18d1dca68a8ca51aab3808849062102310480, 0x22a8023123458505184b0494a422c02876208e224d0a094594c09f10b121edcc5052002041422938400a423c034742c4c100d085b244282240200058c440c26753000902cca3a43),
 (0x2000945005128235510062481484428f461c871d044032b3c3e00007d05146023222815542811d44f001b822a9276a5a046800000846160028d00100405a0d29c10050942ca029, 0x300882386100d3c0806ea10a1e01b3530b0a1380239b14c4c180589e022863851419c3620352c20290fe643c906489000d21224f70200610d042076319b25600232cea60a4005d2),
 (0x17000104c40b3802068832208f1d28964b3450b9a04540462598404ff4806591284b625680a486c91ab3df817dc40246402022680c2120310b0c4a82bb2c1004293c38905204631, 0x884a2d8129087790135858e508083403009a8065b103f99c24614a00b50902cd580050820014906440c202a021a70a03fd75d012396de008061a02004d12f5bd202850480e3186),
 (0xa344801860661c1b2a236806aa50840387c1044022b0e5a7088851a06901d4025b8d8e22818ea5568468188168013a198c718d0a1591cc00742eb20820e800222c2155b97dc8b5, 0x18016e200d1981a4808487a9540a60a470142381150818508600ae1d840623d500402180707012004117243684c40564338c70f58228101d88c0097617107d510310204680010a),
 (0x6000d194012509ba8db5a8c36f318563482033ec1287102059039d7ab821d4914b2288c8dd08094008711745a71539e58c2878407cb0888454abde08002680e51e82e60a8ca08b, 0x380b4280ac6d0d6001002012c8040480004ddc00000380905029c420143c2292ea4881003226024311780e818502a061242800086800a265b801021b2b1997e0aa1780181401214)],
  #[
 (0x250c31a5b98895ccc808d1242ddca495dd010410182023556a0830403c4a1d221c00893181b06464006892a0a86a328f602f648ac021284140127345653100a160f286194880080, 0x1813421a4470203033810453c0225800006cd22b2646182a15c6001b0190625de26b46826a4f9a980b95284955058c60161013313b8c0236a9ad00220a022f1a15005946140c544),
 (0x35135a4a90a00c00a65020080642422c6809101800ac1006b88200078020e082581a8224d6050016b8c65181501f84636020fa9402c09f30c09c073c05861f8159240c4500d556a, 0xc8491004d835548269372d82d29d2066243624353e2b1004cbf180e520d158020059309689fe1021128720e601b109cde052b91356001266190815240a01aa4817298aa2aa04),
 (0xd0204a4803c0344082062001e8f8a01240148032e208942254a1e38424150215124fda8424d031c4001c90062c0041000548016e8006c6d1b71a814c1c8f68053b315a10a2bc3, 0xd0e96b0a5c4154937013014b407075461966b1e09012703910942143a4a4095a8c8300161410e8e2b26014d11d3eca6b630a4f2103e78202248e41003812082a0c044208c49010),
 (0x1d5415904fe2a816d8445906c8b8002878495b2115747f8ce0884fa9b0188b6000688f3a9c8842c86258bb3c3cf6c8824a8c0000a52968284d7008420e31657d628cc995098c418, 0x222ac86b001c00c902b80431324138140690005ac80180410b5710140d864498fc8210c520302c0189a14401800034512530b28d02941392b08013a530089a021d2324427452982),
 (0x32902c008ca24b3a00b29409922002c1264803577b803688317c4a7941908c0151a004c0080fa502b0d5a0049e38319404836130545022ca3541880a06c9020e207d1700870e5c, 0x4d60415840503045230163c248c0b92e98974000847988108c008084b60d73280e4b5a1b62001014412a0e826103c4420034964c01268030080a52209816f881828020a450c001),
 (0x3c0d6531351899d488184006205ee1305063984a9af95b06a06ccf49228030ab0c00c1024020710c709358e5029a440e126105a5904528012c10620304c002b232e84d88f135046, 0x3a0900e4a26222142853a490720060b078827b0610004d141923004803e0b40927138e816d38c73010ca3187c2538210998725241900694d042958c592ec808c915b2760e88f39),
 (0x108859b6d22400862202da9844c1215b9f0c6a91892f4126b44a4b430702e6bd864208b1da16249a2e3dbc041005126e243448168048440a0011ce862408c03060d95dd9b556962, 0x2335040901c084119df82061aa3ec40060d1106a16c0b2d90201b4b4483c080010a4064600288905d1c041800cb0ac119ac986415204a2b404a830581867270a862202224289405),
 (0x110440ba5434c96c002314818344364254d82847fd150925f094242b0280908a8081c0998526ae80c80fb256280004c0047b6c5e1c08000909014924b044107282302a547a4c7a4, 0x8ea2544818a26813fd0682434b848290824918000a0928a04615014e15d2455677839205298416526c009a047687a0851849101e0814d3462503499401366045502c4a88081851),
 (0,0),  (0x5a8a8090203b250174b20207917a204201018741006c9cde80300012c19d0c6018314d794208a1d5227bc69d02a408fa8c521252c89804d240238890b98081c19038030e5600d3, 0x2a4143b2d5680c8f0820d7d080481dda1f29a58b46001012024cb890c2a00039dc08202021487180040842860cc0236011021ed8012403a0826cc214f42426e382f81949189e30c),
 (0x1002052108101b48a0da6868089c5a83502dad29409404884d0a79d2e4a803008f16001c02480004821168436d7181eaea646691cf4185c800c584eb0a0220e8104a96006130461, 0x29658a5676c9e0b44f21828240430574299040568808592100b5802c0b540c017028d40290029c2b1ce4070482846a041489194830b828061a30501460cd8700e7b0491a104e202),
 (0x25b84c084181ed40b32c236451c88511600a431408018166d44ab22a402040208b9b02000420d8b9c5981f0ccb012162813410145089041086521887a4108b181050966bdc42225, 0x1a4410b3140a023444410481a02040a29731a4c3971a4c882a300d04bddf1c4f1424a453980303460224c0b120f4021538434d6bab20a1221081036841ce14a6652a68902389d00),
 (0x284406008d80151f84916420a2188188201c905a162223985a820310c30766444000565c3410488708fc8620c32071204459006558028863e480194163b2906b821362288b4c032, 0x142998710059c2a05b6e0ad758c66015c4a32304c155d4070548d00c1c7800ab05ffa082c864b210850250193c8b8e4f1000f20005d031841a63e4a6184c2a9421648c5040203c0),
 (0x2c098e1664054804d8500ca00120210aa0804212698403151101061923b2041d33017e2248d7c6014633d28402687025240c025900a01d590a016810808086d653382185023f2c8, 0x12a400889a8816a92526f21624920471135d28cd0269e8004642c8e6dc4d6be008ea01819600184839c80948b40207820b821c044b01a0043156044337127809ac430e20c040421),
 (0x3c50b0c05101a4141475090c09e22825ad2a282489042052f4712f2f0154e706896da051755c7104a84504086ed30666605e2a127b06a4544210800e19800d932045e0c4020e0, 0x2641a147002602490a618860b3020501d05080d44860a819850b021040540308d932904e04822008730390f0328100290091a0044404114121880757b06474700896a209180111a),
 (0x1043514cb026106d9da412949370174b040400080384840418a2153102a0c7ba88b72022003006900c035afe9a8a0519022a9f0416e32000a8da2488f2040445e06518a2ce888d2, 0x22308ab30751ca00204b090948016004d85248949c30396bc0594046290a00003208cd19c300f96f209ca5014045b200608540f92114043b05015173086beab81808e5143057324),
 (0x634038300001684910a0045608822930dd3280b803201400c43120002808658148800182653a58230d82303b1a65688402202451688028e300f231098085400f02028808e43004, 0x1149286cfdf42048026524b08033840c222087c428c1083d11082caa1c1d70a5e843182149ac021c4420d4244e5989510a98fc220133ac10400054c1638000880958907210801d0),
 (0x100891049a082021208080c0dcd00b0436200251797b10203c320050c0ef562a984512292a85520e2250c0472d818c5c04205b002558b700171881d08d2848a283248090a19129, 0x3efb2200801378318df082c24202ff4cbc14ff90404002380c2c83aa41e00a115028a64d2517221f0850f1198807020838acea04fd0220853a02660246283271564180d610e6e14),
 (0xe4e6c022ae2954490a815c152a7240f140e23068dd033131048820c2892ce021d422158942e9990009901443064ca0550861d1a168198e718ccc344fc0a2c9222722b218052105, 0x90832c911c2a310a038030a1189910a0a004f0420ac0286c852542812c20f4a004420308d1426faa04c4880c8031f88c306280c1466608c132080002e0822dc889c04039a8068),
 (0,0),  (0x491028212590c547100616280a021808058018d202e90415116444c24d485308420914440470211c80045f518448000d881027111332042a14000094e483082008ec411810dbb3, 0x116a656c4da692a380611018551d04350682d41043416200a860932382236a0571c120333c30316a035d0800a3b02f0e276a558c40801b0810293e428006cb513e70312c106000c),
 (0x38d880ca040b86c081609448b83d1783c52501088201a28c03a0c82c080b10a171098eb5ddb10a500a0551282c13c06904c925ca592a0140c85e024431002709825a08b6b204c8e, 0x721281561c44011501168020242406410c278c720841d5334522652f4e001420690004a2202450ab1d88cd613a02b001a12c82120155abb0521c138cccbd89205a453400842360),
 (0x1107501b457c81e2428085608900e00606088aa5040660c90099e802011909a25f08a364e46a00818485a5821a80506c1144c354309a80de5c7340c628a1928204ae6018050a54, 0x48f003600a835e148c5410805686062161133410ca8112068420035586e0b61080f610931204ee08597a0a49c0702593c01204a1c2455c21830c150056006444c8410004d26089),
 (0x151132018b717202c20614307196be0cc880641a10028209d81c280201044822190e82145c32c1a54e40010b01c40328a67380b100025c00700903a194384215560a1459842001, 0x242a2413024028cc01c3920808a014131342003e5a17c4df603e110a880a32589c401104b83c1060aa00300f07c32ac43188c33002ce5031b0fc63c1e4302bc42a09469264accb6),
 (0x104ab00159619c4b525843811103010a10a934d92024484f16024a1e4c01a3052db224c8a4a26e212002427106d280060901a023034a428806438aaa04f9c3664a08008e780a8a6, 0x2b954c9c829e019025053440c49476654e42002498d13680606191e0022008e8900d82270054114606200984f8210b89a2ec4ecc1090184660b870450a04000010c614310421501),
 (0x2030684499343c45da020d2a2c487323400c2ca8f59a612d44cae13604afa049242c8a10400502008a0f09686800131329631056d821610005341202101147570574005c454493, 0xc5cd80814200c1a02481e08503900cd80482420408451080b3301ec9a9104484c3c105a88c506d5b2450f20606fc08a094108a80205084106ac1cc7020caa020fa806c21983804),
 (0x140e009322781813421807584e102c540e8411213384119370082063280000603282250a1c2830038518a88560040d0c1a48270c57046e9043a331843121431280c0780484651c, 0x83405708818061082443c88630e48129e030ea964060a40c03c59c0404506691840900956385cdac20874338197362f300258043882b102f3c008e3bc2840c0d5e0986eb409ae3),
 (0x180842b02107e144492df74b0cf4a000cbca4a0043a8002b00ce02b4e5806068b048080500b0aefe504308337304b01390384048de04951c403d8941470bc49b106e220a6020481, 0x2c03d0b4c58002982d20084e1094bc12435a5d71c1650040d30a14b1a7f1d064e85a7585b0b5101068843400c7a40e02044b7250053624319c2362c005013202011cc35025016a),
 (0x14b02877cc042856112c4504768a063b0944405e3c4c8a108215216e48d11636b308030905a30525002200914808843a8857b4e863a44a18237eb3106075453860582022881c304, 0x22011100338117a0ae11aaf388752180f289a721c0b110cc75484880b42e808008e5a0b6005460c824413504a5e5580551284a15145b142398000880068092c30ba0df5c7383859),
 (0x2a9ac99c1202a81441822340202588f4370a6a400982d822205c8c844842208830830862108308320b8380417608a2a92311241270e20ca060a0d030831128b221ee8c451b0002b, 0x410441415945009a11949e1e5a3300c80000b2507d27d51d23414aa31080214568f211ad3862cd70783c8a01d40854486ac0e50904c313801106c450280300de10132880ec110),
 (0x3235c512b8e0228932887749c28012540282080c684100c4c139249200213c328020641c042a13c4ca15b1524c34c8175a4b6410cd3202582068e14785855340326210854059188, 0xca1220051b4912815208163c0669a8445510d316343f1b0446ca61144a4348354e83809a11e4293182422592c006088400990e02cd29a188830e885a10a0900480e102b580c73),
 (0, 0)],
  #[
 (0x30989b2028451700c209452dc5e8000022200c02208402502081182db1910449022358441a080758132fe880201f12454380fe64e20a1e14d80a0900022844968a8a010c1be809, 0x3c2270017d6a8606b25d402923014c1ff0890d0111360edaf995805424804320041040009e5d79004e0d01054c0406cb23c750012055080cb0630a00de857a9212044da222002d2),
 (0x8808a9c900d0312d681289ad4c08c50126c96d00a784d0015000048a09080a998a3e445bc90c5843dc0c56b82242b2848788b7964218c06ac9a4b3800c871085890d62907ec611, 0x4470624172186920581324202d02a824924925f183309cea6e1db41308775426400828036f0210422920105958d08590007402811071991324244764270696046c21d4f8108c2),
 (0x394cb08007848748248cc9c8030119086f9b84904d01058200260027065a021b8a1cc46146c04d1074a4c381060286e0c90408e24c98246716801c41682cba3e98d54162e522320, 0x6a34932f8733897cb63301454b82492106018243016702d3d90b700e1a46ca061813982110b804f8b03140c08c9281a12c9f1048162500021142382811345406220a69c1081890),
 (0x412b590430269c90844895e2250422859a01053958814930464db032799a64a0e802800468a01173905e99219114026040a48022158e8c57e2120ac819d0d318098c8050969448, 0x39cd006e28c10634d6184601850c3545025885086017a96cf30904fc88044105110901cda911c6a804da104c268695c13a4432f0d2071608811214027a20e002326737d2c292305),
 (0,0),  (0x14a8f0010564081140811114aa7a0645c8004e834c2ec5005d1621002004809a7d9402002000c1a824c04c0009030202ab5022500585a43e02040838b81d020008b874214683094, 0x95104ae40118542354ecea11080481014a03170b0d13a16a2a14e09d593472080216c7f545d3e46c230b19b34e094c9500d598cd2184301a9aaf5030340f46e1746838c310c348),
 (0x3900e738340293b711270e990d123489a0150e8d017688008e20e412ae77bce18838b0626461202308e029178422905e2122fdd438af0e0090382af9c04ca4260a0004d5030ab0, 0x1423a1042c0b02408405850420261c076432230308288270841d410601080031442040f100a0a5d10031042e8609847a1da94020a825031a50d04110426105ad8b516a3288ca10a),
 (0x10182600c62c0a522001408110720804a5a7043034312e4cd2b1d0401081099440433c4e451fdc0184e81745b023110000070aaec9166818ac7490fd0522e920f041105040d042, 0xafa391d52902d42097fa9a180c88041108583b83c3845111054c2622665a2421920001909840235a1011880a0b586c95f500941016c196c441032800028112150912e200ab0c90),
 (0x2240288480cc504884044c4140411180d28480c0508b205a0042062380771090940c824a03003e0a40088060086244c2049400d6c00e50604588b113022a0026bd891709b4807c4, 0x1cbe45736421ad052a8aa32e32b46c33011b4235255086217430f9182688012841726d206c18417082936a9db389a2184a0b4d280d70ac1c00320a2c9440e2104036e8704271030),
 (0x17083c24a4fa00a0524008488dbfc06960120dd1048adb0d3522580c0ca4c345200202291c41f909025124851b2495209450a1c4b4a04a0785a028037185a040c57cc001470248, 0xa065818901046453aca107033240118019a1d20c43550470800407d3a14900a01070d19623a000041500503204d2424900874c3b411695a862161724087a4716308120ee98d901),
 (0x3910e424048b1a2088100192e4351400d7484060811e0c7001617101480855a2980c2408921528d01151087c0421380011d5420c4842220a7c6a0a6a820923d7181db9900c04138, 0x48118434a3000c670864e6c1a40208328a2a38d6840400b6c80840a104422484142039304a0c30a4caa720078580602880a0c1317a941310311349141e48c00c760422cd1aa205),
 (0,0),  (0x302009c18031421ac847d882c536e0010c148386406c402c900000d10444c80a0d4561802b47040840f130898c008807947da0212880080a091128844bf25050a000005d50104a, 0x38196f02614863dc4323024340a89035ab26278012e909d402cd5232833a2201500229e65809011138c0603246395241049025b8c526042b5c06c152a3000050246df78228fa2a0),
 (0x30c884502280e084d850921c4404d01402ce81804700b124fa5d516812bd0030003c541ea9505c10800b2010c42135426221c0761042dd099b258142141391f132b010015b08210, 0xe051b0344701c4b228d0480036b03c38c213c3c98270ec000a222844d4225094f82a08012878026215097a70a9882a198940409212822e0240a5408882824088941a816846504e),
 (0x910423c19919b141d50a74842e8a04642ccb0585823ea68209d422c0141af41a810324401000c0323644bc211800426202c1782df06aa38066c847000803672129984fd160c00a, 0x208e3500620c0028a02658b6010043989c024aa10058111197600dd14cbc501a07eb4c8a34b2017c841a1001ec04ca811d5348590030004191925a836c5dc1858c247902e881cd1),
 (0,0),  (0xca862259f8c300c88001a87411cc4204b60ac0b00965e141583333d307a662bac407118349a9202cea22924a1a20b6055fb03f10088b0d46a02040187b79844c85026109a6141c, 0x202955a402288a0346be018bc4019d1a4804014d00001a8205cc8c24e841810402502428200007131189298445544800804840800364a2090894b3a300841210424082f2412023),
 (0x805a1065c4c000992fa48bc0430a2c749e89206663f400e05061a4275a44db8180408010d1112220016bb1285ec984c2485c11b0606a5212052ca3126130000a48420638064d19, 0x220810d9a122d0a64800830152484c288411213899403fc00aa804250843a242a66bf24012c809096a6804293a1060a35010324478a8480c472c204448685d1511180f080a830e6),
 (0x2a2c0002a5421b0a40a34942d16c219c841a8de251c5a4ca1c040b20341da0020e2279a20188324603b82902122eb308c88202200ce1881b0bd04321510009404a74409b035a84, 0x145911bc9483580f59114921d2c02dc0031616000221a5331c31ad09440a002611154865dbe134c90c40100408d1048c6252c214fb0102120a428a8028055501095880c40f8257a),
 (0x230410814c90a9203694c85a7e5175655093ac08e18040c0c285685027a203e156500ad9147800c051e40a79c08257a85b458c443638498d309c82089cc6e7307e832800a0bec86, 0x69cb32a30e4492880833250000081801080336000eb63a3072112c08193c0621a151226804102aa60855840b5d0841a03a4192c0001632ce0030f243380889817c84b21601209),
 (0x31912490d04803224130052083c102321e864b120201958965c1722b3fe3b85b29808464a028412033093824a048a5060608460080c951e020250e00a8ca0e71a8d6a0c90b4340a, 0x64a134720b218dca205b25010061989c14190e94022482208340404801c44a0d27b48190193169e00f485480a340038f0f620684f060e0ed008c1e80621d10e40205f26a410a50),
 (0x3b2915523210c0610001858e04132374444ea1b67261c079c542f18ba0300d21965035b4ba21c0062f40300423008f100480ac8c1ec72700000d688a099018455041bc5a00001b0, 0x82208941279025a62a11d8405c0019104401890e26041a900c041a4df2dc40a40241005c02c1d0394bebc02e4001332a52532120180ec0621464e6434522a41c03247c77446),
 (0x1c10164899aaca800284e8fa083648071e80009d0b5abc2a2a0054001074c4c6011048e541d3526a2006445620e45009e025a56604570a1a2ac0820b8a419a80e900c0b02c0501f, 0x2eb600160443072407b0700a70094f06145346244050155146803e9a10a29383acf871a9c0c011483098228d71aab20115010080808c4a5910f6860613e615906c10b47d050820),
 (0xc00fc8b500e93043415d2c2822f500026eaa30401440206891448824122240a8ea0380a812766000dc3c3010057d030812346a2c090b5069ec64398380cc43c13e02c929082d0c, 0x11a4011082804c1903a00d143d4009a0c000403346a920e86023905d80d119641018415512000198a018240c5008034d5294b04439624ac801303c4707e23102201541242c48083),
 (0x3c4569c223062580030030615410cdc80c63c87129105864f3a02154801ba55bcbc224c055903c892880b40c8bac07bc80629008d0608d0c1022a8b8e328010107510e019524244, 0x1b0060d88681271bc2f8f1223232215b190220682418498044090a279e45aa4241c4a2c82244030c31509331043484231884353021240d02900430200c00a6e900201f002d1431),
 (0x940790b1200c50140421250247224c00659006090560112691157c6d8432f384a88158a0586b6609c01031b1200d000041eb5a760728108d3d20261c158843e80d9b7148061120, 0x129e0220e04932de1805c486430cc21b7900ec9427a18608966880390408900285610861aa1940060288e8002c9d222f9be14200020116812820fd002e8630814f2400210b940c5),
 (0x13609401007f0b326c8b00e02852ff91010b84b7009f128a11315124b801000c10868901c9064176c934964276078ac82844014b406f2880d2452086029806446303906026277d4, 0x2c8600567c0084cd0024a9044620000ac4a450402c208c41cc02a6d204c6e3024000325e30c012883608692c80c06402d3826e141980542d20b253087101e09898740208c800829),
 (0xa403c1dc411586a00cad3a905805482e68c1b63e21c052ac4c80b01d229fc1030110d000260048421e8346889010298588106643001150c04965200b23302df957915c43dc2120, 0x34b2c2a0024ca3145611201248758a20081300041921da113b20a06e24d200a3cdaaf09b5582493a4606489206369121007c800b840a4271a908292e4cccb8004006e2198229e08),
 (0x1a6e1900a0925530eb430a683046041a430e27c261801252d222400b50ce1c8e1426180c611927514a53a8d38a802986043a9514582b320588b035a621cc018112250af3a5e8871, 0x210044351f48a2c9143cd093cb10a9208c60c8009603890404109144891102518248620200840020a18857286514d01849c400a8a14404102145ca09c631b86a2c588004481010e),
 (0,0),  (0x38c5153a39404121c7802d04eaf580c01b12cc5713ac108238f800132c855520000448011488500c20efc417008244958519a130328601021d612154e454e051c4f645b03003759, 0x52a88c580bd165c083c90f20002683264e1110080036278c1039900121a801db1b93012a007a542941033807e243b2808c650c10838240da214582810201e0c0a08384b43cc820),
 (0x3920d95942c0ec440000d00528b8d806118812238411a94003262b0045208405c82622b5102ee912083e7a4402001d0a910d8cd420a90443a495ac4203f0a44b2886cd91742428c, 0x8902228904002a59d509d097460461e82500044aa014b4f01804871a9708b812999d000b900688b080010ae57e82342c62222b9a145380412043817c0452201428204e015b150)],
  #[
 (0x2181f2850696a03048824ab461a4a820200050144500e03e50948808293fd213c2808044081f02595a6055541b2b80678449880511878c003072a9e30c20cec048be0bc2882261, 0x318180d0240210dca9014b10b1411025f03880d09085913000341376100c001c83051382936009880259f222160d42100232465f0026060454e880014509d1009b5409438250582),
 (0x2a34114a00a686543a2c0c30882dc80f90261146080122542037249e12dfa484004909dc9101149bcca92f40100841986cf90002d0504e002235b403424831112525180293b8b46, 0x118222a51940682ac083a388074001004e116600b6760421414809606c005060818492212674e960035440318dd298620300337d0e8a207888080acc888140609898c1854c420b0),
 (0x2120906044041d0f4c0481c7d810380c0504c18a704878d5c0e5070068b8257274e1488738942690665d50810089641484148401e2ea2a6d1304e1a6612100e041088708c981100, 0xe0c238e30b3e240b02b2c1807e7078088e0063480b383282f0ac09313404805891c9218c64249470980202ce950914a69c9533a1404959288eb0849968a1b1d326470760466a88),
 (0x5e2ac3120148a04d833e639492845883175b4381ac0286a003200149e422867110302c20e6412088c27b2032a1080762b014588924128eca120c821da0a10028161c806031484, 0x1321801c44fc271290684184686d0106608824805a51d06116f803e48412403088ee0ac1871890d9362880c18c5aa6f81941682470824c703424d070c20342aed421e25f9a0424a),
 (0x800260d002c8405ce06a4924029c621007204a30964b5005014d082a0bdc861a0279227008e884aa38388f6378910248b50414618b8805014309c1c183613a00064070222603b, 0x3a1f21192b243598830f818099e8618da4884a840a098485f8a62246c4240058601d82050e7102621047437094016830a04059698e344358e430c40e1c6006405e50b707dd59b04),
 (0x1ec2088c50032214124002c07a70000e08813911007076300415a1d3ab2594680280487e12c8b45418c45272404f11111b118c13400c30b068650881848793cc1901c6458810a62, 0x1214762a5d8d0c3483c412b84001be0310cc2acea0b0847604a4204148203829d00178025330202a720a908bd202842a4e0518484618104959a16584160602000a80100660c09c),
 (0x23420036c00224e821d0100062d2823406594ccd3584a0c80886a4417414448a00260d160006875148840964302a23490900d58e1217e84808b98182a9761b26409822014806a20, 0x8911a88280458155a23488281080c0010a22032004b0216e02959b801eab2559d9890e1f69910ae0528e49186c45c92449f0a21a08007a427427a5500094449a02418e02161011),
 (0x141e1c20c65b2031bd02305684015255813f8b38030022100843cb00c421c0745508289e01d141040824318b0cad1e2083183a39c63562290a0718305429308f220620184a051e8, 0x2b80e0422024cc4600c1c38038bc0c8210007005d80cc4c6d6a8201a02160508aab240419224988930db460082026000242785c41948158065a0804189c24800980151a42438c02),
 (0x8268e029150178401030408305364856cc83371a4116e2225d11806610a6221b8282c807c802c484842cb0208aa9a5a0a0127154405b244400b5242a60be1030001e0d2419042a, 0x12c12170440de0430af4f8a204a48870930704024ac01118980ca0898a9104040096d23881010105103c145cc50401a1703648c223c24d28b0e0240d11e41cbc864a100882679d0),
 (0x2ca3001806fa40ea84481513105090e037060c800825424258d50c3a05025009045c6441481a8240138a07870385a4a3e04466006504c20108559194c095a2052050d0591e4114, 0x290449de1e1019d10693028480908021f80319357454aa9b50120c1c00a080162c1a0919807411c9928404818646a4844163a90ea084331e811a0662837620ca21da20606a01cc8),
 (0x2820b03d010608f90989880e6a16e884100200502a040a9d2305ac5d8231821080ab2c100204050c727a20230e21a0a80f19ad90b4459115404228c91810d924888a16123302d06, 0x17dd02c020c80702c646270115e807604da8340e01b36060046841005404344d1904c369e57060b38985dac43000490390a2520a09122ce8afa885220209044254500129c4840c9),
 (0,0),  (0x54904bcabaa1d2842a82c12374d4a30211ccc0004811d880212f5944ed465018130458198071c3401c04820ab07511003971a484ba8a3415c830881240621500880c9d1361c695, 0x100219400400600211151141c020018642a330aa0a74a026710d000a900b907e54cfb23c47a08303ea2d001240002a283800e48694015426a208922a8bd08e20262e062409c200a),
 (0x2a83510464162098625528130311612024989602920a335f99060958a00503ab914229a104ad4b45a5288077a4818043011520a289f2b442802300c00a1030a20018f02614d5122, 0x40cac2991c91d239800c6e8600486d3180700984cb0c0a026e064211af024406e20d4002250903a5a16588853366e20f64a165962084bad1944230254410c1997260559680a259),
 (0x14240378898aa4b31492104800908109384db292e80b3004428b8f1110550a590a88e545d0109148948c90aa0e043025084605e008301c432090005216228b24411a3908339418c, 0x4b9483765513042b44859396646280c4900841157003309c1040a22fa8c12060300028276944a020104245402a4ed075209a1955c203284b06f50489c850132aa182d00c40e40),
 (0xa40030846e6d1f1f19c4a7e53035ec68900010024992082188608c22f900949b040ce9ad51548dddcd982804042802c48100a16c72c4412ac994000682062a0863008200a07881, 0x101798c2b8082e0006613500a0c0a000326ed66681625754e459a01cc040d0b6038c20612288b60002206d330b890bd20200c42908909208122084c4129290594145318871e067a),
 (0x746034605711c027c9c1923823f42b04d2d00d6800084442a064210a013b68103986241a814c09228a0786134a500004c904f000594260300c08128a073b05002a2929a0a216b, 0x32830dcb82082a3bd0121064825c0a00d22d234210eef293ad449bc6f51a841587c229ca005021e09c109809c03509b1e136e30e312418138e2201c5114044a80194d0420b48a04),
 (0x3028d30298200975cd82ded827268d30c708714521e20c80b1182202000f8e40240521a08010b944440a1040207e06e21f002142687381308243382a0e434020d2139285311a2, 0x3f03d02c1565886000203921264841028428058890840983624427cd0c368030829aa0c8591da4008a19506a885501981d80fac2808380100d5c0001141184af8f00e0202a4a458),
 (0xae8021444e501148731080850e0e10b021344cac89004f90671ab386290da25210012800780098c43115a401210096a9935ee008e1c01b1b1801855038c27a8380be3532a05868, 0x301575e0830a14ca10c293b022030480296811052424ab00788e5403992104d2821365217817e272b4e6a528e000d0004088116a51c17c0a0e43a4828c518014c484140841f8503),
 (0x34021b564d98809824f20013a4cb4044001031c3c8055870236234894c0801d11313bc16d6c0761a029004c00081716d9427e200b014406402a2418946004201400050ec200adb0, 0x141e40992063904930ddf8c10343f221c218c08108a030c4809095430d2040c2c68010908190145590e81356f000e8229801c8c098a189331100464009a15180ac480021f9124e),
 (0x1634642d0280b8229ce114009a410418375235802ab1722206020b4c1382000005042012200134b3906260049189ca90b488e9d205949410109900d0b8868b2592b232aa262b125, 0x2981108284504050230a409001ae114208800208500a084c99709431a03d0f599ac883a9c652cb40070099a10a3605680b331020120369cf0d044a000748708a68018d548144882),
 (0xc852b15000007061a40909008258094bba2150b320a28601c0060043900b0ed0d4e18088c240460750259f4d0e90bd665a922123c340e0da923894ec561a545819435e20702528, 0x326290229d0fb838211c454e209238294414488081e15386e1bc0e41c6120b000210a4253389c99882b5a2030412842192144c2c4143019042dc32a022061a227021880028d9a05),
 (0x310002cd801a9280698022c0540cc620468e1ded593280981024ce27a02cb3add41e106840608870fb000b9c990c703298b10a1aea19847b50a28810c0aadc0720002f0a5274030, 0xe7f213222010047107c8134a0f310488161c000200c3867ee4a1080008348000a816b112581028000a3d442242182082342806414a27284091872253f0022c801f580302901a03),
 (0xa6c01311200403340218204ad8118942c15512990d29605a014cdb810080a484808a910041410c813dc1e1bb88d071541a0824a105a102cb36008281c0a6101c8664c11a65e4, 0x24f413e6c8a41f870cbd105c980252a020d32000140e2d48385b010201acb20426160206c61940a832642260e007223068bc0b6d11e52104d24c1cd615a1c08c2e3389000241810),
 (0x3033618d02a9c8cc04227488805845868006084e02411c13259db11124693c96c062000a489640088c814474202fc2580f640a240079224202408086ef2000847420c8982042109, 0x5c4102035061431ebd900252ba200706f7974911d3ce004da624c464b960109221427e49049b581124c1088829011a4b008354a4280009df4b846281042e65a00c2164455b54b0),
 (0x712842b41b420310842c4a2225420b12080126aec823b078e4400bba8090108b0442bd80705b204a039205a2014437a8910ca22c369281e488e488c50c78418c50f42b0648910, 0x190c07a90b441cfc46588321d002a4f02d2066010115480e07183b244016638d00529c426281a40784e441584c0c91480626f31581c025661200192220c204ba60a0098401366a9),
 (0,0),  (0x48045006b10e0000021239cf89274ee73c162f001809f488abca06a085018400918a00132044abc1db43411401a080d32048a2990e0a25dc00cb401e2000044202409442440b91, 0x197b0a72104f0eae0286586202058b01082a950154600010010015104422640c1262515801a91400404142829904d7a2812171900f1355223e33016a1d61bd89050070a9998204c),
 (0x204db00120566909cdcbf020851642121910070d923f61347011a4121c09c0140ca044041c07100c0963dd8906a8c824c1201090107080d16102612008288a5a3b0030084764801, 0x13a2465c8e2802a40204099a0ac10849e2a1609200401ec98acc1ac5c30616c88350a990e2182060721020403945171302c064272b0b0e0086f08845d057148000d704c3389b172),
 (0x1090d821c4b450326321204338540998343270231c016500a4a80312086e1aa4a0e8a230942a00418088020010908ba340649004422c1909032500a690c80d98c2088821761075, 0x2660802062a0304c18c428a904021a603c0400c4023d8185e5301ac859191404a0a1309816191bc826921a14f46070040bd0b4c83b1c064566cc29441013270211433728c08c98a),
 (0x825aec700102b0444d1915889024110169f5a04f30925a18922c4d8336120a6500a885d015100118121c62a8cae0342004175222c384bc05a010f204c0b18a6820451400543d00, 0x251211083b2704b1182c482424d93c688840a12000345012045c0805089c46500e154000842cff047c18205101414c39e43088189042241724c4304eb0f0405041b98418121c2bb),
 (0x11d92c081494004030929804310880494200229d3408c6719cc87001c120018b80258703903d874194a585c1200727022507c0058cc9a1b0ca984a00e2e0f01150bc48898d66bc2, 0x804d357c121510b052c64b94aa62220b8c7c540c1522884421707d20ece8264680810ec65421882200072368af840c810c8328802324e41304391ee110c0d22844387202018421)],
  #[
 (0xa0120150a40281cdc1c480883148070681da590a08cf00044ac5a5a819683c49a1087121706a04255371680c000709d0d63f930744234080024f00f3c35210c005672c2c02583a, 0x34eec382b18ec3e320e3b1d428611e0915c0584257610e72ab1304a50c697833446370c0c87810b5a2c8a15b28af0e20708c024309bdca249c41018002c85653b920840c3312784),
 (0x21a445021103214740a13421826290f845d20947c27122040b1002afc810c8c8166b9c121908405611a06d0a1b18e0d84180a8b189551a18940324a540309f031bf914608014d18, 0x141ab2b5c8e88ab88d1c8a48209866009a2026b0280414988046d910104e03336080424880d489a8a0151254a4260507320511464022e583008cd05a97092094a00489167701025),
 (0x2011214502512440800008552828199995b6491970080c2913d25208c4229e25e11090a22088f332842c892e0e5a88bd0a3a196c00a1804000bc20022268222409212bdf44089e0, 0x15080830682e5b1422d572a84546c6062841a0840f474010cc24a9053b0841c21c2f61540c1104cd19d240c0702003401145229303120f32a2008a3d4097dc1834d29000b892011),
 (0xd0a142db000db103a6122100442621d0428d05940e8841c82340636d760180301eaa01c10907a546250b821280a6072000c9e308690107202010dc163b022a19008182c2bdca56, 0x324022c0011f002bc48854cbab3d9d42f8c32da0271639e20141c1c80895662844044d22824e81080c0b400cc1301a0409a12083284a6008d414103e9049490a6fa521508020581),
 (0x248c5002ac0ac1102a9fc3a4605101002134006a17283133205b280c720346268812060e003b2b269c1281de588a14011421d00d48f0945156b2a2254a1a84b702302ab9d08c173, 0x4a852e50209d04034110182023c8a4a5a1588864ecc84001211841c881945693180d904d01800244e21a015e82020982c80200a400428445c4295a57308f18144042400204),
 (0x20050c90c644c0b9274604680185b0b51142056a8600a01b4005a028401a112ab11051320b882920dd850301600125a811a0638988800520590080441c98f5e880708c10a9300d, 0x10f08f1631810154418b91003fe7800400628d290696f19a433b21fd0306524c004e428c9f42392c1226040d41d3c1a40484598726616d25ea40e42a220660a122c8d5327104600),
 (0,0),  (0x64081618190e081a04040b8deae95f980b3420a020bef47269346c0c6c13013224a94228208814b42818779008881aca38c8980562a40224ce0220a400102946417276632e800c, 0x98d500e1c060d1a5e9f910300106002070c11b05da40010180c9122090e45cc0c044a9530936e1421127080c64332501c435619a915918ca21b0c01046e18021ba808000106291),
 (0x30f50414b3598014e0c092e0972100890028164402a0c18400c604917c0a293a25be1581019108710c58484061d2057914c80a60a401348468f38138a88d72400934a856a08206c, 0xc009b420000774b10220806409e0574f78269083d583272c7209b2e81f19084d801c8361c2ca008200690a91e217a84eb07f1985a70087912004c854740091fd6c910205159d91),
 (0x445a4036415862b04ba88190218686444f0522b278c82009f1a402100d410293f0bdac3412a405b85c92392c7378652201484209b1e63610090b650395040232e9b00b40034920, 0xa18502490204084ea4172608de08719800320801831382020a0369ee829065200d40134a0402b802a369c6d08c8090d5ce8599b44011000fd2c488a848ab10c01642901384a4d4),
 (0x7c08ee40240a07293c91183004113424e2a096a51068306434245d511462959ecc48a5612085000204346222128ee3653d21ac4088a2c8e1489144a6a58c901139679006581c44, 0x2829211864b41c8528100a38b6bacc1511d1c09184214c29b0a08200e8b902a0011971a16464a81c503c9101d20200080c084501860593612374cb80900020086c4906c0981c013),
 (0x201423c90627062811803421cea2028579ff2b912a1205ea200266e921200102f3603430201122a65028564d91c6d0a80c8063801c5538ea41647078f810b39903161ca9580c4c1, 0x96310029080980648590ac610083d408600040054e438148d5490160494d021000002845be8d501ae57a8002c002d54e2779c1ac12207112600038206e94c2278686310a26212c),
 (0x178a168403364f84fa248013252b54a92943f3002949b4a4023104ab9600caf40060a9010345a0c03810a2114b55420d22742015daf920ae24fa67e0641a3c2620c5284a1438629, 0x25e93bec091041040926ac40948a5012240cc9d210485079cc6910205d3400051b00d8d49850278684112290a0b4b29882894001025310830510130240c0905a381310ca84894),
 (0x10f9010ac459419d6908040352a23ca44d8b209b58198a0f0960be44144705020cea91fc71326848950e16822b640010b458828620ae8110120072bd08223154099208071605119, 0x2b0696843822a8201692ab78211d81409040c12486a60510f08b003bcaa8f86912156001028800342ad008598080228e08807d3858410c0b455c0502b2188201d0053728a9fa4e0),
 (0x124304c574a04514b3c430a403912cc05144120408202db903a02247408f30b8898a943685628070794c001f21c6026405aad00c300d6c1960000cc4c01d26822309454b13c1630, 0x110c03a084a88694c09475b484241290aa16ca8440ad0443c1e94a012200c4062202b88220d58080090cca04239858be81001c0859082a48623f1322a22184d8890a2900c24846),
 (0x353242b28c800fa002e028081c2081010a84a120051894048014590d0c4004c2650871301060908005014544830984156c12840409ce608a47648c57a97bf0a087958120100d8c7, 0xc581045023800abc13d49601503088500b14540a4108601e0aa260213f382190348247299f4e07601c88b0749003c2938428b8c0308515008a302044840f5f700012d82980438),
 (0x2845004c02b00200a44a218020d268108d4414807141a0a854a800a084024008599c024a470e8213dd23348204ca751020927811d03a248b11208000250158f903811d0a090f148, 0x148898902d073d4e11b51272c208030f4211aa1c06085505aa10624b28e80b65a002358180c019a000008b60380500ab080186ac26c58930ec8227cd48560000c4642090e4c0a01),
 (0x200d849951e1001600e00ce09cbc54c5310d002148005310294144844a1705401109c867802c099dd04d210248a080078a2602900cf2a4a64108a482592452008ce280b4e86a784, 0x111068222e14dae89d0cb01b2240a32acc42411834b824ae543a1a00a020a00b4a2605004ec0e0202d80100c30482c305049bc249004121184a15175808884161119740a1681033),
 (0x212105a2472f03340832a40b61004c8ec00a4c504802ca8857886a4e042b1d2c14c1426587784265500a890000246b931a025c308402a846ec8b0202d11048ac409189205431141, 0x10f01508502000c68512308c593341366102ada5f11407802294b01a800212e21605023087998a2e5536db1402144cc10c200c3bd152801330b5f8204834009168508b01c0012),
 (0x68cc140c00c2822c92025010e4a95c5808e657d818840433cd000221414da1019781c07c8605a103b40c010af4500802508c4e02227060044a15c2521920587580801442844109, 0x9522e342973960132815a522091220a7f6198027a2538b40102641109030583228323980514814c84a23e240098cb5240c73a175018a9c9110200880821e81023800892d3382b4),
 (0x688084a2b41a5040a8b262805053bea025822452cc19c0f20409824a432078001428a0261885589435d6d40c800600a0140ea04a69092820c988041058a5c567814200a82c72a5, 0x184610914438184b71744081d02ac011a9231510512c4270dfb8420241441073e0b5419c8e268a201482829422288910329205da19016541d2065bbc00312009024119853c00102),
 (0x22321d0a34782b4c22670500e802c108a1044a86089a4024c1423465bc8be0d002401638c93052508506844f31e2b6286008021430d1ab09312854e00c06821a80a4c2a5a200021, 0xd89c025008750301000f20f00cc32634440a468f224198804950b980074192140946844240084835a601820ce1801c40f20d9234d2e44800e068a10a36925c066501810416e38a),
 (0x1606088280ca408208052e80470f0b0578d6824c9269209424259144c43b4c84501a962b38680968d08734e012d6b032318042b2140e00d1791100288280e54a0dec84017220f84, 0x950301c6200b250705251089810a4f885217db34412080992024e383984a22226044810030780132328890c89010b8c0e38840ce141ff00866c07c63055022110037b7600d701a),
 (0x20807b70204021e08802d9ee48759b60361d154023612441cc0450e80626601c001687d6a723d06810a4900326a820882780318001520cc08819815023155280a642103ac01100, 0x3cb54840d9ca3581a357d26010082048188c26a2e58820b0e10c90207905896215b20500940d42a918c580db801139830183b043fd088930a5766140598088d701019828539a699),
 (0,0),  (0x7020868852a49aeb064104b0712026914882941a654e5801426063d0400906f380529248108183407a42d2b51c1320b01143aa0893b08148d80261300866928245258486a241c5, 0x3008659458909641091b8b10082cf414e014429448a81027a20971c201292800c198845a6070a68bf04912042234891016228454544406610222d0c4a7609695c30401161012a1a),
 (0x3986c944031140430a6c8620400988a14c77b1a04431002584240e4c40cad810748c060c84a60102eab5212446c9b50d0815c2145c41882088e4090b48f0240da201840a0066770, 0x1832227c82bbb08593305300224306b2880e1628caa70a6b922022912421828911d8b26850267c114a8e92a90402a2e74238e0802e354e1718e2002308c120084a32e01d09805),
 (0x4491bd49032531653742c2f9103800bd4e43a25429028a1c4284c120a44410c7600d5f2e65e23486a044475268054a611a4024513f9a8223882409026459103a5925d164114c88, 0x22a0800968c180a8ac0992d006440de02b1801d83800805230d012cc448324d200a6080c088158079591290288272210a60380826c00129c8461192f90a0646c182480210889016),
 (0x500874a080f7001602b445589700f9816150c03a44b152744f023684c4e846204b024a8460a210a878a1a5588215ae8011101a39065e0c05bef401a7450091064108a65380130a, 0xacb7830c77005720804212a02840044c96a42e0138482981804dc839191239c910c9b00981504455000050a05c6a4154ee0e80c0c18182ca40099c4808f40018aac618a05100f4),
 (0x420053357734a4f30340080002710fa1d02cb808018004286b1380a051ab0004642928888d42bf1050089e90e026bc542c200d4794413811791a0480c6c9053c10208142680208, 0x3bc7a84ca80821a00ec1436632d02d0520b1204815853100710043c498c147b7992c0842040b400c98a96412f1ac84283c017a0a84b8647660605737431069001a6c62600848071),
 (0x558c508443204c14205c046fa244040c8483412270ac8ce202dc2a0235a040a3a08720380115119084c0002700180010061189622a92541cd9504ca4b4658151150c8c282c633, 0x42212865820d01382c6825280188a1be219789c458313230ccc028415c85c11104b78dd05640824476338f6d0f0a1696f70e81294856c0a6100aba002499a2088c82003544298c),
 (0x22de6640190a4530c4e314cc66357f241600266253ca03c90114505056108e100120d45c102209198b0b80481c35f0e19a8d0840000b048b904ac04154ca0607400403a0030064f, 0x50001b7a6f580c33200e92111c88081c8db41040c218804de63aa872183108666d72100cb1454e250843a36e2020d182110213f628020302d0410a2832589a8ad09641d5cab9b0)],
  #[
 (0x2ab99140a00061cf0420e348088c522b6480180602860660905f100000c862109501051020d929416c02696860a00db403ba45cb5063040400974f3e10435a80ac1b0417640aec, 0x1144606b4149c1a109a531c267353a4c4980921d8346079172620e09caa07012b287ee861de24941411349084100c700278019010a310a11ba2203000c534205c03e002a8811501),
 (0x221200029451898628614481f8050f89020822e92363082498083482010fc4c5904862e00c701cc2016681130411903022672503a0b2247032055882f4b485142185a049840080, 0x300e00ef50b0e62691302110407683074118394104c1cf31a45b58a31925010122013190a408542145e0174a86bc44e42510858341c458309c920812c010a2a6a882042b258b30a),
 (0,0),  (0x1013608e111031c280491806cc0646800090068b22bc01e4040221048024b83da63404c02c96e74800137140b042d5005842f9284fe05c86007886140582c621a4498546ba0440b, 0x2fc017516e62843c7c1067e01041a10c240d71441501fe118ad590536fd0024049836b17d16910b20eec8e8e05ad0025871106d7000e0201b3870868206911c0418222014088350),
 (0x1c0a04240c0283962ce5f4fe0211e0890c54551fc68101a843132b80c3c08c380916190d2a883835722614053099250284c382e411d80060e38588a0a0a963180820a0c05b90a50, 0x2134e881d07c0868900a0b0069cc10701322a8202864a44790c89418300a630524e084e05473c4c88c40c9f0cc0642191b1458036401a11b0068310957109cc4374215112002023),
 (0x13463214a1045015091a890a9a519ac8830202024aaa01870e6ea28e940904110b062fa228010401c00201929704928e42b02a2257428a2b310800453620022e1003054612cab92, 0x2c21c9e842710f6244a012a5048e61104c1415f5a0457e20e10010400a36a020f0591005d54a60c62945204528c02170904b4405a0102410ca80e918405b4481ccd81a29000540d),
 (0x220991aa098500021b204845c78610004c1461e90e903a0828316a5b6825b034191a4840e4819e0be4022c3b2586244186829290186a1900f05284845d2c062da09036024868a08, 0x422a1590303f04044333020028e240120b0206316bc0c196ca858016c2024b26252520125a2014034d82040a79cb3e08182c606714e0d20a004872a25199505f03c049a297073),
 (0xfc3a12232c42fab94d44442a15005065e431041ad2020a66788a5f717081008180b18c0e02f048418842090a3041613800f18e541320080e31000cf616a570b08062550e06058, 0x2d0240a4c012a400023200a0152246879002ce710420bdf1188520a08e837c02607c0871a0cc00011a61ad20258b901ac3970e4001ccdb41118ab94109a812020a30040a1180407),
 (0x25140341b0270840704059b40487050a9c12000246e2127264dfab1040038224430a002a2e009ba250100180421309960c711402b711518c0a593029740088f200c4012a651dd5c, 0x108874184c4861a2029b2402ab38eac043cc7731201021098a00044689183c131811c0814038444d0ae2ec341d448620320662ad400404232506848409e2630d9910709598e0223),
 (0x284496005ba08c2294703510482858800804da0824b082e5af46a2a022a420123a82c6509064c03983a4a4408491155c60452152124248114ad20124142b29195af4065d1a54070, 0x148869b28046428d2a0c80af94c78158f45005649340190840a0595f141a87a0c4443107001333867808432e592040a30992560c29388348100828912284540684030182c488788),
 (0x221445a30f8b127988917cc28e073000899210033169277741010162ec8c1914292d8b8d4249008010825ec4334434d1225e7c4b49b943b100810e921a20442e035408a20030604, 0xd018a4460702c86676e813850800d1516694c60c806508816b4f80801318620808204628802ff414f68012148388028900001a0b044b846c83051692452b1007023e645b4c08b0),
 (0x5053800846008c00105a925050c13861d0431c1ee0ebc34c8064070c280156de812b2a0d61805d25412a105010c8e1b41c10860507bc60080094a0220230aa21510430f0901c79, 0x1ac24083319ca3357c3254187001046862a2860e00b043c222e83c023911a2801720040d0845f0292a2c0050c60010a0223ab28daa0431696284a4dcd748f51800ae1c70f61e282),
 (0x13055240192049a0090b1da23775520888830c2c0c088007242643530caeba8402861b06230a09b0021a724009c0100484619c970c30e3c4242a02c00c720b9010a0d25e88c21c4, 0x20b02d1e8201820b4260a2550880acd7720890d2f3e42b60c2d830a0221004590d2164611474104288e40502240ea9e0008a6220f2820c129a90e51e310cf02f041e05211135e0a),
 (0xe085c869043d001fc01a409bf91024309a2874c0800ec28a40a95005a1eca1303891020088654562421b1cac050ba4a7681980a01a412a10fc52212418330993f14104a111802, 0x280c4a0186f142b4c01e61990406024a0c60128a0e1b401c6009440478080018c20322d8e1618a1a9ca5a0e3414850185801863905e41e900e028d42188384e0680298781a626e8),
 (0x288471a044043054005862c46cba6022358213402b07894c888b0548101982d2831a35a04870034484b1159013275628049102e40800c148182a600805343022e0237a4038a8994, 0x14210c08a908c1aa1d02943903400c1cc879808e50e06690167472328d24200444614a4b240f44983848e84f0c5009c0c36ae91aa06038b647541eb5608947c9078c80bdc044263),
 (0x2864ab080a1120129094043407820093d10b8f0603f06a095460532a4a48039384f06ac00928b0d1c2d0c048af38002008d1379d18d5749120072908496812200188a918e094de8, 0x121b1077b0668e814d4040c15844702004d40070bc078500a80d28052022a4483106803042834d002c050e24104408902722480201220a00104852c2200389cad4415461126b003),
 (0x1c0c88ee500de008ea0dde3652484c1822625212c4c480a5006014c11014766820b851c622804080430820a9a4004c84904c0340c188061004e8688681202583131334112a21a3, 0x2e3202300a6e202510450004885361021441d290d32222d427d86ca2a0bc1010094012611955c8b6da4d5c01413c7826b419270ab1a06c14cdb1511785054da48444000a0c14610),
 (0x21f98d282d2c120480a235a1c21959bc400030c2d90041a002239fd2094268d26532600274214200201c23660c05120a0a8598d503960038a08c218495087c000020022cc134bb0, 0x120030035082413b7e5c000c00a28600b10d8b0d042eb408f91c0004c0a892258ac88fd800d631294761981883628454b570252a546043415e02183a424301c49813e483240b440),
 (0x1a78b3b020d973583300c2a2504e7c400065922c7c061618c1125ac5c801aa10262023d140f02b0000921b090b4148ca2a08f2341b00810552a80c8308805e8380a818d422168d1, 0x25024046c1228423ccb315040320011bb5084940813020201ae48000125e10e589588826b3049026d2054414d090341095b600cb20c86a880c54810c031400446342850a98a970c),
 (0x204829a547e62c780411542002eaa45e500603801632c6e04101e0216003002348c4ed108200eb03889b500a480714416200544800184001480146e412037865c94389f8016, 0x2457531284009810038412e28145e911182082a8dc58694d1811264602d69a00e55c141110e96ca210881504aa5035c00b9810ec0a8601610bb8b2941919ac080000261c24038c9),
 (0,0),  (0x41e419073024fc6d1e202045f084228986901fa0049008d0c44d7306a831582a2bb548428393c5043018130222b2440008332a03c126c2888214140941264250a05008c8029a7, 0x3cbc1a26f0c2020192e0dd9ca20c388050306700462905130a103288c015448545144aa28918641ac10682200c810888cb76cc914434d01066546a216280811c091da6e6318d458),
 (0x11048d0250088058292630b150cb3465000e829c0058b338100982911400c1181688d21a80550c0458d011b548e5d0804bece54c0890830580004b8cc6800e84033054546080018, 0x289800a8add42a84d41900480734cb08360178215a030c06e1325d00e9f40ac36110056528a2306a830d860a34082f3f20130202420a301879d2a0613932005318878901836d420),
 (0x1ce84285408704500aa556438098245d4000e24644d3e13c9242ccabc8921c1e216384028c201539253aca040601f01113775021158a3a0446885252f00649083118183fd208c89, 0x204bc720e282123c112a8bc3c600202ad201db13a201c4100240010216983e01e8438d87053a08298052498e0160c266c880a48a271c43a8942ad050a20a0618026078024e3276),
 (0x2c39134225c08494844405b89340862602d5811103ab0910a8433658a1d84283cc0aa00816c50d444bc0cb0303612de200244920124010cc1284588a808800521608088a600048a, 0x1c6600c102c38420b99c04204b159d885022ec89c00c241023040015627090422b459b30920e012002b2404881810114d9b0082450c8f30c86985041013cc2c28d3636416be305),
 (0x62d0129970604a00a203411901a19300ae6200922bdc24502f00a44b18a04628642988a188010c488da1281602917a8a02393304490a038008546b803c47631785b5de14600a0, 0x29840020220180208540ccae800a1e402d5195772c1002d02e50ce11806548a9171b52350025ac7100720cc569b16a8114e14680a990d5c020f182903701b88c20784021e193043),
 (0x81055002510090210888304aa842e9440291f12540122012a1150e78729181428003c41c0c660e50c04e842022d4440852ec214280f944870370f5c5c30a048c52182101302948, 0x20020ab6906246cdec376c3a015a81082982802caabe89e884cc851878c4a628050b008833201312a1c0033d6082993932d0152300e021278f08008202890d240ad83dc2e874224),
 (0x20008908082e1252429e0952805c07041888c2b8232b18e8048009101610188840800000811814d4080a4e0521925d61030c710c0a380189a1a02173025eb6240c8a01860054041, 0x1ee4680a5812080b5006621678060216371314694d4a200d8275629c9aca3521a30f56c3ea76b09d0d590c84e45a29a740300e084c6b0104e0bc28cb5a00188d125ec60c789e0a),
 (0x2f02680020844820a140521408432142e8450450a00a860d02d424492164200565442a4b0d43af5a304b23a5648819f0564cd00c0073810e91029226923c0e44e2c0bf4d18182a, 0x340ac05ed4c2a034d5606a54a62a8cca806006800095440c2190a82828211dd1a029041a06210500406804c4a0a66e20c81b02c83d4085a410821684808c2d118000600a022a640),
 (0x4b0043289efe26052bc04a90cfe010558015651692644710eea0418208db800a16cec0b52580802a4a09b487e8a78c8102e32285b73002a26e0134a5500d2229c5005a0a285192, 0x2a45a88860000d9d0d423254f00164e28786010a1490090e601503c44c324233029102f428025188520640a1014101072390051184844f80011aa4808a342888220f185e5470609),
 (0x2a106012440609096819224c480cb5d31081d585948a14682040a80000080238a810e3e004b0b58c207800690021a11e8870930a080118a2241874c00925493495f82d490812450, 0x11ef8ee031f9304406828c33b192022ceb42005a2961a803489104feb802454741ab1c1ca3410a005380348040924ae1248f00d58010e01d0ac00036049096cb4a005034168932e),
 (0, 0)],
  #[
 (0x109a10b0b3c0501e80054cfc08022402103f2024a60590ac0bf0e8d91500440812958503e0d016446200204a0008a82ee2cb5a8043308209000ca440102f8c14cf40863108c041a, 0x9650000040f8da10782110336651a3c0b005f9b58186513d00d14244881a251ad42325810212991884212318ef6029100048400a4cd20a0b72248ba294032a230b201847735b41),
 (0x41a2338a86762c2d1880c08080c7090458405411fdeb5906283b338180ac0a110701cb55315e41d1304a0695600870a888260c34a7d24285868a36fac089882a8bd349f00a8852, 0x2a854c011308993c0a51d08041330c0a2871c00e4021406285784cc644103b4660804108a4020a428c420a02882638e571708a148400c257a51104105071206016424260b244628),
 (0x941857224c290940059a258c51c0d01c02708602079284e055470148a614dc182208b94c90258708a61889d9c4c7ad13080804704100471410480415c282094840c021bac54200, 0x12b86801d0106e407b26190138c170f211c09098460457b0c8098a6a149ca2025d49304b34442506341464006290040a071d3e305826428a0a8010882103d72a539240e04080599),
 (0xa94534d1820c099a008013c84dc0872031048aa03824520e8d0e0100c631daa22010690080c2c7a900039624604009200230c280117668a008a10b80481f1ac8505028042141b5, 0x2008a430460431420f5460026100160038022344a408080f020a12c51290c211886e6142e022920061c30605981b0e69a984e05368001975ed24a94712340a5342b21d491021e00),
 (0xc20b00641512f61ed480020ab8a0644d3f4d22b1236859a2c0d6b2ae41410b48a96ad08a0227412a8123314820281183e841d8b99080241008807194b0a01598f902493120a000, 0x12c545c93082d010122062df5011f0200c0109408d81004112e290050b018d09356852c64a518aad552908c838a04063000a603020d3dd146c4358c204040c00004ad8286ce1954),
 (0xe43c0f12421ba0d016821200124a0a000537172504b62d484402040970c0d50010977a8c8186287020da286c7da50426540e68849c4080046a40a5100440029390118823402084, 0x3c250e935641d2f09492df4493464696048e812e94942b19a719a568a002af3870081725019d200882596908012d3d12361117b42bc24330501506c289530406e4e62d03d4623),
 (0x2780044e421004a872580c00109186a6b43e218496042802026038ab5084ac021a309d82922b452320608231d6b804419242e1321ada269cc200501b071c16f00002a646059382, 0x2487e7321ac6913110025e15ec960010103c18a0a49399515290841542e6a518d254e02156910aa4c9218448e000298822cbc040d600098032c880f24d023090f7bb80899886c04),
 (0x308c255898038f78403328132a0282431002a0526c41c08a0410b00881942401f3c101005bd14097d06a92e02a760ac10c4396a21c820088214202270210008ad6243480592b40a, 0xe4042046768700285cc438c94417c08ed3d4ba1808e1354730b04b3082bca800c2ab8c6202613402a856417c489350853886851e148b3670c007040ece35a54215bc1228654025),
 (0x16297847395fe02066c0092884c50033016aa1a30ddc0a174328d3528a045a2a020957119c26d99201820590010585c801a6ea00bbc412742481a24f4c5e24dc478432541a101e2, 0x2092053080a00199882ac2865b22898802844600a00105c098d22825206a2114f062208c60d002207a28c2476e304a25301105260038a981405248202200090330308c8a45e8804),
 (0x3016914070c4601480c8000e02e8087051a9c1ea102d900e70612ff0e3896029c41611c2b304013e88d708031019130e4a27b101b1b8853c075145883a091589451398981a51007, 0x4410ea5040a90e06e01ded1cd02d183a4523801c8126711821c1001187085023268e2110c8b92401020333863c6c4d0b51804f20a0362c010a8b273419280323a80246381a4ae0),
 (0x8c4a0a513003200150081822cb4780588088302915122666299969442108448b40b06d09920980da827c0498a002b4048041c47b0d0310298190006c3261c94048702210699549, 0x25001308c8600d482aad3831004b066210f41ca0268e0c1119606103b0491b874810c10026432450034807305131d00c816a2028480b4cc500c40a300c08a049422098dad104814),
 (0x18681ca829021840a67d849019659a06340595c062e550e00d401010a854351642d80a271a8446ed80003885b0e00058114140f60011102404b015984e81f625d2d6e2e724008f1, 0x680c25540a482935000490da00801d8c218482a15128c1852114c0e07ab0a6038267008a57231025281853a0f040da0082eb308b0ec84497802c004b10601da292819101378702),
 (0x2c504810980702431a35120840a24ea487110e1293705410408c2020054045212624a802000464b3ea4a252a1206c540934c44642dc00b8fa085e100840800981238e48006c07b0, 0x1022a02967b0c01cc4c0e1b33054005000c4302d288daac2a8718014e211800ec14212886a61810c10b48844c1a9303a40213019523e600008481aca2ae35c654c410b40910a800),
 (0x3209c94403884046b0102200ac6d2e022c2e0040854418c0e88a0ae4aed2b1814a9980202d2408315d3108804c1f288900848293a9001810cc0c23ab2bac5bb181061504100c880, 0x97436a148171ea84f6b952f5110c049c0003f942ab1432002446112110c40360142308e908007c0228c804c8040c47674195c60048be54913834c50c442800e1ab908d14cb246a),
 (0x159a4008090137023c4c83800005684022c0893e2410901c4342250170081945044838000874441090c3a203ca20800206c2c634011c0c92c5a71c6620b8332d59660d6029082f0, 0x45bb0082da00bc8110206329681712c13c3041da4e69431c35d24e8a30a6880300850e330a22a4281014b804cb5381292909cb86a17161000061905e4148102608c012d4f1003),
 (0xa03e4c2b409c400fec5090a882252044d932130302820111045901004c24498089051013396a04d0a00a000c1844519c791e49e5071225406115341f132810200495c102b0314f, 0x15dc0a0001f01b110022d6500755a5b8820c5ac74ec5846e42aa4886aa1c0b66312e8a2480281f12202741e0084932a0080a19202d069d0280248008044c7abc0fb2a02c54d4410),
 (0,0),  (0x29662500f85e40919406c71c1b28e8896304d0481d2265180e00800c231000958895f0d804a20602e052e5501e4429d18082aa26ec708807a050ad08488862967850c38b2f32121, 0x141908a30000996e699908e3001016740c70253580908026306903b2d400ec0a00220721580dc8c80da40824812104002d5c55d8108b63c8458042b712029d6087ab1c109088c92),
 (0x100c7b2211d003a40029007094e00111ddc129cb134c10680c0d1240ab8888029099a0aa55606208e1f024a2ed7251024201ae4c040831f72048e50cd86240059002523016c722c, 0x83380c9082f201be806990c29198042000002146021260182c0c18a042060f04d601d01aa9494111c0e101c1204046889520003d9314c00c08708e2040000a066b1018b88189c2),
 (0x6098fbd02c4d200599424132e1a9409a215201d83f04080207880006803b0de000274439a0d751f4815ad4940484293124140c960852ba5f228e5602c20249486a0c10469d0120, 0x21a05042c90109c0a24b8b00c08041221460c562200601569f874b588068492075800b284170804017a040020593b16008aea1228528401a09500a89929a190829033c689202c93),
 (0x11c7b22e2f610403b7412eac949b7cf42de340c04f22191f1010062116c00868204300d114883c998529c8a4146a689119026114602ea73f8423f724010ae698e8b011c040c1236, 0x8004dc0d08ccbc80096000323648000d2081125904c42e0c60f990a0923d6814018882a2132c3641a161510ab84976c608d92ab180150c05244084850b51862154ec2020f30509),
 (0x4845106a000001a46111108a4620a100055100226d134f41d851e2a80d88c4216803b31812a7800818808340418ac24250a40ab04938e8b2650b3e44b2b1e21ccc43011a2210, 0x24031186100f05dd6580a48ed44180f52004224fbcd10c49028222611579076221a97f008e18040253360445c28b6712c0c0813144a82c317009804c0b20c0619e301a4f4e149c9),
 (0x372e9013a10419e143500c4050820280409b8561535a01e3242184862a44d021009948c01483a13118006d050180464058086e2185111feec358e000d3843116f015820a43bc00, 0x2800105845c08e01e348df18306441c163700128a0ca45a0c12d40b41d4a20b4e5e24122d424842c6e11492a8f60f389d82f0005030a2c00100020720243a40a90c804401084252),
 (0x3c783959c007e1022a35a632011d4c3226e0cd12100890402a80c04a09a46a103260830813f80b2069052100d13481621fc022c04868014248e9f48c087d0aa2f090b8210da1086, 0x38680a01f680068048a49c5b66231814910306482a4241181760615a21a04c90d9228f5c802449586e2043c0681408d400f5c3293950a30210401605502d105040703cef246368),
 (0x82151820e8486aa64028cf40c0df44005900c408018218045c5ab004668e8825d0cee416707640a00740741250028c8c727da90f00404c8013210d0022292a4314b019021b270, 0x1605aae59e16340541bc8520851b2019a5a0d83b00e82c670a80a0449800601180070103888389270e882503e0a32d32610d800010390a23500c48020c1cc485a4884142d444d80),
 (0x101e6060a00c422c88214c0463425a684265c31ac15922708308c0424e11210096c105821a2108950a0705129020998881c42000e4282b2933e0b1dc07baf1343c8545f4202941, 0x2ca8016871b5184024400a0e888880091a9982c453222c4060ce71994b18a0ad24132e24de48a040a54e8a88468c804636421091a1114c05044024822f045060102200209128636),
 (0x3a501a8aca1908c05e1051008391030203a9864c00401001917a48086b00b10203c27005912e208f8a07318a5345026241ced02444060a5003ce0115c690c26230040f850c66e55, 0x26c0553546720d80e9868e5c0aa4a9f0120131a2ac0ed6088194e200ef4e7d182d863a4440944030484a25282a6d91ae312e519ab9c1abf8111442204d28144972102050181aa),
 (0,0),  (0x11a60848690c0838208987d630a085bb1e210a11ac9620a8644118b264088a7160604904032810408280c4b0244d41259c601a110460a01901f0026b10ab20406a0630030000287, 0x2a195720849210064d5218210b190a00e088b58a1100c9148b8880099ac0658688158202108500b94443230f8a302c50628025c4d10b5d22020661100644dd0a15f089c8b92a100),
 (0x4831826f0419cc0381ca00046841b0d86c745582cc44a74723444408090a230445b848c1c0417980430028020e082003d490461950f2b00080484841740b24b2ac1c698f5a1150, 0x2940c11808342034c761182ba0336490092890a60301a1088883810d4d0344c4a8a46072a0b1a861028a581d8d1f24abc2924a10626050dc17b3485080244404c4163161020e8a0),
 (0x2c454180601096a90cd282222024c53c104161083c4a2dab183e64104941ccad7141029130c880260118c6220310b0b861218270803e04184407c004bc2182000862820b10b1475, 0x29e208504495052203411055a2a418e1418408094d01467c1904f222c31020e98484440014f013ec21085988207448410380c104161e028d8366842960157e3857c40eb0e000),
 (0x1401d0956f0d12300403892401a8378a19600a883011558682621028120a02a18424a34400032e0c0180092dc090806c958111a81c90523f10255a24209c046052028b11413200b, 0x2bf80d4a10204d06b3fc549a2854c015c01d3430c1c42a0150090ed3c1b02c5a504b540902fcc0516817664229241503484a80408307898046d82180d063fb17a02514440c00384)],
  #[
 (0x318610880198ecd108085a021125a20ad00e0281045581340704221b2181e5e05422c0418a148a44417c20b1a0012d16030101794071888349e471041984a40b4945203b700d250, 0x30a447a4240126f261a1ac8cd009c029d0906c20880cc9c05250644e061016010501b601e071013203184413ec4268ac74cc821d8c463492190e09243a48b4b298d9400e5098c),
 (0x6c975c708298e4518213003b2f9132400e810b2712884860824a0c8407152362b90bf922d8d4570f40288540a81250ed5c04302232502cae5c8a039b003468b101fa0a049a106a, 0x8140238559020a200560d3c050400114b17cd4d80820b4890904c041c0a8080844500690232ba0c0bc80628c1569a11202d0c4d1c8a8d01101143c206f0a96448600947125cd10),
 (0x56891bcc004121014f50aa06324032584c04031525190b1891040044d0b6081980578d01016c3281240004833856446b54813c4b10f1328bc202016c76295e3f9c81022c0511e2, 0x309708433180818da302b01f0c02a402110a038ca42e2d4e1040a71a12c41d4020da0107808118d4c4b02601044a02a00806440242e0e81302070308301122000424e844070881c),
 (0x719e9108403653000624b44427cc466c2100d9a0820ca6386a2007910d3415303a09d94520811043b29b00a00228a4161a8ff1860a22042d080bd84e849084d40f0200048610d0, 0x20c016044ab010447699a4a3bd03239920aa90601244211409550784aa0090ac08412243a135aa9a40d24c544408412c0042004509198e302420002b17a617020008594aa102b08),
 (0x21606e111a13880a11c400c02e2123f2f5287752059c261a0057002210024d981bc8100bf8e8f00312c41c4800a98132192850025043cc6901a5780209c7412910980185400e700, 0x10011046e5c02095a40103111006840402c388215a4119a0e7a8758981891061441005d0021401800108e320eb106044e0908cb4ab1420907c1004b9b4280a024921887a12d1822),
 (0x13868a443118533000918554a01c87002f8c6ae2018202129a0f0a0a10006952e128d8c0d008977092122229e090434b2c311848a00100008d482389043059704a2a0030126282e, 0x2c3835b90a240c09df063a2157e310e890411104722028852460c4b04efd0401145420280635680d41498906036b3494404043a00cda148c42369c3479c7040f10416484e8913c0),
 (0x280a601337cd7405e467a4f84051184878ce2089184a06115136920e04820640018c42500828009484c004008a5585ccb357d30c2721e40a59890f80a4dc8081210a110900c11, 0x198201828448128a6203005a0324a2e10605214e66a00000cea4892d619861a1004210918df0c70c436a2b99f254825a0100082432508808b18462106d5a00405e8cc1e2a0de20e),
 (0x2812014b01860a4c81116c0833190b1400049480a0091c01128252e0fa8d046066b41240cad40456c24f83183a8684e10a490dc3c0c3f91854c191006855080e0c82e00420e4023, 0x1445ec345c1005334cc603b0cce254c1eb2b43084474027cc004291d0412b1838043e00a110968803d3054c1c518731aa1b2021c212c04a10b0c047e0420a600421118b88211550),
 (0x3476d070854d24913048c400162a16482f34028802c228a51b0125f850698b8113020690d239002c8b150105dca04415a209031d1a6e101010b98000ce02109520050000af10005, 0x209210a6ab2124847170b15e80100a4c04981537511870840a6020186145054e4f978212402ac10648a440022478baa046424e0e001ca676b0664542159454a83c0d40d0007a8a),
 (0x400c0305040420a09c7082065178a085036402c711301bf918e01c2802020010009272089003835c1a3c7ca2ba84194c5548065441c700e658156520fa00a2152044ca2006d8b0, 0x2502708a8b2b4501638514f1aa851278640935102ec8a400460700454164bf83d701817422284022e50380114561c09380b090aab020e501854a1a13040a18608e3b150360224f),
 (0x1001eda99c47a1088429f020616428e40bd3818660153a410972a63069088a86044a287051069013d29129906881fb860245d04334c97de0005231000cc10005f94700199207344, 0xe5e020643b842e4705001831292d302a4282428896885345681414b1200213108a01303a4192b682c644266026c0039352220248130021a56058c31e228e4a802a8478648208a9),
 (0x2c83285060b4990ca50dca49a994946281104c007390097068d262081144a34160c228a585804b922328175fce6c4381a0842970340b04500968a1a441ca11448f0167294058440, 0x115885058f41021200500090044060002ca58027880a7208840889b38e3a1ca0960c875a4865140008866080311384285d58568bc07483a3b20454030635c691303488040d210be),
 (0,0),  (0x3f25c485127c2484190406038ce6019084818098d561006cc82020a910900d9284008106a6ad30025b438619d997520d5ae2c85a40041170c2c146ec2357585d835c170c2166060, 0xc8111860009b1302f3f0dc73191e46693c44610202e912055b5546814e424d623f7c6818128dbd202410e4224800f2241d00209863060d1936a0005c88a2807ca3a8829c9971f),
 (0x180080534dc931a4cce8400141800044004d410102523008303806a40ac80610923ac14c45518635560a1c780ba6603001e014509f10b8698ce25200b0010b8642ae69211c14772, 0x26dc06042000cc081101043c9c039d926432841481084290cb428101a534c08c4005189292245000a90580000051998bec06c1ac600904167205a1ab48b6140188018414c241084),
 (0x14240b5e202630d301cc2a421041011344461032224c08e001466202d184102c47244860af70241a898f1f927d21538888002c81551142d30610ab25048142a8043a151c63650a5, 0x9d810801359c600520185318b081c641208ebcd181051123cb08dad0603a18330da30171083d3655660406800188c752398932220049d28984e409a8b04a1142b04a0421c9a812),
 (0x26103625021930c1010d020099b949c4b231802283c8e2006f4c3f272c6ac340935289070f05001048c38801444c11112080662047040c560f629140145699cfea221050a49850, 0x912a401a1d42c02cb2d221060240203b41cc699d203715db900080c001840c24440424a0f0faccea072c71c803304a68042d80c9b088322900194e3ca9a92610008c07af194689),
 (0x30040188a4164a0850982986a02a9001a20415950d42d710a01444030646b04a0007c4089156d46d51090141b80a00a05092a038009503484002e99d611038fc20218540102f2e1, 0x9331e01188904e72900103849d041a0418a8000c02820881643b2f89890051116583b000ea120000460509240c5c40da0455404d420a83631c502600cc1c002cdcc0a186b40d10),
 (0x1c841063cc042609001732c411c24050e016fdd001b72c64408882a00011f842932a9b659c803035048bb0da0c431080e10806d4287003c8496491298004000012c8a0940075050, 0x2ae494302198340fe8c00026352fa717a900042208d3099274540b58c2040c28d16088210d8bca5b304401823ca42e1c72500ac38f2434140166c002614c3385205a0b050a50f),
 (0x22a90c10012230140d65c1005c2046d4d91504021d0c420858180a4606580208414a4633221a02e314c3079a58246059a0103000239235578593a2108ac6053837492620a401127, 0x1810336862854bc0d21a100422db300220689970c2122533872080885081213396b0a0c84cc4cd10233c300081130f864f4283679c050a80626c512424084a4440b440424242008),
 (0x895844490c7343b50b8c03558563d088600230470404910009801013943a3148080d31e00131b24801a06902a0e67adbc623002608ca60224c8561c42883c204d1ed2820409004, 0x354063996a300ac4a6413c0aa029c04200654c908396b4eed627dc96461c5c20023f08c08c60809a5ce5802780f010104319caa90e0259781911a9038817029a22c121589142421),
 (0x2f568d219bc0ca0081c018c500dc0b474302017008514533d6b12d9f7077514640e078003cd9220172495cb0ce220e40040242744c6ea2040102b3834308c001ba6715865d34900, 0x892088200530df12272112082370a83c55c00140a6aac0090a12000f808e01801600a34320140e0914a34d211c401a5a58200302111d90a6880c1838060dd04598c8480248043),
 (0,0),  (0x31149ec4a3a04908401a213000cac8a022204600019118881c6045134147b304583000292044401447c0fa181c0991a14b12a42f2a9024221420252a22d15e068d410866480ca0, 0xc8ca61225c5d96232c815881d13137024913b068f0428476619280e82c3844f2848931d695a395410820048022524046b4cc48809146c9490806d2854c2681614218709801e25c),
 (0x2c4aa500a21311025118355160d00dcb929a18164600c042c516160f1084230200b2454108b8946c0068495091110420805824e8a60536002de04b41904170b5534850246d90d8, 0x392210a40586ceebda0e600089a2360344101c5601055331d306988c081309c7172040a8c26026b828e94922d4e62facb47818b174010c8c4500e308e45340c0208300b1a100c02),
 (0x1004a3710c2262080330b0e91294252000e8c39ea2084a51ea9e538602541016cd54d2f59249400da000000b383a3dcc24100d3a4298910562194186f4151020400a2669720006a, 0x259b000ee2410967900d4106e829021f1b0004400002800611408410c4030fe802880902082033104398f620c48542225808100531616c181182b0090ba26d042d70099489da911),
 (0x869213ac14d7711660a0000480a24100084642a11400341300940a4f0100af604830205a4828920a704a008001b22080f0840408340300105ce5310c7054053c42d041897e8485, 0x371416041a92004808418c243525586ea730034480ae608c0470105204c94501ba28b9a01818401500821d3146a41591701401856088ce3a58200c2f208a97081a1242014013130),
 (0x8985103b4060446000669487c590ea7414012238c8988a0812a080024462800d87374e5887d83a0704028214691a9a440277724691be0054194d8d40429061104909148f74506a, 0x4270c3c4b08f8a8882100b50120301808a2a998037601417c459621c3809543270c81083100204e811e5052b046544b39c888c31200068a96412408e94680cae906041600b8084),
 (0x10322ee6740584d2ae0c290d09156c0318ea96012b3738930009d0c0003421d1931020c030ca008890e4500c2219816061bd619142d05991a646a07129832ba7160101cd0260020, 0xc1511989e0210d51228270924890c8640120c4d4c80620f7200b24fa81d02e2c65c83d4c319d33280a27f1ddc06c868c001464ad0e8468102901089258c008c1fed4204514f86),
 (0x4450630800093006a6002905390a100a20124f23247260441c014070b8c4501c57058855300015b041084a05a0643c51b0153801000c0b04a2a49ebf830228d031496921085108, 0x330af08b00274c9a8094204b884b1e474078c8044db08950a01149e04050b2ba188523488073600449cd32548521b030c4f2a42604713b0c8184261005450010bc8848256b08a23),
 (0x28c55b002a803900849c6092964e6be4027008d215811ca02695d72b52202682038a4263528a1931df598f50db022c9254098400990130ed014484fa2181082e203218252814980, 0x418a0c30544401f08420100682090128c8a2029ca106002912208c4a500d11df46401802c71a04c2086508300fc1244aad06bbd60b48110a4a260008a4ac5818205e510050166e),
 (0x2afa09ee040c8506454311371892a0b118d0cc6ca2013c1cce0064a11080a968160d602c7c080c3200507158690122050301905a116329c5123a0102f145ada462cb83154003a76, 0x40142114a626aa8121444c800654d40640d1210143a4222309d105ecc044007a16200c082e2710dd18f04a000e88028f0f40505e01cd61269848aa8089a5202901420803008501)],
  #[
 (0x806a88a40908420a02621461a484d3020d615450068e842d4011243b0189c00e0d12eb20141c8010b4b980500104d11438d5110b08a206211be0805d2a820caf60087052831180, 0x33c95334866d33db0b518e110191a000cc09c298419012b522f68d180cc161a605064101b49a2780b0b4447a7b89a248245000e04401db946a01728a0406d10408f20808d24225f),
 (0x6061c00040c4031a0064a00b15421058090218ba112e916404ab0a5d3801adda0548a68813928a20f88271daa28a71222630b05a15088934c3c20600400a2a18628603c82201a, 0x1986060761021940e5059b4b80a028a4a252454105ac00441aba5094a0414c4225a0b14917882814050015840115100e10010143800831428300005070117154819800881559820),
 (0x1e02509a024e2251620d054308b0122cc8c48daa4c05d5a022a601c2d0502158300d48003011e40c02207463022082b3923d4584648e6061768ca89ce0620079e44989509614511, 0x20e4a8250190dc8c1902c090f2088cd33400020123f8201f59090a04060dd4a045323371860000b11c0901804950584c498020210341021e0122142312150a0212b07486084100e),
 (0x240810d144801080210c8804b35d0063c61322b8488a8410001b05e15610041864020869a1aa49060c600991a011a82d0584410040c7180401a1e0efc6230332d0520534037214, 0x19397252c805dce4680d2035a0422f604192000069341790adba4b810884342a29974548058512689c1854600094206d0881036338b006613060c0b00295cd0cc2525680a9c05c3),
 (0x8484190343092c6c6146c146469184a82262a11808a05112a112430c59c7360a0d690b4250185115720c0e00191453d0203c9428804af400b6813222e04480c685d14b9a125aea, 0x259614038880083038a210a08010c0150159548607305804908853ce2261008a1d0127491af432cc8094301ebe0e0000ec1802894213401c349428c4815323028582c9405012514),
 (0x2244d8adc81d3dcb6c181003303c0540a06c686108a081005dad380045d62b602370c732001014bca40c356b84052000ec03c890206d5b78a0135c29830c0aa08e34d00980c546c, 0x1cb1251002e2820082822d90cec2b8b95690009e401c248d2050412db029c001408230c87d0fcb401321480013a2806411b431234590a0005da4a2407891f45b110229502838292),
 (0,0),  (0xd2028d0bce6a803102a8404d5862044647a010d4a0b140268d36c0af1b4a0008a082e24651210a04989606418aa810204608262c19322a01610b64c011ad2800040a4217681093, 0x3092d202411144544690008128318a9298859a322484085994088321084841e1119311c28a08e44394100883a3104439ba11218900289d51c1c20181b2c4055381015196087ad44),
 (0x31bc11b090c2c0c02519544e2005724462eb10940a4288464419c64400a50a1069a32692836cfd8801025ab9046818043012420aa0881710402bca10e05838e828250c200827808, 0xe412e0b6e343d2d80448b21018084318004614ac43c57a1ba66119b515831050050880558030250de0c2544029661a3878194f40317e083241410ec16264212d1d07245f240042),
 (0x10761d81165084131248e9d5aa8014a650c00170f44330804c00424c85a902101154342d0a886097198f113040d5288510911218762286d009ec2a06a06d9a060b0003253ea112b, 0xd886060218a110ce03310204566aa48071a8e8f03340b3a01af00b32a50916d22a2c1d0d5529a08e030c289ae02d772e74e8c45885c6927821304394d12448134fbecd001164c0),
 (0x4306a04b9391b2213368144028080324052d292129d000240c621907c9c96541c2c32f129cb7430800542207042a00af9d28191cc649c451443f1860138c4048a22d8096405a22, 0x3940857002c6a01d40c8201090354c0c24240425092271cc3a3112460021088b43410102d00481853a2a1cc309284f95000c7c0e110003b828240c311e0503087104018413fa149),
 (0xbc02276561a00a65b822f672a5080dcd2dd000073ca14da200806004e1468292300142980b0c3401918281882e481ebc1081a10409e849298e2f5156123088504d0f88240c480, 0xd027c081204181092004c098c48961032800ce9c0815880450e499fe9020909248d6231612482088e6e6908478197410089321270d417a486718008800cc201a7a2602003c007a),
 (0x3b88f2010d2c29b11d0ba83878a40001001c04135344f7fd4104864a43f1440650619055401086c064f0d55888752445090c388140632c60c1ada7611950a050003030a026e8b12, 0x6504522251004a80f04105844027282de360000091080010b271918800b958011e678036ad710b010a2203548a0320e661027a0a0cc08d0c101010e42714025a4e8819d11606d),
 (0x210c40c40727825a22c16d06c4b676ce08083000525884022466800071fe9c843312a110480007409101005064002ba818c1050f40505043a3f0a420100a2111b713bc9a3608bf3, 0xca1023b209848a4152492200b488000b4d5cde008233219cb9107db020041104c490806b77188b9221efe220268d4100500ca0031a8ab84540a5a9ba484dc6c406401450190408),
 (0xcc24032286623904e306f82085e05e9940621150d8631f923e4c9036018400040810989250c1a02303a07765c661491fc0005e8548940ad470635968a0c7409e17942d2286e83, 0x1730c83404701142ca048803496a092006af8446802284800140334208f22350cb06a005680e1c1b44b04b08803094b20032ff81609502f121081826974728b020484302540902c),
 (0x52682d0f1504aa44c5f81417d20918c0506298514810902024080aa000000840a4013c4045ea0c34115002c01d15040800801470c07009090440403a021b788c86420ee010c880, 0x20182021028f21512300401c825e6a601048c612407ea67c94843504600a0f61212eac003221182898e2565072248e090cd4ba101080884a0411a168510a40061591c9011a23771),
 (0x351a2a220e001820f60168821674b81002048a81a8155690da4345864600101180dc223e0980b887945454110248006a52403250222501b418988002265f2241210c40f110a460a, 0x8c1958d018f271700101565e9830046c009753e1042094c051898212144a7e6732081811612015002a8a184a085e0018dba8806d9084603e46319e14000d1b84ea29702e70b0d1),
 (0x100bc8d20044bc9116527c408864410210368324d8994e07cc8816e814336000810a1c503c46084a02ba80d9a594f900280074800176f43930841c3f009020414e98a1a0ccb642a, 0x2da0110471310108482d022c7308384dc34158900500b1f0223080044944976f646160ad8300642400413420526106bb966383160a880344ca738040890c5008a1275c1c12082d0),
 (0x1500b014b48b0222249ad0808692ee4093c27abd1a8296890e72189042904e810080912a43a07910881896000694e489f8c85986043b435871348c84bd6b3608110a3a461504e08, 0xaa46e2083064085a402567412d01b44c300100610d09502109a46a10260006f26a4080b013822b238248bf79401942002302016280a0a1800173530294491006914591ea281b2),
 (0,0),  (0x142b8001006c0c8304064d00172d340c4b3542e8668b60a0a4e3361242e118c02f1902e62707440500187044201408289d486221a2559d4fa5237022004c9a979243081446a5410, 0x344328042830348d8f9b2c50002403390000c071944994f49180025a00e652bd062041000b0097ace608d8b96caf28340b20c0a500820305a0c86d43191412860b057c29840329),
 (0x114b4918f03901ed0809c401081c296208e441658b201a4544afd00d58c5260ac012f9432011222000133230407318900d80a68ac030c02c068182cca9858482069294312840661, 0x28a0144007c09602214422c056605001f30a1400605d8412a3100a502128d1f00dec04b49cea4199eea448813c88234a006511310b4b1d816066640056126b2418644146d138004),
 (0xc0a28aac410cb1b1401843231c42002484e041404e20a04159ac6606018117b8413c2c4208612041048124e6ec17755140582008c0c4002031aae92321821c6c280140512fb11a, 0x3a1145539441040099a6b44cc0a920da720c229a31555932840310a07434880734c2938023104b30c13489080328082808865ad301298f40821102549a7983034104a22c0048e4),
 (0xc0000e2090bf3038a341a08843c5a84470b03af61d90005583981530411a02080609d021658084cb004101822981040729002426924a5104832218005928e5001652ea0014d203, 0x222ce30092400430150285842202814120b0a4400a24a86286004620898e12877906422d00a1973206e9aa20556280b50429d58c025a528e348cc8043865000b1e90d117f290954),
 (0x3d1c0054c802f1cb002360618401083820812343011b920d2a301819443091981014008914c002152c20006b90016e01360a98f7a8540e0e958d44218a494100000342924914440, 0x62730036f10c2048d09188525050c38b2c5414f8c001100446a6a0a3024806a1891352ea2560a25356ec9441fc118c48100400168a219020521282740280579a74b16c964199b),
 (0x23c43a8f458240006034c2c54040cba8861d211421444a8179632254f126b9b84aac44ac11070264821a10012f408881878e4548058e2283502001626cc5901614604114a10a402, 0x39c1509a4419d305480d08a08210442102da0a5cb3b45a841c5c0a0009464225520041c0789d020961ec12501451021800aa3332614c74211f560d912008292393802a50710c1),
 (0x20404c3ca30e0a82752d30502da9a7024804c50182d60511053226328801e8140b897404952a07844aba018d089d0442028507e8d0ba1a9248e2087d21382ea48cd811038920071, 0x1c1cb24000d0810088d28d85401050b184912ac4540188ea62c801cc75ec15ca741089300245b87831458212e522b0a81c68b01624056504b5156380ccc15059532048986011388),
 (0x20448c068981a29c582bb0108815d4a9242f29f1af61e208ec087a48045429908024e204b1c8a87009900120e458ca868e2108b488928c90360124a7c6520880a0c106b1a2e0820, 0x179313513012102183c002a51288231042d0c40e400e0c70030604b02208c4266158102244135006b0408c9808a500493150d20824081261c95a4a08182441560d12094455113d8),
 (0x465d132428daf926d0070126101a0b130b2000510d3bd26de00408e0aaa44b04ac4f36808aca257275906920237280250480446420800f97211cc2191c06b038d463287108109e, 0x12980a4c8442104880b80380004210068504f5922b00404820a40060c045aa4fa1180c94c40000200082b001240093ad833300889983ae040d8c31d2663480dc7231c168c27a140),
 (0x8844a282caca82a2aa343418c132026303809a6aa2101e082023439f41108d552244968280373841698046808028960a488e0282506039212208604184c258000822321820239, 0x2f269915742010594c05ca83c03a0c6484ec0a00915c4780b6cb5484202a0542a881826158794806280672906910866064a410e910a89e801444160d2e433d216e40518ca056002),
 (0x267591ebd86a20228221082e904cd124742f000111a3685021c0a0c803a7802471012a102b4380d00bc1a7ac09c3891a4c664241e24400b28e60e365610c330802b711498182b41, 0x118a2800260090101c5ac54168302c9903c02f7c640c172b5e034812fc1026988a62c0a4d4006b0554001842c61446a5811929300d087e4d4010189a161288f1d408448456540a2),
 (0x12486044408af010181cf9a406b211394a8c3009860024424b52c1152291c8811c774012090ccfca02abc40c9d02e16038623910c2a526022943241de06c4d48dc591640468c404, 0x20018e0a1a5006c5c0e102005905e0c23523ca6638fdd099800422885048214c030800a5f2e31024a05013b3404c1e184785c4623458d04d0430c1601081b0b50126e1a08902bd2)],
  #[
 (0x1f421040a006e1442c2e98ab520a310502c10bb85b80e3c010c651188c28a12004806a12204a40306900841011c8039350437e23225020120c2d88406002485543040260603204b, 0xbd25ba5fe10a00c351260429d0c030cc02c005a006040a22100e6132461e85aa7800ec1500b6c790d771ac24008c640c94809c18a1560c2242133a8ea0808a98db64191485b94),
 (0x1a80860572824a040a8c07b20452c1550b9004ebc1244001d8218000017201455149f300d507240402c8100584804ab0d00d203500920434bc40ac80821b7501a0912490d001255, 0x146700a81640562f5239849d0211282102e0b000a0193be235e0a47ac8c783aa824005e02b859b9341128d21374310e26f24a42ba205bcb02bf531b684488045246926c0414822),
 (0x1405494f138305ab34728100099903833c11424347440241b5a00cc8128c00963452002130a02315b525348b5c3202280a6951fc252306a59b48b344ce6100234891616402bfd00, 0x2b601290cc08721002055658b660303c418ab410a009ed904a09d00301304d49408df840021ec06a0812022083c4dd16a1922a0398dc181a440140032182104c0020120a150001c),
 (0x10109380058f60284249604a7791204020fa45ca653c445865404354dd494804e946812430060868f14b21602b1a6c2e8008486aa80a419002c84131c8a0081206d262603c29a65, 0x9cf2c24e2400310ac868b91884c48ac1f04921590c29b219800a8212286118112814ed94608f0010010441c00459390346222815040bc0cd4013e422657c541e92d0882c106192),
 (0,0),  (0x8458910425023480c027c1798862006202147d11502c4ec120b94172ca01cb001f689361454a9046f28b0b4809ac03760011814549600a1157655104220b1b1a0a14854c8d6c2, 0x295b0740428a988b682ed82e0663917190c42800a22cd110365442088934b0240a80826c9cba010e8905245481a4138c8106680200148bc564881a28339064a0a58149321200934),
 (0x2000f3840001020820382201842471d2f624612c583248b9344782908c14c74cf104c850888412d5d056106a93929c0800e98051ca00d8a7e88200ad148645000e055708f08090e, 0x1a6d043188ac19678fc2042e6b51060501809e1087893300c098346b30ea28830882330d3750690a0b21a79168044357cb00548a24cb2348134da102691090931142281400396f1),
 (0x108004c0942261056c38c88cd46894281023c368040c92383200470409e80508084540840aa36483616e7849890e026b120580198b431ad88380be82f54c41166948198ac2000ef, 0xa250b3e620d84fa90411710229208470a44309400302d8101651862f2167a14d720ab1ad5000848169007920080fd006050664634982127205e002d08939ca980b1e64521b9000),
 (0x176c0009300db91000a1680712190c244003618065ce95510d0217cb130a4e4504116103054641aa42680171528009e02c0295a608d297481906f963d250f3fa00a45768a050032, 0x28004732029242a6ca4e8528c866e0481fdc942d1031420e707cc030e8d4802259221c683ab12e45050712020d3a161bc2b06259852140872281008000aa0001f313a01055294cd),
 (0x2a97096344e441b80068678221dd7021324006440b011842e1201210aa6100201800e1a9d2c8007c0178a0403b4178837f283e5c108ea0f1886148148842ef4940304f284118788, 0x148269808181443cd0010084e00075c450e9039e41805b80c1c6c4c501aa6986267005620132802ca80552a408e03708004410286511c086308250b77990030a4cbb012a881871),
 (0xa909e9610219a680101420c110d2082f9384ca8884414ce9c2650b064f0f025203ed0142c8910c010a096800a008027131806ad0006f1656e12220804e59391ec93033801841f, 0x3616f2020c5c24113cc3c2dc1a41082550080a35360a0c121425022499b0f0a5a11c02faa825023388957695991ab18108882c8103171088a900d50c6b002000c03608c80866860),
 (0x59230bc02084140618900cc8861d12043006030138521349122648002a27464c0e68e55810d88c3e6a38002001b88d011080083491d2c530201ce3404b1022815110c0088e0470, 0x222c0e43803636081a209811469a00d42c3f028fa42a8442660c804309000910230020a034927530115056c8fbe0142342205618b2c0d38489c410803904ec10226262d25200188),
 (0x150c1a059404c012030e1e8928cc021e42c7860892030041821001a135b040a0694440b15493d4510b04b0d86c2a1001761060c065eb3e5940614803b00760c6912202b4f062824, 0x28f20502232337c928f1205216318c40853831c241f4b11e7d427a1aca0b0908829a384ea82c01a6c4304800019063fa886a830018108106bf9aa7b849d01b392645c8430e10759),
 (0x83e10444401a43da301cd441501521c1c2401058610832e216caac30449c8955a42ca09ed888e5aac301003058c8100b02682198b0bd35671b05463b72007001e45215649f0db2, 0x24810b908a9c41820c0400b8e27aac43a0d0829239e5349196015128538022680530343210105120008068f0aa1272584e51514440902c818c0b2880009f70f101308a009405044),
 (0,0),  (0x6214294218404449488008ae5c2f17b2208065d8814b228a26940007135220832b152141218090caa5422390022201065012418a16439ea9228081002ba008d10c203198b6a554, 0x980a021887a339248456a41122402005135c00011c800410010956c8ac8dd974902a06a6440249340219582e0dc15a612dac3225a8a44044c05572c84058b400c384cc04485aa9),
 (0x68694850ed40020ae441348808060602019a4e9003a80300e28a2b12034e25d89a7501164944018932a823120b0078914060147041d7ec2080867220eb148228503e8420aa44, 0x13311002707021034700338ca0407f9387c5a412126c80134f2153010ec4881c0270408f4292423cc5045105c48907d04008004a2810e28015a4b500d9e146111178cc153434032),
 (0x1a1184c852d37745d4e2502328965994dbd2864492a812583441a3680356c09c018299448007c9a8604681a89283140361454192fb61d4e931440264ca8008271c27020e689c01a, 0x5ca3313a1208882281d231cc700a409000139030d5280a3009850934c890d40987c6682660006130f38164120006bd082023a28049000064088359331060008a34870900043845),
 (0x45822160094c21444822014288082080a247610c941640a38a02c94101a82c45202203c5506e00c9304096820ca0840c646c3471226820c2c942495108f8d94a0550ac0d092a02, 0x30235560906009e382304d8a41486c33d4c3006102921834835c4001e1e0010924800f022a91145244a00403c124262e0029183845d94c33d0410b084570104b052250062c49581),
 (0x3a41e190142cfe0013308003800e3257426c00d6ee9ca032f06042686200abc954022011383d04a8340301c30d0e1901823a0f228a88c868a102c58c903024b98e01c01461bb648, 0x2000aa1c201f2008b161850704528a411250110220a040c9609069dd750300804c90083c28106c898b800c070e002600180d1742503031aa82860450dd84061b21aa80e40817),
 (0xf1c0485810b0522c3043e809122ec9088c3ca67c289c0967acfa50e11b8001457019411c200ad210640207922a0f489033702ea88a985dd0400d91ccd5010600428c78e44dca8d, 0x100378705ee462c124f380362a54014f10002188387412400400100148031969281223463c2b10d0d0334184881d091490000c0505004822b8f122022281849370d300219b22060),
 (0x36bf6320a92ded27c14d0391000490821bc6a690719d44a0aa2b0cc241c162cc0121661b800444302120490171a4008409a06d84530990484a52aca92410900c14511a348480281, 0x8409cc70612128038b0042e1ae30975a028580e0e028b4d5004c12d9a0e0830d44a18a41903214acc43362808112c73641a0279a8664d1725054110d0442f02632ac1c97813810),
 (0x21c88d9b08c0a1118441200b09a445ed0324006003234930a09909024a041245400806989a650d3df00a810a25a021805012e6d25420c410b2412e4b800d1a40090106511280c3, 0x282101004e33856c233325cc4864b281298184c9d50cca2ce030482f9342928829d644922250212c00060789498484429a549082429c2002e0d0040043b7285a532c8c884e04014),
 (0xc104460b60b2580916a244f4a74644a2438c5211443888a6f512305480136826911c823021a24d1cecc3d8438024a0059e041d4669be9724574e010a3840126cc85110a0f49b2, 0x2b364a00c00500a69421440908008081083452a02c120700500821c0002be8954962626c46880032c20108271869081caa0050e011820008c9a0910ca1800200911220c35402241),
 (0x1628058280c0846948d8066089f0a4a1c20e0e808a6992f51716b320ce23e689a5250aac6668e111f801852c524600311cd0800084ccdf614682461881c3c120a8009fe1223128, 0x6940fa1036187b809020300e0004431a2040a10360046d0840694805314008720a1ab102001012ea07b25a108188b582e02e692d58030000b85cb1c7103c3649435a4000c54206),
 (0x22111870b619344a40af0a6631eb10933048ca9880280122719243d92a8349398ae0310111e81221da3298482103543860d1c94816c089095534300c62301782044838e85624185, 0x15e4a70e488081a40d4064884614802443a62167050604d80e209c0004780640200bc6e42800280e21cd47b0908ca1060a203237e90c2052224aca519009882c6100c111a808e2a),
 (0x3a199c8dc181503d10813a02e80a80018c0a0618589864490822998468b4a494e001980b9a9868081187801684a038ec210800aac40d40cd47ea498420270241145101c83675301, 0x50040220076a742a3580151040514ba013488858364191070494428060b024004f067f424060120ea405261705b8401d8f1a8411212310238041020c6c8551a898ea4050000c72),
 (0x88824898a0121914a01cee022d94f55884a2500d0c20214a0f8d25a500933032a6638d3948449001cc14910630519543936845a06a289c045a40b04043051005061a3038a8226a, 0x2137c242004ec66cb0780001150010a823b11806251885c81e0004a005b64cbcd481c32c086814d6e224348890b22400c0412321310050203019606af9020a990a805878053c911),
 (0x300cc1209196f40a0541c28a15104800685568685a1b30c88a3011510882a002218e24046039919c80a69320a08226444029f94700219a3c3c21c80100c50930224c9201b4b4409, 0xa01cd246610954a8b20c45404a81258728919421a4033065c8442e314848c19a1191299f446060795844890e5110bb96d0029074926440408a1290dd02d20999b20172400ab24),
 (0x12212d5300225a0c8b4c9aa138416c842d74b43e01d0139c70002140c0c69a00a0d022a481608e92ac1b2d88f3182501e1cc0566908014001e431a13229100c0953751f3230806, 0x144d8c024ef5405a060b0051e46b2907002000300ce2b846203145a2d110045db530291101c1661485024507008070a20000292912042217ae19424c45d66bb0308080008902150),
 (0x3e45b352116916135c0184ec001625436510050e6ac0e0390445a0aa05fe141a4207074e083180660e15011878a04a625598345407630020501c36ec467450854c7f02c88188a42, 0x380c8c600448a883604b02df4180a8128fcac1901c0700498a0f40a8004a652d68a020b0c80e00d08830a483008518a206c38a188c680fa0828910110a0e22a3804113043700c),
 (0xb00270000028e2a082813b4029048048c458d13087e03089f43630974d1a20131981f019302485108502d00038cc03c00551042100100209cb00dcec59209012742d1c81820020, 0x300910b6e394015506c66449a804207063a24068c280d000208c88f408264c960e65801e60843222108040dbcc220d420600ee98aee6f01321460030026cf494088d0014228ec0b)],
  #[
 (0,0),  (0x339e28867855c60df6ae09000542e81b24909020c00ce17440664111004c011504c1882a6c3d9249290a48086029b1605f80d9a0704a45008854154f0014168c192830c6a1012a4, 0x219051040221800140d0da401d01a0026d668a0e0100893091840eab0326e0893011000282410456b430178f500c008045061d8cb0024657034a00e2cb881384d1c82044b4840),
 (0x1403870191a1180b0510d05144050a20e08e3c0750612b72d3248835e5e661c213900109a80b80002030538488c1d400e24408fc2b455c99116840490b983068a021990853a0d00, 0x99078a860044094f862268e99f845dc0f6102680d8210092c8b25021a100415ec6eea8605c04bb4828ca80b432428a1180bd600500a0326ea813a92a46546875a522446804c2c2),
 (0x110895038c108b2421034a20211340706729841119602b918c0320021107335c940292688601439575836892a0ae8554143a4485dad800d0a4013014d315040c04500a118008fa, 0x1a4320060714d3081da4434138844230f08465960629b040e13d4cf99c478cca368484506310020608810122d1d01308aeb4401502025ba01021e4843086ab1928a82252a10a504),
 (0xb51474cc28d5e9c0fea409548e8ed8809b209b2930100a82cbb200814080a08916b7bc218e104491209ab8e85081808c2a0d9d9030488898911404d6bf1108402c12166018b834, 0x102c18820432a12090143d68a11610013609760824beeb1010400777c3e120c40010043941047aa2c4c2501062c7e3163c412420a0cb451200e0a6a294000b115832cc193e40508),
 (0x15e08b21b8d746a83a0500131160000020921a02c8f60002404622a51dd1080300c0d2464418832000ea89c6932381a800d880e2976087bc03eb581a48c00000a6151c140783420, 0x2811008806008046c5504da4460f9ce3c50c402914089c2423988810e2024494193a09900882544745052409480464554a06191c40063043e8142744070160730982402af8648c9),
 (0x23680c5e40c1be98100808a403673c0d7c001d4c00e04821031898fa176601dca2647a84b42b690020e5419da751991c104089e519689512106200490704a84ca1565143a3c06, 0x2d08934320b41c0105e160e21a8c804262027260a11f0d93d02c64000400194c02081a847b0840849582181a40188444c2a18226086611682c84912024a0e2071014882c14042b9),
 (0x341b2120300961409ac4a449348f41412c86d408601406cc503f0d094c644697c4932208087c12804202c085028045232c1220472060008852b085f9217c60c20104400b128042b, 0x1840ed044e60c0001211382006004aa936123f48261b9318a409070b10b98282128c577e380e15abd3d3e5a453108185229d030d290d2322d4152068480943d46402fa0ac441c4),
 (0x407d2dd1f180ed01007e0d05408e20990453c6004de9510552043c004843250008316080a0e052b1c1a094b5a83757098425082544980a039488949358574c8530214a60893c8, 0x328980d0220e4512621000f2d2214197044804218c2006ae3201390378379cc2c3734490770a0108022a5922424088a8447a88b25a2247b1282b152a4ca6a893404cc2810e72c31),
 (0x2dc801a48f604a612181309c82060a9cd009602a81a64f044946450095c541d015d2ee0cd084e018158c1a3286840470a068306468638e40c56a01a2a2a0cda49cc490cad45c50e, 0x10239a5a3005151ace664d222c1995432c3080c43409a0e082a8124b6a122c01e80411c002410907405204886971ab091e950018119020832a01ae1c004c321b410027042102870),
 (0x184420436241278e918985280424d804680648709200e81a30022210c1a12001307aa80384db951501ac309a42101e0100847906c41829cb9296023606024db5440488905cd2109, 0x780de3889a450502a160a9118c822828509b2810529060545b10de1125e91a082840504082462e8f2510965a4690186f5588038182310306828dc09a808b200a23042062101642),
 (0,0),  (0x24630c1d37b34016700d0520949889508268199d140bc0709c01bf1b0c1aa33e8300228b60c40881002cdca0226c001800c100090e810a1002fab6422000903cb0314000d78330, 0x499431c0080809c80210488d6323462105040402ab14118f22640004c3040c81749788000a01713a28d2225c010078c625322262c144b10ddc0448100e31080202429d6a083487),
 (0x15ca10026580a74e27aa02013408a0556e000ef32d6d11b32028128c011859ab031c1801078a0088168820d3d0ad82480a3fc80462005a415828864c800cca400c012e2089a8cca, 0x2a346bbd025c40a14051c0ae83645b8a80fa900c10906e4c58802c10ea01a2504042457af801d5436837da2c21525896c4c00492898aa432a40061201b8114301236904d3411321),
 (0x244010804482ba4720b441126a23a834404121d70c3180c0a0850802694f17286849580227d93cc0846800040763248bc2268062606c400898064c38801a40803b4d9a82596575, 0x38a852a3b0078019009030c29901003c3123094009286740e1b42c6d10620205512040060c82443130a82c2b3f89c90640548119816118624676181c04ac4ab60c4a04124000a88),
 (0x1440b3051cb1640635802a4205454e99228e07899338021c094608da8010050890138c8416710ec3220040010ec178ac4d60ccc01a654188912bd82c3c0c35298ab5dc03438224d, 0x2bbb481a40000019c81c81845010a0044810d86400c7a4201298a7000e83725662405228200ad0289da52b5a91208143108c201181103062620022c1c260c8542048222c200d502),
 (0x131175f6d2f168280ed2526821c56324420808b1069440010ac16f25424580888a430c0193a5920006ac810a0f053184c70178721010494141121d64b67120389816c2c82003405, 0x288088012c040402e0210504803098088845514cd809a6eee02c90c0a49a662600a8a2c020482d8b381166d1609a4453088680882eae8232aacd0091400c400103283815407ca0a),
 (0x28219d5c23100c4124e0f2c96012a62b5850a16a4a932150950a1800a4e92c4224854856b2a10ae86d4b6c6105880c0428a4c0a4f90b54c000351a3328f12ad4001619058202441, 0x145042021c633394c11d093402ec1154848412859500c0af00a561924a12c2bc0b689709415a201782b48396704670e90752125102948118938a8504910e9420f42942ea7c44b18),
 (0x203148a9038b10581693801700102004afef868e17141245991109676281242820a68890092c2004003dc2b207c89c09aec04a8407104d8d74c245020c4cac8c3c89967f225026f, 0x602950670446e25c8042fe0464e469940102111e0e3a19a248e40988926530258502028d4525498cec030005020400601183012806600300a11027430b31253823061801527d10),
 (0x220c40a814689b89c212241061081008d4230024c7e2cc80e02326050864a100700ca2004ca485020505429d8e805511075127d0118840348870001022143b01b0230584081010, 0x1c962b541480040363d2588ae9882afa500dcf01a180c205405d0c0ca938a04d98aa155c2324050ace2c22900316ca8a49024800c804017017181bbcd1d03c0ee47543023426a4c),
 (0x2204002910285c2604fd8a218d481c200022587201039014115450a6c007081c0901b683144f6102244130668825658206a88802198c4e5b100da50447480f68e3598a0bc895c80, 0x140bff160d4480c1e90270c640830044bdc8850c949c69e04a09854830708142826c4870802008ec1a22c688324a0a1429113439c03391840db25821a0a2b017048451a40268179),
 (0x9202c50873e21518e19c4421c8c001a0a0162a49010400a845243058080c0445208558b880108b04044f1a1a22202e46003000080e5700802c2ca2c0455607c4119325e041608d, 0x9680ad600154a0204208b48263d8c091c2000842e92b5402042c9a207e35292d010234376096080d38060809c91818129027d54a128637f531059019a21f011240c0208aa1430),
 (0x4d0947a021284881da09087a00092022087102183cc6972c1ece10a646460d96de5814315da642e8000c500122c4403a84cfa80080018b1b0208c162b0509019840a8062121, 0x1e2c82a620401e86043625c62400c6000800930e8461421828d06020c00119b8600120204082a0593402d8c284505d2aac05521050df5e6414400c522e80498f2da233f06e996d2),
 (0x10f8224872ca60015c1015d911001c82a595a094011841eb006755051466b45ac18c16085128d90bd04448220940d732f61ccc4667550d2182a7b56c4c0641806e80f8a0304463a, 0x2b034db0891485dc804f4200c48a0231504a1e20346286008f0020d0e001422038134042069326d400929689601c284900631300100070884d40408212b10c2d115a024f829a041),
 (0x2c0da60417528ab2268612840c0000048841041042021b5598234c42100a3040801707209269c863e1900a05119724090c01c04493920ba42000198cc1e0bca48c6222ce29a0953, 0x360410180806544c851a440e1f89d2b7212b84d1c4d0428220021bd06b4c1a27e88080305100690002494c24a6840c4b00a038928004040d595847018014018610cd100401a288),
 (0x30c37a24228b955c8a025572444500c60a09281f5428010f461216fcc21053081d30501cd8a2202300154004e91ac4046808efc95a8c446b6e28623965028e8920823c880a20f55, 0x21884538120280270fd0204bb128028149012c0a944b8b02841010100832ca3404ea6a32449db48d2023403020510d883871002a4119914809389449ad561304a0d8267f1180a2),
 (0x5806581040d39f298a11500814b4027a3461ce0630e11d90ba44980052a1860005490ab188001c4110707089ca3410231829103031d0c854c00018ba21510c4961681e2464079, 0x1d2421a7e3b4280096708e8f8781489d04c89230d884184202052867bd8c56015f10a630086364a3b4e10a00742548a914c0c4e4c20226070124d42444862681041282808a89882),
 (0,0),  (0x222815091627900848f402532b112a50a87148403990e8203080c330516802f410d088788a4f759323000912908060a981022c8c609a829869e9d503a94387321905240f2805b11, 0x1302a629d803c6830218a8544cd0824302a31f042a078d836a2cca08001002810a00852110084804ead2c12b7509445071435315655d25940622f816a8180066ea8b3047100a2),
 (0x2463d00952603c938f1c28524a18cf0125c10e1e4a3171c2db46188c1a2442c2006073929c617846008c4c241a0158002d74820032e0f026f4247008f32043396078b858d180b8f, 0xa8c0f92800a412050c24084344400481814c1c111800c310499c10060101c142e04886c019080a89240339be14c800a42014070050005000953841604cc2c06830444a40c60420),
 (0x1241ed0408b6e040001319710e1ade42384801ca500085948022146b4095282a59485700a90020590e306da44809c82172086408064c408dc88a1de60184014c14800188288a03a, 0x21b610a10049042378e0c486704020298586401582217a2b4b0961948d20d24586b3881742d384a2a1c39252b38223ce8db31ac0a11239621514a209ce23ec914a0e6810c371305),
 (0x81b0c40826321a2087810811142d8a6242909310d307278872224a241ce18054c28804a412822682289b08480a0e100152ba20850019cc665409ac00a86c821800e060810f68a0, 0x268031b7040cc45001002e522881274118d0260a20c1808568550b09ba3103e8b1555a909a92148690164828721516300a845d702a466300128825055139245854a1b8126b00148)],
  #[
 (0x2093595cc12076693982d295cd880001a080164a020c0541b1082d0001879054ea80116c40920a281004c4404403c0c808cd40801820a806d391c70402824a44eb40178c0002806, 0x1704222116158916c23025281014d2c61a0aa904ed914a9a0433d2b4ba08210101186a039760245028803b2e0234241701022f6c800c500124661023c119b48804b468200985630),
 (0x81a00a23200d85f188089058241022289301086481403fd005ac81011bc90480aca04a82a7a3e127ee904182c10893f8444a4461081f24a4042222446080c9a65176415e04940, 0x22540454848810100831a243048a8bc4d2443241123e02c026ca1010648024d02a515e9120481c0a98116ea0293e240c0738b59a04d600991a728d4190921614502281a0019b23b),
 (0x16866c481e86b09ca95210ee5c681a0121f68b0036c402d54300864082e20b2122f74040a8c92e74084c2b8c2500385e1c204eacad206a0c5a0e20f01293010840e902b0f76a5d0, 0x214910b201284900040d8e10a285a1728209502601008c08b0084028690c4440c50089a75324c10371a0c0704aae8001225bb053429a15e1a121030da84830710d0454410801a01),
 (0x809305a5be2525500140aa6b5062130ae980048a568a92ee1ad400230e84892aa2413b30800d02a0180d98c6a6d3c06669a55419c854c4a82a50142d961c82a21d0c015d220322, 0x16340f2404102420c0ab515040d8d88e51665600589040011800bff94300830040000c44534f2914786802338592c139994128a6416a31354c02e8310298119402220e282806cd1),
 (0x38d4b75f2000202ce08a91d12e90c72ccaf0c01800379b2a7c6644a99615b10265824f4800d24802c0653960044318840c08fb01207082d0841802404102180a00361ba44191b10, 0x40240a01d021c421b104c02d0483813200d20a2f40840058088a31000204aec8015309365210075081ac40880804300629404f212812c0932e429b53aaca3c19c412058ac40466),
 (0x208e1ce1404b21251d3028000684b9200c90827f8b180a7842b00387002041480c864286627001410650091009075a2050827af8429056480414011a0c501022920bc241aa18456, 0x1e1160062d900cd2e28f954cc87a40db104519004460a4032008c850fe421c9183199d791c8e1c1630024282d0a0240c24248500212789b5790850e422812d082060142841e2a89),
 (0x3900b300000ba08015421100303811d0821233c92082002024e5ec98081e94e691200110259ab6d06022860034448e7230c9a03beb48809a59451d086bf4a8147c8203564c20d8, 0x244bc44318b501a5ea8998e0a0145ca064c45c0305d341c040a100022b00062116a4cf040ca400124878448a382332101cd221e4004b51b6584b88276900a472881607c88b25903),
 (0,0),  (0x3200002af48ea910900034863d1c4c0506a890003101413c2012423c766811518214448289c4740404d790060d06ea0076dd804f3d404e8954000000650ba431c3d371d1c81a826, 0x8ce62850b01020d2954c160826202f8f9550f8a44102a835f601c40800308a65d0882507029889252006788b29004ed8002502002b830522a429c6e00b041403c2c08061560158),
 (0x3865f1576e324991cfd29ccd7cab7d4946c1202a6c044ce09848dc45b11a20b02803633298c691338fc040c4b08220422821276713c12052100c8648531023ea04012895a6a8007, 0x21a0e080044320a3009200203548094392adc85123331064494021044c44349d2a8188527110ac07014bd32070556ad46545088242405888a01499700078c1028fc43081157d98),
 (0x303697100840904103354846065909482091424000315a219a08200694925043b5039486a62ca0caae40089f1360805c4ae8507900c4480a8ab84213004e9b8051085045b00b082, 0x7c108cb32a34e2eb0008138d80670a40b2c8db0298e21c000d40f292b608c3c40f8633959915c0000897360cc9242a00116a400bd0a176044471d64b930643fa4822f024660c14),
 (0x255041a84486620001901218510913101864360010c808c881803b66894300341145e1c8c41291069262180c3000142422201504e12c1247c4690238a0356750a09804528438a4e, 0xa608063b208d61260881428c40e04ae680c9b8043715236c174408368cfd8b0aa8140730e068704891e5718a4648994c45ea9a08108d300094dd834e8200a608032a8c1003500),
 (0x180b4a0831083917284a2c498241430188a548d1d2108818042b4842400360d447118e06c021b0046b730401c18208480c8e1205a024c920515605a2b708709c04408a258200523, 0x3d0a4358a354460c02411a040161856311a012a0c25572593d430a81f301e00080840d01b9401609400b1263a78f213512100f25fd2105d2421a24908170440d18e150a40ea258),
 (0x1552881208325f22a029180414223124016810442032918d0c28020016c55312444220cd41854012d2402810000c351101331984405d8732c192cb141d7124588f04807460000e, 0xc82d320d230d00595254862b234d86cbbc016d0a9804402061946015080224642a294f22823a29a80595066557334aeac800647b062078051a2410c9c00cc321701878090a1200),
 (0x42260319f890568a01328748b14069b0c7201c50012644611281409e84990142865c20a28025004238ec328a253a3c506282c0a085ac6e7a072e801a13d6ab4338402041b170a7, 0x31cd0a80200668875c08c20b54417860f20d9838da2d9a988696c15402160348549234e005dca4395070000408845012f01750d554011000488d06a4124204494029fd28c060818),
 (0x412c45949cd0aa004820c9054a48e30234e1580a3029299b64c507f135298111bcc5114740b88d21c750038701613403065e69a9008360303fae0054d1329600510029808715e, 0x259a801868232311fa84cc26d280970cf9030c25d480500224102ac00242143e864102cc381704020610ab2020288e40ecc18090567f60128f8040ce832c4d61dfa642903818a01),
 (0x2de4143d39ce3420a2901ac8b0d201440ab4ac324020304104324b891063a3d08800543202d0442485011198e67902dac9812199d947a0c44e18020d271968a28456058b424a101, 0x2102a4044000b9e400fe0060908d0a0b40952452002402e8005042641801006435d03c9212502cb58364607000260212076062202184333110331601006141d3280d8108031264),
 (0x26a0a123594c4d8f83c3d00a8cd2c218654b0a440061cc0272c41c4ad0cd441d0e82d0cf7810e1e04c08678552012b48884541000206c2e4b0144122620e4a3c927510411828b8c, 0x115916cc84908030582c0c243001344280300489400e11b4052a62012d220aa2715d213003aa16051050905a21dc4493442090fb444119000229b2050dc024832108eb9c8603053),
 (0x286108c1281e80343b508061c7a540101f1d0248c09d142b08280a2c8b2f5410cf1006e8049080804bc20c8181a103503106ac83d208203b063662de44144003090002714050280, 0x1516013007c06ac34080578c2802232ce0a09cb23f60c19430c731837400aaa010873904536c1a6a2430c0583200ecaf00e950400d27198051400020182089b456602488b92393d),
 (0x8fc704ecab01c09b47d0319524285910522ac002808135800400da005002b5380008c02201960863e0349097f60a486d8465664086aa064c12c37c329da0860007094040484bb1, 0x5312405e3744182acc621990a22d08112d29752c884ac23325242be448012332025c7c2184881e080940000421125a8288bf5144f083880c034c425c7812e8a2968f831004),
 (0x150752478932042c896d12188008097ba3ad0a32690fe8084e1b94e413e3332ba78068501e7032424889c055502c388101192d25a28202a2b43c219885611688047e0204510514a, 0x2c0253032411011708248c015d066005040b10c008013b4b1a40b1b80048494506816a2a0834c9024421b82298283363062801a4104cc4509031e4052864817c3006d028eb2e25),
 (0x14ac180e2030222d881a00c81060d06802c80380b7ccc3915805c50004263340446c4351bc43c0642a001e5d41180404201800022d8d828b8315e834c2518c0a469540a1250342, 0x3c9122370c0ce844251a48c224b9f21013d26cc5508312c0822003078bbd100232203902a02082e021511200288065918098707240060045030ea14821c0c03a5a80a8740d2988c),
 (0x9cb244c8d071b504f858200b41819c020d65480012560130e28e080eba64315f032a1fec005a010b000b3d4ce4a94bb50841148c6e021202140d6ad72826088c681e2808811174, 0x120498b3022080aba040344943a1a62e10010372725284644107006c1000bc40030540003a284da70072042101840300a763a610291ac0004eb0290001109001093e1c1c01c6a82),
 (0,0),  (0x616682a65b89260304a2d2706824489c8c41440521c208a04040e16500cc2199cc10411c25d4b5b0005025313c083600d50294b1c4311801854414a2d840011080150853b22063, 0x292092c59a034d9a06a55008816dab042723e2a62ca3db0500d9c1200ca02d00021a430e148030204032292024001c9a10861480a19c422981aba4814033532ce5c68438c4c1510),
 (0x32e0104261f0290404040050400aa1284d681201007406d563402602a099298ce11386029740233746310ca501014d61ac0023a1320196401230cc80c421a41038852a00700e551, 0x101083d040ec28159792300baa44e96b28744704708d92a14a6d1f44e46d0510208314d68ad1c003088911a508c809850be104849fa2987c0c52112019c5ae14638c5f48b81a80),
 (0x19a01d400a039b989321923900a103080a003209a0000064c000a4284045020468086080004230232218d08e20fc226d01a382949a06a0716134d648025912b1e0132040181644, 0x3865b800721c0402528d665067318cc17516741701e3a469132bc521113129571076708269b0d81c0c1020410dd0048828404046240891406060a0902e904c9420c208c3ea68923),
 (0x161520028e1514b8c803d402040b258a8816400201413a4894ad1e220288986491148099109098c216393a6661e224053a15aedfb6d00564406014000a83068c20470d9c40c6460, 0x2882808500aae24422940289a8c0401150a013ccc4968100024021c13431429366e32c20240b47088086011194048280c42a0000080602129999627ca544f013d20820403b3899f),
 (0x26685ce52144410a4a9f20911060d83c222051e284a387909ba96b2704280865420009b45006482502f0bc581518b24448e4b10001383ad051ba7f0c3091761198d07c840e1015e, 0x800a00a4ca922d495205c0a2c972081d05988003a08186b0000949050462488103b420823a8a58299080122c0050012260904b1cec3812cae0400f0ca4e0004622c0278a04ba00),
 (0x8c66064042af7c8020035a1a4084011984092cc28aac2808284054144408d83c840002a091c511117083b6ca0c801a80208523720002718094500218205c31008bc002c03a2d6a, 0x23200e19781408264cbe0a5e0a851ce666092d304314117d0829f2203384726c2611cb419241a802c8b1441142328215d53121c8907148c2003851164df0086ac042b5813058004),
 (0x8460208940124e404c92788a79e0a0a4e415d30002dc0d001a5a4010c5b78075e062544cdb4c92919c0c5128848a50044025580914175920469b930f6e0a10a0803b070838992a, 0x1791a10103fcd1106b069025484181213198a0048310242e0c181844232485c800a95892300a1014260c308441a2085283402a6e64800244bb9244c3001708f184f84a8c7c44451),
 (0x1245c22026296635a0129521a004d4346481101454000488407a471c0959417080bd1d21f69049926913839c926200e93cc8aac0b33048219e400012c6041028321b212848a1301, 0x241a00c5c00089884484005a550123c10a5861c003c340533a01a00066043c8973422000000e142506687062498d53024124542200c2a21e40b6e68c1913ed0189c448c4041e858)],
  #[
 (0x12c41230238858a3bc1088ca70da09e0b8905910201026cdc01b10a2002f39260649405a58b40088214307e0480025100d1245ac504054ac111074ae0240726619002aa80ced858, 0x2d038c8ec434870c014b33240921340d4726a08c5027d8323ee4e64d6f9000109814320085483a750680201b345fd887d089b2022234ab520844034028938498628155433112680),
 (0x1c5c400989c0594da031017056041006a04184a4d408a50402642bc900034400d4d20a90300006908c29291e44a1014906020a122131b821a2dc40008ca0468b24208a919480, 0x10242a18ed6443d24921ec4f809a9338480452c1948005148398d90941447843a7a0008f4068625996340c696612b1244362024e145864840864920ba3f02189850cb4b04660329),
 (0x244b010120e910259cc1b01f130cdb5b85eda4008828800880405425b9874007200304a5d2c5005a083191cc820002b9a94ed9648938c1a20048a5364816e01660c6a20528e003, 0x21ba02c12d902a788632e0f2060a104243202130d50d53da62dbda29244488ec89734b0100d08f385d0406a0331b515060481068844030a48d2b340c016281e089838584a8607dc),
 (0,0),  (0xbb0318419a97263c085641950ec430482b0502e8f41ef045a1b68000d521a98480f5748190634070c025008113ab83880067528e57005b1102c82622e202055e00e9f020c528f3, 0x4080a5926060d18237a03622911a85b694c2b8020b8003884c4906d60a4416296f02080a40181a0b0282e2166c0414723e180520089ca00a1430089c00dc62800d020a592a0608),
 (0x33bc415c21190004b790e004fc48c9f13608c120340114d0c49c7415002e00a250321010443f232457ccd06032429d3180451f280d2d21889c205afe20075baf70448c0dce4402c, 0x4018ca214a63518080710610016260e49601ec5c33ca00d0a6088a89701340902046da113008000a8230c08850d00084a2aa04700409803439e8101d5502000879b32923089a10),
 (0x122850300033102086d05553219418cfe101014050de82cc900a90a14815202421b824da39f2d59e4db3243182ad0002b8e00d02490808e1d01d9232200411c2501108ff99a5903, 0x2c44098ae84ca19e110fa284c809c430004e66818a0121026e502d1cb4c20c90c2468b2104042841b208010c2550610006019215a030561a2b6065809bea42212f025200004203c),
 (0x2214838509110c08041115804d0d0a42371215440178c1e589000705460582210c20dc6bc380044f3c5c2895636d161c8c0e23ab4287380901b0c319600f024c01d5e804629cb2e, 0x10c86c703686b167c140c0470260f521c888c22236822c1a120788f011222d941305200024584800c2818162900040e21080c0500950c206e84d1080021011b39e2a062014220c1),
 (0x6a140d805705cc4cc55021a928009dc5810e10d0a14f40320321944c06120b001a004899144e7d414140068803420545c1c2aca49040451648110b10b189800080018c82028966, 0x115c8c26d284a13a21205cc0294e5020068e1e7201e20b3c8f8000a2028e404b8453d3720ea2080269c81c007b40d0a02222c034209b5a029a7e8148b04000c0b6800106dec6489),
 (0x307a8a40bd70c2427389c4d960345801a18be17208cf400ce618810c3d604020018100153492010c49d91e10009cd7e143080915d0481086058602a6c41083aae0885178115106, 0x20681401642062d24841018229e4226820e401a8dc2202a8211410ab3401526da3250daeaca64e0b0a00261a7a44008149c94e2c20436610830181550318b5454040488814482f1),
 (0x25a0509042a494a0da1011080822400795444690842f2079483d931de10ac25ba241d20641846028605eab3a01250ac91655541d4940064151a8484323420c1a3511e1fc0900014, 0x51242ab9026a1705052ea5050caf5848ba390b5210840083406c0014e50420541e09b00c2399c5178050c1de52a430c9a0a1202084e92a241125141419e34480a01c03c0b5180),
 (0x20608818460040618023154205030a60a28480310831121a020009026214354360148104106504090d0619800f422501cd92a846e41c4007ca286c821154102402d68044c313303, 0x169d60e5b0e2191c7b08023070b0801c403b7dc2f10489c1c1c764bc8d038a2c1540188bee80f1622289c45b7024905c00650390116136380097811162a2275aa9004ab804a4810),
 (0x3ce50400c74b4080807d8428a940000062b021000d04609c01e0c06208a9482d48c00908265710176a40e241054201100c4026c1b140825e02c2168784009808848200400106081, 0x11a48eb0094916368823b454625a8d8154b544110f212229a100595335492802018864398288ba8153519a42299ea43d02fc93e4ca77800a819400808f72570293db51f701122c),
 (0xe5d1050211082ce18458a47c4c4a0d0d4818092049306aa00dae80e59201326428042691403f2a3e2005810600163306d88aa2057500800565961a151f2e20c03400c0474887f4, 0x3080aeaa5e8f05300508342023001c03005c4128406c58109a2413f0004de04188761d96e8980d48199825c6921418488214009da029d4e080a21416ac04101330b0c2b30b76008),
 (0x39c2033582dd8001202057910219027508006826980340e0b04520854a464424390878c5825915315a32a41101a60c0a5d2091d9043802210200794aca04b195306024fa8a5aa09, 0x2598c86d026c200209284231846108a47a07d9622c871305a04f5214b99b500637023a78a46046818459e45c584064224b0e04c887b448f1a982b5356b4e68850c810474a01b2),
 (0x1ba12075a1000010496e4d20f40763844009144013512833219a2df1c00d000028b885dc12841bae04043884e30908db30809440844688e805e4780048c0036404e52ab1030aa20, 0x445a8a0cc29767860012dd02a89c539dc221064c0417440c6592060850d5fec101020305122040ab39002a1404e52482540aa61ba16406f2088266b514a498611a414e1cc450a),
 (0x38c0611df041a04803874808c0d289ba189b28056a12d804e50890e110ac06aa40b010a35a24018304414940c3068cda10c9a2948401142231450e2828651008085c31179e45240, 0x33706c20d0a4d07a07800a213006444a5405308946427e20a814704cf0300053e0ee51480d30054e280962138006001eb044101193aab0c88b2b104d700c6d505a1ca88602818a),
 (0x2e848131c318431326428a4142309d28141da12072c205190221d24f0c00e0784041151f03200557c47230b9b8c328d0c01d48dcb8442091518400849b848401804d313a4605802, 0x115378420c66a86c998415bab18f22c62b220e170d05fa80f0882500f14503068c266a00541b1288300005424130d02e304023004013d0288078864a2060330c7a22ca4019322cd),
 (0x293245521b5085a1e6922a282849099aa918631222531060e21502528203e32101034a228004aeb465809c029b848817d1af3152399c0c5220a82004c327d07895067c8c40aa20, 0x2508108a4c4af48540828d446d726d02040c10049052c6b1f14ca64217c50184c78f420d803a301018a0c61b8043b16082c40c0a50240018099445a4828c0030700310012b45158),
 (0x14225061345c000019988918050200344894d000e6d980aab86200ee4812f04403a0208a82d8804b000e07122644a3fc08c4242e0118a9a9d1220e5090d684230011cff85f9e23, 0x3cd0e944aa33b3120621206a05579cba7030a7e10226c45468d3d1113ed0592d44c110571065c206e80f885d19a4c03e619c1d15206101422d0b00509286a50aa00000400218c),
 (0,0),  (0x2f0c920c3000008306121aa865e320006144aa2a00808520426b4a9c10d0b601aecb00770204348820edfe00b17dc08da8ac28450a8480872c94925413b2f2101820014ac281289, 0x53287247b6651868c82545181803989c305400cd3e3acf889401406801411611204708e452cb12981001ca0c803a704301c08231105620426b20a100090c61031f5a21181e016),
 (0x1910660a912de4dc780270b1b20510021422a56e18b4189014312a9d1fa8304554ce767084611525104a22022521c966c00400412043960a8808273146f4062b000549f8b082d81, 0x2cd8834448210238661094404f889094a490011a64b2722e0080400e0478c02020080812a8e42c0223454595800001036213c32db086970539288c4310a5814009a82044259030),
 (0x12043d098a004c16372221a080630149d4aceb1020c205346c00d3020b58a904432080c0134b185a000490714036889446800167911752474101741d000ded2886207ca1404d30c, 0x1f20230543b02600058561a3f1c1416034110e1c53c0a4300bd0cfda4855223b842531aa000a22007126282ac08246a91765e106e88880890a40262b4a01001109f0106ab30cd0),
 (0x6b8aaf808e00707d440010001d283e38d10226c8a2a104110180c00dc0231a08659b1089200408812015410298044100101046a7828c924594428380e100275454913e540f946a, 0x441107540ac0b82b9e125a4a2c700c32040c023110e2aa45a043c522688a0f180606656de92001c4a6892d04783ac2fcb2bb158357300a242144c2314565821802400a0f04a14),
 (0x20869010045c883d2110825d5004856306c0063c53070911522fc091d51ce0c433204508c4600c8998a2025c828a0caa430500007818002802e2177408034347084404022003039, 0x1741276bf9004782d84055008c493a9c211d08400c50a0a401c0124200c0192b8c4e38b53803a066471dc0207d74f31180ba4ed581e1519459146001c1283820c603b8f5d1042c4),
 (0x4028acf88046001448212cd0401a401a84251a80d1501661309056c01c22c049006e719044a400540199352f434a006998d700a721c02450d1891d9a04500011c488c08b12720, 0x17a843100405a1e8aaa39c5128acc597a53182444d0624a01080080022e39d0c105e808e671848bb087c6048002c048386220005088410c3a2202042243aa2b6ae29363b0060059),
 (0x9061b8e5200aa6cc9d2d020a8e8680209b82750b0442c4b1af200402225e06ddd048022f256000191e83875621fc029c124911648299002890c510d38041e255a17c122449e0c2, 0x4d0a40025e0401136292d185604046cd443d82401a9d184400dc6aad0420f0002501ad50c2163f420070102950039160e426cc835c460b520110030812081c080001c90b801919),
 (0x180d1992d4c47d34e05d53272f80508d4220029a682eb2c22a92210970848c00e4145322a88d8a81c04918201620238094816882020802e459c840421901210a62e02acc984caac, 0x2142c06c290102091400a89810538d0209cb542002500d08d124ce94852963bd1063a0485202657c12926712209a482823689644e8e6cd0a2435bd09a4e44a45181c14120703440),
 (0x1802e4045148a0904a57214d30008d400410544b65648d000ab294c43281102a06e2178ac0963565525960011cb082dab00552ccd0c14320c1b8831c2240004fd0403803068142, 0x167681aaa8eb6086500081e2242d830a0fa8321941088404ea40c4b1244060c9488000804174140122c8289e2a1086d000100242303001c8e380074c20438ac0003a1c47420068c),
 (0x40547001c544f87062991694100130c82e919803400c10104d00459e4fd8eaba414720141c25144bac000c1401f043908002531148d5635e96a85007318005230048016a0640a, 0x398122093c283a02020026c06b8b388a10114c0568b25286c1a049000100271540ba204981c2d06090439430e2440a2064389dacec1208988000412d804646185c6a84969198205),
 (0, 0)],
  #[
 (0x5402f000a4d0318828500490901d4353080606600001a24c20065eadeb4204243b050650794f48628048fa7407140240948a2b59084609b4888199141db120c1f60a748b134802, 0xaa801d4182104205729532e4de034209548b11cb6464c930c8800100499184b446a982d80a0148d1685040be000a483022050a6a388a001366200e9204ccd1c09250070088068),
 (0x24a4530083c166024440700004a62b7a1e92c001952505564f0028a86135401750a3202908203b82095618c246600200605101250319308000a410152d807804954a641f862aee1, 0x104a04e30c0491dc1b87856518588001816c300a008892a990fc5010908a9d80a340828647cc00001621e63cb9938c8f8986c2424480c359a55b6762d232026b608401406884110),
 (0x11b3197484860a819610f965904018092468341540a4121c226047830a2ee1e800ce4e8b407116154e3936b31202c4202d2c68173092149d2152c3992301782040a1b45887c229c, 0x804e6025b4874026125041a241286a2db00ca629a19e862d98f385015901206e92090300a0488021184410ca868299a924083008b2d2b22d8a83422d802864fa9480024603c503),
 (0x1a286f087100e48d5b28d9843a4d4ad924f68211034f12114b8381781241f6651500b424e3843990148404a91201294c84ff2a18a8460092202d009a1b0e8af8e22842e0e039471, 0x18300228c95137020032000c412a120cb085108503008eab4607480699a0102225b495b0c390606e313e114e86084806a00044752a9da4dc312202084b1700604848001124220e),
 (0x82e804c611a1c8e98361e80e05090b9540153a82a4682b42c12843ba0911e023156a093c087060e12001016705504040c02b4810c21681818a25973f05224c754cc30854c09022, 0x14d04681120561116248807d040c2446a154000785913441c1c418800440807006885c041c68c151655d07a98aa0a22b2074030c339c96464715028c0e219a308b12c200a362c91),
 (0x3b30b1188d80220094134858a1c615ac48699a6b18c44188924e30a98a0228040591a294d048904509a10470146442085d06000400c4a0810cd4408e8940c20a3e7031961061980, 0x40f0ec53072597c000037a65618204294140594e6091c6349318f466469520ac0281c6322362a88760a408c228b2494a2b11e7abd0a0214c02a1b31468a28b0810004618b88033),
 (0xd4b040ce0e0c3a10150e23090400211c602082be401420600120670250e09830a88001460808096208a581450245044a4014044918141c904a90e06760b88c953801204604200, 0x3a29402a20d06140a062410460f005d06106541d40bb038814864718bca10645ce036882b8046006953040542270a062a51843e800e4ea2328352c0c80940170628728c890eb1a0),
 (0xd69525d66cd9413640562081e28cf637789f30250839261c7fc0c7150c3050111738494d4b2114c542002a4c820010009a05a046098fd52621a88999209a07000a860c80939066, 0x12100d20190063a813b88d26c1c40000083608852324050230012002840878ea260c792a0b45c622a30b310a059c06bce25c21e3026002ad190144224c0211886514882352c2d89),
 (0x2dc4c11d70b078a08a1049b0800e1648b58c2000023da02250d002d88445216540c40021a11103cc00499a2008410843011c682328b4468c8a0343a948210500344cc8360c495ac, 0x103018628b020752000a94027c10291300338abd75024fc0a52040247a9092803701ab100a604411d50221d4022ec2b0aaa00548d108880355c490021052ea28c802114032a2243),
 (0x210d26caa185aaca0b63204120033c49162032ea2c07000c4001d09b089027a369033832070c08c042681264109150296514a0837800b3609814601072ad42cd5348217e06e7483, 0x6f288200a705001300c47b0c07cc110a05c8d0492581ff127a82464f76c005080dc4684a8d1523831944810cd408284882348548035001847400c6e8900a5202c865480b808a7c),
 (0x2004a5209641322002326a0c522185400d0908a064d9ca422040508909e3900b5807777618a96050e40a0d4a0e497068330d265c07c9803042117520a09c2040a08238a0c8c4908, 0x5891045699c8116150084920c9a50b1f264c658912431009317885206004c70858808894210092c0b8522a01190809504920002d83657892026029f5b41c5824a384358041a075),
 (0x8108b4bc5202a7980e9006656583809884b4dbe202e902f090e9200234236100cc348402c20771091ac1c11be898d32c0010bd940dc1000040691a08102005c24a50b2a5023af6, 0x13657414204ec4801a04d990a880033416b0a0015f400f00d2d124cb1411c1c7b23881a202818881625202a0005622081e42b0000b2085e668b92a5e20fc22a3491af0908c44108),
 (0x3310a0108c81500c741054409c201c4b091d88860a00634205920640079a388117080c128467583922c40d4080a0c720613b11225263040120b2281f895191d46a20a2041ac6510, 0x86a5881014620110240a9890199011424002059f04d1ca94208402d08244258203021e04b08a0021808709d114820080a84a4888c14905e4d0415c070ae6602050c0cba4119222),
 (0x3006d80dc1108cb212520004942159a84d805103052841040d280405091089860c86048c650cd7c93d42585941881088238cc10940544044001a196e38b05cc8134b310590ea40, 0x1cbc0235020ca71494d0d6b914904a0421056226c5a103a52f015e10a22ab5609930139700a600830801925a09002ea3044600e200a2193385bc14010844120360494485a2500ba),
 (0x26109393d9807120e0ae8ed852531206008a80c487044a179001028afcd9fa3418a466a102acb808ac52108d1464404199308af89aed71d711e408a0380b90a20a0023030b4c0a0, 0x10ce2028043180001c000104a9244d7836450c08101aa0484bc219550120004bc041085a451107c742a8ec7261129fb824857403400082008e1b015f04d00611c074d00c4032d5b),
 (0,0),  (0x4502060d064a2680091a8e2421c0ca5981024170cd2405e229020e229e5b08188a418e0706e1d8ccc142933307d0257ad4bc210a544621600304004c132342c40931d216807301, 0xba00e800a1140948f06460829c2301a200b8b60402114019546100482104826771b011f0a80e22323024280c20001a800b4094448a09d21580330293e01ca823640401c0630c04),
 (0x29050b021e264820e6300a88001c8005b1483b3696c161d0183f000880c322411b45249065646014014b511024ac3f320081cd20040c4105619244c0802d428f06439a738820181, 0x5a849cc008a713010f0006f5e14e6a0e2180080810040b224092006d30549aa422884a1a119acaa4142881585300c4ad1a1003a872bac2966023324fd0a440b184448c31c7608),
 (0x2433049150119b44281fd29c005024c761812c82050132a48d9f014044112200c023108096e53d2026e3ac001049191d6626119540230c2e3524a081561288446c2399910414309, 0x100cd966ae0c009346c02140c1a202101a30c231fa684c517260a63d106299b520886703481040c5d80c001e479062828091e040ba5492900092122400ad07890014606473e8cb6),
 (0x36caf055850850341200c82b42428da55120501cb6a00449d208a381812285020787220a02ee5ad893e41ca3ad002827400511803083114201000246668440c1131008202882093, 0x8350b024040a1434dc216c0941d104208c684e3415c10b22852442000004ad9e0185450601001026410034810c7d6488f484631053cee0c88b60509080a8838e84f81804749e40),
 (0x9601041d0b444e566076a0901332c14c605e00423006430a61011d404300da923ca8a0031449040f9248848e24800121090128a34049473f17144c7803f8480402cc01a0e03903, 0x121d032c2f40100289381104d80cd32339c81e8ad85012c909894a01728fd0001c315409c8814c17024870350401f5844003ac3442e142080604b8303b80435612d0078121b4418),
 (0x3080206222da38118814c8e67cc143602f002e7037400142ce9000a032671280806145f003109b509ce0890511366d2f884840280202608e0c41501690605570b590b00005a07c0, 0xf32979c9904402432c11000031c0002c09c110080a67600012311438810e47f4b80a8039063640a630a5240828900803684bf51bd340601a10829810715a802424a40ed180b813),
 (0x341a173d7575a080a0aa2d48a736d0163a0c8803c42c314ca4810427c85e0043e248800e4445106a2914aa770410186901e2e71057105108858461180a4f2b004666400c4918301, 0xac068408a004040480082a618c100080151264c0b510430116280d03600871c1c904c20b1b8ad15d46a1008bba603068a01006328c5020048199201640010d58001b761b202ca4),
 (0x91056335845808d0438e60c3a0a40214a041160f04911054324200d4d98c885a52485d0ec2f00700000ca81a12302aa81e761c82201e0b2c911d58b3c246168088f44060c0c5, 0x6d02d810884aa5a323140100180b48a9c05c10a0c02a2c87a10804880b066332840481a2912906305014d24241e583844761014250596174014ae0820831902026570834990430),
 (0x231b0284c1220b0422a6474491967cb886e098e11a79c93c04c002894208b4b90240640d1a63dc5092d00b4068c300a386090aaa421825c29a89bae27e1c0048953028189d50586, 0x1844380a3684a04a401808090069814329024708a08604c3ba1f18722dc20b40ed088972e00821ab692860281200035448d09450a4a18028257241188143f114680393e560ab878),
 (0x1532192b481260150c2431a40462080c05d00407b140b388402d081184c4a0702211a1d99a60833a28003720a84a1952b584c0a28806935815540a36c2a65234c6040029f289148, 0x2a00668423e592eab0480401c21995719a2db03840354c542842f666430018099cca0222241040c0c00340ca429080294a792050717904a66a82f4403809090800b2068000046a6),
 (0x100500c8c05343041601920442299c854194280178faa515e4e04b04941690eb4108008f92c20405008790b81c6823b803544204452c84e31a648842a170b0c460a08c5e401d788, 0x42260301700b04828b42d3324d46378ac2094f4000410e2011024894109411418e52c5068142b00cd286e44a0029443a80a849012117014451017a81a804611074110019a00047),
 (0,0),  (0xcb044d224404504178fac9adcd365071e0429a21218148001939509bac8982089c126a0716a024320106004700744c452443624118238524015220108c12553c558f0e13a44300, 0x1038b08c88f38d028704125200c9a00a02ac21d49606311f86c42f645332192520cd94586951430c4ae8c9305d89a292d3309da203c44ad2088980cf512122c0204060cc0ba4e3),
 (0x29010406cc04011450813418341e8181ea185ac488c10c3858260894626184c008081011b55850abb43c229434140143b6c39170c8d07a482c8148546b011d3806819490498980c, 0x8ca000034bcc212d368b04cac04a401502050a531eb040a200f0621c1c4a08b0a2e1e602870a144b41186840e1bc9c493c4c0a06210480d36821820096228338646a2a00544e1),
 (0x28025c84e80d011c7258281994c96092b75014441d0088210a2c3920a650c12c828120029809648ca18e86468037c2e806286284f11016301101224208525038a28528201e868, 0x300264032906d298030404852263320a6c482fc3a320fb440885d2c25149aa28d2110acba845609353120119907d80091690d38153008d41834ab05095330121051130531761281),
 (0x208999290449552902cd4405243b0803ad19180906d0caf4543243dd6416201a0b9ea0b04a016c4287034260809dd1cf30586050040b2b80c3b8816e0148097870819c00f84ec1, 0x2426244c648a228162122233a510010701022217038052008a94194220888cb24c040004c80e0813070041c9434620a204ea30f863a10145f30056480cca700000e3440de00902a)],
  #[
 (0x25806492a102a1c147101ac20ab360a2d4b224c0417a04005a2a5102f642c0198c852c07095400226c4a414d090022f12009484c09cc118432864440c03d08815c046652a188300, 0x105b1b2c0e191c3e086ee129800c18000b4583238a84928e059026ac08152462230293f892801a0192843600222c510ac96484004203ec584929ab9b1400920c021a88ac4435cd2),
 (0x1580930034011c80a04810864404f8870a5b66b8b218981696401bcd17838f05d013a8646160501a198454c4c1cc14a0c0827dc1b250555484020081e8190ec6a265a3814368805, 0x24604dc42ac830a4a11e92131e200284120900649a340a100a8a402c85070e8240441881a998201a6588a3b2a13a91e3034800e4107a80b00dc297e00e2a1095480446838074fa),
 (0x880c023075022211bb40881c681a04210405754c59fe9b747139502000f40a9d62425004dc22c540a82ac00184112b454e1ace2ad869432a400010200201942b31001c678558a, 0x3551a084088894114e40a061a116e1fb5a0bd28030820004098ac68a5fcf0175228d15a8ca234810a1058019485228c41011a410c12104ac810ba48f5940fe08540072019870a24),
 (0xfc7018189a0000b00a6d7c61298a1062dc08004602310414018c140e005ab871040118aa20a0461b46c688aca501086c0852280441d0c67059985820660c24c9404d8040803b2, 0xa018846a161a59949a09000924671e39c21538911390c61034671cb103800048659708444c74c10803031124252d49303b084019ba00c28042266a5d09003801097807c9202445),
 (0x12a70ec8a8a206514809210101a4065121db4143cbc7c05da1820e01601880b36f21002a8a0151ce00017211403a00482a822222c213ea2d645dba11166d6c209b02f0c08620020, 0x2c50d0105440810033f20a984a5af82840003e94301832220a45f1fc0f202140000e4e0051fa82107cbc048cb2402d14c011808038a8115280a0006cc002028b04580b374859714),
 (0x1422ae4aa94070403a1254439100d280700107903a285e0c12e41d43099060a93ce068a1028a004427842ac0000628a8006172d119c88808227a20a40044542c0470a09798a1444, 0x19441b0148e0081842c23046089246d01de380684c681e02d03a0b094631340c000124065016d1bd873913c86c051144d9a802ae63217a39101881ab138a192818a4948651cbb0),
 (0x23291d1e8690c0b1284852c30406808d0866f43306c48285cc324a190a020c40871424e1882ca0353122820a2e5a1b08d00c037200599007120e332cc402b42032942a00182015, 0x294d6e201796c1e004204013c901147622689028419236122320130662189732918c21110368344c0cc954971d085e490036214005fa263000c31c010001c415b8c6a5457e6c3aa),
 (0x226010da780982a28061e3528e22422393d301d0781011a591240c2804a4860208809c0406a1280944238a5114e86c08106a00c0bc0200fb0001480aa123196028348240a820003, 0x99aeb0087b46d580a881ca56015081004202a2a07820e5026184187b919494c624722c1f8509582239031ac0a0202d66a115210039d190043f404745ec0429f918b20a7120c950),
 (0x58000060738a0010574c248a5b017605a728a01b48591382288080324a7a8481e3c1c4e0c24a004e288c3f0af4a150c0009584c53602c590310620182121209804046341093583, 0x281dc2d058470494728810a30240a8098585119e49300a06945470c80218172201018110720a59630043180c1031ca3384b280212c9582a64c06807250ed28f4679501c3e34c874),
 (0x890b2c404f5931608064204a305c09004017013b3879a2182628922880e5231108ca9508076aba45d01b1accb1480a00c5c0d200303c80311310e1508c06082a8c4a667dd50696, 0x224c051bab08006977610c9b40722022714c85e84840011a79904208063009c2e26114241900445b80444211300a660e52a32205b0302648e8429020710a8f14002a1188020f140),
 (0x2c000c294b000438220b28c1682272aa7c99c860ab04145273e068980822b9cb9906a5d005c0b1481112d011208605011d041422400f147f0c5617b8d225202012813f40205833a, 0x114f11294a072c79c60902c971980018242370c106bc2a5840394478149462006b90804123804b362ed08025768ea5a62e84a512e30e10053a140460cc24bd04024400513820c1),
 (0x141218db8208de80a0625e489c47022c60276e52255ea918ce01002e00094621b166ccec2cb0083d21000404560b868018c0c8a8204414e013a892501c6d0845ed26a300084214, 0x1e248600464330015429da1830238edd29ac891201aa11642205c4640d900b9500a813002d048c042162a710208305931c60a301195a1c11b045305aae39013a802981013a1b542),
 (0,0),  (0x290007381802c45f05002c62214feaca0200811060044711b54a624894800ea90e23121dd0d2e6222b450048200ab049631800447e024184a6212b300000ad06d042a609f0a343, 0x3408a188346491020b047829886a0010421d02aec854b38e64a149d972a63f01451d86c82060419dd14a0c7a75c21460498a552b08004b069484a1484bf3f52482a94194404509c),
 (0x5c66183364a431a02c23e9d014845c42c3208054aac13d349101404509948c104c196755eb8040342a2b41c9c570f540211039a0044230611fa82dc60f06508b08d880c4808160, 0x39986040351ce1183d8000e0b0382bc0c087c294008c2432a3c012ad20a522a83c208080044a84101d49e20080808134a64441d73344e06804142290099a164e724083b204083),
 (0x117dd2199cd0e81f2040a81c2cf00f33042c0a500de945744888048a85d29b0082804088a8b054804000152c1e5188a9121694011a4029a5402c512fa40d1560cac11dc860a5351, 0x4820de6232f06e0caba06431000100059d2c4ab8006128b9344c3405a2420d10d0e02445301222887834212c18e6216212009a48197c01012810ed04160c89f10128000875a028),
 (0x28200218905041380c1843600555e3750128df10e1097420dfe984a68e2a883d041582a96504f04b4201e497318a292e0680ba0a406cd480ba380014f744a180081610365924e0d, 0x104c59634d871a42c3c48c9ef28a0c80688300c616660b412006594941143640c0624006988800243cdc0320c82400c1090c4054890108044442fb4a089b526c17c08881a658002),
 (0x320809225942c6cc81020025400c01416c93c9284c5a28611625798d2304a86e2e7c0cb104270203100434c165448443032785004a0154c6219422a8461c475180920229a0c8085, 0x8c4e49c043d39016071561a13e2a49610040006a020828e49188212805a5710c18102027a987ce46d29832e88a30a80a41000f711bea9399c2b1151a9408886642598d00e0582a),
 (0x590fcc88a282cc99202141ed6d8a980900a42b064b489234620bc8e304083f9a9624000502106f9975302c14020092910351180dc42f1088b1d452621a2724a0819030d7218904, 0x1a07030240970006608120e1210156156ef4904d914930d099940160cebf2006069c30d209cca80068801d18869f74448302e471219502e014a298c1000c08b4e38028028946278),
 (0x840030092453b05240e01110db210e528084050000f0d1824488fa1c93822078491015a60888a9083b0411604e2a8089da036869051001ac182c2240380910e045138f302bc43a, 0x13a62c31040080a09a011eae80014202d6d195874330c2e11021201414c591705244a8a08c0745433c09b8a00a0803f32217c90104aaaf651400359908364a90a8aac7082c40204),
 (0x2038010020e020b370a734002c0e6aa43001a140027a043918ce398c1060e5c101204f4674004059b72007a04c4c1084160429065493d264bb03d580d6e44008c8500d19c008021, 0x1a01043d991a8a0400088ad903508143c94e4eaffd819a0246110433220a0a1a0cdeb0308a680984404408070191af7ba8731478002c28180424280b08133811130572643484450),
 (0,0),  (0x10e10484762817906a911d208050acad1240b604696891b029a4725496126e5a20fe25522d51e1012c8445746e840f21842010e07b211b204d20228914a8675b03100092a201162, 0x80cd2030913a861004480ca5fae0240ed3c48db16910c0a921989aa408c91840f01da80022c1c368108b20a901390120a47a2010010e095128b1032e3410884fc02d40d41e2e09),
 (0x212108431e82c989a385f077b0c52722e2e6942c102ae08997610e22b002309698809ac517202088c08a03666410c012f28c016c039018898e0108018c01461c1c4cb1ed1d08904, 0x1406d1244068163440420c88412ac8411d0143432b841212088e510846ccc76805732538488b98742015cc89938103c409422610a827054671ea50f61106a92200324e0002b668b),
 (0x4e20658d315aa0016a0040012415a003092d2091000c81001858c80652c3241351801ec3450c0084592d10e98454e684b08a830407a758f891045b5245c029f3298a76332aa2b2, 0x2b0840a10802158821024b286c9604ff4c410d1005f417abb678515d1841c48a88a0c612c9ab27c100490e312338a112a46600803d040a4030a7a20000a25820842000888005c08),
 (0x21f3b009201b4c8411429f8d3a1d87e088431a404008a5005809010851f5402a0101aa10a2286808a2a68cc288a8211640c205432650f11a5d210010e0231c408c0404c4099236, 0x35e000c4044a42108ee25002044800804721801922b3050b10550baa32402a1c0e6b001ac5c909701080922101443ca892f095a9000000aa5a246ae011c00200271e9622bb600c9),
 (0x2b8d230006938884c222803541240064da802903c3b04041c0dce62c1e451adcfc3f6104260dbca12830165b60c15208a07d01920d094422400e12849a921190420f11816199440, 0x470d4e2a108210a28150dc29693a219207d00e804063c181a2009d2601a8000028096e999c0425ec6cc28849510a0335900c06d32c0228020e06d0305606a4cbcb0484a98448a2),
 (0x28a4e588448c056d84e4cc21002204160022102a46401390c042e1e8c31e0040089ca82513477eec30001b486908133c6815a0a2e80030cb0f73863c24968e84108ba10108a405f, 0x105a08519b70c0804b03218ea41c2b802a59c095b0846c2a15241e1420819028c442478ae0980102cef2242086012c80954a5c5901270d14108469039b41301a05644aa09611b20),
 (0x38400227640ea3180f2da602961a1120ae41eb0ce3037140180029004030667b3c074a41b8c51c214d04269cd5085a720a90b04cab0400b27101d21940282c60c0131200880b14b, 0x13b0dc81a21180720c0402129a44497409814b31c6084b906d006613d4a81004108a1b84438c252a00b50620aa48584756903104483480102102882969210962f202c3271648b0),
 (0x286a00522402127a000a821ab038981112a21285c28a007490a0992684220a20bff0d8c0f669ab8a440af8a91c9a2532288e4c6626a9f1014822942988010454f08546eb5088061, 0x1715c60d532d8c800cd119a50a83028c0005e80a0d604582035b021939dcc50b000d26220816402438d404508264c04896701098c80204de825d2b5645c28b880d1010040623586),
 (0x283042122100a6086819ac40b8daa690401802167c9408d02445c80331230cdb152024c55520a57804d8643ea99448898a08c734d3050097210d784d8220632484002084404e094, 0x128985a4da250907970041920321186384c67ce9806a34261932021084c8b100a0524232081a1006ba0218c1562a861635f2104124ca5168c25284803cd00c987b549758baa1a0a),
 (0x9444d401a14b65a0000b0164dab0c20841102a30a5f8e83190068c1048706901202400028e0410243d8c2f10204029c03f82b5954b400821c86588887d98200c0042d4525595a9, 0x320180a901230800c41349e8b000b0cd2b8a0c5c25805050e297873ebb186924ec3935c640148e340406040eadba5d234004c4a220003469410026120806549c0ee1d09890a2a54)],
  #[
 (0x92c0d02010351ec11501ac625364444b8021c90488849650412234810a0324001b8913a0488f09fc08018242f04a230ed5f04a23283608c810380108200440080a5e360591824, 0x5253103992e4a601e2024000d2c0091343b043433127029aca4004302a428dab3c416641930305603200c25a0069050a00001944043814321a204ced643101e402401010a28513),
 (0x2908fdb08deeb1031090550e2da8906c332008485d339103660e62a69e05116a04a08d931acf6800428109434380280404de1496c8e140201090d9252192d8fdc180729e1105390, 0x1481000f42114858ad008071c0054190cc91c4a20200261808a08c5901024e81e34f320c641097ca8d222630a02144e25001ab2916182fcb806f0242da442600081c884166c0463),
 (0x58a42913e8214105c32307829ad25275b40a01448a154221f4834026921e420640d1400221918d5c2027190246b3f040608046cb39a0f30ca309e813c11d6063b100f24e299400, 0x51256c81108045000002008040d800809a1b889742204c60944ac094520bc581a0ea730ca660200041886103948099d0b4d301406510c92086013840ec2928c00ec0c21d44b9b),
 (0x63818ec844a24640225a8c528980a0813260016a16942219b40c360f5002c802cc07833500410c2b003a7250093b03c2819e2001902171f06040a120110804014b8a90c8819413, 0x180180035201d28b00da560a5506c152c808e3e0029430984432080500dd9121400504442d906e240ddc18da1c68028045041c2326fc0060b99175c0380b48302047029111869a0),
 (0x1c29a00241470c59423a7800a5aa940029850235022808040051423860d6c5b020bae0100044a942044cb12596c0c828b679c102408da12620491234410310290e18cc69f5281a8, 0x209654ed941840a62901025c120528a596004d888c4623f8e42080859b29300d5f400bc68d0310a94a92000a6105050608801ac8923246510c8248011abc2100c186229002c0200),
 (0x24022c944aa0c042e0620879285068cb1a195803065421618021488620102da2d048c41482d8f4645150c6aac3a39066b040105b1aabd70400932242824e390780216d818070b99, 0x2a95069304e0da91791210293051100c48206240108908a354e137805e582090d272a290d220a822c8411551414481805af2724e554087b476c40b11d30c0f81bda92081486442),
 (0x1b26956808cc629586a814c51090a8499ca30c64c2263484a89e541b8c08800117916428900809b0a1fa26402181c5603232181015f203820558c8244e31bc04a24042824072920, 0x24112886910391601157c93aa5070426411c100a0d98c8714120a8004344671208401b13239376431a00999e1a3e321d448de4870a09b4584821024b818243424c07b428280d2d2),
 (0x6ce60d054602000ab9a42a440a4122b6da2094003242a1823e696804bca0fc8c4402288c5346850024609441822880458d54b84c310532112894610024c1044100121593193de2, 0x28209a07a0185925006514433b090104920c92af4c9a508314092157143110340a0a193728808306a1b0d020469103db220a947b28e780042422390adc226c2864965202024c015),
 (0,0),  (0x808e0965ac25111514630904a18042180a123910463537a04140804a139c61208b1251c141cc02010004b88d810387a2022c64829010084476b4803026e2170420510290a06c01, 0x1760122184042a222218c5200444680e0356042458140405b1c0b4010c460068e34e1a02c343219f0382b476016443010344298580022609901022a8f1108c86b47a8a063171328),
 (0xe04019e9bd8d814028420939151060759477047e301429835b081fb420402b4aaea40a448043220fdd4c3110b8d862d22c4a00a015d58344656e28009b00c0981074a5a6013e52, 0x30c29c41600723839c225e0c682cf8e8008001a004f6bd6142440e0091e1214b45009a09b3b3c1c600210ce8c0402952153b5504b280014b80a91d15500613e014c084019f6c12c),
 (0x2090a227a22149462c05890c002504091671212033454502f482468848a0c308008100000850341891001128479805a500881138aa2810022a749600c0519310008308227e63940, 0xc4f5c085818b620836040d142125886e90a8682c482a83c0978b862240d342540024edb1109818340beae04a005204aae6400c20592ea18810369af21a60c2ac120b6418010413),
 (0x287a344701a484640a9e84c4408060040c54e11cf0294042100740c148c11027804c0483e18206e2202a508407704c4480c10152cc85da229c429601f22621612b0400444c88d30, 0x16010a306c1a539804215228893f06f950aa16810d44bd34c6001e0a8124c64809b3e12808116011df950948180e31024b2a9608323204d14009411405d81412903aa5082075287),
 (0x2b430277d60024e64448a01b2644020092622b6096421aec38b88c432902a080523c40004608bc01101e0c0e56a587a5b780c8d421b6151a1107e4084400630090fa88493808032, 0x420e108289cc80019960dc058b924d20909149f4820e4018203100080b80d6108829feba8a601604bc131f0a958784a00130322084902a4c0b018a119558c2409000302c661289),
 (0x542ab88d033018009522435e90ea3c896044148ac69844912971c7224b2e02052858c3024fa820a0cc40333300d40c6c24ca5103a0000400401065128e4043c25701320703a061, 0x100910472c4074050688d182027104172193b2344396733269408380090407d8097a70ced00405743203cc0883e200001d931a2245de9b3083f4e8a2d40a334212880c568e84002),
 (0x153800c0820ac4888a0810813806108a28b0350121ef8ed4114d014449d0080d2845b4727ca600825080b13f49080709041002de2800c0a4054808f009c0889004302af0d22d0a0, 0x842cf0d454128006516c47a42b02a20444b803a0e10500a0212acb9962c91a0c1124208830846710b6500c024d3807699095920c4123e58029287073621122b7041c00d2d42e55),
 (0,0),  (0x19313030314c2310278280158882208650058120b8846b880f66c054ab2d00001001806805960ba30882145940318858084261f026f94e7980c05d4412b7e1144b20582c4052387, 0x260a04074483802cc8456a821141cc6109d204dd436a800570811e2b0092011aed261b80d220641c106cea22240c460443ad1c0399003104023e800a48000e29b0d724128d80850),
 (0x32a08104b008ce81012038569d086c8037a4a696a78181c018122892826a940056c024a00e926384f8904203191546f31414c84e82b0c64380d8f37048af08b80080420902a370, 0x380412a2005a7012cb0d1452842c4810fc8434101102a40258785552c60956a032117080dd100842b004a20b0e2c2a10cc3e22730510a39005b060409b0508600c5558dc4d05404),
 (0x2c0808492442e4d7330f8ab44008a5d06b9680e00121e6d0a422024a0383284c3e586126dd6088b08cf903100329989363cc946c1a7008212044945a448489154959b105daebc3a, 0x1c3e5961a081220c810554207e24205104943038ed8010d4b0490b53810d621018006d9029074002302ac8d5490214410302381a00052d8c1a008249353768a242200400010281),
 (0x925309a704240a099800391b9260fa0194a975f8680c02d490e8891400a6040a0a9507909c07601840c6080632a002bb00b38a8a2d95e03100dc7008985d4de220042edad1cc84, 0x365049058b8ca15f20152c0000d14013e6154000292d1f1236501708315506a517508f006630008e4a830132141538100a744056192281244080108922122120544f24021061349),
 (0x2798068e00308900829b188030705e8c84505a2691ad1202303560984975990f4a10466d1ca00303000112ca65101c05604c4802e1f4542d0c0d402d064c2802181d56307a31802, 0x18665110484f443a7924a673c084a072500c0150041080d8c80a910302880680150cb80263422c24084a85140a4d6230008132580a0082c0e26030425100c484c382214284422c1),
 (0x32f0518d070ba012dc4c4244710844260a12e10062cc4ab710212e6753d62509267254619198201e142310802a2512cb89cb40802570064930a2a4245201001068279023625c80, 0x2880426424034438d01822dab8294ba48c04c04c71c1390486658d090a0015834c80989064a214e808b5c042c45dae80434243029c80139b40d5c1a0988107c689188451c19a033),
 (0x209a841941e007219c312c640065041a53104dc35008794387120cb21d1a263286b8b0fb035148845cf20108b9a4350e5d8204a120049002c6cd10da811b4383045124500ac5f34, 0x5443a241a03904c618c928acd92f244886e10382bd5869410a10249c264000401424404e42e347a800828614219c2010035325847a066c13930cb051ee0bc30b2a413a51430049),
 (0xc2210be0b40342014e36197940a12881acb460ca4c628455d596151222e2939c358036c2dc89c0c32e9ac845c8c03944a12f01802c593040f8321414008190dc011a925191894c, 0x120d43015015031f890404406395a100e02481a04008d5b222a4162a519102860c86dc0340120123c81450582353306a11690fe0d12848e3906488b08c61c0d22b4c544aa462212),
 (0x2267577a4181501400119202109cba10b8c920713f88007e30554a033a8290c10321aa28c5d4050c840009200424c0435c0005a815693008084010061c20c1b90913291000bd290, 0x1980808008300603440401158b0244c40402df844035cb0149a031e0c5784e1a484e54d02001dad30b13228e02c81704a088f000c28088b132ab04a842953e0624a04282e402d2b),
 (0x9434940cc0c4a40ddb81301cd473c820114030090ae043b3012b021305a668dad50602a8e720c841500023054143b48d60e0ad822d010d833048804451089b89388041044f5111, 0x68814a21271213b20414cd20290804d34e010e94940424444a40106cc25816252aa8cd00000001beac1b149a203841529b054010803c404c80016f92a0460436440e2e900008a0),
 (0x24c815806b72a4bc6b0411700750a24562801096358aa20406732d30c51e02fa08002d16647b0150049080a0d403280903237a09003b9800b29b20b08408cb94a0090022ac08300, 0x19258a1f9485420380d02602008309909d1fcd08487048f08808528022a0fd01657ad0e801801c8b0a0e295d2ab855b4fcc88586e384664309041d0d40d304630f90e21d439401b),
 (0x21e420661b15490c61c6808fc027b201f0406023080a14197304002524216ab694980944888b27ca360690c984c30010bf07088968110073290878fab48d2207997e430354494ae, 0x10004690800a14d218212820298045f60e3101189151a2c08031781293d001402140e6304034081589494d020814196f00487062852cc600108606050b229960628098180104151),
 (0x20931a211a00388250c01481580aa402a0b83650e83643420b008974807f3c69a0033d3716450a118804a12351a72028c840c8128831a08b588001dcaf444acc210620d6008529d, 0x524e118e4ea4114a001290607e018dc5443000d14c1202804f130021b8002144d7cc2c8081244cc75081c58a410975415b8030975cc4824276a0a031028900010714a085410542),
 (0x2a002012114a8409b1931a241701b4108651226503426c381852f8488400f14a84000474360e098781fbb1f8400cc02092019d2cc26001e0d8970a00114e542893dc42088303358, 0x11e6d6cd2aa449144064c58140c809ae202c109ad895120160280535397604841a1f5a8208c000404c044401aa020d09651e02d30101d602226851ef809122500c01ac730c5c404),
 (0x20a468d5c12a93a2207080f9e18080895f04a2280813b2572449c24030e0a80181e3280008b54b021f4c0328510061209209391383a0a080800821400400a1800e011323d120b20, 0x1d01170802502c40c80e5c02066d7c24a0705445b3c4080803300584030953de04185256f348a0584001008086bb10c42df4c62c7856080d40b24c2a69880a3af06ca0d002570c0)],
  #[
 (0x1e0024ea84a21a0a44901086024028860c1458a41e446c22c751006328498a39a70829c40e2b1040a2ba0e408022c11e08289443a2c0088060c004ecb801540cc0806108c846821, 0x21f212100a4504652304ec08e4170729006b021260aa9240300a1c009090710210419632b180e99b0c44a116491d1000e65442984404747e8f22a011437602201c6b840117b110e),
 (0x1abe5e29088b314804b8103c24085e91d45a789004825a8c2004284070a30a245d40154116014a9d74135e440103112c82024287188600180c0000604367342003ae210be92e424, 0x2101a0c2f720000681408703c867810e09240245782000324951c71402483489a2b18a86e8363142824021885820464159f9a028a038b1229015e3053c8889cbf44142c41291290),
 (0x130312aba541be0b32d010cd00106882b3d211acdb268a406d4220c852c28810511c80096e01c700e90228708724c10e140e1438805a1a042079c82f03dc30006241b1138f90732, 0x244c611010904030c92aa432ec2e10514c21485200193107828d50130139226202214dc28186285e1694578100cb00618b00e2045da0a4d8d9843650f00289f50cae08c8602b080),
 (0xc31906563029b28a323b2498c9950797084094010c904054081222b8710039988000e81447004c60009c4608515e485eb2185cb72c1059d0161022407313d10b7731056a0cfb40, 0x2286049208352451044c08162262a2808540e4212106aa7a1c3e49c010cae8220123316c130a1a394932098e7860121800c202100d3a7022e20ce401a8ce00c14080842150104ac),
 (0,0),  (0x2224ab127f15b6649785b9518c62500f04003cb61a450f173960a9414a7c0219100740502917799104c98600a50c0fea02815280456504a0a82001764b038168008188a48621200, 0x4d3404100a009036802402862190e70e1020341a50060a04403063c0401a944a0b01180c0480020a00211ba18a2a00538682449ba1872135483960020106a11b9047718288ed55),
 (0x2018d41988f907a083059437402494c610082002c000b7010e70184245018e31070b00805321081228635bb300ae0d90864800c6a629be1ebdb1069c08008c80805605402d07a68, 0xcc100640402284e74c808c024184b394f1708950bfc00fcd105871922f460ccd0f4570c2810300c559c80005a50624d3022b03900d0400140062123f77473077b2982178060416),
 (0x33e6400814e0441bd30c43d014061f0cc8cd053a89c498a7d1449484d8e65458900b684600a023b1c390301cc06aa408d5a300165884c2412424d9f4203418123858398101c0, 0x2db8011a472cb0e2b4024232821a21900331610b0810421415828934a492101a22525a00608a4580008146c40c21b955a14200c3a01a748182acb032403c6c9c56c8522c40a2c19),
 (0x1588e4038e101908e285a508d87400548033299a403544603000a81b16d19a005da6548051184a14e8fa2144466840690e606544e833150840871b7b2420e080010d023f2129000, 0x281618104181846400024201208a57837a0c52240ec03b83c88b0124082c01012040830602a614ea0000d01a01119304119588280208c2e01b704480494113074220694090c0090),
 (0x1a39881ca698441a4761434083c883805243709b6194ecbc6584a36198000a106974cc836040606420d4c40c508c26c423488a01902a3194e427106d648119804612011200205c6, 0x18034201824a3c1189a1c883c061c23248c05601a4a1241882150120368d4c89681216496b99c13152b3ba10520c128c816607a4d80446a121866120a44c450b92df2886c1da28),
 (0x1189914d6e6310e4d00b1a81222614a00001517258080ed205d46201c140001d32aa080c472400884c999023314717b02222910b01a9088644800471301244000d000d19a900ed6, 0x2614620090140a180dd0053011c1415b5bf6ae8987e0f008da001158029b93424904f2c3a08abd07836644c884b84001949d06501844c1412a764b0606002a66c045c0c4060e128),
 (0xc01a12201b5b53c82b0910e32e38f8a066688935ab21056509feacac32089c5884220968280c12b01c44d42210c128a5cf408c04b1ec1a1004b342711208a71025004c36292, 0x3cb93ca084c344a02c0310f22704804207159000540054c2001a22005303cd51230401c4e29014a2284d23b0200dec224458109b13b2061020443904b48a882300c100d5228152c),
 (0x35049530a824a5034a9e4ba806a04046218e881003088306013230c0223a032465eb05982c9543654202008186c2b20c982315900128a8b003084a0601101257382480240960dd8, 0x2d92a8156d84218b5413042c1040799ce61722058d67c499ccc86345d80ccda0804e821d100a8929184885809000d6340c84a46f00240485453955074e86500c49b04107097205),
 (0,0),  (0x122ae2308278711590a4521801030c92844d1e0d88488cab6d90e390ac2d8e08874312aa8e44b67a20bd4800240418382000e21ca612c05402ee6b32803cbc2000081a540950084, 0x2555004531008a8a281184642a0452003102c10207b6731090081c614150618730b4c440208100810642a7241af847071ba910e041c1390bd50090c875824388d763e02b64a3532),
 (0x106859525b602440070464c34a58491d400a58144068038129b4d8c0b092b1284d63e8851413400354148c10241449104428ce8cd6070206426ab08322a05f10423cd890a185c22, 0xd9206a12099d320e0eb032011020082bd912229b2847420004b231b4a204e412214072280c08b54080932ee9b49b447ab5420422108a458b8110618014820888941000d0c58214),
 (0x80090a94609262907cc4204c108e10ecc0181b5080800402c16a14c2972a2a1244dc214232401209080f3bd00a14148a8288c21a20061a440154006361ac1411838040088028d2, 0x16f66c5290528190b83085fb265106d1036a240a61c70c14d321463006885546c2122d494cc90a4e4f0a0c028a02920706d21392042104189f82980000e0088e6304bbc8369d620),
 (0x2d700a93b228b65294021728e1da1042b30406552461010d404602a84f05c0c832050a8a40810120800d93a4848de8514160b4102c008c0a80443381ca040180444c494b36e785c, 0xdd5204d9548ad42712052180461040c41e9229b06721222893c02002809340422c5413a78f2dc48c2400b3a1213a4161401ce030151a12488cc0a2083b00ba9011624c908583),
 (0x5e928088041d7201508490690099424600808c2a11940870626688e034840b08c0c389248216513459371051c01832057017a0c08513e6648e0040cc02cc4d02924407952117c0, 0x3216d4e17a9a004a48320251233048c08ff3732504e2ac10e18807018425060732220128b00282e0b84c0eaa601a684ca0b2051150ae41801703282126102a20c0c3980405e081b),
 (0x29101184042d034200913624fd20036a602642ba040506c6712c0a1d0474675880c4020540068d6c07013331155d483203640644050009c2013100d14818486029e89589b27027, 0x966d440819921c18102a880b020fe88484d89c41ba5098208292912288098801663945d20c686210a01e44ce082291883819a1289279f401c40eba28b5e1261cd6042202010d58),
 (0x504198c21034108214023f2c30204a18d100d5bc04e7d8404440888330a40200816e2215e8d7eea2934225802d5a7840922029203c4a6400e340413c3000940200483254c42247, 0x1aab6403546cba53882b84092cc01854308a52a43d0000509010411300a4808257800c000112800490cbc8a0ad2a587ba088b124ec10193c90c30b6c1412320a0901048813a0cb0),
 (0x2a146821a5404a694940880600d394c803072f04200880c02c838cc074d945bf3fb4c92321e64d4ac076d31c0142021704820022cdef14c62396b2240bd800251207f7566a21069, 0x4c995c65a10009214a670d955042803189800099d834b1bd318331989209040800010c84210a2803b8828826e3ce988e150e8c122100b0004080111e023c10865b0080085d2884),
 (0x3024c7c2809008eadb1f4006088c53949c44e203b68480182458040668664689b0cd18138509007c0042cde68152982a81286ac40c005202900aa20bcbcf70226474308b1060f64, 0x811301920010510244036e116610463612a158409323284d2030018838899720322246002b401017d3d1010248904d522059009c2442c692250505414108a8098888254e80501a),
 (0x378e4e98e028efa20810680e9e28904b42020c3122915300ce448102181081b61c15404de3c194869d08e11963c9a960a029162482128009248180150098821e9b09e06278d0e10, 0x80001271dc41014076317f020830904b5c9a006482cac3210131659c1ed5a4860a8972214142b4120610e46983204834d04289301cd4956516a12e284076c2000b20f950503067),
 (0x805921520040165f00022e204080cb90081d0c560d30b1109b0c0eef000b28415d440801916045a0d5f01dc0924094d5d91142aa08b3712080e2599de48b1215450b1041aa108, 0x1e2306c009d7b1a8807fdd11d8124e2409e762b388624f4a8d246370109bb4d68802b8e59c6a82a2520a0a2016693249202022351090400a5a62198640185429aa8000e80844072),
 (0x2c9b90048801520f06481e06100cb08206084a0081892896244925c210e404c06d0011850a488740304d61215260d08d8747c0840400a95423068904ea06206eabf0033dc886a8c, 0x1300218965362ce0f0b601400d60402da0a614b51c00854191a28a38e610e12290a12a00543320bf82b20492808029121028252b89a6128a007070d90159c291040894c02611131),
 (0x80314448e30c381ce1c20044ae5d2a201a19b1002103848626530285102009e4202810cb448660109c91208877051530a3040e7689272d805061910b8013af812d50a67c202384, 0x252c49a040432c5a10e00b9931002540420640673de18107048084102c801321a4ec7a914a1409d8f4228c455806ac8cd5c51508152908077800664403a2c403c40090983ca5c0b),
 (0x2602008bae005ea040088ad8a17701141202fc9131710a15a3315f661581422830009a004520607b49d1b584317176e0e8c00109a8e0048804860e316102044b02c6c7f0a80669, 0x21818446001f8a147990234204880b403209102228a80b16058800000aa7abc0709ae21d2ba8d0384142c0060408288180112fcc4150f61046b01614c8e540904f519080717d884),
 (0x263e0901938d04640dd31100394ce041605295af2046f2f40014d2aea246c2c42352b740352d300d084a69205902038c35c2294a79640ea4a2412082b1ff0400d2110d11450130, 0x2900070242032080a302c883684a31d289bad0a509898080bff43254059a118304c21403e884002e2c624861500b8b002c03010950413811258be5f694e00a9ab21a2c0e6a86ac4),
 (0x1d3a0232e75490990b213801a6c0441a0a0660083002658db124190a347c30f84000381140408028c7082230432ae0281344c8a1486a04600be5014dad222a590a1199c92660119, 0x24440cd10894246f01a439e51299284156816e408a000124ec926848183cb03baea038ab39b7356004780c324400014c81110040590a99ea41a5eb250c95422112c4200511daa4),
 (0x240d04b103201b1f573a0d86f1a98408b8102983808c60340428d31be9298a11271407cb0d0211838441102862389268d001b701a34c144384230a744208100d002356249b21e12, 0x11009a4eb009a4a0a044a05006122bb44221c61029528d00b20400241412350c884980145060a4083a8c440501876590043440044411eba458889580aca12f12018c8919240e1e0),
 (0x1bd8c220020ceb84a1400f4523468835ca1bc578890080262181c8e1420421a08c043a70a21e1cb00305940206000018da6090a40c11a2a504004390610e2310bad12120e4244e4, 0x2020144f7572045b4407f01a4cb0240a3044388736b22591de3616081dd9185d002981090960424508a208a8c101f221041a021003c614023330b42714f1140e4506825b09c8900)],
  #[
 (0,0),  (0x21e29d0310271224b000960cd94a05d114b48b4cbf10ac39924629402262903b361c8140c518644242020602ca2201d885110d2812503072604086321a0414b4c80190d70114d9, 0x2181800a4ce58a54b086868a00294620e2a430430404853c24580901d1c096340c821762220610098b03c29bc3141222658e660c40ca1868895af18c004c3014802fe0528b0eb04),
 (0x2831a8484d43101400291201e401250c2a1fa100910c68341228a25853309544d9c3f4a0422f014844289005451004220937046088c920912b00a141230095029850e022bc9291a, 0x110411b03004816a6fd669240a985a9345404c672483820289d301278ccf6a0b04180b5031c030a682456932880ba8d56080d2164234c60a90c1149880d122e54609010903252c0),
 (0x64081049016037199b780980b5891197222a84b286702ad990420c88c0cb256089720407a3a1019c2020c33102db175b4204709e070c211f51a90361b6800d00414041c144609, 0x2711724906720ec8806001f60b40168a28084149081081c1202288b0072214108c46890a90180a02608143308e45044824283381415893c2008c406016093ce265ac252e06010f2),
 (0x2290928d5880c31d2712cd4a1200809b41b225220904a408c04061a01566c0b0599214015e2095016014009520f081102a164841a32700019d7119220350309000e23004cae100, 0xd906417087473c4010c50281a17441408e49d08db43952f6268e0447ea0025498001c22c015e020e10ca3102870d3eaf802911a648481540200a6291100640274e0c8d1825147a),
 (0x3d2cd2be3182bd80009581c4420a28023d140e732145aaa52103623a5071052938812a226a881fc44131df2054490c68a00809050c0021d011c41bc00a507820361cb1c001602a0, 0x290284086794271616a282ba121c2f0c261b0040e18005016c48141250a6816833294d0042660089e8e009aa31602174335046af14a5028402a6023840b839281e3403a3c8e910),
 (0x25d4040922c210414420eb280105ca2424a5a40030501a80403cc2210423ac229461411e08030910b80c632096260913541aa919b5b5219622591021c5930c2020b0bb02840001, 0x118219b20883d01801a8c0042c81a0591c35003364023c46b0a03209420d842992090b8c0b2e4444a07b28c932848c48089a012c602485c4948a6c286126461991045049970429e),
 (0x3612485d230a4cd059712d62710408893048a14a02c44a0640c480831614cd4091184126c431a0251a0042250010100460d5b46984942144c88008a10189e504102d1101920a561, 0x80080009860320fa60882850af1b1260c360430b90330c82e201054690812bf4e21a8d1238e1452404b240250872e481a020110310bcc910305874cf6140aa82b00064a4485a8c),
 (0x901083a17841c4256e1e39e20024304c0a03184a8240e853800902100112504005440c544580124a112d50c0b309211400c0479308060445102810bc08b0020c2239c12214243, 0x3a218e701c02bc389001e18415035b4582852006356029062c0c12cc87e6400d375888d32a2a3da4344e40a9394ca45e82de16b80022b0c3b8ef44ef428747d8f10c4414c5e990c),
 (0x71008b5426ef96688548e888706a8080026d228584953c034d009406812c310ce698672e130d0d1425630c21390274214206038418cc002a87a10e23100000310276c0c2104299, 0x1041a100058006992681512258a1409591d824c38630a82903225035132500cb109600090c4f0b00bd00053d8c4cc8204bdb09c0140336385485cf09c26d3ee483c81371d2e8160),
 (0x12a04d4bc4e9020b328c14410000bc08813810940a8b830163dd860390800163902002803328193900109182a002d0d1008453bc904eca025712a1265cc00000161410ce1106227, 0x284bb0240a106950803368004d900285220640494060607e080249646814d29c681b910504862406cd8b080c0c65252eb12300030ab0348c08091e89222d6e1fe0a2a131e459c80),
 (0,0),  (0x361364b903014004c21240105424160e8e020589133808157421e1020ca012931251ce0d94387c508c5a0307357409800384e0914658800280211ce84818111a452481a1084b111, 0x1e81304243eb8792d2ca7e62992a9f02008a8724047614a8ac21e2441516504a12030e02985020603a494188802040e681a112839201f5015440104170766e102d0085a3280ee2),
 (0x21910cd684c4502660b43107320d701034d47472043881e41cc0010008e270006988808da400aa1b00350c69c906cd1618248e88c114531c1617c006b01c8d7444a30020404caca, 0x1a0c7220212a04580500c420c0500f844009098c48841a0ae03034739419812982413c40434914045c00c08234a110a1858130030ac98042e9e83c8046033001b818011820a3134),
 (0x2050032909ab8c12b5a9a00011f840b5e576813c8148010a5e3d004ec321d2308d682a06508c6d0bf40908006a90544c81388329f20010016a0052064100b8920403a884402e480, 0xd2f74c4061462a5480603630a072b401a894800380580c58080121104460c8a10159418067392400384e572010ca2a344c16c56082b0e0884b628f988dd050583bc44711a9011d),
 (0x94ec5412a22214c3100f42f286d68ab093127706273ab4e527502b2088092521c2e2bca040601c0e002009626082022b6ce2390814844008a0174610cc320890918805036101a, 0x36a13aa0950410820eff00c0c7928000b4c2408d008c109080007c4d6546618800819415fa50101e11a8626101129744001044494216b3cd259c0894d024cc206265710cc18964),
 (0x22cc304061a04280e02a7c02f22a2928002b81034080a460f7e03106a558b4e68c01dc820811a408d54481283588c990d50a3a5ac218408828c809f1c844712b40898a00044e0a0, 0x1230a18040c382e0e9483d905050480ebd04490b8011107001a067808060b097064232181404982202a3a0140662041284140a138418442c7347002263b021432564527ea90413),
 (0x1a96629223b2acc15282895d100110d1039141716874c300004b1690004e1655aa8561040008a90a000400488004024731230242109300a47389d8c430222029fa03acd4006e4c6, 0x210898089c49413a040d248207f4ed263868200c1701284aae84486aa9b1c82054609ed0faa24210d1d1c527216825204cc41c98462c7e118c40212287c8814600f00009ce11130),
 (0x14240084142a14369161d65908e0168740d18b08e00732e2502ca00249a49052426006104429b40333a00847882926800c09007569148650e7030a142207201e018400170bcca35, 0x2983390009d54bc0401c2026630a08201c2a44e60320400daf801caca44a2221098e68439b804a80c00e628812945161f340a10202e3088d00c8804b01a81981c271fe48a0020c0),
 (0x20618be0000440028b5168048d609910128b2031f61840403a291219502f15ace246ed2321810268742051e1505e2290f2023c25804c097683061050c44529647c530183214c511, 0xa187019e073b295148e0568200644470574930c00e08d25c406842004c00a530c091284da6c650089438a1e88a008660841801a438032883cf12f8608325610008c5010c832242),
 (0x315a073db0103101501af2385c4c98100469a43645220088e342d300c484c95905a9c6cfe00120b115481180729d0951ca9001826373012814084019afa11140068d3ac92c01058, 0xc000842420d0a3a81450183212104ac52940a0130844d1218a12449180836000200191005d48d422086ac568402b0aa142f00109004e084627309e00046c214b9208502c03c401),
 (0x10804256a89200a0ae0040f840130e02200150001410d0048072321700291a5a44ec9621200418a442ca398564858428508e694409640030804054ce64c05097a29154aac362600, 0xc69208801442b4001e08300aa44200d1b582323e0ae0623168d4068da92e181910208ce9853c313a900847218487a44a1009631948b668576a0a900190ba0484d680155048d180),
 (0xdc42921019f2ea60a1e059eb0ca802029841130021f0550440c100980ba464205d9808ed3ea480bc3060816504132fe3960025405b0380e9c28c50a0031198205a141402202208, 0x300946429c20d0193001da40403070d0d21b6cc2cc00288aa31226e2290028a4a004616020048294000025c8239ccc00009bac80d84a4040025412941180c40162180cb2d0c4c63),
 (0x140a0d032060870b65220281410b8107481180000bc105208d3aa4d140900a80ba7a1a0e86fe2500d1e6a07884c181cc0e7c01304207049118002994440810018882c4302806e2c, 0x9d04078000a10d012ccc8001e6432c0970a617c4032ba483281510c0b444058058521812801c2a1280150844b2c6c231180bec490381b68c07a560ba8902272163832069000080),
 (0x30080c020081e01130e38540f2613a010204225cf8a6502dcdcc2232c06c13984162227832d4839100ab9160722095804f70453e0182167d70806111b8450d40cc04448070d0223, 0x82232b165481586c9102a1a051284bc99615c0304590c02201351c828936c268a9d85864c226028374068860c98624c208182c14c4c09828f1388c647b8f29900a213100f25944),
 (0xce6090385298a001202815eadb2314c4021205801d404130404020e05881430269208141130d41805322b1d58a9b33001025008c88103082136c20b29d4923c4ae30b0c20a01a3, 0x120040547080202a2dfc30a15008c23239c64585a62350c490538920ba57a2c3102571ebcaca2be0d84540e0a106008efa6cac213116fc835e4039b0860a01413100d0b3174c040),
 (0x6dbc02ac1c4419157ab231a0a09081a50a784722c080c58216a5021a9c101dd25b0e801800142a2a00b026556cb40c122839c2b0009d3c4dc744089e061461146589b11812ac6f, 0x82405803c2a3c0c80101cc035a2f3450610220900558383469526d844344e000202141e1a5a301548c0918080000806c56c41c426442c2021018904161c982008a040805ec5300),
 (0x381651486408c058224660444a611855c6761d491025132386caa9ed90c82f6f0cb0a092401e0613260a154991cdbc04392f009f845cc258025c000807402953bbd0321c53bc16e, 0x1a826b5127725a380191438341a63a83008a282c7ca0c5c683010106d105000e3405f451920b8ec589468a0642202a3c4904e0009030420a4839587608600a4442c80000c01a11),
 (0,0),  (0xa84a880a800054054c82af3820240216d020248009078419e18c0628e78710ca6602b8840d65152d0e200747335874813201005912910e032add048a22dc5c4cb0670b26344778, 0x147a125211e6e2aaa906400c486d0b1482a54db0c242023260823b00010788310080d405bf000c0d050068810cc260b160c5e7324882cc1dcc022a9609502a2320f08a488821004),
 (0x21003009610400521674009a4904ac0120619b66802215d8304360298f148484c5085bdda086180e051e8c4218e5a8e0240056a0460263a1a82c28c0289682100b1a0c49c268301, 0x26d81f014f04009490b1f2432d9114a5a8424915b1dca204d1c820440a13b7b00930420017101118a20738cc1080417904c8942b1d1101e410096171029456ca40420123016442),
 (0x408b90a7500761c904188586a1fc106222084813c805ece4800654d04c02432d8885c04c0a0c2ba1044a52068475064385780100046973d0000166428744e505a02a14a222ec90, 0x1b5600d48a1e89e148a233248500209150c25972824a2020051f9aa248049b48061501b9040e10440281109a86380e8887000c255121008208dec1985588008da5f11ea51990342)],
  #[
 (0x220005105099c2200902909f90e20602040030d8999c68242040f911306712090440aa298d09503293807444082608519a84e4846023a091e21135a608479244270c00180e8621c, 0xca2e062862435dfc2a420002c012964a189c8030441145a802800648d1088a0b90e04d2500608010817809bf5499600443011790d10126e19400250309049abc8c3a4227050043),
 (0x9a591854021cf098c08f460c00110c42701239020ca9000882230182085c5c0008960100c09706175444164c238c76480835032f00a00890b431660c6226b3d45102d2488a2611, 0x104a461823ce209222900b8b21c6c83000ba4c625735286f3781c76704401234d4261bace0f0859802aa9c100c4520895808848806854e724004899530d8840210c4d0993258900),
 (0x262128601a1e293f6ca0304286100aba0a384006544ac3e10e20140185102013023e0a43a8a41304ab430216ce86e3c223ac4698bc5d415659a6fb592cc88183232b20a191bd030, 0x104a070220a014c0911c8c91510f6001d40423902b342c024102808452a6cb28510130b804110022042034403059180d5403006743201c898601040453041848c8d4890a42408cd),
 (0x20a0170c168ac045f03822f02882190ed8583a500bf3f84c138f0323169012d2a132028365402683111a313240000ae41a800c09188003c45131047c300119f8c8821ecaa002004, 0xa56e85268440d300bc3540bd73962302484842d84040300c83020d4402865010644653c102bc93ce2c1040008b6e108257bb310e1278c202048580305ec860337404125157d0b8),
 (0xa00884e806535006d15122c03050906a640c12301cad50a126d1604010003800a8598f354801165acb0220002ae01e3a510aab145088894a89a30d68085a2d02c08a109a000105, 0x249746311c90c02000c2c942e05294110027209cda240a80a990a87aecb4dc66506821048b642e1002014480a54154105aad410880b4110a5041c82166224d2f404454165a53a50),
 (0x26a3c620441410ea120a2886004e04be0296d00c00453805160135f0742a08681ea8491c02420f0100a009818b2192491d8808b60b4021086511100fc99ba8bb6242711da6c9904, 0x844381aa949631469d10708b9903b0124402c301a9806ea899ac8020a1001908041b06191900026e54fa65c44524496a0116708540a44918a24eaf00464160419388e2001040b8),
 (0x3643363ae869c11421d80b625ba9a42808aa822501880288a850583494700868514888046f2aab22001490a02448531882010600b001180500170c50681475e4b0600033a80b553, 0x440214248b1e00a48da456121327405cd0ce15cc70502602894a8a621182027442900040911980205803a0a42315902071004ae4ea36a8e3a417428819461201401500a28),
 (0, 0)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[17+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

private def rows : Array ℕ := #[
  13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 37, 38, 39, 40,
  41, 42, 43, 45, 46, 47, 49, 50, 51, 52, 53, 54, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 68, 69,
  70, 71, 72, 73, 74, 75, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 94, 95,
  96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 123,
  124, 125, 126, 127, 128, 129, 130, 131, 143, 146, 147, 148, 149, 150, 151, 152, 153, 154, 156, 158, 159, 160, 161, 162,
  163, 164, 165, 167, 168, 170, 171, 172, 173, 174, 175, 176, 178, 179, 180, 182, 183, 184, 185, 186, 187, 189, 190, 191,
  192, 193, 194, 195, 196, 197, 198, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 211, 212, 213, 214, 215, 216, 217,
  218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 233, 234, 235, 236, 237, 238, 239, 240, 241, 243, 245,
  246, 247, 248, 249, 250, 251, 252, 253, 256, 257, 258, 259, 260, 261, 262, 263, 275, 276, 279, 280, 281, 282, 283, 284,
  285, 286, 287, 289, 291, 292, 293, 294, 295, 296, 297, 298, 300, 301, 303, 304, 305, 306, 307, 308, 309, 311, 312, 313,
  314, 315, 316, 317, 318, 319, 320, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 333, 334, 335, 336, 337, 338, 339,
  340, 341, 342, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 355, 356, 357, 358, 359, 360, 361, 362, 364, 365, 367,
  368, 369, 370, 371, 372, 373, 374, 376, 378, 379, 380, 381, 382, 383, 384, 385, 386, 389, 390, 391, 392, 393, 394, 395,
  407, 408, 409, 412, 413, 414, 415, 416, 417, 418, 419, 420, 422, 424, 425, 426, 427, 428, 429, 430, 431, 433, 434, 435,
  436, 437, 438, 439, 440, 441, 442, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 455, 456, 457, 458, 459, 460, 461,
  462, 463, 464, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 477, 478, 479, 480, 481, 482, 483, 485, 486, 487, 489,
  490, 491, 492, 493, 494, 495, 497, 498, 500, 501, 502, 503, 504, 505, 506, 507, 509, 511, 512, 513, 514, 515, 516, 517,
  518, 519, 522, 523, 524, 525, 526, 527, 539, 540, 541, 542, 545, 546, 547, 548, 549, 550, 551, 552, 553, 555, 556, 557,
  558, 559, 560, 561, 562, 563, 564, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 577, 578, 579, 580, 581, 582, 583,
  584, 585, 586, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 599, 600, 601, 602, 603, 604, 606, 607, 608, 609, 611,
  612, 613, 614, 615, 616, 618, 619, 620, 622, 623, 624, 625, 626, 627, 628, 630, 631, 633, 634, 635, 636, 637, 638, 639,
  640, 642, 644, 645, 646, 647, 648, 649, 650, 651, 652, 655, 656, 657, 658, 659, 671, 672, 673, 674, 675, 677, 678, 679,
  680, 681, 682, 683, 684, 685, 686, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 699, 700, 701, 702, 703, 704, 705,
  706, 707, 708, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 721, 722, 723, 724, 725]

private def reverseRows : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 9,
  0, 10, 11, 12, 13, 14, 15, 16, 17, 0, 18, 19, 0, 20, 21, 22, 23, 24, 25, 26, 0, 27, 28, 29,
  0, 30, 31, 32, 33, 34, 35, 0, 36, 37, 38, 39, 0, 40, 41, 42, 43, 44, 0, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 0, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 0, 65, 66, 67, 68, 69, 70, 71,
  72, 73, 74, 0, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 0, 85, 86, 87, 88, 89, 90, 91, 92, 93,
  94, 0, 0, 95, 96, 97, 98, 99, 100, 101, 102, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104,
  0, 0, 105, 106, 107, 108, 109, 110, 111, 112, 113, 0, 114, 0, 115, 116, 117, 118, 119, 120, 121, 122, 0, 123,
  124, 0, 125, 126, 127, 128, 129, 130, 131, 0, 132, 133, 134, 0, 135, 136, 137, 138, 139, 140, 0, 141, 142, 143,
  144, 145, 146, 147, 148, 149, 150, 0, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 0, 161, 162, 163, 164, 165,
  166, 167, 168, 169, 170, 0, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 0, 181, 182, 183, 184, 185, 186, 187,
  188, 189, 0, 190, 0, 191, 192, 193, 194, 195, 196, 197, 198, 199, 0, 0, 200, 201, 202, 203, 204, 205, 206, 207,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 209, 0, 0, 210, 211, 212, 213, 214, 215, 216, 217, 218,
  0, 219, 0, 220, 221, 222, 223, 224, 225, 226, 227, 0, 228, 229, 0, 230, 231, 232, 233, 234, 235, 236, 0, 237,
  238, 239, 240, 241, 242, 243, 244, 245, 246, 0, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 0, 257, 258, 259,
  260, 261, 262, 263, 264, 265, 266, 0, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 0, 277, 278, 279, 280, 281,
  282, 283, 284, 0, 285, 286, 0, 287, 288, 289, 290, 291, 292, 293, 294, 0, 295, 0, 296, 297, 298, 299, 300, 301,
  302, 303, 304, 0, 0, 305, 306, 307, 308, 309, 310, 311, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 312,
  313, 314, 0, 0, 315, 316, 317, 318, 319, 320, 321, 322, 323, 0, 324, 0, 325, 326, 327, 328, 329, 330, 331, 332,
  0, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 0, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 0, 353,
  354, 355, 356, 357, 358, 359, 360, 361, 362, 0, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 0, 373, 374, 375,
  376, 377, 378, 379, 0, 380, 381, 382, 0, 383, 384, 385, 386, 387, 388, 389, 0, 390, 391, 0, 392, 393, 394, 395,
  396, 397, 398, 399, 0, 400, 0, 401, 402, 403, 404, 405, 406, 407, 408, 409, 0, 0, 410, 411, 412, 413, 414, 415,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 416, 417, 418, 419, 0, 0, 420, 421, 422, 423, 424, 425, 426,
  427, 428, 0, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 0, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448,
  0, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 0, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 0, 469,
  470, 471, 472, 473, 474, 0, 475, 476, 477, 478, 0, 479, 480, 481, 482, 483, 484, 0, 485, 486, 487, 0, 488, 489,
  490, 491, 492, 493, 494, 0, 495, 496, 0, 497, 498, 499, 500, 501, 502, 503, 504, 0, 505, 0, 506, 507, 508, 509,
  510, 511, 512, 513, 514, 0, 0, 515, 516, 517, 518, 519, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 520,
  521, 522, 523, 524, 0, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 0, 535, 536, 537, 538, 539, 540, 541, 542,
  543, 544, 0, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 0, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564,
  0, 565, 566, 567, 568, 569]

end BasisSeed11

namespace BasisSeed11

private def row (s : ℕ) : Fin 6 × Fin 11 × Fin 11 :=
  (squareCode 6 11).symm (Fin.ofNat _ (rows[s]?.getD 0))

private def index (i : Fin 6) (j k : Fin 11) : Fin 570 :=
  Fin.ofNat _ (reverseRows[(squareCode 6 11 (i,j,k)).val]?.getD 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
private theorem covered :
    ∀ (i : Fin 6) (j k : Fin 11),
      (∃ t : Fin 6, headHit t i j k) ∨ row (index i j k).val = (i,j,k) := by
  decide +kernel

private abbrev Check (s : ℕ) : Prop :=
  imageRow 6 11 11 22 x y z inverse (row s).1.val (row s).2.1.val (row s).2.2.val =
    (2 ^ s, 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid0 : ∀ s : Fin 57, Check (0*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid1 : ∀ s : Fin 57, Check (1*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid2 : ∀ s : Fin 57, Check (2*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid3 : ∀ s : Fin 57, Check (3*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid4 : ∀ s : Fin 57, Check (4*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid5 : ∀ s : Fin 57, Check (5*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid6 : ∀ s : Fin 57, Check (6*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid7 : ∀ s : Fin 57, Check (7*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid8 : ∀ s : Fin 57, Check (8*57+s.val) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem valid9 : ∀ s : Fin 57, Check (9*57+s.val) := by
  decide +kernel

private theorem valid (s : Fin 570) : Check s.val := by
  obtain ⟨⟨q,t⟩,rfl⟩ := (finProdFinEquiv : Fin 10 × Fin 57 ≃ Fin 570).surjective s
  change Check (t.val + 57*q.val)
  rw [Nat.add_comm, Nat.mul_comm]
  fin_cases q
  · exact valid0 t
  · exact valid1 t
  · exact valid2 t
  · exact valid3 t
  · exact valid4 t
  · exact valid5 t
  · exact valid6 t
  · exact valid7 t
  · exact valid8 t
  · exact valid9 t

private theorem spanWitness : Spans 6 11 11 28 := by
  apply fill_basis (by decide) (fun s : Fin 570 => row s.val) ?_ _ _ _
    (checked (fun s : Fin 570 => row s.val) Fin.val Fin.val_injective x y z inverse valid)
  intro i j k
  exact (covered i j k).imp_right (fun h => ⟨index i j k,h⟩)

end BasisSeed11

private lemma square11 : Spans 6 11 11 28 := BasisSeed11.spanWitness

namespace GridCell

private def points : Array (Array ℕ) := #[
  #[2, 0, 0, 0, 0, 2, 1, 1, 2, 1],
  #[1, 1, 2, 1, 2, 1, 0, 0, 2, 2],
  #[1, 0, 1, 1, 0, 1, 0, 0, 1, 0],
  #[0, 0, 1, 0, 2, 2, 0, 0, 2, 2],
  #[0, 0, 0, 1, 2, 2, 0, 0, 0, 1],
  #[2, 2, 1, 0, 0, 0, 0, 1, 0, 0],
  #[0, 1, 2, 0, 2, 1, 2, 1, 0, 0],
  #[2, 2, 1, 0, 1, 0, 2, 0, 0, 0],
  #[1, 1, 2, 1, 0, 2, 1, 2, 0, 0]]

private def inverses : Array (Array Packed) := #[
  #[
 (0x99993, 0x66604),
 (0x996946, 0x669689),
 (0x4865c0, 0xa20039),
 (0x3a050, 0xcc592f),
 (0x9840fa, 0x3a904),
 (0xc09f06, 0x100099),
 (0x909069, 0x606096),
 (0,0),  (0xcf020, 0x330650),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x33333, 0xccc0c),
 (0x33c14c, 0xcc34a3),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0xcf040, 0x33091f),
 (0xcff30, 0x3300cf),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x330a2f, 0xcf150),
 (0x33000f, 0xcf3f0),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x3, 0xfcf0c),
 (0xff0003, 0x3ff0),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x312933, 0xc486cc),
 (0x88013, 0x3520a0),
 (0,0),  (0,0),  (0,0),  (0, 0)],
  #[
 (0,0),  (0,0),  (0,0),  (0,0),  (0x909918, 0x606642),
 (0x606014, 0x909041),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x141624, 0x414981),
 (0x524084, 0x25105a),
 (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0,0),  (0x302303, 0xc08c0c),
 (0xcf680f, 0x9260)]]

private def x (t i : ℕ) : ℕ := (points[t]?.getD #[])[i]?.getD 0
private def y (t j : ℕ) : ℕ := (points[t]?.getD #[])[6+j]?.getD 0
private def z (t k : ℕ) : ℕ := (points[t]?.getD #[])[8+k]?.getD 0
private def inverse (j : ℕ) : Packed := (inverses[j/32]?.getD #[])[j%32]?.getD (0,0)

end GridCell
namespace GridCell

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check0 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 0 j.val k.val =
      (2 ^ (squareCode 6 2 (0,j,k)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check1 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 1 j.val k.val =
      (2 ^ (squareCode 6 2 (1,j,k)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check2 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 2 j.val k.val =
      (2 ^ (squareCode 6 2 (2,j,k)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check3 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 3 j.val k.val =
      (2 ^ (squareCode 6 2 (3,j,k)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check4 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 4 j.val k.val =
      (2 ^ (squareCode 6 2 (4,j,k)).val, 0) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem check5 :
    ∀ j k : Fin 2, imageRow 6 2 2 9 x y z inverse 5 j.val k.val =
      (2 ^ (squareCode 6 2 (5,j,k)).val, 0) := by
  decide +kernel

private theorem valid : ∀ s : Fin 6 × Fin 2 × Fin 2,
    imageRow 6 2 2 9 x y z inverse s.1.val s.2.1.val s.2.2.val =
      (2 ^ (squareCode 6 2 s).val, 0) := by
  rintro ⟨i,j,k⟩
  fin_cases i
  · exact check0 j k
  · exact check1 j k
  · exact check2 j k
  · exact check3 j k
  · exact check4 j k
  · exact check5 j k

end GridCell

private def gridSlot (g h : Fin 5) : ℕ := if h = 0 then g.val else 4+h.val

private def gridParams (p : SixSliceTensor.Grid.Parameters (Fin 5) (Fin 6) 1 2) : ℂ :=
  let t := gridSlot p.1.1 p.1.2.1
  p.2.elim (fun j => (GridCell.y t j.val : ℂ))
    (Sum.elim (fun k => (GridCell.z t k.val : ℂ)) (fun i => (GridCell.x t i.val : ℂ)))

private def leftSlot (g : Fin 5) : Fin 9 := g.castLE (by decide)

private def rightSlot (h : Fin 5) : Fin 9 :=
  if h = 0 then 0 else ⟨4+h.val, by omega⟩

private lemma leftValue (g : Fin 5) : (leftSlot g).val = gridSlot g 0 := by
  simp [leftSlot, gridSlot]

private lemma rightValue (h : Fin 5) : (rightSlot h).val = gridSlot 0 h := by
  by_cases hh : h = 0 <;> simp [rightSlot, gridSlot, hh]

private lemma yOff : ∀ t : Fin 4, ∀ j : Fin 2, GridCell.y (t.val+1) j.val = 0 := by
  decide +kernel

private lemma zOff : ∀ t : Fin 4, ∀ k : Fin 2, GridCell.z (t.val+5) k.val = 0 := by
  decide +kernel

private lemma square10 : Spans 6 10 10 25 := by
  apply SixSliceTensor.Grid.spans_of_cell (g:=5) (d:=2) (s:=1) (a:=6) gridParams
  have hr := checked id (fun s => (squareCode 6 2 s).val)
    (fun _ _ h => (squareCode 6 2).injective (Fin.ext h))
    GridCell.x GridCell.y GridCell.z GridCell.inverse GridCell.valid
  intro T
  obtain ⟨u,v,w,hw⟩ := covers_of_rank hr (fun i j k => T j k i)
  refine ⟨fun g _ => v (leftSlot g), fun h _ => w (rightSlot h), fun _ => u 0, ?_⟩
  intro j k i
  rw [hw i j k]
  simp only [SixSliceTensor.Grid.aval, SixSliceTensor.Grid.bval, SixSliceTensor.Grid.cval, gridParams,
    Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, ← leftValue, ← rightValue]
  have y₁ := yOff 0 j
  have y₂ := yOff 1 j
  have y₃ := yOff 2 j
  have y₄ := yOff 3 j
  have z₅ := zOff 0 k
  have z₆ := zOff 1 k
  have z₇ := zOff 2 k
  have z₈ := zOff 3 k
  change GridCell.y 1 j.val = 0 at y₁
  change GridCell.y 2 j.val = 0 at y₂
  change GridCell.y 3 j.val = 0 at y₃
  change GridCell.y 4 j.val = 0 at y₄
  change GridCell.z 5 k.val = 0 at z₅
  change GridCell.z 6 k.val = 0 at z₆
  change GridCell.z 7 k.val = 0 at z₇
  change GridCell.z 8 k.val = 0 at z₈
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [leftSlot, rightSlot, y₁, y₂, y₃, y₄, z₅, z₆, z₇, z₈]
  ring


private lemma crossSix : Cross 6 2 6 := by
  classical
  let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
  let x₁ (t i : Fin 6) : ℂ := if i = e ((e.symm t).1,0) then 1 else 0
  let x₂ (t i : Fin 6) : ℂ := if i = e ((e.symm t).1,1) then 1 else 0
  let s (t : Fin 6) (j : Fin 2) : ℂ := if j = (e.symm t).2 then 1 else 0
  refine ⟨x₁,x₂,s,s,?_⟩
  intro T
  refine ⟨fun t j => T (e ((e.symm t).1,1)) j (e.symm t).2,
    fun t k => T (e ((e.symm t).1,0)) (e.symm t).2 k, ?_⟩
  intro i j k
  obtain ⟨⟨p,q⟩, rfl⟩ := e.surjective i
  rw [← e.sum_comp, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases q <;>
    simp [x₁,x₂,s,ite_mul,mul_ite,Finset.sum_ite_eq]

private lemma ceiling_between {n d q : ℕ} (hd : 0<d) (hlo : d*q<n) (hhi : n≤d*(q+1)) :
    n ⌈/⌉ d=q+1 := by
  refine le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr hhi) ?_
  by_contra! h
  exact (not_le_of_gt hlo) ((ceilDiv_le_iff_le_mul hd).mp (show n ⌈/⌉ d ≤ q by omega))

private lemma six_square (m : ℕ) (hm : 6 ≤ m) : Spans 6 m m (6*m*m ⌈/⌉ (6+m+m-2)) := by
  by_cases small : m < 10
  · interval_cases m
    · exact square6
    · exact square7
    · exact grow 6 6 2 14 6 1 square6 Format6Border.spans crossSix
    · exact grow 6 7 2 17 6 1 square7 Format7Border.spans crossSix
  · by_cases even : m % 2 = 0
    · obtain ⟨t,rfl⟩ : ∃ t, m = 10+2*t := ⟨(m-10)/2,by omega⟩
      have den : 6+(10+2*t)+(10+2*t)-2 = 24+4*t := by omega
      rw [den]
      have num : 6*(10+2*t)*(10+2*t) ⌈/⌉ (24+4*t) = 25+6*t := by
        convert ceiling_between (n:=6*(10+2*t)*(10+2*t)) (d:=24+4*t) (q:=24+6*t)
          (by omega) (by nlinarith) (by nlinarith) using 1 <;> omega
      rw [num]
      exact grow 6 10 2 25 6 t square10 Format10Border.spans crossSix
    · obtain ⟨t,rfl⟩ : ∃ t, m = 11+2*t := ⟨(m-11)/2,by omega⟩
      have den : 6+(11+2*t)+(11+2*t)-2 = 26+4*t := by omega
      rw [den]
      have num : 6*(11+2*t)*(11+2*t) ⌈/⌉ (26+4*t) = 28+6*t := by
        convert ceiling_between (n:=6*(11+2*t)*(11+2*t)) (d:=26+4*t) (q:=27+6*t)
          (by omega) (by nlinarith) (by nlinarith) using 1 <;> omega
      rw [num]
      exact grow 6 11 2 28 6 t square11 Format11Border.spans crossSix


end SixSliceCertificate

namespace SixSliceBoundary

/-- The pivot is supported at the first coordinate of both factors. Each other
point supplies one entry outside the first row and column. -/
private lemma slice_witness (p q : ℕ) (t : Fin (p*q+1)) :
    ∃ x : Fin (p*q+1) → Fin (p+1) → ℂ, ∃ y : Fin (p*q+1) → Fin (q+1) → ℂ,
      ∀ M : Fin (p+1) → Fin (q+1) → ℂ, ∃ u : Fin (p+1) → ℂ, ∃ v : Fin (q+1) → ℂ,
        ∃ w : Fin (p*q+1) → ℂ, ∀ i j,
          M i j = u i * y t j + x t i * v j + ∑ s, w s * (x s i * y s j) := by
  let e : Fin (p*q+1) ≃ Option (Fin p × Fin q) :=
    (finSuccEquiv' t).trans (Equiv.optionCongr finProdFinEquiv.symm)
  have ht : e t = none := by simp [e]
  let X : Option (Fin p × Fin q) → Fin (p+1) → ℂ
    | none, i => if i = 0 then 1 else 0
    | some z, i => if z.1.succ = i then 1 else 0
  let Y : Option (Fin p × Fin q) → Fin (q+1) → ℂ
    | none, j => if j = 0 then 1 else 0
    | some z, j => if z.2.succ = j then 1 else 0
  refine ⟨fun s => X (e s), fun s => Y (e s), ?_⟩
  intro M
  let W : Option (Fin p × Fin q) → ℂ
    | none => 0
    | some z => M z.1.succ z.2.succ
  refine ⟨fun i => M i 0, fun j => if j = 0 then 0 else M 0 j, fun s => W (e s), ?_⟩
  intro i j
  dsimp only
  rw [ht, e.sum_comp (fun z => W z * (X z i * Y z j))]
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [X, Y, W, Fintype.sum_option, Fintype.sum_prod_type, mul_ite, Finset.sum_ite_eq']

open MvPolynomial SixSliceTensor.Growth

/-- A common choice of factors spans every marked matrix slice. -/
private lemma shared_slices (p q : ℕ) :
    ∃ x : Fin (p*q+1) → Fin (p+1) → ℂ, ∃ y : Fin (p*q+1) → Fin (q+1) → ℂ,
      ∀ t : Fin (p*q+1), ∀ M : Fin (p+1) → Fin (q+1) → ℂ,
        ∃ u : Fin (p+1) → ℂ, ∃ v : Fin (q+1) → ℂ, ∃ w : Fin (p*q+1) → ℂ,
          ∀ i j, M i j = u i * y t j + x t i * v j + ∑ s, w s * (x s i * y s j) := by
  classical
  let a := p+1
  let b := q+1
  let r := p*q+1
  let V := Fin r × (Fin a ⊕ Fin b)
  let I := Fin a × Fin b
  let J := Fin a ⊕ (Fin b ⊕ Fin r)
  let A (t : Fin r) : Matrix I J (MvPolynomial V ℂ) := fun (i,j) k =>
    match k with
    | .inl v => if v=i then X (t,.inr j) else 0
    | .inr (.inl v) => if v=j then X (t,.inl i) else 0
    | .inr (.inr s) => X (s,.inl i) * X (s,.inr j)
  have action (t : Fin r) (p : V → ℂ) (q : J → ℂ) (i : Fin a) (j : Fin b) :
      ((A t).map (eval p)).mulVec q (i,j) =
        q (.inl i) * p (t,.inr j) + p (t,.inl i) * q (.inr (.inl j)) +
          ∑ s, q (.inr (.inr s)) * (p (s,.inl i) * p (s,.inr j)) := by
    change (∑ k : J, eval p (A t (i,j) k) * q k) = _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [A,apply_ite,ite_mul,Finset.sum_ite_eq',mul_comm,mul_assoc,add_assoc]
  have span_iff (t : Fin r) (p : V → ℂ) :
      (∀ M : Fin a → Fin b → ℂ, ∃ u : Fin a → ℂ, ∃ v : Fin b → ℂ, ∃ w : Fin r → ℂ,
        ∀ i j, M i j = u i * p (t,.inr j) + p (t,.inl i) * v j +
          ∑ s, w s * (p (s,.inl i) * p (s,.inr j))) ↔
        Function.Surjective ((A t).map (eval p)).mulVec := by
    constructor
    · intro hs T
      obtain ⟨u,v,w,hw⟩ := hs fun i j => T (i,j)
      refine ⟨Sum.elim u (Sum.elim v w),?_⟩
      funext ⟨i,j⟩
      rw [action]
      exact (hw i j).symm
    · intro hA T
      obtain ⟨q,hq⟩ := hA fun ij => T ij.1 ij.2
      refine ⟨fun i => q (.inl i),fun j => q (.inr (.inl j)),fun s => q (.inr (.inr s)),?_⟩
      intro i j
      exact (congrFun hq (i,j)).symm.trans (action t p q i j)
  have each (t : Fin r) : ∃ p : V → ℂ, Function.Surjective ((A t).map (eval p)).mulVec := by
    obtain ⟨x,y,ht⟩ := slice_witness p q t
    let p (z : V) := z.2.elim (x z.1) (y z.1)
    exact ⟨p,(span_iff t p).mp ht⟩
  choose u hu using each
  choose Q hQ hgood using fun t => surjectivity_polynomial (A t) (u t) (hu t)
  have hprod : (∏ t, Q t) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hQ t
  obtain ⟨s,hs⟩ := CriticalReduction.Grid.nonvanishing (∏ t, Q t) _ hprod le_rfl
  let v (k : V) : ℂ := ((s k).val : ℂ)
  have hvals : (∏ t, eval v (Q t)) ≠ 0 := by simpa only [v,map_prod] using hs
  exact ⟨fun t i => v (t,.inl i),fun t j => v (t,.inr j),
    fun t => (span_iff t v).mpr (hgood t v (Finset.prod_ne_zero_iff.mp hvals t (Finset.mem_univ t)))⟩

/-- At the critical boundary there is an integer-grid tangent witness at the
dimension-count ceiling, with the same factor bound as the remaining formats. -/
private lemma boundary_witness {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : c = (a-1)*(b-1)) :
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k)) := by
  classical
  subst c
  dsimp only
  rw [Arxiv.«0805.3777».critical_ceilDiv ha hb]
  obtain _ | p := a
  · omega
  obtain _ | q := b
  · omega
  let c := p*q
  obtain ⟨x,y,hxy⟩ := shared_slices p q
  apply CriticalReduction.bounded_of_witness (a:=p+1) (b:=q+1) (c:=c) (r:=c+1)
  let z : Fin (c+1) → Fin c → ℂ := fun t k => if t = k.succ then 1 else 0
  refine ⟨x,y,z,?_⟩
  intro T
  choose u v w hw using fun k : Fin c => hxy k.succ (fun i j => T i j k)
  let U : Fin (c+1) → Fin (p+1) → ℂ := Fin.cases 0 u
  let V : Fin (c+1) → Fin (q+1) → ℂ := Fin.cases 0 v
  refine ⟨U,V,fun t k => w k t,?_⟩
  intro i j k
  have hU : (∑ t, U t i * (y t j * z t k)) = u k i * y k.succ j := by
    simp [z, U, mul_ite, Finset.sum_ite_eq']
  have hV : (∑ t, x t i * (V t j * z t k)) = x k.succ i * v k j := by
    simp [z, V, mul_ite, Finset.sum_ite_eq']
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hU, hV, hw k i j]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

end SixSliceBoundary

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2

/-- The admissible strict-interior square-ended formats with first dimension other than five or six. -/
def H1 : Prop :=
  ∀ a m : ℕ, 3 ≤ a → a ≤ m → m < (a-1)*(m-1) →
    (∀ p : ℕ, (a,m,m) ≠ (3,2*p+1,2*p+1)) → a ≠ 5 → a ≠ 6 →
    let r := a*m*m ⌈/⌉ (a+m+m-2)
    let D := 2*(a*m*m)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin m → Fin D, ∃ z : Fin r → Fin m → Fin D,
      ∀ T : Fin a → Fin m → Fin m → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin m → ℂ,
        ∃ w : Fin r → Fin m → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

/-- The strict-interior formats with unequal final dimensions. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 3 ≤ a → a ≤ b → b < c → c < (a-1)*(b-1) →
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.H2 := by
  intro hs hr a b c ha hab hbc hc hexc h₅
  by_cases edge : c = (a-1)*(b-1)
  · exact SixSliceBoundary.boundary_witness ha (by omega) edge
  have interior := lt_of_le_of_ne hc edge
  by_cases eq : b = c
  · subst c
    by_cases six : a = 6
    · subst a
      exact CriticalReduction.bounded_of_witness (SixSliceCertificate.six_square b hab)
    · exact hs a b ha hab interior hexc (h₅.resolve_right (fun h => h rfl)) six
  · exact hr a b c ha hab (lt_of_le_of_ne hbc eq) interior

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2
