import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1

/-! An unrestricted last-slice test for the strict rectangular formats of Friedland's conjecture.

For fixed first and second dimensions a and b, the first strictly rectangular size is c=b+1.
At each subsequent admissible size, form the tangent matrix over the rational function
field on all independent factor coordinates. Deleting the final slice leaves the old rows.
The exact increment is the dimension of the last-slice image of the kernel of the old rows.

A previous spanning configuration pads to a surjection onto the old rows. Thus a gain of
ab is both necessary and sufficient for the full Jacobian to span. A generic full row
rank is equivalent to a complex full-row-rank specialization, and the parent supplies
bounded integer factors. The two hypotheses are proved equivalent to the parent target.

This construction permits every original derivative column to vary. The anchored border
condition in alternative reduction #6570 fails at (3,320,330); that condition is unnecessary
here. The increment still has to be established at every remaining admissible size.
See Friedland, Conjecture 5.1, https://arxiv.org/abs/0805.3777. -/

namespace CriticalTensor.Unrestricted

private lemma surjective_of_multiplier {I J F : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field F]
    (A : Matrix I J F) (B : Matrix J I F) (h : (A*B).det ≠ 0) : Function.Surjective A.mulVec := by
  have onto : Function.Surjective (A*B).mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  intro y
  obtain ⟨u,hu⟩ := onto y
  exact ⟨B.mulVec u,(Matrix.mulVec_mulVec _ _ _).trans hu⟩

/-- A polynomial matrix spans over the rational function field exactly when it spans
at some complex point. Denominators of a generic right inverse may be cleared simultaneously. -/
lemma generic_surjective_iff {I J V : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) :
    Function.Surjective (M.map (algebraMap (MvPolynomial V ℂ) (FractionRing (MvPolynomial V ℂ)))).mulVec ↔
      ∃ x : V → ℂ, Function.Surjective (M.map (MvPolynomial.eval x)).mulVec := by
  classical
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  change Function.Surjective (M.map φ).mulVec ↔ _
  constructor
  · intro h
    obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
    obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun z : J × I => B z.1 z.2)
    have clear_entry (j : J) (i : I) : ∃ p : R, φ p = (d : R) • B j i := hd (j,i)
    choose v hv using clear_entry
    let P : Matrix J I R := Matrix.of v
    have mul_d : P.map φ = φ (d : R) • B := by
      ext j i
      simpa only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Algebra.smul_def,P,Matrix.of_apply] using hv j i
    have hd₀ : φ (d : R) ≠ 0 := fun h => nonZeroDivisors.ne_zero d.property (inj (h.trans φ.map_zero.symm))
    have det_eq : φ (M*P).det = (φ (d : R)) ^ Fintype.card I := by
      rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,mul_d,Matrix.mul_smul,hB,Matrix.det_smul,
        Matrix.det_one,mul_one]
    have hdet : (M*P).det ≠ 0 := by
      intro hz
      rw [hz,map_zero] at det_eq
      exact pow_ne_zero _ hd₀ det_eq.symm
    obtain ⟨v,hv⟩ := CriticalReduction.Grid.nonvanishing (M*P).det _ hdet le_rfl
    let x : V → ℂ := fun i => ((v i).val : ℂ)
    refine ⟨x,surjective_of_multiplier _ (P.map (MvPolynomial.eval x)) ?_⟩
    rw [← Matrix.map_mul,← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact hv
  · rintro ⟨x,h⟩
    obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
    let P := B.map (MvPolynomial.C : ℂ →+* R)
    have hP : P.map (MvPolynomial.eval x) = B := by ext j i; simp [P,Matrix.map_apply]
    have hdet : (M*P).det ≠ 0 := by
      have he : MvPolynomial.eval x (M*P).det = 1 := by
        rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,hP,hB,Matrix.det_one]
      intro hz
      rw [hz,map_zero] at he
      exact zero_ne_one he
    apply surjective_of_multiplier _ (P.map φ)
    rw [← Matrix.map_mul,← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact fun h₀ => hdet (inj (h₀.trans φ.map_zero.symm))

end CriticalTensor.Unrestricted

namespace UnrestrictedSlice

open Module Submodule
open LinearMap (range ker range_eq_top)

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- A finite matrix maps onto all row coordinates exactly when its rank is their cardinality. -/
lemma surjective_iff_row_card (M : Matrix I J K) :
    Function.Surjective M.mulVec ↔ M.rank = Fintype.card I := by
  classical
  change Function.Surjective M.mulVecLin ↔ finrank K (range M.mulVecLin) = Fintype.card I
  rw [← range_eq_top]
  constructor
  · intro h
    rw [h,finrank_top,finrank_pi]
  · intro h
    apply eq_top_of_finrank_eq
    simpa only [finrank_pi] using h

omit [Fintype I] in
/-- Retaining the first `c` slices of a surjective tangent keeps those rows surjective. -/
lemma old_surjective {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) (h : Function.Surjective M.mulVec) :
    Function.Surjective (M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id).mulVec := by
  intro y
  let total (z : I × Fin (c+1)) : K := Fin.lastCases 0 (fun k => y (z.1,k)) z.2
  obtain ⟨v,hv⟩ := h total
  refine ⟨v,?_⟩
  funext z
  rcases z with ⟨i,k⟩
  change M.mulVec v (i,k.castSucc) = y (i,k)
  simpa only [total,Fin.lastCases_castSucc] using congrFun hv (i,k.castSucc)

lemma old_rows_full_rank {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) (h : Function.Surjective M.mulVec) :
    (M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id).rank = Fintype.card I*c := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using (surjective_iff_row_card _).mp (old_surjective M h)

/-- Full surjectivity is equivalent to spanning the old slices and gaining one whole slice in rank. -/
lemma surjective_iff_increment {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) :
    Function.Surjective M.mulVec ↔
      Function.Surjective (M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id).mulVec ∧
      M.rank = (M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id).rank + Fintype.card I := by
  let N := M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id
  change Function.Surjective M.mulVec ↔ Function.Surjective N.mulVec ∧ M.rank=N.rank+Fintype.card I
  constructor
  · intro h
    have hN := old_surjective M h
    refine ⟨hN,?_⟩
    rw [(surjective_iff_row_card M).mp h,(surjective_iff_row_card N).mp hN]
    simp [Fintype.card_prod,Nat.mul_succ]
  · rintro ⟨hN,hr⟩
    apply (surjective_iff_row_card M).mpr
    rw [hr,(surjective_iff_row_card N).mp hN]
    simp [Fintype.card_prod,Nat.mul_succ]

omit [Fintype I] in
/-- The exact rank gain is the dimension of the last-slice image of the old-row kernel. -/
lemma rank_eq_old_add_last_kernel {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) :
    let N := M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id
    let L := M.submatrix (fun i : I => (i,Fin.last c)) id
    M.rank = N.rank + finrank K (range (L.mulVecLin.domRestrict (ker N.mulVecLin))) := by
  classical
  let F := M.mulVecLin
  let N := (M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id).mulVecLin
  let L := (M.submatrix (fun i : I => (i,Fin.last c)) id).mulVecLin
  let R := L.domRestrict (ker N)
  have split (x : J → K) : F x=0 ↔ N x=0 ∧ L x=0 := by
    constructor
    · intro hx
      constructor
      · funext z
        exact congrFun hx (z.1,z.2.castSucc)
      · funext i
        exact congrFun hx (i,Fin.last c)
    · rintro ⟨hn,hl⟩
      funext z
      obtain ⟨i,k⟩ := z
      cases k using Fin.lastCases with
      | last => exact congrFun hl i
      | cast k => exact congrFun hn (i,k)
  let E : ker R ≃ₗ[K] ker F := {
    toFun := fun x => ⟨x.val.val,(split x.val.val).mpr ⟨x.val.property,x.property⟩⟩
    invFun := fun x => ⟨⟨x.val,((split x.val).mp x.property).1⟩,((split x.val).mp x.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hF := F.finrank_range_add_finrank_ker
  have hN := N.finrank_range_add_finrank_ker
  have hR := R.finrank_range_add_finrank_ker
  have hE := E.finrank_eq
  change finrank K (range F) = finrank K (range N) + finrank K (range R)
  omega

/-- A maximal gain on the new rows is equivalent to solving them while fixing all old rows. -/
lemma increment_iff_last_kernel_surjective {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) :
    let N := M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id
    let L := M.submatrix (fun i : I => (i,Fin.last c)) id
    M.rank = N.rank + Fintype.card I ↔ Function.Surjective (L.mulVecLin.domRestrict (ker N.mulVecLin)) := by
  classical
  let N := M.submatrix (fun z : I × Fin c => (z.1,z.2.castSucc)) id
  let L := M.submatrix (fun i : I => (i,Fin.last c)) id
  let R := L.mulVecLin.domRestrict (ker N.mulVecLin)
  change M.rank=N.rank+Fintype.card I ↔ Function.Surjective R
  have h := rank_eq_old_add_last_kernel M
  change M.rank=N.rank+finrank K (range R) at h
  constructor
  · intro hr
    apply range_eq_top.mp
    apply eq_top_of_finrank_eq
    rw [finrank_pi]
    omega
  · intro hs
    rw [range_eq_top.mpr hs,finrank_top,finrank_pi] at h
    exact h

end UnrestrictedSlice

namespace CriticalJacobian

open MvPolynomial

/-- Restrict the tensor rows along any map on the third index. The parameters
and all three variations are still defined on their full coordinate spaces. -/
theorem restricted_tangent_iff {a b c r k : ℕ} (f : Fin k → Fin c)
    (P : Matrix ((Fin a × Fin b) × Fin c) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c)))
      (MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) ℂ))
    (entry : ∀ i j l t v, P ((i,j),l) (t,v) =
      v.elim (fun ii => if ii=i then X (t,.inr (.inl j))*X (t,.inr (.inr l)) else 0)
        (Sum.elim (fun jj => if jj=j then X (t,.inl i)*X (t,.inr (.inr l)) else 0)
          (fun ll => if ll=l then X (t,.inl i)*X (t,.inr (.inl j)) else 0))) :
    (∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j l, T i j l =
          ∑ t, (u t i*(y t j*z t (f l)) + x t i*(v t j*z t (f l)) + x t i*(y t j*w t (f l)))) ↔
    ∃ p : (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) → ℂ,
      Function.Surjective ((P.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,f q.2)) id).map
        (MvPolynomial.eval p)).mulVec := by
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let M := P.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,f q.2)) id
  have action (p q : V → ℂ) (i : Fin a) (j : Fin b) (l : Fin k) :
      (M.map (MvPolynomial.eval p)).mulVec q ((i,j),l) =
        ∑ t : Fin r, (q (t,.inl i)*(p (t,.inr (.inl j))*p (t,.inr (.inr (f l)))) +
          p (t,.inl i)*(q (t,.inr (.inl j))*p (t,.inr (.inr (f l)))) +
          p (t,.inl i)*(p (t,.inr (.inl j))*q (t,.inr (.inr (f l))))) := by
    change (∑ s : V, MvPolynomial.eval p (P ((i,j),f l) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [entry,apply_ite,ite_mul,Finset.sum_ite_eq']
    ring
  let pack (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ) (z : Fin r → Fin c → ℂ) : V → ℂ :=
    fun (t,v) => v.elim (x t) (Sum.elim (y t) (z t))
  constructor
  · rintro ⟨x,y,z,h⟩
    refine ⟨pack x y z,?_⟩
    intro T
    obtain ⟨u,v,w,hu⟩ := h fun i j l => T ((i,j),l)
    refine ⟨pack u v w,?_⟩
    funext ⟨⟨i,j⟩,l⟩
    change (M.map (MvPolynomial.eval (pack x y z))).mulVec (pack u v w) ((i,j),l) = _
    rw [action]
    exact (hu i j l).symm
  · rintro ⟨p,h⟩
    refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),
      fun t l => p (t,.inr (.inr l)),?_⟩
    intro T
    obtain ⟨q,hq⟩ := h fun s => T s.1.1 s.1.2 s.2
    refine ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),
      fun t l => q (t,.inr (.inr l)),?_⟩
    intro i j l
    exact (congrFun hq ((i,j),l)).symm.trans (action p q i j l)

end CriticalJacobian

namespace UnrestrictedRectangle

/-- Enlarging the last tensor factor preserves or increases the dimension-count ceiling. -/
theorem rank_mono {a b c : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a*b*c ⌈/⌉ (a+b+c-2) ≤ a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2) := by
  let D := a+b+c-2
  let R := a*b*(c+1) ⌈/⌉ (D+1)
  have hp : 0 < D := by dsimp [D]; omega
  have hd : a+b+(c+1)-2 = D+1 := by dsimp [D]; omega
  rw [hd]
  change a*b*c ⌈/⌉ D ≤ R
  have cover : a*b*(c+1) ≤ (D+1)*R := (ceilDiv_le_iff_le_mul (by omega)).mp le_rfl
  have bound : R ≤ a*b := by
    apply (ceilDiv_le_iff_le_mul (by omega : 0<D+1)).mpr
    calc
      a*b*(c+1) ≤ a*b*(D+1) := Nat.mul_le_mul_left _ (by dsimp [D]; omega)
      _ = _ := Nat.mul_comm _ _
  apply (ceilDiv_le_iff_le_mul hp).mpr
  nlinarith only [cover,bound]

/-- Pad the point list and the last factor of an unrestricted witness by zero.
On the original slice coordinates the tangent equations still cover every tensor. -/
theorem old_slices {a b c r r' : ℕ} (hrr : r ≤ r')
    (h : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ X : Fin r' → Fin a → ℂ, ∃ Y : Fin r' → Fin b → ℂ, ∃ Z : Fin r' → Fin (c+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ U : Fin r' → Fin a → ℂ,
        ∃ V : Fin r' → Fin b → ℂ, ∃ W : Fin r' → Fin (c+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (U t i*(Y t j*Z t k.castSucc) + X t i*(V t j*Z t k.castSucc) +
            X t i*(Y t j*W t k.castSucc)) := by
  obtain ⟨s,rfl⟩ : ∃ s, r'=r+s := ⟨r'-r,by omega⟩
  obtain ⟨x,y,z,hs⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin (r+s) := finSumFinEquiv
  let pad {I : Type} (f : Fin r → I → ℂ) (t : Fin (r+s)) : I → ℂ :=
    (e.symm t).elim f (fun _ _ => 0)
  let extend (f : Fin c → ℂ) : Fin (c+1) → ℂ := Fin.lastCases 0 f
  refine ⟨pad x,pad y,pad (fun t => extend (z t)),?_⟩
  intro T
  obtain ⟨u,v,w,good⟩ := hs T
  refine ⟨pad u,pad v,pad (fun t => extend (w t)),?_⟩
  intro i j k
  rw [← e.sum_comp]
  simpa [Fintype.sum_sum_type,pad,extend] using good i j k

end UnrestrictedRectangle

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
/-- At the lower seed for first dimension 3 and gap 10, the anchored border of
alternative reduction #6570 cannot span its regular-left face. -/
theorem UnrestrictedRectangle.anchored_border_counterexample :
    ¬ (let a : ℕ := 3
       let d : ℕ := 320
       let s : ℕ := 10
       let e := d+s
       let r := a*d*e ⌈/⌉ (a+d+e-2)
       let D := 2*a*(d+2)*(e+2)+1
       let B := Fin 2 ⊕ Fin d
       let C := Fin 2 ⊕ Fin e
       let val (z : Fin D) : ℂ := z.val
       ∃ X : Fin a → Fin a → Fin D, ∃ Y : Fin a → B → Fin D, ∃ Z : Fin a → C → Fin D,
       ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin d → Fin D, ∃ z : Fin r → Fin e → Fin D,
         ∀ T : Fin a → B → C → ℂ, ∃ U : Fin a → Fin a → ℂ, ∃ V : Fin a → B → ℂ, ∃ W : Fin a → C → ℂ,
           ∃ v w : Fin r → Fin 2 → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
             T i j k = (∑ t, (U t i*(val (Y t j)*val (Z t k)) + val (X t i)*(V t j*val (Z t k)) +
               val (X t i)*(val (Y t j)*W t k))) +
             ∑ t, (val (x t i)*(j.elim (v t) (fun _ => 0)*k.elim (fun _ => 0) (fun l => val (z t l))) +
               val (x t i)*(j.elim (fun _ => 0) (fun l => val (y t l))*k.elim (w t) (fun _ => 0)))) := by
  classical
  rintro ⟨X,Y,Z,x,y,z,cover⟩
  let K := Fin 2 ⊕ Fin 330
  let I := Fin 3 × Fin 2 × K
  let J := (Fin 3 × (Fin 3 ⊕ (Fin 2 ⊕ K))) ⊕ (Fin 487 × Fin 2)
  let val (v : Fin 641425) : ℂ := v.val
  let L : (J → ℂ) →ₗ[ℂ] (I → ℂ) := {
    toFun := fun b (i,j,k) =>
      (∑ t, (b (.inl (t,.inl i)) * (val (Y t (.inl j)) * val (Z t k)) +
        val (X t i) * (b (.inl (t,.inr (.inl j))) * val (Z t k)) +
        val (X t i) * (val (Y t (.inl j)) * b (.inl (t,.inr (.inr k)))))) +
      ∑ t, val (x t i) * (b (.inr (t,j)) * k.elim (fun _ => 0) (fun l => val (z t l)))
    map_add' := by
      intro b c
      funext ⟨i,j,k⟩
      simp only [Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
      abel
    map_smul' := by
      intro c b
      funext ⟨i,j,k⟩
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      rw [mul_add c,Finset.mul_sum,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring }
  have onto : Function.Surjective L := by
    intro M
    let T (i : Fin 3) (j : Fin 2 ⊕ Fin 320) (k : K) :=
      j.elim (fun l => M (i,l,k)) (fun _ => 0)
    obtain ⟨U,V,W,v,w,hT⟩ := cover T
    let b : J → ℂ
      | .inl (t,.inl i) => U t i
      | .inl (t,.inr (.inl j)) => V t (.inl j)
      | .inl (t,.inr (.inr k)) => W t k
      | .inr (t,j) => v t j
    refine ⟨b,?_⟩
    funext ⟨i,j,k⟩
    simpa only [L,b,val,LinearMap.coe_mk,AddHom.coe_mk,T,Sum.elim_inl,
      zero_mul,mul_zero,add_zero] using (hT i (.inl j) k (Or.inl rfl)).symm
  have bound := LinearMap.finrank_le_finrank_of_surjective onto
  simp only [Module.finrank_fintype_fun_eq_card,I,J,K,Fintype.card_prod,
    Fintype.card_sum,Fintype.card_fin] at bound
  exact (by decide : ¬(1992 ≤ 1985)) bound

namespace UnrestrictedRectangle

open MvPolynomial

/-- Once the preceding slices span, the exact remaining condition is the
generic rank increment of the last slice. All factor variables are free. -/
private lemma step_for_matrix {a b c r r' : ℕ} (hrr : r ≤ r')
    (prev : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
  ∃ z : Fin r → Fin c → ℂ, ∀ T : Fin a → Fin b → Fin c → ℂ,
  ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
  ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (P : Matrix ((Fin a × Fin b) × Fin (c+1)) (Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) (MvPolynomial (Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ))
    (entry : ∀ i j l t v, P ((i,j),l) (t,v) =
  v.elim (fun ii => if ii=i then X (t,.inr (.inl j))*X (t,.inr (.inr l)) else 0)
    (Sum.elim (fun jj => if jj=j then X (t,.inl i)*X (t,.inr (.inr l)) else 0)
      (fun kk => if kk=l then X (t,.inl i)*X (t,.inr (.inl j)) else 0))) :
    (∃ x : Fin r' → Fin a → ℂ, ∃ y : Fin r' → Fin b → ℂ,
  ∃ z : Fin r' → Fin (c+1) → ℂ, ∀ T : Fin a → Fin b → Fin (c+1) → ℂ,
  ∃ u : Fin r' → Fin a → ℂ, ∃ v : Fin r' → Fin b → ℂ,
  ∃ w : Fin r' → Fin (c+1) → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let R := MvPolynomial (Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b := by
  classical
  let R := MvPolynomial (Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ
  let G := P.map (algebraMap R (FractionRing R))
  let rows (q : (Fin a × Fin b) × Fin c) := (q.1,q.2.castSucc)
  have full : (∃ x : Fin r' → Fin a → ℂ, ∃ y : Fin r' → Fin b → ℂ,
  ∃ z : Fin r' → Fin (c+1) → ℂ, ∀ T : Fin a → Fin b → Fin (c+1) → ℂ,
  ∃ u : Fin r' → Fin a → ℂ, ∃ v : Fin r' → Fin b → ℂ,
  ∃ w : Fin r' → Fin (c+1) → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔ Function.Surjective G.mulVec :=
    (CriticalJacobian.restricted_tangent_iff id P entry).trans
      (CriticalTensor.Unrestricted.generic_surjective_iff P).symm
  have old : Function.Surjective (G.submatrix rows id).mulVec := by
    let P₀ := P.submatrix rows id
    change Function.Surjective (P₀.map (algebraMap R (FractionRing R))).mulVec
    exact (CriticalTensor.Unrestricted.generic_surjective_iff P₀).mpr
      ((CriticalJacobian.restricted_tangent_iff Fin.castSucc P entry).mp (old_slices hrr prev))
  change _ ↔ G.rank=(G.submatrix rows id).rank+a*b
  rw [full]
  constructor
  · intro h
    simpa only [Fintype.card_prod,Fintype.card_fin] using ((UnrestrictedSlice.surjective_iff_increment G).mp h).2
  · intro h
    exact (UnrestrictedSlice.surjective_iff_increment G).mpr
      ⟨old,by simpa only [Fintype.card_prod,Fintype.card_fin] using h⟩

lemma step_iff {a b c : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (prev : ∃ x : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin a → ℂ, ∃ y : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin b → ℂ,
  ∃ z : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin c → ℂ, ∀ T : Fin a → Fin b → Fin c → ℂ,
  ∃ u : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin a → ℂ, ∃ v : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin b → ℂ,
  ∃ w : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin c → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    (∃ x : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin a → ℂ, ∃ y : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin b → ℂ,
  ∃ z : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin (c+1) → ℂ, ∀ T : Fin a → Fin b → Fin (c+1) → ℂ,
  ∃ u : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin a → ℂ, ∃ v : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin b → ℂ,
  ∃ w : Fin (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) → Fin (c+1) → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
    let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let coord : V → R := MvPolynomial.X
    let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
        (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
          (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b := by
  let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
  let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
  let R := MvPolynomial V ℂ
  let coord : V → R := MvPolynomial.X
  let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
  exact step_for_matrix (rank_mono ha hab hbc) prev P (fun _ _ _ _ _ => rfl)

end UnrestrictedRectangle

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1

open MvPolynomial

section ConsecutiveSides

/-- Seed each pair of first dimensions by proving the first admissible strict rectangle. -/
def H1 : Prop :=
  ∀ a b : ℕ, 3 ≤ a → a ≤ b → b+1 < (a-1)*(b-1) →
    let r := (a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2))
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
  ∃ z : Fin r → Fin (b+1) → ℂ, ∀ T : Fin a → Fin b → Fin (b+1) → ℂ,
  ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
  ∃ w : Fin r → Fin (b+1) → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

end ConsecutiveSides

section LastSlice

/-- Over the rational function field, adding the final slice contributes all ab new directions
modulo the old rows at the same unrestricted point count. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 3 ≤ a → a ≤ b → b < c → c+1 < (a-1)*(b-1) →
    let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
    let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let coord : V → R := MvPolynomial.X
    let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
        (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
          (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b

end LastSlice

private lemma complex_of_parent (parent_rectangles : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H3) {a b c : ℕ}
    (ha : 3≤a) (hab : a≤b) (hbc : b<c) (hc : c<(a-1)*(b-1)) :
    ∃ x : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin a → ℂ, ∃ y : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin b → ℂ,
  ∃ z : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin c → ℂ, ∀ T : Fin a → Fin b → Fin c → ℂ,
  ∃ u : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin a → ℂ, ∃ v : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin b → ℂ,
  ∃ w : Fin (a*b*c ⌈/⌉ (a+b+c-2)) → Fin c → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  obtain ⟨x,y,z,h⟩ := parent_rectangles a b c ha hab hbc hc
  exact ⟨fun t i => ((x t i).val:ℂ),fun t j => ((y t j).val:ℂ),
    fun t k => ((z t k).val:ℂ),h⟩

/-- Necessity ensures that actual tangent spanning at the predicted ranks already
supplies the two independent tests, without imposing a fixed support pattern. -/
lemma necessary (parent_rectangles : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H3) : H1 ∧ H2 := by
  constructor
  · intro a b ha hab hc
    exact complex_of_parent parent_rectangles ha hab (by omega) hc
  · intro a b c ha hab hbc hc
    apply (UnrestrictedRectangle.step_iff ha hab hbc.le
      (complex_of_parent parent_rectangles ha hab hbc (by omega))).mp
    exact complex_of_parent parent_rectangles ha hab (by omega) hc

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H3 := by
  intro seed increment a b c ha hab hbc hc
  have spans : ∀ k : ℕ, b<k → k<(a-1)*(b-1) →
      ∃ x : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin a → ℂ, ∃ y : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin b → ℂ,
  ∃ z : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin k → ℂ, ∀ T : Fin a → Fin b → Fin k → ℂ,
  ∃ u : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin a → ℂ, ∃ v : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin b → ℂ,
  ∃ w : Fin (a*b*k ⌈/⌉ (a+b+k-2)) → Fin k → ℂ, ∀ i j k, T i j k =
    ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk hcut
      by_cases first : k=b
      · subst k
        exact seed a b ha hab hcut
      · have prev : b<k := by omega
        exact (UnrestrictedRectangle.step_iff ha hab prev.le (ih prev (by omega))).mpr
          (increment a b k ha hab prev hcut)
  exact CriticalReduction.bounded_of_witness (spans c hbc hc)

/-- The new criterion is equivalent to the registered parent tangent statement. -/
lemma iff_seed_and_increment : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1.H3 ↔ H1 ∧ H2 :=
  ⟨necessary,fun h => main h.1 h.2⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1
