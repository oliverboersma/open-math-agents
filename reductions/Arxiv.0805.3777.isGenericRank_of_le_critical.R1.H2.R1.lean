import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1

/-! Bounded tangent witnesses on the critical boundary and the remaining strict interior.

For c=(a-1)(b-1), mark one rank-one a-by-b matrix. Its first two
factor variations cover its row and column, while the other c matrices
can cover every coordinate off that row and column. Nonvanishing of a
finite product of minors makes these marked-slice conditions simultaneous.
Using separate third-axis coordinates for c summands and varying every
third factor gives a spanning tangent with c+1 terms. The finite-grid
lemma of the parent reduction bounds all the factor entries.

In the strict interior the remaining targets are the six-slice square
family, the other square families, and the strictly rectangular formats.
For the boundary rank formula see Friedland, Corollary 6.4(2),
https://arxiv.org/abs/0805.3777. -/

namespace RemainingBoundary

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
lemma boundary_witness {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : c = (a-1)*(b-1)) :
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

end RemainingBoundary

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1

section SixSliceSquares

/-- The square-ended six-slice family. -/
def H1 : Prop :=
  ∀ m : ℕ, 6 ≤ m →
    let r := 6*m*m ⌈/⌉ (6+m+m-2)
    let D := 2*(6*m*m)+1
    ∃ x : Fin r → Fin 6 → Fin D, ∃ y : Fin r → Fin m → Fin D, ∃ z : Fin r → Fin m → Fin D,
      ∀ T : Fin 6 → Fin m → Fin m → ℂ, ∃ u : Fin r → Fin 6 → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin m → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end SixSliceSquares

section OtherSquares

/-- Other admissible square-ended formats strictly below the critical boundary. -/
def H2 : Prop :=
  ∀ a m : ℕ, 3 ≤ a → a ≤ m → m < (a-1)*(m-1) →
    (∀ p : ℕ, (a,m,m) ≠ (3,2*p+1,2*p+1)) → a ≠ 5 → a ≠ 6 →
    let r := a*m*m ⌈/⌉ (a+m+m-2)
    let D := 2*(a*m*m)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin m → Fin D, ∃ z : Fin r → Fin m → Fin D,
      ∀ T : Fin a → Fin m → Fin m → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin m → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end OtherSquares

section Rectangles

/-- Formats with unequal last two dimensions strictly below the critical boundary. -/
def H3 : Prop :=
  ∀ a b c : ℕ, 3 ≤ a → a ≤ b → b < c → c < (a-1)*(b-1) →
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end Rectangles

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.H2 := by
  intro h₁ h₂ h₃ a b c ha hab hbc hc hexc h₅
  by_cases edge : c = (a-1)*(b-1)
  · exact RemainingBoundary.boundary_witness ha (by omega) edge
  have inside := lt_of_le_of_ne hc edge
  by_cases square : b = c
  · subst c
    by_cases six : a = 6
    · subst a
      exact h₁ b hab
    · exact h₂ a b ha hab inside hexc (h₅.resolve_right (fun h => h rfl)) six
  · exact h₃ a b c ha hab (lt_of_le_of_ne hbc square) inside

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1
