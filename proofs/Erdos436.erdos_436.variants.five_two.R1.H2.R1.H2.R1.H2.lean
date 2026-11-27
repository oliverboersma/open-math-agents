import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1
import Mathlib
open Polynomial Finset
namespace OrbitResidue

lemma separate {m p : ℕ} (hp : p.Prime) (large : m*m < p)
    {R F : Type} [CommRing R] [Field F] [CharP F p]
    (ψ : R →+* F) (f : Fin m → R →+* F) (point : ∀ x, ∃ i, ψ x=f i x) :
    ∃ i, ∀ x, ψ x=f i x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra! bad
  choose a ha using bad
  let P (i : Fin m) : F[X] := ∑ j : Fin m, monomial j.val (ψ (a j)-f i (a j))
  have nz (i : Fin m) : P i ≠ 0 := by
    intro hz
    have eq := congrArg (fun Q : F[X] => Q.coeff i.val) hz
    rw [show (P i).coeff i.val = ψ (a i)-f i (a i) by
      simp [P,finset_sum_coeff,coeff_monomial,Fin.val_inj]] at eq
    exact ha i (sub_eq_zero.mp (by simpa using eq))
  have deg (i : Fin m) : (P i).natDegree ≤ m :=
    natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_monomial_le _).trans j.isLt.le
  let U := univ.biUnion fun i : Fin m => (P i).roots.toFinset
  have cu : U.card ≤ m*m := calc
    _ ≤ ∑ i : Fin m, (P i).roots.toFinset.card := card_biUnion_le
    _ ≤ ∑ _i : Fin m, m := sum_le_sum fun i _ =>
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (deg i))
    _ = _ := by simp
  let j := ZMod.castHom (m := p) dvd_rfl F
  have sub : univ.image j ⊆ U := by
    intro y hy
    obtain ⟨t,_,rfl⟩ := mem_image.mp hy
    let v : R := ∑ k : Fin m, a k*(t.val : R)^k.val
    obtain ⟨i,hi⟩ := point v
    refine mem_biUnion.mpr ⟨i,mem_univ _,Multiset.mem_toFinset.mpr ((mem_roots (nz i)).mpr ?_)⟩
    have e : j t = (t.val : F) := by
      change ZMod.castHom (m := p) dvd_rfl F t = _
      conv_lhs => rw [← ZMod.natCast_zmod_val t]
      rw [map_natCast]
    rw [Polynomial.IsRoot.def,e]
    simp only [v,map_sum,map_mul,map_pow,map_natCast] at hi
    simpa only [P,eval_finsetSum,eval_monomial,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr hi
  have low := card_le_card sub
  rw [card_image_of_injective _ j.injective,card_univ,ZMod.card] at low
  omega

lemma iteration {R : Type} [CommRing R] (σ : R ≃+* R) (n : ℕ) (x : R) :
    (σ : R → R)^[n] x = (σ^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',pow_succ']
    exact congrArg σ ih

lemma conjugate {R F : Type} [CommRing R] [Field F] (σ : R ≃+* R) (m : ℕ)
    (pos : 0 < m) (period : ∀ x : R, (σ : R → R)^[m] x=x)
    (φ ψ : R →+* F) (fix : ∀ x, σ x=x → ψ x=φ x) (x : R) :
    ∃ i : Fin m, ψ x = φ ((σ : R → R)^[i.val] x) := by
  classical
  let g (i : ℕ) : R[X] := X-C ((σ : R → R)^[i] x)
  let P := ∏ i ∈ range m, g i
  have cyc : P.map σ.toRingHom = P := by
    change (Polynomial.mapRingHom σ.toRingHom) (∏ i ∈ range m, g i) = _
    rw [map_prod]
    have step (i : ℕ) : Polynomial.mapRingHom σ.toRingHom (g i) = g (i+1) := by
      simp [g,Function.iterate_succ_apply']
    simp only [step]
    change (∏ i ∈ range m,g (i+1))=∏ i ∈ range m,g i
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    rw [prod_range_succ,prod_range_succ' g]
    congr 1
    simp [g,period]
  have cfix (i : ℕ) : σ (P.coeff i)=P.coeff i := by
    simpa using congrArg (fun Q : R[X] => Q.coeff i) cyc
  have maps : P.map ψ=P.map φ := by ext i; simp [fix _ (cfix i)]
  have root : (P.map ψ).eval (ψ x)=0 := by
    change (Polynomial.evalRingHom (ψ x)) ((Polynomial.mapRingHom ψ) (∏ i ∈ range m,g i))=0
    rw [map_prod,map_prod]
    apply prod_eq_zero (mem_range.mpr pos : 0 ∈ range m)
    simp [g]
  rw [maps] at root
  change (Polynomial.evalRingHom (ψ x)) ((Polynomial.mapRingHom φ) (∏ i ∈ range m,g i))=0 at root
  rw [map_prod,map_prod,Finset.prod_eq_zero_iff] at root
  obtain ⟨i,hi,eq⟩ := root
  exact ⟨⟨i,mem_range.mp hi⟩,sub_eq_zero.mp (by simpa [g] using eq)⟩

theorem orbit {R : Type} [CommRing R] (σ : R ≃+* R) (m p : ℕ)
    (pos : 0 < m) (period : ∀ x, (σ : R → R)^[m] x=x)
    (large : m*m < p) (hp : p.Prime) (F : Type) [Field F] [CharP F p] (φ : R →+* F)
    (fix : ∀ a, σ a=a → (φ a)^p=φ a) : ∃ t : ℕ, ∀ a, (φ a)^p=φ ((σ : R → R)^[t] a) := by
  letI : Fact p.Prime := ⟨hp⟩
  let ψ := (frobenius F p).comp φ
  let f (i : Fin m) := φ.comp (σ^i.val).toRingHom
  obtain ⟨i,hi⟩ := separate hp large ψ f (fun x => by
    obtain ⟨i,eq⟩ := conjugate σ m pos period φ ψ fix x
    refine ⟨i,?_⟩
    rw [iteration] at eq
    exact eq)
  refine ⟨i,fun x => ?_⟩
  rw [iteration]
  exact hi x

end OrbitResidue
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1.H2 := fun _ _ σ => OrbitResidue.orbit σ
